/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.List.OfFn
import Numlib.Analysis.Matrix.ToEuclideanLin
import Numlib.Krylov.Preconditioned
import Numlib.Optimization.Subproblem.Krylov

/-!
# Conn, Gould and Toint, Algorithm 7.5.2: The generalized Lanczos trust-region iteration

Algorithm 7.5.2 of [conn2000trust] approximates the minimizer of $m(s) = \langle g, s \rangle +
\frac{1}{2} \langle s, H s \rangle$ subject to $\|s\|_M \le \Delta$, where $M$ is a preconditioner.
While every preconditioned CG (PCG) trial for $Hs = -g$ has positive curvature and stays strictly
inside the trust region, the algorithm takes the PCG iterates. After the first failure it solves the
reduced subproblem in the Lanczos basis exactly at every later trial:
$$\min_h \; \|g\|_{M^{-1}} h_0 + \tfrac{1}{2} h^T T_{k+1} h \quad \text{subject to} \quad \|h\| \le
  \Delta,$$
where $T_{k+1}$ is the Lanczos tridiagonal matrix of $M^{-1} H$ in the $M$-inner product, and it
lifts $h$ to $s = \sum_i h_i q_i$ with the Lanczos vectors $q_i$. Each trial reports a residual norm
for the stopping test. This module defines the trials, proves that they are feasible, proves that
the reported reduced residual is the norm of the full shifted residual, and proves that a scan of
the trials with a nonnegative tolerance terminates by the first invariant Krylov subspace. The
proofs use `Numlib.Krylov.Preconditioned`, `Numlib.Krylov.Lanczos` and the ball characterization
`Subproblem.isMinOn_closedBall_iff`.

## Main definitions

* Algorithm 7.5.2, `ConnGouldToint.Chapter07.gltrInterior`: the interior flag, true while all PCG
  trials so far have positive curvature and lie strictly inside the trust region.
* Algorithm 7.5.2, `ConnGouldToint.Chapter07.algorithm_7_5_2`: the $k$-th trial step and its
  reported residual norm.
* Algorithm 7.5.2, `ConnGouldToint.Chapter07.algorithm_7_5_2_until`: the first trial, up to the
  first invariant Krylov subspace, whose residual norm meets a tolerance.

## Main results

* Algorithm 7.5.2, `ConnGouldToint.Chapter07.gltrInterior_succ`: once the interior flag fails, it
  stays false.
* Algorithm 7.5.2, `ConnGouldToint.Chapter07.algorithm_7_5_2_feasible`: up to the first invariant
  Krylov subspace, every trial satisfies $\|s\|_M \le \Delta$.
* Algorithm 7.5.2, `ConnGouldToint.Chapter07.algorithm_7_5_2_reduced_residual`: a reduced trial
  reports $\|g + Hs + \mu M s\|_{M^{-1}}$ for some $\mu \ge 0$.
* Algorithm 7.5.2, `ConnGouldToint.Chapter07.algorithm_7_5_2_until_spec`: a returned trial is
  feasible and meets the tolerance.
* Algorithm 7.5.2, `ConnGouldToint.Chapter07.algorithm_7_5_2_until_terminates`: with a nonnegative
  tolerance the scan returns a trial.

## Conventions

* The preconditioner is a pair $M$, $M^{-1}$ with `Krylov.IsPreconditioner M Minv`. The norms are
  $\|x\|_M = \sqrt{\langle M x, x \rangle}$ (`energyNorm M`) and $\|x\|_{M^{-1}} = \sqrt{\langle
  M^{-1} x, x \rangle}$ (`energyNorm Minv`).
* The PCG iterates for $Hs = -g$ from $0$ are `PCG.iterate H Minv (-g) 0 j`. Trial $k$ uses the PCG
  state with index $k + 1$ and the Lanczos matrix of order $k + 1$.

## Implementation notes

* The $M$-inner product space is `hM.EnergySpace`, with the identity map `hM.toEnergy`. In it,
  $M^{-1} H$ is the operator `hM.energyEnd (Minv ∘ₗ H)` and $M^{-1} g$ is the vector
  `hM.toEnergy (Minv g)`.
* The exact reduced minimizer is chosen with `Classical.choose` from the existence of minimizers on
  a closed ball. The trial is therefore a noncomputable function, and the results hold for every
  choice.
* The interior flag tests the curvature $\langle H p_j, p_j \rangle > 0$ directly, which also covers
  a zero denominator in the PCG step length.

## Deviations from the source

* **Algorithm 7.5.2** (reading). The reduced tridiagonal matrix comes from the Lanczos recurrence
  for $M^{-1} H$ in the $M$-inner product, computed independently of the PCG coefficients, as the
  text suggests when the PCG curvature vanishes. The physical residual is checked before stopping.
  See `ConnGouldToint.Chapter07.algorithm_7_5_2`.
-/

namespace ConnGouldToint.Chapter07

open Krylov Subproblem Matrix WithLp
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Algorithm 7.5.2** of [conn2000trust], interior flag. Let $H$, $M$ and $M^{-1}$ be linear
operators on a real inner product space $E$, let $g \in E$, $\Delta \in \mathbb{R}$ and
$k \in \mathbb{N}$, and let $x_j$ and $p_j$ be the PCG iterates and directions for $Hx = -g$
from $0$. The **interior flag** holds at $k$ if for every $j < k$
$$\langle H p_j, p_j \rangle > 0 \qquad \text{and} \qquad \|x_{j+1}\|_M < \Delta.$$

Testing the curvature directly also covers a zero denominator before the division in the PCG
step length. -/
def gltrInterior (H M Minv : E →ₗ[ℝ] E) (g : E) (Δ : ℝ) (k : ℕ) : Prop :=
  ∀ j < k, let s := PCG.iterate H Minv (-g) 0 j
    0 < ⟪H s.p, s.p⟫ ∧ energyNorm M (PCG.iterate H Minv (-g) 0 (j + 1)).x < Δ

/-- **Algorithm 7.5.2** of [conn2000trust], switch from the interior to the reduced problem. The
interior flag holds at $k + 1$ if and only if it holds at $k$ and the PCG trial with index $k$
satisfies $\langle H p_k, p_k \rangle > 0$ and $\|x_{k+1}\|_M < \Delta$.

In particular, once the flag fails, it fails at every later index, and the algorithm stays with
the reduced problem. -/
theorem gltrInterior_succ (H M Minv : E →ₗ[ℝ] E) (g : E) (Δ : ℝ) (k : ℕ) :
    gltrInterior H M Minv g Δ (k + 1) ↔
      gltrInterior H M Minv g Δ k ∧
      (let s := PCG.iterate H Minv (-g) 0 k
       0 < ⟪H s.p, s.p⟫ ∧ energyNorm M (PCG.iterate H Minv (-g) 0 (k + 1)).x < Δ) := by
  constructor
  · intro h
    exact ⟨fun j hj => h j (hj.trans (Nat.lt_succ_self k)), h k (Nat.lt_succ_self k)⟩
  · rintro ⟨h, hk⟩ j hj
    rcases (Nat.le_of_lt_succ hj).lt_or_eq with hj | rfl
    · exact h j hj
    · exact hk

private noncomputable def gltrReducedOperator {k : ℕ} (T : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) :
    EuclideanSpace ℝ (Fin (k + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (k + 1)) :=
  (toEuclideanLin T).toContinuousLinearMap

private noncomputable def gltrReducedStep {k : ℕ} (T : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)
    (γ Δ : ℝ) (hΔ : 0 ≤ Δ) : EuclideanSpace ℝ (Fin (k + 1)) :=
  Classical.choose (exists_isMinOn_closedBall (toLp 2 (Pi.single 0 γ)) (gltrReducedOperator T) hΔ)

private theorem gltrReducedStep_spec {k : ℕ} (T : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)
    (γ Δ : ℝ) (hΔ : 0 ≤ Δ) :
    ‖gltrReducedStep T γ Δ hΔ‖ ≤ Δ ∧
      IsMinOn (quadModel (toLp 2 (Pi.single 0 γ)) (gltrReducedOperator T))
        (Metric.closedBall 0 Δ) (gltrReducedStep T γ Δ hΔ) := by
  unfold gltrReducedStep
  let r : EuclideanSpace ℝ (Fin (k + 1)) := toLp 2 (Pi.single 0 γ)
  exact Classical.choose_spec (exists_isMinOn_closedBall r (gltrReducedOperator T) hΔ)

/-- **Algorithm 7.5.2** of [conn2000trust], one trial. Let $M$, $M^{-1}$ be a preconditioner on a
real inner product space $E$, let $H$ be a linear operator on $E$, and let $g \in E$,
$\Delta \ge 0$ and $k \in \mathbb{N}$. The $k$-th **trial** is a pair $(s, \rho)$ of a step and
a residual norm.

* If the interior flag holds at $k + 1$, then $s = x_{k+1}$ is the PCG iterate for $Hx = -g$
  from $0$, and $\rho = \|r_{k+1}\|_{M^{-1}}$ is the $M^{-1}$-norm of its residual.
* Otherwise, let $q_0, \dots, q_k$ be the Lanczos vectors and $T_{k+1}$ the Lanczos tridiagonal
  matrix of $M^{-1} H$ and $M^{-1} g$ in the $M$-inner product, and let $h \in \mathbb{R}^{k+1}$
  be an exact minimizer of $\|M^{-1} g\|_M h_0 + \frac{1}{2} h^T T_{k+1} h$ on the ball
  $\|h\| \le \Delta$. Then $s = \sum_{i=0}^{k} h_i q_i$ and $\rho = \beta_k |h_k|$, where
  $\beta_k$ is the next Lanczos coefficient.

The reduced subproblem is solved exactly. The minimizer $h$ is chosen by `Classical.choose`. The
Lanczos matrix and vectors are `Lanczos.tridiag` and `Arnoldi.vec` for
`hM.energyEnd (Minv ∘ₗ H)` and `hM.toEnergy (Minv g)`. -/
noncomputable def algorithm_7_5_2 {H M Minv : E →ₗ[ℝ] E} (hM : IsPreconditioner M Minv)
    (g : E) (Δ : ℝ) (hΔ : 0 ≤ Δ) (k : ℕ) : E × ℝ := by
  classical
  exact if gltrInterior H M Minv g Δ (k + 1) then
    let s := PCG.iterate H Minv (-g) 0 (k + 1)
    (s.x, energyNorm Minv s.r)
  else
    let A := hM.energyEnd (Minv ∘ₗ H)
    let b := hM.toEnergy (Minv g)
    let h := gltrReducedStep (Lanczos.tridiag A b (k + 1)) ‖b‖ Δ hΔ
    (hM.toEnergy.symm (∑ i : Fin (k + 1), ofLp h i • Arnoldi.vec A b i),
      Lanczos.beta A b k * |ofLp h (Fin.last k)|)

/-- **Algorithm 7.5.2** of [conn2000trust], feasibility of the trial. Let $E$ be finite-dimensional,
let $M$, $M^{-1}$ be a preconditioner, and let $\Delta \ge 0$. If $k + 1$ does not exceed the
dimension of the Krylov space of $M^{-1} H$ generated by $M^{-1} g$, then the step $s$ of the
$k$-th trial satisfies $\|s\|_M \le \Delta$.

The dimension is `Krylov.grade` of `hM.energyEnd (Minv ∘ₗ H)` and `hM.toEnergy (Minv g)`, so the
condition says that trial $k$ comes no later than the first invariant Krylov subspace. -/
theorem algorithm_7_5_2_feasible [FiniteDimensional ℝ E] {H M Minv : E →ₗ[ℝ] E} (hM : IsPreconditioner M Minv)
    (g : E) (Δ : ℝ) (hΔ : 0 ≤ Δ) (k : ℕ)
    (hk : k + 1 ≤ grade (hM.energyEnd (Minv ∘ₗ H)) (hM.toEnergy (Minv g))) :
    energyNorm M (algorithm_7_5_2 hM (H := H) g Δ hΔ k).1 ≤ Δ := by
  classical
  unfold algorithm_7_5_2
  split
  · rename_i h
    exact (h k (Nat.lt_succ_self k)).2.le
  · let : FiniteDimensional ℝ hM.EnergySpace :=
      FiniteDimensional.of_injective hM.toEnergy.symm.toLinearMap hM.toEnergy.symm.injective
    let A := hM.energyEnd (Minv ∘ₗ H)
    let b := hM.toEnergy (Minv g)
    let T := Lanczos.tridiag A b (k + 1)
    let h := gltrReducedStep T ‖b‖ Δ hΔ
    have hh : ‖h‖ ≤ Δ := (gltrReducedStep_spec T ‖b‖ Δ hΔ).1
    have ho : Orthonormal ℝ (fun i : Fin (k + 1) => Arnoldi.vec A b i) :=
      (Arnoldi.orthonormal A b).comp (Fin.castLE hk) (Fin.castLE_injective _)
    change ‖hM.toEnergy (hM.toEnergy.symm (∑ i : Fin (k + 1), ofLp h i • Arnoldi.vec A b i))‖ ≤ Δ
    rw [LinearEquiv.apply_symm_apply, ho.norm_sum_smul_eq_norm_toLp, WithLp.toLp_ofLp]
    exact hh

private theorem gltrEnergySymmetric {H M Minv : E →ₗ[ℝ] E}
    (hM : IsPreconditioner M Minv) (hH : H.IsSymmetric) :
    (hM.energyEnd (Minv ∘ₗ H)).IsSymmetric := by
  intro u v
  obtain ⟨u, rfl⟩ := hM.toEnergy.surjective u
  obtain ⟨v, rfl⟩ := hM.toEnergy.surjective v
  rw [hM.inner_energyEnd_left H, hM.inner_energyEnd_right H]
  exact hH u v

/-- **Algorithm 7.5.2** of [conn2000trust], correctness of the reduced residual. Let $E$ be
finite-dimensional, let $M$, $M^{-1}$ be a preconditioner, let $H$ be symmetric, and let
$\Delta > 0$ and $M^{-1} g \neq 0$. Let $k + 1$ not exceed the dimension of the Krylov space of
$M^{-1} H$ generated by $M^{-1} g$, and assume that the interior flag fails at $k + 1$. Then the
$k$-th trial $(s, \rho)$ satisfies
$$\|g + H s + \mu M s\|_{M^{-1}} = \rho$$
for some $\mu \ge 0$.

The reported reduced residual is thus the norm of the full shifted residual at the lifted step.
The multiplier $\mu$ is the multiplier of the reduced subproblem. -/
theorem algorithm_7_5_2_reduced_residual [FiniteDimensional ℝ E] {H M Minv : E →ₗ[ℝ] E}
    (hM : IsPreconditioner M Minv) (hH : H.IsSymmetric) (g : E) {Δ : ℝ} (hΔ : 0 < Δ) (k : ℕ)
    (hg : hM.toEnergy (Minv g) ≠ 0)
    (hk : k + 1 ≤ grade (hM.energyEnd (Minv ∘ₗ H)) (hM.toEnergy (Minv g)))
    (hflag : ¬ gltrInterior H M Minv g Δ (k + 1)) :
    let trial := algorithm_7_5_2 hM (H := H) g Δ hΔ.le k
    ∃ μ : ℝ, 0 ≤ μ ∧ energyNorm Minv (g + H trial.1 + μ • M trial.1) = trial.2 := by
  let : FiniteDimensional ℝ hM.EnergySpace :=
    FiniteDimensional.of_injective hM.toEnergy.symm.toLinearMap hM.toEnergy.symm.injective
  let A := hM.energyEnd (Minv ∘ₗ H)
  let b := hM.toEnergy (Minv g)
  let T := Lanczos.tridiag A b (k + 1)
  let h := gltrReducedStep T ‖b‖ Δ hΔ.le
  let y := ofLp h
  let q := fun j : ℕ => Arnoldi.vec A b j
  let z := ∑ j : Fin (k + 1), y j • q j
  let s := hM.toEnergy.symm z
  have hA : A.IsSymmetric := gltrEnergySymmetric hM hH
  have hT : (toEuclideanLin T).IsSymmetric :=
    (Lanczos.tridiag_isSymm A b (k + 1)).isSymmetric_toEuclideanLin
  have hmin := gltrReducedStep_spec T ‖b‖ Δ hΔ.le
  obtain ⟨μ, hμ⟩ := (isMinOn_closedBall_iff hT hΔ hmin.1).1 hmin.2
  have hsolve : (T + μ • 1) *ᵥ y = -(Pi.single 0 ‖b‖ : Fin (k + 1) → ℝ) := by
    have he := congrArg ofLp hμ.shifted
    change ofLp (toEuclideanLin T h + μ • h) =
      ofLp (-(toLp 2 (Pi.single 0 ‖b‖) : EuclideanSpace ℝ (Fin (k + 1)))) at he
    rw [WithLp.ofLp_add, Matrix.ofLp_toEuclideanLin, WithLp.ofLp_smul,
      WithLp.ofLp_neg, WithLp.ofLp_toLp] at he
    simpa only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] using he
  have hr : ‖b + A z + μ • z‖ = Lanczos.beta A b k * |y (Fin.last k)| :=
    (krylov_lanczos_coordinates (H := A.toContinuousLinearMap) hA hg hk 0 y μ).2.2.2 hsolve
  have hs : hM.toEnergy s = z := LinearEquiv.apply_symm_apply _ _
  have hres : hM.toEnergy (Minv (g + H s + μ • M s)) = b + A z + μ • z := by
    simp only [map_add, map_smul, hM.inv_apply, hs]
    have ha := hM.energyEnd_apply (Minv ∘ₗ H) s
    rw [hs] at ha
    exact congrArg (fun w => b + w + μ • z) ha.symm
  simp only [algorithm_7_5_2, ite_eq_right hflag]
  change ∃ μ : ℝ, 0 ≤ μ ∧ energyNorm Minv (g + H s + μ • M s) = Lanczos.beta A b k * |y (Fin.last k)|
  refine ⟨μ, hμ.nonneg, ?_⟩
  unfold energyNorm
  rw [real_inner_comm, ← hM.norm_toEnergy_inv_sq, Real.sqrt_sq (norm_nonneg _), hres, hr]

/-- **Algorithm 7.5.2** of [conn2000trust], stopping scan. Let $M$, $M^{-1}$ be a preconditioner,
let $\Delta \ge 0$ and $\mathrm{tol} \in \mathbb{R}$, and let $d$ be the dimension of the Krylov
space of $M^{-1} H$ generated by $M^{-1} g$. If $\|g\| = 0$ and $\mathrm{tol} \ge 0$, the scan
returns $(0, 0)$. Otherwise it returns the first trial $(s, \rho)$ with index $k < d$ and
$\rho \le \mathrm{tol}$, and nothing if no such trial exists. -/
noncomputable def algorithm_7_5_2_until {H M Minv : E →ₗ[ℝ] E} (hM : IsPreconditioner M Minv)
    (g : E) (Δ : ℝ) (hΔ : 0 ≤ Δ) (tol : ℝ) : Option (E × ℝ) :=
  let m := grade (hM.energyEnd (Minv ∘ₗ H)) (hM.toEnergy (Minv g))
  let trial := algorithm_7_5_2 hM (H := H) g Δ hΔ
  if ‖g‖ = 0 ∧ 0 ≤ tol then some (0, 0)
  else ((List.ofFn (id : Fin m → Fin m)).find? (fun k : Fin m =>
    decide ((trial k.val).2 ≤ tol))).map (fun k : Fin m => trial k.val)

/-- **Algorithm 7.5.2** of [conn2000trust], returned step. Let $E$ be finite-dimensional, let $M$,
$M^{-1}$ be a preconditioner, and let $\Delta \ge 0$. If the stopping scan with tolerance
$\mathrm{tol}$ returns $(s, \rho)$, then
$$\|s\|_M \le \Delta \qquad \text{and} \qquad \rho \le \mathrm{tol}.$$
-/
theorem algorithm_7_5_2_until_spec [FiniteDimensional ℝ E] {H M Minv : E →ₗ[ℝ] E}
    (hM : IsPreconditioner M Minv) (g : E) (Δ : ℝ) (hΔ : 0 ≤ Δ) (tol : ℝ)
    {s : E × ℝ} (hs : algorithm_7_5_2_until hM (H := H) g Δ hΔ tol = some s) :
    energyNorm M s.1 ≤ Δ ∧ s.2 ≤ tol := by
  unfold algorithm_7_5_2_until at hs
  split at hs
  · rename_i h
    cases hs
    exact ⟨by simpa [energyNorm] using hΔ, h.2⟩
  · obtain ⟨k, hk, htrial⟩ := Option.map_eq_some_iff.mp hs
    subst s
    exact ⟨algorithm_7_5_2_feasible hM (H := H) g Δ hΔ k (Nat.succ_le_of_lt k.isLt),
      of_decide_eq_true (List.find?_some (p := fun j : Fin
        (grade (hM.energyEnd (Minv ∘ₗ H)) (hM.toEnergy (Minv g))) =>
          decide ((algorithm_7_5_2 hM (H := H) g Δ hΔ j.val).2 ≤ tol)) hk)⟩

/-- The last trial at the first invariant Krylov subspace has residual norm $0$, whether the
algorithm stayed with PCG or switched to the reduced problem. -/
private theorem gltr_last_residual_zero [FiniteDimensional ℝ E] {H M Minv : E →ₗ[ℝ] E}
    (hM : IsPreconditioner M Minv) (hH : H.IsSymmetric) (g : E) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (k : ℕ) (hk : grade (hM.energyEnd (Minv ∘ₗ H)) (hM.toEnergy (Minv g)) = k + 1) :
    (algorithm_7_5_2 hM (H := H) g Δ hΔ k).2 = 0 := by
  let : FiniteDimensional ℝ hM.EnergySpace :=
    FiniteDimensional.of_injective hM.toEnergy.symm.toLinearMap hM.toEnergy.symm.injective
  let A := hM.energyEnd (Minv ∘ₗ H)
  let b := hM.toEnergy (Minv g)
  let cg := CG.iterate A (-b) 0
  let pcg := PCG.iterate H Minv (-g) 0
  have hgrade : grade A (-b) = k + 1 := by
    rw [← neg_one_smul ℝ b, grade_smul A b (by norm_num : (-1 : ℝ) ≠ 0)]
    exact hk
  have hA : A.IsSymmetric := gltrEnergySymmetric hM hH
  unfold algorithm_7_5_2
  split
  · rename_i hflag
    have hp (j : ℕ) (hj : j < k + 1) : 0 < ⟪A (cg j).p, (cg j).p⟫ := by
      have hjp : hM.toEnergy (pcg j).p = (cg j).p := by
        simpa [pcg, cg, A, b] using
          (PCG.iterate_eq_CG_iterate_withEnergy H Minv (-g) 0 hM j).2.2.1
      rw [← hjp, hM.inner_energyEnd_left H]
      exact (hflag j hj).1
    have hgal := CG.isGalerkinIterate_of_pos_prefix (-b) 0 hA hp
    have hx := hgal.apply_eq_of_grade_le (by simp [hgrade])
    have hcg : (cg (k + 1)).r = 0 := by
      change (CG.iterate A (-b) 0 (k + 1)).r = 0
      rw [CG.residual_eq, hx, sub_self]
    have hpcg : hM.toEnergy (Minv (pcg (k + 1)).r) = 0 := by
      have hr : hM.toEnergy (Minv (pcg (k + 1)).r) = (cg (k + 1)).r := by
        simpa [pcg, cg, A, b] using
          (PCG.iterate_eq_CG_iterate_withEnergy H Minv (-g) 0 hM (k + 1)).2.1
      exact hr.trans hcg
    change energyNorm Minv (pcg (k + 1)).r = 0
    unfold energyNorm
    rw [real_inner_comm, ← hM.norm_toEnergy_inv_sq, hpcg]
    simp
  · have hβ : Lanczos.beta A b k = 0 := (Lanczos.beta_eq_zero_iff (A := A) b k).2 hk.le
    simp [A, b] at hβ
    simp [hβ]

/-- **Algorithm 7.5.2** of [conn2000trust], finite termination. Let $E$ be finite-dimensional, let
$M$, $M^{-1}$ be a preconditioner, let $H$ be symmetric, and let $\Delta \ge 0$ and
$\mathrm{tol} \ge 0$. Then the stopping scan returns a trial.

The trial with index $d - 1$, where $d$ is the dimension of the Krylov space, has residual $0$,
both when the algorithm stays with PCG and when it switches to the reduced problem. A zero
gradient returns the zero step. -/
theorem algorithm_7_5_2_until_terminates [FiniteDimensional ℝ E] {H M Minv : E →ₗ[ℝ] E}
    (hM : IsPreconditioner M Minv) (hH : H.IsSymmetric) (g : E) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    {tol : ℝ} (htol : 0 ≤ tol) :
    ∃ s, algorithm_7_5_2_until hM (H := H) g Δ hΔ tol = some s := by
  let : FiniteDimensional ℝ hM.EnergySpace :=
    FiniteDimensional.of_injective hM.toEnergy.symm.toLinearMap hM.toEnergy.symm.injective
  let A := hM.energyEnd (Minv ∘ₗ H)
  let b := hM.toEnergy (Minv g)
  let m := grade A b
  by_cases hg : g = 0
  · exact ⟨(0, 0), by simp [algorithm_7_5_2_until, hg, htol]⟩
  have hb : b ≠ 0 := by
    intro hz
    have hm : Minv g = 0 := hM.toEnergy.injective (by simpa [b] using hz)
    exact hg (by simpa [hm] using (hM.apply_inv g).symm)
  have hm : 0 < m := grade_pos_of_ne_zero A b hb
  let k : Fin m := ⟨m - 1, by omega⟩
  have hk : m = k.val + 1 := by dsimp [k]; omega
  let trial := algorithm_7_5_2 hM (H := H) g Δ hΔ
  let test : Fin m → Bool := fun i => decide ((trial i.val).2 ≤ tol)
  have htest : test k = true := by
    change decide ((trial k.val).2 ≤ tol) = true
    rw [decide_eq_true_eq, gltr_last_residual_zero hM hH g Δ hΔ k.val hk]
    exact htol
  unfold algorithm_7_5_2_until
  dsimp only
  rw [ite_eq_right (fun h => hg (norm_eq_zero.mp h.1))]
  change ∃ s, ((List.ofFn (id : Fin m → Fin m)).find? test).map (fun i => trial i.val) = some s
  cases hfind : (List.ofFn (id : Fin m → Fin m)).find? test with
  | none => exact ((List.find?_eq_none.mp hfind k (by simp)) htest).elim
  | some i => exact ⟨trial i.val, rfl⟩

end ConnGouldToint.Chapter07
