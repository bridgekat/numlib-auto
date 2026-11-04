/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.List.OfFn
import Numlib.Analysis.Matrix.ToEuclideanLin
import Numlib.Krylov.Preconditioned
import Numlib.Optimization.Subproblem.Krylov

/-!
# Generalized Lanczos trust-region iteration

Algorithm 7.5.2 of [conn2000trust], with the independent Lanczos recurrence
for the reduced matrix, as suggested in the text when PCG curvature vanishes.
-/

namespace ConnGouldToint.Chapter07

open Krylov Subproblem Matrix WithLp
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The interior flag is set exactly while every accepted PCG trial has
positive curvature and remains strictly inside the trust region. Testing
curvature directly also covers a zero denominator before division. -/
def gltrInterior (H M Minv : E →ₗ[ℝ] E) (g : E) (Δ : ℝ) (k : ℕ) : Prop :=
  ∀ j < k, let s := PCG.iterate H Minv (-g) 0 j
    0 < ⟪H s.p, s.p⟫ ∧ energyNorm M (PCG.iterate H Minv (-g) 0 (j + 1)).x < Δ

/-- A failed interior test permanently switches to the reduced problem. -/
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

/-- One trial of Algorithm 7.5.2 returns the physical step and the residual
norm used by the stopping test. The reduced subproblem is solved exactly.
An interior trial uses the PCG update, and a reduced trial lifts the
minimizer through the preconditioned Lanczos basis. -/
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

/-- Up to the first invariant Krylov subspace, the trial returned by
Algorithm 7.5.2 is feasible in the preconditioner norm. -/
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

/-- The reduced residual reported by Algorithm 7.5.2 is the full shifted
residual norm at the lifted step, in the inverse-preconditioner metric. -/
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

/-- Scan the trials through the first invariant Krylov subspace and return
the first whose residual norm meets the given stopping tolerance. -/
noncomputable def algorithm_7_5_2_until {H M Minv : E →ₗ[ℝ] E} (hM : IsPreconditioner M Minv)
    (g : E) (Δ : ℝ) (hΔ : 0 ≤ Δ) (tol : ℝ) : Option (E × ℝ) :=
  let m := grade (hM.energyEnd (Minv ∘ₗ H)) (hM.toEnergy (Minv g))
  let trial := algorithm_7_5_2 hM (H := H) g Δ hΔ
  if ‖g‖ = 0 ∧ 0 ≤ tol then some (0, 0)
  else ((List.ofFn (id : Fin m → Fin m)).find? (fun k : Fin m =>
    decide ((trial k.val).2 ≤ tol))).map (fun k : Fin m => trial k.val)

/-- Every returned trial is feasible and meets the chosen stopping tolerance. -/
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

/-- The last trial at the first invariant Krylov space has zero stopping
residual, whether the algorithm stayed in PCG or switched to Lanczos. -/
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

/-- With a nonnegative tolerance the exact scan returns a trial by the
first invariant subspace. A zero starting gradient returns the zero step. -/
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
