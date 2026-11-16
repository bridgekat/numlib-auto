/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Optimization.Constrained.TwoPhase.HighOrder.Examples.Plane

/-!
# A Phase-2 run that never terminates

This module gives a run of Phase 2 of the two-phase method TPqp-GC of [cartis2022evaluation],
Algorithm 14.3.2 (`Constrained.IsHighOrderTargetRun`), that never terminates, although its inner
calls satisfy the end-criticality contract. The problem is posed on $\mathbb{R}^2$ with the simple
constraint set $X = \{x : |x_1| \le 3\}$, the objective $f(x) = x_2 - x_1$ and the equality
constraint $c(x) = 3/5 + x_2 \in \mathbb{R}^1$, with $q = 1$, $\theta = 3/5$ and the tolerances
$\varepsilon_j = 1$. The outer iterates are $x_k = (-\tfrac{24}{5} 2^{-k}, 0)$, the targets are
$t_k = \tfrac{16}{5} 2^{-k}$, all optimality radii are $1$, and the $k$-th inner call makes one
successful iteration, from $x_k$ to $x_{k+1}$ (`Constrained.HighOrderTargetSeq.oneStep`). The run
shows that the decreases used in the proof of Lemma 14.3.8 of [cartis2022evaluation] do not bound
the bad outer iterations (`CartisGouldToint.Chapter14.lemma_14_3_8_proof_gap_counterexample`).

With $a_k = \tfrac45 2^{-k}$, one has $f(x_{k+1}) = t_k - a_k$, so every outer iteration is in
$\mathcal{K}_b$, and the target update (14.3.35) gives $t_{k+1} = t_k - 2 a_k$. Each call ends at a
point that passes the criticality test (14.3.34) for the old target, because $\|\nabla \mu(x_{k+1},
t_k)\|^2 = \theta^2 + 2 a_k^2 - 2 \theta a_k \le \theta^2 + a_k^2 = \|r(x_{k+1}, t_k)\|^2$. Hence
the end-criticality contract `Constrained.HighOrderTargetSeq.IsEndCritContract` holds for all
constants with $\kappa_{\mathrm{uns}} + \kappa_{\mathrm{unc}} \ge 1$, and no inner iteration is
good. The test (14.3.34) fails at $x_{k+1}$ for the new target $t_{k+1}$, because the decrease along
$d = -e_2$ is $\theta + a_k > \sqrt{\theta^2 + a_k^2}$; so Phase 2 does not stop. The inner-test
contract `Constrained.HighOrderTargetSeq.IsInnerTestContract` fails for every admissible choice of
constants, since otherwise Phase 2 would terminate by
`Constrained.IsHighOrderTargetRun.complexity_of_innerTest`.

## Main definitions

* `Constrained.TwoPhaseExample.Drift.strip`, `Constrained.TwoPhaseExample.Drift.obj`,
  `Constrained.TwoPhaseExample.Drift.con`: the set $X$, the objective $f$ and the constraint $c$.
* `Constrained.TwoPhaseExample.Drift.iter`: the outer iterates $x_k$.
* `Constrained.TwoPhaseExample.Drift.seq`: the Phase-2 data with one-step inner calls.

## Main results

* `Constrained.TwoPhaseExample.Drift.isHighOrderTargetRun`: the data form a run of Phase 2 for every
  $\beta \in (0, 3/5]$.
* `Constrained.TwoPhaseExample.Drift.not_stop`, `Constrained.TwoPhaseExample.Drift.before`: the run
  never terminates, and every outer iteration is reached.
* `Constrained.TwoPhaseExample.Drift.isEndCritContract`: the inner calls satisfy the end-criticality
  contract for all constants with $\kappa_{\mathrm{uns}} + \kappa_{\mathrm{unc}} \ge 1$.
* `Constrained.TwoPhaseExample.Drift.not_isInnerTestContract`: the inner calls satisfy no inner-test
  contract with admissible constants.
* `Constrained.TwoPhaseExample.Drift.badCount_eq`: $K - 1$ of the outer iterations before $K$ are
  bad.

## Implementation notes

* The coordinates $x_1$ and $x_2$ of $x \in \mathbb{R}^2$ are `x 0` and `x 1`. The constraint takes
  values in $\mathbb{R}^1$ as a multiple of `Constrained.TwoPhaseExample.unitVec`.
* All results take $q = 1$, $\theta = 3/5$ and the tolerances `fun _ => 1`.
-/

open Set Metric
open scoped RealInnerProductSpace

namespace Constrained.TwoPhaseExample.Drift

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

local notation "ℝ¹" => EuclideanSpace ℝ (Fin 1)

/-- The simple constraint set $X = \{x \in \mathbb{R}^2 : |x_1| \le 3\}$, a closed strip. -/
def strip : Set ℝ² := {x | |x 0| ≤ 3}

/-- The objective $f(x) = x_2 - x_1$ on $\mathbb{R}^2$.

It is the linear objective `Constrained.TwoPhaseExample.linObj (-1) 1`. -/
def obj : ℝ² → ℝ := linObj (-1) 1

/-- The equality constraint $c(x) = 3/5 + x_2$, with values in $\mathbb{R}^1$.

It is $x \mapsto (3/5 + x_2)\, e$, with $e$ the unit vector
`Constrained.TwoPhaseExample.unitVec`. -/
noncomputable def con : ℝ² → ℝ¹ := fun x => (3 / 5 + x 1) • unitVec

/-- The outer iterates $x_k = (-\tfrac{24}{5} 2^{-k}, 0)$ for $k \in \mathbb{N}$.

Phase 2 starts at $x_1 = (-12/5, 0)$; the value at $k = 0$ is not used. -/
noncomputable def iter (k : ℕ) : ℝ² := pt (-(24 / 5) * (1 / 2) ^ k) 0

/-- The Phase-2 data of the run: the outer iterates $x_k$ of
`Constrained.TwoPhaseExample.Drift.iter`, the targets $t_k = \tfrac{16}{5} 2^{-k}$, all
optimality radii equal to $1$, and for each $k$ an inner call that makes one successful
iteration, from $x_k$ to $x_{k+1}$.

It is `Constrained.HighOrderTargetSeq.oneStep`. -/
noncomputable def seq : HighOrderTargetSeq ℝ² :=
  HighOrderTargetSeq.oneStep iter fun k => 16 / 5 * (1 / 2) ^ k

/-- $f(y) = y_2 - y_1$ for $y \in \mathbb{R}^2$. -/
theorem obj_apply (y : ℝ²) : obj y = y 1 - y 0 := by simp [obj, linObj]; ring

/-- The second coordinate of every iterate $x_k$ is $0$. -/
theorem iter_apply_one (k : ℕ) : iter k 1 = 0 := pt_one _ _

/-- The first coordinate of the iterate $x_k$ is $-\tfrac{24}{5} 2^{-k}$. -/
theorem iter_apply_zero (k : ℕ) : iter k 0 = -(24 / 5) * (1 / 2) ^ k := pt_zero _ _

/-- $f(x_k) = \tfrac{24}{5} 2^{-k}$ for every $k$. -/
theorem obj_iter (k : ℕ) : obj (iter k) = 24 / 5 * (1 / 2) ^ k := by
  rw [obj_apply, iter_apply_one, iter_apply_zero]; ring

/-- $\|c(y)\| = |3/5 + y_2|$ for $y \in \mathbb{R}^2$. -/
theorem norm_con (y : ℝ²) : ‖con y‖ = |3 / 5 + y 1| := norm_smul_unitVec _

/-- At every point $y$, the derivative of $c$ is the linear map $d \mapsto d_2\, e$, where $e$ is
the unit vector of $\mathbb{R}^1$. -/
theorem hasFDerivAt_con (y : ℝ²) :
    HasFDerivAt con ((EuclideanSpace.proj (1 : Fin 2) : ℝ² →L[ℝ] ℝ).smulRight unitVec) y := by
  have := ((hasFDerivAt_const (3 / 5 : ℝ) y).add
    (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 y 1)).smul_const unitVec
  exact this.congr_fderiv (ContinuousLinearMap.ext fun d => by simp)

/-- Let $y \in \mathbb{R}^2$ with $y_2 = 0$, and let $t \in \mathbb{R}$. The first-order Taylor
decrement of $\mu(\cdot, t)$ at $y$ along $d$ is
$$-\nabla \mu(y, t)[d] = (f(y) - t)\, d_1 - (f(y) - t + 3/5)\, d_2.$$
-/
theorem taylorDecrement_one {y : ℝ²} (hy : y 1 = 0) (t : ℝ) (d : ℝ²) :
    (ftaylorSeries ℝ (Constrained.targetMerit obj con t) y).taylorDecrement 1 d =
      (obj y - t) * d 0 - (obj y - t + 3 / 5) * d 1 := by
  rw [Constrained.taylorDecrement_one_targetMerit (f := obj) (hasFDerivAt_linObj _ _ y)
    (hasFDerivAt_con y)]
  simp [con, unitVec, hy, inner_smul_left, inner_smul_right]
  ring

/-- Let $y \in \mathbb{R}^2$ with $y_2 = 0$, let $t \in \mathbb{R}$, and let
$S \subseteq \mathbb{R}^2$ contain $0$. The first-order measure of $\mu(\cdot, t)$ at $y$ on $S$
with radius $1$ is at most $\sqrt{(f(y) - t)^2 + (f(y) - t + 3/5)^2}$, by the Cauchy–Schwarz
inequality. -/
theorem taylorMeasure_le {y : ℝ²} (hy : y 1 = 0) (t : ℝ) {S : Set ℝ²} (h0 : (0 : ℝ²) ∈ S) :
    Optimization.taylorMeasure (ftaylorSeries ℝ (Constrained.targetMerit obj con t) y) 1 1 S ≤
      √((obj y - t) ^ 2 + (obj y - t + 3 / 5) ^ 2) := by
  have := decrementMeasure_lin_le_sqrt (a := obj y - t) (b := -(obj y - t + 3 / 5))
    (Δ := (ftaylorSeries ℝ (Constrained.targetMerit obj con t) y).taylorDecrement 1)
    (fun d => by rw [taylorDecrement_one hy]; ring) h0
  rwa [neg_sq] at this

/-- Let $y \in \mathbb{R}^2$ with $y_2 = 0$, let $t \in \mathbb{R}$, and let
$S \subseteq \mathbb{R}^2$ contain $-e_2$. The first-order measure of $\mu(\cdot, t)$ at $y$ on
$S$ with radius $1$ is at least $f(y) - t + 3/5$, the decrease along $d = -e_2$. -/
theorem le_taylorMeasure {y : ℝ²} (hy : y 1 = 0) (t : ℝ) {S : Set ℝ²}
    (hS : EuclideanSpace.single 1 (-1) ∈ S) :
    obj y - t + 3 / 5 ≤
      Optimization.taylorMeasure (ftaylorSeries ℝ (Constrained.targetMerit obj con t) y) 1 1
        S := by
  have := Optimization.taylorDecrement_le_taylorMeasure
    (ftaylorSeries ℝ (Constrained.targetMerit obj con t) y) 1 (δ := 1)
    (d := EuclideanSpace.single 1 (-1)) ⟨by simp, hS⟩
  rw [taylorDecrement_one hy] at this
  simpa using this

/-- If $y_2 = 0$, then $\|r(y, t)\| = \sqrt{(3/5)^2 + (f(y) - t)^2}$ for every target $t$. -/
theorem targetResidual_eq {y : ℝ²} (hy : y 1 = 0) (t : ℝ) :
    Constrained.targetResidual obj con t y = √((3 / 5) ^ 2 + (obj y - t) ^ 2) := by
  rw [Constrained.targetResidual_def, norm_con, hy, add_zero, abs_of_pos (by norm_num)]

/-- For $q = 1$, the tolerances $\varepsilon_j = 1$ and the radii $1$, the criticality test
(14.3.34) at $y$ for the target $t$ holds if and only if
$\phi^1_{\mu, X(y), 1}(y, t) \le \|r(y, t)\|$. Here $\phi^1_{\mu, X(y), 1}(y, t)$ is the
first-order measure of $\mu(\cdot, t)$ at $y$ with radius $1$ on $X(y) = \{d : y + d \in X\}$. -/
theorem targetCrit_iff {y : ℝ²} {t : ℝ} :
    targetCrit obj con strip 1 (fun _ => 1) t y (fun _ => 1) ↔
      Optimization.taylorMeasure (ftaylorSeries ℝ (Constrained.targetMerit obj con t) y) 1 1
        {d | y + d ∈ strip} ≤ Constrained.targetResidual obj con t y := by
  simp [targetCrit, Constrained.targetCrit]

/-- For every $k$ and every $a$ with $|a| \le 3/5$, $|-\tfrac{24}{5} 2^{-(k+1)} + a| \le 3$. -/
private theorem abs_iter_add_le (k : ℕ) {a : ℝ} (ha : |a| ≤ 3 / 5) :
    |-(24 / 5) * (1 / 2) ^ (k + 1) + a| ≤ 3 := by
  have := abs_le.1 ha
  rw [abs_le]; constructor <;> nlinarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 2) k,
    pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1) (n := k),
    pow_succ (1 / 2 : ℝ) k]

/-- For every $k$, the iterate $x_{k+1}$ passes the criticality test (14.3.34) for the old target
$t_k$, with $q = 1$, the tolerances $\varepsilon_j = 1$ and the radii $1$. -/
theorem targetCrit_old (k : ℕ) :
    targetCrit obj con strip 1 (fun _ => 1) (16 / 5 * (1 / 2) ^ k) (iter (k + 1))
      (fun _ => 1) := by
  rw [targetCrit_iff]
  have h0 : (0 : ℝ²) ∈ {d | iter (k + 1) + d ∈ strip} := by
    simpa [strip, iter_apply_zero] using abs_iter_add_le k (a := 0) (by norm_num)
  refine (taylorMeasure_le (iter_apply_one _) _ h0).trans ?_
  rw [targetResidual_eq (iter_apply_one _), obj_iter]
  refine Real.sqrt_le_sqrt ?_
  have hw := pow_pos (by norm_num : (0 : ℝ) < 1 / 2) k
  have hw1 := pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1) (n := k)
  have e : (1 / 2 : ℝ) ^ (k + 1) = (1 / 2) ^ k / 2 := by rw [pow_succ]; ring
  rw [e]
  nlinarith

/-- For every $k$, the iterate $x_{k+1}$ fails the criticality test (14.3.34) for the new target
$t_{k+1}$, with $q = 1$, the tolerances $\varepsilon_j = 1$ and the radii $1$. -/
theorem not_targetCrit_new (k : ℕ) :
    ¬ targetCrit obj con strip 1 (fun _ => 1) (16 / 5 * (1 / 2) ^ (k + 1)) (iter (k + 1))
      (fun _ => 1) := by
  rw [targetCrit_iff, not_le]
  have hS : EuclideanSpace.single 1 (-1) ∈ {d | iter (k + 1) + d ∈ strip} := by
    have e : (EuclideanSpace.single (1 : Fin 2) (-1 : ℝ)) 0 = 0 := by simp
    simpa [strip, iter_apply_zero, e] using abs_iter_add_le k (a := 0) (by norm_num)
  refine lt_of_lt_of_le ?_ (le_taylorMeasure (iter_apply_one _) _ hS)
  rw [targetResidual_eq (iter_apply_one _), obj_iter]
  have hw := pow_pos (by norm_num : (0 : ℝ) < 1 / 2) (k + 1)
  rw [Real.sqrt_lt' (by nlinarith)]
  nlinarith

/-- If $y_2 = 0$, then $\|r(y, t)\| \ge 3/5 = \theta \varepsilon_0$ for every target $t$. -/
theorem le_targetResidual {y : ℝ²} (hy : y 1 = 0) (t : ℝ) :
    3 / 5 ≤ Constrained.targetResidual obj con t y := by
  rw [targetResidual_eq hy]
  calc (3 / 5 : ℝ) = √((3 / 5) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
    _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (obj y - t)])

/-- No outer iteration is in $\mathcal{K}_a$: for every $k$,
$\|r(x_{k+1}, t_k)\| \ge \theta \varepsilon_0$ with $\theta = 3/5$ and $\varepsilon_0 = 1$. -/
theorem not_isKa (k : ℕ) : ¬ seq.IsKa obj con (3 / 5) (fun _ => 1) k := by
  rw [Constrained.HighOrderTargetSeq.isKa_iff]
  rw [mul_one, not_lt]
  exact le_targetResidual (iter_apply_one _) _

/-- Every outer iteration $k$ is in $\mathcal{K}_b$, for $\theta = 3/5$ and $\varepsilon_0 = 1$. -/
theorem isKb (k : ℕ) : seq.IsKb obj con (3 / 5) (fun _ => 1) k := by
  refine ⟨by rw [mul_one]; exact le_targetResidual (iter_apply_one _) _, ?_⟩
  change obj (iter (k + 1)) < 16 / 5 * (1 / 2) ^ k
  rw [obj_iter, pow_succ]
  nlinarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 2) k]

/-- **Phase 2 never terminates.** For every outer iteration $k$, the termination test
`Constrained.HighOrderTargetSeq.Stop` of the data `Constrained.TwoPhaseExample.Drift.seq` fails,
for $q = 1$, $\theta = 3/5$ and the tolerances $\varepsilon_j = 1$.

Since $k \in \mathcal{K}_b$, Phase 2 could stop at $k$ only if the criticality test (14.3.34)
held at $(x_{k+1}, t_{k+1})$, and it fails there
(`Constrained.TwoPhaseExample.Drift.not_targetCrit_new`). -/
theorem not_stop (k : ℕ) : ¬ seq.Stop obj con strip 1 (3 / 5) (fun _ => 1) k := by
  rintro (⟨-, hb⟩ | ⟨-, hm⟩)
  · exact hb (isKb k)
  · exact not_targetCrit_new k hm

/-- Every outer iteration $K$ is reached: no outer iteration $j \in [1, K)$ terminates Phase 2, for
$q = 1$, $\theta = 3/5$ and the tolerances $\varepsilon_j = 1$. -/
theorem before (K : ℕ) : seq.Before obj con strip 1 (3 / 5) (fun _ => 1) K :=
  fun k _ _ => not_stop k

/-- No inner call contains a good iteration: for every $k$, the number of good iterations of the
$k$-th call is $0$, for $q = 1$, $\theta = 3/5$ and the tolerances $\varepsilon_j = 1$. -/
theorem goodCount_eq_zero (k : ℕ) : seq.goodCount obj con strip 1 (3 / 5) (fun _ => 1) k = 0 := by
  classical
  rw [Constrained.HighOrderTargetSeq.goodCount,
      Constrained.TargetFollowingSeq.goodCount_eq_zero_iff]
  rintro i - ⟨hi, -, h | h, -⟩
  · exact absurd h (by change ¬ i + 1 < 1; omega)
  · exact h (targetCrit_old k)

/-- The iterates $x_k$ with $k \ge 1$ lie in $X$. -/
theorem iter_mem {k : ℕ} (hk : 1 ≤ k) : iter k ∈ strip := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hk
  simpa [strip, iter_apply_zero] using abs_iter_add_le k (a := 0) (by norm_num)

/-- The objective $f$ is of class $C^\omega$ (analytic), which is `ContDiff ℝ ⊤`. -/
theorem contDiff_obj : ContDiff ℝ ⊤ obj := contDiff_linObj _ _

/-- The constraint $c$ is of class $C^\omega$ (analytic), which is `ContDiff ℝ ⊤`. -/
theorem contDiff_con : ContDiff ℝ ⊤ con := by
  have h1 : ContDiff ℝ ⊤ (fun x : ℝ² => 3 / 5 + x 1) :=
    contDiff_const.add (contDiff_piLp_apply (p := 2))
  exact h1.smul contDiff_const

/-- At every point $y$, the first derivative of $f$ has norm at most $2$. -/
theorem norm_iteratedFDeriv_obj_le (y : ℝ²) :
    ∀ i ∈ Finset.Icc 1 1, ‖iteratedFDeriv ℝ i obj y‖ ≤ 2 :=
  fun i hi => (norm_iteratedFDeriv_linObj_le (-1) 1 y i hi).trans (by norm_num)

/-- If $x \in X$ and $\|c(x)\| \le 1$, then $-5 \le f(x) \le 4$. -/
theorem obj_mem_Icc {x : ℝ²} (hxX : x ∈ strip) (hcx : ‖con x‖ ≤ 1) : -5 ≤ obj x ∧ obj x ≤ 4 := by
  rw [norm_con] at hcx
  have h0 := abs_le.1 (show |x 0| ≤ 3 from hxX)
  have h1 := abs_le.1 hcx
  rw [obj_apply]
  constructor <;> linarith

/-- **The data form a run of Phase 2.** Let $0 < \beta \le 3/5$. The data
`Constrained.TwoPhaseExample.Drift.seq` form a run of Phase 2
(`Constrained.IsHighOrderTargetRun`) for the objective $f$, the constraint $c$ and the set $X$,
from $x_1 = (-12/5, 0)$, with $q = 1$, $\theta = 3/5$, the constant $\beta$ and the tolerances
$\varepsilon_j = 1$.

The point $x_1$ is `iter 1`. It satisfies $\|c(x_1)\| = 3/5 = \theta \varepsilon_0$, so the
start condition $\|c(x_1)\| \le \theta \varepsilon_0$ holds with equality. -/
theorem isHighOrderTargetRun {β : ℝ} (hβ : 0 < β) (hβθ : β ≤ 3 / 5) :
    IsHighOrderTargetRun obj con strip 1 (3 / 5) β (fun _ => 1) (iter 1) seq := by
  have hc1 : ‖con (iter 1)‖ = 3 / 5 := by
    rw [norm_con, iter_apply_one, add_zero, abs_of_pos (by norm_num)]
  refine isHighOrderTargetRun_oneStep (by norm_num) (by norm_num) hβ hβθ (fun _ _ => one_pos)
    (fun _ _ => le_rfl) (iter_mem le_rfl) (by rw [hc1]; norm_num) ?_
    (fun k _ _ => iter_mem (by omega)) (fun k _ _ => Or.inr (Or.inl (isKb k).2))
    (fun k _ _ => ?_) (fun k _ _ => by simpa using le_targetResidual (iter_apply_one k) _)
    (fun k _ _ ha => absurd ha (not_isKa k)) (fun k _ _ _ => ?_)
  · change (16 / 5 : ℝ) * (1 / 2) ^ 1 = obj (iter 1) - √(1 ^ 2 - ‖con (iter 1)‖ ^ 2)
    rw [hc1, obj_iter, show (1 : ℝ) ^ 2 - (3 / 5) ^ 2 = (4 / 5) ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
    norm_num
  · change Constrained.targetMerit obj con (16 / 5 * (1 / 2) ^ k) (iter (k + 1)) ≤
      Constrained.targetMerit obj con (16 / 5 * (1 / 2) ^ k) (iter k)
    rw [Constrained.targetMerit_def, Constrained.targetMerit_def, norm_con, norm_con,
      iter_apply_one, iter_apply_one, obj_iter, obj_iter]
    have e : (1 / 2 : ℝ) ^ (k + 1) = (1 / 2) ^ k / 2 := by rw [pow_succ]; ring
    rw [e]
    have hw := pow_pos (by norm_num : (0 : ℝ) < 1 / 2) k
    nlinarith
  · change (16 / 5 : ℝ) * (1 / 2) ^ (k + 1) = 2 * obj (iter (k + 1)) - 16 / 5 * (1 / 2) ^ k
    rw [obj_iter, pow_succ]
    ring

/-- The set $X$ is closed. -/
theorem isClosed_strip : IsClosed strip :=
  isClosed_le (continuous_abs.comp (EuclideanSpace.proj (0 : Fin 2)).continuous) continuous_const

/-- **The end-criticality contract holds.** Let $\beta, \kappa_{\mathrm{decr}} \in \mathbb{R}$, let
$\pi_j$ be any exponents, and let $\kappa_{\mathrm{uns}}, \kappa_{\mathrm{unc}} \in \mathbb{R}$
satisfy $\kappa_{\mathrm{uns}} + \kappa_{\mathrm{unc}} \ge 1$. Then the inner calls of
`Constrained.TwoPhaseExample.Drift.seq` satisfy the end-criticality contract
`Constrained.HighOrderTargetSeq.IsEndCritContract` with these constants, for $q = 1$,
$\theta = 3/5$ and the tolerances $\varepsilon_j = 1$.

Each call makes one successful iteration and ends at a point that passes the criticality test
(14.3.34) for the old target (`Constrained.TwoPhaseExample.Drift.targetCrit_old`). So this
iteration is exempt from the decrease that the contract asks for, and the contract puts no
condition on $\beta$, $\kappa_{\mathrm{decr}}$ or $\pi$. -/
theorem isEndCritContract {β κdecr κuns κunc : ℝ} {π : ℕ → ℝ} (hκ : 1 ≤ κuns + κunc) :
    seq.IsEndCritContract obj con strip 1 (3 / 5) β (fun _ => 1) κdecr κuns κunc π :=
  HighOrderTargetSeq.isEndCritContract_oneStep hκ fun k _ _ => targetCrit_old k

/-- **No inner-test contract holds.** Let $0 < \beta \le 3/5$, $\kappa_{\mathrm{decr}} > 0$,
$\kappa_{\mathrm{uns}} \ge 0$ and $\kappa_{\mathrm{unc}} \in \mathbb{R}$, and let $\pi_j$ and
$\rho_j$ be families with $\pi_1 \ge 0$ and $\rho_1 \ge 0$. Then the inner calls of
`Constrained.TwoPhaseExample.Drift.seq` do not satisfy the inner-test contract
`Constrained.HighOrderTargetSeq.IsInnerTestContract` with these constants, for $q = 1$,
$\theta = 3/5$ and the tolerances $\varepsilon_j = 1$.

If they did, Phase 2 would terminate by
`Constrained.IsHighOrderTargetRun.complexity_of_innerTest`, applied with $B_f = 2$ and
$\tau = \eta / 4$, where $\eta = \theta (1 - \theta) \varepsilon_0 / (1 + \theta)$ is
`Constrained.kbMargin θ ε₀`. This contradicts `Constrained.TwoPhaseExample.Drift.not_stop`. -/
theorem not_isInnerTestContract {β κdecr κuns κunc : ℝ} {π ρ : ℕ → ℝ} (hβ : 0 < β)
    (hβθ : β ≤ 3 / 5) (hκ : 0 < κdecr) (hκuns : 0 ≤ κuns) (hπ : 0 ≤ π 1) (hρ : 0 ≤ ρ 1) :
    ¬ seq.IsInnerTestContract obj con strip 1 (3 / 5) β (fun _ => 1) κdecr κuns κunc π ρ := by
  intro hs
  have hI : ∀ {j : ℕ}, j ∈ Finset.Icc 1 1 → j = 1 := fun hj => by simpa using hj
  have hη : 0 < kbMargin (3 / 5) 1 := by rw [kbMargin_def]; norm_num
  obtain ⟨-, kε, hend, -⟩ := (isHighOrderTargetRun hβ hβθ).complexity_of_innerTest hs hκ hκuns
    (πmax := π 1) (M := 1) (fun l hl => by obtain rfl := hI hl; exact ⟨hπ, le_rfl⟩) one_pos
    (fun l hl => by obtain rfl := hI hl; simp) (fun z hz hcz => obj_mem_Icc hz hcz)
    (fun j hj => by obtain rfl := hI hj; exact hρ)
    (fun _ _ => (contDiff_obj.of_le le_top).contDiffAt)
    (fun _ _ => (contDiff_con.of_le le_top).contDiffAt) (fun y _ _ => norm_iteratedFDeriv_obj_le y)
    (div_pos hη (by norm_num : (0 : ℝ) < 4))
    (fun j hj => by obtain rfl := hI hj; simp; linarith)
  exact not_stop kε hend.2.1

/-- **Every outer iteration is bad.** For every $K \in \mathbb{N}$, the number of bad outer
iterations among $[1, K)$ is $K - 1$, for $q = 1$, $\theta = 3/5$ and the tolerances
$\varepsilon_j = 1$.

The difference $K - 1$ is the truncated subtraction of natural numbers, so the count is $0$ for
$K = 0$. -/
theorem badCount_eq (K : ℕ) : seq.badCount obj con strip 1 (3 / 5) (fun _ => 1) K = K - 1 := by
  classical
  rw [HighOrderTargetSeq.badCount, TargetFollowingSeq.badCount_eq_card_filter,
    Finset.filter_true_of_mem fun k _ => ⟨isKb k, goodCount_eq_zero k⟩, Nat.card_Ico]

end Constrained.TwoPhaseExample.Drift
