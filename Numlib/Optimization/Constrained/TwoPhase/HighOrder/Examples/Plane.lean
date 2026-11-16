/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.InnerProductSpace.PiL2
import Numlib.Optimization.ModelBased.HighOrder.MeasureTest
import Numlib.Optimization.Constrained.TwoPhase.HighOrder.OneStep

/-!
# Points, linear objectives and linear decrements in the plane

This module collects elementary facts about the Euclidean plane $\mathbb{R}^2$
(`EuclideanSpace ℝ (Fin 2)`) that the two-dimensional examples of runs of high-order
target-following methods use, in particular
`Numlib.Optimization.Constrained.TwoPhase.HighOrder.Examples.Box` and
`Numlib.Optimization.Constrained.TwoPhase.HighOrder.Examples.Drift`. It defines the point $(a, b)$,
the unit vector of $\mathbb{R}^1$ and the linear objective $x \mapsto a x_1 + b x_2$. It bounds the
measure $\sup \{\Delta(d) : \|d\| \le 1,\ d \in S\}$ (`Optimization.decrementMeasure`) of a linear
decrement $\Delta(d) = a d_1 + b d_2$ with radius $1$ by $|a| + |b|$ and by $\sqrt{a^2 + b^2}$, and
it gives a witness for an approximate measure step of such a decrement.

## Main definitions

* `Constrained.TwoPhaseExample.pt`: the point $(a, b) \in \mathbb{R}^2$.
* `Constrained.TwoPhaseExample.unitVec`: the unit vector of $\mathbb{R}^1$.
* `Constrained.TwoPhaseExample.linObj`: the linear objective $x \mapsto a x_1 + b x_2$.

## Main results

* `Constrained.TwoPhaseExample.decrementMeasure_lin_le`: the measure of $d \mapsto a d_1 + b d_2$
  with radius $1$ is at most $|a| + |b|$.
* `Constrained.TwoPhaseExample.decrementMeasure_lin_le_sqrt`: the same measure is at most
  $\sqrt{a^2 + b^2}$.
* `Constrained.TwoPhaseExample.isApproxMeasureStep_lin`: a feasible displacement of norm at most $1$
  whose decrease is at least $(|a| + |b|)/2$ is a $\tfrac12$-approximate measure step.

## Implementation notes

* The coordinates $x_1$ and $x_2$ of $x \in \mathbb{R}^2$ are `x 0` and `x 1`.
-/

open Set Metric
open scoped RealInnerProductSpace

namespace Constrained.TwoPhaseExample

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

local notation "ℝ¹" => EuclideanSpace ℝ (Fin 1)

/-- The **point** $(a, b) \in \mathbb{R}^2$, with first coordinate $a$ and second coordinate $b$.

It is Mathlib's `!₂[a, b]` in `EuclideanSpace ℝ (Fin 2)`. -/
noncomputable def pt (a b : ℝ) : ℝ² := !₂[a, b]

/-- The first coordinate of $(a, b)$ is $a$. -/
@[simp] theorem pt_zero (a b : ℝ) : pt a b 0 = a := rfl

/-- The second coordinate of $(a, b)$ is $b$. -/
@[simp] theorem pt_one (a b : ℝ) : pt a b 1 = b := rfl

/-- For $d \in \mathbb{R}^2$, $(a, b) + d = (a + d_1, b + d_2)$. -/
theorem pt_add (a b : ℝ) (d : ℝ²) : pt a b + d = pt (a + d 0) (b + d 1) := by
  ext i; fin_cases i <;> simp

/-- $(a, b) + (a', b') = (a + a', b + b')$. -/
theorem pt_add_pt (a b a' b' : ℝ) : pt a b + pt a' b' = pt (a + a') (b + b') := by
  rw [pt_add]; simp

/-- $(a, b) - (a', b') = (a - a', b - b')$. -/
theorem pt_sub (a b a' b' : ℝ) : pt a b - pt a' b' = pt (a - a') (b - b') := by
  ext i; fin_cases i <;> simp

/-- For $d \in \mathbb{R}^2$, $\langle (a, b), d \rangle = a d_1 + b d_2$. -/
theorem inner_pt (a b : ℝ) (d : ℝ²) : ⟪pt a b, d⟫ = a * d 0 + b * d 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two, mul_comm]

/-- $\|(a, b)\| = \sqrt{a^2 + b^2}$. -/
theorem norm_pt (a b : ℝ) : ‖pt a b‖ = √(a ^ 2 + b ^ 2) := by
  simp [EuclideanSpace.norm_eq, Fin.sum_univ_two]

/-- $\|(a, b)\|^2 = a^2 + b^2$. -/
theorem norm_pt_sq (a b : ℝ) : ‖pt a b‖ ^ 2 = a ^ 2 + b ^ 2 :=
  EuclideanSpace.norm_sq_eq_fin_two (pt a b)

/-- $\|(a, b)\| \le |a| + |b|$. -/
theorem norm_pt_le_add (a b : ℝ) : ‖pt a b‖ ≤ |a| + |b| := by
  rw [norm_pt, Real.sqrt_le_left (by positivity)]
  nlinarith [sq_abs a, sq_abs b, mul_nonneg (abs_nonneg a) (abs_nonneg b)]

/-- If $|a| \le 1/2$ and $|b| \le 1/2$, then $\|(a, b)\| \le 1$. -/
theorem norm_pt_le {a b : ℝ} (ha : |a| ≤ 1 / 2) (hb : |b| ≤ 1 / 2) : ‖pt a b‖ ≤ 1 :=
  (norm_pt_le_add a b).trans (by linarith)

/-- The **unit vector** $e$ of $\mathbb{R}^1$: the vector whose only coordinate is $1$.

It is `EuclideanSpace.single 0 1`. The examples write a constraint with values in $\mathbb{R}^1$
as $x \mapsto r(x)\, e$ for a real function $r$. -/
noncomputable def unitVec : ℝ¹ := EuclideanSpace.single 0 1

/-- For $r \in \mathbb{R}$, $\|r e\| = |r|$, where $e$ is the unit vector of $\mathbb{R}^1$. -/
theorem norm_smul_unitVec (r : ℝ) : ‖r • unitVec‖ = |r| := by simp [unitVec, norm_smul]

/-- The **linear objective** $x \mapsto a x_1 + b x_2$ on $\mathbb{R}^2$, for $a, b \in \mathbb{R}$.
-/
def linObj (a b : ℝ) (x : ℝ²) : ℝ := a * x 0 + b * x 1

/-- The linear objective at the point $(u, v)$ has the value $a u + b v$. -/
theorem linObj_pt (a b u v : ℝ) : linObj a b (pt u v) = a * u + b * v := by simp [linObj]

/-- At every point $y \in \mathbb{R}^2$, the derivative of the linear objective
$x \mapsto a x_1 + b x_2$ is the linear map $d \mapsto a d_1 + b d_2$. -/
theorem hasFDerivAt_linObj (a b : ℝ) (y : ℝ²) :
    HasFDerivAt (linObj a b) (a • EuclideanSpace.proj (0 : Fin 2) +
      b • EuclideanSpace.proj (1 : Fin 2) : ℝ² →L[ℝ] ℝ) y :=
  ((PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 y 0).const_smul a).add
    ((PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 y 1).const_smul b)

/-- The linear objective $x \mapsto a x_1 + b x_2$ is of class $C^\omega$ (analytic), which is
`ContDiff ℝ ⊤`. -/
theorem contDiff_linObj (a b : ℝ) : ContDiff ℝ ⊤ (linObj a b) :=
  (contDiff_const.mul (contDiff_piLp_apply (p := 2))).add
    (contDiff_const.mul (contDiff_piLp_apply (p := 2)))

/-- At every point $y$, the first derivative of the linear objective $x \mapsto a x_1 + b x_2$ has
norm at most $|a| + |b|$. -/
theorem norm_iteratedFDeriv_linObj_le (a b : ℝ) (y : ℝ²) :
    ∀ i ∈ Finset.Icc 1 1, ‖iteratedFDeriv ℝ i (linObj a b) y‖ ≤ |a| + |b| := by
  intro i hi
  obtain rfl : i = 1 := by simpa using hi
  rw [norm_iteratedFDeriv_one, (hasFDerivAt_linObj a b y).fderiv]
  have h : ∀ j : Fin 2, ‖(EuclideanSpace.proj j : ℝ² →L[ℝ] ℝ)‖ ≤ 1 := fun j =>
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
      simpa using PiLp.norm_apply_le x j
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [norm_smul, Real.norm_eq_abs]
  · exact mul_le_of_le_one_right (abs_nonneg a) (h 0)
  · exact mul_le_of_le_one_right (abs_nonneg b) (h 1)

/-- If $d \in \mathbb{R}^2$ satisfies $\|d\| \le 1$, then $a d_1 + b d_2 \le |a| + |b|$. -/
theorem lin_le (a b : ℝ) {d : ℝ²} (hd : ‖d‖ ≤ 1) : a * d 0 + b * d 1 ≤ |a| + |b| := by
  have h0 : |d 0| ≤ 1 := by simpa [Real.norm_eq_abs] using (PiLp.norm_apply_le d 0).trans hd
  have h1 : |d 1| ≤ 1 := by simpa [Real.norm_eq_abs] using (PiLp.norm_apply_le d 1).trans hd
  have e0 : a * d 0 ≤ |a| := (le_abs_self _).trans (by
    rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg a) h0)
  have e1 : b * d 1 ≤ |b| := (le_abs_self _).trans (by
    rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg b) h1)
  linarith

/-- Let $\Delta : \mathbb{R}^2 \to \mathbb{R}$ be the linear decrement $\Delta(d) = a d_1 + b d_2$,
and let $S \subseteq \mathbb{R}^2$ contain $0$. The measure of $\Delta$ on $S$ with radius $1$
satisfies
$$\sup \{\Delta(d) : \|d\| \le 1,\ d \in S\} \le |a| + |b|.$$

The measure is `Optimization.decrementMeasure Δ 1 S`. The hypothesis $0 \in S$ makes the set
nonempty, so that the supremum is the least upper bound of a nonempty bounded set. -/
theorem decrementMeasure_lin_le {Δ : ℝ² → ℝ} {a b : ℝ} (hΔ : ∀ d, Δ d = a * d 0 + b * d 1)
    {S : Set ℝ²} (h0 : (0 : ℝ²) ∈ S) : Optimization.decrementMeasure Δ 1 S ≤ |a| + |b| :=
  Optimization.decrementMeasure_le ⟨0, mem_closedBall_self zero_le_one, h0⟩ fun d hd => by
    rw [hΔ]; exact lin_le a b (mem_closedBall_zero_iff.1 hd.1)

/-- Let $\Delta : \mathbb{R}^2 \to \mathbb{R}$ be the linear decrement $\Delta(d) = a d_1 + b d_2$,
and let $S \subseteq \mathbb{R}^2$ contain $0$. The measure of $\Delta$ on $S$ with radius $1$
satisfies
$$\sup \{\Delta(d) : \|d\| \le 1,\ d \in S\} \le \sqrt{a^2 + b^2}.$$

The measure is `Optimization.decrementMeasure Δ 1 S`. The bound is the Cauchy–Schwarz
inequality, in the form `Optimization.decrementMeasure_inner_le`. -/
theorem decrementMeasure_lin_le_sqrt {Δ : ℝ² → ℝ} {a b : ℝ} (hΔ : ∀ d, Δ d = a * d 0 + b * d 1)
    {S : Set ℝ²} (h0 : (0 : ℝ²) ∈ S) :
    Optimization.decrementMeasure Δ 1 S ≤ √(a ^ 2 + b ^ 2) := by
  have e : Δ = fun d => ⟪pt a b, d⟫ := funext fun d => by rw [hΔ, inner_pt]
  rw [e, ← norm_pt, ← one_mul ‖pt a b‖]
  exact Optimization.decrementMeasure_inner_le ⟨0, mem_closedBall_self zero_le_one, h0⟩

/-- A **witness for a linear decrement with $\varsigma = 1/2$**. Let $\Delta(d) = a d_1 + b d_2$,
let $S \subseteq \mathbb{R}^2$ contain $0$, and let $w \in S$ satisfy $\|w\| \le 1$ and
$\Delta(w) \ge (|a| + |b|)/2$. Then $w$ is a $\tfrac12$-approximate measure step of $\Delta$ on
$S$ with radius $1$: it is a feasible displacement whose decrease is at least half of the
measure of $\Delta$.

The conclusion is `Optimization.IsApproxMeasureStep Δ 1 S (1 / 2) w`. It follows from
`Constrained.TwoPhaseExample.decrementMeasure_lin_le`. -/
theorem isApproxMeasureStep_lin {Δ : ℝ² → ℝ} {a b : ℝ} (hΔ : ∀ d, Δ d = a * d 0 + b * d 1)
    {S : Set ℝ²} (h0 : (0 : ℝ²) ∈ S) {w : ℝ²} (hw : ‖w‖ ≤ 1) (hwS : w ∈ S)
    (hval : (|a| + |b|) / 2 ≤ Δ w) : Optimization.IsApproxMeasureStep Δ 1 S (1 / 2) w :=
  ⟨⟨mem_closedBall_zero_iff.2 hw, hwS⟩, by have := decrementMeasure_lin_le hΔ h0; linarith⟩

end Constrained.TwoPhaseExample
