import Numlib.Analysis.InnerProductSpace.PiL2
import Numlib.Optimization.ModelBased.HighOrder.MeasureTest
import Numlib.Optimization.Constrained.TwoPhase.HighOrder.OneStep

/-!
# Points, linear objectives and linear decrements on `ℝ²`

Elementary data on `EuclideanSpace ℝ (Fin 2)` shared by the two-dimensional examples of runs of
high-order target-following methods
(`Numlib.Optimization.Constrained.TwoPhase.HighOrder.Examples.*`): the point `(a, b)`, the unit
vector of `ℝ¹`, linear objectives `x ↦ a x₁ + b x₂`, and bounds on the measure
`Optimization.decrementMeasure` of a linear decrement with radius `1`.

## Main definitions

* `Constrained.TwoPhaseExample.pt a b`: the point `(a, b)` of `ℝ²`;
* `Constrained.TwoPhaseExample.unitVec`: the unit vector of `ℝ¹`;
* `Constrained.TwoPhaseExample.linObj a b`: the linear objective `x ↦ a x₁ + b x₂`.

## Main results

* `Constrained.TwoPhaseExample.decrementMeasure_lin_le`,
  `Constrained.TwoPhaseExample.decrementMeasure_lin_le_sqrt`: the measure of `d ↦ a d₁ + b d₂`
  with radius `1` is at most `|a| + |b|` and `√(a² + b²)`;
* `Constrained.TwoPhaseExample.isApproxMeasureStep_lin`: a displacement achieving half of
  `|a| + |b|` is a `1/2`-approximate measure step.
-/

open Set Metric
open scoped RealInnerProductSpace

namespace Constrained.TwoPhaseExample

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

local notation "ℝ¹" => EuclideanSpace ℝ (Fin 1)

/-- The point `(a, b)` of `ℝ²` (Mathlib's `!₂[a, b]`). -/
noncomputable def pt (a b : ℝ) : ℝ² := !₂[a, b]

@[simp] theorem pt_zero (a b : ℝ) : pt a b 0 = a := rfl

@[simp] theorem pt_one (a b : ℝ) : pt a b 1 = b := rfl

theorem pt_add (a b : ℝ) (d : ℝ²) : pt a b + d = pt (a + d 0) (b + d 1) := by
  ext i; fin_cases i <;> simp

theorem pt_add_pt (a b a' b' : ℝ) : pt a b + pt a' b' = pt (a + a') (b + b') := by
  rw [pt_add]; simp

theorem pt_sub (a b a' b' : ℝ) : pt a b - pt a' b' = pt (a - a') (b - b') := by
  ext i; fin_cases i <;> simp

/-- `⟪(a, b), d⟫ = a d₁ + b d₂`. -/
theorem inner_pt (a b : ℝ) (d : ℝ²) : ⟪pt a b, d⟫ = a * d 0 + b * d 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two, mul_comm]

/-- `‖(a, b)‖ = √(a² + b²)`. -/
theorem norm_pt (a b : ℝ) : ‖pt a b‖ = √(a ^ 2 + b ^ 2) := by
  simp [EuclideanSpace.norm_eq, Fin.sum_univ_two]

/-- `‖(a, b)‖² = a² + b²`. -/
theorem norm_pt_sq (a b : ℝ) : ‖pt a b‖ ^ 2 = a ^ 2 + b ^ 2 :=
  EuclideanSpace.norm_sq_eq_fin_two (pt a b)

/-- `‖(a, b)‖ ≤ |a| + |b|`. -/
theorem norm_pt_le_add (a b : ℝ) : ‖pt a b‖ ≤ |a| + |b| := by
  rw [norm_pt, Real.sqrt_le_left (by positivity)]
  nlinarith [sq_abs a, sq_abs b, mul_nonneg (abs_nonneg a) (abs_nonneg b)]

/-- `‖(a, b)‖ ≤ 1` for `|a|, |b| ≤ 1/2`. -/
theorem norm_pt_le {a b : ℝ} (ha : |a| ≤ 1 / 2) (hb : |b| ≤ 1 / 2) : ‖pt a b‖ ≤ 1 :=
  (norm_pt_le_add a b).trans (by linarith)

/-- The unit vector of `ℝ¹`. -/
noncomputable def unitVec : ℝ¹ := EuclideanSpace.single 0 1

theorem norm_smul_unitVec (r : ℝ) : ‖r • unitVec‖ = |r| := by simp [unitVec, norm_smul]

/-- The linear objective `x ↦ a x₁ + b x₂`. -/
def linObj (a b : ℝ) (x : ℝ²) : ℝ := a * x 0 + b * x 1

theorem linObj_pt (a b u v : ℝ) : linObj a b (pt u v) = a * u + b * v := by simp [linObj]

theorem hasFDerivAt_linObj (a b : ℝ) (y : ℝ²) :
    HasFDerivAt (linObj a b) (a • EuclideanSpace.proj (0 : Fin 2) +
      b • EuclideanSpace.proj (1 : Fin 2) : ℝ² →L[ℝ] ℝ) y :=
  ((PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 y 0).const_smul a).add
    ((PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 y 1).const_smul b)

theorem contDiff_linObj (a b : ℝ) : ContDiff ℝ ⊤ (linObj a b) :=
  (contDiff_const.mul (contDiff_piLp_apply (p := 2))).add
    (contDiff_const.mul (contDiff_piLp_apply (p := 2)))

/-- `‖∇(a x₁ + b x₂)‖ ≤ |a| + |b|`. -/
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

/-- A linear decrement `a d₁ + b d₂` is at most `|a| + |b|` on the unit ball. -/
theorem lin_le (a b : ℝ) {d : ℝ²} (hd : ‖d‖ ≤ 1) : a * d 0 + b * d 1 ≤ |a| + |b| := by
  have h0 : |d 0| ≤ 1 := by simpa [Real.norm_eq_abs] using (PiLp.norm_apply_le d 0).trans hd
  have h1 : |d 1| ≤ 1 := by simpa [Real.norm_eq_abs] using (PiLp.norm_apply_le d 1).trans hd
  have e0 : a * d 0 ≤ |a| := (le_abs_self _).trans (by
    rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg a) h0)
  have e1 : b * d 1 ≤ |b| := (le_abs_self _).trans (by
    rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg b) h1)
  linarith

/-- The measure of a linear decrement `d ↦ a d₁ + b d₂` with radius `1` is at most `|a| + |b|`. -/
theorem decrementMeasure_lin_le {Δ : ℝ² → ℝ} {a b : ℝ} (hΔ : ∀ d, Δ d = a * d 0 + b * d 1)
    {S : Set ℝ²} (h0 : (0 : ℝ²) ∈ S) : Optimization.decrementMeasure Δ 1 S ≤ |a| + |b| :=
  Optimization.decrementMeasure_le ⟨0, mem_closedBall_self zero_le_one, h0⟩ fun d hd => by
    rw [hΔ]; exact lin_le a b (mem_closedBall_zero_iff.1 hd.1)

/-- The measure of a linear decrement `d ↦ a d₁ + b d₂` with radius `1` is at most
`√(a² + b²)` (Cauchy–Schwarz, `Optimization.decrementMeasure_inner_le`). -/
theorem decrementMeasure_lin_le_sqrt {Δ : ℝ² → ℝ} {a b : ℝ} (hΔ : ∀ d, Δ d = a * d 0 + b * d 1)
    {S : Set ℝ²} (h0 : (0 : ℝ²) ∈ S) :
    Optimization.decrementMeasure Δ 1 S ≤ √(a ^ 2 + b ^ 2) := by
  have e : Δ = fun d => ⟪pt a b, d⟫ := funext fun d => by rw [hΔ, inner_pt]
  rw [e, ← norm_pt, ← one_mul ‖pt a b‖]
  exact Optimization.decrementMeasure_inner_le ⟨0, mem_closedBall_self zero_le_one, h0⟩

/-- **A witness for a linear decrement with `ς = 1/2`**: a feasible displacement `w` of norm at
most `1` whose decrease is at least `(|a| + |b|)/2` is a `1/2`-approximate measure step. -/
theorem isApproxMeasureStep_lin {Δ : ℝ² → ℝ} {a b : ℝ} (hΔ : ∀ d, Δ d = a * d 0 + b * d 1)
    {S : Set ℝ²} (h0 : (0 : ℝ²) ∈ S) {w : ℝ²} (hw : ‖w‖ ≤ 1) (hwS : w ∈ S)
    (hval : (|a| + |b|) / 2 ≤ Δ w) : Optimization.IsApproxMeasureStep Δ 1 S (1 / 2) w :=
  ⟨⟨mem_closedBall_zero_iff.2 hw, hwS⟩, by have := decrementMeasure_lin_le hΔ h0; linarith⟩

end Constrained.TwoPhaseExample
