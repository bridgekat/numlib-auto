import Numlib.Analysis.SpecialFunctions.Sqrt
import Numlib.Optimization.Constrained.TargetResidual
import Numlib.Optimization.Constrained.TwoPhase.HighOrder.Examples.Plane

/-!
# A two-dimensional problem on a square

The data of the examples of runs of high-order target-following methods in
`Numlib.Optimization.Constrained.TwoPhase.HighOrder.Examples.BoxBadIter` and
`Numlib.Optimization.Constrained.TwoPhase.HighOrder.Examples.BoxARqp`: on `ℝ²`, the simple
constraint set `X = [-1, 1]²`, the objectives `f_a(x) = x₁ - a x₂` and the equality constraint
`c(x) = x₁²/2 ∈ ℝ¹`. The first-order Taylor decrement of the merit function
`μ(·, t) = ½ ‖r(·, t)‖²` is explicit (`Constrained.TwoPhaseExample.Box.taylorDecrement_one`),
which bounds its first-order measure from above (Cauchy–Schwarz) and from below (along `-e₁`).

## Main definitions

* `Constrained.TwoPhaseExample.Box.square`: the square `[-1, 1]²`;
* `Constrained.TwoPhaseExample.Box.obj a`: the objective `x ↦ x₁ - a x₂`;
* `Constrained.TwoPhaseExample.Box.con`: the constraint `x ↦ x₁²/2`.
-/

open Set Metric
open scoped RealInnerProductSpace

namespace Constrained.TwoPhaseExample.Box

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

local notation "ℝ¹" => EuclideanSpace ℝ (Fin 1)

/-- The simple constraint square `X = [-1, 1]²`. -/
def square : Set ℝ² := {x | |x 0| ≤ 1 ∧ |x 1| ≤ 1}

/-- The objective `f_a(x) = x₁ - a x₂`. -/
def obj (a : ℝ) : ℝ² → ℝ := linObj 1 (-a)

/-- The constraint `c(x) = x₁²/2`. -/
noncomputable def con : ℝ² → ℝ¹ := fun x => (x 0 ^ 2 / 2) • unitVec

theorem obj_apply (a : ℝ) (y : ℝ²) : obj a y = y 0 - a * y 1 := by simp [obj, linObj]; ring

theorem obj_pt (a u v : ℝ) : obj a (pt u v) = u - a * v := by simp [obj_apply]

/-- `f(a, b) = a - b` for the objective `f = f_1` of this module. -/
theorem obj_one_pt (a b : ℝ) : obj 1 (pt a b) = a - b := by rw [obj_pt]; ring

/-- `(a, b) ∈ X` for `|a|, |b| ≤ 1`. -/
theorem pt_mem_square {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) : pt a b ∈ square := by
  simp only [square, mem_ofPred_eq, pt_zero, pt_one]; exact ⟨ha, hb⟩

/-- `‖c(y)‖ = y₁²/2`. -/
theorem norm_con (y : ℝ²) : ‖con y‖ = y 0 ^ 2 / 2 := by
  rw [con, norm_smul_unitVec, abs_of_nonneg (by positivity)]

/-- The derivative of `c`: `d ↦ y₁ d₁ e`. -/
theorem hasFDerivAt_con (y : ℝ²) :
    HasFDerivAt con ((y 0 • (EuclideanSpace.proj (0 : Fin 2) : ℝ² →L[ℝ] ℝ)).smulRight unitVec)
      y := by
  have h1 : HasFDerivAt (fun x : ℝ² => x 0 ^ 2 / 2)
      (y 0 • (EuclideanSpace.proj (0 : Fin 2) : ℝ² →L[ℝ] ℝ)) y := by
    have := ((PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 y 0).pow 2).mul_const (1 / 2 : ℝ)
    convert this using 1
    · funext x; ring
    · ext d; simp; ring
  exact h1.smul_const unitVec

/-- The first-order Taylor decrement of `μ(·, t)` at `y`:
`-∇μ(y, t)[d] = -(y₁³/2 + (f_a(y) - t)) d₁ + a (f_a(y) - t) d₂`. -/
theorem taylorDecrement_one (a : ℝ) (y : ℝ²) (t : ℝ) (d : ℝ²) :
    (ftaylorSeries ℝ (targetMerit (obj a) con t) y).taylorDecrement 1 d =
      -(y 0 ^ 3 / 2 + (obj a y - t)) * d 0 + a * (obj a y - t) * d 1 := by
  rw [taylorDecrement_one_targetMerit (f := obj a) (hasFDerivAt_linObj _ _ y)
    (hasFDerivAt_con y), obj_apply]
  simp [con, unitVec, inner_smul_left, inner_smul_right]
  ring

/-- An upper bound on the first-order measure with radius `1` (Cauchy–Schwarz). -/
theorem taylorMeasure_le (y : ℝ²) (t : ℝ) {S : Set ℝ²} (h0 : (0 : ℝ²) ∈ S) :
    Optimization.taylorMeasure (ftaylorSeries ℝ (targetMerit (obj 1) con t) y) 1 1 S ≤
      √((y 0 ^ 3 / 2 + (obj 1 y - t)) ^ 2 + (obj 1 y - t) ^ 2) := by
  have := decrementMeasure_lin_le_sqrt (a := -(y 0 ^ 3 / 2 + (obj 1 y - t))) (b := obj 1 y - t)
    (Δ := (ftaylorSeries ℝ (targetMerit (obj 1) con t) y).taylorDecrement 1)
    (fun d => by rw [taylorDecrement_one, one_mul]) h0
  rwa [neg_sq] at this

/-- A lower bound on the first-order measure with radius `1`, along `d = -e₁`. -/
theorem le_taylorMeasure (y : ℝ²) (t : ℝ) {S : Set ℝ²} (hS : EuclideanSpace.single 0 (-1) ∈ S) :
    y 0 ^ 3 / 2 + (obj 1 y - t) ≤
      Optimization.taylorMeasure (ftaylorSeries ℝ (targetMerit (obj 1) con t) y) 1 1
        S := by
  have := Optimization.taylorDecrement_le_taylorMeasure
    (ftaylorSeries ℝ (targetMerit (obj 1) con t) y) 1 (δ := 1)
    (d := EuclideanSpace.single 0 (-1)) ⟨by simp, hS⟩
  rw [taylorDecrement_one] at this
  simpa using this

/-- `‖r(y, t)‖² = (y₁²/2)² + (f_a(y) - t)²`. -/
theorem targetResidual_sq (a : ℝ) (y : ℝ²) (t : ℝ) :
    targetResidual (obj a) con t y ^ 2 = (y 0 ^ 2 / 2) ^ 2 + (obj a y - t) ^ 2 := by
  rw [Constrained.targetResidual_sq, norm_con]

/-- `X` is closed. -/
theorem isClosed_square : IsClosed square :=
  (isClosed_le (continuous_abs.comp (EuclideanSpace.proj (0 : Fin 2)).continuous)
    continuous_const).inter
  (isClosed_le (continuous_abs.comp (EuclideanSpace.proj (1 : Fin 2)).continuous)
    continuous_const)

/-- `X` is convex. -/
theorem convex_square : Convex ℝ square := by
  have e : square = (EuclideanSpace.proj (0 : Fin 2) : ℝ² →L[ℝ] ℝ) ⁻¹' Icc (-1) 1 ∩
      (EuclideanSpace.proj (1 : Fin 2) : ℝ² →L[ℝ] ℝ) ⁻¹' Icc (-1) 1 := by
    ext x; simp [square, abs_le]
  rw [e]
  exact ((convex_Icc _ _).linear_preimage
      (EuclideanSpace.proj (0 : Fin 2) : ℝ² →L[ℝ] ℝ).toLinearMap).inter
    ((convex_Icc _ _).linear_preimage
      (EuclideanSpace.proj (1 : Fin 2) : ℝ² →L[ℝ] ℝ).toLinearMap)

/-- `X ⊆ B(0, 2)`. -/
theorem square_subset_ball : square ⊆ ball 0 2 := by
  intro x hx
  obtain ⟨h0, h1⟩ := hx
  rw [mem_ball_zero_iff, EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.sqrt_lt' (by norm_num)]
  simp only [Real.norm_eq_abs, sq_abs]
  have := abs_le.1 h0
  have := abs_le.1 h1
  nlinarith

/-- `c` is smooth. -/
theorem contDiff_con : ContDiff ℝ ⊤ con := by
  have h : ContDiff ℝ ⊤ (fun x : ℝ² => x 0 ^ 2 / 2) :=
    ((contDiff_piLp_apply (p := 2) (i := (0 : Fin 2))).pow 2).div_const 2
  exact h.smul contDiff_const

/-- `f_a` is smooth. -/
theorem contDiff_obj (a : ℝ) : ContDiff ℝ ⊤ (obj a) := contDiff_linObj _ _

/-- `‖∇f_a‖ ≤ 2` for `|a| ≤ 1`. -/
theorem norm_iteratedFDeriv_obj_le {a : ℝ} (ha : |a| ≤ 1) (y : ℝ²) :
    ∀ i ∈ Finset.Icc 1 1, ‖iteratedFDeriv ℝ i (obj a) y‖ ≤ 2 := fun i hi =>
  (norm_iteratedFDeriv_linObj_le 1 (-a) y i hi).trans (by rw [abs_one, abs_neg]; linarith)


/-- `-2 ≤ f_a ≤ 2` on `X` for `|a| ≤ 1`. -/
theorem obj_mem_Icc {a : ℝ} (ha : |a| ≤ 1) {x : ℝ²} (hx : x ∈ square) :
    -2 ≤ obj a x ∧ obj a x ≤ 2 := by
  obtain ⟨h0, h1⟩ := hx
  have h2 : |a * x 1| ≤ 1 := by rw [abs_mul]; nlinarith [abs_nonneg a, abs_nonneg (x 1)]
  have := abs_le.1 h0
  have := abs_le.1 h2
  rw [obj_apply]
  constructor <;> linarith

end Constrained.TwoPhaseExample.Box
