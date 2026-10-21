import Numlib.Optimization.HigherOrderRegularization
import Mathlib.Data.Finset.Max

/-!
# Families of Lipschitz derivative bounds

A smooth scalar objective may have distinct Lipschitz constants at every positive derivative
order. The family reuses the diagonal Taylor remainder interface order by order; its finite
maximum gives a common bound without introducing an assumption on the objective itself.
-/

noncomputable section
namespace Optimization
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A smooth objective with actual diagonal Lipschitz bounds at every positive active order. -/
structure HigherOrderDerivativeFamily (f : E → ℝ) (p : ℕ) (L : ℕ → ℝ) : Prop where
  smooth : ContDiff ℝ p f
  nonneg : ∀ j, 1 ≤ j → j ≤ p → 0 ≤ L j
  bound : ∀ j, 1 ≤ j → j ≤ p → ∀ x y d,
    ‖(iteratedFDeriv ℝ j f x - iteratedFDeriv ℝ j f y) (fun _ => d)‖ ≤
      L j * ‖x - y‖ * ‖d‖ ^ j

namespace HigherOrderDerivativeFamily

/-- The maximum of the positive-order constants; the empty-order convention is one. -/
def maxConstant (p : ℕ) (L : ℕ → ℝ) : ℝ :=
  if hp : 1 ≤ p then (Finset.Icc 1 p).sup' ⟨1, by simp [hp]⟩ L else 1

/-- Every active constant is bounded by the maximum. -/
theorem le_maxConstant {p j : ℕ} (L : ℕ → ℝ) (hj : 1 ≤ j) (hjp : j ≤ p) :
    L j ≤ maxConstant p L := by
  have hp : 1 ≤ p := hj.trans hjp
  simp only [maxConstant, dite_eq_left hp]
  exact Finset.le_sup' L (by simp [hj, hjp])

/-- A family gives the existing single-order diagonal Lipschitz interface. -/
theorem at_order {f : E → ℝ} {p : ℕ} {L : ℕ → ℝ}
    (hf : HigherOrderDerivativeFamily f p L) {j : ℕ} (hj : 1 ≤ j) (hjp : j ≤ p) :
    HigherOrderRegularization.DiagonalLipschitz f j (L j) :=
  ⟨hf.smooth.of_le (by exact_mod_cast hjp), hf.nonneg j hj hjp, hf.bound j hj hjp⟩

/-- Restricting the highest requested order preserves all actual derivative bounds. -/
theorem mono {f : E → ℝ} {p q : ℕ} {L : ℕ → ℝ}
    (hf : HigherOrderDerivativeFamily f p L) (hqp : q ≤ p) :
    HigherOrderDerivativeFamily f q L :=
  ⟨hf.smooth.of_le (by exact_mod_cast hqp),
    fun j hj hjq => hf.nonneg j hj (hjq.trans hqp),
    fun j hj hjq => hf.bound j hj (hjq.trans hqp)⟩

/-- The finite maximum of the family's constants is nonnegative. -/
theorem maxConstant_nonneg {f : E → ℝ} {p : ℕ} {L : ℕ → ℝ}
    (hf : HigherOrderDerivativeFamily f p L) : 0 ≤ maxConstant p L := by
  by_cases hp : 1 ≤ p
  · exact (hf.nonneg 1 le_rfl hp).trans (le_maxConstant L le_rfl hp)
  · simp [maxConstant, hp]

/-- Every active derivative can use the common maximum constant. -/
theorem at_order_max {f : E → ℝ} {p : ℕ} {L : ℕ → ℝ}
    (hf : HigherOrderDerivativeFamily f p L) {j : ℕ} (hj : 1 ≤ j) (hjp : j ≤ p) :
    HigherOrderRegularization.DiagonalLipschitz f j (maxConstant p L) := by
  refine ⟨(hf.at_order hj hjp).smooth, hf.maxConstant_nonneg, fun x y d => ?_⟩
  exact (hf.bound j hj hjp x y d).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_maxConstant L hj hjp) (norm_nonneg _))
      (pow_nonneg (norm_nonneg _) _))

end HigherOrderDerivativeFamily
end Optimization
