import Numlib.Optimization.Constrained.FirstOrderCriticality

/-!
# Unit-radius constrained first-order certificates

Convexity preserves scaled feasible displacements. Actual first-order Taylor
linearity therefore transports any positive-radius normalized certificate to
the unit radius, with no interiority or unrestricted-gradient assumption.
-/

namespace TaylorModel
open Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The genuine first-order Taylor decrement is linear in displacement scaling. -/
theorem decrement_one_smul (f : E → ℝ) (x d : E) (t : ℝ) :
    decrement f 1 x (t • d) = t * decrement f 1 x d := by
  simp only [decrement_eq, eval_eq_sum, Finset.sum_range_succ, Finset.sum_range_zero,
    zero_add, iteratedFDeriv_one_apply]
  norm_num

end TaylorModel

namespace TaylorModel
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]

/-- On a closed convex feasible set, a normalized first-order certificate at
any legal positive radius implies the unit-radius constrained certificate. -/
theorem constrainedCriticality_one_unit_le_of_radius {f : E → ℝ} {X : Set E}
    (hX : IsClosed X) (hconv : Convex ℝ X) {x : E} (hx : x ∈ X)
    {δ ε : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hc : constrainedCriticality f 1 X x δ ≤ ε * δ) :
    constrainedCriticality f 1 X x 1 ≤ ε := by
  obtain ⟨d, hd, hn, he⟩ := exists_decrement_eq_constrainedCriticality f 1 hX hx zero_le_one
  have hfeas := hconv.add_smul_mem hx hd ⟨hδ.le, hδ1⟩
  have hnorm : ‖δ • d‖ ≤ δ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hδ]
    exact mul_le_of_le_one_right hδ.le hn
  have hb := (decrement_le_constrainedCriticality f 1 hX hfeas hnorm).trans hc
  rw [decrement_one_smul, he] at hb
  nlinarith

end TaylorModel
