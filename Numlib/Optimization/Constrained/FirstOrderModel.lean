import Numlib.Optimization.Constrained.FirstOrderCriticality

/-!
# Actual constrained first-order model comparison

Feasible translations at the trial model coincide with original endpoint
displacements. The genuine derivative error therefore bounds the corresponding
constrained first-order criticality error.
-/

namespace TaylorModel
open Set
variable {E : Type*} [NormedAddCommGroup E]

/-- Translating feasible displacements twice is the actual endpoint translation. -/
theorem feasibleDisplacements_translate (C : Set E) (x s : E) :
    feasibleDisplacements (feasibleDisplacements C x) s =
      feasibleDisplacements C (x + s) := by
  ext d
  simp only [mem_feasibleDisplacements, add_assoc]

variable [InnerProductSpace ℝ E] [ProperSpace E]

/-- The actual first-order derivative error controls constrained criticality
on the common feasible displacement set of an iterate and its trial model. -/
theorem constrainedCriticality_one_le_model {f m : E → ℝ} {C : Set E}
    (hC : IsClosed C) {x s : E} (hxs : x + s ∈ C) :
    constrainedCriticality f 1 C (x + s) 1 ≤
      constrainedCriticality m 1 (feasibleDisplacements C x) s 1 +
        ‖fderiv ℝ f (x + s) - fderiv ℝ m s‖ := by
  obtain ⟨d, hd, hn, he⟩ := exists_decrement_eq_constrainedCriticality
    f 1 hC hxs zero_le_one
  rw [←he]
  have hM : IsClosed (feasibleDisplacements C x) :=
    hC.preimage (continuous_const.add continuous_id)
  have hmd : s + d ∈ feasibleDisplacements C x := by
    change x + (s + d) ∈ C
    simpa only [add_assoc] using hd
  have hmc := decrement_le_constrainedCriticality m 1 hM hmd hn
  have ht := (fderiv ℝ f (x + s) - fderiv ℝ m s).le_opNorm d
  have hb := ht.trans (mul_le_of_le_one_right (norm_nonneg _) hn)
  rw [decrement_one, inner_gradient_left] at hmc
  rw [decrement_one, inner_gradient_left]
  simp only [sub_apply, Real.norm_eq_abs] at hb
  linarith [(abs_le.mp hb).1]

end TaylorModel
