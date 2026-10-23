import Numlib.Optimization.HighOrder.ConstrainedCriticality
/-!
# Taylor criticality on arbitrary displacement sets

The supremum is taken over the actual allowed displacements in a bounded ball.
Boundedness comes from the enclosing ball, so the displacement set need not be
closed or convex. Every admissible decrement is bounded by this supremum.
-/

namespace TaylorModel
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
/-- Actual Taylor criticality over an arbitrary set of allowed displacements. -/
noncomputable def restrictedCriticality (f : E → ℝ) (j : ℕ) (V : Set E) (x : E) (δ : ℝ) : ℝ :=
  sSup ((decrement f j x) '' (V ∩ Metric.closedBall 0 δ))
variable [ProperSpace E]
/-- Every allowed Taylor decrement lies below the bounded criticality supremum. -/
theorem decrement_le_restrictedCriticality (f : E → ℝ) (j : ℕ) (V : Set E) (x : E)
    {δ : ℝ} {d : E} (hdV : d ∈ V) (hd : ‖d‖ ≤ δ) :
    decrement f j x d ≤ restrictedCriticality f j V x δ := by
  have hb := ((isCompact_closedBall (0 : E) δ).image
    (continuous_decrement f j x)).bddAbove
  exact le_csSup (hb.mono (Set.image_mono Set.inter_subset_right))
    ⟨d, ⟨hdV, by simpa using hd⟩, rfl⟩
end TaylorModel
