import Numlib.Optimization.HighOrder.CriticalityStability

/-!
# Taylor criticality on closed feasible sets

The feasible displacements from `x` satisfy the actual condition `x + d ∈ X`. Taylor
criticality is the supremum of genuine decrements over their intersection with a closed
ball. Closedness and feasibility give compact attainment and nonnegativity without
convexity or connectivity assumptions on `X`. The sharp local Taylor remainder gives
objective stability with an additive criticality allowance.
-/

open Set

namespace TaylorModel
variable {E : Type*} [NormedAddCommGroup E]

/-- The displacements preserving feasibility from `x`. -/
def feasibleDisplacements (X : Set E) (x : E) : Set E := {d | x + d ∈ X}

/-- Feasible-displacement membership is the actual translated constraint. -/
@[simp] theorem mem_feasibleDisplacements {X : Set E} {x d : E} :
    d ∈ feasibleDisplacements X x ↔ x + d ∈ X := Iff.rfl

/-- Zero displacement is feasible exactly at feasible points. -/
@[simp] theorem zero_mem_feasibleDisplacements {X : Set E} {x : E} :
    0 ∈ feasibleDisplacements X x ↔ x ∈ X := by simp [feasibleDisplacements]

variable [NormedSpace ℝ E]

/-- Taylor criticality restricted to genuine feasible displacements. -/
noncomputable def constrainedCriticality (f : E → ℝ) (p : ℕ) (X : Set E) (x : E) (δ : ℝ) : ℝ :=
  sSup ((decrement f p x) '' (feasibleDisplacements X x ∩ Metric.closedBall 0 δ))

variable [ProperSpace E]

omit [NormedSpace ℝ E] in
/-- Closed feasible displacements in a bounded ball form a compact set. -/
theorem isCompact_feasibleDisplacements_inter_closedBall {X : Set E} (hX : IsClosed X)
    (x : E) (δ : ℝ) : IsCompact (feasibleDisplacements X x ∩ Metric.closedBall 0 δ) := by
  exact (isCompact_closedBall (0 : E) δ).inter_left
    (hX.preimage (continuous_const.add continuous_id))

/-- At a feasible point the constrained Taylor criticality supremum is attained. -/
theorem exists_decrement_eq_constrainedCriticality (f : E → ℝ) (p : ℕ) {X : Set E}
    (hX : IsClosed X) {x : E} (hx : x ∈ X) {δ : ℝ} (hδ : 0 ≤ δ) :
    ∃ d : E, x + d ∈ X ∧ ‖d‖ ≤ δ ∧
      decrement f p x d = constrainedCriticality f p X x δ := by
  obtain ⟨d, hd, heq⟩ :=
    (isCompact_feasibleDisplacements_inter_closedBall hX x δ).exists_sSup_image_eq
    ⟨0, by simpa using hx, by simpa using hδ⟩ (continuous_decrement f p x).continuousOn
  exact ⟨d, hd.1, by simpa using hd.2, heq.symm⟩

/-- Each feasible Taylor decrement lies below the actual constrained criticality. -/
theorem decrement_le_constrainedCriticality (f : E → ℝ) (p : ℕ) {X : Set E}
    (hX : IsClosed X) {x d : E} (hfeas : x + d ∈ X) {δ : ℝ} (hd : ‖d‖ ≤ δ) :
    decrement f p x d ≤ constrainedCriticality f p X x δ := by
  exact le_csSup ((isCompact_feasibleDisplacements_inter_closedBall hX x δ).image
    (continuous_decrement f p x)).bddAbove ⟨d, ⟨hfeas, by simpa using hd⟩, rfl⟩

/-- At feasible points, zero displacement makes constrained criticality nonnegative. -/
theorem constrainedCriticality_nonneg (f : E → ℝ) (p : ℕ) {X : Set E} (hX : IsClosed X)
    {x : E} (hx : x ∈ X) {δ : ℝ} (hδ : 0 ≤ δ) : 0 ≤ constrainedCriticality f p X x δ := by
  simpa using decrement_le_constrainedCriticality f p hX (by simpa using hx) (d := 0)
    (by simpa using hδ)

/-- Zero constrained criticality means every feasible model decrement is nonpositive. -/
theorem constrainedCriticality_eq_zero_iff (f : E → ℝ) (p : ℕ) {X : Set E}
    (hX : IsClosed X) {x : E} (hx : x ∈ X) {δ : ℝ} (hδ : 0 ≤ δ) :
    constrainedCriticality f p X x δ = 0 ↔
      ∀ d : E, x + d ∈ X → ‖d‖ ≤ δ → decrement f p x d ≤ 0 := by
  constructor
  · intro h d hfeas hd
    simpa [h] using decrement_le_constrainedCriticality f p hX hfeas hd
  · intro h
    apply le_antisymm _ (constrainedCriticality_nonneg f p hX hx hδ)
    obtain ⟨d, hfeas, hd, heq⟩ := exists_decrement_eq_constrainedCriticality f p hX hx hδ
    rw [← heq]
    exact h d hfeas hd

omit [ProperSpace E] in
/-- With no constraints, constrained criticality equals ordinary Taylor criticality. -/
@[simp] theorem constrainedCriticality_univ (f : E → ℝ) (p : ℕ) (x : E) (δ : ℝ) :
    constrainedCriticality f p univ x δ = criticality f p x δ := by
  simp [constrainedCriticality, feasibleDisplacements, criticality]

/-- Constrained approximate criticality bounds true feasible objective decrease up to
the sharp local Taylor error, retaining an additive accuracy allowance. -/
theorem value_ge_of_constrainedCriticality {f : E → ℝ} {j : ℕ} (hj : 0 < j)
    {X D : Set E} (hX : IsClosed X) (hD : IsOpen D) (hf : ContDiffOn ℝ j f D) (x : E)
    {δ ε η L : ℝ} (hδ : 0 ≤ δ) (hball : Metric.closedBall x δ ⊆ D) (hL : 0 ≤ L)
    (hlip : ∀ u ∈ Metric.closedBall x δ, ∀ v ∈ Metric.closedBall x δ,
      ‖iteratedFDeriv ℝ j f u - iteratedFDeriv ℝ j f v‖ ≤ L * ‖u - v‖)
    (hcrit : constrainedCriticality f j X x δ ≤ ε * δ ^ j / j.factorial + η)
    {d : E} (hfeas : x + d ∈ X) (hd : ‖d‖ ≤ δ) :
    f x - ε * δ ^ j / j.factorial - η - L * ‖d‖ ^ (j + 1) / (j + 1).factorial ≤ f (x + d) := by
  have hb := value_ge_of_decrement_le hj hD hf x hδ hball hL hlip hd
    ((decrement_le_constrainedCriticality f j hX hfeas hd).trans hcrit)
  linarith

end TaylorModel
