import Numlib.Optimization.Constrained.TwoPhase.Geometry

/-!
# Two-phase constrained target geometry

Actual primitive ARp-CC inner executions imply all Phase2 residual, target and
reset-count invariants. Literal strict-reset and corrected closed-reset modes
are explicit. The general feasibility Phase1 execution remains separate.
-/

open Set
namespace CartisGouldToint

/-- The genuine Euclidean augmented residual `(c(x), f(x)−t)` in(7.2.4). -/
noncomputable abbrev targetResidual := @Constrained.TwoPhase.residual

/-- Legal fixed first-order settings for every actual ARp-CC inner execution. -/
abbrev twoPhaseInnerSettings := ConvexRegularization.Settings

/-- Actual outer points/targets and complete primitive inner arrays. -/
abbrev twoPhaseData := Constrained.TwoPhase.Data

/-- Primitive Phase2 executions, parameterized by the explicit reset guard.
`false` is the literal strict guard and `true` includes the equality boundary. -/
abbrev twoPhasePhaseTwoRun := @Constrained.TwoPhase.PhaseTwoRun

/-- The literal printed Phase2 execution has a strict residual reset guard. -/
abbrev twoPhaseLiteralPhaseTwoRun := @Constrained.TwoPhase.LiteralPhaseTwoRun

/-- The corrected Phase2 execution closes only the residual reset guard. -/
abbrev twoPhaseCorrectedPhaseTwoRun := @Constrained.TwoPhase.CorrectedPhaseTwoRun

/-- Actual reset indices among the first N outer returns, matching `K_a`. -/
noncomputable abbrev twoPhaseResetIndices := @Constrained.TwoPhase.resetIterations

/-- **Lemma7.2.3.** All Phase2 target and residual invariants follow from actual
inner model acceptance and the explicit reset/reflection formulas. The optional
objective-range bounds give the exact source target interval, including both
endpoints. Both literal and corrected reset modes satisfy these invariants. -/
theorem lemma_7_2_3 {n m p : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {C : Set (EuclideanSpace ℝ (Fin n))} {P : twoPhaseInnerSettings p}
    {ε₀ ε₁ θ β flow fup : ℝ} {D : twoPhaseData (EuclideanSpace ℝ (Fin n))}
    {N : ℕ} {closedReset : Bool}
    (h : twoPhasePhaseTwoRun closedReset f c C P ε₀ ε₁ θ D N) (hβ : ε₀ ≤ β)
    (hf : ∀ z ∈ C, ‖c z‖ ≤ β → flow ≤ f z ∧ f z ≤ fup) :
    (∀ i j, i ≤ j → j ≤ N → D.target j ≤ D.target i) ∧
      (∀ k ≤ N, 0 ≤ f (D.point k) - D.target k ∧
        ‖c (D.point k)‖ ≤ ε₀ ∧ f (D.point k) - D.target k ≤ ε₀ ∧
        flow - 1 ≤ D.target k ∧ D.target k ≤ fup) ∧
      (∀ k < N, Constrained.TwoPhase.ResetGuard closedReset f c ε₀ θ
        (D.target k) (D.point (k + 1)) →
        ‖targetResidual f c (D.target (k + 1)) (D.point (k + 1))‖ = ε₀ ∧
          (1 - θ) * ε₀ ≤ D.target k - D.target (k + 1)) ∧
      (∀ k < N, ¬Constrained.TwoPhase.ResetGuard closedReset f c ε₀ θ
        (D.target k) (D.point (k + 1)) → f (D.point (k + 1)) < D.target k →
        ‖targetResidual f c (D.target (k + 1)) (D.point (k + 1))‖ =
          ‖targetResidual f c (D.target k) (D.point (k + 1))‖ ∧
        ‖targetResidual f c (D.target k) (D.point (k + 1))‖ ≤ ε₀) := by
  refine ⟨fun _ _ hij hj => h.target_le hij hj, ?_, ?_, ?_⟩
  · intro k hk
    exact ⟨(h.invariants hk).1, (h.component_bounds hk).1, (h.component_bounds hk).2,
      h.target_bounds hβ hf hk⟩
  · intro k hk hr
    exact ⟨h.reset_residual hk hr, h.reset_drop hk hr⟩
  · exact fun _ hk hr hgap => h.reflection_residual hk hr hgap

/-- **Lemma7.2.4.** The exact source objective range bounds every actual outer
reset count by `(f_up−f_low+1)/(1−θ) ε₀⁻¹`, without assuming termination or a
reset decrease floor as part of the algorithm trace. -/
theorem lemma_7_2_4 {n m p : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {C : Set (EuclideanSpace ℝ (Fin n))} {P : twoPhaseInnerSettings p}
    {ε₀ ε₁ θ β flow fup : ℝ} {D : twoPhaseData (EuclideanSpace ℝ (Fin n))}
    {N : ℕ} {closedReset : Bool}
    (h : twoPhasePhaseTwoRun closedReset f c C P ε₀ ε₁ θ D N) (hβ : ε₀ ≤ β)
    (hf : ∀ z ∈ C, ‖c z‖ ≤ β → flow ≤ f z ∧ f z ≤ fup) :
    ((twoPhaseResetIndices closedReset f c ε₀ θ D N).card : ℝ) ≤
      (fup - flow + 1) / (1 - θ) * ε₀⁻¹ := h.card_resets_le hβ hf

end CartisGouldToint
