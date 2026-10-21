import Numlib.Optimization.ExplicitRegularizationRefinementBounds

/-!
# Full outer-iteration bounds with explicit accuracy costs

The actual executed prefix partitions into trial and accuracy-only passes. Combining its
parameter-update budget with the geometric request budget retains the tolerance logarithm
in the additive term. No true-quality failure or observable termination is assumed.
-/

noncomputable section
namespace Optimization.ExplicitRegularization

variable {E : Type} [NormedAddCommGroup E]

/-- The entire executed prefix, including accuracy-only passes, is bounded by its actual
accepted count, a terminal parameter bound and an explicit refinement budget. -/
theorem Execution.iteration_count_le [NormedSpace ℝ E] {P : Parameters}
    {f : E → ℝ} {O : Oracle f P.p}
    {N : ℕ} (r : Execution P O N) {S R : ℝ} (hS : (r.state N).sigma ≤ S)
    (hR : (r.refinementCount N : ℝ) ≤ R) :
    (N : ℝ) ≤ (r.acceptedCount : ℝ) *
      (1 + |Real.log P.gamma1| / Real.log P.gamma2) +
      Real.log (S / (r.state 0).sigma) / Real.log P.gamma2 + R := by
  have ht := r.trial_count_le hS
  have hp : (r.trialCount : ℝ) + (r.refinementCount N : ℝ) = N := by
    exact_mod_cast r.trialCount_add_refinementCount
  linarith

variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Objective regularity and actual supplied-tensor bounds control every executed pass.
The additive accuracy cost is explicitly logarithmic in a common tolerance lower bound. -/
theorem Execution.iteration_count_log_le {P : Parameters} {f : E → ℝ} {O : Oracle f P.p}
    {N : ℕ} (r : Execution P O N) {L M : ℝ} (hM : 1 ≤ M)
    (hf : HigherOrderRegularization.DiagonalLipschitz f P.p L)
    (hA : ∀ k, k ≤ N → ∀ i ∈ Finset.Icc 1 P.p,
      ‖O.derivative (r.state k).point (r.state k).request i‖ ≤ M)
    {ε : ℝ} (hε : 0 < ε) (hεj : ∀ j, 1 ≤ j → j ≤ P.q → ε ≤ P.epsilon j) :
    let S := InexactRegularization.correctedSigmaBound P.toImplicitParameters
      (r.state 0).request (r.state 0).sigma L 1
    let c := InexactRegularization.refinementAccuracyCoefficient P.toImplicitParameters M S 1
    let D := InexactRegularization.refinementLogConstant P.toImplicitParameters
      (r.state 0).request c
    (N : ℝ) ≤ (r.acceptedCount : ℝ) *
      (1 + |Real.log P.gamma1| / Real.log P.gamma2) +
      Real.log (S / (r.state 0).sigma) / Real.log P.gamma2 +
      InexactRegularization.refinementLogSlope P.toImplicitParameters * |Real.log ε| + D + 2 := by
  dsimp only
  have hb := r.iteration_count_le (r.sigma_upper hf le_rfl)
    (r.refinement_count_le hM hf hA hε hεj).2
  linarith

/-- With fixed controls and initialization, positive constants precede every replacement
tolerance vector and every actual finite execution. The full iteration count is bounded
by the actual accepted count plus an explicit logarithmic accuracy term. -/
theorem iteration_bound_fixed_initialization {P : Parameters} {f : E → ℝ}
    (O : Oracle f P.p) {L M : ℝ} (hM : 1 ≤ M)
    (hf : HigherOrderRegularization.DiagonalLipschitz f P.p L)
    (hA : ∀ (x : E) (h : ℕ → ℝ),
      (∀ i ∈ Finset.Icc 1 P.p, 0 < h i ∧ h i ≤ P.kappaInitial) →
      ∀ i ∈ Finset.Icc 1 P.p, ‖O.derivative x h i‖ ≤ M)
    (h0 : ℕ → ℝ) (sigma0 : ℝ) :
    ∃ A G F : ℝ, 0 < A ∧ 0 < G ∧ 0 < F ∧
      ∀ (ε : ℕ → ℝ) (hpos : ∀ j, 1 ≤ j → j ≤ P.q → 0 < ε j)
        (hlt : ∀ j, 1 ≤ j → j ≤ P.q → ε j < 1) (e : ℝ), 0 < e →
        (∀ j, 1 ≤ j → j ≤ P.q → e ≤ ε j) →
        ∀ (N : ℕ) (r : Execution (P.withTolerances ε hpos hlt) O N),
          (r.state 0).request = h0 → (r.state 0).sigma = sigma0 →
          (N : ℝ) ≤ A * (r.acceptedCount : ℝ) + G * |Real.log e| + F := by
  let S := InexactRegularization.correctedSigmaBound P.toImplicitParameters h0 sigma0 L 1
  let c := InexactRegularization.refinementAccuracyCoefficient P.toImplicitParameters M S 1
  let A := 1 + |Real.log P.gamma1| / Real.log P.gamma2
  let G := InexactRegularization.refinementLogSlope P.toImplicitParameters
  let D := InexactRegularization.refinementLogConstant P.toImplicitParameters h0 c
  let C := Real.log (S / sigma0) / Real.log P.gamma2
  refine ⟨A, G, |C| + D + 2, ?_, ?_, ?_, ?_⟩
  · exact add_pos_of_pos_of_nonneg zero_lt_one
      (div_nonneg (abs_nonneg _) (Real.log_pos P.one_lt_gamma2).le)
  · exact InexactRegularization.refinementLogSlope_pos P.toImplicitParameters
  · exact add_pos_of_nonneg_of_pos
      (add_nonneg (abs_nonneg _) (InexactRegularization.refinementLogConstant_nonneg _ _ _))
      (by norm_num)
  intro ε hpos hlt e he hej N r hr hσ
  have hAr : ∀ k, k ≤ N → ∀ i ∈ Finset.Icc 1 P.p,
      ‖O.derivative (r.state k).point (r.state k).request i‖ ≤ M := by
    intro k hk
    apply hA
    intro i hi
    exact ⟨(r.request_bounds hk hi).1,
      (r.request_bounds hk hi).2.trans (r.initial_request_le i hi)⟩
  have hb := r.iteration_count_log_le hM hf hAr he hej
  dsimp only at hb
  rw [hr, hσ] at hb
  have hc : C ≤ |C| := le_abs_self C
  change (N : ℝ) ≤ A * (r.acceptedCount : ℝ) + G * |Real.log e| + (|C| + D + 2)
  change (N : ℝ) ≤ (r.acceptedCount : ℝ) * A + C + G * |Real.log e| + D + 2 at hb
  linarith

end Optimization.ExplicitRegularization
