import Numlib.Optimization.Constrained.TwoPhase.CoarseComplexity
import Numlib.Optimization.Constrained.TwoPhase.FullRun
import Numlib.Optimization.Regularization.Convex.LeastSquares.PhaseOneComplexity

/-!
# Full corrected two-phase outputs and coarser evaluation complexity

The actual least-residual phase precedes the closed-reset target method.
All three true output alternatives and initialized oracle schedules refer to
the returned point of the corresponding actual phase.
-/

namespace Constrained.TwoPhase
open Set TaylorModel EvaluationComplexity
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The actual returned point is the feasibility endpoint on its exit branch,
or the last target-method endpoint on entry to Phase2. -/
noncomputable def FullData.outputPoint (c : E → F) (ε₀ θ : ℝ) (D : FullData E) : E := by
  classical
  exact if θ * ε₀ < ‖c (D.phaseOne.point D.phaseOneLength)‖ then
    D.phaseOne.point D.phaseOneLength else D.phaseTwo.point D.phaseTwoLength

/-- Full initialized function calls: the feasibility schedule and each actual
interrupted inner-call schedule, including its initial values. -/
def FullData.functionEvaluations (D : FullData E) : ℕ :=
  (D.phaseOneLength + 1) + ∑ k ∈ Finset.range D.phaseTwoLength, (D.phaseTwo.length k + 1)

/-- Full derivative calls use the genuine feasibility derivative schedule and
cached derivatives on rejection within each actual target-method call. -/
noncomputable def FullData.derivativeEvaluations {p : ℕ} (c : E → F)
    (P₁ P₂ : ConvexRegularization.Settings p) (ε₀ θ : ℝ)
    (D : FullData E) (j : ℕ) : ℕ :=
  ConvexLeastSquares.derivativeEvaluations c (θ * ε₀) P₁ D.phaseOne D.phaseOneLength j +
    if 1 ≤ j ∧ j ≤ p then ∑ k ∈ Finset.range D.phaseTwoLength,
      ((successfulIterations {i | P₂.eta1 ≤ (D.phaseTwo.inner k).ratio i}
        (D.phaseTwo.length k)).card + 1) else 0

/-- Every true full closed-reset stopping return satisfies one of all three
source output alternatives, at the actual returned point. -/
theorem FullRun.output_certificate {p : ℕ} {f : E → ℝ} {c : E → F} {C : Set E}
    {P₁ P₂ : ConvexRegularization.Settings p} {ℓ ε₀ ε₁ θ : ℝ} {D : FullData E}
    (h : FullRun true f c C P₁ P₂ ℓ ε₀ ε₁ θ D) (hC : IsClosed C)
    (hf : ∀ x ∈ C, DifferentiableAt ℝ f x) (hc : ∀ x ∈ C, DifferentiableAt ℝ c x)
    (hstop : FullStop true f c C ε₀ ε₁ θ D) :
    let x := D.outputPoint c ε₀ θ
    (firstCriticality (LeastSquares.powerObjective c ℓ) C x ≤ ε₁ * ‖c x‖ ^ (ℓ - 1) ∧
      θ * ε₀ < ‖c x‖) ∨
    (firstCriticality (fun z => ‖c z‖ ^ 2 / 2) C x ≤ ε₁ * ‖c x‖ ∧
      θ * ε₀ < ‖c x‖) ∨
    ∃ y : F, firstCriticality (vectorLagrangian f c y) C x ≤ ε₁ * multiplierNorm y ∧
      ‖c x‖ ≤ ε₀ := by
  classical
  dsimp only
  by_cases hexit : θ * ε₀ < ‖c (D.phaseOne.point D.phaseOneLength)‖
  · left
    rw [FullData.outputPoint, ite_eq_left hexit]
    have hs := (ConvexLeastSquares.stop_iff_scaled c ℓ C
      (mul_pos h.theta_pos h.primal_pos) _).mp h.phaseOne_return
    exact phase_one_termination hs hexit
  · have hentry : ‖c (D.phaseOne.point D.phaseOneLength)‖ ≤ θ * ε₀ := not_lt.mp hexit
    have hr := h.phaseTwo_run hentry
    have hs : 0 < D.phaseTwoLength ∧ StopAfter true f c C ε₀ ε₁ θ
        (D.phaseTwo.target (D.phaseTwoLength - 1)) (D.phaseTwo.point D.phaseTwoLength) :=
      hstop.resolve_left hexit
    have hk : D.phaseTwoLength - 1 < D.phaseTwoLength := by omega
    have hx := hr.mem le_rfl
    have ht := CorrectedPhaseTwoRun.termination hr hC hk (by
      simpa only [Nat.sub_add_cancel hs.1] using hf _ hx) (by
      simpa only [Nat.sub_add_cancel hs.1] using hc _ hx) (by
      simpa only [Nat.sub_add_cancel hs.1] using hs.2)
    right
    rw [FullData.outputPoint, ite_eq_right hexit]
    simpa only [Nat.sub_add_cancel hs.1] using ht

end Constrained.TwoPhase

namespace Constrained.TwoPhase
open Set TaylorModel EvaluationComplexity LeastSquares
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Full actual two-phase executions reach a true return in either phase and
satisfy every initialized oracle budget. The reset-equality repair is the only
algorithm change. The coarser second-phase budget explicitly pays for terminal
reflections; all fixed constants precede the independent accuracies. -/
theorem exists_corrected_full_complexity {p : ℕ} {f : E → ℝ} {c : E → F} {C S : Set E}
    (P₁ P₂ : ConvexRegularization.Settings p) (ℓ : ℝ) (a : ℕ)
    (hι : 0 ≤ cascadingExponent p ℓ a 1)
    (hclosed : IsClosed C) (hS : IsOpen S) (hCS : C ⊆ S) (hC : Convex ℝ C)
    (hφ : ContDiffOn ℝ p (powerObjective c ℓ) S) {L₁ L₂ B b flow fup θ β : ℝ}
    (hL₁ : 0 < L₁)
    (hlipφ : ∀ y ∈ C, ∀ z ∈ C,
      ‖iteratedFDeriv ℝ p (powerObjective c ℓ) y -
        iteratedFDeriv ℝ p (powerObjective c ℓ) z‖ ≤ L₁ * ‖y - z‖)
    (hmu : ∀ t, ContDiffOn ℝ p (targetMerit f c t) S) (hL₂ : 0 < L₂)
    (hlipmu : ∀ t ∈ Icc (flow - 1) fup, ∀ y ∈ C, ∀ z ∈ C,
      ‖iteratedFDeriv ℝ p (targetMerit f c t) y -
        iteratedFDeriv ℝ p (targetMerit f c t) z‖ ≤ L₂ * ‖y - z‖)
    (hθ : 0 < θ) (hθ1 : θ < 1) (hβ : P₂.theta < β) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hB : 0 < B) (hf : ∀ x ∈ C, ContDiffAt ℝ 1 f x) (hc : ∀ x ∈ C, ContDiffAt ℝ 1 c x)
    (hDf : ∀ x ∈ C, ‖c x‖ ≤ 1 → ‖fderiv ℝ f x‖ ≤ B)
    (hfb : ∀ x ∈ C, ‖c x‖ ≤ b → flow ≤ f x ∧ f x ≤ fup) :
    ∃ κS > 0, ∃ κA > 0, ∃ κC > 0,
      ∀ (ε₀ ε₁ : ℝ),
        0 < ε₀ → ε₀ ≤ 1 → 0 < ε₁ → ε₁ ≤ 1 → ε₀ ≤ b →
      ∀ (D₁ : ConvexRegularization.Data E) (D₂ : ℕ → Data E),
        (∀ N, (∀ i < N, ¬ConvexLeastSquares.Stop c ℓ C (θ * ε₀) ε₁ (D₁.point i)) →
          ConvexLeastSquares.Run c ℓ C P₁ (θ * ε₀) ε₁ D₁ N) →
        (∀ K, (D₂ K).point 0 = D₁.point K) →
        (∀ K, ConvexLeastSquares.Stop c ℓ C (θ * ε₀) ε₁ (D₁.point K) →
          ‖c (D₁.point K)‖ ≤ θ * ε₀ →
          ∀ N, (∀ k < N, ¬StopAfter true f c C ε₀ ε₁ θ
            ((D₂ K).target k) ((D₂ K).point (k + 1))) →
            PhaseTwoRun true f c C P₂ ε₀ ε₁ θ (D₂ K) (N + 1)) →
      let J := coarseBudgets P₂ L₂ B β θ (fup - flow + 1) ε₀ ε₁
      let R := lowerBudget false p ℓ a ‖c (D₁.point 0)‖ /
        lowerAccuracyFactor false p a (θ * ε₀) ε₁ 1
      ∃ D : FullData E, D.phaseOne = D₁ ∧ D.phaseTwo = D₂ D.phaseOneLength ∧
        FullRun true f c C P₁ P₂ ℓ ε₀ ε₁ θ D ∧
        FullStop true f c C ε₀ ε₁ θ D ∧
        (∀ i < D.phaseOneLength,
          ¬ConvexLeastSquares.Stop c ℓ C (θ * ε₀) ε₁ (D₁.point i)) ∧
        (∀ k, k + 1 < D.phaseTwoLength → ¬StopAfter true f c C ε₀ ε₁ θ
          (D.phaseTwo.target k) (D.phaseTwo.point (k + 1))) ∧
        ((firstCriticality (powerObjective c ℓ) C (D.outputPoint c ε₀ θ) ≤
            ε₁ * ‖c (D.outputPoint c ε₀ θ)‖ ^ (ℓ - 1) ∧
            θ * ε₀ < ‖c (D.outputPoint c ε₀ θ)‖) ∨
          (firstCriticality (fun x => ‖c x‖ ^ 2 / 2) C (D.outputPoint c ε₀ θ) ≤
            ε₁ * ‖c (D.outputPoint c ε₀ θ)‖ ∧
            θ * ε₀ < ‖c (D.outputPoint c ε₀ θ)‖) ∨
          ∃ y : F, firstCriticality (vectorLagrangian f c y) C (D.outputPoint c ε₀ θ) ≤
            ε₁ * multiplierNorm y ∧ ‖c (D.outputPoint c ε₀ θ)‖ ≤ ε₀) ∧
        (D.functionEvaluations : ℝ) ≤ κA * R + κC + max 0 J.functions ∧
        ∀ j : ℕ, 1 ≤ j → j ≤ p →
          (D.derivativeEvaluations c P₁ P₂ ε₀ θ j : ℝ) ≤
            κS * R + max 0 J.derivatives := by
  classical
  obtain ⟨κS, hs, κA, ha, κC, hconst, _, _, _, hall⟩ :=
    ConvexLeastSquares.exists_uniform_complexity_without_offset P₁ ℓ a hclosed hS hCS hC
      hφ hL₁ hlipφ (β := 1 / 2) (by norm_num) (by norm_num) hι
  refine ⟨κS, hs, κA, ha, κC, hconst, ?_⟩
  intro ε₀ ε₁ hε₀ hε₀1 hε₁ hε₁1 hb D₁ D₂ hphase₁ hstart hphase₂
  dsimp only
  obtain ⟨K₁, hstop₁, hrun₁, hfirst₁, hF₁, hD₁⟩ :=
    hall (θ * ε₀) ε₁ D₁ hphase₁
  let J := coarseBudgets P₂ L₂ B β θ (fup - flow + 1) ε₀ ε₁
  let R := lowerBudget false p ℓ a ‖c (D₁.point 0)‖ /
    lowerAccuracyFactor false p a (θ * ε₀) ε₁ 1
  have hF₁' : (K₁ + 1 : ℕ) ≤ κA * R + κC := by
    simpa only [ConvexRegularization.functionEvaluations, mul_div_assoc] using hF₁
  have hD₁' : ∀ j : ℕ, 1 ≤ j → j ≤ p →
      (ConvexLeastSquares.derivativeEvaluations c (θ * ε₀) P₁ D₁ K₁ j : ℝ) ≤
        κS * R := by
    intro j hj hjp
    simpa only [mul_div_assoc] using hD₁ j hj hjp
  by_cases hexit : θ * ε₀ < ‖c (D₁.point K₁)‖
  · let D : FullData E := ⟨D₁, K₁, D₂ K₁, 0⟩
    have hr : FullRun true f c C P₁ P₂ ℓ ε₀ ε₁ θ D := {
      primal_pos := hε₀
      primal_le_one := hε₀1
      dual_pos := hε₁
      dual_le_one := hε₁1
      theta_pos := hθ
      theta_lt_one := hθ1
      phaseOne_run := hrun₁
      phaseOne_return := hstop₁
      phaseTwo_start := hstart K₁
      phaseTwo_run := fun hh => (not_le_of_gt hexit hh).elim
      phaseOne_exit := fun _ => rfl }
    have ht : FullStop true f c C ε₀ ε₁ θ D := Or.inl hexit
    refine ⟨D, rfl, rfl, hr, ht, hfirst₁, ?_, ?_, ?_, ?_⟩
    · intro k hk
      have : D.phaseTwoLength = 0 := rfl
      omega
    · exact hr.output_certificate hclosed (fun x hx => (hf x hx).differentiableAt (by norm_num))
        (fun x hx => (hc x hx).differentiableAt (by norm_num)) ht
    · have hh := add_le_add hF₁' (show (0 : ℝ) ≤ max 0 J.functions from le_max_left _ _)
      simpa only [FullData.functionEvaluations, D, Finset.range_zero, Finset.sum_empty,
        add_zero, Nat.cast_add, Nat.cast_one] using hh
    · intro j hj hjp
      have hh := add_le_add (hD₁' j hj hjp)
        (show (0 : ℝ) ≤ max 0 J.derivatives from le_max_left _ _)
      simpa only [FullData.derivativeEvaluations, D, hj, hjp, and_self, ite_true,
        Finset.range_zero, Finset.sum_empty, add_zero] using hh
  · have hentry : ‖c (D₁.point K₁)‖ ≤ θ * ε₀ := not_lt.mp hexit
    obtain ⟨K₂, hstop₂, hrun₂, hfirst₂, _, hF₂, hD₂, _⟩ :=
      exists_phase_two_termination P₂ hclosed hS hCS hC hmu hL₂ hlipmu
        hβ hβ0 hβ1 hB hf hc hDf
        hb hfb (hphase₂ K₁ hstop₁ hentry)
    let D : FullData E := ⟨D₁, K₁, D₂ K₁, K₂ + 1⟩
    have hr : FullRun true f c C P₁ P₂ ℓ ε₀ ε₁ θ D := {
      primal_pos := hε₀
      primal_le_one := hε₀1
      dual_pos := hε₁
      dual_le_one := hε₁1
      theta_pos := hθ
      theta_lt_one := hθ1
      phaseOne_run := hrun₁
      phaseOne_return := hstop₁
      phaseTwo_start := hstart K₁
      phaseTwo_run := fun _ => hrun₂
      phaseOne_exit := fun hh => (not_lt_of_ge hentry hh).elim }
    have ht : FullStop true f c C ε₀ ε₁ θ D := by
      apply Or.inr
      exact ⟨Nat.succ_pos _, by simpa only [D, Nat.add_sub_cancel] using hstop₂⟩
    refine ⟨D, rfl, rfl, hr, ht, hfirst₁, ?_, ?_, ?_, ?_⟩
    · intro k hk
      exact hfirst₂ k (by change k + 1 < K₂ + 1 at hk; omega)
    · exact hr.output_certificate hclosed (fun x hx => (hf x hx).differentiableAt (by norm_num))
        (fun x hx => (hc x hx).differentiableAt (by norm_num)) ht
    · have hh := add_le_add hF₁' (hF₂.trans (le_max_right 0 J.functions))
      simpa only [FullData.functionEvaluations, D, Nat.cast_add, Nat.cast_sum] using hh
    · intro j hj hjp
      have hh := add_le_add (hD₁' j hj hjp) (hD₂.trans (le_max_right 0 J.derivatives))
      simpa only [FullData.derivativeEvaluations, D, hj, hjp, and_self, ite_true,
        Nat.cast_add, Nat.cast_sum] using hh

end Constrained.TwoPhase
