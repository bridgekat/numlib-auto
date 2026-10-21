import NumlibSurface.CartisGouldToint.Chapter12.Section02.ARqpInner
import Numlib.Optimization.HigherOrderApproximateRegularizationInnerReturn

/-!
# Finite ARqp inner progress and actual returned model steps

Legal inner choices always return after finitely many transitions, for every initial positive
accuracy fraction at most one. The strict boundary variant tests unit steps and copies inherited
radii on a genuinely long return. Its final inspection epoch supplies all model-gap witnesses.
The separate existence clause permits unit low-order radii even for arbitrary inherited radii.
-/

noncomputable section
namespace CartisGouldToint.Chapter12.Section02
open Optimization HigherOrderApproximateRegularization
variable {n : ℕ}

/-- Finite executions of the strict-boundary correction of Algorithm12.2.3. -/
abbrev arqpCorrectedInnerExecution (P : ARqp.Parameters)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n))
    (σ : ℝ) (z : EuclideanSpace ℝ (Fin n)) (inherited : ℕ → ℝ) (N : ℕ) :=
  CorrectedInnerExecution P (model f P.p x σ) z inherited N

/-- Lemma12.2.9: actual admissible steps exist with the quantitative radii; all legal raw
and corrected inner histories are finite. Every initial corrected state has an actual returned
execution producing a valid outer step. Small returned steps retain unit low radii and every
higher radius floor; long corrected returns faithfully inherit the supplied radii. -/
theorem lemma_12_2_9 (P : ARqp.Parameters)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {L : ℕ → ℝ}
    (hf : LipschitzDerivativeFamily f P.p L) (x : EuclideanSpace ℝ (Fin n))
    {σ : ℝ} (hσ : 0 < σ) (inherited : ℕ → ℝ) (hinherited : ValidRadii P inherited) :
    ∃ z : EuclideanSpace ℝ (Fin n), (∀ t, model f P.p x σ z ≤ model f P.p x σ t) ∧
      (∃ trial : ModelStep P f x σ inherited,
        (∀ j, 1 ≤ j → j ≤ P.q → j ≤ 2 → trial.radii j = 1) ∧
        (‖trial.step‖ ≤ 1 → ∀ j, 3 ≤ j → j ≤ P.q →
          P.fraction * P.theta / (8 * (3 * derivativeFamilyConstant P.p L + σ)) *
            P.epsilon j ≤ trial.radii j)) ∧
      (∃ B : ℕ, ∀ N, ∀ _run : algorithm_12_2_3 P f x σ z N, N ≤ B) ∧
      (∃ B : ℕ, ∀ inherited N,
        ∀ _run : arqpCorrectedInnerExecution P f x σ z inherited N, N ≤ B) ∧
      ∀ a : InnerState (EuclideanSpace ℝ (Fin n)), InnerInitial a →
        ∃ N, ∃ run : arqpCorrectedInnerExecution P f x σ z inherited N,
          ∃ trial : ModelStep P f x σ inherited,
            run.state 0 = a ∧ (run.state N).phase = .returned ∧
            trial.step = (run.state N).step ∧ trial.radii = (run.state N).radii ∧
            (‖trial.step‖ ≤ 1 →
              (∀ j, 1 ≤ j → j ≤ P.q → j ≤ 2 → trial.radii j = 1) ∧
              ∀ j, 3 ≤ j → j ≤ P.q →
                P.fraction * P.theta / (8 * (3 * derivativeFamilyConstant P.p L + σ)) *
                  P.epsilon j ≤ trial.radii j) := by
  have hL := hf.one_le_constant (P.order_pos.trans P.order_le)
  have hM : 1 ≤ 3 * derivativeFamilyConstant P.p L + σ := by linarith
  obtain ⟨z, hmin⟩ := exists_model_minimizer f P.p x hσ
  obtain ⟨trial, hlow, hfloor⟩ := exists_arqp_modelStep P hf x hσ inherited
  obtain ⟨Braw, hraw⟩ := InnerExecution.terminates P hf.toHigherOrderDerivativeFamily hL x hσ hmin
  obtain ⟨Bcorr, hcorr⟩ :=
    CorrectedInnerExecution.terminates P hf.toHigherOrderDerivativeFamily hL x hσ hmin
  refine ⟨z, hmin, ⟨trial, hlow, hfloor⟩, ⟨Braw, fun N run => (hraw N run).1⟩,
    ⟨Bcorr, fun inherited N run => (hcorr inherited N run).1⟩, ?_⟩
  intro a ha
  obtain ⟨N, run, hstart, hreturn⟩ := exists_model_corrected_inner_return_execution P
    hf.toHigherOrderDerivativeFamily hL x hσ hmin inherited ha
  obtain ⟨trial, hstep, hradii⟩ := run.exists_modelStep hinherited hreturn
  refine ⟨N, run, trial, hstart, hreturn, hstep, hradii, ?_⟩
  intro hs
  have hs' : ‖(run.state N).step‖ ≤ 1 := by rwa [hstep] at hs
  have hb := run.radii_of_return_small hM
    (smallRadiusDecrease_model P hf.toHigherOrderDerivativeFamily x hσ.le) hreturn hs'
  constructor
  · intro j _ _ hj
    rw [hradii]
    exact hb.1 j hj
  · intro j hj hjq
    rw [hradii]
    calc
      _ = radiusFloor P (3 * derivativeFamilyConstant P.p L + σ) j := by
        unfold radiusFloor accuracyTarget
        ring
      _ ≤ _ := hb.2 j hj hjq

end CartisGouldToint.Chapter12.Section02
