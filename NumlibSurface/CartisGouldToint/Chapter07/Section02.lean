import Numlib.Optimization.Constrained.TwoPhase.FullBoundary
import NumlibSurface.CartisGouldToint.Chapter06.Section03
import Numlib.Optimization.Regularization.Convex.LeastSquares.PhaseOneComplexity
import Numlib.Optimization.Constrained.TwoPhase.Geometry
import Numlib.Optimization.Constrained.TwoPhase.Uniform
import Numlib.Optimization.Constrained.TwoPhase.Termination
import Numlib.Optimization.Constrained.TwoPhase.BoundaryRegularity

/-!
# Two-phase constrained target geometry

Actual primitive ARp-CC inner executions imply all Phase2 residual, target and
reset-count invariants. Literal strict-reset and corrected closed-reset modes
are explicit. The general feasibility Phase1 execution remains separate.
-/

open Set
namespace CartisGouldToint

/-- Complete primitive feasibility and target-call arrays. -/
abbrev twoPhaseFullData := Constrained.TwoPhase.FullData

/-- A full genuine two-phase prefix, with separate operational feasibility and target calls. -/
abbrev twoPhaseRun := @Constrained.TwoPhase.FullRun

/-- The literal operational final guard of the complete two-phase method. -/
abbrev twoPhaseStop := @Constrained.TwoPhase.FullStop

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

/-- **Lemma 7.2.3.** All Phase2 target and residual invariants follow from actual
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

/-- **Lemma 7.2.4.** The exact source objective range bounds every actual outer
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

section BoundaryCounterexample
open Constrained Constrained.TwoPhase Constrained.TwoPhase.Boundary

/-- The literal nonstrict inner return and strict outer reset disagree at
residual equality. A genuine p=2 one-call execution on a bounded Euclidean disk
terminates with exact feasibility and fails the scaled Lagrangian inequality
for every multiplier. Both source merits are globally smooth with constant
actual Hessians; Phase1 starts feasible with admissible ℓ=p=2. -/
theorem lemma_7_2_1_counterexample :
    ((0 : E) ∈ region ∧ ‖constraint (0 : E)‖ ≤ (1 / 2 : ℝ) * (1 / 2) ∧
      (2 : ℝ) > Real.logb 2 2 ∧ (2 : ℝ) > 1) ∧
    region.Nonempty ∧ IsClosed region ∧ Convex ℝ region ∧ Bornology.IsBounded region ∧
    ContDiff ℝ 2 feasibilityMerit ∧ LipschitzWith 0 (iteratedFDeriv ℝ 2 feasibilityMerit) ∧
    (∀ t : ℝ, ContDiff ℝ 2 (targetMerit objective constraint t) ∧
      LipschitzWith 0 (iteratedFDeriv ℝ 2 (targetMerit objective constraint t))) ∧
    (∀ x ∈ region, -2 ≤ objective x ∧ objective x ≤ 2) ∧
    PhaseTwoRun false objective constraint region settings
      (1 / 2) (1 / 10) (1 / 2) outerData 1 ∧
    StopAfter false objective constraint region (1 / 2) (1 / 10) (1 / 2)
      (outerData.target 0) (outerData.point 1) ∧
    ‖constraint (outerData.point 1)‖ = 0 ∧
    ¬∃ y : ℝ, firstCriticality (vectorLagrangian objective constraint y)
      region (outerData.point 1) ≤ (1 / 10 : ℝ) * multiplierNorm y :=
  counterexample

end BoundaryCounterexample

/-- **Lemma7.2.1, corrected.** The unchanged Phase1 return and exit guards
imply its infeasible criticality certificate. Closing the Phase2 reset guard at
residual equality yields both printed Phase2 alternatives, with the genuine
Lagrangian and an actual multiplier. Only differentiability at the returned
point is needed for the termination implication; the source Cp assumptions
supply it. The literal algorithm is refuted by `lemma_7_2_1_counterexample`. -/
theorem lemma_7_2_1_corrected {n m p : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {C : Set (EuclideanSpace ℝ (Fin n))} {P : twoPhaseInnerSettings p}
    {ε₀ ε₁ θ : ℝ} {D : twoPhaseData (EuclideanSpace ℝ (Fin n))} {N k : ℕ}
    (h : twoPhasePhaseTwoRun true f c C P ε₀ ε₁ θ D N)
    (hC : IsClosed C) (hk : k < N)
    (hf : DifferentiableAt ℝ f (D.point (k + 1)))
    (hc : DifferentiableAt ℝ c (D.point (k + 1)))
    (hs : Constrained.TwoPhase.StopAfter true f c C ε₀ ε₁ θ
      (D.target k) (D.point (k + 1))) :
    (∀ (ℓ : ℝ) (x : EuclideanSpace ℝ (Fin n)),
      (‖c x‖ ≤ θ * ε₀ ∨ Constrained.TwoPhase.firstCriticality
        (fun z => ‖c z‖ ^ ℓ / ℓ) C x ≤ ε₁ * ‖c x‖ ^ (ℓ - 1)) →
      θ * ε₀ < ‖c x‖ →
      Constrained.TwoPhase.firstCriticality (fun z => ‖c z‖ ^ ℓ / ℓ) C x ≤
        ε₁ * ‖c x‖ ^ (ℓ - 1) ∧ θ * ε₀ < ‖c x‖) ∧
    ((Constrained.TwoPhase.firstCriticality (fun z => ‖c z‖ ^ 2 / 2)
      C (D.point (k + 1)) ≤ ε₁ * ‖c (D.point (k + 1))‖ ∧
      θ * ε₀ < ‖c (D.point (k + 1))‖) ∨
      ∃ y : EuclideanSpace ℝ (Fin m),
        Constrained.TwoPhase.firstCriticality (Constrained.vectorLagrangian f c y)
          C (D.point (k + 1)) ≤ ε₁ * Constrained.multiplierNorm y ∧
          ‖c (D.point (k + 1))‖ ≤ ε₀) := by
  exact ⟨fun _ _ hr hs => Constrained.TwoPhase.phase_one_termination hr hs,
    Constrained.TwoPhase.CorrectedPhaseTwoRun.termination h hC hk hf hc hs⟩

/-- **Lemma7.2.5.** The source merit smoothness and highest-derivative
Lipschitz assumptions give one actual uniform Lipschitz constant and one strict
regularization cap for all Phase2 calls. Both constants precede every accuracy
and execution. All actual iterates and feasible trial endpoints remain in the
source convex domain; only its open neighborhood needs Cp regularity. -/
theorem lemma_7_2_5 {n m p : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {C S : Set (EuclideanSpace ℝ (Fin n))} (hS : IsOpen S) (hCS : C ⊆ S)
    (hC : Convex ℝ C) (P : twoPhaseInnerSettings p)
    (hmu : ∀ t : ℝ, ContDiffOn ℝ p (Constrained.targetMerit f c t) S)
    (hlip : ∀ t : ℝ, ∃ L ≥ 0, ∀ x ∈ C, ∀ y ∈ C,
      ‖iteratedFDeriv ℝ p (Constrained.targetMerit f c t) x -
        iteratedFDeriv ℝ p (Constrained.targetMerit f c t) y‖ ≤ L * ‖x - y‖)
    {β flow fup : ℝ}
    (hfb : ∀ x ∈ C, ‖c x‖ ≤ β → flow ≤ f x ∧ f x ≤ fup) :
    ∃ L ≥ 0, ∃ σmax > P.sigmaMin,
      ∀ (ε₀ ε₁ θ : ℝ) (D : twoPhaseData (EuclideanSpace ℝ (Fin n)))
        (N : ℕ) (closedReset : Bool),
        twoPhasePhaseTwoRun closedReset f c C P ε₀ ε₁ θ D N → ε₀ ≤ β →
        (∀ k ≤ N, ∀ x ∈ C, ∀ y ∈ C,
          ‖iteratedFDeriv ℝ p (Constrained.targetMerit f c (D.target k)) x -
            iteratedFDeriv ℝ p (Constrained.targetMerit f c (D.target k)) y‖ ≤
              L * ‖x - y‖) ∧
        (∀ k < N, ∀ i ≤ D.length k, (D.inner k).parameter i ≤ σmax) :=
  Constrained.TwoPhase.exists_uniform_bounds hS hCS hC P hmu hlip hfb

/-- **Lemma7.2.2.** Phase1 reaches its first literal residual or normalized
constrained-criticality stop with the complete printed source constants. The
derivative bound has no additive offset; the initialized and terminal sites
are paid by the remaining preterminal residual budget. -/
theorem lemma_7_2_2 {n m p a : ℕ}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {C S : Set (EuclideanSpace ℝ (Fin n))}
    (P : arpFirstOrderConvexSettings p) (ℓ : ℝ) (_hℓ : 1 < ℓ)
    (hchoice : (ℓ = (p : ℝ) ∧ Real.logb 2 (p : ℝ) < a) ∨
      ∃ o : ℕ, Odd o ∧ Even p ∧ p = o * 2 ^ a ∧
        ℓ = 1 + (o : ℝ) * ((2 : ℝ) ^ a - 1))
    (hclosed : IsClosed C) (hS : IsOpen S)
    (hCS : C ⊆ S) (hC : Convex ℝ C)
    (hf : ContDiffOn ℝ p (LeastSquares.powerObjective c ℓ) S) {L β : ℝ} (hL : 0 < L)
    (hlip : ∀ y ∈ C, ∀ z ∈ C,
      ‖iteratedFDeriv ℝ p (LeastSquares.powerObjective c ℓ) y -
        iteratedFDeriv ℝ p (LeastSquares.powerObjective c ℓ) z‖ ≤ L * ‖y - z‖)
    (hβ : 0 < β) (hβ1 : β < 1) :
    ∃ κS > 0, ∃ κA > 0, ∃ κC > 0,
      κS = max (1 / (1 - β ^ (1 / (2 : ℝ) ^ a)))
        ((2 : ℝ) ^ a / β ^ ((ℓ - 1) * ((p + 1 : ℕ) : ℝ) / p) *
          ((p + 1).factorial / (P.eta1 * P.sigmaMin) *
            ((L + ConvexRegularization.parameterCap P L + P.theta * p.factorial) /
              p.factorial) ^
              (((p + 1 : ℕ) : ℝ) / p))) ∧
      κA = κS * (1 + |Real.log P.gamma1| / Real.log P.gamma2) ∧
      κC = |Real.log P.gamma1| / Real.log P.gamma2 +
        Real.log (ConvexRegularization.parameterCap P L / P.sigmaInitial) /
          Real.log P.gamma2 + 2 ∧
      ∀ (ε₀ ε₁ θ : ℝ), 0 < θ → θ < 1 → 0 < ε₀ →
        ∀ (D : arpFirstOrderConvexData (EuclideanSpace ℝ (Fin n))),
        (∀ N, (∀ i < N,
            ¬arpLeastEuclideanConvexStop c ℓ C (θ * ε₀) ε₁ (D.point i)) →
          arpLeastEuclideanConvexRun c ℓ C P (θ * ε₀) ε₁ D N) →
        ∃ K, arpLeastEuclideanConvexStop c ℓ C (θ * ε₀) ε₁ (D.point K) ∧
          arpLeastEuclideanConvexRun c ℓ C P (θ * ε₀) ε₁ D K ∧
          (∀ i < K, ¬arpLeastEuclideanConvexStop c ℓ C (θ * ε₀) ε₁ (D.point i)) ∧
          (ConvexRegularization.functionEvaluations K : ℝ) ≤
            κA * max (‖c (D.point 0)‖ ^ (1 / (2 : ℝ) ^ a))
              (‖c (D.point 0)‖ ^ (1 - (ℓ - 1) / p)) /
            min (θ ^ (1 / (2 : ℝ) ^ a) * ε₀ ^ (1 / (2 : ℝ) ^ a))
              (ε₁ ^ (((p + 1 : ℕ) : ℝ) / p)) + κC ∧
          ∀ j : ℕ, 1 ≤ j → j ≤ p →
            (ConvexLeastSquares.derivativeEvaluations c (θ * ε₀) P D K j : ℝ) ≤
            κS * max (‖c (D.point 0)‖ ^ (1 / (2 : ℝ) ^ a))
              (‖c (D.point 0)‖ ^ (1 - (ℓ - 1) / p)) /
              min (θ ^ (1 / (2 : ℝ) ^ a) * ε₀ ^ (1 / (2 : ℝ) ^ a))
              (ε₁ ^ (((p + 1 : ℕ) : ℝ) / p)) := by
  have H := LeastSquares.cascadingExponent_choices P.order_pos
  have hg : 0 ≤ LeastSquares.cascadingExponent p ℓ a 1 := by
    rcases hchoice with ⟨rfl, hlog⟩ | ⟨o, ho, heven, hfac, rfl⟩
    · exact (H.1 a hlog).le
    · exact (H.2.1 o a ho heven hfac).1.symm.le
  obtain ⟨κS, hκS, κA, hκA, κC, hκC, heq, hA, hCst, Hrun⟩ :=
    ConvexLeastSquares.exists_uniform_complexity_without_offset P ℓ a hclosed hS hCS hC
      hf hL hlip hβ hβ1 hg
  refine ⟨κS, hκS, κA, hκA, κC, hκC, heq, hA, hCst, ?_⟩
  intro ε₀ ε₁ θ hθ _hθ1 hε₀ D hprefix
  simpa only [LeastSquares.lowerBudget, LeastSquares.lowerAccuracyFactor,
    Bool.false_eq_true, ite_false, Real.mul_rpow hθ.le hε₀.le] using
      Hrun (θ * ε₀) ε₁ D hprefix

section FullCounterexample
open Constrained Constrained.TwoPhase Constrained.TwoPhase.Boundary

/-- **Counterexample to Theorem7.2.7.** A complete actual zero-trial Phase1
and one-trial Phase2 execution satisfies every source smoothness and boundedness
assumption. Its literal final guard fires, while all three promised output
alternatives fail. The obstruction concerns the literal return certificate;
no failure of a separate evaluation-count inequality is asserted here. -/
theorem theorem_7_2_7_counterexample :
    twoPhaseRun false objective constraint region settings settings 2
      (1 / 2) (1 / 10) (1 / 2) fullData ∧
    twoPhaseStop false objective constraint region (1 / 2) (1 / 10) (1 / 2) fullData ∧
    ¬((firstCriticality feasibilityMerit region endpoint ≤
          (1 / 10 : ℝ) * ‖constraint endpoint‖ ∧
        (1 / 2 : ℝ) * (1 / 2) < ‖constraint endpoint‖) ∨
      (firstCriticality feasibilityMerit region endpoint ≤
          (1 / 10 : ℝ) * ‖constraint endpoint‖ ∧
        (1 / 2 : ℝ) * (1 / 2) < ‖constraint endpoint‖) ∨
      ∃ y : ℝ, firstCriticality (vectorLagrangian objective constraint y) region endpoint ≤
        (1 / 10 : ℝ) * multiplierNorm y ∧ ‖constraint endpoint‖ ≤ (1 / 2 : ℝ)) ∧
    (((0 : E) ∈ region ∧ ‖constraint (0 : E)‖ ≤ (1 / 2 : ℝ) * (1 / 2) ∧
      (2 : ℝ) > Real.logb 2 2 ∧ (2 : ℝ) > 1) ∧
    region.Nonempty ∧ IsClosed region ∧ Convex ℝ region ∧ Bornology.IsBounded region ∧
    ContDiff ℝ 2 feasibilityMerit ∧ LipschitzWith 0 (iteratedFDeriv ℝ 2 feasibilityMerit) ∧
    (∀ t : ℝ, ContDiff ℝ 2 (targetMerit objective constraint t) ∧
      LipschitzWith 0 (iteratedFDeriv ℝ 2 (targetMerit objective constraint t))) ∧
    (∀ x ∈ region, -2 ≤ objective x ∧ objective x ≤ 2) ∧
    PhaseTwoRun false objective constraint region settings
      (1 / 2) (1 / 10) (1 / 2) outerData 1 ∧
    StopAfter false objective constraint region (1 / 2) (1 / 10) (1 / 2)
      (outerData.target 0) (outerData.point 1) ∧
    ‖constraint (outerData.point 1)‖ = 0 ∧
    ¬∃ y : ℝ, firstCriticality (vectorLagrangian objective constraint y)
      region (outerData.point 1) ≤ (1 / 10 : ℝ) * multiplierNorm y) :=
  ⟨full_run, full_stop, all_certificates_fail, lemma_7_2_1_counterexample⟩

end FullCounterexample

end CartisGouldToint
