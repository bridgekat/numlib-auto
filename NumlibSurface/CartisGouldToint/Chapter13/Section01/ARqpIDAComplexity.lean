import NumlibSurface.CartisGouldToint.Chapter13.Section01.ARqpIDADecrease
import Numlib.Optimization.InexactRegularizationToleranceRates

/-!
# First true quality and evaluation complexity of literal ARqpIDA

Global smoothness and oracle data, all nonepsilon algorithm controls, and initial derivative
requests and regularization parameter are fixed before choosing any tolerance vector. The
literal q-checked method attains true quality with the two source exponent regimes. The
constants retain the full initial request-ratio dependence needed to repair the printed
local lemmas. Function calls have no logarithmic accuracy term; derivative batches do.

The tolerance domain follows Algorithm 13.1.2's strict epsilon_j < 1 initialization,
resolving the endpoint discrepancy with the theorem's printed epsilon_j <= 1. Actual
operational complete runs supply all legal transitions; the theorem derives their first
true-quality point and does not certify an observable IDA stopping test.
-/

noncomputable section
namespace CartisGouldToint.Chapter13.Section01
open Optimization InexactRegularization
variable {n : ℕ}

/-- Fixed normalized global analytic bounds for all tolerance replacements of the same
implicit-accuracy controls. -/
theorem arqpida_fixed_analysis_bounds (P : ARqpIDAParameters)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (O : ImplicitAccuracyOracle f P.p)
    (hf : ImplicitSmoothness f P.p) :
    ∃ L K M : ℝ, 1 ≤ L ∧ 0 ≤ K ∧ 1 ≤ M ∧
      HigherOrderRegularization.DiagonalLipschitz f P.p L ∧
      InexactTrustRegion.UniformAccuracy (TRqIDA.oracle O) K ∧
      (∀ (x : EuclideanSpace ℝ (Fin n)) (h : ℕ → ℝ),
        (∀ i ∈ Finset.Icc 1 P.p, 0 < h i ∧ h i ≤ P.kappaInitial) →
        ∀ i ∈ Finset.Icc 1 P.p, ‖O.derivative x h i‖ ≤ M) := by
  obtain ⟨L, hL, hfL, _⟩ := TRqIDA.exists_uniform_smoothness hf
  have hcap : 0 < P.kappaInitial + 1 := by linarith [P.kappaInitial_nonneg]
  obtain ⟨_, K, M, _, hK, _, hO, _, hnorm⟩ :=
    TRqIDA.exists_global_analysis_bounds O hf hcap
  refine ⟨L, K, max 1 M, hL, hK, le_max_left _ _,
    hfL P.p (P.order_pos.trans P.order_le) le_rfl, hO, ?_⟩
  intro x h hh i hi
  exact (hnorm x h (fun j hj => (hh j hj).1)
    (fun j hj => (hh j hj).2.trans (by linarith)) i hi).trans (le_max_right _ _)


/-- Theorem 13.1.19 for the literal checked-q algorithm: fixed positive constants are chosen
BEFORE all tolerance vectors and all actual complete runs with the specified initial request
vector and sigma. The simultaneous tolerance measure uses the source's two exponent regimes.
True quality uses unit balls when q<=2 and a genuine valid radius witness when q>2.
The printed local constants are corrected for independent initial requests and long steps;
the epsilon endpoint follows the strict algorithm domain as explained in the module doc. -/
theorem theorem_13_1_19 (P : ARqpIDAParameters)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (O : ImplicitAccuracyOracle f P.p)
    (hf : ImplicitSmoothness f P.p) (h0 : ℕ → ℝ) {sigma0 low : ℝ}
    (hsigma : P.sigmaMin ≤ sigma0) (hlow : ∀ x, low ≤ f x) :
    ∃ A C S E F : ℝ, 0 < A ∧ 0 < C ∧ 0 < S ∧ 0 < E ∧ 0 < F ∧
      ∀ (epsilon : ℕ → ℝ)
        (hpos : ∀ j, 1 ≤ j → j ≤ P.q → 0 < epsilon j)
        (hlt : ∀ j, 1 ≤ j → j ≤ P.q → epsilon j < 1)
        (r : InexactRegularization.Run (P.withTolerances epsilon hpos hlt) P.q f O.derivative),
        (r.state 0).request = h0 → (r.state 0).sigma = sigma0 →
        ∃ k : ℕ, PointQuality (P.withTolerances epsilon hpos hlt) f (r.state k).point ∧
          (∀ j < k, ¬PointQuality (P.withTolerances epsilon hpos hlt) f (r.state j).point) ∧
          ((r.prefix k).functionCount : ℝ) ≤
            A * (f (r.state 0).point - low) /
              HigherOrderApproximateRegularization.toleranceMeasure
                P.p P.q P.order_pos epsilon + C ∧
          ((r.prefix k).derivativeBatches : ℝ) ≤
            S * (f (r.state 0).point - low) /
                HigherOrderApproximateRegularization.toleranceMeasure P.p P.q P.order_pos epsilon +
              E * |Real.log (Chapter12.Section02.TRq.epsilonMinimum P.q epsilon)| + F := by
  obtain ⟨L, K, M, hL, hK, hM, hfL, hO, hnorm⟩ := arqpida_fixed_analysis_bounds P O hf
  let d := acceptedDecreaseCoefficient P h0 sigma0 L K M
  let G := trialCountMultiplier P
  let C0 := trialLogBudget P h0 sigma0 L K
  let F0 := refinementCountConstant P h0 sigma0 L K M
  have hs0 : 0 < sigma0 := P.sigmaMin_pos.trans_le hsigma
  have hd : 0 < d := acceptedDecreaseCoefficient_pos P h0 hs0.le hL hK hM
  have hG : 0 < G := trialCountMultiplier_pos P
  have hC0 : 0 ≤ C0 := trialLogBudget_nonneg P h0 hs0 L K
  have hF0 : 0 < F0 := refinementCountConstant_pos P h0 sigma0 L K M
  refine ⟨G / d, G + C0 + 1, 1 / d, refinementLogSlope P, F0 + 2,
    div_pos hG hd, by positivity, div_pos one_pos hd, refinementLogSlope_pos P,
    by positivity, ?_⟩
  intro epsilon hpos hlt r hrequest hsig
  have he := Chapter12.Section02.TRq.epsilonMinimum_pos P.order_pos hpos
  obtain ⟨k, _, hquality, hfirst, hfunction, hderivative⟩ :=
    r.first_pointQuality_bounds (P := P.withTolerances epsilon hpos hlt)
      (TRqIDA.oracle O) hfL hL hK hO hM hnorm hlow he
      (fun j hj hjq => Chapter12.Section02.TRq.epsilonMinimum_le epsilon hj hjq)
  refine ⟨k, hquality, hfirst, ?_, ?_⟩
  · have hb : ((r.prefix k).functionCount : ℝ) ≤
        G * ((f (r.state 0).point - low) /
            (d * HigherOrderApproximateRegularization.toleranceMeasure
              P.p P.q P.order_pos epsilon)) + G + C0 + 1 := by
      have hf1 := hfunction
      simp only [hrequest, hsig, trialCountMultiplier_withTolerances,
        acceptedDecreaseCoefficient_withTolerances, trialLogBudget_withTolerances,
        toleranceMeasure_withTolerances] at hf1
      convert hf1 using 1
      rfl
    calc
      _ ≤ _ := hb
      _ = _ := by rw [div_mul_eq_div_div]; ring
  · have hb : ((r.prefix k).derivativeBatches : ℝ) ≤
        (f (r.state 0).point - low) /
            (d * HigherOrderApproximateRegularization.toleranceMeasure
              P.p P.q P.order_pos epsilon) +
          refinementLogSlope P *
            |Real.log (Chapter12.Section02.TRq.epsilonMinimum P.q epsilon)| + F0 + 2 := by
      have hd1 := hderivative
      simp only [hrequest, hsig, acceptedDecreaseCoefficient_withTolerances,
        refinementLogSlope_withTolerances, refinementCountConstant_withTolerances,
        toleranceMeasure_withTolerances] at hd1
      convert hd1 using 1
      rfl
    calc
      _ ≤ _ := hb
      _ = _ := by rw [div_mul_eq_div_div]; ring

end CartisGouldToint.Chapter13.Section01
