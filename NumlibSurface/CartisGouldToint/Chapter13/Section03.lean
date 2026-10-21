import Numlib.Optimization.ExplicitTrustRegionRates
import NumlibSurface.CartisGouldToint.Chapter13.Section01.TRqIDA

/-!
# Chapter 13, Section 3: explicit dynamic accuracy

The known absolute-error oracle supplies approximate function values and derivative tensors.
The trust-region algorithm evaluates both trial endpoints at the same value accuracy and can
stop only after the computed half-threshold tests and the explicit full-order error-sum test.
The latter is the literal condition (13.3.8); it implies the shorter-order error certificates.
-/

noncomputable section
open scoped Nat
open Optimization
namespace CartisGouldToint.Chapter13.Section03
open ExplicitTrustRegion HigherOrderTrustRegion
variable {n : ℕ}

/-- Equations (13.3.1)–(13.3.4): actual approximate function values and derivatives have known
absolute errors bounded by their positive requests, with every coefficient normalized to one. -/
abbrev ExplicitAccuracyOracle (f : EuclideanSpace ℝ (Fin n) → ℝ) (q : ℕ) :=
  ExplicitTrustRegion.Oracle f q

namespace TRqEDA

/-- Algorithm 13.3.1 with literal full-order certificate (13.3.8), the two accuracy-only loops,
common-accuracy inexact endpoint ratios, rejected derivative caching, and source radius updates.
The trace obeys the operational transitions until its first observable stopping certificate. -/
def algorithm (p : Parameters) (a : AccuracyParameters) (q : ℕ) (epsilon : ℕ → ℝ)
    (κh : ℝ) {f : EuclideanSpace ℝ (Fin n) → ℝ} (O : ExplicitAccuracyOracle f q)
    (t : ExplicitTrustRegion.Trace (EuclideanSpace ℝ (Fin n))) : Prop :=
  1 ≤ q ∧ (∀ j, 1 ≤ j → j ≤ q → 0 < epsilon j ∧ epsilon j ≤ 1) ∧
    Chapter12.Section02.TRq.epsilonMinimum q epsilon ≤ p.theta ∧
    p.theta ≤ t.radius 0 ∧ (∀ i ∈ Finset.Icc 1 q, t.request 0 i ≤ κh) ∧
    IsExecution p a epsilon (Chapter12.Section02.TRq.epsilonMinimum q epsilon) O t

variable {p : Parameters} {a : AccuracyParameters} {q : ℕ} {epsilon : ℕ → ℝ} {κh : ℝ}
  {f : EuclideanSpace ℝ (Fin n) → ℝ} {O : ExplicitAccuracyOracle f q}
  {t : ExplicitTrustRegion.Trace (EuclideanSpace ℝ (Fin n))}

/-- Every prefix before the first observable certificate satisfies the source transitions. -/
theorem algorithm.prefix (h : algorithm p a q epsilon κh O t) (N : ℕ)
    (hn : ∀ j < N,
      ¬Certified p epsilon (Chapter12.Section02.TRq.epsilonMinimum q epsilon) O t j) :
    LegalPrefix p a epsilon (Chapter12.Section02.TRq.epsilonMinimum q epsilon) O t N :=
  h.2.2.2.2.2 N hn

/-- The minimum active source tolerance is positive and at most one. -/
theorem algorithm.minimum_bounds (h : algorithm p a q epsilon κh O t) :
    0 < Chapter12.Section02.TRq.epsilonMinimum q epsilon ∧
      Chapter12.Section02.TRq.epsilonMinimum q epsilon ≤ 1 :=
  ⟨Chapter12.Section02.TRq.epsilonMinimum_pos h.1 (fun j hj hjq => (h.2.1 j hj hjq).1),
    (Chapter12.Section02.TRq.epsilonMinimum_le epsilon le_rfl h.1).trans
      (h.2.1 1 le_rfl h.1).2⟩

/-- Positive derivative requests before termination never exceed their initialization cap. -/
theorem algorithm.request_le_initial_bound (h : algorithm p a q epsilon κh O t)
    {k : ℕ} (hn : ∀ j < k,
      ¬Certified p epsilon (Chapter12.Section02.TRq.epsilonMinimum q epsilon) O t j)
    {i : ℕ} (hi : i ∈ Finset.Icc 1 q) : t.request k i ≤ κh := by
  have hp := h.prefix k hn
  have hh := hp.request_le_pow h.2.2.2.2.1 le_rfl hi
  have hκh : 0 < κh := (hp.requests_pos (k := 0) (by omega)
    (Finset.mem_Icc.mpr ⟨le_rfl, h.1⟩)).trans_le
    (h.2.2.2.2.1 1 (Finset.mem_Icc.mpr ⟨le_rfl, h.1⟩))
  have hpow : a.contraction ^ (refinements t k).card ≤ 1 :=
    pow_le_one₀ a.contraction_pos.le a.contraction_lt_one.le
  exact hh.trans (mul_le_of_le_one_left hκh.le hpow)

/-- The source initialization coefficient from (13.1.31), specialized to known multiplier one. -/
def sourceRadiusCoefficient (p : Parameters) (a : AccuracyParameters) (q : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (t : ExplicitTrustRegion.Trace (EuclideanSpace ℝ (Fin n)))
    (L κh : ℝ) : ℝ :=
  Section01.TRqIDA.sourceRadiusCoefficient p a q f (t.point 0) (t.radius 0)
    (testRadius p t 0) L 1 κh

/-- The source coefficient is bounded by the uniform analytic radius coefficient. -/
theorem algorithm.source_bounds (h : algorithm p a q epsilon κh O t)
    {L : ℝ} (hL : 1 ≤ L) :
    0 ≤ sourceRadiusCoefficient p a q f t L κh ∧
      sourceRadiusCoefficient p a q f t L κh ≤
        ExplicitTrustRegion.radiusCoefficient p (t.radius 0) (errorCoefficient q L 1
          a.stepConstant) := by
  have hp := h.prefix 0 (by simp)
  have hh : 0 ≤ κh := (hp.request_pos 1 (Finset.mem_Icc.mpr ⟨le_rfl, h.1⟩)).le.trans
    (h.2.2.2.2.1 1 (Finset.mem_Icc.mpr ⟨le_rfl, h.1⟩))
  have hb := Section01.TRqIDA.sourceRadiusCoefficient_bounds (p := p) (a := a) (f := f)
    (x := t.point 0) h.1 hp.initial_pos.le (hp.testRadius_bounds le_rfl).1.le hL
    (by norm_num : (0 : ℝ) ≤ 1) hh
  have hc : sourceRadiusCoefficient p a q f t L κh ≤ p.theta := by
    unfold sourceRadiusCoefficient Section01.TRqIDA.sourceRadiusCoefficient
    have hD : 0 ≤ Section01.TRqIDA.initialDerivativeBound f q (t.point 0) := by
      rw [Section01.TRqIDA.initialDerivativeBound, dite_eq_left h.1]
      exact (norm_nonneg (iteratedFDeriv ℝ 1 f (t.point 0))).trans
        (Finset.le_sup' (fun i => ‖iteratedFDeriv ℝ i f (t.point 0)‖)
          (Finset.mem_Icc.mpr ⟨le_rfl, h.1⟩))
    have hr : 0 ≤ Section01.TRqIDA.initialRadiusPower q (testRadius p t 0) := by
      rw [Section01.TRqIDA.initialRadiusPower, dite_eq_left h.1]
      exact Finset.le_inf' _ _ (fun j _ => pow_nonneg (hp.testRadius_bounds le_rfl).1.le j)
    have hsecond : 0 ≤ min p.theta
        (t.radius 0 * Section01.TRqIDA.initialRadiusPower q (testRadius p t 0) /
          (2 * q * (Section01.TRqIDA.initialDerivativeBound f q (t.point 0) + 1 * κh))) := by
      exact le_min p.theta_pos.le (div_nonneg (mul_nonneg hp.initial_pos.le hr)
        (mul_nonneg (by positivity) (by linarith)))
    exact (mul_le_of_le_one_left hsecond (min_le_left _ _)).trans (min_le_left _ _)
  exact ⟨hb.1, le_min (hc.trans h.2.2.2.1) (le_min hb.2.1 hb.2.2)⟩

/-- The source testing-radius floor holds at every reachable state before certification. -/
theorem algorithm.testRadius_lower (h : algorithm p a q epsilon κh O t)
    {L : ℝ} (hL : 1 ≤ L)
    (hf : ∀ j, 1 ≤ j → j ≤ q → HigherOrderRegularization.DiagonalLipschitz f j L)
    {k : ℕ} (hn : ∀ j < k,
      ¬Certified p epsilon (Chapter12.Section02.TRq.epsilonMinimum q epsilon) O t j) :
    sourceRadiusCoefficient p a q f t L κh * p.fraction *
      Chapter12.Section02.TRq.epsilonMinimum q epsilon / 2 ≤ testRadius p t k := by
  have hp := h.prefix k hn
  have he := h.minimum_bounds
  have hc := h.source_bounds hL
  have hmain := hp.radius_lower he.1 he.2 h.2.2.1
    (fun j hj hjq => Chapter12.Section02.TRq.epsilonMinimum_le epsilon hj hjq)
    (by norm_num) (zero_lt_one.trans_le hL) O.uniformAccuracy hf le_rfl
  have hfrac := p.fraction_pos
  have hmul := mul_le_mul_of_nonneg_right hc.2 (mul_nonneg hfrac.le he.1.le)
  have hr : sourceRadiusCoefficient p a q f t L κh * p.fraction *
      Chapter12.Section02.TRq.epsilonMinimum q epsilon / 2 ≤ t.radius k := by
    nlinarith only [hmul, hmain]
  have hcoeffone := (hc.2.trans (ExplicitTrustRegion.radiusCoefficient_le_one _ _))
  have hmulone := mul_le_mul_of_nonneg_right hcoeffone (mul_nonneg hfrac.le he.1.le)
  have heps := mul_le_mul_of_nonneg_right p.fraction_le_one he.1.le
  exact le_min hr (by nlinarith [h.2.2.1])

end TRqEDA

/-- Algorithm 13.3.1, using the known absolute-error oracle and an observable joint certificate. -/
abbrev algorithm_13_3_1 := @TRqEDA.algorithm

variable {p : Parameters} {a : AccuracyParameters} {q : ℕ} {epsilon : ℕ → ℝ} {κh : ℝ}
  {f : EuclideanSpace ℝ (Fin n) → ℝ} {O : ExplicitAccuracyOracle f q}
  {t : ExplicitTrustRegion.Trace (EuclideanSpace ℝ (Fin n))}

/-- Lemma 13.3.1: the IDA radius condition with known multiplier one makes the actual
inexact-value ratio very successful; the next radius is at least the current radius. -/
theorem lemma_13_3_1 (h : algorithm_13_3_1 p a q epsilon κh O t)
    {L : ℝ} (hL : 0 < L)
    (hf : ∀ j, 1 ≤ j → j ≤ q → HigherOrderRegularization.DiagonalLipschitz f j L)
    {N k : ℕ} (hn : ∀ j < N,
      ¬Certified p epsilon (Chapter12.Section02.TRq.epsilonMinimum q epsilon) O t j)
    (hk : k < N) (ht : t.branch k = .trial)
    (hr : t.radius k ≤ min p.theta ((1 - p.eta2) * scaledGap p O t k /
      errorCoefficient q L 1 a.stepConstant)) :
    p.eta2 ≤ ratio O t k ∧ t.radius k ≤ t.radius (k + 1) := by
  have hp := h.prefix N hn
  have hks := a.stepConstant_pos
  have hC : 0 < errorCoefficient q L 1 a.stepConstant := by
    dsimp [errorCoefficient, InexactTrustRegion.errorCoefficient]
    positivity
  have hs := hp.ratio_ge_of_radius (fun j hj hjq => (h.2.1 j hj hjq).1)
    (by norm_num) hL.le O.uniformAccuracy hf hk ht (hr.trans (min_le_left _ _))
    (by simpa only [mul_comm] using (le_div_iff₀ hC).mp (hr.trans (min_le_right _ _)))
  exact ⟨hs, hp.radius_nondecrease hk ht hs⟩

/-- Lemma 13.3.2: the unchanged source model-decrease bound and the accepted true-objective
bound, retaining the factor one half needed to absorb both inexact endpoint errors. -/
theorem lemma_13_3_2 (h : algorithm_13_3_1 p a q epsilon κh O t)
    {L : ℝ} (hL : 1 ≤ L)
    (hf : ∀ j, 1 ≤ j → j ≤ q → HigherOrderRegularization.DiagonalLipschitz f j L)
    {N k : ℕ} (hn : ∀ j < N,
      ¬Certified p epsilon (Chapter12.Section02.TRq.epsilonMinimum q epsilon) O t j)
    (hk : k < N) (ht : t.branch k = .trial) :
    let b := TRqEDA.sourceRadiusCoefficient p a q f t L κh * p.fraction *
      Chapter12.Section02.TRq.epsilonMinimum q epsilon / 2
    b ^ (q + 1) / (q ! : ℝ) ≤ prediction O t k (t.order k) (t.step k) ∧
      (Successful p O t k → p.eta1 * b ^ (q + 1) / (2 * (q ! : ℝ)) ≤
        f (t.point k) - f (t.point (k + 1))) := by
  intro b
  have hp := h.prefix N hn
  have he := h.minimum_bounds
  have hc := h.source_bounds hL
  have hb : 0 ≤ b := by
    have hcn := hc.1
    have hfrac := p.fraction_pos
    have hepos := he.1
    dsimp [b]
    positivity
  have hpre : ∀ j < k,
      ¬Certified p epsilon (Chapter12.Section02.TRq.epsilonMinimum q epsilon) O t j :=
    fun j hj => hn j (by omega)
  have hr := h.testRadius_lower hL hf hpre
  have hb1 : b ≤ 1 := hr.trans (hp.testRadius_bounds (k := k) (by omega)).2
  have hco := hc.2.trans (ExplicitTrustRegion.radiusCoefficient_le_one _ _)
  have hg := hp.scaledGap_lower
    (fun j hj hjq => Chapter12.Section02.TRq.epsilonMinimum_le epsilon hj hjq) hk
    (by simp [ht])
  have hmul := mul_le_mul_of_nonneg_right hco (mul_nonneg p.fraction_pos.le he.1.le)
  have hd := hp.predicted_lower_of_radius hb hb1 hk (by simp [ht]) hr
    (by dsimp [b]; nlinarith only [hmul, hg])
  refine ⟨hd, ?_⟩
  intro hs
  have ha := hp.accepted_decrease (fun j hj hjq => (h.2.1 j hj hjq).1) hk hs
  have hm := mul_le_mul_of_nonneg_left hd p.eta1_pos.le
  have hx := (div_le_div_of_nonneg_right hm (by norm_num : (0 : ℝ) ≤ 2)).trans ha
  convert hx using 1; ring

/-- Lemma 13.3.3: a reachable computed pass and explicit error check certify all true gaps.
At any reachable Step 1.4, the source request threshold (13.1.37), with multiplier one,
forces that certificate and therefore prevents a return to the accuracy-refinement branch. -/
theorem lemma_13_3_3 (h : algorithm_13_3_1 p a q epsilon κh O t)
    {k : ℕ} (hn : ∀ j < k,
      ¬Certified p epsilon (Chapter12.Section02.TRq.epsilonMinimum q epsilon) O t j)
    (hpass : AllPass p epsilon O t k) :
    (ErrorCheck p q (Chapter12.Section02.TRq.epsilonMinimum q epsilon) t k →
      Quality (q := q) p epsilon f t k) ∧
    (∀ L : ℝ, 1 ≤ L →
      (∀ j, 1 ≤ j → j ≤ q → HigherOrderRegularization.DiagonalLipschitz f j L) →
      ∀ H : ℝ, 0 ≤ H → (∀ i ∈ Finset.Icc 1 q, t.request k i ≤ H) →
      4 * H ≤ p.fraction * Chapter12.Section02.TRq.epsilonMinimum q epsilon *
        (TRqEDA.sourceRadiusCoefficient p a q f t L κh * p.fraction *
          Chapter12.Section02.TRq.epsilonMinimum q epsilon / 2) ^ q / (q ! : ℝ) →
      Certified p epsilon (Chapter12.Section02.TRq.epsilonMinimum q epsilon) O t k) := by
  have hp := h.prefix k hn
  have he := h.minimum_bounds
  refine ⟨fun hc => hp.certified_quality he.1.le
    (fun j hj hjq => Chapter12.Section02.TRq.epsilonMinimum_le epsilon hj hjq)
    le_rfl ⟨hpass, hc⟩, ?_⟩
  intro L hL hf H hH hh hsmall
  refine ⟨hpass, hp.errorCheck_of_requests hH le_rfl hh (hsmall.trans ?_)⟩
  have hc := h.source_bounds hL
  have hcn := hc.1
  have hepos := he.1
  have hb : 0 ≤ TRqEDA.sourceRadiusCoefficient p a q f t L κh * p.fraction *
      Chapter12.Section02.TRq.epsilonMinimum q epsilon / 2 := by
    have hv := p.fraction_pos
    positivity
  have hr := h.testRadius_lower hL hf hn
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ hb hr q) (mul_nonneg p.fraction_pos.le he.1.le)) (by positivity)

/-- Theorem 13.3.4: fixed positive coefficients, chosen before tolerances and traces, bound
both actual inexact-value calls and eager derivative batches at certified termination.
The all-orders conclusion uses the corrected index `phi_j` in the printed final formula.
The eager derivative schedule includes initialization, accuracy refinements and final checks;
rejected trials reuse their derivative tensors. -/
theorem theorem_13_3_4 (p : Parameters) (a : AccuracyParameters) (q : ℕ)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (O : ExplicitAccuracyOracle f q)
    (hf : Section01.ImplicitSmoothness f q) {initial κh low : ℝ}
    (hi : 0 < initial) (hlow : ∀ x, low ≤ f x) :
    ∃ A B C D F : ℝ, 0 < A ∧ 0 < B ∧ 0 < C ∧ 0 < D ∧ 0 < F ∧
      ∀ (epsilon : ℕ → ℝ) (t : ExplicitTrustRegion.Trace (EuclideanSpace ℝ (Fin n))),
        t.radius 0 = initial → algorithm_13_3_1 p a q epsilon κh O t →
          ∃ k : ℕ, Certified p epsilon (Chapter12.Section02.TRq.epsilonMinimum q epsilon) O t k ∧
            Quality (q := q) p epsilon f t k ∧
            (∀ j < k,
              ¬Certified p epsilon (Chapter12.Section02.TRq.epsilonMinimum q epsilon) O t j) ∧
            (0 < testRadius p t k ∧ testRadius p t k ≤ 1) ∧
            ((functionQueries t k).length : ℝ) ≤
              A * (f (t.point 0) - low) /
                  Chapter12.Section02.TRq.epsilonMinimum q epsilon ^ (q + 1) +
                B * |Real.log (Chapter12.Section02.TRq.epsilonMinimum q epsilon)| + C ∧
            ((derivativeQueries p O t k).length : ℝ) ≤
              A * (f (t.point 0) - low) /
                  Chapter12.Section02.TRq.epsilonMinimum q epsilon ^ (q + 1) +
                D * |Real.log (Chapter12.Section02.TRq.epsilonMinimum q epsilon)| + F := by
  by_cases hκh : 0 < κh
  · obtain ⟨L, hL, hfL, hnorm⟩ := Section01.TRqIDA.exists_uniform_smoothness hf
    have hLp : 0 < L := zero_lt_one.trans_le hL
    let M := L + κh
    have hM : 0 < M := by dsimp [M]; positivity
    obtain ⟨hA, hB, hC, hS, hD, hF⟩ :=
      evaluationRates_pos (p := p) (a := a) (q := q) (M := M) (H0 := κh) hi hLp
        (by norm_num : (0 : ℝ) ≤ 1)
    refine ⟨2 * functionRate p a q initial L 1 + successEvaluationRate p a q initial L 1,
      2 * functionLogRate p, 2 * functionOffsetRate p a q initial L 1,
      derivativeLogRate a q, derivativeOffsetRate p a q initial L 1 M κh,
      by positivity, by positivity, by positivity, hD, hF, ?_⟩
    intro epsilon t hinit h
    have he := h.minimum_bounds
    have hAactual : ∀ k,
        (∀ j < k,
          ¬Certified p epsilon (Chapter12.Section02.TRq.epsilonMinimum q epsilon) O t j) →
        ∀ i ∈ Finset.Icc 1 q, ‖coefficients O t k i‖ ≤ M := by
      intro k hn i hi
      have hp := h.prefix k hn
      have he := O.derivative_accuracy (t.point k) (t.request k)
        (fun i hi => hp.requests_pos le_rfl hi) i hi
      have hnrm := hnorm (t.point k) i (Finset.mem_Icc.mp hi).1 (Finset.mem_Icc.mp hi).2
      have hreq := h.request_le_initial_bound hn hi
      have htri := norm_add_le (O.derivative (t.point k) (t.request k) i -
        iteratedFDeriv ℝ i f (t.point k)) (iteratedFDeriv ℝ i f (t.point k))
      rw [sub_add_cancel] at htri
      change ‖O.derivative (t.point k) (t.request k) i‖ ≤ M
      dsimp [M]
      linarith
    obtain ⟨k, hc, hfirst, hr, hfc, hdc⟩ :=
      IsExecution.exists_first_certificate_rates h.2.2.2.2.2 h.1 he h.2.2.1
        (fun j hj hjq => Chapter12.Section02.TRq.epsilonMinimum_le epsilon hj hjq)
        h.2.2.2.2.1 hκh hinit hLp (by norm_num) hM O.uniformAccuracy hfL hAactual hlow
    have hquality := (h.prefix k hfirst).certified_quality he.1.le
      (fun j hj hjq => Chapter12.Section02.TRq.epsilonMinimum_le epsilon hj hjq) le_rfl hc
    have hgap : 0 ≤ f (t.point 0) - low := sub_nonneg.mpr (hlow _)
    have hfunc : 2 * functionRate p a q initial L 1 * (f (t.point 0) - low) /
        Chapter12.Section02.TRq.epsilonMinimum q epsilon ^ (q + 1) ≤
        (2 * functionRate p a q initial L 1 + successEvaluationRate p a q initial L 1) *
          (f (t.point 0) - low) /
            Chapter12.Section02.TRq.epsilonMinimum q epsilon ^ (q + 1) := by
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_right hS.le) hgap) (pow_nonneg he.1.le _)
    have hderiv : successEvaluationRate p a q initial L 1 * (f (t.point 0) - low) /
        Chapter12.Section02.TRq.epsilonMinimum q epsilon ^ (q + 1) ≤
        (2 * functionRate p a q initial L 1 + successEvaluationRate p a q initial L 1) *
          (f (t.point 0) - low) /
            Chapter12.Section02.TRq.epsilonMinimum q epsilon ^ (q + 1) := by
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_left (mul_nonneg (by norm_num) hA.le)) hgap)
        (pow_nonneg he.1.le _)
    exact ⟨k, hc, hquality, hfirst, hr, by linarith, by linarith⟩
  · refine ⟨1, 1, 1, 1, 1, by norm_num, by norm_num, by norm_num,
      by norm_num, by norm_num, ?_⟩
    intro epsilon t _ h
    have hp := h.prefix 0 (by simp)
    have hpos := hp.request_pos 1 (Finset.mem_Icc.mpr ⟨le_rfl, h.1⟩)
    have hcap := h.2.2.2.2.1 1 (Finset.mem_Icc.mpr ⟨le_rfl, h.1⟩)
    exact (hκh (hpos.trans_le hcap)).elim

end CartisGouldToint.Chapter13.Section03
