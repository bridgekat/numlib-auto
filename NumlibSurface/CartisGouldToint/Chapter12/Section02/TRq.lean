import Numlib.Optimization.HigherOrderTrustRegion
import NumlibSurface.CartisGouldToint.Chapter12.Section02

/-!
# Chapter 12, Section 2: the TRq algorithm

The arbitrary-order algorithm uses actual Taylor witnesses, their first failing order, actual
acceptance ratios, and the three printed radius intervals. All legal-prefix requirements stop
at the first actual termination test. The complexity theorem includes every requested order,
a first stopping index, and cached function and derivative-batch counts.
-/

noncomputable section
open scoped Nat
open Optimization Metric Set
namespace CartisGouldToint.Chapter12.Section02
namespace TRq
open HigherOrderTrustRegion
variable {n : ℕ}

/-- The smallest requested tolerance, with zero used only for the excluded order-zero case. -/
def epsilonMinimum (q : ℕ) (epsilon : ℕ → ℝ) : ℝ :=
  if h : 1 ≤ q then (Finset.Icc 1 q).inf' (by simp [h]) epsilon else 0

/-- The minimum tolerance lies below each active tolerance. -/
theorem epsilonMinimum_le {q j : ℕ} (epsilon : ℕ → ℝ) (hj : 1 ≤ j) (hjq : j ≤ q) :
    epsilonMinimum q epsilon ≤ epsilon j := by
  rw [epsilonMinimum, dite_eq_left (hj.trans hjq)]
  exact Finset.inf'_le _ (Finset.mem_Icc.mpr ⟨hj, hjq⟩)

/-- Positive active tolerances have a positive finite minimum. -/
theorem epsilonMinimum_pos {q : ℕ} {epsilon : ℕ → ℝ} (hq : 1 ≤ q)
    (he : ∀ j, 1 ≤ j → j ≤ q → 0 < epsilon j) : 0 < epsilonMinimum q epsilon := by
  rw [epsilonMinimum, dite_eq_left hq]
  obtain ⟨j, hj, heq⟩ := Finset.exists_mem_eq_inf' (s := Finset.Icc 1 q) (by simp [hq]) epsilon
  rw [heq]
  exact he j (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2

/-- The exact Algorithm 12.2.1 obligations. Legal prefixes include fractional global Taylor
witnesses at every requested order, the increasing first-failure scan, selected-order model
step domination, acceptance/rejection and all three radius intervals. -/
def algorithm (p : Parameters) (q : ℕ) (epsilon : ℕ → ℝ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (t : Trace (EuclideanSpace ℝ (Fin n))) : Prop :=
  1 ≤ q ∧ (∀ j, 1 ≤ j → j ≤ q → 0 < epsilon j ∧ epsilon j ≤ 1) ∧
    epsilonMinimum q epsilon ≤ p.theta ∧ IsRun p q epsilon f t

variable {p : Parameters} {q : ℕ} {epsilon : ℕ → ℝ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {t : Trace (EuclideanSpace ℝ (Fin n))}

/-- The source assumptions give positive and unit-bounded minimum tolerance. -/
theorem algorithm.minimum_bounds (h : algorithm p q epsilon f t) :
    0 < epsilonMinimum q epsilon ∧ epsilonMinimum q epsilon ≤ 1 :=
  ⟨epsilonMinimum_pos h.1 (fun j hj hjq => (h.2.1 j hj hjq).1),
    (epsilonMinimum_le epsilon le_rfl h.1).trans (h.2.1 1 le_rfl h.1).2⟩

end TRq
open HigherOrderTrustRegion
variable {n : ℕ}

/-- Algorithm 12.2.1, with no convergence or complexity result assumed as a run field. -/
abbrev algorithm_12_2_1 := @TRq.algorithm

variable {p : Parameters} {q : ℕ} {epsilon : ℕ → ℝ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {t : Trace (EuclideanSpace ℝ (Fin n))}

/-- Lemma 12.2.1: the historical scaled gap and selected-order predicted decrement. -/
theorem lemma_12_2_1 (h : algorithm_12_2_1 p q epsilon f t) {k : ℕ}
    (hk : ∀ i ≤ k, ¬Stops p q epsilon f t i) :
    p.fraction * TRq.epsilonMinimum q epsilon ≤ runningGap p f t k ∧
    trqScaledGap f (t.order k) (testRadius p t k) (t.point k)
      (t.witness k (t.order k)) * testRadius p t k ^ t.order k / ((t.order k)! : ℝ) ≤
        Section01.taylorDecrement f (t.order k) (t.point k) (t.step k) := by
  have hp := h.2.2.2 (k + 1) (fun i hi => hk i (by omega))
  constructor
  · apply le_runningGap
    intro i hi
    exact (hp.scaledGap_lower (fun j hj hjq => TRq.epsilonMinimum_le epsilon hj hjq)
      (by omega : i < k + 1)).le
  · exact hp.predicted_ge_scaledGap (by omega)

/-- Lemma 12.2.2: the printed small-radius condition implies a very successful trial and
nondecreasing radius, using the actual selected-order Taylor remainder. -/
theorem lemma_12_2_2 (h : algorithm_12_2_1 p q epsilon f t) {L : ℕ → ℝ}
    (hf : LipschitzDerivativeFamily f q L) {k : ℕ}
    (hk : ∀ i ≤ k, ¬Stops p q epsilon f t i)
    (hr : t.radius k ≤ min p.theta ((1 - p.eta2) * scaledGap p f t k /
      derivativeFamilyConstant q L)) :
    p.eta2 ≤ ratio f t k ∧ t.radius k ≤ t.radius (k + 1) := by
  have hp := h.2.2.2 (k + 1) (fun i hi => hk i (by omega))
  have hL : 0 < derivativeFamilyConstant q L := zero_lt_one.trans_le (hf.one_le_constant h.1)
  have ha := hp.ratio_ge_of_radius (fun j hj hjq => (h.2.1 j hj hjq).1)
    (fun j hj hjq => hf.at_order_max hj hjq) (k := k) (by omega) (hr.trans (min_le_left _ _))
    (by have hb := (le_div_iff₀ hL).mp (hr.trans (min_le_right _ _)); nlinarith)
  exact ⟨ha, hp.radius_nondecrease (by omega) ha⟩

/-- The initial maximum of the source diagonal tensor norms. -/
def trqInitialDerivativeMaximum (f : EuclideanSpace ℝ (Fin n) → ℝ) (q : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  if h : 1 ≤ q then (Finset.Icc 1 q).sup' (by simp [h])
    (fun j => (iteratedFDeriv ℝ j f x).diagonalNorm) else 0

/-- The coefficient printed in (12.2.14), with `2 * q!` interpreted correctly. -/
def trqRadiusConstant (p : Parameters) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (q : ℕ) (L : ℕ → ℝ) (t : Trace (EuclideanSpace ℝ (Fin n))) : ℝ :=
  p.gamma1 * (1 - p.eta2) / derivativeFamilyConstant q L * min p.theta
    (t.radius 0 * testRadius p t 0 ^ q /
      (2 * (q ! : ℝ) * trqInitialDerivativeMaximum f q (t.point 0)))

/-- Every active initial tensor norm is below the initial maximum. -/
theorem diagonalNorm_le_trqInitialDerivativeMaximum {i : ℕ} (hi : 1 ≤ i) (hiq : i ≤ q) :
    (iteratedFDeriv ℝ i f (t.point 0)).diagonalNorm ≤
      trqInitialDerivativeMaximum f q (t.point 0) := by
  rw [trqInitialDerivativeMaximum, dite_eq_left (hi.trans hiq)]
  exact Finset.le_sup' (fun j => (iteratedFDeriv ℝ j f (t.point 0)).diagonalNorm)
    (Finset.mem_Icc.mpr ⟨hi, hiq⟩)

/-- Lemma 12.2.3: the printed historical-gap lower radius bound and positive coefficient.
An initial nonterminal witness forces a nonzero initial derivative maximum, so the printed
division has a positive denominator. -/
theorem lemma_12_2_3 (h : algorithm_12_2_1 p q epsilon f t) {L : ℕ → ℝ}
    (hf : LipschitzDerivativeFamily f q L) {k : ℕ}
    (hk : ∀ i ≤ k, ¬Stops p q epsilon f t i) :
    0 < trqRadiusConstant p f q L t ∧ trqRadiusConstant p f q L t < p.gamma1 ∧
    min (p.gamma1 * p.theta) (trqRadiusConstant p f q L t * runningGap p f t k) ≤
      t.radius k := by
  have hp := h.2.2.2 (k + 1) (fun i hi => hk i (by omega))
  let M := trqInitialDerivativeMaximum f q (t.point 0)
  let D := testRadius p t 0
  let A := p.gamma1 * (1 - p.eta2) / derivativeFamilyConstant q L
  have hL := hf.one_le_constant h.1
  have hLpos : 0 < derivativeFamilyConstant q L := zero_lt_one.trans_le hL
  have hM : 0 ≤ M :=
    (iteratedFDeriv ℝ 1 f (t.point 0)).diagonalNorm_nonneg.trans
      (diagonalNorm_le_trqInitialDerivativeMaximum le_rfl h.1)
  have hD : 0 < D := (hp.testRadius_bounds (k := 0) (by omega)).1
  have hbound := hp.initial_scaledGap_upper (by omega : 0 < k + 1) hM
    (fun i hi hiq => diagonalNorm_le_trqInitialDerivativeMaximum hi hiq)
  have hsg : 0 < scaledGap p f t 0 := by
    have hh := hp.scaledGap_lower
      (fun j hj hjq => TRq.epsilonMinimum_le epsilon hj hjq) (k := 0) (by omega)
    exact (mul_pos p.fraction_pos h.minimum_bounds.1).trans hh
  have hMpos : 0 < M := by
    by_contra hn
    have hz : M = 0 := le_antisymm (le_of_not_gt hn) hM
    change scaledGap p f t 0 ≤ 2 * (q ! : ℝ) * M / D ^ q at hbound
    rw [hz, mul_zero, zero_div] at hbound
    exact (not_le_of_gt hsg) hbound
  have hA : 0 < A := div_pos
    (mul_pos p.gamma1_pos (sub_pos.mpr p.eta2_lt_one)) hLpos
  have hAgamma : A < p.gamma1 := by
    apply (div_lt_iff₀ hLpos).mpr
    have heta := p.eta1_pos.trans_le p.eta_le
    have hh := mul_pos p.gamma1_pos heta
    nlinarith [mul_le_mul_of_nonneg_left hL p.gamma1_pos.le]
  have hAone : A < 1 := hAgamma.trans_le (p.gamma_le.trans p.gamma2_lt_one.le)
  let B := t.radius 0 * D ^ q / (2 * (q ! : ℝ) * M)
  have hB : 0 < B := div_pos (mul_pos hp.initial_pos (pow_pos hD q))
    (mul_pos (mul_pos (by norm_num) (by positivity)) hMpos)
  have hc : 0 < trqRadiusConstant p f q L t := mul_pos hA (lt_min p.theta_pos hB)
  have hcleA : trqRadiusConstant p f q L t ≤ A := by
    have hh : min p.theta B ≤ 1 := (min_le_left _ _).trans p.theta_le_one
    exact mul_le_of_le_one_right hA.le hh
  have hcleB : trqRadiusConstant p f q L t ≤ B :=
    (mul_le_mul_of_nonneg_left (min_le_right p.theta B) hA.le).trans
      (mul_le_of_le_one_left hB.le hAone.le)
  have hinit : trqRadiusConstant p f q L t * scaledGap p f t 0 ≤ t.radius 0 := by
    have hh := mul_le_mul_of_nonneg_left hbound hc.le
    have hz := mul_le_mul_of_nonneg_right hcleB
      (div_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * (q ! : ℝ)) hM)
        (pow_nonneg hD.le q))
    calc
      _ ≤ trqRadiusConstant p f q L t * (2 * (q ! : ℝ) * M / D ^ q) := hh
      _ ≤ B * (2 * (q ! : ℝ) * M / D ^ q) := hz
      _ = t.radius 0 := by dsimp [B]; field_simp
  exact ⟨hc, hcleA.trans_lt hAgamma, hp.radius_lower_runningGap
    (fun j hj hjq => (h.2.1 j hj hjq).1) hLpos (fun j hj hjq => hf.at_order_max hj hjq)
      hc.le hcleA hinit (by omega)⟩

/-- Lemma 12.2.4: the printed model decrease and accepted objective decrease for arbitrary
requested order, with the source coefficient from (12.2.14). -/
theorem lemma_12_2_4 (h : algorithm_12_2_1 p q epsilon f t) {L : ℕ → ℝ}
    (hf : LipschitzDerivativeFamily f q L) {k : ℕ}
    (hk : ∀ i ≤ k, ¬Stops p q epsilon f t i) :
    (p.fraction * trqRadiusConstant p f q L t) ^ (q + 1) *
      TRq.epsilonMinimum q epsilon ^ (q + 1) / (q ! : ℝ) ≤
        Section01.taylorDecrement f (t.order k) (t.point k) (t.step k) ∧
    (p.eta1 ≤ ratio f t k → p.eta1 * ((p.fraction * trqRadiusConstant p f q L t) ^
      (q + 1) * TRq.epsilonMinimum q epsilon ^ (q + 1) / (q ! : ℝ)) ≤
        f (t.point k) - f (t.point (k + 1))) := by
  have hp := h.2.2.2 (k + 1) (fun i hi => hk i (by omega))
  obtain ⟨hc, hcg, hr⟩ := lemma_12_2_3 h hf hk
  let a := trqRadiusConstant p f q L t * p.fraction * TRq.epsilonMinimum q epsilon
  have he := h.minimum_bounds
  have hc1 : trqRadiusConstant p f q L t ≤ 1 :=
    hcg.le.trans (p.gamma_le.trans p.gamma2_lt_one.le)
  have hfe : p.fraction * TRq.epsilonMinimum q epsilon ≤ TRq.epsilonMinimum q epsilon :=
    mul_le_of_le_one_left he.1.le p.fraction_le_one
  have ha : 0 < a := mul_pos (mul_pos hc p.fraction_pos) he.1
  have hae : a ≤ TRq.epsilonMinimum q epsilon :=
    (show a ≤ p.fraction * TRq.epsilonMinimum q epsilon from
      by dsimp [a]; nlinarith [mul_nonneg p.fraction_pos.le he.1.le]).trans hfe
  have hrad : a ≤ t.radius k := by
    apply le_trans (le_min ?_ ?_) hr
    · have hh := mul_le_mul_of_nonneg_right hcg.le
        (mul_nonneg p.fraction_pos.le he.1.le)
      have hz := mul_le_mul_of_nonneg_left (hfe.trans h.2.2.1) p.gamma1_pos.le
      dsimp [a]; nlinarith
    · have hg := (lemma_12_2_1 h hk).1
      have hh := mul_le_mul_of_nonneg_left hg hc.le
      dsimp [a]; nlinarith
  have hgap : a ≤ scaledGap p f t k := by
    have hh := hp.scaledGap_lower
      (fun j hj hjq => TRq.epsilonMinimum_le epsilon hj hjq) (k := k) (by omega)
    have hz : a ≤ p.fraction * TRq.epsilonMinimum q epsilon := by
      dsimp [a]; nlinarith [mul_nonneg p.fraction_pos.le he.1.le]
    exact hz.trans hh.le
  have hd := hp.predicted_lower_of_radius ha.le (hae.trans he.2) (k := k) (by omega)
    (le_min hrad (hae.trans h.2.2.1)) hgap
  have heq : a ^ (q + 1) / (q ! : ℝ) =
      (p.fraction * trqRadiusConstant p f q L t) ^ (q + 1) *
        TRq.epsilonMinimum q epsilon ^ (q + 1) / (q ! : ℝ) := by
    dsimp [a]; rw [mul_pow]; congr 2; ring
  rw [heq] at hd
  refine ⟨hd, fun hs => ?_⟩
  exact (mul_le_mul_of_nonneg_left hd p.eta1_pos.le).trans
    (hp.accepted_decrease (fun j hj hjq => (h.2.1 j hj hjq).1) (by omega) hs)

/-- Theorem 12.2.5: finite termination for every requested positive order, with a first
actual stopping index, all true gap criteria, and both cached oracle counts. Its explicit
power and logarithmic constants are independent of the tolerance and the testing cap. -/
theorem trq_complexity_explicit (h : algorithm_12_2_1 p q epsilon f t) {L : ℕ → ℝ}
    (hf : LipschitzDerivativeFamily f q L) {low : ℝ} (hlow : ∀ x, low ≤ f x) :
    ∃ K ≤ ⌊trialBudget p q (t.radius 0) (derivativeFamilyConstant q L)
      (f (t.point 0) - low) (TRq.epsilonMinimum q epsilon)⌋₊,
      Stops p q epsilon f t K ∧ (∀ i < K, ¬Stops p q epsilon f t i) ∧
      Section01.IsApproxOrderMinimizer f (t.point K) q epsilon
        (fun _ => testRadius p t K) ∧
      (functionEvaluations K : ℝ) ≤ trialBudget p q (t.radius 0) (derivativeFamilyConstant q L)
        (f (t.point 0) - low) (TRq.epsilonMinimum q epsilon) + 1 ∧
      (derivativeBatches p f t K : ℝ) ≤
        successCoefficient p q (t.radius 0) (derivativeFamilyConstant q L) *
          (f (t.point 0) - low) / TRq.epsilonMinimum q epsilon ^ (q + 1) + 1 := by
  obtain ⟨K, hK, hs, hfirst, hr, hg, hfc, hdc⟩ := h.2.2.2.complexity
    h.minimum_bounds.1 h.minimum_bounds.2 h.2.2.1
    (fun j hj hjq => TRq.epsilonMinimum_le epsilon hj hjq)
    (zero_lt_one.trans_le (hf.one_le_constant h.1))
    (fun j hj hjq => hf.at_order_max hj hjq) hlow
  refine ⟨K, hK, hs, hfirst, ?_, hfc, hdc⟩
  apply Section01.isApproxOrderMinimizer_iff.mpr
  exact ⟨h.1, fun j hj hjq => ⟨(h.2.1 j hj hjq).1, (h.2.1 j hj hjq).2,
    hr.1, hr.2, hg j hj hjq⟩⟩

/-- Theorem 12.2.5 in its printed constant form. Positive constants `A,B,C,S` depend on the
objective smoothness bound, requested order, initial radius and fixed update parameters;
none of their definitions involve the accuracy vector or testing cap. The first actual stop
satisfies every order criterion, with cached evaluation counts and an integer floor bound. -/
theorem theorem_12_2_5 (h : algorithm_12_2_1 p q epsilon f t) {L : ℕ → ℝ}
    (hf : LipschitzDerivativeFamily f q L) {low : ℝ} (hlow : ∀ x, low ≤ f x) :
    ∃ A B C S : ℝ, 0 < A ∧ 0 < B ∧ 0 < C ∧ 0 < S ∧
      ∃ K ≤ ⌊A * (f (t.point 0) - low) / TRq.epsilonMinimum q epsilon ^ (q + 1) +
        B * |Real.log (TRq.epsilonMinimum q epsilon)| + C - 1⌋₊,
        Stops p q epsilon f t K ∧ (∀ i < K, ¬Stops p q epsilon f t i) ∧
        Section01.IsApproxOrderMinimizer f (t.point K) q epsilon
          (fun _ => testRadius p t K) ∧
        (functionEvaluations K : ℝ) ≤
          A * (f (t.point 0) - low) / TRq.epsilonMinimum q epsilon ^ (q + 1) +
            B * |Real.log (TRq.epsilonMinimum q epsilon)| + C ∧
        (derivativeBatches p f t K : ℝ) ≤
          S * (f (t.point 0) - low) / TRq.epsilonMinimum q epsilon ^ (q + 1) + 1 := by
  have hp := h.2.2.2 0 (by simp)
  have hL : 0 < derivativeFamilyConstant q L := zero_lt_one.trans_le (hf.one_le_constant h.1)
  obtain ⟨hA, hB, hC, hS⟩ := complexity_constants_pos (p := p) (q := q) hp.initial_pos hL
  obtain ⟨K, hK, hs, hfirst, hcrit, hfc, hdc⟩ := trq_complexity_explicit h hf hlow
  refine ⟨functionCoefficient p q (t.radius 0) (derivativeFamilyConstant q L),
    logCoefficient p, offsetCoefficient p (t.radius 0) (derivativeFamilyConstant q L),
    successCoefficient p q (t.radius 0) (derivativeFamilyConstant q L),
    hA, hB, hC, hS, K, ?_, hs, hfirst, hcrit, ?_, hdc⟩
  · convert hK using 1
    congr 1
    have hh := trialBudget_add_one_eq (p := p) (q := q) (t.radius 0)
      (derivativeFamilyConstant q L) (f (t.point 0) - low) (TRq.epsilonMinimum q epsilon)
    linarith
  · rwa [trialBudget_add_one_eq] at hfc

end CartisGouldToint.Chapter12.Section02
