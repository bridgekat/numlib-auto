import Numlib.Optimization.ExplicitTrustRegionAccuracy
import Numlib.Optimization.InexactTrustRegionBounds

/-!
# Radius and decrease estimates for implicit trust-region trials

Taylor remainder and actual tensor-error estimates supply the success threshold. Radius
updates at accuracy-only iterations are identities, so the usual radius induction still applies.
-/

noncomputable section
open scoped Nat
namespace Optimization.ExplicitTrustRegion
open HigherOrderTrustRegion HigherOrderRegularization TaylorCriticality RegularizedTaylorModel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : E → ℝ} {q N : ℕ} {p : Parameters} {a : AccuracyParameters}
  {epsilon : ℕ → ℝ} {minimumTolerance : ℝ} {O : Oracle f q} {t : Trace E}

/-- A conservative common coefficient combining Taylor remainders and inexact tensor errors. -/
abbrev errorCoefficient := InexactTrustRegion.errorCoefficient

/-- The true decrease differs from the computed decrement by the two actual analytic errors. -/
theorem LegalPrefix.decrease_error (h : LegalPrefix p a epsilon minimumTolerance O t N)
    {K L : ℝ} (hK : 0 ≤ K) (hO : UniformAccuracy O K)
    (hf : ∀ j, 1 ≤ j → j ≤ q → DiagonalLipschitz f j L)
    {k : ℕ} (hk : k < N) (ht : t.branch k = .trial) :
    |(f (t.point k) - f (t.point k + t.step k)) -
      ExplicitTrustRegion.prediction O t k (t.order k) (t.step k)| ≤
      L / ((t.order k + 1)! : ℝ) * ‖t.step k‖ ^ (t.order k + 1) +
        2 * K * a.stepConstant * ‖t.step k‖ ^ (q + 1) := by
  have hn : t.branch k ≠ .testRefinement := by simp [ht]
  have hr := (hf _ (h.order_pos k hk hn) (h.order_le k hk hn)).value_remainder
    (h.order_pos k hk hn) (t.point k) (t.step k)
  have he := h.step_decrement_error hK hO hk ht
  have he' := he
  rw [abs_sub_comm] at he'
  calc
    _ = |((f (t.point k) - f (t.point k + t.step k)) -
      taylorDecrement f (t.order k) (t.point k) (t.step k)) +
      (taylorDecrement f (t.order k) (t.point k) (t.step k) -
        ExplicitTrustRegion.prediction O t k (t.order k) (t.step k))| := by congr 1; ring
    _ ≤ |(f (t.point k) - f (t.point k + t.step k)) -
      taylorDecrement f (t.order k) (t.point k) (t.step k)| +
      |taylorDecrement f (t.order k) (t.point k) (t.step k) -
        ExplicitTrustRegion.prediction O t k (t.order k) (t.step k)| := abs_add_le _ _
    _ ≤ _ := add_le_add (by simpa only [taylorDecrement_eq, sub_sub_sub_cancel_left,
      abs_sub_comm] using hr) he'

/-- A small radius forces a very successful trial, including a conservative factor
four in the error coefficient. Its two contributions are proved from the actual derivatives. -/
theorem LegalPrefix.ratio_ge_of_radius (h : LegalPrefix p a epsilon minimumTolerance O t N)
    (he : ∀ j, 1 ≤ j → j ≤ q → 0 < epsilon j)
    {K L : ℝ} (hK : 0 ≤ K) (hL : 0 ≤ L) (hO : UniformAccuracy O K)
    (hf : ∀ j, 1 ≤ j → j ≤ q → DiagonalLipschitz f j L)
    {k : ℕ} (hk : k < N) (ht : t.branch k = .trial)
    (hr : t.radius k ≤ p.theta)
    (hs : errorCoefficient q L K a.stepConstant * t.radius k ≤
      (1 - p.eta2) * ExplicitTrustRegion.scaledGap p O t k) :
    p.eta2 ≤ ExplicitTrustRegion.ratio O t k := by
  have hks := a.stepConstant_pos
  have hn : t.branch k ≠ .testRefinement := by simp [ht]
  have hrad := h.radius_pos (k := k) (by omega)
  have hr1 : t.radius k ≤ 1 := hr.trans p.theta_le_one
  have hjq := h.order_le k hk hn
  have hfac : (0 : ℝ) < ((t.order k)! : ℝ) := by positivity
  have hfacmono : 2 * ((t.order k)! : ℝ) ≤ ((t.order k + 1)! : ℝ) := by
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    have hj : (1 : ℝ) ≤ t.order k := by exact_mod_cast h.order_pos k hk hn
    nlinarith
  have hfq : ((t.order k)! : ℝ) ≤ ((q + 1)! : ℝ) :=
    Nat.cast_le.mpr (Nat.factorial_le (by omega))
  have hnorm := h.step_feasible k hk hn
  have hpj : ‖t.step k‖ ^ (t.order k + 1) ≤ t.radius k ^ (t.order k + 1) :=
    pow_le_pow_left₀ (norm_nonneg _) hnorm _
  have hpq : ‖t.step k‖ ^ (q + 1) ≤ t.radius k ^ (t.order k + 1) :=
    (pow_le_pow_left₀ (norm_nonneg _) hnorm _).trans
      (pow_le_pow_of_le_one hrad.le hr1 (by omega))
  have hR : L / ((t.order k + 1)! : ℝ) * ‖t.step k‖ ^ (t.order k + 1) ≤
      (L / 2) * t.radius k * (t.radius k ^ t.order k / ((t.order k)! : ℝ)) := by
    calc
      _ ≤ L / ((t.order k + 1)! : ℝ) * t.radius k ^ (t.order k + 1) :=
        mul_le_mul_of_nonneg_left hpj (by positivity)
      _ ≤ L / (2 * ((t.order k)! : ℝ)) * t.radius k ^ (t.order k + 1) :=
        mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_left hL (by positivity) hfacmono) (pow_nonneg hrad.le _)
      _ = _ := by rw [pow_succ]; ring
  have hE : 2 * K * a.stepConstant * ‖t.step k‖ ^ (q + 1) ≤
      (2 * ((q + 1)! : ℝ) * a.stepConstant * K) * t.radius k *
        (t.radius k ^ t.order k / ((t.order k)! : ℝ)) := by
    have hp := mul_le_mul_of_nonneg_left hpq
      (by positivity : 0 ≤ 2 * K * a.stepConstant)
    have hc : 2 * K * a.stepConstant ≤
        2 * ((q + 1)! : ℝ) * a.stepConstant * K / ((t.order k)! : ℝ) := by
      apply (le_div_iff₀ hfac).mpr
      nlinarith [mul_le_mul_of_nonneg_right hfq (mul_nonneg hK a.stepConstant_pos.le),
        mul_nonneg (mul_nonneg hK a.stepConstant_pos.le) (by positivity : (0 : ℝ) ≤ (q + 1)!)]
    have hb := mul_le_mul_of_nonneg_right hc (pow_nonneg hrad.le (t.order k + 1))
    rw [pow_succ] at hb
    apply hp.trans
    convert hb using 1 <;> ring
  have herr := (abs_le.mp (h.decrease_error hK hO hf hk ht)).1
  have hpred := h.predicted_ge_scaledGap hk hn
  simp only [ExplicitTrustRegion.testRadius, min_eq_left hr] at hpred
  have hb := mul_le_mul_of_nonneg_right hs
    (div_nonneg (pow_nonneg hrad.le (t.order k)) hfac.le)
  have hl := mul_le_mul_of_nonneg_left hpred (sub_nonneg.mpr p.eta2_lt_one.le)
  have hp := h.predicted_pos he hk hn
  have hv := h.value_request k hk ht
  have hleft := (abs_le.mp (O.value_accuracy (t.point k) _ hv.1)).1
  have hright := (abs_le.mp (O.value_accuracy (t.point k + t.step k) _ hv.1)).2
  have hvalue : (f (t.point k) - f (t.point k + t.step k)) -
      2 * t.valueRequest k ≤
      O.value (t.point k) (t.valueRequest k) -
        O.value (t.point k + t.step k) (t.valueRequest k) := by linarith
  have hbudget := (le_div_iff₀ (by norm_num : (0 : ℝ) < 4)).mp h.step_constant_success
  have hbudgetD := mul_le_mul_of_nonneg_right hbudget hp.le
  unfold ExplicitTrustRegion.ratio
  rw [le_div_iff₀ hp]
  dsimp [errorCoefficient, InexactTrustRegion.errorCoefficient] at hb
  ring_nf at hR hE herr hb hl ⊢
  nlinarith only [hR, hE, herr, hb, hl, hvalue, hv.2, hbudgetD]

/-- Very successful trials preserve or enlarge the trust-region radius. -/
theorem LegalPrefix.radius_nondecrease (h : LegalPrefix p a epsilon minimumTolerance O t N)
    {k : ℕ} (hk : k < N) (ht : t.branch k = .trial)
    (hs : p.eta2 ≤ ExplicitTrustRegion.ratio O t k) : t.radius k ≤ t.radius (k + 1) := by
  have hu := h.trial_radius k hk ht
  rw [ite_eq_left hs] at hu
  exact hu.1

/-- A common sufficient-success threshold gives a uniform radius floor through the endpoint. -/
theorem LegalPrefix.radius_lower_of_threshold (h : LegalPrefix p a epsilon minimumTolerance O t N)
    {T : ℝ} (hs : ∀ k < N, t.branch k = .trial → t.radius k ≤ T →
      p.eta2 ≤ ExplicitTrustRegion.ratio O t k) {k : ℕ} (hk : k ≤ N) :
    min (t.radius 0) (p.gamma1 * T) ≤ t.radius k := by
  induction k with
  | zero => exact min_le_left _ _
  | succ k ih =>
    have hkN : k < N := by omega
    by_cases ht : t.branch k = .trial
    · by_cases hr : t.radius k ≤ T
      · exact (ih (by omega)).trans (h.radius_nondecrease hkN ht (hs k hkN ht hr))
      · exact ((min_le_right _ _).trans
          (mul_le_mul_of_nonneg_left (le_of_not_ge hr) p.gamma1_pos.le)).trans
          (h.radius_update_lower hkN (h.radius_pos (by omega)).le)
    · rw [h.accuracy_radius k hkN ht]
      exact ih (by omega)

/-- The shared tolerance-independent radius coefficient, including accuracy-only states. -/
abbrev radiusCoefficient := InexactTrustRegion.radiusCoefficient

/-- Positive analytic bounds give a positive shared radius coefficient. -/
theorem radiusCoefficient_pos {initial C : ℝ} (hi : 0 < initial) (hC : 0 < C) :
    0 < ExplicitTrustRegion.radiusCoefficient p initial C :=
  InexactTrustRegion.radiusCoefficient_pos hi hC

/-- The shared radius coefficient is at most one. -/
theorem radiusCoefficient_le_one (initial C : ℝ) :
    ExplicitTrustRegion.radiusCoefficient p initial C ≤ 1 :=
  InexactTrustRegion.radiusCoefficient_le_one initial C

/-- Uniform radius control follows from half-threshold failures and actual analytic accuracy. -/
theorem LegalPrefix.radius_lower (h : LegalPrefix p a epsilon minimumTolerance O t N)
    {emin K L : ℝ} (hemin : 0 < emin) (heone : emin ≤ 1) (hetheta : emin ≤ p.theta)
    (he : ∀ j, 1 ≤ j → j ≤ q → emin ≤ epsilon j)
    (hK : 0 ≤ K) (hL : 0 < L) (hO : UniformAccuracy O K)
    (hf : ∀ j, 1 ≤ j → j ≤ q → DiagonalLipschitz f j L)
    {k : ℕ} (hk : k ≤ N) :
    ExplicitTrustRegion.radiusCoefficient p (t.radius 0) (errorCoefficient q L K a.stepConstant) *
      p.fraction * emin / 2 ≤ t.radius k := by
  have hks := a.stepConstant_pos
  have hfrac := p.fraction_pos
  let C := errorCoefficient q L K a.stepConstant
  have hC : 0 < C := by dsimp [C, errorCoefficient, InexactTrustRegion.errorCoefficient]; positivity
  let T := min p.theta ((1 - p.eta2) * (p.fraction * emin / 2) / C)
  have hs : ∀ i < N, t.branch i = .trial → t.radius i ≤ T →
      p.eta2 ≤ ExplicitTrustRegion.ratio O t i := by
    intro i hi ht hr
    apply h.ratio_ge_of_radius (fun j hj hjq => hemin.trans_le (he j hj hjq)) hK hL.le hO hf
      hi ht (hr.trans (min_le_left _ _))
    have hb := (le_div_iff₀ hC).mp (hr.trans (min_le_right _ _))
    have hg := h.scaledGap_lower he hi (by simp [ht])
    have hm := mul_le_mul_of_nonneg_left hg.le (sub_nonneg.mpr p.eta2_lt_one.le)
    nlinarith
  have hb := h.radius_lower_of_threshold hs hk
  apply le_trans _ hb
  apply le_min
  · have hc : ExplicitTrustRegion.radiusCoefficient p (t.radius 0) C ≤ t.radius 0 :=
      min_le_left _ _
    have heps : p.fraction * emin / 2 ≤ 1 := by nlinarith [p.fraction_le_one, p.fraction_pos]
    have hm := mul_le_mul_of_nonneg_left heps (radiusCoefficient_pos (p := p) h.initial_pos hC).le
    nlinarith
  · dsimp [T]
    rw [mul_min_of_nonneg _ _ p.gamma1_pos.le]
    apply le_min
    · have hc : ExplicitTrustRegion.radiusCoefficient p (t.radius 0) C ≤ p.gamma1 :=
        (min_le_right _ _).trans (min_le_left _ _)
      have hfe : p.fraction * emin / 2 ≤ p.theta := by nlinarith [p.fraction_le_one]
      have ha := mul_le_mul_of_nonneg_right hc
        (by positivity : 0 ≤ p.fraction * emin / 2)
      have hb := mul_le_mul_of_nonneg_left hfe p.gamma1_pos.le
      nlinarith
    · have hc : ExplicitTrustRegion.radiusCoefficient p (t.radius 0) C ≤
          p.gamma1 * (1 - p.eta2) / C :=
        (min_le_right _ _).trans (min_le_right _ _)
      have hh := mul_le_mul_of_nonneg_right hc
        (by positivity : 0 ≤ p.fraction * emin / 2)
      convert hh using 1 <;> ring

/-- A uniform scalar lower bound for both testing radius and scaled gap bounds the decrement. -/
theorem LegalPrefix.predicted_lower_of_radius (h : LegalPrefix p a epsilon minimumTolerance O t N)
    {b : ℝ} (hb : 0 ≤ b) (hb1 : b ≤ 1) {k : ℕ} (hk : k < N)
    (ht : t.branch k ≠ .testRefinement) (hr : b ≤ ExplicitTrustRegion.testRadius p t k)
    (hg : b ≤ ExplicitTrustRegion.scaledGap p O t k) :
    b ^ (q + 1) / (q ! : ℝ) ≤ ExplicitTrustRegion.prediction O t k (t.order k) (t.step k) := by
  have hp : b ^ q ≤ ExplicitTrustRegion.testRadius p t k ^ t.order k :=
    (pow_le_pow_of_le_one hb hb1 (h.order_le k hk ht)).trans (pow_le_pow_left₀ hb hr _)
  have hmul := mul_le_mul hg hp (pow_nonneg hb _) (hb.trans hg)
  have hfac : ((t.order k)! : ℝ) ≤ (q ! : ℝ) :=
    Nat.cast_le.mpr (Nat.factorial_le (h.order_le k hk ht))
  calc
    _ = b * b ^ q / (q ! : ℝ) := by rw [pow_succ]; ring
    _ ≤ ExplicitTrustRegion.scaledGap p O t k *
        ExplicitTrustRegion.testRadius p t k ^ t.order k / (q ! : ℝ) :=
      div_le_div_of_nonneg_right hmul (by positivity)
    _ ≤ ExplicitTrustRegion.scaledGap p O t k *
        ExplicitTrustRegion.testRadius p t k ^ t.order k / ((t.order k)! : ℝ) :=
      div_le_div_of_nonneg_left
        (mul_nonneg (hb.trans hg) (pow_nonneg (h.testRadius_bounds (by omega)).1.le _))
        (by positivity) hfac
    _ ≤ _ := h.predicted_ge_scaledGap hk ht

/-- Uniform decrement decrease, obtained without any hypothesis that computed passes are true
optimality certificates. It applies to the candidate of every computed candidate step. -/
theorem LegalPrefix.predicted_lower (h : LegalPrefix p a epsilon minimumTolerance O t N)
    {emin K L : ℝ} (hemin : 0 < emin) (heone : emin ≤ 1) (hetheta : emin ≤ p.theta)
    (he : ∀ j, 1 ≤ j → j ≤ q → emin ≤ epsilon j)
    (hK : 0 ≤ K) (hL : 0 < L) (hO : UniformAccuracy O K)
    (hf : ∀ j, 1 ≤ j → j ≤ q → DiagonalLipschitz f j L)
    {k : ℕ} (hk : k < N) (ht : t.branch k ≠ .testRefinement) :
    (ExplicitTrustRegion.radiusCoefficient p (t.radius 0)
      (errorCoefficient q L K a.stepConstant) * p.fraction * emin / 2) ^ (q + 1) /
        (q ! : ℝ) ≤ ExplicitTrustRegion.prediction O t k (t.order k) (t.step k) := by
  let c := ExplicitTrustRegion.radiusCoefficient p (t.radius 0)
    (errorCoefficient q L K a.stepConstant)
  have hks := a.stepConstant_pos
  have hC : 0 < errorCoefficient q L K a.stepConstant := by
    dsimp [errorCoefficient, InexactTrustRegion.errorCoefficient]; positivity
  have hc : 0 < c := radiusCoefficient_pos h.initial_pos hC
  have hc1 : c ≤ 1 := radiusCoefficient_le_one _ _
  have hfrac := p.fraction_pos
  have hcf : c * p.fraction ≤ 1 :=
    (mul_le_mul_of_nonneg_right hc1 hfrac.le).trans (by simpa using p.fraction_le_one)
  have hb : c * p.fraction * emin / 2 ≤ emin := by
    nlinarith [mul_le_mul_of_nonneg_right hcf hemin.le]
  apply h.predicted_lower_of_radius (by positivity) (hb.trans heone) hk ht
  · exact le_min (h.radius_lower hemin heone hetheta he hK hL hO hf (by omega))
      (hb.trans hetheta)
  · have hg := (h.scaledGap_lower he hk ht).le
    have hh : c * p.fraction * emin / 2 ≤ p.fraction * emin / 2 := by
      nlinarith [mul_le_mul_of_nonneg_right hc1 (mul_nonneg p.fraction_pos.le hemin.le)]
    exact hh.trans hg

/-- Actual successful trials consume the fixed objective-decrease budget. -/
theorem LegalPrefix.success_count_le (h : LegalPrefix p a epsilon minimumTolerance O t N)
    {emin K L low : ℝ} (hemin : 0 < emin) (heone : emin ≤ 1) (hetheta : emin ≤ p.theta)
    (he : ∀ j, 1 ≤ j → j ≤ q → emin ≤ epsilon j)
    (hK : 0 ≤ K) (hL : 0 < L) (hO : UniformAccuracy O K)
    (hf : ∀ j, 1 ≤ j → j ≤ q → DiagonalLipschitz f j L)
    (hlow : low ≤ f (t.point N)) :
    ((successes p O t N).card : ℝ) ≤ (f (t.point 0) - low) /
      (p.eta1 * ((ExplicitTrustRegion.radiusCoefficient p (t.radius 0)
        (errorCoefficient q L K a.stepConstant) * p.fraction * emin / 2) ^ (q + 1) /
          (q ! : ℝ)) / 2) := by
  have hks := a.stepConstant_pos
  have hfrac := p.fraction_pos
  have heta := p.eta1_pos
  have hC : 0 < errorCoefficient q L K a.stepConstant := by
    dsimp [errorCoefficient, InexactTrustRegion.errorCoefficient]; positivity
  have hc := radiusCoefficient_pos (p := p) h.initial_pos hC
  have hd : 0 < p.eta1 * ((ExplicitTrustRegion.radiusCoefficient p (t.radius 0)
      (errorCoefficient q L K a.stepConstant) * p.fraction * emin / 2) ^ (q + 1) /
        (q ! : ℝ)) / 2 := by positivity
  apply (le_div_iff₀ hd).mpr
  apply EvaluationComplexity.card_mul_le_gap
    (u := fun k => f (t.point k)) (S := successes p O t N)
    (by exact (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)) hlow
    (fun k hk => h.objective_mono (fun j hj hjq => hemin.trans_le (he j hj hjq)) hk)
  intro k hk
  have hs := Finset.mem_filter.mp hk
  have ht := Finset.mem_filter.mp hs.1
  exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
    (h.predicted_lower hemin heone hetheta he hK hL hO hf (Finset.mem_range.mp ht.1)
      (by simp [ht.2])) p.eta1_pos.le) (by norm_num : (0 : ℝ) ≤ 2)).trans
    (h.accepted_decrease (fun j hj hjq => hemin.trans_le (he j hj hjq))
      (Finset.mem_range.mp ht.1) ⟨ht.2, hs.2⟩)

/-- Coefficient norms control the actual decrement on the unit ball. -/
abbrev decrement_le_two_mul_norm := @InexactTrustRegion.decrement_le_two_mul_norm

/-- A positive decrement and bounded actual coefficients force a step floor, including steps
outside the unit ball. -/
theorem LegalPrefix.step_norm_lower_min (h : LegalPrefix p a epsilon minimumTolerance O t N)
    {M D : ℝ} (hM : 0 < M) {k : ℕ} (hk : k < N)
    (ht : t.branch k ≠ .testRefinement)
    (hA : ∀ i ∈ Finset.Icc 1 q, ‖coefficients O t k i‖ ≤ M)
    (hdec : D ≤ ExplicitTrustRegion.prediction O t k (t.order k) (t.step k)) :
    min 1 (D / (2 * M)) ≤ ‖t.step k‖ := by
  by_cases hs : ‖t.step k‖ ≤ 1
  · have hb := decrement_le_two_mul_norm (coefficients O t k) hM.le (fun i hi =>
      hA i (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hi).1,
        (Finset.mem_Icc.mp hi).2.trans (h.order_le k hk ht)⟩)) (t.step k) hs
    change D ≤ InexactTaylorModels.decrement (coefficients O t k) (t.order k) (t.step k) at hdec
    apply (min_le_right _ _).trans
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * M)).mpr
    nlinarith only [hdec, hb]
  · exact (min_le_left _ _).trans (le_of_not_ge hs)

/-- A positive candidate decrement and bounded actual coefficients force a positive step norm. -/
theorem LegalPrefix.step_norm_lower (h : LegalPrefix p a epsilon minimumTolerance O t N)
    {M D : ℝ} (hM : 0 < M) (hD1 : D / (2 * M) ≤ 1)
    {k : ℕ} (hk : k < N) (ht : t.branch k ≠ .testRefinement)
    (hA : ∀ i ∈ Finset.Icc 1 q, ‖coefficients O t k i‖ ≤ M)
    (hdec : D ≤ ExplicitTrustRegion.prediction O t k (t.order k) (t.step k)) :
    D / (2 * M) ≤ ‖t.step k‖ := by
  simpa only [min_eq_right hD1] using h.step_norm_lower_min hM hk ht hA hdec

/-- A positive step floor prevents the forced candidate-step refinement at a fixed request
threshold. -/
theorem LegalPrefix.step_accurate_of_requests (h : LegalPrefix p a epsilon minimumTolerance O t N)
    {b : ℝ} (hb : 0 ≤ b) (hb1 : b ≤ 1)
    {k : ℕ} (hk : k < N) (ht : t.branch k ≠ .testRefinement)
    (hs : b ≤ ‖t.step k‖)
    (hh : ∀ i ∈ Finset.Icc 1 q, t.request k i ≤ a.stepConstant * b ^ q) :
    t.branch k = .trial := by
  apply (h.step_branch k hk ht).mpr
  intro i hi
  have hexp : q - i + 1 ≤ q := by have := Finset.mem_Icc.mp hi; omega
  exact (hh i hi).trans (mul_le_mul_of_nonneg_left
    ((pow_le_pow_of_le_one hb hb1 hexp).trans (pow_le_pow_left₀ hb hs _))
      a.stepConstant_pos.le)

/-- Separate scalar lower bounds for the scaled gap and radius yield a sharper decrement. -/
theorem LegalPrefix.predicted_lower_two (h : LegalPrefix p a epsilon minimumTolerance O t N)
    {b α : ℝ} (hb : 0 ≤ b) (hb1 : b ≤ 1) (hα : 0 ≤ α)
    {k : ℕ} (hk : k < N) (ht : t.branch k ≠ .testRefinement)
    (hr : b ≤ ExplicitTrustRegion.testRadius p t k)
    (hg : α ≤ ExplicitTrustRegion.scaledGap p O t k) :
    α * b ^ q / (q ! : ℝ) ≤
      ExplicitTrustRegion.prediction O t k (t.order k) (t.step k) := by
  have hp : b ^ q ≤ ExplicitTrustRegion.testRadius p t k ^ t.order k :=
    (pow_le_pow_of_le_one hb hb1 (h.order_le k hk ht)).trans (pow_le_pow_left₀ hb hr _)
  have hm := mul_le_mul hg hp (pow_nonneg hb _) (hα.trans hg)
  have hfac : ((t.order k)! : ℝ) ≤ (q ! : ℝ) :=
    Nat.cast_le.mpr (Nat.factorial_le (h.order_le k hk ht))
  exact ((div_le_div_of_nonneg_right hm (by positivity)).trans
    (div_le_div_of_nonneg_left (mul_nonneg (hα.trans hg)
      (pow_nonneg (h.testRadius_bounds (by omega)).1.le _)) (by positivity) hfac)).trans
        (h.predicted_ge_scaledGap hk ht)

end Optimization.ExplicitTrustRegion
