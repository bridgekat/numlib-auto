import Numlib.Optimization.UniversalRegularization

/-!
# Sufficient success for universal real-power regularization

Sharp Hölder Taylor remainders control the actual ratio and both active length tests.
The sufficient parameter depends on the computed step and uses no positive parameter floor.
-/

noncomputable section
namespace Optimization.UniversalRegularization
open RegularizedTaylorModel

/-- Transfer a coefficient bound between two real-power scales at a positive argument. -/
theorem scaled_rpow_le {A F K sigma t r j u : ℝ} (hu : 0 < u) (hF : 0 < F)
    (hcoef : A * F ≤ K) (hscale : K * u ^ (t - r) ≤ sigma) :
    A * u ^ (t - j) ≤ sigma / F * u ^ (r - j) := by
  have he : u ^ (t - j) = u ^ (t - r) * u ^ (r - j) := by
    rw [← Real.rpow_add hu]
    congr 1
    ring
  rw [he]
  have hc : A ≤ K / F := (le_div_iff₀ hF).mpr hcoef
  have hs : K / F * u ^ (t - r) ≤ sigma / F := by
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right hscale hF.le
  calc
    _ ≤ (K / F) * (u ^ (t - r) * u ^ (r - j)) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = (K / F * u ^ (t - r)) * u ^ (r - j) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hs (by positivity)

/-- A common Hölder coefficient for the ratio and active length tests. -/
def successCoefficient (H t r eta : ℝ) : ℝ :=
  Real.powerFactorial r * H / (Real.powerFactorial (t - 1) * (1 - eta))

/-- The common success coefficient is nonnegative for nonnegative Hölder constants. -/
theorem successCoefficient_nonneg {H t r eta : ℝ} (hH : 0 ≤ H) (ht : 1 ≤ t)
    (hr : 0 ≤ r) (heta : eta < 1) : 0 ≤ successCoefficient H t r eta := by
  exact div_nonneg (mul_nonneg (Real.powerFactorial_pos hr).le hH)
    (mul_nonneg (Real.powerFactorial_pos (by linarith : 0 ≤ t - 1)).le
      (sub_pos.mpr heta).le)

/-- The value remainder coefficient is dominated by the common success coefficient. -/
theorem successCoefficient_value {H t r eta : ℝ} (hH : 0 ≤ H) (ht : 1 ≤ t)
    (hr : 0 ≤ r) (heta : eta < 1) :
    H / Real.powerFactorial t * (Real.powerFactorial r / (1 - eta)) ≤
      successCoefficient H t r eta := by
  have hF := Real.powerFactorial_pos (r := t - 1) (by linarith)
  have hR := Real.powerFactorial_pos hr
  have he := sub_pos.mpr heta
  rw [Real.powerFactorial_sub_one ht, successCoefficient]
  rw [div_mul_div_comm]
  apply (div_le_div_iff₀ (mul_pos (mul_pos (by linarith : 0 < t) hF) he)
    (mul_pos hF he)).mpr
  nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hR.le hH) hF.le)
    (mul_nonneg he.le (sub_nonneg.mpr ht))]

/-- The first-derivative coefficient is dominated by the common success coefficient. -/
theorem successCoefficient_first {H t r eta : ℝ} (hH : 0 ≤ H) (ht : 1 ≤ t)
    (hr : 1 ≤ r) (heta0 : 0 ≤ eta) (heta : eta < 1) :
    H / Real.powerFactorial (t - 1) * Real.powerFactorial (r - 1) ≤
      successCoefficient H t r eta := by
  have hF := Real.powerFactorial_pos (r := t - 1) (by linarith)
  have hR := Real.powerFactorial_pos (r := r - 1) (by linarith)
  have he := sub_pos.mpr heta
  rw [successCoefficient, Real.powerFactorial_sub_one hr]
  apply (le_div_iff₀ (mul_pos hF he)).mpr
  field_simp
  nlinarith [mul_nonneg (mul_nonneg hR.le hH) (by linarith : 0 ≤ r - (1 - eta))]

/-- The second-derivative coefficient is dominated by the same common coefficient. -/
theorem successCoefficient_second {H t r eta : ℝ} (hH : 0 ≤ H) (ht : 2 ≤ t)
    (htr : t ≤ r) (heta0 : 0 ≤ eta) (heta : eta < 1) :
    H / Real.powerFactorial (t - 2) * Real.powerFactorial (r - 2) ≤
      successCoefficient H t r eta := by
  have hF := Real.powerFactorial_pos (r := t - 2) (by linarith)
  have hR := Real.powerFactorial_pos (r := r - 2) (by linarith)
  have he := sub_pos.mpr heta
  have htf : Real.powerFactorial (t - 1) = (t - 1) * Real.powerFactorial (t - 2) := by
    simpa only [show t - 1 - 1 = t - 2 by ring] using
      Real.powerFactorial_sub_one (r := t - 1) (by linarith)
  have hrf : Real.powerFactorial r = r * ((r - 1) * Real.powerFactorial (r - 2)) := by
    rw [Real.powerFactorial_sub_one (by linarith : 1 ≤ r)]
    congr 1
    simpa only [show r - 1 - 1 = r - 2 by ring] using
      Real.powerFactorial_sub_one (r := r - 1) (by linarith)
  rw [successCoefficient, htf, hrf]
  apply (le_div_iff₀ (mul_pos (mul_pos (by linarith : 0 < t - 1) hF) he)).mpr
  field_simp
  have hgap : (t - 1) * (1 - eta) ≤ r * (r - 1) := by
    have h1 : (t - 1) * (1 - eta) ≤ t - 1 := by nlinarith
    have h2 : t - 1 ≤ r * (r - 1) := by nlinarith
    exact h1.trans h2
  nlinarith [mul_nonneg (mul_nonneg hR.le hH) (sub_nonneg.mpr hgap)]

/-- The tolerance coefficient obtained by eliminating a positive derivative scale. -/
def toleranceCoefficient (K F t r j : ℝ) : ℝ :=
  (F / 3) ^ ((t - r) / (t - j)) * K ^ ((r - j) / (t - j))

/-- The tolerance coefficient is exactly the scaled inverse-derivative power. -/
theorem toleranceCoefficient_mul_rpow {K F t r j epsilon : ℝ} (hK : 0 < K)
    (hF : 0 < F) (hepsilon : 0 < epsilon) (htj : j < t) :
    toleranceCoefficient K F t r j * epsilon ^ ((t - r) / (t - j)) =
      K * (epsilon * F / (3 * K)) ^ ((t - r) / (t - j)) := by
  have he : (r - j) / (t - j) = 1 - (t - r) / (t - j) := by
    field_simp [(sub_pos.mpr htj).ne']
    ring
  rw [toleranceCoefficient, he, Real.rpow_sub hK, Real.rpow_one]
  rw [show epsilon * F / (3 * K) = epsilon * (F / 3) / K by ring,
    Real.div_rpow (mul_nonneg hepsilon.le (by positivity)) hK.le,
    Real.mul_rpow hepsilon.le (by positivity)]
  ring

/-- A nonzero criticality residual removes the unknown step from a sufficient threshold.
The exponent may vanish when the smoothness and regularization powers agree. -/
theorem threshold_of_tolerance {A F K sigma theta t r j u epsilon measure : ℝ}
    (hu : 0 < u) (hF : 0 < F) (hK : 0 ≤ K) (hsigma : 0 < sigma)
    (hepsilon : 0 < epsilon) (htj : j < t) (htr : t ≤ r)
    (hcoef : A * F ≤ K) (htheta : theta * F ≤ sigma)
    (hmeasure : epsilon < measure)
    (hbound : measure ≤ A * u ^ (t - j) + (sigma / F + theta) * u ^ (r - j))
    (hlarge : toleranceCoefficient K F t r j * epsilon ^ ((t - r) / (t - j)) ≤ sigma) :
    K * u ^ (t - r) ≤ sigma := by
  by_contra hnot
  have hbad : sigma < K * u ^ (t - r) := lt_of_not_ge hnot
  have hKpos : 0 < K := by
    by_contra hn
    have hzero : K = 0 := le_antisymm (le_of_not_gt hn) hK
    simp only [hzero, zero_mul] at hbad
    exact (hsigma.trans hbad).false
  have hA : A ≤ K / F := (le_div_iff₀ hF).mpr hcoef
  have hth : theta ≤ sigma / F := (le_div_iff₀ hF).mpr htheta
  have heq : u ^ (t - r) * u ^ (r - j) = u ^ (t - j) := by
    rw [← Real.rpow_add hu]
    congr 1
    ring
  have hsmall : sigma / F * u ^ (r - j) < K / F * u ^ (t - j) := by
    have hh := mul_lt_mul_of_pos_right hbad
      (div_pos (Real.rpow_pos_of_pos hu (r - j)) hF)
    calc
      _ = sigma * (u ^ (r - j) / F) := by ring
      _ < K * u ^ (t - r) * (u ^ (r - j) / F) := hh
      _ = K / F * (u ^ (t - r) * u ^ (r - j)) := by ring
      _ = _ := by rw [heq]
  have hcrit : epsilon < 3 * K / F * u ^ (t - j) := by
    have hA' := mul_le_mul_of_nonneg_right hA (Real.rpow_nonneg hu.le (t - j))
    have hth' := mul_le_mul_of_nonneg_right hth (Real.rpow_nonneg hu.le (r - j))
    have hh : measure < 3 * K / F * u ^ (t - j) := by
      linear_combination hbound + hA' + hth' + 2 * hsmall
    exact hmeasure.trans hh
  have hbase : epsilon * F / (3 * K) < u ^ (t - j) := by
    apply (div_lt_iff₀ (by positivity : 0 < 3 * K)).mpr
    have hh := (lt_div_iff₀ hF).mp (show epsilon < (3 * K * u ^ (t - j)) / F by
      simpa only [div_mul_eq_mul_div] using hcrit)
    nlinarith only [hh]
  have hroot : (epsilon * F / (3 * K)) ^ (t - j)⁻¹ < u :=
    (Real.rpow_inv_lt_iff_of_pos (by positivity) hu.le (sub_pos.mpr htj)).mpr hbase
  have hpow : u ^ (t - r) ≤
      ((epsilon * F / (3 * K)) ^ (t - j)⁻¹) ^ (t - r) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hroot.le (sub_nonpos.mpr htr)
  have hfinal : K * u ^ (t - r) ≤
      toleranceCoefficient K F t r j * epsilon ^ ((t - r) / (t - j)) := by
    rw [toleranceCoefficient_mul_rpow hKpos hF hepsilon htj,
      ← Real.rpow_mul (by positivity : 0 ≤ epsilon * F / (3 * K))] at *
    simpa only [div_eq_mul_inv, mul_comm (t - r)] using
      mul_le_mul_of_nonneg_left hpow hK
  exact (hbad.trans_le (hfinal.trans hlarge)).false

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
variable {q p : ℕ} {r sigma H beta : ℝ} {a : Parameters q p r}
  {f : E → ℝ} {x s : E}

omit [FiniteDimensional ℝ E] [Nontrivial E] in
/-- The actual ratio exceeds its very-successful threshold when the Taylor value error
is paid by the corresponding fraction of the regularization term. -/
theorem ComputedStep.ratio_ge_of_error (hs : ComputedStep a f x sigma s)
    (hsigma : 0 < sigma)
    (herr : |f (x + s) - taylorModel f p x s| ≤
      (1 - a.eta2) * (sigma / Real.powerFactorial r * ‖s‖ ^ r)) :
    a.eta2 ≤ ratio f p x s := by
  have hden := hs.predicted_positive hsigma
  have hpaid := mul_le_mul_of_nonneg_left hs.predicted_decrease
    (sub_pos.mpr a.eta2_lt_one).le
  have he := (abs_le.mp herr).2
  rw [ratio, le_div_iff₀ hden]
  rw [RegularizedTaylorModel.taylorModel_zero] at hpaid ⊢
  nlinarith

/-- Every activated length test follows from a three-term derivative bound at the
regularizer scale. Negative curvature is allowed to have either sign. -/
theorem length_test_of_bound {alpha F measure sigma u : ℝ} (hF : 0 < F)
    (halpha : 0 < alpha) (hsmall : alpha ≤ F / 3) (hsigma : 0 ≤ sigma)
    (hu : 0 ≤ u) (hbound : measure ≤ 3 * sigma / F * u) :
    alpha * measure ≤ sigma * u := by
  have hcoef : alpha * (3 * sigma / F * u) ≤ sigma * u := by
    have hmul := mul_le_mul_of_nonneg_right hsmall (by positivity : 0 ≤ 3 * sigma / F * u)
    have he : F / 3 * (3 * sigma / F * u) = sigma * u := by field_simp
    exact he ▸ hmul
  exact (mul_le_mul_of_nonneg_left hbound halpha.le).trans hcoef

/-- A computed real-power step is very successful once its parameter exceeds the common
Hölder step threshold and the active model-residual coefficients. This applies for every
nonnegative Hölder exponent, including equality of regularization and smoothness. -/
theorem ComputedStep.verySuccessful_of_threshold (hf : HolderDerivative f p H beta)
    (htr : (p : ℝ) + beta ≤ r)
    (hsigma : 0 < sigma) (hs : ComputedStep a f x sigma s)
    (htheta1 : a.theta 0 * Real.powerFactorial (r - 1) ≤ sigma)
    (htheta2 : 2 ≤ q → a.theta 1 * Real.powerFactorial (r - 2) ≤ sigma)
    (hlarge : successCoefficient H ((p : ℝ) + beta) r a.eta2 *
      ‖s‖ ^ ((p : ℝ) + beta - r) ≤ sigma) : VerySuccessful a f x sigma s := by
  have hp : 1 ≤ p := a.order_pos.trans a.degree_ge_order
  have ht : 1 ≤ (p : ℝ) + beta := by
    have hpr : (1 : ℝ) ≤ p := by exact_mod_cast hp
    linarith [hf.exponent_nonneg]
  have hr : 1 < r := by
    have hpr : (1 : ℝ) ≤ p := by exact_mod_cast hp
    linarith [a.power_gt_degree]
  have hn : 0 < ‖s‖ := norm_pos_iff.mpr hs.step_ne_zero
  have he : 0 < 1 - a.eta2 := sub_pos.mpr a.eta2_lt_one
  have heta : 0 ≤ a.eta2 := a.eta1_pos.le.trans a.eta1_le_eta2
  have hF := Real.powerFactorial_pos (r := r) (by linarith)
  have hF1 := Real.powerFactorial_pos (r := r - 1) (by linarith)
  have hv := scaled_rpow_le (j := 0) hn (div_pos hF he)
    (successCoefficient_value hf.constant_nonneg ht (by linarith) a.eta2_lt_one) hlarge
  simp only [sub_zero] at hv
  have hval : |f (x + s) - taylorModel f p x s| ≤
      (1 - a.eta2) * (sigma / Real.powerFactorial r * ‖s‖ ^ r) := by
    have hh := hf.norm_sub_taylorModel_le hp x s
    rw [Real.norm_eq_abs] at hh
    apply hh.trans
    convert hv using 1
    field_simp
  refine ⟨hs.ratio_ge_of_error hsigma hval, ?_, ?_⟩
  · have hfirst := hf.trial_fderiv_bound hp hr hsigma.le x s hs.first
    have hs1 := scaled_rpow_le (j := 1) hn hF1
      (successCoefficient_first hf.constant_nonneg ht hr.le heta a.eta2_lt_one) hlarge
    have hth1 : a.theta 0 ≤ sigma / Real.powerFactorial (r - 1) :=
      (le_div_iff₀ hF1).mpr htheta1
    have hbound : ‖fderiv ℝ f (x + s)‖ ≤
        3 * sigma / Real.powerFactorial (r - 1) * ‖s‖ ^ (r - 1) := by
      have hm := mul_le_mul_of_nonneg_right hth1 (Real.rpow_nonneg (norm_nonneg s) (r - 1))
      linear_combination hfirst + hs1 + hm
    apply length_test_of_bound hF1 (a.alpha_pos 0) _ hsigma.le
      (Real.rpow_nonneg (norm_nonneg s) _) hbound
    have hh := a.alpha_le 0
    norm_num only [Fin.val_zero, Nat.cast_zero, zero_add] at hh
    exact hh.trans (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num))
  · intro hq
    have hp2 : 2 ≤ p := hq.trans a.degree_ge_order
    have ht2 : 2 ≤ (p : ℝ) + beta := by
      have hpr : (2 : ℝ) ≤ p := by exact_mod_cast hp2
      linarith [hf.exponent_nonneg]
    have hr2 : 2 < r := by
      have hpr : (2 : ℝ) ≤ p := by exact_mod_cast hp2
      linarith [a.power_gt_degree]
    have hF2 := Real.powerFactorial_pos (r := r - 2) (by linarith)
    have hcurv := (le_leastCurvature_iff _ _).mpr (fun u =>
      hf.trial_curvature_bound hp2 hr2 hsigma.le x s u
        ((le_leastCurvature_iff _ _).mp (hs.second hq) u))
    have hs2 := scaled_rpow_le (j := 2) hn hF2
      (successCoefficient_second hf.constant_nonneg ht2 htr heta a.eta2_lt_one) hlarge
    have hth2 : a.theta 1 ≤ sigma / Real.powerFactorial (r - 2) :=
      (le_div_iff₀ hF2).mpr (htheta2 hq)
    have hbound : -leastCurvature (fderiv ℝ (fderiv ℝ f) (x + s)) ≤
        3 * sigma / Real.powerFactorial (r - 2) * ‖s‖ ^ (r - 2) := by
      have hm := mul_le_mul_of_nonneg_right hth2 (Real.rpow_nonneg (norm_nonneg s) (r - 2))
      linear_combination hcurv + hs2 + hm
    have halpha := a.alpha_le 1
    norm_num only [Fin.val_one, Nat.cast_one, one_add_one_eq_two] at halpha
    have hh := length_test_of_bound hF2 (a.alpha_pos 1)
      (halpha.trans (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)))
      hsigma.le (Real.rpow_nonneg (norm_nonneg s) _) hbound
    simpa only [mul_neg, neg_mul] using hh

/-- At a nonterminal actual trial, the tolerance thresholds imply the step-dependent
threshold, simultaneously for both active orders. -/
theorem ComputedStep.threshold_of_nonstationary (hf : HolderDerivative f p H beta)
    (hexp : (q : ℝ) < (p : ℝ) + beta) (htr : (p : ℝ) + beta ≤ r)
    (hsigma : 0 < sigma) (hs : ComputedStep a f x sigma s)
    (hnonterminal : ¬Stationary a f (x + s))
    (htheta1 : a.theta 0 * Real.powerFactorial (r - 1) ≤ sigma)
    (htheta2 : 2 ≤ q → a.theta 1 * Real.powerFactorial (r - 2) ≤ sigma)
    (htolerance1 : toleranceCoefficient (successCoefficient H ((p : ℝ) + beta) r a.eta2)
      (Real.powerFactorial (r - 1)) ((p : ℝ) + beta) r 1 *
        a.epsilon 0 ^ (((p : ℝ) + beta - r) / ((p : ℝ) + beta - 1)) ≤ sigma)
    (htolerance2 : 2 ≤ q →
      toleranceCoefficient (successCoefficient H ((p : ℝ) + beta) r a.eta2)
        (Real.powerFactorial (r - 2)) ((p : ℝ) + beta) r 2 *
          a.epsilon 1 ^ (((p : ℝ) + beta - r) / ((p : ℝ) + beta - 2)) ≤ sigma) :
    successCoefficient H ((p : ℝ) + beta) r a.eta2 *
      ‖s‖ ^ ((p : ℝ) + beta - r) ≤ sigma := by
  have hp : 1 ≤ p := a.order_pos.trans a.degree_ge_order
  have hqr : (1 : ℝ) ≤ q := by exact_mod_cast a.order_pos
  have ht : 1 < (p : ℝ) + beta := by linarith
  have hr : 1 < r := lt_of_lt_of_le ht htr
  have heta : 0 ≤ a.eta2 := a.eta1_pos.le.trans a.eta1_le_eta2
  have hK := successCoefficient_nonneg (r := r) hf.constant_nonneg ht.le (by linarith) a.eta2_lt_one
  have hn : 0 < ‖s‖ := norm_pos_iff.mpr hs.step_ne_zero
  by_cases hfirst : a.epsilon 0 < ‖fderiv ℝ f (x + s)‖
  · exact threshold_of_tolerance hn (Real.powerFactorial_pos (by linarith : 0 ≤ r - 1)) hK
      hsigma (a.epsilon_pos 0 (by have := a.order_pos; simp only [Fin.val_zero]; omega)) ht htr
      (successCoefficient_first hf.constant_nonneg ht.le hr.le heta a.eta2_lt_one)
      htheta1 hfirst (hf.trial_fderiv_bound hp hr hsigma.le x s hs.first) htolerance1
  · have hsecond : 2 ≤ q ∧
        a.epsilon 1 < -leastCurvature (fderiv ℝ (fderiv ℝ f) (x + s)) := by
      have hh : ¬(2 ≤ q → -a.epsilon 1 ≤
          leastCurvature (fderiv ℝ (fderiv ℝ f) (x + s))) := by
        intro hh
        exact hnonterminal ⟨le_of_not_gt hfirst, hh⟩
      push Not at hh
      exact ⟨hh.1, by linarith [hh.2]⟩
    have hp2 : 2 ≤ p := hsecond.1.trans a.degree_ge_order
    have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hsecond.1
    have ht2 : 2 < (p : ℝ) + beta := by linarith
    have hr2 : 2 < r := ht2.trans_le htr
    have hcurv := (le_leastCurvature_iff _ _).mpr (fun u =>
      hf.trial_curvature_bound hp2 hr2 hsigma.le x s u
        ((le_leastCurvature_iff _ _).mp (hs.second hsecond.1) u))
    apply threshold_of_tolerance hn (Real.powerFactorial_pos (by linarith : 0 ≤ r - 2)) hK
      hsigma (a.epsilon_pos 1 (by have := hsecond.1; simp only [Fin.val_one]; omega)) ht2 htr
      (successCoefficient_second hf.constant_nonneg ht2.le htr heta a.eta2_lt_one)
      (htheta2 hsecond.1) hsecond.2 _ (htolerance2 hsecond.1)
    linarith only [hcurv]

/-- A computable sufficient parameter formed from the active residual and tolerance terms. -/
def successThreshold (a : Parameters q p r) (H t : ℝ) : ℝ :=
  max (max (a.theta 0 * Real.powerFactorial (r - 1))
    (toleranceCoefficient (successCoefficient H t r a.eta2)
      (Real.powerFactorial (r - 1)) t r 1 * a.epsilon 0 ^ ((t - r) / (t - 1))))
    (if 2 ≤ q then max (a.theta 1 * Real.powerFactorial (r - 2))
      (toleranceCoefficient (successCoefficient H t r a.eta2)
        (Real.powerFactorial (r - 2)) t r 2 * a.epsilon 1 ^ ((t - r) / (t - 2)))
    else a.theta 0 * Real.powerFactorial (r - 1))

/-- The threshold inequality is exactly the active residual and tolerance inequalities. -/
theorem successThreshold_le_iff {t : ℝ} : successThreshold a H t ≤ sigma ↔
    a.theta 0 * Real.powerFactorial (r - 1) ≤ sigma ∧
    toleranceCoefficient (successCoefficient H t r a.eta2)
      (Real.powerFactorial (r - 1)) t r 1 * a.epsilon 0 ^ ((t - r) / (t - 1)) ≤ sigma ∧
    (2 ≤ q → a.theta 1 * Real.powerFactorial (r - 2) ≤ sigma ∧
      toleranceCoefficient (successCoefficient H t r a.eta2)
        (Real.powerFactorial (r - 2)) t r 2 * a.epsilon 1 ^ ((t - r) / (t - 2)) ≤ sigma) := by
  classical
  by_cases hq : 2 ≤ q <;> simp [successThreshold, hq, and_assoc]

/-- Above the explicit tolerance threshold, every nonterminal actual trial is very successful. -/
theorem ComputedStep.verySuccessful_of_successThreshold (hf : HolderDerivative f p H beta)
    (hexp : (q : ℝ) < (p : ℝ) + beta) (htr : (p : ℝ) + beta ≤ r)
    (hsigma : 0 < sigma) (hs : ComputedStep a f x sigma s)
    (hnonterminal : ¬Stationary a f (x + s))
    (hlarge : successThreshold a H ((p : ℝ) + beta) ≤ sigma) :
    VerySuccessful a f x sigma s := by
  obtain ⟨ht1, hc1, ht2⟩ := successThreshold_le_iff.mp hlarge
  exact hs.verySuccessful_of_threshold hf htr hsigma ht1 (fun hq => (ht2 hq).1)
    (hs.threshold_of_nonstationary hf hexp htr hsigma hnonterminal ht1
      (fun hq => (ht2 hq).1) hc1 (fun hq => (ht2 hq).2))

omit [FiniteDimensional ℝ E] [Nontrivial E] in
/-- Every legal branch has the same multiplicative upper bound. -/
theorem LegalUpdate.le_mul_gamma3 {next : ℝ} (h : LegalUpdate a f x s sigma next)
    (hsigma : 0 ≤ sigma) : next ≤ a.gamma3 * sigma := by
  have hgamma : 1 < a.gamma3 := a.gamma2_gt_one.trans a.gamma2_lt_gamma3
  by_cases hv : VerySuccessful a f x sigma s
  · exact (h.1 hv).2.trans (by nlinarith)
  · by_cases ha : Accepted a f x sigma s
    · exact (h.2.1 ha hv).2.trans
        (mul_le_mul_of_nonneg_right a.gamma2_lt_gamma3.le hsigma)
    · exact (h.2.2 ha).2

/-- Actual legal updates cannot cross the tolerance success threshold by more than the
maximum increase factor. No lower parameter bound besides positivity is required. -/
theorem RunPrefix.sigma_upper {x s : ℕ → E} {sigma : ℕ → ℝ} {N k : ℕ}
    (h : RunPrefix a f x s sigma N) (hf : HolderDerivative f p H beta)
    (hexp : (q : ℝ) < (p : ℝ) + beta) (htr : (p : ℝ) + beta ≤ r) (hk : k ≤ N) :
    sigma k ≤ max (sigma 0) (a.gamma3 * successThreshold a H ((p : ℝ) + beta)) := by
  induction k with
  | zero => exact le_max_left _ _
  | succ k ih =>
    have hkN : k < N := by omega
    have hpos := h.positive (k := k) (by omega)
    by_cases hlarge : successThreshold a H ((p : ℝ) + beta) ≤ sigma k
    · have hn : ¬Stationary a f (x k + s k) := by
        simpa only [observation_succ] using h.nonterminal (k + 1) hk
      have hv := (h.computed k hkN).verySuccessful_of_successThreshold hf hexp htr hpos hn hlarge
      exact ((h.update k hkN).1 hv).2.trans (ih (by omega))
    · have hg : 0 ≤ a.gamma3 := by linarith [a.gamma2_gt_one, a.gamma2_lt_gamma3]
      exact ((h.update k hkN).le_mul_gamma3 hpos.le).trans
        ((mul_le_mul_of_nonneg_left (le_of_not_ge hlarge) hg).trans (le_max_right _ _))

/-- A tolerance-independent threshold containing both derivative orders. -/
def uniformSuccessThreshold (a : Parameters q p r) (H t : ℝ) : ℝ :=
  max (max (a.theta 0 * Real.powerFactorial (r - 1))
    (toleranceCoefficient (successCoefficient H t r a.eta2)
      (Real.powerFactorial (r - 1)) t r 1))
    (max (a.theta 1 * Real.powerFactorial (r - 2))
      (toleranceCoefficient (successCoefficient H t r a.eta2)
        (Real.powerFactorial (r - 2)) t r 2))

/-- The tolerance-independent upper-parameter constant for two activated orders. -/
def uniformSigma (a : Parameters q p r) (H t initial : ℝ) : ℝ :=
  max initial (a.gamma3 * uniformSuccessThreshold a H t)

/-- A positive initial parameter makes the uniform upper-parameter constant positive. -/
theorem uniformSigma_pos {t initial : ℝ} (hinitial : 0 < initial) :
    0 < uniformSigma a H t initial := hinitial.trans_le (le_max_left _ _)

/-- The two-order parameter bound factors into a uniform constant and the maximum of
the two nonpositive tolerance powers. -/
theorem RunPrefix.sigma_upper_uniform {x s : ℕ → E} {sigma : ℕ → ℝ} {N k : ℕ}
    (h : RunPrefix a f x s sigma N) (hf : HolderDerivative f p H beta)
    (hexp : (q : ℝ) < (p : ℝ) + beta) (htr : (p : ℝ) + beta ≤ r)
    (hq : 2 ≤ q) (hk : k ≤ N) :
    sigma k ≤ uniformSigma a H ((p : ℝ) + beta) (sigma 0) *
      max (a.epsilon 0 ^ (((p : ℝ) + beta - r) / ((p : ℝ) + beta - 1)))
        (a.epsilon 1 ^ (((p : ℝ) + beta - r) / ((p : ℝ) + beta - 2))) := by
  let t := (p : ℝ) + beta
  let e := a.epsilon 0 ^ ((t - r) / (t - 1))
  let g := a.epsilon 1 ^ ((t - r) / (t - 2))
  let C := uniformSuccessThreshold a H t
  let M := uniformSigma a H t (sigma 0)
  have hqr : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have ht : 2 < t := by dsimp [t]; linarith
  have hr : 2 < r := ht.trans_le htr
  have he0 := a.epsilon_pos 0 (by have := a.order_pos; simp only [Fin.val_zero]; omega)
  have he1 := a.epsilon_pos 1 (by simp only [Fin.val_one]; omega)
  have he : 1 ≤ e := Real.one_le_rpow_of_pos_of_le_one_of_nonpos he0
    (a.epsilon_le_one 0 (by have := a.order_pos; simp only [Fin.val_zero]; omega))
    (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr htr) (by linarith))
  have hg : 1 ≤ g := Real.one_le_rpow_of_pos_of_le_one_of_nonpos he1
    (a.epsilon_le_one 1 (by simp only [Fin.val_one]; omega))
    (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr htr) (by linarith))
  have hE : 1 ≤ max e g := he.trans (le_max_left _ _)
  have htheta0 : a.theta 0 * Real.powerFactorial (r - 1) ≤ C :=
    (le_max_left _ _).trans (le_max_left _ _)
  have htheta1 : a.theta 1 * Real.powerFactorial (r - 2) ≤ C :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hcoef0 : toleranceCoefficient (successCoefficient H t r a.eta2)
      (Real.powerFactorial (r - 1)) t r 1 ≤ C :=
    (le_max_right _ _).trans (le_max_left _ _)
  have hcoef1 : toleranceCoefficient (successCoefficient H t r a.eta2)
      (Real.powerFactorial (r - 2)) t r 2 ≤ C :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hC : 0 ≤ C := (mul_pos (a.theta_pos 0)
    (Real.powerFactorial_pos (by linarith : 0 ≤ r - 1))).le.trans htheta0
  have hCE : C ≤ C * max e g := le_mul_of_one_le_right hC hE
  have hthreshold : successThreshold a H t ≤ C * max e g := by
    apply successThreshold_le_iff.mpr
    refine ⟨htheta0.trans hCE, ?_, fun _ => ⟨htheta1.trans hCE, ?_⟩⟩
    · exact mul_le_mul hcoef0 (le_max_left _ _) (by linarith [he]) hC
    · exact mul_le_mul hcoef1 (le_max_right _ _) (by linarith [hg]) hC
  have hgamma : 0 ≤ a.gamma3 := by linarith [a.gamma2_gt_one, a.gamma2_lt_gamma3]
  have hM : 0 ≤ M := h.initial_positive.le.trans (le_max_left _ _)
  have hbase : sigma 0 ≤ M * max e g :=
    (le_max_left _ _).trans (le_mul_of_one_le_right hM hE)
  have hscaled : a.gamma3 * successThreshold a H t ≤ M * max e g := by
    calc
      _ ≤ a.gamma3 * (C * max e g) := mul_le_mul_of_nonneg_left hthreshold hgamma
      _ = (a.gamma3 * C) * max e g := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith)
  exact (h.sigma_upper hf hexp htr hk).trans (max_le hbase hscaled)

omit [FiniteDimensional ℝ E] [Nontrivial E] in
/-- Every accepted computed trial decreases the actual objective by its accepted fraction
of the complete real-power regularization payment. -/
theorem ComputedStep.objective_decrease (hs : ComputedStep a f x sigma s)
    (hsigma : 0 < sigma) (ha : Accepted a f x sigma s) :
    a.eta1 * (sigma / Real.powerFactorial r * ‖s‖ ^ r) ≤ f x - f (x + s) := by
  have hratio := (le_div_iff₀ (hs.predicted_positive hsigma)).mp ha.1
  have hpaid := mul_le_mul_of_nonneg_left hs.predicted_decrease a.eta1_pos.le
  rw [RegularizedTaylorModel.taylorModel_zero] at hpaid hratio
  exact hpaid.trans hratio

omit [FiniteDimensional ℝ E] [Nontrivial E] in
/-- Rejected iterates stay fixed and accepted iterates strictly pay a nonnegative
regularization decrease, so every processed objective sequence is nonincreasing. -/
theorem RunPrefix.objective_nonincrease {x s : ℕ → E} {sigma : ℕ → ℝ} {N k : ℕ}
    (h : RunPrefix a f x s sigma N) (hk : k < N) : f (x (k + 1)) ≤ f (x k) := by
  have hpos := h.positive (k := k) (by omega)
  have hr : 0 ≤ r := by
    have hp : (0 : ℝ) < p := by exact_mod_cast a.order_pos.trans a.degree_ge_order
    linarith [a.power_gt_degree]
  rw [h.iterate k hk]
  split_ifs with ha
  · have hd := (h.computed k hk).objective_decrease hpos ha
    have hn : 0 ≤ a.eta1 * (sigma k / Real.powerFactorial r * ‖s k‖ ^ r) :=
      mul_nonneg a.eta1_pos.le (mul_nonneg
        (div_nonneg hpos.le (Real.powerFactorial_pos hr).le) (Real.rpow_nonneg (norm_nonneg _) _))
    linarith
  · exact le_rfl

end Optimization.UniversalRegularization
