import Numlib.Optimization.UniversalRegularizationBounds

/-!
# Uniform decrease for universal real-power regularization

A common tolerance radius eliminates the mixed powers in the parameter upper bound.
The resulting payment estimate applies to every positive derivative exponent.
-/

noncomputable section
namespace Optimization.UniversalRegularization

/-- The radial payment coefficient, with derivative order `j`. -/
def paymentCoefficient (alpha M r j : ℝ) : ℝ :=
  (alpha ^ r / M ^ j) ^ (r - j)⁻¹

/-- The payment coefficient is positive for positive length and parameter constants. -/
theorem paymentCoefficient_pos {alpha M r j : ℝ} (ha : 0 < alpha) (hM : 0 < M) :
    0 < paymentCoefficient alpha M r j := by
  unfold paymentCoefficient
  positivity

/-- A length bound and a parameter bound at a common radius give a complete radial payment.
Only positivity of `r-j` and nonnegativity of the derivative order are used. -/
theorem radial_payment_lower {alpha M r j t z sigma u : ℝ}
    (ha : 0 < alpha) (hM : 0 < M) (hz : 0 < z) (hu : 0 < u)
    (hj : 0 ≤ j) (hrj : j < r)
    (hupper : sigma ≤ M * z ^ (t - r))
    (hlength : alpha * z ^ (t - j) ≤ sigma * u ^ (r - j)) :
    paymentCoefficient alpha M r j * z ^ t ≤ sigma * u ^ r := by
  have hscaled : alpha / M * z ^ (r - j) ≤ u ^ (r - j) := by
    have hh := hlength.trans (mul_le_mul_of_nonneg_right hupper (by positivity))
    have he : z ^ (t - j) = z ^ (t - r) * z ^ (r - j) := by
      rw [← Real.rpow_add hz]
      congr 1
      ring
    rw [he] at hh
    have hh' : z ^ (t - r) * (alpha * z ^ (r - j)) ≤
        z ^ (t - r) * (M * u ^ (r - j)) := by nlinarith only [hh]
    have hc := (mul_le_mul_iff_right₀ (Real.rpow_pos_of_pos hz (t - r))).mp hh'
    rw [div_mul_eq_mul_div]
    exact (div_le_iff₀ hM).mpr (by nlinarith only [hc])
  have hroot : (alpha / M) ^ (r - j)⁻¹ * z ≤ u := by
    have hh := (Real.rpow_inv_le_iff_of_pos (by positivity :
      0 ≤ alpha / M * z ^ (r - j)) hu.le (sub_pos.mpr hrj)).mpr hscaled
    rw [Real.mul_rpow (by positivity) (by positivity), Real.rpow_rpow_inv hz.le
      (sub_ne_zero.mpr hrj.ne')] at hh
    exact hh
  have hjpower := Real.rpow_le_rpow (by positivity) hroot hj
  have hpay : alpha * z ^ (t - j) * u ^ j ≤ sigma * u ^ r := by
    have hh := mul_le_mul_of_nonneg_right hlength (Real.rpow_nonneg hu.le j)
    rw [mul_assoc sigma, ← Real.rpow_add hu,
      show r - j + j = r by ring] at hh
    exact hh
  have hlow := mul_le_mul_of_nonneg_left hjpower
    (show 0 ≤ alpha * z ^ (t - j) by positivity)
  have hcoef : alpha * (alpha / M) ^ (j / (r - j)) =
      paymentCoefficient alpha M r j := by
    rw [paymentCoefficient, Real.div_rpow (Real.rpow_nonneg ha.le _) (Real.rpow_nonneg hM.le _),
      ← Real.rpow_mul ha.le, ← Real.rpow_mul hM.le,
      Real.div_rpow ha.le hM.le]
    rw [← mul_div_assoc]
    congr 1
    conv_lhs => lhs; rw [← Real.rpow_one alpha]
    rw [← Real.rpow_add ha]
    congr 1
    field_simp [(sub_pos.mpr hrj).ne']
    ring
  rw [Real.mul_rpow (by positivity) hz.le, ← Real.rpow_mul (by positivity : 0 ≤ alpha / M),
    show (r - j)⁻¹ * j = j / (r - j) by ring] at hlow
  have he : alpha * z ^ (t - j) * ((alpha / M) ^ (j / (r - j)) * z ^ j) =
      paymentCoefficient alpha M r j * z ^ t := by
    calc
      _ = (alpha * (alpha / M) ^ (j / (r - j))) * (z ^ (t - j) * z ^ j) := by ring
      _ = _ := by rw [hcoef, ← Real.rpow_add hz, show t - j + j = t by ring]
  rw [he] at hlow
  exact hlow.trans hpay

variable {q p : ℕ} {r H : ℝ} {a : Parameters q p r}

/-- A radius common to the activated tolerance roots. -/
def toleranceRadius (a : Parameters q p r) (t : ℝ) : ℝ :=
  if 2 ≤ q then min (a.epsilon 0 ^ (t - 1)⁻¹) (a.epsilon 1 ^ (t - 2)⁻¹)
  else a.epsilon 0 ^ (t - 1)⁻¹

/-- The common tolerance radius is positive. -/
theorem toleranceRadius_pos {t : ℝ} : 0 < toleranceRadius a t := by
  have he := a.epsilon_pos 0 (by have := a.order_pos; simp only [Fin.val_zero]; omega)
  unfold toleranceRadius
  split_ifs with hq
  · have he' := a.epsilon_pos 1 (by simp only [Fin.val_one]; omega)
    exact lt_min (by positivity) (by positivity)
  · positivity

/-- The common radius is no larger than the first tolerance root. -/
theorem toleranceRadius_le_first {t : ℝ} :
    toleranceRadius a t ≤ a.epsilon 0 ^ (t - 1)⁻¹ := by
  unfold toleranceRadius
  split_ifs <;> simp only [min_le_left, le_refl]

/-- When curvature is active, the common radius is no larger than its tolerance root. -/
theorem toleranceRadius_le_second {t : ℝ} (hq : 2 ≤ q) :
    toleranceRadius a t ≤ a.epsilon 1 ^ (t - 2)⁻¹ := by
  rw [toleranceRadius, ite_eq_left hq]
  exact min_le_right _ _

/-- A common radius bounded by a tolerance root satisfies the corresponding tolerance bound. -/
theorem tolerance_power_of_root {epsilon z t j : ℝ} (he : 0 < epsilon)
    (hz : 0 ≤ z) (htj : j < t) (hroot : z ≤ epsilon ^ (t - j)⁻¹) :
    z ^ (t - j) ≤ epsilon := by
  have hh := Real.rpow_le_rpow hz hroot (sub_pos.mpr htj).le
  rwa [Real.rpow_inv_rpow he.le (sub_pos.mpr htj).ne'] at hh

/-- The tolerance-root identity also transfers negative smoothness exponents. -/
theorem tolerance_scale_of_root {epsilon z t r j : ℝ} (he : 0 < epsilon)
    (hz : 0 < z) (htr : t ≤ r)
    (hroot : z ≤ epsilon ^ (t - j)⁻¹) :
    epsilon ^ ((t - r) / (t - j)) ≤ z ^ (t - r) := by
  have hh := Real.rpow_le_rpow_of_nonpos hz hroot (sub_nonpos.mpr htr)
  rw [← Real.rpow_mul he.le] at hh
  convert hh using 1
  congr 1
  ring

/-- The common-radius power is the exact minimum of the activated complexity powers. -/
theorem toleranceRadius_power {t : ℝ} (ht : 0 ≤ t) :
    toleranceRadius a t ^ t = if 2 ≤ q then
      min (a.epsilon 0 ^ (t / (t - 1))) (a.epsilon 1 ^ (t / (t - 2)))
    else a.epsilon 0 ^ (t / (t - 1)) := by
  have he := a.epsilon_pos 0 (by have := a.order_pos; simp only [Fin.val_zero]; omega)
  unfold toleranceRadius
  split_ifs with hq
  · have he' := a.epsilon_pos 1 (by simp only [Fin.val_one]; omega)
    have hpow : (min (a.epsilon 0 ^ (t - 1)⁻¹) (a.epsilon 1 ^ (t - 2)⁻¹)) ^ t =
        min ((a.epsilon 0 ^ (t - 1)⁻¹) ^ t) ((a.epsilon 1 ^ (t - 2)⁻¹) ^ t) := by
      rcases le_total (a.epsilon 0 ^ (t - 1)⁻¹) (a.epsilon 1 ^ (t - 2)⁻¹) with hh | hh
      · rw [min_eq_left hh, min_eq_left (Real.rpow_le_rpow (by positivity) hh ht)]
      · rw [min_eq_right hh, min_eq_right (Real.rpow_le_rpow (by positivity) hh ht)]
    rw [hpow, ← Real.rpow_mul he.le, ← Real.rpow_mul he'.le]
    congr 2 <;> ring
  · rw [← Real.rpow_mul he.le]
    congr 1
    ring

/-- The uniform parameter coefficient for exactly the activated derivative orders.
For two orders this is `uniformSigma`; for one it omits all curvature data. -/
def decreaseSigma (a : Parameters q p r) (H t initial : ℝ) : ℝ :=
  if 2 ≤ q then uniformSigma a H t initial else
    max initial (a.gamma3 * max (a.theta 0 * Real.powerFactorial (r - 1))
      (toleranceCoefficient (successCoefficient H t r a.eta2)
        (Real.powerFactorial (r - 1)) t r 1))

/-- A positive initial parameter makes the uniform decrease coefficient positive. -/
theorem decreaseSigma_pos {t initial : ℝ} (hi : 0 < initial) :
    0 < decreaseSigma a H t initial := by
  unfold decreaseSigma
  split_ifs
  · exact uniformSigma_pos hi
  · exact hi.trans_le (le_max_left _ _)

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]

/-- The actual legal parameter bound expressed at the common tolerance radius. -/
theorem RunPrefix.sigma_upper_radius {f : E → ℝ} {x s : ℕ → E}
    {sigma : ℕ → ℝ} {N k : ℕ} {beta : ℝ}
    (h : RunPrefix a f x s sigma N) (hf : HolderDerivative f p H beta)
    (hexp : (q : ℝ) < (p : ℝ) + beta) (htr : (p : ℝ) + beta ≤ r) (hk : k ≤ N) :
    sigma k ≤ decreaseSigma a H ((p : ℝ) + beta) (sigma 0) *
      toleranceRadius a ((p : ℝ) + beta) ^ ((p : ℝ) + beta - r) := by
  let t := (p : ℝ) + beta
  let z := toleranceRadius a t
  have hz : 0 < z := toleranceRadius_pos
  have ht : 1 < t := by
    have hh : (1 : ℝ) ≤ q := by exact_mod_cast a.order_pos
    dsimp [t]
    linarith
  have he := a.epsilon_pos 0 (by have := a.order_pos; simp only [Fin.val_zero]; omega)
  have he1 := a.epsilon_le_one 0 (by have := a.order_pos; simp only [Fin.val_zero]; omega)
  have hz1 : z ≤ 1 := toleranceRadius_le_first.trans
    (Real.rpow_le_one he.le he1 (inv_nonneg.mpr (by linarith)))
  have hZ : 1 ≤ z ^ (t - r) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hz hz1 (sub_nonpos.mpr htr)
  have hscale0 := tolerance_scale_of_root he hz htr (toleranceRadius_le_first (a := a))
  by_cases hq : 2 ≤ q
  · have he' := a.epsilon_pos 1 (by simp only [Fin.val_one]; omega)
    have hscale1 := tolerance_scale_of_root he' hz htr (toleranceRadius_le_second (a := a) hq)
    have hh := h.sigma_upper_uniform hf hexp htr hq hk
    have hM : 0 ≤ uniformSigma a H t (sigma 0) := (uniformSigma_pos h.initial_positive).le
    apply hh.trans
    rw [decreaseSigma, ite_eq_left hq]
    exact mul_le_mul_of_nonneg_left (max_le hscale0 hscale1) hM
  · let C := max (a.theta 0 * Real.powerFactorial (r - 1))
      (toleranceCoefficient (successCoefficient H t r a.eta2)
        (Real.powerFactorial (r - 1)) t r 1)
    let M := decreaseSigma a H t (sigma 0)
    have hr : 1 < r := ht.trans_le htr
    have hC : 0 ≤ C := (mul_pos (a.theta_pos 0)
      (Real.powerFactorial_pos (by linarith : 0 ≤ r - 1))).le.trans (le_max_left _ _)
    have hM : 0 ≤ M := (decreaseSigma_pos h.initial_positive).le
    have hMC : a.gamma3 * C ≤ M := by
      dsimp [M, decreaseSigma]
      rw [ite_eq_right hq]
      exact le_max_right _ _
    have hMi : sigma 0 ≤ M := by
      dsimp [M, decreaseSigma]
      rw [ite_eq_right hq]
      exact le_max_left _ _
    have hcoef := (le_max_right _ _ : toleranceCoefficient (successCoefficient H t r a.eta2)
      (Real.powerFactorial (r - 1)) t r 1 ≤ C)
    have hthreshold : successThreshold a H t ≤ C * z ^ (t - r) := by
      apply successThreshold_le_iff.mpr
      refine ⟨(le_max_left _ _).trans (le_mul_of_one_le_right hC hZ), ?_, fun hh => (hq hh).elim⟩
      exact mul_le_mul hcoef hscale0 (by positivity) hC
    have hg : 0 ≤ a.gamma3 := by linarith [a.gamma2_gt_one, a.gamma2_lt_gamma3]
    apply (h.sigma_upper hf hexp htr hk).trans
    apply max_le
    · exact hMi.trans (le_mul_of_one_le_right hM hZ)
    · calc
        _ ≤ a.gamma3 * (C * z ^ (t - r)) := mul_le_mul_of_nonneg_left hthreshold hg
        _ = (a.gamma3 * C) * z ^ (t - r) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hMC (by positivity)

/-- The exact uniform objective-decrease coefficient for the activated orders. -/
def decreaseConstant (a : Parameters q p r) (H t initial : ℝ) : ℝ :=
  a.eta1 / Real.powerFactorial r *
    (if 2 ≤ q then min (paymentCoefficient (a.alpha 0) (decreaseSigma a H t initial) r 1)
      (paymentCoefficient (a.alpha 1) (decreaseSigma a H t initial) r 2)
    else paymentCoefficient (a.alpha 0) (decreaseSigma a H t initial) r 1)

/-- The objective-decrease constant is positive for positive initialization. -/
theorem decreaseConstant_pos {t initial : ℝ} (hi : 0 < initial) :
    0 < decreaseConstant a H t initial := by
  have hp : (0 : ℝ) < p := by exact_mod_cast a.order_pos.trans a.degree_ge_order
  have hr := hp.trans a.power_gt_degree
  have hM := decreaseSigma_pos (a := a) (H := H) (t := t) hi
  unfold decreaseConstant
  apply mul_pos (div_pos a.eta1_pos (Real.powerFactorial_pos hr.le))
  split_ifs
  · exact lt_min (paymentCoefficient_pos (a.alpha_pos 0) hM)
      (paymentCoefficient_pos (a.alpha_pos 1) hM)
  · exact paymentCoefficient_pos (a.alpha_pos 0) hM

/-- The decrease constant is independent of accuracies: a family with fixed update,
residual and length parameters has the very same constant before any tolerance is chosen. -/
theorem decreaseConstant_eq_of_parameters {b : Parameters q p r} {t initial : ℝ}
    (heta1 : a.eta1 = b.eta1) (heta2 : a.eta2 = b.eta2)
    (hgamma3 : a.gamma3 = b.gamma3) (htheta : a.theta = b.theta)
    (halpha : a.alpha = b.alpha) :
    decreaseConstant a H t initial = decreaseConstant b H t initial := by
  simp only [decreaseConstant, decreaseSigma, uniformSigma, uniformSuccessThreshold,
    heta1, heta2, hgamma3, htheta, halpha]

/-- The actual accepted, nonterminal computed step pays the uniform decrease at the common
radius, using only the derived upper bound and the actual activated length tests. -/
theorem RunPrefix.successful_decrease {f : E → ℝ} {x s : ℕ → E}
    {sigma : ℕ → ℝ} {N k : ℕ} {beta : ℝ}
    (h : RunPrefix a f x s sigma N) (hf : HolderDerivative f p H beta)
    (hexp : (q : ℝ) < (p : ℝ) + beta) (htr : (p : ℝ) + beta ≤ r) (hk : k < N)
    (ha : Accepted a f (x k) (sigma k) (s k)) :
    decreaseConstant a H ((p : ℝ) + beta) (sigma 0) *
      toleranceRadius a ((p : ℝ) + beta) ^ ((p : ℝ) + beta) ≤
        f (x k) - f (x (k + 1)) := by
  let t := (p : ℝ) + beta
  let z := toleranceRadius a t
  let M := decreaseSigma a H t (sigma 0)
  have hz : 0 < z := toleranceRadius_pos
  have hM : 0 < M := decreaseSigma_pos h.initial_positive
  have hqr : (1 : ℝ) ≤ q := by exact_mod_cast a.order_pos
  have ht : 1 < t := by dsimp [t]; linarith
  have hr : 1 < r := ht.trans_le htr
  have hu : 0 < ‖s k‖ := norm_pos_iff.mpr (h.computed k hk).step_ne_zero
  have hupper := h.sigma_upper_radius hf hexp htr (Nat.le_of_lt hk)
  have hnon : ¬Stationary a f (x k + s k) := by
    simpa only [observation_succ] using h.nonterminal (k + 1) (by omega)
  have hpaid := (h.computed k hk).objective_decrease (h.positive (by omega)) ha
  rw [h.iterate k hk, ite_eq_left ha]
  have hfactor : 0 ≤ a.eta1 / Real.powerFactorial r := by
    exact (div_pos a.eta1_pos (Real.powerFactorial_pos (by linarith))).le
  have hpay : (if 2 ≤ q then min (paymentCoefficient (a.alpha 0) M r 1)
      (paymentCoefficient (a.alpha 1) M r 2) else paymentCoefficient (a.alpha 0) M r 1) *
        z ^ t ≤ sigma k * ‖s k‖ ^ r := by
    by_cases hfirst : a.epsilon 0 < ‖fderiv ℝ f (x k + s k)‖
    · have he := a.epsilon_pos 0 (by have := a.order_pos; simp only [Fin.val_zero]; omega)
      have hzpow := tolerance_power_of_root he hz.le ht
        (toleranceRadius_le_first (a := a))
      have hlength : a.alpha 0 * z ^ (t - 1) ≤ sigma k * ‖s k‖ ^ (r - 1) :=
        (mul_le_mul_of_nonneg_left (hzpow.trans hfirst.le) (a.alpha_pos 0).le).trans ha.2.1
      have hh := radial_payment_lower (a.alpha_pos 0) hM hz hu (by norm_num : (0 : ℝ) ≤ 1)
        hr hupper hlength
      apply le_trans _ hh
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      split_ifs
      · exact min_le_left _ _
      · exact le_rfl
    · have hsecond : 2 ≤ q ∧
          a.epsilon 1 < -leastCurvature (fderiv ℝ (fderiv ℝ f) (x k + s k)) := by
        have hh : ¬(2 ≤ q → -a.epsilon 1 ≤
            leastCurvature (fderiv ℝ (fderiv ℝ f) (x k + s k))) := by
          intro hh
          exact hnon ⟨le_of_not_gt hfirst, hh⟩
        push Not at hh
        exact ⟨hh.1, by linarith [hh.2]⟩
      have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hsecond.1
      have ht2 : 2 < t := by dsimp [t]; linarith
      have hr2 : 2 < r := ht2.trans_le htr
      have he := a.epsilon_pos 1 (by simp only [Fin.val_one]; omega)
      have hzpow := tolerance_power_of_root he hz.le ht2
        (toleranceRadius_le_second (a := a) hsecond.1)
      have hlength : a.alpha 1 * z ^ (t - 2) ≤ sigma k * ‖s k‖ ^ (r - 2) := by
        have hh := mul_le_mul_of_nonneg_left (hzpow.trans hsecond.2.le) (a.alpha_pos 1).le
        have hl := ha.2.2 hsecond.1
        nlinarith only [hh, hl]
      have hh := radial_payment_lower (a.alpha_pos 1) hM hz hu (by norm_num : (0 : ℝ) ≤ 2)
        hr2 hupper hlength
      rw [ite_eq_left hsecond.1]
      exact (mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)).trans hh
  have hh := mul_le_mul_of_nonneg_left hpay hfactor
  calc
    _ = (a.eta1 / Real.powerFactorial r) *
        ((if 2 ≤ q then min (paymentCoefficient (a.alpha 0) M r 1)
          (paymentCoefficient (a.alpha 1) M r 2)
        else paymentCoefficient (a.alpha 0) M r 1) * z ^ t) := by
      dsimp [decreaseConstant, M, z, t]
      ring
    _ ≤ (a.eta1 / Real.powerFactorial r) * (sigma k * ‖s k‖ ^ r) := hh
    _ = a.eta1 * (sigma k / Real.powerFactorial r * ‖s k‖ ^ r) := by ring
    _ ≤ _ := hpaid

end Optimization.UniversalRegularization
