import Numlib.Optimization.Regularization.Universal.Bounds
/-!
# Very successful universal regularization trials

The Hölder parameter threshold controls the actual value and derivative errors.
Its finite - factorial coefficients force the ratio and every enabled length test.
-/

namespace UniversalRegularization
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- Multiplying a parameter threshold by a positive step power transfers the
Hölder error to the regularizer's power. -/
theorem power_transfer {t a r j H A R σ η : ℝ}
    (ht : 0 < t) (hA : 0 < A) (hR : 0 < R) (hη : η < 1)
    (hσ : R * H / (A * (1 - η)) * t ^ (a - r) ≤ σ) :
    H / A * t ^ (a - j) ≤ σ * (1 - η) / R * t ^ (r - j) := by
  have hm := mul_le_mul_of_nonneg_right hσ (Real.rpow_pos_of_pos ht (r - j)).le
  have he : t ^ (a - r) * t ^ (r - j) = t ^ (a - j) := by
    rw [←Real.rpow_add ht]
    congr 1
    ring
  rw [mul_assoc, he] at hm
  have hh := mul_le_mul_of_nonneg_right hm (div_pos (sub_pos.mpr hη) hR).le
  have hi : R * H / (A * (1 - η)) * t ^ (a - j) * ((1 - η) / R) = H / A * t ^ (a - j) := by
    field_simp [ne_of_gt (sub_pos.mpr hη)]
  rw [hi] at hh
  convert hh using 1; ring

/-- The source Hölder-success coefficient. -/
noncomputable def betaCoefficient {p : ℕ} (P : Settings p) (H β : ℝ) : ℝ :=
  Real.finiteFactorial P.r * H /
    (Real.finiteFactorial ((p : ℝ) + β - 1) * (1 - P.eta2))
/-- Hölder continuity bounds the actual Taylor value error. -/
theorem abs_value_error {p : ℕ} {f : E → ℝ} (hf : ContDiff ℝ p f)
    {H β : ℝ} (hH : 0 ≤ H) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (hholder : ∀ y z,
      ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ H * ‖y - z‖ ^ β)
    (x s : E) : |f (x + s) - TaylorModel.eval f p x s| ≤
      H / Real.finiteFactorial ((p : ℝ) + β) * ‖s‖ ^ ((p : ℝ) + β) := by
  have hh := TaylorModel.norm_iteratedFDeriv_sub_eval_le_holder (j := 0)
    (C := univ) (D := univ) isOpen_univ (Subset.refl _) convex_univ
    hf.contDiffOn hH hβ (fun y _ z _ => hholder y z) (Nat.zero_le p)
    (mem_univ x) (mem_univ (x + s))
  simp only [Nat.sub_zero] at hh
  rw [←Real.finiteFactorial_nat_add hβ hβ1] at hh
  have ht := (iteratedFDeriv ℝ 0 f (x + s)-
    iteratedFDeriv ℝ 0 (TaylorModel.eval f p x) s).le_opNorm (fun _ => (0 : E))
  simp only [sub_apply,iteratedFDeriv_zero_apply,Fin.prod_const,pow_zero,mul_one,
    Real.norm_eq_abs] at ht
  exact ht.trans hh
/-- The source parameter threshold makes the true Taylor ratio very successful. -/
theorem Step.ratio_ge_eta2 {p : ℕ} {P : Settings p} {f : E → ℝ}
    (hf : ContDiff ℝ p f) {H β : ℝ} (hH : 0 ≤ H) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (hholder : ∀ y z,
      ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ H * ‖y - z‖ ^ β)
    (ha : 1 < (p : ℝ) + β) {ε2 : Option ℝ} {x s : E} {σ : ℝ} (hσ : 0 < σ)
    (h : Step f P ε2 x s σ)
    (hthreshold : betaCoefficient P H β * ‖s‖ ^ ((p : ℝ) + β - P.r) ≤ σ) :
    P.eta2 ≤ (f x - f (x + s)) / (f x - TaylorModel.eval f p x s) := by
  have ht : 0 < ‖s‖ := norm_pos_iff.mpr h.ne_zero
  have hfac1 := Real.finiteFactorial_pos (show 0 ≤ (p : ℝ) + β - 1 by linarith)
  have hfacr := Real.finiteFactorial_pos (show 0 ≤ P.r by
    have := P.power_gt; have hp : (1 : ℝ) ≤ p := by exact_mod_cast P.order_pos
    linarith)
  have hb := power_transfer (a := (p : ℝ) + β) (r := P.r) (j := 0)
    ht hfac1 hfacr P.eta2_lt hthreshold
  simp only [sub_zero] at hb
  have hfac : Real.finiteFactorial ((p : ℝ) + β - 1) ≤ Real.finiteFactorial ((p : ℝ) + β) := by
    rw [Real.finiteFactorial_succ ha.le]
    nlinarith
  have hc := div_le_div_of_nonneg_left hH hfac1 hfac
  have hv := abs_value_error hf hH hβ hβ1 hholder x s
  have hc' := mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg (norm_nonneg s) ((p : ℝ) + β))
  have he : f (x + s) - TaylorModel.eval f p x s ≤
      σ * (1 - P.eta2) / Real.finiteFactorial P.r * ‖s‖ ^ P.r :=
    (le_abs_self _).trans (hv.trans (hc'.trans hb))
  have hp := h.taylor_decrease
  have hd : 0 < f x - TaylorModel.eval f p x s :=
    (mul_pos (div_pos hσ hfacr) (Real.rpow_pos_of_pos ht _)).trans hp
  apply (le_div_iff₀ hd).mpr
  have hm := mul_le_mul_of_nonneg_left hp.le (sub_pos.mpr P.eta2_lt).le
  have hid : (1 - P.eta2) * (σ / Real.finiteFactorial P.r * ‖s‖ ^ P.r) =
      σ * (1 - P.eta2) / Real.finiteFactorial P.r * ‖s‖ ^ P.r := by ring
  rw [hid] at hm
  linarith
/-- The source one-third restriction absorbs three equal positive terms. -/
theorem third_factor_absorption {G C F α : ℝ} (hF : 0 < F) (hC : 0 ≤ C)
    (hα : 0 ≤ α) (hαF : α ≤ F / 3) (hG : G ≤ 3 * (C / F)) : α * G ≤ C := by
  have hm := mul_le_mul_of_nonneg_left hG hα
  have hh := mul_le_mul_of_nonneg_right (show α * 3 ≤ F by linarith)
    (div_nonneg hC hF.le)
  have he : F * (C / F) = C := by field_simp
  rw [he] at hh
  nlinarith
/-- The source parameter thresholds force its actual gradient length check. -/
theorem Step.first_length_check {p : ℕ} {P : Settings p} {f : E → ℝ}
    (hf : ContDiff ℝ p f) {H β : ℝ} (hH : 0 ≤ H) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (hholder : ∀ y z,
      ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ H * ‖y - z‖ ^ β)
    (ha : 1 < (p : ℝ) + β) {ε2 : Option ℝ} {x s : E} {σ : ℝ} (hσ : 0 ≤ σ)
    (h : Step f P ε2 x s σ)
    (hfirst : P.theta1 * Real.finiteFactorial (P.r - 1) ≤ σ)
    (hthreshold : betaCoefficient P H β * ‖s‖ ^ ((p : ℝ) + β - P.r) ≤ σ) :
    P.alpha1 * ‖fderiv ℝ f (x + s)‖ ≤ σ * ‖s‖ ^ (P.r - 1) := by
  have ht : 0 < ‖s‖ := norm_pos_iff.mpr h.ne_zero
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast P.order_pos
  have hr := hpR.trans_lt P.power_gt
  have hfac1 := Real.finiteFactorial_pos (show 0 ≤ (p : ℝ) + β - 1 by linarith)
  have hfacr := Real.finiteFactorial_pos (show 0 ≤ P.r by linarith)
  have hfac := Real.finiteFactorial_pos (show 0 ≤ P.r - 1 by linarith)
  have hb := power_transfer (a := (p : ℝ) + β) (r := P.r) (j := 1)
    ht hfac1 hfacr P.eta2_lt hthreshold
  have hη := P.eta1_pos.trans_le P.eta12
  have hc : σ * (1 - P.eta2) / Real.finiteFactorial P.r ≤ σ / Real.finiteFactorial (P.r - 1) := by
    apply (div_le_div_iff₀ hfacr hfac).mpr
    rw [Real.finiteFactorial_succ hr.le]
    have hh := mul_le_mul_of_nonneg_left (show 1 - P.eta2 ≤ P.r by linarith)
      (mul_nonneg hσ hfac.le)
    nlinarith
  have hc' := mul_le_mul_of_nonneg_right hc
    (Real.rpow_nonneg (norm_nonneg s) (P.r - 1))
  have he := hb.trans hc'
  have hθ := mul_le_mul_of_nonneg_right ((le_div_iff₀ hfac).mpr hfirst)
    (Real.rpow_nonneg (norm_nonneg s) (P.r - 1))
  have hg := h.gradient_bound hf hH hβ hβ1 hholder hσ
  have hbound : ‖fderiv ℝ f (x + s)‖ ≤
      3 * (σ * ‖s‖ ^ (P.r - 1) / Real.finiteFactorial (P.r - 1)) := by
    simp only [div_mul_eq_mul_div] at he hθ hg
    linarith
  have hα : P.alpha1 ≤ Real.finiteFactorial (P.r - 1) / 3 := by
    have hm := mul_le_mul_of_nonneg_left
      (min_le_right (1 : ℝ) (Real.finiteFactorial (P.r - 1))) (by norm_num : (0 : ℝ) ≤ 1 / 3)
    linarith [P.alpha1_le]
  exact third_factor_absorption hfac (mul_nonneg hσ (Real.rpow_nonneg (norm_nonneg s) _))
    P.alpha1_pos.le hα hbound
/-- The source second-order parameter thresholds force the actual curvature length check. -/
theorem Step.second_length_check {p : ℕ} {P : Settings p} (hp : 2 ≤ p) {f : E → ℝ}
    (hf : ContDiff ℝ p f) {H β : ℝ} (hH : 0 ≤ H) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (hholder : ∀ y z,
      ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ H * ‖y - z‖ ^ β)
    (ha : 2 ≤ (p : ℝ) + β) (har : (p : ℝ) + β ≤ P.r)
    {ε2 : Option ℝ} {x s : E} {σ e : ℝ} (hσ : 0 ≤ σ) (h : Step f P ε2 x s σ)
    (he : e ∈ ε2) (v : E) (hv : ‖v‖ = 1)
    (hsecond : P.theta2 * Real.finiteFactorial (P.r - 2) ≤ σ)
    (hthreshold : betaCoefficient P H β * ‖s‖ ^ ((p : ℝ) + β - P.r) ≤ σ) :
    -P.alpha2 * iteratedFDeriv ℝ 2 f (x + s) (fun _ => v) ≤ σ * ‖s‖ ^ (P.r - 2) := by
  let a : ℝ := (p : ℝ) + β
  have ht : 0 < ‖s‖ := norm_pos_iff.mpr h.ne_zero
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hr : 2 < P.r := hpR.trans_lt P.power_gt
  have hfac1 := Real.finiteFactorial_pos (show 0 ≤ a - 1 by dsimp [a];linarith)
  have hfacr := Real.finiteFactorial_pos (show 0 ≤ P.r by linarith)
  have hfac2 := Real.finiteFactorial_pos (show 0 ≤ P.r - 2 by linarith)
  have hfaca := Real.finiteFactorial_pos (show 0 ≤ a - 2 by dsimp [a];linarith)
  have hb := power_transfer (a := a) (r := P.r) (j := 2)
    ht hfac1 hfacr P.eta2_lt hthreshold
  have hprev : Real.finiteFactorial (a - 1) = (a - 1) * Real.finiteFactorial (a - 2) := by
    have hh := Real.finiteFactorial_succ (show 1 ≤ a - 1 by dsimp [a];linarith)
    simpa only [show a - 1 - 1 = a - 2 by ring] using hh
  have heq : H / Real.finiteFactorial (a - 2) = (a - 1) * (H / Real.finiteFactorial (a - 1)) := by
    rw [hprev]
    field_simp [ne_of_gt (show 0 < a - 1 by dsimp [a];linarith)]
  have hb' := mul_le_mul_of_nonneg_left hb (show 0 ≤ a - 1 by dsimp [a];linarith)
  rw [←mul_assoc,←heq] at hb'
  have hη := P.eta1_pos.trans_le P.eta12
  have hc : (a - 1) * (σ * (1 - P.eta2) / Real.finiteFactorial P.r) ≤
      σ / Real.finiteFactorial (P.r - 2) := by
    rw [←mul_div_assoc]
    apply (div_le_div_iff₀ hfacr hfac2).mpr
    rw [Real.finiteFactorial_succ (by linarith : 1 ≤ P.r),
      Real.finiteFactorial_succ (by linarith : 1 ≤ P.r - 1)]
    have hrel : (a - 1) * (1 - P.eta2) ≤ P.r * (P.r - 1) := by
      have hm := mul_le_mul_of_nonneg_left (show 1 - P.eta2 ≤ 1 by linarith)
        (show 0 ≤ a - 1 by dsimp [a];linarith)
      have har' : a ≤ P.r := har
      nlinarith
    have hh := mul_le_mul_of_nonneg_left hrel (mul_nonneg hσ hfac2.le)
    rw [show P.r - 1 - 1 = P.r - 2 by ring]
    nlinarith
  have hc' := mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg (norm_nonneg s) (P.r - 2))
  have herror := hb'.trans (by simpa only [mul_assoc] using hc')
  have hθ := mul_le_mul_of_nonneg_right ((le_div_iff₀ hfac2).mpr hsecond)
    (Real.rpow_nonneg (norm_nonneg s) (P.r - 2))
  have hg := h.curvature_bound hp hf hH hβ hβ1 hholder hσ he v hv
  change H / Real.finiteFactorial ((p : ℝ) + β - 2) * ‖s‖ ^ ((p : ℝ) + β - 2) ≤ _ at herror
  have hbound : -iteratedFDeriv ℝ 2 f (x + s) (fun _ => v) ≤
      3 * (σ * ‖s‖ ^ (P.r - 2) / Real.finiteFactorial (P.r - 2)) := by
    simp only [div_mul_eq_mul_div] at herror hθ hg
    linarith
  have hα : P.alpha2 ≤ Real.finiteFactorial (P.r - 2) / 3 := by
    have hm := mul_le_mul_of_nonneg_left
      (min_le_right (1 : ℝ) (Real.finiteFactorial (P.r - 2))) (by norm_num : (0 : ℝ) ≤ 1 / 3)
    linarith [P.alpha2_le]
  have hh := third_factor_absorption hfac2
    (mul_nonneg hσ (Real.rpow_nonneg (norm_nonneg s) (P.r - 2))) P.alpha2_pos.le hα hbound
  nlinarith
/-- Every computed step at the source threshold has a very successful ratio
and both enabled length tests. -/
theorem Step.very_successful {p : ℕ} {P : Settings p} {f : E → ℝ}
    (hf : ContDiff ℝ p f) {H β : ℝ} (hH : 0 ≤ H) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (hholder : ∀ y z,
      ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ H * ‖y - z‖ ^ β)
    (ha : 1 < (p : ℝ) + β) (har : (p : ℝ) + β ≤ P.r)
    {ε2 : Option ℝ} {x s : E} {σ : ℝ} (hσ : 0 < σ) (h : Step f P ε2 x s σ)
    (hp : ∀ e ∈ ε2, 2 ≤ p) (ha2 : ∀ e ∈ ε2, 2 ≤ (p : ℝ) + β)
    (hfirst : P.theta1 * Real.finiteFactorial (P.r - 1) ≤ σ)
    (hsecond : ∀ e ∈ ε2, P.theta2 * Real.finiteFactorial (P.r - 2) ≤ σ)
    (hthreshold : betaCoefficient P H β * ‖s‖ ^ ((p : ℝ) + β - P.r) ≤ σ) :
    P.eta2 ≤ (f x - f (x + s)) / (f x - TaylorModel.eval f p x s) ∧
      P.alpha1 * ‖fderiv ℝ f (x + s)‖ ≤ σ * ‖s‖ ^ (P.r - 1) ∧
      ∀ e ∈ ε2, ∀ v : E, ‖v‖ = 1 →
        -P.alpha2 * iteratedFDeriv ℝ 2 f (x + s) (fun _ => v) ≤ σ * ‖s‖ ^ (P.r - 2) := by
  exact ⟨h.ratio_ge_eta2 hf hH hβ hβ1 hholder ha hσ hthreshold,
    h.first_length_check hf hH hβ hβ1 hholder ha hσ.le hfirst hthreshold,
    fun e he v hv => h.second_length_check (hp e he) hf hH hβ hβ1 hholder
      (ha2 e he) har hσ.le he v hv (hsecond e he) hthreshold⟩
end UniversalRegularization
