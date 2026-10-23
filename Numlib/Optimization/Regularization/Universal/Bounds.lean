import Numlib.Optimization.Regularization.Universal.Run
import Numlib.Analysis.Calculus.TaylorModel.Smooth
import Numlib.Analysis.InnerProductSpace.NormPow.SecondBound
/-!
# Actual gradient and curvature estimates for real-power models

Hölder Taylor remainders and genuine radial derivatives give the two source
step estimates with the finite real factorial coefficients.
-/

namespace UniversalRegularization
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- The actual first derivative splits into Taylor and radial derivatives. -/
theorem fderiv_model {f : E → ℝ} {p : ℕ} (P : Settings p) (x : E) (σ : ℝ) (s : E) :
    fderiv ℝ (model f p P.r x σ) s = fderiv ℝ (TaylorModel.eval f p x) s +
      (σ / Real.finiteFactorial P.r) • fderiv ℝ (fun z : E => ‖z‖ ^ P.r) s := by
  have hp : (1 : ℝ) ≤ p := by exact_mod_cast P.order_pos
  have hr : 1 < P.r := hp.trans_lt P.power_gt
  have hT := (TaylorModel.contDiff_eval f p x 1).differentiable (by norm_num) s
  have hN := (NormPower.hasFDerivAt_normPower hr s)
  rw [hN.fderiv]
  exact (hT.hasFDerivAt.add (hN.const_smul (σ / Real.finiteFactorial P.r))).fderiv
/-- The radial gradient penalty has the exact real factorial coefficient. -/
theorem norm_first_penalty {p : ℕ} (P : Settings p) {σ : ℝ} (hσ : 0 ≤ σ)
    {s : E} (hs : s ≠ 0) :
    ‖(σ / Real.finiteFactorial P.r) • fderiv ℝ (fun z : E => ‖z‖ ^ P.r) s‖ =
      σ / Real.finiteFactorial (P.r - 1) * ‖s‖ ^ (P.r - 1) := by
  have hp : (1 : ℝ) ≤ p := by exact_mod_cast P.order_pos
  have hr : 1 < P.r := hp.trans_lt P.power_gt
  have hfac := Real.finiteFactorial_pos (show 0 ≤ P.r - 1 by linarith)
  rw [norm_smul, Real.norm_of_nonneg (div_nonneg hσ
    (Real.finiteFactorial_pos (by linarith : 0 ≤ P.r)).le),
    norm_fderiv_norm_rpow_of_ne_zero hs, abs_of_pos (by linarith : 0 < P.r),
    Real.finiteFactorial_succ hr.le]
  field_simp
/-- Hölder continuity bounds the actual Taylor gradient remainder. -/
theorem norm_first_error {p : ℕ} (hp : 1 ≤ p) {f : E → ℝ} (hf : ContDiff ℝ p f)
    {H β : ℝ} (hH : 0 ≤ H) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (hholder : ∀ y z,
      ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ H * ‖y - z‖ ^ β)
    (x s : E) :
    ‖fderiv ℝ f (x + s)-fderiv ℝ (TaylorModel.eval f p x) s‖ ≤
      H / Real.finiteFactorial ((p : ℝ) + β - 1) * ‖s‖ ^ ((p : ℝ) + β - 1) := by
  have hh := TaylorModel.norm_iteratedFDeriv_sub_eval_le_holder (j := 1)
    (C := univ) (D := univ) isOpen_univ (Subset.refl _) convex_univ
    hf.contDiffOn hH hβ (fun y _ z _ => hholder y z) hp (mem_univ x) (mem_univ (x + s))
  have he : ((p - 1 : ℕ) : ℝ) + β = (p : ℝ) + β - 1 := by rw [Nat.cast_sub hp];norm_num;ring
  rw [←Real.finiteFactorial_nat_add hβ hβ1, he] at hh
  have hcoef : 0 ≤ H / Real.finiteFactorial ((p : ℝ) + β - 1) * ‖s‖ ^ ((p : ℝ) + β - 1) := by
    have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
    exact mul_nonneg (div_nonneg hH (Real.finiteFactorial_pos (by linarith)).le)
      (Real.rpow_nonneg (norm_nonneg _) _)
  apply ContinuousLinearMap.opNorm_le_bound _ hcoef
  intro v
  have ht := (iteratedFDeriv ℝ 1 f (x + s)-
    iteratedFDeriv ℝ 1 (TaylorModel.eval f p x) s).le_opNorm (fun _ => v)
  simp only [sub_apply, iteratedFDeriv_one_apply, Fin.prod_const, pow_one] at ht
  exact ht.trans (mul_le_mul_of_nonneg_right hh (norm_nonneg v))
/-- A genuine computed step satisfies the source gradient bound. -/
theorem Step.gradient_bound {p : ℕ} {P : Settings p} {f : E → ℝ}
    (hf : ContDiff ℝ p f) {H β : ℝ} (hH : 0 ≤ H) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (hholder : ∀ y z,
      ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ H * ‖y - z‖ ^ β)
    {ε2 : Option ℝ} {x s : E} {σ : ℝ} (hσ : 0 ≤ σ) (h : Step f P ε2 x s σ) :
    ‖fderiv ℝ f (x + s)‖ ≤
      H / Real.finiteFactorial ((p : ℝ) + β - 1) * ‖s‖ ^ ((p : ℝ) + β - 1) +
      σ / Real.finiteFactorial (P.r - 1) * ‖s‖ ^ (P.r - 1) +
      P.theta1 * ‖s‖ ^ (P.r - 1) := by
  have he := norm_first_error P.order_pos hf hH hβ hβ1 hholder x s
  have hm := h.first
  rw [fderiv_model P x σ s] at hm
  have hn := norm_first_penalty P hσ h.ne_zero
  have ht := norm_add_le
    (fderiv ℝ f (x + s)-fderiv ℝ (TaylorModel.eval f p x) s)
    (fderiv ℝ (TaylorModel.eval f p x) s)
  rw [sub_add_cancel] at ht
  have hu := norm_sub_le (fderiv ℝ (TaylorModel.eval f p x) s +
    (σ / Real.finiteFactorial P.r) • fderiv ℝ (fun z : E => ‖z‖ ^ P.r) s)
    ((σ / Real.finiteFactorial P.r) • fderiv ℝ (fun z : E => ‖z‖ ^ P.r) s)
  rw [add_sub_cancel_right, hn] at hu
  linarith
/-- The actual Hessian splits into the polynomial Hessian and radial Hessian. -/
theorem hessian_model {f : E → ℝ} {p : ℕ} (P : Settings p) (hp : 2 ≤ p)
    (x : E) (σ : ℝ) (s : E) :
    fderiv ℝ (fderiv ℝ (model f p P.r x σ)) s =
      fderiv ℝ (fderiv ℝ (TaylorModel.eval f p x)) s +
      (σ / Real.finiteFactorial P.r) • NormPower.second P.r s := by
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hr : 2 < P.r := hpR.trans_lt P.power_gt
  have hT := ((TaylorModel.contDiff_eval f p x 2).fderiv_right (m := 1)
    (by norm_num)).differentiable (by norm_num) s
  have hn := NormPower.hasFDerivAt_first_of_two_lt hr s
  have heq : fderiv ℝ (model f p P.r x σ) =
      fderiv ℝ (TaylorModel.eval f p x) +
        (σ / Real.finiteFactorial P.r) • NormPower.first P.r := by
    funext z
    rw [fderiv_model P x σ z,
      (NormPower.hasFDerivAt_normPower (by linarith : 1 < P.r) z).fderiv]
    rfl
  rw [heq]
  exact (hT.hasFDerivAt.add (hn.const_smul (σ / Real.finiteFactorial P.r))).fderiv
/-- The actual radial Hessian penalty has the sharp real-factorial bound. -/
theorem norm_second_penalty {p : ℕ} (P : Settings p) (hp : 2 ≤ p)
    {σ : ℝ} (hσ : 0 ≤ σ) (s : E) :
    ‖(σ / Real.finiteFactorial P.r) • NormPower.second P.r s‖ ≤
      σ / Real.finiteFactorial (P.r - 2) * ‖s‖ ^ (P.r - 2) := by
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hr : 2 < P.r := hpR.trans_lt P.power_gt
  have hf := Real.finiteFactorial_pos (show 0 ≤ P.r by linarith)
  have hf2 := Real.finiteFactorial_pos (show 0 ≤ P.r - 2 by linarith)
  have hs := ContinuousLinearMap.opNorm_smul_le (σ / Real.finiteFactorial P.r)
    (NormPower.second P.r s)
  rw [Real.norm_of_nonneg (div_nonneg hσ hf.le)] at hs
  have hb := mul_le_mul_of_nonneg_left (NormPower.norm_second_le_of_two_lt hr s)
    (div_nonneg hσ hf.le)
  apply hs.trans
  convert hb using 1
  rw [Real.finiteFactorial_succ (by linarith : 1 ≤ P.r),
    Real.finiteFactorial_succ (by linarith : 1 ≤ P.r - 1)]
  have he : P.r - 1-1 = P.r - 2 := by ring
  rw [he]
  field_simp [ne_of_gt (show 0 < P.r - 1 by linarith), ne_of_gt (show 0 < P.r by linarith)]
/-- Hölder continuity gives the genuine Hessian error on every unit direction. -/
theorem abs_second_error {p : ℕ} (hp : 2 ≤ p) {f : E → ℝ} (hf : ContDiff ℝ p f)
    {H β : ℝ} (hH : 0 ≤ H) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (hholder : ∀ y z,
      ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ H * ‖y - z‖ ^ β)
    (x s v : E) (hv : ‖v‖ = 1) :
    |iteratedFDeriv ℝ 2 f (x + s) (fun _ => v) -
      iteratedFDeriv ℝ 2 (TaylorModel.eval f p x) s (fun _ => v)| ≤
      H / Real.finiteFactorial ((p : ℝ) + β - 2) * ‖s‖ ^ ((p : ℝ) + β - 2) := by
  have hh := TaylorModel.norm_iteratedFDeriv_sub_eval_le_holder (j := 2)
    (C := univ) (D := univ) isOpen_univ (Subset.refl _) convex_univ
    hf.contDiffOn hH hβ (fun y _ z _ => hholder y z) hp (mem_univ x) (mem_univ (x + s))
  have he : ((p - 2 : ℕ) : ℝ) + β = (p : ℝ) + β - 2 := by rw [Nat.cast_sub hp];norm_num;ring
  rw [←Real.finiteFactorial_nat_add hβ hβ1, he] at hh
  have ht := (iteratedFDeriv ℝ 2 f (x + s)-
    iteratedFDeriv ℝ 2 (TaylorModel.eval f p x) s).le_opNorm (fun _ => v)
  simp only [sub_apply, Fin.prod_const, hv, one_pow, mul_one, Real.norm_eq_abs] at ht
  exact ht.trans hh
/-- Every genuine computed second-order step satisfies the source curvature bound. -/
theorem Step.curvature_bound {p : ℕ} {P : Settings p} (hp : 2 ≤ p) {f : E → ℝ}
    (hf : ContDiff ℝ p f) {H β : ℝ} (hH : 0 ≤ H) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (hholder : ∀ y z,
      ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ H * ‖y - z‖ ^ β)
    {ε2 : Option ℝ} {x s : E} {σ e : ℝ} (hσ : 0 ≤ σ) (h : Step f P ε2 x s σ)
    (he : e ∈ ε2) (v : E) (hv : ‖v‖ = 1) :
    -iteratedFDeriv ℝ 2 f (x + s) (fun _ => v) ≤
      H / Real.finiteFactorial ((p : ℝ) + β - 2) * ‖s‖ ^ ((p : ℝ) + β - 2) +
      σ / Real.finiteFactorial (P.r - 2) * ‖s‖ ^ (P.r - 2) +
      P.theta2 * ‖s‖ ^ (P.r - 2) := by
  have ha := abs_second_error hp hf hH hβ hβ1 hholder x s v hv
  have hm := h.second e he v hv
  have hh := congrArg (fun T : E →L[ℝ] E →L[ℝ] ℝ => T v v)
    (hessian_model (f := f) P hp x σ s)
  simp only [add_apply, smul_apply,
    smul_eq_mul] at hh
  rw [iteratedFDeriv_two_apply] at hm
  rw [hh] at hm
  have hn := norm_second_penalty P hp hσ s
  have ht := (((σ / Real.finiteFactorial P.r) • NormPower.second P.r s) v).le_opNorm v
  rw [hv, mul_one, Real.norm_eq_abs] at ht
  have hu := ((σ / Real.finiteFactorial P.r) • NormPower.second P.r s).le_opNorm v
  rw [hv, mul_one] at hu
  have hb := ht.trans (hu.trans hn)
  simp only [smul_apply, smul_eq_mul] at hb
  simp only [iteratedFDeriv_two_apply] at ha ⊢
  have hal := (abs_le.mp ha).1
  have hbu := (abs_le.mp hb).2
  linarith
end UniversalRegularization
