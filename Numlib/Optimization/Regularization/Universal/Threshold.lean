import Numlib.Optimization.Regularization.Universal.Success
import Mathlib.Tactic
/-!
# Accuracy thresholds for universal regularization

Real power identities turn literal trial point failure and genuine derivative
estimates into the source parameter threshold depending on the step. Constants retain
the exact finite factorial powers for first and second order.
-/

namespace UniversalRegularization
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- The real-power threshold converts a lower step-power estimate into the
parameter inequality needed for universal success. -/
theorem parameter_threshold_of_lower_power {t ε κ C d e σ : ℝ}
    (ht : 0 < t) (hε : 0 < ε) (hκ : 0 < κ) (hC : 0 < C)
    (hd : 0 ≤ d) (he : 0 < e)
    (hlower : ε < κ / C * t ^ e)
    (hσ : C ^ (-d / e) * κ ^ (1 + d / e) * ε ^ (-d / e) ≤ σ) :
    κ ≤ σ * t ^ d := by
  let τ := d / e
  have hτ : 0 ≤ τ := div_nonneg hd he.le
  have hu : 0 < C * ε / κ := div_pos (mul_pos hC hε) hκ
  have hbase : C * ε / κ ≤ t ^ e := by
    apply (div_le_iff₀ hκ).mpr
    have hh := (mul_lt_mul_of_pos_left hlower hC)
    have hi : C * (κ / C * t ^ e)=t ^ e * κ := by field_simp
    rw [hi] at hh
    linarith
  have hp := Real.rpow_le_rpow hu.le hbase hτ
  have hexp : e * τ=d := by dsimp [τ];field_simp
  rw [←Real.rpow_mul ht.le,hexp] at hp
  have hid : C ^ (-τ) * κ ^ (1 + τ) * ε ^ (-τ) * (C * ε / κ) ^ τ = κ := by
    rw [Real.div_rpow (mul_pos hC hε).le hκ.le,Real.mul_rpow hC.le hε.le,
      Real.rpow_add hκ,Real.rpow_one,Real.rpow_neg hC.le,Real.rpow_neg hε.le]
    field_simp
  have hσ' : C ^ (-τ) * κ ^ (1 + τ) * ε ^ (-τ) ≤ σ := by
    simpa only [τ, neg_div] using hσ
  have hlow : 0 ≤ C ^ (-τ) * κ ^ (1 + τ) * ε ^ (-τ) := by positivity
  have hσ0 : 0 ≤ σ := hlow.trans hσ'
  have hm := mul_le_mul hσ' hp (Real.rpow_nonneg hu.le _) hσ0
  rw [hid] at hm
  exact hm
/-- The source accuracy-dependent coefficient for the first or second order. -/
noncomputable def thresholdCoefficient {p : ℕ} (P : Settings p) (H β : ℝ) (j : ℕ) : ℝ :=
  (Real.finiteFactorial (P.r - j) / 3) ^ (((p : ℝ) + β - P.r) / ((p : ℝ) + β - j)) *
    betaCoefficient P H β ^ ((P.r - j) / ((p : ℝ) + β - j))
/-- The Hölder coefficient is nonnegative, including zero smoothness constants. -/
theorem betaCoefficient_nonneg {p : ℕ} (P : Settings p) {H β : ℝ}
    (hH : 0 ≤ H) (hβ : 0 ≤ β) : 0 ≤ betaCoefficient P H β := by
  have hp : (1 : ℝ) ≤ p := by exact_mod_cast P.order_pos
  have hr := P.power_gt
  unfold betaCoefficient
  exact div_nonneg (mul_nonneg (Real.finiteFactorial_pos (by linarith : 0 ≤ P.r)).le hH)
    (mul_nonneg (Real.finiteFactorial_pos (by linarith : 0 ≤ (p : ℝ) + β - 1)).le
      (sub_pos.mpr P.eta2_lt).le)
/-- The fixed source coefficient dominates the first Hölder derivative coefficient. -/
theorem holder_first_coefficient {p : ℕ} (P : Settings p) {H β : ℝ}
    (hH : 0 ≤ H) (hβ : 0 ≤ β) :
    H / Real.finiteFactorial ((p : ℝ) + β - 1) ≤
      betaCoefficient P H β / Real.finiteFactorial (P.r - 1) := by
  have hp : (1 : ℝ) ≤ p := by exact_mod_cast P.order_pos
  have hr : 1 < P.r := hp.trans_lt P.power_gt
  have hf := Real.finiteFactorial_pos (show 0 ≤ (p : ℝ) + β - 1 by linarith)
  have hfr := Real.finiteFactorial_pos (show 0 ≤ P.r by linarith)
  have hfr1 := Real.finiteFactorial_pos (show 0 ≤ P.r - 1 by linarith)
  have hκ := betaCoefficient_nonneg P hH hβ
  have hid : H / Real.finiteFactorial ((p : ℝ) + β - 1) =
      betaCoefficient P H β * (1 - P.eta2) / Real.finiteFactorial P.r := by
    unfold betaCoefficient
    field_simp [ne_of_gt (sub_pos.mpr P.eta2_lt)]
  rw [hid]
  apply (div_le_div_iff₀ hfr hfr1).mpr
  rw [Real.finiteFactorial_succ hr.le]
  have hη := P.eta1_pos.trans_le P.eta12
  have hm := mul_le_mul_of_nonneg_left (show 1 - P.eta2 ≤ P.r by linarith)
    (mul_nonneg hκ hfr1.le)
  nlinarith
/-- The exact accuracy threshold bounds the step-dependent parameter term
whenever an actual nonterminal measure obeys the model error estimate. -/
theorem step_threshold_of_model_bound {t ε κ F a r j σ A θ V : ℝ}
    (ht : 0 < t) (hε : 0 < ε) (hF : 0 < F) (hσ : 0 < σ)
    (ha : j < a) (har : a ≤ r) (hA : A ≤ κ / F) (hθ : θ * F ≤ σ)
    (hbound : V ≤ A * t ^ (a - j) + σ / F * t ^ (r - j) + θ * t ^ (r - j))
    (hfail : ε < V)
    (hparameter : (F / 3) ^ ((a - r) / (a - j)) * κ ^ ((r - j) / (a - j)) *
      ε ^ ((a - r) / (a - j)) ≤ σ) :
    κ * t ^ (a - r) ≤ σ := by
  by_contra hn
  have hnot : σ < κ * t ^ (a - r) := lt_of_not_ge hn
  have hbad := mul_lt_mul_of_pos_right hnot (Real.rpow_pos_of_pos ht (r - a))
  have hcancel : t ^ (a - r) * t ^ (r - a)=1 := by
    rw [←Real.rpow_add ht, show a - r + (r - a) = 0 by ring, Real.rpow_zero]
  rw [mul_assoc,hcancel,mul_one] at hbad
  have hκ : 0 < κ := (mul_pos hσ (Real.rpow_pos_of_pos ht _)).trans hbad
  have he : 0 < a - j := sub_pos.mpr ha
  have hd : 0 ≤ r - a := sub_nonneg.mpr har
  have hp : t ^ (r - j)=t ^ (r - a) * t ^ (a - j) := by
    rw [←Real.rpow_add ht]
    congr 1
    ring
  have hb := mul_le_mul_of_nonneg_right hA (Real.rpow_nonneg ht.le (a - j))
  have htheta := mul_le_mul_of_nonneg_right ((le_div_iff₀ hF).mpr hθ)
    (Real.rpow_nonneg ht.le (r - j))
  have hsmall : σ / F * t ^ (r - j) < κ / F * t ^ (a - j) := by
    rw [hp]
    have hh := mul_lt_mul_of_pos_right ((div_lt_div_iff_of_pos_right hF).mpr hbad)
      (Real.rpow_pos_of_pos ht (a - j))
    convert hh using 1; ring
  have hsharp : ε < κ / (F / 3) * t ^ (a - j) := by
    have hi : κ / (F / 3) * t ^ (a - j)=3 * (κ / F * t ^ (a - j)) := by field_simp
    rw [hi]
    linarith
  have hneg : (a - r) / (a - j)=-(r - a) / (a - j) := by ring
  have hexp : (r - j) / (a - j)=1 + (r - a) / (a - j) := by field_simp;ring
  rw [hneg,hexp] at hparameter
  have hresult := parameter_threshold_of_lower_power ht hε hκ
    (show 0 < F / 3 by positivity) hd he hsharp hparameter
  exact (not_le_of_gt hbad) hresult
/-- The fixed source coefficient dominates the second Hölder derivative coefficient. -/
theorem holder_second_coefficient {p : ℕ} (P : Settings p) (hp : 2 ≤ p) {H β : ℝ}
    (hH : 0 ≤ H) (hβ : 0 ≤ β) (har : (p : ℝ) + β ≤ P.r) :
    H / Real.finiteFactorial ((p : ℝ) + β - 2) ≤
      betaCoefficient P H β / Real.finiteFactorial (P.r - 2) := by
  let a : ℝ := (p : ℝ) + β
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have ha : 2 ≤ a := by dsimp [a];linarith
  have hr : 2 < P.r := hpR.trans_lt P.power_gt
  have hfa := Real.finiteFactorial_pos (show 0 ≤ a - 2 by linarith)
  have hfr := Real.finiteFactorial_pos (show 0 ≤ P.r by linarith)
  have hfr2 := Real.finiteFactorial_pos (show 0 ≤ P.r - 2 by linarith)
  have hκ := betaCoefficient_nonneg P hH hβ
  have hid : H / Real.finiteFactorial (a - 2) =
      (a - 1) * (betaCoefficient P H β * (1 - P.eta2) / Real.finiteFactorial P.r) := by
    have he : Real.finiteFactorial (a - 1)=(a - 1) * Real.finiteFactorial (a - 2) := by
      simpa only [show a - 1 - 1=a - 2 by ring] using
        Real.finiteFactorial_succ (show 1 ≤ a - 1 by linarith)
    unfold betaCoefficient
    change H / Real.finiteFactorial (a - 2) =
      (a - 1) * (Real.finiteFactorial P.r * H / (Real.finiteFactorial (a - 1) * (1 - P.eta2)) *
        (1 - P.eta2) / Real.finiteFactorial P.r)
    rw [he]
    field_simp [ne_of_gt (sub_pos.mpr P.eta2_lt),ne_of_gt (show 0 < a - 1 by linarith)]
  change H / Real.finiteFactorial (a - 2) ≤ _
  rw [hid,←mul_div_assoc]
  apply (div_le_div_iff₀ hfr hfr2).mpr
  rw [Real.finiteFactorial_succ (by linarith : 1 ≤ P.r),
    Real.finiteFactorial_succ (by linarith : 1 ≤ P.r - 1),
    show P.r - 1 - 1=P.r - 2 by ring]
  have hη := P.eta1_pos.trans_le P.eta12
  have hrel : (a - 1) * (1 - P.eta2) ≤ P.r * (P.r - 1) := by
    have hm := mul_le_mul_of_nonneg_left (show 1 - P.eta2 ≤ 1 by linarith)
      (show 0 ≤ a - 1 by linarith)
    have h_ar : a ≤ P.r := har
    nlinarith
  have hh := mul_le_mul_of_nonneg_left hrel (mul_nonneg hκ hfr2.le)
  nlinarith
/-- Failure of the true trial gradient and the source accuracy threshold give
its parameter threshold depending on the step. -/
theorem Step.threshold_of_gradient_failure {p : ℕ} {P : Settings p} {f : E → ℝ}
    (hf : ContDiff ℝ p f) {H β : ℝ} (hH : 0 ≤ H) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (hholder : ∀ y z,
      ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ H * ‖y - z‖ ^ β)
    (ha : 1 < (p : ℝ) + β) (har : (p : ℝ) + β ≤ P.r)
    {ε2 : Option ℝ} {x s : E} {σ ε : ℝ} (hσ : 0 < σ) (hε : 0 < ε)
    (h : Step f P ε2 x s σ) (hfail : ε < ‖fderiv ℝ f (x + s)‖)
    (hθ : P.theta1 * Real.finiteFactorial (P.r - 1) ≤ σ)
    (hparameter : thresholdCoefficient P H β 1 *
      ε ^ (((p : ℝ) + β - P.r) / ((p : ℝ) + β - 1)) ≤ σ) :
    betaCoefficient P H β * ‖s‖ ^ ((p : ℝ) + β - P.r) ≤ σ := by
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast P.order_pos
  have hr := hpR.trans_lt P.power_gt
  exact step_threshold_of_model_bound (norm_pos_iff.mpr h.ne_zero) hε
    (Real.finiteFactorial_pos (by linarith : 0 ≤ P.r - 1)) hσ ha har
    (holder_first_coefficient P hH hβ) hθ
    (h.gradient_bound hf hH hβ hβ1 hholder hσ.le) hfail
    (by simpa only [thresholdCoefficient,Nat.cast_one] using hparameter)
/-- True negative curvature and the second source accuracy threshold give
the parameter threshold depending on the step. -/
theorem Step.threshold_of_curvature_failure {p : ℕ} {P : Settings p} (hp : 2 ≤ p)
    {f : E → ℝ} (hf : ContDiff ℝ p f) {H β : ℝ}
    (hH : 0 ≤ H) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (hholder : ∀ y z,
      ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ H * ‖y - z‖ ^ β)
    (ha : 2 < (p : ℝ) + β) (har : (p : ℝ) + β ≤ P.r)
    {ε2 : Option ℝ} {x s v : E} {σ ε : ℝ} (hσ : 0 < σ) (hε : 0 < ε)
    (h : Step f P ε2 x s σ) (he : ε ∈ ε2) (hv : ‖v‖ = 1)
    (hfail : ε < -iteratedFDeriv ℝ 2 f (x + s) (fun _ => v))
    (hθ : P.theta2 * Real.finiteFactorial (P.r - 2) ≤ σ)
    (hparameter : thresholdCoefficient P H β 2 *
      ε ^ (((p : ℝ) + β - P.r) / ((p : ℝ) + β - 2)) ≤ σ) :
    betaCoefficient P H β * ‖s‖ ^ ((p : ℝ) + β - P.r) ≤ σ := by
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hr := hpR.trans_lt P.power_gt
  exact step_threshold_of_model_bound (norm_pos_iff.mpr h.ne_zero) hε
    (Real.finiteFactorial_pos (by linarith : 0 ≤ P.r - 2)) hσ ha har
    (holder_second_coefficient P hp hH hβ har) hθ
    (h.curvature_bound hp hf hH hβ hβ1 hholder hσ.le he v hv) hfail
    (by simpa only [thresholdCoefficient,Nat.cast_ofNat] using hparameter)
/-- Literal failure of the trial-point stopping test is sufficient; no
endpoint nonoptimality assumption is hidden in the execution. -/
theorem Step.threshold_of_trial_failure {p : ℕ} {P : Settings p} {f : E → ℝ}
    (hf : ContDiff ℝ p f) {H β : ℝ} (hH : 0 ≤ H) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (hholder : ∀ y z,
      ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ H * ‖y - z‖ ^ β)
    (ha : 1 < (p : ℝ) + β) (har : (p : ℝ) + β ≤ P.r)
    {ε1 : ℝ} {ε2 : Option ℝ} {x s : E} {σ : ℝ}
    (hσ : 0 < σ) (hε1 : 0 < ε1) (hε2 : ∀ e ∈ ε2, 0 < e)
    (h : Step f P ε2 x s σ) (hfail : ¬Stops f ε1 ε2 (x + s))
    (hp : ∀ e ∈ ε2, 2 ≤ p) (ha2 : ∀ e ∈ ε2, 2 < (p : ℝ) + β)
    (hfirst : max (P.theta1 * Real.finiteFactorial (P.r - 1))
      (thresholdCoefficient P H β 1 *
        ε1 ^ (((p : ℝ) + β - P.r) / ((p : ℝ) + β - 1))) ≤ σ)
    (hsecond : ∀ e ∈ ε2, max (P.theta2 * Real.finiteFactorial (P.r - 2))
      (thresholdCoefficient P H β 2 *
        e ^ (((p : ℝ) + β - P.r) / ((p : ℝ) + β - 2))) ≤ σ) :
    betaCoefficient P H β * ‖s‖ ^ ((p : ℝ) + β - P.r) ≤ σ := by
  classical
  by_cases hg : ε1 < ‖fderiv ℝ f (x + s)‖
  · exact h.threshold_of_gradient_failure hf hH hβ hβ1 hholder ha har hσ hε1 hg
      ((le_max_left _ _).trans hfirst) ((le_max_right _ _).trans hfirst)
  have hc : ¬∀ e ∈ ε2, ∀ v : E, ‖v‖ = 1 →
      -e ≤ iteratedFDeriv ℝ 2 f (x + s) (fun _ => v) := by
    intro hc
    exact hfail ⟨le_of_not_gt hg,hc⟩
  push Not at hc
  obtain ⟨e, he, v, hv, hnegative⟩ := hc
  exact h.threshold_of_curvature_failure (hp e he) hf hH hβ hβ1 hholder
    (ha2 e he) har hσ (hε2 e he) he hv (by linarith)
    ((le_max_left _ _).trans (hsecond e he)) ((le_max_right _ _).trans (hsecond e he))
end UniversalRegularization
