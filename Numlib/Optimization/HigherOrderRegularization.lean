import Numlib.Optimization.ParameterUpdates
import Numlib.Optimization.TaylorModelRemainder

/-!
# Higher-order regularization trial traces

Canonical factorial-normalized Taylor models, actual acceptance ratios, and shared interval
updates. The value remainder uses only repeated-direction control of the highest derivative;
it does not require identifying a symmetric tensor's diagonal norm with its operator norm.
-/

noncomputable section
open scoped Nat
namespace Optimization.HigherOrderRegularization
open RegularizedTaylorModel ParameterUpdates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Global diagonal Lipschitz control of the actual highest derivative of a smooth map. -/
structure DiagonalLipschitz (f : E → ℝ) (degree : ℕ) (L : ℝ) : Prop where
  smooth : ContDiff ℝ degree f
  nonneg : 0 ≤ L
  bound : ∀ x y d, ‖(iteratedFDeriv ℝ degree f x - iteratedFDeriv ℝ degree f y)
    (fun _ ↦ d)‖ ≤ L * ‖x - y‖ * ‖d‖ ^ degree

/-- Operator-norm Lipschitz control implies the weaker diagonal condition. -/
theorem DiagonalLipschitz.of_operator {f : E → ℝ} {degree : ℕ} {L : ℝ}
    (hf : ContDiff ℝ degree f) (hL : 0 ≤ L)
    (h : ∀ x y, ‖iteratedFDeriv ℝ degree f x - iteratedFDeriv ℝ degree f y‖ ≤
      L * ‖x - y‖) : DiagonalLipschitz f degree L := by
  refine ⟨hf, hL, fun x y d => ?_⟩
  calc
    _ ≤ ‖iteratedFDeriv ℝ degree f x - iteratedFDeriv ℝ degree f y‖ * ‖d‖ ^ degree := by
      simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
        (iteratedFDeriv ℝ degree f x - iteratedFDeriv ℝ degree f y).le_opNorm (fun _ ↦ d)
    _ ≤ _ := mul_le_mul_of_nonneg_right (h x y) (pow_nonneg (norm_nonneg d) degree)

/-- Diagonal Lipschitz control already gives the sharp factorial Taylor value remainder. -/
theorem DiagonalLipschitz.value_remainder {f : E → ℝ} {degree : ℕ} {L : ℝ}
    (hf : DiagonalLipschitz f degree L) (hp : 1 ≤ degree) (x s : E) :
    |f (x + s) - taylorModel f degree x s| ≤
      L / ((degree + 1)! : ℝ) * ‖s‖ ^ (degree + 1) := by
  simpa only [Real.norm_eq_abs] using norm_sub_taylorModel_le_of_lipschitz_diagonal hp
    (fun _ _ => hf.smooth.contDiffAt)
    (fun t _ => by simpa only [add_sub_cancel_left] using hf.bound (x + t • s) x s)

/-- The standard Taylor model regularized by a factorial-normalized radial power. -/
def model (f : E → ℝ) (degree : ℕ) (x : E) (sigma : ℝ) (s : E) : ℝ :=
  taylorModel f degree x s + sigma / ((degree + 1)! : ℝ) * ‖s‖ ^ (degree + 1)

/-- The regularized model agrees with the objective at zero displacement. -/
@[simp] theorem model_zero (f : E → ℝ) (degree : ℕ) (x : E) (sigma : ℝ) :
    model f degree x sigma 0 = f x := by simp [model]

open Classical in
/-- The actual reduction divided by the unregularized Taylor prediction. The zero-step value
provides a harmless continuation after a finite algorithm has stopped. -/
def ratio (f : E → ℝ) (degree : ℕ) (x s : E) : ℝ :=
  if s = 0 then 1 else (f x - f (x + s)) /
    (taylorModel f degree x 0 - taylorModel f degree x s)

/-- The part of a regularization trace used by value and parameter estimates. Nonzero
trials strictly reduce the actual model; zero steps permit unused continuations after stopping.
Derivative residual tests belong to the stronger algorithm specification. -/
structure TrialTrace (params : RegularizationParameters) (degree : ℕ) (f : E → ℝ)
    (x s : ℕ → E) (sigma : ℕ → ℝ) : Prop extends
    RegularizationUpdates params (fun k => ratio f degree (x k) (s k)) sigma where
  decrease : ∀ k, model f degree (x k) (sigma k) (s k) < f (x k) ∨ s k = 0
  iterate : ∀ k, x (k + 1) = if params.eta1 ≤ ratio f degree (x k) (s k)
    then x k + s k else x k

variable {params : RegularizationParameters} {degree : ℕ} {f : E → ℝ}
    {x s : ℕ → E} {sigma : ℕ → ℝ}

/-- Any nonincreasing regularized model pays the full regularization in Taylor reduction. -/
theorem predicted_decrease_of_model_le {z d : E} {sigma : ℝ}
    (h : model f degree z sigma d ≤ model f degree z sigma 0) :
    sigma / ((degree + 1)! : ℝ) * ‖d‖ ^ (degree + 1) ≤
      taylorModel f degree z 0 - taylorModel f degree z d := by
  rw [model_zero] at h
  simp only [taylorModel_zero]
  unfold model at h
  linarith

/-- Every computed trial has the standard predicted reduction. -/
theorem TrialTrace.predicted_decrease (h : TrialTrace params degree f x s sigma) (k : ℕ) :
    sigma k / ((degree + 1)! : ℝ) * ‖s k‖ ^ (degree + 1) ≤
      taylorModel f degree (x k) 0 - taylorModel f degree (x k) (s k) := by
  rcases h.decrease k with hd | hz
  · apply predicted_decrease_of_model_le
    simpa only [model_zero] using hd.le
  · simp [hz]

/-- Every nonzero trial has a positive Taylor denominator. -/
theorem TrialTrace.predicted_pos (h : TrialTrace params degree f x s sigma) (k : ℕ)
    (hs : s k ≠ 0) : 0 < taylorModel f degree (x k) 0 - taylorModel f degree (x k) (s k) := by
  apply lt_of_lt_of_le _ (h.predicted_decrease k)
  exact mul_pos (div_pos (h.toRegularizationUpdates.pos k) (by positivity))
    (pow_pos (norm_pos_iff.mpr hs) _)

/-- A one-step sufficient-success criterion using the actual Taylor ratio and prediction. -/
theorem ratio_ge_of_prediction {z d : E} {sigma L : ℝ}
    (hf : DiagonalLipschitz f degree L) (hp : 1 ≤ degree) (hd : d ≠ 0)
    (hpos : 0 < taylorModel f degree z 0 - taylorModel f degree z d)
    (hpred : sigma / ((degree + 1)! : ℝ) * ‖d‖ ^ (degree + 1) ≤
      taylorModel f degree z 0 - taylorModel f degree z d)
    (hb : L / (1 - params.eta2) ≤ sigma) : params.eta2 ≤ ratio f degree z d := by
  rw [ratio, ite_eq_right hd, le_div_iff₀ hpos]
  have he := (abs_le.mp (hf.value_remainder hp z d)).2
  have hden : 0 < 1 - params.eta2 := sub_pos.mpr params.eta2_lt_one
  have hb' := (div_le_iff₀ hden).mp hb
  have hh := mul_le_mul_of_nonneg_right hb' (pow_nonneg (norm_nonneg d) (degree + 1))
  have hd' := mul_le_mul_of_nonneg_left hpred hden.le
  have hc : L / ((degree + 1)! : ℝ) * ‖d‖ ^ (degree + 1) ≤
      (1 - params.eta2) * (sigma / ((degree + 1)! : ℝ) * ‖d‖ ^ (degree + 1)) := by
    calc
      _ = (L * ‖d‖ ^ (degree + 1)) / ((degree + 1)! : ℝ) := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hh (by positivity)
      _ = _ := by ring
  have herr := he.trans (hc.trans hd')
  simp only [taylorModel_zero] at herr ⊢
  nlinarith

/-- Sufficient regularization makes every trial very successful. -/
theorem TrialTrace.ratio_ge_of_sigma_ge (h : TrialTrace params degree f x s sigma)
    {L : ℝ} (hf : DiagonalLipschitz f degree L) (hp : 1 ≤ degree) (k : ℕ)
    (hb : L / (1 - params.eta2) ≤ sigma k) : params.eta2 ≤ ratio f degree (x k) (s k) := by
  by_cases hs : s k = 0
  · simp [ratio, hs, params.eta2_lt_one.le]
  exact ratio_ge_of_prediction hf hp hs (h.predicted_pos k hs) (h.predicted_decrease k) hb

/-- The shared interval update mechanism uniformly bounds all regularization parameters. -/
theorem TrialTrace.sigma_upper (h : TrialTrace params degree f x s sigma) {L : ℝ}
    (hf : DiagonalLipschitz f degree L) (hp : 1 ≤ degree) (k : ℕ) :
    sigma k ≤ max (sigma 0) (params.gamma3 * (L / (1 - params.eta2))) :=
  h.toRegularizationUpdates.upper (fun j hj => h.ratio_ge_of_sigma_ge hf hp j hj) k

end Optimization.HigherOrderRegularization
