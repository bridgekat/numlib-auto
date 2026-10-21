import Numlib.Optimization.ParameterUpdates
import Numlib.Optimization.AdaptiveRegularizationComplexity
import Numlib.Optimization.TaylorModelRemainder

/-!
# Adaptive cubic regularization

Cubic Taylor models, actual trial acceptance, and residual-based inexact step computation.
The parameter mechanism is shared with all adaptive regularization orders. Zero steps provide
unused continuations at exact critical points; every nonzero computed step strictly reduces
its regularized model.
-/

noncomputable section
namespace Optimization.CubicRegularization
open RegularizedTaylorModel ParameterUpdates

variable {E : Type} [NormedAddCommGroup E]
section Normed
variable [NormedSpace ℝ E]

/-- A twice continuously differentiable objective with a nonnegative Lipschitz Hessian bound. -/
structure HessianLipschitz (f : E → ℝ) (L : ℝ) : Prop where
  smooth : ContDiff ℝ 2 f
  nonneg : 0 ≤ L
  bound : ∀ x y, ‖iteratedFDeriv ℝ 2 f x - iteratedFDeriv ℝ 2 f y‖ ≤ L * ‖x - y‖

/-- The cubic regularization of the canonical quadratic Taylor polynomial. -/
def cubicModel (f : E → ℝ) (x : E) (sigma : ℝ) (s : E) : ℝ :=
  regularizedModel f 2 x sigma 6 3 s

/-- Polynomial power form of the cubic model. -/
theorem cubicModel_eq (f : E → ℝ) (x : E) (sigma : ℝ) (s : E) :
    cubicModel f x sigma s = taylorModel f 2 x s + sigma / 6 * ‖s‖ ^ 3 := by
  simp [cubicModel, regularizedModel]

/-- The cubic model agrees with the objective at the expansion point. -/
@[simp] theorem cubicModel_zero (f : E → ℝ) (x : E) (sigma : ℝ) :
    cubicModel f x sigma 0 = f x := by simp [cubicModel_eq]

open Classical in
/-- Actual objective decrease divided by unregularized quadratic Taylor decrease. -/
def ratio (f : E → ℝ) (x s : E) (_sigma : ℝ) : ℝ :=
  if s = 0 then 1 else (f x - f (x + s)) / (taylorModel f 2 x 0 - taylorModel f 2 x s)

/-- Actual cubic trial acceptance and interval updates, independent of a stationarity rule. -/
structure TrialTrace (p : RegularizationParameters) (f : E → ℝ)
    (x s : ℕ → E) (sigma : ℕ → ℝ) : Prop extends
    RegularizationUpdates p (fun k => ratio f (x k) (s k) (sigma k)) sigma where
  decrease : ∀ k, cubicModel f (x k) (sigma k) (s k) < f (x k) ∨ s k = 0
  iterate : ∀ k, x (k + 1) = if p.eta1 ≤ ratio f (x k) (s k) (sigma k)
    then x k + s k else x k

/-- A lawful cubic-model update trace with an actual model derivative residual. Zero steps
permit continuation after exact stationarity; every nonzero step strictly reduces the model. -/
structure IsRun (p : RegularizationParameters) (theta : ℝ) (f : E → ℝ)
    (x s : ℕ → E) (sigma : ℕ → ℝ) : Prop extends TrialTrace p f x s sigma where
  residual : ∀ k, ‖fderiv ℝ (cubicModel f (x k) (sigma k)) (s k)‖ ≤ theta / 2 * ‖s k‖ ^ 2

variable {p : RegularizationParameters} {theta : ℝ} {f : E → ℝ}
    {x s : ℕ → E} {sigma : ℕ → ℝ}

/-- Model decrease forces the Taylor reduction to pay for the cubic regularizer. -/
theorem TrialTrace.predicted_decrease (h : TrialTrace p f x s sigma) (k : ℕ) :
    sigma k / 6 * ‖s k‖ ^ 3 ≤ taylorModel f 2 (x k) 0 - taylorModel f 2 (x k) (s k) := by
  have hh := h.decrease k
  rcases hh with hh | hz
  · rw [cubicModel_eq] at hh
    simp only [taylorModel_zero]
    linarith
  · simp [hz]

/-- Every nonzero step yields strictly more Taylor decrease than its regularization term. -/
theorem TrialTrace.predicted_decrease_strict (h : TrialTrace p f x s sigma) (k : ℕ)
    (hs : s k ≠ 0) :
    sigma k / 6 * ‖s k‖ ^ 3 < taylorModel f 2 (x k) 0 - taylorModel f 2 (x k) (s k) := by
  have hh := (h.decrease k).resolve_right hs
  rw [cubicModel_eq] at hh
  simp only [taylorModel_zero]
  linarith

/-- Predicted reduction is positive at every nonzero computed step. -/
theorem TrialTrace.predicted_pos (h : TrialTrace p f x s sigma) (k : ℕ) (hs : s k ≠ 0) :
    0 < taylorModel f 2 (x k) 0 - taylorModel f 2 (x k) (s k) := by
  exact (mul_pos (div_pos (h.toRegularizationUpdates.pos k) (by norm_num))
    (pow_pos (norm_pos_iff.mpr hs) 3)).trans_le (h.predicted_decrease k)

/-- Accepted trials realize the acceptance fraction of predicted reduction. -/
theorem TrialTrace.accepted_decrease (h : TrialTrace p f x s sigma) (k : ℕ)
    (hk : p.eta1 ≤ ratio f (x k) (s k) (sigma k)) :
    p.eta1 * (taylorModel f 2 (x k) 0 - taylorModel f 2 (x k) (s k)) ≤
      f (x k) - f (x (k + 1)) := by
  rw [h.iterate k, ite_eq_left hk]
  by_cases hs : s k = 0
  · simp [hs]
  · rw [ratio, ite_eq_right hs] at hk
    exact (le_div_iff₀ (h.predicted_pos k hs)).mp hk

/-- Accepted cubic steps pay a uniform amount of actual objective decrease. -/
theorem TrialTrace.accepted_cubic_decrease (h : TrialTrace p f x s sigma) (k : ℕ)
    (hk : p.eta1 ≤ ratio f (x k) (s k) (sigma k)) :
    p.eta1 * p.sigmaMin / 6 * ‖s k‖ ^ 3 ≤ f (x k) - f (x (k + 1)) := by
  have hp := h.predicted_decrease k
  have hd := h.accepted_decrease k hk
  have hs := h.toRegularizationUpdates.lower k
  calc
    _ ≤ p.eta1 * (sigma k / 6 * ‖s k‖ ^ 3) := by
      have hh := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hs (pow_nonneg (norm_nonneg (s k)) 3)) p.eta1_pos.le
      nlinarith
    _ ≤ _ := (mul_le_mul_of_nonneg_left hp p.eta1_pos.le).trans hd

/-- The objective never increases, including on unused zero-step continuations. -/
theorem TrialTrace.objective_nonincrease (h : TrialTrace p f x s sigma) (k : ℕ) :
    f (x (k + 1)) ≤ f (x k) := by
  by_cases hk : p.eta1 ≤ ratio f (x k) (s k) (sigma k)
  · have hd := h.accepted_decrease k hk
    have hpred := (mul_nonneg (div_nonneg (h.toRegularizationUpdates.pos k).le
      (by norm_num)) (pow_nonneg (norm_nonneg (s k)) 3)).trans (h.predicted_decrease k)
    have hn := mul_nonneg p.eta1_pos.le hpred
    linarith
  · rw [h.iterate k, ite_eq_right hk]

/-- Lipschitz Hessians give the sharp cubic Taylor value remainder. -/
theorem HessianLipschitz.value_remainder {L : ℝ} (hf : HessianLipschitz f L) (x s : E) :
    |f (x + s) - taylorModel f 2 x s| ≤ L / 6 * ‖s‖ ^ 3 := by
  have hh := norm_sub_taylorModel_le_holder (n := 1) (β := 1) (H := L)
    (x := x) (s := s) (by norm_num)
    (fun t _ => hf.smooth.contDiffAt)
    (fun t _ => by simpa using hf.bound (x + t • s) x)
  norm_num [Finset.prod_range_succ, Real.rpow_natCast, Real.norm_eq_abs] at hh
  exact hh

/-- The first Taylor derivative has a sharp quadratic remainder. -/
theorem HessianLipschitz.derivative_remainder {L : ℝ} (hf : HessianLipschitz f L) (x s : E) :
    ‖fderiv ℝ f (x + s) - fderiv ℝ (taylorModel f 2 x) s‖ ≤ L / 2 * ‖s‖ ^ 2 := by
  have hh := norm_iteratedFDeriv_sub_taylorModel_le_holder (p := 2) (j := 1)
    (β := 1) (H := L) (x := x) (s := s) (by norm_num) (by norm_num)
    (fun t _ => hf.smooth.contDiffAt)
    (fun t _ => by simpa using hf.bound (x + t • s) x)
  rw [show (1 : ℕ) = 0 + 1 from rfl,
    norm_iteratedFDeriv_sub_eq_fderiv_sub, norm_iteratedFDeriv_zero_sub] at hh
  norm_num [Finset.prod_range_succ, Real.rpow_natCast] at hh
  exact hh

/-- Above the Taylor-error threshold, every nonzero trial is very successful. -/
theorem TrialTrace.ratio_ge_of_sigma_ge (h : TrialTrace p f x s sigma) {L : ℝ}
    (hf : HessianLipschitz f L) (k : ℕ) (hb : L / (1 - p.eta2) ≤ sigma k) :
    p.eta2 ≤ ratio f (x k) (s k) (sigma k) := by
  by_cases hs : s k = 0
  · simp [ratio, hs, p.eta2_lt_one.le]
  have hp := h.predicted_pos k hs
  rw [ratio, ite_eq_right hs, le_div_iff₀ hp]
  have hd := h.predicted_decrease k
  have he := (abs_le.mp (hf.value_remainder (x k) (s k))).2
  have hden : 0 < 1 - p.eta2 := sub_pos.mpr p.eta2_lt_one
  have hb' := (div_le_iff₀ hden).mp hb
  have hh := mul_le_mul_of_nonneg_right hb' (pow_nonneg (norm_nonneg (s k)) 3)
  have hd' := mul_le_mul_of_nonneg_left hd hden.le
  simp only [taylorModel_zero] at *
  nlinarith

/-- The regularization parameters are uniformly bounded by the Hessian smoothness constant. -/
theorem TrialTrace.sigma_upper (h : TrialTrace p f x s sigma) {L : ℝ}
    (hf : HessianLipschitz f L) (n : ℕ) :
    sigma n ≤ max (sigma 0) (p.gamma3 * (L / (1 - p.eta2))) :=
  h.toRegularizationUpdates.upper (fun k hk => h.ratio_ge_of_sigma_ge hf k hk) n

/-- The common trial-trace bound applied to a model-residual run. -/
theorem IsRun.predicted_decrease (h : IsRun p theta f x s sigma) (k : ℕ) :
    sigma k / 6 * ‖s k‖ ^ 3 ≤ taylorModel f 2 (x k) 0 - taylorModel f 2 (x k) (s k) :=
  h.toTrialTrace.predicted_decrease k

/-- The common trial-trace bound applied to a model-residual run. -/
theorem IsRun.predicted_decrease_strict (h : IsRun p theta f x s sigma) (k : ℕ)
    (hs : s k ≠ 0) :
    sigma k / 6 * ‖s k‖ ^ 3 < taylorModel f 2 (x k) 0 - taylorModel f 2 (x k) (s k) :=
  h.toTrialTrace.predicted_decrease_strict k hs

/-- The common trial-trace bound applied to a model-residual run. -/
theorem IsRun.predicted_pos (h : IsRun p theta f x s sigma) (k : ℕ) (hs : s k ≠ 0) :
    0 < taylorModel f 2 (x k) 0 - taylorModel f 2 (x k) (s k) :=
  h.toTrialTrace.predicted_pos k hs

/-- The common trial-trace bound applied to a model-residual run. -/
theorem IsRun.accepted_decrease (h : IsRun p theta f x s sigma) (k : ℕ)
    (hk : p.eta1 ≤ ratio f (x k) (s k) (sigma k)) :
    p.eta1 * (taylorModel f 2 (x k) 0 - taylorModel f 2 (x k) (s k)) ≤
      f (x k) - f (x (k + 1)) :=
  h.toTrialTrace.accepted_decrease k hk

/-- The common trial-trace bound applied to a model-residual run. -/
theorem IsRun.accepted_cubic_decrease (h : IsRun p theta f x s sigma) (k : ℕ)
    (hk : p.eta1 ≤ ratio f (x k) (s k) (sigma k)) :
    p.eta1 * p.sigmaMin / 6 * ‖s k‖ ^ 3 ≤ f (x k) - f (x (k + 1)) :=
  h.toTrialTrace.accepted_cubic_decrease k hk

/-- The common trial-trace bound applied to a model-residual run. -/
theorem IsRun.objective_nonincrease (h : IsRun p theta f x s sigma) (k : ℕ) :
    f (x (k + 1)) ≤ f (x k) :=
  h.toTrialTrace.objective_nonincrease k

/-- The common trial-trace bound applied to a model-residual run. -/
theorem IsRun.ratio_ge_of_sigma_ge (h : IsRun p theta f x s sigma) {L : ℝ}
    (hf : HessianLipschitz f L) (k : ℕ) (hb : L / (1 - p.eta2) ≤ sigma k) :
    p.eta2 ≤ ratio f (x k) (s k) (sigma k) :=
  h.toTrialTrace.ratio_ge_of_sigma_ge hf k hb

/-- The common trial-trace bound applied to a model-residual run. -/
theorem IsRun.sigma_upper (h : IsRun p theta f x s sigma) {L : ℝ}
    (hf : HessianLipschitz f L) (n : ℕ) :
    sigma n ≤ max (sigma 0) (p.gamma3 * (L / (1 - p.eta2))) :=
  h.toTrialTrace.sigma_upper hf n

end Normed
section InnerProduct
variable [InnerProductSpace ℝ E]
variable {p : RegularizationParameters} {theta : ℝ} {f : E → ℝ}
    {x s : ℕ → E} {sigma : ℕ → ℝ}

/-- At the zero displacement, the actual model derivative is the objective derivative. -/
theorem fderiv_cubicModel_zero_of_contDiffAt {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (sigma : ℝ) :
    fderiv ℝ (cubicModel f x sigma) 0 = fderiv ℝ f x := by
  change fderiv ℝ (regularizedModel f 2 x sigma 6 3) 0 = _
  rw [fderiv_regularizedModel f 2 x 0 sigma 6 (by norm_num : (1 : ℝ) < 3),
    fderiv_taylorModel_eq_taylorModel_fderiv hf 0]
  rw [fderiv_norm_rpow (0 : E) (by norm_num : (1 : ℝ) < 3)]
  simp

/-- The cubic-model derivative agrees with the objective derivative at zero. -/
theorem fderiv_cubicModel_zero {L : ℝ} (hf : HessianLipschitz f L) (x : E) (sigma : ℝ) :
    fderiv ℝ (cubicModel f x sigma) 0 = fderiv ℝ f x :=
  fderiv_cubicModel_zero_of_contDiffAt hf.smooth.contDiffAt sigma

/-- A zero computed step can occur only at an exact first-order critical point. -/
theorem IsRun.fderiv_eq_zero_of_step_eq_zero (h : IsRun p theta f x s sigma) {L : ℝ}
    (hf : HessianLipschitz f L) (k : ℕ) (hs : s k = 0) : fderiv ℝ f (x k) = 0 := by
  have hr := h.residual k
  rw [hs, fderiv_cubicModel_zero hf] at hr
  simpa using hr

/-- Inexact model stationarity bounds the objective derivative at the trial point. -/
theorem IsRun.trial_derivative_bound (h : IsRun p theta f x s sigma) {L : ℝ}
    (hf : HessianLipschitz f L) (k : ℕ) :
    ‖fderiv ℝ f (x k + s k)‖ ≤ (L + theta + sigma k) / 2 * ‖s k‖ ^ 2 := by
  have hb := fderiv_step_lower_bound (p := 2) (beta := 1) (r := 3)
    (A := L / 2) (c := 6) (theta := theta / 2) (h.toRegularizationUpdates.pos k).le
    (by norm_num) (by norm_num)
    (by simpa using hf.derivative_remainder (x k) (s k))
    (by norm_num; exact h.residual k)
  norm_num at hb
  convert hb using 1
  ring

/-- An accepted trial gives the uniform step bound with the global parameter upper bound. -/
theorem IsRun.accepted_derivative_bound (h : IsRun p theta f x s sigma) {L : ℝ}
    (hf : HessianLipschitz f L) (k : ℕ)
    (hk : p.eta1 ≤ ratio f (x k) (s k) (sigma k)) :
    ‖fderiv ℝ f (x (k + 1))‖ ≤
      (L + theta + max (sigma 0) (p.gamma3 * (L / (1 - p.eta2)))) / 2 * ‖s k‖ ^ 2 := by
  rw [h.iterate k, ite_eq_left hk]
  exact (h.trial_derivative_bound hf k).trans
    (mul_le_mul_of_nonneg_right (by linarith [h.sigma_upper hf k]) (sq_nonneg _))

/-- Raising a quadratic step bound to the three-halves power produces cubic decrease. -/
theorem rpow_three_halves_le_cube {z a t : ℝ} (hz : 0 ≤ z) (ha : 0 ≤ a) (ht : 0 ≤ t)
    (h : z ≤ a * t ^ 2) : z ^ (3 / 2 : ℝ) ≤ a ^ (3 / 2 : ℝ) * t ^ 3 := by
  calc
    _ ≤ (a * t ^ 2) ^ (3 / 2 : ℝ) := Real.rpow_le_rpow hz h (by norm_num)
    _ = _ := by
      rw [Real.mul_rpow ha (sq_nonneg t), ← Real.rpow_natCast t 2,
        ← Real.rpow_mul ht]
      norm_num

/-- A successful trial before successor termination pays a uniform cubic-descent budget. -/
theorem IsRun.accepted_budget (h : IsRun p theta f x s sigma) {L epsilon a : ℝ}
    (hf : HessianLipschitz f L) (he : 0 < epsilon) (ha : 0 < a)
    (hA : (L + theta + max (sigma 0) (p.gamma3 * (L / (1 - p.eta2)))) / 2 ≤ a)
    (k : ℕ) (hk : p.eta1 ≤ ratio f (x k) (s k) (sigma k))
    (htest : epsilon < ‖fderiv ℝ f (x (k + 1))‖) :
    p.eta1 * p.sigmaMin / (6 * a ^ (3 / 2 : ℝ)) * epsilon ^ (3 / 2 : ℝ) ≤
      f (x k) - f (x (k + 1)) := by
  have hstep : epsilon ≤ a * ‖s k‖ ^ 2 := htest.le.trans
    ((h.accepted_derivative_bound hf k hk).trans
      (mul_le_mul_of_nonneg_right hA (sq_nonneg _)))
  have hc := rpow_three_halves_le_cube he.le ha.le (norm_nonneg (s k)) hstep
  have hpaid := h.accepted_cubic_decrease k hk
  have ha' := Real.rpow_pos_of_pos ha (3 / 2 : ℝ)
  calc
    _ = (p.eta1 * p.sigmaMin / 6) * (epsilon ^ (3 / 2 : ℝ) / a ^ (3 / 2 : ℝ)) := by field_simp
    _ ≤ (p.eta1 * p.sigmaMin / 6) * ‖s k‖ ^ 3 := by
      exact mul_le_mul_of_nonneg_left ((div_le_iff₀ ha').mpr (by simpa [mul_comm] using hc))
        (div_nonneg (mul_nonneg p.eta1_pos.le p.sigmaMin_pos.le) (by norm_num))
    _ ≤ _ := hpaid

/-- Successful iterations before successor termination are counted by telescoping actual values. -/
theorem IsRun.success_count_le (h : IsRun p theta f x s sigma) {L epsilon a low : ℝ}
    (hf : HessianLipschitz f L) (he : 0 < epsilon) (ha : 0 < a)
    (hA : (L + theta + max (sigma 0) (p.gamma3 * (L / (1 - p.eta2)))) / 2 ≤ a)
    (n : ℕ) (hlow : low ≤ f (x n))
    (htest : ∀ j ≤ n, epsilon < ‖fderiv ℝ f (x j)‖) :
    (successCount (fun k => p.eta1 ≤ ratio f (x k) (s k) (sigma k)) n : ℝ) ≤
      6 * a ^ (3 / 2 : ℝ) / (p.eta1 * p.sigmaMin) *
        ((f (x 0) - low) / epsilon ^ (3 / 2 : ℝ)) := by
  have hdelta : 0 < p.eta1 * p.sigmaMin / (6 * a ^ (3 / 2 : ℝ)) * epsilon ^ (3 / 2 : ℝ) :=
    mul_pos (div_pos (mul_pos p.eta1_pos p.sigmaMin_pos)
      (mul_pos (by norm_num) (Real.rpow_pos_of_pos ha _))) (Real.rpow_pos_of_pos he _)
  have hb := successCount_le_of_successor_decrease
    (P := fun k => ‖fderiv ℝ f (x k)‖ ≤ epsilon)
    (fun k => p.eta1 ≤ ratio f (x k) (s k) (sigma k)) hdelta h.objective_nonincrease
    (fun k hk ht => h.accepted_budget hf he ha hA k hk (lt_of_not_ge ht)) n hlow
    (fun j hj => not_le.mpr (htest j hj))
  convert hb using 1
  field_simp

/-- Before the first successful test at most one accepted step has an untested successor. -/
theorem IsRun.success_count_before_test (h : IsRun p theta f x s sigma) {L epsilon a low : ℝ}
    (hf : HessianLipschitz f L) (he : 0 < epsilon) (ha : 0 < a)
    (hA : (L + theta + max (sigma 0) (p.gamma3 * (L / (1 - p.eta2)))) / 2 ≤ a)
    (hlow : ∀ y, low ≤ f y) (n : ℕ)
    (htest : ∀ j < n, epsilon < ‖fderiv ℝ f (x j)‖) :
    (successCount (fun k => p.eta1 ≤ ratio f (x k) (s k) (sigma k)) n : ℝ) ≤
      6 * a ^ (3 / 2 : ℝ) / (p.eta1 * p.sigmaMin) *
        ((f (x 0) - low) / epsilon ^ (3 / 2 : ℝ)) + 1 := by
  have hdelta : 0 < p.eta1 * p.sigmaMin / (6 * a ^ (3 / 2 : ℝ)) * epsilon ^ (3 / 2 : ℝ) :=
    mul_pos (div_pos (mul_pos p.eta1_pos p.sigmaMin_pos)
      (mul_pos (by norm_num) (Real.rpow_pos_of_pos ha _))) (Real.rpow_pos_of_pos he _)
  have hb := successCount_before_test_le_of_successor_decrease
    (P := fun k => ‖fderiv ℝ f (x k)‖ ≤ epsilon)
    (fun k => p.eta1 ≤ ratio f (x k) (s k) (sigma k)) hdelta (fun k => hlow (x k))
    h.objective_nonincrease
    (fun k hk ht => h.accepted_budget hf he ha hA k hk (lt_of_not_ge ht)) n
    (fun j hj => not_le.mpr (htest j hj))
  convert hb using 1
  field_simp

/-- Actual derivative termination with all function and derivative evaluations counted.
The extra accepted step accounts for the use of successor criticality in the cubic bound. -/
theorem IsRun.exists_stationary_with_cost (h : IsRun p theta f x s sigma) {L epsilon a low : ℝ}
    (hf : HessianLipschitz f L) (he : 0 < epsilon) (ha : 0 < a)
    (hA : (L + theta + max (sigma 0) (p.gamma3 * (L / (1 - p.eta2)))) / 2 ≤ a)
    (hlow : ∀ y, low ≤ f y) :
    let M := max (sigma 0) (p.gamma3 * (L / (1 - p.eta2)))
    let C := 1 + |Real.log p.gamma1| / Real.log p.gamma2
    let D := Real.log (M / sigma 0) / Real.log p.gamma2
    let B := 6 * a ^ (3 / 2 : ℝ) / (p.eta1 * p.sigmaMin) *
      ((f (x 0) - low) / epsilon ^ (3 / 2 : ℝ))
    ∃ K : ℕ, ‖fderiv ℝ f (x K)‖ ≤ epsilon ∧
      (∀ j < K, epsilon < ‖fderiv ℝ f (x j)‖) ∧
      (K : ℝ) + 1 ≤ C * B + C + D + 1 ∧
      (successCount (fun k => p.eta1 ≤ ratio f (x k) (s k) (sigma k)) K : ℝ) + 1 ≤ B + 2 := by
  have hdelta : 0 < p.eta1 * p.sigmaMin / (6 * a ^ (3 / 2 : ℝ)) * epsilon ^ (3 / 2 : ℝ) :=
    mul_pos (div_pos (mul_pos p.eta1_pos p.sigmaMin_pos)
      (mul_pos (by norm_num) (Real.rpow_pos_of_pos ha _))) (Real.rpow_pos_of_pos he _)
  have hb := h.toRegularizationUpdates.exists_first_with_cost
    (P := fun k => ‖fderiv ℝ f (x k)‖ ≤ epsilon)
    (h.sigma_upper hf) hdelta (fun k => hlow (x k)) h.objective_nonincrease
    (fun k hk ht => h.accepted_budget hf he ha hA k hk (lt_of_not_ge ht))
  have hid : (f (x 0) - low) /
      (p.eta1 * p.sigmaMin / (6 * a ^ (3 / 2 : ℝ)) * epsilon ^ (3 / 2 : ℝ)) =
      6 * a ^ (3 / 2 : ℝ) / (p.eta1 * p.sigmaMin) *
        ((f (x 0) - low) / epsilon ^ (3 / 2 : ℝ)) := by field_simp
  simpa only [hid, not_le] using hb

end InnerProduct

end Optimization.CubicRegularization
