import Numlib.Optimization.CubicRegularization
import Numlib.Optimization.AdaptiveRegularizationComplexity
import Numlib.Optimization.RegularizedTaylorCurvature
import Numlib.Optimization.HessianCurvature

/-!
# Second-order cubic regularization

A lawful cubic trace can impose a lower quadratic bound on the genuine model Hessian.
That bound transfers to the objective and yields both curvature step estimates and a
joint first- and second-order evaluation budget.
-/
noncomputable section
namespace Optimization.CubicRegularization
open ParameterUpdates RegularizedTaylorModel
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A joint approximate first- and second-order criticality test. -/
def SecondOrderStationary (f : E → ℝ) (epsilon1 epsilon2 : ℝ) (y : E) : Prop :=
  ‖fderiv ℝ f y‖ ≤ epsilon1 ∧
    ∀ u : E, -epsilon2 * ‖u‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ f) y u u

/-- A cubic trace satisfying the actual model Hessian lower-curvature residual. -/
structure SecondOrderRun (p : RegularizationParameters) (theta1 theta2 : ℝ) (f : E → ℝ)
    (x s : ℕ → E) (sigma : ℕ → ℝ) : Prop extends IsRun p theta1 f x s sigma where
  curvature : ∀ k u, -(theta2 * ‖s k‖) * ‖u‖ ^ 2 ≤
    fderiv ℝ (fderiv ℝ (cubicModel f (x k) (sigma k))) (s k) u u

variable {p : RegularizationParameters} {theta1 theta2 : ℝ} {f : E → ℝ}
    {x s : ℕ → E} {sigma : ℕ → ℝ}

/-- The tensor Hessian Lipschitz hypothesis also bounds its curried representation. -/
theorem HessianLipschitz.curried_bound {L : ℝ} (hf : HessianLipschitz f L) (x y : E) :
    ‖fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) y‖ ≤ L * ‖x - y‖ := by
  have h := hf.bound x y
  rw [norm_iteratedFDeriv_sub_eq_fderiv_sub, norm_iteratedFDeriv_sub_eq_fderiv_sub,
    norm_iteratedFDeriv_zero_sub] at h
  exact h

/-- Every accepted trial inherits the uniform lower-curvature bound. -/
theorem SecondOrderRun.accepted_curvature_bound (h : SecondOrderRun p theta1 theta2 f x s sigma)
    {L : ℝ} (hf : HessianLipschitz f L) (k : ℕ)
    (hk : p.eta1 ≤ ratio f (x k) (s k) (sigma k)) (u : E) :
    -((L + max (sigma 0) (p.gamma3 * (L / (1 - p.eta2))) + theta2) * ‖s k‖) *
      ‖u‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ f) (x (k + 1)) u u := by
  rw [h.iterate k, ite_eq_left hk]
  have hb := cubic_curvature_step_lower_bound_of_lipschitz
    (h.toIsRun.toRegularizationUpdates.pos k).le (hf.smooth.contDiffAt (x := x k))
    (by simpa using hf.curried_bound (x k + s k) (x k)) (h.curvature k u)
  have hM := h.toIsRun.sigma_upper hf k
  have hm := mul_le_mul_of_nonneg_right hM (norm_nonneg (s k))
  have hm' := mul_le_mul_of_nonneg_right hm (sq_nonneg ‖u‖)
  nlinarith

/-- Zero steps are unused continuations only at exact second-order stationary points. -/
theorem SecondOrderRun.stationary_of_step_eq_zero (h : SecondOrderRun p theta1 theta2 f x s sigma)
    {L : ℝ} (hf : HessianLipschitz f L) (k : ℕ) (hs : s k = 0) :
    SecondOrderStationary f 0 0 (x k) := by
  refine ⟨by simp [h.toIsRun.fderiv_eq_zero_of_step_eq_zero hf k hs], ?_⟩
  intro u
  have hc := h.curvature k u
  rw [hs] at hc
  change -(theta2 * ‖(0 : E)‖) * ‖u‖ ^ 2 ≤
    fderiv ℝ (fderiv ℝ (regularizedModel f 2 (x k) (sigma k) 6 3)) 0 u u at hc
  rw [hessian_regularizedModel _ _ _ _ _ _ (by norm_num : (2 : ℝ) < 3),
    hessian_taylorModel_two (hf.smooth.contDiffAt (x := x k)),
    normRpowHessian_zero 3 (by norm_num)] at hc
  simpa using hc

/-- The least-curvature form of the accepted cubic step estimate. -/
theorem SecondOrderRun.accepted_leastCurvature_bound [Nontrivial E]
    (h : SecondOrderRun p theta1 theta2 f x s sigma) {L : ℝ}
    (hf : HessianLipschitz f L) (k : ℕ)
    (hk : p.eta1 ≤ ratio f (x k) (s k) (sigma k)) :
    -((L + max (sigma 0) (p.gamma3 * (L / (1 - p.eta2))) + theta2) * ‖s k‖) ≤
      leastCurvature (fderiv ℝ (fderiv ℝ f) (x (k + 1))) :=
  (le_leastCurvature_iff _ _).mpr (h.accepted_curvature_bound hf k hk)

/-- Negative least curvature at an accepted successor forces a positive step length. -/
theorem SecondOrderRun.step_norm_lower_bound [Nontrivial E]
    (h : SecondOrderRun p theta1 theta2 f x s sigma) {L : ℝ}
    (hf : HessianLipschitz f L) (htheta2 : 0 ≤ theta2) (k : ℕ)
    (hk : p.eta1 ≤ ratio f (x k) (s k) (sigma k))
    (hneg : leastCurvature (fderiv ℝ (fderiv ℝ f) (x (k + 1))) < 0) :
    |leastCurvature (fderiv ℝ (fderiv ℝ f) (x (k + 1)))| /
      (L + max (sigma 0) (p.gamma3 * (L / (1 - p.eta2))) + theta2) ≤ ‖s k‖ := by
  have hM : 0 < max (sigma 0) (p.gamma3 * (L / (1 - p.eta2))) :=
    (h.toIsRun.toRegularizationUpdates.pos 0).trans_le (h.toIsRun.sigma_upper hf 0)
  have hden : 0 < L + max (sigma 0) (p.gamma3 * (L / (1 - p.eta2))) + theta2 := by
    linarith [hf.nonneg]
  rw [div_le_iff₀ hden, abs_of_neg hneg]
  linarith [h.accepted_leastCurvature_bound hf k hk]

/-- Failure of either successor test forces a cubic step budget. -/
theorem SecondOrderRun.accepted_joint_budget
    (h : SecondOrderRun p theta1 theta2 f x s sigma) {L epsilon1 epsilon2 B : ℝ}
    (hf : HessianLipschitz f L) (he1 : 0 < epsilon1) (he2 : 0 < epsilon2) (hB : 0 < B)
    (hA : (L + theta1 + max (sigma 0) (p.gamma3 * (L / (1 - p.eta2)))) / 2 ≤ B ^ 2)
    (hC : L + max (sigma 0) (p.gamma3 * (L / (1 - p.eta2))) + theta2 ≤ B)
    (k : ℕ) (hk : p.eta1 ≤ ratio f (x k) (s k) (sigma k))
    (htest : ¬SecondOrderStationary f epsilon1 epsilon2 (x (k + 1))) :
    p.eta1 * p.sigmaMin / (6 * B ^ 3) * min (epsilon1 ^ (3 / 2 : ℝ)) (epsilon2 ^ 3) ≤
      f (x k) - f (x (k + 1)) := by
  have hstep : min (epsilon1 ^ (3 / 2 : ℝ)) (epsilon2 ^ 3) ≤ B ^ 3 * ‖s k‖ ^ 3 := by
    by_cases hg : ‖fderiv ℝ f (x (k + 1))‖ ≤ epsilon1
    · have hu : ∃ u, fderiv ℝ (fderiv ℝ f) (x (k + 1)) u u < -epsilon2 * ‖u‖ ^ 2 := by
        by_contra! hu
        exact htest ⟨hg, hu⟩
      obtain ⟨u, hu⟩ := hu
      have hb := h.accepted_curvature_bound hf k hk u
      have hn : 0 < ‖u‖ ^ 2 := by
        by_contra! hn
        have hz : u = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg u])
        simp [hz] at hu
      have hlen : epsilon2 ≤ B * ‖s k‖ := by
        have hc := mul_le_mul_of_nonneg_right hC (norm_nonneg (s k))
        have hh : epsilon2 <
            (L + max (sigma 0) (p.gamma3 * (L / (1 - p.eta2))) + theta2) * ‖s k‖ := by
          nlinarith
        linarith
      calc
        _ ≤ epsilon2 ^ 3 := min_le_right _ _
        _ ≤ (B * ‖s k‖) ^ 3 := pow_le_pow_left₀ he2.le hlen _
        _ = _ := by ring
    · have hg' : epsilon1 ≤ B ^ 2 * ‖s k‖ ^ 2 :=
        (lt_of_not_ge hg).le.trans ((h.toIsRun.accepted_derivative_bound hf k hk).trans
          (mul_le_mul_of_nonneg_right hA (sq_nonneg _)))
      have hp : (B ^ 2) ^ (3 / 2 : ℝ) = B ^ 3 := by
        rw [← Real.rpow_natCast B 2, ← Real.rpow_mul hB.le]
        norm_num
      have hb := rpow_three_halves_le_cube he1.le (sq_nonneg B) (norm_nonneg (s k)) hg'
      rw [hp] at hb
      exact (min_le_left _ _).trans hb
  have hpaid := h.toIsRun.accepted_cubic_decrease k hk
  calc
    _ = (p.eta1 * p.sigmaMin / 6) *
        (min (epsilon1 ^ (3 / 2 : ℝ)) (epsilon2 ^ 3) / B ^ 3) := by ring
    _ ≤ (p.eta1 * p.sigmaMin / 6) * ‖s k‖ ^ 3 := by
      exact mul_le_mul_of_nonneg_left
        ((div_le_iff₀ (pow_pos hB 3)).mpr (by simpa [mul_comm] using hstep))
        (div_nonneg (mul_nonneg p.eta1_pos.le p.sigmaMin_pos.le) (by norm_num))
    _ ≤ _ := hpaid

/-- The joint curvature and derivative stopping test has the expected cubic evaluation budget. -/
theorem SecondOrderRun.exists_stationary_with_cost
    (h : SecondOrderRun p theta1 theta2 f x s sigma) {L epsilon1 epsilon2 B low : ℝ}
    (hf : HessianLipschitz f L) (he1 : 0 < epsilon1) (he2 : 0 < epsilon2) (hB : 0 < B)
    (hA : (L + theta1 + max (sigma 0) (p.gamma3 * (L / (1 - p.eta2)))) / 2 ≤ B ^ 2)
    (hC : L + max (sigma 0) (p.gamma3 * (L / (1 - p.eta2))) + theta2 ≤ B)
    (hlow : ∀ y, low ≤ f y) :
    let M := max (sigma 0) (p.gamma3 * (L / (1 - p.eta2)))
    let C := 1 + |Real.log p.gamma1| / Real.log p.gamma2
    let D := Real.log (M / sigma 0) / Real.log p.gamma2
    let Q := 6 * B ^ 3 / (p.eta1 * p.sigmaMin) *
      ((f (x 0) - low) / min (epsilon1 ^ (3 / 2 : ℝ)) (epsilon2 ^ 3))
    ∃ K : ℕ, SecondOrderStationary f epsilon1 epsilon2 (x K) ∧
      (∀ j < K, ¬SecondOrderStationary f epsilon1 epsilon2 (x j)) ∧
      (K : ℝ) + 1 ≤ C * Q + C + D + 1 ∧
      (successCount (fun k => p.eta1 ≤ ratio f (x k) (s k) (sigma k)) K : ℝ) + 1 ≤ Q + 2 := by
  have hmin : 0 < min (epsilon1 ^ (3 / 2 : ℝ)) (epsilon2 ^ 3) :=
    lt_min (Real.rpow_pos_of_pos he1 _) (pow_pos he2 _)
  have hdelta : 0 < p.eta1 * p.sigmaMin / (6 * B ^ 3) *
      min (epsilon1 ^ (3 / 2 : ℝ)) (epsilon2 ^ 3) :=
    mul_pos (div_pos (mul_pos p.eta1_pos p.sigmaMin_pos) (by positivity)) hmin
  have hb := h.toIsRun.toRegularizationUpdates.exists_first_with_cost
    (P := fun k => SecondOrderStationary f epsilon1 epsilon2 (x k))
    (h.toIsRun.sigma_upper hf) hdelta (fun k => hlow (x k)) h.toIsRun.objective_nonincrease
    (h.accepted_joint_budget hf he1 he2 hB hA hC)
  have hid : (f (x 0) - low) /
      (p.eta1 * p.sigmaMin / (6 * B ^ 3) * min (epsilon1 ^ (3 / 2 : ℝ)) (epsilon2 ^ 3)) =
      6 * B ^ 3 / (p.eta1 * p.sigmaMin) *
        ((f (x 0) - low) / min (epsilon1 ^ (3 / 2 : ℝ)) (epsilon2 ^ 3)) := by field_simp
  simpa only [hid] using hb

/-- The alternate cubic trace with the unregularized Taylor derivative stopping rule. -/
structure ModifiedRun (p : RegularizationParameters) (theta : ℝ) (f : E → ℝ)
    (x s : ℕ → E) (sigma : ℕ → ℝ) : Prop extends TrialTrace p f x s sigma where
  residual : ∀ k, ‖fderiv ℝ (taylorModel f 2 (x k)) (s k)‖ ≤
    theta * sigma k / 2 * ‖s k‖ ^ 2

/-- The alternative Taylor derivative residual yields its sharper uniform derivative bound. -/
theorem ModifiedRun.accepted_derivative_bound {theta : ℝ}
    (h : ModifiedRun p theta f x s sigma) {L : ℝ} (hf : HessianLipschitz f L)
    (htheta : 0 ≤ theta) (k : ℕ) (hk : p.eta1 ≤ ratio f (x k) (s k) (sigma k)) :
    ‖fderiv ℝ f (x (k + 1))‖ ≤
      (L + theta * max (sigma 0) (p.gamma3 * (L / (1 - p.eta2)))) / 2 * ‖s k‖ ^ 2 := by
  rw [h.iterate k, ite_eq_left hk]
  have hb := hf.derivative_remainder (x k) (s k)
  have hr := h.residual k
  have hM := h.toTrialTrace.sigma_upper hf k
  have hm := mul_le_mul_of_nonneg_left hM htheta
  have hm' := mul_le_mul_of_nonneg_right hm (sq_nonneg ‖s k‖)
  have hn := norm_le_norm_sub_add (fderiv ℝ f (x k + s k))
    (fderiv ℝ (taylorModel f 2 (x k)) (s k))
  nlinarith

end Optimization.CubicRegularization
