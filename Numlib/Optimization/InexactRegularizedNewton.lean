import Numlib.Optimization.InexactNewton
import Numlib.Optimization.ParameterUpdatesFinite

/-!
# Inexact regularized Newton trials

Quadratically shifted Taylor steps, cubic actual-decrease acceptance, and adaptive lower and
upper multiplier intervals. Curvature is certified only in the chosen isometrically embedded
subspace. Finite prefixes encode local algorithm laws without assuming termination.
-/
noncomputable section
namespace Optimization.InexactRegularizedNewton
open InnerProductSpace
variable {E V : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Algorithm constants, independent of the stopping tolerances. -/
structure Parameters where
  eta : ℝ
  gamma1 : ℝ
  gamma2 : ℝ
  sigmaMin : ℝ
  sigmaMax : ℝ
  kappa1 : ℝ
  kappa2 : ℝ
  kappa3 : ℝ
  kappa4 : ℝ
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  one_lt_gamma1 : 1 < gamma1
  gamma_le : gamma1 ≤ gamma2
  sigmaMin_pos : 0 < sigmaMin
  sigma_le : sigmaMin ≤ sigmaMax
  kappa1_pos : 0 < kappa1
  kappa2_pos : 0 < kappa2
  kappa3_pos : 0 < kappa3
  kappa4_pos : 0 < kappa4

/-- The quadratic Taylor model plus a quadratic shift. -/
def model (f : E → ℝ) (x : E) (lambda : ℝ) (s : E) : ℝ :=
  RegularizedTaylorModel.taylorModel f 2 x s + lambda / 2 * ‖s‖ ^ 2

/-- The shifted Newton model gradient, using the actual objective derivatives. -/
def residual (f : E → ℝ) (x s : E) (lambda : ℝ) : E :=
  gradient f x + TrustRegionSecondOrder.hessianOperator f x s + lambda • s

omit [CompleteSpace E] in
/-- The genuine derivative of the shifted quadratic model. -/
theorem fderiv_model (f : E → ℝ) (x s : E) (lambda : ℝ)
    (hf : ContDiffAt ℝ 2 f x) :
    fderiv ℝ (model f x lambda) s = fderiv ℝ f x +
      fderiv ℝ (fderiv ℝ f) x s + lambda • innerSL ℝ s := by
  have hT := (RegularizedTaylorModel.hasFDerivAt_taylorModel f 2 x s).differentiableAt
  have hn := ((hasFDerivAt_id s).norm_sq).const_mul (lambda / 2)
  have hd := (hT.hasFDerivAt.add hn).fderiv
  change fderiv ℝ (model f x lambda) s = _ at hd
  rw [hd, RegularizedTaylorModel.fderiv_taylorModel_eq_taylorModel_fderiv
    (p := 1) hf, RegularizedTaylorModel.taylorModel_one]
  ext u
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, id_eq, smul_eq_mul]
  ring

/-- The residual vector is exactly the actual model gradient. -/
theorem gradient_model (f : E → ℝ) (x s : E) (lambda : ℝ)
    (hf : ContDiffAt ℝ 2 f x) : gradient (model f x lambda) s = residual f x s lambda := by
  apply (toDual ℝ E).injective
  rw [toDual_gradient, fderiv_model f x s lambda hf]
  ext u
  simp only [residual, map_add, map_smul, add_apply,
    smul_apply, toDual_apply_apply]
  rw [TrustRegionSecondOrder.hessianOperator, continuousLinearMapOfBilin_apply,
    ← toDual_apply_apply, toDual_gradient]
  rfl

omit [CompleteSpace E] in
/-- The genuine Hessian of the shifted model is the objective Hessian plus the shift identity. -/
theorem hessian_model (f : E → ℝ) (x s : E) (lambda : ℝ)
    (hf : ContDiffAt ℝ 2 f x) :
    fderiv ℝ (fderiv ℝ (model f x lambda)) s =
      fderiv ℝ (fderiv ℝ f) x + lambda • ((innerSL ℝ).restrictScalars ℝ : E →L[ℝ] E →L[ℝ] ℝ) := by
  have he : fderiv ℝ (model f x lambda) = fun z =>
      fderiv ℝ f x + (fderiv ℝ (fderiv ℝ f) x +
        lambda • ((innerSL ℝ).restrictScalars ℝ : E →L[ℝ] E →L[ℝ] ℝ)) z := by
    funext z
    simpa [add_assoc] using fderiv_model f x z lambda hf
  rw [he, fderiv_const_add, ContinuousLinearMap.fderiv]

/-- The objective Hessian restricted to an orthonormal subspace basis. -/
def projectedHessian (f : E → ℝ) (x : E) (Q : V →ₗᵢ[ℝ] E) : V →L[ℝ] V →L[ℝ] ℝ :=
  (fderiv ℝ (fderiv ℝ f) x).bilinearComp Q.toContinuousLinearMap Q.toContinuousLinearMap

/-- Least objective curvature within the chosen orthonormal subspace. -/
def projectedCurvature (f : E → ℝ) (x : E) (Q : V →ₗᵢ[ℝ] E) : ℝ :=
  leastCurvature (projectedHessian f x Q)

omit [CompleteSpace E] in
/-- Evaluation of the actual objective Hessian in subspace coordinates. -/
@[simp] theorem projectedHessian_apply (f : E → ℝ) (x : E) (Q : V →ₗᵢ[ℝ] E) (u v : V) :
    projectedHessian f x Q u v = fderiv ℝ (fderiv ℝ f) x (Q u) (Q v) := rfl

omit [CompleteSpace E] in
/-- The genuine shifted model Hessian, evaluated along the orthonormal subspace basis. -/
theorem projected_model_hessian (f : E → ℝ) (x s : E) (lambda : ℝ)
    (Q : V →ₗᵢ[ℝ] E) (hf : ContDiffAt ℝ 2 f x) (u : V) :
    fderiv ℝ (fderiv ℝ (model f x lambda)) s (Q u) (Q u) =
      projectedHessian f x Q u u + lambda * ‖u‖ ^ 2 := by
  rw [hessian_model f x s lambda hf]
  change fderiv ℝ (fderiv ℝ f) x (Q u) (Q u) + lambda * inner ℝ (Q u) (Q u) = _
  rw [real_inner_self_eq_norm_sq, Q.norm_map]
  rfl

omit [CompleteSpace E] in
/-- A spanning orthonormal subspace certifies the full objective curvature. -/
theorem projectedCurvature_eq_of_surjective [Nontrivial E] [Nontrivial V]
    (f : E → ℝ) (x : E) (Q : V →ₗᵢ[ℝ] E) (hQ : Function.Surjective Q) :
    projectedCurvature f x Q = TrustRegionSecondOrder.curvature f x := by
  apply le_antisymm
  · apply (le_leastCurvature_iff _ _).mpr
    intro u
    obtain ⟨v, rfl⟩ := hQ u
    have hh := (le_leastCurvature_iff (projectedHessian f x Q)
      (projectedCurvature f x Q)).mp le_rfl v
    simpa only [Q.norm_map, projectedHessian_apply] using hh
  · apply (le_leastCurvature_iff _ _).mpr
    intro u
    have hh := (le_leastCurvature_iff (fderiv ℝ (fderiv ℝ f) x)
      (TrustRegionSecondOrder.curvature f x)).mp le_rfl (Q u)
    simpa only [Q.norm_map, projectedHessian_apply] using hh

/-- Exact model-step conditions: feasibility, both slope tests, the complete model-gradient
residual test, and the optional projected shifted-Hessian lower bound. -/
structure IsStep (p : Parameters) (second : Bool) (f : E → ℝ) (x s : E)
    (lambda lower upper : ℝ) (Q : V →ₗᵢ[ℝ] E) : Prop where
  lower_nonneg : 0 ≤ lower
  feasible_lower : lower * ‖s‖ ≤ lambda
  feasible_upper : lambda ≤ upper * ‖s‖
  slope_linear : inner ℝ s (residual f x s lambda) ≤ p.kappa1 * ‖s‖ ^ 2
  slope_quadratic : inner ℝ s (residual f x s lambda) ≤
    1 / 2 * (fderiv ℝ (fderiv ℝ f) x s s + lambda * ‖s‖ ^ 2) +
      1 / 2 * p.kappa2 * ‖s‖ ^ 3
  norm_residual : ‖residual f x s lambda‖ ≤ lambda * ‖s‖ + p.kappa3 * ‖s‖ ^ 2
  curvature : second = true → ∀ u : V,
    -(p.kappa4 * ‖s‖) * ‖u‖ ^ 2 ≤
      projectedHessian f x Q u u + lambda * ‖u‖ ^ 2

/-- The objective reduction per cubed step norm. -/
def ratio (f : E → ℝ) (x s : E) : ℝ := (f x - f (x + s)) / ‖s‖ ^ 3

open Classical in
/-- Exact accepted/reset/growth interval update. -/
def IntervalUpdate (p : Parameters) (accepted : Prop)
    (t lambda lowerNext upperNext upper : ℝ) : Prop :=
  if accepted then lowerNext = 0 ∧ upperNext = upper
  else if lambda < p.sigmaMin * t then
    lowerNext ∈ Set.Icc p.sigmaMin p.sigmaMax ∧ upperNext ∈ Set.Icc lowerNext p.sigmaMax
  else lowerNext = p.gamma1 * (lambda / t) ∧ upperNext = p.gamma2 * (lambda / t)

/-- A finite executable prefix, with no stopping assertion or complexity assumption. -/
structure TrialTrace (p : Parameters) (second : Bool) (f : E → ℝ) (x s : ℕ → E)
    (lambda lower upper : ℕ → ℝ) (Q : ℕ → V →ₗᵢ[ℝ] E) (N : ℕ) : Prop where
  initial_lower : lower 0 = 0
  initial_upper : upper 0 ∈ Set.Icc p.sigmaMin p.sigmaMax
  nonzero : ∀ k < N, s k ≠ 0
  step : ∀ k < N, IsStep p second f (x k) (s k) (lambda k) (lower k) (upper k) (Q k)
  iterate : ∀ k < N, x (k + 1) = if p.eta ≤ ratio f (x k) (s k) then x k + s k else x k
  update : ∀ k < N, IntervalUpdate p (p.eta ≤ ratio f (x k) (s k))
    ‖s k‖ (lambda k) (lower (k + 1)) (upper (k + 1)) (upper k)

variable {p : Parameters} {second : Bool} {f : E → ℝ} {x s : E}
  {lambda lower upper L M : ℝ} {Q : V →ₗᵢ[ℝ] E}

/-- At a stationary point with nonnegative selected curvature, the zero terminal model
step satisfies every residual and slope condition. Nonzero steps are required only for
executed trials, where the cubic acceptance ratio is evaluated. -/
theorem IsStep.zero (p : Parameters) (second : Bool) (f : E → ℝ) (x : E)
    (lower upper : ℝ) (Q : V →ₗᵢ[ℝ] E) (hl : 0 ≤ lower) (hg : gradient f x = 0)
    (hc : second = true → ∀ u : V, 0 ≤ projectedHessian f x Q u u) :
    IsStep p second f x 0 0 lower upper Q := by
  refine ⟨hl, by simp, by simp, ?_, ?_, ?_, ?_⟩
  · simp [residual, hg]
  · simp [residual, hg]
  · simp [residual, hg]
  · intro hs u
    simpa using hc hs u

/-- The lower interval enforces a nonnegative shift. -/
theorem IsStep.shift_nonneg (h : IsStep p second f x s lambda lower upper Q) : 0 ≤ lambda :=
  (mul_nonneg h.lower_nonneg (norm_nonneg _)).trans h.feasible_lower

/-- The slope condition pays for half the shift, up to the cubic residual. -/
theorem IsStep.taylor_decrease (h : IsStep p second f x s lambda lower upper Q) :
    lambda / 2 * ‖s‖ ^ 2 - p.kappa2 / 2 * ‖s‖ ^ 3 ≤
      f x - RegularizedTaylorModel.taylorModel f 2 x s := by
  have hh := h.slope_quadratic
  have hi : inner ℝ s (residual f x s lambda) =
      inner ℝ (gradient f x) s + fderiv ℝ (fderiv ℝ f) x s s + lambda * ‖s‖ ^ 2 := by
    simp only [residual, inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
    conv_lhs => rw [real_inner_comm (gradient f x) s, real_inner_comm
      (TrustRegionSecondOrder.hessianOperator f x s) s]
    rw [TrustRegionSecondOrder.hessianOperator, continuousLinearMapOfBilin_apply]
  rw [hi] at hh
  rw [TrustRegionSecondOrder.taylorModel_eq]
  simp only [QuadraticSubproblem.quadratic]
  have hi' : inner ℝ s (TrustRegionSecondOrder.hessianOperator f x s) =
      fderiv ℝ (fderiv ℝ f) x s s := by
    rw [real_inner_comm, TrustRegionSecondOrder.hessianOperator, continuousLinearMapOfBilin_apply]
  rw [hi']
  linarith

/-- A sufficiently large multiplier guarantees actual cubic-decrease acceptance. -/
theorem IsStep.accepted_of_shift (h : IsStep p second f x s lambda lower upper Q)
    (hs : s ≠ 0) (hf : CubicRegularization.HessianLipschitz f L)
    (hl : (2 * p.eta + p.kappa2 + L) * ‖s‖ ≤ lambda) : p.eta ≤ ratio f x s := by
  rw [ratio, le_div_iff₀ (pow_pos (norm_pos_iff.mpr hs) _)]
  have ht := (abs_le.mp (hf.value_remainder x s)).2
  have hd := h.taylor_decrease
  have hs := mul_le_mul_of_nonneg_right hl (sq_nonneg ‖s‖)
  have hn : 0 ≤ L * ‖s‖ ^ 3 := mul_nonneg hf.nonneg (pow_nonneg (norm_nonneg _) _)
  nlinarith only [ht, hd, hs, hn]

/-- The complete residual test controls the next objective gradient quadratically. -/
theorem IsStep.trial_gradient_le (h : IsStep p second f x s lambda lower upper Q)
    (hf : CubicRegularization.HessianLipschitz f L) (hu : upper ≤ M) :
    ‖gradient f (x + s)‖ ≤ (L / 2 + 2 * M + p.kappa3) * ‖s‖ ^ 2 := by
  have hr := InexactNewton.gradient_remainder hf x s
  have he : gradient f x + TrustRegionSecondOrder.hessianOperator f x s =
      residual f x s lambda - lambda • s := by unfold residual; abel
  rw [he] at hr
  have hn := norm_le_norm_sub_add (gradient f (x + s)) (residual f x s lambda - lambda • s)
  have hn' := norm_sub_le (residual f x s lambda) (lambda • s)
  rw [norm_smul, Real.norm_of_nonneg h.shift_nonneg] at hn'
  have hl := h.feasible_upper.trans (mul_le_mul_of_nonneg_right hu (norm_nonneg s))
  have hl' := mul_le_mul_of_nonneg_right hl (norm_nonneg s)
  nlinarith only [hr, hn, hn', h.norm_residual, hl']

/-- The projected shifted-Hessian test yields current projected objective curvature control. -/
theorem IsStep.projected_curvature_ge [Nontrivial V]
    (h : IsStep p second f x s lambda lower upper Q) (hsecond : second = true) (hu : upper ≤ M) :
    -(p.kappa4 + M) * ‖s‖ ≤ projectedCurvature f x Q := by
  apply (le_leastCurvature_iff _ _).mpr
  intro u
  have hh := h.curvature hsecond u
  have hl := h.feasible_upper.trans (mul_le_mul_of_nonneg_right hu (norm_nonneg s))
  have hl' := mul_le_mul_of_nonneg_right hl (sq_nonneg ‖u‖)
  nlinarith only [hh, hl']

/-- A uniform upper regularization constant independent of the stopping tolerances. -/
def upperBound (p : Parameters) (L : ℝ) : ℝ :=
  max p.sigmaMax (p.gamma2 * (2 * p.eta + p.kappa2 + L))

variable {x s : ℕ → E} {lambda lower upper : ℕ → ℝ}
  {Q : ℕ → V →ₗᵢ[ℝ] E} {N : ℕ}

/-- Every upper interval through a finite prefix obeys the uniform multiplier bound. -/
theorem TrialTrace.upper_le (h : TrialTrace p second f x s lambda lower upper Q N)
    (hf : CubicRegularization.HessianLipschitz f L) {k : ℕ} (hk : k ≤ N) :
    upper k ≤ upperBound p L := by
  induction k with
  | zero => exact h.initial_upper.2.trans (le_max_left _ _)
  | succ k ih =>
    have hs := h.step k (by omega)
    have hu := h.update k (by omega)
    unfold IntervalUpdate at hu
    split_ifs at hu with ha hreset
    · rw [hu.2]; exact ih (by omega)
    · exact hu.2.2.trans (le_max_left _ _)
    · rw [hu.2]
      apply le_trans _ (le_max_right _ _)
      apply mul_le_mul_of_nonneg_left _ (by linarith [p.one_lt_gamma1, p.gamma_le])
      apply (div_le_iff₀ (norm_pos_iff.mpr (h.nonzero k (by omega)))).mpr
      by_contra hn
      exact ha (hs.accepted_of_shift (h.nonzero k (by omega)) hf (le_of_lt (lt_of_not_ge hn)))

/-- Acceptance pays the full cubic norm decrease in the actual objective. -/
theorem TrialTrace.accepted_decrease (h : TrialTrace p second f x s lambda lower upper Q N)
    {k : ℕ} (hk : k < N) (ha : p.eta ≤ ratio f (x k) (s k)) :
    p.eta * ‖s k‖ ^ 3 ≤ f (x k) - f (x (k + 1)) := by
  rw [h.iterate k hk, ite_eq_left ha]
  exact (le_div_iff₀ (pow_pos (norm_pos_iff.mpr (h.nonzero k hk)) _)).mp ha

/-- The actual objective never increases along any executed trial. -/
theorem TrialTrace.monotone (h : TrialTrace p second f x s lambda lower upper Q N)
    {k : ℕ} (hk : k < N) : f (x (k + 1)) ≤ f (x k) := by
  by_cases ha : p.eta ≤ ratio f (x k) (s k)
  · have hh := h.accepted_decrease hk ha
    have hp := mul_nonneg p.eta_pos.le (pow_nonneg (norm_nonneg (s k)) 3)
    linarith
  · rw [h.iterate k hk, ite_eq_right ha]

/-- Successful steps satisfy the squared next-gradient length bound. -/
theorem TrialTrace.accepted_step_sq (h : TrialTrace p second f x s lambda lower upper Q N)
    (hf : CubicRegularization.HessianLipschitz f L) {k : ℕ} (hk : k < N)
    (ha : p.eta ≤ ratio f (x k) (s k)) :
    2 * ‖gradient f (x (k + 1))‖ / (L + 4 * upperBound p L + 2 * p.kappa3) ≤ ‖s k‖ ^ 2 := by
  have hM : 0 < upperBound p L := p.sigmaMin_pos.trans_le (p.sigma_le.trans (le_max_left _ _))
  have hD : 0 < L + 4 * upperBound p L + 2 * p.kappa3 := by
    linarith [hf.nonneg, p.kappa3_pos]
  rw [div_le_iff₀ hD, h.iterate k hk, ite_eq_left ha]
  have hh := (h.step k hk).trial_gradient_le hf (h.upper_le hf (by omega : k ≤ N))
  nlinarith only [hh]

/-- The current projected curvature gives a linear step lower bound. -/
theorem TrialTrace.curvature_step [Nontrivial V]
    (h : TrialTrace p second f x s lambda lower upper Q N)
    (hf : CubicRegularization.HessianLipschitz f L) (hsecond : second = true)
    {k : ℕ} (hk : k < N) :
    -projectedCurvature f (x k) (Q k) / (p.kappa4 + upperBound p L) ≤ ‖s k‖ := by
  have hM : 0 < upperBound p L := p.sigmaMin_pos.trans_le (p.sigma_le.trans (le_max_left _ _))
  rw [div_le_iff₀ (by linarith [p.kappa4_pos] : 0 < p.kappa4 + upperBound p L)]
  have hh := (h.step k hk).projected_curvature_ge hsecond (h.upper_le hf (by omega : k ≤ N))
  nlinarith only [hh]

/-- Every endpoint has ordered, nonnegative regularization intervals. -/
theorem TrialTrace.interval_order (h : TrialTrace p second f x s lambda lower upper Q N)
    {k : ℕ} (hk : k ≤ N) : 0 ≤ lower k ∧ lower k ≤ upper k ∧ p.sigmaMin ≤ upper k := by
  induction k with
  | zero => rw [h.initial_lower]; exact ⟨le_rfl, p.sigmaMin_pos.le.trans h.initial_upper.1,
      h.initial_upper.1⟩
  | succ k ih =>
    have hs := h.step k (by omega)
    have hu := h.update k (by omega)
    unfold IntervalUpdate at hu
    split_ifs at hu with ha hr
    · rw [hu.1, hu.2]
      exact ⟨le_rfl, (ih (by omega)).2.2.trans' p.sigmaMin_pos.le, (ih (by omega)).2.2⟩
    · exact ⟨p.sigmaMin_pos.le.trans hu.1.1, hu.2.1, hu.1.1.trans hu.2.1⟩
    · have ht := norm_pos_iff.mpr (h.nonzero k (by omega))
      have hl : p.sigmaMin ≤ lambda k / ‖s k‖ := (le_div_iff₀ ht).mpr (le_of_not_gt hr)
      have hq := p.sigmaMin_pos.le.trans hl
      rw [hu.1, hu.2]
      exact ⟨mul_nonneg (by linarith [p.one_lt_gamma1]) hq,
        mul_le_mul_of_nonneg_right p.gamma_le hq,
        hl.trans (le_mul_of_one_le_left hq (by linarith [p.one_lt_gamma1, p.gamma_le]))⟩

/-- Any rejected trial installs at least the fixed positive lower regularization bound. -/
theorem TrialTrace.lower_after_failure (h : TrialTrace p second f x s lambda lower upper Q N)
    {k : ℕ} (hk : k < N) (ha : ¬p.eta ≤ ratio f (x k) (s k)) :
    p.sigmaMin ≤ lower (k + 1) := by
  have hu := h.update k hk
  simp only [IntervalUpdate, ite_eq_right ha] at hu
  split_ifs at hu with hr
  · exact hu.1.1
  · rw [hu.1]
    have hq : p.sigmaMin ≤ lambda k / ‖s k‖ :=
      (le_div_iff₀ (norm_pos_iff.mpr (h.nonzero k hk))).mpr (le_of_not_gt hr)
    exact hq.trans (le_mul_of_one_le_left (p.sigmaMin_pos.le.trans hq)
      p.one_lt_gamma1.le)

/-- Once the lower endpoint exceeds the fixed minimum, every rejection multiplies it by
at least the smallest growth factor. -/
theorem TrialTrace.lower_growth (h : TrialTrace p second f x s lambda lower upper Q N)
    {k : ℕ} (hk : k < N) (ha : ¬p.eta ≤ ratio f (x k) (s k))
    (hl : p.sigmaMin ≤ lower k) : p.gamma1 * lower k ≤ lower (k + 1) := by
  have hs := h.step k hk
  have hq : lower k ≤ lambda k / ‖s k‖ :=
    (le_div_iff₀ (norm_pos_iff.mpr (h.nonzero k (by omega)))).mpr hs.feasible_lower
  have hr : ¬lambda k < p.sigmaMin * ‖s k‖ := by
    have hh := mul_le_mul_of_nonneg_right hl (norm_nonneg (s k))
    exact not_lt.mpr (hh.trans hs.feasible_lower)
  have hu := h.update k hk
  simp only [IntervalUpdate, ite_eq_right ha, ite_eq_right hr] at hu
  rw [hu.1]
  exact mul_le_mul_of_nonneg_left hq (by linarith [p.one_lt_gamma1])

/-- A failed block has geometric growth after its first reset, including its final endpoint. -/
theorem TrialTrace.failed_block_growth (h : TrialTrace p second f x s lambda lower upper Q N)
    (a m : ℕ) (hN : a + 1 + m ≤ N)
    (ha : ∀ j < m + 1, ¬p.eta ≤ ratio f (x (a + j)) (s (a + j))) :
    p.gamma1 ^ m * p.sigmaMin ≤ lower (a + 1 + m) := by
  induction m with
  | zero => simpa using h.lower_after_failure (k := a) (by omega) (by simpa using ha 0 (by omega))
  | succ m ih =>
    have hprev := ih (by omega) (fun j hj => ha j (by omega))
    have hmin : p.sigmaMin ≤ lower (a + 1 + m) := by
      have hp : 1 ≤ p.gamma1 ^ m := one_le_pow₀ p.one_lt_gamma1.le
      have hh := mul_le_mul_of_nonneg_right hp p.sigmaMin_pos.le
      exact (show p.sigmaMin ≤ p.gamma1 ^ m * p.sigmaMin by simpa using hh).trans hprev
    have hh := h.lower_growth (k := a + 1 + m) (by omega)
      (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ha (m + 1) (by omega)) hmin
    have hm := mul_le_mul_of_nonneg_left hprev (by linarith [p.one_lt_gamma1] : 0 ≤ p.gamma1)
    rw [pow_succ]
    convert hm.trans hh using 1
    ring

/-- The uniform number of failures in any contiguous block, including the initial block. -/
def failureBound (p : Parameters) (L : ℝ) : ℝ :=
  Real.log (upperBound p L / p.sigmaMin) / Real.log p.gamma1 + 1

/-- Every contiguous failed block has the logarithmic bound. Unlike a statement restricted
to two successes, this also controls failed prefixes before the first success. -/
theorem TrialTrace.failed_block_count (h : TrialTrace p second f x s lambda lower upper Q N)
    (hf : CubicRegularization.HessianLipschitz f L) (a m : ℕ) (hN : a + m ≤ N)
    (ha : ∀ j < m, ¬p.eta ≤ ratio f (x (a + j)) (s (a + j))) :
    (m : ℝ) ≤ failureBound p L := by
  have hM : p.sigmaMin ≤ upperBound p L := p.sigma_le.trans (le_max_left _ _)
  have hratio : 1 ≤ upperBound p L / p.sigmaMin :=
    (le_div_iff₀ p.sigmaMin_pos).mpr (by simpa using hM)
  have hlog := Real.log_nonneg hratio
  cases m with
  | zero =>
    simpa only [Nat.cast_zero, failureBound] using
      add_nonneg (div_nonneg hlog (Real.log_pos p.one_lt_gamma1).le) zero_le_one
  | succ m =>
    have hg := h.failed_block_growth a m (by omega) (fun j hj => ha j hj)
    have hb := (h.interval_order (k := a + 1 + m) (by omega)).2.1.trans
      (h.upper_le hf (k := a + 1 + m) (by omega))
    have hp : p.gamma1 ^ m ≤ upperBound p L / p.sigmaMin :=
      (le_div_iff₀ p.sigmaMin_pos).mpr (hg.trans hb)
    have hh := Real.log_le_log (pow_pos (by linarith [p.one_lt_gamma1] : 0 < p.gamma1) m) hp
    rw [Real.log_pow] at hh
    have hd : (m : ℝ) ≤ Real.log (upperBound p L / p.sigmaMin) / Real.log p.gamma1 :=
      (le_div_iff₀ (Real.log_pos p.one_lt_gamma1)).mpr hh
    unfold failureBound
    push_cast
    linarith only [hd]

/-- The logarithmic failure coefficient is positive and independent of the tolerances. -/
theorem failureBound_pos (p : Parameters) (L : ℝ) : 0 < failureBound p L := by
  have hM : p.sigmaMin ≤ upperBound p L := p.sigma_le.trans (le_max_left _ _)
  have hr : 1 ≤ upperBound p L / p.sigmaMin :=
    (le_div_iff₀ p.sigmaMin_pos).mpr (by simpa using hM)
  exact add_pos_of_nonneg_of_pos (div_nonneg (Real.log_nonneg hr)
    (Real.log_pos p.one_lt_gamma1).le) zero_lt_one

/-- Total trial count from the number of accepted steps, including both end failure blocks. -/
theorem TrialTrace.total_count (h : TrialTrace p second f x s lambda lower upper Q N)
    (hf : CubicRegularization.HessianLipschitz f L) :
    (N : ℝ) ≤ (ParameterUpdates.successCount (fun k => p.eta ≤ ratio f (x k) (s k)) N : ℝ) *
      (failureBound p L + 1) + failureBound p L :=
  ParameterUpdates.count_of_failed_blocks _ _ (failureBound_pos p L).le N (h.failed_block_count hf)

/-- The coefficient in the quadratic upper bound on the next gradient. -/
def gradientBound (p : Parameters) (L : ℝ) : ℝ := L / 2 + 2 * upperBound p L + p.kappa3

/-- The gradient coefficient is positive for every nonnegative Hessian Lipschitz bound. -/
theorem gradientBound_pos (p : Parameters) {L : ℝ} (hL : 0 ≤ L) : 0 < gradientBound p L := by
  have hM : 0 < upperBound p L := p.sigmaMin_pos.trans_le (p.sigma_le.trans (le_max_left _ _))
  unfold gradientBound
  linarith [p.kappa3_pos]

/-- Uniform cubic objective-decrease coefficient for gradient termination. -/
def decreaseCoefficient (p : Parameters) (L : ℝ) : ℝ :=
  p.eta * ((Real.sqrt (gradientBound p L))⁻¹) ^ 3

/-- The objective-decrease coefficient is strictly positive. -/
theorem decreaseCoefficient_pos (p : Parameters) {L : ℝ} (hL : 0 ≤ L) :
    0 < decreaseCoefficient p L :=
  mul_pos p.eta_pos (pow_pos (inv_pos.mpr (Real.sqrt_pos.mpr (gradientBound_pos p hL))) _)

/-- A successful step whose next gradient still exceeds the squared tolerance pays the
uniform cubic tolerance decrease. -/
theorem TrialTrace.accepted_gradient_decrease
    (h : TrialTrace p second f x s lambda lower upper Q N)
    (hf : CubicRegularization.HessianLipschitz f L) {e : ℝ} (he : 0 < e)
    {k : ℕ} (hk : k < N) (ha : p.eta ≤ ratio f (x k) (s k))
    (hg : e ^ 2 ≤ ‖gradient f (x (k + 1))‖) :
    decreaseCoefficient p L * e ^ 3 ≤ f (x k) - f (x (k + 1)) := by
  have hh := (h.step k hk).trial_gradient_le hf (h.upper_le hf (by omega : k ≤ N))
  have hx : x (k + 1) = x k + s k := by rw [h.iterate k hk, ite_eq_left ha]
  rw [← hx] at hh
  have hs := InexactNewton.sqrt_gradient_le_step (gradientBound_pos p hf.nonneg)
    (norm_nonneg (s k)) (hg.trans hh)
  rw [Real.sqrt_sq he.le] at hs
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ (Real.sqrt (gradientBound p L))⁻¹ * e) hs 3
  have hd := mul_le_mul_of_nonneg_left hp p.eta_pos.le
  have ha' := h.accepted_decrease hk ha
  unfold decreaseCoefficient
  rw [mul_pow] at hd
  nlinarith only [hd, ha']

/-- A prefix ending before gradient termination has a bounded number of successes. -/
theorem TrialTrace.success_count (h : TrialTrace p second f x s lambda lower upper Q N)
    (hf : CubicRegularization.HessianLipschitz f L) {e low : ℝ} (he : 0 < e)
    (hlow : low ≤ f (x N)) (htest : ∀ j ≤ N, e ^ 2 < ‖gradient f (x j)‖) :
    (ParameterUpdates.successCount (fun k => p.eta ≤ ratio f (x k) (s k)) N : ℝ) ≤
      (f (x 0) - low) / (decreaseCoefficient p L * e ^ 3) := by
  classical
  rw [le_div_iff₀ (mul_pos (decreaseCoefficient_pos p hf.nonneg) (pow_pos he _))]
  apply EvaluationComplexity.card_mul_le_gap (u := fun j => f (x j))
    (Finset.filter_subset _ _) hlow (fun j hj => h.monotone hj)
  intro j hj
  obtain ⟨hj, ha⟩ := Finset.mem_filter.mp hj
  exact h.accepted_gradient_decrease hf he (Finset.mem_range.mp hj) ha
    (htest (j + 1) (by have := Finset.mem_range.mp hj; omega)).le

/-- Initial objective plus one objective evaluation per executed trial. -/
def functionEvaluations (N : ℕ) : ℕ := N + 1

/-- Initial derivatives plus fresh derivatives only at accepted successors; rejections retain
both cached derivatives. This counts each of gradient and Hessian evaluations separately. -/
def derivativeEvaluations (p : Parameters) (f : E → ℝ) (x s : ℕ → E) (N : ℕ) : ℕ :=
  ParameterUpdates.successCount (fun k => p.eta ≤ ratio f (x k) (s k)) N + 1

/-- First successful gradient test exists from local laws on every still-required finite
prefix, with actual objective and cached-derivative evaluation budgets. -/
theorem exists_firstOrder_with_cost {e low : ℝ} (he : 0 < e)
    (hf : CubicRegularization.HessianLipschitz f L) (hlow : ∀ y, low ≤ f y)
    (hprefix : ∀ n, (∀ j < n, e ^ 2 < ‖gradient f (x j)‖) →
      TrialTrace p false f x s lambda lower upper Q n) :
    ∃ K : ℕ, ‖gradient f (x K)‖ ≤ e ^ 2 ∧
      (∀ j < K, e ^ 2 < ‖gradient f (x j)‖) ∧
      (functionEvaluations K : ℝ) ≤
        (f (x 0) - low) / (decreaseCoefficient p L * e ^ 3) * (failureBound p L + 1) +
          failureBound p L + 2 ∧
      (derivativeEvaluations p f x s K : ℝ) ≤
        (f (x 0) - low) / (decreaseCoefficient p L * e ^ 3) + 2 := by
  classical
  let D := (f (x 0) - low) / (decreaseCoefficient p L * e ^ 3)
  let B := D * (failureBound p L + 1) + failureBound p L
  have hD : 0 ≤ D := div_nonneg (sub_nonneg.mpr (hlow _))
    (mul_pos (decreaseCoefficient_pos p hf.nonneg) (pow_pos he _)).le
  have hfail := failureBound_pos p L
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hbound : ∀ n, (∀ j < n, e ^ 2 < ‖gradient f (x j)‖) → (n : ℝ) ≤ B + 1 := by
    intro n hn
    cases n with
    | zero => simp only [Nat.cast_zero]; linarith only [hB]
    | succ n =>
      have h := hprefix n (fun j hj => hn j (by omega))
      have hs := h.success_count hf he (hlow _) (fun j hj => hn j (by omega))
      have ht := h.total_count hf
      have hm := mul_le_mul_of_nonneg_right hs (by positivity : 0 ≤ failureBound p L + 1)
      change _ ≤ D * _ at hm
      change _ ≤ _ * _ + failureBound p L at ht
      push_cast
      dsimp [B]
      linarith only [ht, hm]
  obtain ⟨K, _, hK, hfirst⟩ := EvaluationComplexity.exists_first_of_prefix_bound
    (P := fun j => ‖gradient f (x j)‖ ≤ e ^ 2)
    (fun n hn => hbound n (fun j hj => lt_of_not_ge (hn j hj)))
  have htest : ∀ j < K, e ^ 2 < ‖gradient f (x j)‖ := fun j hj => lt_of_not_ge (hfirst j hj)
  refine ⟨K, hK, htest, ?_, ?_⟩
  · have hb := hbound K htest
    simp only [functionEvaluations, Nat.cast_add, Nat.cast_one]
    change (K : ℝ) + 1 ≤ B + 2
    linarith only [hb]
  · cases K with
    | zero => simpa [derivativeEvaluations, ParameterUpdates.successCount] using
        (by linarith only [hD] : (1 : ℝ) ≤ D + 2)
    | succ n =>
      have h := hprefix n (fun j hj => htest j (by omega))
      have hs := h.success_count hf he (hlow _) (fun j hj => htest j (by omega))
      have hc : ParameterUpdates.successCount (fun j => p.eta ≤ ratio f (x j) (s j)) (n + 1) ≤
          ParameterUpdates.successCount (fun j => p.eta ≤ ratio f (x j) (s j)) n + 1 := by
        simp only [ParameterUpdates.successCount, Finset.range_add_one, Finset.filter_insert]
        split_ifs
        · exact Finset.card_insert_le _ _
        · omega
      have hc' :
          (ParameterUpdates.successCount (fun j => p.eta ≤ ratio f (x j) (s j)) (n + 1) : ℝ) ≤
          (ParameterUpdates.successCount (fun j => p.eta ≤ ratio f (x j) (s j)) n : ℝ) + 1 := by
        exact_mod_cast hc
      simp only [derivativeEvaluations, Nat.cast_add, Nat.cast_one]
      change _ ≤ D + 2
      linarith only [hs, hc']

/-- The first-order evaluation-complexity constants are fixed before the tolerance and the
execution; existence of the first stop and both actual evaluation budgets are conclusions. -/
theorem exists_firstOrder_complexity_constants (p : Parameters) (f : E → ℝ) (x0 : E)
    {L low : ℝ} (hf : CubicRegularization.HessianLipschitz f L) (hlow : ∀ y, low ≤ f y) :
    ∃ kS kA kB : ℝ, 0 < kS ∧ 0 < kA ∧ 0 < kB ∧
      ∀ tolerance : ℝ, 0 < tolerance → tolerance ≤ 1 →
      ∀ (x s : ℕ → E) (lambda lower upper : ℕ → ℝ) (Q : ℕ → V →ₗᵢ[ℝ] E),
        x 0 = x0 →
        (∀ n, (∀ j < n, tolerance < ‖gradient f (x j)‖) →
          TrialTrace p false f x s lambda lower upper Q n) →
        ∃ K : ℕ, ‖gradient f (x K)‖ ≤ tolerance ∧
          (∀ j < K, tolerance < ‖gradient f (x j)‖) ∧
          (functionEvaluations K : ℝ) ≤ kA * ((f x0 - low) / tolerance ^ (3 / 2 : ℝ)) + kB ∧
          (derivativeEvaluations p f x s K : ℝ) ≤
            kS * ((f x0 - low) / tolerance ^ (3 / 2 : ℝ)) + 2 := by
  have hc := decreaseCoefficient_pos p hf.nonneg
  have hb := failureBound_pos p L
  refine ⟨(decreaseCoefficient p L)⁻¹, (decreaseCoefficient p L)⁻¹ * (failureBound p L + 1),
    failureBound p L + 2, inv_pos.mpr hc, mul_pos (inv_pos.mpr hc) (by linarith),
    by linarith, ?_⟩
  intro tolerance ht _ht1 x s lambda lower upper Q hx hprefix
  obtain ⟨K, hK, hfirst, hfun, hderiv⟩ := exists_firstOrder_with_cost
    (e := Real.sqrt tolerance) (Real.sqrt_pos.mpr ht) hf hlow
    (fun n hn => hprefix n (by simpa [Real.sq_sqrt ht.le] using hn))
  have hpow : (Real.sqrt tolerance) ^ 3 = tolerance ^ (3 / 2 : ℝ) := by
    rw [← Real.rpow_natCast (Real.sqrt tolerance) 3, Real.sqrt_eq_rpow,
      ← Real.rpow_mul ht.le]
    norm_num
  rw [Real.sq_sqrt ht.le] at hK hfirst
  rw [hpow, hx] at hfun hderiv
  refine ⟨K, hK, hfirst, ?_, ?_⟩
  · convert hfun using 1; ring
  · convert hderiv using 1; ring

/-- First-order stopping, and projected second-order stopping when requested. -/
def Stationary (second : Bool) (f : E → ℝ) (epsilon1 epsilon2 : ℝ) (y : E)
    (Q : V →ₗᵢ[ℝ] E) : Prop :=
  ‖gradient f y‖ ≤ epsilon1 ∧ (second = true → -epsilon2 ≤ projectedCurvature f y Q)

/-- A complete finite iRN execution records the first successful stopping test. In the
second-order branch, step computation also precedes the final projected curvature test. -/
structure IsRun (p : Parameters) (second : Bool) (epsilon1 epsilon2 : ℝ) (f : E → ℝ)
    (x s : ℕ → E) (lambda lower upper : ℕ → ℝ) (Q : ℕ → V →ₗᵢ[ℝ] E) (N : ℕ) : Prop extends
    TrialTrace p second f x s lambda lower upper Q N where
  epsilon1_pos : 0 < epsilon1
  epsilon1_le_one : epsilon1 ≤ 1
  epsilon2_pos : second = true → 0 < epsilon2
  terminal_step : second = true →
    IsStep p second f (x N) (s N) (lambda N) (lower N) (upper N) (Q N)
  terminal : Stationary second f epsilon1 epsilon2 (x N) (Q N)
  first : ∀ k < N, ¬Stationary second f epsilon1 epsilon2 (x k) (Q k)

/-- Current projected curvature forces a cubic successful objective decrease. -/
theorem TrialTrace.accepted_curvature_decrease [Nontrivial V]
    (h : TrialTrace p true f x s lambda lower upper Q N)
    (hf : CubicRegularization.HessianLipschitz f L) {t : ℝ} (ht : 0 < t)
    {k : ℕ} (hk : k < N) (ha : p.eta ≤ ratio f (x k) (s k))
    (hc : projectedCurvature f (x k) (Q k) ≤ -t) :
    (p.eta * ((p.kappa4 + upperBound p L)⁻¹) ^ 3) * t ^ 3 ≤
      f (x k) - f (x (k + 1)) := by
  have hM : 0 < upperBound p L := p.sigmaMin_pos.trans_le (p.sigma_le.trans (le_max_left _ _))
  have hD : 0 < p.kappa4 + upperBound p L := add_pos p.kappa4_pos hM
  have hs := h.curvature_step hf rfl hk
  have ht' : t / (p.kappa4 + upperBound p L) ≤ ‖s k‖ := by
    have hh := div_le_div_of_nonneg_right (neg_le_neg hc) hD.le
    simpa only [neg_neg] using hh.trans hs
  have hp := pow_le_pow_left₀ (div_nonneg ht.le hD.le) ht' 3
  have hd := mul_le_mul_of_nonneg_left hp p.eta_pos.le
  have ha' := h.accepted_decrease hk ha
  rw [div_eq_mul_inv, mul_pow] at hd
  nlinarith only [hd, ha']

/-- A common coefficient for gradient and projected-curvature decrease. -/
def mixedCoefficient (p : Parameters) (L : ℝ) : ℝ :=
  min (decreaseCoefficient p L) (p.eta * ((p.kappa4 + upperBound p L)⁻¹) ^ 3)

/-- Both criticality mechanisms have a strictly positive common decrease coefficient. -/
theorem mixedCoefficient_pos (p : Parameters) {L : ℝ} (hL : 0 ≤ L) :
    0 < mixedCoefficient p L := by
  have hM : 0 < upperBound p L := p.sigmaMin_pos.trans_le (p.sigma_le.trans (le_max_left _ _))
  exact lt_min (decreaseCoefficient_pos p hL)
    (mul_pos p.eta_pos (pow_pos (inv_pos.mpr (add_pos p.kappa4_pos hM)) _))

/-- The common mixed tolerance scale is positive. -/
theorem mixedScale_pos {e t : ℝ} (he : 0 < e) (ht : 0 < t) :
    0 < min (e ^ 3) (t ^ 3) := lt_min (pow_pos he _) (pow_pos ht _)

/-- A success pays the common decrease if either the next gradient is large or the current
projected objective curvature is negative. -/
theorem TrialTrace.accepted_mixed_decrease [Nontrivial V]
    (h : TrialTrace p true f x s lambda lower upper Q N)
    (hf : CubicRegularization.HessianLipschitz f L) {e t : ℝ} (he : 0 < e) (ht : 0 < t)
    {k : ℕ} (hk : k < N) (ha : p.eta ≤ ratio f (x k) (s k))
    (hcrit : e ^ 2 ≤ ‖gradient f (x (k + 1))‖ ∨ projectedCurvature f (x k) (Q k) ≤ -t) :
    mixedCoefficient p L * min (e ^ 3) (t ^ 3) ≤ f (x k) - f (x (k + 1)) := by
  rcases hcrit with hg | hc
  · have hh := h.accepted_gradient_decrease hf he hk ha hg
    exact (mul_le_mul (min_le_left _ _) (min_le_left _ _) (mixedScale_pos he ht).le
      (decreaseCoefficient_pos p hf.nonneg).le).trans hh
  · have hh := h.accepted_curvature_decrease hf ht hk ha hc
    exact (mul_le_mul (min_le_right _ _) (min_le_right _ _) (mixedScale_pos he ht).le
      (le_trans (mixedCoefficient_pos p hf.nonneg).le (min_le_right _ _))).trans hh

open Classical in
/-- A merit function compensating the mismatch between current curvature and next gradient.
The additional half-decrease is present exactly when the current gradient test fails. -/
def merit (f : E → ℝ) (e d : ℝ) (y : E) : ℝ :=
  f y + if e ^ 2 < ‖gradient f y‖ then d / 2 else 0

/-- Every successful nonterminal current iteration decreases the merit function, even when
its successor first passes the gradient test. Rejections preserve the same merit value. -/
theorem TrialTrace.merit_decrease [Nontrivial V]
    (h : TrialTrace p true f x s lambda lower upper Q N)
    (hf : CubicRegularization.HessianLipschitz f L) {e t : ℝ} (he : 0 < e) (ht : 0 < t)
    {k : ℕ} (hk : k < N) (hfail : ¬Stationary true f (e ^ 2) t (x k) (Q k)) :
    let d := mixedCoefficient p L * min (e ^ 3) (t ^ 3)
    (if p.eta ≤ ratio f (x k) (s k) then d / 2 else 0) ≤
      merit f e d (x k) - merit f e d (x (k + 1)) := by
  classical
  dsimp only
  let d := mixedCoefficient p L * min (e ^ 3) (t ^ 3)
  have hd : 0 < d := mul_pos (mixedCoefficient_pos p hf.nonneg) (mixedScale_pos he ht)
  change (if p.eta ≤ ratio f (x k) (s k) then d / 2 else 0) ≤ _
  by_cases ha : p.eta ≤ ratio f (x k) (s k)
  · rw [ite_eq_left ha]
    have hmono := h.monotone hk
    by_cases hnext : e ^ 2 < ‖gradient f (x (k + 1))‖
    · have hdec := h.accepted_mixed_decrease hf he ht hk ha (Or.inl hnext.le)
      change d ≤ _ at hdec
      unfold merit
      rw [ite_eq_left hnext]
      split_ifs <;> linarith only [hdec, hd]
    · by_cases hcurrent : e ^ 2 < ‖gradient f (x k)‖
      · simp only [merit, ite_eq_left hcurrent, ite_eq_right hnext]
        linarith only [hmono]
      · have hc : projectedCurvature f (x k) (Q k) < -t := by
          by_contra hn
          exact hfail ⟨le_of_not_gt hcurrent, fun _ => le_of_not_gt hn⟩
        have hdec := h.accepted_mixed_decrease hf he ht hk ha (Or.inr hc.le)
        change d ≤ _ at hdec
        simp only [merit, ite_eq_right hcurrent, ite_eq_right hnext]
        linarith only [hdec, hd]
  · rw [ite_eq_right ha, h.iterate k hk, ite_eq_right ha]
    simp

/-- A second-order failed prefix has at most twice its objective-gap budget plus one
success. No curvature at a successor or full-dimensional subspace is assumed. -/
theorem TrialTrace.secondOrder_success_count [Nontrivial V]
    (h : TrialTrace p true f x s lambda lower upper Q N)
    (hf : CubicRegularization.HessianLipschitz f L) {e t low : ℝ} (he : 0 < e) (ht : 0 < t)
    (hlow : low ≤ f (x N)) (htest : ∀ j < N, ¬Stationary true f (e ^ 2) t (x j) (Q j)) :
    (ParameterUpdates.successCount (fun k => p.eta ≤ ratio f (x k) (s k)) N : ℝ) ≤
      2 * (f (x 0) - low) / (mixedCoefficient p L * min (e ^ 3) (t ^ 3)) + 1 := by
  classical
  let d := mixedCoefficient p L * min (e ^ 3) (t ^ 3)
  have hd : 0 < d := mul_pos (mixedCoefficient_pos p hf.nonneg) (mixedScale_pos he ht)
  have hlow' : low ≤ merit f e d (x N) := by
    unfold merit
    split_ifs <;> linarith only [hlow, hd]
  have hmono : ∀ k < N, merit f e d (x (k + 1)) ≤ merit f e d (x k) := by
    intro k hk
    have hh := h.merit_decrease hf he ht hk (htest k hk)
    change (if p.eta ≤ ratio f (x k) (s k) then d / 2 else 0) ≤ _ at hh
    split_ifs at hh <;> linarith only [hh, hd]
  have hdec : ∀ k ∈ (Finset.range N).filter (fun k => p.eta ≤ ratio f (x k) (s k)),
      d / 2 ≤ merit f e d (x k) - merit f e d (x (k + 1)) := by
    intro k hk
    obtain ⟨hk, ha⟩ := Finset.mem_filter.mp hk
    have hh := h.merit_decrease hf he ht (Finset.mem_range.mp hk)
      (htest k (Finset.mem_range.mp hk))
    simpa only [ite_eq_left ha] using hh
  have hh := EvaluationComplexity.card_mul_le_gap (Finset.filter_subset _ _) hlow' hmono hdec
  have hinit : merit f e d (x 0) ≤ f (x 0) + d / 2 := by
    unfold merit
    split_ifs <;> linarith only [hd]
  change _ ≤ 2 * (f (x 0) - low) / d + 1
  have hh' : (ParameterUpdates.successCount (fun k => p.eta ≤ ratio f (x k) (s k)) N : ℝ) - 1 ≤
      2 * (f (x 0) - low) / d := by
    apply (le_div_iff₀ hd).mpr
    change (ParameterUpdates.successCount (fun k => p.eta ≤ ratio f (x k) (s k)) N : ℝ) *
      (d / 2) ≤ _ at hh
    nlinarith only [hh, hinit]
  linarith only [hh']

/-- In the second-order branch, the current trial and its orthonormal subspace are computed
before the current stopping test, including the final stopping point. -/
structure SecondOrderPrefix (p : Parameters) (f : E → ℝ) (x s : ℕ → E)
    (lambda lower upper : ℕ → ℝ) (Q : ℕ → V →ₗᵢ[ℝ] E) (N : ℕ) : Prop extends
    TrialTrace p true f x s lambda lower upper Q N where
  current_step : IsStep p true f (x N) (s N) (lambda N) (lower N) (upper N) (Q N)

/-- A finite first projected second-order stopping index exists from local prefix laws.
The half-decrease merit accounts for current-curvature/next-gradient index changes. -/
theorem exists_secondOrder_with_cost [Nontrivial V] {e t low : ℝ} (he : 0 < e) (ht : 0 < t)
    (he1 : e ^ 2 ≤ 1) (hf : CubicRegularization.HessianLipschitz f L) (hlow : ∀ y, low ≤ f y)
    (hprefix : ∀ n, (∀ j < n, ¬Stationary true f (e ^ 2) t (x j) (Q j)) →
      SecondOrderPrefix p f x s lambda lower upper Q n) :
    ∃ K : ℕ, IsRun p true (e ^ 2) t f x s lambda lower upper Q K ∧
      (functionEvaluations K : ℝ) ≤
        2 * (f (x 0) - low) / (mixedCoefficient p L * min (e ^ 3) (t ^ 3)) *
          (failureBound p L + 1) + 2 * failureBound p L + 2 ∧
      (derivativeEvaluations p f x s K : ℝ) ≤
        2 * (f (x 0) - low) / (mixedCoefficient p L * min (e ^ 3) (t ^ 3)) + 2 := by
  classical
  let D := 2 * (f (x 0) - low) / (mixedCoefficient p L * min (e ^ 3) (t ^ 3))
  let B := (D + 1) * (failureBound p L + 1) + failureBound p L
  have hfail := failureBound_pos p L
  have hbound : ∀ n, (∀ j < n, ¬Stationary true f (e ^ 2) t (x j) (Q j)) → (n : ℝ) ≤ B := by
    intro n hn
    have h := (hprefix n hn).toTrialTrace
    have hs := h.secondOrder_success_count hf he ht (hlow _) hn
    have hh := h.total_count hf
    have hm := mul_le_mul_of_nonneg_right hs (by linarith only [hfail] : 0 ≤ failureBound p L + 1)
    change _ ≤ (D + 1) * _ at hm
    dsimp [B]
    linarith only [hh, hm]
  obtain ⟨K, _, hK, hfirst⟩ := EvaluationComplexity.exists_first_of_prefix_bound hbound
  have hp := hprefix K hfirst
  have hs := hp.toTrialTrace.secondOrder_success_count hf he ht (hlow _) hfirst
  refine ⟨K, ⟨hp.toTrialTrace, sq_pos_of_pos he, he1, fun _ => ht,
    fun _ => hp.current_step, hK, hfirst⟩, ?_, ?_⟩
  · have hb := hbound K hfirst
    simp only [functionEvaluations, Nat.cast_add, Nat.cast_one]
    change (K : ℝ) + 1 ≤ D * _ + 2 * failureBound p L + 2
    dsimp [B] at hb
    linarith only [hb]
  · simp only [derivativeEvaluations, Nat.cast_add, Nat.cast_one]
    change _ ≤ D + 2
    change _ ≤ D + 1 at hs
    linarith only [hs]

/-- Uniform projected second-order evaluation complexity. The constants precede both
accuracy thresholds, and the final curvature certificate refers exactly to the chosen final
subspace; no full-space curvature claim is made without a spanning basis. -/
theorem exists_secondOrder_complexity_constants [Nontrivial V]
    (p : Parameters) (f : E → ℝ) (x0 : E) {L low : ℝ}
    (hf : CubicRegularization.HessianLipschitz f L) (hlow : ∀ y, low ≤ f y) :
    ∃ kT kC kD : ℝ, 0 < kT ∧ 0 < kC ∧ 0 < kD ∧
      ∀ tolerance1 tolerance2 : ℝ, 0 < tolerance1 → tolerance1 ≤ 1 →
        0 < tolerance2 → tolerance2 ≤ 1 →
      ∀ (x s : ℕ → E) (lambda lower upper : ℕ → ℝ) (Q : ℕ → V →ₗᵢ[ℝ] E),
        x 0 = x0 →
        (∀ n, (∀ j < n, ¬Stationary true f tolerance1 tolerance2 (x j) (Q j)) →
          SecondOrderPrefix p f x s lambda lower upper Q n) →
        ∃ K : ℕ, IsRun p true tolerance1 tolerance2 f x s lambda lower upper Q K ∧
          (functionEvaluations K : ℝ) ≤
            kC * ((f x0 - low) / min (tolerance1 ^ (3 / 2 : ℝ)) (tolerance2 ^ 3)) + kD ∧
          (derivativeEvaluations p f x s K : ℝ) ≤
            kT * ((f x0 - low) / min (tolerance1 ^ (3 / 2 : ℝ)) (tolerance2 ^ 3)) + 2 := by
  have hc := mixedCoefficient_pos p hf.nonneg
  have hb := failureBound_pos p L
  refine ⟨2 / mixedCoefficient p L, (2 / mixedCoefficient p L) * (failureBound p L + 1),
    2 * failureBound p L + 2, div_pos (by norm_num) hc,
    mul_pos (div_pos (by norm_num) hc) (by linarith), by linarith, ?_⟩
  intro tolerance1 tolerance2 ht1 ht11 ht2 _ht21 x s lambda lower upper Q hx hprefix
  obtain ⟨K, hK, hfun, hderiv⟩ := exists_secondOrder_with_cost
    (e := Real.sqrt tolerance1) (t := tolerance2) (Real.sqrt_pos.mpr ht1) ht2
    (by simpa [Real.sq_sqrt ht1.le] using ht11) hf hlow
    (fun n hn => hprefix n (by simpa [Real.sq_sqrt ht1.le] using hn))
  have hpow : (Real.sqrt tolerance1) ^ 3 = tolerance1 ^ (3 / 2 : ℝ) := by
    rw [← Real.rpow_natCast (Real.sqrt tolerance1) 3, Real.sqrt_eq_rpow,
      ← Real.rpow_mul ht1.le]
    norm_num
  rw [Real.sq_sqrt ht1.le] at hK
  rw [hpow, hx] at hfun hderiv
  refine ⟨K, hK, ?_, ?_⟩
  · convert hfun using 1; ring
  · convert hderiv using 1; ring

end Optimization.InexactRegularizedNewton
