import Numlib.Optimization.QuadraticSubproblem
import Numlib.Optimization.CubicRegularization
import Numlib.Optimization.RegularizedTaylorCurvature
import Numlib.Optimization.HigherOrder
import Numlib.Optimization.FirstOrderRegularization

/-!
# Actual minimizers of cubic Taylor models

Positive cubic regularization makes the actual Taylor model coercive in finite dimension.
Its global minimizers satisfy both exact derivative conditions. If the objective is not
second-order stationary, every global minimizer strictly decreases the model.
-/

open scoped ContDiff InnerProductSpace Nat
open Set

noncomputable section

namespace Optimization.CubicRegularization
open RegularizedTaylorModel QuadraticSubproblem

/-- A scalar Hessian quadratic form determines the actual cubic model without requiring
any smoothness, definiteness or optimality hypotheses. -/
theorem cubicModel_of_scalar_hessian {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : F → ℝ} {x : F} {a σ : ℝ}
    (hH : ∀ u, fderiv ℝ (fderiv ℝ f) x u u = a * ‖u‖ ^ 2) (s : F) :
    cubicModel f x σ s =
      f x + fderiv ℝ f x s + a / 2 * ‖s‖ ^ 2 + σ / 6 * ‖s‖ ^ 3 := by
  rw [cubicModel_eq, show taylorModel f 2 x s =
    taylorModel f 1 x s + (2! : ℝ)⁻¹ • iteratedFDeriv ℝ 2 f x (fun _ => s)
      from taylorModel_succ f 1 x s]
  simp only [taylorModel_one, iteratedFDeriv_two_apply, hH, smul_eq_mul]
  norm_num
  ring

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The cubic Taylor model is genuinely twice continuously differentiable. -/
theorem contDiff_two_cubicModel (f : E → ℝ) (x : E) (sigma : ℝ) :
    ContDiff ℝ 2 (cubicModel f x sigma) := by
  have h := (contDiff_taylorModel f 2 x 2).add
    ((contDiff_two_norm_rpow (E := E) (by norm_num : (2 : ℝ) < 3)).const_smul (sigma / 6))
  change ContDiff ℝ 2 (fun z : E ↦ taylorModel f 2 x z + sigma / 6 * ‖z‖ ^ (3 : ℝ))
  exact h

/-- Riesz representation identifies the actual cubic Taylor model with a power-regularized
quadratic plus its constant value. No optimality assumptions occur in this identity. -/
theorem cubicModel_eq_powerRegularizedQuadratic [CompleteSpace E]
    (f : E → ℝ) (x : E) (sigma : ℝ) (s : E) :
    cubicModel f x sigma s = f x + powerRegularizedQuadratic
      ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x))
      (InnerProductSpace.continuousLinearMapOfBilin (fderiv ℝ (fderiv ℝ f) x))
      (sigma / 2) 3 s := by
  rw [cubicModel_eq, show taylorModel f 2 x s =
    taylorModel f 1 x s + (2! : ℝ)⁻¹ • iteratedFDeriv ℝ 2 f x (fun _ ↦ s)
      from taylorModel_succ f 1 x s]
  simp only [taylorModel_one, iteratedFDeriv_two_apply, powerRegularizedQuadratic, quadratic,
    InnerProductSpace.toDual_symm_apply, smul_eq_mul]
  have hi := InnerProductSpace.continuousLinearMapOfBilin_apply
    (fderiv ℝ (fderiv ℝ f) x) s s
  rw [real_inner_comm] at hi
  rw [hi, ← Real.rpow_natCast]
  norm_num
  ring

/-- Every positively regularized cubic Taylor model attains an actual global minimum. -/
theorem exists_isMinOn_cubicModel [FiniteDimensional ℝ E]
    (f : E → ℝ) (x : E) {sigma : ℝ} (hsigma : 0 < sigma) :
    ∃ s : E, IsMinOn (cubicModel f x sigma) univ s := by
  obtain ⟨s, hs⟩ := exists_isMinOn_powerRegularizedQuadratic
    ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x))
    (InnerProductSpace.continuousLinearMapOfBilin (fderiv ℝ (fderiv ℝ f) x))
    (div_pos hsigma (by norm_num : (0 : ℝ) < 2)) (by norm_num : (2 : ℝ) < 3)
  refine ⟨s, fun y hy ↦ ?_⟩
  change cubicModel f x sigma s ≤ cubicModel f x sigma y
  simp only [cubicModel_eq_powerRegularizedQuadratic]
  have hval : powerRegularizedQuadratic _ _ _ _ s ≤
      powerRegularizedQuadratic _ _ _ _ y := hs hy
  linarith [hval]

/-- A global cubic-model minimizer has exactly zero model derivative. -/
theorem fderiv_eq_zero_of_isMinOn_cubicModel {f : E → ℝ} {x s : E} {sigma : ℝ}
    (hs : IsMinOn (cubicModel f x sigma) univ s) :
    fderiv ℝ (cubicModel f x sigma) s = 0 :=
  (hs.isLocalMin (by simp)).fderiv_eq_zero

/-- A global cubic-model minimizer has a positive semidefinite genuine Hessian. -/
theorem hessian_nonneg_of_isMinOn_cubicModel {f : E → ℝ} {x s : E} {sigma : ℝ}
    (hs : IsMinOn (cubicModel f x sigma) univ s) (u : E) :
    0 ≤ fderiv ℝ (fderiv ℝ (cubicModel f x sigma)) s u u := by
  have hc := contDiff_two_cubicModel f x sigma
  apply Descent.nonneg_apply_apply_of_isLocalMinOn (C := univ) convex_univ
    (mem_univ s) (mem_univ (s + u)) hs.isLocalMinOn
    (Filter.Eventually.of_forall fun z ↦ (hc.differentiable (by norm_num) z).hasFDerivAt)
    (((hc.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) s).hasFDerivAt)
  rw [fderiv_eq_zero_of_isMinOn_cubicModel hs]
  rfl

/-- At zero the model Hessian is the objective Hessian; the cubic radial Hessian vanishes. -/
theorem hessian_cubicModel_zero {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (sigma : ℝ) :
    fderiv ℝ (fderiv ℝ (cubicModel f x sigma)) 0 = fderiv ℝ (fderiv ℝ f) x := by
  change fderiv ℝ (fderiv ℝ (regularizedModel f 2 x sigma 6 3)) 0 = _
  rw [hessian_regularizedModel f 2 x 0 sigma 6 (by norm_num : (2 : ℝ) < 3),
    hessian_taylorModel_two hf 0, normRpowHessian_zero 3 (by norm_num)]
  simp

/-- A global cubic-model minimizer strictly decreases the model, or is the zero step.
This remains true at an exactly second-order stationary objective point. -/
theorem decrease_or_eq_zero_of_isMinOn_cubicModel {f : E → ℝ} {x s : E} {sigma : ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hsigma : 0 < sigma)
    (hs : IsMinOn (cubicModel f x sigma) univ s) :
    cubicModel f x sigma s < f x ∨ s = 0 := by
  have hle : cubicModel f x sigma s ≤ f x := by simpa using hs (mem_univ (0 : E))
  by_cases heq : cubicModel f x sigma s = f x
  · right
    have hz : IsMinOn (cubicModel f x sigma) univ 0 := by
      intro y hy
      simpa only [cubicModel_zero, ← heq] using hs hy
    have hg : fderiv ℝ f x = 0 := by
      rw [← fderiv_cubicModel_zero_of_contDiffAt hf sigma]
      exact fderiv_eq_zero_of_isMinOn_cubicModel hz
    have hH : 0 ≤ fderiv ℝ (fderiv ℝ f) x s s := by
      rw [← hessian_cubicModel_zero hf sigma]
      exact hessian_nonneg_of_isMinOn_cubicModel hz s
    by_contra hne
    have hpos : 0 < sigma / 6 * ‖s‖ ^ (3 : ℕ) := by positivity
    rw [cubicModel_eq, show taylorModel f 2 x s =
      taylorModel f 1 x s + (2! : ℝ)⁻¹ • iteratedFDeriv ℝ 2 f x (fun _ ↦ s)
        from taylorModel_succ f 1 x s] at heq
    simp only [taylorModel_one, iteratedFDeriv_two_apply, hg, zero_apply,
      add_zero, smul_eq_mul] at heq
    norm_num at heq
    nlinarith
  · exact Or.inl (lt_of_le_of_ne hle heq)

/-- Away from exact second-order stationarity, every global cubic-model minimizer strictly
reduces the model. Negative curvature may occur in any direction. -/
theorem strict_decrease_of_isMinOn_cubicModel {f : E → ℝ} {x s : E} {sigma : ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hsigma : 0 < sigma)
    (hactive : fderiv ℝ f x ≠ 0 ∨
      ∃ u : E, fderiv ℝ (fderiv ℝ f) x u u < 0)
    (hs : IsMinOn (cubicModel f x sigma) univ s) :
    cubicModel f x sigma s < f x := by
  rcases decrease_or_eq_zero_of_isMinOn_cubicModel hf hsigma hs with hlt | hz
  · exact hlt
  · subst s
    rcases hactive with hg | ⟨u, hu⟩
    · exact (hg (by rw [← fderiv_cubicModel_zero_of_contDiffAt hf sigma]
                    exact fderiv_eq_zero_of_isMinOn_cubicModel hs)).elim
    · have hH := hessian_nonneg_of_isMinOn_cubicModel hs u
      rw [hessian_cubicModel_zero hf sigma] at hH
      exact (not_lt_of_ge hH hu).elim

/-- Actual global cubic minimizers supply admissible model steps for arbitrary nonnegative
first- and second-order residual tolerances. -/
theorem exists_legal_cubicModel_step [FiniteDimensional ℝ E] {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) {sigma theta1 theta2 : ℝ} (hsigma : 0 < sigma)
    (htheta1 : 0 ≤ theta1) (htheta2 : 0 ≤ theta2) :
    ∃ s : E, IsMinOn (cubicModel f x sigma) univ s ∧
      (cubicModel f x sigma s < f x ∨ s = 0) ∧
      ‖fderiv ℝ (cubicModel f x sigma) s‖ ≤ theta1 / 2 * ‖s‖ ^ 2 ∧
      (∀ u : E, -(theta2 * ‖s‖) * ‖u‖ ^ 2 ≤
        fderiv ℝ (fderiv ℝ (cubicModel f x sigma)) s u u) := by
  obtain ⟨s, hs⟩ := exists_isMinOn_cubicModel f x hsigma
  refine ⟨s, hs, decrease_or_eq_zero_of_isMinOn_cubicModel hf hsigma hs, ?_, ?_⟩
  · rw [fderiv_eq_zero_of_isMinOn_cubicModel hs, norm_zero]
    positivity
  · intro u
    apply le_trans _ (hessian_nonneg_of_isMinOn_cubicModel hs u)
    have : 0 ≤ theta2 * ‖s‖ * ‖u‖ ^ (2 : ℕ) := by positivity
    nlinarith

/-- At a nonstationary objective point there is an actual global cubic minimizer satisfying
strict model decrease and both prescribed approximate model conditions. -/
theorem exists_strict_legal_cubicModel_step [FiniteDimensional ℝ E] {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) {sigma theta1 theta2 : ℝ} (hsigma : 0 < sigma)
    (htheta1 : 0 ≤ theta1) (htheta2 : 0 ≤ theta2)
    (hactive : fderiv ℝ f x ≠ 0 ∨
      ∃ u : E, fderiv ℝ (fderiv ℝ f) x u u < 0) :
    ∃ s : E, IsMinOn (cubicModel f x sigma) univ s ∧
      cubicModel f x sigma s < f x ∧
      ‖fderiv ℝ (cubicModel f x sigma) s‖ ≤ theta1 / 2 * ‖s‖ ^ 2 ∧
      (∀ u : E, -(theta2 * ‖s‖) * ‖u‖ ^ 2 ≤
        fderiv ℝ (fderiv ℝ (cubicModel f x sigma)) s u u) := by
  obtain ⟨s, hs, _, hgrad, hcurv⟩ := exists_legal_cubicModel_step hf hsigma htheta1 htheta2
  exact ⟨s, hs, strict_decrease_of_isMinOn_cubicModel hf hsigma hactive hs, hgrad, hcurv⟩

section ExactRun
variable [FiniteDimensional ℝ E]

open Classical in
/-- Choose an actual global minimum when the regularization is positive. -/
def exactStep (f : E → ℝ) (x : E) (sigma : ℝ) : E :=
  if hsigma : 0 < sigma then (exists_isMinOn_cubicModel f x hsigma).choose else 0

/-- The chosen step minimizes the actual model, rather than an encoded optimality condition. -/
theorem exactStep_isMinOn (f : E → ℝ) (x : E) {sigma : ℝ} (hsigma : 0 < sigma) :
    IsMinOn (cubicModel f x sigma) univ (exactStep f x sigma) := by
  simp only [exactStep, dite_eq_left hsigma]
  exact (exists_isMinOn_cubicModel f x hsigma).choose_spec

open Classical in
/-- Exact minimization followed by the actual acceptance test and a legal parameter update. -/
def exactStates (p : ParameterUpdates.RegularizationParameters) (f : E → ℝ)
    (x0 : E) (sigma0 : ℝ) : ℕ → E × ℝ
  | 0 => (x0, sigma0)
  | k + 1 =>
    let z := exactStates p f x0 sigma0 k
    let s := exactStep f z.1 z.2
    let rho := ratio f z.1 s z.2
    (if p.eta1 ≤ rho then z.1 + s else z.1,
      FirstOrderRegularization.nextSigma p rho z.2)

/-- Initialization of the concrete exact cubic algorithm. -/
@[simp] theorem exactStates_zero (p : ParameterUpdates.RegularizationParameters)
    (f : E → ℝ) (x0 : E) (sigma0 : ℝ) : exactStates p f x0 sigma0 0 = (x0, sigma0) := rfl

/-- The exact algorithm preserves the prescribed positive parameter floor. -/
theorem exactStates_sigma_lower (p : ParameterUpdates.RegularizationParameters)
    (f : E → ℝ) (x0 : E) {sigma0 : ℝ} (h0 : p.sigmaMin ≤ sigma0) (k : ℕ) :
    p.sigmaMin ≤ (exactStates p f x0 sigma0 k).2 := by
  induction k with
  | zero => exact h0
  | succ k ih => exact FirstOrderRegularization.nextSigma_lower p _ ih

/-- The computed steps of the concrete exact cubic algorithm. -/
def exactSteps (p : ParameterUpdates.RegularizationParameters) (f : E → ℝ)
    (x0 : E) (sigma0 : ℝ) (k : ℕ) : E :=
  exactStep f (exactStates p f x0 sigma0 k).1 (exactStates p f x0 sigma0 k).2

/-- At each iteration the concrete step is an actual global model minimizer. -/
theorem exactSteps_isMinOn (p : ParameterUpdates.RegularizationParameters) (f : E → ℝ)
    (x0 : E) {sigma0 : ℝ} (h0 : p.sigmaMin ≤ sigma0) (k : ℕ) :
    IsMinOn (cubicModel f (exactStates p f x0 sigma0 k).1
      (exactStates p f x0 sigma0 k).2) univ (exactSteps p f x0 sigma0 k) :=
  exactStep_isMinOn f _ (p.sigmaMin_pos.trans_le (exactStates_sigma_lower p f x0 h0 k))

/-- The exact algorithm inhabits the cubic-run interface with every nonnegative
first-order residual tolerance. -/
theorem exactStates_isRun (p : ParameterUpdates.RegularizationParameters)
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) (x0 : E) {sigma0 theta : ℝ}
    (h0 : p.sigmaMin ≤ sigma0) (htheta : 0 ≤ theta) :
    IsRun p theta f (fun k ↦ (exactStates p f x0 sigma0 k).1)
      (exactSteps p f x0 sigma0) (fun k ↦ (exactStates p f x0 sigma0 k).2) where
  initial_lower := h0
  update k := FirstOrderRegularization.nextSigma_mem p _ (exactStates_sigma_lower p f x0 h0 k)
  iterate _ := rfl
  decrease k := decrease_or_eq_zero_of_isMinOn_cubicModel hf.contDiffAt
    (p.sigmaMin_pos.trans_le (exactStates_sigma_lower p f x0 h0 k))
    (exactSteps_isMinOn p f x0 h0 k)
  residual k := by
    rw [fderiv_eq_zero_of_isMinOn_cubicModel (exactSteps_isMinOn p f x0 h0 k), norm_zero]
    positivity

/-- The exact algorithm has nonnegative genuine model curvature at every computed step. -/
theorem exactStates_hessian_nonneg (p : ParameterUpdates.RegularizationParameters)
    (f : E → ℝ) (x0 : E) {sigma0 : ℝ} (h0 : p.sigmaMin ≤ sigma0) (k : ℕ) (u : E) :
    0 ≤ fderiv ℝ (fderiv ℝ (cubicModel f (exactStates p f x0 sigma0 k).1
      (exactStates p f x0 sigma0 k).2)) (exactSteps p f x0 sigma0 k) u u :=
  hessian_nonneg_of_isMinOn_cubicModel (exactSteps_isMinOn p f x0 h0 k) u

end ExactRun

end Optimization.CubicRegularization
