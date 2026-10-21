import Numlib.Optimization.CubicGradientSharpness
import Numlib.Optimization.CubicCurvatureSharpness
import NumlibSurface.CartisGouldToint.Chapter03.Section01
import NumlibSurface.CartisGouldToint.Chapter01.Section01
import Numlib.Optimization.CubicSecondOrder
import Numlib.Optimization.CubicModelMinimizer
import NumlibSurface.CartisGouldToint.Chapter02.Section04

/-!
# First-order complexity of cubic regularization

Both AR2 variants use actual model residuals, Taylor acceptance and legal parameter intervals.
The optional curvature test has a true least-eigenvalue interface; derivative costs include
initialization and each accepted trial.

The model is normalized by `sigma/6`; its actual radial Hessian has the factor `sigma/2`.
The displayed Hessian formula after (3.3.2) in the supplied transcription omits this factor.
-/
noncomputable section
namespace CartisGouldToint.Chapter03.Section03
open Optimization.ParameterUpdates Optimization.CubicRegularization
open Chapter03.Section01 Chapter02.Section01
variable {n : ℕ}

/-- The actual cubic Taylor model (3.3.1), including its value at zero. -/
def cubicModel (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n))
    (sigma : ℝ) (s : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Chapter01.Section03.taylorModel f 2 x s + sigma / 6 * ‖s‖ ^ 3

/-- The book model is the canonical regularized Taylor model. -/
theorem cubicModel_eq (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n))
    (sigma : ℝ) : cubicModel f x sigma = Optimization.CubicRegularization.cubicModel f x sigma := by
  funext s
  exact (Optimization.CubicRegularization.cubicModel_eq f x sigma s).symm

/-- The first-order variant of Algorithm 3.3.1. Zero steps extend a run only at exact
stationarity, so every computed step before a positive first-order test strictly decreases
its actual model. Stopping and oracle costs are specified in Theorem 3.3.5. -/
def firstOrderRun (p : RegularizationParameters) (theta : ℝ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x s : ℕ → EuclideanSpace ℝ (Fin n))
    (sigma : ℕ → ℝ) : Prop := IsRun p theta f x s sigma

/-- The uniform parameter bound (3.3.14). -/
def sigmaMax (p : RegularizationParameters) (L sigma0 : ℝ) : ℝ :=
  max sigma0 (p.gamma3 * (L / (1 - p.eta2)))

variable {p : RegularizationParameters} {theta : ℝ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {x s : ℕ → EuclideanSpace ℝ (Fin n)} {sigma : ℕ → ℝ}

/-- Lemma 3.3.1: strict decrease in the actual cubic model pays for its regularizer. -/
theorem lemma_3_3_1 {x s : EuclideanSpace ℝ (Fin n)} {sigma : ℝ}
    (h : cubicModel f x sigma s < cubicModel f x sigma 0) :
    sigma / 6 * ‖s‖ ^ 3 <
      Chapter01.Section03.taylorModel f 2 x 0 - Chapter01.Section03.taylorModel f 2 x s := by
  rw [cubicModel_eq] at h
  simpa [Chapter01.Section03.taylorModel, Optimization.CubicRegularization.cubicModel] using
    Optimization.RegularizedTaylorModel.taylor_decrease_of_model_decrease_strict
      (by norm_num : (0 : ℝ) < 3) h

/-- Lemma 3.3.2: f.HL bounds every regularization parameter. -/
theorem lemma_3_3_2 (h : firstOrderRun p theta f x s sigma) {L : ℝ}
    (hf : hessianLipschitz f L) (k : ℕ) : sigma k ≤ sigmaMax p L (sigma 0) :=
  h.sigma_upper hf.toHessianLipschitz k

/-- Lemma 3.3.3: successful steps control the gradient at the accepted successor. -/
theorem lemma_3_3_3 (h : firstOrderRun p theta f x s sigma) {L : ℝ}
    (hf : hessianLipschitz f L) (htheta : 0 < theta) (k : ℕ)
    (hk : p.eta1 ≤ ratio f (x k) (s k) (sigma k)) :
    2 / (L + theta + sigmaMax p L (sigma 0)) * ‖gradient f (x (k + 1))‖ ≤ ‖s k‖ ^ 2 := by
  have hM : 0 < sigmaMax p L (sigma 0) :=
    (h.toRegularizationUpdates.pos 0).trans_le (lemma_3_3_2 h hf 0)
  have hd : 0 < L + theta + sigmaMax p L (sigma 0) := by linarith [hf.one_le]
  have hb := h.accepted_derivative_bound hf.toHessianLipschitz k hk
  have hn : ‖gradient f (x (k + 1))‖ = ‖fderiv ℝ f (x (k + 1))‖ := by simp [gradient]
  rw [hn, div_mul_eq_mul_div, div_le_iff₀ hd]
  change ‖fderiv ℝ f (x (k + 1))‖ ≤ (L + theta + sigmaMax p L (sigma 0)) / 2 * _ at hb
  nlinarith

/-- Lemma 3.3.4 with an explicit positive constant independent of the accuracy threshold.
The final successful step accounts for the successor-gradient estimate. -/
theorem lemma_3_3_4 (h : firstOrderRun p theta f x s sigma) {L low : ℝ}
    (hf : hessianLipschitz f L) (htheta : 0 < theta) (hlow : ∀ y, low ≤ f y) :
    ∃ kappaS : ℝ, 0 < kappaS ∧ ∀ epsilon : ℝ, 0 < epsilon → ∀ K : ℕ,
      (∀ j < K, epsilon < ‖gradient f (x j)‖) →
      (successCount (fun k => p.eta1 ≤ ratio f (x k) (s k) (sigma k)) K : ℝ) ≤
        kappaS * ((f (x 0) - low) / epsilon ^ (3 / 2 : ℝ)) + 1 := by
  let a := (L + theta + sigmaMax p L (sigma 0)) / 2
  have hM : 0 < sigmaMax p L (sigma 0) :=
    (h.toRegularizationUpdates.pos 0).trans_le (lemma_3_3_2 h hf 0)
  have ha : 0 < a := by dsimp [a]; linarith [hf.one_le]
  refine ⟨6 * a ^ (3 / 2 : ℝ) / (p.eta1 * p.sigmaMin),
    div_pos (mul_pos (by norm_num) (Real.rpow_pos_of_pos ha _))
      (mul_pos p.eta1_pos p.sigmaMin_pos), ?_⟩
  intro epsilon he K ht
  exact h.success_count_before_test hf.toHessianLipschitz he ha le_rfl hlow K
    (fun j hj => by simpa [gradient] using ht j hj)

/-- Theorem 3.3.5: first-order AR2 takes order `epsilon^(-3/2)` actual oracle calls.
Function calls include initialization and every trial; gradient and Hessian calls both include
initialization and each accepted trial, giving the printed additive constant two. -/
theorem theorem_3_3_5 (h : firstOrderRun p theta f x s sigma) {L low : ℝ}
    (hf : hessianLipschitz f L) (htheta : 0 < theta) (hlow : ∀ y, low ≤ f y) :
    ∃ kappaS kappaA kappaC : ℝ, 0 < kappaS ∧ 0 < kappaA ∧ 0 < kappaC ∧
      ∀ epsilon : ℝ, 0 < epsilon → ∃ K : ℕ,
        approximateFirstOrderMinimizer f epsilon (x K) ∧
        (∀ j < K, epsilon < ‖gradient f (x j)‖) ∧
        (K : ℝ) + 1 ≤ kappaA * ((f (x 0) - low) / epsilon ^ (3 / 2 : ℝ)) + kappaC ∧
        (successCount (fun k => p.eta1 ≤ ratio f (x k) (s k) (sigma k)) K : ℝ) + 1 ≤
          kappaS * ((f (x 0) - low) / epsilon ^ (3 / 2 : ℝ)) + 2 := by
  let M := sigmaMax p L (sigma 0)
  let a := (L + theta + M) / 2
  let S := 6 * a ^ (3 / 2 : ℝ) / (p.eta1 * p.sigmaMin)
  let C := 1 + |Real.log p.gamma1| / Real.log p.gamma2
  let D := Real.log (M / sigma 0) / Real.log p.gamma2
  have hM : 0 < M := (h.toRegularizationUpdates.pos 0).trans_le (lemma_3_3_2 h hf 0)
  have ha : 0 < a := by dsimp [a]; linarith [hf.one_le]
  have hS : 0 < S := div_pos (mul_pos (by norm_num) (Real.rpow_pos_of_pos ha _))
    (mul_pos p.eta1_pos p.sigmaMin_pos)
  have hlog : 0 < Real.log p.gamma2 := Real.log_pos p.one_lt_gamma2
  have hC : 0 < C := add_pos_of_pos_of_nonneg zero_lt_one
    (div_nonneg (abs_nonneg _) hlog.le)
  have hD : 0 ≤ D := div_nonneg
    (Real.log_nonneg ((one_le_div (h.toRegularizationUpdates.pos 0)).mpr
      (lemma_3_3_2 h hf 0))) hlog.le
  refine ⟨S, C * S, C + D + 1, hS, mul_pos hC hS, by linarith, ?_⟩
  intro epsilon he
  obtain ⟨K, hk, ht, _, hderiv⟩ :=
    h.exists_stationary_with_cost hf.toHessianLipschitz he ha le_rfl hlow
  refine ⟨K, ?_, ?_, ?_, hderiv⟩
  · simpa [approximateFirstOrderMinimizer, gradient] using hk
  · intro j hj
    simpa [gradient] using ht j hj
  · have hcount := Chapter02.Section04.lemma_2_4_1 h.toRegularizationUpdates K
      (lemma_3_3_2 h hf K)
    have hsuccess : (successCount
        (fun k => p.eta1 ≤ ratio f (x k) (s k) (sigma k)) K : ℝ) ≤
        S * ((f (x 0) - low) / epsilon ^ (3 / 2 : ℝ)) + 1 := by
      linarith only [hderiv]
    have hb := mul_le_mul_of_nonneg_left hsuccess hC.le
    change (K : ℝ) ≤ _ * C + D at hcount
    nlinarith only [hcount, hb]

/-- Algorithm 3.3.1, with the optional curvature test represented by an explicit Boolean.
Stopping is specified by the first relevant accuracy test in the complexity theorems.
Its actual model residuals and interval
updates are retained; zero steps are only unused continuations after exact stationarity. -/
def algorithm_3_3_1 (p : RegularizationParameters) (theta1 theta2 : ℝ) (curvature : Bool)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x s : ℕ → EuclideanSpace ℝ (Fin n))
    (sigma : ℕ → ℝ) : Prop :=
  0 < theta1 ∧ 0 < theta2 ∧
    if curvature then SecondOrderRun p theta1 theta2 f x s sigma
    else firstOrderRun p theta1 f x s sigma

/-- Every AR2 variant satisfies the first-order trace interface. -/
theorem algorithm_3_3_1.toFirstOrderRun {theta2 : ℝ} {curvature : Bool}
    (h : algorithm_3_3_1 p theta theta2 curvature f x s sigma) :
    firstOrderRun p theta f x s sigma := by
  cases curvature
  · exact h.2.2
  · exact h.2.2.toIsRun

/-- Enabling curvature supplies the true model Hessian residual. -/
theorem algorithm_3_3_1.toSecondOrderRun {theta2 : ℝ}
    (h : algorithm_3_3_1 p theta theta2 true f x s sigma) :
    SecondOrderRun p theta theta2 f x s sigma := h.2.2

/-- Actual global model minimizers and legal updates realize either AR2 variant. -/
theorem algorithm_3_3_1_exists (p : RegularizationParameters)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ 2 f)
    (x0 : EuclideanSpace ℝ (Fin n)) {sigma0 theta1 theta2 : ℝ}
    (h0 : p.sigmaMin ≤ sigma0) (htheta1 : 0 < theta1) (htheta2 : 0 < theta2)
    (curvature : Bool) :
    algorithm_3_3_1 p theta1 theta2 curvature f
      (fun k => (exactStates p f x0 sigma0 k).1) (exactSteps p f x0 sigma0)
      (fun k => (exactStates p f x0 sigma0 k).2) := by
  refine ⟨htheta1, htheta2, ?_⟩
  have hr := exactStates_isRun p hf x0 h0 htheta1.le
  cases curvature
  · exact hr
  · refine { hr with curvature := ?_ }
    intro k u
    have hb := exactStates_hessian_nonneg p f x0 h0 k u
    have hn : 0 ≤ theta2 * ‖exactSteps p f x0 sigma0 k‖ * ‖u‖ ^ 2 :=
      mul_nonneg (mul_nonneg htheta2.le (norm_nonneg _)) (sq_nonneg _)
    nlinarith

/-- The textbook gradient/eigenvalue test is the backbone's actual joint criticality test. -/
theorem secondOrderStationary_iff [NeZero n] (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (epsilon1 epsilon2 : ℝ) (y : EuclideanSpace ℝ (Fin n)) :
    SecondOrderStationary f epsilon1 epsilon2 y ↔
      ‖gradient f y‖ ≤ epsilon1 ∧
        -epsilon2 ≤ Chapter01.Section03.leastHessianEigenvalue f y := by
  rw [Chapter01.Section03.le_leastHessianEigenvalue_iff]
  simp [SecondOrderStationary, gradient]

/-- Before termination the model step really decreases strictly, as required by Step 2. -/
theorem algorithm_3_3_1.strict_decrease_before_test {theta2 L epsilon1 epsilon2 : ℝ}
    (h : algorithm_3_3_1 p theta theta2 true f x s sigma) (hf : hessianLipschitz f L)
    (he1 : 0 ≤ epsilon1) (he2 : 0 ≤ epsilon2) (k : ℕ)
    (htest : ¬SecondOrderStationary f epsilon1 epsilon2 (x k)) :
    cubicModel f (x k) (sigma k) (s k) < cubicModel f (x k) (sigma k) 0 := by
  have hr := h.toSecondOrderRun
  have hs : s k ≠ 0 := by
    intro hs
    have hz := hr.stationary_of_step_eq_zero hf.toHessianLipschitz k hs
    apply htest
    refine ⟨hz.1.trans he1, ?_⟩
    intro u
    have hu := hz.2 u
    simp only [neg_zero, zero_mul] at hu
    have hn := mul_nonneg he2 (sq_nonneg ‖u‖)
    linarith
  rw [cubicModel_eq, Optimization.CubicRegularization.cubicModel_zero]
  exact (hr.decrease k).resolve_right hs

/-- Lemma 3.3.7: the alternate Taylor residual gives the modified successful step bound. -/
theorem lemma_3_3_7 {L : ℝ} (hf : hessianLipschitz f L) (htheta : 1 < theta)
    (h : ModifiedRun p theta f x s sigma) (k : ℕ)
    (hk : p.eta1 ≤ ratio f (x k) (s k) (sigma k)) :
    2 / (L + theta * sigmaMax p L (sigma 0)) * ‖gradient f (x (k + 1))‖ ≤ ‖s k‖ ^ 2 := by
  have hM : 0 < sigmaMax p L (sigma 0) :=
    (h.toTrialTrace.toRegularizationUpdates.pos 0).trans_le
      (h.toTrialTrace.sigma_upper hf.toHessianLipschitz 0)
  have hd : 0 < L + theta * sigmaMax p L (sigma 0) := by
    have := mul_pos (by linarith : 0 < theta) hM
    linarith [hf.one_le]
  have hb := h.accepted_derivative_bound hf.toHessianLipschitz (by linarith) k hk
  have hn : ‖gradient f (x (k + 1))‖ = ‖fderiv ℝ f (x (k + 1))‖ := by simp [gradient]
  rw [hn, div_mul_eq_mul_div, div_le_iff₀ hd]
  change ‖fderiv ℝ f (x (k + 1))‖ ≤ (L + theta * sigmaMax p L (sigma 0)) / 2 * _ at hb
  nlinarith

/-- Lemma 3.3.8: actual negative least Hessian eigenvalue forces the curvature step length. -/
theorem lemma_3_3_8 [NeZero n] {theta2 L : ℝ}
    (h : algorithm_3_3_1 p theta theta2 true f x s sigma) (hf : hessianLipschitz f L)
    (k : ℕ) (hk : p.eta1 ≤ ratio f (x k) (s k) (sigma k))
    (hneg : Chapter01.Section03.leastHessianEigenvalue f (x (k + 1)) < 0) :
    |Chapter01.Section03.leastHessianEigenvalue f (x (k + 1))| /
      (L + theta2 + sigmaMax p L (sigma 0)) ≤ ‖s k‖ := by
  have hb := h.toSecondOrderRun.step_norm_lower_bound hf.toHessianLipschitz h.2.1.le k hk hneg
  simpa [Chapter01.Section03.leastHessianEigenvalue, sigmaMax,
    add_comm, add_left_comm, add_assoc] using hb

/-- Explicit second-order AR2 constants give the successor-step derivative budget `+2`.
The printed proof of (3.3.30) drops one call; the numbered existential theorem below enlarges
its constant to recover the printed `+1` uniformly for tolerances at most one. -/
theorem secondOrder_cost_with_explicit_constants [NeZero n] {theta2 L low : ℝ}
    (h : algorithm_3_3_1 p theta theta2 true f x s sigma) (hf : hessianLipschitz f L)
    (hlow : ∀ y, low ≤ f y) :
    ∃ kappaT kappaD kappaF : ℝ, 0 < kappaT ∧ 0 < kappaD ∧ 1 ≤ kappaF ∧
      ∀ epsilon1 epsilon2 : ℝ, 0 < epsilon1 → 0 < epsilon2 → ∃ K : ℕ,
        (‖gradient f (x K)‖ ≤ epsilon1 ∧
          -epsilon2 ≤ Chapter01.Section03.leastHessianEigenvalue f (x K)) ∧
        (∀ j < K, ¬SecondOrderStationary f epsilon1 epsilon2 (x j)) ∧
        (K : ℝ) + 1 ≤ kappaD *
          ((f (x 0) - low) / min (epsilon1 ^ (3 / 2 : ℝ)) (epsilon2 ^ 3)) + kappaF ∧
        (successCount (fun k => p.eta1 ≤ ratio f (x k) (s k) (sigma k)) K : ℝ) + 1 ≤
          kappaT * ((f (x 0) - low) / min (epsilon1 ^ (3 / 2 : ℝ)) (epsilon2 ^ 3)) + 2 := by
  let M := sigmaMax p L (sigma 0)
  let B := L + max 1 (max theta theta2) + M
  let S := 6 * B ^ 3 / (p.eta1 * p.sigmaMin)
  let C := 1 + |Real.log p.gamma1| / Real.log p.gamma2
  let D := Real.log (M / sigma 0) / Real.log p.gamma2
  have hr := h.toSecondOrderRun
  have hM : 0 < M := (hr.toRegularizationUpdates.pos 0).trans_le (lemma_3_3_2 hr.toIsRun hf 0)
  have hB : 0 < B := by dsimp [B]; linarith [hf.one_le, le_max_left (1 : ℝ) (max theta theta2)]
  have hB1 : 1 ≤ B := by dsimp [B]; linarith [hf.one_le, le_max_left (1 : ℝ) (max theta theta2)]
  have htheta : theta ≤ max 1 (max theta theta2) := (le_max_left _ _).trans (le_max_right _ _)
  have htheta2 : theta2 ≤ max 1 (max theta theta2) := (le_max_right _ _).trans (le_max_right _ _)
  have hA : (L + theta + M) / 2 ≤ B ^ 2 := by
    have hsq : B ≤ B ^ 2 := by nlinarith
    dsimp [B] at *
    linarith [hf.one_le]
  have hcurv : L + M + theta2 ≤ B := by dsimp [B]; linarith
  have hS : 0 < S := div_pos (by positivity) (mul_pos p.eta1_pos p.sigmaMin_pos)
  have hlog : 0 < Real.log p.gamma2 := Real.log_pos p.one_lt_gamma2
  have hC : 0 < C := add_pos_of_pos_of_nonneg zero_lt_one
    (div_nonneg (abs_nonneg _) hlog.le)
  have hD : 0 ≤ D := div_nonneg
    (Real.log_nonneg ((one_le_div (hr.toRegularizationUpdates.pos 0)).mpr
      (lemma_3_3_2 hr.toIsRun hf 0))) hlog.le
  have hC1 : 1 ≤ C := by
    dsimp [C]
    exact le_add_of_nonneg_right (div_nonneg (abs_nonneg _) hlog.le)
  refine ⟨S, C * S, C + D + 1, hS, mul_pos hC hS, by linarith, ?_⟩
  intro epsilon1 epsilon2 he1 he2
  obtain ⟨K, hk, ht, _, hderiv⟩ :=
    hr.exists_stationary_with_cost hf.toHessianLipschitz he1 he2 hB hA hcurv hlow
  refine ⟨K, (secondOrderStationary_iff _ _ _ _).mp hk, ht, ?_, hderiv⟩
  have hcount := Chapter02.Section04.lemma_2_4_1 hr.toRegularizationUpdates K
    (lemma_3_3_2 hr.toIsRun hf K)
  have hsuccess : (successCount (fun k => p.eta1 ≤ ratio f (x k) (s k) (sigma k)) K : ℝ) ≤
      S * ((f (x 0) - low) / min (epsilon1 ^ (3 / 2 : ℝ)) (epsilon2 ^ 3)) + 1 := by
    linarith only [hderiv]
  have hb := mul_le_mul_of_nonneg_left hsuccess hC.le
  change (K : ℝ) ≤ _ * C + D at hcount
  nlinarith only [hcount, hb]

/-- Theorem 3.3.9: second-order AR2 evaluation complexity, including the printed `+1`
derivative count. The explicit successor-step estimate has `+2`; for positive initial gap
we enlarge its constant by the reciprocal gap, uniformly over tolerances at most one.
If the initial gap is zero, the initial point is already second-order stationary. -/
theorem theorem_3_3_9 [NeZero n] {theta2 L low : ℝ}
    (h : algorithm_3_3_1 p theta theta2 true f x s sigma) (hf : hessianLipschitz f L)
    (hlow : ∀ y, low ≤ f y) :
    ∃ kappaT kappaD kappaF : ℝ, 0 < kappaT ∧ 0 < kappaD ∧ 0 < kappaF ∧
      ∀ epsilon1 epsilon2 : ℝ, 0 < epsilon1 → epsilon1 ≤ 1 →
        0 < epsilon2 → epsilon2 ≤ 1 → ∃ K : ℕ,
        (‖gradient f (x K)‖ ≤ epsilon1 ∧
          -epsilon2 ≤ Chapter01.Section03.leastHessianEigenvalue f (x K)) ∧
        (∀ j < K, ¬SecondOrderStationary f epsilon1 epsilon2 (x j)) ∧
        (K : ℝ) + 1 ≤ kappaD *
          ((f (x 0) - low) / min (epsilon1 ^ (3 / 2 : ℝ)) (epsilon2 ^ 3)) + kappaF ∧
        (successCount (fun k => p.eta1 ≤ ratio f (x k) (s k) (sigma k)) K : ℝ) + 1 ≤
          kappaT * ((f (x 0) - low) / min (epsilon1 ^ (3 / 2 : ℝ)) (epsilon2 ^ 3)) + 1 := by
  obtain ⟨S, A, F, hS, hA, hF, hbudget⟩ := secondOrder_cost_with_explicit_constants h hf hlow
  by_cases hg : 0 < f (x 0) - low
  · refine ⟨S + 1 / (f (x 0) - low), A, F, add_pos hS (div_pos zero_lt_one hg),
      hA, lt_of_lt_of_le zero_lt_one hF, ?_⟩
    intro epsilon1 epsilon2 he1 _ he2 he2upper
    obtain ⟨K, hk, ht, hfun, hderiv⟩ := hbudget epsilon1 epsilon2 he1 he2
    refine ⟨K, hk, ht, hfun, ?_⟩
    have hd : 0 < min (epsilon1 ^ (3 / 2 : ℝ)) (epsilon2 ^ 3) :=
      lt_min (Real.rpow_pos_of_pos he1 _) (pow_pos he2 _)
    have hd1 : min (epsilon1 ^ (3 / 2 : ℝ)) (epsilon2 ^ 3) ≤ 1 :=
      (min_le_right _ _).trans (pow_le_one₀ he2.le he2upper)
    have hid : 1 / (f (x 0) - low) *
        ((f (x 0) - low) / min (epsilon1 ^ (3 / 2 : ℝ)) (epsilon2 ^ 3)) =
        1 / min (epsilon1 ^ (3 / 2 : ℝ)) (epsilon2 ^ 3) := by field_simp
    have hu : 1 ≤ 1 / (f (x 0) - low) *
        ((f (x 0) - low) / min (epsilon1 ^ (3 / 2 : ℝ)) (epsilon2 ^ 3)) := by
      rw [hid]
      exact (le_div_iff₀ hd).mpr (by simpa using hd1)
    nlinarith only [hderiv, hu]
  · have hzero : f (x 0) - low = 0 := by linarith [hlow (x 0)]
    have hmin : IsMinOn f Set.univ (x 0) := by
      intro y _
      change f (x 0) ≤ f y
      rw [sub_eq_zero.mp hzero]
      exact hlow y
    have hloc : IsLocalMin f (x 0) := hmin.isLocalMin (by simp)
    have hfirst := Chapter01.Section01.theorem_1_1_1 f (x 0)
    have hgrad := hfirst.1 (hf.smooth.of_le (by norm_num)) hloc
    have hcurv := hfirst.2.1 hf.smooth hloc
    refine ⟨S, A, F, hS, hA, lt_of_lt_of_le zero_lt_one hF, ?_⟩
    intro epsilon1 epsilon2 he1 _ he2 _
    refine ⟨0, ⟨by simpa [hgrad] using he1.le, ?_⟩, by intro j hj; omega, ?_, ?_⟩
    · apply (Chapter01.Section03.le_leastHessianEigenvalue_iff _ _ _).mpr
      intro u
      have hn := mul_nonneg he2.le (sq_nonneg ‖u‖)
      linarith [hcurv u]
    · simpa [hzero] using hF
    · simp [hzero, successCount]

/-- Theorem 3.3.6: fixed global Hessian and value bounds admit AR2 runs requiring
`ε^(-3/2)` iterations and calls to each of the three oracles. Every active trial succeeds. -/
theorem theorem_3_3_6 :
    ∃ L B : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ (f : EuclideanSpace ℝ (Fin 1) → ℝ) (N : ℕ)
        (x s : ℕ → EuclideanSpace ℝ (Fin 1)),
        hessianLipschitz f L ∧ assumption_f_Bb f ∧
        (∀ y, |f y| ≤ B) ∧ f (x 0) = 0 ∧
        algorithm_3_3_1 sharpParameters 1 1 false f x s (fun _ => 4) ∧
        (∀ k < N, ε < ‖gradient f (x k)‖) ∧
        approximateFirstOrderMinimizer f ε (x N) ∧
        1 / ε ^ (3 / 2 : ℝ) ≤ (N : ℝ) ∧
        1 / ε ^ (3 / 2 : ℝ) ≤ (N : ℝ) + 1 ∧
        1 / ε ^ (3 / 2 : ℝ) ≤ (successCount
          (fun k => sharpParameters.eta1 ≤ ratio f (x k) (s k) 4) N : ℝ) + 1 := by
  obtain ⟨L, B, hfamily⟩ := Optimization.CubicGradientSharpness.exists_hard_family
  refine ⟨max 1 (L : ℝ), B, ?_⟩
  intro ε he he1
  obtain ⟨f, N, x, s, hf, hLip, hb, hzero, _, hr, hpre, hlast, _, hcount, hN⟩ :=
    hfamily ε he he1
  refine ⟨f, N, x, s, hessianLipschitz.of_lipschitzWith hf hLip,
    assumption_f_Bb_iff.mpr ⟨-(B : ℝ), fun y => (abs_le.mp (hb y)).1⟩,
    hb, hzero, ?_, ?_, ?_, hN, by linarith, ?_⟩
  · exact ⟨by norm_num, by norm_num, hr.toIsRun⟩
  · intro k hk
    simpa [gradient] using hpre k hk
  · simpa [approximateFirstOrderMinimizer, gradient] using hlast
  · rw [hcount]
    linarith

/-- Theorem 3.3.10: uniform smooth bounded objectives attain the maximum of the first-order
and curvature evaluation lower bounds. The explicit first terminal test uses the actual
least Hessian eigenvalue, and successful trials account for both derivative oracles. -/
theorem theorem_3_3_10 :
    ∃ L B : ℝ, ∀ ε₁ ε₂ : ℝ, 0 < ε₁ → ε₁ ≤ 1 → 0 < ε₂ → ε₂ ≤ 1 →
      ∃ (f : EuclideanSpace ℝ (Fin 1) → ℝ) (N : ℕ)
        (x s : ℕ → EuclideanSpace ℝ (Fin 1)),
        hessianLipschitz f L ∧ assumption_f_Bb f ∧
        (∀ y, |f y| ≤ B) ∧ f (x 0) = 0 ∧
        algorithm_3_3_1 sharpParameters 1 1 true f x s (fun _ => 4) ∧
        (∀ k < N, ε₁ < ‖gradient f (x k)‖ ∨
          Chapter01.Section03.leastHessianEigenvalue f (x k) < -ε₂) ∧
        (‖gradient f (x N)‖ ≤ ε₁ ∧
          -ε₂ ≤ Chapter01.Section03.leastHessianEigenvalue f (x N)) ∧
        max (1 / ε₁ ^ (3 / 2 : ℝ)) (1 / ε₂ ^ 3) ≤ (N : ℝ) ∧
        max (1 / ε₁ ^ (3 / 2 : ℝ)) (1 / ε₂ ^ 3) ≤ (N : ℝ) + 1 ∧
        max (1 / ε₁ ^ (3 / 2 : ℝ)) (1 / ε₂ ^ 3) ≤ (successCount
          (fun k => sharpParameters.eta1 ≤ ratio f (x k) (s k) 4) N : ℝ) + 1 := by
  obtain ⟨Lg, Bg, hg⟩ := Optimization.CubicGradientSharpness.exists_hard_family
  obtain ⟨Lc, Bc, hc⟩ := Optimization.CubicCurvatureSharpness.exists_hard_family
  refine ⟨max 1 (max (Lg : ℝ) (Lc : ℝ)), max (Bg : ℝ) (Bc : ℝ), ?_⟩
  intro ε₁ ε₂ he₁ he₁one he₂ he₂one
  by_cases hdom : 1 / ε₂ ^ 3 ≤ 1 / ε₁ ^ (3 / 2 : ℝ)
  · obtain ⟨f, N, x, s, hf, hLip, hb, hzero, _, hr, hpre, hlast, hH, hcount, hN⟩ :=
      hg ε₁ he₁ he₁one
    have hmax := max_eq_left hdom
    refine ⟨f, N, x, s, ?_,
      assumption_f_Bb_iff.mpr ⟨-(Bg : ℝ), fun y => (abs_le.mp (hb y)).1⟩,
      fun y => (hb y).trans (le_max_left _ _), hzero,
      ⟨by norm_num, by norm_num, hr⟩, ?_, ?_, ?_, ?_, ?_⟩
    · exact (hessianLipschitz.of_lipschitzWith hf hLip).mono
        (max_le (le_max_left _ _) ((le_max_left _ _).trans (le_max_right _ _)))
    · intro k hk
      exact Or.inl (by simpa [gradient] using hpre k hk)
    · apply (secondOrderStationary_iff _ _ _ _).mp
      refine ⟨hlast, fun u => ?_⟩
      rw [hH]
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr he₂.le) (sq_nonneg _)
    · rw [hmax]
      exact hN
    · rw [hmax]
      linarith
    · rw [hcount, hmax]
      linarith
  · obtain ⟨f, N, x, s, hf, hLip, hb, hzero, _, hr, hgrad, hH, hlast, hcount, hN⟩ :=
      hc ε₂ he₂ he₂one
    have hmax := max_eq_right (le_of_not_ge hdom)
    refine ⟨f, N, x, s, ?_,
      assumption_f_Bb_iff.mpr ⟨-(Bc : ℝ), fun y => (abs_le.mp (hb y)).1⟩,
      fun y => (hb y).trans (le_max_right _ _), hzero,
      ⟨by norm_num, by norm_num, hr⟩, ?_, ?_, ?_, ?_, ?_⟩
    · exact (hessianLipschitz.of_lipschitzWith hf hLip).mono
        (max_le (le_max_left _ _) ((le_max_right _ _).trans (le_max_right _ _)))
    · intro k hk
      right
      have hh := Optimization.leastCurvature_eq_of_scalar
        (fderiv ℝ (fderiv ℝ f) (x k)) (hH k hk)
      change Optimization.leastCurvature (fderiv ℝ (fderiv ℝ f) (x k)) < _
      rw [hh]
      linarith
    · apply (secondOrderStationary_iff _ _ _ _).mp
      refine ⟨?_, fun u => ?_⟩
      · rw [hgrad, norm_zero]
        exact he₁.le
      · rw [hlast]
        exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr he₂.le) (sq_nonneg _)
    · rw [hmax]
      exact hN
    · rw [hmax]
      linarith
    · rw [hcount, hmax]
      linarith

end CartisGouldToint.Chapter03.Section03
