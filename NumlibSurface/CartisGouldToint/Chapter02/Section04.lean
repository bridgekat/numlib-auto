import Numlib.Optimization.FirstOrderSharpness
import Numlib.Optimization.FirstOrderRegularization
import Numlib.Optimization.QuadraticSubproblem
import Numlib.Optimization.RegularizedTaylorModel
import NumlibSurface.CartisGouldToint.Chapter02.Section01

/-!
# First-order adaptive regularization

Algorithm 2.4.1 is a lawful run with all interval choices. A concrete legal choice is also
provided. Runs are truncated at the first gradient test; the unused zero-gradient ratio is
extended by one. Oracle counts include initialization and reuse cached gradients after rejection.
-/
noncomputable section
namespace CartisGouldToint.Chapter02.Section04
open Section01 Optimization.FirstOrderRegularization
variable {n : ℕ}

/-- The ordered constants in (2.4.2); initialization additionally requires `sigmaMin ≤ sigma 0`.
The reversed suggested numerical gamma values in the transcription are not used. -/
abbrev regularizationParameters := Parameters

/-- Algorithm 2.4.1: a legal AR1 trace, to be stopped at its first small-gradient iterate. -/
def algorithm_2_4_1 (p : regularizationParameters) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (sigma : ℕ → ℝ) : Prop :=
  IsRun p f (gradient f) x sigma

/-- A deterministic choice realizes the AR1 trace specification. -/
theorem algorithm_2_4_1_exists (p : regularizationParameters)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x0 : EuclideanSpace ℝ (Fin n))
    {sigma0 : ℝ} (hs : p.sigmaMin ≤ sigma0) :
    algorithm_2_4_1 p f (fun k => (states p f (gradient f) x0 sigma0 k).1)
      (fun k => (states p f (gradient f) x0 sigma0 k).2) :=
  states_isRun p f (gradient f) x0 hs

/-- The quadratic model (2.4.1). -/
def regularizationModel (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (sigma : ℝ) (s : EuclideanSpace ℝ (Fin n)) : ℝ :=
  f x + inner ℝ (gradient f x) s + sigma / 2 * ‖s‖ ^ 2

/-- The linear part is the canonical first-order Taylor model. -/
theorem regularizationModel_eq {f : EuclideanSpace ℝ (Fin n) → ℝ} {L : ℝ}
    (hf : assumption_f_gL f L) (x s : EuclideanSpace ℝ (Fin n)) (sigma : ℝ) :
    regularizationModel f x sigma s =
      Optimization.RegularizedTaylorModel.taylorModel f 1 x s + sigma / 2 * ‖s‖ ^ 2 := by
  rw [Optimization.RegularizedTaylorModel.taylorModel_one, (hf.hasFDerivAt x).fderiv]
  rfl

/-- The exact minimizer used in step 2 is the negative gradient divided by sigma. -/
theorem regularizationModel_minimizer (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) {sigma : ℝ} (hs : 0 < sigma) :
    IsMinOn (regularizationModel f x sigma) Set.univ (-(sigma⁻¹ • gradient f x)) :=
  Optimization.QuadraticSubproblem.isMinOn_univ_linear_add_norm_sq (f x) (gradient f x) hs

/-- The uniform regularization-parameter bound in (2.4.9). -/
def sigmaMax (p : regularizationParameters) (L sigma0 : ℝ) : ℝ :=
  max sigma0 (p.gamma3 * (L / (2 * (1 - p.eta2))))

variable {p : regularizationParameters} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : ℕ → EuclideanSpace ℝ (Fin n)} {sigma : ℕ → ℝ}

/-- Lemma 2.4.1: unsuccessful iterations are controlled by multiplicative updates. -/
theorem lemma_2_4_1 {p : regularizationParameters} {rho sigma : ℕ → ℝ}
    (h : Optimization.ParameterUpdates.RegularizationUpdates p rho sigma) (k : ℕ) {M : ℝ}
    (hM : sigma k ≤ M) :
    (k : ℝ) ≤ (Optimization.ParameterUpdates.successCount
      (fun j => p.eta1 ≤ rho j) k : ℝ) *
      (1 + |Real.log p.gamma1| / Real.log p.gamma2) +
      Real.log (M / sigma 0) / Real.log p.gamma2 :=
  h.total_count_le k hM

/-- Lemma 2.4.2: Lipschitz gradients bound every regularization parameter. -/
theorem lemma_2_4_2 (h : algorithm_2_4_1 p f x sigma) {L : ℝ}
    (hf : assumption_f_gL f L) (k : ℕ) : sigma k ≤ sigmaMax p L (sigma 0) :=
  h.sigma_upper hf.hasFDerivAt hf.lipschitz hf.constant_pos k

/-- Lemma 2.4.3 with the explicit positive constant sigmaMax/eta1. The bound holds for every
prefix before the first gradient test succeeds. -/
theorem lemma_2_4_3 (h : algorithm_2_4_1 p f x sigma) {L low epsilon : ℝ}
    (hf : assumption_f_gL f L) (hlow : ∀ y, low ≤ f y) (he : 0 < epsilon)
    (k : ℕ) (htest : ∀ j < k, epsilon < ‖gradient f (x j)‖) :
    (Optimization.ParameterUpdates.successCount
      (fun j => p.eta1 ≤ ratio f (gradient f) (x j) (sigma j)) k : ℝ) ≤
      (sigmaMax p L (sigma 0) / p.eta1) * ((f (x 0) - low) / epsilon ^ 2) := by
  have hM := lemma_2_4_2 h hf
  have hp : 0 < sigmaMax p L (sigma 0) := (h.sigma_pos 0).trans_le (hM 0)
  have hb := h.success_count_le he (hlow (x k)) (fun j _ => hM j) hp htest
  convert hb using 1
  field_simp

/-- Theorem 2.4.4: constants independent of epsilon bound all function and gradient calls.
There is one initial function/gradient evaluation, one trial function call per iteration,
and one new gradient per accepted trial. The first successful test is retained explicitly. -/
theorem theorem_2_4_4 (h : algorithm_2_4_1 p f x sigma) {L low : ℝ}
    (hf : assumption_f_gL f L) (hlow : ∀ y, low ≤ f y) :
    ∃ kappaS kappaA kappaC : ℝ, 0 < kappaS ∧ 0 < kappaA ∧ 0 < kappaC ∧
      ∀ epsilon : ℝ, 0 < epsilon → ∃ K : ℕ,
        approximateFirstOrderMinimizer f epsilon (x K) ∧
        (∀ j < K, epsilon < ‖gradient f (x j)‖) ∧
        (K : ℝ) + 1 ≤ kappaA * ((f (x 0) - low) / epsilon ^ 2) + kappaC ∧
        (Optimization.ParameterUpdates.successCount
          (fun j => p.eta1 ≤ ratio f (gradient f) (x j) (sigma j)) K : ℝ) + 1 ≤
          kappaS * ((f (x 0) - low) / epsilon ^ 2) + 1 := by
  let M := sigmaMax p L (sigma 0)
  let C := 1 + |Real.log p.gamma1| / Real.log p.gamma2
  let D := Real.log (M / sigma 0) / Real.log p.gamma2
  have hM : ∀ k, sigma k ≤ M := lemma_2_4_2 h hf
  have hMp : 0 < M := (h.sigma_pos 0).trans_le (hM 0)
  have hlog : 0 < Real.log p.gamma2 := Real.log_pos p.one_lt_gamma2
  have hC : 0 < C := by
    dsimp [C]
    exact add_pos_of_pos_of_nonneg zero_lt_one (div_nonneg (abs_nonneg _) hlog.le)
  have hD : 0 ≤ D := by
    exact div_nonneg (Real.log_nonneg ((one_le_div (h.sigma_pos 0)).mpr (hM 0))) hlog.le
  refine ⟨M / p.eta1, M / p.eta1 * C, D + 1, div_pos hMp p.eta1_pos,
    mul_pos (div_pos hMp p.eta1_pos) hC, by linarith, ?_⟩
  intro epsilon he
  obtain ⟨K, hk, hfirst, hfun, hgrad⟩ := h.exists_stationary_with_cost he hlow hM
  have hbudget : (f (x 0) - low) / (p.eta1 * (epsilon ^ 2 / M)) =
      (M / p.eta1) * ((f (x 0) - low) / epsilon ^ 2) := by
    field_simp
  refine ⟨K, hk, hfirst, ?_, ?_⟩
  · dsimp [C, D] at *
    rw [hbudget] at hfun
    nlinarith only [hfun]
  · rwa [hbudget] at hgrad

/-- Theorem 2.4.5: a fixed global smoothness and initial-gap bound admits a hard AR1
objective at every tolerance. Constant unit regularization is a legal parameter choice,
all iterations before termination succeed, and both oracle counts exceed `ε⁻²`. -/
theorem theorem_2_4_5 (p : regularizationParameters) (hp : p.sigmaMin ≤ 1) :
    ∃ L B : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ (f : EuclideanSpace ℝ (Fin 1) → ℝ)
        (x : ℕ → EuclideanSpace ℝ (Fin 1)) (N : ℕ),
        assumption_f_gL f L ∧ assumption_f_Bb f ∧
        (∀ u, -B ≤ f u) ∧ f (x 0) - (-B) ≤ B ∧
        algorithm_2_4_1 p f x (fun _ => 1) ∧
        ε⁻¹ ^ 2 ≤ (N : ℝ) ∧
        (∀ k < N, ε < ‖gradient f (x k)‖) ∧
        approximateFirstOrderMinimizer f ε (x N) ∧
        ε⁻¹ ^ 2 ≤ (N : ℝ) + 1 ∧
        ε⁻¹ ^ 2 ≤ (Optimization.ParameterUpdates.successCount
          (fun k => p.eta1 ≤ ratio f (gradient f) (x k) 1) N : ℝ) + 1 := by
  classical
  obtain ⟨L, B, hL, _, hc⟩ := Optimization.LowerBound.exists_firstOrder_chain
  refine ⟨L, B, ?_⟩
  intro ε he he1
  obtain ⟨f, N, x, hf, hLip, hlow, hzero, hN, hpre, hlast, hstep, hdrop⟩ := hc ε he he1
  have hr (k : ℕ) : ratio f (gradient f) (x k) 1 = 1 :=
    Optimization.LowerBound.unitSteps_ratio_eq_one hstep hdrop k
  have hcount : Optimization.ParameterUpdates.successCount
      (fun k => p.eta1 ≤ ratio f (gradient f) (x k) 1) N = N := by
    simp [Optimization.ParameterUpdates.successCount, hr, p.eta_le.trans p.eta2_lt_one.le]
  refine ⟨f, x, N, ⟨hf, hL, hLip⟩, assumption_f_Bb_iff.mpr ⟨-B, hlow⟩,
    hlow, by rw [hzero]; simp,
    Optimization.LowerBound.unitSteps_isRegularizationRun hstep hdrop p hp,
    hN, ?_, ?_, by linarith, ?_⟩
  · intro k hk
    rw [hpre k hk]
    linarith
  · rw [approximateFirstOrderMinimizer, hlast, norm_zero]
    exact he.le
  · rw [hcount]
    linarith

end CartisGouldToint.Chapter02.Section04
