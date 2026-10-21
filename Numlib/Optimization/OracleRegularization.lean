import Numlib.Optimization.OracleRegularizationModel
import Numlib.Optimization.HigherOrderRegularizationComplexity
import Numlib.Optimization.OracleMinimax

/-!
# A deterministic adaptive regularization oracle method

Finite raw reply histories determine the accepted point, cached tensor reply and parameter.
Each next query is the actual model trial, including rejected trials. The cache and replay
laws below are objective-independent; actual replies recover the canonical ARp ratio,
acceptance and parameter updates.
-/

noncomputable section
namespace Optimization.DerivativeOracle
open ZeroChains ParameterUpdates HigherOrderRegularization

/-- State of a raw-history adaptive regularization implementation. -/
structure RegularizationState (n p : ℕ) where
  point : Space n
  cached : Reply n p
  sigma : ℝ

variable {n p : ℕ}

/-- The selected step uses precisely the accepted point's cached reply. -/
def RegularizationState.step (a : RegularizationState n p) : Space n :=
  a.cached.minimizer a.sigma

/-- Every pass queries its trial point, even when that trial will be rejected. -/
def RegularizationState.trial (a : RegularizationState n p) : Space n := a.point + a.step

open Classical in
/-- The trial's value and cached polynomial determine its ratio; the zero-step convention
agrees with the canonical continuation ratio. -/
def RegularizationState.ratio (a : RegularizationState n p) (R : Reply n p) : ℝ :=
  if a.step = 0 then 1 else (a.cached.value - R.value) /
    (a.cached.value - a.cached.taylor a.step)

open Classical in
/-- A deterministic choice from the three source parameter update intervals. -/
def updatedSigma (P : RegularizationParameters) (rho sigma : ℝ) : ℝ :=
  if P.eta2 ≤ rho then max P.sigmaMin (P.gamma1 * sigma)
  else if P.eta1 ≤ rho then sigma else P.gamma2 * sigma

/-- This parameter choice belongs to the literal source update interval. -/
theorem updatedSigma_mem (P : RegularizationParameters) (rho sigma : ℝ)
    (hsigma : P.sigmaMin ≤ sigma) :
    if P.eta2 ≤ rho then updatedSigma P rho sigma ∈
      Set.Icc (max P.sigmaMin (P.gamma1 * sigma)) sigma
    else if P.eta1 ≤ rho then updatedSigma P rho sigma ∈ Set.Icc sigma (P.gamma2 * sigma)
    else updatedSigma P rho sigma ∈ Set.Icc (P.gamma2 * sigma) (P.gamma3 * sigma) := by
  have hs : 0 ≤ sigma := P.sigmaMin_pos.le.trans hsigma
  unfold updatedSigma
  split_ifs <;> simp only [Set.mem_Icc, le_refl, true_and]
  · exact max_le hsigma (mul_le_of_le_one_left hs P.gamma1_lt_one.le)
  · exact le_mul_of_one_le_left hs P.one_lt_gamma2.le
  · exact mul_le_mul_of_nonneg_right P.gamma2_lt_gamma3.le hs

/-- Parameter updates retain the positive floor. -/
theorem updatedSigma_lower (P : RegularizationParameters) (rho sigma : ℝ)
    (hsigma : P.sigmaMin ≤ sigma) : P.sigmaMin ≤ updatedSigma P rho sigma := by
  classical
  unfold updatedSigma
  split_ifs
  · exact le_max_left _ _
  · exact hsigma
  · exact hsigma.trans (le_mul_of_one_le_left (P.sigmaMin_pos.le.trans hsigma)
      P.one_lt_gamma2.le)

open Classical in
/-- Consume a trial response, accepting both the point and its reply together, or retaining
both cached values on rejection. -/
def RegularizationState.advance (P : RegularizationParameters)
    (a : RegularizationState n p) (R : Reply n p) : RegularizationState n p :=
  let rho := a.ratio R
  ⟨if P.eta1 ≤ rho then a.trial else a.point,
    if P.eta1 ≤ rho then R else a.cached, updatedSigma P rho a.sigma⟩

/-- Replay all finite raw replies, starting with the response to the compulsory origin query.
No consistency with any objective is required. -/
noncomputable def replay (P : RegularizationParameters) :
    (k : ℕ) → (Fin (k + 1) → Reply n p) → RegularizationState n p
  | 0, R => ⟨0, R 0, P.sigmaMin⟩
  | k + 1, R => (replay P k (fun i => R i.castSucc)).advance P (R (Fin.last (k + 1)))
termination_by k _ => k

/-- A single dimension-polymorphic order-p oracle method, determined before the objective.
It always uses a global regularized-model minimizer and queries every trial. -/
def regularizationMethod (P : RegularizationParameters) (p : ℕ) : Method p :=
  ⟨fun _ k R => (replay P k R).trial⟩

/-- The implementation's replayed state on actual oracle replies. -/
def actualState (P : RegularizationParameters) (f : Space n → ℝ) (k : ℕ) :
    RegularizationState n p :=
  replay P k (fun i => oracle p f ((regularizationMethod P p).iterate f i.val))

/-- Initial actual state has the origin reply and the chosen positive parameter floor. -/
@[simp] theorem actualState_zero (P : RegularizationParameters) (f : Space n → ℝ) :
    actualState (p := p) P f 0 = ⟨0, oracle p f 0, P.sigmaMin⟩ := by
  simp only [actualState, replay, Fin.val_zero, Method.iterate_zero]

/-- The next actual oracle query is exactly the outstanding trial of the replayed state. -/
theorem regularizationMethod_query_succ (P : RegularizationParameters)
    (f : Space n → ℝ) (k : ℕ) :
    (regularizationMethod P p).iterate f (k + 1) = (actualState (p := p) P f k).trial := by
  rw [Method.iterate_succ]
  rfl

/-- Finite-history replay consumes precisely the next actual trial response. -/
theorem actualState_succ (P : RegularizationParameters) (f : Space n → ℝ) (k : ℕ) :
    actualState (p := p) P f (k + 1) =
      (actualState (p := p) P f k).advance P (oracle p f ((actualState (p := p) P f k).trial)) := by
  unfold actualState
  rw [replay]
  simp only [Fin.val_castSucc, Fin.val_last, regularizationMethod_query_succ]
  rfl

/-- Every actual replay cache is the full true jet at the current accepted point. -/
theorem actualState_cached (P : RegularizationParameters) (f : Space n → ℝ) (k : ℕ) :
    (actualState (p := p) P f k).cached = oracle p f (actualState (p := p) P f k).point := by
  classical
  induction k with
  | zero => simp
  | succ k ih =>
    rw [actualState_succ]
    simp only [RegularizationState.advance]
    split_ifs <;> simp_all

/-- The positive regularization floor holds at all actual states. -/
theorem actualState_sigma_lower (P : RegularizationParameters) (f : Space n → ℝ) (k : ℕ) :
    P.sigmaMin ≤ (actualState (p := p) P f k).sigma := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [actualState_succ]
    exact updatedSigma_lower P _ _ ih

/-- Every accepted point has already been queried, including after any number of rejections. -/
theorem actualState_point_queried (P : RegularizationParameters) (f : Space n → ℝ) (k : ℕ) :
    ∃ j ≤ k, (actualState (p := p) P f k).point = (regularizationMethod P p).iterate f j := by
  classical
  induction k with
  | zero => exact ⟨0, le_rfl, by simp⟩
  | succ k ih =>
    rw [actualState_succ]
    simp only [RegularizationState.advance]
    split_ifs
    · exact ⟨k + 1, le_rfl, (regularizationMethod_query_succ P f k).symm⟩
    · obtain ⟨j, hj, heq⟩ := ih
      exact ⟨j, by omega, heq⟩

/-- On actual replies, the implementation's ratio is the source's actual Taylor ratio. -/
theorem actualState_ratio (P : RegularizationParameters) (f : Space n → ℝ) (k : ℕ) :
    (actualState (p := p) P f k).ratio (oracle p f (actualState (p := p) P f k).trial) =
      HigherOrderRegularization.ratio f p (actualState (p := p) P f k).point
        (actualState (p := p) P f k).step := by
  classical
  simp only [RegularizationState.ratio, HigherOrderRegularization.ratio,
    actualState_cached, oracle_value, oracle_taylor, RegularizedTaylorModel.taylorModel_zero,
    RegularizationState.trial]

/-- The accepted-point recursion is exactly the canonical acceptance rule. -/
theorem actualState_point_succ (P : RegularizationParameters) (f : Space n → ℝ) (k : ℕ) :
    (actualState (p := p) P f (k + 1)).point =
      if P.eta1 ≤ HigherOrderRegularization.ratio f p (actualState (p := p) P f k).point
        (actualState (p := p) P f k).step then
      (actualState (p := p) P f k).point + (actualState (p := p) P f k).step
      else (actualState (p := p) P f k).point := by
  rw [actualState_succ]
  simp only [RegularizationState.advance]
  rw [actualState_ratio]
  rfl

/-- The actual scalar parameter uses the same ratio and the chosen legal interval update. -/
theorem actualState_sigma_succ (P : RegularizationParameters) (f : Space n → ℝ) (k : ℕ) :
    (actualState (p := p) P f (k + 1)).sigma = updatedSigma P
      (HigherOrderRegularization.ratio f p (actualState (p := p) P f k).point
        (actualState (p := p) P f k).step) (actualState (p := p) P f k).sigma := by
  rw [actualState_succ]
  simp only [RegularizationState.advance, actualState_ratio]

/-- The replayed trial is the deterministic minimizer of the true current model. -/
theorem actualState_step (P : RegularizationParameters) (f : Space n → ℝ) (k : ℕ) :
    (actualState (p := p) P f k).step =
      (oracle p f (actualState (p := p) P f k).point).minimizer
        (actualState (p := p) P f k).sigma := by
  simp only [RegularizationState.step, actualState_cached]

/-- Every finite prefix before a failed first-order stopping test is a legal ARp prefix.
The legal model-step existence is proved by the raw-reply minimizer construction. -/
theorem actualState_runPrefix (P : RegularizationParameters) (hp : 1 ≤ p)
    {f : Space n → ℝ} (hf : ContDiff ℝ p f) {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (N : ℕ) (hfirst : ∀ k < N, ¬Stationary 1 (fun _ => epsilon) f
      (actualState (p := p) P f k).point
      (directionSequence p (1 / 2) epsilon f
        (fun i => (actualState (p := p) P f i).point) (fun i => (actualState (p := p) P f i).step)
        (fun i => (actualState (p := p) P f i).sigma) k)) :
    RunPrefix P 1 p (fun _ => 1 / 2) (fun _ => epsilon) f
      (fun i => (actualState (p := p) P f i).point) (fun i => (actualState (p := p) P f i).step)
      (fun i => (actualState (p := p) P f i).sigma) N := by
  refine ⟨⟨⟨by simp, ?_⟩, ?_, ?_⟩, by decide, by decide, hp,
    by norm_num, by norm_num, fun _ _ => hepsilon, ?_⟩
  · intro k _
    rw [actualState_sigma_succ]
    exact updatedSigma_mem P _ _ (actualState_sigma_lower (p := p) P f k)
  · intro k hk
    have hg : fderiv ℝ f (actualState (p := p) P f k).point ≠ 0 := by
      intro hz
      apply hfirst k hk
      simp only [stationary_one_iff, hz, norm_zero]
      exact hepsilon.le
    rw [actualState_step]
    exact oracle_minimizer_strict hp hf _
      (P.sigmaMin_pos.trans_le (actualState_sigma_lower (p := p) P f k)) hg
  · intro k _
    exact actualState_point_succ (p := p) P f k
  · intro k _
    refine ⟨?_, by omega, by omega⟩
    rw [actualState_step, oracle_minimizer_fderiv _ _
      (P.sigmaMin_pos.trans_le (actualState_sigma_lower (p := p) P f k)), norm_zero]
    positivity

/-- First-order termination at an accepted point implies actual oracle attainment by that
trial index. Rejected trial queries are included in the index. -/
theorem actualState_firstStationaryTime_le (P : RegularizationParameters)
    (f : Space n → ℝ) {epsilon : ℝ} {K : ℕ}
    (hK : ‖fderiv ℝ f (actualState (p := p) P f K).point‖ ≤ epsilon) :
    firstStationaryTime f ((regularizationMethod P p).iterate f) epsilon ≤ K := by
  obtain ⟨j, hj, heq⟩ := actualState_point_queried (p := p) P f K
  apply (firstStationaryTime_le_natCast_iff _ _ _).mpr
  refine ⟨j, hj, ?_⟩
  rw [← heq]
  simpa only [gradient, LinearIsometryEquiv.norm_map] using hK

/-- Fixed acceptance and update ratios, with the regularization floor scaled to the
requested derivative Lipschitz budget. The maximum makes the interface total for all inputs. -/
def regularizationParameters (L : ℝ) : RegularizationParameters where
  eta1 := 1 / 4
  eta2 := 1 / 2
  gamma1 := 1 / 2
  gamma2 := 2
  gamma3 := 3
  sigmaMin := max 1 L
  eta1_pos := by norm_num
  eta_le := by norm_num
  eta2_lt_one := by norm_num
  gamma1_pos := by norm_num
  gamma1_lt_one := by norm_num
  one_lt_gamma2 := by norm_num
  gamma2_lt_gamma3 := by norm_num
  sigmaMin_pos := lt_of_lt_of_le zero_lt_one (le_max_left _ _)

/-- The dimension-independent trial-cost budget for this actual oracle implementation.
Only the real-power denominator depends on the requested tolerance. -/
def regularizationCost (p : ℕ) (Delta L epsilon : ℝ) : ℝ :=
  let P := regularizationParameters L
  let S := max P.sigmaMin (P.gamma3 * (L / (1 - P.eta2)))
  let C := 1 + |Real.log P.gamma1| / Real.log P.gamma2
  let D := Real.log (S / P.sigmaMin) / Real.log P.gamma2
  C * (firstOrderComplexityConstant P p L S (1 / 2) *
    (Delta / epsilon ^ (((p + 1 : ℕ) : ℝ) / p))) + C + D + 1

end Optimization.DerivativeOracle
