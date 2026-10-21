import Numlib.Optimization.ExplicitRegularizationRequestRatios
import Numlib.Optimization.InexactRegularizationDecrease
import Numlib.Optimization.InexactRegularizationRefinementBounds

/-!
# Uniform regularization bounds for actual known-error trials

The quantitative objective-model remainder leaves half of the successful-ratio margin for
both approximate endpoint values. Cached current values satisfy the same allowance because
their original requests are no larger. Literal checked first-order accuracy and proportional
tensor requests control every model coefficient, while long steps use the independent cap.
All operational parameter intervals then yield a uniform initialization-dependent bound.
-/

noncomputable section
open scoped Nat
namespace Optimization.ExplicitRegularization
open InexactTaylorModels InexactRegularization
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Full-order coefficient scaling controls the actual objective decrement error. This
quantitative estimate keeps its complete constant for subsequent inexact-value ratios. -/
theorem objective_decrement_error_le_step_power {f : E → ℝ} {x s : E}
    {A : Coefficients E} {p : ℕ} {L κ : ℝ} (hp : 1 ≤ p)
    (hf : HigherOrderRegularization.DiagonalLipschitz f p L) (hκ : 0 ≤ κ)
    (hcoeff : ∀ i ∈ Finset.Icc 1 p,
      ‖A i - iteratedFDeriv ℝ i f x‖ ≤ κ * ‖s‖ ^ (p - i + 1)) :
    |f x - f (x + s) - decrement A p s| ≤
      (L / ((p + 1)! : ℝ) + 2 * κ) * ‖s‖ ^ (p + 1) := by
  have hrem := hf.value_remainder hp x s
  have herror := decrement_error_le_step_power A (fun i => iteratedFDeriv ℝ i f x)
    s (le_refl p) (by norm_num : (0 : ℝ) ≤ 1) hκ (by simpa using hcoeff)
  rw [decrement_iteratedFDeriv, ← polynomial_error_eq f x A p s] at herror
  have heq : f x - f (x + s) - decrement A p s =
      polynomial (f x) A p s - f (x + s) := by
    rw [decrement_eq (f x), polynomial_zero]
    ring
  rw [heq, abs_sub_comm]
  calc
    _ ≤ |f (x + s) - RegularizedTaylorModel.taylorModel f p x s| +
        |RegularizedTaylorModel.taylorModel f p x s - polynomial (f x) A p s| :=
      abs_sub_le _ _ _
    _ ≤ L / ((p + 1)! : ℝ) * ‖s‖ ^ (p + 1) + 2 * κ * ‖s‖ ^ (p + 1) := by
      rw [abs_sub_comm (RegularizedTaylorModel.taylorModel f p x s)]
      exact add_le_add hrem (by simpa using herror)
    _ = _ := by ring

/-- The actual value ratio is very successful at the corrected threshold. The true
objective/model error uses half the available margin; the two known value errors use
at most the other half, including a compatible cached current endpoint. -/
theorem ValueTrial.very_successful_of_step_accuracy {P : Parameters} {f : E → ℝ}
    {O : Oracle f P.p} {a : State E} {s : E} (v : ValueTrial P O a s) {L κ : ℝ}
    (hf : HigherOrderRegularization.DiagonalLipschitz f P.p L) (hκ : 0 ≤ κ)
    (hcoeff : ∀ i ∈ Finset.Icc 1 P.p,
      ‖O.derivative a.point a.request i - iteratedFDeriv ℝ i f a.point‖ ≤
        κ * ‖s‖ ^ (P.p - i + 1))
    (hpay : a.sigma * ‖s‖ ^ (P.p + 1) / ((P.p + 1)! : ℝ) ≤
      decrement (O.derivative a.point a.request) P.p s)
    (hlarge : (2 * L + 4 * ((P.p + 1)! : ℝ) * κ) / (1 - P.eta2) ≤ a.sigma) :
    P.eta2 ≤ v.ratio := by
  have hp := v.prediction_pos
  have he := objective_decrement_error_le_step_power (P.order_pos.trans P.order_le)
    hf hκ hcoeff
  have hη : 0 < 1 - P.eta2 := sub_pos.mpr P.eta2_lt_one
  have hh := (div_le_iff₀ hη).mp hlarge
  have hbase : L / ((P.p + 1)! : ℝ) + 2 * κ ≤
      ((1 - P.eta2) / 2) * a.sigma / ((P.p + 1)! : ℝ) := by
    apply (le_div_iff₀ (by positivity : 0 < ((P.p + 1)! : ℝ))).mpr
    have hden : (((P.p + 1)! : ℝ)) ≠ 0 := by positivity
    field_simp
    nlinarith
  have he' := he.trans
    (mul_le_mul_of_nonneg_right hbase (pow_nonneg (norm_nonneg s) _))
  have hscaled := mul_le_mul_of_nonneg_left hpay (div_nonneg hη.le (by norm_num : (0 : ℝ) ≤ 2))
  have heq : ((1 - P.eta2) / 2 * a.sigma / ((P.p + 1)! : ℝ)) * ‖s‖ ^ (P.p + 1) =
      ((1 - P.eta2) / 2) * (a.sigma * ‖s‖ ^ (P.p + 1) / ((P.p + 1)! : ℝ)) := by ring
  rw [heq] at he'
  have htrue := (abs_le.mp (he'.trans hscaled)).1
  have hc := (abs_le.mp v.current_accuracy).1
  have ht := (abs_le.mp (O.value_accuracy (a.point + s) v.request v.request_pos)).2
  have hstep := (le_div_iff₀ (by norm_num : (0 : ℝ) < 4)).mp P.step_success
  have hbudget := v.budget
  have hallow := mul_le_mul_of_nonneg_right hstep hp.le
  unfold ValueTrial.ratio
  apply (le_div_iff₀ hp).mpr
  linarith

/-- Full-order errors derived from the actual literal short-step check force the actual
inexact-value ratio to be very successful beyond the corrected fixed-data threshold. -/
theorem Execution.very_successful_of_large {P : Parameters} {f : E → ℝ}
    {O : Oracle f P.p} {N : ℕ} (r : Execution P O N) {k : ℕ} (hk : k ≤ N)
    (I : Inspection P O.derivative (r.state k)) (hq : I.order ≤ P.q)
    (s : InnerResult P.toImplicitParameters 0
      (O.derivative (r.state k).point (r.state k).request)
      (r.state k).sigma I.radii (I.direction hq))
    (ha : StepAccurate P.toImplicitParameters P.q (r.state k).request s.step)
    (v : ValueTrial P O (r.state k) s.step) {L : ℝ}
    (hf : HigherOrderRegularization.DiagonalLipschitz f P.p L)
    (hlarge : (2 * L + 4 * ((P.p + 1)! : ℝ) *
      effectiveAccuracy P.toImplicitParameters (r.state 0).request) /
      (1 - P.eta2) ≤ (r.state k).sigma) : P.eta2 ≤ v.ratio := by
  have hσ : 0 ≤ (r.state k).sigma := P.sigmaMin_pos.le.trans (r.sigma_floor hk)
  have hd := InnerResult.decrement_pos I hq s hσ (r.valid_radii hk)
  apply v.very_successful_of_step_accuracy hf
    (effectiveAccuracy_pos P.toImplicitParameters _).le ?_ hd.1 hlarge
  intro i hi
  exact (O.derivative_accuracy _ _ (fun _ hj => (r.request_bounds hk hj).1) i hi).trans
    (r.step_request_le_power hk ha hi)

/-- Every actual parameter update grows by at most its largest prescribed factor. Both
accuracy refinements preserve the parameter and both trial outcomes obey their intervals. -/
theorem Transition.sigma_le_gamma3 {P : Parameters} {f : E → ℝ} {O : Oracle f P.p}
    {a b : State E} {I : Inspection P O.derivative a} {trial accepted : Bool}
    {queries : List (E × ℝ)} (t : Transition P O a I b trial accepted queries)
    (hσ : 0 ≤ a.sigma) : b.sigma ≤ P.gamma3 * a.sigma := by
  have hg : 1 ≤ P.gamma3 := (P.one_lt_gamma2.trans P.gamma2_lt_gamma3).le
  have hs : a.sigma ≤ P.gamma3 * a.sigma := le_mul_of_one_le_left hσ hg
  cases t with
  | refineInspection => exact hs
  | refineStep => exact hs
  | trial hq s hacc v next hu =>
    have hh : next ≤ P.gamma3 * a.sigma := by
      unfold HigherOrderApproximateRegularization.ParameterUpdate at hu
      split_ifs at hu
      · exact hu.2.trans hs
      · exact hu.2.trans (mul_le_mul_of_nonneg_right P.gamma2_lt_gamma3.le hσ)
      · exact hu.2
    unfold trialState
    split_ifs <;> exact hh

/-- A parameter above the corrected threshold cannot grow at an actual EDA transition.
The success is proved for its approximate endpoint ratio, including cached values. -/
theorem Execution.sigma_step_nonincrease_of_large {P : Parameters} {f : E → ℝ}
    {O : Oracle f P.p} {N : ℕ} (r : Execution P O N) {k : ℕ} (hk : k < N) {L : ℝ}
    (hf : HigherOrderRegularization.DiagonalLipschitz f P.p L)
    (hlarge : (2 * L + 4 * ((P.p + 1)! : ℝ) *
      effectiveAccuracy P.toImplicitParameters (r.state 0).request) /
      (1 - P.eta2) ≤ (r.state k).sigma) :
    (r.state (k + 1)).sigma ≤ (r.state k).sigma := by
  have ht := r.transition k hk
  generalize r.state (k + 1) = nextState at ht ⊢
  generalize r.trial k = trial at ht
  generalize r.accepted k = accepted at ht
  generalize r.queries k = queries at ht
  cases ht with
  | refineInspection => exact le_rfl
  | refineStep => exact le_rfl
  | trial hq s hacc v next hu =>
    have hv := r.very_successful_of_large hk.le (r.inspection k) hq s hacc v hf hlarge
    unfold HigherOrderApproximateRegularization.ParameterUpdate at hu
    simp only [ite_eq_left hv] at hu
    unfold trialState
    split_ifs <;> exact hu.2

/-- Every reachable parameter has a uniform bound derived from the actual known-error
oracle and literal checked execution. The fixed initial request ratios and independent
long-step cap are retained explicitly; no parameter or model-quality bound is assumed. -/
theorem Execution.sigma_upper {P : Parameters} {f : E → ℝ}
    {O : Oracle f P.p} {N : ℕ} (r : Execution P O N) {L : ℝ}
    (hf : HigherOrderRegularization.DiagonalLipschitz f P.p L) {k : ℕ} (hk : k ≤ N) :
    (r.state k).sigma ≤ correctedSigmaBound P.toImplicitParameters
      (r.state 0).request (r.state 0).sigma L 1 := by
  let T := (2 * L + 4 * ((P.p + 1)! : ℝ) *
    effectiveAccuracy P.toImplicitParameters (r.state 0).request) / (1 - P.eta2)
  have hg : 0 ≤ P.gamma3 := (zero_lt_one.trans
    (P.one_lt_gamma2.trans P.gamma2_lt_gamma3)).le
  simp only [correctedSigmaBound, mul_one]
  change (r.state k).sigma ≤ max (r.state 0).sigma (P.gamma3 * T)
  induction k with
  | zero => exact le_max_left _ _
  | succ k ih =>
    have hs : 0 ≤ (r.state k).sigma := P.sigmaMin_pos.le.trans (r.sigma_floor (by omega))
    by_cases hb : T ≤ (r.state k).sigma
    · exact (r.sigma_step_nonincrease_of_large (by omega) hf hb).trans (ih (by omega))
    · exact ((r.transition k (by omega)).sigma_le_gamma3 hs).trans
        ((mul_le_mul_of_nonneg_left (le_of_not_ge hb) hg).trans (le_max_right _ _))

/-- Known unit tensor errors and a true tensor norm bound give an all-point supplied bound
for every positive request vector below an independent cap. -/
theorem _root_.Optimization.ExplicitTrustRegion.Oracle.derivative_norm_le
    {f : E → ℝ} {p : ℕ} (O : Oracle f p) {L H : ℝ}
    (htrue : ∀ x i, 1 ≤ i → i ≤ p → ‖iteratedFDeriv ℝ i f x‖ ≤ L)
    (x : E) (h : ℕ → ℝ) (hpos : ∀ i ∈ Finset.Icc 1 p, 0 < h i)
    (hcap : ∀ i ∈ Finset.Icc 1 p, h i ≤ H) {i : ℕ} (hi : i ∈ Finset.Icc 1 p) :
    ‖O.derivative x h i‖ ≤ L + H := by
  have he := O.derivative_accuracy x h hpos i hi
  have ht := htrue x i (Finset.mem_Icc.mp hi).1 (Finset.mem_Icc.mp hi).2
  have hn := norm_add_le (O.derivative x h i - iteratedFDeriv ℝ i f x)
    (iteratedFDeriv ℝ i f x)
  rw [sub_add_cancel] at hn
  linarith [hcap i hi]

/-- Every actual reachable supplied tensor is bounded by the true global jet bound plus
its independent initialization cap, uniformly over cache hits and all refinements. -/
theorem Execution.coefficient_norm_le {P : Parameters} {f : E → ℝ} {O : Oracle f P.p}
    {N : ℕ} (r : Execution P O N) {L : ℝ}
    (htrue : ∀ x i, 1 ≤ i → i ≤ P.p → ‖iteratedFDeriv ℝ i f x‖ ≤ L)
    {k i : ℕ} (hk : k ≤ N) (hi : i ∈ Finset.Icc 1 P.p) :
    ‖O.derivative (r.state k).point (r.state k).request i‖ ≤ L + P.kappaInitial :=
  O.derivative_norm_le htrue _ _ (fun _ hj => (r.request_bounds hk hj).1)
    (fun j hj => (r.request_bounds hk hj).2.trans (r.initial_request_le j hj)) hi

/-- Small uniform requests imply the literal observable known-error sum at the actual
inspected radii. This proves ErrorCheck itself, without a true-quality premise. -/
theorem Inspection.errorCheck_of_uniform_request {P : Parameters} {f : E → ℝ}
    {O : Oracle f P.p} {a : State E} (I : Inspection P O.derivative a)
    (hδ : HigherOrderApproximateRegularization.ValidRadii P.toParameters a.radii)
    {κ ε H : ℝ} (hκ : 0 ≤ κ) (hε : 0 ≤ ε) (hH : 0 ≤ H)
    (hεj : ∀ j, 1 ≤ j → j ≤ P.q → ε ≤ P.epsilon j)
    (hlower : ∀ j, 1 ≤ j → j ≤ P.q → κ * ε ≤ I.radii j)
    (hh : ∀ i ∈ Finset.Icc 1 P.p, a.request i ≤ H)
    (hsmall : 4 * (P.q ! : ℝ) * H ≤ P.fraction * κ ^ P.q * ε ^ (P.q + 1)) :
    ErrorCheck P a I := by
  intro j hj hjq
  have hv := I.valid_radii hδ j hj hjq
  have hb : 4 * (P.q ! : ℝ) * 1 * (H / P.fraction) ≤
      1 * κ ^ P.q * ε ^ (P.q + 1) := by
    simp only [mul_one, ← mul_div_assoc]
    apply (div_le_iff₀ P.fraction_pos).mpr
    nlinarith [hsmall]
  have hbudget := uniform_error_budget hjq hκ hε (hεj j hj hjq) ⟨hv.1.le, hv.2⟩
    (hlower j hj hjq) (by norm_num : (0 : ℝ) ≤ 1)
    (div_nonneg hH P.fraction_pos.le) (by norm_num : (1 : ℝ) ≤ 1) hb
  have hscaled := mul_le_mul_of_nonneg_left hbudget P.fraction_pos.le
  have hcancel : P.fraction * (2 * 1 * (H / P.fraction)) = 2 * H := by
    field_simp [P.fraction_pos.ne']
  rw [hcancel] at hscaled
  apply (error_sum_le ⟨hv.1.le, hv.2⟩ hH ?_).trans
  · simpa only [mul_div_assoc, mul_assoc] using hscaled
  · intro i hi
    exact hh i (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hi).1,
      (Finset.mem_Icc.mp hi).2.trans (hjq.trans P.order_le)⟩)

end Optimization.ExplicitRegularization

namespace Optimization.ExplicitRegularization
open InexactTaylorModels InexactRegularization
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The actual EDA transition preserves a common historical radius floor. Refinements
restore incoming radii, rejection retains inspected radii, and short accepted returns use
their genuine detailed-inner radius bound. No unit-radius state invariant is assumed. -/
theorem Transition.radii_lower {P : Parameters} {f : E → ℝ} {O : Oracle f P.p}
    {a b : State E} {I : Inspection P O.derivative a} {trial accepted : Bool}
    {queries : List (E × ℝ)} (t : Transition P O a I b trial accepted queries)
    {M S : ℝ} (hM : 1 ≤ M) (hσ0 : 0 ≤ a.sigma) (hσ : a.sigma ≤ S)
    (hv : HigherOrderApproximateRegularization.ValidRadii P.toParameters a.radii)
    (hA : ∀ i ∈ Finset.Icc 1 P.p, ‖O.derivative a.point a.request i‖ ≤ M)
    {j : ℕ} (hj : 1 ≤ j) (hjq : j ≤ P.q)
    (hprev : refinementRadiusCoefficient P.toImplicitParameters M S * P.epsilon j ≤
      a.radii j) :
    refinementRadiusCoefficient P.toImplicitParameters M S * P.epsilon j ≤ b.radii j := by
  have hB : 0 < max M S := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hcoef : P.fraction * P.theta / (24 * max M S) ≤ 1 := by
    apply (div_le_one (by positivity : 0 < 24 * max M S)).mpr
    have hvθ : P.fraction * P.theta ≤ 1 :=
      (mul_le_mul_of_nonneg_right P.fraction_le_one P.theta_pos.le).trans
        (by simpa using P.theta_lt_one.le)
    have := le_max_left M S
    linarith
  have htarget : P.fraction * P.theta / (24 * max M S) * P.epsilon j ≤ 1 :=
    (mul_le_of_le_one_left (P.epsilon_pos j hj hjq).le hcoef).trans
      (P.epsilon_lt_one j hj hjq).le
  cases t with
  | refineInspection => exact hprev
  | refineStep => exact hprev
  | trial hq s hacc v next hu =>
    have hi := le_trans (le_min le_rfl hprev)
      (I.radii_lower hM hσ hv hA hj hjq)
    unfold trialState
    split_ifs
    · change _ ≤ s.radii j
      by_cases hs : 1 ≤ ‖s.step‖
      · simpa only [InnerResult.radii, ite_eq_left hs] using hi
      · have hb := s.radii_bounds hM hσ0 hA (lt_of_not_ge hs)
        by_cases hj2 : j ≤ 2
        · rw [hb.1 j hj2]
          exact htarget
        · have hr := hb.2 j (by omega) hjq
          apply le_trans _ hr
          apply mul_le_mul_of_nonneg_right _ (P.epsilon_pos j hj hjq).le
          apply div_le_div_of_nonneg_left (mul_nonneg P.fraction_pos.le P.theta_pos.le)
            (by positivity) (by gcongr)
    · exact hi

/-- Analytic bounds on the actual supplied tensors and parameters give a historical radius
floor through every EDA branch, including rejected trials and both refinements. -/
theorem Execution.radii_lower_of_bounds {P : Parameters} {f : E → ℝ} {O : Oracle f P.p}
    {N : ℕ} (r : Execution P O N) {M S : ℝ} (hM : 1 ≤ M)
    (hσ : ∀ k, k ≤ N → (r.state k).sigma ≤ S)
    (hA : ∀ k < N, ∀ i ∈ Finset.Icc 1 P.p,
      ‖O.derivative (r.state k).point (r.state k).request i‖ ≤ M)
    {k : ℕ} (hk : k ≤ N) {j : ℕ} (hj : 1 ≤ j) (hjq : j ≤ P.q) :
    refinementRadiusCoefficient P.toImplicitParameters M S * P.epsilon j ≤
      (r.state k).radii j := by
  induction k with
  | zero =>
    apply le_trans _ (r.initial_tolerance j hj hjq)
    exact mul_le_of_le_one_left (P.epsilon_pos j hj hjq).le
      (prescribedRadiusCoefficient_le_one P.toImplicitParameters hM)
  | succ k ih =>
    exact (r.transition k (by omega)).radii_lower hM
      (P.sigmaMin_pos.le.trans (r.sigma_floor (by omega))) (hσ k (by omega))
      (r.valid_radii (by omega)) (hA k (by omega)) hj hjq (ih (by omega))

/-- Historical incoming radii and the actual current searches give the same floor for every
inspected radius, including an all-pass inspection whose error check may still fail. -/
theorem Execution.inspection_radii_lower_of_bounds {P : Parameters} {f : E → ℝ}
    {O : Oracle f P.p} {N : ℕ} (r : Execution P O N) {M S : ℝ} (hM : 1 ≤ M)
    (hσ : ∀ k, k ≤ N → (r.state k).sigma ≤ S)
    (hA : ∀ k, k ≤ N → ∀ i ∈ Finset.Icc 1 P.p,
      ‖O.derivative (r.state k).point (r.state k).request i‖ ≤ M)
    (I : Inspection P O.derivative (r.state N)) {j : ℕ} (hj : 1 ≤ j) (hjq : j ≤ P.q) :
    refinementRadiusCoefficient P.toImplicitParameters M S * P.epsilon j ≤ I.radii j :=
  le_trans (le_min le_rfl
    (r.radii_lower_of_bounds hM hσ (fun k hk => hA k hk.le) le_rfl hj hjq))
    (I.radii_lower hM (hσ N le_rfl) (r.valid_radii le_rfl) (hA N le_rfl) hj hjq)

/-- The corrected sigma bound is derived internally from the actual ratio. Together with
an analytic supplied-tensor bound it gives the actual inspected-radius floor at the endpoint. -/
theorem Execution.inspection_radii_lower {P : Parameters} {f : E → ℝ}
    {O : Oracle f P.p} {N : ℕ} (r : Execution P O N) {L M : ℝ} (hM : 1 ≤ M)
    (hf : HigherOrderRegularization.DiagonalLipschitz f P.p L)
    (hA : ∀ k, k ≤ N → ∀ i ∈ Finset.Icc 1 P.p,
      ‖O.derivative (r.state k).point (r.state k).request i‖ ≤ M)
    (I : Inspection P O.derivative (r.state N)) {j : ℕ} (hj : 1 ≤ j) (hjq : j ≤ P.q) :
    refinementRadiusCoefficient P.toImplicitParameters M
      (correctedSigmaBound P.toImplicitParameters (r.state 0).request (r.state 0).sigma L 1) *
      P.epsilon j ≤ I.radii j :=
  r.inspection_radii_lower_of_bounds hM (fun _ hk => r.sigma_upper hf hk) hA I hj hjq

/-- Below the polynomial threshold the actual retained inner result passes all tensor
checks. The corrected sigma and historical radius floor are derived from the execution. -/
theorem Execution.stepAccurate_of_uniform_request {P : Parameters} {f : E → ℝ}
    {O : Oracle f P.p} {N : ℕ} (r : Execution P O N) {L M : ℝ} (hM : 1 ≤ M)
    (hf : HigherOrderRegularization.DiagonalLipschitz f P.p L)
    (hA : ∀ k, k ≤ N → ∀ i ∈ Finset.Icc 1 P.p,
      ‖O.derivative (r.state k).point (r.state k).request i‖ ≤ M)
    (I : Inspection P O.derivative (r.state N)) (hq : I.order ≤ P.q)
    (s : InnerResult P.toImplicitParameters 0 (O.derivative (r.state N).point (r.state N).request)
      (r.state N).sigma I.radii (I.direction hq))
    {ε : ℝ} (hε : 0 ≤ ε) (hεj : ∀ j, 1 ≤ j → j ≤ P.q → ε ≤ P.epsilon j)
    (hh : ∀ i ∈ Finset.Icc 1 P.p, (r.state N).request i ≤
      refinementThreshold P.toImplicitParameters M
        (correctedSigmaBound P.toImplicitParameters (r.state 0).request (r.state 0).sigma L 1)
        1 ε) :
    StepAccurate P.toImplicitParameters P.p (r.state N).request s.step := by
  let S := correctedSigmaBound P.toImplicitParameters (r.state 0).request (r.state 0).sigma L 1
  let κ := refinementRadiusCoefficient P.toImplicitParameters M S
  have hκ : 0 ≤ κ := (refinementRadiusCoefficient_pos P.toImplicitParameters (S := S) hM).le
  have hMS : 0 < max M S := zero_lt_one.trans_le (hM.trans (le_max_left _ _))
  have hvf := P.fraction_pos
  by_cases hs : 1 ≤ ‖s.step‖
  · exact Or.inl hs
  · have hlo := s.norm_lower I hq hM
      (P.sigmaMin_pos.le.trans (r.sigma_floor le_rfl)) (hA N le_rfl)
      (r.valid_radii le_rfl) hκ hε (hεj _ I.order_pos hq)
      ((mul_le_mul_of_nonneg_left (hεj _ I.order_pos hq) hκ).trans
        (r.inspection_radii_lower hM hf hA I I.order_pos hq)) (le_of_not_ge hs)
    have hMσ : max M (r.state N).sigma ≤ max M S := max_le_max_left M (r.sigma_upper hf le_rfl)
    have hM0 : 0 < max M (r.state N).sigma :=
      lt_of_lt_of_le (by linarith) (le_max_left _ _)
    have hlo' : (P.fraction * κ ^ P.q / (12 * (P.q ! : ℝ) * max M S)) *
        ε ^ (P.q + 1) ≤ ‖s.step‖ := by
      apply le_trans _ hlo
      rw [div_mul_eq_mul_div]
      apply div_le_div_of_nonneg_left (by positivity) (by positivity) (by gcongr)
    apply InexactRegularization.stepAccurate_of_uniform_request (by positivity) hlo'
    intro i hi
    have hh' := (hh i hi).trans (refinementThreshold_le_step P.toImplicitParameters hε)
    change (r.state N).request i ≤ P.kappaStep *
      (P.fraction * κ ^ P.q / (12 * (P.q ! : ℝ) * max M S)) ^ P.p *
        ε ^ (P.p * (P.q + 1)) at hh'
    convert hh' using 1
    rw [mul_pow, ← pow_mul]
    ring

/-- An all-pass inspection below the same polynomial threshold is actually Certified.
The conclusion is the observable error check at the inspected radii, rather than existence
of true criteria at some other radii. Parameter and radius bounds are derived internally. -/
theorem Execution.certified_of_uniform_request {P : Parameters} {f : E → ℝ}
    {O : Oracle f P.p} {N : ℕ} (r : Execution P O N) {L M : ℝ} (hM : 1 ≤ M)
    (hf : HigherOrderRegularization.DiagonalLipschitz f P.p L)
    (hA : ∀ k, k ≤ N → ∀ i ∈ Finset.Icc 1 P.p,
      ‖O.derivative (r.state k).point (r.state k).request i‖ ≤ M)
    (I : Inspection P O.derivative (r.state N)) (hall : I.order = P.q + 1)
    {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hεj : ∀ j, 1 ≤ j → j ≤ P.q → ε ≤ P.epsilon j)
    (hh : ∀ i ∈ Finset.Icc 1 P.p, (r.state N).request i ≤
      refinementThreshold P.toImplicitParameters M
        (correctedSigmaBound P.toImplicitParameters (r.state 0).request (r.state 0).sigma L 1)
        1 ε) : Certified P (r.state N) I := by
  let S := correctedSigmaBound P.toImplicitParameters (r.state 0).request (r.state 0).sigma L 1
  let κ := refinementRadiusCoefficient P.toImplicitParameters M S
  have hκ : 0 ≤ κ := (refinementRadiusCoefficient_pos P.toImplicitParameters (S := S) hM).le
  refine ⟨hall, I.errorCheck_of_uniform_request (r.valid_radii le_rfl) hκ hε
    (mul_nonneg (refinementAccuracyCoefficient_pos P.toImplicitParameters
      (S := S) hM (by norm_num : (0 : ℝ) ≤ 1)).le (pow_nonneg hε _)) hεj ?_ hh ?_⟩
  · intro j hj hjq
    exact (mul_le_mul_of_nonneg_left (hεj j hj hjq) hκ).trans
      (r.inspection_radii_lower hM hf hA I hj hjq)
  · simpa only [mul_one, refinementThreshold, refinementRadiusCoefficient, κ] using
      (refinementThreshold_inspection_budget P.toImplicitParameters hM
        (by norm_num : (0 : ℝ) ≤ 1) hε hε1)

/-- At every actual nonterminal iteration, uniform requests below the polynomial threshold
exclude both accuracy-refinement constructors. An all-pass inspection would be observably
Certified; otherwise the actual inner return passes the literal checked range. No failure
of true point quality, stopping certificate, parameter bound, or radius floor is assumed. -/
theorem Execution.trial_of_small_uniform_request {P : Parameters} {f : E → ℝ}
    {O : Oracle f P.p} {N : ℕ} (r : Execution P O N) {L M : ℝ} (hM : 1 ≤ M)
    (hf : HigherOrderRegularization.DiagonalLipschitz f P.p L)
    (hA : ∀ k, k ≤ N → ∀ i ∈ Finset.Icc 1 P.p,
      ‖O.derivative (r.state k).point (r.state k).request i‖ ≤ M)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hεj : ∀ j, 1 ≤ j → j ≤ P.q → ε ≤ P.epsilon j)
    {k : ℕ} (hk : k < N)
    (hh : ∀ i ∈ Finset.Icc 1 P.p, (r.state k).request i ≤
      refinementThreshold P.toImplicitParameters M
        (correctedSigmaBound P.toImplicitParameters (r.state 0).request (r.state 0).sigma L 1)
        1 ε) : r.trial k = true := by
  have hε1 : ε ≤ 1 := (hεj 1 le_rfl P.order_pos).trans (P.epsilon_lt_one 1 le_rfl P.order_pos).le
  let u := r.prefix hk.le
  have hAu : ∀ l, l ≤ k → ∀ i ∈ Finset.Icc 1 P.p,
      ‖O.derivative (u.state l).point (u.state l).request i‖ ≤ M :=
    fun l hl => hA l (hl.trans hk.le)
  have ht := r.transition k hk
  generalize r.state (k + 1) = nextState at ht
  generalize r.trial k = trial at ht ⊢
  generalize r.accepted k = accepted at ht
  generalize r.queries k = queries at ht
  cases ht with
  | refineInspection hall herr =>
    exact (herr (u.certified_of_uniform_request hM hf hAu (r.inspection k)
      hall hε hε1 hεj hh).2).elim
  | refineStep hq s herr =>
    exact (herr ((u.stepAccurate_of_uniform_request hM hf hAu (r.inspection k)
      hq s hε hεj hh).of_le P.order_le)).elim
  | trial => rfl

end Optimization.ExplicitRegularization
