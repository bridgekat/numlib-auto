import Numlib.Optimization.InexactRegularizationRequestRatios
import Numlib.Optimization.InexactRegularizationTransfer

/-!
# Actual trial decreases with proportional derivative requests

A checked first request controls every supplied derivative order through its fixed initial
request ratios. Combined with the derived uniform parameter bound, a genuine failed
successor criterion yields both source step-size regimes and a positive predicted decrease.
Long steps use their regularizer payment directly and retain their actual inherited radii.
Operational trial extraction links acceptance, parameter intervals, points and derivative
caches to the resulting objective decrease. No decrease or parameter bound is assumed.
-/

noncomputable section
open scoped Nat
namespace Optimization.InexactRegularization
open InexactTaylorModels

/-- The uniform parameter bound with explicit fixed initialization data and request-ratio
amplification. Its formula contains no tolerance values. -/
def correctedSigmaBound (P : Parameters) (h0 : ℕ → ℝ) (σ0 L K : ℝ) : ℝ :=
  max σ0 (P.gamma3 * ((2 * L + 4 * ((P.p + 1)! : ℝ) * effectiveAccuracy P h0 * K) /
    (1 - P.eta2)))

/-- The initialized parameter is bounded by the corrected uniform bound. -/
theorem initial_le_correctedSigmaBound (P : Parameters) (h0 : ℕ → ℝ) (σ0 L K : ℝ) :
    σ0 ≤ correctedSigmaBound P h0 σ0 L K := le_max_left _ _

/-- A positive initialized parameter makes the corrected uniform bound positive. -/
theorem correctedSigmaBound_pos (P : Parameters) (h0 : ℕ → ℝ) {σ0 : ℝ}
    (hσ0 : 0 < σ0) (L K : ℝ) : 0 < correctedSigmaBound P h0 σ0 L K :=
  hσ0.trans_le (initial_le_correctedSigmaBound P h0 σ0 L K)

/-- The genuine objective/model transfer constant includes the global oracle multiplier,
the fixed initial request amplification and the derived uniform parameter bound. -/
def correctedTransferConstant (P : Parameters) (h0 : ℕ → ℝ) (σ0 L K : ℝ) : ℝ :=
  L + correctedSigmaBound P h0 σ0 L K + 3 * (K * requestAmplification P.p h0) * P.kappaStep

/-- Normalized global smoothness makes the corrected transfer constant at least one. -/
theorem one_le_correctedTransferConstant (P : Parameters) (h0 : ℕ → ℝ)
    {σ0 L K : ℝ} (hσ0 : 0 ≤ σ0) (hL : 1 ≤ L) (hK : 0 ≤ K) :
    1 ≤ correctedTransferConstant P h0 σ0 L K := by
  have hS := hσ0.trans (initial_le_correctedSigmaBound P h0 σ0 L K)
  have he : 0 ≤ 3 * (K * requestAmplification P.p h0) * P.kappaStep := by
    exact mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg hK
      (zero_le_one.trans (one_le_requestAmplification _ _)))) P.kappaStep_pos.le
  dsimp only [correctedTransferConstant]
  linarith

/-- The corrected model-decrease coefficient is positive for fixed positive radius data. -/
theorem corrected_decrease_coefficient_pos (P : Parameters) (h0 : ℕ → ℝ)
    {σ0 L K κ : ℝ} (hσ0 : 0 ≤ σ0) (hL : 1 ≤ L) (hK : 0 ≤ K) (hκ : 0 < κ) :
    0 < HigherOrderApproximateRegularization.modelDecreaseConstant P.p P.q P.order_pos P.theta
      (correctedTransferConstant P h0 σ0 L K) κ P.sigmaMin :=
  HigherOrderApproximateRegularization.modelDecreaseConstant_pos P.p P.q P.order_pos
    P.theta_lt_one (zero_lt_one.trans_le (one_le_correctedTransferConstant P h0 hσ0 hL hK))
    hκ P.sigmaMin_pos

/-- The uniform model-radius coefficient obtained from supplied tensor and parameter bounds. -/
def prescribedRadiusCoefficient (P : Parameters) (M S : ℝ) : ℝ :=
  P.fraction * P.theta / (24 * max M S)

/-- A normalized supplied tensor bound gives a strictly positive radius coefficient. -/
theorem prescribedRadiusCoefficient_pos (P : Parameters) {M S : ℝ} (hM : 1 ≤ M) :
    0 < prescribedRadiusCoefficient P M S := by
  have hm : 0 < max M S := zero_lt_one.trans_le (hM.trans (le_max_left _ _))
  exact div_pos (mul_pos P.fraction_pos P.theta_pos) (by positivity)

/-- The same normalized radius coefficient is at most one. -/
theorem prescribedRadiusCoefficient_le_one (P : Parameters) {M S : ℝ} (hM : 1 ≤ M) :
    prescribedRadiusCoefficient P M S ≤ 1 := by
  have hm : 1 ≤ max M S := hM.trans (le_max_left _ _)
  have hn := mul_le_of_le_one_left P.theta_pos.le P.fraction_le_one
  apply (div_le_one (by positivity : 0 < (24 : ℝ) * max M S)).mpr
  nlinarith [P.theta_lt_one]

/-- The prescribed returned model radii have unit low-order components and a fixed positive
coefficient times the tolerance as a lower bound at higher active orders. This concerns
radius choices alone, independently of any gap, step-size or decrease conclusion. -/
structure PrescribedModelRadii (P : Parameters) (κ : ℝ) (δ : ℕ → ℝ) : Prop where
  /-- Orders one and two use the unit ball. -/
  unit_low : ∀ j, 1 ≤ j → j ≤ P.q → j ≤ 2 → δ j = 1
  /-- Higher active orders retain the prescribed tolerance radius floor. -/
  lower_high : ∀ j, 3 ≤ j → j ≤ P.q → κ * P.epsilon j ≤ δ j

/-- The prescribed component radii imply both scalar radius regimes. -/
theorem PrescribedModelRadii.regimes {P : Parameters} {κ : ℝ} {δ : ℕ → ℝ}
    (h : PrescribedModelRadii P κ δ) (hκ : κ ≤ 1) :
    (P.q ≤ 2 → ∀ j, 1 ≤ j → j ≤ P.q → δ j = 1) ∧
      (2 < P.q → ∀ j, 1 ≤ j → j ≤ P.q → κ * P.epsilon j ≤ δ j) :=
  HigherOrderApproximateRegularization.regime_radii_of_unit_low_and_lower_high
    P.toParameters hκ h.unit_low h.lower_high

section Normed
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {checked : ℕ}

/-- Data of an actual trial transition, retaining the completed inspection, detailed inner
return, literal checked accuracy, exact ratio update, successor state and acceptance flag. -/
structure ExecutedTrial (P : Parameters) (checked : ℕ) (f : E → ℝ)
    (oracle : E → (ℕ → ℝ) → Coefficients E) (a b : State E) (accepted : Bool) where
  /-- The actual completed source inspection. -/
  inspection : Inspection P (f a.point) (oracle a.point a.request) a.sigma a.radii
  /-- The inspection selected a genuine failing order. -/
  order_le : inspection.order ≤ P.q
  /-- The actual returned detailed inner execution. -/
  inner : InnerResult P (f a.point) (oracle a.point a.request) a.sigma inspection.radii
    (inspection.direction order_le)
  /-- The literal checked degrees passed, or the step uses the long-step exemption. -/
  accurate : StepAccurate P checked a.request inner.step
  /-- The regularization parameter selected by the actual update. -/
  nextSigma : ℝ
  /-- The actual source parameter interval for its genuine objective ratio. -/
  update : HigherOrderApproximateRegularization.ParameterUpdate P.toParameters
    (ratio P f oracle a inner.step) a.sigma nextSigma
  /-- The accepted or rejected successor, including its actual tensor cache. -/
  next_state : b = if P.eta1 ≤ ratio P f oracle a inner.step then
    ⟨a.point + inner.step, nextSigma, inner.radii, a.request, true⟩ else
    ⟨a.point, nextSigma, inspection.radii, a.request, false⟩
  /-- The actual acceptance flag is computed from the full supplied Taylor prediction. -/
  accepted_eq : accepted = decide (P.eta1 ≤ ratio P f oracle a inner.step)

/-- Every actual trial transition provides precisely its operational trial witnesses. -/
theorem Transition.exists_executedTrial {P : Parameters} {f : E → ℝ}
    {oracle : E → (ℕ → ℝ) → Coefficients E} {a b : State E} {trial accepted : Bool}
    (t : Transition P checked f oracle a b trial accepted) (ht : trial = true) :
    Nonempty (ExecutedTrial P checked f oracle a b accepted) := by
  cases t with
  | refineInspection => cases ht
  | refineStep => cases ht
  | trial I hq s ha next hu =>
    exact ⟨⟨I, hq, s, ha, next, hu, rfl, rfl⟩⟩

/-- Actual acceptance is equivalent to the source threshold on the actual trial ratio. -/
theorem ExecutedTrial.accepted_iff {P : Parameters} {f : E → ℝ}
    {oracle : E → (ℕ → ℝ) → Coefficients E} {a b : State E} {accepted : Bool}
    (t : ExecutedTrial P checked f oracle a b accepted) :
    accepted = true ↔ P.eta1 ≤ ratio P f oracle a t.inner.step := by
  constructor
  · intro ha
    simpa using t.accepted_eq.symm.trans ha
  · intro ha
    exact t.accepted_eq.trans (by simp [ha])

/-- The chosen update is the parameter recorded in the actual successor state. -/
theorem ExecutedTrial.next_sigma {P : Parameters} {f : E → ℝ}
    {oracle : E → (ℕ → ℝ) → Coefficients E} {a b : State E} {accepted : Bool}
    (t : ExecutedTrial P checked f oracle a b accepted) : b.sigma = t.nextSigma := by
  have h := congrArg State.sigma t.next_state
  split_ifs at h <;> exact h

/-- Both trial decisions retain the exact derivative request key. -/
theorem ExecutedTrial.next_request {P : Parameters} {f : E → ℝ}
    {oracle : E → (ℕ → ℝ) → Coefficients E} {a b : State E} {accepted : Bool}
    (t : ExecutedTrial P checked f oracle a b accepted) : b.request = a.request := by
  have h := congrArg State.request t.next_state
  split_ifs at h <;> exact h

/-- The derivative cache is fresh exactly after an accepted actual trial. -/
theorem ExecutedTrial.next_fresh {P : Parameters} {f : E → ℝ}
    {oracle : E → (ℕ → ℝ) → Coefficients E} {a b : State E} {accepted : Bool}
    (t : ExecutedTrial P checked f oracle a b accepted) : b.fresh = accepted := by
  have h := congrArg State.fresh t.next_state
  have he : b.fresh = decide (P.eta1 ≤ ratio P f oracle a t.inner.step) := by
    split_ifs at h with hρ <;> simpa [hρ] using h
  exact he.trans t.accepted_eq.symm

/-- An accepted actual trial moves to the returned model step. -/
theorem ExecutedTrial.accepted_point {P : Parameters} {f : E → ℝ}
    {oracle : E → (ℕ → ℝ) → Coefficients E} {a b : State E} {accepted : Bool}
    (t : ExecutedTrial P checked f oracle a b accepted) (ha : accepted = true) :
    b.point = a.point + t.inner.step := by
  have h := congrArg State.point t.next_state
  simpa only [ite_eq_left (t.accepted_iff.mp ha)] using h

/-- Acceptance retains the actual returned model radii in the successor state. -/
theorem ExecutedTrial.accepted_radii {P : Parameters} {f : E → ℝ}
    {oracle : E → (ℕ → ℝ) → Coefficients E} {a b : State E} {accepted : Bool}
    (t : ExecutedTrial P checked f oracle a b accepted) (ha : accepted = true) :
    b.radii = t.inner.radii := by
  have h := congrArg State.radii t.next_state
  simpa only [ite_eq_left (t.accepted_iff.mp ha)] using h

/-- The actual trial witnesses selected from a finite execution's operational transition. -/
def Execution.executedTrial {P : Parameters} {f : E → ℝ}
    {oracle : E → (ℕ → ℝ) → Coefficients E} {N : ℕ} (r : Execution P checked f oracle N)
    {k : ℕ} (hk : k < N) (ht : r.trial k = true) :
    ExecutedTrial P checked f oracle (r.state k) (r.state (k + 1)) (r.accepted k) :=
  Classical.choice ((r.transition k hk).exists_executedTrial ht)

/-- The corrected uniform parameter bound follows from the global oracle contract on every
reachable state; it is not an independent trial premise. -/
theorem Execution.sigma_le_correctedSigmaBound {P : Parameters} {f : E → ℝ}
    (O : InexactTrustRegion.Oracle f P.p) {N : ℕ} (r : Execution P checked f O.derivative N)
    (hchecked : 1 ≤ checked) {L K : ℝ}
    (hf : HigherOrderRegularization.DiagonalLipschitz f P.p L) (hK : 0 ≤ K)
    (hO : InexactTrustRegion.UniformAccuracy O K) {k : ℕ} (hk : k ≤ N) :
    (r.state k).sigma ≤ correctedSigmaBound P (r.state 0).request (r.state 0).sigma L K :=
  r.sigma_upper_of_oracle O hchecked hf hK hO hk

/-- Global true tensor bounds and actual oracle accuracy give a supplied coefficient norm
bound through the real initial request cap. No coefficient norm certificate is assumed. -/
theorem Execution.supplied_coefficient_norm_le {P : Parameters} {f : E → ℝ}
    (O : InexactTrustRegion.Oracle f P.p) {N : ℕ} (r : Execution P checked f O.derivative N)
    {k : ℕ} (hk : k ≤ N) {L K : ℝ} (hK : 0 ≤ K)
    (hO : InexactTrustRegion.UniformAccuracy O K) {i : ℕ} (hi : i ∈ Finset.Icc 1 P.p)
    (htrue : ‖iteratedFDeriv ℝ i f (r.state k).point‖ ≤ L) :
    ‖O.derivative (r.state k).point (r.state k).request i‖ ≤ L + K * P.kappaInitial := by
  have he := hO (r.state k).point (r.state k).request
    (fun _ hj => (r.request_bounds hk hj).1) i hi
  have hcap := (r.request_bounds hk hi).2.trans (r.initial_request_le i hi)
  calc
    _ ≤ ‖O.derivative (r.state k).point (r.state k).request i -
        iteratedFDeriv ℝ i f (r.state k).point‖ +
          ‖iteratedFDeriv ℝ i f (r.state k).point‖ := by
      simpa only [sub_add_cancel] using norm_add_le
        (O.derivative (r.state k).point (r.state k).request i -
          iteratedFDeriv ℝ i f (r.state k).point) (iteratedFDeriv ℝ i f (r.state k).point)
    _ ≤ K * (r.state k).request i + L := add_le_add he htrue
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hcap hK]

/-- Every actual long inner return pays the initialized regularization floor, independently
of the successor quality or of any prescribed radius convention. -/
theorem InnerResult.long_predicted_decrease {P : Parameters} {c : ℝ} {A : Coefficients E}
    {σ : ℝ} {δ : ℕ → ℝ} (I : Inspection P c A σ δ) (hq : I.order ≤ P.q)
    (s : InnerResult P c A σ I.radii (I.direction hq)) (hσ : P.sigmaMin ≤ σ)
    (hδ : HigherOrderApproximateRegularization.ValidRadii P.toParameters δ)
    (hs : 1 ≤ ‖s.step‖) : P.sigmaMin / ((P.p + 1)! : ℝ) ≤ decrement A P.p s.step := by
  have hd := s.decrement_pos I hq (P.sigmaMin_pos.le.trans hσ) hδ
  calc
    _ ≤ P.sigmaMin / ((P.p + 1)! : ℝ) * ‖s.step‖ ^ (P.p + 1) :=
      le_mul_of_one_le_right (div_nonneg P.sigmaMin_pos.le (by positivity)) (one_le_pow₀ hs)
    _ ≤ σ / ((P.p + 1)! : ℝ) * ‖s.step‖ ^ (P.p + 1) := by gcongr
    _ = σ * ‖s.step‖ ^ (P.p + 1) / ((P.p + 1)! : ℝ) := by ring
    _ ≤ _ := hd.1

/-- A genuine accepted long trial pays a fixed objective decrease without any true-gap or
radius-choice premise. Its successor is the actual accepted point from the transition. -/
theorem ExecutedTrial.long_objective_decrease {P : Parameters} {f : E → ℝ}
    {oracle : E → (ℕ → ℝ) → Coefficients E} {a b : State E} {accepted : Bool}
    (t : ExecutedTrial P checked f oracle a b accepted) (ha : accepted = true)
    (hσ : P.sigmaMin ≤ a.sigma)
    (hδ : HigherOrderApproximateRegularization.ValidRadii P.toParameters a.radii)
    (hs : 1 ≤ ‖t.inner.step‖) :
    P.eta1 * (P.sigmaMin / ((P.p + 1)! : ℝ)) ≤ f a.point - f b.point := by
  have hb := t.inner.long_predicted_decrease t.inspection t.order_le hσ hδ hs
  have hd := t.inner.decrement_pos t.inspection t.order_le (P.sigmaMin_pos.le.trans hσ) hδ
  have hρ := t.accepted_iff.mp ha
  change P.eta1 ≤ (f a.point - f (a.point + t.inner.step)) /
    decrement (oracle a.point a.request) P.p t.inner.step at hρ
  have hp := (le_div_iff₀ hd.2.1).mp hρ
  have hx := t.accepted_point ha
  rw [hx]
  exact (mul_le_mul_of_nonneg_left hb P.eta1_pos.le).trans hp

end Normed

section InnerProduct
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {checked : ℕ}

/-- The actual detailed short inner return supplies the prescribed model radii from a
supplied tensor norm bound and an encountered parameter bound. No model-quality or radius
certificate is assumed. -/
theorem InnerResult.prescribedModelRadii_of_bounds {P : Parameters} {c : ℝ}
    {A : Coefficients E} {σ M S : ℝ} {δ : ℕ → ℝ} {d : E}
    (s : InnerResult P c A σ δ d) (hM : 1 ≤ M) (hσ : 0 ≤ σ)
    (hA : ∀ i ∈ Finset.Icc 1 P.p, ‖A i‖ ≤ M) (hS : σ ≤ S) (hs : ‖s.step‖ < 1) :
    PrescribedModelRadii P (prescribedRadiusCoefficient P M S) s.radii := by
  have hb := s.radii_bounds hM hσ hA hs
  refine ⟨fun j _ _ hj => hb.1 j hj, fun j hj hjq => ?_⟩
  apply le_trans _ (hb.2 j hj hjq)
  apply mul_le_mul_of_nonneg_right _ (P.epsilon_pos j (by omega) hjq).le
  exact div_le_div_of_nonneg_left (mul_nonneg P.fraction_pos.le P.theta_pos.le)
    (by have := hM.trans (le_max_left M σ); positivity)
    (mul_le_mul_of_nonneg_left (max_le_max_left M hS) (by norm_num))

/-- Global oracle accuracy derives the parameter bound used by the actual inner-radius
constructor, leaving only the genuine supplied coefficient norm bound as an analytic input. -/
theorem Execution.prescribedModelRadii_of_bounds {P : Parameters} {f : E → ℝ}
    (O : InexactTrustRegion.Oracle f P.p) {N : ℕ} (r : Execution P checked f O.derivative N)
    (hchecked : 1 ≤ checked) {k : ℕ} (hk : k ≤ N)
    (I : Inspection P (f (r.state k).point) (O.derivative (r.state k).point (r.state k).request)
      (r.state k).sigma (r.state k).radii) (hq : I.order ≤ P.q)
    (s : InnerResult P (f (r.state k).point) (O.derivative (r.state k).point (r.state k).request)
      (r.state k).sigma I.radii (I.direction hq)) {L K M : ℝ}
    (hf : HigherOrderRegularization.DiagonalLipschitz f P.p L) (hK : 0 ≤ K)
    (hO : InexactTrustRegion.UniformAccuracy O K) (hM : 1 ≤ M)
    (hA : ∀ i ∈ Finset.Icc 1 P.p,
      ‖O.derivative (r.state k).point (r.state k).request i‖ ≤ M) (hs : ‖s.step‖ < 1) :
    PrescribedModelRadii P (prescribedRadiusCoefficient P M
      (correctedSigmaBound P (r.state 0).request (r.state 0).sigma L K)) s.radii :=
  s.prescribedModelRadii_of_bounds hM (P.sigmaMin_pos.le.trans (r.sigma_floor hk)) hA
    (r.sigma_le_correctedSigmaBound O hchecked hf hK hO hk) hs

/-- A true failed successor criterion yields an actual step lower bound in both source
exponent regimes. All supplied coefficient powers and the uniform parameter bound are
consequences of the global oracle contract and the initial request ratios. The prescribed
radius convention is imposed only on short returned steps. -/
theorem Execution.step_lower_bound_of_true_gap_failure {P : Parameters} {f : E → ℝ}
    (O : InexactTrustRegion.Oracle f P.p) {N : ℕ} (r : Execution P checked f O.derivative N)
    (hchecked : 1 ≤ checked) {k : ℕ} (hk : k ≤ N)
    (I : Inspection P (f (r.state k).point) (O.derivative (r.state k).point (r.state k).request)
      (r.state k).sigma (r.state k).radii) (hq : I.order ≤ P.q)
    (s : InnerResult P (f (r.state k).point) (O.derivative (r.state k).point (r.state k).request)
      (r.state k).sigma I.radii (I.direction hq))
    (ha : StepAccurate P checked (r.state k).request s.step) {L K κ : ℝ}
    (hf : HigherOrderRegularization.DiagonalLipschitz f P.p L) (hL : 1 ≤ L)
    (hK : 0 ≤ K) (hO : InexactTrustRegion.UniformAccuracy O K) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hradii : ‖s.step‖ < 1 → PrescribedModelRadii P κ s.radii)
    (hfail : ¬HigherOrderApproximateRegularization.SatisfiesCriteria P.toParameters
      f ((r.state k).point + s.step) s.radii) :
    ∃ j, 1 ≤ j ∧ j ≤ P.q ∧
      HigherOrderApproximateRegularization.stepBoundConstant P.p P.q j P.theta
        (correctedTransferConstant P (r.state 0).request (r.state 0).sigma L K) κ *
        (P.epsilon j) ^ HigherOrderApproximateRegularization.stepBoundExponent P.p P.q j ≤
          ‖s.step‖ := by
  have hσ := P.sigmaMin_pos.le.trans (r.sigma_floor hk)
  have hσ0 := P.sigmaMin_pos.le.trans r.initial_sigma
  have hS := r.sigma_le_correctedSigmaBound O hchecked hf hK hO hk
  have hR : 0 ≤ K * requestAmplification P.p (r.state 0).request :=
    mul_nonneg hK (zero_le_one.trans (one_le_requestAmplification _ _))
  have hC := one_le_correctedTransferConstant P (r.state 0).request hσ0 hL hK
  by_cases hs : ‖s.step‖ < 1
  · obtain ⟨j, hj, hjq, hb⟩ := s.transfer_of_true_gap_failure I hq hf hR hσ hS
      (r.valid_radii hk) hs (fun i hi =>
        r.short_step_coefficient_le_power O hchecked hk ha hs hK hO hi) hfail
    have hv := s.valid_radii (I.valid_radii (r.valid_radii hk)) j hj hjq
    have hm := (hradii hs).regimes hκ1
    refine ⟨j, hj, hjq, ?_⟩
    exact HigherOrderApproximateRegularization.step_lower_bound_of_transfer hj
      (hjq.trans P.order_le) (norm_nonneg _) hv.1 (zero_lt_one.trans_le hC)
      (P.epsilon_pos j hj hjq) (P.epsilon_lt_one j hj hjq).le P.theta_lt_one hκ
      (fun hq => hm.1 hq j hj hjq) (fun hq => hm.2 hq j hj hjq) hb hs.le
  · exact HigherOrderApproximateRegularization.step_lower_bound_of_one_le
      P.toParameters hC (le_of_not_gt hs)

/-- Every actual retained trial whose successor fails the true criterion pays the full
simultaneous tolerance-power model decrease. Long steps retain their actual radii and use
the uniform regularization floor; short steps use the genuine returned model tests. -/
theorem Execution.predicted_decrease_of_true_gap_failure {P : Parameters} {f : E → ℝ}
    (O : InexactTrustRegion.Oracle f P.p) {N : ℕ} (r : Execution P checked f O.derivative N)
    (hchecked : 1 ≤ checked) {k : ℕ} (hk : k ≤ N)
    (I : Inspection P (f (r.state k).point) (O.derivative (r.state k).point (r.state k).request)
      (r.state k).sigma (r.state k).radii) (hq : I.order ≤ P.q)
    (s : InnerResult P (f (r.state k).point) (O.derivative (r.state k).point (r.state k).request)
      (r.state k).sigma I.radii (I.direction hq))
    (ha : StepAccurate P checked (r.state k).request s.step) {L K κ : ℝ}
    (hf : HigherOrderRegularization.DiagonalLipschitz f P.p L) (hL : 1 ≤ L)
    (hK : 0 ≤ K) (hO : InexactTrustRegion.UniformAccuracy O K) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hradii : ‖s.step‖ < 1 → PrescribedModelRadii P κ s.radii)
    (hfail : ¬HigherOrderApproximateRegularization.SatisfiesCriteria P.toParameters
      f ((r.state k).point + s.step) s.radii) :
    HigherOrderApproximateRegularization.modelDecreaseConstant P.p P.q P.order_pos P.theta
        (correctedTransferConstant P (r.state 0).request (r.state 0).sigma L K) κ P.sigmaMin *
      HigherOrderApproximateRegularization.toleranceMeasure P.p P.q P.order_pos P.epsilon ≤
        decrement (O.derivative (r.state k).point (r.state k).request) P.p s.step := by
  have hσ := r.sigma_floor hk
  have hd := s.decrement_pos I hq (P.sigmaMin_pos.le.trans hσ) (r.valid_radii hk)
  apply HigherOrderApproximateRegularization.predicted_decrease_of_step_lower_bound
    P.toParameters (zero_lt_one.trans_le (one_le_correctedTransferConstant P
      (r.state 0).request (P.sigmaMin_pos.le.trans r.initial_sigma) hL hK)) hκ
    (r.step_lower_bound_of_true_gap_failure O hchecked hk I hq s ha hf hL hK hO hκ hκ1
      hradii hfail)
  calc
    _ ≤ (r.state k).sigma / ((P.p + 1)! : ℝ) * ‖s.step‖ ^ (P.p + 1) := by gcongr
    _ = (r.state k).sigma * ‖s.step‖ ^ (P.p + 1) / ((P.p + 1)! : ℝ) := by ring
    _ ≤ _ := hd.1

/-- The genuine trial extracted from an actual execution inherits the full predicted-decrease
bound. Its numerator is the actual supplied full-p Taylor prediction used in acceptance. -/
theorem Execution.trial_predicted_decrease_of_true_gap_failure {P : Parameters} {f : E → ℝ}
    (O : InexactTrustRegion.Oracle f P.p) {N : ℕ} (r : Execution P checked f O.derivative N)
    (hchecked : 1 ≤ checked) {k : ℕ} (hk : k < N) (ht : r.trial k = true) {L K κ : ℝ}
    (hf : HigherOrderRegularization.DiagonalLipschitz f P.p L) (hL : 1 ≤ L)
    (hK : 0 ≤ K) (hO : InexactTrustRegion.UniformAccuracy O K) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hradii : ‖(r.executedTrial hk ht).inner.step‖ < 1 →
      PrescribedModelRadii P κ (r.executedTrial hk ht).inner.radii)
    (hfail : ¬HigherOrderApproximateRegularization.SatisfiesCriteria P.toParameters f
      ((r.state k).point + (r.executedTrial hk ht).inner.step)
      (r.executedTrial hk ht).inner.radii) :
    HigherOrderApproximateRegularization.modelDecreaseConstant P.p P.q P.order_pos P.theta
        (correctedTransferConstant P (r.state 0).request (r.state 0).sigma L K) κ P.sigmaMin *
      HigherOrderApproximateRegularization.toleranceMeasure P.p P.q P.order_pos P.epsilon ≤
        decrement (O.derivative (r.state k).point (r.state k).request) P.p
          (r.executedTrial hk ht).inner.step :=
  r.predicted_decrease_of_true_gap_failure O hchecked hk.le
    (r.executedTrial hk ht).inspection (r.executedTrial hk ht).order_le
    (r.executedTrial hk ht).inner (r.executedTrial hk ht).accurate
    hf hL hK hO hκ hκ1 hradii hfail

/-- An actual accepted transition with a true failed successor gap pays the full objective
budget at its actual successor point and radii. This uses the literal checked algorithm,
its exact objective ratio and its real accepted state; no abstract decrease sequence is assumed. -/
theorem Execution.accepted_decrease_of_true_gap_failure {P : Parameters} {f : E → ℝ}
    (O : InexactTrustRegion.Oracle f P.p) {N : ℕ} (r : Execution P checked f O.derivative N)
    (hchecked : 1 ≤ checked) {k : ℕ} (hk : k < N) (ht : r.trial k = true)
    (ha : r.accepted k = true) {L K κ : ℝ}
    (hf : HigherOrderRegularization.DiagonalLipschitz f P.p L) (hL : 1 ≤ L)
    (hK : 0 ≤ K) (hO : InexactTrustRegion.UniformAccuracy O K) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hradii : ‖(r.executedTrial hk ht).inner.step‖ < 1 →
      PrescribedModelRadii P κ (r.executedTrial hk ht).inner.radii)
    (hfail : ¬HigherOrderApproximateRegularization.SatisfiesCriteria P.toParameters
      f (r.state (k + 1)).point (r.state (k + 1)).radii) :
    P.eta1 * (HigherOrderApproximateRegularization.modelDecreaseConstant P.p P.q P.order_pos
        P.theta (correctedTransferConstant P (r.state 0).request (r.state 0).sigma L K)
          κ P.sigmaMin *
      HigherOrderApproximateRegularization.toleranceMeasure P.p P.q P.order_pos P.epsilon) ≤
        f (r.state k).point - f (r.state (k + 1)).point := by
  let t := r.executedTrial hk ht
  have hx := t.accepted_point ha
  have hδ := t.accepted_radii ha
  have hf' : ¬HigherOrderApproximateRegularization.SatisfiesCriteria P.toParameters f
      ((r.state k).point + t.inner.step) t.inner.radii := by
    simpa only [hx, hδ] using hfail
  have hb := r.trial_predicted_decrease_of_true_gap_failure O hchecked hk ht
    hf hL hK hO hκ hκ1 hradii hf'
  have hd := t.inner.decrement_pos t.inspection t.order_le
    (P.sigmaMin_pos.le.trans (r.sigma_floor hk.le)) (r.valid_radii hk.le)
  have hratio := t.accepted_iff.mp ha
  change P.eta1 ≤ (f (r.state k).point - f ((r.state k).point + t.inner.step)) /
    decrement (O.derivative (r.state k).point (r.state k).request) P.p t.inner.step at hratio
  have hdec := (le_div_iff₀ hd.2.1).mp hratio
  rw [hx]
  exact (mul_le_mul_of_nonneg_left hb P.eta1_pos.le).trans hdec

end InnerProduct
end Optimization.InexactRegularization
