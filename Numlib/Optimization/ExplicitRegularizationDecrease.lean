import Numlib.Optimization.ExplicitRegularizationTransfer
import Numlib.Optimization.ExplicitRegularizationRequestRatios
import Numlib.Optimization.InexactRegularizationDecrease

/-!
# Accepted explicit-accuracy trials before certification

Accepted trial data retain the actual inner execution, endpoint queries and approximate
ratio update. Shared derivative requests control errors at both endpoint jets. An
uncertified next inspection therefore yields a precise transfer at the stored returned
model radii, without equating them with arbitrarily halved inspection radii.

The computed-witness branch retains the literal margin `fraction / 2 - theta`. This margin
need not be positive for the source algorithm. The independent incoming-error-sum branch
has a positive margin and supplies both tolerance-exponent decrease regimes. No unrestricted
accepted-payment or certified-complexity theorem is asserted by this module.
-/

noncomputable section
open scoped Nat
namespace Optimization.ExplicitRegularization
open InexactTaylorModels TaylorCriticality

section Normed
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {P : Parameters} {f : E → ℝ} {O : Oracle f P.p}
variable {a b : State E} {I : Inspection P O.derivative a} {queries : List (E × ℝ)}

/-- Data extracted from a genuine accepted transition, including its actual completed inner
execution, endpoint calls, approximate acceptance ratio, parameter interval and full cache
update. No stopping quality, payment estimate or global bound is part of these data. -/
structure AcceptedTrial (P : Parameters) (O : Oracle f P.p) (a : State E)
    (I : Inspection P O.derivative a) (b : State E) (queries : List (E × ℝ)) where
  /-- The actual inspection selected a failing active order. -/
  order_le : I.order ≤ P.q
  /-- The detailed inner return used by the source transition. -/
  inner : InexactRegularization.InnerResult P.toImplicitParameters 0
    (O.derivative a.point a.request) a.sigma I.radii (I.direction order_le)
  /-- The literal short-step check covers exactly the source range through `q`. -/
  accurate : InexactRegularization.StepAccurate P.toImplicitParameters P.q a.request inner.step
  /-- The actual endpoint budgets, cache compatibility and query decisions. -/
  values : ValueTrial P O a inner.step
  /-- The parameter selected by the genuine approximate-value ratio update. -/
  nextSigma : ℝ
  /-- The source interval governing that update. -/
  update : HigherOrderApproximateRegularization.ParameterUpdate
    P.toImplicitParameters.toParameters values.ratio a.sigma nextSigma
  /-- The actual approximate-value acceptance threshold holds. -/
  accepted : P.eta1 ≤ values.ratio
  /-- The actual successor retains the source point, radii, requests and endpoint cache. -/
  next_state : b = trialState a I order_le inner values nextSigma
  /-- The transition logs exactly these actual value requests. -/
  queries_eq : queries = values.queries

/-- Every actual accepted transition supplies the operational accepted-trial data. -/
theorem Transition.exists_acceptedTrial {trial accepted : Bool}
    (t : Transition P O a I b trial accepted queries) (ha : accepted = true) :
    Nonempty (AcceptedTrial P O a I b queries) := by
  cases t with
  | refineInspection => cases ha
  | refineStep => cases ha
  | trial hq s hacc v next hu =>
    exact ⟨⟨hq, s, hacc, v, next, hu, by simpa using ha, rfl, rfl⟩⟩

/-- The actual accepted successor is the incoming point plus its returned step. -/
theorem AcceptedTrial.next_point (t : AcceptedTrial P O a I b queries) :
    b.point = a.point + t.inner.step := by
  have h := congrArg (fun z : State E => z.point) t.next_state
  simpa only [trialState, ite_eq_left t.accepted] using h

/-- Acceptance stores exactly the detailed inner return's model radii. -/
theorem AcceptedTrial.next_radii (t : AcceptedTrial P O a I b queries) :
    b.radii = t.inner.radii := by
  have h := congrArg (fun z : State E => z.radii) t.next_state
  simpa only [trialState, ite_eq_left t.accepted] using h

/-- Acceptance preserves every derivative request, independently of value-cache decisions. -/
theorem AcceptedTrial.next_request (t : AcceptedTrial P O a I b queries) :
    b.request = a.request := by
  have h := congrArg (fun z : State E => z.request) t.next_state
  simpa only [trialState, ite_eq_left t.accepted] using h

/-- The source half-acceptance payment holds at the actual recorded successor point. -/
theorem AcceptedTrial.objective_decrease (t : AcceptedTrial P O a I b queries) :
    P.eta1 * decrement (O.derivative a.point a.request) P.p t.inner.step / 2 ≤
      f a.point - f b.point := by
  rw [t.next_point]
  exact t.values.accepted_decrease t.accepted

/-- Every actual accepted long trial pays the regularization floor, independently of any
next inspection, stopping-quality or radius-floor condition. -/
theorem AcceptedTrial.long_predicted_decrease (t : AcceptedTrial P O a I b queries)
    (hσ : P.sigmaMin ≤ a.sigma)
    (hδ : HigherOrderApproximateRegularization.ValidRadii
      P.toImplicitParameters.toParameters a.radii) (hs : 1 ≤ ‖t.inner.step‖) :
    P.sigmaMin / ((P.p + 1)! : ℝ) ≤
      decrement (O.derivative a.point a.request) P.p t.inner.step :=
  InexactRegularization.InnerResult.long_predicted_decrease I t.order_le t.inner hσ hδ hs

/-- The real endpoint values of an accepted long trial pay half the acceptance factor times
its unconditional regularization-floor prediction. -/
theorem AcceptedTrial.long_objective_decrease (t : AcceptedTrial P O a I b queries)
    (hσ : P.sigmaMin ≤ a.sigma)
    (hδ : HigherOrderApproximateRegularization.ValidRadii
      P.toImplicitParameters.toParameters a.radii) (hs : 1 ≤ ‖t.inner.step‖) :
    P.eta1 / 2 * (P.sigmaMin / ((P.p + 1)! : ℝ)) ≤ f a.point - f b.point := by
  have hp := mul_le_mul_of_nonneg_left (t.long_predicted_decrease hσ hδ hs)
    (div_nonneg P.eta1_pos.le (by norm_num : (0 : ℝ) ≤ 2))
  have ho := t.objective_decrease
  linarith only [hp, ho]

/-- Select the actual accepted data from a legal finite prefix. -/
def Execution.acceptedTrial {N : ℕ} (r : Execution P O N) {k : ℕ}
    (hk : k < N) (ha : r.accepted k = true) :
    AcceptedTrial P O (r.state k) (r.inspection k) (r.state (k + 1)) (r.queries k) :=
  Classical.choice ((r.transition k hk).exists_acceptedTrial ha)

omit [NormedSpace ℝ E] in
/-- An incoming error-sum failure and full-order request powers give a positive transfer
at the original stored radius. This does not use any objective-gap failure. -/
theorem incomingErrorCheck_failure_transfer {s : E} {R : ℝ}
    (hh : ∀ i ∈ Finset.Icc 1 P.p,
      a.request i ≤ R * P.kappaStep * ‖s‖ ^ (P.p - i + 1))
    (hn : ¬IncomingErrorCheck P a)
    (hδ : HigherOrderApproximateRegularization.ValidRadii
      P.toImplicitParameters.toParameters a.radii) :
    ∃ j, 1 ≤ j ∧ j ≤ P.q ∧
      (P.fraction / 2) * P.epsilon j * a.radii j ^ j / (j ! : ℝ) ≤
        R * P.kappaStep * ∑ l ∈ Finset.Icc 1 j,
          a.radii j ^ l * ‖s‖ ^ (P.p - l + 1) / (l ! : ℝ) := by
  obtain ⟨j, hj, hjq, hb⟩ := (not_incomingErrorCheck_iff P a).mp hn
  refine ⟨j, hj, hjq, ?_⟩
  have he : (P.fraction / 2) * P.epsilon j * a.radii j ^ j / (j ! : ℝ) =
      P.fraction * P.epsilon j * a.radii j ^ j / (2 * (j ! : ℝ)) := by ring
  rw [he]
  apply hb.le.trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hip : i ∈ Finset.Icc 1 P.p := Finset.mem_Icc.mpr
    ⟨(Finset.mem_Icc.mp hi).1, (Finset.mem_Icc.mp hi).2.trans (hjq.trans P.order_le)⟩
  calc
    _ ≤ R * P.kappaStep * ‖s‖ ^ (P.p - i + 1) * a.radii j ^ i / (i ! : ℝ) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hh i hip)
        (pow_nonneg (hδ j hj hjq).1.le _)) (by positivity)
    _ = _ := by ring

/-- A normalized scalar constant transfers a failed observable error sum to the usual
step-bound analysis. It is independent of all tolerance values. -/
def errorTransferConstant (P : Parameters) (R : ℝ) : ℝ :=
  max 1 (2 * R * P.kappaStep / P.fraction)

/-- The error-sum transfer constant is normalized to at least one. -/
theorem one_le_errorTransferConstant (P : Parameters) (R : ℝ) :
    1 ≤ errorTransferConstant P R := le_max_left _ _

omit [NormedSpace ℝ E] in
/-- The positive error-sum transfer implies the standard scalar transfer form without any
extra restriction on the source model-accuracy parameter. -/
theorem incomingErrorCheck_failure_transfer_standard {s : E} {R : ℝ}
    (hh : ∀ i ∈ Finset.Icc 1 P.p,
      a.request i ≤ R * P.kappaStep * ‖s‖ ^ (P.p - i + 1))
    (hn : ¬IncomingErrorCheck P a)
    (hδ : HigherOrderApproximateRegularization.ValidRadii
      P.toImplicitParameters.toParameters a.radii) :
    ∃ j, 1 ≤ j ∧ j ≤ P.q ∧
      (1 - P.theta) * P.epsilon j * a.radii j ^ j / (j ! : ℝ) ≤
        errorTransferConstant P R * ∑ l ∈ Finset.Icc 1 j,
          a.radii j ^ l * ‖s‖ ^ (P.p - l + 1) / (l ! : ℝ) := by
  obtain ⟨j, hj, hjq, hb⟩ := incomingErrorCheck_failure_transfer hh hn hδ
  refine ⟨j, hj, hjq, ?_⟩
  let T := P.epsilon j * a.radii j ^ j / (j ! : ℝ)
  let W := ∑ l ∈ Finset.Icc 1 j,
    a.radii j ^ l * ‖s‖ ^ (P.p - l + 1) / (l ! : ℝ)
  have hT : 0 ≤ T := div_nonneg (mul_nonneg (P.epsilon_pos j hj hjq).le
    (pow_nonneg (hδ j hj hjq).1.le _)) (by positivity)
  have hW : 0 ≤ W := Finset.sum_nonneg (fun _ _ => by
    exact div_nonneg (mul_nonneg (pow_nonneg (hδ j hj hjq).1.le _)
      (pow_nonneg (norm_nonneg s) _)) (by positivity))
  have hb' : (P.fraction / 2) * T ≤ R * P.kappaStep * W := by
    simpa only [T, W, mul_assoc, mul_div_assoc] using hb
  have hcancel : (2 * R * P.kappaStep / P.fraction * W) * P.fraction =
      2 * R * P.kappaStep * W := by field_simp [P.fraction_pos.ne']
  have ht : T ≤ 2 * R * P.kappaStep / P.fraction * W := by
    apply (mul_le_mul_iff_left₀ P.fraction_pos).mp
    nlinarith only [hb', hcancel]
  calc
    (1 - P.theta) * P.epsilon j * a.radii j ^ j / (j ! : ℝ) = (1 - P.theta) * T := by
      dsimp [T]; ring
    _ ≤ T := mul_le_of_le_one_left hT (by linarith [P.theta_pos])
    _ ≤ 2 * R * P.kappaStep / P.fraction * W := ht
    _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hW

end Normed

section Euclidean
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {P : Parameters} {f : E → ℝ} {O : Oracle f P.p}
variable {a b : State E} {I : Inspection P O.derivative a} {queries : List (E × ℝ)}

/-- A genuine accepted short step controls the next supplied gap using known errors at both
actual endpoints and their unchanged request vector. -/
theorem AcceptedTrial.endpoint_gap_le (t : AcceptedTrial P O a I b queries)
    {L S R : ℝ} (hf : HigherOrderRegularization.DiagonalLipschitz f P.p L)
    (hR : 0 ≤ R) (hσ : 0 ≤ a.sigma) (hS : a.sigma ≤ S)
    (hδ : HigherOrderApproximateRegularization.ValidRadii
      P.toImplicitParameters.toParameters a.radii)
    (hpos : ∀ i ∈ Finset.Icc 1 P.p, 0 < a.request i) (hs : ‖t.inner.step‖ < 1)
    (hh : ∀ i ∈ Finset.Icc 1 P.p,
      a.request i ≤ R * P.kappaStep * ‖t.inner.step‖ ^ (P.p - i + 1))
    {j : ℕ} (hj : 1 ≤ j) (hjq : j ≤ P.q) :
    gapOn (decrement (O.derivative b.point b.request) j)
        (Metric.closedBall 0 (t.inner.radii j)) ≤
      P.theta * P.epsilon j * t.inner.radii j ^ j / (j ! : ℝ) +
        (L + S + 4 * R * P.kappaStep) * ∑ l ∈ Finset.Icc 1 j,
          t.inner.radii j ^ l * ‖t.inner.step‖ ^ (P.p - l + 1) / (l ! : ℝ) := by
  have hv := t.inner.valid_radii (I.valid_radii hδ) j hj hjq
  have hne := (t.inner.decrement_pos I t.order_le hσ hδ).2.2
  apply t.inner.endpoint_gap_le hf hR hσ hS hne hs
    (fun i hi => (O.derivative_accuracy _ _ hpos i hi).trans (hh i hi)) _ hj hjq hv.1.le
  intro i hi
  rw [← t.next_point]
  have hp : ∀ i ∈ Finset.Icc 1 P.p, 0 < b.request i := by
    simpa only [t.next_request] using hpos
  exact (O.derivative_accuracy _ _ hp i hi).trans (by
    simpa only [t.next_request] using hh i hi)

/-- A computed initial witness failure at the actual accepted successor gives the literal
transfer margin. Its coefficient `fraction / 2 - theta` is intentionally not asserted positive. -/
theorem AcceptedTrial.transfer_of_initialFailure (t : AcceptedTrial P O a I b queries)
    {L S R : ℝ} (hf : HigherOrderRegularization.DiagonalLipschitz f P.p L)
    (hR : 0 ≤ R) (hσ : 0 ≤ a.sigma) (hS : a.sigma ≤ S)
    (hδ : HigherOrderApproximateRegularization.ValidRadii
      P.toImplicitParameters.toParameters a.radii)
    (hpos : ∀ i ∈ Finset.Icc 1 P.p, 0 < a.request i) (hs : ‖t.inner.step‖ < 1)
    (hh : ∀ i ∈ Finset.Icc 1 P.p,
      a.request i ≤ R * P.kappaStep * ‖t.inner.step‖ ^ (P.p - i + 1))
    (hn : InitialFailure P O.derivative b) :
    ∃ j, 1 ≤ j ∧ j ≤ P.q ∧
      (P.fraction / 2 - P.theta) * P.epsilon j * t.inner.radii j ^ j / (j ! : ℝ) ≤
        (L + S + 4 * R * P.kappaStep) * ∑ l ∈ Finset.Icc 1 j,
          t.inner.radii j ^ l * ‖t.inner.step‖ ^ (P.p - l + 1) / (l ! : ℝ) := by
  obtain ⟨j, hj, hjq, d, hw, hb⟩ := hn
  refine ⟨j, hj, hjq, ?_⟩
  have hv := t.inner.valid_radii (I.valid_radii hδ) j hj hjq
  have hd := le_gapOn (isCompact_closedBall (0 : E) (t.inner.radii j))
    (continuous_decrement (O.derivative b.point b.request) j).continuousOn
    (show d ∈ Metric.closedBall 0 (t.inner.radii j) by
      simpa only [Metric.mem_closedBall, dist_zero_right, t.next_radii] using hw.feasible)
  have hg := t.endpoint_gap_le hf hR hσ hS hδ hpos hs hh hj hjq
  have hb' : P.fraction * P.epsilon j * t.inner.radii j ^ j / (2 * (j ! : ℝ)) <
      decrement (O.derivative b.point b.request) j d := by
    simpa only [t.next_radii] using hb
  have he : (P.fraction / 2 - P.theta) * P.epsilon j * t.inner.radii j ^ j / (j ! : ℝ) =
      P.fraction * P.epsilon j * t.inner.radii j ^ j / (2 * (j ! : ℝ)) -
        P.theta * P.epsilon j * t.inner.radii j ^ j / (j ! : ℝ) := by ring
  rw [he]
  linarith only [hb', hd, hg]


/-- The actual next uncertified inspection gives either a computed initial-failure transfer
with its literal margin, or a positive observable-error transfer. Both use the actual stored
returned radii and the same accepted endpoint request vector. -/
theorem AcceptedTrial.transfer_cases_of_not_certified (t : AcceptedTrial P O a I b queries)
    (J : Inspection P O.derivative b) (hnc : ¬Certified P b J)
    {L S R : ℝ} (hf : HigherOrderRegularization.DiagonalLipschitz f P.p L)
    (hR : 0 ≤ R) (hσ : 0 ≤ a.sigma) (hS : a.sigma ≤ S)
    (hδ : HigherOrderApproximateRegularization.ValidRadii
      P.toImplicitParameters.toParameters a.radii)
    (hpos : ∀ i ∈ Finset.Icc 1 P.p, 0 < a.request i) (hs : ‖t.inner.step‖ < 1)
    (hh : ∀ i ∈ Finset.Icc 1 P.p,
      a.request i ≤ R * P.kappaStep * ‖t.inner.step‖ ^ (P.p - i + 1)) :
    (J.InitialFailure ∧ ∃ j, 1 ≤ j ∧ j ≤ P.q ∧
      (P.fraction / 2 - P.theta) * P.epsilon j * t.inner.radii j ^ j / (j ! : ℝ) ≤
        (L + S + 4 * R * P.kappaStep) * ∑ l ∈ Finset.Icc 1 j,
          t.inner.radii j ^ l * ‖t.inner.step‖ ^ (P.p - l + 1) / (l ! : ℝ)) ∨
    (¬IncomingErrorCheck P b ∧ ∃ j, 1 ≤ j ∧ j ≤ P.q ∧
      (P.fraction / 2) * P.epsilon j * t.inner.radii j ^ j / (j ! : ℝ) ≤
        R * P.kappaStep * ∑ l ∈ Finset.Icc 1 j,
          t.inner.radii j ^ l * ‖t.inner.step‖ ^ (P.p - l + 1) / (l ! : ℝ)) := by
  rcases J.not_certified_initial_cases hnc with hn | ⟨he, _⟩
  · exact Or.inl ⟨hn, t.transfer_of_initialFailure hf hR hσ hS hδ hpos hs hh
      (J.initialFailure_imp hn)⟩
  · refine Or.inr ⟨he, ?_⟩
    have hv : HigherOrderApproximateRegularization.ValidRadii
        P.toImplicitParameters.toParameters b.radii := by
      rw [t.next_radii]
      exact t.inner.valid_radii (I.valid_radii hδ)
    have hh' : ∀ i ∈ Finset.Icc 1 P.p,
        b.request i ≤ R * P.kappaStep * ‖t.inner.step‖ ^ (P.p - i + 1) := by
      simpa only [t.next_request] using hh
    simpa only [t.next_radii] using incomingErrorCheck_failure_transfer hh' he hv

/-- In the no-initial-failure branch of an actual uncertified next inspection, both source
step-size exponent regimes follow from the literal observable error sum. Actual short model
radii are derived from supplied tensor and parameter bounds; long steps use their norm. -/
theorem AcceptedTrial.step_lower_bound_of_no_initialFailure
    (t : AcceptedTrial P O a I b queries) (J : Inspection P O.derivative b)
    (hnc : ¬Certified P b J) (hn : ¬J.InitialFailure)
    {M S R : ℝ} (hM : 1 ≤ M) (hσ : P.sigmaMin ≤ a.sigma) (hS : a.sigma ≤ S)
    (hδ : HigherOrderApproximateRegularization.ValidRadii
      P.toImplicitParameters.toParameters a.radii)
    (hA : ∀ i ∈ Finset.Icc 1 P.p, ‖O.derivative a.point a.request i‖ ≤ M)
    (hh : ‖t.inner.step‖ < 1 → ∀ i ∈ Finset.Icc 1 P.p,
      a.request i ≤ R * P.kappaStep * ‖t.inner.step‖ ^ (P.p - i + 1)) :
    ∃ j, 1 ≤ j ∧ j ≤ P.q ∧
      HigherOrderApproximateRegularization.stepBoundConstant P.p P.q j P.theta
        (errorTransferConstant P R)
        (InexactRegularization.prescribedRadiusCoefficient P.toImplicitParameters M S) *
        (P.epsilon j) ^ HigherOrderApproximateRegularization.stepBoundExponent P.p P.q j ≤
          ‖t.inner.step‖ := by
  have hC := one_le_errorTransferConstant P R
  have hκ := InexactRegularization.prescribedRadiusCoefficient_pos P.toImplicitParameters
    (S := S) hM
  by_cases hs : ‖t.inner.step‖ < 1
  · have he : ¬IncomingErrorCheck P b := by
      rcases J.not_certified_initial_cases hnc with hf | ⟨he, _⟩
      · exact (hn hf).elim
      · exact he
    have hv := t.inner.valid_radii (I.valid_radii hδ)
    have hvb : HigherOrderApproximateRegularization.ValidRadii
        P.toImplicitParameters.toParameters b.radii := by simpa only [t.next_radii] using hv
    have hh' : ∀ i ∈ Finset.Icc 1 P.p,
        b.request i ≤ R * P.kappaStep * ‖t.inner.step‖ ^ (P.p - i + 1) := by
      simpa only [t.next_request] using hh hs
    obtain ⟨j, hj, hjq, hb⟩ := incomingErrorCheck_failure_transfer_standard hh' he hvb
    rw [t.next_radii] at hb
    have hr := (t.inner.prescribedModelRadii_of_bounds hM
      (P.sigmaMin_pos.le.trans hσ) hA hS hs).regimes
      (InexactRegularization.prescribedRadiusCoefficient_le_one P.toImplicitParameters hM)
    refine ⟨j, hj, hjq, ?_⟩
    exact HigherOrderApproximateRegularization.step_lower_bound_of_transfer hj
      (hjq.trans P.order_le) (norm_nonneg _) (hv j hj hjq).1 (zero_lt_one.trans_le hC)
      (P.epsilon_pos j hj hjq) (P.epsilon_lt_one j hj hjq).le P.theta_lt_one hκ
      (fun hq => hr.1 hq j hj hjq) (fun hq => hr.2 hq j hj hjq) hb hs.le
  · exact HigherOrderApproximateRegularization.step_lower_bound_of_one_le
      P.toImplicitParameters.toParameters hC (le_of_not_gt hs)

/-- The observable-error branch before actual certification pays the full simultaneous
model-prediction scale for every `p ≥ q ≥ 1`. This theorem explicitly retains the branch
hypothesis; it is not an unrestricted before-certification payment theorem. -/
theorem AcceptedTrial.predicted_decrease_of_no_initialFailure
    (t : AcceptedTrial P O a I b queries) (J : Inspection P O.derivative b)
    (hnc : ¬Certified P b J) (hn : ¬J.InitialFailure)
    {M S R : ℝ} (hM : 1 ≤ M) (hσ : P.sigmaMin ≤ a.sigma) (hS : a.sigma ≤ S)
    (hδ : HigherOrderApproximateRegularization.ValidRadii
      P.toImplicitParameters.toParameters a.radii)
    (hA : ∀ i ∈ Finset.Icc 1 P.p, ‖O.derivative a.point a.request i‖ ≤ M)
    (hh : ‖t.inner.step‖ < 1 → ∀ i ∈ Finset.Icc 1 P.p,
      a.request i ≤ R * P.kappaStep * ‖t.inner.step‖ ^ (P.p - i + 1)) :
    HigherOrderApproximateRegularization.modelDecreaseConstant P.p P.q P.order_pos P.theta
        (errorTransferConstant P R)
        (InexactRegularization.prescribedRadiusCoefficient P.toImplicitParameters M S)
        P.sigmaMin *
      HigherOrderApproximateRegularization.toleranceMeasure P.p P.q P.order_pos P.epsilon ≤
        decrement (O.derivative a.point a.request) P.p t.inner.step := by
  apply HigherOrderApproximateRegularization.predicted_decrease_of_step_lower_bound
    P.toImplicitParameters.toParameters (zero_lt_one.trans_le (one_le_errorTransferConstant P R))
    (InexactRegularization.prescribedRadiusCoefficient_pos P.toImplicitParameters hM)
    (t.step_lower_bound_of_no_initialFailure J hnc hn hM hσ hS hδ hA hh)
  calc
    _ ≤ a.sigma / ((P.p + 1)! : ℝ) * ‖t.inner.step‖ ^ (P.p + 1) := by gcongr
    _ = a.sigma * ‖t.inner.step‖ ^ (P.p + 1) / ((P.p + 1)! : ℝ) := by ring
    _ ≤ _ := (t.inner.decrement_pos I t.order_le (P.sigmaMin_pos.le.trans hσ) hδ).1

/-- The same observable-error branch pays the actual successor objective, including both
approximate endpoint errors and the source factor one half. -/
theorem AcceptedTrial.accepted_decrease_of_no_initialFailure
    (t : AcceptedTrial P O a I b queries) (J : Inspection P O.derivative b)
    (hnc : ¬Certified P b J) (hn : ¬J.InitialFailure)
    {M S R : ℝ} (hM : 1 ≤ M) (hσ : P.sigmaMin ≤ a.sigma) (hS : a.sigma ≤ S)
    (hδ : HigherOrderApproximateRegularization.ValidRadii
      P.toImplicitParameters.toParameters a.radii)
    (hA : ∀ i ∈ Finset.Icc 1 P.p, ‖O.derivative a.point a.request i‖ ≤ M)
    (hh : ‖t.inner.step‖ < 1 → ∀ i ∈ Finset.Icc 1 P.p,
      a.request i ≤ R * P.kappaStep * ‖t.inner.step‖ ^ (P.p - i + 1)) :
    P.eta1 / 2 *
      (HigherOrderApproximateRegularization.modelDecreaseConstant P.p P.q P.order_pos P.theta
        (errorTransferConstant P R)
        (InexactRegularization.prescribedRadiusCoefficient P.toImplicitParameters M S)
        P.sigmaMin *
      HigherOrderApproximateRegularization.toleranceMeasure P.p P.q P.order_pos P.epsilon) ≤
      f a.point - f b.point := by
  have hp := mul_le_mul_of_nonneg_left
    (t.predicted_decrease_of_no_initialFailure J hnc hn hM hσ hS hδ hA hh)
    (div_nonneg P.eta1_pos.le (by norm_num : (0 : ℝ) ≤ 2))
  have ho := t.objective_decrease
  linarith only [hp, ho]


/-- Along an actual finite execution, initial request ratios and the literal `q`-checked
accepted step supply every endpoint error power in the uncertified-transfer dichotomy.
Only analytic smoothness and the current parameter upper bound remain as inputs. -/
theorem Execution.accepted_transfer_cases {N : ℕ} (r : Execution P O N) {k : ℕ}
    (hk : k < N) (ha : r.accepted k = true)
    (hnc : ¬Certified P (r.state (k + 1)) (r.inspection (k + 1)))
    {L S : ℝ} (hf : HigherOrderRegularization.DiagonalLipschitz f P.p L)
    (hS : (r.state k).sigma ≤ S) (hs : ‖(r.acceptedTrial hk ha).inner.step‖ < 1) :
    let t := r.acceptedTrial hk ha
    let R := InexactRegularization.requestAmplification P.p (r.state 0).request
    ((r.inspection (k + 1)).InitialFailure ∧ ∃ j, 1 ≤ j ∧ j ≤ P.q ∧
      (P.fraction / 2 - P.theta) * P.epsilon j * t.inner.radii j ^ j / (j ! : ℝ) ≤
        (L + S + 4 * R * P.kappaStep) * ∑ l ∈ Finset.Icc 1 j,
          t.inner.radii j ^ l * ‖t.inner.step‖ ^ (P.p - l + 1) / (l ! : ℝ)) ∨
    (¬IncomingErrorCheck P (r.state (k + 1)) ∧ ∃ j, 1 ≤ j ∧ j ≤ P.q ∧
      (P.fraction / 2) * P.epsilon j * t.inner.radii j ^ j / (j ! : ℝ) ≤
        R * P.kappaStep * ∑ l ∈ Finset.Icc 1 j,
          t.inner.radii j ^ l * ‖t.inner.step‖ ^ (P.p - l + 1) / (l ! : ℝ)) := by
  apply (r.acceptedTrial hk ha).transfer_cases_of_not_certified
    (r.inspection (k + 1)) hnc hf
    (zero_le_one.trans (InexactRegularization.one_le_requestAmplification _ _))
    (P.sigmaMin_pos.le.trans (r.sigma_floor hk.le)) hS (r.valid_radii hk.le)
    (fun i hi => (r.request_bounds hk.le hi).1) hs
  intro i hi
  exact r.short_step_request_le_power hk.le (r.acceptedTrial hk ha).accurate hs hi

/-- The full simultaneous prediction payment for the observable-error branch of a genuine
execution. The fixed initial request vector supplies its ratio constant, the checked first
request supplies all derivative powers, and the detailed inner execution supplies its radii. -/
theorem Execution.predicted_decrease_of_no_initialFailure {N : ℕ} (r : Execution P O N)
    {k : ℕ} (hk : k < N) (ha : r.accepted k = true)
    (hnc : ¬Certified P (r.state (k + 1)) (r.inspection (k + 1)))
    (hn : ¬(r.inspection (k + 1)).InitialFailure)
    {M S : ℝ} (hM : 1 ≤ M) (hS : (r.state k).sigma ≤ S)
    (hA : ∀ i ∈ Finset.Icc 1 P.p,
      ‖O.derivative (r.state k).point (r.state k).request i‖ ≤ M) :
    HigherOrderApproximateRegularization.modelDecreaseConstant P.p P.q P.order_pos P.theta
        (errorTransferConstant P
          (InexactRegularization.requestAmplification P.p (r.state 0).request))
        (InexactRegularization.prescribedRadiusCoefficient P.toImplicitParameters M S)
        P.sigmaMin *
      HigherOrderApproximateRegularization.toleranceMeasure P.p P.q P.order_pos P.epsilon ≤
        decrement (O.derivative (r.state k).point (r.state k).request) P.p
          (r.acceptedTrial hk ha).inner.step := by
  apply (r.acceptedTrial hk ha).predicted_decrease_of_no_initialFailure
    (r.inspection (k + 1)) hnc hn hM (r.sigma_floor hk.le) hS (r.valid_radii hk.le) hA
  intro hs i hi
  exact r.short_step_request_le_power hk.le (r.acceptedTrial hk ha).accurate hs hi

/-- Actual accepted objective payment in the observable-error branch of an uncertified
successor inspection. The source one-half acceptance factor pays the real endpoint errors. -/
theorem Execution.accepted_decrease_of_no_initialFailure {N : ℕ} (r : Execution P O N)
    {k : ℕ} (hk : k < N) (ha : r.accepted k = true)
    (hnc : ¬Certified P (r.state (k + 1)) (r.inspection (k + 1)))
    (hn : ¬(r.inspection (k + 1)).InitialFailure)
    {M S : ℝ} (hM : 1 ≤ M) (hS : (r.state k).sigma ≤ S)
    (hA : ∀ i ∈ Finset.Icc 1 P.p,
      ‖O.derivative (r.state k).point (r.state k).request i‖ ≤ M) :
    P.eta1 / 2 *
      (HigherOrderApproximateRegularization.modelDecreaseConstant P.p P.q P.order_pos P.theta
        (errorTransferConstant P
          (InexactRegularization.requestAmplification P.p (r.state 0).request))
        (InexactRegularization.prescribedRadiusCoefficient P.toImplicitParameters M S)
        P.sigmaMin *
      HigherOrderApproximateRegularization.toleranceMeasure P.p P.q P.order_pos P.epsilon) ≤
      f (r.state k).point - f (r.state (k + 1)).point := by
  apply (r.acceptedTrial hk ha).accepted_decrease_of_no_initialFailure
    (r.inspection (k + 1)) hnc hn hM (r.sigma_floor hk.le) hS (r.valid_radii hk.le) hA
  intro hs i hi
  exact r.short_step_request_le_power hk.le (r.acceptedTrial hk ha).accurate hs hi

end Euclidean
end Optimization.ExplicitRegularization
