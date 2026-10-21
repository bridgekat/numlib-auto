import Numlib.Optimization.InexactRegularizationAccuracy
import Numlib.Optimization.InexactTrustRegionAccuracy

/-!
# Uniform regularization bounds from proportional accuracy requests

All derivative requests share the same geometric refinement scale. Their ratios to the
first request therefore remain fixed even through accepted and rejected trials. For a short
step, the checked first-order request controls every supplied derivative order through the
maximum initial request ratio. Long steps use the independent initialization cap. These two
bounds supply a genuine uniform regularization bound for any checked order at least one.
The bound depends on the fixed initial request vector, and is not uniform over all such vectors.
-/

noncomputable section
open scoped Nat
namespace Optimization.InexactRegularization
open InexactTaylorModels

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {checked : ℕ}

/-- Maximum of one and all active request ratios relative to the first derivative request. -/
def requestAmplification (p : ℕ) (h : ℕ → ℝ) : ℝ :=
  (insert 0 (Finset.Icc 1 p)).sup' (by simp)
    (fun i => if i = 0 then 1 else h i / h 1)

/-- The request amplification is at least one, independently of inactive request values. -/
theorem one_le_requestAmplification (p : ℕ) (h : ℕ → ℝ) :
    1 ≤ requestAmplification p h := by
  have hh := Finset.le_sup' (s := insert 0 (Finset.Icc 1 p))
    (f := fun i => if i = 0 then (1 : ℝ) else h i / h 1) (by simp : 0 ∈ _)
  simpa only [requestAmplification, ite_true] using hh

/-- Every active initial ratio is bounded by the request amplification. -/
theorem request_ratio_le_amplification {p i : ℕ} (h : ℕ → ℝ)
    (hi : i ∈ Finset.Icc 1 p) : h i / h 1 ≤ requestAmplification p h := by
  have hi0 : i ≠ 0 := by have := (Finset.mem_Icc.mp hi).1; omega
  have hh := Finset.le_sup' (s := insert 0 (Finset.Icc 1 p))
    (f := fun i => if i = 0 then (1 : ℝ) else h i / h 1) (Finset.mem_insert_of_mem hi)
  simpa only [requestAmplification, ite_eq_right hi0] using hh

/-- A common upper bound on one and all active ratios bounds the request amplification. -/
theorem requestAmplification_le {p : ℕ} {h : ℕ → ℝ} {R : ℝ} (hR : 1 ≤ R)
    (hbound : ∀ i ∈ Finset.Icc 1 p, h i / h 1 ≤ R) :
    requestAmplification p h ≤ R := by
  apply Finset.sup'_le
  intro i hi
  rcases Finset.mem_insert.mp hi with rfl | hi
  · simpa using hR
  · split_ifs
    · exact hR
    · exact hbound i hi

/-- A scalar bounds the request amplification exactly when it bounds one and every active ratio. -/
@[simp] theorem requestAmplification_le_iff {p : ℕ} {h : ℕ → ℝ} {R : ℝ} :
    requestAmplification p h ≤ R ↔ 1 ≤ R ∧ ∀ i ∈ Finset.Icc 1 p, h i / h 1 ≤ R := by
  constructor
  · intro hb
    exact ⟨(one_le_requestAmplification p h).trans hb,
      fun i hi => (request_ratio_le_amplification h hi).trans hb⟩
  · rintro ⟨hR, hbound⟩
    exact requestAmplification_le hR hbound

/-- Every request has its exact initial proportion to the first request. The invariant includes
both refinement branches and accepted or rejected trials, through their common geometric scale. -/
theorem Execution.request_proportional {P : Parameters} {f : E → ℝ}
    {oracle : E → (ℕ → ℝ) → Coefficients E} {N : ℕ} (r : Execution P checked f oracle N)
    {k : ℕ} (hk : k ≤ N) (i : ℕ) :
    (r.state k).request i = ((r.state 0).request i / (r.state 0).request 1) *
      (r.state k).request 1 := by
  have hp : 1 ∈ Finset.Icc 1 P.p :=
    Finset.mem_Icc.mpr ⟨le_rfl, P.order_pos.trans P.order_le⟩
  have h1 := (r.initial_request 1 hp).ne'
  rw [r.request_eq hk i, r.request_eq hk 1]
  field_simp

/-- Normalized active requests equal their fixed initial ratios at every reachable state. -/
theorem Execution.request_ratio {P : Parameters} {f : E → ℝ}
    {oracle : E → (ℕ → ℝ) → Coefficients E} {N : ℕ} (r : Execution P checked f oracle N)
    {k : ℕ} (hk : k ≤ N) (i : ℕ) :
    (r.state k).request i / (r.state k).request 1 =
      (r.state 0).request i / (r.state 0).request 1 := by
  have hp : 1 ∈ Finset.Icc 1 P.p :=
    Finset.mem_Icc.mpr ⟨le_rfl, P.order_pos.trans P.order_le⟩
  rw [r.request_proportional hk i, mul_div_cancel_right₀ _ (r.request_bounds hk hp).1.ne']

/-- The largest initial request ratio controls every active request by the current first one. -/
theorem Execution.request_le_amplification {P : Parameters} {f : E → ℝ}
    {oracle : E → (ℕ → ℝ) → Coefficients E} {N : ℕ} (r : Execution P checked f oracle N)
    {k i : ℕ} (hk : k ≤ N) (hi : i ∈ Finset.Icc 1 P.p) :
    (r.state k).request i ≤ requestAmplification P.p (r.state 0).request *
      (r.state k).request 1 := by
  have hp : 1 ∈ Finset.Icc 1 P.p :=
    Finset.mem_Icc.mpr ⟨le_rfl, P.order_pos.trans P.order_le⟩
  rw [r.request_proportional hk i]
  exact mul_le_mul_of_nonneg_right (request_ratio_le_amplification _ hi)
    (r.request_bounds hk hp).1.le

omit [NormedSpace ℝ E] in
/-- Checking any positive number of derivative orders bounds the first request on short steps. -/
theorem StepAccurate.first_request_le_power {P : Parameters} {h : ℕ → ℝ} {s : E}
    (ha : StepAccurate P checked h s) (hchecked : 1 ≤ checked) (hs : ‖s‖ < 1) :
    h 1 ≤ P.kappaStep * ‖s‖ ^ P.p := by
  have h := (StepAccurate.short_iff hs).mp ha 1 (Finset.mem_Icc.mpr ⟨le_rfl, hchecked⟩)
  simpa only [Nat.sub_add_cancel (P.order_pos.trans P.order_le)] using h

omit [NormedSpace ℝ E] in
/-- The checked first request controls every active short-step request once its proportional
bound is known. No check on the higher derivative order is needed. -/
theorem StepAccurate.short_request_le_power {P : Parameters} {h : ℕ → ℝ} {s : E}
    (ha : StepAccurate P checked h s) (hchecked : 1 ≤ checked) (hs : ‖s‖ < 1)
    {R : ℝ} (hR : 0 ≤ R) {i : ℕ} (hi : i ∈ Finset.Icc 1 P.p)
    (hhi : h i ≤ R * h 1) : h i ≤ R * P.kappaStep * ‖s‖ ^ (P.p - i + 1) := by
  have hexp : P.p - i + 1 ≤ P.p := by have := Finset.mem_Icc.mp hi; omega
  calc
    h i ≤ R * h 1 := hhi
    _ ≤ R * (P.kappaStep * ‖s‖ ^ P.p) :=
      mul_le_mul_of_nonneg_left (ha.first_request_le_power hchecked hs) hR
    _ ≤ R * (P.kappaStep * ‖s‖ ^ (P.p - i + 1)) := by
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one (norm_nonneg s) hs.le hexp) P.kappaStep_pos.le) hR
    _ = _ := by ring

/-- Effective step-accuracy coefficient accounting for the initial request ratios on short
steps and the independent initialization cap on long steps. -/
def effectiveAccuracy (P : Parameters) (h : ℕ → ℝ) : ℝ :=
  max (requestAmplification P.p h * P.kappaStep) P.kappaInitial

/-- Bounding the effective accuracy is equivalent to bounding its short-step and long-step terms. -/
@[simp] theorem effectiveAccuracy_le_iff {P : Parameters} {h : ℕ → ℝ} {C : ℝ} :
    effectiveAccuracy P h ≤ C ↔
      requestAmplification P.p h * P.kappaStep ≤ C ∧ P.kappaInitial ≤ C :=
  max_le_iff

/-- The effective accuracy coefficient is strictly positive. -/
theorem effectiveAccuracy_pos (P : Parameters) (h : ℕ → ℝ) : 0 < effectiveAccuracy P h :=
  (mul_pos (zero_lt_one.trans_le (one_le_requestAmplification P.p h)) P.kappaStep_pos).trans_le
    (le_max_left _ _)

/-- Every active request at a reachable checked step has full-order step scaling. This covers
all positive checked degrees, including the literal case `checked=q<p`, and the long-step bypass. -/
theorem Execution.step_request_le_power {P : Parameters} {f : E → ℝ}
    {oracle : E → (ℕ → ℝ) → Coefficients E} {N : ℕ} (r : Execution P checked f oracle N)
    (hchecked : 1 ≤ checked) {k : ℕ} (hk : k ≤ N) {s : E}
    (ha : StepAccurate P checked (r.state k).request s)
    {i : ℕ} (hi : i ∈ Finset.Icc 1 P.p) :
    (r.state k).request i ≤ effectiveAccuracy P (r.state 0).request *
      ‖s‖ ^ (P.p - i + 1) := by
  by_cases hs : ‖s‖ < 1
  · exact (ha.short_request_le_power hchecked hs
      (zero_le_one.trans (one_le_requestAmplification _ _)) hi
      (r.request_le_amplification hk hi)).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (norm_nonneg s) _))
  · have hl : 1 ≤ ‖s‖ := le_of_not_gt hs
    exact ((r.request_bounds hk hi).2.trans (r.initial_request_le i hi)).trans
      ((le_max_right _ _).trans (le_mul_of_one_le_right
        (effectiveAccuracy_pos P _).le (one_le_pow₀ hl)))

/-- Every active short-step request inherits its initial ratio times the checked first-order
accuracy. This sharper form retains the step constant used by model-gap transfer estimates. -/
theorem Execution.short_step_request_le_power {P : Parameters} {f : E → ℝ}
    {oracle : E → (ℕ → ℝ) → Coefficients E} {N : ℕ} (r : Execution P checked f oracle N)
    (hchecked : 1 ≤ checked) {k : ℕ} (hk : k ≤ N) {s : E}
    (ha : StepAccurate P checked (r.state k).request s) (hs : ‖s‖ < 1)
    {i : ℕ} (hi : i ∈ Finset.Icc 1 P.p) :
    (r.state k).request i ≤ requestAmplification P.p (r.state 0).request *
      P.kappaStep * ‖s‖ ^ (P.p - i + 1) :=
  ha.short_request_le_power hchecked hs
    (zero_le_one.trans (one_le_requestAmplification _ _)) hi (r.request_le_amplification hk hi)

/-- A globally valid oracle's actual coefficient errors have full-order short-step scaling,
with its common multiplier enlarged only by the fixed initial request amplification. -/
theorem Execution.short_step_coefficient_le_power {P : Parameters} {f : E → ℝ}
    (O : InexactTrustRegion.Oracle f P.p) {N : ℕ} (r : Execution P checked f O.derivative N)
    (hchecked : 1 ≤ checked) {k : ℕ} (hk : k ≤ N) {s : E}
    (ha : StepAccurate P checked (r.state k).request s) (hs : ‖s‖ < 1)
    {K : ℝ} (hK : 0 ≤ K) (hO : InexactTrustRegion.UniformAccuracy O K)
    {i : ℕ} (hi : i ∈ Finset.Icc 1 P.p) :
    ‖O.derivative (r.state k).point (r.state k).request i -
      iteratedFDeriv ℝ i f (r.state k).point‖ ≤
        (K * requestAmplification P.p (r.state 0).request) * P.kappaStep *
          ‖s‖ ^ (P.p - i + 1) := by
  exact (hO _ _ (fun _ hj => (r.request_bounds hk hj).1) i hi).trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
      (r.short_step_request_le_power hchecked hk ha hs hi) hK)

/-- For an actual retained inner result, full-order errors derived from the positive checked
range force the genuine objective ratio to be very successful beyond the corrected threshold. -/
theorem Execution.very_successful_of_large {P : Parameters} {f : E → ℝ}
    {oracle : E → (ℕ → ℝ) → Coefficients E} {N : ℕ} (r : Execution P checked f oracle N)
    (hchecked : 1 ≤ checked) {k : ℕ} (hk : k ≤ N)
    (I : Inspection P (f (r.state k).point) (oracle (r.state k).point (r.state k).request)
      (r.state k).sigma (r.state k).radii) (hq : I.order ≤ P.q)
    (s : InnerResult P (f (r.state k).point) (oracle (r.state k).point (r.state k).request)
      (r.state k).sigma I.radii (I.direction hq))
    (ha : StepAccurate P checked (r.state k).request s.step) {L K : ℝ}
    (hf : HigherOrderRegularization.DiagonalLipschitz f P.p L) (hK : 0 ≤ K)
    (hcoeff : ∀ i ∈ Finset.Icc 1 P.p,
      ‖oracle (r.state k).point (r.state k).request i -
        iteratedFDeriv ℝ i f (r.state k).point‖ ≤ K * (r.state k).request i)
    (hlarge : (2 * L + 4 * ((P.p + 1)! : ℝ) * effectiveAccuracy P (r.state 0).request * K) /
      (1 - P.eta2) ≤ (r.state k).sigma) :
    P.eta2 ≤ ratio P f oracle (r.state k) s.step := by
  have hσ : 0 ≤ (r.state k).sigma := P.sigmaMin_pos.le.trans (r.sigma_floor hk)
  have hd := InnerResult.decrement_pos I hq s hσ (r.valid_radii hk)
  have he : ∀ i ∈ Finset.Icc 1 P.p,
      ‖oracle (r.state k).point (r.state k).request i -
        iteratedFDeriv ℝ i f (r.state k).point‖ ≤
        K * effectiveAccuracy P (r.state 0).request * ‖s.step‖ ^ (P.p - i + 1) := by
    intro i hi
    exact (hcoeff i hi).trans (by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
        (r.step_request_le_power hchecked hk ha hi) hK)
  exact very_successful_of_step_accuracy hf hK (effectiveAccuracy_pos P _).le
    he hd.2.1 hd.1 hlarge

/-- Global oracle accuracy and the actual inner return certify a very successful ratio at
the corrected threshold, without a separate supplied coefficient-error hypothesis. -/
theorem Execution.very_successful_of_oracle {P : Parameters} {f : E → ℝ}
    (O : InexactTrustRegion.Oracle f P.p) {N : ℕ} (r : Execution P checked f O.derivative N)
    (hchecked : 1 ≤ checked) {k : ℕ} (hk : k ≤ N)
    (I : Inspection P (f (r.state k).point) (O.derivative (r.state k).point (r.state k).request)
      (r.state k).sigma (r.state k).radii) (hq : I.order ≤ P.q)
    (s : InnerResult P (f (r.state k).point) (O.derivative (r.state k).point (r.state k).request)
      (r.state k).sigma I.radii (I.direction hq))
    (ha : StepAccurate P checked (r.state k).request s.step) {L K : ℝ}
    (hf : HigherOrderRegularization.DiagonalLipschitz f P.p L) (hK : 0 ≤ K)
    (hO : InexactTrustRegion.UniformAccuracy O K)
    (hlarge : (2 * L + 4 * ((P.p + 1)! : ℝ) * effectiveAccuracy P (r.state 0).request * K) /
      (1 - P.eta2) ≤ (r.state k).sigma) :
    P.eta2 ≤ ratio P f O.derivative (r.state k) s.step :=
  r.very_successful_of_large hchecked hk I hq s ha hf hK
    (fun i hi => hO _ _ (fun _ hj => (r.request_bounds hk hj).1) i hi) hlarge

/-- A large parameter cannot increase in a reachable transition whose positive checked
range and proportional requests provide all-order accuracy for the actual supplied model. -/
theorem Execution.sigma_step_nonincrease_of_large {P : Parameters} {f : E → ℝ}
    {oracle : E → (ℕ → ℝ) → Coefficients E} {N : ℕ} (r : Execution P checked f oracle N)
    (hchecked : 1 ≤ checked) {k : ℕ} (hk : k < N) {L K : ℝ}
    (hf : HigherOrderRegularization.DiagonalLipschitz f P.p L) (hK : 0 ≤ K)
    (hcoeff : ∀ i ∈ Finset.Icc 1 P.p,
      ‖oracle (r.state k).point (r.state k).request i -
        iteratedFDeriv ℝ i f (r.state k).point‖ ≤ K * (r.state k).request i)
    (hlarge : (2 * L + 4 * ((P.p + 1)! : ℝ) * effectiveAccuracy P (r.state 0).request * K) /
      (1 - P.eta2) ≤ (r.state k).sigma) :
    (r.state (k + 1)).sigma ≤ (r.state k).sigma := by
  have ht := r.transition k hk
  generalize r.state (k + 1) = nextState at ht ⊢
  generalize r.trial k = trial at ht
  generalize r.accepted k = accepted at ht
  cases ht with
  | refineInspection => exact le_rfl
  | refineStep => exact le_rfl
  | trial I hq s hacc next hu =>
    have hv := r.very_successful_of_large hchecked hk.le I hq s hacc hf hK hcoeff hlarge
    unfold HigherOrderApproximateRegularization.ParameterUpdate at hu
    simp only [ite_eq_left hv] at hu
    split_ifs <;> exact hu.2

/-- Every state of a literal positive-order checked execution has a uniform parameter bound.
The formula explicitly retains the maximum initial request ratio; no model-quality or
parameter-bound certificate is assumed. -/
theorem Execution.sigma_upper_of_initial_requests {P : Parameters} {f : E → ℝ}
    {oracle : E → (ℕ → ℝ) → Coefficients E} {N : ℕ} (r : Execution P checked f oracle N)
    (hchecked : 1 ≤ checked) {L K : ℝ}
    (hf : HigherOrderRegularization.DiagonalLipschitz f P.p L) (hK : 0 ≤ K)
    (hcoeff : ∀ k < N, ∀ i ∈ Finset.Icc 1 P.p,
      ‖oracle (r.state k).point (r.state k).request i -
        iteratedFDeriv ℝ i f (r.state k).point‖ ≤ K * (r.state k).request i)
    {k : ℕ} (hk : k ≤ N) :
    (r.state k).sigma ≤ max (r.state 0).sigma
      (P.gamma3 * ((2 * L + 4 * ((P.p + 1)! : ℝ) *
        effectiveAccuracy P (r.state 0).request * K) / (1 - P.eta2))) := by
  let T := (2 * L + 4 * ((P.p + 1)! : ℝ) * effectiveAccuracy P (r.state 0).request * K) /
    (1 - P.eta2)
  have hg : 0 ≤ P.gamma3 := (zero_lt_one.trans
    (P.one_lt_gamma2.trans P.gamma2_lt_gamma3)).le
  induction k with
  | zero => exact le_max_left _ _
  | succ k ih =>
    have hs : 0 ≤ (r.state k).sigma := P.sigmaMin_pos.le.trans (r.sigma_floor (by omega))
    by_cases hb : T ≤ (r.state k).sigma
    · exact (r.sigma_step_nonincrease_of_large hchecked (by omega) hf hK
        (hcoeff k (by omega)) hb).trans (ih (by omega))
    · exact ((r.transition k (by omega)).sigma_le_gamma3 hs).trans
        ((mul_le_mul_of_nonneg_left (le_of_not_ge hb) hg).trans (le_max_right _ _))

/-- A global all-positive-request oracle contract supplies every coefficient hypothesis of
the uniform bound. The checked range need only contain degree one. -/
theorem Execution.sigma_upper_of_oracle {P : Parameters} {f : E → ℝ}
    (O : InexactTrustRegion.Oracle f P.p) {N : ℕ} (r : Execution P checked f O.derivative N)
    (hchecked : 1 ≤ checked) {L K : ℝ}
    (hf : HigherOrderRegularization.DiagonalLipschitz f P.p L) (hK : 0 ≤ K)
    (hO : InexactTrustRegion.UniformAccuracy O K) {k : ℕ} (hk : k ≤ N) :
    (r.state k).sigma ≤ max (r.state 0).sigma
      (P.gamma3 * ((2 * L + 4 * ((P.p + 1)! : ℝ) *
        effectiveAccuracy P (r.state 0).request * K) / (1 - P.eta2))) :=
  r.sigma_upper_of_initial_requests hchecked hf hK
    (fun _ hk i hi => hO _ _ (fun _ hj => (r.request_bounds hk.le hj).1) i hi) hk

end Optimization.InexactRegularization
