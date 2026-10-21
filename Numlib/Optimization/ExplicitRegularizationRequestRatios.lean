import Numlib.Optimization.ExplicitRegularizationBounds
import Numlib.Optimization.InexactRegularizationRequestRatios

/-!
# Actual proportional requests for explicit regularization

Every tensor request contracts by the same geometric factor at accuracy-only iterations.
Trials preserve the tensor request vector, independently of their endpoint-value requests
and cache behavior. The fixed initial request ratios therefore lift the literal checked
first request to full-order short-step scaling. Long steps retain their independent cap.
-/

noncomputable section
namespace Optimization.ExplicitRegularization
open InexactTaylorModels InexactRegularization
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Every refinement contracts all tensor requests by the same factor; value trials leave
that derivative key unchanged, including when endpoint values are recomputed. -/
theorem Transition.request_eq {P : Parameters} {f : E → ℝ} {O : Oracle f P.p}
    {a b : State E} {I : Inspection P O.derivative a} {trial accepted : Bool}
    {queries : List (E × ℝ)} (t : Transition P O a I b trial accepted queries) (i : ℕ) :
    b.request i = (if trial then 1 else P.gammaAccuracy) * a.request i := by
  cases t with
  | refineInspection => rfl
  | refineStep => rfl
  | trial => unfold trialState; split_ifs <;> simp_all

/-- Tensor requests have their exact common geometric scale along every actual transition. -/
theorem Execution.request_eq {P : Parameters} {f : E → ℝ} {O : Oracle f P.p} {N : ℕ}
    (r : Execution P O N) {k : ℕ} (hk : k ≤ N) (i : ℕ) :
    (r.state k).request i =
      P.gammaAccuracy ^ ((Finset.range k).filter fun l => r.trial l = false).card *
        (r.state 0).request i := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [(r.transition k (by omega)).request_eq i, ih (by omega)]
    by_cases ht : r.trial k = true
    · simp [Finset.range_add_one, Finset.filter_insert, ht]
    · simp [Finset.range_add_one, Finset.filter_insert, ht, pow_succ]
      ring

/-- Every request has its exact initial proportion to the first request. The invariant includes
both refinement branches and accepted or rejected trials, through their common geometric scale. -/
theorem Execution.request_proportional {P : Parameters} {f : E → ℝ}
    {O : Oracle f P.p} {N : ℕ} (r : Execution P O N)
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
    {O : Oracle f P.p} {N : ℕ} (r : Execution P O N)
    {k : ℕ} (hk : k ≤ N) (i : ℕ) :
    (r.state k).request i / (r.state k).request 1 =
      (r.state 0).request i / (r.state 0).request 1 := by
  have hp : 1 ∈ Finset.Icc 1 P.p :=
    Finset.mem_Icc.mpr ⟨le_rfl, P.order_pos.trans P.order_le⟩
  rw [r.request_proportional hk i, mul_div_cancel_right₀ _ (r.request_bounds hk hp).1.ne']

/-- The largest initial request ratio controls every active request by the current first one. -/
theorem Execution.request_le_amplification {P : Parameters} {f : E → ℝ}
    {O : Oracle f P.p} {N : ℕ} (r : Execution P O N)
    {k i : ℕ} (hk : k ≤ N) (hi : i ∈ Finset.Icc 1 P.p) :
    (r.state k).request i ≤ requestAmplification P.p (r.state 0).request *
      (r.state k).request 1 := by
  have hp : 1 ∈ Finset.Icc 1 P.p :=
    Finset.mem_Icc.mpr ⟨le_rfl, P.order_pos.trans P.order_le⟩
  rw [r.request_proportional hk i]
  exact mul_le_mul_of_nonneg_right (request_ratio_le_amplification _ hi)
    (r.request_bounds hk hp).1.le

/-- Every active request at a reachable checked step has full-order step scaling. This covers
all positive checked degrees, including the literal case `checked=q<p`, and the long-step bypass. -/
theorem Execution.step_request_le_power {P : Parameters} {f : E → ℝ}
    {O : Oracle f P.p} {N : ℕ} (r : Execution P O N) {k : ℕ} (hk : k ≤ N) {s : E}
    (ha : InexactRegularization.StepAccurate P.toImplicitParameters P.q (r.state k).request s)
    {i : ℕ} (hi : i ∈ Finset.Icc 1 P.p) :
    (r.state k).request i ≤ effectiveAccuracy P.toImplicitParameters (r.state 0).request *
      ‖s‖ ^ (P.p - i + 1) := by
  by_cases hs : ‖s‖ < 1
  · exact (ha.short_request_le_power P.order_pos hs
      (zero_le_one.trans (one_le_requestAmplification _ _)) hi
      (r.request_le_amplification hk hi)).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (norm_nonneg s) _))
  · have hl : 1 ≤ ‖s‖ := le_of_not_gt hs
    exact ((r.request_bounds hk hi).2.trans (r.initial_request_le i hi)).trans
      ((le_max_right _ _).trans (le_mul_of_one_le_right
        (effectiveAccuracy_pos P.toImplicitParameters _).le (one_le_pow₀ hl)))

/-- Every active short-step request inherits its initial ratio times the checked first-order
accuracy. This sharper form retains the step constant used by model-gap transfer estimates. -/
theorem Execution.short_step_request_le_power {P : Parameters} {f : E → ℝ}
    {O : Oracle f P.p} {N : ℕ} (r : Execution P O N) {k : ℕ} (hk : k ≤ N) {s : E}
    (ha : InexactRegularization.StepAccurate P.toImplicitParameters P.q (r.state k).request s)
    (hs : ‖s‖ < 1)
    {i : ℕ} (hi : i ∈ Finset.Icc 1 P.p) :
    (r.state k).request i ≤ requestAmplification P.p (r.state 0).request *
      P.kappaStep * ‖s‖ ^ (P.p - i + 1) :=
  ha.short_request_le_power P.order_pos hs
    (zero_le_one.trans (one_le_requestAmplification _ _)) hi (r.request_le_amplification hk hi)

end Optimization.ExplicitRegularization
