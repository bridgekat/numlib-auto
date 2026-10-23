import Numlib.Optimization.TrustRegion.Inexact.FunctionDecrease
import Numlib.Optimization.TrustRegion.Inexact.Complexity
/-!
# Operational trust regions with explicit dynamic accuracy

The computed optimality directions and their finite known error budget define
the actual stopping test. Trials use two approximate objective values and their
actual ratio. Accuracy-only iterations arise from a passing computed loop with
an unverified budget or a failed relative step request. Radius floors and true
optimality at stopping are consequences, not primitive execution assumptions.
-/

namespace InexactTrustRegion.Explicit
open Set EvaluationComplexity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
/-- Fixed TRqEDA settings include the known unit oracle and both objective error margins. -/
structure Settings (q : ℕ) extends toImplicit : InexactTrustRegion.Settings q where
  known_unit_bound : oracleBound = 1
  function_acceptance_margin : requestFactor ≤ eta1 / 4
  function_success_margin : requestFactor ≤ (1 - eta2) / 4
/-- The actual computed jets, selected directions, radius history, requests and objective values. -/
structure ExecutionData (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (q : ℕ) where
  jet : ℕ → FormalMultilinearSeries ℝ E ℝ
  trials : Set ℕ
  order : ℕ → Fin q
  point : ℕ → E
  reference : ℕ → E
  step : ℕ → E
  radius : ℕ → ℝ
  ratio : ℕ → ℝ
  accuracy : ℕ → ℕ → ℝ
  checkDirection : ℕ → Fin q → E
  functionStart : ℕ → ℝ
  functionTrial : ℕ → ℝ
  functionRequest : ℕ → ℝ
/-- Every actual computed all-order optimality test passes at the current capped radius. -/
def PassingAt {q : ℕ} (P : Settings q) (ε : Fin q → ℝ)
    (D : ExecutionData E q) (k : ℕ) : Prop :=
  ∀ a : Fin q, TaylorModel.jetDecrement (D.jet k) (modelOrder a) (D.checkDirection k a) ≤
    P.zeta / 2 * ε a * optimalityRadius P.theta (D.radius k) ^ modelOrder a /
      (modelOrder a).factorial
/-- The literal TRqEDA stopping test combines the completed computed loop
with its finite error budget. -/
def StopsAt {q : ℕ} (P : Settings q) (ε : Fin q → ℝ)
    (D : ExecutionData E q) (k : ℕ) : Prop :=
  PassingAt P ε D k ∧
    tensorErrorBudget (D.accuracy k) q (optimalityRadius P.theta (D.radius k)) ≤
    P.zeta / 2 * minimumAccuracy P.order_pos ε * optimalityRadius P.theta (D.radius k) ^ q /
      q.factorial
/-- A finite TRqEDA execution with actual computed directions, first failed order,
objective errors and ratios, point and radius updates, literal accuracy branches,
and the specified derivative and reference reuse after rejection. -/
structure Run {q : ℕ} (f : E → ℝ) (P : Settings q) (ε : Fin q → ℝ)
    (D : ExecutionData E q) (N : ℕ) : Prop
    extends FunctionModelTrace f D.jet D.trials D.order D.point D.reference D.step
      D.radius D.ratio D.functionStart D.functionTrial D.functionRequest ε D.accuracy
      P.zeta P.theta P.requestFactor P.eta1 P.eta2 P.gamma1 P.gamma2 P.gamma3 P.radiusMax N where
  initial_accuracy : ∀ a, 1 ≤ a → a ≤ q → D.accuracy 0 a ∈ Ioc 0 P.initialCap
  accuracy_trial : ∀ i < N, i ∈ D.trials → ∀ a, 1 ≤ a → a ≤ q →
    D.accuracy (i + 1) a = D.accuracy i a
  accuracy_improvement : ∀ i < N, i ∉ D.trials → ∀ a, 1 ≤ a → a ≤ q →
    D.accuracy (i + 1) a = P.reduction * D.accuracy i a
  oracle_all : ∀ i ≤ N, ∀ a, 1 ≤ a → a ≤ q →
    ‖D.jet i a - iteratedFDeriv ℝ a f (D.point i)‖ ≤ P.oracleBound * D.accuracy i a
  check_feasible : ∀ i ≤ N, ∀ a,
    ‖D.checkDirection i a‖ ≤ optimalityRadius P.theta (D.radius i)
  check_approximation : ∀ i ≤ N, ∀ a,
    P.zeta * TaylorModel.jetCriticality (D.jet i) (modelOrder a)
      (optimalityRadius P.theta (D.radius i)) ≤
        TaylorModel.jetDecrement (D.jet i) (modelOrder a) (D.checkDirection i a)
  chosen_direction : ∀ i ≤ N, D.reference i = D.checkDirection i (D.order i)
  earlier_passes : ∀ i ≤ N, ∀ a, a < D.order i →
    TaylorModel.jetDecrement (D.jet i) (modelOrder a) (D.checkDirection i a) ≤
      P.zeta / 2 * ε a * optimalityRadius P.theta (D.radius i) ^ modelOrder a /
        (modelOrder a).factorial
  constant_value : ∀ i < N, i ∈ D.trials → D.jet i 0 (fun _ => 0) = D.functionStart i
  reuse_direction : ∀ i < N, i ∈ D.trials → ¬P.eta1 ≤ D.ratio i →
    P.theta ≤ D.radius (i + 1) →
      D.order (i + 1) = D.order i ∧ D.reference (i + 1) = D.reference i
  no_exit : ∀ i < N, ¬StopsAt P ε D i
  point_trial : ∀ i < N, i ∈ D.trials →
    D.point (i + 1) = if P.eta1 ≤ D.ratio i then D.point i + D.step i else D.point i
  point_inactive : ∀ i < N, i ∉ D.trials → D.point (i + 1) = D.point i
  unchanged_jet : ∀ i < N, i ∈ D.trials → ¬P.eta1 ≤ D.ratio i →
    ∀ a, 1 ≤ a → a ≤ q → D.jet (i + 1) a = D.jet i a
  accuracy_branch : ∀ i < N, i ∉ D.trials → PassingAt P ε D i ∨
    (P.zeta / 2 * ε (D.order i) * optimalityRadius P.theta (D.radius i) ^ modelOrder (D.order i) /
        (modelOrder (D.order i)).factorial < decrement (D.jet i) (modelOrder (D.order i))
          (D.reference i) ∧ ‖D.step i‖ ≤ D.radius i ∧
      TaylorModel.ofJet (D.jet i) (modelOrder (D.order i)) (D.step i) ≤
        TaylorModel.ofJet (D.jet i) (modelOrder (D.order i)) (D.reference i) ∧
      ∃ a, 1 ≤ a ∧ a ≤ q ∧
        P.requestFactor * ‖D.step i‖ ^ (q - a + 1) < D.accuracy i a)
namespace Run
variable {q : ℕ} {f : E → ℝ} {P : Settings q} {ε : Fin q → ℝ}
  {D : ExecutionData E q} {N : ℕ}
/-- Each derivative request follows the actual multiplicative accuracy update rules. -/
theorem accuracy_updates (h : Run f P ε D N) {a : ℕ} (ha : 1 ≤ a) (haq : a ≤ q) :
    AccuracyUpdates D.trialsᶜ (fun i => D.accuracy i a) P.reduction N := by
  classical
  refine ⟨(h.initial_accuracy a ha haq).1, P.reduction_pos, P.reduction_lt_one, ?_⟩
  intro i hi
  by_cases hT : i ∈ D.trials
  · simpa [hT] using h.accuracy_trial i hi hT a ha haq
  · simpa [hT] using h.accuracy_improvement i hi hT a ha haq
/-- Actual derivative requests are positive and bounded by the geometrically reduced cap. -/
theorem accuracy_bounds (h : Run f P ε D N) {i a : ℕ} (hi : i ≤ N)
    (ha : 1 ≤ a) (haq : a ≤ q) :
    0 < D.accuracy i a ∧ D.accuracy i a ≤ accuracyCap P.toImplicit D.trials i ∧
      accuracyCap P.toImplicit D.trials i ≤ P.initialCap := by
  have hu := h.accuracy_updates ha haq
  refine ⟨hu.pos hi, ?_, ?_⟩
  · rw [hu.eq_initial_mul_pow hi]
    exact mul_le_mul_of_nonneg_right (h.initial_accuracy a ha haq).2
      (pow_nonneg P.reduction_pos.le _)
  · exact mul_le_of_le_one_right P.initialCap_pos.le
      (pow_le_one₀ P.reduction_pos.le P.reduction_lt_one.le)
/-- The actual inexact-objective acceptance ratio yields a fixed uniform optimality-radius floor. -/
theorem radius_floor (h : Run f P ε D N) (hf : ContDiff ℝ q f) {L : ℝ} (hL : 1 ≤ L)
    (hlip : ∀ a, 1 ≤ a → a ≤ q → ∀ u v,
      ‖iteratedFDeriv ℝ a f u - iteratedFDeriv ℝ a f v‖ ≤ L * ‖u - v‖)
    {i : ℕ} (hi : i ≤ N) :
    P.zeta * (positiveRadiusCoefficient P.toImplicit L / 2) * minimumAccuracy P.order_pos ε ≤
      optimalityRadius P.theta (D.radius i) := by
  have hκ := (positiveRadiusCoefficient_properties P.toImplicit hL).2.2
  simp only [P.known_unit_bound, mul_one] at hκ
  exact h.toFunctionModelTrace.optimalityRadius_lower hf hL hlip hκ hi
variable [ProperSpace E]
/-- Literal stopping certifies every true Taylor criticality measure at the actual capped radius. -/
theorem stopped_optimality (h : Run f P ε D N) {i : ℕ} (hi : i ≤ N) (hs : StopsAt P ε D i) :
    ∀ a : Fin q, TaylorModel.criticality f (modelOrder a) (D.point i)
      (optimalityRadius P.theta (D.radius i)) ≤
        ε a * optimalityRadius P.theta (D.radius i) ^ modelOrder a / (modelOrder a).factorial := by
  have hc : TerminationCheck (D.jet i) (optimalityRadius P.theta (D.radius i))
      P.zeta ε (D.checkDirection i) (D.accuracy i) :=
    ⟨P.order_pos, (lt_min P.theta_pos (h.updates.pos hi)).le,
      (min_le_left _ _).trans P.theta_le_one, P.zeta_pos, P.zeta_le_one, h.accuracy_pos,
      h.check_approximation i hi, hs.1, hs.2⟩
  apply hc.true_optimality f (D.point i)
  intro a ha haq
  simpa only [P.known_unit_bound, one_mul] using h.oracle_all i hi a ha haq

omit [ProperSpace E] in
/-- The common request cap follows exactly the accuracy-only reduction count. -/
theorem accuracyCap_updates : AccuracyUpdates D.trialsᶜ
    (accuracyCap P.toImplicit D.trials) P.reduction N :=
  InexactTrustRegion.Run.accuracyCap_updates
omit [ProperSpace E] in
/-- Primitive oracle requests and true lower-derivative Lipschitz bounds
uniformly bound computed tensors. -/
theorem tensor_norm_le (h : Run f P ε D N) {L : ℝ} (hL : 1 ≤ L)
    (hlip : ∀ a, a < q → ∀ u v,
      ‖iteratedFDeriv ℝ a f u - iteratedFDeriv ℝ a f v‖ ≤ L * ‖u - v‖)
    {i a : ℕ} (hi : i ≤ N) (ha : 1 ≤ a) (haq : a ≤ q) :
    ‖D.jet i a‖ ≤ L + P.oracleBound * P.initialCap :=
  TaylorModel.norm_jet_le_of_lipschitz_oracle (by linarith) P.initialCap_pos.le hlip
    (D.jet i) (D.point i) (fun _ => P.oracleBound) (D.accuracy i)
    (fun _ _ _ => ⟨P.oracleBound_nonneg, le_rfl⟩)
    (fun b hb hbq => (h.accuracy_bounds hi hb hbq).2.1.trans
      (h.accuracy_bounds hi hb hbq).2.2) (h.oracle_all i hi) ha haq
omit [ProperSpace E] in
/-- An accuracy-only iteration before literal stopping requires a request cap above
a fixed threshold. A passing computed loop with a sufficiently small cap
passes the actual verification test; the other branch satisfies every step request. -/
theorem accuracy_branch_large (h : Run f P ε D N)
    (hf : ContDiff ℝ q f) {L : ℝ} (hL : 1 ≤ L)
    (hlip : ∀ a, a ≤ q → ∀ u v,
      ‖iteratedFDeriv ℝ a f u - iteratedFDeriv ℝ a f v‖ ≤ L * ‖u - v‖)
    {i : ℕ} (hi : i < N) (hT : i ∉ D.trials) :
    accuracyCoefficient P.toImplicit L * minimumAccuracy P.order_pos ε ^ (q * (q + 1)) <
      accuracyCap P.toImplicit D.trials i := by
  by_contra hn
  have hcap := le_of_not_gt hn
  let μ := minimumAccuracy P.order_pos ε
  let κ := positiveRadiusCoefficient P.toImplicit L / 2
  let K := max 1 P.oracleBound
  let M := L + P.oracleBound * P.initialCap
  let H := accuracyCoefficient P.toImplicit L * μ ^ (q * (q + 1))
  have hμ : 0 < μ := minimumAccuracy_pos P.order_pos h.accuracy_pos
  have hμ1 : μ ≤ 1 :=
    (minimumAccuracy_le P.order_pos ε (D.order i)).trans (h.accuracy_le_one _)
  have hκp := positiveRadiusCoefficient_properties P.toImplicit hL
  have hκ : 0 < κ := div_pos hκp.1 (by norm_num)
  have hκ1 : κ ≤ 1 := by dsimp [κ]; linarith [hκp.2.1]
  have hζ := P.zeta_pos
  have hH : 0 < H := mul_pos (accuracyCoefficient_pos P.toImplicit hL) (pow_pos hμ _)
  have hK : 0 < K := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hM : 1 ≤ M := hL.trans (le_add_of_nonneg_right
    (mul_nonneg P.oracleBound_nonneg P.initialCap_pos.le))
  have haccuracy : ∀ a, 1 ≤ a → a ≤ q → D.accuracy i a ≤ H := by
    intro a ha haq
    exact (h.accuracy_bounds hi.le ha haq).2.1.trans hcap
  have hfirst : H ≤ accuracyThreshold q P.zeta κ K μ := by
    have hb : accuracyCoefficient P.toImplicit L ≤ accuracyThreshold q P.zeta κ K 1 :=
      min_le_left _ _
    have hp : μ ^ (q * (q + 1)) ≤ μ ^ (q + 1) :=
      pow_le_pow_of_le_one hμ.le hμ1 (by nlinarith [P.order_pos])
    have hm := mul_le_mul hb hp (pow_nonneg hμ.le _) (by
      unfold accuracyThreshold
      positivity : 0 ≤ accuracyThreshold q P.zeta κ K 1)
    convert hm using 1
    unfold accuracyThreshold
    simp only [one_pow, mul_one]
  have hsecond : H ≤ P.requestFactor * (accuracyThreshold q P.zeta κ M μ) ^ q := by
    have hb : accuracyCoefficient P.toImplicit L ≤
        P.requestFactor * (accuracyThreshold q P.zeta κ M 1) ^ q := min_le_right _ _
    have hm := mul_le_mul_of_nonneg_right hb (pow_nonneg hμ.le (q * (q + 1)))
    convert hm using 1
    unfold accuracyThreshold
    simp only [one_pow, mul_one]
    rw [mul_pow, ← pow_mul]
    simp only [Nat.mul_comm (q + 1) q]
    ring
  have hfloor := h.radius_floor hf hL (fun a _ ha => hlip a ha) hi.le
  have hδ := le_min P.theta_pos.le (h.updates.pos hi.le).le
  have hδ1 := (min_le_left P.theta (D.radius i)).trans P.theta_le_one
  rcases h.accuracy_branch i hi hT with hchecks | ⟨hfailed, hfeasible, hcompare,
    a, ha, haq, hbad⟩
  · have hc := terminationCheck_of_accuracyThreshold P.order_pos hδ hδ1
      P.zeta_pos P.zeta_le_one hκ.le hK hH.le h.accuracy_pos rfl hfloor hfirst
      haccuracy (h.check_approximation i hi.le) hchecks
    apply h.no_exit i hi
    refine ⟨hchecks, ?_⟩
    have he : (fun a => K * D.accuracy i a) = D.accuracy i := by
      funext a
      simp only [K, P.known_unit_bound, max_self, one_mul]
    have hv : tensorErrorBudget (fun a => K * D.accuracy i a) q
        (optimalityRadius P.theta (D.radius i)) ≤
      P.zeta / 2 * minimumAccuracy P.order_pos ε *
        optimalityRadius P.theta (D.radius i) ^ q / q.factorial := hc.verified
    rw [he] at hv
    exact hv
  · have htest : P.zeta / 2 * μ * optimalityRadius P.theta (D.radius i) ^ modelOrder (D.order i) /
        (modelOrder (D.order i)).factorial ≤
        decrement (D.jet i) (modelOrder (D.order i)) (D.step i) := by
      have he := mul_le_mul_of_nonneg_left (minimumAccuracy_le P.order_pos ε (D.order i))
        (show 0 ≤ P.zeta / 2 by positivity)
      have he' := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right he (pow_nonneg hδ (modelOrder (D.order i))))
        (Nat.cast_nonneg (modelOrder (D.order i)).factorial)
      have hc := sub_le_sub_left hcompare (TaylorModel.ofJet (D.jet i) (modelOrder (D.order i)) 0)
      exact he'.trans (hfailed.le.trans hc)
    have hs := norm_step_ge_of_failed_test (D.jet i) (D.order i).isLt P.zeta_pos.le P.zeta_le_one
      hκ.le hκ1 hM hμ.le hμ1 hfloor (D.step i)
      (fun a ha haj => h.tensor_norm_le hL (fun a ha => hlip a ha.le) hi.le
        ha (haj.trans (D.order i).isLt)) htest
    have hc : 0 ≤ accuracyThreshold q P.zeta κ M μ := by unfold accuracyThreshold; positivity
    have hc1 := accuracyThreshold_le_one (q := q) P.zeta_pos.le P.zeta_le_one
      hκ.le hκ1 hM hμ.le hμ1
    have hr := requests_of_norm_floor hc hc1 P.requestFactor_pos.le hsecond
      (D.accuracy i) haccuracy (D.step i) hs a ha haq
    exact (not_lt_of_ge hr) hbad

end Run
end InexactTrustRegion.Explicit
