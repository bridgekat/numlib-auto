import Numlib.Optimization.TrustRegion.Inexact.RadiusConsequences
import Numlib.Optimization.TrustRegion.HighOrder.Complexity
import Numlib.Optimization.EvaluationComplexity.AccuracyUpdates

/-!
# Actual implicit-dynamic-accuracy trust-region executions

Finite traces specify model selection, actual oracle errors, requested-accuracy
updates, acceptance ratios, point/radius updates, and the two concrete routes
to an accuracy improvement. No true optimality, decrease or radius floor is a field.
-/

namespace InexactTrustRegion
open Set EvaluationComplexity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Fixed algorithm settings, chosen independently of the requested accuracies. -/
structure Settings (q : ℕ) extends HighOrderTrustRegion.Settings q where
  requestFactor : ℝ
  requestFactor_pos : 0 < requestFactor
  oracleBound : ℝ
  oracleBound_nonneg : 0 ≤ oracleBound
  initialCap : ℝ
  initialCap_pos : 0 < initialCap
  reduction : ℝ
  reduction_pos : 0 < reduction
  reduction_lt_one : reduction < 1

/-- A genuine finite TRqIDA execution, including the literal passing Step 1
loop or failed Step 2 request that causes each accuracy-only iteration. -/
structure Run {q : ℕ} (f : E → ℝ) (P : Settings q) (ε : Fin q → ℝ)
    (A : ℕ → FormalMultilinearSeries ℝ E ℝ) (T : Set ℕ) (j : ℕ → Fin q)
    (x d s : ℕ → E) (Δ ρ : ℕ → ℝ) (accuracy : ℕ → ℕ → ℝ) (N : ℕ) : Prop
    extends ExecutionTrace f A T j x d s Δ ρ ε accuracy P.zeta P.theta
      P.requestFactor P.oracleBound P.eta1 P.eta2 P.gamma1 P.gamma2 P.gamma3 P.radiusMax N where
  initial_accuracy : ∀ a, 1 ≤ a → a ≤ q → accuracy 0 a ∈ Ioc 0 P.initialCap
  accuracy_trial : ∀ i < N, i ∈ T → ∀ a, 1 ≤ a → a ≤ q →
    accuracy (i + 1) a = accuracy i a
  accuracy_improvement : ∀ i < N, i ∉ T → ∀ a, 1 ≤ a → a ≤ q →
    accuracy (i + 1) a = P.reduction * accuracy i a
  oracle_all : ∀ i ≤ N, ∀ a, 1 ≤ a → a ≤ q →
    ‖A i a - iteratedFDeriv ℝ a f (x i)‖ ≤ P.oracleBound * accuracy i a
  unchanged_jet : ∀ i < N, i ∈ T → ¬P.eta1 ≤ ρ i → A (i + 1) = A i
  accuracy_branch : ∀ i < N, i ∉ T →
    (∃ direction : Fin q → E, ∀ a,
      ‖direction a‖ ≤ optimalityRadius P.theta (Δ i) ∧
      P.zeta * TaylorModel.jetCriticality (A i) (modelOrder a)
        (optimalityRadius P.theta (Δ i)) ≤
        TaylorModel.jetDecrement (A i) (modelOrder a) (direction a) ∧
      TaylorModel.jetDecrement (A i) (modelOrder a) (direction a) ≤
        P.zeta / 2 * ε a * optimalityRadius P.theta (Δ i) ^ modelOrder a /
          (modelOrder a).factorial) ∨
    (P.zeta / 2 * ε (j i) * optimalityRadius P.theta (Δ i) ^ modelOrder (j i) /
        (modelOrder (j i)).factorial < decrement (A i) (modelOrder (j i)) (d i) ∧
      TaylorModel.ofJet (A i) (modelOrder (j i)) (s i) ≤
        TaylorModel.ofJet (A i) (modelOrder (j i)) (d i) ∧
      ∃ a, 1 ≤ a ∧ a ≤ q ∧
        P.requestFactor * ‖s i‖ ^ (q - a + 1) < accuracy i a)

/-- A fixed, strictly positive radius coefficient that also covers a vanishing
initial true derivative jet and an exact tensor oracle. -/
noncomputable def positiveRadiusCoefficient {q : ℕ} (P : Settings q) (L : ℝ) : ℝ :=
  min 1 (P.gamma1 * ((1 - P.eta2) /
    acceptanceCoefficient q L (P.requestFactor * P.oracleBound))) * P.theta

/-- The fixed coefficient is positive, at most one, and admissible for the
operational radius-floor theorem. -/
theorem positiveRadiusCoefficient_properties {q : ℕ} (P : Settings q) {L : ℝ} (hL : 1 ≤ L) :
    0 < positiveRadiusCoefficient P L ∧ positiveRadiusCoefficient P L ≤ 1 ∧
      positiveRadiusCoefficient P L ≤ P.gamma1 * ((1 - P.eta2) /
        acceptanceCoefficient q L (P.requestFactor * P.oracleBound)) := by
  have hK := mul_nonneg P.requestFactor_pos.le P.oracleBound_nonneg
  have hC : 0 < acceptanceCoefficient q L (P.requestFactor * P.oracleBound) := by
    dsimp [acceptanceCoefficient]
    positivity
  have hc : 0 < P.gamma1 * ((1 - P.eta2) /
      acceptanceCoefficient q L (P.requestFactor * P.oracleBound)) :=
    mul_pos P.gamma1_pos (div_pos (sub_pos.mpr P.eta2_lt_one) hC)
  have hm := lt_min (by norm_num : (0 : ℝ) < 1) hc
  unfold positiveRadiusCoefficient
  refine ⟨mul_pos hm P.theta_pos, ?_, ?_⟩
  · exact (mul_le_of_le_one_left P.theta_pos.le (min_le_left _ _)).trans P.theta_le_one
  · exact (mul_le_of_le_one_right hm.le P.theta_le_one).trans (min_le_right _ _)

/-- The uniform cap obtained after the actual number of accuracy-only reductions. -/
noncomputable def accuracyCap {q : ℕ} (P : Settings q) (T : Set ℕ) (i : ℕ) : ℝ :=
  P.initialCap * P.reduction ^ (successfulIterations Tᶜ i).card

namespace Run
variable {q : ℕ} {f : E → ℝ} {P : Settings q} {ε : Fin q → ℝ}
  {A : ℕ → FormalMultilinearSeries ℝ E ℝ} {T : Set ℕ} {j : ℕ → Fin q}
  {x d s : ℕ → E} {Δ ρ : ℕ → ℝ} {accuracy : ℕ → ℕ → ℝ} {N : ℕ}

/-- Each derivative's actual requested accuracy obeys the primitive scalar
multiplicative reduction rules. -/
theorem accuracy_updates (h : Run f P ε A T j x d s Δ ρ accuracy N)
    {a : ℕ} (ha : 1 ≤ a) (haq : a ≤ q) :
    AccuracyUpdates Tᶜ (fun i => accuracy i a) P.reduction N := by
  classical
  refine ⟨(h.initial_accuracy a ha haq).1, P.reduction_pos, P.reduction_lt_one, ?_⟩
  intro i hi
  by_cases hT : i ∈ T
  · simpa [hT] using
      h.accuracy_trial i hi hT a ha haq
  · simpa [hT] using
      h.accuracy_improvement i hi hT a ha haq

/-- Every actual request is positive and lies below the uniform geometrically
reduced cap, which in turn is bounded by the initial cap. -/
theorem accuracy_bounds (h : Run f P ε A T j x d s Δ ρ accuracy N)
    {i : ℕ} (hi : i ≤ N) {a : ℕ} (ha : 1 ≤ a) (haq : a ≤ q) :
    0 < accuracy i a ∧ accuracy i a ≤ accuracyCap P T i ∧ accuracyCap P T i ≤
      P.initialCap := by
  have hu := h.accuracy_updates ha haq
  refine ⟨hu.pos hi, ?_, ?_⟩
  · rw [hu.eq_initial_mul_pow hi]
    exact mul_le_mul_of_nonneg_right (h.initial_accuracy a ha haq).2 (pow_nonneg
      P.reduction_pos.le _)
  · exact mul_le_of_le_one_right P.initialCap_pos.le
      (pow_le_one₀ P.reduction_pos.le P.reduction_lt_one.le)

/-- The uniform cap itself follows the same actual iteration-class updates. -/
theorem accuracyCap_updates :
    AccuracyUpdates Tᶜ (accuracyCap P T) P.reduction N := by
  classical
  refine ⟨by simpa only [accuracyCap, successfulIterations, Finset.range_zero,
    Finset.filter_empty, Finset.card_empty, pow_zero, mul_one] using P.initialCap_pos,
    P.reduction_pos, P.reduction_lt_one, ?_⟩
  intro i hi
  unfold accuracyCap
  rw [card_successful_succ]
  split_ifs
  · rw [pow_succ]; ring
  · simp

/-- Every computed tensor has the source's uniform norm bound, derived from
actual lower-derivative Lipschitz estimates and primitive oracle requests. -/
theorem tensor_norm_le (h : Run f P ε A T j x d s Δ ρ accuracy N)
    {L : ℝ} (hL : 1 ≤ L)
    (hlip : ∀ a, a < q → ∀ u v,
      ‖iteratedFDeriv ℝ a f u - iteratedFDeriv ℝ a f v‖ ≤ L * ‖u - v‖)
    {i : ℕ} (hi : i ≤ N) {a : ℕ} (ha : 1 ≤ a) (haq : a ≤ q) :
    ‖A i a‖ ≤ L + P.oracleBound * P.initialCap :=
  TaylorModel.norm_jet_le_of_lipschitz_oracle (by linarith) P.initialCap_pos.le hlip
    (A i) (x i) (fun _ => P.oracleBound) (accuracy i)
    (fun _ _ _ => ⟨P.oracleBound_nonneg, le_rfl⟩)
    (fun b hb hbq => (h.accuracy_bounds hi hb hbq).2.1.trans
      (h.accuracy_bounds hi hb hbq).2.2) (h.oracle_all i hi) ha haq

end Run

/-- A positive fixed accuracy coefficient for both concrete accuracy-improvement
branches. The unit lower bound on the oracle coefficient also covers exact oracles. -/
noncomputable def accuracyCoefficient {q : ℕ} (P : Settings q) (L : ℝ) : ℝ :=
  let κ := positiveRadiusCoefficient P L / 2
  min (accuracyThreshold q P.zeta κ (max 1 P.oracleBound) 1)
    (P.requestFactor * (accuracyThreshold q P.zeta κ
      (L + P.oracleBound * P.initialCap) 1) ^ q)

/-- The fixed accuracy coefficient is strictly positive independently of the
requested tolerances and every actual execution. -/
theorem accuracyCoefficient_pos {q : ℕ} (P : Settings q) {L : ℝ} (hL : 1 ≤ L) :
    0 < accuracyCoefficient P L := by
  have hκ := (positiveRadiusCoefficient_properties P hL).1
  have hζ := P.zeta_pos
  have hM : 0 < L + P.oracleBound * P.initialCap := by
    have hh := mul_nonneg P.oracleBound_nonneg P.initialCap_pos.le
    linarith
  have hK : 0 < max 1 P.oracleBound := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hs := P.requestFactor_pos
  unfold accuracyCoefficient accuracyThreshold
  positivity

/-- Failure of true all-order Taylor approximate optimality at a given radius. -/
def NotOptimal {q : ℕ} (f : E → ℝ) (ε : Fin q → ℝ) (x : E) (δ : ℝ) : Prop :=
  ¬ ∀ a : Fin q, TaylorModel.criticality f (modelOrder a) x δ ≤
    ε a * δ ^ modelOrder a / (modelOrder a).factorial

namespace Run
variable {q : ℕ} {f : E → ℝ} {P : Settings q} {ε : Fin q → ℝ}
  {A : ℕ → FormalMultilinearSeries ℝ E ℝ} {T : Set ℕ} {j : ℕ → Fin q}
  {x d s : ℕ → E} {Δ ρ : ℕ → ℝ} {accuracy : ℕ → ℕ → ℝ} {N : ℕ}

/-- The positive fixed radius coefficient gives the actual endpoint radius floor. -/
theorem radius_floor (h : Run f P ε A T j x d s Δ ρ accuracy N)
    (hf : ContDiff ℝ q f) {L : ℝ} (hL : 1 ≤ L)
    (hlip : ∀ a, 1 ≤ a → a ≤ q → ∀ u v,
      ‖iteratedFDeriv ℝ a f u - iteratedFDeriv ℝ a f v‖ ≤ L * ‖u - v‖)
    {i : ℕ} (hi : i ≤ N) :
    P.zeta * (positiveRadiusCoefficient P L / 2) * minimumAccuracy P.order_pos ε ≤
      optimalityRadius P.theta (Δ i) :=
  h.toModelTrace.optimalityRadius_lower hf hL hlip
    (positiveRadiusCoefficient_properties P hL).2.2 hi

variable [ProperSpace E]

/-- Once the geometrically reduced cap crosses the fixed threshold, neither
concrete accuracy-improving branch is possible before true optimality. -/
theorem accuracy_branch_large (h : Run f P ε A T j x d s Δ ρ accuracy N)
    (hf : ContDiff ℝ q f) {L : ℝ} (hL : 1 ≤ L)
    (hlip : ∀ a, a ≤ q → ∀ u v,
      ‖iteratedFDeriv ℝ a f u - iteratedFDeriv ℝ a f v‖ ≤ L * ‖u - v‖)
    {i : ℕ} (hi : i < N) (hT : i ∉ T)
    (hnot : NotOptimal f ε (x i) (optimalityRadius P.theta (Δ i))) :
    accuracyCoefficient P L * minimumAccuracy P.order_pos ε ^ (q * (q + 1)) <
      accuracyCap P T i := by
  by_contra hn
  have hcap := le_of_not_gt hn
  let μ := minimumAccuracy P.order_pos ε
  let κ := positiveRadiusCoefficient P L / 2
  let K := max 1 P.oracleBound
  let M := L + P.oracleBound * P.initialCap
  let H := accuracyCoefficient P L * μ ^ (q * (q + 1))
  have hμ : 0 < μ := minimumAccuracy_pos P.order_pos h.accuracy_pos
  have hμ1 : μ ≤ 1 := (minimumAccuracy_le P.order_pos ε (j i)).trans (h.accuracy_le_one _)
  have hκp := positiveRadiusCoefficient_properties P hL
  have hκ : 0 < κ := div_pos hκp.1 (by norm_num)
  have hκ1 : κ ≤ 1 := by dsimp [κ]; linarith [hκp.2.1]
  have hζ := P.zeta_pos
  have hH : 0 < H := mul_pos (accuracyCoefficient_pos P hL) (pow_pos hμ _)
  have hK : 0 < K := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hM : 1 ≤ M := hL.trans (le_add_of_nonneg_right
    (mul_nonneg P.oracleBound_nonneg P.initialCap_pos.le))
  have haccuracy : ∀ a, 1 ≤ a → a ≤ q → accuracy i a ≤ H := by
    intro a ha haq
    exact (h.accuracy_bounds hi.le ha haq).2.1.trans hcap
  have hfirst : H ≤ accuracyThreshold q P.zeta κ K μ := by
    have hb : accuracyCoefficient P L ≤ accuracyThreshold q P.zeta κ K 1 := min_le_left _ _
    have hp : μ ^ (q * (q + 1)) ≤ μ ^ (q + 1) :=
      pow_le_pow_of_le_one hμ.le hμ1 (by nlinarith [P.order_pos])
    have hm := mul_le_mul hb hp (pow_nonneg hμ.le _) (by
      unfold accuracyThreshold
      positivity : 0 ≤ accuracyThreshold q P.zeta κ K 1)
    convert hm using 1
    unfold accuracyThreshold
    simp only [one_pow, mul_one]
  have hsecond : H ≤ P.requestFactor * (accuracyThreshold q P.zeta κ M μ) ^ q := by
    have hb : accuracyCoefficient P L ≤
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
  have hδ1 := (min_le_left P.theta (Δ i)).trans P.theta_le_one
  rcases h.accuracy_branch i hi hT with ⟨direction, hchecks⟩ | ⟨hfailed, hcompare,
    a, ha, haq, hbad⟩
  · have hc := terminationCheck_of_accuracyThreshold P.order_pos hδ hδ1
      P.zeta_pos P.zeta_le_one hκ.le hK hH.le h.accuracy_pos rfl hfloor hfirst
      haccuracy (fun a => (hchecks a).2.1) (fun a => (hchecks a).2.2)
    apply hnot
    apply hc.true_optimality f (x i)
    intro a ha haq
    exact (h.oracle_all i hi.le a ha haq).trans
      (mul_le_mul_of_nonneg_right (le_max_right 1 P.oracleBound)
        (h.accuracy_bounds hi.le ha haq).1.le)
  · have htest : P.zeta / 2 * μ * optimalityRadius P.theta (Δ i) ^ modelOrder (j i) /
        (modelOrder (j i)).factorial ≤ decrement (A i) (modelOrder (j i)) (s i) := by
      have he := mul_le_mul_of_nonneg_left (minimumAccuracy_le P.order_pos ε (j i))
        (show 0 ≤ P.zeta / 2 by positivity)
      have he' := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right he (pow_nonneg hδ (modelOrder (j i))))
        (Nat.cast_nonneg (modelOrder (j i)).factorial)
      have hc := sub_le_sub_left hcompare (TaylorModel.ofJet (A i) (modelOrder (j i)) 0)
      exact he'.trans (hfailed.le.trans hc)
    have hs := norm_step_ge_of_failed_test (A i) (j i).isLt P.zeta_pos.le P.zeta_le_one
      hκ.le hκ1 hM hμ.le hμ1 hfloor (s i)
      (fun a ha haj => h.tensor_norm_le hL (fun a ha => hlip a ha.le) hi.le
        ha (haj.trans (j i).isLt)) htest
    have hc : 0 ≤ accuracyThreshold q P.zeta κ M μ := by unfold accuracyThreshold; positivity
    have hc1 := accuracyThreshold_le_one (q := q) P.zeta_pos.le P.zeta_le_one
      hκ.le hκ1 hM hμ.le hμ1
    have hr := requests_of_norm_floor hc hc1 P.requestFactor_pos.le hsecond
      (accuracy i) haccuracy (s i) hs a ha haq
    exact (not_lt_of_ge hr) hbad

end Run
end InexactTrustRegion
