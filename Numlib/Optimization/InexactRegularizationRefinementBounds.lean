import Numlib.Optimization.FiniteIncrementCounts
import Numlib.Optimization.TaylorGapLowOrderScaling
import Numlib.Optimization.InexactRegularizationRadii
import Numlib.Optimization.InexactRegularizationRequestRatios
import Mathlib.Tactic

/-!
# Refinement bounds before true point quality

The literal checked-q execution has no accuracy-only transition below a fixed polynomial
request threshold before true point quality. Historical radii and the corrected parameter
bound are derived from actual execution rules. Geometric request contraction then gives
an integer and a logarithmic bound on every actual accuracy-refinement count.
-/

noncomputable section
open scoped Nat
namespace Optimization.InexactRegularization
open InexactTaylorModels HigherOrderApproximateRegularization
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

open Classical in
/-- The source's pointwise true quality: orders at most two use unit radii; higher orders
admit any valid positive radius vector bounded by one. -/
def PointQuality (P : Parameters) (f : E → ℝ) (x : E) : Prop :=
  if P.q ≤ 2 then SatisfiesCriteria P.toParameters f x (fun _ => 1)
  else ∃ δ : ℕ → ℝ, ValidRadii P.toParameters δ ∧ SatisfiesCriteria P.toParameters f x δ

omit [FiniteDimensional ℝ E] in
/-- At low criticality order point quality is exactly the true unit-radius criterion. -/
theorem pointQuality_iff_of_le_two {P : Parameters} {f : E → ℝ} {x : E} (hq : P.q ≤ 2) :
    PointQuality P f x ↔ SatisfiesCriteria P.toParameters f x (fun _ => 1) := by
  simp only [PointQuality, ite_eq_left hq]

omit [FiniteDimensional ℝ E] in
/-- Higher-order point quality has a genuine valid-radius witness. -/
theorem pointQuality_iff_of_two_lt {P : Parameters} {f : E → ℝ} {x : E} (hq : 2 < P.q) :
    PointQuality P f x ↔ ∃ δ : ℕ → ℝ, ValidRadii P.toParameters δ ∧
      SatisfiesCriteria P.toParameters f x δ := by
  simp only [PointQuality, ite_eq_right (by omega : ¬P.q ≤ 2)]

/-- True criteria at valid inspected radii imply point quality. The low-order branch uses
actual linear/quadratic Taylor scaling, rather than a unit-radius state invariant. -/
theorem PointQuality.of_criteria {P : Parameters} {f : E → ℝ} {x : E} {δ : ℕ → ℝ}
    (hδ : ValidRadii P.toParameters δ) (h : SatisfiesCriteria P.toParameters f x δ) :
    PointQuality P f x := by
  classical
  unfold PointQuality
  split_ifs with hq
  · exact h.unit_of_order_le_two hδ hq
  · exact ⟨δ, hδ, h⟩

/-- Before point quality, the actual criterion fails at every valid radius vector. -/
theorem not_criteria_of_not_pointQuality {P : Parameters} {f : E → ℝ} {x : E}
    (h : ¬PointQuality P f x) {δ : ℕ → ℝ} (hδ : ValidRadii P.toParameters δ) :
    ¬SatisfiesCriteria P.toParameters f x δ := fun ht => h (PointQuality.of_criteria hδ ht)

/-- The common historical radius coefficient from a supplied tensor norm bound and a fixed
regularization bound. Its definition contains no tolerance. -/
def refinementRadiusCoefficient (P : Parameters) (M S : ℝ) : ℝ :=
  P.fraction * P.theta / (24 * max M S)

/-- A tolerance-independent coefficient for the simultaneous inspection and step accuracy
thresholds. The `K+1` denominator handles an exact oracle as well as positive errors. -/
def refinementAccuracyCoefficient (P : Parameters) (M S K : ℝ) : ℝ :=
  min (P.kappaStep * (P.fraction * (refinementRadiusCoefficient P M S) ^ P.q /
    (12 * (P.q ! : ℝ) * max M S)) ^ P.p)
    (P.fraction * (refinementRadiusCoefficient P M S) ^ P.q /
      (4 * (P.q ! : ℝ) * (K + 1)))

/-- A common polynomial accuracy threshold for every supplied derivative order. -/
def refinementThreshold (P : Parameters) (M S K ε : ℝ) : ℝ :=
  refinementAccuracyCoefficient P M S K * ε ^ (P.p * (P.q + 1))

/-- The historical radius coefficient is strictly positive. -/
theorem refinementRadiusCoefficient_pos (P : Parameters) {M S : ℝ} (hM : 1 ≤ M) :
    0 < refinementRadiusCoefficient P M S := by
  unfold refinementRadiusCoefficient
  exact div_pos (mul_pos P.fraction_pos P.theta_pos)
    (mul_pos (by norm_num) (zero_lt_one.trans_le (hM.trans (le_max_left _ _))))

/-- The simultaneous threshold coefficient is fixed and strictly positive. -/
theorem refinementAccuracyCoefficient_pos (P : Parameters) {M S K : ℝ}
    (hM : 1 ≤ M) (hK : 0 ≤ K) : 0 < refinementAccuracyCoefficient P M S K := by
  have hr := refinementRadiusCoefficient_pos P (S := S) hM
  have hs : 0 < max M S := zero_lt_one.trans_le (hM.trans (le_max_left _ _))
  unfold refinementAccuracyCoefficient
  exact lt_min (mul_pos P.kappaStep_pos (pow_pos (div_pos
    (mul_pos P.fraction_pos (pow_pos hr _)) (by positivity)) _))
    (div_pos (mul_pos P.fraction_pos (pow_pos hr _)) (by positivity))

/-- Positive common tolerance gives a positive request threshold. -/
theorem refinementThreshold_pos (P : Parameters) {M S K ε : ℝ}
    (hM : 1 ≤ M) (hK : 0 ≤ K) (hε : 0 < ε) :
    0 < refinementThreshold P M S K ε :=
  mul_pos (refinementAccuracyCoefficient_pos P hM hK) (pow_pos hε _)

/-- The common threshold is no larger than the actual all-order step-check threshold. -/
theorem refinementThreshold_le_step (P : Parameters) {M S K ε : ℝ} (hε : 0 ≤ ε) :
    refinementThreshold P M S K ε ≤
      P.kappaStep * (P.fraction * (P.fraction * P.theta / (24 * max M S)) ^ P.q /
        (12 * (P.q ! : ℝ) * max M S)) ^ P.p * ε ^ (P.p * (P.q + 1)) :=
  mul_le_mul_of_nonneg_right (min_le_left _ _) (pow_nonneg hε _)

/-- The same polynomial threshold pays for the true all-pass gap error at every order. -/
theorem refinementThreshold_inspection_budget (P : Parameters) {M S K ε : ℝ}
    (hM : 1 ≤ M) (hK : 0 ≤ K) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    4 * (P.q ! : ℝ) * K * refinementThreshold P M S K ε ≤
      P.fraction * (P.fraction * P.theta / (24 * max M S)) ^ P.q * ε ^ (P.q + 1) := by
  have hc := refinementAccuracyCoefficient_pos P (S := S) hM hK
  have hden : 0 < 4 * (P.q ! : ℝ) * (K + 1) := by positivity
  have hb : refinementAccuracyCoefficient P M S K ≤
      P.fraction * refinementRadiusCoefficient P M S ^ P.q /
        (4 * (P.q ! : ℝ) * (K + 1)) := min_le_right _ _
  have hb' := (le_div_iff₀ hden).mp hb
  have hbase : 4 * (P.q ! : ℝ) * K * refinementAccuracyCoefficient P M S K ≤
      P.fraction * refinementRadiusCoefficient P M S ^ P.q := by
    nlinarith [mul_nonneg (by positivity : 0 ≤ 4 * (P.q ! : ℝ)) hc.le]
  have hrad := refinementRadiusCoefficient_pos P (S := S) hM
  have hv := P.fraction_pos
  have hp : 1 ≤ P.p := P.order_pos.trans P.order_le
  have hn : P.q + 1 ≤ P.p * (P.q + 1) := by
    simpa using Nat.mul_le_mul_right (P.q + 1) hp
  have hpow := pow_le_pow_of_le_one hε hε1 hn
  unfold refinementThreshold
  calc
    _ = (4 * (P.q ! : ℝ) * K * refinementAccuracyCoefficient P M S K) *
        ε ^ (P.p * (P.q + 1)) := by ring
    _ ≤ (P.fraction * refinementRadiusCoefficient P M S ^ P.q) * ε ^ (P.q + 1) :=
      mul_le_mul hbase hpow (by positivity) (by positivity)
    _ = _ := rfl

/-- At a reachable state before point quality, sufficiently small requests force a trial.
Both actual accuracy-only constructors are excluded using the proved historical radius floor. -/
theorem Execution.trial_of_small_uniform_request {P : Parameters} {f : E → ℝ}
    {oracle : E → (ℕ → ℝ) → Coefficients E} {N : ℕ}
    (r : Execution P P.q f oracle N) {M S K ε : ℝ} (hM : 1 ≤ M) (hK : 0 ≤ K)
    (hε : 0 < ε) (hεj : ∀ j, 1 ≤ j → j ≤ P.q → ε ≤ P.epsilon j)
    (hσ : ∀ k, k ≤ N → (r.state k).sigma ≤ S)
    (hA : ∀ k, k ≤ N → ∀ i ∈ Finset.Icc 1 P.p,
      ‖oracle (r.state k).point (r.state k).request i‖ ≤ M)
    {k : ℕ} (hk : k < N) (hnot : ¬PointQuality P f (r.state k).point)
    (hcoeff : ∀ i ∈ Finset.Icc 1 P.p,
      ‖oracle (r.state k).point (r.state k).request i -
        iteratedFDeriv ℝ i f (r.state k).point‖ ≤ K * (r.state k).request i)
    (hh : ∀ i ∈ Finset.Icc 1 P.p,
      (r.state k).request i ≤ refinementThreshold P M S K ε) : r.trial k = true := by
  have hε1 : ε ≤ 1 := (hεj 1 le_rfl P.order_pos).trans (P.epsilon_lt_one 1 le_rfl P.order_pos).le
  have hs := r.transition k hk
  let rp := r.prefix hk.le
  have hσp : ∀ l, l ≤ k → (rp.state l).sigma ≤ S := fun l hl => hσ l (hl.trans hk.le)
  have hAp : ∀ l, l ≤ k → ∀ i ∈ Finset.Icc 1 P.p,
      ‖oracle (rp.state l).point (rp.state l).request i‖ ≤ M :=
    fun l hl => hA l (hl.trans hk.le)
  generalize hnext : r.state (k + 1) = b at hs
  generalize htrial : r.trial k = trial at hs ⊢
  generalize haccept : r.accepted k = accepted at hs
  cases hs with
  | refineInspection I hall =>
    exfalso
    apply hnot
    apply PointQuality.of_criteria (I.valid_radii (rp.valid_radii le_rfl))
    apply rp.true_quality_of_uniform_accuracy hM hσp hAp I hall hε.le hεj hK
      (refinementThreshold_pos P hM hK hε).le
    · intro i hi
      exact (hcoeff i hi).trans (mul_le_mul_of_nonneg_left (hh i hi) hK)
    · exact refinementThreshold_inspection_budget P hM hK hε.le hε1
  | refineStep I hq s hinaccurate =>
    exfalso
    apply hinaccurate
    apply StepAccurate.of_le _ P.order_le
    apply rp.stepAccurate_of_uniform_request hM hσp hAp I hq s hε.le hεj
    intro i hi
    exact (hh i hi).trans (refinementThreshold_le_step P hε.le)
  | trial => rfl

/-- A fixed finite envelope for every active initial request. It is positive even if inactive
entries or empty ranges are supplied; its definition contains no tolerance. -/
def requestEnvelope (p : ℕ) (h0 : ℕ → ℝ) : ℝ := 1 + ∑ i ∈ Finset.Icc 1 p, |h0 i|

/-- The initial request envelope is at least one. -/
theorem one_le_requestEnvelope (p : ℕ) (h0 : ℕ → ℝ) : 1 ≤ requestEnvelope p h0 := by
  unfold requestEnvelope
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => abs_nonneg _))

/-- The envelope bounds each active initial request. -/
theorem request_le_envelope {p i : ℕ} (h0 : ℕ → ℝ) (hi : i ∈ Finset.Icc 1 p) :
    h0 i ≤ requestEnvelope p h0 := by
  change h0 i ≤ 1 + ∑ j ∈ Finset.Icc 1 p, |h0 j|
  have hs : |h0 i| ≤ ∑ j ∈ Finset.Icc 1 p, |h0 j| :=
    Finset.single_le_sum (f := fun j => |h0 j|) (fun j _ => abs_nonneg (h0 j)) hi
  linarith [le_abs_self (h0 i)]

omit [FiniteDimensional ℝ E] in
/-- The actual refinement count grows by one precisely on accuracy-only transitions. -/
theorem Execution.refinementCount_succ {P : Parameters} {checked : ℕ} {f : E → ℝ}
    {oracle : E → (ℕ → ℝ) → Coefficients E} {N : ℕ}
    (r : Execution P checked f oracle N) (k : ℕ) :
    r.refinementCount (k + 1) = r.refinementCount k + if r.trial k then 0 else 1 := by
  exact Finset.sum_range_succ _ _

/-- The logarithmic refinement slope depends only on the fixed algorithm controls. -/
def refinementLogSlope (P : Parameters) : ℝ :=
  (P.p * (P.q + 1) : ℕ) / (-Real.log P.gammaAccuracy)

/-- The initialization-dependent logarithmic constant is independent of tolerance. -/
def refinementLogConstant (P : Parameters) (h0 : ℕ → ℝ) (c : ℝ) : ℝ :=
  |Real.log (requestEnvelope P.p h0 / c)| / (-Real.log P.gammaAccuracy)

/-- The refinement logarithmic slope is strictly positive. -/
theorem refinementLogSlope_pos (P : Parameters) : 0 < refinementLogSlope P := by
  have hp : 1 ≤ P.p := P.order_pos.trans P.order_le
  have hn : 0 < P.p * (P.q + 1) := Nat.mul_pos (by omega) (by omega)
  exact div_pos (by exact_mod_cast hn)
    (neg_pos.mpr (Real.log_neg P.gammaAccuracy_pos P.gammaAccuracy_lt_one))

/-- The logarithmic initialization term is nonnegative, including exact cancellation. -/
theorem refinementLogConstant_nonneg (P : Parameters) (h0 : ℕ → ℝ) (c : ℝ) :
    0 ≤ refinementLogConstant P h0 c :=
  div_nonneg (abs_nonneg _)
    (neg_pos.mpr (Real.log_neg P.gammaAccuracy_pos P.gammaAccuracy_lt_one)).le

/-- Geometric decay crossing a positive polynomial threshold gives the logarithmic exponent
bound. Absolute logarithms handle every initial scale without a sign side condition. -/
theorem geometric_exponent_lt_log_bound {gamma c ε U : ℝ} {n a : ℕ}
    (hg : 0 < gamma) (hg1 : gamma < 1) (hc : 0 < c) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hU : 0 < U) (h : c * ε ^ n < gamma ^ a * U) :
    (a : ℝ) < (n : ℝ) / (-Real.log gamma) * |Real.log ε| +
      |Real.log (U / c)| / (-Real.log gamma) := by
  have hden : 0 < -Real.log gamma := neg_pos.mpr (Real.log_neg hg hg1)
  have hl := Real.log_lt_log (mul_pos hc (pow_pos hε n)) h
  rw [Real.log_mul hc.ne' (pow_pos hε n).ne', Real.log_pow,
    Real.log_mul (pow_pos hg a).ne' hU.ne', Real.log_pow] at hl
  have hεlog : Real.log ε ≤ 0 := Real.log_nonpos hε.le hε1
  have hr : Real.log U - Real.log c ≤ |Real.log (U / c)| := by
    rw [← Real.log_div hU.ne' hc.ne']
    exact le_abs_self _
  rw [abs_of_nonpos hεlog]
  have he : (n : ℝ) / (-Real.log gamma) * -Real.log ε +
      |Real.log (U / c)| / (-Real.log gamma) =
      (-(n : ℝ) * Real.log ε + |Real.log (U / c)|) / (-Real.log gamma) := by ring
  rw [he]
  apply (lt_div_iff₀ hden).mpr
  nlinarith

/-- Actual refinement counts before first true point quality have an integer geometric
budget and an `E*|log epsilon|+F` bound. The corrected sigma bound and every historical radius
floor are derived here from the actual literal checked-q execution. The only analytic inputs
are a genuine objective Lipschitz bound, global oracle accuracy, and supplied tensor norms. -/
theorem Execution.refinement_count_before_pointQuality {P : Parameters} {f : E → ℝ}
    (O : InexactTrustRegion.Oracle f P.p) {N : ℕ} (r : Execution P P.q f O.derivative N)
    {L K M : ℝ} (hf : HigherOrderRegularization.DiagonalLipschitz f P.p L)
    (hK : 0 ≤ K) (hO : InexactTrustRegion.UniformAccuracy O K) (hM : 1 ≤ M)
    (hA : ∀ k, k ≤ N → ∀ i ∈ Finset.Icc 1 P.p,
      ‖O.derivative (r.state k).point (r.state k).request i‖ ≤ M)
    (hfirst : ∀ k, k < N → ¬PointQuality P f (r.state k).point)
    {ε : ℝ} (hε : 0 < ε) (hεj : ∀ j, 1 ≤ j → j ≤ P.q → ε ≤ P.epsilon j) :
    let S := max (r.state 0).sigma
      (P.gamma3 * ((2 * L + 4 * ((P.p + 1)! : ℝ) *
        effectiveAccuracy P (r.state 0).request * K) / (1 - P.eta2)))
    let c := refinementAccuracyCoefficient P M S K
    let D := refinementLogConstant P (r.state 0).request c
    r.refinementCount N ≤ ⌈refinementLogSlope P * |Real.log ε| + D⌉₊ + 1 ∧
      (r.refinementCount N : ℝ) ≤ refinementLogSlope P * |Real.log ε| + D + 2 := by
  let S := max (r.state 0).sigma
    (P.gamma3 * ((2 * L + 4 * ((P.p + 1)! : ℝ) *
      effectiveAccuracy P (r.state 0).request * K) / (1 - P.eta2)))
  let c := refinementAccuracyCoefficient P M S K
  let U := requestEnvelope P.p (r.state 0).request
  let B := refinementLogSlope P * |Real.log ε| + refinementLogConstant P (r.state 0).request c
  have hc : 0 < c := refinementAccuracyCoefficient_pos P hM hK
  have hU : 0 < U := zero_lt_one.trans_le (one_le_requestEnvelope _ _)
  have hε1 : ε ≤ 1 := (hεj 1 le_rfl P.order_pos).trans
    (P.epsilon_lt_one 1 le_rfl P.order_pos).le
  have hσ : ∀ k, k ≤ N → (r.state k).sigma ≤ S :=
    fun _ hk => r.sigma_upper_of_oracle O P.order_pos hf hK hO hk
  have hforce (k : ℕ) (hk : k < N) (ht : r.trial k = false) :
      c * ε ^ (P.p * (P.q + 1)) < P.gammaAccuracy ^ r.refinementCount k * U := by
    by_contra hn
    have hb := le_of_not_gt hn
    have hh : ∀ i ∈ Finset.Icc 1 P.p,
        (r.state k).request i ≤ refinementThreshold P M S K ε := by
      intro i hi
      rw [r.request_eq hk.le i]
      exact (mul_le_mul_of_nonneg_left (request_le_envelope _ hi)
        (pow_pos P.gammaAccuracy_pos _).le).trans hb
    have ht' := r.trial_of_small_uniform_request hM hK hε hεj hσ hA hk (hfirst k hk)
      (fun i hi => hO _ _ (fun j hj => (r.request_bounds hk.le hj).1) i hi) hh
    simp only [ht, Bool.false_eq_true] at ht'
  have hnat : r.refinementCount N ≤ ⌈B⌉₊ + 1 :=
    nat_count_le_ceil_of_increment_gate (by simp [Execution.refinementCount])
      (fun k _ => by rw [r.refinementCount_succ]; split_ifs <;> omega)
      (fun k hk hinc => by
        have htfalse : r.trial k = false := by
          cases ht : r.trial k with
          | false => rfl
          | true => simp [r.refinementCount_succ, ht] at hinc
        exact geometric_exponent_lt_log_bound P.gammaAccuracy_pos P.gammaAccuracy_lt_one hc
          hε hε1 hU (hforce k hk htfalse))
  have hB : 0 ≤ B := add_nonneg
    (mul_nonneg (refinementLogSlope_pos P).le (abs_nonneg _))
    (refinementLogConstant_nonneg P _ _)
  have hceil : (⌈B⌉₊ : ℝ) < B + 1 := Nat.ceil_lt_add_one hB
  dsimp only
  refine ⟨hnat, ?_⟩
  have hnatr : (r.refinementCount N : ℝ) ≤ (⌈B⌉₊ : ℝ) + 1 := by exact_mod_cast hnat
  linarith

/-- Fixed initial requests and parameter give fixed positive logarithmic constants before
any common tolerance, horizon, or actual execution is chosen. The supplied tensor bound is
an analytic global norm assumption; parameter and historical-radius bounds are derived. -/
theorem refinement_bound_fixed_initialization {P : Parameters} {f : E → ℝ}
    (O : InexactTrustRegion.Oracle f P.p) {L K M : ℝ}
    (hf : HigherOrderRegularization.DiagonalLipschitz f P.p L)
    (hK : 0 ≤ K) (hO : InexactTrustRegion.UniformAccuracy O K) (hM : 1 ≤ M)
    (hA : ∀ (x : E) (h : ℕ → ℝ),
      (∀ i ∈ Finset.Icc 1 P.p, 0 < h i ∧ h i ≤ P.kappaInitial) →
      ∀ i ∈ Finset.Icc 1 P.p, ‖O.derivative x h i‖ ≤ M)
    (h0 : ℕ → ℝ) (sigma0 : ℝ) :
    let S := max sigma0 (P.gamma3 * ((2 * L + 4 * ((P.p + 1)! : ℝ) *
      effectiveAccuracy P h0 * K) / (1 - P.eta2)))
    let c := refinementAccuracyCoefficient P M S K
    let E := refinementLogSlope P
    let F := refinementLogConstant P h0 c + 2
    0 < E ∧ 0 < F ∧
      ∀ ε : ℝ, 0 < ε → (∀ j, 1 ≤ j → j ≤ P.q → ε ≤ P.epsilon j) →
      ∀ N : ℕ, ∀ r : Execution P P.q f O.derivative N,
        (r.state 0).request = h0 → (r.state 0).sigma = sigma0 →
        (∀ k, k < N → ¬PointQuality P f (r.state k).point) →
        r.refinementCount N ≤
          ⌈E * |Real.log ε| + refinementLogConstant P h0 c⌉₊ + 1 ∧
          (r.refinementCount N : ℝ) ≤ E * |Real.log ε| + F := by
  dsimp only
  refine ⟨refinementLogSlope_pos P, add_pos_of_nonneg_of_pos
    (refinementLogConstant_nonneg P h0 _) (by norm_num), ?_⟩
  intro ε hε hεj N r hr hσ hfirst
  have hAr : ∀ k, k ≤ N → ∀ i ∈ Finset.Icc 1 P.p,
      ‖O.derivative (r.state k).point (r.state k).request i‖ ≤ M := by
    intro k hk
    apply hA
    intro i hi
    exact ⟨(r.request_bounds hk hi).1,
      (r.request_bounds hk hi).2.trans (r.initial_request_le i hi)⟩
  have hb := r.refinement_count_before_pointQuality O hf hK hO hM hAr hfirst hε hεj
  simpa only [hr, hσ, add_assoc] using hb

end Optimization.InexactRegularization
