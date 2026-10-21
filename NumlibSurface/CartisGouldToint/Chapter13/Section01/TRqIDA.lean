import Numlib.Optimization.InexactTrustRegionComplexity
import Numlib.Optimization.InexactTrustRegionRates
import Numlib.Optimization.InexactTrustRegionRunningGap
import NumlibSurface.CartisGouldToint.Chapter13.Section01
import NumlibSurface.CartisGouldToint.Chapter12.Section02.TRq
import NumlibSurface.CartisGouldToint.AppendixA.Section08

/-!
# Chapter 13, Section 1: the TRqIDA algorithm

The source algorithm refines accuracy when computed optimality tests pass; it has no certified
stopping rule. Its actual objective evaluations use approximate Taylor decrements as denominators.
The finite-prefix interface records the two forced refinement branches and the rejected-trial
cache return. The analysis counts true quality attainment separately from these computed tests.
-/

noncomputable section
open scoped Nat
open Optimization
namespace CartisGouldToint.Chapter13.Section01
namespace TRqIDA
open InexactTrustRegion HigherOrderTrustRegion
variable {n : ℕ}

/-- The source oracle viewed through the general, analysis-independent accuracy interface. -/
def oracle {f : EuclideanSpace ℝ (Fin n) → ℝ} {q : ℕ}
    (O : ImplicitAccuracyOracle f q) : InexactTrustRegion.Oracle f q :=
  ⟨O.derivative, O.accuracy⟩

/-- Algorithm 13.1.1 with the actual half-threshold witnesses, literal Step 2 accuracy check,
forced geometric refinement, exact function ratios and cached rejected-trial return. Initialization
uses the interval-consistent contraction convention `gamma1 ≤ gamma2 < 1` of (13.1.17). -/
def algorithm (p : Parameters) (a : AccuracyParameters) (q : ℕ) (epsilon : ℕ → ℝ)
    (κh : ℝ) {f : EuclideanSpace ℝ (Fin n) → ℝ} (O : ImplicitAccuracyOracle f q)
    (t : InexactTrustRegion.Trace (EuclideanSpace ℝ (Fin n))) : Prop :=
  1 ≤ q ∧ (∀ j, 1 ≤ j → j ≤ q → 0 < epsilon j ∧ epsilon j ≤ 1) ∧
    Chapter12.Section02.TRq.epsilonMinimum q epsilon ≤ p.theta ∧
    p.theta ≤ t.radius 0 ∧ (∀ i ∈ Finset.Icc 1 q, t.request 0 i ≤ κh) ∧
    InexactTrustRegion.IsRun p a epsilon (oracle O) t

variable {p : Parameters} {a : AccuracyParameters} {q : ℕ} {epsilon : ℕ → ℝ} {κh : ℝ}
  {f : EuclideanSpace ℝ (Fin n) → ℝ} {O : ImplicitAccuracyOracle f q}
  {t : InexactTrustRegion.Trace (EuclideanSpace ℝ (Fin n))}

/-- Every actual finite execution prefix satisfies the operational source transitions. -/
theorem algorithm.prefix (h : algorithm p a q epsilon κh O t) (N : ℕ) :
    LegalPrefix p a epsilon (oracle O) t N := h.2.2.2.2.2 N

/-- The minimum active source tolerance is positive and at most one. -/
theorem algorithm.minimum_bounds (h : algorithm p a q epsilon κh O t) :
    0 < Chapter12.Section02.TRq.epsilonMinimum q epsilon ∧
      Chapter12.Section02.TRq.epsilonMinimum q epsilon ≤ 1 :=
  ⟨Chapter12.Section02.TRq.epsilonMinimum_pos h.1 (fun j hj hjq => (h.2.1 j hj hjq).1),
    (Chapter12.Section02.TRq.epsilonMinimum_le epsilon le_rfl h.1).trans
      (h.2.1 1 le_rfl h.1).2⟩

/-- The source f.D0qL assumption gives a common actual remainder and derivative norm bound.
The zeroth-order Lipschitz hypothesis supplies the first derivative bound as well. -/
theorem exists_uniform_smoothness {f : EuclideanSpace ℝ (Fin n) → ℝ} {q : ℕ}
    (hf : ImplicitSmoothness f q) : ∃ L : ℝ, 1 ≤ L ∧
      (∀ j, 1 ≤ j → j ≤ q → HigherOrderRegularization.DiagonalLipschitz f j L) ∧
      (∀ x i, 1 ≤ i → i ≤ q → ‖iteratedFDeriv ℝ i f x‖ ≤ L) := by
  have hex : ∀ i : ℕ, ∃ Li : ℝ, 1 ≤ Li ∧
      ∀ x y, i ≤ q → ‖iteratedFDeriv ℝ i f x - iteratedFDeriv ℝ i f y‖ ≤ Li * ‖x - y‖ := by
    intro i
    by_cases hi : i ≤ q
    · obtain ⟨Li, hLi, hLip⟩ := hf.lipschitz i hi
      exact ⟨Li, hLi, fun x y _ => hLip x y⟩
    · exact ⟨1, by norm_num, fun _ _ h => (hi h).elim⟩
  choose Li hLi hLip using hex
  let L := ∑ i ∈ Finset.range (q + 1), Li i
  have hmono : ∀ i ≤ q, Li i ≤ L := by
    intro i hi
    exact Finset.single_le_sum (fun j _ => zero_le_one.trans (hLi j))
      (Finset.mem_range.mpr (by omega))
  have hL : 1 ≤ L := (hLi 0).trans (hmono 0 (Nat.zero_le q))
  have hbound : ∀ i ≤ q, ∀ x y,
      ‖iteratedFDeriv ℝ i f x - iteratedFDeriv ℝ i f y‖ ≤ L * ‖x - y‖ := by
    intro i hi x y
    exact (hLip i x y hi).trans (mul_le_mul_of_nonneg_right (hmono i hi) (norm_nonneg _))
  refine ⟨L, hL, ?_, ?_⟩
  · intro j _ hjq
    exact HigherOrderRegularization.DiagonalLipschitz.of_operator
      (hf.contDiff.of_le (by exact_mod_cast hjq)) (zero_le_one.trans hL) (hbound j hjq)
  · intro x i hi hiq
    have his : i - 1 + 1 = i := by omega
    have hdiff : ContDiffOn ℝ ((i - 1 + 1 : ℕ) : WithTop ℕ∞) f Set.univ := by
      rw [his]
      exact (hf.contDiff.of_le (by exact_mod_cast hiq)).contDiffOn
    have ht := (AppendixA.Section08.theorem_A_8_5 (p := i - 1) (L := ⟨L, zero_le_one.trans hL⟩)
      isOpen_univ convex_univ hdiff).mp
      (fun x _ y _ => hbound (i - 1) (by omega) x y) x (Set.mem_univ _)
    change ‖iteratedFDeriv ℝ (i - 1 + 1) f x‖ ≤ L at ht
    rwa [his] at ht

/-- Fixed global smoothness and oracle bounds are chosen before any tolerance vector or run.
All returned tensors at any point obey the bound for every positive request vector below κh. -/
theorem exists_global_analysis_bounds {f : EuclideanSpace ℝ (Fin n) → ℝ} {q : ℕ}
    (O : ImplicitAccuracyOracle f q) (hf : ImplicitSmoothness f q)
    {κh : ℝ} (hκh : 0 < κh) : ∃ L K M : ℝ, 0 < L ∧ 0 ≤ K ∧ 0 < M ∧
      UniformAccuracy (oracle O) K ∧
      (∀ j, 1 ≤ j → j ≤ q → HigherOrderRegularization.DiagonalLipschitz f j L) ∧
      (∀ x h, (∀ i ∈ Finset.Icc 1 q, 0 < h i) →
        (∀ i ∈ Finset.Icc 1 q, h i ≤ κh) →
        ∀ i ∈ Finset.Icc 1 q, ‖O.derivative x h i‖ ≤ M) := by
  obtain ⟨L, hL, hfL, hnorm⟩ := exists_uniform_smoothness hf
  obtain ⟨K, hK, hO⟩ := (oracle O).exists_uniformAccuracy
  refine ⟨L, K, L + K * κh, zero_lt_one.trans_le hL, hK, by positivity, hO, hfL, ?_⟩
  intro x h hh hcap i hi
  have herr := hO x h hh i hi
  change ‖O.derivative x h i - iteratedFDeriv ℝ i f x‖ ≤ K * h i at herr
  have hn := hnorm x i (Finset.mem_Icc.mp hi).1 (Finset.mem_Icc.mp hi).2
  have htri := norm_add_le (O.derivative x h i - iteratedFDeriv ℝ i f x)
    (iteratedFDeriv ℝ i f x)
  rw [sub_add_cancel] at htri
  exact htri.trans (by nlinarith [mul_le_mul_of_nonneg_left (hcap i hi) hK])

/-- Positive requests in a legal run remain below the fixed initialization bound. -/
theorem algorithm.request_le_initial_bound (h : algorithm p a q epsilon κh O t)
    {k i : ℕ} (hi : i ∈ Finset.Icc 1 q) : t.request k i ≤ κh := by
  have hp := h.prefix k
  have hh := hp.request_le_pow h.2.2.2.2.1 le_rfl hi
  have hκh : 0 < κh := (hp.requests_pos (k := 0) (by omega)
    (Finset.mem_Icc.mpr ⟨le_rfl, h.1⟩)).trans_le
    (h.2.2.2.2.1 1 (Finset.mem_Icc.mpr ⟨le_rfl, h.1⟩))
  have hpow : a.contraction ^ (refinements t k).card ≤ 1 :=
    pow_le_one₀ a.contraction_pos.le a.contraction_lt_one.le
  exact hh.trans (mul_le_of_le_one_left hκh.le hpow)

/-- The oracle and f.D0qL bound actual returned tensors uniformly throughout a legal run. -/
theorem algorithm.exists_analysis_bounds (h : algorithm p a q epsilon κh O t)
    (hf : ImplicitSmoothness f q) : ∃ L K M : ℝ, 0 < L ∧ 0 ≤ K ∧ 0 < M ∧
      UniformAccuracy (oracle O) K ∧
      (∀ j, 1 ≤ j → j ≤ q → HigherOrderRegularization.DiagonalLipschitz f j L) ∧
      (∀ k, ∀ i ∈ Finset.Icc 1 q, ‖coefficients (oracle O) t k i‖ ≤ M) := by
  have hκh : 0 < κh := ((h.prefix 0).request_pos 1 (Finset.mem_Icc.mpr ⟨le_rfl, h.1⟩)).trans_le
    (h.2.2.2.2.1 1 (Finset.mem_Icc.mpr ⟨le_rfl, h.1⟩))
  obtain ⟨L, K, M, hL, hK, hM, hO, hfL, hnorm⟩ := exists_global_analysis_bounds O hf hκh
  refine ⟨L, K, M, hL, hK, hM, hO, hfL, ?_⟩
  intro k i hi
  exact hnorm (t.point k) (t.request k) (fun i hi => (h.prefix k).requests_pos le_rfl hi)
    (fun i hi => h.request_le_initial_bound hi) i hi

end TRqIDA

/-- Algorithm 13.1.1, expressed entirely by actual computed transitions and oracle requests. -/
abbrev algorithm_13_1_1 := @TRqIDA.algorithm

namespace TRqIDA
open InexactTrustRegion HigherOrderTrustRegion
variable {n : ℕ}

/-- The finite maximum of the initial actual derivative norms in (13.1.31). -/
def initialDerivativeBound (f : EuclideanSpace ℝ (Fin n) → ℝ) (q : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  if hq : 1 ≤ q then (Finset.Icc 1 q).sup' (by simp [hq])
    (fun i => ‖iteratedFDeriv ℝ i f x‖) else 0

/-- The finite minimum of the initial testing-radius powers in (13.1.31). -/
def initialRadiusPower (q : ℕ) (δ : ℝ) : ℝ :=
  if hq : 1 ≤ q then (Finset.Icc 1 q).inf' (by simp [hq]) (fun j => δ ^ j) else 0

/-- The printed initialization coefficient (13.1.31), with an analysis-only common oracle
multiplier. A zero denominator is interpreted by real division, as elsewhere in the source API. -/
def sourceRadiusCoefficient (p : Parameters) (a : AccuracyParameters) (q : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n))
    (initial δ0 L K κh : ℝ) : ℝ :=
  min 1 (p.gamma1 * (1 - p.eta2) / errorCoefficient q L K a.stepConstant) *
    min p.theta (initial * initialRadiusPower q δ0 /
      (2 * q * (initialDerivativeBound f q x + K * κh)))

/-- The source initialization coefficient is nonnegative and below the sufficient-success
coefficient. No inverse error multiplier or positive initial derivative is required. -/
theorem sourceRadiusCoefficient_bounds {p : Parameters} {a : AccuracyParameters} {q : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    {initial δ0 L K κh : ℝ} (hq : 1 ≤ q) (hi : 0 ≤ initial) (hδ : 0 ≤ δ0)
    (hL : 1 ≤ L) (hK : 0 ≤ K) (hh : 0 ≤ κh) :
    0 ≤ sourceRadiusCoefficient p a q f x initial δ0 L K κh ∧
      sourceRadiusCoefficient p a q f x initial δ0 L K κh ≤ p.gamma1 ∧
      sourceRadiusCoefficient p a q f x initial δ0 L K κh ≤
        p.gamma1 * (1 - p.eta2) / errorCoefficient q L K a.stepConstant := by
  have hks := a.stepConstant_pos
  have hC : 1 ≤ errorCoefficient q L K a.stepConstant := by
    dsimp [errorCoefficient]
    have : 0 ≤ 4 * ((q + 1)! : ℝ) * a.stepConstant * K := by positivity
    linarith
  have hCp : 0 < errorCoefficient q L K a.stepConstant := zero_lt_one.trans_le hC
  have hd : 0 ≤ initialDerivativeBound f q x := by
    rw [initialDerivativeBound, dite_eq_left hq]
    exact (norm_nonneg (iteratedFDeriv ℝ 1 f x)).trans
      (Finset.le_sup' (fun i => ‖iteratedFDeriv ℝ i f x‖) (Finset.mem_Icc.mpr ⟨le_rfl, hq⟩))
  have hr : 0 ≤ initialRadiusPower q δ0 := by
    rw [initialRadiusPower, dite_eq_left hq]
    exact Finset.le_inf' _ _ (fun j _ => pow_nonneg hδ j)
  have hfirst : 0 ≤ min 1 (p.gamma1 * (1 - p.eta2) /
      errorCoefficient q L K a.stepConstant) :=
    le_min (by norm_num) (div_nonneg (mul_nonneg p.gamma1_pos.le
      (sub_nonneg.mpr p.eta2_lt_one.le)) hCp.le)
  have hsecond : 0 ≤ min p.theta (initial * initialRadiusPower q δ0 /
      (2 * q * (initialDerivativeBound f q x + K * κh))) :=
    le_min p.theta_pos.le (div_nonneg (mul_nonneg hi hr) (by positivity))
  have hs1 : min p.theta (initial * initialRadiusPower q δ0 /
      (2 * q * (initialDerivativeBound f q x + K * κh))) ≤ 1 :=
    (min_le_left _ _).trans p.theta_le_one
  have hc : sourceRadiusCoefficient p a q f x initial δ0 L K κh ≤
      p.gamma1 * (1 - p.eta2) / errorCoefficient q L K a.stepConstant :=
    (mul_le_of_le_one_right hfirst hs1).trans (min_le_right _ _)
  have hquot : p.gamma1 * (1 - p.eta2) / errorCoefficient q L K a.stepConstant ≤ p.gamma1 := by
    apply (div_le_iff₀ hCp).mpr
    have heta := p.eta1_pos.trans_le p.eta_le
    nlinarith [mul_le_mul_of_nonneg_left hC p.gamma1_pos.le, mul_pos p.gamma1_pos heta]
  exact ⟨mul_nonneg hfirst hsecond, hc.trans hquot, hc⟩

end TRqIDA

open InexactTrustRegion HigherOrderTrustRegion
variable {n : ℕ} {p : Parameters} {a : AccuracyParameters} {q : ℕ} {epsilon : ℕ → ℝ}
  {κh : ℝ} {f : EuclideanSpace ℝ (Fin n) → ℝ} {O : ImplicitAccuracyOracle f q}
  {t : InexactTrustRegion.Trace (EuclideanSpace ℝ (Fin n))}

/-- Lemma 13.1.1: accuracy-only iterations contribute no radius change and no trial count. -/
theorem lemma_13_1_1 (h : algorithm_13_1_1 p a q epsilon κh O t) (N : ℕ)
    {rmin : ℝ} (hm : 0 < rmin) (hmin : rmin ≤ t.radius N) :
    ((trials t N).card : ℝ) ≤ (successes p (TRqIDA.oracle O) t N).card *
      (1 + Real.log p.gamma3 / |Real.log p.gamma2|) +
        |Real.log (rmin / t.radius 0)| / |Real.log p.gamma2| :=
  (TRqIDA.algorithm.prefix h N).trial_count_le hm hmin

/-- Lemma 13.1.2: the historical minimum of scaled computed gaps and the selected prediction. -/
theorem lemma_13_1_2 (h : algorithm_13_1_1 p a q epsilon κh O t) {k : ℕ}
    (ht : t.branch k = .trial) :
    p.fraction * Chapter12.Section02.TRq.epsilonMinimum q epsilon / 2 ≤
      InexactTrustRegion.runningGap p (TRqIDA.oracle O) t k ∧
    InexactTrustRegion.scaledGap p (TRqIDA.oracle O) t k *
      InexactTrustRegion.testRadius p t k ^ t.order k / ((t.order k)! : ℝ) ≤
        InexactTrustRegion.prediction (TRqIDA.oracle O) t k (t.order k) (t.step k) := by
  have hp := TRqIDA.algorithm.prefix h (k + 1)
  refine ⟨hp.runningGap_lower (fun j hj hjq => Chapter12.Section02.TRq.epsilonMinimum_le
    epsilon hj hjq) (by omega) ⟨k, Finset.mem_filter.mpr ⟨by simp, ht⟩⟩,
    hp.predicted_ge_scaledGap (by omega) (by simp [ht])⟩

/-- Lemma 13.1.3: actual Taylor and tensor errors imply very successful small-radius trials. -/
theorem lemma_13_1_3 (h : algorithm_13_1_1 p a q epsilon κh O t)
    {L K : ℝ} (hL : 0 < L) (hK : 0 ≤ K) (hO : UniformAccuracy (TRqIDA.oracle O) K)
    (hf : ∀ j, 1 ≤ j → j ≤ q → HigherOrderRegularization.DiagonalLipschitz f j L)
    {k : ℕ} (ht : t.branch k = .trial)
    (hr : t.radius k ≤ min p.theta ((1 - p.eta2) *
      InexactTrustRegion.scaledGap p (TRqIDA.oracle O) t k /
        errorCoefficient q L K a.stepConstant)) :
    p.eta2 ≤ InexactTrustRegion.ratio (TRqIDA.oracle O) t k ∧ t.radius k ≤ t.radius (k + 1) := by
  have hp := TRqIDA.algorithm.prefix h (k + 1)
  have hks := a.stepConstant_pos
  have hC : 0 < errorCoefficient q L K a.stepConstant := by
    dsimp [errorCoefficient]; positivity
  have hs := hp.ratio_ge_of_radius (fun j hj hjq => (h.2.1 j hj hjq).1) hK hL.le hO hf
    (by omega) ht (hr.trans (min_le_left _ _))
    (by simpa only [mul_comm] using (le_div_iff₀ hC).mp (hr.trans (min_le_right _ _)))
  exact ⟨hs, hp.radius_nondecrease (by omega) ht hs⟩

/-- Lemma 13.1.4: both historical-radius cases and the uniform testing-radius bound, with
exactly the initialization coefficient (13.1.31) and `κδ = κΔ / 2`. -/
theorem lemma_13_1_4 (h : algorithm_13_1_1 p a q epsilon κh O t)
    {L K : ℝ} (hL : 1 ≤ L) (hK : 0 ≤ K) (hO : UniformAccuracy (TRqIDA.oracle O) K)
    (hf : ∀ j, 1 ≤ j → j ≤ q → HigherOrderRegularization.DiagonalLipschitz f j L) (k : ℕ) :
    let c := TRqIDA.sourceRadiusCoefficient p a q f (t.point 0) (t.radius 0)
      (InexactTrustRegion.testRadius p t 0) L K κh
    ((trials t (k + 1)).Nonempty →
      min (p.gamma1 * p.theta) (c * InexactTrustRegion.runningGap p (TRqIDA.oracle O) t k) ≤
        t.radius k) ∧
    (trials t (k + 1) = ∅ → p.gamma1 * p.theta ≤ t.radius k) ∧
    c * p.fraction * Chapter12.Section02.TRq.epsilonMinimum q epsilon / 2 ≤
      InexactTrustRegion.testRadius p t k := by
  intro c
  let e := Chapter12.Section02.TRq.epsilonMinimum q epsilon
  have hp := TRqIDA.algorithm.prefix h (k + 1)
  have he := TRqIDA.algorithm.minimum_bounds h
  have hepos : 0 < e := he.1
  have hh : 0 ≤ κh := (le_of_lt ((h.prefix 0).request_pos 1
    (Finset.mem_Icc.mpr ⟨le_rfl, h.1⟩))).trans (h.2.2.2.2.1 1
      (Finset.mem_Icc.mpr ⟨le_rfl, h.1⟩))
  have hc := TRqIDA.sourceRadiusCoefficient_bounds (p := p) (a := a) (f := f)
    (x := t.point 0) h.1 hp.initial_pos.le
    (hp.testRadius_bounds (k := 0) (by omega)).1.le hL hK hh
  have hfrac := p.fraction_pos
  have hα : p.fraction * e / 2 ≤ p.theta := by
    have hem : e ≤ p.theta := h.2.2.1
    have hemul := mul_le_mul_of_nonneg_right p.fraction_le_one he.1.le
    nlinarith
  have hb : c * p.fraction * e / 2 ≤ p.gamma1 * p.theta := by
    have hm := mul_le_mul_of_nonneg_left hα hc.1
    have hn := mul_le_mul_of_nonneg_right hc.2.1 p.theta_pos.le
    nlinarith only [hm, hn]
  have hg1 : p.gamma1 * p.theta ≤ p.theta :=
    mul_le_of_le_one_left p.theta_pos.le (p.gamma_le.trans p.gamma2_lt_one.le)
  have hrun : (trials t (k + 1)).Nonempty →
      min (p.gamma1 * p.theta) (c * InexactTrustRegion.runningGap p (TRqIDA.oracle O) t k) ≤
        t.radius k := by
    intro hs
    have hg := hp.runningGap_lower
      (fun j hj hjq => Chapter12.Section02.TRq.epsilonMinimum_le epsilon hj hjq) (by omega) hs
    exact hp.radius_lower_runningGap (fun j hj hjq => (h.2.1 j hj hjq).1) hK
      (zero_lt_one.trans_le hL) hO hf h.2.2.2.1 hc.2.2 (by omega)
      ((by positivity : 0 ≤ p.fraction * e / 2).trans hg)
  have hempty : trials t (k + 1) = ∅ → p.gamma1 * p.theta ≤ t.radius k := by
    intro hs
    have hs' : trials t k = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      have hm := Finset.mem_filter.mp hi
      have hm' : i ∈ trials t (k + 1) := Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (by have := Finset.mem_range.mp hm.1; omega), hm.2⟩
      rw [hs] at hm'
      exact Finset.notMem_empty i hm'
    rw [(TRqIDA.algorithm.prefix h k).radius_eq_initial_of_no_trials hs']
    exact hg1.trans h.2.2.2.1
  refine ⟨hrun, hempty, le_min ?_ (hb.trans hg1)⟩
  by_cases hs : (trials t (k + 1)).Nonempty
  · have hg := hp.runningGap_lower
      (fun j hj hjq => Chapter12.Section02.TRq.epsilonMinimum_le epsilon hj hjq) (by omega) hs
    have hm := mul_le_mul_of_nonneg_left hg hc.1
    exact (le_min hb (by nlinarith only [hm])).trans (hrun hs)
  · exact hb.trans (hempty (Finset.not_nonempty_iff_eq_empty.mp hs))

namespace TRqIDA

/-- The source radius coefficient is nonnegative and no larger than the smallest contraction. -/
theorem algorithm.source_bounds (h : algorithm_13_1_1 p a q epsilon κh O t)
    {L K : ℝ} (hL : 1 ≤ L) (hK : 0 ≤ K) :
    let c := sourceRadiusCoefficient p a q f (t.point 0) (t.radius 0)
      (InexactTrustRegion.testRadius p t 0) L K κh
    0 ≤ c ∧ c ≤ p.gamma1 ∧
      c ≤ p.gamma1 * (1 - p.eta2) / errorCoefficient q L K a.stepConstant := by
  have hp := algorithm.prefix h 0
  apply sourceRadiusCoefficient_bounds h.1 hp.initial_pos.le
    (hp.testRadius_bounds le_rfl).1.le hL hK
  exact (hp.request_pos 1 (Finset.mem_Icc.mpr ⟨le_rfl, h.1⟩)).le.trans
    (h.2.2.2.2.1 1 (Finset.mem_Icc.mpr ⟨le_rfl, h.1⟩))

end TRqIDA

/-- Lemma 13.1.5: the source decrement lower bound and the retained factor one half in the
accepted true-objective decrease. Writing `b = varsigma κδ εmin` exposes (13.1.33). -/
theorem lemma_13_1_5 (h : algorithm_13_1_1 p a q epsilon κh O t)
    {L K : ℝ} (hL : 1 ≤ L) (hK : 0 ≤ K) (hO : UniformAccuracy (TRqIDA.oracle O) K)
    (hf : ∀ j, 1 ≤ j → j ≤ q → HigherOrderRegularization.DiagonalLipschitz f j L)
    {k : ℕ} (ht : t.branch k = .trial) :
    let c := TRqIDA.sourceRadiusCoefficient p a q f (t.point 0) (t.radius 0)
      (InexactTrustRegion.testRadius p t 0) L K κh
    let b := c * p.fraction * Chapter12.Section02.TRq.epsilonMinimum q epsilon / 2
    b ^ (q + 1) / (q ! : ℝ) ≤
      InexactTrustRegion.prediction (TRqIDA.oracle O) t k (t.order k) (t.step k) ∧
    (Successful p (TRqIDA.oracle O) t k → p.eta1 * b ^ (q + 1) / (2 * (q ! : ℝ)) ≤
      f (t.point k) - f (t.point (k + 1))) := by
  intro c b
  have hp := TRqIDA.algorithm.prefix h (k + 1)
  have he := TRqIDA.algorithm.minimum_bounds h
  have hepos := he.1
  have hc := TRqIDA.algorithm.source_bounds h hL hK
  have hcn : 0 ≤ c := hc.1
  have hfrac := p.fraction_pos
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hr := (lemma_13_1_4 h hL hK hO hf k).2.2
  have hb1 : b ≤ 1 := hr.trans (hp.testRadius_bounds (k := k) (by omega)).2
  have hc1 : c ≤ 1 := hc.2.1.trans (p.gamma_le.trans p.gamma2_lt_one.le)
  have hg := hp.scaledGap_lower
    (fun j hj hjq => Chapter12.Section02.TRq.epsilonMinimum_le epsilon hj hjq)
    (k := k) (by omega) (by simp [ht])
  have hα : b ≤ p.fraction * Chapter12.Section02.TRq.epsilonMinimum q epsilon / 2 := by
    have hm := mul_le_mul_of_nonneg_right hc1
      (mul_nonneg hfrac.le he.1.le)
    dsimp [b]
    nlinarith only [hm]
  have hd := hp.predicted_lower_of_radius hb hb1 (by omega) (by simp [ht]) hr (hα.trans hg.le)
  refine ⟨hd, ?_⟩
  intro hs
  have ha := hp.accepted_decrease (fun j hj hjq => (h.2.1 j hj hjq).1) (by omega) hs
  have hm := mul_le_mul_of_nonneg_left hd p.eta1_pos.le
  have heq : p.eta1 * b ^ (q + 1) / (2 * (q ! : ℝ)) =
      (p.eta1 * (b ^ (q + 1) / (q ! : ℝ))) / 2 := by ring
  rw [heq]
  apply (half_le_self (mul_nonneg p.eta1_pos.le
    (div_nonneg (pow_nonneg hb _) (by positivity)))).trans
  exact hm.trans ha

/-- Lemma 13.1.6: the explicit Step 2 accuracy threshold excludes refinement. The displayed
step floor equals `varsigma^(q+1) κδ^q εmin^(q+1)/(4 q! M)` with `κδ = κΔ/2`. -/
theorem lemma_13_1_6 (h : algorithm_13_1_1 p a q epsilon κh O t)
    {L K M : ℝ} (hL : 1 ≤ L) (hK : 0 ≤ K) (hM : 1 ≤ M)
    (hO : UniformAccuracy (TRqIDA.oracle O) K)
    (hf : ∀ j, 1 ≤ j → j ≤ q → HigherOrderRegularization.DiagonalLipschitz f j L)
    {k : ℕ} (ht : t.branch k ≠ .testRefinement)
    (hA : ∀ i ∈ Finset.Icc 1 q, ‖coefficients (TRqIDA.oracle O) t k i‖ ≤ M) :
    let c := TRqIDA.sourceRadiusCoefficient p a q f (t.point 0) (t.radius 0)
      (InexactTrustRegion.testRadius p t 0) L K κh
    let e := Chapter12.Section02.TRq.epsilonMinimum q epsilon
    let b := c * p.fraction * e / 2
    let stepFloor := (p.fraction * e / 2 * b ^ q / (q ! : ℝ)) / (2 * M)
    (∀ i ∈ Finset.Icc 1 q, t.request k i ≤ a.stepConstant * stepFloor ^ q) →
      t.branch k = .trial := by
  intro c e b stepFloor hh
  have hp := TRqIDA.algorithm.prefix h (k + 1)
  have he := TRqIDA.algorithm.minimum_bounds h
  have hepos : 0 < e := he.1
  have hc := TRqIDA.algorithm.source_bounds h hL hK
  have hcn : 0 ≤ c := hc.1
  have hfrac := p.fraction_pos
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hr := (lemma_13_1_4 h hL hK hO hf k).2.2
  have hb1 : b ≤ 1 := hr.trans (hp.testRadius_bounds (k := k) (by omega)).2
  have hα : 0 ≤ p.fraction * e / 2 := by positivity
  have hα1 : p.fraction * e / 2 ≤ 1 := by
    nlinarith [mul_le_mul p.fraction_le_one he.2 he.1.le (by norm_num : (0 : ℝ) ≤ 1)]
  have hD : 0 ≤ p.fraction * e / 2 * b ^ q / (q ! : ℝ) := by positivity
  have hD1 : p.fraction * e / 2 * b ^ q / (q ! : ℝ) ≤ 1 := by
    apply (div_le_self (mul_nonneg hα (pow_nonneg hb q))
      (by exact_mod_cast Nat.factorial_pos q)).trans
    exact (mul_le_mul_of_nonneg_left (pow_le_one₀ hb hb1) hα).trans
      (by simpa only [mul_one] using hα1)
  have hs0 : 0 ≤ stepFloor := by dsimp [stepFloor]; positivity
  have hs1 : stepFloor ≤ 1 :=
    (div_le_self hD (by linarith : 1 ≤ 2 * M)).trans hD1
  have hg := (hp.scaledGap_lower
    (fun j hj hjq => Chapter12.Section02.TRq.epsilonMinimum_le epsilon hj hjq)
    (k := k) (by omega) ht).le
  have hd := hp.predicted_lower_two hb hb1 hα (by omega) ht hr hg
  have hs := hp.step_norm_lower (zero_lt_one.trans_le hM) hs1 (by omega) ht hA hd
  exact hp.step_accurate_of_requests hs0 hs1 (by omega) ht hs hh

/-- Lemma 13.1.7: Step 1 refinement attains true optimality once the source absolute-error
threshold holds. The multiplicative form also covers a zero common oracle multiplier. -/
theorem lemma_13_1_7 (h : algorithm_13_1_1 p a q epsilon κh O t)
    {L K H : ℝ} (hL : 1 ≤ L) (hK : 0 ≤ K) (hH : 0 ≤ H)
    (hO : UniformAccuracy (TRqIDA.oracle O) K)
    (hf : ∀ j, 1 ≤ j → j ≤ q → HigherOrderRegularization.DiagonalLipschitz f j L)
    {k : ℕ} (ht : t.branch k = .testRefinement)
    (hh : ∀ i ∈ Finset.Icc 1 q, t.request k i ≤ H) :
    let c := TRqIDA.sourceRadiusCoefficient p a q f (t.point 0) (t.radius 0)
      (InexactTrustRegion.testRadius p t 0) L K κh
    let e := Chapter12.Section02.TRq.epsilonMinimum q epsilon
    let b := c * p.fraction * e / 2
    4 * K * H ≤ p.fraction * e * b ^ q / (q ! : ℝ) →
      Quality (q := q) p epsilon f t k := by
  intro c e b hsmall
  have hp := TRqIDA.algorithm.prefix h (k + 1)
  have he := TRqIDA.algorithm.minimum_bounds h
  have hepos : 0 < e := he.1
  have hc := TRqIDA.algorithm.source_bounds h hL hK
  have hcn : 0 ≤ c := hc.1
  have hfrac := p.fraction_pos
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hr := (lemma_13_1_4 h hL hK hO hf k).2.2
  have hb1 : b ≤ 1 := hr.trans (hp.testRadius_bounds (k := k) (by omega)).2
  apply hp.quality_at_pass hK hH hO (by omega) hh ((hp.test_branch k (by omega)).mp ht)
  intro j hj hjq
  have hbnd := tolerance_monomial_lower he.1.le hb hb1 hr hjq
    (Chapter12.Section02.TRq.epsilonMinimum_le epsilon hj hjq)
  have hm := mul_le_mul_of_nonneg_right p.fraction_le_one
    (div_nonneg (mul_nonneg he.1.le (pow_nonneg hb q)) (by positivity : (0 : ℝ) ≤ (q ! : ℝ)))
  apply hsmall.trans
  apply le_trans _ hbnd
  convert hm using 1 <;> ring

/-- A given legal run attains true quality with the named fixed-data rate coefficients.
The rate functions contain neither its tolerance vector nor its trace. Derivative costs use the
chosen eager full-batch upper envelope for the source's incremental visited-order evaluations. -/
theorem TRqIDA.algorithm.quality_with_fixed_rates
    (h : algorithm_13_1_1 p a q epsilon κh O t) {initial L K M : ℝ}
    (hinit : t.radius 0 = initial) (hL : 0 < L) (hK : 0 ≤ K) (hM : 0 < M)
    (hO : UniformAccuracy (TRqIDA.oracle O) K)
    (hfL : ∀ j, 1 ≤ j → j ≤ q → HigherOrderRegularization.DiagonalLipschitz f j L)
    (hA : ∀ k, ∀ i ∈ Finset.Icc 1 q, ‖coefficients (TRqIDA.oracle O) t k i‖ ≤ M)
    {low : ℝ} (hlow : ∀ x, low ≤ f x) :
    ∃ k : ℕ, Quality (q := q) p epsilon f t k ∧
      (∀ j < k, ¬Quality (q := q) p epsilon f t j) ∧
      (0 < InexactTrustRegion.testRadius p t k ∧ InexactTrustRegion.testRadius p t k ≤ 1) ∧
      ((functionQueries t k).length : ℝ) ≤
        functionRate p a q initial L K * (f (t.point 0) - low) /
            Chapter12.Section02.TRq.epsilonMinimum q epsilon ^ (q + 1) +
          functionLogRate p * |Real.log (Chapter12.Section02.TRq.epsilonMinimum q epsilon)| +
            functionOffsetRate p a q initial L K ∧
      ((derivativeQueries p (TRqIDA.oracle O) t k).length : ℝ) ≤
        successEvaluationRate p a q initial L K * (f (t.point 0) - low) /
            Chapter12.Section02.TRq.epsilonMinimum q epsilon ^ (q + 1) +
          derivativeLogRate a q * |Real.log (Chapter12.Section02.TRq.epsilonMinimum q epsilon)| +
            derivativeOffsetRate p a q initial L K M κh := by
  have hp := TRqIDA.algorithm.prefix h 0
  have he := TRqIDA.algorithm.minimum_bounds h
  let e := Chapter12.Section02.TRq.epsilonMinimum q epsilon
  have hi : 0 < initial := by simpa only [hinit] using hp.initial_pos
  let v := radiusRate p a q initial L K
  have hks := a.stepConstant_pos
  have hfrac := p.fraction_pos
  have heta := p.eta1_pos
  have hC : 0 < errorCoefficient q L K a.stepConstant := by
    dsimp [errorCoefficient]; positivity
  have hc := InexactTrustRegion.radiusCoefficient_pos (p := p) hi hC
  have hv : 0 < v := by dsimp [v, radiusRate]; positivity
  let ca := accuracyRate a q v (p.fraction / 2) M K
  have hca : 0 < ca := accuracyRate_pos hv (by positivity) hM hK
  have hh0 := h.2.2.2.2.1
  have hκh : 0 < κh := (hp.request_pos 1 (Finset.mem_Icc.mpr ⟨le_rfl, h.1⟩)).trans_le
    (hh0 1 (Finset.mem_Icc.mpr ⟨le_rfl, h.1⟩))
  have hthreshold : ca * e ^ (q * (q + 1)) ≤
      analysisThreshold p a q initial L K M e := by
    have ht := accuracyRate_mul_pow_le_threshold (a := a) h.1 hv
      (by positivity : 0 < p.fraction / 2) hM hK he.1 he.2
    convert ht using 1
    simp only [analysisThreshold, radiusFloor, radiusRate, v]
    congr 2 <;> ring
  have hrbudget := refinementBudget_le_log (a := a) hκh hca he.1 hthreshold
  let A := successRate p q v * trialFactor p
  let B := 1 / |Real.log p.gamma2|
  let C := |Real.log (v / initial)| / |Real.log p.gamma2| + 1
  let D := (q * (q + 1) : ℕ) / |Real.log a.contraction| + 1
  let F := |Real.log (κh / ca)| / |Real.log a.contraction| + 2
  obtain ⟨k, _, hq, hfirst, hradius, hfc, hdc⟩ :=
    InexactTrustRegion.IsRun.exists_first_quality h.2.2.2.2.2 he.1 he.2 h.2.2.1
      (fun j hj hjq => Chapter12.Section02.TRq.epsilonMinimum_le epsilon hj hjq)
      hK hL hM hO hfL hA hh0 hlow
  rw [hinit] at hfc hdc
  refine ⟨k, hq, hfirst, hradius, ?_, ?_⟩
  · change ((functionQueries t k).length : ℝ) ≤
      A * (f (t.point 0) - low) / e ^ (q + 1) + B * |Real.log e| + C
    have ht := trialBudget_le_rate hi hv he.1
      (gap := f (t.point 0) - low)
    have hh := hfc.trans (add_le_add ht le_rfl)
    convert hh using 1
    dsimp [A, B, C, v, e]
    ring
  · change ((derivativeQueries p (TRqIDA.oracle O) t k).length : ℝ) ≤
      successRate p q v * (f (t.point 0) - low) / e ^ (q + 1) + D * |Real.log e| + F
    rw [successBudget_eq hv he.1] at hdc
    have hlog : 0 ≤ |Real.log e| := abs_nonneg _
    have hh := add_le_add (le_refl
      (successRate p q v * (f (t.point 0) - low) / e ^ (q + 1))) hrbudget
    have hfinal := hdc.trans (add_le_add hh le_rfl)
    dsimp [D, F]
    have heq : (|Real.log (κh / ca)| + (q * (q + 1) : ℕ) * |Real.log e|) /
        |Real.log a.contraction| + 1 + 1 =
      (q * (q + 1) : ℕ) / |Real.log a.contraction| * |Real.log e| +
        (|Real.log (κh / ca)| / |Real.log a.contraction| + 2) := by ring
    rw [add_assoc, heq] at hfinal
    dsimp [e] at hlog
    nlinarith only [hfinal, hlog]


/-- Theorem 13.1.8 in uniform quantifier order: fixed positive evaluation-rate constants are
chosen from global f.D0qL/oracle bounds BEFORE every tolerance vector and every legal run with
the specified initial radius and request cap. Initial points may vary because the analytic bounds
are global. Nonpositive request caps admit no legal run and are covered vacuously. True quality
is attained; the eager derivative-batch count bounds incremental source
work and is not a literal per-positive-order query count or an observable stopping certificate. -/
theorem theorem_13_1_8 (p : Parameters) (a : AccuracyParameters) (q : ℕ)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (O : ImplicitAccuracyOracle f q)
    (hf : ImplicitSmoothness f q) {initial κh low : ℝ}
    (hi : 0 < initial) (hlow : ∀ x, low ≤ f x) :
    ∃ A B C S D F : ℝ, 0 < A ∧ 0 < B ∧ 0 < C ∧ 0 < S ∧ 0 < D ∧ 0 < F ∧
      ∀ (epsilon : ℕ → ℝ) (t : InexactTrustRegion.Trace (EuclideanSpace ℝ (Fin n))),
        t.radius 0 = initial → algorithm_13_1_1 p a q epsilon κh O t →
          ∃ k : ℕ, Quality (q := q) p epsilon f t k ∧
            (∀ j < k, ¬Quality (q := q) p epsilon f t j) ∧
            (0 < InexactTrustRegion.testRadius p t k ∧ InexactTrustRegion.testRadius p t k ≤ 1) ∧
            ((functionQueries t k).length : ℝ) ≤
              A * (f (t.point 0) - low) /
                  Chapter12.Section02.TRq.epsilonMinimum q epsilon ^ (q + 1) +
                B * |Real.log (Chapter12.Section02.TRq.epsilonMinimum q epsilon)| + C ∧
            ((derivativeQueries p (TRqIDA.oracle O) t k).length : ℝ) ≤
              S * (f (t.point 0) - low) /
                  Chapter12.Section02.TRq.epsilonMinimum q epsilon ^ (q + 1) +
                D * |Real.log (Chapter12.Section02.TRq.epsilonMinimum q epsilon)| + F := by
  by_cases hκh : 0 < κh
  · obtain ⟨L, K, M, hL, hK, hM, hO, hfL, hnorm⟩ :=
      TRqIDA.exists_global_analysis_bounds O hf hκh
    obtain ⟨hA, hB, hC, hS, hD, hF⟩ :=
      evaluationRates_pos (p := p) (a := a) (q := q) (M := M) (H0 := κh) hi hL hK
    refine ⟨functionRate p a q initial L K, functionLogRate p,
      functionOffsetRate p a q initial L K, successEvaluationRate p a q initial L K,
      derivativeLogRate a q, derivativeOffsetRate p a q initial L K M κh,
      hA, hB, hC, hS, hD, hF, ?_⟩
    intro epsilon t hinit h
    apply TRqIDA.algorithm.quality_with_fixed_rates h hinit hL hK hM hO hfL _ hlow
    intro k i hi
    exact hnorm (t.point k) (t.request k) (fun i hi => (h.prefix k).requests_pos le_rfl hi)
      (fun i hi => h.request_le_initial_bound hi) i hi
  · refine ⟨1, 1, 1, 1, 1, 1, by norm_num, by norm_num, by norm_num,
      by norm_num, by norm_num, by norm_num, ?_⟩
    intro epsilon t _ h
    have hpos := (h.prefix 0).request_pos 1 (Finset.mem_Icc.mpr ⟨le_rfl, h.1⟩)
    have hcap := h.2.2.2.2.1 1 (Finset.mem_Icc.mpr ⟨le_rfl, h.1⟩)
    exact (hκh (hpos.trans_le hcap)).elim

end CartisGouldToint.Chapter13.Section01
