import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Numlib.Optimization.ModelBased.SupportDescent
import Numlib.Optimization.Optimality.Clarke

/-!
# Steepest descent for a nonsmooth objective

[conn2000trust], Section 11.1. The steepest-descent calculation follows from the
Clarke support representation (3.1.4) and metric projection.
-/

open Filter Metric ConvexAnalysis Optimization
open scoped Topology RealInnerProductSpace

namespace ConnGouldToint.Chapter11

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The model-value agreement condition (11.1.1). -/
def modelValueMatches {P : Type*} (f : E → ℝ) (m : E → P → E → ℝ) : Prop :=
  ∀ x p, m x p 0 = f x

/-- The model-directional derivative agreement condition (11.1.2). -/
def modelDerivativeMatches {P : Type*} (f : E → ℝ) (m : E → P → E → ℝ) : Prop :=
  ∀ x p d, d ≠ 0 → clarkeDerivative (m x p) 0 d = clarkeDerivative f x d

/-- The minimizing property in (11.1.3) of a steepest-descent direction. -/
def IsSteepestDirection (f : E → ℝ) (x d : E) : Prop :=
  ‖d‖ ≤ 1 ∧ IsMinOn (clarkeDerivative f x) (closedBall 0 1) d

/-- The least slope over the closed unit ball. -/
noncomputable def steepestSlope (f : E → ℝ) (x : E) : ℝ :=
  sInf (clarkeDerivative f x '' closedBall 0 1)

/-- The minimum-norm subgradient (11.1.4), as the projection of zero. -/
noncomputable def minimumNormSubgradient (f : E → ℝ) (x : E) : E :=
  bestApprox (clarkeSubgradient f x) 0

/-- The selected steepest-descent direction (11.1.6). It is zero when the minimum-norm
subgradient is zero. -/
noncomputable def steepestDirection (f : E → ℝ) (x : E) : E :=
  negativeUnit (minimumNormSubgradient f x)

variable [CompleteSpace E]

/-- Lemma 11.1.1 and formula (11.1.6), using the support representation (3.1.4).
The selected direction attains the least slope, equal to minus the norm of the
minimum-norm Clarke subgradient. -/
theorem lemma_11_1_1 {f : E → ℝ} {x : E} {U : Set E} {L : NNReal}
    (hU : U ∈ 𝓝 x) (hL : LipschitzOnWith L f U) :
    (minimumNormSubgradient f x ∈ clarkeSubgradient f x ∧
      ∀ z ∈ clarkeSubgradient f x, ‖minimumNormSubgradient f x‖ ≤ ‖z‖) ∧
    IsSteepestDirection f x (steepestDirection f x) ∧
    clarkeDerivative f x (steepestDirection f x) = steepestSlope f x ∧
    steepestSlope f x = -‖minimumNormSubgradient f x‖ := by
  have h := hasClarkeSupport_of_lipschitzOnWith hU hL
  let K := clarkeSubgradient f x
  have hcl := isClosed_clarkeSubgradient f x
  have hco := convex_clarkeSubgradient f x
  have hg := isBestApprox_bestApprox_of_isClosed h.nonempty hcl hco (0 : E)
  have hval := supportFn_negativeUnit_bestApprox h.nonempty hcl hco
  change supportFn (innerₗ E) K (steepestDirection f x) =
    ((-‖minimumNormSubgradient f x‖ : ℝ) : EReal) at hval
  rw [h] at hval
  have hval' := EReal.coe_eq_coe_iff.mp hval
  have hlo (d : E) (hd : ‖d‖ ≤ 1) :
      -‖minimumNormSubgradient f x‖ ≤ clarkeDerivative f x d := by
    have hh := neg_norm_bestApprox_le_supportFn h.nonempty hcl hco hd
    rw [h] at hh
    exact EReal.coe_le_coe_iff.mp hh
  have hdir : ‖steepestDirection f x‖ ≤ 1 := norm_negativeUnit_le_one _
  have hleast : IsLeast (clarkeDerivative f x '' closedBall 0 1)
      (-‖minimumNormSubgradient f x‖) := by
    refine ⟨⟨steepestDirection f x, mem_closedBall_zero_iff.mpr hdir, hval'⟩, ?_⟩
    rintro _ ⟨d, hd, rfl⟩
    exact hlo d (mem_closedBall_zero_iff.mp hd)
  have hslope : steepestSlope f x = -‖minimumNormSubgradient f x‖ := hleast.csInf_eq
  refine ⟨⟨hg.1, fun z hz ↦ ?_⟩, ⟨hdir, isMinOn_iff.mpr fun d hd ↦ ?_⟩,
    hval'.trans hslope.symm, hslope⟩
  · simpa [minimumNormSubgradient] using hg.2 z hz
  · exact hval'.le.trans (hlo d (mem_closedBall_zero_iff.mp hd))

/-- The least slope vanishes exactly at Clarke stationary points. -/
theorem steepestSlope_eq_zero_iff {f : E → ℝ} {x : E} {U : Set E} {L : NNReal}
    (hU : U ∈ 𝓝 x) (hL : LipschitzOnWith L f U) :
    steepestSlope f x = 0 ↔ (0 : E) ∈ clarkeSubgradient f x := by
  have h := hasClarkeSupport_of_lipschitzOnWith hU hL
  rw [(lemma_11_1_1 hU hL).2.2.2, neg_eq_zero, norm_eq_zero]
  constructor
  · intro hg
    exact hg ▸ (lemma_11_1_1 hU hL).1.1
  · intro hzero
    apply (bestApprox_eq_iff h.nonempty (isClosed_clarkeSubgradient f x)
      (convex_clarkeSubgradient f x)).mpr
    exact ⟨hzero, by simp⟩

/-- The minimizing property of a model step for (11.1.7). -/
def IsModelMinimizer (m : E → ℝ) (Δ : ℝ) (s : E) : Prop :=
  ‖s‖ ≤ Δ ∧ IsMinOn m (closedBall 0 Δ) s

omit [CompleteSpace E] in
/-- The minimizing property of a Cauchy step length along the selected direction
in (11.1.8). -/
def IsCauchyLength (m : E → ℝ) (d : E) (Δ t : ℝ) : Prop :=
  t ∈ Set.Ioc 0 Δ ∧ IsMinOn (fun u : ℝ ↦ m (u • d)) (Set.Ioc 0 Δ) t

/-- The Cauchy step in (11.1.8) given its length and direction. -/
def cauchyStep (t : ℝ) (d : E) : E := t • d

/-- Sufficient model decrease relative to a Cauchy step, as in (11.1.9). -/
def HasSufficientCauchyDecrease (m : E → ℝ) (s sC : E) (Δ κ : ℝ) : Prop :=
  ‖s‖ ≤ Δ ∧ κ * (m 0 - m sC) ≤ m 0 - m s

/-- Lemma 11.1.2. Away from Clarke stationarity, the norm of the minimum-norm
subgradient is bounded below on a neighborhood. Use one fixed strict descent
direction and upper semicontinuity of its Clarke derivative. -/
theorem lemma_11_1_2 {f : E → ℝ} {x : E} {U : Set E} {L : NNReal}
    (hU : U ∈ 𝓝 x) (hL : LipschitzOnWith L f U)
    (hx : (0 : E) ∉ clarkeSubgradient f x) :
    ∃ ε κ : ℝ, 0 < ε ∧ 0 < κ ∧ ∀ y ∈ ball x ε, κ ≤ ‖minimumNormSubgradient f y‖ := by
  have h := lemma_11_1_1 hU hL
  let d := steepestDirection f x
  let κ := ‖minimumNormSubgradient f x‖ / 2
  have hg : minimumNormSubgradient f x ≠ 0 := fun he ↦ hx (he ▸ h.1.1)
  have hκ : 0 < κ := half_pos (norm_pos_iff.mpr hg)
  have hstrict : clarkeDerivative f x d < -κ := by
    change clarkeDerivative f x (steepestDirection f x) < -κ
    rw [h.2.2.1, h.2.2.2]
    dsimp [κ]
    linarith [norm_pos_iff.mpr hg]
  obtain ⟨V, hVU, hV, hxV⟩ := _root_.mem_nhds_iff.mp
    ((eventually_clarkeDerivative_le_of_lt hU hL hstrict).and hU)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hxV)
  refine ⟨ε, κ, hε, hκ, fun y hy ↦ ?_⟩
  have hyV := hball hy
  have hUy : U ∈ 𝓝 y := Filter.mem_of_superset (hV.mem_nhds hyV) fun z hz ↦ (hVU hz).2
  have hyL := lemma_11_1_1 hUy hL
  have hySlope := isMinOn_iff.mp hyL.2.1.2 d (mem_closedBall_zero_iff.mpr h.2.1.1)
  rw [hyL.2.2.1, hyL.2.2.2] at hySlope
  linarith [(hVU hyV).1]

/-- A uniform one-sided first-order expansion of the model around zero, over
nearby base points, admissible parameters, and unit-ball directions. -/
def UniformModelUpperApproximationAt {P : Type*} (m : E → P → E → ℝ) (x : E) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ ε δ : ℝ, 0 < ε ∧ 0 < δ ∧
    ∀ y ∈ ball x ε, ∀ (p : P) (d : E), ‖d‖ ≤ 1 → ∀ t ∈ Set.Ioc 0 δ,
      m y p (t • d) - m y p 0 ≤ t * (clarkeDerivative (m y p) 0 d + η)

/-- Corrected Lemma 11.1.3 near a nonstationary point. The uniform first-order
estimate controls varying parameters and base points. Pointwise regularity
alone only controls a fixed model as the step tends to zero. -/
theorem lemma_11_1_3 {P : Type*} {f : E → ℝ} {m : E → P → E → ℝ}
    {x : E} {U : Set E} {L : NNReal} (hU : U ∈ 𝓝 x) (hL : LipschitzOnWith L f U)
    (hx : (0 : E) ∉ clarkeSubgradient f x) (hm : modelDerivativeMatches f m)
    (happrox : UniformModelUpperApproximationAt m x) :
    ∃ ε δ : ℝ, 0 < ε ∧ 0 < δ ∧ ∀ y ∈ ball x ε, ∀ (p : P) (t : ℝ), 0 ≤ t → t ≤ δ →
      ‖minimumNormSubgradient f y‖ * t / 2 ≤ m y p 0 - m y p (t • steepestDirection f y) := by
  obtain ⟨ε₀, κ, hε₀, hκ, hbound⟩ := lemma_11_1_2 hU hL hx
  obtain ⟨ε₁, δ, hε₁, hδ, happ⟩ := happrox (κ / 2) (half_pos hκ)
  obtain ⟨V, hVU, hV, hxV⟩ := _root_.mem_nhds_iff.mp hU
  obtain ⟨ε₂, hε₂, hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hxV)
  refine ⟨min ε₀ (min ε₁ ε₂), δ, lt_min hε₀ (lt_min hε₁ hε₂), hδ, ?_⟩
  intro y hy p t ht htδ
  rcases ht.eq_or_lt with rfl | ht
  · simp
  have hy₀ := ball_subset_ball (min_le_left ε₀ _) hy
  have hy₁ := ball_subset_ball ((min_le_right ε₀ _).trans (min_le_left ε₁ ε₂)) hy
  have hy₂ := ball_subset_ball ((min_le_right ε₀ _).trans (min_le_right ε₁ ε₂)) hy
  have hUy : U ∈ 𝓝 y := Filter.mem_of_superset (hV.mem_nhds (hball hy₂)) hVU
  have h := lemma_11_1_1 hUy hL
  have hg := hbound y hy₀
  have hdir : steepestDirection f y ≠ 0 := by
    have hn : 0 < ‖minimumNormSubgradient f y‖ := hκ.trans_le hg
    exact smul_ne_zero (neg_ne_zero.mpr (inv_ne_zero hn.ne')) (norm_pos_iff.mp hn)
  have hdecr := happ y hy₁ p _ h.2.1.1 t ⟨ht, htδ⟩
  rw [hm y p _ hdir, h.2.2.1, h.2.2.2] at hdecr
  nlinarith [mul_nonneg ht.le (sub_nonneg.mpr hg)]

omit [CompleteSpace E] in
/-- A continuous model with a strictly decreasing positive trial step attains
its Cauchy minimum at a positive length. -/
theorem exists_cauchyLength_of_strict_decrease {m : E → ℝ} {d : E} {Δ t₀ : ℝ}
    (hm : Continuous m) (ht₀ : t₀ ∈ Set.Ioc 0 Δ) (hdec : m (t₀ • d) < m 0) :
    ∃ t, IsCauchyLength m d Δ t := by
  have ht₀' : t₀ ∈ Set.Icc 0 Δ := ⟨ht₀.1.le, ht₀.2⟩
  have hc : Continuous (fun t : ℝ ↦ m (t • d)) := hm.comp (continuous_id.smul continuous_const)
  obtain ⟨t, ht, hmin⟩ := isCompact_Icc.exists_isMinOn ⟨t₀, ht₀'⟩ hc.continuousOn
  have htpos : 0 < t := by
    by_contra! hn
    have hz := le_antisymm hn ht.1
    have h := isMinOn_iff.mp hmin t₀ ht₀'
    rw [hz, zero_smul] at h
    exact hdec.not_ge h
  refine ⟨t, ⟨htpos, ht.2⟩, isMinOn_iff.mpr fun u hu ↦ ?_⟩
  exact isMinOn_iff.mp hmin u ⟨hu.1.le, hu.2⟩

/-- Corrected Corollary 11.1.4. Compare a minimizing Cauchy length with the
trial length equal to the smaller of the uniform bound and the given radius. -/
theorem corollary_11_1_4 {P : Type*} {f : E → ℝ} {m : E → P → E → ℝ}
    {x : E} {U : Set E} {L : NNReal} (hU : U ∈ 𝓝 x) (hL : LipschitzOnWith L f U)
    (hx : (0 : E) ∉ clarkeSubgradient f x) (hm : modelDerivativeMatches f m)
    (happrox : UniformModelUpperApproximationAt m x) (hcont : ∀ y p, Continuous (m y p))
    {Δ : ℝ} (hΔ : 0 < Δ) :
    ∃ ε δ : ℝ, 0 < ε ∧ 0 < δ ∧ ∀ y ∈ ball x ε, ∀ p : P,
      (∃ t, IsCauchyLength (m y p) (steepestDirection f y) Δ t) ∧
      ∀ t, IsCauchyLength (m y p) (steepestDirection f y) Δ t →
        ‖minimumNormSubgradient f y‖ * min δ Δ / 2 ≤
          m y p 0 - m y p (cauchyStep t (steepestDirection f y)) := by
  obtain ⟨ε, δ, hε, hδ, h⟩ := lemma_11_1_3 hU hL hx hm happrox
  obtain ⟨ε₀, κ, hε₀, hκ, hbound⟩ := lemma_11_1_2 hU hL hx
  refine ⟨min ε ε₀, δ, lt_min hε hε₀, hδ, fun y hy p ↦ ?_⟩
  have hyε := ball_subset_ball (min_le_left ε ε₀) hy
  have hyε₀ := ball_subset_ball (min_le_right ε ε₀) hy
  have hr := lt_min hδ hΔ
  have htrial := h y hyε p (min δ Δ) hr.le (min_le_left _ _)
  have hpos : 0 < ‖minimumNormSubgradient f y‖ * min δ Δ / 2 :=
    half_pos (mul_pos (hκ.trans_le (hbound y hyε₀)) hr)
  refine ⟨exists_cauchyLength_of_strict_decrease (hcont y p) ⟨hr, min_le_right _ _⟩
    (sub_pos.mp (hpos.trans_le htrial)), fun t ht ↦ ?_⟩
  have hmin := isMinOn_iff.mp ht.2 (min δ Δ) ⟨hr, min_le_right _ _⟩
  exact htrial.trans (sub_le_sub_left hmin _)

/-! ### Failure of uniformity for pointwise smooth models -/

/-- A bounded-below smooth objective for the counterexamples. -/
noncomputable def oscillatoryObjective (x : ℝ) : ℝ := x ^ 2 - x

/-- For each positive frequency the model has the correct derivative at zero.
The largest available decrease at base point zero is at most the inverse frequency. -/
noncomputable def oscillatoryModel (x : ℝ) (p : {p : ℝ // 0 < p}) (s : ℝ) : ℝ :=
  oscillatoryObjective x + (2 * x - 1) * (Real.sin (p.val * s) / p.val)

private theorem oscillatoryObjective_strict (x : ℝ) :
    HasStrictDerivAt oscillatoryObjective (2 * x - 1) x := by
  unfold oscillatoryObjective
  convert (hasStrictDerivAt_pow 2 x).sub (hasStrictDerivAt_id x) using 1
  · rfl
  · ring

private theorem oscillatoryModel_strict (x : ℝ) (p : {p : ℝ // 0 < p}) :
    HasStrictDerivAt (oscillatoryModel x p) (2 * x - 1) 0 := by
  have hs := (((hasStrictDerivAt_id (0 : ℝ)).const_mul p.val).sin.div_const p.val)
  have hs' : HasStrictDerivAt (fun s : ℝ ↦ Real.sin (p.val * s) / p.val) 1 0 := by
    simpa [p.prop.ne'] using hs
  change HasStrictDerivAt
    (fun s : ℝ ↦ oscillatoryObjective x + (2 * x - 1) * (Real.sin (p.val * s) / p.val))
    (2 * x - 1) 0
  rw [hasStrictDerivAt_const_add_iff]
  simpa only [mul_one] using hs'.const_mul (2 * x - 1)

/-- The family satisfies pointwise smoothness, continuity in the model parameters
at every fixed step, and both model matching conditions. -/
theorem oscillatoryModel_pointwiseSmooth :
    ContDiff ℝ ⊤ oscillatoryObjective ∧ (∀ x, -(1 / 4 : ℝ) ≤ oscillatoryObjective x) ∧
    (∀ x p, ContDiff ℝ ⊤ (oscillatoryModel x p)) ∧
    (∀ s, Continuous (fun xp : ℝ × {p : ℝ // 0 < p} ↦ oscillatoryModel xp.1 xp.2 s)) ∧
    modelValueMatches oscillatoryObjective oscillatoryModel ∧
    modelDerivativeMatches oscillatoryObjective oscillatoryModel := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold oscillatoryObjective
    fun_prop
  · intro x
    unfold oscillatoryObjective
    nlinarith [sq_nonneg (x - 1 / 2)]
  · intro x p
    unfold oscillatoryModel
    fun_prop
  · intro s
    unfold oscillatoryModel oscillatoryObjective
    have hp : Continuous (fun xp : ℝ × {p : ℝ // 0 < p} ↦ xp.2.val) :=
      continuous_subtype_val.comp continuous_snd
    have hs : Continuous (fun xp : ℝ × {p : ℝ // 0 < p} ↦
        Real.sin (xp.2.val * s) / xp.2.val) :=
      (Real.continuous_sin.comp (hp.mul continuous_const)).div hp fun xp ↦ xp.2.prop.ne'
    fun_prop
  · intro x p
    simp [oscillatoryModel]
  · intro x p d _
    rw [clarkeDerivative_eq_of_hasStrictFDerivAt (oscillatoryModel_strict x p).hasStrictFDerivAt,
      clarkeDerivative_eq_of_hasStrictFDerivAt (oscillatoryObjective_strict x).hasStrictFDerivAt]

private theorem oscillatoryObjective_subgradient_zero :
    clarkeSubgradient oscillatoryObjective 0 = {(-1 : ℝ)} := by
  have hf : HasStrictDerivAt oscillatoryObjective (-1) 0 := by
    simpa using oscillatoryObjective_strict 0
  have h (d : ℝ) : clarkeDerivative oscillatoryObjective 0 d = -d := by
    rw [clarkeDerivative_eq_of_hasStrictFDerivAt hf.hasStrictFDerivAt]
    simp
  ext g
  change (∀ d : ℝ, inner ℝ g d ≤ clarkeDerivative oscillatoryObjective 0 d) ↔ g = -1
  simp only [h, RCLike.inner_apply, conj_trivial]
  constructor
  · intro hg
    have hp := hg 1
    have hm := hg (-1)
    linarith
  · rintro rfl d
    linarith

/-- At zero the quadratic example has minimum-norm subgradient `-1`. -/
theorem oscillatoryObjective_minimumNorm :
    minimumNormSubgradient oscillatoryObjective 0 = -1 := by
  unfold minimumNormSubgradient
  rw [oscillatoryObjective_subgradient_zero]
  apply (bestApprox_eq_iff ⟨-1, by simp⟩ isClosed_singleton (convex_singleton _)).mpr
  simp

private theorem oscillatoryObjective_steepest :
    steepestDirection oscillatoryObjective 0 = 1 := by
  simp [steepestDirection, oscillatoryObjective_minimumNorm, negativeUnit]

/-- Counterexample to the literal Lemma 11.1.3. For any proposed step bound there
is a positive step and a frequency for which the model decrease is zero. -/
theorem oscillatoryModel_fails_uniform_decrease {δ : ℝ} (hδ : 0 < δ) :
    ∃ (p : {p : ℝ // 0 < p}) (t : ℝ), 0 < t ∧ t ≤ δ ∧
      oscillatoryModel 0 p 0 - oscillatoryModel 0 p
        (t • steepestDirection oscillatoryObjective 0) <
          ‖minimumNormSubgradient oscillatoryObjective 0‖ * t / 2 := by
  let p : {p : ℝ // 0 < p} := ⟨Real.pi / δ, div_pos Real.pi_pos hδ⟩
  refine ⟨p, δ, hδ, le_rfl, ?_⟩
  have hp : p.val * δ = Real.pi := div_mul_cancel₀ _ hδ.ne'
  simpa [oscillatoryModel, oscillatoryObjective_minimumNorm, oscillatoryObjective_steepest,
    smul_eq_mul, hp] using half_pos hδ

/-- Counterexample to the literal Corollary 11.1.4 at the fixed radius one.
An exact Cauchy step exists but its decrease tends to zero as the frequency grows. -/
theorem oscillatoryModel_fails_cauchy_decrease {δ : ℝ} (hδ : 0 < δ) :
    ∃ (p : {p : ℝ // 0 < p}) (t : ℝ),
      IsCauchyLength (oscillatoryModel 0 p) (steepestDirection oscillatoryObjective 0) 1 t ∧
      oscillatoryModel 0 p 0 - oscillatoryModel 0 p
        (cauchyStep t (steepestDirection oscillatoryObjective 0)) <
          ‖minimumNormSubgradient oscillatoryObjective 0‖ * min δ 1 / 2 := by
  let r := min δ (1 : ℝ)
  have hr : 0 < r := lt_min hδ zero_lt_one
  obtain ⟨a, ha⟩ := exists_gt (max Real.pi (2 / r))
  have haπ : Real.pi < a := (le_max_left _ _).trans_lt ha
  have ha' : 0 < a := Real.pi_pos.trans haπ
  let p : {p : ℝ // 0 < p} := ⟨a, ha'⟩
  let t := (Real.pi / 2) / a
  have ht : 0 < t := div_pos (half_pos Real.pi_pos) ha'
  have hta : a * t = Real.pi / 2 := by
    dsimp [t]
    rw [mul_comm, div_mul_cancel₀ _ ha'.ne']
  have ht₁ : t ≤ 1 := (div_le_one ha').mpr (by linarith [Real.pi_pos])
  refine ⟨p, t, ⟨⟨ht, ht₁⟩, ?_⟩, ?_⟩
  · apply isMinOn_iff.mpr
    intro u _
    have hsin := div_le_div_of_nonneg_right (Real.sin_le_one (a * u)) ha'.le
    simp only [oscillatoryObjective_steepest, smul_eq_mul, mul_one, oscillatoryModel]
    change oscillatoryObjective 0 + (2 * 0 - 1) * (Real.sin (a * t) / a) ≤
      oscillatoryObjective 0 + (2 * 0 - 1) * (Real.sin (a * u) / a)
    rw [hta, Real.sin_pi_div_two]
    linarith
  · have har : 2 / r < a := (le_max_right _ _).trans_lt ha
    have har' := (div_lt_iff₀ hr).mp har
    have hb : 1 / a < r / 2 := (div_lt_iff₀ ha').mpr (by linarith)
    simpa [oscillatoryModel, oscillatoryObjective_minimumNorm, oscillatoryObjective_steepest,
      cauchyStep, smul_eq_mul, p, hta, r] using hb

end ConnGouldToint.Chapter11
