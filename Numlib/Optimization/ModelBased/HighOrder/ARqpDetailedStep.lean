import Numlib.Optimization.ModelBased.HighOrder.ARqp
import Numlib.Optimization.ModelBased.HighOrderStep
import Numlib.Optimization.Optimality.HighOrder

/-!
# The detailed Step 2 of ARqp

Algorithm 12.2.3 of [cartis2022evaluation] computes the step of the high-order adaptive
regularization method ARqp from the regularized model `m = regularizedModel D p σ`
(`T_p(s) + σ ‖s‖^{p+1}/(p+1)!`): it is the instance `J = {j | 3 ≤ j}` (radii halved only at the
orders `j ≥ 3`), without constraints, of the abstract transition system
`Optimization.DetailedStepTrans` of `Numlib.Optimization.ModelBased.HighOrderStep`.

This file proves, for that model:
* `IsDetailedStepOutput.exists_arqpStep`: the outputs are admissible ARqp steps
((12.2.27)–(12.2.29)), with unit radii at the orders `j ≤ 2`;
* `arqpDetailedStep_radius_ge`: the radii stay above `min(1, ς θ ε_j/(8 (3 L + σ)))` ((12.2.45)),
  since a halving only happens while the radius exceeds `ς θ ε_j/(4 (3 L + σ))` (Lemma 12.2.8);
* `arqpDetailedStep_terminates`, `arqpDetailedStep_exists_trans`: in finite dimension every
  execution returns (proof of Lemma 12.2.9), through the halving bound
  (`detailedHalvingBound_regularizedModel`) and the restart gap
  (`detailedRestartGap_regularizedModel`, by compactness at the orders `j ≤ 2`).
-/

open Set Metric
open scoped Nat

namespace Optimization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The Taylor decrements of the model `regularizedModel D p σ` at a trial step. -/
noncomputable abbrev arqpDetailedModelDec (D : FormalMultilinearSeries ℝ E ℝ) (p : ℕ) (σ : ℝ) :
    ℕ → E → E → ℝ :=
  fun j s d => (ftaylorSeries ℝ (regularizedModel D p σ) s).taylorDecrement j d

/-- The transitions of Algorithm 12.2.3 for the model `regularizedModel D p σ`. -/
abbrev ARqpDetailedTrans (D : FormalMultilinearSeries ℝ E ℝ) (p : ℕ) (σ : ℝ) (q : ℕ) (ς θ : ℝ)
    (ε : ℕ → ℝ) : DetailedStepState E → DetailedStepState E → Prop :=
  DetailedStepTrans (regularizedModel D p σ) univ (fun _ => univ) (arqpDetailedModelDec D p σ) q ς θ
    ε {j | 3 ≤ j}

/-- The lower bound on the radius of order `j`: `min(1, ς θ ε_j/(8 (3L + σ)))` at the orders
`j ∈ [3, q]` that may be halved, `1` otherwise. -/
noncomputable def arqpRadiusLB (q : ℕ) (ς θ L σ : ℝ) (ε : ℕ → ℝ) (j : ℕ) : ℝ :=
  if 3 ≤ j ∧ j ≤ q then min 1 (ς * θ * ε j / (8 * (3 * L + σ))) else 1

section

variable {q : ℕ} {ς θ L σ : ℝ} {ε : ℕ → ℝ}

theorem min_le_arqpRadiusLB (j : ℕ) :
    min 1 (ς * θ * ε j / (8 * (3 * L + σ))) ≤ arqpRadiusLB q ς θ L σ ε j := by
  unfold arqpRadiusLB; split_ifs
  · exact le_rfl
  · exact min_le_left _ _

theorem arqpRadiusLB_pos (hσ : 0 < σ) (hL : 0 ≤ L) (hς : 0 < ς) (hθ : 0 < θ)
    (hε : ∀ j ∈ Finset.Icc 1 q, 0 < ε j) (j : ℕ) : 0 < arqpRadiusLB q ς θ L σ ε j := by
  unfold arqpRadiusLB; split_ifs with h
  · have := hε j (Finset.mem_Icc.2 ⟨by omega, h.2⟩)
    exact lt_min one_pos (by positivity)
  · exact one_pos

theorem arqpRadiusLB_le_one (j : ℕ) : arqpRadiusLB q ς θ L σ ε j ≤ 1 := by
  unfold arqpRadiusLB; split_ifs
  · exact min_le_left _ _
  · exact le_rfl

theorem arqpRadiusLB_eq_one {j : ℕ} (hj : j < 3) : arqpRadiusLB q ς θ L σ ε j = 1 := by
  unfold arqpRadiusLB; rw [ite_eq_right (by omega)]

end

section Termination

variable {D : FormalMultilinearSeries ℝ E ℝ} {p q : ℕ} {σ L ς θ : ℝ} {ε : ℕ → ℝ}

/-- A halving at order `j ∈ [1, p]` (Step 2.4.3) only happens when `δ_j` exceeds
`ς θ ε_j/(4 (3L + σ))` (Lemma 12.2.8). -/
private theorem lt_radius_of_halve (hσ : 0 < σ) (hL : 0 ≤ L)
    (hD : ∀ i ∈ Finset.Icc 2 p, ‖D i‖ ≤ L) {j : ℕ} (hj : j ∈ Finset.Icc 1 p) {s d : E}
    (hs : ‖s‖ < 1) {δj : ℝ} (hδ0 : 0 ≤ δj) (hδ1 : δj ≤ 1) (hd : ‖d‖ ≤ δj)
    (hlarge : ς * θ * ε j * δj ^ j / j ! < arqpDetailedModelDec D p σ j s d)
    (hmodel : regularizedModel D p σ s - regularizedModel D p σ (s + d) <
      ς * θ * ε j * δj ^ j / (2 * j !)) :
    ς * θ * ε j / (4 * (3 * L + σ)) < δj := by
  by_contra hle
  push Not at hle
  have hK : 0 < 3 * L + σ := by positivity
  have hδα : 4 * (3 * L + σ) * δj ≤ ς * θ * ε j := by
    rw [le_div_iff₀ (by positivity)] at hle; linarith
  have := sub_regularizedModel_ge_of_taylorDecrement_ge hL hD hσ.le hj hs.le hδ0 hδ1 hδα hd
    hlarge.le
  have e : ς * θ * ε j / 2 * δj ^ j / j ! = ς * θ * ε j * δj ^ j / (2 * j !) := by ring
  linarith

/-- **The halving bound of Algorithm 12.2.3** (proof of Lemma 12.2.9): a halving at order
`j ∈ [3, q]` only happens when `δ_j > ς θ ε_j/(4 (3L + σ)) ≥ 2 lb_j`, with
`lb = arqpRadiusLB` (Lemma 12.2.8). -/
theorem detailedHalvingBound_regularizedModel (hσ : 0 < σ) (hL : 0 ≤ L)
    (hD : ∀ i ∈ Finset.Icc 2 p, ‖D i‖ ≤ L) (hqp : q ≤ p) (hς : 0 < ς) (hθ : 0 < θ)
    (hε : ∀ j ∈ Finset.Icc 1 q, 0 < ε j) :
    DetailedHalvingBound (regularizedModel D p σ) univ (fun _ => univ)
      (arqpDetailedModelDec D p σ) q ς θ ε {j | 3 ≤ j} (arqpRadiusLB q ς θ L σ ε) := by
  intro s δ j d _ hs hj1 hjq hJ hlb hle1 hd hlarge hmodel
  have hlt := lt_radius_of_halve (ς := ς) (θ := θ) (ε := ε) hσ hL hD
    (Finset.mem_Icc.2 ⟨hj1, hjq.trans hqp⟩) hs
    ((arqpRadiusLB_pos hσ hL hς hθ hε j).le.trans hlb) hle1
    (mem_closedBall_zero_iff.1 hd.1) hlarge hmodel
  have h3 : 3 ≤ j := hJ
  have hK : 0 < 3 * L + σ := by positivity
  unfold arqpRadiusLB
  rw [ite_eq_left ⟨h3, hjq⟩]
  have e : ς * θ * ε j / (8 * (3 * L + σ)) = ς * θ * ε j / (4 * (3 * L + σ)) / 2 := by
    field_simp; ring
  have := min_le_right 1 (ς * θ * ε j / (8 * (3 * L + σ)))
  rw [e] at this ⊢
  linarith

/-- **Radii of Algorithm 12.2.3 stay bounded below** ([cartis2022evaluation], (12.2.45), proof
of Lemma 12.2.9). For the model `m = regularizedModel D p σ` with `σ > 0`, `‖D_i‖ ≤ L`
(`i = 2, …, p`, `L ≥ 0`), `1 ≤ q ≤ p`, `ς > 0`, `θ > 0` and `ε_j > 0`, every state reached
by Algorithm 12.2.3 from `μ₀ ∈ (0, 1]` and unit radii has radii
`δ_j ≥ min(1, ς θ ε_j/(8 (3 L + σ)))` for `j ∈ [1, q]` (a halving at order `j` only happens while
`δ_j > ς θ ε_j/(4 (3L + σ))`, Lemma 12.2.8). -/
theorem arqpDetailedStep_radius_ge (hσ : 0 < σ) (hL : 0 ≤ L)
    (hD : ∀ i ∈ Finset.Icc 2 p, ‖D i‖ ≤ L) (hq : 1 ≤ q) (hqp : q ≤ p) (hς : 0 < ς)
    (hθ : 0 < θ) (hε : ∀ j ∈ Finset.Icc 1 q, 0 < ε j) {μ₀ : ℝ}
    (hμ₀ : μ₀ ∈ Ioc (0 : ℝ) 1) {b : DetailedStepState E}
    (h : Relation.ReflTransGen (ARqpDetailedTrans D p σ q ς θ ε) (.findStep μ₀ fun _ => 1) b) :
    ∀ j ∈ Finset.Icc 1 q, min 1 (ς * θ * ε j / (8 * (3 * L + σ))) ≤ b.radii j :=
  fun j _ => (min_le_arqpRadiusLB (q := q) j).trans
    ((DetailedStepState.lb_le_radii hq (fun _ => arqpRadiusLB_le_one _)
      (detailedHalvingBound_regularizedModel hσ hL hD hqp hς hθ hε) hμ₀ h j).1)

/-- The global minimal value `m* = sInf (m '' univ)` of the model is attained. -/
private theorem exists_eq_sInf [FiniteDimensional ℝ E] (hσ : 0 < σ) (hp : 1 ≤ p) :
    ∃ s₀, IsMinOn (regularizedModel D p σ) univ s₀ ∧
      sInf (regularizedModel D p σ '' univ) = regularizedModel D p σ s₀ := by
  obtain ⟨s₀, hmin, -⟩ := exists_isMinOn_regularizedModel (D := D) hσ hp
  exact ⟨s₀, hmin, IsLeast.csInf_eq ⟨⟨s₀, mem_univ _, rfl⟩,
    by rintro _ ⟨t, _, rfl⟩; exact hmin (mem_univ t)⟩⟩

/-- **Gap at low orders** (proof of Lemma 12.2.9): for `j ∈ {1, 2}` and `τ > 0` there is
`η > 0` such that `m(s) - m* ≥ η` whenever `‖s‖ ≤ 1` and `φ^1_{m,j}(s) > τ`: the set of such
`s` lies in a compact set on which `m > m*`, since `φ^1_{m,j}` vanishes at global minimizers
(Theorem 12.1.4). -/
private theorem exists_gap_low [FiniteDimensional ℝ E] (hσ : 0 < σ) (hp : 1 ≤ p) {j : ℕ}
    (hj : j ∈ Finset.Icc 1 2) (hjp : j ≤ p) {τ : ℝ} (hτ : 0 < τ) :
    ∃ η > 0, ∀ s : E, ‖s‖ ≤ 1 →
      τ < taylorMeasure (ftaylorSeries ℝ (regularizedModel D p σ) s) j 1 univ →
      η ≤ regularizedModel D p σ s - sInf (regularizedModel D p σ '' univ) := by
  obtain ⟨s₀, hmin, hinf⟩ := exists_eq_sInf (D := D) hσ hp
  rw [hinf]
  set m := regularizedModel D p σ
  have hmc : ContDiff ℝ p m := contDiff_regularizedModel
  have hφ := Optimization.continuous_taylorMeasure_ftaylorSeries hmc hjp zero_le_one
  set K := closedBall (0 : E) 1 ∩ {s | τ ≤ taylorMeasure (ftaylorSeries ℝ m s) j 1 univ}
  have hK : IsCompact K :=
    (isCompact_closedBall 0 1).inter_right (isClosed_le continuous_const hφ)
  rcases K.eq_empty_or_nonempty with hK0 | hKne
  · refine ⟨1, one_pos, fun s hs hτs => ?_⟩
    have : s ∈ K := ⟨mem_closedBall_zero_iff.2 hs, hτs.le⟩
    rw [hK0] at this
    exact absurd this (notMem_empty s)
  obtain ⟨s₁, hs₁, hmin₁⟩ := hK.exists_isMinOn hKne hmc.continuous.continuousOn
  refine ⟨m s₁ - m s₀, sub_pos.2 (lt_of_le_of_ne (hmin (mem_univ s₁)) fun heq => ?_),
    fun s hs hτs => ?_⟩
  · have hmin' : IsMinOn m univ s₁ := isMinOn_iff.2 fun t _ => by
      rw [← heq]; exact hmin (mem_univ t)
    have h0 := taylorMeasure_eq_zero_of_isLocalMin
      (hmc.contDiffAt.of_le (by exact_mod_cast hjp))
        (hmin'.isLocalMin Filter.univ_mem) hj zero_le_one
    have h1 : τ ≤ taylorMeasure (ftaylorSeries ℝ m s₁) j 1 univ := hs₁.2
    linarith
  · have := isMinOn_iff.1 hmin₁ s ⟨mem_closedBall_zero_iff.2 hs, hτs.le⟩
    linarith

/-- **The restart gap of Algorithm 12.2.3** (proof of Lemma 12.2.9): a restart (Step 2.4.4) at a
short trial step `s` with radii above `arqpRadiusLB` needs `m(s) - m* ≥ η` for some fixed
`η > 0` — at orders `j ≥ 3` because of the model decrease (12.2.37) with radii bounded below, at
orders `j ≤ 2` by compactness (`exists_gap_low`). -/
theorem detailedRestartGap_regularizedModel [FiniteDimensional ℝ E] (hσ : 0 < σ) (hL : 0 ≤ L)
    (hq : 1 ≤ q) (hqp : q ≤ p) (hς : 0 < ς) (hθ : 0 < θ)
    (hε : ∀ j ∈ Finset.Icc 1 q, 0 < ε j) :
    DetailedRestartGap (regularizedModel D p σ) univ (fun _ => univ)
      (arqpDetailedModelDec D p σ) q ς θ ε {j | 3 ≤ j} (arqpRadiusLB q ς θ L σ ε) := by
  have hp : 1 ≤ p := hq.trans hqp
  obtain ⟨s₀, hmin, hinf⟩ := exists_eq_sInf (D := D) hσ hp
  have hlow : ∀ t, sInf (regularizedModel D p σ '' univ) ≤ regularizedModel D p σ t :=
    fun t => hinf ▸ hmin (mem_univ t)
  have hex : ∀ j ∈ Finset.Icc 1 q, ∃ η > 0, ∀ (s : E) (δ : ℕ → ℝ) (d : E), ‖s‖ < 1 →
      (∀ i, arqpRadiusLB q ς θ L σ ε i ≤ δ i ∧ δ i ≤ 1 ∧ (i ∉ {j : ℕ | 3 ≤ j} → δ i = 1)) →
      d ∈ closedBall 0 (δ j) →
      ς * θ * ε j * δ j ^ j / j ! < arqpDetailedModelDec D p σ j s d →
      (j ∉ {j : ℕ | 3 ≤ j} ∨ ς * θ * ε j * δ j ^ j / (2 * j !) ≤
        regularizedModel D p σ s - regularizedModel D p σ (s + d)) →
      η ≤ regularizedModel D p σ s - sInf (regularizedModel D p σ '' univ) := by
    intro j hj
    have hεj := hε j hj
    have hlb := arqpRadiusLB_pos (q := q) hσ hL hς hθ hε j
    by_cases h3 : 3 ≤ j
    · refine ⟨ς * θ * ε j * arqpRadiusLB q ς θ L σ ε j ^ j / (2 * j !), by positivity,
        fun s δ d _ hR _ _ hJ => ?_⟩
      have hdec := hJ.resolve_left (not_not.2 h3)
      have hδ := (hR j).1
      have : ς * θ * ε j * arqpRadiusLB q ς θ L σ ε j ^ j / (2 * j !) ≤
          ς * θ * ε j * δ j ^ j / (2 * j !) := by gcongr
      linarith [hlow (s + d)]
    · have hj2 : j ∈ Finset.Icc 1 2 := Finset.mem_Icc.2 ⟨(Finset.mem_Icc.1 hj).1, by omega⟩
      obtain ⟨η, hη, H⟩ := exists_gap_low (D := D) hσ hp hj2 ((Finset.mem_Icc.1 hj).2.trans hqp)
        (τ := ς * θ * ε j / j !) (by positivity)
      refine ⟨η, hη, fun s δ d hs hR hd hlarge _ => ?_⟩
      have hδ1 : δ j = 1 := (hR j).2.2 h3
      rw [hδ1, one_pow, mul_one] at hlarge
      rw [hδ1] at hd
      refine H s hs.le (hlarge.trans_le ?_)
      exact taylorDecrement_le_taylorMeasure _ j ⟨hd, mem_univ _⟩
  choose! ηf hηf H using hex
  have hne : (Finset.Icc 1 q).Nonempty := ⟨1, Finset.mem_Icc.2 ⟨le_rfl, hq⟩⟩
  refine ⟨(Finset.Icc 1 q).inf' hne ηf, (Finset.lt_inf'_iff _).2 hηf,
    fun s δ j d _ hs hj1 hjq hR hd hlarge hJ => ?_⟩
  have hj : j ∈ Finset.Icc 1 q := Finset.mem_Icc.2 ⟨hj1, hjq⟩
  exact (Finset.inf'_le _ hj).trans (H j hj s δ d hs hR hd.1 hlarge hJ)

/-- **Termination of Algorithm 12.2.3** ([cartis2022evaluation], Lemma 12.2.9). For the model
`m = regularizedModel D p σ` in finite dimension with `σ > 0`, `‖D_i‖ ≤ L` (`i = 2, …, p`,
`L ≥ 0`), `1 ≤ q ≤ p`, `0 < ς`, `θ > 0` and `ε_j > 0` (`j ∈ [1, q]`), there is no infinite
execution of the detailed Step 2 started (Step 2.1) with `μ₀ ∈ (0, 1]` and unit radii (the
abstract `Optimization.detailedStep_terminates` with `detailedHalvingBound_regularizedModel` and
`detailedRestartGap_regularizedModel`). -/
theorem arqpDetailedStep_terminates [FiniteDimensional ℝ E] (hσ : 0 < σ) (hL : 0 ≤ L)
    (hD : ∀ i ∈ Finset.Icc 2 p, ‖D i‖ ≤ L) (hq : 1 ≤ q) (hqp : q ≤ p)
    (hς : 0 < ς) (hθ : 0 < θ) (hε : ∀ j ∈ Finset.Icc 1 q, 0 < ε j) {μ₀ : ℝ}
    (hμ₀ : μ₀ ∈ Ioc (0 : ℝ) 1) :
    ¬ ∃ c : ℕ → DetailedStepState E, c 0 = .findStep μ₀ (fun _ => 1) ∧
      ∀ n, ARqpDetailedTrans D p σ q ς θ ε (c n) (c (n + 1)) := by
  obtain ⟨s₀, hmin, -⟩ := exists_eq_sInf (D := D) hσ (hq.trans hqp)
  exact Optimization.detailedStep_terminates hq (mem_univ 0)
    ⟨_, by rintro _ ⟨t, -, rfl⟩; exact hmin (mem_univ t)⟩
    (fun j => ⟨arqpRadiusLB_pos hσ hL hς hθ hε j, arqpRadiusLB_le_one j⟩)
    (detailedHalvingBound_regularizedModel hσ hL hD hqp hς hθ hε)
    (detailedRestartGap_regularizedModel hσ hL hq hqp hς hθ hε) hμ₀

/-- **Progress of Algorithm 12.2.3** ([cartis2022evaluation], Algorithm 12.2.3 is well defined):
in finite dimension, with `σ > 0`, `1 ≤ p` and `ς ≤ 1`, every non-final state reached from
`μ₀ ∈ (0, 1]` and unit radii has a successor: Step 2.2 can use a global minimizer of the model,
and Step 2.4.1 an exact maximizer of the decrement on the compact ball. -/
theorem arqpDetailedStep_exists_trans [FiniteDimensional ℝ E] (hσ : 0 < σ) (hp : 1 ≤ p)
    (hς1 : ς ≤ 1) {μ₀ : ℝ} (hμ₀ : μ₀ ∈ Ioc (0 : ℝ) 1) {b : DetailedStepState E}
    (h : Relation.ReflTransGen (ARqpDetailedTrans D p σ q ς θ ε) (.findStep μ₀ fun _ => 1) b)
    (hb : ∀ s δ, b ≠ .done s δ) : ∃ b', ARqpDetailedTrans D p σ q ς θ ε b b' := by
  obtain ⟨s₀, hmin, hinf⟩ := exists_eq_sInf (D := D) hσ hp
  refine DetailedStepState.exists_trans (fun μ hμ => ⟨s₀, mem_univ _, ?_⟩)
    (fun s _ j r hr _ => ?_) hμ₀ h hb
  · rw [hinf]
    have : 0 ≤ regularizedModel D p σ 0 - regularizedModel D p σ s₀ :=
      sub_nonneg.2 (hmin (mem_univ 0))
    nlinarith [hμ.2]
  · obtain ⟨d, hd⟩ := exists_isApproxMeasureStep_taylorDecrement
      (ftaylorSeries ℝ (regularizedModel D p σ) s) j isClosed_univ (mem_univ 0) hr.le hς1
    exact ⟨d, hd.1, hd.2⟩

end Termination

/-- **The outputs of Algorithm 12.2.3 are admissible ARqp steps** ([cartis2022evaluation],
(12.2.27)–(12.2.29)): in finite dimension, with `σ > 0` and `p ≥ 1`, every output `(s, δs)` of
the detailed Step 2 for the model `m = regularizedModel D p σ` satisfies the Step-2 conditions of
ARqp (with suitable displacements `d^m_j`), and its radii are `1` at the orders `j ≤ 2`. -/
theorem IsDetailedStepOutput.exists_arqpStep [FiniteDimensional ℝ E] (P : ARqpParams) {p q : ℕ}
    (hp : 1 ≤ p) {ε : ℕ → ℝ} {D : FormalMultilinearSeries ℝ E ℝ} {σ : ℝ} (hσ : 0 < σ) (x : E)
    {s : E} {δs : ℕ → ℝ}
    (h : IsDetailedStepOutput (regularizedModel D p σ) univ (fun _ => univ)
      (arqpDetailedModelDec D p σ) q P.ς P.θ ε {j | 3 ≤ j} s δs) :
    (∃ dm : ℕ → E, ARqpStep univ P q ε (ARqpData.ofTaylor D p σ) x s δs dm) ∧
      ∀ j ≤ 2, δs j = 1 := by
  obtain ⟨smin, hmin, -⟩ := exists_isMinOn_regularizedModel (D := D) (σ := σ) hσ hp
  have hb : BddBelow (regularizedModel D p σ '' univ) :=
    ⟨regularizedModel D p σ smin, by rintro _ ⟨t, -, rfl⟩; exact hmin (mem_univ t)⟩
  obtain ⟨-, -, hrad, hJ, hbranch⟩ := h.spec
  have hU : ∀ y : E, {e : E | y + e ∈ (univ : Set E)} = univ := fun y => by ext; simp
  refine ⟨?_, fun j hj => hJ j fun h3 => by have : 3 ≤ j := h3; omega⟩
  have hdm : ∀ j, ∃ d : E, (j ∈ Finset.Icc 1 q ∧ ¬ 1 ≤ ‖s‖) →
      IsApproxMeasureStep ((ftaylorSeries ℝ (regularizedModel D p σ) s).taylorDecrement j)
        (δs j) univ P.ς d ∧
      (ftaylorSeries ℝ (regularizedModel D p σ) s).taylorDecrement j d ≤
        P.ς * P.θ * ε j * δs j ^ j / j ! := fun j => by
    by_cases hj : j ∈ Finset.Icc 1 q ∧ ¬ 1 ≤ ‖s‖
    · obtain ⟨d, hd, h1, h2⟩ := (hbranch.resolve_left hj.2) j hj.1
      exact ⟨d, fun _ => ⟨⟨hd, h1⟩, h2⟩⟩
    · exact ⟨0, fun h' => absurd h' hj⟩
  choose dm hdm using hdm
  refine ⟨dm, mem_univ _, h.le_of_bddBelow (mem_univ 0) hb, fun heq => ?_,
    fun j _ => (hrad j).1, fun j _ => (hrad j).2, ?_⟩
  · rw [hU]
    exact h.isMinOn_of_eq hb heq
  · by_cases hs : 1 ≤ ‖s‖
    · exact Or.inl hs
    · refine Or.inr fun j hj => ?_
      rw [hU]
      exact hdm j ⟨hj, hs⟩

end Optimization
