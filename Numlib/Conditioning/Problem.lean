import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Numlib.Analysis.Normed.Ring.CondNumber

/-!
# Well-posedness and condition numbers of a problem

The conditioning vocabulary of [quarteroni2000numerical] §2.1. A *problem* is `F x d = 0` with
datum `d : D` and unknown `x : X`; its *resolvent* on a set `S` of admissible data is the map
`G : D → X` giving the unique solution (`Conditioning.IsResolvent`), and the problem is
*well posed* when a continuous resolvent exists (`Conditioning.IsWellPosed`, Hadamard).

The *condition numbers* measure how a perturbation `δd` of the datum is amplified in the
solution. The primitive is `Conditioning.absCondNumberOn G N d : ℝ≥0∞`, the supremum of
`‖G (d + δd) - G d‖ₑ / ‖δd‖ₑ` over the nonzero perturbations `δd` of a set `N` (the
neighbourhood of admissible perturbations of [quarteroni2000numerical] Definition 2.1);
`Conditioning.absCondNumberWithin G S d η` restricts to the admissible perturbations of size
`< η` (`Conditioning.perturbations S d η`), and `Conditioning.absCondNumber G S d` is the limit as
`η → 0⁺`, which by monotonicity is an infimum. The relative numbers `relCondNumberOn`,
`relCondNumberWithin`, `relCondNumber` divide by `‖G d‖ₑ / ‖d‖ₑ` inside the supremum, as the book's
(2.4) does; they are the absolute ones times `‖d‖ₑ / ‖G d‖ₑ`.

Everything is valued in `ℝ≥0∞`: "the condition number is infinite" ([quarteroni2000numerical]
Remark 2.1) is the value `⊤`, the suprema and infima are total, and the Lipschitz condition
(2.3) of the book is exactly finiteness (`Conditioning.absCondNumberWithin_ne_top_iff`).

The main theorem is the first-order formula (2.7): for a resolvent differentiable at `d`,
`Conditioning.absCondNumber G S d = ‖G'‖ₑ` (`absCondNumber_eq_enorm_fderiv`), whose lower bound
`‖G'‖ₑ ≤ absCondNumberWithin G S d η` holds for every radius. Instances: a bounded linear
resolvent has condition number `‖L‖ₑ` over every neighbourhood, which gives the book's Example
2.3 `K(b) ≤ κ(A)` for `A x = b` through `NormedRing.condNumber`; the root of `φ x = d` has
absolute condition number `‖φ'‖ₑ⁻¹` (Example 2.4, the source of §6.1), and a multiple root has
condition number `⊤` (`absCondNumber_eq_top_of_fderiv_eq_zero`, stated within an admissible set so
that one-sided roots are covered).

The finite-dimensional evolution-scheme form of the same vocabulary is
`Numlib/FiniteDifference/LaxEquivalence`; the two are different notions and neither is stated
through the other.
-/

open Asymptotics Filter Topology Set
open scoped ENNReal NNReal

namespace Conditioning

variable {D X Y : Type*}

/-! ### Problems and resolvents -/

section Resolvent

variable [Zero Y]

/-- `G` is the **resolvent** of the problem `F x d = 0` on the admissible data `S`: for every
`d ∈ S`, the solutions of `F x d = 0` are exactly `x = G d` ([quarteroni2000numerical] (2.6)). -/
def IsResolvent (F : X → D → Y) (S : Set D) (G : D → X) : Prop :=
  ∀ d ∈ S, ∀ x, F x d = 0 ↔ x = G d

/-- **Well-posedness** (Hadamard, [quarteroni2000numerical] §2.1): the problem `F x d = 0` has a
unique solution for every admissible datum, depending continuously on it. Continuity, not the
Lipschitz condition (2.3) of the book: a well-posed problem may have infinite condition number
(Remark 2.1 there), and (2.3) is `absCondNumberWithin_ne_top_iff`. -/
def IsWellPosed [TopologicalSpace D] [TopologicalSpace X] (F : X → D → Y) (S : Set D) : Prop :=
  ∃ G, IsResolvent F S G ∧ ContinuousOn G S

variable {F : X → D → Y} {S : Set D} {G : D → X}

/-- A solution of an admissible problem is the value of the resolvent. -/
theorem IsResolvent.eq_of (h : IsResolvent F S G) {d : D} (hd : d ∈ S) {x : X} (hx : F x d = 0) :
    x = G d :=
  (h d hd x).1 hx

/-- The resolvent solves the problem: `F (G d) d = 0` for admissible `d`. -/
theorem IsResolvent.apply (h : IsResolvent F S G) {d : D} (hd : d ∈ S) : F (G d) d = 0 :=
  (h d hd (G d)).2 rfl

/-- A continuous resolvent witnesses well-posedness. -/
theorem IsResolvent.isWellPosed [TopologicalSpace D] [TopologicalSpace X] (h : IsResolvent F S G)
    (hG : ContinuousOn G S) : IsWellPosed F S :=
  ⟨G, h, hG⟩

end Resolvent

/-! ### Condition numbers -/

variable [NormedAddCommGroup D] [NormedAddCommGroup X]

/-- **The absolute condition number over a set of perturbations** `N`: the supremum of the
amplification `‖G (d + δd) - G d‖ₑ / ‖δd‖ₑ` over the nonzero perturbations `δd ∈ N` of the datum
`d` ([quarteroni2000numerical] Definition 2.1, (2.5), with the book's neighbourhood of admissible
perturbations as the parameter `N`). -/
noncomputable def absCondNumberOn (G : D → X) (N : Set D) (d : D) : ℝ≥0∞ :=
  ⨆ (δd : D) (_ : δd ∈ N) (_ : δd ≠ 0), ‖G (d + δd) - G d‖ₑ / ‖δd‖ₑ

/-- The admissible perturbations of size `< η` of the datum `d` inside the admissible set `S`. -/
def perturbations (S : Set D) (d : D) (η : ℝ) : Set D :=
  {δd | ‖δd‖ < η ∧ d + δd ∈ S}

/-- The absolute condition number over the admissible perturbations of size `< η`: the book's
`K_abs(d)` with the neighbourhood `D` of (2.5) the ball of radius `η` intersected with the
admissible data. -/
noncomputable def absCondNumberWithin (G : D → X) (S : Set D) (d : D) (η : ℝ) : ℝ≥0∞ :=
  absCondNumberOn G (perturbations S d η) d

/-- **The first-order absolute condition number**: the limit of `absCondNumberWithin G S d η` as
the size `η` of the admissible perturbations tends to `0⁺` — an infimum, since that quantity is
monotone in `η` (`tendsto_absCondNumberWithin`). This is what the first-order formula (2.7) of
[quarteroni2000numerical] computes, "the limit of the Lipschitz constant of `G` as the
perturbation on the data tends to zero". -/
noncomputable def absCondNumber (G : D → X) (S : Set D) (d : D) : ℝ≥0∞ :=
  ⨅ (η : ℝ) (_ : 0 < η), absCondNumberWithin G S d η

/-- **The relative condition number over a set of perturbations** `N`: the supremum of
`(‖δx‖ / ‖x‖) / (‖δd‖ / ‖d‖)` over the nonzero perturbations `δd ∈ N`, exactly (2.4) of
[quarteroni2000numerical] Definition 2.1. Meaningful for `d ≠ 0` and `G d ≠ 0`; otherwise the
absolute number is the one to use, as the book says. -/
noncomputable def relCondNumberOn (G : D → X) (N : Set D) (d : D) : ℝ≥0∞ :=
  ⨆ (δd : D) (_ : δd ∈ N) (_ : δd ≠ 0), (‖G (d + δd) - G d‖ₑ / ‖G d‖ₑ) / (‖δd‖ₑ / ‖d‖ₑ)

/-- The relative condition number over the admissible perturbations of size `< η`. -/
noncomputable def relCondNumberWithin (G : D → X) (S : Set D) (d : D) (η : ℝ) : ℝ≥0∞ :=
  relCondNumberOn G (perturbations S d η) d

/-- **The first-order relative condition number**, the limit of `relCondNumberWithin G S d η` as
`η → 0⁺`. -/
noncomputable def relCondNumber (G : D → X) (S : Set D) (d : D) : ℝ≥0∞ :=
  ⨅ (η : ℝ) (_ : 0 < η), relCondNumberWithin G S d η

variable {G : D → X} {N S : Set D} {d δd : D}

/-- Every nonzero admissible perturbation's amplification ratio is at most the condition
number. -/
theorem le_absCondNumberOn (hN : δd ∈ N) (h0 : δd ≠ 0) :
    ‖G (d + δd) - G d‖ₑ / ‖δd‖ₑ ≤ absCondNumberOn G N d :=
  le_iSup₂_of_le δd hN (le_iSup_of_le h0 le_rfl)

/-- A bound on every amplification ratio bounds the condition number. -/
theorem absCondNumberOn_le {M : ℝ≥0∞}
    (h : ∀ δd ∈ N, δd ≠ 0 → ‖G (d + δd) - G d‖ₑ / ‖δd‖ₑ ≤ M) : absCondNumberOn G N d ≤ M :=
  iSup₂_le fun δd hN => iSup_le fun h0 => h δd hN h0

/-- The defining inequality of the condition number, in product form:
`‖G (d + δd) - G d‖ₑ ≤ absCondNumberOn G N d * ‖δd‖ₑ` for every admissible perturbation. -/
theorem enorm_sub_le_absCondNumberOn_mul (hN : δd ∈ N) :
    ‖G (d + δd) - G d‖ₑ ≤ absCondNumberOn G N d * ‖δd‖ₑ := by
  by_cases h0 : δd = 0
  · simp [h0]
  · exact (ENNReal.div_le_iff (enorm_ne_zero.2 h0) enorm_ne_top).1 (le_absCondNumberOn hN h0)

/-- A finite bound on the condition number is a Lipschitz bound on the resolvent, in real
numbers. -/
theorem norm_sub_le_of_absCondNumberOn_le {K : ℝ≥0} (hK : absCondNumberOn G N d ≤ K)
    (hN : δd ∈ N) : ‖G (d + δd) - G d‖ ≤ K * ‖δd‖ := by
  have h := (enorm_sub_le_absCondNumberOn_mul hN).trans (mul_le_mul_left hK _)
  rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_coe_nnreal,
    ← ENNReal.ofReal_mul K.coe_nonneg] at h
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h

/-- If `‖G (d + δd) - G d‖ ≤ K * ‖δd‖` for every nonzero `δd ∈ N`, with `0 ≤ K`, then the
condition number over `N` is at most `K`. -/
theorem absCondNumberOn_le_of_forall_norm_sub_le {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ δd ∈ N, δd ≠ 0 → ‖G (d + δd) - G d‖ ≤ K * ‖δd‖) :
    absCondNumberOn G N d ≤ ENNReal.ofReal K := by
  refine absCondNumberOn_le fun δd hN h0 => ?_
  rw [ENNReal.div_le_iff (enorm_ne_zero.2 h0) enorm_ne_top, ← ofReal_norm, ← ofReal_norm,
    ← ENNReal.ofReal_mul hK]
  exact ENNReal.ofReal_le_ofReal (h δd hN h0)

/-- The condition number over `N` is at most `K : ℝ≥0` iff `G` is `K`-Lipschitz along the
perturbations `N` of `d`. -/
theorem absCondNumberOn_le_coe_iff {K : ℝ≥0} :
    absCondNumberOn G N d ≤ K ↔ ∀ δd ∈ N, ‖G (d + δd) - G d‖ ≤ K * ‖δd‖ :=
  ⟨fun hK _ hN => norm_sub_le_of_absCondNumberOn_le hK hN, fun h =>
    ENNReal.ofReal_coe_nnreal ▸
      absCondNumberOn_le_of_forall_norm_sub_le K.coe_nonneg fun δd hN _ => h δd hN⟩

/-- The condition number is monotone in the set of perturbations. -/
theorem absCondNumberOn_mono (G : D → X) (d : D) {N N' : Set D} (h : N ⊆ N') :
    absCondNumberOn G N d ≤ absCondNumberOn G N' d :=
  absCondNumberOn_le fun _ hN h0 => le_absCondNumberOn (h hN) h0

/-- The condition number over the perturbations of size `< η` is monotone in the radius `η`. -/
theorem monotone_absCondNumberWithin (G : D → X) (S : Set D) (d : D) :
    Monotone (absCondNumberWithin G S d) := fun _ _ hη =>
  absCondNumberOn_mono G d fun _ ⟨h1, h2⟩ => ⟨h1.trans_le hη, h2⟩

/-- The first-order condition number is at most the condition number over any positive
radius. -/
theorem absCondNumber_le_absCondNumberWithin (G : D → X) (S : Set D) (d : D) {η : ℝ} (hη : 0 < η) :
    absCondNumber G S d ≤ absCondNumberWithin G S d η :=
  iInf₂_le η hη

/-- The infimum defining `absCondNumber` is the limit of `absCondNumberWithin G S d η` as the
perturbation size `η` tends to `0` from above. -/
theorem tendsto_absCondNumberWithin (G : D → X) (S : Set D) (d : D) :
    Tendsto (absCondNumberWithin G S d) (𝓝[>] 0) (𝓝 (absCondNumber G S d)) := by
  have h := (monotone_absCondNumberWithin G S d).tendsto_nhdsGT 0
  rw [sInf_image] at h
  exact h

/-- **The Lipschitz condition (2.3) of [quarteroni2000numerical] is finiteness of the condition
number**: `G` satisfies `‖δx‖ ≤ K ‖δd‖` for the admissible perturbations of size `< η` iff
`absCondNumberWithin G S d η ≠ ⊤`. -/
theorem absCondNumberWithin_ne_top_iff (G : D → X) (S : Set D) (d : D) (η : ℝ) :
    absCondNumberWithin G S d η ≠ ⊤ ↔
      ∃ K : ℝ, ∀ δd, ‖δd‖ < η → d + δd ∈ S → ‖G (d + δd) - G d‖ ≤ K * ‖δd‖ := by
  constructor
  · intro h
    refine ⟨(absCondNumberWithin G S d η).toNNReal, fun δd h1 h2 => ?_⟩
    exact norm_sub_le_of_absCondNumberOn_le (ENNReal.coe_toNNReal h).ge ⟨h1, h2⟩
  · rintro ⟨K, hK⟩
    refine ne_top_of_le_ne_top ENNReal.coe_ne_top
      ((absCondNumberOn_le_coe_iff (K := K.toNNReal)).2 fun δd hδd => ?_)
    exact (hK δd hδd.1 hδd.2).trans
      (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal K) (norm_nonneg _))

/-- A finite condition number over some radius makes the resolvent continuous at `d` within the
admissible data. -/
theorem continuousWithinAt_of_absCondNumberWithin_ne_top {η : ℝ} (hη : 0 < η)
    (h : absCondNumberWithin G S d η ≠ ⊤) : ContinuousWithinAt G S d := by
  obtain ⟨K, hK⟩ := (absCondNumberWithin_ne_top_iff G S d η).1 h
  refine Metric.continuousWithinAt_iff.2 fun ε hε => ⟨min η (ε / (max K 0 + 1)), by positivity,
    fun y hy hyd => ?_⟩
  have h1 : ‖y - d‖ < η := (dist_eq_norm y d ▸ hyd).trans_le (min_le_left _ _)
  have h2 : ‖y - d‖ ≤ ε / (max K 0 + 1) := (dist_eq_norm y d ▸ hyd).le.trans (min_le_right _ _)
  have h3 := hK (y - d) h1 (by simpa using hy)
  rw [add_sub_cancel] at h3
  rw [dist_eq_norm]
  calc ‖G y - G d‖ ≤ max K 0 * ‖y - d‖ :=
        h3.trans (mul_le_mul_of_nonneg_right (le_max_left K 0) (norm_nonneg _))
    _ ≤ max K 0 * (ε / (max K 0 + 1)) := mul_le_mul_of_nonneg_left h2 (le_max_right K 0)
    _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith [le_max_right K 0]

/-- The relative condition number is the absolute one rescaled by `‖d‖ₑ / ‖G d‖ₑ`. -/
theorem relCondNumberOn_eq (G : D → X) (N : Set D) (d : D) :
    relCondNumberOn G N d = absCondNumberOn G N d * (‖d‖ₑ / ‖G d‖ₑ) := by
  simp only [relCondNumberOn, absCondNumberOn, ENNReal.iSup_mul]
  refine iSup_congr fun δd => iSup_congr fun _ => iSup_congr fun h0 => ?_
  simp only [div_eq_mul_inv]
  rw [ENNReal.mul_inv (Or.inl (enorm_ne_zero.2 h0)) (Or.inl enorm_ne_top), inv_inv]
  ring

/-- For `d ≠ 0` and `G d ≠ 0`, the first-order relative condition number is the absolute one
rescaled by `‖d‖ₑ / ‖G d‖ₑ`. -/
theorem relCondNumber_eq (G : D → X) (S : Set D) {d : D} (hd : d ≠ 0) (hx : G d ≠ 0) :
    relCondNumber G S d = absCondNumber G S d * (‖d‖ₑ / ‖G d‖ₑ) := by
  have h0 : ‖d‖ₑ / ‖G d‖ₑ ≠ 0 := (ENNReal.div_pos (enorm_ne_zero.2 hd) enorm_ne_top).ne'
  have ht : ‖d‖ₑ / ‖G d‖ₑ ≠ ⊤ := (ENNReal.div_lt_top enorm_ne_top (enorm_ne_zero.2 hx)).ne
  simp only [relCondNumber, absCondNumber, relCondNumberWithin, absCondNumberWithin,
    relCondNumberOn_eq, ENNReal.iInf_mul_of_ne h0 ht]

/-! ### The first-order formula -/

section FirstOrder

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 D] [NormedSpace 𝕜 X]

/-- The derivative never exceeds the condition number over any neighbourhood:
`‖G' d‖ₑ ≤ absCondNumberWithin G S d η` whenever `G` is differentiable at the interior point `d`
of `S`. So the first-order number of (2.7) in [quarteroni2000numerical] can underestimate the
true one, as the book's example `G d = cos d - 1` shows. -/
theorem enorm_fderiv_le_absCondNumberWithin {G' : D →L[𝕜] X} (hG : HasFDerivAt G G' d)
    (hS : S ∈ 𝓝 d) {η : ℝ} (hη : 0 < η) : ‖G'‖ₑ ≤ absCondNumberWithin G S d η := by
  by_cases hA : absCondNumberWithin G S d η = ⊤
  · exact hA ▸ le_top
  have hAK : absCondNumberWithin G S d η ≤ (absCondNumberWithin G S d η).toNNReal :=
    (ENNReal.coe_toNNReal hA).ge
  have hlip : ∀ᶠ x in 𝓝 d,
      ‖G x - G d‖ ≤ (absCondNumberWithin G S d η).toNNReal * ‖x - d‖ := by
    filter_upwards [hS, Metric.ball_mem_nhds d hη] with x hxS hxd
    have h := norm_sub_le_of_absCondNumberOn_le hAK (δd := x - d)
      ⟨by simpa [dist_eq_norm] using hxd, by simpa using hxS⟩
    rwa [add_sub_cancel] at h
  calc ‖G'‖ₑ = ENNReal.ofReal ‖G'‖ := (ofReal_norm _).symm
    _ ≤ ENNReal.ofReal ((absCondNumberWithin G S d η).toNNReal : ℝ) :=
        ENNReal.ofReal_le_ofReal (hG.le_of_lip' (NNReal.coe_nonneg _) hlip)
    _ = absCondNumberWithin G S d η := by rw [ENNReal.ofReal_coe_nnreal, ENNReal.coe_toNNReal hA]

/-- **The first-order formula (2.7) of [quarteroni2000numerical], absolute form**: the
first-order absolute condition number of a resolvent differentiable at the interior point `d` of
the admissible data is the norm of its derivative, `absCondNumber G S d = ‖G'‖ₑ`. -/
theorem absCondNumber_eq_enorm_fderiv {G' : D →L[𝕜] X} (hG : HasFDerivAt G G' d)
    (hS : S ∈ 𝓝 d) : absCondNumber G S d = ‖G'‖ₑ := by
  refine le_antisymm ?_ (le_iInf₂ fun η hη => enorm_fderiv_le_absCondNumberWithin hG hS hη)
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hlo := isLittleO_iff.1 (hasFDerivAt_iff_isLittleO_nhds_zero.1 hG) (NNReal.coe_pos.2 hε)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hlo
  calc absCondNumber G S d ≤ absCondNumberWithin G S d δ :=
        absCondNumber_le_absCondNumberWithin G S d hδ
    _ ≤ ENNReal.ofReal (‖G'‖ + ε) := by
        refine absCondNumberOn_le_of_forall_norm_sub_le (by positivity) fun δd hδd _ => ?_
        have h1 := hball (y := δd) (by simpa [dist_eq_norm] using hδd.1)
        calc ‖G (d + δd) - G d‖ = ‖G' δd + (G (d + δd) - G d - G' δd)‖ := by congr 1; abel
          _ ≤ ‖G' δd‖ + ‖G (d + δd) - G d - G' δd‖ := norm_add_le _ _
          _ ≤ ‖G'‖ * ‖δd‖ + ε * ‖δd‖ := add_le_add (G'.le_opNorm δd) h1
          _ = (‖G'‖ + ε) * ‖δd‖ := by ring
    _ = ‖G'‖ₑ + ε := by
        rw [ENNReal.ofReal_add (norm_nonneg _) ε.coe_nonneg, ofReal_norm,
          ENNReal.ofReal_coe_nnreal]

/-- **The first-order formula (2.7) of [quarteroni2000numerical], relative form**: for `d ≠ 0`
and `G d ≠ 0`, `relCondNumber G S d = ‖G'‖ₑ * (‖d‖ₑ / ‖G d‖ₑ)`. -/
theorem relCondNumber_eq_enorm_fderiv {G' : D →L[𝕜] X} (hG : HasFDerivAt G G' d)
    (hS : S ∈ 𝓝 d) (hd : d ≠ 0) (hx : G d ≠ 0) :
    relCondNumber G S d = ‖G'‖ₑ * (‖d‖ₑ / ‖G d‖ₑ) := by
  rw [relCondNumber_eq G S hd hx, absCondNumber_eq_enorm_fderiv hG hS]

/-! ### Instance: linear problems -/

/-- A bounded linear resolvent has condition number `‖L‖ₑ` over every neighbourhood of the
datum: the amplification ratio `‖L δd‖ / ‖δd‖` is scale invariant, so its supremum over any ball
is the operator norm. -/
theorem absCondNumberWithin_continuousLinearMap (L : D →L[𝕜] X) (hS : S ∈ 𝓝 d) {η : ℝ}
    (hη : 0 < η) : absCondNumberWithin L S d η = ‖L‖ₑ := by
  refine le_antisymm ?_ (enorm_fderiv_le_absCondNumberWithin L.hasFDerivAt hS hη)
  rw [← ofReal_norm]
  exact absCondNumberOn_le_of_forall_norm_sub_le (norm_nonneg L) fun δd _ _ => by
    simpa using L.le_opNorm δd

/-- A bounded linear resolvent has first-order condition number `‖L‖ₑ`. -/
theorem absCondNumber_continuousLinearMap (L : D →L[𝕜] X) (hS : S ∈ 𝓝 d) :
    absCondNumber L S d = ‖L‖ₑ :=
  absCondNumber_eq_enorm_fderiv L.hasFDerivAt hS

/-- The relative condition number of a bounded linear resolvent over any neighbourhood of `d` is
`‖L‖ₑ * (‖d‖ₑ / ‖L d‖ₑ)`. -/
theorem relCondNumberWithin_continuousLinearMap (L : D →L[𝕜] X) (hS : S ∈ 𝓝 d) {η : ℝ}
    (hη : 0 < η) : relCondNumberWithin L S d η = ‖L‖ₑ * (‖d‖ₑ / ‖L d‖ₑ) := by
  rw [relCondNumberWithin, relCondNumberOn_eq, ← absCondNumberWithin,
    absCondNumberWithin_continuousLinearMap L hS hη]

/-- **Conditioning of a linear system with respect to its right-hand side**
([quarteroni2000numerical] Example 2.3, (2.9)): for an isomorphism `A : E ≃L[𝕜] F` of normed
spaces and `b ≠ 0`, the problem `A x = b` perturbed in `b` only has resolvent `A.symm` and
relative condition number `‖A⁻¹‖ ‖b‖ / ‖A⁻¹ b‖ ≤ ‖A‖ ‖A⁻¹‖ = κ(A)`, the condition number
`ContinuousLinearEquiv.condNumber`. -/
theorem relCondNumber_symm_le_condNumber {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] (A : E ≃L[𝕜] F) {b : F} (hb : b ≠ 0) :
    relCondNumber A.symm univ b ≤ ENNReal.ofReal A.condNumber := by
  have hAb : A.symm b ≠ 0 := by simpa using hb
  have hle : ‖b‖ₑ / ‖A.symm b‖ₑ ≤ ‖(A : E →L[𝕜] F)‖ₑ := by
    rw [ENNReal.div_le_iff (enorm_ne_zero.2 hAb) enorm_ne_top, ← ofReal_norm, ← ofReal_norm,
      ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (by simpa using (A : E →L[𝕜] F).le_opNorm (A.symm b))
  calc relCondNumber A.symm univ b = ‖(A.symm : F →L[𝕜] E)‖ₑ * (‖b‖ₑ / ‖A.symm b‖ₑ) := by
        rw [relCondNumber_eq _ _ hb hAb, absCondNumber_eq_enorm_fderiv A.symm.hasFDerivAt univ_mem]
    _ ≤ ‖(A.symm : F →L[𝕜] E)‖ₑ * ‖(A : E →L[𝕜] F)‖ₑ := mul_le_mul_right hle _
    _ = ENNReal.ofReal A.condNumber := by
        rw [ContinuousLinearEquiv.condNumber, ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm,
          ofReal_norm, mul_comm]

end FirstOrder

/-! ### Instance: roots of functions -/

section Roots

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- **Conditioning of a simple root** ([quarteroni2000numerical] Example 2.4, (2.11); the
instance behind its §6.1): if `G` is a continuous local inverse of `φ` at `d`, so that `G y` is
the root of `φ x = y`, and `φ' ≠ 0` is the strict derivative of `φ` at that root, then the root
depends on the datum with absolute condition number `‖φ'‖ₑ⁻¹`. -/
theorem absCondNumber_of_local_left_inverse {φ G : 𝕜 → 𝕜} {φ' d : 𝕜} (hG : ContinuousAt G d)
    (hφ : HasStrictDerivAt φ φ' (G d)) (hφ' : φ' ≠ 0) (hinv : ∀ᶠ y in 𝓝 d, φ (G y) = y) :
    absCondNumber G univ d = ‖φ'‖ₑ⁻¹ := by
  rw [absCondNumber_eq_enorm_fderiv
    (HasStrictDerivAt.of_local_left_inverse hG hφ hφ' hinv).hasDerivAt.hasFDerivAt univ_mem,
    ← enorm_inv hφ', ← ofReal_norm, ← ofReal_norm]
  simp

/-- **Relative conditioning of a simple root** ([quarteroni2000numerical] Example 2.4, (2.10)):
under the hypotheses of `absCondNumber_of_local_left_inverse`, for `d ≠ 0` and a nonzero root,
`relCondNumber G univ d = ‖φ'‖ₑ⁻¹ * (‖d‖ₑ / ‖G d‖ₑ)`. -/
theorem relCondNumber_of_local_left_inverse {φ G : 𝕜 → 𝕜} {φ' d : 𝕜} (hG : ContinuousAt G d)
    (hφ : HasStrictDerivAt φ φ' (G d)) (hφ' : φ' ≠ 0) (hinv : ∀ᶠ y in 𝓝 d, φ (G y) = y)
    (hd : d ≠ 0) (hx : G d ≠ 0) :
    relCondNumber G univ d = ‖φ'‖ₑ⁻¹ * (‖d‖ₑ / ‖G d‖ₑ) := by
  rw [relCondNumber_eq G univ hd hx, absCondNumber_of_local_left_inverse hG hφ hφ' hinv]

variable [NormedSpace 𝕜 D] [NormedSpace 𝕜 X]

/-- **A multiple root is infinitely ill conditioned**, Fréchet form: if `G` is a right inverse
of `φ` on the admissible data `S` near `d` (`φ (G y) = y`), `G` is continuous at `d` within `S`,
`d` is an accumulation point of `S`, and the derivative of `φ` at the root `G d` vanishes, then
`absCondNumber G S d = ⊤`. Indeed `‖y - d‖ = ‖φ (G y) - φ (G d)‖ = o(‖G y - G d‖)`, so the
amplification ratio is unbounded on every ball. Stated within `S`, not on the whole space, so
that one-sided roots are covered — the double root at `p = 1` of `x² - 2px + 1`, whose
resolvent exists only for `p ≥ 1` ([quarteroni2000numerical] Remark 2.1). The book calls such a
root "ill posed"; the problem may well be well posed (continuous), so the honest statement is
infinite conditioning. -/
theorem absCondNumber_eq_top_of_fderiv_eq_zero {φ : X → D} [NeBot (𝓝[S \ {d}] d)]
    (hG : ContinuousWithinAt G S d) (hφ : HasFDerivAt φ (0 : X →L[𝕜] D) (G d))
    (hinv : ∀ᶠ y in 𝓝[S] d, φ (G y) = y) : absCondNumber G S d = ⊤ := by
  have hle : 𝓝[S \ {d}] d ≤ 𝓝[S] d := nhdsWithin_mono _ sdiff_subset
  have hinv' : ∀ᶠ y in 𝓝[S \ {d}] d, φ (G y) = y := hinv.filter_mono hle
  have hT : Tendsto G (𝓝[S \ {d}] d) (𝓝 (G d)) := hG.tendsto.mono_left hle
  have hφd : φ (G d) = d :=
    tendsto_nhds_unique (hφ.continuousAt.tendsto.comp hT)
      ((tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).congr' (hinv'.mono fun _ hy => hy.symm))
  simp only [absCondNumber, iInf_eq_top]
  intro η hη
  refine ENNReal.eq_top_of_forall_nnreal_le fun M => ?_
  have hε : (0 : ℝ) < ((M : ℝ) + 1)⁻¹ := by positivity
  have h1 : ∀ᶠ x in 𝓝 (G d), ‖φ x - φ (G d)‖ ≤ ((M : ℝ) + 1)⁻¹ * ‖x - G d‖ := by
    simpa using isLittleO_iff.1 (hasFDerivAt_iff_isLittleO.1 hφ) hε
  have h2 : ∀ᶠ y in 𝓝[S \ {d}] d, ‖y - d‖ ≤ ((M : ℝ) + 1)⁻¹ * ‖G y - G d‖ := by
    filter_upwards [hT.eventually h1, hinv'] with y hy hy'
    rwa [hy', hφd] at hy
  have h3 : ∀ᶠ y in 𝓝[S \ {d}] d, ‖y - d‖ < η :=
    (Metric.eventually_nhds_iff.2 ⟨η, hη, fun y hy => dist_eq_norm y d ▸ hy⟩).filter_mono
      nhdsWithin_le_nhds
  obtain ⟨y, hyS, hy1, hy2⟩ := (eventually_mem_nhdsWithin.and (h2.and h3)).exists
  have hyd : y - d ≠ 0 := sub_ne_zero.2 hyS.2
  have h4 := le_absCondNumberOn (G := G) (N := perturbations S d η) (d := d) (δd := y - d)
    ⟨hy2, by simpa using hyS.1⟩ hyd
  rw [add_sub_cancel] at h4
  refine le_trans ?_ h4
  rw [ENNReal.le_div_iff_mul_le (Or.inl (enorm_ne_zero.2 hyd)) (Or.inl enorm_ne_top),
    ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul M.coe_nonneg]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [inv_mul_eq_div, le_div_iff₀ (by positivity)] at hy1
  nlinarith [norm_nonneg (y - d)]

/-- **A multiple root is infinitely ill conditioned** ([quarteroni2000numerical] Example 2.4,
"ill posed if `x` is a multiple root", and §6.1): for `φ G : 𝕜 → 𝕜` with `G` a continuous right
inverse of `φ` on the admissible data `S` near the accumulation point `d` of `S`, and
`φ' (G d) = 0`, the root has `absCondNumber G S d = ⊤`. -/
theorem absCondNumber_eq_top_of_deriv_eq_zero {φ G : 𝕜 → 𝕜} {S : Set 𝕜} {d : 𝕜}
    [NeBot (𝓝[S \ {d}] d)] (hG : ContinuousWithinAt G S d) (hφ : HasDerivAt φ 0 (G d))
    (hinv : ∀ᶠ y in 𝓝[S] d, φ (G y) = y) : absCondNumber G S d = ⊤ :=
  absCondNumber_eq_top_of_fderiv_eq_zero hG (by simpa using hφ.hasFDerivAt) hinv

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **Conditioning of a root in Banach spaces**: the local inverse of `φ` given by the inverse
function theorem at a point where the strict derivative `φ'` is an isomorphism has absolute
condition number `‖φ'⁻¹‖ₑ`. -/
theorem absCondNumber_localInverse {φ : E → F} {φ' : E ≃L[𝕜] F} {x : E}
    (hφ : HasStrictFDerivAt φ (φ' : E →L[𝕜] F) x) :
    absCondNumber (hφ.localInverse φ φ' x) univ (φ x) = ‖(φ'.symm : F →L[𝕜] E)‖ₑ :=
  absCondNumber_eq_enorm_fderiv hφ.to_localInverse.hasFDerivAt univ_mem

end Roots

end Conditioning
