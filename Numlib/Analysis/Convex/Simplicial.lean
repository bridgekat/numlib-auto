import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.Semicontinuity.Basic
import Numlib.Analysis.Convex.RelativeInterior

/-!
# Simplices, locally simplicial sets, and upper semicontinuity

A convex function is upper semicontinuous relative to any *locally simplicial* subset of its
effective domain, so a closed convex function is continuous relative to such a set. This is the
sharp form of "a convex function is continuous on a simplex in its domain": the phenomenon is
genuinely about simplices and fails for arbitrary convex subsets of `dom f`. The application is an
extension theorem: a finite convex function on `ri C`, bounded above on bounded subsets, extends
uniquely to a continuous finite convex function on a locally simplicial convex `C`.

## Main definitions

* `IsSimplex S` — `S` is the convex hull of a finite affinely independent family.
* `LocallySimplicial S` — every point of `S` has a neighbourhood in which `S` coincides with a
  finite union of simplices contained in `S`; every polyhedral convex set is one.

## Main results

* `ConvexFn.upperSemicontinuousWithinAt_convexHull_range` — the analytic core: a convex function
  finite on the vertices of a simplex is upper semicontinuous relative to that simplex, at *every*
  one of its points.
* `ConvexFn.upperSemicontinuousOn_of_locallySimplicial` — the same, relative to any locally
  simplicial subset of `dom f`.
* `ConvexFn.continuousOn_of_locallySimplicial` — continuity there, for a closed `f`.
* `exists_closedFn_continuousOn_of_locallySimplicial`, `eqOn_of_continuousOn_of_eqOn_relint` —
  the extension theorem, existence and uniqueness.

## Implementation notes

The analytic core needs no triangulation. Rockafellar reduces to the case where `x` is a *vertex*
of the simplex by triangulating around `x`. Instead, writing `x = Σ μᵢ vᵢ` and `z = Σ wᵢ vᵢ`, every
`z` whose weights satisfy `wᵢ ≥ (1 - ε) μᵢ` is `(1 - ε) x + ε y` with `y` again in the simplex, for
a *fixed* `ε` chosen in advance from the target bound; convexity then bounds `f z` by
`(1 - ε) β + ε ν`. That weight condition holds on a neighbourhood of `x` by compactness of the
standard simplex, affine independence making the weights of a point unique — the only use of
affine independence, and the only use of a topology: no metric, no finite dimension.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §10.
-/

open Set Filter
open scoped Topology

namespace ConvexAnalysis

/-! ### Barycentric weights -/

section Weights

variable {ι : Type*} [Fintype ι] {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The point with barycentric weights `w` relative to the family `v`. -/
def weightPt (v : ι → E) (w : ι → ℝ) : E := ∑ i, w i • v i

theorem weightPt_eq_affineCombination (v : ι → E) {w : ι → ℝ} (hw : ∑ i, w i = 1) :
    weightPt v w = Finset.univ.affineCombination ℝ v w :=
  (Finset.affineCombination_eq_linear_combination _ _ _ hw).symm

/-- A convex hull of finitely many points is the image of the standard simplex under the
weight map. -/
theorem convexHull_range_eq_image_stdSimplex (v : ι → E) :
    convexHull ℝ (Set.range v) = weightPt v '' stdSimplex ℝ ι := by
  classical
  ext x
  rw [convexHull_range_eq_exists_affineCombination]
  constructor
  · rintro ⟨s, w, hw0, hw1, rfl⟩
    refine ⟨fun i => if i ∈ s then w i else 0, ⟨fun i => ?_, ?_⟩, ?_⟩
    · by_cases hi : i ∈ s
      · simpa [hi] using hw0 i hi
      · simp [hi]
    · simpa using hw1
    · simp only [weightPt, ite_smul, zero_smul, Finset.sum_ite_mem, Finset.univ_inter]
      exact (Finset.affineCombination_eq_linear_combination _ _ _ hw1).symm
  · rintro ⟨w, ⟨hw0, hw1⟩, rfl⟩
    exact ⟨Finset.univ, w, fun i _ => hw0 i, hw1,
      Finset.affineCombination_eq_linear_combination _ _ _ hw1⟩

/-- The weight map is affine in the weights: a convex combination of weight vectors gives the
corresponding convex combination of points. -/
theorem weightPt_combo (v : ι → E) (w₁ w₂ : ι → ℝ) (a b : ℝ) :
    weightPt v (fun i => a * w₁ i + b * w₂ i) = a • weightPt v w₁ + b • weightPt v w₂ := by
  simp only [weightPt, add_smul, mul_smul, Finset.smul_sum]
  exact Finset.sum_add_distrib

end Weights

/-! ### Simplices and locally simplicial sets -/

section Defs

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]

/-- A **simplex**: the convex hull of a finite affinely independent family of points. -/
def IsSimplex (S : Set E) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (v : ι → E), AffineIndependent ℝ v ∧ S = convexHull ℝ (Set.range v)

/-- Rockafellar's **locally simplicial** sets: near each of its points, `S` agrees with a finite
union of simplices contained in `S`. Such a set need be neither convex nor closed. -/
def LocallySimplicial (S : Set E) : Prop :=
  ∀ x ∈ S, ∃ (n : ℕ) (P : Fin n → Set E), (∀ i, IsSimplex (P i)) ∧ (∀ i, P i ⊆ S) ∧
    ∃ U ∈ 𝓝 x, U ∩ (⋃ i, P i) = U ∩ S

/-- A simplex is compact: it is the convex hull of a finite set. -/
theorem IsSimplex.isCompact [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] {S : Set E}
    (hS : IsSimplex S) : IsCompact S := by
  obtain ⟨ι, _, v, -, rfl⟩ := hS
  exact (Set.finite_range v).isCompact_convexHull ℝ

end Defs

/-! ### The analytic core: upper semicontinuity relative to a simplex -/

section Core

variable {ι : Type*} [Finite ι] {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E] {f : E → EReal}

/-- **A convex function whose value at each vertex of a simplex is `< ⊤` is upper semicontinuous
relative to that simplex**, at every point of it. -/
theorem ConvexFn.upperSemicontinuousWithinAt_convexHull_range (hf : ConvexFn f) {v : ι → E}
    (hv : AffineIndependent ℝ v) (hdom : ∀ i, v i ∈ dom f) {x : E}
    (hx : x ∈ convexHull ℝ (Set.range v)) :
    UpperSemicontinuousWithinAt f (convexHull ℝ (Set.range v)) x := by
  classical
  obtain ⟨hι⟩ := nonempty_fintype ι
  -- a real bound for `f` on the whole simplex
  have hbdd : ∀ i, ∃ c : ℝ, f (v i) ≤ (c : EReal) := fun i => by
    obtain ⟨c, hc, -⟩ := _root_.EReal.lt_iff_exists_real_btwn.1 (mem_dom.1 (hdom i))
    exact ⟨c, hc.le⟩
  choose c hc using hbdd
  obtain ⟨ν, hν⟩ := (Set.finite_range c).bddAbove
  have hνv : ∀ i, f (v i) ≤ (ν : EReal) := fun i =>
    (hc i).trans (_root_.EReal.coe_le_coe_iff.2 (hν ⟨i, rfl⟩))
  have hνT : ∀ z ∈ convexHull ℝ (Set.range v), f z ≤ (ν : EReal) :=
    convexHull_min (by rintro _ ⟨i, rfl⟩; exact hνv i) (hf.convex_le (ν : EReal))
  -- the weights of `x`
  rw [convexHull_range_eq_image_stdSimplex] at hx
  obtain ⟨μ, hμΔ, rfl⟩ := hx
  intro b hb
  -- two real numbers below `b` and above `f x`
  obtain ⟨β, hβ1, hβ2⟩ := _root_.EReal.lt_iff_exists_real_btwn.1 hb
  obtain ⟨γ, hγ1, hγ2⟩ := _root_.EReal.lt_iff_exists_real_btwn.1 hβ2
  have hβγ : β < γ := by exact_mod_cast hγ1
  -- the shrinking factor
  set ε : ℝ := min 1 ((γ - β) / (|ν - β| + 1)) with hε
  have hpos : (0 : ℝ) < |ν - β| + 1 := by positivity
  have hε0 : 0 < ε := lt_min zero_lt_one (div_pos (by linarith) hpos)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hεle : ε * (|ν - β| + 1) ≤ γ - β := by
    have := min_le_right (1 : ℝ) ((γ - β) / (|ν - β| + 1))
    calc ε * (|ν - β| + 1) ≤ (γ - β) / (|ν - β| + 1) * (|ν - β| + 1) := by
          exact mul_le_mul_of_nonneg_right this hpos.le
      _ = γ - β := by field_simp
  -- the bad weights form a compact set whose image misses `x`
  set D : Set (ι → ℝ) :=
    stdSimplex ℝ ι ∩ ⋃ i ∈ {i : ι | μ i ≠ 0}, {w : ι → ℝ | w i ≤ (1 - ε) * μ i} with hD
  have hDclosed : IsClosed (⋃ i ∈ {i : ι | μ i ≠ 0}, {w : ι → ℝ | w i ≤ (1 - ε) * μ i}) :=
    Set.Finite.isClosed_biUnion (Set.toFinite _) fun i _ =>
      isClosed_le (continuous_apply i) continuous_const
  have hDcompact : IsCompact D := (isCompact_stdSimplex ℝ ι).inter_right hDclosed
  have hwcont : Continuous (weightPt v) :=
    continuous_finsetSum _ fun i _ => (continuous_apply i).smul continuous_const
  have hImg : IsClosed (weightPt v '' D) := (hDcompact.image hwcont).isClosed
  have hnot : weightPt v μ ∉ weightPt v '' D := by
    rintro ⟨w, ⟨hwΔ, hwU⟩, hwx⟩
    have hwμ : w = μ := by
      refine (affineIndependent_iff_eq_of_fintype_affineCombination_eq (k := ℝ) v).1 hv w μ
        hwΔ.2 hμΔ.2 ?_
      rw [← weightPt_eq_affineCombination v hwΔ.2, ← weightPt_eq_affineCombination v hμΔ.2, hwx]
    obtain ⟨i, hi, hle⟩ := Set.mem_iUnion₂.1 hwU
    have hi' : μ i ≠ 0 := hi
    have hle' : w i ≤ (1 - ε) * μ i := hle
    rw [hwμ] at hle'
    have hμi : 0 < μ i := lt_of_le_of_ne (hμΔ.1 i) (Ne.symm hi')
    nlinarith
  -- and therefore misses a neighbourhood of `x`
  have hnbhd : (weightPt v '' D)ᶜ ∈ 𝓝 (weightPt v μ) := hImg.isOpen_compl.mem_nhds hnot
  rw [eventually_nhdsWithin_iff]
  filter_upwards [hnbhd] with z hz hzT
  -- `z` has weights, and they are not bad
  rw [convexHull_range_eq_image_stdSimplex] at hzT
  obtain ⟨w, hwΔ, rfl⟩ := hzT
  have hgood : ∀ i, (1 - ε) * μ i ≤ w i := by
    intro i
    by_cases hi : μ i = 0
    · simpa [hi] using hwΔ.1 i
    · by_contra hcon
      exact hz ⟨w, ⟨hwΔ, Set.mem_iUnion₂.2 ⟨i, hi, le_of_not_ge hcon⟩⟩, rfl⟩
  -- the rescaled weights
  set y : ι → ℝ := fun i => ε⁻¹ * (w i - (1 - ε) * μ i) with hy
  have hyΔ : y ∈ stdSimplex ℝ ι := by
    constructor
    · intro i
      exact mul_nonneg (inv_nonneg.2 hε0.le) (by linarith [hgood i])
    · have hsum : ∑ i, y i = ∑ i, ε⁻¹ * (w i - (1 - ε) * μ i) := rfl
      rw [hsum, ← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum, hwΔ.2, hμΔ.2,
        mul_one, show (1 : ℝ) - (1 - ε) = ε by ring]
      exact inv_mul_cancel₀ hε0.ne'
  have hdecomp : w = fun i => (1 - ε) * μ i + ε * y i := by
    funext i
    simp only [hy]
    rw [← mul_assoc, mul_inv_cancel₀ hε0.ne', one_mul]
    ring
  have hz' : weightPt v w = (1 - ε) • weightPt v μ + ε • weightPt v y := by
    rw [hdecomp, weightPt_combo]
  rw [hz']
  refine lt_of_le_of_lt (hf.epi_combo hβ1.le (hνT _ ?_) (by linarith) hε0.le (by ring)) ?_
  · rw [convexHull_range_eq_image_stdSimplex]
    exact ⟨y, hyΔ, rfl⟩
  · refine lt_of_le_of_lt (_root_.EReal.coe_le_coe_iff.2 ?_) hγ2
    nlinarith [le_abs_self (ν - β), abs_nonneg (ν - β)]

end Core

/-! ### Upper semicontinuity on a locally simplicial set -/

section UpperSemicontinuous

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E] {f : E → EReal} {S : Set E}

/-- **A convex function is upper semicontinuous relative to any locally simplicial subset of its
effective domain.** -/
theorem ConvexFn.upperSemicontinuousOn_of_locallySimplicial (hf : ConvexFn f)
    (hS : LocallySimplicial S) (hSdom : S ⊆ dom f) : UpperSemicontinuousOn f S := by
  intro x hxS b hb
  obtain ⟨n, P, hPsimp, hPsub, U, hU, hUeq⟩ := hS x hxS
  -- the pieces that stay away from `x` can be discarded
  have hfar : ∀ i : {i : Fin n // x ∉ P i}, (P i.1)ᶜ ∈ 𝓝 x := fun i =>
    ((IsSimplex.isCompact (hPsimp i.1)).isClosed).isOpen_compl.mem_nhds i.2
  -- upper semicontinuity relative to each piece containing `x`
  have hnear : ∀ i : Fin n, x ∈ P i → ∀ᶠ z in 𝓝 x, z ∈ P i → f z < b := by
    intro i hi
    obtain ⟨ι, _, v, hv, hPv⟩ := hPsimp i
    rw [← eventually_nhdsWithin_iff, hPv]
    refine hf.upperSemicontinuousWithinAt_convexHull_range hv (fun j => ?_) (hPv ▸ hi) b hb
    exact hSdom (hPsub i (hPv ▸ subset_convexHull ℝ _ ⟨j, rfl⟩))
  choose W hWmem hWlt using fun (i : {i : Fin n // x ∈ P i}) => (hnear i.1 i.2).exists_mem
  -- assemble a single neighbourhood of `x`
  have hV : U ∩ (⋂ i : {i : Fin n // x ∈ P i}, W i) ∩
      (⋂ i : {i : Fin n // x ∉ P i}, (P i.1)ᶜ) ∈ 𝓝 x :=
    Filter.inter_mem (Filter.inter_mem hU (Filter.iInter_mem.2 hWmem))
      (Filter.iInter_mem.2 hfar)
  rw [eventually_nhdsWithin_iff]
  filter_upwards [hV] with z hz hzS
  obtain ⟨⟨hzU, hzW⟩, hzF⟩ := hz
  have hzP : z ∈ ⋃ i, P i := by
    have hmem : z ∈ U ∩ S := ⟨hzU, hzS⟩
    rw [← hUeq] at hmem
    exact hmem.2
  obtain ⟨i, hzi⟩ := Set.mem_iUnion.1 hzP
  by_cases hi : x ∈ P i
  · exact hWlt ⟨i, hi⟩ z (Set.mem_iInter.1 hzW ⟨i, hi⟩) hzi
  · exact absurd hzi (Set.mem_iInter.1 hzF ⟨i, hi⟩)

/-- **A closed convex function is continuous relative to any locally simplicial subset of its
effective domain.** Lower semicontinuity supplies one half of `tendsto_order` and upper
semicontinuity the other. -/
theorem ConvexFn.continuousOn_of_locallySimplicial (hf : ConvexFn f)
    (hlsc : LowerSemicontinuous f) (hS : LocallySimplicial S) (hSdom : S ⊆ dom f) :
    ContinuousOn f S := by
  intro x hx
  rw [ContinuousWithinAt, tendsto_order]
  exact ⟨fun b hb => (hlsc x b hb).filter_mono nhdsWithin_le_nhds,
    fun b hb => hf.upperSemicontinuousOn_of_locallySimplicial hS hSdom x hx b hb⟩

end UpperSemicontinuous

/-! ### Extension from the relative interior -/

section Extension

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {C : Set E} {f : E → EReal}

/-- `ri C` is dense in `C`, so two functions continuous relative to `C` that agree on `ri C` agree
on all of `C`. This is the uniqueness half of the extension theorem, and it needs neither convexity
of the functions nor local simpliciality of `C`. -/
theorem eqOn_of_continuousOn_of_eqOn_relint (hC : Convex ℝ C) {g₁ g₂ : E → EReal}
    (h₁ : ContinuousOn g₁ C) (h₂ : ContinuousOn g₂ C) (h : Set.EqOn g₁ g₂ (ri C)) :
    Set.EqOn g₁ g₂ C := by
  intro x hx
  have hxcl : x ∈ closure (ri C) := by
    rw [Convex.closure_relint hC]; exact subset_closure hx
  have hne : (𝓝[ri C] x).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hxcl
  have t₁ : Tendsto g₁ (𝓝[ri C] x) (𝓝 (g₁ x)) := (h₁ x hx).mono intrinsicInterior_subset
  have t₂ : Tendsto g₂ (𝓝[ri C] x) (𝓝 (g₂ x)) := (h₂ x hx).mono intrinsicInterior_subset
  exact tendsto_nhds_unique
    (t₁.congr' (eventually_nhdsWithin_of_forall fun y hy => h hy)) t₂

/-- **The extension theorem, existence.** A convex function finite exactly on `ri C` and bounded
above on every bounded subset of `ri C` has a closure that is finite and continuous on the
whole of a locally simplicial convex `C`, and still agrees with `f` on `ri C`. Uniqueness is
`eqOn_of_continuousOn_of_eqOn_relint`. -/
theorem exists_closedFn_continuousOn_of_locallySimplicial (hC : Convex ℝ C)
    (hCls : LocallySimplicial C) (hne : C.Nonempty) (hf : ConvexFn f) (hbot : ∀ x, f x ≠ ⊥)
    (hdom : dom f = ri C)
    (hbdd : ∀ S ⊆ ri C, Bornology.IsBounded S → ∃ c : ℝ, ∀ x ∈ S, f x ≤ (c : EReal)) :
    ∃ g : E → EReal, ConvexFn g ∧ ClosedFn g ∧ Proper g ∧ Set.EqOn g f (ri C) ∧
      C ⊆ dom g ∧ ContinuousOn g C := by
  have hriC : (ri C).Nonempty := Convex.relint_nonempty hC hne
  have hp : Proper f := ⟨by rw [hdom]; exact hriC, hbot⟩
  have hridom : ri (dom f) = ri C := by rw [hdom, Convex.relint_relint hC]
  obtain ⟨x₀, hx₀⟩ := hriC
  have hCdom : C ⊆ dom (clFn f) := by
    intro x hx
    have hseg : (fun a : ℝ => (1 - a) • x₀ + a • x) '' Set.Ico 0 1 ⊆ ri C := by
      rintro _ ⟨a, ha, rfl⟩
      exact Convex.segment_mem_relint hC hx₀ (subset_closure hx) ha.1 ha.2
    have hcont : Continuous fun a : ℝ => (1 - a) • x₀ + a • x :=
      ((continuous_const.sub continuous_id).smul continuous_const).add
        (continuous_id.smul continuous_const)
    have hbnd : Bornology.IsBounded ((fun a : ℝ => (1 - a) • x₀ + a • x) '' Set.Ico 0 1) :=
      (isCompact_Icc.image hcont).isBounded.subset
        (Set.image_mono Set.Ico_subset_Icc_self)
    obtain ⟨c, hc⟩ := hbdd _ hseg hbnd
    have htend := hf.tendsto_clFn_along_segment_relint hp (hridom ▸ hx₀) x
    have hle : clFn f x ≤ (c : EReal) := by
      refine le_of_tendsto htend ?_
      filter_upwards [eventually_mem_Ico_nhdsLT_one] with a ha
      exact hc _ ⟨a, ha, rfl⟩
    exact mem_dom.2 (lt_of_le_of_lt hle (_root_.EReal.coe_lt_top c))
  refine ⟨clFn f, convexFn_clFn hf, closedFn_clFn f, hf.proper_clFn hp, ?_, hCdom, ?_⟩
  · intro x hx
    exact hf.clFn_eq_of_mem_relint_dom (hridom ▸ hx)
  · exact (convexFn_clFn hf).continuousOn_of_locallySimplicial
      (closedFn_clFn f).lowerSemicontinuous hCls hCdom

end Extension

end ConvexAnalysis
