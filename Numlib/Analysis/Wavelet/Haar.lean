import Mathlib.Algebra.GroupWithZero.Action.Pointwise.Set
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The Haar system on `L²(ℝ)`

The Haar scaling functions `2^(j/2) φ(2^j x - k)` for the unit step `φ = 1_[0,1)`, the scaling
spaces `V j`, the Haar wavelet `ψ = φ(2 ·) - φ(2 · - 1)`, the wavelet spaces `W j`, and the
decomposition and reconstruction formulas relating consecutive levels.

Two design points fix the shape of the module.

*The spaces are closed subspaces, not spans of finite combinations.* The scaling space of a level is
defined here as `(span ℝ (range (scalingFun j))).topologicalClosure`, so that "orthonormal basis",
the nesting `V j ≤ V (j+1)`, `⨅ j, V j = ⊥` and the density of `⨆ j, V j` all read in `L²`; the set
of *finite* linear combinations of the scaling functions is its dense subspace.

*Dilation is a unitary of `L²(ℝ)`, and it comes first.* `MeasureTheory.Lp.dilationₗᵢ c` sends `f` to
`x ↦ |c| ^ (1/2) * f (c * x)`; every scale-invariance statement goes through it. Mathlib has
`MeasureTheory.Lp.compMeasurePreserving`, but a scaling is not measure preserving, only
quasi-measure preserving, so the underlying map on `α →ₘ[μ] β` is built from
`MeasureTheory.AEEqFun.compQuasiMeasurePreserving`.

## Main definitions

* `MeasureTheory.Lp.dilationₗᵢ`: the dilation, as an element of `L²(ℝ) ≃ₗᵢ[ℝ] L²(ℝ)`.
* `Haar.scalingFun`, `Haar.waveletFun`: the Haar scaling and wavelet functions.
* `Haar.V`, `Haar.W`: the scaling and wavelet spaces, with their Hilbert bases.
* `Haar.hilbertBasis`: the wavelets of all levels together, as a Hilbert basis of `L²(ℝ)`.

## Main statements

* `Haar.orthonormal_scalingFun`, `Haar.V_eq_map_dilation`, `Haar.V_le_V_succ`,
  `Haar.topologicalClosure_iSup_V`, `Haar.iInf_V_eq_bot`: the multiresolution properties of the
  scaling spaces.
* `Haar.mem_W_iff`, `Haar.isCompl_V_W`: `V (j+1)` is the orthogonal direct sum of `V j` and `W j`.
* `Haar.decomposition`, `Haar.reconstruction`: the analysis and synthesis formulas for the
  coefficients of one level in terms of the next.
* `Haar.starProjection_V_eq_sum`: the multi-level decomposition, one analysis step iterated, which
  splits the projection onto `V j` into a coarse part in `V i` and the detail parts in the
  intermediate wavelet spaces.
* `Haar.orthonormal_waveletFun_prod`, `Haar.hilbertBasis`: the wavelets of all levels are
  orthonormal and complete.

## References

The material is [han2009theoretical] §4.4 (Theorems 4.4.1–4.4.4 and Exercise 4.4.4). None of it
is in Mathlib.
-/

open scoped ENNReal Pointwise

noncomputable section

namespace MeasureTheory.Lp

variable {c d : ℝ}

/-! ### Auxiliary facts about the scaling `x ↦ c * x` of `ℝ` -/

/-- Multiplication by a nonzero constant is quasi-measure-preserving for the Lebesgue measure on
`ℝ`. -/
private theorem qmp_const_mul (hc : c ≠ 0) :
    Measure.QuasiMeasurePreserving (fun x : ℝ => c * x) volume volume := by
  refine ⟨measurable_const_mul c, ?_⟩
  rw [Real.map_volume_mul_left hc]
  exact Measure.smul_absolutelyContinuous

/-- Almost-everywhere equality is preserved by precomposition with `x ↦ c * x` for `c ≠ 0`. -/
theorem ae_comp_const_mul (hc : c ≠ 0) {g g' : ℝ → ℝ} (h : g =ᵐ[volume] g') :
    (fun x => g (c * x)) =ᵐ[volume] fun x => g' (c * x) :=
  h.comp_tendsto (qmp_const_mul hc).tendsto_ae

/-- The `L²` seminorm of `x ↦ g (c * x)`, for `c ≠ 0`. -/
private theorem eLpNorm_comp_const_mul (hc : c ≠ 0) {g : ℝ → ℝ}
    (hg : AEStronglyMeasurable g volume) :
    eLpNorm (fun x => g (c * x)) 2 volume
      = ENNReal.ofReal |c⁻¹| ^ (1 / 2 : ℝ) * eLpNorm g 2 volume := by
  have hmap : Measure.map (fun x : ℝ => c * x) volume = ENNReal.ofReal |c⁻¹| • volume :=
    Real.map_volume_mul_left hc
  have hg' : AEStronglyMeasurable g (Measure.map (fun x : ℝ => c * x) volume) := by
    rw [hmap]; exact hg.mono_ac Measure.smul_absolutelyContinuous
  have h1 := eLpNorm_map_measure (p := 2) hg' (measurable_const_mul c).aemeasurable
  rw [hmap, eLpNorm_smul_measure_of_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ∞)] at h1
  have h2 : ((1 : ℝ≥0∞) / 2).toReal = (1 / 2 : ℝ) := by simp
  rw [h2, smul_eq_mul, Function.comp_def] at h1
  exact h1.symm

/-- The preimage of a set of finite measure under `x ↦ c * x`, `c ≠ 0`, has finite measure. -/
theorem volume_preimage_const_mul_ne_top (hc : c ≠ 0) {s : Set ℝ} (hμs : volume s ≠ ∞) :
    volume ((fun x : ℝ => c * x) ⁻¹' s) ≠ ∞ := by
  rw [Real.volume_preimage_mul_left hc]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hμs

/-- The preimage of `s` under the scaling `x ↦ c * x`, `c ≠ 0`, is the rescaled set `c⁻¹ • s`. -/
theorem preimage_const_mul_eq_inv_smul (hc : c ≠ 0) (s : Set ℝ) :
    (fun x : ℝ => c * x) ⁻¹' s = c⁻¹ • s := by
  ext x
  rw [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero hc), inv_inv,
    smul_eq_mul]

/-! ### Precomposition with a scaling -/

private theorem mem_Lp_compQMP (hc : c ≠ 0) (f : Lp ℝ 2 (volume : Measure ℝ)) :
    f.1.compQuasiMeasurePreserving (fun x : ℝ => c * x) (qmp_const_mul hc)
      ∈ Lp ℝ 2 (volume : Measure ℝ) := by
  rw [mem_Lp_iff_eLpNorm_lt_top,
    eLpNorm_congr_ae (AEEqFun.coeFn_compQuasiMeasurePreserving _ _), Function.comp_def,
    eLpNorm_comp_const_mul hc (Lp.aestronglyMeasurable f)]
  exact ENNReal.mul_lt_top
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top) (eLpNorm_lt_top f)

/-- Precomposition of an `L²(ℝ)` function with the scaling `x ↦ c * x`, for `c ≠ 0`. -/
private noncomputable def compConstMul (c : ℝ) (hc : c ≠ 0) :
    Lp ℝ 2 (volume : Measure ℝ) →ₗ[ℝ] Lp ℝ 2 (volume : Measure ℝ) where
  toFun f := ⟨f.1.compQuasiMeasurePreserving _ (qmp_const_mul hc), mem_Lp_compQMP hc f⟩
  map_add' := by rintro ⟨⟨_⟩, _⟩ ⟨⟨_⟩, _⟩; rfl
  map_smul' := by rintro r ⟨⟨_⟩, _⟩; rfl

private theorem coeFn_compConstMul (hc : c ≠ 0) (f : Lp ℝ 2 (volume : Measure ℝ)) :
    compConstMul c hc f =ᵐ[volume] fun x => f (c * x) :=
  AEEqFun.coeFn_compQuasiMeasurePreserving f.1 (qmp_const_mul hc)

private theorem norm_compConstMul (hc : c ≠ 0) (f : Lp ℝ 2 (volume : Measure ℝ)) :
    ‖compConstMul c hc f‖ = |c⁻¹| ^ (1 / 2 : ℝ) * ‖f‖ := by
  rw [norm_def, norm_def, eLpNorm_congr_ae (coeFn_compConstMul hc f),
    eLpNorm_comp_const_mul hc (Lp.aestronglyMeasurable f), ENNReal.toReal_mul,
    ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal (abs_nonneg _)]

/-! ### The dilation as a linear map -/

/-- The dilation `f ↦ (x ↦ |c| ^ (1/2) * f (c * x))` of `L²(ℝ)`, as a linear map. -/
private noncomputable def dilationₗ (c : ℝ) (hc : c ≠ 0) :
    Lp ℝ 2 (volume : Measure ℝ) →ₗ[ℝ] Lp ℝ 2 (volume : Measure ℝ) :=
  (|c| ^ (1 / 2 : ℝ)) • compConstMul c hc

private theorem dilationₗ_apply (c : ℝ) (hc : c ≠ 0) (f : Lp ℝ 2 (volume : Measure ℝ)) :
    dilationₗ c hc f = (|c| ^ (1 / 2 : ℝ)) • compConstMul c hc f := rfl

private theorem coeFn_dilationₗ (c : ℝ) (hc : c ≠ 0) (f : Lp ℝ 2 (volume : Measure ℝ)) :
    dilationₗ c hc f =ᵐ[volume] fun x => |c| ^ (1 / 2 : ℝ) * f (c * x) := by
  rw [dilationₗ_apply]
  filter_upwards [Lp.coeFn_smul (|c| ^ (1 / 2 : ℝ)) (compConstMul c hc f),
    coeFn_compConstMul hc f] with x hx hx'
  rw [hx]
  simp [hx']

private theorem norm_dilationₗ (hc : c ≠ 0) (f : Lp ℝ 2 (volume : Measure ℝ)) :
    ‖dilationₗ c hc f‖ = ‖f‖ := by
  rw [dilationₗ_apply, norm_smul, norm_compConstMul hc, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (abs_nonneg c) _), ← mul_assoc,
    ← Real.mul_rpow (abs_nonneg c) (abs_nonneg c⁻¹), ← abs_mul, mul_inv_cancel₀ hc, abs_one,
    Real.one_rpow, one_mul]

private theorem dilationₗ_congr {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (h : a = b) :
    dilationₗ a ha = dilationₗ b hb := by subst h; rfl

private theorem dilationₗ_one (h : (1 : ℝ) ≠ 0) (f : Lp ℝ 2 (volume : Measure ℝ)) :
    dilationₗ 1 h f = f := by
  refine Lp.ext ?_
  filter_upwards [coeFn_dilationₗ 1 h f] with x hx
  rw [hx]
  simp

private theorem dilationₗ_comp (hc : c ≠ 0) (hd : d ≠ 0) (f : Lp ℝ 2 (volume : Measure ℝ)) :
    dilationₗ c hc (dilationₗ d hd f) = dilationₗ (d * c) (mul_ne_zero hd hc) f := by
  refine Lp.ext ?_
  filter_upwards [coeFn_dilationₗ c hc (dilationₗ d hd f),
    ae_comp_const_mul hc (coeFn_dilationₗ d hd f),
    coeFn_dilationₗ (d * c) (mul_ne_zero hd hc) f] with x hx hx2 hx3
  rw [hx, hx3, hx2, ← mul_assoc, ← mul_assoc]
  congr 1
  rw [← Real.mul_rpow (abs_nonneg c) (abs_nonneg d), ← abs_mul, mul_comm c d]

/-! ### The unitary dilation of `L²(ℝ)` -/

/-- For `c ≠ 0`, the unitary dilation of `L²(ℝ)`: `f ↦ (x ↦ |c| ^ (1/2) * f (c * x))`. -/
noncomputable def dilationₗᵢ (c : ℝ) (hc : c ≠ 0) :
    Lp ℝ 2 (volume : Measure ℝ) ≃ₗᵢ[ℝ] Lp ℝ 2 (volume : Measure ℝ) where
  toFun := dilationₗ c hc
  map_add' := map_add (dilationₗ c hc)
  map_smul' := map_smul (dilationₗ c hc)
  invFun := dilationₗ c⁻¹ (inv_ne_zero hc)
  left_inv f := by
    rw [dilationₗ_comp (inv_ne_zero hc) hc f,
      dilationₗ_congr (mul_ne_zero hc (inv_ne_zero hc)) one_ne_zero (mul_inv_cancel₀ hc)]
    exact dilationₗ_one _ f
  right_inv f := by
    rw [dilationₗ_comp hc (inv_ne_zero hc) f,
      dilationₗ_congr (mul_ne_zero (inv_ne_zero hc) hc) one_ne_zero (inv_mul_cancel₀ hc)]
    exact dilationₗ_one _ f
  norm_map' := norm_dilationₗ hc

theorem dilationₗᵢ_apply (c : ℝ) (hc : c ≠ 0) (f : Lp ℝ 2 (volume : Measure ℝ)) :
    dilationₗᵢ c hc f =ᵐ[volume] fun x => |c| ^ (1 / 2 : ℝ) * f (c * x) :=
  coeFn_dilationₗ c hc f

theorem dilationₗᵢ_trans (c d : ℝ) (hc : c ≠ 0) (hd : d ≠ 0)
    (f : Lp ℝ 2 (volume : Measure ℝ)) :
    dilationₗᵢ c hc (dilationₗᵢ d hd f) = dilationₗᵢ (d * c) (mul_ne_zero hd hc) f :=
  dilationₗ_comp hc hd f

theorem dilationₗᵢ_symm (c : ℝ) (hc : c ≠ 0) :
    (dilationₗᵢ c hc).symm = dilationₗᵢ c⁻¹ (inv_ne_zero hc) :=
  LinearIsometryEquiv.ext fun _ => rfl

/-! ### Action on indicator functions -/

/-- The dilation of `r` times the indicator of `s` is `|c| ^ (1/2) * r` times the indicator of the
rescaled set `(fun x => c * x) ⁻¹' s = c⁻¹ • s`. -/
theorem dilationₗᵢ_indicatorConstLp (c : ℝ) (hc : c ≠ 0) {s : Set ℝ} (hs : MeasurableSet s)
    (hμs : volume s ≠ ∞) (r : ℝ) :
    dilationₗᵢ c hc (indicatorConstLp 2 hs hμs r)
      = indicatorConstLp 2 (measurable_const_mul c hs)
          (volume_preimage_const_mul_ne_top hc hμs) (|c| ^ (1 / 2 : ℝ) * r) := by
  refine Lp.ext ?_
  filter_upwards [dilationₗᵢ_apply c hc (indicatorConstLp 2 hs hμs r),
    ae_comp_const_mul hc (indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hμs) (c := r)),
    indicatorConstLp_coeFn (p := 2) (hs := measurable_const_mul c hs)
      (hμs := volume_preimage_const_mul_ne_top hc hμs) (c := |c| ^ (1 / 2 : ℝ) * r)] with
    x hx hx2 hx3
  rw [hx, hx2, hx3]
  by_cases hxs : c * x ∈ s
  · rw [Set.indicator_of_mem hxs, Set.indicator_of_mem (Set.mem_preimage.mpr hxs)]
  · rw [Set.indicator_of_notMem hxs,
      Set.indicator_of_notMem (fun h => hxs (Set.mem_preimage.mp h)), mul_zero]

end MeasureTheory.Lp

/-! ### Two elementary facts about `indicatorConstLp` -/

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ≥0∞} {s t : Set α}

/-- Rescaling the constant of an `indicatorConstLp`. -/
theorem smul_indicatorConstLp (c : ℝ) (hs : MeasurableSet s) (hμs : μ s ≠ ⊤) (a : ℝ) :
    c • indicatorConstLp p hs hμs a = indicatorConstLp p hs hμs (c * a) := by
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_smul c (indicatorConstLp p hs hμs a),
    indicatorConstLp_coeFn (p := p) (hs := hs) (hμs := hμs) (c := a),
    indicatorConstLp_coeFn (p := p) (hs := hs) (hμs := hμs) (c := c * a)] with x h1 h2 h3
  rw [h1, h3, Pi.smul_apply, h2, smul_eq_mul]
  by_cases hx : x ∈ s <;>
    simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx]

/-- Transporting an `indicatorConstLp` along an equality of sets. -/
theorem indicatorConstLp_congr_set (hs : MeasurableSet s) (hμs : μ s ≠ ⊤) (ht : MeasurableSet t)
    (hμt : μ t ≠ ⊤) (h : s = t) (c : ℝ) :
    indicatorConstLp p hs hμs c = indicatorConstLp p ht hμt c := by
  subst h
  rfl

end MeasureTheory

/-! ### A Hilbert basis of the closed span of an orthonormal family -/

section HilbertBasis

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {v : ι → E}

omit [CompleteSpace E] in
/-- A vector orthogonal to every member of a family is orthogonal to the span of the family. -/
theorem Submodule.mem_orthogonal_span_range {x : E} (h : ∀ i, inner ℝ (v i) x = 0) :
    x ∈ (Submodule.span ℝ (Set.range v))ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro u hu
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hu
  · rintro y ⟨i, rfl⟩
    exact h i
  · simp
  · intro a b _ _ ha hb
    rw [inner_add_left, ha, hb, add_zero]
  · intro r a _ ha
    rw [real_inner_smul_left, ha, mul_zero]

/-- An orthonormal family is a Hilbert basis of the closure of its span. -/
def Orthonormal.hilbertBasisTopologicalClosure (hv : Orthonormal ℝ v) :
    HilbertBasis ι ℝ ((Submodule.span ℝ (Set.range v)).topologicalClosure) :=
  haveI : CompleteSpace ((Submodule.span ℝ (Set.range v)).topologicalClosure) :=
    (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  HilbertBasis.mkOfOrthogonalEqBot
    (hv.codRestrict _ fun i =>
      Submodule.le_topologicalClosure _ (Submodule.subset_span (Set.mem_range_self i)))
    (by
      rw [Submodule.eq_bot_iff]
      intro x hx
      have hgen : ∀ i, inner ℝ (v i) (x : E) = 0 := fun i =>
        (Submodule.mem_orthogonal _ _).1 hx _ (Submodule.subset_span (Set.mem_range_self i))
      have hmem : (x : E) ∈ (Submodule.span ℝ (Set.range v))ᗮ :=
        Submodule.mem_orthogonal_span_range hgen
      have hmem2 : (x : E) ∈ (Submodule.span ℝ (Set.range v))ᗮᗮ :=
        Submodule.topologicalClosure_minimal _ (Submodule.le_orthogonal_orthogonal _)
          (Submodule.isClosed_orthogonal _) x.2
      have hzero : inner ℝ (x : E) (x : E) = 0 := (Submodule.mem_orthogonal _ _).1 hmem2 _ hmem
      exact Submodule.coe_eq_zero.mp (inner_self_eq_zero.mp hzero))

/-- **The expansion of an orthogonal projection in an orthonormal family.** The projection onto
the closed span of an orthonormal family is the sum of the family against the coefficients of the
projected vector; for a vector already in that closed span it is the expansion of the vector
itself. -/
theorem Orthonormal.hasSum_inner_smul_starProjection (hv : Orthonormal ℝ v) (x : E) :
    HasSum (fun i : ι => (inner ℝ (v i) x) • v i)
      ((Submodule.span ℝ (Set.range v)).topologicalClosure.starProjection x) := by
  have : CompleteSpace ((Submodule.span ℝ (Set.range v)).topologicalClosure) :=
    (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  have hmem : ∀ i : ι, v i ∈ (Submodule.span ℝ (Set.range v)).topologicalClosure := fun i =>
    Submodule.le_topologicalClosure _ (Submodule.subset_span (Set.mem_range_self i))
  have hbcoe : ∀ i : ι, ((hv.hilbertBasisTopologicalClosure i :
      (Submodule.span ℝ (Set.range v)).topologicalClosure) : E) = v i := by
    intro i
    simp only [Orthonormal.hilbertBasisTopologicalClosure]
    rw [HilbertBasis.coe_mkOfOrthogonalEqBot]
    rfl
  have hsum := (hv.hilbertBasisTopologicalClosure.hasSum_repr
      ⟨_, (Submodule.span ℝ (Set.range v)).topologicalClosure.starProjection_apply_mem x⟩).mapL
    (Submodule.span ℝ (Set.range v)).topologicalClosure.subtypeL
  refine hsum.congr_fun fun i => ?_
  rw [ContinuousLinearMap.map_smul, Submodule.subtypeL_apply, hbcoe i,
    HilbertBasis.repr_apply_apply, Submodule.coe_inner, hbcoe i,
    ← Submodule.inner_starProjection_left_eq_right,
    Submodule.starProjection_eq_self_iff.mpr (hmem i)]

end HilbertBasis

/-! ### The Haar scaling functions -/

namespace Haar

open MeasureTheory Real

/-- The dyadic interval `[k 2 ^ (-j), (k + 1) 2 ^ (-j))`, the support of the Haar scaling function
`Haar.scalingFun j k`. -/
def dyadic (j k : ℤ) : Set ℝ := Set.Ico ((k : ℝ) * 2 ^ (-j)) (((k : ℝ) + 1) * 2 ^ (-j))

theorem measurableSet_dyadic (j k : ℤ) : MeasurableSet (dyadic j k) := measurableSet_Ico

@[simp]
theorem volume_dyadic (j k : ℤ) : volume (dyadic j k) = ENNReal.ofReal ((2 : ℝ) ^ (-j)) := by
  rw [dyadic, Real.volume_Ico]
  congr 1
  ring

theorem volume_dyadic_ne_top (j k : ℤ) : volume (dyadic j k) ≠ ⊤ := by
  rw [volume_dyadic]
  exact ENNReal.ofReal_ne_top

/-- Distinct dyadic intervals of the same level are disjoint. -/
theorem dyadic_inter_dyadic (j : ℤ) {k l : ℤ} (h : k ≠ l) : dyadic j k ∩ dyadic j l = ∅ := by
  have ht : (0 : ℝ) < 2 ^ (-j) := by positivity
  rw [dyadic, dyadic, Set.Ico_inter_Ico]
  refine Set.Ico_eq_empty (not_lt.mpr ?_)
  rcases lt_or_gt_of_ne h with hkl | hkl
  · have hkl' : ((k : ℝ) + 1) ≤ (l : ℝ) := by exact_mod_cast (by omega : k + 1 ≤ l)
    exact le_trans (min_le_left _ _) (le_trans (by nlinarith) (le_max_right _ _))
  · have hkl' : ((l : ℝ) + 1) ≤ (k : ℝ) := by exact_mod_cast (by omega : l + 1 ≤ k)
    exact le_trans (min_le_right _ _) (le_trans (by nlinarith) (le_max_left _ _))

@[simp]
theorem dyadic_zero_zero : dyadic 0 0 = Set.Ico 0 1 := by
  simp [dyadic]

/-- The Haar scaling function `2 ^ (j / 2) φ (2 ^ j x - k)` for the unit step `φ = 1_[0,1)`: the
normalized indicator of the dyadic interval `[k 2 ^ (-j), (k + 1) 2 ^ (-j))`, as an element of
`L²(ℝ)` ([han2009theoretical], (4.4.1)). -/
def scalingFun (j k : ℤ) : Lp ℝ 2 (volume : Measure ℝ) :=
  indicatorConstLp 2 (measurableSet_dyadic j k) (volume_dyadic_ne_top j k) (√((2 : ℝ) ^ j))

/-- At level `0` and index `0` the scaling function is the unit step `φ = 1_[0,1)`. -/
theorem scalingFun_zero_zero :
    scalingFun 0 0 =
      indicatorConstLp 2 (measurableSet_dyadic 0 0) (volume_dyadic_ne_top 0 0) 1 := by
  rw [scalingFun]
  norm_num

/-- Every scaling function is a dilation of a scaling function of level `0`. -/
theorem scalingFun_eq_dilation (j k : ℤ) :
    scalingFun j k = Lp.dilationₗᵢ ((2 : ℝ) ^ j) (zpow_ne_zero j two_ne_zero) (scalingFun 0 k) := by
  have hpos : (0 : ℝ) < 2 ^ j := by positivity
  have hd0 : dyadic 0 k = Set.Ico (k : ℝ) ((k : ℝ) + 1) := by simp [dyadic]
  have hset : (fun x : ℝ => (2 : ℝ) ^ j * x) ⁻¹' dyadic 0 k = dyadic j k := by
    rw [hd0, Set.preimage_const_mul_Ico₀ _ _ hpos, dyadic]
    congr 1 <;> rw [zpow_neg, div_eq_mul_inv]
  simp only [scalingFun]
  rw [Lp.dilationₗᵢ_indicatorConstLp,
    indicatorConstLp_congr_set _ _ (measurableSet_dyadic j k) (volume_dyadic_ne_top j k) hset]
  congr 1
  rw [abs_of_pos hpos, ← Real.sqrt_eq_rpow]
  simp

/-- [han2009theoretical], Theorem 4.4.1 (1): the scaling functions of a fixed level are orthonormal
in `L²(ℝ)`. -/
theorem orthonormal_scalingFun (j : ℤ) : Orthonormal ℝ (scalingFun j) := by
  have hpos : (0 : ℝ) < 2 ^ j := by positivity
  rw [orthonormal_iff_ite]
  intro k l
  rw [scalingFun, scalingFun,
    L2.inner_indicatorConstLp_indicatorConstLp (measurableSet_dyadic j k)
      (measurableSet_dyadic j l) (volume_dyadic_ne_top j k) (volume_dyadic_ne_top j l)]
  rcases eq_or_ne k l with rfl | h
  · rw [Set.inter_self, measureReal_def, volume_dyadic,
      ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
    simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial]
    rw [Real.mul_self_sqrt hpos.le, zpow_neg, inv_mul_cancel₀ hpos.ne']
    simp
  · rw [dyadic_inter_dyadic j h]
    simp [h]

/-- `⟪s_{j,k}, s_{j,k}⟫ = 1`. -/
theorem inner_scalingFun_self (j k : ℤ) :
    inner ℝ (scalingFun j k) (scalingFun j k) = (1 : ℝ) := by
  have h := orthonormal_scalingFun j
  rw [orthonormal_iff_ite] at h
  simpa using h k k

/-- `⟪s_{j,k}, s_{j,l}⟫ = 0` for `k ≠ l`. -/
theorem inner_scalingFun_of_ne (j : ℤ) {k l : ℤ} (h : k ≠ l) :
    inner ℝ (scalingFun j k) (scalingFun j l) = (0 : ℝ) := by
  have hon := orthonormal_scalingFun j
  rw [orthonormal_iff_ite] at hon
  simpa [h] using hon k l

/-- The normalizing constant of the two-scale relation. -/
private theorem inv_sqrt_two_mul_self : (√2)⁻¹ * (√2)⁻¹ * 2 = 1 := by
  rw [← mul_inv, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-! ### The scaling spaces -/

/-- The level-`j` Haar scaling space: the closed span in `L²(ℝ)` of the scaling functions of level
`j`. [han2009theoretical] `V_j`, the set of *finite* linear combinations, is its dense subspace. -/
def V (j : ℤ) : Submodule ℝ (Lp ℝ 2 (volume : Measure ℝ)) :=
  (Submodule.span ℝ (Set.range (scalingFun j))).topologicalClosure

theorem isClosed_V (j : ℤ) : IsClosed (V j : Set (Lp ℝ 2 (volume : Measure ℝ))) :=
  Submodule.isClosed_topologicalClosure _

theorem scalingFun_mem_V (j k : ℤ) : scalingFun j k ∈ V j :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span (Set.mem_range_self k))

/-- Membership in `(V j)ᗮ` is orthogonality to every scaling function of level `j`. -/
theorem mem_orthogonal_V_iff (j : ℤ) (f : Lp ℝ 2 (volume : Measure ℝ)) :
    f ∈ (V j)ᗮ ↔ ∀ k : ℤ, inner ℝ (scalingFun j k) f = 0 := by
  refine ⟨fun h k => (Submodule.mem_orthogonal _ _).1 h _ (scalingFun_mem_V j k), fun h => ?_⟩
  simp only [V]
  rw [Submodule.orthogonal_closure]
  exact Submodule.mem_orthogonal_span_range h

/-- The scaling functions of level `j` form a Hilbert basis of the scaling space `V j`. -/
def hilbertBasis_V (j : ℤ) : HilbertBasis ℤ ℝ (V j) :=
  (orthonormal_scalingFun j).hilbertBasisTopologicalClosure

/-- The image of the closure of a subspace under a surjective linear isometry is the closure of the
image. -/
private theorem map_topologicalClosure
    (D : Lp ℝ 2 (volume : Measure ℝ) ≃ₗᵢ[ℝ] Lp ℝ 2 (volume : Measure ℝ))
    (K : Submodule ℝ (Lp ℝ 2 (volume : Measure ℝ))) :
    K.topologicalClosure.map D.toLinearEquiv.toLinearMap
      = (K.map D.toLinearEquiv.toLinearMap).topologicalClosure := by
  refine SetLike.ext' ?_
  rw [Submodule.map_coe, Submodule.topologicalClosure_coe, Submodule.topologicalClosure_coe,
    Submodule.map_coe]
  exact D.toHomeomorph.image_closure _

/-- [han2009theoretical], Theorem 4.4.1 (2), scale invariance: `V j` is the image of `V 0` under the
dilation by `2 ^ j`. -/
theorem V_eq_map_dilation (j : ℤ) :
    V j = (V 0).map
      (Lp.dilationₗᵢ ((2 : ℝ) ^ j) (zpow_ne_zero j two_ne_zero)).toLinearEquiv.toLinearMap := by
  have himg : (Lp.dilationₗᵢ ((2 : ℝ) ^ j)
      (zpow_ne_zero j two_ne_zero)).toLinearEquiv.toLinearMap ''
        Set.range (scalingFun 0) = Set.range (scalingFun j) := by
    rw [← Set.range_comp]
    exact congrArg Set.range (funext fun k => (scalingFun_eq_dilation j k).symm)
  simp only [V]
  rw [map_topologicalClosure, Submodule.map_span, himg]

/-- The two-scale relation: a scaling function of level `j` is the normalized sum of the two scaling
functions of level `j + 1` supported on its two halves. -/
theorem scalingFun_two_scale (j k : ℤ) :
    scalingFun j k = (√2)⁻¹ • (scalingFun (j + 1) (2 * k) + scalingFun (j + 1) (2 * k + 1)) := by
  have ht : (0 : ℝ) < 2 ^ (-(j + 1)) := by positivity
  have hs2 : (0 : ℝ) < √2 := Real.sqrt_pos.mpr (by norm_num)
  have hstep : (2 : ℝ) ^ (-(j + 1)) * 2 = 2 ^ (-j) := by
    rw [← zpow_add_one₀ (two_ne_zero' ℝ)]
    congr 1
    ring
  have hdisj : Disjoint (dyadic (j + 1) (2 * k)) (dyadic (j + 1) (2 * k + 1)) :=
    Set.disjoint_iff_inter_eq_empty.mpr (dyadic_inter_dyadic (j + 1) (by omega))
  have hunion : dyadic (j + 1) (2 * k) ∪ dyadic (j + 1) (2 * k + 1) = dyadic j k := by
    simp only [dyadic]
    push_cast
    rw [Set.Ico_union_Ico_eq_Ico (by nlinarith) (by nlinarith)]
    congr 1 <;> rw [← hstep] <;> ring
  simp only [scalingFun]
  rw [← indicatorConstLp_disjoint_union (measurableSet_dyadic (j + 1) (2 * k))
      (measurableSet_dyadic (j + 1) (2 * k + 1)) (volume_dyadic_ne_top (j + 1) (2 * k))
      (volume_dyadic_ne_top (j + 1) (2 * k + 1)) hdisj,
    smul_indicatorConstLp,
    indicatorConstLp_congr_set _ _ (measurableSet_dyadic j k) (volume_dyadic_ne_top j k) hunion]
  congr 1
  rw [zpow_add_one₀ (two_ne_zero' ℝ), Real.sqrt_mul (by positivity)]
  field_simp

/-- [han2009theoretical], Theorem 4.4.1 (3), nesting. -/
theorem V_le_V_succ (j : ℤ) : V j ≤ V (j + 1) := by
  refine Submodule.topologicalClosure_minimal _ ?_ (isClosed_V (j + 1))
  rw [Submodule.span_le]
  rintro _ ⟨k, rfl⟩
  rw [scalingFun_two_scale]
  exact Submodule.smul_mem _ _
    (Submodule.add_mem _ (scalingFun_mem_V _ _) (scalingFun_mem_V _ _))

/-! ### Dyadic intervals and the floor function -/

private theorem mul_zpow_neg_le_iff (j : ℤ) (a x : ℝ) : a * 2 ^ (-j) ≤ x ↔ a ≤ 2 ^ j * x := by
  have h2 : (0 : ℝ) < 2 ^ j := by positivity
  rw [zpow_neg, ← div_eq_mul_inv, div_le_iff₀ h2, mul_comm x ((2 : ℝ) ^ j)]

private theorem lt_mul_zpow_neg_iff (j : ℤ) (a x : ℝ) : x < a * 2 ^ (-j) ↔ 2 ^ j * x < a := by
  have h2 : (0 : ℝ) < 2 ^ j := by positivity
  rw [zpow_neg, ← div_eq_mul_inv, lt_div_iff₀ h2, mul_comm x ((2 : ℝ) ^ j)]

private theorem le_mul_zpow_neg_iff (j : ℤ) (a x : ℝ) : x ≤ a * 2 ^ (-j) ↔ 2 ^ j * x ≤ a := by
  have h2 : (0 : ℝ) < 2 ^ j := by positivity
  rw [zpow_neg, ← div_eq_mul_inv, le_div_iff₀ h2, mul_comm x ((2 : ℝ) ^ j)]

private theorem mem_dyadic_iff (j k : ℤ) (x : ℝ) :
    x ∈ dyadic j k ↔ (k : ℝ) ≤ 2 ^ j * x ∧ 2 ^ j * x < (k : ℝ) + 1 := by
  rw [dyadic, Set.mem_Ico, mul_zpow_neg_le_iff, lt_mul_zpow_neg_iff]

private theorem mem_dyadic_iff_floor (j k : ℤ) (x : ℝ) :
    x ∈ dyadic j k ↔ k = ⌊(2 : ℝ) ^ j * x⌋ := by
  rw [mem_dyadic_iff, eq_comm, Int.floor_eq_iff]

/-! ### Finite sums of indicators in `L²` -/

private theorem coeFn_sum_indicatorConstLp (j : ℤ) (s : Finset ℤ) (c : ℤ → ℝ) :
    ((∑ k ∈ s, indicatorConstLp 2 (measurableSet_dyadic j k) (volume_dyadic_ne_top j k) (c k) :
        Lp ℝ 2 (volume : Measure ℝ)) : ℝ → ℝ)
      =ᵐ[volume] fun x => ∑ k ∈ s, (dyadic j k).indicator (fun _ => c k) x := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.sum_empty]
    exact Lp.coeFn_zero ℝ 2 (volume : Measure ℝ)
  · intro a t ha ih
    rw [Finset.sum_insert ha]
    filter_upwards [Lp.coeFn_add
        (indicatorConstLp 2 (measurableSet_dyadic j a) (volume_dyadic_ne_top j a) (c a))
        (∑ k ∈ t, indicatorConstLp 2 (measurableSet_dyadic j k) (volume_dyadic_ne_top j k) (c k)),
      ih, indicatorConstLp_coeFn (p := 2) (hs := measurableSet_dyadic j a)
        (hμs := volume_dyadic_ne_top j a) (c := c a)] with x h1 h2 h3
    rw [h1, Pi.add_apply, h2, h3, Finset.sum_insert ha]

/-! ### The dyadic step approximation -/

/-- The level-`j` dyadic step function of `g`, cut off outside the window `[-M 2 ^ (-j), M 2 ^
(-j))`. -/
private def stepFun (g : ℝ → ℝ) (j M : ℤ) : ℝ → ℝ := fun x =>
  ∑ k ∈ Finset.Ico (-M) M, (dyadic j k).indicator (fun _ => g ((k : ℝ) * 2 ^ (-j))) x

private theorem stepFun_apply (g : ℝ → ℝ) (j M : ℤ) (x : ℝ) :
    stepFun g j M x =
      ∑ k ∈ Finset.Ico (-M) M, (dyadic j k).indicator (fun _ => g ((k : ℝ) * 2 ^ (-j))) x :=
  rfl

/-- The step function of `g`, as an element of `L²(ℝ)` lying in `V j`. -/
private def stepLp (g : ℝ → ℝ) (j M : ℤ) : Lp ℝ 2 (volume : Measure ℝ) :=
  ∑ k ∈ Finset.Ico (-M) M, (g ((k : ℝ) * 2 ^ (-j)) * √((2 : ℝ) ^ (-j))) • scalingFun j k

private theorem stepLp_mem_V (g : ℝ → ℝ) (j M : ℤ) : stepLp g j M ∈ V j :=
  Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (scalingFun_mem_V j k)

private theorem stepLp_eq_sum (g : ℝ → ℝ) (j M : ℤ) :
    stepLp g j M = ∑ k ∈ Finset.Ico (-M) M,
      indicatorConstLp 2 (measurableSet_dyadic j k) (volume_dyadic_ne_top j k)
        (g ((k : ℝ) * 2 ^ (-j))) := by
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [scalingFun, smul_indicatorConstLp]
  congr 1
  rw [mul_assoc, ← Real.sqrt_mul (by positivity), ← zpow_add₀ (two_ne_zero' ℝ)]
  simp

private theorem coeFn_stepLp (g : ℝ → ℝ) (j M : ℤ) :
    (stepLp g j M : ℝ → ℝ) =ᵐ[volume] stepFun g j M := by
  rw [stepLp_eq_sum]
  exact coeFn_sum_indicatorConstLp j _ _

/-- A continuous function with compact support is approximated in `L²` by its dyadic step functions.
-/
private theorem exists_step_approx (g : ℝ → ℝ) (hgc : Continuous g) (hgs : HasCompactSupport g)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ j M : ℤ, eLpNorm (g - stepFun g j M) 2 volume ≤ ENNReal.ofReal ε := by
  obtain ⟨R, hR⟩ := hgs.isCompact.isBounded.subset_closedBall (0 : ℝ)
  obtain ⟨R₀, hR₀0, hzero⟩ :
      ∃ R₀ : ℝ, 0 ≤ R₀ ∧ ∀ x : ℝ, R₀ < |x| → g x = 0 := by
    refine ⟨max R 0, le_max_right _ _, fun x hx => ?_⟩
    refine image_eq_zero_of_notMem_tsupport fun hmem => ?_
    have h := hR hmem
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at h
    exact absurd (h.trans (le_max_left _ _)) (not_le.2 hx)
  -- the fixed window and the target modulus of continuity
  have hCpos : (0 : ℝ) < √(2 * (R₀ + 2)) := Real.sqrt_pos.mpr (by linarith)
  have hδ : (0 : ℝ) < ε / √(2 * (R₀ + 2)) := div_pos hε hCpos
  obtain ⟨η, hη, huc⟩ := Metric.uniformContinuous_iff.mp
    (hgs.uniformContinuous_of_continuous hgc) _ hδ
  obtain ⟨j, hjlt, hjge⟩ : ∃ j : ℤ, (2 : ℝ) ^ (-j) < η ∧ (1 : ℝ) ≤ 2 ^ j := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hη (by norm_num : (1 / 2 : ℝ) < 1)
    refine ⟨(n : ℤ), ?_, ?_⟩
    · have hrw : (2 : ℝ) ^ (-(n : ℤ)) = (1 / 2 : ℝ) ^ n := by
        rw [zpow_neg, zpow_natCast, one_div, inv_pow]
      rw [hrw]; exact hn
    · rw [zpow_natCast]; exact one_le_pow₀ (by norm_num)
  have hj0 : (0 : ℝ) < 2 ^ (-j) := by positivity
  obtain ⟨M, hMlow, hMhigh⟩ :
      ∃ M : ℤ, R₀ + 1 ≤ (M : ℝ) * 2 ^ (-j) ∧ (M : ℝ) * 2 ^ (-j) ≤ R₀ + 2 := by
    refine ⟨⌈(2 : ℝ) ^ j * (R₀ + 1)⌉, (le_mul_zpow_neg_iff j _ _).mpr (Int.le_ceil _), ?_⟩
    refine (mul_zpow_neg_le_iff j _ _).mpr ?_
    have h := Int.ceil_lt_add_one ((2 : ℝ) ^ j * (R₀ + 1))
    have h2 : (2 : ℝ) ^ j * (R₀ + 2) = 2 ^ j * (R₀ + 1) + 2 ^ j := by ring
    linarith
  refine ⟨j, M, ?_⟩
  -- the pointwise bound
  have hkey : ∀ x : ℝ, ‖(g - stepFun g j M) x‖ ≤
      ‖(Set.Ico (-((M : ℝ) * 2 ^ (-j))) ((M : ℝ) * 2 ^ (-j))).indicator
        (fun _ => ε / √(2 * (R₀ + 2))) x‖ := by
    intro x
    by_cases hx : x ∈ Set.Ico (-((M : ℝ) * 2 ^ (-j))) ((M : ℝ) * 2 ^ (-j))
    · rw [Set.indicator_of_mem hx]
      have hk : ⌊(2 : ℝ) ^ j * x⌋ ∈ Finset.Ico (-M) M := by
        rw [Finset.mem_Ico]
        refine ⟨?_, ?_⟩
        · rw [Int.le_floor]
          push_cast
          rw [← mul_zpow_neg_le_iff j (-(M : ℝ)) x, neg_mul]
          exact hx.1
        · rw [Int.floor_lt]
          exact (lt_mul_zpow_neg_iff j (M : ℝ) x).mp hx.2
      have hstep : stepFun g j M x = g ((⌊(2 : ℝ) ^ j * x⌋ : ℝ) * 2 ^ (-j)) := by
        have hsum := Finset.sum_eq_single_of_mem (f := fun k : ℤ =>
            (dyadic j k).indicator (fun _ => g ((k : ℝ) * 2 ^ (-j))) x)
          ⌊(2 : ℝ) ^ j * x⌋ hk (fun b _ hb =>
            Set.indicator_of_notMem (fun hmem => hb ((mem_dyadic_iff_floor j b x).mp hmem)) _)
        rw [stepFun_apply, hsum, Set.indicator_of_mem ((mem_dyadic_iff_floor j _ x).mpr rfl)]
      have hxd : x ∈ dyadic j ⌊(2 : ℝ) ^ j * x⌋ := (mem_dyadic_iff_floor j _ x).mpr rfl
      rw [dyadic, Set.mem_Ico] at hxd
      have hexp : ((⌊(2 : ℝ) ^ j * x⌋ : ℝ) + 1) * 2 ^ (-j)
          = (⌊(2 : ℝ) ^ j * x⌋ : ℝ) * 2 ^ (-j) + 2 ^ (-j) := by ring
      have hdist : dist x ((⌊(2 : ℝ) ^ j * x⌋ : ℝ) * 2 ^ (-j)) < η := by
        rw [Real.dist_eq, abs_of_nonneg (by linarith [hxd.1])]
        have h2 := hxd.2
        rw [hexp] at h2
        linarith
      have hgd := huc hdist
      rw [Real.dist_eq] at hgd
      rw [Pi.sub_apply, hstep, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hδ.le]
      linarith
    · rw [Set.indicator_of_notMem hx]
      have hgx : g x = 0 := by
        refine hzero x ?_
        rcases lt_or_ge x (-((M : ℝ) * 2 ^ (-j))) with h | h
        · rw [abs_of_neg (by linarith)]
          linarith
        · have hb2 : (M : ℝ) * 2 ^ (-j) ≤ x := by
            by_contra hcon
            exact hx ⟨h, not_le.mp hcon⟩
          rw [abs_of_nonneg (by linarith)]
          linarith
      have hstep0 : stepFun g j M x = 0 := by
        rw [stepFun_apply]
        refine Finset.sum_eq_zero fun k hk => ?_
        refine Set.indicator_of_notMem (fun hmem => hx ?_) _
        rw [Finset.mem_Ico] at hk
        rw [dyadic, Set.mem_Ico] at hmem
        have hk1 : (-(M : ℝ)) ≤ (k : ℝ) := by exact_mod_cast hk.1
        have hk2 : ((k : ℝ) + 1) ≤ (M : ℝ) := by exact_mod_cast (by omega : k + 1 ≤ M)
        have h1 : (-(M : ℝ)) * 2 ^ (-j) ≤ (k : ℝ) * 2 ^ (-j) :=
          mul_le_mul_of_nonneg_right hk1 hj0.le
        have h2 : ((k : ℝ) + 1) * 2 ^ (-j) ≤ (M : ℝ) * 2 ^ (-j) :=
          mul_le_mul_of_nonneg_right hk2 hj0.le
        rw [neg_mul] at h1
        exact ⟨le_trans h1 hmem.1, lt_of_lt_of_le hmem.2 h2⟩
      rw [Pi.sub_apply, hgx, hstep0]
      simp
  -- from the pointwise bound to the `L²` bound
  have hvol : volume (Set.Ico (-((M : ℝ) * 2 ^ (-j))) ((M : ℝ) * 2 ^ (-j)))
      ≤ ENNReal.ofReal (2 * (R₀ + 2)) := by
    rw [Real.volume_Ico]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  calc eLpNorm (g - stepFun g j M) 2 volume
      ≤ eLpNorm ((Set.Ico (-((M : ℝ) * 2 ^ (-j))) ((M : ℝ) * 2 ^ (-j))).indicator
          (fun _ => ε / √(2 * (R₀ + 2)))) 2 volume := eLpNorm_mono hkey
    _ ≤ ‖ε / √(2 * (R₀ + 2))‖ₑ
        * volume (Set.Ico (-((M : ℝ) * 2 ^ (-j))) ((M : ℝ) * 2 ^ (-j)))
          ^ (1 / (2 : ℝ≥0∞).toReal) := eLpNorm_indicator_const_le _ _
    _ ≤ ENNReal.ofReal (ε / √(2 * (R₀ + 2)))
        * (ENNReal.ofReal (2 * (R₀ + 2))) ^ (1 / (2 : ℝ≥0∞).toReal) := by
        gcongr
        · exact le_of_eq (Real.enorm_eq_ofReal hδ.le)
    _ = ENNReal.ofReal ε := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
          ← ENNReal.ofReal_mul hδ.le]
        congr 1
        rw [show (1 / (2 : ℝ≥0∞).toReal) = (1 / 2 : ℝ) by norm_num,
          ← Real.sqrt_eq_rpow]
        exact div_mul_cancel₀ ε hCpos.ne'

/-! ### Density -/

/-- [han2009theoretical], Theorem 4.4.1 (4), density: the union of the scaling spaces is dense in
`L²(ℝ)`. -/
theorem topologicalClosure_iSup_V : (⨆ j : ℤ, V j).topologicalClosure = ⊤ := by
  refine Submodule.dense_iff_topologicalClosure_eq_top.mp fun f => ?_
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨g, hgs, hgapprox, hgc, hgmem⟩ :=
    (Lp.memLp f).exists_hasCompactSupport_eLpNorm_sub_le (p := 2) (by norm_num)
      (ε := ENNReal.ofReal (ε / 3)) (ENNReal.ofReal_pos.mpr (by linarith)).ne'
  obtain ⟨j, M, hstep⟩ := exists_step_approx g hgc hgs (ε := ε / 3) (by linarith)
  refine ⟨stepLp g j M, ?_, ?_⟩
  · exact le_iSup V j (stepLp_mem_V g j M)
  · have h1 : ((f - hgmem.toLp g : Lp ℝ 2 (volume : Measure ℝ)) : ℝ → ℝ)
        =ᵐ[volume] (f : ℝ → ℝ) - g := by
      filter_upwards [Lp.coeFn_sub f (hgmem.toLp g), hgmem.coeFn_toLp] with x hx hx2
      rw [hx, Pi.sub_apply, Pi.sub_apply, hx2]
    have h2 : ((hgmem.toLp g - stepLp g j M : Lp ℝ 2 (volume : Measure ℝ)) : ℝ → ℝ)
        =ᵐ[volume] g - stepFun g j M := by
      filter_upwards [Lp.coeFn_sub (hgmem.toLp g) (stepLp g j M), hgmem.coeFn_toLp,
        coeFn_stepLp g j M] with x hx hx2 hx3
      rw [hx, Pi.sub_apply, Pi.sub_apply, hx2, hx3]
    have hn1 : ‖f - hgmem.toLp g‖ ≤ ε / 3 := by
      rw [Lp.norm_def, eLpNorm_congr_ae h1]
      have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hgapprox
      rwa [ENNReal.toReal_ofReal (by linarith)] at h
    have hn2 : ‖hgmem.toLp g - stepLp g j M‖ ≤ ε / 3 := by
      rw [Lp.norm_def, eLpNorm_congr_ae h2]
      have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hstep
      rwa [ENNReal.toReal_ofReal (by linarith)] at h
    have hsplit : f - stepLp g j M
        = (f - hgmem.toLp g) + (hgmem.toLp g - stepLp g j M) := by abel
    rw [dist_eq_norm, hsplit]
    have := norm_add_le (f - hgmem.toLp g) (hgmem.toLp g - stepLp g j M)
    linarith

/-! ### Separation -/

/-- A vector orthogonal to every level-`j` scaling function is orthogonal to `V j`. -/
private theorem inner_eq_zero_of_mem_V {j : ℤ} {u v : Lp ℝ 2 (volume : Measure ℝ)}
    (hu : u ∈ V j) (h : ∀ k : ℤ, inner ℝ (scalingFun j k) v = (0 : ℝ)) :
    inner ℝ u v = (0 : ℝ) :=
  (Submodule.mem_orthogonal _ _).1 ((mem_orthogonal_V_iff j v).2 h) u hu

/-- The scale factor relating two levels. -/
private theorem sqrt_zpow_mul (j i : ℤ) :
    (2 : ℝ) ^ (-i) * (√((2 : ℝ) ^ j) * √((2 : ℝ) ^ i)) = √((2 : ℝ) ^ (j - i)) := by
  have hi : (0 : ℝ) < 2 ^ i := by positivity
  have hji : (0 : ℝ) ≤ (2 : ℝ) ^ (j - i) := by positivity
  have key : √((2 : ℝ) ^ (j - i)) * √((2 : ℝ) ^ i) = √((2 : ℝ) ^ j) := by
    rw [← Real.sqrt_mul hji, ← zpow_add₀ (two_ne_zero' ℝ)]
    congr 2
    ring
  have hsi : √((2 : ℝ) ^ i) * √((2 : ℝ) ^ i) = 2 ^ i := Real.mul_self_sqrt hi.le
  calc (2 : ℝ) ^ (-i) * (√((2 : ℝ) ^ j) * √((2 : ℝ) ^ i))
      = 2 ^ (-i) * ((√((2 : ℝ) ^ (j - i)) * √((2 : ℝ) ^ i)) * √((2 : ℝ) ^ i)) := by rw [key]
    _ = 2 ^ (-i) * (√((2 : ℝ) ^ (j - i)) * (√((2 : ℝ) ^ i) * √((2 : ℝ) ^ i))) := by ring
    _ = ((2 : ℝ) ^ (-i) * 2 ^ i) * √((2 : ℝ) ^ (j - i)) := by rw [hsi]; ring
    _ = √((2 : ℝ) ^ (j - i)) := by rw [← zpow_add₀ (two_ne_zero' ℝ)]; simp

/-- For `j ≤ i` each level-`i` dyadic interval sits inside a level-`j` one. -/
private theorem exists_dyadic_subset {j i : ℤ} (hji : j ≤ i) (k : ℤ) :
    ∃ l : ℤ, dyadic i k ⊆ dyadic j l := by
  have hmi : (((i - j).toNat : ℤ)) = i - j := Int.toNat_of_nonneg (by omega)
  set m : ℕ := (i - j).toNat
  have hBA : (2 : ℝ) ^ (-j) = (2 : ℝ) ^ m * 2 ^ (-i) := by
    rw [← zpow_natCast (2 : ℝ) m, hmi, ← zpow_add₀ (two_ne_zero' ℝ)]
    congr 1
    omega
  have hpos : (0 : ℤ) < 2 ^ m := pow_pos (by norm_num) m
  have hdiv := Int.mul_ediv_add_emod k (2 ^ m)
  have hmod0 : 0 ≤ k % 2 ^ m := Int.emod_nonneg k (by positivity)
  have hmodlt := Int.emod_lt_of_pos k hpos
  have h1 : 2 ^ m * (k / 2 ^ m) ≤ k := by linarith
  have hexp : (2 : ℤ) ^ m * (k / 2 ^ m + 1) = 2 ^ m * (k / 2 ^ m) + 2 ^ m := by ring
  have h2 : k + 1 ≤ 2 ^ m * (k / 2 ^ m + 1) := by rw [hexp]; linarith
  refine ⟨k / 2 ^ m, ?_⟩
  have hA : (0 : ℝ) < 2 ^ (-i) := by positivity
  intro x hx
  rw [dyadic, Set.mem_Ico] at hx ⊢
  have hc1 : ((k / 2 ^ m : ℤ) : ℝ) * 2 ^ (-j) ≤ (k : ℝ) * 2 ^ (-i) := by
    rw [hBA, ← mul_assoc]
    have hcast : ((k / 2 ^ m : ℤ) : ℝ) * 2 ^ m = ((2 ^ m * (k / 2 ^ m) : ℤ) : ℝ) := by
      push_cast; ring
    rw [hcast]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast h1) hA.le
  have hc2 : ((k : ℝ) + 1) * 2 ^ (-i) ≤ (((k / 2 ^ m : ℤ) : ℝ) + 1) * 2 ^ (-j) := by
    rw [hBA, ← mul_assoc]
    have hcast : (((k / 2 ^ m : ℤ) : ℝ) + 1) * 2 ^ m = ((2 ^ m * (k / 2 ^ m + 1) : ℤ) : ℝ) := by
      push_cast; ring
    rw [hcast]
    refine mul_le_mul_of_nonneg_right ?_ hA.le
    exact_mod_cast h2
  exact ⟨le_trans hc1 hx.1, lt_of_lt_of_le hx.2 hc2⟩

private theorem inner_scalingFun_cross {j i l k : ℤ} (hsub : dyadic i k ⊆ dyadic j l) :
    inner ℝ (scalingFun j l) (scalingFun i k) = √((2 : ℝ) ^ (j - i)) := by
  rw [scalingFun, scalingFun,
    L2.inner_indicatorConstLp_indicatorConstLp (measurableSet_dyadic j l)
      (measurableSet_dyadic i k) (volume_dyadic_ne_top j l) (volume_dyadic_ne_top i k),
    Set.inter_eq_right.mpr hsub, measureReal_def, volume_dyadic,
    ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
  simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial]
  rw [← sqrt_zpow_mul j i]
  ring

private theorem inner_scalingFun_cross_zero {j i l k m : ℤ} (hsub : dyadic i k ⊆ dyadic j l)
    (hm : m ≠ l) : inner ℝ (scalingFun j m) (scalingFun i k) = (0 : ℝ) := by
  have hempty : dyadic j m ∩ dyadic i k = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro x ⟨hx1, hx2⟩
    have hx3 : x ∈ dyadic j m ∩ dyadic j l := ⟨hx1, hsub hx2⟩
    rw [dyadic_inter_dyadic j hm] at hx3
    exact hx3
  rw [scalingFun, scalingFun,
    L2.inner_indicatorConstLp_indicatorConstLp (measurableSet_dyadic j m)
      (measurableSet_dyadic i k) (volume_dyadic_ne_top j m) (volume_dyadic_ne_top i k),
    hempty]
  simp

/-- The level-`i` scaling coefficients of an element of `V j`, `j ≤ i`, are controlled by `2 ^ ((j -
i) / 2)`. -/
private theorem abs_inner_scalingFun_le {j i : ℤ} (hji : j ≤ i) (k : ℤ)
    {f : Lp ℝ 2 (volume : Measure ℝ)} (hf : f ∈ V j) :
    |inner ℝ (scalingFun i k) f| ≤ √((2 : ℝ) ^ (j - i)) * ‖f‖ := by
  obtain ⟨l, hsub⟩ := exists_dyadic_subset hji k
  set c : ℝ := √((2 : ℝ) ^ (j - i))
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  have hperp : ∀ m : ℤ,
      inner ℝ (scalingFun j m) (scalingFun i k - c • scalingFun j l) = (0 : ℝ) := by
    intro m
    rw [inner_sub_right, real_inner_smul_right]
    rcases eq_or_ne m l with rfl | hm
    · rw [inner_scalingFun_cross hsub, inner_scalingFun_self]
      ring
    · rw [inner_scalingFun_cross_zero hsub hm, inner_scalingFun_of_ne j hm]
      ring
  have hzero := inner_eq_zero_of_mem_V hf hperp
  rw [real_inner_comm] at hzero
  rw [inner_sub_left, real_inner_smul_left, sub_eq_zero] at hzero
  rw [hzero, abs_mul, abs_of_nonneg hc0]
  refine mul_le_mul_of_nonneg_left ?_ hc0
  have hnorm : ‖scalingFun j l‖ = 1 := (orthonormal_scalingFun j).1 l
  have := abs_real_inner_le_norm (scalingFun j l) f
  rwa [hnorm, one_mul] at this

private theorem inner_scalingFun_eq_zero_of_mem_iInf {f : Lp ℝ 2 (volume : Measure ℝ)}
    (hf : ∀ j : ℤ, f ∈ V j) (i k : ℤ) : inner ℝ (scalingFun i k) f = (0 : ℝ) := by
  by_contra hne
  have hpos : 0 < |inner ℝ (scalingFun i k) f| := abs_pos.mpr hne
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one
    (div_pos hpos (by positivity : (0 : ℝ) < ‖f‖ + 1)) (by norm_num : (1 / 2 : ℝ) < 1)
  have hji : i - 2 * (n : ℤ) ≤ i := by omega
  have hsq : √((2 : ℝ) ^ (i - 2 * (n : ℤ) - i)) = (1 / 2 : ℝ) ^ n := by
    have hrw : i - 2 * (n : ℤ) - i = (-(n : ℤ)) + (-(n : ℤ)) := by ring
    rw [hrw, zpow_add₀ (two_ne_zero' ℝ), Real.sqrt_mul_self (by positivity),
      zpow_neg, zpow_natCast, one_div, inv_pow]
  have hb := abs_inner_scalingFun_le hji k (hf (i - 2 * (n : ℤ)))
  rw [hsq] at hb
  have hle : (1 / 2 : ℝ) ^ n * ‖f‖ ≤ (1 / 2 : ℝ) ^ n * (‖f‖ + 1) := by
    have := pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) n
    nlinarith [norm_nonneg f]
  have hlt : (1 / 2 : ℝ) ^ n * (‖f‖ + 1) < |inner ℝ (scalingFun i k) f| := by
    have h1 := mul_lt_mul_of_pos_right hn (by positivity : (0 : ℝ) < ‖f‖ + 1)
    rwa [div_mul_cancel₀ _ (by positivity : (‖f‖ + 1) ≠ 0)] at h1
  linarith

/-- [han2009theoretical], Theorem 4.4.1 (5), separation: the scaling spaces intersect in `0`. -/
theorem iInf_V_eq_bot : (⨅ j : ℤ, V j) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro f hf
  have hfV : ∀ j : ℤ, f ∈ V j := fun j => (Submodule.mem_iInf _).mp hf j
  have hzero := inner_scalingFun_eq_zero_of_mem_iInf hfV
  have horth : ∀ i : ℤ, V i ≤ (Submodule.span ℝ {f})ᗮ := by
    intro i u hu
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, real_inner_comm]
    exact inner_eq_zero_of_mem_V hu (hzero i)
  have hclose : (⨆ i : ℤ, V i).topologicalClosure ≤ (Submodule.span ℝ {f})ᗮ :=
    Submodule.topologicalClosure_minimal _ (iSup_le horth) (Submodule.isClosed_orthogonal _)
  rw [topologicalClosure_iSup_V] at hclose
  have hfmem : f ∈ (Submodule.span ℝ {f})ᗮ := hclose Submodule.mem_top
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at hfmem
  exact inner_self_eq_zero.mp hfmem

/-! ### The wavelet functions and wavelet spaces -/

/-- The Haar wavelet `2 ^ (j / 2) ψ (2 ^ j x - k)` for `ψ = φ (2 ·) - φ (2 · - 1)`: the difference
of the two level-`(j + 1)` scaling functions supported on the halves of the dyadic interval `[k 2 ^
(-j), (k + 1) 2 ^ (-j))`, normalized. [han2009theoretical], (4.4.2). -/
def waveletFun (j k : ℤ) : Lp ℝ 2 (volume : Measure ℝ) :=
  (√2)⁻¹ • (scalingFun (j + 1) (2 * k) - scalingFun (j + 1) (2 * k + 1))

theorem waveletFun_eq (j k : ℤ) :
    waveletFun j k = (√2)⁻¹ • (scalingFun (j + 1) (2 * k) - scalingFun (j + 1) (2 * k + 1)) :=
  rfl

/-- The Haar wavelet in closed form: it is `√(2 ^ j)` on the left half of the dyadic interval `[k 2
^ (-j), (k + 1) 2 ^ (-j))` and `-√(2 ^ j)` on the right half, which is `2 ^ (j / 2) ψ (2 ^ j x - k)`
for `ψ = 1_[0,1/2) - 1_[1/2,1)`. -/
theorem waveletFun_eq_sub_indicator (j k : ℤ) :
    waveletFun j k =
      indicatorConstLp 2 (measurableSet_dyadic (j + 1) (2 * k))
          (volume_dyadic_ne_top (j + 1) (2 * k)) (√((2 : ℝ) ^ j)) -
        indicatorConstLp 2 (measurableSet_dyadic (j + 1) (2 * k + 1))
          (volume_dyadic_ne_top (j + 1) (2 * k + 1)) (√((2 : ℝ) ^ j)) := by
  have hs2 : (0 : ℝ) < √2 := Real.sqrt_pos.mpr (by norm_num)
  have hconst : (√2)⁻¹ * √((2 : ℝ) ^ (j + 1)) = √((2 : ℝ) ^ j) := by
    rw [zpow_add_one₀ (two_ne_zero' ℝ), Real.sqrt_mul (by positivity)]
    field_simp
  rw [waveletFun, smul_sub]
  simp only [scalingFun, smul_indicatorConstLp, hconst]

/-- The wavelets of a fixed level are orthonormal. -/
theorem orthonormal_waveletFun (j : ℤ) : Orthonormal ℝ (waveletFun j) := by
  rw [orthonormal_iff_ite]
  intro k l
  simp only [waveletFun, real_inner_smul_left, real_inner_smul_right, inner_sub_left,
    inner_sub_right]
  rcases eq_or_ne k l with rfl | h
  · rw [inner_scalingFun_self, inner_scalingFun_self,
      inner_scalingFun_of_ne (j + 1) (by omega : 2 * k ≠ 2 * k + 1),
      inner_scalingFun_of_ne (j + 1) (by omega : 2 * k + 1 ≠ 2 * k),
      show (if k = k then (1 : ℝ) else 0) = 1 from by simp]
    linear_combination inv_sqrt_two_mul_self
  · rw [inner_scalingFun_of_ne (j + 1) (by omega : 2 * k ≠ 2 * l),
      inner_scalingFun_of_ne (j + 1) (by omega : 2 * k ≠ 2 * l + 1),
      inner_scalingFun_of_ne (j + 1) (by omega : 2 * k + 1 ≠ 2 * l),
      inner_scalingFun_of_ne (j + 1) (by omega : 2 * k + 1 ≠ 2 * l + 1),
      show (if k = l then (1 : ℝ) else 0) = 0 from by simp [h]]
    ring

/-- The level-`j` Haar wavelet space: the closed span in `L²(ℝ)` of the wavelets of level `j`. -/
def W (j : ℤ) : Submodule ℝ (Lp ℝ 2 (volume : Measure ℝ)) :=
  (Submodule.span ℝ (Set.range (waveletFun j))).topologicalClosure

theorem waveletFun_mem_W (j k : ℤ) : waveletFun j k ∈ W j :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span (Set.mem_range_self k))

/-- The wavelets of level `j` form a Hilbert basis of the wavelet space `W j`. -/
def hilbertBasis_W (j : ℤ) : HilbertBasis ℤ ℝ (W j) :=
  (orthonormal_waveletFun j).hilbertBasisTopologicalClosure

/-- The level-`(j + 1)` scaling functions in terms of the level-`j` scaling function and wavelet. -/
theorem scalingFun_succ_eq (j k : ℤ) :
    scalingFun (j + 1) (2 * k) = (√2)⁻¹ • (scalingFun j k + waveletFun j k) ∧
      scalingFun (j + 1) (2 * k + 1) = (√2)⁻¹ • (scalingFun j k - waveletFun j k) := by
  have hone : (√2)⁻¹ * ((√2)⁻¹ * 2) = 1 := by linear_combination inv_sqrt_two_mul_self
  have key : ∀ a b : Lp ℝ 2 (volume : Measure ℝ),
      (√2)⁻¹ • ((√2)⁻¹ • (a + b) + (√2)⁻¹ • (a - b)) = a ∧
        (√2)⁻¹ • ((√2)⁻¹ • (a + b) - (√2)⁻¹ • (a - b)) = b := by
    intro a b
    constructor
    · rw [show (√2)⁻¹ • (a + b) + (√2)⁻¹ • (a - b) = ((√2)⁻¹ * 2) • a by module, smul_smul,
        hone, one_smul]
    · rw [show (√2)⁻¹ • (a + b) - (√2)⁻¹ • (a - b) = ((√2)⁻¹ * 2) • b by module, smul_smul,
        hone, one_smul]
  refine ⟨?_, ?_⟩
  · rw [waveletFun, scalingFun_two_scale j k]
    exact (key _ _).1.symm
  · rw [waveletFun, scalingFun_two_scale j k]
    exact (key _ _).2.symm

theorem isClosed_W (j : ℤ) : IsClosed (W j : Set (Lp ℝ 2 (volume : Measure ℝ))) :=
  Submodule.isClosed_topologicalClosure _

instance (j : ℤ) : CompleteSpace (V j) := (isClosed_V j).completeSpace_coe

instance (j : ℤ) : CompleteSpace (W j) := (isClosed_W j).completeSpace_coe

/-- A scaling function and a wavelet of the same level are orthogonal. -/
theorem inner_scalingFun_waveletFun (j k l : ℤ) :
    inner ℝ (scalingFun j k) (waveletFun j l) = 0 := by
  simp only [waveletFun, scalingFun_two_scale j k, real_inner_smul_left, real_inner_smul_right,
    inner_add_left, inner_sub_right]
  rcases eq_or_ne k l with rfl | h
  · rw [inner_scalingFun_self, inner_scalingFun_self,
      inner_scalingFun_of_ne (j + 1) (by omega : 2 * k ≠ 2 * k + 1),
      inner_scalingFun_of_ne (j + 1) (by omega : 2 * k + 1 ≠ 2 * k)]
    ring
  · rw [inner_scalingFun_of_ne (j + 1) (by omega : 2 * k ≠ 2 * l),
      inner_scalingFun_of_ne (j + 1) (by omega : 2 * k ≠ 2 * l + 1),
      inner_scalingFun_of_ne (j + 1) (by omega : 2 * k + 1 ≠ 2 * l),
      inner_scalingFun_of_ne (j + 1) (by omega : 2 * k + 1 ≠ 2 * l + 1)]
    ring

theorem waveletFun_mem_V_succ (j k : ℤ) : waveletFun j k ∈ V (j + 1) :=
  Submodule.smul_mem _ _
    (Submodule.sub_mem _ (scalingFun_mem_V _ _) (scalingFun_mem_V _ _))

/-- The wavelet space of level `j` sits inside the scaling space of level `j + 1`. -/
theorem W_le_V_succ (j : ℤ) : W j ≤ V (j + 1) := by
  refine Submodule.topologicalClosure_minimal _ ?_ (isClosed_V (j + 1))
  rw [Submodule.span_le]
  rintro _ ⟨k, rfl⟩
  exact waveletFun_mem_V_succ j k

/-- Every element of the scaling space of level `j` is orthogonal to the wavelet space of the same
level. -/
theorem V_le_orthogonal_W (j : ℤ) : V j ≤ (W j)ᗮ := by
  simp only [W]
  rw [Submodule.orthogonal_closure]
  refine Submodule.topologicalClosure_minimal _ ?_ (Submodule.isClosed_orthogonal _)
  rw [Submodule.span_le]
  rintro _ ⟨k, rfl⟩
  exact Submodule.mem_orthogonal_span_range fun l => by
    rw [real_inner_comm]; exact inner_scalingFun_waveletFun j k l

/-- The wavelet space of level `j` is orthogonal to the scaling space of the same level, the other
reading of `V_le_orthogonal_W`. -/
theorem W_le_orthogonal_V (j : ℤ) : W j ≤ (V j)ᗮ :=
  (Submodule.le_orthogonal_orthogonal _).trans (Submodule.orthogonal_le (V_le_orthogonal_W j))

/-- The level-`(j + 1)` scaling functions lie in `V j ⊔ W j`, so `V (j + 1)` is contained in the
closure of that sum. -/
private theorem V_succ_le_topologicalClosure_sup (j : ℤ) :
    V (j + 1) ≤ (V j ⊔ W j).topologicalClosure := by
  refine Submodule.topologicalClosure_minimal _ ?_ (Submodule.isClosed_topologicalClosure _)
  rw [Submodule.span_le]
  rintro _ ⟨m, rfl⟩
  have hle : V j ⊔ W j ≤ (V j ⊔ W j).topologicalClosure := Submodule.le_topologicalClosure _
  rcases Int.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
  · obtain rfl : m = 2 * k := by omega
    rw [(scalingFun_succ_eq j k).1]
    exact hle (Submodule.smul_mem _ _ (Submodule.add_mem _
      (Submodule.mem_sup_left (scalingFun_mem_V j k))
      (Submodule.mem_sup_right (waveletFun_mem_W j k))))
  · obtain rfl : m = 2 * k + 1 := by omega
    rw [(scalingFun_succ_eq j k).2]
    exact hle (Submodule.smul_mem _ _ (Submodule.sub_mem _
      (Submodule.mem_sup_left (scalingFun_mem_V j k))
      (Submodule.mem_sup_right (waveletFun_mem_W j k))))

/-- [han2009theoretical], Theorem 4.4.2: an element of `V (j + 1)` lies in `W j` exactly when it is
orthogonal to every scaling function of level `j`; in terms of the coefficients `a k = ⟪scalingFun
(j+1) k, f⟫` this says `a (2k+1) = -a (2k)`. -/
theorem mem_W_iff (j : ℤ) (f : Lp ℝ 2 (volume : Measure ℝ)) :
    f ∈ W j ↔ f ∈ V (j + 1) ∧ ∀ k : ℤ, inner ℝ (scalingFun j k) f = 0 := by
  refine ⟨fun h => ⟨W_le_V_succ j h, (mem_orthogonal_V_iff j f).1 (W_le_orthogonal_V j h)⟩,
    fun ⟨hf, horth⟩ => ?_⟩
  have hfV : f ∈ (V j)ᗮ := (mem_orthogonal_V_iff j f).2 horth
  set u := (W j).starProjection f with hu
  have huW : u ∈ W j := (W j).starProjection_apply_mem f
  have hr1 : f - u ∈ (W j)ᗮ := (W j).sub_starProjection_mem_orthogonal f
  have hr2 : f - u ∈ (V j)ᗮ := Submodule.sub_mem _ hfV (W_le_orthogonal_V j huW)
  have hr3 : f - u ∈ V (j + 1) := Submodule.sub_mem _ hf (W_le_V_succ j huW)
  have hr4 : f - u ∈ (V j ⊔ W j)ᗮ := by
    rw [← Submodule.inf_orthogonal]
    exact ⟨hr2, hr1⟩
  have hr5 : f - u ∈ (V (j + 1))ᗮ := by
    refine Submodule.orthogonal_le (V_succ_le_topologicalClosure_sup j) ?_
    rwa [Submodule.orthogonal_closure]
  have : f - u = 0 := by
    have := Submodule.inf_orthogonal_eq_bot (K := V (j + 1))
    rw [Submodule.eq_bot_iff] at this
    exact this _ ⟨hr3, hr5⟩
  rwa [sub_eq_zero.mp this]

/-- `W j` is the part of `V (j + 1)` orthogonal to `V j`. -/
theorem W_eq_inf_orthogonal (j : ℤ) : W j = V (j + 1) ⊓ (V j)ᗮ := by
  ext f
  rw [mem_W_iff, Submodule.mem_inf, mem_orthogonal_V_iff]

/-- The scaling and wavelet spaces of level `j` span the scaling space of level `j + 1`. -/
theorem sup_V_W (j : ℤ) : V j ⊔ W j = V (j + 1) := by
  refine le_antisymm (sup_le (V_le_V_succ j) (W_le_V_succ j)) fun f hf => ?_
  set g := (V j).starProjection f with hg
  have hgV : g ∈ V j := (V j).starProjection_apply_mem f
  have hr : f - g ∈ (V j)ᗮ := (V j).sub_starProjection_mem_orthogonal f
  have hrW : f - g ∈ W j := by
    refine (mem_W_iff j (f - g)).2 ⟨Submodule.sub_mem _ hf (V_le_V_succ j hgV), ?_⟩
    exact (mem_orthogonal_V_iff j (f - g)).1 hr
  have := Submodule.add_mem (V j ⊔ W j) (Submodule.mem_sup_left hgV)
    (Submodule.mem_sup_right hrW)
  rwa [add_sub_cancel] at this

/-- The scaling and wavelet spaces of the same level meet only in `0`. -/
theorem disjoint_V_W (j : ℤ) : Disjoint (V j) (W j) := by
  rw [disjoint_iff, Submodule.eq_bot_iff]
  rintro f ⟨hV, hW⟩
  have := Submodule.inf_orthogonal_eq_bot (K := V j)
  rw [Submodule.eq_bot_iff] at this
  exact this _ ⟨hV, W_le_orthogonal_V j hW⟩

/-- `V (j + 1)` is the orthogonal direct sum of `V j` and `W j`. -/
theorem isCompl_V_W (j : ℤ) :
    IsCompl ((V j).comap (V (j + 1)).subtype) ((W j).comap (V (j + 1)).subtype) := by
  have hinj : Function.Injective (V (j + 1)).subtype := Subtype.coe_injective
  constructor
  · rw [disjoint_iff, ← Submodule.comap_inf, (disjoint_V_W j).eq_bot, Submodule.comap_bot,
      Submodule.ker_subtype]
  · rw [codisjoint_iff]
    refine Submodule.map_injective_of_injective hinj ?_
    rw [Submodule.map_sup, Submodule.map_comap_subtype, Submodule.map_comap_subtype,
      Submodule.map_subtype_top, inf_eq_right.mpr (V_le_V_succ j),
      inf_eq_right.mpr (W_le_V_succ j), sup_V_W]

/-! ### Decomposition and reconstruction -/

/-- [han2009theoretical], Theorem 4.4.3, the decomposition (analysis) step: the level-`j` scaling
and wavelet coefficients of `f` from its level-`(j + 1)` scaling coefficients. -/
theorem decomposition (j k : ℤ) (f : Lp ℝ 2 (volume : Measure ℝ)) :
    inner ℝ (scalingFun j k) f =
        (√2)⁻¹ * (inner ℝ (scalingFun (j + 1) (2 * k)) f +
          inner ℝ (scalingFun (j + 1) (2 * k + 1)) f) ∧
      inner ℝ (waveletFun j k) f =
        (√2)⁻¹ * (inner ℝ (scalingFun (j + 1) (2 * k)) f -
          inner ℝ (scalingFun (j + 1) (2 * k + 1)) f) := by
  refine ⟨?_, ?_⟩
  · rw [scalingFun_two_scale j k, real_inner_smul_left, inner_add_left]
  · rw [waveletFun, real_inner_smul_left, inner_sub_left]

/-- [han2009theoretical], Theorem 4.4.4, the reconstruction (synthesis) step, inverse to
`Haar.decomposition`. -/
theorem reconstruction (j k : ℤ) (f : Lp ℝ 2 (volume : Measure ℝ)) :
    inner ℝ (scalingFun (j + 1) (2 * k)) f =
        (√2)⁻¹ * (inner ℝ (scalingFun j k) f + inner ℝ (waveletFun j k) f) ∧
      inner ℝ (scalingFun (j + 1) (2 * k + 1)) f =
        (√2)⁻¹ * (inner ℝ (scalingFun j k) f - inner ℝ (waveletFun j k) f) := by
  obtain ⟨h1, h2⟩ := scalingFun_succ_eq j k
  refine ⟨?_, ?_⟩
  · rw [h1, real_inner_smul_left, inner_add_left]
  · rw [h2, real_inner_smul_left, inner_sub_left]

/-! ### The multi-level decomposition -/

/-- The scaling spaces increase with the level, by iterating `Haar.V_le_V_succ`. -/
theorem V_mono {i j : ℤ} (h : i ≤ j) : V i ≤ V j := by
  induction j, h using Int.leInduction with
  | base => exact le_rfl
  | succ n _ ih => exact ih.trans (V_le_V_succ n)

/-- Membership in `(W j)ᗮ` is orthogonality to every wavelet of level `j`. -/
theorem mem_orthogonal_W_iff (j : ℤ) (f : Lp ℝ 2 (volume : Measure ℝ)) :
    f ∈ (W j)ᗮ ↔ ∀ k : ℤ, inner ℝ (waveletFun j k) f = 0 := by
  refine ⟨fun h k => (Submodule.mem_orthogonal _ _).1 h _ (waveletFun_mem_W j k), fun h => ?_⟩
  simp only [W]
  rw [Submodule.orthogonal_closure]
  exact Submodule.mem_orthogonal_span_range h

/-- **One analysis step, as a splitting of the projection.** Since `V (j + 1)` is the orthogonal
direct sum of `V j` and `W j`, the projection onto it is the sum of the projections onto the two
summands. -/
theorem starProjection_V_succ (j : ℤ) (f : Lp ℝ 2 (volume : Measure ℝ)) :
    (V (j + 1)).starProjection f = (V j).starProjection f + (W j).starProjection f := by
  obtain ⟨g, hg⟩ : ∃ g, (V (j + 1)).starProjection f = g := ⟨_, rfl⟩
  have hgmem : g ∈ V (j + 1) := hg ▸ (V (j + 1)).starProjection_apply_mem f
  -- projecting `f` onto `V j` or `W j` is projecting `g` onto them
  have hVg : (V j).starProjection g = (V j).starProjection f := by
    rw [← hg]
    exact congrFun (congrArg DFunLike.coe
      (Submodule.starProjection_comp_starProjection_of_le (V_le_V_succ j))) f
  have hWg : (W j).starProjection g = (W j).starProjection f := by
    rw [← hg]
    exact congrFun (congrArg DFunLike.coe
      (Submodule.starProjection_comp_starProjection_of_le (W_le_V_succ j))) f
  -- the part of `g` orthogonal to `V j` lies in `W j`, and is what `W j` projects it to
  have hsub : g - (V j).starProjection g ∈ W j := by
    refine (mem_W_iff j _).2 ⟨Submodule.sub_mem _ hgmem
      (V_le_V_succ j ((V j).starProjection_apply_mem g)), ?_⟩
    exact (mem_orthogonal_V_iff j _).1 ((V j).sub_starProjection_mem_orthogonal g)
  have hzero : (W j).starProjection ((V j).starProjection g) = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff _).mpr
      (V_le_orthogonal_W j ((V j).starProjection_apply_mem g))
  have hWval : (W j).starProjection g = g - (V j).starProjection g := by
    have h := map_sub ((W j).starProjection) g ((V j).starProjection g)
    rw [hzero, sub_zero] at h
    rw [← h]
    exact Submodule.starProjection_eq_self_iff.mpr hsub
  rw [hg, ← hVg, ← hWg, hWval]
  abel

/-- **The multi-level Haar decomposition** ([han2009theoretical], (4.4.9)–(4.4.13) and (4.4.18)):
iterating one analysis step from level `j` down to level `i` splits the projection onto `V j` into
the coarse part in `V i` and the detail parts in the intermediate wavelet spaces,

`P_{V j} f = P_{V i} f + ∑_{i ≤ l < j} P_{W l} f`.

This is the Haar transform as an algorithm: `j - i` rounds of `Haar.decomposition` produce exactly
these summands, each expanded in its own orthonormal system by `Haar.hilbertBasis_V` and
`Haar.hilbertBasis_W`. -/
theorem starProjection_V_eq_sum {i j : ℤ} (h : i ≤ j) (f : Lp ℝ 2 (volume : Measure ℝ)) :
    (V j).starProjection f
      = (V i).starProjection f + ∑ l ∈ Finset.Ico i j, (W l).starProjection f := by
  induction j, h using Int.leInduction with
  | base => simp
  | succ n hn ih =>
      rw [starProjection_V_succ, ih, ← Finset.sum_Ico_add_eq_sum_Ico_add_one hn, add_assoc]

/-- The coarse part of `f` at level `j`, expanded in the level-`j` scaling functions: this is the
book's `f_j = ∑_k a_k^j φ(2^j x - k)` with `a_k^j` its scaling coefficients. -/
theorem hasSum_inner_smul_starProjection_V (j : ℤ) (f : Lp ℝ 2 (volume : Measure ℝ)) :
    HasSum (fun k : ℤ => (inner ℝ (scalingFun j k) f) • scalingFun j k)
      ((V j).starProjection f) :=
  (orthonormal_scalingFun j).hasSum_inner_smul_starProjection f

/-- The detail part of `f` at level `j`, expanded in the level-`j` wavelets: this is the book's
`w_j = ∑_k b_k^j ψ(2^j x - k)` with `b_k^j` its wavelet coefficients. -/
theorem hasSum_inner_smul_starProjection_W (j : ℤ) (f : Lp ℝ 2 (volume : Measure ℝ)) :
    HasSum (fun k : ℤ => (inner ℝ (waveletFun j k) f) • waveletFun j k)
      ((W j).starProjection f) :=
  (orthonormal_waveletFun j).hasSum_inner_smul_starProjection f

/-! ### The Haar wavelets as a basis of `L²(ℝ)` -/

/-- Wavelets of different levels are orthogonal: the level-`i` wavelet space sits inside `V j` for
`i < j`, and `V j` is orthogonal to `W j`. -/
theorem inner_waveletFun_of_lt {i j : ℤ} (hij : i < j) (k l : ℤ) :
    inner ℝ (waveletFun i k) (waveletFun j l) = 0 := by
  have hmem : waveletFun i k ∈ (W j)ᗮ :=
    (((W_le_V_succ i).trans (V_mono (by omega))).trans (V_le_orthogonal_W j)) (waveletFun_mem_W i k)
  rw [real_inner_comm]
  exact (Submodule.mem_orthogonal _ _).1 hmem _ (waveletFun_mem_W j l)

/-- The Haar wavelets of all levels and translations together are orthonormal. -/
theorem orthonormal_waveletFun_prod :
    Orthonormal ℝ fun p : ℤ × ℤ => waveletFun p.1 p.2 := by
  rw [orthonormal_iff_ite]
  rintro ⟨i, k⟩ ⟨j, l⟩
  rcases lt_trichotomy i j with hij | rfl | hij
  · rw [inner_waveletFun_of_lt hij, ite_eq_right (by simp [Prod.ext_iff]; omega)]
  · have h := (orthonormal_iff_ite.mp (orthonormal_waveletFun i)) k l
    rw [h]
    by_cases hkl : k = l
    · rw [ite_eq_left hkl, ite_eq_left (by rw [hkl])]
    · rw [ite_eq_right hkl, ite_eq_right (by simp [Prod.ext_iff, hkl])]
  · rw [real_inner_comm, inner_waveletFun_of_lt hij, ite_eq_right (by simp [Prod.ext_iff]; omega)]

/-- A function orthogonal to every Haar wavelet is zero: the wavelet spaces span `L²(ℝ)`. -/
theorem orthogonal_span_waveletFun_prod_eq_bot :
    (Submodule.span ℝ (Set.range fun p : ℤ × ℤ => waveletFun p.1 p.2))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro f hf
  -- `f` is orthogonal to every wavelet space, so every detail projection vanishes
  have hW : ∀ j : ℤ, (W j).starProjection f = 0 := by
    intro j
    refine (Submodule.starProjection_apply_eq_zero_iff _).mpr
      ((mem_orthogonal_W_iff j f).2 fun k => ?_)
    exact (Submodule.mem_orthogonal _ _).1 hf _ (Submodule.subset_span ⟨(j, k), rfl⟩)
  -- the coarse projections are then all equal, hence lie in every scaling space
  have hV : ∀ {i j : ℤ}, i ≤ j → (V j).starProjection f = (V i).starProjection f := by
    intro i j hij
    rw [starProjection_V_eq_sum hij f, Finset.sum_congr rfl fun l _ => hW l, Finset.sum_const_zero,
      add_zero]
  have hmem : ∀ j : ℤ, (V j).starProjection f ∈ ⨅ i : ℤ, V i := by
    intro j
    refine Submodule.mem_iInf _ |>.mpr fun i => ?_
    rcases le_total i j with hij | hij
    · rw [hV hij]
      exact (V i).starProjection_apply_mem f
    · exact V_mono hij ((V j).starProjection_apply_mem f)
  have hVzero : ∀ j : ℤ, (V j).starProjection f = 0 := by
    intro j
    have := hmem j
    rw [iInf_V_eq_bot, Submodule.mem_bot] at this
    exact this
  -- so `f` is orthogonal to every scaling space, and those are dense
  have horth : ∀ i : ℤ, V i ≤ (Submodule.span ℝ {f})ᗮ := by
    intro i u hu
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, real_inner_comm]
    exact (Submodule.mem_orthogonal _ _).1
      ((Submodule.starProjection_apply_eq_zero_iff _).mp (hVzero i)) u hu
  have hclose : (⨆ i : ℤ, V i).topologicalClosure ≤ (Submodule.span ℝ {f})ᗮ :=
    Submodule.topologicalClosure_minimal _ (iSup_le horth) (Submodule.isClosed_orthogonal _)
  rw [topologicalClosure_iSup_V] at hclose
  have hfmem : f ∈ (Submodule.span ℝ {f})ᗮ := hclose Submodule.mem_top
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at hfmem
  exact inner_self_eq_zero.mp hfmem

/-- **The Haar wavelets are an orthonormal basis of `L²(ℝ)`** ([han2009theoretical], Exercise
4.4.4): the family `2 ^ (j/2) ψ (2 ^ j x - k)`, over all levels `j` and translations `k`, is a
Hilbert basis. -/
noncomputable def hilbertBasis : HilbertBasis (ℤ × ℤ) ℝ (Lp ℝ 2 (volume : Measure ℝ)) :=
  HilbertBasis.mkOfOrthogonalEqBot orthonormal_waveletFun_prod
    orthogonal_span_waveletFun_prod_eq_bot

@[simp]
theorem coe_hilbertBasis : ⇑hilbertBasis = fun p : ℤ × ℤ => waveletFun p.1 p.2 :=
  HilbertBasis.coe_mkOfOrthogonalEqBot _ _

end Haar

end
