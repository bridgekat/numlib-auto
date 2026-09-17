/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.MeasureTheory.Function.EssSupport`, beside
`Mathlib.MeasureTheory.Measure.Support`, which has the support of a measure and is what this
is built on.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Measure.Support

/-!
# The essential support of a function

The support of a function, `Function.support f = {x | f x ≠ 0}`, is not a function of the
almost-everywhere class of `f`: the indicator of the rationals has support `ℚ` although it is
almost everywhere zero. The right notion for an `L^p` class is the **essential support** of `f`
with respect to a measure `μ`: the complement of the largest open set on which `f` vanishes
almost everywhere, equivalently the set of points all of whose neighbourhoods meet `{f ≠ 0}` in a
set of positive measure. This is the support of the measure `μ.restrict (Function.support f)` in
the sense of `MeasureTheory.Measure.support`, and that is how it is defined here:

* `MeasureTheory.essSupport μ f := (μ.restrict (Function.support f)).support`.

That the definition is sound — that `f` vanishes almost everywhere off its essential support,
although the essential support is a complement of a union of *uncountably* many open null sets
— is `MeasureTheory.ae_eq_zero_of_notMem_essSupport`, valid on a hereditarily Lindelöf space
(every second-countable space is one); it is Mathlib's `MeasureTheory.Measure.support_mem_ae`
applied to the restricted measure.

## Main statements

* `MeasureTheory.mem_essSupport_iff`, `MeasureTheory.mem_essSupport_iff_forall_mem_nhds`,
  `MeasureTheory.notMem_essSupport_iff`: the pointwise characterizations.
* `MeasureTheory.isClosed_essSupport`, `MeasureTheory.essSupport_subset_tsupport`,
  `MeasureTheory.essSupport_zero`: the essential support is closed, contained in the topological
  support, and empty for the zero function.
* `MeasureTheory.ae_eq_zero_of_notMem_essSupport`, `MeasureTheory.indicator_essSupport_ae_eq`,
  `MeasureTheory.essSupport_eq_empty_iff`: `f = 0` almost everywhere outside its essential
  support, so `f` is almost everywhere equal to its restriction to its essential support, and the
  essential support is empty exactly when `f = 0` almost everywhere.
* `MeasureTheory.essSupport_congr_ae`: the essential support depends only on the
  almost-everywhere class of `f`.
* `MeasureTheory.essSupport_eq_tsupport`: for a continuous function and a measure positive on
  open sets, the essential support is the topological support.
* `MeasureTheory.essSupport_convolution_subset`: the essential support of a convolution is
  contained in the closure of the sum of the essential supports of the factors.

## Implementation notes

The definition asks for nothing beyond a topology and a measurable structure on the domain and a
zero in the codomain. Measurability of `f` is never needed: the characterizations of membership
use only open neighbourhoods, which are measurable under `OpensMeasurableSpace`, and the
vanishing off the essential support uses the inequality
`μ (t ∩ s) ≤ μ.restrict s t` (`MeasureTheory.Measure.le_restrict_apply`), which holds for every
`s` and `t`.

## References

Haim Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
Universitext, Springer, 2011 [brezis2011functional], Proposition 4.17 with its Remark 9, and
Proposition 4.18.
-/

open Filter Function Set Topology
open scoped Convolution ENNReal Pointwise

namespace MeasureTheory

variable {α E : Type*} [TopologicalSpace α] [MeasurableSpace α] {μ : Measure α}

section Definition

variable [Zero E] {f g : α → E}

variable (μ) in
/-- The **essential support** of `f` with respect to `μ`: the set of points all of whose
neighbourhoods meet `{f ≠ 0}` in a set of positive `μ`-measure, that is, the support of the
measure `μ.restrict (Function.support f)`. Its complement is the largest open set on which `f`
vanishes `μ`-almost everywhere ([brezis2011functional] Proposition 4.17 and the definition
following it). -/
def essSupport (f : α → E) : Set α :=
  (μ.restrict (Function.support f)).support

/-- The essential support is closed. -/
theorem isClosed_essSupport : IsClosed (essSupport μ f) :=
  Measure.isClosed_support

/-- The complement of the essential support is open. -/
theorem isOpen_compl_essSupport : IsOpen (essSupport μ f)ᶜ :=
  Measure.isOpen_compl_support

/-- The essential support of the zero function is empty. -/
@[simp]
theorem essSupport_zero : essSupport μ (0 : α → E) = ∅ := by
  simp [essSupport]

/-- The essential support depends only on the almost-everywhere class of the function
([brezis2011functional] Remark 9 (a) of chapter 4). -/
theorem essSupport_congr_ae (h : f =ᵐ[μ] g) : essSupport μ f = essSupport μ g := by
  unfold essSupport
  congr 1
  refine Measure.restrict_congr_set (h.mono fun x hx => ?_)
  simp only [eq_iff_iff, mem_support, ne_eq]
  rw [hx]

variable [OpensMeasurableSpace α]

/-- A point lies in the essential support of `f` iff every open set containing it meets the
support of `f` in a set of positive measure. -/
theorem mem_essSupport_iff {x : α} :
    x ∈ essSupport μ f ↔ ∀ U, IsOpen U → x ∈ U → 0 < μ (U ∩ support f) := by
  rw [essSupport, Measure.support_eq_forall_isOpen]
  change (∀ U, x ∈ U → IsOpen U → 0 < μ.restrict (support f) U) ↔ _
  constructor
  · intro h U hU hxU
    rw [← Measure.restrict_apply hU.measurableSet]
    exact h U hxU hU
  · intro h U hxU hU
    rw [Measure.restrict_apply hU.measurableSet]
    exact h U hU hxU

/-- A point lies in the essential support of `f` iff every neighbourhood of it meets the support
of `f` in a set of positive measure. -/
theorem mem_essSupport_iff_forall_mem_nhds {x : α} :
    x ∈ essSupport μ f ↔ ∀ U ∈ 𝓝 x, 0 < μ (U ∩ support f) := by
  rw [mem_essSupport_iff]
  constructor
  · intro h U hU
    obtain ⟨V, hVU, hV, hxV⟩ := mem_nhds_iff.1 hU
    exact (h V hV hxV).trans_le (measure_mono (inter_subset_inter_left _ hVU))
  · exact fun h U hU hxU => h U (hU.mem_nhds hxU)

/-- A point lies outside the essential support of `f` iff some neighbourhood of it meets the
support of `f` in a null set. -/
theorem notMem_essSupport_iff {x : α} :
    x ∉ essSupport μ f ↔ ∃ U ∈ 𝓝 x, μ (U ∩ support f) = 0 := by
  simp [mem_essSupport_iff_forall_mem_nhds, pos_iff_ne_zero]

/-- The essential support is contained in the topological support. -/
theorem essSupport_subset_tsupport : essSupport μ f ⊆ tsupport f :=
  Measure.support_restrict_subset.trans inter_subset_left

end Definition

/-! ### Vanishing off the essential support -/

section Lindelof

variable [HereditarilyLindelofSpace α] [Zero E] {f : α → E}

/-- **The essential support carries the function** ([brezis2011functional] Proposition 4.17):
`f` vanishes almost everywhere outside its essential support, on a hereditarily Lindelöf space
(in particular on any second-countable space). This is what makes the definition sound: the
complement of the essential support is the union of *all* open sets on which `f` vanishes almost
everywhere, and there may be uncountably many of them. -/
theorem ae_eq_zero_of_notMem_essSupport : ∀ᵐ x ∂μ, x ∉ essSupport μ f → f x = 0 := by
  have h0 : μ ((essSupport μ f)ᶜ ∩ support f) = 0 := by
    refine le_antisymm ((Measure.le_restrict_apply _ _).trans (le_of_eq ?_)) zero_le
    exact Measure.measure_compl_support
  rw [measure_eq_zero_iff_ae_notMem] at h0
  filter_upwards [h0] with x hx hxs
  by_contra hfx
  exact hx ⟨hxs, hfx⟩

/-- `f` is almost everywhere equal to its restriction to its essential support. -/
theorem indicator_essSupport_ae_eq : (essSupport μ f).indicator f =ᵐ[μ] f := by
  filter_upwards [ae_eq_zero_of_notMem_essSupport (μ := μ) (f := f)] with x hx
  by_cases hxs : x ∈ essSupport μ f
  · simp [indicator_of_mem hxs]
  · simp [indicator_of_notMem hxs, hx hxs]

/-- The essential support is empty exactly when the function vanishes almost everywhere. -/
theorem essSupport_eq_empty_iff : essSupport μ f = ∅ ↔ f =ᵐ[μ] 0 := by
  rw [essSupport, Measure.support_eq_empty_iff, Measure.restrict_eq_zero,
    measure_eq_zero_iff_ae_notMem]
  simp [EventuallyEq]

end Lindelof

/-! ### Continuous functions -/

/-- For a continuous function and a measure positive on open sets, the essential support is the
topological support ([brezis2011functional] Remark 9 (b) of chapter 4). -/
theorem essSupport_eq_tsupport [OpensMeasurableSpace α] [μ.IsOpenPosMeasure] [Zero E]
    [TopologicalSpace E] [T1Space E] {f : α → E} (hf : Continuous f) :
    essSupport μ f = tsupport f := by
  refine subset_antisymm essSupport_subset_tsupport (isClosed_essSupport.closure_subset_iff.2 ?_)
  have h : interior (support f) ∩ μ.support ⊆ essSupport μ f := Measure.interior_inter_support
  rwa [hf.isOpen_support.interior_eq, Measure.support_eq_univ, inter_univ] at h

/-! ### Convolution -/

section Convolution

variable {𝕜 G E' F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedAddCommGroup E'] [NormedAddCommGroup F]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜 E'] [NormedSpace 𝕜 F] [NormedSpace ℝ F]
  [AddCommGroup G] [TopologicalSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]
  [HereditarilyLindelofSpace G] [MeasurableAdd₂ G] [MeasurableNeg G]
  {μ : Measure G} [SFinite μ] [μ.IsAddRightInvariant]
  {f : G → E} {g : G → E'}

/-- **The essential support of a convolution** ([brezis2011functional] Proposition 4.18):
`essSupport μ (f ⋆ g) ⊆ closure (essSupport μ f + essSupport μ g)`. No integrability is
assumed: where the convolution integral does not exist it is `0`, and the bound holds there for
free. Replacing `f` and `g` by their restrictions to their essential supports changes neither
side (`MeasureTheory.indicator_essSupport_ae_eq`, `MeasureTheory.convolution_congr`), and for
the restrictions the statement is `MeasureTheory.support_convolution_subset`. -/
theorem essSupport_convolution_subset (L : E →L[𝕜] E' →L[𝕜] F) :
    essSupport μ (f ⋆[L, μ] g) ⊆ closure (essSupport μ f + essSupport μ g) := by
  have hf : f =ᵐ[μ] (essSupport μ f).indicator f := indicator_essSupport_ae_eq.symm
  have hg : g =ᵐ[μ] (essSupport μ g).indicator g := indicator_essSupport_ae_eq.symm
  rw [convolution_congr L hf hg]
  refine essSupport_subset_tsupport.trans (closure_mono ?_)
  exact (support_convolution_subset L).trans
    (add_subset_add support_indicator_subset support_indicator_subset)

end Convolution

end MeasureTheory
