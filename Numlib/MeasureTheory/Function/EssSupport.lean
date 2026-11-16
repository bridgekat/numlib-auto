/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
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

The support $\{x : f(x) \neq 0\}$ of a function $f$ does not depend only on the class of $f$ up to
equality almost everywhere: the indicator function of the rationals has the support $\mathbb{Q}$,
but it is zero almost everywhere. The right notion for an element of $L^p$ is the **essential
support** of $f$ with respect to a measure $\mu$. It is the set of points $x$ such that every
neighbourhood of $x$ meets $\{f \neq 0\}$ in a set of positive measure. It is defined here as the
support of the measure $\mu$ restricted to $\{f \neq 0\}$. The presentation follows Propositions
4.17 and 4.18 and Remark 9 in Chapter 4 of [brezis2011functional].

The complement of the essential support is the union of all open sets on which $f$ vanishes almost
everywhere, and there can be uncountably many such sets. On a hereditarily Lindelöf space, for
example a second-countable space, $f$ still vanishes almost everywhere outside its essential
support, so that the complement is the largest open set on which $f$ vanishes almost everywhere.
This makes the definition sound.

## Main definitions

* `MeasureTheory.essSupport`: the essential support of $f$ with respect to $\mu$.

## Main results

* `MeasureTheory.mem_essSupport_iff`, `MeasureTheory.mem_essSupport_iff_forall_mem_nhds`,
  `MeasureTheory.notMem_essSupport_iff`: $x$ is in the essential support if and only if every open
  set or every neighbourhood of $x$ meets $\{f \neq 0\}$ in a set of positive measure.
* `MeasureTheory.isClosed_essSupport`, `MeasureTheory.essSupport_subset_tsupport`,
  `MeasureTheory.essSupport_zero`: the essential support is closed, is contained in the closure of
  $\{f \neq 0\}$, and is empty for the zero function.
* `MeasureTheory.ae_eq_zero_of_notMem_essSupport`: $f = 0$ almost everywhere outside its essential
  support.
* `MeasureTheory.indicator_essSupport_ae_eq`: $f$ is equal almost everywhere to its restriction to
  its essential support.
* `MeasureTheory.essSupport_eq_empty_iff`: the essential support is empty if and only if $f = 0$
  almost everywhere.
* `MeasureTheory.essSupport_congr_ae`: functions that are equal almost everywhere have the same
  essential support.
* `MeasureTheory.essSupport_eq_tsupport`: for a continuous function and a measure that is positive
  on nonempty open sets, the essential support is the closure of $\{f \neq 0\}$.
* `MeasureTheory.essSupport_convolution_subset`: the essential support of $f * g$ is contained in
  the closure of the sum of the essential supports of $f$ and $g$.

## Implementation notes

* The definition is `(μ.restrict (Function.support f)).support`, with
  `MeasureTheory.Measure.support`. It needs only a topology and a measurable structure on the domain
  and a zero in the codomain.
* No result needs the measurability of $f$. The characterizations of membership use only open sets,
  which are measurable under `OpensMeasurableSpace`. The vanishing outside the essential support
  uses the inequality $\mu(t \cap s) \le \mu|_s(t)$ (`MeasureTheory.Measure.le_restrict_apply`),
  which holds for all sets $s$ and $t$. It is `MeasureTheory.Measure.support_mem_ae` for the
  restricted measure.
-/

open Filter Function Set Topology
open scoped Convolution ENNReal Pointwise

namespace MeasureTheory

variable {α E : Type*} [TopologicalSpace α] [MeasurableSpace α] {μ : Measure α}

section Definition

variable [Zero E] {f g : α → E}

variable (μ) in
/-- Let $\alpha$ be a topological space with a measure $\mu$, and let $f \colon \alpha \to E$, where
$E$ has a zero. The **essential support** of $f$ with respect to $\mu$ is the set of points
$x \in \alpha$ such that every neighbourhood of $x$ meets $\{f \neq 0\}$ in a set of positive
$\mu$-measure. Its complement is the union of all open sets on which $f$ vanishes $\mu$-almost
everywhere. On a hereditarily Lindelöf space it is the largest such open set, by
`MeasureTheory.ae_eq_zero_of_notMem_essSupport`. This is Proposition 4.17 of
[brezis2011functional] and the definition after it.

The definition is the support `MeasureTheory.Measure.support` of the measure
`μ.restrict (Function.support f)`. -/
noncomputable def essSupport (f : α → E) : Set α :=
  (μ.restrict (Function.support f)).support

/-- The essential support of a function is closed. -/
theorem isClosed_essSupport : IsClosed (essSupport μ f) :=
  Measure.isClosed_support

/-- The complement of the essential support of a function is open. -/
theorem isOpen_compl_essSupport : IsOpen (essSupport μ f)ᶜ :=
  Measure.isOpen_compl_support

/-- The essential support of the zero function is empty. -/
@[simp]
theorem essSupport_zero : essSupport μ (0 : α → E) = ∅ := by
  simp [essSupport]

/-- If $f = g$ $\mu$-almost everywhere, then $f$ and $g$ have the same essential support with
respect to $\mu$. This is Remark 9(a) in Chapter 4 of [brezis2011functional]. -/
theorem essSupport_congr_ae (h : f =ᵐ[μ] g) : essSupport μ f = essSupport μ g := by
  unfold essSupport
  congr 1
  refine Measure.restrict_congr_set (h.mono fun x hx => ?_)
  simp only [eq_iff_iff, mem_support, ne_eq]
  rw [hx]

variable [OpensMeasurableSpace α]

/-- Let open sets of $\alpha$ be measurable. A point $x$ is in the essential support of $f$ if and
only if $\mu(U \cap \{f \neq 0\}) > 0$ for every open set $U$ that contains $x$. -/
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

/-- Let open sets of $\alpha$ be measurable. A point $x$ is in the essential support of $f$ if and
only if $\mu(U \cap \{f \neq 0\}) > 0$ for every neighbourhood $U$ of $x$. -/
theorem mem_essSupport_iff_forall_mem_nhds {x : α} :
    x ∈ essSupport μ f ↔ ∀ U ∈ 𝓝 x, 0 < μ (U ∩ support f) := by
  rw [mem_essSupport_iff]
  constructor
  · intro h U hU
    obtain ⟨V, hVU, hV, hxV⟩ := mem_nhds_iff.1 hU
    exact (h V hV hxV).trans_le (measure_mono (inter_subset_inter_left _ hVU))
  · exact fun h U hU hxU => h U (hU.mem_nhds hxU)

/-- Let open sets of $\alpha$ be measurable. A point $x$ is outside the essential support of $f$ if
and only if $\mu(U \cap \{f \neq 0\}) = 0$ for some neighbourhood $U$ of $x$. -/
theorem notMem_essSupport_iff {x : α} :
    x ∉ essSupport μ f ↔ ∃ U ∈ 𝓝 x, μ (U ∩ support f) = 0 := by
  simp [mem_essSupport_iff_forall_mem_nhds, pos_iff_ne_zero]

/-- Let open sets of $\alpha$ be measurable. The essential support of $f$ is contained in the
closure of $\{f \neq 0\}$. -/
theorem essSupport_subset_tsupport : essSupport μ f ⊆ tsupport f :=
  Measure.support_restrict_subset.trans inter_subset_left

end Definition

/-! ### Vanishing off the essential support -/

section Lindelof

variable [HereditarilyLindelofSpace α] [Zero E] {f : α → E}

/-- **The function vanishes outside its essential support.** Let $\alpha$ be a hereditarily Lindelöf
topological space, for example a second-countable space, with a measure $\mu$. Then for every
$f \colon \alpha \to E$, $f(x) = 0$ for $\mu$-almost every $x$ outside the essential support of
$f$. This is Proposition 4.17 of [brezis2011functional].

This result makes the definition sound. The complement of the essential support is the union of
all open sets on which $f$ vanishes almost everywhere, and there can be uncountably many of
them. -/
theorem ae_eq_zero_of_notMem_essSupport : ∀ᵐ x ∂μ, x ∉ essSupport μ f → f x = 0 := by
  have h0 : μ ((essSupport μ f)ᶜ ∩ support f) = 0 := by
    refine le_antisymm ((Measure.le_restrict_apply _ _).trans (le_of_eq ?_)) zero_le
    exact Measure.measure_compl_support
  rw [measure_eq_zero_iff_ae_notMem] at h0
  filter_upwards [h0] with x hx hxs
  by_contra hfx
  exact hx ⟨hxs, hfx⟩

/-- Let $\alpha$ be a hereditarily Lindelöf topological space with a measure $\mu$. Every function
$f$ is equal $\mu$-almost everywhere to the function that is $f$ on the essential support of $f$
and $0$ outside it. -/
theorem indicator_essSupport_ae_eq : (essSupport μ f).indicator f =ᵐ[μ] f := by
  filter_upwards [ae_eq_zero_of_notMem_essSupport (μ := μ) (f := f)] with x hx
  by_cases hxs : x ∈ essSupport μ f
  · simp [indicator_of_mem hxs]
  · simp [indicator_of_notMem hxs, hx hxs]

/-- Let $\alpha$ be a hereditarily Lindelöf topological space with a measure $\mu$. The essential
support of $f$ is empty if and only if $f = 0$ $\mu$-almost everywhere. -/
theorem essSupport_eq_empty_iff : essSupport μ f = ∅ ↔ f =ᵐ[μ] 0 := by
  rw [essSupport, Measure.support_eq_empty_iff, Measure.restrict_eq_zero,
    measure_eq_zero_iff_ae_notMem]
  simp [EventuallyEq]

end Lindelof

/-! ### Continuous functions -/

/-- Let $\alpha$ be a topological space in which open sets are measurable, with a measure $\mu$ that
is positive on nonempty open sets, and let $E$ be a $T_1$ topological space with a zero. If
$f \colon \alpha \to E$ is continuous, then the essential support of $f$ is the closure of
$\{f \neq 0\}$. This is Remark 9(b) in Chapter 4 of [brezis2011functional]. -/
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

/-- **The essential support of a convolution.** Let $G$ be a hereditarily Lindelöf additive
commutative group with a topology in which open sets are measurable, and with measurable
addition and negation. Let $\mu$ be an $s$-finite right-invariant measure on $G$. Let $E$, $E'$
and $F$ be normed spaces over a nontrivially normed field $\mathbb{K}$, with $F$ also a real
normed space, let $L \colon E \times E' \to F$ be a continuous bilinear map, and let
$f \colon G \to E$ and $g \colon G \to E'$. Then
$$\operatorname{ess\,supp}(f * g) \subseteq \overline{\operatorname{ess\,supp} f +
  \operatorname{ess\,supp} g},$$
where $(f * g)(x) = \int L(f(t), g(x - t)) \, d\mu(t)$. This is Proposition 4.18 of
[brezis2011functional].

No integrability is assumed. Where the integral of the convolution does not exist, its value is
$0$, and the inclusion holds there trivially. The proof replaces $f$ and $g$ by their
restrictions to their essential supports, which changes neither side
(`MeasureTheory.indicator_essSupport_ae_eq`, `MeasureTheory.convolution_congr`). For the
restrictions the statement is `MeasureTheory.support_convolution_subset`. -/
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
