/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.InnerProductSpace.l2Space`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# Hilbert sums and countable Hilbert bases

Let $E$ be an inner product space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$. A pairwise
orthogonal family of vectors $(v_i)$ in a Hilbert space is summable if and only if
$\sum_i \|v_i\|^2 < \infty$, and then $\|\sum_i v_i\|^2 = \sum_i \|v_i\|^2$. For a family of
mutually orthogonal subspaces $(E_i)$ with orthogonal projections $P_{E_i}$, every vector is
expanded as $u = \sum_i P_{E_i} u$ when the subspaces span a dense subspace, with the
Bessel–Parseval identity $\|u\|^2 = \sum_i \|P_{E_i} u\|^2$. The presentation follows §5.4 of
[brezis2011functional] (Lemma 5.1, Theorems 5.9 and 5.11, Remarks 10 and 11).

An orthonormal family in a separable space is countable, because orthonormal vectors are at distance
$\sqrt 2$ and the balls of radius $1/2$ around them are pairwise disjoint. Hence every separable
Hilbert space has a countable Hilbert basis, and an infinite-dimensional one has a Hilbert basis
indexed by $\mathbb{N}$. Conversely, a Hilbert space with a countable Hilbert basis is separable.

## Main definitions

* `HilbertBasis.reindex`: a Hilbert basis reindexed along an equivalence of index types.

## Main results

* `summable_iff_summable_norm_sq_of_pairwise_inner_eq_zero`,
  `hasSum_norm_sq_of_pairwise_inner_eq_zero`: a pairwise orthogonal family is summable if and only
  if its squared norms are, and its sum satisfies $\|S\|^2 = \sum_i \|v_i\|^2$ (Lemma 5.1 of
  [brezis2011functional]).
* `OrthogonalFamily.hasSum_starProjection`: the projections $P_{E_i} u$ sum to the projection of $u$
  onto the closure of the span of the subspaces $E_i$.
* `OrthogonalFamily.hasSum_starProjection_of_dense`,
  `OrthogonalFamily.hasSum_norm_sq_starProjection_of_dense`: if the subspaces span a dense subspace,
  then $u = \sum_i P_{E_i} u$ and $\|u\|^2 = \sum_i \|P_{E_i} u\|^2$ (Theorem 5.9 of
  [brezis2011functional]).
* `OrthogonalFamily.tsum_norm_sq_starProjection_le`: Bessel's inequality
  $\sum_i \|P_{E_i} u\|^2 \le \|u\|^2$.
* `Orthonormal.countable_of_separableSpace`: an orthonormal family in a separable space is
  countable.
* `exists_hilbertBasis_countable`, `exists_hilbertBasis_nat`: a separable Hilbert space has a
  countable Hilbert basis, and one indexed by $\mathbb{N}$ if it is infinite-dimensional (Theorem
  5.11 of [brezis2011functional]).
* `HilbertBasis.separableSpace`: a Hilbert space with a countable Hilbert basis is separable.

## Proof outline

The projection expansion identifies the coordinates of Mathlib's expansion of a vector in $\ell^2$
(`OrthogonalFamily.hasSum_linearIsometry`) with the orthogonal projections $P_{E_i} u$. The source
proves Theorem 5.11 by the Gram–Schmidt process applied to a dense sequence. Here the countable
basis comes from Mathlib's `exists_hilbertBasis`, which uses Zorn's lemma, and the counting argument
above; this route is shorter.

## Implementation notes

* All results are over a field $\mathbb{K}$ with `RCLike 𝕜`, because the arguments do not use that
  the scalars are real.
* The orthogonal projection onto $V$ is Mathlib's `Submodule.starProjection`, an operator from $E$
  to $E$.
* Mathlib's `OrthogonalFamily.summable_iff_norm_sq_summable` is the statement for a family of
  subspaces. The form for a family of vectors $(v_i)$ follows from it with the lines
  $\mathbb{K} v_i$.
* Mathlib has `OrthonormalBasis.reindex` but no reindexing of a `HilbertBasis`;
  `HilbertBasis.reindex` supplies it.
-/

open Filter Topology
open scoped InnerProductSpace

noncomputable section

variable {ι 𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-! ### Pairwise orthogonal families of vectors -/

section PairwiseOrthogonal

variable {v : ι → E}

/-- If the vectors $(v_i)$ are pairwise orthogonal, then the lines $\mathbb{K} v_i$ that they span
form an orthogonal family of subspaces. -/
theorem orthogonalFamily_span_singleton_of_pairwise_inner_eq_zero
    (hv : Pairwise fun i j => ⟪v i, v j⟫_𝕜 = 0) :
    OrthogonalFamily 𝕜 (fun i => (𝕜 ∙ v i)) fun i => (𝕜 ∙ v i).subtypeₗᵢ :=
  orthogonalFamily_iff_pairwise.2 fun i j hij =>
    Submodule.isOrtho_span.2 fun _ hu _ hw => by
      rw [Set.mem_singleton_iff.1 hu, Set.mem_singleton_iff.1 hw]
      exact hv hij

/-- **Pythagoras' theorem** for a finite sum. If the vectors $(v_i)$ are pairwise orthogonal, then
for every finite set $s$ of indices
$$\Bigl\|\sum_{i \in s} v_i\Bigr\|^2 = \sum_{i \in s} \|v_i\|^2.$$
-/
theorem norm_sum_sq_of_pairwise_inner_eq_zero (hv : Pairwise fun i j => ⟪v i, v j⟫_𝕜 = 0)
    (s : Finset ι) : ‖∑ i ∈ s, v i‖ ^ 2 = ∑ i ∈ s, ‖v i‖ ^ 2 :=
  (orthogonalFamily_span_singleton_of_pairwise_inner_eq_zero hv).norm_sum
    (fun i => ⟨v i, Submodule.mem_span_singleton_self _⟩) s

/-- Let $E$ be a Hilbert space and let $(v_i)_{i \in \iota}$ be pairwise orthogonal vectors in $E$,
indexed by an arbitrary type $\iota$. Then $(v_i)$ is summable (unconditionally) if and only if
$(\|v_i\|^2)$ is summable.

This is the existence part of Lemma 5.1 of [brezis2011functional], for an arbitrary index type. -/
theorem summable_iff_summable_norm_sq_of_pairwise_inner_eq_zero [CompleteSpace E]
    (hv : Pairwise fun i j => ⟪v i, v j⟫_𝕜 = 0) :
    Summable v ↔ Summable fun i => ‖v i‖ ^ 2 :=
  (orthogonalFamily_span_singleton_of_pairwise_inner_eq_zero hv).summable_iff_norm_sq_summable
    fun i => ⟨v i, Submodule.mem_span_singleton_self _⟩

/-- Let $(v_i)$ be pairwise orthogonal vectors in $E$ with unconditional sum $S$. Then $(\|v_i\|^2)$
has the sum $\|S\|^2$:
$$\|S\|^2 = \sum_i \|v_i\|^2.$$

This is the identity (23) of Lemma 5.1 of [brezis2011functional]. No completeness of $E$ is
needed. -/
theorem hasSum_norm_sq_of_pairwise_inner_eq_zero {S : E}
    (hv : Pairwise fun i j => ⟪v i, v j⟫_𝕜 = 0) (hS : HasSum v S) :
    HasSum (fun i => ‖v i‖ ^ 2) (‖S‖ ^ 2) := by
  have h : Tendsto (fun s : Finset ι => ‖∑ i ∈ s, v i‖ ^ 2) atTop (𝓝 (‖S‖ ^ 2)) :=
    (continuous_norm.pow 2).continuousAt.tendsto.comp hS
  simpa only [HasSum, SummationFilter.unconditional_filter,
    norm_sum_sq_of_pairwise_inner_eq_zero hv] using h

end PairwiseOrthogonal

/-! ### The projection expansion -/

namespace OrthogonalFamily

variable [CompleteSpace E] {V : ι → Submodule 𝕜 E} [∀ i, (V i).HasOrthogonalProjection]
  (hV : OrthogonalFamily 𝕜 (fun i => V i) fun i => (V i).subtypeₗᵢ)
include hV

omit [CompleteSpace E] in
/-- Let $(V_i)$ be mutually orthogonal subspaces of $E$, each with an orthogonal projection
$P_{V_i}$. Then for every $u \in E$ the projections $P_{V_i} u$ are pairwise orthogonal. -/
theorem pairwise_inner_starProjection_eq_zero (u : E) :
    Pairwise fun i j => ⟪(V i).starProjection u, (V j).starProjection u⟫_𝕜 = 0 :=
  fun i j hij => (hV.isOrtho hij).inner_eq ((V i).starProjection_apply_mem u)
    ((V j).starProjection_apply_mem u)

/-- Let $E$ be a Hilbert space and let $(V_i)$ be mutually orthogonal subspaces of $E$, each with an
orthogonal projection $P_{V_i}$. Let $W$ be the closure of the span of all the $V_i$. Then for
every $u \in E$ the projections $P_{V_i} u$ sum unconditionally to $P_W u$:
$$\sum_i P_{V_i} u = P_W u.$$

This is the form of Theorem 5.9 of [brezis2011functional] that its proof gives without the
density hypothesis (b), display (26) there. -/
theorem hasSum_starProjection (u : E) :
    HasSum (fun i => (V i).starProjection u)
      ((⨆ i, V i).topologicalClosure.starProjection u) := by
  classical
  -- a subspace with an orthogonal projection is closed, hence complete
  have : ∀ i, CompleteSpace (V i) := fun i => by
    have : IsClosed ((V i : Set E)) := by
      rw [← Submodule.orthogonal_orthogonal (V i)]
      exact Submodule.isClosed_orthogonal _
    exact this.completeSpace_coe
  set F := (⨆ i, V i).topologicalClosure with hF
  set w := F.starProjection u with hw
  -- `w` lies in the range of the isometry `lp (fun i => V i) 2 →ₗᵢ E`
  have hwF : w ∈ F := F.starProjection_apply_mem u
  have hrange : w ∈ LinearMap.range hV.linearIsometry.toLinearMap := by
    rw [hV.range_linearIsometry]
    simpa only [Submodule.subtypeₗᵢ_toLinearMap, Submodule.range_subtype] using hwF
  obtain ⟨f, hf⟩ := hrange
  have hsum : HasSum (fun i => ((f i : V i) : E)) w := by
    have h := hV.hasSum_linearIsometry f
    have hf' : hV.linearIsometry f = w := hf
    rw [hf'] at h
    exact h
  -- the `i`-th coordinate of `w` is its projection onto `V i`
  have hcoord : ∀ i, (V i).starProjection w = f i := by
    intro i
    have h1 : HasSum (fun j => (V i).starProjection ((f j : V j) : E)) ((V i).starProjection w) :=
      ((V i).starProjection).hasSum hsum
    have h2 : HasSum (fun j => (V i).starProjection ((f j : V j) : E)) (f i) := by
      have heq : (fun j => (V i).starProjection ((f j : V j) : E))
          = fun j => if j = i then ((f i : V i) : E) else 0 := by
        funext j
        split_ifs with hji
        · subst hji
          exact Submodule.starProjection_eq_self_iff.2 (f j).2
        · exact (Submodule.starProjection_apply_eq_zero_iff (V i)).2 ((hV.isOrtho hji) (f j).2)
      rw [heq]
      exact hasSum_ite_eq i _
    exact h1.unique h2
  -- projecting `u` onto `V i` is projecting `w` onto `V i`, since `V i ≤ F`
  have hle : ∀ i, V i ≤ F := fun i => (le_iSup V i).trans (Submodule.le_topologicalClosure _)
  refine hsum.congr_fun fun i => ?_
  rw [← hcoord i, hw, ← ContinuousLinearMap.comp_apply,
    Submodule.starProjection_comp_starProjection_of_le (hle i)]

/-- **Bessel–Parseval identity for the closed span.** Let $E$ be a Hilbert space, let $(V_i)$ be
mutually orthogonal subspaces of $E$, each with an orthogonal projection $P_{V_i}$, and let $W$
be the closure of their span. Then for every $u \in E$,
$$\sum_i \|P_{V_i} u\|^2 = \|P_W u\|^2,$$
with an unconditionally convergent sum. -/
theorem hasSum_norm_sq_starProjection (u : E) :
    HasSum (fun i => ‖(V i).starProjection u‖ ^ 2)
      (‖(⨆ i, V i).topologicalClosure.starProjection u‖ ^ 2) :=
  hasSum_norm_sq_of_pairwise_inner_eq_zero (hV.pairwise_inner_starProjection_eq_zero u)
    (hV.hasSum_starProjection u)

/-- **Bessel's inequality.** Let $E$ be a Hilbert space and let $(V_i)$ be mutually orthogonal
subspaces of $E$, each with an orthogonal projection $P_{V_i}$. Then for every $u \in E$,
$$\sum_i \|P_{V_i} u\|^2 \le \|u\|^2.$$
-/
theorem tsum_norm_sq_starProjection_le (u : E) :
    ∑' i, ‖(V i).starProjection u‖ ^ 2 ≤ ‖u‖ ^ 2 := by
  rw [(hV.hasSum_norm_sq_starProjection u).tsum_eq]
  gcongr
  exact Submodule.norm_starProjection_apply_le _ u

/-- Let $E$ be a Hilbert space and let $(V_i)$ be mutually orthogonal subspaces of $E$, each with an
orthogonal projection $P_{V_i}$. If the span of the $V_i$ is dense in $E$, then every $u \in E$
is the unconditional sum of its projections:
$$u = \sum_i P_{V_i} u.$$
This is Theorem 5.9 of [brezis2011functional]. -/
theorem hasSum_starProjection_of_dense (hdense : (⨆ i, V i).topologicalClosure = ⊤) (u : E) :
    HasSum (fun i => (V i).starProjection u) u := by
  have h := hV.hasSum_starProjection u
  simp only [hdense, Submodule.starProjection_top, ContinuousLinearMap.id_apply] at h
  exact h

/-- **Bessel–Parseval identity.** Let $E$ be a Hilbert space and let $(V_i)$ be mutually orthogonal
subspaces of $E$, each with an orthogonal projection $P_{V_i}$. If the span of the $V_i$ is
dense in $E$, then for every $u \in E$,
$$\sum_i \|P_{V_i} u\|^2 = \|u\|^2,$$
with an unconditionally convergent sum. This is the identity (20) of Theorem 5.9 of
[brezis2011functional]. -/
theorem hasSum_norm_sq_starProjection_of_dense (hdense : (⨆ i, V i).topologicalClosure = ⊤)
    (u : E) : HasSum (fun i => ‖(V i).starProjection u‖ ^ 2) (‖u‖ ^ 2) :=
  hasSum_norm_sq_of_pairwise_inner_eq_zero (hV.pairwise_inner_starProjection_eq_zero u)
    (hV.hasSum_starProjection_of_dense hdense u)

end OrthogonalFamily

/-! ### Countable Hilbert bases -/

/-- Two distinct members $v_i$, $v_j$ of an orthonormal family satisfy $\|v_i - v_j\|^2 = 2$. In
particular the balls of radius $1/2$ around them are disjoint. -/
theorem Orthonormal.norm_sub_sq_eq_two {v : ι → E} (hv : Orthonormal 𝕜 v) {i j : ι} (hij : i ≠ j) :
    ‖v i - v j‖ ^ 2 = 2 := by
  rw [norm_sub_sq (𝕜 := 𝕜), hv.1 i, hv.1 j, hv.2 hij]
  norm_num

/-- An orthonormal family $(v_i)_{i \in \iota}$ in a separable space $E$ is countable: the index
type $\iota$ is countable.

This is the counting step of the proof of Theorem 5.11 of [brezis2011functional]. The balls of
radius $1/2$ around the members of the family are open, nonempty and pairwise disjoint, so each
contains a different point of a countable dense set. No completeness of $E$ is needed. -/
theorem Orthonormal.countable_of_separableSpace [TopologicalSpace.SeparableSpace E] {v : ι → E}
    (hv : Orthonormal 𝕜 v) : Countable ι := by
  refine Pairwise.countable_of_isOpen_disjoint (s := fun i => Metric.ball (v i) (1 / 2))
    (fun i j hij => Metric.ball_disjoint_ball ?_) (fun i => Metric.isOpen_ball)
    fun i => Metric.nonempty_ball.2 (by norm_num)
  rw [dist_eq_norm]
  have h2 := hv.norm_sub_sq_eq_two hij
  nlinarith [norm_nonneg (v i - v j)]

namespace HilbertBasis

variable [CompleteSpace E]

/-- Let $E$ be a Hilbert space, let $b = (b_i)_{i \in \iota}$ be a Hilbert basis of $E$ and let
$e : \iota \to \iota'$ be a bijection. The **reindexed Hilbert basis** `b.reindex e` is the
Hilbert basis $(b_{e^{-1}(i')})_{i' \in \iota'}$. -/
protected def reindex {ι' : Type*} (b : HilbertBasis ι 𝕜 E) (e : ι ≃ ι') :
    HilbertBasis ι' 𝕜 E :=
  HilbertBasis.mk (b.orthonormal.comp e.symm e.symm.injective) (by
    rw [Set.range_comp, Equiv.range_eq_univ, Set.image_univ]
    exact b.dense_span.ge)

/-- The vectors of a reindexed Hilbert basis are those of $b$ composed with $e^{-1}$:
`⇑(b.reindex e) = ⇑b ∘ e.symm`. -/
@[simp]
theorem coe_reindex {ι' : Type*} (b : HilbertBasis ι 𝕜 E) (e : ι ≃ ι') :
    ⇑(b.reindex e) = ⇑b ∘ e.symm :=
  HilbertBasis.coe_mk _ _

/-- The reindexed Hilbert basis at the index $i'$ is $b_{e^{-1}(i')}$. -/
theorem reindex_apply {ι' : Type*} (b : HilbertBasis ι 𝕜 E) (e : ι ≃ ι') (i' : ι') :
    b.reindex e i' = b (e.symm i') := by
  rw [coe_reindex, Function.comp_apply]

omit [CompleteSpace E] in
/-- An inner product space $E$ with a countable Hilbert basis is separable.

This is the converse of `exists_hilbertBasis_countable`. It is the countable-basis form of the
statement of Remark 10 in Chapter 5 of [brezis2011functional] that the separable Hilbert spaces
are exactly those isometric to $\ell^2$. -/
theorem separableSpace [Countable ι] (b : HilbertBasis ι 𝕜 E) :
    TopologicalSpace.SeparableSpace E := by
  rw [← TopologicalSpace.isSeparable_univ_iff]
  have h1 : TopologicalSpace.IsSeparable (Set.range b) := (Set.countable_range b).isSeparable
  have h2 := h1.span (R := 𝕜) |>.closure
  rw [← Submodule.topologicalClosure_coe, b.dense_span, Submodule.top_coe] at h2
  exact h2

end HilbertBasis

section Separable

variable (𝕜 E) [CompleteSpace E] [TopologicalSpace.SeparableSpace E]

/-- Every separable Hilbert space $E$ has a countable Hilbert basis. More precisely, there are a
countable set $w \subseteq E$ and a Hilbert basis of $E$ indexed by $w$ whose vectors are the
elements of $w$. This is Theorem 5.11 of [brezis2011functional].

The basis is indexed by a subset of the space, as in Mathlib's `exists_hilbertBasis`. The source
gives the basis as a sequence, which a finite-dimensional space cannot have. The form with a
sequence, for an infinite-dimensional space, is `exists_hilbertBasis_nat`. -/
theorem exists_hilbertBasis_countable :
    ∃ (w : Set E) (b : HilbertBasis w 𝕜 E), w.Countable ∧ ⇑b = ((↑) : w → E) := by
  obtain ⟨w, b, hb⟩ := exists_hilbertBasis 𝕜 E
  have hc : Countable w := by
    have := b.orthonormal
    rw [hb] at this
    exact this.countable_of_separableSpace
  exact ⟨w, b, Set.countable_coe_iff.1 hc, hb⟩

/-- Every infinite-dimensional separable Hilbert space $E$ has a Hilbert basis indexed by
$\mathbb{N}$. This is Theorem 5.11 of [brezis2011functional] in the form of the source, a basis
$(e_n)_{n \ge 1}$.

The index set of `exists_hilbertBasis_countable` is countable. It is infinite, because a finite
orthonormal set spans a finite-dimensional subspace, which is closed and hence not dense. -/
theorem exists_hilbertBasis_nat (h : ¬ FiniteDimensional 𝕜 E) : Nonempty (HilbertBasis ℕ 𝕜 E) := by
  obtain ⟨w, b, hwc, hb⟩ := exists_hilbertBasis_countable 𝕜 E
  have hinf : Infinite w := by
    rw [Set.infinite_coe_iff]
    intro hfin
    apply h
    have hspan : Submodule.span 𝕜 w = ⊤ := by
      have hd := b.dense_span
      rw [hb, Subtype.range_coe] at hd
      have : FiniteDimensional 𝕜 (Submodule.span 𝕜 w) := FiniteDimensional.span_of_finite 𝕜 hfin
      rwa [(Submodule.closed_of_finiteDimensional _).submodule_topologicalClosure_eq] at hd
    exact Module.finite_def.2 (by rw [← hspan]; exact Submodule.fg_span hfin)
  have : Countable w := Set.countable_coe_iff.2 hwc
  obtain ⟨e⟩ : Nonempty (Denumerable w) := nonempty_denumerable_iff.2 ⟨inferInstance, hinf⟩
  exact ⟨b.reindex (Denumerable.eqv w)⟩

end Separable

end
