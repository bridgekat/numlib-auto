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

Hilbert sums of closed subspaces and countable Hilbert bases: the projection expansion
`u = ∑ P_{Eᵢ} u` with Bessel–Parseval, the summability of a pairwise orthogonal family of
vectors, and the existence of a countable (or `ℕ`-indexed) Hilbert basis of a separable Hilbert
space. This is [brezis2011functional] §5.4 (Lemma 5.1, Theorem 5.9, Theorem 5.11, Remarks 10
and 11). Everything is over `RCLike 𝕜`, since nothing in the arguments is real.

## Main results

* `summable_iff_summable_norm_sq_of_pairwise_inner_eq_zero` and
  `hasSum_norm_sq_of_pairwise_inner_eq_zero`: a pairwise orthogonal family of vectors is summable
  iff its squared norms are, and the sum satisfies Pythagoras `‖∑ vᵢ‖² = ∑ ‖vᵢ‖²`
  ([brezis2011functional] Lemma 5.1). Mathlib's `OrthogonalFamily.summable_iff_norm_sq_summable`
  is the statement for a family of *subspaces* `V : ∀ i, G i →ₗᵢ E`; the vector form is obtained
  from it with `G i := 𝕜 ∙ v i`.
* `OrthogonalFamily.hasSum_starProjection`: **the projection expansion**. For a family of mutually
  orthogonal subspaces `V i` with orthogonal projections, the projections `(V i).starProjection u`
  sum (unconditionally) to the projection of `u` onto the closure of their span — the sharper form
  of [brezis2011functional] Theorem 5.9 that its proof establishes "even without assumption (b)"
  (its display (26)). Mathlib expands a vector in the coordinates of `lp G 2`
  (`OrthogonalFamily.hasSum_linearIsometry`) but does not identify the `i`-th coordinate with the
  orthogonal projection; this identification is the content here. With density
  (`OrthogonalFamily.hasSum_starProjection_of_dense`) the sum is `u` itself and
  `∑ ‖P_{Eᵢ} u‖² = ‖u‖²` (Bessel–Parseval,
  `OrthogonalFamily.hasSum_norm_sq_starProjection_of_dense`); without it there is Bessel's
  inequality `OrthogonalFamily.tsum_norm_sq_starProjection_le`.
* `Orthonormal.countable_of_separableSpace`: an orthonormal family in a separable space is
  countable — the balls of radius `1/2` around its members are pairwise disjoint, since
  orthonormal vectors are at distance `√2`. Hence `exists_hilbertBasis_countable`
  ([brezis2011functional] Theorem 5.11: every separable Hilbert space has a countable orthonormal
  basis, from Mathlib's Zorn-based `exists_hilbertBasis`) and, in infinite dimension, a basis
  indexed by `ℕ` (`exists_hilbertBasis_nat`, the book's "sequence `(eₙ)_{n ≥ 1}`", which a
  finite-dimensional space cannot have). The converse `HilbertBasis.separableSpace` says a
  countable Hilbert basis makes the space separable (Remark 10's "separable Hilbert spaces are
  exactly those isometric to `ℓ²`", in the countable-basis form).
* `HilbertBasis.reindex`: a Hilbert basis reindexed along an equivalence of index types
  (Mathlib has `OrthonormalBasis.reindex` only).

The book proves Theorem 5.11 by Gram–Schmidt on a dense sequence; the Zorn-plus-counting route is
shorter given `exists_hilbertBasis`.
-/

open Filter Topology
open scoped InnerProductSpace

noncomputable section

variable {ι 𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-! ### Pairwise orthogonal families of vectors -/

section PairwiseOrthogonal

variable {v : ι → E}

/-- The lines `𝕜 ∙ v i` spanned by a pairwise orthogonal family of vectors form an orthogonal
family of subspaces. -/
theorem orthogonalFamily_span_singleton_of_pairwise_inner_eq_zero
    (hv : Pairwise fun i j => ⟪v i, v j⟫_𝕜 = 0) :
    OrthogonalFamily 𝕜 (fun i => (𝕜 ∙ v i)) fun i => (𝕜 ∙ v i).subtypeₗᵢ :=
  orthogonalFamily_iff_pairwise.2 fun i j hij =>
    Submodule.isOrtho_span.2 fun _ hu _ hw => by
      rw [Set.mem_singleton_iff.1 hu, Set.mem_singleton_iff.1 hw]
      exact hv hij

/-- **Pythagoras** for a finite sum of pairwise orthogonal vectors:
`‖∑ i ∈ s, v i‖ ^ 2 = ∑ i ∈ s, ‖v i‖ ^ 2`. -/
theorem norm_sum_sq_of_pairwise_inner_eq_zero (hv : Pairwise fun i j => ⟪v i, v j⟫_𝕜 = 0)
    (s : Finset ι) : ‖∑ i ∈ s, v i‖ ^ 2 = ∑ i ∈ s, ‖v i‖ ^ 2 :=
  (orthogonalFamily_span_singleton_of_pairwise_inner_eq_zero hv).norm_sum
    (fun i => ⟨v i, Submodule.mem_span_singleton_self _⟩) s

/-- A pairwise orthogonal family of vectors in a Hilbert space is (unconditionally) summable if and
only if its squared norms are: the existence clause of [brezis2011functional] Lemma 5.1, for an
arbitrary index type. -/
theorem summable_iff_summable_norm_sq_of_pairwise_inner_eq_zero [CompleteSpace E]
    (hv : Pairwise fun i j => ⟪v i, v j⟫_𝕜 = 0) :
    Summable v ↔ Summable fun i => ‖v i‖ ^ 2 :=
  (orthogonalFamily_span_singleton_of_pairwise_inner_eq_zero hv).summable_iff_norm_sq_summable
    fun i => ⟨v i, Submodule.mem_span_singleton_self _⟩

/-- The sum of a pairwise orthogonal family satisfies `‖S‖ ^ 2 = ∑ ‖v i‖ ^ 2`: the identity
clause of [brezis2011functional] Lemma 5.1 (its display (23)). No completeness is needed. -/
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
/-- The orthogonal projections of a vector onto a family of mutually orthogonal subspaces are
pairwise orthogonal. -/
theorem pairwise_inner_starProjection_eq_zero (u : E) :
    Pairwise fun i j => ⟪(V i).starProjection u, (V j).starProjection u⟫_𝕜 = 0 :=
  fun i j hij => (hV.isOrtho hij).inner_eq ((V i).starProjection_apply_mem u)
    ((V j).starProjection_apply_mem u)

/-- **The projection expansion** ([brezis2011functional] Theorem 5.9, in the form its proof
establishes without any density hypothesis, display (26)): for a family of mutually orthogonal
subspaces `V i` of a Hilbert space, each with an orthogonal projection, the projections
`(V i).starProjection u` of any vector `u` sum unconditionally to the projection of `u` onto the
closure of the span of the family. -/
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

/-- **Bessel–Parseval for the closed span**: the squared norms of the projections sum to the
squared norm of the projection onto the closure of the span. -/
theorem hasSum_norm_sq_starProjection (u : E) :
    HasSum (fun i => ‖(V i).starProjection u‖ ^ 2)
      (‖(⨆ i, V i).topologicalClosure.starProjection u‖ ^ 2) :=
  hasSum_norm_sq_of_pairwise_inner_eq_zero (hV.pairwise_inner_starProjection_eq_zero u)
    (hV.hasSum_starProjection u)

/-- **Bessel's inequality** for an orthogonal family of subspaces:
`∑' i, ‖(V i).starProjection u‖ ^ 2 ≤ ‖u‖ ^ 2`. -/
theorem tsum_norm_sq_starProjection_le (u : E) :
    ∑' i, ‖(V i).starProjection u‖ ^ 2 ≤ ‖u‖ ^ 2 := by
  rw [(hV.hasSum_norm_sq_starProjection u).tsum_eq]
  gcongr
  exact Submodule.norm_starProjection_apply_le _ u

/-- **The Hilbert-sum expansion** ([brezis2011functional] Theorem 5.9): if the mutually orthogonal
subspaces `V i` span a dense subspace, every `u` is the unconditional sum of its projections
`(V i).starProjection u`. -/
theorem hasSum_starProjection_of_dense (hdense : (⨆ i, V i).topologicalClosure = ⊤) (u : E) :
    HasSum (fun i => (V i).starProjection u) u := by
  have h := hV.hasSum_starProjection u
  simp only [hdense, Submodule.starProjection_top, ContinuousLinearMap.id_apply] at h
  exact h

/-- **The Bessel–Parseval identity** ([brezis2011functional] Theorem 5.9, display (20)): if the
mutually orthogonal subspaces `V i` span a dense subspace,
`∑ ‖(V i).starProjection u‖ ^ 2 = ‖u‖ ^ 2`. -/
theorem hasSum_norm_sq_starProjection_of_dense (hdense : (⨆ i, V i).topologicalClosure = ⊤)
    (u : E) : HasSum (fun i => ‖(V i).starProjection u‖ ^ 2) (‖u‖ ^ 2) :=
  hasSum_norm_sq_of_pairwise_inner_eq_zero (hV.pairwise_inner_starProjection_eq_zero u)
    (hV.hasSum_starProjection_of_dense hdense u)

end OrthogonalFamily

/-! ### Countable Hilbert bases -/

/-- Two distinct members of an orthonormal family are at distance `√2`; in particular the balls of
radius `1/2` around them are disjoint. -/
theorem Orthonormal.norm_sub_sq_eq_two {v : ι → E} (hv : Orthonormal 𝕜 v) {i j : ι} (hij : i ≠ j) :
    ‖v i - v j‖ ^ 2 = 2 := by
  rw [norm_sub_sq (𝕜 := 𝕜), hv.1 i, hv.1 j, hv.2 hij]
  norm_num

/-- An orthonormal family in a separable space is countable ([brezis2011functional] Theorem
5.11, the counting step): the balls of radius `1/2` around its members are pairwise disjoint,
nonempty and open. No completeness is needed. -/
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

/-- A Hilbert basis reindexed along an equivalence of index types: `b.reindex e = b ∘ e.symm`. -/
protected def reindex {ι' : Type*} (b : HilbertBasis ι 𝕜 E) (e : ι ≃ ι') :
    HilbertBasis ι' 𝕜 E :=
  HilbertBasis.mk (b.orthonormal.comp e.symm e.symm.injective) (by
    rw [Set.range_comp, Equiv.range_eq_univ, Set.image_univ]
    exact b.dense_span.ge)

/-- The vectors of a reindexed Hilbert basis. -/
@[simp]
theorem coe_reindex {ι' : Type*} (b : HilbertBasis ι 𝕜 E) (e : ι ≃ ι') :
    ⇑(b.reindex e) = ⇑b ∘ e.symm :=
  HilbertBasis.coe_mk _ _

/-- A reindexed Hilbert basis evaluated at an index. -/
theorem reindex_apply {ι' : Type*} (b : HilbertBasis ι 𝕜 E) (e : ι ≃ ι') (i' : ι') :
    b.reindex e i' = b (e.symm i') := by
  rw [coe_reindex, Function.comp_apply]

omit [CompleteSpace E] in
/-- A Hilbert space with a countable Hilbert basis is separable: the converse of
`exists_hilbertBasis_countable` ([brezis2011functional] Chapter 5, Remark 10). -/
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

/-- **Every separable Hilbert space has a countable orthonormal basis** ([brezis2011functional]
Theorem 5.11), indexed by a countable subset of the space as in Mathlib's `exists_hilbertBasis`.
The book's basis is a *sequence*, which a finite-dimensional space cannot have; the sequence form
under infinite dimension is `exists_hilbertBasis_nat`. -/
theorem exists_hilbertBasis_countable :
    ∃ (w : Set E) (b : HilbertBasis w 𝕜 E), w.Countable ∧ ⇑b = ((↑) : w → E) := by
  obtain ⟨w, b, hb⟩ := exists_hilbertBasis 𝕜 E
  have hc : Countable w := by
    have := b.orthonormal
    rw [hb] at this
    exact this.countable_of_separableSpace
  exact ⟨w, b, Set.countable_coe_iff.1 hc, hb⟩

/-- **Every infinite-dimensional separable Hilbert space has a Hilbert basis indexed by `ℕ`**
([brezis2011functional] Theorem 5.11 in the book's own form, a basis `(eₙ)_{n ≥ 1}`). The index set
of `exists_hilbertBasis_countable` is countable, and infinite because a finite orthonormal set
spans a finite-dimensional, hence closed, subspace, which then could not be dense. -/
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
