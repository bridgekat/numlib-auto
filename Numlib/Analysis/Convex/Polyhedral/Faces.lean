import Numlib.Analysis.Convex.Polyhedral.Ops
import Numlib.Analysis.Convex.Representation

/-!
# Finite generation and a finite set of faces

A closed convex set has only finitely many faces exactly when it is finitely generated. This is
the third description of a polyhedral convex set: `Polyhedral/Defs.lean` identifies "polyhedral"
with "finitely generated", and this module adds "closed, with a finite set of faces".

## Main results

* `FinitelyGenerated.finite_setOf_isFace`, `FinitelyGenerated.of_isFace` — a finitely generated
  set has finitely many faces, each of them finitely generated. Both come from the description of
  a face as the hull of the generating points it contains and the generating directions in which
  it recedes, so the faces are indexed by pairs of subsets of the generators.
* `finitelyGenerated_of_finite_setOf_isFace`, `polyhedral_of_finite_setOf_isFace` — the converse
  for a closed convex set, by way of the lineality-zero case
  `finitelyGenerated_of_finite_setOf_isFace_of_containsNoLine`.
* `polyhedral_iff_isClosed_finite_setOf_isFace` — the characterisation the two halves give.

## Implementation notes

Extreme directions are counted as rays, not as vectors: `extremeDirections C` is closed under
positive rescaling and so is never finite. What a finite face set bounds is the number of
half-line faces, and `exists_finite_generating_extremeDirections` turns that bound into a finite
generating set by choosing a direction vector for each half-line face.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §18 and §19.
-/

open Set

open scoped Pointwise

namespace ConvexAnalysis

/-! ### Counting extreme points and extreme directions -/

section Counting

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {C : Set E}

/-- **A set with finitely many faces has finitely many extreme points**, because the extreme
points are exactly the singleton faces (`isFace_singleton`). -/
theorem finite_extremePoints_of_finite_setOf_isFace
    (hfin : {C' : Set E | IsFace C C'}.Finite) : (C.extremePoints ℝ).Finite := by
  refine Set.Finite.of_finite_image (hfin.subset ?_) Set.singleton_injective.injOn
  rintro _ ⟨x, hx, rfl⟩
  exact isFace_singleton.2 hx

/-- **A set with finitely many faces has finitely many extreme rays**: there is a finite subset of
`extremeDirections C` generating all of it as a pointed cone. Every extreme direction is the
direction of a half-line face, and every generator of one lies in that face's recession cone. -/
theorem exists_finite_generating_extremeDirections
    (hfin : {C' : Set E | IsFace C C'}.Finite) :
    ∃ D : Set E, D.Finite ∧ D ⊆ extremeDirections C ∧
      extremeDirections C ⊆ (PointedCone.hull ℝ D : Set E) := by
  classical
  have hchoice : ∀ C' : Set E, ∃ y : E,
      (∃ x : E, y ≠ 0 ∧ C' = halfLine x y) ∨ ∀ x z : E, z ≠ 0 → C' ≠ halfLine x z := by
    intro C'
    by_cases h : ∃ x z : E, z ≠ 0 ∧ C' = halfLine x z
    · obtain ⟨x, z, hz, he⟩ := h
      exact ⟨z, Or.inl ⟨x, hz, he⟩⟩
    · exact ⟨0, Or.inr fun x z hz he => h ⟨x, z, hz, he⟩⟩
  choose g hg using hchoice
  refine ⟨g '' {C' : Set E | IsFace C C'} ∩ extremeDirections C,
    (hfin.image g).subset Set.inter_subset_left, Set.inter_subset_right, ?_⟩
  rintro y ⟨hy, x, hface⟩
  rcases hg (halfLine x y) with ⟨x', hg0, hx'⟩ | hno
  · have hgmem : g (halfLine x y) ∈
        g '' {C' : Set E | IsFace C C'} ∩ extremeDirections C := by
      refine ⟨⟨halfLine x y, hface, rfl⟩, hg0, x', ?_⟩
      rw [← hx']
      exact hface
    have hrec : y ∈ recessionCone (halfLine x' (g (halfLine x y))) := by
      rw [← hx']
      exact mem_recessionCone_halfLine x y
    rw [recessionCone_halfLine] at hrec
    obtain ⟨a, ha, hya⟩ := hrec
    have hone : y ∈ (PointedCone.hull ℝ ({g (halfLine x y)} : Set E) : Set E) := by
      rw [coe_coneHull_singleton]
      exact ⟨a, ha, hya⟩
    exact Submodule.span_mono (Set.singleton_subset_iff.2 hgmem) hone
  · exact absurd rfl (hno x y hy)

/-- **A finitely generated set has only finitely many extreme points.**
`extremePoints_convexHullPD_subset` puts every extreme point among the generating *points*, so a
`Finset` of generators bounds them. Nothing here is finite-dimensional or even normed. -/
theorem FinitelyGenerated.finite_extremePoints (hC : FinitelyGenerated C) :
    (C.extremePoints ℝ).Finite := by
  obtain ⟨P, D, hPD⟩ := hC
  have hPD' : C = convexHullPD (P : Set E) (D : Set E) := hPD
  rw [hPD']
  exact finite_extremePoints_convexHullPD P D

end Counting

/-! ### The faces of a finitely generated set -/

section Generated

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {C C' : Set E}

/-- **A face of a finitely generated set is finitely generated.** The face is the hull of the
generating points it contains and the generating directions in which it recedes, both of which
are a `Finset.filter` of the original generators. -/
theorem FinitelyGenerated.of_isFace (hC : FinitelyGenerated C) (hface : IsFace C C') :
    FinitelyGenerated C' := by
  classical
  obtain ⟨P, D, hPD⟩ := hC
  have hPD' : C = convexHullPD (P : Set E) (D : Set E) := hPD
  rw [hPD'] at hface
  refine ⟨P.filter (· ∈ C'), D.filter (· ∈ recessionCone C'), ?_⟩
  have hp : ((P.filter (· ∈ C') : Finset E) : Set E) = (P : Set E) ∩ C' := by
    ext z; simp
  have hd : ((D.filter (· ∈ recessionCone C') : Finset E) : Set E)
      = {y ∈ (D : Set E) | y ∈ recessionCone C'} := by
    ext z; simp
  rw [← convexHullPD_def, hp, hd]
  exact hface.eq_convexHullPD

/-- **A finitely generated set has only finitely many faces**, the same description making the
face map factor through the pairs of subsets of the two generating sets. -/
theorem FinitelyGenerated.finite_setOf_isFace (hC : FinitelyGenerated C) :
    {C' : Set E | IsFace C C'}.Finite := by
  classical
  obtain ⟨P, D, hPD⟩ := hC
  have hPD' : C = convexHullPD (P : Set E) (D : Set E) := hPD
  refine Set.Finite.subset (Set.Finite.image
    (fun q : Finset E × Finset E => convexHullPD (q.1 : Set E) (q.2 : Set E))
    (P.powerset ×ˢ D.powerset).finite_toSet) ?_
  rintro C' hC'
  have hface : IsFace (convexHullPD (P : Set E) (D : Set E)) C' := hPD' ▸ hC'
  have hp : ((P.filter (· ∈ C') : Finset E) : Set E) = (P : Set E) ∩ C' := by
    ext z; simp
  have hd : ((D.filter (· ∈ recessionCone C') : Finset E) : Set E)
      = {y ∈ (D : Set E) | y ∈ recessionCone C'} := by
    ext z; simp
  refine ⟨(P.filter (· ∈ C'), D.filter (· ∈ recessionCone C')), ?_, ?_⟩
  · exact Finset.mem_coe.2 (Finset.mem_product.2
      ⟨Finset.mem_powerset.2 (Finset.filter_subset _ _),
        Finset.mem_powerset.2 (Finset.filter_subset _ _)⟩)
  · change convexHullPD ((P.filter (· ∈ C') : Finset E) : Set E)
      ((D.filter (· ∈ recessionCone C') : Finset E) : Set E) = C'
    rw [hp, hd]
    exact hface.eq_convexHullPD.symm

theorem Polyhedral.of_isFace (hC : Polyhedral C) (hface : IsFace C C') : Polyhedral C' :=
  (hC.finitelyGenerated.of_isFace hface).polyhedral

theorem Polyhedral.finite_setOf_isFace (hC : Polyhedral C) :
    {C' : Set E | IsFace C C'}.Finite :=
  hC.finitelyGenerated.finite_setOf_isFace

end Generated

/-! ### Finitely many faces forces finite generation -/

section FiniteFaces

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {C : Set E}

/-- **A closed convex set containing no lines and having only finitely many faces is finitely
generated.** The set is the hull of its extreme points and extreme directions, a finite face set
bounds both, and replacing the extreme directions by a finite generating set keeps the hull. -/
theorem finitelyGenerated_of_finite_setOf_isFace_of_containsNoLine (hC : Convex ℝ C)
    (hCcl : IsClosed C) (hnl : ContainsNoLine C)
    (hfin : {C' : Set E | IsFace C C'}.Finite) : FinitelyGenerated C := by
  classical
  obtain ⟨D, hDfin, hDsub, hDcov⟩ := exists_finite_generating_extremeDirections hfin
  have hPfin := finite_extremePoints_of_finite_setOf_isFace hfin
  have hrepr := convexHullPD_extremePoints_extremeDirections hC hCcl hnl
  refine ⟨hPfin.toFinset, hDfin.toFinset, ?_⟩
  rw [hPfin.coe_toFinset, hDfin.coe_toFinset, ← convexHullPD_def]
  refine Set.Subset.antisymm (Set.Subset.trans hrepr.ge ?_)
    (Set.Subset.trans (convexHullPD_mono_right _ hDsub) hrepr.subset)
  exact Set.Subset.trans (convexHullPD_mono_right _ hDcov)
    (convexHullPD_coneHull _ _).subset

/-- **A closed convex set with only finitely many faces is polyhedral.** Rockafellar's reduction to
lineality zero: with `N` the lineality space and `M` a complement, `C = N + (C ∩ M)`, the faces of
`C ∩ M` correspond to those of `C`, and `C ∩ M` contains no lines because a line inside it would
have its direction in `N ⊓ M = ⊥`. So `C ∩ M` is finitely generated and `C` is a sum of two
polyhedral sets. -/
theorem polyhedral_of_finite_setOf_isFace (hC : Convex ℝ C) (hCcl : IsClosed C)
    (hfin : {C' : Set E | IsFace C C'}.Finite) : Polyhedral C := by
  classical
  obtain ⟨M, hcompl⟩ := (linealitySubmodule C).exists_isCompl
  have hN : ((linealitySubmodule C : Submodule ℝ E) : Set E) ⊆ linealitySpace C :=
    (coe_linealitySubmodule C).subset
  have hdec : C = ((linealitySubmodule C : Submodule ℝ E) : Set E) + (C ∩ (M : Set E)) :=
    eq_add_inter_of_isCompl_of_le hN hcompl
  have hC₀nl : ContainsNoLine (C ∩ (M : Set E)) := by
    intro x y hy
    by_contra hall
    push Not at hall
    have hyL : y ∈ linealitySpace C :=
      mem_linealitySpace_of_forall_add_smul_mem hC hCcl fun t => (hall t).1
    have h0 : x + (0 : ℝ) • y ∈ M := (hall 0).2
    have h1 : x + (1 : ℝ) • y ∈ M := (hall 1).2
    have hsub : (x + (1 : ℝ) • y) - (x + (0 : ℝ) • y) ∈ M := M.sub_mem h1 h0
    have heq : (x + (1 : ℝ) • y) - (x + (0 : ℝ) • y) = y := by module
    rw [heq] at hsub
    exact hy ((Submodule.disjoint_def.1 hcompl.disjoint) y
      (mem_linealitySubmodule.2 hyL) hsub)
  have hfin₀ : {C₀ : Set E | IsFace (C ∩ (M : Set E)) C₀}.Finite := by
    have h1 : Finite {C' : Set E // IsFace C C'} := hfin.to_subtype
    have h2 : Finite {C₀ : Set E // IsFace (C ∩ (M : Set E)) C₀} :=
      Finite.of_equiv _ (isFaceEquivInter hN hcompl)
    have h3 : Finite ↥{C₀ : Set E | IsFace (C ∩ (M : Set E)) C₀} := h2
    exact Set.toFinite _
  have hC₀ : FinitelyGenerated (C ∩ (M : Set E)) :=
    finitelyGenerated_of_finite_setOf_isFace_of_containsNoLine (hC.inter M.convex)
      (hCcl.inter M.closed_of_finiteDimensional) hC₀nl hfin₀
  have hsum : Polyhedral (((linealitySubmodule C : Submodule ℝ E) : Set E)
      + (C ∩ (M : Set E))) :=
    (polyhedral_coe_submodule _).add hC₀.polyhedral
  rwa [← hdec] at hsum

/-- **A closed convex set with only finitely many faces is finitely generated.** -/
theorem finitelyGenerated_of_finite_setOf_isFace (hC : Convex ℝ C) (hCcl : IsClosed C)
    (hfin : {C' : Set E | IsFace C C'}.Finite) : FinitelyGenerated C :=
  (polyhedral_of_finite_setOf_isFace hC hCcl hfin).finitelyGenerated

/-- **A convex set is polyhedral exactly when it is closed and has only finitely many faces.**
Together with `polyhedral_iff_finitelyGenerated` this is the full three-way characterisation. -/
theorem polyhedral_iff_isClosed_finite_setOf_isFace (hC : Convex ℝ C) :
    Polyhedral C ↔ IsClosed C ∧ {C' : Set E | IsFace C C'}.Finite :=
  ⟨fun h => ⟨h.isClosed, h.finite_setOf_isFace⟩,
    fun h => polyhedral_of_finite_setOf_isFace hC h.1 h.2⟩

theorem finitelyGenerated_iff_isClosed_finite_setOf_isFace (hC : Convex ℝ C) :
    FinitelyGenerated C ↔ IsClosed C ∧ {C' : Set E | IsFace C C'}.Finite := by
  rw [← polyhedral_iff_finitelyGenerated]
  exact polyhedral_iff_isClosed_finite_setOf_isFace hC

end FiniteFaces

end ConvexAnalysis
