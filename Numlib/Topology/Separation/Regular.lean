/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Topology.Separation.Regular`, beside
`connectedComponent_eq_iInter_isClopen`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Topology.Separation.Regular

/-!
# Splitting a compact set away from a finite set

In a compact Hausdorff space a connected component is the intersection of the clopen sets
containing it (`connectedComponent_eq_iInter_isClopen`). Read inside a compact subset `s` of a
Hausdorff space, finitely many points outside the component of `z` are therefore cut off by one
clopen part of `s`: `s` splits into disjoint compact parts `C ∋ z` and `D ⊇ t`
(`IsCompact.exists_compact_split_of_finite`). This is the topological step of the statement that
every connected component of a pseudospectrum contains an eigenvalue.
-/

open Set

/-- **A connected component of a compact set `s` that misses a finite set `t ⊆ s` lies in a
relatively clopen part of `s` that misses `t`**: `s = C ∪ D` with `C`, `D` compact and disjoint,
`z ∈ C`, `t ⊆ D`. -/
theorem IsCompact.exists_compact_split_of_finite {α : Type*} [TopologicalSpace α] [T2Space α]
    {s t : Set α} (hs : IsCompact s) (ht : t.Finite) (hts : t ⊆ s) {z : α} (hz : z ∈ s)
    (hK : ∀ x ∈ t, x ∉ connectedComponentIn s z) :
    ∃ C D : Set α, IsCompact C ∧ IsCompact D ∧ Disjoint C D ∧ C ∪ D = s ∧ z ∈ C ∧ t ⊆ D := by
  have : CompactSpace s := isCompact_iff_compactSpace.mp hs
  -- for each point of `t`, a clopen subset of `s` containing `z` and not that point
  have hsep : ∀ x : t, ∃ U : Set s, IsClopen U ∧ (⟨z, hz⟩ : s) ∈ U ∧
      (⟨x.1, hts x.2⟩ : s) ∉ U := by
    intro x
    have hnot : (⟨x.1, hts x.2⟩ : s) ∉ connectedComponent (⟨z, hz⟩ : s) := by
      intro hmem
      apply hK x.1 x.2
      rw [connectedComponentIn_eq_image hz]
      exact ⟨_, hmem, rfl⟩
    rw [connectedComponent_eq_iInter_isClopen, mem_iInter] at hnot
    push Not at hnot
    obtain ⟨⟨U, hU, hzU⟩, hxU⟩ := hnot
    exact ⟨U, hU, hzU, hxU⟩
  choose U hU hzU hxU using hsep
  have : Fintype t := ht.fintype
  set V : Set s := ⋂ x ∈ (Finset.univ : Finset t), U x with hV
  have hVc : IsClopen V := isClopen_biInter_finset fun x _ => hU x
  refine ⟨(↑) '' V, (↑) '' Vᶜ, hVc.isClosed.isCompact.image continuous_subtype_val,
    hVc.compl.isClosed.isCompact.image continuous_subtype_val, ?_, ?_, ?_, ?_⟩
  · rw [Set.disjoint_left]
    rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
    exact hb (Subtype.ext hab ▸ ha)
  · rw [← image_union, union_compl_self, image_univ, Subtype.range_coe]
  · exact ⟨⟨z, hz⟩, mem_iInter₂.mpr fun x _ => hzU x, rfl⟩
  · intro x hx
    refine ⟨⟨x, hts hx⟩, fun hmem => ?_, rfl⟩
    exact hxU ⟨x, hx⟩ (mem_iInter₂.mp hmem ⟨x, hx⟩ (Finset.mem_univ _))
