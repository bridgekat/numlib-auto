/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
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

Let $s$ be a compact subset of a Hausdorff space, let $z \in s$, and let $t \subseteq s$ be a finite
set with no point in the connected component of $z$ in $s$. This file proves that $s$ splits into
two disjoint compact parts $C$ and $D$ with $z \in C$ and $t \subseteq D$. This is the topological
step in the proof that every connected component of a pseudospectrum contains an eigenvalue.

## Main results

* `IsCompact.exists_compact_split_of_finite`: $s = C \cup D$ with $C$ and $D$ compact and disjoint,
  $z \in C$ and $t \subseteq D$.

## Proof outline

In a compact Hausdorff space, a connected component is the intersection of the sets that are both
open and closed and contain it (`connectedComponent_eq_iInter_isClopen`). Apply this in the compact
space $s$. Each of the finitely many points of $t$ lies outside some relatively clopen subset of $s$
that contains $z$. The intersection of these finitely many sets is a relatively clopen set $C$; its
complement $D$ in $s$ contains $t$.
-/

open Set

/-- Let $\alpha$ be a Hausdorff topological space, let $s \subseteq \alpha$ be compact, let
$t \subseteq s$ be finite, and let $z \in s$. Assume that no point of $t$ lies in the connected
component of $z$ in $s$. Then there are compact sets $C, D \subseteq \alpha$ such that
$$C \cap D = \emptyset, \qquad C \cup D = s, \qquad z \in C, \qquad t \subseteq D.$$

The sets $C$ and $D$ are closed in $s$ and complementary in $s$, so both are open and closed in
$s$. Hence the connected component of $z$ in $s$ lies in $C$, although the statement does not
say this. The component is `connectedComponentIn s z`. -/
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
