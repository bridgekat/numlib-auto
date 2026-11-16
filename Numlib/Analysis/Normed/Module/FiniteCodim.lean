/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural homes: `Mathlib.Topology.Algebra.Module.FiniteDimension` (the complement lemmas) and
`Mathlib.Analysis.Normed.Module.DoubleDual` (the dimension of the strong dual).
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.LocallyConvex.HahnBanach
import Mathlib.Analysis.Normed.Module.Complemented
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.Finiteness.Cofinite
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Finite-dimensional and finite-codimensional subspaces of a normed space

This file proves the facts on complements and dimensions of §11.1 of [brezis2011functional] that
Mathlib does not have. Let $E$ be a normed space. A subspace $M$ of $E$ is **complemented** if there
is a continuous linear projection of $E$ onto $M$, or equivalently, if $M$ is closed and there is a
closed subspace $N$ with $M \oplus N = E$. The file shows that a normed space and its dual have the
same finite dimension, that for a closed subspace $M$ and a finite-dimensional subspace $X$ the sum
$M + X$ is complemented if and only if $M$ is complemented, that a closed subspace of finite
codimension has an algebraic complement inside any dense subspace, and that in a Banach space two
closed subspaces $G$, $L$ with $G + L$ of finite codimension and $G \cap L$ finite-dimensional are
complemented.

## Main results

* `NormedSpace.finrank_strongDual`: if $E$ is finite-dimensional, then $\dim E^* = \dim E$.
* `NormedSpace.finiteDimensional_of_finiteDimensional_strongDual`: if the dual $E^*$ is
  finite-dimensional, then $E$ is finite-dimensional (Proposition 11.3 of [brezis2011functional]).
* `Submodule.ClosedComplemented.sup_finiteDimensional`: if $M$ is complemented and $X$ is
  finite-dimensional, then $M + X$ is complemented.
* `Submodule.ClosedComplemented.of_sup_finiteDimensional`: if $M$ is closed, $X$ is
  finite-dimensional and $M + X$ is complemented, then $M$ is complemented.
* `Submodule.closedComplemented_sup_finiteDimensional_iff`: for $M$ closed and $X$
  finite-dimensional, $M + X$ is complemented if and only if $M$ is complemented (the second clause
  of Proposition 11.4 of [brezis2011functional]).
* `Submodule.exists_isCompl_le_of_dense`: a closed subspace of finite codimension has an algebraic
  complement inside any dense subspace $D$ (Proposition 11.6 of [brezis2011functional]).
* `Submodule.closedComplemented_of_disjoint_of_sup_sup_eq_top`: in a Banach space, closed subspaces
  $G$, $L$ with $G \cap L = 0$ and $G + L + X_1 = E$ for a finite-dimensional $X_1$ are
  complemented.
* `Submodule.closedComplemented_of_sup_sup_eq_top_of_inf_le`: in a Banach space, closed subspaces
  $G$, $L$ with $G + L + X_1 = E$ and $G \cap L \subseteq X_2$ for finite-dimensional $X_1$, $X_2$
  are complemented (Proposition 11.7 of [brezis2011functional]). This is the bookkeeping behind the
  statement "$I - T$ has index zero" of the Fredholm alternative in Chapter 6 of
  [brezis2011functional].

## Proof outline

For the "if" direction of Proposition 11.4, the complement of $M + X$ is built from a complement $N$
of $M$: the projection of $X$ into $N$ is finite-dimensional, so it has a complement inside $N$. For
the "only if" direction, $M$ has finite codimension inside $M + X$, so the projection of $M + X$
onto $M$ is automatically continuous, and its composition with a continuous projection onto $M + X$
is a continuous projection onto $M$. Neither direction needs $E$ to be complete. For Proposition
11.6, the subspace $M + D$ is closed because it contains the closed subspace $M$ of finite
codimension, and it is dense because it contains $D$. Hence $M + D = E$, and a complement of
$M \cap D$ inside $D$ is a complement of $M$. No induction on the codimension is needed.

## Implementation notes

* Most of §11.1 of [brezis2011functional] is in Mathlib, and it is not proved again here: a
  finite-dimensional subspace is closed (`Submodule.closed_of_finiteDimensional`, Proposition 11.1),
  every linear map from a finite-dimensional space is continuous
  (`LinearMap.continuous_of_finiteDimensional`, Proposition 11.2), the sum of a closed subspace and
  a finite-dimensional subspace is closed (`Submodule.isClosed_sup_finiteDimensional`, the first
  clause of Proposition 11.4), and a subspace that contains a closed subspace of finite codimension
  is closed (`Submodule.isClosed_mono_of_finiteDimensional_quotient`, Proposition 11.5).
* Mathlib also has the one-directional complement facts: a finite-dimensional subspace is
  complemented (`Submodule.ClosedComplemented.of_finiteDimensional`, by the Hahn–Banach theorem), a
  closed subspace of finite codimension is complemented
  (`Submodule.ClosedComplemented.of_finiteDimensional_quotient`), and in a Banach space a closed
  algebraic complement is a topological complement
  (`Submodule.ClosedComplemented.of_isCompl_isClosed`).
* "Finite codimension" is `Submodule.CoFG`, that is, `M.CoFG` is `Module.Finite 𝕜 (E ⧸ M)`. The
  lemmas `Submodule.FG.cofg_of_codisjoint` and `Submodule.CoFG.fg_of_isCompl` relate it to the
  condition "$M + X = E$ for a finite-dimensional $X$" of [brezis2011functional].
* "Complemented" is `Submodule.ClosedComplemented`, the existence of a continuous linear projection
  onto $M$. It is equivalent to the definition of [brezis2011functional], a closed subspace $N$ with
  $M \oplus N = E$, by `Submodule.closedComplemented_iff_isClosed_exists_isClosed_isCompl`.
* The scalars are `RCLike 𝕜` exactly where the Hahn–Banach theorem is used: Proposition 11.3, the
  "if" direction of Proposition 11.4, and Step 2 of Proposition 11.7. Elsewhere the scalar field is
  any complete nontrivially normed field. Completeness of $E$ is assumed only in Proposition 11.7,
  where the open mapping theorem shows that a closed algebraic complement is a topological
  complement.
-/

open Module

section Dual

/-- Let $\mathbb{K}$ be a complete nontrivially normed field and let $E$ be a finite-dimensional
normed space over $\mathbb{K}$. Then the dual $E^*$ of continuous linear functionals has the
same dimension as $E$: $$\dim E^* = \dim E.$$ This is stated in §11.1 of [brezis2011functional],
in the paragraph before Proposition 11.3.

The dual $E^*$ is `StrongDual 𝕜 E`. Every linear functional on $E$ is continuous, so $E^*$ is
linearly equivalent to the algebraic dual, whose dimension is that of $E$. -/
theorem NormedSpace.finrank_strongDual {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E] :
    finrank 𝕜 (StrongDual 𝕜 E) = finrank 𝕜 E := by
  rw [← Subspace.dual_finrank_eq (K := 𝕜) (V := E)]
  exact (LinearMap.toContinuousLinearMap (𝕜 := 𝕜) (E := E) (F' := 𝕜)).symm.finrank_eq

/-- Let $E$ be a normed space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$. If the dual $E^*$ is
finite-dimensional, then $E$ is finite-dimensional. This is Proposition 11.3 of
[brezis2011functional].

[brezis2011functional] assumes that $E$ is a Banach space. Completeness is not needed here. The
bidual $E^{**}$ is finite-dimensional, and the canonical embedding of $E$ into $E^{**}$ is
injective because it is an isometry; this is where the Hahn–Banach theorem enters. The
dimensions agree by `NormedSpace.finrank_strongDual`. -/
theorem NormedSpace.finiteDimensional_of_finiteDimensional_strongDual {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 (StrongDual 𝕜 E)] :
    FiniteDimensional 𝕜 E :=
  FiniteDimensional.of_injective (NormedSpace.inclusionInDoubleDual 𝕜 E).toLinearMap
    (NormedSpace.inclusionInDoubleDualLi 𝕜 (E := E)).injective

end Dual

namespace Submodule

section SupRCLike

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Let $E$ be a normed space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, let $M$ be a
complemented subspace of $E$, and let $X$ be a finite-dimensional subspace of $E$. Then $M + X$
is complemented. This is the "if" half of the second clause of Proposition 11.4 of
[brezis2011functional].

Completeness of $E$ is not needed. Let $N$ be a topological complement of $M$, with projections
$P_M$ and $P_N$. The finite-dimensional subspace $X' = P_N(X)$ of $N$ has a continuous
projection $R$ of $N$ onto it, by the Hahn–Banach theorem in $N$. Then $P_M + R \circ P_N$ is a
continuous projection of $E$ onto $M + X' = M + X$. -/
theorem ClosedComplemented.sup_finiteDimensional {M : Submodule 𝕜 E}
    (hM : M.ClosedComplemented) (X : Submodule 𝕜 E) [FiniteDimensional 𝕜 X] :
    (M ⊔ X).ClosedComplemented := by
  obtain ⟨N, hN⟩ := hM.exists_isTopCompl
  set X' : Submodule 𝕜 N := X.map (N.projectionOntoL M hN.symm : E →ₗ[𝕜] N)
  obtain ⟨R, hR⟩ := ClosedComplemented.of_finiteDimensional X'
  set g : E →L[𝕜] E :=
    M.projectionL N hN + N.subtypeL ∘L X'.subtypeL ∘L R ∘L N.projectionOntoL M hN.symm with hg
  -- the values of `g` lie in `M ⊔ X`
  have hmem : ∀ x, g x ∈ M ⊔ X := by
    intro x
    obtain ⟨z, hz, hzR⟩ := mem_map.1 (R (N.projectionOntoL M hN.symm x)).2
    rw [ContinuousLinearMap.coe_coe] at hzR
    have hz' : ((N.projectionOntoL M hN.symm z : N) : E) = z - M.projectionL N hN z := by
      rw [coe_projectionOntoL_apply, projectionL_eq_self_sub_projectionL]
    refine mem_sup.2 ⟨M.projectionL N hN x - M.projectionL N hN z,
      M.sub_mem (projectionL_apply_mem hN x) (projectionL_apply_mem hN z), z, hz, ?_⟩
    simp only [hg, add_apply, ContinuousLinearMap.comp_apply, subtypeL_apply]
    rw [← hzR, hz']
    abel
  refine ⟨g.codRestrict (M ⊔ X) hmem, fun y => ?_⟩
  apply Subtype.ext
  change g (y : E) = y
  obtain ⟨m, hm, x, hx, hy⟩ := mem_sup.1 y.2
  rw [← hy]
  have hPNm : N.projectionOntoL M hN.symm m = 0 :=
    N.projectionOntoL_apply_eq_zero_of_mem_right hN.symm hm
  have hPNx : N.projectionOntoL M hN.symm x ∈ X' := mem_map_of_mem hx
  have hRx : R (N.projectionOntoL M hN.symm x) = ⟨_, hPNx⟩ := hR ⟨_, hPNx⟩
  have hPMm : M.projectionL N hN m = m := projectionL_apply_left hN ⟨m, hm⟩
  simp only [hg, add_apply, ContinuousLinearMap.comp_apply, map_add, hPNm, hRx, subtypeL_apply,
    hPMm, coe_projectionOntoL_apply, map_zero, add_zero,
    projectionL_add_projectionL_eq_self]

end SupRCLike

section Sup

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E]

/-- Let $\mathbb{K}$ be a complete nontrivially normed field, let $E$ be a normed space over
$\mathbb{K}$, let $M$ be a closed subspace of $E$, and let $X$ be a finite-dimensional subspace
of $E$. If $M + X$ is complemented, then $M$ is complemented. This is the "only if" half of the
second clause of Proposition 11.4 of [brezis2011functional].

Completeness of $E$ is not needed. The subspace $M$ has finite codimension in $M + X$, so the
projection of $M + X$ onto $M$ along any algebraic complement is continuous
(`Submodule.ClosedComplemented.of_finiteDimensional_quotient`). Its composition with a
continuous projection of $E$ onto $M + X$ is a continuous projection onto $M$. -/
theorem ClosedComplemented.of_sup_finiteDimensional {M : Submodule 𝕜 E}
    (hM : IsClosed (M : Set E)) (X : Submodule 𝕜 E) [FiniteDimensional 𝕜 X]
    (h : (M ⊔ X).ClosedComplemented) : M.ClosedComplemented := by
  obtain ⟨f, hf⟩ := h
  let M' : Submodule 𝕜 ↥(M ⊔ X) := M.comap (M ⊔ X).subtype
  let X' : Submodule 𝕜 ↥(M ⊔ X) := X.comap (M ⊔ X).subtype
  have hM'c : IsClosed (M' : Set ↥(M ⊔ X)) := hM.preimage continuous_subtype_val
  have hX'f : FiniteDimensional 𝕜 X' :=
    (comapSubtypeEquivOfLe (le_sup_right : X ≤ M ⊔ X)).symm.finiteDimensional
  have hcod : Codisjoint M' X' := by
    rw [codisjoint_iff, eq_top_iff]
    rintro ⟨y, hy⟩ -
    obtain ⟨m, hm, x, hx, rfl⟩ := mem_sup.1 hy
    exact mem_sup.2 ⟨⟨m, mem_sup_left hm⟩, hm, ⟨x, mem_sup_right hx⟩, hx, rfl⟩
  have : FiniteDimensional 𝕜 (↥(M ⊔ X) ⧸ M') :=
    FG.cofg_of_codisjoint hcod.symm (Module.Finite.iff_fg.1 hX'f)
  obtain ⟨g, hg⟩ := ClosedComplemented.of_finiteDimensional_quotient hM'c
  refine ⟨((M ⊔ X).subtypeL ∘L M'.subtypeL ∘L g ∘L f).codRestrict M fun x => (g (f x)).2,
    fun y => ?_⟩
  apply Subtype.ext
  have hfy : f (y : E) = ⟨y, mem_sup_left y.2⟩ := hf ⟨y, mem_sup_left y.2⟩
  have hgy : g (⟨⟨y, mem_sup_left y.2⟩, y.2⟩ : M') = ⟨⟨y, mem_sup_left y.2⟩, y.2⟩ := hg _
  change ((g (f (y : E)) : ↥(M ⊔ X)) : E) = y
  rw [hfy, hgy]

/-- Let $E$ be a normed space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, let $M$ be a closed
subspace of $E$, and let $X$ be a finite-dimensional subspace of $E$. Then $M + X$ is
complemented if and only if $M$ is complemented. This is the second clause of Proposition 11.4
of [brezis2011functional].

The two directions are `Submodule.ClosedComplemented.sup_finiteDimensional` and
`Submodule.ClosedComplemented.of_sup_finiteDimensional`. -/
theorem closedComplemented_sup_finiteDimensional_iff {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {M : Submodule 𝕜 E} (hM : IsClosed (M : Set E))
    (X : Submodule 𝕜 E) [FiniteDimensional 𝕜 X] :
    (M ⊔ X).ClosedComplemented ↔ M.ClosedComplemented :=
  ⟨ClosedComplemented.of_sup_finiteDimensional hM X, fun h => h.sup_finiteDimensional X⟩

end Sup

section Dense

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E]

/-- Let $\mathbb{K}$ be a complete nontrivially normed field, let $E$ be a normed space over
$\mathbb{K}$, let $M$ be a closed subspace of $E$ of finite codimension, and let $D$ be a dense
subspace of $E$. Then there is a subspace $X \subseteq D$ with $M \oplus X = E$ as an algebraic
direct sum. This is Proposition 11.6 of [brezis2011functional].

The complement $X$ is automatically finite-dimensional (`Submodule.CoFG.fg_of_isCompl`) and a
topological complement (`Submodule.IsCompl.isTopCompl_of_finiteDimensional_quotient`). For the
proof, $M + D$ is closed because it contains the closed subspace $M$ of finite codimension, and
it contains the dense subspace $D$, so $M + D = E$. A complement $X$ of $M \cap D$ inside $D$ is
then a complement of $M$ in $E$, by the modular law. -/
theorem exists_isCompl_le_of_dense {M : Submodule 𝕜 E} (hM : IsClosed (M : Set E)) [M.CoFG]
    {D : Submodule 𝕜 E} (hD : Dense (D : Set E)) :
    ∃ X : Submodule 𝕜 E, X ≤ D ∧ IsCompl M X := by
  have hMD : M ⊔ D = ⊤ := by
    have hcl : IsClosed ((M ⊔ D : Submodule 𝕜 E) : Set E) :=
      isClosed_mono_of_finiteDimensional_quotient hM le_sup_left
    rw [eq_top_iff]
    rintro y -
    have hsub : (D : Set E) ⊆ (M ⊔ D : Submodule 𝕜 E) := fun d hd => mem_sup_right hd
    exact closure_minimal hsub hcl (hD y)
  obtain ⟨X, hdisj, hsup⟩ :=
    IsModularLattice.exists_disjoint_and_sup_eq (inf_le_right : M ⊓ D ≤ D)
  have hXD : X ≤ D := hsup ▸ le_sup_right
  refine ⟨X, hXD, ?_, ?_⟩
  · rw [disjoint_iff, ← inf_eq_right.2 hXD, ← inf_assoc]
    exact hdisj.eq_bot
  · rw [codisjoint_iff, ← hMD, ← hsup, ← sup_assoc, sup_inf_self]

end Dense

section Fredholm

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [CompleteSpace E]

/-- Let $\mathbb{K}$ be a complete nontrivially normed field and let $E$ be a Banach space over
$\mathbb{K}$. Let $G$ and $L$ be closed subspaces of $E$ with $G \cap L = \{0\}$, and let $X_1$
be a finite-dimensional subspace with $G + L + X_1 = E$. Then $G$ is complemented. This is Step
1 of the proof of Proposition 11.7 of [brezis2011functional], the case $X_2 = 0$.

The hypotheses are symmetric in $G$ and $L$, so $L$ is complemented as well. Let $\tilde X_1$ be
a complement of $(G + L) \cap X_1$ inside $X_1$. Then $L + \tilde X_1$ is closed and is an
algebraic complement of $G$, and in a Banach space a closed algebraic complement is a
topological complement. -/
theorem closedComplemented_of_disjoint_of_sup_sup_eq_top {G L : Submodule 𝕜 E}
    (hG : IsClosed (G : Set E)) (hL : IsClosed (L : Set E)) (hGL : Disjoint G L)
    (X₁ : Submodule 𝕜 E) [FiniteDimensional 𝕜 X₁] (hsup : G ⊔ L ⊔ X₁ = ⊤) :
    G.ClosedComplemented := by
  obtain ⟨Y, hdisj, hY⟩ :=
    IsModularLattice.exists_disjoint_and_sup_eq (inf_le_right : (G ⊔ L) ⊓ X₁ ≤ X₁)
  have hYX : Y ≤ X₁ := hY ▸ le_sup_right
  have : FiniteDimensional 𝕜 Y := finiteDimensional_of_le hYX
  have hclosed : IsClosed ((L ⊔ Y : Submodule 𝕜 E) : Set E) :=
    isClosed_sup_finiteDimensional L Y hL
  refine ClosedComplemented.of_isCompl_isClosed ⟨?_, ?_⟩ hG hclosed
  · refine hGL.disjoint_sup_right_of_disjoint_sup_left ?_
    rw [disjoint_iff, ← inf_eq_right.2 hYX, ← inf_assoc]
    exact hdisj.eq_bot
  · rw [codisjoint_iff, ← sup_assoc, ← hsup, ← hY, ← sup_assoc, sup_inf_self]

/-- Let $E$ be a Banach space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, and let $G$ and $L$ be
closed subspaces of $E$. Assume that there are finite-dimensional subspaces $X_1$ and $X_2$ with
$$G + L + X_1 = E \quad \text{and} \quad G \cap L \subseteq X_2.$$ Then $G$ is complemented.
This is Proposition 11.7 of [brezis2011functional].

The hypotheses are symmetric in $G$ and $L$, so $L$ is complemented as well. The
finite-dimensional subspace $G \cap L$ has a topological complement $N$ in $E$, by the
Hahn–Banach theorem. The subspaces $\tilde G = G \cap N$ and $\tilde L = L \cap N$ are closed
and disjoint, and $\tilde G + \tilde L + (X_1 + X_2) = E$, so $\tilde G$ is complemented by
`Submodule.closedComplemented_of_disjoint_of_sup_sup_eq_top`. Then $G = \tilde G + (G \cap L)$
is complemented by `Submodule.ClosedComplemented.sup_finiteDimensional`. -/
theorem closedComplemented_of_sup_sup_eq_top_of_inf_le {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E] {G L : Submodule 𝕜 E}
    (hG : IsClosed (G : Set E)) (hL : IsClosed (L : Set E)) (X₁ X₂ : Submodule 𝕜 E)
    [FiniteDimensional 𝕜 X₁] [FiniteDimensional 𝕜 X₂] (hsup : G ⊔ L ⊔ X₁ = ⊤)
    (hinf : G ⊓ L ≤ X₂) : G.ClosedComplemented := by
  have hK : FiniteDimensional 𝕜 (G ⊓ L : Submodule 𝕜 E) := finiteDimensional_of_le hinf
  obtain ⟨N, hN⟩ := (ClosedComplemented.of_finiteDimensional (G ⊓ L)).exists_isTopCompl
  have hNc : IsClosed (N : Set E) := hN.isClosed'
  -- `G = (G ⊓ L) ⊔ (N ⊓ G)`, and likewise for `L`: the modular law
  have hGeq : G ⊓ L ⊔ N ⊓ G = G := by
    rw [← sup_inf_assoc_of_le N (inf_le_left : G ⊓ L ≤ G), hN.isCompl.sup_eq_top, top_inf_eq]
  have hLeq : G ⊓ L ⊔ N ⊓ L = L := by
    rw [← sup_inf_assoc_of_le N (inf_le_right : G ⊓ L ≤ L), hN.isCompl.sup_eq_top, top_inf_eq]
  have hGc : IsClosed ((G ⊓ N : Submodule 𝕜 E) : Set E) := by rw [coe_inf]; exact hG.inter hNc
  have hLc : IsClosed ((L ⊓ N : Submodule 𝕜 E) : Set E) := by rw [coe_inf]; exact hL.inter hNc
  have hdisj : Disjoint (G ⊓ N) (L ⊓ N) := by
    rw [disjoint_iff_inf_le]
    calc G ⊓ N ⊓ (L ⊓ N) ≤ G ⊓ L ⊓ N :=
          le_inf (inf_le_inf inf_le_left inf_le_left) (inf_le_left.trans inf_le_right)
      _ ≤ ⊥ := hN.isCompl.disjoint.le_bot
  have hsup' : G ⊓ N ⊔ L ⊓ N ⊔ (X₁ ⊔ X₂) = ⊤ := by
    rw [eq_top_iff, ← hsup]
    refine sup_le (sup_le ?_ ?_) (le_sup_of_le_right le_sup_left)
    · calc G = G ⊓ L ⊔ N ⊓ G := hGeq.symm
        _ ≤ X₂ ⊔ G ⊓ N := sup_le_sup hinf (inf_comm _ _).le
        _ ≤ _ := sup_le (le_sup_of_le_right le_sup_right) (le_sup_of_le_left le_sup_left)
    · calc L = G ⊓ L ⊔ N ⊓ L := hLeq.symm
        _ ≤ X₂ ⊔ L ⊓ N := sup_le_sup hinf (inf_comm _ _).le
        _ ≤ _ := sup_le (le_sup_of_le_right le_sup_right) (le_sup_of_le_left le_sup_right)
  have hG' : (G ⊓ N).ClosedComplemented :=
    closedComplemented_of_disjoint_of_sup_sup_eq_top hGc hLc hdisj (X₁ ⊔ X₂) hsup'
  have := hG'.sup_finiteDimensional (G ⊓ L)
  rwa [sup_comm, inf_comm G N, hGeq] at this

end Fredholm

end Submodule
