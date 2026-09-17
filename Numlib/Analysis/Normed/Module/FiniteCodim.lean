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

The complement and dimension facts of [brezis2011functional] §11.1 that Mathlib does not have.

Most of that section *is* in Mathlib, and nothing of it is re-proved here: a finite-dimensional
subspace is closed (`Submodule.closed_of_finiteDimensional`, Proposition 11.1), every linear map
out of a finite-dimensional space is continuous (`LinearMap.continuous_of_finiteDimensional`,
Proposition 11.2), the sum of a closed and a finite-dimensional subspace is closed
(`Submodule.isClosed_sup_finiteDimensional`, the first clause of Proposition 11.4), a subspace
containing a closed subspace of finite codimension is closed
(`Submodule.isClosed_mono_of_finiteDimensional_quotient`, Proposition 11.5), and "finite
codimension" is `Submodule.CoFG` (`M.CoFG := Module.Finite 𝕜 (E ⧸ M)`, with
`Submodule.FG.cofg_of_codisjoint` and `Submodule.CoFG.fg_of_isCompl` relating it to the book's
"`M + X = E` for a finite-dimensional `X`"). Mathlib also has the one-directional complement
facts: a finite-dimensional subspace is complemented
(`Submodule.ClosedComplemented.of_finiteDimensional`, by Hahn–Banach), a closed subspace of
finite codimension is complemented (`Submodule.ClosedComplemented.of_finiteDimensional_quotient`),
and closed algebraic complements in a Banach space are topological complements
(`Submodule.ClosedComplemented.of_isCompl_isClosed`).

## Main statements

* `NormedSpace.finrank_strongDual` — `dim E* = dim E` for a finite-dimensional `E`, and
  `NormedSpace.finiteDimensional_of_finiteDimensional_strongDual` — a normed space whose strong
  dual is finite-dimensional is finite-dimensional (Proposition 11.3; the canonical embedding
  into the bidual is injective, which is where Hahn–Banach enters).
* `Submodule.ClosedComplemented.sup_finiteDimensional`,
  `Submodule.ClosedComplemented.of_sup_finiteDimensional`,
  `Submodule.closedComplemented_sup_finiteDimensional_iff` — for a closed `M` and a
  finite-dimensional `X`, `M ⊔ X` is complemented iff `M` is (the second clause of
  Proposition 11.4). Neither direction needs `E` complete: the complement of `M ⊔ X` is built
  from a complement `N` of `M` by complementing the finite-dimensional projection of `X` inside
  `N`, and conversely `M` has finite codimension inside `M ⊔ X`, so a continuous projection onto
  `M ⊔ X` composed with the (automatically continuous) projection of `M ⊔ X` onto `M` is a
  continuous projection onto `M`.
* `Submodule.exists_isCompl_le_of_dense` — a closed subspace of finite codimension has an
  algebraic complement inside any dense subspace `D` (Proposition 11.6): `M ⊔ D` is closed and
  contains `D`, hence is everything, and a complement of `M ⊓ D` inside `D` does the job. No
  induction on the codimension is needed.
* `Submodule.closedComplemented_of_disjoint_of_sup_sup_eq_top`,
  `Submodule.closedComplemented_of_sup_sup_eq_top_of_inf_le` — Proposition 11.7: in a Banach
  space, closed subspaces `G, L` with `G + L + X₁ = E` and `G ∩ L ⊆ X₂` for finite-dimensional
  `X₁, X₂` are complemented. This is the bookkeeping behind the Fredholm alternative's "`I - T`
  has index zero" in the book's chapter 6.

## Generality

Scalars are `RCLike 𝕜` exactly where Hahn–Banach enters (Proposition 11.3, the complement of a
finite-dimensional subspace in the `sup` direction of Proposition 11.4 and in Step 2 of
Proposition 11.7) and a complete nontrivially normed field elsewhere. Completeness of `E` is
assumed only in Proposition 11.7, where a closed algebraic complement must be shown topological
by the open mapping theorem. `Submodule.ClosedComplemented` is "admits a complement" in the
book's sense: a closed subspace `N` with `M ⊕ N = E`, equivalently a continuous projection
onto `M` (`Submodule.closedComplemented_iff_isClosed_exists_isClosed_isCompl`).
-/

open Module

section Dual

/-- **The strong dual of a finite-dimensional normed space has the same dimension**
([brezis2011functional] §11.1, the paragraph before Proposition 11.3): every linear functional
is continuous, so `StrongDual 𝕜 E` is linearly equivalent to the algebraic dual, whose dimension
is that of `E`. -/
theorem NormedSpace.finrank_strongDual {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E] :
    finrank 𝕜 (StrongDual 𝕜 E) = finrank 𝕜 E := by
  rw [← Subspace.dual_finrank_eq (K := 𝕜) (V := E)]
  exact (LinearMap.toContinuousLinearMap (𝕜 := 𝕜) (E := E) (F' := 𝕜)).symm.finrank_eq

/-- **A normed space whose strong dual is finite-dimensional is finite-dimensional**
([brezis2011functional] Proposition 11.3; the book assumes `E` complete, which is not used).
The bidual is then finite-dimensional, and the canonical embedding of `E` into it is injective,
being an isometry. The dimensions agree by `NormedSpace.finrank_strongDual`. -/
theorem NormedSpace.finiteDimensional_of_finiteDimensional_strongDual {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 (StrongDual 𝕜 E)] :
    FiniteDimensional 𝕜 E :=
  FiniteDimensional.of_injective (NormedSpace.inclusionInDoubleDual 𝕜 E).toLinearMap
    (NormedSpace.inclusionInDoubleDualLi 𝕜 (E := E)).injective

end Dual

namespace Submodule

section SupRCLike

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- **A complemented subspace stays complemented after adding a finite-dimensional one**
([brezis2011functional] Proposition 11.4, second clause, "if" half): for `M` complemented and
`X` finite-dimensional, `M ⊔ X` is complemented. No completeness of `E` is needed.

With `N` a topological complement of `M` and `P_M`, `P_N` the two projections, the
finite-dimensional subspace `X' = P_N(X)` of `N` has a continuous projection `R` of `N` onto it
(Hahn–Banach in `N`), and `P_M + R ∘ P_N` is a continuous projection of `E` onto
`M ⊔ X' = M ⊔ X`. -/
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

/-- **If `M ⊔ X` is complemented then so is the closed subspace `M`**, for `X` finite-dimensional
([brezis2011functional] Proposition 11.4, second clause, "only if" half). No completeness of
`E` is needed: `M` has finite codimension inside `M ⊔ X`, so the projection of `M ⊔ X` onto `M`
along any algebraic complement is continuous
(`Submodule.ClosedComplemented.of_finiteDimensional_quotient`), and composing it with a
continuous projection of `E` onto `M ⊔ X` gives a continuous projection onto `M`. -/
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

/-- **[brezis2011functional] Proposition 11.4, second clause**: for `M` closed and `X`
finite-dimensional, `M ⊔ X` is complemented iff `M` is. -/
theorem closedComplemented_sup_finiteDimensional_iff {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {M : Submodule 𝕜 E} (hM : IsClosed (M : Set E))
    (X : Submodule 𝕜 E) [FiniteDimensional 𝕜 X] :
    (M ⊔ X).ClosedComplemented ↔ M.ClosedComplemented :=
  ⟨ClosedComplemented.of_sup_finiteDimensional hM X, fun h => h.sup_finiteDimensional X⟩

end Sup

section Dense

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E]

/-- **A closed subspace of finite codimension has a complement inside any dense subspace**
([brezis2011functional] Proposition 11.6). The complement is automatically finite-dimensional
(`Submodule.CoFG.fg_of_isCompl`) and topological
(`Submodule.IsCompl.isTopCompl_of_finiteDimensional_quotient`).

`M ⊔ D` is closed, containing the closed finite-codimensional `M`, and contains the dense `D`,
so `M ⊔ D = ⊤`; a complement `X` of `M ⊓ D` inside `D` is then a complement of `M` in `E`
(the modular law). -/
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

/-- **[brezis2011functional] Proposition 11.7, Step 1** (the case `X₂ = 0`): in a Banach space,
closed subspaces `G`, `L` with `G ∩ L = 0` and `G + L + X₁ = E` for a finite-dimensional `X₁`
are complemented (the statement is symmetric in `G` and `L`).

With `X̃₁` a complement of `(G ⊔ L) ⊓ X₁` inside `X₁`, the subspace `L ⊔ X̃₁` is closed and an
algebraic complement of `G`; in a Banach space closed algebraic complements are topological. -/
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

/-- **[brezis2011functional] Proposition 11.7**: in a Banach space over `RCLike 𝕜`, closed
subspaces `G`, `L` with `G + L + X₁ = E` and `G ∩ L ⊆ X₂` for finite-dimensional `X₁`, `X₂` are
complemented (the statement is symmetric in `G` and `L`).

The finite-dimensional `G ⊓ L` has a topological complement `N` in `E` (Hahn–Banach), and
`G̃ = G ⊓ N`, `L̃ = L ⊓ N` are closed, disjoint, and satisfy `G̃ + L̃ + (X₁ + X₂) = E`, so `G̃` is
complemented by Step 1; then `G = G̃ ⊔ (G ⊓ L)` is complemented by
`Submodule.ClosedComplemented.sup_finiteDimensional`. -/
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
