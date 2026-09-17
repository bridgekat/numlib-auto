import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.LocallyConvex.HahnBanach
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Numlib.Analysis.Normed.Module.Annihilator
import Numlib.Analysis.Normed.Module.Complemented
import Numlib.Analysis.Normed.Module.Quotient
import NumlibSurface.Brezis.Chapter02.Section03

/-!
# Brezis §2.4: complementary subspaces, right and left invertibility

Surface file for Haim Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential
Equations*, Universitext, Springer, 2011, §2.4, for real Banach spaces `E`, `F`. Theorem 2.10,
Corollary 2.11 with Remark 7's converse, and the new direction of Theorem 2.12 are the backbone
`Numlib/Analysis/Normed/Module/Complemented`; the book's two "Definition." paragraphs are the
surface definitions `IsComplement` and `IsRightInverse` / `IsLeftInverse`, each identified with
Mathlib's notion (`Submodule.IsTopCompl` / `Submodule.ClosedComplemented`,
`ContinuousLinearMap.HasRightInverse` / `HasLeftInverse`), so that the Examples and Theorems
2.12–2.13 are restatements of Mathlib and the backbone.

## Main results

* `theorem_2_10`, `corollary_2_11`, `remark_2_7` — the bounded decomposition of a closed sum
  `G + L`, the distance inequality (14), and its converse.
* `IsComplement`, `isComplement_iff_isTopCompl`, `exists_isComplement_iff_closedComplemented`,
  `IsComplement.existsUnique_add`, `IsComplement.continuous_projection` — the Definition of a
  topological complement and the sentences following it.
* `example_2_1`, `example_2_2`, `example_2_2_strongDualCoannihilator`, `example_2_3` —
  finite-dimensional subspaces, closed subspaces of finite codimension (typically `N^⊥` for a
  finite-dimensional `N ⊆ E*`), and closed subspaces of a Hilbert space admit complements.
* `IsRightInverse`, `IsLeftInverse`, `theorem_2_12`, `theorem_2_13`, `remark_2_9` — right and
  left inverses, their characterizations, and the quotient map by an uncomplemented subspace.

Remark 8 (Lindenstrauss–Tzafriri) is not formalized; Remark 9 is stated conditionally on a
closed subspace without complement. Example 2's "typical example" (`N^⊥` for a
finite-dimensional `N ⊆ E*` is closed of codimension `dim N`) is
`example_2_2_strongDualCoannihilator`, whose codimension identity is chapter 11's
`Submodule.finrank_eq_finrank_quotient_strongDualCoannihilator` (Proposition 11.14).
-/

open Metric

namespace Brezis.Chapter02

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-! ### Theorem 2.10 and Corollary 2.11 -/

/-- **Theorem 2.10.** Let `E` be a Banach space and `G`, `L` closed subspaces with `G + L`
closed. Then there is a constant `C ≥ 0` such that every `z ∈ G + L` admits a decomposition
`z = x + y` with `x ∈ G`, `y ∈ L`, `‖x‖ ≤ C ‖z‖` and `‖y‖ ≤ C ‖z‖` (13). -/
theorem theorem_2_10 [CompleteSpace E] (G L : Submodule ℝ E) (hG : IsClosed (G : Set E))
    (hL : IsClosed (L : Set E)) (hGL : IsClosed ((G ⊔ L : Submodule ℝ E) : Set E)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ z ∈ G ⊔ L, ∃ x ∈ G, ∃ y ∈ L, z = x + y ∧ ‖x‖ ≤ C * ‖z‖ ∧ ‖y‖ ≤ C * ‖z‖ :=
  Submodule.exists_add_eq_norm_le_of_isClosed_sup G L hG hL hGL

/-- **Corollary 2.11.** Under the assumptions of Theorem 2.10 there is a constant `C` with
`dist (x, G ∩ L) ≤ C (dist (x, G) + dist (x, L))` for all `x ∈ E` (14). -/
theorem corollary_2_11 [CompleteSpace E] (G L : Submodule ℝ E) (hG : IsClosed (G : Set E))
    (hL : IsClosed (L : Set E)) (hGL : IsClosed ((G ⊔ L : Submodule ℝ E) : Set E)) :
    ∃ C : ℝ, ∀ x : E,
      infDist x (G ⊓ L : Submodule ℝ E) ≤ C * (infDist x (G : Set E) + infDist x (L : Set E)) :=
  Submodule.exists_infDist_inf_le_of_isClosed_sup G L hG hL hGL

/-- **Remark 7.** The converse of Corollary 2.11: if `G`, `L` are closed subspaces of a Banach
space for which (14) holds, then `G + L` is closed (Exercise 2.16). -/
theorem remark_2_7 [CompleteSpace E] (G L : Submodule ℝ E) (hG : IsClosed (G : Set E))
    (hL : IsClosed (L : Set E)) {C : ℝ}
    (h : ∀ x : E,
      infDist x (G ⊓ L : Submodule ℝ E) ≤ C * (infDist x (G : Set E) + infDist x (L : Set E))) :
    IsClosed ((G ⊔ L : Submodule ℝ E) : Set E) :=
  (Submodule.isClosed_sup_iff_exists_infDist_inf_le G L hG hL).2 ⟨C, h⟩

/-! ### Complementary subspaces -/

/-- **The Definition of §2.4.** Let `G` be a closed subspace of a Banach space `E`. A subspace
`L ⊆ E` is a topological complement (or simply a complement) of `G` if (i) `L` is closed and
(ii) `G ∩ L = {0}` and `G + L = E`; `G` and `L` are then complementary subspaces. -/
def IsComplement (G L : Submodule ℝ E) : Prop :=
  IsClosed (L : Set E) ∧ IsCompl G L

/-- The book's complements are Mathlib's topological complements: for a closed `G` in a Banach
space, `IsComplement G L ↔ Submodule.IsTopCompl G L`. -/
theorem isComplement_iff_isTopCompl [CompleteSpace E] {G L : Submodule ℝ E}
    (hG : IsClosed (G : Set E)) : IsComplement G L ↔ Submodule.IsTopCompl G L :=
  ⟨fun h => Submodule.isTopCompl_iff_isCompl_isClosed.2 ⟨h.2, hG, h.1⟩,
    fun h => ⟨h.isClosed', h.isCompl⟩⟩

/-- "`G` admits a complement" is Mathlib's `Submodule.ClosedComplemented`: for a closed `G` in
a Banach space, `(∃ L, IsComplement G L) ↔ G.ClosedComplemented`. -/
theorem exists_isComplement_iff_closedComplemented [CompleteSpace E] {G : Submodule ℝ E}
    (hG : IsClosed (G : Set E)) : (∃ L, IsComplement G L) ↔ G.ClosedComplemented := by
  rw [Submodule.closedComplemented_iff_isClosed_exists_isClosed_isCompl]
  exact ⟨fun ⟨L, hL⟩ => ⟨hG, L, hL.1, hL.2⟩, fun ⟨_, L, hL, hGL⟩ => ⟨L, hL, hGL⟩⟩

/-- If `G` and `L` are complementary, every `z ∈ E` may be uniquely written as `z = x + y` with
`x ∈ G` and `y ∈ L`. -/
theorem IsComplement.existsUnique_add {G L : Submodule ℝ E} (h : IsComplement G L) (z : E) :
    ∃! p : G × L, (p.1 : E) + p.2 = z :=
  Submodule.existsUnique_add_of_isCompl_prod h.2 z

/-- It follows from Theorem 2.10 that, for complementary subspaces `G`, `L` of a Banach space
(`G` closed), the projection operators `z ↦ x` and `z ↦ y` are continuous linear operators;
that property could also serve as a definition of complementary subspaces (and is Mathlib's
`Submodule.IsTopCompl`). -/
theorem IsComplement.continuous_projection [CompleteSpace E] {G L : Submodule ℝ E}
    (hG : IsClosed (G : Set E)) (h : IsComplement G L) :
    Continuous (G.projectionOnto L h.2) ∧ Continuous (L.projectionOnto G h.2.symm) :=
  ⟨((isComplement_iff_isTopCompl hG).1 h).continuous_projectionOnto,
    ((isComplement_iff_isTopCompl hG).1 h).symm.continuous_projectionOnto⟩

/-- **Example 1.** Every finite-dimensional subspace `G` of a Banach space admits a
complement. -/
theorem example_2_1 [CompleteSpace E] (G : Submodule ℝ E) [FiniteDimensional ℝ G] :
    ∃ L, IsComplement G L :=
  (exists_isComplement_iff_closedComplemented G.closed_of_finiteDimensional).2
    (Submodule.ClosedComplemented.of_finiteDimensional G)

/-- **Example 2.** Every closed subspace `G` of finite codimension admits a complement. -/
theorem example_2_2 [CompleteSpace E] {G : Submodule ℝ E} (hG : IsClosed (G : Set E))
    [FiniteDimensional ℝ (E ⧸ G)] : ∃ L, IsComplement G L :=
  (exists_isComplement_iff_closedComplemented hG).2
    (Submodule.ClosedComplemented.of_finiteDimensional_quotient hG)

/-- **Example 2, the "typical example".** For a subspace `N ⊆ E*` of finite dimension `p`, the
subspace `G = N^⊥ = {x ∈ E | ⟨f, x⟩ = 0 ∀ f ∈ N}` (chapter 1's `N.strongDualCoannihilator`) is
closed and of codimension `p`, hence admits a complement. The codimension identity
`dim (E ⧸ N^⊥) = dim N` is Proposition 11.14 ("another proof … in Chapter 11"); the book's own
argument, through the map `x ↦ (⟨fᵢ, x⟩)ᵢ` onto `ℝ^p` for a basis `(fᵢ)` of `N`, is not
repeated here. -/
theorem example_2_2_strongDualCoannihilator [CompleteSpace E] (N : Submodule ℝ (StrongDual ℝ E))
    [FiniteDimensional ℝ N] :
    IsClosed (N.strongDualCoannihilator : Set E) ∧
      Module.finrank ℝ (E ⧸ N.strongDualCoannihilator) = Module.finrank ℝ N ∧
      ∃ L, IsComplement N.strongDualCoannihilator L := by
  have hcl : IsClosed (N.strongDualCoannihilator : Set E) := N.isClosed_strongDualCoannihilator
  have : FiniteDimensional ℝ (E ⧸ N.strongDualCoannihilator) :=
    (N.finiteDimensional_iff_coFG_strongDualCoannihilator).1 ‹_›
  exact ⟨hcl, (N.finrank_eq_finrank_quotient_strongDualCoannihilator).symm, example_2_2 hcl⟩

/-- **Example 3.** In a Hilbert space every closed subspace `K` admits a complement, namely its
orthogonal `K^⊥` (§5.2). -/
theorem example_2_3 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {K : Submodule ℝ H} (hK : IsClosed (K : Set H)) : IsComplement K Kᗮ := by
  have := hK.completeSpace_coe
  exact (isComplement_iff_isTopCompl hK).2 K.isTopCompl_orthogonal

/-! ### Right and left inverses -/

/-- **The Definition of a right inverse.** For `T ∈ 𝓛(E, F)`, a right inverse of `T` is an
operator `S ∈ 𝓛(F, E)` with `T ∘ S = I_F`. -/
def IsRightInverse (T : E →L[ℝ] F) (S : F →L[ℝ] E) : Prop :=
  T.comp S = ContinuousLinearMap.id ℝ F

/-- **The Definition of a left inverse.** For `T ∈ 𝓛(E, F)`, a left inverse of `T` is an
operator `S ∈ 𝓛(F, E)` with `S ∘ T = I_E`. -/
def IsLeftInverse (T : E →L[ℝ] F) (S : F →L[ℝ] E) : Prop :=
  S.comp T = ContinuousLinearMap.id ℝ E

/-- "`T` admits a right inverse" is Mathlib's `ContinuousLinearMap.HasRightInverse`. -/
theorem exists_isRightInverse_iff_hasRightInverse (T : E →L[ℝ] F) :
    (∃ S, IsRightInverse T S) ↔ T.HasRightInverse := by
  simp only [IsRightInverse, ContinuousLinearMap.ext_iff, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply]
  rfl

/-- "`T` admits a left inverse" is Mathlib's `ContinuousLinearMap.HasLeftInverse`. -/
theorem exists_isLeftInverse_iff_hasLeftInverse (T : E →L[ℝ] F) :
    (∃ S, IsLeftInverse T S) ↔ T.HasLeftInverse := by
  simp only [IsLeftInverse, ContinuousLinearMap.ext_iff, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply]
  rfl

/-- **Theorem 2.12.** Let `T ∈ 𝓛(E, F)` be surjective (`E`, `F` Banach). Then `T` admits a
right inverse iff `N(T) = T⁻¹(0)` admits a complement in `E`. -/
theorem theorem_2_12 [CompleteSpace E] [CompleteSpace F] (T : E →L[ℝ] F)
    (hT : Function.Surjective T) : (∃ S, IsRightInverse T S) ↔ ∃ L, IsComplement T.ker L := by
  rw [exists_isRightInverse_iff_hasRightInverse,
    exists_isComplement_iff_closedComplemented T.isClosed_ker]
  exact ContinuousLinearMap.hasRightInverse_iff_closedComplemented_ker hT

/-- **Remark 9.** A surjective operator without a right inverse: if `G` is a closed subspace of
the Banach space `E` without complement, the canonical projection `T : E → E ⧸ G` is
surjective and admits no right inverse (by Theorem 2.12, since `N(T) = G`). -/
theorem remark_2_9 [CompleteSpace E] {G : Submodule ℝ E} (hG : IsClosed (G : Set E))
    (h : ¬ ∃ L, IsComplement G L) :
    Function.Surjective G.mkQL ∧ ¬ ∃ S : (E ⧸ G) →L[ℝ] E, IsRightInverse G.mkQL S := by
  have := hG
  have hsurj : Function.Surjective G.mkQL := G.mkQ_surjective
  refine ⟨hsurj, fun hS => h ?_⟩
  have hker : G.mkQL.ker = G := G.ker_mkQ
  rw [theorem_2_12 G.mkQL hsurj, hker] at hS
  exact hS

/-- **Theorem 2.13.** Let `T ∈ 𝓛(E, F)` be injective (`E`, `F` Banach). Then `T` admits a left
inverse iff `R(T) = T(E)` is closed and admits a complement in `F`. -/
theorem theorem_2_13 [CompleteSpace E] [CompleteSpace F] (T : E →L[ℝ] F)
    (hT : Function.Injective T) :
    (∃ S, IsLeftInverse T S) ↔ IsClosed (Set.range T) ∧ ∃ L, IsComplement T.range L := by
  rw [exists_isLeftInverse_iff_hasLeftInverse,
    ContinuousLinearMap.hasLeftInverse_iff_isClosed_range_and_closedComplemented_range hT]
  refine and_congr_right fun hR => ?_
  exact (exists_isComplement_iff_closedComplemented hR).symm

end Brezis.Chapter02
