/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.LocallyConvex.HahnBanach
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Numlib.Analysis.Normed.Module.Annihilator
import Numlib.Analysis.Normed.Module.Complemented
import Numlib.Analysis.Normed.Module.Quotient
import NumlibSurface.Brezis.Chapter02.Section03

/-!
# Brezis, Section 2.4: Complementary subspaces, right and left invertibility

This module formalizes Section 2.4 of [brezis2011functional] for real Banach spaces $E$ and $F$. If
$G$ and $L$ are closed subspaces of $E$ and $G + L$ is closed, then every $z \in G + L$ splits as
$z = x + y$ with $x \in G$, $y \in L$ and $\|x\|, \|y\| \le C\|z\|$ (Theorem 2.10), and
$\operatorname{dist}(x, G \cap L) \le C(\operatorname{dist}(x, G) + \operatorname{dist}(x, L))$
(Corollary 2.11); the converse of the second statement also holds (Remark 7). A closed subspace $L$
is a topological complement of a closed subspace $G$ if $G \cap L = \{0\}$ and $G + L = E$.
Finite-dimensional subspaces, closed subspaces of finite codimension and closed subspaces of a
Hilbert space have complements (Examples 1 to 3). A surjective $T \in \mathcal{L}(E, F)$ has a right
inverse if and only if its kernel has a complement (Theorem 2.12). An injective $T$ has a left
inverse if and only if its range is closed and has a complement (Theorem 2.13).

Theorem 2.10, Corollary 2.11, Remark 7 and the new direction of Theorem 2.12 specialize the backbone
module `Numlib.Analysis.Normed.Module.Complemented`. The two definitions of the section are
identified with Mathlib's `Submodule.IsTopCompl`, `Submodule.ClosedComplemented`,
`ContinuousLinearMap.HasRightInverse` and `ContinuousLinearMap.HasLeftInverse`, so that the Examples
and Theorems 2.12 and 2.13 restate Mathlib and the backbone.

## Main definitions

* Section 2.4, definition of a topological complement, `Brezis.Chapter02.IsComplement`: $L$ is
  closed, $G \cap L = \{0\}$ and $G + L = E$.
* Section 2.4, definition of a right inverse, `Brezis.Chapter02.IsRightInverse`:
  $S \in \mathcal{L}(F, E)$ with $T \circ S = I_F$.
* Section 2.4, definition of a left inverse, `Brezis.Chapter02.IsLeftInverse`:
  $S \in \mathcal{L}(F, E)$ with $S \circ T = I_E$.

## Main results

* Theorem 2.10, `Brezis.Chapter02.theorem_2_10`: every $z \in G + L$ is $z = x + y$ with
  $\|x\| \le C\|z\|$ and $\|y\| \le C\|z\|$.
* Corollary 2.11, `Brezis.Chapter02.corollary_2_11`: the distance inequality (14).
* Remark 7, `Brezis.Chapter02.remark_2_7`: if (14) holds for closed subspaces $G$ and $L$, then
  $G + L$ is closed.
* Section 2.4, `Brezis.Chapter02.isComplement_iff_isTopCompl`: a complement in the sense of the
  source is a topological complement in the sense of Mathlib.
* Section 2.4, `Brezis.Chapter02.exists_isComplement_iff_closedComplemented`: $G$ has a complement
  if and only if it is `Submodule.ClosedComplemented`.
* Section 2.4, `Brezis.Chapter02.IsComplement.existsUnique_add`: for complementary subspaces, every
  $z$ is uniquely $x + y$ with $x \in G$ and $y \in L$.
* Section 2.4, `Brezis.Chapter02.IsComplement.continuous_projection`: the projections onto
  complementary subspaces are continuous.
* Example 1, `Brezis.Chapter02.example_2_1`: a finite-dimensional subspace has a complement.
* Example 2, `Brezis.Chapter02.example_2_2`: a closed subspace of finite codimension has a
  complement.
* Example 2, `Brezis.Chapter02.example_2_2_strongDualCoannihilator`: for a finite-dimensional
  $N \subseteq E^\star$, the subspace $N^\perp$ is closed, of codimension $\dim N$, and has a
  complement.
* Example 3, `Brezis.Chapter02.example_2_3`: in a Hilbert space, a closed subspace $K$ has the
  complement $K^\perp$.
* Section 2.4, `Brezis.Chapter02.exists_isRightInverse_iff_hasRightInverse`: $T$ has a right inverse
  if and only if `ContinuousLinearMap.HasRightInverse`.
* Section 2.4, `Brezis.Chapter02.exists_isLeftInverse_iff_hasLeftInverse`: $T$ has a left inverse if
  and only if `ContinuousLinearMap.HasLeftInverse`.
* Theorem 2.12, `Brezis.Chapter02.theorem_2_12`: a surjective $T$ has a right inverse if and only if
  $N(T)$ has a complement.
* Remark 9, `Brezis.Chapter02.remark_2_9`: the quotient map by a closed subspace without complement
  is surjective and has no right inverse.
* Theorem 2.13, `Brezis.Chapter02.theorem_2_13`: an injective $T$ has a left inverse if and only if
  $R(T)$ is closed and has a complement.

## Implementation notes

* Remark 9 is stated for a given closed subspace without complement. The existence of such a
  subspace is the subject of Remark 8, which is not formalized.
* The codimension identity of Example 2 is the backbone theorem
  `Submodule.finrank_eq_finrank_quotient_strongDualCoannihilator`, which is Proposition 11.14 of the
  source.

## Not formalized

* **Remark 8 (Lindenstrauss–Tzafriri).**
-/

open Metric

namespace Brezis.Chapter02

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-! ### Theorem 2.10 and Corollary 2.11 -/

/-- **Theorem 2.10** of [brezis2011functional]. Let $E$ be a Banach space and let $G$ and $L$ be two
closed linear subspaces such that $G + L$ is closed. Then there is a constant $C \ge 0$ such
that every $z \in G + L$ admits a decomposition $z = x + y$ with $x \in G$, $y \in L$,
$$\|x\| \le C\|z\| \quad \text{and} \quad \|y\| \le C\|z\|. \qquad (13)$$

The proof specializes the backbone theorem `Submodule.exists_add_eq_norm_le_of_isClosed_sup`. -/
theorem theorem_2_10 [CompleteSpace E] (G L : Submodule ℝ E) (hG : IsClosed (G : Set E))
    (hL : IsClosed (L : Set E)) (hGL : IsClosed ((G ⊔ L : Submodule ℝ E) : Set E)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ z ∈ G ⊔ L, ∃ x ∈ G, ∃ y ∈ L, z = x + y ∧ ‖x‖ ≤ C * ‖z‖ ∧ ‖y‖ ≤ C * ‖z‖ :=
  Submodule.exists_add_eq_norm_le_of_isClosed_sup G L hG hL hGL

/-- **Corollary 2.11** of [brezis2011functional]. Let $E$ be a Banach space and let $G$ and $L$ be
two closed linear subspaces such that $G + L$ is closed. Then there is a constant $C$ such that
$$\operatorname{dist}(x, G \cap L) \le C\{\operatorname{dist}(x, G) + \operatorname{dist}(x,
  L)\} \quad \text{for all } x \in E. \qquad (14)$$

The distance is Mathlib's `Metric.infDist`. The proof specializes the backbone theorem
`Submodule.exists_infDist_inf_le_of_isClosed_sup`. -/
theorem corollary_2_11 [CompleteSpace E] (G L : Submodule ℝ E) (hG : IsClosed (G : Set E))
    (hL : IsClosed (L : Set E)) (hGL : IsClosed ((G ⊔ L : Submodule ℝ E) : Set E)) :
    ∃ C : ℝ, ∀ x : E,
      infDist x (G ⊓ L : Submodule ℝ E) ≤ C * (infDist x (G : Set E) + infDist x (L : Set E)) :=
  Submodule.exists_infDist_inf_le_of_isClosed_sup G L hG hL hGL

/-- **Remark 7** of [brezis2011functional], the converse of Corollary 2.11. Let $E$ be a Banach
space and let $G$ and $L$ be two closed linear subspaces. If there is a constant $C$ such that
(14) holds for all $x \in E$, then $G + L$ is closed. This is Exercise 2.16 of the source. -/
theorem remark_2_7 [CompleteSpace E] (G L : Submodule ℝ E) (hG : IsClosed (G : Set E))
    (hL : IsClosed (L : Set E)) {C : ℝ}
    (h : ∀ x : E,
      infDist x (G ⊓ L : Submodule ℝ E) ≤ C * (infDist x (G : Set E) + infDist x (L : Set E))) :
    IsClosed ((G ⊔ L : Submodule ℝ E) : Set E) :=
  (Submodule.isClosed_sup_iff_exists_infDist_inf_le G L hG hL).2 ⟨C, h⟩

/-! ### Complementary subspaces -/

/-- **Section 2.4** of [brezis2011functional], definition of a topological complement. Let $E$ be a
real normed space and let $G \subseteq E$ be a linear subspace. A linear subspace
$L \subseteq E$ is a **topological complement** (or simply a **complement**) of $G$ if (i) $L$
is closed, and (ii) $G \cap L = \{0\}$ and $G + L = E$. Then $G$ and $L$ are **complementary
subspaces**.

The source assumes that $G$ is closed and $E$ is a Banach space; here these are hypotheses of
the theorems. Condition (ii) is Mathlib's `IsCompl G L` in the lattice of submodules. -/
def IsComplement (G L : Submodule ℝ E) : Prop :=
  IsClosed (L : Set E) ∧ IsCompl G L

/-- Let $E$ be a Banach space and $G \subseteq E$ a closed linear subspace. A linear subspace $L$ is
a complement of $G$ in the sense of `Brezis.Chapter02.IsComplement` if and only if it is a
topological complement in the sense of Mathlib's `Submodule.IsTopCompl`. -/
theorem isComplement_iff_isTopCompl [CompleteSpace E] {G L : Submodule ℝ E}
    (hG : IsClosed (G : Set E)) : IsComplement G L ↔ Submodule.IsTopCompl G L :=
  ⟨fun h => Submodule.isTopCompl_iff_isCompl_isClosed.2 ⟨h.2, hG, h.1⟩,
    fun h => ⟨h.isClosed', h.isCompl⟩⟩

/-- **Section 2.4** of [brezis2011functional], "$G$ admits a complement". Let $E$ be a Banach space
and $G \subseteq E$ a closed linear subspace. Then $G$ admits a complement if and only if $G$ is
closed complemented in the sense of Mathlib's `Submodule.ClosedComplemented`, that is, $G$ is
the range of a bounded linear projection. -/
theorem exists_isComplement_iff_closedComplemented [CompleteSpace E] {G : Submodule ℝ E}
    (hG : IsClosed (G : Set E)) : (∃ L, IsComplement G L) ↔ G.ClosedComplemented := by
  rw [Submodule.closedComplemented_iff_isClosed_exists_isClosed_isCompl]
  exact ⟨fun ⟨L, hL⟩ => ⟨hG, L, hL.1, hL.2⟩, fun ⟨_, L, hL, hGL⟩ => ⟨L, hL, hGL⟩⟩

/-- **Section 2.4** of [brezis2011functional], unique decomposition. If $G$ and $L$ are
complementary subspaces of a real normed space $E$, then every $z \in E$ can be written uniquely
as $z = x + y$ with $x \in G$ and $y \in L$. -/
theorem IsComplement.existsUnique_add {G L : Submodule ℝ E} (h : IsComplement G L) (z : E) :
    ∃! p : G × L, (p.1 : E) + p.2 = z :=
  Submodule.existsUnique_add_of_isCompl_prod h.2 z

/-- **Section 2.4** of [brezis2011functional], continuity of the projections. Let $E$ be a Banach
space and let $G$ and $L$ be complementary subspaces, with $G$ closed. Then the projection
operators $z \mapsto x$ and $z \mapsto y$ of the decomposition $z = x + y$ are continuous linear
operators.

The source notes that this follows from Theorem 2.10, and that this property could also serve as
the definition of complementary subspaces; it is Mathlib's `Submodule.IsTopCompl`. The
projections are Mathlib's `Submodule.projectionOnto`. -/
theorem IsComplement.continuous_projection [CompleteSpace E] {G L : Submodule ℝ E}
    (hG : IsClosed (G : Set E)) (h : IsComplement G L) :
    Continuous (G.projectionOnto L h.2) ∧ Continuous (L.projectionOnto G h.2.symm) :=
  ⟨((isComplement_iff_isTopCompl hG).1 h).continuous_projectionOnto,
    ((isComplement_iff_isTopCompl hG).1 h).symm.continuous_projectionOnto⟩

/-- **Example 1** of [brezis2011functional]. Every finite-dimensional linear subspace $G$ of a
Banach space admits a complement. -/
theorem example_2_1 [CompleteSpace E] (G : Submodule ℝ E) [FiniteDimensional ℝ G] :
    ∃ L, IsComplement G L :=
  (exists_isComplement_iff_closedComplemented G.closed_of_finiteDimensional).2
    (Submodule.ClosedComplemented.of_finiteDimensional G)

/-- **Example 2** of [brezis2011functional]. Every closed linear subspace $G$ of finite codimension
in a Banach space $E$ admits a complement.

Finite codimension means that the quotient $E / G$ is finite-dimensional. -/
theorem example_2_2 [CompleteSpace E] {G : Submodule ℝ E} (hG : IsClosed (G : Set E))
    [FiniteDimensional ℝ (E ⧸ G)] : ∃ L, IsComplement G L :=
  (exists_isComplement_iff_closedComplemented hG).2
    (Submodule.ClosedComplemented.of_finiteDimensional_quotient hG)

/-- **Example 2** of [brezis2011functional], the typical example. Let $E$ be a Banach space and let
$N \subseteq E^\star$ be a linear subspace of finite dimension $p$. Then
$$G = N^\perp = \{x \in E : \langle f, x \rangle = 0 \ \forall f \in N\}$$
is closed and of codimension $p$, that is, $\dim(E / N^\perp) = \dim N$, and hence $G$ admits a
complement.

The set $N^\perp$ is `N.strongDualCoannihilator`, as in Section 1.3. The codimension identity is
Proposition 11.14 of the source, which notes that "another proof" is given in Chapter 11; it is
the backbone theorem `Submodule.finrank_eq_finrank_quotient_strongDualCoannihilator`. The
argument of the source, through the map $x \mapsto (\langle f_i, x \rangle)_{1 \le i \le p}$
onto $\mathbb{R}^p$ for a basis $(f_i)$ of $N$, is not repeated. -/
theorem example_2_2_strongDualCoannihilator [CompleteSpace E] (N : Submodule ℝ (StrongDual ℝ E))
    [FiniteDimensional ℝ N] :
    IsClosed (N.strongDualCoannihilator : Set E) ∧
      Module.finrank ℝ (E ⧸ N.strongDualCoannihilator) = Module.finrank ℝ N ∧
      ∃ L, IsComplement N.strongDualCoannihilator L := by
  have hcl : IsClosed (N.strongDualCoannihilator : Set E) := N.isClosed_strongDualCoannihilator
  have : FiniteDimensional ℝ (E ⧸ N.strongDualCoannihilator) :=
    (N.finiteDimensional_iff_coFG_strongDualCoannihilator).1 ‹_›
  exact ⟨hcl, (N.finrank_eq_finrank_quotient_strongDualCoannihilator).symm, example_2_2 hcl⟩

/-- **Example 3** of [brezis2011functional]. In a real Hilbert space $H$, every closed linear
subspace $K$ admits a complement, namely its orthogonal complement $K^\perp$ (Section 5.2). -/
theorem example_2_3 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {K : Submodule ℝ H} (hK : IsClosed (K : Set H)) : IsComplement K Kᗮ := by
  have := hK.completeSpace_coe
  exact (isComplement_iff_isTopCompl hK).2 K.isTopCompl_orthogonal

/-! ### Right and left inverses -/

/-- **Section 2.4** of [brezis2011functional], definition of a right inverse. Let $E$ and $F$ be
real normed spaces and $T \in \mathcal{L}(E, F)$. An operator $S \in \mathcal{L}(F, E)$ is a
**right inverse** of $T$ if $T \circ S = I_F$. -/
def IsRightInverse (T : E →L[ℝ] F) (S : F →L[ℝ] E) : Prop :=
  T.comp S = ContinuousLinearMap.id ℝ F

/-- **Section 2.4** of [brezis2011functional], definition of a left inverse. Let $E$ and $F$ be real
normed spaces and $T \in \mathcal{L}(E, F)$. An operator $S \in \mathcal{L}(F, E)$ is a **left
inverse** of $T$ if $S \circ T = I_E$. -/
def IsLeftInverse (T : E →L[ℝ] F) (S : F →L[ℝ] E) : Prop :=
  S.comp T = ContinuousLinearMap.id ℝ E

/-- **Section 2.4** of [brezis2011functional], "$T$ admits a right inverse". An operator
$T \in \mathcal{L}(E, F)$ has a right inverse in the sense of `Brezis.Chapter02.IsRightInverse`
if and only if it satisfies Mathlib's `ContinuousLinearMap.HasRightInverse`. -/
theorem exists_isRightInverse_iff_hasRightInverse (T : E →L[ℝ] F) :
    (∃ S, IsRightInverse T S) ↔ T.HasRightInverse := by
  simp only [IsRightInverse, ContinuousLinearMap.ext_iff, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply]
  rfl

/-- **Section 2.4** of [brezis2011functional], "$T$ admits a left inverse". An operator
$T \in \mathcal{L}(E, F)$ has a left inverse in the sense of `Brezis.Chapter02.IsLeftInverse` if
and only if it satisfies Mathlib's `ContinuousLinearMap.HasLeftInverse`. -/
theorem exists_isLeftInverse_iff_hasLeftInverse (T : E →L[ℝ] F) :
    (∃ S, IsLeftInverse T S) ↔ T.HasLeftInverse := by
  simp only [IsLeftInverse, ContinuousLinearMap.ext_iff, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply]
  rfl

/-- **Theorem 2.12** of [brezis2011functional]. Let $E$ and $F$ be Banach spaces and let
$T \in \mathcal{L}(E, F)$ be surjective. Then the following properties are equivalent: (i) $T$
admits a right inverse; (ii) $N(T) = T^{-1}(0)$ admits a complement in $E$.

The proof specializes the backbone theorem
`ContinuousLinearMap.hasRightInverse_iff_closedComplemented_ker`. -/
theorem theorem_2_12 [CompleteSpace E] [CompleteSpace F] (T : E →L[ℝ] F)
    (hT : Function.Surjective T) : (∃ S, IsRightInverse T S) ↔ ∃ L, IsComplement T.ker L := by
  rw [exists_isRightInverse_iff_hasRightInverse,
    exists_isComplement_iff_closedComplemented T.isClosed_ker]
  exact ContinuousLinearMap.hasRightInverse_iff_closedComplemented_ker hT

/-- **Remark 9** of [brezis2011functional]. Let $E$ be a Banach space and let $G$ be a closed linear
subspace of $E$ that has no complement. Then the canonical projection $T : E \to E / G$ is
surjective and has no right inverse. This follows from Theorem 2.12, since $N(T) = G$.

The canonical projection is `G.mkQL`. The statement takes the subspace $G$ as a hypothesis;
Remark 8 of the source, on the existence of such subspaces, is not formalized. -/
theorem remark_2_9 [CompleteSpace E] {G : Submodule ℝ E} (hG : IsClosed (G : Set E))
    (h : ¬ ∃ L, IsComplement G L) :
    Function.Surjective G.mkQL ∧ ¬ ∃ S : (E ⧸ G) →L[ℝ] E, IsRightInverse G.mkQL S := by
  have := hG
  have hsurj : Function.Surjective G.mkQL := G.mkQ_surjective
  refine ⟨hsurj, fun hS => h ?_⟩
  have hker : G.mkQL.ker = G := G.ker_mkQ
  rw [theorem_2_12 G.mkQL hsurj, hker] at hS
  exact hS

/-- **Theorem 2.13** of [brezis2011functional]. Let $E$ and $F$ be Banach spaces and let
$T \in \mathcal{L}(E, F)$ be injective. Then the following properties are equivalent: (i) $T$
admits a left inverse; (ii) $R(T) = T(E)$ is closed and admits a complement in $F$.

The proof specializes the backbone theorem
`ContinuousLinearMap.hasLeftInverse_iff_isClosed_range_and_closedComplemented_range`. -/
theorem theorem_2_13 [CompleteSpace E] [CompleteSpace F] (T : E →L[ℝ] F)
    (hT : Function.Injective T) :
    (∃ S, IsLeftInverse T S) ↔ IsClosed (Set.range T) ∧ ∃ L, IsComplement T.range L := by
  rw [exists_isLeftInverse_iff_hasLeftInverse,
    ContinuousLinearMap.hasLeftInverse_iff_isClosed_range_and_closedComplemented_range hT]
  refine and_congr_right fun hR => ?_
  exact (exists_isComplement_iff_closedComplemented hR).symm

end Brezis.Chapter02
