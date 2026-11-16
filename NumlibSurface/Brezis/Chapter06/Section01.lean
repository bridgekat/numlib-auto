/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Normed.Operator.Compact.Banach
import Numlib.Nonlinear.CompletelyContinuous
import NumlibSurface.Brezis.Chapter03.Section05

/-!
# Brezis, Section 6.1: Definitions, elementary properties, adjoint

This module formalizes Section 6.1 of [brezis2011functional] on compact operators between real
Banach spaces $E$ and $F$. A bounded operator $T \in \mathcal{L}(E, F)$ is compact if the image
$T(B_E)$ of the closed unit ball has compact closure. The set $\mathcal{K}(E, F)$ of compact
operators is a closed linear subspace of $\mathcal{L}(E, F)$ (Theorem 6.1). Operators of finite rank
are compact, and so are norm limits of operators of finite rank (Corollary 6.2); into a Hilbert
space every compact operator is such a limit (Remark 1). Compositions with a compact operator are
compact (Proposition 6.3), and $T$ is compact if and only if its adjoint $T^\star$ is compact
(Theorem 6.4, Schauder). A compact operator maps weakly convergent sequences to strongly convergent
ones (Remark 2).

Theorem 6.1 and Proposition 6.3 are Mathlib's results on `IsCompactOperator`. Corollary 6.2, Remark
1 and Theorem 6.4 specialize the backbone modules `Numlib.Analysis.Normed.Operator.Compact` and
`Numlib.Analysis.Normed.Operator.Compact.Banach`; the nonlinear part of Remark 1 specializes
`Numlib.Nonlinear.CompletelyContinuous`.

## Main definitions

* Section 6.1, definition of a compact operator, `Brezis.Chapter06.compactOperator_iff`: $T$ is
  compact if and only if $T(B_E)$ has compact closure.
* Section 6.1, definition of an operator of finite rank, `Brezis.Chapter06.IsFiniteRank`: the range
  of $T$ is finite dimensional.

## Main results

* Theorem 6.1, `Brezis.Chapter06.theorem_6_1`: $\mathcal{K}(E, F)$ is closed in $\mathcal{L}(E, F)$.
* Theorem 6.1, `Brezis.Chapter06.theorem_6_1_submodule`: $\mathcal{K}(E, F)$ is a closed linear
  subspace of $\mathcal{L}(E, F)$.
* `Brezis.Chapter06.IsFiniteRank.isCompactOperator`: an operator of finite rank is compact.
* Corollary 6.2, `Brezis.Chapter06.corollary_6_2`: a norm limit of operators of finite rank is
  compact.
* Remark 1, `Brezis.Chapter06.remark_6_1`: a compact operator into a Hilbert space is a norm limit
  of operators of finite rank.
* Remark 1, `Brezis.Chapter06.remark_6_1_nonlinear`: a continuous map with relatively compact range
  is a uniform limit of continuous maps of finite rank.
* Proposition 6.3, `Brezis.Chapter06.proposition_6_3_left` and
  `Brezis.Chapter06.proposition_6_3_right`: $S \circ T$ is compact if $S$ or $T$ is compact.
* Theorem 6.4, `Brezis.Chapter06.theorem_6_4` and `Brezis.Chapter06.theorem_6_4_mpr` (Schauder): $T$
  is compact if and only if $T^\star$ is compact.
* Remark 2, `Brezis.Chapter06.remark_6_2`: a compact operator maps weakly convergent sequences to
  strongly convergent sequences.
* Remark 2, `Brezis.Chapter06.remark_6_2_mpr`: on a reflexive space the converse holds.

## Conventions

* The space $\mathcal{K}(E, F)$ is Mathlib's predicate `IsCompactOperator` on `T : E →L[ℝ] F`, and
  the submodule `compactOperator (RingHom.id ℝ) E F`.
* The adjoint $T^\star : F^\star \to E^\star$ is `ContinuousLinearMap.strongDualMap T`, as in
  Chapter 2.
* Weak convergence $u_n \rightharpoonup u$ is `Brezis.Chapter03.WeakTendsto`, and reflexivity is
  `Brezis.Chapter03.IsReflexive`, as in Chapter 3.
* Completeness of $E$ and $F$ is assumed only where a statement uses it.

## Not formalized

* **Remark 1, Enflo's counterexample and Schauder bases.** This part of the remark is
  bibliographical.
-/

open Filter Topology

noncomputable section

namespace Brezis.Chapter06

open Brezis.Chapter03 (WeakTendsto)

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-! ### Compact operators -/

/-- **Section 6.1** of [brezis2011functional], definition of a compact operator. Let $E$ and $F$ be
normed spaces. A bounded operator $T \in \mathcal{L}(E, F)$ is compact if and only if the image
$T(B_E)$ of the closed unit ball $B_E$ has compact closure in $F$ for the strong topology.

Mathlib's definition `IsCompactOperator` says that $T$ maps some neighbourhood of $0$ into a
compact set. This theorem reads it with the closed ball of radius $1$, as the source defines it. -/
theorem compactOperator_iff (T : E →L[ℝ] F) :
    IsCompactOperator T ↔ IsCompact (closure (T '' Metric.closedBall 0 1)) := by
  have key := isCompactOperator_iff_isCompact_closure_image_closedBall (T : E →ₗ[ℝ] F) one_pos
  rwa [ContinuousLinearMap.coe_coe] at key

/-- **Theorem 6.1** of [brezis2011functional], closedness. Let $E$ be a normed space and $F$ a
Banach space. The set $\mathcal{K}(E, F)$ of compact operators is closed in $\mathcal{L}(E, F)$
for the operator norm. -/
theorem theorem_6_1 [CompleteSpace F] : IsClosed {T : E →L[ℝ] F | IsCompactOperator T} :=
  isClosed_setOfPred_isCompactOperator

/-- **Theorem 6.1** of [brezis2011functional], the linear subspace. Let $E$ be a normed space and
$F$ a Banach space. The set $\mathcal{K}(E, F)$ of compact operators is a linear subspace of
$\mathcal{L}(E, F)$, and this subspace is closed: it equals its topological closure.

The subspace is Mathlib's `compactOperator (RingHom.id ℝ) E F`. The first part of the statement
says that its carrier is the set of compact operators. -/
theorem theorem_6_1_submodule [CompleteSpace F] :
    ((compactOperator (RingHom.id ℝ) E F : Submodule ℝ (E →L[ℝ] F)) : Set (E →L[ℝ] F)) =
        {T : E →L[ℝ] F | IsCompactOperator T} ∧
      (compactOperator (RingHom.id ℝ) E F).topologicalClosure =
        compactOperator (RingHom.id ℝ) E F :=
  ⟨rfl, compactOperator_topologicalClosure⟩

/-- **Section 6.1** of [brezis2011functional], definition of an operator of finite rank. An operator
$T \in \mathcal{L}(E, F)$ has **finite rank** if its range $R(T)$ is finite dimensional. -/
def IsFiniteRank (T : E →L[ℝ] F) : Prop :=
  FiniteDimensional ℝ (LinearMap.range (T : E →ₗ[ℝ] F))

/-- Every operator $T \in \mathcal{L}(E, F)$ of finite rank is compact. The source states this in
Section 6.1 with the words "clearly, any finite-rank operator is compact". -/
theorem IsFiniteRank.isCompactOperator {T : E →L[ℝ] F} (hT : IsFiniteRank T) :
    IsCompactOperator T :=
  haveI : FiniteDimensional ℝ (LinearMap.range (T : E →ₗ[ℝ] F)) := hT
  IsCompactOperator.of_finiteDimensional_range T

/-- **Corollary 6.2** of [brezis2011functional]. Let $E$ be a normed space and $F$ a Banach space.
Let $(T_n)$ be a sequence of operators of finite rank in $\mathcal{L}(E, F)$ and let
$T \in \mathcal{L}(E, F)$ with $\|T_n - T\| \to 0$. Then $T \in \mathcal{K}(E, F)$. -/
theorem corollary_6_2 [CompleteSpace F] {T : ℕ → E →L[ℝ] F} (hT : ∀ n, IsFiniteRank (T n))
    {S : E →L[ℝ] F} (h : Tendsto (fun n => ‖T n - S‖) atTop (𝓝 0)) : IsCompactOperator S :=
  IsCompactOperator.of_tendsto (fun n => (hT n).isCompactOperator) h

/-- **Remark 1** in Chapter 6 of [brezis2011functional], the approximation property of Hilbert
spaces. Let $E$ be a normed space and $F$ a Hilbert space, let $T \in \mathcal{K}(E, F)$, and
let $\varepsilon > 0$. Then there is an operator $T_\varepsilon \in \mathcal{L}(E, F)$ of finite
rank with $\|T_\varepsilon - T\| < \varepsilon$.

The source proves the bound $2\varepsilon$; the statement here is the same with $\varepsilon$
halved. The operator is $T_\varepsilon = P_G T$, where $G$ is the span of a finite
$\varepsilon/2$-net of $T(B_E)$. -/
theorem remark_6_1 {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {T : E →L[ℝ] F} (hT : IsCompactOperator T) {ε : ℝ} (hε : 0 < ε) :
    ∃ S : E →L[ℝ] F, IsFiniteRank S ∧ ‖S - T‖ < ε :=
  hT.exists_finiteDimensional_range_norm_sub_lt hε

/-- **Remark 1** in Chapter 6 of [brezis2011functional], the nonlinear approximation (3). Let $X$ be
a topological space, let $F$ be a Banach space, and let $T : X \to F$ be continuous with $T(X)$
of compact closure. Then for every $\varepsilon > 0$ there is a continuous map
$T_\varepsilon : X \to F$ whose range lies in a finite-dimensional subspace of $F$ and with
$\|T_\varepsilon x - T x\| < \varepsilon$ for all $x \in X$.

The construction of the source covers $K = \overline{T(X)}$ by finitely many balls
$B(f_i, \varepsilon/2)$, puts $q_i(x) = \max(\varepsilon - \|T x - f_i\|, 0)$ and $T_\varepsilon
x = \sum_i q_i(x) f_i / \sum_i q_i(x)$, a convex combination of points within $\varepsilon$ of
$T x$. This is the step from Brouwer's fixed point theorem to Schauder's fixed point theorem
(Exercise 6.26 of the source). -/
theorem remark_6_1_nonlinear {X : Type*} [TopologicalSpace X] {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] {T : X → F} (hT : Continuous T)
    (hK : IsCompact (closure (Set.range T))) {ε : ℝ} (hε : 0 < ε) :
    ∃ Tε : X → F, Continuous Tε ∧
      (∃ G : Submodule ℝ F, FiniteDimensional ℝ G ∧ ∀ x, Tε x ∈ G) ∧ ∀ x, ‖Tε x - T x‖ < ε := by
  obtain ⟨t, -, Tε, hc, hmem, hlt⟩ :=
    hT.exists_finset_mem_convexHull_norm_sub_lt (hK.totallyBounded.subset subset_closure) hε
  exact ⟨Tε, hc, ⟨Submodule.span ℝ (t : Set F), inferInstance, fun x =>
    convexHull_min Submodule.subset_span (Submodule.span ℝ _).convex (hmem x)⟩, hlt⟩

/-- **Proposition 6.3** of [brezis2011functional], first case. Let $E$, $F$, $G$ be normed spaces,
let $T \in \mathcal{L}(E, F)$ and let $S \in \mathcal{K}(F, G)$. Then
$S \circ T \in \mathcal{K}(E, G)$. -/
theorem proposition_6_3_left (T : E →L[ℝ] F) {S : F →L[ℝ] G} (hS : IsCompactOperator S) :
    IsCompactOperator (S ∘L T) :=
  hS.comp_clm T

/-- **Proposition 6.3** of [brezis2011functional], second case. Let $E$, $F$, $G$ be normed spaces,
let $T \in \mathcal{K}(E, F)$ and let $S \in \mathcal{L}(F, G)$. Then
$S \circ T \in \mathcal{K}(E, G)$. -/
theorem proposition_6_3_right {T : E →L[ℝ] F} (hT : IsCompactOperator T) (S : F →L[ℝ] G) :
    IsCompactOperator (S ∘L T) :=
  hT.clm_comp S

/-! ### Schauder's theorem and weak-to-strong continuity -/

/-- **Theorem 6.4** of [brezis2011functional] (Schauder). Let $E$ and $F$ be Banach spaces. If
$T \in \mathcal{K}(E, F)$, then its adjoint $T^\star$ belongs to
$\mathcal{K}(F^\star, E^\star)$.

The adjoint $T^\star$ is `ContinuousLinearMap.strongDualMap T`. -/
theorem theorem_6_4 [CompleteSpace E] [CompleteSpace F] {T : E →L[ℝ] F}
    (hT : IsCompactOperator T) : IsCompactOperator T.strongDualMap :=
  hT.strongDualMap

/-- **Theorem 6.4** of [brezis2011functional], the converse. Let $E$ and $F$ be Banach spaces and
let $T \in \mathcal{L}(E, F)$. If $T^\star \in \mathcal{K}(F^\star, E^\star)$, then
$T \in \mathcal{K}(E, F)$.

The proof uses only the completeness of $F$. -/
theorem theorem_6_4_mpr [CompleteSpace E] [CompleteSpace F] {T : E →L[ℝ] F}
    (hT : IsCompactOperator T.strongDualMap) : IsCompactOperator T :=
  IsCompactOperator.of_strongDualMap hT

/-- **Remark 2** in Chapter 6 of [brezis2011functional], first sentence. Let $E$ and $F$ be Banach
spaces and $T \in \mathcal{K}(E, F)$. If $u_n \rightharpoonup u$ weakly in $E$, then
$T u_n \to T u$ strongly in $F$.

This is also question 2 of Exercise 6.7 of the source. Weak convergence is
`Brezis.Chapter03.WeakTendsto`. -/
theorem remark_6_2 [CompleteSpace E] [CompleteSpace F] {T : E →L[ℝ] F}
    (hT : IsCompactOperator T) {u : ℕ → E} {x : E} (hu : WeakTendsto u x) :
    Tendsto (fun n => T (u n)) atTop (𝓝 (T x)) :=
  hT.tendsto_of_tendsto_toWeakSpace hu

/-- **Remark 2** in Chapter 6 of [brezis2011functional], second sentence. Let $E$ be a reflexive
Banach space, let $F$ be a Banach space, and let $T \in \mathcal{L}(E, F)$. If $T u_n \to T u$
strongly in $F$ for every sequence with $u_n \rightharpoonup u$ weakly in $E$, then
$T \in \mathcal{K}(E, F)$.

The source says that "the converse is also true if $E$ is reflexive (see Exercise 6.7)"; this is
question 4 of that exercise. Reflexivity is `Brezis.Chapter03.IsReflexive`. -/
theorem remark_6_2_mpr [CompleteSpace E] [CompleteSpace F] (hE : Brezis.Chapter03.IsReflexive E)
    (T : E →L[ℝ] F)
    (h : ∀ (u : ℕ → E) (x : E), WeakTendsto u x → Tendsto (fun n => T (u n)) atTop (𝓝 (T x))) :
    IsCompactOperator T :=
  haveI := Brezis.Chapter03.isReflexive_iff.1 hE
  IsCompactOperator.of_forall_tendsto_of_tendsto_toWeakSpace T h

end Brezis.Chapter06

end
