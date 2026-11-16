/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.RingTheory.Finiteness.Cofinite
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Numlib.Analysis.Normed.Module.FiniteCodim
import NumlibSurface.Brezis.Chapter02.Section04

/-!
# Brezis, Section 11.1: Finite-dimensional and finite-codimensional spaces

This module formalizes Section 11.1 of [brezis2011functional] over a real Banach space $E$. A
finite-dimensional subspace of $E$ is closed (Proposition 11.1), every linear operator on a
finite-dimensional space is bounded (Proposition 11.2), and a Banach space with a finite-dimensional
dual is finite-dimensional (Proposition 11.3). If $M$ is closed and $X$ is finite-dimensional, then
$M + X$ is closed, and it admits a complement if and only if $M$ does (Proposition 11.4). A subspace
$M$ has finite codimension if $M + X = E$ for some finite-dimensional subspace $X$. A subspace that
contains a closed subspace of finite codimension is closed (Proposition 11.5), a closed subspace of
finite codimension has a complement inside any dense subspace (Proposition 11.6), and Proposition
11.7 gives complements from $G + L + X_1 = E$ and $G \cap L \subseteq X_2$.

Most results are in Mathlib: Propositions 11.1, 11.2 and 11.5 and the closedness part of Proposition
11.4 are `Submodule.closed_of_finiteDimensional`, `LinearMap.continuous_of_finiteDimensional`,
`Submodule.isClosed_mono_of_finiteDimensional_quotient` and
`Submodule.isClosed_sup_finiteDimensional`. The rest, namely $\dim X^* = \dim X$, Proposition 11.3,
the complement part of Proposition 11.4 and Propositions 11.6 and 11.7, specializes the backbone
module `Numlib.Analysis.Normed.Module.FiniteCodim`, which is stated over `RCLike 𝕜` and read here at
`ℝ`.

## Main definitions

* Section 11.1, definition of finite codimension, `Brezis.Chapter11.IsFiniteCodim`: $M + X = E$ for
  some finite-dimensional subspace $X$.
* Section 11.1, the codimension, `Brezis.Chapter11.codim`: $\operatorname{codim} M = \dim(E/M)$.

## Main results

* Proposition 11.1, `Brezis.Chapter11.proposition_11_1`: a finite-dimensional subspace of a Banach
  space is closed.
* Proposition 11.2, `Brezis.Chapter11.proposition_11_2`: a linear operator from a finite-dimensional
  space to a Banach space is bounded.
* Proposition 11.2, `Brezis.Chapter11.proposition_11_2_functional`: every linear functional on a
  finite-dimensional space is continuous.
* Section 11.1, after Proposition 11.2, `Brezis.Chapter11.finrank_dual`: $\dim X^* = \dim X$ for
  finite-dimensional $X$.
* Section 11.1, after Proposition 11.2, `Brezis.Chapter11.coord_basis_strongDual`: the coordinate
  functionals of a basis form a basis of $X^*$.
* Proposition 11.3, `Brezis.Chapter11.proposition_11_3`: if $X$ is a Banach space and $X^*$ is
  finite-dimensional, then $X$ is finite-dimensional and $\dim X = \dim X^*$.
* Section 11.1, complements, `Brezis.Chapter11.admitsComplement_iff`: the complements of Section 2.4
  agree with Mathlib's `Submodule.ClosedComplemented`.
* Proposition 11.4, `Brezis.Chapter11.proposition_11_4`: $M + X$ is closed.
* Proposition 11.4, `Brezis.Chapter11.proposition_11_4_closedComplemented`: $M + X$ admits a
  complement if and only if $M$ does.
* Section 11.1, definition of finite codimension, `Brezis.Chapter11.isFiniteCodim_iff_coFG`: finite
  codimension is Mathlib's `Submodule.CoFG`.
* Section 11.1, definition of finite codimension,
  `Brezis.Chapter11.IsFiniteCodim.exists_finiteDimensional_isCompl`: one may assume
  $M \cap X = \{0\}$.
* Section 11.1, the codimension, `Brezis.Chapter11.codim_eq_finrank_of_isCompl`: the codimension is
  the dimension of any algebraic complement.
* Proposition 11.5, `Brezis.Chapter11.proposition_11_5`: a subspace that contains a closed subspace
  of finite codimension is closed.
* Proposition 11.6, `Brezis.Chapter11.proposition_11_6`: a closed subspace of finite codimension has
  a complement inside any dense subspace.
* Proposition 11.7, `Brezis.Chapter11.proposition_11_7`: if $G + L + X_1 = E$ and
  $G \cap L \subseteq X_2$ with $X_1, X_2$ finite-dimensional, then $G$ and $L$ admit complements.

## Conventions

* "$M$ admits a complement" is `∃ N, Brezis.Chapter02.IsComplement M N` of Section 2.4: a closed
  subspace $N$ with $M \cap N = \{0\}$ and $M + N = E$. For a closed $M$ in a Banach space this is
  Mathlib's `Submodule.ClosedComplemented M` (`Brezis.Chapter11.admitsComplement_iff`). The theorems
  are stated with the phrase of the source and connected to the backbone through that lemma.
* "Finite codimension" is `Brezis.Chapter11.IsFiniteCodim M`, identified with Mathlib's
  `Submodule.CoFG M`, that is, `Module.Finite ℝ (E ⧸ M)`, by
  `Brezis.Chapter11.isFiniteCodim_iff_coFG`. The codimension is `Module.finrank ℝ (E ⧸ M)`.

## Implementation notes

* The theorems carry the hypothesis `[CompleteSpace E]` of the source whether or not the proof uses
  it.

## Not formalized

* **The facts about $\mathbb{R}^p$ in the opening sentence** (completeness, equivalence of norms,
  compactness of the unit ball). They are Mathlib's `FiniteDimensional.complete`,
  `ContinuousLinearEquiv.ofFinrankEq` and `FiniteDimensional.proper`.
* **The two bracketed warnings**, that a sum of closed subspaces need not be closed and that a
  subspace of finite codimension need not be closed.
-/

open Module

namespace Brezis.Chapter11

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### Finite-dimensional spaces -/

/-- **Proposition 11.1** of [brezis2011functional]. Let $E$ be a Banach space and let
$X \subseteq E$ be a finite-dimensional subspace. Then $X$ is closed. -/
theorem proposition_11_1 [CompleteSpace E] (X : Submodule ℝ E) [FiniteDimensional ℝ X] :
    IsClosed (X : Set E) :=
  X.closed_of_finiteDimensional

/-- **Proposition 11.2** of [brezis2011functional]. Let $X$ be a finite-dimensional normed space and
$F$ a Banach space. Then every linear operator $T : X \to F$ is bounded: $T$ is continuous, and
there is a constant $C$ with
$$\|T x\| \le C \|x\| \qquad \text{for all } x \in X.$$

In the source, $C$ is $\max_i \|T e_i\|$ times the constant of the equivalence of norms. -/
theorem proposition_11_2 {X F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (T : X →ₗ[ℝ] F) : Continuous T ∧ ∃ C : ℝ, ∀ x, ‖T x‖ ≤ C * ‖x‖ :=
  ⟨T.continuous_of_finiteDimensional,
    ⟨‖LinearMap.toContinuousLinearMap T‖, fun x =>
      (LinearMap.toContinuousLinearMap T).le_opNorm x⟩⟩

/-- **Proposition 11.2** of [brezis2011functional], "in particular". Let $X$ be a finite-dimensional
normed space. Then every linear functional $f : X \to \mathbb{R}$ is continuous. -/
theorem proposition_11_2_functional {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] (f : X →ₗ[ℝ] ℝ) : Continuous f :=
  f.continuous_of_finiteDimensional

/-- **Section 11.1** of [brezis2011functional], the paragraph after Proposition 11.2. Let $X$ be a
finite-dimensional normed space. Then the dual space $X^*$ is finite-dimensional, and
$\dim X^* = \dim X$.

The dual space $X^*$ is `StrongDual ℝ X`. -/
theorem finrank_dual {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] :
    FiniteDimensional ℝ (StrongDual ℝ X) ∧ finrank ℝ (StrongDual ℝ X) = finrank ℝ X :=
  ⟨(LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := X) (F' := ℝ)).finiteDimensional,
    NormedSpace.finrank_strongDual⟩

/-- **Section 11.1** of [brezis2011functional], the paragraph after Proposition 11.2, "more
precisely". Let $X$ be a finite-dimensional normed space and let $(e_i)_{i \in I}$ be a basis of
$X$, with $I$ finite. Write $x = \sum_i x_i e_i$ and set $f_i(x) = x_i$. Then there is a basis
$(f_i)_{i \in I}$ of $X^*$ with $f_i(x) = x_i$ for all $i$ and $x$. -/
theorem coord_basis_strongDual {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] {ι : Type*} [Finite ι] (b : Basis ι ℝ X) :
    ∃ b' : Basis ι ℝ (StrongDual ℝ X), ∀ i x, b' i x = b.repr x i := by
  classical
  exact ⟨b.dualBasis.map LinearMap.toContinuousLinearMap, fun i x => by
    rw [Basis.map_apply]
    exact b.dualBasis_apply i x⟩

/-- **Proposition 11.3** of [brezis2011functional]. Let $X$ be a Banach space such that $X^*$ is
finite-dimensional. Then $X$ is finite-dimensional and $\dim X = \dim X^*$. -/
theorem proposition_11_3 {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [FiniteDimensional ℝ (StrongDual ℝ X)] :
    FiniteDimensional ℝ X ∧ finrank ℝ X = finrank ℝ (StrongDual ℝ X) :=
  have := NormedSpace.finiteDimensional_of_finiteDimensional_strongDual (𝕜 := ℝ) (E := X)
  ⟨this, NormedSpace.finrank_strongDual.symm⟩

/-! ### Complements -/

/-- **Section 11.1** of [brezis2011functional], the meaning of "admits a complement". Let $E$ be a
Banach space and $M \subseteq E$ a subspace. Then $M$ is closed and admits a complement in the
sense of Section 2.4, that is, a closed subspace $N$ with $M \cap N = \{0\}$ and $M + N = E$, if
and only if $M$ is `Submodule.ClosedComplemented` in the sense of Mathlib.

The complement of Section 2.4 is `Brezis.Chapter02.IsComplement`. -/
theorem admitsComplement_iff [CompleteSpace E] (M : Submodule ℝ E) :
    M.ClosedComplemented ↔ IsClosed (M : Set E) ∧ ∃ N, Chapter02.IsComplement M N :=
  Submodule.closedComplemented_iff_isClosed_exists_isClosed_isCompl

/-- **Proposition 11.4** of [brezis2011functional], first part. Let $E$ be a Banach space,
$M \subseteq E$ a closed subspace and $X \subseteq E$ a finite-dimensional subspace. Then
$M + X$ is closed. -/
theorem proposition_11_4 [CompleteSpace E] {M : Submodule ℝ E} (hM : IsClosed (M : Set E))
    (X : Submodule ℝ E) [FiniteDimensional ℝ X] :
    IsClosed ((M ⊔ X : Submodule ℝ E) : Set E) :=
  Submodule.isClosed_sup_finiteDimensional M X hM

/-- **Proposition 11.4** of [brezis2011functional], "moreover". Let $E$ be a Banach space,
$M \subseteq E$ a closed subspace and $X \subseteq E$ a finite-dimensional subspace. Then
$M + X$ admits a complement in $E$ if and only if $M$ admits a complement in $E$.

A complement is `Brezis.Chapter02.IsComplement` of Section 2.4. -/
theorem proposition_11_4_closedComplemented [CompleteSpace E] {M : Submodule ℝ E}
    (hM : IsClosed (M : Set E)) (X : Submodule ℝ E) [FiniteDimensional ℝ X] :
    (∃ N, Chapter02.IsComplement (M ⊔ X) N) ↔ ∃ N, Chapter02.IsComplement M N := by
  have hMX : IsClosed ((M ⊔ X : Submodule ℝ E) : Set E) := proposition_11_4 hM X
  refine ((and_iff_right hMX).symm.trans (admitsComplement_iff _).symm).trans ?_
  refine (Submodule.closedComplemented_sup_finiteDimensional_iff hM X).trans ?_
  exact (admitsComplement_iff M).trans (and_iff_right hM)

/-! ### Finite codimension -/

/-- **Section 11.1** of [brezis2011functional], definition of finite codimension. Let $E$ be a
normed space. A subspace $M \subseteq E$ has **finite codimension** if there is a
finite-dimensional subspace $X \subseteq E$ with $M + X = E$.

The source states the definition for a Banach space $E$. The definition does not need
completeness. -/
def IsFiniteCodim (M : Submodule ℝ E) : Prop :=
  ∃ X : Submodule ℝ E, FiniteDimensional ℝ X ∧ M ⊔ X = ⊤

/-- **Section 11.1** of [brezis2011functional], definition of finite codimension. A subspace $M$ of
a normed space $E$ has finite codimension if and only if $E/M$ is finite-dimensional, that is,
if and only if $M$ is `Submodule.CoFG`. -/
theorem isFiniteCodim_iff_coFG (M : Submodule ℝ E) : IsFiniteCodim M ↔ M.CoFG := by
  constructor
  · rintro ⟨X, hX, hsup⟩
    exact (Module.Finite.iff_fg.1 hX).cofg_of_codisjoint (codisjoint_iff.2 (by rwa [sup_comm]))
  · intro h
    obtain ⟨X, hX⟩ := M.exists_isCompl
    exact ⟨X, Module.Finite.iff_fg.2 (h.fg_of_isCompl hX), hX.sup_eq_top⟩

/-- **Section 11.1** of [brezis2011functional], "we may always assume that $M \cap X = \{0\}$". If a
subspace $M$ of a normed space $E$ has finite codimension, then there is a finite-dimensional
subspace $X$ with $M \cap X = \{0\}$ and $M + X = E$. -/
theorem IsFiniteCodim.exists_finiteDimensional_isCompl {M : Submodule ℝ E}
    (h : IsFiniteCodim M) : ∃ X : Submodule ℝ E, FiniteDimensional ℝ X ∧ IsCompl M X := by
  have := (isFiniteCodim_iff_coFG M).1 h
  obtain ⟨X, hX⟩ := M.exists_isCompl
  exact ⟨X, Module.Finite.iff_fg.2 (Submodule.CoFG.fg_of_isCompl hX this), hX⟩

/-- **Section 11.1** of [brezis2011functional], the codimension. The **codimension** of a subspace
$M$ of a normed space $E$ is $\operatorname{codim} M = \dim(E/M)$.

The source defines $\operatorname{codim} M$ as the dimension of a finite-dimensional complement
$X$ of $M$ and notes that "it coincides with $\dim (E/M)$"; the definition here takes the second
form (see `Brezis.Chapter11.codim_eq_finrank_of_isCompl`). When $E/M$ is infinite-dimensional
the value is $0$, as for `Module.finrank`. -/
noncomputable def codim (M : Submodule ℝ E) : ℕ :=
  finrank ℝ (E ⧸ M)

/-- **Section 11.1** of [brezis2011functional], the codimension. Let $M$ and $X$ be subspaces of a
normed space $E$ with $M \cap X = \{0\}$ and $M + X = E$. Then
$\operatorname{codim} M = \dim X$; so the codimension is "independent of the special choice of
$X$".

If $X$ is infinite-dimensional, both sides are $0$ by the convention of `Module.finrank`. -/
theorem codim_eq_finrank_of_isCompl {M X : Submodule ℝ E} (h : IsCompl M X) :
    codim M = finrank ℝ X :=
  (M.quotientEquivOfIsCompl X h).finrank_eq

/-- **Proposition 11.5** of [brezis2011functional]. Let $E$ be a Banach space and $M \subseteq E$ a
closed subspace of finite codimension. Then every subspace $\tilde M$ of $E$ that contains $M$
is closed. -/
theorem proposition_11_5 [CompleteSpace E] {M M' : Submodule ℝ E} (hM : IsClosed (M : Set E))
    (hcodim : IsFiniteCodim M) (hle : M ≤ M') : IsClosed (M' : Set E) :=
  have := (isFiniteCodim_iff_coFG M).1 hcodim
  Submodule.isClosed_mono_of_finiteDimensional_quotient hM hle

/-- **Proposition 11.6** of [brezis2011functional]. Let $E$ be a Banach space, $M \subseteq E$ a
closed subspace of finite codimension, and $D \subseteq E$ a dense subspace. Then there is a
complement $X$ of $M$ with $X \subseteq D$.

A complement is `Brezis.Chapter02.IsComplement` of Section 2.4. -/
theorem proposition_11_6 [CompleteSpace E] {M D : Submodule ℝ E} (hM : IsClosed (M : Set E))
    (hcodim : IsFiniteCodim M) (hD : Dense (D : Set E)) :
    ∃ X : Submodule ℝ E, X ≤ D ∧ Chapter02.IsComplement M X := by
  have := (isFiniteCodim_iff_coFG M).1 hcodim
  obtain ⟨X, hXD, hMX⟩ := Submodule.exists_isCompl_le_of_dense hM hD
  have : FiniteDimensional ℝ X := Module.Finite.iff_fg.2 (Submodule.CoFG.fg_of_isCompl hMX this)
  exact ⟨X, hXD, X.closed_of_finiteDimensional, hMX⟩

/-- **Proposition 11.7** of [brezis2011functional]. Let $E$ be a Banach space and $G, L \subseteq E$
closed subspaces. Assume that there are finite-dimensional subspaces $X_1, X_2 \subseteq E$ with
$$G + L + X_1 = E \qquad \text{and} \qquad G \cap L \subseteq X_2.$$
Then $G$ admits a complement, and $L$ admits a complement.

A complement is `Brezis.Chapter02.IsComplement` of Section 2.4. -/
theorem proposition_11_7 [CompleteSpace E] {G L : Submodule ℝ E} (hG : IsClosed (G : Set E))
    (hL : IsClosed (L : Set E)) (X₁ X₂ : Submodule ℝ E) [FiniteDimensional ℝ X₁]
    [FiniteDimensional ℝ X₂] (hsup : G ⊔ L ⊔ X₁ = ⊤) (hinf : G ⊓ L ≤ X₂) :
    (∃ N, Chapter02.IsComplement G N) ∧ ∃ N, Chapter02.IsComplement L N := by
  constructor
  · exact ((admitsComplement_iff G).1
      (Submodule.closedComplemented_of_sup_sup_eq_top_of_inf_le hG hL X₁ X₂ hsup hinf)).2
  · refine ((admitsComplement_iff L).1
      (Submodule.closedComplemented_of_sup_sup_eq_top_of_inf_le hL hG X₁ X₂ ?_ ?_)).2
    · rwa [sup_comm L G]
    · rwa [inf_comm L G]

end Brezis.Chapter11
