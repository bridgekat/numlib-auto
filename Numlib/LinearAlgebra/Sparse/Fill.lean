/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.LinearAlgebra.Matrix.Cholesky

/-!
# Symbolic fill-in of the Cholesky factorization

Let $A$ be a square matrix whose index set is linearly ordered. The **symbolic Cholesky fill** of
$A$ is the least set of positions $(i, j)$ with $j < i$ that contains the strictly lower nonzero
pattern of $A$ and is closed under **Parter's rule**: if $(i, k)$ and $(j, k)$ are in the set and
$k < j < i$, then $(i, j)$ is in the set. In words, when the elimination of column $k$ reaches the
rows $j$ and $i$, it couples $i$ and $j$. This set is the *filled graph* of the literature on sparse
direct methods ([golub2013matrix], §11.1.6–11.1.7; S. Parter, *The use of linear graphs in Gauss
elimination*, SIAM Review 3 (1961); A. George and J. W. H. Liu, *Computer Solution of Large Sparse
Positive Definite Systems*, Chapter 5). It depends only on the pattern of $A$, and it is defined
here as an inductive predicate, with no graph.

The main theorem is that the Cholesky factor vanishes outside the symbolic fill, with no hypothesis
on numerical cancellation. This is the fact on which the symbolic factorization relies: the storage
for the predicted fill is allocated before any number is computed. A consequence is the separator
property of nested dissection: if an initial segment of the ordering is not coupled to a set of
later indices, then the Cholesky factor has the same zero block.

## Main definitions

* `Matrix.IsCholeskyFill`: the symbolic Cholesky fill of a matrix.

## Main results

* `Matrix.IsCholesky.apply_eq_zero_of_not_isCholeskyFill`: an entry of the lower Cholesky factor at
  a position $(i, j)$, $j < i$, outside the symbolic fill is zero.
* `Matrix.not_isCholeskyFill_of_isLowerSet_of_forall_eq_zero`: the **separator lemma**. If no entry
  of $A$ couples a row in $T$ to a column in an initial segment $S$ of the ordering, then the
  symbolic fill has no position in $T \times S$.
* `Matrix.IsCholesky.apply_eq_zero_of_separated`: in the same situation the Cholesky factor has a
  zero block in $T \times S$. This is why nested dissection keeps its zero blocks.

## Proof outline

The main theorem is proved by strong induction on the column through the Cholesky recurrence
`Matrix.IsCholesky.star_apply_mul_diag_eq`. If $(i, j)$ is not fill, then $a_{ij} = 0$, and no term
of the sum in the recurrence is nonzero, because such a term would make $(i, k)$ and $(j, k)$ fill
by the induction hypothesis, and then $(i, j)$ fill by Parter's rule. The separator lemma is an
induction on the definition of the fill.

## Implementation notes

* The backbone Cholesky specification `Matrix.IsCholesky A H` has $H$ *upper* triangular with
  $H^H H = A$. The lower factor $G = H^H$ of the books has $g_{ij} = \overline{h_{ji}}$, so a zero
  of $g_{ij}$ is a zero of `H j i`.
* The literature states Parter's two facts as "$g_{ij}$ is nonzero, assuming no numerical
  cancellation". That direction has no exact meaning, because a cancellation can make any predicted
  entry zero, and it is not formalized. Only the converse direction, proved here, is a theorem.
-/

namespace Matrix

variable {n R : Type*} [LinearOrder n]

section Fill

variable [Zero R]

/-- Let $A$ be a square matrix over a type $R$ with zero, with a linearly ordered index set. The
**symbolic Cholesky fill** of $A$ is the least relation on positions $(i, j)$ such that

* if $j < i$ and $a_{ij} \neq 0$, then $(i, j)$ is fill (`Matrix.IsCholeskyFill.of_ne_zero`, the
  first of Parter's facts);
* if $k < j < i$ and $(i, k)$ and $(j, k)$ are fill, then $(i, j)$ is fill
  (`Matrix.IsCholeskyFill.trans`, **Parter's rule**, the second of Parter's facts).

It predicts the strictly lower nonzero pattern of the Cholesky factor ([golub2013matrix],
§11.1.6). Every fill position is strictly below the diagonal (`Matrix.IsCholeskyFill.lt`). -/
inductive IsCholeskyFill (A : Matrix n n R) : n → n → Prop
  /-- A position $(i, j)$ with $j < i$ and $a_{ij} \neq 0$ is fill. -/
  | of_ne_zero {i j : n} (hji : j < i) (h : A i j ≠ 0) : IsCholeskyFill A i j
  /-- **Parter's rule**: if $k < j < i$ and $(i, k)$ and $(j, k)$ are fill, then $(i, j)$ is fill.
  The elimination of column $k$ couples the two rows that it reaches. -/
  | trans {i j k : n} (hkj : k < j) (hji : j < i) (hik : IsCholeskyFill A i k)
      (hjk : IsCholeskyFill A j k) : IsCholeskyFill A i j

/-- If $(i, j)$ is in the symbolic Cholesky fill of $A$, then $j < i$. -/
theorem IsCholeskyFill.lt {A : Matrix n n R} {i j : n} (h : A.IsCholeskyFill i j) : j < i := by
  cases h with
  | of_ne_zero hji _ => exact hji
  | trans _ hji _ _ => exact hji

/-- The **separator lemma**. Let $A$ be a square matrix with a linearly ordered index set, let $S$
be a lower set of indices (an initial segment of the ordering) and let $T$ be a set of indices.
If $a_{ij} = 0$ for all $i \in T$ and $j \in S$, then no position $(i, j)$ with $i \in T$ and
$j \in S$ is in the symbolic Cholesky fill of $A$.

Parter's rule produces $(i, j)$ only from a position $(i, k)$ with $k < j$, and such a $k$ is
again in $S$. This is why nested dissection ([golub2013matrix], §11.1.7) creates no fill between
the two dissected halves: the first half is numbered before the second and is not coupled to it. -/
theorem not_isCholeskyFill_of_isLowerSet_of_forall_eq_zero {A : Matrix n n R} {S T : Set n}
    (hS : IsLowerSet S) (hTS : ∀ i ∈ T, ∀ j ∈ S, A i j = 0) :
    ∀ i ∈ T, ∀ j ∈ S, ¬ A.IsCholeskyFill i j := by
  intro i hi j hj h
  induction h with
  | of_ne_zero _ hne => exact hne (hTS _ hi _ hj)
  | trans hkj _ _ _ ih₁ _ => exact ih₁ hi (hS hkj.le hj)

end Fill

section Cholesky

variable [Fintype n] {𝕜 : Type*} [RCLike 𝕜]

/-- Let $A$ be a square matrix over $\mathbb{R}$ or $\mathbb{C}$ with a finite linearly ordered
index set, and let $H$ be its Cholesky factor: $H$ is upper triangular with positive diagonal
and $H^H H = A$. If $j < i$ and $(i, j)$ is not in the symbolic Cholesky fill of $A$, then
$h_{ji} = 0$, that is, the entry $g_{ij}$ of the lower factor $G = H^H$ is zero.

This is the half of Parter's facts ([golub2013matrix], §11.1.6, Facts 1–2) that holds exactly,
with no hypothesis on cancellation. The proof is a strong induction on the column $j$ through
the Cholesky recurrence $\bar h_{ji} h_{jj} = a_{ij} - \sum_{k < j} \bar h_{ki} h_{kj}$: there
$a_{ij} = 0$, since otherwise $(i, j)$ is fill; no term of the sum is nonzero, since
$h_{ki} \neq 0 \neq h_{kj}$ would make $(i, k)$ and $(j, k)$ fill by the induction hypothesis
and then $(i, j)$ fill by Parter's rule; and $h_{jj} \neq 0$. -/
theorem IsCholesky.apply_eq_zero_of_not_isCholeskyFill {A H : Matrix n n 𝕜} (h : A.IsCholesky H)
    {i j : n} (hji : j < i) (hfill : ¬ A.IsCholeskyFill i j) : H j i = 0 := by
  have main : ∀ j i : n, j < i → ¬ A.IsCholeskyFill i j → H j i = 0 := by
    intro j
    induction j using WellFoundedLT.induction with
    | ind j ih =>
      intro i hji hfill
      have key := h.star_apply_mul_diag_eq hji
      have hA : A i j = 0 := by
        by_contra hne
        exact hfill (.of_ne_zero hji hne)
      have hsum : ∑ k with k < j, star (H k i) * H k j = 0 := by
        refine Finset.sum_eq_zero fun k hk => ?_
        have hkj : k < j := (Finset.mem_filter.mp hk).2
        by_cases hki : H k i = 0
        · rw [hki, star_zero, zero_mul]
        by_cases hkj' : H k j = 0
        · rw [hkj', mul_zero]
        exfalso
        have f₁ : A.IsCholeskyFill i k := by
          by_contra hc
          exact hki (ih k hkj i (hkj.trans hji) hc)
        have f₂ : A.IsCholeskyFill j k := by
          by_contra hc
          exact hkj' (ih k hkj j hkj hc)
        exact hfill (.trans hkj hji f₁ f₂)
      rw [hA, hsum, sub_zero] at key
      rcases mul_eq_zero.mp key with h₁ | h₁
      · exact star_eq_zero.mp h₁
      · exact absurd h₁ (h.diag_ne_zero j)
  exact main j i hji hfill

/-- **Nested dissection keeps its zero blocks** ([golub2013matrix], §11.1.7). Let $A$ be a square
matrix over $\mathbb{R}$ or $\mathbb{C}$ with a finite linearly ordered index set, with Cholesky
factor $H$ ($H$ upper triangular with positive diagonal and $H^H H = A$). Let $S$ be a lower set
of indices and $T$ a set of indices with $a_{ij} = 0$ for all $i \in T$ and $j \in S$. Then
$h_{ji} = 0$ for all $i \in T$ and $j \in S$ with $j < i$: the lower Cholesky factor $G = H^H$
has the same zero block as $A$. -/
theorem IsCholesky.apply_eq_zero_of_separated {A H : Matrix n n 𝕜} (h : A.IsCholesky H)
    {S T : Set n} (hS : IsLowerSet S) (hTS : ∀ i ∈ T, ∀ j ∈ S, A i j = 0) {i j : n} (hi : i ∈ T)
    (hj : j ∈ S) (hji : j < i) : H j i = 0 :=
  h.apply_eq_zero_of_not_isCholeskyFill hji
    (not_isCholeskyFill_of_isLowerSet_of_forall_eq_zero hS hTS i hi j hj)

end Cholesky

end Matrix
