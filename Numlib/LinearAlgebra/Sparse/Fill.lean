import Numlib.LinearAlgebra.Matrix.Cholesky

/-!
# Symbolic fill-in of the Cholesky factorization

Which entries of the Cholesky factor of a sparse matrix can be nonzero, read off the pattern of the
matrix alone. `Matrix.IsCholeskyFill A i j` (always with `j < i`) is the least relation containing
the strictly lower pattern of `A` and closed under **Parter's rule**: if the column `k` of the
factor reaches the rows `j` and `i`, `k < j < i`, then eliminating `k` couples `i` and `j`. It is
the *filled graph* of the sparse-direct literature, stated as an inductive predicate over any
linearly ordered index type, with no graph in sight.

The literature states Parter's two facts as "`g_ij` is nonzero, assuming no numerical
cancellation". That direction has no exact reading — a cancellation can make any predicted entry
zero — and it is not formalized. What is a theorem, and what the symbolic factorization (allocate
the predicted fill before computing anything) relies on, is the converse:
`Matrix.IsCholesky.apply_eq_zero_of_not_isCholeskyFill`, the Cholesky factor vanishes outside the
predicted fill, with no cancellation hypothesis.

The backbone Cholesky specification `Matrix.IsCholesky A H` has `H` *upper* triangular with
`Hᴴ H = A`, so the lower factor `G = Hᴴ` of the books has `g_ij = star (H j i)`, and a zero of
`g_ij` is a zero of `H j i`.

## Main results

* `Matrix.IsCholesky.apply_eq_zero_of_not_isCholeskyFill`: strong induction on the column through
  the Cholesky recurrence `Matrix.IsCholesky.star_apply_mul_diag_eq`.
* `Matrix.not_isCholeskyFill_of_isLowerSet_of_forall_eq_zero`, the **separator lemma**: an initial
  segment of the ordering that is uncoupled from a set of later indices creates no fill between
  them. Its corollary `Matrix.IsCholesky.apply_eq_zero_of_separated` is why nested dissection works:
  the Cholesky factor inherits the zero blocks of the dissected ordering.

## References

[golub2013matrix] §11.1.6–11.1.7; S. Parter, *The use of linear graphs in Gauss elimination*, SIAM
Review 3 (1961); A. George and J. W. H. Liu, *Computer Solution of Large Sparse Positive Definite
Systems*, Ch. 5.
-/

namespace Matrix

variable {n R : Type*} [LinearOrder n]

section Fill

variable [Zero R]

/-- **The symbolic Cholesky fill** of `A`: the least relation on positions `(i, j)` with `j < i`
that contains the strictly lower nonzero pattern of `A` (`of_ne_zero`, the first of Parter's facts)
and is closed under Parter's rule (`trans`, the second): if `(i, k)` and `(j, k)` are fill with
`k < j < i`, so is `(i, j)`. It predicts the strictly lower nonzero pattern of the Cholesky factor
([golub2013matrix] §11.1.6). -/
inductive IsCholeskyFill (A : Matrix n n R) : n → n → Prop
  /-- A strictly lower nonzero entry of `A` is fill. -/
  | of_ne_zero {i j : n} (hji : j < i) (h : A i j ≠ 0) : IsCholeskyFill A i j
  /-- **Parter's rule**: eliminating the column `k` couples every two rows it reaches. -/
  | trans {i j k : n} (hkj : k < j) (hji : j < i) (hik : IsCholeskyFill A i k)
      (hjk : IsCholeskyFill A j k) : IsCholeskyFill A i j

/-- Fill positions lie strictly below the diagonal. -/
theorem IsCholeskyFill.lt {A : Matrix n n R} {i j : n} (h : A.IsCholeskyFill i j) : j < i := by
  cases h with
  | of_ne_zero hji _ => exact hji
  | trans _ hji _ _ => exact hji

/-- **The separator lemma.** If `S` is an initial segment of the ordering (a lower set) and no
entry of `A` couples a row of `T` to a column of `S`, then there is no fill between them either:
Parter's rule only ever produces `(i, j)` from some `(i, k)` with `k < j`, and `k` stays in `S`.
This is why nested dissection ([golub2013matrix] §11.1.7) creates no fill between the two dissected
halves, the first being numbered before the second and uncoupled from it. -/
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

/-- **The Cholesky factor vanishes outside the symbolic fill** — the rigorous half of Parter's facts
([golub2013matrix] §11.1.6, Facts 1–2), with no hypothesis on cancellation: if `(i, j)`, `j < i`,
is not fill, then `H j i = 0`, that is, the entry `g_ij` of the lower factor `G = Hᴴ` vanishes.

By strong induction on the column `j`: the Cholesky recurrence
`star (H j i) H j j = A i j - ∑_{k < j} star (H k i) H k j` has `A i j = 0` (else `(i, j)` is fill)
and no nonzero term (a term with `H k i ≠ 0 ≠ H k j` would make `(i, k)` and `(j, k)` fill by the
induction hypothesis, and then `(i, j)` by Parter's rule), and `H j j ≠ 0`. -/
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

/-- **Nested dissection keeps its zero blocks** ([golub2013matrix] §11.1.7). If `S` is an initial
segment of the ordering and `A` has no entry coupling a row of `T` to a column of `S`, then the
lower Cholesky factor has the same zero block: `H j i = 0` for `i ∈ T`, `j ∈ S`, `j < i`. -/
theorem IsCholesky.apply_eq_zero_of_separated {A H : Matrix n n 𝕜} (h : A.IsCholesky H)
    {S T : Set n} (hS : IsLowerSet S) (hTS : ∀ i ∈ T, ∀ j ∈ S, A i j = 0) {i j : n} (hi : i ∈ T)
    (hj : j ∈ S) (hji : j < i) : H j i = 0 :=
  h.apply_eq_zero_of_not_isCholeskyFill hji
    (not_isCholeskyFill_of_isLowerSet_of_forall_eq_zero hS hTS i hi j hj)

end Cholesky

end Matrix
