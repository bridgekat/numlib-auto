/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix.Determinant.Basic`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Data.Fintype.Perm
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# The Cauchy–Binet formula

The determinant of a product of rectangular matrices as a sum over selections of rows or columns,
over any commutative ring.

## Main results

* `Matrix.det_mul_eq_sum_prod_mul_det_submatrix`: for `P : Matrix p m R` and `Q : Matrix m p R`,
  `det (P Q) = ∑_{r : p → m} (∏ᵢ Q_{r i, i}) det (P_{·, r})` — the first step of Mathlib's
  `Matrix.det_mul`, for rectangular factors.
* `Matrix.factorial_mul_det_transpose_mul_diagonal_mul`: the Cauchy–Binet formula for a weighted
  Gram matrix, `p! det (Xᵀ D Y) = ∑_{r : p → m} (∏ᵢ d_{r i}) det (X_r) det (Y_r)`.

## Implementation notes

The formula is stated symmetrized over the orderings of the selected rows: the sum runs over all
maps `r : p → m` rather than over the `p`-element subsets of `m`. A non-injective `r` contributes
`0` (two equal rows), and each subset is counted `p!` times with the same sign in both
determinants, whence the factor `p!`. This keeps sorted subsets and their reindexings out of the
statement and the proof.
-/

namespace Matrix

section CauchyBinet

variable {R : Type*} [CommRing R] {m p : Type*} [Fintype m] [DecidableEq m] [Fintype p]
  [DecidableEq p]

omit [DecidableEq m] in
/-- **The determinant of a product over its column selections**: for `P : Matrix p m R` and
`Q : Matrix m p R`, `det (P Q) = ∑_{r : p → m} (∏ᵢ Q_{r i, i}) det (P_{·, r})`, where `P_{·, r}`
takes the columns `r` of `P`. The first step of Mathlib's `Matrix.det_mul`, for rectangular
factors. -/
theorem det_mul_eq_sum_prod_mul_det_submatrix (P : Matrix p m R) (Q : Matrix m p R) :
    (P * Q).det = ∑ r : p → m, (∏ i, Q (r i) i) * (P.submatrix id r).det := by
  simp only [det_apply', mul_apply, Finset.prod_univ_sum, Finset.mul_sum, Fintype.piFinset_univ,
    submatrix_apply, id]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.prod_mul_distrib]
  ring

/-- **The Cauchy–Binet formula**, symmetrized over the orderings of the selected rows: for
`X Y : Matrix m p R` and weights `d`,
`p! det (Xᵀ D Y) = ∑_{r : p → m} (∏ᵢ d_{r i}) det (X_r) det (Y_r)`, where `X_r` takes the rows
`r` of `X` (non-injective `r` contribute `0`, and each `p`-element row set is counted `p!` times,
with the same sign in both determinants). -/
theorem factorial_mul_det_transpose_mul_diagonal_mul (X Y : Matrix m p R) (d : m → R) :
    ((Fintype.card p).factorial : R) * (Xᵀ * diagonal d * Y).det =
      ∑ r : p → m, (∏ i, d (r i)) * (X.submatrix r id).det * (Y.submatrix r id).det := by
  have h1 : ∀ r : p → m, ((Xᵀ * diagonal d).submatrix id r).det =
      (∏ i, d (r i)) * (X.submatrix r id).det := fun r => by
    have : (Xᵀ * diagonal d).submatrix id r =
        (X.submatrix r id)ᵀ * diagonal fun i => d (r i) := by
      ext i j
      simp [mul_diagonal]
    rw [this, det_mul, det_transpose, det_diagonal, mul_comm]
  have h2 : ∀ σ : Equiv.Perm p, (Xᵀ * diagonal d * Y).det = ∑ r : p → m,
      (Equiv.Perm.sign σ : R) * (∏ i, Y (r (σ i)) i) *
        ((∏ i, d (r i)) * (X.submatrix r id).det) := fun σ => by
    rw [det_mul_eq_sum_prod_mul_det_submatrix]
    simp_rw [h1]
    rw [← (Equiv.arrowCongr σ.symm (Equiv.refl m)).sum_comp]
    refine Finset.sum_congr rfl fun r _ => ?_
    have e1 : (Equiv.arrowCongr σ.symm (Equiv.refl m) r) = r ∘ σ := by
      funext i
      simp
    have e2 : ∏ i, d ((r ∘ σ) i) = ∏ i, d (r i) := Equiv.prod_comp σ fun i => d (r i)
    have e3 : (X.submatrix (r ∘ σ) id).det = (Equiv.Perm.sign σ : R) * (X.submatrix r id).det := by
      have : X.submatrix (r ∘ σ) id = (X.submatrix r id).submatrix σ id := rfl
      rw [this, det_permute]
    rw [e1, e2, e3]
    simp only [Function.comp_apply]
    ring
  have hsum : ((Fintype.card p).factorial : R) * (Xᵀ * diagonal d * Y).det =
      ∑ σ : Equiv.Perm p, (Xᵀ * diagonal d * Y).det := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, nsmul_eq_mul]
  rw [hsum, Finset.sum_congr rfl fun σ _ => h2 σ, Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [det_apply' (Y.submatrix r id), Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [submatrix_apply, id]
  ring

end CauchyBinet

end Matrix
