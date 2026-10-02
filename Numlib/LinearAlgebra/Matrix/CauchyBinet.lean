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
* `Matrix.factorial_mul_det_mul`: **the Cauchy–Binet formula**, for `P : Matrix p m R` and
  `Q : Matrix m p R`, `p! det (P Q) = ∑_{r : p → m} det (P_{·, r}) det (Q_{r, ·})`.
* `Matrix.factorial_mul_det_transpose_mul_diagonal_mul`: its weighted Gram case,
  `p! det (Xᵀ D Y) = ∑_{r : p → m} (∏ᵢ d_{r i}) det (X_r) det (Y_r)`.

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

omit [DecidableEq m] in
/-- **The Cauchy–Binet formula**, symmetrized over the orderings of the selected indices: for
`P : Matrix p m R` and `Q : Matrix m p R`,
`p! det (P Q) = ∑_{r : p → m} det (P_{·, r}) det (Q_{r, ·})`, where `P_{·, r}` takes the columns
`r` of `P` and `Q_{r, ·}` the rows `r` of `Q` (non-injective `r` contribute `0`, and each
`p`-element index set is counted `p!` times, with the same sign in both determinants). Each
ordering `σ` of the selection rewrites `Matrix.det_mul_eq_sum_prod_mul_det_submatrix` with a
sign, and summing over `σ` assembles `det (Q_{r, ·})`. -/
theorem factorial_mul_det_mul (P : Matrix p m R) (Q : Matrix m p R) :
    ((Fintype.card p).factorial : R) * (P * Q).det =
      ∑ r : p → m, (P.submatrix id r).det * (Q.submatrix r id).det := by
  have h2 : ∀ σ : Equiv.Perm p, (P * Q).det = ∑ r : p → m,
      (Equiv.Perm.sign σ : R) * (∏ i, Q (r (σ i)) i) * (P.submatrix id r).det := fun σ => by
    rw [det_mul_eq_sum_prod_mul_det_submatrix]
    rw [← (Equiv.arrowCongr σ.symm (Equiv.refl m)).sum_comp]
    refine Finset.sum_congr rfl fun r _ => ?_
    have e1 : (Equiv.arrowCongr σ.symm (Equiv.refl m) r) = r ∘ σ := by
      funext i
      simp
    have e3 : (P.submatrix id (r ∘ σ)).det = (Equiv.Perm.sign σ : R) * (P.submatrix id r).det := by
      have : P.submatrix id (r ∘ σ) = (P.submatrix id r).submatrix id σ := rfl
      rw [this, det_permute']
    rw [e1, e3]
    simp only [Function.comp_apply]
    ring
  have hsum : ((Fintype.card p).factorial : R) * (P * Q).det =
      ∑ σ : Equiv.Perm p, (P * Q).det := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, nsmul_eq_mul]
  rw [hsum, Finset.sum_congr rfl fun σ _ => h2 σ, Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [det_apply' (Q.submatrix r id), Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [submatrix_apply, id]
  ring

/-- **The Cauchy–Binet formula for a weighted Gram matrix**, the case `P = Xᵀ D`, `Q = Y` of
`Matrix.factorial_mul_det_mul`: for `X Y : Matrix m p R` and weights `d`,
`p! det (Xᵀ D Y) = ∑_{r : p → m} (∏ᵢ d_{r i}) det (X_r) det (Y_r)`, where `X_r` takes the rows
`r` of `X`. -/
theorem factorial_mul_det_transpose_mul_diagonal_mul (X Y : Matrix m p R) (d : m → R) :
    ((Fintype.card p).factorial : R) * (Xᵀ * diagonal d * Y).det =
      ∑ r : p → m, (∏ i, d (r i)) * (X.submatrix r id).det * (Y.submatrix r id).det := by
  rw [factorial_mul_det_mul]
  refine Finset.sum_congr rfl fun r _ => ?_
  have : (Xᵀ * diagonal d).submatrix id r = (X.submatrix r id)ᵀ * diagonal fun i => d (r i) := by
    ext i j
    simp [mul_diagonal]
  rw [this, det_mul, det_transpose, det_diagonal, mul_comm (X.submatrix r id).det]

end CauchyBinet

end Matrix
