/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix.Cholesky` beside `Mathlib.Analysis.Matrix.LDL`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.LDL
import Mathlib.Analysis.Matrix.PosDef
import Numlib.Data.Fin.Sum
import Numlib.Direct.Substitution
import Numlib.LinearAlgebra.Matrix.HermitianPart
import Numlib.LinearAlgebra.Matrix.LU
import Numlib.LinearAlgebra.Matrix.QR

/-!
# The Cholesky factorization and positive definite matrices

Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$, and let $A \in \mathbb{K}^{n \times n}$, with the
indices in a finite linear order. A **Cholesky factorization** of $A$ is $A = H^H H$ with $H$ upper
triangular with a positive diagonal. This file proves that a positive definite matrix has exactly
one Cholesky factorization (Theorem 3.6 of [quarteroni2000numerical], Theorem 10.1 of
[higham2002accuracy]), and that the recurrence (3.45) of [quarteroni2000numerical] computes it. It
also proves Sylvester's criterion and the other characterizations of positive definiteness in
Property 1.18 of [quarteroni2000numerical], the entry bounds $|a_{ij}|^2 \le a_{ii} a_{jj}$ of a
positive semidefinite matrix, and the relation to the $LDL^H$ factorization of Mathlib's module
`Mathlib.Analysis.Matrix.LDL`. The presentation follows §1.12, §3.4.2 and §3.4.3 of
[quarteroni2000numerical] and §10.1 of [higham2002accuracy].

The file also proves results of §4.2 of [golub2013matrix]: the LU factorization of an unsymmetric
matrix whose Hermitian part is positive definite, and a bound on the size of $|L| |U|$ for it; the
elimination step and the rank-revealing pivoted $LDL^H$ factorization of a positive semidefinite
matrix; and the block form, the bandwidth and the norm of the Cholesky factor.

## Main definitions

* `Matrix.IsCholesky`: $H$ is upper triangular with a positive diagonal and $H^H H = A$.
* `Matrix.cholesky`: the lower triangular factor $H^H$, computed by the recurrence (3.45) of
  [quarteroni2000numerical] as one total function on a finite linear order. `Matrix.choleskyAux` is
  its well-founded recursion.

## Main results

* `Matrix.exists_isCholesky`, `Matrix.IsCholesky.unique`, `Matrix.existsUnique_isCholesky`: a
  positive definite matrix has exactly one Cholesky factor (Theorem 3.6 of
  [quarteroni2000numerical]).
* `Matrix.IsCholesky.posDef`: conversely, $H^H H$ is positive definite for a nonsingular $H$.
* `Matrix.cholesky_eq_of_isCholesky`, `Matrix.isCholesky_cholesky`: the recurrence (3.45) computes
  the Cholesky factor.
* `Matrix.posDef_iff_forall_det_leadingPrincipalSubmatrix_pos`: **Sylvester's criterion**, Property
  1.18(3) of [quarteroni2000numerical].
* `Matrix.posDef_iff_exists_isUnit_conjTranspose_mul_self`: $A$ is positive definite if and only if
  $A = H^H H$ for a nonsingular $H$ (Property 1.18(4)).
* `Matrix.posDef_iff_forall_principalSubmatrix_eigenvalues_pos`: a Hermitian matrix is positive
  definite if and only if all its principal submatrices have positive eigenvalues (Property
  1.18(2)).
* `Matrix.PosSemidef.norm_apply_sq_le_mul_re_diag`,
  `Matrix.PosSemidef.norm_apply_le_add_re_diag_div_two`,
  `Matrix.PosSemidef.norm_apply_le_max_re_diag`, `Matrix.PosDef.norm_apply_le_max_re_diag`: for a
  positive semidefinite matrix, $|a_{ij}|^2 \le a_{ii} a_{jj}$ and
  $|a_{ij}| \le (a_{ii} + a_{jj})/2$, so an entry of largest modulus lies on the diagonal (§1.12 of
  [quarteroni2000numerical], (4.2.12)–(4.2.14) of [golub2013matrix]).
* `Matrix.LDL.lower_isUnitLowerTriangular`, `Matrix.LDL.diagEntries_pos`, `Matrix.isLDM_ldl`,
  `Matrix.LDL.lower_eq_of_isLDM`: the factors `LDL.lower` and `LDL.diag` of Mathlib are the unique
  $LDL^H$ factors of `Numlib.LinearAlgebra.Matrix.LU`.
* `Matrix.isCholesky_conjTranspose_mul_self_of_qr`, `Matrix.cholesky_conjTranspose_mul_self_of_qr`:
  the triangular factor of a reduced QR factorization $X = QR$ is the Cholesky factor of $X^H X$
  (Property 3.3 of [quarteroni2000numerical], last clause).
* `Matrix.IsThinQR.isCholesky`: the triangular factor of a thin QR factorization is the Cholesky
  factor of the Gram matrix (Theorem 5.2.3 of [golub2013matrix]).
* `Matrix.exists_isLU_of_posDef_hermitianPart`: a matrix with a positive definite Hermitian part has
  an LU factorization with pivots of positive real part (Corollary 4.2.4 of [golub2013matrix]).
* `Matrix.posDef_hermitianPart_schurComplementSingle`: one elimination step keeps a positive
  definite Hermitian part (Theorem 4.2.5 of [golub2013matrix]).
* `Matrix.IsLU.frobenius_norm_abs_mul_abs_le`: $\| |L| |U| \|_F \le n (\|T\|_2 + \|S T^{-1} S\|_2)$
  (Theorem 4.2.6 of [golub2013matrix]).
* `Matrix.PosSemidef.apply_eq_zero_of_diag_eq_zero`: a zero diagonal entry of a positive
  semidefinite matrix has a zero row and a zero column ((4.2.15) of [golub2013matrix]).
* `Matrix.PosSemidef.schurComplementSingle`,
  `Matrix.PosSemidef.re_schurComplementSingle_apply_self_le`: one elimination step keeps a matrix
  positive semidefinite and does not increase the diagonal ((4.2.16) of [golub2013matrix]).
* `Matrix.PosSemidef.exists_perm_ldl_rank`: the rank-revealing pivoted $LDL^H$ factorization
  ((4.2.17) of [golub2013matrix]).
* `Matrix.cholesky_finSumFin`: the block form of the Cholesky factor ((4.2.18) of
  [golub2013matrix]).
* `Matrix.cholesky_hasLowerBandwidth`: the Cholesky factor has the lower bandwidth of the matrix
  (§4.3.5 of [golub2013matrix]).
* `Matrix.sq_norm_cholesky_apply_le`, `Matrix.l2_opNorm_cholesky_sq`: the entries and the spectral
  norm of the Cholesky factor are bounded by those of $A$ (§4.2.6 of [golub2013matrix]).

## Proof outline

Existence goes through the $LDL^H$ factorization that `Matrix.existsUnique_isLDM` of
`Numlib.LinearAlgebra.Matrix.LU` gives (`Matrix.exists_isLDM_conjTranspose_of_posDef`): the Cholesky
factor is $H = D^{1/2} L^H$. Uniqueness is the uniqueness of the LU factorization
$A = (H^H D^{-1})(D H)$ with $D = \operatorname{diag}(h_{11}, \dots, h_{nn})$
(`Matrix.IsCholesky.isLU`). As for the Doolittle recurrence, the correctness of the recurrence
(3.45) needs no bordering induction: the recurrence restates the entrywise identities
`Matrix.IsCholesky.apply_eq_sum` that every Cholesky factor satisfies, so the computed entries agree
with the factor by strong induction along the order of $\min(i, j)$. Sylvester's criterion uses the
pivots of the $LDL^H$ factorization as ratios of consecutive leading principal minors
(`Matrix.IsLU.diag_upper_eq_div_leadingPrincipalMinor`).

Corollary 4.2.4 and Theorem 4.2.5 of [golub2013matrix] both use
`Matrix.exists_star_dotProduct_schurComplementSingle_mulVec`: the quadratic form of a one-step Schur
complement is a quadratic form of the matrix. Theorem 4.2.6 applies the bounds $\|Ax\|^2, \|A^T
x\|^2 \le (\|T\|_2 + \|S T^{-1} S\|_2) \, x^T A x$
(`Matrix.dotProduct_mulVec_self_le_of_posDef_hermitianPart` and
`Matrix.dotProduct_transpose_mulVec_self_le_of_posDef_hermitianPart`, through
$A T^{-1} A^T = A^T T^{-1} A = T - S T^{-1} S$) to a row of $L^{-1}$ and a column of $U^{-1}$.

## Notation

* $A(\le k)$: the leading principal submatrix of $A$ on the indices $i \le k$,
  `Matrix.leadingPrincipalSubmatrix A k`.
* $A(< k)$: the strict leading principal submatrix of $A$ on the indices $i < k$,
  `Matrix.strictLeadingPrincipalSubmatrix A k`.
* $\bar{L}$: the entrywise conjugate of $L$, written `Lᴴᵀ` in Lean.

## Implementation notes

* The index type is `[Fintype n] [LinearOrder n]` throughout. Only the section on Mathlib's $LDL^H$
  factorization adds the assumption `[LocallyFiniteOrderBot n]` that `LDL.lower` needs. Nothing else
  depends on it: the existence of the Cholesky factor is proved through the LU theory instead.
* The scalars are `[RCLike 𝕜]`, with `open scoped ComplexOrder`, so that `Matrix.PosDef` and the
  condition $0 < h_{ii}$ make sense over $\mathbb{C}$ as over $\mathbb{R}$. In this order, $0 < z$
  means that $z$ is real and positive.
* The $LDM^T$ factorization `Matrix.IsLDM` of `Numlib.LinearAlgebra.Matrix.LU` is used in the
  Hermitian form $M = \bar{L}$, whose transpose is $L^H$.
* A $2 \times 2$ principal minor is the determinant of the submatrix along `![i, j] : Fin 2 → n`
  (`Matrix.PosSemidef.submatrix`, `Matrix.det_fin_two`).
-/

open Finset
open scoped ComplexOrder

namespace Matrix

variable {n : Type*} [Fintype n] [LinearOrder n] {𝕜 : Type*} [RCLike 𝕜]

/-! ### Entry bounds of positive semidefinite and positive definite matrices -/

section Entries

variable {A : Matrix n n 𝕜}

omit [Fintype n] [LinearOrder n] in
/-- Let $A \in \mathbb{K}^{n \times n}$ be positive semidefinite. Then every $2 \times 2$ principal
minor of $A$ is nonnegative: for all indices $i$ and $j$,
$$|a_{ij}|^2 \le \operatorname{Re} a_{ii} \cdot \operatorname{Re} a_{jj}.$$
This is in §1.12 of [quarteroni2000numerical].

The diagonal entries of $A$ are real; the statement uses their real parts. -/
theorem PosSemidef.norm_apply_sq_le_mul_re_diag (hA : A.PosSemidef) (i j : n) :
    ‖A i j‖ ^ 2 ≤ RCLike.re (A i i) * RCLike.re (A j j) := by
  classical
  have h := (hA.submatrix ![i, j]).det_nonneg
  rw [det_fin_two] at h
  simp only [submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  rw [← hA.1.apply j i, RCLike.star_def, RCLike.mul_conj, ← hA.1.coe_re_apply_self i,
    ← hA.1.coe_re_apply_self j, ← RCLike.ofReal_pow, ← RCLike.ofReal_mul, ← RCLike.ofReal_sub,
    RCLike.ofReal_nonneg, sub_nonneg] at h
  exact h

omit [Fintype n] [LinearOrder n] in
/-- Let $A \in \mathbb{K}^{n \times n}$ be positive semidefinite. Then every entry of $A$ is bounded
in modulus by the mean of the two diagonal entries in its row and its column:
$$|a_{ij}| \le \frac{\operatorname{Re} a_{ii} + \operatorname{Re} a_{jj}}{2}.$$
This is (4.2.12) of [golub2013matrix].

The proof is $|a_{ij}|^2 \le a_{ii} a_{jj} \le \bigl((a_{ii} + a_{jj})/2\bigr)^2$. -/
theorem PosSemidef.norm_apply_le_add_re_diag_div_two (hA : A.PosSemidef) (i j : n) :
    ‖A i j‖ ≤ (RCLike.re (A i i) + RCLike.re (A j j)) / 2 := by
  have hi : 0 ≤ RCLike.re (A i i) := (RCLike.nonneg_iff.1 hA.diag_nonneg).1
  have hj : 0 ≤ RCLike.re (A j j) := (RCLike.nonneg_iff.1 hA.diag_nonneg).1
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
  refine (hA.norm_apply_sq_le_mul_re_diag i j).trans ?_
  nlinarith [sq_nonneg (RCLike.re (A i i) - RCLike.re (A j j))]

omit [Fintype n] [LinearOrder n] in
/-- Let $A \in \mathbb{K}^{n \times n}$ be positive semidefinite. Then every entry of $A$ is bounded
in modulus by the larger of the two diagonal entries in its row and its column:
$$|a_{ij}| \le \max\{\operatorname{Re} a_{ii}, \operatorname{Re} a_{jj}\}.$$
So an entry of largest modulus lies on the diagonal. This is (4.2.14) of [golub2013matrix]. -/
theorem PosSemidef.norm_apply_le_max_re_diag (hA : A.PosSemidef) (i j : n) :
    ‖A i j‖ ≤ max (RCLike.re (A i i)) (RCLike.re (A j j)) :=
  (hA.norm_apply_le_add_re_diag_div_two i j).trans (by
    linarith [le_max_left (RCLike.re (A i i)) (RCLike.re (A j j)),
      le_max_right (RCLike.re (A i i)) (RCLike.re (A j j))])

omit [Fintype n] [LinearOrder n] in
/-- Let $A \in \mathbb{K}^{n \times n}$ be positive definite. Then every entry of $A$ is bounded in
modulus by the larger of the two diagonal entries in its row and its column:
$$|a_{ij}| \le \max\{\operatorname{Re} a_{ii}, \operatorname{Re} a_{jj}\}.$$
So an entry of largest modulus lies on the diagonal. This is in §1.12 of
[quarteroni2000numerical], after Property 1.18.

This is the definite case of `Matrix.PosSemidef.norm_apply_le_max_re_diag`. -/
theorem PosDef.norm_apply_le_max_re_diag (hA : A.PosDef) (i j : n) :
    ‖A i j‖ ≤ max (RCLike.re (A i i)) (RCLike.re (A j j)) :=
  hA.posSemidef.norm_apply_le_max_re_diag i j

end Entries

/-! ### Leading principal submatrices of a positive definite matrix -/

section Leading

variable {A : Matrix n n 𝕜} (hA : A.PosDef)
include hA

omit [Fintype n] in
/-- Let $A \in \mathbb{K}^{n \times n}$ be positive definite. Then for every index $k$, the leading
principal submatrix $A(\le k)$ is positive definite. -/
theorem PosDef.leadingPrincipalSubmatrix (k : n) : (A.leadingPrincipalSubmatrix k).PosDef :=
  hA.submatrix Subtype.val_injective

omit [Fintype n] in
/-- Let $A \in \mathbb{K}^{n \times n}$ be positive definite. Then for every index $k$, the strict
leading principal submatrix $A(< k)$ is positive definite.

For the least index $k$, the matrix $A(< k)$ is empty, and it is positive definite trivially. -/
theorem PosDef.strictLeadingPrincipalSubmatrix (k : n) :
    (A.strictLeadingPrincipalSubmatrix k).PosDef :=
  hA.submatrix Subtype.val_injective

/-- Let $A \in \mathbb{K}^{n \times n}$ be positive definite. Then for every index $k$, the leading
principal minor $\det A(\le k)$ is positive.

In the order on $\mathbb{C}$, this means that $\det A(\le k)$ is real and positive. -/
theorem PosDef.det_leadingPrincipalSubmatrix_pos (k : n) :
    0 < (A.leadingPrincipalSubmatrix k).det :=
  (hA.leadingPrincipalSubmatrix k).det_pos

/-- Let $A \in \mathbb{K}^{n \times n}$ be positive definite. Then for every index $k$, the leading
principal submatrix $A(\le k)$ is nonsingular. -/
theorem PosDef.isUnit_leadingPrincipalSubmatrix (k : n) :
    IsUnit (A.leadingPrincipalSubmatrix k) :=
  (hA.leadingPrincipalSubmatrix k).isUnit

/-- Let $A \in \mathbb{K}^{n \times n}$ be positive definite. Then for every index $k$, the strict
leading principal submatrix $A(< k)$ is nonsingular. -/
theorem PosDef.isUnit_strictLeadingPrincipalSubmatrix (k : n) :
    IsUnit (A.strictLeadingPrincipalSubmatrix k) :=
  (hA.strictLeadingPrincipalSubmatrix k).isUnit

/-- A positive definite matrix $A \in \mathbb{K}^{n \times n}$ satisfies the hypothesis of the
existence theorem for the LU factorization: every strict leading principal submatrix $A(< k)$ is
nonsingular (`Matrix.HasUnitStrictLeadingPrincipalSubmatrices`). -/
theorem PosDef.hasUnitStrictLeadingPrincipalSubmatrices :
    A.HasUnitStrictLeadingPrincipalSubmatrices :=
  hA.isUnit_strictLeadingPrincipalSubmatrix

end Leading

/-! ### The Hermitian $LDL^H$ factorization -/

section LDLstar

omit [Fintype n] in
/-- Let $L \in \mathbb{K}^{n \times n}$ be lower triangular. Then its conjugate transpose $L^H$ is
upper triangular. -/
theorem IsLowerTriangular.conjTranspose_isUpperTriangular {L : Matrix n n 𝕜}
    (hL : L.IsLowerTriangular) : Lᴴ.IsUpperTriangular := fun i j hij => by
  rw [conjTranspose_apply, hL (i := j) (j := i) (OrderDual.toDual_lt_toDual.2 hij), star_zero]

omit [Fintype n] in
/-- Let $U \in \mathbb{K}^{n \times n}$ be upper triangular. Then its conjugate transpose $U^H$ is
lower triangular. -/
theorem IsUpperTriangular.conjTranspose_isLowerTriangular {U : Matrix n n 𝕜}
    (hU : U.IsUpperTriangular) : Uᴴ.IsLowerTriangular := fun i j hij => by
  rw [conjTranspose_apply, hU (i := j) (j := i) (OrderDual.toDual_lt_toDual.1 hij), star_zero]

omit [Fintype n] in
/-- Let $L \in \mathbb{K}^{n \times n}$ be unit lower triangular. Then its entrywise conjugate
$\bar{L}$ is unit lower triangular.

In Lean, $\bar{L}$ is `Lᴴᵀ`, the transpose of the conjugate transpose. -/
theorem IsUnitLowerTriangular.conjTranspose_transpose {L : Matrix n n 𝕜}
    (hL : L.IsUnitLowerTriangular) : Lᴴᵀ.IsUnitLowerTriangular where
  isLowerTriangular i j hij := by
    rw [transpose_apply, conjTranspose_apply, hL.isLowerTriangular (i := i) (j := j) hij, star_zero]
  diag_eq_one i := by rw [transpose_apply, conjTranspose_apply, hL.diag_eq_one, star_one]

variable {A L D M : Matrix n n 𝕜}

/-- Let $A = L D M^T$ be an $LDM^T$ factorization of $A \in \mathbb{K}^{n \times n}$: $L$ and $M$
are unit lower triangular and $D$ is diagonal. Then its conjugate transpose is the $LDM^T$
factorization
$$A^H = \bar{M} \, D^H \, \bar{L}^T,$$
with the unit lower triangular factors $\bar{M}$ and $\bar{L}$ and the diagonal factor $D^H$. -/
theorem IsLDM.conjTranspose (h : IsLDM A L D M) : IsLDM Aᴴ Mᴴᵀ Dᴴ Lᴴᵀ where
  isUnitLowerTriangular_left := h.isUnitLowerTriangular_right.conjTranspose_transpose
  isDiag := h.isDiag.conjTranspose
  isUnitLowerTriangular_right := h.isUnitLowerTriangular_left.conjTranspose_transpose
  mul_eq := by
    rw [← h.mul_eq, conjTranspose_mul, conjTranspose_mul, transpose_transpose,
      conjTranspose_transpose, transpose_conjTranspose, Matrix.mul_assoc]

/-- Let $A \in \mathbb{K}^{n \times n}$ be Hermitian, with every strict leading principal submatrix
$A(< k)$ nonsingular, and let $A = L D M^T$ be an $LDM^T$ factorization. Then the factorization
is Hermitian:
$$M = \bar{L} \quad \text{and} \quad D = D^H.$$
So $M^T = L^H$, and $D$ is real.

The conjugate transpose of the factorization is a second $LDM^T$ factorization of $A$
(`Matrix.IsLDM.conjTranspose`), and the uniqueness theorem `Matrix.existsUnique_isLDM`
identifies the two. -/
theorem IsLDM.eq_of_isHermitian (h : IsLDM A L D M) (hA : A.IsHermitian)
    (hlead : A.HasUnitStrictLeadingPrincipalSubmatrices) : M = Lᴴᵀ ∧ D = Dᴴ := by
  have h' := h.conjTranspose
  rw [hA.eq] at h'
  obtain ⟨LDM₀, -, huniq⟩ := existsUnique_isLDM hlead
  have := (huniq (Mᴴᵀ, Dᴴ, Lᴴᵀ) h').trans (huniq (L, D, M) h).symm
  simp only [Prod.mk.injEq] at this
  obtain ⟨hL, hD, -⟩ := this
  refine ⟨?_, hD.symm⟩
  rw [← hL]
  ext i j
  simp only [transpose_apply, conjTranspose_apply, star_star]

/-- Let $A \in \mathbb{K}^{n \times n}$ be Hermitian, with every strict leading principal submatrix
$A(< k)$ nonsingular. Then $A$ has a Hermitian $LDL^H$ factorization: there are a unit lower
triangular $L$ and a diagonal $D$ with
$$A = L D L^H.$$
This is Theorem 4.1.3 of [golub2013matrix].

The factorization is unique by `Matrix.existsUnique_isLDM`, and it is obtained from that
theorem. In Lean, the factorization is `Matrix.IsLDM A L D Lᴴᵀ`. -/
theorem exists_isLDM_conjTranspose_of_isHermitian (hA : A.IsHermitian)
    (hlead : A.HasUnitStrictLeadingPrincipalSubmatrices) : ∃ L D, IsLDM A L D Lᴴᵀ := by
  obtain ⟨⟨L, D, M⟩, h, -⟩ := existsUnique_isLDM hlead
  obtain ⟨hM, -⟩ := h.eq_of_isHermitian hA hlead
  exact ⟨L, D, hM ▸ h⟩

/-- Let $A = L D L^H$ with $L \in \mathbb{K}^{n \times n}$ unit lower triangular and $D$ diagonal.
Then $A$ is positive definite if and only if every diagonal entry $d_{ii}$ of $D$ is positive.

The matrix $A$ is congruent to $D$. -/
theorem IsLDM.posDef_iff (h : IsLDM A L D Lᴴᵀ) : A.PosDef ↔ ∀ i, 0 < D i i := by
  have hU : IsUnit Lᴴ := (isUnit_conjTranspose _).2 h.isUnitLowerTriangular_left.isUnit
  have hL : L * D * Lᴴ = star Lᴴ * D * Lᴴ := by
    rw [star_eq_conjTranspose, conjTranspose_conjTranspose]
  rw [← h.mul_eq, transpose_transpose, hL, Matrix.IsUnit.posDef_star_left_conjugate_iff hU]
  conv_lhs => rw [← h.isDiag.diagonal_diag]
  rw [posDef_diagonal_iff]
  rfl

/-- Let $A = L D M^T$ be an $LDM^T$ factorization of $A \in \mathbb{K}^{n \times n}$, and assume
that every leading principal minor $\det A(\le k)$ is positive. Then every pivot $d_{kk}$ is
positive.

The pivots are the ratios $d_{kk} = \det A(\le k) / \det A(< k)$ of consecutive leading
principal minors, and the proof is a strong induction along the order: $\det A(< k)$ is the
product of the earlier pivots. In the order on $\mathbb{C}$, positive means real and positive. -/
theorem IsLDM.diag_pos_of_forall_det_pos (h : IsLDM A L D M)
    (hpos : ∀ k, 0 < (A.leadingPrincipalSubmatrix k).det) (k : n) : 0 < D k k := by
  have hLU := h.isLU
  have hdiag : ∀ k, (D * Mᵀ) k k = D k k := fun k => by
    rw [h.isDiag.isUpperTriangular.mul_apply_self
      h.isUnitLowerTriangular_right.isLowerTriangular.transpose_isUpperTriangular, transpose_apply,
      h.isUnitLowerTriangular_right.diag_eq_one, mul_one]
  suffices ∀ k, 0 < (D * Mᵀ) k k by rw [← hdiag]; exact this k
  intro k
  induction k using WellFoundedLT.induction with
  | ind k ih =>
  have hlt : 0 < (A.strictLeadingPrincipalSubmatrix k).det := by
    rw [hLU.det_strictLeadingPrincipalSubmatrix]
    exact Finset.prod_pos fun i hi => ih i (mem_filter.1 hi).2
  rw [hLU.diag_upper_eq_div_leadingPrincipalMinor hlt.ne']
  exact div_pos (hpos k) hlt

/-- Let $A \in \mathbb{K}^{n \times n}$ be positive definite. Then $A$ has an $LDL^H$ factorization
$A = L D L^H$, with $L$ unit lower triangular and $D$ diagonal with positive pivots
$d_{ii} > 0$. This is in §3.4.2 of [quarteroni2000numerical]. -/
theorem exists_isLDM_conjTranspose_of_posDef (hA : A.PosDef) :
    ∃ L D, IsLDM A L D Lᴴᵀ ∧ ∀ i, 0 < D i i := by
  obtain ⟨L, D, h⟩ :=
    exists_isLDM_conjTranspose_of_isHermitian hA.1 hA.isUnit_strictLeadingPrincipalSubmatrix
  exact ⟨L, D, h, h.posDef_iff.1 hA⟩

end LDLstar

/-! ### Sylvester's criterion -/

section Sylvester

variable {A : Matrix n n 𝕜}

/-- **Sylvester's criterion**. Let $A \in \mathbb{K}^{n \times n}$ be Hermitian. Then $A$ is
positive definite if and only if all its leading principal minors are positive:
$$A \text{ is positive definite} \iff \det A(\le k) > 0 \text{ for every index } k.$$
This is Property 1.18(3) of [quarteroni2000numerical].

For the forward direction, every leading principal submatrix of a positive definite matrix is
positive definite, so its determinant is positive. For the backward direction, the strict
leading principal submatrices are nonsingular, so $A = L D L^H$
(`Matrix.exists_isLDM_conjTranspose_of_isHermitian`). The pivots
$d_{kk} = \det A(\le k) / \det A(< k)$ are positive (`Matrix.IsLDM.diag_pos_of_forall_det_pos`),
and $A$ is congruent to $D$. -/
theorem posDef_iff_forall_det_leadingPrincipalSubmatrix_pos (hA : A.IsHermitian) :
    A.PosDef ↔ ∀ k, 0 < (A.leadingPrincipalSubmatrix k).det := by
  refine ⟨fun h k => h.det_leadingPrincipalSubmatrix_pos k, fun hpos => ?_⟩
  have hlead : ∀ k, IsUnit (A.leadingPrincipalSubmatrix k) := fun k =>
    (isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (hpos k).ne')
  obtain ⟨L, D, h⟩ := exists_isLDM_conjTranspose_of_isHermitian hA
    (isUnit_strictLeadingPrincipalSubmatrix_of_forall_isUnit hlead)
  exact h.posDef_iff.2 (h.diag_pos_of_forall_det_pos hpos)

omit [Fintype n] in
/-- Let $A \in \mathbb{K}^{n \times n}$ be Hermitian, with $n$ finite. Then $A$ is positive definite
if and only if, for every set $s$ of indices, all eigenvalues of the principal submatrix
$A(s, s)$ are positive. This is Property 1.18(2) of [quarteroni2000numerical].

For the forward direction, every principal submatrix is positive definite. For the backward
direction, the principal submatrix on the set of all indices is a reindexing of $A$. The
eigenvalues are `Matrix.IsHermitian.eigenvalues` of the Hermitian submatrix along
`Subtype.val : s → n`. -/
theorem posDef_iff_forall_principalSubmatrix_eigenvalues_pos [Finite n] (hA : A.IsHermitian) :
    A.PosDef ↔
      ∀ (s : Finset n) (i : s), 0 < (hA.submatrix (Subtype.val : s → n)).eigenvalues i := by
  cases nonempty_fintype n
  constructor
  · intro h s i
    exact (h.submatrix Subtype.val_injective).eigenvalues_pos i
  · intro h
    have hsub : (A.submatrix (Subtype.val : {x // x ∈ (univ : Finset n)} → n)
        Subtype.val).PosDef :=
      (hA.submatrix _).posDef_iff_eigenvalues_pos.2 (h univ)
    have := hsub.submatrix (e := fun i : n => (⟨i, mem_univ i⟩ : {x // x ∈ (univ : Finset n)}))
      fun i j hij => Subtype.mk.inj hij
    rwa [submatrix_submatrix, show (Subtype.val ∘ fun i : n =>
      (⟨i, mem_univ i⟩ : {x // x ∈ (univ : Finset n)})) = id from rfl, submatrix_id_id] at this

end Sylvester

/-! ### The Cholesky specification -/

/-- A **Cholesky factorization** of $A \in \mathbb{K}^{n \times n}$. The proposition
`Matrix.IsCholesky A H` holds if $H \in \mathbb{K}^{n \times n}$ is upper triangular, every
diagonal entry $h_{ii}$ is real and positive, and
$$A = H^H H.$$
This is the Cholesky factorization of Theorem 3.6 of [quarteroni2000numerical], equation (3.44).
[higham2002accuracy] writes it $A = R^H R$.

A theorem about "the Cholesky factor" is a theorem about any $H$ that satisfies this
specification; `Matrix.IsCholesky.unique` shows that there is at most one. -/
structure IsCholesky (A H : Matrix n n 𝕜) : Prop where
  /-- The factor $H$ is upper triangular. -/
  isUpperTriangular : H.IsUpperTriangular
  /-- Every diagonal entry $h_{ii}$ of the factor is positive, so in particular real. -/
  diag_pos : ∀ i, 0 < H i i
  /-- The factor satisfies $H^H H = A$. -/
  conjTranspose_mul_self : Hᴴ * H = A

namespace IsCholesky

variable {A H : Matrix n n 𝕜} (h : IsCholesky A H)
include h

/-- Let $H$ be a Cholesky factor of $A$. Then every diagonal entry $h_{ii}$ is nonzero. -/
theorem diag_ne_zero (i : n) : H i i ≠ 0 := (h.diag_pos i).ne'

/-- Let $H$ be a Cholesky factor of $A$. Then every diagonal entry $h_{ii}$ is real:
$\overline{h_{ii}} = h_{ii}$. -/
theorem star_diag (i : n) : star (H i i) = H i i :=
  RCLike.conj_eq_iff_im.2 (RCLike.pos_iff.1 (h.diag_pos i)).2

/-- Let $H$ be a Cholesky factor of $A$. Then every diagonal entry $h_{ii}$ equals its real part
$\operatorname{Re} h_{ii}$, cast to $\mathbb{K}$. -/
theorem coe_re_diag (i : n) : (RCLike.re (H i i) : 𝕜) = H i i :=
  RCLike.conj_eq_iff_re.1 (h.star_diag i)

/-- Let $H$ be a Cholesky factor of $A$. Then $H$ is nonsingular. -/
theorem isUnit : IsUnit H :=
  h.isUpperTriangular.isUnit_iff.2 h.diag_ne_zero

/-- The converse of Theorem 3.6 of [quarteroni2000numerical], and one direction of its Property
1.18(4). Let $H$ be a Cholesky factor of $A$. Then $A$ is positive definite.

The matrix $H^H H$ is positive definite because $H$ is nonsingular. -/
theorem posDef : A.PosDef :=
  h.conjTranspose_mul_self ▸
    PosDef.conjTranspose_mul_self H (mulVec_injective_iff_isUnit.2 h.isUnit)

/-- Let $H$ be a Cholesky factor of $A$. Then $A$ is Hermitian. -/
theorem isHermitian : A.IsHermitian := h.posDef.isHermitian

/-- Let $H$ be a Cholesky factor of $A$. Then for all indices $i$ and $j$,
$$a_{ij} = \sum_{k \le \min(i, j)} \overline{h_{ki}} \, h_{kj},$$
because $H$ vanishes below the diagonal. -/
theorem apply_eq_sum (i j : n) :
    A i j = ∑ k ∈ univ.filter (· ≤ min i j), star (H k i) * H k j := by
  rw [← h.conjTranspose_mul_self, Matrix.mul_apply]
  simp only [conjTranspose_apply]
  refine (Finset.sum_filter_of_ne fun k _ hk => ?_).symm
  rw [le_min_iff]
  by_contra hcon
  rw [not_and_or, not_le, not_le] at hcon
  rcases hcon with hik | hjk
  · exact hk (by rw [h.isUpperTriangular hik, star_zero, zero_mul])
  · exact hk (by rw [h.isUpperTriangular hjk, mul_zero])

/-- The off-diagonal identity of the Cholesky recurrence, the first line of (3.45) of
[quarteroni2000numerical]. Let $H$ be a Cholesky factor of $A$, and let $j < i$. Then
$$\overline{h_{ji}} \, h_{jj} = a_{ij} - \sum_{k < j} \overline{h_{ki}} \, h_{kj}.$$
-/
theorem star_apply_mul_diag_eq {i j : n} (hij : j < i) :
    star (H j i) * H j j = A i j - ∑ k ∈ univ.filter (· < j), star (H k i) * H k j := by
  rw [h.apply_eq_sum, min_eq_right hij.le, sum_filter_le_eq_add, add_sub_cancel_left]

/-- The diagonal identity of the Cholesky recurrence, the second line of (3.45) of
[quarteroni2000numerical]. Let $H$ be a Cholesky factor of $A$. Then for every index $i$,
$$\operatorname{Re} h_{ii} = \sqrt{\operatorname{Re} a_{ii} - \sum_{k < i} |h_{ki}|^2}.$$

This follows from $h_{ii}^2 = a_{ii} - \sum_{k < i} |h_{ki}|^2$ and $h_{ii} > 0$. -/
theorem re_diag_eq_sqrt (i : n) :
    RCLike.re (H i i) =
      Real.sqrt (RCLike.re (A i i) - ∑ k ∈ univ.filter (· < i), ‖H k i‖ ^ 2) := by
  have hsum : A i i = ((∑ k ∈ univ.filter (· < i), ‖H k i‖ ^ 2 : ℝ) : 𝕜) +
      ((‖H i i‖ ^ 2 : ℝ) : 𝕜) := by
    rw [h.apply_eq_sum, min_self, sum_filter_le_eq_add, RCLike.ofReal_sum]
    congr 1
    · exact Finset.sum_congr rfl fun k _ => by
        rw [RCLike.star_def, RCLike.conj_mul, RCLike.ofReal_pow]
    · rw [RCLike.star_def, RCLike.conj_mul, RCLike.ofReal_pow]
  have hre : RCLike.re (A i i) - ∑ k ∈ univ.filter (· < i), ‖H k i‖ ^ 2 = ‖H i i‖ ^ 2 := by
    rw [hsum, map_add, RCLike.ofReal_re, RCLike.ofReal_re, add_sub_cancel_left]
  rw [hre, Real.sqrt_sq (norm_nonneg _)]
  conv_rhs => rw [← h.coe_re_diag i]
  rw [RCLike.norm_ofReal, abs_of_pos (RCLike.pos_iff.1 (h.diag_pos i)).1]

/-- Let $H$ be a Cholesky factor of $A$, and let $D = \operatorname{diag}(h_{11}, \dots, h_{nn})$.
Then $A = (H^H D^{-1})(D H)$ is an LU factorization of $A$: the factor $H^H D^{-1}$ is unit
lower triangular and $D H$ is upper triangular. -/
theorem isLU : IsLU A (Hᴴ * diagonal fun i => (H i i)⁻¹) (diagonal (fun i => H i i) * H) where
  isUnitLowerTriangular := by
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · rw [mul_diagonal, conjTranspose_apply,
        h.isUpperTriangular (OrderDual.toDual_lt_toDual.1 hij), star_zero, zero_mul]
    · rw [mul_diagonal, conjTranspose_apply, h.star_diag, mul_inv_cancel₀ (h.diag_ne_zero i)]
  isUpperTriangular := (blockTriangular_diagonal _).mul h.isUpperTriangular
  mul_eq := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal _), diagonal_mul_diagonal]
    simp only [inv_mul_cancel₀ (h.diag_ne_zero _), diagonal_one, Matrix.one_mul,
      h.conjTranspose_mul_self]

/-- **Uniqueness of the Cholesky factorization**. Let $H$ and $H_2$ be Cholesky factors of the same
matrix $A$. Then $H = H_2$. This is the uniqueness part of Theorem 3.6 of
[quarteroni2000numerical] and of Theorem 10.1 of [higham2002accuracy].

Both factors give LU factorizations $A = (H^H D^{-1})(D H)$ of the positive definite matrix $A$,
with $D = \operatorname{diag}(h_{11}, \dots, h_{nn})$ (`Matrix.IsCholesky.isLU`), and the LU
factorization is unique (`Matrix.IsLU.unique`). The diagonal of $D H$ is $h_{ii}^2$, which
determines the positive $h_{ii}$, and then $H = D^{-1}(D H)$. -/
theorem unique {H₂ : Matrix n n 𝕜} (h₂ : IsCholesky A H₂) : H = H₂ := by
  obtain ⟨-, hU⟩ := h.isLU.unique h₂.isLU h.posDef.isUnit_strictLeadingPrincipalSubmatrix
  have hdiag : ∀ i, H i i = H₂ i i := fun i => by
    have := congrFun (congrFun hU i) i
    rw [diagonal_mul, diagonal_mul, ← sq, ← sq] at this
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 this with h' | h'
    · exact h'
    · have h1 := h.diag_pos i
      rw [h'] at h1
      have h2 := add_pos h1 (h₂.diag_pos i)
      rw [neg_add_cancel] at h2
      exact absurd h2 (lt_irrefl _)
  ext i j
  have := congrFun (congrFun hU i) j
  rw [diagonal_mul, diagonal_mul, hdiag i] at this
  exact mul_left_cancel₀ (h₂.diag_ne_zero i) this

end IsCholesky

/-! ### Existence of the Cholesky factorization -/

section Existence

variable {A : Matrix n n 𝕜}

/-- **Existence of the Cholesky factorization**. Let $A \in \mathbb{K}^{n \times n}$ be positive
definite. Then $A$ has a Cholesky factor: there is an upper triangular $H$ with a positive
diagonal and $A = H^H H$. This is the existence part of Theorem 3.6 of [quarteroni2000numerical]
and of Theorem 10.1 of [higham2002accuracy].

If $A = L D L^H$ with positive pivots $d_i$, then $H = D^{1/2} L^H$ is the factor, with the
diagonal entries $\sqrt{d_i}$. -/
theorem exists_isCholesky (hA : A.PosDef) : ∃ H, IsCholesky A H := by
  obtain ⟨L, D, h, hD⟩ := exists_isLDM_conjTranspose_of_posDef hA
  set s : n → 𝕜 := fun i => ((Real.sqrt (RCLike.re (D i i)) : ℝ) : 𝕜) with hs
  have hre : ∀ i, 0 < RCLike.re (D i i) := fun i => (RCLike.pos_iff.1 (hD i)).1
  have hss : ∀ i, s i * s i = D i i := fun i => by
    rw [hs, ← RCLike.ofReal_mul, Real.mul_self_sqrt (hre i).le]
    exact RCLike.conj_eq_iff_re.1 (RCLike.conj_eq_iff_im.2 (RCLike.pos_iff.1 (hD i)).2)
  have hstar : star s = s := funext fun i => by simp [hs]
  refine ⟨diagonal s * Lᴴ, (blockTriangular_diagonal _).mul
    h.isUnitLowerTriangular_left.isLowerTriangular.conjTranspose_isUpperTriangular, fun i => ?_, ?_⟩
  · rw [diagonal_mul, conjTranspose_apply, h.isUnitLowerTriangular_left.diag_eq_one, star_one,
      mul_one, hs]
    exact RCLike.ofReal_pos.2 (Real.sqrt_pos.2 (hre i))
  · rw [conjTranspose_mul, conjTranspose_conjTranspose, diagonal_conjTranspose, hstar,
      Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal s), diagonal_mul_diagonal, ← h.mul_eq,
      transpose_transpose, Matrix.mul_assoc]
    congr 2
    conv_rhs => rw [← h.isDiag.diagonal_diag]
    exact congrArg _ (funext hss)

/-- **Theorem 3.6** of [quarteroni2000numerical], and Theorem 10.1 of [higham2002accuracy]. Let
$A \in \mathbb{K}^{n \times n}$ be positive definite. Then $A$ has exactly one Cholesky
factorization: there is exactly one upper triangular $H$ with a positive diagonal such that
$A = H^H H$. -/
theorem existsUnique_isCholesky (hA : A.PosDef) : ∃! H, IsCholesky A H := by
  obtain ⟨H, h⟩ := exists_isCholesky hA
  exact ⟨H, h, fun H' h' => h'.unique h⟩

/-- Property 1.18(4) of [quarteroni2000numerical]. A matrix $A \in \mathbb{K}^{n \times n}$ is
positive definite if and only if $A = H^H H$ for a nonsingular $H \in \mathbb{K}^{n \times n}$.

Neither direction assumes that $A$ is Hermitian. -/
theorem posDef_iff_exists_isUnit_conjTranspose_mul_self :
    A.PosDef ↔ ∃ H : Matrix n n 𝕜, IsUnit H ∧ Hᴴ * H = A := by
  constructor
  · intro hA
    obtain ⟨H, h⟩ := exists_isCholesky hA
    exact ⟨H, h.isUnit, h.conjTranspose_mul_self⟩
  · rintro ⟨H, hH, rfl⟩
    exact PosDef.conjTranspose_mul_self H (mulVec_injective_iff_isUnit.2 hH)

end Existence

/-! ### The Cholesky recurrence -/

/-- The Cholesky recurrence (3.45) of [quarteroni2000numerical], as one total function on a finite
linear order. It computes the entries $c_{ij}$ of the lower triangular factor, which is $H^H$
for the Cholesky factor $H$:
$$c_{ij} = \begin{cases} \bigl(a_{ij} - \sum_{k < j} c_{ik} \overline{c_{jk}}\bigr) / c_{jj} &
  \text{if } j < i, \\ \sqrt{\operatorname{Re} a_{ii} - \sum_{k < i} |c_{ik}|^2} & \text{if }
  i = j, \\ 0 & \text{if } i < j. \end{cases}$$

The entries are indexed as the entries $h_{ij}$ of the lower triangular factor in the source.
The recursion is well founded on the number of indices below $\min(i, j)$, with the off-diagonal
entries after the diagonal entry at the same level, as in `Matrix.luPacked`. When $A$ is not
positive definite, the result has no meaning: the square root of a negative number is $0$, and
division by $0$ gives $0$. `Matrix.isCholesky_cholesky` says when the result is the Cholesky
factor. -/
noncomputable def choleskyAux (A : Matrix n n 𝕜) : n → n → 𝕜
  | i, j =>
    if j < i then
      (A i j - ∑ k ∈ (univ.filter (· < j)).attach, choleskyAux A i k * star (choleskyAux A j k)) /
        choleskyAux A j j
    else if i = j then
      ((Real.sqrt (RCLike.re (A i i) -
        ∑ k ∈ (univ.filter (· < i)).attach, ‖choleskyAux A i k‖ ^ 2) : ℝ) : 𝕜)
    else 0
termination_by i j => (#{k | k < min i j}, if j < i then 1 else 0)
decreasing_by
  all_goals first
    | -- the calls `choleskyAux A j k` and `choleskyAux A i k` below the diagonal, `k < j < i`
      (have hr : (k : n) < j := (mem_filter.1 k.2).2
       have hji : j < i := ‹j < i›
       first
         | rw [min_eq_right hr.le, min_eq_right hji.le]
         | rw [min_eq_right (hr.trans hji).le, min_eq_right hji.le]
       exact Prod.Lex.left _ _ (card_filter_lt_lt_of_lt hr))
    | -- the call `choleskyAux A j j`, at the same level
      (have hji : j < i := ‹j < i›
       rw [min_self, min_eq_right hji.le]
       refine Prod.Lex.right _ ?_
       simp [hji])
    | -- the diagonal branch, `k < i = j`
      (have hr : (k : n) < i := (mem_filter.1 k.2).2
       have hij : i = j := ‹i = j›
       subst hij
       rw [min_eq_right hr.le, min_self]
       exact Prod.Lex.left _ _ (card_filter_lt_lt_of_lt hr))

/-- The lower triangular Cholesky factor $H^H$ computed by the recurrence (3.45) of
[quarteroni2000numerical], as a matrix: its entries are `Matrix.choleskyAux A i j`. -/
noncomputable def cholesky (A : Matrix n n 𝕜) : Matrix n n 𝕜 :=
  of fun i j => choleskyAux A i j

section Recurrence

variable (A : Matrix n n 𝕜)

/-- The Cholesky recurrence below the diagonal, the first line of (3.45) of
[quarteroni2000numerical]. Let $C$ be the matrix `Matrix.cholesky A`, with the entries $c_{ij}$.
For $j < i$,
$$c_{ij} = \Bigl(a_{ij} - \sum_{k < j} c_{ik} \overline{c_{jk}}\Bigr) / c_{jj}.$$
-/
theorem cholesky_apply_of_lt {i j : n} (hij : j < i) :
    cholesky A i j =
      (A i j - ∑ k ∈ univ.filter (· < j), cholesky A i k * star (cholesky A j k)) /
        cholesky A j j := by
  simp only [cholesky, of_apply]
  rw [choleskyAux, ite_eq_left hij,
    Finset.sum_attach (univ.filter (· < j)) fun k => choleskyAux A i k * star (choleskyAux A j k)]

/-- The Cholesky recurrence on the diagonal, the second line of (3.45) of [quarteroni2000numerical].
Let $C$ be the matrix `Matrix.cholesky A`, with the entries $c_{ij}$. For every index $i$,
$$c_{ii} = \sqrt{\operatorname{Re} a_{ii} - \sum_{k < i} |c_{ik}|^2},$$
where the square root of a negative number is $0$. -/
theorem cholesky_apply_self (i : n) :
    cholesky A i i =
      ((Real.sqrt (RCLike.re (A i i) - ∑ k ∈ univ.filter (· < i), ‖cholesky A i k‖ ^ 2) : ℝ) :
        𝕜) := by
  simp only [cholesky, of_apply]
  rw [choleskyAux, ite_eq_right (lt_irrefl i), ite_eq_left rfl,
    Finset.sum_attach (univ.filter (· < i)) fun k => ‖choleskyAux A i k‖ ^ 2]

/-- The matrix `Matrix.cholesky A` vanishes above the diagonal: its entry $c_{ij}$ is $0$ for
$i < j$. -/
theorem cholesky_apply_of_gt {i j : n} (hij : i < j) : cholesky A i j = 0 := by
  simp only [cholesky, of_apply]
  rw [choleskyAux, ite_eq_right (not_lt.2 hij.le), ite_eq_right hij.ne]

/-- The matrix `Matrix.cholesky A` is lower triangular. -/
theorem isLowerTriangular_cholesky : (cholesky A).IsLowerTriangular := fun _ _ hij =>
  cholesky_apply_of_gt A (OrderDual.toDual_lt_toDual.1 hij)

variable {A}

/-- **Correctness of the Cholesky recurrence**. Let $H$ be a Cholesky factor of $A$. Then the
recurrence (3.45) of [quarteroni2000numerical] computes $H^H$: `Matrix.cholesky A` $= H^H$. This
is the second half of Theorem 3.6 of [quarteroni2000numerical].

The recurrence equations are the entrywise identities `Matrix.IsCholesky.star_apply_mul_diag_eq`
and `Matrix.IsCholesky.re_diag_eq_sqrt` that every Cholesky factor satisfies. So the computed
entries agree with $H^H$ by strong induction along the order of $\min(i, j)$, with the diagonal
entry at each level before the entries below it. -/
theorem cholesky_eq_of_isCholesky {H : Matrix n n 𝕜} (h : IsCholesky A H) : cholesky A = Hᴴ := by
  suffices ∀ m i j, min i j = m → cholesky A i j = Hᴴ i j from
    Matrix.ext fun i j => this _ i j rfl
  intro m
  induction m using WellFoundedLT.induction with
  | ind m ih =>
  -- the diagonal entry at level `m`
  have hdiag : ∀ i, i = m → cholesky A i i = Hᴴ i i := by
    rintro i rfl
    rw [cholesky_apply_self, conjTranspose_apply, h.star_diag, ← h.coe_re_diag, h.re_diag_eq_sqrt]
    congr 3
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := (mem_filter.1 hk).2
    rw [ih k hk' i k (min_eq_right hk'.le), conjTranspose_apply, norm_star]
  intro i j hm
  rcases lt_trichotomy i j with hij | rfl | hij
  · rw [cholesky_apply_of_gt A hij, conjTranspose_apply, h.isUpperTriangular hij, star_zero]
  · exact hdiag i (by rw [min_self] at hm; exact hm)
  · have hjm : j = m := (min_eq_right hij.le).symm.trans hm
    rw [cholesky_apply_of_lt A hij, hdiag j hjm, conjTranspose_apply, h.star_diag,
      div_eq_iff (h.diag_ne_zero j), conjTranspose_apply, h.star_apply_mul_diag_eq hij]
    congr 1
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := (mem_filter.1 hk).2
    have hkm : k < m := hjm ▸ hk'
    rw [ih k hkm i k (min_eq_right (hk'.trans hij).le), ih k hkm j k (min_eq_right hk'.le),
      conjTranspose_apply, conjTranspose_apply, star_star]

/-- **The Cholesky recurrence computes the Cholesky factor**. Let $A \in \mathbb{K}^{n \times n}$ be
positive definite, and let $C$ be the matrix `Matrix.cholesky A` computed by the recurrence
(3.45) of [quarteroni2000numerical]. Then $C^H$ is the Cholesky factor of $A$. -/
theorem isCholesky_cholesky (hA : A.PosDef) : IsCholesky A (cholesky A)ᴴ := by
  obtain ⟨H, h⟩ := exists_isCholesky hA
  rw [cholesky_eq_of_isCholesky h, conjTranspose_conjTranspose]
  exact h

/-- Let $H$ be a Cholesky factor of $A$, and let $C$ be the matrix `Matrix.cholesky A`. Then
$C^H = H$.

So every method that computes a Cholesky factor computes `Matrix.cholesky`: the recurrence of
Program 7, the $LDL^H$ route and the QR route of Property 3.3 of [quarteroni2000numerical] all
give the unique factor. -/
theorem cholesky_conjTranspose_eq_of_isCholesky {H : Matrix n n 𝕜} (h : IsCholesky A H) :
    (cholesky A)ᴴ = H := by
  rw [cholesky_eq_of_isCholesky h, conjTranspose_conjTranspose]

end Recurrence

/-! ### The QR route -/

section QR

variable {m : Type*} [Fintype m]

/-- The last clause of Property 3.3 of [quarteroni2000numerical]. Let
$X, Q \in \mathbb{K}^{m \times n}$ and let $R \in \mathbb{K}^{n \times n}$. Assume that
$X = QR$, $Q^H Q = I$, $R$ is upper triangular and every diagonal entry $r_{ii}$ is positive, so
that $X = QR$ is a reduced QR factorization (`Matrix.exists_isThinQR`). Then $R$ is the Cholesky
factor of $X^H X$.

The proof is $X^H X = R^H Q^H Q R = R^H R$. -/
theorem isCholesky_conjTranspose_mul_self_of_qr {X Q : Matrix m n 𝕜} {R : Matrix n n 𝕜}
    (hX : X = Q * R) (hQ : Qᴴ * Q = 1) (hR : R.IsUpperTriangular) (hd : ∀ i, 0 < R i i) :
    IsCholesky (Xᴴ * X) R where
  isUpperTriangular := hR
  diag_pos := hd
  conjTranspose_mul_self := by
    rw [hX, conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Qᴴ, hQ, Matrix.one_mul]

/-- Let $X, Q \in \mathbb{K}^{m \times n}$ and let $R \in \mathbb{K}^{n \times n}$. Assume that
$X = QR$, $Q^H Q = I$, $R$ is upper triangular and every diagonal entry $r_{ii}$ is positive.
Then the Cholesky recurrence applied to $X^H X$ computes $R^H$: `Matrix.cholesky` of $X^H X$ is
$R^H$. This is Property 3.3 and §3.4.3 of [quarteroni2000numerical]. -/
theorem cholesky_conjTranspose_mul_self_of_qr {X Q : Matrix m n 𝕜} {R : Matrix n n 𝕜}
    (hX : X = Q * R) (hQ : Qᴴ * Q = 1) (hR : R.IsUpperTriangular) (hd : ∀ i, 0 < R i i) :
    cholesky (Xᴴ * X) = Rᴴ :=
  cholesky_eq_of_isCholesky (isCholesky_conjTranspose_mul_self_of_qr hX hQ hR hd)

/-- **The triangular factor of a thin QR factorization is the Cholesky factor of the Gram matrix**.
Let $A, Q \in \mathbb{K}^{m \times N}$ and $R \in \mathbb{K}^{N \times N}$ form a thin QR
factorization $A = QR$ (`Matrix.IsThinQR`), and assume that every diagonal entry $r_{jj}$ is
positive. Then $R$ is the Cholesky factor of $A^H A$, that is, $A^H A = R^H R$. This is Theorem
5.2.3 of [golub2013matrix], which states "$R_1 = G^T$ where $G$ is the lower triangular Cholesky
factor of $A^T A$".

With `Matrix.IsCholesky.unique`, this gives a second proof of `Matrix.IsThinQR.unique`. -/
theorem IsThinQR.isCholesky {N : ℕ} {A Q : Matrix m (Fin N) 𝕜} {R : Matrix (Fin N) (Fin N) 𝕜}
    (h : IsThinQR A Q R) (hd : ∀ j, 0 < R j j) : IsCholesky (Aᴴ * A) R :=
  isCholesky_conjTranspose_mul_self_of_qr h.mul_eq.symm h.conjTranspose_mul_self
    h.isUpperTriangular hd

end QR

/-! ### Mathlib's $LDL^H$ factorization -/

section LDL

open InnerProductSpace

variable [LocallyFiniteOrderBot n] {S : Matrix n n 𝕜} (hS : S.PosDef)
include hS

/-- Let $S \in \mathbb{K}^{n \times n}$ be positive definite. Then the Gram–Schmidt matrix
`LDL.lowerInv` of $S$, from Mathlib, has the diagonal entries $1$.

The $i$-th row is $e_i$ minus a combination of the earlier rows, and these vanish at the
coordinate $i$. -/
theorem LDL.lowerInv_apply_self (i : n) : LDL.lowerInv hS i i = 1 := by
  have h := congrFun (@gramSchmidt_def'' 𝕜 (n → 𝕜) _ (Sᵀ.toNormedAddCommGroup hS.transpose)
    (Sᵀ.toInnerProductSpace hS.transpose.posSemidef) n _ _ (Pi.basisFun 𝕜 n) i) i
  rw [Pi.add_apply, Finset.sum_apply, Finset.sum_eq_zero (fun k hk => ?_), add_zero,
    Pi.basisFun_apply, Pi.single_eq_same] at h
  · exact h.symm
  · rw [Pi.smul_apply]
    exact smul_eq_zero_of_right _
      (LDL.isLowerTriangular_lowerInv hS (OrderDual.toDual_lt_toDual.2 (Finset.mem_Iio.1 hk)))

/-- Let $S \in \mathbb{K}^{n \times n}$ be positive definite. Then the Gram–Schmidt matrix
`LDL.lowerInv` of $S$, from Mathlib, is unit lower triangular. -/
theorem LDL.lowerInv_isUnitLowerTriangular : (LDL.lowerInv hS).IsUnitLowerTriangular :=
  ⟨LDL.isLowerTriangular_lowerInv hS, LDL.lowerInv_apply_self hS⟩

/-- Let $S \in \mathbb{K}^{n \times n}$ be positive definite. Then the factor $L$ of Mathlib's
$LDL^H$ factorization of $S$, `LDL.lower`, is unit lower triangular.

Mathlib proves only that $L$ is lower triangular (`LDL.isLowerTriangular_lower`). The matrix $L$
is the inverse of the unit lower triangular matrix `LDL.lowerInv`. -/
theorem LDL.lower_isUnitLowerTriangular : (LDL.lower hS).IsUnitLowerTriangular :=
  (LDL.lowerInv_isUnitLowerTriangular hS).inv

/-- Let $S \in \mathbb{K}^{n \times n}$ be positive definite. Then every diagonal entry
`LDL.diagEntries` of Mathlib's $LDL^H$ factorization of $S$ is positive.

Each entry is the quadratic form of $S$ at a row of the invertible matrix `LDL.lowerInv`. -/
theorem LDL.diagEntries_pos (i : n) : 0 < LDL.diagEntries hS i := by
  have hx : star (LDL.lowerInv hS i) ≠ 0 := fun h0 => by
    have := congrFun h0 i
    rw [Pi.star_apply, LDL.lowerInv_apply_self, star_one, Pi.zero_apply] at this
    exact one_ne_zero this
  have := hS.dotProduct_mulVec_pos hx
  rw [LDL.diagEntries, EuclideanSpace.inner_toLp_toLp, dotProduct_comm]
  exact this

/-- Let $S \in \mathbb{K}^{n \times n}$ be positive definite, and let $L$ and $D$ be the factors
`LDL.lower` and `LDL.diag` of Mathlib. Then $S = L D L^H$ is an $LDM^T$ factorization in the
Hermitian form $M = \bar{L}$. -/
theorem isLDM_ldl : IsLDM S (LDL.lower hS) (LDL.diag hS) (LDL.lower hS)ᴴᵀ where
  isUnitLowerTriangular_left := LDL.lower_isUnitLowerTriangular hS
  isDiag := isDiag_diagonal _
  isUnitLowerTriangular_right := (LDL.lower_isUnitLowerTriangular hS).conjTranspose_transpose
  mul_eq := by rw [transpose_transpose, LDL.lower_conj_diag]

/-- Let $S \in \mathbb{K}^{n \times n}$ be positive definite, and let $S = L D L^H$ with $L$ unit
lower triangular and $D$ diagonal. Then $L$ and $D$ are the factors `LDL.lower` and `LDL.diag`
of Mathlib. So Mathlib's factors are the unique $LDL^H$ factors of a positive definite matrix. -/
theorem LDL.lower_eq_of_isLDM {L D : Matrix n n 𝕜} (h : IsLDM S L D Lᴴᵀ) :
    LDL.lower hS = L ∧ LDL.diag hS = D := by
  obtain ⟨LDM₀, -, huniq⟩ := existsUnique_isLDM hS.isUnit_strictLeadingPrincipalSubmatrix
  have := (huniq (LDL.lower hS, LDL.diag hS, (LDL.lower hS)ᴴᵀ) (isLDM_ldl hS)).trans
    (huniq (L, D, Lᴴᵀ) h).symm
  simp only [Prod.mk.injEq] at this
  exact ⟨this.1, this.2.1⟩

end LDL

/-! ### Unsymmetric matrices with a positive definite Hermitian part, and semidefinite matrices -/

section Unsymmetric

/-- **Corollary 4.2.4** of [golub2013matrix]. Let $A \in \mathbb{K}^{n \times n}$, and assume that
its Hermitian part $(A + A^H)/2$ is positive definite. Then $A$ has an LU factorization
$A = LU$, and every pivot $u_{ii}$ has a positive real part.

The source calls such an unsymmetric matrix $A$ "positive definite". The strict leading
principal submatrices of $A$ have a positive definite Hermitian part, so they are nonsingular.
And $u_{ii} = y^H A y$ for the conjugate $y$ of the $i$-th row of $L^{-1}$, because
$U L^{-H} = L^{-1} A L^{-H}$ has the diagonal of $U$. -/
theorem exists_isLU_of_posDef_hermitianPart {A : Matrix n n 𝕜}
    (hA : (hermitianPart A).PosDef) : ∃ L U, IsLU A L U ∧ ∀ i, 0 < RCLike.re (U i i) := by
  obtain ⟨L, U, h⟩ := exists_isLU_of_forall_isUnit_strictLeadingPrincipalSubmatrix fun k => by
    have hk : (hermitianPart (A.strictLeadingPrincipalSubmatrix k)).PosDef := by
      change (hermitianPart (A.submatrix Subtype.val Subtype.val)).PosDef
      rw [hermitianPart_submatrix]
      exact hA.submatrix Subtype.val_injective
    exact isUnit_of_posDef_hermitianPart hk
  refine ⟨L, U, h, fun i => ?_⟩
  have hLi := h.isUnitLowerTriangular.inv
  have hUeq : U = L⁻¹ * A := by
    rw [← h.mul_eq, ← Matrix.mul_assoc,
      nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 h.isUnitLowerTriangular.isUnit),
      Matrix.one_mul]
  set y : n → 𝕜 := fun l => star (L⁻¹ i l) with hy
  have hy0 : y ≠ 0 := fun h0 => by
    have := congrFun h0 i
    simp [hy, hLi.diag_eq_one] at this
  have e1 : (U * (L⁻¹)ᴴ) i i = U i i := by
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [conjTranspose_apply, hLi.diag_eq_one, star_one, mul_one]
    · intro b _ hbi
      rcases lt_or_gt_of_ne hbi with hb | hb
      · rw [h.isUpperTriangular hb, zero_mul]
      · rw [conjTranspose_apply, hLi.isLowerTriangular (OrderDual.toDual_lt_toDual.2 hb),
          star_zero, mul_zero]
    · simp
  have key : U i i = star y ⬝ᵥ (A *ᵥ y) := by
    rw [← e1, hUeq]
    simp only [Matrix.mul_apply, conjTranspose_apply, dotProduct, mulVec, hy, star_star,
      Pi.star_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  rw [key]
  exact re_dotProduct_mulVec_pos_of_posDef_hermitianPart hA hy0

end Unsymmetric

section SchurStep

variable {A : Matrix n n 𝕜} {p : n}

/-- **The quadratic form of one elimination step**. Let $A \in \mathbb{K}^{n \times n}$ with
$a_{pp} \neq 0$, and let $S$ be the Schur complement `Matrix.schurComplementSingle A p` of one
elimination step at the pivot $p$. Then for every vector $z$ on the indices other than $p$,
there is a vector $X$ on all indices that extends $z$ and satisfies
$$z^H S z = X^H A X.$$

The proof takes $X_p = -a_{pp}^{-1} \sum_{j \neq p} a_{pj} z_j$, for which $(AX)_p = 0$. -/
theorem exists_star_dotProduct_schurComplementSingle_mulVec (hpp : A p p ≠ 0)
    (z : {x : n // x ≠ p} → 𝕜) :
    ∃ X : n → 𝕜, (∀ t : {x : n // x ≠ p}, X t.1 = z t) ∧
      star z ⬝ᵥ (A.schurComplementSingle p *ᵥ z) = star X ⬝ᵥ (A *ᵥ X) := by
  classical
  set X : n → 𝕜 := fun t =>
    if h : t = p then -((A p p)⁻¹ * ∑ j : {x : n // x ≠ p}, A p j.1 * z j) else z ⟨t, h⟩ with hXd
  have hXz : ∀ t : {x : n // x ≠ p}, X t.1 = z t := fun t => by simp [hXd, t.2]
  have hzX : z = fun t : {x : n // x ≠ p} => X t.1 := funext fun t => (hXz t).symm
  have hXp : X p = -((A p p)⁻¹ * ∑ j : {x : n // x ≠ p}, A p j.1 * z j) := by simp [hXd]
  have hAX : (A *ᵥ X) p = 0 := by
    rw [mulVec, dotProduct, sum_eq_add_sum_subtype_ne p, hXp]
    simp only [hXz]
    field_simp
    ring
  refine ⟨X, hXz, ?_⟩
  conv_rhs => rw [dotProduct, sum_eq_add_sum_subtype_ne p, hAX, mul_zero, zero_add]
  rw [dotProduct]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [hzX, schurComplementSingle_mulVec_of_apply_eq_zero A hpp hAX t]
  rfl

end SchurStep

omit [Fintype n] in
/-- **Theorem 4.2.5** of [golub2013matrix]. Let $A \in \mathbb{K}^{n \times n}$, with $n$ finite,
have a positive definite Hermitian part, and let $p$ be an index. Then the Schur complement $S$
of one elimination step at the pivot $p$ (`Matrix.schurComplementSingle A p`) also has a
positive definite Hermitian part.

The Schur complement is the matrix $B_1 + C_1$ of (4.2.1) in the source. By
`Matrix.exists_star_dotProduct_schurComplementSingle_mulVec`, the quadratic form of $S$ is a
quadratic form of $A$. -/
theorem posDef_hermitianPart_schurComplementSingle [Finite n] {A : Matrix n n 𝕜}
    (hA : (hermitianPart A).PosDef) (p : n) :
    (hermitianPart (A.schurComplementSingle p)).PosDef := by
  have : Fintype n := Fintype.ofFinite n
  have hpp : A p p ≠ 0 := by
    intro h0
    have := re_dotProduct_mulVec_pos_of_posDef_hermitianPart hA (x := Pi.single p 1)
      (Pi.single_ne_zero_iff.2 one_ne_zero)
    simp [h0] at this
  refine posDef_iff_dotProduct_mulVec.2 ⟨hermitianPart_isHermitian _, fun z hz => ?_⟩
  rw [star_dotProduct_hermitianPart_mulVec, RCLike.ofReal_pos]
  obtain ⟨X, hXz, hq⟩ := exists_star_dotProduct_schurComplementSingle_mulVec hpp z
  rw [hq]
  refine re_dotProduct_mulVec_pos_of_posDef_hermitianPart hA fun h0 => hz (funext fun t => ?_)
  rw [← hXz t, h0]
  rfl

section Semidefinite

variable {A : Matrix n n 𝕜}

omit [Fintype n] [LinearOrder n] in
/-- (4.2.15) of [golub2013matrix]. Let $A \in \mathbb{K}^{n \times n}$ be positive semidefinite,
with $a_{ii} = 0$. Then the $i$-th row and the $i$-th column of $A$ are zero: $a_{ij} = 0$ and
$a_{ji} = 0$ for every index $j$.

The proof uses $|a_{ij}|^2 \le a_{ii} a_{jj}$. -/
theorem PosSemidef.apply_eq_zero_of_diag_eq_zero (hA : A.PosSemidef) {i : n} (hi : A i i = 0)
    (j : n) : A i j = 0 ∧ A j i = 0 := by
  have h1 := hA.norm_apply_sq_le_mul_re_diag i j
  have h2 := hA.norm_apply_sq_le_mul_re_diag j i
  rw [hi, map_zero, zero_mul] at h1
  rw [hi, map_zero, mul_zero] at h2
  exact ⟨norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm h1 (sq_nonneg _))),
    norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm h2 (sq_nonneg _)))⟩

omit [Fintype n] in
/-- The two statements `Matrix.PosSemidef.schurComplementSingle` and
`Matrix.PosSemidef.re_schurComplementSingle_apply_self_le`, proved together. -/
private theorem PosSemidef.schurComplementSingle_aux [Finite n] (hA : A.PosSemidef) {p : n}
    (hpp : A p p ≠ 0) :
    (A.schurComplementSingle p).PosSemidef ∧
      ∀ i, RCLike.re ((A.schurComplementSingle p) i i) ≤ RCLike.re (A i.1 i.1) := by
  have : Fintype n := Fintype.ofFinite n
  have hstar : ∀ a b, star (A a b) = A b a := fun a b => hA.1.apply b a
  have hαr : ((RCLike.re (A p p) : ℝ) : 𝕜) = A p p :=
    RCLike.conj_eq_iff_re.1 (by rw [← RCLike.star_def, hstar])
  have hαpos : 0 < RCLike.re (A p p) := by
    have h0 : (0 : 𝕜) ≤ A p p := hA.diag_nonneg
    have h1 := (RCLike.le_iff_re_im.1 h0).1
    rw [map_zero] at h1
    refine lt_of_le_of_ne h1 fun h => hpp ?_
    rw [← hαr, ← h, RCLike.ofReal_zero]
  refine ⟨posSemidef_iff_dotProduct_mulVec.2 ⟨?_, fun z => ?_⟩, fun i => ?_⟩
  · ext i j
    simp only [conjTranspose_apply, schurComplementSingle_apply, star_sub, star_mul', star_inv₀,
      hstar]
    ring
  · obtain ⟨X, -, hq⟩ := exists_star_dotProduct_schurComplementSingle_mulVec hpp z
    rw [hq]
    exact hA.dotProduct_mulVec_nonneg X
  · rw [schurComplementSingle_apply, map_sub]
    refine sub_le_self _ ?_
    have : A i.1 p * (A p p)⁻¹ * A p i.1 =
        ((‖A i.1 p‖ ^ 2 / RCLike.re (A p p) : ℝ) : 𝕜) := by
      rw [← hstar i.1 p, ← hαr, RCLike.star_def, mul_comm (A i.1 p), mul_assoc, RCLike.mul_conj]
      push_cast
      field_simp
    rw [this, RCLike.ofReal_re]
    positivity

omit [Fintype n] in
/-- **One step of the outer-product $LDL^H$ factorization of a positive semidefinite matrix**,
(4.2.16) of [golub2013matrix]. Let $A \in \mathbb{K}^{n \times n}$, with $n$ finite, be positive
semidefinite, and let $a_{pp} \neq 0$. Then the Schur complement of one elimination step at the
pivot $p$ (`Matrix.schurComplementSingle A p`) is positive semidefinite.

The Schur complement is the matrix $\tilde{A} = B - v v^T / \alpha$ of the source. This is the
semidefinite analogue of `Matrix.PosDef.schurComplement`. Its diagonal is bounded by the
diagonal of $A$ (`Matrix.PosSemidef.re_schurComplementSingle_apply_self_le`). -/
theorem PosSemidef.schurComplementSingle [Finite n] (hA : A.PosSemidef) {p : n} (hpp : A p p ≠ 0) :
    (A.schurComplementSingle p).PosSemidef :=
  (hA.schurComplementSingle_aux hpp).1

omit [Fintype n] in
/-- (4.2.16) of [golub2013matrix]. Let $A \in \mathbb{K}^{n \times n}$, with $n$ finite, be positive
semidefinite, let $a_{pp} \neq 0$, and let $\tilde{A}$ be the Schur complement of one
elimination step at the pivot $p$ (`Matrix.schurComplementSingle A p`). Then the diagonal of
$\tilde{A}$ is bounded by the diagonal of $A$: for every index $i \neq p$,
$$\operatorname{Re} \tilde{a}_{ii} \le \operatorname{Re} a_{ii}.$$
-/
theorem PosSemidef.re_schurComplementSingle_apply_self_le [Finite n] (hA : A.PosSemidef) {p : n}
    (hpp : A p p ≠ 0) (i : {x : n // x ≠ p}) :
    RCLike.re ((A.schurComplementSingle p) i i) ≤ RCLike.re (A i.1 i.1) :=
  (hA.schurComplementSingle_aux hpp).2 i

end Semidefinite

section Factor

variable {A : Matrix n n 𝕜}

/-- **The Cholesky factor has the lower bandwidth of the matrix**. Let
$A \in \mathbb{K}^{n \times n}$ be positive definite with the lower bandwidth $p$. Then the
lower triangular factor `Matrix.cholesky A` also has the lower bandwidth $p$. This is in §4.3.5
of [golub2013matrix].

The factor $H^H$ is $L D$ for the LU factorization $A = (H^H D^{-1})(D H)$, and the lower factor
$L$ keeps the lower bandwidth of $A$ (`Matrix.IsLU.hasLowerBandwidth`). Multiplication on the
right by a nonsingular diagonal matrix changes no zero pattern. -/
theorem cholesky_hasLowerBandwidth (hA : A.PosDef) {p : ℕ} (hp : A.HasLowerBandwidth p) :
    (cholesky A).HasLowerBandwidth p := by
  have hc := isCholesky_cholesky hA
  have hL := hc.isLU.hasLowerBandwidth hA.isUnit_strictLeadingPrincipalSubmatrix hp
  intro i j hij
  have := hL i j hij
  rw [conjTranspose_conjTranspose, mul_diagonal] at this
  exact (mul_eq_zero.1 this).resolve_right (inv_ne_zero (hc.diag_ne_zero j))

/-- **The entries of the Cholesky factor are bounded by the diagonal**. Let
$A \in \mathbb{K}^{n \times n}$ be positive definite, and let $G$ be the lower triangular factor
`Matrix.cholesky A`. Then for all indices $i$ and $j$,
$$|g_{ij}|^2 \le \operatorname{Re} a_{ii}.$$
This is in §4.2.6 of [golub2013matrix], which writes
"$g_{ij}^2 \le \sum_{k \le i} g_{ik}^2 = a_{ii}$".

The bound follows from the diagonal of $A = G G^H$. -/
theorem sq_norm_cholesky_apply_le (hA : A.PosDef) (i j : n) :
    ‖cholesky A i j‖ ^ 2 ≤ RCLike.re (A i i) := by
  have hc := isCholesky_cholesky hA
  have hsum : RCLike.re (A i i) = ∑ k, ‖cholesky A i k‖ ^ 2 := by
    conv_lhs => rw [← hc.conjTranspose_mul_self]
    rw [conjTranspose_conjTranspose, Matrix.mul_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [conjTranspose_apply, RCLike.star_def, RCLike.mul_conj, ← RCLike.ofReal_pow,
      RCLike.ofReal_re]
  rw [hsum]
  exact Finset.single_le_sum (f := fun k => ‖cholesky A i k‖ ^ 2) (fun k _ => sq_nonneg _)
    (Finset.mem_univ j)

open scoped Matrix.Norms.L2Operator in
/-- Let $A \in \mathbb{K}^{n \times n}$ be positive definite, and let $G$ be the lower triangular
factor `Matrix.cholesky A`. Then in the spectral norm,
$$\|G\|_2^2 = \|A\|_2.$$
This is in §4.2.6 of [golub2013matrix].

The proof is Mathlib's C*-identity $\|B^H B\| = \|B\|^2$ for $B = G^H$, since $A = G G^H$. -/
theorem l2_opNorm_cholesky_sq (hA : A.PosDef) : ‖cholesky A‖ ^ 2 = ‖A‖ := by
  have hc := isCholesky_cholesky hA
  conv_rhs => rw [← hc.conjTranspose_mul_self]
  rw [l2_opNorm_conjTranspose_mul_self, l2_opNorm_conjTranspose, sq]

end Factor

/-! ### The rank-revealing pivoted $LDL^H$ factorization of a semidefinite matrix -/

section PivotedLDL

/-- For a unit lower triangular $L$, the diagonal entry of $L \operatorname{diag}(d) L^H$ at the
least index $i$ is $d_i$. -/
private theorem mul_diagonal_mul_conjTranspose_apply_of_isBot {n : ℕ}
    {L : Matrix (Fin n) (Fin n) 𝕜} (hL : L.IsUnitLowerTriangular) (d : Fin n → 𝕜) {i : Fin n}
    (hi : IsBot i) : (L * diagonal d * Lᴴ) i i = d i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · rw [mul_diagonal, conjTranspose_apply, hL.diag_eq_one, star_one, mul_one, one_mul]
  · intro k _ hki
    rw [mul_diagonal, hL.isLowerTriangular (OrderDual.toDual_lt_toDual.2
      (lt_of_le_of_ne (hi k) (Ne.symm hki))), zero_mul, zero_mul]
  · simp

/-- **The pivoted $LDL^H$ factorization of a positive semidefinite matrix**, without the count of
the rank. Let $A \in \mathbb{K}^{n \times n}$ be positive semidefinite, with the indices
$0, \dots, n - 1$. Then there are a permutation $\sigma$, a unit lower triangular $L$ and a
nonincreasing real vector $d \ge 0$ with
$$A(\sigma, \sigma) = L \operatorname{diag}(d) L^H,$$
where $A(\sigma, \sigma)$ is the symmetric permutation `A.submatrix σ σ` of $A$.

The proof takes the largest remaining diagonal entry as the pivot at every step. -/
theorem PosSemidef.exists_perm_ldl_antitone :
    ∀ {n : ℕ} {A : Matrix (Fin n) (Fin n) 𝕜}, A.PosSemidef →
      ∃ (σ : Equiv.Perm (Fin n)) (L : Matrix (Fin n) (Fin n) 𝕜) (d : Fin n → ℝ),
        L.IsUnitLowerTriangular ∧ A.submatrix σ σ = L * diagonal (fun i => (d i : 𝕜)) * Lᴴ ∧
          Antitone d ∧ ∀ i, 0 ≤ d i
  | 0, A, _ => ⟨1, 1, 0, isUnitLowerTriangular_one, Subsingleton.elim _ _,
      fun _ _ _ => le_rfl, fun _ => le_rfl⟩
  | m + 1, A, hA => by
    have hdiag : ∀ i, ((RCLike.re (A i i) : ℝ) : 𝕜) = A i i := fun i =>
      RCLike.conj_eq_iff_re.1 (by rw [← RCLike.star_def]; exact hA.1.apply i i)
    have hre0 : ∀ i, 0 ≤ RCLike.re (A i i) := fun i => (RCLike.nonneg_iff.1 hA.diag_nonneg).1
    obtain ⟨p, -, hp⟩ := Finset.exists_max_image univ (fun i => RCLike.re (A i i)) univ_nonempty
    rcases (hre0 p).eq_or_lt with h0 | hpos
    · -- the largest diagonal entry vanishes, so `A = 0`
      have hz : ∀ i, A i i = 0 := fun i => by
        rw [← hdiag i, RCLike.ofReal_eq_zero]
        exact le_antisymm (h0 ▸ hp i (mem_univ _)) (hre0 i)
      have hA0 : A = 0 := by
        ext i j
        exact (hA.apply_eq_zero_of_diag_eq_zero (hz i) j).1
      refine ⟨1, 1, 0, isUnitLowerTriangular_one, ?_, fun _ _ _ => le_rfl, fun _ => le_rfl⟩
      rw [hA0]
      simp
    -- pivot at the largest diagonal entry
    set α := RCLike.re (A p p) with hα
    have hαne : (α : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.2 hpos.ne'
    set B := A.submatrix (Equiv.swap 0 p) (Equiv.swap 0 p) with hBd
    have hB : B.PosSemidef := hA.submatrix _
    have hB00 : B 0 0 = (α : 𝕜) := by
      simp [hBd, hα, hdiag]
    have hBstar : ∀ a b, star (B a b) = B b a := fun a b => hB.1.apply b a
    have hBle : ∀ y, RCLike.re (B y y) ≤ α := fun y => hp _ (mem_univ _)
    set e : Fin m → {i : Fin (m + 1) // i ≠ 0} := fun i => ⟨i.succ, Fin.succ_ne_zero i⟩ with he
    have hSchur := hB.schurComplementSingle_aux (p := 0) (by rw [hB00]; exact hαne)
    set S := (B.schurComplementSingle 0).submatrix e e with hSd
    have hS : S.PosSemidef := hSchur.1.submatrix e
    obtain ⟨σ', L', d', hL', heq, hanti, hnn⟩ := PosSemidef.exists_perm_ldl_antitone hS
    set c : Fin m → 𝕜 := fun x => B (σ' x).succ 0 with hc
    set L : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜 := of fun i j =>
      Fin.cases (motive := fun _ => 𝕜) (Fin.cases (motive := fun _ => 𝕜) 1 (fun _ => 0) j)
        (fun i' => Fin.cases (motive := fun _ => 𝕜) (c i' / α) (fun j' => L' i' j') j) i with hLd
    have hd0 : ∀ (h : 0 < m), d' ⟨0, h⟩ ≤ α := fun h => by
      have e1 := congrFun (congrFun heq ⟨0, h⟩) ⟨0, h⟩
      rw [mul_diagonal_mul_conjTranspose_apply_of_isBot hL' _
        (fun k => Fin.le_def.2 (Nat.zero_le _))] at e1
      have e2 : RCLike.re ((d' ⟨0, h⟩ : ℝ) : 𝕜) = RCLike.re (S (σ' ⟨0, h⟩) (σ' ⟨0, h⟩)) := by
        rw [← e1]
        rfl
      rw [RCLike.ofReal_re] at e2
      rw [e2]
      exact (hSchur.2 _).trans (hBle _)
    refine ⟨Equiv.Perm.decomposeFin.symm (p, σ'), L, Fin.cons α d',
      ⟨fun i j hij => ?_, fun i => ?_⟩, ?_, fun i j hij => ?_, fun i => ?_⟩
    · have hij' : i < j := OrderDual.toDual_lt_toDual.1 hij
      induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero => exact absurd hij' (lt_irrefl _)
        | succ j' => simp [hLd]
      | succ i' =>
        induction j using Fin.cases with
        | zero => exact absurd hij' (not_lt.2 (Fin.le_def.2 (Nat.zero_le _)))
        | succ j' =>
          simp only [hLd, of_apply, Fin.cases_succ]
          exact hL'.isLowerTriangular (OrderDual.toDual_lt_toDual.2 (Fin.succ_lt_succ_iff.1 hij'))
    · induction i using Fin.cases with
      | zero => simp [hLd]
      | succ i' => simp [hLd, hL'.diag_eq_one]
    · ext i j
      rw [Matrix.mul_apply, Fin.sum_univ_succ]
      simp only [submatrix_apply, conjTranspose_apply, mul_diagonal, Fin.cons_zero, Fin.cons_succ]
      induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero =>
          simp [hLd, Equiv.Perm.decomposeFin_symm_apply_zero, hα, hdiag]
        | succ j' =>
          simp only [hLd, of_apply, Fin.cases_zero, Fin.cases_succ, zero_mul, Finset.sum_const_zero,
            add_zero, one_mul, Equiv.Perm.decomposeFin_symm_apply_zero,
            Equiv.Perm.decomposeFin_symm_apply_succ, star_div₀, hc, hBstar]
          rw [RCLike.star_def, RCLike.conj_ofReal]
          have : A p ((Equiv.swap 0 p) (σ' j').succ) = B 0 (σ' j').succ := by
            simp [hBd]
          rw [this]
          field_simp
      | succ i' =>
        induction j using Fin.cases with
        | zero =>
          simp only [hLd, of_apply, Fin.cases_zero, Fin.cases_succ, star_zero, mul_zero,
            Finset.sum_const_zero, add_zero, star_one, mul_one,
            Equiv.Perm.decomposeFin_symm_apply_zero, Equiv.Perm.decomposeFin_symm_apply_succ, hc]
          have : A ((Equiv.swap 0 p) (σ' i').succ) p = B (σ' i').succ 0 := by
            simp [hBd]
          rw [this]
          field_simp
        | succ j' =>
          have e1 := congrFun (congrFun heq i') j'
          rw [Matrix.mul_apply] at e1
          simp only [conjTranspose_apply, mul_diagonal] at e1
          simp only [hLd, of_apply, Fin.cases_succ, Fin.cases_zero,
            Equiv.Perm.decomposeFin_symm_apply_succ, hc]
          rw [← e1]
          simp only [submatrix_apply, hSd, he, schurComplementSingle_apply]
          have : A ((Equiv.swap 0 p) (σ' i').succ) ((Equiv.swap 0 p) (σ' j').succ) =
              B (σ' i').succ (σ' j').succ := rfl
          rw [this, hB00, star_div₀, RCLike.star_def, RCLike.conj_ofReal, ← RCLike.star_def,
            hBstar]
          field_simp
          ring
    · induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero => exact le_rfl
        | succ j' =>
          simp only [Fin.cons_zero, Fin.cons_succ]
          exact (hanti (Fin.le_def.2 (Nat.zero_le _) : (⟨0, Fin.pos j'⟩ : Fin m) ≤ j')).trans
            (hd0 (Fin.pos j'))
      | succ i' =>
        induction j using Fin.cases with
        | zero => exact absurd hij (not_le.2 (Fin.succ_pos _))
        | succ j' =>
          simp only [Fin.cons_succ]
          exact hanti (Fin.succ_le_succ_iff.1 hij)
    · induction i using Fin.cases with
      | zero => exact hpos.le
      | succ i' => exact hnn i'

/-- On `Fin n`, a nonnegative nonincreasing vector $d$ is positive exactly at the first $k$ indices,
where $k$ is the number of its nonzero entries. -/
private theorem pos_iff_lt_card_of_antitone {n : ℕ} {d : Fin n → ℝ} (hanti : Antitone d)
    (hnn : ∀ i, 0 ≤ d i) (i : Fin n) : 0 < d i ↔ (i : ℕ) < #{j | d j ≠ 0} := by
  constructor
  · intro hi
    have hsub : univ.filter (fun j : Fin n => (j : ℕ) < i + 1) ⊆ univ.filter (fun j => d j ≠ 0) :=
      fun j hj => by
        simp only [mem_filter, mem_univ, true_and] at hj ⊢
        exact (lt_of_lt_of_le hi (hanti (Fin.le_def.2 (Nat.lt_succ_iff.1 hj)))).ne'
    have := card_le_card hsub
    rw [Fin.card_filter_val_lt] at this
    omega
  · intro hi
    by_contra hcon
    have hdi : d i = 0 := le_antisymm (not_lt.1 hcon) (hnn i)
    have hsub : univ.filter (fun j => d j ≠ 0) ⊆ univ.filter (fun j : Fin n => (j : ℕ) < i) :=
      fun j hj => by
        simp only [mem_filter, mem_univ, true_and] at hj ⊢
        by_contra hji
        exact hj (le_antisymm (hdi ▸ hanti (Fin.le_def.2 (not_lt.1 hji))) (hnn j))
    have := card_le_card hsub
    rw [Fin.card_filter_val_lt] at this
    omega

/-- **The rank-revealing pivoted factorization**, (4.2.17) of [golub2013matrix]. Let
$A \in \mathbb{K}^{n \times n}$ be positive semidefinite with the rank $r$, with the indices
$0, \dots, n - 1$. Then there are a permutation $\sigma$, a unit lower triangular $L$ and a
nonincreasing real vector $d$ with
$$A(\sigma, \sigma) = L \operatorname{diag}(d) L^H,$$
$d_i > 0$ for $i < r$, and $d_i = 0$ for $i \ge r$. So only the first $r$ columns of $L$
contribute to the factorization. Here $A(\sigma, \sigma)$ is the symmetric permutation
`A.submatrix σ σ` of $A$.

The pivot is the largest remaining diagonal entry
(`Matrix.PosSemidef.exists_perm_ldl_antitone`). The matrix $A$ is congruent to
$\operatorname{diag}(d)$, so its rank is the number of nonzero pivots. -/
theorem PosSemidef.exists_perm_ldl_rank {n : ℕ} {A : Matrix (Fin n) (Fin n) 𝕜}
    (hA : A.PosSemidef) :
    ∃ (σ : Equiv.Perm (Fin n)) (L : Matrix (Fin n) (Fin n) 𝕜) (d : Fin n → ℝ),
      L.IsUnitLowerTriangular ∧ A.submatrix σ σ = L * diagonal (fun i => (d i : 𝕜)) * Lᴴ ∧
        Antitone d ∧ (∀ i : Fin n, (i : ℕ) < A.rank → 0 < d i) ∧
          ∀ i : Fin n, A.rank ≤ i → d i = 0 := by
  classical
  obtain ⟨σ, L, d, hL, heq, hanti, hnn⟩ := hA.exists_perm_ldl_antitone
  have hLu : IsUnit L.det := (isUnit_iff_isUnit_det _).1 hL.isUnit
  have hLHu : IsUnit Lᴴ.det := by
    rw [det_conjTranspose]
    exact hLu.star
  have hrank : A.rank = #{j | d j ≠ 0} := by
    rw [← rank_submatrix A σ σ, heq, rank_mul_eq_left_of_isUnit_det _ _ hLHu,
      rank_mul_eq_right_of_isUnit_det _ _ hLu, rank_diagonal, Fintype.card_subtype]
    simp only [ne_eq, RCLike.ofReal_eq_zero]
  refine ⟨σ, L, d, hL, heq, hanti, fun i hi => ?_, fun i hi => ?_⟩
  · rw [hrank] at hi
    exact (pos_iff_lt_card_of_antitone hanti hnn i).2 hi
  · rw [hrank] at hi
    exact le_antisymm (not_lt.1 fun h => absurd ((pos_iff_lt_card_of_antitone hanti hnn i).1 h)
      (not_lt.2 hi)) (hnn i)

end PivotedLDL

/-! ### The block form of the Cholesky factor -/

section Block

/-- **The block form of the Cholesky factor**, (4.2.18) of [golub2013matrix], which specifies the
block Cholesky algorithms 4.2.3 and 4.2.4. Let $A \in \mathbb{K}^{(r+s) \times (r+s)}$ be
positive definite, and write it in blocks as
$$A = \begin{bmatrix} A_{11} & A_{12} \\ A_{21} & A_{22} \end{bmatrix}$$
with $A_{11} \in \mathbb{K}^{r \times r}$. Let $G_{11}$ be the lower triangular Cholesky factor
of $A_{11}$, and let $G_{22}$ be the lower triangular Cholesky factor of the Schur complement
$A_{22} - A_{21} A_{11}^{-1} A_{12}$. Then the lower triangular Cholesky factor of $A$ is
$$\begin{bmatrix} G_{11} & 0 \\ A_{21} G_{11}^{-H} & G_{22} \end{bmatrix}.$$

The source writes the condition on the block $G_{21}$ as $G_{21} G_{11}^T = A_{21}$. The blocks
are taken along `finSumFinEquiv`, and each factor is `Matrix.cholesky` of the block. The proof
uses the uniqueness of the Cholesky factor: the block matrix is lower triangular with a positive
diagonal in the order of `Fin (r + s)`, and its product with its conjugate transpose is $A$. -/
theorem cholesky_finSumFin {r s : ℕ} {A : Matrix (Fin (r + s)) (Fin (r + s)) 𝕜} (hA : A.PosDef) :
    (cholesky A).submatrix finSumFinEquiv finSumFinEquiv =
      fromBlocks (cholesky (A.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁) 0
        ((A.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁ *
          (cholesky (A.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁)ᴴ⁻¹)
        (cholesky (A.submatrix finSumFinEquiv finSumFinEquiv).schurComplement) := by
  set e : Fin r ⊕ Fin s ≃ Fin (r + s) := finSumFinEquiv with he
  set A' := A.submatrix e e with hA'd
  have hA' : A'.PosDef := hA.submatrix e.injective
  have h11 : A'.toBlocks₁₁.PosDef := hA'.submatrix Sum.inl_injective
  have hS : A'.schurComplement.PosDef := hA'.schurComplement
  set G₁ := cholesky A'.toBlocks₁₁ with hG₁
  set G₂ := cholesky A'.schurComplement with hG₂
  have c1 := isCholesky_cholesky h11
  have c2 := isCholesky_cholesky hS
  have hG1 : G₁ * G₁ᴴ = A'.toBlocks₁₁ := by
    simpa using c1.conjTranspose_mul_self
  have hG2 : G₂ * G₂ᴴ = A'.schurComplement := by
    simpa using c2.conjTranspose_mul_self
  have hu : IsUnit G₁ᴴ.det := (isUnit_iff_isUnit_det _).1 c1.isUnit
  have hu' : IsUnit G₁.det := by
    rw [← conjTranspose_conjTranspose G₁, det_conjTranspose]
    exact hu.star
  have h12 : A'.toBlocks₁₂ = A'.toBlocks₂₁ᴴ := by
    ext i j
    exact (hA'.1.apply (Sum.inl i) (Sum.inr j)).symm
  set K := fromBlocks G₁ 0 (A'.toBlocks₂₁ * G₁ᴴ⁻¹) G₂ with hK
  have hKK : K * Kᴴ = A' := by
    rw [hK, fromBlocks_conjTranspose, fromBlocks_multiply]
    conv_rhs => rw [← fromBlocks_toBlocks A']
    have hinv : (G₁ᴴ⁻¹)ᴴ = G₁⁻¹ := by
      rw [conjTranspose_nonsing_inv, conjTranspose_conjTranspose]
    congr 1 <;> simp only [conjTranspose_mul, hinv, conjTranspose_zero, Matrix.mul_zero,
      Matrix.zero_mul, add_zero, Matrix.mul_assoc]
    · exact hG1
    · rw [← Matrix.mul_assoc, mul_nonsing_inv _ hu', Matrix.one_mul, h12]
    · rw [nonsing_inv_mul _ hu, Matrix.mul_one]
    · rw [hG2, schurComplement_eq, h12, ← hG1, Matrix.mul_inv_rev]
      simp only [Matrix.mul_assoc]
      abel
  have hc : cholesky A = K.submatrix e.symm e.symm := by
    refine (cholesky_eq_of_isCholesky (H := (K.submatrix e.symm e.symm)ᴴ) ⟨?_, ?_, ?_⟩).trans
      (conjTranspose_conjTranspose _)
    · intro i j hij
      have hij' : (j : ℕ) < i := hij
      rw [conjTranspose_apply, submatrix_apply]
      rcases finSumFinEquiv_symm_cases i with ⟨hi, ei⟩ | ⟨hi, ei⟩ <;>
        rcases finSumFinEquiv_symm_cases j with ⟨hj, ej⟩ | ⟨hj, ej⟩ <;> rw [ei, ej]
      · rw [hK, fromBlocks_apply₁₁, hG₁, isLowerTriangular_cholesky _
          (OrderDual.toDual_lt_toDual.2 (Fin.lt_def.2 (by simpa using hij'))), star_zero]
      · omega
      · rw [hK, fromBlocks_apply₁₂, Matrix.zero_apply, star_zero]
      · rw [hK, fromBlocks_apply₂₂, hG₂, isLowerTriangular_cholesky _
          (OrderDual.toDual_lt_toDual.2 (Fin.lt_def.2 (by simp; omega))), star_zero]
    · intro i
      rw [conjTranspose_apply, submatrix_apply]
      rcases finSumFinEquiv_symm_cases i with ⟨hi, ei⟩ | ⟨hi, ei⟩ <;> rw [ei]
      · rw [hK, fromBlocks_apply₁₁, ← conjTranspose_apply]
        exact c1.diag_pos _
      · rw [hK, fromBlocks_apply₂₂, ← conjTranspose_apply]
        exact c2.diag_pos _
    · rw [conjTranspose_conjTranspose, conjTranspose_submatrix, submatrix_mul_equiv, hKK, hA'd,
        submatrix_submatrix]
      simp
  rw [hc, submatrix_submatrix]
  simp

end Block

/-! ### The size of $|L| |U|$ when the Hermitian part is positive definite -/

section UnsymmetricLU

open scoped Matrix.Norms.L2Operator

/-- For a real positive definite $T$, a real square matrix $M$ and a vector $x$,
$\|Mx\|^2 \le \|M T^{-1} M^T\|_2 \, x^T T x$. -/
private theorem dotProduct_mulVec_self_le_of_posDef {T : Matrix n n ℝ} (hT : T.PosDef)
    (M : Matrix n n ℝ) (x : n → ℝ) :
    (M *ᵥ x) ⬝ᵥ (M *ᵥ x) ≤ ‖M * T⁻¹ * Mᵀ‖ * (x ⬝ᵥ (T *ᵥ x)) := by
  have hTu : IsUnit T.det := (isUnit_iff_isUnit_det T).1 hT.isUnit
  set y := M *ᵥ x
  set w := T⁻¹ *ᵥ (Mᵀ *ᵥ y) with hw
  have hTw : T *ᵥ w = Mᵀ *ᵥ y := by rw [mulVec_mulVec, mul_nonsing_inv T hTu, one_mulVec]
  have hyy : y ⬝ᵥ y = x ⬝ᵥ (T *ᵥ w) := by
    rw [hTw]
    conv_rhs => rw [dotProduct_mulVec, vecMul_transpose]
  have hwTw : w ⬝ᵥ (T *ᵥ w) = y ⬝ᵥ ((M * T⁻¹ * Mᵀ) *ᵥ y) := by
    rw [hTw, dotProduct_mulVec w, vecMul_transpose, dotProduct_comm]
    simp only [hw, mulVec_mulVec, Matrix.mul_assoc]
  have hq0 : 0 ≤ x ⬝ᵥ (T *ᵥ x) := by simpa using hT.posSemidef.dotProduct_mulVec_nonneg x
  have h1 := hT.posSemidef.sq_dotProduct_mulVec_le x w
  have h2 : y ⬝ᵥ ((M * T⁻¹ * Mᵀ) *ᵥ y) ≤ ‖M * T⁻¹ * Mᵀ‖ * (y ⬝ᵥ y) := by
    have := dotProduct_mulVec_le_l2_opNorm (M * T⁻¹ * Mᵀ) y y
    rwa [← sq, ← dotProduct_self_eq_norm_sq] at this
  have hy0 : 0 ≤ y ⬝ᵥ y := by simpa using dotProduct_star_self_nonneg y
  have hsq : (y ⬝ᵥ y) ^ 2 ≤ (y ⬝ᵥ y) * (‖M * T⁻¹ * Mᵀ‖ * (x ⬝ᵥ (T *ᵥ x))) :=
    calc (y ⬝ᵥ y) ^ 2 = (x ⬝ᵥ (T *ᵥ w)) ^ 2 := by rw [hyy]
      _ ≤ (x ⬝ᵥ (T *ᵥ x)) * (w ⬝ᵥ (T *ᵥ w)) := h1
      _ ≤ (x ⬝ᵥ (T *ᵥ x)) * (‖M * T⁻¹ * Mᵀ‖ * (y ⬝ᵥ y)) := by
          rw [hwTw]; exact mul_le_mul_of_nonneg_left h2 hq0
      _ = _ := by ring
  have hr0 : 0 ≤ ‖M * T⁻¹ * Mᵀ‖ * (x ⬝ᵥ (T *ᵥ x)) := mul_nonneg (norm_nonneg _) hq0
  nlinarith

/-- For a real $A$ whose symmetric part $T = (A + A^T)/2$ is positive definite, with the skew part
$S = A - T$: $x^T A x = x^T T x$, $A T^{-1} A^T = A^T T^{-1} A$ (both equal $T - S T^{-1} S$,
the identity $A T^{-1} A^T = T + S T^{-1} S^T$ of Golub and Van Loan (1979)), and $\|A T^{-1}
A^T\|_2 \le \|T\|_2 + \|S T^{-1} S\|_2$. -/
private theorem growth_aux {A : Matrix n n ℝ} (hT : (hermitianPart A).PosDef) (x : n → ℝ) :
    x ⬝ᵥ (A *ᵥ x) = x ⬝ᵥ (hermitianPart A *ᵥ x) ∧
      A * (hermitianPart A)⁻¹ * Aᵀ = Aᵀ * (hermitianPart A)⁻¹ * Aᵀᵀ ∧
      ‖A * (hermitianPart A)⁻¹ * Aᵀ‖ ≤ ‖hermitianPart A‖
        + ‖(A - hermitianPart A) * (hermitianPart A)⁻¹ * (A - hermitianPart A)‖ := by
  classical
  set T := hermitianPart A with hTdef
  set S := A - T with hSdef
  have hTt : Tᵀ = T := by
    have := hT.isHermitian.eq
    rwa [conjTranspose_eq_transpose_of_trivial] at this
  have hAT : Aᵀ = T - S := by
    rw [hSdef, hTdef, hermitianPart, conjTranspose_eq_transpose_of_trivial]
    ext i j
    simp only [transpose_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
    ring
  have hSt : Sᵀ = -S := by
    have e : Sᵀ = Aᵀ - Tᵀ := by rw [hSdef, transpose_sub]
    rw [e, hAT, hTt]
    abel
  have hA : A = T + S := by rw [hSdef]; abel
  have hTu : IsUnit T.det := (isUnit_iff_isUnit_det T).1 hT.isUnit
  have hTT : T * T⁻¹ = 1 := mul_nonsing_inv T hTu
  have hTT' : T⁻¹ * T = 1 := nonsing_inv_mul T hTu
  have hskew : x ⬝ᵥ (S *ᵥ x) = 0 := by
    have h1 : x ⬝ᵥ (S *ᵥ x) = -(x ⬝ᵥ (S *ᵥ x)) := by
      conv_lhs => rw [dotProduct_mulVec, ← mulVec_transpose, hSt, neg_mulVec, neg_dotProduct,
        dotProduct_comm]
    linarith
  have hG : A * T⁻¹ * Aᵀ = T - S * T⁻¹ * S := by
    rw [hAT, hA]
    simp only [Matrix.add_mul, Matrix.mul_sub, hTT, Matrix.one_mul, Matrix.mul_assoc, hTT',
      Matrix.mul_one]
    abel
  have hG' : Aᵀ * T⁻¹ * Aᵀᵀ = T - S * T⁻¹ * S := by
    rw [transpose_transpose, hAT, hA]
    simp only [Matrix.sub_mul, Matrix.mul_add, hTT, Matrix.one_mul, Matrix.mul_assoc, hTT',
      Matrix.mul_one]
    abel
  refine ⟨by rw [hA, add_mulVec, dotProduct_add, hskew, add_zero], hG.trans hG'.symm, ?_⟩
  rw [hG]
  exact norm_sub_le _ _

/-- **The growth bound behind Theorem 4.2.6** of [golub2013matrix]. Let
$A \in \mathbb{R}^{n \times n}$ have a positive definite symmetric part $T = (A + A^T)/2$, and
let $S = A - T$ be its skew part. Then for every $x \in \mathbb{R}^n$, in the spectral norm,
$$\|Ax\|^2 \le \bigl(\|T\|_2 + \|S T^{-1} S\|_2\bigr) \, x^T A x.$$

The proof uses $x^T A x = x^T T x$ and $A T^{-1} A^T = T - S T^{-1} S$, so that
$\|Ax\|^2 \le \|A T^{-1} A^T\|_2 \, x^T T x$ by the Cauchy–Schwarz inequality for the form of
$T$. The bound for the transpose is
`Matrix.dotProduct_transpose_mulVec_self_le_of_posDef_hermitianPart`. -/
theorem dotProduct_mulVec_self_le_of_posDef_hermitianPart {A : Matrix n n ℝ}
    (hT : (hermitianPart A).PosDef) (x : n → ℝ) :
    (A *ᵥ x) ⬝ᵥ (A *ᵥ x) ≤ (‖hermitianPart A‖
        + ‖(A - hermitianPart A) * (hermitianPart A)⁻¹ * (A - hermitianPart A)‖) *
      (x ⬝ᵥ (A *ᵥ x)) := by
  obtain ⟨hq, -, hnorm⟩ := growth_aux hT x
  have hq0 : 0 ≤ x ⬝ᵥ (hermitianPart A *ᵥ x) := by
    simpa using hT.posSemidef.dotProduct_mulVec_nonneg x
  rw [hq]
  exact (dotProduct_mulVec_self_le_of_posDef hT A x).trans
    (mul_le_mul_of_nonneg_right hnorm hq0)

/-- **The growth bound behind Theorem 4.2.6** of [golub2013matrix], for the transpose. Let
$A \in \mathbb{R}^{n \times n}$ have a positive definite symmetric part $T = (A + A^T)/2$, and
let $S = A - T$ be its skew part. Then for every $x \in \mathbb{R}^n$, in the spectral norm,
$$\|A^T x\|^2 \le \bigl(\|T\|_2 + \|S T^{-1} S\|_2\bigr) \, x^T A x.$$

The proof uses $A^T T^{-1} A = T - S T^{-1} S$. -/
theorem dotProduct_transpose_mulVec_self_le_of_posDef_hermitianPart {A : Matrix n n ℝ}
    (hT : (hermitianPart A).PosDef) (x : n → ℝ) :
    (Aᵀ *ᵥ x) ⬝ᵥ (Aᵀ *ᵥ x) ≤ (‖hermitianPart A‖
        + ‖(A - hermitianPart A) * (hermitianPart A)⁻¹ * (A - hermitianPart A)‖) *
      (x ⬝ᵥ (A *ᵥ x)) := by
  obtain ⟨hq, hG, hnorm⟩ := growth_aux hT x
  have hq0 : 0 ≤ x ⬝ᵥ (hermitianPart A *ᵥ x) := by
    simpa using hT.posSemidef.dotProduct_mulVec_nonneg x
  rw [hq]
  have h := dotProduct_mulVec_self_le_of_posDef hT Aᵀ x
  rw [← hG] at h
  exact h.trans (mul_le_mul_of_nonneg_right hnorm hq0)

end UnsymmetricLU

section UnsymmetricLUGrowth

open scoped Matrix.Norms.Frobenius

/-- **Theorem 4.2.6** of [golub2013matrix] (the growth of $|L| |U|$ for a positive definite
symmetric part). Let $A \in \mathbb{R}^{n \times n}$ have a positive definite symmetric part
$T = (A + A^T)/2$, let $S = A - T$, and let $A = LU$ be an LU factorization. Then
$$\bigl\| |L| \, |U| \bigr\|_F \le n \bigl(\|T\|_2 + \|S T^{-1} S\|_2\bigr),$$
where $|L|$ and $|U|$ are the matrices of the absolute values of the entries. The source takes
this result from G. H. Golub and C. F. Van Loan, *Unsymmetric positive definite linear systems*,
Linear Algebra Appl. 28 (1979) 85–97.

The product is $|L| |U| = \sum_k |\ell_k| |u_k^T|$, where $\ell_k$ is the $k$-th column of $L$
and $u_k^T$ the $k$-th row of $U$. With $y$ the $k$-th row of $L^{-1}$ and $x$ the $k$-th column
of $U^{-1}$, $u_k = A^T y$, $\ell_k = A x$, $y^T A y = u_{kk}$ and $x^T A x = 1/u_{kk}$. So
`Matrix.dotProduct_mulVec_self_le_of_posDef_hermitianPart` gives $\|\ell_k\| \|u_k\| \le
\|T\|_2 + \|S T^{-1} S\|_2$ for each of the $n$ terms. The norm of $|L| |U|$ is the Frobenius
norm, so the spectral norms are written with `Matrix.toEuclideanCLM`
(`Matrix.l2_opNorm_toEuclideanCLM`), because the two scoped matrix norms cannot be open
together. The matrix $|L|$ is `Matrix.abs L`. -/
theorem IsLU.frobenius_norm_abs_mul_abs_le {A L U : Matrix n n ℝ}
    (hT : (hermitianPart A).PosDef) (h : IsLU A L U) :
    ‖L.abs * U.abs‖ ≤ Fintype.card n * (‖toEuclideanCLM (𝕜 := ℝ) (hermitianPart A)‖
      + ‖toEuclideanCLM (𝕜 := ℝ) ((A - hermitianPart A) * (hermitianPart A)⁻¹
        * (A - hermitianPart A))‖) := by
  set a := ‖toEuclideanCLM (𝕜 := ℝ) (hermitianPart A)‖
  set b := ‖toEuclideanCLM (𝕜 := ℝ) ((A - hermitianPart A) * (hermitianPart A)⁻¹
        * (A - hermitianPart A))‖
  set c := a + b
  have hc0 : 0 ≤ c := add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hPA : ∀ v : n → ℝ, (A *ᵥ v) ⬝ᵥ (A *ᵥ v) ≤ c * (v ⬝ᵥ (A *ᵥ v)) := fun v => by
    have := dotProduct_mulVec_self_le_of_posDef_hermitianPart hT v
    rwa [← l2_opNorm_toEuclideanCLM, ← l2_opNorm_toEuclideanCLM] at this
  have hPAt : ∀ v : n → ℝ, (Aᵀ *ᵥ v) ⬝ᵥ (Aᵀ *ᵥ v) ≤ c * (v ⬝ᵥ (A *ᵥ v)) := fun v => by
    have := dotProduct_transpose_mulVec_self_le_of_posDef_hermitianPart hT v
    rwa [← l2_opNorm_toEuclideanCLM, ← l2_opNorm_toEuclideanCLM] at this
  have hL := h.isUnitLowerTriangular
  have hLi := hL.inv
  have hLL : L⁻¹ * L = 1 := nonsing_inv_mul L ((isUnit_iff_isUnit_det L).1 hL.isUnit)
  have hLU : L⁻¹ * A = U := by rw [← h.mul_eq, ← Matrix.mul_assoc, hLL, Matrix.one_mul]
  -- the pivots `u_kk = yᵀ A y` with `y` the `k`-th row of `L⁻¹`
  have hyA : ∀ k, (fun j => L⁻¹ k j) ᵥ* A = fun j => U k j := fun k => by
    funext j
    rw [← hLU, Matrix.mul_apply]
    rfl
  have hyAy : ∀ k, (fun j => L⁻¹ k j) ⬝ᵥ (A *ᵥ fun j => L⁻¹ k j) = U k k := fun k => by
    rw [dotProduct_mulVec, hyA k, dotProduct, Finset.sum_eq_single k]
    · rw [hLi.diag_eq_one, mul_one]
    · intro j _ hjk
      rcases lt_or_gt_of_ne hjk with hj | hj
      · rw [h.isUpperTriangular hj, zero_mul]
      · rw [hLi.isLowerTriangular (OrderDual.toDual_lt_toDual.2 hj), mul_zero]
    · simp
  have hsym : ∀ v : n → ℝ, v ⬝ᵥ (A *ᵥ v) = v ⬝ᵥ (hermitianPart A *ᵥ v) := fun v => by
    have e : v ⬝ᵥ (Aᵀ *ᵥ v) = v ⬝ᵥ (A *ᵥ v) := by
      rw [mulVec_transpose, dotProduct_comm, ← dotProduct_mulVec]
    rw [hermitianPart, conjTranspose_eq_transpose_of_trivial, smul_mulVec, add_mulVec,
      dotProduct_smul, dotProduct_add, e, smul_eq_mul]
    ring
  have hpos : ∀ k, 0 < U k k := fun k => by
    rw [← hyAy k]
    have hy : (fun j => L⁻¹ k j) ≠ 0 := fun h0 => by
      have := congrFun h0 k
      simp [hLi.diag_eq_one] at this
    have h1 := (posDef_iff_dotProduct_mulVec.1 hT).2 hy
    rw [hsym]
    simpa using h1
  -- the rows of `U`
  have hrow : ∀ k, (fun j => U k j) ⬝ᵥ (fun j => U k j) ≤ c * U k k := fun k => by
    have := hPAt fun j => L⁻¹ k j
    rwa [mulVec_transpose, hyA k, hyAy k] at this
  -- the columns of `L`, through the columns of `U⁻¹`
  have hUu : IsUnit U.det := by
    rw [det_of_isUpperTriangular h.isUpperTriangular]
    exact (Finset.prod_pos fun k _ => hpos k).ne'.isUnit
  have hUU : U * U⁻¹ = 1 := mul_nonsing_inv U hUu
  have hUi := h.isUpperTriangular.inv
  have hUkk : ∀ k, U⁻¹ k k = (U k k)⁻¹ := fun k => by
    have := congrFun (congrFun hUU k) k
    rw [h.isUpperTriangular.mul_apply_self hUi, one_apply_eq] at this
    exact eq_inv_of_mul_eq_one_right this
  have hAx : ∀ k, A *ᵥ (fun i => U⁻¹ i k) = fun i => L i k := fun k => by
    funext i
    rw [← h.mul_eq, ← mulVec_mulVec]
    have hUx : U *ᵥ (fun i => U⁻¹ i k) = fun i => (1 : Matrix n n ℝ) i k := by
      funext i'
      rw [← hUU, Matrix.mul_apply]
      rfl
    rw [hUx]
    simp [mulVec, dotProduct, Matrix.one_apply]
  have hxAx : ∀ k, (fun i => U⁻¹ i k) ⬝ᵥ (A *ᵥ fun i => U⁻¹ i k) = (U k k)⁻¹ := fun k => by
    rw [hAx k, dotProduct, Finset.sum_eq_single k]
    · rw [hL.diag_eq_one, mul_one, hUkk]
    · intro i _ hik
      rcases lt_or_gt_of_ne hik with hi | hi
      · rw [hL.isLowerTriangular (OrderDual.toDual_lt_toDual.2 hi), mul_zero]
      · rw [hUi hi, zero_mul]
    · simp
  have hcol : ∀ k, (fun i => L i k) ⬝ᵥ (fun i => L i k) ≤ c * (U k k)⁻¹ := fun k => by
    have := hPA fun i => U⁻¹ i k
    rwa [hxAx k, hAx k] at this
  -- each rank-one term has norm at most `c`
  have hnorm : ∀ v : n → ℝ, ‖WithLp.toLp 2 (fun i => |v i|)‖ = √(v ⬝ᵥ v) := fun v => by
    rw [EuclideanSpace.norm_eq, dotProduct]
    simp [sq]
  have hterm : ∀ k, ‖WithLp.toLp 2 (fun i => |L i k|)‖ * ‖WithLp.toLp 2 (fun j => |U k j|)‖
      ≤ c := fun k => by
    have hdot : ∀ v : n → ℝ, 0 ≤ v ⬝ᵥ v := fun v => by simpa using dotProduct_star_self_nonneg v
    rw [hnorm (fun i => L i k), hnorm (fun j => U k j), ← Real.sqrt_mul (hdot _)]
    calc √(((fun i => L i k) ⬝ᵥ fun i => L i k) * ((fun j => U k j) ⬝ᵥ fun j => U k j))
        ≤ √((c * (U k k)⁻¹) * (c * U k k)) :=
          Real.sqrt_le_sqrt (mul_le_mul (hcol k) (hrow k) (hdot _)
            (mul_nonneg hc0 (inv_nonneg.2 (hpos k).le)))
      _ = c := by
          rw [show c * (U k k)⁻¹ * (c * U k k) = c ^ 2 by field_simp [(hpos k).ne']]
          exact Real.sqrt_sq hc0
  -- the outer-product expansion of `|L| |U|`
  have hsum : L.abs * U.abs = ∑ k, vecMulVec (fun i => |L i k|) (fun j => |U k j|) := by
    ext i j
    simp [Matrix.mul_apply, Matrix.abs, vecMulVec_apply, Matrix.sum_apply]
  have hvmv : ∀ u v : n → ℝ, ‖vecMulVec u v‖ ≤ ‖WithLp.toLp 2 u‖ * ‖WithLp.toLp 2 v‖ :=
    fun u v => by
      rw [vecMulVec_eq Unit]
      refine (frobenius_norm_mul _ _).trans (le_of_eq ?_)
      rw [frobenius_norm_replicateCol, frobenius_norm_replicateRow]
  rw [hsum]
  calc ‖∑ k, vecMulVec (fun i => |L i k|) (fun j => |U k j|)‖
      ≤ ∑ k, ‖vecMulVec (fun i => |L i k|) (fun j => |U k j|)‖ := norm_sum_le _ _
    _ ≤ ∑ _k : n, c := Finset.sum_le_sum fun k _ => (hvmv _ _).trans (hterm k)
    _ = Fintype.card n * c := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end UnsymmetricLUGrowth

end Matrix
