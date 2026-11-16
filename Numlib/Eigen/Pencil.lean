/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Numlib.Eigen.Normal
import Numlib.LinearAlgebra.Matrix.Complexify
import Numlib.LinearAlgebra.Matrix.PosDef
import Numlib.LinearAlgebra.Matrix.QR
import Numlib.LinearAlgebra.Matrix.Schur

/-!
# Matrix pencils and the generalized eigenvalue problem

Let $A, B$ be square matrices of order $n$. The **matrix pencil** $(A, B)$ is the family $A - zB$ of
matrices, and the **generalized eigenvalue problem** asks for a scalar $\mu$ and a vector $x \neq 0$
with $Ax = \mu Bx$. Its finite eigenvalues form the set $\sigma(A, B) = \{\mu \mid \det(A - \mu B) =
0\}$, the roots of the characteristic polynomial $p_{A,B}(z) = \det(A - zB)$ of degree at most $n$.
The pencil is **regular** if $p_{A,B} \neq 0$. For $B = I$ the problem is the standard eigenvalue
problem, and for invertible $B$ it is the standard problem for $B^{-1}A$. The presentation follows
[quarteroni2000numerical], §5.9 and display (5.58); see also §7.7 of [golub2013matrix] and Chapter 9
of [saad2011numerical].

The file proves the **generalized Schur decomposition**: over $\mathbb{C}$, a regular pencil has
unitary $U, Z$ with $U^H A Z$ and $U^H B Z$ upper triangular, and the eigenvalues are the ratios
$t_{ii} / s_{ii}$ of the diagonal entries with $s_{ii} \neq 0$. A **symmetric-definite** pencil,
with $A$ Hermitian and $B$ positive definite, is simultaneously diagonalized by a congruence,
$M^H B M = I$ and $M^H A M$ real diagonal, so its eigenvalues are real. For real symmetric $A$ and
symmetric positive definite $P$, the eigenvalues of the preconditioned matrix $P^{-1} A$ are the
eigenvalues of the pencil $(A, P)$; they are real and are enclosed by the bounds of the generalized
Rayleigh quotient $(Ax, x) / (Px, x)$ ([quarteroni2000numerical], Remark 4.2 and (4.33)).

## Main definitions

* `Matrix.pencilPoly`: the characteristic polynomial $\det(A - XB)$ of the pencil, over any
  commutative ring.
* `Matrix.IsRegularPencil`: the pencil is regular if its characteristic polynomial is not the zero
  polynomial.
* `Matrix.pencilInftyMultiplicity`: the multiplicity $n - \deg p_{A,B}$ of the eigenvalue $\infty$.
* `Matrix.pencilSpectrum`: the set $\sigma(A, B)$ of finite eigenvalues, over a field.
* `Matrix.HasPencilEigenvector`: $x \neq 0$ and $Ax = \mu Bx$.
* `Matrix.IsDeflatingSubspace`: a subspace $S$ with $\dim(AS + BS) \le \dim S$ ([golub2013matrix],
  §7.7.8).

## Main results

* `Matrix.mem_pencilSpectrum_iff_exists`, `Matrix.mem_pencilSpectrum_iff_isRoot`:
  $\mu \in \sigma(A, B)$ if and only if $\mu$ has an eigenvector, and if and only if $\mu$ is a root
  of $p_{A,B}$.
* `Matrix.pencilSpectrum_one`, `Matrix.pencilSpectrum_eq_spectrum_of_isUnit`:
  $\sigma(A, I) = \sigma(A)$, and $\sigma(A, B) = \sigma(B^{-1} A)$ for invertible $B$.
* `Matrix.natDegree_pencilPoly_eq_card_iff`: $p_{A,B}$ has degree $n$ if and only if $B$ is
  invertible.
* `Matrix.pencilSpectrum_eq_univ_of_not_isRegularPencil`: every scalar is an eigenvalue of a
  singular pencil.
* `Matrix.exists_unitary_pencil_isUpperTriangular`: the generalized Schur decomposition of a regular
  pencil over $\mathbb{C}$.
* `Matrix.pencilSpectrum_eq_of_isUpperTriangular`: for upper triangular $T, S$,
  $\mu \in \sigma(T, S)$ if and only if $t_{ii} = \mu s_{ii}$ for some $i$.
* `Matrix.spectrum_inv_mul_subset_of_posDef`: if $l_{\min} (Px, x) \le (Ax, x) \le l_{\max} (Px, x)$
  for all real $x$, the eigenvalues of $P^{-1}A$ are real and lie in $[l_{\min}, l_{\max}]$.
* `Matrix.spectrum_inv_mul_subset_Icc_div`: $\lambda_{\min}(A) / \lambda_{\max}(P) \le \lambda \le
  \lambda_{\max}(A) / \lambda_{\min}(P)$ for the eigenvalues $\lambda$ of $P^{-1}A$.
* `Matrix.hasPencilEigenvector_col_of_conj_diagonal`,
  `Matrix.pencilSpectrum_eq_range_of_conj_diagonal`: if $X^H P X = \operatorname{diag}(a)$ and
  $X^H Q X = \operatorname{diag}(b)$ with $X$ invertible, the columns of $X$ are eigenvectors of
  $(P, Q)$ and the eigenvalues are the ratios $a_k / b_k$ ([golub2013matrix], §8.7.4).
* `Matrix.exists_simultaneous_diagonalization`: a symmetric-definite pencil has an invertible $M$
  with $M^H B M = I$ and $M^H A M = \operatorname{diag}(d)$, $d$ real, and $\sigma(A, B) = \{d_i\}$
  ([quarteroni2000numerical], Theorem 5.7).
* `Matrix.pencilSpectrum_subset_range_ofReal_of_posDef`,
  `Matrix.re_pos_of_mem_pencilSpectrum_of_posDef`: the eigenvalues of a symmetric-definite pencil
  are real, and they are positive when $A$ is positive definite too.
* `Matrix.inv_mem_pencilSpectrum_swap`: if $\mu \neq 0$ is an eigenvalue of $(A, B)$, then
  $\mu^{-1}$ is an eigenvalue of $(B, A)$ ([golub2013matrix], §7.7.1).
* `Matrix.isDeflatingSubspace_one_iff`: a deflating subspace of $(A, I)$ is an invariant subspace of
  $A$.
* `Matrix.isDeflatingSubspace_span_cols_of_isUpperTriangular`: the leading columns of the right
  factor of a generalized Schur decomposition span deflating subspaces.

## Proof outline

For the generalized Schur decomposition, regularity gives a scalar $\mu_0$ with $A_0 = A - \mu_0 B$
invertible. A Schur form $A_0^{-1} B = Z T_0 Z^H$ and a QR factorization $A_0 Z = U S_0$ give
$U^H B Z = S_0 T_0$ and $U^H A Z = S_0 + \mu_0 S_0 T_0$, both upper triangular. For the simultaneous
diagonalization, the unitary eigenbasis of $B$ scaled by the inverse square roots of the eigenvalues
of $B$ is a matrix $W$ with $W^H B W = I$, and the spectral theorem for the Hermitian matrix
$W^H A W$ gives the rest. No Cholesky factor is used. For the real pencil $(A, P)$, an eigenvector
equation $Ax = \mu Px$ over $\mathbb{C}$ gives $\mu = x^H A x / x^H P x$, the quotient of a real
number by a positive real number.

## Implementation notes

* The generalized Schur decomposition reduces to the Schur form of one matrix
  (`Numlib.LinearAlgebra.Matrix.Schur`) and to one QR factorization
  (`Numlib.LinearAlgebra.Matrix.QR`).
* The statements about $P^{-1} A$ use the Hermitian form of the complexification
  (`Matrix.star_dotProduct_complexify_mulVec_of_isHermitian`), and not the operator of the $P$-inner
  product of `Numlib.Krylov.Preconditioned`. The real matrices act on complex vectors through
  `Matrix.complexify`.
* The ordered eigenvalues of a symmetric-definite pencil, their min–max characterization and their
  perturbation theory are in `Numlib.Eigen.SymmetricPencil`.
-/

open Polynomial

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### The characteristic polynomial of a pencil -/

section Ring

variable {R : Type*} [CommRing R]

/-- The **characteristic polynomial** of the pencil $(A, B)$ of matrices over a commutative ring $R$
is $p_{A,B}(X) = \det(A - XB) \in R[X]$ ([quarteroni2000numerical], §5.9).

The matrices are mapped entrywise into $R[X]$ by `Polynomial.C`. -/
noncomputable def pencilPoly (A B : Matrix n n R) : R[X] :=
  (A.map C - (X : R[X]) • B.map C).det

/-- The characteristic polynomial of the pencil is $\det(X(-B) + A)$, the form that Mathlib's lemmas
on degrees and coefficients use. -/
private theorem pencilPoly_eq_det_X_smul_add (A B : Matrix n n R) :
    pencilPoly A B = ((X : R[X]) • (-B).map C + A.map C).det := by
  rw [pencilPoly, Matrix.map_neg _ (map_neg C), smul_neg, ← sub_eq_neg_add]

/-- For every $\mu \in R$, the evaluation of the characteristic polynomial of the pencil at $\mu$ is
$p_{A,B}(\mu) = \det(A - \mu B)$. -/
theorem pencilPoly_eval (A B : Matrix n n R) (μ : R) :
    (pencilPoly A B).eval μ = (A - μ • B).det := by
  rw [pencilPoly, ← coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, map_apply, Matrix.sub_apply, Matrix.smul_apply,
    coe_evalRingHom, eval_sub, eval_C, eval_mul, eval_X, smul_eq_mul, Matrix.smul_apply]

/-- For $B = I$, the characteristic polynomial of the pencil is $p_{A,I} = (-1)^n \chi_A$, where
$\chi_A = \det(XI - A)$ is the characteristic polynomial of $A$ and $n$ is the order of $A$. -/
theorem pencilPoly_one (A : Matrix n n R) :
    pencilPoly A 1 = (-1) ^ Fintype.card n * A.charpoly := by
  rw [charpoly, ← det_neg, pencilPoly]
  congr 1
  ext i j
  simp [charmatrix_apply, Matrix.one_apply, diagonal_apply]

/-- The characteristic polynomial of a pencil of order $n$ has degree at most $n$. -/
theorem natDegree_pencilPoly_le (A B : Matrix n n R) :
    (pencilPoly A B).natDegree ≤ Fintype.card n := by
  rw [pencilPoly_eq_det_X_smul_add]
  exact natDegree_det_X_add_C_le _ _

/-- The coefficient of $X^n$ in the characteristic polynomial of a pencil of order $n$ is
$(-1)^n \det B$.

It follows that $p_{A,B}$ has degree $n$ if and only if $B$ is invertible
(`Matrix.natDegree_pencilPoly_eq_card_iff`). -/
theorem coeff_pencilPoly_card (A B : Matrix n n R) :
    (pencilPoly A B).coeff (Fintype.card n) = (-1) ^ Fintype.card n * B.det := by
  rw [pencilPoly_eq_det_X_smul_add, coeff_det_X_add_C_card, det_neg]

/-- A pencil $(A, B)$ is **regular** if its characteristic polynomial $\det(A - zB)$ is not the zero
polynomial, and **singular** otherwise ([quarteroni2000numerical], §5.9). -/
def IsRegularPencil (A B : Matrix n n R) : Prop := pencilPoly A B ≠ 0

/-- Let $R$ be a nontrivial commutative ring. If $\det B$ is a unit of $R$, then the pencil $(A, B)$
is regular.

The leading coefficient $(-1)^n \det B$ of $p_{A,B}$ is then a unit, so $p_{A,B} \neq 0$. -/
theorem isRegularPencil_of_isUnit [Nontrivial R] (A : Matrix n n R) {B : Matrix n n R}
    (hB : IsUnit B.det) : IsRegularPencil A B := by
  intro h
  have := coeff_pencilPoly_card A B
  rw [h, coeff_zero] at this
  exact hB.ne_zero (by simpa using this.symm)

/-- Over a nontrivial commutative ring, the pencil $(A, I)$ of the standard eigenvalue problem is
regular. -/
theorem isRegularPencil_one [Nontrivial R] (A : Matrix n n R) : IsRegularPencil A 1 :=
  isRegularPencil_of_isUnit A (by simp)

/-- The **multiplicity of the eigenvalue $\infty$** of the pencil $(A, B)$ of order $n$ is
$n - \deg p_{A,B}$, the number of roots that the characteristic polynomial lacks to have degree
$n$ ([quarteroni2000numerical], §5.9).

Over a field, the multiplicity is $0$ if and only if $B$ is invertible
(`Matrix.natDegree_pencilPoly_eq_card_iff`). The definition applies to every pencil. For a
singular pencil, $p_{A,B} = 0$ has degree $0$ in Mathlib, so the value is $n$. -/
noncomputable def pencilInftyMultiplicity (A B : Matrix n n R) : ℕ :=
  Fintype.card n - (pencilPoly A B).natDegree

end Ring

/-! ### The spectrum of a pencil over a field -/

section Field

variable {K : Type*} [Field K]

/-- The **spectrum** of the pencil $(A, B)$ over a field $K$ is the set of its finite generalized
eigenvalues, $\sigma(A, B) = \{\mu \in K \mid \det(A - \mu B) = 0\}$ ([quarteroni2000numerical],
§5.9). -/
def pencilSpectrum (A B : Matrix n n K) : Set K := {μ | (A - μ • B).det = 0}

/-- A scalar $\mu$ and a vector $x$ form an **eigenpair** of the pencil $(A, B)$ if $x \neq 0$ and
$Ax = \mu Bx$ ([quarteroni2000numerical], display (5.58)). -/
def HasPencilEigenvector (A B : Matrix n n K) (μ : K) (x : n → K) : Prop :=
  x ≠ 0 ∧ A *ᵥ x = μ • (B *ᵥ x)

/-- $\mu \in \sigma(A, B)$ if and only if $\det(A - \mu B) = 0$. -/
theorem mem_pencilSpectrum_iff_det {A B : Matrix n n K} {μ : K} :
    μ ∈ pencilSpectrum A B ↔ (A - μ • B).det = 0 := Iff.rfl

/-- $\mu \in \sigma(A, B)$ if and only if there is a vector $x$ such that $(\mu, x)$ is an eigenpair
of the pencil $(A, B)$, that is, $x \neq 0$ and $Ax = \mu Bx$. -/
theorem mem_pencilSpectrum_iff_exists (A B : Matrix n n K) (μ : K) :
    μ ∈ pencilSpectrum A B ↔ ∃ x, HasPencilEigenvector A B μ x := by
  rw [mem_pencilSpectrum_iff_det, ← Matrix.exists_mulVec_eq_zero_iff]
  simp only [HasPencilEigenvector, sub_mulVec, smul_mulVec, sub_eq_zero]

/-- $\mu \in \sigma(A, B)$ if and only if $\mu$ is a root of the characteristic polynomial
$p_{A,B}$. -/
theorem mem_pencilSpectrum_iff_isRoot (A B : Matrix n n K) (μ : K) :
    μ ∈ pencilSpectrum A B ↔ (pencilPoly A B).IsRoot μ := by
  rw [mem_pencilSpectrum_iff_det, IsRoot.def, pencilPoly_eval]

/-- The spectrum of the pencil $(A, I)$ is the spectrum of $A$: $\sigma(A, I) = \sigma(A)$. -/
theorem pencilSpectrum_one (A : Matrix n n K) : pencilSpectrum A 1 = spectrum K A := by
  ext μ
  rw [mem_pencilSpectrum_iff_exists, mem_spectrum_iff_exists_mulVec_eq_smul]
  simp [HasPencilEigenvector]

/-- If $B$ is invertible, then $\sigma(A, B) = \sigma(B^{-1} A)$ ([quarteroni2000numerical],
§5.9.1).

The source writes the reduced problem as $Cx = \lambda x$ with $BC = A$. -/
theorem pencilSpectrum_eq_spectrum_of_isUnit (A : Matrix n n K) {B : Matrix n n K}
    (hB : IsUnit B) : pencilSpectrum A B = spectrum K (B⁻¹ * A) := by
  have hBd := (isUnit_iff_isUnit_det B).mp hB
  ext μ
  rw [mem_pencilSpectrum_iff_exists, mem_spectrum_iff_exists_mulVec_eq_smul]
  refine exists_congr fun x => and_congr_right' ⟨fun h => ?_, fun h => ?_⟩
  · rw [← mulVec_mulVec, h, mulVec_smul, mulVec_mulVec, nonsing_inv_mul _ hBd, one_mulVec]
  · have h' := congrArg (B *ᵥ ·) h
    simpa [mulVec_mulVec, ← Matrix.mul_assoc, mul_nonsing_inv _ hBd, mulVec_smul] using h'

/-- The characteristic polynomial of a pencil of order $n$ has degree $n$ if and only if $\det B$ is
a unit, that is, if and only if $B$ is nonsingular ([quarteroni2000numerical], §5.9.1). Over an
algebraically closed field, the pencil thus has $n$ finite eigenvalues, counted with
multiplicity, exactly when $B$ is nonsingular. -/
theorem natDegree_pencilPoly_eq_card_iff (A B : Matrix n n K) :
    (pencilPoly A B).natDegree = Fintype.card n ↔ IsUnit B.det := by
  rw [isUnit_iff_ne_zero]
  constructor
  · intro h
    rcases Nat.eq_zero_or_pos (Fintype.card n) with hn | hn
    · have : IsEmpty n := Fintype.card_eq_zero_iff.mp hn
      simp
    · have hne : pencilPoly A B ≠ 0 := fun h0 => by
        rw [h0, natDegree_zero] at h
        omega
      have := leadingCoeff_ne_zero.mpr hne
      rw [leadingCoeff, h, coeff_pencilPoly_card] at this
      exact right_ne_zero_of_mul this
  · intro h
    refine le_antisymm (natDegree_pencilPoly_le A B) (le_natDegree_of_ne_zero ?_)
    rw [coeff_pencilPoly_card]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) h

/-- If the pencil $(A, B)$ is not regular, then every scalar is an eigenvalue: $\sigma(A, B) = K$
([quarteroni2000numerical], Example 5.14, the third pencil). -/
theorem pencilSpectrum_eq_univ_of_not_isRegularPencil {A B : Matrix n n K}
    (h : ¬ IsRegularPencil A B) : pencilSpectrum A B = Set.univ := by
  rw [IsRegularPencil, not_not] at h
  ext μ
  simp [mem_pencilSpectrum_iff_isRoot, h]

/-- A regular pencil has only finitely many eigenvalues, because they are the roots of a nonzero
polynomial. -/
theorem IsRegularPencil.finite_pencilSpectrum {A B : Matrix n n K} (h : IsRegularPencil A B) :
    (pencilSpectrum A B).Finite := by
  convert finite_setOfPred_isRoot h using 1
  ext μ
  exact mem_pencilSpectrum_iff_isRoot A B μ

/-- Let $K$ be an infinite field. If the pencil $(A, B)$ is regular, then there is a scalar
$\mu_0 \in K$ such that $A - \mu_0 B$ is invertible.

This is the first step of the proof of the generalized Schur decomposition
`Matrix.exists_unitary_pencil_isUpperTriangular`. -/
theorem IsRegularPencil.exists_isUnit_sub_smul [Infinite K] {A B : Matrix n n K}
    (h : IsRegularPencil A B) : ∃ μ₀ : K, IsUnit (A - μ₀ • B) := by
  obtain ⟨μ₀, hμ₀⟩ := h.finite_pencilSpectrum.exists_notMem
  exact ⟨μ₀, (isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hμ₀)⟩

/-- If $U$ and $Z$ are invertible, then $\sigma(UAZ, UBZ) = \sigma(A, B)$, because $\det(U(A - \mu
B)Z) = \det U \cdot \det(A - \mu B) \cdot \det Z$. -/
theorem pencilSpectrum_mul_mul_of_isUnit (A B : Matrix n n K) {U Z : Matrix n n K}
    (hU : IsUnit U) (hZ : IsUnit Z) :
    pencilSpectrum (U * A * Z) (U * B * Z) = pencilSpectrum A B := by
  have hUd := (isUnit_iff_isUnit_det U).mp hU
  have hZd := (isUnit_iff_isUnit_det Z).mp hZ
  ext μ
  have : U * A * Z - μ • (U * B * Z) = U * (A - μ • B) * Z := by
    simp [Matrix.mul_sub, Matrix.sub_mul]
  rw [mem_pencilSpectrum_iff_det, mem_pencilSpectrum_iff_det, this, det_mul, det_mul,
    mul_eq_zero, mul_eq_zero]
  simp [hUd.ne_zero, hZd.ne_zero]

/-- For $d, e \in K^n$, the spectrum of the pencil of the diagonal matrices $\operatorname{diag}(d)$
and $\operatorname{diag}(e)$ is $\{\mu \mid d_i = \mu e_i \text{ for some } i\}$. -/
theorem pencilSpectrum_diagonal (d e : n → K) :
    pencilSpectrum (diagonal d) (diagonal e) = {μ | ∃ i, d i = μ * e i} := by
  ext μ
  rw [mem_pencilSpectrum_iff_det, smul_eq_diagonal_mul, diagonal_mul_diagonal, diagonal_sub,
    det_diagonal, Finset.prod_eq_zero_iff]
  simp [sub_eq_zero]

variable [LinearOrder n]

/-- If $T$ and $S$ are upper triangular, then the characteristic polynomial of the pencil $(T, S)$
is the product of the diagonal pencils:
$$p_{T,S}(X) = \prod_i (t_{ii} - X s_{ii}).$$
-/
theorem pencilPoly_of_isUpperTriangular {T S : Matrix n n K} (hT : T.IsUpperTriangular)
    (hS : S.IsUpperTriangular) :
    pencilPoly T S = ∏ i, (C (T i i) - X * C (S i i)) := by
  rw [pencilPoly, det_of_isUpperTriangular]
  · simp
  · intro i j hij
    simp [hT hij, hS hij]

/-- Let $T$ and $S$ be upper triangular. Then $\mu \in \sigma(T, S)$ if and only if
$t_{ii} = \mu s_{ii}$ for some $i$.

Thus each index $i$ with $s_{ii} \neq 0$ gives the eigenvalue $t_{ii} / s_{ii}$. An index with
$s_{ii} = 0$ and $t_{ii} \neq 0$ gives no finite eigenvalue; it gives the eigenvalue $\infty$ of
[quarteroni2000numerical], Property 5.10. An index with $s_{ii} = t_{ii} = 0$ makes every scalar
an eigenvalue. -/
theorem pencilSpectrum_eq_of_isUpperTriangular {T S : Matrix n n K} (hT : T.IsUpperTriangular)
    (hS : S.IsUpperTriangular) :
    pencilSpectrum T S = {μ | ∃ i, T i i = μ * S i i} := by
  ext μ
  rw [mem_pencilSpectrum_iff_isRoot, pencilPoly_of_isUpperTriangular hT hS, IsRoot.def,
    eval_prod, Finset.prod_eq_zero_iff]
  simp only [Finset.mem_univ, true_and, eval_sub, eval_C, eval_mul, eval_X, sub_eq_zero,
    Set.mem_ofPred_eq]

end Field

/-!
### The real symmetric-definite pencil in the preconditioned form

For real matrices $A$ and $P$, the eigenvalues of the preconditioned matrix $P^{-1} A$ are the
eigenvalues of the pencil $(A, P)$.
-/

section Real

open scoped ComplexOrder

/-- Let $A, P \in \mathbb{R}^{n \times n}$ with $P$ invertible, and let $\mu \in \mathbb{C}$. Then
$\mu$ is an eigenvalue of $P^{-1} A$ if and only if there is a vector $x \in \mathbb{C}^n$ with
$x \neq 0$ and $Ax = \mu Px$ ([quarteroni2000numerical], Remark 4.2, display (4.32)).

The real matrices act on $\mathbb{C}^n$ through `Matrix.complexify`, and the spectrum is the
complex spectrum of the complexification of $P^{-1} A$. -/
theorem mem_spectrum_inv_mul_iff_exists_mulVec_eq_smul (A : Matrix n n ℝ) {P : Matrix n n ℝ}
    (hP : IsUnit P) (μ : ℂ) :
    μ ∈ spectrum ℂ (complexify (P⁻¹ * A)) ↔
      ∃ x : n → ℂ, x ≠ 0 ∧ complexify A *ᵥ x = μ • (complexify P *ᵥ x) := by
  rw [complexify_mul, complexify_inv,
    ← pencilSpectrum_eq_spectrum_of_isUnit _ ((isUnit_complexify_iff P).mpr hP),
    mem_pencilSpectrum_iff_exists]
  rfl

omit [DecidableEq n] in
/-- Let $A \in \mathbb{R}^{n \times n}$ be symmetric and $P \in \mathbb{R}^{n \times n}$ be positive
definite; if $Ax = \mu Px$ for a complex $x \neq 0$, then $\mu = (a_1 + a_2) / (p_1 + p_2)$ is
real, where $a_1, a_2$ and $p_1, p_2$ are the quadratic forms of $A$ and of $P$ at the real and
the imaginary parts of $x$, and $p_1 + p_2 > 0$. -/
private theorem eq_ofReal_div_of_mulVec_eq_smul {A P : Matrix n n ℝ} (hA : A.IsHermitian)
    (hP : P.PosDef) {μ : ℂ} {x : n → ℂ} (hx : x ≠ 0)
    (hμ : complexify A *ᵥ x = μ • (complexify P *ᵥ x)) :
    let xr : n → ℝ := fun i => (x i).re
    let xi : n → ℝ := fun i => (x i).im
    0 < xr ⬝ᵥ (P *ᵥ xr) + xi ⬝ᵥ (P *ᵥ xi) ∧
      μ = ((xr ⬝ᵥ (A *ᵥ xr) + xi ⬝ᵥ (A *ᵥ xi)) / (xr ⬝ᵥ (P *ᵥ xr) + xi ⬝ᵥ (P *ᵥ xi)) : ℝ) := by
  intro xr xi
  have hform := congrArg (star x ⬝ᵥ ·) hμ
  simp only [dotProduct_smul, star_dotProduct_complexify_mulVec_of_isHermitian hA,
    star_dotProduct_complexify_mulVec_of_isHermitian hP.1] at hform
  have hpos : (0 : ℂ) < star x ⬝ᵥ (complexify P *ᵥ x) :=
    (posDef_complexify_iff.mpr hP).dotProduct_mulVec_pos hx
  rw [star_dotProduct_complexify_mulVec_of_isHermitian hP.1, Complex.zero_lt_real] at hpos
  refine ⟨hpos, ?_⟩
  rw [Complex.ofReal_div, hform, smul_eq_mul, mul_div_cancel_right₀]
  exact_mod_cast hpos.ne'

/-- **The spectrum of $P^{-1} A$ is real and bounded by the generalized Rayleigh quotient.** Let
$A \in \mathbb{R}^{n \times n}$ be symmetric, let $P \in \mathbb{R}^{n \times n}$ be positive
definite, and let $l_{\min}, l_{\max} \in \mathbb{R}$ satisfy
$$l_{\min} (Px, x) \le (Ax, x) \le l_{\max} (Px, x) \qquad \text{for all } x \in \mathbb{R}^n.$$
Then every complex eigenvalue of $P^{-1} A$ is a real number in $[l_{\min}, l_{\max}]$
([quarteroni2000numerical], Remark 4.2, in the form that Theorem 4.9 there uses).

Here $(y, x)$ is the real dot product, written `y ⬝ᵥ x`. An eigenvector equation $Ax = \mu Px$
over $\mathbb{C}$ gives $\mu = x^H A x / x^H P x$, and each Hermitian form is the sum of the
real quadratic forms at the real and the imaginary parts of $x$. -/
theorem spectrum_inv_mul_subset_of_posDef {A P : Matrix n n ℝ} (hA : A.IsHermitian)
    (hP : P.PosDef) {lmin lmax : ℝ}
    (hlo : ∀ x : n → ℝ, lmin * (P *ᵥ x ⬝ᵥ x) ≤ A *ᵥ x ⬝ᵥ x)
    (hhi : ∀ x : n → ℝ, A *ᵥ x ⬝ᵥ x ≤ lmax * (P *ᵥ x ⬝ᵥ x)) :
    spectrum ℂ (complexify (P⁻¹ * A)) ⊆ Complex.ofReal '' Set.Icc lmin lmax := by
  intro μ hμ
  obtain ⟨x, hx, hμ⟩ := (mem_spectrum_inv_mul_iff_exists_mulVec_eq_smul A hP.isUnit μ).mp hμ
  obtain ⟨hpos, rfl⟩ := eq_ofReal_div_of_mulVec_eq_smul hA hP hx hμ
  refine ⟨_, ⟨?_, ?_⟩, rfl⟩
  · rw [le_div_iff₀ hpos, mul_add]
    have h1 := hlo fun i => (x i).re
    have h2 := hlo fun i => (x i).im
    simp only [dotProduct_comm _ (P *ᵥ _), dotProduct_comm _ (A *ᵥ _)] at h1 h2 ⊢
    linarith
  · rw [div_le_iff₀ hpos, mul_add]
    have h1 := hhi fun i => (x i).re
    have h2 := hhi fun i => (x i).im
    simp only [dotProduct_comm _ (P *ᵥ _), dotProduct_comm _ (A *ᵥ _)] at h1 h2 ⊢
    linarith

/-- Let $A \in \mathbb{R}^{n \times n}$ be symmetric, let $P \in \mathbb{R}^{n \times n}$ be
positive definite, and let $c \in \mathbb{R}$ satisfy $c (Px, x) \le (Ax, x)$ for all
$x \in \mathbb{R}^n$. If $c (Px_0, x_0) = (Ax_0, x_0)$ for some $x_0 \neq 0$, then $c$ is a real
eigenvalue of $P^{-1} A$.

The matrix $A - cP$ is positive semidefinite and its quadratic form vanishes at $x_0$, so
$(A - cP) x_0 = 0$. This is how the hypotheses on the endpoints in [quarteroni2000numerical],
Theorem 4.9 are met. -/
theorem mem_spectrum_inv_mul_of_forall_mul_le_of_eq {A P : Matrix n n ℝ} (hA : A.IsHermitian)
    (hP : P.PosDef) {c : ℝ} (hlo : ∀ x : n → ℝ, c * (P *ᵥ x ⬝ᵥ x) ≤ A *ᵥ x ⬝ᵥ x)
    {x₀ : n → ℝ} (hx₀ : x₀ ≠ 0) (heq : c * (P *ᵥ x₀ ⬝ᵥ x₀) = A *ᵥ x₀ ⬝ᵥ x₀) :
    c ∈ spectrum ℝ (P⁻¹ * A) := by
  have hM : (A - c • P).PosSemidef := by
    refine PosSemidef.of_dotProduct_mulVec_nonneg (hA.sub (hP.1.smul (IsSelfAdjoint.all c)))
      fun x => ?_
    have := hlo x
    simp only [star_trivial, sub_mulVec, smul_mulVec, sub_dotProduct, smul_dotProduct,
      smul_eq_mul, dotProduct_comm x] at this ⊢
    linarith
  have h0 : (A - c • P) *ᵥ x₀ = 0 := by
    rw [← hM.dotProduct_mulVec_zero_iff]
    simp only [star_trivial, sub_mulVec, smul_mulVec, sub_dotProduct, smul_dotProduct,
      smul_eq_mul, dotProduct_comm x₀]
    linarith
  rw [← pencilSpectrum_eq_spectrum_of_isUnit _ hP.isUnit, mem_pencilSpectrum_iff_exists]
  refine ⟨x₀, hx₀, ?_⟩
  rwa [sub_mulVec, smul_mulVec, sub_eq_zero] at h0

/-- Let $A \in \mathbb{R}^{n \times n}$ be symmetric, let $P \in \mathbb{R}^{n \times n}$ be
positive definite, and let $c \in \mathbb{R}$ satisfy $(Ax, x) \le c (Px, x)$ for all
$x \in \mathbb{R}^n$. If $(Ax_0, x_0) = c (Px_0, x_0)$ for some $x_0 \neq 0$, then $c$ is a real
eigenvalue of $P^{-1} A$.

This is `Matrix.mem_spectrum_inv_mul_of_forall_mul_le_of_eq` applied to the pencil $(-A, P)$. -/
theorem mem_spectrum_inv_mul_of_forall_le_mul_of_eq {A P : Matrix n n ℝ} (hA : A.IsHermitian)
    (hP : P.PosDef) {c : ℝ} (hhi : ∀ x : n → ℝ, A *ᵥ x ⬝ᵥ x ≤ c * (P *ᵥ x ⬝ᵥ x))
    {x₀ : n → ℝ} (hx₀ : x₀ ≠ 0) (heq : A *ᵥ x₀ ⬝ᵥ x₀ = c * (P *ᵥ x₀ ⬝ᵥ x₀)) :
    c ∈ spectrum ℝ (P⁻¹ * A) := by
  have h := mem_spectrum_inv_mul_of_forall_mul_le_of_eq hA.neg hP (c := -c)
    (fun x => by have := hhi x; simp only [neg_mulVec, neg_dotProduct]; linarith) hx₀
    (by simp only [neg_mulVec, neg_dotProduct]; linarith)
  rw [Matrix.mul_neg, ← spectrum.neg_eq, Set.mem_neg] at h
  simpa using h

/-- **Enclosure of the spectrum of $P^{-1} A$ by the extreme eigenvalues.** Let
$A \in \mathbb{R}^{n \times n}$ be symmetric and $P \in \mathbb{R}^{n \times n}$ be positive
definite. Let $a, a', p, p' \in \mathbb{R}$ with $0 \le a$, $0 < p$ and $0 < p'$, and suppose
that for all $x \in \mathbb{R}^n$
$$a \|x\|^2 \le (Ax, x) \le a' \|x\|^2, \qquad p \|x\|^2 \le (Px, x) \le p' \|x\|^2.$$
Then every complex eigenvalue of $P^{-1} A$ is a real number in $[a / p', a' / p]$
([quarteroni2000numerical], (4.33)).

With $a, a'$ the extreme eigenvalues of $A$ and $p, p'$ those of $P$, this is the printed bound
$\lambda_{\min}(A) / \lambda_{\max}(P) \le \lambda \le \lambda_{\max}(A) / \lambda_{\min}(P)$.
Here $\|x\|^2$ is `x ⬝ᵥ x`. The form without the hypothesis $0 \le a$ is
`Matrix.spectrum_inv_mul_subset_Icc_min_div_max_div`. -/
theorem spectrum_inv_mul_subset_Icc_div {A P : Matrix n n ℝ} (hA : A.IsHermitian)
    (hP : P.PosDef) {a a' p p' : ℝ} (ha : 0 ≤ a) (hp : 0 < p) (hp' : 0 < p')
    (hAlo : ∀ x : n → ℝ, a * (x ⬝ᵥ x) ≤ A *ᵥ x ⬝ᵥ x)
    (hAhi : ∀ x : n → ℝ, A *ᵥ x ⬝ᵥ x ≤ a' * (x ⬝ᵥ x))
    (hPlo : ∀ x : n → ℝ, p * (x ⬝ᵥ x) ≤ P *ᵥ x ⬝ᵥ x)
    (hPhi : ∀ x : n → ℝ, P *ᵥ x ⬝ᵥ x ≤ p' * (x ⬝ᵥ x)) :
    spectrum ℂ (complexify (P⁻¹ * A)) ⊆ Complex.ofReal '' Set.Icc (a / p') (a' / p) := by
  rcases isEmpty_or_nonempty n with hn | ⟨⟨i⟩⟩
  · rw [spectrum.of_subsingleton]
    exact Set.empty_subset _
  have ha' : 0 ≤ a' := by
    have h1 := hAlo (Pi.single i 1)
    have h2 := hAhi (Pi.single i 1)
    have h3 : (Pi.single i (1 : ℝ)) ⬝ᵥ (Pi.single i 1) = 1 := by simp
    rw [h3] at h1 h2
    linarith
  refine spectrum_inv_mul_subset_of_posDef hA hP (fun x => ?_) fun x => ?_
  · calc a / p' * (P *ᵥ x ⬝ᵥ x) ≤ a / p' * (p' * (x ⬝ᵥ x)) := by
          gcongr; exact hPhi x
      _ = a * (x ⬝ᵥ x) := by field_simp
      _ ≤ A *ᵥ x ⬝ᵥ x := hAlo x
  · calc A *ᵥ x ⬝ᵥ x ≤ a' * (x ⬝ᵥ x) := hAhi x
      _ = a' / p * (p * (x ⬝ᵥ x)) := by field_simp
      _ ≤ a' / p * (P *ᵥ x ⬝ᵥ x) := by gcongr; exact hPlo x

/-- Let $A \in \mathbb{R}^{n \times n}$ be symmetric and $P \in \mathbb{R}^{n \times n}$ be positive
definite. Let $a, a', p, p' \in \mathbb{R}$ with $0 < p$ and $0 < p'$, and suppose that
$a \|x\|^2 \le (Ax, x) \le a' \|x\|^2$ and $p \|x\|^2 \le (Px, x) \le p' \|x\|^2$ for all
$x \in \mathbb{R}^n$. Then every complex eigenvalue of $P^{-1} A$ is a real number in
$$\left[\min\{a/p, a/p'\}, \max\{a'/p, a'/p'\}\right].$$

This is `Matrix.spectrum_inv_mul_subset_Icc_div` without a sign hypothesis on $a$. For
$0 \le a \le a'$ and $p \le p'$ the interval is $[a/p', a'/p]$; for $a \le 0 \le a'$ it is
$[a/p, a'/p]$; for $a' \le 0$ it is $[a/p, a'/p']$. -/
theorem spectrum_inv_mul_subset_Icc_min_div_max_div {A P : Matrix n n ℝ} (hA : A.IsHermitian)
    (hP : P.PosDef) {a a' p p' : ℝ} (hp : 0 < p) (hp' : 0 < p')
    (hAlo : ∀ x : n → ℝ, a * (x ⬝ᵥ x) ≤ A *ᵥ x ⬝ᵥ x)
    (hAhi : ∀ x : n → ℝ, A *ᵥ x ⬝ᵥ x ≤ a' * (x ⬝ᵥ x))
    (hPlo : ∀ x : n → ℝ, p * (x ⬝ᵥ x) ≤ P *ᵥ x ⬝ᵥ x)
    (hPhi : ∀ x : n → ℝ, P *ᵥ x ⬝ᵥ x ≤ p' * (x ⬝ᵥ x)) :
    spectrum ℂ (complexify (P⁻¹ * A)) ⊆
      Complex.ofReal '' Set.Icc (min (a / p) (a / p')) (max (a' / p) (a' / p')) := by
  have hPnn : ∀ x : n → ℝ, 0 ≤ P *ᵥ x ⬝ᵥ x := fun x => by
    have := hPlo x
    have := dotProduct_self_star_nonneg x
    simp only [star_trivial] at *
    nlinarith
  refine spectrum_inv_mul_subset_of_posDef hA hP (fun x => ?_) fun x => ?_
  · rcases le_or_gt 0 a with ha | ha
    · calc min (a / p) (a / p') * (P *ᵥ x ⬝ᵥ x) ≤ a / p' * (P *ᵥ x ⬝ᵥ x) := by
            gcongr
            · exact hPnn x
            · exact min_le_right _ _
        _ ≤ a / p' * (p' * (x ⬝ᵥ x)) := by gcongr; exact hPhi x
        _ = a * (x ⬝ᵥ x) := by field_simp
        _ ≤ A *ᵥ x ⬝ᵥ x := hAlo x
    · calc min (a / p) (a / p') * (P *ᵥ x ⬝ᵥ x) ≤ a / p * (P *ᵥ x ⬝ᵥ x) := by
            gcongr
            · exact hPnn x
            · exact min_le_left _ _
        _ ≤ a / p * (p * (x ⬝ᵥ x)) := by
            rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hp]
            exact mul_le_mul_of_nonpos_left (hPlo x) ha.le
        _ = a * (x ⬝ᵥ x) := by field_simp
        _ ≤ A *ᵥ x ⬝ᵥ x := hAlo x
  · rcases le_or_gt 0 a' with ha | ha
    · calc A *ᵥ x ⬝ᵥ x ≤ a' * (x ⬝ᵥ x) := hAhi x
        _ = a' / p * (p * (x ⬝ᵥ x)) := by field_simp
        _ ≤ a' / p * (P *ᵥ x ⬝ᵥ x) := by gcongr; exact hPlo x
        _ ≤ max (a' / p) (a' / p') * (P *ᵥ x ⬝ᵥ x) := by
            gcongr
            · exact hPnn x
            · exact le_max_left _ _
    · calc A *ᵥ x ⬝ᵥ x ≤ a' * (x ⬝ᵥ x) := hAhi x
        _ = a' / p' * (p' * (x ⬝ᵥ x)) := by field_simp
        _ ≤ a' / p' * (P *ᵥ x ⬝ᵥ x) := by
            rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hp']
            exact mul_le_mul_of_nonpos_left (hPhi x) ha.le
        _ ≤ max (a' / p) (a' / p') * (P *ᵥ x ⬝ᵥ x) := by
            gcongr
            · exact hPnn x
            · exact le_max_right _ _

end Real

/-! ### The generalized Schur decomposition -/

section Schur

variable {𝕜 : Type*} [RCLike 𝕜]

variable [IsAlgClosed 𝕜]

/-- The **generalized Schur decomposition**. Let $\mathbb{K}$ be an algebraically closed `RCLike`
field (that is, $\mathbb{C}$), and let $(A, B)$ be a regular pencil over $\mathbb{K}$. Then
there are unitary matrices $U$ and $Z$ such that $T = U^H A Z$ and $S = U^H B Z$ are both upper
triangular. This is Property 5.10 of [quarteroni2000numerical]; see also §7.7 of
[golub2013matrix].

The eigenvalues are then read off the diagonals by
`Matrix.pencilSpectrum_eq_of_isUpperTriangular`. For the proof, let $A_0 = A - \mu_0 B$ be
invertible. A Schur form $A_0^{-1} B = Z T_0 Z^H$ and a QR factorization $A_0 Z = U S_0$ give
$U^H B Z = S_0 T_0$ and $U^H A Z = S_0 + \mu_0 S_0 T_0$. -/
theorem exists_unitary_pencil_isUpperTriangular [LinearOrder n] {A B : Matrix n n 𝕜}
    (h : IsRegularPencil A B) :
    ∃ U ∈ unitaryGroup n 𝕜, ∃ Z ∈ unitaryGroup n 𝕜,
      (star U * A * Z).IsUpperTriangular ∧ (star U * B * Z).IsUpperTriangular := by
  obtain ⟨μ₀, hμ₀⟩ := h.exists_isUnit_sub_smul
  have hd := (isUnit_iff_isUnit_det _).mp hμ₀
  obtain ⟨Z, hZ, hT₀, -⟩ := exists_unitary_conj_upperTriangular ((A - μ₀ • B)⁻¹ * B)
  obtain ⟨U, hU, hS₀⟩ := exists_unitary_mul_isUpperTriangular ((A - μ₀ • B) * Z)
  have hBZ : U * ((A - μ₀ • B) * Z) * (star Z * ((A - μ₀ • B)⁻¹ * B) * Z) = U * B * Z := by
    calc _ = U * (A - μ₀ • B) * (Z * star Z) * (A - μ₀ • B)⁻¹ * B * Z := by
          simp only [Matrix.mul_assoc]
      _ = U * B * Z := by
          rw [mem_unitaryGroup_iff.mp hZ, Matrix.mul_one, mul_nonsing_inv_cancel_right _ _ hd]
  refine ⟨star U, Unitary.star_mem hU, Z, hZ, ?_, ?_⟩
  · have hAZ : U * A * Z = U * ((A - μ₀ • B) * Z) + μ₀ • (U * B * Z) := by
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.mul_assoc]
      abel
    rw [star_star, hAZ, ← hBZ]
    intro i j hij
    simp [hS₀ hij, (hS₀.mul hT₀) hij]
  · rw [star_star, ← hBZ]
    exact hS₀.mul hT₀

end Schur

/-! ### Symmetric-definite pencils -/

section CongruenceDiagonal
/-! ### A pencil congruent to a pair of diagonal matrices -/

variable {K : Type*} [Field K] [StarRing K] {X P Q : Matrix n n K} {a b : n → K}

/-- Let $K$ be a field with an involution $\bar{\cdot}$, and let $X, P, Q \in K^{n \times n}$ and
$a, b \in K^n$. If $X$ is invertible, $X^H P X = \operatorname{diag}(a)$ and
$X^H Q X = \operatorname{diag}(b)$, then every column $x_i$ of $X$ satisfies
$b_i P x_i = a_i Q x_i$. -/
theorem smul_mulVec_col_eq_of_conj_diagonal (hX : IsUnit X) (hP : Xᴴ * P * X = diagonal a)
    (hQ : Xᴴ * Q * X = diagonal b) (i : n) :
    b i • (P *ᵥ X.col i) = a i • (Q *ᵥ X.col i) := by
  have hXh : IsUnit Xᴴ.det := by
    rw [det_conjTranspose]; exact ((isUnit_iff_isUnit_det X).1 hX).star
  have hPX : P * X = (Xᴴ)⁻¹ * diagonal a := by
    rw [← hP, ← Matrix.mul_assoc, ← Matrix.mul_assoc, nonsing_inv_mul _ hXh, Matrix.one_mul]
  have hQX : Q * X = (Xᴴ)⁻¹ * diagonal b := by
    rw [← hQ, ← Matrix.mul_assoc, ← Matrix.mul_assoc, nonsing_inv_mul _ hXh, Matrix.one_mul]
  have hmat : P * X * diagonal b = Q * X * diagonal a := by
    rw [hPX, hQX, Matrix.mul_assoc, Matrix.mul_assoc, diagonal_mul_diagonal,
      diagonal_mul_diagonal]
    congr 2
    funext j
    ring
  rw [← col_mul_eq_mulVec_col, ← col_mul_eq_mulVec_col]
  ext k
  have := congrFun (congrFun hmat k) i
  simp only [mul_diagonal] at this
  simp only [Pi.smul_apply, smul_eq_mul, col_apply]
  rw [mul_comm, this, mul_comm]

/-- **The columns of a congruence to diagonal forms are eigenvectors of the pencil.** Let $X$ be
invertible with $X^H P X = \operatorname{diag}(a)$ and $X^H Q X = \operatorname{diag}(b)$. If
$b_k \neq 0$, then $(a_k / b_k, x_k)$ is an eigenpair of the pencil $(P, Q)$, where $x_k$ is the
column $k$ of $X$. -/
theorem hasPencilEigenvector_col_of_conj_diagonal (hX : IsUnit X)
    (hP : Xᴴ * P * X = diagonal a) (hQ : Xᴴ * Q * X = diagonal b) {k : n} (hk : b k ≠ 0) :
    HasPencilEigenvector P Q (a k / b k) (X.col k) := by
  refine ⟨(linearIndependent_col_iff_isUnit.2 hX).ne_zero k, ?_⟩
  have h := smul_mulVec_col_eq_of_conj_diagonal hX hP hQ k
  rw [div_eq_inv_mul, mul_smul, ← h, smul_smul, inv_mul_cancel₀ hk, one_smul]

/-- **The spectrum of a pencil congruent to diagonal forms.** Let $X$ be invertible with
$X^H P X = \operatorname{diag}(a)$ and $X^H Q X = \operatorname{diag}(b)$, and let $b_k \neq 0$
for every $k$. Then the eigenvalues of the pencil $(P, Q)$ are exactly the ratios $a_k / b_k$:
$$\sigma(P, Q) = \{a_k / b_k \mid k\}.$$
-/
theorem pencilSpectrum_eq_range_of_conj_diagonal (hX : IsUnit X)
    (hP : Xᴴ * P * X = diagonal a) (hQ : Xᴴ * Q * X = diagonal b) (hb : ∀ k, b k ≠ 0) :
    pencilSpectrum P Q = Set.range fun k => a k / b k := by
  have hXd : IsUnit X.det := (isUnit_iff_isUnit_det X).1 hX
  ext l
  simp only [mem_pencilSpectrum_iff_det, Set.mem_range]
  have hdet : (P - l • Q).det * (star X.det * X.det) = ∏ k, (a k - l * b k) := by
    have hpen : Xᴴ * (P - l • Q) * X = diagonal fun k => a k - l * b k := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, hP, hQ]
      ext i j
      by_cases h : i = j <;> simp [h]
    have := congrArg det hpen
    rw [det_mul, det_mul, det_conjTranspose, det_diagonal] at this
    rw [← this]
    ring
  have hXX : star X.det * X.det ≠ 0 := mul_ne_zero (star_ne_zero.2 hXd.ne_zero) hXd.ne_zero
  constructor
  · intro h
    rw [h, zero_mul, eq_comm, Finset.prod_eq_zero_iff] at hdet
    obtain ⟨k, -, hk⟩ := hdet
    refine ⟨k, ?_⟩
    rw [div_eq_iff (hb k)]
    linear_combination hk
  · rintro ⟨k, rfl⟩
    have hk : ∏ j, (a j - a k / b k * b j) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ k) (by rw [div_mul_cancel₀ _ (hb k), sub_self])
    rw [hk] at hdet
    exact (mul_eq_zero.1 hdet).resolve_right hXX

end CongruenceDiagonal

section SymmetricDefinite

open scoped ComplexOrder

variable {𝕜 : Type*} [RCLike 𝕜]

/-- Let $A, B, M \in \mathbb{K}^{n \times n}$ with $M$ invertible, and let $d \in \mathbb{K}^n$. If
$M^H B M = I$ and $M^H A M = \operatorname{diag}(d)$, then for every $i$ the column $m_i$ of $M$
satisfies $A m_i = d_i B m_i$ and $m_i \neq 0$: it is an eigenvector of the pencil $(A, B)$ for
$d_i$.

The columns are linearly independent by `Matrix.linearIndependent_col_iff_isUnit`, and they are
$B$-orthonormal by `Matrix.star_col_dotProduct_mulVec_col_of_conj_eq_one`. -/
theorem hasPencilEigenvector_col_of_conj_eq_diagonal {A B M : Matrix n n 𝕜} {d : n → 𝕜}
    (hM : IsUnit M) (hB : star M * B * M = 1) (hA : star M * A * M = diagonal d) (i : n) :
    HasPencilEigenvector A B (d i) (M.col i) := by
  simpa using hasPencilEigenvector_col_of_conj_diagonal (b := fun _ => 1) hM hA
    (by rw [diagonal_one]; exact hB) (k := i) one_ne_zero

/-- If $M^H B M = I$, then the columns $m_i$ of $M$ are $B$-orthonormal:
$m_i^H B m_j = \delta_{ij}$. -/
theorem star_col_dotProduct_mulVec_col_of_conj_eq_one {B M : Matrix n n 𝕜}
    (hB : star M * B * M = 1) (i j : n) :
    star (M.col i) ⬝ᵥ (B *ᵥ M.col j) = if i = j then 1 else 0 := by
  have := congrFun (congrFun hB i) j
  rw [Matrix.one_apply] at this
  rw [← this, dotProduct_mulVec]
  simp [Matrix.mul_apply, vecMul, dotProduct, col, Finset.sum_mul, mul_assoc]

/-- **Simultaneous diagonalization of a symmetric-definite pencil.** Let
$A \in \mathbb{K}^{n \times n}$ be Hermitian and $B \in \mathbb{K}^{n \times n}$ be positive
definite. Then there are an invertible matrix $M$ and a real vector $d \in \mathbb{R}^n$ such
that
$$M^H B M = I, \qquad M^H A M = \operatorname{diag}(d),$$
and the eigenvalues of the pencil $(A, B)$ are exactly the $d_i$:
$\sigma(A, B) = \{d_i \mid i\}$. This is Theorem 5.7 of [quarteroni2000numerical]; see also §8.7
of [golub2013matrix].

The source takes $M = H^{-1} Y$, with $H$ the Cholesky factor of $B$ and $Y$ an orthonormal
eigenbasis of $H^{-H} A H^{-1}$. Here $H^{-1}$ is replaced by any $W$ with $W^H B W = I$
(`Matrix.PosDef.exists_isUnit_conj_eq_one`). The columns of $M$ are $B$-orthonormal eigenvectors
of the pencil (`Matrix.hasPencilEigenvector_col_of_conj_eq_diagonal`,
`Matrix.star_col_dotProduct_mulVec_col_of_conj_eq_one`), and they are linearly independent by
`Matrix.linearIndependent_col_iff_isUnit`. -/
theorem exists_simultaneous_diagonalization {A B : Matrix n n 𝕜} (hA : A.IsHermitian)
    (hB : B.PosDef) :
    ∃ (M : Matrix n n 𝕜) (d : n → ℝ), IsUnit M ∧ star M * B * M = 1 ∧
      star M * A * M = diagonal (fun i => (d i : 𝕜)) ∧
      pencilSpectrum A B = Set.range (fun i => (d i : 𝕜)) := by
  obtain ⟨W, hW, hWB⟩ := hB.exists_isUnit_conj_eq_one
  have hC : (star W * A * W).IsHermitian := by
    rw [star_eq_conjTranspose]
    exact isHermitian_conjTranspose_mul_mul W hA
  set V : Matrix n n 𝕜 := (hC.eigenvectorUnitary : Matrix n n 𝕜) with hVdef
  have hV : star V * (star W * A * W) * V = diagonal (RCLike.ofReal ∘ hC.eigenvalues) :=
    hC.star_eigenvectorUnitary_mul_mul
  have hM : IsUnit (W * V) := hW.mul Unitary.isUnit_coe
  have h1 : star (W * V) * B * (W * V) = 1 := by
    rw [star_mul, show star V * star W * B * (W * V) = star V * (star W * B * W) * V by
      simp only [Matrix.mul_assoc], hWB, Matrix.mul_one, hVdef, Unitary.coe_star_mul_self]
  have h2 : star (W * V) * A * (W * V) = diagonal (fun i => (hC.eigenvalues i : 𝕜)) := by
    rw [star_mul, show star V * star W * A * (W * V) = star V * (star W * A * W) * V by
      simp only [Matrix.mul_assoc], hV]
    rfl
  refine ⟨W * V, hC.eigenvalues, hM, h1, h2, ?_⟩
  rw [← pencilSpectrum_mul_mul_of_isUnit A B hM.star hM, h1, h2, ← diagonal_one,
    pencilSpectrum_diagonal]
  ext μ
  simp [eq_comm]

/-- If $A$ is Hermitian and $B$ is positive definite, then every eigenvalue of the pencil $(A, B)$
is real ([quarteroni2000numerical], Theorem 5.7). -/
theorem pencilSpectrum_subset_range_ofReal_of_posDef {A B : Matrix n n 𝕜} (hA : A.IsHermitian)
    (hB : B.PosDef) : pencilSpectrum A B ⊆ Set.range ((↑) : ℝ → 𝕜) := by
  obtain ⟨M, d, -, -, -, hspec⟩ := exists_simultaneous_diagonalization hA hB
  rw [hspec]
  rintro _ ⟨i, rfl⟩
  exact ⟨d i, rfl⟩

/-- If $A$ and $B$ are both positive definite, then every eigenvalue $\mu$ of the pencil $(A, B)$
has $\operatorname{Re} \mu > 0$.

From $Ax = \mu Bx$, $\mu = x^H A x / x^H B x$ is the quotient of two positive real numbers. The
stability analysis of the θ-method for $M u' + A u = f$ with $M$ and $A$ symmetric positive
definite uses this fact ([quarteroni2000numerical], §13.3.1). -/
theorem re_pos_of_mem_pencilSpectrum_of_posDef {A B : Matrix n n 𝕜} (hA : A.PosDef)
    (hB : B.PosDef) {μ : 𝕜} (hμ : μ ∈ pencilSpectrum A B) : 0 < RCLike.re μ := by
  obtain ⟨x, hx, hμ⟩ := (mem_pencilSpectrum_iff_exists A B μ).mp hμ
  have ha := RCLike.pos_iff.mp (hA.dotProduct_mulVec_pos hx)
  have hb := RCLike.pos_iff.mp (hB.dotProduct_mulVec_pos hx)
  have h := congrArg (fun v => RCLike.re (star x ⬝ᵥ v)) hμ
  simp only [dotProduct_smul, smul_eq_mul, RCLike.mul_re, hb.2, mul_zero, sub_zero] at h
  exact (mul_pos_iff_of_pos_right hb.1).mp (h ▸ ha.1)

end SymmetricDefinite

section Deflating
/-! ### Reversed pencils and deflating subspaces -/

variable {K : Type*} [Field K]

/-- **Reciprocal eigenvalues of the reversed pencil.** If $\mu \neq 0$ and $\mu \in \sigma(A, B)$,
then $\mu^{-1} \in \sigma(B, A)$ ([golub2013matrix], §7.7.1).

The proof uses $B - \mu^{-1} A = -\mu^{-1} (A - \mu B)$. -/
theorem inv_mem_pencilSpectrum_swap {A B : Matrix n n K} {μ : K} (hμ : μ ≠ 0)
    (h : μ ∈ pencilSpectrum A B) : μ⁻¹ ∈ pencilSpectrum B A := by
  rw [mem_pencilSpectrum_iff_det] at h ⊢
  have heq : B - μ⁻¹ • A = (-μ⁻¹) • (A - μ • B) := by
    simp only [smul_sub, smul_smul, neg_mul, inv_mul_cancel₀ hμ, neg_smul, one_smul]
    abel
  rw [heq, det_smul, h, mul_zero]

/-- A subspace $S \subseteq K^n$ is a **deflating subspace** of the pencil $A - \lambda B$ if
$$\dim(AS + BS) \le \dim S,$$
where $AS + BS = \{Ax + By \mid x, y \in S\}$ ([golub2013matrix], §7.7.8).

For $B = I$ this says that $S$ is invariant under $A$ (`Matrix.isDeflatingSubspace_one_iff`). -/
def IsDeflatingSubspace (A B : Matrix n n K) (S : Submodule K (n → K)) : Prop :=
  Module.finrank K ↥(S.map A.mulVecLin ⊔ S.map B.mulVecLin) ≤ Module.finrank K S

/-- A subspace $S$ is a deflating subspace of the pencil $A - \lambda I$ if and only if $S$ is
invariant under $A$. -/
theorem isDeflatingSubspace_one_iff {A : Matrix n n K} {S : Submodule K (n → K)} :
    IsDeflatingSubspace A 1 S ↔ S ∈ Module.End.invtSubmodule A.mulVecLin := by
  rw [IsDeflatingSubspace, mulVecLin_one, Submodule.map_id, Module.End.mem_invtSubmodule_iff_map_le]
  constructor
  · intro h
    have heq : S.map A.mulVecLin ⊔ S = S :=
      (Submodule.eq_of_le_of_finrank_le le_sup_right h).symm
    exact le_sup_left.trans heq.le
  · intro h
    rw [sup_eq_right.2 h]

variable [LinearOrder n]

/-- **The flag of a generalized Schur decomposition is deflating.** Let $U$ and $Z$ be invertible,
with $U^{-1} A Z$ and $U^{-1} B Z$ upper triangular, and let $u_j$ and $z_j$ be the columns of
$U$ and $Z$. Then for every index $k$:

* $A z_j \in \operatorname{span}\{u_i \mid i \le k\}$ for all $j \le k$;
* $B z_j \in \operatorname{span}\{u_i \mid i \le k\}$ for all $j \le k$;
* $\operatorname{span}\{z_j \mid j \le k\}$ is a deflating subspace of the pencil
  $A - \lambda B$.

This is stated in [golub2013matrix], §7.7.8. The first two parts are stated as inclusions of the
spans of $\{A z_j \mid j \le k\}$ and $\{B z_j \mid j \le k\}$ in
$\operatorname{span}\{u_i \mid i \le k\}$. -/
theorem isDeflatingSubspace_span_cols_of_isUpperTriangular {A B U Z : Matrix n n K}
    (hU : IsUnit U) (hZ : IsUnit Z) (hA : (U⁻¹ * A * Z).IsUpperTriangular)
    (hB : (U⁻¹ * B * Z).IsUpperTriangular) (k : n) :
    (Submodule.span K (Set.range fun j : Set.Iic k => A *ᵥ Z.col j) ≤
        Submodule.span K (Set.range fun j : Set.Iic k => U.col j)) ∧
      (Submodule.span K (Set.range fun j : Set.Iic k => B *ᵥ Z.col j) ≤
        Submodule.span K (Set.range fun j : Set.Iic k => U.col j)) ∧
      IsDeflatingSubspace A B (Submodule.span K (Set.range fun j : Set.Iic k => Z.col j)) := by
  have hUd : IsUnit U.det := (isUnit_iff_isUnit_det U).1 hU
  have hZd : IsUnit Z.det := (isUnit_iff_isUnit_det Z).1 hZ
  -- the columns of `M Z` are combinations of leading columns of `U`
  have hcol : ∀ M : Matrix n n K, (U⁻¹ * M * Z).IsUpperTriangular →
      Submodule.span K (Set.range fun j : Set.Iic k => M *ᵥ Z.col j) ≤
        Submodule.span K (Set.range fun j : Set.Iic k => U.col j) := by
    intro M hM
    rw [Submodule.span_le]
    rintro _ ⟨⟨j, hj⟩, rfl⟩
    set T := U⁻¹ * M * Z
    have hMZ : M * Z = U * T := by
      simp only [T, ← Matrix.mul_assoc, mul_nonsing_inv U hUd, Matrix.one_mul]
    have hcolj : M *ᵥ Z.col j = ∑ i, T i j • U.col i := by
      ext r
      have := congrFun (congrFun hMZ r) j
      simp only [Matrix.mul_apply] at this
      simp only [mulVec, dotProduct, col_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [this]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    simp only at hcolj ⊢
    rw [SetLike.mem_coe, hcolj]
    refine Submodule.sum_mem _ fun i _ => ?_
    by_cases hij : i ≤ j
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i, hij.trans hj⟩, rfl⟩)
    · rw [hM (lt_of_not_ge hij), zero_smul]
      exact Submodule.zero_mem _
  refine ⟨hcol A hA, hcol B hB, ?_⟩
  set Zk := Submodule.span K (Set.range fun j : Set.Iic k => Z.col j)
  set Uk := Submodule.span K (Set.range fun j : Set.Iic k => U.col j)
  have hmap : ∀ M : Matrix n n K, Zk.map M.mulVecLin =
      Submodule.span K (Set.range fun j : Set.Iic k => M *ᵥ Z.col j) := fun M => by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  have hle : Zk.map A.mulVecLin ⊔ Zk.map B.mulVecLin ≤ Uk := by
    rw [hmap, hmap]; exact sup_le (hcol A hA) (hcol B hB)
  have hUli : LinearIndependent K fun j : Set.Iic k => U.col j :=
    (linearIndependent_cols_of_det_ne_zero hUd.ne_zero).comp _ Subtype.val_injective
  have hZli : LinearIndependent K fun j : Set.Iic k => Z.col j :=
    (linearIndependent_cols_of_det_ne_zero hZd.ne_zero).comp _ Subtype.val_injective
  unfold IsDeflatingSubspace
  calc Module.finrank K ↥(Zk.map A.mulVecLin ⊔ Zk.map B.mulVecLin) ≤ Module.finrank K Uk :=
        Submodule.finrank_mono hle
    _ = Module.finrank K Zk := by rw [finrank_span_eq_card hUli, finrank_span_eq_card hZli]

end Deflating

end Matrix
