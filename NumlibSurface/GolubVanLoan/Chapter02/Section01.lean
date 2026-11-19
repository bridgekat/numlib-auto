/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Numlib.Eigen.MinMax
import Numlib.LinearAlgebra.Matrix.NonsingularInverse
import Numlib.LinearAlgebra.Matrix.Rank
import Numlib.LinearAlgebra.Matrix.SVD
import Numlib.LinearAlgebra.Matrix.Similar

/-!
# Golub and Van Loan, Section 2.1: Basic ideas from linear algebra

This module formalizes §2.1 of [golub2013matrix], a review of linear algebra. It covers range, null
space and rank (§2.1.2), the inverse identities (2.1.1)–(2.1.3), the Sherman–Morrison–Woodbury
formula (2.1.4) and its rank-one case, the Sherman–Morrison formula (2.1.5), orthogonality (§2.1.5,
Theorem 2.1.1), the determinant (§2.1.6), eigenvalues, similarity and diagonalizability (§2.1.7),
the symmetric Schur decomposition (2.1.6), and the characterizations (2.1.7)–(2.1.8) of the largest
and the smallest eigenvalue of a symmetric matrix as the maximum and the minimum of the Rayleigh
quotient $x^T A x / x^T x$.

The proofs use Mathlib (rank–nullity, `Matrix.mul_inv_rev`, the determinant, the characteristic
polynomial and the spectral theorem) and the backbone modules `Numlib.LinearAlgebra.Matrix.Rank`,
`Numlib.LinearAlgebra.Matrix.NonsingularInverse`, `Numlib.LinearAlgebra.Matrix.Similar` and
`Numlib.Eigen.MinMax`.

## Main definitions

* §2.1.2, `GolubVanLoan.Chapter02.IsRankDeficient`: $A \in \mathbb{R}^{m \times n}$ is rank
  deficient if $\operatorname{rank}(A) < \min\{m, n\}$.

## Main results

* §2.1.2, `GolubVanLoan.Chapter02.finrank_ker_add_rank`: $\dim(\mathrm{null}(A)) +
  \operatorname{rank}(A) = n$.
* §2.1.2, `GolubVanLoan.Chapter02.range_eq_span_columns`: $\mathrm{ran}(A)$ is the span of the
  columns of $A$.
* §2.1.2, `GolubVanLoan.Chapter02.rank_eq_finrank_span_col_and_row`: the rank is the dimension of
  the column span and of the row span.
* Equation (2.1.1), `GolubVanLoan.Chapter02.equation_2_1_1`: $(AB)^{-1} = B^{-1} A^{-1}$.
* Equation (2.1.2), `GolubVanLoan.Chapter02.equation_2_1_2`: $(A^{-1})^T = (A^T)^{-1}$.
* Equation (2.1.3), `GolubVanLoan.Chapter02.equation_2_1_3`:
  $B^{-1} = A^{-1} - B^{-1}(B - A)A^{-1}$.
* Equation (2.1.4), `GolubVanLoan.Chapter02.equation_2_1_4`: the Sherman–Morrison–Woodbury formula.
* Equation (2.1.5), `GolubVanLoan.Chapter02.equation_2_1_5`: the Sherman–Morrison formula.
* §2.1.5, `GolubVanLoan.Chapter02.orthogonal_range_eq_ker_transpose`:
  $\mathrm{ran}(A)^\perp = \mathrm{null}(A^T)$.
* §2.1.5, `GolubVanLoan.Chapter02.orthogonal_range_submatrix_eq`: complementary column blocks of an
  orthogonal matrix span orthogonal complements.
* Theorem 2.1.1, `GolubVanLoan.Chapter02.theorem_2_1_1`: a matrix with orthonormal columns extends
  to an orthogonal matrix.
* §2.1.6, `GolubVanLoan.Chapter02.determinant_properties`: the cofactor expansion and the basic
  properties of the determinant.
* §2.1.7, `GolubVanLoan.Chapter02.mem_spectrum_iff_det_sub_eq_zero`: the eigenvalues are the zeros
  of $\det(A - xI)$, and there are $n$ of them with multiplicity.
* §2.1.7, `GolubVanLoan.Chapter02.isSimilar_spectrum_eq`: similar matrices have the same
  eigenvalues.
* §2.1.7, `GolubVanLoan.Chapter02.diagonalizable_of_linearIndependent_eigenvectors`: $n$ independent
  eigenvectors diagonalize $A$.
* Equation (2.1.6), `GolubVanLoan.Chapter02.equation_2_1_6`: the symmetric Schur decomposition $Q^T
  A Q = \operatorname{diag}(\lambda_1, \dots, \lambda_n)$.
* Equation (2.1.7), `GolubVanLoan.Chapter02.equation_2_1_7`: $\lambda_{\max}(A) = \max_{x \neq 0}
  x^T A x / x^T x$.
* Equation (2.1.8), `GolubVanLoan.Chapter02.equation_2_1_8`: $\lambda_{\min}(A) = \min_{x \neq 0}
  x^T A x / x^T x$.

## Conventions

* Matrices are `Matrix (Fin m) (Fin n) ℝ`, with 0-based indices. §2.1.7 is over $\mathbb{C}$, as in
  the source.
* The range $\mathrm{ran}(A)$ and the null space $\mathrm{null}(A)$ are `LinearMap.range` and
  `LinearMap.ker` of `Matrix.toEuclideanLin A`, so that orthogonal complements are taken in
  `EuclideanSpace ℝ (Fin n)`.
* The eigenvalues $\lambda_1(A) \ge \dots \ge \lambda_n(A)$ of a symmetric matrix $A$ are the
  backbone's `Matrix.IsHermitian.sortedEigenvalues`, with 0-based indices: $\lambda_{k+1}(A)$ is
  `hA.sortedEigenvalues k`.
* A real matrix $A$ is symmetric, $A^T = A$, when `A.IsHermitian` holds.
* The inverse $A^{-1}$ of a nonsingular matrix is Mathlib's `A⁻¹`. Its value at a singular matrix is
  $0$, which makes (2.1.1) and (2.1.2) hold without hypotheses.

## Deviations from the source

* **Equations (2.1.1) and (2.1.2)** (generalization). The identities also hold for singular
  matrices with Mathlib's inverse convention. See `GolubVanLoan.Chapter02.equation_2_1_1` and
  `GolubVanLoan.Chapter02.equation_2_1_2`.
* **Note after Theorem 2.1.1** (generalization). The complementary spans can be selected from
  arbitrary disjoint column lists that partition the orthogonal matrix. See
  `GolubVanLoan.Chapter02.orthogonal_range_submatrix_eq`.
* **§2.1.7, similarity** (generalization). The theorem gives equality of characteristic
  polynomials, hence equality of spectra with multiplicity. See
  `GolubVanLoan.Chapter02.isSimilar_spectrum_eq`.

## Not formalized

* **Independence, span, basis and dimension, §2.1.1.** These are the vocabulary of Mathlib.
* **The notation of §2.1.8.** The subsection fixes a notation only.
-/

open Matrix

namespace GolubVanLoan.Chapter02

variable {m n : ℕ}

/-! ### §2.1.2 Range, null space and rank -/

/-- The rank of $A$ is the dimension of $\mathrm{ran}(A)$, the range of `Matrix.toEuclideanLin A`.
-/
private theorem rank_eq_finrank_range_toEuclideanLin (A : Matrix (Fin m) (Fin n) ℝ) :
    A.rank = Module.finrank ℝ (LinearMap.range (toEuclideanLin A)) := by
  rw [rank_eq_finrank_range_toLin _ (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis]
  rfl

/-- **§2.1.2** of [golub2013matrix], rank–nullity. For $A \in \mathbb{R}^{m \times n}$,
$$\dim(\mathrm{null}(A)) + \operatorname{rank}(A) = n.$$
-/
theorem finrank_ker_add_rank (A : Matrix (Fin m) (Fin n) ℝ) :
    Module.finrank ℝ (LinearMap.ker (toEuclideanLin A)) + A.rank = n := by
  rw [rank_eq_finrank_range_toEuclideanLin, add_comm,
    LinearMap.finrank_range_add_finrank_ker, finrank_euclideanSpace_fin]

/-- **§2.1.2** of [golub2013matrix], the column space. For $A \in \mathbb{R}^{m \times n}$ with
columns $a_1, \dots, a_n$,
$$\mathrm{ran}(A) = \mathrm{span}\{a_1, \dots, a_n\}.$$
-/
theorem range_eq_span_columns (A : Matrix (Fin m) (Fin n) ℝ) :
    LinearMap.range (toEuclideanLin A) =
      Submodule.span ℝ (Set.range fun j => WithLp.toLp 2 (A.col j)) :=
  Matrix.range_toEuclideanLin_eq_span_col A

/-- **§2.1.2** of [golub2013matrix], rank. For $A \in \mathbb{R}^{m \times n}$, the rank of $A$ is
the dimension of the span of its columns, and also the dimension of the span of its rows. So the
rank is the maximal number of independent columns, and also of independent rows. -/
theorem rank_eq_finrank_span_col_and_row (A : Matrix (Fin m) (Fin n) ℝ) :
    A.rank = Module.finrank ℝ (Submodule.span ℝ (Set.range A.col)) ∧
      A.rank = Module.finrank ℝ (Submodule.span ℝ (Set.range A.row)) :=
  ⟨A.rank_eq_finrank_span_cols, A.rank_eq_finrank_span_row⟩

/-- **§2.1.2** of [golub2013matrix], rank deficiency. A matrix $A \in \mathbb{R}^{m \times n}$ is
**rank deficient** if
$$\operatorname{rank}(A) < \min\{m, n\}.$$
-/
def IsRankDeficient (A : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  A.rank < min m n

/-! ### §2.1.3–2.1.4 The inverse and the Sherman–Morrison–Woodbury formula -/

/-- **Equation (2.1.1)** of [golub2013matrix]. The inverse of a product is the product of the
inverses in reverse order: for $A, B \in \mathbb{R}^{n \times n}$,
$$(AB)^{-1} = B^{-1} A^{-1}.$$

**Generalization.** The source uses nonsingular factors. If either factor is singular, the
product is singular and both sides evaluate to zero under Lean's inverse convention. -/
theorem equation_2_1_1 (A B : Matrix (Fin n) (Fin n) ℝ) : (A * B)⁻¹ = B⁻¹ * A⁻¹ :=
  Matrix.mul_inv_rev A B

/-- **Equation (2.1.2)** of [golub2013matrix]. The transpose of the inverse is the inverse of the
transpose: for $A \in \mathbb{R}^{n \times n}$,
$$(A^{-1})^T = (A^T)^{-1} \equiv A^{-T}.$$

**Generalization.** The source uses a nonsingular matrix. A singular matrix and its transpose
both have zero inverse under Lean's convention, so that case also satisfies the equality. -/
theorem equation_2_1_2 (A : Matrix (Fin n) (Fin n) ℝ) : (A⁻¹)ᵀ = (Aᵀ)⁻¹ :=
  Matrix.transpose_nonsing_inv A

/-- **Equation (2.1.3)** of [golub2013matrix]. Let $A, B \in \mathbb{R}^{n \times n}$ be
nonsingular. Then
$$B^{-1} = A^{-1} - B^{-1} (B - A) A^{-1},$$
which "shows how the inverse changes if the matrix changes". -/
theorem equation_2_1_3 {A B : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A) (hB : IsUnit B) :
    B⁻¹ = A⁻¹ - B⁻¹ * (B - A) * A⁻¹ := by
  have hA' := (isUnit_iff_isUnit_det A).1 hA
  have hB' := (isUnit_iff_isUnit_det B).1 hB
  rw [Matrix.mul_sub, Matrix.sub_mul, nonsing_inv_mul B hB', Matrix.one_mul, Matrix.mul_assoc,
    mul_nonsing_inv A hA', Matrix.mul_one, sub_sub_cancel]

/-- **Equation (2.1.4)** of [golub2013matrix] (Sherman–Morrison–Woodbury formula). Let
$A \in \mathbb{R}^{n \times n}$ and $U, V \in \mathbb{R}^{n \times k}$. If $A$ and
$I + V^T A^{-1} U$ are nonsingular, then $A + UV^T$ is nonsingular and
$$(A + UV^T)^{-1} = A^{-1} - A^{-1} U (I + V^T A^{-1} U)^{-1} V^T A^{-1}.$$
So a rank-$k$ correction of a matrix gives a rank-$k$ correction of its inverse. -/
theorem equation_2_1_4 {k : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A)
    (U V : Matrix (Fin n) (Fin k) ℝ) (hW : IsUnit (1 + Vᵀ * A⁻¹ * U)) :
    IsUnit (A + U * Vᵀ) ∧
      (A + U * Vᵀ)⁻¹ = A⁻¹ - A⁻¹ * U * (1 + Vᵀ * A⁻¹ * U)⁻¹ * Vᵀ * A⁻¹ := by
  have hA' := (isUnit_iff_isUnit_det A).1 hA
  refine ⟨?_, ?_⟩
  · rw [isUnit_iff_isUnit_det, det_add_mul U Vᵀ hA']
    exact hA'.mul ((isUnit_iff_isUnit_det _).1 hW)
  · have h := add_mul_mul_mul_inv_eq_sub_of_isUnit_one_add hA U 1 Vᵀ (by rwa [Matrix.one_mul])
    simpa only [Matrix.mul_one, Matrix.one_mul] using h

/-- **Equation (2.1.5)** of [golub2013matrix] (Sherman–Morrison formula), the case $k = 1$ of
(2.1.4). Let $A \in \mathbb{R}^{n \times n}$ be nonsingular, let $u, v \in \mathbb{R}^n$, and
let $\alpha = 1 + v^T A^{-1} u \neq 0$. Then $A + uv^T$ is nonsingular and
$$(A + uv^T)^{-1} = A^{-1} - \frac{1}{\alpha} A^{-1} u v^T A^{-1}.$$

The outer product $uv^T$ is `Matrix.vecMulVec u v`. -/
theorem equation_2_1_5 {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A) {u v : Fin n → ℝ}
    (hα : 1 + v ⬝ᵥ (A⁻¹ *ᵥ u) ≠ 0) :
    IsUnit (A + vecMulVec u v) ∧
      (A + vecMulVec u v)⁻¹
        = A⁻¹ - (1 / (1 + v ⬝ᵥ (A⁻¹ *ᵥ u))) • (A⁻¹ * vecMulVec u v * A⁻¹) := by
  refine ⟨isUnit_add_vecMulVec hA hα, ?_⟩
  rw [inv_add_vecMulVec hA hα, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]

/-! ### §2.1.5 Orthogonality -/

/-- **§2.1.5** of [golub2013matrix]. For $A \in \mathbb{R}^{m \times n}$,
$$\mathrm{ran}(A)^\perp = \mathrm{null}(A^T).$$
-/
theorem orthogonal_range_eq_ker_transpose (A : Matrix (Fin m) (Fin n) ℝ) :
    (LinearMap.range (toEuclideanLin A))ᗮ = LinearMap.ker (toEuclideanLin Aᵀ) := by
  rw [LinearMap.orthogonal_range, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    conjTranspose_eq_transpose_of_trivial]

/-- **§2.1.5** of [golub2013matrix], complementary column blocks. Let
$V \in \mathbb{R}^{n \times n}$ be orthogonal. Let $f : \{1, \dots, r\} \to \{1, \dots, n\}$ and
$g : \{1, \dots, s\} \to \{1, \dots, n\}$ be injective column selections with disjoint images,
and let $r + s = n$, so that together they select every column once. Then
$$\mathrm{ran}(V(:, f))^\perp = \mathrm{ran}(V(:, g)).$$

**Generalization.** The note after Theorem 2.1.1 takes the two contiguous column blocks.
The declaration allows any two disjoint column selections of those sizes, since the
concatenated selections form a permutation of all columns. -/
theorem orthogonal_range_submatrix_eq {r s : ℕ} {V : Matrix (Fin n) (Fin n) ℝ}
    (hV : V ∈ orthogonalGroup (Fin n) ℝ) {f : Fin r → Fin n} {g : Fin s → Fin n}
    (hf : Function.Injective f) (hg : Function.Injective g) (hfg : ∀ a b, f a ≠ g b)
    (hrs : r + s = n) :
    (LinearMap.range (toEuclideanLin (V.submatrix id f)))ᗮ =
      LinearMap.range (toEuclideanLin (V.submatrix id g)) :=
  (range_submatrix_eq_orthogonal hV ((Fintype.bijective_iff_injective_and_card _).2
    ⟨hf.sumElim hg hfg, by simp [hrs]⟩)).symm

/-- **Theorem 2.1.1** of [golub2013matrix]. Let $V_1 \in \mathbb{R}^{n \times r}$ have orthonormal
columns, $V_1^T V_1 = I$. Then $r \le n$, and there is $V_2 \in \mathbb{R}^{n \times (n - r)}$
such that
$$V = [\, V_1 \mid V_2 \,]$$
is orthogonal and $\mathrm{ran}(V_1)^\perp = \mathrm{ran}(V_2)$.

The inequality $r \le n$ follows from the hypothesis and is part of the conclusion. The matrix
$[\, V_1 \mid V_2 \,]$ is `Matrix.fromCols V₁ V₂`, read on `Fin n` through `Fin (r + (n - r))`.
The proof is the backbone's orthonormal completion
`Matrix.exists_mem_unitaryGroup_submatrix_eq`, which extends an orthonormal basis; the source
defers this step to the QR factorization. -/
theorem theorem_2_1_1 {r : ℕ} (V₁ : Matrix (Fin n) (Fin r) ℝ) (hV₁ : V₁ᵀ * V₁ = 1) :
    ∃ (hr : r ≤ n) (V₂ : Matrix (Fin n) (Fin (n - r)) ℝ),
      (fromCols V₁ V₂).submatrix id (finSumFinEquiv.symm ∘ Fin.cast (Nat.add_sub_of_le hr).symm)
          ∈ orthogonalGroup (Fin n) ℝ ∧
        (LinearMap.range (toEuclideanLin V₁))ᗮ = LinearMap.range (toEuclideanLin V₂) := by
  have hr : r ≤ n := by
    have h1 : V₁.rank = r := by
      rw [← rank_transpose_mul_self, hV₁, rank_one, Fintype.card_fin]
    have h2 := V₁.rank_le_card_height
    rwa [h1, Fintype.card_fin] at h2
  have hV₁' : V₁ᴴ * V₁ = 1 := by rwa [conjTranspose_eq_transpose_of_trivial]
  obtain ⟨U, hU, hUV⟩ := exists_mem_unitaryGroup_submatrix_eq V₁ hV₁' (Fin.castLEEmb hr)
  have hUV' : U.submatrix id (Fin.castLE hr) = V₁ := hUV
  set g : Fin (n - r) → Fin n := Fin.cast (Nat.add_sub_of_le hr) ∘ Fin.natAdd r with hg
  have hg_inj : Function.Injective g := fun a b h => by
    have := congrArg Fin.val h
    simp only [hg, Function.comp_apply, Fin.val_cast, Fin.val_natAdd] at this
    exact Fin.ext (by omega)
  refine ⟨hr, U.submatrix id g, ?_, ?_⟩
  · convert hU using 1
    ext i k
    obtain ⟨k', rfl⟩ : ∃ k', Fin.cast (Nat.add_sub_of_le hr) k' = k :=
      ⟨Fin.cast (Nat.add_sub_of_le hr).symm k, by simp⟩
    induction k' using Fin.addCases with
    | left a =>
      simp only [submatrix_apply, id, Function.comp_apply, Fin.cast_cast, Fin.cast_eq_self,
        finSumFinEquiv_symm_apply_castAdd, fromCols_apply_inl, ← hUV']
      congr 1
    | right b =>
      simp only [submatrix_apply, id, Function.comp_apply, Fin.cast_cast, Fin.cast_eq_self,
        finSumFinEquiv_symm_apply_natAdd, fromCols_apply_inr, hg]
  · rw [← hUV']
    refine orthogonal_range_submatrix_eq hU (Fin.castLE_injective hr) hg_inj (fun a b h => ?_)
      (Nat.add_sub_of_le hr)
    have := congrArg Fin.val h
    simp only [hg, Function.comp_apply, Fin.val_cast, Fin.val_natAdd, Fin.val_castLE] at this
    omega

/-! ### §2.1.6 The determinant -/

/-- **§2.1.6** of [golub2013matrix], the determinant. Let $C \in \mathbb{R}^{(n+1) \times (n+1)}$,
$A, B \in \mathbb{R}^{n \times n}$ and $c \in \mathbb{R}$. Then:
* the cofactor expansion along the first row holds, $\det(C) = \sum_{j=1}^{n+1} (-1)^{j+1}
  c_{1j} \det(C_{1j})$, where $C_{1j}$ is $C$ without the first row and the $j$-th column;
* $\det(AB) = \det(A) \det(B)$;
* $\det(A^T) = \det(A)$;
* $\det(cA) = c^n \det(A)$;
* $\det(A) \neq 0$ if and only if $A$ is nonsingular.

In 0-based indices the sign of the cofactor expansion is $(-1)^j$. -/
theorem determinant_properties (C : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (A B : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) :
    C.det = ∑ j : Fin (n + 1), (-1) ^ (j : ℕ) * C 0 j * (C.submatrix Fin.succ j.succAbove).det ∧
      (A * B).det = A.det * B.det ∧ Aᵀ.det = A.det ∧ (c • A).det = c ^ n * A.det ∧
      (A.det ≠ 0 ↔ IsUnit A) := by
  refine ⟨det_succ_row_zero C, det_mul A B, det_transpose A, ?_, ?_⟩
  · rw [det_smul, Fintype.card_fin]
  · rw [isUnit_iff_isUnit_det, isUnit_iff_ne_zero]

/-! ### §2.1.7 Eigenvalues and eigenvectors -/

/-- **§2.1.7** of [golub2013matrix], eigenvalues. Let $A \in \mathbb{C}^{n \times n}$ and
$x \in \mathbb{C}$. Then $x$ is an eigenvalue of $A$ if and only if $\det(A - xI) = 0$, so that
$\lambda(A) = \{x : \det(A - xI) = 0\}$. Also, $x$ is an eigenvalue of $A$ if and only if
$Av = xv$ for some $v \neq 0$. Last, "every $n$-by-$n$ matrix has $n$ eigenvalues": the
characteristic polynomial of $A$ has $n$ roots, counted with multiplicity.

The set $\lambda(A)$ is `spectrum ℂ A`. -/
theorem mem_spectrum_iff_det_sub_eq_zero (A : Matrix (Fin n) (Fin n) ℂ) (x : ℂ) :
    (x ∈ spectrum ℂ A ↔ (A - x • (1 : Matrix (Fin n) (Fin n) ℂ)).det = 0) ∧
      (x ∈ spectrum ℂ A ↔ ∃ v ≠ 0, A *ᵥ v = x • v) ∧
      A.charpoly.roots.card = n := by
  have hdet : x ∈ spectrum ℂ A ↔ (A - x • (1 : Matrix (Fin n) (Fin n) ℂ)).det = 0 := by
    rw [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one, ← neg_sub, IsUnit.neg_iff,
      isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not]
  refine ⟨hdet, ?_, ?_⟩
  · rw [hdet, ← exists_mulVec_eq_zero_iff]
    refine exists_congr fun v => and_congr_right fun _ => ?_
    rw [sub_mulVec, smul_mulVec, one_mulVec, sub_eq_zero]
  · rw [IsAlgClosed.card_roots_eq_natDegree, charpoly_natDegree_eq_dim, Fintype.card_fin]

/-- **§2.1.7** of [golub2013matrix], similarity. Let $A, X \in \mathbb{C}^{n \times n}$ with $X$
nonsingular, and let $B = X^{-1} A X$. Then $A$ and $B$ have the same characteristic polynomial,
and so exactly the same eigenvalues.

**Generalization.** The source states equality of the eigenvalue sets. Preserving the
characteristic polynomial also preserves each algebraic multiplicity. -/
theorem isSimilar_spectrum_eq (A X : Matrix (Fin n) (Fin n) ℂ) (hX : IsUnit X) :
    (X⁻¹ * A * X).charpoly = A.charpoly ∧ spectrum ℂ (X⁻¹ * A * X) = spectrum ℂ A :=
  ⟨(IsSimilar.charpoly_eq ⟨X, hX, rfl⟩).symm, (IsSimilar.spectrum_eq ⟨X, hX, rfl⟩).symm⟩

/-- **§2.1.7** of [golub2013matrix], diagonalizability. Let $A \in \mathbb{C}^{n \times n}$ have $n$
linearly independent eigenvectors $x_1, \dots, x_n$, with $A x_i = \lambda_i x_i$. Then
$X = [\, x_1 \mid \cdots \mid x_n \,]$ is nonsingular and
$$X^{-1} A X = \operatorname{diag}(\lambda_1, \dots, \lambda_n).$$

The matrix $X$ with the columns $x_i$ is `(Matrix.of x)ᵀ`. -/
theorem diagonalizable_of_linearIndependent_eigenvectors (A : Matrix (Fin n) (Fin n) ℂ)
    (x : Fin n → Fin n → ℂ) (μ : Fin n → ℂ) (hx : LinearIndependent ℂ x)
    (hAx : ∀ i, A *ᵥ x i = μ i • x i) :
    IsUnit (Matrix.of x)ᵀ ∧ ((Matrix.of x)ᵀ)⁻¹ * A * (Matrix.of x)ᵀ = diagonal μ := by
  have hX : IsUnit (Matrix.of x)ᵀ := Matrix.linearIndependent_col_iff_isUnit.1 hx
  have hd : IsUnit ((Matrix.of x)ᵀ).det := (isUnit_iff_isUnit_det _).1 hX
  have hAX : A * (Matrix.of x)ᵀ = (Matrix.of x)ᵀ * diagonal μ := by
    ext i j
    have h := congrFun (hAx j) i
    rw [Matrix.mul_apply, Matrix.mul_apply]
    simp only [diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [show ((Matrix.of x)ᵀ) i j = x j i from rfl, mul_comm]
    exact h
  refine ⟨hX, ?_⟩
  rw [Matrix.mul_assoc, hAX, ← Matrix.mul_assoc, nonsing_inv_mul _ hd, Matrix.one_mul]

/-! ### (2.1.6)–(2.1.8) Symmetric matrices -/

/-- The eigenvalues of a symmetric operator do not depend on how the dimension of the space is
written. -/
private theorem eigenvalues_cast {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) {a b : ℕ}
    (ha : Module.finrank ℝ E = a) (hb : Module.finrank ℝ E = b) (i : Fin a) :
    hT.eigenvalues ha i = hT.eigenvalues hb (Fin.cast (ha.symm.trans hb) i) := by
  obtain rfl : a = b := ha.symm.trans hb
  rfl

/-- The sorted eigenvalues of a symmetric matrix $A$ are those of `Matrix.toEuclideanLin A`, indexed
by `Fin n`. -/
private theorem sortedEigenvalues_eq {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian)
    (k : Fin n) :
    hA.sortedEigenvalues k =
      (isSymmetric_toEuclideanLin_iff.mpr hA).eigenvalues finrank_euclideanSpace_fin k := by
  rw [IsHermitian.sortedEigenvalues_apply, IsHermitian.eigenvalues₀, eigenvalues_cast]
  rfl

/-- **Equation (2.1.6)** of [golub2013matrix] (symmetric Schur decomposition). Let
$A \in \mathbb{R}^{n \times n}$ be symmetric. Then there is an orthogonal
$Q \in \mathbb{R}^{n \times n}$ with
$$Q^T A Q = \operatorname{diag}(\lambda_1, \dots, \lambda_n),$$
where $\lambda_1 \ge \dots \ge \lambda_n$ are the eigenvalues of $A$ in decreasing order, as in
the source.

The eigenvalues are `Matrix.IsHermitian.sortedEigenvalues`. -/
theorem equation_2_1_6 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) :
    ∃ Q ∈ orthogonalGroup (Fin n) ℝ, Qᵀ * A * Q = diagonal hA.sortedEigenvalues := by
  set U : Matrix (Fin n) (Fin n) ℝ := (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)
  have hU : Uᵀ * A * U = diagonal hA.eigenvalues := by
    have h := hA.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_apply] at h
    simpa [U, Unitary.coe_star, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
      using h
  have hUU : Uᵀ * U = 1 := by
    simpa [U, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using
      mem_unitaryGroup_iff'.1 hA.eigenvectorUnitary.2
  set e : Fin (Fintype.card (Fin n)) ≃ Fin n := Fintype.equivOfCardEq (Fintype.card_fin _)
  set σ : Fin n ≃ Fin n := (finCongr (Fintype.card_fin n).symm).trans e
  have hσ : hA.eigenvalues ∘ σ = hA.sortedEigenvalues := by
    funext k
    simp [σ, e, IsHermitian.eigenvalues, IsHermitian.sortedEigenvalues_apply]
  have hconj : ∀ M : Matrix (Fin n) (Fin n) ℝ,
      (U.submatrix id σ)ᵀ * M * U.submatrix id σ = (Uᵀ * M * U).submatrix σ σ := fun M => by
    rw [transpose_submatrix, ← submatrix_id_id M, ← submatrix_mul _ _ _ _ _ Function.bijective_id,
      ← submatrix_mul _ _ _ _ _ Function.bijective_id, submatrix_id_id]
  refine ⟨U.submatrix id σ, (mem_orthogonalGroup_iff' (Fin n) ℝ).2 ?_, ?_⟩
  · have h := hconj 1
    rwa [Matrix.mul_one, Matrix.mul_one, hUU, submatrix_one_equiv] at h
  · rw [hconj, hU, submatrix_diagonal_equiv, hσ]

/-- The Rayleigh quotient of `Matrix.toEuclideanLin A` at a vector $x$ is $x^T A x / x^T x$. -/
private theorem rayleighQuotient_toEuclideanLin (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    (toEuclideanLin A).rayleighQuotient (WithLp.toLp 2 x) = x ⬝ᵥ (A *ᵥ x) / (x ⬝ᵥ x) := by
  rw [LinearMap.rayleighQuotient, ← real_inner_self_eq_norm_sq, RCLike.re_to_real,
    EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
  simp

/-- Every eigenvalue of a symmetric matrix $A$ is a Rayleigh quotient $x^T A x / x^T x$ at some
$x \neq 0$, and every Rayleigh quotient at $x \neq 0$ lies between the smallest and the largest
eigenvalue. -/
private theorem rayleigh_attained_and_mem_Icc {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hA : A.IsHermitian) (k : Fin (n + 1)) :
    (∃ x : Fin (n + 1) → ℝ, x ≠ 0 ∧ hA.sortedEigenvalues k = x ⬝ᵥ (A *ᵥ x) / (x ⬝ᵥ x)) ∧
      ∀ x : Fin (n + 1) → ℝ, x ≠ 0 → x ⬝ᵥ (A *ᵥ x) / (x ⬝ᵥ x) ∈
        Set.Icc (hA.sortedEigenvalues (Fin.last n)) (hA.sortedEigenvalues 0) := by
  have hT := isSymmetric_toEuclideanLin_iff.mpr hA
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1 := finrank_euclideanSpace_fin
  simp only [sortedEigenvalues_eq]
  refine ⟨⟨WithLp.ofLp (hT.eigenvectorBasis hn k), by simpa using hT.eigenvectorBasis_ne_zero hn k,
    ?_⟩, fun x hx => ?_⟩
  · rw [← rayleighQuotient_toEuclideanLin, WithLp.toLp_ofLp, hT.rayleighQuotient_eigenvectorBasis]
  · rw [← rayleighQuotient_toEuclideanLin]
    exact hT.rayleighQuotient_mem_Icc hn (by simpa using hx)

/-- **Equation (2.1.7)** of [golub2013matrix]. Let $A$ be a symmetric real matrix of order
$n + 1 \ge 1$. Then the largest eigenvalue of $A$ is the maximum of the Rayleigh quotient:
$$\lambda_{\max}(A) = \max_{x \neq 0} \frac{x^T A x}{x^T x}.$$

The maximum is `IsGreatest` of the set of Rayleigh quotients, and $\lambda_{\max}(A)$ is
`hA.sortedEigenvalues 0`. -/
theorem equation_2_1_7 {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hA : A.IsHermitian) :
    IsGreatest {r : ℝ | ∃ x : Fin (n + 1) → ℝ, x ≠ 0 ∧ r = x ⬝ᵥ (A *ᵥ x) / (x ⬝ᵥ x)}
      (hA.sortedEigenvalues 0) := by
  obtain ⟨hx, hI⟩ := rayleigh_attained_and_mem_Icc hA 0
  exact ⟨hx, by rintro r ⟨x, hx, rfl⟩; exact (hI x hx).2⟩

/-- **Equation (2.1.8)** of [golub2013matrix]. Let $A$ be a symmetric real matrix of order
$n + 1 \ge 1$. Then the smallest eigenvalue of $A$ is the minimum of the Rayleigh quotient:
$$\lambda_{\min}(A) = \min_{x \neq 0} \frac{x^T A x}{x^T x}.$$

The minimum is `IsLeast` of the set of Rayleigh quotients, and $\lambda_{\min}(A)$ is
`hA.sortedEigenvalues (Fin.last n)`. -/
theorem equation_2_1_8 {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hA : A.IsHermitian) :
    IsLeast {r : ℝ | ∃ x : Fin (n + 1) → ℝ, x ≠ 0 ∧ r = x ⬝ᵥ (A *ᵥ x) / (x ⬝ᵥ x)}
      (hA.sortedEigenvalues (Fin.last n)) := by
  obtain ⟨hx, hI⟩ := rayleigh_attained_and_mem_Icc hA (Fin.last n)
  exact ⟨hx, by rintro r ⟨x, hx, rfl⟩; exact (hI x hx).1⟩

end GolubVanLoan.Chapter02
