/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Eigen.Normal
import Numlib.LinearAlgebra.Matrix.Schur
import Numlib.LinearAlgebra.Matrix.Similar
import NumlibSurface.QuarteroniSaccoSaleri.Chapter01.Section07

/-!
# Quarteroni, Sacco and Saleri, Section 1.8: Similarity transformations

This module formalizes §1.8 of [quarteroni2000numerical]. Two matrices
$A, B \in \mathbb{C}^{n \times n}$ are similar if $B = C^{-1} A C$ for a nonsingular $C$, and
unitarily similar if $C$ can be chosen unitary (Definition 1.14). Similar matrices have the same
characteristic polynomial and the same eigenvalues, and the products $AB$ and $BA$ have the same
nonzero eigenvalues. The Schur decomposition (Property 1.5) states that every matrix is unitarily
similar to an upper triangular matrix; its consequences are that a Hermitian matrix is unitarily
similar to a real diagonal matrix, that a matrix is normal if and only if it is unitarily similar to
a diagonal matrix, and that two commuting normal matrices are diagonalized by one unitary matrix.
The Jordan canonical form (Property 1.6) states that every matrix is similar to a block diagonal
matrix of Jordan blocks; a matrix is diagonalizable if and only if it is not defective, and the
columns of the transforming matrix satisfy the recursion (1.8) of the principal vectors. Example 1.6
computes the Jordan form of one $6 \times 6$ matrix.

The proofs specialize the backbone modules `Numlib.LinearAlgebra.Matrix.Similar` (similarity),
`Numlib.LinearAlgebra.Matrix.Schur` (the Schur decomposition,
`Matrix.exists_unitary_conj_upperTriangular`), `Numlib.Eigen.Normal` (the spectral theorem for
normal matrices, `Matrix.IsStarNormal.spectral_theorem`) and `Numlib.LinearAlgebra.Matrix.Jordan`
(the Jordan form), together with Mathlib's spectral theorem `Matrix.IsHermitian.spectral_theorem`.

## Main definitions

* Definition 1.14, `QuarteroniSaccoSaleri.Chapter01.definition_1_14`: similar and unitarily similar
  matrices, stated for the backbone predicates `Matrix.IsSimilar` and `Matrix.IsUnitarilySimilar`.
* Example 1.6, `QuarteroniSaccoSaleri.Chapter01.example_1_6_A`,
  `QuarteroniSaccoSaleri.Chapter01.example_1_6_J`, `QuarteroniSaccoSaleri.Chapter01.example_1_6_X`
  and `QuarteroniSaccoSaleri.Chapter01.example_1_6_Xinv`: the matrix $A$, its Jordan form $J$, the
  transforming matrix $X$ and its inverse.

## Main results

* §1.8, `QuarteroniSaccoSaleri.Chapter01.charpoly_eq_of_isSimilar`: similar matrices have the same
  characteristic polynomial and spectrum, and a similarity maps eigenvectors to eigenvectors.
* §1.8, `QuarteroniSaccoSaleri.Chapter01.spectrum_mul_comm`: $\sigma(AB) \setminus \{0\} =
  \sigma(BA) \setminus \{0\}$ and $\rho(AB) = \rho(BA)$.
* Property 1.5, `QuarteroniSaccoSaleri.Chapter01.property_1_5` (Schur decomposition): every matrix
  is unitarily similar to an upper triangular matrix whose diagonal entries are the eigenvalues.
* §1.8, `QuarteroniSaccoSaleri.Chapter01.property_1_5_hermitian`: a Hermitian matrix is unitarily
  similar to a real diagonal matrix, and its eigenvectors form an orthonormal basis.
* §1.8, `QuarteroniSaccoSaleri.Chapter01.property_1_5_diagonalizable_iff`: a matrix is similar to a
  diagonal matrix if and only if it has $n$ linearly independent eigenvectors.
* §1.8, `QuarteroniSaccoSaleri.Chapter01.property_1_5_normal`: a matrix is normal if and only if it
  is unitarily similar to a diagonal matrix, and a normal matrix has a spectral decomposition.
* §1.8, `QuarteroniSaccoSaleri.Chapter01.property_1_5_commute`: two commuting normal matrices are
  diagonalized by the same unitary matrix.
* Property 1.6, `QuarteroniSaccoSaleri.Chapter01.property_1_6` (Jordan canonical form): every matrix
  is similar to a block diagonal matrix of Jordan blocks.
* §1.8, `QuarteroniSaccoSaleri.Chapter01.property_1_6_diagonalizable_iff_nondefective`: a matrix is
  diagonalizable if and only if it is not defective, and normal matrices are diagonalizable.
* Equation (1.8), `QuarteroniSaccoSaleri.Chapter01.equation_1_8`: the columns of the transforming
  matrix of a Jordan form are principal vectors.
* Example 1.6, `QuarteroniSaccoSaleri.Chapter01.example_1_6`: $X^{-1} A X = J =
  \operatorname{diag}(J_2(2), J_3(3), J_1(2))$.

## Conventions

* The Jordan form $\operatorname{diag}(J_{k_1}(\lambda_1), \dots, J_{k_l}(\lambda_l))$ is the
  backbone's `Matrix.jordanForm e μ`, a block diagonal matrix indexed by the sigma type
  `(i : ι) × Fin (e i)`. A matrix of order $n$ in this form is `reindex σ σ (jordanForm e μ)` for an
  equivalence `σ` of the sigma type with `Fin n`. The book's column $x_j$ of $X$, at position $j$ of
  the block $i$, is `Xᵀ (σ ⟨i, j⟩)`.
* Property 1.6 groups the Jordan blocks by eigenvalue, as the backbone statement does. Example 1.6
  places the blocks one after the other along the diagonal, through `finSigmaFinEquiv`.
-/

open Finset Matrix Polynomial
open scoped ENNReal NNReal

namespace QuarteroniSaccoSaleri.Chapter01

variable {n : ℕ}

/-! ### Definition 1.14 and the invariants of similarity -/

/-- **Definition 1.14** of [quarteroni2000numerical]. Let $A, B \in \mathbb{C}^{n \times n}$. The
matrices $A$ and $B$ are **similar** if and only if $B = C^{-1} A C$ for some nonsingular
$C \in \mathbb{C}^{n \times n}$; the map $A \mapsto C^{-1} A C$ is a **similarity
transformation**. The matrices are **unitarily similar** if and only if $B = U^H A U$ for some
unitary $U$. Unitarily similar matrices are similar, and similarity is reflexive, symmetric and
transitive.

Similarity is the backbone predicate `Matrix.IsSimilar A B`, and unitary similarity is
`Matrix.IsUnitarilySimilar A B`. -/
theorem definition_1_14 (A B : Matrix (Fin n) (Fin n) ℂ) :
    (IsSimilar A B ↔ ∃ C : Matrix (Fin n) (Fin n) ℂ, IsUnit C ∧ B = C⁻¹ * A * C) ∧
      (IsUnitarilySimilar A B ↔ ∃ U ∈ unitaryGroup (Fin n) ℂ, B = star U * A * U) ∧
      (IsUnitarilySimilar A B → IsSimilar A B) ∧
      (IsSimilar A A ∧ (IsSimilar A B → IsSimilar B A) ∧
        ∀ C, IsSimilar A B → IsSimilar B C → IsSimilar A C) :=
  ⟨Iff.rfl, Iff.rfl, IsUnitarilySimilar.isSimilar,
    IsSimilar.refl A, IsSimilar.symm, fun _ h₁ h₂ => h₁.trans h₂⟩

/-- **Section 1.8** of [quarteroni2000numerical], similar matrices share the spectrum. Let
$A, B \in \mathbb{C}^{n \times n}$ be similar. Then $A$ and $B$ have the same characteristic
polynomial and the same spectrum. Moreover, if $B = C^{-1} A C$ with $C$ nonsingular and
$Ax = \lambda x$, then $B (C^{-1} x) = \lambda C^{-1} x$, because
$(C^{-1} A C) C^{-1} x = C^{-1} A x$.

The proof uses the backbone theorems `Matrix.IsSimilar.charpoly_eq` and
`Matrix.IsSimilar.mulVec_eq_smul`. -/
theorem charpoly_eq_of_isSimilar {A B : Matrix (Fin n) (Fin n) ℂ} (h : IsSimilar A B) :
    A.charpoly = B.charpoly ∧ spectrum ℂ A = spectrum ℂ B ∧
      ∀ (C : Matrix (Fin n) (Fin n) ℂ), IsUnit C → B = C⁻¹ * A * C →
        ∀ (μ : ℂ) (x : Fin n → ℂ), A *ᵥ x = μ • x → B *ᵥ (C⁻¹ *ᵥ x) = μ • (C⁻¹ *ᵥ x) := by
  refine ⟨h.charpoly_eq, Set.ext fun μ => ?_,
    fun C hC hB μ x hx => IsSimilar.mulVec_eq_smul hC hB hx⟩
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, Matrix.mem_spectrum_iff_isRoot_charpoly,
    h.charpoly_eq]

/-- **Section 1.8** of [quarteroni2000numerical], the spectra of $AB$ and $BA$. Let
$A \in \mathbb{C}^{n \times m}$ and $B \in \mathbb{C}^{m \times n}$. The products $AB$ and $BA$
need not be similar, but they have the same nonzero eigenvalues,
$$\sigma(AB) \setminus \{0\} = \sigma(BA) \setminus \{0\},$$
and consequently $\rho(AB) = \rho(BA)$.

The proof uses the identity $\lambda^m p_{AB}(\lambda) = \lambda^n p_{BA}(\lambda)$ of Mathlib's
`Matrix.charpoly_mul_comm'`. -/
theorem spectrum_mul_comm {m : ℕ} (A : Matrix (Fin n) (Fin m) ℂ) (B : Matrix (Fin m) (Fin n) ℂ) :
    spectrum ℂ (A * B) \ {0} = spectrum ℂ (B * A) \ {0} ∧
      spectralRadius ℂ (A * B) = spectralRadius ℂ (B * A) := by
  have hset : spectrum ℂ (A * B) \ {0} = spectrum ℂ (B * A) \ {0} := by
    ext μ
    simp only [Set.mem_sdiff, Set.mem_singleton_iff, Matrix.mem_spectrum_iff_isRoot_charpoly]
    constructor
    · rintro ⟨h, hμ⟩
      refine ⟨?_, hμ⟩
      have := congrArg (eval μ) (charpoly_mul_comm' A B)
      rw [eval_mul, eval_mul, eval_pow, eval_pow, eval_X, h.eq_zero, mul_zero, eq_comm,
        mul_eq_zero] at this
      exact IsRoot.def.2 (this.resolve_left (pow_ne_zero _ hμ))
    · rintro ⟨h, hμ⟩
      refine ⟨?_, hμ⟩
      have := congrArg (eval μ) (charpoly_mul_comm' A B)
      rw [eval_mul, eval_mul, eval_pow, eval_pow, eval_X, h.eq_zero, mul_zero, mul_eq_zero] at this
      exact IsRoot.def.2 (this.resolve_left (pow_ne_zero _ hμ))
  exact ⟨hset, by rw [spectralRadius_eq_iSup_diff_singleton_zero,
    spectralRadius_eq_iSup_diff_singleton_zero, hset]⟩

/-! ### Property 1.5: the Schur decomposition -/

/-- **Property 1.5** of [quarteroni2000numerical] (Schur decomposition). For every
$A \in \mathbb{C}^{n \times n}$ there is a unitary matrix $U$, so that $U^{-1} = U^H$, such that
$$U^{-1} A U = U^H A U = T$$
is upper triangular. Then $A$ is unitarily similar to $T$, and the diagonal entries $t_{ii}$ of
$T$ are the eigenvalues of $A$: $p_A(\lambda) = \prod_i (\lambda - t_{ii})$ and
$\sigma(A) = \{t_{11}, \dots, t_{nn}\}$.

Here $p_A$ is Mathlib's `A.charpoly`, the polynomial $\det(\lambda I - A)$. The proof
specializes the backbone theorem `Matrix.exists_unitary_conj_upperTriangular`. -/
theorem property_1_5 (A : Matrix (Fin n) (Fin n) ℂ) :
    ∃ U ∈ unitaryGroup (Fin n) ℂ, U⁻¹ = star U ∧ (star U * A * U).IsUpperTriangular ∧
      IsUnitarilySimilar A (star U * A * U) ∧
      A.charpoly = ∏ i, (X - C ((star U * A * U) i i)) ∧
      spectrum ℂ A = Set.range fun i => (star U * A * U) i i := by
  obtain ⟨U, hU, hT, hp⟩ := exists_unitary_conj_upperTriangular A
  refine ⟨U, hU, inv_eq_left_inv (mem_unitaryGroup_iff'.1 hU), hT, ⟨U, hU, rfl⟩, hp, ?_⟩
  rw [(charpoly_eq_of_isSimilar (IsUnitarilySimilar.isSimilar ⟨U, hU, rfl⟩)).2.1,
    (spectrum_of_isTriangular (star U * A * U) 0).1 hT]

/-- A Hermitian upper triangular matrix $T \in \mathbb{C}^{n \times n}$ is diagonal: its entries
below the diagonal vanish, and the entries above the diagonal are their conjugates. This
supports consequence 1 of Property 1.5 of [quarteroni2000numerical], in
`QuarteroniSaccoSaleri.Chapter01.property_1_5_hermitian`. -/
theorem IsHermitian.isDiag_of_isUpperTriangular {T : Matrix (Fin n) (Fin n) ℂ}
    (hT : T.IsHermitian) (hU : T.IsUpperTriangular) : T.IsDiag := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · rw [← hT.apply i j, hU h, star_zero]
  · exact hU h

/-- **Section 1.8** of [quarteroni2000numerical], consequence 1 of the Schur decomposition. Let
$A \in \mathbb{C}^{n \times n}$ be Hermitian. Then there are a unitary matrix $U$ and real
numbers $\lambda_1, \dots, \lambda_n$ such that
$$U^H A U = \Lambda = \operatorname{diag}(\lambda_1, \dots, \lambda_n).$$
Moreover, for every unitary $V$ such that $V^H A V$ is upper triangular, $V^H A V$ is diagonal.
The relation $AU = U \Lambda$ holds, that is, $A u_i = \lambda_i u_i$ for the columns $u_i$ of
$U$. These columns are the eigenvectors of $A$; they are orthonormal, and they span
$\mathbb{C}^n$.

In Lean, `hA.eigenvectorUnitary` is $U$, `hA.eigenvalues` gives the eigenvalues, and
`hA.eigenvectorBasis` gives the columns $u_i$, from Mathlib's `Matrix.IsHermitian.spectral_theorem`.
The second clause uses
`QuarteroniSaccoSaleri.Chapter01.IsHermitian.isDiag_of_isUpperTriangular`. -/
theorem property_1_5_hermitian {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) :
    star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) * A * hA.eigenvectorUnitary =
        diagonal (fun i => (hA.eigenvalues i : ℂ)) ∧
      (∀ U ∈ unitaryGroup (Fin n) ℂ, (star U * A * U).IsUpperTriangular →
        (star U * A * U).IsDiag) ∧
      A * hA.eigenvectorUnitary =
        hA.eigenvectorUnitary * diagonal (fun i => (hA.eigenvalues i : ℂ)) ∧
      (∀ i, A *ᵥ (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)ᵀ i =
        (hA.eigenvalues i : ℂ) • (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)ᵀ i) ∧
      (∀ i, (hA.eigenvectorBasis i : Fin n → ℂ) =
        (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)ᵀ i) ∧
      Orthonormal ℂ hA.eigenvectorBasis ∧
      Submodule.span ℂ (Set.range hA.eigenvectorBasis) = ⊤ := by
  have hdiag : star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) * A * hA.eigenvectorUnitary
      = diagonal (fun i => (hA.eigenvalues i : ℂ)) := by
    have h := hA.conjStarAlgAut_star_eigenvectorUnitary
    rwa [Unitary.conjStarAlgAut_star_apply] at h
  have hU := hA.eigenvectorUnitary.2
  refine ⟨hdiag, fun U hU hT => IsHermitian.isDiag_of_isUpperTriangular
    (isHermitian_conjTranspose_mul_mul U hA) hT, ?_, fun i => ?_,
    fun i => (hA.eigenvectorUnitary_transpose_apply i).symm,
    hA.eigenvectorBasis.orthonormal, ?_⟩
  · rw [← hdiag, ← Matrix.mul_assoc, ← Matrix.mul_assoc, (mem_unitaryGroup_iff.1 hU),
      Matrix.one_mul]
  · rw [hA.eigenvectorUnitary_transpose_apply, hA.mulVec_eigenvectorBasis,
      RCLike.real_smul_eq_coe_smul (K := ℂ)]
    rfl
  · rw [← OrthonormalBasis.coe_toBasis, hA.eigenvectorBasis.toBasis.span_eq]

/-- **Section 1.8** of [quarteroni2000numerical], the last sentence of consequence 1 of the Schur
decomposition. A matrix $A \in \mathbb{C}^{n \times n}$ is similar to a diagonal matrix if and
only if there are $n$ linearly independent vectors $v_1, \dots, v_n$ and numbers
$d_1, \dots, d_n$ with $A v_j = d_j v_j$ for all $j$, that is, if and only if the eigenvectors
of $A$ form a basis of $\mathbb{C}^n$.

The proof is the backbone theorem `Matrix.isSimilar_diagonal_iff_exists_basis_eigenvectors`. -/
theorem property_1_5_diagonalizable_iff (A : Matrix (Fin n) (Fin n) ℂ) :
    (∃ d : Fin n → ℂ, IsSimilar A (diagonal d)) ↔
      ∃ (d : Fin n → ℂ) (v : Fin n → Fin n → ℂ), LinearIndependent ℂ v ∧
        ∀ j, A *ᵥ v j = d j • v j :=
  isSimilar_diagonal_iff_exists_basis_eigenvectors A

/-- **Section 1.8** of [quarteroni2000numerical], consequence 2 of the Schur decomposition. A matrix
$A \in \mathbb{C}^{n \times n}$ is normal if and only if it is unitarily similar to a diagonal
matrix. Consequently, a normal matrix $A$ has the **spectral decomposition**
$$A = U \Lambda U^H = \sum_{i=1}^n \lambda_i u_i u_i^H,$$
where $U$ is unitary with columns $u_i$, $\Lambda = \operatorname{diag}(\lambda_1, \dots,
\lambda_n)$, and $U^H A U = \Lambda$.

Normality is Mathlib's `IsStarNormal A`. The proof uses the backbone theorems
`Matrix.IsStarNormal.spectral_theorem` and `Matrix.IsStarNormal.eq_sum_smul_vecMulVec`. -/
theorem property_1_5_normal (A : Matrix (Fin n) (Fin n) ℂ) :
    (IsStarNormal A ↔ ∃ d : Fin n → ℂ, IsUnitarilySimilar A (diagonal d)) ∧
      (IsStarNormal A → ∃ U ∈ unitaryGroup (Fin n) ℂ, ∃ d : Fin n → ℂ,
        star U * A * U = diagonal d ∧ A = U * diagonal d * star U ∧
          A = ∑ i, d i • vecMulVec (Uᵀ i) (star (Uᵀ i))) := by
  refine ⟨?_, fun hA => ?_⟩
  · rw [IsStarNormal.spectral_theorem]
    exact ⟨fun ⟨U, hU, d, hd⟩ => ⟨d, U, hU, hd.symm⟩, fun ⟨d, U, hU, hd⟩ => ⟨U, hU, d, hd.symm⟩⟩
  · obtain ⟨U, hU, d, hd, hsum⟩ := hA.eq_sum_smul_vecMulVec
    refine ⟨U, hU, d, hd, ?_, hsum⟩
    rw [← hd, Matrix.mul_assoc, Matrix.mul_assoc, mem_unitaryGroup_iff.1 hU, Matrix.mul_one,
      ← Matrix.mul_assoc, mem_unitaryGroup_iff.1 hU, Matrix.one_mul]

/-- **Section 1.8** of [quarteroni2000numerical], consequence 3 of the Schur decomposition. Let
$A, B \in \mathbb{C}^{n \times n}$ be normal with $AB = BA$. Then there are a unitary matrix $U$
with columns $u_i$ and vectors $\lambda, \xi \in \mathbb{C}^n$ such that
$$U^H A U = \operatorname{diag}(\lambda), \qquad U^H B U = \operatorname{diag}(\xi), \qquad U^H
  (A + B) U = \operatorname{diag}(\lambda + \xi).$$
So every eigenvalue $\mu_i$ of $A + B$ is the sum $\lambda_i + \xi_i$ of the eigenvalues of $A$
and $B$ for the same eigenvector $u_i$: $(A + B) u_i = (\lambda_i + \xi_i) u_i$.

The proof uses the backbone theorem
`Matrix.IsStarNormal.exists_unitary_conj_diagonal_of_commute`. -/
theorem property_1_5_commute {A B : Matrix (Fin n) (Fin n) ℂ} (hA : IsStarNormal A)
    (hB : IsStarNormal B) (hAB : A * B = B * A) :
    ∃ U ∈ unitaryGroup (Fin n) ℂ, ∃ d e : Fin n → ℂ,
      star U * A * U = diagonal d ∧ star U * B * U = diagonal e ∧
        star U * (A + B) * U = diagonal (d + e) ∧
        ∀ i, (A + B) *ᵥ Uᵀ i = (d i + e i) • Uᵀ i := by
  obtain ⟨U, hU, d, e, hd, he⟩ := hA.exists_unitary_conj_diagonal_of_commute hB hAB
  have hsum : star U * (A + B) * U = diagonal (d + e) := by
    rw [Matrix.mul_add, Matrix.add_mul, hd, he, diagonal_add]
    rfl
  refine ⟨U, hU, d, e, hd, he, hsum, fun i => ?_⟩
  have hcol : (A + B) * U = U * diagonal (d + e) := by
    rw [← hsum, ← Matrix.mul_assoc, ← Matrix.mul_assoc, mem_unitaryGroup_iff.1 hU,
      Matrix.one_mul]
  have hl : ((A + B) * U)ᵀ i = (A + B) *ᵥ Uᵀ i := by
    ext r; simp [Matrix.mul_apply, mulVec, dotProduct]
  have hr : (U * diagonal (d + e))ᵀ i = (d i + e i) • Uᵀ i := by
    ext r; simp [mul_diagonal, mul_comm]
  rw [← hl, hcol, hr]

/-! ### Property 1.6: the Jordan canonical form -/

/-- **Property 1.6** of [quarteroni2000numerical] (canonical Jordan form). Every matrix
$A \in \mathbb{C}^{n \times n}$ is similar to a block diagonal matrix
$$X^{-1} A X = J = \operatorname{diag}(J_{k_1}(\lambda_1), \dots, J_{k_l}(\lambda_l))$$
with $X$ nonsingular, where the $\lambda_j$ are the eigenvalues of $A$ and
$J_k(\lambda) \in \mathbb{C}^{k \times k}$ is the **Jordan block** with $\lambda$ on the
diagonal, $1$ on the superdiagonal and $0$ elsewhere (so $J_1(\lambda) = \lambda$). In the
statement the blocks are grouped by eigenvalue: there are distinct numbers $\nu_1, \dots, \nu_q$
whose set is $\sigma(A)$, and for each $i$ a family of Jordan blocks of positive sizes for the
eigenvalue $\nu_i$.

The grouped form is the backbone theorem `Matrix.exists_conj_blockDiagonal'_jordanForm`. The
outer block of $\nu_i$ is `Matrix.jordanForm (e i) (fun _ => ν i)`, and the Jordan block is
`Matrix.jordanBlock k μ`. -/
theorem property_1_6 (A : Matrix (Fin n) (Fin n) ℂ) :
    (∃ (q : ℕ) (ν : Fin q → ℂ) (d : Fin q → ℕ) (e : ∀ i : Fin q, Fin (d i) → ℕ)
      (σ : ((i : Fin q) × (j : Fin (d i)) × Fin (e i j)) ≃ Fin n),
      Function.Injective ν ∧ (∀ μ, μ ∈ spectrum ℂ A ↔ μ ∈ Set.range ν) ∧ (∀ i j, 0 < e i j) ∧
        IsSimilar A (reindex σ σ (blockDiagonal' fun i => jordanForm (e i) fun _ => ν i))) ∧
      ∀ (k : ℕ) (μ : ℂ) (i j : Fin k),
        jordanBlock k μ i j = if i = j then μ else if (i : ℕ) + 1 = j then 1 else 0 := by
  obtain ⟨q, ν, d, e, σ, P, hinj, heig, hpos, hP, hPA⟩ := exists_conj_blockDiagonal'_jordanForm A
  exact ⟨⟨q, ν, d, e, σ, hinj, fun μ => (mem_spectrum_iff_exists_mulVec_eq_smul A μ).trans (heig μ),
    hpos, P, hP, hPA.symm⟩, fun k μ i j => jordanBlock_apply i j⟩

/-- **Section 1.8** of [quarteroni2000numerical], after Property 1.6. A matrix
$A \in \mathbb{C}^{n \times n}$ is similar to a diagonal matrix if and only if it is not
defective. For this reason nondefective matrices are called **diagonalizable**. In particular,
normal matrices are diagonalizable.

Defectiveness is `QuarteroniSaccoSaleri.Chapter01.IsDefective`. The proof uses the backbone
theorem `Matrix.isSimilar_diagonal_iff_forall_finrank_eigenspace_eq_rootMultiplicity`: since the
geometric multiplicity never exceeds the algebraic multiplicity
(`QuarteroniSaccoSaleri.Chapter01.finrank_eigenspace_le_rootMultiplicity`), no eigenvalue is
defective if and only if the two multiplicities are equal at every eigenvalue. -/
theorem property_1_6_diagonalizable_iff_nondefective (A : Matrix (Fin n) (Fin n) ℂ) :
    ((∃ d : Fin n → ℂ, IsSimilar A (diagonal d)) ↔ ¬ IsDefective A) ∧
      (IsStarNormal A → ∃ d : Fin n → ℂ, IsSimilar A (diagonal d)) := by
  refine ⟨?_, fun hA => ?_⟩
  · rw [isSimilar_diagonal_iff_forall_finrank_eigenspace_eq_rootMultiplicity, IsDefective]
    push Not
    constructor
    · exact fun h μ _ => (h μ).ge
    · intro h μ
      by_cases hμ : μ ∈ spectrum ℂ A
      · exact le_antisymm (finrank_eigenspace_le_rootMultiplicity A μ) (h μ hμ)
      · rw [Matrix.mem_spectrum_iff_isRoot_charpoly] at hμ
        rw [rootMultiplicity_eq_zero hμ]
        exact Nat.eq_zero_of_le_zero
          ((finrank_eigenspace_le_rootMultiplicity A μ).trans (rootMultiplicity_eq_zero hμ).le)
  · obtain ⟨d, hd⟩ := (property_1_5_normal A).1.1 hA
    exact ⟨d, hd.isSimilar⟩

/-- The column `c` of a matrix reindexed by `σ.symm` is the column `σ c` of the original,
composed with `σ`. -/
private theorem transpose_reindex_symm_apply {ι : Type*} (X : Matrix (Fin n) (Fin n) ℂ)
    (σ : ι ≃ Fin n) (c : ι) : (reindex σ.symm σ.symm X)ᵀ c = Xᵀ (σ c) ∘ σ := rfl

/-- A matrix reindexed by `σ.symm` acts on a reindexed vector as the original matrix does. -/
private theorem reindex_symm_mulVec {ι : Type*} [Fintype ι] (M : Matrix (Fin n) (Fin n) ℂ)
    (σ : ι ≃ Fin n) (v : Fin n → ℂ) :
    reindex σ.symm σ.symm M *ᵥ (v ∘ σ) = (M *ᵥ v) ∘ σ := by
  rw [reindex_apply, Equiv.symm_symm, submatrix_mulVec_equiv]
  congr 2
  ext r
  simp

/-- **Equation (1.8)** of [quarteroni2000numerical], the principal vectors. Let
$A, X \in \mathbb{C}^{n \times n}$ with $X$ nonsingular and $X^{-1} A X = J$ a Jordan form with
blocks $J_{k_i}(\lambda_i)$, and partition $X$ by columns. Let $x_1, \dots, x_{k_i}$ be the
columns of $X$ that belong to the block $J_{k_i}(\lambda_i)$. Then
$$A x_1 = \lambda_i x_1, \qquad A x_j = \lambda_i x_j + x_{j-1} \quad (j = 2, \dots, k_i).$$
These columns are the **principal vectors**, or **generalized eigenvectors**, of $A$.

The Jordan form is `reindex σ σ (jordanForm e μ)` for an equivalence `σ` of the block indices
with `Fin n`, and the column at position $j$ (0-based) of the block $i$ is `Xᵀ (σ ⟨i, j⟩)`. The
proof transports the backbone theorem `Matrix.mulVec_eq_of_conj_jordanForm` along `σ`. -/
theorem equation_1_8 {ι : Type*} [Finite ι] [DecidableEq ι] {e : ι → ℕ} {μ : ι → ℂ}
    {A X : Matrix (Fin n) (Fin n) ℂ} (σ : ((i : ι) × Fin (e i)) ≃ Fin n) (hX : IsUnit X)
    (h : X⁻¹ * A * X = reindex σ σ (jordanForm e μ)) :
    (∀ (i : ι) (h0 : 0 < e i),
        A *ᵥ Xᵀ (σ ⟨i, ⟨0, h0⟩⟩) = μ i • Xᵀ (σ ⟨i, ⟨0, h0⟩⟩)) ∧
      ∀ (i : ι) (j : ℕ) (hj : j + 1 < e i),
        A *ᵥ Xᵀ (σ ⟨i, ⟨j + 1, hj⟩⟩) =
          μ i • Xᵀ (σ ⟨i, ⟨j + 1, hj⟩⟩) + Xᵀ (σ ⟨i, ⟨j, by omega⟩⟩) := by
  cases nonempty_fintype ι
  have key : ∀ M : Matrix (Fin n) (Fin n) ℂ,
      reindex σ.symm σ.symm M = reindexAlgEquiv ℂ ℂ σ.symm M := fun _ => rfl
  have hX' : IsUnit (reindex σ.symm σ.symm X) := by rw [key]; exact hX.map _
  have h' : (reindex σ.symm σ.symm X)⁻¹ * reindex σ.symm σ.symm A * reindex σ.symm σ.symm X
      = jordanForm e μ := by
    rw [inv_reindex, key, key, key, ← map_mul, ← map_mul, ← key, h, ← reindex_symm,
      Equiv.symm_apply_apply]
  obtain ⟨h0, hsucc⟩ := mulVec_eq_of_conj_jordanForm hX' h'
  refine ⟨fun i hi => funext fun r => ?_, fun i j hj => funext fun r => ?_⟩
  · have := congrFun (h0 i hi) (σ.symm r)
    simp only [transpose_reindex_symm_apply, reindex_symm_mulVec] at this
    simpa using this
  · have := congrFun (hsucc i j hj) (σ.symm r)
    simp only [transpose_reindex_symm_apply, reindex_symm_mulVec] at this
    simpa using this

/-! ### Example 1.6 -/

/-- **Example 1.6** of [quarteroni2000numerical], the matrix
$$A = \frac14 \begin{bmatrix} 7 & 3 & -1 & -1 & -1 & 1 \\ 0 & 8 & 0 & 0 & 0 & 0 \\ -2 & -2 & 10
  & 2 & -2 & 2 \\ -2 & -2 & -2 & 10 & 2 & 2 \\ -1 & -1 & -1 & -1 & 11 & 1 \\ -6 & -2 & -2 & 2 &
  2 & 14 \end{bmatrix}.$$
-/
def example_1_6_A : Matrix (Fin 6) (Fin 6) ℚ :=
  !![7/4, 3/4, -1/4, -1/4, -1/4, 1/4;
     0, 2, 0, 0, 0, 0;
     -1/2, -1/2, 5/2, 1/2, -1/2, 1/2;
     -1/2, -1/2, -1/2, 5/2, 1/2, 1/2;
     -1/4, -1/4, -1/4, -1/4, 11/4, 1/4;
     -3/2, -1/2, -1/2, 1/2, 1/2, 7/2]

/-- **Example 1.6** of [quarteroni2000numerical], the Jordan canonical form $J =
\operatorname{diag}(J_2(2), J_3(3), J_1(2))$ of the matrix $A$, a $6 \times 6$ rational matrix. -/
def example_1_6_J : Matrix (Fin 6) (Fin 6) ℚ :=
  !![2, 1, 0, 0, 0, 0; 0, 2, 0, 0, 0, 0; 0, 0, 3, 1, 0, 0; 0, 0, 0, 3, 1, 0;
     0, 0, 0, 0, 3, 0; 0, 0, 0, 0, 0, 2]

/-- **Example 1.6** of [quarteroni2000numerical], the transforming matrix
$$X = \begin{bmatrix} 1 & 0 & 0 & 0 & 0 & 1 \\ 0 & 1 & 0 & 0 & 0 & 1 \\ 0 & 0 & 1 & 0 & 0 & 1 \\
  0 & 0 & 0 & 1 & 0 & 1 \\ 0 & 0 & 0 & 0 & 1 & 1 \\ 1 & 1 & 1 & 1 & 1 & 1 \end{bmatrix}.$$
-/
def example_1_6_X : Matrix (Fin 6) (Fin 6) ℚ :=
  !![1, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 1;
     0, 0, 0, 0, 1, 1; 1, 1, 1, 1, 1, 1]

/-- **Example 1.6** of [quarteroni2000numerical], the inverse of the matrix $X$:
$$X^{-1} = \frac14 \begin{bmatrix} 4I - E & e \\ e^T & -1 \end{bmatrix},$$
where $E$ is the $5 \times 5$ matrix of ones and $e \in \mathbb{Q}^5$ is the vector of ones.

The formula follows from the Schur complement $1 - e^T e = -4$ of $X$. -/
def example_1_6_Xinv : Matrix (Fin 6) (Fin 6) ℚ :=
  !![3/4, -1/4, -1/4, -1/4, -1/4, 1/4;
     -1/4, 3/4, -1/4, -1/4, -1/4, 1/4;
     -1/4, -1/4, 3/4, -1/4, -1/4, 1/4;
     -1/4, -1/4, -1/4, 3/4, -1/4, 1/4;
     -1/4, -1/4, -1/4, -1/4, 3/4, 1/4;
     1/4, 1/4, 1/4, 1/4, 1/4, -1/4]

/-- **Example 1.6** of [quarteroni2000numerical], the layout of the three Jordan blocks of sizes
$2$, $3$ and $1$, one after the other along the diagonal of a $6 \times 6$ matrix. It is an
equivalence between the block indices $(i, j)$ with $j < k_i$ and the indices `Fin 6`. -/
def example_1_6_equiv : ((i : Fin 3) × Fin (![2, 3, 1] i)) ≃ Fin 6 :=
  finSigmaFinEquiv.trans (finCongr (by decide))

/-- **Example 1.6** of [quarteroni2000numerical]. For the matrices $A$, $X$ and $J$ of the example,
$AX = XJ$, the matrix $X$ is nonsingular with inverse the matrix $X^{-1}$ above, and
$$X^{-1} A X = J = \operatorname{diag}(J_2(2), J_3(3), J_1(2)),$$
in which two different Jordan blocks belong to the same eigenvalue $2$. For the block of the
eigenvalue $3$, the columns $x_3, x_4, x_5$ of $X$ (the third, fourth and fifth columns) satisfy
(1.8):
$$A x_3 = (0, 0, 3, 0, 0, 3)^T = 3 x_3, \quad A x_4 = (0, 0, 1, 3, 0, 4)^T = 3 x_4 + x_3, \quad
  A x_5 = (0, 0, 0, 1, 3, 4)^T = 3 x_5 + x_4.$$

The matrices have rational entries, and all identities are checked by computation. The Jordan
form $J$ is `jordanForm ![2, 3, 1] ![2, 3, 2]` reindexed along
`QuarteroniSaccoSaleri.Chapter01.example_1_6_equiv`. The columns of $X$ are 0-based in Lean:
$x_3$ is `example_1_6_Xᵀ 2`. -/
theorem example_1_6 :
    example_1_6_A * example_1_6_X = example_1_6_X * example_1_6_J ∧
      example_1_6_X * example_1_6_Xinv = 1 ∧ IsUnit example_1_6_X ∧
      example_1_6_X⁻¹ = example_1_6_Xinv ∧
      example_1_6_X⁻¹ * example_1_6_A * example_1_6_X = example_1_6_J ∧
      example_1_6_J =
        reindex example_1_6_equiv example_1_6_equiv (jordanForm ![2, 3, 1] ![2, 3, 2]) ∧
      (example_1_6_A *ᵥ example_1_6_Xᵀ 2 = ![0, 0, 3, 0, 0, 3] ∧
        example_1_6_A *ᵥ example_1_6_Xᵀ 2 = (3 : ℚ) • example_1_6_Xᵀ 2) ∧
      (example_1_6_A *ᵥ example_1_6_Xᵀ 3 = ![0, 0, 1, 3, 0, 4] ∧
        example_1_6_A *ᵥ example_1_6_Xᵀ 3 = (3 : ℚ) • example_1_6_Xᵀ 3 + example_1_6_Xᵀ 2) ∧
      (example_1_6_A *ᵥ example_1_6_Xᵀ 4 = ![0, 0, 0, 1, 3, 4] ∧
        example_1_6_A *ᵥ example_1_6_Xᵀ 4 = (3 : ℚ) • example_1_6_Xᵀ 4 + example_1_6_Xᵀ 3) := by
  have hAX : example_1_6_A * example_1_6_X = example_1_6_X * example_1_6_J := by decide +kernel
  have hXY : example_1_6_X * example_1_6_Xinv = 1 := by decide +kernel
  have hX : IsUnit example_1_6_X :=
    (isUnit_iff_isUnit_det _).2 (isUnit_det_of_right_inverse hXY)
  refine ⟨hAX, hXY, hX, inv_eq_right_inv hXY, ?_, by decide +kernel,
    ⟨by decide +kernel, by decide +kernel⟩, ⟨by decide +kernel, by decide +kernel⟩,
    ⟨by decide +kernel, by decide +kernel⟩⟩
  rw [Matrix.mul_assoc, hAX, ← Matrix.mul_assoc,
    nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hX), Matrix.one_mul]

end QuarteroniSaccoSaleri.Chapter01
