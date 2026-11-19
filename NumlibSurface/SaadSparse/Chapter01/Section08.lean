/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Numlib.Analysis.Normed.Module.NormEquivalence
import Numlib.LinearAlgebra.Eigenspace.Spectral
import Numlib.LinearAlgebra.Matrix.Complexify
import Numlib.LinearAlgebra.Matrix.Jordan
import Numlib.LinearAlgebra.Matrix.RealSchur
import Numlib.LinearAlgebra.Matrix.Schur
import Numlib.LinearAlgebra.Matrix.Similar

/-!
# Saad, Section 1.8: Canonical forms of matrices

This module formalizes §1.8 of [saad2003iterative]: similarity and the canonical forms of a square
matrix, namely the diagonal form (§1.8.1), the Jordan form (§1.8.2) and the Schur form (§1.8.3), and
their application to powers of matrices (§1.8.4). Two matrices $A$ and $B$ are similar when
$B = X^{-1} A X$ for a nonsingular $X$. The module proves that $A$ is diagonalizable exactly when it
has $n$ linearly independent eigenvectors, and over $\mathbb{C}$ exactly when every eigenvalue is
semisimple. It proves the Jordan canonical form with the identification of its block sizes, the
complex Schur form, the real (quasi-Schur) form, and the three results on powers: $A^k \to 0$ if and
only if $\rho(A) < 1$, the Neumann series $\sum_k A^k$ converges if and only if $\rho(A) < 1$, and
Gelfand's formula $\|A^k\|^{1/k} \to \rho(A)$.

The proofs specialize the backbone modules `Numlib.LinearAlgebra.Matrix.Similar`,
`Numlib.LinearAlgebra.Matrix.Jordan`, `Numlib.LinearAlgebra.Matrix.Schur`,
`Numlib.LinearAlgebra.Matrix.RealSchur`, `Numlib.LinearAlgebra.Matrix.Complexify` and
`Numlib.Analysis.Normed.Module.NormEquivalence`.

## Main results

* Theorem 1.6, `SaadSparse.Chapter01.theorem_1_6`: a matrix is diagonalizable if and only if it has
  $n$ linearly independent eigenvectors.
* Proposition 1.7, `SaadSparse.Chapter01.diagonalizable_of_injective_eigenvalues`: a matrix with $n$
  eigenvectors for $n$ distinct eigenvalues is diagonalizable.
* Proposition 1.7, `SaadSparse.Chapter01.proposition_1_7`: a complex matrix is diagonalizable if and
  only if every eigenvalue is semisimple.
* Theorem 1.8, `SaadSparse.Chapter01.theorem_1_8`: every complex matrix is similar to a block
  diagonal matrix of Jordan blocks, grouped by the distinct eigenvalues.
* Theorem 1.8, `SaadSparse.Chapter01.theorem_1_8_geometricMultiplicity`: the number of Jordan blocks
  for an eigenvalue is its geometric multiplicity.
* Theorem 1.8, `SaadSparse.Chapter01.theorem_1_8_algebraicMultiplicity`: the total size of the
  Jordan blocks for an eigenvalue is its algebraic multiplicity.
* Theorem 1.8, `SaadSparse.Chapter01.theorem_1_8_index`: the Jordan blocks for an eigenvalue have
  size at most its index, and the index is at most the algebraic multiplicity.
* Theorem 1.9, `SaadSparse.Chapter01.theorem_1_9`: every complex matrix is unitarily similar to an
  upper triangular matrix, whose diagonal carries the eigenvalues.
* Theorem 1.9, `SaadSparse.Chapter01.theorem_1_9_partial`: the span of the first $k$ Schur vectors
  is invariant under $A$.
* §1.8.3, `SaadSparse.Chapter01.realSchur`: every real matrix is orthogonally similar to a block
  upper triangular matrix with diagonal blocks of size $1 \times 1$ or $2 \times 2$.
* Theorem 1.10, `SaadSparse.Chapter01.theorem_1_10`: $A^k \to 0$ if and only if $\rho(A) < 1$.
* Theorem 1.11, `SaadSparse.Chapter01.theorem_1_11`: the series $\sum_k A^k$ converges if and only
  if $\rho(A) < 1$.
* Theorem 1.11, `SaadSparse.Chapter01.theorem_1_11_isUnit`: if $\rho(A) < 1$, then $I - A$ is
  nonsingular.
* Theorem 1.12, `SaadSparse.Chapter01.theorem_1_12`: Gelfand's formula
  $\|A^k\|_2^{1/k} \to \rho(A)$.
* Theorem 1.12, `SaadSparse.Chapter01.theorem_1_12_norm`: Gelfand's formula for an arbitrary matrix
  norm.

## Implementation notes

* Similarity is `Matrix.IsSimilar A B`, which means $B = C^{-1} A C$ for a nonsingular $C$; this is
  the book's $A = X B X^{-1}$ (Definition 1.5) with $X = C$. The backbone module
  `Numlib.LinearAlgebra.Matrix.Similar` proves that similarity is an equivalence relation, that it
  transports eigenvectors and preserves the characteristic polynomial (Problem P-1.9), and the
  criterion for diagonalizability behind Theorem 1.6.
* The vocabulary of multiplicities in the section (algebraic and geometric multiplicity, simple,
  semisimple, defective and derogatory eigenvalues) is Mathlib's `Module.End.eigenspace`,
  `Module.End.maxGenEigenspace` and `Polynomial.rootMultiplicity` of the characteristic polynomial,
  and has no definition here. The index of an eigenvalue $\lambda$ is written out where it is used,
  as the least $k$ at which $\operatorname{Null}((A - \lambda I)^k)$ stops growing.
* Mathlib has no Jordan form; the backbone module `Numlib.LinearAlgebra.Matrix.Jordan` constructs
  it. Theorem 1.8 states a block structure and then identifies three numbers in it.
  `SaadSparse.Chapter01.theorem_1_8` is the block structure. The identifications are three separate
  statements about a decomposition of that shape, so that a user can use the structure without the
  arithmetic, and the arithmetic without unpacking the structure.
* The book derives Theorems 1.10 and 1.11 from the Jordan form. The backbone module
  `Numlib.LinearAlgebra.Matrix.Complexify` proves them from Gelfand's formula instead, which needs
  less. Theorems 1.10, 1.11 and 1.12 are backbone results in a stronger form, restated here in the
  words of the book.
* Theorem 1.12 has two forms. `SaadSparse.Chapter01.theorem_1_12` uses the Euclidean operator norm,
  for which the backbone proves it. `SaadSparse.Chapter01.theorem_1_12_norm` holds for an arbitrary
  matrix norm, as the book states it with the proof deferred to Problem P-1.10. The second form
  follows from the first because all norms on a finite-dimensional space are equivalent and the
  equivalence constants disappear under a $k$-th root. No consistency condition on the norm is used.

## Deviations from the source

* **Theorem 1.6 and the corollary to Proposition 1.7** (generalization). Both statements also
  cover real eigenvalues and vectors over the real field. See `SaadSparse.Chapter01.theorem_1_6`
  and `SaadSparse.Chapter01.diagonalizable_of_injective_eigenvalues`.
* **Theorem 1.8, the sentence after the block display** (correction). Individual Jordan blocks
  can have different sizes. The index bounds every block size. See
  `SaadSparse.Chapter01.theorem_1_8_index`.
* **§1.8.3, partial Schur decomposition** (reading). The declaration states invariance of the
  column span. If $k>n$, the index condition selects all columns. See
  `SaadSparse.Chapter01.theorem_1_9_partial`.
* **§1.8.3, real Schur form** (reading). The declaration asserts the block shape only. See
  `SaadSparse.Chapter01.realSchur`.
* **Theorem 1.10** (reading). The chapter works over $\mathbb{C}$ by default. This declaration
  treats real matrices using their complex spectral radius. See `SaadSparse.Chapter01.theorem_1_10`.
* **Theorem 1.11** (reading). The summability equivalence uses positive dimension. The separate
  nonsingularity theorem treats real matrices. See `SaadSparse.Chapter01.theorem_1_11` and
  `SaadSparse.Chapter01.theorem_1_11_isUnit`.
* **Theorem 1.12** (reading and generalization). The statement concerns real matrices and allows
  every norm on that space. See `SaadSparse.Chapter01.theorem_1_12_norm` and its Euclidean case
  `SaadSparse.Chapter01.theorem_1_12`.

## Not formalized

* **§1.8.3, the spectra of the $2 \times 2$ real Schur blocks.** The theorem records only the
  block sizes and the vanishing entries below the blocks.
* **Theorem 1.11, the value of the sum.** The surface states summability and nonsingularity
  separately. The real-matrix identity is available as
  `Matrix.hasSum_pow_inv_one_sub_of_complexSpectralRadius_lt_one`.
-/

open Matrix Filter Topology
open scoped ENNReal

namespace SaadSparse.Chapter01

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

/-! ### §1.8.1 Theorem 1.6: diagonalizability -/

/-- **Theorem 1.6** of [saad2003iterative]. Let $A \in \mathbb{K}^{n \times n}$, where $\mathbb{K}$
is $\mathbb{R}$ or $\mathbb{C}$. Then $A$ is **diagonalizable**, that is similar to a diagonal
matrix $\operatorname{diag}(d)$ with $d \in \mathbb{K}^n$, if and only if there are
$d \in \mathbb{K}^n$ and linearly independent vectors $v_1, \dots, v_n \in \mathbb{K}^n$ with
$$A v_j = d_j v_j \quad \text{for all } j.$$

**Generalization.** The chapter works over $\mathbb{C}$ by default. The same basis criterion
also holds over $\mathbb{R}$, with eigenvalues in the field of the vectors.

Both directions read the relation $AX = XD$ column by column: the columns of the transforming
matrix $X$ are the eigenvectors, and $X$ is nonsingular exactly when they are linearly
independent. The proof is the backbone's
`Matrix.isSimilar_diagonal_iff_exists_basis_eigenvectors`. -/
theorem theorem_1_6 (A : Matrix (Fin n) (Fin n) 𝕜) :
    (∃ d : Fin n → 𝕜, IsSimilar A (Matrix.diagonal d)) ↔
      ∃ (d : Fin n → 𝕜) (v : Fin n → Fin n → 𝕜),
        LinearIndependent 𝕜 v ∧ ∀ j, A *ᵥ v j = d j • v j :=
  Matrix.isSimilar_diagonal_iff_exists_basis_eigenvectors A

/-- **Proposition 1.7** of [saad2003iterative], corollary (Problem P-1.2). Let
$A \in \mathbb{K}^{n \times n}$, where $\mathbb{K}$ is $\mathbb{R}$ or $\mathbb{C}$, let
$d_1, \dots, d_n \in \mathbb{K}$ be pairwise distinct, and let
$v_1, \dots, v_n \in \mathbb{K}^n$ be nonzero vectors with $A v_j = d_j v_j$ for every $j$. Then
$A$ is diagonalizable.

**Generalization.** The chapter states the corollary over $\mathbb{C}$. The declaration also uses
real scalars when the eigenvalues and eigenvectors are real.

Eigenvectors that belong to distinct eigenvalues are linearly independent, so this follows from
`SaadSparse.Chapter01.theorem_1_6`. -/
theorem diagonalizable_of_injective_eigenvalues {A : Matrix (Fin n) (Fin n) 𝕜} {d : Fin n → 𝕜}
    (hd : Function.Injective d) {v : Fin n → Fin n → 𝕜} (hv : ∀ j, v j ≠ 0)
    (hAv : ∀ j, A *ᵥ v j = d j • v j) : ∃ e : Fin n → 𝕜, IsSimilar A (Matrix.diagonal e) :=
  (theorem_1_6 A).2 ⟨d, v, Module.End.eigenvectors_linearIndependent' A.mulVecLin d hd v
    fun j => ⟨Module.End.mem_eigenspace_iff.2 (hAv j), hv j⟩, hAv⟩

/-! ### §1.8.1 Proposition 1.7: semisimple eigenvalues -/

/-- **Proposition 1.7** of [saad2003iterative]. Let $A \in \mathbb{C}^{n \times n}$. Then $A$ is
diagonalizable if and only if every eigenvalue of $A$ is **semisimple**: for every
$\mu \in \mathbb{C}$, the eigenspace of $A$ for $\mu$ equals the maximal generalized eigenspace
of $A$ for $\mu$. Equivalently, the geometric and the algebraic multiplicity of every eigenvalue
agree.

One direction holds because the generalized eigenspaces always span the space over an
algebraically closed field. The other holds because a spanning family of eigenspaces leaves no
room for a defective eigenvalue. The corollary of the book, that $n$ distinct eigenvalues force
diagonalizability, is `SaadSparse.Chapter01.diagonalizable_of_injective_eigenvalues`. -/
theorem proposition_1_7 (A : Matrix (Fin n) (Fin n) ℂ) :
    (∃ d : Fin n → ℂ, IsSimilar A (Matrix.diagonal d)) ↔
      ∀ μ : ℂ, Module.End.eigenspace A.mulVecLin μ =
        Module.End.maxGenEigenspace A.mulVecLin μ := by
  rw [Matrix.isSimilar_diagonal_iff_iSup_eigenspace_eq_top]
  constructor
  · exact fun hsup μ =>
      (Module.End.maxGenEigenspace_eq_eigenspace_of_iSup_eigenspace_eq_top hsup μ).symm
  · intro hss
    calc (⨆ μ : ℂ, Module.End.eigenspace A.mulVecLin μ)
        = ⨆ μ : ℂ, Module.End.maxGenEigenspace A.mulVecLin μ := iSup_congr hss
      _ = ⊤ := Module.End.iSup_maxGenEigenspace_eq_top _

/-! ### §1.8.2 Theorem 1.8: the Jordan canonical form -/

/-- **Theorem 1.8** of [saad2003iterative] (Jordan canonical form). Let
$A \in \mathbb{C}^{n \times n}$. Then there are a number $p$, pairwise distinct scalars
$\lambda_1, \dots, \lambda_p \in \mathbb{C}$, numbers $\gamma_1, \dots, \gamma_p$ and positive
sizes $l_{ik}$ for $k = 1, \dots, \gamma_i$, such that:

* the eigenvalues of $A$ are exactly $\lambda_1, \dots, \lambda_p$;
* $A$ is similar to the block diagonal matrix $J = \operatorname{diag}(J_1, \dots, J_p)$, where
  $J_i$ is itself block diagonal with the $\gamma_i$ Jordan blocks $J_{ik}$ of size $l_{ik}$ for
  $\lambda_i$.

A Jordan block $J_{ik}$ is upper bidiagonal, with the constant $\lambda_i$ on the diagonal and
the constant $1$ on the superdiagonal. Thus $X^{-1} A X = J$ for a nonsingular $X$.

The block $J_i$ is `Matrix.jordanForm (l i) (fun _ => lam i)`, and its Jordan blocks are
`Matrix.jordanBlock (l i k) (lam i)`. The equivalence `σ` names the indices of the block
diagonal matrix by `Fin n`; reindexing by it is a permutation similarity. The further
identifications of the numbers in the book are three separate statements about a decomposition
of this shape: $\gamma_i$ is the geometric multiplicity of $\lambda_i$
(`SaadSparse.Chapter01.theorem_1_8_geometricMultiplicity`), the block $J_i$ has size the
algebraic multiplicity $m_i$ of $\lambda_i$
(`SaadSparse.Chapter01.theorem_1_8_algebraicMultiplicity`), and the Jordan blocks have size at
most the index $l_i$ of $\lambda_i$, which is at most $m_i$
(`SaadSparse.Chapter01.theorem_1_8_index`). -/
theorem theorem_1_8 (A : Matrix (Fin n) (Fin n) ℂ) :
    ∃ (p : ℕ) (lam : Fin p → ℂ) (γ : Fin p → ℕ) (l : ∀ i : Fin p, Fin (γ i) → ℕ)
      (σ : ((i : Fin p) × (k : Fin (γ i)) × Fin (l i k)) ≃ Fin n),
      Function.Injective lam ∧ (∀ μ : ℂ, (∃ v ≠ 0, A *ᵥ v = μ • v) ↔ μ ∈ Set.range lam) ∧
        (∀ i k, 0 < l i k) ∧
        IsSimilar A (Matrix.reindex σ σ
          (Matrix.blockDiagonal' fun i => Matrix.jordanForm (l i) (fun _ => lam i))) := by
  obtain ⟨p, lam, γ, l, σ, P, hinj, heig, hlpos, hP, hPA⟩ :=
    Matrix.exists_conj_blockDiagonal'_jordanForm A
  exact ⟨p, lam, γ, l, σ, hinj, heig, hlpos, P, hP, hPA.symm⟩

/-- If $A$ is similar to a Jordan form as in Theorem 1.8 with pairwise distinct $\lambda_i$, then
for every $k$ the dimension of $\operatorname{Null}((A - \lambda_i I)^k)$ equals the dimension
of the kernel of $(J_i - \lambda_i I)^k$, since the other diagonal blocks carry other
eigenvalues. -/
private theorem finrank_ker_pow_sub_smul_one_of_jordan {A : Matrix (Fin n) (Fin n) ℂ} {p : ℕ}
    {lam : Fin p → ℂ} {γ : Fin p → ℕ} {l : ∀ i : Fin p, Fin (γ i) → ℕ}
    {σ : ((i : Fin p) × (k : Fin (γ i)) × Fin (l i k)) ≃ Fin n} (hinj : Function.Injective lam)
    (hA : IsSimilar A (Matrix.reindex σ σ
      (Matrix.blockDiagonal' fun i => Matrix.jordanForm (l i) (fun _ => lam i))))
    (i : Fin p) (k : ℕ) :
    Module.finrank ℂ (LinearMap.ker (((A - lam i • 1) ^ k).mulVecLin))
      = Module.finrank ℂ (LinearMap.ker
          (((Matrix.jordanForm (l i) (fun _ => lam i) - lam i • 1) ^ k).mulVecLin)) := by
  classical
  set J : Matrix ((i : Fin p) × (k : Fin (γ i)) × Fin (l i k))
      ((i : Fin p) × (k : Fin (γ i)) × Fin (l i k)) ℂ :=
    Matrix.blockDiagonal' fun i => Matrix.jordanForm (l i) (fun _ => lam i) with hJ
  have hre : (Matrix.reindex σ σ J - lam i • 1) ^ k
      = Matrix.reindex σ σ ((J - lam i • 1) ^ k) := by
    simp only [← Matrix.coe_reindexAlgEquiv ℂ ℂ σ]
    rw [← map_one (Matrix.reindexAlgEquiv ℂ ℂ σ), ← map_smul, ← map_sub, ← map_pow]
  rw [((hA.sub_smul_one (lam i)).pow k).finrank_ker_mulVecLin_eq, hre,
    Matrix.finrank_ker_mulVecLin_reindex, hJ, Matrix.blockDiagonal'_sub_smul_one,
    ← Matrix.blockDiagonal'_pow, Matrix.finrank_ker_mulVecLin_blockDiagonal']
  refine Finset.sum_eq_single i (fun j _ hj => ?_) (fun h => absurd (Finset.mem_univ i) h)
  rw [show ((fun j => Matrix.jordanForm (l j) (fun _ => lam j) - lam i • 1) ^ k) j
      = (Matrix.jordanForm (l j) (fun _ => lam j) - lam i • 1) ^ k from rfl,
    Matrix.finrank_ker_mulVecLin_jordanForm_sub_smul_one_pow,
    Finset.filter_false_of_mem fun _ _ (h : lam j = lam i) => hj (hinj h), Finset.sum_empty]

/-- **Theorem 1.8** of [saad2003iterative], geometric multiplicity. Let
$A \in \mathbb{C}^{n \times n}$ be similar to a Jordan form as in
`SaadSparse.Chapter01.theorem_1_8`, with pairwise distinct eigenvalues
$\lambda_1, \dots, \lambda_p$ and Jordan blocks of positive sizes $l_{ik}$. Then for every $i$
the number $\gamma_i$ of Jordan blocks for $\lambda_i$ is the geometric multiplicity of
$\lambda_i$:
$$\dim \operatorname{Null}(A - \lambda_i I) = \gamma_i.$$

Each Jordan block "corresponds to a different eigenvector associated with the eigenvalue" and
contributes exactly one dimension. -/
theorem theorem_1_8_geometricMultiplicity {A : Matrix (Fin n) (Fin n) ℂ} {p : ℕ}
    {lam : Fin p → ℂ} {γ : Fin p → ℕ} {l : ∀ i : Fin p, Fin (γ i) → ℕ}
    {σ : ((i : Fin p) × (k : Fin (γ i)) × Fin (l i k)) ≃ Fin n} (hinj : Function.Injective lam)
    (hlpos : ∀ i k, 0 < l i k)
    (hA : IsSimilar A (Matrix.reindex σ σ
      (Matrix.blockDiagonal' fun i => Matrix.jordanForm (l i) (fun _ => lam i))))
    (i : Fin p) :
    Module.finrank ℂ (Module.End.eigenspace A.mulVecLin (lam i)) = γ i := by
  classical
  have h := finrank_ker_pow_sub_smul_one_of_jordan hinj hA i 1
  rw [pow_one, pow_one] at h
  rw [Matrix.eigenspace_mulVecLin_eq_ker, h,
    Matrix.finrank_ker_mulVecLin_jordanForm_sub_smul_one (hlpos i) (fun _ => lam i) (lam i),
    Finset.filter_true_of_mem fun _ _ => rfl, Finset.card_univ, Fintype.card_fin]

/-- **Theorem 1.8** of [saad2003iterative], algebraic multiplicity. Let
$A \in \mathbb{C}^{n \times n}$ be similar to a Jordan form as in
`SaadSparse.Chapter01.theorem_1_8`, with pairwise distinct $\lambda_1, \dots, \lambda_p$. Then
for every $i$ the block $J_i$ has size the algebraic multiplicity $m_i$ of $\lambda_i$, the
multiplicity of $\lambda_i$ as a root of the characteristic polynomial of $A$:
$$m_i = \sum_k l_{ik}.$$

The size of $J_i$ is the total size $\sum_k l_{ik}$ of its Jordan blocks. The statement does not
need the sizes $l_{ik}$ to be positive. -/
theorem theorem_1_8_algebraicMultiplicity {A : Matrix (Fin n) (Fin n) ℂ} {p : ℕ}
    {lam : Fin p → ℂ} {γ : Fin p → ℕ} {l : ∀ i : Fin p, Fin (γ i) → ℕ}
    {σ : ((i : Fin p) × (k : Fin (γ i)) × Fin (l i k)) ≃ Fin n} (hinj : Function.Injective lam)
    (hA : IsSimilar A (Matrix.reindex σ σ
      (Matrix.blockDiagonal' fun i => Matrix.jordanForm (l i) (fun _ => lam i))))
    (i : Fin p) :
    A.charpoly.rootMultiplicity (lam i) = ∑ k, l i k := by
  classical
  have hcp : A.charpoly = (Matrix.jordanForm (fun j => ∑ k, l j k) lam).charpoly := by
    rw [Matrix.charpoly_jordanForm, hA.charpoly_eq, Matrix.charpoly_reindex,
      Matrix.charpoly_blockDiagonal']
    exact Finset.prod_congr rfl fun j _ => by
      rw [Matrix.charpoly_jordanForm, Finset.prod_pow_eq_pow_sum]
  have hfilter : (Finset.univ.filter fun j => lam j = lam i) = {i} := by
    ext j
    simp [hinj.eq_iff]
  rw [hcp, Matrix.rootMultiplicity_charpoly_jordanForm, hfilter, Finset.sum_singleton]

/-- **Theorem 1.8** of [saad2003iterative], index. Let $A \in \mathbb{C}^{n \times n}$ be similar to
a Jordan form as in `SaadSparse.Chapter01.theorem_1_8`, with pairwise distinct
$\lambda_1, \dots, \lambda_p$. Then for every $i$ there is a least integer $L \ge 0$ with
$$\operatorname{Null}((A - \lambda_i I)^{L+1}) = \operatorname{Null}((A - \lambda_i I)^L),$$
the **index** of $\lambda_i$, and every Jordan block for $\lambda_i$ has size $l_{ik} \le L$,
and $L \le m_i = \sum_k l_{ik}$.

**Correction.** The sentence after the block display assigns the index to each individual block.
For $A = J_2(0) \oplus J_1(0)$, the index at zero is $2$ and one block has size $1$. The theorem
states the upper bound on each size, as in the numbered statement. -/
theorem theorem_1_8_index {A : Matrix (Fin n) (Fin n) ℂ} {p : ℕ} {lam : Fin p → ℂ} {γ : Fin p → ℕ}
    {l : ∀ i : Fin p, Fin (γ i) → ℕ}
    {σ : ((i : Fin p) × (k : Fin (γ i)) × Fin (l i k)) ≃ Fin n} (hinj : Function.Injective lam)
    (hA : IsSimilar A (Matrix.reindex σ σ
      (Matrix.blockDiagonal' fun i => Matrix.jordanForm (l i) (fun _ => lam i))))
    (i : Fin p) :
    ∃ L : ℕ, IsLeast {k : ℕ | LinearMap.ker (((A - lam i • 1) ^ (k + 1)).mulVecLin)
          = LinearMap.ker (((A - lam i • 1) ^ k).mulVecLin)} L ∧
        (∀ k, l i k ≤ L) ∧ L ≤ ∑ k, l i k := by
  classical
  have hiff : ∀ k : ℕ,
      LinearMap.ker (((A - lam i • 1) ^ (k + 1)).mulVecLin)
          = LinearMap.ker (((A - lam i • 1) ^ k).mulVecLin) ↔ ∀ κ, l i κ ≤ k := by
    intro k
    have hbb := Matrix.finrank_ker_mulVecLin_jordanForm_sub_smul_one_pow_succ_eq_iff (l i)
      (fun _ => lam i) (lam i) k
    rw [← finrank_ker_pow_sub_smul_one_of_jordan hinj hA i,
      ← finrank_ker_pow_sub_smul_one_of_jordan hinj hA i] at hbb
    refine Iff.trans ?_ (hbb.trans ⟨fun h κ => h κ rfl, fun h κ _ => h κ⟩)
    exact ⟨fun h => by rw [h], fun h => (Submodule.eq_of_le_of_finrank_eq
      (Matrix.ker_mulVecLin_pow_le_succ (A - lam i • 1) k) h.symm).symm⟩
  refine ⟨Finset.univ.sup fun k => l i k, ⟨(hiff _).2 fun κ => Finset.le_sup (Finset.mem_univ κ),
    fun k hk => Finset.sup_le fun κ _ => (hiff k).1 hk κ⟩,
    fun k => Finset.le_sup (Finset.mem_univ k), Finset.sup_le fun κ _ => ?_⟩
  exact Finset.single_le_sum (f := fun κ => l i κ) (fun _ _ => Nat.zero_le _) (Finset.mem_univ κ)

/-! ### §1.8.3 Theorem 1.9: the Schur canonical form -/

/-- **Theorem 1.9** of [saad2003iterative] (Schur canonical form). Let
$A \in \mathbb{C}^{n \times n}$. Then there is a unitary $Q \in \mathbb{C}^{n \times n}$ such
that $R = Q^H A Q$ is upper triangular, and the diagonal of $R$ carries the eigenvalues of $A$
with their algebraic multiplicities:
$$\det(\lambda I - A) = \prod_{i=1}^n (\lambda - r_{ii}).$$

The proof is the induction on the dimension in the book. The alternative proof from the Jordan
form and a QR factorization (Problem P-1.7) is not carried out. -/
theorem theorem_1_9 (A : Matrix (Fin n) (Fin n) ℂ) :
    ∃ Q ∈ Matrix.unitaryGroup (Fin n) ℂ,
      (star Q * A * Q).IsUpperTriangular ∧
        A.charpoly = ∏ i, (Polynomial.X - Polynomial.C ((star Q * A * Q) i i)) :=
  Matrix.exists_unitary_conj_upperTriangular A

/-- **Theorem 1.9** of [saad2003iterative], partial Schur decomposition. Let
$A, Q \in \mathbb{C}^{n \times n}$ with $Q$ unitary and $Q^H A Q$ upper triangular, and let
$k \ge 0$. Then the span of the first $k$ Schur vectors, the first $k$ columns $q_1, \dots, q_k$
of $Q$, is invariant under $A$: if $v$ is in this span, then so is $Av$.

**Reading.** The text gives the explicit identity $A Q_k = Q_k R_k$ for $k \le n$. This
declaration gives its span-invariance consequence. For $k>n$ its index set selects all columns,
whose span is the entire space.

The quasi-Schur (real Schur) form with $2 \times 2$ diagonal blocks is
`SaadSparse.Chapter01.realSchur`. -/
theorem theorem_1_9_partial {A Q : Matrix (Fin n) (Fin n) ℂ}
    (hQ : Q ∈ Matrix.unitaryGroup (Fin n) ℂ) (hR : (star Q * A * Q).IsUpperTriangular) (k : ℕ)
    {v : Fin n → ℂ} (hv : v ∈ Submodule.span ℂ (Q.col '' {i : Fin n | (i : ℕ) < k})) :
    A *ᵥ v ∈ Submodule.span ℂ (Q.col '' {i : Fin n | (i : ℕ) < k}) := by
  have hQstar : Q * star Q = 1 := (Matrix.mem_unitaryGroup_iff).1 hQ
  have hAQ : A * Q = Q * (star Q * A * Q) := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hQstar, Matrix.one_mul]
  have hgen : ∀ j : Fin n, (j : ℕ) < k →
      A *ᵥ Q.col j ∈ Submodule.span ℂ (Q.col '' {i : Fin n | (i : ℕ) < k}) := by
    intro j hj
    have hcol : A *ᵥ Q.col j = ∑ l, (star Q * A * Q) l j • Q.col l := by
      ext i
      simp only [Matrix.mulVec, dotProduct, Matrix.col, Matrix.transpose_apply,
        Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      have h := congrFun (congrFun hAQ i) j
      simp only [Matrix.mul_apply] at h
      rw [h]
      exact Finset.sum_congr rfl fun l _ => mul_comm _ _
    rw [hcol]
    refine Submodule.sum_mem _ fun l _ => ?_
    rcases le_or_gt (l : ℕ) (j : ℕ) with hlj | hlj
    · exact Submodule.smul_mem _ _ (Submodule.subset_span
        ⟨l, by simpa using lt_of_le_of_lt hlj hj, rfl⟩)
    · rw [hR (by exact_mod_cast hlj), zero_smul]
      exact Submodule.zero_mem _
  induction hv using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨j, hj, rfl⟩ := hx
      exact hgen j hj
  | zero => simp
  | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ _ hx

/-! ### §1.8.4 Theorems 1.10–1.12: powers of a matrix -/

/-- **Theorem 1.10** of [saad2003iterative]. Let $A \in \mathbb{R}^{n \times n}$. Then $A^k \to 0$
as $k \to \infty$ if and only if $\rho(A) < 1$.

**Reading.** The chapter assumes complex matrices by default. This declaration treats real inputs,
using their complex eigenvalues to compute the spectral radius for the stationary iterations that
use the result.

The spectral radius is `Matrix.complexSpectralRadius`, computed from the complex eigenvalues of
$A$. The book proves the difficult direction with the Jordan form. The backbone proves it with
Gelfand's formula, in `Numlib.LinearAlgebra.Matrix.Complexify`. Theorem 4.1 uses this result. -/
theorem theorem_1_10 (A : Matrix (Fin n) (Fin n) ℝ) :
    Tendsto (fun k => A ^ k) atTop (𝓝 0) ↔ A.complexSpectralRadius < 1 :=
  Matrix.tendsto_pow_iff_complexSpectralRadius_lt_one A

open scoped Matrix.Norms.L2Operator in
/-- **Theorem 1.11** of [saad2003iterative]. Let $A \in \mathbb{C}^{n \times n}$ with $n \ge 1$.
Then the series $\sum_{k=0}^\infty A^k$ converges if and only if $\rho(A) < 1$.

**Reading.** The book gives no explicit lower bound on $n$. The declaration assumes $n \ge 1$ to use
the unital Banach algebra convergence criterion. The book also identifies the sum as $(I-A)^{-1}$.
The declaration states the convergence criterion only.

The statement is over $\mathbb{C}$, with the Euclidean operator norm `Matrix.Norms.L2Operator`,
which is where the Banach algebra results of Mathlib apply. The spectral radius is Mathlib's
`spectralRadius ℂ A`, and convergence is `Summable`. -/
theorem theorem_1_11 [NeZero n] (A : Matrix (Fin n) (Fin n) ℂ) :
    (Summable fun k => A ^ k) ↔ spectralRadius ℂ A < 1 :=
  summable_pow_iff_spectralRadius_lt_one A

/-- **Theorem 1.11** of [saad2003iterative], second part. Let $A \in \mathbb{R}^{n \times n}$ with
$\rho(A) < 1$. Then $I - A$ is nonsingular.

**Reading.** The book asserts nonsingularity and identifies the sum for complex matrices. This
declaration gives the nonsingularity conclusion for real matrices, as needed for the stationary
iteration argument in §4.1.2.

For a real matrix, the spectral radius that decides is the one of the complex eigenvalues,
`Matrix.complexSpectralRadius`, because `spectrum ℝ` can miss the eigenvalues altogether.
Theorem 1.29 and §4.1.2 use this result. -/
theorem theorem_1_11_isUnit {A : Matrix (Fin n) (Fin n) ℝ} (h : A.complexSpectralRadius < 1) :
    IsUnit (1 - A) :=
  Matrix.isUnit_one_sub_of_complexSpectralRadius_lt_one h

open scoped Matrix.Norms.L2Operator in
/-- **Theorem 1.12** of [saad2003iterative] (Gelfand's formula), for the Euclidean operator norm.
Let $A \in \mathbb{R}^{n \times n}$. Then
$$\lim_{k \to \infty} \|A^k\|_2^{1/k} = \rho(A).$$

**Reading.** The chapter assumes complex matrices by default and states the formula for any
induced matrix norm. This declaration uses the Euclidean operator norm of real matrices. The
companion `SaadSparse.Chapter01.theorem_1_12_norm` covers all norms on the real matrix space.

The norm is `Matrix.Norms.L2Operator`. Theorem 1.28 and §4.2.1 use this result. -/
theorem theorem_1_12 (A : Matrix (Fin n) (Fin n) ℝ) :
    Tendsto (fun k : ℕ => ‖A ^ k‖ ^ (1 / k : ℝ)) atTop (𝓝 A.complexSpectralRadius.toReal) :=
  Matrix.tendsto_pow_rpow_complexSpectralRadius A

open scoped Matrix.Norms.L2Operator in
/-- **Theorem 1.12** of [saad2003iterative] (Gelfand's formula), for an arbitrary matrix norm. Let
$p$ be a norm on $\mathbb{R}^{n \times n}$ and let $A \in \mathbb{R}^{n \times n}$. Then
$$\lim_{k \to \infty} p(A^k)^{1/k} = \rho(A).$$

**Reading.** The chapter assumes complex matrices by default. The declaration quantifies over
norms of real matrices, using their complex spectral radius. The Euclidean operator norm case
is `SaadSparse.Chapter01.theorem_1_12`.

**Generalization.** The convention in §1.5 restricts matrix norms to induced norms. The theorem
allows every norm on the real matrix space because the equivalence constants between norms
disappear under the $k$-th root.

The norm is a `Seminorm ℝ` with the definiteness hypothesis `hp`. -/
theorem theorem_1_12_norm (p : Seminorm ℝ (Matrix (Fin n) (Fin n) ℝ))
    (hp : ∀ M : Matrix (Fin n) (Fin n) ℝ, p M = 0 → M = 0) (A : Matrix (Fin n) (Fin n) ℝ) :
    Tendsto (fun k : ℕ => p (A ^ k) ^ (1 / k : ℝ)) atTop (𝓝 A.complexSpectralRadius.toReal) :=
  p.tendsto_rpow_one_div hp (theorem_1_12 A)

/-- **Section 1.8.3** of [saad2003iterative], the quasi-Schur form, also called the real Schur form.
Let $A \in \mathbb{R}^{n \times n}$. Then there is an orthogonal $Q \in \mathbb{R}^{n \times n}$
such that $Q^T A Q$ is quasi upper triangular: block upper triangular, with diagonal blocks of
consecutive indices of size $1 \times 1$ or $2 \times 2$.

**Reading.** The book also associates each $2 \times 2$ block with a pair of complex conjugate
eigenvalues. The declaration supplies the block shape and size bounds.

The block structure is a monotone index map $p$ from the indices to $\mathbb{N}$: monotonicity
makes each block an interval of consecutive indices, the bound on the size of each fibre of $p$
makes every block $1 \times 1$ or $2 \times 2$, and `Matrix.BlockTriangular` says that the
entries below the blocks vanish. Theorem 1.9 does not specialize to this form, because over
$\mathbb{R}$ there need be no eigenvector: the induction removes an invariant subspace of
dimension one or two (`LinearMap.exists_invariant_finrank_le_two`). The proof is the backbone's
`Matrix.exists_orthogonal_conj_isQuasiUpperTriangular`. -/
theorem realSchur (A : Matrix (Fin n) (Fin n) ℝ) :
    ∃ Q ∈ Matrix.orthogonalGroup (Fin n) ℝ, ∃ p : Fin n → ℕ, Monotone p ∧
      (∀ k, (Finset.univ.filter fun i => p i = k).card ≤ 2) ∧
      (Qᵀ * A * Q).BlockTriangular p :=
  Matrix.exists_orthogonal_conj_isQuasiUpperTriangular A

end SaadSparse.Chapter01
