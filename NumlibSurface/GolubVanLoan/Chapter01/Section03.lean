/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.SymplecticGroup
import Mathlib.Tactic.NoncommRing
import Numlib.LinearAlgebra.Matrix.Block
import Numlib.LinearAlgebra.Matrix.Hamiltonian
import Numlib.LinearAlgebra.Matrix.Kronecker
import NumlibSurface.GolubVanLoan.Chapter01.Section02

/-!
# Golub and Van Loan, Section 1.3: Block matrices and algorithms

This module formalizes §1.3 of [golub2013matrix]: block multiplication (Theorem 1.3.1), the
properties (1.3.1)–(1.3.5) of the Kronecker product $B \otimes C$, the identity (1.3.6) that
$Y = CXB^T$ if and only if $\mathrm{vec}(Y) = (B \otimes C) \mathrm{vec}(X)$, Hamiltonian and
symplectic matrices (§1.3.10), and Strassen's recursive matrix multiplication (Algorithm 1.3.1),
with its proof of correctness in exact arithmetic.

The proofs specialize `Numlib.LinearAlgebra.Matrix.Block` for block multiplication,
`Numlib.LinearAlgebra.Matrix.Kronecker` and `Numlib.LinearAlgebra.Matrix.Permutation` for the
Kronecker product and the perfect shuffle, and `Numlib.LinearAlgebra.Matrix.Hamiltonian` and
Mathlib's symplectic group for §1.3.10.

## Main definitions

* §1.3.10, `GolubVanLoan.Chapter01.bookJ`: the matrix $J = \begin{bmatrix} 0 & I_n \\ -I_n & 0
  \end{bmatrix}$.
* Algorithm 1.3.1, `GolubVanLoan.Chapter01.algorithm_1_3_1`: Strassen matrix multiplication.
* `GolubVanLoan.Chapter01.matrixAdd` and `GolubVanLoan.Chapter01.matrixSub`: the entrywise rounded
  sum and difference of two matrices, used by Algorithm 1.3.1 and by later chapters.

## Main results

* Theorem 1.3.1, `GolubVanLoan.Chapter01.theorem_1_3_1`: block multiplication, $C_{\alpha\beta} =
  \sum_\gamma A_{\alpha\gamma} B_{\gamma\beta}$.
* Equation (1.3.1), `GolubVanLoan.Chapter01.equation_1_3_1`: $(B \otimes C)^T = B^T \otimes C^T$.
* Equation (1.3.2), `GolubVanLoan.Chapter01.equation_1_3_2`:
  $(B \otimes C)(D \otimes F) = BD \otimes CF$.
* Equation (1.3.3), `GolubVanLoan.Chapter01.equation_1_3_3`: for nonsingular $B$ and $C$,
  $(B \otimes C)^{-1} = B^{-1} \otimes C^{-1}$.
* Equation (1.3.4), `GolubVanLoan.Chapter01.equation_1_3_4`: $B \otimes (C \otimes D) = (B \otimes
  C) \otimes D$.
* Equation (1.3.5), `GolubVanLoan.Chapter01.equation_1_3_5`: $P (B \otimes C) Q^T = C \otimes B$ for
  perfect shuffles $P$ and $Q$.
* Equation (1.3.6), `GolubVanLoan.Chapter01.equation_1_3_6`: $Y = CXB^T$ if and only if
  $\mathrm{vec}(Y) = (B \otimes C) \mathrm{vec}(X)$.
* §1.3.10, `GolubVanLoan.Chapter01.isHamiltonian_iff`: the block form and the condition
  $JMJ^T = -M^T$ define the same Hamiltonian matrices.
* §1.3.10, `GolubVanLoan.Chapter01.isSymplectic_iff`: $S^T J S = J$ if and only if $S$ is in
  Mathlib's symplectic group.
* §1.3.10, `GolubVanLoan.Chapter01.symplectic_blocks`: the conditions on the blocks of a symplectic
  matrix.
* Algorithm 1.3.1, `GolubVanLoan.Chapter01.algorithm_1_3_1_spec`: in exact arithmetic Strassen's
  algorithm computes $AB$.

## Conventions

* A partition into blocks of sizes $m_1, \dots, m_q$ is the sigma type `(α : Fin q) × Fin (m α)`,
  laid out contiguously by Mathlib's `finSigmaFinEquiv : (α : Fin q) × Fin (m α) ≃ Fin (∑ α, m α)`.
  The block $A_{\alpha\beta} = A(\tau+1{:}\tau+m_\alpha, \mu+1{:}\mu+n_\beta)$ of the source is
  `A.submatrix (finSigmaFinEquiv ∘ Sigma.mk α) (finSigmaFinEquiv ∘ Sigma.mk β)`.
* The Kronecker product $B \otimes C \in \mathbb{R}^{m_1 m_2 \times n_1 n_2}$ is
  `Matrix.kroneckerFin B C`. Its $(i, j)$ block is $b_{ij} C$, and its row $(i_1 - 1) m_2 + i_2$ is
  `finProdFinEquiv (i₁, i₂)` in 0-based indices.
* The column stacking $\mathrm{vec}$ is `Matrix.vecFin`.
* The perfect shuffle $\mathcal{P}_{p,r}$ is `Matrix.perfectShuffle`.
* The $2n \times 2n$ matrices of §1.3.10 are kept in their $2 \times 2$ block form
  `Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ`.

## Implementation notes

* Theorem 1.3.1 is the backbone's `Matrix.mul_submatrix_sigmaMk_eq_sum`, transported along
  `finSigmaFinEquiv`.
* Hamiltonian matrices are the backbone's `Matrix.IsHamiltonian`, and symplectic matrices are
  Mathlib's `Matrix.symplecticGroup (Fin n) ℝ`. The source's $J$ is `GolubVanLoan.Chapter01.bookJ`,
  the negative of Mathlib's `Matrix.J`. Both defining conditions are invariant under $J \mapsto -J$,
  so they are stated with the source's $J$ and proved equivalent to the Mathlib forms.
* Algorithm 1.3.1 recurses on $q$ for $n = 2^q$. It splits `Fin (2 ^ (q + 1))` as
  `Fin (2 ^ q) ⊕ Fin (2 ^ q)` by `GolubVanLoan.Chapter01.twoPowSplit`, which gives the source's
  $u = 1{:}m$ and $v = m+1{:}n$. The seven sums and differences and the four assemblies are the
  entrywise rounded operations `GolubVanLoan.Chapter01.matrixAdd` and
  `GolubVanLoan.Chapter01.matrixSub`, and the base case is Algorithm 1.1.5 with $C = 0$.

## Deviations from the source

* **Equation (1.3.6)** (typo). The source gives $X \in \mathbb{R}^{n_1 \times m_2}$; the size is
  $X \in \mathbb{R}^{n_2 \times n_1}$, the only size for which $CXB^T$ is defined. See
  `GolubVanLoan.Chapter01.equation_1_3_6`.
* **§1.3.10, blocks of a symplectic matrix** (generalization). The source derives the block
  conditions from $S^T J S = J$; the statement is an equivalence. See
  `GolubVanLoan.Chapter01.symplectic_blocks`.
* **Algorithm 1.3.1** (generalization). The source assumes $n_{\min} = 2^d$ with $d \le q$; the
  specification holds for every $d$. See `GolubVanLoan.Chapter01.algorithm_1_3_1_spec`.

## Not formalized

* **The terminology for block-sparse matrices of §1.3.1.**
* **The submatrix notation of §1.3.3.**
* **The unnumbered blocked gaxpys of §1.3.4 and block products of §1.3.5.**
* **The band structure that $B \otimes C$ inherits from $B$ and $C$.**
* **The reshaping of multiple Kronecker products in §1.3.8, with its count $6n^4$.** Operation
  counts are out of scope for the library.
* **The real form of complex matrix multiplication in §1.3.9.**
* **The operation counts of Strassen's method and the exponent $2.807$.** Operation counts are out
  of scope for the library.
* **The MATLAB `reshape` example.** The backbone has `Matrix.reshape`.
-/

open Matrix

namespace GolubVanLoan.Chapter01

/-! ### Theorem 1.3.1: block multiplication -/

/-- **Theorem 1.3.1** of [golub2013matrix] (block multiplication). Let
$A \in \mathbb{R}^{M \times P}$ and $B \in \mathbb{R}^{P \times N}$, with
$M = m_1 + \dots + m_q$, $P = p_1 + \dots + p_s$ and $N = n_1 + \dots + n_r$. Partition $A$ into
blocks $A_{\alpha\gamma}$ of size $m_\alpha \times p_\gamma$ and $B$ into blocks
$B_{\gamma\beta}$ of size $p_\gamma \times n_\beta$. Then for all $\alpha$ and $\beta$ the block
$C_{\alpha\beta}$ of $C = AB$ is
$$C_{\alpha\beta} = \sum_{\gamma=1}^{s} A_{\alpha\gamma} B_{\gamma\beta}.$$

The block $X_{\alpha\beta}$ is $X$ restricted to the contiguous rows of block $\alpha$ and
columns of block $\beta$, through `finSigmaFinEquiv ∘ Sigma.mk α` and
`finSigmaFinEquiv ∘ Sigma.mk β`. -/
theorem theorem_1_3_1 {q s r : ℕ} {m : Fin q → ℕ} {p : Fin s → ℕ} {n : Fin r → ℕ}
    (A : Matrix (Fin (∑ α, m α)) (Fin (∑ γ, p γ)) ℝ)
    (B : Matrix (Fin (∑ γ, p γ)) (Fin (∑ β, n β)) ℝ) (α : Fin q) (β : Fin r) :
    (A * B).submatrix (finSigmaFinEquiv ∘ Sigma.mk α) (finSigmaFinEquiv ∘ Sigma.mk β) =
      ∑ γ, A.submatrix (finSigmaFinEquiv ∘ Sigma.mk α) (finSigmaFinEquiv ∘ Sigma.mk γ) *
        B.submatrix (finSigmaFinEquiv ∘ Sigma.mk γ) (finSigmaFinEquiv ∘ Sigma.mk β) := by
  have h := mul_submatrix_sigmaMk_eq_sum (A.submatrix finSigmaFinEquiv finSigmaFinEquiv)
    (B.submatrix finSigmaFinEquiv finSigmaFinEquiv) α β
  simp only [submatrix_mul_equiv, submatrix_submatrix] at h
  exact h

/-! ### The Kronecker product (1.3.1)–(1.3.6) -/

section Kronecker

variable {m₁ n₁ m₂ n₂ : ℕ}

/-- **Equation (1.3.1)** of [golub2013matrix]. For $B \in \mathbb{R}^{m_1 \times n_1}$ and
$C \in \mathbb{R}^{m_2 \times n_2}$,
$$(B \otimes C)^T = B^T \otimes C^T.$$
-/
theorem equation_1_3_1 (B : Matrix (Fin m₁) (Fin n₁) ℝ) (C : Matrix (Fin m₂) (Fin n₂) ℝ) :
    (kroneckerFin B C)ᵀ = kroneckerFin Bᵀ Cᵀ :=
  transpose_kroneckerFin B C

/-- **Equation (1.3.2)** of [golub2013matrix]. For $B \in \mathbb{R}^{m_1 \times n_1}$,
$C \in \mathbb{R}^{m_2 \times n_2}$, $D \in \mathbb{R}^{n_1 \times p_1}$ and
$F \in \mathbb{R}^{n_2 \times p_2}$,
$$(B \otimes C)(D \otimes F) = BD \otimes CF.$$
-/
theorem equation_1_3_2 {p₁ p₂ : ℕ} (B : Matrix (Fin m₁) (Fin n₁) ℝ)
    (C : Matrix (Fin m₂) (Fin n₂) ℝ) (D : Matrix (Fin n₁) (Fin p₁) ℝ)
    (F : Matrix (Fin n₂) (Fin p₂) ℝ) :
    kroneckerFin B C * kroneckerFin D F = kroneckerFin (B * D) (C * F) :=
  kroneckerFin_mul_kroneckerFin B C D F

/-- **Equation (1.3.3)** of [golub2013matrix]. Let $B \in \mathbb{R}^{m_1 \times m_1}$ and
$C \in \mathbb{R}^{m_2 \times m_2}$ be nonsingular. Then $B \otimes C$ is nonsingular and
$$(B \otimes C)^{-1} = B^{-1} \otimes C^{-1}.$$

Nonsingularity is `IsUnit B.det`. Lean's inverse, which is $0$ for a singular matrix, makes the
identity hold without the hypotheses; they are the source's hypotheses, and they give the
nonsingularity of $B \otimes C$. -/
theorem equation_1_3_3 (B : Matrix (Fin m₁) (Fin m₁) ℝ) (C : Matrix (Fin m₂) (Fin m₂) ℝ)
    (hB : IsUnit B.det) (hC : IsUnit C.det) :
    IsUnit (kroneckerFin B C).det ∧ (kroneckerFin B C)⁻¹ = kroneckerFin B⁻¹ C⁻¹ := by
  refine ⟨?_, inv_kroneckerFin B C⟩
  rw [kroneckerFin, det_submatrix_equiv_self, det_kronecker]
  exact (hB.pow _).mul (hC.pow _)

/-- **Equation (1.3.4)** of [golub2013matrix]. For $B \in \mathbb{R}^{m_1 \times n_1}$,
$C \in \mathbb{R}^{m_2 \times n_2}$ and $D \in \mathbb{R}^{m_3 \times n_3}$,
$$B \otimes (C \otimes D) = (B \otimes C) \otimes D.$$

The two sides are indexed by `Fin (m₁ * (m₂ * m₃))` and `Fin (m₁ * m₂ * m₃)`, and the statement
identifies them by `Nat.mul_assoc`. -/
theorem equation_1_3_4 {m₃ n₃ : ℕ} (B : Matrix (Fin m₁) (Fin n₁) ℝ)
    (C : Matrix (Fin m₂) (Fin n₂) ℝ) (D : Matrix (Fin m₃) (Fin n₃) ℝ) :
    kroneckerFin B (kroneckerFin C D) =
      (kroneckerFin (kroneckerFin B C) D).submatrix (finCongr (Nat.mul_assoc m₁ m₂ m₃)).symm
        (finCongr (Nat.mul_assoc n₁ n₂ n₃)).symm :=
  kroneckerFin_assoc B C D

/-- **Equation (1.3.5)** of [golub2013matrix]. Let $B \in \mathbb{R}^{m_1 \times n_1}$ and
$C \in \mathbb{R}^{m_2 \times n_2}$, and let $P = \mathcal{P}_{m_1, m_2}$ and
$Q = \mathcal{P}_{n_1, n_2}$ be perfect shuffles. Then
$$P (B \otimes C) Q^T = C \otimes B.$$
-/
theorem equation_1_3_5 (B : Matrix (Fin m₁) (Fin n₁) ℝ) (C : Matrix (Fin m₂) (Fin n₂) ℝ) :
    perfectShuffle m₁ m₂ * kroneckerFin B C *
        (perfectShuffle n₁ n₂ : Matrix (Fin (n₂ * n₁)) (Fin (n₁ * n₂)) ℝ)ᵀ =
      kroneckerFin C B :=
  perfectShuffle_mul_kroneckerFin_mul_transpose B C

/-- **Equation (1.3.6)** of [golub2013matrix]. Let $B \in \mathbb{R}^{m_1 \times n_1}$,
$C \in \mathbb{R}^{m_2 \times n_2}$, $X \in \mathbb{R}^{n_2 \times n_1}$ and
$Y \in \mathbb{R}^{m_2 \times m_1}$. Then
$$Y = C X B^T \iff \mathrm{vec}(Y) = (B \otimes C) \, \mathrm{vec}(X).$$

**Typo.** The source gives the size $X \in \mathbb{R}^{n_1 \times m_2}$. This is a misprint for
$\mathbb{R}^{n_2 \times n_1}$, the only size for which $CXB^T$ is defined.

The column stacking $\mathrm{vec}$ is `Matrix.vecFin`. -/
theorem equation_1_3_6 (B : Matrix (Fin m₁) (Fin n₁) ℝ) (C : Matrix (Fin m₂) (Fin n₂) ℝ)
    (X : Matrix (Fin n₂) (Fin n₁) ℝ) (Y : Matrix (Fin m₂) (Fin m₁) ℝ) :
    Y = C * X * Bᵀ ↔ vecFin Y = kroneckerFin B C *ᵥ vecFin X := by
  rw [kroneckerFin_mulVec_vecFin]
  exact ⟨fun h => h ▸ rfl, fun h => vecFin_injective h⟩

end Kronecker

/-! ### Hamiltonian and symplectic matrices (§1.3.10) -/

/-- **§1.3.10** of [golub2013matrix], the matrix $J$. It is the $2n \times 2n$ matrix
$$J = \begin{bmatrix} 0 & I_n \\ -I_n & 0 \end{bmatrix},$$
indexed by `Fin n ⊕ Fin n`. -/
def bookJ (n : ℕ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ :=
  fromBlocks 0 1 (-1) 0

/-- The source's $J$ is the negative of Mathlib's `Matrix.J`. -/
theorem bookJ_eq_neg_J (n : ℕ) : bookJ n = -J (Fin n) ℝ := by
  rw [bookJ, J, fromBlocks_neg, neg_zero, neg_neg]

/-- **§1.3.10** of [golub2013matrix], the two definitions of a Hamiltonian matrix. Let
$A, F, G, H \in \mathbb{R}^{n \times n}$ and $M = \begin{bmatrix} A & G \\ F & H \end{bmatrix}$.
Then $M$ has the form $\begin{bmatrix} A & G \\ F & -A^T \end{bmatrix}$ with $F$ and $G$
symmetric if and only if $J M J^T = -M^T$, for the source's $J$. Also, $M$ is Hamiltonian in the
sense of the backbone if and only if $J M J^T = -M^T$.

The backbone's predicate is `Matrix.IsHamiltonian`, which uses Mathlib's `Matrix.J`. -/
theorem isHamiltonian_iff {n : ℕ} (A F G H : Matrix (Fin n) (Fin n) ℝ) :
    ((H = -Aᵀ ∧ Fᵀ = F ∧ Gᵀ = G) ↔
        bookJ n * fromBlocks A G F H * (bookJ n)ᵀ = -(fromBlocks A G F H)ᵀ) ∧
      ((fromBlocks A G F H).IsHamiltonian ↔
        bookJ n * fromBlocks A G F H * (bookJ n)ᵀ = -(fromBlocks A G F H)ᵀ) := by
  have h : (fromBlocks A G F H).IsHamiltonian ↔
      bookJ n * fromBlocks A G F H * (bookJ n)ᵀ = -(fromBlocks A G F H)ᵀ := by
    rw [IsHamiltonian]
    simp only [bookJ_eq_neg_J, transpose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg]
  exact ⟨isHamiltonian_fromBlocks_iff.symm.trans h, h⟩

/-- **§1.3.10** of [golub2013matrix], symplectic matrices. A matrix
$S \in \mathbb{R}^{2n \times 2n}$ satisfies $S^T J S = J$, for the source's $J$, if and only if
$S$ is in Mathlib's symplectic group `Matrix.symplecticGroup (Fin n) ℝ`. -/
theorem isSymplectic_iff {n : ℕ} (S : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) :
    Sᵀ * bookJ n * S = bookJ n ↔ S ∈ symplecticGroup (Fin n) ℝ := by
  rw [SymplecticGroup.mem_iff', bookJ_eq_neg_J, Matrix.mul_neg, Matrix.neg_mul, neg_inj]

/-- **§1.3.10** of [golub2013matrix], blocks of a symplectic matrix. Let $S_{11}, S_{12}, S_{21},
S_{22} \in \mathbb{R}^{n \times n}$ and $S = \begin{bmatrix} S_{11} & S_{12} \\ S_{21} & S_{22}
\end{bmatrix}$. Then $S^T J S = J$ if and only if $S_{11}^T S_{21}$ and $S_{22}^T S_{12}$ are
symmetric and
$$S_{11}^T S_{22} = I_n + S_{21}^T S_{12}.$$

**Generalization.** The source states only that the block conditions follow from $S^T J S = J$.
The converse holds as well, and the statement is an equivalence. -/
theorem symplectic_blocks {n : ℕ} (S₁₁ S₁₂ S₂₁ S₂₂ : Matrix (Fin n) (Fin n) ℝ) :
    (fromBlocks S₁₁ S₁₂ S₂₁ S₂₂)ᵀ * bookJ n * fromBlocks S₁₁ S₁₂ S₂₁ S₂₂ = bookJ n ↔
      (S₁₁ᵀ * S₂₁).IsSymm ∧ (S₂₂ᵀ * S₁₂).IsSymm ∧ S₁₁ᵀ * S₂₂ = 1 + S₂₁ᵀ * S₁₂ := by
  rw [isSymplectic_iff, SymplecticGroup.fromBlocks_mem_iff, IsSymm, IsSymm, transpose_mul,
    transpose_mul, transpose_transpose, transpose_transpose, sub_eq_iff_eq_add]
  exact and_congr eq_comm Iff.rfl

/-! ### Algorithm 1.3.1: Strassen matrix multiplication -/

section Strassen

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- The entrywise rounded sum $\mathrm{fl}(X + Y)$ of two matrices
$X, Y \in \mathbb{R}^{m \times n}$: the program computes
$x_{ij} \leftarrow \mathrm{fl}(x_{ij} + y_{ij})$ over the rows, and in each row over the
columns. -/
def matrixAdd {m n : ℕ} (X Y : Matrix (Fin m) (Fin n) ℝ) : M (Matrix (Fin m) (Fin n) ℝ) :=
  (List.finRange m).foldlM (fun Z i =>
    (List.finRange n).foldlM (fun Z j => do
      let z ← rnd (Z i j + Y i j)
      pure (Z.updateRow i (Function.update (Z i) j z))) Z) X

/-- The entrywise rounded difference $\mathrm{fl}(X - Y)$ of two matrices
$X, Y \in \mathbb{R}^{m \times n}$: the program computes
$x_{ij} \leftarrow \mathrm{fl}(x_{ij} - y_{ij})$ over the rows, and in each row over the
columns. -/
def matrixSub {m n : ℕ} (X Y : Matrix (Fin m) (Fin n) ℝ) : M (Matrix (Fin m) (Fin n) ℝ) :=
  (List.finRange m).foldlM (fun Z i =>
    (List.finRange n).foldlM (fun Z j => do
      let z ← rnd (Z i j - Y i j)
      pure (Z.updateRow i (Function.update (Z i) j z))) Z) X

/-- The splitting of the indices `Fin (2 ^ (q + 1))` into two halves, the source's $u = 1{:}m$ and
$v = m+1{:}n$ for $n = 2m = 2^{q+1}$. The left summand `Sum.inl` is the first half, and the
right summand `Sum.inr` is the second half. -/
def twoPowSplit (q : ℕ) : Fin (2 ^ q) ⊕ Fin (2 ^ q) ≃ Fin (2 ^ (q + 1)) :=
  finSumFinEquiv.trans (finCongr (by rw [pow_succ, mul_two]))

/-- **Algorithm 1.3.1** of [golub2013matrix] (Strassen matrix multiplication). "Suppose $n = 2^q$
and that $A, B \in \mathbb{R}^{n \times n}$. If $n_{\min} = 2^d$ with $d \le q$, then this
algorithm computes $C = AB$ by applying Strassen procedure recursively":
```
function C = strass(A, B, n, n_min)
    if n ≤ n_min
        C = AB (conventionally computed)
    else
        m = n/2; u = 1:m; v = m+1:n
        P₁ = strass(A(u,u) + A(v,v), B(u,u) + B(v,v), m, n_min)
        P₂ = strass(A(v,u) + A(v,v), B(u,u), m, n_min)
        P₃ = strass(A(u,u), B(u,v) − B(v,v), m, n_min)
        P₄ = strass(A(v,v), B(v,u) − B(u,u), m, n_min)
        P₅ = strass(A(u,u) + A(u,v), B(v,v), m, n_min)
        P₆ = strass(A(v,u) − A(u,u), B(u,u) + B(u,v), m, n_min)
        P₇ = strass(A(u,v) − A(v,v), B(v,u) + B(v,v), m, n_min)
        C(u,u) = P₁ + P₄ − P₅ + P₇
        C(u,v) = P₃ + P₅
        C(v,u) = P₂ + P₄
        C(v,v) = P₁ + P₃ − P₂ + P₆
    end
```
Every sum and difference of blocks is computed entrywise with one rounding per entry.

**Generalization.** The printed precondition is $d \le q$. The program also accepts $d > q$ and
uses conventional multiplication immediately, since the input is already below the threshold.

The conventional product is Algorithm 1.1.5 with $C = 0$, and the test $n \le n_{\min}$ is
$q \le d$. The program is defined by recursion on $q$. -/
def algorithm_1_3_1 (d : ℕ) :
    (q : ℕ) → Matrix (Fin (2 ^ q)) (Fin (2 ^ q)) ℝ → Matrix (Fin (2 ^ q)) (Fin (2 ^ q)) ℝ →
      M (Matrix (Fin (2 ^ q)) (Fin (2 ^ q)) ℝ)
  | 0, A, B => algorithm_1_1_5 rnd A B 0
  | q + 1, A, B =>
    if q + 1 ≤ d then algorithm_1_1_5 rnd A B 0 else do
      let A' := A.submatrix (twoPowSplit q) (twoPowSplit q)
      let B' := B.submatrix (twoPowSplit q) (twoPowSplit q)
      let P₁ ← algorithm_1_3_1 d q (← matrixAdd rnd A'.toBlocks₁₁ A'.toBlocks₂₂)
        (← matrixAdd rnd B'.toBlocks₁₁ B'.toBlocks₂₂)
      let P₂ ← algorithm_1_3_1 d q (← matrixAdd rnd A'.toBlocks₂₁ A'.toBlocks₂₂) B'.toBlocks₁₁
      let P₃ ← algorithm_1_3_1 d q A'.toBlocks₁₁ (← matrixSub rnd B'.toBlocks₁₂ B'.toBlocks₂₂)
      let P₄ ← algorithm_1_3_1 d q A'.toBlocks₂₂ (← matrixSub rnd B'.toBlocks₂₁ B'.toBlocks₁₁)
      let P₅ ← algorithm_1_3_1 d q (← matrixAdd rnd A'.toBlocks₁₁ A'.toBlocks₁₂) B'.toBlocks₂₂
      let P₆ ← algorithm_1_3_1 d q (← matrixSub rnd A'.toBlocks₂₁ A'.toBlocks₁₁)
        (← matrixAdd rnd B'.toBlocks₁₁ B'.toBlocks₁₂)
      let P₇ ← algorithm_1_3_1 d q (← matrixSub rnd A'.toBlocks₁₂ A'.toBlocks₂₂)
        (← matrixAdd rnd B'.toBlocks₂₁ B'.toBlocks₂₂)
      let C₁₁ ← matrixAdd rnd (← matrixSub rnd (← matrixAdd rnd P₁ P₄) P₅) P₇
      let C₁₂ ← matrixAdd rnd P₃ P₅
      let C₂₁ ← matrixAdd rnd P₂ P₄
      let C₂₂ ← matrixAdd rnd (← matrixSub rnd (← matrixAdd rnd P₁ P₃) P₂) P₆
      pure ((fromBlocks C₁₁ C₁₂ C₂₁ C₂₂).submatrix (twoPowSplit q).symm
        (twoPowSplit q).symm)

end Strassen

/-- The loop over one row of `GolubVanLoan.Chapter01.matrixAdd` or
`GolubVanLoan.Chapter01.matrixSub` after fusion. -/
private def matrixRowOp {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ) (op : ℝ → ℝ → ℝ) {n : ℕ}
    (y : Fin n → ℝ) (r : Fin n → ℝ) : M (Fin n → ℝ) :=
  (List.finRange n).foldlM (fun r j => do
    let c ← rnd (op (r j) (y j)); pure (Function.update r j c)) r

/-- An entrywise operation, written as a loop over the rows of fused loops over single rows. -/
private theorem foldlM_entrywise_eq {M : Type → Type} [Monad M] [LawfulMonad M] (rnd : ℝ → M ℝ)
    (op : ℝ → ℝ → ℝ) {m n : ℕ} (X Y : Matrix (Fin m) (Fin n) ℝ) :
    (List.finRange m).foldlM (fun (Z : Matrix (Fin m) (Fin n) ℝ) i =>
      (List.finRange n).foldlM (fun (Z : Matrix (Fin m) (Fin n) ℝ) j => do
        let z ← rnd (op (Z i j) (Y i j))
        pure (Z.updateRow i (Function.update (Z i) j z))) Z) X =
    (List.finRange m).foldlM (fun Z i => do
      let r ← matrixRowOp rnd op (Y i) (Z i); pure (Z.updateRow i r)) X := by
  congr 1
  funext Z i
  exact Matrix.foldlM_updateRow_entrywise i (fun j c => rnd (op c (Y i j))) _ Z

/-- In exact arithmetic, an entrywise loop computes the entrywise operation. -/
private theorem idRun_foldlM_entrywise (op : ℝ → ℝ → ℝ) {m n : ℕ}
    (X Y : Matrix (Fin m) (Fin n) ℝ) :
    Id.run ((List.finRange m).foldlM (fun (Z : Matrix (Fin m) (Fin n) ℝ) i =>
      (List.finRange n).foldlM (fun (Z : Matrix (Fin m) (Fin n) ℝ) j => do
        let z ← (pure (op (Z i j) (Y i j)) : Id ℝ)
        pure (Z.updateRow i (Function.update (Z i) j z))) Z) X) =
      Matrix.of fun i j => op (X i j) (Y i j) := by
  rw [foldlM_entrywise_eq pure op X Y]
  ext i j
  rw [Matrix.idRun_foldlM_updateRow_apply _ _ (List.nodup_finRange m),
    ite_eq_left (List.mem_finRange i), matrixRowOp,
    List.idRun_foldlM_update_apply (fun j c => (pure (op c (Y i j)) : Id ℝ)) _
      (List.nodup_finRange n), ite_eq_left (List.mem_finRange j)]
  rfl

/-- In exact arithmetic, `GolubVanLoan.Chapter01.matrixAdd` computes the sum $X + Y$. -/
theorem matrixAdd_spec {m n : ℕ} (X Y : Matrix (Fin m) (Fin n) ℝ) :
    Id.run (matrixAdd pure X Y) = X + Y :=
  (idRun_foldlM_entrywise (· + ·) X Y).trans rfl

/-- In exact arithmetic, `GolubVanLoan.Chapter01.matrixSub` computes the difference $X - Y$. -/
theorem matrixSub_spec {m n : ℕ} (X Y : Matrix (Fin m) (Fin n) ℝ) :
    Id.run (matrixSub pure X Y) = X - Y :=
  (idRun_foldlM_entrywise (· - ·) X Y).trans rfl

/-- **Algorithm 1.3.1** of [golub2013matrix], exact correctness. Let $d, q \in \mathbb{N}$,
$n = 2^q$, $n_{\min} = 2^d$, and $A, B \in \mathbb{R}^{n \times n}$. In exact arithmetic,
Algorithm 1.3.1 returns $C = AB$.

**Generalization.** The source assumes $d \le q$. The statement holds for every $d$; for
$d \ge q$ the algorithm is the conventional product.

The proof is by induction on $q$. The base case is Algorithm 1.1.5, and the step uses Strassen's
seven identities ("easily confirmed by substitution"), which hold in the noncommutative ring of
$2^q \times 2^q$ matrices. -/
theorem algorithm_1_3_1_spec (d : ℕ) :
    ∀ (q : ℕ) (A B : Matrix (Fin (2 ^ q)) (Fin (2 ^ q)) ℝ),
      Id.run (algorithm_1_3_1 pure d q A B) = A * B
  | 0, A, B => by rw [algorithm_1_3_1, algorithm_1_1_5_spec, zero_add]
  | q + 1, A, B => by
    rw [algorithm_1_3_1]
    split_ifs
    · rw [algorithm_1_1_5_spec, zero_add]
    · simp only [Id.run_bind, Id.run_pure, matrixAdd_spec, matrixSub_spec,
        algorithm_1_3_1_spec d q]
      set e := twoPowSplit q
      have hAB : A * B = (A.submatrix e e * B.submatrix e e).submatrix e.symm e.symm := by
        rw [submatrix_mul_equiv, submatrix_submatrix, e.self_comp_symm, submatrix_id_id]
      rw [hAB]
      conv_rhs => rw [← fromBlocks_toBlocks (A.submatrix e e),
        ← fromBlocks_toBlocks (B.submatrix e e), fromBlocks_multiply]
      congr 1
      rw [fromBlocks_inj]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> noncomm_ring

end GolubVanLoan.Chapter01
