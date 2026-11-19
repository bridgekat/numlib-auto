/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Eigen.HamiltonianSchur
import Numlib.Eigen.PeriodicSchur
import NumlibSurface.GolubVanLoan.Chapter07.Section04

/-!
# Golub and Van Loan, Section 7.8: Hamiltonian and product eigenvalue problems

This module formalizes §7.8 of [golub2013matrix]. Let $J = \begin{bmatrix} 0 & I_n \\ -I_n & 0
\end{bmatrix}$. A real $2n \times 2n$ matrix $M$ is Hamiltonian if $JMJ^T = -M^T$, skew-Hamiltonian
if $JMJ^T = M^T$, and symplectic if $M^T J M = J$. §7.8.1 states the block forms of these classes
(Figure 7.8.1) and four facts: symplectic similarities preserve the Hamiltonian structure, the
square of a Hamiltonian matrix is skew-Hamiltonian, the eigenvalues of a Hamiltonian matrix come in
pairs $\pm\lambda$, and those of a symplectic matrix in pairs $\lambda, 1/\lambda$. It then reduces
a Hamiltonian matrix by orthogonal symplectic transformations: one deflation step by a real
eigenvector, the real Hamiltonian–Schur form (7.8.1) and the algebraic Riccati equation (7.8.2), the
Paige–Van Loan form (7.8.3), and the Hessenberg (7.8.4) and real Schur forms of the skew-Hamiltonian
matrix $M^2$.

§7.8.2 treats the eigenvalues of a product $A = A_3 A_2 A_1$ of $n \times n$ matrices without
forming the product. Orthogonal $U_1, U_2, U_3$ reduce the three factors to
Hessenberg–triangular–triangular form (7.8.5) and to the periodic real Schur form (7.8.6). The same
reduction is a reduction of the block-cyclic matrix $\begin{bmatrix} 0 & 0 & A_3 \\ A_1 & 0 & 0 \\ 0
& A_2 & 0 \end{bmatrix}$, which becomes upper Hessenberg after a perfect shuffle of its rows and
columns. The proofs specialize the backbone modules `Numlib.LinearAlgebra.Matrix.Hamiltonian`,
`Numlib.Eigen.HamiltonianSchur` and `Numlib.Eigen.PeriodicSchur`.

## Main results

* Figure 7.8.1, `GolubVanLoan.Chapter07.figure_7_8_1_skewHamiltonian`: $JN$ is skew-symmetric if and
  only if $N = \begin{bmatrix} A & G \\ F & A^T \end{bmatrix}$ with $F$ and $G$ skew-symmetric.
* Figure 7.8.1, `GolubVanLoan.Chapter07.figure_7_8_1_orthogonalSymplectic`: an orthogonal $Q$ is
  symplectic if and only if $JQ = QJ$, if and only if $Q = \begin{bmatrix} Q_1 & Q_2 \\ -Q_2 & Q_1
  \end{bmatrix}$ with $Q_1^T Q_2$ symmetric and $Q_1^T Q_1 + Q_2^T Q_2 = I$.
* §7.8.1 (1), `GolubVanLoan.Chapter07.hamiltonian_symplectic_conj`: a symplectic similarity
  preserves Hamiltonian and skew-Hamiltonian structure.
* §7.8.1 (2), `GolubVanLoan.Chapter07.hamiltonian_sq_skewHamiltonian`: the square of a Hamiltonian
  matrix is skew-Hamiltonian.
* §7.8.1 (3), `GolubVanLoan.Chapter07.hamiltonian_neg_mem_spectrum`: if $\lambda$ is an eigenvalue
  of a Hamiltonian matrix, so is $-\lambda$.
* §7.8.1 (4), `GolubVanLoan.Chapter07.symplectic_inv_mem_spectrum`: if $\lambda$ is an eigenvalue of
  a symplectic matrix, then $\lambda \neq 0$ and $1/\lambda$ is an eigenvalue.
* §7.8.1, `GolubVanLoan.Chapter07.symplectic_householder_givens`: symplectic Householder and Givens
  transformations are orthogonal symplectic, and they map every vector to a multiple of $e_1$.
* §7.8.1, `GolubVanLoan.Chapter07.hamiltonian_deflation_structure`: the deflation of a Hamiltonian
  matrix by a unit eigenvector of a real eigenvalue.
* (7.8.1), `GolubVanLoan.Chapter07.equation_7_8_1`: the real Hamiltonian–Schur decomposition.
* (7.8.2), `GolubVanLoan.Chapter07.equation_7_8_2`: the Hamiltonian–Schur form gives a symmetric
  solution of the algebraic Riccati equation.
* (7.8.3), `GolubVanLoan.Chapter07.equation_7_8_3`: the Paige–Van Loan form $\begin{bmatrix} H & R
  \\ D & -H^T \end{bmatrix}$.
* (7.8.4), `GolubVanLoan.Chapter07.equation_7_8_4`: $M^2$ is orthogonally symplectically similar to
  $\begin{bmatrix} H & R \\ 0 & H^T \end{bmatrix}$ with $H$ upper Hessenberg.
* §7.8.1, `GolubVanLoan.Chapter07.skewHamiltonian_schur`: the real skew-Hamiltonian Schur form of
  $M^2$.
* (7.8.5), `GolubVanLoan.Chapter07.equation_7_8_5`: the Hessenberg–triangular–triangular form of
  $A_3 A_2 A_1$.
* (7.8.6), `GolubVanLoan.Chapter07.equation_7_8_6`: the periodic real Schur form of $A_3 A_2 A_1$.
* §7.8.2, `GolubVanLoan.Chapter07.blockCyclic_restatement`: the reduction of the factors is a
  block-diagonal orthogonal transformation of the block-cyclic matrix.
* §7.8.2, `GolubVanLoan.Chapter07.blockCyclic_shuffle_isUpperHessenberg`: the perfect shuffle of the
  reduced block-cyclic matrix is upper Hessenberg.

## Conventions

* A $2n \times 2n$ matrix with $n \times n$ blocks is a real matrix indexed by `Fin n ⊕ Fin n`, and
  a block matrix $\begin{bmatrix} A & B \\ C & D \end{bmatrix}$ is `Matrix.fromBlocks A B C D`.
* The source's $J = \begin{bmatrix} 0 & I \\ -I & 0 \end{bmatrix}$ is `-Matrix.J (Fin n) ℝ`, since
  Mathlib's `Matrix.J` is $\begin{bmatrix} 0 & -I \\ I & 0 \end{bmatrix}$. Every structure in this
  section is invariant under $J \mapsto -J$, so the section states everything with Mathlib's
  `Matrix.J`. Chapter 1 states §1.3.10 with the source's $J$, `GolubVanLoan.Chapter01.bookJ`, and
  proves the two forms equivalent.
* Hamiltonian is the backbone's `Matrix.IsHamiltonian`, skew-Hamiltonian is
  `Matrix.IsSkewHamiltonian`, and symplectic is membership in Mathlib's
  `Matrix.symplecticGroup (Fin n) ℝ`. The Hamiltonian and symplectic rows of Figure 7.8.1 are
  `GolubVanLoan.Chapter01.isHamiltonian_iff` and `GolubVanLoan.Chapter01.symplectic_blocks` of
  Chapter 1; this section adds the skew-Hamiltonian and orthogonal symplectic rows.
* The complex eigenvalues of a real matrix $M$ are the elements of `spectrum ℂ M.complexify`.
* The product problem uses $A_1, A_2, A_3$ as the source does, with $A = A_3 A_2 A_1$. The
  block-cyclic theorems index the factors by `Fin 3`, with `A 0` for $A_1$, `A 1` for $A_2$ and
  `A 2` for $A_3$.

## Deviations from the source

* **Figure 7.8.1, orthogonal-symplectic row** (reading).
  `GolubVanLoan.Chapter07.figure_7_8_1_orthogonalSymplectic` takes orthogonality explicitly when
  characterizing symplecticity by $JQ=QJ$.
* **§7.8.1, structured vector reduction** (generalization).
  `GolubVanLoan.Chapter07.symplectic_householder_givens` allows any repeated orthogonal block
  and any target coordinate in the first block.
* **Equations (7.8.1)–(7.8.2)** (reading). `GolubVanLoan.Chapter07.equation_7_8_1` includes the
  stable ordering of $T$ specified in the Riccati discussion.
  `GolubVanLoan.Chapter07.equation_7_8_2` derives symmetry from the cross Gram identity and uses
  the block transformation without assuming symmetry of $F$ and $G$.
* **§7.8.2, perfect shuffle display** (typo). The source repeats the same permutation matrix on
  both sides. `GolubVanLoan.Chapter07.blockCyclic_shuffle_isUpperHessenberg` uses simultaneous
  row and column reindexing, equivalent to a permutation similarity.

## Not formalized

* **Display (7.8.7).** It describes convergence of product iterates that remain in
  Hessenberg–triangular–triangular form, without specifying convergence hypotheses.
* **The remark that a structure-preserving QR iteration has yet to be devised, and the quality of
  the eigenvalues computed from $M^2$.** The source makes no precise claims.
* **Rectangular and inverted factors in the product problem.** The source only mentions them.
-/

open Matrix

namespace GolubVanLoan.Chapter07

variable {n : ℕ}

/-! ### §7.8.1 Hamiltonian matrix eigenproblems -/

/-- **Figure 7.8.1** of [golub2013matrix], skew-Hamiltonian row. Let
$A, F, G, H \in \mathbb{R}^{n \times n}$ and $N = \begin{bmatrix} A & G \\ F & H \end{bmatrix}$.
Then $JN$ is skew-symmetric, $(JN)^T = -JN$, if and only if $$H = A^T, \qquad F^T = -F, \qquad
G^T = -G.$$

Here $J$ is Mathlib's `Matrix.J (Fin n) ℝ`. -/
theorem figure_7_8_1_skewHamiltonian (A G F H : Matrix (Fin n) (Fin n) ℝ) :
    (J (Fin n) ℝ * fromBlocks A G F H)ᵀ = -(J (Fin n) ℝ * fromBlocks A G F H) ↔
      H = Aᵀ ∧ Fᵀ = -F ∧ Gᵀ = -G := by
  rw [← isSkewHamiltonian_iff_transpose_J_mul, isSkewHamiltonian_fromBlocks_iff]

/-- **Figure 7.8.1** of [golub2013matrix], orthogonal symplectic row. Let
$Q \in \mathbb{R}^{2n \times 2n}$ be orthogonal. Then $Q$ is symplectic if and only if
$JQ = QJ$. Also, $Q$ is symplectic if and only if there are
$Q_1, Q_2 \in \mathbb{R}^{n \times n}$ with $$Q = \begin{bmatrix} Q_1 & Q_2 \\ -Q_2 & Q_1
\end{bmatrix}, \qquad Q_1^T Q_2 \text{ symmetric}, \qquad Q_1^T Q_1 + Q_2^T Q_2 = I.$$

The commutation $JQ = QJ$ is `Commute (Matrix.J (Fin n) ℝ) Q`.

**Reading.** The source places $JQ=QJ$ in the definition column for the orthogonal-symplectic
family. Lean states commutation as a characterization under the standing assumption that $Q$ is
orthogonal. -/
theorem figure_7_8_1_orthogonalSymplectic {Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ}
    (hQ : Q ∈ orthogonalGroup (Fin n ⊕ Fin n) ℝ) :
    (Q ∈ symplecticGroup (Fin n) ℝ ↔ Commute (J (Fin n) ℝ) Q) ∧
      (Q ∈ symplecticGroup (Fin n) ℝ ↔ ∃ Q₁ Q₂ : Matrix (Fin n) (Fin n) ℝ,
        Q = fromBlocks Q₁ Q₂ (-Q₂) Q₁ ∧ (Q₁ᵀ * Q₂).IsSymm ∧ Q₁ᵀ * Q₁ + Q₂ᵀ * Q₂ = 1) :=
  ⟨mem_symplecticGroup_iff_commute_J_of_mem_orthogonalGroup hQ, by
    rw [← mem_orthogonalGroup_symplecticGroup_iff]
    exact ⟨fun h => ⟨hQ, h⟩, fun h => h.2⟩⟩

/-- **§7.8.1 (1)** of [golub2013matrix]. Let $S \in \mathbb{R}^{2n \times 2n}$ be symplectic. If $M$
is Hamiltonian, then $S^{-1} M S$ is Hamiltonian, and if $N$ is skew-Hamiltonian, then
$S^{-1} N S$ is skew-Hamiltonian.

The source states "Symplectic similarity transformations preserve Hamiltonian structure"; it
remarks the skew-Hamiltonian case before (7.8.4).

**Reading.** Fact (1) states Hamiltonian preservation. Lean also includes the skew-Hamiltonian
counterpart mentioned in the discussion before (7.8.4). -/
theorem hamiltonian_symplectic_conj {S : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ}
    (hS : S ∈ symplecticGroup (Fin n) ℝ) :
    (∀ M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ, M.IsHamiltonian →
      (S⁻¹ * M * S).IsHamiltonian) ∧
    ∀ N : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ, N.IsSkewHamiltonian →
      (S⁻¹ * N * S).IsSkewHamiltonian :=
  ⟨fun _ hM => hM.conj_symplectic hS, fun _ hN => hN.conj_symplectic hS⟩

/-- **§7.8.1 (2)** of [golub2013matrix]. If $M \in \mathbb{R}^{2n \times 2n}$ is Hamiltonian, then
$M^2$ is skew-Hamiltonian. -/
theorem hamiltonian_sq_skewHamiltonian {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ}
    (hM : M.IsHamiltonian) : (M * M).IsSkewHamiltonian :=
  hM.isSkewHamiltonian_mul_self

/-- The complexification of Mathlib's real $J$ is the complex $J$. -/
private theorem complexify_J : (J (Fin n) ℝ).complexify = J (Fin n) ℂ := by
  ext (i | i) (j | j) <;> by_cases h : i = j <;> simp [J, complexify, h]

/-- For Mathlib's $J$ and $x = (u, v)$, $Jx = (-v, u)$, so that $(v, -u) = -Jx$. -/
private theorem J_mulVec_eq (x : Fin n ⊕ Fin n → ℂ) :
    J (Fin n) ℂ *ᵥ x = -Sum.elim (x ∘ Sum.inr) (-(x ∘ Sum.inl)) := by
  rw [J, fromBlocks_mulVec]
  ext (i | i) <;> simp [neg_mulVec]

/-- **§7.8.1 (3)** of [golub2013matrix]. Let $M \in \mathbb{R}^{2n \times 2n}$ be Hamiltonian. If
$\lambda \in \mathbb{C}$ is an eigenvalue of $M$, then $-\lambda$ is an eigenvalue of $M$. More
precisely, for every $u, v \in \mathbb{C}^n$ and $\lambda \in \mathbb{C}$, $$M \begin{bmatrix} u
\\ v \end{bmatrix} = \lambda \begin{bmatrix} u \\ v \end{bmatrix} \implies M^T \begin{bmatrix} v
\\ -u \end{bmatrix} = -\lambda \begin{bmatrix} v \\ -u \end{bmatrix}.$$

The second part is the witness of the source's proof. The eigenvalues are those of
`Matrix.complexify M`, and the vector $(u, v)$ is a function on `Fin n ⊕ Fin n`. -/
theorem hamiltonian_neg_mem_spectrum {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ}
    (hM : M.IsHamiltonian) :
    (∀ μ ∈ spectrum ℂ M.complexify, -μ ∈ spectrum ℂ M.complexify) ∧
      ∀ (x : Fin n ⊕ Fin n → ℂ) (μ : ℂ), M.complexify *ᵥ x = μ • x →
        (M.complexify)ᵀ *ᵥ Sum.elim (x ∘ Sum.inr) (-(x ∘ Sum.inl)) =
          (-μ) • Sum.elim (x ∘ Sum.inr) (-(x ∘ Sum.inl)) := by
  refine ⟨fun μ hμ => hM.neg_mem_spectrum hμ, fun x μ hx => ?_⟩
  have hJ : J (Fin n) ℂ * M.complexify = -(M.complexify)ᵀ * J (Fin n) ℂ := by
    have h := congrArg complexify (isHamiltonian_iff_J_mul_eq.1 hM)
    rwa [complexify_mul, complexify_mul, complexify_neg, complexify_transpose, complexify_J] at h
  have key : (M.complexify)ᵀ *ᵥ (J (Fin n) ℂ *ᵥ x) = (-μ) • (J (Fin n) ℂ *ᵥ x) := by
    have h := congrArg (· *ᵥ x) hJ
    simp only [← mulVec_mulVec, hx, mulVec_smul, Matrix.neg_mul, neg_mulVec] at h
    rw [neg_smul, h, neg_neg]
  rw [J_mulVec_eq, mulVec_neg, smul_neg, neg_inj] at key
  exact key

/-- **§7.8.1 (4)** of [golub2013matrix]. Let $S \in \mathbb{R}^{2n \times 2n}$ be symplectic. If
$\lambda \in \mathbb{C}$ is an eigenvalue of $S$, then $\lambda \neq 0$ and $1/\lambda$ is an
eigenvalue of $S$. More precisely, for every $u, v \in \mathbb{C}^n$ and $\lambda \neq 0$, $$S
\begin{bmatrix} u \\ v \end{bmatrix} = \lambda \begin{bmatrix} u \\ v \end{bmatrix} \implies S^T
\begin{bmatrix} v \\ -u \end{bmatrix} = \frac{1}{\lambda} \begin{bmatrix} v \\ -u
\end{bmatrix}.$$

The second part is the witness of the source's proof. The eigenvalues are those of
`Matrix.complexify S`. -/
theorem symplectic_inv_mem_spectrum {S : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ}
    (hS : S ∈ symplecticGroup (Fin n) ℝ) :
    (∀ μ ∈ spectrum ℂ S.complexify, μ ≠ 0 ∧ μ⁻¹ ∈ spectrum ℂ S.complexify) ∧
      ∀ (x : Fin n ⊕ Fin n → ℂ) (μ : ℂ), μ ≠ 0 → S.complexify *ᵥ x = μ • x →
        (S.complexify)ᵀ *ᵥ Sum.elim (x ∘ Sum.inr) (-(x ∘ Sum.inl)) =
          μ⁻¹ • Sum.elim (x ∘ Sum.inr) (-(x ∘ Sum.inl)) := by
  refine ⟨fun μ hμ => inv_mem_spectrum_of_mem_symplecticGroup hS hμ, fun x μ hμ hx => ?_⟩
  have hSJ : (S.complexify)ᵀ * J (Fin n) ℂ * S.complexify = J (Fin n) ℂ := by
    have h := congrArg complexify (SymplecticGroup.mem_iff'.1 hS)
    rwa [complexify_mul, complexify_mul, complexify_transpose, complexify_J] at h
  have key : (S.complexify)ᵀ *ᵥ (J (Fin n) ℂ *ᵥ x) = μ⁻¹ • (J (Fin n) ℂ *ᵥ x) := by
    have h := congrArg (· *ᵥ x) hSJ
    simp only [← mulVec_mulVec, hx, mulVec_smul] at h
    calc (S.complexify)ᵀ *ᵥ (J (Fin n) ℂ *ᵥ x)
        = μ⁻¹ • (μ • ((S.complexify)ᵀ *ᵥ (J (Fin n) ℂ *ᵥ x))) := by
          rw [smul_smul, inv_mul_cancel₀ hμ, one_smul]
      _ = μ⁻¹ • (J (Fin n) ℂ *ᵥ x) := by rw [h]
  rw [J_mulVec_eq, mulVec_neg, smul_neg, neg_inj] at key
  exact key

/-- **§7.8.1** of [golub2013matrix], symplectic Householder and Givens transformations. The
following hold.

1. If $P \in \mathbb{R}^{n \times n}$ is orthogonal, for example a Householder matrix
   $I - 2vv^T$, then $\operatorname{diag}(P, P)$ is orthogonal and symplectic.
2. If $c^2 + s^2 = 1$ and $1 \le i \le n$, then the Givens rotation in the coordinate planes $i$
   and $n + i$ is orthogonal and symplectic.
3. For every $x \in \mathbb{R}^{2n}$ and every $1 \le i_0 \le n$ there is an orthogonal
   symplectic $Q$ with $Q^T x = \|x\|_2 e_{i_0}$.

The third part is the result of the source's Householder–Givens–Householder sequence; the source
takes $i_0 = 1$. The Givens rotation is `Matrix.planeRotation (Sum.inl i) (Sum.inr i) c s`, and
$e_{i_0}$ is `Pi.single (Sum.inl i₀) 1`.

**Generalization.** The source gives a block-diagonal Householder example and illustrates the
vector reduction to the first coordinate. Lean allows any orthogonal matrix in the diagonal
pair and any coordinate in the first block for the vector reduction. -/
theorem symplectic_householder_givens :
    (∀ P : Matrix (Fin n) (Fin n) ℝ, P ∈ orthogonalGroup (Fin n) ℝ →
      fromBlocks P 0 0 P ∈ orthogonalGroup (Fin n ⊕ Fin n) ℝ ∧
        fromBlocks P 0 0 P ∈ symplecticGroup (Fin n) ℝ) ∧
    (∀ (i : Fin n) (c s : ℝ), c ^ 2 + s ^ 2 = 1 →
      planeRotation (Sum.inl i) (Sum.inr i) c s ∈ orthogonalGroup (Fin n ⊕ Fin n) ℝ ∧
        planeRotation (Sum.inl i) (Sum.inr i) c s ∈ symplecticGroup (Fin n) ℝ) ∧
    ∀ (x : Fin n ⊕ Fin n → ℝ) (i₀ : Fin n),
      ∃ Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ, Q ∈ orthogonalGroup (Fin n ⊕ Fin n) ℝ ∧
        Q ∈ symplecticGroup (Fin n) ℝ ∧
        Qᵀ *ᵥ x = ‖WithLp.toLp 2 x‖ • Pi.single (Sum.inl i₀) 1 :=
  ⟨fun _ hP => fromBlocks_diagonal_mem_orthoSymplecticGroup hP,
    fun i _ _ hcs => planeRotation_inl_inr_mem_orthoSymplecticGroup i hcs, fun x i₀ => by
      obtain ⟨Q, ⟨hQo, hQs⟩, hQ⟩ := exists_orthogonalSymplectic_mulVec_eq x i₀
      exact ⟨Q, hQo, hQs, hQ⟩⟩

/-- **§7.8.1** of [golub2013matrix], the deflation step displayed before (7.8.1). Let $n \ge 1$, let
$M \in \mathbb{R}^{2n \times 2n}$ be Hamiltonian, and let $Mx = \lambda x$ with
$\lambda \in \mathbb{R}$ and $x \in \mathbb{R}^{2n}$. Let $Q_1$ be orthogonal and symplectic
with $Q_1^T x = e_1$, so that $\|x\|_2 = 1$. Then $Q_1^T M Q_1$ is Hamiltonian, its first column
is $\lambda e_1$, its row $n + 1$ is $-\lambda e_{n+1}^T$, and the submatrix in the rows and
columns $2{:}n$ and $n{+}2{:}2n$ is a $(2n-2) \times (2n-2)$ Hamiltonian matrix.

In the words of the source, "the 'extra' zeros follow from the Hamiltonian structure of
$Q_1^T M Q_1$", and on the submatrix "the process can be repeated". Here $n = N + 1$, the index
type is `Fin (N+1) ⊕ Fin (N+1)`, $e_1$ is at `Sum.inl 0`, row $n + 1$ is `Sum.inr 0`, and the
submatrix is the reindexing by `Sum.map Fin.succ Fin.succ`. -/
theorem hamiltonian_deflation_structure {N : ℕ}
    {M Q₁ : Matrix (Fin (N + 1) ⊕ Fin (N + 1)) (Fin (N + 1) ⊕ Fin (N + 1)) ℝ}
    (hM : M.IsHamiltonian) (hQo : Q₁ ∈ orthogonalGroup (Fin (N + 1) ⊕ Fin (N + 1)) ℝ)
    (hQs : Q₁ ∈ symplecticGroup (Fin (N + 1)) ℝ) {x : Fin (N + 1) ⊕ Fin (N + 1) → ℝ} {μ : ℝ}
    (hx : M *ᵥ x = μ • x) (hQx : Q₁ᵀ *ᵥ x = Pi.single (Sum.inl 0) 1) :
    (∀ i, (Q₁ᵀ * M * Q₁) i (Sum.inl 0) = if i = Sum.inl 0 then μ else 0) ∧
      (∀ j, (Q₁ᵀ * M * Q₁) (Sum.inr 0) j = if j = Sum.inr 0 then -μ else 0) ∧
      (Q₁ᵀ * M * Q₁).IsHamiltonian ∧
      ((Q₁ᵀ * M * Q₁).submatrix (Sum.map Fin.succ Fin.succ)
        (Sum.map Fin.succ Fin.succ)).IsHamiltonian := by
  have hQQ : Q₁ * Q₁ᵀ = 1 := (mem_orthogonalGroup_iff _ ℝ).1 hQo
  have hQQ' : Q₁ᵀ * Q₁ = 1 := (mem_orthogonalGroup_iff' _ ℝ).1 hQo
  have hH : (Q₁ᵀ * M * Q₁).IsHamiltonian := by
    have h := hM.conj_symplectic hQs
    rwa [Matrix.inv_eq_left_inv hQQ'] at h
  have hcol : ∀ i, (Q₁ᵀ * M * Q₁) i (Sum.inl 0) = if i = Sum.inl 0 then μ else 0 := by
    have hxe : Q₁ *ᵥ Pi.single (Sum.inl 0) 1 = x := by
      rw [← hQx, mulVec_mulVec, hQQ, one_mulVec]
    have hv : (Q₁ᵀ * M * Q₁) *ᵥ Pi.single (Sum.inl 0) 1 =
        μ • (Pi.single (Sum.inl 0) 1 : Fin (N + 1) ⊕ Fin (N + 1) → ℝ) := by
      rw [← mulVec_mulVec, hxe, ← mulVec_mulVec, hx, mulVec_smul, hQx]
    intro i
    have h := congrFun hv i
    rw [mulVec_single_one, col_apply] at h
    rw [h, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    split_ifs <;> simp
  refine ⟨hcol, ?_, hH, ?_⟩
  · rw [← fromBlocks_toBlocks (Q₁ᵀ * M * Q₁), isHamiltonian_fromBlocks_iff] at hH
    obtain ⟨hD, hF, -⟩ := hH
    intro j
    rcases j with j | j
    · have h := congrFun (congrFun hF j) 0
      simp only [transpose_apply, toBlocks₂₁, of_apply] at h
      rw [h, hcol]
      simp
    · have h := congrFun (congrFun hD 0) j
      simp only [Matrix.neg_apply, transpose_apply, toBlocks₂₂, toBlocks₁₁, of_apply] at h
      rw [h, hcol]
      by_cases hj : j = 0
      · subst hj; simp
      · simp [hj]
  · rw [← fromBlocks_toBlocks (Q₁ᵀ * M * Q₁), fromBlocks_submatrix_sum_map,
      isHamiltonian_fromBlocks_iff]
    rw [← fromBlocks_toBlocks (Q₁ᵀ * M * Q₁), isHamiltonian_fromBlocks_iff] at hH
    obtain ⟨hD, hF, hG⟩ := hH
    refine ⟨?_, ?_, ?_⟩
    · rw [hD]; rfl
    · rw [transpose_submatrix, hF]
    · rw [transpose_submatrix, hG]

/-- **Equation (7.8.1)** of [golub2013matrix], the real Hamiltonian–Schur decomposition. Let
$M \in \mathbb{R}^{2n \times 2n}$ be Hamiltonian with no eigenvalue on the imaginary axis. Then
there are $Q_1, Q_2, T, R \in \mathbb{R}^{n \times n}$ such that $Q = \begin{bmatrix} Q_1 & Q_2
\\ -Q_2 & Q_1 \end{bmatrix}$ is orthogonal and symplectic, $$Q^T M Q = \begin{bmatrix} T & R \\
0 & -T^T \end{bmatrix},$$ $T$ is upper quasi-triangular, and every eigenvalue of $T$ has
negative real part.

The hypothesis is that every complex eigenvalue of $M$ has nonzero real part.

**Reading.** The source adds left-half-plane ordering of $T$ in the Riccati discussion after
(7.8.2). The Lean existence theorem includes that ordering in the decomposition. -/
theorem equation_7_8_1 {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ} (hM : M.IsHamiltonian)
    (hre : ∀ μ ∈ spectrum ℂ M.complexify, μ.re ≠ 0) :
    ∃ Q₁ Q₂ T R : Matrix (Fin n) (Fin n) ℝ,
      fromBlocks Q₁ Q₂ (-Q₂) Q₁ ∈ orthogonalGroup (Fin n ⊕ Fin n) ℝ ∧
      fromBlocks Q₁ Q₂ (-Q₂) Q₁ ∈ symplecticGroup (Fin n) ℝ ∧
      (fromBlocks Q₁ Q₂ (-Q₂) Q₁)ᵀ * M * fromBlocks Q₁ Q₂ (-Q₂) Q₁ = fromBlocks T R 0 (-Tᵀ) ∧
      T.IsQuasiUpperTriangular ∧ ∀ μ ∈ spectrum ℂ T.complexify, μ.re < 0 := by
  obtain ⟨Q, ⟨hQo, hQs⟩, T, R, hQM, hT, hst⟩ := exists_orthogonalSymplectic_hamiltonianSchur hM hre
  obtain ⟨Q₁, Q₂, rfl, -, -⟩ := (figure_7_8_1_orthogonalSymplectic hQo).2.1 hQs
  exact ⟨Q₁, Q₂, T, R, hQo, hQs, hQM, hT, hst⟩

/-- **Equation (7.8.2)** of [golub2013matrix], the algebraic Riccati equation. Let $A, F, G, T, R,
Q_1, Q_2 \in \mathbb{R}^{n \times n}$. Suppose that $Q = \begin{bmatrix} Q_1 & Q_2 \\ -Q_2 & Q_1
\end{bmatrix}$ is orthogonal, that $$Q^T \begin{bmatrix} A & F \\ G & -A^T \end{bmatrix} Q =
\begin{bmatrix} T & R \\ 0 & -T^T \end{bmatrix},$$ and that $Q_1$ is nonsingular. Let
$X = Q_2 Q_1^{-1}$. Then $X$ is symmetric, $$G + XA + A^T X - XFX = 0,$$
$A - FX = Q_1 T Q_1^{-1}$, and therefore $\lambda(A - FX) = \lambda(T)$.

If $T$ is chosen as in (7.8.1), the eigenvalues of $A - FX$ lie in the open left half-plane. The
source derives the symmetry of $X$ "from $I_n = Q_1^T Q_1 + Q_2^T Q_2$"; it follows from the
symmetry of $Q_1^T Q_2$. The theorem assumes neither that $F$ and $G$ are symmetric nor that $Q$
is symplectic.

**Reading.** The source attributes the symmetry of $Q_2Q_1^{-1}$ to the diagonal Gram identity
alone. The proof uses symmetry of the cross Gram block $Q_1^TQ_2$, which follows from the block
orthogonality. The stated conclusions use the block transformation without assuming $F$ and $G$
symmetric. -/
theorem equation_7_8_2 {A F G T R Q₁ Q₂ : Matrix (Fin n) (Fin n) ℝ}
    (hQ : fromBlocks Q₁ Q₂ (-Q₂) Q₁ ∈ orthogonalGroup (Fin n ⊕ Fin n) ℝ)
    (hS : (fromBlocks Q₁ Q₂ (-Q₂) Q₁)ᵀ * fromBlocks A F G (-Aᵀ) * fromBlocks Q₁ Q₂ (-Q₂) Q₁ =
      fromBlocks T R 0 (-Tᵀ)) (hQ₁ : IsUnit Q₁) :
    (Q₂ * Q₁⁻¹).IsSymm ∧
      G + Q₂ * Q₁⁻¹ * A + Aᵀ * (Q₂ * Q₁⁻¹) - Q₂ * Q₁⁻¹ * F * (Q₂ * Q₁⁻¹) = 0 ∧
      A - F * (Q₂ * Q₁⁻¹) = Q₁ * T * Q₁⁻¹ ∧
      spectrum ℂ (A - F * (Q₂ * Q₁⁻¹)).complexify = spectrum ℂ T.complexify := by
  obtain ⟨h1, h2, h3⟩ := riccati_of_hamiltonianSchur hQ hS hQ₁
  refine ⟨h1, h2, h3, ?_⟩
  have hsim : IsSimilar (A - F * (Q₂ * Q₁⁻¹)).complexify T.complexify := by
    refine ⟨Q₁.complexify, (isUnit_complexify_iff Q₁).2 hQ₁, ?_⟩
    rw [h3, ← complexify_inv, ← complexify_mul, ← complexify_mul, Matrix.mul_assoc,
      Matrix.mul_assoc, Matrix.mul_assoc,
      nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hQ₁), Matrix.mul_one, ← Matrix.mul_assoc,
      nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hQ₁), Matrix.one_mul]
  exact IsSimilar.spectrum_eq hsim

/-- **Equation (7.8.3)** of [golub2013matrix], the Paige–Van Loan form. If
$M \in \mathbb{R}^{2n \times 2n}$ is Hamiltonian, then there is an orthogonal symplectic $U_0$
and there are $H, R, D \in \mathbb{R}^{n \times n}$ such that $$U_0^T M U_0 = \begin{bmatrix} H
& R \\ D & -H^T \end{bmatrix},$$ where $H$ is upper Hessenberg and $D$ is diagonal.

The source says that $U_0$ is "easy to compute" but gives no algorithm. The proof is
`Matrix.IsHamiltonian.exists_orthogonalSymplectic_paigeVanLoan`. -/
theorem equation_7_8_3 {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ} (hM : M.IsHamiltonian) :
    ∃ U₀ ∈ orthogonalGroup (Fin n ⊕ Fin n) ℝ, U₀ ∈ symplecticGroup (Fin n) ℝ ∧
      ∃ H R D : Matrix (Fin n) (Fin n) ℝ,
        U₀ᵀ * M * U₀ = fromBlocks H R D (-Hᵀ) ∧ H.IsUpperHessenberg ∧ D.IsDiag := by
  obtain ⟨U₀, ⟨hUo, hUs⟩, H, R, D, h, hH, hD⟩ := hM.exists_orthogonalSymplectic_paigeVanLoan
  exact ⟨U₀, hUo, hUs, H, R, D, h, hH, hD⟩

/-- **Equation (7.8.4)** of [golub2013matrix]. If $M \in \mathbb{R}^{2n \times 2n}$ is Hamiltonian,
then there is an orthogonal symplectic $V_0$ and there are $H, R \in \mathbb{R}^{n \times n}$
such that $$V_0^T M^2 V_0 = \begin{bmatrix} H & R \\ 0 & H^T \end{bmatrix},$$ where $H$ is upper
Hessenberg.

The matrix $M^2$ is skew-Hamiltonian (`GolubVanLoan.Chapter07.hamiltonian_sq_skewHamiltonian`),
and "because the (2,1) block of a skew-Hamiltonian matrix is skew-symmetric, it has a zero
diagonal". The proof applies `Matrix.IsSkewHamiltonian.exists_orthogonalSymplectic_hessenberg`. -/
theorem equation_7_8_4 {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ} (hM : M.IsHamiltonian) :
    ∃ V₀ ∈ orthogonalGroup (Fin n ⊕ Fin n) ℝ, V₀ ∈ symplecticGroup (Fin n) ℝ ∧
      ∃ H R : Matrix (Fin n) (Fin n) ℝ,
        V₀ᵀ * (M * M) * V₀ = fromBlocks H R 0 Hᵀ ∧ H.IsUpperHessenberg := by
  obtain ⟨V₀, ⟨hVo, hVs⟩, H, R, h, hH⟩ :=
    (hamiltonian_sq_skewHamiltonian hM).exists_orthogonalSymplectic_hessenberg
  exact ⟨V₀, hVo, hVs, H, R, h, hH⟩

/-- **§7.8.1** of [golub2013matrix], the real skew-Hamiltonian Schur form. Let
$M \in \mathbb{R}^{2n \times 2n}$ be Hamiltonian. The following hold.

1. If $V_0 \in \mathbb{R}^{2n \times 2n}$ and $H, R, U \in \mathbb{R}^{n \times n}$ satisfy
   $V_0^T M^2 V_0 = \begin{bmatrix} H & R \\ 0 & H^T \end{bmatrix}$, then
   $Q = V_0 \operatorname{diag}(U, U)$ satisfies $$Q^T M^2 Q = \begin{bmatrix} U^T H U & U^T R U
   \\ 0 & (U^T H U)^T \end{bmatrix}.$$
2. There is an orthogonal symplectic $Q$ and there are $T, R \in \mathbb{R}^{n \times n}$ with
   $Q^T M^2 Q = \begin{bmatrix} T & R \\ 0 & T^T \end{bmatrix}$ and $T$ upper quasi-triangular.

The source states the first part for the $V_0$ of (7.8.4) and the orthogonal $U$ of a real Schur
form $U^T H U = T$; the identity holds for every $V_0$ and $U$. The second part is
`Matrix.IsSkewHamiltonian.exists_orthogonalSymplectic_schur`. -/
theorem skewHamiltonian_schur {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ}
    (hM : M.IsHamiltonian) :
    (∀ {V₀ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ} {H R U : Matrix (Fin n) (Fin n) ℝ},
      V₀ᵀ * (M * M) * V₀ = fromBlocks H R 0 Hᵀ →
        (V₀ * fromBlocks U 0 0 U)ᵀ * (M * M) * (V₀ * fromBlocks U 0 0 U) =
          fromBlocks (Uᵀ * H * U) (Uᵀ * R * U) 0 (Uᵀ * H * U)ᵀ) ∧
    ∃ Q ∈ orthogonalGroup (Fin n ⊕ Fin n) ℝ, Q ∈ symplecticGroup (Fin n) ℝ ∧
      ∃ T R : Matrix (Fin n) (Fin n) ℝ,
        Qᵀ * (M * M) * Q = fromBlocks T R 0 Tᵀ ∧ T.IsQuasiUpperTriangular := by
  refine ⟨fun {V₀ H R U} hHR => ?_, ?_⟩
  · have key : (V₀ * fromBlocks U 0 0 U)ᵀ * (M * M) * (V₀ * fromBlocks U 0 0 U)
        = (fromBlocks U 0 0 U)ᵀ * (V₀ᵀ * (M * M) * V₀) * fromBlocks U 0 0 U := by
      rw [transpose_mul]
      simp only [Matrix.mul_assoc]
    rw [key, hHR, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply]
    simp only [transpose_zero, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add,
      transpose_mul, transpose_transpose, Matrix.mul_assoc]
  · obtain ⟨Q, ⟨hQo, hQs⟩, T, R, h, hT⟩ :=
      (hamiltonian_sq_skewHamiltonian hM).exists_orthogonalSymplectic_schur
    exact ⟨Q, hQo, hQs, T, R, h, hT⟩

/-! ### §7.8.2 Product eigenvalue problems -/

/-- **Equation (7.8.5)** of [golub2013matrix] and the display after it. For
$A_1, A_2, A_3 \in \mathbb{R}^{n \times n}$ there are orthogonal $U_1, U_2, U_3$ such that
$U_1^T A_3 U_3 = H_3$ is upper Hessenberg, $U_3^T A_2 U_2 = T_2$ and $U_2^T A_1 U_1 = T_1$ are
upper triangular, and $$U_1^T (A_3 A_2 A_1) U_1 = H_3 T_2 T_1$$ is upper Hessenberg.

The source describes a procedure, QR factorizations followed by Givens rotations with bulge
chasing, but gives no algorithm. -/
theorem equation_7_8_5 (A₁ A₂ A₃ : Matrix (Fin n) (Fin n) ℝ) :
    ∃ U₁ ∈ orthogonalGroup (Fin n) ℝ, ∃ U₂ ∈ orthogonalGroup (Fin n) ℝ,
      ∃ U₃ ∈ orthogonalGroup (Fin n) ℝ,
        (U₁ᵀ * A₃ * U₃).IsUpperHessenberg ∧ (U₃ᵀ * A₂ * U₂).IsUpperTriangular ∧
          (U₂ᵀ * A₁ * U₁).IsUpperTriangular ∧ (U₁ᵀ * (A₃ * A₂ * A₁) * U₁).IsUpperHessenberg := by
  obtain ⟨U, hU, hT, hH⟩ := exists_orthogonal_periodicHessenberg ![A₁, A₂, A₃]
  have hT₁ : ((U 1)ᵀ * A₁ * U 0).IsUpperTriangular := by simpa using hT 0
  have hT₂ : ((U 2)ᵀ * A₂ * U 1).IsUpperTriangular := by simpa using hT 1
  have hH₃ : ((U 0)ᵀ * A₃ * U 2).IsUpperHessenberg := by simpa using hH
  have h2 : U 2 * (U 2)ᵀ = 1 := (mem_orthogonalGroup_iff (Fin n) ℝ).1 (hU 2)
  have h1 : U 1 * (U 1)ᵀ = 1 := (mem_orthogonalGroup_iff (Fin n) ℝ).1 (hU 1)
  have hprod : (U 0)ᵀ * (A₃ * A₂ * A₁) * U 0 =
      ((U 0)ᵀ * A₃ * U 2) * ((U 2)ᵀ * A₂ * U 1) * ((U 1)ᵀ * A₁ * U 0) := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (U 2) (U 2)ᵀ, h2, Matrix.one_mul, ← Matrix.mul_assoc (U 1) (U 1)ᵀ, h1,
      Matrix.one_mul]
  refine ⟨U 0, hU 0, U 1, hU 1, U 2, hU 2, hH₃, hT₂, hT₁, ?_⟩
  rw [hprod]
  exact (hH₃.mul_isUpperTriangular hT₂).mul_isUpperTriangular hT₁

/-- **Equation (7.8.6)** of [golub2013matrix], the periodic real Schur form. For
$A_1, A_2, A_3 \in \mathbb{R}^{n \times n}$ there are orthogonal $Q_1, Q_2, Q_3$ such that
$Q_1^T A_3 Q_3 = T_3$ is upper quasi-triangular, $Q_3^T A_2 Q_2 = T_2$ and $Q_2^T A_1 Q_1 = T_1$
are upper triangular, and $Q_1^T (A_3 A_2 A_1) Q_1 = T_3 T_2 T_1$ is upper quasi-triangular, a
real Schur form of the product. -/
theorem equation_7_8_6 (A₁ A₂ A₃ : Matrix (Fin n) (Fin n) ℝ) :
    ∃ Q₁ ∈ orthogonalGroup (Fin n) ℝ, ∃ Q₂ ∈ orthogonalGroup (Fin n) ℝ,
      ∃ Q₃ ∈ orthogonalGroup (Fin n) ℝ,
        (Q₁ᵀ * A₃ * Q₃).IsQuasiUpperTriangular ∧ (Q₃ᵀ * A₂ * Q₂).IsUpperTriangular ∧
          (Q₂ᵀ * A₁ * Q₁).IsUpperTriangular ∧
          (Q₁ᵀ * (A₃ * A₂ * A₁) * Q₁).IsQuasiUpperTriangular := by
  obtain ⟨U, hU, hT, hH⟩ := exists_orthogonal_periodicRealSchur ![A₁, A₂, A₃]
  have hT₁ : ((U 1)ᵀ * A₁ * U 0).IsUpperTriangular := by simpa using hT 0
  have hT₂ : ((U 2)ᵀ * A₂ * U 1).IsUpperTriangular := by simpa using hT 1
  have hH₃ : ((U 0)ᵀ * A₃ * U 2).IsQuasiUpperTriangular := by simpa using hH
  have h2 : U 2 * (U 2)ᵀ = 1 := (mem_orthogonalGroup_iff (Fin n) ℝ).1 (hU 2)
  have h1 : U 1 * (U 1)ᵀ = 1 := (mem_orthogonalGroup_iff (Fin n) ℝ).1 (hU 1)
  have hprod : (U 0)ᵀ * (A₃ * A₂ * A₁) * U 0 =
      ((U 0)ᵀ * A₃ * U 2) * ((U 2)ᵀ * A₂ * U 1) * ((U 1)ᵀ * A₁ * U 0) := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (U 2) (U 2)ᵀ, h2, Matrix.one_mul, ← Matrix.mul_assoc (U 1) (U 1)ᵀ, h1,
      Matrix.one_mul]
  refine ⟨U 0, hU 0, U 1, hU 1, U 2, hU 2, hH₃, hT₂, hT₁, ?_⟩
  rw [hprod]
  exact (hH₃.mul_isUpperTriangular hT₂).mul_isUpperTriangular hT₁

/-- **§7.8.2** of [golub2013matrix], the block-cyclic restatement. Let $A_1, A_2, A_3, U_1, U_2, U_3
\in \mathbb{R}^{n \times n}$ and $U = \operatorname{diag}(U_1, U_2, U_3)$. Then $$U^T
\begin{bmatrix} 0 & 0 & A_3 \\ A_1 & 0 & 0 \\ 0 & A_2 & 0 \end{bmatrix} U = \begin{bmatrix} 0 &
0 & U_1^T A_3 U_3 \\ U_2^T A_1 U_1 & 0 & 0 \\ 0 & U_3^T A_2 U_2 & 0 \end{bmatrix}.$$ For the
$U_i$ of (7.8.5) the right side is the source's $\tilde H = \begin{bmatrix} 0 & 0 & H_3 \\ T_1 &
0 & 0 \\ 0 & T_2 & 0 \end{bmatrix}$.

The factors are indexed by `Fin 3`: `A 0` is $A_1$ and `U 0` is $U_1$. The block-cyclic matrix
is `Matrix.blockCyclic A`, whose block $(i + 1, i)$ is `A i` with indices modulo 3, and $U$ is
Mathlib's `Matrix.blockDiagonal U`. Both are indexed by `Fin n × Fin 3`, with the block index
second. -/
theorem blockCyclic_restatement (A U : Fin 3 → Matrix (Fin n) (Fin n) ℝ) :
    (blockDiagonal U)ᵀ * blockCyclic A * blockDiagonal U =
      blockCyclic fun i => (U (i + 1))ᵀ * A i * U i :=
  blockDiagonal_conj_blockCyclic A U

/-- **§7.8.2** of [golub2013matrix], the perfect shuffle. Let $T_1, T_2 \in \mathbb{R}^{n \times n}$
be upper triangular and $H_3 \in \mathbb{R}^{n \times n}$ upper Hessenberg, and let $\tilde H =
\begin{bmatrix} 0 & 0 & H_3 \\ T_1 & 0 & 0 \\ 0 & T_2 & 0 \end{bmatrix}$. If $\mathcal{P}$ is
the perfect shuffle permutation, then $\mathcal{P} \tilde H \mathcal{P}^T$ is upper Hessenberg.

The source says that "$\mathcal{P} \tilde H \mathcal{P}^T$ is a highly structured upper
Hessenberg matrix" and displays the case $n = 4$; the theorem holds for every $n$. The factors
are `A 0` $= T_1$, `A 1` $= T_2$ and `A 2` $= H_3$. The shuffle is the reindexing of
`Matrix.blockCyclic A` by `finProdFinEquiv.symm`, which puts row $i$ of block $k$ at position
$3i + k$ (0-based).

**Typo.** The source prints the same perfect shuffle on both sides of $\widetilde H$. The
displayed Hessenberg pattern comes from a simultaneous row and column reindexing, which uses
the inverse permutation factor on one side. -/
theorem blockCyclic_shuffle_isUpperHessenberg {A : Fin 3 → Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ i : Fin 2, (A i.castSucc).IsUpperTriangular) (hH : (A 2).IsUpperHessenberg) :
    ((blockCyclic A).submatrix finProdFinEquiv.symm finProdFinEquiv.symm).IsUpperHessenberg :=
  isUpperHessenberg_reindex_blockCyclic hA hH

end GolubVanLoan.Chapter07
