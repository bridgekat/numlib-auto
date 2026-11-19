/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Eigen.MinMax
import Numlib.LinearAlgebra.Matrix.LeastSquares
import Numlib.LinearAlgebra.Matrix.SVD
import Numlib.LinearAlgebra.Tensor.CP
import Numlib.LinearAlgebra.Tensor.HOSVD
import Numlib.LinearAlgebra.Tensor.SingularValue
import Numlib.LinearAlgebra.Tensor.Train
import Numlib.LinearAlgebra.Tensor.Tucker
import NumlibSurface.GolubVanLoan.Chapter12.Section03
import NumlibSurface.GolubVanLoan.Chapter12.Section04

/-!
# Golub and Van Loan, Section 12.5: Tensor decompositions and iterations

This module formalizes §12.5 of [golub2013matrix], which extends the singular value decomposition
(SVD) of a matrix to tensors $\mathcal{A} \in \mathbb{R}^{n_1 \times \cdots \times n_d}$. It starts
from the SVD viewpoint (12.5.1)–(12.5.3), in which the leading left singular vectors of $A$ maximize
$\|Q^T A\|_F$. It then treats the higher-order SVD of Theorem 12.5.1, $\mathcal{A} = \mathcal{S}
\times_1 U_1 \cdots \times_d U_d$ with $U_k$ the left factor of an SVD of the mode-$k$ unfolding
$\mathcal{A}_{(k)}$, and the error of its truncation (12.5.11); the Tucker problem of §12.5.3 and
its alternating update; the CP problem and the normal equations of its alternating least squares
update (12.5.14)–(12.5.21); singular values and eigenvalues as stationary values of Rayleigh
quotients, for matrices and for tensors (12.5.22)–(12.5.24); and tensor trains (12.5.25)–(12.5.29).

The proofs specialize the backbone modules `Numlib.LinearAlgebra.Matrix.SVD`, `Numlib.Eigen.MinMax`,
`Numlib.LinearAlgebra.Matrix.LeastSquares`, `Numlib.LinearAlgebra.Tensor.HOSVD`,
`Numlib.LinearAlgebra.Tensor.Tucker`, `Numlib.LinearAlgebra.Tensor.CP`,
`Numlib.LinearAlgebra.Tensor.SingularValue` and `Numlib.LinearAlgebra.Tensor.Train`, and use the
unfoldings and products of `NumlibSurface.GolubVanLoan.Chapter12.Section04`.

## Main definitions

* Equation (12.5.25), `GolubVanLoan.Chapter12.trainOfCarriages`: the tensor train of a list of
  carriages $\mathcal{G}_k \in \mathbb{R}^{r_{k-1} \times n_k \times r_k}$.

## Main results

* Equations (12.5.1)–(12.5.2), `GolubVanLoan.Chapter12.equation_12_5_1`: for an SVD
  $A = U \Sigma V^T$, the rows of $U^T A = \Sigma V^T$ are orthogonal with nonincreasing norms.
* Equation (12.5.3), `GolubVanLoan.Chapter12.equation_12_5_3`: the maximum of $\|Q^T A\|_F^2$ over
  $Q$ with $r$ orthonormal columns is $\sigma_1^2 + \cdots + \sigma_r^2$, attained at
  $Q = U(:, 1{:}r)$.
* §12.5.1 and (12.5.5), `GolubVanLoan.Chapter12.hosvd_modeProduct_slices`: the rows of the mode-$k$
  unfolding of $\mathcal{A} \times_k U_k^T$ are orthogonal with norms $\sigma_i(\mathcal{A}_{(k)})$.
* Theorem 12.5.1, `GolubVanLoan.Chapter12.theorem_12_5_1`: the higher-order SVD $\mathcal{A} =
  \mathcal{S} \times_1 U_1 \cdots \times_d U_d$, in the forms (12.5.6)–(12.5.9).
* Theorem 12.5.1, `GolubVanLoan.Chapter12.theorem_12_5_1_b`: the rows of $\mathcal{S}_{(k)}$ are
  orthogonal with norms $\sigma_i(\mathcal{A}_{(k)})$, (12.5.10).
* Equation (12.5.11), `GolubVanLoan.Chapter12.equation_12_5_11`: the squared error of the truncated
  HOSVD is at most the sum over the modes of the tails of the squared singular values.
* §12.5.3, `GolubVanLoan.Chapter12.tucker_best_core`: for fixed factors with orthonormal columns,
  the best Tucker core is $\mathcal{A} \times_1 U_1^T \cdots \times_d U_d^T$.
* §12.5.3, `GolubVanLoan.Chapter12.tucker_objective_unfoldings`: the forms of the Tucker objective,
  and the alternating update of one factor as problem (12.5.3).
* Equations (12.5.16)–(12.5.18), `GolubVanLoan.Chapter12.equation_12_5_16`: the modal unfoldings and
  the vectorization of a CP tensor, through Khatri–Rao products.
* Equations (12.5.19)–(12.5.20), `GolubVanLoan.Chapter12.equation_12_5_20`: the CP alternating least
  squares update is characterized by its normal equations.
* Equation (12.5.22), `GolubVanLoan.Chapter12.equation_12_5_22`: the singular values of a matrix
  are, up to sign, the stationary values of $u^T A v / (\|u\|_2 \|v\|_2)$.
* §12.5.6, `GolubVanLoan.Chapter12.tensor_singular_value`: the stationary points of the tensor
  Rayleigh quotient $\psi_{\mathcal{A}}$ are the singular vectors of the tensor.
* Equation (12.5.23), `GolubVanLoan.Chapter12.equation_12_5_23`: the stationary vectors of
  $x^T C x / x^T x$ for symmetric $C$ are eigenvectors.
* Equation (12.5.24), `GolubVanLoan.Chapter12.equation_12_5_24`: the modal unfoldings of a symmetric
  tensor agree, and the stationary points of $\phi_{\mathcal{C}}$ are the eigenvectors of the
  tensor.
* Equation (12.5.25), `GolubVanLoan.Chapter12.equation_12_5_25`: the tensor train of carriages is
  the matrix-product form $G_1(i_1) \cdots G_d(i_d)$.
* Equations (12.5.26)–(12.5.28), `GolubVanLoan.Chapter12.equation_12_5_28`: a factorization of an
  unfolding gives the next carriage of a tensor train.
* Equation (12.5.29), `GolubVanLoan.Chapter12.equation_12_5_29`: every tensor of order $d \ge 1$ is
  a tensor train whose ranks are the ranks of its sequential unfoldings.

## Conventions

* Tensors are `GolubVanLoan.Chapter12.RTensor n` of §12.4, and the mode-$k$ unfolding
  $\mathcal{A}_{(k)}$ is the flattened `GolubVanLoan.Chapter12.modalUnfolding`, with columns in the
  vec order. Some statements use the typed unfolding `Tensor.modeUnfold`, whose columns are the
  tuples of the other indices; each says so.
* An SVD $U^T A V = \Sigma$ is the backbone's `Matrix.IsSVD A U σ V`: $U$ and $V$ are orthogonal,
  $\Sigma = \operatorname{diag}(\sigma)$ is `Matrix.rectDiagonal σ`, and $\sigma$ is nonincreasing
  and nonnegative. The source's $\sigma_i$ is `σ (i - 1)`, since the sequence `σ : ℕ → ℝ` is
  0-based.
  The statements take any SVDs of the unfoldings, as the source does.
* Over $\mathbb{R}$ the conjugate transposes of the backbone are transposes
  (`Matrix.conjTranspose_eq_transpose_of_trivial`).

## Implementation notes

* The "Repeat" iterations of the section (Tucker alternating least squares, CP alternating least
  squares, and the higher-order power methods) are not programmed. For each update, the statement
  says which problem the update solves.
* The TT-SVD procedure (12.5.29) is not programmed either, because its ranks depend on the data and
  so the shapes of its carriages depend on the run. `GolubVanLoan.Chapter12.equation_12_5_29` states
  what it computes. This departs from the library convention that an algorithm-shaped display gets a
  program.
* The truncation $\mathcal{A}^{(r)}$ of the HOSVD is the backbone's `Tensor.truncatedHOSVDOf` in the
  factors $U_k$, which keeps the leading $r_k$ columns of each $U_k$.

## Deviations from the source

* **Equation (12.5.4)** (typo). The third row-inner-product line is missing its equality sign.
  The full Gram identity states the inner products in all modes of tensors of arbitrary positive
  order. See `GolubVanLoan.Chapter12.gram_modeUnfold_of_isSVD`.
* **Equations (12.5.16)–(12.5.20)** (generalization). The CP unfolding identity uses arbitrary
  order, and the row normal equations are combined into a matrix equivalence. See
  `GolubVanLoan.Chapter12.equation_12_5_16` and `GolubVanLoan.Chapter12.equation_12_5_20`.
* **Equation (12.5.22)** (correction). The absolute value of a stationary quotient is a singular
  value. A sign change in one vector changes the quotient sign. See
  `GolubVanLoan.Chapter12.equation_12_5_22`.
* **Equations (12.5.25)–(12.5.29)** (reading). The contraction extends to arbitrary boundary
  ranks. The TT-SVD result gives existence with the sequential unfolding ranks. See
  `GolubVanLoan.Chapter12.equation_12_5_25` and `GolubVanLoan.Chapter12.equation_12_5_29`.
* **Equation (12.5.1)** (typo). The source writes $v_i T$ for $v_i^T$. See
  `GolubVanLoan.Chapter12.equation_12_5_1`.
* **Equation (12.5.3)** (typo). The source writes the maximum of $\|Q^T A\|_F$ as
  $\sigma_1^2 + \cdots + \sigma_r^2$; this is the maximum of $\|Q^T A\|_F^2$. See
  `GolubVanLoan.Chapter12.equation_12_5_3`.
* **Equation (12.5.5)** (correction). The source prints $\mathcal{A} \times_k U_k$, which does not
  produce the stated unfoldings; the statement uses $\mathcal{A} \times_k U_k^T$. See
  `GolubVanLoan.Chapter12.hosvd_modeProduct_slices`.
* **The displayed unfoldings before Theorem 12.5.1** (typo). Displays such as
  $\mathcal{B}^{(1)}_{(1)} = \Sigma_1 V_1^T (U_3 \otimes U_2)^T$ are misprints and are not
  reproduced. See `GolubVanLoan.Chapter12.hosvd_modeProduct_slices`.
* **The slice norms before Theorem 12.5.1** (generalization). The source states them for an order-3
  tensor; the statement holds in every mode of a tensor of any order. See
  `GolubVanLoan.Chapter12.hosvd_modeProduct_slices`.
* **Equation (12.5.11)** (correction). The source prints $\min_{1 \le k \le d}$ in place of
  $\sum_{k=1}^{d}$, and the printed bound is false. See `GolubVanLoan.Chapter12.equation_12_5_11`.
* **The Tucker problem of §12.5.3** (generalization). The source writes it for order 3; the
  statements hold for every order. See `GolubVanLoan.Chapter12.tucker_best_core` and
  `GolubVanLoan.Chapter12.tucker_objective_unfoldings`.
* **The gradient display before (12.5.24)** (typo). The gradient of $\phi_{\mathcal{C}}$ omits the
  factor $d$, which does not change where it vanishes. See
  `GolubVanLoan.Chapter12.equation_12_5_24`.

## Not formalized

* **The "Repeat" iterations** of Tucker and CP alternating least squares and of the higher-order
  power methods, as programs. What each update solves is formalized.
* **The TT-SVD procedure (12.5.29) as a program.** Its ranks depend on the data, so the shapes of
  its carriages depend on the run.
* **The claim that the truncated HOSVD does not solve the Tucker problem.** The source gives no
  example.
* **Complications 1–6 of §12.5.5** on tensor rank: NP-hardness, maximal and typical ranks, real
  versus complex rank, and degeneracy.
* **The counts for tensor trains.**
-/

open Matrix

namespace GolubVanLoan.Chapter12

/-! ### The SVD viewpoint (12.5.1)–(12.5.3) -/

section SVD

variable {m n : ℕ}

/-- A real rectangular diagonal matrix whose entries are cast from $\mathbb{R}$ to $\mathbb{R}$ is
the rectangular diagonal matrix of the same values. -/
private theorem rectDiagonal_ofReal (σ : ℕ → ℝ) :
    (rectDiagonal fun i => ((σ i : ℝ) : ℝ) : Matrix (Fin m) (Fin n) ℝ) = rectDiagonal σ :=
  rfl

/-- Let $A \in \mathbb{R}^{m \times n}$ have an SVD $U^T A V = \Sigma$ (`Matrix.IsSVD A U σ V`, with
$\Sigma$ = `Matrix.rectDiagonal σ`). Then the factors are orthogonal, $U U^T = U^T U = I$ and
$V V^T = V^T V = I$, and $A = U \Sigma V^T$ and $U^T A = \Sigma V^T$. -/
theorem isSVD_real_facts {A : Matrix (Fin m) (Fin n) ℝ} {U : Matrix (Fin m) (Fin m) ℝ} {σ : ℕ → ℝ}
    {V : Matrix (Fin n) (Fin n) ℝ} (h : IsSVD A U σ V) :
    U * Uᵀ = 1 ∧ Uᵀ * U = 1 ∧ V * Vᵀ = 1 ∧ Vᵀ * V = 1 ∧
      A = U * (rectDiagonal σ : Matrix (Fin m) (Fin n) ℝ) * Vᵀ ∧
      Uᵀ * A = (rectDiagonal σ : Matrix (Fin m) (Fin n) ℝ) * Vᵀ := by
  have hU := h.mem_unitaryGroup_left
  have hV := h.mem_unitaryGroup_right
  have h1 : U * Uᵀ = 1 := (mem_orthogonalGroup_iff _ _).1 hU
  have h2 : Uᵀ * U = 1 := (mem_orthogonalGroup_iff' _ _).1 hU
  have h3 : V * Vᵀ = 1 := (mem_orthogonalGroup_iff _ _).1 hV
  have h4 : Vᵀ * V = 1 := (mem_orthogonalGroup_iff' _ _).1 hV
  have hA : A = U * (rectDiagonal σ : Matrix (Fin m) (Fin n) ℝ) * Vᵀ := by
    have := h.eq_mul_mul_star
    rwa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial, rectDiagonal_ofReal]
      at this
  refine ⟨h1, h2, h3, h4, hA, ?_⟩
  rw [hA, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.one_mul]

/-- For $\Sigma = \operatorname{diag}(\sigma_0, \sigma_1, \dots) \in \mathbb{R}^{m \times n}$ with
0-based indices, the diagonal entry $(\Sigma \Sigma^T)_{ii}$ is $\sigma_i^2$ for $i < n$ and $0$
for $i \ge n$. -/
theorem rectDiagonal_mul_transpose_apply (σ : ℕ → ℝ) (i : Fin m) :
    ((rectDiagonal σ : Matrix (Fin m) (Fin n) ℝ) * (rectDiagonal σ)ᵀ : Matrix (Fin m) (Fin m) ℝ)
      i i =
      if (i : ℕ) < n then σ i ^ 2 else 0 := by
  rw [Matrix.mul_apply]
  split_ifs with hi
  · rw [Finset.sum_eq_single ⟨i, hi⟩]
    · simp [rectDiagonal_apply, sq]
    · intro j _ hj
      have : (i : ℕ) ≠ j := fun h => hj (Fin.ext h.symm)
      simp [rectDiagonal_apply, this]
    · simp
  · refine Finset.sum_eq_zero fun j _ => ?_
    have : (i : ℕ) ≠ j := fun h => hi (h ▸ j.isLt)
    simp [rectDiagonal_apply, this]

/-- **Equations (12.5.1)–(12.5.2)** of [golub2013matrix]. Let $A \in \mathbb{R}^{m \times n}$ have
the SVD $A = U \Sigma V^T$, with $U \in \mathbb{R}^{m \times m}$ and
$V \in \mathbb{R}^{n \times n}$ orthogonal and $\Sigma = \operatorname{diag}(\sigma_1, \sigma_2,
\dots) \in \mathbb{R}^{m \times n}$ with $\sigma_1 \ge \sigma_2 \ge \cdots \ge 0$. Then
$$U^T A = \Sigma V^T,$$
so that the $i$-th row of $U^T A$ is $\sigma_i v_i^T$ for $i \le \min(m, n)$ and zero beyond.
These rows are mutually orthogonal,
$$(U^T A)(U^T A)^T = \Sigma \Sigma^T,$$
and their norms are nonincreasing: $\|(U^T A)(i, :)\|_2 \ge \|(U^T A)(i + 1, :)\|_2$ for every
$i$.

**Typo.** The source writes $v_i T$ in (12.5.1) for $v_i^T$.

The SVD is `Matrix.IsSVD A U σ V` with the 0-based sequence `σ`, and $\Sigma$ is
`Matrix.rectDiagonal σ`. The statement also records $A = U \Sigma V^T$. The monotonicity is
stated as `Antitone` for the squared row norms $\sum_j (U^T A)_{ij}^2$. -/
theorem equation_12_5_1 {A : Matrix (Fin m) (Fin n) ℝ} {U : Matrix (Fin m) (Fin m) ℝ} {σ : ℕ → ℝ}
    {V : Matrix (Fin n) (Fin n) ℝ} (h : IsSVD A U σ V) :
    A = U * (rectDiagonal σ : Matrix (Fin m) (Fin n) ℝ) * Vᵀ ∧
      Uᵀ * A = (rectDiagonal σ : Matrix (Fin m) (Fin n) ℝ) * Vᵀ ∧
      (Uᵀ * A) * (Uᵀ * A)ᵀ = (rectDiagonal σ : Matrix (Fin m) (Fin n) ℝ) * (rectDiagonal σ)ᵀ ∧
      Antitone fun i : Fin m => ∑ j, (Uᵀ * A) i j ^ 2 := by
  obtain ⟨-, -, -, h4, hA, hUA⟩ := (isSVD_real_facts h)
  have hG : (Uᵀ * A) * (Uᵀ * A)ᵀ =
      (rectDiagonal σ : Matrix (Fin m) (Fin n) ℝ) * (rectDiagonal σ)ᵀ := by
    rw [hUA, transpose_mul, transpose_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc Vᵀ, h4,
      Matrix.one_mul]
  refine ⟨hA, hUA, hG, ?_⟩
  have hrow : ∀ i, ∑ j, (Uᵀ * A) i j ^ 2 = if (i : ℕ) < n then σ i ^ 2 else 0 := by
    intro i
    rw [← rectDiagonal_mul_transpose_apply, ← hG, Matrix.mul_apply]
    simp only [transpose_apply, sq]
  intro i i' hii'
  simp only [hrow]
  split_ifs with h1 h2 h2
  · exact pow_le_pow_left₀ (h.nonneg _) (h.antitone (Fin.le_iff_val_le_val.1 hii')) 2
  · exact absurd (lt_of_le_of_lt (Fin.le_iff_val_le_val.1 hii') h1) h2
  · exact sq_nonneg _
  · exact le_rfl

open scoped Matrix.Norms.Frobenius in
/-- **Equation (12.5.3)** of [golub2013matrix], with the sentence after it. Let
$A \in \mathbb{R}^{m \times n}$ have an SVD $U^T A V = \Sigma$ with singular values
$\sigma_1 \ge \sigma_2 \ge \cdots$, and let $r \le \min(m, n)$. Then
$$\max_{Q \in \mathbb{R}^{m \times r}, \ Q^T Q = I_r} \|Q^T A\|_F^2 = \sigma_1^2 + \cdots +
  \sigma_r^2,$$
"and it can be attained by setting $Q = U(:, 1{:}r)$".

**Typo.** The source writes the maximum of $\|Q^T A\|_F$, not of its square, as
$\sigma_1^2 + \cdots + \sigma_r^2$.

The maximum is stated as `IsGreatest` of the set of values, and the norm is the Frobenius norm
of `Matrix.Norms.Frobenius`. The matrix $U(:, 1{:}r)$ is `U.submatrix id (Fin.castLE hrm)`. The
proof specializes Ky Fan's maximum principle,
`Matrix.isGreatest_frobenius_norm_sq_conjTranspose_mul`, and identifies the diagonal of the SVD
with the singular values. -/
theorem equation_12_5_3 {A : Matrix (Fin m) (Fin n) ℝ} {U : Matrix (Fin m) (Fin m) ℝ} {σ : ℕ → ℝ}
    {V : Matrix (Fin n) (Fin n) ℝ} (h : IsSVD A U σ V) {r : ℕ} (hrm : r ≤ m) (hrn : r ≤ n) :
    IsGreatest ((fun Q : Matrix (Fin m) (Fin r) ℝ => ‖Qᵀ * A‖ ^ 2) '' {Q | Qᵀ * Q = 1})
        (∑ i ∈ Finset.range r, σ i ^ 2) ∧
      ‖(U.submatrix id (Fin.castLE hrm))ᵀ * A‖ ^ 2 = ∑ i ∈ Finset.range r, σ i ^ 2 := by
  have hσ : ∑ i ∈ Finset.range r, σ i ^ 2 =
      ∑ i ∈ Finset.range r, A.sortedSingularValues i ^ 2 :=
    Finset.sum_congr rfl fun i hi => by
      have := Finset.mem_range.1 hi
      rw [h.singularValues_eq (by omega) (by omega)]
  have hK := isGreatest_frobenius_norm_sq_conjTranspose_mul A (r := r) (by simpa using hrm)
  simp only [conjTranspose_eq_transpose_of_trivial] at hK
  refine ⟨hσ ▸ hK, ?_⟩
  obtain ⟨-, -, -, -, -, hUA⟩ := isSVD_real_facts h
  have hQA : (U.submatrix id (Fin.castLE hrm))ᵀ * A =
      (1 : Matrix (Fin r) (Fin r) ℝ) *
        ((rectDiagonal σ : Matrix (Fin m) (Fin n) ℝ).submatrix (Fin.castLE hrm) id) * Vᵀ := by
    have hsub : (U.submatrix id (Fin.castLE hrm))ᵀ * A = (Uᵀ * A).submatrix (Fin.castLE hrm) id :=
      by ext a b; simp [Matrix.mul_apply]
    rw [hsub, hUA, Matrix.one_mul]
    ext a b
    simp [Matrix.mul_apply]
  have hVT : Vᵀ ∈ unitaryGroup (Fin n) ℝ := by
    have := Unitary.star_mem h.mem_unitaryGroup_right
    rwa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at this
  rw [hQA, frobenius_norm_unitary_mul_mul_unitary (one_mem _) _ hVT, frobenius_norm_sq_eq_sum_sq,
    ← Fin.sum_univ_eq_sum_range (fun i => σ i ^ 2) r]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single ⟨a, lt_of_lt_of_le a.isLt hrn⟩]
  · simp [rectDiagonal_apply]
  · intro b _ hb
    have : (a : ℕ) ≠ b := fun h => hb (Fin.ext h.symm)
    simp [rectDiagonal_apply, this]
  · simp

end SVD

/-! ### The higher-order SVD (Theorem 12.5.1, (12.5.4)–(12.5.11)) -/

section HOSVD

variable {d : ℕ}

variable {n : Fin (d + 1) → ℕ}

/-- Let $\mathcal{A}$ be a tensor and let $U_k$ be the left factor of an SVD
$\mathcal{A}_{(k)} = U_k \Sigma_k V_k^T$ of the flattened mode-$k$ unfolding. Then the rows of
$U_k^T \mathcal{A}_{(k)}$, with the typed unfolding $\mathcal{A}_{(k)}$, are orthogonal:
$$U_k^T \mathcal{A}_{(k)} \bigl(U_k^T \mathcal{A}_{(k)}\bigr)^T =
  \operatorname{diag}(\sigma_0^2, \sigma_1^2, \dots),$$
where, with 0-based indices, the $i$-th diagonal entry is $0$ when $i$ is at least the number
$\prod_{j \neq k} n_j$ of columns of the unfolding.

**Generalization.** The Gram identity holds in every mode of a tensor of arbitrary positive
order. The third equality in (12.5.4) is missing its equality sign in print. -/
theorem gram_modeUnfold_of_isSVD {A : RTensor n} {k : Fin (d + 1)}
    {U : Matrix (Fin (n k)) (Fin (n k)) ℝ} {σ : ℕ → ℝ}
    {V : Matrix (Fin (∏ j : Fin d, n (k.succAbove j))) (Fin (∏ j : Fin d, n (k.succAbove j))) ℝ}
    (h : IsSVD (modalUnfolding A k) U σ V) :
    Uᵀ * A.modeUnfold k * (Uᵀ * A.modeUnfold k)ᵀ =
      diagonal fun i : Fin (n k) =>
        if (i : ℕ) < ∏ j : Fin d, n (k.succAbove j) then σ i ^ 2 else 0 := by
  have hG : modalUnfolding A k * (modalUnfolding A k)ᵀ = A.modeUnfold k * (A.modeUnfold k)ᵀ := by
    rw [modalUnfolding, reindex_apply, transpose_submatrix, submatrix_mul_equiv]
    simp
  have e : ∀ {β : Type} [Fintype β] (X : Matrix (Fin (n k)) β ℝ),
      Uᵀ * X * (Uᵀ * X)ᵀ = Uᵀ * (X * Xᵀ) * U := fun X => by
    rw [transpose_mul, transpose_transpose]
    simp only [Matrix.mul_assoc]
  rw [e, ← hG, ← e, (equation_12_5_1 h).2.2.1, rectDiagonal_transpose,
    rectDiagonal_mul_rectDiagonal, rectDiagonal_eq_diagonal]
  simp only [sq]

/-- **Section 12.5.1** of [golub2013matrix], before Theorem 12.5.1, with (12.5.5). Let $\mathcal{A}
\in \mathbb{R}^{n_1 \times \cdots \times n_d}$ with $d \ge 1$, let $k$ be a mode, let
$\mathcal{A}_{(k)} = U_k \Sigma_k V_k^T$ be an SVD of the mode-$k$ unfolding with singular
values $\sigma_1 \ge \sigma_2 \ge \cdots$, and let
$\mathcal{B}^{(k)} = \mathcal{A} \times_k U_k^T$. Then the rows of $\mathcal{B}^{(k)}_{(k)}$ are
mutually orthogonal, and the $i$-th row has norm $\sigma_i(\mathcal{A}_{(k)})$:
$$\mathcal{B}^{(k)}_{(k)} \bigl(\mathcal{B}^{(k)}_{(k)}\bigr)^T = \Sigma_k \Sigma_k^T, \qquad
  \bigl\|\mathcal{B}^{(k)}_{(k)}(i, :)\bigr\|_2^2 = \sigma_i^2,$$
where the right side is $0$ for $i > \prod_{j \neq k} n_j$. For $k = 1$ and order 3, the second
identity is the source's $\|\mathcal{B}^{(1)}(i, :, :)\|_F = \sigma_i(\mathcal{A}_{(1)})$.

**Correction.** The source's (12.5.5) prints $\mathcal{B}^{(k)} = \mathcal{A} \times_k U_k$,
which does not produce the stated unfoldings. The statement uses $\mathcal{A} \times_k U_k^T$.

**Typo.** The displayed unfoldings of the source, such as $\mathcal{B}^{(1)}_{(1)} = \Sigma_1
V_1^T (U_3 \otimes U_2)^T$, are misprints and are not reproduced.

**Generalization.** The source writes the slice norms of an order-3 tensor. The statement holds
in every mode of a tensor of any order.

The Lean tensor has order `d + 1`, the SVD is of the flattened
`GolubVanLoan.Chapter12.modalUnfolding A k`, and the mode product is the shape-preserving
`Tensor.modeProd`. The rows are those of the typed unfolding `Tensor.modeUnfold`, and
$\Sigma_k \Sigma_k^T$ is written as the diagonal matrix of the values $\sigma_i^2$, with 0-based
indices. The proof specializes the backbone's `Tensor.modeProd_conjTranspose_row`. -/
theorem hosvd_modeProduct_slices (A : RTensor n) (k : Fin (d + 1))
    {U : Matrix (Fin (n k)) (Fin (n k)) ℝ} {σ : ℕ → ℝ}
    {V : Matrix (Fin (∏ j : Fin d, n (k.succAbove j))) (Fin (∏ j : Fin d, n (k.succAbove j))) ℝ}
    (h : IsSVD (modalUnfolding A k) U σ V) :
    (A.modeProd k Uᵀ).modeUnfold k * ((A.modeProd k Uᵀ).modeUnfold k)ᵀ =
        diagonal (fun i : Fin (n k) =>
          if (i : ℕ) < ∏ j : Fin d, n (k.succAbove j) then σ i ^ 2 else 0) ∧
      ∀ i, ∑ c, (A.modeProd k Uᵀ).modeUnfold k i c ^ 2 =
        if (i : ℕ) < ∏ j : Fin d, n (k.succAbove j) then σ i ^ 2 else 0 := by
  have hrow := Tensor.modeProd_conjTranspose_row A k U
  simp only [conjTranspose_eq_transpose_of_trivial] at hrow
  rw [gram_modeUnfold_of_isSVD h] at hrow
  refine ⟨hrow, fun i => ?_⟩
  have := congrFun (congrFun hrow i) i
  rw [Matrix.mul_apply, diagonal_apply_eq] at this
  simpa [sq] using this

/-- **Theorem 12.5.1** of [golub2013matrix] (higher-order SVD), with (12.5.6)–(12.5.9). Let
$\mathcal{A} \in \mathbb{R}^{n_1 \times \cdots \times n_d}$ with $d \ge 1$, for every mode $k$
let $\mathcal{A}_{(k)} = U_k \Sigma_k V_k^T$ be an SVD of the mode-$k$ unfolding, and let
$\mathcal{S} = \mathcal{A} \times_1 U_1^T \cdots \times_d U_d^T$. Then
$$\mathcal{A} = \mathcal{S} \times_1 U_1 \cdots \times_d U_d,$$
or equivalently
$$\mathcal{A} = \sum_{j} \mathcal{S}(j) \, U_1(:, j_1) \circ \cdots \circ U_d(:, j_d), \qquad
  \mathcal{A}(i) = \sum_{j} \mathcal{S}(j) \, U_1(i_1, j_1) \cdots U_d(i_d, j_d),$$
with the sums over all index tuples $j$, and
$$\operatorname{vec}(\mathcal{A}) = (U_d \otimes \cdots \otimes U_1)
  \operatorname{vec}(\mathcal{S}).$$

The Lean tensor has order `d + 1`. The multilinear product is `Tensor.multilinearProd`, and the
Kronecker product is the family product `Matrix.piKronecker U` flattened by `finPiFinEquiv`,
which is the product in the reversed order of the source by
`Matrix.piKronecker_reindex_finPiFinEquiv`. The proof uses only the orthogonality of the $U_k$;
the SVDs matter for (12.5.10), `GolubVanLoan.Chapter12.theorem_12_5_1_b`. -/
theorem theorem_12_5_1 (A : RTensor n) (U : ∀ k, Matrix (Fin (n k)) (Fin (n k)) ℝ)
    (σ : Fin (d + 1) → ℕ → ℝ) (V : ∀ k, Matrix (Fin (∏ j : Fin d, n (k.succAbove j)))
      (Fin (∏ j : Fin d, n (k.succAbove j))) ℝ)
    (h : ∀ k, IsSVD (modalUnfolding A k) (U k) (σ k) (V k)) :
    let S : RTensor n := Tensor.multilinearProd (fun k => (U k)ᵀ) A
    A = Tensor.multilinearProd U S ∧
      A = ∑ j, S j • Tensor.rankOne (κ := fun k => Fin (n k)) (fun k x => U k x (j k)) ∧
      (∀ i, A i = ∑ j, S j * ∏ k, U k (i k) (j k)) ∧
      Tensor.vecFin A = (piKronecker U).reindex finPiFinEquiv finPiFinEquiv *ᵥ Tensor.vecFin S := by
  intro S
  have hUU : ∀ k, U k * (U k)ᵀ = 1 := fun k => (isSVD_real_facts (h k)).1
  have hA : A = Tensor.multilinearProd U S := by
    simp only [S, Tensor.multilinearProd_multilinearProd, hUU, Tensor.multilinearProd_one]
  refine ⟨hA, ?_, fun i => ?_, ?_⟩
  · conv_lhs => rw [hA]
    exact Tensor.multilinearProd_eq_sum_rankOne _ _
  · conv_lhs => rw [hA]
    rw [Tensor.multilinearProd_apply]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  · conv_lhs => rw [hA]
    exact Tensor.vecFin_multilinearProd U S

/-- If $U_j U_j^T = I$ for every $j$, then the flattened Kronecker product $K$ of the transposes
$U_j^T$ satisfies $K^T K = I$. -/
private theorem transpose_mul_reindex_piKronecker {n : Fin d → ℕ}
    (U : ∀ j, Matrix (Fin (n j)) (Fin (n j)) ℝ) (hU : ∀ j, U j * (U j)ᵀ = 1) :
    ((piKronecker fun j => (U j)ᵀ).reindex finPiFinEquiv finPiFinEquiv)ᵀ *
      (piKronecker fun j => (U j)ᵀ).reindex finPiFinEquiv finPiFinEquiv = 1 := by
  rw [reindex_apply, transpose_submatrix, submatrix_mul_equiv, transpose_piKronecker,
    piKronecker_mul_piKronecker]
  simp only [transpose_transpose, hU, piKronecker_one, submatrix_one_equiv]

/-- **Theorem 12.5.1** of [golub2013matrix], equation (12.5.10). Let $\mathcal{A} \in
\mathbb{R}^{n_1 \times \cdots \times n_d}$ with $d \ge 1$, for every mode $k$ let
$\mathcal{A}_{(k)} = U_k \Sigma_k V_k^T$ be an SVD of the mode-$k$ unfolding with singular
values $\sigma_{k,1} \ge \sigma_{k,2} \ge \cdots$, and let $\mathcal{S} = \mathcal{A} \times_1
U_1^T \cdots \times_d U_d^T$. Then for every mode $k$ the rows of $\mathcal{S}_{(k)}$ are
mutually orthogonal and the $i$-th row has norm $\sigma_{k,i}$:
$$\mathcal{S}_{(k)} \mathcal{S}_{(k)}^T = \Sigma_k \Sigma_k^T,$$
where $\sigma_{k,i}$ is read as $0$ for $i > \prod_{j \neq k} n_j$. Moreover,
$\sigma_{k,i} = \sigma_i(\mathcal{A}_{(k)})$ is the $i$-th largest singular value of
$\mathcal{A}_{(k)}$ for $i \le \min(n_k, \prod_{j \neq k} n_j)$.

The proof follows the source: by Theorem 12.4.1, $\mathcal{S}_{(k)} = U_k^T \mathcal{A}_{(k)}
(U_d^T \otimes \cdots \otimes U_{k+1}^T \otimes U_{k-1}^T \otimes \cdots \otimes U_1^T)^T =
\Sigma_k V_k^T (U_d^T \otimes \cdots \otimes U_1^T)^T$, with the factor $U_k^T$ left out of the
Kronecker product, and this Kronecker product is orthogonal. The Lean tensor has order `d + 1`,
the unfoldings are the flattened `GolubVanLoan.Chapter12.modalUnfolding`, and $\Sigma_k$ is
`Matrix.rectDiagonal (σ k)`. The sorted singular values are `Matrix.sortedSingularValues`,
identified with the diagonal of the SVD by `Matrix.IsSVD.singularValues_eq`. It follows that the
rows of $\mathcal{S}_{(k)}$ beyond $\operatorname{rank}(\mathcal{A}_{(k)})$ vanish, so the sums
of the HOSVD may stop at $\operatorname{rank}_*(\mathcal{A})$, as §12.5.2 of the source says.

**Generalization.** The Gram matrix gives the row norms, including zero singular values within
the rectangular size. -/
theorem theorem_12_5_1_b (A : RTensor n) (U : ∀ k, Matrix (Fin (n k)) (Fin (n k)) ℝ)
    (σ : Fin (d + 1) → ℕ → ℝ) (V : ∀ k, Matrix (Fin (∏ j : Fin d, n (k.succAbove j)))
      (Fin (∏ j : Fin d, n (k.succAbove j))) ℝ)
    (h : ∀ k, IsSVD (modalUnfolding A k) (U k) (σ k) (V k)) (k : Fin (d + 1)) :
    let S : RTensor n := Tensor.multilinearProd (fun k => (U k)ᵀ) A
    modalUnfolding S k * (modalUnfolding S k)ᵀ =
        (rectDiagonal (σ k) : Matrix (Fin (n k)) (Fin (∏ j : Fin d, n (k.succAbove j))) ℝ) *
          (rectDiagonal (σ k))ᵀ ∧
      ∀ i : ℕ, i < n k → i < ∏ j : Fin d, n (k.succAbove j) →
        σ k i = (modalUnfolding A k).sortedSingularValues i := by
  intro S
  refine ⟨?_, fun i hi hi' => (h k).singularValues_eq hi hi'⟩
  have hS : modalUnfolding S k = (U k)ᵀ * modalUnfolding A k *
      ((piKronecker fun j : Fin d => (U (k.succAbove j))ᵀ).reindex finPiFinEquiv
        finPiFinEquiv)ᵀ :=
    theorem_12_4_1 (fun k => (U k)ᵀ) A k
  have hK := transpose_mul_reindex_piKronecker (fun j : Fin d => U (k.succAbove j))
    fun j => (isSVD_real_facts (h _)).1
  calc modalUnfolding S k * (modalUnfolding S k)ᵀ
      = ((U k)ᵀ * modalUnfolding A k) *
          (((piKronecker fun j : Fin d => (U (k.succAbove j))ᵀ).reindex finPiFinEquiv
            finPiFinEquiv)ᵀ *
          (piKronecker fun j : Fin d => (U (k.succAbove j))ᵀ).reindex finPiFinEquiv
            finPiFinEquiv) * ((U k)ᵀ * modalUnfolding A k)ᵀ := by
        rw [hS, transpose_mul, transpose_transpose]
        simp only [Matrix.mul_assoc]
    _ = ((U k)ᵀ * modalUnfolding A k) * ((U k)ᵀ * modalUnfolding A k)ᵀ := by
        rw [hK, Matrix.mul_one]
    _ = rectDiagonal (σ k) * (rectDiagonal (σ k))ᵀ := (equation_12_5_1 (h k)).2.2.1

/-- **Equation (12.5.11)** of [golub2013matrix], for the HOSVD of Theorem 12.5.1. Let $\mathcal{A}
\in \mathbb{R}^{n_1 \times \cdots \times n_d}$ with $d \ge 1$, for every mode $k$ let
$\mathcal{A}_{(k)} = U_k \Sigma_k V_k^T$ be an SVD of the mode-$k$ unfolding, let $\mathcal{S} =
\mathcal{A} \times_1 U_1^T \cdots \times_d U_d^T$, and let $r = (r_1, \dots, r_d)$ be natural
numbers. The truncation of §12.5.2,
$$\mathcal{A}^{(r)} = \sum_{j \le r} \mathcal{S}(j) \, U_1(:, j_1) \circ \cdots \circ U_d(:,
  j_d),$$
the sum over the index tuples $j$ with $j_k \le r_k$ for every $k$, satisfies
$$\|\mathcal{A} - \mathcal{A}^{(r)}\|_F^2 \le \sum_{k=1}^{d} \sum_{i > r_k}
  \sigma_i(\mathcal{A}_{(k)})^2,$$
where the inner sum runs over $r_k < i \le \min(n_k, \prod_{j \neq k} n_j)$.

**Correction.** The source prints $\min_{1 \le k \le d}$ in place of $\sum_{k=1}^{d}$. This is
false: every tensor of multilinear rank at most $r$ is at squared distance at least $\max_k
\sum_{i > r_k} \sigma_i(\mathcal{A}_{(k)})^2$ from $\mathcal{A}$
(`Tensor.sum_sq_le_norm_sub_sq_of_multilinearRank_le`), so the printed bound fails whenever one
tail vanishes and another does not.

The truncation is the backbone's `Tensor.truncatedHOSVDOf U A s`, which projects mode $k$ onto
the columns of $U_k$ in the set $s_k$ of 0-based indices below $r_k$; the first part of the
statement identifies it with the sum above. If $r_k \ge n_k$, mode $k$ is not truncated. With
0-based indices the inner sum runs over $r_k \le i < \min(n_k, \prod_{j \neq k} n_j)$. Any SVDs
serve, also with repeated singular values (`Tensor.norm_sub_truncatedHOSVDOf_sq_le`). -/
theorem equation_12_5_11 (A : RTensor n) (U : ∀ k, Matrix (Fin (n k)) (Fin (n k)) ℝ)
    (σ : Fin (d + 1) → ℕ → ℝ) (V : ∀ k, Matrix (Fin (∏ j : Fin d, n (k.succAbove j)))
      (Fin (∏ j : Fin d, n (k.succAbove j))) ℝ)
    (h : ∀ k, IsSVD (modalUnfolding A k) (U k) (σ k) (V k)) (r : Fin (d + 1) → ℕ) :
    let S : RTensor n := Tensor.multilinearProd (fun k => (U k)ᵀ) A
    let s : ∀ k, Finset (Fin (n k)) := fun k => Finset.univ.filter fun i => (i : ℕ) < r k
    Tensor.truncatedHOSVDOf U A s = ∑ j ∈ Fintype.piFinset s,
        S j • Tensor.rankOne (κ := fun k => Fin (n k)) (fun k x => U k x (j k)) ∧
      ‖A - Tensor.truncatedHOSVDOf U A s‖ ^ 2 ≤
        ∑ k, ∑ i ∈ Finset.Ico (r k) (min (n k) (∏ j : Fin d, n (k.succAbove j))), σ k i ^ 2 := by
  intro S s
  have hU : ∀ k, U k ∈ unitaryGroup (Fin (n k)) ℝ := fun k => (h k).mem_unitaryGroup_left
  refine ⟨?_, ?_⟩
  · rw [Tensor.truncatedHOSVDOf_eq_sum]
    simp only [Tensor.hosvdCoreOf, conjTranspose_eq_transpose_of_trivial, S]
  set N : Fin (d + 1) → ℕ := fun k => ∏ j : Fin d, n (k.succAbove j) with hN
  have hσ : ∀ k, (U k)ᴴ * A.modeUnfold k * (A.modeUnfold k)ᴴ * U k =
      diagonal fun i : Fin (n k) => (((if (i : ℕ) < N k then σ k i else 0) ^ 2 : ℝ) : ℝ) :=
        fun k => by
    have e : (U k)ᵀ * A.modeUnfold k * (A.modeUnfold k)ᵀ * U k =
        (U k)ᵀ * A.modeUnfold k * ((U k)ᵀ * A.modeUnfold k)ᵀ := by
      rw [transpose_mul, transpose_transpose]
      simp only [Matrix.mul_assoc]
    simp only [conjTranspose_eq_transpose_of_trivial]
    rw [e, gram_modeUnfold_of_isSVD (h k)]
    congr 1
    funext i
    split_ifs <;> simp
  refine (Tensor.norm_sub_truncatedHOSVDOf_sq_le A hU hσ s).trans
    (le_of_eq (Finset.sum_congr rfl fun k _ => ?_))
  calc ∑ i ∈ (s k)ᶜ, (if (i : ℕ) < N k then σ k i else 0) ^ 2
      = ∑ i : Fin (n k), if r k ≤ (i : ℕ) ∧ (i : ℕ) < N k then σ k i ^ 2 else 0 := by
        rw [Finset.compl_filter, Finset.sum_filter]
        refine Finset.sum_congr rfl fun i _ => ?_
        by_cases h1 : r k ≤ (i : ℕ) <;> by_cases h2 : (i : ℕ) < N k <;> simp [h1, h2]
    _ = ∑ i ∈ Finset.range (n k), if r k ≤ i ∧ i < N k then σ k i ^ 2 else 0 :=
        Fin.sum_univ_eq_sum_range (fun i => if r k ≤ i ∧ i < N k then σ k i ^ 2 else 0) (n k)
    _ = _ := by
        rw [← Finset.sum_filter]
        congr 1
        ext i
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, hN]
        omega

end HOSVD

/-! ### The Tucker problem (§12.5.3) -/

section Tucker

variable {d : ℕ} {n r : Fin d → ℕ}

/-- The Euclidean norm of the vectorization of a tensor is its Frobenius norm:
$\|\operatorname{vec}(\mathcal{T})\|_2 = \|\mathcal{T}\|_F$. -/
theorem norm_toLp_vecFin (T : RTensor n) : ‖WithLp.toLp 2 (Tensor.vecFin T)‖ = ‖T‖ := by
  rw [EuclideanSpace.norm_eq, Tensor.frobenius_norm_def]
  congr 1
  rw [← finPiFinEquiv.sum_comp]
  simp [Tensor.vecFin_apply]

/-- **Section 12.5.3** of [golub2013matrix], the best core of the Tucker problem. Let $\mathcal{A}
\in \mathbb{R}^{n_1 \times \cdots \times n_d}$, and let $U_k \in \mathbb{R}^{n_k \times r_k}$
have orthonormal columns, $U_k^T U_k = I_{r_k}$, for $k = 1, \dots, d$. For a core $\mathcal{S}
\in \mathbb{R}^{r_1 \times \cdots \times r_d}$ let $\mathcal{X} = \mathcal{S} \times_1 U_1
\cdots \times_d U_d$, the form (12.5.13), and let $\mathcal{S}_* = \mathcal{A} \times_1 U_1^T
\cdots \times_d U_d^T$. Then for every core $\mathcal{S}$,
$$\|\mathcal{A} - \mathcal{X}\|_F = \|\operatorname{vec}(\mathcal{A}) - (U_d \otimes \cdots
  \otimes U_1) \operatorname{vec}(\mathcal{S})\|_2, \qquad \|\mathcal{A} - \mathcal{X}\|_F^2 =
  \|\mathcal{A}\|_F^2 - \|\mathcal{S}_*\|_F^2 + \|\mathcal{S} - \mathcal{S}_*\|_F^2.$$
So the core $\mathcal{S}_*$, for which $\operatorname{vec}(\mathcal{S}_*) = (U_d^T \otimes
\cdots \otimes U_1^T) \operatorname{vec}(\mathcal{A})$, minimizes
$\|\mathcal{A} - \mathcal{X}\|_F$, and the minimum satisfies
$$\|\mathcal{A} - \mathcal{S}_* \times_1 U_1 \cdots \times_d U_d\|_F^2 = \|\mathcal{A}\|_F^2 -
  \|\mathcal{S}_*\|_F^2,$$
which the source writes as $\|\operatorname{vec}(\mathcal{A})\|_2^2 - \|(U_d \otimes \cdots
\otimes U_1)^T \operatorname{vec}(\mathcal{A})\|_2^2$.

**Generalization.** The source writes the Tucker problem for order 3. The statement holds for
every order.

The multilinear product is `Tensor.multilinearProd`, the Kronecker product is the family product
`Matrix.piKronecker U` flattened by `finPiFinEquiv`, and the Euclidean norm is that of
`WithLp.toLp 2`. The minimization is `IsMinOn` over all cores. -/
theorem tucker_best_core (U : ∀ k, Matrix (Fin (n k)) (Fin (r k)) ℝ) (hU : ∀ k, (U k)ᵀ * U k = 1)
    (A : RTensor n) :
    (∀ S : RTensor r, ‖A - Tensor.multilinearProd U S‖ =
      ‖WithLp.toLp 2 (Tensor.vecFin A -
        (piKronecker U).reindex finPiFinEquiv finPiFinEquiv *ᵥ Tensor.vecFin S)‖) ∧
      (∀ S : RTensor r, ‖A - Tensor.multilinearProd U S‖ ^ 2 =
        ‖A‖ ^ 2 - ‖Tensor.multilinearProd (fun k => (U k)ᵀ) A‖ ^ 2 +
          ‖S - Tensor.multilinearProd (fun k => (U k)ᵀ) A‖ ^ 2) ∧
      IsMinOn (fun S : RTensor r => ‖A - Tensor.multilinearProd U S‖) Set.univ
        (Tensor.multilinearProd (fun k => (U k)ᵀ) A) ∧
      ‖A - Tensor.multilinearProd U (Tensor.multilinearProd (fun k => (U k)ᵀ) A)‖ ^ 2 =
        ‖A‖ ^ 2 - ‖Tensor.multilinearProd (fun k => (U k)ᵀ) A‖ ^ 2 := by
  have hU' : ∀ k, (U k)ᴴ * U k = 1 := fun k => by
    rw [conjTranspose_eq_transpose_of_trivial]; exact hU k
  have key : ∀ S : RTensor r, ‖A - Tensor.multilinearProd U S‖ ^ 2 =
      ‖A‖ ^ 2 - ‖Tensor.multilinearProd (fun k => (U k)ᵀ) A‖ ^ 2 +
        ‖S - Tensor.multilinearProd (fun k => (U k)ᵀ) A‖ ^ 2 := fun S => by
    simpa only [conjTranspose_eq_transpose_of_trivial] using
      Tensor.norm_sub_multilinearProd_sq hU' A S
  refine ⟨fun S => ?_, key, fun S _ => ?_, ?_⟩
  · rw [← norm_toLp_vecFin]
    congr 2
    rw [← Tensor.vecFin_multilinearProd]
    rfl
  · refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
    change ‖A - Tensor.multilinearProd U (Tensor.multilinearProd (fun k => (U k)ᵀ) A)‖ ^ 2 ≤
      ‖A - Tensor.multilinearProd U S‖ ^ 2
    rw [key, key, sub_self, norm_zero]
    nlinarith [sq_nonneg ‖S - Tensor.multilinearProd (fun k => (U k)ᵀ) A‖]
  · rw [key, sub_self, norm_zero]
    ring

end Tucker

section TuckerALS

variable {d : ℕ} {n r : Fin (d + 1) → ℕ}

open scoped Matrix.Norms.Frobenius in
/-- The Frobenius norm of a tensor is the Frobenius norm of each of its flattened modal unfoldings.
-/
private theorem norm_modalUnfolding (T : RTensor n) (k : Fin (d + 1)) :
    ‖modalUnfolding T k‖ = ‖T‖ := by
  rw [modalUnfolding, reindex_apply, frobenius_norm_submatrix_equiv,
    Tensor.frobenius_norm_modeUnfold]

open scoped Matrix.Norms.Frobenius in
/-- For every mode $k$, $\|\mathcal{A} \times_1 U_1^T \cdots \times_d U_d^T\|_F = \|U_k^T
\mathcal{A}_{(k)} (U_d \otimes \cdots \otimes U_{k+1} \otimes U_{k-1} \otimes \cdots \otimes
U_1)\|_F$.

**Reading.** Unfolded objective formula for arbitrary positive tensor order.
-/
private theorem norm_multilinearProd_transpose_eq_modalUnfolding
    (U : ∀ k, Matrix (Fin (n k)) (Fin (r k)) ℝ) (A : RTensor n) (k : Fin (d + 1)) :
    ‖Tensor.multilinearProd (fun k => (U k)ᵀ) A‖ =
      ‖(U k)ᵀ * modalUnfolding A k *
        (piKronecker fun j : Fin d => U (k.succAbove j)).reindex finPiFinEquiv finPiFinEquiv‖ := by
  rw [← norm_modalUnfolding _ k, theorem_12_4_1, transpose_reindex]
  rfl

open scoped Matrix.Norms.Frobenius in
/-- **Section 12.5.3** of [golub2013matrix], the Tucker objective and its alternating update. Let
$\mathcal{A} \in \mathbb{R}^{n_1 \times \cdots \times n_d}$ with $d \ge 1$, and let
$U_k \in \mathbb{R}^{n_k \times r_k}$ for $k = 1, \dots, d$. Then for every mode $k$,
$$\|(U_d^T \otimes \cdots \otimes U_1^T) \operatorname{vec}(\mathcal{A})\|_2 = \|\mathcal{A}
  \times_1 U_1^T \cdots \times_d U_d^T\|_F = \|U_k^T \mathcal{A}_{(k)} (U_d \otimes \cdots
  \otimes U_{k+1} \otimes U_{k-1} \otimes \cdots \otimes U_1)\|_F.$$
Now fix a mode $k$, freeze the other factors, and let $\mathcal{A}_{(k)} (U_d \otimes \cdots
\otimes U_{k+1} \otimes U_{k-1} \otimes \cdots \otimes U_1) = \tilde U_k \Sigma_k V_k^T$ be an
SVD. If $r_k \le n_k$ and $r_k \le \prod_{j \neq k} r_j$, then the squared objective, as a
function of a matrix $W \in \mathbb{R}^{n_k \times r_k}$ with $W^T W = I$ in place of $U_k$, has
its maximum at $W = \tilde U_k(:, 1{:}r_k)$. This is problem (12.5.3) for the matrix
$\mathcal{A}_{(k)} (U_d \otimes \cdots \otimes U_{k+1} \otimes U_{k-1} \otimes \cdots \otimes
U_1)$, and $\tilde U_k(:, 1{:}r_k)$ is the update of the "Repeat" loop. In particular, if the
old $U_k$ has orthonormal columns, the update does not decrease the objective.

**Generalization.** The source writes the Tucker problem for order 3. The statement holds for
every order.

The Lean tensor has order `d + 1`. The hypothesis $r_k \le \prod_{j \neq k} r_j$ is the
condition $r \le \min(m, n)$ of (12.5.3) for this matrix. The other factors need not have
orthonormal columns. The replacement of $U_k$ by $W$ is `Function.update U k W`, the unfoldings
are the flattened `GolubVanLoan.Chapter12.modalUnfolding`, and the Kronecker products are
flattened family products `Matrix.piKronecker`. -/
theorem tucker_objective_unfoldings (U : ∀ k, Matrix (Fin (n k)) (Fin (r k)) ℝ) (A : RTensor n) :
    ‖WithLp.toLp 2 ((piKronecker fun k => (U k)ᵀ).reindex finPiFinEquiv finPiFinEquiv *ᵥ
        Tensor.vecFin A)‖ = ‖Tensor.multilinearProd (fun k => (U k)ᵀ) A‖ ∧
    (∀ k, ‖Tensor.multilinearProd (fun k => (U k)ᵀ) A‖ =
      ‖(U k)ᵀ * modalUnfolding A k *
        (piKronecker fun j : Fin d => U (k.succAbove j)).reindex finPiFinEquiv finPiFinEquiv‖) ∧
    ∀ k {Ũ : Matrix (Fin (n k)) (Fin (n k)) ℝ} {σ : ℕ → ℝ}
      {V : Matrix (Fin (∏ j : Fin d, r (k.succAbove j))) (Fin (∏ j : Fin d, r (k.succAbove j)))
        ℝ},
      IsSVD (modalUnfolding A k *
        (piKronecker fun j : Fin d => U (k.succAbove j)).reindex finPiFinEquiv finPiFinEquiv)
        Ũ σ V →
      ∀ (hrm : r k ≤ n k), r k ≤ ∏ j : Fin d, r (k.succAbove j) →
      IsGreatest ((fun W => ‖Tensor.multilinearProd (fun j => (Function.update U k W j)ᵀ) A‖ ^ 2) ''
          {W | Wᵀ * W = 1})
        (‖Tensor.multilinearProd
          (fun j => (Function.update U k (Ũ.submatrix id (Fin.castLE hrm)) j)ᵀ) A‖ ^ 2) ∧
      ((U k)ᵀ * U k = 1 → ‖Tensor.multilinearProd (fun k => (U k)ᵀ) A‖ ≤
        ‖Tensor.multilinearProd
          (fun j => (Function.update U k (Ũ.submatrix id (Fin.castLE hrm)) j)ᵀ) A‖) := by
  refine ⟨?_, norm_multilinearProd_transpose_eq_modalUnfolding U A, ?_⟩
  · rw [← Tensor.vecFin_multilinearProd, norm_toLp_vecFin]
  intro k Ũ σ V h hrm hrn
  set P := (piKronecker fun j : Fin d => U (k.succAbove j)).reindex finPiFinEquiv finPiFinEquiv
  have hobj : ∀ W : Matrix (Fin (n k)) (Fin (r k)) ℝ,
      ‖Tensor.multilinearProd (fun j => (Function.update U k W j)ᵀ) A‖ ^ 2 =
        ‖Wᵀ * (modalUnfolding A k * P)‖ ^ 2 := fun W => by
    have hP : (piKronecker fun j : Fin d => Function.update U k W (k.succAbove j)) =
        piKronecker fun j : Fin d => U (k.succAbove j) := by
      congr 1
      funext j
      rw [Function.update_of_ne (Fin.succAbove_ne k j)]
    rw [norm_multilinearProd_transpose_eq_modalUnfolding _ A k, Function.update_self, hP,
      Matrix.mul_assoc]
  have himg : ((fun W => ‖Tensor.multilinearProd (fun j => (Function.update U k W j)ᵀ) A‖ ^ 2) ''
      {W | Wᵀ * W = 1}) =
        (fun Q : Matrix (Fin (n k)) (Fin (r k)) ℝ => ‖Qᵀ * (modalUnfolding A k * P)‖ ^ 2) ''
          {Q | Qᵀ * Q = 1} := by
    simp only [hobj]
  obtain ⟨hmax, hval⟩ := equation_12_5_3 h hrm hrn
  have hgreat : IsGreatest
      ((fun W => ‖Tensor.multilinearProd (fun j => (Function.update U k W j)ᵀ) A‖ ^ 2) ''
        {W | Wᵀ * W = 1})
      (‖Tensor.multilinearProd
        (fun j => (Function.update U k (Ũ.submatrix id (Fin.castLE hrm)) j)ᵀ) A‖ ^ 2) := by
    rw [himg, hobj, hval]
    exact hmax
  refine ⟨hgreat, fun hU => ?_⟩
  have hle := hgreat.2 ⟨U k, hU, rfl⟩
  simp only [Function.update_eq_self] at hle
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 hle

end TuckerALS

/-! ### The CP problem (12.5.14)–(12.5.21) -/

section CP

variable {d r : ℕ} {n : Fin (d + 1) → ℕ}

/-- **Equations (12.5.16)–(12.5.18)** of [golub2013matrix], with the displays before them. Let
$F^{(k)} \in \mathbb{R}^{n_k \times r}$ for $k = 1, \dots, d$ with $d \ge 1$, let
$\lambda \in \mathbb{R}^r$, and let
$$\mathcal{X} = \sum_{j=1}^{r} \lambda_j \, F^{(1)}(:, j) \circ \cdots \circ F^{(d)}(:, j).$$
Then for every mode $k$,
$$\mathcal{X}_{(k)} = F^{(k)} \operatorname{diag}(\lambda) \bigl(F^{(d)} \odot \cdots \odot
  F^{(k+1)} \odot F^{(k-1)} \odot \cdots \odot F^{(1)}\bigr)^T,$$
where $\odot$ is the Khatri–Rao product, and $\|\mathcal{A} - \mathcal{X}\|_F =
\|\mathcal{A}_{(k)} - \mathcal{X}_{(k)}\|_F$ for every tensor $\mathcal{A}$. Moreover,
$$\operatorname{vec}(\mathcal{X}) = (F^{(d)} \odot \cdots \odot F^{(1)}) \lambda,$$
which is Problem P12.5.6 of the source.

The Lean tensor has order `d + 1`, and the statement holds at every order. The tensor
$\mathcal{X}$ is `Tensor.cp c F`, where `c` is the vector $\lambda$. The Khatri–Rao product of a
family is `Matrix.piKhatriRao`, with its rows flattened by `finPiFinEquiv` in the reversed order
of the source. The unfoldings are the flattened `GolubVanLoan.Chapter12.modalUnfolding`.

**Generalization.** The CP unfolding and vectorization formulas hold for arbitrary positive
tensor order. -/
theorem equation_12_5_16 (c : Fin r → ℝ) (F : ∀ k, Matrix (Fin (n k)) (Fin r) ℝ)
    (k : Fin (d + 1)) :
    modalUnfolding (Tensor.cp c F : RTensor n) k =
        F k * diagonal c *
          ((piKhatriRao fun j : Fin d => F (k.succAbove j)).reindex finPiFinEquiv
            (Equiv.refl _))ᵀ ∧
      (∀ A : RTensor n, ‖A - Tensor.cp c F‖ =
        (open scoped Matrix.Norms.Frobenius in
          ‖modalUnfolding A k - modalUnfolding (Tensor.cp c F : RTensor n) k‖)) ∧
      Tensor.vecFin (Tensor.cp c F : RTensor n) =
        (piKhatriRao F).reindex finPiFinEquiv (Equiv.refl _) *ᵥ c := by
  have hP : (piKhatriRao fun j : {j // j ≠ k} => F j).reindex (modalColumnEquiv n k)
      (Equiv.refl _) =
        (piKhatriRao fun j : Fin d => F (k.succAbove j)).reindex finPiFinEquiv
          (Equiv.refl _) := by
    ext a t
    obtain ⟨a', rfl⟩ := (modalColumnEquiv n k).surjective a
    simp only [reindex_apply, submatrix_apply, Equiv.symm_apply_apply, piKhatriRao_apply,
      modalColumnEquiv_symm_apply, Equiv.refl_symm, Equiv.coe_refl, id]
    rw [← (finSuccAboveEquiv k).prod_comp]
    rfl
  refine ⟨?_, fun A => ?_, Tensor.vecFin_cp c F⟩
  · rw [modalUnfolding, Tensor.modeUnfold_cp, ← hP]
    simp only [reindex_apply, Equiv.refl_symm, Equiv.coe_refl, transpose_submatrix]
    rw [Matrix.submatrix_mul _ _ id id _ Function.bijective_id, submatrix_id_id]
  · open scoped Matrix.Norms.Frobenius in
    rw [show modalUnfolding A k - modalUnfolding (Tensor.cp c F : RTensor n) k =
        modalUnfolding (A - Tensor.cp c F) k from rfl, modalUnfolding, reindex_apply,
      frobenius_norm_submatrix_equiv,
      Tensor.frobenius_norm_modeUnfold]

end CP

section ALS

open scoped Matrix.Norms.Frobenius

/-- **Equations (12.5.19)–(12.5.20)** of [golub2013matrix], the update of CP alternating least
squares. Let $H \in \mathbb{R}^{p \times r}$, $G \in \mathbb{R}^{q \times r}$,
$A \in \mathbb{R}^{N \times pq}$ (the unfolding $\mathcal{A}_{(1)}$ of the source) and
$\tilde F \in \mathbb{R}^{N \times r}$. Then $\tilde F$ minimizes
$\|A - \tilde F (H \odot G)^T\|_F$ over all $N \times r$ matrices if and only if it satisfies
the normal equations
$$\tilde F \bigl((H^T H) .\!* (G^T G)\bigr) = A (H \odot G),$$
where $\odot$ is the Khatri–Rao product and $.*$ is the entrywise product.

The Khatri–Rao product is `Matrix.khatriRao H G`, whose rows are indexed by pairs, and the
columns of $A$ are indexed by the same pairs. The entrywise product is Mathlib's Hadamard
product `Matrix.hadamard`. The proof uses the Gram identity $(H \odot G)^T (H \odot G) = (H^T H)
.\!* (G^T G)$ (`Matrix.khatriRao_transpose_mul_self`). For $N = 1$ this is the vector form of
the source: $z$ minimizes $\|(B \odot C) z - d\|_2$ if and only if
$((B^T B) .\!* (C^T C)) z = (B \odot C)^T d$.

**Reading.** The statement combines the separate least-squares normal equations into one matrix
equivalence. -/
theorem equation_12_5_20 {N p q r : ℕ} (H : Matrix (Fin p) (Fin r) ℝ) (G : Matrix (Fin q) (Fin r) ℝ)
    (A : Matrix (Fin N) (Fin p × Fin q) ℝ) (F : Matrix (Fin N) (Fin r) ℝ) :
    (∀ F' : Matrix (Fin N) (Fin r) ℝ,
        ‖A - F * (khatriRao H G)ᵀ‖ ≤ ‖A - F' * (khatriRao H G)ᵀ‖) ↔
      F * ((Hᵀ * H) ⊙ (Gᵀ * G)) = A * khatriRao H G := by
  have h := isMinOn_norm_sub_mul_conjTranspose_iff A (khatriRao H G) F
  simp only [isMinOn_univ_iff, conjTranspose_eq_transpose_of_trivial,
    khatriRao_transpose_mul_self] at h
  exact h

end ALS

/-! ### Variational singular values and eigenvalues (12.5.22)–(12.5.23) -/

/-- **Equation (12.5.22)** of [golub2013matrix], with the gradient display after it. Let
$A \in \mathbb{R}^{m \times n}$ and
$$\psi_A(u, v) = \frac{u^T A v}{\|u\|_2 \|v\|_2}.$$
Let $u \in \mathbb{R}^m$ and $v \in \mathbb{R}^n$ be nonzero, and let $\hat u = u / \|u\|_2$ and
$\hat v = v / \|v\|_2$. Then $\nabla \psi_A(u, v) = 0$ if and only if
$$A \hat v = \psi_A(u, v) \, \hat u \quad \text{and} \quad A^T \hat u = \psi_A(u, v) \, \hat
  v,$$
and in that case $|\psi_A(u, v)|$ is a singular value of $A$. So the singular values of $A$ are,
up to sign, the stationary values of $\psi_A$.

The function $\psi_A$ is `Matrix.bilinearRayleigh A` on pairs of Euclidean vectors, and
$\nabla \psi_A(u, v) = 0$ is the vanishing of its Fréchet derivative `fderiv`. A singular value
is a value of `Matrix.colSingularValues A`, the square roots of the eigenvalues of $A^T A$
listed with multiplicity, which include zeros when $n > m$.

**Correction.** The stationary quotient is signed. For $A=[1]$, $u=-1$ and $v=1$, it is $-1$.
Its absolute value is a singular value. The hypotheses permit arbitrary nonzero inputs,
normalized in the equations. -/
theorem equation_12_5_22 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) {u : EuclideanSpace ℝ (Fin m)}
    {v : EuclideanSpace ℝ (Fin n)} (hu : u ≠ 0) (hv : v ≠ 0) :
    (fderiv ℝ A.bilinearRayleigh (u, v) = 0 ↔
        toEuclideanLin A (‖v‖⁻¹ • v) = A.bilinearRayleigh (u, v) • ‖u‖⁻¹ • u ∧
          toEuclideanLin Aᵀ (‖u‖⁻¹ • u) = A.bilinearRayleigh (u, v) • ‖v‖⁻¹ • v) ∧
      (fderiv ℝ A.bilinearRayleigh (u, v) = 0 →
        ∃ i, |A.bilinearRayleigh (u, v)| = A.colSingularValues i) :=
  ⟨A.fderiv_bilinearRayleigh_eq_zero_iff hu hv,
    A.abs_critical_bilinearRayleigh_mem_colSingularValues hu hv⟩

/-- **Equation (12.5.23)** of [golub2013matrix]. Let $C \in \mathbb{R}^{N \times N}$ be symmetric
and
$$\phi_C(x) = \frac{x^T C x}{x^T x}.$$
Let $x \neq 0$, and let $f'$ be the derivative of $\phi_C$ at $x$. Then $f' = 0$ if and only if
$$C x = \phi_C(x) \, x.$$
So the stationary vectors of $\phi_C$ are the eigenvectors of $C$, and the stationary values are
its eigenvalues.

The function $\phi_C$ is `LinearMap.rayleighQuotient` of `Matrix.toEuclideanLin C`, and the
derivative is given by the hypothesis `HasFDerivAt`. -/
theorem equation_12_5_23 {N : ℕ} {C : Matrix (Fin N) (Fin N) ℝ} (hC : C.IsSymm)
    {x : EuclideanSpace ℝ (Fin N)} (hx : x ≠ 0) {f' : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ}
    (hf : HasFDerivAt (toEuclideanLin C).rayleighQuotient f' x) :
    f' = 0 ↔ toEuclideanLin C x = (toEuclideanLin C).rayleighQuotient x • x := by
  have hH : C.IsHermitian := by
    rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]
    exact hC
  exact (isSymmetric_toEuclideanLin_iff.2 hH).hasFDerivAt_rayleighQuotient_eq_zero_iff hx hf

/-! ### Tensor trains (12.5.25)–(12.5.29) -/

section TensorTrain

variable {n r : ℕ → ℕ}

/-- **Equation (12.5.25)** of [golub2013matrix], the tensor train of a list of carriages. Let
$\mathcal{G}_k \in \mathbb{R}^{r_{k-1} \times n_k \times r_k}$ for $k = 1, \dots, d$. The
**tensor train** of the carriages is the tensor $\mathcal{T} \in \mathbb{R}^{n_1 \times \cdots
\times n_d}$ with
$$\mathcal{T}(i) = \sum_{\kappa} \mathcal{G}_1(\kappa_0, i_1, \kappa_1) \,
  \mathcal{G}_2(\kappa_1, i_2, \kappa_2) \cdots \mathcal{G}_d(\kappa_{d-1}, i_d, \kappa_d),$$
the sum over all rank indices $\kappa_0, \dots, \kappa_d$.

Indices are 0-based: the carriage `𝒢 k` has the shape `r k × n k × r (k + 1)`, and the carriages
are given for every `k : ℕ`, of which the first $d$ are used. The source has $r_0 = r_d = 1$, so
that the boundary rank indices $\kappa_0$ and $\kappa_d$ take a single value; the definition
does not assume it.

**Reading.** Defines arbitrary-order contraction summing even over nonsingleton boundary ranks.
-/
noncomputable def trainOfCarriages (d : ℕ)
    (𝒢 : ∀ k : ℕ, Fin (r k) → Fin (n k) → Fin (r (k + 1)) → ℝ) :
    Tensor (fun k : Fin d => Fin (n k)) ℝ :=
  Tensor.of fun i => ∑ κ : (∀ j : Fin (d + 1), Fin (r j)),
    ∏ k : Fin d, 𝒢 k (κ k.castSucc) (i k) (κ k.succ)

/-- The carriages read as matrix-valued cores, the convention of the backbone's
`Tensor.tensorTrain`: $G_k(x) = \mathcal{G}_k(:, x, :) \in \mathbb{R}^{r_k \times r_{k+1}}$,
with 0-based indices. -/
def carriageCores (𝒢 : ∀ k : ℕ, Fin (r k) → Fin (n k) → Fin (r (k + 1)) → ℝ) (k : ℕ)
    (x : Fin (n k)) : Matrix (Fin (r k)) (Fin (r (k + 1))) ℝ :=
  of fun p q => 𝒢 k p x q

/-- For vectors $u$ and $v$, $u^T (G_0(i_0) \cdots G_{D-1}(i_{D-1})) v$ is the sum, over all rank
indices $\kappa$, of $u(\kappa_0) \prod_k \mathcal{G}_k(\kappa_k, i_k, \kappa_{k+1}) \,
v(\kappa_D)$. -/
private theorem dotProduct_ttPartial_mulVec
    (𝒢 : ∀ k : ℕ, Fin (r k) → Fin (n k) → Fin (r (k + 1)) → ℝ) :
    ∀ (D : ℕ) (i : ∀ k : Fin D, Fin (n k)) (u : Fin (r 0) → ℝ) (v : Fin (r D) → ℝ),
      u ⬝ᵥ (Tensor.ttPartial (carriageCores 𝒢) D i *ᵥ v) =
        ∑ κ : (∀ j : Fin (D + 1), Fin (r j)),
          u (κ ⟨0, D.succ_pos⟩) * (∏ k : Fin D, 𝒢 k (κ k.castSucc) (i k) (κ k.succ)) *
            v (κ (Fin.last D))
  | 0, i, u, v => by
    rw [Tensor.ttPartial_zero, one_mulVec, dotProduct]
    rw [← (Equiv.piUnique fun j : Fin 1 => Fin (r j)).symm.sum_comp]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.univ_eq_empty, Finset.prod_empty, mul_one]
    rfl
  | D + 1, i, u, v => by
    rw [Tensor.ttPartial_succ, ← mulVec_mulVec, dotProduct_ttPartial_mulVec 𝒢 D]
    rw [← (Fin.snocEquiv fun j : Fin (D + 2) => Fin (r j)).sum_comp, Fintype.sum_prod_type,
      Finset.sum_comm]
    refine Finset.sum_congr rfl fun κ _ => ?_
    simp only [mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Fin.prod_univ_castSucc]
    have h0 : (Fin.snocEquiv fun j : Fin (D + 2) => Fin (r j)) (s, κ) ⟨0, (D + 1).succ_pos⟩ =
        κ ⟨0, D.succ_pos⟩ :=
      Fin.snoc_castSucc (α := fun j : Fin (D + 2) => Fin (r j)) (p := κ) (x := s) ⟨0, D.succ_pos⟩
    have hl : (Fin.snocEquiv fun j : Fin (D + 2) => Fin (r j)) (s, κ) (Fin.last (D + 1)) = s :=
      Fin.snoc_last (α := fun j : Fin (D + 2) => Fin (r j)) (p := κ) (x := s)
    have hc : ∀ k : Fin (D + 1),
        (Fin.snocEquiv fun j : Fin (D + 2) => Fin (r j)) (s, κ) k.castSucc = κ k := fun k =>
      Fin.snoc_castSucc (α := fun j : Fin (D + 2) => Fin (r j)) (p := κ) (x := s) k
    have hs : ∀ k : Fin D,
        ((Fin.snocEquiv fun j : Fin (D + 2) => Fin (r j)) (s, κ) k.castSucc.succ :
          Fin (r (k + 1))) = κ k.succ := fun k =>
      Fin.snoc_castSucc (α := fun j : Fin (D + 2) => Fin (r j)) (p := κ) (x := s) k.succ
    rw [h0, hl]
    simp only [hc, hs]
    have hls : ((Fin.snocEquiv fun j : Fin (D + 2) => Fin (r j)) (s, κ) (Fin.last D).succ :
        Fin (r (D + 1))) = s := hl
    rw [hls, carriageCores, of_apply]
    have e1 : (∏ x : Fin D, 𝒢 (↑x.castSucc) (κ x.castSucc) (i x.castSucc) (κ x.succ)) =
        ∏ k : Fin D, 𝒢 k (κ k.castSucc) (i k.castSucc) (κ k.succ) := rfl
    have e2 : 𝒢 (↑(Fin.last D)) (κ (Fin.last D)) (i (Fin.last D)) s =
        𝒢 D (κ (Fin.last D)) (i (Fin.last D)) s := rfl
    rw [e1, e2]
    ring

/-- **Equation (12.5.25)** of [golub2013matrix]. Let $\mathcal{G}_1, \dots, \mathcal{G}_d$ be
carriages with the boundary ranks $r_0 = r_d = 1$. Then the tensor train of the carriages has
the matrix-product form
$$\mathcal{T}(i) = G_1(i_1) \, G_2(i_2) \cdots G_d(i_d),$$
a product of size $1 \times 1$, where $G_k(i_k) = \mathcal{G}_k(:, i_k, :)$.

The left side is `GolubVanLoan.Chapter12.trainOfCarriages`, and the right side is the backbone's
`Tensor.tensorTrain` with the cores `GolubVanLoan.Chapter12.carriageCores`.

**Reading.** Equivalent core matrix contractions with boundary ranks one in every order.
-/
theorem equation_12_5_25 (d : ℕ) (𝒢 : ∀ k : ℕ, Fin (r k) → Fin (n k) → Fin (r (k + 1)) → ℝ)
    (h0 : r 0 = 1) (hd : r d = 1) :
    trainOfCarriages d 𝒢 = Tensor.tensorTrain (carriageCores 𝒢) d h0 hd := by
  ext i
  rw [Tensor.tensorTrain_apply]
  have key := dotProduct_ttPartial_mulVec 𝒢 d i (Pi.single (Fin.cast h0.symm 0) 1)
    (Pi.single (Fin.cast hd.symm 0) 1)
  rw [single_dotProduct, one_mul, mulVec_single_one, col_apply] at key
  rw [key, trainOfCarriages, Tensor.of_apply]
  refine Finset.sum_congr rfl fun κ _ => ?_
  have e0 : κ ⟨0, d.succ_pos⟩ = Fin.cast h0.symm 0 :=
    Fin.ext (by have := (κ ⟨0, d.succ_pos⟩).isLt; simp [h0] at this ⊢; omega)
  have ed : κ (Fin.last d) = Fin.cast hd.symm 0 :=
    Fin.ext (by have := (κ (Fin.last d)).isLt; simp [hd] at this ⊢; omega)
  rw [e0, ed, Pi.single_eq_same, Pi.single_eq_same, one_mul, mul_one]

end TensorTrain

/-- **Equations (12.5.26)–(12.5.28)** of [golub2013matrix], with Problem P12.5.11. Let
$C \in \mathbb{R}^{pm \times N}$ be the unfolding $\mathcal{C}_{[1\,2] \times [3\,4]}$, with
rows indexed by the pairs $(k_2, i_3)$, $1 \le k_2 \le p$ and $1 \le i_3 \le m$. If $C = U_3 W$
with $U_3 \in \mathbb{R}^{pm \times s}$ and $W \in \mathbb{R}^{s \times N}$, for example the
thin SVD $C = U_3 (\Sigma_3 V_3^T)$ with $s = r_3 = \operatorname{rank}(C)$, then the carriage
$\mathcal{G}_3(k_2, i_3, k_3) = U_3((k_2, i_3), k_3)$ and $\tilde{\mathcal{C}} = W$ satisfy
(12.5.26):
$$\mathcal{C}(k_2, i_3, \cdot) = \sum_{k_3 = 1}^{s} \mathcal{G}_3(k_2, i_3, k_3) \,
  \tilde{\mathcal{C}}(k_3, \cdot).$$
Moreover, a carriage $\mathcal{G}_3$ with $s$ columns and a matrix $\tilde{\mathcal{C}}$ with
this property exist whenever $\operatorname{rank}(C) \le s$.

The columns of $C$ are indexed by any finite type. For a fixed $i_3$, the carriage is the
$p \times s$ matrix `of fun k' k₃ => U₃ (k', i) k₃`. The existence part is the backbone's
`Tensor.exists_ttCore_of_rank`.

**Generalization.** The reshaping identity takes an arbitrary factorization, with rank alone
ensuring existence of a compressed one. -/
theorem equation_12_5_28 {p m s : ℕ} {N : Type*} [Fintype N] (C : Matrix (Fin p × Fin m) N ℝ) :
    (∀ (U₃ : Matrix (Fin p × Fin m) (Fin s) ℝ) (W : Matrix (Fin s) N ℝ), C = U₃ * W →
      ∀ k i c, C (k, i) c = ((of fun k' k₃ => U₃ (k', i) k₃) * W) k c) ∧
    (C.rank ≤ s → ∃ (G : Fin m → Matrix (Fin p) (Fin s) ℝ) (C' : Matrix (Fin s) N ℝ),
      ∀ k i c, C (k, i) c = (G i * C') k c) := by
  refine ⟨fun U₃ W hC k i c => ?_, Tensor.exists_ttCore_of_rank C⟩
  rw [hC, Matrix.mul_apply, Matrix.mul_apply]
  rfl

/-! ### Tensor singular values and eigenvalues, tensor trains -/

section Variational

variable {d : ℕ} {n : Fin d → ℕ}

/-- **Section 12.5.6** of [golub2013matrix], singular values of a tensor. Let $\mathcal{A} \in
\mathbb{R}^{n_1 \times \cdots \times n_d}$, and for vectors $u_k \in \mathbb{R}^{n_k}$ let
$$\mathcal{A}(u_1, \dots, u_d) = \sum_{i} \mathcal{A}(i) \, u_1(i_1) \cdots u_d(i_d), \qquad
  \psi_{\mathcal{A}}(u) = \frac{\mathcal{A}(u_1, \dots, u_d)}{\|u_1\|_2 \cdots \|u_d\|_2}.$$
Then for every mode $k$,
$$\mathcal{A}(u_1, \dots, u_d) = u_k^T \mathcal{A}_{(k)} \Bigl(\bigotimes_{j \neq k}
  u_j\Bigr);$$
for $d = 3$ this is the source's $u_1^T \mathcal{A}_{(1)} (u_3 \otimes u_2) = u_2^T
\mathcal{A}_{(2)} (u_3 \otimes u_1) = u_3^T \mathcal{A}_{(3)} (u_2 \otimes u_1)$. Moreover, if
every $u_i$ is nonzero and $\hat u_i = u_i / \|u_i\|_2$, then $\nabla \psi_{\mathcal{A}}(u) = 0$
if and only if
$$\mathcal{A}_{(k)} \Bigl(\bigotimes_{j \neq k} \hat u_j\Bigr) = \psi_{\mathcal{A}}(u) \, \hat
  u_k \quad \text{for every mode } k.$$
This condition is the source's definition of a singular value of the tensor
(`Tensor.IsSingularValue`).

The form $\mathcal{A}(u)$ is `Tensor.multilinearForm A u`. The quotient $\psi_{\mathcal{A}}$ is
`Tensor.multilinearRayleigh A`. The condition $\nabla \psi_{\mathcal{A}}(u) = 0$ is
`HasFDerivAt` with the derivative $0$. The unfoldings are the typed unfoldings
`Tensor.modeUnfold`, whose columns are the tuples of the other indices. The tensor
$\bigotimes_{j \neq k} u_j$ is the rank-one tensor `Tensor.rankOne` of the other vectors.

**Generalization.** The derivative criterion applies to a tensor of any order, with normalized
factors in each mode. -/
theorem tensor_singular_value (A : RTensor n) :
    (∀ (u : ∀ i, Fin (n i) → ℝ) (k : Fin d), Tensor.multilinearForm A u =
      u k ⬝ᵥ (A.modeUnfold k *ᵥ Tensor.rankOne fun j : {j // j ≠ k} => u j)) ∧
    ∀ {u : ∀ i, EuclideanSpace ℝ (Fin (n i))}, (∀ i, u i ≠ 0) →
      (HasFDerivAt (Tensor.multilinearRayleigh A)
          (0 : (∀ i, EuclideanSpace ℝ (Fin (n i))) →L[ℝ] ℝ) u ↔
        ∀ k, A.modeUnfold k *ᵥ Tensor.rankOne (fun j : {j // j ≠ k} => (‖u j‖⁻¹ • u j).ofLp)
          = Tensor.multilinearRayleigh A u • (‖u k‖⁻¹ • u k).ofLp) :=
  ⟨fun u k => Tensor.multilinearForm_eq_modeUnfold A u k,
    fun hu => Tensor.hasFDerivAt_multilinearRayleigh_eq_zero_iff A hu⟩

/-- **Equation (12.5.24)** of [golub2013matrix], with the sentences around it. Let $\mathcal{C} \in
\mathbb{R}^{N \times \cdots \times N}$ be a symmetric tensor of order $d$ (§12.5.7), that is,
its entries are invariant under every permutation of the modes. Then all modal unfoldings of
$\mathcal{C}$ are equal, up to the relabelling of their columns by the transposition of the two
modes. Let
$$\phi_{\mathcal{C}}(x) = \frac{\mathcal{C}(x, \dots, x)}{\|x\|_2^d}.$$
For $x \neq 0$, with $\hat x = x / \|x\|_2$, and for every mode $k$,
$\nabla \phi_{\mathcal{C}}(x) = 0$ if and only if
$$\mathcal{C}_{(k)} (\hat x \otimes \cdots \otimes \hat x) = \phi_{\mathcal{C}}(x) \, \hat x,$$
which is the source's definition of an eigenvalue of the tensor.

**Typo.** The gradient of $\phi_{\mathcal{C}}$ in the source omits the factor $d$. This does not
change where the gradient vanishes.

Symmetry is `Tensor.IsSymm`, the relabelling of the columns is `Tensor.swapColEquiv k l`, and
$\phi_{\mathcal{C}}$ is `Tensor.symmetricRayleigh C`. The unfoldings are the typed unfoldings
`Tensor.modeUnfold`, and $\hat x \otimes \cdots \otimes \hat x$ is the rank-one tensor of
$d - 1$ copies of $\hat x$. -/
theorem equation_12_5_24 {N : ℕ} {C : Tensor (fun _ : Fin d => Fin N) ℝ} (hC : C.IsSymm) :
    (∀ k l, C.modeUnfold l = (C.modeUnfold k).submatrix id (Tensor.swapColEquiv k l).symm) ∧
    ∀ {x : EuclideanSpace ℝ (Fin N)}, x ≠ 0 → ∀ k,
      (HasFDerivAt (Tensor.symmetricRayleigh C) (0 : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ) x ↔
        C.modeUnfold k *ᵥ Tensor.rankOne (fun _ : {j // j ≠ k} => (‖x‖⁻¹ • x).ofLp)
          = Tensor.symmetricRayleigh C x • (‖x‖⁻¹ • x).ofLp) :=
  ⟨fun k l => hC.modeUnfold_eq k l,
    fun hx k => Tensor.hasFDerivAt_symmetricRayleigh_eq_zero_iff hC hx k⟩

end Variational

/-- **Equation (12.5.29)** of [golub2013matrix] (TT-SVD of Oseledets and Tyrtyshnikov). Every tensor
$\mathcal{A} \in \mathbb{R}^{n_1 \times \cdots \times n_d}$ of order $d \ge 1$ is the tensor
train (12.5.25) of some carriages $\mathcal{G}_1, \dots, \mathcal{G}_d$ whose ranks are
$r_0 = r_d = 1$ and
$$r_k = \operatorname{rank}\bigl(\mathcal{A}_{[1:k] \times [k+1:d]}\bigr), \qquad 0 < k < d,$$
the ranks of the sequential unfoldings. These are the ranks of the matrices that the successive
SVDs of the procedure factor.

For $d = 0$ a tensor train is the constant $1$, so the hypothesis $d \neq 0$ is needed. The
sequential unfolding is `Tensor.unfold` with the 0-based modes below $k$ as row modes, and the
train is `GolubVanLoan.Chapter12.trainOfCarriages`. The proof specializes the backbone's
`Tensor.exists_tensorTrain_of_ne_zero`, through `GolubVanLoan.Chapter12.equation_12_5_25`. The
procedure itself is not a program, because its ranks depend on the data.

**Reading.** Existence of exact train with unfolding ranks instead of executable sequence of SVDs.
-/
theorem equation_12_5_29 {n : ℕ → ℕ} {d : ℕ} (hd : d ≠ 0)
    (A : Tensor (fun k : Fin d => Fin (n k)) ℝ) :
    ∃ (r : ℕ → ℕ) (_ : r 0 = 1) (_ : r d = 1),
      (∀ k, 0 < k → k < d → r k = (A.unfold fun i : Fin d => (i : ℕ) < k).rank) ∧
      ∃ 𝒢 : ∀ k : ℕ, Fin (r k) → Fin (n k) → Fin (r (k + 1)) → ℝ, A = trainOfCarriages d 𝒢 := by
  obtain ⟨r, h0, hr, hrk, G, hG⟩ := Tensor.exists_tensorTrain_of_ne_zero A hd
  refine ⟨r, h0, hr, hrk, fun k p x q => G k x p q, ?_⟩
  rw [equation_12_5_25 d _ h0 hr, hG]
  rfl

end GolubVanLoan.Chapter12
