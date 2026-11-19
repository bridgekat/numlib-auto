/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Numlib.Analysis.Matrix.OperatorNorm
import Numlib.Direct.Updating
import NumlibSurface.GolubVanLoan.Chapter05.Section02

/-!
# Golub and Van Loan, Section 6.5: Updating matrix factorizations

This module formalizes §6.5 of [golub2013matrix]: how a QR or Cholesky factorization changes when
the matrix changes slightly. If $A = QR$ and $\tilde A = A + uv^T$, then $\tilde A = Q(R + wv^T)$
with $w = Q^T u$ (6.5.1), and two sweeps of Givens rotations restore the triangular form through an
upper Hessenberg matrix ((6.5.2)–(6.5.3)). Similar sweeps update the QR factorization after a column
is deleted or appended (§6.5.2) and after a row is appended or deleted (§6.5.3). For a Cholesky
factorization $A = GG^T$, the update $\tilde A = A + zz^T$ is a QR factorization of the stacked
matrix $[G^T; z^T]$ ((6.5.5)–(6.5.7)). The downdate $\tilde A = A - zz^T$ uses $S$-orthogonal
matrices for $S = \operatorname{diag}(I_n, -1)$ and hyperbolic rotations ((6.5.8)–(6.5.15), Theorem
6.5.1). Finally, the module states the exact content of the rank-revealing ULV decomposition
(6.5.16) and its approximate null space (§6.5.5).

The section has no numbered algorithm. Its procedures are programs named by their content, each with
a theorem on its exact-arithmetic correctness. The proofs specialize `Numlib.Direct.Updating` (the
structure of the sweeps, the existence of the updated factorizations, the Gram identities of the
stacked matrices, and Theorem 6.5.1 as `Matrix.hyperbolicDowndate_step`),
`Numlib.LinearAlgebra.Matrix.PlaneRotation` (hyperbolic rotations, `Matrix.hyperbolicPair` and
`Matrix.IsJOrthogonal`) and `Numlib.Analysis.Matrix.OperatorNorm`, together with the programs of
Chapter 5 and Algorithms 1.1.2–1.1.3 of Chapter 1.

## Main definitions

* §6.5.1, `GolubVanLoan.Chapter06.qrUpdateRankOne`: the QR factorization of $A + uv^T$ from that of
  $A$.
* §6.5.2, `GolubVanLoan.Chapter06.qrDeleteColumn`: the QR factorization after a column is deleted.
* §6.5.2, `GolubVanLoan.Chapter06.qrInsertColumn`: the QR factorization after a column is inserted.
* §6.5.3, `GolubVanLoan.Chapter06.qrInsertRow`: the QR factorization after a row is inserted.
* §6.5.3, `GolubVanLoan.Chapter06.qrDeleteFirstRow`: the QR factorization after the first row is
  deleted.
* §6.5.4, `GolubVanLoan.Chapter06.choleskyUpdate`: the Cholesky factor of $A + zz^T$ by Givens
  rotations.
* Equation (6.5.11), `GolubVanLoan.Chapter06.IsSOrthogonal`: $H S H^T = S$ for
  $S = \operatorname{diag}(I_n, -1)$.
* §6.5.4, `GolubVanLoan.Chapter06.choleskyDowndate`: the Cholesky factor of $A - zz^T$ by hyperbolic
  rotations.

## Main results

* Equation (6.5.1), `GolubVanLoan.Chapter06.equation_6_5_1`: $A + uv^T = Q(R + wv^T)$ with
  $w = Q^T u$.
* Equation (6.5.2), `GolubVanLoan.Chapter06.equation_6_5_2`: a sweep of rotations in adjacent planes
  maps an upper triangular $R$ to an upper Hessenberg matrix.
* Equation (6.5.3), `GolubVanLoan.Chapter06.equation_6_5_3`: if the sweep maps $w$ to $\rho e_1$,
  then it maps $R + wv^T$ to the upper Hessenberg matrix $H + \rho e_1 v^T$.
* §6.5.1, `GolubVanLoan.Chapter06.qrUpdateRankOne_spec`: in exact arithmetic the rank-one update
  returns a QR factorization of $A + uv^T$.
* §6.5.2, `GolubVanLoan.Chapter06.qrDeleteColumn_spec`: in exact arithmetic the column deletion
  returns a QR factorization.
* §6.5.2, `GolubVanLoan.Chapter06.qrInsertColumn_spec`: in exact arithmetic the column insertion
  returns a QR factorization.
* §6.5.3, `GolubVanLoan.Chapter06.qrInsertRow_spec`: in exact arithmetic the row insertion returns a
  QR factorization.
* §6.5.3, `GolubVanLoan.Chapter06.qrDeleteFirstRow_spec`: in exact arithmetic the deletion of the
  first row returns a QR factorization.
* §6.5.3, `GolubVanLoan.Chapter06.qrDeleteRow_exists`: after any row is deleted, a QR factorization
  exists.
* Equation (6.5.6), `GolubVanLoan.Chapter06.equation_6_5_6`: $A + zz^T = [G^T; z^T]^T [G^T; z^T]$.
* Equation (6.5.7), `GolubVanLoan.Chapter06.equation_6_5_7`: if $Q^T [G^T; z^T] = [R; 0]$ with $Q$
  orthogonal, then $A + zz^T = R^T R$.
* §6.5.4, `GolubVanLoan.Chapter06.choleskyUpdate_spec`: in exact arithmetic the Cholesky update
  returns a Cholesky factor of $A + zz^T$, up to the signs of its diagonal.
* Equation (6.5.10), `GolubVanLoan.Chapter06.equation_6_5_10`:
  $A - zz^T = [G^T; z^T]^T S [G^T; z^T]$.
* §6.5.4, `GolubVanLoan.Chapter06.IsSOrthogonal.mul`: a product of $S$-orthogonal matrices is
  $S$-orthogonal.
* Equation (6.5.12), `GolubVanLoan.Chapter06.equation_6_5_12`: if $H^T [G^T; z^T] = [R; 0]$ with $H$
  $S$-orthogonal, then $A - zz^T = R^T R$.
* §6.5.4, `GolubVanLoan.Chapter06.hyperbolicRotation_isSOrthogonal`: a hyperbolic rotation is
  $S$-orthogonal.
* Equation (6.5.13), `GolubVanLoan.Chapter06.equation_6_5_13`: the hyperbolic rotation computed from
  $\tau = x_2/x_1$ zeroes $x_2$ when $|x_2| < |x_1|$.
* §6.5.4, `GolubVanLoan.Chapter06.hyperbolic_not_exists`: no hyperbolic rotation zeroes $x_2$ when
  $|x_1| \le |x_2|$ and $x_2 \neq 0$.
* §6.5.4, `GolubVanLoan.Chapter06.abs_lt_of_posDef_sub`: if $A - zz^T$ is positive definite, then
  $|z_1| < |g_{11}|$.
* Theorem 6.5.1, `GolubVanLoan.Chapter06.theorem_6_5_1`: one hyperbolic rotation zeroes the first
  entry of $z$ and leaves a smaller positive definite downdating problem.
* Equation (6.5.14), `GolubVanLoan.Chapter06.equation_6_5_14`: the first row and the trailing block
  of a Cholesky factor.
* Equation (6.5.15), `GolubVanLoan.Chapter06.equation_6_5_15`: the cosh–sinh pair of the first
  downdating step.
* §6.5.4, `GolubVanLoan.Chapter06.choleskyDowndate_exists`: the factorization (6.5.12) exists with a
  product of hyperbolic rotations.
* §6.5.4, `GolubVanLoan.Chapter06.choleskyDowndate_spec`: in exact arithmetic the Cholesky downdate
  returns the Cholesky factor of $A - zz^T$.
* Equation (6.5.16), `GolubVanLoan.Chapter06.equation_6_5_16`: pivoted QR followed by a QR
  factorization of $R^T$ gives a ULV decomposition.
* §6.5.5, `GolubVanLoan.Chapter06.ulv_nullspace_norm`: $\|AV_2\|_2 = \|L_{22}\|_2$.

## Conventions

* Matrices are real and indices are 0-based: the $n \times n$ matrices of the source are
  `Matrix (Fin n) (Fin n) ℝ`.
* The QR factorization $A = QR$ is `Matrix.IsQR A Q R`: $Q$ is orthogonal (in `Matrix.unitaryGroup`
  over $\mathbb{R}$) and $R$ is upper trapezoidal.
* The Cholesky factorization $A = GG^T$ with $G$ lower triangular is `Matrix.IsCholesky A Gᵀ`: the
  factor $G^T$ is upper triangular with positive diagonal, and $(G^T)^T G^T = A$.
* The stacked matrix $[G^T; z^T]$ of (6.5.6) and (6.5.10) is
  `Matrix.fromRows Gᵀ (replicateRow Unit z)`, with the rows indexed by `Fin n ⊕ Unit`. The signature
  $S = \operatorname{diag}(I_n, -1)$ of (6.5.9) is Mathlib's
  `LieAlgebra.Orthogonal.indefiniteDiagonal (Fin n) Unit`.
* A sweep of rotations in the adjacent planes $(k, k + 1)$ is a product of the matrices
  `Matrix.adjacentEmbed k (G k)`. The hyperbolic rotation $H_k$ of §6.5.4 is
  `Matrix.hyperbolicRotation (Sum.inl k) (Sum.inr ()) c s`.
* In (6.5.16), the partitions $[R; 0]$ are `Matrix.fromRows` over `Fin n ⊕ Fin p`, and the rows of
  `A : Matrix (Fin (n + p)) (Fin n) ℝ` are reindexed by `finSumFinEquiv`.

## Implementation notes

* The programs follow the algorithm conventions of the library: every product, difference, quotient
  and square root is rounded by `rnd`, loops are `List.foldlM`, and the exact semantics (`M := Id`,
  `rnd := pure`) is a `_spec` theorem against the backbone.
* The Cholesky downdate `GolubVanLoan.Chapter06.choleskyDowndate` writes out its hyperbolic
  rotations, which are not Givens rotations, through the row helper
  `GolubVanLoan.Chapter05.hyperbolicApplyLeft`.
* The Givens procedures call the shared programs of Chapter 5: the pair
  $[c, s] = \operatorname{givens}(a, b)$ is `GolubVanLoan.Chapter05.algorithm_5_1_3`; the rotations
  of two rows, of two columns of $Q$, and of two entries of a vector are
  `GolubVanLoan.Chapter05.givensApplyLeft`, `GolubVanLoan.Chapter05.givensApplyRight` and
  `GolubVanLoan.Chapter05.givensRotateVec`. The products $Q^T u$ are the gaxpy
  `GolubVanLoan.Chapter01.algorithm_1_1_3`, and the rank-one change of the first row is the saxpy
  `GolubVanLoan.Chapter01.algorithm_1_1_2`.
* Two sweeps of Chapter 5 are shared: the top-down triangularization of an upper Hessenberg matrix,
  `GolubVanLoan.Chapter05.givensHessenbergSweep` (after Algorithm 5.2.5), and the bottom-up sweep
  driven by a vector, `GolubVanLoan.Chapter05.givensVectorSweep`.
* Every rotation is applied to all the columns (or all the rows) of its matrix. The source leaves
  the column ranges implicit; the extra columns are zero in both rotated rows.

## Deviations from the source

* **Equations (6.5.6) and (6.5.10)** (generalization). The two Gram identities hold for any
  square $G$ with $GG^T=A$, without the source's positive-definite Cholesky setting. See
  `GolubVanLoan.Chapter06.equation_6_5_6` and `GolubVanLoan.Chapter06.equation_6_5_10`.
* **Equations (6.5.2)–(6.5.3)** (generalization). Arbitrary embedded adjacent blocks preserve
  the Hessenberg structure. The rank-one update identity assumes only that the sweep maps $w$ to
  $\rho e_1$. See `GolubVanLoan.Chapter06.equation_6_5_2` and
  `GolubVanLoan.Chapter06.equation_6_5_3`.
* **§6.5.2** (generalization). The column updates accept wide upper trapezoidal factors.
  Insertion can occur at the first column. See `GolubVanLoan.Chapter06.qrDeleteColumn` and
  `GolubVanLoan.Chapter06.qrInsertColumn`.
* **§6.5.3, row deletion** (reading). The arbitrary-row result gives existence of a QR
  factorization. The implemented update treats the source's detailed first-row procedure. See
  `GolubVanLoan.Chapter06.qrDeleteRow_exists` and `GolubVanLoan.Chapter06.qrDeleteFirstRow`.
* **§6.5.4, downdate sweep** (typo). The matrix whose bottom row is zeroed is the stack
  $[G^T;z^T]$. The prose immediately before Theorem 6.5.1 transposes the concatenation
  $[G^T\mid z]$, which gives $[G;z^T]$. See
  `GolubVanLoan.Chapter06.choleskyDowndate`.
* **§6.5.1** (typo). "Following Algorithm 5.2.4" means Algorithm 5.2.5, the QR factorization of an
  upper Hessenberg matrix. See `GolubVanLoan.Chapter06.qrUpdateRankOne`.
* **Equation (6.5.7)** (typo). The source prints $\tilde A = RR^T$. The correct identity is
  $\tilde A = R^T R$. See `GolubVanLoan.Chapter06.equation_6_5_7`.
* **Equation (6.5.7)** (correction). The source says that $\tilde G = R^T$ is the updated Cholesky
  factor. When the rotations are Givens rotations, the diagonal of $R$ can have negative entries, so
  $R^T$ is the Cholesky factor only after the signs of its diagonal are normalized. See
  `GolubVanLoan.Chapter06.equation_6_5_7` and `GolubVanLoan.Chapter06.choleskyUpdate_spec`.
* **Equation (6.5.12)** (correction). The source says that $\tilde G = R^T$ is the Cholesky factor
  of $A - zz^T$. The statement normalizes the signs of the diagonal of $R$, as for (6.5.7). See
  `GolubVanLoan.Chapter06.equation_6_5_12`.
* **§6.5.4, nonexistence of a hyperbolic rotation** (generalization). The source treats
  $|x_2| > |x_1|$. The statement also covers $|x_2| = |x_1| \neq 0$. See
  `GolubVanLoan.Chapter06.hyperbolic_not_exists`.
* **Proof of Theorem 6.5.1** (typo). The Schur complement in the proof uses the pivot
  $\alpha - \mu^2$, printed as $\alpha$ in the prose. See `GolubVanLoan.Chapter06.theorem_6_5_1`.
* **Equation (6.5.16)** (generalization). The source obtains $\Pi$ and $R$ from QR with column
  pivoting. The statement holds for every orthogonal $\Pi$ and every $R$ with $U^T A \Pi = [R; 0]$.
  See `GolubVanLoan.Chapter06.equation_6_5_16`.
* **§6.5.5** (typo). In $\|AV_2\|_2 = \|U_2 L_{22}\|_2$, the source takes $U_2 = U(:, r{+}1{:}m)$,
  which does not match the $n - r$ rows of $L_{22}$. The columns $r{+}1{:}n$ of $U$ are meant; in
  both readings the norm is $\|L_{22}\|_2$. See `GolubVanLoan.Chapter06.ulv_nullspace_norm`.

## Not formalized

* **The ULV updating procedure of §6.5.5 beyond (6.5.16):** condition estimation, the "small"
  entries, "$\approx \sigma_{\min}$", and zero chasing.
* **The rank-revealing smallness of $L_{21}$ and $L_{22}$ in (6.5.16).** It is a heuristic property
  of QR with column pivoting.
* **The numerical caveats on hyperbolic rotations with $|x_1| \approx |x_2|$.**
* **The flop counts** ($26n^2$, $O(n^2)$, $O(mn)$).
* **Displays (6.5.4), (6.5.5), (6.5.8) and (6.5.9).** They only name data.
-/

open Matrix

namespace GolubVanLoan.Chapter06

/-! ### §6.5.1 Rank-one changes -/

/-- **Equation (6.5.1)** of [golub2013matrix]. Suppose $A = QR$ is a QR factorization of
$A \in \mathbb{R}^{n \times n}$, and let $u, v \in \mathbb{R}^n$. Then $$\tilde A = A + uv^T =
Q(R + wv^T), \qquad w = Q^T u.$$
-/
theorem equation_6_5_1 {n : ℕ} {A Q R : Matrix (Fin n) (Fin n) ℝ} (h : IsQR A Q R)
    (u v : Fin n → ℝ) : A + vecMulVec u v = Q * (R + vecMulVec (Qᵀ *ᵥ u) v) := by
  have hQ : Q * Qᵀ = 1 := by
    exact (mem_orthogonalGroup_iff _ ℝ).1 h.mem_unitaryGroup
  rw [Matrix.mul_add, h.mul_eq, mul_vecMulVec, mulVec_mulVec, hQ, one_mulVec]

/-- **Equation (6.5.2)** of [golub2013matrix]. Let $R \in \mathbb{R}^{n \times n}$ be upper
triangular, and let $J_1, \dots, J_{n-1}$ be matrices such that $J_k^T$ acts only in the planes
$k$ and $k + 1$. Then $$H = J_1^T \cdots J_{n-1}^T R$$ is upper Hessenberg: $h_{il} = 0$
whenever $i > l + 1$.

**Generalization.** The source takes Givens rotations computed so that
$J_1^T \cdots J_{n-1}^T w = \pm\|w\|_2 e_1$. The shape holds whatever the rotations are.

The factor $J_k^T$ is `Matrix.adjacentEmbed (k - 1) (G (k - 1))` for an arbitrary $2 \times 2$
block, which acts in the 0-based plane $(k - 1, k)$. The product $P = J_1^T \cdots J_{n-1}^T$
applies $J_{n-1}^T$ first. -/
theorem equation_6_5_2 {n : ℕ} {R : Matrix (Fin n) (Fin n) ℝ} (hR : R.IsUpperTriangular)
    (G : ℕ → Matrix (Fin 2) (Fin 2) ℝ) {P : Matrix (Fin n) (Fin n) ℝ}
    (hP : P = (List.map (fun j => adjacentEmbed j (G j)) (List.range (n - 1))).prod)
    (i l : Fin n) (hil : (l : ℕ) + 1 < i) : (P * R) i l = 0 := by
  have hT : R.HasLowerBandwidthRect 0 := fun i j hij => hR (by
    change j < i
    rw [Fin.lt_def]
    omega)
  rw [hP, List.range_eq_range', prod_map_range'_eq_prodFwd]
  exact prodFwd_adjacentEmbed_mul_apply_eq_zero hT G 0 (n - 1) (Or.inl hil)

/-- **Equation (6.5.3)** of [golub2013matrix]. Let $R \in \mathbb{R}^{n \times n}$ be upper
triangular with $n \ge 1$, let $P = J_1^T \cdots J_{n-1}^T$ be a sweep of rotations in adjacent
planes as in (6.5.2), and let $w, v \in \mathbb{R}^n$ with $Pw = \rho e_1$. Then $$P(R + wv^T) =
PR + \rho e_1 v^T = H_1,$$ and $H_1$ is upper Hessenberg.

The source has $\rho = \pm\|w\|_2$. As in (6.5.2), the $2 \times 2$ blocks of the rotations are
arbitrary.

**Generalization.** The proof uses arbitrary adjacent two-by-two blocks that map $w$ to $\rho
e_1$. For the orthogonal sweep in the source, $|\rho|=\|w\|_2$. -/
theorem equation_6_5_3 {n : ℕ} {R : Matrix (Fin n) (Fin n) ℝ} (hR : R.IsUpperTriangular)
    (G : ℕ → Matrix (Fin 2) (Fin 2) ℝ) {P : Matrix (Fin n) (Fin n) ℝ}
    (hP : P = (List.map (fun j => adjacentEmbed j (G j)) (List.range (n - 1))).prod)
    {w : Fin n → ℝ} {ρ : ℝ} (hn : 0 < n) (hw : P *ᵥ w = Pi.single ⟨0, hn⟩ ρ) (v : Fin n → ℝ) :
    P * (R + vecMulVec w v) = P * R + vecMulVec (Pi.single ⟨0, hn⟩ ρ) v ∧
      ∀ i l : Fin n, (l : ℕ) + 1 < i → (P * (R + vecMulVec w v)) i l = 0 := by
  have e : P * (R + vecMulVec w v) = P * R + vecMulVec (Pi.single ⟨0, hn⟩ ρ) v := by
    rw [Matrix.mul_add, mul_vecMulVec, hw]
  refine ⟨e, fun i l hil => ?_⟩
  rw [e, Matrix.add_apply, equation_6_5_2 hR G hP i l hil, zero_add, vecMulVec_apply,
    Pi.single_apply, ite_eq_right (fun h => by rw [h] at hil; simp at hil), zero_mul]

/-! ### §6.5.3 Appending or deleting a row -/

/-- **Section 6.5.3** of [golub2013matrix], deleting an arbitrary row ("The procedure is similar
when an arbitrary row is deleted."). If $A = QR$ is a QR factorization of
$A \in \mathbb{R}^{(m+1) \times n}$ and $k$ is a row index, then the matrix $A$ with its row $k$
deleted has a QR factorization.

**Reading.** The arbitrary-row declaration gives existence of the smaller QR factorization. The
executable Givens sweep in this module treats deletion of the first row. -/
theorem qrDeleteRow_exists {m n : ℕ} {A : Matrix (Fin (m + 1)) (Fin n) ℝ}
    {Q : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ} {R : Matrix (Fin (m + 1)) (Fin n) ℝ}
    (h : IsQR A Q R) (k : Fin (m + 1)) :
    ∃ Q₁ R₁, IsQR (A.submatrix k.succAbove id) Q₁ R₁ := by
  obtain ⟨-, -, -, Q₁, -, R₁, -, -, -, -, h₁⟩ := h.exists_deleteRow k
  exact ⟨Q₁, R₁, h₁⟩

/-! ### §6.5.4 Cholesky updating -/

/-- **Equation (6.5.6)** of [golub2013matrix]. Let $G \in \mathbb{R}^{n \times n}$ with $GG^T = A$,
and let $z \in \mathbb{R}^n$. Then $\tilde A = A + zz^T$ (6.5.5) satisfies $$\tilde A =
\begin{bmatrix} G^T \\ z^T \end{bmatrix}^T \begin{bmatrix} G^T \\ z^T \end{bmatrix}.$$

**Reading.** Stacked Gram identity only uses GGᵀ=A, without definite or triangular premise.
-/
theorem equation_6_5_6 {n : ℕ} {A G : Matrix (Fin n) (Fin n) ℝ} (hA : G * Gᵀ = A)
    (z : Fin n → ℝ) :
    A + vecMulVec z z =
      (fromRows Gᵀ (replicateRow Unit z))ᵀ * fromRows Gᵀ (replicateRow Unit z) := by
  rw [transpose_mul_self_fromRows, transpose_transpose, hA]

/-- **Equation (6.5.7)** of [golub2013matrix]. Let $G \in \mathbb{R}^{n \times n}$ with $GG^T = A$
and $z \in \mathbb{R}^n$, and let $Q \in \mathbb{R}^{(n+1) \times (n+1)}$ be orthogonal with
$$Q^T \begin{bmatrix} G^T \\ z^T \end{bmatrix} = \begin{bmatrix} R \\ 0 \end{bmatrix}.$$ Then
$A + zz^T = R^T R$. If moreover $R$ is upper triangular with nonzero diagonal, and $D =
\operatorname{diag}(\operatorname{sign}(r_{ii}))$, then $DR$ is the upper triangular Cholesky
factor of $A + zz^T$, so the updated Cholesky factor is $\tilde G = R^T D$.

**Typo.** The source prints $\tilde A = RR^T$. The correct identity is $\tilde A = R^T R$.

**Correction.** The source says that $\tilde G = R^T$ is the updated Cholesky factor. A Givens
rotation can produce a negative diagonal entry $r$, so $R^T$ is the Cholesky factor only after
the signs of its diagonal are normalized.

The source takes $Q = Q_1 \cdots Q_n$, a product of Givens rotations; the statement holds for
every orthogonal $Q$. The stacked matrix is `Matrix.fromRows Gᵀ (replicateRow Unit z)`, and the
Cholesky factor is `Matrix.IsCholesky`. -/
theorem equation_6_5_7 {n : ℕ} {A G R : Matrix (Fin n) (Fin n) ℝ} (hA : G * Gᵀ = A)
    {z : Fin n → ℝ} {Q : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ}
    (hQ : Q ∈ orthogonalGroup (Fin n ⊕ Unit) ℝ)
    (h : Qᵀ * fromRows Gᵀ (replicateRow Unit z) = fromRows R 0) :
    A + vecMulVec z z = Rᵀ * R ∧
      (R.IsUpperTriangular → (∀ i, R i i ≠ 0) →
        IsCholesky (A + vecMulVec z z) (diagonal (fun i => (SignType.sign (R i i) : ℝ)) * R)) := by
  have e : A + vecMulVec z z = Rᵀ * R := by
    rw [equation_6_5_6 hA, transpose_mul_self_eq_of_mem_orthogonalGroup hQ h]
  exact ⟨e, fun hR hd => isCholesky_diagonal_sign_mul hR hd e.symm⟩

/-! ### §6.5.4 Cholesky downdating: $S$-orthogonality and hyperbolic rotations -/

/-- **Equation (6.5.10)** of [golub2013matrix]. Let $G \in \mathbb{R}^{n \times n}$ with $GG^T = A$,
let $z \in \mathbb{R}^n$, and let $S = \operatorname{diag}(I_n, -1)$ (6.5.9). Then $$\tilde A =
GG^T - zz^T = \begin{bmatrix} G^T \\ z^T \end{bmatrix}^T S \begin{bmatrix} G^T \\ z^T
\end{bmatrix}.$$

**Reading.** Signature Gram identity only uses GGᵀ=A, without triangularity or positivity premise.
-/
theorem equation_6_5_10 {n : ℕ} {A G : Matrix (Fin n) (Fin n) ℝ} (hA : G * Gᵀ = A)
    (z : Fin n → ℝ) :
    A - vecMulVec z z =
      (fromRows Gᵀ (replicateRow Unit z))ᵀ *
        LieAlgebra.Orthogonal.indefiniteDiagonal (Fin n) Unit ℝ *
          fromRows Gᵀ (replicateRow Unit z) := by
  rw [transpose_mul_indefiniteDiagonal_mul_fromRows, transpose_transpose, hA]

/-- **Equation (6.5.11)** of [golub2013matrix]. A matrix $H \in \mathbb{R}^{(n+1) \times (n+1)}$ is
**$S$-orthogonal** if $$H S H^T = S, \qquad S = \operatorname{diag}(I_n, -1).$$

It is `Matrix.IsJOrthogonal` for the signature `LieAlgebra.Orthogonal.indefiniteDiagonal (Fin n)
Unit ℝ`. -/
def IsSOrthogonal {n : ℕ} (H : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ) : Prop :=
  IsJOrthogonal (LieAlgebra.Orthogonal.indefiniteDiagonal (Fin n) Unit ℝ) H

/-- **Section 6.5.4** of [golub2013matrix]. The product of $S$-orthogonal matrices is
$S$-orthogonal. -/
theorem IsSOrthogonal.mul {n : ℕ} {H₁ H₂ : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ}
    (h₁ : IsSOrthogonal H₁) (h₂ : IsSOrthogonal H₂) : IsSOrthogonal (H₁ * H₂) :=
  IsJOrthogonal.mul h₁ h₂

/-- **Equation (6.5.12)** of [golub2013matrix]. Let $G \in \mathbb{R}^{n \times n}$ with $GG^T = A$
and $z \in \mathbb{R}^n$, and let $H \in \mathbb{R}^{(n+1) \times (n+1)}$ be $S$-orthogonal with
$$H^T \begin{bmatrix} G^T \\ z^T \end{bmatrix} = \begin{bmatrix} R \\ 0 \end{bmatrix}.$$ Then
$A - zz^T = R^T R$. If moreover $R$ is upper triangular with nonzero diagonal, and $D =
\operatorname{diag}(\operatorname{sign}(r_{ii}))$, then $DR$ is the upper triangular Cholesky
factor of $A - zz^T$, so the Cholesky factor of $\tilde A = A - zz^T$ is $\tilde G = R^T D$.

**Correction.** The source says that $\tilde G = R^T$ is the Cholesky factor of $\tilde A$. The
diagonal of $R$ can have negative entries, so $R^T$ is the Cholesky factor only after the signs
of its diagonal are normalized. -/
theorem equation_6_5_12 {n : ℕ} {A G R : Matrix (Fin n) (Fin n) ℝ} (hA : G * Gᵀ = A)
    {z : Fin n → ℝ} {H : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ} (hH : IsSOrthogonal H)
    (h : Hᵀ * fromRows Gᵀ (replicateRow Unit z) = fromRows R 0) :
    A - vecMulVec z z = Rᵀ * R ∧
      (R.IsUpperTriangular → (∀ i, R i i ≠ 0) →
        IsCholesky (A - vecMulVec z z) (diagonal (fun i => (SignType.sign (R i i) : ℝ)) * R)) := by
  have e : A - vecMulVec z z = Rᵀ * R := by
    rw [← transpose_mul_self_sub_eq_of_isJOrthogonal hH h, transpose_transpose, hA]
  exact ⟨e, fun hR hd => isCholesky_diagonal_sign_mul hR hd e.symm⟩

/-- **Section 6.5.4** of [golub2013matrix], hyperbolic rotations. For $k \in \{1, \dots, n\}$ and
$\theta \in \mathbb{R}$, let $H_k \in \mathbb{R}^{(n+1) \times (n+1)}$ agree with $I_{n+1}$
except in four entries: $$[H_k]_{kk} = [H_k]_{n+1,n+1} = \cosh(\theta), \qquad [H_k]_{k,n+1} =
[H_k]_{n+1,k} = -\sinh(\theta).$$ Then $H_k$ is $S$-orthogonal.

The source derives this from $\cosh(\theta)^2 - \sinh(\theta)^2 = 1$. The matrix is
`Matrix.hyperbolicRotation (Sum.inl k) (Sum.inr ()) (Real.cosh θ) (Real.sinh θ)`. -/
theorem hyperbolicRotation_isSOrthogonal {n : ℕ} (k : Fin n) (θ : ℝ) :
    IsSOrthogonal (hyperbolicRotation (Sum.inl k) (Sum.inr ()) (Real.cosh θ) (Real.sinh θ)) :=
  isJOrthogonal_hyperbolicRotation Sum.inl_ne_inr (ε := Sum.elim (fun _ => 1) fun _ => -1)
    rfl rfl (by rw [Real.cosh_sq θ]; ring)

/-- **Equation (6.5.13)** of [golub2013matrix]. Let $x_1, x_2 \in \mathbb{R}$ with $|x_1| > |x_2|$,
and let $$\tau = x_2 / x_1, \qquad c = 1 / \sqrt{1 - \tau^2}, \qquad s = c \cdot \tau.$$ Then
$c^2 - s^2 = 1$, and $(c, s) = (\cosh(\theta), \sinh(\theta))$ for
$\theta = \operatorname{arsinh}(s)$. Moreover $$\begin{bmatrix} c & -s \\ -s & c \end{bmatrix}
\begin{bmatrix} x_1 \\ x_2 \end{bmatrix} = \begin{bmatrix} r \\ 0 \end{bmatrix}, \qquad r =
\operatorname{sign}(x_1) \sqrt{x_1^2 - x_2^2}.$$

The pair $(c, s)$ is `Matrix.hyperbolicPair x₁ x₂`. -/
theorem equation_6_5_13 {x₁ x₂ c s : ℝ} (h : |x₂| < |x₁|)
    (hc : c = 1 / √(1 - (x₂ / x₁) ^ 2)) (hs : s = c * (x₂ / x₁)) :
    c ^ 2 - s ^ 2 = 1 ∧ Real.cosh (Real.arsinh s) = c ∧ Real.sinh (Real.arsinh s) = s ∧
      (hyperbolicRotation (0 : Fin 2) 1 c s *ᵥ ![x₁, x₂]) 1 = 0 ∧
      (hyperbolicRotation (0 : Fin 2) 1 c s *ᵥ ![x₁, x₂]) 0 =
        SignType.sign x₁ * √(x₁ ^ 2 - x₂ ^ 2) := by
  have hp : (c, s) = hyperbolicPair x₁ x₂ := by
    rw [hs, hc, hyperbolicPair]
  have hx : |(![x₁, x₂] : Fin 2 → ℝ) 1| < |(![x₁, x₂] : Fin 2 → ℝ) 0| := h
  obtain ⟨hcs, hc0⟩ := hyperbolicPair_sq_sub_sq h
  obtain ⟨h1, h0⟩ := hyperbolicRotation_hyperbolicPair_mulVec (Fin.zero_ne_one) hx
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h1 h0
  rw [← hp] at hcs hc0 h1 h0
  refine ⟨hcs, ?_, Real.sinh_arsinh s, h1, h0⟩
  rw [Real.cosh_arsinh]
  rw [show 1 + s ^ 2 = c ^ 2 by linarith, Real.sqrt_sq hc0.le]

/-- **Section 6.5.4** of [golub2013matrix], nonexistence of a hyperbolic rotation. Let
$x_1, x_2 \in \mathbb{R}$ with $|x_1| \le |x_2|$ and $x_2 \neq 0$. Then there are no real $c, s$
with $c^2 - s^2 = 1$ and $-s x_1 + c x_2 = 0$.

**Generalization.** The source argues from $|\cosh(\theta)| > |\sinh(\theta)|$ that there is no
real solution if $|x_2| > |x_1|$. The statement also covers $|x_2| = |x_1| \neq 0$. -/
theorem hyperbolic_not_exists {x₁ x₂ : ℝ} (h : |x₁| ≤ |x₂|) (hx₂ : x₂ ≠ 0) :
    ¬ ∃ c s : ℝ, c ^ 2 - s ^ 2 = 1 ∧ -s * x₁ + c * x₂ = 0 :=
  not_exists_hyperbolic_of_abs_le h hx₂

/-- **Section 6.5.4** of [golub2013matrix]. Let $A = H^T H$ be a Cholesky factorization of
$A \in \mathbb{R}^{(n+1) \times (n+1)}$ with $H = G^T$ upper triangular, and let
$z \in \mathbb{R}^{n+1}$. If $\tilde A = A - zz^T$ is positive definite, then $$[\tilde
A]_{11} = g_{11}^2 - z_1^2 > 0,$$ and therefore $|z_1| < |g_{11}|$. This guarantees that the
cosh–sinh computations (6.5.13) go through.

The entry $g_{11}$ is the entry $(0, 0)$ of the upper triangular factor $H$, and the
factorization is `Matrix.IsCholesky A H`. -/
theorem abs_lt_of_posDef_sub {n : ℕ} {A H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hH : IsCholesky A H) {z : Fin (n + 1) → ℝ} (hA : (A - vecMulVec z z).PosDef) :
    (A - vecMulVec z z) 0 0 = H 0 0 ^ 2 - z 0 ^ 2 ∧ 0 < H 0 0 ^ 2 - z 0 ^ 2 ∧
      |z 0| < |H 0 0| := by
  have h00 : A 0 0 = H 0 0 ^ 2 := by
    rw [hH.apply_eq_sum 0 0]
    simp [Finset.filter_eq', sq]
  have e : (A - vecMulVec z z) 0 0 = H 0 0 ^ 2 - z 0 ^ 2 := by
    rw [Matrix.sub_apply, vecMulVec_apply, h00]
    ring
  have hpos : 0 < H 0 0 ^ 2 - z 0 ^ 2 := e ▸ hA.diag_pos
  exact ⟨e, hpos, sq_lt_sq.1 (by linarith)⟩

/-- **Theorem 6.5.1** of [golub2013matrix]. Let $$A = \begin{bmatrix} \alpha & v^T \\ v & B
\end{bmatrix} = \begin{bmatrix} g_{11} & 0 \\ g_1 & G_1 \end{bmatrix} \begin{bmatrix} g_{11} &
g_1^T \\ 0 & G_1^T \end{bmatrix}$$ be a Cholesky factorization of
$A \in \mathbb{R}^{(n+1) \times (n+1)}$, let $z = [\mu; w] \in \mathbb{R}^{n+1}$, and assume
that $\tilde A = A - zz^T$ is positive definite. Then there are $\theta \in \mathbb{R}$,
$c = \cosh(\theta)$ and $s = \sinh(\theta)$ such that $$\begin{bmatrix} c & 0 & -s \\ 0 & I_n &
0 \\ -s & 0 & c \end{bmatrix} \begin{bmatrix} g_{11} & g_1^T \\ 0 & G_1^T \\ \mu & w^T
\end{bmatrix} = \begin{bmatrix} \tilde g_{11} & \tilde g_1^T \\ 0 & G_1^T \\ 0 & w_1^T
\end{bmatrix}$$ for some $\tilde g_{11}$, $\tilde g_1$ and $w_1$. Moreover, the matrix
$\tilde A_1 = G_1 G_1^T - w_1 w_1^T$ is positive definite.

**Typo.** The proof calls $\tilde A_1$ the Schur complement of $\alpha$ in $\tilde A$. The pivot
is its $(1,1)$ entry, $\alpha - \mu^2$, as the displayed block matrix for $\tilde A$ shows.

The factorization is `Matrix.IsCholesky A H` with $H = [g_{11}\ g_1^T; 0\ G_1^T]$ indexed by
`Fin (n + 1)`, where the first index carries $\alpha$, $g_{11}$ and $\mu$. The rotated stacked
matrix is $[R'; z'^T]$, where $R'$ equals $H$ off its first row, $z'_1 = 0$, and $w_1$ is the
rest of $z'$. The theorem is `Matrix.hyperbolicDowndate_step`. -/
theorem theorem_6_5_1 {n : ℕ} {A H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hH : IsCholesky A H) {z : Fin (n + 1) → ℝ} (hA : (A - vecMulVec z z).PosDef) :
    ∃ θ : ℝ, ∃ (R' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (z' : Fin (n + 1) → ℝ),
      hyperbolicRotation (Sum.inl (0 : Fin (n + 1))) (Sum.inr ()) (Real.cosh θ) (Real.sinh θ) *
          fromRows H (replicateRow Unit z) = fromRows R' (replicateRow Unit z') ∧
        z' 0 = 0 ∧ (∀ i, i ≠ 0 → R' i = H i) ∧
        ((H.submatrix Fin.succ Fin.succ)ᵀ * H.submatrix Fin.succ Fin.succ -
          vecMulVec (fun j : Fin n => z' j.succ) (fun j : Fin n => z' j.succ)).PosDef := by
  obtain ⟨hlt, hcs, R', z', e, hz0, -, hR', -, hpd⟩ :=
    hyperbolicDowndate_step hH hA (c := √(A 0 0) / √(A 0 0 - z 0 ^ 2))
      (s := z 0 / √(A 0 0 - z 0 ^ 2)) rfl rfl
  set c := √(A 0 0) / √(A 0 0 - z 0 ^ 2) with hc
  set s := z 0 / √(A 0 0 - z 0 ^ 2) with hs
  have hc0 : 0 < c := by
    have : 0 < A 0 0 := lt_of_le_of_lt (sq_nonneg _) hlt
    rw [hc]
    exact div_pos (Real.sqrt_pos.2 this) (Real.sqrt_pos.2 (by linarith))
  have hcosh : Real.cosh (Real.arsinh s) = c := by
    rw [Real.cosh_arsinh, show 1 + s ^ 2 = c ^ 2 by linarith, Real.sqrt_sq hc0.le]
  refine ⟨Real.arsinh s, R', z', ?_, hz0, hR', hpd⟩
  rw [hcosh, Real.sinh_arsinh]
  exact e

/-- **Equation (6.5.14)** of [golub2013matrix]. Let $$A = \begin{bmatrix} \alpha & v^T \\ v & B
\end{bmatrix} \in \mathbb{R}^{(n+1) \times (n+1)}$$ have the Cholesky factorization $A = H^T H$
with $H = [g_{11}\ g_1^T; 0\ G_1^T]$ upper triangular with positive diagonal. Then the blocks of
the Cholesky factor are $$g_{11} = \sqrt{\alpha}, \qquad g_1 = v / g_{11}, \qquad G_1 G_1^T =
B - \frac{1}{\alpha} v v^T.$$

The factorization is `Matrix.IsCholesky A H`. -/
theorem equation_6_5_14 {n : ℕ} {A H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hH : IsCholesky A H) :
    H 0 0 = √(A 0 0) ∧ (∀ j : Fin n, H 0 j.succ = A j.succ 0 / H 0 0) ∧
      (H.submatrix Fin.succ Fin.succ)ᵀ * H.submatrix Fin.succ Fin.succ =
        A.submatrix Fin.succ Fin.succ -
          (1 / A 0 0) • vecMulVec (fun j : Fin n => A j.succ 0) (fun j : Fin n => A j.succ 0) := by
  have hA : Hᵀ * H = A := by
    rw [← conjTranspose_eq_transpose_of_trivial, hH.conjTranspose_mul_self]
  have hcol : ∀ i : Fin n, H i.succ 0 = 0 := fun i => hH.isUpperTriangular (Fin.succ_pos i)
  have hent : ∀ i j, A i j = H 0 i * H 0 j + ∑ k : Fin n, H k.succ i * H k.succ j := by
    intro i j
    rw [← hA, Matrix.mul_apply, Fin.sum_univ_succ]
    rfl
  have h00 : A 0 0 = H 0 0 ^ 2 := by
    rw [hent]
    simp [hcol, sq]
  have hH0 := hH.diag_pos 0
  have hv : ∀ j : Fin n, A j.succ 0 = H 0 0 * H 0 j.succ := fun j => by
    rw [hent]
    simp [hcol, mul_comm]
  refine ⟨by rw [h00, Real.sqrt_sq hH0.le], fun j => ?_, ?_⟩
  · rw [hv, mul_div_cancel_left₀ _ hH0.ne']
  · ext i j
    have e1 : ((H.submatrix Fin.succ Fin.succ)ᵀ * H.submatrix Fin.succ Fin.succ) i j =
        ∑ k : Fin n, H k.succ i.succ * H k.succ j.succ := by
      simp [Matrix.mul_apply]
    rw [e1, Matrix.sub_apply, Matrix.smul_apply, submatrix_apply, vecMulVec_apply,
      hent i.succ j.succ, hv i, hv j, h00, smul_eq_mul]
    field_simp
    ring

/-- **Equation (6.5.15)** of [golub2013matrix]. Let $A = [\alpha\ v^T; v\ B] = H^T H$ be a Cholesky
factorization as in Theorem 6.5.1, with first row $[g_{11}\ g_1^T]$ of $H$, and let
$z = [\mu; w] \in \mathbb{R}^{n+1}$ with $A - zz^T$ positive definite. Then the pair (6.5.13)
for $x_1 = g_{11}$, $x_2 = \mu$ is $$c = \frac{\sqrt{\alpha}}{\sqrt{\alpha - \mu^2}}, \qquad s =
\frac{\mu}{\sqrt{\alpha - \mu^2}}.$$ The rotation zeroes $\mu$, that is,
$-s g_{11} + c \mu = 0$, and it produces the new last row $[0\ w_1^T]$ with $$w_1 = -s g_1 + c
w.$$

The source derives the formulas from $a_{11} - z_1^2 = g_{11}^2 - \mu^2 > 0$, which is
`GolubVanLoan.Chapter06.abs_lt_of_posDef_sub`. The pair is
`Matrix.hyperbolicPair (H 0 0) (z 0)`, and the rotation is `Matrix.hyperbolicRotation` in the
planes of the first row of $H$ and the row $z^T$. -/
theorem equation_6_5_15 {n : ℕ} {A H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hH : IsCholesky A H) {z : Fin (n + 1) → ℝ} (hA : (A - vecMulVec z z).PosDef) :
    hyperbolicPair (H 0 0) (z 0) =
        (√(A 0 0) / √(A 0 0 - z 0 ^ 2), z 0 / √(A 0 0 - z 0 ^ 2)) ∧
      -(z 0 / √(A 0 0 - z 0 ^ 2)) * H 0 0 + √(A 0 0) / √(A 0 0 - z 0 ^ 2) * z 0 = 0 ∧
      ∃ (R' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (z' : Fin (n + 1) → ℝ),
        hyperbolicRotation (Sum.inl (0 : Fin (n + 1))) (Sum.inr ())
            (√(A 0 0) / √(A 0 0 - z 0 ^ 2)) (z 0 / √(A 0 0 - z 0 ^ 2)) *
          fromRows H (replicateRow Unit z) = fromRows R' (replicateRow Unit z') ∧
        z' 0 = 0 ∧ ∀ j : Fin n, z' j.succ =
          -(z 0 / √(A 0 0 - z 0 ^ 2)) * H 0 j.succ + √(A 0 0) / √(A 0 0 - z 0 ^ 2) * z j.succ := by
  obtain ⟨hlt, -, R', z', e, hz0, -, -, hw, -⟩ :=
    hyperbolicDowndate_step hH hA (c := √(A 0 0) / √(A 0 0 - z 0 ^ 2))
      (s := z 0 / √(A 0 0 - z 0 ^ 2)) rfl rfl
  obtain ⟨hg, -, -⟩ := equation_6_5_14 hH
  have hH0 := hH.diag_pos 0
  have hd : 0 < A 0 0 - z 0 ^ 2 := by linarith
  have hsq : √(A 0 0) ^ 2 = A 0 0 := Real.sq_sqrt (by nlinarith [sq_nonneg (z 0)])
  have hdd : √(A 0 0 - z 0 ^ 2) ^ 2 = A 0 0 - z 0 ^ 2 := Real.sq_sqrt hd.le
  have hd0 : 0 < √(A 0 0 - z 0 ^ 2) := Real.sqrt_pos.2 hd
  have hA0 : A 0 0 ≠ 0 := by nlinarith [sq_nonneg (z 0)]
  have hroot : √(1 - (z 0 / H 0 0) ^ 2) = √(A 0 0 - z 0 ^ 2) / √(A 0 0) := by
    rw [hg, show 1 - (z 0 / √(A 0 0)) ^ 2 = (√(A 0 0 - z 0 ^ 2) / √(A 0 0)) ^ 2 by
      rw [div_pow, div_pow, hsq, hdd, sub_div, div_self hA0], Real.sqrt_sq (by positivity)]
  refine ⟨?_, ?_, R', z', e, hz0, hw⟩
  · rw [hyperbolicPair, hroot, ← hg]
    have : H 0 0 ≠ 0 := hH0.ne'
    ext
    · simp only
      field_simp
    · simp only
      field_simp
  · rw [hg]
    field_simp
    ring

/-- **Section 6.5.4** of [golub2013matrix], existence of the factorization (6.5.12). Let $A = GG^T$
be a Cholesky factorization of $A \in \mathbb{R}^{n \times n}$, and let $z \in \mathbb{R}^n$
with $A - zz^T$ positive definite. Then there are numbers $c_k, s_k$ with $c_k^2 - s_k^2 = 1$
for $k = 1, \dots, n$, such that the hyperbolic rotations $H_k$ in the planes $(k, n + 1)$ have
an $S$-orthogonal product $H = H_1 \cdots H_n$ with $$H^T \begin{bmatrix} G^T \\ z^T
\end{bmatrix} = \begin{bmatrix} R \\ 0 \end{bmatrix},$$ where $R$ is upper triangular and is the
upper triangular Cholesky factor of $A - zz^T$.

The source says that Theorem 6.5.1 is the key step in an induction proof of this fact. The
hypothesis $A = GG^T$ is `Matrix.IsCholesky A Gᵀ`. -/
theorem choleskyDowndate_exists {n : ℕ} {A G : Matrix (Fin n) (Fin n) ℝ} (hG : IsCholesky A Gᵀ)
    {z : Fin n → ℝ} (hA : (A - vecMulVec z z).PosDef) :
    ∃ c s : Fin n → ℝ, (∀ k, c k ^ 2 - s k ^ 2 = 1) ∧ ∃ R : Matrix (Fin n) (Fin n) ℝ,
      IsSOrthogonal
        (List.ofFn fun k => hyperbolicRotation (Sum.inl k) (Sum.inr ()) (c k) (s k)).prod ∧
      (List.ofFn fun k => hyperbolicRotation (Sum.inl k) (Sum.inr ()) (c k) (s k)).prodᵀ *
        fromRows Gᵀ (replicateRow Unit z) = fromRows R 0 ∧
      R.IsUpperTriangular ∧ IsCholesky (A - vecMulVec z z) R := by
  obtain ⟨c, s, hcs, R, hJ, h, hR⟩ := exists_choleskyDowndate hG hA
  exact ⟨c, s, hcs, R, hJ, h, hR.isUpperTriangular, hR⟩

/-! ### §6.5.4 The downdating procedure -/

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- **Section 6.5.4** of [golub2013matrix], Cholesky downdating with hyperbolic rotations. Given a
Cholesky factorization $A = GG^T$ and a vector $z \in \mathbb{R}^n$, the program computes the
Cholesky factorization $\tilde A = \tilde G \tilde G^T$ of $\tilde A = A - zz^T$. It applies to
the stacked matrix $[G^T; z^T]$ the hyperbolic rotations $H_k$ in the planes $(k, n + 1)$, for
$k = 1, \dots, n$. Each is computed by (6.5.13), $$\tau = x_2 / x_1, \qquad c = 1 / \sqrt{1 -
\tau^2}, \qquad s = c \tau,$$ where $x_1$ and $x_2$ are the current entries $(k, k)$ and
$(n + 1, k)$. The output is $\tilde G = R^T$ for the triangular block $R$ of the result.

Every arithmetic result is rounded, and $\sqrt{\cdot}$ is `Real.sqrt` followed by one rounding.
The rotations are applied by `GolubVanLoan.Chapter05.hyperbolicApplyLeft`.

**Typo.** The prose before Theorem 6.5.1 writes the stack of the factor and update vector as
$[G^T\mid z]^T$. The sweep uses the stacked matrix $[G^T;z^T]$ from (6.5.12). -/
noncomputable def choleskyDowndate {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ) (z : Fin n → ℝ) :
    M (Matrix (Fin n) (Fin n) ℝ) := do
  let S ← (List.finRange n).foldlM (fun (S : Matrix (Fin n ⊕ Unit) (Fin n) ℝ) (k : Fin n) => do
      let τ ← rnd (S (Sum.inr ()) k / S (Sum.inl k) k)
      let c ← rnd (1 / (← rnd (√(← rnd (1 - (← rnd (τ * τ)))))))
      let s ← rnd (c * τ)
      Chapter05.hyperbolicApplyLeft rnd (Sum.inl k) (Sum.inr ()) c s (List.finRange n) S)
    (fromRows Gᵀ (replicateRow Unit z))
  pure (S.toRows₁)ᵀ

end Programs

/-- In exact arithmetic, one step of `GolubVanLoan.Chapter06.choleskyDowndate` multiplies the
current matrix on the left by the hyperbolic rotation in the planes $(k, n + 1)$ with the pair
(6.5.13) of its entries $(k, k)$ and $(n + 1, k)$. -/
private theorem choleskyDowndate_step_run {n : ℕ} (k : Fin n)
    (S : Matrix (Fin n ⊕ Unit) (Fin n) ℝ) :
    Id.run (do
      let τ ← pure (S (Sum.inr ()) k / S (Sum.inl k) k)
      let c ← pure (1 / (← pure (√(← pure (1 - (← pure (τ * τ)))))))
      let s ← pure (c * τ)
      Chapter05.hyperbolicApplyLeft (pure : ℝ → Id ℝ) (Sum.inl k) (Sum.inr ()) c s
        (List.finRange n) S) =
      hyperbolicRotation (Sum.inl k) (Sum.inr ())
        (hyperbolicPair (S (Sum.inl k) k) (S (Sum.inr ()) k)).1
        (hyperbolicPair (S (Sum.inl k) k) (S (Sum.inr ()) k)).2 * S := by
  have hp : hyperbolicPair (S (Sum.inl k) k) (S (Sum.inr ()) k) =
      (1 / √(1 - S (Sum.inr ()) k / S (Sum.inl k) k * (S (Sum.inr ()) k / S (Sum.inl k) k)),
        1 / √(1 - S (Sum.inr ()) k / S (Sum.inl k) k * (S (Sum.inr ()) k / S (Sum.inl k) k)) *
          (S (Sum.inr ()) k / S (Sum.inl k) k)) := by
    rw [hyperbolicPair, sq]
  have hspec := Chapter05.hyperbolicApplyLeft_spec
    (Sum.inl_ne_inr : (Sum.inl k : Fin n ⊕ Unit) ≠ Sum.inr ())
    (1 / √(1 - S (Sum.inr ()) k / S (Sum.inl k) k * (S (Sum.inr ()) k / S (Sum.inl k) k)))
    (1 / √(1 - S (Sum.inr ()) k / S (Sum.inl k) k * (S (Sum.inr ()) k / S (Sum.inl k) k)) *
      (S (Sum.inr ()) k / S (Sum.inl k) k)) (List.nodup_finRange n) S
  simp only [List.mem_finRange, ite_true] at hspec
  rw [hp]
  exact hspec

/-- In exact arithmetic, the downdating sweep of `GolubVanLoan.Chapter06.choleskyDowndate` is a left
fold of multiplications by hyperbolic rotations. -/
private theorem choleskyDowndate_fold_run {n : ℕ} (l : List (Fin n))
    (S : Matrix (Fin n ⊕ Unit) (Fin n) ℝ) :
    Id.run (l.foldlM (fun (S : Matrix (Fin n ⊕ Unit) (Fin n) ℝ) (k : Fin n) => do
      let τ ← pure (S (Sum.inr ()) k / S (Sum.inl k) k)
      let c ← pure (1 / (← pure (√(← pure (1 - (← pure (τ * τ)))))))
      let s ← pure (c * τ)
      Chapter05.hyperbolicApplyLeft (pure : ℝ → Id ℝ) (Sum.inl k) (Sum.inr ()) c s
        (List.finRange n) S) S) =
      l.foldl (fun S k => hyperbolicRotation (Sum.inl k) (Sum.inr ())
        (hyperbolicPair (S (Sum.inl k) k) (S (Sum.inr ()) k)).1
        (hyperbolicPair (S (Sum.inl k) k) (S (Sum.inr ()) k)).2 * S) S := by
  induction l generalizing S with
  | nil => rfl
  | cons k l ih =>
    rw [List.foldl_cons, ← choleskyDowndate_step_run, ← ih]
    rfl

/-- **Section 6.5.4** of [golub2013matrix], correctness of the downdate in exact arithmetic. Let
$A = GG^T$ be a Cholesky factorization of $A \in \mathbb{R}^{n \times n}$, and let
$z \in \mathbb{R}^n$ with $\tilde A = A - zz^T$ positive definite. Then the output $\tilde G$ of
`GolubVanLoan.Chapter06.choleskyDowndate` is the Cholesky factor of $\tilde A$: $\tilde G$ is
lower triangular with positive diagonal and $\tilde G \tilde G^T = \tilde A$.

The run is at `M := Id` with `rnd := pure`, and the conclusion is
`Matrix.IsCholesky (A - zzᵀ) G̃ᵀ`. At step $k$ the current matrix $[R; z'^T]$ satisfies
$R^T R - z' z'^T = \tilde A$, because the rotations are $S$-orthogonal. So $|z'_k| < r_{kk}$ and
the pair (6.5.13) exists, as in the proof of Theorem 6.5.1. The new diagonal entry
$\sqrt{r_{kk}^2 - z_k'^2}$ is positive, so no normalization of signs is needed. -/
theorem choleskyDowndate_spec {n : ℕ} {A G : Matrix (Fin n) (Fin n) ℝ} (hG : IsCholesky A Gᵀ)
    {z : Fin n → ℝ} (hA : (A - vecMulVec z z).PosDef) :
    IsCholesky (A - vecMulVec z z) (Id.run (choleskyDowndate pure G z))ᵀ := by
  have hne : ∀ k : Fin n, (Sum.inl k : Fin n ⊕ Unit) ≠ Sum.inr () := fun _ => Sum.inl_ne_inr
  set F : Matrix (Fin n ⊕ Unit) (Fin n) ℝ → Fin n → Matrix (Fin n ⊕ Unit) (Fin n) ℝ :=
    fun S k => hyperbolicRotation (Sum.inl k) (Sum.inr ())
      (hyperbolicPair (S (Sum.inl k) k) (S (Sum.inr ()) k)).1
      (hyperbolicPair (S (Sum.inl k) k) (S (Sum.inr ()) k)).2 * S with hF
  set Inv : ℕ → Matrix (Fin n ⊕ Unit) (Fin n) ℝ → Prop := fun t S =>
    ∃ (R : Matrix (Fin n) (Fin n) ℝ) (z' : Fin n → ℝ),
      S = fromRows R (replicateRow Unit z') ∧ R.IsUpperTriangular ∧ (∀ i, 0 < R i i) ∧
        (∀ j : Fin n, (j : ℕ) < t → z' j = 0) ∧ Rᵀ * R - vecMulVec z' z' = A - vecMulVec z z
    with hInv
  have hGG : Gᵀᵀ * Gᵀ = A := by
    rw [← conjTranspose_eq_transpose_of_trivial Gᵀ, hG.conjTranspose_mul_self]
  have hstep : ∀ t (ht : t < n) S, Inv t S → Inv (t + 1) (F S ⟨t, ht⟩) := by
    rintro t ht S ⟨R, z', rfl, hRt, hRd, hz', hGr⟩
    set k : Fin n := ⟨t, ht⟩ with hk
    have hlt : |z' k| < |R k k| := by
      rw [← sq_lt_sq]
      exact Matrix.sq_lt_sq_of_posDef_transpose_mul_self_sub hRt hRd (fun j hj => hz' j hj)
        (hGr ▸ hA)
    set x : Fin n ⊕ Unit → ℝ := fun r => fromRows R (replicateRow Unit z') r k with hx
    have hxi : x (Sum.inl k) = R k k := rfl
    have hxr : x (Sum.inr ()) = z' k := rfl
    have hxk : |x (Sum.inr ())| < |x (Sum.inl k)| := by rwa [hxi, hxr]
    obtain ⟨p, hp⟩ : ∃ p, p = hyperbolicPair (x (Sum.inl k)) (x (Sum.inr ())) := ⟨_, rfl⟩
    obtain ⟨hcs, -⟩ := hyperbolicPair_sq_sub_sq hxk
    obtain ⟨hzero, hdiag⟩ := hyperbolicRotation_hyperbolicPair_mulVec (hne k) hxk
    rw [← hp] at hcs hzero hdiag
    have hFS : F (fromRows R (replicateRow Unit z')) k =
        hyperbolicRotation (Sum.inl k) (Sum.inr ()) p.1 p.2 *
          fromRows R (replicateRow Unit z') := by
      rw [hF, hp]
    obtain ⟨R', z'', e, hR't, hz'', hR'i, -, -⟩ :=
      fromRows_rotate_step hRt (k := k) (fun j hj => hz' j hj) !![p.1, -p.2; -p.2, p.1]
    have e' : hyperbolicRotation (Sum.inl k) (Sum.inr ()) p.1 p.2 *
        fromRows R (replicateRow Unit z') = fromRows R' (replicateRow Unit z'') := e
    have hcol : ∀ i, fromRows R' (replicateRow Unit z'') i k =
        (hyperbolicRotation (Sum.inl k) (Sum.inr ()) p.1 p.2 *ᵥ x) i := fun i => by
      rw [← e']
      rfl
    refine ⟨R', z'', hFS.trans e', hR't, fun i => ?_, fun j hj => ?_, ?_⟩
    · by_cases hik : i = k
      · rw [hik]
        have h1 := hcol (Sum.inl k)
        rw [hdiag, fromRows_apply_inl, hxi, hxr, sign_pos (hRd k), SignType.coe_one,
          one_mul] at h1
        rw [h1]
        have h2 := hlt
        rw [abs_of_pos (hRd k)] at h2
        exact Real.sqrt_pos.2 (by nlinarith [abs_lt.1 h2])
      · rw [hR'i i hik]
        exact hRd i
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
      · exact hz'' j hj
      · obtain rfl : j = k := Fin.ext hj
        have h1 := hcol (Sum.inr ())
        rw [hzero, fromRows_apply_inr] at h1
        simpa using h1
    · rw [← hGr]
      exact (transpose_mul_self_sub_eq_of_isJOrthogonal_of_fromRows
        (isJOrthogonal_hyperbolicRotation (hne k) (ε := Sum.elim (fun _ => 1) fun _ => -1)
          rfl rfl hcs)
        (by rw [hyperbolicRotation_transpose (hne k)]; exact e')).symm
  have hpre := List.foldl_finRange_induction Inv (f := F)
    (init := fromRows Gᵀ (replicateRow Unit z))
    ⟨Gᵀ, z, rfl, hG.isUpperTriangular, hG.diag_pos, fun _ h => absurd h (Nat.not_lt_zero _),
      by rw [hGG]⟩ fun k S hS => hstep k k.isLt S hS
  have hrun : Id.run (choleskyDowndate pure G z) =
      ((List.finRange n).foldl F (fromRows Gᵀ (replicateRow Unit z))).toRows₁ᵀ := by
    change (Id.run ((List.finRange n).foldlM _ (fromRows Gᵀ (replicateRow Unit z)))).toRows₁ᵀ = _
    rw [choleskyDowndate_fold_run]
  obtain ⟨R, z', hS, hRt, hRd, hz', hGr⟩ := hpre
  have hz0 : z' = 0 := funext fun j => hz' j j.isLt
  subst hz0
  rw [vecMulVec_zero, sub_zero] at hGr
  rw [hrun, hS, toRows₁_fromRows, transpose_transpose]
  exact ⟨hRt, hRd, by rw [conjTranspose_eq_transpose_of_trivial, hGr]⟩

/-! ### §6.5.1–6.5.4 The Givens updating procedures -/

section GivensPrograms

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- **Section 6.5.1** of [golub2013matrix], the rank-one QR update. Given a QR factorization
$A = QR$ of $A \in \mathbb{R}^{n \times n}$ and $u, v \in \mathbb{R}^n$, the program computes a
QR factorization $\tilde A = A + uv^T = Q_1 R_1$. It computes $w = Q^T u$ by a gaxpy (Algorithm
1.1.3). It then computes the rotations $J_{n-1}, \dots, J_1$ that reduce $w$ to
$\pm\|w\|_2 e_1$, applies them to $R$ and accumulates them into $Q$; this leaves an upper
Hessenberg $H$. It forms $H_1 = H \pm \|w\|_2 e_1 v^T$ by a saxpy on the first row (Algorithm
1.1.2), and finally computes the rotations $G_1, \dots, G_{n-1}$ that triangularize $H_1$. The
output is $(Q_1, R_1)$ with $Q_1 = Q J_{n-1} \cdots J_1 G_1 \cdots G_{n-1}$.

**Typo.** The source says "Following Algorithm 5.2.4" for the second sweep. It means Algorithm
5.2.5, the QR factorization of an upper Hessenberg matrix.

The first sweep is `GolubVanLoan.Chapter05.givensVectorSweep`, and the second is
`GolubVanLoan.Chapter05.givensHessenbergSweep`. -/
noncomputable def qrUpdateRankOne {n : ℕ} (Q R : Matrix (Fin n) (Fin n) ℝ) (u v : Fin n → ℝ) :
    M (Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ) := do
  let w ← Chapter01.algorithm_1_1_3 rnd Qᵀ u 0
  let st ← Chapter05.givensVectorSweep rnd 0 (n - 1) w Q R
  let H ← if h : 0 < n then do
      let r ← Chapter01.algorithm_1_1_2 rnd (st.1 ⟨0, h⟩) v (st.2.2 ⟨0, h⟩)
      pure (st.2.2.updateRow ⟨0, h⟩ r)
    else pure st.2.2
  Chapter05.givensHessenbergSweep rnd 0 (n - 1) st.2.1 H

/-- **Section 6.5.2** of [golub2013matrix], deleting a column. Given a QR factorization $A = QR$ of
$A \in \mathbb{R}^{m \times (n+1)}$ and a column index $k$ (0-based), let $\tilde A$ be $A$ with
its column $k$ deleted. Then $Q^T \tilde A = H$ is $R$ with its column $k$ deleted, which is
upper Hessenberg. The program zeroes the unwanted subdiagonal entries by a sequence of Givens
rotations, $G_{n-1}^T \cdots G_k^T H = R_1$, and returns $(Q_1, R_1)$ with
$Q_1 = Q G_k \cdots G_{n-1}$, a QR factorization of $\tilde A$.

Forming $H$ needs no arithmetic. The sweep is `GolubVanLoan.Chapter05.givensHessenbergSweep`
from column $k$.

**Generalization.** The program also handles wide upper trapezoidal factors, stopping rotations
when either adjacent row is absent. -/
noncomputable def qrDeleteColumn {m n : ℕ} (Q : Matrix (Fin m) (Fin m) ℝ)
    (R : Matrix (Fin m) (Fin (n + 1)) ℝ) (k : Fin (n + 1)) :
    M (Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin n) ℝ) :=
  Chapter05.givensHessenbergSweep rnd k (n - k) Q (R.submatrix id k.succAbove)

/-- **Section 6.5.2** of [golub2013matrix], appending a column. Given a QR factorization $A = QR$ of
$A \in \mathbb{R}^{m \times n}$, a vector $z \in \mathbb{R}^m$ and a column index $k$ (0-based),
let $\tilde A$ be $A$ with $z$ inserted as its column $k$. With $w = Q^T z$, the matrix $$Q^T
\tilde A = [Q^T a_1 \mid \dots \mid Q^T a_k \mid w \mid Q^T a_{k+1} \mid \dots]$$ is upper
triangular except for a "spike" in column $k$. The program computes $w$ by Algorithm 1.1.3,
inserts it into $R$ as column $k$ to obtain $H$, and then, for $j = m - 2, \dots, k$, computes
$[c, s] = \operatorname{givens}(H(j, k), H(j + 1, k))$ to zero $H(j + 1, k)$, rotates the rows
$j$ and $j + 1$ of $H$, and accumulates the rotation into $Q$.

These rotations are the $J_{m-1}, \dots, J_{k+1}$ of the source.

**Generalization.** The insertion index can be the first position, and the input factor can be
wide. The source illustrates insertion after the $k$-th column in a tall factor. -/
noncomputable def qrInsertColumn {m n : ℕ} (Q : Matrix (Fin m) (Fin m) ℝ)
    (R : Matrix (Fin m) (Fin n) ℝ) (z : Fin m → ℝ) (k : Fin (n + 1)) :
    M (Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin (n + 1)) ℝ) := do
  let w ← Chapter01.algorithm_1_1_3 rnd Qᵀ z 0
  (List.range' k (m - 1 - k)).reverse.foldlM
    (fun (st : Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin (n + 1)) ℝ) (j : ℕ) =>
      if h : j + 1 < m then do
        let cs ← Chapter05.algorithm_5_1_3 rnd (st.2 ⟨j, by omega⟩ k) (st.2 ⟨j + 1, h⟩ k)
        let H ← Chapter05.givensApplyLeft rnd ⟨j, by omega⟩ ⟨j + 1, h⟩ cs.1 cs.2
          (List.finRange (n + 1)) st.2
        let Q ← Chapter05.givensApplyRight rnd ⟨j, by omega⟩ ⟨j + 1, h⟩ cs.1 cs.2
          (List.finRange m) st.1
        pure (Q, H)
      else pure st) (Q, of fun i => k.insertNth (w i) (R i))

/-- **Section 6.5.3** of [golub2013matrix], inserting a row. Given a QR factorization $A = QR$ of
$A \in \mathbb{R}^{m \times n}$, a vector $w \in \mathbb{R}^n$ and a row index $k$ (0-based),
let $\tilde A$ be $A$ with $w^T$ inserted as its row $k$. For $k = 0$, $$\operatorname{diag}(1,
Q^T)\, \tilde A = \begin{bmatrix} w^T \\ R \end{bmatrix} = H$$ is upper Hessenberg, so rotations
$J_1, \dots, J_n$ can be determined with $J_n^T \cdots J_1^T H = R_1$ upper triangular. Then
$\tilde A = Q_1 R_1$ with $Q_1 = \operatorname{diag}(1, Q) J_1 \cdots J_n$ (see Algorithm
5.2.5). For other $k$ the source notes that no essential complications result, through a
permutation $P$.

The starting orthogonal factor is $P^T \operatorname{diag}(1, Q)$: the rows of
`Matrix.consDiag 1 Q` are permuted by `Fin.cycleRange k`, which needs no arithmetic. The sweep
is `GolubVanLoan.Chapter05.givensHessenbergSweep`. -/
noncomputable def qrInsertRow {m n : ℕ} (Q : Matrix (Fin m) (Fin m) ℝ)
    (R : Matrix (Fin m) (Fin n) ℝ) (w : Fin n → ℝ) (k : Fin (m + 1)) :
    M (Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ × Matrix (Fin (m + 1)) (Fin n) ℝ) :=
  Chapter05.givensHessenbergSweep rnd 0 n ((consDiag 1 Q).submatrix k.cycleRange id)
    (of (Fin.cons w R))

/-- **Section 6.5.3** of [golub2013matrix], deleting the first row. Given a QR factorization
$A = QR$ of $A \in \mathbb{R}^{(m+1) \times n}$, let $q^T$ be the first row of $Q$. The program
computes Givens rotations $G_1, \dots, G_m$ with $G_1^T \cdots G_m^T q = \alpha e_1$, where
$\alpha = \pm 1$. Then $$H = G_1^T \cdots G_m^T R = \begin{bmatrix} v^T \\ R_1 \end{bmatrix}$$
is upper Hessenberg and $Q G_m \cdots G_1 = \operatorname{diag}(\alpha, Q_1)$. The program
returns $(Q_1, R_1)$.

In the source, $A$ has $m$ rows and the rotations are $G_1, \dots, G_{m-1}$. The sweep is
`GolubVanLoan.Chapter05.givensVectorSweep` driven by $q$. -/
noncomputable def qrDeleteFirstRow {m n : ℕ} (Q : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (R : Matrix (Fin (m + 1)) (Fin n) ℝ) :
    M (Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin n) ℝ) := do
  let st ← Chapter05.givensVectorSweep rnd 0 m (Q 0) Q R
  pure (st.2.1.submatrix Fin.succ Fin.succ, st.2.2.submatrix Fin.succ id)

/-- **Section 6.5.4** of [golub2013matrix], Cholesky updating. Given a Cholesky factorization
$A = GG^T$ and $z \in \mathbb{R}^n$, the program computes a factor $\tilde G$ with
$\tilde G \tilde G^T = A + zz^T$. It computes Givens rotations $Q = Q_1 \cdots Q_n$ with
$Q^T [G^T; z^T] = [R; 0]$, where the update by $Q_k$ involves only the rows $k$ and $n + 1$: for
$k = 1, \dots, n$ it computes $[c, s] = \operatorname{givens}(M(k, k), M(n + 1, k))$ by
Algorithm 5.1.3 and rotates the rows $k$ and $n + 1$ of the current stacked matrix $M$. The
output is $\tilde G = R^T$, the transpose of the first $n$ rows of $M$.

The stacked matrix has the rows `Fin (n + 1)`, and the rotation is
`GolubVanLoan.Chapter05.givensApplyLeft`. -/
noncomputable def choleskyUpdate {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ) (z : Fin n → ℝ) :
    M (Matrix (Fin n) (Fin n) ℝ) := do
  let S ← (List.finRange n).foldlM (fun (S : Matrix (Fin (n + 1)) (Fin n) ℝ) (k : Fin n) => do
      let cs ← Chapter05.algorithm_5_1_3 rnd (S k.castSucc k) (S (Fin.last n) k)
      Chapter05.givensApplyLeft rnd k.castSucc (Fin.last n) cs.1 cs.2 (List.finRange n) S)
    (of fun i => Fin.lastCases (motive := fun _ => Fin n → ℝ) z (fun i => Gᵀ i) i)
  pure (S.submatrix Fin.castSucc id)ᵀ

end GivensPrograms

/-! ### Correctness of the procedures -/

/-- **Section 6.5.1** of [golub2013matrix], correctness of the rank-one update in exact arithmetic.
If $A = QR$ is a QR factorization of $A \in \mathbb{R}^{n \times n}$ and
$u, v \in \mathbb{R}^n$, then the output $(Q_1, R_1)$ of
`GolubVanLoan.Chapter06.qrUpdateRankOne` is a QR factorization of $A + uv^T$.

The run is at `M := Id` with `rnd := pure`. The first sweep keeps $QR = A$, leaves $H$ upper
Hessenberg and reduces $w$ to its first entry (6.5.2). So $QH_1 = A + uv^T$ with $H_1$ still
upper Hessenberg (6.5.3), and the second sweep triangularizes $H_1$. -/
theorem qrUpdateRankOne_spec {n : ℕ} {A Q R : Matrix (Fin n) (Fin n) ℝ} (h : IsQR A Q R)
    (u v : Fin n → ℝ) :
    IsQR (A + vecMulVec u v) (Id.run (qrUpdateRankOne pure Q R u v)).1
      (Id.run (qrUpdateRankOne pure Q R u v)).2 := by
  have hQ : Q ∈ orthogonalGroup (Fin n) ℝ := h.mem_unitaryGroup
  have hQQ : Q * Qᵀ = 1 := (mem_orthogonalGroup_iff _ ℝ).1 hQ
  have hw1 : Id.run (Chapter01.algorithm_1_1_3 pure Qᵀ u 0) = Qᵀ *ᵥ u := by
    rw [Chapter01.algorithm_1_1_3_spec, zero_add]
  obtain ⟨⟨P, hP, h1, h2, h3⟩, hwz, hHess, -⟩ :=
    Chapter05.givensVectorSweep_spec 0 (n - 1) (Qᵀ *ᵥ u) Q R h.apply_eq_zero (fun i hi => by omega)
  set st := Id.run (Chapter05.givensVectorSweep pure 0 (n - 1) (Qᵀ *ᵥ u) Q R) with hst
  set H : Matrix (Fin n) (Fin n) ℝ := Id.run (if h : 0 < n then do
      let r ← Chapter01.algorithm_1_1_2 pure (st.1 ⟨0, h⟩) v (st.2.2 ⟨0, h⟩)
      pure (st.2.2.updateRow ⟨0, h⟩ r)
    else pure st.2.2) with hHdef
  have hrun : Id.run (qrUpdateRankOne pure Q R u v) =
      Id.run (Chapter05.givensHessenbergSweep pure 0 (n - 1) st.2.1 H) := by
    simp only [qrUpdateRankOne, Id.run_bind, hw1]
    rw [hHdef]
    split_ifs <;> rfl
  have hHe : H = st.2.2 + vecMulVec st.1 v := by
    rw [hHdef]
    split_ifs with hn
    · ext i j
      simp only [Id.run_bind, Id.run_pure, Chapter01.algorithm_1_1_2_spec]
      by_cases hi : i = ⟨0, hn⟩
      · subst hi
        simp [vecMulVec_apply, mul_comm]
      · rw [updateRow_ne hi, Matrix.add_apply, vecMulVec_apply,
          hwz i (by have : (i : ℕ) ≠ 0 := fun e => hi (Fin.ext e); omega), zero_mul, add_zero]
    · ext i
      exact absurd i.isLt (by omega)
  have hPP : Pᵀ * P = 1 := (mem_orthogonalGroup_iff' _ ℝ).1 hP
  have hPt : Pᵀ ∈ orthogonalGroup (Fin n) ℝ := by
    rw [← conjTranspose_eq_transpose_of_trivial, ← star_eq_conjTranspose]
    exact Unitary.star_mem hP
  have e1 : Q * Pᵀ * (P * R) = A := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Pᵀ, hPP, Matrix.one_mul, h.mul_eq]
  have e2 : (Q * Pᵀ) *ᵥ (P *ᵥ (Qᵀ *ᵥ u)) = u := by
    rw [mulVec_mulVec, mulVec_mulVec]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Pᵀ P, hPP, Matrix.one_mul, hQQ, one_mulVec]
  have hprod : st.2.1 * H = A + vecMulVec u v := by
    rw [hHe, h1, h2, h3, Matrix.mul_add, mul_vecMulVec, e1, e2]
  have hHH : ∀ (i j : Fin n), (j : ℕ) + 1 < i → H i j = 0 := fun i j hij => by
    rw [hHe, Matrix.add_apply, hHess i j hij, vecMulVec_apply, hwz i (by omega), zero_mul,
      add_zero]
  rw [hrun]
  exact Chapter05.givensHessenbergSweep_spec (by rw [h2]; exact mul_mem hQ hPt) hprod hHH
    (fun i j _ hj => absurd hj (Nat.not_lt_zero _)) (Or.inr (by omega))

/-- **Section 6.5.2** of [golub2013matrix], correctness of the column deletion in exact arithmetic.
If $A = QR$ is a QR factorization of $A \in \mathbb{R}^{m \times (n+1)}$, then the output of
`GolubVanLoan.Chapter06.qrDeleteColumn` is a QR factorization of $A$ with its column $k$
deleted.

The run is at `M := Id` with `rnd := pure`. The matrix $Q^T \tilde A = H$ is upper Hessenberg
and upper triangular before column $k$ (`Matrix.IsQR.conjTranspose_mul_deleteColumn`), and the
sweep from column $k$ triangularizes it.

**Reading.** Deletion result includes wide matrices.
-/
theorem qrDeleteColumn_spec {m n : ℕ} {A : Matrix (Fin m) (Fin (n + 1)) ℝ}
    {Q : Matrix (Fin m) (Fin m) ℝ} {R : Matrix (Fin m) (Fin (n + 1)) ℝ} (h : IsQR A Q R)
    (k : Fin (n + 1)) :
    IsQR (A.submatrix id k.succAbove) (Id.run (qrDeleteColumn pure Q R k)).1
      (Id.run (qrDeleteColumn pure Q R k)).2 := by
  obtain ⟨h1, h2, h3⟩ := h.conjTranspose_mul_deleteColumn k
  have hQ : Q ∈ orthogonalGroup (Fin m) ℝ := h.mem_unitaryGroup
  have hk := k.isLt
  refine Chapter05.givensHessenbergSweep_spec hQ ?_ (fun i j hij => h2 i j hij)
    (fun i j hij hjk => h3 i j hij hjk) (Or.inl (by omega))
  rw [← h1, ← Matrix.mul_assoc, conjTranspose_eq_transpose_of_trivial,
    (mem_orthogonalGroup_iff _ ℝ).1 hQ, Matrix.one_mul]

/-- The exact-arithmetic step $j$ of `GolubVanLoan.Chapter06.qrInsertColumn`: if $j + 1 < m$,
compute the Givens pair of the entries $(j, k)$ and $(j + 1, k)$ of the current $H$ and rotate
the rows $j$, $j + 1$ of $H$ and the columns $j$, $j + 1$ of $Q$; otherwise do nothing. -/
private noncomputable def insColStep {m n : ℕ} (k : Fin (n + 1))
    (st : Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin (n + 1)) ℝ) (j : ℕ) :
    Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin (n + 1)) ℝ :=
  if h : j + 1 < m then
    Chapter05.givensPairStep ⟨j, by omega⟩ ⟨j + 1, h⟩
      (Id.run (Chapter05.algorithm_5_1_3 pure (st.2 ⟨j, by omega⟩ k) (st.2 ⟨j + 1, h⟩ k))) st
  else st

/-- **Section 6.5.2** of [golub2013matrix], correctness of the column insertion in exact arithmetic.
If $A = QR$ is a QR factorization of $A \in \mathbb{R}^{m \times n}$, $z \in \mathbb{R}^m$ and
$k$ is a column index, then the output of `GolubVanLoan.Chapter06.qrInsertColumn` is a QR
factorization of $A$ with $z$ inserted as its column $k$.

The run is at `M := Id` with `rnd := pure`. The invariant of the bottom-up sweep is:
$QH = \tilde A$; $H$ is upper triangular off the spike column $k$; the diagonal entries right of
the spike vanish in the rows not yet rotated, so a rotation of the rows $j$ and $j + 1$ creates
no subdiagonal entry; and the spike vanishes below the rows already rotated.

**Reading.** Exact QR for any insertion position and any rectangular shape.
-/
theorem qrInsertColumn_spec {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    {Q : Matrix (Fin m) (Fin m) ℝ} {R : Matrix (Fin m) (Fin n) ℝ} (h : IsQR A Q R)
    (z : Fin m → ℝ) (k : Fin (n + 1)) :
    IsQR (of fun i => k.insertNth (z i) (A i)) (Id.run (qrInsertColumn pure Q R z k)).1
      (Id.run (qrInsertColumn pure Q R z k)).2 := by
  set At : Matrix (Fin m) (Fin (n + 1)) ℝ := of fun i => k.insertNth (z i) (A i) with hAt
  obtain ⟨h1, h2⟩ := h.conjTranspose_mul_insertColumn z k
  have hQ : Q ∈ orthogonalGroup (Fin m) ℝ := h.mem_unitaryGroup
  set H₀ : Matrix (Fin m) (Fin (n + 1)) ℝ := of fun i => k.insertNth ((Qᵀ *ᵥ z) i) (R i)
    with hH₀
  rw [conjTranspose_eq_transpose_of_trivial] at h1 h2
  rw [← hAt] at h1 h2
  rw [← hH₀] at h1
  have hrun : Id.run (qrInsertColumn pure Q R z k) =
      (List.range' k (m - 1 - k)).reverse.foldl (insColStep k) (Q, H₀) := by
    simp only [qrInsertColumn, Id.run_bind, Chapter01.algorithm_1_1_3_spec, zero_add,
      List.idRun_foldlM]
    congr 1
    funext st j
    unfold insColStep
    split_ifs with hj
    · have hpq : (⟨j, by omega⟩ : Fin m) ≠ ⟨j + 1, hj⟩ := fun e => by simp [Fin.ext_iff] at e
      simp only [Id.run_bind, Id.run_pure]
      rw [Chapter05.givensApplyLeft_spec_of_forall_mem hpq _ _ (List.nodup_finRange (n + 1))
        (List.mem_finRange), Chapter05.givensApplyRight_spec_of_forall_mem hpq _ _
        (List.nodup_finRange m) (List.mem_finRange)]
      rfl
    · rfl
  set V : ℕ → Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin (n + 1)) ℝ → Prop := fun K st =>
    st.1 ∈ orthogonalGroup (Fin m) ℝ ∧ st.1 * st.2 = At ∧
      (∀ (i : Fin m) (j : Fin (n + 1)), (j : ℕ) < i → j ≠ k → st.2 i j = 0) ∧
      (∀ (i : Fin m) (j : Fin (n + 1)), k < j → (j : ℕ) = i → (i : ℕ) < K → st.2 i j = 0) ∧
      ∀ i : Fin m, K < i → st.2 i k = 0 with hV
  have hstep : ∀ j st, (k : ℕ) ≤ j → V (j + 1) st → V j (insColStep k st j) := by
    rintro j st hkj ⟨hQ, hQH, hab, hdiag, hspike⟩
    unfold insColStep
    split_ifs with hj
    · set p : Fin m := ⟨j, by omega⟩ with hp
      set q : Fin m := ⟨j + 1, hj⟩ with hq
      have hpv : (p : ℕ) = j := rfl
      have hqv : (q : ℕ) = j + 1 := rfl
      have hpq : p ≠ q := fun e => by have := congrArg Fin.val e; omega
      have hcs := (Chapter05.algorithm_5_1_3_spec (st.2 p k) (st.2 q k)).1
      refine ⟨Chapter05.givensPairStep_mem hpq hcs hQ,
        by rw [Chapter05.givensPairStep_mul hpq hcs, hQH],
        fun i l hil hlk => ?_, fun i l hkl hli hiK => ?_, fun i hi => ?_⟩
      · refine Chapter05.givensPairStep_eq_zero hpq _ st (fun hi => ?_) fun _ _ => hab i l hil hlk
        have hiv := hi.imp (congrArg Fin.val) (congrArg Fin.val)
        refine ⟨?_, hab q l (by omega) hlk⟩
        by_cases hlp : (l : ℕ) < j
        · exact hab p l (by omega) hlk
        · have hkl : k < l := by
            rcases lt_or_gt_of_ne hlk with h' | h'
            · exfalso
              have : (l : ℕ) < k := h'
              omega
            · exact h'
          exact hdiag p l hkl (by omega) (by omega)
      · have hip : i ≠ p := fun e => by rw [e] at hiK; omega
        have hiq : i ≠ q := fun e => by rw [e] at hiK; omega
        rw [Chapter05.givensPairStep_apply hpq, ite_eq_right hip, ite_eq_right hiq]
        exact hdiag i l hkl hli (by omega)
      · by_cases hiq : i = q
        · rw [hiq]
          exact Chapter05.givensPairStep_zero hpq k st
        · have hip : i ≠ p := fun e => by rw [e] at hi; omega
          rw [Chapter05.givensPairStep_apply hpq, ite_eq_right hip, ite_eq_right hiq]
          exact hspike i (by
            have : (i : ℕ) ≠ j + 1 := fun e => hiq (Fin.ext (by rw [hqv, e]))
            omega)
    · refine ⟨hQ, hQH, hab, fun i l hkl hli hiK => hdiag i l hkl hli (by omega), fun i hi => ?_⟩
      exfalso
      have := i.isLt
      omega
  have hall : ∀ t st, V (k + t) st →
      V k ((List.range' k t).reverse.foldl (insColStep k) st) := by
    intro t
    induction t with
    | zero => intro st h; simpa using h
    | succ t ih =>
      intro st h
      rw [List.range'_concat, List.reverse_append, one_mul]
      simp only [List.reverse_singleton, List.singleton_append, List.foldl_cons]
      exact ih _ (hstep (k + t) st (by omega) h)
  have h0 : V (k + (m - 1 - k)) (Q, H₀) := by
    refine ⟨hQ, ?_, fun i j hij hjk => ?_, fun i j hkj hji _ => ?_, fun i hi => ?_⟩
    · rw [← h1, ← Matrix.mul_assoc, (mem_orthogonalGroup_iff _ ℝ).1 hQ, Matrix.one_mul]
    · rw [← h1]
      exact h2 i j hij hjk
    · obtain ⟨t, rfl⟩ := Fin.exists_succAbove_eq (ne_of_gt hkj)
      have hts : (k.succAbove t : ℕ) = t + 1 := by
        rcases lt_or_ge t.castSucc k with h' | h'
        · rw [Fin.succAbove_of_castSucc_lt _ _ h'] at hkj
          exact absurd hkj (not_lt.2 h'.le)
        · rw [Fin.succAbove_of_le_castSucc _ _ h']
          simp
      simp only [hH₀, of_apply, Fin.insertNth_apply_succAbove]
      exact h.apply_eq_zero i t (by omega)
    · exfalso
      have := i.isLt
      omega
  obtain ⟨hQ', hQH', hab', -, hspike'⟩ := hall (m - 1 - k) (Q, H₀) h0
  rw [hrun]
  refine ⟨hQ', fun i j hij => ?_, hQH'⟩
  by_cases hjk : j = k
  · rw [hjk] at hij ⊢
    exact hspike' i hij
  · exact hab' i j hij hjk

/-- **Section 6.5.3** of [golub2013matrix], correctness of the row insertion in exact arithmetic. If
$A = QR$ is a QR factorization of $A \in \mathbb{R}^{m \times n}$, $w \in \mathbb{R}^n$ and $k$
is a row index, then the output of `GolubVanLoan.Chapter06.qrInsertRow` is a QR factorization of
$A$ with $w^T$ inserted as its row $k$.

The run is at `M := Id` with `rnd := pure`. With the permutation $P$ given by
`Fin.cycleRange k`, the matrix $\operatorname{diag}(1, Q^T) P \tilde A = [w^T; R]$ is upper
Hessenberg (`Matrix.IsQR.conjTranspose_mul_insertRow`), and the sweep triangularizes it. -/
theorem qrInsertRow_spec {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ} {Q : Matrix (Fin m) (Fin m) ℝ}
    {R : Matrix (Fin m) (Fin n) ℝ} (h : IsQR A Q R) (w : Fin n → ℝ) (k : Fin (m + 1)) :
    IsQR (of (k.insertNth w A)) (Id.run (qrInsertRow pure Q R w k)).1
      (Id.run (qrInsertRow pure Q R w k)).2 := by
  obtain ⟨h1, h2⟩ := h.conjTranspose_mul_insertRow w k
  have hQ : Q ∈ unitaryGroup (Fin m) ℝ := h.mem_unitaryGroup
  have hQ' : (consDiag 1 Q).submatrix k.cycleRange id ∈ orthogonalGroup (Fin (m + 1)) ℝ :=
    submatrix_mem_unitaryGroup (consDiag_mem_unitaryGroup (by simp) hQ) _
  refine Chapter05.givensHessenbergSweep_spec hQ' ?_ (fun i j hij => h2 i j hij)
    (fun i j _ hj => absurd hj (Nat.not_lt_zero _)) (Or.inl (by omega))
  rw [← h1, submatrix_id_mul, ← Matrix.mul_assoc, consDiag_mul_consDiag, mul_one,
    ← star_eq_conjTranspose, mem_unitaryGroup_iff.1 hQ, consDiag_one, Matrix.one_mul,
    submatrix_submatrix, Equiv.symm_comp_self, Function.comp_id, submatrix_id_id]

/-- **Section 6.5.3** of [golub2013matrix], correctness of the deletion of the first row in exact
arithmetic. If $A = QR$ is a QR factorization of $A \in \mathbb{R}^{(m+1) \times n}$, then the
output of `GolubVanLoan.Chapter06.qrDeleteFirstRow` is a QR factorization of $A(2{:}m{+}1, :)$.

The run is at `M := Id` with `rnd := pure`. After the sweep, the first row of $Q G_m \cdots G_1$
is $\alpha e_1^T$ with $\alpha^2 = 1$, so its first column is $\alpha e_1$ as well, and $A =
\operatorname{diag}(\alpha, Q_1) [v^T; R_1]$ with $[v^T; R_1]$ upper Hessenberg. -/
theorem qrDeleteFirstRow_spec {m n : ℕ} {A : Matrix (Fin (m + 1)) (Fin n) ℝ}
    {Q : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ} {R : Matrix (Fin (m + 1)) (Fin n) ℝ}
    (h : IsQR A Q R) :
    IsQR (A.submatrix Fin.succ id) (Id.run (qrDeleteFirstRow pure Q R)).1
      (Id.run (qrDeleteFirstRow pure Q R)).2 := by
  have hQ : Q ∈ orthogonalGroup (Fin (m + 1)) ℝ := h.mem_unitaryGroup
  obtain ⟨⟨P, hP, h1, h2, h3⟩, hwz, hHess, -⟩ :=
    Chapter05.givensVectorSweep_spec 0 m (Q 0) Q R h.apply_eq_zero (fun i hi => by omega)
  set st := Id.run (Chapter05.givensVectorSweep pure 0 m (Q 0) Q R) with hst
  have hrun : Id.run (qrDeleteFirstRow pure Q R) =
      (st.2.1.submatrix Fin.succ Fin.succ, st.2.2.submatrix Fin.succ id) := rfl
  rw [hrun]
  have hPt : Pᵀ ∈ orthogonalGroup (Fin (m + 1)) ℝ := by
    rw [← conjTranspose_eq_transpose_of_trivial, ← star_eq_conjTranspose]
    exact Unitary.star_mem hP
  have hQo : st.2.1 ∈ orthogonalGroup (Fin (m + 1)) ℝ := by rw [h2]; exact mul_mem hQ hPt
  have hQR : st.2.1 * st.2.2 = A := by
    rw [h2, h3, Matrix.mul_assoc, ← Matrix.mul_assoc Pᵀ,
      (mem_orthogonalGroup_iff' _ ℝ).1 hP, Matrix.one_mul, h.mul_eq]
  have hrow : ∀ j, st.2.1 0 j = st.1 j := by
    intro j
    rw [h2, h1, Matrix.mul_apply, mulVec, dotProduct]
    simp only [transpose_apply]
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _
  have hrow0 : ∀ j : Fin m, st.2.1 0 j.succ = 0 := fun j => by
    rw [hrow]
    exact hwz _ (by simp)
  have hcol0 : ∀ i : Fin m, st.2.1 i.succ 0 = 0 := by
    have e1 : (st.2.1 * st.2.1ᵀ) 0 0 = 1 := by rw [(mem_orthogonalGroup_iff _ ℝ).1 hQo]; simp
    have e2 : (st.2.1ᵀ * st.2.1) 0 0 = 1 := by rw [(mem_orthogonalGroup_iff' _ ℝ).1 hQo]; simp
    rw [Matrix.mul_apply, Fin.sum_univ_succ] at e1 e2
    simp only [transpose_apply, hrow0, mul_zero, Finset.sum_const_zero, add_zero] at e1 e2
    have hs : ∑ i : Fin m, st.2.1 i.succ 0 * st.2.1 i.succ 0 = 0 := by linarith
    intro i
    exact mul_self_eq_zero.1 ((Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => mul_self_nonneg (st.2.1 (Fin.succ i) 0))).1 hs i (Finset.mem_univ _))
  refine ⟨?_, fun i j hij => ?_, ?_⟩
  · refine (mem_orthogonalGroup_iff _ ℝ).2 ?_
    ext i j
    have := congrFun (congrFun ((mem_orthogonalGroup_iff _ ℝ).1 hQo) i.succ) j.succ
    rw [Matrix.mul_apply, Fin.sum_univ_succ] at this
    simp only [transpose_apply, hcol0, zero_mul, zero_add, Matrix.one_apply, Fin.succ_inj] at this
    simpa [Matrix.mul_apply, Matrix.one_apply] using this
  · exact hHess i.succ j (by simp; omega)
  · ext i j
    have := congrFun (congrFun hQR i.succ) j
    rw [Matrix.mul_apply, Fin.sum_univ_succ, hcol0, zero_mul, zero_add] at this
    simpa [Matrix.mul_apply] using this

/-- The exact-arithmetic step $k$ of `GolubVanLoan.Chapter06.choleskyUpdate`: multiply the stacked
matrix on the left by the transpose of the Givens rotation in the rows $k$ and $n + 1$ computed
from its entries $(k, k)$ and $(n + 1, k)$. -/
private noncomputable def cholUpdStep {n : ℕ} (S : Matrix (Fin (n + 1)) (Fin n) ℝ) (k : Fin n) :
    Matrix (Fin (n + 1)) (Fin n) ℝ :=
  (Chapter05.givensRotation k.castSucc (Fin.last n)
    (Id.run (Chapter05.algorithm_5_1_3 pure (S k.castSucc k) (S (Fin.last n) k))).1
    (Id.run (Chapter05.algorithm_5_1_3 pure (S k.castSucc k) (S (Fin.last n) k))).2)ᵀ * S

/-- For $S \in \mathbb{R}^{(n+1) \times p}$, the Gram matrix splits off the last row:
$S^T S = S_{1:n}^T S_{1:n} + s_{n+1} s_{n+1}^T$, where $s_{n+1}^T$ is the last row of $S$. -/
private theorem transpose_mul_self_castSucc {n p : ℕ} (S : Matrix (Fin (n + 1)) (Fin p) ℝ) :
    Sᵀ * S = (S.submatrix Fin.castSucc id)ᵀ * S.submatrix Fin.castSucc id +
      vecMulVec (S (Fin.last n)) (S (Fin.last n)) := by
  ext i j
  simp [Matrix.mul_apply, Fin.sum_univ_castSucc, vecMulVec_apply]

/-- **Section 6.5.4** of [golub2013matrix], correctness of the Cholesky update in exact arithmetic.
Let $A = GG^T$ be a Cholesky factorization of $A \in \mathbb{R}^{n \times n}$, and let
$z \in \mathbb{R}^n$. Then the output $\tilde G$ of `GolubVanLoan.Chapter06.choleskyUpdate` is
lower triangular with nonzero diagonal and $\tilde G \tilde G^T = A + zz^T$. With $D =
\operatorname{diag}(\operatorname{sign}(\tilde g_{ii}))$, the matrix $D \tilde G^T$ is the upper
triangular Cholesky factor of $A + zz^T$.

**Correction.** The source says that the updated Cholesky factor is $\tilde G = R^T$. A Givens
rotation can produce a negative diagonal entry $r$, so $\tilde G$ is the Cholesky factor only
after the signs of its diagonal are normalized; see `GolubVanLoan.Chapter06.equation_6_5_7`.

The run is at `M := Id` with `rnd := pure`. The invariant is: the rotations keep the Gram matrix
$M^T M = A + zz^T$ of the stacked matrix $M$, keep its top block upper triangular with nonzero
diagonal (because $|r| = \sqrt{a^2 + b^2}$), and zero the appended row before the current
column. -/
theorem choleskyUpdate_spec {n : ℕ} {A G : Matrix (Fin n) (Fin n) ℝ} (hG : IsCholesky A Gᵀ)
    (z : Fin n → ℝ) :
    (Id.run (choleskyUpdate pure G z))ᵀ.IsUpperTriangular ∧
      (∀ i, Id.run (choleskyUpdate pure G z) i i ≠ 0) ∧
      Id.run (choleskyUpdate pure G z) * (Id.run (choleskyUpdate pure G z))ᵀ =
        A + vecMulVec z z ∧
      IsCholesky (A + vecMulVec z z) (diagonal (fun i =>
        (SignType.sign (Id.run (choleskyUpdate pure G z) i i) : ℝ)) *
          (Id.run (choleskyUpdate pure G z))ᵀ) := by
  set S₀ : Matrix (Fin (n + 1)) (Fin n) ℝ :=
    of fun i => Fin.lastCases (motive := fun _ => Fin n → ℝ) z (fun i => Gᵀ i) i with hS₀
  have hF : ∀ (S : Matrix (Fin (n + 1)) (Fin n) ℝ) (k : Fin n),
      Id.run (Chapter05.givensApplyLeft pure k.castSucc (Fin.last n)
        (Id.run (Chapter05.algorithm_5_1_3 pure (S k.castSucc k) (S (Fin.last n) k))).1
        (Id.run (Chapter05.algorithm_5_1_3 pure (S k.castSucc k) (S (Fin.last n) k))).2
        (List.finRange n) S) = cholUpdStep S k := fun S k =>
    Chapter05.givensApplyLeft_spec_of_forall_mem (Fin.castSucc_lt_last k).ne _ _
      (List.nodup_finRange n) List.mem_finRange S
  have hrun : Id.run (choleskyUpdate pure G z) =
      (((List.finRange n).foldl cholUpdStep S₀).submatrix Fin.castSucc id)ᵀ := by
    simp only [choleskyUpdate, Id.run_bind, Id.run_pure, List.idRun_foldlM, hF]
    rfl
  set Inv : ℕ → Matrix (Fin (n + 1)) (Fin n) ℝ → Prop := fun t S =>
    (∀ i j : Fin n, j < i → S i.castSucc j = 0) ∧ (∀ i : Fin n, S i.castSucc i ≠ 0) ∧
      (∀ j : Fin n, (j : ℕ) < t → S (Fin.last n) j = 0) ∧ Sᵀ * S = A + vecMulVec z z with hInv
  have hstep : ∀ t (ht : t < n) S, Inv t S → Inv (t + 1) (cholUpdStep S ⟨t, ht⟩) := by
    rintro t ht S ⟨hU, hd, hy, hgram⟩
    set k : Fin n := ⟨t, ht⟩ with hk
    have hne : k.castSucc ≠ Fin.last n := (Fin.castSucc_lt_last k).ne
    obtain ⟨hcs, hz, habs⟩ := Chapter05.algorithm_5_1_3_spec (S k.castSucc k) (S (Fin.last n) k)
    set c := (Id.run (Chapter05.algorithm_5_1_3 pure (S k.castSucc k) (S (Fin.last n) k))).1
    set s := (Id.run (Chapter05.algorithm_5_1_3 pure (S k.castSucc k) (S (Fin.last n) k))).2
    have happ := Chapter05.givensRotation_transpose_mul_apply hne c s S
    have hGo := Chapter05.givensRotation_mem_orthogonalGroup hne hcs
    have hne' : ∀ i : Fin n, i ≠ k → i.castSucc ≠ k.castSucc := fun i hi e =>
      hi (Fin.castSucc_injective _ e)
    have hlast : ∀ i : Fin n, i.castSucc ≠ Fin.last n := fun i => (Fin.castSucc_lt_last i).ne
    refine ⟨fun i j hji => ?_, fun i => ?_, fun j hj => ?_, ?_⟩
    · change ((Chapter05.givensRotation k.castSucc (Fin.last n) c s)ᵀ * S) i.castSucc j = 0
      rw [happ]
      by_cases hik : i = k
      · have hjk : j < k := hik ▸ hji
        rw [ite_eq_left (congrArg Fin.castSucc hik), hU k j hjk, hy j hjk]
        ring
      · rw [ite_eq_right (hne' i hik), ite_eq_right (hlast i)]
        exact hU i j hji
    · change ((Chapter05.givensRotation k.castSucc (Fin.last n) c s)ᵀ * S) i.castSucc i ≠ 0
      rw [happ]
      by_cases hik : i = k
      · rw [ite_eq_left (congrArg Fin.castSucc hik), hik]
        intro h0
        rw [h0, abs_zero] at habs
        have := (Real.sqrt_eq_zero (by positivity)).1 habs.symm
        exact hd k (by nlinarith [sq_nonneg (S k.castSucc k), sq_nonneg (S (Fin.last n) k)])
      · rw [ite_eq_right (hne' i hik), ite_eq_right (hlast i)]
        exact hd i
    · change ((Chapter05.givensRotation k.castSucc (Fin.last n) c s)ᵀ * S) (Fin.last n) j = 0
      rw [happ, ite_eq_right hne.symm, ite_eq_left rfl]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
      · rw [hU k j hj, hy j hj]
        ring
      · obtain rfl : j = k := Fin.ext hj
        exact hz
    · change ((Chapter05.givensRotation k.castSucc (Fin.last n) c s)ᵀ * S)ᵀ *
        ((Chapter05.givensRotation k.castSucc (Fin.last n) c s)ᵀ * S) = _
      rw [transpose_mul, transpose_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc
        (Chapter05.givensRotation k.castSucc (Fin.last n) c s),
        (mem_orthogonalGroup_iff _ ℝ).1 hGo, Matrix.one_mul, hgram]
  have hS₀c : ∀ i : Fin n, S₀ i.castSucc = Gᵀ i := fun i => funext fun j => by
    rw [hS₀, of_apply, Fin.lastCases_castSucc]
  have hS₀l : S₀ (Fin.last n) = z := funext fun j => by
    rw [hS₀, of_apply, Fin.lastCases_last]
  have h0 : Inv 0 S₀ := by
    refine ⟨fun i j hji => ?_, fun i => ?_, fun _ h => absurd h (Nat.not_lt_zero _), ?_⟩
    · rw [hS₀c]
      exact hG.isUpperTriangular hji
    · rw [hS₀c]
      exact (hG.diag_pos i).ne'
    · rw [transpose_mul_self_castSucc, hS₀l]
      congr 1
      rw [← conjTranspose_eq_transpose_of_trivial (S₀.submatrix Fin.castSucc id),
        ← hG.conjTranspose_mul_self]
      congr 1 <;> ext i j <;> simp [hS₀c]
  obtain ⟨hU, hd, hy, hgram⟩ := List.foldl_finRange_induction Inv (f := cholUpdStep) h0
    fun k S hS => hstep k k.isLt S hS
  set S := (List.finRange n).foldl cholUpdStep S₀ with hS
  have hy0 : S (Fin.last n) = 0 := funext fun j => hy j j.isLt
  rw [transpose_mul_self_castSucc, hy0, vecMulVec_zero, add_zero] at hgram
  have hR : (S.submatrix Fin.castSucc id).IsUpperTriangular := fun i j hji => hU i j hji
  have hdR : ∀ i, S.submatrix Fin.castSucc id i i ≠ 0 := hd
  rw [hrun, transpose_transpose]
  refine ⟨hR, fun i => ?_, ?_, ?_⟩
  · rw [transpose_apply]
    exact hd i
  · rw [← hgram]
  · have := isCholesky_diagonal_sign_mul hR hdR hgram
    simpa [transpose_apply] using this

/-! ### §6.5.5 The ULV decomposition -/

/-- **Equation (6.5.16)** of [golub2013matrix], its exact content. A rank-revealing ULV
decomposition of $A \in \mathbb{R}^{m \times n}$ has the form $$U^T A V = \begin{bmatrix} L \\ 0
\end{bmatrix}, \qquad U^T U = I_m, \qquad V^T V = I_n,$$ with $L$ lower triangular. Such a
decomposition can be obtained by QR with column pivoting, $U^T A \Pi = [R; 0]$, followed by a QR
factorization $V_1^T R^T = L^T$; then $V = \Pi V_1$. The theorem says: let $m = n + p$, let
$U \in \mathbb{R}^{m \times m}$, $\Pi \in \mathbb{R}^{n \times n}$ and
$V_1 \in \mathbb{R}^{n \times n}$ be orthogonal, and let $R, L \in \mathbb{R}^{n \times n}$ with
$U^T A \Pi = [R; 0]$, $V_1^T R^T = L^T$ and $L^T$ upper triangular. Then
$U^T A (\Pi V_1) = [L; 0]$, $L$ is lower triangular, $U^T U = I_m$ and
$(\Pi V_1)^T (\Pi V_1) = I_n$.

**Generalization.** The source obtains $\Pi$ and $R$ from QR with column pivoting. The statement
holds for every orthogonal $\Pi$ (a permutation matrix is one) and every $R$ with
$U^T A \Pi = [R; 0]$.

The rank-revealing smallness of $L_{21}$ and $L_{22}$ is a heuristic property of pivoted QR and
is not formalized. The rows of $A$ are reindexed by `finSumFinEquiv`, and $[L; 0]$ is
`Matrix.fromRows L 0`. -/
theorem equation_6_5_16 {n p : ℕ} {A : Matrix (Fin (n + p)) (Fin n) ℝ}
    {U : Matrix (Fin (n + p)) (Fin (n + p)) ℝ} (hU : U ∈ orthogonalGroup (Fin (n + p)) ℝ)
    {P V₁ R L : Matrix (Fin n) (Fin n) ℝ} (hP : P ∈ orthogonalGroup (Fin n) ℝ)
    (hV₁ : V₁ ∈ orthogonalGroup (Fin n) ℝ)
    (hR : (Uᵀ * A * P).submatrix finSumFinEquiv id = fromRows R 0) (hL : V₁ᵀ * Rᵀ = Lᵀ)
    (hLt : Lᵀ.IsUpperTriangular) :
    (Uᵀ * A * (P * V₁)).submatrix finSumFinEquiv id = fromRows L 0 ∧ L.IsLowerTriangular ∧
      Uᵀ * U = 1 ∧ (P * V₁)ᵀ * (P * V₁) = 1 := by
  have hRV : R * V₁ = L := by
    rw [← transpose_transpose (R * V₁), transpose_mul, hL, transpose_transpose]
  refine ⟨?_, fun i j hij => ?_, ?_, ?_⟩
  · rw [← Matrix.mul_assoc, ← hRV]
    ext i j
    have := congrFun (congrFun hR i)
    simp only [submatrix_apply, id] at this ⊢
    rw [Matrix.mul_apply]
    simp only [this] at *
    rcases i with i | i
    · simp [fromRows_apply_inl, Matrix.mul_apply]
    · simp [fromRows_apply_inr]
  · exact hLt hij
  · exact (mem_orthogonalGroup_iff' _ ℝ).1 hU
  · exact (mem_orthogonalGroup_iff' _ ℝ).1 ((orthogonalGroup (Fin n) ℝ).mul_mem hP hV₁)

open scoped Matrix.Norms.L2Operator in
/-- **Section 6.5.5** of [golub2013matrix], the approximate null space. Let $n = r + q$ and
$m = n + p$, let $U \in \mathbb{R}^{m \times m}$ be orthogonal, let
$V \in \mathbb{R}^{n \times n}$, and let $L = [L_{11}\ 0; L_{21}\ L_{22}] \in \mathbb{R}^{n
\times n}$ be lower triangular with $$U^T A V = \begin{bmatrix} L \\ 0 \end{bmatrix}.$$ If
$V = [V_1 \mid V_2]$ with $V_2 = V(:, r{+}1{:}n)$, then $$\|AV_2\|_2 = \|L_{22}\|_2.$$ So when
$L_{22}$ is small, the columns of $V_2$ define an approximate null space of $A$.

**Typo.** The source writes $\|AV_2\|_2 = \|U_2 L_{22}\|_2 = \|L_{22}\|_2$ with
$U_2 = U(:, r{+}1{:}m)$, which does not match the $n - r$ rows of $L_{22}$. The columns
$r{+}1{:}n$ of $U$ are meant; in both readings the norm is $\|L_{22}\|_2$.

The proof writes $AV_2 = U [0; L_{22}; 0]$. The statement does not need $V$ to be orthogonal.
The norm is the scoped `Matrix.Norms.L2Operator` norm. -/
theorem ulv_nullspace_norm {r q p : ℕ} {A : Matrix (Fin (r + q + p)) (Fin (r + q)) ℝ}
    {U : Matrix (Fin (r + q + p)) (Fin (r + q + p)) ℝ}
    (hU : U ∈ orthogonalGroup (Fin (r + q + p)) ℝ) {V L : Matrix (Fin (r + q)) (Fin (r + q)) ℝ}
    (h : (Uᵀ * A * V).submatrix finSumFinEquiv id = fromRows L 0) (hL : L.IsLowerTriangular) :
    ‖A * V.submatrix id (Fin.natAdd r)‖ = ‖L.submatrix (Fin.natAdd r) (Fin.natAdd r)‖ := by
  set f : Fin q → Fin (r + q + p) := fun j => Fin.castAdd p (Fin.natAdd r j) with hf
  set W : Matrix (Fin (r + q + p)) (Fin q) ℝ := (1 : Matrix _ _ ℝ).submatrix id f with hW
  have hUU : U * Uᵀ = 1 := (mem_orthogonalGroup_iff _ ℝ).1 hU
  have hUU' : Uᵀ * U = 1 := (mem_orthogonalGroup_iff' _ ℝ).1 hU
  have hfinj : Function.Injective f := fun a b hab => by
    simpa [hf, Fin.ext_iff] using hab
  have hWW : Wᵀ * W = 1 := by
    ext a b
    simp only [hW, Matrix.mul_apply, transpose_apply, submatrix_apply, id, Matrix.one_apply]
    rw [Finset.sum_eq_single (f a)]
    · simp [hfinj.eq_iff]
    · intro i _ hi
      simp only [hi, ite_false, zero_mul]
    · simp
  have key : Uᵀ * A * V.submatrix id (Fin.natAdd r) =
      W * L.submatrix (Fin.natAdd r) (Fin.natAdd r) := by
    ext i j
    have hsub : (Uᵀ * A * V.submatrix id (Fin.natAdd r)) i j = (Uᵀ * A * V) i (Fin.natAdd r j) := by
      simp only [Matrix.mul_apply, submatrix_apply, id]
    rw [hsub]
    refine Fin.addCases (fun a => ?_) (fun b => ?_) i
    · have e := congrFun (congrFun h (Sum.inl a)) (Fin.natAdd r j)
      simp only [submatrix_apply, finSumFinEquiv_apply_left, id, fromRows_apply_inl] at e
      rw [e, Matrix.mul_apply]
      refine Fin.addCases (fun a' => ?_) (fun b' => ?_) a
      · have : L (Fin.castAdd q a') (Fin.natAdd r j) = 0 := hL (by
          have := a'.isLt
          simp [Fin.lt_def]
          omega)
        rw [this, Finset.sum_eq_zero]
        intro k _
        simp only [hW, submatrix_apply, id, Matrix.one_apply, hf]
        rw [ite_eq_right]
        · simp
        · intro hk
          have := congrArg Fin.val hk
          simp at this
          omega
      · rw [Finset.sum_eq_single b']
        · simp [hW, hf, Matrix.one_apply]
        · intro k _ hk
          simp only [hW, submatrix_apply, id, Matrix.one_apply, hf]
          rw [ite_eq_right]
          · simp
          · intro hk'
            exact hk (Fin.ext (by have := congrArg Fin.val hk'; simp at this; omega))
        · simp
    · have e := congrFun (congrFun h (Sum.inr b)) (Fin.natAdd r j)
      simp only [submatrix_apply, finSumFinEquiv_apply_right, id, fromRows_apply_inr,
        Matrix.zero_apply] at e
      rw [e, Matrix.mul_apply, Finset.sum_eq_zero]
      intro k _
      simp only [hW, submatrix_apply, id, Matrix.one_apply, hf]
      rw [ite_eq_right]
      · simp
      · intro hk
        have := congrArg Fin.val hk
        simp at this
        omega
  have hAV : A * V.submatrix id (Fin.natAdd r) =
      (U * W) * L.submatrix (Fin.natAdd r) (Fin.natAdd r) := by
    rw [Matrix.mul_assoc U W, ← key, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hUU,
      Matrix.one_mul]
  have hUW : (U * W)ᴴ * (U * W) = 1 := by
    rw [conjTranspose_eq_transpose_of_trivial, transpose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc Uᵀ, hUU', Matrix.one_mul, hWW]
  rw [hAV, l2_opNorm_mul_of_conjTranspose_mul_self_eq_one hUW]

end GolubVanLoan.Chapter06
