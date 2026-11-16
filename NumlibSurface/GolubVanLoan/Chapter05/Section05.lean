/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.GolubVanLoan.Chapter05.Section04

/-!
# Golub and Van Loan, Section 5.5: The rank-deficient least-squares problem

This module formalizes §5.5 of [golub2013matrix], the least-squares problem $\min_x \|Ax - b\|_2$
for $A \in \mathbb{R}^{m \times n}$ and $b \in \mathbb{R}^m$ when $A$ can be rank deficient. The set
of minimizers is then convex, and its unique element of minimum 2-norm is $x_{LS} = A^+ b$, where
$A^+$ is the pseudoinverse. For an SVD $U^T A V = \Sigma$ and $r = \operatorname{rank}(A)$, Theorem
5.5.1 gives $x_{LS} = \sum_{i=1}^{r} (u_i^T b / \sigma_i) v_i$ and $\|Ax_{LS} - b\|_2^2 =
\sum_{i=r+1}^{m} (u_i^T b)^2$. The module also proves the characterizations of $A^+$ (the SVD
formula, the Frobenius-norm problem (5.5.3) and the Moore–Penrose conditions), the sensitivity of
$A^+$ (Wedin's bound and an example of discontinuity), an error bound for the truncated SVD
solution, the properties of the basic solution $x_B$ from QR with column pivoting with the
comparison (5.5.5) of $x_B$ and $x_{LS}$, and SVD-based subset selection (Theorems 5.5.2–5.5.3 and
Algorithm 5.5.1).

The proofs specialize the backbone modules `Numlib.LinearAlgebra.Matrix.LeastSquares`,
`Numlib.LinearAlgebra.Matrix.SVD`, `Numlib.LinearAlgebra.Matrix.CompleteOrthogonal` and
`Numlib.LinearAlgebra.Matrix.RankRevealing`.

## Main definitions

* §5.5.4, `GolubVanLoan.Chapter05.truncatedSVDSolution`: the truncated SVD solution $x_{\hat r} =
  \sum_{i=1}^{\hat r} (\hat u_i^T b / \hat\sigma_i) \hat v_i$.
* Algorithm 5.5.1, `GolubVanLoan.Chapter05.algorithm_5_5_1`: SVD-based subset selection.

## Main results

* §5.5.1, `GolubVanLoan.Chapter05.minNorm_existsUnique`: the set of least-squares minimizers is
  convex, and $A^+ b$ is its unique element of minimum 2-norm.
* §5.5.1, `GolubVanLoan.Chapter05.minNorm_of_completeOrthogonal`: the minimum-norm solution and the
  residual from a complete orthogonal decomposition.
* Equation (5.5.1), `GolubVanLoan.Chapter05.equation_5_5_1`: $\sum_{i=1}^{r} (u_i^T b / \sigma_i)
  v_i = A^+ b$, and this vector is the least-squares minimizer of minimum 2-norm.
* Equation (5.5.2), `GolubVanLoan.Chapter05.equation_5_5_2`: $\|A x_{LS} - b\|_2^2 =
  \sum_{i=r+1}^{m} (u_i^T b)^2$.
* Theorem 5.5.1, `GolubVanLoan.Chapter05.theorem_5_5_1`: the SVD formula for $x_{LS}$ and for its
  residual.
* §5.5.2, `GolubVanLoan.Chapter05.pseudoinverse_eq_svd`: $A^+ = V \Sigma^+ U^T$,
  $\rho_{LS} = \|(I - AA^+) b\|_2$, and $A^+ = (A^T A)^{-1} A^T$ when $\operatorname{rank}(A) = n$.
* §5.5.2, `GolubVanLoan.Chapter05.pseudoinverse_eq_inv`: $A^+ = A^{-1}$ for a nonsingular square
  $A$.
* Equation (5.5.3), `GolubVanLoan.Chapter05.equation_5_5_3`: $A^+$ is the solution of minimum
  Frobenius norm of $\min_X \|AX - I_m\|_F$.
* §5.5.2, `GolubVanLoan.Chapter05.moorePenrose`: $A^+$ is the unique matrix that satisfies the four
  Moore–Penrose conditions, and $AA^+$ is the orthogonal projection onto $\operatorname{ran}(A)$.
* §5.5.3, `GolubVanLoan.Chapter05.pinv_perturbation`: $\|(A + \delta A)^+ - A^+\|_F \le 2 \|\delta
  A\|_F \max\{\|A^+\|_2^2, \|(A + \delta A)^+\|_2^2\}$.
* §5.5.3, `GolubVanLoan.Chapter05.pinv_discontinuity`: the pseudoinverse is not a continuous
  function of the matrix.
* §5.5.4, `GolubVanLoan.Chapter05.norm_truncatedSVDSolution_sub_le`: a bound on
  $\|x_{\hat r} - x_{LS}\|_2$ when the computed singular vectors are close to the exact ones.
* §5.5.5, `GolubVanLoan.Chapter05.basicSolution`: the least-squares minimizers in terms of a QR
  factorization with column pivoting, and the basic solution $x_B$ is a minimizer with at most $r$
  nonzero components.
* Equation (5.5.4), `GolubVanLoan.Chapter05.equation_5_5_4`: $\|x_{LS}\|_2$ as a minimum over the
  minimizers $x_B - \Pi [R_{11}^{-1} R_{12}; -I] z$.
* §5.5.5, `GolubVanLoan.Chapter05.basicSolution_eq_pinv_of_eq_zero`: if $R_{12} = 0$, then
  $x_B = x_{LS}$.
* Equation (5.5.5), `GolubVanLoan.Chapter05.equation_5_5_5`: $1 \le \|x_B\|_2 / \|x_{LS}\|_2 \le
  \sqrt{1 + \|R_{11}^{-1} R_{12}\|_2^2}$.
* Theorem 5.5.2, `GolubVanLoan.Chapter05.theorem_5_5_2`: $\sigma_{\tilde r}(A) / \|\tilde
  V_{11}^{-1}\|_2 \le \sigma_{\tilde r}(B_1) \le \sigma_{\tilde r}(A)$ for the first $\tilde r$
  columns $B_1$ of $AP$.
* §5.5.7, `GolubVanLoan.Chapter05.qrcp_V11`: QR with column pivoting of $V(:, 1{:}\tilde r)^T$ gives
  a nonsingular $\tilde V_{11}$ with $\|\tilde V_{11}^{-1}\|_2 = \|R_{11}^{-1}\|_2$.
* Algorithm 5.5.1, `GolubVanLoan.Chapter05.algorithm_5_5_1_spec`: in exact arithmetic, the selected
  columns are independent and $z$ solves the least-squares problem on them.
* Theorem 5.5.3, `GolubVanLoan.Chapter05.theorem_5_5_3`: the residuals of the subset solution and of
  the nearest rank-$\tilde r$ solution differ by at most $(\sigma_{\tilde r + 1}(A) / \sigma_{\tilde
  r}(A)) \|\tilde V_{11}^{-1}\|_2 \|b\|_2$.

## Conventions

* The pseudoinverse $A^+$ is `Matrix.pinv`. The definition $A^+ = V \Sigma^+ U^T$ of the source is
  the theorem `GolubVanLoan.Chapter05.pseudoinverse_eq_svd`.
* An SVD $U^T A V = \Sigma$ is `Matrix.IsSVD A U σ V`: $U$ and $V$ are orthogonal, and the singular
  values $\sigma$ are nonnegative and nonincreasing. Indices are 0-based: the source's $u_i$, $v_i$
  and $\sigma_i$ are `U.col (i - 1)`, `V.col (i - 1)` and `σ (i - 1)`. The sorted singular value
  $\sigma_k(A)$ is `A.sortedSingularValues (k - 1)`.
* Least-squares statements are on `EuclideanSpace ℝ (Fin m)`, where a matrix acts through
  `Matrix.toEuclideanLin`. A least-squares minimizer is `Matrix.IsLeastSquaresSolution`, and the
  minimizer of minimum 2-norm is `Matrix.IsMinNormLeastSquaresSolution`.
* A QR factorization with column pivoting $A\Pi = QR$ with $R = [R_{11}\ R_{12}; 0\ 0]$ and
  $R_{11} \in \mathbb{R}^{r \times r}$ nonsingular is
  `Matrix.IsPivotedQR.IsRankRevealing A Q R π r`, with the product by $\Pi$ written as
  `A.submatrix id π`. A complete orthogonal decomposition is `Matrix.IsCompleteOrthogonal`, and
  the basic solution $x_B$ is `Matrix.pivotedBasicSolution`.
* From §5.5.3 on, the matrix norm $\|\cdot\|_2$ is the spectral norm.

## Deviations from the source

* **§5.5.1** (typo). The source writes $z \in \operatorname{hull}(A)$ where
  $z \in \operatorname{null}(A)$ is meant. See `GolubVanLoan.Chapter05.minNorm_existsUnique`.
* **Equation (5.5.3)** (typo). The source prints $X \in \mathbb{R}^{m \times n}$; the unknown is
  $X \in \mathbb{R}^{n \times m}$. See `GolubVanLoan.Chapter05.equation_5_5_3`.
* **Example of §5.5.3** (typo). The source prints $(A + \delta A)^+$ with a spurious entry $1$ in
  position $(2, 1)$. See `GolubVanLoan.Chapter05.pinv_discontinuity`.
* **Equation (5.5.4)** (typo). The source prints $z \in \mathbb{R}^{n-2}$ for
  $z \in \mathbb{R}^{n-r}$. See `GolubVanLoan.Chapter05.equation_5_5_4`.
* **Theorem 5.5.3** (typo). The source calls $\tilde V_{11}$ the leading "$r$-by-$r$" principal
  submatrix of $P^T V$; it is $\tilde r$-by-$\tilde r$. See `GolubVanLoan.Chapter05.theorem_5_5_3`.
* **Theorem 5.5.3** (reading). The source leaves the hypothesis
  $\tilde r \le \operatorname{rank}(A)$ implicit; the statement assumes it. See
  `GolubVanLoan.Chapter05.theorem_5_5_3`.

## Not formalized

* **The second bound of §5.5.4.** Its middle term cannot be right as printed, and the source gives
  no derivation.
* **The display of the $\delta$-rank in §5.5.4.** It is misprinted; the definition is (5.4.5).
* **The flop table of §5.5.6.** Operation counts are out of scope for the library.
* **The example of an unstable subset.** It is a numerical example.
* **The remark that column pivoting tends to produce a well-conditioned $R_{11}$.** It is a
  heuristic.
-/

open Matrix WithLp

namespace GolubVanLoan.Chapter05

variable {m n : ℕ}

/-! ### §5.5.1 The minimum norm solution -/

section MinNorm

/-- **§5.5.1** of [golub2013matrix], the minimum norm solution. Let $A \in \mathbb{R}^{m \times n}$
and $b \in \mathbb{R}^m$. The set $\mathcal{X} = \{x \in \mathbb{R}^n : \|Ax - b\|_2 = \min\}$
of least-squares minimizers is convex, the vector $x_{LS} = A^+ b$ is a least-squares minimizer
of minimum 2-norm, and every least-squares minimizer of minimum 2-norm is equal to $A^+ b$.

**Typo.** The source writes $z \in \operatorname{hull}(A)$ in this subsection where
$z \in \operatorname{null}(A)$ is meant.

The minimizer of minimum 2-norm is `Matrix.IsMinNormLeastSquaresSolution`, and $x_{LS}$ is
`toEuclideanLin A.pinv b`. -/
theorem minNorm_existsUnique (A : Matrix (Fin m) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin m)) :
    Convex ℝ {x | IsLeastSquaresSolution A b x} ∧
      IsMinNormLeastSquaresSolution A b (toEuclideanLin A.pinv b) ∧
      ∀ x, IsMinNormLeastSquaresSolution A b x → x = toEuclideanLin A.pinv b :=
  ⟨convex_setOf_isLeastSquaresSolution A b, isMinNormLeastSquaresSolution_pinv A b,
    fun _ hx => hx.unique (isMinNormLeastSquaresSolution_pinv A b)⟩

/-- **§5.5.1** of [golub2013matrix], least squares through a complete orthogonal decomposition. Let
$A \in \mathbb{R}^{m \times n}$ and $b \in \mathbb{R}^m$, and let
$Q \in \mathbb{R}^{m \times m}$ and $Z \in \mathbb{R}^{n \times n}$ be orthogonal with
$$Q^T A Z = T = \begin{bmatrix} T_{11} & 0 \\ 0 & 0 \end{bmatrix},$$
where $T_{11} \in \mathbb{R}^{r \times r}$ is nonsingular. Write $Q^T b = [c; d]$ with
$c \in \mathbb{R}^r$. Then for every $x \in \mathbb{R}^n$, with $Z^T x = [w; y]$ and
$w \in \mathbb{R}^r$,
$$\|Ax - b\|_2^2 = \|T_{11} w - c\|_2^2 + \|d\|_2^2.$$
The vector $x_{LS} = Z [T_{11}^{-1} c; 0]$ is the least-squares minimizer of minimum 2-norm, and
$\|A x_{LS} - b\|_2 = \|d\|_2$.

The decomposition is `Matrix.IsCompleteOrthogonal A Q Z r`; then $r = \operatorname{rank}(A)$.
The block $T_{11}$ is a submatrix of `Qᵀ * A * Z`, the vector $[u; v]$ is `Matrix.blockVec`, and
the entries of $d$ are read through `Matrix.tailIdx`. -/
theorem minNorm_of_completeOrthogonal {A : Matrix (Fin m) (Fin n) ℝ}
    {Q : Matrix (Fin m) (Fin m) ℝ} {Z : Matrix (Fin n) (Fin n) ℝ} {r : ℕ}
    (h : IsCompleteOrthogonal A Q Z r) (b : EuclideanSpace ℝ (Fin m)) :
    (∀ x : EuclideanSpace ℝ (Fin n), ‖toEuclideanLin A x - b‖ ^ 2 =
      ∑ i : Fin r, (((Qᵀ * A * Z).submatrix (Fin.castLE h.le_rows) (Fin.castLE h.le_cols) *ᵥ
          fun k => (Zᵀ *ᵥ ofLp x) (Fin.castLE h.le_cols k)) i -
        (Qᵀ *ᵥ ofLp b) (Fin.castLE h.le_rows i)) ^ 2 +
      ∑ j : Fin (m - r), (Qᵀ *ᵥ ofLp b) (tailIdx h.le_rows j) ^ 2) ∧
    IsMinNormLeastSquaresSolution A b (toLp 2 (Z *ᵥ blockVec h.le_cols
      (((Qᵀ * A * Z).submatrix (Fin.castLE h.le_rows) (Fin.castLE h.le_cols))⁻¹ *ᵥ
        fun i => (Qᵀ *ᵥ ofLp b) (Fin.castLE h.le_rows i)) 0)) ∧
    ‖toEuclideanLin A (toLp 2 (Z *ᵥ blockVec h.le_cols
      (((Qᵀ * A * Z).submatrix (Fin.castLE h.le_rows) (Fin.castLE h.le_cols))⁻¹ *ᵥ
        fun i => (Qᵀ *ᵥ ofLp b) (Fin.castLE h.le_rows i)) 0)) - b‖ =
      ‖(toLp 2 fun j => (Qᵀ *ᵥ ofLp b) (tailIdx h.le_rows j) :
        EuclideanSpace ℝ (Fin (m - r)))‖ := by
  have hmin := h.isMinNormLeastSquaresSolution b
  simp only [conjTranspose_eq_transpose_of_trivial] at hmin
  refine ⟨fun x => ?_, hmin⟩
  have hsplit := norm_toEuclideanLin_sub_sq_eq_of_eq_mul h.mem_unitaryGroup_left h.le_rows
    h.eq_mul (fun i j hi => h.apply_eq_zero i j (Or.inl hi)) b x
  simp only [conjTranspose_eq_transpose_of_trivial, Real.norm_eq_abs, sq_abs] at hsplit
  rw [hsplit]
  have hz : ∀ (i : Fin m) (j : Fin n), r ≤ (j : ℕ) → (Qᵀ * A * Z) i j = 0 := fun i j hj => by
    simpa only [conjTranspose_eq_transpose_of_trivial] using h.apply_eq_zero i j (Or.inr hj)
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  rw [mulVec, dotProduct, sum_eq_sum_castLE_add_sum_tailIdx h.le_cols]
  have htail : ∑ j : Fin (n - r), (Qᵀ * A * Z) (Fin.castLE h.le_rows i) (tailIdx h.le_cols j) *
      (Zᵀ *ᵥ ofLp x) (tailIdx h.le_cols j) = 0 :=
    Finset.sum_eq_zero fun j _ => by rw [hz _ _ (by simp), zero_mul]
  rw [htail, add_zero]
  rfl

end MinNorm

/-! ### Theorem 5.5.1 and the pseudoinverse -/

section SVD

variable {A : Matrix (Fin m) (Fin n) ℝ} {U : Matrix (Fin m) (Fin m) ℝ} {σ : ℕ → ℝ}
  {V : Matrix (Fin n) (Fin n) ℝ}

/-- For an SVD $U^T A V = \Sigma$ of $A$ of any shape, $A^+ b = \sum_{j < \min(m, n)} (u_j^T b /
\sigma_j) v_j$, where a term with $\sigma_j = 0$ is zero. -/
private theorem pinv_mulVec_eq_sum_dite (h : IsSVD A U σ V) (b : Fin m → ℝ) :
    A.pinv *ᵥ b = ∑ j : Fin n,
      (if hj : (j : ℕ) < m then (U.col ⟨j, hj⟩ ⬝ᵥ b) / σ j else 0) • V.col j := by
  rw [h.pinv_eq, ← mulVec_mulVec, ← mulVec_mulVec]
  simp only [RCLike.ofReal_real_eq_id, id]
  have hD : ∀ j : Fin n, ((rectDiagonal fun i => (σ i)⁻¹ : Matrix (Fin n) (Fin m) ℝ) *ᵥ
      (star U *ᵥ b)) j = if hj : (j : ℕ) < m then (U.col ⟨j, hj⟩ ⬝ᵥ b) / σ j else 0 := by
    intro j
    simp only [mulVec, dotProduct, rectDiagonal, of_apply, ite_mul, zero_mul]
    split_ifs with hj
    · rw [Finset.sum_eq_single ⟨j, hj⟩ (fun i _ hi => by
        rw [ite_eq_right (fun e => hi (Fin.ext e.symm))]) (by simp)]
      simp only [↓reduceIte, star_apply, star_trivial, col_apply]
      rw [div_eq_inv_mul]
    · refine Finset.sum_eq_zero fun i _ => ?_
      rw [ite_eq_right (fun e => hj (by have := i.isLt; omega))]
  ext p
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, col_apply]
  change ∑ j, V p j * _ = _
  simp only [hD, mul_comm]

/-- **Equation (5.5.1)** of [golub2013matrix]. Let $U^T A V = \Sigma$ be an SVD of
$A \in \mathbb{R}^{m \times n}$ with $r = \operatorname{rank}(A)$, and let $b \in \mathbb{R}^m$.
Then the vector
$$x_{LS} = \sum_{i=1}^{r} \frac{u_i^T b}{\sigma_i} v_i$$
is equal to $A^+ b$, and it is the minimizer of $\|Ax - b\|_2$ that has the smallest 2-norm of
all minimizers.

The SVD is `Matrix.IsSVD A U σ V`, and $u_i$, $v_i$ are the columns `U.col (i - 1)` and
`V.col (i - 1)`. -/
theorem equation_5_5_1 (h : IsSVD A U σ V) (b : Fin m → ℝ) :
    ∑ i : Fin A.rank, ((U.col (Fin.castLE (rank_le_height A) i) ⬝ᵥ b) / σ i) •
        V.col (Fin.castLE (rank_le_width A) i) = A.pinv *ᵥ b ∧
      IsMinNormLeastSquaresSolution A (toLp 2 b)
        (toLp 2 (∑ i : Fin A.rank, ((U.col (Fin.castLE (rank_le_height A) i) ⬝ᵥ b) / σ i) •
          V.col (Fin.castLE (rank_le_width A) i))) := by
  have hsum : ∑ i : Fin A.rank, ((U.col (Fin.castLE (rank_le_height A) i) ⬝ᵥ b) / σ i) •
      V.col (Fin.castLE (rank_le_width A) i) = A.pinv *ᵥ b := by
    rw [pinv_mulVec_eq_sum_dite h b]
    set g : Fin n → Fin n → ℝ := fun j =>
      (if hj : (j : ℕ) < m then (U.col ⟨j, hj⟩ ⬝ᵥ b) / σ j else 0) • V.col j with hg
    have h1 : ∀ i : Fin A.rank, ((U.col (Fin.castLE (rank_le_height A) i) ⬝ᵥ b) / σ i) •
        V.col (Fin.castLE (rank_le_width A) i) = g (Fin.castLE (rank_le_width A) i) := by
      intro i
      have hi : ((Fin.castLE (rank_le_width A) i : Fin n) : ℕ) < m :=
        lt_of_lt_of_le i.isLt (rank_le_height A)
      simp only [hg, hi, ↓reduceDIte]
      rfl
    rw [Finset.sum_congr rfl fun i _ => h1 i, Fin.sum_castLE_eq_sum_ite]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs with hjr
    · rfl
    · simp only [hg]
      split_ifs with hjm
      · rw [h.singularValues_eq hjm j.isLt,
          (sortedSingularValues_eq_zero_iff_rank_le (A := A) _).2 (not_lt.1 hjr), div_zero,
          zero_smul]
      · rw [zero_smul]
  refine ⟨hsum, ?_⟩
  rw [hsum, ← toEuclideanLin_toLp]
  exact isMinNormLeastSquaresSolution_pinv A (toLp 2 b)

/-- **Equation (5.5.2)** of [golub2013matrix]. Let $U^T A V = \Sigma$ be an SVD of
$A \in \mathbb{R}^{m \times n}$ with $r = \operatorname{rank}(A)$, and let $b \in \mathbb{R}^m$.
The residual of $x_{LS} = A^+ b$ satisfies
$$\rho_{LS}^2 = \|A x_{LS} - b\|_2^2 = \sum_{i=r+1}^{m} (u_i^T b)^2.$$
-/
theorem equation_5_5_2 (h : IsSVD A U σ V) (b : Fin m → ℝ) :
    ‖toEuclideanLin A (toLp 2 (A.pinv *ᵥ b)) - toLp 2 b‖ ^ 2 =
      ∑ i ∈ Finset.univ.filter (fun i : Fin m => A.rank ≤ (i : ℕ)), (U.col i ⬝ᵥ b) ^ 2 := by
  rw [← toEuclideanLin_toLp, norm_sub_sq_pinv_eq_sum_of_isSVD h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [EuclideanSpace.inner_toLp_toLp, Real.norm_eq_abs, sq_abs]
  simp only [star_trivial, dotProduct_comm]
  rfl

/-- **Theorem 5.5.1** of [golub2013matrix]. Let $U^T A V = \Sigma$ be an SVD of
$A \in \mathbb{R}^{m \times n}$ with $r = \operatorname{rank}(A)$, and let $b \in \mathbb{R}^m$.
Then
$$x_{LS} = \sum_{i=1}^{r} \frac{u_i^T b}{\sigma_i} v_i$$
minimizes $\|Ax - b\|_2$ and has the smallest 2-norm of all minimizers. Moreover
$$\rho_{LS}^2 = \|A x_{LS} - b\|_2^2 = \sum_{i=r+1}^{m} (u_i^T b)^2.$$

The SVD is `Matrix.IsSVD A U σ V`. The proof combines `GolubVanLoan.Chapter05.equation_5_5_1`
and `GolubVanLoan.Chapter05.equation_5_5_2`. -/
theorem theorem_5_5_1 (h : IsSVD A U σ V) (b : Fin m → ℝ) :
    IsMinNormLeastSquaresSolution A (toLp 2 b)
        (toLp 2 (∑ i : Fin A.rank, ((U.col (Fin.castLE (rank_le_height A) i) ⬝ᵥ b) / σ i) •
          V.col (Fin.castLE (rank_le_width A) i))) ∧
      ‖toEuclideanLin A (toLp 2 (∑ i : Fin A.rank,
          ((U.col (Fin.castLE (rank_le_height A) i) ⬝ᵥ b) / σ i) •
            V.col (Fin.castLE (rank_le_width A) i))) - toLp 2 b‖ ^ 2 =
        ∑ i ∈ Finset.univ.filter (fun i : Fin m => A.rank ≤ (i : ℕ)), (U.col i ⬝ᵥ b) ^ 2 := by
  obtain ⟨hsum, hmin⟩ := equation_5_5_1 h b
  exact ⟨hmin, by rw [hsum]; exact equation_5_5_2 h b⟩

/-- **§5.5.2** of [golub2013matrix], the pseudoinverse from the SVD. Let $U^T A V = \Sigma$ be an
SVD of $A \in \mathbb{R}^{m \times n}$ with $r = \operatorname{rank}(A)$, and let
$b \in \mathbb{R}^m$. Then
$$A^+ = V \Sigma^+ U^T, \qquad \Sigma^+ = \operatorname{diag}(1/\sigma_1, \dots, 1/\sigma_r, 0,
  \dots, 0) \in \mathbb{R}^{n \times m}.$$
The vector $x_{LS} = A^+ b$ is the least-squares minimizer of minimum 2-norm, and $\rho_{LS} =
\|A x_{LS} - b\|_2 = \|(I - AA^+) b\|_2$. If $\operatorname{rank}(A) = n$, then
$A^+ = (A^T A)^{-1} A^T$.

The matrix $\Sigma^+$ is `Matrix.rectDiagonal` of $i \mapsto \sigma_i^{-1}$. In Lean
$0^{-1} = 0$, so the zero singular values give the zero entries. The hypothesis
$\operatorname{rank}(A) = n$ is `LinearIndependent ℝ Aᵀ`, that is, the columns of $A$ are
linearly independent. The case of a nonsingular square matrix is
`GolubVanLoan.Chapter05.pseudoinverse_eq_inv`. -/
theorem pseudoinverse_eq_svd (h : IsSVD A U σ V) (b : Fin m → ℝ) :
    A.pinv = V * (rectDiagonal fun i => (σ i)⁻¹ : Matrix (Fin n) (Fin m) ℝ) * Uᵀ ∧
      IsMinNormLeastSquaresSolution A (toLp 2 b) (toLp 2 (A.pinv *ᵥ b)) ∧
      ‖toEuclideanLin A (toLp 2 (A.pinv *ᵥ b)) - toLp 2 b‖ =
        ‖(toLp 2 ((1 - A * A.pinv) *ᵥ b) : EuclideanSpace ℝ (Fin m))‖ ∧
      (LinearIndependent ℝ Aᵀ → A.pinv = (Aᵀ * A)⁻¹ * Aᵀ) := by
  refine ⟨?_, ?_, ?_, fun hA => ?_⟩
  · have := h.pinv_eq
    simpa only [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial,
      RCLike.ofReal_real_eq_id, id] using this
  · rw [← toEuclideanLin_toLp]; exact isMinNormLeastSquaresSolution_pinv A (toLp 2 b)
  · rw [toEuclideanLin_toLp, ← norm_neg, neg_sub, ← WithLp.toLp_sub, mulVec_mulVec,
      sub_mulVec, one_mulVec]
  · have := pinv_eq_inv_conjTranspose_mul_self_mul_conjTranspose hA
    rwa [conjTranspose_eq_transpose_of_trivial] at this

/-- **§5.5.2** of [golub2013matrix]. If $B \in \mathbb{R}^{n \times n}$ is nonsingular, then
$B^+ = B^{-1}$. -/
theorem pseudoinverse_eq_inv {B : Matrix (Fin n) (Fin n) ℝ} (hB : IsUnit B) : B.pinv = B⁻¹ :=
  pinv_eq_inv hB

/-- **Equation (5.5.3)** of [golub2013matrix]. Let $A \in \mathbb{R}^{m \times n}$. The
pseudoinverse $A^+$ is a solution of
$$\min_{X \in \mathbb{R}^{n \times m}} \|AX - I_m\|_F,$$
and it is the unique solution of minimum Frobenius norm: every $X \in \mathbb{R}^{n \times m}$
with $\|AX - I_m\|_F = \|AA^+ - I_m\|_F$ satisfies $\|A^+\|_F \le \|X\|_F$, with equality only
for $X = A^+$.

**Typo.** The source prints $X \in \mathbb{R}^{m \times n}$. The product $AX$ requires
$X \in \mathbb{R}^{n \times m}$.

The Frobenius norm is put on the matrix types by `Matrix.frobeniusNormedAddCommGroup`. The proof
specializes `Matrix.isMinOn_norm_mul_sub_one_pinv`. -/
theorem equation_5_5_3 (A : Matrix (Fin m) (Fin n) ℝ) :
    letI := Matrix.frobeniusNormedAddCommGroup (m := Fin m) (n := Fin m) (α := ℝ)
    letI := Matrix.frobeniusNormedAddCommGroup (m := Fin n) (n := Fin m) (α := ℝ)
    (∀ X : Matrix (Fin n) (Fin m) ℝ, ‖A * A.pinv - 1‖ ≤ ‖A * X - 1‖) ∧
      ∀ X : Matrix (Fin n) (Fin m) ℝ,
        ‖A * X - 1‖ = ‖A * A.pinv - 1‖ → ‖A.pinv‖ ≤ ‖X‖ ∧ (‖X‖ = ‖A.pinv‖ → X = A.pinv) :=
  ⟨fun X => isMinOn_iff.1 (isMinOn_norm_mul_sub_one_pinv A).1 X (Set.mem_univ X),
    (isMinOn_norm_mul_sub_one_pinv A).2⟩

/-- **§5.5.2** of [golub2013matrix], the Moore–Penrose conditions. Let
$A \in \mathbb{R}^{m \times n}$. Then $A^+$ is the unique $X \in \mathbb{R}^{n \times m}$ that
satisfies

(i) $AXA = A$, (ii) $XAX = X$, (iii) $(AX)^T = AX$, (iv) $(XA)^T = XA$.

Moreover, $AA^+$ is the orthogonal projection onto $\operatorname{ran}(A)$.

The orthogonal projection is `Submodule.starProjection` of the range of
`Matrix.toEuclideanLin A`. -/
theorem moorePenrose (A : Matrix (Fin m) (Fin n) ℝ) :
    A * A.pinv * A = A ∧ A.pinv * A * A.pinv = A.pinv ∧ (A * A.pinv)ᵀ = A * A.pinv ∧
      (A.pinv * A)ᵀ = A.pinv * A ∧
      (∀ X : Matrix (Fin n) (Fin m) ℝ, A * X * A = A → X * A * X = X → (A * X)ᵀ = A * X →
        (X * A)ᵀ = X * A → X = A.pinv) ∧
      toEuclideanLin (A * A.pinv) = ((toEuclideanLin A).range.starProjection : _ →ₗ[ℝ] _) := by
  have h3 : (A * A.pinv)ᵀ = A * A.pinv := by
    have := (isHermitian_mul_pinv (A := A)).eq
    rwa [conjTranspose_eq_transpose_of_trivial] at this
  have h4 : (A.pinv * A)ᵀ = A.pinv * A := by
    have := (isHermitian_pinv_mul (A := A)).eq
    rwa [conjTranspose_eq_transpose_of_trivial] at this
  refine ⟨mul_pinv_mul_self A, pinv_mul_self_mul_pinv A, h3, h4, fun X h1 h2 h3' h4' =>
    pinv_unique A h1 h2 ?_ ?_, mul_pinv_eq_starProjection A⟩
  · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]; exact h3'
  · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]; exact h4'

end SVD

/-! ### §5.5.3 The perturbation of the pseudoinverse -/

section PinvPerturbation

open scoped Matrix.Norms.Frobenius

/-- **§5.5.3** of [golub2013matrix], the perturbation of the pseudoinverse (Wedin 1973, Stewart
1975). For all $A, \delta A \in \mathbb{R}^{m \times n}$,
$$\|(A + \delta A)^+ - A^+\|_F \le 2 \|\delta A\|_F \max\{\|A^+\|_2^2, \|(A + \delta
  A)^+\|_2^2\}.$$

The statement has no hypothesis on the ranks of $A$ and $A + \delta A$. The Frobenius norm comes
from the scoped instance `Matrix.Norms.Frobenius`, and the spectral norm $\|\cdot\|_2$ is
`Matrix.lpOpNorm 2`. -/
theorem pinv_perturbation (A δA : Matrix (Fin m) (Fin n) ℝ) :
    ‖(A + δA).pinv - A.pinv‖ ≤ 2 * ‖δA‖ *
      max (lpOpNorm 2 A.pinv ^ 2) (lpOpNorm 2 (A + δA).pinv ^ 2) :=
  frobenius_norm_pinv_sub_le A δA

end PinvPerturbation

/-- The matrix $A = \begin{bmatrix} 1 & 0 \\ 0 & 0 \\ 0 & 0 \end{bmatrix} \in \mathbb{R}^{3 \times
2}$ of the example in §5.5.3 of [golub2013matrix]. -/
def pinvExampleA : Matrix (Fin 3) (Fin 2) ℝ := !![1, 0; 0, 0; 0, 0]

/-- The perturbation $\delta A = \begin{bmatrix} 0 & 0 \\ 0 & \epsilon \\ 0 & 0 \end{bmatrix} \in
\mathbb{R}^{3 \times 2}$ of the example in §5.5.3 of [golub2013matrix]. -/
def pinvExampleE (ε : ℝ) : Matrix (Fin 3) (Fin 2) ℝ := !![0, 0; 0, ε; 0, 0]

/-- For $\epsilon \neq 0$, the pseudoinverse of $A + \delta A$ in the example of §5.5.3 is
$\begin{bmatrix} 1 & 0 & 0 \\ 0 & 1/\epsilon & 0 \end{bmatrix}$. -/
theorem pinv_pinvExample {ε : ℝ} (hε : ε ≠ 0) :
    (pinvExampleA + pinvExampleE ε).pinv = !![1, 0, 0; 0, 1 / ε, 0] := by
  symm
  refine pinv_unique (A := pinvExampleA + pinvExampleE ε) ?_ ?_ ?_ ?_
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pinvExampleA, pinvExampleE, Matrix.mul_apply, Fin.sum_univ_succ, hε]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pinvExampleA, pinvExampleE, Matrix.mul_apply, Fin.sum_univ_succ, hε]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pinvExampleA, pinvExampleE, Matrix.mul_apply, Fin.sum_univ_succ, hε]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pinvExampleA, pinvExampleE, Matrix.mul_apply, Fin.sum_univ_succ, hε]

/-- The pseudoinverse of the matrix $A$ in the example of §5.5.3 is $\begin{bmatrix} 1 & 0 & 0 \\ 0
& 0 & 0 \end{bmatrix}$. -/
theorem pinv_pinvExampleA : pinvExampleA.pinv = !![1, 0, 0; 0, 0, 0] := by
  symm
  refine pinv_unique (A := pinvExampleA) ?_ ?_ ?_ ?_
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [pinvExampleA, Matrix.mul_apply, Fin.sum_univ_succ]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [pinvExampleA, Matrix.mul_apply, Fin.sum_univ_succ]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [pinvExampleA, Matrix.mul_apply, Fin.sum_univ_succ]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [pinvExampleA, Matrix.mul_apply, Fin.sum_univ_succ]

open scoped Matrix.Norms.L2Operator in
/-- **§5.5.3** of [golub2013matrix], the example of discontinuity. Let $\epsilon > 0$,
$$A = \begin{bmatrix} 1 & 0 \\ 0 & 0 \\ 0 & 0 \end{bmatrix}, \qquad \delta A = \begin{bmatrix} 0
  & 0 \\ 0 & \epsilon \\ 0 & 0 \end{bmatrix}.$$
Then
$$A^+ = \begin{bmatrix} 1 & 0 & 0 \\ 0 & 0 & 0 \end{bmatrix}, \qquad (A + \delta A)^+ =
  \begin{bmatrix} 1 & 0 & 0 \\ 0 & 1/\epsilon & 0 \end{bmatrix},$$
and $\|A^+ - (A + \delta A)^+\|_2 = 1/\epsilon$. Hence the map $B \mapsto B^+$ on
$\mathbb{R}^{3 \times 2}$ is not continuous at $A$: "$x_{LS}$ is not even a continuous function
of the data".

**Typo.** The source prints $(A + \delta A)^+$ with an entry $1$ in position $(2, 1)$. This
entry is $0$.

The matrices are `GolubVanLoan.Chapter05.pinvExampleA` and
`GolubVanLoan.Chapter05.pinvExampleE`, and $\|\cdot\|_2$ is the spectral norm. -/
theorem pinv_discontinuity {ε : ℝ} (hε : 0 < ε) :
    pinvExampleA.pinv = !![1, 0, 0; 0, 0, 0] ∧
      (pinvExampleA + pinvExampleE ε).pinv = !![1, 0, 0; 0, 1 / ε, 0] ∧
      ‖pinvExampleA.pinv - (pinvExampleA + pinvExampleE ε).pinv‖ = 1 / ε ∧
      ¬ ContinuousAt (fun B : Matrix (Fin 3) (Fin 2) ℝ => B.pinv) pinvExampleA := by
  refine ⟨pinv_pinvExampleA, pinv_pinvExample hε.ne', ?_, ?_⟩
  · rw [pinv_pinvExampleA, pinv_pinvExample hε.ne']
    have hD : (!![1, 0, 0; 0, 0, 0] - !![1, 0, 0; 0, 1 / ε, 0] : Matrix (Fin 2) (Fin 3) ℝ) =
        !![0, 0, 0; 0, -(1 / ε), 0] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    rw [hD]
    set M : Matrix (Fin 2) (Fin 3) ℝ := !![0, 0, 0; 0, -(1 / ε), 0] with hM
    have hMM : Mᴴᴴ * Mᴴ = diagonal ![0, (1 / ε) ^ 2] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hM, Matrix.mul_apply, Fin.sum_univ_succ, sq]
    have hsq : ‖M‖ * ‖M‖ = (1 / ε) ^ 2 := by
      rw [← l2_opNorm_conjTranspose M, ← l2_opNorm_conjTranspose_mul_self, hMM,
        l2_opNorm_diagonal]
      refine le_antisymm ((pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_) ?_
      · fin_cases i <;> simp [sq_nonneg]
      · have := norm_le_pi_norm (![0, (1 / ε) ^ 2] : Fin 2 → ℝ) 1
        simpa using this
    have h0 : 0 ≤ ‖M‖ := norm_nonneg _
    nlinarith [show 0 < 1 / ε by positivity]
  · intro hc
    have hE : ∀ t : ℝ, pinvExampleA + pinvExampleE t =
        pinvExampleA + t • (!![0, 0; 0, 1; 0, 0] : Matrix (Fin 3) (Fin 2) ℝ) := by
      intro t
      congr 1
      ext i j
      fin_cases i <;> fin_cases j <;> simp [pinvExampleE]
    have hf : ContinuousAt (fun t : ℝ => (pinvExampleA + pinvExampleE t).pinv 1 1) 0 := by
      simp only [hE]
      have hg : Continuous fun t : ℝ =>
          pinvExampleA + t • (!![0, 0; 0, 1; 0, 0] : Matrix (Fin 3) (Fin 2) ℝ) := by fun_prop
      have hpt : pinvExampleA + (0 : ℝ) • (!![0, 0; 0, 1; 0, 0] : Matrix (Fin 3) (Fin 2) ℝ) =
          pinvExampleA := by rw [zero_smul, add_zero]
      have := ContinuousAt.comp_of_eq hc hg.continuousAt hpt
      exact ((continuous_apply 1).comp (continuous_apply 1)).continuousAt.comp this
    rw [Metric.continuousAt_iff] at hf
    obtain ⟨δ, hδ, hδf⟩ := hf 1 one_pos
    set t := min (δ / 2) (1 / 2) with ht
    have ht0 : 0 < t := by positivity
    have htδ : dist t 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos ht0]
      exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have := hδf htδ
    have hE0 : pinvExampleE 0 = 0 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [pinvExampleE]
    simp only [hE0, add_zero, pinv_pinvExampleA, pinv_pinvExample ht0.ne'] at this
    simp only [of_apply, cons_val', cons_val_one, cons_val_zero, empty_val',
      cons_val_fin_one, Real.dist_eq, sub_zero] at this
    have ht2 : t ≤ 1 / 2 := min_le_right _ _
    rw [abs_of_pos (by positivity)] at this
    rw [div_lt_one ht0] at this
    linarith

/-! ### §5.5.4 The truncated SVD solution -/

section TruncatedSVD

/-- **§5.5.4** of [golub2013matrix], the truncated SVD solution. Let
$\hat U \in \mathbb{R}^{m \times m}$ and $\hat V \in \mathbb{R}^{n \times n}$ have columns
$\hat u_i$ and $\hat v_i$, let $\hat\sigma_1, \hat\sigma_2, \dots$ be real numbers, let
$\hat r \ge 0$, and let $b \in \mathbb{R}^m$. The **truncated SVD solution** is
$$x_{\hat r} = \sum_{i=1}^{\hat r} \frac{\hat u_i^T b}{\hat\sigma_i} \hat v_i.$$

In the source, $\hat U$, $\hat\Sigma = \operatorname{diag}(\hat\sigma_i)$ and $\hat V$ are
computed factors and $\hat r$ is an accepted $\delta$-rank. The 0-based sum runs over the
indices $i < \hat r$, and an index $i \ge \min(m, n)$ gives no term. A term with
$\hat\sigma_i = 0$ is zero, because division by zero gives zero in Lean. -/
noncomputable def truncatedSVDSolution (U : Matrix (Fin m) (Fin m) ℝ) (σ : ℕ → ℝ)
    (V : Matrix (Fin n) (Fin n) ℝ) (r : ℕ) (b : Fin m → ℝ) : Fin n → ℝ :=
  ∑ i : Fin n, if h : (i : ℕ) < r ∧ (i : ℕ) < m then ((U.col ⟨i, h.2⟩ ⬝ᵥ b) / σ i) • V.col i
    else 0

/-- The Cauchy–Schwarz inequality $|x^T y| \le \|x\|_2 \|y\|_2$ for real vectors. -/
private theorem abs_dotProduct_le_norm {k : ℕ} (x y : Fin k → ℝ) :
    |x ⬝ᵥ y| ≤
      ‖(toLp 2 x : EuclideanSpace ℝ (Fin k))‖ * ‖(toLp 2 y : EuclideanSpace ℝ (Fin k))‖ := by
  have := abs_real_inner_le_norm (toLp 2 x : EuclideanSpace ℝ (Fin k)) (toLp 2 y)
  simpa [EuclideanSpace.inner_toLp_toLp, dotProduct_comm] using this

/-- The columns of an orthogonal matrix are orthonormal. -/
private theorem col_dotProduct_col_of_mem {k : ℕ} {Q : Matrix (Fin k) (Fin k) ℝ}
    (hQ : Q ∈ unitaryGroup (Fin k) ℝ) (i j : Fin k) :
    Q.col i ⬝ᵥ Q.col j = (1 : Matrix (Fin k) (Fin k) ℝ) i j := by
  have := congrFun (congrFun (mem_unitaryGroup_iff'.1 hQ) i) j
  rw [← this]
  simp [Matrix.mul_apply, dotProduct, col_apply]

/-- The columns of an orthogonal matrix have Euclidean norm $1$. -/
private theorem norm_col_of_mem {k : ℕ} {Q : Matrix (Fin k) (Fin k) ℝ}
    (hQ : Q ∈ unitaryGroup (Fin k) ℝ) (j : Fin k) :
    ‖(toLp 2 (Q.col j) : EuclideanSpace ℝ (Fin k))‖ = 1 := by
  have h1 := col_dotProduct_col_of_mem hQ j j
  rw [one_apply_eq, dotProduct_self_eq_norm_sq] at h1
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h1

/-- **§5.5.4** of [golub2013matrix], the error of the truncated SVD solution. Let
$A \in \mathbb{R}^{m \times n}$ with $n \le m$, and let $W^T A Z = \Sigma =
\operatorname{diag}(\sigma_1, \dots, \sigma_n)$ be an SVD of $A$, with columns $w_i$ of $W$ and
$z_i$ of $Z$. Let $\hat U \in \mathbb{R}^{m \times m}$ and $\hat V \in \mathbb{R}^{n \times n}$
have columns $\hat u_i$ and $\hat v_i$, let $\hat r \le n$ with $\sigma_{\hat r} > 0$, and let
$\epsilon \ge 0$ with
$$\|w_i - \hat u_i\|_2 \le \epsilon, \qquad \|z_i - \hat v_i\|_2 \le \epsilon \qquad (1 \le i
  \le \hat r).$$
Then for every $b \in \mathbb{R}^m$ the truncated SVD solution $x_{\hat r}$ formed from
$\hat U$, $\Sigma$ and $\hat V$ satisfies
$$\|x_{\hat r} - x_{LS}\|_2 \le \frac{\hat r}{\sigma_{\hat r}} 2 (1 + \epsilon) \epsilon
  \|b\|_2 + \sqrt{\sum_{i=\hat r+1}^{n} \left(\frac{w_i^T b}{\sigma_i}\right)^2},$$
where $x_{LS} = A^+ b$.

The source makes the simplifying assumptions $r = n$ and $\Delta A = 0$ in (5.4.4), so that
$\hat\Sigma = \Sigma = W^T A Z$ with $W$ and $Z$ orthogonal; here this is an SVD
`Matrix.IsSVD A W σ Z` with $n \le m$. The hypothesis on $\sigma_{\hat r}$ is stated for the
0-based `σ (r - 1)`, so for $\hat r = 0$ it reads $\sigma_1 > 0$. A term with $\sigma_i = 0$ in
the last sum is zero, because division by zero gives zero in Lean. -/
theorem norm_truncatedSVDSolution_sub_le {A : Matrix (Fin m) (Fin n) ℝ}
    {W : Matrix (Fin m) (Fin m) ℝ} {σ : ℕ → ℝ} {Z : Matrix (Fin n) (Fin n) ℝ}
    (h : IsSVD A W σ Z) (hnm : n ≤ m) {r : ℕ} (hr : r ≤ n) (hσ : 0 < σ (r - 1))
    {Uh : Matrix (Fin m) (Fin m) ℝ} {Vh : Matrix (Fin n) (Fin n) ℝ} {ε : ℝ} (hε : 0 ≤ ε)
    (hU : ∀ i : Fin n, (i : ℕ) < r → ‖(toLp 2 (W.col (Fin.castLE hnm i) -
      Uh.col (Fin.castLE hnm i)) : EuclideanSpace ℝ (Fin m))‖ ≤ ε)
    (hV : ∀ i : Fin n, (i : ℕ) < r →
      ‖(toLp 2 (Z.col i - Vh.col i) : EuclideanSpace ℝ (Fin n))‖ ≤ ε)
    (b : Fin m → ℝ) :
    ‖(toLp 2 (truncatedSVDSolution Uh σ Vh r b - A.pinv *ᵥ b) : EuclideanSpace ℝ (Fin n))‖ ≤
      r / σ (r - 1) * (2 * (1 + ε) * ε * ‖(toLp 2 b : EuclideanSpace ℝ (Fin m))‖) +
        √(∑ i ∈ Finset.univ.filter (fun i : Fin n => r ≤ (i : ℕ)),
          ((W.col (Fin.castLE hnm i) ⬝ᵥ b) / σ i) ^ 2) := by
  set nb := ‖(toLp 2 b : EuclideanSpace ℝ (Fin m))‖ with hnb
  set K := 2 * (1 + ε) * ε * nb with hK
  -- the two sums of the book's decomposition
  set D : Fin n → Fin n → ℝ := fun j => if (j : ℕ) < r then
      ((Uh.col (Fin.castLE hnm j) ⬝ᵥ b) / σ j) • Vh.col j -
        ((W.col (Fin.castLE hnm j) ⬝ᵥ b) / σ j) • Z.col j else 0 with hD
  set a : Fin n → ℝ := fun j => if r ≤ (j : ℕ) then (W.col (Fin.castLE hnm j) ⬝ᵥ b) / σ j
    else 0 with ha
  have hZa : Z *ᵥ a = ∑ j, a j • Z.col j := by
    ext p
    simp only [mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, col_apply,
      mul_comm]
  have hsplit : truncatedSVDSolution Uh σ Vh r b - A.pinv *ᵥ b = ∑ j, D j - Z *ᵥ a := by
    rw [pinv_mulVec_eq_sum_of_isSVD h hnm b, truncatedSVDSolution, hZa,
      ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hjm : (j : ℕ) < m := lt_of_lt_of_le j.isLt hnm
    by_cases hj : (j : ℕ) < r
    · simp only [hD, ha, hj, hjm, and_self, ↓reduceDIte, ↓reduceIte, not_le.2 hj, zero_smul,
        sub_zero]
      rfl
    · simp only [hD, ha, hj, false_and, ↓reduceDIte, ↓reduceIte, not_lt.1 hj]
  have hWu := h.mem_unitaryGroup_left
  have hZu := h.mem_unitaryGroup_right
  -- each term of the first sum
  have hDj : ∀ j : Fin n, ‖(toLp 2 (D j) : EuclideanSpace ℝ (Fin n))‖ ≤
      if (j : ℕ) < r then K / σ (r - 1) else 0 := by
    intro j
    by_cases hj : (j : ℕ) < r
    · simp only [hD, hj, ↓reduceIte]
      set u := Uh.col (Fin.castLE hnm j)
      set w := W.col (Fin.castLE hnm j)
      set v := Vh.col j
      set z := Z.col j
      have hσj : σ (r - 1) ≤ σ j := h.antitone (by omega)
      have hσj0 : 0 < σ (j : ℕ) := lt_of_lt_of_le hσ hσj
      have hid : ((u ⬝ᵥ b) / σ j) • v - ((w ⬝ᵥ b) / σ j) • z =
          (σ j)⁻¹ • ((u ⬝ᵥ b) • (v - z) + ((u - w) ⬝ᵥ b) • z) := by
        rw [sub_dotProduct, smul_sub, sub_smul, div_eq_inv_mul, div_eq_inv_mul, mul_smul,
          mul_smul, smul_add, smul_sub, smul_sub]
        abel
      have hw : ‖(toLp 2 w : EuclideanSpace ℝ (Fin m))‖ = 1 := norm_col_of_mem hWu _
      have hz : ‖(toLp 2 z : EuclideanSpace ℝ (Fin n))‖ = 1 := norm_col_of_mem hZu _
      have huw : ‖(toLp 2 (u - w) : EuclideanSpace ℝ (Fin m))‖ ≤ ε := by
        rw [← neg_sub, toLp_neg, norm_neg]
        exact hU j hj
      have hvz : ‖(toLp 2 (v - z) : EuclideanSpace ℝ (Fin n))‖ ≤ ε := by
        rw [← neg_sub, toLp_neg, norm_neg]
        exact hV j hj
      have hu : ‖(toLp 2 u : EuclideanSpace ℝ (Fin m))‖ ≤ 1 + ε := by
        have : u = w + (u - w) := by abel
        rw [this, toLp_add]
        exact (norm_add_le _ _).trans (by rw [hw]; linarith)
      have hub : |u ⬝ᵥ b| ≤ (1 + ε) * nb :=
        (abs_dotProduct_le_norm u b).trans
          (mul_le_mul_of_nonneg_right hu (norm_nonneg _))
      have huwb : |(u - w) ⬝ᵥ b| ≤ ε * nb :=
        (abs_dotProduct_le_norm _ b).trans
          (mul_le_mul_of_nonneg_right huw (norm_nonneg _))
      rw [hid, toLp_smul, norm_smul, toLp_add, toLp_smul, toLp_smul, Real.norm_eq_abs,
        abs_inv, abs_of_pos hσj0]
      have hsum : ‖(toLp 2 ((u ⬝ᵥ b) • (v - z)) : EuclideanSpace ℝ (Fin n)) +
          toLp 2 (((u - w) ⬝ᵥ b) • z)‖ ≤ K := by
        refine (norm_add_le _ _).trans ?_
        rw [toLp_smul, toLp_smul, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, hz,
          mul_one]
        have hnb0 : 0 ≤ nb := norm_nonneg _
        have h1 : |u ⬝ᵥ b| * ‖(toLp 2 (v - z) : EuclideanSpace ℝ (Fin n))‖ ≤ (1 + ε) * nb * ε :=
          mul_le_mul hub hvz (norm_nonneg _) (by positivity)
        have h2 : ε * nb ≤ (1 + ε) * ε * nb := by nlinarith [mul_nonneg hε hnb0]
        rw [hK]
        nlinarith
      have hK0 : 0 ≤ K := by positivity
      calc (σ j)⁻¹ * ‖(toLp 2 ((u ⬝ᵥ b) • (v - z)) : EuclideanSpace ℝ (Fin n)) +
            toLp 2 (((u - w) ⬝ᵥ b) • z)‖ ≤ (σ j)⁻¹ * K :=
            mul_le_mul_of_nonneg_left hsum (inv_nonneg.2 hσj0.le)
        _ ≤ (σ (r - 1))⁻¹ * K :=
            mul_le_mul_of_nonneg_right ((inv_le_inv₀ hσj0 hσ).2 hσj) hK0
        _ = K / σ (r - 1) := by rw [div_eq_inv_mul]
    · simp [hD, hj]
  -- the first sum
  have hfirst : ‖(toLp 2 (∑ j, D j) : EuclideanSpace ℝ (Fin n))‖ ≤ r / σ (r - 1) * K := by
    rw [toLp_sum]
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun j _ => hDj j).trans (le_of_eq ?_))
    rw [← Fin.sum_castLE_eq_sum_ite hr (fun _ => K / σ (r - 1))]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  -- the tail
  have hZZ : Zᵀ * Z = 1 := by
    have := mem_unitaryGroup_iff'.1 hZu
    rwa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at this
  have htail : ‖(toLp 2 (Z *ᵥ a) : EuclideanSpace ℝ (Fin n))‖ =
      √(∑ i ∈ Finset.univ.filter (fun i : Fin n => r ≤ (i : ℕ)),
        ((W.col (Fin.castLE hnm i) ⬝ᵥ b) / σ i) ^ 2) := by
    have h1 : (Z *ᵥ a) ⬝ᵥ (Z *ᵥ a) = a ⬝ᵥ a := by
      rw [dotProduct_mulVec, ← vecMul_transpose, vecMul_vecMul, hZZ, vecMul_one]
    have h2 : a ⬝ᵥ a = ∑ i ∈ Finset.univ.filter (fun i : Fin n => r ≤ (i : ℕ)),
        ((W.col (Fin.castLE hnm i) ⬝ᵥ b) / σ i) ^ 2 := by
      rw [Finset.sum_filter, dotProduct]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [ha]
      split_ifs <;> ring
    rw [← h2, ← h1, dotProduct_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  rw [hsplit, toLp_sub, ← htail]
  exact (norm_sub_le _ _).trans (add_le_add hfirst le_rfl)

end TruncatedSVD

/-! ### §5.5.5 Basic solutions via QR with column pivoting -/

section Basic

open scoped Matrix.Norms.L2Operator

variable {A : Matrix (Fin m) (Fin n) ℝ} {Q : Matrix (Fin m) (Fin m) ℝ}
  {R : Matrix (Fin m) (Fin n) ℝ} {π : Equiv.Perm (Fin n)} {r : ℕ}

/-- **§5.5.5** of [golub2013matrix], basic solutions via QR with column pivoting. Let
$A \in \mathbb{R}^{m \times n}$ have a QR factorization with column pivoting $A \Pi = QR$ as in
(5.4.6), with
$$R = \begin{bmatrix} R_{11} & R_{12} \\ 0 & 0 \end{bmatrix}$$
and $R_{11} \in \mathbb{R}^{r \times r}$ nonsingular (then $r = \operatorname{rank}(A)$). Let
$b \in \mathbb{R}^m$, and write $Q^T b = [c; d]$ with $c \in \mathbb{R}^r$. For every
$x \in \mathbb{R}^n$, with $\Pi^T x = [y; z]$ and $y \in \mathbb{R}^r$,
$$\|Ax - b\|_2^2 = \|R_{11} y + R_{12} z - c\|_2^2 + \|d\|_2^2.$$
Hence $x$ is a least-squares minimizer if and only if $R_{11} y + R_{12} z = c$, that is,
$x = \Pi [R_{11}^{-1}(c - R_{12} z); z]$. The basic solution $x_B = \Pi [R_{11}^{-1} c; 0]$ is a
least-squares minimizer, and it has at most $r$ nonzero components.

The factorization is `Matrix.IsPivotedQR.IsRankRevealing A Q R π r`, and $x_B$ is
`Matrix.pivotedBasicSolution`. The vector $R_{11} y + R_{12} z$ is the first $r$ entries of
$R \Pi^T x$, where $\Pi^T x$ is `x ∘ π`. The bound on the nonzero components is stated as: the
entries of $x_B$ at the positions $\pi(r), \dots, \pi(n - 1)$ are zero. -/
theorem basicSolution (h : IsPivotedQR.IsRankRevealing A Q R π r)
    (b : EuclideanSpace ℝ (Fin m)) :
    (∀ x : EuclideanSpace ℝ (Fin n), ‖toEuclideanLin A x - b‖ ^ 2 =
      ∑ i : Fin r, ((R *ᵥ (ofLp x ∘ π)) (Fin.castLE h.le_rows i) -
        (Qᵀ *ᵥ ofLp b) (Fin.castLE h.le_rows i)) ^ 2 +
      ∑ j : Fin (m - r), (Qᵀ *ᵥ ofLp b) (tailIdx h.le_rows j) ^ 2) ∧
    (∀ x : EuclideanSpace ℝ (Fin n), IsLeastSquaresSolution A b x ↔ ∀ i : Fin r,
      (R *ᵥ (ofLp x ∘ π)) (Fin.castLE h.le_rows i) = (Qᵀ *ᵥ ofLp b) (Fin.castLE h.le_rows i)) ∧
    IsLeastSquaresSolution A b (pivotedBasicSolution Q R π h.le_rows h.le_cols b) ∧
    ∀ j : Fin (n - r), pivotedBasicSolution Q R π h.le_rows h.le_cols b (π (tailIdx h.le_cols j)) =
      0 := by
  refine ⟨fun x => ?_, fun x => ?_, (h.isLeastSquaresSolution_basic b).1,
    (h.isLeastSquaresSolution_basic b).2⟩
  · have hsplit := norm_toEuclideanLin_sub_sq_eq_of_eq_mul h.isQR.mem_unitaryGroup h.le_rows
      h.eq_mul h.apply_eq_zero b x
    simpa only [one_submatrix_mulVec, conjTranspose_eq_transpose_of_trivial, Real.norm_eq_abs,
      sq_abs] using hsplit
  · have := h.isLeastSquaresSolution_iff (b := b) (x := x)
    simpa only [conjTranspose_eq_transpose_of_trivial] using this

/-- **Equation (5.5.4)** of [golub2013matrix]. In the setting of
`GolubVanLoan.Chapter05.basicSolution`, the minimum-norm solution $x_{LS} = A^+ b$ satisfies
$$\|x_{LS}\|_2 = \min_{z \in \mathbb{R}^{n-r}} \left\| x_B - \Pi \begin{bmatrix} R_{11}^{-1}
  R_{12} \\ -I_{n-r} \end{bmatrix} z \right\|_2.$$

**Typo.** The source prints $z \in \mathbb{R}^{n-2}$.

The minimum is stated as the infimum over $z$. -/
theorem equation_5_5_4 (h : IsPivotedQR.IsRankRevealing A Q R π r)
    (b : EuclideanSpace ℝ (Fin m)) :
    ‖toEuclideanLin A.pinv b‖ = ⨅ z : Fin (n - r) → ℝ,
      ‖pivotedBasicSolution Q R π h.le_rows h.le_cols b - toLp 2 (blockVec h.le_cols
        (((R.submatrix (Fin.castLE h.le_rows) (Fin.castLE h.le_cols))⁻¹ *
          R.submatrix (Fin.castLE h.le_rows) (tailIdx h.le_cols)) *ᵥ z) (-z) ∘ π.symm)‖ :=
  h.norm_minNorm_eq_iInf b

/-- **§5.5.5** of [golub2013matrix]. In the setting of `GolubVanLoan.Chapter05.basicSolution`, if
$R_{12} = 0$, then $x_B = x_{LS} = A^+ b$ for every $b$. This is the converse of the remark of
the source that "the basic solution is not the minimal 2-norm solution unless the submatrix
$R_{12}$ is zero". -/
theorem basicSolution_eq_pinv_of_eq_zero (h : IsPivotedQR.IsRankRevealing A Q R π r)
    (hR : R.submatrix (Fin.castLE h.le_rows) (tailIdx h.le_cols) = 0)
    (b : EuclideanSpace ℝ (Fin m)) :
    pivotedBasicSolution Q R π h.le_rows h.le_cols b = toEuclideanLin A.pinv b := by
  obtain ⟨-, hle⟩ := h.norm_basic_le b
  rw [hR, Matrix.mul_zero, norm_zero, sq, mul_zero, add_zero, Real.sqrt_one, one_mul] at hle
  refine IsMinNormLeastSquaresSolution.eq_pinv ⟨(h.isLeastSquaresSolution_basic b).1,
    fun y hy => hle.trans ?_⟩
  exact (isMinNormLeastSquaresSolution_pinv A b).2 y hy

/-- **Equation (5.5.5)** of [golub2013matrix] (Golub and Pereyra). In the setting of
`GolubVanLoan.Chapter05.basicSolution`, if $x_{LS} = A^+ b \neq 0$, then
$$1 \le \frac{\|x_B\|_2}{\|x_{LS}\|_2} \le \sqrt{1 + \|R_{11}^{-1} R_{12}\|_2^2}.$$

The matrix norm $\|\cdot\|_2$ is the spectral norm. -/
theorem equation_5_5_5 (h : IsPivotedQR.IsRankRevealing A Q R π r)
    (b : EuclideanSpace ℝ (Fin m)) (hx : toEuclideanLin A.pinv b ≠ 0) :
    1 ≤ ‖pivotedBasicSolution Q R π h.le_rows h.le_cols b‖ / ‖toEuclideanLin A.pinv b‖ ∧
      ‖pivotedBasicSolution Q R π h.le_rows h.le_cols b‖ / ‖toEuclideanLin A.pinv b‖ ≤
        √(1 + ‖(R.submatrix (Fin.castLE h.le_rows) (Fin.castLE h.le_cols))⁻¹ *
          R.submatrix (Fin.castLE h.le_rows) (tailIdx h.le_cols)‖ ^ 2) := by
  have hpos : 0 < ‖toEuclideanLin A.pinv b‖ := norm_pos_iff.2 hx
  obtain ⟨h1, h2⟩ := h.norm_basic_le b
  exact ⟨(one_le_div hpos).2 h1, (div_le_iff₀ hpos).2 h2⟩

end Basic

/-! ### §5.5.7 SVD-based subset selection -/

section SubsetSelection

open scoped Matrix.Norms.L2Operator

/-- **Theorem 5.5.2** of [golub2013matrix]. Let $U^T A V = \Sigma$ be an SVD of
$A \in \mathbb{R}^{m \times n}$, let $P \in \mathbb{R}^{n \times n}$ be a permutation, and let
$1 \le \tilde r \le \operatorname{rank}(A)$. Let $B_1$ be the first $\tilde r$ columns of $AP$,
and let $\tilde V_{11}$ be the leading $\tilde r \times \tilde r$ block of $P^T V$ as in
(5.5.6). If $\tilde V_{11}$ is nonsingular, then
$$\frac{\sigma_{\tilde r}(A)}{\|\tilde V_{11}^{-1}\|_2} \le \sigma_{\tilde r}(B_1) \le
  \sigma_{\tilde r}(A).$$

The permutation is `π : Equiv.Perm (Fin n)`: $AP$ is `A.submatrix id π` and $P^T V$ is
`V.submatrix π id`. The singular values are 0-based: `sortedSingularValues (k - 1)` is
$\sigma_k$, and $\|\cdot\|_2$ is the spectral norm. The proof of the upper bound applies
Corollary 2.4.5 repeatedly; the source cites Corollary 2.4.4 at this step. -/
theorem theorem_5_5_2 {A : Matrix (Fin m) (Fin n) ℝ} {U : Matrix (Fin m) (Fin m) ℝ} {σ : ℕ → ℝ}
    {V : Matrix (Fin n) (Fin n) ℝ} (h : IsSVD A U σ V) (π : Equiv.Perm (Fin n)) {r : ℕ}
    (hr0 : 0 < r) (hrA : r ≤ A.rank)
    (hV : IsUnit ((V.submatrix π id).submatrix (Fin.castLE (hrA.trans A.rank_le_width))
      (Fin.castLE (hrA.trans A.rank_le_width)))) :
    A.sortedSingularValues (r - 1) /
        ‖((V.submatrix π id).submatrix (Fin.castLE (hrA.trans A.rank_le_width))
          (Fin.castLE (hrA.trans A.rank_le_width)))⁻¹‖ ≤
      ((A.submatrix id π).submatrix id
        (Fin.castLE (hrA.trans A.rank_le_width))).sortedSingularValues (r - 1) ∧
    ((A.submatrix id π).submatrix id
        (Fin.castLE (hrA.trans A.rank_le_width))).sortedSingularValues (r - 1) ≤
      A.sortedSingularValues (r - 1) := by
  have hrN : r ≤ n := hrA.trans A.rank_le_width
  have hrM : r ≤ m := hrA.trans A.rank_le_height
  have hlow := h.sortedSingularValues_le_mul_submatrix π hr0 hrM hrN hV
  have hne : Nonempty (Fin r) := ⟨⟨0, hr0⟩⟩
  have hinv : 0 < ‖((V.submatrix π id).submatrix (Fin.castLE hrN) (Fin.castLE hrN))⁻¹‖ :=
    norm_pos_iff.2 ((isUnit_nonsing_inv_iff.2 hV).ne_zero)
  refine ⟨(div_le_iff₀ hinv).2 (by rwa [mul_comm]), ?_⟩
  have := sortedSingularValues_submatrix_le A Function.injective_id
    ((Fin.castLEEmb hrN).trans π.toEmbedding).injective (r - 1)
  exact this

/-- If $V \in \mathbb{R}^{n \times n}$ is orthogonal and $r \le n$, then $V(:, 1{:}r)^T$ has rank
$r$. -/
private theorem rank_transpose_leadingCols {V : Matrix (Fin n) (Fin n) ℝ}
    (hV : V ∈ orthogonalGroup (Fin n) ℝ) {r : ℕ} (hr : r ≤ n) :
    ((V.submatrix id (Fin.castLE hr))ᵀ).rank = r := by
  set W := (V.submatrix id (Fin.castLE hr))ᵀ with hW
  have hVV : Vᵀ * V = 1 := (mem_orthogonalGroup_iff' _ _).1 hV
  have hWW : W * Wᵀ = 1 := by
    ext i j
    have := congrFun (congrFun hVV (Fin.castLE hr i)) (Fin.castLE hr j)
    simpa [hW, Matrix.mul_apply, Matrix.one_apply, Fin.castLE_inj] using this
  refine le_antisymm (rank_le_height W) ?_
  have := rank_mul_le_left W Wᵀ
  rwa [hWW, rank_one, Fintype.card_fin] at this

/-- **§5.5.7** of [golub2013matrix], QR with column pivoting of $V(:, 1{:}\tilde r)^T$. Let
$V \in \mathbb{R}^{n \times n}$ be orthogonal, let $\tilde r \le n$, and let $W = V(:,
1{:}\tilde r)^T = [V_{11}^T\ V_{21}^T] \in \mathbb{R}^{\tilde r \times n}$. Let $WP = QR$ be a
QR factorization with column pivoting, $Q^T W P = [R_{11}\ R_{12}]$, in which the rows of $R$
from row $r + 1$ on are zero and the leading $r \times r$ block is nonsingular, as (5.4.6)
provides. Then $r = \tilde r$,
$$\begin{bmatrix} \tilde V_{11} \\ \tilde V_{21} \end{bmatrix} = P^T \begin{bmatrix} V_{11} \\
  V_{21} \end{bmatrix} = \begin{bmatrix} R_{11}^T Q^T \\ R_{12}^T Q^T \end{bmatrix},$$
the block $R_{11} \in \mathbb{R}^{\tilde r \times \tilde r}$ is nonsingular, and
$\|\tilde V_{11}^{-1}\|_2 = \|R_{11}^{-1}\|_2$.

The factorization is `Matrix.IsPivotedQR.IsRankRevealing` for $W$ with block size $r$. The
equation $r = \tilde r$ holds because the rows of $W$ are orthonormal. -/
theorem qrcp_V11 {V : Matrix (Fin n) (Fin n) ℝ} (hV : V ∈ orthogonalGroup (Fin n) ℝ) {r' r : ℕ}
    (hr : r ≤ n) {Q : Matrix (Fin r) (Fin r) ℝ} {R : Matrix (Fin r) (Fin n) ℝ}
    {π : Equiv.Perm (Fin n)}
    (h : IsPivotedQR.IsRankRevealing (V.submatrix id (Fin.castLE hr))ᵀ Q R π r') :
    r' = r ∧ (V.submatrix π id).submatrix id (Fin.castLE hr) = Rᵀ * Qᵀ ∧
      IsUnit (R.submatrix id (Fin.castLE hr)) ∧
      ‖((V.submatrix π id).submatrix (Fin.castLE hr) (Fin.castLE hr))⁻¹‖ =
        ‖(R.submatrix id (Fin.castLE hr))⁻¹‖ := by
  set W := (V.submatrix id (Fin.castLE hr))ᵀ with hW
  -- the rows of `W` are orthonormal, so `rank W = r`
  have hrank : W.rank = r := rank_transpose_leadingCols hV hr
  have hr' : r' = r := h.rank_eq.symm.trans hrank
  subst hr'
  have hQO : Q ∈ orthogonalGroup (Fin r') ℝ := h.isQR.mem_unitaryGroup
  have hT : (V.submatrix π id).submatrix id (Fin.castLE hr) = Rᵀ * Qᵀ := by
    rw [← transpose_mul, h.isQR.mul_eq]
    ext i j
    rfl
  have hB : R.submatrix id (Fin.castLE hr) =
      R.submatrix (Fin.castLE h.le_rows) (Fin.castLE h.le_cols) := by
    ext i j
    rfl
  have hu : IsUnit (R.submatrix id (Fin.castLE hr)) := hB ▸ h.isUnit_block
  refine ⟨rfl, hT, hu, ?_⟩
  set B := R.submatrix id (Fin.castLE hr) with hBdef
  have hV11 : (V.submatrix π id).submatrix (Fin.castLE hr) (Fin.castLE hr) = Bᵀ * Qᵀ := by
    ext i j
    have h2 := congrFun (congrFun hT (Fin.castLE hr i)) j
    simp only [submatrix_apply, id] at h2 ⊢
    rw [h2]
    simp [Matrix.mul_apply, hBdef]
  have hQinv : (Qᵀ)⁻¹ = Q := inv_eq_left_inv ((mem_orthogonalGroup_iff _ _).1 hQO)
  rw [hV11, Matrix.mul_inv_rev, hQinv, ← transpose_nonsing_inv, l2_opNorm_unitary_mul hQO,
    ← conjTranspose_eq_transpose_of_trivial, l2_opNorm_conjTranspose]

/-! ### §5.5.8 Column independence versus residual size -/

/-- **Theorem 5.5.3** of [golub2013matrix]. Let $U^T A V = \Sigma$ be an SVD of
$A \in \mathbb{R}^{m \times n}$, let $P \in \mathbb{R}^{n \times n}$ be a permutation, let
$1 \le \tilde r \le \operatorname{rank}(A)$, and let $b \in \mathbb{R}^m$. Let $U_1$ be the
first $\tilde r$ columns of $U$, let $B_1$ be the first $\tilde r$ columns of $AP$, and let
$\tilde V_{11}$ be the leading $\tilde r \times \tilde r$ block of $P^T V$. Assume that
$\tilde V_{11}$ is nonsingular. Let $r_{x_{\tilde r}} = b - A x_{\tilde r} = (I - U_1 U_1^T) b$
be the residual of the solution $x_{\tilde r}$ of the nearest rank-$\tilde r$ problem, and let
$r_y = b - B_1 z = (I - B_1 B_1^+) b$ be the residual of the least-squares solution
$z = B_1^+ b$ on the columns of $B_1$. Then
$$\|r_{x_{\tilde r}} - r_y\|_2 \le \frac{\sigma_{\tilde r + 1}(A)}{\sigma_{\tilde r}(A)}
  \|\tilde V_{11}^{-1}\|_2 \|b\|_2,$$
and, as in the remark after the proof, $r_{x_{\tilde r}} - r_y = B_1 z - \sum_{i=1}^{\tilde r}
(u_i^T b) u_i$.

**Typo.** The source calls $\tilde V_{11}$ the leading "$r$-by-$r$" principal submatrix of
$P^T V$. It is $\tilde r$-by-$\tilde r$.

**Reading.** The source leaves the hypothesis $\tilde r \le \operatorname{rank}(A)$ implicit.
The hypothesis is needed: for $A = 0$ the left side need not vanish.

The quotient $\sigma_{\tilde r + 1}(A) / \sigma_{\tilde r}(A)$ is `A.sortedSingularValues r /
A.sortedSingularValues (r - 1)`, and $\|\cdot\|_2$ is the spectral norm. The proof specializes
`Matrix.norm_residual_subset_sub_le`. -/
theorem theorem_5_5_3 {A : Matrix (Fin m) (Fin n) ℝ} {U : Matrix (Fin m) (Fin m) ℝ} {σ : ℕ → ℝ}
    {V : Matrix (Fin n) (Fin n) ℝ} (h : IsSVD A U σ V) (π : Equiv.Perm (Fin n)) {r : ℕ}
    (hr0 : 0 < r) (hrA : r ≤ A.rank)
    (hV : IsUnit ((V.submatrix π id).submatrix (Fin.castLE (hrA.trans A.rank_le_width))
      (Fin.castLE (hrA.trans A.rank_le_width))))
    (b : EuclideanSpace ℝ (Fin m)) :
    ‖(b - toEuclideanLin (U.submatrix id (Fin.castLE (hrA.trans A.rank_le_height)) *
          (U.submatrix id (Fin.castLE (hrA.trans A.rank_le_height)))ᵀ) b) -
        (b - toEuclideanLin ((A.submatrix id π).submatrix id
            (Fin.castLE (hrA.trans A.rank_le_width)) *
          ((A.submatrix id π).submatrix id (Fin.castLE (hrA.trans A.rank_le_width))).pinv) b)‖ ≤
      A.sortedSingularValues r / A.sortedSingularValues (r - 1) *
        ‖((V.submatrix π id).submatrix (Fin.castLE (hrA.trans A.rank_le_width))
          (Fin.castLE (hrA.trans A.rank_le_width)))⁻¹‖ * ‖b‖ ∧
    (b - toEuclideanLin (U.submatrix id (Fin.castLE (hrA.trans A.rank_le_height)) *
          (U.submatrix id (Fin.castLE (hrA.trans A.rank_le_height)))ᵀ) b) -
        (b - toEuclideanLin ((A.submatrix id π).submatrix id
            (Fin.castLE (hrA.trans A.rank_le_width)) *
          ((A.submatrix id π).submatrix id (Fin.castLE (hrA.trans A.rank_le_width))).pinv) b) =
      toEuclideanLin ((A.submatrix id π).submatrix id (Fin.castLE (hrA.trans A.rank_le_width)))
          (toEuclideanLin ((A.submatrix id π).submatrix id
            (Fin.castLE (hrA.trans A.rank_le_width))).pinv b) -
        toLp 2 (∑ i : Fin r, (U.col (Fin.castLE (hrA.trans A.rank_le_height) i) ⬝ᵥ ofLp b) •
          U.col (Fin.castLE (hrA.trans A.rank_le_height) i)) := by
  have hle := norm_residual_subset_sub_le h π hr0 (hrA.trans A.rank_le_height)
    (hrA.trans A.rank_le_width) hrA hV b
  simp only [conjTranspose_eq_transpose_of_trivial] at hle
  refine ⟨hle, ?_⟩
  rw [sub_sub_sub_cancel_left, toEuclideanLin_mul_apply]
  congr 1
  ext p
  simp only [toEuclideanLin_apply, PiLp.toLp_apply, mulVec, dotProduct, Matrix.mul_apply,
    submatrix_apply, id_eq, transpose_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    col_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end SubsetSelection

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- **Algorithm 5.5.1** of [golub2013matrix] (SVD-based subset selection). "Given
$A \in \mathbb{R}^{m \times n}$ and $b \in \mathbb{R}^m$ the following algorithm computes a
permutation $P$, a rank estimate $\tilde r$, and a vector $z \in \mathbb{R}^{\tilde r}$ such
that the first $\tilde r$ columns of $B = AP$ are independent and
$\|B(:, 1{:}\tilde r) z - b\|_2$ is minimized":
```
Compute the SVD UᵀAV = diag(σ₁, …, σ_n) and save V.
Determine r̃ ≤ rank(A).
Apply QR with column pivoting: QᵀV(:, 1:r̃)ᵀP = [R₁₁ | R₁₂] and set AP = [B₁ | B₂].
Determine z ∈ ℝ^r̃ such that ‖b - B₁z‖₂ = min.
```
The program takes $V$ and $\tilde r$, with $\tilde r \le n$ and $\tilde r \le m$, as arguments,
and it returns the pair $(P, z)$.

The SVD is an algorithm of Chapter 8 and the choice of $\tilde r$ is a decision, so both are
inputs (convention 5 of `NumlibSurface.GolubVanLoan`). QR with column pivoting is Algorithm
5.4.1 (`GolubVanLoan.Chapter05.algorithm_5_4_1`) on $V(:, 1{:}\tilde r)^T$ padded with zero rows
(`Matrix.padRows`), and $P$ is `GolubVanLoan.Chapter05.pivotPerm` of its pivots. The
least-squares step is the Householder least-squares solution of §5.3.3 with the returned $\beta$
(`GolubVanLoan.Chapter05.householderLS`). Algorithm 5.3.2 as printed recomputes $\beta$ and
fails, for example for $B_1 = I_2$ (`GolubVanLoan.Chapter05.algorithm_5_3_2_counterexample`). -/
noncomputable def algorithm_5_5_1 {r : ℕ} (hrn : r ≤ n) (hrm : r ≤ m)
    (A : Matrix (Fin m) (Fin n) ℝ) (V : Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ) :
    M (Equiv.Perm (Fin n) × (Fin r → ℝ)) := do
  let st ← algorithm_5_4_1 rnd le_rfl (Matrix.padRows (V.submatrix id (Fin.castLE hrn))ᵀ hrn)
  let z ← householderLS rnd hrm ((A.submatrix id (pivotPerm st.piv)).submatrix id
    (Fin.castLE hrn)) b
  pure (pivotPerm st.piv, z)

end Programs

section Spec

open scoped Matrix.Norms.L2Operator

/-- **Algorithm 5.5.1** of [golub2013matrix], correctness in exact arithmetic. Let
$U^T A V = \Sigma$ be an SVD of $A \in \mathbb{R}^{m \times n}$, let $b \in \mathbb{R}^m$, and
let $1 \le \tilde r \le \operatorname{rank}(A)$, with $\tilde r \le n$ and $\tilde r \le m$. Let
$(P, z)$ be the output of Algorithm 5.5.1 in exact arithmetic, let $B_1$ be the first $\tilde r$
columns of $AP$, and let $\tilde V_{11}$ be the leading $\tilde r \times \tilde r$ block of
$P^T V$. Then $\tilde V_{11}$ is nonsingular,
$$\frac{\sigma_{\tilde r}(A)}{\|\tilde V_{11}^{-1}\|_2} \le \sigma_{\tilde r}(B_1),$$
the columns of $B_1$ are linearly independent ("the first $\tilde r$ columns of $B = AP$ are
independent"), and $z$ minimizes $\|B_1 z - b\|_2$.

QR with column pivoting of $V(:, 1{:}\tilde r)^T$ has rank $\tilde r$, because the rows of this
matrix are orthonormal, so its pivots give a nonsingular $\tilde V_{11}$
(`GolubVanLoan.Chapter05.qrcp_V11`). Theorem 5.5.2 then gives the bound, whose left side is
positive. The least-squares property is `GolubVanLoan.Chapter05.householderLS_spec`. The zero
rows of the padding change neither the rank nor the rows of $R$ that the argument uses. -/
theorem algorithm_5_5_1_spec {A : Matrix (Fin m) (Fin n) ℝ} {U : Matrix (Fin m) (Fin m) ℝ}
    {σ : ℕ → ℝ} {V : Matrix (Fin n) (Fin n) ℝ} (h : IsSVD A U σ V) {r : ℕ} (hrn : r ≤ n)
    (hrm : r ≤ m) (hr0 : 0 < r) (hrA : r ≤ A.rank) (b : Fin m → ℝ)
    {P : Equiv.Perm (Fin n)} {z : Fin r → ℝ}
    (hout : Id.run (algorithm_5_5_1 pure hrn hrm A V b) = (P, z)) :
    IsUnit ((V.submatrix P id).submatrix (Fin.castLE hrn) (Fin.castLE hrn)) ∧
      A.sortedSingularValues (r - 1) /
          ‖((V.submatrix P id).submatrix (Fin.castLE hrn) (Fin.castLE hrn))⁻¹‖ ≤
        ((A.submatrix id P).submatrix id (Fin.castLE hrn)).sortedSingularValues (r - 1) ∧
      LinearIndependent ℝ ((A.submatrix id P).submatrix id (Fin.castLE hrn))ᵀ ∧
      IsLeastSquaresSolution ((A.submatrix id P).submatrix id (Fin.castLE hrn)) (toLp 2 b)
        (toLp 2 z) := by
  have : Nonempty (Fin r) := ⟨⟨0, hr0⟩⟩
  set W : Matrix (Fin r) (Fin n) ℝ := (V.submatrix id (Fin.castLE hrn))ᵀ with hW
  obtain ⟨hRR, hrank, -⟩ := algorithm_5_4_1_spec le_rfl (Matrix.padRows W hrn)
  have hP : P = pivotPerm (Id.run (algorithm_5_4_1 pure le_rfl (Matrix.padRows W hrn))).piv :=
    (congrArg Prod.fst hout).symm
  have hz : z = Id.run (householderLS pure hrm ((A.submatrix id
      (pivotPerm (Id.run (algorithm_5_4_1 pure le_rfl (Matrix.padRows W hrn))).piv)).submatrix id
        (Fin.castLE hrn)) b) :=
    (congrArg Prod.snd hout).symm
  subst hP hz
  set st := Id.run (algorithm_5_4_1 pure le_rfl (Matrix.padRows W hrn)) with hst
  -- the rows of `W` are orthonormal, so `rank W = r̃`, and the run has `r = r̃`
  have hrankW : W.rank = r := rank_transpose_leadingCols h.mem_unitaryGroup_right hrn
  have hr : st.r = r := by
    rw [hrank, Matrix.padRows_eq_mul W hrn, rank_submatrix_one_mul (Fin.castLE_injective hrn),
      hrankW]
  have hRR' := hRR
  rw [hr] at hRR'
  -- `[Ṽ₁₁ᵀ; 0] = Q [R₁₁; 0]`, of rank `r̃`
  set Vt := (V.submatrix (pivotPerm st.piv) id).submatrix (Fin.castLE hrn) (Fin.castLE hrn)
    with hVt
  have hkey : (1 : Matrix (Fin n) (Fin n) ℝ).submatrix id (Fin.castLE hrn) * Vtᵀ =
      factoredQ st.β st.A * (upperPart st.A).submatrix id (Fin.castLE hrn) := by
    have h1 : ((Matrix.padRows W hrn).submatrix id (pivotPerm st.piv)).submatrix id
        (Fin.castLE hrn) =
        (1 : Matrix (Fin n) (Fin n) ℝ).submatrix id (Fin.castLE hrn) * Vtᵀ := by
      rw [Matrix.padRows_eq_mul W hrn]
      rfl
    rw [← h1, ← hRR'.isQR.mul_eq]
    rfl
  have hrankT : ((upperPart st.A).submatrix id (Fin.castLE hrn)).rank = r :=
    HasRevealingBlock.rank_eq ⟨hRR'.le_rows, le_rfl,
      fun i j hi => hRR'.apply_eq_zero i _ hi, hRR'.isUnit_block⟩
  have hQdet : IsUnit (factoredQ st.β st.A).det :=
    (isUnit_iff_isUnit_det _).1 (isUnit_of_mem_unitaryGroup hRR'.isQR.mem_unitaryGroup)
  have hVtu : IsUnit Vt := by
    have hrk : Vtᵀ.rank = r := by
      rw [← rank_submatrix_one_mul (Fin.castLE_injective hrn), hkey,
        rank_mul_eq_right_of_isUnit_det _ _ hQdet, hrankT]
    exact (isUnit_transpose _).1 (isUnit_of_rank_eq_card (by rw [hrk, Fintype.card_fin]))
  -- Theorem 5.5.2
  have hbound := (theorem_5_5_2 h (pivotPerm st.piv) hr0 hrA hVtu).1
  have hsA0 : 0 < A.sortedSingularValues (r - 1) :=
    lt_of_le_of_ne (A.sortedSingularValues_nonneg _)
      (Ne.symm ((A.sortedSingularValues_eq_zero_iff_rank_le _).not.2 (by omega)))
  have hinv : 0 < ‖Vt⁻¹‖ := norm_pos_iff.2 (isUnit_nonsing_inv_iff.2 hVtu).ne_zero
  have hB0 := lt_of_lt_of_le (div_pos hsA0 hinv) hbound
  have hlin : LinearIndependent ℝ
      ((A.submatrix id (pivotPerm st.piv)).submatrix id (Fin.castLE hrn))ᵀ := by
    refine linearIndependent_transpose_of_iInf_colSingularValues_pos ?_
    rw [← sortedSingularValues_eq_iInf_colSingularValues, Fintype.card_fin]
    exact hB0
  exact ⟨hVtu, hbound, hlin, householderLS_spec hrm hlin b⟩

end Spec


end GolubVanLoan.Chapter05
