/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.LinearAlgebra.Matrix.LeastSquares.Regularized
import Numlib.LinearAlgebra.Matrix.LeastSquares.Weighted

/-!
# Golub and Van Loan, Section 6.1: Weighting and regularization

This module formalizes §6.1 of [golub2013matrix]: least-squares problems with weights on the rows or
the columns, and problems with a regularization term. Row weighting with
$D = \operatorname{diag}(d_1, \dots, d_m)$ replaces $\min \|Ax - b\|_2$ by $\min \|D(Ax - b)\|_2$.
For this problem the module proves the normal equations (6.1.2), the difference (6.1.3) from the
unweighted solution, the derivative (6.1.4) of a residual with respect to its weight, and the
augmented system (6.1.5). The generalized least-squares problem $\min_{b = Ax + Bv} v^T v$ is solved
by Paige's method (6.1.7)–(6.1.10), and column weighting gives the least-squares minimizer of least
$G$-norm (§6.1.3). Ridge regression minimizes $\|Ax - b\|_2^2 + \lambda \|x\|_2^2$; the module
proves its normal equations, its SVD form (6.1.14), its limit as $\lambda \to 0$, and the formulas
(6.1.15)–(6.1.19) for cross-validation. Tikhonov regularization replaces $\|x\|_2$ by $\|Bx\|_2$
((6.1.20)–(6.1.21)). Last, the generalized singular value decomposition (Theorem 6.1.1) diagonalizes
the Tikhonov problem (6.1.26).

The proofs specialize the backbone modules `Numlib.LinearAlgebra.Matrix.LeastSquares.Weighted`,
`Numlib.LinearAlgebra.Matrix.LeastSquares.Regularized` and `Numlib.LinearAlgebra.Matrix.GSVD`.

## Main definitions

* §6.1.1, `GolubVanLoan.Chapter06.IsWeightedLeastSquaresSolution`: $x$ minimizes $\|D(Ax - b)\|_2$.
* Equation (6.1.15), `GolubVanLoan.Chapter06.ridgeDeleted`: the ridge solution $x_k(\lambda)$ of the
  problem without the $k$-th equation.
* §6.1.4, `GolubVanLoan.Chapter06.crossValidationError`: the cross-validation weighted square error
  $C(\lambda)$.

## Main results

* Equation (6.1.1), `GolubVanLoan.Chapter06.equation_6_1_1`: $\|D(Ax - b)\|_2^2 = \sum_i d_i^2
  (a_i^T x - b_i)^2$.
* Equation (6.1.2), `GolubVanLoan.Chapter06.equation_6_1_2`: for full column rank, the weighted
  solution solves $(A^T D^2 A) x = A^T D^2 b$.
* Equation (6.1.3), `GolubVanLoan.Chapter06.equation_6_1_3`: $x_D - x_{LS} = (A^T D^2 A)^{-1} A^T
  (D^2 - I)(b - A x_{LS})$.
* Equation (6.1.4), `GolubVanLoan.Chapter06.equation_6_1_4`: the derivative of the residual
  $r_k(\delta)$ with respect to the perturbation $\delta$ of the $k$-th weight.
* §6.1.1, `GolubVanLoan.Chapter06.abs_weightedResidual_antitoneOn`: $|r_k(\delta)|$ is nonincreasing
  in $\delta$.
* Equation (6.1.5), `GolubVanLoan.Chapter06.equation_6_1_5`: a solution of the augmented system
  gives a weighted least-squares solution.
* Equations (6.1.7)–(6.1.8), `GolubVanLoan.Chapter06.equation_6_1_8`: for nonsingular $B$, the
  weighted problem is the generalized least-squares problem.
* Equations (6.1.9)–(6.1.10), `GolubVanLoan.Chapter06.equation_6_1_9`: Paige's method solves the
  generalized least-squares problem.
* Equation (6.1.10), `GolubVanLoan.Chapter06.equation_6_1_10`: the simplification of the top half of
  Paige's equations.
* §6.1.3, `GolubVanLoan.Chapter06.isLeastSquaresSolution_columnWeighting`: $x_G = G^{-1} y$
  minimizes $\|Ax - b\|_2$.
* §6.1.3, `GolubVanLoan.Chapter06.norm_columnWeighting_le`: $x_G$ has the smallest $G$-norm of all
  minimizers.
* Equation (6.1.11), `GolubVanLoan.Chapter06.equation_6_1_11`: ridge regression is the least-squares
  problem of a stacked matrix.
* Equation (6.1.12), `GolubVanLoan.Chapter06.equation_6_1_12`: the normal equations
  $(A^T A + \lambda I) x = A^T b$ of ridge regression.
* Equation (6.1.14), `GolubVanLoan.Chapter06.equation_6_1_14`: $x(\lambda) = \sum_i (\sigma_i u_i^T
  b / (\sigma_i^2 + \lambda)) v_i$.
* §6.1.4, `GolubVanLoan.Chapter06.tendsto_ridge_leastSquares`: $x(\lambda) \to x_{LS}$ as
  $\lambda \to 0^+$.
* §6.1.4, `GolubVanLoan.Chapter06.norm_ridge_antitoneOn`: $\|x(\lambda)\|_2$ is nonincreasing in
  $\lambda$.
* Equation (6.1.15), `GolubVanLoan.Chapter06.ridgeDeleted_spec`: $x_k(\lambda)$ is the unique ridge
  solution without the $k$-th equation.
* Equation (6.1.16), `GolubVanLoan.Chapter06.equation_6_1_16`: $x_k(\lambda)$ as a rank-one update
  of $x(\lambda)$.
* Equation (6.1.17), `GolubVanLoan.Chapter06.equation_6_1_17`: the leave-one-out residual
  $b_k - a_k^T x_k(\lambda)$.
* Equation (6.1.18), `GolubVanLoan.Chapter06.equation_6_1_18`: $C(\lambda)$ in terms of the residual
  $r$ and $\partial r_k / \partial b_k$.
* Equation (6.1.19), `GolubVanLoan.Chapter06.equation_6_1_19`: $C(\lambda)$ in terms of an SVD of
  $A$.
* Equation (6.1.20), `GolubVanLoan.Chapter06.equation_6_1_20`: Tikhonov regularization is the
  least-squares problem of a stacked matrix.
* Equation (6.1.21), `GolubVanLoan.Chapter06.equation_6_1_21`: the normal equations of Tikhonov
  regularization are nonsingular if and only if $\operatorname{null}(A) \cap
  \operatorname{null}(B) = \{0\}$.
* Theorem 6.1.1, `GolubVanLoan.Chapter06.theorem_6_1_1`: existence of the generalized singular value
  decomposition.
* Theorem 6.1.1, `GolubVanLoan.Chapter06.theorem_6_1_1_b`: the decomposition can be chosen with
  $\alpha_i^2 + \beta_i^2 = 1$.
* §6.1.6, `GolubVanLoan.Chapter06.gsvd_one`: the GSVD of $(A, I)$ gives $U_1^T A U_2 =
  \operatorname{diag}(\alpha_i / \beta_i)$.
* §6.1.6, `GolubVanLoan.Chapter06.gsvd_generalizedEigen`: the columns of $X$ are eigenvectors of the
  pencil $A^T A - \mu^2 B^T B$.
* Equation (6.1.26), `GolubVanLoan.Chapter06.equation_6_1_26`: the solution of the Tikhonov problem
  in GSVD coordinates.

## Conventions

* Matrices are real and indices are 0-based. Vectors of a least-squares statement are in
  `EuclideanSpace ℝ (Fin n)`, where a matrix acts through `Matrix.toEuclideanLin`. The entrywise
  formulas of the cross-validation of Golub, Heath and Wahba (§6.1.4) use plain vectors `Fin m → ℝ`
  and `Matrix.mulVec`, as the leave-one-out lemmas of the backbone do.
* The weight matrix $D = \operatorname{diag}(d_1, \dots, d_m)$ is `diagonal d`, and the row
  $a_k^T = A(k, :)$ is `A k`.
* The parameter $\lambda$ of the source is written `μ` in Lean, because `λ` is a keyword.
* The ridge solution $x(\lambda) = (A^T A + \lambda I)^{-1} A^T b$ is the Tikhonov regularization
  `Matrix.tikhonov` of $A$ at $\lambda$, applied to $b$.
* An SVD is `Matrix.IsSVD A U σ V`. The source's $u_i$ and $v_i$ are the columns of $U$ and $V$,
  which appear as the rows `Uᵀ i` and `Vᵀ i` of the transposes.
* A GSVD is `Matrix.IsGSVD A B U₁ U₂ X α β`, in the block order of Theorem 6.1.1: $D_A$ is
  `Matrix.rectDiagonal α` and $D_B$ is `Matrix.shiftedRectDiagonal p β`, with
  $p = \max\{r - m_2, 0\}$.

## Deviations from the source

* **Remark after (6.1.4)** (correction). The source derives the monotonicity of $|r_k(\delta)|$ from
  $\frac{d}{d\delta} [r_k(\delta)^2] < 0$, which fails when $a_k = 0$ or $r_k(\delta) = 0$. The
  library states the non-strict monotonicity. See
  `GolubVanLoan.Chapter06.abs_weightedResidual_antitoneOn`.
* **Paige's method, (6.1.9)–(6.1.10)** (generalization). The source assumes that $A$ has full column
  rank and $B$ is nonsingular; the statement needs only that $S$ is nonsingular. See
  `GolubVanLoan.Chapter06.equation_6_1_9`.
* **§6.1.3, column weighting** (generalization). $x_G = G^{-1} y$ minimizes $\|Ax - b\|_2$ for every
  least-squares solution $y$, not only for the minimum-norm one. See
  `GolubVanLoan.Chapter06.isLeastSquaresSolution_columnWeighting`.
* **§6.1.3, the least $G$-norm** (generalization). The source states the property for
  $\operatorname{rank}(A) < n$; it holds for every rank. See
  `GolubVanLoan.Chapter06.norm_columnWeighting_le`.
* **Equation (6.1.19)** (typo). The numerator has $\tilde b_k$ where $b_k$ is meant. See
  `GolubVanLoan.Chapter06.equation_6_1_19`.
* **Theorem 6.1.1** (typo). The row labels $p$, $r - p$, $m_2 - r$ of the blocks of $D_B$ are
  $r - p$, $m_2 - r + p$, and $n_{1-r}$ is $n_1 - r$. See `GolubVanLoan.Chapter06.theorem_6_1_1`.
* **§6.1.6, the GSVD of $(A, I)$** (correction). The source sets $X = U_2$ to obtain the SVD of $A$;
  in fact $X = U_2 D_B$ and $U_1^T A U_2 = \operatorname{diag}(\alpha_i / \beta_i)$. See
  `GolubVanLoan.Chapter06.gsvd_one`.

## Not formalized

* **Equation (6.1.6).** It is a statistical model.
* **Equation (6.1.13).** It recalls the SVD.
* **Equations (6.1.24)–(6.1.25).** They are steps of the proof of Theorem 6.1.1.
* **Paige's claim on the stability of his method.**
* **The remark of van der Sluis that $\kappa_2(AG^{-1})$ is approximately minimized.**
* **The choice of $\lambda$ that minimizes $C(\lambda)$.**
* **The flop counts.** Operation counts are out of scope for the library.
-/

open Matrix Finset Filter Topology

namespace GolubVanLoan.Chapter06

variable {m n : ℕ}

/-! ### §6.1.1 Row weighting -/

/-- **§6.1.1** of [golub2013matrix], the weighted least-squares problem (6.1.1). Let
$A \in \mathbb{R}^{m \times n}$, $b \in \mathbb{R}^m$ and $d \in \mathbb{R}^m$, and let
$D = \operatorname{diag}(d_1, \dots, d_m)$. A vector $x \in \mathbb{R}^n$ is a **weighted
least-squares solution** if it minimizes $\|D(Ax - b)\|_2$, that is, if it is a least-squares
solution of $DAx = Db$. As the source notes, "if $x_D$ minimizes this summation, then it
minimizes $\|\tilde A x - \tilde b\|_2$ where $\tilde A = DA$ and $\tilde b = Db$".

The definition is `Matrix.IsLeastSquaresSolution` for `diagonal d * A` and $Db$. It puts no
condition on the weights. -/
def IsWeightedLeastSquaresSolution (d : Fin m → ℝ) (A : Matrix (Fin m) (Fin n) ℝ)
    (b : EuclideanSpace ℝ (Fin m)) (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  IsLeastSquaresSolution (diagonal d * A) (toEuclideanLin (diagonal d) b) x

/-- The weighted objective in coordinates: $\|D(Ax - b)\|_2^2 = \sum_i d_i^2 (a_i^T x - b_i)^2$. -/
private theorem norm_sq_weighted_eq (d : Fin m → ℝ) (A : Matrix (Fin m) (Fin n) ℝ)
    (b : EuclideanSpace ℝ (Fin m)) (x : EuclideanSpace ℝ (Fin n)) :
    ‖toEuclideanLin (diagonal d * A) x - toEuclideanLin (diagonal d) b‖ ^ 2 =
      ∑ i, d i ^ 2 * (A i ⬝ᵥ WithLp.ofLp x - WithLp.ofLp b i) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  refine sum_congr rfl fun i _ => ?_
  simp only [PiLp.sub_apply, toEuclideanLin_apply, ← mulVec_mulVec, mulVec_diagonal,
    Real.norm_eq_abs, sq_abs]
  rw [← mul_sub, mul_pow]
  rfl

/-- **Equation (6.1.1)** of [golub2013matrix]. Let $A \in \mathbb{R}^{m \times n}$,
$b, d \in \mathbb{R}^m$ and $x \in \mathbb{R}^n$, and let
$D = \operatorname{diag}(d_1, \dots, d_m)$. Then
$$\|D(Ax - b)\|_2^2 = \sum_{i=1}^{m} d_i^2 (a_i^T x - b_i)^2,$$
and $x$ is a weighted least-squares solution if and only if it minimizes this sum.

The row $a_i^T$ is `A i`. -/
theorem equation_6_1_1 (d : Fin m → ℝ) (A : Matrix (Fin m) (Fin n) ℝ)
    (b : EuclideanSpace ℝ (Fin m)) (x : EuclideanSpace ℝ (Fin n)) :
    (‖toEuclideanLin (diagonal d * A) x - toEuclideanLin (diagonal d) b‖ ^ 2 =
      ∑ i, d i ^ 2 * (A i ⬝ᵥ WithLp.ofLp x - WithLp.ofLp b i) ^ 2) ∧
    (IsWeightedLeastSquaresSolution d A b x ↔
      ∀ y : EuclideanSpace ℝ (Fin n),
        ∑ i, d i ^ 2 * (A i ⬝ᵥ WithLp.ofLp x - WithLp.ofLp b i) ^ 2 ≤
          ∑ i, d i ^ 2 * (A i ⬝ᵥ WithLp.ofLp y - WithLp.ofLp b i) ^ 2) := by
  refine ⟨norm_sq_weighted_eq d A b x, ?_⟩
  refine forall_congr' fun y => ?_
  rw [← norm_sq_weighted_eq, ← norm_sq_weighted_eq]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).symm

/-- $DD = \operatorname{diag}(d_i^2)$. -/
private theorem diagonal_mul_diagonal_self (d : Fin m → ℝ) :
    diagonal d * diagonal d = diagonal fun i => d i ^ 2 := by
  rw [diagonal_mul_diagonal]
  simp only [sq]

/-- $(DA)^T = A^T D$ for a real diagonal matrix $D$. -/
private theorem conjTranspose_diagonal_mul (d : Fin m → ℝ) (A : Matrix (Fin m) (Fin n) ℝ) :
    (diagonal d * A)ᴴ = Aᵀ * diagonal d := by
  rw [conjTranspose_eq_transpose_of_trivial, transpose_mul, diagonal_transpose]

/-- $D^T D = \operatorname{diag}(d_i^2)$ for a real diagonal matrix $D$. -/
private theorem conjTranspose_diagonal_mul_self (d : Fin m → ℝ) :
    (diagonal d)ᴴ * diagonal d = diagonal fun i => d i ^ 2 := by
  rw [conjTranspose_eq_transpose_of_trivial, diagonal_transpose, diagonal_mul_diagonal_self]

/-- A diagonal matrix with nonzero diagonal is invertible. -/
private theorem isUnit_diagonal_of_ne_zero {d : Fin m → ℝ} (hd : ∀ i, d i ≠ 0) :
    IsUnit (diagonal d) :=
  (isUnit_iff_isUnit_det _).2 (by
    rw [det_diagonal]
    exact (prod_ne_zero_iff.2 fun i _ => hd i).isUnit)

/-- A nonzero weight has a positive square. -/
private theorem sq_weight_pos {d : Fin m → ℝ} (hd : ∀ i, d i ≠ 0) (i : Fin m) : 0 < d i ^ 2 :=
  lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (hd i)))

/-- **Equation (6.1.2)** of [golub2013matrix]. Let $A \in \mathbb{R}^{m \times n}$ have full column
rank, let $d \in \mathbb{R}^m$ have no zero entry, let
$D = \operatorname{diag}(d_1, \dots, d_m)$, and let $b \in \mathbb{R}^m$ and
$x \in \mathbb{R}^n$. The method of normal equations leads to "the following positive definite
system":
$$(A^T D^2 A) x_D = A^T D^2 b.$$
Precisely, $A^T D^2 A$ is positive definite, $x$ is a weighted least-squares solution if and
only if $(A^T D^2 A) x = A^T D^2 b$, and $x$ is a weighted least-squares solution if and only if
$x = (A^T D^2 A)^{-1} A^T D^2 b$.

Full column rank is `LinearIndependent ℝ Aᵀ`. The matrix $(A^T D^2 A)^{-1} A^T D^2$ is
`Matrix.weightedLeastSquaresOp`. -/
theorem equation_6_1_2 {A : Matrix (Fin m) (Fin n) ℝ} (hA : LinearIndependent ℝ Aᵀ)
    {d : Fin m → ℝ} (hd : ∀ i, d i ≠ 0) (b : EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin n)) :
    (Aᵀ * diagonal (fun i => d i ^ 2) * A).PosDef ∧
    (IsWeightedLeastSquaresSolution d A b x ↔
      toEuclideanLin (Aᵀ * diagonal (fun i => d i ^ 2) * A) x =
        toEuclideanLin (Aᵀ * diagonal (fun i => d i ^ 2)) b) ∧
    (IsWeightedLeastSquaresSolution d A b x ↔
      x = toEuclideanLin (weightedLeastSquaresOp (diagonal fun i => d i ^ 2) A) b) := by
  refine ⟨?_, ?_, ?_⟩
  · have := posDef_conjTranspose_mul_diagonal_mul hA (u := fun i => d i ^ 2)
      (sq_weight_pos hd)
    rwa [conjTranspose_eq_transpose_of_trivial] at this
  · rw [IsWeightedLeastSquaresSolution, isLeastSquaresSolution_iff_normalEquations,
      conjTranspose_diagonal_mul, ← toEuclideanLin_mul_apply, Matrix.mul_assoc,
      ← Matrix.mul_assoc (diagonal d), diagonal_mul_diagonal_self, Matrix.mul_assoc,
      ← Matrix.mul_assoc Aᵀ, diagonal_mul_diagonal_self]
  · rw [IsWeightedLeastSquaresSolution,
      isLeastSquaresSolution_weightedLeastSquaresOp (isUnit_diagonal_of_ne_zero hd) hA,
      conjTranspose_diagonal_mul_self]

/-- **Equation (6.1.3)** of [golub2013matrix]. Let $A \in \mathbb{R}^{m \times n}$ have full column
rank, let $d \in \mathbb{R}^m$ have no zero entry, let
$D = \operatorname{diag}(d_1, \dots, d_m)$, and let $b \in \mathbb{R}^m$. If $x_D$ is a weighted
least-squares solution and $x_{LS}$ is a least-squares solution of $\min \|Ax - b\|_2$, then
$$x_D - x_{LS} = (A^T D^2 A)^{-1} A^T (D^2 - I)(b - A x_{LS}).$$
The source obtains this by "subtracting the unweighted system $A^T A x_{LS} = A^T b$". -/
theorem equation_6_1_3 {A : Matrix (Fin m) (Fin n) ℝ} (hA : LinearIndependent ℝ Aᵀ)
    {d : Fin m → ℝ} (hd : ∀ i, d i ≠ 0) {b : EuclideanSpace ℝ (Fin m)}
    {xD xLS : EuclideanSpace ℝ (Fin n)} (hxD : IsWeightedLeastSquaresSolution d A b xD)
    (hxLS : IsLeastSquaresSolution A b xLS) :
    xD - xLS = toEuclideanLin ((Aᵀ * diagonal (fun i => d i ^ 2) * A)⁻¹ * Aᵀ *
      (diagonal (fun i => d i ^ 2) - 1)) (b - toEuclideanLin A xLS) := by
  obtain ⟨hpd, -, h3⟩ := equation_6_1_2 hA hd b xD
  rw [(isLeastSquaresSolution_iff_eq_pinv_of_linearIndependent hA).1 hxLS, h3.1 hxD]
  have hW : IsUnit (Aᴴ * diagonal (fun i => d i ^ 2) * A) := by
    rw [conjTranspose_eq_transpose_of_trivial]
    exact hpd.isUnit
  rw [weightedLeastSquaresOp_mulVec_sub_pinv_mulVec hW b, conjTranspose_eq_transpose_of_trivial]

/-- Replacing the $k$-th entry of the squared weights twice is the same as replacing it once by the
second value. -/
private theorem update_update_weights (d : Fin m → ℝ) (k : Fin m) (s t : ℝ) :
    Function.update (Function.update (fun i => d i ^ 2) k s) k t =
      Function.update (fun i => d i ^ 2) k t :=
  Function.update_idem _ _ _

/-- If no $d_i$ is zero and $t > 0$, the squared weights $d_i^2$ with the $k$-th entry replaced by
$t$ are positive. -/
private theorem update_weights_pos {d : Fin m → ℝ} (hd : ∀ i, d i ≠ 0) (k : Fin m) {t : ℝ}
    (ht : 0 < t) (i : Fin m) : 0 < Function.update (fun i => d i ^ 2) k t i := by
  by_cases hi : i = k
  · rw [hi, Function.update_self]
    exact ht
  · rw [Function.update_of_ne hi]
    exact sq_weight_pos hd i

/-- **Equation (6.1.4)** of [golub2013matrix]. Let $A \in \mathbb{R}^{m \times n}$ have full column
rank, let $d \in \mathbb{R}^m$ have no zero entry, let $b \in \mathbb{R}^m$, let
$1 \le k \le m$, and let $\delta > -1$. Let
$$D(\delta) = \operatorname{diag}(d_1, \dots, d_{k-1}, d_k \sqrt{1 + \delta}, d_{k+1}, \dots,
  d_m),$$
let $x(\delta)$ minimize $\|D(\delta)(Ax - b)\|_2$, and let
$r_k(\delta) = e_k^T (b - A x(\delta))$. Then $r_k$ is differentiable at $\delta$, and
$$\frac{d}{d\delta} r_k(\delta) = -d_k^2 \left(a_k^T (A^T D(\delta)^2 A)^{-1} a_k\right)
  r_k(\delta).$$

The residual $r_k(\delta)$ is `Matrix.weightedResidual A b w k` at the weights $w$ on the
diagonal of $D(\delta)^2$: $w_i = d_i^2$ for $i \neq k$ and $w_k = d_k^2 (1 + \delta)$. Its
weighted solution is $x(\delta) = (A^T D(\delta)^2 A)^{-1} A^T D(\delta)^2 b$. -/
theorem equation_6_1_4 {A : Matrix (Fin m) (Fin n) ℝ} (hA : LinearIndependent ℝ Aᵀ)
    {d : Fin m → ℝ} (hd : ∀ i, d i ≠ 0) (b : Fin m → ℝ) (k : Fin m) {δ : ℝ} (hδ : -1 < δ) :
    HasDerivAt
      (fun δ => weightedResidual A b (Function.update (fun i => d i ^ 2) k (d k ^ 2 * (1 + δ))) k)
      (-d k ^ 2 * (A k ⬝ᵥ ((Aᵀ * diagonal
          (Function.update (fun i => d i ^ 2) k (d k ^ 2 * (1 + δ))) * A)⁻¹ *ᵥ A k)) *
        weightedResidual A b (Function.update (fun i => d i ^ 2) k (d k ^ 2 * (1 + δ))) k) δ := by
  have hdk : 0 < d k ^ 2 := sq_weight_pos hd k
  set w := Function.update (fun i => d i ^ 2) k (d k ^ 2 * (1 + δ)) with hw
  have hwpos : ∀ i, 0 < w i :=
    update_weights_pos hd k (mul_pos hdk (by linarith))
  have hback := hasDerivAt_weightedResidual hA hwpos b k
  have hwk : w k = d k ^ 2 * (1 + δ) := by rw [hw, Function.update_self]
  rw [hwk] at hback
  have hin : HasDerivAt (fun δ : ℝ => d k ^ 2 * (1 + δ)) (d k ^ 2) δ := by
    simpa using ((hasDerivAt_id δ).const_add 1).const_mul (d k ^ 2)
  have := hback.comp δ hin
  convert this using 1
  · funext δ'
    simp only [Function.comp_apply, hw, update_update_weights]
  · ring

/-- **§6.1.1** of [golub2013matrix]. Let $A \in \mathbb{R}^{m \times n}$ have full column rank, let
$d \in \mathbb{R}^m$ have no zero entry, let $b \in \mathbb{R}^m$ and $1 \le k \le m$, and let
$r_k(\delta)$ be the residual of (6.1.4). Then "$|r_k(\delta)|$ is a monotone decreasing
function of $\delta$": the map $\delta \mapsto |r_k(\delta)|$ is nonincreasing on $\delta > -1$.

**Correction.** The source derives the claim from $\frac{d}{d\delta} [r_k(\delta)^2] < 0$. This
inequality fails when $a_k = 0$ or $r_k(\delta) = 0$. The statement here is the non-strict
monotonicity, which holds in all cases. -/
theorem abs_weightedResidual_antitoneOn {A : Matrix (Fin m) (Fin n) ℝ}
    (hA : LinearIndependent ℝ Aᵀ) {d : Fin m → ℝ} (hd : ∀ i, d i ≠ 0) (b : Fin m → ℝ)
    (k : Fin m) :
    AntitoneOn
      (fun δ => |weightedResidual A b
        (Function.update (fun i => d i ^ 2) k (d k ^ 2 * (1 + δ))) k|) (Set.Ioi (-1)) := by
  have hdk : 0 < d k ^ 2 := sq_weight_pos hd k
  have hw : ∀ i, 0 < (fun i => d i ^ 2) i := sq_weight_pos hd
  have hback := antitoneOn_abs_weightedResidual hA hw b k
  intro δ₁ h₁ δ₂ h₂ h12
  simp only [Set.mem_Ioi] at h₁ h₂
  refine hback (Set.mem_Ioi.2 (mul_pos hdk (by linarith)))
    (Set.mem_Ioi.2 (mul_pos hdk (by linarith))) ?_
  exact mul_le_mul_of_nonneg_left (by linarith) hdk.le

/-- **Equation (6.1.5)** of [golub2013matrix]. Let $d \in \mathbb{R}^m$ have no zero entry, let
$D = \operatorname{diag}(d_1, \dots, d_m)$, and let $A \in \mathbb{R}^{m \times n}$,
$b, r \in \mathbb{R}^m$ and $x \in \mathbb{R}^n$. If
$$\begin{bmatrix} D^{-2} & A \\ A^T & 0 \end{bmatrix} \begin{bmatrix} r \\ x \end{bmatrix} =
  \begin{bmatrix} b \\ 0 \end{bmatrix},$$
then $x$ minimizes (6.1.1), that is, $x$ is a weighted least-squares solution.

The two block rows are the hypotheses $D^{-2} r + Ax = b$ and $A^T r = 0$. -/
theorem equation_6_1_5 {d : Fin m → ℝ} (hd : ∀ i, d i ≠ 0) {A : Matrix (Fin m) (Fin n) ℝ}
    {b r : EuclideanSpace ℝ (Fin m)} {x : EuclideanSpace ℝ (Fin n)}
    (h1 : toEuclideanLin (diagonal fun i => d i ^ 2)⁻¹ r + toEuclideanLin A x = b)
    (h2 : toEuclideanLin Aᵀ r = 0) : IsWeightedLeastSquaresSolution d A b x := by
  refine isLeastSquaresSolution_of_augmented (r := r) (isUnit_diagonal_of_ne_zero hd) ?_ ?_
  · rwa [conjTranspose_diagonal_mul_self]
  · rwa [conjTranspose_eq_transpose_of_trivial]

/-! ### §6.1.2 Generalized least squares -/

/-- **Equations (6.1.7)–(6.1.8)** of [golub2013matrix]. Let $A \in \mathbb{R}^{m \times n}$, let
$B \in \mathbb{R}^{m \times m}$ be nonsingular, so that $W = BB^T$, and let $b \in \mathbb{R}^m$
and $x \in \mathbb{R}^n$. Then $x$ minimizes $\|B^{-1}(Ax - b)\|_2$, which is (6.1.7) for
$W = BB^T$, if and only if the pair $(x, B^{-1}(b - Ax))$ solves the generalized least-squares
problem (6.1.8)
$$\min_{b = Ax + Bv} v^T v.$$

The generalized least-squares problem is `Matrix.IsGeneralizedLeastSquaresSolution`. -/
theorem equation_6_1_8 {A : Matrix (Fin m) (Fin n) ℝ} {B : Matrix (Fin m) (Fin m) ℝ}
    (hB : IsUnit B) {b : EuclideanSpace ℝ (Fin m)} {x : EuclideanSpace ℝ (Fin n)} :
    IsLeastSquaresSolution (B⁻¹ * A) (toEuclideanLin B⁻¹ b) x ↔
      IsGeneralizedLeastSquaresSolution A B b x (toEuclideanLin B⁻¹ (b - toEuclideanLin A x)) := by
  rw [isGeneralizedLeastSquaresSolution_iff hB]
  exact ⟨fun h => ⟨h, rfl⟩, fun h => h.1⟩

/-- **Equations (6.1.9)–(6.1.10)** of [golub2013matrix], Paige's method. Let
$A \in \mathbb{R}^{(n+q) \times n}$ have a QR factorization $A = QR$, with $Q = [Q_1\ Q_2]$,
$Q_1 \in \mathbb{R}^{(n+q) \times n}$ and $R_1 = R(1{:}n, 1{:}n)$, so that $Q^T A = [R_1; 0]$.
Let $B \in \mathbb{R}^{(n+q) \times (n+q)}$, let $Z = [Z_1\ Z_2] \in \mathbb{R}^{(n+q) \times
(n+q)}$ be orthogonal with $Z_2 \in \mathbb{R}^{(n+q) \times q}$, and let
$S \in \mathbb{R}^{q \times q}$ be nonsingular with $(Q_2^T B) Z = [0\ S]$. Let
$b \in \mathbb{R}^{n+q}$, and let $u \in \mathbb{R}^q$ and $x \in \mathbb{R}^n$ satisfy
$$S u = Q_2^T b, \qquad R_1 x = Q_1^T b - Q_1^T B Z_2 u.$$
Then $(x, v)$ with $v = Z_2 u$ solves the generalized least-squares problem (6.1.8). In the
words of the source, "the bottom half of this equation determines $v$ while the top half
prescribes $x$".

**Generalization.** The source assumes that $A$ has full column rank and that $B$ is
nonsingular, so that $R_1$ and the upper triangular $S$ are nonsingular. The statement needs
only that $S$ is nonsingular.

The blocks are submatrices of columns: $Q_1$ is `Matrix.firstColumns Q`, $Q_2$ and $Z_2$ are the
last $q$ columns (through `Fin.natAdd n`), $Z_1$ is the first $n$ columns (through
`Fin.castAdd q`), and $R_1$ is `Matrix.firstRows R`. -/
theorem equation_6_1_9 {q : ℕ} {A : Matrix (Fin (n + q)) (Fin n) ℝ}
    {Q : Matrix (Fin (n + q)) (Fin (n + q)) ℝ} {R : Matrix (Fin (n + q)) (Fin n) ℝ}
    (hQR : IsQR A Q R) {B Z : Matrix (Fin (n + q)) (Fin (n + q)) ℝ}
    (hZ : Z ∈ orthogonalGroup (Fin (n + q)) ℝ) {S : Matrix (Fin q) (Fin q) ℝ} (hS : IsUnit S)
    (hZ₁ : (Q.submatrix id (Fin.natAdd n))ᵀ * B * Z.submatrix id (Fin.castAdd q) = 0)
    (hZ₂ : (Q.submatrix id (Fin.natAdd n))ᵀ * B * Z.submatrix id (Fin.natAdd n) = S)
    {b : EuclideanSpace ℝ (Fin (n + q))} {u : EuclideanSpace ℝ (Fin q)}
    {x : EuclideanSpace ℝ (Fin n)}
    (hu : toEuclideanLin S u = toEuclideanLin (Q.submatrix id (Fin.natAdd n))ᵀ b)
    (hx : toEuclideanLin (firstRows R (Nat.le_add_right n q)) x =
      toEuclideanLin (firstColumns Q (Nat.le_add_right n q))ᵀ b -
        toEuclideanLin ((firstColumns Q (Nat.le_add_right n q))ᵀ * B *
          Z.submatrix id (Fin.natAdd n)) u) :
    IsGeneralizedLeastSquaresSolution A B b x
      (toEuclideanLin (Z.submatrix id (Fin.natAdd n)) u) := by
  simp only [← conjTranspose_eq_transpose_of_trivial, ← lastColumns_eq_submatrix_natAdd]
    at hZ₁ hZ₂ hu hx ⊢
  exact isGeneralizedLeastSquaresSolution_of_paige hQR hZ hS hZ₁ hZ₂ hu hx

/-- **Equation (6.1.10)** of [golub2013matrix], the simplification. Let $Z = [Z_1\ Z_2] \in
\mathbb{R}^{(n+q) \times (n+q)}$ be orthogonal, with $Z_1$ the first $n$ columns, let
$C \in \mathbb{R}^{k \times (n+q)}$, $c \in \mathbb{R}^k$ and $u \in \mathbb{R}^q$, and let
$v = Z_2 u$. Then
$$c - (C Z_1 Z_1^T + C Z_2 Z_2^T) v = c - C Z_2 u.$$
In the source $C = Q_1^T B$ and $c = Q_1^T b$, and the equation reads "$R_1 x = Q_1^T b - (Q_1^T
B Z_1 Z_1^T + Q_1^T B Z_2 Z_2^T) v = Q_1^T b - Q_1^T B Z_2 u$". -/
theorem equation_6_1_10 {k q : ℕ} {Z : Matrix (Fin (n + q)) (Fin (n + q)) ℝ}
    (hZ : Z ∈ orthogonalGroup (Fin (n + q)) ℝ) (C : Matrix (Fin k) (Fin (n + q)) ℝ)
    (c : Fin k → ℝ) (u : Fin q → ℝ) :
    c - (C * Z.submatrix id (Fin.castAdd q) * (Z.submatrix id (Fin.castAdd q))ᵀ +
        C * Z.submatrix id (Fin.natAdd n) * (Z.submatrix id (Fin.natAdd n))ᵀ) *ᵥ
          (Z.submatrix id (Fin.natAdd n) *ᵥ u) =
      c - (C * Z.submatrix id (Fin.natAdd n)) *ᵥ u := by
  have hZZ : Z.submatrix id (Fin.castAdd q) * (Z.submatrix id (Fin.castAdd q))ᵀ +
      Z.submatrix id (Fin.natAdd n) * (Z.submatrix id (Fin.natAdd n))ᵀ = 1 := by
    have h1 : Z * Zᵀ = 1 := by
      exact (mem_orthogonalGroup_iff _ ℝ).1 hZ
    rw [← h1]
    ext i j
    simp only [Matrix.add_apply, Matrix.mul_apply, submatrix_apply, transpose_apply, id,
      Fin.sum_univ_add]
  rw [Matrix.mul_assoc, Matrix.mul_assoc C, ← Matrix.mul_add, hZZ, Matrix.mul_one, mulVec_mulVec]

/-! ### §6.1.3 Column weighting -/

/-- **§6.1.3** of [golub2013matrix], column weighting. Let $A \in \mathbb{R}^{m \times n}$, let
$G \in \mathbb{R}^{n \times n}$ be nonsingular, let $b \in \mathbb{R}^m$, and let $y$ be a
least-squares solution of $\min_y \|(AG^{-1}) y - b\|_2$. Then $x_G = G^{-1} y$ minimizes
$\|Ax - b\|_2$.

**Generalization.** The source takes for $y$ the minimum 2-norm solution $y_{LS}$. Every
least-squares solution $y$ gives a minimizer. -/
theorem isLeastSquaresSolution_columnWeighting {A : Matrix (Fin m) (Fin n) ℝ}
    {G : Matrix (Fin n) (Fin n) ℝ} (hG : IsUnit G) {b : EuclideanSpace ℝ (Fin m)}
    {y : EuclideanSpace ℝ (Fin n)} (hy : IsLeastSquaresSolution (A * G⁻¹) b y) :
    IsLeastSquaresSolution A b (toEuclideanLin G⁻¹ y) :=
  (isLeastSquaresSolution_mul_inv_iff hG).1 hy

/-- **§6.1.3** of [golub2013matrix]. Let $A \in \mathbb{R}^{m \times n}$, let
$G \in \mathbb{R}^{n \times n}$ be nonsingular, let $b \in \mathbb{R}^m$, and let
$\|z\|_G = \|Gz\|_2$. Let $y_{LS}$ be the minimum 2-norm solution of
$\min_y \|(AG^{-1}) y - b\|_2$, and let $x_G = G^{-1} y_{LS}$. Then $\|x_G\|_G \le \|x\|_G$ for
every minimizer $x$ of $\|Ax - b\|_2$: "within the set of minimizers, $x_G$ has the smallest
$G$-norm".

**Generalization.** The source states the property for $\operatorname{rank}(A) < n$. It holds
for every rank. -/
theorem norm_columnWeighting_le {A : Matrix (Fin m) (Fin n) ℝ} {G : Matrix (Fin n) (Fin n) ℝ}
    (hG : IsUnit G) {b : EuclideanSpace ℝ (Fin m)} {y x : EuclideanSpace ℝ (Fin n)}
    (hy : IsMinNormLeastSquaresSolution (A * G⁻¹) b y) (hx : IsLeastSquaresSolution A b x) :
    ‖toEuclideanLin G (toEuclideanLin G⁻¹ y)‖ ≤ ‖toEuclideanLin G x‖ := by
  rw [toEuclideanLin_mul_nonsing_inv_apply hG]
  exact hy.norm_le_of_mul_inv hG hx

/-! ### §6.1.4 Ridge regression -/

/-- For $\mu \ge 0$, $\|\sqrt{\mu} M x - 0\|_2^2 = \mu \|Mx\|_2^2$: the regularization term of a
stacked problem. -/
private theorem norm_sqrt_smul_sub_zero_sq {k : ℕ} {μ : ℝ} (hμ : 0 ≤ μ)
    (M : Matrix (Fin k) (Fin n) ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    ‖toEuclideanLin (Real.sqrt μ • M) x - WithLp.toLp 2 0‖ ^ 2 =
      μ * ‖toEuclideanLin M x‖ ^ 2 := by
  rw [WithLp.toLp_zero, sub_zero, toEuclideanLin_smul_apply, norm_smul, mul_pow,
    Real.norm_eq_abs, sq_abs, Real.sq_sqrt hμ]

/-- **Equation (6.1.11)** of [golub2013matrix], ridge regression. Let
$A \in \mathbb{R}^{m \times n}$, $b \in \mathbb{R}^m$, $\lambda \ge 0$ and $x \in \mathbb{R}^n$.
Then
$$\left\| \begin{bmatrix} A \\ \sqrt{\lambda} I \end{bmatrix} x - \begin{bmatrix} b \\ 0
  \end{bmatrix} \right\|_2^2 = \|Ax - b\|_2^2 + \lambda \|x\|_2^2,$$
and $x$ is a least-squares solution of the stacked problem if and only if it minimizes
$\|Ax - b\|_2^2 + \lambda \|x\|_2^2$.

The stacked matrix is `Matrix.fromRows`, and the stacked vector is `Sum.elim b 0`. -/
theorem equation_6_1_11 (A : Matrix (Fin m) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin m)) {μ : ℝ}
    (hμ : 0 ≤ μ) (x : EuclideanSpace ℝ (Fin n)) :
    (‖toEuclideanLin (fromRows A (Real.sqrt μ • (1 : Matrix (Fin n) (Fin n) ℝ))) x -
        WithLp.toLp 2 (Sum.elim (WithLp.ofLp b) 0)‖ ^ 2 =
      ‖toEuclideanLin A x - b‖ ^ 2 + μ * ‖x‖ ^ 2) ∧
    (IsLeastSquaresSolution (fromRows A (Real.sqrt μ • (1 : Matrix (Fin n) (Fin n) ℝ)))
        (WithLp.toLp 2 (Sum.elim (WithLp.ofLp b) 0)) x ↔
      ∀ y, ‖toEuclideanLin A x - b‖ ^ 2 + μ * ‖x‖ ^ 2 ≤
        ‖toEuclideanLin A y - b‖ ^ 2 + μ * ‖y‖ ^ 2) := by
  refine ⟨?_, ?_⟩
  · rw [norm_fromRows_sub_sq, WithLp.toLp_ofLp, norm_sqrt_smul_sub_zero_sq hμ,
      toEuclideanLin_one_apply]
  · have h := isLeastSquaresSolution_fromRows_iff A (1 : Matrix (Fin n) (Fin n) ℝ)
      (WithLp.ofLp b) 0 hμ x
    simp only [smul_zero, WithLp.toLp_ofLp, toEuclideanLin_one_apply, WithLp.toLp_zero,
      sub_zero, RCLike.ofReal_real_eq_id, id_eq] at h
    exact h

/-- **Equation (6.1.12)** of [golub2013matrix]. Let $A \in \mathbb{R}^{m \times n}$, $\lambda > 0$,
$b \in \mathbb{R}^m$ and $x \in \mathbb{R}^n$. Then $x$ minimizes
$\|Ax - b\|_2^2 + \lambda \|x\|_2^2$ if and only if it solves "the normal equation system for
this problem"
$$(A^T A + \lambda I) x = A^T b,$$
and if and only if $x = x(\lambda) = (A^T A + \lambda I)^{-1} A^T b$.

The ridge solution $x(\lambda)$ is `Matrix.tikhonov` of $A$ at $\lambda$, applied to $b$. -/
theorem equation_6_1_12 (A : Matrix (Fin m) (Fin n) ℝ) {μ : ℝ} (hμ : 0 < μ)
    (b : EuclideanSpace ℝ (Fin m)) (x : EuclideanSpace ℝ (Fin n)) :
    ((∀ y, ‖toEuclideanLin A x - b‖ ^ 2 + μ * ‖x‖ ^ 2 ≤
        ‖toEuclideanLin A y - b‖ ^ 2 + μ * ‖y‖ ^ 2) ↔
      toEuclideanLin (Aᵀ * A + μ • (1 : Matrix (Fin n) (Fin n) ℝ)) x = toEuclideanLin Aᵀ b) ∧
    ((∀ y, ‖toEuclideanLin A x - b‖ ^ 2 + μ * ‖x‖ ^ 2 ≤
        ‖toEuclideanLin A y - b‖ ^ 2 + μ * ‖y‖ ^ 2) ↔
      x = toEuclideanLin (A.tikhonov μ) b) := by
  have h2 := ((eq_toEuclideanLin_tikhonov_iff_isMinOn A hμ b x).trans isMinOn_univ_iff).symm
  refine ⟨?_, h2⟩
  rw [h2, ← tikhonov_unique A μ hμ b x]
  have e : toEuclideanLin (Aᵀ * A + μ • (1 : Matrix (Fin n) (Fin n) ℝ)) x =
      μ • x + toEuclideanLin (Aᵀ * A) x := by
    rw [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, toEuclideanLin_one,
      LinearMap.id_apply, add_comm]
  rw [e, conjTranspose_eq_transpose_of_trivial]
  rfl

/-- **Equation (6.1.14)** of [golub2013matrix]. Let $U^T A V = \Sigma$ be an SVD of
$A \in \mathbb{R}^{m \times n}$, let $\lambda > 0$, and let $b \in \mathbb{R}^m$. Then the ridge
solution is
$$x(\lambda) = \sum_{i=1}^{\min(m, n)} \frac{\sigma_i u_i^T b}{\sigma_i^2 + \lambda} v_i.$$
The terms with $\sigma_i = 0$, which are those after the rank $r$, vanish, so this is the sum to
$r$ of the source. -/
theorem equation_6_1_14 {A : Matrix (Fin m) (Fin n) ℝ} {U : Matrix (Fin m) (Fin m) ℝ} {σ : ℕ → ℝ}
    {V : Matrix (Fin n) (Fin n) ℝ} (h : IsSVD A U σ V) {μ : ℝ} (hμ : 0 < μ)
    (b : EuclideanSpace ℝ (Fin m)) :
    toEuclideanLin (A.tikhonov μ) b = ∑ i : Fin (min m n),
      (σ i * inner ℝ (WithLp.toLp 2 (Uᵀ (Fin.castLE (min_le_left m n) i))) b / (σ i ^ 2 + μ)) •
        (WithLp.toLp 2 (Vᵀ (Fin.castLE (min_le_right m n) i)) : EuclideanSpace ℝ (Fin n)) := by
  rw [toEuclideanLin_tikhonov_eq_sum_of_isSVD h hμ b]
  refine sum_congr rfl fun i _ => ?_
  rw [smul_smul, RCLike.ofReal_real_eq_id, id_eq, mul_div_right_comm]

/-- **§6.1.4** of [golub2013matrix]. For $A \in \mathbb{R}^{m \times n}$ and $b \in \mathbb{R}^m$,
the ridge solution $x(\lambda)$ tends to the minimum-norm least-squares solution
$x_{LS} = A^+ b$ as $\lambda \to 0^+$: "by inspection, it is clear that
$\lim_{\lambda \to 0} x(\lambda) = x_{LS}$". -/
theorem tendsto_ridge_leastSquares (A : Matrix (Fin m) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin m)) :
    Tendsto (fun μ => toEuclideanLin (A.tikhonov μ) b) (𝓝[>] 0)
      (𝓝 (toEuclideanLin A.pinv b)) := by
  have hc : Continuous fun M : Matrix (Fin n) (Fin m) ℝ => toEuclideanLin M b := by
    simp only [toEuclideanLin_apply]
    exact (PiLp.continuous_toLp 2 _).comp (continuous_id.matrix_mulVec continuous_const)
  exact (hc.tendsto _).comp (tendsto_tikhonov_pinv A)

/-- **§6.1.4** of [golub2013matrix]. For $A \in \mathbb{R}^{m \times n}$ and $b \in \mathbb{R}^m$,
"$\|x(\lambda)\|_2$ is a monotone decreasing function of $\lambda$": the map
$\lambda \mapsto \|x(\lambda)\|_2$ is nonincreasing on $\lambda > 0$, and it is strictly
decreasing there if $A^T b \neq 0$. -/
theorem norm_ridge_antitoneOn (A : Matrix (Fin m) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin m)) :
    AntitoneOn (fun μ => ‖toEuclideanLin (A.tikhonov μ) b‖) (Set.Ioi 0) ∧
      (toEuclideanLin Aᵀ b ≠ 0 →
        StrictAntiOn (fun μ => ‖toEuclideanLin (A.tikhonov μ) b‖) (Set.Ioi 0)) := by
  refine ⟨antitoneOn_norm_toEuclideanLin_tikhonov A b, fun hb => ?_⟩
  rw [← conjTranspose_eq_transpose_of_trivial] at hb
  exact strictAntiOn_norm_toEuclideanLin_tikhonov A hb

/-- **Equation (6.1.15)** of [golub2013matrix], ridge regression without the $k$-th equation. Let
$A \in \mathbb{R}^{m \times n}$, $b \in \mathbb{R}^m$, $\lambda \in \mathbb{R}$ and
$1 \le k \le m$, and let $D_k = I - e_k e_k^T = \operatorname{diag}(1, \dots, 1, 0, 1, \dots,
1)$. The source lets "$x_k(\lambda)$ solve $\min \|D_k(Ax - b)\|_2^2 + \lambda \|x\|_2^2$". Here
$x_k(\lambda)$ is defined as
$$x_k(\lambda) = \left((D_k A)^T (D_k A) + \lambda I\right)^{-1} (D_k A)^T (D_k b).$$

The definition applies `Matrix.tikhonov` of $D_k A$ to $D_k b$. Where the matrix is singular,
Lean's inverse is zero. For $\lambda > 0$ it is the minimizer
(`GolubVanLoan.Chapter06.ridgeDeleted_spec`). -/
noncomputable def ridgeDeleted (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (μ : ℝ)
    (k : Fin m) : Fin n → ℝ :=
  (diagonal (Function.update (1 : Fin m → ℝ) k 0) * A).tikhonov μ *ᵥ
    (diagonal (Function.update (1 : Fin m → ℝ) k 0) *ᵥ b)

/-- **Equation (6.1.15)** of [golub2013matrix]. Let $A \in \mathbb{R}^{m \times n}$,
$b \in \mathbb{R}^m$, $\lambda > 0$ and $1 \le k \le m$. Then $x_k(\lambda)$ is the unique
minimizer of $\|D_k(Ax - b)\|_2^2 + \lambda \|x\|_2^2$: a vector $x$ is equal to $x_k(\lambda)$
if and only if it minimizes this function. -/
theorem ridgeDeleted_spec (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) {μ : ℝ} (hμ : 0 < μ)
    (k : Fin m) (x : EuclideanSpace ℝ (Fin n)) :
    x = WithLp.toLp 2 (ridgeDeleted A b μ k) ↔
      ∀ y, ‖toEuclideanLin (diagonal (Function.update (1 : Fin m → ℝ) k 0) * A) x -
            WithLp.toLp 2 (diagonal (Function.update (1 : Fin m → ℝ) k 0) *ᵥ b)‖ ^ 2 +
          μ * ‖x‖ ^ 2 ≤
        ‖toEuclideanLin (diagonal (Function.update (1 : Fin m → ℝ) k 0) * A) y -
            WithLp.toLp 2 (diagonal (Function.update (1 : Fin m → ℝ) k 0) *ᵥ b)‖ ^ 2 +
          μ * ‖y‖ ^ 2 :=
  (eq_toEuclideanLin_tikhonov_iff_isMinOn (diagonal (Function.update (1 : Fin m → ℝ) k 0) * A) hμ
    (WithLp.toLp 2 (diagonal (Function.update (1 : Fin m → ℝ) k 0) *ᵥ b)) x).trans
    isMinOn_univ_iff

/-- **Equation (6.1.16)** of [golub2013matrix]. Let $A \in \mathbb{R}^{m \times n}$,
$b \in \mathbb{R}^m$, $\lambda > 0$ and $1 \le k \le m$. Let
$x(\lambda) = (A^T A + \lambda I)^{-1} A^T b$ and $z_k = (A^T A + \lambda I)^{-1} a_k$. Then
$1 - z_k^T a_k > 0$, and
$$x_k(\lambda) = x(\lambda) + \frac{a_k^T x(\lambda) - b_k}{1 - z_k^T a_k} z_k.$$
-/
theorem equation_6_1_16 (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) {μ : ℝ} (hμ : 0 < μ)
    (k : Fin m) :
    ridgeDeleted A b μ k = A.tikhonov μ *ᵥ b +
        ((A k ⬝ᵥ (A.tikhonov μ *ᵥ b) - b k) /
          (1 - ((Aᵀ * A + μ • 1)⁻¹ *ᵥ A k) ⬝ᵥ A k)) • ((Aᵀ * A + μ • 1)⁻¹ *ᵥ A k) ∧
      0 < 1 - ((Aᵀ * A + μ • 1)⁻¹ *ᵥ A k) ⬝ᵥ A k := by
  refine ⟨tikhonov_deleteRow_eq A b hμ k, ?_⟩
  rw [dotProduct_comm]
  exact one_sub_dotProduct_inv_gram_pos A hμ k

/-- **Equation (6.1.17)** of [golub2013matrix]. Let $A \in \mathbb{R}^{m \times n}$,
$b \in \mathbb{R}^m$, $\lambda > 0$ and $1 \le k \le m$. Then
$$r_k = b_k - a_k^T x_k(\lambda) = \frac{e_k^T (I - A(A^T A + \lambda I)^{-1} A^T) b}{e_k^T (I -
  A(A^T A + \lambda I)^{-1} A^T) e_k},$$
and the denominator is positive. -/
theorem equation_6_1_17 (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) {μ : ℝ} (hμ : 0 < μ)
    (k : Fin m) :
    b k - A k ⬝ᵥ ridgeDeleted A b μ k =
        ((1 - A * (Aᵀ * A + μ • 1)⁻¹ * Aᵀ : Matrix (Fin m) (Fin m) ℝ) *ᵥ b) k /
          (1 - A * (Aᵀ * A + μ • 1)⁻¹ * Aᵀ : Matrix (Fin m) (Fin m) ℝ) k k ∧
      0 < (1 - A * (Aᵀ * A + μ • 1)⁻¹ * Aᵀ : Matrix (Fin m) (Fin m) ℝ) k k :=
  tikhonov_deleteRow_residual_eq A b hμ k

/-- **§6.1.4** of [golub2013matrix], the cross-validation weighted square error. Let
$w \in \mathbb{R}^m$, $A \in \mathbb{R}^{m \times n}$, $b \in \mathbb{R}^m$ and
$\lambda \in \mathbb{R}$. The **cross-validation weighted square error** is
$$C(\lambda) = \frac{1}{m} \sum_{k=1}^{m} w_k (a_k^T x_k(\lambda) - b_k)^2.$$
In the source, "$w_1, \dots, w_m$ are nonnegative weights"; the definition does not need this
condition. -/
noncomputable def crossValidationError (w : Fin m → ℝ) (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (μ : ℝ) : ℝ :=
  (1 / m : ℝ) * ∑ k, w k * (A k ⬝ᵥ ridgeDeleted A b μ k - b k) ^ 2

/-- For a matrix $M$, the $k$-th entry of $Mb$, as a function of $b_k$, has the derivative $M_{kk}$.
-/
private theorem hasDerivAt_mulVec_update (M : Matrix (Fin m) (Fin m) ℝ) (b : Fin m → ℝ)
    (k : Fin m) :
    HasDerivAt (fun t => (M *ᵥ Function.update b k t) k) (M k k) (b k) := by
  have e : (fun t => (M *ᵥ Function.update b k t) k) =
      fun t => (M *ᵥ b) k + M k k * (t - b k) := by
    funext t
    have hu : Function.update b k t = b + Pi.single k (t - b k) := by
      funext j
      by_cases hj : j = k
      · subst hj
        simp
      · simp [hj]
    rw [hu, mulVec_add, Pi.add_apply]
    congr 1
    simp [mulVec, dotProduct, Pi.single_apply]
  rw [e]
  simpa using (((hasDerivAt_id (b k)).sub_const (b k)).const_mul (M k k)).const_add ((M *ᵥ b) k)

/-- **Equation (6.1.18)** of [golub2013matrix]. Let $w, b \in \mathbb{R}^m$,
$A \in \mathbb{R}^{m \times n}$ and $\lambda > 0$. Let $H = A(A^T A + \lambda I)^{-1} A^T$, so
that the residual $r = b - A x(\lambda)$ "is given by the formula $r = [I - H] b$". Then
$\partial r_k / \partial b_k = (I - H)_{kk}$ for every $k$, and
$$C(\lambda) = \frac{1}{m} \sum_{k=1}^{m} w_k \left(\frac{r_k}{\partial r_k / \partial
  b_k}\right)^2.$$

The partial derivative is the derivative at $t = b_k$ of the $k$-th entry of $(I - H) b'$, where
$b'$ is $b$ with its $k$-th entry replaced by $t$. -/
theorem equation_6_1_18 (w : Fin m → ℝ) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) {μ : ℝ}
    (hμ : 0 < μ) :
    (∀ k, HasDerivAt
      (fun t => ((1 - A * (Aᵀ * A + μ • 1)⁻¹ * Aᵀ : Matrix (Fin m) (Fin m) ℝ) *ᵥ
        Function.update b k t) k)
      ((1 - A * (Aᵀ * A + μ • 1)⁻¹ * Aᵀ : Matrix (Fin m) (Fin m) ℝ) k k) (b k)) ∧
    crossValidationError w A b μ = (1 / m : ℝ) * ∑ k, w k *
      (((1 - A * (Aᵀ * A + μ • 1)⁻¹ * Aᵀ : Matrix (Fin m) (Fin m) ℝ) *ᵥ b) k /
        (1 - A * (Aᵀ * A + μ • 1)⁻¹ * Aᵀ : Matrix (Fin m) (Fin m) ℝ) k k) ^ 2 := by
  refine ⟨fun k => hasDerivAt_mulVec_update _ b k, ?_⟩
  rw [crossValidationError]
  congr 1
  refine sum_congr rfl fun k _ => ?_
  rw [← neg_sub, neg_sq, (equation_6_1_17 A b hμ k).1]

/-- For an SVD $U^T A V = \Sigma$ and $\lambda > 0$, $A(A^T A + \lambda I)^{-1} A^T = U
\operatorname{diag}(c_i) U^T$, with $c_i = \sigma_i^2 / (\sigma_i^2 + \lambda)$ for $i < n$ and
$c_i = 0$ otherwise. -/
private theorem hat_eq_of_isSVD {A : Matrix (Fin m) (Fin n) ℝ} {U : Matrix (Fin m) (Fin m) ℝ}
    {σ : ℕ → ℝ} {V : Matrix (Fin n) (Fin n) ℝ} (h : IsSVD A U σ V) {μ : ℝ} (hμ : 0 < μ) :
    A * (Aᵀ * A + μ • 1)⁻¹ * Aᵀ = U * diagonal (fun i : Fin m =>
      if (i : ℕ) < n then σ i * (σ i / (σ i ^ 2 + μ)) else 0) * Uᵀ := by
  have hV : star V * V = 1 := mem_unitaryGroup_iff'.1 h.mem_unitaryGroup_right
  have hT : A * (Aᵀ * A + μ • 1)⁻¹ * Aᵀ = A * A.tikhonov μ := by
    rw [tikhonov_eq_real, Matrix.mul_assoc]
  rw [hT, h.tikhonov_eq hμ]
  conv_lhs => rw [h.eq_mul_mul_star]
  have e : U * (rectDiagonal fun i => ((σ i : ℝ) : ℝ) : Matrix (Fin m) (Fin n) ℝ) * star V *
      (V * (rectDiagonal fun i => ((σ i / (σ i ^ 2 + μ) : ℝ) : ℝ) :
        Matrix (Fin n) (Fin m) ℝ) * star U) =
      U * ((rectDiagonal fun i => ((σ i : ℝ) : ℝ) : Matrix (Fin m) (Fin n) ℝ) *
        (rectDiagonal fun i => ((σ i / (σ i ^ 2 + μ) : ℝ) : ℝ) : Matrix (Fin n) (Fin m) ℝ)) *
        star U := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (star V), hV, Matrix.one_mul]
  simp only [RCLike.ofReal_real_eq_id, id_eq] at e ⊢
  rw [e, rectDiagonal_mul_rectDiagonal, rectDiagonal_eq_diagonal, star_eq_conjTranspose,
    conjTranspose_eq_transpose_of_trivial]

/-- **Equation (6.1.19)** of [golub2013matrix]. Let $U^T A V = \Sigma$ be an SVD of
$A \in \mathbb{R}^{m \times n}$ with $U = (u_{kj})$, let $w, b \in \mathbb{R}^m$, let
$\lambda > 0$, and let $\tilde b = U^T b$. Then
$$C(\lambda) = \frac{1}{m} \sum_{k=1}^{m} w_k \left[\frac{b_k - \sum_{j=1}^{\min(m, n)} u_{kj}
  \tilde b_j \frac{\sigma_j^2}{\sigma_j^2 + \lambda}}{1 - \sum_{j=1}^{\min(m, n)} u_{kj}^2
  \frac{\sigma_j^2}{\sigma_j^2 + \lambda}}\right]^2.$$
The terms with $j > r = \operatorname{rank}(A)$ vanish, so the inner sums are the sums to $r$ of
the source.

**Typo.** The source prints $\tilde b_k$ in the numerator. The correct entry is $b_k$: as
$\lambda \to \infty$, the numerator must tend to $b_k$. -/
theorem equation_6_1_19 (w : Fin m → ℝ) {A : Matrix (Fin m) (Fin n) ℝ}
    {U : Matrix (Fin m) (Fin m) ℝ} {σ : ℕ → ℝ} {V : Matrix (Fin n) (Fin n) ℝ} (h : IsSVD A U σ V)
    (b : Fin m → ℝ) {μ : ℝ} (hμ : 0 < μ) :
    crossValidationError w A b μ = (1 / m : ℝ) * ∑ k, w k *
      ((b k - ∑ j : Fin (min m n), U k (Fin.castLE (min_le_left m n) j) *
          (Uᵀ *ᵥ b) (Fin.castLE (min_le_left m n) j) * (σ j ^ 2 / (σ j ^ 2 + μ))) /
        (1 - ∑ j : Fin (min m n), U k (Fin.castLE (min_le_left m n) j) ^ 2 *
          (σ j ^ 2 / (σ j ^ 2 + μ)))) ^ 2 := by
  rw [(equation_6_1_18 w A b hμ).2, hat_eq_of_isSVD h hμ]
  congr 1
  refine sum_congr rfl fun k _ => ?_
  congr 3
  · rw [sub_mulVec, one_mulVec, Pi.sub_apply, ← mulVec_mulVec, ← mulVec_mulVec]
    congr 1
    have e := Fin.sum_castLE_eq_sum_ite (min_le_left m n) fun i : Fin m =>
      U k i * (Uᵀ *ᵥ b) i * (σ i ^ 2 / (σ i ^ 2 + μ))
    simp only [Fin.val_castLE] at e
    rw [e]
    change ∑ i, U k i * (diagonal _ *ᵥ (Uᵀ *ᵥ b)) i = _
    refine sum_congr rfl fun i _ => ?_
    rw [mulVec_diagonal]
    have hi := i.isLt
    by_cases hin : (i : ℕ) < n
    · rw [ite_eq_left (lt_min hi hin), ite_eq_left hin]
      ring
    · rw [ite_eq_right (fun h' => hin (lt_of_lt_of_le h' (min_le_right m n))), ite_eq_right hin]
      ring
  · rw [Matrix.sub_apply, one_apply_eq]
    congr 1
    have e := Fin.sum_castLE_eq_sum_ite (min_le_left m n) fun i : Fin m =>
      U k i ^ 2 * (σ i ^ 2 / (σ i ^ 2 + μ))
    simp only [Fin.val_castLE] at e
    rw [e, Matrix.mul_apply]
    refine sum_congr rfl fun i _ => ?_
    have hi := i.isLt
    rw [Matrix.mul_apply, sum_eq_single i, diagonal_apply_eq, transpose_apply]
    · by_cases hin : (i : ℕ) < n
      · rw [ite_eq_left (lt_min hi hin), ite_eq_left hin]
        ring
      · rw [ite_eq_right (fun h' => hin (lt_of_lt_of_le h' (min_le_right m n))),
          ite_eq_right hin]
        ring
    · intro j _ hj
      rw [diagonal_apply_ne _ hj, mul_zero]
    · intro h'
      exact absurd (mem_univ _) h'

/-! ### §6.1.5 Tikhonov regularization -/

/-- **Equation (6.1.20)** of [golub2013matrix], Tikhonov regularization. Let
$A \in \mathbb{R}^{m \times n}$, $B \in \mathbb{R}^{n \times n}$, $b \in \mathbb{R}^m$,
$\lambda \ge 0$ and $x \in \mathbb{R}^n$. Then
$$\left\| \begin{bmatrix} A \\ \sqrt{\lambda} B \end{bmatrix} x - \begin{bmatrix} b \\ 0
  \end{bmatrix} \right\|_2^2 = \|Ax - b\|_2^2 + \lambda \|Bx\|_2^2,$$
and $x$ is a least-squares solution of the stacked problem if and only if it minimizes
$\|Ax - b\|_2^2 + \lambda \|Bx\|_2^2$. -/
theorem equation_6_1_20 (A : Matrix (Fin m) (Fin n) ℝ) (B : Matrix (Fin n) (Fin n) ℝ)
    (b : EuclideanSpace ℝ (Fin m)) {μ : ℝ} (hμ : 0 ≤ μ) (x : EuclideanSpace ℝ (Fin n)) :
    (‖toEuclideanLin (fromRows A (Real.sqrt μ • B)) x -
        WithLp.toLp 2 (Sum.elim (WithLp.ofLp b) 0)‖ ^ 2 =
      ‖toEuclideanLin A x - b‖ ^ 2 + μ * ‖toEuclideanLin B x‖ ^ 2) ∧
    (IsLeastSquaresSolution (fromRows A (Real.sqrt μ • B))
        (WithLp.toLp 2 (Sum.elim (WithLp.ofLp b) 0)) x ↔
      ∀ y, ‖toEuclideanLin A x - b‖ ^ 2 + μ * ‖toEuclideanLin B x‖ ^ 2 ≤
        ‖toEuclideanLin A y - b‖ ^ 2 + μ * ‖toEuclideanLin B y‖ ^ 2) := by
  refine ⟨?_, ?_⟩
  · rw [norm_fromRows_sub_sq, WithLp.toLp_ofLp, norm_sqrt_smul_sub_zero_sq hμ]
  · have h := isLeastSquaresSolution_fromRows_iff A B (WithLp.ofLp b) 0 hμ x
    simp only [smul_zero, WithLp.toLp_ofLp, WithLp.toLp_zero, sub_zero,
      RCLike.ofReal_real_eq_id, id_eq] at h
    exact h

/-- **Equation (6.1.21)** of [golub2013matrix]. Let $A \in \mathbb{R}^{m \times n}$,
$B \in \mathbb{R}^{n \times n}$ and $\lambda > 0$. "The normal equations for this problem have
the form $(A^T A + \lambda B^T B) x = A^T b$. This system is nonsingular if
$\operatorname{null}(A) \cap \operatorname{null}(B) = \{0\}$." Precisely,
$A^T A + \lambda B^T B$ is positive definite if and only if $\operatorname{null}(A) \cap
\operatorname{null}(B) = \{0\}$. In that case, for every $b \in \mathbb{R}^m$, a vector $x$
minimizes $\|Ax - b\|_2^2 + \lambda \|Bx\|_2^2$ if and only if
$(A^T A + \lambda B^T B) x = A^T b$. -/
theorem equation_6_1_21 (A : Matrix (Fin m) (Fin n) ℝ) (B : Matrix (Fin n) (Fin n) ℝ) {μ : ℝ}
    (hμ : 0 < μ) :
    ((Aᵀ * A + μ • (Bᵀ * B)).PosDef ↔
      LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin = ⊥) ∧
    (LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin = ⊥ →
      ∀ (b : EuclideanSpace ℝ (Fin m)) (x : EuclideanSpace ℝ (Fin n)),
        (∀ y, ‖toEuclideanLin A x - b‖ ^ 2 + μ * ‖toEuclideanLin B x‖ ^ 2 ≤
            ‖toEuclideanLin A y - b‖ ^ 2 + μ * ‖toEuclideanLin B y‖ ^ 2) ↔
          toEuclideanLin (Aᵀ * A + μ • (Bᵀ * B)) x = toEuclideanLin Aᵀ b) := by
  refine ⟨?_, fun hAB b x => ?_⟩
  · have h := posDef_gram_add_smul_gram_iff A B hμ
    simp only [conjTranspose_eq_transpose_of_trivial, RCLike.ofReal_real_eq_id, id_eq] at h
    exact h
  · have h := eq_toEuclideanLin_generalFormTikhonov_iff A B hμ hAB b x
    simp only [conjTranspose_eq_transpose_of_trivial, RCLike.ofReal_real_eq_id, id_eq] at h
    exact (isMinOn_univ_iff.symm.trans h.2.symm).trans h.1

/-! ### §6.1.6 The generalized singular value decomposition -/

/-- **Theorem 6.1.1** of [golub2013matrix] (generalized singular value decomposition). Let
$A \in \mathbb{R}^{m_1 \times n_1}$ and $B \in \mathbb{R}^{m_2 \times n_1}$ with $m_1 \ge n_1$,
let $r = \operatorname{rank}([A; B])$, and let $p = \max\{r - m_2, 0\}$. There exist orthogonal
$U_1 \in \mathbb{R}^{m_1 \times m_1}$ and $U_2 \in \mathbb{R}^{m_2 \times m_2}$, an invertible
$X \in \mathbb{R}^{n_1 \times n_1}$, and real numbers $\alpha_1, \alpha_2, \dots$ and
$\beta_1, \beta_2, \dots$ such that
$$U_1^T A X = D_A, \qquad U_2^T B X = D_B,$$
which are (6.1.22) and (6.1.23). Here $D_A \in \mathbb{R}^{m_1 \times n_1}$ has the diagonal
$\alpha_1, \dots, \alpha_{n_1}$ and zeros elsewhere, and $D_B \in \mathbb{R}^{m_2 \times n_1}$
has the entry $\beta_{i+p}$ at the position $(i, i + p)$ and zeros elsewhere. Moreover
$\alpha_i = 1$ and $\beta_i = 0$ for $i \le p$, and $\alpha_i = \beta_i = 0$ for $i > r$. In
block form, $D_A$ has the diagonal blocks $I_p$, $\operatorname{diag}(\alpha_{p+1}, \dots,
\alpha_r)$ and $0$, and $D_B$ has the blocks $0$, $\operatorname{diag}(\beta_{p+1}, \dots,
\beta_r)$ and $0$.

**Typo.** The source labels the rows of the blocks of $D_B$ with $p$, $r - p$ and $m_2 - r$. The
correct labels are $r - p$ and $m_2 - r + p$. The source also writes $n_{1-r}$ for $n_1 - r$.

The matrix $D_A$ is `Matrix.rectDiagonal α`, and $D_B$ is `Matrix.shiftedRectDiagonal p β`.
Indices are 0-based, so the condition for $i \le p$ is stated for `i < p`. The theorem as
printed does not state $\alpha_i^2 + \beta_i^2 = 1$, which its proof gives; this is
`GolubVanLoan.Chapter06.theorem_6_1_1_b`. The proof in the source cites "(6.1.21) and (6.1.22)"
for (6.1.22)–(6.1.23). -/
theorem theorem_6_1_1 {m₁ m₂ n₁ : ℕ} (hmn : n₁ ≤ m₁) (A : Matrix (Fin m₁) (Fin n₁) ℝ)
    (B : Matrix (Fin m₂) (Fin n₁) ℝ) :
    ∃ (U₁ : Matrix (Fin m₁) (Fin m₁) ℝ) (U₂ : Matrix (Fin m₂) (Fin m₂) ℝ)
      (X : Matrix (Fin n₁) (Fin n₁) ℝ) (α β : ℕ → ℝ),
      U₁ ∈ orthogonalGroup (Fin m₁) ℝ ∧ U₂ ∈ orthogonalGroup (Fin m₂) ℝ ∧ IsUnit X ∧
      U₁ᵀ * A * X = rectDiagonal α ∧
      U₂ᵀ * B * X = shiftedRectDiagonal ((fromRows A B).rank - m₂) β ∧
      (∀ i < (fromRows A B).rank - m₂, α i = 1 ∧ β i = 0) ∧
      ∀ i, (fromRows A B).rank ≤ i → α i = 0 ∧ β i = 0 := by
  obtain ⟨U₁, U₂, X, α, β, h⟩ := exists_isGSVD hmn A B
  refine ⟨U₁, U₂, X, α, β, h.mem_unitaryGroup_left₁, h.mem_unitaryGroup_left₂, h.isUnit, ?_, ?_,
    h.eq_one_and_eq_zero_of_lt, h.eq_zero_and_eq_zero_of_rank_le⟩
  · have e := h.star_mul_mul₁
    simp only [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial,
      RCLike.ofReal_real_eq_id, id_eq] at e
    exact e
  · have e := h.star_mul_mul₂
    simp only [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial,
      RCLike.ofReal_real_eq_id, id_eq] at e
    exact e

/-- **Theorem 6.1.1** of [golub2013matrix], with the clause that the source does not print. Let
$A \in \mathbb{R}^{m_1 \times n_1}$ and $B \in \mathbb{R}^{m_2 \times n_1}$ with $m_1 \ge n_1$.
There is a decomposition as in `GolubVanLoan.Chapter06.theorem_6_1_1` in which, moreover,
$\alpha_i \ge 0$ and $\beta_i \ge 0$ for all $i$, and $\alpha_i^2 + \beta_i^2 = 1$ for
$p < i \le r$.

The pairs $(\alpha_i, \beta_i)$ for $p < i \le r$ are the cosine–sine pairs of the CS
decomposition (6.1.25) in the proof. The conclusion is the full specification `Matrix.IsGSVD`. -/
theorem theorem_6_1_1_b {m₁ m₂ n₁ : ℕ} (hmn : n₁ ≤ m₁) (A : Matrix (Fin m₁) (Fin n₁) ℝ)
    (B : Matrix (Fin m₂) (Fin n₁) ℝ) : ∃ U₁ U₂ X α β, IsGSVD A B U₁ U₂ X α β :=
  exists_isGSVD hmn A B

/-- **§6.1.6** of [golub2013matrix]. Let $A \in \mathbb{R}^{m_1 \times n_1}$, and let
$U_1^T A X = D_A$ and $U_2^T I X = D_B$ be a GSVD of $(A, I_{n_1})$. Then $\beta_i > 0$ for
$1 \le i \le n_1$, and
$$U_1^T A U_2 = \operatorname{diag}(\alpha_1 / \beta_1, \dots, \alpha_{n_1} / \beta_{n_1}).$$

**Correction.** The source says "if $B = I_{n_1}$ and we set $X = U_2$, then we obtain the SVD
of $A$". This is loose: the GSVD gives $X = U_2 D_B$, and the diagonal factor is
$\operatorname{diag}(\alpha_i / \beta_i)$.

The diagonal matrix is `Matrix.rectDiagonal` of $i \mapsto \alpha_i / \beta_i$. -/
theorem gsvd_one {m₁ n₁ : ℕ} {A : Matrix (Fin m₁) (Fin n₁) ℝ} {U₁ : Matrix (Fin m₁) (Fin m₁) ℝ}
    {U₂ X : Matrix (Fin n₁) (Fin n₁) ℝ} {α β : ℕ → ℝ} (h : IsGSVD A 1 U₁ U₂ X α β) :
    (∀ i < n₁, 0 < β i) ∧ U₁ᵀ * A * U₂ = rectDiagonal fun i => α i / β i := by
  have hβ := h.pos_of_eq_one
  have e := h.star_mul_mul_eq_of_eq_one
  simp only [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial,
    RCLike.ofReal_real_eq_id, id_eq] at e
  exact ⟨hβ, e⟩

/-- **§6.1.6** of [golub2013matrix]. "The GSVD is related to the generalized eigenvalue problem
$A^T A x = \mu^2 B^T B x$": let $U_1^T A X = D_A$, $U_2^T B X = D_B$ be a GSVD of $(A, B)$ with
$m_1 \ge n_1$, and let $x_i$ be the $i$-th column of $X$. Then
$$\beta_i^2 A^T A x_i = \alpha_i^2 B^T B x_i,$$
and if $\beta_i \neq 0$, then $A^T A x_i = (\alpha_i / \beta_i)^2 B^T B x_i$, so $x_i$ is a
generalized eigenvector with $\mu_i = \alpha_i / \beta_i$. -/
theorem gsvd_generalizedEigen {m₁ m₂ n₁ : ℕ} {A : Matrix (Fin m₁) (Fin n₁) ℝ}
    {B : Matrix (Fin m₂) (Fin n₁) ℝ} {U₁ : Matrix (Fin m₁) (Fin m₁) ℝ}
    {U₂ : Matrix (Fin m₂) (Fin m₂) ℝ} {X : Matrix (Fin n₁) (Fin n₁) ℝ} {α β : ℕ → ℝ}
    (h : IsGSVD A B U₁ U₂ X α β) (hmn : n₁ ≤ m₁) (i : Fin n₁) :
    β i ^ 2 • ((Aᵀ * A) *ᵥ X.col i) = α i ^ 2 • ((Bᵀ * B) *ᵥ X.col i) ∧
      (β i ≠ 0 → (Aᵀ * A) *ᵥ X.col i = (α i / β i) ^ 2 • ((Bᵀ * B) *ᵥ X.col i)) := by
  have e := h.gram_mulVec_col hmn i
  simp only [conjTranspose_eq_transpose_of_trivial, RCLike.ofReal_real_eq_id, id_eq] at e
  refine ⟨e, fun hβ => ?_⟩
  have hβ2 : β i ^ 2 ≠ 0 := pow_ne_zero 2 hβ
  rw [div_pow, div_eq_inv_mul, mul_smul, ← e, smul_smul, inv_mul_cancel₀ hβ2, one_smul]

/-- **Equation (6.1.26)** of [golub2013matrix], and the display before it. Let
$A \in \mathbb{R}^{m \times n}$ with $m \ge n$, let $B \in \mathbb{R}^{n \times n}$ be
nonsingular, and let $U_1^T A X = D_A$, $U_2^T B X = D_B$ be a GSVD of $(A, B)$, with columns
$x_k$ of $X$. Let $\lambda > 0$, $b \in \mathbb{R}^m$ and $\tilde b = U_1^T b$. Then
$$X^T (A^T A + \lambda B^T B) X = \operatorname{diag}(\alpha_1^2 + \lambda \beta_1^2, \dots,
  \alpha_n^2 + \lambda \beta_n^2),$$
which is $D_A^T D_A + \lambda D_B^T D_B$, and
$$x(\lambda) = \sum_{k=1}^{n} \frac{\alpha_k \tilde b_k}{\alpha_k^2 + \lambda \beta_k^2} x_k$$
minimizes $\|Ax - b\|_2^2 + \lambda \|Bx\|_2^2$, so it solves (6.1.20).

In the source, the GSVD "transforms the system (6.1.21) to $(D_A^T D_A + \lambda D_B^T D_B) y =
D_A^T \tilde b$ where $x = Xy$". -/
theorem equation_6_1_26 {A : Matrix (Fin m) (Fin n) ℝ} {B : Matrix (Fin n) (Fin n) ℝ}
    (hB : IsUnit B) {U₁ : Matrix (Fin m) (Fin m) ℝ} {U₂ X : Matrix (Fin n) (Fin n) ℝ}
    {α β : ℕ → ℝ} (h : IsGSVD A B U₁ U₂ X α β) (hnm : n ≤ m) {μ : ℝ} (hμ : 0 < μ)
    (b : EuclideanSpace ℝ (Fin m)) :
    Xᵀ * (Aᵀ * A + μ • (Bᵀ * B)) * X = diagonal (fun i : Fin n => α i ^ 2 + μ * β i ^ 2) ∧
    ∀ x : EuclideanSpace ℝ (Fin n),
      x = WithLp.toLp 2 (∑ k : Fin n, (α k / (α k ^ 2 + μ * β k ^ 2) *
        (U₁ᵀ *ᵥ WithLp.ofLp b) (Fin.castLE hnm k)) • X.col k) →
      ∀ y, ‖toEuclideanLin A x - b‖ ^ 2 + μ * ‖toEuclideanLin B x‖ ^ 2 ≤
        ‖toEuclideanLin A y - b‖ ^ 2 + μ * ‖toEuclideanLin B y‖ ^ 2 := by
  refine ⟨?_, fun x hx => ?_⟩
  · have e := h.conjTranspose_mul_gram_add_smul_gram_mul hnm μ
    simp only [conjTranspose_eq_transpose_of_trivial, RCLike.ofReal_real_eq_id, id_eq] at e
    exact e
  · have hker : LinearMap.ker B.mulVecLin = ⊥ :=
      LinearMap.ker_eq_bot.2 (mulVec_injective_iff_isUnit.2 hB)
    have hAB : LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin = ⊥ := by
      rw [hker, inf_bot_eq]
    refine isMinOn_univ_iff.1 ((eq_toEuclideanLin_generalFormTikhonov_iff A B hμ hAB b x).2.1 ?_)
    have e := generalFormTikhonov_mulVec_eq_sum_of_isGSVD hB h hnm hμ (WithLp.ofLp b)
    simp only [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial,
      RCLike.ofReal_real_eq_id, id_eq] at e
    rw [hx, toEuclideanLin_apply, e]

end GolubVanLoan.Chapter06
