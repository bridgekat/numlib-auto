/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.InnerProductSpace.LeastSquares`, beside the least-squares solutions
of `Numlib/LinearAlgebra/Matrix/LeastSquares`.
-/
import Numlib.LinearAlgebra.Matrix.LeastSquares

/-!
# Weighted and generalized least squares

This file studies the weighted and generalized least-squares problems of [golub2013matrix],
§6.1.1–6.1.3. Let $A \in \mathbb{K}^{m \times n}$ and $b \in \mathbb{K}^m$, where $\mathbb{K}$ is
$\mathbb{R}$ or $\mathbb{C}$. For an invertible weight factor $M \in \mathbb{K}^{m \times m}$, the
weighted problem is to minimize $\|M(Ax - b)\|$, and for $W = M^H M$ and $A$ of full column rank its
unique solution is $x_W = (A^H W A)^{-1} A^H W b$. The file compares $x_W$ with the unweighted
solution $A^+ b$, shows that a change of one row weight is a rank-one update of the normal
equations, computes the derivative of a residual component in its own weight, and treats the
augmented system. Paige's generalized problem minimizes $\|v\|$ subject to $b = Ax + Bv$; the file
reduces it to the weighted problem for a nonsingular $B$ and proves the correctness of Paige's
method. Finally, column weighting $x = G^{-1} y$ gives the least-squares solution of least $G$-norm.

## Main definitions

* `Matrix.weightedLeastSquaresOp`: the weighted solution operator $(A^H W A)^{-1} A^H W$.
* `Matrix.weightedResidual`: the residual $b - A x_w$ of the weighted solution, as a function of
  real weights $w$.
* `Matrix.IsGeneralizedLeastSquaresSolution`: the pair $(x, v)$ minimizes $\|v\|$ subject to
  $b = Ax + Bv$.

## Main results

* `Matrix.isLeastSquaresSolution_weightedLeastSquaresOp`: for an invertible $M$ and $A$ of full
  column rank, $x$ minimizes $\|M(Ax - b)\|$ if and only if $x = (A^H M^H M A)^{-1} A^H M^H M b$
  ([golub2013matrix] (6.1.1)–(6.1.2)).
* `Matrix.weightedLeastSquaresOp_mulVec_sub_pinv_mulVec`: $x_W - A^+ b = (A^H W A)^{-1} A^H (W -
  I)(b - A A^+ b)$ ([golub2013matrix] (6.1.3)).
* `Matrix.conjTranspose_mul_diagonal_update_mul`, `Matrix.conjTranspose_mul_diagonal_update_mulVec`:
  a change of one row weight is a rank-one update of the weighted normal equations. The deletion of
  a row is the weight $0$, as in `Matrix.tikhonov_deleteRow_eq` in
  `Numlib.LinearAlgebra.Matrix.LeastSquares.Regularized`.
* `Matrix.hasDerivAt_weightedResidual`, `Matrix.antitoneOn_abs_weightedResidual`: the derivative of
  a residual component in its own weight, and the decrease of its absolute value as that weight
  grows ([golub2013matrix] (6.1.4)).
* `Matrix.isLeastSquaresSolution_of_augmented`: a solution of the augmented system solves the
  weighted problem ([golub2013matrix] (6.1.5)).
* `Matrix.isGeneralizedLeastSquaresSolution_iff`: for a nonsingular $B$ the generalized problem is
  the weighted problem with weight factor $B^{-1}$ ([golub2013matrix] (6.1.7)–(6.1.8)).
* `Matrix.isGeneralizedLeastSquaresSolution_of_paige`: Paige's method solves the generalized problem
  ([golub2013matrix] (6.1.9)–(6.1.10)).
* `Matrix.isLeastSquaresSolution_mul_inv_iff`,
  `Matrix.IsMinNormLeastSquaresSolution.norm_le_of_mul_inv`: column weighting ([golub2013matrix]
  §6.1.3).

## Implementation notes

* Vectors are `EuclideanSpace 𝕜 m`, and matrices act on them through `Matrix.toEuclideanLin`, as in
  `Numlib.LinearAlgebra.Matrix.LeastSquares`. The scalars are `[RCLike 𝕜]`, except in the statements
  about a derivative in a weight, which are over `ℝ`.
* There is no separate predicate for the weighted problem. The statement "$x$ minimizes
  $\|M(Ax - b)\|$" is `Matrix.IsLeastSquaresSolution (M * A) (toEuclideanLin M b) x`. A surface
  module can name the diagonal-weight problem of the source as an abbreviation of it.
* `Matrix.weightedLeastSquaresOp W A` $= (A^H W A)^{-1} A^H W$ is the solution operator of the
  weighted problem for $A$ of full column rank and a Hermitian positive definite $W = M^H M$. It is
  the full-rank weighted pseudoinverse, not the weighted pseudoinverse of general rank of the
  literature. Here "weighted" always means weights on the rows (or on the columns).
* The augmented-system result has a general weight factor $M$, so the unweighted augmented system
  ([golub2013matrix] (5.3.20)) is its case $M = I$.
* `Matrix.IsGeneralizedLeastSquaresSolution` is defined for rank-deficient $A$ and $B$. Paige's
  method is stated through the equations that define its output, so the statement needs neither $B$
  nor the factor $S$ to be triangular.
-/

open Finset
open scoped ComplexOrder

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-! ### The weighted solution operator -/

section Weighted

/-- The **weighted least-squares solution operator** of $W \in \mathbb{K}^{m \times m}$ and
$A \in \mathbb{K}^{m \times n}$ is the matrix $$(A^H W A)^{-1} A^H W \in \mathbb{K}^{n \times
m}.$$ This is (6.1.2) of [golub2013matrix] with $W = D^2$.

When $W = M^H M$ for an invertible $M$ and $A$ has full column rank, the operator solves the
problem of minimizing $\|M(Ax - b)\|$ (`Matrix.isLeastSquaresSolution_weightedLeastSquaresOp`).
When $A^H W A$ is singular, Lean's `⁻¹` gives the zero matrix as its inverse, and the operator
has no meaning. It is not the weighted pseudoinverse of general rank. -/
noncomputable def weightedLeastSquaresOp (W : Matrix m m 𝕜) (A : Matrix m n 𝕜) : Matrix n m 𝕜 :=
  (Aᴴ * W * A)⁻¹ * Aᴴ * W

/-- Let $W \in \mathbb{K}^{m \times m}$ and $A \in \mathbb{K}^{m \times n}$. The weighted solution
operator `Matrix.weightedLeastSquaresOp W A` is equal to $(A^H W A)^{-1} A^H W$. -/
theorem weightedLeastSquaresOp_def (W : Matrix m m 𝕜) (A : Matrix m n 𝕜) :
    weightedLeastSquaresOp W A = (Aᴴ * W * A)⁻¹ * Aᴴ * W := rfl

variable [DecidableEq m]

/-- Let $M \in \mathbb{K}^{m \times m}$ be invertible, let $A \in \mathbb{K}^{m \times n}$ have
linearly independent columns, and let $b \in \mathbb{K}^m$ and $x \in \mathbb{K}^n$. Then $x$
minimizes $\|M(Ay - b)\|$ over all $y \in \mathbb{K}^n$ if and only if $$x = (A^H M^H M A)^{-1}
A^H M^H M b.$$ This is (6.1.1)–(6.1.2) of [golub2013matrix].

The weighted problem is `Matrix.IsLeastSquaresSolution (M * A) (toEuclideanLin M b) x`, and the
solution is `Matrix.weightedLeastSquaresOp (Mᴴ * M) A` applied to $b$. The proof uses that $MA$
has full column rank and that its pseudoinverse is $((MA)^H MA)^{-1} (MA)^H$. -/
theorem isLeastSquaresSolution_weightedLeastSquaresOp {M : Matrix m m 𝕜} (hM : IsUnit M)
    {A : Matrix m n 𝕜} (hA : LinearIndependent 𝕜 Aᵀ) {b : EuclideanSpace 𝕜 m}
    {x : EuclideanSpace 𝕜 n} :
    IsLeastSquaresSolution (M * A) (toEuclideanLin M b) x ↔
      x = toEuclideanLin (weightedLeastSquaresOp (Mᴴ * M) A) b := by
  have hMA : LinearIndependent 𝕜 (M * A)ᵀ := by
    refine mulVec_injective_iff.1 fun y z hyz => ?_
    have h1 : Function.Injective M.mulVec := mulVec_injective_iff_isUnit.2 hM
    have h2 : Function.Injective A.mulVec := mulVec_injective_iff.2 hA
    exact h2 (h1 (by simpa only [mulVec_mulVec] using hyz))
  have hgram : (M * A)ᴴ * (M * A) = Aᴴ * (Mᴴ * M) * A := by
    simp only [conjTranspose_mul, Matrix.mul_assoc]
  rw [isLeastSquaresSolution_iff_eq_pinv_of_linearIndependent hMA,
    pinv_eq_inv_conjTranspose_mul_self_mul_conjTranspose hMA, ← toEuclideanLin_mul_apply, hgram,
    weightedLeastSquaresOp, conjTranspose_mul]
  simp only [Matrix.mul_assoc]

/-- Let $W \in \mathbb{K}^{m \times m}$ and $A \in \mathbb{K}^{m \times n}$ be such that $A^H W A$
is invertible, and let $b \in \mathbb{K}^m$. Let $x_W = (A^H W A)^{-1} A^H W b$ be the weighted
solution and $x = A^+ b$ the unweighted least-squares solution of least norm. Then $$x_W - x =
(A^H W A)^{-1} A^H (W - I)(b - Ax).$$ This is (6.1.3) of [golub2013matrix].

No rank hypothesis on $A$ is needed beyond the invertibility of $A^H W A$. The proof subtracts
the two normal equations: $A^H(b - Ax) = 0$, so $A^H W A (x_W - x) = A^H W (b - Ax) - A^H (b -
Ax)$. The matrix $A^+$ is `Matrix.pinv A`. -/
theorem weightedLeastSquaresOp_mulVec_sub_pinv_mulVec {W : Matrix m m 𝕜} {A : Matrix m n 𝕜}
    (hW : IsUnit (Aᴴ * W * A)) (b : EuclideanSpace 𝕜 m) :
    toEuclideanLin (weightedLeastSquaresOp W A) b - toEuclideanLin A.pinv b =
      toEuclideanLin ((Aᴴ * W * A)⁻¹ * Aᴴ * (W - 1))
        (b - toEuclideanLin A (toEuclideanLin A.pinv b)) := by
  have hdet : IsUnit (Aᴴ * W * A).det := (isUnit_iff_isUnit_det _).1 hW
  have h1 : (Aᴴ * W * A)⁻¹ * (Aᴴ * W * A) = 1 := nonsing_inv_mul _ hdet
  have h2 : Aᴴ * (A * A.pinv) = Aᴴ := conjTranspose_mul_mul_pinv A
  have key : weightedLeastSquaresOp W A - A.pinv =
      (Aᴴ * W * A)⁻¹ * Aᴴ * (W - 1) * (1 - A * A.pinv) := by
    have e1 : A.pinv = (Aᴴ * W * A)⁻¹ * (Aᴴ * W * A) * A.pinv := by rw [h1, Matrix.one_mul]
    have e2 : (Aᴴ * W * A)⁻¹ * (Aᴴ * (A * A.pinv)) = (Aᴴ * W * A)⁻¹ * Aᴴ := by rw [h2]
    conv_lhs => rw [e1]
    rw [weightedLeastSquaresOp]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc] at e2 ⊢
    rw [e2]
    abel
  rw [← LinearMap.sub_apply, ← map_sub, key, toEuclideanLin_mul_apply]
  congr 1
  rw [toEuclideanLin_sub_apply, toEuclideanLin_one_apply, toEuclideanLin_mul_apply]

/-- Let $M \in \mathbb{K}^{m \times m}$ be invertible, let $A \in \mathbb{K}^{m \times n}$, and let
$b, r \in \mathbb{K}^m$ and $x \in \mathbb{K}^n$. If $r$ and $x$ solve the **augmented system**
$$(M^H M)^{-1} r + Ax = b, \qquad A^H r = 0,$$ then $x$ minimizes $\|M(Ay - b)\|$ over all
$y \in \mathbb{K}^n$. This is (6.1.5) of [golub2013matrix], and its case $M = I$ is (5.3.20).

The first equation gives $r = M^H M (b - Ax)$, so the second equation is the normal equations of
the weighted problem. -/
theorem isLeastSquaresSolution_of_augmented {M : Matrix m m 𝕜} (hM : IsUnit M)
    {A : Matrix m n 𝕜} {b r : EuclideanSpace 𝕜 m} {x : EuclideanSpace 𝕜 n}
    (h1 : toEuclideanLin (Mᴴ * M)⁻¹ r + toEuclideanLin A x = b) (h2 : toEuclideanLin Aᴴ r = 0) :
    IsLeastSquaresSolution (M * A) (toEuclideanLin M b) x := by
  have hW : IsUnit (Mᴴ * M) := ((isUnit_conjTranspose M).2 hM).mul hM
  have hr : toEuclideanLin (Mᴴ * M) (b - toEuclideanLin A x) = r := by
    rw [← h1, add_sub_cancel_right, toEuclideanLin_mul_nonsing_inv_apply hW]
  rw [isLeastSquaresSolution_iff_normalEquations]
  have key : toEuclideanLin (M * A)ᴴ (toEuclideanLin M b) - toEuclideanLin ((M * A)ᴴ * (M * A)) x =
      toEuclideanLin Aᴴ (toEuclideanLin (Mᴴ * M) (b - toEuclideanLin A x)) := by
    simp only [conjTranspose_mul, map_sub, ← toEuclideanLin_mul_apply, Matrix.mul_assoc]
  rw [hr, h2, sub_eq_zero] at key
  exact key.symm

end Weighted

/-! ### Real weights: the derivative of a residual in its own weight -/

section RealWeights

variable [DecidableEq m] {A : Matrix m n ℝ}

/-- The **residual of the weighted solution** as a function of the weights. For
$A \in \mathbb{R}^{m \times n}$, $b \in \mathbb{R}^m$ and weights $w \in \mathbb{R}^m$, it is
$$r(w) = b - A x_w, \qquad x_w = (A^T \operatorname{diag}(w) A)^{-1} A^T \operatorname{diag}(w)
b.$$ This is the residual $r(\delta)$ of [golub2013matrix], §6.1.1.

The matrix $D(\delta)^2$ of the source, whose $k$-th weight $d_k^2$ is changed to
$d_k^2 (1 + \delta)$, is `diagonal (Function.update (d²) k (d_k² (1 + δ)))`. When
$A^T \operatorname{diag}(w) A$ is singular, the inverse is the zero matrix and $r(w) = b$. -/
noncomputable def weightedResidual (A : Matrix m n ℝ) (b : m → ℝ) (w : m → ℝ) : m → ℝ :=
  b - A *ᵥ (weightedLeastSquaresOp (diagonal w) A *ᵥ b)

omit [DecidableEq n] [Fintype n] in
/-- Let $A \in \mathbb{R}^{m \times n}$ have linearly independent columns and let
$u \in \mathbb{R}^m$ have positive entries. Then the weighted Gram matrix
$A^T \operatorname{diag}(u) A$ is positive definite. -/
theorem posDef_conjTranspose_mul_diagonal_mul [Finite n] (hA : LinearIndependent ℝ Aᵀ)
    {u : m → ℝ} (hu : ∀ i, 0 < u i) : (Aᴴ * diagonal u * A).PosDef := by
  cases nonempty_fintype n
  exact (PosDef.diagonal hu).conjTranspose_mul_mul_same (mulVec_injective_iff.2 hA)

omit [Fintype m] in
/-- A change of one entry is the addition of a multiple of a standard basis vector:
$w[k \mapsto t] = w + (t - w_k) e_k$. -/
private theorem update_eq_add_single (w : m → ℝ) (k : m) (t : ℝ) :
    Function.update w k t = w + Pi.single k (t - w k) := by
  ext i
  by_cases hi : i = k
  · subst hi
    simp
  · simp [hi]

omit [Fintype n] [DecidableEq n] in
/-- A weight on one row gives a rank-one weighted Gram matrix: $A^T \operatorname{diag}(c e_k) A =
c\, a_k a_k^T$. -/
private theorem conjTranspose_mul_diagonal_single_mul (A : Matrix m n ℝ) (k : m) (c : ℝ) :
    Aᴴ * diagonal (Pi.single k c) * A = c • vecMulVec (A k) (A k) := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single k]
  · simp [mul_diagonal, vecMulVec_apply]
    ring
  · intro x _ hx
    simp [mul_diagonal, hx]
  · simp

omit [Fintype n] [DecidableEq n] in
/-- Let $A \in \mathbb{R}^{m \times n}$ have rows $a_1^T, \dots, a_m^T$, let $w \in \mathbb{R}^m$,
let $k$ be a row index and let $t \in \mathbb{R}$. A change of the $k$-th weight to $t$ is a
rank-one update of the weighted Gram matrix: $$A^T \operatorname{diag}(w[k \mapsto t]) A = A^T
\operatorname{diag}(w) A + (t - w_k)\, a_k a_k^T.$$

The deletion of row $k$ is the case $w = 1$, $t = 0$: $A^T D_k A = A^T A - a_k a_k^T$. The row
$a_k^T$ is `A k`. -/
theorem conjTranspose_mul_diagonal_update_mul (A : Matrix m n ℝ) (w : m → ℝ) (k : m) (t : ℝ) :
    Aᴴ * diagonal (Function.update w k t) * A =
      Aᴴ * diagonal w * A + (t - w k) • vecMulVec (A k) (A k) := by
  have hd : diagonal (w + Pi.single k (t - w k)) = diagonal w + diagonal (Pi.single k (t - w k)) :=
    (diagonal_add _ _).symm
  rw [update_eq_add_single, hd, Matrix.mul_add, Matrix.add_mul,
    conjTranspose_mul_diagonal_single_mul]

omit [Fintype n] [DecidableEq n] in
/-- Let $A \in \mathbb{R}^{m \times n}$ have rows $a_1^T, \dots, a_m^T$, let
$w, b \in \mathbb{R}^m$, let $k$ be a row index and let $t \in \mathbb{R}$. A change of the
$k$-th weight to $t$ changes the weighted right-hand side by a multiple of the $k$-th row: $$A^T
\operatorname{diag}(w[k \mapsto t])\, b = A^T \operatorname{diag}(w)\, b + (t - w_k)\, b_k\,
a_k.$$
-/
theorem conjTranspose_mul_diagonal_update_mulVec (A : Matrix m n ℝ) (w : m → ℝ) (k : m) (t : ℝ)
    (b : m → ℝ) : (Aᴴ * diagonal (Function.update w k t)) *ᵥ b
      = (Aᴴ * diagonal w) *ᵥ b + ((t - w k) * b k) • A k := by
  have hd : diagonal (w + Pi.single k (t - w k)) = diagonal w + diagonal (Pi.single k (t - w k)) :=
    (diagonal_add _ _).symm
  rw [update_eq_add_single, hd, Matrix.mul_add, add_mulVec]
  congr 1
  ext j
  rw [mulVec, dotProduct, Finset.sum_eq_single k]
  · simp [mul_diagonal]
    ring
  · intro x _ hx
    simp [mul_diagonal, hx]
  · simp

/-- The weighted solution is $(A^T \operatorname{diag}(u) A)^{-1} (A^T \operatorname{diag}(u) b)$.
-/
private theorem weightedLeastSquaresOp_diagonal_mulVec (A : Matrix m n ℝ) (u b : m → ℝ) :
    weightedLeastSquaresOp (diagonal u) A *ᵥ b
      = (Aᴴ * diagonal u * A)⁻¹ *ᵥ ((Aᴴ * diagonal u) *ᵥ b) := by
  simp only [weightedLeastSquaresOp, mulVec_mulVec, Matrix.mul_assoc]

/-- Let $A \in \mathbb{R}^{m \times n}$ have rows $a_1^T, \dots, a_m^T$, let
$w, b \in \mathbb{R}^m$, let $k$ be a row index and let $t \in \mathbb{R}$. Write $r(w)$ for
`Matrix.weightedResidual`. If the matrices $A^T \operatorname{diag}(w) A$ and
$A^T \operatorname{diag}(w[k \mapsto t]) A$ are both invertible, then the $k$-th residual
components satisfy $$r_k(w[k \mapsto t]) \left(1 + (t - w_k)\, a_k^T (A^T \operatorname{diag}(w)
A)^{-1} a_k\right) = r_k(w).$$

This is the Sherman–Morrison computation behind (6.1.4) of [golub2013matrix]. -/
theorem weightedResidual_update_mul {w : m → ℝ} {k : m} {t : ℝ}
    (hM : IsUnit (Aᴴ * diagonal w * A)) (hMt : IsUnit (Aᴴ * diagonal (Function.update w k t) * A))
    (b : m → ℝ) :
    weightedResidual A b (Function.update w k t) k *
        (1 + (t - w k) * (A k ⬝ᵥ ((Aᴴ * diagonal w * A)⁻¹ *ᵥ A k))) =
      weightedResidual A b w k := by
  have hdM : IsUnit (Aᴴ * diagonal w * A).det := (isUnit_iff_isUnit_det _).1 hM
  have hdMt : IsUnit (Aᴴ * diagonal (Function.update w k t) * A).det :=
    (isUnit_iff_isUnit_det _).1 hMt
  set y := weightedLeastSquaresOp (diagonal (Function.update w k t)) A *ᵥ b with hy_def
  set x := weightedLeastSquaresOp (diagonal w) A *ᵥ b with hx_def
  have hx : x = ((Aᴴ * diagonal w * A)⁻¹ * (Aᴴ * diagonal w)) *ᵥ b := by
    rw [hx_def, weightedLeastSquaresOp_diagonal_mulVec, mulVec_mulVec]
  have hy : (Aᴴ * diagonal (Function.update w k t) * A) *ᵥ y
      = (Aᴴ * diagonal (Function.update w k t)) *ᵥ b := by
    rw [hy_def, weightedLeastSquaresOp_diagonal_mulVec, mulVec_mulVec, mul_nonsing_inv _ hdMt,
      one_mulVec]
  rw [conjTranspose_mul_diagonal_update_mul, add_mulVec, smul_mulVec, vecMulVec_mulVec,
    op_smul_eq_smul, smul_smul, conjTranspose_mul_diagonal_update_mulVec] at hy
  have h3 := congrArg (fun v => A k ⬝ᵥ ((Aᴴ * diagonal w * A)⁻¹ *ᵥ v)) hy
  simp only [mulVec_add, mulVec_smul, mulVec_mulVec, nonsing_inv_mul _ hdM, one_mulVec,
    dotProduct_add, dotProduct_smul, smul_eq_mul, ← hx] at h3
  have hAy : (A *ᵥ y) k = A k ⬝ᵥ y := rfl
  have hAx : (A *ᵥ x) k = A k ⬝ᵥ x := rfl
  simp only [weightedResidual, Pi.sub_apply, ← hy_def, ← hx_def, hAy, hAx]
  linear_combination -h3

/-- Let $A \in \mathbb{R}^{m \times n}$ have linearly independent columns and rows
$a_1^T, \dots, a_m^T$, let $w \in \mathbb{R}^m$ have positive entries, let $b \in \mathbb{R}^m$,
and let $k$ be a row index. Write $W = \operatorname{diag}(w)$ and $r(w)$ for
`Matrix.weightedResidual`. Then the function $t \mapsto r_k(w[k \mapsto t])$ has at $t = w_k$
the derivative $$-\left(a_k^T (A^T W A)^{-1} a_k\right) r_k(w).$$ This is (6.1.4) of
[golub2013matrix].

The source differentiates in $\delta$, where the weight is $d_k^2 (1 + \delta)$, so its
derivative has the extra factor $d_k^2$ of the chain rule. The proof uses that near $w_k$,
$r_k(w[k \mapsto t]) = r_k(w) / (1 + (t - w_k)\, a_k^T (A^T W A)^{-1} a_k)$
(`Matrix.weightedResidual_update_mul`). -/
theorem hasDerivAt_weightedResidual (hA : LinearIndependent ℝ Aᵀ) {w : m → ℝ}
    (hw : ∀ i, 0 < w i) (b : m → ℝ) (k : m) :
    HasDerivAt (fun t => weightedResidual A b (Function.update w k t) k)
      (-(A k ⬝ᵥ ((Aᵀ * diagonal w * A)⁻¹ *ᵥ A k)) * weightedResidual A b w k) (w k) := by
  have hAT : Aᴴ = Aᵀ := conjTranspose_eq_transpose_of_trivial A
  set c := A k ⬝ᵥ ((Aᵀ * diagonal w * A)⁻¹ *ᵥ A k)
  set r := weightedResidual A b w k
  have hM : IsUnit (Aᴴ * diagonal w * A) := (posDef_conjTranspose_mul_diagonal_mul hA hw).isUnit
  have h1 : HasDerivAt (fun t : ℝ => 1 + (t - w k) * c) c (w k) := by
    have := (((hasDerivAt_id' (w k)).sub_const (w k)).mul_const c).const_add 1
    simpa using this
  have hf : HasDerivAt (fun t => r * (1 + (t - w k) * c)⁻¹) (-c * r) (w k) := by
    have h2 := (h1.inv (by simp)).const_mul r
    refine h2.congr_deriv ?_
    simp only [sub_self, zero_mul, add_zero, one_pow, div_one]
    ring
  refine hf.congr_of_eventuallyEq ?_
  have hev1 : ∀ᶠ t in nhds (w k), 0 < t := eventually_gt_nhds (hw k)
  have hev2 : ∀ᶠ t in nhds (w k), 1 + (t - w k) * c ≠ 0 :=
    h1.continuousAt.eventually_ne (by simp)
  filter_upwards [hev1, hev2] with t ht hne
  have hu : ∀ i, 0 < Function.update w k t i := fun i => by
    by_cases hi : i = k
    · rw [hi, Function.update_self]
      exact ht
    · rw [Function.update_of_ne hi]
      exact hw i
  have hMt := (posDef_conjTranspose_mul_diagonal_mul hA hu).isUnit
  have key := weightedResidual_update_mul hM hMt b
  rw [hAT] at key
  rw [eq_mul_inv_iff_mul_eq₀ hne]
  exact key

/-- Let $A \in \mathbb{R}^{m \times n}$ have linearly independent columns, let $w \in \mathbb{R}^m$
have positive entries, let $b \in \mathbb{R}^m$, and let $k$ be a row index. Then the function
$t \mapsto |r_k(w[k \mapsto t])|$ is antitone on $t > 0$, where $r$ is
`Matrix.weightedResidual`. So an increase of a weight never increases its residual component.
This is the statement of [golub2013matrix], §6.1.1, that "$|r_k(\delta)|$ is a monotone
decreasing function of $\delta$".

The source suggests a strict decrease. The decrease is not strict when $a_k = 0$ or $r_k = 0$,
because then $r_k$ is constant, so only the weak form is stated. The proof uses that the
derivative of $r_k^2$ is $-2 (a_k^T (A^T W A)^{-1} a_k) r_k^2 \le 0$
(`Matrix.hasDerivAt_weightedResidual`), where $(A^T W A)^{-1}$ is positive definite. -/
theorem antitoneOn_abs_weightedResidual (hA : LinearIndependent ℝ Aᵀ) {w : m → ℝ}
    (hw : ∀ i, 0 < w i) (b : m → ℝ) (k : m) :
    AntitoneOn (fun t => |weightedResidual A b (Function.update w k t) k|) (Set.Ioi 0) := by
  have hAT : Aᴴ = Aᵀ := conjTranspose_eq_transpose_of_trivial A
  set f : ℝ → ℝ := fun t => weightedResidual A b (Function.update w k t) k
  have hpos : ∀ t, 0 < t → ∀ i, 0 < Function.update w k t i := fun t ht i => by
    by_cases hi : i = k
    · rw [hi, Function.update_self]
      exact ht
    · rw [Function.update_of_ne hi]
      exact hw i
  have hderiv : ∀ t, 0 < t → HasDerivAt f
      (-(A k ⬝ᵥ ((Aᵀ * diagonal (Function.update w k t) * A)⁻¹ *ᵥ A k)) * f t) t := by
    intro t ht
    have h := hasDerivAt_weightedResidual hA (hpos t ht) b k
    simp only [Function.update_idem, Function.update_self] at h
    exact h
  have hc : ∀ t, 0 < t → 0 ≤ A k ⬝ᵥ ((Aᵀ * diagonal (Function.update w k t) * A)⁻¹ *ᵥ A k) := by
    intro t ht
    have hP := (posDef_conjTranspose_mul_diagonal_mul hA (hpos t ht)).inv.posSemidef
    rw [hAT] at hP
    simpa using hP.dotProduct_mulVec_nonneg (A k)
  have hsq : AntitoneOn (fun t => f t * f t) (Set.Ioi 0) := by
    have hd : ∀ t ∈ Set.Ioi (0 : ℝ), HasDerivAt (fun t => f t * f t)
        (-(A k ⬝ᵥ ((Aᵀ * diagonal (Function.update w k t) * A)⁻¹ *ᵥ A k)) * f t * f t +
          f t * (-(A k ⬝ᵥ ((Aᵀ * diagonal (Function.update w k t) * A)⁻¹ *ᵥ A k)) * f t)) t :=
      fun t ht => (hderiv t ht).mul (hderiv t ht)
    refine antitoneOn_of_deriv_nonpos (convex_Ioi 0)
      (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt)
      fun t ht => ?_
    rw [interior_Ioi] at ht
    rw [(hd t ht).deriv]
    nlinarith [mul_nonneg (hc t ht) (mul_self_nonneg (f t))]
  intro s hs t ht hst
  exact sq_le_sq.1 (by simpa only [sq] using hsq hs ht hst)

end RealWeights

/-! ### Generalized least squares -/

section Generalized

variable {l : Type*} [Fintype l] [DecidableEq l]

/-- The **generalized least-squares problem** of Paige ([golub2013matrix] (6.1.8)). Let
$A \in \mathbb{K}^{m \times n}$, $B \in \mathbb{K}^{m \times l}$ and $b \in \mathbb{K}^m$. A
pair $(x, v)$ with $x \in \mathbb{K}^n$ and $v \in \mathbb{K}^l$ **solves the generalized
least-squares problem** if $b = Ax + Bv$ and every pair $(x', v')$ with $b = Ax' + Bv'$ has
$\|v\| \le \|v'\|$.

The definition allows rank-deficient $A$ and $B$. For a nonsingular $B$ it is the weighted
problem with weight factor $B^{-1}$ (`Matrix.isGeneralizedLeastSquaresSolution_iff`). -/
structure IsGeneralizedLeastSquaresSolution (A : Matrix m n 𝕜) (B : Matrix m l 𝕜)
    (b : EuclideanSpace 𝕜 m) (x : EuclideanSpace 𝕜 n) (v : EuclideanSpace 𝕜 l) : Prop where
  /-- The constraint holds: $b = Ax + Bv$. -/
  eq_add : b = toEuclideanLin A x + toEuclideanLin B v
  /-- Every pair $(x', v')$ with $b = Ax' + Bv'$ has $\|v\| \le \|v'\|$. -/
  norm_le : ∀ x' v', b = toEuclideanLin A x' + toEuclideanLin B v' → ‖v‖ ≤ ‖v'‖

variable [DecidableEq m]

/-- Let $A \in \mathbb{K}^{m \times n}$, let $B \in \mathbb{K}^{m \times m}$ be invertible, and let
$b, v \in \mathbb{K}^m$ and $x \in \mathbb{K}^n$. Then $(x, v)$ solves the generalized
least-squares problem if and only if $x$ minimizes $\|B^{-1}(Ay - b)\|$ over all
$y \in \mathbb{K}^n$ and $v = B^{-1}(b - Ax)$. So for a nonsingular $B$ the problem (6.1.8) of
[golub2013matrix] is the weighted problem (6.1.7) (§6.1.2).

The constraint $b = Ax + Bv$ forces $v = B^{-1}(b - Ax)$, so the objective is
$\|B^{-1}(Ax - b)\|$. The weighted problem is `Matrix.IsLeastSquaresSolution (B⁻¹ * A)
(toEuclideanLin B⁻¹ b) x`. -/
theorem isGeneralizedLeastSquaresSolution_iff {A : Matrix m n 𝕜} {B : Matrix m m 𝕜}
    (hB : IsUnit B) {b : EuclideanSpace 𝕜 m} {x : EuclideanSpace 𝕜 n} {v : EuclideanSpace 𝕜 m} :
    IsGeneralizedLeastSquaresSolution A B b x v ↔
      IsLeastSquaresSolution (B⁻¹ * A) (toEuclideanLin B⁻¹ b) x ∧
        v = toEuclideanLin B⁻¹ (b - toEuclideanLin A x) := by
  have hfeas : ∀ x' v', b = toEuclideanLin A x' + toEuclideanLin B v' ↔
      v' = toEuclideanLin B⁻¹ (b - toEuclideanLin A x') := fun x' v' => by
    constructor
    · intro h
      rw [h, add_sub_cancel_left, toEuclideanLin_nonsing_inv_mul_apply hB]
    · intro h
      rw [h, toEuclideanLin_mul_nonsing_inv_apply hB, add_sub_cancel]
  have hnorm : ∀ x', ‖toEuclideanLin B⁻¹ (b - toEuclideanLin A x')‖ =
      ‖toEuclideanLin (B⁻¹ * A) x' - toEuclideanLin B⁻¹ b‖ := fun x' => by
    rw [map_sub, toEuclideanLin_mul_apply, norm_sub_rev]
  constructor
  · rintro ⟨hfe, hmin⟩
    have hv := (hfeas x v).1 hfe
    refine ⟨fun y => ?_, hv⟩
    rw [← hnorm, ← hnorm, ← hv]
    exact hmin y _ ((hfeas y _).2 rfl)
  · rintro ⟨hls, hv⟩
    refine ⟨(hfeas x v).2 hv, fun x' v' h' => ?_⟩
    rw [hv, (hfeas x' v').1 h', hnorm, hnorm]
    exact hls x'

end Generalized

/-! ### Paige's method -/

section Paige

variable {p q : ℕ}

/-- **Paige's method** for the generalized least-squares problem ([golub2013matrix]
(6.1.9)–(6.1.10)). Let $A \in \mathbb{K}^{(p+q) \times p}$ have a full QR factorization
$A = QR$, and split $Q = [Q_1\ Q_2]$ into its first $p$ and its last $q$ columns. Let $R_1$ be
the leading $p \times p$ block of $R$. Let $B, Z \in \mathbb{K}^{(p+q) \times (p+q)}$ with $Z$
unitary, split $Z = [Z_1\ Z_2]$ into its first $p$ and its last $q$ columns, and let
$S \in \mathbb{K}^{q \times q}$ be invertible with $$Q_2^H B Z_1 = 0, \qquad Q_2^H B Z_2 = S.$$
Let $b \in \mathbb{K}^{p+q}$, $u \in \mathbb{K}^q$ and $x \in \mathbb{K}^p$ satisfy $$S u =
Q_2^H b, \qquad R_1 x = Q_1^H b - Q_1^H B Z_2 u.$$ Then $(x, Z_2 u)$ solves the generalized
least-squares problem: it minimizes $\|v\|$ subject to $b = Ax + Bv$.

The source computes $Z$ from an RQ factorization, so that $S$ is upper triangular, and it
assumes that $B$ is nonsingular and that $A$ has full column rank, so that $S$ and $R_1$ are
nonsingular. The statement uses only what the proof needs. The proof checks the constraint on
the two blocks of $Q^H(Ax + Bv)$. For minimality, a feasible $(x', v')$ has
$S (Z_2^H v') = Q_2^H b$, so $Z_2^H v' = u$ and $\|v'\| \ge \|Z_2^H v'\| = \|u\| = \|Z_2 u\|$.

The QR factorization is `Matrix.IsQR A Q R`. The blocks are $Q_1$ = `Matrix.firstColumns Q`,
$Q_2$ = `Matrix.lastColumns Q`, $Z_1$ = `Matrix.firstColumns Z`, $Z_2$ = `Matrix.lastColumns Z`
and $R_1$ = `Matrix.firstRows R`. -/
theorem isGeneralizedLeastSquaresSolution_of_paige {A : Matrix (Fin (p + q)) (Fin p) 𝕜}
    {Q : Matrix (Fin (p + q)) (Fin (p + q)) 𝕜} {R : Matrix (Fin (p + q)) (Fin p) 𝕜}
    (hQR : IsQR A Q R) {B Z : Matrix (Fin (p + q)) (Fin (p + q)) 𝕜}
    (hZ : Z ∈ unitaryGroup (Fin (p + q)) 𝕜) {S : Matrix (Fin q) (Fin q) 𝕜} (hS : IsUnit S)
    (hZ₁ : (lastColumns Q (Nat.le_add_left q p))ᴴ * B * firstColumns Z (Nat.le_add_right p q) = 0)
    (hZ₂ : (lastColumns Q (Nat.le_add_left q p))ᴴ * B * lastColumns Z (Nat.le_add_left q p) = S)
    {b : EuclideanSpace 𝕜 (Fin (p + q))} {u : EuclideanSpace 𝕜 (Fin q)}
    {x : EuclideanSpace 𝕜 (Fin p)}
    (hu : toEuclideanLin S u = toEuclideanLin (lastColumns Q (Nat.le_add_left q p))ᴴ b)
    (hx : toEuclideanLin (firstRows R (Nat.le_add_right p q)) x =
      toEuclideanLin (firstColumns Q (Nat.le_add_right p q))ᴴ b -
        toEuclideanLin ((firstColumns Q (Nat.le_add_right p q))ᴴ * B *
          lastColumns Z (Nat.le_add_left q p)) u) :
    IsGeneralizedLeastSquaresSolution A B b x
      (toEuclideanLin (lastColumns Z (Nat.le_add_left q p)) u) := by
  have hp : p ≤ p + q := Nat.le_add_right p q
  have hq : q ≤ p + q := Nat.le_add_left q p
  have hQ := hQR.mem_unitaryGroup
  have hQQ : Qᴴ * Q = 1 := by
    rw [← star_eq_conjTranspose]; exact Unitary.star_mul_self_of_mem hQ
  set Q₁ := firstColumns Q hp with hQ₁
  set Q₂ := lastColumns Q hq with hQ₂
  set Z₁ := firstColumns Z hp with hZ₁def
  set Z₂ := lastColumns Z hq with hZ₂def
  set R₁ := firstRows R hp with hR₁
  have hA : A = Q₁ * R₁ := (hQR.firstColumns_mul_firstRows hp).symm
  have hQ₁Q₁ : Q₁ᴴ * Q₁ = 1 := hQR.conjTranspose_firstColumns_mul_self hp
  have hQ₂Q₁ : Q₂ᴴ * Q₁ = 0 := conjTranspose_lastColumns_mul_firstColumns hQQ hp hq le_rfl
  have hQ₁A : Q₁ᴴ * A = R₁ := by rw [hA, ← Matrix.mul_assoc, hQ₁Q₁, Matrix.one_mul]
  have hQ₂A : Q₂ᴴ * A = 0 := by rw [hA, ← Matrix.mul_assoc, hQ₂Q₁, Matrix.zero_mul]
  have hZ₂Z₂ : Z₂ᴴ * Z₂ = 1 := conjTranspose_lastColumns_mul_lastColumns
    (by rw [← star_eq_conjTranspose]; exact Unitary.star_mul_self_of_mem hZ) hq
  -- the resolutions of the identity by the column blocks
  have hsplit : ∀ {X : Matrix (Fin (p + q)) (Fin (p + q)) 𝕜}, X ∈ unitaryGroup (Fin (p + q)) 𝕜 →
      ∀ w, w = toEuclideanLin (firstColumns X hp) (toEuclideanLin (firstColumns X hp)ᴴ w)
        + toEuclideanLin (lastColumns X hq) (toEuclideanLin (lastColumns X hq)ᴴ w) := by
    intro X hX w
    rw [← toEuclideanLin_mul_apply, ← toEuclideanLin_mul_apply, ← LinearMap.add_apply, ← map_add,
      firstColumns_mul_conjTranspose_add_lastColumns_mul_conjTranspose hX hp hq rfl,
      toEuclideanLin_one_apply]
  refine ⟨?_, fun x' v' h' => ?_⟩
  · -- feasibility, block by block
    set y := toEuclideanLin A x + toEuclideanLin B (toEuclideanLin Z₂ u) with hy
    have e1 : toEuclideanLin Q₁ᴴ (toEuclideanLin B (toEuclideanLin Z₂ u)) =
        toEuclideanLin (Q₁ᴴ * B * Z₂) u := by
      rw [toEuclideanLin_mul_apply, toEuclideanLin_mul_apply]
    have e2 : toEuclideanLin Q₂ᴴ (toEuclideanLin B (toEuclideanLin Z₂ u)) =
        toEuclideanLin (Q₂ᴴ * B * Z₂) u := by
      rw [toEuclideanLin_mul_apply, toEuclideanLin_mul_apply]
    have h1 : toEuclideanLin Q₁ᴴ y = toEuclideanLin Q₁ᴴ b := by
      rw [hy, map_add, e1, ← toEuclideanLin_mul_apply Q₁ᴴ A x, hQ₁A, hx, sub_add_cancel]
    have h2 : toEuclideanLin Q₂ᴴ y = toEuclideanLin Q₂ᴴ b := by
      rw [hy, map_add, e2, hZ₂, hu, ← toEuclideanLin_mul_apply Q₂ᴴ A x, hQ₂A,
        toEuclideanLin_zero_apply, zero_add]
    calc b = toEuclideanLin Q₁ (toEuclideanLin Q₁ᴴ b) + toEuclideanLin Q₂ (toEuclideanLin Q₂ᴴ b) :=
          hsplit hQ b
      _ = toEuclideanLin Q₁ (toEuclideanLin Q₁ᴴ y) + toEuclideanLin Q₂ (toEuclideanLin Q₂ᴴ y) := by
          rw [h1, h2]
      _ = y := (hsplit hQ y).symm
  · -- minimality
    have e : toEuclideanLin Q₂ᴴ b = toEuclideanLin (Q₂ᴴ * B) v' := by
      rw [h', map_add, ← toEuclideanLin_mul_apply Q₂ᴴ A x', hQ₂A, toEuclideanLin_zero_apply,
        zero_add, toEuclideanLin_mul_apply]
    have e3 : toEuclideanLin (Q₂ᴴ * B) v' = toEuclideanLin S (toEuclideanLin Z₂ᴴ v') := by
      conv_lhs => rw [hsplit hZ v']
      rw [map_add, ← toEuclideanLin_mul_apply (Q₂ᴴ * B) Z₁,
        ← toEuclideanLin_mul_apply (Q₂ᴴ * B) Z₂, hZ₁, hZ₂, toEuclideanLin_zero_apply, zero_add]
    have hSv : toEuclideanLin S (toEuclideanLin Z₂ᴴ v') = toEuclideanLin S u := by
      rw [hu, e, e3]
    have hZv : toEuclideanLin Z₂ᴴ v' = u := by
      have := congrArg (toEuclideanLin S⁻¹) hSv
      rwa [toEuclideanLin_nonsing_inv_mul_apply hS, toEuclideanLin_nonsing_inv_mul_apply hS]
        at this
    have hnormv : ‖toEuclideanLin Z₂ u‖ = ‖u‖ :=
      (toEuclideanLinearIsometry hZ₂Z₂).norm_map u
    have hle : ‖toEuclideanLin Z₂ᴴ v'‖ ≤ ‖v'‖ := by
      have hZs : Zᴴ ∈ unitaryGroup (Fin (p + q)) 𝕜 := by
        rw [← star_eq_conjTranspose]
        exact Unitary.star_mem hZ
      rw [← norm_toEuclideanLin_apply_of_mem_unitaryGroup hZs v', hZ₂def,
        lastColumns_eq_submatrix_natAdd]
      refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
      rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fin.sum_univ_add]
      exact le_add_of_nonneg_left (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    rw [hnormv, ← hZv]
    exact hle

end Paige

/-! ### Column weighting -/

section ColumnWeighting

/-- **Column weighting** ([golub2013matrix], §6.1.3). Let $A \in \mathbb{K}^{m \times n}$, let
$G \in \mathbb{K}^{n \times n}$ be invertible, and let $b \in \mathbb{K}^m$ and
$y \in \mathbb{K}^n$. Then $y$ is a least-squares solution of $A G^{-1} y = b$ if and only if
$G^{-1} y$ is a least-squares solution of $Ax = b$.

The change of variables $x = G^{-1} y$ is a bijection. -/
theorem isLeastSquaresSolution_mul_inv_iff {A : Matrix m n 𝕜} {G : Matrix n n 𝕜} (hG : IsUnit G)
    {b : EuclideanSpace 𝕜 m} {y : EuclideanSpace 𝕜 n} :
    IsLeastSquaresSolution (A * G⁻¹) b y ↔ IsLeastSquaresSolution A b (toEuclideanLin G⁻¹ y) := by
  simp only [isLeastSquaresSolution_iff, toEuclideanLin_mul_apply]
  constructor
  · intro h x'
    have := h (toEuclideanLin G x')
    rwa [toEuclideanLin_nonsing_inv_mul_apply hG] at this
  · intro h y'
    exact h _

/-- Let $A \in \mathbb{K}^{m \times n}$, let $G \in \mathbb{K}^{n \times n}$ be invertible, and let
$b \in \mathbb{K}^m$. Write $\|z\|_G = \|Gz\|$. If $y$ is the least-squares solution of
$A G^{-1} y = b$ of least norm and $x$ is any least-squares solution of $Ax = b$, then $$\|y\|
\le \|Gx\|,$$ that is, $\|x_G\|_G \le \|x\|_G$ for $x_G = G^{-1} y$. This is the statement of
[golub2013matrix], §6.1.3, that "within the set of minimizers, $x_G$ has the smallest $G$-norm". -/
theorem IsMinNormLeastSquaresSolution.norm_le_of_mul_inv {A : Matrix m n 𝕜} {G : Matrix n n 𝕜}
    (hG : IsUnit G) {b : EuclideanSpace 𝕜 m} {y x : EuclideanSpace 𝕜 n}
    (hy : IsMinNormLeastSquaresSolution (A * G⁻¹) b y) (hx : IsLeastSquaresSolution A b x) :
    ‖y‖ ≤ ‖toEuclideanLin G x‖ :=
  hy.2 _ ((isLeastSquaresSolution_mul_inv_iff hG).2
    (by rwa [toEuclideanLin_nonsing_inv_mul_apply hG]))

end ColumnWeighting

end Matrix
