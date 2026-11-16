/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Numlib.Analysis.Matrix.Frobenius
import Numlib.Analysis.Matrix.ToEuclideanLin
import Numlib.Direct.Substitution
import Numlib.LinearAlgebra.Matrix.QR
import Numlib.LinearAlgebra.Matrix.SVD

/-!
# Least-squares solutions of linear systems

Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$, let $A \in \mathbb{K}^{m \times n}$ and
$b \in \mathbb{K}^m$. A vector $x \in \mathbb{K}^n$ is a **least-squares solution** of $Ax = b$ if
it minimizes the Euclidean norm $\|Ay - b\|$ of the residual over all $y \in \mathbb{K}^n$. It is
the **least-squares solution of least norm** if in addition $\|x\| \le \|y\|$ for every
least-squares solution $y$. This module proves that the least-squares solutions are the solutions of
the normal equations $A^H A x = A^H b$, and that the least-squares solution of least norm is
$A^+ b$, where $A^+$ is the Moore–Penrose pseudoinverse. If $A$ has full column rank, the
least-squares solution is unique and equals $(A^H A)^{-1} A^H b = \tilde R^{-1} \tilde Q^H b$ for
every reduced QR factorization $A = \tilde Q \tilde R$. The presentation follows
[quarteroni2000numerical], §3.4.3 and §3.13, and [golub2013matrix], §5.2, §5.3 and §5.5.

The module also proves facts about the geometry of the problem: the gradient of
$\frac{1}{2} \|Ax - b\|^2$ is $A^T (Ax - b)$, the set of least-squares solutions is convex, the
augmented matrix $\begin{bmatrix} I & A \\ A^H & 0 \end{bmatrix}$ is nonsingular exactly for full
column rank, and the trailing columns of a full QR factor span $\operatorname{ran}(A)^\perp$. It
solves the matrix problems $\min_X \|AX - I\|_F$ and $\min_F \|A - F K^H\|_F$. The modules
`Numlib.LinearAlgebra.Matrix.LeastSquares.Weighted` (row and column weights, the augmented system,
Paige's generalized least squares), `Numlib.LinearAlgebra.Matrix.LeastSquares.Regularized` (ridge
regression, general-form Tikhonov regularization, cross-validation),
`Numlib.LinearAlgebra.Matrix.LeastSquares.Constrained` (quadratic inequality and linear equality
constraints) and `Numlib.LinearAlgebra.Matrix.LeastSquares.Total` (total least squares) refine the
problem after [golub2013matrix], §6.1–6.3.

## Main definitions

* `Matrix.IsLeastSquaresSolution`: $x$ minimizes $\|Ay - b\|$ over all $y$, equation (3.73) of
  [quarteroni2000numerical].
* `Matrix.IsMinNormLeastSquaresSolution`: $x$ is a least-squares solution of least norm, equation
  (3.76) of [quarteroni2000numerical].

## Main results

* `Matrix.norm_toEuclideanLin_sub_sq_eq_of_normalEquations`: if $A^H A x = A^H b$, then
  $\|Ay - b\|^2 = \|Ax - b\|^2 + \|A(y - x)\|^2$ for every $y$.
* `Matrix.isLeastSquaresSolution_iff_normalEquations`: $x$ is a least-squares solution if and only
  if $A^H A x = A^H b$.
* `Matrix.posDef_conjTranspose_mul_self_of_linearIndependent`: for full column rank, $A^H A$ is
  positive definite.
* `Matrix.existsUnique_isLeastSquaresSolution`: for full column rank, the least-squares solution
  exists and is unique.
* `Matrix.pinv_eq_inv_conjTranspose_mul_self_mul_conjTranspose`: for full column rank,
  $A^+ = (A^H A)^{-1} A^H$.
* `Matrix.isLeastSquaresSolution_iff_eq_pinv_of_linearIndependent`: for full column rank, the
  least-squares solution is $A^+ b$.
* `Matrix.isLeastSquaresSolution_of_qr`: for a reduced QR factorization $A = \tilde Q \tilde R$ with
  nonsingular $\tilde R$, the vector $\tilde R^{-1} \tilde Q^H b$ is a least-squares solution.
* `Matrix.norm_sub_sq_eq_of_isQR_of_isLeastSquaresSolution`: for full column rank and a full QR
  factorization $A = QR$, the least squared residual is $\sum_{i = n+1}^{m} |(Q^H b)_i|^2$.
* `Matrix.isMinNormLeastSquaresSolution_pinv`: $A^+ b$ is a least-squares solution of least norm.
* `Matrix.IsMinNormLeastSquaresSolution.eq_pinv`: every least-squares solution of least norm equals
  $A^+ b$.
* `Matrix.pinv_eq_conjTranspose_mul_inv_self_mul_conjTranspose`: for full row rank,
  $A^+ = A^H (A A^H)^{-1}$.
* `Matrix.hasGradientAt_leastSquaresObjective`: over $\mathbb{R}$, the gradient of
  $\frac{1}{2} \|Ax - b\|^2$ is $A^T (Ax - b)$.
* `Matrix.convex_setOf_isLeastSquaresSolution`: the least-squares solutions form a convex set.
* `Matrix.isUnit_augmented_iff`: the augmented matrix
  $\begin{bmatrix} I & A \\ A^H & 0 \end{bmatrix}$ is nonsingular if and only if $A$ has full column
  rank.
* `Matrix.IsQR.range_orthogonal_eq_span_lastColumns`: for full column rank,
  $\operatorname{ran}(A)^\perp$ is spanned by the last $m - n$ columns of a full QR factor $Q$.
* `Matrix.isMinOn_norm_mul_sub_one_pinv`: $A^+$ minimizes $\|AX - I\|_F$, and it is the unique
  minimizer of least Frobenius norm.
* `Matrix.isMinOn_norm_sub_mul_conjTranspose_iff`: $F$ minimizes $\|A - G K^H\|_F$ over $G$ if and
  only if $F K^H K = A K$.
* `Matrix.pinv_eq_of_isThinQR_conjTranspose`: if $A^H = QR$ is a thin QR factorization with $R$
  nonsingular, then $A^+ = Q (R^H)^{-1}$.

## Implementation notes

* Vectors are elements of `EuclideanSpace 𝕜 m`, not functions `m → 𝕜`, because the statements are
  about the Euclidean norm. A matrix acts on them through `Matrix.toEuclideanLin`. The lemmas of
  `Numlib.Analysis.Matrix.ToEuclideanLin` move between the two forms.
* The pseudoinverse $A^+$ is `Matrix.pinv` of `Numlib.LinearAlgebra.Matrix.SVD`, so the results on
  it there apply directly.
* "Full column rank" is `LinearIndependent 𝕜 Aᵀ` (the columns of $A$ are linearly independent), and
  "full row rank" is `LinearIndependent 𝕜 A`.
* The index types are arbitrary finite types wherever the statement makes sense. The types `Fin M`
  and `Fin N` appear only with the full QR factorization `Matrix.IsQR` of
  `Numlib.LinearAlgebra.Matrix.QR`. Its reduced factors $\tilde Q$ and $\tilde R$ are the first $N$
  columns of $Q$ (`Matrix.firstColumns`) and the first $N$ rows of $R$ (`Matrix.firstRows`).
-/

open Finset
open scoped ComplexOrder

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-! ### Least-squares solutions and the normal equations -/

section NormalEquations

/-- Let $A \in \mathbb{K}^{m \times n}$ and $b \in \mathbb{K}^m$. A vector $x \in \mathbb{K}^n$ is a
**least-squares solution** of $Ax = b$ if
$$\|Ax - b\| \le \|Ay - b\| \quad \text{for all } y \in \mathbb{K}^n.$$
This is equation (3.73) of [quarteroni2000numerical].

The norms are the Euclidean norms of `EuclideanSpace`, and $A$ acts through
`Matrix.toEuclideanLin`. -/
def IsLeastSquaresSolution (A : Matrix m n 𝕜) (b : EuclideanSpace 𝕜 m) (x : EuclideanSpace 𝕜 n) :
    Prop :=
  ∀ y, ‖toEuclideanLin A x - b‖ ≤ ‖toEuclideanLin A y - b‖

variable {A : Matrix m n 𝕜} {b : EuclideanSpace 𝕜 m} {x : EuclideanSpace 𝕜 n}

/-- A vector $x$ is a least-squares solution of $Ax = b$ if and only if $\|Ax - b\| \le \|Ay - b\|$
for every $y$. This is the definition of `Matrix.IsLeastSquaresSolution`. -/
theorem isLeastSquaresSolution_iff :
    IsLeastSquaresSolution A b x ↔ ∀ y, ‖toEuclideanLin A x - b‖ ≤ ‖toEuclideanLin A y - b‖ :=
  Iff.rfl

variable [DecidableEq m]

/-- The **Pythagorean identity of least squares**. Let $A \in \mathbb{K}^{m \times n}$ and
$b \in \mathbb{K}^m$, and let $x \in \mathbb{K}^n$ solve the normal equations $A^H A x = A^H b$.
Then for every $y \in \mathbb{K}^n$,
$$\|Ay - b\|^2 = \|Ax - b\|^2 + \|A(y - x)\|^2.$$

The identity holds because the residual $Ax - b$ is orthogonal to the range of $A$. -/
theorem norm_toEuclideanLin_sub_sq_eq_of_normalEquations
    (hx : toEuclideanLin (Aᴴ * A) x = toEuclideanLin Aᴴ b) (y : EuclideanSpace 𝕜 n) :
    ‖toEuclideanLin A y - b‖ ^ 2 =
      ‖toEuclideanLin A x - b‖ ^ 2 + ‖toEuclideanLin A (y - x)‖ ^ 2 := by
  have hperp : (inner 𝕜 (toEuclideanLin A x - b) (toEuclideanLin A (y - x)) : 𝕜) = 0 := by
    rw [← toEuclideanLin_conjTranspose_inner_left, map_sub, ← toEuclideanLin_mul_apply, hx,
      sub_self, inner_zero_left]
  have hsplit : toEuclideanLin A y - b = (toEuclideanLin A x - b) + toEuclideanLin A (y - x) := by
    rw [map_sub]
    abel
  rw [hsplit, sq, norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hperp, sq, sq]

/-- Let $A \in \mathbb{K}^{m \times n}$ and $b \in \mathbb{K}^m$. The vector $A^+ b$ solves the
normal equations: $A^H A (A^+ b) = A^H b$. -/
theorem normalEquations_pinv (A : Matrix m n 𝕜) (b : EuclideanSpace 𝕜 m) :
    toEuclideanLin (Aᴴ * A) (toEuclideanLin A.pinv b) = toEuclideanLin Aᴴ b := by
  rw [← toEuclideanLin_mul_apply, Matrix.mul_assoc, conjTranspose_mul_mul_pinv]

/-- The **normal equations**. Let $A \in \mathbb{K}^{m \times n}$ and $b \in \mathbb{K}^m$. A vector
$x \in \mathbb{K}^n$ is a least-squares solution of $Ax = b$ if and only if
$$A^H A x = A^H b.$$
This is equation (3.74) of [quarteroni2000numerical].

The direction from the normal equations to the minimum is
`Matrix.norm_toEuclideanLin_sub_sq_eq_of_normalEquations`. For the other direction, the same
identity at the solution $A^+ b$ of the normal equations gives $\|A(x - A^+ b)\| = 0$, so
$Ax = A A^+ b$, and $x$ solves the normal equations too. -/
theorem isLeastSquaresSolution_iff_normalEquations :
    IsLeastSquaresSolution A b x ↔ toEuclideanLin (Aᴴ * A) x = toEuclideanLin Aᴴ b := by
  constructor
  · intro h
    have h1 := norm_toEuclideanLin_sub_sq_eq_of_normalEquations (normalEquations_pinv A b) x
    have h2 := pow_le_pow_left₀ (norm_nonneg _) (h (toEuclideanLin A.pinv b)) 2
    have h3 : ‖toEuclideanLin A (x - toEuclideanLin A.pinv b)‖ ^ 2 = 0 :=
      le_antisymm (by linarith) (sq_nonneg _)
    rw [pow_eq_zero_iff two_ne_zero, norm_eq_zero, map_sub, sub_eq_zero] at h3
    rw [toEuclideanLin_mul_apply, h3, ← toEuclideanLin_mul_apply, normalEquations_pinv]
  · intro hx y
    refine le_of_sq_le_sq ?_ (norm_nonneg _)
    rw [norm_toEuclideanLin_sub_sq_eq_of_normalEquations hx y]
    exact le_add_of_nonneg_right (sq_nonneg _)

/-- Let $A \in \mathbb{K}^{m \times n}$ and $b \in \mathbb{K}^m$. The vector $A^+ b$ is a
least-squares solution of $Ax = b$. -/
theorem isLeastSquaresSolution_pinv (A : Matrix m n 𝕜) (b : EuclideanSpace 𝕜 m) :
    IsLeastSquaresSolution A b (toEuclideanLin A.pinv b) :=
  isLeastSquaresSolution_iff_normalEquations.2 (normalEquations_pinv A b)

end NormalEquations

/-! ### Full column rank -/

section FullRank

variable {A : Matrix m n 𝕜}

omit [Fintype m] [DecidableEq n] in
/-- Let $A \in \mathbb{K}^{m \times n}$ have linearly independent columns. Then the map
$x \mapsto Ax$ is injective. -/
theorem mulVec_injective_of_linearIndependent_transpose (hA : LinearIndependent 𝕜 Aᵀ) :
    Function.Injective A.mulVec :=
  mulVec_injective_iff.2 hA

omit [Fintype n] [DecidableEq n] in
/-- Let $A \in \mathbb{K}^{m \times n}$ have linearly independent rows. Then the map
$y \mapsto y^T A$ on row vectors is injective. -/
theorem vecMul_injective_of_linearIndependent (hA : LinearIndependent 𝕜 A) :
    Function.Injective A.vecMul :=
  vecMul_injective_iff.2 hA

omit [Fintype n] [DecidableEq n] in
/-- Let $A \in \mathbb{K}^{m \times n}$ have linearly independent columns. Then the matrix $A^H A$
of the normal equations is positive definite. This is stated in §3.13 of
[quarteroni2000numerical]. -/
theorem posDef_conjTranspose_mul_self_of_linearIndependent [Finite n]
    (hA : LinearIndependent 𝕜 Aᵀ) : (Aᴴ * A).PosDef := by
  cases nonempty_fintype n
  exact PosDef.conjTranspose_mul_self A (mulVec_injective_of_linearIndependent_transpose hA)

omit [Fintype m] [DecidableEq n] in
/-- Let $A \in \mathbb{K}^{m \times n}$ have linearly independent rows. Then $A A^H$ is positive
definite. -/
theorem posDef_self_mul_conjTranspose_of_linearIndependent [Finite m]
    (hA : LinearIndependent 𝕜 A) : (A * Aᴴ).PosDef := by
  cases nonempty_fintype m
  exact PosDef.mul_conjTranspose_self A (vecMul_injective_of_linearIndependent hA)

/-- Let $A \in \mathbb{K}^{m \times n}$ have linearly independent columns, and let
$b \in \mathbb{K}^m$. Then $Ax = b$ has exactly one least-squares solution. This is stated in
§3.13 of [quarteroni2000numerical], after equation (3.74).

The solution is $(A^H A)^{-1} A^H b = A^+ b$, by
`Matrix.pinv_eq_inv_conjTranspose_mul_self_mul_conjTranspose` and
`Matrix.isLeastSquaresSolution_iff_eq_pinv_of_linearIndependent`. -/
theorem existsUnique_isLeastSquaresSolution (hA : LinearIndependent 𝕜 Aᵀ)
    (b : EuclideanSpace 𝕜 m) : ∃! x, IsLeastSquaresSolution A b x := by
  classical
  have hG : IsUnit (Aᴴ * A) := (posDef_conjTranspose_mul_self_of_linearIndependent hA).isUnit
  refine ⟨toEuclideanLin ((Aᴴ * A)⁻¹ * Aᴴ) b, ?_, fun x hx => ?_⟩
  · dsimp only
    rw [isLeastSquaresSolution_iff_normalEquations, ← toEuclideanLin_mul_apply,
      ← Matrix.mul_assoc, mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hG), Matrix.one_mul]
  · dsimp only at hx
    rw [isLeastSquaresSolution_iff_normalEquations] at hx
    rw [toEuclideanLin_mul_apply, ← hx, ← toEuclideanLin_mul_apply,
      nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hG), toEuclideanLin_one, LinearMap.id_apply]

/-- Let $A \in \mathbb{K}^{m \times n}$ have linearly independent columns. Then
$$A^+ = (A^H A)^{-1} A^H.$$

Both sides satisfy the four Penrose conditions, so `Matrix.pinv_unique` applies. -/
theorem pinv_eq_inv_conjTranspose_mul_self_mul_conjTranspose (hA : LinearIndependent 𝕜 Aᵀ) :
    A.pinv = (Aᴴ * A)⁻¹ * Aᴴ := by
  have hG : IsUnit (Aᴴ * A).det :=
    (isUnit_iff_isUnit_det _).1 (posDef_conjTranspose_mul_self_of_linearIndependent hA).isUnit
  have hleft : (Aᴴ * A)⁻¹ * Aᴴ * A = 1 := by
    rw [Matrix.mul_assoc, nonsing_inv_mul _ hG]
  have hH : ((Aᴴ * A)⁻¹).IsHermitian :=
    (isHermitian_conjTranspose_mul_self A).inv
  refine (pinv_unique A ?_ ?_ ?_ ?_).symm
  · rw [Matrix.mul_assoc, hleft, Matrix.mul_one]
  · rw [hleft, Matrix.one_mul]
  · rw [IsHermitian, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hH.eq,
      Matrix.mul_assoc]
  · rw [hleft]
    exact isHermitian_one

variable [DecidableEq m]

/-- Let $A \in \mathbb{K}^{m \times n}$ have linearly independent columns, and let
$b \in \mathbb{K}^m$. Then $x$ is a least-squares solution of $Ax = b$ if and only if
$x = A^+ b$. -/
theorem isLeastSquaresSolution_iff_eq_pinv_of_linearIndependent (hA : LinearIndependent 𝕜 Aᵀ)
    {b : EuclideanSpace 𝕜 m} {x : EuclideanSpace 𝕜 n} :
    IsLeastSquaresSolution A b x ↔ x = toEuclideanLin A.pinv b := by
  obtain ⟨x₀, hx₀, huniq⟩ := existsUnique_isLeastSquaresSolution hA b
  have hp := huniq _ (isLeastSquaresSolution_pinv A b)
  exact ⟨fun hx => (huniq x hx).trans hp.symm, fun hx => hx ▸ isLeastSquaresSolution_pinv A b⟩

end FullRank

/-! ### The least-squares solution of least norm -/

section MinNorm

variable {A : Matrix m n 𝕜} {b : EuclideanSpace 𝕜 m} {x : EuclideanSpace 𝕜 n}

/-- Let $A \in \mathbb{K}^{m \times n}$ and $b \in \mathbb{K}^m$. A vector $x \in \mathbb{K}^n$ is a
**least-squares solution of least norm** of $Ax = b$ if $x$ is a least-squares solution and
$\|x\| \le \|y\|$ for every least-squares solution $y$. This is equation (3.76) of
[quarteroni2000numerical]. -/
def IsMinNormLeastSquaresSolution (A : Matrix m n 𝕜) (b : EuclideanSpace 𝕜 m)
    (x : EuclideanSpace 𝕜 n) : Prop :=
  IsLeastSquaresSolution A b x ∧ ∀ y, IsLeastSquaresSolution A b y → ‖x‖ ≤ ‖y‖

variable [DecidableEq m]

/-- Let $A \in \mathbb{K}^{m \times n}$ and $b \in \mathbb{K}^m$. If $x$ solves the normal equations
$A^H A x = A^H b$, then $A(x - A^+ b) = 0$. That is, $x$ differs from $A^+ b$ by an element of
the kernel of $A$. -/
theorem toEuclideanLin_sub_pinv_eq_zero_of_normalEquations
    (hx : toEuclideanLin (Aᴴ * A) x = toEuclideanLin Aᴴ b) :
    toEuclideanLin A (x - toEuclideanLin A.pinv b) = 0 := by
  have hgram : toEuclideanLin (Aᴴ * A) (x - toEuclideanLin A.pinv b) = 0 := by
    rw [map_sub, hx, normalEquations_pinv, sub_self]
  have h := A.inner_toEuclideanLin_apply (x - toEuclideanLin A.pinv b)
    (x - toEuclideanLin A.pinv b)
  rw [hgram, inner_zero_right] at h
  exact inner_self_eq_zero.1 h

/-- Let $A \in \mathbb{K}^{m \times n}$ and $b \in \mathbb{K}^m$. If $Ad = 0$, then
$\langle A^+ b, d \rangle = 0$. That is, $A^+ b$ is orthogonal to the kernel of $A$.

The vector $A^+ b$ lies in the range of $A^+ = A^+ A A^+$. -/
theorem inner_pinv_eq_zero_of_toEuclideanLin_eq_zero (b : EuclideanSpace 𝕜 m)
    {d : EuclideanSpace 𝕜 n} (hd : toEuclideanLin A d = 0) :
    (inner 𝕜 (toEuclideanLin A.pinv b) d : 𝕜) = 0 := by
  have hpp : toEuclideanLin (A.pinv * A) (toEuclideanLin A.pinv b) = toEuclideanLin A.pinv b := by
    rw [← toEuclideanLin_mul_apply, pinv_mul_self_mul_pinv]
  rw [← hpp, inner_toEuclideanLin_of_isHermitian A.isHermitian_pinv_mul,
    toEuclideanLin_mul_apply, hd, map_zero, inner_zero_right]

/-- The **Pythagorean identity of the least-norm solution**. Let $A \in \mathbb{K}^{m \times n}$ and
$b \in \mathbb{K}^m$. If $x$ solves the normal equations $A^H A x = A^H b$, then
$$\|x\|^2 = \|A^+ b\|^2 + \|x - A^+ b\|^2.$$
-/
theorem norm_sq_eq_norm_pinv_sq_add_of_normalEquations
    (hx : toEuclideanLin (Aᴴ * A) x = toEuclideanLin Aᴴ b) :
    ‖x‖ ^ 2 = ‖toEuclideanLin A.pinv b‖ ^ 2 + ‖x - toEuclideanLin A.pinv b‖ ^ 2 := by
  have hxeq : toEuclideanLin A.pinv b + (x - toEuclideanLin A.pinv b) = x := by abel
  conv_lhs => rw [← hxeq]
  rw [sq, norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _
    (inner_pinv_eq_zero_of_toEuclideanLin_eq_zero b
      (toEuclideanLin_sub_pinv_eq_zero_of_normalEquations hx)), sq, sq]

/-- Let $A \in \mathbb{K}^{m \times n}$ and $b \in \mathbb{K}^m$. Then $A^+ b$ is a least-squares
solution of least norm of $Ax = b$. This is the existence part of Theorem 3.9 of
[quarteroni2000numerical]. -/
theorem isMinNormLeastSquaresSolution_pinv (A : Matrix m n 𝕜) (b : EuclideanSpace 𝕜 m) :
    IsMinNormLeastSquaresSolution A b (toEuclideanLin A.pinv b) :=
  ⟨isLeastSquaresSolution_pinv A b, fun _ hy =>
    norm_pinv_le_of_normalEquations A b (isLeastSquaresSolution_iff_normalEquations.1 hy)⟩

/-- Let $A \in \mathbb{K}^{m \times n}$ and $b \in \mathbb{K}^m$. If $x$ is a least-squares solution
of least norm of $Ax = b$, then $x = A^+ b$. This is the uniqueness part of Theorem 3.9 of
[quarteroni2000numerical].

Minimality against $A^+ b$ gives $\|x\| \le \|A^+ b\|$, and the identity
$\|x\|^2 = \|A^+ b\|^2 + \|x - A^+ b\|^2$ of
`Matrix.norm_sq_eq_norm_pinv_sq_add_of_normalEquations` then forces $x = A^+ b$. -/
theorem IsMinNormLeastSquaresSolution.eq_pinv (h : IsMinNormLeastSquaresSolution A b x) :
    x = toEuclideanLin A.pinv b := by
  have h1 := norm_sq_eq_norm_pinv_sq_add_of_normalEquations
    (isLeastSquaresSolution_iff_normalEquations.1 h.1)
  have h2 := pow_le_pow_left₀ (norm_nonneg _) (h.2 _ (isLeastSquaresSolution_pinv A b)) 2
  have h3 : ‖x - toEuclideanLin A.pinv b‖ ^ 2 = 0 := le_antisymm (by linarith) (sq_nonneg _)
  rw [pow_eq_zero_iff two_ne_zero, norm_eq_zero, sub_eq_zero] at h3
  exact h3

omit [DecidableEq m] in
/-- Two least-squares solutions of least norm of the same system $Ax = b$ are equal. -/
theorem IsMinNormLeastSquaresSolution.unique {y : EuclideanSpace 𝕜 n}
    (hx : IsMinNormLeastSquaresSolution A b x) (hy : IsMinNormLeastSquaresSolution A b y) :
    x = y := by
  classical
  rw [hx.eq_pinv, hy.eq_pinv]

/-- Let $A \in \mathbb{K}^{m \times n}$ have linearly independent rows. Then
$$A^+ = A^H (A A^H)^{-1}.$$
Hence the least-squares solution of least norm of $Ax = b$ is $A^H (A A^H)^{-1} b$, and by
`Matrix.toEuclideanLin_conjTranspose_mul_inv_self_mul_conjTranspose` it solves $Ax = b$. This is
the underdetermined case in the last paragraph of §3.13 of [quarteroni2000numerical].

Both sides satisfy the four Penrose conditions, so `Matrix.pinv_unique` applies. -/
theorem pinv_eq_conjTranspose_mul_inv_self_mul_conjTranspose (hA : LinearIndependent 𝕜 A) :
    A.pinv = Aᴴ * (A * Aᴴ)⁻¹ := by
  have hG : IsUnit (A * Aᴴ).det :=
    (isUnit_iff_isUnit_det _).1 (posDef_self_mul_conjTranspose_of_linearIndependent hA).isUnit
  have hright : A * (Aᴴ * (A * Aᴴ)⁻¹) = 1 := by
    rw [← Matrix.mul_assoc, mul_nonsing_inv _ hG]
  have hH : ((A * Aᴴ)⁻¹).IsHermitian := (isHermitian_mul_conjTranspose_self A).inv
  refine (pinv_unique A ?_ ?_ ?_ ?_).symm
  · rw [hright, Matrix.one_mul]
  · rw [Matrix.mul_assoc, hright, Matrix.mul_one]
  · rw [hright]
    exact isHermitian_one
  · rw [IsHermitian, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hH.eq,
      Matrix.mul_assoc]

/-- Let $A \in \mathbb{K}^{m \times n}$ have linearly independent rows. Then
$A \bigl(A^H (A A^H)^{-1} b\bigr) = b$ for every $b \in \mathbb{K}^m$. In particular, the system
$Ax = b$ is consistent. -/
theorem toEuclideanLin_conjTranspose_mul_inv_self_mul_conjTranspose (hA : LinearIndependent 𝕜 A)
    (b : EuclideanSpace 𝕜 m) :
    toEuclideanLin A (toEuclideanLin (Aᴴ * (A * Aᴴ)⁻¹) b) = b := by
  have hG : IsUnit (A * Aᴴ).det :=
    (isUnit_iff_isUnit_det _).1 (posDef_self_mul_conjTranspose_of_linearIndependent hA).isUnit
  rw [← toEuclideanLin_mul_apply, ← Matrix.mul_assoc, mul_nonsing_inv _ hG, toEuclideanLin_one,
    LinearMap.id_apply]

end MinNorm

/-! ### The QR route -/

section QRSolve

variable {o : Type*} [Fintype o] [LinearOrder o] [DecidableEq m]

/-- Let $A, \tilde Q \in \mathbb{K}^{m \times n}$ and $\tilde R \in \mathbb{K}^{n \times n}$ with
$A = \tilde Q \tilde R$, $\tilde Q^H \tilde Q = I$, and $\tilde R$ upper triangular with nonzero
diagonal entries. Then for every $b \in \mathbb{K}^m$, the vector
$$x = \tilde R^{-1} \tilde Q^H b$$
is a least-squares solution of $Ax = b$. This is Theorem 3.8 of [quarteroni2000numerical],
equation (3.75).

The column index type is any finite linearly ordered type. The reduced factorization of
`Matrix.exists_isThinQR` satisfies the hypotheses. The vector $x$ solves the normal equations:
$A^H A x = \tilde R^H \tilde Q^H \tilde Q \tilde R \tilde R^{-1} \tilde Q^H b = \tilde R^H
\tilde Q^H b = A^H b$. -/
theorem isLeastSquaresSolution_of_qr {A Q : Matrix m o 𝕜} {R : Matrix o o 𝕜} (hA : A = Q * R)
    (hQ : Qᴴ * Q = 1) (hR : R.IsUpperTriangular) (hd : ∀ i, R i i ≠ 0) (b : EuclideanSpace 𝕜 m) :
    IsLeastSquaresSolution A b (toEuclideanLin (R⁻¹ * Qᴴ) b) := by
  have hRd : IsUnit R.det :=
    (isUnit_iff_isUnit_det R).1 (hR.isUnit_iff.2 hd)
  rw [isLeastSquaresSolution_iff_normalEquations, ← toEuclideanLin_mul_apply]
  have : Aᴴ * A * (R⁻¹ * Qᴴ) = Aᴴ := by
    rw [hA, conjTranspose_mul]
    calc Rᴴ * Qᴴ * (Q * R) * (R⁻¹ * Qᴴ) = Rᴴ * (Qᴴ * Q) * (R * R⁻¹) * Qᴴ := by
          simp only [Matrix.mul_assoc]
      _ = Rᴴ * Qᴴ := by rw [hQ, mul_nonsing_inv _ hRd, Matrix.mul_one, Matrix.mul_one]
  rw [this]

end QRSolve

/-! ### Least squares through a full QR factorization -/

section FullQR

variable {M N : ℕ} {A : Matrix (Fin M) (Fin N) 𝕜} {Q : Matrix (Fin M) (Fin M) 𝕜}
variable {R : Matrix (Fin M) (Fin N) 𝕜}

/-- Let $A \in \mathbb{K}^{M \times N}$ with $N \le M$ have linearly independent columns, and let
$A = QR$ be a full QR factorization. Let $\tilde Q$ be the first $N$ columns of $Q$, and let
$\tilde R$ be the first $N$ rows of $R$. Then for every $b \in \mathbb{K}^M$, the vector
$\tilde R^{-1} \tilde Q^H b$ is a least-squares solution of $Ax = b$. This is Theorem 3.8 of
[quarteroni2000numerical].

The full QR factorization is `Matrix.IsQR`: $Q$ is unitary and $R$ is upper trapezoidal. The
reduced factors are `Matrix.firstColumns Q hNM` and `Matrix.firstRows R hNM`. -/
theorem IsQR.isLeastSquaresSolution (h : IsQR A Q R) (hNM : N ≤ M) (hA : LinearIndependent 𝕜 Aᵀ)
    (b : EuclideanSpace 𝕜 (Fin M)) :
    IsLeastSquaresSolution A b
      (toEuclideanLin ((firstRows R hNM)⁻¹ * (firstColumns Q hNM)ᴴ) b) :=
  isLeastSquaresSolution_of_qr (h.firstColumns_mul_firstRows hNM).symm
    (h.conjTranspose_firstColumns_mul_self hNM) (h.isUpperTriangular_firstRows hNM)
    (h.firstRows_diag_ne_zero_of_linearIndependent hNM hA) b

/-- Let $A = QR$ be a full QR factorization of $A \in \mathbb{K}^{M \times N}$. Then for every
$b \in \mathbb{K}^M$ and $x \in \mathbb{K}^N$,
$$\|Ax - b\| = \|Rx - Q^H b\|.$$
-/
theorem IsQR.norm_sub_eq (h : IsQR A Q R) (b : EuclideanSpace 𝕜 (Fin M))
    (x : EuclideanSpace 𝕜 (Fin N)) :
    ‖toEuclideanLin A x - b‖ = ‖toEuclideanLin R x - toEuclideanLin Qᴴ b‖ := by
  have hQ : Q * Qᴴ = 1 := Unitary.mul_star_self_of_mem h.mem_unitaryGroup
  have : toEuclideanLin A x - b = toEuclideanLin Q (toEuclideanLin R x - toEuclideanLin Qᴴ b) := by
    rw [map_sub, ← toEuclideanLin_mul_apply, ← toEuclideanLin_mul_apply, h.mul_eq, hQ,
      toEuclideanLin_one, LinearMap.id_apply]
  rw [this]
  exact norm_toEuclideanCLM_apply_of_mem_unitaryGroup h.mem_unitaryGroup _

/-- Let $A = QR$ be a full QR factorization of $A \in \mathbb{K}^{M \times N}$ with $N \le M$, and
let $\tilde Q$ and $\tilde R$ be the first $N$ columns of $Q$ and the first $N$ rows of $R$.
Then for every $b \in \mathbb{K}^M$ and $x \in \mathbb{K}^N$,
$$\|Ax - b\|^2 = \|\tilde R x - \tilde Q^H b\|^2 + \sum_{i = N+1}^{M} |(Q^H b)_i|^2.$$
This is the identity in the proof of Theorem 3.8 of [quarteroni2000numerical].

Lean indices start at $0$, so the sum is over the `i : Fin M` with `N ≤ i`. -/
theorem norm_sub_sq_eq_of_isQR (h : IsQR A Q R) (hNM : N ≤ M) (b : EuclideanSpace 𝕜 (Fin M))
    (x : EuclideanSpace 𝕜 (Fin N)) :
    ‖toEuclideanLin A x - b‖ ^ 2 =
      ‖toEuclideanLin (firstRows R hNM) x - toEuclideanLin (firstColumns Q hNM)ᴴ b‖ ^ 2 +
        ∑ i ∈ univ.filter (fun i : Fin M => N ≤ i), ‖(toEuclideanLin Qᴴ b) i‖ ^ 2 := by
  rw [h.norm_sub_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
    ← Finset.sum_filter_add_sum_filter_not univ (fun i : Fin M => N ≤ i)
      (fun i => ‖(toEuclideanLin R x - toEuclideanLin Qᴴ b) i‖ ^ 2), add_comm]
  congr 1
  · -- the leading rows, reindexed by `Fin.castLE`
    symm
    refine Finset.sum_bij (fun (j : Fin N) _ => Fin.castLE hNM j) (fun j _ => ?_)
      (fun _ _ _ _ hk => Fin.castLE_injective hNM hk) (fun i hi => ?_) fun j _ => rfl
    · simp only [mem_filter, mem_univ, true_and, not_le, Fin.val_castLE]
      exact j.2
    · simp only [mem_filter, mem_univ, true_and, not_le] at hi
      exact ⟨⟨i, hi⟩, mem_univ _, Fin.ext rfl⟩
  · -- the trailing rows: `(R x) i = 0` for `N ≤ i`
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := (mem_filter.1 hi).2
    have hRx : (toEuclideanLin R x) i = 0 := by
      change (R *ᵥ WithLp.ofLp x) i = 0
      rw [mulVec, dotProduct]
      exact Finset.sum_eq_zero fun j _ => by rw [h.apply_eq_zero_of_le hi', zero_mul]
    rw [PiLp.sub_apply, hRx, zero_sub, norm_neg]

/-- Let $A \in \mathbb{K}^{M \times N}$ with $N \le M$ have linearly independent columns, and let
$A = QR$ be a full QR factorization. If $x$ is a least-squares solution of $Ax = b$, then
$$\|Ax - b\|^2 = \sum_{i = N+1}^{M} |(Q^H b)_i|^2.$$
This is the value of the minimum in Theorem 3.8 of [quarteroni2000numerical].

At the solution, $\tilde R x = \tilde Q^H b$, so the first term of
`Matrix.norm_sub_sq_eq_of_isQR` vanishes. Lean indices start at $0$, so the sum is over the
`i : Fin M` with `N ≤ i`. -/
theorem norm_sub_sq_eq_of_isQR_of_isLeastSquaresSolution (h : IsQR A Q R) (hNM : N ≤ M)
    (hA : LinearIndependent 𝕜 Aᵀ) {b : EuclideanSpace 𝕜 (Fin M)} {x : EuclideanSpace 𝕜 (Fin N)}
    (hx : IsLeastSquaresSolution A b x) :
    ‖toEuclideanLin A x - b‖ ^ 2 =
      ∑ i ∈ univ.filter (fun i : Fin M => N ≤ i), ‖(toEuclideanLin Qᴴ b) i‖ ^ 2 := by
  rw [norm_sub_sq_eq_of_isQR h hNM]
  have hxs : x = toEuclideanLin ((firstRows R hNM)⁻¹ * (firstColumns Q hNM)ᴴ) b := by
    obtain ⟨x₀, -, huniq⟩ := existsUnique_isLeastSquaresSolution hA b
    exact (huniq x hx).trans (huniq _ (h.isLeastSquaresSolution hNM hA b)).symm
  have hR : IsUnit (firstRows R hNM).det :=
    (isUnit_iff_isUnit_det _).1 (h.isUnit_firstRows_of_linearIndependent hNM hA)
  rw [hxs, ← toEuclideanLin_mul_apply, ← Matrix.mul_assoc, mul_nonsing_inv _ hR, Matrix.one_mul,
    sub_self, norm_zero, zero_pow two_ne_zero, zero_add]

end FullQR

/-! ### More on the set of least-squares solutions -/

section Solutions

variable {A : Matrix m n 𝕜} {b : EuclideanSpace 𝕜 m} {x : EuclideanSpace 𝕜 n}

/-- Let $A \in \mathbb{K}^{m \times n}$ and $b \in \mathbb{K}^m$. If $x$ and $y$ are least-squares
solutions of $Ax = b$, then $A(y - x) = 0$. This is stated in §5.3.1 of [golub2013matrix].

Both solutions differ from $A^+ b$ by an element of the kernel of $A$
(`Matrix.toEuclideanLin_sub_pinv_eq_zero_of_normalEquations`). -/
theorem IsLeastSquaresSolution.toEuclideanLin_sub_eq_zero {y : EuclideanSpace 𝕜 n}
    (hx : IsLeastSquaresSolution A b x) (hy : IsLeastSquaresSolution A b y) :
    toEuclideanLin A (y - x) = 0 := by
  classical
  have h1 := toEuclideanLin_sub_pinv_eq_zero_of_normalEquations
    (isLeastSquaresSolution_iff_normalEquations.1 hx)
  have h2 := toEuclideanLin_sub_pinv_eq_zero_of_normalEquations
    (isLeastSquaresSolution_iff_normalEquations.1 hy)
  rw [map_sub] at h1 h2 ⊢
  rw [sub_eq_zero] at h1 h2
  rw [h1, h2, sub_self]

/-- Let $A \in \mathbb{K}^{m \times n}$ and $b \in \mathbb{K}^m$. The set of least-squares solutions
of $Ax = b$ is convex. This is stated in §5.5.1 of [golub2013matrix].

Convexity is over $\mathbb{R}$. The set is the affine subspace of solutions of the normal
equations. -/
theorem convex_setOf_isLeastSquaresSolution (A : Matrix m n 𝕜) (b : EuclideanSpace 𝕜 m) :
    Convex ℝ {x | IsLeastSquaresSolution A b x} := by
  classical
  intro x hx y hy a c ha hc hac
  simp only [Set.mem_ofPred_eq, isLeastSquaresSolution_iff_normalEquations] at hx hy ⊢
  rw [map_add, LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower, hx, hy, ← add_smul,
    hac, one_smul]

open scoped ComplexOrder in
/-- Let $A \in \mathbb{K}^{m \times n}$. The augmented matrix
$$\begin{bmatrix} I & A \\ A^H & 0 \end{bmatrix}$$
is nonsingular if and only if the columns of $A$ are linearly independent. This matrix is the
matrix of the augmented system (5.3.20) of [golub2013matrix].

The matrix is `Matrix.fromBlocks 1 A Aᴴ 0`, indexed by `m ⊕ n`. Its determinant is
$(-1)^n \det(A^H A)$, and $A^H A$ is nonsingular if and only if the columns of $A$ are linearly
independent. -/
theorem isUnit_augmented_iff [DecidableEq m] (A : Matrix m n 𝕜) :
    IsUnit (fromBlocks 1 A Aᴴ 0) ↔ LinearIndependent 𝕜 Aᵀ := by
  rw [isUnit_iff_isUnit_det, det_fromBlocks_one₁₁, zero_sub, det_neg, IsUnit.mul_iff,
    ← isUnit_iff_isUnit_det]
  simp only [((isUnit_one.neg).pow _ : IsUnit ((-1 : 𝕜) ^ Fintype.card n)), true_and]
  constructor
  · intro h
    have hinj : Function.Injective A.mulVec := fun x y hxy => by
      have : (Aᴴ * A) *ᵥ x = (Aᴴ * A) *ᵥ y := by rw [← mulVec_mulVec, hxy, mulVec_mulVec]
      exact (mulVec_injective_iff_isUnit (A := Aᴴ * A)).2 h this
    exact mulVec_injective_iff.1 hinj
  · intro h
    exact (posDef_conjTranspose_mul_self_of_linearIndependent h).isUnit

/-- Let $V \in \mathbb{K}^{m \times k}$ have orthonormal columns, $V^H V = I$. Then $V V^H$ is the
orthogonal projection onto the range of $V$. This is stated in §2.5.1 of [golub2013matrix].

This is the case $V^+ = V^H$ of `Matrix.mul_pinv_eq_starProjection`. The projection is
`Submodule.starProjection`. -/
theorem toEuclideanLin_mul_conjTranspose_eq_starProjection {k : Type*} [Fintype k]
    [DecidableEq k] [DecidableEq m] {V : Matrix m k 𝕜} (hV : Vᴴ * V = 1) :
    toEuclideanLin (V * Vᴴ) = ((LinearMap.range (toEuclideanLin V)).starProjection :
      EuclideanSpace 𝕜 m →ₗ[𝕜] EuclideanSpace 𝕜 m) := by
  have hp : V.pinv = Vᴴ := by
    rw [pinv_eq_inv_conjTranspose_mul_self_mul_conjTranspose_of_isUnit
      (by rw [hV]; exact isUnit_one), hV, inv_one, Matrix.one_mul]
  rw [← hp, mul_pinv_eq_starProjection]

omit [Fintype m] in
/-- Let $A \in \mathbb{K}^{m \times n}$. The range of $A$, as a map from $\mathbb{K}^n$ to
$\mathbb{K}^m$, has dimension $\operatorname{rank} A$. -/
theorem finrank_range_toEuclideanLin [Finite m] (A : Matrix m n 𝕜) :
    Module.finrank 𝕜 (LinearMap.range (toEuclideanLin A)) = A.rank := by
  classical
  cases nonempty_fintype m
  rw [rank_eq_finrank_range_toLin A (EuclideanSpace.basisFun m 𝕜).toBasis
      (EuclideanSpace.basisFun n 𝕜).toBasis, ← toEuclideanLin_eq_toLin_orthonormal]

end Solutions

section Gradient

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n] [DecidableEq m]

/-- Let $A \in \mathbb{R}^{m \times n}$ and $b \in \mathbb{R}^m$. At every $x \in \mathbb{R}^n$, the
function $f(y) = \frac{1}{2} \|Ay - b\|^2$ has the gradient
$$\nabla f(x) = A^T (Ax - b).$$
Hence the normal equations say that the gradient vanishes. This is stated in §5.3.1 of
[golub2013matrix]. -/
theorem hasGradientAt_leastSquaresObjective (A : Matrix m n ℝ) (b : EuclideanSpace ℝ m)
    (x : EuclideanSpace ℝ n) :
    HasGradientAt (fun y => ‖toEuclideanLin A y - b‖ ^ 2 / 2)
      (toEuclideanLin Aᵀ (toEuclideanLin A x - b)) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  set L := LinearMap.toContinuousLinearMap (toEuclideanLin A) with hL
  have hf : HasFDerivAt (fun y => toEuclideanLin A y - b) L x := L.hasFDerivAt.sub_const b
  have h1 : HasFDerivAt (fun y => ‖toEuclideanLin A y - b‖ ^ 2)
      (2 • (innerSL ℝ (toEuclideanLin A x - b)).comp L) x := hf.norm_sq
  have h2 := h1.mul_const (1 / 2 : ℝ)
  have hfun : (fun y => ‖toEuclideanLin A y - b‖ ^ 2 / 2)
      = fun y => ‖toEuclideanLin A y - b‖ ^ 2 * (1 / 2 : ℝ) := by
    funext y; ring
  rw [hfun]
  convert h2 using 1
  ext v
  have := toEuclideanLin_conjTranspose_inner_left A v (toEuclideanLin A x - b)
  rw [conjTranspose_eq_transpose_of_trivial] at this
  rw [InnerProductSpace.toDual_apply_apply, this]
  simp only [_root_.smul_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
    hL, LinearMap.coe_toContinuousLinearMap', smul_eq_mul, nsmul_eq_mul]
  rw [real_inner_comm]
  ring

end Gradient

/-! ### The orthogonal complement of the range through a QR factorization -/

section RangeComplement

variable {M N : ℕ} {A : Matrix (Fin M) (Fin N) 𝕜} {Q : Matrix (Fin M) (Fin M) 𝕜}
  {R : Matrix (Fin M) (Fin N) 𝕜}

/-- Let $A \in \mathbb{K}^{M \times N}$ with $N \le M$ have linearly independent columns, and let
$A = QR$ be a full QR factorization with columns $q_1, \dots, q_M$ of $Q$. Then the orthogonal
complement of the range of $A$ is spanned by the last $M - N$ columns of $Q$:
$$\operatorname{ran}(A)^\perp = \operatorname{span}\{q_{N+1}, \dots, q_M\}.$$
This follows Theorem 5.2.2 of [golub2013matrix].

The last columns are `Matrix.lastColumns Q`. They are orthogonal to the range, since
$A^H q_i = R^H e_i = 0$ for $i > N$, and they are $M - N$ orthonormal vectors in a complement of
dimension $M - N$. -/
theorem IsQR.range_orthogonal_eq_span_lastColumns (h : IsQR A Q R) (hNM : N ≤ M)
    (hA : LinearIndependent 𝕜 Aᵀ) :
    (LinearMap.range (toEuclideanLin A))ᗮ
      = Submodule.span 𝕜 (Set.range fun j : Fin (M - N) =>
          (WithLp.toLp 2 ((lastColumns Q (Nat.sub_le M N))ᵀ j) : EuclideanSpace 𝕜 (Fin M))) := by
  have hQ : Qᴴ * Q = 1 := by
    rw [← star_eq_conjTranspose]; exact mem_unitaryGroup_iff'.1 h.mem_unitaryGroup
  have hq := orthonormal_toLp_transpose_of_conjTranspose_mul_self_eq_one hQ
  set e : Fin (M - N) → Fin M := fun j => ⟨M - (M - N) + j, by omega⟩ with he
  have he_inj : Function.Injective e := fun a b hab => by
    have := congrArg Fin.val hab
    simp only [he] at this
    exact Fin.ext (by omega)
  set T := Submodule.span 𝕜 (Set.range fun j : Fin (M - N) =>
    (WithLp.toLp 2 ((lastColumns Q (Nat.sub_le M N))ᵀ j) : EuclideanSpace 𝕜 (Fin M))) with hT
  have hle : T ≤ (LinearMap.range (toEuclideanLin A))ᗮ := by
    rw [hT, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_orthogonal]
    rintro _ ⟨x, rfl⟩
    have hzero : toEuclideanLin Aᴴ (WithLp.toLp 2 (Qᵀ (e j))) = 0 := by
      rw [← h.mul_eq, conjTranspose_mul, toEuclideanLin_mul_apply]
      have hsingle : toEuclideanLin Qᴴ (WithLp.toLp 2 (Qᵀ (e j)))
          = WithLp.toLp 2 (Pi.single (e j) 1) := by
        rw [toEuclideanLin_toLp]
        congr 1
        have : Qᵀ (e j) = Q *ᵥ Pi.single (e j) 1 := by
          rw [mulVec_single_one]; rfl
        rw [this, mulVec_mulVec, hQ, one_mulVec]
      rw [hsingle, toEuclideanLin_toLp]
      ext l
      have hR := h.apply_eq_zero_of_le (show N ≤ (e j : ℕ) by simp only [he]; omega) l
      simp [hR]
    change inner 𝕜 (toEuclideanLin A x) (WithLp.toLp 2 (Qᵀ (e j)) : EuclideanSpace 𝕜 (Fin M)) = 0
    rw [← inner_conj_symm, ← toEuclideanLin_conjTranspose_inner_left, hzero, inner_zero_left,
      map_zero]
  have hrank : A.rank = N := by
    rw [rank_eq_finrank_span_cols]
    exact (finrank_span_eq_card hA).trans (Fintype.card_fin N)
  have h1 : Module.finrank 𝕜 (LinearMap.range (toEuclideanLin A))ᗮ = M - N := by
    have := (LinearMap.range (toEuclideanLin A)).finrank_add_finrank_orthogonal
    rw [finrank_range_toEuclideanLin, hrank, finrank_euclideanSpace_fin] at this
    omega
  have h2 : Module.finrank 𝕜 T = M - N := by
    rw [hT, show (fun j : Fin (M - N) => (WithLp.toLp 2 ((lastColumns Q (Nat.sub_le M N))ᵀ j) :
        EuclideanSpace 𝕜 (Fin M)))
        = (fun i => (WithLp.toLp 2 (Qᵀ i) : EuclideanSpace 𝕜 (Fin M))) ∘ e from rfl,
      finrank_span_eq_card (hq.comp _ he_inj).linearIndependent, Fintype.card_fin]
  exact (Submodule.eq_of_le_of_finrank_eq hle (h2.trans h1.symm)).symm

end RangeComplement

/-! ### Matrix least-squares problems -/

section Frobenius

open scoped Matrix.Norms.Frobenius

variable {p q : Type*} [Fintype p] [Fintype q]

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- Let $A \in \mathbb{K}^{m \times n}$, and let the norm be the Frobenius norm. The pseudoinverse
minimizes $X \mapsto \|AX - I\|_F$ over $X \in \mathbb{K}^{n \times m}$, and it is the unique
minimizer of least norm: $\|A A^+ - I\|_F \le \|AX - I\|_F$ for every $X$, and every $X$ with
$\|AX - I\|_F = \|A A^+ - I\|_F$ satisfies $\|A^+\|_F \le \|X\|_F$, with equality only for
$X = A^+$. This is the problem (5.5.3) of [golub2013matrix].

Column $j$ of $X$ is a least-squares problem with the right-hand side $e_j$, and its
least-squares solution of least norm is $A^+ e_j$. -/
theorem isMinOn_norm_mul_sub_one_pinv (A : Matrix m n 𝕜) :
    IsMinOn (fun X : Matrix n m 𝕜 => ‖A * X - 1‖) Set.univ A.pinv ∧
      ∀ X : Matrix n m 𝕜, ‖A * X - 1‖ = ‖A * A.pinv - 1‖ →
        ‖A.pinv‖ ≤ ‖X‖ ∧ (‖X‖ = ‖A.pinv‖ → X = A.pinv) := by
  set e : m → EuclideanSpace 𝕜 m := fun j => EuclideanSpace.single j 1 with he
  have hcol : ∀ (X : Matrix n m 𝕜) j,
      (WithLp.toLp 2 fun i => (A * X - 1 : Matrix m m 𝕜) i j : EuclideanSpace 𝕜 m)
        = toEuclideanLin A (WithLp.toLp 2 fun i => X i j) - e j := by
    intro X j
    ext i
    simp [he, mulVec, dotProduct, Matrix.mul_apply, Matrix.one_apply, eq_comm]
  have hpinv : ∀ j, (WithLp.toLp 2 fun i => A.pinv i j : EuclideanSpace 𝕜 n)
      = toEuclideanLin A.pinv (e j) := by
    intro j
    ext i
    simp [he, mulVec, dotProduct, Pi.single_apply]
  have hsq : ∀ X : Matrix n m 𝕜, ‖A * X - 1‖ ^ 2
      = ∑ j, ‖toEuclideanLin A (WithLp.toLp 2 fun i => X i j) - e j‖ ^ 2 := fun X => by
    rw [frobenius_norm_sq_eq_sum_norm_sq_col]
    exact Finset.sum_congr rfl fun j _ => by rw [hcol]
  have hterm : ∀ (X : Matrix n m 𝕜) j,
      ‖toEuclideanLin A (WithLp.toLp 2 fun i => A.pinv i j) - e j‖ ^ 2
        ≤ ‖toEuclideanLin A (WithLp.toLp 2 fun i => X i j) - e j‖ ^ 2 := fun X j => by
    rw [hpinv]
    exact pow_le_pow_left₀ (norm_nonneg _) (A.norm_toEuclideanLin_pinv_sub_le _ _) 2
  have hmin : ∀ X : Matrix n m 𝕜, ‖A * A.pinv - 1‖ ≤ ‖A * X - 1‖ := fun X => by
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
    rw [hsq, hsq]
    exact Finset.sum_le_sum fun j _ => hterm X j
  refine ⟨isMinOn_univ_iff.2 hmin, fun X hX => ?_⟩
  -- every column of a minimizer is a least-squares solution
  have hls : ∀ j, IsLeastSquaresSolution A (e j) (WithLp.toLp 2 fun i => X i j) := by
    have heq : ∑ j, ‖toEuclideanLin A (WithLp.toLp 2 fun i => A.pinv i j) - e j‖ ^ 2
        = ∑ j, ‖toEuclideanLin A (WithLp.toLp 2 fun i => X i j) - e j‖ ^ 2 := by
      rw [← hsq, ← hsq, hX]
    have hj := (Finset.sum_eq_sum_iff_of_le fun j _ => hterm X j).1 heq
    intro j y
    have h1 := hj j (Finset.mem_univ _)
    rw [hpinv] at h1
    have h2 := pow_le_pow_left₀ (norm_nonneg _) (A.norm_toEuclideanLin_pinv_sub_le (e j) y) 2
    rw [h1] at h2
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h2
  have hnorm : ∀ j, ‖toEuclideanLin A.pinv (e j)‖ ≤ ‖(WithLp.toLp 2 fun i => X i j :
      EuclideanSpace 𝕜 n)‖ := fun j =>
    A.norm_pinv_le_of_normalEquations _ (isLeastSquaresSolution_iff_normalEquations.1 (hls j))
  have hnormsq : ∀ Y : Matrix n m 𝕜, ‖Y‖ ^ 2
      = ∑ j, ‖(WithLp.toLp 2 fun i => Y i j : EuclideanSpace 𝕜 n)‖ ^ 2 :=
    frobenius_norm_sq_eq_sum_norm_sq_col
  have hle : ∀ j ∈ (Finset.univ : Finset m),
      ‖(WithLp.toLp 2 fun i => A.pinv i j : EuclideanSpace 𝕜 n)‖ ^ 2
        ≤ ‖(WithLp.toLp 2 fun i => X i j : EuclideanSpace 𝕜 n)‖ ^ 2 := fun j _ => by
    rw [hpinv]; exact pow_le_pow_left₀ (norm_nonneg _) (hnorm j) 2
  refine ⟨(pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_, fun hXn => ?_⟩
  · rw [hnormsq, hnormsq]
    exact Finset.sum_le_sum hle
  · have heq : ∑ j, ‖(WithLp.toLp 2 fun i => A.pinv i j : EuclideanSpace 𝕜 n)‖ ^ 2
        = ∑ j, ‖(WithLp.toLp 2 fun i => X i j : EuclideanSpace 𝕜 n)‖ ^ 2 := by
      rw [← hnormsq, ← hnormsq, hXn]
    have hj := (Finset.sum_eq_sum_iff_of_le hle).1 heq
    ext i j
    have hmn : IsMinNormLeastSquaresSolution A (e j) (WithLp.toLp 2 fun i => X i j) := by
      refine ⟨hls j, fun y hy => ?_⟩
      have h1 := hj j (Finset.mem_univ _)
      rw [hpinv] at h1
      have h2 := A.norm_pinv_le_of_normalEquations _
        (isLeastSquaresSolution_iff_normalEquations.1 hy)
      have h3 := (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h1
      rw [← h3]
      exact h2
    have h := congrArg (fun w : EuclideanSpace 𝕜 n => w i) hmn.eq_pinv
    rw [← hpinv] at h
    simpa using h

end Frobenius

section MatrixUnknown

open scoped Matrix.Norms.Frobenius

variable {r : Type*} [Fintype r] [DecidableEq r]

omit [Fintype m] [Fintype r] [DecidableEq r] in
/-- Row $i$ of $A - F K^H$ is $-(\bar K f_i - a_i)$, where $f_i$ and $a_i$ are the rows of $F$ and
$A$ and $\bar K$ is the entrywise conjugate of $K$. -/
private theorem toLp_sub_mul_conjTranspose_row (A : Matrix m r 𝕜) (K : Matrix r n 𝕜)
    (F : Matrix m n 𝕜) (i : m) :
    (WithLp.toLp 2 ((A - F * Kᴴ) i) : EuclideanSpace 𝕜 r)
      = -(toEuclideanLin (K.map star) (WithLp.toLp 2 (F i)) - WithLp.toLp 2 (A i)) := by
  classical
  rw [neg_sub, toEuclideanLin_toLp]
  congr 1
  funext j
  simp only [Matrix.sub_apply, Matrix.mul_apply, conjTranspose_apply, Pi.sub_apply]
  congr 1
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

omit [DecidableEq r] in
/-- The squared Frobenius norm $\|A - F K^H\|_F^2$ is the sum over $i$ of the squared residuals
$\|\bar K f_i - a_i\|^2$ of the rows. -/
private theorem norm_sub_mul_conjTranspose_sq (A : Matrix m r 𝕜) (K : Matrix r n 𝕜)
    (F : Matrix m n 𝕜) :
    ‖A - F * Kᴴ‖ ^ 2 = ∑ i, ‖toEuclideanLin (K.map star) (WithLp.toLp 2 (F i))
      - WithLp.toLp 2 (A i)‖ ^ 2 := by
  classical
  rw [frobenius_norm_sq_eq_sum_norm_sq_row]
  exact Finset.sum_congr rfl fun i _ => by rw [toLp_sub_mul_conjTranspose_row, norm_neg]

omit [DecidableEq n] [DecidableEq r] in
/-- Let $A \in \mathbb{K}^{m \times r}$, $K \in \mathbb{K}^{r \times n}$ and
$F \in \mathbb{K}^{m \times n}$, and let the norm be the Frobenius norm. Then $F$ minimizes
$G \mapsto \|A - G K^H\|_F$ over all $G \in \mathbb{K}^{m \times n}$ if and only if
$$F K^H K = A K.$$
These are the normal equations of one update of the alternating least-squares method for the CP
decomposition, [golub2013matrix] (12.5.16)–(12.5.20).

Row by row, $\|A - F K^H\|_F^2 = \sum_i \|\bar K f_i - a_i\|^2$ with $\bar K$ the entrywise
conjugate of $K$ (`K.map star`), so each row is an ordinary least-squares problem
(`Matrix.isLeastSquaresSolution_iff_normalEquations`). A row that is not optimal can be replaced
alone. -/
theorem isMinOn_norm_sub_mul_conjTranspose_iff (A : Matrix m r 𝕜)
    (K : Matrix r n 𝕜) (F : Matrix m n 𝕜) :
    IsMinOn (fun G : Matrix m n 𝕜 => ‖A - G * Kᴴ‖) Set.univ F ↔ F * (Kᴴ * K) = A * K := by
  classical
  rw [isMinOn_univ_iff]
  set Kb : Matrix r n 𝕜 := K.map star with hKb
  have hrow : ∀ i, IsLeastSquaresSolution Kb (WithLp.toLp 2 (A i)) (WithLp.toLp 2 (F i)) ↔
      (F * (Kᴴ * K)) i = (A * K) i := by
    intro i
    rw [isLeastSquaresSolution_iff_normalEquations]
    simp only [toEuclideanLin_toLp]
    rw [(WithLp.toLp_injective 2).eq_iff]
    have h1 : Kbᴴ * Kb = (Kᴴ * K)ᵀ := by
      rw [hKb, transpose_mul]
      ext a c
      simp [Matrix.mul_apply, conjTranspose_apply]
    have h2 : Kbᴴ = Kᵀ := by ext a c; simp [hKb]
    rw [h1, h2, mulVec_transpose, mulVec_transpose]
    constructor <;> intro h <;> funext j <;>
      simpa [vecMul, dotProduct, Matrix.mul_apply] using congrFun h j
  have hsum := norm_sub_mul_conjTranspose_sq A K
  constructor
  · intro h
    ext i
    refine congrFun ((hrow i).1 fun y => ?_) _
    by_contra hlt
    push Not at hlt
    set G := F.updateRow i (WithLp.ofLp y) with hG
    have hGF : ∀ j, j ≠ i → G j = F j := fun j hj => updateRow_ne hj
    have hGi : G i = WithLp.ofLp y := updateRow_self
    have hlt2 := h G
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hlt2 2
    rw [hsum, hsum, ← Finset.add_sum_erase _ _ (Finset.mem_univ i),
      ← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hsq
    have heq : ∑ j ∈ Finset.univ.erase i, ‖toEuclideanLin Kb (WithLp.toLp 2 (G j))
        - WithLp.toLp 2 (A j)‖ ^ 2 = ∑ j ∈ Finset.univ.erase i,
        ‖toEuclideanLin Kb (WithLp.toLp 2 (F j)) - WithLp.toLp 2 (A j)‖ ^ 2 :=
      Finset.sum_congr rfl fun j hj => by rw [hGF j (Finset.ne_of_mem_erase hj)]
    rw [heq, hGi, WithLp.toLp_ofLp] at hsq
    have := pow_lt_pow_left₀ hlt (norm_nonneg _) two_ne_zero
    linarith
  · intro h G
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
    rw [hsum, hsum]
    refine Finset.sum_le_sum fun i _ => ?_
    exact pow_le_pow_left₀ (norm_nonneg _) (((hrow i).2 (congrFun h i)) _) 2

omit [DecidableEq n] [DecidableEq r] [Fintype m] in
/-- Let $A \in \mathbb{K}^{m \times r}$ and $K \in \mathbb{K}^{r \times n}$. Then some
$F \in \mathbb{K}^{m \times n}$ satisfies $F K^H K = A K$, so the problem
$\min_F \|A - F K^H\|_F$ has a solution.

Row $i$ of $F$ can be taken to be $\bar K^+ a_i$, the pseudoinverse solution of its row problem. -/
theorem exists_mul_conjTranspose_mul_self_eq [Finite m] (A : Matrix m r 𝕜)
    (K : Matrix r n 𝕜) : ∃ F : Matrix m n 𝕜, F * (Kᴴ * K) = A * K := by
  classical
  cases nonempty_fintype m
  refine ⟨Matrix.of fun i => WithLp.ofLp (toEuclideanLin (K.map star).pinv
    (WithLp.toLp 2 (A i))), ?_⟩
  refine (isMinOn_norm_sub_mul_conjTranspose_iff A K _).1 (isMinOn_univ_iff.2 fun G => ?_)
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
  rw [norm_sub_mul_conjTranspose_sq A K, norm_sub_mul_conjTranspose_sq A K]
  refine Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) ?_ 2
  exact
    isLeastSquaresSolution_pinv (K.map star) (WithLp.toLp 2 (A i)) (WithLp.toLp 2 (G i))

end MatrixUnknown

/-! ### Underdetermined systems through a QR factorization of $A^H$ -/

section ThinQR

variable {N : ℕ} [DecidableEq m]

/-- Let $A \in \mathbb{K}^{N \times m}$, and let $A^H = QR$ be a thin QR factorization:
$Q \in \mathbb{K}^{m \times N}$ with $Q^H Q = I$, and $R \in \mathbb{K}^{N \times N}$ upper
triangular. If $R$ is nonsingular, then
$$A^+ = Q (R^H)^{-1}.$$
Hence $x = Q (R^H)^{-1} b$ is the least-squares solution of least norm of $Ax = b$
(`Matrix.isMinNormLeastSquaresSolution_pinv`). This is the method of §5.6.2 of
[golub2013matrix], Algorithm 5.6.2, for a matrix of full row rank.

The thin QR factorization is `Matrix.IsThinQR`. With $A = R^H Q^H$, we have $A Q (R^H)^{-1} = I$
and $Q (R^H)^{-1} A = Q Q^H$, so the four Penrose conditions hold. -/
theorem pinv_eq_of_isThinQR_conjTranspose {A : Matrix (Fin N) m 𝕜} {Q : Matrix m (Fin N) 𝕜}
    {R : Matrix (Fin N) (Fin N) 𝕜} (h : IsThinQR Aᴴ Q R) (hR : IsUnit R) :
    A.pinv = Q * (Rᴴ)⁻¹ := by
  have hA : A = Rᴴ * Qᴴ := by
    rw [← conjTranspose_mul, h.mul_eq, conjTranspose_conjTranspose]
  have hRd : IsUnit Rᴴ.det := by
    rw [det_conjTranspose]
    exact ((isUnit_iff_isUnit_det R).1 hR).star
  have hAB : A * (Q * (Rᴴ)⁻¹) = 1 := by
    rw [hA, Matrix.mul_assoc, ← Matrix.mul_assoc Qᴴ, h.conjTranspose_mul_self, Matrix.one_mul,
      mul_nonsing_inv _ hRd]
  have hBA : Q * (Rᴴ)⁻¹ * A = Q * Qᴴ := by
    rw [hA, Matrix.mul_assoc, ← Matrix.mul_assoc (Rᴴ)⁻¹, nonsing_inv_mul _ hRd, Matrix.one_mul]
  refine (pinv_unique A ?_ ?_ ?_ ?_).symm
  · rw [hAB, Matrix.one_mul]
  · rw [Matrix.mul_assoc, hAB, Matrix.mul_one]
  · rw [hAB]; exact isHermitian_one
  · rw [hBA, IsHermitian, conjTranspose_mul, conjTranspose_conjTranspose]

end ThinQR

end Matrix
