/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.LinearAlgebra.Matrix.LeastSquares
import Numlib.LinearAlgebra.Matrix.CompleteOrthogonal
import Numlib.LinearAlgebra.Matrix.NonsingularInverse
import Numlib.LinearAlgebra.Matrix.SchurComplement
import Numlib.Analysis.InnerProductSpace.Energy

/-!
# Conn, Gould and Toint, Section 4.4: Least-squares problems and projections

This module formalizes Section 4.4 of [conn2000trust]. For $A \in \mathbb{R}^{m \times n}$ and
$g \in \mathbb{R}^n$, a least-squares multiplier $y$ minimizes $\|A^T y - g\|_2$ (4.4.1). It is
characterized by the normal equations $AA^T y = Ag$ (4.4.3) and by the augmented system with the
matrix $\begin{bmatrix} I & A^T \\ A & 0 \end{bmatrix}$ (4.4.4)–(4.4.5). The section then treats the
equality-constrained quadratic problem
$$\min_x \ \tfrac{1}{2} x^T H x - g^T x \quad \text{subject to} \quad Ax = b$$
of (4.4.14) and the weighted projection (4.4.7), the point of $\{x : Ax = b\}$ nearest to $x_0$ in
the $H$-norm. Both lead to the augmented system $\begin{bmatrix} H & A^T \\ A & 0 \end{bmatrix}
\begin{bmatrix} x \\ -y \end{bmatrix} = \begin{bmatrix} g \\ b \end{bmatrix}$ of (4.4.8), which the
range-space method (4.4.9) and the null-space method (4.4.10)–(4.4.13) reduce to smaller systems.

The proofs use the backbone modules `Numlib.LinearAlgebra.Matrix.LeastSquares`,
`Numlib.LinearAlgebra.Matrix.CompleteOrthogonal`, `Numlib.LinearAlgebra.Matrix.SchurComplement` and
`Numlib.Analysis.InnerProductSpace.Energy`.

## Main definitions

* Equation (4.4.1), `ConnGouldToint.Chapter04.IsLeastSquaresMultiplier`: $y$ minimizes
  $\|A^T y - g\|_2$.
* Equation (4.4.5), `ConnGouldToint.Chapter04.leastSquaresMatrix`: the matrix
  $\begin{bmatrix} I & A^T \\ A & 0 \end{bmatrix}$.
* Equation (4.4.7), `ConnGouldToint.Chapter04.IsWeightedProjection`: $x$ minimizes
  $\frac{1}{2} \|x_0 - z\|_H^2$ over $Az = b$.
* Equation (4.4.14), `ConnGouldToint.Chapter04.IsEqualityQuadraticMin`: $x$ minimizes
  $\frac{1}{2} z^T H z - z^T g$ over $Az = b$.

## Main results

* Equation (4.4.2), `ConnGouldToint.Chapter04.least_squares_square_4_4_2`: the expansion of
  $\|A^T y - g\|_2^2$ as a quadratic in $y$.
* Equation (4.4.3), `ConnGouldToint.Chapter04.normal_equations_4_4_3`: the least-squares multipliers
  are the solutions of $AA^T y = Ag$.
* Equation (4.4.3), `ConnGouldToint.Chapter04.normal_equations_consistent_4_4_3`: the normal
  equations always have a solution.
* Equation (4.4.3), `ConnGouldToint.Chapter04.normal_equations_unique_4_4_3`: the solution is unique
  if and only if the rows of $A$ are linearly independent.
* Equation (4.4.4), `ConnGouldToint.Chapter04.augmented_least_squares_4_4_4`: the least-squares
  multipliers are the second components of the solutions of the augmented system.
* Equation (4.4.5), `ConnGouldToint.Chapter04.isUnit_leastSquaresMatrix`: the augmented matrix is
  nonsingular if and only if the rows of $A$ are linearly independent.
* Equation (4.4.6), `ConnGouldToint.Chapter04.complete_orthogonal_4_4_6`: $A$ has a complete
  orthogonal decomposition with a lower triangular leading block of order $\operatorname{rank} A$.
* Equations (4.4.7)–(4.4.8), `ConnGouldToint.Chapter04.weighted_projection_of_system_4_4_8`: a
  solution of the augmented system gives the weighted projection.
* Equations (4.4.7)–(4.4.8), `ConnGouldToint.Chapter04.weighted_projection_4_4_8_iff`: the weighted
  projections are the first components of the solutions of the augmented system.
* Equations (4.4.8)–(4.4.9), `ConnGouldToint.Chapter04.projection_system_4_4_8`: the augmented
  system is equivalent to stationarity and feasibility.
* Equations (4.4.8)–(4.4.9), `ConnGouldToint.Chapter04.projection_range_system_4_4_9`: for
  invertible $H$, the range-space system for $y$.
* Equation (4.4.10), `ConnGouldToint.Chapter04.range_null_decomposition_4_4_10`: every vector is the
  sum of a vector in the range of $A^T$ and a vector in the null space of $A$.
* Equation (4.4.11), `ConnGouldToint.Chapter04.feasible_null_decomposition_4_4_11`: every feasible
  point is a particular feasible point plus a null-space displacement.
* Equation (4.4.12), `ConnGouldToint.Chapter04.reduced_system_4_4_12`: the reduced system
  $N^T H N u = N^T g - N^T H x_F$.
* Equation (4.4.13), `ConnGouldToint.Chapter04.null_basis_4_4_13`: the null basis
  $\begin{bmatrix} -R^{-1} C \\ I \end{bmatrix}$ for $A = \begin{bmatrix} R & C \end{bmatrix}$ up to
  a column permutation.
* Equation (4.4.14), `ConnGouldToint.Chapter04.quadratic_minimum_4_4_14`: a stationary feasible
  point with positive semidefinite reduced Hessian is a global minimizer, and it is unique if the
  reduced Hessian is positive definite.
* Equation (4.4.14), `ConnGouldToint.Chapter04.quadratic_minimum_4_4_14_iff`: the minimizers are the
  feasible stationary points with positive semidefinite reduced Hessian.
* After (4.4.14), `ConnGouldToint.Chapter04.semidefinite_reduced_quadratic_not_unique`: with a
  positive semidefinite reduced Hessian the minimizer need not be unique.

## Conventions

* Vectors in norms and inner products are `EuclideanSpace ℝ (Fin n)`; vectors in matrix-vector
  products are `Fin n → ℝ`. The coercion between them is `WithLp.ofLp`.
* "The rows of $A$ are linearly independent" is `LinearIndependent ℝ A`, since a matrix is the
  family of its rows.
* The block vector $(x, y)$ is `Sum.elim x y`, and the block matrix
  $\begin{bmatrix} H & A^T \\ A & 0 \end{bmatrix}$ is `Matrix.saddleMatrix H Aᵀ 0`.

## Deviations from the source

* **Equation (4.4.10)** (reading). The range-space component of the decomposition lies in the range
  of $A^T$, which is the orthogonal complement of the null space of $A$. See
  `ConnGouldToint.Chapter04.range_null_decomposition_4_4_10`.
* **After (4.4.14)** (correction). Positive semidefinite reduced curvature makes a stationary
  feasible point a global minimizer but does not make it unique; uniqueness needs positive definite
  reduced curvature. See `ConnGouldToint.Chapter04.quadratic_minimum_4_4_14` and
  `ConnGouldToint.Chapter04.semidefinite_reduced_quadratic_not_unique`.
-/

open Matrix
open scoped Matrix RealInnerProductSpace

namespace ConnGouldToint.Chapter04

variable {m n : ℕ}

/-- **Equation (4.4.1)** of [conn2000trust]. Let $A \in \mathbb{R}^{m \times n}$ and
$g \in \mathbb{R}^n$. A vector $y \in \mathbb{R}^m$ is a **least-squares multiplier** if it
minimizes the residual of the transposed system:
$$\|A^T y - g\|_2 \le \|A^T w - g\|_2 \quad \text{for all } w \in \mathbb{R}^m.$$

It is `Matrix.IsLeastSquaresSolution Aᵀ g y`. -/
abbrev IsLeastSquaresMultiplier (A : Matrix (Fin m) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n))
    (y : EuclideanSpace ℝ (Fin m)) : Prop := Matrix.IsLeastSquaresSolution Aᵀ g y

/-- **Equation (4.4.2)** of [conn2000trust]. Let $A \in \mathbb{R}^{m \times n}$,
$g \in \mathbb{R}^n$ and $y \in \mathbb{R}^m$. Then
$$\|A^T y - g\|_2^2 = y^T A A^T y - 2 y^T A g + g^T g.$$
-/
theorem least_squares_square_4_4_2 (A : Matrix (Fin m) (Fin n) ℝ)
    (g : EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin m)) :
    ‖Aᵀ.toEuclideanLin y - g‖ ^ 2 =
      inner ℝ y ((A * Aᵀ).toEuclideanLin y) - 2 * inner ℝ y (A.toEuclideanLin g) + inner ℝ g g := by
  rw [norm_sub_sq_real, ← real_inner_self_eq_norm_sq (Aᵀ.toEuclideanLin y),
    ← real_inner_self_eq_norm_sq g, Matrix.toEuclideanLin_mul_apply,
    Matrix.toEuclideanLin_transpose_inner_left A (Aᵀ.toEuclideanLin y) y,
    Matrix.toEuclideanLin_transpose_inner_left A g y]

/-- **Equation (4.4.3)** of [conn2000trust]. Let $A \in \mathbb{R}^{m \times n}$ and
$g \in \mathbb{R}^n$. A vector $y \in \mathbb{R}^m$ is a least-squares multiplier if and only if
it solves the normal equations
$$A A^T y = A g.$$
-/
theorem normal_equations_4_4_3 {A : Matrix (Fin m) (Fin n) ℝ}
    {g : EuclideanSpace ℝ (Fin n)} {y : EuclideanSpace ℝ (Fin m)} :
    IsLeastSquaresMultiplier A g y ↔ (A * Aᵀ).toEuclideanLin y = A.toEuclideanLin g := by
  simpa only [conjTranspose_eq_transpose_of_trivial, transpose_transpose] using
    (Matrix.isLeastSquaresSolution_iff_normalEquations (A := Aᵀ) (b := g) (x := y))


/-- **Equation (4.4.3)** of [conn2000trust], consistency. Let $A \in \mathbb{R}^{m \times n}$ and
$g \in \mathbb{R}^n$. Then the normal equations $AA^T y = Ag$ have a solution
$y \in \mathbb{R}^m$. -/
theorem normal_equations_consistent_4_4_3 (A : Matrix (Fin m) (Fin n) ℝ)
    (g : EuclideanSpace ℝ (Fin n)) :
    ∃ y : EuclideanSpace ℝ (Fin m), (A * Aᵀ).toEuclideanLin y = A.toEuclideanLin g :=
  ⟨_, normal_equations_4_4_3.mp (Matrix.isLeastSquaresSolution_pinv Aᵀ g)⟩

/-- **Equation (4.4.3)** of [conn2000trust], uniqueness. Let $A \in \mathbb{R}^{m \times n}$ and
$g \in \mathbb{R}^n$. The normal equations $AA^T y = Ag$ have exactly one solution if and only
if the rows of $A$ are linearly independent. -/
theorem normal_equations_unique_4_4_3 (A : Matrix (Fin m) (Fin n) ℝ)
    (g : EuclideanSpace ℝ (Fin n)) :
    (∃! y : EuclideanSpace ℝ (Fin m), (A * Aᵀ).toEuclideanLin y = A.toEuclideanLin g) ↔
      LinearIndependent ℝ A := by
  constructor
  · rintro ⟨u, hu, hu'⟩
    apply Matrix.vecMul_injective_iff.mp
    intro v w hvw
    let d : EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 (v - w)
    have hd : Aᵀ.toEuclideanLin d = 0 := by
      rw [Matrix.toEuclideanLin_apply, ← Matrix.vecMul_transpose, Matrix.transpose_transpose,
        ← WithLp.toLp_zero 2]
      congr 1
      simp only [d, Matrix.sub_vecMul, hvw, sub_self]
    have hsol : (A * Aᵀ).toEuclideanLin (u + d) = A.toEuclideanLin g := by
      rw [map_add, hu, Matrix.toEuclideanLin_mul_apply, hd, map_zero, add_zero]
    have he : d = 0 := add_eq_left.mp (hu' _ hsol)
    exact sub_eq_zero.mp ((WithLp.toLp_injective 2) (by simpa only [WithLp.toLp_zero] using he))
  · intro h
    simpa only [← normal_equations_4_4_3] using
      (Matrix.existsUnique_isLeastSquaresSolution (A := Aᵀ)
        (by simpa only [transpose_transpose] using h) g)

/-- **Equation (4.4.5)** of [conn2000trust]. For $A \in \mathbb{R}^{m \times n}$, the coefficient
matrix of the augmented least-squares system is
$$\begin{bmatrix} I & A^T \\ A & 0 \end{bmatrix} \in \mathbb{R}^{(n + m) \times (n + m)}.$$
-/
abbrev leastSquaresMatrix (A : Matrix (Fin m) (Fin n) ℝ) :
    Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ := Matrix.fromBlocks 1 Aᵀ A 0

/-- **Equation (4.4.5)** of [conn2000trust], nonsingularity. For $A \in \mathbb{R}^{m \times n}$,
the matrix $\begin{bmatrix} I & A^T \\ A & 0 \end{bmatrix}$ is nonsingular if and only if the
rows of $A$ are linearly independent. -/
theorem isUnit_leastSquaresMatrix (A : Matrix (Fin m) (Fin n) ℝ) :
    IsUnit (leastSquaresMatrix A) ↔ LinearIndependent ℝ A := by
  simpa only [leastSquaresMatrix, conjTranspose_eq_transpose_of_trivial, transpose_transpose] using
    (Matrix.isUnit_augmented_iff Aᵀ)

/-- **Equation (4.4.4)** of [conn2000trust]. Let $A \in \mathbb{R}^{m \times n}$,
$g \in \mathbb{R}^n$ and $y \in \mathbb{R}^m$. Then $y$ is a least-squares multiplier if and
only if there is $r \in \mathbb{R}^n$ with
$$\begin{bmatrix} I & A^T \\ A & 0 \end{bmatrix} \begin{bmatrix} r \\ y \end{bmatrix} =
  \begin{bmatrix} g \\ 0 \end{bmatrix}.$$

The first component is then the residual $r = g - A^T y$. -/
theorem augmented_least_squares_4_4_4 (A : Matrix (Fin m) (Fin n) ℝ)
    (g : EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin m)) :
    IsLeastSquaresMultiplier A g y ↔
      ∃ r : Fin n → ℝ,
        leastSquaresMatrix A *ᵥ Sum.elim r (WithLp.ofLp y) =
          Sum.elim (WithLp.ofLp g) 0 := by
  rw [normal_equations_4_4_3]
  have hnormal :
      (A * Aᵀ).toEuclideanLin y = A.toEuclideanLin g ↔
        A *ᵥ (Aᵀ *ᵥ WithLp.ofLp y) = A *ᵥ WithLp.ofLp g := by
    rw [Matrix.toEuclideanLin_mul_apply, Matrix.toEuclideanLin_apply, Matrix.toEuclideanLin_apply,
      Matrix.toEuclideanLin_apply, WithLp.ofLp_toLp, (WithLp.toLp_injective 2).eq_iff]
  rw [hnormal]
  have hblock (r : Fin n → ℝ) :
      leastSquaresMatrix A *ᵥ Sum.elim r (WithLp.ofLp y) = Sum.elim (WithLp.ofLp g) 0 ↔
        r + Aᵀ *ᵥ WithLp.ofLp y = WithLp.ofLp g ∧ A *ᵥ r = 0 := by
    rw [leastSquaresMatrix, Matrix.fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr,
      Sum.elim_eq_iff]
    simp
  constructor
  · intro h
    refine ⟨WithLp.ofLp g - Aᵀ *ᵥ WithLp.ofLp y, (hblock _).2 ⟨by abel, ?_⟩⟩
    rw [Matrix.mulVec_sub, h, sub_self]
  · rintro ⟨r, hr⟩
    obtain ⟨he, hz⟩ := (hblock r).1 hr
    rw [← he, Matrix.mulVec_add, hz, zero_add]

/-- **Equation (4.4.6)** of [conn2000trust] (complete orthogonal decomposition). Let
$A \in \mathbb{R}^{m \times n}$ have rank $r$. Then there are orthogonal matrices
$U \in \mathbb{R}^{m \times m}$ and $V \in \mathbb{R}^{n \times n}$ such that
$$U^T A V = \begin{bmatrix} T & 0 \\ 0 & 0 \end{bmatrix}$$
with $T \in \mathbb{R}^{r \times r}$ nonsingular and lower triangular.

The decomposition is `Matrix.IsCompleteOrthogonal A U V A.rank`. The proof takes a singular
value decomposition, whose leading block is diagonal. -/
theorem complete_orthogonal_4_4_6 (A : Matrix (Fin m) (Fin n) ℝ) :
    ∃ U V, ∃ h : Matrix.IsCompleteOrthogonal A U V A.rank,
      ((Uᵀ * A * V).submatrix (Fin.castLE h.le_rows) (Fin.castLE h.le_cols)).IsLowerTriangular := by
  obtain ⟨U, σ, V, h⟩ := A.exists_isSVD
  refine ⟨U, V, Matrix.isCompleteOrthogonal_of_svd h, ?_⟩
  have he : Uᵀ * A * V = Matrix.rectDiagonal σ := by
    simpa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using h.star_mul_mul
  rw [he]
  intro i j hij
  have hne : (i : ℕ) ≠ (j : ℕ) := fun h => (ne_of_lt hij) (Fin.ext h.symm)
  simp [Matrix.rectDiagonal_apply, hne]

/-- **Equation (4.4.7)** of [conn2000trust]. Let $H \in \mathbb{R}^{n \times n}$ be symmetric
positive definite, $A \in \mathbb{R}^{m \times n}$, $b \in \mathbb{R}^m$ and
$x_0 \in \mathbb{R}^n$. A point $x$ is the **weighted projection** of $x_0$ onto
$\{z : Az = b\}$ if $Ax = b$ and $x$ minimizes
$$\tfrac{1}{2} \|x_0 - z\|_H^2$$
over all $z$ with $Az = b$.

The $H$-norm is `energyNorm` of `Matrix.toEuclideanLin H`. The positive definiteness is an
argument that the definition does not use. -/
def IsWeightedProjection (H : Matrix (Fin n) (Fin n) ℝ) (_ : H.PosDef)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin m))
    (x₀ x : EuclideanSpace ℝ (Fin n)) : Prop :=
  x ∈ {z | A.toEuclideanLin z = b} ∧
    IsMinOn (fun z => (1 / 2 : ℝ) * energyNorm H.toEuclideanLin (x₀ - z) ^ 2)
      {z | A.toEuclideanLin z = b} x

/-- **Equations (4.4.8)–(4.4.9)** of [conn2000trust]. Let $H \in \mathbb{R}^{n \times n}$,
$A \in \mathbb{R}^{m \times n}$, $x, g \in \mathbb{R}^n$ and $y, b \in \mathbb{R}^m$. Then
$$\begin{bmatrix} H & A^T \\ A & 0 \end{bmatrix} \begin{bmatrix} x \\ -y \end{bmatrix} =
  \begin{bmatrix} g \\ b \end{bmatrix} \iff Hx = g + A^T y \text{ and } Ax = b.$$

The second block of the unknown is the negated multiplier $-y$. -/
theorem projection_system_4_4_8 (H : Matrix (Fin n) (Fin n) ℝ)
    (A : Matrix (Fin m) (Fin n) ℝ) (x g : Fin n → ℝ) (y b : Fin m → ℝ) :
    Matrix.saddleMatrix H Aᵀ 0 *ᵥ Sum.elim x (-y) = Sum.elim g b ↔
      H *ᵥ x = g + Aᵀ *ᵥ y ∧ A *ᵥ x = b := by
  rw [Matrix.saddleMatrix_mulVec_elim]
  simp [conjTranspose_eq_transpose_of_trivial, mulVec_neg, ← sub_eq_add_neg, sub_eq_iff_eq_add]

/-- **Equation (4.4.10)** of [conn2000trust]. Let $A \in \mathbb{R}^{m \times n}$. Every
$x \in \mathbb{R}^n$ is the sum of a range-space component and a null-space component: there are
$r \in \mathbb{R}^m$ and $z \in \mathbb{R}^n$ with
$$x = A^T r + z, \qquad Az = 0.$$

**Reading.** The source calls the first component the row-space component. Here it is a vector
of the range of $A^T$, which is the orthogonal complement of the null space of $A$. -/
theorem range_null_decomposition_4_4_10 (A : Matrix (Fin m) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    ∃ r : EuclideanSpace ℝ (Fin m), ∃ z : EuclideanSpace ℝ (Fin n),
      A.toEuclideanLin z = 0 ∧ x = Aᵀ.toEuclideanLin r + z := by
  obtain ⟨z, hz, w, hw, hx⟩ := (LinearMap.ker A.toEuclideanLin).exists_add_mem_mem_orthogonal x
  rw [LinearMap.orthogonal_ker, ← Matrix.toEuclideanLin_transpose_eq_adjoint] at hw
  obtain ⟨r, hr⟩ := hw
  exact ⟨r, z, hz, by rw [hr, add_comm]; exact hx⟩

/-- **Equation (4.4.11)** of [conn2000trust]. Let $A \in \mathbb{R}^{m \times n}$, and let the
columns of $N \in \mathbb{R}^{n \times k}$ span the null space of $A$, that is, every $z$ with
$Az = 0$ is $Nu$ for some $u$. If $Ax = b$ and $Ax_F = b$, then $x = x_F + Nu$ for some
$u \in \mathbb{R}^k$. -/
theorem feasible_null_decomposition_4_4_11 {k : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (N : Matrix (Fin n) (Fin k) ℝ) (x xF : Fin n → ℝ) (b : Fin m → ℝ)
    (hx : A *ᵥ x = b) (hF : A *ᵥ xF = b)
    (hN : ∀ z : Fin n → ℝ, A *ᵥ z = 0 → ∃ u, N *ᵥ u = z) :
    ∃ u, x = xF + N *ᵥ u := by
  obtain ⟨u, hu⟩ := hN (x - xF) (by rw [Matrix.mulVec_sub, hx, hF, sub_self])
  exact ⟨u, by rw [hu]; abel⟩

/-- **Equation (4.4.12)** of [conn2000trust]. Let $H \in \mathbb{R}^{n \times n}$,
$A \in \mathbb{R}^{m \times n}$ and $N \in \mathbb{R}^{n \times k}$ with $AN = 0$. Let
$x_F, g \in \mathbb{R}^n$, $y \in \mathbb{R}^m$ and $u \in \mathbb{R}^k$ satisfy the
stationarity condition $H(x_F + Nu) = g + A^T y$. Then the null-space coordinates $u$ solve the
reduced system
$$N^T H N u = N^T g - N^T H x_F.$$
-/
theorem reduced_system_4_4_12 {k : ℕ} (H : Matrix (Fin n) (Fin n) ℝ)
    (A : Matrix (Fin m) (Fin n) ℝ) (N : Matrix (Fin n) (Fin k) ℝ)
    (xF g : Fin n → ℝ) (y : Fin m → ℝ) (u : Fin k → ℝ)
    (hN : A * N = 0) (hstat : H *ᵥ (xF + N *ᵥ u) = g + Aᵀ *ᵥ y) :
    (Nᵀ * H * N) *ᵥ u = Nᵀ *ᵥ g - Nᵀ *ᵥ (H *ᵥ xF) := by
  have h := congrArg (fun v => Nᵀ *ᵥ v) hstat
  have hzero : Nᵀ * Aᵀ = 0 := by rw [← Matrix.transpose_mul, hN, transpose_zero]
  simp only [mulVec_add, mulVec_mulVec, hzero, zero_mulVec, add_zero] at h
  rw [mulVec_mulVec]
  exact eq_sub_of_add_eq (by simpa [add_comm, Matrix.mul_assoc] using h)

/-- **Equation (4.4.13)** of [conn2000trust]. Let $R \in \mathbb{R}^{m \times m}$ be nonsingular and
$C \in \mathbb{R}^{m \times k}$, and let $A = \begin{bmatrix} R & C \end{bmatrix}$ with its
columns permuted, and
$$N = \begin{bmatrix} -R^{-1} C \\ I \end{bmatrix}$$
with its rows permuted in the same way. Then $u \mapsto Nu$ is injective, and $Az = 0$ if and
only if $z = Nu$ for some $u \in \mathbb{R}^k$.

The permutation is a bijection `e : Fin (m + k) ≃ Fin m ⊕ Fin k` that sends each column index of
$A$ to a pivot or a free coordinate. -/
theorem null_basis_4_4_13 {k : ℕ} (R : Matrix (Fin m) (Fin m) ℝ) (C : Matrix (Fin m) (Fin k) ℝ)
    (hR : IsUnit R) (e : Fin (m + k) ≃ (Fin m ⊕ Fin k)) :
    let A := (Matrix.fromCols R C).submatrix id e
    let N := (Matrix.fromRows (-(R⁻¹ * C)) (1 : Matrix (Fin k) (Fin k) ℝ)).submatrix e id
    Function.Injective N.mulVec ∧ ∀ z, A *ᵥ z = 0 ↔ ∃ u, N *ᵥ u = z := by
  dsimp only
  let N := (Matrix.fromRows (-(R⁻¹ * C)) (1 : Matrix (Fin k) (Fin k) ℝ)).submatrix e id
  have hN (u : Fin k → ℝ) :
      N *ᵥ u = Sum.elim (-(R⁻¹ *ᵥ (C *ᵥ u))) u ∘ e := by
    dsimp only [N]
    rw [show (id : Fin k → Fin k) = (Equiv.refl (Fin k) : Fin k → Fin k) from rfl,
      Matrix.submatrix_mulVec_equiv]
    simp [Matrix.neg_mulVec, Matrix.mulVec_mulVec]
  refine ⟨fun u v huv => ?_, fun z => ?_⟩
  · change N *ᵥ u = N *ᵥ v at huv
    rw [hN, hN] at huv
    funext j
    simpa using congrFun huv (e.symm (Sum.inr j))
  · rw [Matrix.submatrix_mulVec_equiv, Function.comp_id, Matrix.fromCols_mulVec]
    constructor
    · intro hz
      let u := z ∘ e.symm ∘ Sum.inr
      have hz' : R *ᵥ (z ∘ e.symm ∘ Sum.inl) = -(C *ᵥ u) := eq_neg_of_add_eq_zero_left hz
      have hp := (Matrix.nonsing_inv_mulVec_eq hR hz').symm
      rw [Matrix.mulVec_neg] at hp
      refine ⟨u, ?_⟩
      change N *ᵥ u = z
      rw [hN, ← hp]
      funext j
      have h : z (e.symm (e j)) = z j := by simp
      cases hj : e j <;> simpa [Function.comp_apply, hj, u] using h
    · rintro ⟨u, hu⟩
      change N *ᵥ u = z at hu
      rw [← hu, hN]
      have h₁ : ((Sum.elim (-(R⁻¹ *ᵥ (C *ᵥ u))) u ∘ e) ∘ e.symm) ∘ Sum.inl =
          -(R⁻¹ *ᵥ (C *ᵥ u)) := by ext i; simp
      have h₂ : ((Sum.elim (-(R⁻¹ *ᵥ (C *ᵥ u))) u ∘ e) ∘ e.symm) ∘ Sum.inr = u := by
        ext i
        simp
      rw [h₁, h₂, Matrix.mulVec_neg, Matrix.mulVec_nonsing_inv_mulVec hR, neg_add_cancel]

/-- **Equation (4.4.14)** of [conn2000trust]. Let $H \in \mathbb{R}^{n \times n}$,
$A \in \mathbb{R}^{m \times n}$, $g \in \mathbb{R}^n$ and $b \in \mathbb{R}^m$. A point $x$ is a
**minimizer of the equality-constrained quadratic** if $Ax = b$ and $x$ minimizes
$$\tfrac{1}{2} z^T H z - z^T g$$
over all $z$ with $Az = b$. -/
def IsEqualityQuadraticMin (H : Matrix (Fin n) (Fin n) ℝ)
    (A : Matrix (Fin m) (Fin n) ℝ) (g x : Fin n → ℝ) (b : Fin m → ℝ) : Prop :=
  A *ᵥ x = b ∧ IsMinOn (fun z => (1 / 2 : ℝ) * (z ⬝ᵥ (H *ᵥ z)) - z ⬝ᵥ g)
    {z | A *ᵥ z = b} x

/-- **Equation (4.4.14)** of [conn2000trust], sufficiency and uniqueness. Let
$H \in \mathbb{R}^{n \times n}$ be symmetric, $A \in \mathbb{R}^{m \times n}$,
$g \in \mathbb{R}^n$ and $b \in \mathbb{R}^m$. Let $x$ be feasible, $Ax = b$, and stationary,
$Hx = g + A^T y$ for some $y \in \mathbb{R}^m$, and suppose $d^T H d \ge 0$ for every $d$ with
$Ad = 0$. Then

* $x$ is a global minimizer of $\frac{1}{2} z^T H z - z^T g$ subject to $Az = b$, and
* if moreover $d^T H d > 0$ for every nonzero $d$ with $Ad = 0$, then $x$ is the only minimizer.

**Correction.** The source draws uniqueness from positive semidefinite reduced curvature.
Semidefinite curvature gives only global optimality, and uniqueness needs positive definite
reduced curvature; see `ConnGouldToint.Chapter04.semidefinite_reduced_quadratic_not_unique`. -/
theorem quadratic_minimum_4_4_14 {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.IsSymm)
    (A : Matrix (Fin m) (Fin n) ℝ) {x g : Fin n → ℝ} {y b : Fin m → ℝ}
    (hx : A *ᵥ x = b) (hstat : H *ᵥ x = g + Aᵀ *ᵥ y)
    (hnonneg : ∀ d : Fin n → ℝ, A *ᵥ d = 0 → 0 ≤ d ⬝ᵥ (H *ᵥ d)) :
    IsEqualityQuadraticMin H A g x b ∧
      ((∀ d : Fin n → ℝ, A *ᵥ d = 0 → d ≠ 0 → 0 < d ⬝ᵥ (H *ᵥ d)) →
        ∀ z, IsEqualityQuadraticMin H A g z b → z = x) := by
  let f (z : Fin n → ℝ) := (1 / 2 : ℝ) * (z ⬝ᵥ (H *ᵥ z)) - z ⬝ᵥ g
  have hd (z : Fin n → ℝ) (hz : A *ᵥ z = b) : A *ᵥ (z - x) = 0 := by
    rw [mulVec_sub, hz, hx, sub_self]
  have hdiff (z : Fin n → ℝ) (hz : A *ᵥ z = b) :
      f z - f x = (1 / 2 : ℝ) * ((z - x) ⬝ᵥ (H *ᵥ (z - x))) := by
    let d := z - x
    have hsplit : z = x + d := by dsimp [d]; abel
    have hsym : x ⬝ᵥ (H *ᵥ d) = d ⬝ᵥ (H *ᵥ x) := by
      conv_lhs => rw [← hH.eq]
      exact Matrix.dotProduct_transpose_mulVec H x d
    have hzstat : d ⬝ᵥ (H *ᵥ x) = d ⬝ᵥ g := by
      rw [hstat, dotProduct_add, Matrix.dotProduct_transpose_mulVec, hd z hz,
        dotProduct_zero, add_zero]
    change f z - f x = (1 / 2 : ℝ) * (d ⬝ᵥ (H *ᵥ d))
    conv_lhs => rw [hsplit]
    simp only [f, mulVec_add, dotProduct_add, add_dotProduct, hsym, hzstat]
    ring
  have hmin : IsEqualityQuadraticMin H A g x b :=
    ⟨hx, fun z hz => sub_nonneg.mp (by
      rw [hdiff z hz]
      exact mul_nonneg (by norm_num) (hnonneg (z - x) (hd z hz)))⟩
  refine ⟨hmin, fun hpos z hz => ?_⟩
  by_contra hne
  have hp := hpos (z - x) (hd z hz.1) (sub_ne_zero.2 hne)
  have hle : f z ≤ f x := hz.2 hx
  linarith [hdiff z hz.1]


/-- **Equation (4.4.14)** of [conn2000trust], characterization. Let $H \in \mathbb{R}^{n \times n}$
be symmetric, $A \in \mathbb{R}^{m \times n}$, $g, x \in \mathbb{R}^n$ and $b \in \mathbb{R}^m$.
Then $x$ minimizes $\frac{1}{2} z^T H z - z^T g$ subject to $Az = b$ if and only if

* $Ax = b$,
* $Hx = g + A^T y$ for some $y \in \mathbb{R}^m$, and
* $d^T H d \ge 0$ for every $d$ with $Ad = 0$.

The multiplier $y$ exists also when the rows of $A$ are linearly dependent. -/
theorem quadratic_minimum_4_4_14_iff {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.IsSymm)
    (A : Matrix (Fin m) (Fin n) ℝ) (g x : Fin n → ℝ) (b : Fin m → ℝ) :
    IsEqualityQuadraticMin H A g x b ↔
      A *ᵥ x = b ∧ (∃ y : Fin m → ℝ, H *ᵥ x = g + Aᵀ *ᵥ y) ∧
      ∀ d : Fin n → ℝ, A *ᵥ d = 0 → 0 ≤ d ⬝ᵥ (H *ᵥ d) := by
  constructor
  · rintro ⟨hx, hmin⟩
    let f (z : Fin n → ℝ) := (1 / 2 : ℝ) * (z ⬝ᵥ (H *ᵥ z)) - z ⬝ᵥ g
    let r := H *ᵥ x - g
    have hpoly (d : Fin n → ℝ) (t : ℝ) :
        f (x + t • d) = f x + t * (d ⬝ᵥ r) + (1 / 2 : ℝ) * t ^ 2 * (d ⬝ᵥ (H *ᵥ d)) := by
      have hsym : x ⬝ᵥ (H *ᵥ d) = d ⬝ᵥ (H *ᵥ x) := by
        conv_lhs => rw [← hH.eq]
        exact Matrix.dotProduct_transpose_mulVec H x d
      simp only [f, r, mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct,
        smul_dotProduct, dotProduct_smul, smul_eq_mul, hsym, dotProduct_sub]
      ring
    have hfeas (d : Fin n → ℝ) (hd : A *ᵥ d = 0) (t : ℝ) :
        A *ᵥ (x + t • d) = b := by
      rw [mulVec_add, mulVec_smul, hx, hd, smul_zero, add_zero]
    have hzero (d : Fin n → ℝ) (hd : A *ᵥ d = 0) : d ⬝ᵥ r = 0 := by
      have hm : IsLocalMin (fun t : ℝ ↦
          f x + t * (d ⬝ᵥ r) + (1 / 2 : ℝ) * t ^ 2 * (d ⬝ᵥ (H *ᵥ d))) 0 := by
        apply IsMinOn.isLocalMin (s := Set.univ) ?_ Filter.univ_mem
        intro t _
        have ht : f x ≤ f (x + t • d) := hmin (hfeas d hd t)
        rw [hpoly] at ht
        simpa using ht
      have hder : HasDerivAt (fun t : ℝ ↦
          f x + t * (d ⬝ᵥ r) + (1 / 2 : ℝ) * t ^ 2 * (d ⬝ᵥ (H *ᵥ d))) (d ⬝ᵥ r) 0 := by
        convert (((hasDerivAt_id (0 : ℝ)).mul_const (d ⬝ᵥ r)).const_add (f x)).add
          ((((hasDerivAt_id (0 : ℝ)).pow 2).const_mul (1 / 2 : ℝ)).mul_const
            (d ⬝ᵥ (H *ᵥ d))) using 1
        · rfl
        · norm_num [id]
      exact hm.hasDerivAt_eq_zero hder
    have horth : WithLp.toLp 2 r ∈ (LinearMap.ker A.toEuclideanLin)ᗮ := by
      rw [Submodule.mem_orthogonal]
      intro d hd
      have hd' : A *ᵥ WithLp.ofLp d = 0 := by
        simpa only [LinearMap.mem_ker, Matrix.toEuclideanLin_apply, ← WithLp.toLp_zero 2,
          (WithLp.toLp_injective 2).eq_iff] using hd
      simpa [EuclideanSpace.inner_eq_star_dotProduct] using
        (dotProduct_comm r (WithLp.ofLp d)).trans (hzero (WithLp.ofLp d) hd')
    rw [LinearMap.orthogonal_ker, ← Matrix.toEuclideanLin_transpose_eq_adjoint] at horth
    obtain ⟨y, hy⟩ := horth
    refine ⟨hx, ⟨WithLp.ofLp y, ?_⟩, fun d hd ↦ ?_⟩
    · rw [Matrix.toEuclideanLin_apply, (WithLp.toLp_injective 2).eq_iff] at hy
      exact eq_add_of_sub_eq' hy.symm
    · have ht : f x ≤ f (x + (1 : ℝ) • d) := hmin (hfeas d hd 1)
      rw [hpoly, hzero d hd] at ht
      linarith
  · rintro ⟨hx, ⟨y, hy⟩, hpos⟩
    exact (quadratic_minimum_4_4_14 hH A hx hy hpos).1

private theorem weighted_projection_objective {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.PosDef)
    (x₀ z : EuclideanSpace ℝ (Fin n)) :
      (1 / 2 : ℝ) * energyNorm H.toEuclideanLin (x₀ - z) ^ 2 =
        ((1 / 2 : ℝ) * (WithLp.ofLp z ⬝ᵥ (H *ᵥ WithLp.ofLp z)) -
          WithLp.ofLp z ⬝ᵥ (H *ᵥ WithLp.ofLp x₀)) +
        (1 / 2 : ℝ) * (WithLp.ofLp x₀ ⬝ᵥ (H *ᵥ WithLp.ofLp x₀)) := by
  have hSym := Matrix.isHermitian_iff_isSymm.1 hH.isHermitian
  have hpsd (d : Fin n → ℝ) : 0 ≤ d ⬝ᵥ (H *ᵥ d) :=
    hH.posSemidef.dotProduct_mulVec_nonneg d
  have henergy (v : EuclideanSpace ℝ (Fin n)) :
      energyNorm H.toEuclideanLin v ^ 2 = WithLp.ofLp v ⬝ᵥ (H *ᵥ WithLp.ofLp v) := by
    have he : energyNorm H.toEuclideanLin v = √(WithLp.ofLp v ⬝ᵥ (H *ᵥ WithLp.ofLp v)) := by
      simp [energyNorm, EuclideanSpace.inner_eq_star_dotProduct, Matrix.toEuclideanLin_apply]
    rw [he, Real.sq_sqrt (hpsd _)]
  have hcross : WithLp.ofLp x₀ ⬝ᵥ (H *ᵥ WithLp.ofLp z) =
        WithLp.ofLp z ⬝ᵥ (H *ᵥ WithLp.ofLp x₀) := by
    conv_lhs => rw [← hSym.eq]
    exact Matrix.dotProduct_transpose_mulVec _ _ _
  rw [henergy]
  simp only [WithLp.ofLp_sub, mulVec_sub, dotProduct_sub, sub_dotProduct, hcross]
  ring

/-- **Equations (4.4.7)–(4.4.8)** of [conn2000trust]. Let $H \in \mathbb{R}^{n \times n}$ be
symmetric positive definite, $A \in \mathbb{R}^{m \times n}$, $x_0, x \in \mathbb{R}^n$,
$y \in \mathbb{R}^m$ and $b \in \mathbb{R}^m$. If
$$\begin{bmatrix} H & A^T \\ A & 0 \end{bmatrix} \begin{bmatrix} x \\ -y \end{bmatrix} =
  \begin{bmatrix} H x_0 \\ b \end{bmatrix},$$
then $x$ is the weighted projection of $x_0$ onto $\{z : Az = b\}$. -/
theorem weighted_projection_of_system_4_4_8 {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.PosDef)
    (A : Matrix (Fin m) (Fin n) ℝ) (x₀ x : EuclideanSpace ℝ (Fin n))
    (y : Fin m → ℝ) (b : EuclideanSpace ℝ (Fin m))
    (h : Matrix.saddleMatrix H Aᵀ 0 *ᵥ Sum.elim (WithLp.ofLp x) (-y) =
      Sum.elim (H *ᵥ WithLp.ofLp x₀) (WithLp.ofLp b)) :
    IsWeightedProjection H hH A b x₀ x := by
  obtain ⟨hs, hx⟩ := (projection_system_4_4_8 H A _ _ _ _).1 h
  have hSym : H.IsSymm := Matrix.isHermitian_iff_isSymm.1 hH.isHermitian
  have hpsd (d : Fin n → ℝ) : 0 ≤ d ⬝ᵥ (H *ᵥ d) := by
    simpa using hH.posSemidef.dotProduct_mulVec_nonneg d
  have hmin := (quadratic_minimum_4_4_14 hSym A hx hs (fun d _ => hpsd d)).1.2
  refine ⟨?_, fun z hz => ?_⟩
  · change A.toEuclideanLin x = b
    rw [Matrix.toEuclideanLin_apply, hx, WithLp.toLp_ofLp]
  · change A.toEuclideanLin z = b at hz
    have hz' : A *ᵥ WithLp.ofLp z = WithLp.ofLp b := by
      simpa only [Matrix.toEuclideanLin_apply, WithLp.ofLp_toLp] using congrArg WithLp.ofLp hz
    change (1 / 2 : ℝ) * energyNorm H.toEuclideanLin (x₀ - x) ^ 2 ≤
      (1 / 2 : ℝ) * energyNorm H.toEuclideanLin (x₀ - z) ^ 2
    rw [weighted_projection_objective hH, weighted_projection_objective hH]
    exact add_le_add_left (isMinOn_iff.mp hmin _ hz') _


/-- **Equations (4.4.7)–(4.4.8)** of [conn2000trust], characterization. Let
$H \in \mathbb{R}^{n \times n}$ be symmetric positive definite, $A \in \mathbb{R}^{m \times n}$,
$x_0, x \in \mathbb{R}^n$ and $b \in \mathbb{R}^m$. Then $x$ is the weighted projection of $x_0$
onto $\{z : Az = b\}$ if and only if there is $y \in \mathbb{R}^m$ with
$$\begin{bmatrix} H & A^T \\ A & 0 \end{bmatrix} \begin{bmatrix} x \\ -y \end{bmatrix} =
  \begin{bmatrix} H x_0 \\ b \end{bmatrix}.$$
-/
theorem weighted_projection_4_4_8_iff {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.PosDef)
    (A : Matrix (Fin m) (Fin n) ℝ) (x₀ x : EuclideanSpace ℝ (Fin n))
    (b : EuclideanSpace ℝ (Fin m)) :
    IsWeightedProjection H hH A b x₀ x ↔
      ∃ y : Fin m → ℝ, Matrix.saddleMatrix H Aᵀ 0 *ᵥ Sum.elim (WithLp.ofLp x) (-y) =
        Sum.elim (H *ᵥ WithLp.ofLp x₀) (WithLp.ofLp b) := by
  constructor
  · rintro ⟨hx, hmin⟩
    have hSym := Matrix.isHermitian_iff_isSymm.1 hH.isHermitian
    have hx' : A *ᵥ WithLp.ofLp x = WithLp.ofLp b := by
      simpa only [Matrix.toEuclideanLin_apply, WithLp.ofLp_toLp] using congrArg WithLp.ofLp hx
    have hquad : IsEqualityQuadraticMin H A (H *ᵥ WithLp.ofLp x₀) (WithLp.ofLp x)
        (WithLp.ofLp b) := by
      refine ⟨hx', fun z hz ↦ ?_⟩
      have hz' : A.toEuclideanLin (WithLp.toLp 2 z) = b := by
        rw [Matrix.toEuclideanLin_apply, WithLp.ofLp_toLp, show A *ᵥ z = WithLp.ofLp b from hz,
          WithLp.toLp_ofLp]
      have hle := hmin hz'
      change (1 / 2 : ℝ) * energyNorm H.toEuclideanLin (x₀ - x) ^ 2 ≤
        (1 / 2 : ℝ) * energyNorm H.toEuclideanLin (x₀ - WithLp.toLp 2 z) ^ 2 at hle
      rw [weighted_projection_objective hH, weighted_projection_objective hH,
        WithLp.ofLp_toLp, add_le_add_iff_right] at hle
      exact hle
    obtain ⟨_, ⟨y, hy⟩, _⟩ := (quadratic_minimum_4_4_14_iff hSym A _ _ _).mp hquad
    exact ⟨y, (projection_system_4_4_8 H A _ _ _ _).mpr ⟨hy, hx'⟩⟩
  · rintro ⟨y, hy⟩
    exact weighted_projection_of_system_4_4_8 hH A x₀ x y b hy

/-- **Equations (4.4.8)–(4.4.9)** of [conn2000trust], range-space method. Let
$H \in \mathbb{R}^{n \times n}$ be invertible, $A \in \mathbb{R}^{m \times n}$,
$x, g \in \mathbb{R}^n$ and $y, b \in \mathbb{R}^m$. Then
$$\begin{bmatrix} H & A^T \\ A & 0 \end{bmatrix} \begin{bmatrix} x \\ -y \end{bmatrix} =
  \begin{bmatrix} g \\ b \end{bmatrix}$$
if and only if
$$x = H^{-1}(g + A^T y) \quad \text{and} \quad A H^{-1} A^T y = b - A H^{-1} g.$$
-/
theorem projection_range_system_4_4_9 {H : Matrix (Fin n) (Fin n) ℝ} (hH : IsUnit H)
    (A : Matrix (Fin m) (Fin n) ℝ) (x g : Fin n → ℝ) (y b : Fin m → ℝ) :
    Matrix.saddleMatrix H Aᵀ 0 *ᵥ Sum.elim x (-y) = Sum.elim g b ↔
      x = H⁻¹ *ᵥ (g + Aᵀ *ᵥ y) ∧
        (A * H⁻¹ * Aᵀ) *ᵥ y = b - (A * H⁻¹) *ᵥ g := by
  rw [projection_system_4_4_8]
  have heq : H *ᵥ x = g + Aᵀ *ᵥ y ↔ x = H⁻¹ *ᵥ (g + Aᵀ *ᵥ y) := by
    constructor
    · intro h
      exact (Matrix.nonsing_inv_mulVec_eq hH h).symm
    · intro h
      rw [h, Matrix.mulVec_nonsing_inv_mulVec hH]
  rw [heq]
  refine and_congr_right fun hx ↦ ?_
  have hAx : A *ᵥ x = (A * H⁻¹) *ᵥ g + (A * H⁻¹ * Aᵀ) *ᵥ y := by
    rw [hx]
    simp only [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [hAx]
  exact ⟨fun h ↦ eq_sub_of_add_eq (by simpa [add_comm] using h),
    fun h ↦ by rw [h]; abel⟩

/-- **Section 4.4** of [conn2000trust], counterexample to uniqueness after (4.4.14). Let $n = 1$,
$m = 0$, $H = 0$ and $g = 0$, so that there are no constraints. Then $d^T H d \ge 0$ for all
$d$, and there are two distinct minimizers of $\frac{1}{2} z^T H z - z^T g$.

The witnesses are $x = 0$ and $z = 1$. -/
theorem semidefinite_reduced_quadratic_not_unique :
    let H : Matrix (Fin 1) (Fin 1) ℝ := 0
    let A : Matrix (Fin 0) (Fin 1) ℝ := 0
    (∀ d : Fin 1 → ℝ, 0 ≤ d ⬝ᵥ (H *ᵥ d)) ∧
      ∃ x z, x ≠ z ∧ IsEqualityQuadraticMin H A 0 x 0 ∧ IsEqualityQuadraticMin H A 0 z 0 := by
  dsimp only
  refine ⟨by simp, 0, fun _ => 1, ?_, ?_, ?_⟩
  · intro h
    have := congrFun h (0 : Fin 1)
    simp at this
  · exact ⟨by simp, fun _ _ => by simp⟩
  · exact ⟨by simp, fun _ _ => by simp⟩

end ConnGouldToint.Chapter04
