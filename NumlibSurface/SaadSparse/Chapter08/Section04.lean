/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Matrix.PosDef
import Numlib.Krylov.Subspace
import Numlib.Projection.OneDimensional
import Numlib.Projection.Optimality
import NumlibSurface.SaadSparse.Chapter04.Section02
import NumlibSurface.SaadSparse.Chapter08.Section01

/-!
# Saad, Section 8.4: Saddle-point problems

This module formalizes Section 8.4 of [saad2003iterative], together with Problems P-8.5(b), P-8.6,
P-8.7 and P-8.12. Let $A \in \mathbb{K}^{n \times n}$ be symmetric positive definite and
$B \in \mathbb{K}^{n \times m}$. The section studies the minimization of
$f(x) = \tfrac12 (Ax, x) - (x, b)$ under the constraint $B^H x = c$, and the block system (8.30)
$$\begin{bmatrix} A & B \\ B^H & 0 \end{bmatrix} \begin{bmatrix} x \\ y \end{bmatrix} =
  \begin{bmatrix} b \\ c \end{bmatrix}$$
that characterizes its solution, with the Lagrange multiplier $y$. The solution is the saddle point
of the Lagrangian $L(x, y) = f(x) + (y, B^H x - c)$. The proofs specialize the Galerkin
characterization of a minimizer in `Numlib.Projection.Optimality` and the saddle-point matrices of
`Numlib.LinearAlgebra.Matrix.SchurComplement`.

Eliminating $x = A^{-1}(b - By)$ leaves the reduced system $Sy = g$ with the Schur complement
$S = B^H A^{-1} B$ and $g = B^H A^{-1} b - c$. The matrix $S$ is symmetric positive definite when
$B$ has full column rank. Uzawa's method (Algorithm 8.6) is Richardson's iteration for $Sy = g$, so
its convergence is that of Example 4.1 applied to $S$ (Corollary 8.1). For $c = 0$ the reduced
system is the system of normal equations of $\min_y \|b - By\|_{A^{-1}}$. The module also states the
Arrow–Hurwicz method (Algorithm 8.7), the regularized Schur complement of Example 8.2, the projector
onto the constraint space of Problem P-8.6, and the indefinite saddle-point matrix of Problem
P-8.12, on which steepest descent and the minimal residual iteration stall.

## Main definitions

* Equation (8.30) and Example 8.2, `SaadSparse.Chapter08.saddleMatrix`: the block matrix
  $\begin{bmatrix} A & B \\ B^H & D \end{bmatrix}$.
* Equation (8.28), `SaadSparse.Chapter08.saddleObjective`: the objective
  $f(z) = \tfrac12 (Az, z) - (z, b)$.
* Equation (8.32) and Corollary 8.1, `SaadSparse.Chapter08.schur`: the Schur complement
  $S = B^H A^{-1} B$.
* Equation (8.32), `SaadSparse.Chapter08.schurRhs`: the reduced right-hand side
  $g = B^H A^{-1} b - c$.
* Algorithm 8.6, `SaadSparse.Chapter08.uzawa`: Uzawa's method.
* Algorithm 8.7, `SaadSparse.Chapter08.arrowHurwicz`: the Arrow–Hurwicz method.
* Example 8.2, `SaadSparse.Chapter08.regularizedSchur`: the regularized Schur complement
  $\rho B^H B - B^H A^{-1} B$.
* Section 8.4, `SaadSparse.Chapter08.lagrangian`: the Lagrangian $L(x, y) = f(x) + (y, B^H x - c)$.
* Problem P-8.6, `SaadSparse.Chapter08.constraintProjector`: the projector
  $P = I - B (B^H B)^{-1} B^H$.
* Problem P-8.12, `SaadSparse.Chapter08.blockVec`: the block vector $(u, v)$.

## Main results

* Equations (8.28)–(8.30), `SaadSparse.Chapter08.equation_8_30`: an admissible $x$ has a Lagrange
  multiplier if and only if it minimizes $f$ over the admissible set.
* Equation (8.30), `SaadSparse.Chapter08.equation_8_30_unique`: the Lagrange multiplier is unique
  when $B$ has full column rank.
* Equations (8.31)–(8.32), `SaadSparse.Chapter08.schur_eq`: with $x = A^{-1}(b - By)$, the block
  system holds if and only if $Sy = g$.
* Corollary 8.1, `SaadSparse.Chapter08.schur_posDef`: $S$ is positive definite when $A$ is and $B$
  has full column rank.
* Section 8.4, `SaadSparse.Chapter08.equation_8_32_isMinResidual`: for $c = 0$ the reduced system is
  the system of normal equations of $\min_y \|b - By\|_{A^{-1}}$.
* Equations (8.31)–(8.32), `SaadSparse.Chapter08.equation_8_32`: the $y$-update of Uzawa's method is
  Richardson's iteration for $Sy = g$.
* Problem P-8.7, `SaadSparse.Chapter08.uzawa_eq_splitting`: Uzawa's method is the iteration of a
  splitting of the block system.
* Section 8.4, `SaadSparse.Chapter08.arrowHurwicz_eq_block`: the block form of the Arrow–Hurwicz
  method.
* Example 8.2, `SaadSparse.Chapter08.example_8_2`: the regularized Schur complement is symmetric,
  positive definite for large $\rho$ and negative definite for small $\rho$.
* Corollary 8.1, `SaadSparse.Chapter08.corollary_8_1`: $S$ is positive definite, and Richardson's
  iteration for $S$ converges exactly when $0 < \omega < 2/\lambda_{\max}(S)$, with optimal
  parameter $2/(\lambda_{\min}(S) + \lambda_{\max}(S))$.
* Section 8.4, `SaadSparse.Chapter08.lagrangian_isSaddle`: the solution of (8.30) is a saddle point
  of the Lagrangian.
* Problem P-8.6(a), `SaadSparse.Chapter08.problem_8_6_projector`: $P$ is the orthogonal projector
  onto $\operatorname{Ker} B^H$.
* Problem P-8.6(b) and Equation (8.35), `SaadSparse.Chapter08.equation_8_35`: for $c = 0$ the block
  system is equivalent to $PAPx = Pb$ for admissible $x$.
* Problem P-8.6(c), `SaadSparse.Chapter08.conjTranspose_mul_constraintProjector`: $B^H P = 0$.
* Problem P-8.6(c), `SaadSparse.Chapter08.problem_8_6_cg_subspace`: the Krylov subspaces of $PAP$
  from $Pb$ lie in $\operatorname{Ker} B^H$.
* Problem P-8.5(b), `SaadSparse.Chapter08.problem_8_5b`: a solution of the reduced system gives a
  solution of the block system.
* Problem P-8.12, `SaadSparse.Chapter08.saddleMatrix_apply_blockVec`: the saddle-point matrix acts
  on block vectors blockwise.
* Problem P-8.12, `SaadSparse.Chapter08.inner_blockVec`: the inner product of block vectors is the
  sum of the block inner products.
* Problem P-8.12(1), `SaadSparse.Chapter08.problem_8_12_pos`: the quadratic form of the saddle-point
  matrix is positive on $(u, 0)$ for $u \neq 0$.
* Problem P-8.12(1), `SaadSparse.Chapter08.problem_8_12_neg`: the quadratic form is negative on
  $(-A^{-1} B p, p)$ for $p \neq 0$.
* Problem P-8.12(1), `SaadSparse.Chapter08.problem_8_12_indefinite`: the saddle-point matrix has a
  positive and a negative eigenvalue.
* Problem P-8.12(2)–(3), `SaadSparse.Chapter08.inner_saddleMatrix_blockVec_zero`: the quadratic form
  vanishes on every vector $(0, s)$.
* Problem P-8.12(2), `SaadSparse.Chapter08.problem_8_12_residual`: the initial guess $(u_0, 0)$ with
  $Au_0 = f$ has a residual of the form $(0, s_0)$.
* Problem P-8.12(2), `SaadSparse.Chapter08.problem_8_12_steepestDescent_stalls`: steepest descent
  from this initial guess does not move.
* Problem P-8.12(3), `SaadSparse.Chapter08.problem_8_12_minRes_stalls`: the minimal residual
  iteration from this initial guess does not move.
* Problem P-8.12(5), `SaadSparse.Chapter08.problem_8_12_reduced`: the iteration of part (5) is
  steepest descent for the reduced system.

## Conventions

* The scalar field $\mathbb{K}$ is $\mathbb{R}$ or $\mathbb{C}$ (`[RCLike 𝕜]`); Corollary 8.1 is
  stated over $\mathbb{R}$. Vectors are in `EuclideanSpace 𝕜 (Fin n)`, and a matrix acts on a vector
  by `Matrix.toEuclideanLin`, written `A ⬝ x`.
* Mathlib's `inner 𝕜 u v` is the inner product $(v, u)$ of the book. Real-valued quantities such as
  $f$ and $L$ use the real parts of inner products.
* "Symmetric positive definite" is `Matrix.PosDef`, and "$B$ has full column rank" is the
  injectivity of `Matrix.toEuclideanLin B`. "Nonsingular" is `IsUnit`.

## Implementation notes

* Block matrices are indexed by `Fin n ⊕ Fin m`. A block vector $(x, y)$ is
  `Sum.elim (WithLp.ofLp x) (WithLp.ofLp y)` in plain coordinates, or
  `SaadSparse.Chapter08.blockVec x y` in `EuclideanSpace 𝕜 (Fin n ⊕ Fin m)`.
* A state of Uzawa's method or of the Arrow–Hurwicz method is a pair $(x_k, y_k)$.
* Division by zero is $0$ in Lean, and the inverse of a singular matrix is $0$. This makes the
  stalled steps of Problem P-8.12 the identity.

## Not formalized

* **Problem P-8.6(c)**, the convergence of the conjugate gradient method applied to $PAPx = Pb$. It
  needs a theorem on the conjugate gradient method for a consistent symmetric positive semidefinite
  system, which the backbone does not have; `Numlib.Krylov.Singular` treats only minimal residual
  methods. The question of the subspace in which the iterates lie is answered by
  `SaadSparse.Chapter08.problem_8_6_cg_subspace`.
* **Problem P-8.6(d)**. It needs a QR factorization of a rectangular $B$.
* **Problem P-8.9** (inexact Uzawa). It needs a theorem on perturbed fixed-point iterations.
-/

open Matrix Filter Topology

open scoped Matrix SaadSparse ComplexOrder

namespace SaadSparse.Chapter08

variable {n m : ℕ} {𝕜 : Type*} [RCLike 𝕜]

/-! ### Moving $B$ across the inner product -/

/-- For $B \in \mathbb{K}^{n \times m}$, $u \in \mathbb{K}^m$ and $w \in \mathbb{K}^n$,
$(w, Bu) = (B^H w, u)$. This is the companion of `SaadSparse.Chapter08.inner_conjTranspose` with
the rectangular matrix on the other side. -/
theorem inner_mul_conjTranspose (B : Matrix (Fin n) (Fin m) 𝕜) (u : EuclideanSpace 𝕜 (Fin m))
    (w : EuclideanSpace 𝕜 (Fin n)) : inner 𝕜 (B ⬝ u) w = inner 𝕜 u (Bᴴ ⬝ w) := by
  have h := inner_conjTranspose Bᴴ u w
  rwa [Matrix.conjTranspose_conjTranspose] at h

/-- For $B \in \mathbb{K}^{n \times m}$, $(\operatorname{Ran} B)^\perp = \operatorname{Ker} B^H$:
the constraint space of (8.29) is the orthogonal complement of the range of $B$. -/
theorem orthogonal_range_eq_ker (B : Matrix (Fin n) (Fin m) 𝕜) :
    (LinearMap.range (Matrix.toEuclideanLin B))ᗮ = LinearMap.ker (Matrix.toEuclideanLin Bᴴ) := by
  ext z
  simp only [LinearMap.mem_ker]
  constructor
  · intro hz
    have h : ∀ w, inner 𝕜 (Bᴴ ⬝ z) w = (0 : 𝕜) := by
      intro w
      rw [inner_conjTranspose]
      exact inner_eq_zero_symm.1 (hz _ ⟨w, rfl⟩)
    exact inner_self_eq_zero.1 (h (Bᴴ ⬝ z))
  · rintro hz _ ⟨w, rfl⟩
    rw [show (Matrix.toEuclideanLin B) w = (B ⬝ w) from rfl, inner_mul_conjTranspose, hz,
      inner_zero_right]

/-- For $B \in \mathbb{K}^{n \times m}$, $(\operatorname{Ker} B^H)^\perp = \operatorname{Ran} B$.
This is the form that (8.30) needs: a vector orthogonal to every admissible direction is $By$
for some $y$, and that $y$ is the Lagrange multiplier. -/
theorem orthogonal_ker_eq_range (B : Matrix (Fin n) (Fin m) 𝕜) :
    (LinearMap.ker (Matrix.toEuclideanLin Bᴴ))ᗮ = LinearMap.range (Matrix.toEuclideanLin B) := by
  rw [← orthogonal_range_eq_ker, Submodule.orthogonal_orthogonal]

/-! ### (8.30): the block system -/

/-- **Equation (8.30)** and **Example 8.2** of [saad2003iterative]. For
$A \in \mathbb{K}^{n \times n}$, $B \in \mathbb{K}^{n \times m}$ and
$D \in \mathbb{K}^{m \times m}$, the **saddle-point block matrix** is
$$\begin{bmatrix} A & B \\ B^H & D \end{bmatrix} \in \mathbb{K}^{(n + m) \times (n + m)}.$$
The block system of Section 8.4 has $D = 0$, and the regularized system of Example 8.2 has
$D = \rho C$.

The definition is the backbone `Matrix.saddleMatrix`, with rows and columns indexed by
`Fin n ⊕ Fin m`. -/
def saddleMatrix (A : Matrix (Fin n) (Fin n) 𝕜) (B : Matrix (Fin n) (Fin m) 𝕜)
    (D : Matrix (Fin m) (Fin m) 𝕜) : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) 𝕜 :=
  Matrix.saddleMatrix A B D

private theorem ofLp_eq_add_iff {k : ℕ} (x y z : EuclideanSpace 𝕜 (Fin k)) :
    WithLp.ofLp x = WithLp.ofLp y + WithLp.ofLp z ↔ x = y + z := by
  rw [← WithLp.ofLp_add]
  exact (WithLp.ofLp_injective 2).eq_iff

private theorem fromBlocks_mulVec_elim (M₁ : Matrix (Fin n) (Fin n) 𝕜)
    (M₂ : Matrix (Fin n) (Fin m) 𝕜) (M₃ : Matrix (Fin m) (Fin n) 𝕜)
    (M₄ : Matrix (Fin m) (Fin m) 𝕜) (u : EuclideanSpace 𝕜 (Fin n))
    (v : EuclideanSpace 𝕜 (Fin m)) :
    Matrix.fromBlocks M₁ M₂ M₃ M₄ *ᵥ Sum.elim (WithLp.ofLp u) (WithLp.ofLp v)
      = Sum.elim (WithLp.ofLp ((M₁ ⬝ u) + (M₂ ⬝ v))) (WithLp.ofLp ((M₃ ⬝ u) + (M₄ ⬝ v))) := by
  rw [Matrix.fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr, WithLp.ofLp_add,
    WithLp.ofLp_add]
  rfl

/-- **Equation (8.30)** of [saad2003iterative], written out. For $A, B, D$ as in
`SaadSparse.Chapter08.saddleMatrix` and vectors $x, b \in \mathbb{K}^n$,
$y, c \in \mathbb{K}^m$, the pair $(x, y)$ solves the block system with right-hand side $(b, c)$
if and only if
$$Ax + By = b \quad \text{and} \quad B^H x + Dy = c.$$
The proof is the backbone `Matrix.saddleMatrix_mulVec_elim`. -/
theorem saddleMatrix_mulVec_iff (A : Matrix (Fin n) (Fin n) 𝕜) (B : Matrix (Fin n) (Fin m) 𝕜)
    (D : Matrix (Fin m) (Fin m) 𝕜) (x b : EuclideanSpace 𝕜 (Fin n))
    (y c : EuclideanSpace 𝕜 (Fin m)) :
    saddleMatrix A B D *ᵥ Sum.elim (WithLp.ofLp x) (WithLp.ofLp y)
        = Sum.elim (WithLp.ofLp b) (WithLp.ofLp c) ↔
      ((A ⬝ x) + (B ⬝ y) = b ∧ (Bᴴ ⬝ x) + (D ⬝ y) = c) := by
  rw [saddleMatrix, Matrix.saddleMatrix_mulVec_elim]
  exact and_congr (WithLp.ofLp_injective 2).eq_iff (WithLp.ofLp_injective 2).eq_iff

/-- A block identity $M z' = N z + p$, for $2 \times 2$ block matrices $M$ and $N$, holds if and
only if it holds in each of the two block rows. -/
private theorem fromBlocks_elim_eq_iff
    (M₁ N₁ : Matrix (Fin n) (Fin n) 𝕜) (M₂ N₂ : Matrix (Fin n) (Fin m) 𝕜)
    (M₃ N₃ : Matrix (Fin m) (Fin n) 𝕜) (M₄ N₄ : Matrix (Fin m) (Fin m) 𝕜)
    (u u' p : EuclideanSpace 𝕜 (Fin n)) (v v' q : EuclideanSpace 𝕜 (Fin m)) :
    Matrix.fromBlocks M₁ M₂ M₃ M₄ *ᵥ Sum.elim (WithLp.ofLp u') (WithLp.ofLp v')
        = Matrix.fromBlocks N₁ N₂ N₃ N₄ *ᵥ Sum.elim (WithLp.ofLp u) (WithLp.ofLp v)
          + Sum.elim (WithLp.ofLp p) (WithLp.ofLp q) ↔
      ((M₁ ⬝ u') + (M₂ ⬝ v') = (N₁ ⬝ u) + (N₂ ⬝ v) + p ∧
        (M₃ ⬝ u') + (M₄ ⬝ v') = (N₃ ⬝ u) + (N₄ ⬝ v) + q) := by
  rw [fromBlocks_mulVec_elim, fromBlocks_mulVec_elim, ← Sum.elim_add_add, Sum.elim_eq_iff]
  exact and_congr (ofLp_eq_add_iff _ _ _) (ofLp_eq_add_iff _ _ _)

/-! ### Equations (8.28)–(8.30): the constrained minimization problem -/

/-- **Equation (8.28)** of [saad2003iterative]. For $A \in \mathbb{K}^{n \times n}$ and
$b \in \mathbb{K}^n$, the **quadratic objective** is the real-valued function
$$f(z) = \tfrac12 \operatorname{Re} (Az, z) - \operatorname{Re} (z, b).$$
The saddle-point system minimizes $f$ under the constraint $B^H z = c$.

Over $\mathbb{R}$ this is $\tfrac12 (Az, z) - (z, b)$. Over $\mathbb{C}$ the real parts make $f$
real-valued. -/
noncomputable def saddleObjective (A : Matrix (Fin n) (Fin n) 𝕜)
    (b z : EuclideanSpace 𝕜 (Fin n)) : ℝ :=
  RCLike.re (inner 𝕜 (A ⬝ z) z) / 2 - RCLike.re (inner 𝕜 b z)

section Objective

variable {A : Matrix (Fin n) (Fin n) 𝕜} {b : EuclideanSpace 𝕜 (Fin n)}

/-- For symmetric positive definite $A$ and $Ax_* = b$, $f(z) = \tfrac12 \|x_* - z\|_A^2 - \tfrac12
\operatorname{Re}(x_*, b)$: up to an additive constant, $f$ is half the squared energy norm of
the error. -/
private theorem saddleObjective_eq (hA : A.PosDef) {xstar : EuclideanSpace 𝕜 (Fin n)}
    (hstar : (A ⬝ xstar) = b) (z : EuclideanSpace 𝕜 (Fin n)) :
    saddleObjective A b z = energyNorm (Matrix.toEuclideanLin A) (xstar - z) ^ 2 / 2
      - RCLike.re (inner 𝕜 b xstar) / 2 := by
  have hsc := (Matrix.posDef_iff_isSymmetricCoercive A).1 hA
  have hsym : inner 𝕜 (A ⬝ z) xstar = inner 𝕜 z b := by
    rw [show inner 𝕜 (A ⬝ z) xstar = inner 𝕜 ((Matrix.toEuclideanLin A) z) xstar from rfl,
      hsc.isSymmetric z xstar, hstar]
  have hre : RCLike.re (inner 𝕜 z b) = RCLike.re (inner 𝕜 b z) := by
    rw [← inner_conj_symm]
    exact RCLike.conj_re _
  rw [hsc.energyNorm_sq, saddleObjective,
    show (Matrix.toEuclideanLin A) (xstar - z) = (A ⬝ xstar) - (A ⬝ z) from map_sub _ _ _,
    hstar, inner_sub_left, inner_sub_right, inner_sub_right, hsym]
  simp only [map_sub]
  rw [hre]
  ring

/-- Let $A \in \mathbb{K}^{n \times n}$ be symmetric positive definite, $b \in \mathbb{K}^n$, $K$ a
finite-dimensional subspace and $x_0, x \in \mathbb{K}^n$. Then $x$ is the Galerkin
approximation from $x_0 + K$ for $Ax = b$ (`IsGalerkin`) if and only if $x - x_0 \in K$ and
$f(x) \le f(z)$ for every $z$ with $z - x_0 \in K$.

The proof is `IsGalerkin.iff_energyNorm_min`, read through the energy-norm form of $f$. -/
theorem isGalerkin_iff_saddleObjective_min (hA : A.PosDef)
    {K : Submodule 𝕜 (EuclideanSpace 𝕜 (Fin n))} [FiniteDimensional 𝕜 K]
    (x₀ x : EuclideanSpace 𝕜 (Fin n)) :
    IsGalerkin (Matrix.toEuclideanLin A) b x₀ K x ↔
      x - x₀ ∈ K ∧ ∀ z, z - x₀ ∈ K → saddleObjective A b x ≤ saddleObjective A b z := by
  have hsc := (Matrix.posDef_iff_isSymmetricCoercive A).1 hA
  have hstar : (A ⬝ (A⁻¹ ⬝ b)) = b := toEuclideanLin_mul_nonsing_inv_apply hA.isUnit b
  have hx0 := energyNorm_nonneg (Matrix.toEuclideanLin A) ((A⁻¹ ⬝ b) - x)
  rw [IsGalerkin.iff_energyNorm_min hsc hstar]
  refine and_congr_right fun _ => ?_
  constructor
  · intro h z hz
    have hz' := h z hz
    have hz0 := energyNorm_nonneg (Matrix.toEuclideanLin A) ((A⁻¹ ⬝ b) - z)
    rw [saddleObjective_eq hA hstar, saddleObjective_eq hA hstar]
    nlinarith
  · intro h z hz
    have hz' := h z hz
    have hz0 := energyNorm_nonneg (Matrix.toEuclideanLin A) ((A⁻¹ ⬝ b) - z)
    rw [saddleObjective_eq hA hstar, saddleObjective_eq hA hstar] at hz'
    nlinarith

end Objective

/-- **Equations (8.28)–(8.30)** of [saad2003iterative], the Karush–Kuhn–Tucker conditions. Let
$A \in \mathbb{K}^{n \times n}$ be symmetric positive definite, $B \in \mathbb{K}^{n \times m}$,
$b \in \mathbb{K}^n$ and $c \in \mathbb{K}^m$, and let $x \in \mathbb{K}^n$ be admissible,
$B^H x = c$. Then there is a Lagrange multiplier $y \in \mathbb{K}^m$ with
$$Ax + By = b,$$
that is, a $y$ such that $(x, y)$ solves the block system (8.30), if and only if $f(x) \le f(z)$
for every $z$ with $B^H z = c$.

The multiplier is unique when $B$ has full column rank
(`SaadSparse.Chapter08.equation_8_30_unique`). Both directions are the Galerkin characterization
of the minimizer over the affine space $x + \operatorname{Ker} B^H$, whose orthogonal complement
is $\operatorname{Ran} B$; this is where the multiplier comes from. -/
theorem equation_8_30 {A : Matrix (Fin n) (Fin n) 𝕜} (hA : A.PosDef)
    (B : Matrix (Fin n) (Fin m) 𝕜) (b : EuclideanSpace 𝕜 (Fin n))
    (c : EuclideanSpace 𝕜 (Fin m)) (x : EuclideanSpace 𝕜 (Fin n)) (hx : (Bᴴ ⬝ x) = c) :
    (∃ y, (A ⬝ x) + (B ⬝ y) = b) ↔
      ∀ z, (Bᴴ ⬝ z) = c → saddleObjective A b x ≤ saddleObjective A b z := by
  have hmem : ∀ z : EuclideanSpace 𝕜 (Fin n),
      z - x ∈ LinearMap.ker (Matrix.toEuclideanLin Bᴴ) ↔ (Bᴴ ⬝ z) = c := by
    intro z
    rw [LinearMap.mem_ker,
      show (Matrix.toEuclideanLin Bᴴ) (z - x) = (Bᴴ ⬝ z) - (Bᴴ ⬝ x) from map_sub _ _ _, hx,
      sub_eq_zero]
  have hgal : IsGalerkin (Matrix.toEuclideanLin A) b x
      (LinearMap.ker (Matrix.toEuclideanLin Bᴴ)) x ↔ ∃ y, (A ⬝ x) + (B ⬝ y) = b := by
    constructor
    · intro h
      have h2 := h.orth
      rw [orthogonal_ker_eq_range B] at h2
      obtain ⟨y, hy⟩ := h2
      refine ⟨y, ?_⟩
      rw [show (Matrix.toEuclideanLin B) y = (B ⬝ y) from rfl] at hy
      rw [hy]
      abel
    · rintro ⟨y, hy⟩
      refine ⟨by rw [sub_self]; exact Submodule.zero_mem _, ?_⟩
      rw [orthogonal_ker_eq_range B]
      exact ⟨y, by rw [show (Matrix.toEuclideanLin B) y = (B ⬝ y) from rfl, ← hy]; abel⟩
  rw [← hgal, isGalerkin_iff_saddleObjective_min hA x x]
  simp only [hmem]
  exact ⟨fun h => h.2, fun h => ⟨hx, h⟩⟩

/-- **Equation (8.30)** of [saad2003iterative], uniqueness of the multiplier. Let
$B \in \mathbb{K}^{n \times m}$ have full column rank, and let $A \in \mathbb{K}^{n \times n}$,
$b, x \in \mathbb{K}^n$ and $y, y' \in \mathbb{K}^m$. If $Ax + By = b$ and $Ax + By' = b$, then
$y = y'$. -/
theorem equation_8_30_unique {B : Matrix (Fin n) (Fin m) 𝕜}
    (hB : Function.Injective (Matrix.toEuclideanLin B)) {A : Matrix (Fin n) (Fin n) 𝕜}
    {b x : EuclideanSpace 𝕜 (Fin n)} {y y' : EuclideanSpace 𝕜 (Fin m)}
    (hy : (A ⬝ x) + (B ⬝ y) = b) (hy' : (A ⬝ x) + (B ⬝ y') = b) : y = y' :=
  hB (by rw [show (Matrix.toEuclideanLin B) y = (B ⬝ y) from rfl,
    show (Matrix.toEuclideanLin B) y' = (B ⬝ y') from rfl, ← add_right_inj (A ⬝ x), hy, hy'])

/-! ### Equations (8.31)–(8.32): the Schur complement -/

/-- **Equation (8.32)** and **Corollary 8.1** of [saad2003iterative]. For
$A \in \mathbb{K}^{n \times n}$ and $B \in \mathbb{K}^{n \times m}$, the **Schur complement** of
the block system (8.30) is
$$S = B^H A^{-1} B \in \mathbb{K}^{m \times m}.$$
It is the coefficient matrix of the system that remains after eliminating $x$. -/
noncomputable def schur (A : Matrix (Fin n) (Fin n) 𝕜) (B : Matrix (Fin n) (Fin m) 𝕜) :
    Matrix (Fin m) (Fin m) 𝕜 :=
  Bᴴ * A⁻¹ * B

/-- **Equation (8.32)** of [saad2003iterative]. For $A \in \mathbb{K}^{n \times n}$,
$B \in \mathbb{K}^{n \times m}$, $b \in \mathbb{K}^n$ and $c \in \mathbb{K}^m$, the **reduced
right-hand side** is
$$g = B^H A^{-1} b - c.$$
-/
noncomputable def schurRhs (A : Matrix (Fin n) (Fin n) 𝕜) (B : Matrix (Fin n) (Fin m) 𝕜)
    (b : EuclideanSpace 𝕜 (Fin n)) (c : EuclideanSpace 𝕜 (Fin m)) :
    EuclideanSpace 𝕜 (Fin m) :=
  ((Bᴴ * A⁻¹) ⬝ b) - c

variable {A : Matrix (Fin n) (Fin n) 𝕜} {B : Matrix (Fin n) (Fin m) 𝕜}

/-- The Schur complement acts as $Sy = B^H (A^{-1} (By))$. -/
theorem schur_apply (y : EuclideanSpace 𝕜 (Fin m)) :
    (schur A B ⬝ y) = (Bᴴ ⬝ (A⁻¹ ⬝ (B ⬝ y))) := by
  rw [schur, Matrix.toEuclideanLin_mul_apply, Matrix.toEuclideanLin_mul_apply]

private theorem conjTranspose_inv_sub (b : EuclideanSpace 𝕜 (Fin n))
    (y : EuclideanSpace 𝕜 (Fin m)) :
    (Bᴴ ⬝ (A⁻¹ ⬝ (b - (B ⬝ y)))) = ((Bᴴ * A⁻¹) ⬝ b) - (schur A B ⬝ y) := by
  rw [schur_apply, Matrix.toEuclideanLin_mul_apply,
    show (Matrix.toEuclideanLin A⁻¹) (b - (B ⬝ y)) = (A⁻¹ ⬝ b) - (A⁻¹ ⬝ (B ⬝ y)) from
      map_sub _ _ _,
    show (Matrix.toEuclideanLin Bᴴ) ((A⁻¹ ⬝ b) - (A⁻¹ ⬝ (B ⬝ y)))
      = (Bᴴ ⬝ (A⁻¹ ⬝ b)) - (Bᴴ ⬝ (A⁻¹ ⬝ (B ⬝ y))) from map_sub _ _ _]

/-- **Equations (8.31)–(8.32)** of [saad2003iterative]. Let $A \in \mathbb{K}^{n \times n}$ be
nonsingular, $B \in \mathbb{K}^{n \times m}$, $b \in \mathbb{K}^n$ and $c, y \in \mathbb{K}^m$,
and let $x = A^{-1}(b - By)$. Then
$$Sy = g \iff \bigl(Ax + By = b \text{ and } B^H x = c\bigr).$$
So with this $x$ the first block equation holds, and the second one is the reduced system
$Sy = g$. -/
theorem schur_eq (hA : IsUnit A) (b : EuclideanSpace 𝕜 (Fin n)) (c y : EuclideanSpace 𝕜 (Fin m))
    {x : EuclideanSpace 𝕜 (Fin n)} (hx : x = (A⁻¹ ⬝ (b - (B ⬝ y)))) :
    (schur A B ⬝ y) = schurRhs A B b c ↔ ((A ⬝ x) + (B ⬝ y) = b ∧ (Bᴴ ⬝ x) = c) := by
  have h1 : (A ⬝ x) + (B ⬝ y) = b := by
    rw [hx, toEuclideanLin_mul_nonsing_inv_apply hA]
    abel
  have h2 : (Bᴴ ⬝ x) = ((Bᴴ * A⁻¹) ⬝ b) - (schur A B ⬝ y) := by
    rw [hx, conjTranspose_inv_sub]
  rw [schurRhs]
  refine ⟨fun h => ⟨h1, ?_⟩, fun h => ?_⟩
  · rw [h2, h]
    abel
  · have h3 := h.2
    rw [h2] at h3
    rw [← h3]
    abel

/-- **Corollary 8.1** of [saad2003iterative], positive definiteness of $S$. Let
$A \in \mathbb{K}^{n \times n}$ be symmetric positive definite and let
$B \in \mathbb{K}^{n \times m}$ have full column rank. Then the Schur complement
$S = B^H A^{-1} B$ is symmetric positive definite.

The proof is the backbone `Matrix.PosDef.conjTranspose_mul_inv_mul`. -/
theorem schur_posDef (hA : A.PosDef) (hB : Function.Injective (Matrix.toEuclideanLin B)) :
    (schur A B).PosDef :=
  hA.conjTranspose_mul_inv_mul fun x y hxy =>
    (WithLp.toLp_injective 2) (hB (a₁ := WithLp.toLp 2 x) (a₂ := WithLp.toLp 2 y)
      (WithLp.ofLp_injective 2 hxy))

/-- **Section 8.4** of [saad2003iterative], the reduced system as normal equations. Let
$A \in \mathbb{K}^{n \times n}$ be symmetric positive definite, $B \in \mathbb{K}^{n \times m}$,
$b \in \mathbb{K}^n$ and $y \in \mathbb{K}^m$. Then $Sy = B^H A^{-1} b$ if and only if
$$\|b - By\|_{A^{-1}} \le \|b - z\|_{A^{-1}} \quad \text{for all } z \in \operatorname{Ran} B.$$
So for $c = 0$ the reduced system is the system of normal equations of the least-squares problem
$\min_y \|b - By\|_{A^{-1}}$ in the $A^{-1}$ inner product. This is the reason of the book why
the preconditioners of the section for the Stokes problem work.

The norm $\|v\|_{A^{-1}} = \sqrt{\operatorname{Re}(A^{-1} v, v)}$ is `energyNorm`. -/
theorem equation_8_32_isMinResidual (hA : A.PosDef) (b : EuclideanSpace 𝕜 (Fin n))
    (y : EuclideanSpace 𝕜 (Fin m)) :
    (schur A B ⬝ y) = ((Bᴴ * A⁻¹) ⬝ b) ↔
      ∀ z ∈ LinearMap.range (Matrix.toEuclideanLin B),
        energyNorm (Matrix.toEuclideanLin A⁻¹) (b - (B ⬝ y))
          ≤ energyNorm (Matrix.toEuclideanLin A⁻¹) (b - z) := by
  have hAinv := (Matrix.posDef_iff_isSymmetricCoercive A⁻¹).1 hA.inv
  have hmem : (B ⬝ y) ∈ LinearMap.range (Matrix.toEuclideanLin B) :=
    LinearMap.mem_range_self (Matrix.toEuclideanLin B) y
  have hres : (A⁻¹ ⬝ b) - (Matrix.toEuclideanLin A⁻¹) (B ⬝ y)
      = (Matrix.toEuclideanLin A⁻¹) (b - (B ⬝ y)) := (map_sub _ _ _).symm
  have hgal : IsGalerkin (Matrix.toEuclideanLin A⁻¹) (A⁻¹ ⬝ b) 0
      (LinearMap.range (Matrix.toEuclideanLin B)) (B ⬝ y)
      ↔ (schur A B ⬝ y) = ((Bᴴ * A⁻¹) ⬝ b) := by
    constructor
    · intro h
      have h2 := h.orth
      rw [hres, orthogonal_range_eq_ker, LinearMap.mem_ker,
        show (Matrix.toEuclideanLin Bᴴ) ((Matrix.toEuclideanLin A⁻¹) (b - (B ⬝ y)))
          = (Bᴴ ⬝ (A⁻¹ ⬝ (b - (B ⬝ y)))) from rfl, conjTranspose_inv_sub, sub_eq_zero] at h2
      exact h2.symm
    · intro h
      refine ⟨by rw [sub_zero]; exact hmem, ?_⟩
      rw [hres, orthogonal_range_eq_ker, LinearMap.mem_ker,
        show (Matrix.toEuclideanLin Bᴴ) ((Matrix.toEuclideanLin A⁻¹) (b - (B ⬝ y)))
          = (Bᴴ ⬝ (A⁻¹ ⬝ (b - (B ⬝ y)))) from rfl, conjTranspose_inv_sub, h, sub_self]
  rw [← hgal, IsGalerkin.iff_energyNorm_min hAinv (rfl : (A⁻¹ ⬝ b) = (A⁻¹ ⬝ b))]
  simp only [sub_zero]
  exact ⟨fun h z hz => h.2 z hz, fun h => ⟨hmem, fun z hz => h z hz⟩⟩

/-! ### Algorithm 8.6: Uzawa's method -/

section Uzawa

variable (A B) (b : EuclideanSpace 𝕜 (Fin n)) (c : EuclideanSpace 𝕜 (Fin m)) (ω : 𝕜)

/-- One pass through Algorithm 8.6 of [saad2003iterative] (Uzawa's method): the pair $(x_k, y_k)$
goes to $(x_{k+1}, y_{k+1})$ with
$$x_{k+1} = A^{-1}(b - By_k), \qquad y_{k+1} = y_k + \omega (B^H x_{k+1} - c).$$
-/
noncomputable def uzawaStep (s : EuclideanSpace 𝕜 (Fin n) × EuclideanSpace 𝕜 (Fin m)) :
    EuclideanSpace 𝕜 (Fin n) × EuclideanSpace 𝕜 (Fin m) :=
  (A⁻¹ ⬝ (b - (B ⬝ s.2)), s.2 + ω • ((Bᴴ ⬝ (A⁻¹ ⬝ (b - (B ⬝ s.2)))) - c))

/-- **Algorithm 8.6** of [saad2003iterative] (Uzawa's method). Let $A \in \mathbb{K}^{n \times n}$,
$B \in \mathbb{K}^{n \times m}$, $b \in \mathbb{K}^n$, $c \in \mathbb{K}^m$ and
$\omega \in \mathbb{K}$. From a starting pair $(x_0, y_0)$, the state after $k$ steps is
obtained by $k$ passes of
$$x_{j+1} = A^{-1}(b - By_j), \qquad y_{j+1} = y_j + \omega (B^H x_{j+1} - c).$$

A pass is `SaadSparse.Chapter08.uzawaStep`. The starting $x_0$ is not used. -/
noncomputable def uzawa (s₀ : EuclideanSpace 𝕜 (Fin n) × EuclideanSpace 𝕜 (Fin m)) (k : ℕ) :
    EuclideanSpace 𝕜 (Fin n) × EuclideanSpace 𝕜 (Fin m) :=
  (uzawaStep A B b c ω)^[k] s₀

/-- The state of Algorithm 8.6 after $k + 1$ steps is one pass of the algorithm applied to the state
after $k$ steps. -/
theorem uzawa_succ (s₀ : EuclideanSpace 𝕜 (Fin n) × EuclideanSpace 𝕜 (Fin m)) (k : ℕ) :
    uzawa A B b c ω s₀ (k + 1) = uzawaStep A B b c ω (uzawa A B b c ω s₀ k) :=
  Function.iterate_succ_apply' _ _ _

variable {A B b c ω}

/-- **Equations (8.31)–(8.32)** of [saad2003iterative], Uzawa's method on the reduced system. For
$A \in \mathbb{K}^{n \times n}$, $B \in \mathbb{K}^{n \times m}$, $b \in \mathbb{K}^n$,
$c \in \mathbb{K}^m$, $\omega \in \mathbb{K}$ and every pair $(x_k, y_k)$, the $y$-update of one
pass of Algorithm 8.6 is
$$y_{k+1} = y_k + \omega (g - Sy_k).$$
So eliminating $x$ from Uzawa's method leaves Richardson's iteration for the reduced system
$Sy = g$. -/
theorem equation_8_32 (s : EuclideanSpace 𝕜 (Fin n) × EuclideanSpace 𝕜 (Fin m)) :
    (uzawaStep A B b c ω s).2 = s.2 + ω • (schurRhs A B b c - (schur A B ⬝ s.2)) := by
  have h : (Bᴴ ⬝ (A⁻¹ ⬝ (b - (B ⬝ s.2)))) - c = schurRhs A B b c - (schur A B ⬝ s.2) := by
    rw [conjTranspose_inv_sub, schurRhs]
    abel
  rw [uzawaStep, h]

/-- **Problem P-8.7** of [saad2003iterative]. Let $A \in \mathbb{K}^{n \times n}$ be nonsingular,
and let $B$, $b$, $c$ and $\omega$ be as in Algorithm 8.6. If $(x_{k+1}, y_{k+1})$ is one pass
of Uzawa's method from $(x_k, y_k)$, then
$$\begin{bmatrix} A & 0 \\ -\omega B^H & I \end{bmatrix} \begin{bmatrix} x_{k+1} \\ y_{k+1}
  \end{bmatrix} = \begin{bmatrix} 0 & -B \\ 0 & I \end{bmatrix} \begin{bmatrix} x_k \\ y_k
  \end{bmatrix} + \begin{bmatrix} b \\ -\omega c \end{bmatrix}.$$
So Uzawa's method is the fixed-point iteration of the splitting $M - N$ with these two block
matrices $M$ and $N$. The difference $M - N$ is the saddle-point matrix with its second block
row multiplied by $-\omega$. -/
theorem uzawa_eq_splitting (hA : IsUnit A)
    (s : EuclideanSpace 𝕜 (Fin n) × EuclideanSpace 𝕜 (Fin m)) :
    Matrix.fromBlocks A 0 (-(ω • Bᴴ)) 1
        *ᵥ Sum.elim (WithLp.ofLp (uzawaStep A B b c ω s).1)
          (WithLp.ofLp (uzawaStep A B b c ω s).2)
      = Matrix.fromBlocks 0 (-B) 0 1 *ᵥ Sum.elim (WithLp.ofLp s.1) (WithLp.ofLp s.2)
          + Sum.elim (WithLp.ofLp b) (WithLp.ofLp (-(ω • c))) := by
  have hx : (A ⬝ (uzawaStep A B b c ω s).1) = b - (B ⬝ s.2) :=
    toEuclideanLin_mul_nonsing_inv_apply hA _
  have hy : (uzawaStep A B b c ω s).2
      = s.2 + ω • ((Bᴴ ⬝ (uzawaStep A B b c ω s).1) - c) := rfl
  rw [fromBlocks_elim_eq_iff]
  refine ⟨?_, ?_⟩
  · simp only [toEuclideanLin_zero_apply, toEuclideanLin_neg_apply]
    rw [hx]
    abel
  · simp only [toEuclideanLin_zero_apply, toEuclideanLin_one_apply, toEuclideanLin_neg_apply,
      toEuclideanLin_smul_apply]
    rw [hy, smul_sub]
    abel

end Uzawa

/-! ### Algorithm 8.7: the Arrow–Hurwicz method -/

section ArrowHurwicz

variable (A B) (b : EuclideanSpace 𝕜 (Fin n)) (c : EuclideanSpace 𝕜 (Fin m)) (ε ω : 𝕜)

/-- One pass through Algorithm 8.7 of [saad2003iterative] (the Arrow–Hurwicz method): the pair
$(x_k, y_k)$ goes to $(x_{k+1}, y_{k+1})$ with
$$x_{k+1} = x_k + \epsilon (b - Ax_k - By_k), \qquad y_{k+1} = y_k + \omega (B^H x_{k+1} - c).$$
One gradient step replaces the exact solve of Uzawa's method. -/
noncomputable def arrowHurwiczStep (s : EuclideanSpace 𝕜 (Fin n) × EuclideanSpace 𝕜 (Fin m)) :
    EuclideanSpace 𝕜 (Fin n) × EuclideanSpace 𝕜 (Fin m) :=
  (s.1 + ε • (b - (A ⬝ s.1) - (B ⬝ s.2)),
    s.2 + ω • ((Bᴴ ⬝ (s.1 + ε • (b - (A ⬝ s.1) - (B ⬝ s.2)))) - c))

/-- **Algorithm 8.7** of [saad2003iterative] (the Arrow–Hurwicz method). Let
$A \in \mathbb{K}^{n \times n}$, $B \in \mathbb{K}^{n \times m}$, $b \in \mathbb{K}^n$,
$c \in \mathbb{K}^m$ and $\epsilon, \omega \in \mathbb{K}$. From a starting pair $(x_0, y_0)$,
the state after $k$ steps is obtained by $k$ passes of
$$x_{j+1} = x_j + \epsilon (b - Ax_j - By_j), \qquad y_{j+1} = y_j + \omega (B^H x_{j+1} - c).$$

A pass is `SaadSparse.Chapter08.arrowHurwiczStep`. -/
noncomputable def arrowHurwicz
    (s₀ : EuclideanSpace 𝕜 (Fin n) × EuclideanSpace 𝕜 (Fin m)) (k : ℕ) :
    EuclideanSpace 𝕜 (Fin n) × EuclideanSpace 𝕜 (Fin m) :=
  (arrowHurwiczStep A B b c ε ω)^[k] s₀

/-- The state of Algorithm 8.7 after $k + 1$ steps is one pass of the algorithm applied to the state
after $k$ steps. -/
theorem arrowHurwicz_succ (s₀ : EuclideanSpace 𝕜 (Fin n) × EuclideanSpace 𝕜 (Fin m)) (k : ℕ) :
    arrowHurwicz A B b c ε ω s₀ (k + 1)
      = arrowHurwiczStep A B b c ε ω (arrowHurwicz A B b c ε ω s₀ k) :=
  Function.iterate_succ_apply' _ _ _

variable {A B b c ε ω}

/-- **Section 8.4** of [saad2003iterative], the block form of Algorithm 8.7. For $A$, $B$, $b$, $c$,
$\epsilon$ and $\omega$ as in Algorithm 8.7, if $(x_{k+1}, y_{k+1})$ is one pass of the
Arrow–Hurwicz method from $(x_k, y_k)$, then
$$\begin{bmatrix} I & 0 \\ -\omega B^H & I \end{bmatrix} \begin{bmatrix} x_{k+1} \\ y_{k+1}
  \end{bmatrix} = \begin{bmatrix} I - \epsilon A & -\epsilon B \\ 0 & I \end{bmatrix}
  \begin{bmatrix} x_k \\ y_k \end{bmatrix} + \begin{bmatrix} \epsilon b \\ -\omega c
  \end{bmatrix}.$$
This exhibits the Arrow–Hurwicz method as a stationary iteration. -/
theorem arrowHurwicz_eq_block (s : EuclideanSpace 𝕜 (Fin n) × EuclideanSpace 𝕜 (Fin m)) :
    Matrix.fromBlocks 1 0 (-(ω • Bᴴ)) 1
        *ᵥ Sum.elim (WithLp.ofLp (arrowHurwiczStep A B b c ε ω s).1)
          (WithLp.ofLp (arrowHurwiczStep A B b c ε ω s).2)
      = Matrix.fromBlocks (1 - ε • A) (-(ε • B)) 0 1
            *ᵥ Sum.elim (WithLp.ofLp s.1) (WithLp.ofLp s.2)
          + Sum.elim (WithLp.ofLp (ε • b)) (WithLp.ofLp (-(ω • c))) := by
  have hy : (arrowHurwiczStep A B b c ε ω s).2
      = s.2 + ω • ((Bᴴ ⬝ (arrowHurwiczStep A B b c ε ω s).1) - c) := rfl
  have hx : (arrowHurwiczStep A B b c ε ω s).1
      = s.1 + ε • (b - (A ⬝ s.1) - (B ⬝ s.2)) := rfl
  rw [fromBlocks_elim_eq_iff]
  refine ⟨?_, ?_⟩
  · simp only [toEuclideanLin_zero_apply, toEuclideanLin_one_apply, toEuclideanLin_sub_apply,
      toEuclideanLin_neg_apply, toEuclideanLin_smul_apply]
    rw [hx, smul_sub, smul_sub]
    abel
  · simp only [toEuclideanLin_zero_apply, toEuclideanLin_one_apply, toEuclideanLin_neg_apply,
      toEuclideanLin_smul_apply]
    rw [hy, smul_sub]
    abel

end ArrowHurwicz

/-! ### Example 8.2: the regularized Schur complement -/

/-- **Example 8.2** of [saad2003iterative]. For $A \in \mathbb{K}^{n \times n}$,
$B \in \mathbb{K}^{n \times m}$ and $\rho \in \mathbb{K}$, the **regularized Schur complement**
is the Schur complement of the regularized system $\begin{bmatrix} A & B \\ B^H & \rho B^H B
\end{bmatrix}$:
$$S_\rho = \rho B^H B - B^H A^{-1} B.$$
It equals $B^H (\rho I - A^{-1}) B$ (`SaadSparse.Chapter08.regularizedSchur_eq`). -/
noncomputable def regularizedSchur (A : Matrix (Fin n) (Fin n) 𝕜)
    (B : Matrix (Fin n) (Fin m) 𝕜) (ρ : 𝕜) : Matrix (Fin m) (Fin m) 𝕜 :=
  ρ • (Bᴴ * B) - schur A B

/-- **Example 8.2** of [saad2003iterative]. The regularized Schur complement is
$S_\rho = B^H (\rho I - A^{-1}) B$. -/
theorem regularizedSchur_eq (ρ : 𝕜) :
    regularizedSchur A B ρ = Bᴴ * (ρ • 1 - A⁻¹) * B := by
  rw [regularizedSchur, schur, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one]

/-- The regularized Schur complement acts as $S_\rho y = B^H (\rho By - A^{-1}(By))$. -/
theorem regularizedSchur_apply (ρ : 𝕜) (y : EuclideanSpace 𝕜 (Fin m)) :
    (regularizedSchur A B ρ ⬝ y) = (Bᴴ ⬝ (ρ • (B ⬝ y) - (A⁻¹ ⬝ (B ⬝ y)))) := by
  rw [regularizedSchur_eq, Matrix.toEuclideanLin_mul_apply, Matrix.toEuclideanLin_mul_apply]
  refine congrArg (fun z => (Bᴴ ⬝ z)) ?_
  rw [map_sub, map_smul, Matrix.toEuclideanLin_one]
  rfl

/-- **Example 8.2** of [saad2003iterative], the quadratic form. For real $\rho$ and
$y \in \mathbb{K}^m$,
$$\operatorname{Re}(S_\rho y, y) = \rho \|By\|_2^2 - \operatorname{Re}(A^{-1} By, By).$$
So the quadratic form of $S_\rho$ is that of $\rho I - A^{-1}$ on the range of $B$. -/
theorem re_inner_regularizedSchur (ρ : ℝ) (y : EuclideanSpace 𝕜 (Fin m)) :
    RCLike.re (inner 𝕜 (regularizedSchur A B (ρ : 𝕜) ⬝ y) y)
      = ρ * ‖(B ⬝ y)‖ ^ 2 - RCLike.re (inner 𝕜 (A⁻¹ ⬝ (B ⬝ y)) (B ⬝ y)) := by
  rw [regularizedSchur_apply, inner_conjTranspose B _ y, inner_sub_left, inner_smul_left,
    inner_self_eq_norm_sq_to_K]
  simp only [map_sub]
  rw [RCLike.conj_ofReal]
  have h : RCLike.re ((ρ : 𝕜) * ((‖(B ⬝ y)‖ : 𝕜) ^ 2)) = ρ * ‖(B ⬝ y)‖ ^ 2 := by
    rw [← RCLike.ofReal_pow, ← RCLike.ofReal_mul, RCLike.ofReal_re]
  rw [h]

/-- **Example 8.2** of [saad2003iterative]. Let $A \in \mathbb{K}^{n \times n}$, let
$B \in \mathbb{K}^{n \times m}$ have full column rank, and let
$\mu_{\min}, \mu_{\max} \in \mathbb{R}$ be such that $A^{-1}$ is Hermitian with
$$\mu_{\min} \|v\|_2^2 \le \operatorname{Re}(A^{-1} v, v) \le \mu_{\max} \|v\|_2^2 \quad
  \text{for all } v.$$
Let $\rho \in \mathbb{R}$. Then the regularized Schur complement
$S_\rho = B^H (\rho I - A^{-1}) B$ is symmetric; it is positive definite if $\rho > \mu_{\max}$;
and $\operatorname{Re}(S_\rho y, y) < 0$ for every $y \neq 0$ if $\rho < \mu_{\min}$.

When $A$ is symmetric positive definite, the best bounds are $\mu_{\min} = 1/\lambda_{\max}(A)$
and $\mu_{\max} = 1/\lambda_{\min}(A)$, and the two conditions become
$\rho > 1/\lambda_{\min}(A)$ and $\rho < 1/\lambda_{\max}(A)$, which is how the book states the
two thresholds. The inequalities are strict: at $\rho = 1/\lambda_{\min}(A)$ the form of
$\rho I - A^{-1}$ is only positive semidefinite. The bounds are the hypothesis
`LinearMap.IsSymmetricBoundedBy`; the statement does not need them to be attained, and it does
not assume that $A$ is positive definite. -/
theorem example_8_2 (hB : Function.Injective (Matrix.toEuclideanLin B)) {μmin μmax : ℝ}
    (hbd : (Matrix.toEuclideanLin A⁻¹).IsSymmetricBoundedBy μmin μmax) {ρ : ℝ} :
    (Matrix.toEuclideanLin (regularizedSchur A B (ρ : 𝕜))).IsSymmetric ∧
      (μmax < ρ → (regularizedSchur A B (ρ : 𝕜)).PosDef) ∧
      (ρ < μmin → ∀ y : EuclideanSpace 𝕜 (Fin m), y ≠ 0 →
        RCLike.re (inner 𝕜 (regularizedSchur A B (ρ : 𝕜) ⬝ y) y) < 0) := by
  have hnorm : ∀ y : EuclideanSpace 𝕜 (Fin m), y ≠ 0 → 0 < ‖(B ⬝ y)‖ ^ 2 := by
    intro y hy
    have hBy : (B ⬝ y) ≠ 0 := fun h => hy (hB (by
      rw [show (Matrix.toEuclideanLin B) y = (B ⬝ y) from rfl, h, map_zero]))
    have := norm_pos_iff.2 hBy
    positivity
  have hsymm : (Matrix.toEuclideanLin (regularizedSchur A B (ρ : 𝕜))).IsSymmetric := by
    intro u v
    rw [show (Matrix.toEuclideanLin (regularizedSchur A B (ρ : 𝕜))) u
        = (regularizedSchur A B (ρ : 𝕜) ⬝ u) from rfl,
      show (Matrix.toEuclideanLin (regularizedSchur A B (ρ : 𝕜))) v
        = (regularizedSchur A B (ρ : 𝕜) ⬝ v) from rfl,
      regularizedSchur_apply, regularizedSchur_apply,
      inner_conjTranspose B ((ρ : 𝕜) • (B ⬝ u) - (A⁻¹ ⬝ (B ⬝ u))) v,
      ← inner_mul_conjTranspose B u ((ρ : 𝕜) • (B ⬝ v) - (A⁻¹ ⬝ (B ⬝ v))),
      inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, RCLike.conj_ofReal,
      hbd.isSymmetric (B ⬝ u) (B ⬝ v)]
  refine ⟨hsymm, fun hρ => ?_, fun hρ y hy => ?_⟩
  · rw [Matrix.posDef_iff_isSymmetricCoercive]
    refine ⟨hsymm, (LinearMap.isCoercive_iff_forall_pos _).2 fun y hy => ?_⟩
    rw [show (Matrix.toEuclideanLin (regularizedSchur A B (ρ : 𝕜))) y
      = (regularizedSchur A B (ρ : 𝕜) ⬝ y) from rfl, re_inner_regularizedSchur]
    nlinarith [hbd.re_inner_le (B ⬝ y), hnorm y hy]
  · rw [re_inner_regularizedSchur]
    nlinarith [hbd.le_re_inner (B ⬝ y), hnorm y hy]

/-! ### Corollary 8.1 -/

section Corollary

variable {A : Matrix (Fin n) (Fin n) ℝ} {B : Matrix (Fin n) (Fin m) ℝ}
  {b : EuclideanSpace ℝ (Fin n)} {c : EuclideanSpace ℝ (Fin m)} {ω : ℝ}

/-- **Equation (8.32)** of [saad2003iterative], Uzawa's method as Richardson's iteration. Over
$\mathbb{R}$, let $A \in \mathbb{R}^{n \times n}$, $B \in \mathbb{R}^{n \times m}$,
$b \in \mathbb{R}^n$, $c \in \mathbb{R}^m$ and $\omega \in \mathbb{R}$. For every starting pair
$(x_0, y_0)$ and every $k$, the $y$-component of the state of Uzawa's method after $k$ steps is
the $k$-th iterate of Richardson's iteration $y \mapsto y + \omega (g - Sy)$ from $y_0$.

So the convergence of Uzawa's method is Example 4.1 applied to $S$. Richardson's step is
`SaadSparse.Chapter04.richardsonStep`, in plain coordinates. -/
theorem uzawa_snd_eq_richardson
    (s₀ : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) (k : ℕ) :
    WithLp.ofLp (uzawa A B b c ω s₀ k).2
      = (Chapter04.richardsonStep (schur A B) ω (WithLp.ofLp (schurRhs A B b c)))^[k]
          (WithLp.ofLp s₀.2) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [uzawa_succ, equation_8_32, Function.iterate_succ_apply', ← ih, Chapter04.richardsonStep,
      WithLp.ofLp_add, WithLp.ofLp_smul, WithLp.ofLp_sub]
    rfl

/-- **Corollary 8.1** of [saad2003iterative]. Let $A \in \mathbb{R}^{n \times n}$ be symmetric
positive definite, let $B \in \mathbb{R}^{n \times m}$ have full column rank, and let
$S = B^T A^{-1} B$. Let $\lambda_{\min} > 0$ and $\lambda_{\max}$ be eigenvalues of $S$ such
that the spectrum of $S$ lies in $[\lambda_{\min}, \lambda_{\max}]$, and let $\omega \neq 0$.
Then:

* $S$ is symmetric positive definite;
* Richardson's iteration $y_{k+1} = y_k + \omega (g - Sy_k)$ converges for every $g$ and every
  $y_0$ if and only if $0 < \omega < 2/\lambda_{\max}$;
* among $\omega > 0$, the spectral radius $\rho(I - \omega S)$ is smallest at
  $\omega_{\mathrm{opt}} = 2/(\lambda_{\min} + \lambda_{\max})$.

By `SaadSparse.Chapter08.equation_8_32` and `SaadSparse.Chapter08.uzawa_snd_eq_richardson`, the
$y$-iteration of Uzawa's method is this Richardson iteration with $g = B^T A^{-1} b - c$. So
Uzawa's method converges for every right-hand side and every starting pair exactly when
$0 < \omega < 2/\lambda_{\max}(S)$, with the optimal parameter
$2/(\lambda_{\min}(S) + \lambda_{\max}(S))$. The last two parts are Example 4.1 applied to $S$.
The hypothesis $\omega \neq 0$ excludes the constant iteration. The spectral radius is
`Matrix.complexSpectralRadius`. -/
theorem corollary_8_1 (hA : A.PosDef) (hB : Function.Injective (Matrix.toEuclideanLin B))
    {lmin lmax : ℝ} (hsub : spectrum ℝ (schur A B) ⊆ Set.Icc lmin lmax)
    (hmin : lmin ∈ spectrum ℝ (schur A B)) (hmax : lmax ∈ spectrum ℝ (schur A B))
    (hpos : 0 < lmin) (hω : ω ≠ 0) :
    (schur A B).PosDef ∧
      ((∀ g y₀ : Fin m → ℝ, ∃ y,
          Tendsto (fun k => (Chapter04.richardsonStep (schur A B) ω g)^[k] y₀) atTop (𝓝 y)) ↔
        0 < ω ∧ ω < 2 / lmax) ∧
      IsMinOn (fun ω : ℝ => Matrix.complexSpectralRadius (1 - ω • schur A B)) (Set.Ioi 0)
        (2 / (lmin + lmax)) :=
  ⟨schur_posDef hA hB,
    Chapter04.example_4_1_tendsto_iff (schur_posDef hA hB).isHermitian hsub hmin hmax hpos hω,
    (Chapter04.example_4_1_opt (schur_posDef hA hB).isHermitian hsub hmin hmax hpos).1⟩

end Corollary

/-! ### Section 8.4: the Lagrangian and the saddle point -/

section Lagrangian

variable {A : Matrix (Fin n) (Fin n) 𝕜} {B : Matrix (Fin n) (Fin m) 𝕜}

/-- **Section 8.4** of [saad2003iterative], the Lagrangian. For $A \in \mathbb{K}^{n \times n}$,
$B \in \mathbb{K}^{n \times m}$, $b \in \mathbb{K}^n$ and $c \in \mathbb{K}^m$, the
**Lagrangian** of the constrained problem (8.28)–(8.29) is the real-valued function
$$L(x, y) = f(x) + \operatorname{Re}(y, B^H x - c),$$
where $f$ is the objective `SaadSparse.Chapter08.saddleObjective`. Its stationarity conditions
are the block system (8.30). -/
noncomputable def lagrangian (A : Matrix (Fin n) (Fin n) 𝕜) (B : Matrix (Fin n) (Fin m) 𝕜)
    (b : EuclideanSpace 𝕜 (Fin n)) (c : EuclideanSpace 𝕜 (Fin m))
    (x : EuclideanSpace 𝕜 (Fin n)) (y : EuclideanSpace 𝕜 (Fin m)) : ℝ :=
  saddleObjective A b x + RCLike.re (inner 𝕜 ((Bᴴ ⬝ x) - c) y)

/-- **Section 8.4** of [saad2003iterative], the saddle point. Let $A \in \mathbb{K}^{n \times n}$ be
symmetric positive definite, $B \in \mathbb{K}^{n \times m}$, $b \in \mathbb{K}^n$ and
$c \in \mathbb{K}^m$, and let $(x_*, y_*)$ solve the block system (8.30): $B^H x_* = c$ and
$Ax_* + By_* = b$. Then for every $x \in \mathbb{K}^n$ and every $y \in \mathbb{K}^m$,
$$L(x_*, y) \le L(x_*, y_*) \le L(x, y_*).$$
This is the sentence that names the section: the solution of (8.30) is a saddle point of the
Lagrangian.

The two halves are of different kinds. Since $x_*$ is admissible, $L(x_*, \cdot)$ is constant,
so the first inequality is an equality, and the saddle point is never strict in $y$. On the $x$
side, $L(x, y_*) - L(x_*, y_*) = \tfrac12 \operatorname{Re}(A(x - x_*), x - x_*)$, which is
nonnegative because $A$ is positive definite. The second inequality holds for every $x$,
admissible or not; this distinguishes the saddle-point statement from the constrained
minimization of `SaadSparse.Chapter08.equation_8_30`. -/
theorem lagrangian_isSaddle (hA : A.PosDef) (b : EuclideanSpace 𝕜 (Fin n))
    (c : EuclideanSpace 𝕜 (Fin m)) {xstar : EuclideanSpace 𝕜 (Fin n)}
    {ystar : EuclideanSpace 𝕜 (Fin m)} (hx : (Bᴴ ⬝ xstar) = c)
    (hy : (A ⬝ xstar) + (B ⬝ ystar) = b) (x : EuclideanSpace 𝕜 (Fin n))
    (y : EuclideanSpace 𝕜 (Fin m)) :
    lagrangian A B b c xstar y ≤ lagrangian A B b c xstar ystar ∧
      lagrangian A B b c xstar ystar ≤ lagrangian A B b c x ystar := by
  have hsc := (Matrix.posDef_iff_isSymmetricCoercive A).1 hA
  -- the Lagrangian does not depend on `y` at the admissible point `x_*`
  have hconst : ∀ w : EuclideanSpace 𝕜 (Fin m),
      lagrangian A B b c xstar w = saddleObjective A b xstar := fun w => by
    rw [lagrangian, hx, sub_self, inner_zero_left, map_zero, add_zero]
  refine ⟨le_of_eq (by rw [hconst y, hconst ystar]), ?_⟩
  rw [hconst ystar, lagrangian]
  set e := x - xstar with he
  have hxe : x = xstar + e := by rw [he]; abel
  have hAsym : inner 𝕜 (A ⬝ e) xstar = inner 𝕜 e (A ⬝ xstar) := hsc.isSymmetric e xstar
  have hre : RCLike.re (inner 𝕜 e (A ⬝ xstar)) = RCLike.re (inner 𝕜 (A ⬝ xstar) e) := by
    rw [← inner_conj_symm]
    exact RCLike.conj_re _
  have hquad : RCLike.re (inner 𝕜 (A ⬝ x) x)
      = RCLike.re (inner 𝕜 (A ⬝ xstar) xstar) + 2 * RCLike.re (inner 𝕜 (A ⬝ xstar) e)
        + RCLike.re (inner 𝕜 (A ⬝ e) e) := by
    conv_lhs => rw [hxe]
    rw [show (A ⬝ (xstar + e)) = (A ⬝ xstar) + (A ⬝ e) from map_add _ _ _, inner_add_left,
      inner_add_right, inner_add_right, map_add, map_add, map_add, hAsym, hre]
    ring
  have hlin : RCLike.re (inner 𝕜 b x)
      = RCLike.re (inner 𝕜 b xstar) + RCLike.re (inner 𝕜 b e) := by
    conv_lhs => rw [hxe]
    rw [inner_add_right, map_add]
  have hBe : (Bᴴ ⬝ x) - c = (Bᴴ ⬝ e) := by rw [he, map_sub, hx]
  have hmult : (B ⬝ ystar) = b - (A ⬝ xstar) := by rw [← hy]; abel
  have hcon : RCLike.re (inner 𝕜 ((Bᴴ ⬝ x) - c) ystar)
      = RCLike.re (inner 𝕜 b e) - RCLike.re (inner 𝕜 (A ⬝ xstar) e) := by
    have hbe : RCLike.re (inner 𝕜 e b) = RCLike.re (inner 𝕜 b e) := by
      rw [← inner_conj_symm]
      exact RCLike.conj_re _
    rw [hBe, inner_conjTranspose B e ystar, hmult, inner_sub_right, map_sub, hbe, hre]
  have hnonneg : 0 ≤ RCLike.re (inner 𝕜 (A ⬝ e) e) := by
    rcases eq_or_ne e 0 with h0 | h0
    · rw [h0, show (A ⬝ (0 : EuclideanSpace 𝕜 (Fin n))) = 0 from map_zero _, inner_zero_left,
        map_zero]
    · exact le_of_lt (hsc.isCoercive.inner_self_pos h0)
  rw [saddleObjective, saddleObjective, hquad, hlin, hcon]
  linarith

end Lagrangian

/-! ### Problem P-8.6: the projector onto the constraint space -/

section Projector

variable {A : Matrix (Fin n) (Fin n) 𝕜} {B : Matrix (Fin n) (Fin m) 𝕜}

/-- **Problem P-8.6** of [saad2003iterative]. For $B \in \mathbb{K}^{n \times m}$, the **constraint
projector** of the null-space method for the saddle-point system is
$$P = I - B (B^H B)^{-1} B^H.$$
-/
noncomputable def constraintProjector (B : Matrix (Fin n) (Fin m) 𝕜) :
    Matrix (Fin n) (Fin n) 𝕜 :=
  1 - B * (Bᴴ * B)⁻¹ * Bᴴ

/-- If $B$ has full column rank as an operator on Euclidean space, then the map $y \mapsto By$ on
plain coordinate vectors is injective. -/
private theorem injective_mulVec (hB : Function.Injective (Matrix.toEuclideanLin B)) :
    Function.Injective B.mulVec := fun u v huv =>
  (WithLp.toLp_injective 2) (hB (show (B ⬝ WithLp.toLp 2 u) = (B ⬝ WithLp.toLp 2 v) from
    congrArg (WithLp.toLp 2) huv))

/-- If $B$ has full column rank, then $B^H B$ is nonsingular, so $P$ is well defined. -/
private theorem isUnit_conjTranspose_mul_self
    (hB : Function.Injective (Matrix.toEuclideanLin B)) : IsUnit (Bᴴ * B) :=
  (Matrix.PosDef.conjTranspose_mul_self B (injective_mulVec hB)).isUnit

/-- **Problem P-8.6(a)** of [saad2003iterative]. Let $B \in \mathbb{K}^{n \times m}$ have full
column rank. Then $P = I - B (B^H B)^{-1} B^H$ is the orthogonal projector onto the constraint
space $\operatorname{Ker} B^H = (\operatorname{Ran} B)^\perp$.

The orthogonal projector is `Submodule.starProjection`. The range and the kernel of $P$ are
stated in `SaadSparse.Chapter08.constraintProjector_apply_eq_self_iff` and
`SaadSparse.Chapter08.constraintProjector_apply_eq_zero_iff`. -/
theorem problem_8_6_projector (hB : Function.Injective (Matrix.toEuclideanLin B)) :
    (Matrix.toEuclideanLin (constraintProjector B) :
        EuclideanSpace 𝕜 (Fin n) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin n))
      = ((LinearMap.ker (Matrix.toEuclideanLin Bᴴ)).starProjection :
        EuclideanSpace 𝕜 (Fin n) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin n)) := by
  have hu := isUnit_conjTranspose_mul_self hB
  refine LinearMap.ext fun u => ?_
  refine (Submodule.eq_starProjection_of_mem_orthogonal ?_ ?_).symm
  · rw [LinearMap.mem_ker,
      show (Matrix.toEuclideanLin Bᴴ) ((Matrix.toEuclideanLin (constraintProjector B)) u)
        = ((Bᴴ * constraintProjector B) ⬝ u) from (Matrix.toEuclideanLin_mul_apply _ _ _).symm,
      constraintProjector, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hu),
      Matrix.one_mul, sub_self, map_zero]
    rfl
  · rw [orthogonal_ker_eq_range B]
    refine ⟨(((Bᴴ * B)⁻¹ * Bᴴ) ⬝ u), ?_⟩
    rw [show (Matrix.toEuclideanLin B) (((Bᴴ * B)⁻¹ * Bᴴ) ⬝ u)
        = ((B * ((Bᴴ * B)⁻¹ * Bᴴ)) ⬝ u) from (Matrix.toEuclideanLin_mul_apply _ _ _).symm,
      show (Matrix.toEuclideanLin (constraintProjector B)) u
        = (constraintProjector B ⬝ u) from rfl, constraintProjector, Matrix.mul_assoc]
    rw [show ((1 - B * ((Bᴴ * B)⁻¹ * Bᴴ)) ⬝ u)
      = (Matrix.toEuclideanLin (1 - B * ((Bᴴ * B)⁻¹ * Bᴴ))) u from rfl,
      show (Matrix.toEuclideanLin (1 - B * ((Bᴴ * B)⁻¹ * Bᴴ)) :
          EuclideanSpace 𝕜 (Fin n) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin n))
        = Matrix.toEuclideanLin 1 - Matrix.toEuclideanLin (B * ((Bᴴ * B)⁻¹ * Bᴴ)) from
        map_sub _ _ _]
    rw [LinearMap.sub_apply, Matrix.toEuclideanLin_one]
    simp

/-- **Problem P-8.6(a)** of [saad2003iterative], the range of $P$. Let
$B \in \mathbb{K}^{n \times m}$ have full column rank. Then $Pu = u$ if and only if $B^H u = 0$:
$P$ fixes exactly the admissible directions, so $\operatorname{Ran} P = \operatorname{Ker} B^H$. -/
theorem constraintProjector_apply_eq_self_iff (hB : Function.Injective (Matrix.toEuclideanLin B))
    (u : EuclideanSpace 𝕜 (Fin n)) : (constraintProjector B ⬝ u) = u ↔ (Bᴴ ⬝ u) = 0 := by
  rw [show (constraintProjector B ⬝ u)
    = (Matrix.toEuclideanLin (constraintProjector B)) u from rfl]
  rw [show (Matrix.toEuclideanLin (constraintProjector B)) u
    = ((LinearMap.ker (Matrix.toEuclideanLin Bᴴ)).starProjection u) from
    congrFun (congrArg DFunLike.coe (problem_8_6_projector hB)) u]
  exact Submodule.starProjection_eq_self_iff.trans LinearMap.mem_ker

/-- **Problem P-8.6(a)** of [saad2003iterative], the kernel of $P$. Let
$B \in \mathbb{K}^{n \times m}$ have full column rank. Then $Pu = 0$ if and only if
$u \in \operatorname{Ran} B$. So $\operatorname{Ker} P = \operatorname{Ran} B$, which is where
the Lagrange multiplier term lies. -/
theorem constraintProjector_apply_eq_zero_iff (hB : Function.Injective (Matrix.toEuclideanLin B))
    (u : EuclideanSpace 𝕜 (Fin n)) :
    (constraintProjector B ⬝ u) = 0 ↔ u ∈ LinearMap.range (Matrix.toEuclideanLin B) := by
  rw [show (constraintProjector B ⬝ u)
    = ((LinearMap.ker (Matrix.toEuclideanLin Bᴴ)).starProjection u) from
    congrFun (congrArg DFunLike.coe (problem_8_6_projector hB)) u, ← orthogonal_ker_eq_range B]
  constructor
  · intro h
    have hmem := Submodule.sub_starProjection_mem_orthogonal
      (K := LinearMap.ker (Matrix.toEuclideanLin Bᴴ)) u
    rwa [h, sub_zero] at hmem
  · intro h
    exact Submodule.eq_starProjection_of_mem_orthogonal (Submodule.zero_mem _) (by rwa [sub_zero])

/-- **Problem P-8.6(b)** and **Equation (8.35)** of [saad2003iterative]. Let
$A \in \mathbb{K}^{n \times n}$, let $B \in \mathbb{K}^{n \times m}$ have full column rank, let
$b \in \mathbb{K}^n$, and let $x \in \mathbb{K}^n$ satisfy $B^H x = 0$. Then there is a $y$ with
$Ax + By = b$, that is, $(x, y)$ solves the block system (8.30) with $c = 0$, if and only if
$$PAPx = Pb.$$

Both directions use `SaadSparse.Chapter08.constraintProjector_apply_eq_zero_iff`: $P$ fixes the
admissible $x$, so (8.35) says $P(Ax - b) = 0$, and the kernel of $P$ is $\operatorname{Ran} B$,
where the multiplier term $-By$ lies. When $A$ is symmetric positive definite, $PAP$ is
symmetric positive semidefinite, and it is singular whenever $B \neq 0$. So the convergence of
the conjugate gradient method on this system needs the theory of a consistent semidefinite
system, which is not formalized. -/
theorem equation_8_35 (hB : Function.Injective (Matrix.toEuclideanLin B))
    (b : EuclideanSpace 𝕜 (Fin n)) {x : EuclideanSpace 𝕜 (Fin n)} (hx : (Bᴴ ⬝ x) = 0) :
    (∃ y, (A ⬝ x) + (B ⬝ y) = b) ↔
      (constraintProjector B ⬝ (A ⬝ (constraintProjector B ⬝ x)))
        = (constraintProjector B ⬝ b) := by
  rw [(constraintProjector_apply_eq_self_iff hB x).2 hx]
  have hsub : ((constraintProjector B ⬝ (A ⬝ x)) = (constraintProjector B ⬝ b)) ↔
      (constraintProjector B ⬝ ((A ⬝ x) - b)) = 0 := by
    rw [map_sub, sub_eq_zero]
  rw [hsub, constraintProjector_apply_eq_zero_iff hB]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨-y, ?_⟩
    rw [show (Matrix.toEuclideanLin B) (-y) = -(B ⬝ y) from map_neg _ _, ← hy]
    abel
  · rintro ⟨y, hy⟩
    rw [show (Matrix.toEuclideanLin B) y = (B ⬝ y) from rfl] at hy
    refine ⟨-y, ?_⟩
    rw [show (B ⬝ (-y)) = -(B ⬝ y) from map_neg _ _, hy]
    abel

/-! ### Problem P-8.6(c), first half: the subspace of the conjugate gradient iterates -/

/-- **Problem P-8.6(c)** of [saad2003iterative], the constraint projector lands in the constraint
space. Let $B \in \mathbb{K}^{n \times m}$ have full column rank. Then $B^H P = 0$. -/
theorem conjTranspose_mul_constraintProjector
    (hB : Function.Injective (Matrix.toEuclideanLin B)) : Bᴴ * constraintProjector B = 0 := by
  have hu := (Matrix.isUnit_iff_isUnit_det _).1 (isUnit_conjTranspose_mul_self (B := B) hB)
  rw [constraintProjector, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ hu, Matrix.one_mul, sub_self]

/-- **Problem P-8.6(c)** of [saad2003iterative], the subspace in which the conjugate gradient
iterates for (8.35) lie. Let $A \in \mathbb{K}^{n \times n}$, let
$B \in \mathbb{K}^{n \times m}$ have full column rank, and let $b \in \mathbb{K}^n$. Then for
every $k$,
$$\mathcal{K}_k(PAP, Pb) \subseteq \operatorname{Ker} B^H.$$

From $x_0 = 0$ the conjugate gradient iterates lie in this Krylov subspace, so they lie in the
constraint space. Every generator of the Krylov subspace is a value of $P$, which $B^H$
annihilates (`SaadSparse.Chapter08.conjTranspose_mul_constraintProjector`). This is why the
singular system is harmless: when $A$ is symmetric positive definite, the iteration takes place
in $\operatorname{Ker} B^H$, where $PAP$ is positive definite. The Krylov subspace is the
backbone `Krylov.subspace`. -/
theorem problem_8_6_cg_subspace (hB : Function.Injective (Matrix.toEuclideanLin B))
    (b : EuclideanSpace 𝕜 (Fin n)) (k : ℕ) :
    Krylov.subspace
        (Matrix.toEuclideanLin (constraintProjector B * A * constraintProjector B))
        (Matrix.toEuclideanLin (constraintProjector B) b) k
      ≤ LinearMap.ker (Matrix.toEuclideanLin Bᴴ) := by
  have hBP := conjTranspose_mul_constraintProjector (B := B) hB
  have hstep : ∀ w : EuclideanSpace 𝕜 (Fin n),
      Matrix.toEuclideanLin (constraintProjector B * A * constraintProjector B) w
        ∈ LinearMap.ker (Matrix.toEuclideanLin Bᴴ) := fun w => by
    rw [LinearMap.mem_ker, show (Matrix.toEuclideanLin Bᴴ)
        ((Matrix.toEuclideanLin (constraintProjector B * A * constraintProjector B)) w)
      = ((Bᴴ * (constraintProjector B * A * constraintProjector B)) ⬝ w) from
        (Matrix.toEuclideanLin_mul_apply _ _ _).symm,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, hBP, Matrix.zero_mul, Matrix.zero_mul]
    exact toEuclideanLin_zero_apply w
  have hv : Matrix.toEuclideanLin (constraintProjector B) b
      ∈ LinearMap.ker (Matrix.toEuclideanLin Bᴴ) := by
    rw [LinearMap.mem_ker, show (Matrix.toEuclideanLin Bᴴ)
        ((Matrix.toEuclideanLin (constraintProjector B)) b)
      = ((Bᴴ * constraintProjector B) ⬝ b) from (Matrix.toEuclideanLin_mul_apply _ _ _).symm, hBP]
    exact toEuclideanLin_zero_apply b
  have hpow : ∀ j : ℕ,
      ((Matrix.toEuclideanLin (constraintProjector B * A * constraintProjector B)) ^ j)
          (Matrix.toEuclideanLin (constraintProjector B) b)
        ∈ LinearMap.ker (Matrix.toEuclideanLin Bᴴ) := by
    intro j
    cases j with
    | zero => simpa using hv
    | succ j =>
      rw [pow_succ', Module.End.mul_apply]
      exact hstep _
  rw [Krylov.subspace, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact hpow _

end Projector

/-! ### Problem P-8.5(b): a method for (8.30) through the reduced system -/

section Problem85b

variable {A : Matrix (Fin n) (Fin n) 𝕜} {B : Matrix (Fin n) (Fin m) 𝕜}

/-- **Problem P-8.5(b)** of [saad2003iterative]. Let $A \in \mathbb{K}^{n \times n}$ be nonsingular,
$B \in \mathbb{K}^{n \times m}$, $b \in \mathbb{K}^n$, and let $c, y \in \mathbb{K}^m$ satisfy
$Sy = g$. Then $(A^{-1}(b - By), y)$ solves the block system (8.30):
$$\begin{bmatrix} A & B \\ B^H & 0 \end{bmatrix} \begin{bmatrix} A^{-1}(b - By) \\ y
  \end{bmatrix} = \begin{bmatrix} b \\ c \end{bmatrix}.$$
So any solver for the reduced system (8.32) is a method for solving (8.30), for $c = 0$ and for
$c \neq 0$ alike.

For $c = 0$ the reduced system is the system of normal equations of $\min_y \|b - By\|_{A^{-1}}$
(`SaadSparse.Chapter08.equation_8_32_isMinResidual`), so the method that Problem P-8.5(a) asks
for is CGNR in the $A^{-1}$ inner product. A product $Sy$ costs one solve with $A$, as the hint
of the problem asks. Uzawa's method (`SaadSparse.Chapter08.uzawa`,
`SaadSparse.Chapter08.uzawa_snd_eq_richardson`) is Richardson's iteration for the same reduced
system with a fixed $\omega$; this method replaces the fixed step length by the conjugate
gradient one at the same cost per step. -/
theorem problem_8_5b (hA : IsUnit A) (b : EuclideanSpace 𝕜 (Fin n))
    (c y : EuclideanSpace 𝕜 (Fin m)) (hy : (schur A B ⬝ y) = schurRhs A B b c) :
    saddleMatrix A B 0 *ᵥ Sum.elim (WithLp.ofLp (A⁻¹ ⬝ (b - (B ⬝ y)))) (WithLp.ofLp y)
      = Sum.elim (WithLp.ofLp b) (WithLp.ofLp c) := by
  obtain ⟨h1, h2⟩ := (schur_eq hA b c y rfl).1 hy
  rw [saddleMatrix_mulVec_iff]
  refine ⟨h1, ?_⟩
  rw [toEuclideanLin_zero_apply, add_zero]
  exact h2

end Problem85b

/-! ### Problem P-8.12: the indefinite saddle-point matrix -/

section Problem812

variable {A : Matrix (Fin n) (Fin n) 𝕜} {B : Matrix (Fin n) (Fin m) 𝕜}

/-- **Problem P-8.12** of [saad2003iterative], block vectors. For $u \in \mathbb{K}^n$ and
$v \in \mathbb{K}^m$, the **block vector** $(u, v) \in \mathbb{K}^{n + m}$ is the vector whose
first $n$ entries are those of $u$ and whose last $m$ entries are those of $v$; it is indexed by
`Fin n ⊕ Fin m`. Every vector of Problem P-8.12 has this form. -/
noncomputable def blockVec (u : EuclideanSpace 𝕜 (Fin n)) (v : EuclideanSpace 𝕜 (Fin m)) :
    EuclideanSpace 𝕜 (Fin n ⊕ Fin m) :=
  WithLp.toLp 2 (Sum.elim (WithLp.ofLp u) (WithLp.ofLp v))

/-- **Problem P-8.12** of [saad2003iterative], the action on block vectors. For $A$, $B$, $D$ as in
`SaadSparse.Chapter08.saddleMatrix` and $u \in \mathbb{K}^n$, $v \in \mathbb{K}^m$,
$$\begin{bmatrix} A & B \\ B^H & D \end{bmatrix} \begin{bmatrix} u \\ v \end{bmatrix} =
  \begin{bmatrix} Au + Bv \\ B^H u + Dv \end{bmatrix}.$$
-/
theorem saddleMatrix_apply_blockVec (D : Matrix (Fin m) (Fin m) 𝕜)
    (u : EuclideanSpace 𝕜 (Fin n)) (v : EuclideanSpace 𝕜 (Fin m)) :
    (saddleMatrix A B D ⬝ blockVec u v) = blockVec ((A ⬝ u) + (B ⬝ v)) ((Bᴴ ⬝ u) + (D ⬝ v)) := by
  refine WithLp.ofLp_injective 2 ?_
  rw [show WithLp.ofLp (saddleMatrix A B D ⬝ blockVec u v)
      = saddleMatrix A B D *ᵥ WithLp.ofLp (blockVec u v) from rfl,
    blockVec, WithLp.ofLp_toLp, saddleMatrix, Matrix.saddleMatrix, fromBlocks_mulVec_elim,
    blockVec, WithLp.ofLp_toLp]

/-- **Problem P-8.12** of [saad2003iterative], inner products of block vectors. For
$u, u' \in \mathbb{K}^n$ and $v, v' \in \mathbb{K}^m$, the inner product of $(u, v)$ and
$(u', v')$ is the sum of the inner products of $u, u'$ and of $v, v'$. -/
theorem inner_blockVec (u u' : EuclideanSpace 𝕜 (Fin n)) (v v' : EuclideanSpace 𝕜 (Fin m)) :
    inner 𝕜 (blockVec u v) (blockVec u' v') = inner 𝕜 u u' + inner 𝕜 v v' := by
  simp [blockVec, PiLp.inner_apply, Fintype.sum_sum_type]

/-- **Problem P-8.12(1)** of [saad2003iterative], the positive direction. Let
$A \in \mathbb{K}^{n \times n}$ be symmetric positive definite, $B \in \mathbb{K}^{n \times m}$,
and $u \in \mathbb{K}^n$ with $u \neq 0$. Then the quadratic form of the saddle-point matrix
$\mathcal{A} = \begin{bmatrix} A & B \\ B^H & 0 \end{bmatrix}$ on $x = (u, 0)$ is positive:
$$\operatorname{Re}(\mathcal{A} x, x) = \operatorname{Re}(Au, u) > 0.$$
-/
theorem problem_8_12_pos (hA : A.PosDef) {u : EuclideanSpace 𝕜 (Fin n)} (hu : u ≠ 0) :
    0 < RCLike.re (inner 𝕜 (blockVec u (0 : EuclideanSpace 𝕜 (Fin m)))
      (saddleMatrix A B 0 ⬝ blockVec u 0)) := by
  rw [saddleMatrix_apply_blockVec, map_zero, add_zero, toEuclideanLin_zero_apply, add_zero,
    inner_blockVec, inner_zero_left, add_zero, ← inner_conj_symm, RCLike.conj_re]
  exact ((Matrix.posDef_iff_isSymmetricCoercive A).1 hA).isCoercive.inner_self_pos hu

/-- **Problem P-8.12(1)** of [saad2003iterative], the negative direction. Let
$A \in \mathbb{K}^{n \times n}$ be symmetric positive definite, let
$B \in \mathbb{K}^{n \times m}$ have full column rank, and let $p \in \mathbb{K}^m$ with
$p \neq 0$. Then on $x = (-A^{-1} Bp, p)$ the quadratic form of the saddle-point matrix
$\mathcal{A}$ is negative:
$$\operatorname{Re}(\mathcal{A} x, x) < 0.$$

The first block of $\mathcal{A} x$ vanishes, and the form is
$-\operatorname{Re}(A^{-1} Bp, Bp)$, which is negative since $Bp \neq 0$. -/
theorem problem_8_12_neg (hA : A.PosDef) (hB : Function.Injective (Matrix.toEuclideanLin B))
    {p : EuclideanSpace 𝕜 (Fin m)} (hp : p ≠ 0) :
    RCLike.re (inner 𝕜 (blockVec (-(A⁻¹ ⬝ (B ⬝ p))) p)
      (saddleMatrix A B 0 ⬝ blockVec (-(A⁻¹ ⬝ (B ⬝ p))) p)) < 0 := by
  have hAinv := (Matrix.posDef_iff_isSymmetricCoercive A⁻¹).1 hA.inv
  have hBp : (B ⬝ p) ≠ 0 := fun h => hp (hB (by
    rw [show (Matrix.toEuclideanLin B) p = (B ⬝ p) from rfl, h, map_zero]))
  have hfst : (A ⬝ (-(A⁻¹ ⬝ (B ⬝ p)))) + (B ⬝ p) = 0 := by
    rw [show (A ⬝ (-(A⁻¹ ⬝ (B ⬝ p)))) = -(A ⬝ (A⁻¹ ⬝ (B ⬝ p))) from map_neg _ _,
      toEuclideanLin_mul_nonsing_inv_apply hA.isUnit]
    abel
  rw [saddleMatrix_apply_blockVec, hfst, toEuclideanLin_zero_apply, add_zero, inner_blockVec,
    inner_zero_right, zero_add,
    show (Bᴴ ⬝ (-(A⁻¹ ⬝ (B ⬝ p)))) = -(Bᴴ ⬝ (A⁻¹ ⬝ (B ⬝ p))) from map_neg _ _,
    inner_neg_right, inner_conjTranspose', map_neg, neg_lt_zero, ← inner_conj_symm, RCLike.conj_re]
  exact hAinv.isCoercive.inner_self_pos hBp

/-- A Hermitian matrix $M$ whose real spectrum is nonnegative has a nonnegative quadratic form:
$\operatorname{Re}(Mv, v) \ge 0$ for every $v$. -/
private theorem re_inner_nonneg_of_spectrum_nonneg {k : Type*} [Fintype k] [DecidableEq k]
    {M : Matrix k k 𝕜} (hM : M.IsHermitian) (hspec : ∀ μ ∈ spectrum ℝ M, 0 ≤ μ)
    (v : EuclideanSpace 𝕜 k) : 0 ≤ RCLike.re (inner 𝕜 v (M ⬝ v)) := by
  have hps : M.PosSemidef :=
    (Matrix.IsHermitian.posSemidef_iff_eigenvalues_nonneg hM).2 fun i =>
      hspec _ (Matrix.IsHermitian.eigenvalues_mem_spectrum_real hM i)
  have h := hps.re_dotProduct_nonneg (WithLp.ofLp v)
  have hval : star (WithLp.ofLp v) ⬝ᵥ (M *ᵥ WithLp.ofLp v) = inner 𝕜 v (M ⬝ v) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    exact dotProduct_comm _ _
  rwa [hval] at h

/-- **Problem P-8.12(1)** of [saad2003iterative]. Let $A \in \mathbb{K}^{n \times n}$ be symmetric
positive definite, let $B \in \mathbb{K}^{n \times m}$ have full column rank, and let there be
nonzero vectors $u \in \mathbb{K}^n$ and $p \in \mathbb{K}^m$, that is, $n \ge 1$ and $m \ge 1$.
Then the saddle-point matrix $\mathcal{A} = \begin{bmatrix} A & B \\ B^H & 0 \end{bmatrix}$ has
a positive real eigenvalue and a negative real eigenvalue.

The two signs of the quadratic form are `SaadSparse.Chapter08.problem_8_12_pos` and
`SaadSparse.Chapter08.problem_8_12_neg`, the two choices of $x$ that the problem asks for. A
Hermitian matrix whose spectrum has one sign has a quadratic form of that sign, so each choice
excludes the corresponding half-line. The eigenvalues are elements of `spectrum ℝ`. -/
theorem problem_8_12_indefinite (hA : A.PosDef) (hB : Function.Injective (Matrix.toEuclideanLin B))
    {u : EuclideanSpace 𝕜 (Fin n)} (hu : u ≠ 0) {p : EuclideanSpace 𝕜 (Fin m)} (hp : p ≠ 0) :
    (∃ μ ∈ spectrum ℝ (saddleMatrix A B (0 : Matrix (Fin m) (Fin m) 𝕜)), 0 < μ) ∧
      ∃ μ ∈ spectrum ℝ (saddleMatrix A B (0 : Matrix (Fin m) (Fin m) 𝕜)), μ < 0 := by
  set M : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) 𝕜 :=
    saddleMatrix A B (0 : Matrix (Fin m) (Fin m) 𝕜) with hMdef
  have hherm : M.IsHermitian :=
    hA.isHermitian.saddleMatrix B (Matrix.isHermitian_zero (n := Fin m))
  have hhermneg : (-M).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_neg, hherm.eq]
  refine ⟨?_, ?_⟩
  · by_contra hcon
    push Not at hcon
    have hneg : ∀ μ ∈ spectrum ℝ (-M), 0 ≤ μ := by
      intro μ hμ
      rw [← spectrum.neg_eq, Set.mem_neg] at hμ
      linarith [hcon _ hμ]
    have h := re_inner_nonneg_of_spectrum_nonneg hhermneg hneg
      (blockVec u (0 : EuclideanSpace 𝕜 (Fin m)))
    rw [show ((-M) ⬝ blockVec u (0 : EuclideanSpace 𝕜 (Fin m)))
        = -(M ⬝ blockVec u (0 : EuclideanSpace 𝕜 (Fin m))) from by
      rw [show (Matrix.toEuclideanLin (-M) :
          EuclideanSpace 𝕜 (Fin n ⊕ Fin m) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin n ⊕ Fin m))
        = -Matrix.toEuclideanLin M from map_neg _ _]
      rfl, inner_neg_right, map_neg, neg_nonneg] at h
    exact absurd (problem_8_12_pos (B := B) hA hu) (not_lt.2 h)
  · by_contra hcon
    push Not at hcon
    have h := re_inner_nonneg_of_spectrum_nonneg hherm hcon (blockVec (-(A⁻¹ ⬝ (B ⬝ p))) p)
    exact absurd (problem_8_12_neg hA hB hp) (not_lt.2 h)

/-- **Problem P-8.12(2)–(3)** of [saad2003iterative], the key computation. Let
$A \in \mathbb{K}^{n \times n}$ and $B \in \mathbb{K}^{n \times m}$. For every
$s \in \mathbb{K}^m$, the quadratic form of the saddle-point matrix $\mathcal{A} =
\begin{bmatrix} A & B \\ B^H & 0 \end{bmatrix}$ vanishes on $r = (0, s)$:
$$(\mathcal{A} r, r) = 0.$$
The residual of the initial guess of Problem P-8.12(2) has this form. -/
theorem inner_saddleMatrix_blockVec_zero (s : EuclideanSpace 𝕜 (Fin m)) :
    inner 𝕜 (blockVec (0 : EuclideanSpace 𝕜 (Fin n)) s)
        (saddleMatrix A B (0 : Matrix (Fin m) (Fin m) 𝕜)
          ⬝ blockVec (0 : EuclideanSpace 𝕜 (Fin n)) s) = 0 := by
  have h1 : (A ⬝ (0 : EuclideanSpace 𝕜 (Fin n))) + (B ⬝ s) = (B ⬝ s) := by
    rw [map_zero, zero_add]
  have h2 : (Bᴴ ⬝ (0 : EuclideanSpace 𝕜 (Fin n)))
      + ((0 : Matrix (Fin m) (Fin m) 𝕜) ⬝ s) = 0 := by
    rw [map_zero, zero_add, toEuclideanLin_zero_apply]
  rw [saddleMatrix_apply_blockVec, h1, h2, inner_blockVec, inner_zero_left, inner_zero_right,
    add_zero]

/-- **Problem P-8.12(2)** of [saad2003iterative], the initial guess. Let
$A \in \mathbb{K}^{n \times n}$, $B \in \mathbb{K}^{n \times m}$ and $f \in \mathbb{K}^n$, and
let $u_0$ satisfy $Au_0 = f$. Then for the right-hand side $(f, 0)$ the initial guess
$x_0 = (u_0, 0)$ has the residual
$$r_0 = \begin{bmatrix} f \\ 0 \end{bmatrix} - \mathcal{A} \begin{bmatrix} u_0 \\ 0
  \end{bmatrix} = \begin{bmatrix} 0 \\ -B^H u_0 \end{bmatrix},$$
so the first block of $r_0$ vanishes and $s_0 = -B^H u_0$. -/
theorem problem_8_12_residual (f : EuclideanSpace 𝕜 (Fin n))
    {u₀ : EuclideanSpace 𝕜 (Fin n)} (hu₀ : (A ⬝ u₀) = f) :
    blockVec f (0 : EuclideanSpace 𝕜 (Fin m))
        - (saddleMatrix A B 0 ⬝ blockVec u₀ (0 : EuclideanSpace 𝕜 (Fin m)))
      = blockVec (0 : EuclideanSpace 𝕜 (Fin n)) (-(Bᴴ ⬝ u₀)) := by
  rw [saddleMatrix_apply_blockVec, map_zero, add_zero, toEuclideanLin_zero_apply, add_zero, hu₀]
  refine WithLp.ofLp_injective 2 ?_
  rw [WithLp.ofLp_sub, blockVec, blockVec, blockVec, WithLp.ofLp_toLp, WithLp.ofLp_toLp,
    WithLp.ofLp_toLp, ← Sum.elim_sub_sub]
  simp

/-- **Problem P-8.12(2)** of [saad2003iterative], steepest descent. Let
$A \in \mathbb{K}^{n \times n}$, $B \in \mathbb{K}^{n \times m}$ and $f \in \mathbb{K}^n$, and
let $u_0$ satisfy $Au_0 = f$. Then one step of steepest descent for $\mathcal{A} x = (f, 0)$
from $x_0 = (u_0, 0)$ returns $x_0$.

The step length $(r_0, r_0)/(\mathcal{A} r_0, r_0)$ has a vanishing denominator because
$r_0 = (0, s_0)$, and division by zero is $0$ in Lean, so the step is the identity. The step is
the backbone `Projection.steepestDescentStep`. -/
theorem problem_8_12_steepestDescent_stalls (f : EuclideanSpace 𝕜 (Fin n))
    {u₀ : EuclideanSpace 𝕜 (Fin n)} (hu₀ : (A ⬝ u₀) = f) :
    Projection.steepestDescentStep
        (Matrix.toEuclideanLin (saddleMatrix A B (0 : Matrix (Fin m) (Fin m) 𝕜)))
        (blockVec f 0) (blockVec u₀ 0)
      = blockVec u₀ (0 : EuclideanSpace 𝕜 (Fin m)) := by
  have hr := problem_8_12_residual (B := B) f hu₀
  rw [Projection.steepestDescentStep, Projection.step1,
    show (Matrix.toEuclideanLin (saddleMatrix A B (0 : Matrix (Fin m) (Fin m) 𝕜)))
        (blockVec u₀ (0 : EuclideanSpace 𝕜 (Fin m)))
      = (saddleMatrix A B (0 : Matrix (Fin m) (Fin m) 𝕜) ⬝ blockVec u₀ 0) from rfl, hr,
    show (Matrix.toEuclideanLin (saddleMatrix A B (0 : Matrix (Fin m) (Fin m) 𝕜)))
        (blockVec (0 : EuclideanSpace 𝕜 (Fin n)) (-(Bᴴ ⬝ u₀)))
      = (saddleMatrix A B (0 : Matrix (Fin m) (Fin m) 𝕜)
        ⬝ blockVec (0 : EuclideanSpace 𝕜 (Fin n)) (-(Bᴴ ⬝ u₀))) from rfl,
    inner_saddleMatrix_blockVec_zero (A := A) (B := B) _,
    div_zero, zero_smul, add_zero]

/-- **Problem P-8.12(3)** of [saad2003iterative], the minimal residual iteration. Let
$A \in \mathbb{K}^{n \times n}$, $B \in \mathbb{K}^{n \times m}$ and $f \in \mathbb{K}^n$, and
let $u_0$ satisfy $Au_0 = f$. Then one step of the minimal residual iteration for
$\mathcal{A} x = (f, 0)$ from $x_0 = (u_0, 0)$ returns $x_0$.

The step length is $(r_0, \mathcal{A} r_0)/(\mathcal{A} r_0, \mathcal{A} r_0)$, and its
numerator is the quantity that vanishes. The step is the backbone `Projection.minResStep`. -/
theorem problem_8_12_minRes_stalls (f : EuclideanSpace 𝕜 (Fin n))
    {u₀ : EuclideanSpace 𝕜 (Fin n)} (hu₀ : (A ⬝ u₀) = f) :
    Projection.minResStep
        (Matrix.toEuclideanLin (saddleMatrix A B (0 : Matrix (Fin m) (Fin m) 𝕜)))
        (blockVec f 0) (blockVec u₀ 0)
      = blockVec u₀ (0 : EuclideanSpace 𝕜 (Fin m)) := by
  have hr := problem_8_12_residual (B := B) f hu₀
  have hzero : inner 𝕜 (saddleMatrix A B (0 : Matrix (Fin m) (Fin m) 𝕜)
        ⬝ blockVec (0 : EuclideanSpace 𝕜 (Fin n)) (-(Bᴴ ⬝ u₀)))
      (blockVec (0 : EuclideanSpace 𝕜 (Fin n)) (-(Bᴴ ⬝ u₀))) = 0 := by
    rw [← inner_conj_symm,
      inner_saddleMatrix_blockVec_zero (A := A) (B := B) _,
      map_zero]
  rw [Projection.minResStep, Projection.step1,
    show (Matrix.toEuclideanLin (saddleMatrix A B (0 : Matrix (Fin m) (Fin m) 𝕜)))
        (blockVec u₀ (0 : EuclideanSpace 𝕜 (Fin m)))
      = (saddleMatrix A B (0 : Matrix (Fin m) (Fin m) 𝕜) ⬝ blockVec u₀ 0) from rfl, hr,
    show (Matrix.toEuclideanLin (saddleMatrix A B (0 : Matrix (Fin m) (Fin m) 𝕜)))
        (blockVec (0 : EuclideanSpace 𝕜 (Fin n)) (-(Bᴴ ⬝ u₀)))
      = (saddleMatrix A B (0 : Matrix (Fin m) (Fin m) 𝕜)
        ⬝ blockVec (0 : EuclideanSpace 𝕜 (Fin n)) (-(Bᴴ ⬝ u₀))) from rfl, hzero, zero_div,
    zero_smul, add_zero]

/-- **Problem P-8.12(5)** of [saad2003iterative]. Let $A \in \mathbb{K}^{n \times n}$,
$B \in \mathbb{K}^{n \times m}$, $f \in \mathbb{K}^n$ and $p \in \mathbb{K}^m$, and let
$g = B^H A^{-1} f$ and $s = B^H A^{-1}(f - Bp)$. Then
$$s = g - Sp,$$
and one step of steepest descent for $Sp = g$ from $p$ is
$$p + \frac{(s, s)}{(Ss, s)} \, s.$$
So in the iteration $u_{k+1} = A^{-1}(f - Bp_k)$, $p_{k+1} = p_k + \alpha_k B^H u_{k+1}$, the
increment $B^H u_{k+1}$ is the residual $s_k$ of $p_k$ for the reduced system $Sp = g$ of
Problem P-8.12(4), and the choice $\alpha_k = (s_k, s_k)/(Ss_k, s_k)$ makes $p_{k+1}$ the
steepest-descent iterate for that system.

The book writes this iteration as $u_{k+1} = B^{-1}(f - Cp_k)$,
$p_{k+1} = p_k + \alpha_k C^T u_{k+1}$: its $B$ and $C$ are $A$ and $B$ here. -/
theorem problem_8_12_reduced (f : EuclideanSpace 𝕜 (Fin n))
    (p : EuclideanSpace 𝕜 (Fin m)) :
    (Bᴴ ⬝ (A⁻¹ ⬝ (f - (B ⬝ p)))) = schurRhs A B f 0 - (schur A B ⬝ p) ∧
      Projection.steepestDescentStep (Matrix.toEuclideanLin (schur A B)) (schurRhs A B f 0) p
        = p + (inner 𝕜 (Bᴴ ⬝ (A⁻¹ ⬝ (f - (B ⬝ p)))) (Bᴴ ⬝ (A⁻¹ ⬝ (f - (B ⬝ p)))) /
            inner 𝕜 (Bᴴ ⬝ (A⁻¹ ⬝ (f - (B ⬝ p))))
              (schur A B ⬝ (Bᴴ ⬝ (A⁻¹ ⬝ (f - (B ⬝ p))))))
          • (Bᴴ ⬝ (A⁻¹ ⬝ (f - (B ⬝ p)))) := by
  have hs : (Bᴴ ⬝ (A⁻¹ ⬝ (f - (B ⬝ p)))) = schurRhs A B f 0 - (schur A B ⬝ p) := by
    rw [conjTranspose_inv_sub, schurRhs, sub_zero]
  refine ⟨hs, ?_⟩
  rw [Projection.steepestDescentStep, Projection.step1, hs]

end Problem812

end SaadSparse.Chapter08
