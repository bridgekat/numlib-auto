/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Numlib.Projection.Basic
import NumlibSurface.SaadSparse.Chapter01.Section13
import NumlibSurface.SaadSparse.Common

/-!
# Saad, Section 8.1: The normal equations

This module formalizes Section 8.1 of [saad2003iterative], together with exercises P-8.1 and P-8.10.
Let $A \in \mathbb{K}^{n \times m}$ be a rectangular matrix. The normal equations of the first kind,
$A^H A x = A^H b$ (8.1), characterize the solutions of the least-squares problem (8.2),
$\min_x \|b - Ax\|_2$. Both directions of this equivalence say that the best approximation to $b$
from $\operatorname{Ran} A$ is the point whose error is orthogonal to $\operatorname{Ran} A$. The
normal equations of the second kind, $A A^H u = b$ (8.3), solve $Ax = b$ through $x = A^H u$, and
this $x$ is the solution of least norm, which is (8.4), $\min_u \|x_* - A^H u\|_2$. The module also
states the augmented system (8.5) and the identity (8.8), $\kappa_2(A^H A) = \kappa_2(A)^2$, which
is the reason of the chapter for preferring methods that never form the normal equations. The proofs
use the projection specifications of `Numlib.Projection.Basic` and the condition number of
`Numlib.Analysis.Matrix.OperatorNorm`.

## Main results

* Equations (8.1)–(8.2), `SaadSparse.Chapter08.equation_8_1`: $A^H A x = A^H b$ if and only if $x$
  minimizes $\|b - Ax\|_2$.
* Equation (8.1), `SaadSparse.Chapter08.isSymmetricCoercive_conjTranspose_mul_self`: if the columns
  of $A$ are independent, then $A^H A$ is symmetric positive definite.
* Equations (8.3)–(8.4), `SaadSparse.Chapter08.equation_8_3`: if $A A^H u = b$, then $x = A^H u$ is
  the solution of $Ax = b$ of least norm.
* Equations (8.5)–(8.7) and exercise P-8.1, `SaadSparse.Chapter08.equation_8_5`: the augmented
  system holds if and only if $r = b - Ax$ and $x$ solves the least-squares problem.
* Equation (8.8), `SaadSparse.Chapter08.equation_8_8`: $\kappa_2(A^H A) = \kappa_2(A)^2$.
* Exercise P-8.10, `SaadSparse.Chapter08.problem_8_10` and
  `SaadSparse.Chapter08.problem_8_10_residual`: replacing $b$ by $b + \alpha r$, with $r$ the
  least-squares residual, does not change the minimizers.

## Implementation notes

* Vectors are `EuclideanSpace 𝕜 (Fin n)`, and $Ax$ is `A ⬝ x`, that is `Matrix.toEuclideanLin A x`,
  as everywhere in this library. Only (8.5) is stated on the plain function types with `*ᵥ`, because
  its coefficient matrix is indexed by `Fin n ⊕ Fin m`.
* Equation (8.4) is stated as `IsMinError` over $\operatorname{Ran} A^H$, which is the form that
  Section 8.3 needs for CGNE.

## Deviations from the source

* **Generalization.** The first normal equations use the adjoint, with full column rank required
  only for positive definiteness. See `SaadSparse.Chapter08.equation_8_1`,
  `SaadSparse.Chapter08.isSymmetricCoercive_conjTranspose_mul_self`.
* **Generalization.** Exercise P-8.10 holds for all aspect ratios and identifies the whole minimizer
  set. See `SaadSparse.Chapter08.problem_8_10_residual`, `SaadSparse.Chapter08.problem_8_10`.
* **Generalization.** The second normal equations require solvability of the stated equation in
  place of full row rank. See `SaadSparse.Chapter08.equation_8_3`.
* **Scope.** The augmented-system theorem gives the residual and least-squares equivalence, with the
  multiplier interpretation in prose. See `SaadSparse.Chapter08.equation_8_5`.
* **Generalization.** The squared condition-number identity uses the adjoint and holds for singular
  square matrices with the totalized inverse. See `SaadSparse.Chapter08.equation_8_8`.
* **Equation (8.8)** (generalization). The source states the identity for a nonsingular $A$. It
  holds for every square $A$, because Lean's inverse of a singular matrix is $0$ and both sides
  vanish. See `SaadSparse.Chapter08.equation_8_8`.

## Not formalized

* **The eigenvalues of the augmented matrix** $\begin{bmatrix} 0 & A \\ A^H & 0 \end{bmatrix}$,
  which the section gives as $\pm\sigma_i(A)$. The statement needs a singular value decomposition,
  which Mathlib does not have.
* **Exercise P-8.4.** It needs a singular value decomposition, which Mathlib does not have.
-/

open Matrix

open scoped SaadSparse ENNReal

namespace SaadSparse.Chapter08

variable {n m : ℕ} {𝕜 : Type*} [RCLike 𝕜]

/-! ### Moving $A$ across the inner product -/

/-- Let $A \in \mathbb{K}^{n \times m}$, $u \in \mathbb{K}^n$ and $v \in \mathbb{K}^m$. In Mathlib's
inner product $\langle x, y \rangle = \sum_i \bar x_i y_i$, $\langle A^H u, v \rangle = \langle
u, Av \rangle$: the conjugate transpose acts as the adjoint. -/
theorem inner_conjTranspose (A : Matrix (Fin n) (Fin m) 𝕜) (u : EuclideanSpace 𝕜 (Fin n))
    (v : EuclideanSpace 𝕜 (Fin m)) : inner 𝕜 (Aᴴ ⬝ u) v = inner 𝕜 u (A ⬝ v) :=
  Matrix.toEuclideanLin_conjTranspose_inner_left A v u

/-- Let $A \in \mathbb{K}^{n \times m}$, $u \in \mathbb{K}^n$ and $v \in \mathbb{K}^m$. In Mathlib's
inner product, $\langle v, A^H u \rangle = \langle Av, u \rangle$, the companion of
`SaadSparse.Chapter08.inner_conjTranspose`. -/
theorem inner_conjTranspose' (A : Matrix (Fin n) (Fin m) 𝕜) (u : EuclideanSpace 𝕜 (Fin n))
    (v : EuclideanSpace 𝕜 (Fin m)) : inner 𝕜 v (Aᴴ ⬝ u) = inner 𝕜 (A ⬝ v) u :=
  Matrix.toEuclideanLin_conjTranspose_inner_right A v u

/-- The range of $A$, the space over which the least-squares problem searches. -/
private def ran (A : Matrix (Fin n) (Fin m) 𝕜) : Submodule 𝕜 (EuclideanSpace 𝕜 (Fin n)) :=
  LinearMap.range (toEuclideanLin A)

private theorem mem_ran (A : Matrix (Fin n) (Fin m) 𝕜) (z : EuclideanSpace 𝕜 (Fin m)) :
    (A ⬝ z) ∈ ran A := ⟨z, rfl⟩

/-! ### (8.1)–(8.2): the normal equations of the least-squares problem -/

/-- $A^H w = 0$ if and only if $w$ is orthogonal to the range of $A$. -/
private theorem conjTranspose_apply_eq_zero_iff (A : Matrix (Fin n) (Fin m) 𝕜)
    (w : EuclideanSpace 𝕜 (Fin n)) : (Aᴴ ⬝ w) = 0 ↔ ∀ z, inner 𝕜 w (A ⬝ z) = (0 : 𝕜) := by
  constructor
  · intro h z
    rw [← inner_conjTranspose, h, inner_zero_left]
  · intro h
    rw [← inner_self_eq_zero (𝕜 := 𝕜), ← inner_conj_symm, inner_conjTranspose, h, map_zero]

/-- **Equations (8.1)–(8.2)** of [saad2003iterative]. Let $A \in \mathbb{K}^{n \times m}$,
$b \in \mathbb{K}^n$ and $x \in \mathbb{K}^m$. Then $x$ solves the normal equations if and only
if it solves the least-squares problem: $$A^H A x = A^H b \iff \|b - Ax\|_2 \le \|b - Ay\|_2
\text{ for all } y \in \mathbb{K}^m.$$

Both directions are the characterization of a best approximation from $\operatorname{Ran} A$ by
the orthogonality of its error, so no rank assumption on $A$ is needed. When the columns of $A$
are independent, $A^H A$ is in addition symmetric positive definite
(`SaadSparse.Chapter08.isSymmetricCoercive_conjTranspose_mul_self`), and the minimizer is
unique.

**Generalization.** The normal equations and least-squares equivalence hold over complex scalars and
without a rank hypothesis. Positive definiteness is stated separately under injectivity, which is
the full-column-rank condition implicit in the book's positive-definiteness claim.
-/
theorem equation_8_1 (A : Matrix (Fin n) (Fin m) 𝕜) (b : EuclideanSpace 𝕜 (Fin n))
    (x : EuclideanSpace 𝕜 (Fin m)) :
    ((Aᴴ * A) ⬝ x) = (Aᴴ ⬝ b) ↔ ∀ y, ‖b - (A ⬝ x)‖ ≤ ‖b - (A ⬝ y)‖ := by
  have hres : ((Aᴴ * A) ⬝ x) = (Aᴴ ⬝ b) ↔ (Aᴴ ⬝ (b - (A ⬝ x))) = 0 := by
    rw [Matrix.toEuclideanLin_mul_apply, map_sub, sub_eq_zero]
    exact eq_comm
  rw [hres, conjTranspose_apply_eq_zero_iff]
  constructor
  · intro h y
    refine Submodule.norm_sub_le_of_forall_inner_eq_zero (K := ran A) (mem_ran A x) ?_
      (mem_ran A y)
    rintro _ ⟨z, rfl⟩
    exact h z
  · intro h z
    exact Submodule.inner_eq_zero_of_forall_norm_sub_le (K := ran A) (mem_ran A x)
      (by rintro _ ⟨y, rfl⟩; exact h y) (mem_ran A z)

/-- **Equation (8.1)** of [saad2003iterative], positive definiteness of $A^H A$. Let
$A \in \mathbb{K}^{n \times m}$ have independent columns, that is, let $x \mapsto Ax$ be
injective. Then $A^H A$ is Hermitian, and there is $c > 0$ with $$c \|x\|_2^2 \le
\operatorname{Re} \, (A^H A x, x) \quad\text{for all } x \in \mathbb{K}^m.$$ Hence the normal
equations have a unique solution. This is the hypothesis under which CGNR (Section 8.3) is well
defined.

The conclusion is `LinearMap.IsSymmetricCoercive` for the operator of $A^H A$.

**Generalization.** The normal equations and least-squares equivalence hold over complex scalars and
without a rank hypothesis. Positive definiteness is stated separately under injectivity, which is
the full-column-rank condition implicit in the book's positive-definiteness claim.
-/
theorem isSymmetricCoercive_conjTranspose_mul_self (A : Matrix (Fin n) (Fin m) 𝕜)
    (hA : Function.Injective (toEuclideanLin A)) :
    (toEuclideanLin (Aᴴ * A)).IsSymmetricCoercive where
  isSymmetric x y := by
    rw [Matrix.toEuclideanLin_mul_apply, Matrix.toEuclideanLin_mul_apply, inner_conjTranspose,
      inner_conjTranspose']
  isCoercive := (LinearMap.isCoercive_iff_forall_pos _).2 fun x hx => by
    rw [Matrix.toEuclideanLin_mul_apply, inner_conjTranspose, inner_self_eq_norm_sq_to_K]
    have hAx : (A ⬝ x) ≠ 0 := fun h => hx (hA (by rw [h, map_zero]))
    simpa using by positivity

/-- **Exercise P-8.10** of [saad2003iterative], the residual. Let $A \in \mathbb{K}^{n \times m}$,
$b \in \mathbb{K}^n$, $x_* \in \mathbb{K}^m$ and $\alpha \in \mathbb{K}$, and let
$r = b - Ax_*$. Then the residual of $x_*$ for the right-hand side $b + \alpha r$ is
$(b + \alpha r) - Ax_* = (1 + \alpha) r$.

**Generalization.** The result allows any aspect ratio and complex perturbation scalars. The
minimizer theorem gives equality of the full sets of minimizers; the residual identity holds at
every point used to define the perturbation.
-/
theorem problem_8_10_residual (A : Matrix (Fin n) (Fin m) 𝕜) (b : EuclideanSpace 𝕜 (Fin n))
    (xstar : EuclideanSpace 𝕜 (Fin m)) (α : 𝕜) :
    (b + α • (b - (A ⬝ xstar))) - (A ⬝ xstar) = (1 + α) • (b - (A ⬝ xstar)) := by
  rw [add_smul, one_smul]
  abel

/-- **Exercise P-8.10** of [saad2003iterative]. Let $A \in \mathbb{K}^{n \times m}$ and
$b \in \mathbb{K}^n$, let $x_* \in \mathbb{K}^m$ minimize $\|b - Ax\|_2$, let $r = b - Ax_*$,
and let $\alpha \in \mathbb{K}$. Then for every $x \in \mathbb{K}^m$, $$x \text{ minimizes }
\|(b + \alpha r) - Ax\|_2 \iff x \text{ minimizes } \|b - Ax\|_2.$$ In particular $x_*$
minimizes the perturbed problem, and its residual is $(1 + \alpha) r$
(`SaadSparse.Chapter08.problem_8_10_residual`).

The reason is (8.1): $r$ is orthogonal to $\operatorname{Ran} A$, so
$A^H (b + \alpha r) = A^H b$, and the two problems have the same normal equations. No rank
assumption is needed. The answer is $x_*$ and not $(1 + \alpha) x_*$: a scaling of the minimizer
would scale $Ax$, but not the component of $b$ orthogonal to $\operatorname{Ran} A$.

**Generalization.** The result allows any aspect ratio and complex perturbation scalars. The
minimizer theorem gives equality of the full sets of minimizers; the residual identity holds at
every point used to define the perturbation.
-/
theorem problem_8_10 (A : Matrix (Fin n) (Fin m) 𝕜) (b : EuclideanSpace 𝕜 (Fin n))
    {xstar : EuclideanSpace 𝕜 (Fin m)} (hstar : ∀ y, ‖b - (A ⬝ xstar)‖ ≤ ‖b - (A ⬝ y)‖) (α : 𝕜)
    (x : EuclideanSpace 𝕜 (Fin m)) :
    (∀ y, ‖(b + α • (b - (A ⬝ xstar))) - (A ⬝ x)‖ ≤ ‖(b + α • (b - (A ⬝ xstar))) - (A ⬝ y)‖) ↔
      ∀ y, ‖b - (A ⬝ x)‖ ≤ ‖b - (A ⬝ y)‖ := by
  have hn : ((Aᴴ * A) ⬝ xstar) = (Aᴴ ⬝ b) := (equation_8_1 A b xstar).2 hstar
  have hr : (Aᴴ ⬝ (b - (A ⬝ xstar))) = 0 := by
    rw [map_sub, ← Matrix.toEuclideanLin_mul_apply, hn, sub_self]
  have hb : (Aᴴ ⬝ (b + α • (b - (A ⬝ xstar)))) = (Aᴴ ⬝ b) := by
    rw [map_add, map_smul, hr, smul_zero, add_zero]
  rw [← equation_8_1, ← equation_8_1, hb]

/-! ### (8.3)–(8.4): the normal equations of the second kind -/

/-- **Equations (8.3)–(8.4)** of [saad2003iterative]. Let $A \in \mathbb{K}^{n \times m}$ and
$b, u \in \mathbb{K}^n$ with $A A^H u = b$, and let $x = A^H u$. Then:

* $Ax = b$;
* $\|x\|_2 \le \|y\|_2$ for every $y \in \mathbb{K}^m$ with $Ay = b$, so $x$ is the solution of
  least Euclidean norm;
* for every solution $x_*$ of $Ax_* = b$, $x$ minimizes $\|x_* - z\|_2$ over
  $z \in \operatorname{Ran} A^H$, which is (8.4).

The third clause is the form that Section 8.3 uses for CGNE. It shows that the choice of the
solution $x_*$ does not change the minimizer. The minimization is `IsMinError xstar 0` over the
range of $A^H$.

**Generalization.** The book assumes full row rank for its underdetermined derivation. Lean only
assumes a solution of the second normal equation, allows any aspect ratio, and states minimal norm
among solutions explicitly. The transpose becomes the adjoint.
-/
theorem equation_8_3 (A : Matrix (Fin n) (Fin m) 𝕜) {b u : EuclideanSpace 𝕜 (Fin n)}
    (hu : ((A * Aᴴ) ⬝ u) = b) :
    (A ⬝ (Aᴴ ⬝ u)) = b ∧ (∀ y, (A ⬝ y) = b → ‖(Aᴴ ⬝ u)‖ ≤ ‖y‖) ∧
      ∀ xstar, (A ⬝ xstar) = b →
        IsMinError xstar 0 (LinearMap.range (toEuclideanLin Aᴴ)) (Aᴴ ⬝ u) := by
  have hsol : (A ⬝ (Aᴴ ⬝ u)) = b := by rw [← Matrix.toEuclideanLin_mul_apply, hu]
  have horth : ∀ xstar : EuclideanSpace 𝕜 (Fin m), (A ⬝ xstar) = b →
      ∀ w ∈ LinearMap.range (toEuclideanLin Aᴴ),
        inner 𝕜 (xstar - (Aᴴ ⬝ u)) w = (0 : 𝕜) := by
    rintro xstar hx _ ⟨z, rfl⟩
    rw [show (toEuclideanLin Aᴴ) z = (Aᴴ ⬝ z) from rfl, inner_conjTranspose', map_sub, hx, hsol,
      sub_self, inner_zero_left]
  refine ⟨hsol, fun y hy => ?_, fun xstar hx => ⟨by rw [sub_zero]; exact ⟨u, rfl⟩, fun w hw => ?_⟩⟩
  · have h0 : inner 𝕜 (Aᴴ ⬝ u) (y - (Aᴴ ⬝ u)) = (0 : 𝕜) := by
      rw [inner_conjTranspose, map_sub, hy, hsol, sub_self, inner_zero_right]
    have hsum : ‖(Aᴴ ⬝ u) + (y - (Aᴴ ⬝ u))‖ * ‖(Aᴴ ⬝ u) + (y - (Aᴴ ⬝ u))‖
        = ‖(Aᴴ ⬝ u)‖ * ‖(Aᴴ ⬝ u)‖ + ‖y - (Aᴴ ⬝ u)‖ * ‖y - (Aᴴ ⬝ u)‖ :=
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ h0
    rw [show (Aᴴ ⬝ u) + (y - (Aᴴ ⬝ u)) = y from by abel] at hsum
    nlinarith [norm_nonneg y, norm_nonneg (Aᴴ ⬝ u), norm_nonneg (y - (Aᴴ ⬝ u))]
  · rw [sub_zero] at hw
    exact Submodule.norm_sub_le_of_forall_inner_eq_zero
      (K := LinearMap.range (toEuclideanLin Aᴴ)) ⟨u, rfl⟩ (horth xstar hx) hw

/-! ### (8.5)–(8.7): the augmented system -/

/-- **Equations (8.5)–(8.7)** and **exercise P-8.1** of [saad2003iterative]. Let
$A \in \mathbb{K}^{n \times m}$, $b, r \in \mathbb{K}^n$ and $x \in \mathbb{K}^m$. Then
$$\begin{bmatrix} I & A \\ A^H & 0 \end{bmatrix} \begin{bmatrix} r \\ x \end{bmatrix} =
\begin{bmatrix} b \\ 0 \end{bmatrix}$$ if and only if $r = b - Ax$ and $x$ solves the
least-squares problem (8.2), that is, $\|b - Ax\|_2 \le \|b - Ay\|_2$ for all
$y \in \mathbb{K}^m$. The second block equation $A^H r = 0$ is the constraint of the problem
"minimize $\frac{1}{2} \|r - b\|_2^2$ subject to $A^H r = 0$", and $x$ is its vector of Lagrange
multipliers.

The block matrix is `Matrix.fromBlocks 1 A Aᴴ 0`, indexed by `Fin n ⊕ Fin m`, and the pair
$(r, x)$ is `Sum.elim` of the two coordinate vectors.

**Reading.** The block equation is characterized by the residual and least-squares optimality, using
the complex adjoint. The interpretation of the second block as a Lagrange multiplier of the
constrained problem is described in prose.
-/
theorem equation_8_5 (A : Matrix (Fin n) (Fin m) 𝕜) (b r : EuclideanSpace 𝕜 (Fin n))
    (x : EuclideanSpace 𝕜 (Fin m)) :
    Matrix.fromBlocks 1 A Aᴴ 0 *ᵥ Sum.elim (WithLp.ofLp r) (WithLp.ofLp x)
        = Sum.elim (WithLp.ofLp b) 0 ↔
      r = b - (A ⬝ x) ∧ ∀ y, ‖b - (A ⬝ x)‖ ≤ ‖b - (A ⬝ y)‖ := by
  have hblk : Matrix.fromBlocks 1 A Aᴴ 0 *ᵥ Sum.elim (WithLp.ofLp r) (WithLp.ofLp x)
      = Sum.elim (WithLp.ofLp r + A *ᵥ WithLp.ofLp x) (Aᴴ *ᵥ WithLp.ofLp r) := by
    rw [Matrix.fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.one_mulVec,
      Matrix.zero_mulVec, add_zero]
  have h1 : WithLp.ofLp r + A *ᵥ WithLp.ofLp x = WithLp.ofLp b ↔ r = b - (A ⬝ x) := by
    constructor
    · intro h
      refine WithLp.ofLp_injective 2 ?_
      rw [WithLp.ofLp_sub, Matrix.ofLp_toEuclideanLin]
      exact eq_sub_of_add_eq h
    · intro h
      rw [h, WithLp.ofLp_sub, Matrix.ofLp_toEuclideanLin, sub_add_cancel]
  rw [hblk, Sum.elim_eq_iff, h1]
  refine and_congr_right fun hr => ?_
  have h2 : Aᴴ *ᵥ WithLp.ofLp r = WithLp.ofLp (Aᴴ ⬝ (b - (A ⬝ x))) := by rw [hr]; rfl
  rw [h2, ← WithLp.ofLp_zero (p := 2), (WithLp.ofLp_injective 2).eq_iff,
    ← equation_8_1, Matrix.toEuclideanLin_mul_apply, map_sub, sub_eq_zero]
  exact eq_comm

/-! ### (8.8): the squared condition number -/

open scoped Matrix.Norms.L2Operator in
/-- In the spectral norm, $\|B B^H\|_2 = \|B\|_2^2$, the companion of Mathlib's
`Matrix.l2_opNorm_conjTranspose_mul_self`. -/
private theorem l2_opNorm_self_mul_conjTranspose (B : Matrix (Fin n) (Fin m) 𝕜) :
    ‖B * Bᴴ‖ = ‖B‖ * ‖B‖ := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self (Bᴴ)
  rwa [Matrix.conjTranspose_conjTranspose, Matrix.l2_opNorm_conjTranspose] at h

open scoped Matrix.Norms.L2Operator in
/-- **Equation (8.8)** of [saad2003iterative]. For every $A \in \mathbb{K}^{n \times n}$,
$$\kappa_2(A^H A) = \kappa_2(A)^2,$$ where $\kappa_2(B) = \|B\|_2 \|B^{-1}\|_2$. Passing to the
normal equations squares the condition number. This is the reason of the chapter for the row
projection methods of Section 8.2, and for running CG on $A^H A$ without forming this matrix
(Section 8.3).

**Generalization.** The source states the identity for a nonsingular $A$. Here there is no
hypothesis: for a singular $A$, Lean's inverse is $0$, so both sides are $0$.

The condition number is `Matrix.condNumberLp 2`.

**Generalization.** The equation also holds for singular square matrices: Lean's singular inverse is
zero and hence its condition number is zero. It uses the adjoint over complex scalars.
-/
theorem equation_8_8 (A : Matrix (Fin n) (Fin n) 𝕜) :
    Matrix.condNumberLp 2 (Aᴴ * A) = Matrix.condNumberLp 2 A ^ 2 := by
  have hinv : (Aᴴ * A)⁻¹ = A⁻¹ * (A⁻¹)ᴴ := by
    rw [Matrix.mul_inv_rev, Matrix.conjTranspose_nonsing_inv]
  rw [Matrix.condNumberLp, Matrix.condNumberLp, Matrix.lpOpNorm_two, Matrix.lpOpNorm_two,
    Matrix.lpOpNorm_two, Matrix.lpOpNorm_two, hinv, Matrix.l2_opNorm_conjTranspose_mul_self,
    l2_opNorm_self_mul_conjTranspose]
  ring

end SaadSparse.Chapter08
