/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Numlib.Analysis.InnerProductSpace.Coercive
import Numlib.Analysis.InnerProductSpace.Energy
import Numlib.Analysis.Matrix.ToEuclideanLin
import Numlib.LinearAlgebra.Matrix.NonsingularInverse
import Numlib.Projection.Basic
import Numlib.Projection.OneDimensional
import NumlibSurface.SaadSparse.Chapter05.Section01

/-!
# Saad, Section 5.3: One-dimensional projection processes

This module formalizes §5.3 of [saad2003iterative], the projection methods for $Ax = b$ with
$A \in \mathbb{R}^{n \times n}$ in which $K = \operatorname{span}\{v\}$ and
$L = \operatorname{span}\{w\}$ are lines. One step from $x$, with residual $r = b - Ax$, is
$$x \mapsto x + \frac{(w, r)}{(w, Av)} \, v \qquad (5.12).$$
Steepest descent (Algorithm 5.2) takes $v = w = r$; for symmetric positive definite $A$ it reduces
the $A$-norm of the error by the factor $(\lambda_{\max} - \lambda_{\min})/(\lambda_{\max} +
\lambda_{\min})$ at each step (Theorem 5.9), by Kantorovich's inequality (Lemma 5.8). The minimal
residual iteration (Algorithm 5.3) takes $v = r$, $w = Ar$; for positive definite $A$ it reduces the
residual norm by the factor $(1 - \mu^2/\sigma^2)^{1/2}$ with $\mu = \lambda_{\min}((A + A^T)/2)$
and $\sigma = \|A\|_2$ (Theorem 5.10). The residual norm steepest descent (Algorithm 5.4) takes
$v = A^Tr$, $w = Av$; it is steepest descent for the normal equations $A^TAx = A^Tb$.

The module also proves the exact one-step identities (5.16)–(5.18) and the bound (5.20), the
convergence factor $\rho = \sup_{x \neq 0} \sin \angle(x, Ax)$ of §5.3.2, Example 5.1, and that
Algorithms 5.2–5.4 as printed, with a recursively updated residual, compute the projection iterates.
All three steps are `Projection.step1` of the backbone for `Matrix.toEuclideanLin A`, so the
estimates specialize `Numlib.Projection.OneDimensional`.

## Main definitions

* Equation (5.12), `SaadSparse.Chapter05.step1`: the one-dimensional projection step onto
  $\operatorname{span}\{v\}$ orthogonally to $\operatorname{span}\{w\}$.
* Algorithm 5.2, `SaadSparse.Chapter05.sdStep` and `SaadSparse.Chapter05.sdAlgStep`: the steepest
  descent step, and the algorithm as printed.
* Algorithm 5.3, `SaadSparse.Chapter05.mrStep` and `SaadSparse.Chapter05.mrAlgStep`: the minimal
  residual step, and the algorithm as printed.
* Algorithm 5.4, `SaadSparse.Chapter05.rnsdStep` and `SaadSparse.Chapter05.rnsdAlgStep`: the
  residual norm steepest descent step, and the algorithm as printed.
* §5.3.2, `SaadSparse.Chapter05.sinAngleSup`: the convergence factor
  $\rho = \sup_{x \neq 0} \sin \angle(x, Ax)$.

## Main results

* Example 5.1, `SaadSparse.Chapter05.example_5_1`: the projection step onto
  $K = L = \operatorname{span}\{e_i\}$ is the elementary relaxation step
  $x \mapsto x + (r_i/a_{ii}) e_i$.
* Lemma 5.8, `SaadSparse.Chapter05.lemma_5_8`: Kantorovich's inequality.
* Theorem 5.9, `SaadSparse.Chapter05.theorem_5_9` and `SaadSparse.Chapter05.theorem_5_9_tendsto`:
  the $A$-norm of the error of steepest descent decreases geometrically, and the iterates converge.
* Equations (5.16)–(5.18), `SaadSparse.Chapter05.equation_5_18` and
  `SaadSparse.Chapter05.norm_residual_mrStep_eq_sin`: the exact one-step residual identity of the
  minimal residual iteration, and its form $\|r_{k+1}\|_2 = \|r_k\|_2 \sin \angle(r_k, Ar_k)$.
* Theorem 5.10, `SaadSparse.Chapter05.theorem_5_10` and `SaadSparse.Chapter05.theorem_5_10_tendsto`:
  the residual norm of the minimal residual iteration decreases geometrically, and the iterates
  converge.
* Equation (5.20), `SaadSparse.Chapter05.equation_5_20`: $\|r_{k+1}\|_2^2 \le (1 -
  \mu(A)\mu(A^{-1})) \|r_k\|_2^2$.
* §5.3.2, `SaadSparse.Chapter05.norm_mrStep_le_sup_sin`: the minimal residual iteration reduces the
  residual norm by the factor $\rho < 1$.
* Algorithm 5.4, `SaadSparse.Chapter05.rnsdStep_min` and `SaadSparse.Chapter05.rnsd_tendsto`: each
  step minimizes the residual norm on its line, and the iterates converge for nonsingular $A$.
* Algorithms 5.2–5.4, `SaadSparse.Chapter05.sdAlg_spec`, `SaadSparse.Chapter05.mrAlg_spec`,
  `SaadSparse.Chapter05.rnsdAlg_spec`: the algorithms as printed compute the projection iterates and
  carry the true residual.

## Implementation notes

* "$A$ is positive definite" is the definition of the book, `Matrix.IsPositiveReal`: $(Au, u) > 0$
  for every $u \neq 0$, with no symmetry. "Symmetric positive definite" is Mathlib's
  `Matrix.PosDef`.
* The smallest and largest eigenvalues $\lambda_{\min}$ and $\lambda_{\max}$ of a symmetric matrix
  are `SaadSparse.lambdaMin` and `SaadSparse.lambdaMax`, which need $n \ge 1$.
* The norm $\sigma = \|A\|_2$ is the norm of the scoped instance `Matrix.Norms.L2Operator`. The
  angle $\angle(x, y)$ is `InnerProductGeometry.angle`.
* Equation (5.20) of the book is the residual bound `SaadSparse.Chapter05.equation_5_20` of §5.3.2.
  The exact identity for the $A$-norm of the error of steepest descent,
  `SaadSparse.Chapter05.energyNorm_sdStep_sq_eq`, is the last display in the proof of Theorem 5.9,
  which the book does not number.
-/

open Matrix Module Filter Topology
open scoped SaadSparse

namespace SaadSparse.Chapter05

variable {n : ℕ}

/-- The notation `E n` stands for `EuclideanSpace ℝ (Fin n)`, the space $\mathbb{R}^n$ of Chapter 5.
-/
local notation "E" n => EuclideanSpace ℝ (Fin n)

variable {A : Matrix (Fin n) (Fin n) ℝ} {b x₀ x : E n}

/-! ### The elementary step (5.12) -/

/-- **Equation (5.12)** of [saad2003iterative]. For $A \in \mathbb{R}^{n \times n}$ and
$b, v, w \in \mathbb{R}^n$, the **one-dimensional projection step** onto
$\operatorname{span}\{v\}$ orthogonally to $\operatorname{span}\{w\}$ from $x$ is
$$x \mapsto x + \frac{(w, r)}{(w, Av)} \, v, \qquad r = b - Ax.$$

If $(w, Av) = 0$, the quotient is $0$ in Lean, and the step returns $x$. -/
noncomputable def step1 (A : Matrix (Fin n) (Fin n) ℝ) (b v w x : E n) : E n :=
  x + (inner ℝ w (b - (A ⬝ x)) / inner ℝ w (A ⬝ v)) • v

/-- The step (5.12) of [saad2003iterative] is `Projection.step1` of the backbone for the operator
`Matrix.toEuclideanLin A`. -/
theorem step1_eq (A : Matrix (Fin n) (Fin n) ℝ) (b v w x : E n) :
    step1 A b v w x = Projection.step1 (toEuclideanLin A) b v w x := rfl

/-- Equation (5.12) of [saad2003iterative]: if $(w, Av) \neq 0$, the step is a projection
approximation onto $\operatorname{span}\{v\}$ orthogonally to $\operatorname{span}\{w\}$,
starting from $x$. -/
theorem step1_isProjectionApprox (v w : E n) (h : inner ℝ w (A ⬝ v) ≠ 0) :
    IsProjectionApprox A b x (ℝ ∙ v) (ℝ ∙ w) (step1 A b v w x) :=
  isProjectionApprox_iff.mpr (Projection.step1_isPetrovGalerkin v w x h)

/-- Equation (5.12) of [saad2003iterative]: if $(w, Av) \neq 0$, the step is the only projection
approximation onto $\operatorname{span}\{v\}$ orthogonally to $\operatorname{span}\{w\}$,
starting from $x$. -/
theorem isProjectionApprox_span_singleton_iff {v w x' : E n} (h : inner ℝ w (A ⬝ v) ≠ 0) :
    IsProjectionApprox A b x (ℝ ∙ v) (ℝ ∙ w) x' ↔ x' = step1 A b v w x := by
  refine ⟨fun hx' => ?_, fun hx' => hx' ▸ step1_isProjectionApprox v w h⟩
  refine (isProjectionApprox_iff.mp hx').eq_of_forall
    (isProjectionApprox_iff.mp (step1_isProjectionApprox v w h)) fun z hz hAz => ?_
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
  have h0 : inner ℝ w (toEuclideanLin A (c • v)) = 0 :=
    (Submodule.mem_orthogonal _ _).1 hAz w (Submodule.mem_span_singleton_self w)
  rw [map_smul, inner_smul_right] at h0
  rcases mul_eq_zero.mp h0 with hc | hcon
  · rw [hc, zero_smul]
  · exact absurd hcon h

/-! ### Steepest descent (Algorithm 5.2) and minimal residual (Algorithm 5.3) -/

/-- **Algorithm 5.2** of [saad2003iterative], the step. The **steepest descent step** from $x$ is
the step (5.12) with $v = w = r$, where $r = b - Ax$:
$$x \mapsto x + \frac{(r, r)}{(r, Ar)} \, r.$$
-/
noncomputable def sdStep (A : Matrix (Fin n) (Fin n) ℝ) (b x : E n) : E n :=
  step1 A b (b - (A ⬝ x)) (b - (A ⬝ x)) x

/-- **Algorithm 5.3** of [saad2003iterative], the step. The **minimal residual step** from $x$ is
the step (5.12) with $v = r$ and $w = Ar$, where $r = b - Ax$:
$$x \mapsto x + \frac{(Ar, r)}{(Ar, Ar)} \, r.$$
-/
noncomputable def mrStep (A : Matrix (Fin n) (Fin n) ℝ) (b x : E n) : E n :=
  step1 A b (b - (A ⬝ x)) (A ⬝ (b - (A ⬝ x))) x

/-- **Algorithm 5.4** of [saad2003iterative], the step. The **residual norm steepest descent step**
from $x$ is the step (5.12) with $v = A^Tr$ and $w = Av$, where $r = b - Ax$. -/
noncomputable def rnsdStep (A : Matrix (Fin n) (Fin n) ℝ) (b x : E n) : E n :=
  step1 A b (Aᵀ ⬝ (b - (A ⬝ x))) (A ⬝ (Aᵀ ⬝ (b - (A ⬝ x)))) x

/-- The steepest descent step is `Projection.steepestDescentStep` of the backbone for the operator
of $A$. -/
theorem sdStep_eq (A : Matrix (Fin n) (Fin n) ℝ) (b x : E n) :
    sdStep A b x = Projection.steepestDescentStep (toEuclideanLin A) b x := rfl

/-- The minimal residual step is `Projection.minResStep` of the backbone for the operator of $A$. -/
theorem mrStep_eq (A : Matrix (Fin n) (Fin n) ℝ) (b x : E n) :
    mrStep A b x = Projection.minResStep (toEuclideanLin A) b x := rfl

/-- Algorithm 5.2 of [saad2003iterative]: if $A$ is positive definite, each steepest descent step is
a projection approximation onto $\operatorname{span}\{r\}$ orthogonally to
$\operatorname{span}\{r\}$, where $r = b - Ax$. -/
theorem sdStep_isProjectionApprox (hA : A.IsPositiveReal) (b x : E n) :
    IsProjectionApprox A b x (ℝ ∙ (b - (A ⬝ x))) (ℝ ∙ (b - (A ⬝ x))) (sdStep A b x) :=
  isProjectionApprox_iff.mpr
    (Projection.steepestDescentStep_isGalerkin x ((Matrix.isPositiveReal_iff_isCoercive A).mp hA))

/-- Algorithm 5.2 of [saad2003iterative]: if $A$ is symmetric positive definite and $Ax^* = b$, the
steepest descent step from $x$ minimizes the error functional $E$ over the line
$x + \operatorname{span}\{r\}$. -/
theorem sdStep_min (hA : A.PosDef) {xstar : E n} (hstar : (A ⬝ xstar) = b) (x y : E n)
    (hy : y - x ∈ (ℝ ∙ (b - (A ⬝ x)))) : E_A A xstar (sdStep A b x) ≤ E_A A xstar y := by
  have hpr : A.IsPositiveReal := by
    rw [Matrix.isPositiveReal_iff_isCoercive]
    exact ((Matrix.posDef_iff_isSymmetricCoercive A).mp hA).isCoercive
  exact ((proposition_5_2 hA hstar).mp (sdStep_isProjectionApprox hpr b x)).2 y hy

/-- Algorithm 5.3 of [saad2003iterative]: for every $A$, the minimal residual step from $x$
minimizes the residual norm $\|b - Ay\|_2$ over the line $y \in x + \operatorname{span}\{r\}$. -/
theorem mrStep_min (b x y : E n)
    (hy : y - x ∈ (ℝ ∙ (b - (A ⬝ x)))) : R_A A b (mrStep A b x) ≤ R_A A b y :=
  (Projection.minResStep_isMinResidual x).min y hy

/-! ### Lemma 5.8 (Kantorovich) -/

variable [NeZero n]

/-- For a symmetric positive definite $B$, $\lambda_{\min}(B) > 0$, because every eigenvalue of $B$
is positive. -/
private theorem lambdaMin_pos {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.PosDef) :
    0 < lambdaMin hB.1 := by
  rw [lambdaMin, Finset.lt_inf'_iff]
  exact fun i _ => Matrix.PosDef.eigenvalues_pos hB i

/-- **Lemma 5.8** of [saad2003iterative] (Kantorovich inequality). Let
$B \in \mathbb{R}^{n \times n}$, $n \ge 1$, be symmetric positive definite with smallest and
largest eigenvalues $\lambda_{\min}$ and $\lambda_{\max}$. Then for every $x \in \mathbb{R}^n$,
$$(Bx, x)(B^{-1}x, x) \le \frac{(\lambda_{\max} + \lambda_{\min})^2}{4 \lambda_{\max}
  \lambda_{\min}} (x, x)^2.$$
-/
theorem lemma_5_8 {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.PosDef) (x : Fin n → ℝ) :
    ((B *ᵥ x) ⬝ᵥ x) * ((B⁻¹ *ᵥ x) ⬝ᵥ x) ≤
      (lambdaMax hB.1 + lambdaMin hB.1) ^ 2 / (4 * lambdaMax hB.1 * lambdaMin hB.1) *
        (x ⬝ᵥ x) ^ 2 := by
  have hl : 0 < lambdaMin hB.1 := lambdaMin_pos hB
  have hsb := isSymmetricBoundedBy_toEuclideanLin hB.1
  have hBB : B *ᵥ (B⁻¹ *ᵥ x) = x := mulVec_nonsing_inv_mulVec hB.isUnit x
  have hy : toEuclideanLin B (WithLp.toLp 2 (B⁻¹ *ᵥ x)) = (WithLp.toLp 2 x : E n) :=
    congrArg (WithLp.toLp 2) hBB
  have hk := Projection.kantorovich_inequality hl hsb (WithLp.toLp 2 x : E n) hy
  rw [real_inner_apply_self] at hk
  have h1 : (inner ℝ (WithLp.toLp 2 (B⁻¹ *ᵥ x) : E n) (WithLp.toLp 2 x : E n))
      = (B⁻¹ *ᵥ x) ⬝ᵥ x := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
    simp
  have h4 : ‖(WithLp.toLp 2 x : E n)‖ ^ 4 = (x ⬝ᵥ x) ^ 2 := by
    have h2 : ‖(WithLp.toLp 2 x : E n)‖ ^ 2 = x ⬝ᵥ x := real_norm_sq_eq_dotProduct _
    calc ‖(WithLp.toLp 2 x : E n)‖ ^ 4 = (‖(WithLp.toLp 2 x : E n)‖ ^ 2) ^ 2 := by ring
      _ = (x ⬝ᵥ x) ^ 2 := by rw [h2]
  rw [h1, h4] at hk
  simpa [RCLike.re_to_real] using hk

/-! ### Theorem 5.9 -/

/-- **Theorem 5.9** of [saad2003iterative], one step. Let $A \in \mathbb{R}^{n \times n}$,
$n \ge 1$, be symmetric positive definite, and let $Ax^* = b$. Then for every $x$ the steepest
descent step $x'$ satisfies
$$E(x') \le \frac{\lambda_{\max} - \lambda_{\min}}{\lambda_{\max} + \lambda_{\min}} \, E(x),$$
where $E$ is the error functional $E(x) = (A(x^* - x), x^* - x)^{1/2}$ and $\lambda_{\min}$,
$\lambda_{\max}$ are the extreme eigenvalues of $A$. -/
theorem theorem_5_9_step (hA : A.PosDef) {xstar : E n} (hstar : (A ⬝ xstar) = b) (x : E n) :
    E_A A xstar (sdStep A b x) ≤
      (lambdaMax hA.1 - lambdaMin hA.1) / (lambdaMax hA.1 + lambdaMin hA.1) *
        E_A A xstar x :=
  Projection.energyNorm_steepestDescentStep_le (lambdaMin_pos hA)
    (isSymmetricBoundedBy_toEuclideanLin hA.1) hstar x

/-- **Theorem 5.9** of [saad2003iterative], the factor. For a symmetric positive definite
$H \in \mathbb{R}^{n \times n}$, $n \ge 1$, the contraction factor satisfies
$$0 \le \frac{\lambda_{\max} - \lambda_{\min}}{\lambda_{\max} + \lambda_{\min}} < 1.$$
-/
theorem theorem_5_9_factor_lt_one {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.PosDef) :
    0 ≤ (lambdaMax hH.1 - lambdaMin hH.1) / (lambdaMax hH.1 + lambdaMin hH.1) ∧
      (lambdaMax hH.1 - lambdaMin hH.1) / (lambdaMax hH.1 + lambdaMin hH.1) < 1 := by
  have hl : 0 < lambdaMin hH.1 := lambdaMin_pos hH
  have hle : lambdaMin hH.1 ≤ lambdaMax hH.1 := lambdaMin_le_lambdaMax hH.1
  have hsum : 0 < lambdaMax hH.1 + lambdaMin hH.1 := by linarith
  refine ⟨div_nonneg (by linarith) hsum.le, ?_⟩
  rw [div_lt_one hsum]
  linarith

/-- **Theorem 5.9** of [saad2003iterative]. Let $A \in \mathbb{R}^{n \times n}$, $n \ge 1$, be
symmetric positive definite, and let $Ax^* = b$. Then for every $x_0$ and $k \ge 0$ the iterates
$x_k$ of Algorithm 5.2 satisfy
$$E(x_k) \le \left( \frac{\lambda_{\max} - \lambda_{\min}}{\lambda_{\max} + \lambda_{\min}}
  \right)^k E(x_0).$$

The proof specializes `Projection.energyNorm_iterate_steepestDescentStep_le`. -/
theorem theorem_5_9 (hA : A.PosDef) {xstar : E n} (hstar : (A ⬝ xstar) = b) (x₀ : E n) (k : ℕ) :
    E_A A xstar ((sdStep A b)^[k] x₀) ≤
      ((lambdaMax hA.1 - lambdaMin hA.1) / (lambdaMax hA.1 + lambdaMin hA.1)) ^ k *
        E_A A xstar x₀ :=
  Projection.energyNorm_iterate_steepestDescentStep_le (lambdaMin_pos hA)
    (isSymmetricBoundedBy_toEuclideanLin hA.1) hstar x₀ k

/-- **Theorem 5.9** of [saad2003iterative], convergence. Let $A \in \mathbb{R}^{n \times n}$,
$n \ge 1$, be symmetric positive definite, and let $Ax^* = b$. Then the iterates of Algorithm
5.2 converge to $x^*$ from every starting vector.

The proof specializes `Projection.tendsto_iterate_steepestDescentStep`. -/
theorem theorem_5_9_tendsto (hA : A.PosDef) {xstar : E n} (hstar : (A ⬝ xstar) = b) (x₀ : E n) :
    Tendsto (fun k => (sdStep A b)^[k] x₀) atTop (𝓝 xstar) :=
  Projection.tendsto_iterate_steepestDescentStep (lambdaMin_pos hA)
    (isSymmetricBoundedBy_toEuclideanLin hA.1) hstar x₀

/-! ### Theorem 5.10 -/

omit [NeZero n] in
/-- If $A$ is positive definite, its symmetric part $(A + A^T)/2$ is symmetric positive definite. -/
theorem posDef_hermitianPart (hA : A.IsPositiveReal) : (Matrix.hermitianPart A).PosDef := by
  rw [Matrix.posDef_iff_isSymmetricCoercive]
  obtain ⟨c, hc, hcA⟩ := (Matrix.isPositiveReal_iff_isCoercive A).mp hA
  refine ⟨isSymmetric_toEuclideanLin_iff.mpr (Matrix.hermitianPart_isHermitian A), c, hc, ?_⟩
  intro u
  rw [Matrix.re_inner_hermitianPart A u]
  exact hcA u

/-- Theorem 5.10 of [saad2003iterative]: if $A$ is positive definite and $n \ge 1$, then
$\mu = \lambda_{\min}((A + A^T)/2) > 0$. -/
theorem lambdaMin_hermitianPart_pos (hA : A.IsPositiveReal) :
    0 < lambdaMin (Matrix.hermitianPart_isHermitian A) :=
  lambdaMin_pos (posDef_hermitianPart hA)

open scoped Matrix.Norms.L2Operator in
/-- **Theorem 5.10** of [saad2003iterative], one step. Let $A \in \mathbb{R}^{n \times n}$,
$n \ge 1$, be positive definite, and let $\mu = \lambda_{\min}((A + A^T)/2)$ and
$\sigma = \|A\|_2$. Then for every $b$ and $x$ the minimal residual step $x'$ satisfies
$$\|b - Ax'\|_2 \le \left( 1 - \frac{\mu^2}{\sigma^2} \right)^{1/2} \|b - Ax\|_2.$$
-/
theorem theorem_5_10_step (hA : A.IsPositiveReal) (b x : E n) :
    ‖b - (A ⬝ mrStep A b x)‖ ≤
      Real.sqrt (1 - lambdaMin (Matrix.hermitianPart_isHermitian A) ^ 2 / ‖A‖ ^ 2) *
        ‖b - (A ⬝ x)‖ := by
  have hpos := lambdaMin_hermitianPart_pos hA
  have hcoer := Chapter01.isCoerciveWith_lambdaMin A
  rw [Matrix.l2_opNorm_eq_norm_toEuclideanLin A]
  exact Projection.norm_residual_minResStep_le
    (A := LinearMap.toContinuousLinearMap (toEuclideanLin A)) hpos hcoer b x

open scoped Matrix.Norms.L2Operator in
/-- Theorem 5.10 of [saad2003iterative]: for every $A \in \mathbb{R}^{n \times n}$ with $n \ge 1$,
$\mu = \lambda_{\min}((A + A^T)/2) \le \sigma = \|A\|_2$, because $\mu$ is a lower bound of
$(Au, u)/(u, u) \le \|Au\|_2/\|u\|_2$. So the factor of Theorem 5.10 is real and less than $1$. -/
theorem lambdaMin_hermitianPart_le_opNorm (A : Matrix (Fin n) (Fin n) ℝ) :
    lambdaMin (Matrix.hermitianPart_isHermitian A) ≤ ‖A‖ := by
  obtain ⟨i⟩ : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩⟩
  set u : E n := EuclideanSpace.single i (1 : ℝ) with hudef
  have hu : ‖u‖ = 1 := by simp [hudef]
  have h1 := (Chapter01.isCoerciveWith_lambdaMin A).norm_le_norm_apply u
  have h2 : ‖LinearMap.toContinuousLinearMap (toEuclideanLin A) u‖
      ≤ ‖LinearMap.toContinuousLinearMap (toEuclideanLin A)‖ * ‖u‖ :=
    ContinuousLinearMap.le_opNorm _ u
  have heq : LinearMap.toContinuousLinearMap (toEuclideanLin A) u = (A ⬝ u) := rfl
  rw [heq, hu, mul_one] at h2
  rw [hu, mul_one] at h1
  rw [Matrix.l2_opNorm_eq_norm_toEuclideanLin A]
  linarith

open scoped Matrix.Norms.L2Operator in
/-- Theorem 5.10 of [saad2003iterative]: if $A$ is positive definite and $n \ge 1$, the contraction
factor satisfies $(1 - \mu^2/\sigma^2)^{1/2} < 1$. -/
theorem theorem_5_10_factor_lt_one (hA : A.IsPositiveReal) :
    Real.sqrt (1 - lambdaMin (Matrix.hermitianPart_isHermitian A) ^ 2 / ‖A‖ ^ 2) < 1 := by
  have hpos := lambdaMin_hermitianPart_pos hA
  have hnorm : 0 < ‖A‖ := lt_of_lt_of_le hpos (lambdaMin_hermitianPart_le_opNorm A)
  have hfrac : 0 < lambdaMin (Matrix.hermitianPart_isHermitian A) ^ 2 / ‖A‖ ^ 2 := by positivity
  rw [Real.sqrt_lt' one_pos, one_pow]
  linarith

open scoped Matrix.Norms.L2Operator in
/-- **Theorem 5.10** of [saad2003iterative]. Let $A \in \mathbb{R}^{n \times n}$, $n \ge 1$, be
positive definite, and let $\mu = \lambda_{\min}((A + A^T)/2)$ and $\sigma = \|A\|_2$. Then for
every $b$, $x_0$ and $k \ge 0$ the residuals $r_k = b - Ax_k$ of Algorithm 5.3 satisfy
$$\|r_k\|_2 \le \left( 1 - \frac{\mu^2}{\sigma^2} \right)^{k/2} \|r_0\|_2.$$
-/
theorem theorem_5_10 (hA : A.IsPositiveReal) (b x₀ : E n) (k : ℕ) :
    ‖b - (A ⬝ ((mrStep A b)^[k] x₀))‖ ≤
      Real.sqrt (1 - lambdaMin (Matrix.hermitianPart_isHermitian A) ^ 2 / ‖A‖ ^ 2) ^ k *
        ‖b - (A ⬝ x₀)‖ := by
  set ρ := Real.sqrt (1 - lambdaMin (Matrix.hermitianPart_isHermitian A) ^ 2 / ‖A‖ ^ 2) with hρ
  have hnn : 0 ≤ ρ := Real.sqrt_nonneg _
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', pow_succ]
    refine (theorem_5_10_step hA b _).trans ?_
    calc ρ * ‖b - (A ⬝ ((mrStep A b)^[k] x₀))‖
        ≤ ρ * (ρ ^ k * ‖b - (A ⬝ x₀)‖) := mul_le_mul_of_nonneg_left ih hnn
      _ = ρ ^ k * ρ * ‖b - (A ⬝ x₀)‖ := by ring

/-- **Theorem 5.10** of [saad2003iterative], convergence. Let $A \in \mathbb{R}^{n \times n}$,
$n \ge 1$, be positive definite. Then for every $b$ the iterates of Algorithm 5.3 converge to
$A^{-1}b$ from every starting vector.

The coercivity bound $\mu \|x\|_2 \le \|Ax\|_2$ controls the error by the residual, so the
geometric decay of `SaadSparse.Chapter05.theorem_5_10` carries over to the iterates. -/
theorem theorem_5_10_tendsto (hA : A.IsPositiveReal) (b x₀ : E n) :
    Tendsto (fun k => (mrStep A b)^[k] x₀) atTop (𝓝 (A⁻¹ ⬝ b)) := by
  have hpos := lambdaMin_hermitianPart_pos hA
  have hstar : (A ⬝ (A⁻¹ ⬝ b)) = b :=
    toEuclideanLin_mul_nonsing_inv_apply (Chapter01.theorem_1_34 hA).1 b
  have hres : ∀ y : E n, (A ⬝ ((A⁻¹ ⬝ b) - y)) = b - (A ⬝ y) := fun y => by
    rw [map_sub, hstar]
  refine Projection.tendsto_of_forall_norm_succ_le
    (N := fun v => ‖(A ⬝ v)‖) (C := (lambdaMin (Matrix.hermitianPart_isHermitian A))⁻¹)
    (fun v => ?_) (fun _ => norm_nonneg _) (Real.sqrt_nonneg _)
    (theorem_5_10_factor_lt_one hA) (fun k => ?_)
  · have h := (Chapter01.isCoerciveWith_lambdaMin A).norm_le_norm_apply v
    rw [inv_mul_eq_div, le_div_iff₀ hpos]
    linarith
  · simp only [hres, Function.iterate_succ_apply']
    exact theorem_5_10_step hA b _

/-! ### Algorithm 5.4 -/

omit [NeZero n] in
/-- Over $\mathbb{R}$, $A^T$ is the adjoint of $A$: $(Au, v) = (u, A^Tv)$. -/
theorem real_inner_transpose (A : Matrix (Fin n) (Fin n) ℝ) (u v : E n) :
    inner ℝ (A ⬝ u) v = inner ℝ u (Aᵀ ⬝ v) := by
  rw [real_inner_apply, real_inner_toEuclideanLin', dotProduct_mulVec, mulVec_transpose]

omit [NeZero n] in
/-- §5.3.3 of [saad2003iterative]: if $A$ is nonsingular, $A^TA$ is symmetric positive definite. -/
theorem posDef_transpose_mul_self (hA : IsUnit A) : (Aᵀ * A).PosDef := by
  have hinj : Function.Injective A.mulVec := mulVec_injective_iff_isUnit.mpr hA
  rw [← Matrix.isSPD_iff_posDef]
  refine ⟨?_, fun u hu => ?_⟩
  · change (Aᵀ * A)ᵀ = Aᵀ * A
    rw [transpose_mul, transpose_transpose]
  · have hAu : A *ᵥ u ≠ 0 := fun h => hu (hinj (by rw [h, mulVec_zero]))
    have hkey : ((Aᵀ * A) *ᵥ u) ⬝ᵥ u = (A *ᵥ u) ⬝ᵥ (A *ᵥ u) := by
      rw [← mulVec_mulVec, dotProduct_comm, dotProduct_mulVec, vecMul_transpose]
    obtain ⟨i, hi⟩ : ∃ i, (A *ᵥ u) i ≠ 0 := Function.ne_iff.mp hAu
    rw [hkey, dotProduct]
    exact Finset.sum_pos' (fun j _ => mul_self_nonneg _)
      ⟨i, Finset.mem_univ i, mul_self_pos.mpr hi⟩

omit [NeZero n] in
/-- The operator of $A^TA$ is $x \mapsto A^T(Ax)$. -/
private theorem toEuclideanLin_normal (A : Matrix (Fin n) (Fin n) ℝ) (z : E n) :
    ((Aᵀ * A) ⬝ z) = Aᵀ ⬝ (A ⬝ z) := by
  have h : (Aᵀ * A) *ᵥ WithLp.ofLp z = Aᵀ *ᵥ (A *ᵥ WithLp.ofLp z) := (mulVec_mulVec _ _ _).symm
  exact congrArg (WithLp.toLp 2) h

omit [NeZero n] in
/-- §5.3.3 of [saad2003iterative]: for every $A$, the residual norm steepest descent step is the
steepest descent step for the normal equations $A^TAx = A^Tb$. -/
theorem rnsdStep_eq_sdStep_normal (A : Matrix (Fin n) (Fin n) ℝ) (b x : E n) :
    rnsdStep A b x = sdStep (Aᵀ * A) (Aᵀ ⬝ b) x := by
  have hAA : ∀ z : E n, ((Aᵀ * A) ⬝ z) = Aᵀ ⬝ (A ⬝ z) := by
    intro z
    have h : (Aᵀ * A) *ᵥ WithLp.ofLp z = Aᵀ *ᵥ (A *ᵥ WithLp.ofLp z) :=
      (mulVec_mulVec _ _ _).symm
    exact congrArg (WithLp.toLp 2) h
  have hres : (Aᵀ ⬝ b) - ((Aᵀ * A) ⬝ x) = Aᵀ ⬝ (b - (A ⬝ x)) := by
    rw [hAA, ← map_sub]
  have hnum : inner ℝ (A ⬝ (Aᵀ ⬝ (b - (A ⬝ x)))) (b - (A ⬝ x))
      = inner ℝ (Aᵀ ⬝ (b - (A ⬝ x))) (Aᵀ ⬝ (b - (A ⬝ x))) :=
    real_inner_transpose A (Aᵀ ⬝ (b - (A ⬝ x))) (b - (A ⬝ x))
  have hden : inner ℝ (A ⬝ (Aᵀ ⬝ (b - (A ⬝ x)))) (A ⬝ (Aᵀ ⬝ (b - (A ⬝ x))))
      = inner ℝ (Aᵀ ⬝ (b - (A ⬝ x))) (Aᵀ ⬝ (A ⬝ (Aᵀ ⬝ (b - (A ⬝ x))))) :=
    real_inner_transpose A (Aᵀ ⬝ (b - (A ⬝ x))) (A ⬝ (Aᵀ ⬝ (b - (A ⬝ x))))
  rw [rnsdStep, sdStep, hres]
  simp only [step1]
  rw [hres, hAA, hnum, hden]

omit [NeZero n] in
/-- §5.3.3 of [saad2003iterative]: if $Ax^* = b$, the error functional of the normal equations is
the residual norm: $\big( A^TA(x^* - x), x^* - x \big)^{1/2} = \|b - Ax\|_2$. This turns Theorem
5.9 for $A^TA$ into a statement about the residuals of Algorithm 5.4. -/
theorem energyNorm_normal_eq_norm_residual (A : Matrix (Fin n) (Fin n) ℝ) {b xstar : E n}
    (hstar : (A ⬝ xstar) = b) (x : E n) : E_A (Aᵀ * A) xstar x = ‖b - (A ⬝ x)‖ := by
  have hAA := toEuclideanLin_normal A (xstar - x)
  have hd : (A ⬝ (xstar - x)) = b - (A ⬝ x) := by rw [map_sub, hstar]
  have hinner : inner ℝ ((Aᵀ * A) ⬝ (xstar - x)) (xstar - x) = ‖b - (A ⬝ x)‖ ^ 2 := by
    rw [hAA, real_inner_transpose Aᵀ (A ⬝ (xstar - x)) (xstar - x), transpose_transpose, hd,
      real_inner_self_eq_norm_sq]
  rw [E_A, hinner, Real.sqrt_sq (norm_nonneg _)]

omit [NeZero n] in
/-- **Algorithm 5.4** of [saad2003iterative], optimality of a step. Let
$A \in \mathbb{R}^{n \times n}$ be nonsingular. Then the residual norm steepest descent step
from $x$ minimizes $\|b - Ay\|_2$ over the line $y \in x + \operatorname{span}\{A^Tr\}$, where
$r = b - Ax$. The direction $A^Tr$ is $-\nabla f/2$ for $f(x) = \|b - Ax\|_2^2$.

The step is the projection step onto $\operatorname{span}\{A^Tr\}$ orthogonally to
$A \operatorname{span}\{A^Tr\}$, so Proposition 5.3 applies. -/
theorem rnsdStep_min (hA : IsUnit A) (b x y : E n)
    (hy : y - x ∈ (ℝ ∙ (Aᵀ ⬝ (b - (A ⬝ x))))) : R_A A b (rnsdStep A b x) ≤ R_A A b y := by
  rcases eq_or_ne (Aᵀ ⬝ (b - (A ⬝ x))) 0 with h0 | h0
  · have hstep : rnsdStep A b x = x := by
      simp only [rnsdStep, step1, h0, smul_zero, add_zero]
    rw [Submodule.span_singleton_eq_bot.mpr h0, Submodule.mem_bot, sub_eq_zero] at hy
    exact le_of_eq (by rw [hy, hstep])
  · have hAv : (A ⬝ (Aᵀ ⬝ (b - (A ⬝ x)))) ≠ 0 :=
      fun hc => h0 (injective_toEuclideanLin hA (by rw [hc, map_zero]))
    have hne : inner ℝ (A ⬝ (Aᵀ ⬝ (b - (A ⬝ x)))) (A ⬝ (Aᵀ ⬝ (b - (A ⬝ x)))) ≠ 0 :=
      fun hc => hAv (inner_self_eq_zero.mp hc)
    have hmap : (ℝ ∙ (Aᵀ ⬝ (b - (A ⬝ x)))).map (toEuclideanLin A)
        = ℝ ∙ (A ⬝ (Aᵀ ⬝ (b - (A ⬝ x)))) := by
      rw [Submodule.map_span, Set.image_singleton]
    have hproj := step1_isProjectionApprox (A := A) (b := b) (x := x)
      (Aᵀ ⬝ (b - (A ⬝ x))) (A ⬝ (Aᵀ ⬝ (b - (A ⬝ x)))) hne
    rw [← hmap] at hproj
    exact (proposition_5_3.mp hproj).2 y hy

/-- §5.3.3 of [saad2003iterative]: let $A \in \mathbb{R}^{n \times n}$, $n \ge 1$, be nonsingular,
and let $\lambda_{\min}$, $\lambda_{\max}$ be the extreme eigenvalues of $A^TA$. Then the
residuals of Algorithm 5.4 satisfy $\|r_k\|_2 \le \big( (\lambda_{\max} -
\lambda_{\min})/(\lambda_{\max} + \lambda_{\min}) \big)^k \|r_0\|_2$. This is Theorem 5.9 for
the normal equations, by `SaadSparse.Chapter05.energyNorm_normal_eq_norm_residual`. -/
theorem rnsd_norm_residual_le (hA : IsUnit A) (b x₀ : E n) (k : ℕ) :
    ‖b - (A ⬝ ((rnsdStep A b)^[k] x₀))‖ ≤
      ((lambdaMax (posDef_transpose_mul_self hA).1 - lambdaMin (posDef_transpose_mul_self hA).1) /
          (lambdaMax (posDef_transpose_mul_self hA).1 +
            lambdaMin (posDef_transpose_mul_self hA).1)) ^ k * ‖b - (A ⬝ x₀)‖ := by
  have hstar : (A ⬝ (A⁻¹ ⬝ b)) = b := toEuclideanLin_mul_nonsing_inv_apply hA b
  have hnormal : ((Aᵀ * A) ⬝ (A⁻¹ ⬝ b)) = Aᵀ ⬝ b := by
    rw [toEuclideanLin_normal, hstar]
  have hfun : rnsdStep A b = sdStep (Aᵀ * A) (Aᵀ ⬝ b) := funext (rnsdStep_eq_sdStep_normal A b)
  have h := theorem_5_9 (posDef_transpose_mul_self hA) hnormal x₀ k
  rw [← hfun] at h
  rwa [energyNorm_normal_eq_norm_residual A hstar, energyNorm_normal_eq_norm_residual A hstar] at h

/-- **Section 5.3.3** of [saad2003iterative], convergence of Algorithm 5.4. Let
$A \in \mathbb{R}^{n \times n}$, $n \ge 1$, be nonsingular. Then for every $b$ the iterates of
Algorithm 5.4 converge to $A^{-1}b$ from every starting vector.

Algorithm 5.4 is Algorithm 5.2 for the symmetric positive definite normal equations
$A^TAx = A^Tb$, so Theorem 5.9 applies. -/
theorem rnsd_tendsto (hA : IsUnit A) (b x₀ : E n) :
    Tendsto (fun k => (rnsdStep A b)^[k] x₀) atTop (𝓝 (A⁻¹ ⬝ b)) := by
  have hstar : (A ⬝ (A⁻¹ ⬝ b)) = b := toEuclideanLin_mul_nonsing_inv_apply hA b
  have hnormal : ((Aᵀ * A) ⬝ (A⁻¹ ⬝ b)) = Aᵀ ⬝ b := by
    rw [toEuclideanLin_normal, hstar]
  have hfun : rnsdStep A b = sdStep (Aᵀ * A) (Aᵀ ⬝ b) := funext (rnsdStep_eq_sdStep_normal A b)
  rw [hfun]
  exact theorem_5_9_tendsto (posDef_transpose_mul_self hA) hnormal x₀

/-! ### The exact one-step identities (5.16)–(5.18) and (5.20) -/

omit [NeZero n] in
/-- **Equations (5.16)–(5.18)** of [saad2003iterative]. For every $A \in \mathbb{R}^{n \times n}$,
$b$ and $x$, with $r = b - Ax$, the minimal residual step $x'$ satisfies
$$\|b - Ax'\|_2^2 = \|r\|_2^2 \left( 1 - \frac{(Ar, r)^2}{\|r\|_2^2 \, \|Ar\|_2^2} \right).$$

No hypothesis is needed: at a breakdown, where $r = 0$ or $Ar = 0$, both sides are $\|r\|_2^2$,
because division by zero is zero in Lean. The proof specializes
`Projection.norm_residual_minResStep_sq_eq`. -/
theorem equation_5_18 (A : Matrix (Fin n) (Fin n) ℝ) (b x : E n) :
    ‖b - (A ⬝ mrStep A b x)‖ ^ 2 =
      ‖b - (A ⬝ x)‖ ^ 2 *
        (1 - inner ℝ (A ⬝ (b - (A ⬝ x))) (b - (A ⬝ x)) ^ 2 /
          (‖b - (A ⬝ x)‖ ^ 2 * ‖A ⬝ (b - (A ⬝ x))‖ ^ 2)) := by
  have h := Projection.norm_residual_minResStep_sq_eq (A := toEuclideanLin A) (b := b) x
  rw [mrStep_eq]
  simpa only [Real.norm_eq_abs, sq_abs] using h

omit [NeZero n] in
/-- **Section 5.3.2** of [saad2003iterative], the geometric form of (5.18). For every $A$, $b$ and
$x$, with $r = b - Ax$, the minimal residual step $x'$ satisfies
$$\|b - Ax'\|_2 = \|r\|_2 \sin \angle(r, Ar),$$
where $\cos \angle(r, Ar) = (Ar, r)/(\|Ar\|_2 \|r\|_2)$. -/
theorem norm_residual_mrStep_eq_sin (A : Matrix (Fin n) (Fin n) ℝ) (b x : E n) :
    ‖b - (A ⬝ mrStep A b x)‖ =
      ‖b - (A ⬝ x)‖ * Real.sin (InnerProductGeometry.angle (b - (A ⬝ x)) (A ⬝ (b - (A ⬝ x)))) := by
  set r : E n := b - (A ⬝ x) with hr
  have hnn : 0 ≤ ‖r‖ * Real.sin (InnerProductGeometry.angle r (A ⬝ r)) :=
    mul_nonneg (norm_nonneg _) (InnerProductGeometry.sin_angle_nonneg _ _)
  refine ((pow_left_inj₀ (norm_nonneg _) hnn two_ne_zero).mp ?_)
  rw [mul_pow, Real.sin_sq, InnerProductGeometry.cos_angle, equation_5_18]
  rw [real_inner_comm (A ⬝ r) r, div_pow, mul_pow]

omit [NeZero n] in
/-- **Section 5.3.1** of [saad2003iterative], the exact one-step identity of steepest descent. Let
$A$ be symmetric positive definite, let $Ax^* = b$, and let $r = b - Ax$. Then the steepest
descent step $x'$ satisfies
$$E(x')^2 = E(x)^2 \left( 1 - \frac{(r, r)^2}{(Ar, r)(A^{-1}r, r)} \right).$$
Theorem 5.9 follows from it by Kantorovich's inequality (Lemma 5.8).

This is the last display in the proof of Theorem 5.9, which the book does not number. Equation
(5.20) of the book is the residual bound `SaadSparse.Chapter05.equation_5_20` of §5.3.2. The
proof specializes `Projection.energyNorm_steepestDescentStep_sq_eq`. -/
theorem energyNorm_sdStep_sq_eq (hA : A.PosDef) {xstar : E n} (hstar : (A ⬝ xstar) = b) (x : E n) :
    E_A A xstar (sdStep A b x) ^ 2 =
      E_A A xstar x ^ 2 *
        (1 - inner ℝ (b - (A ⬝ x)) (b - (A ⬝ x)) ^ 2 /
          (inner ℝ (A ⬝ (b - (A ⬝ x))) (b - (A ⬝ x)) *
            inner ℝ (A⁻¹ ⬝ (b - (A ⬝ x))) (b - (A ⬝ x)))) := by
  have hsc : (toEuclideanLin A).IsSymmetricCoercive :=
    (Matrix.posDef_iff_isSymmetricCoercive A).mp hA
  -- the error is `A⁻¹ r`, so the energy norm of the error is `⟪A⁻¹ r, r⟫`
  have hAd : (A ⬝ (xstar - x)) = b - (A ⬝ x) := by rw [map_sub, hstar]
  have hd : xstar - x = (A⁻¹ ⬝ (b - (A ⬝ x))) := by
    rw [← hAd, toEuclideanLin_nonsing_inv_mul_apply hA.isUnit]
  have henergy : E_A A xstar x ^ 2 = inner ℝ (A⁻¹ ⬝ (b - (A ⬝ x))) (b - (A ⬝ x)) := by
    rw [E_A_eq_energyNorm, hsc.energyNorm_sq, hAd, ← hd, RCLike.re_to_real,
      real_inner_comm (b - (A ⬝ x)) (xstar - x), hd]
  have hnorm : ‖b - (A ⬝ x)‖ ^ 4 = inner ℝ (b - (A ⬝ x)) (b - (A ⬝ x)) ^ 2 := by
    rw [real_inner_self_eq_norm_sq]
    ring
  have h := Projection.energyNorm_steepestDescentStep_sq_eq (A := toEuclideanLin A) (b := b)
    hsc hstar x
  rw [E_A_eq_energyNorm, sdStep_eq, h, ← E_A_eq_energyNorm, henergy, hnorm, RCLike.re_to_real]

omit [NeZero n] in
/-- **Section 5.3.2** of [saad2003iterative], "$A^{-1}$ is also positive definite". If $A$ is
positive definite, then $A^{-1}$ is positive definite.

The reason is that $(A^{-1}u, u) = (Av, v)$ for $v = A^{-1}u$. -/
theorem isPositiveReal_inv (hA : A.IsPositiveReal) : A⁻¹.IsPositiveReal := by
  intro u hu
  have hv : A *ᵥ (A⁻¹ *ᵥ u) = u := mulVec_nonsing_inv_mulVec (Chapter01.theorem_1_34 hA).1 u
  have hne : A⁻¹ *ᵥ u ≠ 0 := fun hc => hu (by rw [← hv, hc, mulVec_zero])
  have h := hA (A⁻¹ *ᵥ u) hne
  rwa [hv, dotProduct_comm] at h

/-- **Equation (5.20)** of [saad2003iterative]. Let $A \in \mathbb{R}^{n \times n}$, $n \ge 1$, be
positive definite, and let $\mu(B) = \lambda_{\min}((B + B^T)/2)$. Then for every $b$ and $x$
the minimal residual step $x'$ satisfies
$$\|b - Ax'\|_2^2 \le \big( 1 - \mu(A) \mu(A^{-1}) \big) \|b - Ax\|_2^2.$$

The proof bounds the two quotients of (5.18) separately: $(Ar, r)/(r, r) \ge \mu(A)$ is Theorem
1.34, and $(Ar, r)/(Ar, Ar) = (A^{-1}w, w)/(w, w) \ge \mu(A^{-1})$ for $w = Ar$, because
$A^{-1}$ is also positive definite (`SaadSparse.Chapter05.isPositiveReal_inv`). -/
theorem equation_5_20 (hA : A.IsPositiveReal) (b x : E n) :
    ‖b - (A ⬝ mrStep A b x)‖ ^ 2 ≤
      (1 - lambdaMin (Matrix.hermitianPart_isHermitian A) *
          lambdaMin (Matrix.hermitianPart_isHermitian A⁻¹)) * ‖b - (A ⬝ x)‖ ^ 2 := by
  rw [equation_5_18]
  rcases eq_or_ne (b - (A ⬝ x)) 0 with h0 | h0
  · rw [h0]
    simp
  set r : E n := b - (A ⬝ x) with hrdef
  set μ := lambdaMin (Matrix.hermitianPart_isHermitian A) with hμ
  set μ' := lambdaMin (Matrix.hermitianPart_isHermitian A⁻¹) with hμ'
  have hunit : IsUnit A := (Chapter01.theorem_1_34 hA).1
  have hAr : (A ⬝ r) ≠ 0 := fun hc => h0 (injective_toEuclideanLin hunit (by rw [hc, map_zero]))
  have hrn : (0 : ℝ) < ‖r‖ ^ 2 := by positivity
  have hArn : (0 : ℝ) < ‖A ⬝ r‖ ^ 2 := by positivity
  have hμpos : 0 < μ := lambdaMin_hermitianPart_pos hA
  have hμ'pos : 0 < μ' := lambdaMin_hermitianPart_pos (isPositiveReal_inv hA)
  have h1 : μ * ‖r‖ ^ 2 ≤ inner ℝ (A ⬝ r) r := by
    simpa [RCLike.re_to_real] using (Chapter01.isCoerciveWith_lambdaMin A) r
  have hinv : (A⁻¹ ⬝ (A ⬝ r)) = r := toEuclideanLin_nonsing_inv_mul_apply hunit r
  have h2 : μ' * ‖A ⬝ r‖ ^ 2 ≤ inner ℝ (A ⬝ r) r := by
    have hc := (Chapter01.isCoerciveWith_lambdaMin A⁻¹) (A ⬝ r)
    rw [hinv] at hc
    rw [← real_inner_comm (A ⬝ r) r]
    simpa [RCLike.re_to_real] using hc
  have hp1 : (0 : ℝ) < μ * ‖r‖ ^ 2 := by positivity
  have hp2 : (0 : ℝ) < μ' * ‖A ⬝ r‖ ^ 2 := by positivity
  have hq : μ * μ' ≤ inner ℝ (A ⬝ r) r ^ 2 / (‖r‖ ^ 2 * ‖A ⬝ r‖ ^ 2) := by
    rw [le_div_iff₀ (by positivity)]
    calc μ * μ' * (‖r‖ ^ 2 * ‖A ⬝ r‖ ^ 2) = (μ * ‖r‖ ^ 2) * (μ' * ‖A ⬝ r‖ ^ 2) := by ring
      _ ≤ inner ℝ (A ⬝ r) r * inner ℝ (A ⬝ r) r := mul_le_mul h1 h2 hp2.le (hp1.le.trans h1)
      _ = inner ℝ (A ⬝ r) r ^ 2 := by ring
  nlinarith [hq, hrn]

/-! ### §5.3.2: The convergence factor $\rho = \max \sin \angle(x, Ax)$ -/

/-- **Section 5.3.2** of [saad2003iterative], the convergence factor. For
$A \in \mathbb{R}^{n \times n}$, the number
$$\rho = \sup_{x \neq 0} \sin \angle(x, Ax)$$
is the convergence factor that the book reads off the geometric form $\|r_{k+1}\|_2 = \|r_k\|_2
\sin \angle(r_k, Ar_k)$ of (5.18).

The supremum is the real supremum over the nonzero vectors, so it is $0$ when $n = 0$. -/
noncomputable def sinAngleSup (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ⨆ v : {v : E n // v ≠ 0}, Real.sin (InnerProductGeometry.angle (v : E n) (A ⬝ (v : E n)))

omit [NeZero n] in
/-- The sines $\sin \angle(v, Av)$ are bounded by $1$, so they have a supremum. -/
private theorem bddAbove_sinAngle (A : Matrix (Fin n) (Fin n) ℝ) :
    BddAbove (Set.range fun v : {v : E n // v ≠ 0} =>
      Real.sin (InnerProductGeometry.angle (v : E n) (A ⬝ (v : E n)))) := by
  refine ⟨1, ?_⟩
  rintro y ⟨i, rfl⟩
  exact Real.sin_le_one _

omit [NeZero n] in
/-- For every $v \neq 0$, $\sin \angle(v, Av) \le \rho$. -/
theorem sin_angle_le_sinAngleSup (A : Matrix (Fin n) (Fin n) ℝ) {v : E n} (hv : v ≠ 0) :
    Real.sin (InnerProductGeometry.angle v (A ⬝ v)) ≤ sinAngleSup A :=
  le_ciSup (bddAbove_sinAngle A) (⟨v, hv⟩ : {v : E n // v ≠ 0})

omit [NeZero n] in
/-- §5.3.2 of [saad2003iterative]: for every $A$, $b$ and $x$, the minimal residual step $x'$
satisfies $\|b - Ax'\|_2 \le \rho \|b - Ax\|_2$. -/
theorem norm_residual_mrStep_le_sinAngleSup (A : Matrix (Fin n) (Fin n) ℝ) (b x : E n) :
    ‖b - (A ⬝ mrStep A b x)‖ ≤ sinAngleSup A * ‖b - (A ⬝ x)‖ := by
  rcases eq_or_ne (b - (A ⬝ x)) 0 with h0 | h0
  · have hstep : mrStep A b x = x := by simp only [mrStep, step1, h0, smul_zero, add_zero]
    rw [hstep, h0]
    simp
  · rw [norm_residual_mrStep_eq_sin, mul_comm ‖b - (A ⬝ x)‖]
    exact mul_le_mul_of_nonneg_right (sin_angle_le_sinAngleSup A h0) (norm_nonneg _)

open scoped Matrix.Norms.L2Operator in
/-- §5.3.2 of [saad2003iterative]: if $A$ is positive definite and $n \ge 1$, the largest angle
between $x$ and $Ax$ is acute in the sense that $\rho = \sup_{x \neq 0} \sin \angle(x, Ax) < 1$.
The uniform bound is Theorem 5.10: for $b = x$ and the starting vector $0$, the residual is $x$,
and (5.15) bounds its angle sine by $(1 - \mu^2/\sigma^2)^{1/2} < 1$. No compactness argument is
needed. -/
theorem sinAngleSup_lt_one (hA : A.IsPositiveReal) : sinAngleSup A < 1 := by
  have hbound : ∀ v : {v : E n // v ≠ 0},
      Real.sin (InnerProductGeometry.angle (v : E n) (A ⬝ (v : E n)))
        ≤ Real.sqrt (1 - lambdaMin (Matrix.hermitianPart_isHermitian A) ^ 2 / ‖A‖ ^ 2) := by
    rintro ⟨v, hv⟩
    have h1 := norm_residual_mrStep_eq_sin A v 0
    have h2 := theorem_5_10_step hA v 0
    simp only [map_zero, sub_zero] at h1 h2
    rw [h1] at h2
    have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hv
    nlinarith [h2, hvpos]
  exact lt_of_le_of_lt (Real.iSup_le hbound (Real.sqrt_nonneg _)) (theorem_5_10_factor_lt_one hA)

/-- **Section 5.3.2** of [saad2003iterative], convergence of the minimal residual iteration. Let
$A \in \mathbb{R}^{n \times n}$, $n \ge 1$, be positive definite. Then for every $b$ and $x$ the
minimal residual step $x'$ satisfies
$$\|b - Ax'\|_2 \le \rho \, \|b - Ax\|_2, \qquad \rho = \sup_{x \neq 0} \sin \angle(x, Ax) <
  1.$$
-/
theorem norm_mrStep_le_sup_sin (hA : A.IsPositiveReal) (b x : E n) :
    ‖b - (A ⬝ mrStep A b x)‖ ≤ sinAngleSup A * ‖b - (A ⬝ x)‖ ∧ sinAngleSup A < 1 :=
  ⟨norm_residual_mrStep_le_sinAngleSup A b x, sinAngleSup_lt_one hA⟩

/-! ### Example 5.1: A Gauss–Seidel relaxation is a projection step -/

omit [NeZero n] in
/-- The inner product with the coordinate vector $e_i$ is the component $i$: $(e_i, z) = z_i$. -/
private theorem real_inner_single_left (i : Fin n) (z : E n) :
    inner ℝ (EuclideanSpace.single i (1 : ℝ) : E n) z = WithLp.ofLp z i := by
  rw [EuclideanSpace.inner_single_left]
  simp

omit [NeZero n] in
/-- The diagonal entry is $a_{ii} = (e_i, Ae_i)$. -/
private theorem real_inner_single_apply_single (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    inner ℝ (EuclideanSpace.single i (1 : ℝ) : E n) (A ⬝ (EuclideanSpace.single i (1 : ℝ) : E n))
      = A i i := by
  rw [real_inner_single_left, Matrix.ofLp_toEuclideanLin]
  simp

omit [NeZero n] in
/-- **Example 5.1** of [saad2003iterative]. For every $A \in \mathbb{R}^{n \times n}$, $b$, $x$ and
index $i$, the projection step (5.12) onto $K = L = \operatorname{span}\{e_i\}$ is the
elementary relaxation step
$$x \mapsto x + \frac{r_i}{a_{ii}} \, e_i, \qquad r = b - Ax,$$
the inner step of the Gauss–Seidel sweep (4.6).

If $a_{ii} = 0$, both sides are $x$, because division by zero is zero in Lean. -/
theorem example_5_1 (A : Matrix (Fin n) (Fin n) ℝ) (b x : E n) (i : Fin n) :
    step1 A b (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single i (1 : ℝ)) x
      = x + (WithLp.ofLp (b - (A ⬝ x)) i / A i i) •
          (EuclideanSpace.single i (1 : ℝ) : E n) := by
  rw [step1, real_inner_single_left, real_inner_single_apply_single]

omit [NeZero n] in
/-- Example 5.1 of [saad2003iterative], the Petrov–Galerkin condition for
$L = \operatorname{span}\{e_i\}$: if $a_{ii} \neq 0$, the elementary relaxation step annihilates
component $i$ of the residual, as (4.6) prescribes. -/
theorem example_5_1_residual (A : Matrix (Fin n) (Fin n) ℝ) (b x : E n) {i : Fin n}
    (hii : A i i ≠ 0) :
    WithLp.ofLp (b - (A ⬝ step1 A b (EuclideanSpace.single i (1 : ℝ))
      (EuclideanSpace.single i (1 : ℝ)) x)) i = 0 := by
  have hne : inner ℝ (EuclideanSpace.single i (1 : ℝ) : E n)
      (A ⬝ (EuclideanSpace.single i (1 : ℝ) : E n)) ≠ 0 := by
    rw [real_inner_single_apply_single]
    exact hii
  have h := (step1_isProjectionApprox (A := A) (b := b) (x := x) _ _ hne).2
    (EuclideanSpace.single i (1 : ℝ)) (Submodule.mem_span_singleton_self _)
  rwa [real_inner_single_left] at h

omit [NeZero n] in
/-- Example 5.1 of [saad2003iterative]: the elementary relaxation step at index $i$ changes only
component $i$ of $x$. -/
theorem example_5_1_apply_of_ne (A : Matrix (Fin n) (Fin n) ℝ) (b x : E n) {i j : Fin n}
    (hij : j ≠ i) :
    WithLp.ofLp (step1 A b (EuclideanSpace.single i (1 : ℝ))
      (EuclideanSpace.single i (1 : ℝ)) x) j = WithLp.ofLp x j := by
  rw [example_5_1]
  simp [hij]

/-!
### The recursive residual of Algorithms 5.2–5.4

Each algorithm is printed with the residual carried forward rather than recomputed, so that a step
costs one matrix–vector product. The state is the pair $(x, r)$. The results below say that the
carried $r$ is $b - Ax$ at every step, so that each printed algorithm computes the corresponding
projection iterate.
-/

/-- **Algorithm 5.2** of [saad2003iterative] (steepest descent), as printed. One step on the pair
$(x, r)$ is
$$p \leftarrow Ar, \quad \alpha \leftarrow \frac{(r, r)}{(p, r)}, \quad x \leftarrow x + \alpha
  r, \quad r \leftarrow r - \alpha p.$$
-/
noncomputable def sdAlgStep (A : Matrix (Fin n) (Fin n) ℝ) : (E n) × (E n) → (E n) × (E n)
  | (x, r) => (x + (inner ℝ r r / inner ℝ r (A ⬝ r)) • r,
      r - (inner ℝ r r / inner ℝ r (A ⬝ r)) • (A ⬝ r))

/-- **Algorithm 5.3** of [saad2003iterative] (minimal residual), as printed. One step on the pair
$(x, r)$ is
$$p \leftarrow Ar, \quad \alpha \leftarrow \frac{(p, r)}{(p, p)}, \quad x \leftarrow x + \alpha
  r, \quad r \leftarrow r - \alpha p.$$
-/
noncomputable def mrAlgStep (A : Matrix (Fin n) (Fin n) ℝ) : (E n) × (E n) → (E n) × (E n)
  | (x, r) => (x + (inner ℝ (A ⬝ r) r / inner ℝ (A ⬝ r) (A ⬝ r)) • r,
      r - (inner ℝ (A ⬝ r) r / inner ℝ (A ⬝ r) (A ⬝ r)) • (A ⬝ r))

/-- **Algorithm 5.4** of [saad2003iterative] (residual norm steepest descent), as printed. One step
on the pair $(x, r)$ is
$$v \leftarrow A^Tr, \quad \alpha \leftarrow \frac{\|v\|_2^2}{\|Av\|_2^2}, \quad x \leftarrow
  x + \alpha v, \quad r \leftarrow r - \alpha Av.$$

The step length is written as $(Av, r)/(Av, Av)$, which equals $\|v\|_2^2/\|Av\|_2^2$ (5.21) by
`SaadSparse.Chapter05.rnsdAlgStep_alpha`. -/
noncomputable def rnsdAlgStep (A : Matrix (Fin n) (Fin n) ℝ) : (E n) × (E n) → (E n) × (E n)
  | (x, r) =>
      (x + (inner ℝ (A ⬝ (Aᵀ ⬝ r)) r / inner ℝ (A ⬝ (Aᵀ ⬝ r)) (A ⬝ (Aᵀ ⬝ r))) • (Aᵀ ⬝ r),
        r - (inner ℝ (A ⬝ (Aᵀ ⬝ r)) r / inner ℝ (A ⬝ (Aᵀ ⬝ r)) (A ⬝ (Aᵀ ⬝ r))) • (A ⬝ (Aᵀ ⬝ r)))

omit [NeZero n] in
/-- Equation (5.21) of [saad2003iterative]: with $v = A^Tr$, the step length of Algorithm 5.4 is
$(Av, r)/(Av, Av) = \|v\|_2^2/\|Av\|_2^2$, because $(Av, r) = (v, v)$. -/
theorem rnsdAlgStep_alpha (A : Matrix (Fin n) (Fin n) ℝ) (r : E n) :
    inner ℝ (A ⬝ (Aᵀ ⬝ r)) r / inner ℝ (A ⬝ (Aᵀ ⬝ r)) (A ⬝ (Aᵀ ⬝ r))
      = ‖Aᵀ ⬝ r‖ ^ 2 / ‖A ⬝ (Aᵀ ⬝ r)‖ ^ 2 := by
  rw [real_inner_transpose A (Aᵀ ⬝ r) r, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]

omit [NeZero n] in
/-- **Algorithm 5.2** of [saad2003iterative], correctness. For every $A$, $b$, $x_0$ and $k \ge 0$,
the algorithm as printed, started at $(x_0, b - Ax_0)$, reaches after $k$ steps the pair
$(x_k, b - Ax_k)$, where $x_k$ is the $k$-th steepest descent iterate. -/
theorem sdAlg_spec (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : E n) (k : ℕ) :
    (sdAlgStep A)^[k] (x₀, b - (A ⬝ x₀))
      = ((sdStep A b)^[k] x₀, b - (A ⬝ ((sdStep A b)^[k] x₀))) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    simp only [sdAlgStep, Prod.mk.injEq]
    refine ⟨rfl, ?_⟩
    simp only [sdStep, step1, map_add, map_smul]
    module

omit [NeZero n] in
/-- **Algorithm 5.3** of [saad2003iterative], correctness. For every $A$, $b$, $x_0$ and $k \ge 0$,
the algorithm as printed, started at $(x_0, b - Ax_0)$, reaches after $k$ steps the pair
$(x_k, b - Ax_k)$, where $x_k$ is the $k$-th minimal residual iterate. -/
theorem mrAlg_spec (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : E n) (k : ℕ) :
    (mrAlgStep A)^[k] (x₀, b - (A ⬝ x₀))
      = ((mrStep A b)^[k] x₀, b - (A ⬝ ((mrStep A b)^[k] x₀))) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    simp only [mrAlgStep, Prod.mk.injEq]
    refine ⟨rfl, ?_⟩
    simp only [mrStep, step1, map_add, map_smul]
    module

omit [NeZero n] in
/-- **Algorithm 5.4** of [saad2003iterative], correctness. For every $A$, $b$, $x_0$ and $k \ge 0$,
the algorithm as printed, started at $(x_0, b - Ax_0)$, reaches after $k$ steps the pair
$(x_k, b - Ax_k)$, where $x_k$ is the $k$-th residual norm steepest descent iterate. -/
theorem rnsdAlg_spec (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : E n) (k : ℕ) :
    (rnsdAlgStep A)^[k] (x₀, b - (A ⬝ x₀))
      = ((rnsdStep A b)^[k] x₀, b - (A ⬝ ((rnsdStep A b)^[k] x₀))) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    simp only [rnsdAlgStep, Prod.mk.injEq]
    refine ⟨rfl, ?_⟩
    simp only [rnsdStep, step1, map_add, map_smul]
    module

end SaadSparse.Chapter05
