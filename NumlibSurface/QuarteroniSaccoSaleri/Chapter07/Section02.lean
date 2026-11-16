/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Numlib.Analysis.Calculus.Gradient
import Numlib.Optimization.ConjugateGradient
import Numlib.Optimization.LineSearch
import Numlib.Optimization.QuasiNewton
import Numlib.Projection.ConjugateDirection
import NumlibSurface.QuarteroniSaccoSaleri.Chapter07.Section01

/-!
# Quarteroni, Sacco and Saleri, Section 7.2: Unconstrained Optimization

This module formalizes Section 7.2 of [quarteroni2000numerical], on the minimization of a function
$f : \mathbb{R}^n \to \mathbb{R}$. It defines the Hessian matrix and critical points and states the
optimality conditions of Property 7.4, with the Rosenbrock function of Example 7.5. Descent methods
$x^{(k+1)} = x^{(k)} + \alpha_k d^{(k)}$ (7.25)–(7.28) decrease $f$ along a descent direction, and
an exact line search makes the new gradient orthogonal to the old direction (Theorem 7.3). The line
search conditions of Armijo, Wolfe and Goldstein (7.31)–(7.34) can be met on an interval of steps
(Property 7.5).

For the quadratic $f(x) = \frac{1}{2} x^T A x - b^T x$ (7.35), the module states the exact step
(7.36), the error reduction (7.37)–(7.39) of the steepest descent method with the Kantorovich
inequality (Lemma 7.1), the properties of conjugate directions (Property 7.6), and the conjugate
gradient method with its nonlinear variants (Remark 7.2). It then states Newton's method for
minimization (7.40)–(7.41), the global convergence results (Properties 7.7 and 7.8), and the secant
updates (7.42)–(7.46) of Section 7.2.7 with the least-change property and the bounded deterioration
of the symmetric Powell–Broyden update. The proofs specialize `Numlib.Optimization.Descent`,
`Numlib.Optimization.LineSearch`, `Numlib.Optimization.ConjugateGradient`,
`Numlib.Optimization.QuasiNewton`, `Numlib.Projection.OneDimensional`,
`Numlib.Projection.ConjugateDirection`, `Numlib.Krylov.CG` and
`Numlib.Analysis.InnerProductSpace.Energy`.

## Main definitions

* Section 7.2.1, `QuarteroniSaccoSaleri.Chapter07.hessianMatrix`: the Hessian matrix $H(x)$.
* Section 7.2.1, `QuarteroniSaccoSaleri.Chapter07.IsCriticalPoint`: a critical point, where
  $\nabla f(x) = 0$.
* Example 7.5, `QuarteroniSaccoSaleri.Chapter07.rosenbrock`: the Rosenbrock function (7.24).

## Main results

* Property 7.4(a), `QuarteroniSaccoSaleri.Chapter07.property_7_4_gradient`: at a local minimizer,
  $\nabla f(x^*) = 0$.
* Property 7.4(b), `QuarteroniSaccoSaleri.Chapter07.property_7_4_hessian`: at a local minimizer,
  $H(x^*)$ is positive semidefinite.
* Property 7.4(c), `QuarteroniSaccoSaleri.Chapter07.property_7_4_sufficient`: a critical point with
  positive definite Hessian is a strict local minimizer.
* Section 7.2.1, `QuarteroniSaccoSaleri.Chapter07.isMinOn_of_convexOn_of_isCriticalPoint`: a
  critical point of a convex function is a global minimizer.
* Example 7.5, `QuarteroniSaccoSaleri.Chapter07.example_7_5`: the Rosenbrock function has the unique
  global minimizer $(1, 1)$.
* Equations (7.27)–(7.28), `QuarteroniSaccoSaleri.Chapter07.equation_7_27`: a small step along a
  descent direction decreases $f$.
* Section 7.2.2, `QuarteroniSaccoSaleri.Chapter07.steepestDescent_isDescentDirection`: the
  steepest-descent and Newton-type directions are descent directions.
* Theorem 7.3, `QuarteroniSaccoSaleri.Chapter07.theorem_7_3`: after an exact line search,
  $\nabla f(x^{(k+1)})^T d^{(k)} = 0$.
* Equation (7.31), `QuarteroniSaccoSaleri.Chapter07.equation_7_31`: the Armijo condition.
* Equations (7.32)–(7.33), `QuarteroniSaccoSaleri.Chapter07.equation_7_32`: the strong and weak
  Wolfe conditions.
* Equation (7.34), `QuarteroniSaccoSaleri.Chapter07.equation_7_34`: the Goldstein conditions, and
  the Armijo rule is well defined.
* Property 7.5, `QuarteroniSaccoSaleri.Chapter07.property_7_5`: for $f$ bounded below, an interval
  of steps satisfies (7.31) and (7.32).
* Equation (7.35), `QuarteroniSaccoSaleri.Chapter07.equation_7_35`: the gradient $Ax - b$ and the
  Hessian $A$ of the quadratic.
* Equation (7.36), `QuarteroniSaccoSaleri.Chapter07.equation_7_36`: the exact step
  $\alpha = d^T r / d^T A d$.
* Equations (7.37)–(7.38), `QuarteroniSaccoSaleri.Chapter07.equation_7_38`: the error reduction
  factor of one exact step.
* Equation (7.39), `QuarteroniSaccoSaleri.Chapter07.equation_7_39`: the error bound of the steepest
  descent method.
* Lemma 7.1, `QuarteroniSaccoSaleri.Chapter07.lemma_7_1`: the Kantorovich inequality.
* Property 7.6, `QuarteroniSaccoSaleri.Chapter07.property_7_6_termination`,
  `QuarteroniSaccoSaleri.Chapter07.property_7_6_isMinOn` and
  `QuarteroniSaccoSaleri.Chapter07.property_7_6_orthogonal`: a conjugate direction method ends in at
  most $n$ steps, minimizes over the affine span of the directions, and makes the residual
  orthogonal to the directions.
* Section 7.2.4, `QuarteroniSaccoSaleri.Chapter07.conjugateGradient_eq_CG`: the conjugate gradient
  method for minimization is the backbone's conjugate gradient iteration.
* Remark 7.2, `QuarteroniSaccoSaleri.Chapter07.remark_7_2`: the Fletcher–Reeves and Polak–Ribière
  methods, which reproduce the conjugate gradient method on the quadratic.
* Equation (7.40), `QuarteroniSaccoSaleri.Chapter07.equation_7_40`: Newton's method for minimization
  converges quadratically near a nondegenerate critical point.
* Equation (7.41), `QuarteroniSaccoSaleri.Chapter07.equation_7_41`: on the quadratic, Newton's
  method converges in one step.
* Property 7.7, `QuarteroniSaccoSaleri.Chapter07.property_7_7`: the alternatives of Zoutendijk's
  theorem for gradient-like methods.
* Property 7.8, `QuarteroniSaccoSaleri.Chapter07.property_7_8`: for a bounded sequence whose cluster
  points are critical, $\nabla f(x^{(k)}) \to 0$.
* Equation (7.42), `QuarteroniSaccoSaleri.Chapter07.equation_7_42`: the rank-one secant update
  satisfies the secant equation.
* Equation (7.43), `QuarteroniSaccoSaleri.Chapter07.equation_7_43`: the symmetric rank-one update.
* Equation (7.44), `QuarteroniSaccoSaleri.Chapter07.equation_7_44`: the inverse of the symmetric
  rank-one update.
* Equations (7.45)–(7.46), `QuarteroniSaccoSaleri.Chapter07.equation_7_46`: the symmetrization
  iteration converges to the general symmetric update.
* Section 7.2.7, `QuarteroniSaccoSaleri.Chapter07.psbLeastChange`: the symmetric Powell–Broyden
  update is the closest symmetric matrix in the Frobenius norm that satisfies the secant equation.
* Section 7.2.7, `QuarteroniSaccoSaleri.Chapter07.psbBoundedDeterioration`: the bounded
  deterioration of the symmetric Powell–Broyden update.

## Conventions

* Gradients are Mathlib's `gradient f x` on `EuclideanSpace ℝ (Fin n)`. The backbone works with the
  derivative `fderiv ℝ f`, and the two are related by `fderiv_eq_innerSL_gradient`: the derivative
  of $f$ at $x$ in the direction $d$ is $\langle \nabla f(x), d \rangle$.
* The Hessian matrix $H(x)$ is `QuarteroniSaccoSaleri.Chapter07.hessianMatrix f x`, the matrix of
  the second partial derivatives.
* A descent method (7.25)–(7.26) is the backbone's relational specification
  `Descent.IsDescentSequence (fderiv ℝ f) x d α`.
* The quadratic (7.35) is `energyFunctional (toEuclideanLin A) b`. Its line-search and
  conjugate-direction iterations are the backbone's `Projection.step1` and
  `ConjugateDirection.iterate`.

## Implementation notes

* Property 7.5 carries the restriction $\sigma < 1/2$ of the source, which the proof does not use:
  the backbone proves the statement for every $0 < \sigma < \beta < 1$.
* Property 7.7 carries the hypotheses $f \in C^1$ and $\sigma < \beta$ of the source, which the
  proof does not use: the backbone needs only the Lipschitz gradient, $0 < \sigma$ and $\beta < 1$.
* Equation (7.38) is stated over $\mathbb{R}$, where $|d^T r|^2 = (d^T r)^2$. The backbone identity
  holds over `RCLike`.

## Deviations from the source

* **Property 7.4(a)** (generalization). The source assumes $f \in C^1(B(x^*; R))$; differentiability
  at $x^*$ is enough. See `QuarteroniSaccoSaleri.Chapter07.property_7_4_gradient`.
* **Property 7.4(c)** (correction). The source omits the hypothesis $\nabla f(x^*) = 0$, without
  which the statement is false, and its conclusion is a strict local minimum. See
  `QuarteroniSaccoSaleri.Chapter07.property_7_4_sufficient`.
* **Equation (7.31)** (reading). The source prints an outer inequality $0 \ge v_M(x^{(k+1)})$. The
  Armijo condition is the inner inequality. See `QuarteroniSaccoSaleri.Chapter07.equation_7_31`.
* **Property 7.8** (reading). As printed, the property is the continuity of $\nabla f$. The intended
  statement is the one for bounded sequences whose cluster points are critical. See
  `QuarteroniSaccoSaleri.Chapter07.property_7_8` and
  `QuarteroniSaccoSaleri.Chapter07.property_7_8_of_tendsto`.
* **Equations (7.45)–(7.46)** (reading). The symmetrization iteration converges to (7.46) from a
  symmetric $B_k$ only, which the source leaves implicit. See
  `QuarteroniSaccoSaleri.Chapter07.equation_7_46`.
* **Section 7.2.7, bounded deterioration** (reading). The estimate needs a symmetric $B_k$, which
  the source leaves implicit. See `QuarteroniSaccoSaleri.Chapter07.psbBoundedDeterioration`.

## Not formalized

* **Example 7.5, the numerical comparison of methods.**
-/

open Filter Matrix Metric Set Topology WithLp
open scoped InnerProductSpace

namespace QuarteroniSaccoSaleri.Chapter07

variable {n : ℕ}

/-! ### Gradients, the Hessian matrix, and Property 7.4 -/

section Hessian

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Let $H$ be a real Hilbert space and $f : H \to \mathbb{R}$. The gradient map of $f$ sends $x$ to
the vector that represents the derivative of $f$ at $x$ by the Riesz isomorphism
`InnerProductSpace.toDual`. -/
theorem gradient_eq_toDual_symm_fderiv (f : H → ℝ) :
    gradient f = fun x => (InnerProductSpace.toDual ℝ H).symm (fderiv ℝ f x) :=
  rfl

end Hessian

/-- **Section 7.2.1** of [quarteroni2000numerical], the **Hessian matrix** $H(x)$ of
$f : \mathbb{R}^n \to \mathbb{R}$ at $x$, with entries
$$h_{ij}(x) = \frac{\partial^2 f}{\partial x_i \partial x_j}(x).$$

It is defined as the derivative at $x$ in the direction $e_i$ of the partial derivative
$y \mapsto \partial f / \partial x_j(y)$, the derivative of $f$ at $y$ in the direction $e_j$.
Where these derivatives do not exist, Mathlib's `fderiv` gives $0$. For a $C^2$ function, $H(x)$
is the matrix of the second Fréchet derivative
(`QuarteroniSaccoSaleri.Chapter07.hessianMatrix_apply`), it is symmetric
(`QuarteroniSaccoSaleri.Chapter07.hessianMatrix_isSymm`), and it is the derivative of the
gradient map (`QuarteroniSaccoSaleri.Chapter07.hasFDerivAt_gradient`). -/
noncomputable def hessianMatrix (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j =>
    fderiv ℝ (fun y => fderiv ℝ f y (EuclideanSpace.single j 1)) x (EuclideanSpace.single i 1)

section HessianMatrix

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}

/-- If the derivative of $f$ is differentiable at $x$, the entries of the Hessian matrix are the
values of the second Fréchet derivative on the standard basis: $h_{ij}(x) = f''(x)(e_i)(e_j)$. -/
theorem hessianMatrix_apply (hf : DifferentiableAt ℝ (fderiv ℝ f) x) (i j : Fin n) :
    hessianMatrix f x i j
      = fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
  rw [hessianMatrix, Matrix.of_apply, fderiv_clm_apply hf (differentiableAt_const _)]
  simp

/-- If the derivative of $f$ is differentiable at $x$, then for every $v \in \mathbb{R}^n$ the
coordinates of $H(x) v$ are $(H(x) v)_i = f''(x)(e_i)(v)$. -/
theorem toEuclideanLin_hessianMatrix_apply (hf : DifferentiableAt ℝ (fderiv ℝ f) x)
    (v : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    toEuclideanLin (hessianMatrix f x) v i
      = fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.single i 1) v := by
  have hv : ∑ i, v i • EuclideanSpace.single i 1 = v := by
    conv_rhs => rw [← (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v]
    simp [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply]
  have h1 : fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.single i 1) v
      = fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.single i 1)
        (∑ j, v j • EuclideanSpace.single j 1) := by rw [hv]
  rw [h1, map_sum, toEuclideanLin_apply]
  simp only [Matrix.mulVec, dotProduct, map_smul, smul_eq_mul, hessianMatrix_apply hf]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- If the derivative of $f$ is differentiable at $x$, the quadratic form of the Hessian matrix is
the second derivative along a direction: $v^T H(x) v = f''(x)(v)(v)$ for every
$v \in \mathbb{R}^n$. -/
theorem inner_toEuclideanLin_hessianMatrix (hf : DifferentiableAt ℝ (fderiv ℝ f) x)
    (v : EuclideanSpace ℝ (Fin n)) :
    ⟪toEuclideanLin (hessianMatrix f x) v, v⟫_ℝ = fderiv ℝ (fderiv ℝ f) x v v := by
  set f'' := fderiv ℝ (fderiv ℝ f) x with hf''
  have hv : ∑ i, v i • EuclideanSpace.single i 1 = v := by
    conv_rhs => rw [← (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v]
    simp [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply]
  have hcoord : ∀ i, toEuclideanLin (hessianMatrix f x) v i
      = f'' (EuclideanSpace.single i 1) v := toEuclideanLin_hessianMatrix_apply hf v
  have hvv : f'' v v = f'' (∑ i, v i • EuclideanSpace.single i 1) v := by rw [hv]
  calc ⟪toEuclideanLin (hessianMatrix f x) v, v⟫_ℝ
      = ∑ i, toEuclideanLin (hessianMatrix f x) v i * v i := by
        rw [real_inner_comm, EuclideanSpace.inner_eq_star_dotProduct]
        simp [dotProduct]
    _ = ∑ i, v i * f'' (EuclideanSpace.single i 1) v := by
        simp only [hcoord, mul_comm]
    _ = f'' v v := by
        rw [hvv, map_sum, _root_.sum_apply]
        simp only [map_smul, _root_.smul_apply, smul_eq_mul]

/-- If $f$ is of class $C^2$ on a neighbourhood of $x$, the Hessian matrix $H(x)$ is symmetric. This
is Schwarz's theorem, Mathlib's `ContDiffAt.isSymmSndFDerivAt`. -/
theorem hessianMatrix_isSymm (hf : ContDiffAt ℝ 2 f x) : (hessianMatrix f x).IsSymm := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) le_rfl).differentiableAt one_ne_zero
  have hsymm := hf.isSymmSndFDerivAt (by simp)
  refine IsSymm.ext fun i j => ?_
  rw [hessianMatrix_apply hd, hessianMatrix_apply hd, hsymm]

/-- If $f$ is of class $C^2$ on a neighbourhood of $x$, the gradient map $\nabla f$ has the
derivative $H(x)$ at $x$, with $H(x)$ acting on $\mathbb{R}^n$ through `Matrix.toEuclideanCLM`. -/
theorem hasFDerivAt_gradient (hf : ContDiffAt ℝ 2 f x) :
    HasFDerivAt (gradient f) (toEuclideanCLM (𝕜 := ℝ) (hessianMatrix f x)) x := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) le_rfl).differentiableAt one_ne_zero
  have hsymm := hf.isSymmSndFDerivAt (by simp)
  rw [gradient_eq_toDual_symm_fderiv]
  have h := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.hasFDerivAt.comp x
    hd.hasFDerivAt
  refine h.congr_fderiv ?_
  ext v i
  have hR : toEuclideanCLM (𝕜 := ℝ) (hessianMatrix f x) v i
      = fderiv ℝ (fderiv ℝ f) x v (EuclideanSpace.single i 1) := by
    rw [← hsymm]
    exact toEuclideanLin_hessianMatrix_apply hd v i
  have hL : (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm
      (fderiv ℝ (fderiv ℝ f) x v) i = fderiv ℝ (fderiv ℝ f) x v (EuclideanSpace.single i 1) := by
    rw [← InnerProductSpace.toDual_symm_apply, EuclideanSpace.inner_single_right]
    simp
  rw [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearEquiv.coe_coe]
  exact hL.trans hR.symm

end HessianMatrix

section Property74

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {xstar : EuclideanSpace ℝ (Fin n)}

/-- **Property 7.4(a)** of [quarteroni2000numerical]. Let $f : \mathbb{R}^n \to \mathbb{R}$ have a
local minimizer $x^*$ and be differentiable at $x^*$. Then $\nabla f(x^*) = 0$.

**Generalization.** The source assumes $f \in C^1(B(x^*; R))$. Differentiability at $x^*$ is
enough.

The proof is Mathlib's `IsLocalMin.hasFDerivAt_eq_zero`. -/
theorem property_7_4_gradient (hmin : IsLocalMin f xstar) (hf : DifferentiableAt ℝ f xstar) :
    gradient f xstar = 0 := by
  have h := hmin.hasFDerivAt_eq_zero (hasGradientAt_iff_hasFDerivAt.1 hf.hasGradientAt)
  rw [map_eq_zero_iff _ (InnerProductSpace.toDual ℝ _).injective] at h
  exact h

/-- **Property 7.4(b)** of [quarteroni2000numerical]. Let $f : \mathbb{R}^n \to \mathbb{R}$ have a
local minimizer $x^*$ and be of class $C^2$ on a neighbourhood of $x^*$. Then the Hessian matrix
$H(x^*)$ is positive semidefinite.

The source assumes $f \in C^2(B(x^*; R))$. The backbone's
`Descent.nonneg_apply_apply_of_isLocalMin` gives $0 \le f''(x^*)(v)(v) = v^T H(x^*) v$ for every
$v$, and Schwarz's theorem gives the symmetry. -/
theorem property_7_4_hessian (hmin : IsLocalMin f xstar) (hf : ContDiffAt ℝ 2 f xstar) :
    (hessianMatrix f xstar).PosSemidef := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) xstar :=
    (hf.fderiv_right (m := 1) le_rfl).differentiableAt one_ne_zero
  have hev : ∀ᶠ y in 𝓝 xstar, HasFDerivAt f (fderiv ℝ f y) y := by
    filter_upwards [hf.eventually (by simp)] with y hy
    exact (hy.differentiableAt (by simp)).hasFDerivAt
  refine Matrix.posSemidef_iff_dotProduct_mulVec.2 ⟨isHermitian_iff_isSymm.2
    (hessianMatrix_isSymm hf), fun v => ?_⟩
  have h := Descent.nonneg_apply_apply_of_isLocalMin hmin hev hd.hasFDerivAt (toLp 2 v)
  rw [← inner_toEuclideanLin_hessianMatrix hd, toEuclideanLin_toLp,
    EuclideanSpace.inner_toLp_toLp, star_trivial] at h
  rw [star_trivial]
  exact h

/-- **Property 7.4(c)** of [quarteroni2000numerical]. Let $f : \mathbb{R}^n \to \mathbb{R}$ be of
class $C^2$ on a neighbourhood of $x^*$, let $\nabla f(x^*) = 0$, and let the Hessian matrix
$H(x^*)$ be positive definite. Then $x^*$ is a strict local minimizer of $f$: there is
$\delta > 0$ with $f(x^*) < f(y)$ for every $y \neq x^*$ in the ball $B(x^*; \delta)$.

**Correction.** The source reads "if $x^* \in B(x^*; R)$ and $H(x^*)$ is positive definite then
$x^*$ is a local minimizer". The hypothesis $\nabla f(x^*) = 0$ is missing, and without it the
statement is false: $f(x) = x + x^2$ has $f''(0) = 2 > 0$, but $0$ is not a local minimizer. The
conclusion is also stronger: the minimum is strict.

The proof specializes `Descent.isLocalMin_of_coercive_second`, with the coercivity of the
Hessian form from `Matrix.posDef_iff_isSymmetricCoercive`. -/
theorem property_7_4_sufficient (hf : ContDiffAt ℝ 2 f xstar) (hcrit : gradient f xstar = 0)
    (hH : (hessianMatrix f xstar).PosDef) :
    ∃ δ > 0, ∀ y ∈ ball xstar δ, y ≠ xstar → f xstar < f y := by
  -- the differentiability data on a ball, from `C²` at `x*`
  have h2 : ∀ᶠ y in 𝓝 xstar, ContDiffAt ℝ 2 f y := hf.eventually (by simp)
  have h1 : ∀ᶠ y in 𝓝 xstar, ContDiffAt ℝ 1 (fderiv ℝ f) y :=
    (hf.fderiv_right (m := 1) le_rfl).eventually (by simp)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.1 (h2.and h1)
  have hcont : ContinuousAt (fderiv ℝ (fderiv ℝ f)) xstar :=
    ((hf.fderiv_right (m := 1) le_rfl).fderiv_right (m := 0) le_rfl).continuousAt
  -- coercivity of the Hessian form
  obtain ⟨c, hc, hcoer⟩ := ((Matrix.posDef_iff_isSymmetricCoercive _).1 hH).isCoercive
  have hd : DifferentiableAt ℝ (fderiv ℝ f) xstar :=
    (hf.fderiv_right (m := 1) le_rfl).differentiableAt one_ne_zero
  refine Descent.isLocalMin_of_coercive_second (f' := fderiv ℝ f) (f'' := fderiv ℝ (fderiv ℝ f))
    hr hc (fun y hy => ((hball hy).1.differentiableAt (by simp)).hasFDerivAt)
    (fun y hy => ((hball hy).2.differentiableAt one_ne_zero).hasFDerivAt) hcont ?_ fun v => ?_
  · rw [fderiv_eq_innerSL_gradient, hcrit, map_zero]
  · have := hcoer v
    rwa [inner_toEuclideanLin_hessianMatrix hd, RCLike.re_to_real] at this

/-- **Section 7.2.1** of [quarteroni2000numerical]. A point $x^*$ is a **critical point** of
$f : \mathbb{R}^n \to \mathbb{R}$ if $\nabla f(x^*) = 0$.

By Property 7.4(a) this is necessary for a local minimum. It is sufficient when $f$ is convex,
by `QuarteroniSaccoSaleri.Chapter07.isMinOn_of_convexOn_of_isCriticalPoint`. Where $f$ is not
differentiable, `gradient f x` is $0$, so such a point counts as critical. -/
def IsCriticalPoint (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  gradient f x = 0

/-- **Section 7.2.1** of [quarteroni2000numerical], the remark after Property 7.4. Let
$f : \mathbb{R}^n \to \mathbb{R}$ be convex in the sense of (7.21) and differentiable
everywhere. Then every critical point of $f$ is a global minimizer of $f$.

This is Property 7.9(2) with $\Omega = \mathbb{R}^n$. The proof uses
`isMinOn_iff_forall_lineDeriv_nonneg`. -/
theorem isMinOn_of_convexOn_of_isCriticalPoint (hconv : ConvexOn ℝ univ f)
    (hf : ∀ y, DifferentiableAt ℝ f y) {x : EuclideanSpace ℝ (Fin n)} (hx : IsCriticalPoint f x) :
    IsMinOn f univ x := by
  refine (isMinOn_iff_forall_lineDeriv_nonneg (f' := fderiv ℝ f) hconv
    (fun u _ h => (hf u).hasFDerivAt.hasLineDerivAt h) (mem_univ x)).2 fun v _ => ?_
  rw [fderiv_eq_innerSL_gradient, hx, map_zero]
  rfl

end Property74

/-! ### Example 7.5: the Rosenbrock function -/

/-- **Equation (7.24)** of [quarteroni2000numerical], the **Rosenbrock function**
$$f(x) = 100 (x_2 - x_1^2)^2 + (1 - x_1)^2$$
on $\mathbb{R}^2$.

The components $x_1, x_2$ of the source are `x 0` and `x 1`. -/
noncomputable def rosenbrock (x : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  100 * (x 1 - x 0 ^ 2) ^ 2 + (1 - x 0) ^ 2

/-- **Example 7.5** of [quarteroni2000numerical]. The Rosenbrock function has a global minimizer at
$(1, 1)$, where its value is $0$, and it has no other global minimizer.

The rest of the example is a numerical comparison of methods. -/
theorem example_7_5 :
    IsMinOn rosenbrock univ !₂[1, 1] ∧ rosenbrock !₂[1, 1] = 0 ∧
      ∀ y, IsMinOn rosenbrock univ y → y = !₂[1, 1] := by
  have h0 : rosenbrock !₂[1, 1] = 0 := by simp [rosenbrock]
  have hnn : ∀ y, 0 ≤ rosenbrock y := fun y => by unfold rosenbrock; positivity
  refine ⟨isMinOn_iff.2 fun y _ => by rw [h0]; exact hnn y, h0, fun y hy => ?_⟩
  have hy0 : rosenbrock y = 0 :=
    le_antisymm (by simpa [h0] using isMinOn_iff.1 hy _ (mem_univ !₂[1, 1])) (hnn y)
  have h1 : y 0 = 1 := by
    unfold rosenbrock at hy0
    nlinarith [sq_nonneg (y 1 - y 0 ^ 2), sq_nonneg (1 - y 0)]
  have h2 : y 1 = 1 := by
    unfold rosenbrock at hy0
    rw [h1] at hy0
    nlinarith [sq_nonneg (y 1 - 1)]
  ext i
  fin_cases i <;> simp [h1, h2]

/-! ### Descent methods, Theorem 7.3, and the line search conditions -/

section Descent

variable {f : EuclideanSpace ℝ (Fin n) → ℝ}

/-- **Equations (7.27)–(7.28)** of [quarteroni2000numerical]. Let $f : \mathbb{R}^n \to \mathbb{R}$
be differentiable at $x$, and let $d$ be a descent direction at $x$ in the sense of (7.26), that
is, $d^T \nabla f(x) < 0$. Then there is $\varepsilon > 0$ with $f(x + \alpha d) < f(x)$ for
every $\alpha \in (0, \varepsilon)$.

The proof specializes `Descent.exists_forall_lt_of_isDescentDirection`. -/
theorem equation_7_27 {x d : EuclideanSpace ℝ (Fin n)} (hf : DifferentiableAt ℝ f x)
    (hd : ⟪gradient f x, d⟫_ℝ < 0) : ∃ ε > 0, ∀ α ∈ Ioo (0 : ℝ) ε, f (x + α • d) < f x :=
  Descent.exists_forall_lt_of_isDescentDirection (f' := fderiv ℝ f) hf.hasFDerivAt
    (by rw [Descent.IsDescentDirection, fderiv_eq_innerSL_gradient, innerSL_apply_apply]; exact hd)

/-- **Section 7.2.2** of [quarteroni2000numerical], the descent directions. Let
$f : \mathbb{R}^n \to \mathbb{R}$ and $x \in \mathbb{R}^n$ with $\nabla f(x) \neq 0$. Then:

* the steepest-descent direction $d = -\nabla f(x)$ is a descent direction;
* $d^T \nabla f(x) = -\|\nabla f(x)\|_2^2$;
* for every symmetric positive definite $B \in \mathbb{R}^{n \times n}$, the direction
  $d = -B^{-1} \nabla f(x)$ is a descent direction.

The matrix $B$ is the Hessian $H(x)$ for the Newton direction, or an approximation $B_k$ of it
for the inexact Newton directions. A descent direction is `Descent.IsDescentDirection`. The
hypothesis $\nabla f(x) \neq 0$ makes $f$ differentiable at $x$, because the gradient of Mathlib
is $0$ at a point of nondifferentiability. The proof specializes
`Descent.isDescentDirection_neg_gradient` and
`Descent.isDescentDirection_neg_inverse_of_isCoercive`. -/
theorem steepestDescent_isDescentDirection {x : EuclideanSpace ℝ (Fin n)}
    (hx : gradient f x ≠ 0) :
    Descent.IsDescentDirection (fderiv ℝ f) x (-gradient f x) ∧
      ⟪gradient f x, -gradient f x⟫_ℝ = -‖gradient f x‖ ^ 2 ∧
      ∀ B : Matrix (Fin n) (Fin n) ℝ, B.PosDef →
        Descent.IsDescentDirection (fderiv ℝ f) x
          (-(toEuclideanCLM (𝕜 := ℝ) B⁻¹ (gradient f x))) := by
  have hg : fderiv ℝ f x = innerSL ℝ (gradient f x) := fderiv_eq_innerSL_gradient f x
  refine ⟨Descent.isDescentDirection_neg_gradient hg hx, ?_, fun B hB => ?_⟩
  · rw [inner_neg_right, real_inner_self_eq_norm_sq]
  · have hu : IsUnit B := hB.isUnit
    let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
      ContinuousLinearEquiv.equivOfInverse (toEuclideanCLM (𝕜 := ℝ) B)
        (toEuclideanCLM (𝕜 := ℝ) B⁻¹)
        (fun v => by
          change toEuclideanLin B⁻¹ (toEuclideanLin B v) = v
          exact toEuclideanLin_nonsing_inv_mul_apply hu v)
        (fun v => by
          change toEuclideanLin B (toEuclideanLin B⁻¹ v) = v
          exact toEuclideanLin_mul_nonsing_inv_apply hu v)
    have hcoer : ((e : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
        EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)).IsCoercive := by
      have := ((Matrix.posDef_iff_isSymmetricCoercive B).1 hB).isCoercive
      exact this
    exact Descent.isDescentDirection_neg_inverse_of_isCoercive hg hx e hcoer

/-- **Theorem 7.3** of [quarteroni2000numerical]. Let $x^{(k)}$, $d^{(k)}$ and $\alpha_k$ form a
descent method (7.25) for $f : \mathbb{R}^n \to \mathbb{R}$. Suppose that at step $k$ the step
$\alpha_k$ is a local minimizer of the one-dimensional problem (7.29),
$\varphi(\alpha) = f(x^{(k)} + \alpha d^{(k)})$, and that $f$ is differentiable at $x^{(k+1)}$.
Then
$$\nabla f(x^{(k+1)})^T d^{(k)} = 0.$$

The descent method is `Descent.IsDescentSequence`. The proof specializes
`Descent.fderiv_apply_eq_zero_of_isLocalMin_line`. -/
theorem theorem_7_3 {x d : ℕ → EuclideanSpace ℝ (Fin n)} {α : ℕ → ℝ}
    (hseq : Descent.IsDescentSequence (fderiv ℝ f) x d α) (k : ℕ)
    (hf : DifferentiableAt ℝ f (x (k + 1)))
    (hα : IsLocalMin (fun t : ℝ => f (x k + t • d k)) (α k)) :
    ⟪gradient f (x (k + 1)), d k⟫_ℝ = 0 := by
  rw [← innerSL_apply_apply, ← fderiv_eq_innerSL_gradient, hseq.step k]
  rw [hseq.step k] at hf
  exact Descent.fderiv_apply_eq_zero_of_isLocalMin_line hf.hasFDerivAt hα

variable {x d : EuclideanSpace ℝ (Fin n)} {σ β α : ℝ}

/-- **Equation (7.31)** of [quarteroni2000numerical], the Armijo condition. Let
$f : \mathbb{R}^n \to \mathbb{R}$, let $x, d \in \mathbb{R}^n$, $\sigma \in \mathbb{R}$ and
$\alpha > 0$. The backbone's Armijo condition $f(x + \alpha d) \le f(x) + \sigma \alpha \nabla
f(x)^T d$ holds if and only if
$$\frac{f(x) - f(x + \alpha d)}{\alpha} \ge -\sigma \nabla f(x)^T d,$$
that is, the average rate of descent over the step is at least the fraction $\sigma$ of the
initial rate of descent.

**Reading.** The source prints (7.31) with an additional outer inequality
$0 \ge v_M(x^{(k+1)})$. The Armijo condition is the inner inequality; for a descent direction
the outer one is a consequence of it, not part of the condition.

The condition is `LineSearch.Armijo f (fderiv ℝ f) σ x d α`. -/
theorem equation_7_31 (hα : 0 < α) :
    LineSearch.Armijo f (fderiv ℝ f) σ x d α ↔
      -σ * ⟪gradient f x, d⟫_ℝ ≤ (f x - f (x + α • d)) / α := by
  rw [LineSearch.Armijo, fderiv_eq_innerSL_gradient, innerSL_apply_apply, le_div_iff₀ hα]
  constructor <;> intro h <;> linarith

/-- **Equations (7.32)–(7.33)** of [quarteroni2000numerical], the curvature conditions. Let
$f : \mathbb{R}^n \to \mathbb{R}$, $x, d \in \mathbb{R}^n$ and $\alpha, \beta \in \mathbb{R}$.
Then:

* the strong Wolfe condition (7.32) is $|\nabla f(x + \alpha d)^T d| \le \beta |\nabla f(x)^T
  d|$;
* the weak Wolfe condition (7.33) is $\nabla f(x + \alpha d)^T d \ge \beta \nabla f(x)^T d$;
* if $\nabla f(x)^T d < 0$, the strong condition implies the weak one.

The conditions are `LineSearch.StrongWolfeCurvature` and `LineSearch.WolfeCurvature`. -/
theorem equation_7_32 :
    (LineSearch.StrongWolfeCurvature (fderiv ℝ f) β x d α ↔
        |⟪gradient f (x + α • d), d⟫_ℝ| ≤ β * |⟪gradient f x, d⟫_ℝ|) ∧
      (LineSearch.WolfeCurvature (fderiv ℝ f) β x d α ↔
        β * ⟪gradient f x, d⟫_ℝ ≤ ⟪gradient f (x + α • d), d⟫_ℝ) ∧
      (⟪gradient f x, d⟫_ℝ < 0 → LineSearch.StrongWolfeCurvature (fderiv ℝ f) β x d α →
        LineSearch.WolfeCurvature (fderiv ℝ f) β x d α) := by
  refine ⟨?_, ?_, fun hd h => h.wolfeCurvature ?_⟩
  · rw [LineSearch.StrongWolfeCurvature, fderiv_eq_innerSL_gradient, fderiv_eq_innerSL_gradient,
      innerSL_apply_apply, innerSL_apply_apply]
  · rw [LineSearch.WolfeCurvature, fderiv_eq_innerSL_gradient, fderiv_eq_innerSL_gradient,
      innerSL_apply_apply, innerSL_apply_apply]
  · rw [Descent.IsDescentDirection, fderiv_eq_innerSL_gradient, innerSL_apply_apply]
    exact hd

/-- **Equation (7.34)** of [quarteroni2000numerical], the Goldstein conditions, and the Armijo rule.
Let $f : \mathbb{R}^n \to \mathbb{R}$, let $d$ be a descent direction at $x$,
$\nabla f(x)^T d < 0$, and let $\alpha > 0$. Then:

* the Goldstein conditions hold if and only if $$\sigma \le \frac{f(x + \alpha d) - f(x)}{\alpha
  \nabla f(x)^T d} \le 1 - \sigma;$$
* if $f$ is differentiable at $x$, $\sigma < 1$ and $0 < \beta < 1$, then for every
  $\bar{\alpha} > 0$ some $m \in \mathbb{N}$ makes $\beta^m \bar{\alpha}$ satisfy the Armijo
  condition (7.31).

The second part says that the Armijo rule $\alpha_k = \beta^{m_k} \bar{\alpha}$, with $m_k$ the
first nonnegative integer for which (7.31) holds, is well defined. The Goldstein conditions are
`LineSearch.Goldstein`. The second part uses
`LineSearch.eventually_armijo_of_isDescentDirection`. -/
theorem equation_7_34 (hd : ⟪gradient f x, d⟫_ℝ < 0) (hα : 0 < α) :
    (LineSearch.Goldstein f (fderiv ℝ f) σ x d α ↔
      σ ≤ (f (x + α • d) - f x) / (α * ⟪gradient f x, d⟫_ℝ) ∧
        (f (x + α • d) - f x) / (α * ⟪gradient f x, d⟫_ℝ) ≤ 1 - σ) ∧
      (DifferentiableAt ℝ f x → σ < 1 → 0 < β → β < 1 → ∀ a : ℝ, 0 < a →
        ∃ m : ℕ, LineSearch.Armijo f (fderiv ℝ f) σ x d (β ^ m * a)) := by
  have hneg : α * ⟪gradient f x, d⟫_ℝ < 0 := mul_neg_of_pos_of_neg hα hd
  refine ⟨?_, fun hf hσ hβ0 hβ1 a ha => ?_⟩
  · rw [LineSearch.Goldstein, fderiv_eq_innerSL_gradient, innerSL_apply_apply,
      le_div_iff_of_neg hneg, div_le_iff_of_neg hneg]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, by linarith⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, by linarith⟩
  · have hdesc : Descent.IsDescentDirection (fderiv ℝ f) x d := by
      rw [Descent.IsDescentDirection, fderiv_eq_innerSL_gradient, innerSL_apply_apply]
      exact hd
    have ht : Tendsto (fun m : ℕ => β ^ m * a) atTop (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun m => ?_⟩
      · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).mul_const a
      · exact mul_pos (pow_pos hβ0 m) ha
    exact (ht.eventually (LineSearch.eventually_armijo_of_isDescentDirection hf.hasFDerivAt
      hdesc hσ)).exists

-- The book restricts `σ ∈ (0, 1/2)`; the backbone proves the statement for every `0 < σ < β < 1`
-- (`LineSearch.exists_Icc_armijo_wolfe`), so `hσ2` is carried for fidelity only.
set_option linter.unusedVariables false in
/-- **Property 7.5** of [quarteroni2000numerical]. Let $f : \mathbb{R}^n \to \mathbb{R}$ be of class
$C^1$ and bounded below, $f(x) \ge M$ for all $x$. Let $d$ be a descent direction at $x$,
$\nabla f(x)^T d < 0$, and let $0 < \sigma < 1/2$ and $\sigma < \beta < 1$. Then there are
$0 < c < C$ such that every $\alpha \in [c, C]$ satisfies the Armijo condition (7.31), the
strong Wolfe condition (7.32) and the weak Wolfe condition (7.33).

The restriction $\sigma < 1/2$ of the source is kept, but the proof does not use it. The proof
specializes `LineSearch.exists_Icc_armijo_wolfe`, which holds for every
$0 < \sigma < \beta < 1$. -/
theorem property_7_5 (hf : ContDiff ℝ 1 f) {M : ℝ} (hM : ∀ y, M ≤ f y)
    (hd : ⟪gradient f x, d⟫_ℝ < 0) (hσ : 0 < σ) (hσ2 : σ < 1 / 2) (hσβ : σ < β) (hβ : β < 1) :
    ∃ c C : ℝ, 0 < c ∧ c < C ∧ ∀ α ∈ Icc c C,
      LineSearch.Armijo f (fderiv ℝ f) σ x d α ∧
        LineSearch.StrongWolfeCurvature (fderiv ℝ f) β x d α ∧
        LineSearch.WolfeCurvature (fderiv ℝ f) β x d α := by
  have hdesc : Descent.IsDescentDirection (fderiv ℝ f) x d := by
    rw [Descent.IsDescentDirection, fderiv_eq_innerSL_gradient, innerSL_apply_apply]
    exact hd
  obtain ⟨c, C, hc, hcC, h⟩ := LineSearch.exists_Icc_armijo_wolfe
    (fun y => (hf.differentiable one_ne_zero y).hasFDerivAt) (hf.continuous_fderiv one_ne_zero)
    (fun t => hM (x + t • d)) hdesc hσ hσβ hβ
  exact ⟨c, C, hc, hcC, fun α hα => ⟨(h α hα).1, (h α hα).2.2, (h α hα).2.1⟩⟩

end Descent

/-! ### The quadratic case: (7.35)–(7.39), Lemma 7.1 and Property 7.6 -/

section Quadratic

variable {A : Matrix (Fin n) (Fin n) ℝ} {b : EuclideanSpace ℝ (Fin n)}

/-- A real symmetric matrix $A$ acts on $\mathbb{R}^n$ as a symmetric operator. -/
private theorem isSymmetric_toEuclideanCLM (hA : A.IsSymm) :
    ((toEuclideanCLM (𝕜 := ℝ) A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
      EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)).IsSymmetric := by
  rw [coe_toEuclideanCLM_eq_toEuclideanLin]
  exact hA.isSymmetric_toEuclideanLin

/-- **Equation (7.35)** of [quarteroni2000numerical] and the display after it. Let
$A \in \mathbb{R}^{n \times n}$ be symmetric and $b \in \mathbb{R}^n$. The quadratic
$$f(x) = \frac{1}{2} x^T A x - b^T x$$
has the gradient $\nabla f(x) = A x - b = -r$, the negative of the residual, and the Hessian
matrix $H(x) = A$ at every $x$.

The quadratic is the backbone's `energyFunctional (toEuclideanLin A) b`. The proof uses
`hasGradientAt_energyFunctional`. -/
theorem equation_7_35 (hA : A.IsSymm) (x : EuclideanSpace ℝ (Fin n)) :
    energyFunctional (toEuclideanLin A) b x
        = (ofLp x ⬝ᵥ (A *ᵥ ofLp x)) / 2 - ofLp b ⬝ᵥ ofLp x ∧
      gradient (energyFunctional (toEuclideanLin A) b) x = toEuclideanLin A x - b ∧
      hessianMatrix (energyFunctional (toEuclideanLin A) b) x = A := by
  have hA' := isSymmetric_toEuclideanCLM hA
  have hgrad : ∀ y, HasFDerivAt (energyFunctional (toEuclideanLin A) b)
      (innerSL ℝ (toEuclideanCLM (𝕜 := ℝ) A y - b)) y := fun y => by
    have := hasFDerivAt_energyFunctional (A := toEuclideanCLM (𝕜 := ℝ) A) hA' b y
    rwa [coe_toEuclideanCLM_eq_toEuclideanLin] at this
  refine ⟨?_, ?_, ?_⟩
  · simp only [energyFunctional, RCLike.re_to_real, EuclideanSpace.inner_eq_star_dotProduct,
      star_trivial, ofLp_toEuclideanLin]
    rw [dotProduct_comm (ofLp x) (ofLp b)]
  · have := hasGradientAt_energyFunctional (A := toEuclideanCLM (𝕜 := ℝ) A) hA' b x
    rw [coe_toEuclideanCLM_eq_toEuclideanLin] at this
    exact this.gradient
  · have hfd : fderiv ℝ (energyFunctional (toEuclideanLin A) b)
        = fun y => innerSL ℝ (toEuclideanCLM (𝕜 := ℝ) A y - b) := funext fun y => (hgrad y).fderiv
    ext i j
    rw [hessianMatrix, Matrix.of_apply]
    have hfun : (fun y => fderiv ℝ (energyFunctional (toEuclideanLin A) b) y
          (EuclideanSpace.single j 1))
        = fun y => ⟪EuclideanSpace.single j 1, toEuclideanCLM (𝕜 := ℝ) A y⟫_ℝ
          - ⟪EuclideanSpace.single j 1, b⟫_ℝ := by
      funext y
      rw [hfd, innerSL_apply_apply, inner_sub_left, real_inner_comm, real_inner_comm b]
    have hder : HasFDerivAt (fun y => ⟪EuclideanSpace.single j 1, toEuclideanCLM (𝕜 := ℝ) A y⟫_ℝ
          - ⟪EuclideanSpace.single j 1, b⟫_ℝ)
        ((innerSL ℝ (EuclideanSpace.single j 1)).comp (toEuclideanCLM (𝕜 := ℝ) A)) x :=
      ((innerSL ℝ (EuclideanSpace.single j 1)).comp
        (toEuclideanCLM (𝕜 := ℝ) A)).hasFDerivAt.sub_const _
    rw [hfun, hder.fderiv, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
      EuclideanSpace.inner_single_left, ofLp_toEuclideanCLM]
    simp [hA.apply i j]

/-- **Equation (7.36)** of [quarteroni2000numerical], the exact line search for the quadratic. Let
$A \in \mathbb{R}^{n \times n}$ be symmetric positive definite, $b, x \in \mathbb{R}^n$,
$r = b - A x$, and let $d \neq 0$. Then the problem of minimizing
$\alpha \mapsto f(x + \alpha d)$ for the quadratic (7.35) has the unique solution
$$\alpha = \frac{d^T r}{d^T A d},$$
and the new point $x + \alpha d$ is the backbone's
`Projection.step1 (toEuclideanLin A) b d d x`.

Minimality is `Projection.step1_isGalerkin` with `IsGalerkin.quadratic_le`. Uniqueness follows
from the expansion $f(x + t d) = f(x + \alpha d) + \frac{1}{2} (t - \alpha)^2 d^T A d$, by
`LinearMap.IsSymmetric.energyFunctional_add`. -/
theorem equation_7_36 (hA : A.PosDef) (x : EuclideanSpace ℝ (Fin n))
    {d : EuclideanSpace ℝ (Fin n)} (hd : d ≠ 0) :
    Projection.step1 (toEuclideanLin A) b d d x
        = x + (⟪d, b - toEuclideanLin A x⟫_ℝ / ⟪d, toEuclideanLin A d⟫_ℝ) • d ∧
      IsMinOn (fun t : ℝ => energyFunctional (toEuclideanLin A) b (x + t • d)) univ
        (⟪d, b - toEuclideanLin A x⟫_ℝ / ⟪d, toEuclideanLin A d⟫_ℝ) ∧
      ∀ t : ℝ, IsMinOn (fun t : ℝ => energyFunctional (toEuclideanLin A) b (x + t • d)) univ t →
        t = ⟪d, b - toEuclideanLin A x⟫_ℝ / ⟪d, toEuclideanLin A d⟫_ℝ := by
  have hAsc := (Matrix.posDef_iff_isSymmetricCoercive A).1 hA
  set α : ℝ := ⟪d, b - toEuclideanLin A x⟫_ℝ / ⟪d, toEuclideanLin A d⟫_ℝ with hα
  set φ : ℝ → ℝ := fun t => energyFunctional (toEuclideanLin A) b (x + t • d) with hφ
  have hstep : Projection.step1 (toEuclideanLin A) b d d x = x + α • d := rfl
  -- the exact expansion along the line
  have hq : 0 < ⟪toEuclideanLin A d, d⟫_ℝ := by
    simpa using hAsc.isCoercive.inner_self_pos hd
  have hqs : ⟪d, toEuclideanLin A d⟫_ℝ = ⟪toEuclideanLin A d, d⟫_ℝ := real_inner_comm _ _
  have hexp : ∀ t, φ t = φ α + ⟪toEuclideanLin A d, d⟫_ℝ / 2 * (t - α) ^ 2 := by
    intro t
    have h1 := hAsc.isSymmetric.energyFunctional_add b x (t • d)
    have h2 := hAsc.isSymmetric.energyFunctional_add b x (α • d)
    simp only [hφ, RCLike.re_to_real, inner_smul_right, inner_smul_left, map_smul,
      RCLike.conj_to_real] at h1 h2 ⊢
    rw [h1, h2]
    have hα' : α * ⟪toEuclideanLin A d, d⟫_ℝ = ⟪d, b - toEuclideanLin A x⟫_ℝ := by
      rw [hα, hqs, div_mul_cancel₀ _ hq.ne']
    have hr : ⟪toEuclideanLin A x - b, d⟫_ℝ = -⟪d, b - toEuclideanLin A x⟫_ℝ := by
      rw [real_inner_comm, ← inner_neg_right, neg_sub]
    rw [hr]
    linear_combination (t - α) * hα'
  refine ⟨hstep, isMinOn_iff.2 fun t _ => ?_, fun t ht => ?_⟩
  · have hgal := Projection.step1_isGalerkin (b := b) hAsc.isCoercive d x
    have := IsGalerkin.quadratic_le hAsc hgal (y := x + t • d)
      (by
        rw [add_sub_cancel_left]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self d))
    rw [hstep] at this
    exact this
  · have h1 := isMinOn_iff.1 ht α (mem_univ α)
    have h2 := hexp t
    have h3 : (t - α) ^ 2 = 0 := by
      have hnn : 0 ≤ ⟪toEuclideanLin A d, d⟫_ℝ / 2 * (t - α) ^ 2 := by positivity
      have : ⟪toEuclideanLin A d, d⟫_ℝ / 2 * (t - α) ^ 2 ≤ 0 := by
        change φ t ≤ φ α at h1
        linarith
      have hz : ⟪toEuclideanLin A d, d⟫_ℝ / 2 * (t - α) ^ 2 = 0 := le_antisymm this hnn
      rcases mul_eq_zero.1 hz with h | h
      · exact absurd h (by positivity)
      · exact h
    exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h3)

/-- **Equations (7.37)–(7.38)** of [quarteroni2000numerical]. Let $A \in \mathbb{R}^{n \times n}$ be
symmetric positive definite, let $A x^* = b$, and let $x, d \in \mathbb{R}^n$ with
$r = b - A x$. Let $x_+$ be the point after the exact step (7.36) along $d$. Then
$$\|x_+ - x^*\|_A^2 = \rho \, \|x - x^*\|_A^2, \qquad \rho = 1 - \sigma, \qquad \sigma =
  \frac{(d^T r)^2}{(d^T A d)(r^T A^{-1} r)},$$
where $r^T A^{-1} r = \|x - x^*\|_A^2$. If moreover $d \neq 0$ and $x \neq x^*$, then $\rho < 1$
when $d^T r \neq 0$, and $\rho = 1$ when $d^T r = 0$.

The energy norm is `energyNorm (toEuclideanLin A)`. The statement is over $\mathbb{R}$, where
the backbone's $|d^T r|^2$ is $(d^T r)^2$. The proof specializes
`Projection.energyNorm_step1_sq_eq_mul`. -/
theorem equation_7_38 (hA : A.PosDef) {xstar : EuclideanSpace ℝ (Fin n)}
    (hstar : toEuclideanLin A xstar = b) (x d : EuclideanSpace ℝ (Fin n)) :
    energyNorm (toEuclideanLin A) (xstar - Projection.step1 (toEuclideanLin A) b d d x) ^ 2
        = (1 - ⟪d, b - toEuclideanLin A x⟫_ℝ ^ 2 / (⟪d, toEuclideanLin A d⟫_ℝ *
            ⟪b - toEuclideanLin A x, toEuclideanLin A⁻¹ (b - toEuclideanLin A x)⟫_ℝ))
          * energyNorm (toEuclideanLin A) (xstar - x) ^ 2 ∧
      ⟪b - toEuclideanLin A x, toEuclideanLin A⁻¹ (b - toEuclideanLin A x)⟫_ℝ
        = energyNorm (toEuclideanLin A) (xstar - x) ^ 2 ∧
      (d ≠ 0 → x ≠ xstar →
        (⟪d, b - toEuclideanLin A x⟫_ℝ ≠ 0 →
          1 - ⟪d, b - toEuclideanLin A x⟫_ℝ ^ 2 / (⟪d, toEuclideanLin A d⟫_ℝ *
            ⟪b - toEuclideanLin A x, toEuclideanLin A⁻¹ (b - toEuclideanLin A x)⟫_ℝ) < 1) ∧
        (⟪d, b - toEuclideanLin A x⟫_ℝ = 0 →
          1 - ⟪d, b - toEuclideanLin A x⟫_ℝ ^ 2 / (⟪d, toEuclideanLin A d⟫_ℝ *
            ⟪b - toEuclideanLin A x, toEuclideanLin A⁻¹ (b - toEuclideanLin A x)⟫_ℝ) = 1)) := by
  have hAsc := (Matrix.posDef_iff_isSymmetricCoercive A).1 hA
  have hu : IsUnit A := hA.isUnit
  have hr : b - toEuclideanLin A x = toEuclideanLin A (xstar - x) := by rw [map_sub, hstar]
  have hres : ⟪b - toEuclideanLin A x, toEuclideanLin A⁻¹ (b - toEuclideanLin A x)⟫_ℝ
      = energyNorm (toEuclideanLin A) (xstar - x) ^ 2 := by
    rw [hr, toEuclideanLin_nonsing_inv_mul_apply hu, hAsc.energyNorm_sq, RCLike.re_to_real]
  refine ⟨?_, hres, fun hd hx => ?_⟩
  · rw [Projection.energyNorm_step1_sq_eq_mul hAsc hstar d x, hres, mul_comm, Real.norm_eq_abs,
      sq_abs, RCLike.re_to_real, real_inner_comm d (toEuclideanLin A d)]
  · have hq : 0 < ⟪d, toEuclideanLin A d⟫_ℝ := by
      rw [real_inner_comm]; simpa using hAsc.isCoercive.inner_self_pos hd
    have he : 0 < energyNorm (toEuclideanLin A) (xstar - x) ^ 2 :=
      pow_pos (hAsc.energyNorm_pos (sub_ne_zero.2 (Ne.symm hx))) 2
    rw [hres]
    refine ⟨fun hdr => ?_, fun hdr => by rw [hdr]; simp⟩
    have : 0 < ⟪d, b - toEuclideanLin A x⟫_ℝ ^ 2 / (⟪d, toEuclideanLin A d⟫_ℝ *
        energyNorm (toEuclideanLin A) (xstar - x) ^ 2) :=
      div_pos (by positivity) (mul_pos hq he)
    linarith

/-- **Equation (7.39)** of [quarteroni2000numerical], the steepest descent method. Let
$A \in \mathbb{R}^{n \times n}$ be symmetric positive definite with smallest eigenvalue
$\lambda_{\min}$ and largest eigenvalue $\lambda_{\max}$, let $A x^* = b$, and let
$x \in \mathbb{R}^n$. The steepest descent step from $x$ is the exact step (7.36) along the
residual $d = r = b - A x$, and the new point $x_+$ satisfies
$$\|x_+ - x^*\|_A \le \frac{\lambda_{\max} - \lambda_{\min}}{\lambda_{\max} + \lambda_{\min}}
  \|x - x^*\|_A.$$

The step is the backbone's `Projection.steepestDescentStep`. The proof specializes
`Projection.energyNorm_steepestDescentStep_le` with
`Matrix.IsHermitian.isSymmetricBoundedBy_toEuclideanLin`. -/
theorem equation_7_39 (hA : A.PosDef) {lmin lmax : ℝ}
    (hmin : IsLeast (Set.range hA.1.eigenvalues) lmin)
    (hmax : IsGreatest (Set.range hA.1.eigenvalues) lmax) {xstar : EuclideanSpace ℝ (Fin n)}
    (hstar : toEuclideanLin A xstar = b) (x : EuclideanSpace ℝ (Fin n)) :
    Projection.steepestDescentStep (toEuclideanLin A) b x
        = Projection.step1 (toEuclideanLin A) b (b - toEuclideanLin A x)
          (b - toEuclideanLin A x) x ∧
      energyNorm (toEuclideanLin A) (xstar - Projection.steepestDescentStep (toEuclideanLin A) b x)
        ≤ (lmax - lmin) / (lmax + lmin) * energyNorm (toEuclideanLin A) (xstar - x) := by
  obtain ⟨i, hi⟩ := hmin.1
  have hl : 0 < lmin := hi ▸ hA.eigenvalues_pos i
  have hAb : (toEuclideanLin A).IsSymmetricBoundedBy lmin lmax :=
    hA.1.isSymmetricBoundedBy_toEuclideanLin fun j =>
      ⟨hmin.2 (Set.mem_range_self j), hmax.2 (Set.mem_range_self j)⟩
  exact ⟨rfl, Projection.energyNorm_steepestDescentStep_le hl hAb hstar x⟩

/-- **Lemma 7.1** of [quarteroni2000numerical] (Kantorovich inequality). Let
$A \in \mathbb{R}^{n \times n}$ be symmetric positive definite with smallest eigenvalue
$\lambda_{\min}$ and largest eigenvalue $\lambda_{\max}$. Then for every $y \neq 0$
$$\frac{(y^T y)^2}{(y^T A y)(y^T A^{-1} y)} \ge \frac{4 \lambda_{\max}
  \lambda_{\min}}{(\lambda_{\max} + \lambda_{\min})^2}.$$

This is the reciprocal form of the backbone's `Projection.kantorovich_inequality`. -/
theorem lemma_7_1 (hA : A.PosDef) {lmin lmax : ℝ}
    (hmin : IsLeast (Set.range hA.1.eigenvalues) lmin)
    (hmax : IsGreatest (Set.range hA.1.eigenvalues) lmax) {y : EuclideanSpace ℝ (Fin n)}
    (hy : y ≠ 0) :
    4 * lmax * lmin / (lmax + lmin) ^ 2
      ≤ ⟪y, y⟫_ℝ ^ 2 / (⟪y, toEuclideanLin A y⟫_ℝ * ⟪y, toEuclideanLin A⁻¹ y⟫_ℝ) := by
  obtain ⟨i, hi⟩ := hmin.1
  have hl : 0 < lmin := hi ▸ hA.eigenvalues_pos i
  have hlmax : lmin ≤ lmax := hmax.2 (hi ▸ Set.mem_range_self i)
  have hlmax0 : 0 < lmax := lt_of_lt_of_le hl hlmax
  have hAb : (toEuclideanLin A).IsSymmetricBoundedBy lmin lmax :=
    hA.1.isSymmetricBoundedBy_toEuclideanLin fun j =>
      ⟨hmin.2 (Set.mem_range_self j), hmax.2 (Set.mem_range_self j)⟩
  have hu : IsUnit A := hA.isUnit
  have hk := Projection.kantorovich_inequality hl hAb y (y := toEuclideanLin A⁻¹ y)
    (toEuclideanLin_mul_nonsing_inv_apply hu y)
  simp only [RCLike.re_to_real] at hk
  have hp1 : 0 < ⟪toEuclideanLin A y, y⟫_ℝ := by
    simpa using ((Matrix.posDef_iff_isSymmetricCoercive A).1 hA).isCoercive.inner_self_pos hy
  have hp2 : 0 < ⟪toEuclideanLin A⁻¹ y, y⟫_ℝ := by
    simpa using ((Matrix.posDef_iff_isSymmetricCoercive A⁻¹).1 hA.inv).isCoercive.inner_self_pos hy
  have hpos : 0 < 4 * lmax * lmin := by positivity
  rw [real_inner_comm (toEuclideanLin A y) y, real_inner_comm (toEuclideanLin A⁻¹ y) y,
    real_inner_self_eq_norm_sq, div_le_div_iff₀ (by positivity) (mul_pos hp1 hp2)]
  have hk' : 4 * lmax * lmin * (⟪toEuclideanLin A y, y⟫_ℝ * ⟪toEuclideanLin A⁻¹ y, y⟫_ℝ)
      ≤ (lmax + lmin) ^ 2 * ‖y‖ ^ 4 := by
    have := mul_le_mul_of_nonneg_left hk hpos.le
    have heq : 4 * lmax * lmin * ((lmax + lmin) ^ 2 / (4 * lmax * lmin) * ‖y‖ ^ 4)
        = (lmax + lmin) ^ 2 * ‖y‖ ^ 4 := by field_simp
    linarith
  nlinarith [hk']

/-- **Property 7.6** of [quarteroni2000numerical], the last clause. Let
$A \in \mathbb{R}^{n \times n}$ be symmetric positive definite, and let
$d^{(0)}, d^{(1)}, \dots$ be pairwise $A$-conjugate, $d^{(k)T} A d^{(m)} = 0$ for $k \neq m$.
Let $x^{(k)}$ be the iterates from $x^{(0)}$ with the steps (7.36) along these directions, and
$r^{(k)} = b - A x^{(k)}$. Then the residual is orthogonal to all the directions used so far:
$$r^{(k+1)T} d^{(m)} = 0 \qquad \text{for every } m \le k.$$

The conjugacy is `ConjugateDirection.IsConjugateFamily` and the iterates are
`ConjugateDirection.iterate`. The proof specializes
`ConjugateDirection.inner_residual_direction_eq_zero`. -/
theorem property_7_6_orthogonal (hA : A.PosDef) (x₀ : EuclideanSpace ℝ (Fin n))
    {d : ℕ → EuclideanSpace ℝ (Fin n)}
    (hd : ConjugateDirection.IsConjugateFamily (toEuclideanLin A) d) {k m : ℕ} (hm : m ≤ k) :
    ⟪b - toEuclideanLin A (ConjugateDirection.iterate (toEuclideanLin A) b d x₀ (k + 1)),
      d m⟫_ℝ = 0 :=
  ConjugateDirection.inner_residual_direction_eq_zero b x₀
    ((Matrix.posDef_iff_isSymmetricCoercive A).1 hA).isCoercive hd k m hm

/-- **Property 7.6** of [quarteroni2000numerical], the second clause. Let
$A \in \mathbb{R}^{n \times n}$ be symmetric positive definite, and let $x^{(k)}$ be the
iterates from $x^{(0)}$ with the steps (7.36) along pairwise $A$-conjugate directions
$d^{(0)}, d^{(1)}, \dots$. Then $x^{(k+1)}$ minimizes the quadratic (7.35) over the affine
subspace
$$x^{(0)} + \operatorname{span}\{d^{(0)}, \dots, d^{(k)}\}.$$

This affine subspace is the "subspace generated by $x^{(0)}, d^{(0)}, \dots, d^{(k)}$" of the
source. The proof specializes `ConjugateDirection.isGalerkin_iterate` with
`IsGalerkin.quadratic_le`. -/
theorem property_7_6_isMinOn (hA : A.PosDef) (x₀ : EuclideanSpace ℝ (Fin n))
    {d : ℕ → EuclideanSpace ℝ (Fin n)}
    (hd : ConjugateDirection.IsConjugateFamily (toEuclideanLin A) d) (k : ℕ) :
    IsMinOn (energyFunctional (toEuclideanLin A) b)
      {y | y - x₀ ∈ Submodule.span ℝ (Set.range fun i : Fin (k + 1) => d i)}
      (ConjugateDirection.iterate (toEuclideanLin A) b d x₀ (k + 1)) := by
  have hAsc := (Matrix.posDef_iff_isSymmetricCoercive A).1 hA
  exact isMinOn_iff.2 fun y hy =>
    IsGalerkin.quadratic_le hAsc (ConjugateDirection.isGalerkin_iterate b x₀ hAsc.isCoercive hd
      (k + 1)) hy

/-- **Property 7.6** of [quarteroni2000numerical], the first clause. Let
$A \in \mathbb{R}^{n \times n}$ be symmetric positive definite, let $A x^* = b$, and let
$d^{(0)}, d^{(1)}, \dots$ be pairwise $A$-conjugate with $d^{(i)} \neq 0$ for $i < n$. Then the
conjugate direction method with the steps (7.36) reaches the minimizer $x^*$ of the quadratic
(7.35) after at most $n$ steps: $x^{(k)} = x^*$ for every $k \ge n$.

The proof specializes `ConjugateDirection.iterate_eq_of_finrank_le`. -/
theorem property_7_6_termination (hA : A.PosDef) (x₀ : EuclideanSpace ℝ (Fin n))
    {d : ℕ → EuclideanSpace ℝ (Fin n)}
    (hd : ConjugateDirection.IsConjugateFamily (toEuclideanLin A) d) (h0 : ∀ i < n, d i ≠ 0)
    {xstar : EuclideanSpace ℝ (Fin n)} (hstar : toEuclideanLin A xstar = b) {k : ℕ}
    (hk : n ≤ k) : ConjugateDirection.iterate (toEuclideanLin A) b d x₀ k = xstar :=
  ConjugateDirection.iterate_eq_of_finrank_le b x₀
    ((Matrix.posDef_iff_isSymmetricCoercive A).1 hA).isCoercive hd
    (by rwa [finrank_euclideanSpace_fin]) hstar (by rwa [finrank_euclideanSpace_fin])

/-- **Section 7.2.4** of [quarteroni2000numerical], the conjugate gradient method for function
minimization. Let $A \in \mathbb{R}^{n \times n}$ be symmetric positive definite and
$x^{(0)} \in \mathbb{R}^n$. The conjugate gradient iterates $x^{(k)}$, residuals $r^{(k)}$ and
directions $d^{(k)}$ of the backbone's `CG.iterate (toEuclideanLin A) b x₀` satisfy:

* $x^{(k)}$ is the iterate of the conjugate direction method with the steps (7.36) along the
  directions $d^{(0)}, d^{(1)}, \dots$;
* $r^{(k)} = b - A x^{(k)}$;
* $d^{(0)} = r^{(0)}$ and $d^{(k+1)} = r^{(k+1)} + \beta_k d^{(k)}$;
* $\beta_k = r^{(k+1)T} r^{(k+1)} / r^{(k)T} r^{(k)}$;
* $\beta_k = -r^{(k+1)T} A d^{(k)} / d^{(k)T} A d^{(k)}$.

So the method of the source, with both expressions of $\beta_k$, is the backbone's conjugate
gradient iteration. The proof uses `CG.iterate_x_eq_conjugateDirection_iterate`,
`CG.beta_iterate` and `CG.inner_residual_eq_zero`. The error estimate $\|x^{(k)} - x^*\|_A \le 2
((\sqrt{K_2(A)} - 1)/(\sqrt{K_2(A)} + 1))^k \|x^{(0)} - x^*\|_A$ is the restatement in Chapter 4
of `Krylov.IsGalerkinIterate.energyNorm_error_le`. -/
theorem conjugateGradient_eq_CG (hA : A.PosDef) (x₀ : EuclideanSpace ℝ (Fin n)) :
    (∀ k, (CG.iterate (toEuclideanLin A) b x₀ k).x
        = ConjugateDirection.iterate (toEuclideanLin A) b
          (fun k => (CG.iterate (toEuclideanLin A) b x₀ k).p) x₀ k) ∧
      (∀ k, (CG.iterate (toEuclideanLin A) b x₀ k).r
        = b - toEuclideanLin A (CG.iterate (toEuclideanLin A) b x₀ k).x) ∧
      (CG.iterate (toEuclideanLin A) b x₀ 0).p = b - toEuclideanLin A x₀ ∧
      (∀ k, (CG.iterate (toEuclideanLin A) b x₀ (k + 1)).p
        = (CG.iterate (toEuclideanLin A) b x₀ (k + 1)).r
          + CG.beta (toEuclideanLin A) (CG.iterate (toEuclideanLin A) b x₀ k) •
            (CG.iterate (toEuclideanLin A) b x₀ k).p) ∧
      (∀ k, CG.beta (toEuclideanLin A) (CG.iterate (toEuclideanLin A) b x₀ k)
        = ⟪(CG.iterate (toEuclideanLin A) b x₀ (k + 1)).r,
            (CG.iterate (toEuclideanLin A) b x₀ (k + 1)).r⟫_ℝ /
          ⟪(CG.iterate (toEuclideanLin A) b x₀ k).r, (CG.iterate (toEuclideanLin A) b x₀ k).r⟫_ℝ) ∧
      ∀ k, CG.beta (toEuclideanLin A) (CG.iterate (toEuclideanLin A) b x₀ k)
        = -⟪(CG.iterate (toEuclideanLin A) b x₀ (k + 1)).r,
            toEuclideanLin A (CG.iterate (toEuclideanLin A) b x₀ k).p⟫_ℝ /
          ⟪(CG.iterate (toEuclideanLin A) b x₀ k).p,
            toEuclideanLin A (CG.iterate (toEuclideanLin A) b x₀ k).p⟫_ℝ := by
  have hAsc := (Matrix.posDef_iff_isSymmetricCoercive A).1 hA
  set A' := toEuclideanLin A with hA'
  refine ⟨CG.iterate_x_eq_conjugateDirection_iterate b x₀ hAsc, CG.residual_eq A' b x₀, rfl,
    CG.iterate_succ_p A' b x₀, CG.beta_iterate A' b x₀, fun k => ?_⟩
  rw [CG.beta_iterate]
  set s := CG.iterate A' b x₀ k with hs
  set s' := CG.iterate A' b x₀ (k + 1) with hs'
  rcases eq_or_ne s.r 0 with h0 | h0
  · -- a vanishing residual makes every quantity vanish
    have hr' : s'.r = 0 := by
      rw [hs', CG.iterate_succ_r, ← hs, h0, CG.alpha, h0, inner_zero_left, zero_div, zero_smul,
        sub_zero]
    rw [hr', h0]
    simp
  · have hq : 0 < ⟪A' s.p, s.p⟫_ℝ := by
      simpa using CG.re_inner_apply_direction_pos b x₀ hAsc h0
    have hα : CG.alpha A' s = ⟪s.r, s.r⟫_ℝ / ⟪A' s.p, s.p⟫_ℝ := rfl
    have hrr : 0 < ⟪s.r, s.r⟫_ℝ := real_inner_self_pos.2 h0
    have hα0 : CG.alpha A' s ≠ 0 := by rw [hα]; positivity
    -- `α A p = r - r'`
    have hAp : CG.alpha A' s • A' s.p = s.r - s'.r := by
      rw [hs', CG.iterate_succ_r, ← hs]; abel
    have horth : ⟪s'.r, s.r⟫_ℝ = 0 := CG.inner_residual_eq_zero b x₀ hAsc (Nat.succ_ne_self k)
    have h1 : CG.alpha A' s * ⟪s'.r, A' s.p⟫_ℝ = -⟪s'.r, s'.r⟫_ℝ := by
      rw [← inner_smul_right, hAp, inner_sub_right, horth, zero_sub]
    have h2 : ⟪s.p, A' s.p⟫_ℝ = ⟪A' s.p, s.p⟫_ℝ := real_inner_comm _ _
    rw [h2, div_eq_div_iff hrr.ne' hq.ne']
    rw [hα, div_mul_eq_mul_div, div_eq_iff hq.ne'] at h1
    linear_combination h1

/-- **Remark 7.2** of [quarteroni2000numerical] (the nonquadratic case). For gradients
$g_{\mathrm{old}}, g_{\mathrm{new}} \in \mathbb{R}^n$, the Fletcher–Reeves and Polak–Ribière
coefficients are
$$\beta^{\mathrm{FR}} = \frac{\|g_{\mathrm{new}}\|_2^2}{\|g_{\mathrm{old}}\|_2^2}, \qquad
  \beta^{\mathrm{PR}} = \frac{g_{\mathrm{new}}^T (g_{\mathrm{new}} -
  g_{\mathrm{old}})}{\|g_{\mathrm{old}}\|_2^2}.$$
For a gradient map $g$, a coefficient rule $\beta$ and a step rule $\alpha$, the nonlinear
conjugate gradient method starts with $d^{(0)} = -g(x^{(0)})$ and satisfies $d^{(k+1)} =
-g(x^{(k+1)}) + \beta(g(x^{(k)}), g(x^{(k+1)})) \, d^{(k)}$. For the quadratic (7.35) with $A$
symmetric positive definite and exact line searches, both the Fletcher–Reeves and the
Polak–Ribière method give the conjugate gradient iterates, with gradient $-r^{(k)}$ and
direction $d^{(k)}$.

The initial direction is the choice $\beta_1 = 0$ of the source. The coefficients are
`NonlinearCG.betaFletcherReeves` and `NonlinearCG.betaPolakRibiere`, the method is
`NonlinearCG.iterate`, and the exact step is `NonlinearCG.exactStep`. The last two parts are the
sense in which the methods extend the conjugate gradient method to nonquadratic $f$. The proof
uses `NonlinearCG.iterate_fletcherReeves_eq_CG_iterate` and
`NonlinearCG.iterate_polakRibiere_eq_CG_iterate`. -/
theorem remark_7_2 (gOld gNew : EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (x₀ : EuclideanSpace ℝ (Fin n))
    (hA : A.PosDef) :
    NonlinearCG.betaFletcherReeves gOld gNew = ‖gNew‖ ^ 2 / ‖gOld‖ ^ 2 ∧
      NonlinearCG.betaPolakRibiere gOld gNew = ⟪gNew, gNew - gOld⟫_ℝ / ‖gOld‖ ^ 2 ∧
      (NonlinearCG.init g x₀).d = -g x₀ ∧
      (∀ (β : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ)
        (α : NonlinearCG.State (EuclideanSpace ℝ (Fin n)) → ℝ) (k : ℕ),
        (NonlinearCG.iterate g β α x₀ (k + 1)).d
          = -g (NonlinearCG.iterate g β α x₀ (k + 1)).x
            + β (g (NonlinearCG.iterate g β α x₀ k).x) (g (NonlinearCG.iterate g β α x₀ (k + 1)).x)
              • (NonlinearCG.iterate g β α x₀ k).d) ∧
      (∀ k, NonlinearCG.iterate (gradient (energyFunctional (toEuclideanLin A) b))
          NonlinearCG.betaFletcherReeves (NonlinearCG.exactStep (toEuclideanLin A)) x₀ k
        = ⟨(CG.iterate (toEuclideanLin A) b x₀ k).x, -(CG.iterate (toEuclideanLin A) b x₀ k).r,
            (CG.iterate (toEuclideanLin A) b x₀ k).p⟩) ∧
      ∀ k, NonlinearCG.iterate (gradient (energyFunctional (toEuclideanLin A) b))
          NonlinearCG.betaPolakRibiere (NonlinearCG.exactStep (toEuclideanLin A)) x₀ k
        = ⟨(CG.iterate (toEuclideanLin A) b x₀ k).x, -(CG.iterate (toEuclideanLin A) b x₀ k).r,
            (CG.iterate (toEuclideanLin A) b x₀ k).p⟩ := by
  have hAsc := (Matrix.posDef_iff_isSymmetricCoercive A).1 hA
  have hg : gradient (energyFunctional (toEuclideanLin A) b) = fun x => toEuclideanLin A x - b :=
    funext fun x => (equation_7_35 (isHermitian_iff_isSymm.1 hA.1) x).2.1
  refine ⟨rfl, rfl, rfl, fun β α k => ?_, fun k => ?_, fun k => ?_⟩
  · rw [NonlinearCG.iterate_succ, NonlinearCG.step_d, NonlinearCG.step_g, NonlinearCG.step_x,
      NonlinearCG.iterate_g]
  · rw [hg]
    exact NonlinearCG.iterate_fletcherReeves_eq_CG_iterate hAsc b x₀ k
  · rw [hg]
    exact NonlinearCG.iterate_polakRibiere_eq_CG_iterate hAsc b x₀ k

end Quadratic

/-! ### Newton's method for minimization, (7.40)–(7.41) -/

section NewtonMin

variable {f : EuclideanSpace ℝ (Fin n) → ℝ}

/-- **Equation (7.40)** of [quarteroni2000numerical] and the remark after (7.41). Newton's method
for minimization is $x^{(k+1)} = x^{(k)} - H(x^{(k)})^{-1} \nabla f(x^{(k)})$, that is, Newton's
method (7.4) for $\nabla f$ with the Hessian matrix as Jacobian. Let
$f : \mathbb{R}^n \to \mathbb{R}$ with $\nabla f(x^*) = 0$, and let $R, C, L > 0$. Suppose that
$f$ is of class $C^2$ on a neighbourhood of every point of $B(x^*; R)$, that $H(x^*)$ is
invertible with $\|H(x^*)^{-1}\| \le C$, and that $\|H(x) - H(y)\| \le L \|x - y\|$ for
$x, y \in B(x^*; R)$, as operators on $\mathbb{R}^n$. Then:

* the Newton iterates satisfy the recurrence above for every $x^{(0)}$ and $k$;
* there is $r > 0$ such that for every $x^{(0)} \in B(x^*; r)$ every $H(x^{(k)})$ is invertible,
  $x^{(k)} \to x^*$, and $\|x^{(k+1)} - x^*\| \le C L \|x^{(k)} - x^*\|^2$ for all $k$.

The second part is the "result analogous to Theorem 7.1" of the source. The iterates are
`Newton.iterate (gradient f) (fun x => toEuclideanCLM (hessianMatrix f x)) x₀`, and the inverse
is `ContinuousLinearMap.inverse`. The proof is `QuarteroniSaccoSaleri.Chapter07.theorem_7_1` for
$F = \nabla f$, whose derivative is $H$ by
`QuarteroniSaccoSaleri.Chapter07.hasFDerivAt_gradient`. -/
theorem equation_7_40 {xstar : EuclideanSpace ℝ (Fin n)} (hcrit : gradient f xstar = 0)
    (e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (he : (e : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
      = toEuclideanCLM (𝕜 := ℝ) (hessianMatrix f xstar))
    {R C L : ℝ} (hR : 0 < R) (hC : 0 < C) (hL : 0 < L)
    (hCe : ‖(e.symm : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))‖ ≤ C)
    (hf : ∀ x ∈ ball xstar R, ContDiffAt ℝ 2 f x)
    (hLip : ∀ x ∈ ball xstar R, ∀ y ∈ ball xstar R,
      ‖toEuclideanCLM (𝕜 := ℝ) (hessianMatrix f x) - toEuclideanCLM (𝕜 := ℝ) (hessianMatrix f y)‖
        ≤ L * ‖x - y‖) :
    (∀ (x₀ : EuclideanSpace ℝ (Fin n)) (k : ℕ),
      Newton.iterate (gradient f) (fun x => toEuclideanCLM (𝕜 := ℝ) (hessianMatrix f x)) x₀ (k + 1)
        = Newton.iterate (gradient f) (fun x => toEuclideanCLM (𝕜 := ℝ) (hessianMatrix f x)) x₀ k
          - (toEuclideanCLM (𝕜 := ℝ) (hessianMatrix f
              (Newton.iterate (gradient f) (fun x => toEuclideanCLM (𝕜 := ℝ) (hessianMatrix f x))
                x₀ k))).inverse
            (gradient f (Newton.iterate (gradient f)
              (fun x => toEuclideanCLM (𝕜 := ℝ) (hessianMatrix f x)) x₀ k))) ∧
    ∃ r > 0, ∀ x₀ ∈ ball xstar r,
      (∀ k, ∃ e' : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n),
        (e' : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
          = toEuclideanCLM (𝕜 := ℝ) (hessianMatrix f (Newton.iterate (gradient f)
              (fun x => toEuclideanCLM (𝕜 := ℝ) (hessianMatrix f x)) x₀ k))) ∧
      Tendsto (Newton.iterate (gradient f)
        (fun x => toEuclideanCLM (𝕜 := ℝ) (hessianMatrix f x)) x₀) atTop (𝓝 xstar) ∧
      ∀ k, ‖Newton.iterate (gradient f) (fun x => toEuclideanCLM (𝕜 := ℝ) (hessianMatrix f x)) x₀
            (k + 1) - xstar‖
        ≤ C * L * ‖Newton.iterate (gradient f)
            (fun x => toEuclideanCLM (𝕜 := ℝ) (hessianMatrix f x)) x₀ k - xstar‖ ^ 2 :=
  ⟨fun x₀ k => by rw [Newton.iterate_succ]; rfl,
    theorem_7_1 hcrit e he hR hC hL hCe (fun x hx => hasFDerivAt_gradient (hf x hx)) hLip⟩

/-- **Equation (7.41)** of [quarteroni2000numerical], the remark after it. Let
$A \in \mathbb{R}^{n \times n}$ be symmetric positive definite. For the quadratic (7.35),
Newton's method (7.40) converges in one step: from every $x^{(0)}$, $x^{(1)} = A^{-1} b$.

This holds because $H = A$ and $\nabla f(x^{(0)}) = A x^{(0)} - b$, by
`QuarteroniSaccoSaleri.Chapter07.equation_7_35`. -/
theorem equation_7_41 {A : Matrix (Fin n) (Fin n) ℝ} {b : EuclideanSpace ℝ (Fin n)} (hA : A.PosDef)
    (x₀ : EuclideanSpace ℝ (Fin n)) :
    Newton.iterate (gradient (energyFunctional (toEuclideanLin A) b))
        (fun x => toEuclideanCLM (𝕜 := ℝ) (hessianMatrix (energyFunctional (toEuclideanLin A) b) x))
        x₀ 1
      = toEuclideanLin A⁻¹ b := by
  have hu : IsUnit A := hA.isUnit
  have hS : A.IsSymm := isHermitian_iff_isSymm.1 hA.1
  rw [Newton.iterate, Function.iterate_one, Newton.step, (equation_7_35 hS x₀).2.2,
    (equation_7_35 hS x₀).2.1, ← ContinuousLinearMap.ringInverse_eq_inverse,
    ← toEuclideanCLM_nonsing_inv hu]
  change x₀ - toEuclideanLin A⁻¹ (toEuclideanLin A x₀ - b) = toEuclideanLin A⁻¹ b
  rw [map_sub, toEuclideanLin_nonsing_inv_mul_apply hu]
  abel

end NewtonMin

/-! ### Global convergence: Properties 7.7 and 7.8 -/

section Global

variable {f : EuclideanSpace ℝ (Fin n) → ℝ}

-- The `C¹` hypothesis `hf` and `σ < β` are the book's; the backbone's Zoutendijk theorem
-- (`LineSearch.tendsto_atBot_or_tendsto_zero`) needs only the Lipschitz gradient, `0 < σ` and
-- `β < 1`.
set_option linter.unusedVariables false in
/-- **Property 7.7** of [quarteroni2000numerical] (convergence). Let
$f : \mathbb{R}^n \to \mathbb{R}$ be of class $C^1$ with $\|\nabla f(x) - \nabla f(y)\|_2 \le L
\|x - y\|_2$ for all $x, y$. Let $x^{(k+1)} = x^{(k)} + \alpha_k d^{(k)}$ with $\alpha_k > 0$ be
a gradient-like method: $d^{(k)T} \nabla f(x^{(k)}) < 0$ where $\nabla f(x^{(k)}) \neq 0$, and
$d^{(k)} = 0$ where $\nabla f(x^{(k)}) = 0$. Let every step satisfy (7.31) and (7.33) with
$0 < \sigma < \beta < 1$. Then one of the following holds:

* $\nabla f(x^{(k)}) = 0$ for some $k$;
* $f(x^{(k)}) \to -\infty$;
* $\nabla f(x^{(k)})^T d^{(k)} / \|d^{(k)}\|_2 \to 0$.

The first case is termination. Otherwise the method is a `Descent.IsDescentSequence` and
Zoutendijk's theorem `LineSearch.tendsto_atBot_or_tendsto_zero` applies. The source cites Wolfe
for the proof. The hypotheses $f \in C^1$ and $\sigma < \beta$ are those of the source; the
proof uses only the Lipschitz gradient, $0 < \sigma$ and $\beta < 1$. -/
theorem property_7_7 (hf : ContDiff ℝ 1 f) {L : ℝ}
    (hL : ∀ y z, ‖gradient f y - gradient f z‖ ≤ L * ‖y - z‖)
    {x d : ℕ → EuclideanSpace ℝ (Fin n)} {α : ℕ → ℝ} (hstep : ∀ k, x (k + 1) = x k + α k • d k)
    (hα : ∀ k, 0 < α k)
    (hd : ∀ k, (gradient f (x k) ≠ 0 → ⟪gradient f (x k), d k⟫_ℝ < 0) ∧
      (gradient f (x k) = 0 → d k = 0))
    {σ β : ℝ} (harmijo : ∀ k, LineSearch.Armijo f (fderiv ℝ f) σ (x k) (d k) (α k))
    (hwolfe : ∀ k, LineSearch.WolfeCurvature (fderiv ℝ f) β (x k) (d k) (α k))
    (hσ : 0 < σ) (hσβ : σ < β) (hβ : β < 1) :
    (∃ k, gradient f (x k) = 0) ∨ Tendsto (fun k => f (x k)) atTop atBot ∨
      Tendsto (fun k => ⟪gradient f (x k), d k⟫_ℝ / ‖d k‖) atTop (𝓝 0) := by
  by_cases hz : ∃ k, gradient f (x k) = 0
  · exact Or.inl hz
  simp only [not_exists] at hz
  right
  have hseq : Descent.IsDescentSequence (fderiv ℝ f) x d α :=
    ⟨hstep, hα, fun k => by
      rw [Descent.IsDescentDirection, fderiv_eq_innerSL_gradient, innerSL_apply_apply]
      exact (hd k).1 (hz k)⟩
  have hL' : ∀ y z, ‖fderiv ℝ f y - fderiv ℝ f z‖ ≤ L * ‖y - z‖ := fun y z => by
    rw [fderiv_eq_innerSL_gradient, fderiv_eq_innerSL_gradient, ← map_sub, innerSL_apply_norm]
    exact hL y z
  have h := LineSearch.tendsto_atBot_or_tendsto_zero hL' hseq harmijo hwolfe hσ hβ
  simpa only [fderiv_eq_innerSL_gradient, innerSL_apply_apply] using h

/-- **Property 7.8** of [quarteroni2000numerical]. Let $f : \mathbb{R}^n \to \mathbb{R}$ be of class
$C^1$, and let $x^{(k)}$ be a bounded sequence whose cluster points are all critical points of
$f$. Then $\nabla f(x^{(k)}) \to 0$.

**Reading.** The source assumes "a convergent sequence" generated by a gradient-like method such
that "any limit" is a critical point. Read literally, the property is the continuity of
$\nabla f$, which is `QuarteroniSaccoSaleri.Chapter07.property_7_8_of_tendsto`. The intended
statement is the one for bounded sequences and their cluster points, as here.

The proof specializes `Descent.tendsto_fderiv_zero_of_forall_clusterPt`. -/
theorem property_7_8 (hf : ContDiff ℝ 1 f) {x : ℕ → EuclideanSpace ℝ (Fin n)}
    (hb : Bornology.IsBounded (Set.range x))
    (hcl : ∀ y, MapClusterPt y atTop x → IsCriticalPoint f y) :
    Tendsto (fun k => gradient f (x k)) atTop (𝓝 0) := by
  have h := Descent.tendsto_fderiv_zero_of_forall_clusterPt (f' := fderiv ℝ f)
    (hf.continuous_fderiv one_ne_zero) hb fun y hy => by
      rw [fderiv_eq_innerSL_gradient, hcl y hy, map_zero]
  have hc := ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.continuous.tendsto
    0).comp h
  rw [map_zero] at hc
  exact hc

/-- **Property 7.8** of [quarteroni2000numerical], read literally. Let
$f : \mathbb{R}^n \to \mathbb{R}$ be of class $C^1$, and let $x^{(k)}$ converge to a critical
point $y$ of $f$. Then $\nabla f(x^{(k)}) \to 0$.

This is the continuity of $\nabla f$. The intended statement is
`QuarteroniSaccoSaleri.Chapter07.property_7_8`. -/
theorem property_7_8_of_tendsto (hf : ContDiff ℝ 1 f) {x : ℕ → EuclideanSpace ℝ (Fin n)}
    {y : EuclideanSpace ℝ (Fin n)} (hx : Tendsto x atTop (𝓝 y)) (hy : IsCriticalPoint f y) :
    Tendsto (fun k => gradient f (x k)) atTop (𝓝 0) := by
  have hcont : Continuous (gradient f) := by
    rw [gradient_eq_toDual_symm_fderiv]
    exact (InnerProductSpace.toDual ℝ _).symm.continuous.comp (hf.continuous_fderiv one_ne_zero)
  have := (hcont.tendsto y).comp hx
  rwa [hy] at this

end Global

/-! ### Secant-like methods, Section 7.2.7 -/

section Secant

/-- **Equation (7.42)** of [quarteroni2000numerical], the rank-one secant update. Let
$B \in \mathbb{R}^{n \times n}$ and $s, y, c \in \mathbb{R}^n$ with $c^T s \neq 0$. The update
$$B_+ = B + \frac{(y - B s) c^T}{c^T s}$$
satisfies the secant equation $B_+ s = y$, and the choice $c = s$ is Broyden's update (7.14).

In the notation of the source, $B = B_k$, $s = s^{(k)}$, $y = y^{(k)}$ and $B_+ = B_{k+1}$. The
update is `Matrix.rankOneSecantUpdate`. The proof uses `Matrix.rankOneSecantUpdate_mulVec` and
`Matrix.broydenUpdate_eq_rankOneSecantUpdate`. -/
theorem equation_7_42 (B : Matrix (Fin n) (Fin n) ℝ) {s c : Fin n → ℝ} (hcs : c ⬝ᵥ s ≠ 0)
    (y : Fin n → ℝ) :
    rankOneSecantUpdate B s y c *ᵥ s = y ∧ broydenUpdate B s y = rankOneSecantUpdate B s y s :=
  ⟨rankOneSecantUpdate_mulVec B hcs y, broydenUpdate_eq_rankOneSecantUpdate B s y⟩

/-- **Equation (7.43)** of [quarteroni2000numerical], the symmetric rank-one update. Let
$B \in \mathbb{R}^{n \times n}$ be symmetric and $s, y \in \mathbb{R}^n$ with
$(y - B s)^T s \neq 0$. The symmetric rank-one update `Matrix.sr1Update B s y` is the update
(7.42) with $c = y - B s$, it is symmetric, and it satisfies the secant equation $B_+ s = y$. -/
theorem equation_7_43 {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.IsSymm) {s y : Fin n → ℝ}
    (h : (y - B *ᵥ s) ⬝ᵥ s ≠ 0) :
    sr1Update B s y = rankOneSecantUpdate B s y (y - B *ᵥ s) ∧ (sr1Update B s y).IsSymm ∧
      sr1Update B s y *ᵥ s = y :=
  ⟨rfl, sr1Update_isSymm hB s y, sr1Update_mulVec B h⟩

/-- **Equation (7.44)** of [quarteroni2000numerical]. Let $B \in \mathbb{R}^{n \times n}$ be
symmetric and nonsingular, $C = B^{-1}$, and $s, y \in \mathbb{R}^n$ with $(y - B s)^T s \neq 0$
and $w^T y \neq 0$, where $w = s - C y$. Then the inverse of the symmetric rank-one update of
$B$ is
$$C_+ = C + \frac{w w^T}{w^T y}.$$

The proof uses the Sherman–Morrison formula (3.57), as `Matrix.sr1Update_inv`. -/
theorem equation_7_44 {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.IsSymm) (hu : IsUnit B)
    {s y : Fin n → ℝ} (hσ : (y - B *ᵥ s) ⬝ᵥ s ≠ 0) (hw : (s - B⁻¹ *ᵥ y) ⬝ᵥ y ≠ 0) :
    (sr1Update B s y)⁻¹
      = B⁻¹ + (1 / ((s - B⁻¹ *ᵥ y) ⬝ᵥ y)) • vecMulVec (s - B⁻¹ *ᵥ y) (s - B⁻¹ *ᵥ y) :=
  sr1Update_inv hB hu hσ hw

/-- **Equations (7.45)–(7.46)** of [quarteroni2000numerical]. Let $B \in \mathbb{R}^{n \times n}$ be
symmetric, and let $s, c, y \in \mathbb{R}^n$ with $s \neq 0$ and $c^T s \neq 0$. The
symmetrization iteration
$$B^{(2j+1)} = B^{(2j)} + \frac{(y - B^{(2j)} s) c^T}{c^T s}, \qquad B^{(2j+2)} =
  \frac{B^{(2j+1)} + B^{(2j+1)T}}{2},$$
from $B^{(0)} = B$ converges, as $j \to \infty$, to the matrix (7.46). With $c = s$ the limit is
the symmetric Powell–Broyden matrix $B_{\mathrm{SPB}}$, which is symmetric and satisfies the
secant equation $B_{\mathrm{SPB}} s = y$.

**Reading.** The source does not say that $B = B_k$ must be symmetric. The iteration converges
to (7.46) from a symmetric $B$.

The source says "it can be shown". One step of the iteration is `Matrix.symmetrizationStep`, the
matrix (7.46) is `Matrix.generalSymmetricUpdate B s y c`, and $B_{\mathrm{SPB}}$ is
`Matrix.psbUpdate B s y`. The proof specializes `Matrix.tendsto_symmetrizationStep_iterate`. -/
theorem equation_7_46 {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.IsSymm) {s c : Fin n → ℝ}
    (hcs : c ⬝ᵥ s ≠ 0) (hs : s ≠ 0) (y : Fin n → ℝ) :
    Tendsto (fun j => (symmetrizationStep s y c)^[j] B) atTop
        (𝓝 (generalSymmetricUpdate B s y c)) ∧
      psbUpdate B s y = generalSymmetricUpdate B s y s ∧ (psbUpdate B s y).IsSymm ∧
      psbUpdate B s y *ᵥ s = y :=
  ⟨tendsto_symmetrizationStep_iterate hcs hB, rfl, psbUpdate_isSymm hB s y,
    psbUpdate_mulVec B hs y⟩

open scoped Matrix.Norms.Frobenius

/-- **Section 7.2.7** of [quarteroni2000numerical], the characterization after (7.46). Let
$B \in \mathbb{R}^{n \times n}$ be symmetric, and let $s, y \in \mathbb{R}^n$ with $s \neq 0$.
Then $B_{\mathrm{SPB}}$ is the unique solution of the problem: find a symmetric $\bar{B}$ with
$\bar{B} s = y$ that minimizes $\|\bar{B} - B\|_F$. That is, $B_{\mathrm{SPB}}$ is symmetric
with $B_{\mathrm{SPB}} s = y$, $\|B_{\mathrm{SPB}} - B\|_F \le \|B' - B\|_F$ for every symmetric
$B'$ with $B' s = y$, and equality forces $B' = B_{\mathrm{SPB}}$.

The norm is the Frobenius norm. The proof uses `Matrix.frobenius_norm_psbUpdate_sub_le` and its
strict form `Matrix.frobenius_norm_psbUpdate_sub_lt`. -/
theorem psbLeastChange {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.IsSymm) {s : Fin n → ℝ} (hs : s ≠ 0)
    (y : Fin n → ℝ) :
    (psbUpdate B s y).IsSymm ∧ psbUpdate B s y *ᵥ s = y ∧
      (∀ B' : Matrix (Fin n) (Fin n) ℝ, B'.IsSymm → B' *ᵥ s = y →
        ‖psbUpdate B s y - B‖ ≤ ‖B' - B‖) ∧
      ∀ B' : Matrix (Fin n) (Fin n) ℝ, B'.IsSymm → B' *ᵥ s = y →
        ‖B' - B‖ ≤ ‖psbUpdate B s y - B‖ → B' = psbUpdate B s y :=
  ⟨psbUpdate_isSymm hB s y, psbUpdate_mulVec B hs y,
    fun B' hB' hB's => frobenius_norm_psbUpdate_sub_le hB hs hB' hB's, fun B' hB' hB's hle => by
      by_contra hne
      exact absurd hle (not_le.2 (frobenius_norm_psbUpdate_sub_lt hB hs hB' hB's hne))⟩

/-- **Section 7.2.7** of [quarteroni2000numerical], the last display (bounded deterioration). Let
$D \subseteq \mathbb{R}^n$ be convex, let $f : \mathbb{R}^n \to \mathbb{R}$ be of class $C^2$ on
a neighbourhood of every point of $D$, and let its Hessian satisfy
$\|H(w) - H(z)\|_F \le L \|w - z\|$ for $w, z \in D$. Let $x \in D$ and $s \neq 0$ with
$x + s \in D$, let $y = \nabla f(x + s) - \nabla f(x)$, and let $B$ be symmetric. Then the
symmetric Powell–Broyden update $B_{\mathrm{SPB}}$ of $B$ with $s$ and $y$ satisfies
$$\|B_{\mathrm{SPB}} - H(x + s)\|_F \le \|B - H(x)\|_F + 3 L \|s\|.$$

**Reading.** The source does not say that $B = B_k$ must be symmetric. The estimate needs it.

In the notation of the source, $x = x^{(k)}$, $s = s^{(k)}$ and $x + s = x^{(k+1)}$. The set $D$
need not be open. The proof specializes `Matrix.frobenius_norm_psbUpdate_sub_le_add` with $H$ =
`QuarteroniSaccoSaleri.Chapter07.hessianMatrix f`, whose relation to $\nabla f$ is
`QuarteroniSaccoSaleri.Chapter07.hasFDerivAt_gradient`. -/
theorem psbBoundedDeterioration {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {D : Set (EuclideanSpace ℝ (Fin n))} (hD : Convex ℝ D) (hf : ∀ w ∈ D, ContDiffAt ℝ 2 f w)
    {L : ℝ} (hL : ∀ w ∈ D, ∀ z ∈ D, ‖hessianMatrix f w - hessianMatrix f z‖ ≤ L * ‖w - z‖)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ D) {s : Fin n → ℝ} (hs : s ≠ 0)
    (hxs : x + toLp 2 s ∈ D) {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.IsSymm) :
    ‖psbUpdate B s (ofLp (gradient f (x + toLp 2 s) - gradient f x))
        - hessianMatrix f (x + toLp 2 s)‖
      ≤ ‖B - hessianMatrix f x‖ + 3 * L * ‖toLp 2 s‖ :=
  frobenius_norm_psbUpdate_sub_le_add hD (fun w hw => hasFDerivAt_gradient (hf w hw))
    (fun w hw => hessianMatrix_isSymm (hf w hw)) hL hx hs hxs hB

end Secant

end QuarteroniSaccoSaleri.Chapter07
