/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.ConnGouldToint.Chapter14.Section01
import NumlibSurface.ConnGouldToint.Chapter15.Section02
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Tactic.Abel

/-!
# Conn, Gould and Toint, Section 14.2: The quadratic penalty and augmented Lagrangian

This module formalizes the penalty functions and multiplier estimates of [conn2000trust], Section
14.2, for the problem of minimizing $f(x)$ subject to $c(x) = 0$, with $f : E \to \mathbb{R}$ and
$c : E \to F$. For a penalty parameter $\mu > 0$ and a multiplier estimate $y$, the quadratic
penalty function is $f(x) + \|c(x)\|^2 / (2\mu)$ and the augmented Lagrangian is $\Phi(x, y, \mu) =
f(x) - \langle y, c(x) \rangle + \|c(x)\|^2 / (2\mu)$. The first-order multiplier estimate is
$y^F(x) = y - c(x) / \mu$, and the least-squares multiplier estimate is
$y^{LS}(x) = (A A^*)^{-1} A \nabla f(x)$ with $A = c'(x)$.

Lemma 14.2.1 gives the derivative of the least-squares estimate. Lemma 14.2.2 considers points
$x_k \to x_*$ with $\|\nabla_x \Phi(x_k, y_k, \mu_k)\| \le \omega_k$. It bounds the errors of both
multiplier estimates and the constraint violation (part (i)), shows that both estimates converge to
$y_* = y^{LS}(x_*)$ and that a feasible limit is a KKT point (part (ii)), and gives sharper local
estimates at a nonsingular KKT point (parts (iii) and (iv)). The KKT system is the signed operator
`ConnGouldToint.Chapter15.sqpKKT` of Chapter 15.

## Main definitions

* Equation (14.2.1), `ConnGouldToint.Chapter14.quadraticPenalty`: the quadratic penalty function.
* Equation (14.2.2), `ConnGouldToint.Chapter14.augmentedLagrangian`: the augmented Lagrangian.
* Equation (14.2.3), `ConnGouldToint.Chapter14.IsEqualityKKT`: the first-order conditions of the
  equality-constrained problem.
* Equation (14.2.5), `ConnGouldToint.Chapter14.firstOrderMultiplier`: the first-order multiplier
  estimate.
* Equation (14.2.8), `ConnGouldToint.Chapter14.leastSquaresMultiplier`: the least-squares multiplier
  estimate.
* Equation (14.2.28), `ConnGouldToint.Chapter14.penaltyKKTJacobian`: the KKT operator of the
  equality-constrained problem.

## Main results

* Equation (14.2.4),
  `ConnGouldToint.Chapter14.fderiv_lagrangian_eq_zero_of_augmentedLagrangian_min`: at a local
  minimizer of the augmented Lagrangian, $f'(x) = \langle y^F(x), c'(x) \cdot \rangle$.
* Equation (14.2.6), `ConnGouldToint.Chapter14.constraint_eq_multiplier_difference`:
  $c(x) = \mu (y - y^F(x))$.
* Equation (14.2.7), `ConnGouldToint.Chapter14.fderiv_augmentedLagrangian_eq`: the derivative of the
  augmented Lagrangian is the derivative of the Lagrangian at $y^F(x)$.
* Equation (14.2.10), `ConnGouldToint.Chapter14.leastSquaresMultiplier_normal`: the normal equations
  of the least-squares estimate.
* Lemma 14.2.1, `ConnGouldToint.Chapter14.lemma_14_2_1`: the derivative (14.2.9) of the
  least-squares estimate.
* Lemma 14.2.2(i), `ConnGouldToint.Chapter14.lemma_14_2_2_i`: error bounds for the multiplier
  estimates and the constraint violation.
* Lemma 14.2.2(ii), `ConnGouldToint.Chapter14.lemma_14_2_2_ii`: convergence of both estimates, and
  the KKT conditions at a feasible limit.
* Equation (14.2.30), `ConnGouldToint.Chapter14.penaltyKKT_error_bound`: the local error bound at a
  nonsingular KKT point.
* Lemma 14.2.2(iii), `ConnGouldToint.Chapter14.lemma_14_2_2_iii`: the local estimates for small
  penalty parameters.
* Lemma 14.2.2(iv), `ConnGouldToint.Chapter14.lemma_14_2_2_iv`: a common bound for all errors
  proportional to the larger tolerance.

## Implementation notes

* The least-squares part works with a complete real inner product space $G$ for the variables and a
  complete space $F$ for the constraints. The adjoint $A^*$ of $A = c'(x)$ stands for $A^T$, and the
  inverse is `Ring.inverse`, which is $0$ at a noninvertible operator.
* The KKT operator acts on a primal increment and the increment of the multiplier itself. The source
  puts the negated multiplier increment in its input vector instead; the two forms are equivalent.

## Deviations from the source

* **Equation (14.2.3)** (typo). Both derivatives in the stationarity condition are evaluated at the
  feasible point $x$. See `ConnGouldToint.Chapter14.IsEqualityKKT`.
* **Equation (14.2.26)** (typo). Both multiplier differences on the right side have the sign of the
  identity (14.2.6). See `ConnGouldToint.Chapter14.lemma_14_2_2_i`.
-/

open scoped RealInnerProductSpace

namespace ConnGouldToint.Chapter14

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- **Equation (14.2.1)** of [conn2000trust]. The **quadratic penalty function** is
$$f(x) + \frac{1}{2\mu} \|c(x)\|^2.$$

At $\mu = 0$, Lean's inverse gives $(2\mu)^{-1} = 0$, and the function is $f$. -/
noncomputable def quadraticPenalty (f : E → ℝ) (c : E → F) (μ : ℝ) (x : E) : ℝ :=
  f x + (2 * μ)⁻¹ * ‖c x‖ ^ 2

/-- **Equation (14.2.2)** of [conn2000trust]. The **augmented Lagrangian** is
$$\Phi(x, y, \mu) = f(x) - \langle y, c(x) \rangle + \frac{1}{2\mu} \|c(x)\|^2.$$

At $\mu = 0$, Lean's inverse gives $(2\mu)^{-1} = 0$, and the function is the Lagrangian. -/
noncomputable def augmentedLagrangian (f : E → ℝ) (c : E → F) (y : F) (μ : ℝ) (x : E) : ℝ :=
  lagrangian f c y x + (2 * μ)⁻¹ * ‖c x‖ ^ 2

/-- **Equation (14.2.5)** of [conn2000trust]. The **first-order multiplier estimate** is
$$y^F(x) = y - \frac{c(x)}{\mu}.$$

At $\mu = 0$, Lean's inverse gives $y^F(x) = y$. -/
noncomputable def firstOrderMultiplier (c : E → F) (y : F) (μ : ℝ) (x : E) : F :=
  y - μ⁻¹ • c x

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- **Equation (14.2.6)** of [conn2000trust]. If $\mu \neq 0$, the constraint value is a scaled
multiplier difference:
$$c(x) = \mu \big(y - y^F(x)\big).$$
-/
theorem constraint_eq_multiplier_difference (c : E → F) (y : F) {μ : ℝ} (hμ : μ ≠ 0) (x : E) :
    c x = μ • (y - firstOrderMultiplier c y μ x) := by
  rw [firstOrderMultiplier, sub_sub_cancel, smul_smul, mul_inv_cancel₀ hμ, one_smul]

/-- **Equation (14.2.3)** of [conn2000trust]. The pair $(x, y)$ satisfies the **first-order
conditions** of the equality-constrained problem if
$$c(x) = 0 \quad\text{and}\quad f'(x) = \langle y, c'(x)\, \cdot \rangle.$$

**Typo.** In the printed stationarity condition the two derivatives are not both evaluated at
$x$. Here both are evaluated at the feasible point $x$. -/
def IsEqualityKKT (f : E → ℝ) (c : E → F) (x : E) (y : F) : Prop :=
  c x = 0 ∧ fderiv ℝ f x = (innerSL ℝ y).comp (fderiv ℝ c x)

private theorem hasFDerivAt_lagrangian {f : E → ℝ} {c : E → F} {x : E}
    (hf : DifferentiableAt ℝ f x) (hc : DifferentiableAt ℝ c x) (y : F) :
    HasFDerivAt (lagrangian f c y)
      (fderiv ℝ f x - (innerSL ℝ y).comp (fderiv ℝ c x)) x :=
  hf.hasFDerivAt.sub ((innerSL ℝ y).hasFDerivAt.comp x hc.hasFDerivAt)

/-- **Equation (14.2.7)** of [conn2000trust]. If $f$ and $c$ are differentiable at $x$, then
$$\nabla_x \Phi(x, y, \mu) = \nabla_x \ell\big(x, y^F(x)\big),$$
where the multiplier $y^F(x)$ is held fixed when the Lagrangian is differentiated. -/
theorem fderiv_augmentedLagrangian_eq {f : E → ℝ} {c : E → F} {x : E}
    (hf : DifferentiableAt ℝ f x) (hc : DifferentiableAt ℝ c x) (y : F) (μ : ℝ) :
    fderiv ℝ (augmentedLagrangian f c y μ) x =
      fderiv ℝ (lagrangian f c (firstOrderMultiplier c y μ x)) x := by
  have hpen := hc.hasFDerivAt.norm_sq.const_smul ((2 * μ)⁻¹)
  change fderiv ℝ (lagrangian f c y + (2 * μ)⁻¹ • (fun z ↦ ‖c z‖ ^ 2)) x = _
  rw [((hasFDerivAt_lagrangian hf hc y).add hpen).fderiv,
    (hasFDerivAt_lagrangian hf hc _).fderiv]
  ext d
  simp [firstOrderMultiplier, mul_inv_rev]
  ring

/-- **Equation (14.2.4)** of [conn2000trust]. Let $f$ and $c$ be differentiable at $x$. If $x$ is a
local minimizer of $\Phi(\cdot, y, \mu)$, then
$$f'(x) = \langle y^F(x), c'(x)\, \cdot \rangle.$$
-/
theorem fderiv_lagrangian_eq_zero_of_augmentedLagrangian_min
    {f : E → ℝ} {c : E → F} {x : E} (hf : DifferentiableAt ℝ f x)
    (hc : DifferentiableAt ℝ c x) {y : F} {μ : ℝ} (hmin : IsLocalMin
      (augmentedLagrangian f c y μ) x) :
    fderiv ℝ f x = (innerSL ℝ (firstOrderMultiplier c y μ x)).comp (fderiv ℝ c x) := by
  have hdiff : DifferentiableAt ℝ (augmentedLagrangian f c y μ) x :=
    ((hasFDerivAt_lagrangian hf hc y).add
      (hc.hasFDerivAt.norm_sq.const_smul ((2 * μ)⁻¹))).differentiableAt
  have hzero := hmin.hasFDerivAt_eq_zero hdiff.hasFDerivAt
  rw [fderiv_augmentedLagrangian_eq hf hc, (hasFDerivAt_lagrangian hf hc _).fderiv] at hzero
  exact sub_eq_zero.mp hzero

section LeastSquares

open Filter Topology
open scoped InnerProduct

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
variable [CompleteSpace G] [CompleteSpace F]

private noncomputable def adjointCLM : (G →L[ℝ] F) →L[ℝ] (F →L[ℝ] G) :=
  (ContinuousLinearMap.adjoint (𝕜 := ℝ)).toContinuousLinearEquiv.toContinuousLinearMap

/-- **Equations (14.2.8)–(14.2.10)** of [conn2000trust], the normal-equation operator. For a bounded
linear map $A : G \to F$, the **Gram operator** is $A A^* : F \to F$. -/
noncomputable def multiplierGram (A : G →L[ℝ] F) : F →L[ℝ] F := A.comp A.adjoint

/-- **Equation (14.2.8)** of [conn2000trust]. For $A : G \to F$ and $g \in G$, the **least-squares
multiplier estimate** is
$$y^{LS} = (A A^*)^{-1} A g.$$

The formula is meaningful where $A A^*$ is invertible. Elsewhere Lean's `Ring.inverse` gives
$y^{LS} = 0$. -/
noncomputable def leastSquaresMultiplier (A : G →L[ℝ] F) (g : G) : F :=
  Ring.inverse (multiplierGram A) (A g)

/-- Full row rank, as in assumption AO.1c of [conn2000trust], gives the nonsingularity condition of
Lemma 14.2.1. If $F$ is finite-dimensional and $A : G \to F$ is surjective, then $A A^*$ is
invertible. -/
theorem multiplierGram_isUnit_of_surjective [FiniteDimensional ℝ F] {A : G →L[ℝ] F}
    (hA : Function.Surjective A) : IsUnit (multiplierGram A) := by
  have hi : Function.Injective A.adjoint := by
    intro y z h
    apply ext_inner_right ℝ
    intro v
    obtain ⟨u, rfl⟩ := hA v
    rw [← A.adjoint_inner_left, ← A.adjoint_inner_left, h]
  have hG : Function.Injective (multiplierGram A) := A.self_comp_adjoint_injective_iff.mpr hi
  exact ContinuousLinearMap.isUnit_iff_bijective.mpr
    ⟨hG, (LinearMap.injective_iff_surjective (f := (multiplierGram A).toLinearMap)).mp hG⟩

/-- **Equation (14.2.10)** of [conn2000trust]. If $A A^*$ is invertible, the residual of the
least-squares estimate satisfies the normal equation
$$A \big(g - A^* y^{LS}\big) = 0.$$
-/
theorem leastSquaresMultiplier_normal {A : G →L[ℝ] F} (hA : IsUnit (multiplierGram A)) (g : G) :
    A (g - A.adjoint (leastSquaresMultiplier A g)) = 0 := by
  rw [map_sub, sub_eq_zero]
  have h := DFunLike.congr_fun (Ring.mul_inverse_cancel _ hA) (A g)
  exact h.symm

/-- **Equation (14.2.8)** of [conn2000trust], least-squares property. If $A A^*$ is invertible, then
$y^{LS}$ minimizes $y \mapsto \|g - A^* y\|$ over all $y \in F$. -/
theorem leastSquaresMultiplier_isMinOn {A : G →L[ℝ] F}
    (hA : IsUnit (multiplierGram A)) (g : G) :
    IsMinOn (fun y ↦ ‖g - A.adjoint y‖) Set.univ (leastSquaresMultiplier A g) := by
  intro y _
  let v := leastSquaresMultiplier A g
  let r := g - A.adjoint v
  have hr : A r = 0 := leastSquaresMultiplier_normal hA g
  have horth : ⟪r, A.adjoint (v - y)⟫ = 0 := by rw [A.adjoint_inner_right, hr, inner_zero_left]
  have he : g - A.adjoint y = r + A.adjoint (v - y) := by dsimp [r]; rw [map_sub]; abel
  change ‖r‖ ≤ ‖g - A.adjoint y‖
  rw [he]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_add_sq_real, horth, mul_zero, add_zero]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- **Equation (14.2.8)** of [conn2000trust], differentiability. Let $A : G \to (G \to F)$ and
$g : G \to G$ be $C^n$ at $x$, and let $A(x) A(x)^*$ be invertible. Then
$z \mapsto (A(z) A(z)^*)^{-1} A(z) g(z)$ is $C^n$ at $x$.

Under AW.1, this applies with $A = c'$ and $g = \nabla f$. -/
theorem leastSquaresMultiplier_contDiffAt {n} {A : G → G →L[ℝ] F} {g : G → G} {x : G}
    (hA : ContDiffAt ℝ n A x) (hg : ContDiffAt ℝ n g x)
    (hu : IsUnit (multiplierGram (A x))) :
    ContDiffAt ℝ n (fun z ↦ leastSquaresMultiplier (A z) (g z)) x := by
  have hAdj : ContDiffAt ℝ n (fun z ↦ (A z).adjoint) x :=
    (adjointCLM (G := G) (F := F)).contDiff.contDiffAt.comp x hA
  have hB : ContDiffAt ℝ n (fun z ↦ multiplierGram (A z)) x := hA.clm_comp hAdj
  have hInv : ContDiffAt ℝ n Ring.inverse (multiplierGram (A x)) := by
    rw [← hu.unit_spec]
    exact contDiffAt_ringInverse ℝ hu.unit
  exact (hInv.comp x hB).clm_apply (hA.clm_apply hg)

private theorem leastSquaresMultiplier_fderiv_apply {A : G → G →L[ℝ] F}
    {g : G → G} {x : G} {DA : G →L[ℝ] G →L[ℝ] F} {Dg : G →L[ℝ] G}
    (hA : HasFDerivAt A DA x) (hg : HasFDerivAt g Dg x)
    (hu : IsUnit (multiplierGram (A x))) (d : G) :
    let y := leastSquaresMultiplier (A x) (g x)
    fderiv ℝ (fun z ↦ leastSquaresMultiplier (A z) (g z)) x d =
      Ring.inverse (multiplierGram (A x))
        (A x (Dg d - (DA d).adjoint y) + DA d (g x - (A x).adjoint y)) := by
  let B := multiplierGram (A x)
  let C := Ring.inverse B
  let y := leastSquaresMultiplier (A x) (g x)
  have hAdj : HasFDerivAt (fun z ↦ (A z).adjoint) (adjointCLM.comp DA) x :=
    (adjointCLM (G := G) (F := F)).hasFDerivAt.comp x hA
  have hB := hA.clm_comp hAdj
  have hInv : HasFDerivAt Ring.inverse (-ContinuousLinearMap.mulLeftRight ℝ _ C C) B := by
    have h := hasFDerivAt_ringInverse (𝕜 := ℝ) hu.unit
    simpa only [← Ring.inverse_unit, hu.unit_spec] using h
  have hd := (hInv.comp x hB).clm_apply (hA.clm_apply hg)
  change fderiv ℝ (fun z ↦ leastSquaresMultiplier (A z) (g z)) x d =
    C (A x (Dg d - (DA d).adjoint y) + DA d (g x - (A x).adjoint y))
  rw [show fderiv ℝ (fun z ↦ leastSquaresMultiplier (A z) (g z)) x = _ from hd.fderiv]
  simp only [Function.comp_apply, add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, neg_apply,
    ContinuousLinearMap.mulLeftRight_apply, mul_apply_eq_comp,
    ContinuousLinearMap.compL_apply]
  change C (A x (Dg d) + DA d (g x)) + -
    C (A x ((DA d).adjoint y) + DA d ((A x).adjoint y)) = _
  simp only [map_add, map_sub]
  abel

/-- The gradient of the Lagrangian with the multiplier $y$ fixed is
$$\nabla_x \ell(x, y) = \nabla f(x) - c'(x)^* y,$$
when $f$ and $c$ are differentiable at $x$. -/
theorem gradient_lagrangian_eq {f : G → ℝ} {c : G → F} {x : G}
    (hf : DifferentiableAt ℝ f x) (hc : DifferentiableAt ℝ c x) (y : F) :
    gradient (lagrangian f c y) x = gradient f x - (fderiv ℝ c x).adjoint y := by
  apply ext_inner_right ℝ
  intro d
  rw [inner_gradient_left, (hasFDerivAt_lagrangian hf hc y).fderiv, inner_sub_left,
    inner_gradient_left, ContinuousLinearMap.adjoint_inner_left]
  rfl

/-- **Lemma 14.2.1** of [conn2000trust]. Let $f$ and $c$ be twice continuously differentiable, let
$A(z) = c'(z)$ and $g(z) = \nabla f(z)$, and let $A(x) A(x)^*$ be invertible. Then the
least-squares estimate $y^{LS}(z) = (A(z) A(z)^*)^{-1} A(z) g(z)$ is differentiable at $x$, and
for every direction $d$, as in (14.2.9),
$$(y^{LS})'(x)\, d = (A(x) A(x)^*)^{-1} \Big( A(x) \nabla_{xx} \ell\big(x, y^{LS}(x)\big) d +
  \big(A'(x) d\big) \big(g(x) - A(x)^* y^{LS}(x)\big) \Big).$$

The multiplier $y^{LS}(x)$ is held fixed in the Hessian of the Lagrangian. The second term, the
derivative of the constraint Jacobian applied to the least-squares residual, is the correction
term of (14.2.9). -/
theorem lemma_14_2_1 {f : G → ℝ} {c : G → F} {x : G}
    (hf : ContDiff ℝ 2 f) (hc : ContDiff ℝ 2 c)
    (hu : IsUnit (multiplierGram (fderiv ℝ c x))) :
    let A := fderiv ℝ c
    let g := gradient f
    let ls := fun z ↦ leastSquaresMultiplier (A z) (g z)
    DifferentiableAt ℝ ls x ∧ ∀ d,
      fderiv ℝ ls x d = Ring.inverse (multiplierGram (A x))
        (A x (fderiv ℝ (gradient (lagrangian f c (ls x))) x d) +
          fderiv ℝ A x d (g x - (A x).adjoint (ls x))) := by
  dsimp only
  let A := fderiv ℝ c
  let g := gradient f
  let y := leastSquaresMultiplier (A x) (g x)
  have hA : ContDiffAt ℝ 1 A x := hc.contDiffAt.fderiv_right (by norm_num)
  have hDf : ContDiffAt ℝ 1 (fderiv ℝ f) x := hf.contDiffAt.fderiv_right (by norm_num)
  have hg : ContDiffAt ℝ 1 g x :=
    (InnerProductSpace.toDual ℝ G).symm.toContinuousLinearEquiv.contDiff.contDiffAt.comp x hDf
  refine ⟨(leastSquaresMultiplier_contDiffAt hA hg hu).differentiableAt one_ne_zero, ?_⟩
  intro d
  have hAdj : HasFDerivAt (fun z ↦ (A z).adjoint)
      (adjointCLM.comp (fderiv ℝ A x)) x :=
    (adjointCLM (G := G) (F := F)).hasFDerivAt.comp x
      (hA.differentiableAt one_ne_zero).hasFDerivAt
  have hy := hAdj.clm_apply (hasFDerivAt_const y x)
  have hh := (hg.differentiableAt one_ne_zero).hasFDerivAt.sub hy
  have hh' := hh.congr_of_eventuallyEq (f₁ := gradient (lagrangian f c y)) (by
    exact Eventually.of_forall fun z ↦ gradient_lagrangian_eq
      (hf.differentiable (by norm_num) z) (hc.differentiable (by norm_num) z) y)
  change fderiv ℝ (fun z ↦ leastSquaresMultiplier (A z) (g z)) x d =
    Ring.inverse (multiplierGram (A x))
      (A x (fderiv ℝ (gradient (lagrangian f c y)) x d) +
        fderiv ℝ A x d (g x - (A x).adjoint y))
  rw [hh'.fderiv]
  simp only [sub_apply, add_apply,
    ContinuousLinearMap.comp_apply, zero_apply, map_zero, zero_add,
    ContinuousLinearMap.flip_apply]
  exact leastSquaresMultiplier_fderiv_apply
    (hA.differentiableAt one_ne_zero).hasFDerivAt (hg.differentiableAt one_ne_zero).hasFDerivAt hu d

/-- **Equation (14.2.21)** of [conn2000trust], the underlying identity. If $A A^*$ is invertible,
then for every $y$
$$y^{LS} - y = (A A^*)^{-1} A \big(g - A^* y\big).$$
-/
theorem leastSquaresMultiplier_sub_eq {A : G →L[ℝ] F} (hu : IsUnit (multiplierGram A))
    (g : G) (y : F) :
    leastSquaresMultiplier A g - y =
      Ring.inverse (multiplierGram A) (A (g - A.adjoint y)) := by
  have h := DFunLike.congr_fun (Ring.inverse_mul_cancel _ hu) y
  change Ring.inverse (multiplierGram A) (A (A.adjoint y)) = y at h
  rw [map_sub, map_sub, h]
  rfl

private theorem norm_stationarity_eq_augmentedGradient
    {f : G → ℝ} {c : G → F} {x : G} (hf : DifferentiableAt ℝ f x)
    (hc : DifferentiableAt ℝ c x) (y : F) (μ : ℝ) :
    ‖gradient f x - (fderiv ℝ c x).adjoint (firstOrderMultiplier c y μ x)‖ =
      ‖fderiv ℝ (augmentedLagrangian f c y μ) x‖ := by
  rw [← gradient_lagrangian_eq hf hc, fderiv_augmentedLagrangian_eq hf hc]
  exact LinearIsometryEquiv.norm_map _ _

private theorem contDiff_gradient' {f : G → ℝ} (hf : ContDiff ℝ 2 f) :
    ContDiff ℝ 1 (gradient f) :=
  (InnerProductSpace.toDual ℝ G).symm.toContinuousLinearEquiv.contDiff.comp
    (hf.fderiv_right (by norm_num))

/-- **Lemma 14.2.2(i)** of [conn2000trust]. Let $f$ and $c$ be twice continuously differentiable,
let $x_k \to x_*$, and let $c'(x_*) c'(x_*)^*$ be invertible. Let $\mu_k > 0$ and $\|\nabla_x
\Phi(x_k, y_k, \mu_k)\| \le \omega_k$ for all $k$, and let $y_* = y^{LS}(x_*)$. Then there are
$K_1, K_2 > 0$ such that, for all large $k$,
$$\|y^F_k - y_*\| \le K_1 \omega_k + K_2 \|x_k - x_*\|, \qquad \|y^{LS}(x_k) - y_*\| \le K_2
  \|x_k - x_*\|,$$
$$\|c(x_k)\| \le \mu_k \big(K_1 \omega_k + \|y_k - y_*\| + K_2 \|x_k - x_*\|\big),$$
where $y^F_k = y_k - c(x_k) / \mu_k$.

**Typo.** The two multiplier differences on the right side of the printed (14.2.26) have the
wrong sign. Here they are reversed to agree with the identity (14.2.6), from which the
feasibility bound follows.

The first two bounds also give (14.2.12)–(14.2.14): a uniform bound on the inverse controls the
error of the first-order estimate, and the least-squares estimate is locally Lipschitz. -/
theorem lemma_14_2_2_i {f : G → ℝ} {c : G → F} (hf : ContDiff ℝ 2 f)
    (hc : ContDiff ℝ 2 c) {xstar : G} (hu : IsUnit (multiplierGram (fderiv ℝ c xstar)))
    {x : ℕ → G} (hx : Tendsto x atTop (𝓝 xstar))
    {y : ℕ → F} {μ ω : ℕ → ℝ} (hμ : ∀ k, 0 < μ k)
    (hres : ∀ k, ‖fderiv ℝ (augmentedLagrangian f c (y k) (μ k)) (x k)‖ ≤ ω k) :
    let ls := fun z ↦ leastSquaresMultiplier (fderiv ℝ c z) (gradient f z)
    let ystar := ls xstar
    ∃ K₁ > 0, ∃ K₂ > 0, ∀ᶠ k in atTop,
      ‖firstOrderMultiplier c (y k) (μ k) (x k) - ystar‖ ≤
        K₁ * ω k + K₂ * ‖x k - xstar‖ ∧
      ‖ls (x k) - ystar‖ ≤ K₂ * ‖x k - xstar‖ ∧
      ‖c (x k)‖ ≤ μ k * (K₁ * ω k + ‖y k - ystar‖ + K₂ * ‖x k - xstar‖) := by
  dsimp only
  let A := fderiv ℝ c
  let g := gradient f
  let ls := fun z ↦ leastSquaresMultiplier (A z) (g z)
  let T := fun z ↦ (Ring.inverse (multiplierGram (A z))).comp (A z)
  have hA : ContDiff ℝ 1 A := hc.fderiv_right (by norm_num)
  have hAdj : ContDiff ℝ 1 (fun z ↦ (A z).adjoint) :=
    (adjointCLM (G := G) (F := F)).contDiff.comp hA
  have hB : ContDiffAt ℝ 1 (fun z ↦ multiplierGram (A z)) xstar :=
    hA.contDiffAt.clm_comp hAdj.contDiffAt
  have hInv : ContDiffAt ℝ 1 Ring.inverse (multiplierGram (A xstar)) := by
    rw [← hu.unit_spec]
    exact contDiffAt_ringInverse ℝ hu.unit
  have hInvA : ContDiffAt ℝ 1 (Ring.inverse ∘ fun z ↦ multiplierGram (A z)) xstar :=
    hInv.comp xstar hB
  have hT : ContinuousAt T xstar := (hInvA.clm_comp hA.contDiffAt).continuousAt
  have hnorm : ∀ᶠ k in atTop, ‖T (x k)‖ ≤ ‖T xstar‖ + 1 := by
    have hlim := hT.norm.tendsto.comp hx
    exact (hlim.eventually (gt_mem_nhds (show ‖T xstar‖ < ‖T xstar‖ + 1 by linarith))).mono
      fun _ h ↦ h.le
  have hunit : ∀ᶠ k in atTop, IsUnit (multiplierGram (A (x k))) :=
    (hB.continuousAt.tendsto.comp hx).eventually (Units.isOpen.mem_nhds hu)
  have hls : ContDiffAt ℝ 1 ls xstar :=
    leastSquaresMultiplier_contDiffAt hA.contDiffAt (contDiff_gradient' hf).contDiffAt hu
  obtain ⟨L, S, hS, hL⟩ := hls.exists_lipschitzOnWith
  have hxs : ∀ᶠ k in atTop, x k ∈ S := hx.eventually hS
  refine ⟨‖T xstar‖ + 1, by positivity, (L : ℝ) + 1, by positivity, ?_⟩
  filter_upwards [hnorm, hunit, hxs] with k hkT hkU hkS
  let yF := firstOrderMultiplier c (y k) (μ k) (x k)
  have hω : 0 ≤ ω k := (norm_nonneg _).trans (hres k)
  have hrs : ‖g (x k) - (A (x k)).adjoint yF‖ ≤ ω k := by
    rw [norm_stationarity_eq_augmentedGradient
      (hf.differentiable (by norm_num) (x k)) (hc.differentiable (by norm_num) (x k))]
    exact hres k
  have hdiff : ‖yF - ls (x k)‖ ≤ (‖T xstar‖ + 1) * ω k := by
    rw [norm_sub_rev, leastSquaresMultiplier_sub_eq hkU]
    change ‖T (x k) (g (x k) - (A (x k)).adjoint yF)‖ ≤ _
    exact ((T (x k)).le_opNorm _).trans (mul_le_mul hkT hrs (norm_nonneg _) (by positivity))
  have hLS : ‖ls (x k) - ls xstar‖ ≤ ((L : ℝ) + 1) * ‖x k - xstar‖ := by
    have h := hL.dist_le_mul (x k) hkS xstar (mem_of_mem_nhds hS)
    simp only [dist_eq_norm] at h
    exact h.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
  have hF : ‖yF - ls xstar‖ ≤
      (‖T xstar‖ + 1) * ω k + ((L : ℝ) + 1) * ‖x k - xstar‖ := by
    calc
      ‖yF - ls xstar‖ ≤ ‖yF - ls (x k)‖ + ‖ls (x k) - ls xstar‖ := by
        simpa only [sub_add_sub_cancel] using norm_add_le (yF - ls (x k)) (ls (x k) - ls xstar)
      _ ≤ _ := add_le_add hdiff hLS
  refine ⟨hF, hLS, ?_⟩
  rw [constraint_eq_multiplier_difference c (y k) (hμ k).ne' (x k), norm_smul,
    Real.norm_of_nonneg (hμ k).le]
  apply mul_le_mul_of_nonneg_left _ (hμ k).le
  calc
    ‖y k - yF‖ ≤ ‖y k - ls xstar‖ + ‖yF - ls xstar‖ := by
      rw [norm_sub_rev yF]
      simpa only [sub_add_sub_cancel] using norm_add_le (y k - ls xstar) (ls xstar - yF)
    _ ≤ _ := by linarith

/-- **Lemma 14.2.2(ii)** of [conn2000trust]. Under the hypotheses of Lemma 14.2.2(i), suppose also
that $\omega_k \to 0$. Then
$$y^F_k \to y_* \quad\text{and}\quad y^{LS}(x_k) \to y_*,$$
and if $c(x_*) = 0$, then $(x_*, y_*)$ satisfies the first-order conditions (14.2.3). -/
theorem lemma_14_2_2_ii {f : G → ℝ} {c : G → F} (hf : ContDiff ℝ 2 f)
    (hc : ContDiff ℝ 2 c) {xstar : G} (hu : IsUnit (multiplierGram (fderiv ℝ c xstar)))
    {x : ℕ → G} (hx : Tendsto x atTop (𝓝 xstar))
    {y : ℕ → F} {μ ω : ℕ → ℝ} (hμ : ∀ k, 0 < μ k)
    (hres : ∀ k, ‖fderiv ℝ (augmentedLagrangian f c (y k) (μ k)) (x k)‖ ≤ ω k)
    (hω : Tendsto ω atTop (𝓝 0)) :
    let ls := fun z ↦ leastSquaresMultiplier (fderiv ℝ c z) (gradient f z)
    let ystar := ls xstar
    Tendsto (fun k ↦ firstOrderMultiplier c (y k) (μ k) (x k)) atTop (𝓝 ystar) ∧
    Tendsto (ls ∘ x) atTop (𝓝 ystar) ∧
    (c xstar = 0 → IsEqualityKKT f c xstar ystar) := by
  dsimp only
  let A := fderiv ℝ c
  let g := gradient f
  let ls := fun z ↦ leastSquaresMultiplier (A z) (g z)
  let ystar := ls xstar
  let yF := fun k ↦ firstOrderMultiplier c (y k) (μ k) (x k)
  obtain ⟨K₁, _, K₂, _, hb⟩ := lemma_14_2_2_i hf hc hu hx hμ hres
  have hxnorm := tendsto_iff_norm_sub_tendsto_zero.mp hx
  have hL : Tendsto (fun k ↦ K₂ * ‖x k - xstar‖) atTop (𝓝 0) := by
    simpa only [mul_zero] using hxnorm.const_mul K₂
  have hF : Tendsto yF atTop (𝓝 ystar) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have hmajor : Tendsto (fun k ↦ K₁ * ω k + K₂ * ‖x k - xstar‖) atTop (𝓝 0) := by
      simpa only [mul_zero, zero_add] using (hω.const_mul K₁).add hL
    exact squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) (hb.mono fun _ h ↦ h.1) hmajor
  have hLS : Tendsto (ls ∘ x) atTop (𝓝 ystar) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    exact squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _)
      (hb.mono fun _ h ↦ h.2.1) hL
  refine ⟨hF, hLS, fun hfeas ↦ ⟨hfeas, ?_⟩⟩
  have hA : ContDiff ℝ 1 A := hc.fderiv_right (by norm_num)
  have hAT : Tendsto (fun k ↦ (A (x k)).adjoint) atTop (𝓝 (A xstar).adjoint) :=
    ((adjointCLM (G := G) (F := F)).continuous.continuousAt.tendsto.comp
      hA.continuous.continuousAt.tendsto).comp hx
  have hg : Tendsto (fun k ↦ g (x k)) atTop (𝓝 (g xstar)) :=
    (contDiff_gradient' hf).continuous.continuousAt.tendsto.comp hx
  have hzero : Tendsto (fun k ↦ g (x k) - (A (x k)).adjoint (yF k)) atTop (𝓝 0) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simp only [sub_zero]
    apply squeeze_zero (fun _ ↦ norm_nonneg _) _ hω
    intro k
    rw [norm_stationarity_eq_augmentedGradient
      (hf.differentiable (by norm_num) (x k)) (hc.differentiable (by norm_num) (x k))]
    exact hres k
  have hev : Continuous (fun p : (F →L[ℝ] G) × F ↦ p.1 p.2) :=
    continuous_fst.clm_apply continuous_snd
  have hAy : Tendsto (fun k ↦ (A (x k)).adjoint (yF k)) atTop (𝓝 ((A xstar).adjoint ystar)) :=
    (hev.tendsto ((A xstar).adjoint, ystar)).comp (hAT.prodMk_nhds hF)
  have hl := hg.sub hAy
  have hs : g xstar = (A xstar).adjoint ystar :=
    sub_eq_zero.mp (tendsto_nhds_unique hl hzero)
  ext d
  change fderiv ℝ f xstar d = ⟪ystar, A xstar d⟫
  rw [← inner_gradient_left, show gradient f xstar = (A xstar).adjoint ystar from hs,
    ContinuousLinearMap.adjoint_inner_left]

/-- **Equation (14.2.28)** of [conn2000trust]. The **KKT operator** at $z = (x, y)$ is
$$K(x, y) = \begin{bmatrix} \nabla_{xx} \ell(x, y) & -c'(x)^* \\ c'(x) & 0 \end{bmatrix},$$
acting on a primal increment and a multiplier increment.

The source puts the negated multiplier increment in its input vector; here the operator acts on
the multiplier increment itself. The operator is `ConnGouldToint.Chapter15.sqpKKT`. -/
noncomputable def penaltyKKTJacobian (f : G → ℝ) (c : G → F) (z : G × F) :
    G × F →L[ℝ] G × F :=
  Chapter15.sqpKKT (fun w ↦ fderiv ℝ (gradient (lagrangian f c w.2)) w.1)
    (fderiv ℝ c) (fun x ↦ (fderiv ℝ c x).adjoint) z

private theorem hasFDerivAt_penaltyKKTResidual {f : G → ℝ} {c : G → F}
    (hf : ContDiff ℝ 2 f) (hc : ContDiff ℝ 2 c) (z : G × F) :
    HasFDerivAt (Chapter15.sqpResidual (gradient f) c (fun x ↦ (fderiv ℝ c x).adjoint))
      (penaltyKKTJacobian f c z) z := by
  have hAT : ContDiff ℝ 1 (fun x ↦ (fderiv ℝ c x).adjoint) :=
    (adjointCLM (G := G) (F := F)).contDiff.comp (hc.fderiv_right (by norm_num))
  have hh := Chapter15.hasFDerivAt_sqpResidual (z := z)
    ((contDiff_gradient' hf).differentiable one_ne_zero z.1)
    (hc.differentiable (by norm_num) z.1) (hAT.differentiable one_ne_zero z.1)
  have hg (y : F) : gradient (lagrangian f c y) =
      fun x ↦ gradient f x - (fderiv ℝ c x).adjoint y := by
    funext x
    exact gradient_lagrangian_eq (hf.differentiable (by norm_num) x)
      (hc.differentiable (by norm_num) x) y
  simpa only [penaltyKKTJacobian, hg] using hh

/-- Assumption AO.3b for the constraint block of (14.2.28) in [conn2000trust]. If the KKT operator
$K(x, y)$ is invertible, then $c'(x)$ is surjective. -/
theorem surjective_of_penaltyKKTJacobian_isUnit {f : G → ℝ} {c : G → F}
    {z : G × F} (hK : IsUnit (penaltyKKTJacobian f c z)) :
    Function.Surjective (fderiv ℝ c z.1) := by
  intro b
  obtain ⟨w, hw⟩ := (ContinuousLinearMap.isUnit_iff_bijective.mp hK).2 (0, b)
  exact ⟨w.1, congrArg Prod.snd hw⟩

private theorem penaltyKKTResidual_eq_zero {f : G → ℝ} {c : G → F} {z : G × F}
    (hz : IsEqualityKKT f c z.1 z.2) :
    Chapter15.sqpResidual (gradient f) c (fun x ↦ (fderiv ℝ c x).adjoint) z = 0 := by
  refine Prod.ext (sub_eq_zero.mpr ?_) hz.1
  apply ext_inner_right ℝ
  intro d
  rw [inner_gradient_left, ContinuousLinearMap.adjoint_inner_left]
  exact DFunLike.congr_fun hz.2 d

/-- **Equation (14.2.30)** of [conn2000trust]. Let $f$ and $c$ be twice continuously differentiable,
let $(x_*, y_*)$ satisfy the first-order conditions (14.2.3), and let $K(x_*, y_*)$ be
invertible. If $x_k \to x_*$ and $v_k \to y_*$, then there is $D > 0$ such that, for all large
$k$,
$$\max\{\|x_k - x_*\|, \|v_k - y_*\|\} \le D \big(\|\nabla f(x_k) - c'(x_k)^* v_k\| +
  \|c(x_k)\|\big).$$

The bound follows from the derivative of the KKT residual at its nonsingular root. -/
theorem penaltyKKT_error_bound {f : G → ℝ} {c : G → F}
    (hf : ContDiff ℝ 2 f) (hc : ContDiff ℝ 2 c)
    {xstar : G} {ystar : F} (hstar : IsEqualityKKT f c xstar ystar)
    (hK : IsUnit (penaltyKKTJacobian f c (xstar, ystar)))
    {x : ℕ → G} {v : ℕ → F} (hx : Tendsto x atTop (𝓝 xstar)) (hv : Tendsto v atTop (𝓝 ystar)) :
    ∃ D > 0, ∀ᶠ k in atTop,
      max ‖x k - xstar‖ ‖v k - ystar‖ ≤
        D * (‖gradient f (x k) - (fderiv ℝ c (x k)).adjoint (v k)‖ + ‖c (x k)‖) := by
  let zstar := (xstar, ystar)
  let R := Chapter15.sqpResidual (gradient f) c (fun z ↦ (fderiv ℝ c z).adjoint)
  let J := penaltyKKTJacobian f c zstar
  have hR : HasFDerivAt R J zstar := hasFDerivAt_penaltyKKTResidual hf hc zstar
  have he : Topology.IsInducing J := by
    change Topology.IsInducing (penaltyKKTJacobian f c (xstar, ystar))
    rw [← hK.unit_spec]
    exact (ContinuousLinearEquiv.ofUnit hK.unit).toHomeomorph.isInducing
  obtain ⟨D, hD⟩ := Asymptotics.isBigO_iff.mp (hR.isTheta_sub he).symm.isBigO
  have hzstar : R zstar = 0 := penaltyKKTResidual_eq_zero hstar
  have hpair : Tendsto (fun k ↦ (x k, v k)) atTop (𝓝 zstar) := hx.prodMk_nhds hv
  refine ⟨max D 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  filter_upwards [hpair.eventually hD] with k hk
  rw [hzstar, sub_zero] at hk
  refine hk.trans ((mul_le_mul_of_nonneg_right (le_max_left D (1 : ℝ)) (norm_nonneg _)).trans ?_)
  apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans (le_max_right _ _))
  change max ‖gradient f (x k) - (fderiv ℝ c (x k)).adjoint (v k)‖ ‖c (x k)‖ ≤ _
  exact max_le (le_add_of_nonneg_right (norm_nonneg _)) (le_add_of_nonneg_left (norm_nonneg _))

private theorem penaltyKKT_firstOrder_bound {f : G → ℝ} {c : G → F}
    (hf : ContDiff ℝ 2 f) (hc : ContDiff ℝ 2 c) {xstar : G}
    (hfeas : c xstar = 0) {x : ℕ → G} (hx : Tendsto x atTop (𝓝 xstar))
    {y : ℕ → F} {μ ω : ℕ → ℝ} (hμ : ∀ k, 0 < μ k)
    (hres : ∀ k, ‖fderiv ℝ (augmentedLagrangian f c (y k) (μ k)) (x k)‖ ≤ ω k)
    (hω : Tendsto ω atTop (𝓝 0))
    (hK : IsUnit (penaltyKKTJacobian f c
      (xstar, leastSquaresMultiplier (fderiv ℝ c xstar) (gradient f xstar))))
    [FiniteDimensional ℝ F] :
    let ystar := leastSquaresMultiplier (fderiv ℝ c xstar) (gradient f xstar)
    ∃ D > 0, ∀ᶠ k in atTop,
      max ‖x k - xstar‖ ‖firstOrderMultiplier c (y k) (μ k) (x k) - ystar‖ ≤
        D * (ω k + ‖c (x k)‖) := by
  let ystar := leastSquaresMultiplier (fderiv ℝ c xstar) (gradient f xstar)
  let yF := fun k ↦ firstOrderMultiplier c (y k) (μ k) (x k)
  have hu := multiplierGram_isUnit_of_surjective (surjective_of_penaltyKKTJacobian_isUnit hK)
  obtain ⟨hy, _, hkkt⟩ := lemma_14_2_2_ii hf hc hu hx hμ hres hω
  obtain ⟨D, hD, hbound⟩ := penaltyKKT_error_bound hf hc (hkkt hfeas) hK hx hy
  refine ⟨D, hD, ?_⟩
  filter_upwards [hbound] with k hk
  refine hk.trans (mul_le_mul_of_nonneg_left (add_le_add ?_ le_rfl) hD.le)
  rw [norm_stationarity_eq_augmentedGradient
    (hf.differentiable (by norm_num) (x k)) (hc.differentiable (by norm_num) (x k))]
  exact hres k

/-- **Lemma 14.2.2(iii)** of [conn2000trust]. Let $F$ be finite-dimensional, let $f$ and $c$ be
twice continuously differentiable, let $c(x_*) = 0$, $x_k \to x_*$, $\mu_k > 0$, $\|\nabla_x
\Phi(x_k, y_k, \mu_k)\| \le \omega_k$ with $\omega_k \to 0$, and let $K(x_*, y_*)$ be
invertible, where $y_* = y^{LS}(x_*)$. Then there are $\mu_{\max} > 0$ and $K_3, \dots, K_7 > 0$
such that, for all large $k$ with $\mu_k \le \mu_{\max}$,
$$\|x_k - x_*\| \le K_3 \omega_k + K_4 \mu_k \|y_k - y_*\|,$$
$$\|y^F_k - y_*\| \le K_5 \omega_k + K_6 \mu_k \|y_k - y_*\|, \qquad \|y^{LS}(x_k) - y_*\| \le
  K_7 \omega_k + K_6 \mu_k \|y_k - y_*\|,$$
$$\|c(x_k)\| \le K_5 \mu_k \omega_k + (\mu_k + K_6 \mu_k^2) \|y_k - y_*\|.$$

These are the estimates (14.2.16)–(14.2.18), with the small-penalty cutoff $\mu_{\max}$ of
(14.2.32). -/
theorem lemma_14_2_2_iii [FiniteDimensional ℝ F] {f : G → ℝ} {c : G → F}
    (hf : ContDiff ℝ 2 f) (hc : ContDiff ℝ 2 c) {xstar : G}
    (hfeas : c xstar = 0) {x : ℕ → G} (hx : Tendsto x atTop (𝓝 xstar))
    {y : ℕ → F} {μ ω : ℕ → ℝ} (hμ : ∀ k, 0 < μ k)
    (hres : ∀ k, ‖fderiv ℝ (augmentedLagrangian f c (y k) (μ k)) (x k)‖ ≤ ω k)
    (hω : Tendsto ω atTop (𝓝 0))
    (hK : IsUnit (penaltyKKTJacobian f c
      (xstar, leastSquaresMultiplier (fderiv ℝ c xstar) (gradient f xstar)))) :
    let ls := fun z ↦ leastSquaresMultiplier (fderiv ℝ c z) (gradient f z)
    let ystar := ls xstar
    ∃ μmax > 0, ∃ K₃ > 0, ∃ K₄ > 0, ∃ K₅ > 0, ∃ K₆ > 0, ∃ K₇ > 0,
      ∀ᶠ k in atTop, μ k ≤ μmax →
        ‖x k - xstar‖ ≤ K₃ * ω k + K₄ * μ k * ‖y k - ystar‖ ∧
        ‖firstOrderMultiplier c (y k) (μ k) (x k) - ystar‖ ≤
          K₅ * ω k + K₆ * μ k * ‖y k - ystar‖ ∧
        ‖ls (x k) - ystar‖ ≤ K₇ * ω k + K₆ * μ k * ‖y k - ystar‖ ∧
        ‖c (x k)‖ ≤ K₅ * μ k * ω k + (μ k + K₆ * μ k ^ 2) * ‖y k - ystar‖ := by
  dsimp only
  let ls := fun z ↦ leastSquaresMultiplier (fderiv ℝ c z) (gradient f z)
  let ystar := ls xstar
  have hu := multiplierGram_isUnit_of_surjective (surjective_of_penaltyKKTJacobian_isUnit hK)
  obtain ⟨K₁, hK₁, K₂, hK₂, hls⟩ := lemma_14_2_2_i hf hc hu hx hμ hres
  obtain ⟨D, hD, hbound⟩ := penaltyKKT_firstOrder_bound hf hc hfeas hx hμ hres hω hK
  let μmax := min (1 / K₁) (1 / (2 * D * K₂))
  let K₃ := 4 * D
  let K₄ := 2 * D
  let K₇ := K₂ * K₃
  let K₆ := K₂ * K₄
  let K₅ := K₁ + K₇
  refine ⟨μmax, lt_min (one_div_pos.mpr hK₁) (one_div_pos.mpr (by positivity)),
    K₃, by positivity, K₄, by positivity, K₅, by positivity,
    K₆, by positivity, K₇, by positivity, ?_⟩
  filter_upwards [hls, hbound] with k hk hb
  intro hsmall
  let X := ‖x k - xstar‖
  let Y := ‖y k - ystar‖
  let yF := firstOrderMultiplier c (y k) (μ k) (x k)
  have hω₀ : 0 ≤ ω k := (norm_nonneg _).trans (hres k)
  have hμK₁ : μ k * K₁ ≤ 1 :=
    (le_div_iff₀ hK₁).mp (hsmall.trans (min_le_left _ _))
  have hμK₂ : μ k * (2 * D * K₂) ≤ 1 :=
    (le_div_iff₀ (by positivity : 0 < 2 * D * K₂)).mp (hsmall.trans (min_le_right _ _))
  have hX₀ : X ≤ D * (ω k + μ k * (K₁ * ω k + Y + K₂ * X)) :=
    (le_max_left _ _).trans (hb.trans
      (mul_le_mul_of_nonneg_left (add_le_add le_rfl hk.2.2) hD.le))
  have hX : X ≤ K₃ * ω k + K₄ * μ k * Y := by
    have h₁ := mul_le_mul_of_nonneg_right hμK₁ hω₀
    have h₂ := mul_le_mul_of_nonneg_right hμK₂ (norm_nonneg (x k - xstar))
    have h₃ := mul_le_mul_of_nonneg_left h₁ hD.le
    dsimp [K₃, K₄]
    nlinarith only [hX₀, h₂, h₃]
  have hLS : ‖ls (x k) - ystar‖ ≤ K₇ * ω k + K₆ * μ k * Y := by
    refine hk.2.1.trans ((mul_le_mul_of_nonneg_left hX hK₂.le).trans ?_)
    dsimp [K₇, K₆]
    ring_nf
    exact le_rfl
  have hYF : ‖yF - ystar‖ ≤ K₅ * ω k + K₆ * μ k * Y := by
    refine hk.1.trans ?_
    have hh := mul_le_mul_of_nonneg_left hX hK₂.le
    dsimp [K₅, K₇, K₆]
    linarith only [hh, mul_add K₂ (K₃ * ω k) (K₄ * μ k * Y),
      mul_assoc K₂ K₃ (ω k), mul_assoc K₂ (K₄ * μ k) Y, mul_assoc K₂ K₄ (μ k)]
  refine ⟨hX, hYF, hLS, ?_⟩
  rw [constraint_eq_multiplier_difference c (y k) (hμ k).ne' (x k),
    norm_smul, Real.norm_of_nonneg (hμ k).le]
  have htriangle : ‖y k - yF‖ ≤ Y + ‖yF - ystar‖ := by
    rw [norm_sub_rev yF]
    simpa only [sub_add_sub_cancel] using norm_add_le (y k - ystar) (ystar - yF)
  refine (mul_le_mul_of_nonneg_left (htriangle.trans (add_le_add le_rfl hYF)) (hμ k).le).trans ?_
  change μ k * (Y + (K₅ * ω k + K₆ * μ k * Y)) ≤
    K₅ * μ k * ω k + (μ k + K₆ * μ k ^ 2) * Y
  ring_nf
  exact le_rfl

/-- **Lemma 14.2.2(iv)** of [conn2000trust], quantitative form. Under the hypotheses of Lemma
14.2.2(iii), let also $\|c(x_k)\| \le \eta_k$ for all $k$. Then there is $C > 0$ such that, for
all large $k$,
$$\max\{\|x_k - x_*\|, \|y^F_k - y_*\|, \|y^{LS}(x_k) - y_*\|\} \le C \max\{\omega_k,
  \eta_k\}.$$

In particular, if the tolerances $\omega_k$ and $\eta_k$ converge to zero with a common Q-order,
the three errors converge with the same R-order. -/
theorem lemma_14_2_2_iv [FiniteDimensional ℝ F] {f : G → ℝ} {c : G → F}
    (hf : ContDiff ℝ 2 f) (hc : ContDiff ℝ 2 c) {xstar : G}
    (hfeas : c xstar = 0) {x : ℕ → G} (hx : Tendsto x atTop (𝓝 xstar))
    {y : ℕ → F} {μ ω η : ℕ → ℝ} (hμ : ∀ k, 0 < μ k)
    (hres : ∀ k, ‖fderiv ℝ (augmentedLagrangian f c (y k) (μ k)) (x k)‖ ≤ ω k)
    (hω : Tendsto ω atTop (𝓝 0))
    (hK : IsUnit (penaltyKKTJacobian f c
      (xstar, leastSquaresMultiplier (fderiv ℝ c xstar) (gradient f xstar))))
    (hη : ∀ k, ‖c (x k)‖ ≤ η k) :
    let ls := fun z ↦ leastSquaresMultiplier (fderiv ℝ c z) (gradient f z)
    let ystar := ls xstar
    ∃ C > 0, ∀ᶠ k in atTop,
      max (max ‖x k - xstar‖ ‖firstOrderMultiplier c (y k) (μ k) (x k) - ystar‖)
        ‖ls (x k) - ystar‖ ≤ C * max (ω k) (η k) := by
  dsimp only
  have hu := multiplierGram_isUnit_of_surjective (surjective_of_penaltyKKTJacobian_isUnit hK)
  obtain ⟨K₁, hK₁, K₂, hK₂, hls⟩ := lemma_14_2_2_i hf hc hu hx hμ hres
  obtain ⟨D, hD, hbound⟩ := penaltyKKT_firstOrder_bound hf hc hfeas hx hμ hres hω hK
  let C := 2 * D * max 1 K₂
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  filter_upwards [hls, hbound] with k hk hb
  have hω₀ : 0 ≤ ω k := (norm_nonneg _).trans (hres k)
  have hm : 0 ≤ max (ω k) (η k) := hω₀.trans (le_max_left _ _)
  have hT : ω k + ‖c (x k)‖ ≤ 2 * max (ω k) (η k) := by
    linarith [le_max_left (ω k) (η k), (hη k).trans (le_max_right (ω k) (η k))]
  have hp := hb.trans (mul_le_mul_of_nonneg_left hT hD.le)
  apply max_le
  · refine hp.trans ?_
    dsimp [C]
    have hh := mul_le_mul_of_nonneg_left (le_max_left (1 : ℝ) K₂)
      (mul_nonneg (by positivity : 0 ≤ 2 * D) hm)
    nlinarith only [hh]
  · refine hk.2.1.trans ((mul_le_mul_of_nonneg_left ((le_max_left _ _).trans hp) hK₂.le).trans ?_)
    dsimp [C]
    have hh := mul_le_mul_of_nonneg_left (le_max_right (1 : ℝ) K₂)
      (mul_nonneg (by positivity : 0 ≤ 2 * D) hm)
    nlinarith only [hh]

end LeastSquares

end ConnGouldToint.Chapter14
