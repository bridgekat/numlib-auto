/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Convex.Extrema
import Mathlib.Analysis.Convex.Strong
import Numlib.Optimization.Constrained
import Numlib.Variational.Minimization
import NumlibSurface.QuarteroniSaccoSaleri.Chapter07.Section02

/-!
# Quarteroni, Sacco and Saleri, Section 7.3: Constrained optimization

This module formalizes Section 7.3 of [quarteroni2000numerical], the minimization of a function
$f : \mathbb{R}^n \to \mathbb{R}$ subject to constraints. On a convex set $\Omega$, a local
minimizer $x^*$ satisfies the variational inequality $\nabla f(x^*)^T (x - x^*) \ge 0$ for all
$x \in \Omega$ (7.48), and this condition is sufficient when $f$ is convex. A strongly convex
function (7.49) has exactly one minimizer on a closed convex set. For equality constraints
$h(x) = 0$, a regular local minimizer is a stationary point of the Lagrangian $\mathcal{L}(x,
\lambda) = f(x) + \lambda^T h(x)$, and for added inequality constraints $g(x) \le 0$ the
Karush–Kuhn–Tucker conditions hold. Section 7.3.1 treats the nonlinear programming problem (7.52)
and the Kuhn–Tucker conditions of Properties 7.13–7.15. The module ends with the penalty method
(7.53), the augmented Lagrangian $\mathcal{G}_\alpha(x, \lambda) = f(x) + \lambda^T h(x) +
\frac{1}{2} \alpha \|h(x)\|_2^2$ of (7.55), Example 7.7, and one clause of Property 7.17.

The proofs specialize the backbone modules `Numlib.Optimization.Constrained` (Lagrange multipliers,
the Karush–Kuhn–Tucker theorem, the penalty and augmented Lagrangian methods),
`Numlib.Optimization.Descent`, `Numlib.Analysis.Convex.Gateaux` and
`Numlib.Variational.Minimization`, together with Mathlib's
`IsLocalExtrOn.exists_multipliers_of_hasStrictFDerivAt` and `StrongConvexOn`.

## Main definitions

* (7.49), `QuarteroniSaccoSaleri.Chapter07.IsStronglyConvexOn`: $f$ is strongly convex on $\Omega$
  with constant $\rho > 0$.
* Definition 7.2, `QuarteroniSaccoSaleri.Chapter07.definition_7_2`: a feasible point is regular if
  the gradients $\nabla h_i(x)$ are linearly independent.
* Section 7.3, `QuarteroniSaccoSaleri.Chapter07.lagrangian`: the Lagrangian $\mathcal{L}(x,
  \lambda) = f(x) + \lambda^T h(x)$.
* Definition 7.3, `QuarteroniSaccoSaleri.Chapter07.definition_7_3`: a feasible point is regular if
  the gradients of the equality constraints and of the active inequality constraints are linearly
  independent.
* (7.52), `QuarteroniSaccoSaleri.Chapter07.feasibleRegion`: the feasible region of the nonlinear
  programming problem.
* Section 7.3.1, `QuarteroniSaccoSaleri.Chapter07.nonlinearLagrangian`: the Lagrangian of (7.52).
* Section 7.3.1, `QuarteroniSaccoSaleri.Chapter07.IsRegularNLP`: the constraint qualification for
  (7.52).

## Main results

* Property 7.9, `QuarteroniSaccoSaleri.Chapter07.property_7_9_necessary`: a local minimizer on a
  convex set satisfies (7.48).
* Property 7.9, `QuarteroniSaccoSaleri.Chapter07.property_7_9_sufficient`: for a convex $f$, (7.48)
  implies that $x^*$ is a global minimizer on $\Omega$.
* (7.49), `QuarteroniSaccoSaleri.Chapter07.isStronglyConvexOn_iff`: on a convex set, (7.49) with
  constant $\rho$ is Mathlib's strong convexity with modulus $2\rho$.
* Property 7.10, `QuarteroniSaccoSaleri.Chapter07.property_7_10`: a lower semicontinuous strongly
  convex function on a nonempty closed convex set has exactly one minimizer, and every local
  minimizer is global.
* Definition 7.2, `QuarteroniSaccoSaleri.Chapter07.definition_7_2_iff`: Definition 7.2 is
  `Constrained.IsRegularPoint`.
* Section 7.3, `QuarteroniSaccoSaleri.Chapter07.lagrangian_eq`: $\mathcal{L}(x, \lambda) = f(x) +
  \sum_i \lambda_i h_i(x)$.
* Section 7.3, `QuarteroniSaccoSaleri.Chapter07.gradient_lagrangian`: the partial Jacobian
  $J_\mathcal{L}(x, \lambda) = \nabla f(x) + \sum_i \lambda_i \nabla h_i(x)$.
* Property 7.11, `QuarteroniSaccoSaleri.Chapter07.property_7_11`: a regular local minimizer with
  equality constraints has a unique Lagrange multiplier.
* Property 7.11, `QuarteroniSaccoSaleri.Chapter07.property_7_11_sufficient`: stationarity and a
  positive Hessian of the Lagrangian on the tangent space give a strict local minimizer.
* Definition 7.3, `QuarteroniSaccoSaleri.Chapter07.definition_7_3_iff`: Definition 7.3 is
  `Constrained.IsRegularPointIneq`.
* Property 7.12, `QuarteroniSaccoSaleri.Chapter07.property_7_12`: a regular local minimizer has
  unique Karush–Kuhn–Tucker multipliers.
* (7.52), `QuarteroniSaccoSaleri.Chapter07.mem_feasibleRegion`: membership in the feasible region.
* Section 7.3.1, `QuarteroniSaccoSaleri.Chapter07.nonlinearLagrangian_eq`: the Lagrangian of (7.52)
  in coordinates.
* Section 7.3.1, `QuarteroniSaccoSaleri.Chapter07.gradient_nonlinearLagrangian`: the partial
  Jacobian of the Lagrangian of (7.52).
* (7.52), `QuarteroniSaccoSaleri.Chapter07.nonlinearProgram_toStandard`: for $l \le k$, the feasible
  region of (7.52) is the feasible set of a problem in the standard form of Property 7.12.
* Property 7.13, `QuarteroniSaccoSaleri.Chapter07.exists_kuhnTucker`: a regular constrained local
  maximizer of (7.52) has a multiplier with $\nabla_x \mathcal{L} = 0$, sign conditions and
  complementarity.
* Property 7.13, `QuarteroniSaccoSaleri.Chapter07.property_7_13`: the Kuhn–Tucker conditions I and
  II.
* Property 7.14, `QuarteroniSaccoSaleri.Chapter07.property_7_14`: the Kuhn–Tucker conditions III and
  IV.
* Property 7.15, `QuarteroniSaccoSaleri.Chapter07.property_7_15`: under concavity and convexity
  assumptions, the Kuhn–Tucker conditions are sufficient for a global maximizer.
* (7.53), `QuarteroniSaccoSaleri.Chapter07.equation_7_53`: the penalized Lagrangian
  $\mathcal{L}_\alpha(x) = f(x) + \frac{1}{2} \alpha \|h(x)\|_2^2$ equals $f$ on the constraint set.
* Property 7.16, `QuarteroniSaccoSaleri.Chapter07.property_7_16`: every cluster point of the penalty
  minimizers is a constrained global minimizer, and the minimizers converge if the constrained
  minimizer is unique and the sequence is bounded.
* (7.55), `QuarteroniSaccoSaleri.Chapter07.equation_7_55`: the augmented Lagrangian, its value at
  $\lambda = 0$, and its minimizers on the constraint set.
* Property 7.16, `QuarteroniSaccoSaleri.Chapter07.property_7_16_augmented`: the cluster point
  statement for the method of multipliers with bounded multipliers.
* Example 7.7, `QuarteroniSaccoSaleri.Chapter07.example_7_7`: for $f(x) = -x^4$ and $h(x) = x$, the
  augmented Lagrangian has no global minimizer.
* Example 7.7, `QuarteroniSaccoSaleri.Chapter07.example_7_7_isLocalMin`: for $\lambda = 0$ and
  $\alpha > 0$, the point $0$ is a strict local minimizer of the augmented Lagrangian.
* Property 7.17, `QuarteroniSaccoSaleri.Chapter07.property_7_17_debreu`: condition 2 of Property
  7.17 implies condition 3 for all large $\alpha$.

## Conventions

* The space $\mathbb{R}^n$ is `EuclideanSpace ℝ (Fin n)`. The constraints are families
  `h : Fin m → EuclideanSpace ℝ (Fin n) → ℝ` and `g : Fin r → EuclideanSpace ℝ (Fin n) → ℝ`. The
  book's Jacobian $J_h(x)$, whose columns are the gradients $\nabla h_i(x)$, is the family
  `fun i => gradient (h i) x`.
* The backbone takes the derivatives of the constraints as separate data $h_i'(x)$. Here $h_i'(x)$
  is `fderiv ℝ (h i) x`, which is `innerSL ℝ (gradient (h i) x)` by `fderiv_eq_innerSL_gradient`.
* A local minimizer of $f$ on a set $S$ is `IsLocalMinOn f S`, and a global one is `IsMinOn f S`.
* In the penalty method and the augmented Lagrangian, the constraint is one map
  $h : \mathbb{R}^n \to \mathbb{R}^m$, and the multiplier $\lambda$ is a vector of
  `EuclideanSpace ℝ (Fin m)`.

## Deviations from the source

* **Property 7.9(1)** (generalization). The book assumes $f$ of class $C^1$ on a ball around $x^*$;
  differentiability at $x^*$ suffices. See `QuarteroniSaccoSaleri.Chapter07.property_7_9_necessary`.
* **Property 7.10** (correction). The statement needs $f$ lower semicontinuous on $\Omega$. See
  `QuarteroniSaccoSaleri.Chapter07.property_7_10`.
* **Property 7.11, first part** (correction). The statement needs $x^*$ regular in the sense of
  Definition 7.2: $\min x$ subject to $x^2 = 0$ has no multiplier. See
  `QuarteroniSaccoSaleri.Chapter07.property_7_11`.
* **Equation (7.52)** (reading). The index ranges presuppose $l \le k$, which the book does not
  write; every statement about (7.52) assumes it. See
  `QuarteroniSaccoSaleri.Chapter07.nonlinearProgram_toStandard`.
* **Property 7.13** (correction). The book mentions a constraint qualification after Property 7.14
  and does not state it; the formal statement assumes
  `QuarteroniSaccoSaleri.Chapter07.IsRegularNLP`. See
  `QuarteroniSaccoSaleri.Chapter07.property_7_13`.
* **Property 7.14** (typo). The book prints the fourth condition as
  $(\nabla_\lambda \mathcal{L})^T x^* = 0$, whose two vectors have different lengths; the formal
  statement is $(\nabla_\lambda \mathcal{L})^T \lambda^* = 0$. See
  `QuarteroniSaccoSaleri.Chapter07.property_7_14`.
* **Property 7.15** (correction). The statement needs the sign conditions on the multipliers, which
  the book leaves out of its list of Kuhn–Tucker conditions. See
  `QuarteroniSaccoSaleri.Chapter07.property_7_15`.
* **Property 7.15** (reading). The book's convexity assumptions "in the feasible region" are read on
  a convex set $C$ that contains the feasible region and lies in the nonnegative orthant. See
  `QuarteroniSaccoSaleri.Chapter07.property_7_15`.
* **Property 7.16** (correction). The book asserts that the penalty minimizers converge to $x^*$;
  every cluster point is a constrained global minimizer, and convergence needs a unique constrained
  minimizer and a bounded sequence. See `QuarteroniSaccoSaleri.Chapter07.property_7_16`.
* **Example 7.7** (reading). The book says that the augmented Lagrangian "no longer admits a minimum
  at $x = 0$"; it has no global minimizer, while for $\lambda = 0$ and $\alpha > 0$ the point $0$ is
  a strict local minimizer. See `QuarteroniSaccoSaleri.Chapter07.example_7_7` and
  `QuarteroniSaccoSaleri.Chapter07.example_7_7_isLocalMin`.
* **Property 7.17** (generalization). The book lists condition 3 as a hypothesis; it follows from
  condition 2 for all large $\alpha$. See `QuarteroniSaccoSaleri.Chapter07.property_7_17_debreu`.

## Not formalized

* **Property 7.17, the uniform clause.** Let $x^*$ be a regular strict local minimizer of (7.50),
  with $f$ and the $h_i$ of class $C^2$ near $x^*$, and let $\lambda^*$ be its multiplier. Assume
  condition 2, $z^T H_{\mathcal{G}_0}(x^*, \lambda^*) z > 0$ for every $z \neq 0$ with
  $J_h(x^*)^T z = 0$, and condition 3, $H_{\mathcal{G}_{\bar\alpha}}(x^*, \lambda^*)$ positive
  definite for some $\bar\alpha > 0$. The property asserts that there are $\delta, \gamma, M > 0$
  such that for every pair $(\lambda, \alpha)$ with $\|\lambda - \lambda^*\| < \delta \alpha$ and
  $\alpha \ge \bar\alpha$, the problem $\min \mathcal{G}_\alpha(x, \lambda)$ over the ball
  $B(x^*; \gamma)$ has a unique solution $x(\lambda, \alpha)$, that $x(\lambda, \alpha)$ is
  differentiable in $(\lambda, \alpha)$, and that $\|x(\lambda, \alpha) - x^*\| \le M \|\lambda -
  \lambda^*\|$. The book states it without proof; it is Proposition 2.4 of Bertsekas, *Constrained
  Optimization and Lagrange Multiplier Methods*, and the convergence discussion after it cites
  Proposition 2.7 there. A proof needs an implicit function theorem with parameters and derivatives,
  in the parameters $(\lambda - \lambda^*)/\alpha$ and $1/\alpha$ so that the constants are uniform
  in $\alpha$, and Mathlib's `HasStrictFDerivAt.implicitFunction` does not give this form. The
  uniqueness on the whole ball is not a convexity statement: for the constraint $h(x, y) = y - x^2$
  the Hessian of $\frac{1}{2} \|h\|^2$ at $(0, y)$ is $\operatorname{diag}(-2y, 1)$, which is
  indefinite for every $y > 0$, so the penalty does not make $\mathcal{G}_\alpha(\cdot, \lambda)$
  convex on a fixed ball.
-/

open Filter Matrix Metric Set Topology WithLp
open scoped InnerProductSpace

namespace QuarteroniSaccoSaleri.Chapter07

variable {n : ℕ}

/-! ### Property 7.9: optimality on a convex set -/

section Convex

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
  {xstar : EuclideanSpace ℝ (Fin n)}

/-- **Property 7.9(1)** of [quarteroni2000numerical], necessary condition. Let
$\Omega \subseteq \mathbb{R}^n$ be convex, let $x^* \in \Omega$, and let
$f : \mathbb{R}^n \to \mathbb{R}$ be differentiable at $x^*$. If $x^*$ is a local minimizer of
$f$ on $\Omega$, then (7.48) holds:
$$\nabla f(x^*)^T (x - x^*) \ge 0 \quad \text{for all } x \in \Omega.$$

**Generalization.** The book assumes $f$ of class $C^1$ on a ball around $x^*$.
Differentiability at $x^*$ suffices.

The proof specializes `Descent.fderiv_apply_sub_nonneg_of_isLocalMinOn`. -/
theorem property_7_9_necessary (hΩ : Convex ℝ Ω) (hx : xstar ∈ Ω) (hf : DifferentiableAt ℝ f xstar)
    (hmin : IsLocalMinOn f Ω xstar) : ∀ x ∈ Ω, 0 ≤ ⟪gradient f xstar, x - xstar⟫_ℝ :=
    fun x hxΩ => by
  rw [inner_gradient_left]
  exact Descent.fderiv_apply_sub_nonneg_of_isLocalMinOn hΩ hx hmin hf.hasFDerivAt x hxΩ

/-- **Property 7.9(2)** of [quarteroni2000numerical], sufficient condition. Let $f$ be convex on
$\Omega \subseteq \mathbb{R}^n$ (7.21), so that $\Omega$ is convex, and differentiable at every
point of $\Omega$. If $x^* \in \Omega$ satisfies (7.48), $\nabla f(x^*)^T (x - x^*) \ge 0$ for
all $x \in \Omega$, then $x^*$ is a global minimizer of $f$ on $\Omega$.

The proof is the sufficiency half of `isMinOn_iff_forall_lineDeriv_nonneg` in
`Numlib.Analysis.Convex.Gateaux`. -/
theorem property_7_9_sufficient (hconv : ConvexOn ℝ Ω f) (hf : ∀ y ∈ Ω, DifferentiableAt ℝ f y)
    (hx : xstar ∈ Ω) (h48 : ∀ x ∈ Ω, 0 ≤ ⟪gradient f xstar, x - xstar⟫_ℝ) : IsMinOn f Ω xstar := by
  refine (isMinOn_iff_forall_lineDeriv_nonneg (f' := fderiv ℝ f) hconv
    (fun u hu v => (hf u hu).hasFDerivAt.hasLineDerivAt v) hx).2 fun v hv => ?_
  rw [← inner_gradient_left]
  exact h48 v hv

/-- **Equation (7.49)** of [quarteroni2000numerical]. A function $f$ is **strongly convex** on
$\Omega \subseteq \mathbb{R}^n$ with constant $\rho$ if $\rho > 0$ and
$$f(\alpha x + (1 - \alpha) y) \le \alpha f(x) + (1 - \alpha) f(y) - \alpha (1 - \alpha) \rho
  \|x - y\|_2^2$$
for all $x, y \in \Omega$ and $\alpha \in [0, 1]$. -/
def IsStronglyConvexOn (f : EuclideanSpace ℝ (Fin n) → ℝ) (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (ρ : ℝ) : Prop :=
  0 < ρ ∧ ∀ x ∈ Ω, ∀ y ∈ Ω, ∀ α ∈ Icc (0 : ℝ) 1,
    f (α • x + (1 - α) • y) ≤ α * f x + (1 - α) * f y - α * (1 - α) * ρ * ‖x - y‖ ^ 2

/-- **Equation (7.49)** of [quarteroni2000numerical], relation to Mathlib. On a convex set $\Omega$,
$f$ is strongly convex with constant $\rho$ in the sense of (7.49) if and only if $\rho > 0$ and
$f$ is `StrongConvexOn Ω (2 * ρ) f`.

Mathlib's strong convexity with modulus $m$ subtracts
$\alpha (1 - \alpha) \frac{m}{2} \|x - y\|^2$, so the book's $\rho$ is Mathlib's $m / 2$. -/
theorem isStronglyConvexOn_iff (hΩ : Convex ℝ Ω) {ρ : ℝ} :
    IsStronglyConvexOn f Ω ρ ↔ 0 < ρ ∧ StrongConvexOn Ω (2 * ρ) f := by
  constructor
  · rintro ⟨hρ, h⟩
    refine ⟨hρ, hΩ, fun x hx y hy a b ha hb hab => ?_⟩
    have hb' : b = 1 - a := by linarith
    subst hb'
    have := h x hx y hy a ⟨ha, by linarith⟩
    simp only [smul_eq_mul]
    linarith
  · rintro ⟨hρ, -, h⟩
    refine ⟨hρ, fun x hx y hy α hα => ?_⟩
    have := h hx hy hα.1 (by linarith [hα.2] : (0 : ℝ) ≤ 1 - α) (by ring)
    simp only [smul_eq_mul] at this
    linarith

/-- **Property 7.10** of [quarteroni2000numerical]. Let $\Omega \subseteq \mathbb{R}^n$ be nonempty,
closed and convex, and let $f$ be strongly convex on $\Omega$ in the sense of (7.49) and lower
semicontinuous on $\Omega$. Then $f$ has exactly one global minimizer $x^* \in \Omega$ on
$\Omega$, and every local minimizer of $f$ on $\Omega$ is a global minimizer. So $f$ has exactly
one local minimizer on $\Omega$.

**Correction.** The book does not assume that $f$ is lower semicontinuous, and without this
assumption the statement is false: $f(x) = (x - 1)^2$ on $[0, 1)$ with $f(1) = 5$ is strongly
convex on $[0, 1]$ and has no minimizer. The examples of the book are continuous.

The second part is Mathlib's `IsMinOn.of_isLocalMinOn_of_convexOn`. -/
theorem property_7_10 (hΩc : IsClosed Ω) (hΩ : Convex ℝ Ω) (hne : Ω.Nonempty) {ρ : ℝ}
    (hf : IsStronglyConvexOn f Ω ρ) (hlsc : LowerSemicontinuousOn f Ω) :
    (∃! xstar, xstar ∈ Ω ∧ IsMinOn f Ω xstar) ∧
      ∀ x ∈ Ω, IsLocalMinOn f Ω x → IsMinOn f Ω x := by
  obtain ⟨hρ, hsc⟩ := (isStronglyConvexOn_iff hΩ).1 hf
  refine ⟨existsUnique_isMinOn_of_strongConvexOn hΩc hne (by positivity) hsc hlsc,
    fun x hx hloc => IsMinOn.of_isLocalMinOn_of_convexOn hx hloc (hsc.convexOn fun r => ?_)⟩
  positivity

end Convex

/-! ### Equality constraints: Definition 7.2, the Lagrangian and Property 7.11 -/

section Equality

variable {m : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ} {h : Fin m → EuclideanSpace ℝ (Fin n) → ℝ}
  {xstar : EuclideanSpace ℝ (Fin n)}

/-- The map $v \mapsto \langle v, \cdot \rangle$ from $\mathbb{R}^n$ to its dual is injective. -/
private theorem innerSL_injective :
    Function.Injective (innerSL ℝ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  fun a b hab => by
    have h2 : innerSL ℝ (a - b) = 0 := by rw [map_sub, hab, sub_self]
    have h3 := congrArg norm h2
    rw [innerSL_apply_norm, norm_zero, norm_eq_zero] at h3
    exact sub_eq_zero.1 h3

/-- A linear combination of the functionals $\langle v_i, \cdot \rangle$ is the functional
$\langle \sum_i c_i v_i, \cdot \rangle$. -/
private theorem sum_smul_innerSL {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (v : ι → EuclideanSpace ℝ (Fin n)) :
    ∑ i ∈ s, c i • innerSL ℝ (v i) = innerSL ℝ (∑ i ∈ s, c i • v i) := by
  simp [map_sum]

/-- A family of vectors is linearly independent if and only if the family of the functionals
$\langle v_i, \cdot \rangle$ is linearly independent. -/
private theorem linearIndependent_innerSL_iff {ι : Type*} (v : ι → EuclideanSpace ℝ (Fin n)) :
    LinearIndependent ℝ (fun i => innerSL ℝ (v i)) ↔ LinearIndependent ℝ v := by
  simp only [linearIndependent_iff']
  refine forall_congr' fun s => forall_congr' fun c => imp_congr_left ?_
  rw [sum_smul_innerSL, map_eq_zero_iff _ innerSL_injective]

/-- **Definition 7.2** of [quarteroni2000numerical]. Let
$h_1, \ldots, h_m : \mathbb{R}^n \to \mathbb{R}$. A point $x$ is **regular** if $h(x) = 0$ and
the column vectors $\nabla h_i(x)$ of the Jacobian matrix $J_h(x)$ are linearly independent.

The book assumes the $h_i$ of class $C^1$ near $x$. The definition does not include this
assumption; the theorems that use it assume it. -/
def definition_7_2 (h : Fin m → EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    Prop :=
  (∀ i, h i x = 0) ∧ LinearIndependent ℝ fun i => gradient (h i) x

/-- **Definition 7.2** of [quarteroni2000numerical], relation to the backbone. A point is regular in
the sense of Definition 7.2 if and only if it is `Constrained.IsRegularPoint` for the derivative
data $h_i'(y) = $ `fderiv ℝ (h i) y`. -/
theorem definition_7_2_iff (x : EuclideanSpace ℝ (Fin n)) :
    definition_7_2 h x ↔ Constrained.IsRegularPoint h (fun i y => fderiv ℝ (h i) y) x := by
  rw [definition_7_2, Constrained.IsRegularPoint, Constrained.mem_feasibleEq]
  refine and_congr Iff.rfl ?_
  simp only [fderiv_eq_innerSL_gradient]
  exact (linearIndependent_innerSL_iff _).symm

/-- **Section 7.3** of [quarteroni2000numerical], the Lagrangian. The **Lagrangian** of the
equality-constrained problem (7.50) is
$$\mathcal{L}(x, \lambda) = f(x) + \lambda^T h(x), \qquad x \in \mathbb{R}^n, \ \lambda \in
  \mathbb{R}^m.$$

The definition is the backbone's `Constrained.lagrangian`. -/
def lagrangian (f : EuclideanSpace ℝ (Fin n) → ℝ) (h : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (l : Fin m → ℝ) : ℝ :=
  Constrained.lagrangian f h x l

/-- **Section 7.3** of [quarteroni2000numerical], the Lagrangian in coordinates. $\mathcal{L}(x,
\lambda) = f(x) + \sum_{i=1}^m \lambda_i h_i(x)$. -/
theorem lagrangian_eq (x : EuclideanSpace ℝ (Fin n)) (l : Fin m → ℝ) :
    lagrangian f h x l = f x + ∑ i, l i * h i x :=
  rfl

/-- **Section 7.3** of [quarteroni2000numerical], the partial Jacobian $J_\mathcal{L}$. Let $f$ and
the $h_i$ be differentiable at $x$. Then the gradient of $\mathcal{L}(\cdot, \lambda)$ at $x$ is
$$J_\mathcal{L}(x, \lambda) = \nabla f(x) + \sum_{i=1}^m \lambda_i \nabla h_i(x).$$
-/
theorem gradient_lagrangian {x : EuclideanSpace ℝ (Fin n)} (hf : DifferentiableAt ℝ f x)
    (hh : ∀ i, DifferentiableAt ℝ (h i) x) (l : Fin m → ℝ) :
    gradient (fun y => lagrangian f h y l) x = gradient f x + ∑ i, l i • gradient (h i) x := by
  have hd := Constrained.lagrangian_hasFDerivAt (f' := fun y => fderiv ℝ f y)
    (h' := fun i y => fderiv ℝ (h i) y) hf.hasFDerivAt (fun i => (hh i).hasFDerivAt) l
  refine HasGradientAt.gradient (f' := gradient f x + ∑ i, l i • gradient (h i) x) ?_
  rw [hasGradientAt_iff_hasFDerivAt]
  refine hd.congr_fderiv ?_
  ext v
  simp only [fderiv_eq_innerSL_gradient, InnerProductSpace.toDual_apply_apply, inner_add_left,
    sum_inner, inner_smul_left, RCLike.conj_to_real, _root_.add_apply,
    _root_.sum_apply, _root_.smul_apply, innerSL_apply_apply, smul_eq_mul]

/-- **Property 7.11** of [quarteroni2000numerical], first part. Let $f$ and $h_1, \ldots, h_m$ be of
class $C^1$ near $x^*$. Let $x^*$ be a regular point (Definition 7.2) and a local minimizer of
$f$ on $\{x : h(x) = 0\}$. Then there is a unique $\lambda^* \in \mathbb{R}^m$ with
$J_\mathcal{L}(x^*, \lambda^*) = 0$, that is,
$$\nabla f(x^*) + \sum_{i=1}^m \lambda^*_i \nabla h_i(x^*) = 0.$$

**Correction.** The book does not assume that $x^*$ is regular, although Definition 7.2 comes
just before the property. Without regularity the statement is false: for $\min x$ subject to
$x^2 = 0$, no multiplier exists.

The proof specializes `Constrained.existsUnique_multipliers_of_isLocalMinOn`. -/
theorem property_7_11 (hreg : definition_7_2 h xstar)
    (hmin : IsLocalMinOn f {x | ∀ i, h i x = 0} xstar) (hf : ContDiffAt ℝ 1 f xstar)
    (hh : ∀ i, ContDiffAt ℝ 1 (h i) xstar) :
    ∃! l : Fin m → ℝ, gradient f xstar + ∑ i, l i • gradient (h i) xstar = 0 := by
  have hex := Constrained.existsUnique_multipliers_of_isLocalMinOn (f' := fun y => fderiv ℝ f y)
    ((definition_7_2_iff xstar).1 hreg) hmin (hf.hasStrictFDerivAt one_ne_zero)
    fun i => (hh i).hasStrictFDerivAt one_ne_zero
  refine (existsUnique_congr fun l => ?_).1 hex
  simp only [fderiv_eq_innerSL_gradient]
  rw [sum_smul_innerSL, ← map_add, map_eq_zero_iff _ innerSL_injective]

/-- **Property 7.11** of [quarteroni2000numerical], second part. Let $f$ and $h_1, \ldots, h_m$ be
of class $C^2$ near $x^*$, and let $h(x^*) = 0$. Let $\lambda^* \in \mathbb{R}^m$ satisfy
$J_\mathcal{L}(x^*, \lambda^*) = 0$, and let $H_\mathcal{L}(x^*, \lambda^*)$ be the Hessian
matrix of $\mathcal{L}(\cdot, \lambda^*)$ at $x^*$. If $z^T H_\mathcal{L}(x^*, \lambda^*) z > 0$
for every $z \neq 0$ with $\nabla h_i(x^*)^T z = 0$ for all $i$, then $x^*$ is a strict local
minimizer of (7.50): there is $\delta > 0$ with $f(x^*) < f(y)$ for every $y \neq x^*$ with
$h(y) = 0$ and $\|y - x^*\| < \delta$.

The Hessian matrix is `QuarteroniSaccoSaleri.Chapter07.hessianMatrix`. The proof specializes
`Constrained.isLocalMin_of_lagrangian_second_order`. -/
theorem property_7_11_sufficient (hfeas : ∀ i, h i xstar = 0) (hf : ContDiffAt ℝ 2 f xstar)
    (hh : ∀ i, ContDiffAt ℝ 2 (h i) xstar) {l : Fin m → ℝ}
    (hstat : gradient f xstar + ∑ i, l i • gradient (h i) xstar = 0)
    (hpos : ∀ z, z ≠ 0 → (∀ i, ⟪gradient (h i) xstar, z⟫_ℝ = 0) →
      0 < ⟪toEuclideanLin (hessianMatrix (fun y => lagrangian f h y l) xstar) z, z⟫_ℝ) :
    ∃ δ > 0, ∀ y, (∀ i, h i y = 0) → dist y xstar < δ → y ≠ xstar → f xstar < f y := by
  -- the Lagrangian is `C²` at `x*`
  have hL : ContDiffAt ℝ 2 (fun y => lagrangian f h y l) xstar := by
    simp only [lagrangian_eq]
    exact hf.add (ContDiffAt.sum fun i _ => (hh i).const_smul (l i))
  have hd : DifferentiableAt ℝ (fderiv ℝ fun y => lagrangian f h y l) xstar :=
    (hL.fderiv_right (m := 1) le_rfl).differentiableAt one_ne_zero
  -- the derivative of the Lagrangian near `x*` is `f' + ∑ λ_i h_i'`
  have hf1 : ∀ᶠ y in 𝓝 xstar, HasFDerivAt f (fderiv ℝ f y) y := by
    filter_upwards [hf.eventually (by simp)] with y hy
    exact (hy.differentiableAt (by simp)).hasFDerivAt
  have hh1 : ∀ i, ∀ᶠ y in 𝓝 xstar, HasFDerivAt (h i) (fderiv ℝ (h i) y) y := fun i => by
    filter_upwards [(hh i).eventually (by simp)] with y hy
    exact (hy.differentiableAt (by simp)).hasFDerivAt
  have hLderiv : (fun y => fderiv ℝ f y + ∑ i, l i • fderiv ℝ (h i) y)
      =ᶠ[𝓝 xstar] fderiv ℝ (fun y => lagrangian f h y l) := by
    filter_upwards [hf1, (Filter.eventually_all).2 hh1] with y hfy hhy
    exact (Constrained.lagrangian_hasFDerivAt hfy hhy l).fderiv.symm
  have hH : HasFDerivAt (fun y => fderiv ℝ f y + ∑ i, l i • fderiv ℝ (h i) y)
      (fderiv ℝ (fderiv ℝ fun y => lagrangian f h y l) xstar) xstar :=
    hd.hasFDerivAt.congr_of_eventuallyEq hLderiv
  refine Constrained.isLocalMin_of_lagrangian_second_order (h' := fun i y => fderiv ℝ (h i) y)
    hfeas hf1 hh1 hH ?_ fun z hz hz' => ?_
  · simp only [fderiv_eq_innerSL_gradient]
    rw [sum_smul_innerSL, ← map_add, hstat, map_zero]
  · rw [← inner_toEuclideanLin_hessianMatrix hd]
    refine hpos z hz fun i => ?_
    have := hz' i
    rwa [fderiv_eq_innerSL_gradient, innerSL_apply_apply] at this

end Equality

/-! ### Inequality constraints: Definition 7.3 and the Kuhn–Tucker conditions of Property 7.12 -/

section Inequality

variable {m r : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ} {h : Fin m → EuclideanSpace ℝ (Fin n) → ℝ}
  {g : Fin r → EuclideanSpace ℝ (Fin n) → ℝ} {xstar : EuclideanSpace ℝ (Fin n)}

/-- **Definition 7.3** of [quarteroni2000numerical]. Let $h_1, \ldots, h_m, g_1, \ldots, g_r :
\mathbb{R}^n \to \mathbb{R}$, and let $\mathcal{J}(x) = \{j : g_j(x) = 0\}$ be the set of active
inequality constraints at $x$. A point $x$ is **regular** if $h(x) = 0$, $g(x) \le 0$, and the
vectors $\nabla h_i(x)$, $i = 1, \ldots, m$, together with the vectors $\nabla g_j(x)$,
$j \in \mathcal{J}(x)$, are linearly independent.

The active set is `Constrained.activeSet g x`. -/
def definition_7_3 (h : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (g : Fin r → EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  (∀ i, h i x = 0) ∧ (∀ j, g j x ≤ 0) ∧
    LinearIndependent ℝ (Sum.elim (fun i => gradient (h i) x)
      fun j : Constrained.activeSet g x => gradient (g j) x)

/-- **Definition 7.3** of [quarteroni2000numerical], relation to the backbone. A point is regular in
the sense of Definition 7.3 if and only if it is `Constrained.IsRegularPointIneq` for the
derivative data `fderiv ℝ (h i) y` and `fderiv ℝ (g j) y`. -/
theorem definition_7_3_iff (x : EuclideanSpace ℝ (Fin n)) :
    definition_7_3 h g x ↔ Constrained.IsRegularPointIneq h (fun i y => fderiv ℝ (h i) y) g
      (fun j y => fderiv ℝ (g j) y) x := by
  rw [definition_7_3, Constrained.IsRegularPointIneq]
  refine and_congr Iff.rfl (and_congr Iff.rfl ?_)
  simp only [fderiv_eq_innerSL_gradient]
  have : (Sum.elim (fun i => innerSL ℝ (gradient (h i) x))
      fun j : Constrained.activeSet g x => innerSL ℝ (gradient (g j) x))
      = fun s => innerSL ℝ ((Sum.elim (fun i => gradient (h i) x)
        fun j : Constrained.activeSet g x => gradient (g j) x) s) := by
    funext s
    cases s <;> rfl
  rw [this, linearIndependent_innerSL_iff]

/-- **Property 7.12** of [quarteroni2000numerical] (Karush–Kuhn–Tucker conditions). Let $f$,
$h_1, \ldots, h_m$ and $g_1, \ldots, g_r$ be of class $C^1$ near $x^*$. Let $x^*$ be a regular
point (Definition 7.3) and a local minimizer of $f$ on $\{x : h(x) = 0, \ g(x) \le 0\}$. Then
there is exactly one pair $(\lambda^*, \mu^*) \in \mathbb{R}^m \times \mathbb{R}^r$ with
$$J_\mathcal{M}(x^*, \lambda^*, \mu^*) = \nabla f(x^*) + \sum_{i=1}^m \lambda^*_i \nabla
  h_i(x^*) + \sum_{j=1}^r \mu^*_j \nabla g_j(x^*) = 0,$$
$\mu^*_j \ge 0$ and $\mu^*_j g_j(x^*) = 0$ for all $j$.

Existence is `Constrained.exists_kkt_of_isLocalMinOn`, which uses the implicit function theorem
and Farkas' lemma. Uniqueness is `Constrained.kkt_multipliers_unique`. -/
theorem property_7_12 (hreg : definition_7_3 h g xstar)
    (hmin : IsLocalMinOn f {x | (∀ i, h i x = 0) ∧ ∀ j, g j x ≤ 0} xstar)
    (hf : ContDiffAt ℝ 1 f xstar) (hh : ∀ i, ContDiffAt ℝ 1 (h i) xstar)
    (hg : ∀ j, ContDiffAt ℝ 1 (g j) xstar) :
    ∃! p : (Fin m → ℝ) × (Fin r → ℝ),
      gradient f xstar + ∑ i, p.1 i • gradient (h i) xstar + ∑ j, p.2 j • gradient (g j) xstar = 0
        ∧ (∀ j, 0 ≤ p.2 j) ∧ ∀ j, p.2 j * g j xstar = 0 := by
  have hreg' := (definition_7_3_iff xstar).1 hreg
  have hkkt : ∀ p : (Fin m → ℝ) × (Fin r → ℝ),
      Constrained.IsKKTPoint (fun y => fderiv ℝ f y) h (fun i y => fderiv ℝ (h i) y) g
          (fun j y => fderiv ℝ (g j) y) xstar p.1 p.2 ↔
        gradient f xstar + ∑ i, p.1 i • gradient (h i) xstar
          + ∑ j, p.2 j • gradient (g j) xstar = 0 ∧ (∀ j, 0 ≤ p.2 j) ∧
          ∀ j, p.2 j * g j xstar = 0 := by
    intro p
    have hst : fderiv ℝ f xstar + ∑ i, p.1 i • fderiv ℝ (h i) xstar
          + ∑ j, p.2 j • fderiv ℝ (g j) xstar = 0 ↔
        gradient f xstar + ∑ i, p.1 i • gradient (h i) xstar
          + ∑ j, p.2 j • gradient (g j) xstar = 0 := by
      simp only [fderiv_eq_innerSL_gradient]
      rw [sum_smul_innerSL, sum_smul_innerSL, ← map_add, ← map_add,
        map_eq_zero_iff _ innerSL_injective]
    constructor
    · rintro ⟨-, -, hs, hn, hc⟩
      exact ⟨hst.1 hs, hn, hc⟩
    · rintro ⟨hs, hn, hc⟩
      exact ⟨hreg.1, hreg.2.1, hst.2 hs, hn, hc⟩
  obtain ⟨l, μ, hlμ⟩ := Constrained.exists_kkt_of_isLocalMinOn hreg' hmin
    (hf.differentiableAt one_ne_zero).hasFDerivAt (fun i => (hh i).hasStrictFDerivAt one_ne_zero)
    fun j => (hg j).hasStrictFDerivAt one_ne_zero
  refine ⟨(l, μ), (hkkt (l, μ)).1 hlμ, fun p hp => ?_⟩
  obtain ⟨h1, h2⟩ := Constrained.kkt_multipliers_unique hreg' ((hkkt p).2 hp) hlμ
  exact Prod.ext h1 h2

end Inequality

/-! ### Section 7.3.1: the nonlinear programming problem and the Kuhn–Tucker conditions -/

section NonlinearProgramming

variable {m : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ} {g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ}
  {b : Fin m → ℝ} {l k : ℕ} {xstar : EuclideanSpace ℝ (Fin n)}

/-- **Equation (7.52)** of [quarteroni2000numerical], the feasible region. The nonlinear programming
problem of Section 7.3.1 is to maximize $f(x)$ subject to
$$g_i(x) \le b_i \ (i = 1, \ldots, l), \quad g_i(x) \ge b_i \ (i = l + 1, \ldots, k), \quad
  g_i(x) = b_i \ (i = k + 1, \ldots, m), \quad x \ge 0.$$
A vector that satisfies these constraints is a **feasible solution**, and the set of feasible
solutions is the **feasible region**.

The book's index $i$ is $1$-based, and `i : Fin m` is $0$-based, so the book's $i \le l$ is
`(i : ℕ) < l`. The index sets of Section 7.3.1, $I_= = \{i : g_i(x) = b_i\}$, its complement
$I_{\neq}$, $J_= = \{j : x_j = 0\}$ and $J_> = \{j : x_j > 0\}$, have no Lean definitions; the
statements write out the conditions where they occur. -/
def feasibleRegion (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ) (b : Fin m → ℝ) (l k : ℕ) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {x | (∀ i : Fin m, (i : ℕ) < l → g i x ≤ b i) ∧
    (∀ i : Fin m, l ≤ (i : ℕ) → (i : ℕ) < k → b i ≤ g i x) ∧
    (∀ i : Fin m, k ≤ (i : ℕ) → g i x = b i) ∧ ∀ j, 0 ≤ x j}

/-- **Equation (7.52)** of [quarteroni2000numerical], membership. A vector $x$ is in the feasible
region if and only if $g_i(x) \le b_i$ for $i \le l$, $g_i(x) \ge b_i$ for $l < i \le k$,
$g_i(x) = b_i$ for $i > k$, and $x_j \ge 0$ for all $j$. -/
@[simp] theorem mem_feasibleRegion {x : EuclideanSpace ℝ (Fin n)} :
    x ∈ feasibleRegion g b l k ↔ (∀ i : Fin m, (i : ℕ) < l → g i x ≤ b i) ∧
      (∀ i : Fin m, l ≤ (i : ℕ) → (i : ℕ) < k → b i ≤ g i x) ∧
      (∀ i : Fin m, k ≤ (i : ℕ) → g i x = b i) ∧ ∀ j, 0 ≤ x j := Iff.rfl

/-- For a convex set $C$, a real number $c$ and a coordinate $j$, the function $y \mapsto c \, y_j$
is convex on $C$. -/
private theorem convexOn_const_mul_coord {C : Set (EuclideanSpace ℝ (Fin n))} (hC : Convex ℝ C)
    (c : ℝ) (j : Fin n) : ConvexOn ℝ C fun y : EuclideanSpace ℝ (Fin n) => c * y j := by
  refine ⟨hC, fun x _ y _ a t _ _ _ => le_of_eq ?_⟩
  have h : (a • x + t • y) j = a * x j + t * y j := by simp
  simp only [smul_eq_mul, h]
  ring

/-- **Section 7.3.1** of [quarteroni2000numerical], the Lagrangian of (7.52). For a multiplier
$\lambda \in \mathbb{R}^{m+n}$,
$$\mathcal{L}(x, \lambda) = f(x) + \sum_{i=1}^m \lambda_i (b_i - g_i(x)) - \sum_{i=1}^n
  \lambda_{m+i} x_i.$$

The multiplier $\lambda$ is the pair $(\lambda_1, \lambda_2)$ of its first $m$ and its last $n$
components, with $\lambda_2$ a vector of $\mathbb{R}^n$. The last sum is then the inner product
$\langle \lambda_2, x \rangle$; `QuarteroniSaccoSaleri.Chapter07.nonlinearLagrangian_eq` writes
it in coordinates. -/
noncomputable def nonlinearLagrangian (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ) (b : Fin m → ℝ) (x : EuclideanSpace ℝ (Fin n))
    (lam : (Fin m → ℝ) × EuclideanSpace ℝ (Fin n)) : ℝ :=
  f x + ∑ i, lam.1 i * (b i - g i x) - ⟪lam.2, x⟫_ℝ

/-- **Section 7.3.1** of [quarteroni2000numerical], the Lagrangian of (7.52) in coordinates:
$\mathcal{L}(x, \lambda) = f(x) + \sum_i \lambda_{1,i} (b_i - g_i(x)) - \sum_j \lambda_{2,j}
x_j$. -/
theorem nonlinearLagrangian_eq (x : EuclideanSpace ℝ (Fin n))
    (lam : (Fin m → ℝ) × EuclideanSpace ℝ (Fin n)) :
    nonlinearLagrangian f g b x lam
      = f x + ∑ i, lam.1 i * (b i - g i x) - ∑ j, lam.2 j * x j := by
  rw [nonlinearLagrangian, EuclideanSpace.real_inner_eq_sum]

/-- **Section 7.3.1** of [quarteroni2000numerical], the partial Jacobian $J_\mathcal{L}(x,
\lambda) = \nabla_x \mathcal{L}(x, \lambda)$ of the Lagrangian of (7.52). Let $f$ and the $g_i$
be differentiable at $x$. Then
$$\nabla_x \mathcal{L}(x, \lambda) = \nabla f(x) - \sum_{i=1}^m \lambda_{1,i} \nabla g_i(x) -
  \lambda_2.$$
-/
theorem gradient_nonlinearLagrangian {x : EuclideanSpace ℝ (Fin n)} (hf : DifferentiableAt ℝ f x)
    (hg : ∀ i, DifferentiableAt ℝ (g i) x) (lam : (Fin m → ℝ) × EuclideanSpace ℝ (Fin n)) :
    gradient (fun y => nonlinearLagrangian f g b y lam) x
      = gradient f x - ∑ i, lam.1 i • gradient (g i) x - lam.2 := by
  have hd : HasFDerivAt (fun y => nonlinearLagrangian f g b y lam)
      (fderiv ℝ f x + ∑ i, lam.1 i • (-fderiv ℝ (g i) x) - innerSL ℝ lam.2) x := by
    simp only [nonlinearLagrangian]
    exact (hf.hasFDerivAt.add (HasFDerivAt.fun_sum (u := Finset.univ) fun i _ =>
      ((hg i).hasFDerivAt.const_sub (b i)).const_mul (lam.1 i))).sub
      (innerSL ℝ lam.2).hasFDerivAt
  refine HasGradientAt.gradient ?_
  rw [hasGradientAt_iff_hasFDerivAt]
  refine hd.congr_fderiv ?_
  ext v
  simp only [fderiv_eq_innerSL_gradient, InnerProductSpace.toDual_apply_apply, inner_sub_left,
    sum_inner, inner_smul_left, RCLike.conj_to_real, _root_.add_apply, _root_.sub_apply,
    _root_.sum_apply, _root_.smul_apply, _root_.neg_apply, innerSL_apply_apply, smul_eq_mul,
    mul_neg]
  rw [Finset.sum_neg_distrib]
  ring


/-- The partial Jacobian of the Lagrangian of (7.52) in a direction $v$: $\langle \nabla_x
\mathcal{L}(x, \lambda), v \rangle = f'(x) v - \sum_i \lambda_{1,i} \, g_i'(x) v - \langle
\lambda_2, v \rangle$. -/
private theorem inner_gradient_nonlinearLagrangian {x : EuclideanSpace ℝ (Fin n)}
    (hf : DifferentiableAt ℝ f x) (hg : ∀ i, DifferentiableAt ℝ (g i) x)
    (lam : (Fin m → ℝ) × EuclideanSpace ℝ (Fin n)) (v : EuclideanSpace ℝ (Fin n)) :
    ⟪gradient (fun y => nonlinearLagrangian f g b y lam) x, v⟫_ℝ
      = fderiv ℝ f x v - ∑ i, lam.1 i * fderiv ℝ (g i) x v - ⟪lam.2, v⟫_ℝ := by
  rw [gradient_nonlinearLagrangian hf hg, inner_sub_left, inner_sub_left, sum_inner]
  simp only [inner_smul_left, RCLike.conj_to_real, fderiv_eq_innerSL_gradient,
    innerSL_apply_apply]

/-!
### The standard form of (7.52)

Problem (7.52) is translated into the standard form of Property 7.12: minimize $-f$ subject to
equality constraints $h = 0$ and inequality constraints $\tilde g \le 0$. The equality constraints
are indexed by the $i$ with $i > k$ in the book's numbering. The inequality constraints are indexed
by the $i \le k$, together with the $n$ sign constraints $-x_j \le 0$.
-/

/-- **Equation (7.52)** of [quarteroni2000numerical], standard form. The equality constraints of
(7.52) in the standard form of Property 7.12 are $g_i(x) - b_i = 0$ for $i = k + 1, \ldots, m$. -/
def standardEq (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ) (b : Fin m → ℝ) (k : ℕ) :
    {i : Fin m // k ≤ (i : ℕ)} → EuclideanSpace ℝ (Fin n) → ℝ := fun i y => g i y - b i

/-- **Equation (7.52)** of [quarteroni2000numerical], standard form. The derivatives of the equality
constraints `QuarteroniSaccoSaleri.Chapter07.standardEq`: the derivative of $g_i(x) - b_i$ at
$y$ is $g_i'(y)$. -/
noncomputable def standardEqDeriv (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ) (k : ℕ) :
    {i : Fin m // k ≤ (i : ℕ)} → EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := fun i y => fderiv ℝ (g i) y

/-- **Equation (7.52)** of [quarteroni2000numerical], standard form. The sign $\sigma_i$ with which
the $i$-th constraint of (7.52) enters the standard form of Property 7.12: $\sigma_i = 1$ for
the constraints $g_i(x) \le b_i$ ($i = 1, \ldots, l$), and $\sigma_i = -1$ otherwise, in
particular for $g_i(x) \ge b_i$ ($i = l + 1, \ldots, k$). -/
def standardSign (l : ℕ) (i : Fin m) : ℝ := if (i : ℕ) < l then 1 else -1

/-- The sign $\sigma_i$ of a constraint $g_i(x) \le b_i$ of (7.52), $i \le l$, is $1$. -/
theorem standardSign_of_lt {i : Fin m} (h : (i : ℕ) < l) : standardSign l i = 1 := by
  simp [standardSign, h]

/-- The sign $\sigma_i$ of a constraint of (7.52) with $i > l$ is $-1$. -/
theorem standardSign_of_le {i : Fin m} (h : l ≤ (i : ℕ)) : standardSign l i = -1 := by
  simp [standardSign, Nat.not_lt.2 h]

/-- **Equation (7.52)** of [quarteroni2000numerical], standard form. The inequality constraints of
(7.52) in the standard form of Property 7.12 are $\sigma_i (g_i(x) - b_i) \le 0$ for
$i = 1, \ldots, k$, that is, $g_i(x) \le b_i$ for $i \le l$ and $g_i(x) \ge b_i$ for
$l < i \le k$, together with the sign constraints $-x_j \le 0$, $j = 1, \ldots, n$.

The index type is the sum of $\{i : i \le k\}$ and `Fin n`. -/
def standardIneq (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ) (b : Fin m → ℝ) (l k : ℕ) :
    {i : Fin m // (i : ℕ) < k} ⊕ Fin n → EuclideanSpace ℝ (Fin n) → ℝ :=
  Sum.elim (fun i y => standardSign l (i : Fin m) * (g i y - b i)) fun j y => -y j

/-- **Equation (7.52)** of [quarteroni2000numerical], standard form. The derivatives of the
inequality constraints `QuarteroniSaccoSaleri.Chapter07.standardIneq`: $\sigma_i g_i'(y)$ for
$\sigma_i (g_i(x) - b_i)$, and $-e_j^T$ for $-x_j$. -/
noncomputable def standardIneqDeriv (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ) (l k : ℕ) :
    {i : Fin m // (i : ℕ) < k} ⊕ Fin n → EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
  Sum.elim (fun i y => standardSign l (i : Fin m) • fderiv ℝ (g i) y)
    fun j _ => -EuclideanSpace.proj (𝕜 := ℝ) j

/-- **Equation (7.52)** of [quarteroni2000numerical] in the standard form of Property 7.12. If
$l \le k$, the feasible region of (7.52) is the set `Constrained.feasible` of the points where
all equality constraints `QuarteroniSaccoSaleri.Chapter07.standardEq` vanish and all inequality
constraints `QuarteroniSaccoSaleri.Chapter07.standardIneq` are nonpositive.

**Reading.** The index ranges of (7.52) presuppose $l \le k$, which the book does not write.
Every statement about (7.52) below assumes it. -/
theorem nonlinearProgram_toStandard (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ) (b : Fin m → ℝ)
    {l k : ℕ} (hlk : l ≤ k) : feasibleRegion g b l k
      = Constrained.feasible (standardEq g b k) (standardIneq g b l k) := by
  ext x
  simp only [mem_feasibleRegion, Constrained.mem_feasible, standardEq, standardIneq,
    Subtype.forall, Sum.forall, Sum.elim_inl, Sum.elim_inr, sub_eq_zero, neg_nonpos]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h3, fun i hik => ?_, h4⟩
    rcases lt_or_ge (i : ℕ) l with hil | hil
    · rw [standardSign_of_lt hil]
      linarith [h1 i hil]
    · rw [standardSign_of_le hil]
      linarith [h2 i hil hik]
  · rintro ⟨h3, h12, h4⟩
    refine ⟨fun i hil => ?_, fun i hli hik => ?_, h3, h4⟩
    · have h := h12 i (hil.trans_le hlk)
      rw [standardSign_of_lt hil] at h
      linarith
    · have h := h12 i hik
      rw [standardSign_of_le hli] at h
      linarith

/-- **Section 7.3.1** of [quarteroni2000numerical], the constraint qualification for (7.52). A point
$x$ satisfies it if $x$ is a regular point (Definition 7.3) of the standard form of (7.52) in
`QuarteroniSaccoSaleri.Chapter07.nonlinearProgram_toStandard`. That is, $x$ is feasible, and the
gradients $\nabla g_i(x)$ of the equality constraints $k < i \le m$ and of the active inequality
constraints $i \le k$, together with the vectors $-e_j$ of the active sign constraints
$x_j = 0$, are linearly independent.

The book alludes to a constraint qualification after Property 7.14 and does not state it. -/
def IsRegularNLP (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ) (b : Fin m → ℝ) (l k : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  Constrained.IsRegularPointIneq (standardEq g b k) (standardEqDeriv g k) (standardIneq g b l k)
    (standardIneqDeriv g l k) x

/-! ### The Kuhn–Tucker conditions of Properties 7.13–7.15 -/

/-- For a family $F$ indexed by `Fin m`, the sum over the indices $i < k$ plus the sum over the
indices $i \ge k$ is the sum over all indices. -/
private theorem sum_split_at {V : Type*} [AddCommMonoid V] (k : ℕ) (F : Fin m → V) :
    ∑ i : {i : Fin m // (i : ℕ) < k}, F i + ∑ i : {i : Fin m // k ≤ (i : ℕ)}, F i = ∑ i, F i := by
  have h1 : ∑ i : {i : Fin m // (i : ℕ) < k}, F i
      = ∑ i ∈ Finset.univ.filter fun i : Fin m => (i : ℕ) < k, F i :=
    (Finset.sum_subtype _ (fun x => by simp) F).symm
  have h2 : ∑ i : {i : Fin m // k ≤ (i : ℕ)}, F i
      = ∑ i ∈ Finset.univ.filter fun i : Fin m => ¬ ((i : ℕ) < k), F i :=
    (Finset.sum_subtype _ (fun x => by simp [not_lt]) F).symm
  rw [h1, h2, Finset.sum_filter_add_sum_filter_not]

/-- **Property 7.13** of [quarteroni2000numerical], the Kuhn–Tucker multipliers. Let $l \le k$, let
$f$ and the $g_i$ be of class $C^1$ on $\mathbb{R}^n$, and let $x^*$ be a constrained local
maximizer of (7.52) that satisfies the constraint qualification
`QuarteroniSaccoSaleri.Chapter07.IsRegularNLP`. Then there is a multiplier $\lambda^* =
(\lambda^*_1, \lambda^*_2) \in \mathbb{R}^m \times \mathbb{R}^n$ with
$\nabla_x \mathcal{L}(x^*, \lambda^*) = 0$, with the signs
$$\lambda^*_{1,i} \ge 0 \ (i \le l), \qquad \lambda^*_{1,i} \le 0 \ (l < i \le k), \qquad
  \lambda^*_{2,j} \le 0 \ (\text{all } j),$$
and with the complementarity conditions $\lambda^*_{1,i} (b_i - g_i(x^*)) = 0$ and
$\lambda^*_{2,j} x^*_j = 0$ for all $i$ and $j$.

Properties 7.13 and 7.14 follow from this result. The book does not list the signs among the
Kuhn–Tucker conditions, but Property 7.15 needs them. The proof applies
`Constrained.exists_kkt_of_isLocalMinOn` to the minimization of $-f$ in the standard form. -/
theorem exists_kuhnTucker (hlk : l ≤ k) (hreg : IsRegularNLP g b l k xstar)
    (hmax : IsLocalMaxOn f (feasibleRegion g b l k) xstar) (hf : ContDiff ℝ 1 f)
    (hg : ∀ i, ContDiff ℝ 1 (g i)) :
    ∃ lam : (Fin m → ℝ) × EuclideanSpace ℝ (Fin n),
      gradient (fun y => nonlinearLagrangian f g b y lam) xstar = 0 ∧
        (∀ i : Fin m, (i : ℕ) < l → 0 ≤ lam.1 i) ∧
        (∀ i : Fin m, l ≤ (i : ℕ) → (i : ℕ) < k → lam.1 i ≤ 0) ∧ (∀ j, lam.2 j ≤ 0) ∧
        (∀ i, lam.1 i * (b i - g i xstar) = 0) ∧ ∀ j, lam.2 j * xstar j = 0 := by
  have hdf : ∀ y, HasStrictFDerivAt f (fderiv ℝ f y) y := fun y =>
    hf.contDiffAt.hasStrictFDerivAt one_ne_zero
  have hdg : ∀ i, ∀ y, HasStrictFDerivAt (g i) (fderiv ℝ (g i) y) y := fun i y =>
    (hg i).contDiffAt.hasStrictFDerivAt one_ne_zero
  have hmin : IsLocalMinOn (fun y => -f y)
      (Constrained.feasible (standardEq g b k) (standardIneq g b l k)) xstar := by
    rw [← nonlinearProgram_toStandard g b hlk]
    exact hmax.neg
  obtain ⟨l0, mu, hkkt⟩ := Constrained.exists_kkt_of_isLocalMinOn
    (f' := fun y => -fderiv ℝ f y) (h' := standardEqDeriv g k) (g' := standardIneqDeriv g l k)
    hreg hmin ((hdf xstar).hasFDerivAt.neg) (fun i => (hdg i xstar).sub_const (b i))
    (fun s => by
      cases s with
      | inl i => exact ((hdg i xstar).sub_const (b i)).const_mul (standardSign l (i : Fin m))
      | inr j => exact (EuclideanSpace.proj (𝕜 := ℝ) j).hasStrictFDerivAt.neg)
  set lam1 : Fin m → ℝ := fun i => if hik : (i : ℕ) < k then
    standardSign l i * mu (Sum.inl ⟨i, hik⟩) else l0 ⟨i, not_lt.1 hik⟩ with hlam1
  set lam2 : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun j => -mu (Sum.inr j)) with hlam2
  have hlam2v : ∀ j, lam2 j = -mu (Sum.inr j) := fun j => by rw [hlam2]
  refine ⟨(lam1, lam2), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hdiff : DifferentiableAt ℝ f xstar := (hdf xstar).hasFDerivAt.differentiableAt
    have hdiffg : ∀ i, DifferentiableAt ℝ (g i) xstar := fun i =>
      (hdg i xstar).hasFDerivAt.differentiableAt
    rw [gradient_nonlinearLagrangian hdiff hdiffg]
    refine innerSL_injective ?_
    rw [map_zero, map_sub, map_sub, ← sum_smul_innerSL]
    simp only [← fderiv_eq_innerSL_gradient]
    have hstat : -fderiv ℝ f xstar + ∑ i, l0 i • standardEqDeriv g k i xstar
        + ∑ s, mu s • standardIneqDeriv g l k s xstar = 0 := hkkt.stationary
    have h1 : ∑ i, (lam1, lam2).1 i • fderiv ℝ (g i) xstar
        = ∑ i : {i : Fin m // (i : ℕ) < k},
            mu (Sum.inl i) • standardIneqDeriv g l k (Sum.inl i) xstar
          + ∑ i : {i : Fin m // k ≤ (i : ℕ)}, l0 i • standardEqDeriv g k i xstar := by
      rw [← sum_split_at k fun i => (lam1, lam2).1 i • fderiv ℝ (g i) xstar]
      congr 1
      · refine Finset.sum_congr rfl fun i _ => ?_
        simp only [hlam1, dite_eq_left i.2, standardIneqDeriv, Sum.elim_inl, smul_smul, mul_comm]
      · refine Finset.sum_congr rfl fun i _ => ?_
        simp only [hlam1, dite_eq_right (not_lt.2 i.2), standardEqDeriv]
    have h2 : innerSL ℝ (lam1, lam2).2
        = ∑ j, mu (Sum.inr j) • standardIneqDeriv g l k (Sum.inr j) xstar := by
      rw [EuclideanSpace.innerSL_eq_sum_smul_proj]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [standardIneqDeriv, Sum.elim_inr, hlam2v, neg_smul, smul_neg]
    have h3 : fderiv ℝ f xstar - ∑ i, (lam1, lam2).1 i • fderiv ℝ (g i) xstar
          - innerSL ℝ (lam1, lam2).2
        = -(-fderiv ℝ f xstar + ∑ i, l0 i • standardEqDeriv g k i xstar
            + ∑ s, mu s • standardIneqDeriv g l k s xstar) := by
      rw [Fintype.sum_sum_type, h1, h2]
      abel
    rw [h3, hstat, neg_zero]
  · intro i hil
    simp only [hlam1, dite_eq_left (hil.trans_le hlk), standardSign_of_lt hil, one_mul]
    exact hkkt.nonneg _
  · intro i hli hik
    simp only [hlam1, dite_eq_left hik, standardSign_of_le hli, neg_one_mul, neg_nonpos]
    exact hkkt.nonneg _
  · intro j
    rw [hlam2v j, neg_nonpos]
    exact hkkt.nonneg _
  · intro i
    by_cases hik : (i : ℕ) < k
    · have hc := hkkt.complementary (Sum.inl ⟨i, hik⟩)
      simp only [standardIneq, Sum.elim_inl] at hc
      simp only [hlam1, dite_eq_left hik]
      linear_combination -hc
    · have he : g i xstar - b i = 0 := hkkt.feasible_eq ⟨i, not_lt.1 hik⟩
      simp only [hlam1, dite_eq_right hik]
      linear_combination -l0 ⟨i, not_lt.1 hik⟩ * he
  · intro j
    have hc := hkkt.complementary (Sum.inr j)
    simp only [standardIneq, Sum.elim_inr] at hc
    rw [hlam2v j]
    linear_combination hc

/-- **Property 7.13** of [quarteroni2000numerical] (Kuhn–Tucker conditions I and II). Let $l \le k$,
let $f$ and the $g_i$ be of class $C^1$ on $\mathbb{R}^n$, and let $x^*$ be a constrained local
maximizer of (7.52) that satisfies the constraint qualification
`QuarteroniSaccoSaleri.Chapter07.IsRegularNLP`. Then there is a multiplier
$\lambda^* \in \mathbb{R}^{m+n}$ such that $\nabla_x \mathcal{L}(x^*, \lambda^*) \le 0$
componentwise, with equality in every component $j \in J_>$, that is, with $x^*_j > 0$ (first
condition), and
$$(\nabla_x \mathcal{L}(x^*, \lambda^*))^T x^* = 0 \qquad \text{(second condition)}.$$

**Correction.** The book does not state a constraint qualification; it mentions one after
Property 7.14. Without one, the multiplier need not exist. The formal statement assumes
`QuarteroniSaccoSaleri.Chapter07.IsRegularNLP`.

In fact $\nabla_x \mathcal{L}(x^*, \lambda^*) = 0$ by
`QuarteroniSaccoSaleri.Chapter07.exists_kuhnTucker`, which is stronger than the first condition. -/
theorem property_7_13 (hlk : l ≤ k) (hreg : IsRegularNLP g b l k xstar)
    (hmax : IsLocalMaxOn f (feasibleRegion g b l k) xstar) (hf : ContDiff ℝ 1 f)
    (hg : ∀ i, ContDiff ℝ 1 (g i)) :
    ∃ lam : (Fin m → ℝ) × EuclideanSpace ℝ (Fin n),
      (∀ j, gradient (fun y => nonlinearLagrangian f g b y lam) xstar j ≤ 0) ∧
        (∀ j, 0 < xstar j → gradient (fun y => nonlinearLagrangian f g b y lam) xstar j = 0) ∧
        ⟪gradient (fun y => nonlinearLagrangian f g b y lam) xstar, xstar⟫_ℝ = 0 := by
  obtain ⟨lam, hgrad, -, -, -, -, -⟩ := exists_kuhnTucker hlk hreg hmax hf hg
  exact ⟨lam, fun j => by rw [hgrad]; simp, fun j _ => by rw [hgrad]; simp,
    by rw [hgrad, inner_zero_left]⟩

/-- **Property 7.14** of [quarteroni2000numerical] (Kuhn–Tucker conditions III and IV). Under the
hypotheses of Property 7.13, the partial derivatives $\partial \mathcal{L} / \partial \lambda_i
(x^*, \lambda^*) = b_i - g_i(x^*)$ are $\ge 0$ for $i \le l$, $\le 0$ for $l < i \le k$ and
$= 0$ for $k < i \le m$ (third condition, which is the feasibility of $x^*$). Moreover there is
a multiplier $\lambda^*$ that satisfies the first and second conditions of Property 7.13 and the
complementarity condition
$$(\nabla_\lambda \mathcal{L}(x^*, \lambda^*))^T \lambda^* = \sum_{i=1}^m \lambda^*_{1,i} (b_i -
  g_i(x^*)) - \langle \lambda^*_2, x^* \rangle = 0 \qquad \text{(fourth condition)}.$$

**Typo.** The book prints the fourth condition as $(\nabla_\lambda \mathcal{L})^T x^* = 0$. This
cannot be read as it stands, because $\nabla_\lambda \mathcal{L} \in \mathbb{R}^{m+n}$ and
$x^* \in \mathbb{R}^n$ have different lengths. The complementarity condition of the Kuhn–Tucker
conditions is $(\nabla_\lambda \mathcal{L})^T \lambda^* = 0$. -/
theorem property_7_14 (hlk : l ≤ k) (hreg : IsRegularNLP g b l k xstar)
    (hmax : IsLocalMaxOn f (feasibleRegion g b l k) xstar) (hf : ContDiff ℝ 1 f)
    (hg : ∀ i, ContDiff ℝ 1 (g i)) :
    ((∀ i : Fin m, (i : ℕ) < l → 0 ≤ b i - g i xstar) ∧
        (∀ i : Fin m, l ≤ (i : ℕ) → (i : ℕ) < k → b i - g i xstar ≤ 0) ∧
        ∀ i : Fin m, k ≤ (i : ℕ) → b i - g i xstar = 0) ∧
      ∃ lam : (Fin m → ℝ) × EuclideanSpace ℝ (Fin n),
        (∀ j, gradient (fun y => nonlinearLagrangian f g b y lam) xstar j ≤ 0) ∧
          (∀ j, 0 < xstar j → gradient (fun y => nonlinearLagrangian f g b y lam) xstar j = 0) ∧
          ⟪gradient (fun y => nonlinearLagrangian f g b y lam) xstar, xstar⟫_ℝ = 0 ∧
          ∑ i, lam.1 i * (b i - g i xstar) - ⟪lam.2, xstar⟫_ℝ = 0 := by
  have hfeas : xstar ∈ feasibleRegion g b l k := by
    rw [nonlinearProgram_toStandard g b hlk]
    exact Constrained.IsRegularPointIneq.mem_feasible hreg
  obtain ⟨hy1, hy2, hy3, hy4⟩ := hfeas
  obtain ⟨lam, hgrad, -, -, -, hc1, hc2⟩ := exists_kuhnTucker hlk hreg hmax hf hg
  refine ⟨⟨fun i hil => by linarith [hy1 i hil], fun i hli hik => by linarith [hy2 i hli hik],
    fun i hik => by rw [hy3 i hik]; ring⟩,
    lam, fun j => by rw [hgrad]; simp, fun j _ => by rw [hgrad]; simp,
    by rw [hgrad, inner_zero_left], ?_⟩
  rw [Finset.sum_eq_zero fun i _ => hc1 i, EuclideanSpace.real_inner_eq_sum,
    Finset.sum_eq_zero fun j _ => hc2 j, sub_zero]

/-- **Property 7.15** of [quarteroni2000numerical] (sufficiency of the Kuhn–Tucker conditions). Let
$C \subseteq \mathbb{R}^n$ contain the feasible region of (7.52) and lie in the nonnegative
orthant $\{x : x \ge 0\}$. Let $\lambda = (\lambda_1, \lambda_2) \in \mathbb{R}^m \times
\mathbb{R}^n$. Let $f$ be concave on $C$ (so $C$ is convex), let $g_i$ be convex on $C$ where
$\lambda_{1,i} > 0$ and concave on $C$ where $\lambda_{1,i} < 0$, and let $f$ and the $g_i$ be
differentiable at a feasible point $x^*$. Assume the signs $\lambda_{1,i} \ge 0$ for $i \le l$,
$\lambda_{1,i} \le 0$ for $l < i \le k$ and $\lambda_{2,j} \le 0$ for all $j$, and the
Kuhn–Tucker conditions I, II and IV:
$$\nabla_x \mathcal{L}(x^*, \lambda) \le 0, \qquad (\nabla_x \mathcal{L}(x^*, \lambda))^T x^* =
  0, \qquad \sum_{i=1}^m \lambda_{1,i} (b_i - g_i(x^*)) - \langle \lambda_2, x^* \rangle = 0.$$
Then $x^*$ is a global maximizer of $f$ on the feasible region.

**Correction.** The book leaves the signs of the multipliers out of its list of conditions. The
formal statement assumes them; `QuarteroniSaccoSaleri.Chapter07.exists_kuhnTucker` supplies
them.

**Reading.** The book assumes the concavity and convexity "in the feasible region", which
presupposes that the feasible region is convex. The formal statement uses a convex set $C$ that
contains the feasible region and lies in the nonnegative orthant: $C$ is the feasible region
when it is convex, and otherwise the orthant on which (7.52) is posed.

The proof applies `Constrained.isMinOn_of_lagrangian_convexOn` to $-f$. -/
theorem property_7_15 {C : Set (EuclideanSpace ℝ (Fin n))}
    {lam : (Fin m → ℝ) × EuclideanSpace ℝ (Fin n)} (hsub : feasibleRegion g b l k ⊆ C)
    (hCnonneg : ∀ y ∈ C, ∀ j, 0 ≤ y j) (hfeas : xstar ∈ feasibleRegion g b l k)
    (hconc : ConcaveOn ℝ C f) (hgconv : ∀ i, 0 < lam.1 i → ConvexOn ℝ C (g i))
    (hgconc : ∀ i, lam.1 i < 0 → ConcaveOn ℝ C (g i)) (hfd : DifferentiableAt ℝ f xstar)
    (hgd : ∀ i, DifferentiableAt ℝ (g i) xstar)
    (hs1 : ∀ i : Fin m, (i : ℕ) < l → 0 ≤ lam.1 i)
    (hs2 : ∀ i : Fin m, l ≤ (i : ℕ) → (i : ℕ) < k → lam.1 i ≤ 0) (hs3 : ∀ j, lam.2 j ≤ 0)
    (hI : ∀ j, gradient (fun y => nonlinearLagrangian f g b y lam) xstar j ≤ 0)
    (hII : ⟪gradient (fun y => nonlinearLagrangian f g b y lam) xstar, xstar⟫_ℝ = 0)
    (hIV : ∑ i, lam.1 i * (b i - g i xstar) - ⟪lam.2, xstar⟫_ℝ = 0) :
    IsMaxOn f (feasibleRegion g b l k) xstar := by
  have hC : Convex ℝ C := hconc.1
  obtain ⟨hx1, hx2, hx3, hx4⟩ := hfeas
  have hterm1 : ∀ i : Fin m, 0 ≤ lam.1 i * (b i - g i xstar) := by
    intro i
    rcases lt_or_ge (i : ℕ) k with hik | hik
    · rcases lt_or_ge (i : ℕ) l with hil | hil
      · nlinarith [hs1 i hil, hx1 i hil]
      · nlinarith [hs2 i hil hik, hx2 i hil hik]
    · rw [hx3 i hik]
      simp
  have hterm2 : ∀ j, lam.2 j * xstar j ≤ 0 := fun j => by nlinarith [hs3 j, hx4 j]
  have hzero : ∑ i, lam.1 i * (b i - g i xstar) = 0 ∧ ∑ j, lam.2 j * xstar j = 0 := by
    have hA : 0 ≤ ∑ i, lam.1 i * (b i - g i xstar) := Finset.sum_nonneg fun i _ => hterm1 i
    have hB : ∑ j, lam.2 j * xstar j ≤ 0 := Finset.sum_nonpos fun j _ => hterm2 j
    rw [EuclideanSpace.real_inner_eq_sum] at hIV
    exact ⟨by linarith, by linarith⟩
  have hc1 : ∀ i, lam.1 i * (b i - g i xstar) = 0 := fun i =>
    (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hterm1 i).1 hzero.1 i (Finset.mem_univ i)
  have hc2 : ∀ j, lam.2 j * xstar j = 0 := fun j =>
    (Finset.sum_eq_zero_iff_of_nonpos fun j _ => hterm2 j).1 hzero.2 j (Finset.mem_univ j)
  have hnegf : ConvexOn ℝ C (fun y => -f y) := hconc.neg
  have hmin : IsMinOn (fun y => -f y) (feasibleRegion g b l k) xstar := by
    refine Constrained.isMinOn_of_lagrangian_convexOn (C := C)
      (f' := fun y => -fderiv ℝ f y)
      (g := Sum.elim (fun i (y : EuclideanSpace ℝ (Fin n)) => g i y - b i)
        fun j (y : EuclideanSpace ℝ (Fin n)) => -y j)
      (g' := Sum.elim (fun i (y : EuclideanSpace ℝ (Fin n)) => fderiv ℝ (g i) y)
        fun j (_ : EuclideanSpace ℝ (Fin n)) => -EuclideanSpace.proj (𝕜 := ℝ) j)
      (μ := Sum.elim (fun i => lam.1 i) fun j => -lam.2 j)
      hsub ⟨hx1, hx2, hx3, hx4⟩ hnegf ?_ hfd.hasFDerivAt.neg ?_ ?_ ?_ ?_
    · rintro (i | j)
      · simp only [Sum.elim_inl]
        rcases lt_trichotomy (lam.1 i) 0 with h | h | h
        · have he : (fun y => lam.1 i * (g i y - b i))
              = fun y => (-lam.1 i) • (-(fun y => g i y + -b i)) y := by
            funext y
            simp only [Pi.neg_apply, smul_eq_mul]
            ring
          rw [he]
          exact ((hgconc i h).add_const (-b i)).neg.smul (neg_nonneg.2 h.le)
        · have he : (fun y => lam.1 i * (g i y - b i)) = fun _ => (0 : ℝ) := by
            funext y
            rw [h]
            ring
          rw [he]
          exact convexOn_const 0 hC
        · have he : (fun y => lam.1 i * (g i y - b i)) = fun y => lam.1 i • (g i y + -b i) := by
            funext y
            simp only [smul_eq_mul]
            ring
          rw [he]
          exact ((hgconv i h).add_const (-b i)).smul h.le
      · simp only [Sum.elim_inr]
        have he : (fun y : EuclideanSpace ℝ (Fin n) => -lam.2 j * -y j)
            = fun y => lam.2 j * y j := by
          funext y
          ring
        rw [he]
        exact convexOn_const_mul_coord hC (lam.2 j) j
    · rintro (i | j)
      · exact (hgd i).hasFDerivAt.sub_const (b i)
      · exact (EuclideanSpace.proj (𝕜 := ℝ) j).hasFDerivAt.neg
    · rintro y ⟨hz1, hz2, hz3, hz4⟩ (i | j)
      · simp only [Sum.elim_inl]
        rcases lt_or_ge (i : ℕ) k with hik | hik
        · rcases lt_or_ge (i : ℕ) l with hil | hil
          · nlinarith [hs1 i hil, hz1 i hil]
          · nlinarith [hs2 i hil hik, hz2 i hil hik]
        · rw [hz3 i hik]
          simp
      · simp only [Sum.elim_inr]
        nlinarith [hs3 j, hz4 j]
    · rintro (i | j)
      · simp only [Sum.elim_inl]
        linear_combination -hc1 i
      · simp only [Sum.elim_inr]
        linear_combination hc2 j
    · intro y hyC
      have h2 := inner_gradient_nonlinearLagrangian (b := b) hfd hgd lam (y - xstar)
      have h3 : ⟪gradient (fun y => nonlinearLagrangian f g b y lam) xstar, y - xstar⟫_ℝ
          = ⟪gradient (fun y => nonlinearLagrangian f g b y lam) xstar, y⟫_ℝ := by
        rw [inner_sub_right, hII, sub_zero]
      have h4 : ⟪gradient (fun y => nonlinearLagrangian f g b y lam) xstar, y⟫_ℝ ≤ 0 := by
        rw [EuclideanSpace.real_inner_eq_sum]
        exact Finset.sum_nonpos fun j _ => by nlinarith [hI j, hCnonneg y hyC j]
      have h5 : ∑ j : Fin n, -lam.2 j * -((y - xstar) j) = ⟪lam.2, y - xstar⟫_ℝ := by
        rw [EuclideanSpace.real_inner_eq_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [Fintype.sum_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, _root_.neg_apply, EuclideanSpace.coe_proj]
      linarith [h2, h3, h4, h5]
  refine isMaxOn_iff.2 fun y hy => ?_
  have h := isMinOn_iff.1 hmin y hy
  linarith

end NonlinearProgramming

/-! ### The penalty method and the augmented Lagrangian -/

section Penalty

variable {m : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
  {h : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}

/-- **Equation (7.53)** of [quarteroni2000numerical]. Let $f : \mathbb{R}^n \to \mathbb{R}$,
$h : \mathbb{R}^n \to \mathbb{R}^m$ and $\alpha \in \mathbb{R}$. The penalized Lagrangian is
$$\mathcal{L}_\alpha(x) = f(x) + \frac{1}{2} \alpha \|h(x)\|_2^2,$$
and $\mathcal{L}_\alpha(x) = f(x)$ when $h(x) = 0$. So on the constraint set, minimizing $f$ is
equivalent to minimizing $\mathcal{L}_\alpha$.

The penalized Lagrangian is the backbone's `Constrained.penalized f h α`. -/
theorem equation_7_53 (α : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    Constrained.penalized f h α x = f x + 1 / 2 * α * ‖h x‖ ^ 2 ∧
      (h x = 0 → Constrained.penalized f h α x = f x) :=
  ⟨rfl, fun hx => by simp [Constrained.penalized, hx]⟩

-- The book's `α_k` is "monotonically divergent"; the backbone's `Constrained.penalty_clusterPt`
-- needs only the divergence, so `hpos` and `hmono` are carried for fidelity.
set_option linter.unusedVariables false in
/-- **Property 7.16** of [quarteroni2000numerical]. Let $\Omega \subseteq \mathbb{R}^n$ be closed,
and let $f : \mathbb{R}^n \to \mathbb{R}$ and $h : \mathbb{R}^n \to \mathbb{R}^m$ be continuous
on $\Omega$. Let the penalty parameters $\alpha_k > 0$ be nondecreasing with
$\alpha_k \to \infty$ (the book's "monotonically divergent"). Let $x^* \in \Omega$ with
$h(x^*) = 0$ be a global minimizer of $f$ on $\{x \in \Omega : h(x) = 0\}$, and for each $k$ let
$x^*_k \in \Omega$ be a global minimizer of $\mathcal{L}_{\alpha_k}$ on $\Omega$, as in (7.54).
Then:

* every cluster point $\bar x$ of the sequence $(x^*_k)$ lies in $\Omega$, satisfies
  $h(\bar x) = 0$, and is a global minimizer of $f$ on $\{x \in \Omega : h(x) = 0\}$;
* if $x^*$ is the only global minimizer of $f$ on $\{x \in \Omega : h(x) = 0\}$ and the sequence
  $(x^*_k)$ is bounded (for instance, if $\Omega$ is compact), then $x^*_k \to x^*$.

**Correction.** The book asserts that $x^*_k \to x^*$ without further hypotheses. This fails
when the constrained problem has several minimizers.

The two parts are `Constrained.penalty_clusterPt` and `Constrained.tendsto_penalty_of_unique`.
The proof uses only $\alpha_k \to \infty$; the hypotheses $\alpha_k > 0$ and monotonicity follow
the book. -/
theorem property_7_16 {Ω : Set (EuclideanSpace ℝ (Fin n))} (hΩ : IsClosed Ω)
    (hf : ContinuousOn f Ω) (hh : ContinuousOn h Ω) {α : ℕ → ℝ} (hpos : ∀ k, 0 < α k)
    (hmono : Monotone α) (hdiv : Tendsto α atTop atTop) {xstar : EuclideanSpace ℝ (Fin n)}
    (hstar : xstar ∈ Ω ∧ h xstar = 0) (hmin : IsMinOn f {y | y ∈ Ω ∧ h y = 0} xstar)
    {xk : ℕ → EuclideanSpace ℝ (Fin n)} (hxk : ∀ k, xk k ∈ Ω)
    (hxmin : ∀ k, IsMinOn (Constrained.penalized f h (α k)) Ω (xk k)) :
    (∀ xbar, MapClusterPt xbar atTop xk →
        xbar ∈ Ω ∧ h xbar = 0 ∧ IsMinOn f {y | y ∈ Ω ∧ h y = 0} xbar) ∧
      ((∀ y ∈ Ω, h y = 0 → IsMinOn f {y | y ∈ Ω ∧ h y = 0} y → y = xstar) →
        Bornology.IsBounded (Set.range xk) → Tendsto xk atTop (𝓝 xstar)) :=
  ⟨fun xbar hcl => Constrained.penalty_clusterPt hΩ hf hh hdiv hstar hmin hxk hxmin hcl,
    fun huniq hbdd => Constrained.tendsto_penalty_of_unique hΩ hf hh hdiv hstar hmin huniq hxk
      hxmin hbdd⟩

/-- **Equation (7.55)** of [quarteroni2000numerical]. Let $f : \mathbb{R}^n \to \mathbb{R}$,
$h : \mathbb{R}^n \to \mathbb{R}^m$, $\alpha \in \mathbb{R}$ and $\lambda \in \mathbb{R}^m$. The
augmented Lagrangian is
$$\mathcal{G}_\alpha(x, \lambda) = f(x) + \lambda^T h(x) + \frac{1}{2} \alpha \|h(x)\|_2^2.$$
With $\lambda = 0$ it is the penalized Lagrangian (7.53). If $x^*$ is a global minimizer of $f$
on $\{x : h(x) = 0\}$, then $x^*$ minimizes $\mathcal{G}_\alpha(\cdot, \lambda)$ on
$\{x : h(x) = 0\}$ for every $\alpha$ and $\lambda$, because
$\mathcal{G}_\alpha(\cdot, \lambda) = f$ there.

The augmented Lagrangian is the backbone's `Constrained.augmented f h α λ`. -/
theorem equation_7_55 (α : ℝ) (l : EuclideanSpace ℝ (Fin m)) (x : EuclideanSpace ℝ (Fin n)) :
    Constrained.augmented f h α l x = f x + ⟪l, h x⟫_ℝ + 1 / 2 * α * ‖h x‖ ^ 2 ∧
      Constrained.augmented f h α 0 = Constrained.penalized f h α ∧
      ∀ xstar, h xstar = 0 → IsMinOn f {y | h y = 0} xstar →
        IsMinOn (Constrained.augmented f h α l) {y | h y = 0} xstar := by
  refine ⟨rfl, Constrained.augmented_zero f h α, fun xstar hx hstar =>
    isMinOn_iff.2 fun y hy => ?_⟩
  have hy' : h y = 0 := hy
  simp only [Constrained.augmented, hx, hy', inner_zero_right, norm_zero, add_zero]
  simpa using isMinOn_iff.1 hstar y hy

/-- **Property 7.16** of [quarteroni2000numerical], for the method of multipliers (7.56), as stated
in the text after (7.56). Let $\Omega \subseteq \mathbb{R}^n$ be closed, let $f$ and $h$ be
continuous on $\Omega$, and let $\alpha_k \to \infty$. Let $x^* \in \Omega$ with $h(x^*) = 0$ be
a global minimizer of $f$ on $\{x \in \Omega : h(x) = 0\}$. Let the multipliers
$\lambda_k \in \mathbb{R}^m$ be bounded, $\|\lambda_k\| \le \Lambda$, and for each $k$ let
$x^*_k \in \Omega$ be a global minimizer of $\mathcal{G}_{\alpha_k}(\cdot, \lambda_k)$ on
$\Omega$. Then every cluster point $\bar x$ of $(x^*_k)$ lies in $\Omega$, satisfies
$h(\bar x) = 0$, and is a global minimizer of $f$ on $\{x \in \Omega : h(x) = 0\}$.

The proof specializes `Constrained.augmented_clusterPt`. -/
theorem property_7_16_augmented {Ω : Set (EuclideanSpace ℝ (Fin n))} (hΩ : IsClosed Ω)
    (hf : ContinuousOn f Ω) (hh : ContinuousOn h Ω) {α : ℕ → ℝ} (hdiv : Tendsto α atTop atTop)
    {xstar : EuclideanSpace ℝ (Fin n)} (hstar : xstar ∈ Ω ∧ h xstar = 0)
    (hmin : IsMinOn f {y | y ∈ Ω ∧ h y = 0} xstar) {l : ℕ → EuclideanSpace ℝ (Fin m)} {Λ : ℝ}
    (hl : ∀ k, ‖l k‖ ≤ Λ) {xk : ℕ → EuclideanSpace ℝ (Fin n)} (hxk : ∀ k, xk k ∈ Ω)
    (hxmin : ∀ k, IsMinOn (Constrained.augmented f h (α k) (l k)) Ω (xk k))
    {xbar : EuclideanSpace ℝ (Fin n)} (hcl : MapClusterPt xbar atTop xk) :
    xbar ∈ Ω ∧ h xbar = 0 ∧ IsMinOn f {y | y ∈ Ω ∧ h y = 0} xbar :=
  Constrained.augmented_clusterPt hΩ hf hh hdiv hstar hmin hl hxk hxmin hcl

end Penalty

/-! ### Example 7.7 -/

section Example77

/-- **Example 7.7** of [quarteroni2000numerical]. Let $f(x) = -x^4$ on $\mathbb{R}$ with the
constraint $h(x) = x = 0$, and let $\alpha, \lambda \in \mathbb{R}$. The constrained problem has
the solution $x^* = 0$. The augmented Lagrangian is
$$\mathcal{G}_\alpha(x, \lambda) = -x^4 + \lambda x + \frac{1}{2} \alpha x^2,$$
and it has no global minimizer on $\mathbb{R}$, because it tends to $-\infty$. So problem (7.56)
has no solution.

**Reading.** The book says that $\mathcal{G}_\alpha$ "no longer admits a minimum at $x = 0$" for
any $\alpha_k \neq 0$. This is read as the absence of a global minimizer: for $\lambda = 0$ and
$\alpha > 0$ the point $0$ is a strict local minimizer, by
`QuarteroniSaccoSaleri.Chapter07.example_7_7_isLocalMin`. -/
theorem example_7_7 (α l : ℝ) :
    IsMinOn (fun x : ℝ => -x ^ 4) {x | x = 0} 0 ∧
      (∀ x, Constrained.augmented (fun x : ℝ => -x ^ 4) (fun x : ℝ => x) α l x
        = -x ^ 4 + l * x + 1 / 2 * α * x ^ 2) ∧
      ¬ ∃ x₀, IsMinOn (Constrained.augmented (fun x : ℝ => -x ^ 4) (fun x : ℝ => x) α l) univ
        x₀ := by
  have hinner : ∀ a b : ℝ, ⟪a, b⟫_ℝ = a * b := fun a b => by simp [mul_comm]
  refine ⟨isMinOn_iff.2 fun x hx => by rw [show x = 0 from hx], fun x => ?_,
    fun ⟨x₀, hx₀⟩ => ?_⟩
  · simp only [Constrained.augmented, hinner, Real.norm_eq_abs, sq_abs]
  · -- a point far out is below `x₀`
    set S : ℝ := |x₀| + |l| + |α| + 1 with hS
    have hS1 : 1 ≤ S := by rw [hS]; linarith [abs_nonneg x₀, abs_nonneg l, abs_nonneg α]
    have hx₀S : |x₀| ≤ S := by rw [hS]; linarith [abs_nonneg l, abs_nonneg α]
    have hlS : |l| ≤ S := by rw [hS]; linarith [abs_nonneg x₀, abs_nonneg α]
    have hαS : |α| ≤ S := by rw [hS]; linarith [abs_nonneg x₀, abs_nonneg l]
    have hS2' : 1 ≤ S ^ 2 := by nlinarith
    have hS2 : S ^ 2 ≤ S ^ 4 := by
      calc S ^ 2 = S ^ 2 * 1 := by ring
        _ ≤ S ^ 2 * S ^ 2 := mul_le_mul_of_nonneg_left hS2' (sq_nonneg S)
        _ = S ^ 4 := by ring
    have hS3 : S ^ 3 ≤ S ^ 4 := by
      calc S ^ 3 = S ^ 3 * 1 := by ring
        _ ≤ S ^ 3 * S := mul_le_mul_of_nonneg_left hS1 (by positivity)
        _ = S ^ 4 := by ring
    have hT := isMinOn_iff.1 hx₀ (2 * S) (mem_univ _)
    simp only [Constrained.augmented, Real.norm_eq_abs, sq_abs, hinner] at hT
    -- `g(x₀) ≥ -3 S⁴` and `g(2S) ≤ -8 S⁴`
    have h1 : -x₀ ^ 4 + l * x₀ + 1 / 2 * α * x₀ ^ 2 ≥ -3 * S ^ 4 := by
      have ha : x₀ ^ 4 ≤ S ^ 4 := by
        have := pow_le_pow_left₀ (abs_nonneg x₀) hx₀S 4
        rwa [pow_abs, abs_of_nonneg (by positivity)] at this
      have hb : l * x₀ ≥ -(S * S) := by
        have := neg_abs_le (l * x₀)
        rw [abs_mul] at this
        nlinarith [abs_nonneg l, abs_nonneg x₀]
      have hc : 1 / 2 * α * x₀ ^ 2 ≥ -(S * S ^ 2) := by
        have h2 : x₀ ^ 2 ≤ S ^ 2 := by
          have := pow_le_pow_left₀ (abs_nonneg x₀) hx₀S 2
          rwa [pow_abs, abs_of_nonneg (by positivity)] at this
        have h3 := neg_abs_le α
        nlinarith [sq_nonneg x₀, abs_nonneg α]
      nlinarith
    have h2 : -(2 * S) ^ 4 + l * (2 * S) + 1 / 2 * α * (2 * S) ^ 2 ≤ -8 * S ^ 4 := by
      have hb : l * (2 * S) ≤ 2 * S * S := by nlinarith [le_abs_self l]
      have hc : 1 / 2 * α * (2 * S) ^ 2 ≤ 2 * S * S ^ 2 := by nlinarith [le_abs_self α]
      nlinarith
    nlinarith

/-- **Example 7.7** of [quarteroni2000numerical], the local statement. Let $\alpha > 0$. Then $0$ is
a strict local minimizer of $\mathcal{G}_\alpha(x, 0) = -x^4 + \frac{1}{2} \alpha x^2$: there is
$\delta > 0$ with $\mathcal{G}_\alpha(0, 0) < \mathcal{G}_\alpha(x, 0)$ for all $x$ with
$0 < |x| < \delta$.

The reason is $\mathcal{G}_\alpha''(0) = \alpha > 0$. What fails at $0$ is the global
minimality, by `QuarteroniSaccoSaleri.Chapter07.example_7_7`. -/
theorem example_7_7_isLocalMin {α : ℝ} (hα : 0 < α) :
    ∃ δ > 0, ∀ x : ℝ, |x| < δ → x ≠ 0 →
      Constrained.augmented (fun x : ℝ => -x ^ 4) (fun x : ℝ => x) α 0 0
        < Constrained.augmented (fun x : ℝ => -x ^ 4) (fun x : ℝ => x) α 0 x := by
  refine ⟨min 1 (α / 2), lt_min one_pos (by positivity), fun x hx hx0 => ?_⟩
  simp only [Constrained.augmented, Real.norm_eq_abs, sq_abs, inner_zero_left, add_zero]
  have hx1 : |x| < 1 := lt_of_lt_of_le hx (min_le_left _ _)
  have hxα : |x| < α / 2 := lt_of_lt_of_le hx (min_le_right _ _)
  have hxpos : 0 < |x| := abs_pos.2 hx0
  have hsq : x ^ 2 < α / 2 := by
    have : x ^ 2 = |x| * |x| := by rw [← sq_abs, sq]
    nlinarith
  have hx2 : 0 < x ^ 2 := by positivity
  nlinarith

end Example77

/-! ### Property 7.17: the Hessian of the augmented Lagrangian -/

section Property717

variable {m : ℕ}

/-- **Property 7.17** of [quarteroni2000numerical], condition 3 from condition 2. Let
$f : \mathbb{R}^n \to \mathbb{R}$ and $h : \mathbb{R}^n \to \mathbb{R}^m$ be of class $C^2$ near
$x^*$, let $h(x^*) = 0$, and let $\lambda^* \in \mathbb{R}^m$ be arbitrary. Let
$H_{\mathcal{G}_\alpha}(x^*, \lambda^*)$ be the Hessian matrix in $x$ of
$\mathcal{G}_\alpha(\cdot, \lambda^*)$ at $x^*$, so that $\mathcal{G}_0(\cdot, \lambda^*) = f +
\lambda^{*T} h$ is the Lagrangian. Assume condition 2:
$z^T H_{\mathcal{G}_0}(x^*, \lambda^*) z > 0$ for every $z \neq 0$ with $J_h(x^*)^T z = 0$, that
is, $h'(x^*) z = 0$. Then condition 3 holds for all large parameters: there is $\bar\alpha > 0$
such that $z^T H_{\mathcal{G}_\alpha}(x^*, \lambda^*) z > 0$ for all $\alpha \ge \bar\alpha$ and
all $z \neq 0$.

**Generalization.** The book lists condition 3 as a separate hypothesis of Property 7.17, and
assumes $f$ and $h$ of class $C^2$ on a ball $B(x^*; R)$. Condition 3 follows from condition 2,
and $C^2$ near $x^*$ suffices.

At a zero of $h$ the Hessian is $H_{\mathcal{G}_\alpha}(x^*, \lambda^*) = H_{\mathcal{G}_0}(x^*,
\lambda^*) + \alpha J_h(x^*) J_h(x^*)^T$, where the columns of $J_h(x^*)$ are the gradients
$\nabla h_i(x^*)$, and the result is Debreu's lemma (Lemma 1.25 of Bertsekas) applied to this
sum. The proof specializes `Constrained.exists_forall_pos_fderiv_fderiv_augmented`, through
`Constrained.exists_forall_pos_add_mul_sq_norm_of_pos_on_ker` and
`Constrained.fderiv_fderiv_augmented_apply`. -/
theorem property_7_17_debreu {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {h : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)} {xstar : EuclideanSpace ℝ (Fin n)}
    {l : EuclideanSpace ℝ (Fin m)} (hfeas : h xstar = 0) (hf : ContDiffAt ℝ 2 f xstar)
    (hh : ContDiffAt ℝ 2 h xstar)
    (hpos : ∀ z, z ≠ 0 → fderiv ℝ h xstar z = 0 →
      0 < ⟪toEuclideanLin (hessianMatrix (Constrained.augmented f h 0 l) xstar) z, z⟫_ℝ) :
    ∃ ᾱ > 0, ∀ α, ᾱ ≤ α → ∀ z, z ≠ 0 →
      0 < ⟪toEuclideanLin (hessianMatrix (Constrained.augmented f h α l) xstar) z, z⟫_ℝ := by
  have hG : ∀ α, ContDiffAt ℝ 2 (Constrained.augmented f h α l) xstar := fun α =>
    (hf.add (ContDiffAt.inner ℝ contDiffAt_const hh)).add
      (contDiffAt_const.mul (ContDiffAt.norm_sq ℝ hh))
  have hGd : ∀ α, DifferentiableAt ℝ (fderiv ℝ (Constrained.augmented f h α l)) xstar := fun α =>
    ((hG α).fderiv_right (m := 1) le_rfl).differentiableAt one_ne_zero
  have hpos' : ∀ z, z ≠ 0 → fderiv ℝ h xstar z = 0 →
      0 < fderiv ℝ (fderiv ℝ (Constrained.augmented f h 0 l)) xstar z z := fun z hz hAz => by
    rw [← inner_toEuclideanLin_hessianMatrix (hGd 0)]
    exact hpos z hz hAz
  obtain ⟨α₀, hα₀⟩ := Constrained.exists_forall_pos_fderiv_fderiv_augmented hfeas hf hh l hpos'
  refine ⟨max α₀ 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun α hα z hz => ?_⟩
  rw [inner_toEuclideanLin_hessianMatrix (hGd α)]
  exact hα₀ α ((le_max_left _ _).trans hα) z hz

end Property717

end QuarteroniSaccoSaleri.Chapter07
