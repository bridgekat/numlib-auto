/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Distribution.Distribution
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Numlib.Variational.EllipticInterval
import Numlib.FiniteElement.Interval
import NumlibSurface.QuarteroniSaccoSaleri.Chapter12.Section03

/-!
# Quarteroni, Sacco and Saleri, Section 12.4: The Galerkin method

This module formalizes Section 12.4 of [quarteroni2000numerical]. The two-point boundary value
problem (12.41) is $-(\alpha u')' + \beta u' + \gamma u = f$ on $(0, 1)$ with $u(0) = u(1) = 0$.
Multiplication by a test function and integration by parts give the weak formulation (12.43): find
$u \in V = H^1_0(0, 1)$ (12.42) with $a(u, v) = (f, v)$ for every $v \in V$, where
$$a(u, v) = \int_0^1 \alpha u' v' + \int_0^1 \beta u' v + \int_0^1 \gamma u v$$
is the bilinear form (12.44). The Galerkin method (12.46) poses the same equation in a
finite-dimensional subspace $V_h \subseteq V$. In a basis $\varphi_1, \ldots, \varphi_N$ of $V_h$ it
is the linear system (12.47)–(12.48) with the stiffness matrix
$(A_G)_{ij} = a(\varphi_j, \varphi_i)$. The analysis of Section 12.4.4 uses the seminorm
$|v|_{H^1(0,1)} = \|v'\|_{L^2(0,1)}$ (12.49). Coercivity gives the stability estimate (12.51) and
Theorem 12.3, $|u - u_h|_{H^1(0,1)} \le C \min_{w_h \in V_h} |u - w_h|_{H^1(0,1)}$ with $C =
\alpha_0^{-1}(\|\alpha\|_\infty + C_P^2 \|\gamma\|_\infty)$. The Lax–Milgram lemma (12.54)–(12.55)
and Céa's lemma (12.56) are the abstract forms of these results in a Hilbert space.

The module also covers the distributional derivative (12.45) with the Heaviside example, the finite
element spaces $X_h^{k,0}$ (12.57), the convergence estimates (12.58)–(12.60) for $k = 1$, the
linear and quadratic shape functions (12.61)–(12.66), the structure and the condition number of the
finite element stiffness matrix $A_{fe}$, Example 12.1, and the spectral method (12.68)–(12.69) as a
generalized Galerkin method. The proofs specialize `Numlib.Variational.EllipticInterval`,
`Numlib.Variational.Galerkin` and `Numlib.FiniteElement.Interval`.

## Main definitions

* (12.42), `QuarteroniSaccoSaleri.Chapter12.equation_12_42`: the space $V = H^1_0(0, 1)$.
* (12.44), `QuarteroniSaccoSaleri.Chapter12.equation_12_44`: the bilinear form $a(u, v)$.
* (12.45), `QuarteroniSaccoSaleri.Chapter12.equation_12_45`: the distributional derivative of order
  $k$ on $(0, 1)$.
* Example after (12.45), `QuarteroniSaccoSaleri.Chapter12.heaviside`: the Heaviside function $H$.
* Section 12.4.2, `QuarteroniSaccoSaleri.Chapter12.regularDistribution`: the distribution
  $\varphi \mapsto \int \varphi f$ of a locally integrable function $f$ on $\mathbb{R}$.
* (12.46), `QuarteroniSaccoSaleri.Chapter12.equation_12_46`: the Galerkin problem in a subspace
  $V_h$.
* (12.48), `QuarteroniSaccoSaleri.Chapter12.equation_12_48_matrix`: the stiffness matrix $A_G$ in a
  family of trial functions.
* (12.49), `QuarteroniSaccoSaleri.Chapter12.equation_12_49`: the seminorm $|v|_{H^1(0,1)}$.
* (12.57), `QuarteroniSaccoSaleri.Chapter12.equation_12_57`: the finite element space $X_h^{k,0}$.
* (12.61), `QuarteroniSaccoSaleri.Chapter12.equation_12_61`: the piecewise linear shape functions
  $\varphi_i$.
* (12.61), `QuarteroniSaccoSaleri.Chapter12.equation_12_61_basis`: the basis of $X_h^1$ formed by
  the shape functions.
* (12.62), `QuarteroniSaccoSaleri.Chapter12.equation_12_62`: the affine map of the reference
  interval onto an element.
* (12.63)–(12.64), `QuarteroniSaccoSaleri.Chapter12.equation_12_63`: the piecewise quadratic shape
  functions.
* (12.63)–(12.64), `QuarteroniSaccoSaleri.Chapter12.equation_12_63_basis`: the basis of $X_h^2$
  formed by the quadratic shape functions.
* Example 12.1, `QuarteroniSaccoSaleri.Chapter12.example_12_1_solution`: the function
  $u(x) = u_0 \cosh(m(L - x)) / \cosh(mL)$.
* (12.68), `QuarteroniSaccoSaleri.Chapter12.equation_12_68`: the spectral method as a generalized
  Galerkin problem.
* (12.69), `QuarteroniSaccoSaleri.Chapter12.equation_12_69`: the discrete bilinear form $a_n$.
* Section 12.3, `QuarteroniSaccoSaleri.Chapter12.polyZero`: the space $\mathbb{P}_n^0$ of
  polynomials of degree at most $n$ that vanish at $\pm 1$.

## Main results

* (12.43), `QuarteroniSaccoSaleri.Chapter12.equation_12_43`: a classical solution of (12.41) is a
  weak solution.
* Exercise 12.12, `QuarteroniSaccoSaleri.Chapter12.exercise_12_12`: the weak formulation with
  nonhomogeneous Neumann conditions.
* (12.45), `QuarteroniSaccoSaleri.Chapter12.equation_12_45_apply`: $\langle T^{(k)}, \varphi
  \rangle = (-1)^k \langle T, \varphi^{(k)} \rangle$.
* Example after (12.45), `QuarteroniSaccoSaleri.Chapter12.equation_12_45_heaviside`: the
  distributional derivative of $H$ is the Dirac mass $\delta$ at $0$.
* (12.47)–(12.48), `QuarteroniSaccoSaleri.Chapter12.equation_12_48`: the Galerkin problem is the
  linear system $A_G \xi = f_G$.
* Section 12.4.4, `QuarteroniSaccoSaleri.Chapter12.equation_12_50`: coercivity
  $\alpha_0 |v|^2_{H^1} \le a(v, v)$ for $\beta = 0$ and $\gamma \ge 0$.
* (12.51), `QuarteroniSaccoSaleri.Chapter12.equation_12_51`: the stability estimate
  $|u_h|_{H^1} \le (C_P / \alpha_0) \|f\|_{L^2}$.
* (12.53), `QuarteroniSaccoSaleri.Chapter12.equation_12_53`: Galerkin orthogonality.
* Theorem 12.3, `QuarteroniSaccoSaleri.Chapter12.theorem_12_3`: the quasi-optimal error estimate
  (12.52).
* (12.54)–(12.55), `QuarteroniSaccoSaleri.Chapter12.laxMilgram_lemma`: the Lax–Milgram lemma.
* (12.56), `QuarteroniSaccoSaleri.Chapter12.equation_12_56`: Céa's lemma.
* Section 12.4.4, `QuarteroniSaccoSaleri.Chapter12.galerkinMatrix_posDef`: the stiffness matrix of a
  symmetric coercive form is positive definite.
* (12.58), `QuarteroniSaccoSaleri.Chapter12.equation_12_58`: the finite element error is bounded by
  the interpolation error.
* Property 12.1, `QuarteroniSaccoSaleri.Chapter12.property_12_1`: the $H^1$ estimate (12.59) for
  $k = 1$.
* Property 12.1, `QuarteroniSaccoSaleri.Chapter12.property_12_1_l2`: the $L^2$ estimate (12.60) for
  $k = 1$.
* (12.61), `QuarteroniSaccoSaleri.Chapter12.equation_12_61_apply_node`:
  $\varphi_i(x_j) = \delta_{ij}$.
* Section 12.4.5, `QuarteroniSaccoSaleri.Chapter12.equation_12_61_support`: $\varphi_i$ vanishes
  outside $I_{i-1} \cup I_i$.
* Section 12.4.5, `QuarteroniSaccoSaleri.Chapter12.equation_12_62_shape`: on an element, the shape
  functions are the reference shape functions composed with the reference coordinate.
* (12.63)–(12.64), `QuarteroniSaccoSaleri.Chapter12.equation_12_63_apply_node`: the quadratic shape
  functions satisfy $\varphi_i(x_j) = \delta_{ij}$.
* Section 12.4.5, `QuarteroniSaccoSaleri.Chapter12.equation_12_63_support`: the support of a
  quadratic shape function.
* (12.65), `QuarteroniSaccoSaleri.Chapter12.equation_12_65`: the reference quadratic shape
  functions, when the interior nodes are midpoints.
* (12.57), `QuarteroniSaccoSaleri.Chapter12.equation_12_63_mem_zero`: the interior quadratic shape
  functions lie in $X_h^{2,0}$.
* (12.66), `QuarteroniSaccoSaleri.Chapter12.equation_12_66`: the hierarchical functions are linearly
  independent.
* Section 12.4.5, `QuarteroniSaccoSaleri.Chapter12.equation_12_61_stiffness`: $A_{fe}$ is
  tridiagonal for $k = 1$.
* Section 12.4.5, `QuarteroniSaccoSaleri.Chapter12.equation_12_61_stiffness_tridiagonal`: $A_{fe}$
  is tridiagonal in the interior shape function basis of $X_h^{1,0}$.
* Section 12.4.5, `QuarteroniSaccoSaleri.Chapter12.equation_12_61_stiffness_condNumber`:
  $K_2(A_{fe}) = \cot^2(\pi h / 2)$ for the model problem on a uniform mesh.
* Example 12.1, `QuarteroniSaccoSaleri.Chapter12.example_12_1`: the exact solution of (12.67).
* (12.68)–(12.69), `QuarteroniSaccoSaleri.Chapter12.equation_12_69_model`: for $-u'' = f$,
  $a_n(p, q) = (-p'', q)_n$ on $\mathbb{P}_n^0$.
* Section 12.4.7, `QuarteroniSaccoSaleri.Chapter12.equation_12_68_eq_collocation`: for $-u'' = f$,
  the spectral method (12.68) is the collocation method (12.36).

## Conventions

* $H^1(0, 1)$ is `SobolevInterval 1 0 1`, and $H^1_0(0, 1)$ is `SobolevIntervalZero 0 1`. The value
  $v(c)$ of $v \in H^1(0, 1)$ at a point is the value of its continuous representative,
  `SobolevInterval.rep v c`.
* The coefficients $\alpha, \beta, \gamma$ are elements of $L^\infty(0, 1)$ and the datum $f$ is an
  element of $L^2(0, 1)$. The form and the load functional are `EllipticInterval.form 0 1 α β γ` and
  `EllipticInterval.load 0 1 f`. A norm $\|\alpha\|_\infty$ is the norm of $L^\infty(0, 1)$.
* The Poincaré constant on $(0, 1)$ is $C_P = 1/\sqrt{2}$.
* A partition $0 = x_0 < x_1 < \cdots < x_n = 1$ is `IsIntervalPartition 0 1 n x` with `x : ℕ → ℝ`,
  and the elements are $I_i = [x_i, x_{i+1}]$.

## Implementation notes

* A classical solution $u \in C^2([0, 1])$ is an element of `ContDiffMapIcc zero_le_one 2`. Its
  element of $H^1(0, 1)$ is `EllipticInterval.ofContDiffMapIcc zero_lt_one u`.
* The space $\mathbb{P}_n^0$ of the spectral method is a submodule of the polynomial ring
  $\mathbb{R}[X]$, not of $H^1(0, 1)$, because the discrete form (12.69) evaluates derivatives at
  the Gauss–Lobatto nodes. The method (12.68) is therefore a `IsGeneralizedGalerkinSolution`, not a
  `IsGalerkinSolution`.

## Deviations from the source

* **Equations (12.42)–(12.45) and Exercise 12.12** (reading). The test space uses weak
  derivatives and zero traces in accordance with (12.42). The preceding piecewise-smooth
  description is narrower. The weak form uses essentially bounded coefficients. The classical-
  to-weak theorems assume $C^1$ diffusion, and the lifting identity allows any $H^1$ lift.
  Exercise 12.12 gives the nonhomogeneous Neumann formula. Its final mixed-boundary request is
  not included.
* **Equations (12.46)–(12.56)** (reading). The Galerkin predicate accepts any trial submodule of
  $H^1$. `equation_12_53` requires the exact equation on all of $H^1$, whereas the printed
  Dirichlet statement needs it only on $H_0^1$ with $V_h\subseteq H_0^1$. Coercivity and
  stability use almost-everywhere coefficient inequalities. The abstract estimates accept
  arbitrary trial submodules and Céa's bound uses a distance infimum. `galerkinMatrix_posDef`
  assumes symmetry because Lean's `Matrix.PosDef` includes it.
* **Equations (12.57)–(12.60)** (partial). The dimension theorem concerns the full space, of
  dimension $nk+1$. The text states dimension $nk-1$ for its zero-trace subspace.
  `equation_12_58` combines comparison and interpolation for $k=1$. The estimates in Property
  12.1 treat $k=1$ and $\beta=0$, and the $L^2$ estimate assumes a bound on the $C^1$ diffusion
  derivative.
* **Equations (12.61)–(12.66) and the stiffness matrix** (reading). The nodal basis formulas
  admit a single panel, and the quadratic shape functions allow any interior node in each panel.
  The reference mapping of (12.65) uses the midpoint hypothesis. The condition number formula is
  exact for uniform linear elements and the unit-coefficient model, while the source gives an
  asymptotic estimate. The hierarchical declaration proves independence of its three functions.
* **Example 12.1 and equations (12.68)–(12.69)** (reading). The rod identity applies on the real
  line using the algebraic parameter relation. It verifies the exact solution. The spectral form
  and load accept arbitrary weighted nodes, and the collocation equivalence uses the
  Legendre–Lobatto hypotheses and the corrected endpoints $\pm1$.

## Not formalized

* **Property 12.1 for $k \ge 2$.** Only the case $k = 1$, $s = 2$ of the estimates (12.59)–(12.60)
  is formalized.
-/

open Set Matrix MeasureTheory SobolevInterval EllipticInterval

namespace QuarteroniSaccoSaleri.Chapter12

/-! ### The weak formulation (12.41)–(12.44) -/

/-- **Equation (12.42)** of [quarteroni2000numerical]. The space $V = H^1_0(0, 1)$, a subspace of
$H^1(0, 1)$. It consists of the $v \in H^1(0, 1)$ with $v(0) = v(1) = 0$.

The definition is `SobolevIntervalZero 0 1`. The description by the boundary values is
`QuarteroniSaccoSaleri.Chapter12.equation_12_42_iff`.

**Reading.** Uses the full weak $H_0^1$ space with endpoint traces of the continuous
representative. The preceding prose describes piecewise-continuous first derivatives. -/
noncomputable abbrev equation_12_42 : Submodule ℝ (SobolevInterval 1 0 1) :=
  SobolevIntervalZero 0 1

/-- An element $u \in H^1(0, 1)$ lies in the space $V$ of (12.42) if and only if its continuous
representative vanishes at $0$ and at $1$.

**Reading.** Uses the full weak $H_0^1$ space with endpoint traces of the continuous
representative. The preceding prose describes piecewise-continuous first derivatives. -/
theorem equation_12_42_iff (u : SobolevInterval 1 0 1) :
    u ∈ equation_12_42 ↔ toContinuousMap zero_lt_one u ⟨0, left_mem_Icc.2 zero_le_one⟩ = 0 ∧
      toContinuousMap zero_lt_one u ⟨1, right_mem_Icc.2 zero_le_one⟩ = 0 :=
  mem_sobolevIntervalZero_iff zero_lt_one u

/-- **Equation (12.44)** of [quarteroni2000numerical]. For coefficients
$\alpha, \beta, \gamma \in L^\infty(0, 1)$, the bilinear form on $H^1(0, 1)$
$$a(u, v) = \int_0^1 \alpha u' v' \, dx + \int_0^1 \beta u' v \, dx + \int_0^1 \gamma u v \,
  dx.$$

The form is the bounded bilinear form `EllipticInterval.form 0 1 α β γ`. Its integral expression
is `QuarteroniSaccoSaleri.Chapter12.equation_12_44_apply`.

**Generalization.** Uses essentially bounded coefficient classes and weak derivatives of
arbitrary $H^1$ arguments. -/
noncomputable abbrev equation_12_44 (α β γ : Lp ℝ ⊤ (volume.restrict (Ioo (0 : ℝ) 1))) :
    SesqForm ℝ (SobolevInterval 1 0 1) :=
  EllipticInterval.form 0 1 α β γ

/-- The bilinear form (12.44) is the integral $a(u, v) = \int_0^1 (\alpha u' v' + \beta u' v +
\gamma u v) \, dx$, where $u'$ and $v'$ are the weak derivatives.

**Generalization.** Uses essentially bounded coefficient classes and weak derivatives of
arbitrary $H^1$ arguments. -/
theorem equation_12_44_apply (α β γ : Lp ℝ ⊤ (volume.restrict (Ioo (0 : ℝ) 1)))
    (u v : SobolevInterval 1 0 1) :
    equation_12_44 α β γ u v = ∫ x in Ioo (0 : ℝ) 1,
      (α x * deriv u 1 x * deriv v 1 x + β x * deriv u 1 x * deriv v 0 x
        + γ x * deriv u 0 x * deriv v 0 x) :=
  EllipticInterval.form_apply α β γ u v

/-- The load functional on the right-hand side of (12.43) is $(f, v) = \int_0^1 f v \, dx$ for
$f \in L^2(0, 1)$ and $v \in H^1(0, 1)$. -/
theorem load_apply (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1))) (v : SobolevInterval 1 0 1) :
    EllipticInterval.load 0 1 f v = ∫ x in Ioo (0 : ℝ) 1, f x * deriv v 0 x :=
  EllipticInterval.load_apply f v

/-- **Equation (12.43)** of [quarteroni2000numerical] (the weak formulation). Let
$\alpha \in C^1([0, 1])$, let $\beta$ and $\gamma$ be continuous on $[0, 1]$, and let $f$ be a
function on $(0, 1)$. Let $\alpha, \beta, \gamma$ agree almost everywhere on $(0, 1)$ with
elements of $L^\infty(0, 1)$, and let $f$ agree almost everywhere with an element of
$L^2(0, 1)$. Let $u \in C^2([0, 1])$ satisfy
$$-(\alpha u')' + \beta u' + \gamma u = f \quad \text{on } (0, 1), \qquad u(0) = u(1) = 0.$$
Then $u \in V = H^1_0(0, 1)$ and $a(u, v) = (f, v)$ for every $v \in V$.

The conclusion is `IsGalerkinSolution` with the subspace $V$. The derivative $u'$ is
`u.shift.extend`, and the element of $H^1(0, 1)$ is `EllipticInterval.ofContDiffMapIcc
zero_lt_one u`.

**Reading.** The classical equation uses $C^1$ diffusion. The coefficients and forcing in the
weak form are their almost-everywhere classes. -/
theorem equation_12_43 {α β γ f : ℝ → ℝ}
    (αL βL γL : Lp ℝ ⊤ (volume.restrict (Ioo (0 : ℝ) 1)))
    (fL : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (hαL : αL =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] α)
    (hβL : βL =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] β)
    (hγL : γL =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] γ)
    (hfL : fL =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] f)
    (hα : ContDiffOn ℝ 1 α (Icc 0 1)) (hβ : ContinuousOn β (Icc 0 1))
    (hγ : ContinuousOn γ (Icc 0 1)) (u : ContDiffMapIcc zero_le_one 2)
    (hode : ∀ x ∈ Ioo (0 : ℝ) 1, -deriv (fun t ↦ α t * u.shift.extend t) x
      + β x * u.shift.extend x + γ x * u.extend x = f x)
    (hua : u.extend 0 = 0) (hub : u.extend 1 = 0) :
    IsGalerkinSolution (equation_12_44 αL βL γL) (EllipticInterval.load 0 1 fL) equation_12_42
      (EllipticInterval.ofContDiffMapIcc zero_lt_one u) :=
  EllipticInterval.isWeakSolution_of_classical zero_lt_one αL βL γL fL hαL hβL hγL hfL hα hβ hγ
    u hode hua hub

/-- The nonhomogeneous Dirichlet problem of Section 12.4.1. Let
$\alpha, \beta, \gamma \in L^\infty(0, 1)$ and $f \in L^2(0, 1)$, and let $U \in H^1(0, 1)$
satisfy $a(U, v) = (f, v)$ for all $v \in V$. Then for every $W \in H^1(0, 1)$ and every
$v \in V$,
$$a(U - W, v) = (f, v) - a(W, v).$$

In the book, $W$ is a lifting of the boundary values $u(0) = u_0$, $u(1) = u_1$, for example
$W(x) = x u_1 + (1 - x) u_0$, so that $\mathring{u} = U - W$ lies in $V$. The identity holds for
every $W$.

**Generalization.** The identity holds for any $H^1$ function $W$. Membership of $U-W$ in
$H_0^1$ requires matching its endpoint traces. -/
theorem equation_12_43_lift (α β γ : Lp ℝ ⊤ (volume.restrict (Ioo (0 : ℝ) 1)))
    (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1))) {U : SobolevInterval 1 0 1}
    (hU : ∀ v ∈ equation_12_42, equation_12_44 α β γ U v = EllipticInterval.load 0 1 f v)
    (W : SobolevInterval 1 0 1) {v : SobolevInterval 1 0 1} (hv : v ∈ equation_12_42) :
    equation_12_44 α β γ (U - W) v
      = EllipticInterval.load 0 1 f v - equation_12_44 α β γ W v :=
  EllipticInterval.form_sub_eq_of_forall α β γ f hU W hv

/-- The homogeneous Neumann problem of Section 12.4.1. Let $\alpha$, $\beta$, $\gamma$, $f$ and
$u \in C^2([0, 1])$ be as in (12.43), except that the boundary conditions are
$\alpha(0) u'(0) = \alpha(1) u'(1) = 0$. Then $a(u, v) = (f, v)$ for every $v \in H^1(0, 1)$.

**Reading.** The classical equation uses $C^1$ diffusion. The coefficients and forcing in the
weak form are their almost-everywhere classes. -/
theorem equation_12_43_neumann {α β γ f : ℝ → ℝ}
    (αL βL γL : Lp ℝ ⊤ (volume.restrict (Ioo (0 : ℝ) 1)))
    (fL : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (hαL : αL =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] α)
    (hβL : βL =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] β)
    (hγL : γL =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] γ)
    (hfL : fL =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] f)
    (hα : ContDiffOn ℝ 1 α (Icc 0 1)) (hβ : ContinuousOn β (Icc 0 1))
    (hγ : ContinuousOn γ (Icc 0 1)) (u : ContDiffMapIcc zero_le_one 2)
    (hode : ∀ x ∈ Ioo (0 : ℝ) 1, -deriv (fun t ↦ α t * u.shift.extend t) x
      + β x * u.shift.extend x + γ x * u.extend x = f x)
    (hw₀ : α 0 * u.shift.extend 0 = 0) (hw₁ : α 1 * u.shift.extend 1 = 0)
    (v : SobolevInterval 1 0 1) :
    equation_12_44 αL βL γL (EllipticInterval.ofContDiffMapIcc zero_lt_one u) v
      = EllipticInterval.load 0 1 fL v := by
  have h := EllipticInterval.isWeakSolution_of_classical_neumann zero_lt_one αL βL γL fL hαL hβL
    hγL hfL hα hβ hγ u hode hw₀ hw₁ v
  simpa using h

/-- **Exercise 12.12** of [quarteroni2000numerical], cited at the end of Section 12.4.1. Let
$\alpha$, $\beta$, $\gamma$, $f$ and $u \in C^2([0, 1])$ be as in (12.43), except that the
boundary conditions are the Neumann conditions $\alpha(0) u'(0) = w_0$ and
$\alpha(1) u'(1) = w_1$. Then for every $v \in H^1(0, 1)$,
$$a(u, v) = (f, v) + w_1 v(1) - w_0 v(0).$$

The mixed problem with $\alpha(0) u'(0) = w_0$ and $u(1) = u_1$ follows: test this identity with
the $v$ that satisfy $v(1) = 0$, after a lifting of $u_1$. The values $v(0)$ and $v(1)$ are
those of the continuous representative `SobolevInterval.rep v`.

**Reading.** The classical equation uses $C^1$ diffusion. The coefficients and forcing in the
weak form are their almost-everywhere classes. -/
theorem exercise_12_12 {α β γ f : ℝ → ℝ}
    (αL βL γL : Lp ℝ ⊤ (volume.restrict (Ioo (0 : ℝ) 1)))
    (fL : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (hαL : αL =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] α)
    (hβL : βL =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] β)
    (hγL : γL =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] γ)
    (hfL : fL =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] f)
    (hα : ContDiffOn ℝ 1 α (Icc 0 1)) (hβ : ContinuousOn β (Icc 0 1))
    (hγ : ContinuousOn γ (Icc 0 1)) (u : ContDiffMapIcc zero_le_one 2)
    (hode : ∀ x ∈ Ioo (0 : ℝ) 1, -deriv (fun t ↦ α t * u.shift.extend t) x
      + β x * u.shift.extend x + γ x * u.extend x = f x)
    {w₀ w₁ : ℝ} (hw₀ : α 0 * u.shift.extend 0 = w₀) (hw₁ : α 1 * u.shift.extend 1 = w₁)
    (v : SobolevInterval 1 0 1) :
    equation_12_44 αL βL γL (EllipticInterval.ofContDiffMapIcc zero_lt_one u) v
      = EllipticInterval.load 0 1 fL v + w₁ * rep v 1 - w₀ * rep v 0 :=
  EllipticInterval.isWeakSolution_of_classical_neumann zero_lt_one αL βL γL fL hαL hβL hγL hfL
    hα hβ hγ u hode hw₀ hw₁ v

/-! ### Distributions and the distributional derivative (12.45) -/

section Distributions

open TopologicalSpace
open scoped Distributions

/-- **Equation (12.45)** of [quarteroni2000numerical]. The distributional derivative $T^{(k)}$ of
order $k$ of a distribution $T \in \mathcal{D}'(0, 1)$: the $k$-fold iterate of the
distributional derivative.

The test function space $\mathcal{D}(0, 1) = C_0^\infty(0, 1)$ is Mathlib's
`𝓓(Opens.Ioo 0 1, ℝ)`. Its dual space of continuous linear functionals is
`𝓓'(Opens.Ioo 0 1, ℝ)`. One derivative is `Distribution.lineDerivCLM` along the
vector $1$. Every distribution has derivatives of all orders by construction, which is the
remark that closes Section 12.4.2. -/
noncomputable def equation_12_45 (k : ℕ) (T : 𝓓'(Opens.Ioo (0 : ℝ) 1, ℝ)) :
    𝓓'(Opens.Ioo (0 : ℝ) 1, ℝ) :=
  (fun S ↦ Distribution.lineDerivCLM (1 : ℝ) S)^[k] T

/-- **Equation (12.45)** of [quarteroni2000numerical]. For every distribution
$T \in \mathcal{D}'(0, 1)$, every $k \in \mathbb{N}$ and every test function
$\varphi \in \mathcal{D}(0, 1)$,
$$\langle T^{(k)}, \varphi \rangle = (-1)^k \langle T, \varphi^{(k)} \rangle.$$

The derivative $\varphi^{(k)}$ of the test function is the $k$-fold iterate of
`TestFunction.lineDerivCLM` along the vector $1$. -/
theorem equation_12_45_apply (k : ℕ) (T : 𝓓'(Opens.Ioo (0 : ℝ) 1, ℝ))
    (φ : 𝓓(Opens.Ioo (0 : ℝ) 1, ℝ)) :
    equation_12_45 k T φ
      = (-1) ^ k * T ((fun ψ ↦ TestFunction.lineDerivCLM ℝ (1 : ℝ) ψ)^[k] φ) := by
  induction k generalizing φ with
  | zero => simp [equation_12_45]
  | succ m ih =>
      have hstep : equation_12_45 (m + 1) T
          = Distribution.lineDerivCLM (1 : ℝ) (equation_12_45 m T) :=
        Function.iterate_succ_apply' _ _ _
      rw [hstep, Distribution.lineDerivCLM_apply, ih, Function.iterate_succ_apply]
      ring

/-- **The Heaviside function** of the example after (12.45) of [quarteroni2000numerical]: $H(x) = 1$
for $x \ge 0$ and $H(x) = 0$ for $x < 0$. -/
noncomputable def heaviside : ℝ → ℝ := Set.indicator (Set.Ici 0) 1

/-- The Heaviside function is $H(x) = 1$ if $0 \le x$ and $H(x) = 0$ otherwise. -/
theorem heaviside_apply (x : ℝ) : heaviside x = if 0 ≤ x then 1 else 0 := by
  rw [heaviside, Set.indicator_apply]
  simp

/-- The Heaviside function is measurable. -/
theorem measurable_heaviside : Measurable heaviside :=
  (measurable_const : Measurable (1 : ℝ → ℝ)).indicator measurableSet_Ici

/-- The Heaviside function is locally integrable on $\mathbb{R}$. -/
theorem locallyIntegrable_heaviside : LocallyIntegrable heaviside volume := by
  refine MeasureTheory.locallyIntegrable_iff.2 fun K hK ↦ ?_
  refine Measure.integrableOn_of_bounded hK.measure_lt_top.ne
    measurable_heaviside.aestronglyMeasurable (M := 1) ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, heaviside_apply]
  split_ifs <;> simp

/-- **Section 12.4.2** of [quarteroni2000numerical], the regular distribution. For a function $f$ on
$\mathbb{R}$, the distribution $T_f \in \mathcal{D}'(\mathbb{R})$ given by
$$\langle T_f, \varphi \rangle = \int_{\mathbb{R}} \varphi f \, dx.$$

The book uses this identification of a locally integrable function with a distribution without a
name. The definition is Mathlib's `TestFunction.integralAgainstBilinCLM` for the product
$(u, v) \mapsto uv$ and the Lebesgue measure. The integral formula, for a locally integrable
$f$, is `QuarteroniSaccoSaleri.Chapter12.regularDistribution_apply`.

**Generalization.** Uses the regular distribution on the full line. The integral formula holds
for locally integrable functions. -/
noncomputable def regularDistribution (f : ℝ → ℝ) : 𝓓'((⊤ : Opens ℝ), ℝ) :=
  TestFunction.integralAgainstBilinCLM (ContinuousLinearMap.mul ℝ ℝ) volume f

/-- If $f$ is locally integrable on $\mathbb{R}$, then $\langle T_f, \varphi \rangle =
\int_{\mathbb{R}} \varphi f \, dx$ for every test function $\varphi$ on $\mathbb{R}$.

**Generalization.** Uses the regular distribution on the full line. The integral formula holds
for locally integrable functions. -/
theorem regularDistribution_apply {f : ℝ → ℝ}
    (hf : LocallyIntegrableOn f (⊤ : Opens ℝ) volume) (φ : 𝓓((⊤ : Opens ℝ), ℝ)) :
    regularDistribution f φ = ∫ x, φ x * f x :=
  TestFunction.integralAgainstBilinCLM_eq_integral (B := ContinuousLinearMap.mul ℝ ℝ)
    (μ := volume) (φ := f) hf (f := φ)

/-- The derivative of a test function $\varphi$ on $\mathbb{R}$ along the vector $1$ is its
classical derivative $\varphi'$. -/
theorem testFunction_lineDeriv_apply (φ : 𝓓((⊤ : Opens ℝ), ℝ)) (x : ℝ) :
    (TestFunction.lineDerivCLM ℝ (1 : ℝ) φ : 𝓓((⊤ : Opens ℝ), ℝ)) x = deriv (φ : ℝ → ℝ) x := by
  rw [TestFunction.lineDerivCLM_apply_of_le (by simp), lineDeriv]
  simp only [smul_eq_mul, mul_one]
  rw [deriv_comp_const_add, add_zero]

/-- For a test function $\varphi$ on $\mathbb{R}$, $\int_0^\infty \varphi'(x) \, dx = -\varphi(0)$.
This is the fundamental theorem of calculus on $[0, \infty)$; the term at $+\infty$ vanishes
because $\varphi$ has compact support. -/
theorem integral_Ioi_deriv_testFunction (φ : 𝓓((⊤ : Opens ℝ), ℝ)) :
    ∫ x in Set.Ioi (0 : ℝ), deriv (φ : ℝ → ℝ) x = -φ 0 := by
  have hdiff : ∀ x : ℝ, HasDerivAt (φ : ℝ → ℝ) (deriv (φ : ℝ → ℝ) x) x := fun x ↦
    ((φ.contDiff.differentiable (by simp)).differentiableAt).hasDerivAt
  have hint : Integrable (deriv (φ : ℝ → ℝ)) volume := by
    have h := (TestFunction.lineDerivCLM ℝ (1 : ℝ) φ :
      𝓓((⊤ : Opens ℝ), ℝ)).integrable (μ := volume) (by
        simpa using (locallyIntegrable_const (1 : ℝ)).locallyIntegrableOn _)
    exact h.congr (Filter.Eventually.of_forall fun x ↦ testFunction_lineDeriv_apply φ x)
  have htend : Filter.Tendsto (φ : ℝ → ℝ) Filter.atTop (nhds 0) :=
    φ.hasCompactSupport.is_zero_at_infty.mono_left _root_.atTop_le_cocompact
  have key := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto
    (f := (φ : ℝ → ℝ)) (f' := deriv (φ : ℝ → ℝ)) (a := 0) (m := 0)
    φ.continuous.continuousWithinAt (fun x _ ↦ hdiff x) hint.integrableOn htend
  simpa using key

/-- **Example after (12.45)** of [quarteroni2000numerical]. The distributional derivative of the
regular distribution of the Heaviside function $H$ on $\mathbb{R}$ is the Dirac mass at the
origin: $H' = \delta$, where $\langle \delta, \varphi \rangle = \varphi(0)$.

The proof is the computation $\langle H', \varphi \rangle = -\int_{\mathbb{R}} H \varphi' =
-\int_0^\infty \varphi' = \varphi(0)$. The distributions are on all of $\mathbb{R}$, and
$\delta$ is Mathlib's `Distribution.delta 0`. -/
theorem equation_12_45_heaviside :
    Distribution.lineDerivCLM (1 : ℝ) (regularDistribution heaviside)
      = (Distribution.delta 0 : 𝓓'((⊤ : Opens ℝ), ℝ)) := by
  ext φ
  rw [Distribution.lineDerivCLM_apply, Distribution.delta_apply,
    regularDistribution_apply (locallyIntegrable_heaviside.locallyIntegrableOn _)]
  have hcong : ∀ x : ℝ,
      (TestFunction.lineDerivCLM ℝ (1 : ℝ) φ : 𝓓((⊤ : Opens ℝ), ℝ)) x * heaviside x
        = (Set.Ici (0 : ℝ)).indicator (deriv (φ : ℝ → ℝ)) x := by
    intro x
    rw [testFunction_lineDeriv_apply, Set.indicator_apply, heaviside_apply]
    by_cases h1 : (0 : ℝ) ≤ x
    · simp only [h1, Set.mem_Ici, reduceIte, mul_one]
    · simp only [h1, Set.mem_Ici, reduceIte, mul_zero]
  rw [integral_congr_ae (Filter.Eventually.of_forall hcong),
    MeasureTheory.integral_indicator measurableSet_Ici,
    MeasureTheory.integral_Ici_eq_integral_Ioi, integral_Ioi_deriv_testFunction, neg_neg]

end Distributions

/-! ### The Galerkin method (12.46)–(12.48) -/

/-- **Equation (12.46)** of [quarteroni2000numerical] (the Galerkin method). Let
$\alpha, \beta, \gamma \in L^\infty(0, 1)$, $f \in L^2(0, 1)$, and let $V_h$ be a subspace of
$H^1(0, 1)$. An element $u_h$ **solves the Galerkin problem** in $V_h$ if $u_h \in V_h$ and
$$a(u_h, v_h) = (f, v_h) \quad \text{for all } v_h \in V_h.$$

The book takes $V_h$ to be a finite-dimensional subspace of $V$; the definition allows any
subspace of $H^1(0, 1)$. With $V_h = V$, it is the weak problem (12.43).

**Generalization.** Uses essentially bounded coefficients and an arbitrary trial subspace of
$H^1$. The matrix equivalence uses a finite basis. -/
abbrev equation_12_46 (α β γ : Lp ℝ ⊤ (volume.restrict (Ioo (0 : ℝ) 1)))
    (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (Vh : Submodule ℝ (SobolevInterval 1 0 1)) (uh : SobolevInterval 1 0 1) : Prop :=
  IsGalerkinSolution (equation_12_44 α β γ) (EllipticInterval.load 0 1 f) Vh uh

/-- **Equation (12.48)** of [quarteroni2000numerical], the stiffness matrix. For a family
$\varphi_1, \ldots, \varphi_N$ of elements of $H^1(0, 1)$, the matrix $A_G$ with entries
$$(A_G)_{ij} = a(\varphi_j, \varphi_i).$$

The definition is `SesqForm.gramMatrix` of the form (12.44).

**Generalization.** Uses essentially bounded coefficients and an arbitrary trial subspace of
$H^1$. The matrix equivalence uses a finite basis. -/
noncomputable def equation_12_48_matrix {ι : Type*} (α β γ : Lp ℝ ⊤ (volume.restrict
    (Ioo (0 : ℝ) 1))) (φ : ι → SobolevInterval 1 0 1) : Matrix ι ι ℝ :=
  (equation_12_44 α β γ).gramMatrix φ

/-- **Equations (12.47)–(12.48)** of [quarteroni2000numerical]. Let $\varphi_1, \ldots, \varphi_N$
be a basis of a subspace $V_h$ of $H^1(0, 1)$, and let $\xi \in \mathbb{R}^N$. Then
$u_h = \sum_j \xi_j \varphi_j$ solves the Galerkin problem (12.46) in $V_h$ if and only if
$$A_G \xi = f_G, \qquad (f_G)_i = (f, \varphi_i).$$

**Generalization.** Uses essentially bounded coefficients and an arbitrary trial subspace of
$H^1$. The matrix equivalence uses a finite basis. -/
theorem equation_12_48 {ι : Type*} [Fintype ι] (α β γ : Lp ℝ ⊤ (volume.restrict (Ioo (0 : ℝ) 1)))
    (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    {Vh : Submodule ℝ (SobolevInterval 1 0 1)} (φ : Module.Basis ι ℝ Vh) (ξ : ι → ℝ) :
    equation_12_46 α β γ f Vh (∑ j, ξ j • (φ j : SobolevInterval 1 0 1)) ↔
      equation_12_48_matrix α β γ (fun i ↦ (φ i : SobolevInterval 1 0 1)) *ᵥ ξ
        = fun i ↦ EllipticInterval.load 0 1 f (φ i) := by
  have h := IsGalerkinSolution.iff_gramMatrix_mulVec (a := equation_12_44 α β γ)
    (ℓ := EllipticInterval.load 0 1 f) φ ξ
  simpa [equation_12_46, equation_12_48_matrix] using h

/-! ### Analysis of the Galerkin method (§12.4.4) -/

/-- **Equation (12.49)** of [quarteroni2000numerical]. The seminorm on $H^1(0, 1)$
$$|v|_{H^1(0,1)} = \Big( \int_0^1 |v'|^2 \, dx \Big)^{1/2},$$
which is a norm on $V = H^1_0(0, 1)$.

The definition is `SobolevInterval.seminorm 1 0 1`, the $L^2$ norm of the weak derivative. -/
noncomputable abbrev equation_12_49 : Seminorm ℝ (SobolevInterval 1 0 1) :=
  SobolevInterval.seminorm 1 0 1

/-- The seminorm (12.49) of $v$ is the $L^2(0, 1)$ norm of the weak derivative $v'$. -/
theorem equation_12_49_apply (v : SobolevInterval 1 0 1) : equation_12_49 v = ‖deriv v 1‖ := rfl

/-- **Section 12.4.4** of [quarteroni2000numerical], coercivity for $\beta = 0$. Let
$\alpha, \gamma \in L^\infty(0, 1)$ with $\alpha \ge \alpha_0$ and $\gamma \ge 0$ almost
everywhere on $(0, 1)$. Then the form (12.44) with $\beta = 0$ satisfies
$$\alpha_0 |v|^2_{H^1(0,1)} \le a(v, v) \quad \text{for every } v \in H^1(0, 1).$$

The inequality holds on all of $H^1(0, 1)$, and no sign condition on $\alpha_0$ is needed.

**Reading.** The coefficient inequalities are almost everywhere. The existence theorem and the
stability estimate specialize to $\beta=0$. -/
theorem equation_12_50 (α γ : Lp ℝ ⊤ (volume.restrict (Ioo (0 : ℝ) 1))) {α₀ : ℝ}
    (hα : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), α₀ ≤ α x)
    (hγ : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), 0 ≤ γ x) (v : SobolevInterval 1 0 1) :
    α₀ * equation_12_49 v ^ 2 ≤ equation_12_44 α 0 γ v v :=
  EllipticInterval.form_isCoerciveWith_seminorm α γ hα hγ v

/-- Coercivity under the condition (12.50) of [quarteroni2000numerical]. Let
$\alpha, \gamma \in L^\infty(0, 1)$ with $\alpha \ge \alpha_0$ almost everywhere, and let
$\beta \in C^1([0, 1])$ agree almost everywhere with an element of $L^\infty(0, 1)$. If
$-\beta'/2 + \gamma \ge 0$ almost everywhere on $(0, 1)$, then
$\alpha_0 |v|^2_{H^1(0,1)} \le a(v, v)$ for every $v \in V = H^1_0(0, 1)$.

**Reading.** The coefficient inequalities are almost everywhere. The existence theorem and the
stability estimate specialize to $\beta=0$. -/
theorem equation_12_50_of_le (αL βL γL : Lp ℝ ⊤ (volume.restrict (Ioo (0 : ℝ) 1))) {α₀ : ℝ}
    (hα : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), α₀ ≤ αL x) {β : ℝ → ℝ}
    (hβL : βL =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] β) (hβ : ContDiffOn ℝ 1 β (Icc 0 1))
    (hcond : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), deriv β x / 2 ≤ γL x)
    {v : SobolevInterval 1 0 1} (hv : v ∈ equation_12_42) :
    α₀ * equation_12_49 v ^ 2 ≤ equation_12_44 αL βL γL v v :=
  EllipticInterval.form_isCoerciveWith_seminorm_of_le zero_lt_one αL βL γL hα hβL hβ hcond hv

/-- Unique solvability of the weak problem, the consequence of coercivity stated after (12.50) of
[quarteroni2000numerical]. Let $\alpha, \gamma \in L^\infty(0, 1)$ with
$\alpha \ge \alpha_0 > 0$ and $\gamma \ge 0$ almost everywhere, and let $f \in L^2(0, 1)$. Then
the weak problem (12.43) with $\beta = 0$ has exactly one solution $u \in V$.

**Reading.** The coefficient inequalities are almost everywhere. The existence theorem and the
stability estimate specialize to $\beta=0$. -/
theorem equation_12_50_existsUnique (α γ : Lp ℝ ⊤ (volume.restrict (Ioo (0 : ℝ) 1))) {α₀ : ℝ}
    (hα₀ : 0 < α₀) (hα : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), α₀ ≤ α x)
    (hγ : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), 0 ≤ γ x)
    (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1))) :
    ∃! u, equation_12_46 α 0 γ f equation_12_42 u :=
  EllipticInterval.existsUnique_isWeakSolution zero_lt_one α γ hα₀ hα hγ f

/-- **Equation (12.51)** of [quarteroni2000numerical] (stability of the Galerkin method). Let
$\alpha, \gamma \in L^\infty(0, 1)$ with $\alpha \ge \alpha_0 > 0$ and $\gamma \ge 0$ almost
everywhere, and let $f \in L^2(0, 1)$. Let $V_h$ be any subspace of $V = H^1_0(0, 1)$, and let
$u_h$ solve the Galerkin problem (12.46) in $V_h$ with $\beta = 0$. Then
$$|u_h|_{H^1(0,1)} \le \frac{C_P}{\alpha_0} \|f\|_{L^2(0,1)}, \qquad C_P = \frac{1}{\sqrt{2}}.$$

The bound does not depend on $V_h$.

**Reading.** The coefficient inequalities are almost everywhere. The existence theorem and the
stability estimate specialize to $\beta=0$. -/
theorem equation_12_51 (α γ : Lp ℝ ⊤ (volume.restrict (Ioo (0 : ℝ) 1))) {α₀ : ℝ} (hα₀ : 0 < α₀)
    (hα : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), α₀ ≤ α x)
    (hγ : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), 0 ≤ γ x)
    (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    {Vh : Submodule ℝ (SobolevInterval 1 0 1)} (hVh : Vh ≤ equation_12_42)
    {uh : SobolevInterval 1 0 1} (huh : equation_12_46 α 0 γ f Vh uh) :
    equation_12_49 uh ≤ 1 / Real.sqrt 2 / α₀ * ‖f‖ := by
  have h := EllipticInterval.seminorm_le_of_isGalerkinSolution zero_lt_one α γ hα₀ hα hγ f hVh huh
  simpa using h

/-- **Equation (12.53)** of [quarteroni2000numerical] (Galerkin orthogonality). Let
$\alpha, \beta, \gamma \in L^\infty(0, 1)$, $f \in L^2(0, 1)$, and let $V_h$ be a subspace of
$H^1(0, 1)$. Let $u \in H^1(0, 1)$ satisfy $a(u, v) = (f, v)$ for every $v \in H^1(0, 1)$, and
let $u_h$ solve the Galerkin problem (12.46) in $V_h$. Then
$$a(u - u_h, v_h) = 0 \quad \text{for every } v_h \in V_h.$$

The hypothesis on $u$ is the equation for all test functions $v \in H^1(0, 1)$, not only for
$v \in V$.

**Reading.** Requires the exact variational equation on all of $H^1$. The source only needs it
on $H_0^1$, since it assumes $V_h\subseteq H_0^1$. -/
theorem equation_12_53 (α β γ : Lp ℝ ⊤ (volume.restrict (Ioo (0 : ℝ) 1)))
    (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    {Vh : Submodule ℝ (SobolevInterval 1 0 1)} {u uh : SobolevInterval 1 0 1}
    (hu : ∀ v, equation_12_44 α β γ u v = EllipticInterval.load 0 1 f v)
    (huh : equation_12_46 α β γ f Vh uh) {v : SobolevInterval 1 0 1} (hv : v ∈ Vh) :
    equation_12_44 α β γ (u - uh) v = 0 :=
  IsGalerkinSolution.apply_sub_eq_zero huh hu hv

/-- **Theorem 12.3** of [quarteroni2000numerical]. Let $\alpha, \gamma \in L^\infty(0, 1)$ with
$\alpha \ge \alpha_0 > 0$ and $\gamma \ge 0$ almost everywhere, let $f \in L^2(0, 1)$, and let
$\beta = 0$. Let $u \in V$ solve the weak problem (12.43), let $V_h$ be a subspace of $V$, and
let $u_h$ solve the Galerkin problem (12.46) in $V_h$. Then for every $w_h \in V_h$,
$$|u - u_h|_{H^1(0,1)} \le C |u - w_h|_{H^1(0,1)}, \qquad C = \frac{1}{\alpha_0} \big(
  \|\alpha\|_\infty + C_P^2 \|\gamma\|_\infty \big), \quad C_P = \frac{1}{\sqrt{2}}.$$
Hence $|u - u_h|_{H^1(0,1)} \le C \min_{w_h \in V_h} |u - w_h|_{H^1(0,1)}$, which is (12.52).

**Reading.** Gives the estimate for each trial comparison and allows $L^\infty$ coefficients.
The source states the minimum over its finite-dimensional trial space. -/
theorem theorem_12_3 (α γ : Lp ℝ ⊤ (volume.restrict (Ioo (0 : ℝ) 1))) {α₀ : ℝ} (hα₀ : 0 < α₀)
    (hα : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), α₀ ≤ α x)
    (hγ : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), 0 ≤ γ x)
    (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    {Vh : Submodule ℝ (SobolevInterval 1 0 1)} (hVh : Vh ≤ equation_12_42)
    {u uh : SobolevInterval 1 0 1} (hu : equation_12_46 α 0 γ f equation_12_42 u)
    (huh : equation_12_46 α 0 γ f Vh uh) {w : SobolevInterval 1 0 1} (hw : w ∈ Vh) :
    equation_12_49 (u - uh)
      ≤ α₀⁻¹ * (‖α‖ + (1 / Real.sqrt 2) ^ 2 * ‖γ‖) * equation_12_49 (u - w) := by
  have h := EllipticInterval.galerkin_seminorm_sub_le zero_lt_one α γ hα₀ hα hγ f hVh hu huh hw
  simpa using h

/-! ### Lax–Milgram and Céa in a Hilbert space (12.54)–(12.56) -/

section Abstract

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  {a : SesqForm ℝ V} {ℓ : V →L[ℝ] ℝ}

/-- **Equations (12.54)–(12.55)** of [quarteroni2000numerical] (Lax–Milgram lemma). Let $V$ be a
real Hilbert space, let $a$ be a bounded bilinear form on $V$, and let $\ell$ be a bounded
linear functional on $V$. If $a$ is coercive, $a(v, v) \ge \alpha_0 \|v\|^2$ for all $v \in V$
with $\alpha_0 > 0$, then there is exactly one $u \in V$ with $a(u, v) = \ell(v)$ for every
$v \in V$.

The form need not be symmetric. The bound on the solution is
`QuarteroniSaccoSaleri.Chapter12.laxMilgram_lemma_bound`. -/
theorem laxMilgram_lemma {α₀ : ℝ} (hα₀ : 0 < α₀) (hcoer : a.IsCoerciveWith α₀) :
    ∃! u, ∀ v, a u v = ℓ v :=
  SesqForm.laxMilgram a ℓ hα₀ hcoer

omit [CompleteSpace V] in
/-- The stability bound of the Lax–Milgram lemma. Let $V$ be a real inner product space, let $a$ be
a bounded bilinear form on $V$ that is coercive with constant $\alpha_0 > 0$, and let $\ell$ be
a bounded linear functional with $\|\ell\| \le K$. If $a(u, v) = \ell(v)$ for every $v \in V$,
then $\|u\| \le K / \alpha_0$.

**Generalization.** The norm bound concerns an existing solution, so no completeness assumption
is needed. -/
theorem laxMilgram_lemma_bound {α₀ K : ℝ} (hα₀ : 0 < α₀) (hcoer : a.IsCoerciveWith α₀)
    (hK : ‖ℓ‖ ≤ K) {u : V} (hu : ∀ v, a u v = ℓ v) : ‖u‖ ≤ K / α₀ :=
  (SesqForm.norm_le_of_forall_apply_eq a ℓ hα₀ hcoer hu).trans (by gcongr)

omit [CompleteSpace V] in
/-- The Lax–Milgram lemma for the Galerkin problem. Let $V$ be a real inner product space, and let
$a$ be a bounded bilinear form on $V$ that is coercive with constant $\alpha_0 > 0$. Then for
every complete subspace $V_h$ of $V$ and every bounded linear functional $\ell$, the Galerkin
problem in $V_h$ has exactly one solution $u_h$.

**Generalization.** The trial subspace can have any dimension provided it is complete. -/
theorem laxMilgram_lemma_galerkin {α₀ : ℝ} (hα₀ : 0 < α₀) (hcoer : a.IsCoerciveWith α₀)
    (Vh : Submodule ℝ V) [CompleteSpace Vh] : ∃! uh, IsGalerkinSolution a ℓ Vh uh :=
  IsGalerkinSolution.existsUnique hα₀ hcoer

omit [CompleteSpace V] in
/-- The stability bound for the Galerkin problem. Let $V$ be a real inner product space, let $a$ be
a bounded bilinear form on $V$ that is coercive with constant $\alpha_0 > 0$, and let $\ell$ be
a bounded linear functional with $\|\ell\| \le K$. If $u_h$ solves the Galerkin problem in a
subspace $V_h$, then $\|u_h\| \le K / \alpha_0$.

**Generalization.** The norm bound concerns an existing solution, so no completeness assumption
is needed. -/
theorem laxMilgram_lemma_galerkin_bound {α₀ K : ℝ} (hα₀ : 0 < α₀) (hcoer : a.IsCoerciveWith α₀)
    (hK : ‖ℓ‖ ≤ K) {Vh : Submodule ℝ V} {uh : V} (huh : IsGalerkinSolution a ℓ Vh uh) :
    ‖uh‖ ≤ K / α₀ := by
  have h1 : α₀ * ‖uh‖ ^ 2 ≤ RCLike.re (a uh uh) := hcoer uh
  rw [huh.2 uh huh.1] at h1
  have h2 : RCLike.re (ℓ uh) ≤ ‖ℓ‖ * ‖uh‖ := by
    simpa using (RCLike.re_le_norm (ℓ uh)).trans (ℓ.le_opNorm uh)
  have h3 : α₀ * ‖uh‖ ^ 2 ≤ K * ‖uh‖ :=
    h1.trans (h2.trans (mul_le_mul_of_nonneg_right hK (norm_nonneg uh)))
  have hK0 : 0 ≤ K := (norm_nonneg ℓ).trans hK
  rcases eq_or_lt_of_le (norm_nonneg uh) with h | h
  · rw [← h]
    positivity
  · rw [le_div_iff₀ hα₀]
    nlinarith

omit [CompleteSpace V] in
/-- **Equation (12.56)** of [quarteroni2000numerical] (Céa's lemma). Let $V$ be a real inner product
space, let $a$ be a bilinear form on $V$ with $|a(u, v)| \le M \|u\| \|v\|$ that is coercive
with constant $\alpha_0 > 0$, and let $\ell$ be a bounded linear functional. Let $u \in V$
satisfy $a(u, v) = \ell(v)$ for every $v \in V$, and let $u_h$ solve the Galerkin problem in a
subspace $V_h$. Then
$$\|u - u_h\| \le \frac{M}{\alpha_0} \|u - w_h\| \quad \text{for every } w_h \in V_h.$$

The form with the distance to $V_h$ is `QuarteroniSaccoSaleri.Chapter12.equation_12_56_infDist`.

**Generalization.** The bound applies to any trial subspace with a supplied solution, expressed
pointwise or by the distance infimum. -/
theorem equation_12_56 {α₀ M : ℝ} (hα₀ : 0 < α₀) (hM : a.IsBoundedWith M)
    (hcoer : a.IsCoerciveWith α₀) {Vh : Submodule ℝ V} {u uh : V}
    (huh : IsGalerkinSolution a ℓ Vh uh) (hu : ∀ v, a u v = ℓ v) {w : V} (hw : w ∈ Vh) :
    ‖u - uh‖ ≤ M / α₀ * ‖u - w‖ :=
  IsGalerkinSolution.norm_sub_le hα₀ hM hcoer huh hu hw

omit [CompleteSpace V] in
/-- Céa's lemma (12.56) with the distance to the subspace: under the hypotheses of
`QuarteroniSaccoSaleri.Chapter12.equation_12_56`, $\|u - u_h\| \le (M / \alpha_0) \inf_{w_h \in
V_h} \|u - w_h\|$.

**Generalization.** The bound applies to any trial subspace with a supplied solution, expressed
pointwise or by the distance infimum. -/
theorem equation_12_56_infDist {α₀ M : ℝ} (hα₀ : 0 < α₀) (hM : a.IsBoundedWith M)
    (hcoer : a.IsCoerciveWith α₀) {Vh : Submodule ℝ V} {u uh : V}
    (huh : IsGalerkinSolution a ℓ Vh uh) (hu : ∀ v, a u v = ℓ v) :
    ‖u - uh‖ ≤ M / α₀ * Metric.infDist u (Vh : Set V) :=
  IsGalerkinSolution.norm_sub_le_infDist hα₀ hM hcoer huh hu

end Abstract

/-- **Section 12.4.4** of [quarteroni2000numerical], positive definiteness of the stiffness matrix.
Let $V$ be a real inner product space, let $a$ be a symmetric bounded bilinear form on $V$ that
is coercive with constant $\alpha_0 > 0$, and let $\varphi_1, \ldots, \varphi_N$ be linearly
independent. Then the matrix $(a(\varphi_j, \varphi_i))_{ij}$ is symmetric positive definite.

The proof is $\xi^T A_G \xi = a(v_h, v_h) \ge \alpha_0 \|v_h\|^2 > 0$ for $\xi \neq 0$, where
$v_h = \sum_j \xi_j \varphi_j$. For (12.41) with $\beta = 0$ the form (12.44) is symmetric, so
this applies to $A_G$.

**Reading.** Adds symmetry because `Matrix.PosDef` includes Hermitian symmetry. The text calls
the positive quadratic form sufficient for its use of positive definite. -/
theorem galerkinMatrix_posDef {ι : Type*} [Finite ι] {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] {a : SesqForm ℝ V} {α₀ : ℝ} (hα₀ : 0 < α₀)
    (hsymm : a.IsHermitian) (hcoer : a.IsCoerciveWith α₀) {φ : ι → V}
    (hφ : LinearIndependent ℝ φ) : (a.gramMatrix φ).PosDef := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  exact SesqForm.gramMatrix_posDef hα₀ hsymm hcoer hφ

/-- The stiffness matrix of a symmetric bounded bilinear form on a real inner product space is
symmetric (Section 12.4.4 of [quarteroni2000numerical]).

**Reading.** Proves the forward direction for arbitrary families. Symmetry of a stiffness
matrix only tests the form on the span of the family. -/
theorem galerkinMatrix_isSymm {ι : Type*} {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {a : SesqForm ℝ V} (hsymm : a.IsHermitian) (φ : ι → V) :
    (a.gramMatrix φ).IsHermitian :=
  a.gramMatrix_isHermitian hsymm φ

/-! ### The finite element space (12.57) -/

/-- **Equation (12.57)** of [quarteroni2000numerical]. For nodes $x_0, \ldots, x_n$ and a degree
$k$, the finite element space
$$V_h = X_h^{k,0} = \{ v_h \in X_h^k : v_h(0) = v_h(1) = 0 \},$$
where $X_h^k$ is the space of the $v \in H^1(0, 1)$ whose continuous representative is a
continuous piecewise polynomial of degree at most $k$ on the elements $[x_i, x_{i+1}]$.

The definition is `FiniteElement.lagrangeSpaceZero`. It is a subspace of $V$ by
`QuarteroniSaccoSaleri.Chapter12.equation_12_57_le`.

**Generalization.** The space is defined for arbitrary node data and natural degrees, with
partition hypotheses used in the subsequent results. -/
noncomputable def equation_12_57 (n : ℕ) (x : ℕ → ℝ) (k : ℕ) :
    Submodule ℝ (SobolevInterval 1 0 1) :=
  FiniteElement.lagrangeSpaceZero zero_lt_one n x k

/-- The finite element space $X_h^{k,0}$ of (12.57) is a subspace of $V = H^1_0(0, 1)$.

**Generalization.** The space is defined for arbitrary node data and natural degrees, with
partition hypotheses used in the subsequent results. -/
theorem equation_12_57_le (n : ℕ) (x : ℕ → ℝ) (k : ℕ) : equation_12_57 n x k ≤ equation_12_42 :=
  FiniteElement.lagrangeSpaceZero_le_sobolevIntervalZero zero_lt_one n x k

/-- For a partition $0 = x_0 < \cdots < x_n = 1$ with $n \ge 1$, the space $X_h^k$ has dimension
$nk + 1$, the number of nodal values of a continuous piecewise polynomial of degree $k$.

The book gives $\dim V_h = nk - 1$ for $V_h = X_h^{k,0}$, which is this number minus the two
endpoint values.

**Reading.** Computes the dimension of the unconstrained space $X_h^k$. The text's dimension
$nk-1$ is for the subspace with zero traces. -/
theorem equation_12_57_finrank {n : ℕ} {x : ℕ → ℝ} (hx : IsIntervalPartition 0 1 n x)
    (hn : 1 ≤ n) (k : ℕ) :
    Module.finrank ℝ (FiniteElement.lagrangeSpace zero_lt_one n x k) = n * k + 1 :=
  FiniteElement.finrank_lagrangeSpace zero_lt_one hx hn k

/-! ### The convergence of the finite element method (12.58)–(12.60) -/

section Convergence

variable {n : ℕ} {x : ℕ → ℝ}

/-- **Equation (12.58)** of [quarteroni2000numerical]. Let $0 = x_0 < \cdots < x_n = 1$ be a
partition with $n \ge 1$. Let $\alpha, \gamma \in L^\infty(0, 1)$ with $\alpha \ge \alpha_0 > 0$
and $\gamma \ge 0$ almost everywhere, let $f \in L^2(0, 1)$, and let $\beta = 0$. Let $u \in V$
solve the weak problem (12.43), and let $u_h$ solve the Galerkin problem (12.46) in
$V_h = X_h^{1,0}$. Then
$$|u - u_h|_{H^1(0,1)} \le C |u - \Pi_h^1 u|_{H^1(0,1)}, \qquad C = \frac{1}{\alpha_0} \big(
  \|\alpha\|_\infty + C_P^2 \|\gamma\|_\infty \big), \quad C_P = \frac{1}{\sqrt{2}},$$
where $\Pi_h^1 u = \sum_{i=0}^n u(x_i) \varphi_i$ is the piecewise linear interpolant of $u$.

The interpolant lies in $X_h^{1,0}$, so this is Theorem 12.3 with $w_h = \Pi_h^1 u$. It turns
the estimate of the Galerkin error into an estimate of the interpolation error. The interpolant
is `FiniteElement.lagrangeInterp`.

**Partial.** Gives the solution error bound with the interpolant for $k=1$ and $\beta=0$,
combining the printed comparison with the coercivity estimate.

**Reading.** Combines Céa and interpolation for piecewise linear elements; does not state the
displayed best-error inequality for general k.
-/
theorem equation_12_58 (hx : IsIntervalPartition 0 1 n x) (hn : 1 ≤ n)
    (α γ : Lp ℝ ⊤ (volume.restrict (Ioo (0 : ℝ) 1))) {α₀ : ℝ} (hα₀ : 0 < α₀)
    (hα : ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) 1)), α₀ ≤ α t)
    (hγ : ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) 1)), 0 ≤ γ t)
    (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1))) {u uh : SobolevInterval 1 0 1}
    (hu : equation_12_46 α 0 γ f equation_12_42 u)
    (huh : equation_12_46 α 0 γ f (equation_12_57 n x 1) uh) :
    equation_12_49 (u - uh)
      ≤ α₀⁻¹ * (‖α‖ + (1 / Real.sqrt 2) ^ 2 * ‖γ‖)
        * equation_12_49 (u - FiniteElement.lagrangeInterp hx hn u) :=
  theorem_12_3 α γ hα₀ hα hγ f (equation_12_57_le n x 1) hu huh
    (FiniteElement.lagrangeInterp_mem_lagrangeSpaceZero zero_lt_one hx hn hu.1)

/-- **Property 12.1** of [quarteroni2000numerical], the $H^1$ estimate (12.59) for $k = 1$ and
$s = 2$. Let $0 = x_0 < \cdots < x_n = 1$ be a partition with $n \ge 1$ and
$x_{i+1} - x_i \le h$ for all $i$. Let $\alpha, \gamma \in L^\infty(0, 1)$ with
$\alpha \ge \alpha_0 > 0$ and $\gamma \ge 0$ almost everywhere, let $f \in L^2(0, 1)$, and let
$\beta = 0$. Let $u \in V$ solve the weak problem (12.43), and assume $u \in H^2(0, 1)$. Let
$u_h$ solve the Galerkin problem (12.46) in $V_h = X_h^{1,0}$. Then
$$|u - u_h|_{H^1(0,1)} \le \frac{1}{\alpha_0} \big( \|\alpha\|_\infty + C_P^2 \|\gamma\|_\infty
  \big) \, h \, |u|_{H^2(0,1)}, \qquad C_P = \frac{1}{\sqrt{2}},$$
where $|u|_{H^2(0,1)} = \|u''\|_{L^2(0,1)}$.

The book states the estimate for every $k \ge 1$ and $s \ge 2$ with $l = \min(k, s - 1)$ and
quotes its proof from Theorem 6.2.1 of [quarteroni1994numerical]. The case $l = 1$ is (12.58)
together with the interpolation estimate (8.27), which is
`FiniteElement.seminorm_sub_lagrangeInterp_le`; the interpolation constant is $1$. The element
$u \in H^2(0, 1)$ is an element `U` of `SobolevInterval 2 0 1` whose image under
`SobolevInterval.inclusionCLM` is $u$, and $|u|_{H^2(0,1)}$ is
`SobolevInterval.seminorm 2 0 1 U`.

**Specialization.** Uses piecewise linear elements with $\beta=0$ and explicit constants. The
$L^2$ estimate assumes $C^1$ diffusion with bounded derivative. -/
theorem property_12_1 (hx : IsIntervalPartition 0 1 n x) (hn : 1 ≤ n) {h : ℝ}
    (hmesh : ∀ k < n, x (k + 1) - x k ≤ h)
    (α γ : Lp ℝ ⊤ (volume.restrict (Ioo (0 : ℝ) 1))) {α₀ : ℝ} (hα₀ : 0 < α₀)
    (hα : ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) 1)), α₀ ≤ α t)
    (hγ : ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) 1)), 0 ≤ γ t)
    (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1))) (U : SobolevInterval 2 0 1)
    {u uh : SobolevInterval 1 0 1} (hU : SobolevInterval.inclusionCLM 1 0 1 U = u)
    (hu : equation_12_46 α 0 γ f equation_12_42 u)
    (huh : equation_12_46 α 0 γ f (equation_12_57 n x 1) uh) :
    equation_12_49 (u - uh)
      ≤ α₀⁻¹ * (‖α‖ + (1 / Real.sqrt 2) ^ 2 * ‖γ‖) * (h * SobolevInterval.seminorm 2 0 1 U) := by
  refine (equation_12_58 hx hn α γ hα₀ hα hγ f hu huh).trans ?_
  have hC : 0 ≤ α₀⁻¹ * (‖α‖ + (1 / Real.sqrt 2) ^ 2 * ‖γ‖) := by positivity
  refine mul_le_mul_of_nonneg_left ?_ hC
  have h1 := FiniteElement.seminorm_sub_lagrangeInterp_le zero_lt_one hx hn hmesh U
  rwa [hU] at h1

/-- **Property 12.1** of [quarteroni2000numerical], the $L^2$ estimate (12.60) for $k = 1$ and
$s = 2$. Let $0 = x_0 < \cdots < x_n = 1$ be a partition with $n \ge 1$ and
$x_{i+1} - x_i \le h$ for all $i$, where $h \ge 0$. Let $\alpha \in C^1([0, 1])$ agree almost
everywhere with an element of $L^\infty(0, 1)$, with $\alpha \ge \alpha_0 > 0$ and
$|\alpha'| \le A_1$ on $[0, 1]$. Let $\gamma \in L^\infty(0, 1)$ with $\gamma \ge 0$ almost
everywhere, let $f \in L^2(0, 1)$, and let $\beta = 0$. Let $u \in V$ solve the weak problem
(12.43), and assume $u \in H^2(0, 1)$. Let $u_h$ solve the Galerkin problem (12.46) in
$V_h = X_h^{1,0}$. Then
$$\|u - u_h\|_{L^2(0,1)} \le C h^2 |u|_{H^2(0,1)}$$
with the constant
$$C = \frac{M^2}{\alpha_0} \Big( \frac{C_P^2}{\alpha_0} + \frac{C_P}{\alpha_0} +
  \frac{1}{\alpha_0} \Big( \frac{C_P^2 \|\gamma\|_\infty}{\alpha_0} + 1 + \frac{A_1
  C_P}{\alpha_0} \Big) \Big), \qquad M = \|\alpha\|_\infty + C_P^2 \|\gamma\|_\infty, \quad
  C_P = \frac{1}{\sqrt{2}},$$
which does not depend on $h$ or $u$.

The book quotes this estimate from [quarteroni1994numerical]. The proof is the Aubin–Nitsche
duality argument `EllipticInterval.galerkin_norm_sub_le_l2`, whose approximation hypothesis
holds for the piecewise linear interpolant with $\delta = h$. It gains one power of $h$ over
`QuarteroniSaccoSaleri.Chapter12.property_12_1`. The bounds on $\alpha$ and $\alpha'$ are the
hypotheses of the duality argument. The derivative $\alpha'$ is the derivative within $[0, 1]$.

**Specialization.** Uses piecewise linear elements with $\beta=0$ and explicit constants. The
$L^2$ estimate assumes $C^1$ diffusion with bounded derivative. -/
theorem property_12_1_l2 (hx : IsIntervalPartition 0 1 n x) (hn : 1 ≤ n) {h : ℝ} (hh : 0 ≤ h)
    (hmesh : ∀ k < n, x (k + 1) - x k ≤ h)
    (αL γL : Lp ℝ ⊤ (volume.restrict (Ioo (0 : ℝ) 1))) {α : ℝ → ℝ}
    (hαL : αL =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] α) (hα : ContDiffOn ℝ 1 α (Icc 0 1))
    {α₀ A₁ : ℝ} (hα₀ : 0 < α₀) (hαpos : ∀ t ∈ Icc (0 : ℝ) 1, α₀ ≤ α t)
    (hA₁ : ∀ t ∈ Icc (0 : ℝ) 1, |derivWithin α (Icc 0 1) t| ≤ A₁)
    (hγ : ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) 1)), 0 ≤ γL t)
    (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1))) (U : SobolevInterval 2 0 1)
    {u uh : SobolevInterval 1 0 1} (hU : SobolevInterval.inclusionCLM 1 0 1 U = u)
    (hu : equation_12_46 αL 0 γL f equation_12_42 u)
    (huh : equation_12_46 αL 0 γL f (equation_12_57 n x 1) uh) :
    ‖deriv (u - uh) 0‖
      ≤ (‖αL‖ + (1 / Real.sqrt 2) ^ 2 * ‖γL‖)
          * ((1 / Real.sqrt 2) ^ 2 / α₀ + 1 / Real.sqrt 2 / α₀
            + α₀⁻¹ * (‖γL‖ * ((1 / Real.sqrt 2) ^ 2 / α₀) + 1 + A₁ * (1 / Real.sqrt 2 / α₀)))
          * (α₀⁻¹ * (‖αL‖ + (1 / Real.sqrt 2) ^ 2 * ‖γL‖))
        * h ^ 2 * SobolevInterval.seminorm 2 0 1 U := by
  have hαae : ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) 1)), α₀ ≤ αL t := by
    filter_upwards [hαL, ae_restrict_mem measurableSet_Ioo] with t ht htI
    rw [ht]
    exact hαpos t (Ioo_subset_Icc_self htI)
  have hl2 := EllipticInterval.galerkin_norm_sub_le_l2 zero_lt_one αL γL hαL hα hα₀ hαpos hA₁ hγ f
    (equation_12_57_le n x 1) hh
    (fun Φ hΦ ↦ FiniteElement.exists_mem_lagrangeSpaceZero_seminorm_sub_le zero_lt_one hx hn
      hmesh Φ hΦ) hu huh
  have hH1 := property_12_1 hx hn hmesh αL γL hα₀ hαae hγ f U hU hu huh
  have hMs : 0 ≤ ‖αL‖ + (1 / Real.sqrt 2) ^ 2 * ‖γL‖ := by positivity
  have hA₁0 : 0 ≤ A₁ := (abs_nonneg _).trans (hA₁ 0 (left_mem_Icc.2 zero_le_one))
  have hCreg : 0 ≤ (1 / Real.sqrt 2) ^ 2 / α₀ + 1 / Real.sqrt 2 / α₀
      + α₀⁻¹ * (‖γL‖ * ((1 / Real.sqrt 2) ^ 2 / α₀) + 1 + A₁ * (1 / Real.sqrt 2 / α₀)) := by
    have : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    positivity
  have hnorm : ((1 : ℝ) - 0) / Real.sqrt 2 = 1 / Real.sqrt 2 := by norm_num
  rw [hnorm] at hl2
  calc ‖deriv (u - uh) 0‖
      ≤ (‖αL‖ + (1 / Real.sqrt 2) ^ 2 * ‖γL‖)
          * ((1 / Real.sqrt 2) ^ 2 / α₀ + 1 / Real.sqrt 2 / α₀
            + α₀⁻¹ * (‖γL‖ * ((1 / Real.sqrt 2) ^ 2 / α₀) + 1 + A₁ * (1 / Real.sqrt 2 / α₀)))
          * h * SobolevInterval.seminorm 1 0 1 (u - uh) := hl2
    _ ≤ (‖αL‖ + (1 / Real.sqrt 2) ^ 2 * ‖γL‖)
          * ((1 / Real.sqrt 2) ^ 2 / α₀ + 1 / Real.sqrt 2 / α₀
            + α₀⁻¹ * (‖γL‖ * ((1 / Real.sqrt 2) ^ 2 / α₀) + 1 + A₁ * (1 / Real.sqrt 2 / α₀)))
          * h * (α₀⁻¹ * (‖αL‖ + (1 / Real.sqrt 2) ^ 2 * ‖γL‖)
            * (h * SobolevInterval.seminorm 2 0 1 U)) := by
        have : (0 : ℝ) ≤ (‖αL‖ + (1 / Real.sqrt 2) ^ 2 * ‖γL‖)
            * ((1 / Real.sqrt 2) ^ 2 / α₀ + 1 / Real.sqrt 2 / α₀
              + α₀⁻¹ * (‖γL‖ * ((1 / Real.sqrt 2) ^ 2 / α₀) + 1
                + A₁ * (1 / Real.sqrt 2 / α₀))) * h := by positivity
        exact mul_le_mul_of_nonneg_left hH1 this
    _ = _ := by ring

end Convergence

/-! ### The shape functions of $X_h^1$ (12.61)–(12.62) -/

section ShapeFunctions

variable {n : ℕ} {x : ℕ → ℝ}

/-- **Equation (12.61)** of [quarteroni2000numerical]. For a partition $0 = x_0 < \cdots < x_n = 1$
with $n \ge 1$, the shape function $\varphi_i$ of $X_h^1$: the continuous piecewise linear
function with $\varphi_i(x_j) = \delta_{ij}$, as an element of $H^1(0, 1)$.

The definition is `FiniteElement.hatFunction`. The nodal values are
`QuarteroniSaccoSaleri.Chapter12.equation_12_61_apply_node`.

**Generalization.** Includes a one-panel partition. The individual shape functions are defined
for all natural shape indices. -/
noncomputable def equation_12_61 (hx : IsIntervalPartition 0 1 n x) (hn : 1 ≤ n) (i : ℕ) :
    SobolevInterval 1 0 1 :=
  FiniteElement.hatFunction hx hn i

/-- **Equation (12.61)** of [quarteroni2000numerical], the interpolation property. For a partition
$0 = x_0 < \cdots < x_n = 1$ with $n \ge 1$, every index $i$ and every $j \le n$,
$\varphi_i(x_j) = \delta_{ij}$.

**Generalization.** Includes a one-panel partition. The individual shape functions are defined
for all natural shape indices. -/
theorem equation_12_61_apply_node (hx : IsIntervalPartition 0 1 n x) (hn : 1 ≤ n) {i j : ℕ}
    (hj : j ≤ n) : rep (equation_12_61 hx hn i) (x j) = if i = j then 1 else 0 :=
  FiniteElement.rep_hatFunction_node hx hn hj

/-- **Section 12.4.5** of [quarteroni2000numerical], the support of $\varphi_i$. For a partition
$0 = x_0 < \cdots < x_n = 1$ with $n \ge 1$, let $k < n$ with $i \neq k$ and $i \neq k + 1$.
Then $\varphi_i(t) = 0$ for every $t \in [x_k, x_{k+1}]$. So $\varphi_i$ vanishes outside
$I_{i-1} \cup I_i$.

**Generalization.** Includes a one-panel partition. The individual shape functions are defined
for all natural shape indices. -/
theorem equation_12_61_support (hx : IsIntervalPartition 0 1 n x) (hn : 1 ≤ n) {i k : ℕ}
    (hk : k < n) (h1 : i ≠ k) (h2 : i ≠ k + 1) {t : ℝ} (ht1 : x k ≤ t) (ht2 : t ≤ x (k + 1)) :
    rep (equation_12_61 hx hn i) t = 0 := by
  rw [equation_12_61, FiniteElement.rep_hatFunction hx hn i
    ⟨(hx.left_le hk.le).trans ht1, ht2.trans (hx.le_right hk)⟩]
  exact FiniteElement.hatFun_eq_zero_of_panel hx hk h1 h2 ht1 ht2

/-- **Section 12.4.5** of [quarteroni2000numerical], the basis of $X_h^1$. For a partition
$0 = x_0 < \cdots < x_n = 1$ with $n \ge 1$, the shape functions $\varphi_0, \ldots, \varphi_n$
form a basis of $X_h^1$. The coordinates of an element in this basis are its $n + 1$ nodal
values.

The definition is `FiniteElement.hatBasis`. The coordinates are
`QuarteroniSaccoSaleri.Chapter12.equation_12_61_basis_repr`.

**Generalization.** Includes a one-panel partition. The individual shape functions are defined
for all natural shape indices. -/
noncomputable def equation_12_61_basis (hx : IsIntervalPartition 0 1 n x) (hn : 1 ≤ n) :
    Module.Basis (Fin (n + 1)) ℝ (FiniteElement.lagrangeSpace zero_lt_one n x 1) :=
  FiniteElement.hatBasis zero_lt_one hx hn

/-- The coordinate of $v \in X_h^1$ at the index $j$ in the shape function basis is the nodal value
$v(x_j)$.

**Generalization.** Includes a one-panel partition. The individual shape functions are defined
for all natural shape indices. -/
theorem equation_12_61_basis_repr (hx : IsIntervalPartition 0 1 n x) (hn : 1 ≤ n)
    (v : FiniteElement.lagrangeSpace zero_lt_one n x 1) (j : Fin (n + 1)) :
    (equation_12_61_basis hx hn).repr v j = rep (v : SobolevInterval 1 0 1) (x (j : ℕ)) :=
  FiniteElement.hatBasis_repr zero_lt_one hx hn v j

/-- **Equation (12.62)** of [quarteroni2000numerical]. The affine map of the reference interval
$[0, 1]$ onto the element $I_i = [x_i, x_{i+1}]$:
$$x = \phi(\xi) = x_i + \xi (x_{i+1} - x_i).$$

Its inverse is the reference coordinate $\xi(x) = (x - x_i)/(x_{i+1} - x_i)$,
`FiniteElement.refCoord`.

**Generalization.** The affine and inverse formulas are real expressions on the whole line. The
inverse identity is stated for a valid partition interval. -/
noncomputable def equation_12_62 (x : ℕ → ℝ) (i : ℕ) : ℝ → ℝ := FiniteElement.affineMap x i

/-- For a partition $0 = x_0 < \cdots < x_n = 1$ and $i < n$, the affine map (12.62) inverts the
reference coordinate: $\phi(\xi(t)) = t$ for every real $t$.

**Generalization.** The affine and inverse formulas are real expressions on the whole line. The
inverse identity is stated for a valid partition interval. -/
theorem equation_12_62_refCoord (hx : IsIntervalPartition 0 1 n x) {i : ℕ} (hi : i < n) (t : ℝ) :
    equation_12_62 x i (FiniteElement.refCoord x i t) = t :=
  FiniteElement.affineMap_refCoord (hx.step i hi).ne t

/-- **Section 12.4.5** of [quarteroni2000numerical], the reference shape functions of $X_h^1$. For a
partition $0 = x_0 < \cdots < x_n = 1$ with $n \ge 1$, let $k < n$ and $t \in [x_k, x_{k+1}]$.
Then
$$\varphi_k(t) = \hat\varphi_0(\xi(t)), \qquad \varphi_{k+1}(t) = \hat\varphi_1(\xi(t)),$$
where $\hat\varphi_0(\xi) = 1 - \xi$, $\hat\varphi_1(\xi) = \xi$, and
$\xi(t) = (t - x_k)/(x_{k+1} - x_k)$ is the reference coordinate.

The reference shape functions are `FiniteElement.referenceHat`.

**Generalization.** Includes a one-panel partition. The individual shape functions are defined
for all natural shape indices. -/
theorem equation_12_62_shape (hx : IsIntervalPartition 0 1 n x) (hn : 1 ≤ n) {k : ℕ} (hk : k < n)
    {t : ℝ} (h1 : x k ≤ t) (h2 : t ≤ x (k + 1)) :
    rep (equation_12_61 hx hn k) t = FiniteElement.referenceHat 0 (FiniteElement.refCoord x k t) ∧
      rep (equation_12_61 hx hn (k + 1)) t
        = FiniteElement.referenceHat 1 (FiniteElement.refCoord x k t) := by
  have hmem : t ∈ Icc (0 : ℝ) 1 :=
    ⟨(hx.left_le hk.le).trans h1, h2.trans (hx.le_right hk)⟩
  constructor
  · rw [equation_12_61, FiniteElement.rep_hatFunction hx hn k hmem]
    exact FiniteElement.hatFun_eq_referenceHat_zero hx hk h1 h2
  · rw [equation_12_61, FiniteElement.rep_hatFunction hx hn (k + 1) hmem]
    exact FiniteElement.hatFun_eq_referenceHat_one hx hk h1 h2

end ShapeFunctions

/-! ### The quadratic shape functions (12.63)-(12.65) -/

section QuadraticShapeFunctions

variable {n : ℕ} {x : ℕ → ℝ}

/-- **Equations (12.63)–(12.64)** of [quarteroni2000numerical]. Let
$0 = x_0 < x_1 < \cdots < x_{2n} = 1$ with $n \ge 1$. The $n$ elements are $[x_{2m}, x_{2m+2}]$:
the nodes with even index are their endpoints, and the nodes with odd index are their interior
nodes. The shape function $\varphi_i$ of $X_h^2$ is the continuous piecewise quadratic function
with $\varphi_i(x_j) = \delta_{ij}$, as an element of $H^1(0, 1)$.

For an even $i$, $\varphi_i$ has two quadratic branches on the two adjacent elements. For an odd
$i$, $\varphi_i$ is a bubble supported in one element. The definition is
`FiniteElement.quadraticShape`.

**Generalization.** The interior interpolation node of each quadratic panel can be anywhere
strictly between its endpoints. -/
noncomputable def equation_12_63 (hx : IsIntervalPartition 0 1 (2 * n) x) (hn : 1 ≤ n) (i : ℕ) :
    SobolevInterval 1 0 1 :=
  FiniteElement.quadraticShape zero_lt_one hx hn i

/-- **Equations (12.63)–(12.64)** of [quarteroni2000numerical], the interpolation property. For
nodes $0 = x_0 < \cdots < x_{2n} = 1$ with $n \ge 1$, every index $i$ and every $j \le 2n$, the
quadratic shape functions satisfy $\varphi_i(x_j) = \delta_{ij}$.

**Generalization.** The interior interpolation node of each quadratic panel can be anywhere
strictly between its endpoints. -/
theorem equation_12_63_apply_node (hx : IsIntervalPartition 0 1 (2 * n) x) (hn : 1 ≤ n) {i j : ℕ}
    (hj : j ≤ 2 * n) : rep (equation_12_63 hx hn i) (x j) = if i = j then 1 else 0 :=
  FiniteElement.rep_quadraticShape_node zero_lt_one hx hn hj

/-- **Section 12.4.5** of [quarteroni2000numerical], the support of the quadratic shape functions.
For nodes $0 = x_0 < \cdots < x_{2n} = 1$ with $n \ge 1$, let $m < n$ and let $i$ differ from
$2m$, $2m + 1$ and $2m + 2$. Then $\varphi_i(t) = 0$ for every $t \in [x_{2m}, x_{2m+2}]$.

So $\varphi_i$ vanishes on every element none of whose three nodes is $x_i$. In particular, the
bubble $\varphi_{2m+1}$ is supported in the element $[x_{2m}, x_{2m+2}]$.

**Generalization.** The interior interpolation node of each quadratic panel can be anywhere
strictly between its endpoints. -/
theorem equation_12_63_support (hx : IsIntervalPartition 0 1 (2 * n) x) (hn : 1 ≤ n) {i m : ℕ}
    (hm : m < n) (h0 : i ≠ 2 * m) (h1 : i ≠ 2 * m + 1) (h2 : i ≠ 2 * m + 2) {t : ℝ}
    (ht1 : x (2 * m) ≤ t) (ht2 : t ≤ x (2 * m + 2)) : rep (equation_12_63 hx hn i) t = 0 :=
  FiniteElement.rep_quadraticShape_eq_zero_of_panel zero_lt_one hx hn hm h0 h1 h2 ht1 ht2

/-- **Section 12.4.5** of [quarteroni2000numerical], the basis of $X_h^2$. For nodes
$0 = x_0 < \cdots < x_{2n} = 1$ with $n \ge 1$, the quadratic shape functions
$\varphi_0, \ldots, \varphi_{2n}$ form a basis of $X_h^2$ on the elements $[x_{2m}, x_{2m+2}]$.
The coordinates of an element in this basis are its $2n + 1$ nodal values.

In particular $\dim X_h^2 = 2n + 1$, the value $nk + 1$ of the book at $k = 2$. The space
$X_h^2$ is `FiniteElement.lagrangeSpace` on the even nodes `FiniteElement.evenNodes x`, and the
basis is `FiniteElement.quadraticBasis`.

**Generalization.** The interior interpolation node of each quadratic panel can be anywhere
strictly between its endpoints. -/
noncomputable def equation_12_63_basis (hx : IsIntervalPartition 0 1 (2 * n) x) (hn : 1 ≤ n) :
    Module.Basis (Fin (2 * n + 1)) ℝ
      (FiniteElement.lagrangeSpace zero_lt_one n (FiniteElement.evenNodes x) 2) :=
  FiniteElement.quadraticBasis zero_lt_one hx hn

/-- **Equation (12.65)** of [quarteroni2000numerical]. For nodes $0 = x_0 < \cdots < x_{2n} = 1$
with $n \ge 1$, let $m < n$, and assume that the interior node is the midpoint,
$x_{2m+1} = (x_{2m} + x_{2m+2})/2$. Then for every $t \in [x_{2m}, x_{2m+2}]$,
$$\varphi_{2m}(t) = \hat\varphi_0(\xi(t)), \qquad \varphi_{2m+1}(t) = \hat\varphi_1(\xi(t)),
  \qquad \varphi_{2m+2}(t) = \hat\varphi_2(\xi(t)),$$
where $\hat\varphi_0(\xi) = (1 - \xi)(1 - 2\xi)$, $\hat\varphi_1(\xi) = 4(1 - \xi)\xi$,
$\hat\varphi_2(\xi) = \xi(2\xi - 1)$, and $\xi(t) = (t - x_{2m})/(x_{2m+2} - x_{2m})$ is the
reference coordinate of the element.

The midpoint hypothesis is needed here but not in (12.63)–(12.64): those formulas give the
Lagrange basis of the three nodes of the element for any interior node. The reference shape
functions are `FiniteElement.referenceQuadratic`.

**Generalization.** Only the selected panel needs its interior point at the midpoint for these
reference identities. -/
theorem equation_12_65 (hx : IsIntervalPartition 0 1 (2 * n) x) (hn : 1 ≤ n) {m : ℕ} (hm : m < n)
    (hmid : x (2 * m + 1) = (x (2 * m) + x (2 * m + 2)) / 2) {t : ℝ} (h1 : x (2 * m) ≤ t)
    (h2 : t ≤ x (2 * m + 2)) :
    rep (equation_12_63 hx hn (2 * m)) t
        = FiniteElement.referenceQuadratic 0
          (FiniteElement.refCoord (FiniteElement.evenNodes x) m t) ∧
      rep (equation_12_63 hx hn (2 * m + 1)) t
        = FiniteElement.referenceQuadratic 1
          (FiniteElement.refCoord (FiniteElement.evenNodes x) m t) ∧
      rep (equation_12_63 hx hn (2 * m + 2)) t
        = FiniteElement.referenceQuadratic 2
          (FiniteElement.refCoord (FiniteElement.evenNodes x) m t) :=
  FiniteElement.rep_quadraticShape_eq_referenceQuadratic zero_lt_one hx hn hm hmid h1 h2

/-- **Equation (12.57)** of [quarteroni2000numerical] for $k = 2$. For nodes
$0 = x_0 < \cdots < x_{2n} = 1$ with $n \ge 1$ and an index $i$ with $i \neq 0$ and $i \neq 2n$,
the quadratic shape function $\varphi_i$ lies in $X_h^{2,0}$.

**Generalization.** The interior interpolation node of each quadratic panel can be anywhere
strictly between its endpoints. -/
theorem equation_12_63_mem_zero (hx : IsIntervalPartition 0 1 (2 * n) x) (hn : 1 ≤ n) {i : ℕ}
    (h0 : i ≠ 0) (hi : i ≠ 2 * n) :
    equation_12_63 hx hn i
      ∈ FiniteElement.lagrangeSpaceZero zero_lt_one n (FiniteElement.evenNodes x) 2 :=
  FiniteElement.quadraticShape_mem_lagrangeSpaceZero zero_lt_one hx hn h0 hi

end QuadraticShapeFunctions

/-- **Equation (12.66)** of [quarteroni2000numerical]. The hierarchical functions
$\hat\psi_0(\xi) = 1 - \xi$, $\hat\psi_1(\xi) = (1 - \xi)\xi$ and $\hat\psi_2(\xi) = \xi$ on the
reference interval are linearly independent.

Since they are three polynomials of degree at most $2$, they form a basis of $\mathbb{P}_2$. The
book checks that $\alpha_0 + \xi(\alpha_1 - \alpha_0 + \alpha_2) - \alpha_1 \xi^2 \equiv 0$
forces $\alpha_0 = \alpha_1 = \alpha_2 = 0$. The functions are
`FiniteElement.referenceHierarchical`, as functions on $\mathbb{R}$.

**Partial.** Proves independence of the three polynomial functions on the real line.

**Reading.** Proves independence of polynomial functions on ℝ, without explicitly stating spanning
on the interval.
-/
theorem equation_12_66 : LinearIndependent ℝ FiniteElement.referenceHierarchical :=
  FiniteElement.referenceHierarchical_linearIndependent

/-! ### The structure and conditioning of $A_{fe}$ (Section 12.4.5) -/

section Stiffness

open scoped Matrix.Norms.L2Operator

variable {n : ℕ} {x : ℕ → ℝ}

/-- **Section 12.4.5** of [quarteroni2000numerical], the stiffness matrix $A_{fe}$ for $k = 1$. For
a partition $0 = x_0 < \cdots < x_n = 1$ with $n \ge 1$ and any coefficients
$\alpha, \beta, \gamma \in L^\infty(0, 1)$, the entry $a_{ij} = a(\varphi_j, \varphi_i)$ is $0$
when $|i - j| \ge 2$.

The supports of $\varphi_i$ and $\varphi_j$ then meet in a set of measure zero. The indices
$i, j$ are natural numbers.

**Generalization.** Uses essentially bounded coefficients and permits a one-panel partition. -/
theorem equation_12_61_stiffness (hx : IsIntervalPartition 0 1 n x) (hn : 1 ≤ n)
    (α β γ : Lp ℝ ⊤ (volume.restrict (Ioo (0 : ℝ) 1))) {i j : ℕ}
    (hij : i + 1 < j ∨ j + 1 < i) :
    FiniteElement.stiffnessMatrix 0 1 α β γ (fun k : ℕ ↦ equation_12_61 hx hn k) i j = 0 :=
  FiniteElement.stiffnessMatrix_eq_zero_of_lt hx hn α β γ hij

/-- **Section 12.4.5** of [quarteroni2000numerical]. For a partition $0 = x_0 < \cdots < x_n = 1$
with $n \ge 1$ and any coefficients $\alpha, \beta, \gamma \in L^\infty(0, 1)$, the stiffness
matrix $A_{fe}$ in the basis $\varphi_1, \ldots, \varphi_{n-1}$ of $V_h = X_h^{1,0}$ is
tridiagonal.

Tridiagonal is `Matrix.IsTridiagonal`. The matrix is indexed by `Fin (n - 1)`, and the index $k$
stands for $\varphi_{k+1}$.

**Generalization.** Uses essentially bounded coefficients and permits a one-panel partition. -/
theorem equation_12_61_stiffness_tridiagonal (hx : IsIntervalPartition 0 1 n x) (hn : 1 ≤ n)
    (α β γ : Lp ℝ ⊤ (volume.restrict (Ioo (0 : ℝ) 1))) :
    (FiniteElement.stiffnessMatrix 0 1 α β γ
      fun k : Fin (n - 1) ↦ equation_12_61 hx hn ((k : ℕ) + 1)).IsTridiagonal :=
  FiniteElement.isTridiagonal_stiffnessMatrix hx hn α β γ

/-- **Section 12.4.5** of [quarteroni2000numerical], the condition number of $A_{fe}$. Consider the
model problem $-u'' = f$, that is $\alpha = 1$ and $\beta = \gamma = 0$, on a uniform partition
$0 = x_0 < \cdots < x_n = 1$ with $n \ge 1$ and step $h > 0$, so that $h = 1/n$. Then the
stiffness matrix $A_{fe}$ in the basis $\varphi_1, \ldots, \varphi_{n-1}$ of $X_h^{1,0}$ has the
spectral condition number
$$K_2(A_{fe}) = \|A_{fe}\|_2 \, \|A_{fe}^{-1}\|_2 = \cot^2\Big(\frac{\pi h}{2}\Big).$$

The book quotes $K_2(A_{fe}) = O(h^{-2})$ from [quarteroni1994numerical]. This follows from
`Matrix.condNumber_symmTridiagonalToeplitz_neg_one_two_le`, which gives
$\cot^2(\pi h / 2) \le 4/(\pi h)^2$. The norm is the operator norm induced by the Euclidean
norm, and the right-hand side is written $\cot^2(\pi / (2n))$.

**Specialization.** Gives an exact condition number for uniform partitions and the pure unit
diffusion model. The text states a more general asymptotic estimate. -/
theorem equation_12_61_stiffness_condNumber (hx : IsIntervalPartition 0 1 n x) (hn : 1 ≤ n)
    {h : ℝ} (hh : 0 < h) (huni : ∀ k < n, x (k + 1) - x k = h) :
    ‖FiniteElement.stiffnessMatrix 0 1 (EllipticInterval.constLinf 0 1 1)
        (EllipticInterval.constLinf 0 1 0) (EllipticInterval.constLinf 0 1 0)
        fun i : Fin (n - 1) ↦ equation_12_61 hx hn ((i : ℕ) + 1)‖
      * ‖(FiniteElement.stiffnessMatrix 0 1 (EllipticInterval.constLinf 0 1 1)
        (EllipticInterval.constLinf 0 1 0) (EllipticInterval.constLinf 0 1 0)
        fun i : Fin (n - 1) ↦ equation_12_61 hx hn ((i : ℕ) + 1))⁻¹‖
      = Real.cot (Real.pi / (2 * (n : ℝ))) ^ 2 :=
  FiniteElement.condNumber_stiffnessMatrix_model hx hn hh huni

end Stiffness

/-! ### Example 12.1 -/

/-- **Example 12.1** of [quarteroni2000numerical], the exact solution of (12.67): the function
$$u(x) = u_0 \frac{\cosh(m(L - x))}{\cosh(mL)}, \qquad x \in \mathbb{R}.$$

**Generalization.** The exact rod solution and derivative identities use real parameters on the
whole line. The governing equation uses the relation $\mu A m^2=\sigma p$. -/
noncomputable def example_12_1_solution (L u₀ m : ℝ) : ℝ → ℝ :=
  fun x ↦ u₀ * Real.cosh (m * (L - x)) / Real.cosh (m * L)

/-- The function $u$ of Example 12.1 has the derivative $u'(x) = -u_0 m \sinh(m(L - x)) / \cosh(mL)$
at every $x \in \mathbb{R}$.

**Generalization.** The exact rod solution and derivative identities use real parameters on the
whole line. The governing equation uses the relation $\mu A m^2=\sigma p$. -/
theorem hasDerivAt_example_12_1_solution (L u₀ m x : ℝ) :
    HasDerivAt (example_12_1_solution L u₀ m)
      (-(u₀ * m * Real.sinh (m * (L - x))) / Real.cosh (m * L)) x := by
  have h1 : HasDerivAt (fun t : ℝ ↦ m * (L - t)) (-m) x := by
    simpa using ((hasDerivAt_const x L).sub (hasDerivAt_id x)).const_mul m
  have h2 : HasDerivAt (fun t : ℝ ↦ Real.cosh (m * (L - t)))
      (Real.sinh (m * (L - x)) * (-m)) x := h1.cosh
  exact ((h2.const_mul u₀).div_const (Real.cosh (m * L))).congr_deriv (by ring)

/-- The derivative of the function $u$ of Example 12.1 is
$u'(x) = -u_0 m \sinh(m(L - x)) / \cosh(mL)$.

**Generalization.** The exact rod solution and derivative identities use real parameters on the
whole line. The governing equation uses the relation $\mu A m^2=\sigma p$. -/
theorem deriv_example_12_1_solution (L u₀ m : ℝ) :
    deriv (example_12_1_solution L u₀ m)
      = fun x ↦ -(u₀ * m * Real.sinh (m * (L - x))) / Real.cosh (m * L) :=
  funext fun x ↦ (hasDerivAt_example_12_1_solution L u₀ m x).deriv

/-- The function $u$ of Example 12.1 satisfies $u''(x) = m^2 u(x)$ for every $x \in \mathbb{R}$.

**Generalization.** The exact rod solution and derivative identities use real parameters on the
whole line. The governing equation uses the relation $\mu A m^2=\sigma p$. -/
theorem iteratedDeriv_two_example_12_1_solution (L u₀ m x : ℝ) :
    iteratedDeriv 2 (example_12_1_solution L u₀ m) x
      = m ^ 2 * example_12_1_solution L u₀ m x := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one,
    deriv_example_12_1_solution]
  have h1 : HasDerivAt (fun t : ℝ ↦ m * (L - t)) (-m) x := by
    simpa using ((hasDerivAt_const x L).sub (hasDerivAt_id x)).const_mul m
  have h2 : HasDerivAt (fun t : ℝ ↦ Real.sinh (m * (L - t)))
      (Real.cosh (m * (L - x)) * (-m)) x := h1.sinh
  have h3 : HasDerivAt (fun t : ℝ ↦ -(u₀ * m * Real.sinh (m * (L - t))) / Real.cosh (m * L))
      (m ^ 2 * example_12_1_solution L u₀ m x) x := by
    refine (((h2.const_mul (u₀ * m)).neg).div_const (Real.cosh (m * L))).congr_deriv ?_
    rw [example_12_1_solution]
    field_simp
  exact h3.deriv

/-- The function $u$ of Example 12.1 satisfies the left boundary condition $u(0) = u_0$ of (12.67).

**Generalization.** The exact rod solution and derivative identities use real parameters on the
whole line. The governing equation uses the relation $\mu A m^2=\sigma p$. -/
@[simp]
theorem example_12_1_solution_zero (L u₀ m : ℝ) : example_12_1_solution L u₀ m 0 = u₀ := by
  rw [example_12_1_solution, sub_zero, mul_div_assoc, div_self (Real.cosh_pos _).ne', mul_one]

/-- The function $u$ of Example 12.1 satisfies the right boundary condition $u'(L) = 0$ of (12.67).

**Generalization.** The exact rod solution and derivative identities use real parameters on the
whole line. The governing equation uses the relation $\mu A m^2=\sigma p$. -/
@[simp]
theorem deriv_example_12_1_solution_apply (L u₀ m : ℝ) :
    deriv (example_12_1_solution L u₀ m) L = 0 := by
  rw [deriv_example_12_1_solution]
  simp

/-- **Example 12.1** of [quarteroni2000numerical]. Let $\mu, A, \sigma, p, L, u_0, m$ be real
numbers with $\mu A m^2 = \sigma p$. Then $u(x) = u_0 \cosh(m(L - x)) / \cosh(mL)$ satisfies
$$-\mu A u''(x) + \sigma p \, u(x) = 0 \quad \text{for every } x \in \mathbb{R}, \qquad u(0) =
  u_0, \qquad u'(L) = 0,$$
so it solves the boundary value problem (12.67) on $(0, L)$.

The book writes the hypothesis as $m^2 = \sigma p / (\mu A)$; the statement uses
$\mu A m^2 = \sigma p$, which needs no division.

**Generalization.** The exact rod solution and derivative identities use real parameters on the
whole line. The governing equation uses the relation $\mu A m^2=\sigma p$. -/
theorem example_12_1 {mu A sigma p L u₀ m : ℝ} (hm : mu * A * m ^ 2 = sigma * p) :
    (∀ x : ℝ, -(mu * A) * iteratedDeriv 2 (example_12_1_solution L u₀ m) x
        + sigma * p * example_12_1_solution L u₀ m x = 0) ∧
      example_12_1_solution L u₀ m 0 = u₀ ∧ deriv (example_12_1_solution L u₀ m) L = 0 := by
  refine ⟨fun x ↦ ?_, example_12_1_solution_zero L u₀ m, deriv_example_12_1_solution_apply L u₀ m⟩
  rw [iteratedDeriv_two_example_12_1_solution, ← hm]
  ring

/-! ### The spectral (generalized Galerkin) method (12.68)-(12.69) -/

section Spectral

open Polynomial

variable {n : ℕ} {x w : Fin (n + 1) → ℝ}

/-- **Section 12.3** of [quarteroni2000numerical], the space $\mathbb{P}_n^0$: the real polynomials
of degree at most $n$ that vanish at $-1$ and at $1$, as a subspace of $\mathbb{R}[X]$.

The spectral method (12.68) is a generalized Galerkin method on this space. The trial space is
not a subspace of a function space with the $H^1$ norm, because the discrete form (12.69)
evaluates derivatives at the Gauss–Lobatto nodes.

**Reading.** The spectral polynomials vanish at $\pm1$, the endpoints of the collocation
interval. -/
noncomputable def polyZero (n : ℕ) : Submodule ℝ ℝ[X] :=
  Polynomial.degreeLE ℝ (n : WithBot ℕ) ⊓ LinearMap.ker (Polynomial.leval (-1 : ℝ))
    ⊓ LinearMap.ker (Polynomial.leval (1 : ℝ))

/-- A polynomial $p$ lies in $\mathbb{P}_n^0$ if and only if $\deg p \le n$, $p(-1) = 0$ and
$p(1) = 0$. This is the form of the conditions in
`QuarteroniSaccoSaleri.Chapter12.equation_12_36`.

**Reading.** The spectral polynomials vanish at $\pm1$, the endpoints of the collocation
interval. -/
theorem mem_polyZero {p : ℝ[X]} :
    p ∈ polyZero n ↔ p.natDegree ≤ n ∧ p.eval (-1) = 0 ∧ p.eval 1 = 0 := by
  simp only [polyZero, Submodule.mem_inf, Polynomial.mem_degreeLE, LinearMap.mem_ker,
    Polynomial.leval_apply, Polynomial.natDegree_le_iff_degree_le, and_assoc]

/-- The discrete pairing $(c \cdot Dp, Eq)_n = \sum_k c(x_k) (Dp)(x_k) (Eq)(x_k) w_k$ of the
Gauss–Lobatto rule with nodes $x_k$ and weights $w_k$, for a function $c$ and two linear maps
$D$, $E$ on $\mathbb{R}[X]$. It is a bilinear form on $\mathbb{R}[X]$, and the terms of (12.69)
are of this form. -/
noncomputable def spectralPairing (n : ℕ) (x w : Fin (n + 1) → ℝ) (c : ℝ → ℝ)
    (D E : ℝ[X] →ₗ[ℝ] ℝ[X]) : ℝ[X] →ₗ[ℝ] ℝ[X] →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun p q ↦ ∑ k, c (x k) * (D p).eval (x k) * ((E q).eval (x k)) * w k)
    (fun p₁ p₂ q ↦ by
      simp only [map_add, Polynomial.eval_add]
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ ↦ by ring)
    (fun a p q ↦ by
      simp only [map_smul, Polynomial.eval_smul, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ ↦ by ring)
    (fun p q₁ q₂ ↦ by
      simp only [map_add, Polynomial.eval_add]
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ ↦ by ring)
    (fun a p q ↦ by
      simp only [map_smul, Polynomial.eval_smul, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ ↦ by ring)

/-- The discrete pairing is the discrete scalar product (12.37) of $c \cdot Dp$ and $Eq$. -/
theorem spectralPairing_apply (n : ℕ) (x w : Fin (n + 1) → ℝ) (c : ℝ → ℝ)
    (D E : ℝ[X] →ₗ[ℝ] ℝ[X]) (p q : ℝ[X]) :
    spectralPairing n x w c D E p q
      = equation_12_37 n x w (fun t ↦ c t * (D p).eval t) (fun t ↦ (E q).eval t) := by
  rw [equation_12_37_eq]
  rfl

/-- **Equation (12.69)** of [quarteroni2000numerical]. For nodes $x_0, \ldots, x_n$, weights
$w_0, \ldots, w_n$ and coefficient functions $\alpha, \beta, \gamma$, the discrete bilinear form
on $\mathbb{R}[X]$
$$a_n(u, v) = (\alpha u', v')_n + (\beta u', v)_n + (\gamma u, v)_n,$$
where $(\cdot, \cdot)_n$ is the discrete scalar product (12.37).

The form arises from the form (12.44) when every integral is replaced by the Gauss–Lobatto
formula (12.37).

**Generalization.** The sampled form and load accept arbitrary nodes, weights and coefficient
values. The collocation theorem uses a Lobatto rule. -/
noncomputable def equation_12_69 (n : ℕ) (x w : Fin (n + 1) → ℝ) (α β γ : ℝ → ℝ) :
    ℝ[X] →ₗ[ℝ] ℝ[X] →ₗ[ℝ] ℝ :=
  spectralPairing n x w α Polynomial.derivative Polynomial.derivative
    + spectralPairing n x w β Polynomial.derivative LinearMap.id
    + spectralPairing n x w γ LinearMap.id LinearMap.id

/-- The discrete form (12.69) is the sum of three discrete scalar products (12.37): $a_n(p, q) =
(\alpha p', q')_n + (\beta p', q)_n + (\gamma p, q)_n$.

**Generalization.** The sampled form and load accept arbitrary nodes, weights and coefficient
values. The collocation theorem uses a Lobatto rule. -/
theorem equation_12_69_apply (n : ℕ) (x w : Fin (n + 1) → ℝ) (α β γ : ℝ → ℝ) (p q : ℝ[X]) :
    equation_12_69 n x w α β γ p q
      = equation_12_37 n x w (fun t ↦ α t * (derivative p).eval t)
          (fun t ↦ (derivative q).eval t)
        + equation_12_37 n x w (fun t ↦ β t * (derivative p).eval t) (fun t ↦ q.eval t)
        + equation_12_37 n x w (fun t ↦ γ t * p.eval t) (fun t ↦ q.eval t) := by
  simp only [equation_12_69, LinearMap.add_apply, spectralPairing_apply]
  rfl

/-- **Equation (12.68)** of [quarteroni2000numerical], the discrete load functional. For nodes
$x_k$, weights $w_k$ and a function $f$, the linear functional
$v \mapsto (f, v)_n = \sum_k f(x_k) v(x_k) w_k$ on $\mathbb{R}[X]$.

**Generalization.** The sampled form and load accept arbitrary nodes, weights and coefficient
values. The collocation theorem uses a Lobatto rule. -/
noncomputable def spectralLoad (n : ℕ) (x w : Fin (n + 1) → ℝ) (f : ℝ → ℝ) : ℝ[X] →ₗ[ℝ] ℝ where
  toFun q := ∑ k, f (x k) * q.eval (x k) * w k
  map_add' q₁ q₂ := by
    simp only [Polynomial.eval_add]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ ↦ by ring
  map_smul' a q := by
    simp only [Polynomial.eval_smul, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ ↦ by ring

/-- The discrete load functional is the discrete scalar product (12.37) with $f$.

**Generalization.** The sampled form and load accept arbitrary nodes, weights and coefficient
values. The collocation theorem uses a Lobatto rule. -/
theorem spectralLoad_apply (n : ℕ) (x w : Fin (n + 1) → ℝ) (f : ℝ → ℝ) (q : ℝ[X]) :
    spectralLoad n x w f q = equation_12_37 n x w f (fun t ↦ q.eval t) := by
  rw [equation_12_37_eq]
  rfl

/-- **Equation (12.68)** of [quarteroni2000numerical] (the spectral method). For nodes
$x_0, \ldots, x_n$, weights $w_0, \ldots, w_n$ and functions $\alpha, \beta, \gamma, f$, a
polynomial $u_n$ **solves the spectral method** if $u_n \in \mathbb{P}_n^0$ and
$$a_n(u_n, v_n) = (f, v_n)_n \quad \text{for every } v_n \in \mathbb{P}_n^0,$$
where $a_n$ is the discrete form (12.69).

The definition is `IsGeneralizedGalerkinSolution` on the module $\mathbb{R}[X]$. It is not a
Galerkin method, because $a_n$ is not the form $a$ of (12.44) and the trial space has no norm in
which $a_n$ is bounded.

**Generalization.** The sampled form and load accept arbitrary nodes, weights and coefficient
values. The collocation theorem uses a Lobatto rule. -/
def equation_12_68 (n : ℕ) (x w : Fin (n + 1) → ℝ) (α β γ f : ℝ → ℝ) (u : ℝ[X]) : Prop :=
  IsGeneralizedGalerkinSolution (equation_12_69 n x w α β γ) (spectralLoad n x w f)
    (polyZero n) u

/-- Integration by parts for polynomials: if $q(-1) = q(1) = 0$, then $\int_{-1}^1 p' q' \, dt =
-\int_{-1}^1 p'' q \, dt$ for every polynomial $p$. -/
theorem integral_deriv_mul_deriv_eq_neg {p q : ℝ[X]} (hq1 : q.eval (-1) = 0)
    (hq2 : q.eval 1 = 0) :
    ∫ t in (-1 : ℝ)..1, (derivative p).eval t * (derivative q).eval t
      = -∫ t in (-1 : ℝ)..1, (derivative (derivative p)).eval t * q.eval t := by
  have hu : ∀ t ∈ Set.uIcc (-1 : ℝ) 1,
      HasDerivAt (fun s ↦ (derivative p).eval s) ((derivative (derivative p)).eval t) t :=
    fun t _ ↦ (derivative p).hasDerivAt t
  have hv : ∀ t ∈ Set.uIcc (-1 : ℝ) 1,
      HasDerivAt (fun s ↦ q.eval s) ((derivative q).eval t) t := fun t _ ↦ q.hasDerivAt t
  have hu' : IntervalIntegrable (fun t ↦ (derivative (derivative p)).eval t) volume (-1) 1 :=
    ((derivative (derivative p)).continuous_aeval).intervalIntegrable _ _
  have hv' : IntervalIntegrable (fun t ↦ (derivative q).eval t) volume (-1) 1 :=
    ((derivative q).continuous_aeval).intervalIntegrable _ _
  have key := intervalIntegral.integral_deriv_mul_eq_sub (u := fun s ↦ (derivative p).eval s)
    (v := fun s ↦ q.eval s) (u' := fun t ↦ (derivative (derivative p)).eval t)
    (v' := fun t ↦ (derivative q).eval t) hu hv hu' hv'
  rw [hq1, hq2, mul_zero, mul_zero, sub_zero] at key
  have hsplit : (∫ t in (-1 : ℝ)..1, ((derivative (derivative p)).eval t * q.eval t
        + (derivative p).eval t * (derivative q).eval t))
      = (∫ t in (-1 : ℝ)..1, (derivative (derivative p)).eval t * q.eval t)
        + ∫ t in (-1 : ℝ)..1, (derivative p).eval t * (derivative q).eval t :=
    intervalIntegral.integral_add (hu'.mul_continuousOn q.continuous_aeval.continuousOn)
      (hv'.continuousOn_mul (derivative p).continuous_aeval.continuousOn)
  rw [hsplit] at key
  linarith

/-- **Equation (12.69)** of [quarteroni2000numerical] for the model problem. Let $x_0, \ldots, x_n$
and $w_0, \ldots, w_n$ be the Legendre–Gauss–Lobatto nodes and weights, and let
$p, q \in \mathbb{P}_n^0$. With $\alpha = 1$ and $\beta = \gamma = 0$,
$$a_n(p, q) = (-p'', q)_n,$$
which is the discrete operator of (12.38).

Both sides are exact integrals: the Gauss–Lobatto rule integrates $p' q'$ and $p'' q$ exactly,
because their degrees are at most $2n - 2$. So the identity is the integration by parts
$\int p' q' = -\int p'' q$. -/
theorem equation_12_69_model (hx : IsLegendreLobatto n x w) {p q : ℝ[X]}
    (hp : p ∈ polyZero n) (hq : q ∈ polyZero n) :
    equation_12_69 n x w 1 0 0 p q
      = equation_12_37 n x w (fun t ↦ -(derivative (derivative p)).eval t)
        (fun t ↦ q.eval t) := by
  obtain ⟨hpd, -, -⟩ := mem_polyZero.1 hp
  obtain ⟨hqd, hq1, hq2⟩ := mem_polyZero.1 hq
  have hdeg1 : (derivative p * derivative q).degree ≤ ((2 * n - 1 : ℕ) : WithBot ℕ) := by
    rw [← Polynomial.natDegree_le_iff_degree_le]
    have h1 := Polynomial.natDegree_derivative_le p
    have h2 := Polynomial.natDegree_derivative_le q
    have h3 := Polynomial.natDegree_mul_le (p := derivative p) (q := derivative q)
    omega
  have hdeg2 : (-derivative (derivative p) * q).degree ≤ ((2 * n - 1 : ℕ) : WithBot ℕ) := by
    rw [← Polynomial.natDegree_le_iff_degree_le]
    have h1 := Polynomial.natDegree_derivative_le p
    have h2 := Polynomial.natDegree_derivative_le (derivative p)
    have h3 := Polynomial.natDegree_mul_le (p := -derivative (derivative p)) (q := q)
    rw [Polynomial.natDegree_neg] at h3
    omega
  have hzero : ∀ (c : ℝ → ℝ), c = 0 → ∀ u : ℝ → ℝ,
      equation_12_37 n x w (fun t ↦ c t * u t) (fun t ↦ q.eval t) = 0 := by
    rintro c rfl u
    rw [equation_12_37_eq]
    exact Finset.sum_eq_zero fun k _ ↦ by simp
  rw [equation_12_69_apply, hzero 0 rfl _, hzero 0 rfl _, add_zero, add_zero]
  have h1 : equation_12_37 n x w (fun t ↦ (1 : ℝ → ℝ) t * (derivative p).eval t)
      (fun t ↦ (derivative q).eval t)
      = ∫ t in (-1 : ℝ)..1, (derivative p).eval t * (derivative q).eval t := by
    rw [show (fun t ↦ (1 : ℝ → ℝ) t * (derivative p).eval t) = fun t ↦ (derivative p).eval t by
      funext t; simp]
    exact equation_12_37_exact hx hdeg1
  have h2 : equation_12_37 n x w (fun t ↦ -(derivative (derivative p)).eval t)
      (fun t ↦ q.eval t)
      = ∫ t in (-1 : ℝ)..1, (-derivative (derivative p)).eval t * q.eval t := by
    have := equation_12_37_exact hx (P := -derivative (derivative p)) (Q := q) hdeg2
    simpa using this
  rw [h1, h2]
  rw [integral_deriv_mul_deriv_eq_neg (p := p) hq1 hq2]
  rw [← intervalIntegral.integral_neg]
  exact intervalIntegral.integral_congr fun t _ ↦ by simp

/-- **Section 12.4.7** of [quarteroni2000numerical], the spectral method as a collocation method.
Let $x_0, \ldots, x_n$ and $w_0, \ldots, w_n$ be the Legendre–Gauss–Lobatto nodes and weights,
and let $f$ be a function. For the model problem $-u'' = f$, that is $\alpha = 1$ and
$\beta = \gamma = 0$, a polynomial $p$ solves the spectral method (12.68) if and only if it
solves the collocation problem (12.36).

With these coefficients the form (12.69) is $(-u_n'', v_n)_n$ on $\mathbb{P}_n^0$, so (12.68) is
the discrete weak form (12.38), which is `QuarteroniSaccoSaleri.Chapter12.equation_12_38`. -/
theorem equation_12_68_eq_collocation (hx : IsLegendreLobatto n x w) (f : ℝ → ℝ) (p : ℝ[X]) :
    equation_12_68 n x w 1 0 0 f p ↔ equation_12_36 n x f p := by
  rw [equation_12_38 hx f p, equation_12_68, IsGeneralizedGalerkinSolution]
  constructor
  · rintro ⟨hp, hvar⟩
    obtain ⟨hpd, hp1, hp2⟩ := mem_polyZero.1 hp
    refine ⟨hpd, hp1, hp2, fun q hqd hq1 hq2 ↦ ?_⟩
    have hqmem : q ∈ polyZero n := mem_polyZero.2 ⟨hqd, hq1, hq2⟩
    have h := hvar q hqmem
    rw [equation_12_69_model hx hp hqmem, spectralLoad_apply] at h
    exact h
  · rintro ⟨hpd, hp1, hp2, hvar⟩
    have hp : p ∈ polyZero n := mem_polyZero.2 ⟨hpd, hp1, hp2⟩
    refine ⟨hp, fun q hqmem ↦ ?_⟩
    obtain ⟨hqd, hq1, hq2⟩ := mem_polyZero.1 hqmem
    rw [equation_12_69_model hx hp hqmem, spectralLoad_apply]
    exact hvar q hqd hq1 hq2

end Spectral

end QuarteroniSaccoSaleri.Chapter12
