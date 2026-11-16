/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Variational.AdvectionDiffusion

/-!
# Quarteroni, Sacco and Saleri, Section 12.5: Advection–diffusion equations

This module formalizes Section 12.5 of [quarteroni2000numerical]. The model problem (12.70) is
$-\varepsilon u'' + \beta u' = 0$ on $(0, 1)$ with $u(0) = 0$, $u(1) = 1$ and
$\varepsilon, \beta > 0$, $\varepsilon / \beta \ll 1$. Advection dominates diffusion, the global
Péclet number $\mathrm{Pe}_{gl} = |\beta| L / (2\varepsilon)$ (12.71) is large, and the exact
solution $u(x) = (e^{\beta x / \varepsilon} - 1)/(e^{\beta / \varepsilon} - 1)$ has a boundary layer
of width $O(\varepsilon / \beta)$ at $x = 1$. The piecewise linear Galerkin method on a uniform mesh
gives the difference equation (12.75)–(12.76), $(\mathrm{Pe} - 1) u_{i+1} + 2 u_i -
(\mathrm{Pe} + 1) u_{i-1} = 0$, in the local Péclet number
$\mathrm{Pe} = |\beta| h / (2\varepsilon)$. Its solution $u_i = (1 - \rho^i)/(1 - \rho^n)$ with
$\rho = (1 + \mathrm{Pe})/(1 - \mathrm{Pe})$ oscillates when $\mathrm{Pe} > 1$.

The same equations are the centred finite differences (12.77). The upwind difference (12.78) for
$u'$ is the centred scheme with the larger diffusion $\varepsilon_h = \varepsilon(1 + \mathrm{Pe})$
(12.79)–(12.81), the numerical viscosity. In general (12.82) takes $\varepsilon_h = \varepsilon(1 +
\phi(\mathrm{Pe}))$: $\phi^{UP}(t) = t$ is upwinding, and $\phi^{SG}(t) = t - 1 + B(2t)$ (12.83),
with the Bernoulli function $B$, is the exponential fitting of Scharfetter and Gummel, for which the
scheme is nodally exact (Remark 12.6). For both choices the stabilized Péclet number
$\mathrm{Pe}^* = \mathrm{Pe}/(1 + \phi(\mathrm{Pe}))$ is below $1$ for every mesh size, so the
matrix of the scheme is an M-matrix (Exercise 12.13) and the discrete solution satisfies a maximum
principle. The viscosity carries over to finite elements (12.84), and Theorem 12.4 gives the
convergence rates. The proofs specialize `Numlib.Variational.AdvectionDiffusion`.

## Main definitions

* (12.71), `QuarteroniSaccoSaleri.Chapter12.equation_12_71`: the global Péclet number
  $\mathrm{Pe}_{gl} = |\beta| L / (2\varepsilon)$.
* Section 12.5.1, `QuarteroniSaccoSaleri.Chapter12.meshPeclet`: the local Péclet number
  $\mathrm{Pe} = |\beta| h / (2\varepsilon)$.
* (12.72)–(12.73), `QuarteroniSaccoSaleri.Chapter12.equation_12_72`: the piecewise linear Galerkin
  approximation of (12.70).
* (12.82), `QuarteroniSaccoSaleri.Chapter12.equation_12_82`: the viscosity $\varepsilon_h =
  \varepsilon(1 + \phi(\mathrm{Pe}))$.
* (12.83), `QuarteroniSaccoSaleri.Chapter12.equation_12_83`: the Scharfetter–Gummel function
  $\phi^{SG}(t) = t - 1 + B(2t)$.
* (12.84), `QuarteroniSaccoSaleri.Chapter12.equation_12_84`: the stabilized bilinear form $a_h$.
* (12.84), `QuarteroniSaccoSaleri.Chapter12.equation_12_84_problem`: the stabilized finite element
  problem for (12.70).

## Main results

* (12.70), `QuarteroniSaccoSaleri.Chapter12.equation_12_70_solution`: the exact solution of (12.70).
* (12.70), `QuarteroniSaccoSaleri.Chapter12.equation_12_70_unique`: (12.70) has no other $C^2$
  solution.
* Remark 12.5, `QuarteroniSaccoSaleri.Chapter12.remark_12_5`: for constant coefficients, the
  conservation form (12.74) has the same bilinear form as (12.73).
* (12.75)–(12.76), `QuarteroniSaccoSaleri.Chapter12.equation_12_75`: the Galerkin problem (12.72) on
  a uniform mesh is a three-point difference equation.
* (12.76), `QuarteroniSaccoSaleri.Chapter12.equation_12_76_solution`: the explicit solution of the
  centred difference equation.
* (12.76), `QuarteroniSaccoSaleri.Chapter12.equation_12_76_unique`: the solution is unique.
* (12.76), `QuarteroniSaccoSaleri.Chapter12.equation_12_76_oscillates`: for $\mathrm{Pe} > 1$ the
  increments of the solution alternate in sign.
* (12.76), `QuarteroniSaccoSaleri.Chapter12.equation_12_76_strictMono`: for $\mathrm{Pe} < 1$ the
  solution is strictly increasing.
* (12.77), `QuarteroniSaccoSaleri.Chapter12.equation_12_77`: the centred finite differences are the
  equations (12.75).
* (12.78)–(12.79), `QuarteroniSaccoSaleri.Chapter12.equation_12_79`: the upwind scheme is the
  centred scheme with the viscosity $\phi^{UP}$.
* (12.81), `QuarteroniSaccoSaleri.Chapter12.equation_12_81`: the upwind viscosity is
  $\varepsilon + |\beta| h / 2$.
* Section 12.5.2, `QuarteroniSaccoSaleri.Chapter12.equation_12_78_zero_diffusion`: for
  $\varepsilon = 0$ the upwind scheme gives a constant solution.
* Remark 12.6, `QuarteroniSaccoSaleri.Chapter12.remark_12_6_asymptotics`:
  $\phi^{SG}(t)/\phi^{UP}(t) \to 1$ as $t \to \infty$, and $0 \le \phi^{SG}(t) \le t^2/3$ for
  $t \ge 0$.
* Remark 12.6, `QuarteroniSaccoSaleri.Chapter12.remark_12_6_nodal_exact`: the Scharfetter–Gummel
  scheme is exact at the nodes.
* Section 12.5.2, `QuarteroniSaccoSaleri.Chapter12.stabilizedPeclet_lt_one`: $\mathrm{Pe}^* < 1$ for
  the upwind and the Scharfetter–Gummel schemes.
* Exercise 12.13, `QuarteroniSaccoSaleri.Chapter12.exercise_12_13`: the matrix of the stabilized
  scheme is an M-matrix when $|\mathrm{Pe}^*| \le 1$.
* Exercise 12.13, `QuarteroniSaccoSaleri.Chapter12.exercise_12_13_maximumPrinciple`: the discrete
  maximum principle for an M-matrix.
* (12.84), `QuarteroniSaccoSaleri.Chapter12.equation_12_84_self`:
  $a_h(v, v) = \varepsilon_h |v|^2_{H^1}$ on $H^1_0(0, 1)$.
* (12.84), `QuarteroniSaccoSaleri.Chapter12.equation_12_84_sub`: the stabilization term is $b(u,
  v) = \varepsilon \phi(\mathrm{Pe}) \int_0^1 u' v'$.
* Theorem 12.4, `QuarteroniSaccoSaleri.Chapter12.theorem_12_4`: the estimate (12.85) for the
  Scharfetter–Gummel method with $k = 1$.
* Theorem 12.4, `QuarteroniSaccoSaleri.Chapter12.theorem_12_4_upwind`: the estimate (12.85) for the
  upwind method with $k = 1$.
* Theorem 12.4, `QuarteroniSaccoSaleri.Chapter12.equation_12_86`: the estimate (12.86) for the
  Scharfetter–Gummel method with $k = 2$.

## Conventions

* A grid function is a sequence `u : ℕ → ℝ`; only the values $u_0, \ldots, u_n$ are constrained. A
  three-point relation is written at the indices $i$, $i + 1$, $i + 2$ instead of $i - 1$, $i$,
  $i + 1$.
* The uniform mesh width is $h = 1/n$, `AdvectionDiffusion.meshWidth n`.
* The bilinear forms are `EllipticInterval.form` on $H^1(0, 1)$, `SobolevInterval 1 0 1`, with the
  constant coefficients `EllipticInterval.constLinf 0 1 c` of $L^\infty(0, 1)$.

## Implementation notes

* The homogeneous case of the nodal exactness in Remark 12.6 uses that the discrete ratio
  $(1 + \mathrm{Pe}^*)/(1 - \mathrm{Pe}^*)$ equals $e^{2\mathrm{Pe}}$ for $\phi = \phi^{SG}$
  (`AdvectionDiffusion.centredRatio_stabilizedPeclet_phiSG`); this fixes the homogeneous solution at
  the nodes. The general claim of Remark 12.6, for a piecewise constant $f$, is not a consequence of
  this case: the scheme must also reproduce the particular solution of the two-point problem on each
  panel. The claim depends on how the right-hand side is discretized. It holds when $f$ is
  integrated against the exponentially fitted test functions, because the flux
  $\varepsilon u' - \beta u$ is then linear on each panel (the Il'in–Allen–Southwell scheme, Chapter
  I §2 of Roos, Stynes and Tobiska, *Robust Numerical Methods for Singularly Perturbed Differential
  Equations*, 2nd edition). It is not expected for the finite difference right-hand side $f(x_i)$,
  nor for the piecewise linear load with the viscosity $\phi^{SG}$ alone.

## Not formalized

* **Remark 12.6, the case of a piecewise constant $f$.** The claim is that the Scharfetter–Gummel
  scheme for $-\varepsilon u'' + \beta u' = f$ with $u(0) = 0$, $u(1) = 1$ is nodally exact for
  every $h$. The book quotes it without proof from a reference that it cites as HGR96 (pp. 44–45),
  uses it nowhere, and does not say how $f$ enters the scheme (12.79)–(12.83). Theorem 12.4 needs
  only the homogeneous case, which is `QuarteroniSaccoSaleri.Chapter12.remark_12_6_nodal_exact`. The
  library has no scheme with a right-hand side and no exact solution of
  $-\varepsilon u'' + \beta u' = f$.
* **Example 12.3.** It is a numerical experiment.
-/

open Filter MeasureTheory Set
open scoped ENNReal InnerProductSpace Topology

namespace QuarteroniSaccoSaleri.Chapter12

/-! ### The Péclet numbers -/

/-- **Equation (12.71)** of [quarteroni2000numerical]. The **global Péclet number** of a domain of
size $L$,
$$\mathrm{Pe}_{gl} = \frac{|\beta| L}{2\varepsilon}.$$
It measures the dominance of the advective term over the diffusive term.

The formula is `QuarteroniSaccoSaleri.Chapter12.equation_12_71_eq`. Division by
$\varepsilon = 0$ gives $0$. -/
noncomputable def equation_12_71 (β L ε : ℝ) : ℝ := AdvectionDiffusion.globalPeclet β L ε

/-- **Equation (12.71)** of [quarteroni2000numerical]. The global Péclet number is
$\mathrm{Pe}_{gl} = |\beta| L / (2\varepsilon)$. -/
theorem equation_12_71_eq (β L ε : ℝ) : equation_12_71 β L ε = |β| * L / (2 * ε) := rfl

/-- **Section 12.5.1** of [quarteroni2000numerical]. The **local Péclet number** of a mesh of width
$h$,
$$\mathrm{Pe} = \frac{|\beta| h}{2\varepsilon}.$$
-/
noncomputable def meshPeclet (β h ε : ℝ) : ℝ := AdvectionDiffusion.localPeclet β h ε

/-- **Section 12.5.1** of [quarteroni2000numerical]. The local Péclet number is
$\mathrm{Pe} = |\beta| h / (2\varepsilon)$. -/
theorem meshPeclet_eq (β h ε : ℝ) : meshPeclet β h ε = |β| * h / (2 * ε) := rfl

/-- **Section 12.5.1** of [quarteroni2000numerical]. On the unit interval, the local Péclet number
is $h$ times the global one: $\mathrm{Pe} = \mathrm{Pe}_{gl} \, h$ with $L = 1$. -/
theorem meshPeclet_eq_equation_12_71_mul (β h ε : ℝ) :
    meshPeclet β h ε = equation_12_71 β 1 ε * h :=
  AdvectionDiffusion.localPeclet_eq_globalPeclet_mul β h ε

/-! ### The exact solution of (12.70) -/

/-- **Equation (12.70)** of [quarteroni2000numerical], the exact solution. Let
$\varepsilon, \beta > 0$. The function
$$u(x) = \frac{e^{\beta x / \varepsilon} - 1}{e^{\beta / \varepsilon} - 1}$$
satisfies $u(0) = 0$, $u(1) = 1$ and $-\varepsilon u''(x) + \beta u'(x) = 0$ for every
$x \in \mathbb{R}$.

The function comes from the roots $\lambda_1 = 0$ and $\lambda_2 = \beta / \varepsilon$ of the
characteristic equation. It is `AdvectionDiffusion.exactSolution ε β`. -/
theorem equation_12_70_solution {ε β : ℝ} (hε : 0 < ε) (hβ : 0 < β) :
    AdvectionDiffusion.exactSolution ε β 0 = 0 ∧ AdvectionDiffusion.exactSolution ε β 1 = 1 ∧
      ∀ x, -ε * deriv (deriv (AdvectionDiffusion.exactSolution ε β)) x
        + β * deriv (AdvectionDiffusion.exactSolution ε β) x = 0 :=
  ⟨AdvectionDiffusion.exactSolution_zero ε β, AdvectionDiffusion.exactSolution_one hε hβ,
    AdvectionDiffusion.exactSolution_solves hε.ne' β⟩

/-- **Equation (12.70)** of [quarteroni2000numerical], uniqueness. Let $\varepsilon, \beta > 0$, and
let $u \in C^2(\mathbb{R})$ satisfy $-\varepsilon u''(x) + \beta u'(x) = 0$ for every
$x \in \mathbb{R}$, $u(0) = 0$ and $u(1) = 1$. Then $u(x) = (e^{\beta x / \varepsilon} -
1)/(e^{\beta / \varepsilon} - 1)$ for every $x$.

The general solution is $C_1 + C_2 e^{\beta x / \varepsilon}$, and the boundary conditions fix
the two constants. The equation is assumed on all of $\mathbb{R}$. -/
theorem equation_12_70_unique {ε β : ℝ} (hε : 0 < ε) (hβ : 0 < β) {u : ℝ → ℝ}
    (hu : ContDiff ℝ 2 u) (hode : ∀ x, -ε * deriv (deriv u) x + β * deriv u x = 0)
    (h0 : u 0 = 0) (h1 : u 1 = 1) : u = AdvectionDiffusion.exactSolution ε β :=
  AdvectionDiffusion.exactSolution_unique hε hβ hu hode h0 h1

/-! ### The conservation form (12.74) -/

open SobolevInterval in
/-- **Remark 12.5** of [quarteroni2000numerical] (the conservation form). Let $\varepsilon, \beta$
be constants, let $u \in H^1(0, 1)$, and let $v \in H^1_0(0, 1)$. Then the bilinear form of
(12.73) equals the bilinear form of the conservation form (12.74),
$-(\varepsilon u' - \beta u)' = 0$:
$$\int_0^1 (\varepsilon u' v' + \beta u' v) \, dx = \int_0^1 (\varepsilon u' - \beta u) v' \,
  dx.$$

The two sides differ by $\beta \int_0^1 (u' v + u v') = \beta [u v]_0^1$, which vanishes because
$v(0) = v(1) = 0$. The left side is `EllipticInterval.form` with the coefficients $\varepsilon$,
$\beta$, $0$, and $u$ in the integrand on the right is the continuous representative. -/
theorem remark_12_5 (ε β : ℝ) (u : SobolevInterval 1 0 1) {v : SobolevInterval 1 0 1}
    (hv : v ∈ SobolevIntervalZero 0 1) :
    EllipticInterval.form 0 1 (EllipticInterval.constLinf 0 1 ε)
        (EllipticInterval.constLinf 0 1 β) 0 u v
      = ∫ x in Ioo (0 : ℝ) 1, (ε * deriv u 1 x - β * rep u x) * deriv v 1 x := by
  have hab : (0 : ℝ) < 1 := one_pos
  have hcε := EllipticInterval.coeFn_constLinf 0 1 ε
  have hcβ := EllipticInterval.coeFn_constLinf 0 1 β
  have hc1 := EllipticInterval.coeFn_constLinf 0 1 1
  have hru := fn_ae_eq_rep u
  have hrv := fn_ae_eq_rep v
  -- the three integrands, and their integrability
  have i1 : IntegrableOn (fun x => ε * (deriv u 1 x * deriv v 1 x)) (Ioo (0 : ℝ) 1) := by
    refine (EllipticInterval.integrable_mul_mul (EllipticInterval.constLinf 0 1 ε)
      (deriv u 1) (deriv v 1)).congr ?_
    filter_upwards [hcε] with x hx
    rw [hx]
    ring
  have i2 : IntegrableOn (fun x => deriv u 1 x * rep v x) (Ioo (0 : ℝ) 1) := by
    refine (EllipticInterval.integrable_mul_mul (EllipticInterval.constLinf 0 1 1)
      (deriv u 1) (deriv v 0)).congr ?_
    filter_upwards [hc1, hrv] with x h1 h2
    rw [h1, SobolevInterval.deriv_zero, h2]
    ring
  have i3 : IntegrableOn (fun x => rep u x * deriv v 1 x) (Ioo (0 : ℝ) 1) := by
    refine (EllipticInterval.integrable_mul_mul (EllipticInterval.constLinf 0 1 1)
      (deriv u 0) (deriv v 1)).congr ?_
    filter_upwards [hc1, hru] with x h1 h2
    rw [h1, SobolevInterval.deriv_zero, h2]
    ring
  -- the boundary terms of the integration by parts vanish
  have ibp := integral_deriv_mul_add_mul_deriv hab u v
  rw [SobolevIntervalZero.rep_left_eq_zero hab hv, SobolevIntervalZero.rep_right_eq_zero hab hv,
    mul_zero, mul_zero, sub_zero, intervalIntegral.integral_eq_setIntegral_Ioo hab.le,
    integral_add i2 i3] at ibp
  rw [EllipticInterval.form_apply]
  have e1 : ∀ x : ℝ, (EllipticInterval.constLinf 0 1 ε : ℝ → ℝ) x = ε →
      (EllipticInterval.constLinf 0 1 β : ℝ → ℝ) x = β → fn v x = rep v x →
      ((0 : Lp ℝ ⊤ (volume.restrict (Ioo (0 : ℝ) 1))) : ℝ → ℝ) x = 0 →
      (EllipticInterval.constLinf 0 1 ε : ℝ → ℝ) x * deriv u 1 x * deriv v 1 x
        + (EllipticInterval.constLinf 0 1 β : ℝ → ℝ) x * deriv u 1 x * deriv v 0 x
        + ((0 : Lp ℝ ⊤ (volume.restrict (Ioo (0 : ℝ) 1))) : ℝ → ℝ) x * deriv u 0 x * deriv v 0 x
      = ε * (deriv u 1 x * deriv v 1 x) + β * (deriv u 1 x * rep v x) := by
    intro x h1 h2 h3 h4
    rw [h1, h2, h4, SobolevInterval.deriv_zero, h3]
    ring
  have hform : ∫ x in Ioo (0 : ℝ) 1,
      ((EllipticInterval.constLinf 0 1 ε : ℝ → ℝ) x * deriv u 1 x * deriv v 1 x
        + (EllipticInterval.constLinf 0 1 β : ℝ → ℝ) x * deriv u 1 x * deriv v 0 x
        + ((0 : Lp ℝ ⊤ (volume.restrict (Ioo (0 : ℝ) 1))) : ℝ → ℝ) x * deriv u 0 x
          * deriv v 0 x)
      = (∫ x in Ioo (0 : ℝ) 1, ε * (deriv u 1 x * deriv v 1 x))
        + ∫ x in Ioo (0 : ℝ) 1, β * (deriv u 1 x * rep v x) := by
    rw [← integral_add i1 (i2.const_mul β)]
    refine integral_congr_ae ?_
    filter_upwards [hcε, hcβ, hrv, Lp.coeFn_zero ℝ ⊤ (volume.restrict (Ioo (0 : ℝ) 1))]
      with x h1 h2 h3 h4
    exact e1 x h1 h2 h3 (by rw [h4]; rfl)
  have e2 : ∫ x in Ioo (0 : ℝ) 1, (ε * deriv u 1 x - β * rep u x) * deriv v 1 x
      = (∫ x in Ioo (0 : ℝ) 1, ε * (deriv u 1 x * deriv v 1 x))
        - ∫ x in Ioo (0 : ℝ) 1, β * (rep u x * deriv v 1 x) := by
    rw [← integral_sub i1 (i3.const_mul β)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    ring
  rw [hform, e2]
  simp only [integral_const_mul]
  linear_combination β * ibp

/-! ### The Galerkin approximation (12.72)–(12.76) -/

/-- The constant $0$ of `EllipticInterval.constLinf` is the zero element of $L^\infty(a, b)$. -/
theorem constLinf_zero (a b : ℝ) : EllipticInterval.constLinf a b 0 = 0 :=
  EllipticInterval.constLinf_zero a b

/-- **Equations (12.72)–(12.73)** of [quarteroni2000numerical], the piecewise linear Galerkin
approximation of (12.70). For nodes $x_0, \ldots, x_n$, an element $u_h \in H^1(0, 1)$ **solves
the Galerkin problem** if $u_h \in X_h^1$, $u_h(0) = 0$, $u_h(1) = 1$, and
$$a(u_h, v_h) = \int_0^1 (\varepsilon u_h' v_h' + \beta u_h' v_h) \, dx = 0 \quad \text{for
  every } v_h \in X_h^{1,0}.$$
-/
def equation_12_72 (ε β : ℝ) (n : ℕ) (x : ℕ → ℝ) (uh : SobolevInterval 1 0 1) : Prop :=
  uh ∈ FiniteElement.lagrangeSpace zero_lt_one n x 1 ∧
    SobolevInterval.rep uh 0 = 0 ∧ SobolevInterval.rep uh 1 = 1 ∧
    ∀ vh ∈ FiniteElement.lagrangeSpaceZero zero_lt_one n x 1,
      EllipticInterval.form 0 1 (EllipticInterval.constLinf 0 1 ε)
        (EllipticInterval.constLinf 0 1 β) 0 uh vh = 0

/-- **Equations (12.75)–(12.76)** of [quarteroni2000numerical]. Let $0 = x_0 < \cdots < x_n = 1$ be
a uniform partition with $n \ge 1$ and step $h > 0$. Let $u_0, \ldots, u_n$ be real numbers with
$u_0 = 0$ and $u_n = 1$, and let $\varphi_j$ be the piecewise linear shape functions (12.61).
Then $\sum_{j=0}^n u_j \varphi_j$ solves the Galerkin problem (12.72) if and only if
$$\frac{\varepsilon}{h} (-u_{i-1} + 2u_i - u_{i+1}) + \frac{\beta}{2} (u_{i+1} - u_{i-1}) = 0
  \quad \text{for } 1 \le i < n.$$

By `QuarteroniSaccoSaleri.Chapter12.equation_12_77` this is the centred finite difference
scheme. Multiplied by $h / \varepsilon$, it is $(\mathrm{Pe} - 1) u_{i+1} + 2 u_i -
(\mathrm{Pe} + 1) u_{i-1} = 0$ with $\mathrm{Pe} = |\beta| h / (2\varepsilon)$ when $\beta > 0$. -/
theorem equation_12_75 (ε β : ℝ) {n : ℕ} {x : ℕ → ℝ} (hx : IsIntervalPartition 0 1 n x)
    (hn : 1 ≤ n) {h : ℝ} (hh : 0 < h) (huni : ∀ k < n, x (k + 1) - x k = h) (u : ℕ → ℝ)
    (hu0 : u 0 = 0) (hun : u n = 1) :
    equation_12_72 ε β n x
        (∑ j ∈ Finset.range (n + 1), u j • FiniteElement.hatFunction hx hn j)
      ↔ ∀ i, 1 ≤ i → i < n →
        ε / h * (-u (i - 1) + 2 * u i - u (i + 1)) + β / 2 * (u (i + 1) - u (i - 1)) = 0 := by
  have hmem := FiniteElement.sum_hatFunction_mem_lagrangeSpace zero_lt_one hx hn u
  have hzero := FiniteElement.rep_sum_hatFunction zero_lt_one hx hn u (j := 0) (Nat.zero_le n)
  have hone := FiniteElement.rep_sum_hatFunction zero_lt_one hx hn u (j := n) le_rfl
  rw [hx.first] at hzero
  rw [hx.last] at hone
  rw [equation_12_72, ← constLinf_zero 0 1]
  have hgal := FiniteElement.galerkin_iff_centredScheme zero_lt_one hx hn hh huni ε β u
  constructor
  · rintro ⟨-, -, -, hvar⟩
    exact hgal.1 hvar
  · intro hdiff
    exact ⟨hmem, by rw [hzero, hu0], by rw [hone, hun], hgal.2 hdiff⟩

/-! ### The centred difference equation (12.76) and its oscillation -/

/-- **Equation (12.76)** of [quarteroni2000numerical], the explicit solution. Let $\mathrm{Pe} > 0$
with $\mathrm{Pe} \neq 1$, and let $n \ge 1$. Then $u_i = (1 - \rho^i)/(1 - \rho^n)$ with
$\rho = (1 + \mathrm{Pe})/(1 - \mathrm{Pe})$ satisfies $u_0 = 0$, $u_n = 1$ and
$$(\mathrm{Pe} - 1) u_{i+1} + 2 u_i - (\mathrm{Pe} + 1) u_{i-1} = 0 \quad \text{for } 1 \le i
  \le n - 1.$$

The roots of the characteristic equation $(\mathrm{Pe} - 1) \rho^2 + 2\rho - (\mathrm{Pe} + 1) =
0$ are $\rho$ and $1$. The solution is `AdvectionDiffusion.centredSolution n Pe`. -/
theorem equation_12_76_solution {Pe : ℝ} (hPe : 0 < Pe) (hPe1 : Pe ≠ 1) {n : ℕ} (hn : n ≠ 0) :
    AdvectionDiffusion.centredSolution n Pe 0 = 0 ∧
      AdvectionDiffusion.centredSolution n Pe n = 1 ∧
      ∀ i, i + 2 ≤ n → (Pe - 1) * AdvectionDiffusion.centredSolution n Pe (i + 2)
        + 2 * AdvectionDiffusion.centredSolution n Pe (i + 1)
        - (Pe + 1) * AdvectionDiffusion.centredSolution n Pe i = 0 :=
  ⟨AdvectionDiffusion.centredSolution_zero n Pe,
    AdvectionDiffusion.centredSolution_self hPe hPe1 hn,
    fun i _ => AdvectionDiffusion.centredSolution_solves hPe1 n i⟩

/-- **Equation (12.76)** of [quarteroni2000numerical], uniqueness. Let $\mathrm{Pe} > 0$ with
$\mathrm{Pe} \neq 1$, and let $n \ge 1$. If $u_0 = 0$, $u_n = 1$ and $u$ satisfies the
difference equation (12.76) at the interior nodes, then $u_i = (1 - \rho^i)/(1 - \rho^n)$ for
every $i \le n$. -/
theorem equation_12_76_unique {Pe : ℝ} (hPe : 0 < Pe) (hPe1 : Pe ≠ 1) {n : ℕ} (hn : n ≠ 0)
    {u : ℕ → ℝ} (h0 : u 0 = 0) (hlast : u n = 1)
    (hrec : ∀ i, i + 2 ≤ n → (Pe - 1) * u (i + 2) + 2 * u (i + 1) - (Pe + 1) * u i = 0)
    {i : ℕ} (hi : i ≤ n) : u i = AdvectionDiffusion.centredSolution n Pe i :=
  AdvectionDiffusion.centredSolution_unique hPe hPe1 hn h0 hlast hrec hi

/-- **Equation (12.76)** of [quarteroni2000numerical], oscillation. Let $\mathrm{Pe} > 1$ and
$n \ge 1$, and let $u_i = (1 - \rho^i)/(1 - \rho^n)$ be the solution of (12.76). Then for every
$i$,
$$(-1)^i (u_{i+1} - u_i)(u_1 - u_0) > 0,$$
so the increments of the discrete solution alternate in sign.

For $\mathrm{Pe} > 1$ the ratio $\rho$ is negative. For $\mathrm{Pe} < 1$ the discrete solution
is increasing, like the exact one: see
`QuarteroniSaccoSaleri.Chapter12.equation_12_76_strictMono`. -/
theorem equation_12_76_oscillates {Pe : ℝ} (hPe : 1 < Pe) {n : ℕ} (hn : n ≠ 0) (i : ℕ) :
    0 < (-1) ^ i * (AdvectionDiffusion.centredSolution n Pe (i + 1)
        - AdvectionDiffusion.centredSolution n Pe i)
      * (AdvectionDiffusion.centredSolution n Pe 1 - AdvectionDiffusion.centredSolution n Pe 0) :=
  AdvectionDiffusion.centredSolution_oscillates hPe hn i

/-- **Equation (12.76)** of [quarteroni2000numerical], monotonicity. Let $0 < \mathrm{Pe} < 1$ and
$n \ge 1$. Then the solution $u_i = (1 - \rho^i)/(1 - \rho^n)$ of (12.76) is strictly increasing
in $i$. This is the monotonicity that the mesh condition $\mathrm{Pe} < 1$ of Section 12.5.1
gives. -/
theorem equation_12_76_strictMono {Pe : ℝ} (hPe : 0 < Pe) (hPe1 : Pe < 1) {n : ℕ} (hn : n ≠ 0) :
    StrictMono (AdvectionDiffusion.centredSolution n Pe) :=
  AdvectionDiffusion.centredSolution_strictMono hPe hPe1 hn

/-! ### Finite differences and the numerical viscosity -/

/-- **Equation (12.77)** of [quarteroni2000numerical], the centred finite difference scheme. Let
$n \ge 1$ and $h = 1/n$. A grid function $u$ satisfies the centred scheme
$$-\varepsilon \frac{u_{i+1} - 2u_i + u_{i-1}}{h^2} + \beta \frac{u_{i+1} - u_{i-1}}{2h} = 0,
  \qquad u_0 = 0, \quad u_n = 1,$$
if and only if $u_0 = 0$, $u_n = 1$ and $(\varepsilon / h)(-u_{i-1} + 2u_i - u_{i+1}) + (\beta /
2)(u_{i+1} - u_{i-1}) = 0$ at the interior nodes.

The second form is the equation (12.75) of the piecewise linear Galerkin method; it is the first
form multiplied by $h$. The centred scheme is `AdvectionDiffusion.viscosityScheme` with
$\phi = 0$. -/
theorem equation_12_77 {ε β : ℝ} {n : ℕ} (hn : n ≠ 0) (u : ℕ → ℝ) :
    AdvectionDiffusion.viscosityScheme ε β n 0 u ↔ u 0 = 0 ∧ u n = 1 ∧ ∀ i, i + 2 ≤ n →
      ε / AdvectionDiffusion.meshWidth n * (-u i + 2 * u (i + 1) - u (i + 2))
        + β / 2 * (u (i + 2) - u i) = 0 :=
  AdvectionDiffusion.viscosityScheme_zero_iff hn u

/-- **Equations (12.78)–(12.79)** of [quarteroni2000numerical], upwinding as artificial diffusion.
Let $\varepsilon \neq 0$, $\beta > 0$, $n \ge 1$ and $h = 1/n$. A grid function satisfies the
upwind scheme
$$-\varepsilon \frac{u_{i+1} - 2u_i + u_{i-1}}{h^2} + \beta \frac{u_i - u_{i-1}}{h} = 0, \qquad
  u_0 = 0, \quad u_n = 1,$$
if and only if it satisfies the centred scheme (12.79) with the viscosity
$\varepsilon_h = \varepsilon(1 + \mathrm{Pe})$ in place of $\varepsilon$.

The proof is the identity $(u_i - u_{i-1})/h = (u_{i+1} - u_{i-1})/(2h) - (h/2)(u_{i+1} - 2u_i +
u_{i-1})/h^2$. The two schemes are `AdvectionDiffusion.upwindScheme` and
`AdvectionDiffusion.viscosityScheme` with $\phi = \phi^{UP}$. -/
theorem equation_12_79 {ε β : ℝ} {n : ℕ} (hε : ε ≠ 0) (hβ : 0 < β) (hn : n ≠ 0) (u : ℕ → ℝ) :
    AdvectionDiffusion.upwindScheme ε β n u
      ↔ AdvectionDiffusion.viscosityScheme ε β n AdvectionDiffusion.phiUpwind u :=
  AdvectionDiffusion.upwindScheme_iff_viscosityScheme hε hβ hn u

/-- **Equation (12.81)** of [quarteroni2000numerical], the numerical viscosity. For
$\varepsilon \neq 0$, the viscosity of the upwind scheme is
$$\varepsilon_h = \varepsilon (1 + \mathrm{Pe}) = \varepsilon + \frac{|\beta| h}{2}.$$

So the upwind scheme adds the term $\varepsilon \, \mathrm{Pe} \, u'' = (|\beta| h / 2) u''$ to
the equation. -/
theorem equation_12_81 {ε : ℝ} (hε : ε ≠ 0) (β h : ℝ) :
    AdvectionDiffusion.viscosity ε β h AdvectionDiffusion.phiUpwind = ε + |β| * h / 2 :=
  AdvectionDiffusion.viscosity_phiUpwind hε β h

/-- **Section 12.5.2** of [quarteroni2000numerical], the limit $\varepsilon = 0$. Let $\beta \neq 0$
and $n \ge 1$. If $u$ satisfies the upwind scheme with $\varepsilon = 0$, then $u_i = u_{i-1}$
for $1 \le i \le n - 1$. So $u_0 = u_1 = \cdots = u_{n-1}$, like the solution of the limit
problem $\beta u' = 0$. -/
theorem equation_12_78_zero_diffusion {β : ℝ} {n : ℕ} (hβ : β ≠ 0) (hn : n ≠ 0) {u : ℕ → ℝ}
    (hu : AdvectionDiffusion.upwindScheme 0 β n u) {i : ℕ} (hi : i + 2 ≤ n) :
    u (i + 1) = u i :=
  AdvectionDiffusion.upwindScheme_zero_diffusion hβ hn hu hi

/-- **Equation (12.82)** of [quarteroni2000numerical]. For a function $\phi$ and $h = 1/n$, the
viscosity of the general centred scheme
$$\varepsilon_h = \varepsilon (1 + \phi(\mathrm{Pe})), \qquad \mathrm{Pe} = \frac{|\beta|
  h}{2\varepsilon}.$$

The book requires $\phi(t) \to 0$ as $t \to 0^+$; the definition accepts any $\phi$. The choice
$\phi = 0$ gives the centred scheme (12.77), $\phi^{UP}(t) = t$ gives the upwind scheme (12.78),
and $\phi^{SG}$ of (12.83) gives the exponential fitting scheme. -/
noncomputable def equation_12_82 (ε β : ℝ) (n : ℕ) (φ : ℝ → ℝ) : ℝ :=
  AdvectionDiffusion.viscosity ε β (AdvectionDiffusion.meshWidth n) φ

/-- **Equation (12.82)** of [quarteroni2000numerical]. The viscosity is $\varepsilon_h =
\varepsilon(1 + \phi(\mathrm{Pe}))$, with the local Péclet number $\mathrm{Pe}$ of the mesh
width $h = 1/n$. -/
theorem equation_12_82_eq (ε β : ℝ) (n : ℕ) (φ : ℝ → ℝ) :
    equation_12_82 ε β n φ
      = ε * (1 + φ (meshPeclet β (AdvectionDiffusion.meshWidth n) ε)) := rfl

/-- **Equation (12.82)** of [quarteroni2000numerical] for $\phi = 0$. The viscosity is
$\varepsilon_h = \varepsilon$, the diffusion of the centred scheme. -/
theorem equation_12_82_zero (ε β : ℝ) (n : ℕ) : equation_12_82 ε β n 0 = ε :=
  AdvectionDiffusion.viscosity_zero ε β _

/-- **Equation (12.83)** of [quarteroni2000numerical]. The **Scharfetter–Gummel viscosity function**
(exponential fitting)
$$\phi^{SG}(t) = t - 1 + B(2t),$$
where $B(t) = t / (e^t - 1)$ for $t \neq 0$ and $B(0) = 1$ is the Bernoulli function.

The definition is `AdvectionDiffusion.phiSG`, and the Bernoulli function is
`AdvectionDiffusion.bernoulliFn`. -/
noncomputable def equation_12_83 (t : ℝ) : ℝ := AdvectionDiffusion.phiSG t

/-- **Equation (12.83)** of [quarteroni2000numerical]. The Scharfetter–Gummel function is
$\phi^{SG}(t) = t - 1 + B(2t)$. -/
theorem equation_12_83_eq (t : ℝ) :
    equation_12_83 t = t - 1 + AdvectionDiffusion.bernoulliFn (2 * t) := rfl

/-- **Equation (12.83)** of [quarteroni2000numerical]. For $t \neq 0$, the Bernoulli function is
$B(t) = t / (e^t - 1)$. Its value at $0$ is $1$. -/
theorem bernoulliFn_eq {t : ℝ} (ht : t ≠ 0) :
    AdvectionDiffusion.bernoulliFn t = t / (Real.exp t - 1) :=
  AdvectionDiffusion.bernoulliFn_of_ne_zero ht

/-- **Exercise 12.13** of [quarteroni2000numerical], the identity of the hint. For every real $t$,
the Bernoulli function satisfies $B(-t) = t + B(t)$. -/
theorem bernoulliFn_neg (t : ℝ) :
    AdvectionDiffusion.bernoulliFn (-t) = t + AdvectionDiffusion.bernoulliFn t :=
  AdvectionDiffusion.bernoulliFn_neg t

/-! ### Remark 12.6 -/

/-- **Remark 12.6** of [quarteroni2000numerical], the asymptotics of $\phi^{SG}$. The quotient
$\phi^{SG}(t) / \phi^{UP}(t)$ tends to $1$ as $t \to +\infty$, and
$$0 \le \phi^{SG}(t) \le \frac{t^2}{3} \quad \text{for every } t \ge 0.$$

So $\phi^{SG} \simeq \phi^{UP}$ for large Péclet numbers; their difference $B(2t) - 1$ tends to
$-1$. For small $h$, $\phi^{SG}(\mathrm{Pe}) = O(h^2)$, where
$\phi^{UP}(\mathrm{Pe}) = \mathrm{Pe} = O(h)$. This is why the Scharfetter–Gummel method is
second-order accurate. -/
theorem remark_12_6_asymptotics :
    Tendsto (fun t => AdvectionDiffusion.phiSG t / AdvectionDiffusion.phiUpwind t) atTop (𝓝 1) ∧
      ∀ t : ℝ, 0 ≤ t → 0 ≤ AdvectionDiffusion.phiSG t ∧ AdvectionDiffusion.phiSG t ≤ t ^ 2 / 3 :=
  ⟨AdvectionDiffusion.phiSG_div_phiUpwind_tendsto,
    fun _ ht => ⟨AdvectionDiffusion.phiSG_nonneg ht, AdvectionDiffusion.phiSG_le_sq ht⟩⟩

/-- **Remark 12.6** of [quarteroni2000numerical], nodal exactness. Let $\varepsilon, \beta > 0$,
$n \ge 1$ and $h = 1/n$. If $u$ satisfies the centred scheme (12.79) with the viscosity
$\phi^{SG}$, then for every $i \le n$
$$u_i = \frac{e^{\beta i h / \varepsilon} - 1}{e^{\beta / \varepsilon} - 1},$$
the value of the exact solution of (12.70) at the node $x_i = ih$.

This holds for every mesh size, and hence for every local Péclet number. -/
theorem remark_12_6_nodal_exact {ε β : ℝ} {n : ℕ} (hε : 0 < ε) (hβ : 0 < β) (hn : n ≠ 0)
    {u : ℕ → ℝ} (hu : AdvectionDiffusion.viscosityScheme ε β n AdvectionDiffusion.phiSG u)
    {i : ℕ} (hi : i ≤ n) :
    u i = AdvectionDiffusion.exactSolution ε β (i * AdvectionDiffusion.meshWidth n) :=
  AdvectionDiffusion.sg_nodal_exact hε hβ hn hu hi

/-! ### The stabilized Péclet number and the M-matrix property -/

/-- **Section 12.5.2** of [quarteroni2000numerical], the stabilized Péclet number. Let
$\mathrm{Pe} > 0$, and let $\mathrm{Pe}^* = \mathrm{Pe}/(1 + \phi(\mathrm{Pe}))$. For the upwind
function $\phi^{UP}$, $\mathrm{Pe}^* = \mathrm{Pe}/(1 + \mathrm{Pe}) < 1$. For the
Scharfetter–Gummel function $\phi^{SG}$, $\mathrm{Pe}^* = \tanh \mathrm{Pe} < 1$.

Since $\mathrm{Pe}^* = |\beta| h / (2\varepsilon_h)$, both schemes have $\mathrm{Pe}^* < 1$ for
every mesh size. -/
theorem stabilizedPeclet_lt_one {Pe : ℝ} (hPe : 0 < Pe) :
    AdvectionDiffusion.stabilizedPeclet AdvectionDiffusion.phiUpwind Pe = Pe / (1 + Pe) ∧
      AdvectionDiffusion.stabilizedPeclet AdvectionDiffusion.phiUpwind Pe < 1 ∧
      AdvectionDiffusion.stabilizedPeclet AdvectionDiffusion.phiSG Pe = Real.tanh Pe ∧
      AdvectionDiffusion.stabilizedPeclet AdvectionDiffusion.phiSG Pe < 1 :=
  ⟨AdvectionDiffusion.stabilizedPeclet_phiUpwind Pe,
    AdvectionDiffusion.stabilizedPeclet_phiUpwind_lt_one hPe,
    AdvectionDiffusion.stabilizedPeclet_phiSG_eq_tanh hPe,
    AdvectionDiffusion.stabilizedPeclet_phiSG_lt_one hPe⟩

/-- **Exercise 12.13** of [quarteroni2000numerical]. Let $n \ge 1$ and $h = 1/n$, let $\phi$ be a
function with $\varepsilon_h = \varepsilon(1 + \phi(\mathrm{Pe})) > 0$, and let $\mathrm{Pe}^* =
\mathrm{Pe}/(1 + \phi(\mathrm{Pe}))$ satisfy $|\mathrm{Pe}^*| \le 1$. Then for every size $m$
the matrix
$$\frac{\varepsilon_h}{h^2} \operatorname{tridiag}\big(-(1 + \mathrm{Pe}^*), 2, -(1 -
  \mathrm{Pe}^*)\big) \in \mathbb{R}^{m \times m}$$
of the stabilized scheme (12.79) is an M-matrix. The entries $-(1 + \mathrm{Pe}^*)$ are below
the diagonal and the entries $-(1 - \mathrm{Pe}^*)$ are above it.

By `QuarteroniSaccoSaleri.Chapter12.stabilizedPeclet_lt_one`, the hypothesis
$|\mathrm{Pe}^*| \le 1$ holds for the upwind and the Scharfetter–Gummel viscosities at every
mesh size. The discrete solution then satisfies the maximum principle of Section 12.2.2,
`QuarteroniSaccoSaleri.Chapter12.exercise_12_13_maximumPrinciple`. An M-matrix is
`Matrix.IsMMatrix`: its off-diagonal entries are nonpositive, it is invertible, and its inverse
is entrywise nonnegative. -/
theorem exercise_12_13 {ε β : ℝ} {n : ℕ} {φ : ℝ → ℝ} (m : ℕ)
    (hεh : 0 < AdvectionDiffusion.viscosity ε β (AdvectionDiffusion.meshWidth n) φ) (hn : n ≠ 0)
    (hPe : |AdvectionDiffusion.stabilizedPeclet φ
      (meshPeclet β (AdvectionDiffusion.meshWidth n) ε)| ≤ 1) :
    ((AdvectionDiffusion.viscosity ε β (AdvectionDiffusion.meshWidth n) φ
          / AdvectionDiffusion.meshWidth n ^ 2) •
        Matrix.tridiagonalToeplitz m
          (-(1 + AdvectionDiffusion.stabilizedPeclet φ
            (meshPeclet β (AdvectionDiffusion.meshWidth n) ε))) 2
          (-(1 - AdvectionDiffusion.stabilizedPeclet φ
            (meshPeclet β (AdvectionDiffusion.meshWidth n) ε)))).IsMMatrix :=
  AdvectionDiffusion.viscosityScheme_isMMatrix m hεh hn hPe

/-- **Exercise 12.13** of [quarteroni2000numerical], the discrete maximum principle. Let
$A \in \mathbb{R}^{m \times m}$ be an M-matrix and $x \in \mathbb{R}^m$. If $Ax \ge 0$
entrywise, then $x \ge 0$ entrywise. -/
theorem exercise_12_13_maximumPrinciple {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ} (hA : A.IsMMatrix)
    {x : Fin m → ℝ} (hx : 0 ≤ A.mulVec x) : 0 ≤ x :=
  hA.nonneg_of_mulVec_nonneg hx

/-! ### The stabilized finite element method (12.84) -/

/-- **Equation (12.84)** of [quarteroni2000numerical], the stabilized bilinear form. For constants
$\varepsilon, \beta, h$ and a function $\phi$, the form on $H^1(0, 1)$
$$a_h(u, v) = a(u, v) + b(u, v), \qquad b(u, v) = \varepsilon \phi(\mathrm{Pe}) \int_0^1 u' v'
  \, dx,$$
where $a(u, v) = \int_0^1 (\varepsilon u' v' + \beta u' v) \, dx$ is the form of (12.73).
Equivalently, $a_h$ is the form (12.73) with the viscosity $\varepsilon_h = \varepsilon(1 +
\phi(\mathrm{Pe}))$ of (12.82) in place of $\varepsilon$.

The definition is `AdvectionDiffusion.stabilizedForm`. The stabilized problem of (12.84), find
$\mathring{u}_h \in X_h^{k,0}$ with $a_h(\mathring{u}_h, v_h) = -\int_0^1 \beta v_h$ for all
$v_h \in X_h^{k,0}$, is `IsGalerkinSolution` for this form on `FiniteElement.lagrangeSpaceZero`,
after the lifting $\mathring{u} = u - x$. The problem without the lifting is
`QuarteroniSaccoSaleri.Chapter12.equation_12_84_problem`. -/
noncomputable def equation_12_84 (ε β h : ℝ) (φ : ℝ → ℝ) : SesqForm ℝ (SobolevInterval 1 0 1) :=
  AdvectionDiffusion.stabilizedForm 0 1 ε β h φ

/-- **Equation (12.84)** of [quarteroni2000numerical], the energy identity. For every
$v \in H^1_0(0, 1)$,
$$a_h(v, v) = \varepsilon_h |v|^2_{H^1(0,1)}.$$

Since $\varepsilon_h / \varepsilon = 1 + \phi(\mathrm{Pe}) \ge 1$ for a nonnegative $\phi$, this
gives the stabilized problem its better monotonicity. -/
theorem equation_12_84_self {ε β h : ℝ} (φ : ℝ → ℝ) {v : SobolevInterval 1 0 1}
    (hv : v ∈ SobolevIntervalZero 0 1) :
    equation_12_84 ε β h φ v v
      = AdvectionDiffusion.viscosity ε β h φ * SobolevInterval.seminorm 1 0 1 v ^ 2 :=
  AdvectionDiffusion.stabilizedForm_self one_pos φ hv

/-- **Equation (12.84)** of [quarteroni2000numerical], the stabilization term. For all
$u, v \in H^1(0, 1)$, the difference between the stabilized form and the Galerkin form (12.73)
is
$$a_h(u, v) - a(u, v) = \varepsilon \phi(\mathrm{Pe}) \int_0^1 u' v' \, dx.$$
-/
theorem equation_12_84_sub (ε β h : ℝ) (φ : ℝ → ℝ) (u v : SobolevInterval 1 0 1) :
    equation_12_84 ε β h φ u v
        - EllipticInterval.form 0 1 (EllipticInterval.constLinf 0 1 ε)
          (EllipticInterval.constLinf 0 1 β) 0 u v
      = ε * φ (meshPeclet β h ε)
        * ⟪SobolevInterval.deriv u 1, SobolevInterval.deriv v 1⟫_ℝ :=
  AdvectionDiffusion.stabilizedForm_sub_form 0 1 ε β h φ u v

/-! ### Theorem 12.4, the convergence of the stabilized finite element method -/

/-- **Equation (12.84)** of [quarteroni2000numerical], the stabilized finite element problem for
(12.70), without the lifting. For nodes $x_0, \ldots, x_n$ and a degree $k$, an element
$u_h \in H^1(0, 1)$ **solves the stabilized problem** if $u_h \in X_h^k$, $u_h(0) = 0$,
$u_h(1) = 1$, and $a_h(u_h, v_h) = 0$ for every $v_h \in X_h^{k,0}$.

The book's form is: find $\mathring{u}_h \in X_h^{k,0}$ with
$a_h(\mathring{u}_h, v_h) = -\int_0^1 \beta v_h$. It is this problem after the subtraction of
the lifting $\bar{u}(x) = x$, since $a_h(\bar{u}, v_h) = \int_0^1 \beta v_h$ for every $v_h$
that vanishes at both endpoints. -/
def equation_12_84_problem (ε β h : ℝ) (φ : ℝ → ℝ) (k n : ℕ) (x : ℕ → ℝ)
    (uh : SobolevInterval 1 0 1) : Prop :=
  uh ∈ FiniteElement.lagrangeSpace zero_lt_one n x k ∧
    SobolevInterval.rep uh 0 = 0 ∧ SobolevInterval.rep uh 1 = 1 ∧
    ∀ vh ∈ FiniteElement.lagrangeSpaceZero zero_lt_one n x k,
      equation_12_84 ε β h φ uh vh = 0

/-- **Theorem 12.4** of [quarteroni2000numerical], the estimate (12.85) for the Scharfetter–Gummel
method with $k = 1$. Let $0 = x_0 < \cdots < x_n = 1$ be the uniform partition with $n \ge 1$
and step $h = 1/n$, and let $\varepsilon, \beta > 0$. Let $u \in H^2(0, 1)$ have the nodal
values $u(x_i)$ of the exact solution of (12.70) for $i \le n$. Let $u_h$ solve the stabilized
problem (12.84) with $\phi = \phi^{SG}$ and $k = 1$. Then
$$|u - u_h|_{H^1(0,1)} \le h \, |u|_{H^2(0,1)}.$$

The book states $|\mathring{u} - \mathring{u}_h|_{H^1(0,1)} \le C h |\mathring{u}|_{H^2(0,1)}$
with $C$ independent of $h$ and $\mathring{u}$. Here $C = 1$, without the factor
$(1 + 2\mathrm{Pe}_{gl} C_P)$ of the book, because the Scharfetter–Gummel solution is nodally
exact (Remark 12.6): $u_h$ is the piecewise linear interpolant of $u$, and the Galerkin error is
the interpolation error. The statement is for the pair $u$, $u_h$ without the lifting; it is the
same inequality, since $\mathring{u} - \mathring{u}_h = u - u_h$ and
$|\mathring{u}|_{H^2} = |u|_{H^2}$ for the affine lifting $\bar{u}(x) = x$. The seminorm
$|u|_{H^2(0,1)}$ is $\|u''\|_{L^2(0,1)}$. The upwind case is
`QuarteroniSaccoSaleri.Chapter12.theorem_12_4_upwind`, and the case $k = 2$ is
`QuarteroniSaccoSaleri.Chapter12.equation_12_86`. -/
theorem theorem_12_4 {n : ℕ} {x : ℕ → ℝ} (hx : IsIntervalPartition 0 1 n x) (hn : 1 ≤ n)
    (huni : ∀ k < n, x (k + 1) - x k = AdvectionDiffusion.meshWidth n) {ε β : ℝ} (hε : 0 < ε)
    (hβ : 0 < β) {u uh : SobolevInterval 1 0 1} (U : SobolevInterval 2 0 1)
    (hU : SobolevInterval.inclusionCLM 1 0 1 U = u)
    (hunode : ∀ i ≤ n, SobolevInterval.rep u (x i) = AdvectionDiffusion.exactSolution ε β (x i))
    (hdisc : equation_12_84_problem ε β (AdvectionDiffusion.meshWidth n)
      AdvectionDiffusion.phiSG 1 n x uh) :
    SobolevInterval.seminorm 1 0 1 (u - uh)
      ≤ AdvectionDiffusion.meshWidth n * SobolevInterval.seminorm 2 0 1 U :=
  AdvectionDiffusion.seminorm_sub_stabilized_le_sg hx hn huni hε hβ U hU hunode
    hdisc.1 hdisc.2.1 hdisc.2.2.1 hdisc.2.2.2

/-- **Theorem 12.4** of [quarteroni2000numerical], the estimate (12.85) for the upwind method with
$k = 1$. Let $0 = x_0 < \cdots < x_n = 1$ be a partition with $n \ge 1$ and
$x_{i+1} - x_i \le h$ for all $i$, and let $\varepsilon > 0$. Let $\ell$ be a bounded linear
functional on $H^1(0, 1)$. Let $\mathring{u} \in H^1_0(0, 1) \cap H^2(0, 1)$ satisfy
$a(\mathring{u}, v) = \ell(v)$ for every $v \in X_h^{1,0}$, where $a$ is the form (12.73). Let
$\mathring{u}_h$ solve the Galerkin problem in $X_h^{1,0}$ for the form $a_h$ of (12.84) with
$\phi = \phi^{UP}$ and the same $\ell$. Then
$$|\mathring{u} - \mathring{u}_h|_{H^1(0,1)} \le C h \big( |\mathring{u}|_{H^1(0,1)} +
  |\mathring{u}|_{H^2(0,1)} \big), \qquad C = 2 + \frac{C_P |\beta|}{\varepsilon} +
  \frac{|\beta|}{2\varepsilon}, \quad C_P = \frac{1}{\sqrt{2}}.$$
The constant $C$ does not depend on $h$ or $\mathring{u}$.

The equation for $\mathring{u}$ is needed only on $X_h^{1,0}$. -/
theorem theorem_12_4_upwind {n : ℕ} {x : ℕ → ℝ} (hx : IsIntervalPartition 0 1 n x) (hn : 1 ≤ n)
    {ε β h : ℝ} (hε : 0 < ε) (hmesh : ∀ k < n, x (k + 1) - x k ≤ h)
    {ℓ : SobolevInterval 1 0 1 →L[ℝ] ℝ} {u uh : SobolevInterval 1 0 1} (U : SobolevInterval 2 0 1)
    (hU : SobolevInterval.inclusionCLM 1 0 1 U = u) (hu : u ∈ SobolevIntervalZero 0 1)
    (hexact : ∀ v ∈ FiniteElement.lagrangeSpaceZero zero_lt_one n x 1,
      EllipticInterval.form 0 1 (EllipticInterval.constLinf 0 1 ε)
        (EllipticInterval.constLinf 0 1 β) 0 u v = ℓ v)
    (hdisc : IsGalerkinSolution (equation_12_84 ε β h AdvectionDiffusion.phiUpwind) ℓ
      (FiniteElement.lagrangeSpaceZero zero_lt_one n x 1) uh) :
    SobolevInterval.seminorm 1 0 1 (u - uh)
      ≤ (2 + 1 / Real.sqrt 2 * |β| / ε + |β| / (2 * ε)) * h
        * (SobolevInterval.seminorm 1 0 1 u + SobolevInterval.seminorm 2 0 1 U) := by
  have key := AdvectionDiffusion.seminorm_sub_stabilized_le_upwind zero_lt_one hx hn hε hmesh U hU
    hu hexact hdisc
  simpa using key

/-- **Theorem 12.4** of [quarteroni2000numerical], the estimate (12.86) for the Scharfetter–Gummel
method with $k = 2$. Let $0 = x_0 < x_1 < \cdots < x_{2n} = 1$ with $n \ge 1$, where the $n$
elements $[x_{2m}, x_{2m+2}]$ have length at most $h$, and let $\varepsilon > 0$. Let $\ell$ be
a bounded linear functional on $H^1(0, 1)$. Let $\mathring{u} \in H^1_0(0, 1) \cap H^3(0, 1)$
satisfy $a(\mathring{u}, v) = \ell(v)$ for every $v \in X_h^{2,0}$, where $a$ is the form
(12.73). Let $\mathring{u}_h$ solve the Galerkin problem in $X_h^{2,0}$ for the form $a_h$ of
(12.84) with $\phi = \phi^{SG}$ and the same $\ell$. Then
$$|\mathring{u} - \mathring{u}_h|_{H^1(0,1)} \le C h^2 \big( |\mathring{u}|_{H^1(0,1)} +
  |\mathring{u}|_{H^3(0,1)} \big), \qquad C = 2 + \frac{C_P |\beta|}{\varepsilon} +
  \frac{\beta^2}{12 \varepsilon^2}, \quad C_P = \frac{1}{\sqrt{2}}.$$
The constant $C$ does not depend on $h$ or $\mathring{u}$.

The space $X_h^{2,0}$ is (12.57) at $k = 2$ on the elements $[x_{2m}, x_{2m+2}]$; its nodal
basis is `QuarteroniSaccoSaleri.Chapter12.equation_12_63_basis`. The gain of one power of $h$
over (12.85) has two sources: the quadratic interpolation estimate $|\mathring{u} - \Pi_h^2
\mathring{u}|_{H^1} \le h^2 |\mathring{u}|_{H^3}$ of (8.26), and the bound
$\phi^{SG}(\mathrm{Pe}) \le \mathrm{Pe}^2/3$, which makes the stabilization term $O(h^2)$ where
the upwind term is $O(h)$. -/
theorem equation_12_86 {n : ℕ} {x : ℕ → ℝ} (hx : IsIntervalPartition 0 1 (2 * n) x) (hn : 1 ≤ n)
    {ε β h : ℝ} (hε : 0 < ε) (hmesh : ∀ m < n, x (2 * m + 2) - x (2 * m) ≤ h)
    {ℓ : SobolevInterval 1 0 1 →L[ℝ] ℝ} {u uh : SobolevInterval 1 0 1}
    (U : SobolevInterval 3 0 1)
    (hU : SobolevInterval.inclusionCLM 1 0 1 (SobolevInterval.inclusionCLM 2 0 1 U) = u)
    (hu : u ∈ SobolevIntervalZero 0 1)
    (hexact : ∀ v ∈ FiniteElement.lagrangeSpaceZero zero_lt_one n (FiniteElement.evenNodes x) 2,
      EllipticInterval.form 0 1 (EllipticInterval.constLinf 0 1 ε)
        (EllipticInterval.constLinf 0 1 β) 0 u v = ℓ v)
    (hdisc : IsGalerkinSolution (equation_12_84 ε β h AdvectionDiffusion.phiSG) ℓ
      (FiniteElement.lagrangeSpaceZero zero_lt_one n (FiniteElement.evenNodes x) 2) uh) :
    SobolevInterval.seminorm 1 0 1 (u - uh)
      ≤ (2 + 1 / Real.sqrt 2 * |β| / ε + β ^ 2 / (12 * ε ^ 2)) * h ^ 2
        * (SobolevInterval.seminorm 1 0 1 u + SobolevInterval.seminorm 3 0 1 U) := by
  have key := AdvectionDiffusion.seminorm_sub_stabilized_le_sg_quadratic zero_lt_one hx hn hε
    hmesh U hU hu hexact hdisc
  simpa using key

end QuarteroniSaccoSaleri.Chapter12
