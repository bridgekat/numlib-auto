/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Sobolev.Interval
import Numlib.Approximation.CompositeQuadrature
import Numlib.Approximation.MarkovInequality
import Numlib.Approximation.OrthogonalPolynomial.LegendreNodes
import Numlib.LinearAlgebra.Matrix.TridiagonalToeplitz
import Numlib.FiniteDifference.Parabolic
import Numlib.FiniteElement.Interval
import NumlibSurface.QuarteroniSaccoSaleri.Chapter12.Section03

/-!
# Quarteroni, Sacco and Saleri, Section 13.3: Finite elements for the heat equation

This module formalizes Section 13.3 and Section 13.3.1 of [quarteroni2000numerical]. The heat
equation is put in the weak form (13.12) on $V = H^1_0(0, 1)$ with the bilinear form
$a(u, v) = \nu \int_0^1 u' v'$, so that $a(v, v) = \nu \|v'\|^2_{L^2}$ (13.18). A Galerkin method in
a finite-dimensional trial space $V_h$ discretizes it in space (13.13). In a basis of $V_h$ this is
the system $M \dot\xi + A_{fe} \xi = f_{fe}$ (13.14)–(13.15) with the mass matrix $M$ and the
stiffness matrix $A_{fe}$, and the $\theta$-method (13.16)–(13.17) discretizes it in time. The
stability analysis of Section 13.3.1 consists of the backward Euler estimates (13.19)–(13.21),
Remark 13.1, the eigenpairs of a form (Definition 13.1), the discrete eigenproblem (13.22), the
$\theta$-recursion in the eigenbasis, and the result that the $\theta$-method is unconditionally
stable for $\theta \ge 1/2$ and stable for $\theta < 1/2$ if and only if
$\Delta t \le 2/((1 - 2\theta) \lambda_{\max})$. This analysis uses only the inner product of $V_h$
and the form, as Remark 13.1 and Exercise 4 say, so it is stated for an arbitrary real inner product
space $V$ with a bilinear form $a$. The proofs specialize `Numlib.Variational.Evolution`, and the
matrix form specializes `Numlib.FiniteDifference.Parabolic`.

For piecewise linear elements on the uniform mesh with $h = 1/n$, the mass matrix is
$M = (h/6) \operatorname{tridiag}(1, 4, 1)$, its lumped form is $hI$ (Exercise 2), and the stiffness
matrix of the heat form is $A_{fe} = (\nu/h) \operatorname{tridiag}(-1, 2, -1)$. The generalized
eigenvalues of $A_{fe} \xi = \lambda M \xi$ are $(6\nu/h^2)(1 - \cos\theta_i)/(2 + \cos\theta_i)$,
the largest one lies between $3\nu h^{-2}$ and $12\nu h^{-2}$, and the $\theta$-method with
$\theta < 1/2$ is stable for $\Delta t \le h^2/(6\nu(1 - 2\theta))$ (13.23). For the pseudo-spectral
Galerkin approximation on $\mathbb{P}_N^0$ with the Legendre–Gauss–Lobatto inner product, the
eigenvalues are at most $\nu N^2 (N + 1)^2$, so the $\theta$-method with $\theta < 1/2$ is stable
for $\Delta t \le N^{-4}/(2\nu(1 - 2\theta))$ (13.24). A matching lower bound
$\lambda_{\max} \ge c \nu N^4$ makes a condition of this form necessary.

## Main definitions

* (13.12), `QuarteroniSaccoSaleri.Chapter13.heatForm`: the bilinear form
  $a(u, v) = \nu \int_0^1 u' v'$ on $H^1(0, 1)$.
* (13.12), `QuarteroniSaccoSaleri.Chapter13.equation_13_12`: a weak solution of the heat equation.
* (13.13), `QuarteroniSaccoSaleri.Chapter13.equation_13_13`: the semi-discrete Galerkin problem.
* (13.16), `QuarteroniSaccoSaleri.Chapter13.equation_13_16`: the $\theta$-method for the matrix
  system.
* Section 13.3, `QuarteroniSaccoSaleri.Chapter13.massMatrix`: the mass matrix
  $(h/6) \operatorname{tridiag}(1, 4, 1)$ of the uniform piecewise linear space.
* Section 13.3, `QuarteroniSaccoSaleri.Chapter13.heatStiffnessMatrix`: the stiffness matrix
  $(\nu/h) \operatorname{tridiag}(-1, 2, -1)$ of the heat form.
* (13.17), `QuarteroniSaccoSaleri.Chapter13.equation_13_17`: the $\theta$-method for the Galerkin
  problem.
* Definition 13.1, `QuarteroniSaccoSaleri.Chapter13.definition_13_1`: the eigenpairs of a bilinear
  form.
* Section 13.3.1, `QuarteroniSaccoSaleri.Chapter13.SpectralSpace`: the pseudo-spectral trial space
  $\mathbb{P}_N^0$ with the Gauss–Lobatto inner product.
* Section 13.3.1, `QuarteroniSaccoSaleri.Chapter13.SpectralSpace.spectralForm`: the pseudo-spectral
  form $a_N(u, v) = \nu (u', v')_N$.

## Main results

* (13.18), `QuarteroniSaccoSaleri.Chapter13.equation_13_18`: $a(v, v) = \nu \|v'\|^2_{L^2}$.
* Section 13.3, `QuarteroniSaccoSaleri.Chapter13.heatForm_l2_coercive`:
  $2\nu \|v\|^2_{L^2} \le a(v, v)$ on $H^1_0(0, 1)$.
* Section 13.3, `QuarteroniSaccoSaleri.Chapter13.equation_13_13_energy`: the a priori estimate for
  the semi-discrete solution.
* (13.14), `QuarteroniSaccoSaleri.Chapter13.equation_13_14`: the Galerkin problem in a basis is
  $M \dot\xi + A_{fe} \xi = f_{fe}$.
* (13.15), `QuarteroniSaccoSaleri.Chapter13.equation_13_15`: the normal form
  $\dot\xi = -M^{-1} A \xi + M^{-1} f$.
* (13.16), `QuarteroniSaccoSaleri.Chapter13.equation_13_16_iff`: the $\theta$-method (13.16) is
  solved by the explicit $\theta$-step.
* Section 13.3, `QuarteroniSaccoSaleri.Chapter13.equation_13_16_posDef`: the matrix
  $\Delta t^{-1} M + \theta A_{fe}$ is symmetric positive definite.
* Section 13.3, `QuarteroniSaccoSaleri.Chapter13.massMatrix_apply_eq_integral`: the entries of the
  mass matrix are the integrals $\int_0^1 \varphi_j \varphi_i$.
* Exercise 2, `QuarteroniSaccoSaleri.Chapter13.exercise_13_2`: the lumped mass matrix is $hI$.
* Section 13.3.1, `QuarteroniSaccoSaleri.Chapter13.pencil_hasEigenvalue_iff`: the generalized
  eigenvalues of $(A_{fe}, M)$.
* Section 13.3.1, `QuarteroniSaccoSaleri.Chapter13.pencil_maxEigenvalue_bounds`: $3\nu h^{-2} \le
  \lambda_h^{N_h} \le 12\nu h^{-2}$.
* (13.17), `QuarteroniSaccoSaleri.Chapter13.equation_13_17_iff_thetaStep`: (13.17) in coordinates is
  (13.16).
* Exercise 3, `QuarteroniSaccoSaleri.Chapter13.exercise_13_3`:
  $(u - v, u) \ge \frac{1}{2}(\|u\|^2 - \|v\|^2)$.
* (13.19), `QuarteroniSaccoSaleri.Chapter13.equation_13_19`: the energy estimate for one backward
  Euler step.
* (13.20), `QuarteroniSaccoSaleri.Chapter13.equation_13_20`: the unconditional stability of backward
  Euler.
* (13.21), `QuarteroniSaccoSaleri.Chapter13.equation_13_21`: the stability estimate of backward
  Euler with sources.
* Remark 13.1, `QuarteroniSaccoSaleri.Chapter13.remark_13_1`: (13.20) for any form that is coercive
  in the $L^2$ norm.
* Exercise 4, `QuarteroniSaccoSaleri.Chapter13.exercise_13_4`: (13.21) for any form that is coercive
  in the $L^2$ norm.
* (13.22), `QuarteroniSaccoSaleri.Chapter13.equation_13_22`: the discrete eigenproblem is the
  generalized eigenproblem $A_{fe} \xi = \lambda_h M \xi$.
* Section 13.3.1, `QuarteroniSaccoSaleri.Chapter13.equation_13_22_pos`: the eigenvalues of a
  coercive form are positive.
* Section 13.3.1, `QuarteroniSaccoSaleri.Chapter13.equation_13_22_basis`: a symmetric form has an
  orthonormal basis of eigenvectors.
* Section 13.3.1, `QuarteroniSaccoSaleri.Chapter13.thetaMethod_eigen_recursion`: the $\theta$-step
  multiplies each eigencoordinate by $(1 - (1 - \theta) \lambda \Delta t)/(1 + \theta \lambda \Delta
  t)$.
* Section 13.3.1, `QuarteroniSaccoSaleri.Chapter13.thetaMethod_stable_of_half_le`: for
  $\theta \ge 1/2$ the $\theta$-method is unconditionally stable.
* Section 13.3.1, `QuarteroniSaccoSaleri.Chapter13.thetaMethod_stable_iff_of_lt_half`: for
  $0 \le \theta < 1/2$ it is stable if and only if $\Delta t \le 2/((1 - 2\theta) \lambda_{\max})$.
* (13.23), `QuarteroniSaccoSaleri.Chapter13.equation_13_23`: for piecewise linear elements,
  $\Delta t \le h^2/(6\nu(1 - 2\theta))$ gives stability.
* Section 13.3.1, `QuarteroniSaccoSaleri.Chapter13.SpectralSpace.spectralForm_eigenvalue_le`: the
  pseudo-spectral eigenvalues are at most $\nu N^2 (N + 1)^2$.
* (13.24), `QuarteroniSaccoSaleri.Chapter13.equation_13_24`: for the pseudo-spectral method,
  $\Delta t \le N^{-4}/(2\nu(1 - 2\theta))$ gives stability.
* (13.24), `QuarteroniSaccoSaleri.Chapter13.equation_13_24_lower`: the largest pseudo-spectral
  eigenvalue is at least $c \nu N^4$.

## Conventions

* The space $V$ is the trial space $V_h$ of the source, a real inner product space with the $L^2$
  inner product of the source, and `a : SesqForm ℝ V` is the bilinear form restricted to it.
* A form $a$ is positive if $a(v, v) \ge 0$ for all $v$, which is `a.IsCoerciveWith 0`, and coercive
  in the $L^2$ norm with constant $\alpha$ if $a(v, v) \ge \alpha \|v\|^2$ for all $v$, which is
  `a.IsCoerciveWith α`. The predicate is `SesqForm.IsCoerciveWith` of `Numlib.Variational.Forms`.
* The space $H^1(0, 1)$ is `SobolevInterval 1 0 1`, and its $j$-th weak derivative in $L^2(0, 1)$ is
  `SobolevInterval.deriv u j`. So `‖SobolevInterval.deriv u 0‖` is $\|u\|_{L^2(0,1)}$ and
  `‖SobolevInterval.deriv u 1‖` is $\|\partial_x u\|_{L^2(0,1)}$. The space $H^1_0(0, 1)$ is
  `SobolevIntervalZero 0 1`.

## Implementation notes

* The pseudo-spectral trial space carries the nodes and weights as parameters of its type, so that
  the inner product can be an instance. The inner product is definite when they are the
  Legendre–Gauss–Lobatto ones, which is the hypothesis `[Fact
  (QuarteroniSaccoSaleri.Chapter12.IsLegendreLobatto N x w)]`.
* The lower bound $\lambda_{\max} \ge c \nu N^4$ uses the Lagrange basis polynomial
  $l_j \in \mathbb{P}_N^0$ of the interior Gauss–Lobatto node $x_j$ nearest to $1$. Its Rayleigh
  quotient is at least $\nu/((1 - x_j) w_j)$, and the Sturm comparison for the Legendre equation in
  the variable $\arccos x$ (`Numlib.Approximation.OrthogonalPolynomial.LegendreNodes`) gives
  $1 - x_j \le 81\pi^2/(32 N^2)$ and $w_j \le 2048/N^2$.
* For the convergence estimates after (13.24), the library has the stability half, (13.21) and the
  $\theta$-step (13.17), and the approximation pieces: the $L^2$ projection error for $r = 1$
  (`Numlib.Approximation.PiecewiseLinearL2`), the interpolation estimate of degree $r$ in broken
  form (`Numlib.Approximation.SobolevInterpolation`), and, for $f = 0$, the semigroup smoothing
  $\|A S(t) u_0\| \le \|u_0\|/t$ of Theorem 7.7 of [brezis2011functional] for the Dirichlet
  Laplacian (`Numlib.Analysis.PDE.Heat`).

## Deviations from the source

* **Exercise 2, the hint** (typo). The hint prints $m_{ij} = (h/6) \cdot \{1/2 \ (i \neq j), 1 \
  (i = j)\}$. The exact integrals are $\int \varphi_i^2 = 2h/3$ and
  $\int \varphi_i \varphi_{i \pm 1} = h/6$, so $M = (h/6) \operatorname{tridiag}(1, 4, 1)$, which is
  the matrix that Program 100 of the source assembles. See
  `QuarteroniSaccoSaleri.Chapter13.massMatrix_apply_eq_integral`.
* **Inverse estimate of Section 13.3.1** (reading). The source prints $\lambda_h^{N_h} = c_2 h^{-2}$
  for the upper bound. It is read as $\lambda_h^{N_h} \le c_2 h^{-2}$. See
  `QuarteroniSaccoSaleri.Chapter13.pencil_maxEigenvalue_bounds`.
* **Unconditional stability for $\theta \ge 1/2$** (generalization). The proof of the source uses
  the eigenbasis of a symmetric form. The statement holds for every positive form. See
  `QuarteroniSaccoSaleri.Chapter13.thetaMethod_stable_of_half_le`.
* **(13.24)** (generalization). The source assumes $\theta \ge 0$. Sufficiency holds for every
  $\theta < 1/2$. See `QuarteroniSaccoSaleri.Chapter13.equation_13_24`.

## Not formalized

* The existence and uniqueness of weak solutions of (13.12). This is Bochner-space theory (the
  theorem of Lions).
* The sentence after Definition 13.1: a symmetric coercive form on $H^1_0$ has an unbounded sequence
  of positive eigenvalues whose eigenfunctions form a basis of $V$. This is the spectral theorem for
  an operator with compact resolvent.
* The convergence estimates after (13.24), $\|u(t^k) - u_h^k\|_{L^2} \le C(u_0, f, u)(\Delta
  t^{p(\theta)} + h^{r+1})$ with $p(\theta) = 1$ for $\theta \neq 1/2$ and $p(1/2) = 2$, and, for
  $f = 0$ and $\theta \in \{1, 1/2\}$, $\|u(t^k) - u_h^k\| \le C[(h/\sqrt{t^k})^{r+1} + (\Delta
  t/t^k)^{p(\theta)}] \|u_0\|$. The source quotes them from its reference QV94, pp. 394–395, without
  proof. They need the time regularity of the weak solution of (13.12) ($u_{tt} \in L^2(0, 1)$
  uniformly in $t$, and $u_{ttt}$ for $\theta = 1/2$), which needs the spaces $L^2(0, T; V)$ and
  $H^1(0, T; H^{-1})$ and the existence theorem of Lions; the time truncation error of the
  $\theta$-method against the semi-discrete problem; and the relation between the $H^{r+1}(0, 1)$
  norm of `SobolevInterval` and the broken seminorm of the interpolation estimate. The constant
  $C(u_0, f, u)$ must be uniform in $h$ and $\Delta t$, so no weaker form is available.
* Equation (13.25) of Section 13.4, the only numbered result of that section, which has no module of
  its own: for the cG(1)dG(1) space–time discretization of (13.12) on $[0, 1] \times [0, T]$, with
  continuous piecewise linear elements in space and discontinuous piecewise linear elements in time
  on time slabs whose meshes may change from slab to slab, $\|u(t^n) - U^n\|_{L^2(0,1)} \le
  C(u_{0h}, f, u, n)(\Delta t^2 + h^2)$. The source quotes it from its reference EEHJ96 without
  proof. It needs the space–time finite element spaces with their time jumps; the exact solution of
  (13.12) with a source term, which needs a Duhamel formula, the weak formulation with
  $u' \in L^2(0, T; H^{-1})$, and a bridge between the one-dimensional and the Euclidean Sobolev
  spaces; and the space–time duality argument of the cited proof, with parabolic regularity in time
  for the problem with a source. The constant is not specified, so no weaker form is available.
* The rest of Section 13.4: the space–time spaces and the algebraic forms of the method for $q = 0$
  (backward Euler with the projection matrix $B_{k,k-1}$ on the right-hand side) and $q = 1$ (a
  $2 \times 2$ block system) are unnumbered, and Example 13.2 is a numerical experiment.
-/

open Set Filter Topology MeasureTheory
open scoped Real Matrix RealInnerProductSpace

namespace QuarteroniSaccoSaleri.Chapter13

noncomputable section

/-! ### The weak formulation (13.12) and its form -/

/-- **Equation (13.12)** of [quarteroni2000numerical], the bilinear form of the heat equation. For
$\nu \in \mathbb{R}$, it is the form
$$a(u, v) = \nu \int_0^1 u' v'$$
on $H^1(0, 1)$, where $u'$ and $v'$ are the weak derivatives.

It is the form (12.44) with $\alpha = \nu$ and $\beta = \gamma = 0$. The weak problem uses its
restriction to $H^1_0(0, 1)$. -/
def heatForm (ν : ℝ) : SesqForm ℝ (SobolevInterval 1 0 1) :=
  ν • ((((innerSL ℝ : SesqForm ℝ (Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1)))).comp
    (SobolevInterval.derivL 1 0 1 1)).flip.comp (SobolevInterval.derivL 1 0 1 1)).flip)

/-- For $\nu \in \mathbb{R}$ and $u, v \in H^1(0, 1)$, the heat form is
$a(u, v) = \nu (u', v')_{L^2(0,1)}$, the $L^2$ inner product of the weak derivatives. -/
@[simp]
theorem heatForm_apply (ν : ℝ) (u v : SobolevInterval 1 0 1) :
    heatForm ν u v = ν * ⟪SobolevInterval.deriv u 1, SobolevInterval.deriv v 1⟫ := rfl

/-- **Equation (13.18)** of [quarteroni2000numerical]. For $\nu \in \mathbb{R}$ and
$v \in H^1(0, 1)$,
$$a(v, v) = \nu \|\partial_x v\|^2_{L^2(0,1)}.$$
-/
theorem equation_13_18 (ν : ℝ) (v : SobolevInterval 1 0 1) :
    heatForm ν v v = ν * ‖SobolevInterval.deriv v 1‖ ^ 2 := by
  rw [heatForm_apply, real_inner_self_eq_norm_sq]

/-- For $\nu \in \mathbb{R}$, the heat form is symmetric: $a(u, v) = a(v, u)$. -/
theorem heatForm_isHermitian (ν : ℝ) : (heatForm ν).IsHermitian := fun u v => by
  simp only [heatForm_apply, RCLike.conj_to_real, real_inner_comm]

/-- **Section 13.3** of [quarteroni2000numerical], coercivity of the heat form in the $L^2$ norm.
Let $\nu > 0$ and $u \in H^1_0(0, 1)$. Then
$$2\nu \|u\|^2_{L^2(0,1)} \le a(u, u).$$

This is the constant $\gamma = \nu/C_P^2$ of Sections 13.1 and 13.3, with the Poincaré constant
$C_P = 1/\sqrt{2}$ of $(0, 1)$ from (12.16). It is the constant of (13.7) and of the energy
estimate after (13.13). -/
theorem heatForm_l2_coercive {ν : ℝ} (hν : 0 < ν) {u : SobolevInterval 1 0 1}
    (hu : u ∈ SobolevIntervalZero 0 1) :
    2 * ν * ‖SobolevInterval.deriv u 0‖ ^ 2 ≤ heatForm ν u u := by
  have h := SobolevIntervalZero.norm_deriv_zero_le (by norm_num : (0 : ℝ) < 1) hu
  have hsq : ‖SobolevInterval.deriv u 0‖ ^ 2 ≤ 1 / 2 * ‖SobolevInterval.deriv u 1‖ ^ 2 := by
    rw [show ((1 : ℝ) - 0) / Real.sqrt 2 = 1 / Real.sqrt 2 by norm_num] at h
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    rw [mul_pow, div_pow, one_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] at h2
    linarith
  rw [equation_13_18]
  nlinarith

/-- **Equation (13.12)** of [quarteroni2000numerical], the weak heat equation. Let
$\nu, T \in \mathbb{R}$, $f : \mathbb{R} \to L^2(0, 1)$ and $u_0 \in H^1(0, 1)$. A function
$u : \mathbb{R} \to H^1(0, 1)$ is a **weak solution** if $u(t) \in H^1_0(0, 1)$ for
$t \in [0, T]$, $u(0) = u_0$, and $u$ has a time derivative $\partial_t u$ in $L^2(0, 1)$, taken
within $[0, T]$, such that for every $t \in [0, T]$ and every $v \in H^1_0(0, 1)$
$$(\partial_t u(t), v)_{L^2} + a(u(t), v) = (f(t), v)_{L^2}.$$

Only the definition is stated. The existence and uniqueness of weak solutions is Bochner-space
theory (the theorem of Lions) and is not formalized. -/
def equation_13_12 (ν T : ℝ) (f : ℝ → Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (u₀ : SobolevInterval 1 0 1) (u : ℝ → SobolevInterval 1 0 1) : Prop :=
  (∀ t ∈ Icc (0 : ℝ) T, u t ∈ SobolevIntervalZero 0 1) ∧ u 0 = u₀ ∧
    ∃ u' : ℝ → Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1)), ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (fun s => SobolevInterval.deriv (u s) 0) (u' t) (Icc 0 T) t ∧
        ∀ v ∈ SobolevIntervalZero 0 1,
          ⟪u' t, SobolevInterval.deriv v 0⟫ + heatForm ν (u t) v
            = ⟪f t, SobolevInterval.deriv v 0⟫

/-! ### The semi-discrete Galerkin problem (13.13) -/

section Galerkin

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- **Equation (13.13)** of [quarteroni2000numerical], the semi-discrete Galerkin problem. Let $V$
be a real inner product space (the trial space $V_h$ with the $L^2$ inner product), $a$ a
bounded bilinear form on $V$, $F : \mathbb{R} \to V^*$, $u_0 \in V$ and $T \in \mathbb{R}$. A
function $u : \mathbb{R} \to V$ solves the problem if $u(0) = u_0$ and $u$ has a derivative
$\partial_t u$ within $[0, T]$ such that for every $t \in [0, T]$ and every $v \in V$
$$(\partial_t u(t), v) + a(u(t), v) = F(t)(v).$$

The definition is `Variational.IsSemidiscreteGalerkin` for a form that does not depend on time. -/
def equation_13_13 (a : SesqForm ℝ V) (F : ℝ → V →L[ℝ] ℝ) (u₀ : V) (T : ℝ) (u : ℝ → V) : Prop :=
  Variational.IsSemidiscreteGalerkin (fun _ => a) F u₀ T u

/-- **Section 13.3** of [quarteroni2000numerical], the a priori estimate for the semi-discrete
solution (the display after (13.13)). Let $u$ solve (13.13), let $\gamma > 0$ with
$\gamma \|v\|^2 \le a(v, v)$ for all $v \in V$, and let $\varphi$ be continuous on $[0, T]$ with
$\|F(t)\| \le \varphi(t)$ there. Then for every $t \in [0, T]$
$$\|u(t)\|^2 \le e^{-\gamma t} \|u_0\|^2 + \frac{1}{\gamma} \int_0^t e^{\gamma(s - t)}
  \varphi(s)^2 \, ds.$$

This is $E_h(t) \le e^{-\gamma t} E_h(0) + \gamma^{-1} \int_0^t e^{\gamma(s - t)} F(s)\, ds$
with $E_h(t) = \|u_h(t)\|^2_{L^2}$ and $F(t) = \varphi(t)^2 = \|f(t)\|^2_{L^2}$. For the heat
equation $\gamma = \nu/C_P^2$ by `QuarteroniSaccoSaleri.Chapter13.heatForm_l2_coercive`. -/
theorem equation_13_13_energy {a : SesqForm ℝ V} {F : ℝ → V →L[ℝ] ℝ} {u₀ : V} {T : ℝ} {u : ℝ → V}
    (h : equation_13_13 a F u₀ T u) {γ : ℝ} (hγ : 0 < γ) (hcoer : a.IsCoerciveWith γ)
    {φ : ℝ → ℝ} (hφ : ContinuousOn φ (Icc 0 T)) (hF : ∀ t ∈ Icc 0 T, ‖F t‖ ≤ φ t)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖u t‖ ^ 2 ≤ Real.exp (-γ * t) * ‖u₀‖ ^ 2
      + γ⁻¹ * ∫ s in (0 : ℝ)..t, Real.exp (γ * (s - t)) * φ s ^ 2 :=
  h.norm_sq_le_exp hγ (fun _ _ => hcoer) hφ hF ht

end Galerkin

/-! ### The matrix form (13.14)–(13.16) -/

section MatrixForm

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable {ι : Type*} [Fintype ι]

/-- **Equation (13.14)** of [quarteroni2000numerical], the matrix form of the semi-discrete problem.
Let $V$ be finite-dimensional with a basis $(\varphi_i)$, and let $a$, $F$, $u_0$, $T$ and $u$
be as in (13.13). Then $u$ solves (13.13) if and only if its coordinate vector $\xi(t)$ solves
$$M \dot\xi + A_{fe} \xi = f_{fe}, \quad t \in [0, T], \qquad \xi(0) = \xi_0,$$
with the mass matrix $M_{ij} = (\varphi_j, \varphi_i)$, the stiffness matrix
$(A_{fe})_{ij} = a(\varphi_j, \varphi_i)$, the load vector $(f_{fe})_i(t) = F(t)(\varphi_i)$,
and the coordinate vector $\xi_0$ of $u_0$.

The matrix system is `FiniteDifference.IsSemidiscrete`, and the Gram matrices are
`SesqForm.gramMatrix`. -/
theorem equation_13_14 (φ : Module.Basis ι ℝ V) (a : SesqForm ℝ V) (F : ℝ → V →L[ℝ] ℝ) (u₀ : V)
    (T : ℝ) (u : ℝ → V) :
    equation_13_13 a F u₀ T u ↔
      FiniteDifference.IsSemidiscrete (SesqForm.gramMatrix (innerSL ℝ) φ) (a.gramMatrix φ)
        (fun t i => F t (φ i)) (φ.equivFun u₀) T (fun t => φ.equivFun (u t)) :=
  FiniteDifference.isSemidiscreteGalerkin_iff_isSemidiscrete φ a F u₀ T u

-- the linter does not see the `Fintype` inside `Matrix.PosDef`
set_option linter.unusedFintypeInType false in
omit [FiniteDimensional ℝ V] in
/-- **Section 13.3** of [quarteroni2000numerical], the mass matrix is nonsingular. For a basis
$(\varphi_i)$ of $V$, the Gram matrix $M_{ij} = (\varphi_j, \varphi_i)$ of the inner product is
symmetric positive definite. -/
theorem massMatrix_gram_posDef (φ : Module.Basis ι ℝ V) :
    (SesqForm.gramMatrix (innerSL ℝ) φ).PosDef :=
  FiniteDifference.massMatrix_posDef φ.linearIndependent

/-- **Equation (13.15)** of [quarteroni2000numerical], the normal form. Let $M$ be symmetric
positive definite, and let $A$, $f$, $\xi_0$, $T$ and $\xi$ be given. Then $\xi$ solves
$M \dot\xi + A \xi = f$ with $\xi(0) = \xi_0$ on $[0, T]$ if and only if it solves
$$\dot\xi = -M^{-1} A \xi + M^{-1} f, \qquad \xi(0) = \xi_0.$$
-/
theorem equation_13_15 [DecidableEq ι] {M : Matrix ι ι ℝ} (hM : M.PosDef) (A : Matrix ι ι ℝ)
    (f : ℝ → ι → ℝ) (ξ₀ : ι → ℝ) (T : ℝ) (ξ : ℝ → ι → ℝ) :
    FiniteDifference.IsSemidiscrete M A f ξ₀ T ξ ↔
      FiniteDifference.IsSemidiscrete 1 (M⁻¹ * A) (fun t => M⁻¹ *ᵥ f t) ξ₀ T ξ :=
  FiniteDifference.IsSemidiscrete.iff_normalForm hM.isUnit A f ξ₀ T ξ

/-- **Equation (13.16)** of [quarteroni2000numerical], the $\theta$-method for the matrix system.
For matrices $M$ and $A$, $\theta, \Delta t \in \mathbb{R}$, source vectors $f^k$, $f^{k+1}$ and
iterates $\xi^k$, $\xi^{k+1}$, the relation is
$$M \frac{\xi^{k+1} - \xi^k}{\Delta t} + A \bigl(\theta \xi^{k+1} + (1 - \theta) \xi^k\bigr) =
  \theta f^{k+1} + (1 - \theta) f^k.$$

The arguments `f₀`, `f₁`, `ξ` and `ξ'` are $f^k$, $f^{k+1}$, $\xi^k$ and $\xi^{k+1}$. -/
def equation_13_16 (M A : Matrix ι ι ℝ) (θ Δt : ℝ) (f₀ f₁ ξ ξ' : ι → ℝ) : Prop :=
  M *ᵥ (Δt⁻¹ • (ξ' - ξ)) + A *ᵥ (θ • ξ' + (1 - θ) • ξ) = θ • f₁ + (1 - θ) • f₀

/-- Let $M$ be symmetric positive definite, let $A$ satisfy $x^T A x \ge 0$ for all $x$, and let
$\theta \ge 0$ and $\Delta t > 0$. Then $\xi^{k+1}$ satisfies the $\theta$-method (13.16) if and
only if it is `FiniteDifference.thetaStep` of $\xi^k$, the step with the system matrix
$M + \theta \Delta t A$, which is invertible. -/
theorem equation_13_16_iff [DecidableEq ι] {M A : Matrix ι ι ℝ} (hM : M.PosDef)
    (hA : ∀ x, 0 ≤ x ⬝ᵥ (A *ᵥ x)) {θ Δt : ℝ} (hθ : 0 ≤ θ) (hΔt : 0 < Δt) (f₀ f₁ ξ ξ' : ι → ℝ) :
    equation_13_16 M A θ Δt f₀ f₁ ξ ξ' ↔ ξ' = FiniteDifference.thetaStep M A θ Δt f₀ f₁ ξ :=
  (FiniteDifference.eq_thetaStep_iff_divided
    (FiniteDifference.isUnit_add_smul_of_posDef hM hA (mul_nonneg hθ hΔt.le)) hΔt.ne'
    f₀ f₁ ξ ξ').symm

omit [Fintype ι] in
/-- **Section 13.3** of [quarteroni2000numerical], the matrix of the linear system of the
$\theta$-method. Let $M$ and $A$ be symmetric positive definite, $\theta \ge 0$ and
$\Delta t > 0$. Then
$$K = \Delta t^{-1} M + \theta A$$
is symmetric positive definite. So its Cholesky factorization can be computed once for all time
steps. -/
theorem equation_13_16_posDef {M A : Matrix ι ι ℝ} (hM : M.PosDef)
    (hA : A.PosDef) {θ Δt : ℝ} (hθ : 0 ≤ θ) (hΔt : 0 < Δt) :
    (Δt⁻¹ • M + θ • A).PosDef :=
  (hM.smul (inv_pos.2 hΔt)).add_posSemidef (hA.posSemidef.smul hθ)

/-- **Section 13.3** of [quarteroni2000numerical], the mass matrix of the piecewise linear finite
element space (12.57) on the uniform mesh with $h = 1/n$. It is the matrix of order $n - 1$
$$M = \frac{h}{6} \operatorname{tridiag}(1, 4, 1),$$
with $2h/3$ on the diagonal and $h/6$ on the two neighbouring diagonals. -/
def massMatrix (n : ℕ) : Matrix (Fin (n - 1)) (Fin (n - 1)) ℝ :=
  (1 / (6 * (n : ℝ))) • Matrix.symmTridiagonalToeplitz (n - 1) 1 4

/-- For $n \ge 1$, the mass matrix $M = (h/6) \operatorname{tridiag}(1, 4, 1)$ is symmetric positive
definite, because $\operatorname{tridiag}(1, 4, 1)$ is strictly diagonally dominant. -/
theorem massMatrix_posDef {n : ℕ} (hn : 0 < n) : (massMatrix n).PosDef := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  exact (Matrix.posDef_symmTridiagonalToeplitz (n - 1) (by norm_num)).smul
    (div_pos one_pos (by linarith))

end MatrixForm

/-! ### The mass matrix of the uniform piecewise linear space -/

section MassMatrix

variable {n : ℕ} {x : ℕ → ℝ}

/-- Let $0 = x_0 < x_1 < \cdots < x_n = 1$ be the uniform mesh, $n \ge 1$, with
$x_{k+1} - x_k = 1/n$. Then the mass matrix $M = (h/6) \operatorname{tridiag}(1, 4, 1)$ is the
Gram matrix `FiniteElement.massMatrix` of the interior hat functions
$\varphi_1, \ldots, \varphi_{n-1}$ for the $L^2(0, 1)$ inner product. -/
theorem massMatrix_eq_gram (hx : IsIntervalPartition 0 1 n x) (hn : 1 ≤ n)
    (huni : ∀ k < n, x (k + 1) - x k = 1 / (n : ℝ)) :
    massMatrix n
      = FiniteElement.massMatrix 0 1 fun i : Fin (n - 1) ↦ FiniteElement.hatFunction hx hn
        ((i : ℕ) + 1) := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [FiniteElement.massMatrix_uniform_eq hx hn (by positivity) huni, massMatrix]
  congr 1
  field_simp

/-- **Section 13.3** of [quarteroni2000numerical], the entries of the mass matrix. Let
$0 = x_0 < x_1 < \cdots < x_n = 1$ be the uniform mesh, $n \ge 1$, with $x_{k+1} - x_k = 1/n$,
and let $\varphi_i$ be the hat function of the node $x_i$. Then
$$m_{ij} = \int_0^1 \varphi_j \varphi_i.$$
So $\int \varphi_i^2 = 2h/3$, $\int \varphi_i \varphi_{i \pm 1} = h/6$, and
$\int \varphi_i \varphi_j = 0$ for $|i - j| \ge 2$.

**Typo.** The hint of Exercise 2 prints $m_{ij} = (h/6) \cdot \{1/2 \ (i \neq j), 1 \ (i =
j)\}$. The values above are the exact integrals; they give
$M = (h/6) \operatorname{tridiag}(1, 4, 1)$, which is the matrix that Program 100 of the source
assembles.

In Lean the row index `i : Fin (n - 1)` stands for the node $x_{i+1}$. -/
theorem massMatrix_apply_eq_integral (hx : IsIntervalPartition 0 1 n x) (hn : 1 ≤ n)
    (huni : ∀ k < n, x (k + 1) - x k = 1 / (n : ℝ)) (i j : Fin (n - 1)) :
    massMatrix n i j = ∫ t in Set.Ioo (0 : ℝ) 1,
      FiniteElement.hatFun n x ((j : ℕ) + 1) t * FiniteElement.hatFun n x ((i : ℕ) + 1) t := by
  rw [massMatrix_eq_gram hx hn huni, FiniteElement.massMatrix, FiniteElement.stiffnessMatrix_apply,
    FiniteElement.form_apply_hatFunction hx hn 0 0 1 ((i : ℕ) + 1) ((j : ℕ) + 1)]
  refine setIntegral_congr_fun measurableSet_Ioo fun t _ ↦ ?_
  simp [FiniteElement.hatFormIntegrand]

/-- **Exercise 2 of Chapter 13** of [quarteroni2000numerical], mass lumping. Let
$0 = x_0 < x_1 < \cdots < x_n = 1$ be a mesh with $n \ge 1$ and $x_k = kh$ for $k \le n$, and
let $\varphi_i$ be the hat function of the node $x_i$. Then the composite trapezoidal rule
(9.11) applied to $\int_0^1 \varphi_j \varphi_i$ gives
$$h \sum_k \varphi_j(x_k) \varphi_i(x_k) = h \delta_{ij}.$$
So the lumped mass matrix is $\tilde M = hI$, which is nonsingular. The exact integrals are
those of `QuarteroniSaccoSaleri.Chapter13.massMatrix_apply_eq_integral`.

The rule is `Quadrature.trapezoidSum`, and the index `i : Fin (n - 1)` stands for the node
$x_{i+1}$. -/
theorem exercise_13_2 (hx : IsIntervalPartition 0 1 n x) (hn : 1 ≤ n) {h : ℝ}
    (hxu : ∀ k ≤ n, x k = (k : ℝ) * h) (i j : Fin (n - 1)) :
    Quadrature.trapezoidSum (fun t ↦ FiniteElement.hatFun n x ((j : ℕ) + 1) t
        * FiniteElement.hatFun n x ((i : ℕ) + 1) t) 0 h n
      = if i = j then h else 0 := by
  have hI : (i : ℕ) + 1 < n := by have := i.isLt; omega
  have hJ : (j : ℕ) + 1 < n := by have := j.isLt; omega
  have hnode : ∀ k : ℕ, k ≤ n → ∀ m : ℕ,
      FiniteElement.hatFun n x m ((0 : ℝ) + (k : ℝ) * h) = if m = k then 1 else 0 := by
    intro k hk m
    rw [show (0 : ℝ) + (k : ℝ) * h = x k by rw [hxu k hk]; ring]
    exact FiniteElement.hatFun_apply_node hx hn hk
  have hterm : ∀ k ∈ Finset.range n,
      h / 2 * (FiniteElement.hatFun n x ((j : ℕ) + 1) ((0 : ℝ) + (k : ℝ) * h)
          * FiniteElement.hatFun n x ((i : ℕ) + 1) ((0 : ℝ) + (k : ℝ) * h)
        + FiniteElement.hatFun n x ((j : ℕ) + 1) ((0 : ℝ) + ((k : ℝ) + 1) * h)
          * FiniteElement.hatFun n x ((i : ℕ) + 1) ((0 : ℝ) + ((k : ℝ) + 1) * h))
      = h / 2 * ((if (j : ℕ) + 1 = k then (1 : ℝ) else 0)
            * (if (i : ℕ) + 1 = k then (1 : ℝ) else 0)
          + (if (j : ℕ) + 1 = k + 1 then (1 : ℝ) else 0)
            * (if (i : ℕ) + 1 = k + 1 then (1 : ℝ) else 0)) := by
    intro k hk
    have hkn : k ≤ n := le_of_lt (Finset.mem_range.1 hk)
    have hk1 : k + 1 ≤ n := Finset.mem_range.1 hk
    have hcast : (0 : ℝ) + ((k : ℝ) + 1) * h = (0 : ℝ) + ((k + 1 : ℕ) : ℝ) * h := by
      push_cast; ring
    rw [hnode k hkn, hnode k hkn, hcast, hnode (k + 1) hk1, hnode (k + 1) hk1]
  rw [Quadrature.trapezoidSum, Finset.sum_congr rfl hterm, ← Finset.mul_sum,
    Finset.sum_add_distrib]
  by_cases hij : i = j
  · subst hij
    have hc1 : ∀ k ∈ Finset.range n, ((if (i : ℕ) + 1 = k then (1 : ℝ) else 0)
        * (if (i : ℕ) + 1 = k then (1 : ℝ) else 0)) = if (i : ℕ) + 1 = k then (1 : ℝ) else 0 :=
      fun k _ ↦ by split_ifs <;> ring
    have hc2 : ∀ k ∈ Finset.range n, ((if (i : ℕ) + 1 = k + 1 then (1 : ℝ) else 0)
        * (if (i : ℕ) + 1 = k + 1 then (1 : ℝ) else 0)) = if (i : ℕ) = k then (1 : ℝ) else 0 := by
      intro k _
      by_cases hk : (i : ℕ) = k
      · simp [hk]
      · simp [hk]
    have e1 : ∑ k ∈ Finset.range n, (if (i : ℕ) + 1 = k then (1 : ℝ) else 0)
        * (if (i : ℕ) + 1 = k then (1 : ℝ) else 0) = 1 := by
      rw [Finset.sum_congr rfl hc1,
        Finset.sum_ite_eq (Finset.range n) ((i : ℕ) + 1) (fun _ ↦ (1 : ℝ))]
      simp [Finset.mem_range, hI]
    have e2 : ∑ k ∈ Finset.range n, (if (i : ℕ) + 1 = k + 1 then (1 : ℝ) else 0)
        * (if (i : ℕ) + 1 = k + 1 then (1 : ℝ) else 0) = 1 := by
      rw [Finset.sum_congr rfl hc2,
        Finset.sum_ite_eq (Finset.range n) ((i : ℕ)) (fun _ ↦ (1 : ℝ))]
      simp [Finset.mem_range]
      omega
    rw [e1, e2]
    simp
    ring
  · have e0 : ∀ k ∈ Finset.range n, ((if (j : ℕ) + 1 = k then (1 : ℝ) else 0)
        * (if (i : ℕ) + 1 = k then (1 : ℝ) else 0)) = 0 := by
      intro k _
      have : ¬ ((j : ℕ) + 1 = k ∧ (i : ℕ) + 1 = k) := by
        rintro ⟨h1, h2⟩
        exact hij (Fin.ext (by omega))
      split_ifs with a1 a2 <;> simp_all
    have e1 : ∀ k ∈ Finset.range n, ((if (j : ℕ) + 1 = k + 1 then (1 : ℝ) else 0)
        * (if (i : ℕ) + 1 = k + 1 then (1 : ℝ) else 0)) = 0 := by
      intro k _
      have : ¬ ((j : ℕ) + 1 = k + 1 ∧ (i : ℕ) + 1 = k + 1) := by
        rintro ⟨h1, h2⟩
        exact hij (Fin.ext (by omega))
      split_ifs with a1 a2 <;> simp_all
    rw [Finset.sum_congr rfl e0, Finset.sum_congr rfl e1]
    simp [hij]

end MassMatrix

/-! ### The eigenvalues of the pencil $(A_{fe}, M)$ (Section 13.3.1) -/

section Pencil

open scoped Real

/-- **Section 13.3** of [quarteroni2000numerical], the stiffness matrix of the heat form on the
uniform piecewise linear space with $h = 1/n$. For $\nu \in \mathbb{R}$ it is the matrix of
order $n - 1$
$$A_{fe} = \frac{\nu}{h} \operatorname{tridiag}(-1, 2, -1).$$
-/
noncomputable def heatStiffnessMatrix (ν : ℝ) (n : ℕ) :
    Matrix (Fin (n - 1)) (Fin (n - 1)) ℝ :=
  (ν * (n : ℝ)) • Matrix.symmTridiagonalToeplitz (n - 1) (-1) 2

/-- Let $0 = x_0 < x_1 < \cdots < x_n = 1$ be the uniform mesh, $n \ge 1$, with
$x_{k+1} - x_k = 1/n$, and let $\nu \in \mathbb{R}$. Then the stiffness matrix $A_{fe} = (\nu/h)
\operatorname{tridiag}(-1, 2, -1)$ is the Gram matrix `FiniteElement.stiffnessMatrix` of the
interior hat functions for the heat form $a(u, v) = \nu \int u' v'$. -/
theorem heatStiffnessMatrix_eq_gram {n : ℕ} {x : ℕ → ℝ} (hx : IsIntervalPartition 0 1 n x)
    (hn : 1 ≤ n) (huni : ∀ k < n, x (k + 1) - x k = 1 / (n : ℝ)) (ν : ℝ) :
    heatStiffnessMatrix ν n
      = FiniteElement.stiffnessMatrix 0 1 (EllipticInterval.constLinf 0 1 ν)
        (EllipticInterval.constLinf 0 1 0) (EllipticInterval.constLinf 0 1 0)
        fun i : Fin (n - 1) ↦ FiniteElement.hatFunction hx hn ((i : ℕ) + 1) := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [FiniteElement.stiffnessMatrix_uniform_eq hx hn (by positivity) huni ν 0 0,
    heatStiffnessMatrix]
  simp only [zero_div, zero_mul, zero_smul, add_zero]
  congr 1
  field_simp

/-- For $c, d, a, b, a', b' \in \mathbb{R}$, the symmetric tridiagonal Toeplitz matrices of order
$N$ satisfy
$$c \operatorname{tridiag}(a, b, a) - d \operatorname{tridiag}(a', b', a') =
  \operatorname{tridiag}(ca - da', cb - db', ca - da').$$
-/
theorem smul_sub_smul_symmTridiagonalToeplitz (N : ℕ) (c d a b a' b' : ℝ) :
    c • Matrix.symmTridiagonalToeplitz N a b - d • Matrix.symmTridiagonalToeplitz N a' b'
      = Matrix.symmTridiagonalToeplitz N (c * a - d * a') (c * b - d * b') := by
  ext i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.symmTridiagonalToeplitz_apply']
  split_ifs <;> ring

/-- For a real square matrix $T$ of order $N$, the number $0$ is an eigenvalue of $T$ if and only if
$T\xi = 0$ for some $\xi \neq 0$. -/
theorem hasEigenvalue_zero_iff {N : ℕ} (T : Matrix (Fin N) (Fin N) ℝ) :
    Module.End.HasEigenvalue (Matrix.toEuclideanLin T) 0
      ↔ ∃ ξ : Fin N → ℝ, ξ ≠ 0 ∧ T *ᵥ ξ = 0 := by
  constructor
  · intro hT
    obtain ⟨v, hv, hv0⟩ := hT.exists_hasEigenvector
    rw [Module.End.mem_eigenspace_iff, zero_smul] at hv
    refine ⟨WithLp.ofLp v, fun hc ↦ hv0 ?_, ?_⟩
    · exact (WithLp.ofLp_eq_zero (p := 2)).1 hc
    · have := congrArg (WithLp.ofLp (p := 2)) hv
      rwa [Matrix.toEuclideanLin_apply, WithLp.ofLp_toLp, WithLp.ofLp_zero] at this
  · rintro ⟨ξ, hξ, hT⟩
    refine Module.End.hasEigenvalue_of_hasEigenvector
      (x := WithLp.toLp 2 ξ) ⟨?_, fun hc ↦ hξ ?_⟩
    · rw [Module.End.mem_eigenspace_iff, zero_smul, Matrix.toEuclideanLin_toLp, hT]
      rfl
    · exact (WithLp.toLp_eq_zero (p := 2)).1 hc

/-- **Section 13.3.1** of [quarteroni2000numerical], the eigenvalues of the pencil $(A_{fe}, M)$.
Let $n \ge 1$, $h = 1/n$ and $\nu \in \mathbb{R}$. A real number $\lambda$ satisfies
$A_{fe} \xi = \lambda M \xi$ for some $\xi \neq 0$ if and only if
$$\lambda = \frac{6\nu}{h^2} \frac{1 - \cos\theta_i}{2 + \cos\theta_i}, \qquad \theta_i = i \pi
  h,$$
for some $i \in \{1, \ldots, n - 1\}$.

Both matrices are symmetric tridiagonal Toeplitz matrices, so $A_{fe} - \lambda M$ is one too,
and it is singular exactly when one of its cosine eigenvalues vanishes. In Lean the index
`k : Fin (n - 1)` stands for $i = k + 1$. -/
theorem pencil_hasEigenvalue_iff {n : ℕ} (hn : 1 ≤ n) (ν : ℝ) (lam : ℝ) :
    (∃ ξ : Fin (n - 1) → ℝ, ξ ≠ 0 ∧
        heatStiffnessMatrix ν n *ᵥ ξ = lam • (massMatrix n *ᵥ ξ))
      ↔ ∃ k : Fin (n - 1), lam = 6 * ν * (n : ℝ) ^ 2
        * (1 - Real.cos (((k : ℕ) + 1 : ℝ) * π / (n : ℝ)))
        / (2 + Real.cos (((k : ℕ) + 1 : ℝ) * π / (n : ℝ))) := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hcast : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
    rw [Nat.cast_sub hn, Nat.cast_one]; ring
  set A := -(ν * (n : ℝ)) - lam * (1 / (6 * (n : ℝ))) with hA
  set B := 2 * (ν * (n : ℝ)) - 4 * (lam * (1 / (6 * (n : ℝ)))) with hB
  have hdiff : heatStiffnessMatrix ν n - lam • massMatrix n
      = Matrix.symmTridiagonalToeplitz (n - 1) A B := by
    rw [heatStiffnessMatrix, massMatrix, smul_smul,
      smul_sub_smul_symmTridiagonalToeplitz (n - 1) (ν * (n : ℝ)) (lam * (1 / (6 * (n : ℝ))))
        (-1) 2 1 4]
    congr 1 <;> [rw [hA]; rw [hB]] <;> ring
  have hiff : (∃ ξ : Fin (n - 1) → ℝ, ξ ≠ 0 ∧
      heatStiffnessMatrix ν n *ᵥ ξ = lam • (massMatrix n *ᵥ ξ))
      ↔ ∃ ξ : Fin (n - 1) → ℝ, ξ ≠ 0 ∧
        Matrix.symmTridiagonalToeplitz (n - 1) A B *ᵥ ξ = 0 := by
    refine exists_congr fun ξ ↦ and_congr_right fun _ ↦ ?_
    have hsm : (lam • massMatrix n) *ᵥ ξ = lam • (massMatrix n *ᵥ ξ) := by
      ext i
      simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
    rw [← hdiff, Matrix.sub_mulVec, hsm, sub_eq_zero]
  rw [hiff, ← hasEigenvalue_zero_iff,
    Matrix.symmTridiagonalToeplitz_hasEigenvalue_iff A B 0]
  simp only [hcast]
  refine exists_congr fun k ↦ ?_
  set c := Real.cos (((k : ℕ) + 1 : ℝ) * π / (n : ℝ)) with hc
  have hcpos : 0 < 2 + c := by
    have := Real.neg_one_le_cos (((k : ℕ) + 1 : ℝ) * π / (n : ℝ))
    rw [← hc] at this
    linarith
  constructor
  · intro heq
    rw [hB, hA] at heq
    field_simp at heq ⊢
    nlinarith [heq]
  · intro heq
    rw [hB, hA, heq]
    field_simp
    ring

/-- **Section 13.3.1** of [quarteroni2000numerical], the inverse estimate. Let $n \ge 2$, $h = 1/n$
and $\nu > 0$. Then every eigenvalue $\lambda$ of the pencil, $A_{fe} \xi = \lambda M \xi$ with
$\xi \neq 0$, satisfies $\lambda \le 12\nu h^{-2}$, and some eigenvalue satisfies
$\lambda \ge 3\nu h^{-2}$. So the largest eigenvalue satisfies
$$3\nu h^{-2} \le \lambda_h^{N_h} \le 12\nu h^{-2}.$$

**Reading.** The source prints $\lambda_h^{N_h} = c_2 h^{-2}$ for the upper bound, quoted from
its reference QV94, Section 6.3.2. It is read as the inequality
$\lambda_h^{N_h} \le c_2 h^{-2}$. -/
theorem pencil_maxEigenvalue_bounds {n : ℕ} (hn : 2 ≤ n) {ν : ℝ} (hν : 0 < ν) :
    (∀ lam : ℝ, (∃ ξ : Fin (n - 1) → ℝ, ξ ≠ 0 ∧
        heatStiffnessMatrix ν n *ᵥ ξ = lam • (massMatrix n *ᵥ ξ)) →
      lam ≤ 12 * ν * (n : ℝ) ^ 2) ∧
    ∃ lam : ℝ, (∃ ξ : Fin (n - 1) → ℝ, ξ ≠ 0 ∧
        heatStiffnessMatrix ν n *ᵥ ξ = lam • (massMatrix n *ᵥ ξ)) ∧
      3 * ν * (n : ℝ) ^ 2 ≤ lam := by
  have hn1 : 1 ≤ n := by omega
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  constructor
  · intro lam hlam
    obtain ⟨k, rfl⟩ := (pencil_hasEigenvalue_iff hn1 ν lam).1 hlam
    set θ := ((k : ℕ) + 1 : ℝ) * π / (n : ℝ) with hθ
    have hcpos : 0 < 2 + Real.cos θ := by
      have := Real.neg_one_le_cos θ
      linarith
    rw [div_le_iff₀ hcpos]
    have h1 := Real.neg_one_le_cos θ
    nlinarith [mul_nonneg (mul_nonneg hν.le (sq_nonneg ((n : ℝ))))
      (by linarith : (0 : ℝ) ≤ 1 + Real.cos θ)]
  · have hk : (n - 2 : ℕ) < n - 1 := by omega
    refine ⟨_, (pencil_hasEigenvalue_iff hn1 ν _).2 ⟨⟨n - 2, hk⟩, rfl⟩, ?_⟩
    have hval : (((⟨n - 2, hk⟩ : Fin (n - 1)) : ℕ) + 1 : ℝ) * π / (n : ℝ)
        = π - π / (n : ℝ) := by
      rw [Fin.val_mk]
      have : ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := by
        rw [Nat.cast_sub (by omega)]; norm_num
      rw [this]
      field_simp
      ring
    rw [hval, Real.cos_pi_sub]
    set c := Real.cos (π / (n : ℝ)) with hc
    have hcnn : 0 ≤ c := by
      rw [hc]
      have hpi := Real.pi_pos
      have hpos : (0 : ℝ) < π / (n : ℝ) := by positivity
      refine Real.cos_nonneg_of_mem_Icc ⟨by linarith, ?_⟩
      rw [div_le_div_iff₀ hn' (by norm_num)]
      have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      nlinarith [Real.pi_pos]
    have hc1 : c ≤ 1 := Real.cos_le_one _
    have hden : 0 < 2 + -c := by linarith
    rw [le_div_iff₀ hden]
    nlinarith [mul_nonneg (mul_nonneg hν.le (sq_nonneg ((n : ℝ)))) hcnn,
      mul_nonneg (mul_nonneg hν.le (sq_nonneg ((n : ℝ)))) (by linarith : (0 : ℝ) ≤ 1 - c)]

end Pencil

/-! ### The $\theta$-method for the Galerkin problem (13.17)–(13.21) -/

section ThetaMethod

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- **Equation (13.17)** of [quarteroni2000numerical], the $\theta$-method for the Galerkin problem.
Let $a$ be a bilinear form on $V$, $\theta, \Delta t \in \mathbb{R}$, and
$F^k, F^{k+1} \in V^*$. Two iterates $u^k, u^{k+1} \in V$ satisfy the $\theta$-method if for
every $v \in V$
$$\Bigl(\frac{u^{k+1} - u^k}{\Delta t}, v\Bigr) + a\bigl(\theta u^{k+1} + (1 - \theta) u^k,
  v\bigr) = \theta F^{k+1}(v) + (1 - \theta) F^k(v).$$

The method is a relation between consecutive iterates, so the implicit cases need no inverse.
The definition is `Variational.IsThetaStep`. -/
def equation_13_17 (a : SesqForm ℝ V) (θ Δt : ℝ) (F₀ F₁ : V →L[ℝ] ℝ) (u u' : V) : Prop :=
  Variational.IsThetaStep a θ Δt F₀ F₁ u u'

/-- **Equations (13.17) and (13.16)** of [quarteroni2000numerical], equivalence. Let $V$ be
finite-dimensional with a basis $(\varphi_i)$, let $a$ be positive ($a(v, v) \ge 0$),
$\theta \ge 0$ and $\Delta t > 0$. Then $u^k, u^{k+1}$ satisfy (13.17) if and only if the
coordinate vector of $u^{k+1}$ is the matrix $\theta$-step `FiniteDifference.thetaStep` of the
coordinate vector of $u^k$, with the mass matrix $M_{ij} = (\varphi_j, \varphi_i)$, the
stiffness matrix $a(\varphi_j, \varphi_i)$ and the load vectors $F^k(\varphi_i)$ and
$F^{k+1}(\varphi_i)$. -/
theorem equation_13_17_iff_thetaStep [FiniteDimensional ℝ V] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (φ : Module.Basis ι ℝ V) (a : SesqForm ℝ V) {θ Δt : ℝ} (hθ : 0 ≤ θ)
    (hΔt : 0 < Δt) (hpos : a.IsCoerciveWith 0) (F₀ F₁ : V →L[ℝ] ℝ) (u u' : V) :
    equation_13_17 a θ Δt F₀ F₁ u u' ↔
      φ.equivFun u' = FiniteDifference.thetaStep (SesqForm.gramMatrix (innerSL ℝ) φ)
        (a.gramMatrix φ) θ Δt (fun i => F₀ (φ i)) (fun i => F₁ (φ i)) (φ.equivFun u) :=
  Variational.IsThetaStep.iff_thetaStep φ a hθ hΔt hpos F₀ F₁ u u'

/-- **Exercise 3 of Chapter 13** of [quarteroni2000numerical], the inequality of its hint. For all
$u, v$ in a real inner product space,
$$(u - v, u) \ge \frac{1}{2} \bigl(\|u\|^2 - \|v\|^2\bigr).$$
This inequality turns the backward Euler step, tested with $u^{k+1}$, into (13.19). -/
theorem exercise_13_3 (u v : V) : (1 / 2 : ℝ) * (‖u‖ ^ 2 - ‖v‖ ^ 2) ≤ ⟪u - v, u⟫ :=
  Variational.half_norm_sq_sub_le_inner_sub u v

/-- **Equation (13.19)** of [quarteroni2000numerical]. Let $\Delta t > 0$, and let $u^{k+1}$ be one
backward Euler step ($\theta = 1$) of (13.17) from $u^k$ without sources. Then
$$\|u^{k+1}\|^2 + 2 \Delta t\, a(u^{k+1}, u^{k+1}) \le \|u^k\|^2.$$

For the heat form the middle term is $2\nu \Delta t \|\partial_x u^{k+1}\|^2_{L^2}$ by (13.18). -/
theorem equation_13_19 {a : SesqForm ℝ V} {Δt : ℝ} {u u' : V}
    (h : equation_13_17 a 1 Δt 0 0 u u') (hΔt : 0 < Δt) :
    ‖u'‖ ^ 2 + 2 * Δt * a u' u' ≤ ‖u‖ ^ 2 :=
  h.norm_sq_add_two_mul_le hΔt

/-- **Equation (13.20)** of [quarteroni2000numerical]. Let $\Delta t > 0$, $n \in \mathbb{N}$, and
let $u^0, \ldots, u^n$ be backward Euler iterates of (13.17) without sources. Then
$$\|u^n\|^2 + 2 \Delta t \sum_{k=0}^{n-1} a(u^{k+1}, u^{k+1}) \le \|u^0\|^2.$$
So the scheme is unconditionally stable. The estimate follows from (13.19) by telescoping. -/
theorem equation_13_20 {a : SesqForm ℝ V} {Δt : ℝ} {u : ℕ → V} {n : ℕ} (hΔt : 0 < Δt)
    (h : ∀ k < n, equation_13_17 a 1 Δt 0 0 (u k) (u (k + 1))) :
    ‖u n‖ ^ 2 + 2 * Δt * ∑ k ∈ Finset.range n, a (u (k + 1)) (u (k + 1)) ≤ ‖u 0‖ ^ 2 :=
  Variational.IsThetaStep.norm_sq_add_sum_le hΔt h

/-- **Equation (13.21)** of [quarteroni2000numerical]. Let $\Delta t > 0$, let $a$ satisfy
$a(v, v) \ge \alpha \|v\|^2$ for all $v$ with $\alpha > 0$, let $n \in \mathbb{N}$, and let
$u^0, \ldots, u^n$ be backward Euler iterates of (13.17) with the sources $F^0, \ldots, F^n$.
Then
$$\|u^n\|^2 + \Delta t \sum_{k=0}^{n-1} a(u^{k+1}, u^{k+1}) \le \|u^0\|^2 + \frac{1}{\alpha}
  \sum_{k=0}^{n-1} \Delta t \|F^{k+1}\|^2.$$
So the estimate of the source holds with $C = \max\{1, \alpha^{-1}\}$, which does not depend on
$h$ and $\Delta t$.

The source has the factor $2$ on the terms of the form; here the factor is $1$, because the
source term is absorbed by half of the coercive term. Since the constant $C$ of the source is
not specified, this changes only $C$. -/
theorem equation_13_21 {a : SesqForm ℝ V} {Δt : ℝ} {u : ℕ → V} {F : ℕ → V →L[ℝ] ℝ} {n : ℕ}
    (hΔt : 0 < Δt) {α : ℝ} (hα : 0 < α) (hcoer : a.IsCoerciveWith α)
    (h : ∀ k < n, equation_13_17 a 1 Δt (F k) (F (k + 1)) (u k) (u (k + 1))) :
    ‖u n‖ ^ 2 + Δt * ∑ k ∈ Finset.range n, a (u (k + 1)) (u (k + 1))
      ≤ ‖u 0‖ ^ 2 + α⁻¹ * ∑ k ∈ Finset.range n, Δt * ‖F (k + 1)‖ ^ 2 :=
  Variational.IsThetaStep.norm_sq_add_sum_le_of_coercive hΔt hα hcoer h

/-- **Remark 13.1** of [quarteroni2000numerical]. Let $\Delta t > 0$, let $\alpha \in \mathbb{R}$
with $a(v, v) \ge \alpha \|v\|^2$ for all $v$, let $n \in \mathbb{N}$, and let
$u^0, \ldots, u^n$ be backward Euler iterates of (13.17) without sources. Then
$$\|u^n\|^2 + 2 \alpha \Delta t \sum_{k=0}^{n-1} \|u^{k+1}\|^2 \le \|u^0\|^2.$$
So (13.20) holds for every form that is coercive in the $L^2$ norm, with
$\nu \|\partial_x u^{k+1}\|^2$ replaced by $\alpha \|u^{k+1}\|^2$. The continuity of the form is
not needed. -/
theorem remark_13_1 {a : SesqForm ℝ V} {Δt : ℝ} {u : ℕ → V} {n : ℕ} (hΔt : 0 < Δt) {α : ℝ}
    (hcoer : a.IsCoerciveWith α)
    (h : ∀ k < n, equation_13_17 a 1 Δt 0 0 (u k) (u (k + 1))) :
    ‖u n‖ ^ 2 + 2 * α * Δt * ∑ k ∈ Finset.range n, ‖u (k + 1)‖ ^ 2 ≤ ‖u 0‖ ^ 2 := by
  have hmain := equation_13_20 hΔt h
  have hsum : ∑ k ∈ Finset.range n, α * ‖u (k + 1)‖ ^ 2
      ≤ ∑ k ∈ Finset.range n, a (u (k + 1)) (u (k + 1)) :=
    Finset.sum_le_sum fun k _ => hcoer (u (k + 1))
  rw [← Finset.mul_sum] at hsum
  nlinarith [mul_le_mul_of_nonneg_left hsum (by positivity : (0 : ℝ) ≤ 2 * Δt)]

/-- **Exercise 4 of Chapter 13** of [quarteroni2000numerical]. Let $\Delta t > 0$, let $a$ satisfy
$a(v, v) \ge \alpha \|v\|^2$ for all $v$ with $\alpha > 0$, let $n \in \mathbb{N}$, and let
$u^0, \ldots, u^n$ be backward Euler iterates of (13.17) with the sources $F^0, \ldots, F^n$.
Then
$$\|u^n\|^2 + \alpha \Delta t \sum_{k=0}^{n-1} \|u^{k+1}\|^2 \le \|u^0\|^2 + \frac{1}{\alpha}
  \sum_{k=0}^{n-1} \Delta t \|F^{k+1}\|^2.$$
This is (13.21) for a form that is coercive in the $L^2$ norm, with
$\nu \|\partial_x u^{k+1}\|^2$ replaced by $\alpha \|u^{k+1}\|^2$. Only the coercivity is used;
the continuity (12.54) of the form is not needed. -/
theorem exercise_13_4 {a : SesqForm ℝ V} {Δt : ℝ} {u : ℕ → V} {F : ℕ → V →L[ℝ] ℝ} {n : ℕ}
    (hΔt : 0 < Δt) {α : ℝ} (hα : 0 < α) (hcoer : a.IsCoerciveWith α)
    (h : ∀ k < n, equation_13_17 a 1 Δt (F k) (F (k + 1)) (u k) (u (k + 1))) :
    ‖u n‖ ^ 2 + α * Δt * ∑ k ∈ Finset.range n, ‖u (k + 1)‖ ^ 2
      ≤ ‖u 0‖ ^ 2 + α⁻¹ * ∑ k ∈ Finset.range n, Δt * ‖F (k + 1)‖ ^ 2 := by
  have hmain := equation_13_21 hΔt hα hcoer h
  have hsum : ∑ k ∈ Finset.range n, α * ‖u (k + 1)‖ ^ 2
      ≤ ∑ k ∈ Finset.range n, a (u (k + 1)) (u (k + 1)) :=
    Finset.sum_le_sum fun k _ => hcoer (u (k + 1))
  rw [← Finset.mul_sum] at hsum
  nlinarith [mul_le_mul_of_nonneg_left hsum hΔt.le]

end ThetaMethod

/-! ### Eigenpairs of a form and the stability of the $\theta$-method (Definition 13.1, (13.22)) -/

section Eigen

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- **Definition 13.1** of [quarteroni2000numerical]. Let $a$ be a bilinear form on $V$. A number
$\lambda \in \mathbb{R}$ is an **eigenvalue** of $a$ with the **eigenvector** $w \in V$ if
$w \neq 0$ and
$$a(w, v) = \lambda (w, v) \quad \text{for every } v \in V,$$
where $(\cdot, \cdot)$ is the inner product of $V$ (the $L^2(0, 1)$ inner product in the
source).

The definition is `Variational.IsFormEigenpair`. The sentence of the source after the
definition, that a symmetric coercive form on $V = H^1_0$ has an unbounded sequence of positive
eigenvalues whose eigenfunctions form a basis of $V$, is the spectral theorem for an operator
with compact resolvent and is not formalized. Only the finite-dimensional case (13.22) is used. -/
def definition_13_1 (a : SesqForm ℝ V) (lam : ℝ) (w : V) : Prop :=
  Variational.IsFormEigenpair a lam w

/-- **Equation (13.22)** of [quarteroni2000numerical], the algebraic form of the discrete
eigenproblem. Let $(\varphi_j)$ be a basis of $V$, $a$ a bilinear form on $V$,
$\lambda \in \mathbb{R}$ and $\xi$ a coordinate vector. Then $(\lambda, \sum_j \xi_j \varphi_j)$
is an eigenpair of $a$ if and only if $\xi \neq 0$ and
$$A_{fe} \xi = \lambda M \xi,$$
a generalized eigenvalue problem for the pencil $(A_{fe}, M)$ with
$(A_{fe})_{ij} = a(\varphi_j, \varphi_i)$ and $M_{ij} = (\varphi_j, \varphi_i)$. -/
theorem equation_13_22 {ι : Type*} [Fintype ι] (a : SesqForm ℝ V) (φ : Module.Basis ι ℝ V)
    (lam : ℝ) (ξ : ι → ℝ) :
    definition_13_1 a lam (∑ j, ξ j • φ j) ↔
      ξ ≠ 0 ∧ a.gramMatrix φ *ᵥ ξ = lam • SesqForm.gramMatrix (innerSL ℝ) φ *ᵥ ξ :=
  Variational.isFormEigenpair_iff_gramMatrix_mulVec a φ lam ξ

/-- **Section 13.3.1** of [quarteroni2000numerical], positivity of the eigenvalues. Let $c > 0$ with
$a(v, v) \ge c \|v\|^2$ for all $v$. Then every eigenvalue $\lambda$ of $a$ satisfies
$\lambda > 0$. -/
theorem equation_13_22_pos {a : SesqForm ℝ V} {c : ℝ} (hc : 0 < c) (hcoer : a.IsCoerciveWith c)
    {lam : ℝ} {w : V} (h : definition_13_1 a lam w) : 0 < lam :=
  Variational.IsFormEigenpair.pos_of_coercive hc hcoer h

/-- **Section 13.3.1** of [quarteroni2000numerical], the eigenvectors form an orthonormal basis. Let
$V$ be finite-dimensional and $a$ symmetric. Then there are numbers
$\lambda_1, \ldots, \lambda_{N_h}$, with $N_h = \dim V$, and an orthonormal basis
$w_1, \ldots, w_{N_h}$ of $V$ such that each $(\lambda_i, w_i)$ is an eigenpair of $a$. -/
theorem equation_13_22_basis [FiniteDimensional ℝ V] {a : SesqForm ℝ V} (ha : a.IsHermitian) :
    ∃ (lam : Fin (Module.finrank ℝ V) → ℝ)
      (b : OrthonormalBasis (Fin (Module.finrank ℝ V)) ℝ V), ∀ i, definition_13_1 a (lam i) (b i) :=
  Variational.exists_orthonormalBasis_isFormEigenpair ha

/-- **Section 13.3.1** of [quarteroni2000numerical], the $\theta$-method in the eigenbasis. Let $a$
be symmetric, let $(\lambda, w)$ be an eigenpair of $a$, and let $\Delta t \neq 0$ and
$1 + \theta \lambda \Delta t \neq 0$. If $u^{k+1}$ is a $\theta$-step (13.17) of $u^k$ without
sources, then
$$(u^{k+1}, w) = \frac{1 - (1 - \theta) \lambda \Delta t}{1 + \theta \lambda \Delta t} (u^k,
  w).$$
This is the recursion $u_i^{k+1} = u_i^k [1 - (1 - \theta) \lambda_h^i \Delta t]/[1 + \theta
\lambda_h^i \Delta t]$ of the source. -/
theorem thetaMethod_eigen_recursion {a : SesqForm ℝ V} {θ Δt : ℝ} {u u' : V}
    (h : equation_13_17 a θ Δt 0 0 u u') (ha : a.IsHermitian) {lam : ℝ} {w : V}
    (hw : definition_13_1 a lam w) (hΔt : Δt ≠ 0) (hden : 1 + θ * lam * Δt ≠ 0) :
    ⟪u', w⟫ = (1 - (1 - θ) * lam * Δt) / (1 + θ * lam * Δt) * ⟪u, w⟫ :=
  h.inner_eq_of_isFormEigenpair ha hw hΔt hden

/-- **Section 13.3.1** of [quarteroni2000numerical], unconditional stability for $\theta \ge 1/2$.
Let $a$ be positive ($a(v, v) \ge 0$ for all $v$), $\theta \ge 1/2$ and $\Delta t > 0$. If
$u^{k+1}$ is a $\theta$-step (13.17) of $u^k$ without sources, then
$$\|u^{k+1}\| \le \|u^k\|.$$

**Generalization.** The proof of the source uses the eigenbasis, so it assumes that $a$ is
symmetric. The statement holds without symmetry. -/
theorem thetaMethod_stable_of_half_le {a : SesqForm ℝ V} {θ Δt : ℝ} {u u' : V}
    (h : equation_13_17 a θ Δt 0 0 u u') (hθ : 1 / 2 ≤ θ) (hΔt : 0 < Δt)
    (hpos : a.IsCoerciveWith 0) : ‖u'‖ ≤ ‖u‖ :=
  h.norm_le_of_half_le hθ hΔt hpos

/-- **Section 13.3.1** of [quarteroni2000numerical], conditional stability for $0 \le \theta < 1/2$.
Let $V$ be complete, let $a$ be symmetric with $a(v, v) \ge c \|v\|^2$ for some $c > 0$, let
$0 \le \theta < 1/2$ and $\Delta t > 0$. Let $\lambda_{\max}$ be an eigenvalue of $a$ with
$a(v, v) \le \lambda_{\max} \|v\|^2$ for all $v$. Then the $\theta$-step (13.17) without sources
satisfies $\|u^{k+1}\| \le \|u^k\|$ for all $u^k$ and $u^{k+1}$ if and only if
$$\Delta t \le \frac{2}{(1 - 2\theta) \lambda_{\max}}.$$

The source derives strict inequalities and concludes with $\le$. The non-strict condition is the
exact condition for $\|u^{k+1}\| \le \|u^k\|$. -/
theorem thetaMethod_stable_iff_of_lt_half [CompleteSpace V] {a : SesqForm ℝ V}
    (ha : a.IsHermitian) {c : ℝ} (hc : 0 < c) (hcoer : a.IsCoerciveWith c) {θ Δt : ℝ}
    (hθ0 : 0 ≤ θ) (hθ : θ < 1 / 2) (hΔt : 0 < Δt) {lmax : ℝ} {w₀ : V}
    (hw₀ : definition_13_1 a lmax w₀) (hle : ∀ v, a v v ≤ lmax * ‖v‖ ^ 2) :
    (∀ u u' : V, equation_13_17 a θ Δt 0 0 u u' → ‖u'‖ ≤ ‖u‖) ↔
      Δt ≤ 2 / ((1 - 2 * θ) * lmax) := by
  have hlmax : 0 < lmax := Variational.IsFormEigenpair.pos_of_coercive hc hcoer hw₀
  have hpos : 0 < (1 - 2 * θ) * lmax := by nlinarith
  change (∀ u u' : V, Variational.IsThetaStep a θ Δt 0 0 u u' → ‖u'‖ ≤ ‖u‖) ↔
    Δt ≤ 2 / ((1 - 2 * θ) * lmax)
  rw [Variational.IsThetaStep.forall_norm_le_iff_of_lt_half ha hc hcoer hθ0 hΔt hw₀ hle,
    le_div_iff₀ hpos, mul_comm Δt ((1 - 2 * θ) * lmax)]

/-- **Equation (13.23)** of [quarteroni2000numerical]. Let $V$ be complete, let $a$ be symmetric
with $a(v, v) \ge c \|v\|^2$ for some $c > 0$, and let $\lambda_{\max}$ be an eigenvalue of $a$
with $a(v, v) \le \lambda_{\max} \|v\|^2$ for all $v$. Let $\nu > 0$, $n \ge 1$ and $h = 1/n$
with $\lambda_{\max} \le 12\nu h^{-2}$, let $0 \le \theta < 1/2$, and let
$0 < \Delta t \le C_1(\theta) h^2$ with
$$C_1(\theta) = \frac{1}{6\nu(1 - 2\theta)}.$$
Then the $\theta$-step (13.17) without sources satisfies $\|u^{k+1}\| \le \|u^k\|$ for all $u^k$
and $u^{k+1}$.

For piecewise linear elements on the uniform mesh, the bound $\lambda_{\max} \le 12\nu h^{-2}$
is `QuarteroniSaccoSaleri.Chapter13.pencil_maxEigenvalue_bounds`. The proof uses the exact
condition of `QuarteroniSaccoSaleri.Chapter13.thetaMethod_stable_iff_of_lt_half`. -/
theorem equation_13_23 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] {a : SesqForm ℝ V} (ha : a.IsHermitian) {c : ℝ} (hc : 0 < c)
    (hcoer : a.IsCoerciveWith c) {θ Δt : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ < 1 / 2) (hΔt : 0 < Δt)
    {lmax : ℝ} {w₀ : V} (hw₀ : definition_13_1 a lmax w₀) (hle : ∀ v, a v v ≤ lmax * ‖v‖ ^ 2)
    {ν : ℝ} (hν : 0 < ν) {n : ℕ} (hn : 1 ≤ n) (hlmax : lmax ≤ 12 * ν * (n : ℝ) ^ 2)
    (hstep : Δt ≤ 1 / (6 * ν * (1 - 2 * θ)) * (1 / (n : ℝ)) ^ 2) :
    ∀ u u' : V, equation_13_17 a θ Δt 0 0 u u' → ‖u'‖ ≤ ‖u‖ := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hlmaxpos : 0 < lmax := equation_13_22_pos hc hcoer hw₀
  have hθ' : 0 < 1 - 2 * θ := by linarith
  refine (thetaMethod_stable_iff_of_lt_half ha hc hcoer hθ0 hθ hΔt hw₀ hle).2 ?_
  have hpos : 0 < (1 - 2 * θ) * lmax := by positivity
  rw [le_div_iff₀ hpos]
  have hbound : (1 - 2 * θ) * lmax ≤ (1 - 2 * θ) * (12 * ν * (n : ℝ) ^ 2) := by
    exact mul_le_mul_of_nonneg_left hlmax hθ'.le
  have hstep' : Δt * ((1 - 2 * θ) * (12 * ν * (n : ℝ) ^ 2)) ≤ 2 := by
    calc Δt * ((1 - 2 * θ) * (12 * ν * (n : ℝ) ^ 2))
        ≤ (1 / (6 * ν * (1 - 2 * θ)) * (1 / (n : ℝ)) ^ 2)
          * ((1 - 2 * θ) * (12 * ν * (n : ℝ) ^ 2)) := by
          refine mul_le_mul_of_nonneg_right hstep (by positivity)
      _ = 2 := by field_simp; ring
  nlinarith [mul_le_mul_of_nonneg_left hbound hΔt.le]


/-- **Section 13.3.1** of [quarteroni2000numerical], the Rayleigh quotient is at most the largest
eigenvalue. Let $V$ be finite-dimensional, $a$ symmetric and $v \neq 0$. Then some eigenpair
$(\lambda, w)$ of $a$ satisfies
$$a(v, v) \le \lambda \|v\|^2.$$

In the orthonormal eigenbasis, $a(v, v) = \sum_i \lambda_i (w_i, v)^2 \le \max_i \lambda_i
\|v\|^2$. -/
theorem exists_definition_13_1_mul_norm_sq_le [FiniteDimensional ℝ V] {a : SesqForm ℝ V}
    (ha : a.IsHermitian) {v : V} (hv : v ≠ 0) :
    ∃ (lam : ℝ) (w : V), definition_13_1 a lam w ∧ a v v ≤ lam * ‖v‖ ^ 2 := by
  obtain ⟨lam, b, hb⟩ := equation_13_22_basis ha
  have hpos : 0 < Module.finrank ℝ V := Module.finrank_pos_iff_exists_ne_zero.2 ⟨v, hv⟩
  have : Nonempty (Fin (Module.finrank ℝ V)) := ⟨⟨0, hpos⟩⟩
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image Finset.univ lam Finset.univ_nonempty
  refine ⟨lam i₀, b i₀, hb i₀, ?_⟩
  have hexp : v = ∑ i, ⟪b i, v⟫ • b i := (b.sum_repr' v).symm
  have hv' : ∀ i, a (b i) v = lam i * ⟪b i, v⟫ := fun i => (hb i).2 v
  have hform : a v v = ∑ i, lam i * ⟪b i, v⟫ ^ 2 := by
    calc a v v = a (∑ i, ⟪b i, v⟫ • b i) v := by rw [← hexp]
      _ = ∑ i, ⟪b i, v⟫ * a (b i) v := by
          rw [map_sum]
          simp only [FunLike.coe_sum, Finset.sum_apply, map_smul, FunLike.coe_smul,
            Pi.smul_apply, smul_eq_mul]
      _ = ∑ i, lam i * ⟪b i, v⟫ ^ 2 := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hv' i]; ring
  have hnorm : ‖v‖ ^ 2 = ∑ i, ⟪b i, v⟫ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← b.sum_inner_mul_inner v v]
    exact Finset.sum_congr rfl fun i _ => by rw [real_inner_comm v (b i), sq]
  rw [hform, hnorm, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_right (hi₀ i (Finset.mem_univ i)) (sq_nonneg _)

end Eigen

section Spectral

open Polynomial

/-! ### The pseudo-spectral Galerkin approximation and (13.24) -/

/-- **Section 13.3.1** of [quarteroni2000numerical], the space $\mathbb{P}_N^0$. It is the space of
the real polynomials of degree at most $N$ that vanish at $-1$ and $1$, the trial space of the
spectral collocation method of Section 12.3, as a submodule of $\mathbb{R}[X]$. -/
def spectralSubmodule (N : ℕ) : Submodule ℝ ℝ[X] where
  carrier := {p | p.natDegree ≤ N ∧ p.eval (-1) = 0 ∧ p.eval 1 = 0}
  add_mem' {p q} hp hq := ⟨(natDegree_add_le p q).trans (max_le hp.1 hq.1),
    by rw [eval_add, hp.2.1, hq.2.1, add_zero], by rw [eval_add, hp.2.2, hq.2.2, add_zero]⟩
  zero_mem' := ⟨by simp, by simp, by simp⟩
  smul_mem' c {p} hp := ⟨(natDegree_smul_le c p).trans hp.1,
    by rw [eval_smul, hp.2.1, smul_zero], by rw [eval_smul, hp.2.2, smul_zero]⟩

/-- A polynomial $p$ lies in $\mathbb{P}_N^0$ if and only if $\deg p \le N$, $p(-1) = 0$ and
$p(1) = 0$. -/
theorem mem_spectralSubmodule_iff {N : ℕ} {p : ℝ[X]} :
    p ∈ spectralSubmodule N ↔ p.natDegree ≤ N ∧ p.eval (-1) = 0 ∧ p.eval 1 = 0 := Iff.rfl

-- the nodes and weights are phantom parameters of the type, there for the inner product instance
set_option linter.unusedVariables false in
/-- **Section 13.3.1** of [quarteroni2000numerical], the pseudo-spectral trial space. Let
$N \in \mathbb{N}$ and let $x, w \in \mathbb{R}^{N+1}$ be nodes and weights. The space is
$V_N = \mathbb{P}_N^0$ with the discrete inner product
$$(u, v)_N = \sum_{j=0}^N u(x_j) v(x_j) w_j$$
of (12.37) in place of the $L^2$ inner product.

The nodes and weights are parameters of the type, so that the inner product can be an instance.
It is definite when they are the Legendre–Gauss–Lobatto nodes and weights, so the inner product
space instance assumes `[Fact (QuarteroniSaccoSaleri.Chapter12.IsLegendreLobatto N x w)]`. -/
def SpectralSpace (N : ℕ) (x w : Fin (N + 1) → ℝ) : Type := spectralSubmodule N

namespace SpectralSpace

variable {N : ℕ} {x w : Fin (N + 1) → ℝ}

instance : AddCommGroup (SpectralSpace N x w) :=
  inferInstanceAs (AddCommGroup (spectralSubmodule N))

instance : Module ℝ (SpectralSpace N x w) := inferInstanceAs (Module ℝ (spectralSubmodule N))

instance : Inhabited (SpectralSpace N x w) := ⟨0⟩

/-- The polynomial in $\mathbb{P}_N^0$ of an element of the trial space $V_N$. -/
def poly (v : SpectralSpace N x w) : ℝ[X] := (v : spectralSubmodule N).1

/-- The polynomial of an element of $V_N$ lies in $\mathbb{P}_N^0$. -/
theorem poly_mem (v : SpectralSpace N x w) : v.poly ∈ spectralSubmodule N :=
  (v : spectralSubmodule N).2

/-- The polynomial of an element of $V_N$ has degree at most $N$. -/
theorem natDegree_poly_le (v : SpectralSpace N x w) : v.poly.natDegree ≤ N := v.poly_mem.1

/-- The polynomial of an element of $V_N$ vanishes at $-1$. -/
theorem eval_neg_one_poly (v : SpectralSpace N x w) : v.poly.eval (-1) = 0 := v.poly_mem.2.1

/-- The polynomial of an element of $V_N$ vanishes at $1$. -/
theorem eval_one_poly (v : SpectralSpace N x w) : v.poly.eval 1 = 0 := v.poly_mem.2.2

/-- Two elements of $V_N$ with the same polynomial are equal. -/
@[ext]
theorem ext {u v : SpectralSpace N x w} (h : u.poly = v.poly) : u = v := Subtype.ext h

/-- The element of the trial space $V_N$ given by a polynomial $p \in \mathbb{P}_N^0$. -/
def mk (x w : Fin (N + 1) → ℝ) (p : ℝ[X]) (hp : p ∈ spectralSubmodule N) : SpectralSpace N x w :=
  (⟨p, hp⟩ : spectralSubmodule N)

/-- The polynomial of the element given by $p \in \mathbb{P}_N^0$ is $p$. -/
@[simp]
theorem poly_mk (p : ℝ[X]) (hp : p ∈ spectralSubmodule N) : (mk x w p hp).poly = p := rfl

/-- The polynomial of a sum is the sum of the polynomials. -/
@[simp]
theorem poly_add (u v : SpectralSpace N x w) : (u + v).poly = u.poly + v.poly := rfl

/-- The polynomial of a scalar multiple is the scalar multiple of the polynomial. -/
@[simp]
theorem poly_smul (c : ℝ) (v : SpectralSpace N x w) : (c • v).poly = c • v.poly := rfl

/-- The polynomial of $0$ is $0$. -/
@[simp]
theorem poly_zero : (0 : SpectralSpace N x w).poly = 0 := rfl

/-- The trial space $V_N$ is finite-dimensional, because it lies in the space of polynomials of
degree less than $N + 1$. -/
instance : FiniteDimensional ℝ (SpectralSpace N x w) := by
  have : FiniteDimensional ℝ (Polynomial.degreeLT ℝ (N + 1)) :=
    (Polynomial.degreeLTEquiv ℝ (N + 1)).symm.finiteDimensional
  exact Submodule.finiteDimensional_of_le (S₁ := spectralSubmodule N)
    (S₂ := Polynomial.degreeLT ℝ (N + 1)) fun p hp => mem_degreeLT.2
      ((degree_le_of_natDegree_le hp.1).trans_lt (WithBot.coe_lt_coe.2 (Nat.lt_succ_self N)))

/-- The Gauss–Lobatto inner product $(u, v)_N$ of (12.37) on the trial space $V_N$. -/
instance : Inner ℝ (SpectralSpace N x w) :=
  ⟨fun u v => Chapter12.equation_12_37 N x w (fun t => u.poly.eval t) fun t => v.poly.eval t⟩

/-- For $u, v \in V_N$, the inner product $(u, v)_N$ is the discrete scalar product (12.37) of their
polynomials. -/
theorem inner_def (u v : SpectralSpace N x w) :
    ⟪u, v⟫ = Chapter12.equation_12_37 N x w (fun t => u.poly.eval t) fun t => v.poly.eval t := rfl

instance [hx : Fact (Chapter12.IsLegendreLobatto N x w)] :
    InnerProductSpace.Core ℝ (SpectralSpace N x w) where
  toInner := inferInstance
  conj_inner_symm u v := by
    simp only [conj_trivial, inner_def, Chapter12.equation_12_37]
    exact Quadrature.discreteInner_comm _ _ _ _
  re_inner_nonneg v := by
    simp only [RCLike.re_to_real, inner_def]
    exact Chapter12.equation_12_37_self_nonneg hx.out _
  add_left u v z := by
    simp only [inner_def, poly_add, eval_add, Chapter12.equation_12_37]
    exact Quadrature.discreteInner_add_left _ _ _ _ _
  smul_left u v c := by
    simp only [inner_def, poly_smul, eval_smul, smul_eq_mul, conj_trivial,
      Chapter12.equation_12_37]
    exact Quadrature.discreteInner_smul_left _ _ _ _ _
  definite v hv := by
    simp only [inner_def, Chapter12.equation_12_37] at hv
    by_contra hne
    have hp0 : v.poly ≠ 0 := fun h => hne (ext (by rw [h, poly_zero]))
    have hdeg : v.poly.degree < N + 1 :=
      (degree_le_of_natDegree_le v.natDegree_poly_le).trans_lt
        (WithBot.coe_lt_coe.2 (Nat.lt_succ_self N))
    exact (Quadrature.discreteInner_self_pos hx.out.weight_pos hx.out.injective hp0
      (by exact_mod_cast hdeg)).ne' hv

instance [Fact (Chapter12.IsLegendreLobatto N x w)] : NormedAddCommGroup (SpectralSpace N x w) :=
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)

instance [Fact (Chapter12.IsLegendreLobatto N x w)] : InnerProductSpace ℝ (SpectralSpace N x w) :=
  InnerProductSpace.ofCore _

/-- For Legendre–Gauss–Lobatto nodes and weights and $v \in V_N$, the squared norm is the discrete
norm $\|v\|_N^2 = (v, v)_N$. -/
theorem norm_sq_eq [Fact (Chapter12.IsLegendreLobatto N x w)] (v : SpectralSpace N x w) :
    ‖v‖ ^ 2 = Chapter12.equation_12_37 N x w (fun t => v.poly.eval t) fun t => v.poly.eval t := by
  rw [← real_inner_self_eq_norm_sq, inner_def]

/-- **Section 13.3.1** of [quarteroni2000numerical], the pseudo-spectral bilinear form. For
$\nu \in \mathbb{R}$, it is the form
$$a_N(u, v) = \nu (u', v')_N$$
on $V_N$, the discrete counterpart of $a(u, v) = \nu \int u' v'$.

On $\mathbb{P}_N^0$ the Gauss–Lobatto rule is exact on $u' v' \in \mathbb{P}_{2N-2}$, so
$a_N = a$ (`QuarteroniSaccoSaleri.Chapter13.SpectralSpace.spectralForm_apply_eq_integral`). -/
def spectralBilin (N : ℕ) (x w : Fin (N + 1) → ℝ) (ν : ℝ) :
    SpectralSpace N x w →ₗ[ℝ] SpectralSpace N x w →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun u v => ν * Chapter12.equation_12_37 N x w
      (fun t => (derivative u.poly).eval t) fun t => (derivative v.poly).eval t)
    (fun u u' v => by
      simp only [poly_add, derivative_add, eval_add, Chapter12.equation_12_37,
        Quadrature.discreteInner, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring)
    (fun c u v => by
      simp only [poly_smul, derivative_smul, eval_smul, smul_eq_mul, Chapter12.equation_12_37,
        Quadrature.discreteInner, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring)
    (fun u v v' => by
      simp only [poly_add, derivative_add, eval_add, Chapter12.equation_12_37,
        Quadrature.discreteInner, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring)
    (fun c u v => by
      simp only [poly_smul, derivative_smul, eval_smul, smul_eq_mul, Chapter12.equation_12_37,
        Quadrature.discreteInner, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring)

/-- For Legendre–Gauss–Lobatto nodes and weights and $\nu \in \mathbb{R}$, the pseudo-spectral form
$a_N(u, v) = \nu (u', v')_N$ as a bounded bilinear form on $V_N$. -/
def spectralForm (N : ℕ) (x w : Fin (N + 1) → ℝ) [Fact (Chapter12.IsLegendreLobatto N x w)]
    (ν : ℝ) : SesqForm ℝ (SpectralSpace N x w) :=
  SesqForm.ofBilin (spectralBilin N x w ν)

/-- For Legendre–Gauss–Lobatto nodes and weights, $\nu \in \mathbb{R}$ and $u, v \in V_N$, the
pseudo-spectral form is $a_N(u, v) = \nu (u', v')_N$. -/
theorem spectralForm_apply [Fact (Chapter12.IsLegendreLobatto N x w)] (ν : ℝ)
    (u v : SpectralSpace N x w) :
    spectralForm N x w ν u v = ν * Chapter12.equation_12_37 N x w
      (fun t => (derivative u.poly).eval t) fun t => (derivative v.poly).eval t := rfl

/-- For Legendre–Gauss–Lobatto nodes and weights, $\nu \in \mathbb{R}$ and $u, v \in V_N$, the
pseudo-spectral form is the exact form:
$$a_N(u, v) = \nu \int_{-1}^1 u' v',$$
because the Gauss–Lobatto rule is exact on $\mathbb{P}_{2N-1}$. -/
theorem spectralForm_apply_eq_integral [hx : Fact (Chapter12.IsLegendreLobatto N x w)] (ν : ℝ)
    (u v : SpectralSpace N x w) :
    spectralForm N x w ν u v =
      ν * ∫ t in (-1 : ℝ)..1, (derivative u.poly).eval t * (derivative v.poly).eval t := by
  rw [spectralForm_apply, Chapter12.equation_12_37_exact hx.out]
  rw [← natDegree_le_iff_degree_le]
  have d1 := natDegree_derivative_le u.poly
  have d2 := natDegree_derivative_le v.poly
  have hu := u.natDegree_poly_le
  have hv := v.natDegree_poly_le
  have hm := natDegree_mul_le (p := derivative u.poly) (q := derivative v.poly)
  omega

/-- For Legendre–Gauss–Lobatto nodes and weights and $\nu \in \mathbb{R}$, the pseudo-spectral form
is symmetric. -/
theorem spectralForm_isHermitian [Fact (Chapter12.IsLegendreLobatto N x w)] (ν : ℝ) :
    (spectralForm N x w ν).IsHermitian := fun u v => by
  simp only [spectralForm_apply, RCLike.conj_to_real, Chapter12.equation_12_37]
  rw [Quadrature.discreteInner_comm]

/-- For Legendre–Gauss–Lobatto nodes and weights, $\nu \in \mathbb{R}$ and $v \in V_N$,
$$a_N(v, v) = \nu \|v'\|^2_{L^2(-1,1)},$$
the discrete counterpart of (13.18). -/
theorem spectralForm_apply_self [Fact (Chapter12.IsLegendreLobatto N x w)] (ν : ℝ)
    (v : SpectralSpace N x w) :
    spectralForm N x w ν v v = ν * ∫ t in (-1 : ℝ)..1, (derivative v.poly).eval t ^ 2 := by
  rw [spectralForm_apply_eq_integral]
  congr 1
  exact intervalIntegral.integral_congr fun t _ => (sq _).symm

/-- For Legendre–Gauss–Lobatto nodes and weights, $N \ge 1$ and $\nu > 0$, the pseudo-spectral form
is coercive in the discrete norm:
$$\frac{\nu}{6} \|v\|_N^2 \le a_N(v, v) \quad \text{for all } v \in V_N.$$

The Poincaré inequality (12.16) on $(-1, 1)$ gives $\int v^2 \le 2 \int (v')^2$ for
$v \in \mathbb{P}_N^0$, and the norm equivalence $\|v\|_N^2 \le 3 \int v^2$ of
`QuarteroniSaccoSaleri.Chapter12.equation_12_37_norm_equiv` converts the discrete norm. -/
theorem spectralForm_coercive [hx : Fact (Chapter12.IsLegendreLobatto N x w)] (hN : 1 ≤ N) {ν : ℝ}
    (hν : 0 < ν) : (spectralForm N x w ν).IsCoerciveWith (ν / 6) := by
  intro v
  rw [RCLike.re_to_real, spectralForm_apply_self, norm_sq_eq]
  have h1 := (Chapter12.equation_12_37_norm_equiv hN hx.out v.natDegree_poly_le).2
  have h2 := Chapter12.poincare_poly v.eval_neg_one_poly
  nlinarith

/-- **Section 13.3.1** of [quarteroni2000numerical], the pseudo-spectral eigenvalues are $O(N^4)$.
Let the nodes and weights be the Legendre–Gauss–Lobatto ones, $N \ge 1$ and $\nu \ge 0$. Then
every eigenvalue $\lambda$ (Definition 13.1) of the form $a_N(u, v) = \nu (u', v')_N$ relative
to $(\cdot, \cdot)_N$ on $\mathbb{P}_N^0$ satisfies
$$\lambda \le \nu N^2 (N + 1)^2.$$
This is the statement of the source that the largest eigenvalue of the spectral stiffness matrix
grows like $O(N^4)$.

For an eigenvector $v$, $\lambda \|v\|_N^2 = a_N(v, v) = \nu \|v'\|^2_{L^2} \le \nu N^2 (N +
1)^2 \|v\|^2_{L^2} \le \nu N^2 (N + 1)^2 \|v\|_N^2$, by the $L^2$ Markov inequality
`Polynomial.integral_derivative_sq_le` and the lower half of the norm equivalence
`QuarteroniSaccoSaleri.Chapter12.equation_12_37_norm_equiv`. The matching lower bound is
`QuarteroniSaccoSaleri.Chapter13.equation_13_24_lower`. -/
theorem spectralForm_eigenvalue_le [hx : Fact (Chapter12.IsLegendreLobatto N x w)] (hN : 1 ≤ N)
    {ν : ℝ} (hν : 0 ≤ ν) {lam : ℝ} {v : SpectralSpace N x w}
    (h : definition_13_1 (spectralForm N x w ν) lam v) :
    lam ≤ ν * ((N : ℝ) * (N + 1)) ^ 2 := by
  refine Variational.IsFormEigenpair.le_of_le (fun u => ?_) h
  rw [spectralForm_apply_self, norm_sq_eq]
  have h1 := (Chapter12.equation_12_37_norm_equiv hN hx.out u.natDegree_poly_le).1
  have h2 := Polynomial.integral_derivative_sq_le u.natDegree_poly_le
  have h3 : (0 : ℝ) ≤ ((N : ℝ) * (N + 1)) ^ 2 := sq_nonneg _
  calc ν * ∫ t in (-1 : ℝ)..1, (derivative u.poly).eval t ^ 2
      ≤ ν * (((N : ℝ) * (N + 1)) ^ 2 * ∫ t in (-1 : ℝ)..1, u.poly.eval t ^ 2) := by gcongr
    _ ≤ ν * (((N : ℝ) * (N + 1)) ^ 2 *
          Chapter12.equation_12_37 N x w (fun t => u.poly.eval t) fun t => u.poly.eval t) := by
        gcongr
    _ = _ := by ring

/-! ### The lower eigenvalue bound: the Lagrange basis polynomial of an interior node -/

/-- For Legendre–Gauss–Lobatto nodes and weights and an interior node $x_j$, $0 < j < N$, the
Lagrange basis polynomial $l_j$ of the nodes as an element of $\mathbb{P}_N^0$. It has degree
$N$ and vanishes at the other nodes, among them $x_0 = -1$ and $x_N = 1$. It is the test
function of the lower eigenvalue bound `QuarteroniSaccoSaleri.Chapter13.equation_13_24_lower`. -/
def lagrangeBasis [hx : Fact (Chapter12.IsLegendreLobatto N x w)] (j : Fin (N + 1)) (hj0 : j ≠ 0)
    (hjN : j ≠ Fin.last N) : SpectralSpace N x w :=
  mk x w (Lagrange.basis Finset.univ x j)
    ⟨by
      rw [Lagrange.natDegree_basis hx.out.injective.injOn (Finset.mem_univ _), Finset.card_univ,
        Fintype.card_fin, Nat.add_sub_cancel],
      by rw [← hx.out.first]; exact Lagrange.eval_basis_of_ne hj0 (Finset.mem_univ _),
      by rw [← hx.out.last]; exact Lagrange.eval_basis_of_ne hjN (Finset.mem_univ _)⟩

/-- The polynomial of `QuarteroniSaccoSaleri.Chapter13.SpectralSpace.lagrangeBasis j` is the
Lagrange basis polynomial $l_j$ of the nodes. -/
@[simp]
theorem poly_lagrangeBasis [Fact (Chapter12.IsLegendreLobatto N x w)] (j : Fin (N + 1))
    (hj0 : j ≠ 0) (hjN : j ≠ Fin.last N) :
    (lagrangeBasis j hj0 hjN : SpectralSpace N x w).poly = Lagrange.basis Finset.univ x j := rfl

/-- For an interior node $x_j$, $l_j \neq 0$, because $l_j(x_j) = 1$. -/
theorem lagrangeBasis_ne_zero [hx : Fact (Chapter12.IsLegendreLobatto N x w)] (j : Fin (N + 1))
    (hj0 : j ≠ 0) (hjN : j ≠ Fin.last N) : (lagrangeBasis j hj0 hjN : SpectralSpace N x w) ≠ 0 := by
  intro h
  have := congrArg (fun v : SpectralSpace N x w => v.poly.eval (x j)) h
  simp only [poly_lagrangeBasis, poly_zero, eval_zero] at this
  rw [Lagrange.eval_basis_self hx.out.injective.injOn (Finset.mem_univ _)] at this
  exact one_ne_zero this

/-- For Legendre–Gauss–Lobatto nodes and weights and an interior node $x_j$, the discrete norm of
the Lagrange basis polynomial is its weight: $\|l_j\|_N^2 = w_j$, because
$l_j(x_i) = \delta_{ij}$. -/
theorem norm_sq_lagrangeBasis [hx : Fact (Chapter12.IsLegendreLobatto N x w)] (j : Fin (N + 1))
    (hj0 : j ≠ 0) (hjN : j ≠ Fin.last N) :
    ‖(lagrangeBasis j hj0 hjN : SpectralSpace N x w)‖ ^ 2 = w j := by
  rw [norm_sq_eq, Chapter12.equation_12_37_eq, poly_lagrangeBasis, Finset.sum_eq_single j]
  · rw [Lagrange.eval_basis_self hx.out.injective.injOn (Finset.mem_univ _)]; ring
  · intro i _ hij
    rw [Lagrange.eval_basis_of_ne (Ne.symm hij) (Finset.mem_univ _)]; ring
  · intro h; exact absurd (Finset.mem_univ j) h

/-- For Legendre–Gauss–Lobatto nodes and weights, $\nu \ge 0$ and an interior node $x_j$,
$$\frac{\nu}{1 - x_j} \le a_N(l_j, l_j).$$
On $[x_j, 1]$ the polynomial $l_j$ drops from $1$ to $0$, so the Cauchy–Schwarz inequality gives
$1 \le (1 - x_j) \int_{x_j}^1 (l_j')^2$, and $a_N(l_j, l_j) = \nu \int_{-1}^1 (l_j')^2$. For the
node nearest to $1$, both $1 - x_j$ and $\|l_j\|_N^2 = w_j$ are at most $C N^{-2}$, which gives
$\lambda_{\max} \ge c N^4$. -/
theorem le_spectralForm_lagrangeBasis_self [hx : Fact (Chapter12.IsLegendreLobatto N x w)] {ν : ℝ}
    (hν : 0 ≤ ν) (j : Fin (N + 1)) (hj0 : j ≠ 0) (hjN : j ≠ Fin.last N) :
    ν / (1 - x j) ≤ spectralForm N x w ν (lagrangeBasis j hj0 hjN) (lagrangeBasis j hj0 hjN) := by
  rw [spectralForm_apply_self, poly_lagrangeBasis]
  set l := Lagrange.basis Finset.univ x j with hl
  have hxj1 : x j < 1 := lt_of_le_of_ne (hx.out.mem j).2
    fun h => hjN (hx.out.injective (h.trans hx.out.last.symm))
  have hxj : -1 ≤ x j := (hx.out.mem j).1
  have hpos : 0 < 1 - x j := by linarith
  have h1 := intervalIntegral.sq_sub_le_mul_integral_sq_of_hasDerivAt hxj1.le
    l.continuous.continuousOn (derivative l).continuous.continuousOn fun t _ => l.hasDerivAt t
  have hl1 : l.eval 1 = 0 := by
    rw [hl, ← hx.out.last]; exact Lagrange.eval_basis_of_ne hjN (Finset.mem_univ _)
  have hlj : l.eval (x j) = 1 := by
    rw [hl]; exact Lagrange.eval_basis_self hx.out.injective.injOn (Finset.mem_univ _)
  rw [hl1, hlj] at h1
  norm_num at h1
  have h2 : ∫ t in x j..1, (derivative l).eval t ^ 2 ≤
      ∫ t in (-1 : ℝ)..1, (derivative l).eval t ^ 2 :=
    intervalIntegral.integral_mono_interval hxj hxj1.le le_rfl
      (Filter.Eventually.of_forall fun t => sq_nonneg _)
      (((derivative l).continuous.pow 2).intervalIntegrable _ _)
  rw [div_le_iff₀ hpos]
  calc ν = ν * 1 := (mul_one ν).symm
    _ ≤ ν * ((1 - x j) * ∫ t in x j..1, (derivative l).eval t ^ 2) :=
        mul_le_mul_of_nonneg_left h1 hν
    _ ≤ ν * ((1 - x j) * ∫ t in (-1 : ℝ)..1, (derivative l).eval t ^ 2) := by gcongr
    _ = (ν * ∫ t in (-1 : ℝ)..1, (derivative l).eval t ^ 2) * (1 - x j) := by ring

end SpectralSpace

/-- **Equation (13.24)** of [quarteroni2000numerical], the stability condition of the
$\theta$-method for the pseudo-spectral Galerkin approximation. Let $N \ge 1$, let the nodes and
weights be the Legendre–Gauss–Lobatto ones, let $\nu > 0$, $\theta < 1/2$, and let
$0 < \Delta t \le C_2(\theta) N^{-4}$ with
$$C_2(\theta) = \frac{1}{2\nu(1 - 2\theta)}.$$
Then on $V_N = \mathbb{P}_N^0$ with the form $a_N(u, v) = \nu (u', v')_N$ the $\theta$-step
(13.17) without sources satisfies $\|u_N^{k+1}\|_N \le \|u_N^k\|_N$ for all $u_N^k$ and
$u_N^{k+1}$.

**Generalization.** The source assumes $0 \le \theta < 1/2$. Sufficiency does not need
$\theta \ge 0$.

Every eigenvalue of the form is at most $\nu N^2 (N + 1)^2 \le 4\nu N^4$
(`QuarteroniSaccoSaleri.Chapter13.SpectralSpace.spectralForm_eigenvalue_le`), and the exact
condition is $\Delta t \le 2/((1 - 2\theta) \lambda_{\max})$
(`QuarteroniSaccoSaleri.Chapter13.thetaMethod_stable_iff_of_lt_half`). The necessity of a
condition $\Delta t \le C N^{-4}$, which the source also states, follows from the lower bound
`QuarteroniSaccoSaleri.Chapter13.equation_13_24_lower`. For $\theta \ge 1/2$ the method is
unconditionally stable by `QuarteroniSaccoSaleri.Chapter13.thetaMethod_stable_of_half_le`. -/
theorem equation_13_24 {N : ℕ} (hN : 1 ≤ N) {x w : Fin (N + 1) → ℝ}
    [hx : Fact (Chapter12.IsLegendreLobatto N x w)] {ν : ℝ} (hν : 0 < ν) {θ Δt : ℝ}
    (hθ : θ < 1 / 2) (hΔt : 0 < Δt)
    (hstep : Δt ≤ 1 / (2 * ν * (1 - 2 * θ)) * ((N : ℝ) ^ 4)⁻¹) :
    ∀ u u' : SpectralSpace N x w,
      equation_13_17 (SpectralSpace.spectralForm N x w ν) θ Δt 0 0 u u' → ‖u'‖ ≤ ‖u‖ := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hθ' : 0 < 1 - 2 * θ := by linarith
  -- the largest eigenvalue
  obtain ⟨lam, b, hb⟩ := equation_13_22_basis (SpectralSpace.spectralForm_isHermitian (x := x)
    (w := w) ν)
  have hcoer := SpectralSpace.spectralForm_coercive (x := x) (w := w) hN hν
  set lmax : ℝ := ν * ((N : ℝ) * (N + 1)) ^ 2 with hlmax
  -- every eigenvalue is at most `lmax`, hence so is the quadratic form
  have hle : ∀ v : SpectralSpace N x w,
      SpectralSpace.spectralForm N x w ν v v ≤ lmax * ‖v‖ ^ 2 := by
    intro v
    have hexp : v = ∑ i, ⟪b i, v⟫ • b i := (b.sum_repr' v).symm
    have hv : ∀ i, SpectralSpace.spectralForm N x w ν (b i) v = lam i * ⟪b i, v⟫ :=
      fun i => (hb i).2 v
    have hsymm := SpectralSpace.spectralForm_isHermitian (x := x) (w := w) ν
    have hform : SpectralSpace.spectralForm N x w ν v v = ∑ i, lam i * ⟪b i, v⟫ ^ 2 := by
      calc SpectralSpace.spectralForm N x w ν v v
          = SpectralSpace.spectralForm N x w ν (∑ i, ⟪b i, v⟫ • b i) v := by rw [← hexp]
        _ = ∑ i, ⟪b i, v⟫ * SpectralSpace.spectralForm N x w ν (b i) v := by
            rw [map_sum]
            simp only [FunLike.coe_sum, Finset.sum_apply, map_smul, FunLike.coe_smul,
              Pi.smul_apply, smul_eq_mul]
        _ = ∑ i, lam i * ⟪b i, v⟫ ^ 2 := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [hv i]; ring
    have hnorm : ‖v‖ ^ 2 = ∑ i, ⟪b i, v⟫ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, ← b.sum_inner_mul_inner v v]
      exact Finset.sum_congr rfl fun i _ => by rw [real_inner_comm v (b i), sq]
    rw [hform, hnorm, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    exact mul_le_mul_of_nonneg_right
      (SpectralSpace.spectralForm_eigenvalue_le hN hν.le (hb i)) (sq_nonneg _)
  have hpos : (SpectralSpace.spectralForm N x w ν).IsCoerciveWith 0 :=
    SesqForm.IsCoerciveWith.mono _ hcoer (by positivity)
  intro u u' h
  refine Variational.IsThetaStep.norm_le_of_le_of_lt_half h
    (SpectralSpace.spectralForm_isHermitian ν) hpos hle hΔt ?_
  -- `(1 - 2θ) lmax Δt ≤ 2`
  have hN4 : ((N : ℝ) * (N + 1)) ^ 2 ≤ 4 * (N : ℝ) ^ 4 := by
    have h1 : (N : ℝ) + 1 ≤ 2 * N := by linarith
    have h2 : (N : ℝ) * (N + 1) ≤ N * (2 * N) := by
      exact mul_le_mul_of_nonneg_left h1 (by positivity)
    calc ((N : ℝ) * (N + 1)) ^ 2 ≤ ((N : ℝ) * (2 * N)) ^ 2 := by gcongr
      _ = 4 * (N : ℝ) ^ 4 := by ring
  have hstep' : Δt * (2 * ν * (1 - 2 * θ)) * (N : ℝ) ^ 4 ≤ 1 := by
    have hpos4 : (0 : ℝ) < (N : ℝ) ^ 4 := by positivity
    have := mul_le_mul_of_nonneg_right hstep (by positivity : (0 : ℝ) ≤ 2 * ν * (1 - 2 * θ) * N ^ 4)
    calc Δt * (2 * ν * (1 - 2 * θ)) * (N : ℝ) ^ 4
        = Δt * (2 * ν * (1 - 2 * θ) * N ^ 4) := by ring
      _ ≤ 1 / (2 * ν * (1 - 2 * θ)) * ((N : ℝ) ^ 4)⁻¹ * (2 * ν * (1 - 2 * θ) * N ^ 4) := this
      _ = 1 := by field_simp
  calc (1 - 2 * θ) * lmax * Δt = (1 - 2 * θ) * ν * Δt * ((N : ℝ) * (N + 1)) ^ 2 := by
        rw [hlmax]; ring
    _ ≤ (1 - 2 * θ) * ν * Δt * (4 * (N : ℝ) ^ 4) := by gcongr
    _ = 2 * (Δt * (2 * ν * (1 - 2 * θ)) * (N : ℝ) ^ 4) := by ring
    _ ≤ 2 := by linarith

/-- **Section 13.3.1** of [quarteroni2000numerical], the lower bound for the pseudo-spectral
eigenvalues behind (13.24). Let $\nu \ge 0$. There is $c > 0$ such that for every $N \ge 2$ and
all Legendre–Gauss–Lobatto nodes and weights, the form $a_N(u, v) = \nu (u', v')_N$ on
$\mathbb{P}_N^0$ with the inner product $(\cdot, \cdot)_N$ has an eigenvalue
$$\lambda \ge c \nu N^4.$$
With `QuarteroniSaccoSaleri.Chapter13.thetaMethod_stable_iff_of_lt_half`, this shows that the
$\theta$-method is stable only if $\Delta t \le C_2(\theta) N^{-4}$ up to a constant, the
reading of (13.24) that the source states. The sufficiency half is
`QuarteroniSaccoSaleri.Chapter13.equation_13_24`. The constant is $c = 1/(5184 \pi^2)$.

The test function is the Lagrange basis polynomial $l_j \in \mathbb{P}_N^0$ of the interior
Gauss–Lobatto node $x_j$ nearest to $1$. The Rayleigh quotient of any vector is at most the
largest eigenvalue (`QuarteroniSaccoSaleri.Chapter13.exists_definition_13_1_mul_norm_sq_le`),
$a_N(l_j, l_j) \ge \nu/(1 - x_j)$
(`QuarteroniSaccoSaleri.Chapter13.SpectralSpace.le_spectralForm_lagrangeBasis_self`) and
$\|l_j\|_N^2 = w_j$. The Sturm comparison for the Legendre equation puts $x_j$ within
$81\pi^2/(32 N^2)$ of $1$ (`Polynomial.exists_eval_derivative_legendre_eq_zero_near_one`), and
the bound on the Christoffel function gives $w_j \le 2048/N^2$
(`Quadrature.legendreLobattoWeight_le_of_near_one`). So $\lambda \ge \nu/((1 - x_j) w_j) \ge \nu
N^4/(5184 \pi^2)$.

The statement needs $N \ge 2$: the space $\mathbb{P}_1^0 = \{0\}$ has no eigenvector, so the
statement is false for $N = 1$. The $O(N^4)$ of the source is asymptotic. -/
theorem equation_13_24_lower {ν : ℝ} (hν : 0 ≤ ν) :
    ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, 2 ≤ N → ∀ (x w : Fin (N + 1) → ℝ)
      [Fact (Chapter12.IsLegendreLobatto N x w)], ∃ (lam : ℝ) (v : SpectralSpace N x w),
        definition_13_1 (SpectralSpace.spectralForm N x w ν) lam v ∧
          c * ν * (N : ℝ) ^ 4 ≤ lam := by
  refine ⟨1 / (5184 * π ^ 2), by positivity, fun N hN x w hx => ?_⟩
  have hN1 : 1 ≤ N := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  -- the interior node nearest to `1`
  obtain ⟨t, ht0, ht1, ht2⟩ := Polynomial.exists_eval_derivative_legendre_eq_zero_near_one hN
  obtain ⟨-, hnodal⟩ := hx.out.isInterpolatoryMeasure_and_nodal_eq hN1
  have hroot : (Lagrange.nodal Finset.univ x).eval t = 0 := by
    rw [hnodal, Quadrature.lobattoNodal, eval_mul]
    have hc : ((N : ℝ) * (Polynomial.legendre N).leadingCoeff) ≠ 0 :=
      mul_ne_zero hNR.ne' (leadingCoeff_ne_zero.mpr (Polynomial.legendre_ne_zero N))
    rw [Quadrature.derivative_legendre_eq_family hN1, eval_mul, eval_C] at ht0
    rw [(mul_eq_zero.1 ht0).resolve_left hc, mul_zero]
  obtain ⟨j, hj⟩ : ∃ j, x j = t := by
    by_contra h
    push Not at h
    exact Lagrange.eval_nodal_not_at_node (fun i _ => (h i).symm) hroot
  have hj0 : j ≠ 0 := by
    rintro rfl
    rw [hx.out.first] at hj
    have := Polynomial.eval_neg_one_derivative_legendre N
    rw [← hj] at ht0
    rw [ht0] at this
    have hpos : (0 : ℝ) < (N : ℝ) * (N + 1) / 2 := by positivity
    rcases neg_one_pow_eq_or ℝ (N + 1) with h | h <;> rw [h] at this <;> linarith
  have hjN : j ≠ Fin.last N := by
    rintro rfl
    rw [hx.out.last] at hj
    linarith
  -- the test element and its Rayleigh quotient
  have hv0 := SpectralSpace.lagrangeBasis_ne_zero (x := x) (w := w) j hj0 hjN
  obtain ⟨lam, e, he, hle⟩ := exists_definition_13_1_mul_norm_sq_le
    (SpectralSpace.spectralForm_isHermitian (x := x) (w := w) ν) hv0
  refine ⟨lam, e, he, ?_⟩
  rw [SpectralSpace.norm_sq_lagrangeBasis] at hle
  have hlam : ν / (1 - x j) ≤ lam * w j :=
    (SpectralSpace.le_spectralForm_lagrangeBasis_self hν j hj0 hjN).trans hle
  -- the weight and the node location
  have hnear : 1 - x j ≤ 81 * π ^ 2 / (32 * (N : ℝ) ^ 2) := by rw [hj]; linarith
  have hwj : w j ≤ 2048 / (N : ℝ) ^ 2 :=
    Quadrature.legendreLobattoWeight_le_of_near_one hN1 (fun i => (hx.out.weight_pos i).le)
      hx.out.exact j (hx.out.mem j) hnear
  have hwpos : 0 < w j := hx.out.weight_pos j
  have hxj1 : 0 < 1 - x j := by rw [hj]; linarith
  have hprod : (1 - x j) * w j ≤ 5184 * π ^ 2 / (N : ℝ) ^ 4 := by
    calc (1 - x j) * w j ≤ (81 * π ^ 2 / (32 * (N : ℝ) ^ 2)) * (2048 / (N : ℝ) ^ 2) :=
          mul_le_mul hnear hwj hwpos.le (by positivity)
      _ = 5184 * π ^ 2 / (N : ℝ) ^ 4 := by field_simp; ring
  have hlam' : ν / ((1 - x j) * w j) ≤ lam := by
    rw [div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ hxj1] at hlam
    nlinarith
  calc 1 / (5184 * π ^ 2) * ν * (N : ℝ) ^ 4 = ν / (5184 * π ^ 2 / (N : ℝ) ^ 4) := by
        field_simp
    _ ≤ ν / ((1 - x j) * w j) := div_le_div_of_nonneg_left hν (by positivity) hprod
    _ ≤ lam := hlam'

end Spectral

end

end QuarteroniSaccoSaleri.Chapter13
