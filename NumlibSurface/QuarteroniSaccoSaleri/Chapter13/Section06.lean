/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Matrix.ToLin
import NumlibSurface.QuarteroniSaccoSaleri.Chapter13.Section05

/-!
# Quarteroni, Sacco and Saleri, Section 13.6: Systems of linear hyperbolic equations

This module formalizes Section 13.6 and Section 13.6.1 of [quarteroni2000numerical]. The system
(13.30), $u_t + A u_x = 0$ with a constant real $p \times p$ matrix $A$, is hyperbolic when $A$ is
diagonalizable over $\mathbb{R}$, $A = T \Lambda T^{-1}$, and strictly hyperbolic when the
eigenvalues are distinct. The columns $\omega^k$ of $T$ are right eigenvectors. The characteristic
variables $w = T^{-1} u$ solve $p$ decoupled scalar transport equations, so Section 13.5 applies to
each, and the solution is
$$u(x, t) = \sum_{k=1}^p w_k(x - \lambda_k t, 0)\, \omega^k.$$
In particular, $u(\bar x, \bar t)$ depends on the datum only at the $p$ points
$\bar x - \lambda_k \bar t$, the domain of dependence (13.31). Remark 13.2 defines hyperbolicity of
the nonlinear system (13.32) through the Jacobian of the flux function. Section 13.6.1 rewrites the
wave equation (13.33)–(13.34) as the first-order system (13.35) for $\omega = (u_x, u_t)$, whose
matrix $\begin{bmatrix} 0 & -1 \\ -\gamma^2 & 0 \end{bmatrix}$ has the distinct eigenvalues
$\pm\gamma$.

The proofs specialize the backbone module `Numlib.Analysis.PDE.Transport`.

## Main definitions

* (13.30), `QuarteroniSaccoSaleri.Chapter13.equation_13_30`: a classical solution of the system
  $u_t + A u_x = 0$ with the datum $u_0$.
* Remark 13.2, `QuarteroniSaccoSaleri.Chapter13.remark_13_2`: hyperbolicity of the nonlinear system
  (13.32) at a state $u$.
* (13.33)–(13.34), `QuarteroniSaccoSaleri.Chapter13.equation_13_33`: a classical solution of the
  wave equation on a strip, with homogeneous Dirichlet conditions.

## Main results

* Section 13.6, `QuarteroniSaccoSaleri.Chapter13.isHyperbolic`: a strictly hyperbolic system is
  hyperbolic, and the columns of $T$ are eigenvectors of $A$.
* Section 13.6, `QuarteroniSaccoSaleri.Chapter13.characteristicVariables`: each characteristic
  variable $w_k$ solves a scalar transport equation with speed $\lambda_k$.
* Section 13.6, `QuarteroniSaccoSaleri.Chapter13.hyperbolicSystem_solution`: the formula $u(x, t) =
  \sum_k w_k(x - \lambda_k t, 0) \omega^k$ gives the unique solution.
* (13.31), `QuarteroniSaccoSaleri.Chapter13.equation_13_31`: two data that agree on the domain of
  dependence of $(\bar x, \bar t)$ give solutions that agree at $(\bar x, \bar t)$.
* (13.35), `QuarteroniSaccoSaleri.Chapter13.equation_13_35`: a solution of the homogeneous wave
  equation gives a solution of a first-order system with the matrix $\begin{bmatrix} 0 & -1 \\
  -\gamma^2 & 0 \end{bmatrix}$.
* Section 13.6.1, `QuarteroniSaccoSaleri.Chapter13.waveMatrix_isHyperbolic`: for $\gamma \neq 0$ the
  matrix of (13.35) is strictly hyperbolic.

## Implementation notes

* Vectors of $\mathbb{R}^p$ are functions `Fin p → ℝ`. The $k$-th column of $T$ is `Tᵀ k`.
* Hyperbolicity is `Transport.IsHyperbolic` and strict hyperbolicity is
  `Transport.IsStrictlyHyperbolic`. Both ask for an invertible $T$ and a real diagonal $\Lambda$
  with $A = T \Lambda T^{-1}$; the strict form also asks that the diagonal entries are distinct.

## Deviations from the source

* **Equations (13.30)–(13.31)** (reading). The system holds at time zero and uses within
  differentiability. The characteristic solution requires differentiable transformed data, and
  the domain-of-dependence equality also covers repeated speeds. See
  `QuarteroniSaccoSaleri.Chapter13.hyperbolicSystem_solution` and
  `QuarteroniSaccoSaleri.Chapter13.equation_13_31`.
* **Remark 13.2** (reading). The predicate is pointwise and uses the total Fréchet derivative.
  Differentiability at the relevant states and validity throughout the state range are supplied
  separately. See `QuarteroniSaccoSaleri.Chapter13.remark_13_2`.
* **Equations (13.33)–(13.35)** (correction). The first-order system printed for the forced wave
  equation omits the vector $(0,f)$. The homogeneous reduction requires $f=0$ and uses the
  closed spatial interval and nonnegative times, including the corner compatibility conditions.
  The eigenvalues are distinct when $\gamma\ne0$. See
  `QuarteroniSaccoSaleri.Chapter13.equation_13_35` and
  `QuarteroniSaccoSaleri.Chapter13.waveMatrix_isHyperbolic`.

## Not formalized

* Remark 13.3, the classification of second-order equations by conic sections. It is heuristic
  prose.
* The number of boundary conditions that a hyperbolic system needs at each end of the interval.
-/

open Matrix

namespace QuarteroniSaccoSaleri.Chapter13

variable {p : ℕ}

/-! ### The system (13.30) and hyperbolicity -/

/-- **Equation (13.30)** of [quarteroni2000numerical]. Let $A \in \mathbb{R}^{p \times p}$ and
$u_0 : \mathbb{R} \to \mathbb{R}^p$. A function $u : \mathbb{R} \times \mathbb{R} \to
\mathbb{R}^p$ is a **classical solution** of the system
$$u_t + A u_x = 0 \quad \text{on } \mathbb{R} \times [0, \infty), \qquad u(x, 0) = u_0(x),$$
if every component of $u$ has partial derivatives on $\mathbb{R} \times [0, \infty)$, the vector
equation holds at every point of that set, and the initial condition holds for all $x$.

The definition is `Transport.IsSystemSolution`.

**Reading.** Classical solutions use within derivatives and the equation includes time zero. -/
def equation_13_30 (A : Matrix (Fin p) (Fin p) ℝ) (u₀ : ℝ → Fin p → ℝ)
    (u : ℝ → ℝ → Fin p → ℝ) : Prop := Transport.IsSystemSolution A u₀ u

/-- **Section 13.6** of [quarteroni2000numerical], hyperbolic systems. Let
$A \in \mathbb{R}^{p \times p}$. The system (13.30) is **hyperbolic** if $A = T \Lambda T^{-1}$
for an invertible real matrix $T$ and a real diagonal matrix $\Lambda =
\operatorname{diag}(\lambda_1, \ldots, \lambda_p)$, and **strictly hyperbolic** if moreover the
$\lambda_k$ are distinct. Then:

* a strictly hyperbolic system is hyperbolic;
* if $T$ is invertible and $A = T \Lambda T^{-1}$, then the $k$-th column $\omega^k$ of $T$ is a
  right eigenvector of $A$: $A \omega^k = \lambda_k \omega^k$ for every $k$.

The two notions are `Transport.IsHyperbolic` and `Transport.IsStrictlyHyperbolic`. The column
$\omega^k$ is `Tᵀ k`. -/
theorem isHyperbolic (A : Matrix (Fin p) (Fin p) ℝ) :
    (Transport.IsStrictlyHyperbolic A → Transport.IsHyperbolic A) ∧
      ∀ (T : Matrix (Fin p) (Fin p) ℝ) (lam : Fin p → ℝ), IsUnit T →
        A = T * diagonal lam * T⁻¹ → ∀ k, A *ᵥ Tᵀ k = lam k • Tᵀ k :=
  ⟨Transport.IsStrictlyHyperbolic.isHyperbolic,
    fun _ _ hT hA k => Transport.mulVec_col_eq_smul hT hA k⟩

/-- **Section 13.6** of [quarteroni2000numerical], the characteristic variables. Let
$A, T \in \mathbb{R}^{p \times p}$ with $T$ invertible and $A = T \Lambda T^{-1}$, $\Lambda =
\operatorname{diag}(\lambda_1, \ldots, \lambda_p)$, and let $u$ be a solution of (13.30) with
the datum $u_0$. Then for each $k$ the characteristic variable $w_k = (T^{-1} u)_k$ is a
solution of the scalar transport equation (13.26)
$$\partial_t w_k + \lambda_k \partial_x w_k = 0, \qquad w_k(x, 0) = (T^{-1} u_0(x))_k.$$
-/
theorem characteristicVariables {A T : Matrix (Fin p) (Fin p) ℝ} {lam : Fin p → ℝ} (hT : IsUnit T)
    (hA : A = T * diagonal lam * T⁻¹) {u₀ : ℝ → Fin p → ℝ} {u : ℝ → ℝ → Fin p → ℝ}
    (hu : equation_13_30 A u₀ u) (k : Fin p) :
    equation_13_26 (lam k) (fun x => (T⁻¹ *ᵥ u₀ x) k) (fun x t => (T⁻¹ *ᵥ u x t) k) :=
  hu.characteristicVariables hT hA k

/-- **Section 13.6** of [quarteroni2000numerical], the solution formula of a hyperbolic system. Let
$A, T \in \mathbb{R}^{p \times p}$ with $T$ invertible and $A = T \Lambda T^{-1}$, $\Lambda =
\operatorname{diag}(\lambda_1, \ldots, \lambda_p)$, and let $u_0 : \mathbb{R} \to \mathbb{R}^p$
be such that each component of $T^{-1} u_0$ is differentiable. Then
$$u(x, t) = \sum_{k=1}^p (T^{-1} u_0(x - \lambda_k t))_k\, \omega^k,$$
where $\omega^k$ is the $k$-th column of $T$, is a solution of (13.30), and every solution of
(13.30) with the datum $u_0$ is equal to it at all $x$ and all $t \ge 0$.

The coefficient $(T^{-1} u_0(x - \lambda_k t))_k$ is the characteristic variable
$w_k(x - \lambda_k t, 0)$. The column $\omega^k$ is `Tᵀ k`.

**Reading.** The solution formula and uniqueness require differentiability of each transformed
initial component. -/
theorem hyperbolicSystem_solution {A T : Matrix (Fin p) (Fin p) ℝ} {lam : Fin p → ℝ}
    (hT : IsUnit T) (hA : A = T * diagonal lam * T⁻¹) {u₀ : ℝ → Fin p → ℝ}
    (hu₀ : ∀ k, Differentiable ℝ fun x => (T⁻¹ *ᵥ u₀ x) k) :
    equation_13_30 A u₀ (fun x t => ∑ k, (T⁻¹ *ᵥ u₀ (x - lam k * t)) k • Tᵀ k) ∧
      ∀ u : ℝ → ℝ → Fin p → ℝ, equation_13_30 A u₀ u → ∀ (x t : ℝ), 0 ≤ t →
        u x t = ∑ k, (T⁻¹ *ᵥ u₀ (x - lam k * t)) k • Tᵀ k :=
  ⟨Transport.isSystemSolution_sum hT hA hu₀, fun _ hu x _ ht => hu.eq_sum hT hA x ht⟩

/-- **Equation (13.31)** of [quarteroni2000numerical], the domain of dependence. Let
$A, T \in \mathbb{R}^{p \times p}$ with $T$ invertible and $A = T \Lambda T^{-1}$, $\Lambda =
\operatorname{diag}(\lambda_1, \ldots, \lambda_p)$. Let $u$ and $v$ be solutions of (13.30) with
the data $u_0$ and $v_0$, and let $\bar x \in \mathbb{R}$ and $\bar t \ge 0$. If $u_0$ and $v_0$
agree on the domain of dependence
$$D(\bar x, \bar t) = \{\bar x - \lambda_k \bar t : k = 1, \ldots, p\},$$
then $u(\bar x, \bar t) = v(\bar x, \bar t)$.

The set $D(\bar x, \bar t)$ is `Transport.domainOfDependence`. Its points are the feet of the
characteristics through $(\bar x, \bar t)$.

**Generalization.** Equality of initial data on the characteristic feet suffices even when
speeds repeat. -/
theorem equation_13_31 {A T : Matrix (Fin p) (Fin p) ℝ} {lam : Fin p → ℝ} (hT : IsUnit T)
    (hA : A = T * diagonal lam * T⁻¹) {u₀ v₀ : ℝ → Fin p → ℝ} {u v : ℝ → ℝ → Fin p → ℝ}
    (hu : equation_13_30 A u₀ u) (hv : equation_13_30 A v₀ v) {xb tb : ℝ} (htb : 0 ≤ tb)
    (h : Set.EqOn u₀ v₀ (Transport.domainOfDependence lam xb tb)) : u xb tb = v xb tb :=
  hu.eq_of_eqOn_domainOfDependence hT hA hv htb h

/-- **Remark 13.2** of [quarteroni2000numerical]. Let $g : \mathbb{R}^p \to \mathbb{R}^p$ be the
flux function of the nonlinear system (13.32), $u_t + \partial_x g(u) = 0$. The system is
**hyperbolic at the state** $u \in \mathbb{R}^p$ if the Jacobian matrix $J_g(u)$ is
diagonalizable with real eigenvalues, in the sense of `Transport.IsHyperbolic`.

The Jacobian is the matrix of `fderiv ℝ g u`. If $g$ is not differentiable at $u$, this
derivative is $0$ in Lean, and the system counts as hyperbolic at $u$.

**Reading.** This checks the Jacobian at one state, using the total Fréchet derivative. The
differentiability and state-space hypotheses of the Jacobian interpretation are external. -/
def remark_13_2 (g : (Fin p → ℝ) → (Fin p → ℝ)) (u : Fin p → ℝ) : Prop :=
  Transport.IsHyperbolic (LinearMap.toMatrix' (fderiv ℝ g u : (Fin p → ℝ) →ₗ[ℝ] (Fin p → ℝ)))

/-! ### §13.6.1, the wave equation -/

/-- **Equations (13.33)–(13.34)** of [quarteroni2000numerical]. Let $\gamma \in \mathbb{R}$, $f :
\mathbb{R} \times \mathbb{R} \to \mathbb{R}$, $u_0, v_0 : \mathbb{R} \to \mathbb{R}$ and
$\alpha, \beta \in \mathbb{R}$. A function $u$ is a **classical solution of the wave equation**
$$\partial_{tt} u - \gamma^2 \partial_{xx} u = f \quad \text{on } [\alpha, \beta] \times [0,
  \infty),$$
with $u(x, 0) = u_0(x)$ and $\partial_t u(x, 0) = v_0(x)$ for $x \in [\alpha, \beta]$, and
$u(\alpha, t) = u(\beta, t) = 0$ for $t \ge 0$, if $u$, $\partial_x u$ and $\partial_t u$ have
partial derivatives on the strip and these satisfy the equation and the conditions.

The definition is `Transport.IsWaveSolution`. It uses one function for the two mixed partial
derivatives $\partial_{xt} u$ and $\partial_{tx} u$. This is no restriction for a $C^2$
function.

**Reading.** The PDE and derivatives are imposed on the closed spatial interval and at time
zero, so the initial and boundary data must be compatible. -/
def equation_13_33 (γ : ℝ) (f : ℝ → ℝ → ℝ) (u₀ v₀ : ℝ → ℝ) (α β : ℝ) (u : ℝ → ℝ → ℝ) : Prop :=
  Transport.IsWaveSolution γ f u₀ v₀ α β u

/-- **Equation (13.35)** of [quarteroni2000numerical], the wave equation as a first-order system.
Let $\gamma, \alpha, \beta \in \mathbb{R}$, $u_0, v_0 : \mathbb{R} \to \mathbb{R}$, and let $u$
be a solution of the homogeneous wave equation (13.33)–(13.34), with $f = 0$. Then there is a
function $\omega : \mathbb{R} \times \mathbb{R} \to \mathbb{R}^2$ that solves
$$\partial_t \omega + A \partial_x \omega = 0 \quad \text{on } [\alpha, \beta] \times [0,
  \infty), \qquad A = \begin{bmatrix} 0 & -1 \\ -\gamma^2 & 0 \end{bmatrix},$$
and has the initial values $\omega_1(x, 0) = u_0'(x)$ and $\omega_2(x, 0) = v_0(x)$ for
$x \in [\alpha, \beta]$.

The function constructed in the proof is $\omega = (\partial_x u, \partial_t u)$, but the
statement asserts only that $\omega$ exists. The derivative $u_0'$ is taken within
$[\alpha, \beta]$. The matrix $A$ is `Transport.waveMatrix γ`, and the system on the strip is
`Transport.IsSystemSolutionOn`.

**Correction.** The printed first-order system is homogeneous even in the presence of a source
term. The theorem requires $f=0$; the forced reduction would have right-hand side $(0,f)$. -/
theorem equation_13_35 {γ : ℝ} {u₀ v₀ : ℝ → ℝ} {α β : ℝ} {u : ℝ → ℝ → ℝ}
    (hu : equation_13_33 γ 0 u₀ v₀ α β u) :
    ∃ w : ℝ → ℝ → Fin 2 → ℝ,
      Transport.IsSystemSolutionOn (Set.Icc α β) (Transport.waveMatrix γ) (fun x => w x 0) w ∧
        (∀ x ∈ Set.Icc α β, HasDerivWithinAt u₀ (w x 0 0) (Set.Icc α β) x) ∧
        ∀ x ∈ Set.Icc α β, w x 0 1 = v₀ x :=
  hu.isSystemSolution

/-- **Section 13.6.1** of [quarteroni2000numerical], hyperbolicity of the wave equation. Let
$\gamma \neq 0$. Then the matrix $A = \begin{bmatrix} 0 & -1 \\ -\gamma^2 & 0 \end{bmatrix}$ of
(13.35) is strictly hyperbolic, and therefore hyperbolic.

The proof diagonalizes $A$ with the eigenvalues $\gamma$ and $-\gamma$, the propagation speeds
of the wave, and the eigenvectors $(1, -\gamma)$ and $(1, \gamma)$. The statement does not name
these eigenvalues.

**Reading.** The strict conclusion requires the two speeds to be distinct, so $\gamma\ne0$. -/
theorem waveMatrix_isHyperbolic {γ : ℝ} (hγ : γ ≠ 0) :
    Transport.IsStrictlyHyperbolic (Transport.waveMatrix γ) ∧
      Transport.IsHyperbolic (Transport.waveMatrix γ) :=
  ⟨Transport.waveMatrix_isStrictlyHyperbolic hγ,
    (Transport.waveMatrix_isStrictlyHyperbolic hγ).isHyperbolic⟩

end QuarteroniSaccoSaleri.Chapter13
