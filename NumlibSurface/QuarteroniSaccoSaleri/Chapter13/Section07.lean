/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.FiniteDifference.Hyperbolic

/-!
# Quarteroni, Sacco and Saleri, Section 13.7: The finite difference method for hyperbolic equations

This module formalizes Section 13.7 and Section 13.7.1 of [quarteroni2000numerical], finite
difference schemes for the transport equation (13.26), $u_t + a u_x = 0$. The grid is
$x_j = j \Delta x$, $t^n = n \Delta t$, and $\lambda = \Delta t / \Delta x$. An explicit scheme has
the conservative form (13.36), $u_j^{n+1} = u_j^n - \lambda (h_{j+1/2} - h_{j-1/2})$, with a
numerical flux $h$. The four explicit schemes of Section 13.7.1 are forward Euler/centred (13.37),
Lax–Friedrichs (13.39), Lax–Wendroff (13.40) and upwind (13.41). Each is a three-point scheme with
its own flux, and each of the last three is the forward Euler/centred scheme plus an artificial
viscosity term (13.42), with the coefficient $k$ of Table 13.1. The implicit backward Euler/centred
scheme (13.43) is solved on $\ell^2(\mathbb{Z})$ by the inverse of $I + \frac{\lambda a}{2} D_0$,
which exists because the centred difference $D_0$ is skew-adjoint. The leap-frog scheme (13.44) and
the Newmark scheme (13.45) discretize the wave equation.

The schemes are defined in the backbone module `Numlib.FiniteDifference.Hyperbolic`, over the
stencils of `Numlib.FiniteDifference.Stencil`.

## Main definitions

* (13.36), `QuarteroniSaccoSaleri.Chapter13.equation_13_36`: a one-step map in conservative form
  with a numerical flux $h$.
* (13.37), `QuarteroniSaccoSaleri.Chapter13.equation_13_37`: the forward Euler/centred scheme.
* (13.39), `QuarteroniSaccoSaleri.Chapter13.equation_13_39`: the Lax–Friedrichs scheme.
* (13.40), `QuarteroniSaccoSaleri.Chapter13.equation_13_40`: the Lax–Wendroff scheme.
* (13.41), `QuarteroniSaccoSaleri.Chapter13.equation_13_41`: the upwind scheme.
* (13.42), `QuarteroniSaccoSaleri.Chapter13.equation_13_42`: the forward Euler/centred scheme with
  an artificial viscosity $k$.
* (13.43), `QuarteroniSaccoSaleri.Chapter13.equation_13_43`: the solution operator of the backward
  Euler/centred scheme on $\ell^2(\mathbb{Z})$.
* (13.44), `QuarteroniSaccoSaleri.Chapter13.equation_13_44`: the leap-frog scheme for the wave
  equation.
* (13.45), `QuarteroniSaccoSaleri.Chapter13.equation_13_45`: the Newmark scheme for the wave
  equation.

## Main results

* (13.36), `QuarteroniSaccoSaleri.Chapter13.equation_13_36_ofFlux`: a linear numerical flux gives a
  three-point scheme in conservative form.
* (13.38), `QuarteroniSaccoSaleri.Chapter13.equation_13_38`: the forward Euler/centred scheme has
  the flux $h(u, v) = \frac{a}{2}(u + v)$.
* Section 13.7.1, `QuarteroniSaccoSaleri.Chapter13.equation_13_39_flux`: the Lax–Friedrichs flux.
* Section 13.7.1, `QuarteroniSaccoSaleri.Chapter13.equation_13_40_flux`: the Lax–Wendroff flux.
* (13.50), `QuarteroniSaccoSaleri.Chapter13.equation_13_50`: for $a > 0$ the upwind scheme is
  $u_j^{n+1} = u_j^n - \lambda a (u_j^n - u_{j-1}^n)$.
* Section 13.7.1, `QuarteroniSaccoSaleri.Chapter13.equation_13_41_flux`: the upwind flux.
* Exercise 5 and Table 13.1, `QuarteroniSaccoSaleri.Chapter13.exercise_13_5`: the Lax–Friedrichs,
  Lax–Wendroff and upwind schemes are (13.42) with $k = \Delta x^2$, $a^2 \Delta t^2$ and
  $|a| \Delta x \Delta t$.
* (13.43), `QuarteroniSaccoSaleri.Chapter13.equation_13_43_spec`: the solution operator solves the
  implicit scheme, and $D_0$ is skew-adjoint.

## Implementation notes

* A grid function at one time level is a function $\mathbb{Z} \to \mathbb{R}$, $j \mapsto u_j$. An
  explicit scheme is a `FiniteDifference.Stencil`, a finitely supported function
  $\mathbb{Z} \to \mathbb{R}$ that acts by `FiniteDifference.Stencil.apply`. The stencil
  `FiniteDifference.Stencil.threePoint cm c0 cp` sends $u$ to
  $j \mapsto c_- u_{j-1} + c_0 u_j + c_+ u_{j+1}$.
* The stencil `FiniteDifference.Stencil.ofFlux lam α β` is the conservative scheme (13.36) for the
  linear flux $h(u, v) = \alpha u + \beta v$.
* The implicit scheme (13.43) works on the Hilbert space $\ell^2(\mathbb{Z})$,
  `lp (fun _ : ℤ => ℝ) 2`, where $I + \frac{\lambda a}{2} D_0$ is invertible.
* The schemes for the wave equation are relations between the levels of a function
  $\mathbb{N} \times \mathbb{Z} \to \mathbb{R}$, $(n, j) \mapsto u_j^n$, not stencils.

## Deviations from the source

* **Equations (13.36)–(13.42) and Exercise 13.5** (reading). The conservative predicate and
  viscosity stencil allow arbitrary real parameters, with total division in the viscosity
  definition. The exercise gives the viscosity identities, and the three numerical-flux theorems
  encode the flux terms in Table 13.1. See `QuarteroniSaccoSaleri.Chapter13.exercise_13_5`.
* **Equation (13.43)** (specialization). The implicit update is constructed on square-summable
  sequences. Its pointwise equation and the skew-adjoint identity used for the energy estimate
  are separate conclusions. See `QuarteroniSaccoSaleri.Chapter13.equation_13_43_spec`.
* **Equation (13.45)** (generalization). The update accepts arbitrary real $\beta,\theta,\Delta
  t$ and uses total division. See `QuarteroniSaccoSaleri.Chapter13.equation_13_45`.
-/

open FiniteDifference FiniteDifference.Hyperbolic

namespace QuarteroniSaccoSaleri.Chapter13

/-! ### The conservative form (13.36) -/

/-- **Equation (13.36)** of [quarteroni2000numerical], the conservative form. Let
$\lambda \in \mathbb{R}$ and let $h : \mathbb{R} \times \mathbb{R} \to \mathbb{R}$ be a
numerical flux. A map $S$ on grid functions $u : \mathbb{Z} \to \mathbb{R}$ is **in conservative
form** with the flux $h$ if for all $u$ and $j$
$$(Su)_j = u_j - \lambda \bigl(h(u_j, u_{j+1}) - h(u_{j-1}, u_j)\bigr).$$

The definition is `FiniteDifference.IsConservativeForm`. For a linear flux
$h(u, v) = \alpha u + \beta v$, the map in conservative form is the three-point stencil
`FiniteDifference.Stencil.ofFlux lam α β`.

**Reading.** The two-point flux identity is stated for all grid functions with arbitrary
$\lambda$, with mesh positivity left external. -/
def equation_13_36 (lam : ℝ) (h : ℝ → ℝ → ℝ) (step : (ℤ → ℝ) → ℤ → ℝ) : Prop :=
  FiniteDifference.IsConservativeForm lam h step

/-- **Equation (13.36)** of [quarteroni2000numerical], linear fluxes. Let
$\lambda, \alpha, \beta \in \mathbb{R}$. The action of the stencil
`FiniteDifference.Stencil.ofFlux lam α β` is in conservative form with the linear flux
$h(u, v) = \alpha u + \beta v$.

**Reading.** General linear-flux representation on any real coefficients.
-/
theorem equation_13_36_ofFlux (lam α β : ℝ) :
    equation_13_36 lam (fun u v => α * u + β * v) (Stencil.apply (Stencil.ofFlux lam α β)) :=
  Stencil.isConservativeForm_ofFlux lam α β

/-! ### The explicit schemes of §13.7.1 -/

/-- **Equation (13.37)** of [quarteroni2000numerical], the forward Euler/centred scheme. For
$a, \lambda \in \mathbb{R}$, it is the three-point scheme
$$u_j^{n+1} = u_j^n - \frac{\lambda a}{2} (u_{j+1}^n - u_{j-1}^n).$$

The definition is `FiniteDifference.Hyperbolic.forwardEulerCentred`. -/
noncomputable def equation_13_37 (a lam : ℝ) : Stencil := forwardEulerCentred a lam

/-- **Equation (13.38)** of [quarteroni2000numerical]. Let $a, \lambda \in \mathbb{R}$. The forward
Euler/centred scheme (13.37) is the stencil of the linear flux
$$h(u, v) = \frac{a}{2} (u + v),$$
so it is in conservative form (13.36) with this flux. -/
theorem equation_13_38 (a lam : ℝ) :
    equation_13_37 a lam = Stencil.ofFlux lam (a / 2) (a / 2) ∧
      equation_13_36 lam (fun u v => a / 2 * u + a / 2 * v)
        (Stencil.apply (equation_13_37 a lam)) := by
  refine ⟨forwardEulerCentred_eq_ofFlux a lam, ?_⟩
  rw [equation_13_37, forwardEulerCentred_eq_ofFlux]
  exact Stencil.isConservativeForm_ofFlux lam (a / 2) (a / 2)

/-- **Equation (13.39)** of [quarteroni2000numerical], the Lax–Friedrichs scheme. For
$a, \lambda \in \mathbb{R}$, it is the three-point scheme
$$u_j^{n+1} = \frac{1}{2} (u_{j+1}^n + u_{j-1}^n) - \frac{\lambda a}{2} (u_{j+1}^n -
  u_{j-1}^n).$$

The definition is `FiniteDifference.Hyperbolic.laxFriedrichs`. -/
noncomputable def equation_13_39 (a lam : ℝ) : Stencil := laxFriedrichs a lam

/-- **Section 13.7.1** of [quarteroni2000numerical], the Lax–Friedrichs flux. Let $a \in \mathbb{R}$
and $\lambda \neq 0$. The Lax–Friedrichs scheme (13.39) is the conservative scheme (13.36) of
the flux
$$h(u, v) = \frac{1}{2} \bigl[a (u + v) - \lambda^{-1} (v - u)\bigr].$$
-/
theorem equation_13_39_flux {lam : ℝ} (hlam : lam ≠ 0) (a : ℝ) :
    equation_13_39 a lam = Stencil.ofFlux lam (a / 2 + 1 / (2 * lam)) (a / 2 - 1 / (2 * lam)) :=
  laxFriedrichs_eq_ofFlux hlam a

/-- **Equation (13.40)** of [quarteroni2000numerical], the Lax–Wendroff scheme. For
$a, \lambda \in \mathbb{R}$, it is the three-point scheme
$$u_j^{n+1} = u_j^n - \frac{\lambda a}{2} (u_{j+1}^n - u_{j-1}^n) + \frac{\lambda^2 a^2}{2}
  (u_{j+1}^n - 2 u_j^n + u_{j-1}^n).$$

The definition is `FiniteDifference.Hyperbolic.laxWendroff`. -/
noncomputable def equation_13_40 (a lam : ℝ) : Stencil := laxWendroff a lam

/-- **Section 13.7.1** of [quarteroni2000numerical], the Lax–Wendroff flux. Let
$a, \lambda \in \mathbb{R}$. The Lax–Wendroff scheme (13.40) is the conservative scheme (13.36)
of the flux
$$h(u, v) = \frac{1}{2} \bigl[a (u + v) - \lambda a^2 (v - u)\bigr].$$
-/
theorem equation_13_40_flux (a lam : ℝ) :
    equation_13_40 a lam
      = Stencil.ofFlux lam (a / 2 + lam * a ^ 2 / 2) (a / 2 - lam * a ^ 2 / 2) :=
  laxWendroff_eq_ofFlux a lam

/-- **Equation (13.41)** of [quarteroni2000numerical], the upwind scheme. For
$a, \lambda \in \mathbb{R}$, it is the three-point scheme
$$u_j^{n+1} = u_j^n - \frac{\lambda a}{2} (u_{j+1}^n - u_{j-1}^n) + \frac{\lambda |a|}{2}
  (u_{j+1}^n - 2 u_j^n + u_{j-1}^n).$$

The definition is `FiniteDifference.Hyperbolic.upwind`. For $a > 0$ it is (13.50); see
`QuarteroniSaccoSaleri.Chapter13.equation_13_50`. -/
noncomputable def equation_13_41 (a lam : ℝ) : Stencil := upwind a lam

/-- **Equation (13.50)** of [quarteroni2000numerical]. Let $a > 0$ and $\lambda \in \mathbb{R}$.
Then the upwind scheme (13.41) is
$$u_j^{n+1} = u_j^n - \lambda a (u_j^n - u_{j-1}^n).$$
-/
theorem equation_13_50 {a : ℝ} (ha : 0 < a) (lam : ℝ) :
    equation_13_41 a lam = Stencil.threePoint (lam * a) (1 - lam * a) 0 :=
  upwind_eq_of_pos ha lam

/-- **Section 13.7.1** of [quarteroni2000numerical], the upwind flux. Let
$a, \lambda \in \mathbb{R}$. The upwind scheme (13.41) is the conservative scheme (13.36) of the
flux
$$h(u, v) = \frac{1}{2} \bigl[a (u + v) - |a| (v - u)\bigr].$$
-/
theorem equation_13_41_flux (a lam : ℝ) :
    equation_13_41 a lam = Stencil.ofFlux lam ((a + |a|) / 2) ((a - |a|) / 2) :=
  upwind_eq_ofFlux a lam

/-- **Equation (13.42)** of [quarteroni2000numerical], the artificial viscosity form. For
$a, \lambda, \Delta x, k \in \mathbb{R}$, it is the three-point scheme
$$u_j^{n+1} = u_j^n - \frac{\lambda a}{2} (u_{j+1}^n - u_{j-1}^n) + \frac{k}{2}
  \frac{u_{j+1}^n - 2 u_j^n + u_{j-1}^n}{\Delta x^2}.$$

The definition is `FiniteDifference.Hyperbolic.artificialViscosity`.

**Reading.** The stencil accepts arbitrary real parameters and uses total division at $\Delta
x=0$. -/
noncomputable def equation_13_42 (a lam Δx k : ℝ) : Stencil := artificialViscosity a lam Δx k

/-- **Exercise 5 of Chapter 13** and **Table 13.1** of [quarteroni2000numerical]. Let
$\Delta t \in \mathbb{R}$, $\Delta x \neq 0$, $\lambda = \Delta t / \Delta x$ and
$a \in \mathbb{R}$. Then the Lax–Friedrichs, Lax–Wendroff and upwind schemes are the artificial
viscosity scheme (13.42) with the coefficients
$$k = \Delta x^2, \qquad k = a^2 \Delta t^2, \qquad k = |a| \Delta x \Delta t,$$
respectively.

**Reading.** This states the viscosity identities. The flux theorems give the corresponding
linear flux formulas. -/
theorem exercise_13_5 {Δt Δx lam : ℝ} (hΔx : Δx ≠ 0) (hlam : lam = Δt / Δx) (a : ℝ) :
    equation_13_39 a lam = equation_13_42 a lam Δx (Δx ^ 2) ∧
      equation_13_40 a lam = equation_13_42 a lam Δx (a ^ 2 * Δt ^ 2) ∧
      equation_13_41 a lam = equation_13_42 a lam Δx (|a| * Δx * Δt) :=
  ⟨laxFriedrichs_eq_artificialViscosity hΔx a lam, laxWendroff_eq_artificialViscosity hΔx hlam a,
    upwind_eq_artificialViscosity hΔx hlam a⟩

/-! ### The implicit scheme (13.43) -/

/-- **Equation (13.43)** of [quarteroni2000numerical], the backward Euler/centred scheme
$$u_j^{n+1} + \frac{\lambda a}{2} (u_{j+1}^{n+1} - u_{j-1}^{n+1}) = u_j^n.$$
For $a, \lambda \in \mathbb{R}$, this definition is the operator $B^{-1}$ on
$\ell^2(\mathbb{Z})$ that sends $u^n$ to $u^{n+1}$, where $B = I + \frac{\lambda a}{2} D_0$ and
$D_0$ is the centred difference $(D_0 u)_j = u_{j+1} - u_{j-1}$.

The operator $B$ is invertible because $D_0$ is skew-adjoint, so that
$\langle Bu, u \rangle = \|u\|^2$. The definition is
`FiniteDifference.Hyperbolic.backwardEulerCentred`.

**Specialization.** The implicit equation is realized as a unique bounded update on square-
summable grids. -/
noncomputable def equation_13_43 (a lam : ℝ) :
    lp (fun _ : ℤ => ℝ) 2 →L[ℝ] lp (fun _ : ℤ => ℝ) 2 := backwardEulerCentred a lam

/-- **Equation (13.43)** and **Exercise 7 of Chapter 13** of [quarteroni2000numerical]. Let
$a, \lambda \in \mathbb{R}$, $u \in \ell^2(\mathbb{Z})$ and $j \in \mathbb{Z}$, and let
$w = B^{-1} u$ be the image of $u$ under `QuarteroniSaccoSaleri.Chapter13.equation_13_43`. Then
$$w_j + \frac{\lambda a}{2} (w_{j+1} - w_{j-1}) = u_j,$$
so $w$ is the new level of the implicit scheme (13.43). Moreover the centred difference $D_0$ is
skew-adjoint on $\ell^2(\mathbb{Z})$: $\langle D_0 v, w \rangle = -\langle v, D_0 w \rangle$ for
all $v, w$.

The centred difference is `FiniteDifference.Hyperbolic.centredDiffCLM`.

**Reading.** Proves the specified update on ℓ² and separately gives the bilinear skew identity
behind telescoping.
-/
theorem equation_13_43_spec (a lam : ℝ) (u : lp (fun _ : ℤ => ℝ) 2) (j : ℤ) :
    equation_13_43 a lam u j
        + lam * a / 2 * (equation_13_43 a lam u (j + 1) - equation_13_43 a lam u (j - 1)) = u j ∧
      ∀ v w : lp (fun _ : ℤ => ℝ) 2,
        inner ℝ (centredDiffCLM v) w = -inner ℝ v (centredDiffCLM w) := by
  refine ⟨?_, fun v w => inner_centredDiffCLM_left v w⟩
  have h := backwardEulerCentredOp_apply a lam (backwardEulerCentred a lam u) j
  rw [backwardEulerCentred_spec] at h
  exact h.symm

/-! ### The schemes for the wave equation -/

/-- **Equation (13.44)** of [quarteroni2000numerical], the leap-frog scheme for the wave equation
$u_{tt} = \gamma^2 u_{xx}$. For $\gamma, \lambda \in \mathbb{R}$, a function
$(n, j) \mapsto u_j^n$ on $\mathbb{N} \times \mathbb{Z}$ satisfies the scheme if for all
$n \ge 1$ and all $j$
$$u_j^{n+1} - 2 u_j^n + u_j^{n-1} = (\gamma \lambda)^2 (u_{j+1}^n - 2 u_j^n + u_{j-1}^n).$$

The definition is `FiniteDifference.Hyperbolic.IsLeapFrog`, which states the relation for the
levels $n$, $n + 1$, $n + 2$ for every $n \in \mathbb{N}$. -/
def equation_13_44 (γ lam : ℝ) (u : ℕ → ℤ → ℝ) : Prop := IsLeapFrog γ lam u

/-- **Equation (13.45)** of [quarteroni2000numerical], the Newmark scheme for the wave equation
$u_{tt} = \gamma^2 u_{xx}$. Let $\gamma, \lambda, \Delta t, \beta, \theta \in \mathbb{R}$, and
write $\delta^2 u_j = u_{j+1} - 2 u_j + u_{j-1}$. Functions $u$ and $v$ on
$\mathbb{N} \times \mathbb{Z}$, the displacement and the auxiliary velocity, satisfy the scheme
if for all $n$ and $j$
$$u_j^{n+1} - u_j^n = \Delta t\, v_j^n + (\gamma \lambda)^2 \bigl[\beta\, \delta^2 u_j^{n+1} +
  (\tfrac{1}{2} - \beta)\, \delta^2 u_j^n\bigr],$$
$$v_j^{n+1} - v_j^n = \frac{(\gamma \lambda)^2}{\Delta t} \bigl[\theta\, \delta^2 u_j^{n+1} +
  (1 - \theta)\, \delta^2 u_j^n\bigr].$$

The source takes $0 \le \beta \le \frac{1}{2}$ and $0 \le \theta \le 1$. The definition,
`FiniteDifference.Hyperbolic.IsNewmark`, does not restrict the parameters.

**Generalization.** The predicate omits the source's bounds on $\beta$ and $\theta$ and uses
total division by $\Delta t$. -/
def equation_13_45 (γ lam Δt β θ : ℝ) (u v : ℕ → ℤ → ℝ) : Prop := IsNewmark γ lam Δt β θ u v

end QuarteroniSaccoSaleri.Chapter13
