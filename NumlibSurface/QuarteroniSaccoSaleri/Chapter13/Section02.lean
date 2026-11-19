/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.FiniteDifference.Hyperbolic
import Numlib.FiniteDifference.Parabolic

/-!
# Quarteroni, Sacco and Saleri, Section 13.2: Finite differences for the heat equation

This module formalizes Section 13.2 of [quarteroni2000numerical], the finite difference
approximation of the heat equation $u_t - \nu u_{xx} = f$ on $(0, 1)$. The three-point second
difference on the uniform grid $x_i = ih$, $h = 1/n$, discretizes the equation in space. This leaves
the system (13.8) of ordinary differential equations $\dot u = -\nu A_{fd} u + f$ for the $n - 1$
interior values, where $A_{fd} = h^{-2} \operatorname{tridiag}(-1, 2, -1)$ is the matrix (12.8). The
$\theta$-method (13.9)–(13.10) discretizes (13.8) in time.

Stability means asymptotic stability, as in Section 11.1. Without a source, the forward Euler
iterates are $u^k = (I - \nu \Delta t A_{fd})^k u^0$, and they tend to zero for every datum if and
only if the spectral radius of $I - \nu \Delta t A_{fd}$ is less than $1$ (13.11). The eigenvalues
of $A_{fd}$ are $\mu_i = (4/h^2) \sin^2(i \pi h / 2)$, so this condition is
$\Delta t \nu \mu_{\max} < 2$. The condition $\Delta t \le h^2/(2\nu)$ is sufficient for it, but it
is not necessary. Backward Euler is unconditionally asymptotically stable. Exercise 1 of Chapter 13
gives the accuracy: the local truncation error of the $\theta$-method is $O(\Delta t + h^2)$ in
general and $O(\Delta t^2 + h^2)$ for $\theta = 1/2$. The proofs specialize the backbone modules
`Numlib.FiniteDifference.Parabolic` and `Numlib.LinearAlgebra.Matrix.TridiagonalToeplitz` to the
mass matrix $I$ and the stiffness matrix $\nu A_{fd}$, and use the Taylor bounds of
`Numlib.FiniteDifference.Hyperbolic`.

## Main definitions

* (12.8), `QuarteroniSaccoSaleri.Chapter13.laplacianFD`: the finite difference matrix $A_{fd} =
  h^{-2} \operatorname{tridiag}(-1, 2, -1)$.
* (13.8), `QuarteroniSaccoSaleri.Chapter13.equation_13_8`: the semi-discrete system
  $\dot u = -\nu A_{fd} u + f$, $u(0) = u_0$.
* (13.10), `QuarteroniSaccoSaleri.Chapter13.equation_13_10`: one step of the $\theta$-method for
  (13.8).
* Section 13.2, `QuarteroniSaccoSaleri.Chapter13.laplacianFDMaxEigenvalue`: the largest eigenvalue
  $\mu_{\max}$ of $A_{fd}$.

## Main results

* (13.8), `QuarteroniSaccoSaleri.Chapter13.equation_13_8_iff`: the system (13.8) in the normal form
  $\dot u = -\nu A_{fd} u + f$.
* (13.9)–(13.10), `QuarteroniSaccoSaleri.Chapter13.equation_13_9_iff`: the implicit recursion (13.9)
  and the explicit step (13.10) are the same.
* Section 13.2, `QuarteroniSaccoSaleri.Chapter13.equation_13_11_iterate`: the forward Euler iterates
  are $u^k = (I - \nu \Delta t A_{fd})^k u^0$.
* (13.11), `QuarteroniSaccoSaleri.Chapter13.equation_13_11`: the iterates tend to zero for every
  datum if and only if $\rho(I - \nu \Delta t A_{fd}) < 1$.
* Section 13.2, `QuarteroniSaccoSaleri.Chapter13.laplacianFD_hasEigenvalue_iff`: the eigenvalues of
  $A_{fd}$ are $(4/h^2) \sin^2(i \pi h / 2)$, $i = 1, \ldots, n - 1$.
* Section 13.2, `QuarteroniSaccoSaleri.Chapter13.equation_13_11_iff`:
  $\rho(I - \nu \Delta t A_{fd}) < 1$ if and only if $\Delta t \nu \mu_{\max} < 2$.
* Section 13.2, `QuarteroniSaccoSaleri.Chapter13.equation_13_11_of_le`: $\Delta t \le h^2/(2\nu)$
  implies asymptotic stability of forward Euler.
* Section 13.2, `QuarteroniSaccoSaleri.Chapter13.backwardEuler_tendsto`: backward Euler is
  asymptotically stable for all $\nu, \Delta t > 0$.
* Exercise 1 of Chapter 13, `QuarteroniSaccoSaleri.Chapter13.exercise_13_1`: the local truncation
  error of the $\theta$-method is $O(\Delta t + \Delta x^2)$, and $O(\Delta t^2 + \Delta x^2)$ for
  $\theta = 1/2$.

## Conventions

* The grid has $n$ subintervals and $h = 1/n$. The unknown vector has one component for each
  interior node and is indexed by `Fin (n - 1)`. The statements are written with $n$, and $n = 1/h$;
  each doc comment gives the statement in terms of $h$.

## Implementation notes

* The $\theta$-method is a function of the previous iterate, not a relation, because for the mass
  matrix $I$ the system matrix $I + \nu \theta \Delta t A_{fd}$ is always invertible.
* The local truncation error estimate is a Taylor estimate in one variable in each direction, over
  the interface `HasPartialDerivs` of `Numlib.Analysis.Calculus.PartialDeriv`. Section 13.8 uses the
  same method for the schemes for hyperbolic equations.

## Deviations from the source

* **Equations (13.8)–(13.11)** (reading). The semidiscrete equation uses within derivatives on a
  closed finite time interval. The $\theta$-step is a total one-step map using matrix inverse,
  and equivalence with the difference equation is proved for $\theta\ge0$, positive diffusion,
  and positive time step. The homogeneous spectral-radius criterion explicitly quantifies over
  all initial vectors. See `QuarteroniSaccoSaleri.Chapter13.equation_13_8_iff` and
  `QuarteroniSaccoSaleri.Chapter13.equation_13_11`.
* **Exercise 13.1** (reading). The residual is that of the space-time heat scheme, as indicated
  by the $h^2$ term in the exercise. The bound supplies explicit constants under global fourth-
  order derivative bounds. See `QuarteroniSaccoSaleri.Chapter13.exercise_13_1`.
* **Stability condition after (13.11)** (correction). The source states that forward Euler is
  asymptotically stable if and only if $\Delta t < h^2/(2\nu)$. This condition is sufficient but not
  necessary; the exact condition is $\Delta t \nu \mu_{\max} < 2$ with $\mu_{\max} < 4/h^2$. See
  `QuarteroniSaccoSaleri.Chapter13.equation_13_11_of_le` and
  `QuarteroniSaccoSaleri.Chapter13.equation_13_11_iff`.
-/

open Set Filter Topology FiniteDifference
open scoped Real Matrix

namespace QuarteroniSaccoSaleri.Chapter13

variable {n : ℕ}

/-! ### The finite difference Laplacian and the semi-discrete system (13.8) -/

/-- **Equation (12.8)** of [quarteroni2000numerical], as used in (13.8). Let $n \in \mathbb{N}$ and
$h = 1/n$. The **finite difference Laplacian** on the uniform grid $x_i = ih$ of $[0, 1]$ is the
matrix of order $n - 1$
$$A_{fd} = h^{-2} \operatorname{tridiag}(-1, 2, -1),$$
with $2/h^2$ on the diagonal, $-1/h^2$ on the two off-diagonals, and $0$ elsewhere.

The definition is $n^2$ times `Matrix.symmTridiagonalToeplitz (n - 1) (-1) 2`.

**Reading.** The matrix definition also gives the empty matrix at $n=0$. -/
noncomputable def laplacianFD (n : ℕ) : Matrix (Fin (n - 1)) (Fin (n - 1)) ℝ :=
  ((n : ℝ) ^ 2) • Matrix.symmTridiagonalToeplitz (n - 1) (-1) 2

/-- Let $n \ge 1$. The matrix $A_{fd}$ is symmetric positive definite. -/
theorem posDef_laplacianFD (hn : 0 < n) : (laplacianFD n).PosDef := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  exact (Matrix.posDef_symmTridiagonalToeplitz_neg_one_two (n - 1)).smul (pow_pos hn' 2)

/-- Let $n \ge 1$ and $\nu > 0$. The stiffness matrix $\nu A_{fd}$ of (13.8) is symmetric positive
definite. -/
theorem posDef_smul_laplacianFD (hn : 0 < n) {ν : ℝ} (hν : 0 < ν) : (ν • laplacianFD n).PosDef :=
  (posDef_laplacianFD hn).smul hν

/-- Let $n \ge 1$ and $\nu > 0$. Then $x^T (\nu A_{fd}) x \ge 0$ for every $x \in \mathbb{R}^{n-1}$.
This is the hypothesis under which the system matrix of the $\theta$-method is invertible. -/
theorem dotProduct_mulVec_smul_laplacianFD_nonneg (hn : 0 < n) {ν : ℝ} (hν : 0 < ν)
    (x : Fin (n - 1) → ℝ) : 0 ≤ x ⬝ᵥ ((ν • laplacianFD n) *ᵥ x) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have h : 0 < x ⬝ᵥ ((ν • laplacianFD n) *ᵥ x) := by
      simpa using (posDef_smul_laplacianFD hn hν).dotProduct_mulVec_pos hx
    exact h.le

/-- **Equation (13.8)** of [quarteroni2000numerical], the semi-discrete heat equation. Let
$n \in \mathbb{N}$, $\nu, T \in \mathbb{R}$, $f : \mathbb{R} \to \mathbb{R}^{n-1}$ and
$u_0 \in \mathbb{R}^{n-1}$. A function $u : \mathbb{R} \to \mathbb{R}^{n-1}$ solves the system
$$\dot u(t) + \nu A_{fd} u(t) = f(t), \quad t \in [0, T], \qquad u(0) = u_0,$$
if $u(0) = u_0$ and $u$ has a derivative $\dot u$ within $[0, T]$ at every point of $[0, T]$
that satisfies the equation. This is the system of ordinary differential equations that the
three-point discretization in space leaves.

The definition is `FiniteDifference.IsSemidiscrete` with the mass matrix $I$ and the stiffness
matrix $\nu A_{fd}$.

**Reading.** The system is stated on a closed finite time interval with vector inputs for the
sampled data. -/
def equation_13_8 (n : ℕ) (ν T : ℝ) (f : ℝ → Fin (n - 1) → ℝ) (u₀ : Fin (n - 1) → ℝ)
    (u : ℝ → Fin (n - 1) → ℝ) : Prop :=
  FiniteDifference.IsSemidiscrete 1 (ν • laplacianFD n) f u₀ T u

/-- **Equation (13.8)** of [quarteroni2000numerical], normal form. Let $\nu, T \in \mathbb{R}$,
$f : \mathbb{R} \to \mathbb{R}^{n-1}$, $u_0 \in \mathbb{R}^{n-1}$ and
$u : \mathbb{R} \to \mathbb{R}^{n-1}$. Then $u$ solves (13.8) if and only if $u(0) = u_0$ and
there is a function $\dot u$ such that, for every $t \in [0, T]$, $\dot u(t)$ is the derivative
of $u$ within $[0, T]$ at $t$ and
$$\dot u(t) = -\nu A_{fd} u(t) + f(t).$$

**Reading.** Equivalent normal form with within derivatives at both endpoints.
-/
theorem equation_13_8_iff (ν T : ℝ) (f : ℝ → Fin (n - 1) → ℝ) (u₀ : Fin (n - 1) → ℝ)
    (u : ℝ → Fin (n - 1) → ℝ) :
    equation_13_8 n ν T f u₀ u ↔
      u 0 = u₀ ∧ ∃ u' : ℝ → Fin (n - 1) → ℝ, ∀ t ∈ Icc 0 T,
        HasDerivWithinAt u (u' t) (Icc 0 T) t ∧
          u' t = -((ν • laplacianFD n) *ᵥ u t) + f t := by
  refine and_congr Iff.rfl (exists_congr fun u' => forall_congr' fun t => imp_congr_right fun _ =>
    and_congr_right fun _ => ?_)
  rw [Matrix.one_mulVec]
  constructor
  · intro h; rw [← h]; abel
  · intro h; rw [h]; abel

/-! ### The $\theta$-method (13.9)–(13.10) -/

/-- **Equation (13.10)** of [quarteroni2000numerical], one step of the $\theta$-method for (13.8).
Let $n \in \mathbb{N}$ and $\nu, \theta, \Delta t \in \mathbb{R}$. For the old iterate $u^k$ and
the source values $f^k$ and $f^{k+1}$, the new iterate is
$$u^{k+1} = (I + \nu \theta \Delta t A_{fd})^{-1} \bigl((I - \nu (1 - \theta) \Delta t A_{fd})
  u^k + \Delta t (\theta f^{k+1} + (1 - \theta) f^k)\bigr).$$

The definition is `FiniteDifference.thetaStep` with the mass matrix $I$ and the stiffness matrix
$\nu A_{fd}$. The arguments `f₀`, `f₁` and `u` are $f^k$, $f^{k+1}$ and $u^k$. If the system
matrix is singular, the Lean inverse is $0$; this does not happen under the hypotheses of
`QuarteroniSaccoSaleri.Chapter13.equation_13_9_iff`.

**Reading.** This is one update using total matrix inversion. The initial value is supplied
separately. -/
noncomputable def equation_13_10 (n : ℕ) (ν θ Δt : ℝ) (f₀ f₁ u : Fin (n - 1) → ℝ) :
    Fin (n - 1) → ℝ :=
  FiniteDifference.thetaStep 1 (ν • laplacianFD n) θ Δt f₀ f₁ u

/-- **Equations (13.9) and (13.10)** of [quarteroni2000numerical], equivalence. Let $n \ge 1$,
$\nu > 0$, $\theta \ge 0$ and $\Delta t > 0$, and let $f^k, f^{k+1}, u^k, u^{k+1} \in
\mathbb{R}^{n-1}$. Then $u^{k+1}$ is the $\theta$-step (13.10) of $u^k$ if and only if
$$\frac{u^{k+1} - u^k}{\Delta t} = -\nu A_{fd} \bigl(\theta u^{k+1} + (1 - \theta) u^k\bigr) +
  \theta f^{k+1} + (1 - \theta) f^k,$$
which is the recursion (13.9).

The system matrix $I + \nu \theta \Delta t A_{fd}$ is invertible because $A_{fd}$ is positive
definite.

**Generalization.** The one-step equivalence permits all $\theta\ge0$ under positive diffusion
and time step. -/
theorem equation_13_9_iff (hn : 0 < n) {ν θ Δt : ℝ} (hν : 0 < ν) (hθ : 0 ≤ θ) (hΔt : 0 < Δt)
    (f₀ f₁ u u' : Fin (n - 1) → ℝ) :
    u' = equation_13_10 n ν θ Δt f₀ f₁ u ↔
      Δt⁻¹ • (u' - u)
        = -((ν • laplacianFD n) *ᵥ (θ • u' + (1 - θ) • u)) + (θ • f₁ + (1 - θ) • f₀) := by
  have hK : IsUnit ((1 : Matrix (Fin (n - 1)) (Fin (n - 1)) ℝ) + (θ * Δt) • (ν • laplacianFD n)) :=
    FiniteDifference.isUnit_add_smul_of_posDef Matrix.PosDef.one
      (dotProduct_mulVec_smul_laplacianFD_nonneg hn hν) (mul_nonneg hθ hΔt.le)
  rw [equation_13_10, FiniteDifference.eq_thetaStep_iff_divided hK hΔt.ne', Matrix.one_mulVec]
  constructor
  · intro h; rw [← h]; abel
  · intro h; rw [h]; abel

/-! ### Asymptotic stability (13.11) -/

/-- For $\nu, \Delta t \in \mathbb{R}$, the amplification matrix
`FiniteDifference.thetaAmplification` of forward Euler ($\theta = 0$) with the mass matrix $I$
and the stiffness matrix $\nu A_{fd}$ is $I - \nu \Delta t A_{fd}$.

**Reading.** Same amplification matrix defined for arbitrary real ν and Δt.
-/
theorem thetaAmplification_forwardEuler (ν Δt : ℝ) :
    FiniteDifference.thetaAmplification (1 : Matrix (Fin (n - 1)) (Fin (n - 1)) ℝ)
        (ν • laplacianFD n) 0 Δt = 1 - (ν * Δt) • laplacianFD n := by
  rw [FiniteDifference.thetaAmplification]
  simp [smul_smul, mul_comm]

/-- **Section 13.2** of [quarteroni2000numerical], the forward Euler iterates (the display before
(13.11)). Let $\nu, \Delta t \in \mathbb{R}$ and $u^0 \in \mathbb{R}^{n-1}$. For $\theta = 0$
and $f = 0$, the $k$-th iterate of the step (13.10) is
$$u^k = (I - \nu \Delta t A_{fd})^k u^0.$$

**Reading.** Same homogeneous iteration for all real ν and Δt and k including zero.
-/
theorem equation_13_11_iterate (ν Δt : ℝ) (u₀ : Fin (n - 1) → ℝ) (k : ℕ) :
    (fun u => equation_13_10 n ν 0 Δt 0 0 u)^[k] u₀
      = ((1 - (ν * Δt) • laplacianFD n) ^ k) *ᵥ u₀ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, equation_13_10,
      FiniteDifference.thetaStep_zero_zero, thetaAmplification_forwardEuler,
      Matrix.mulVec_mulVec, ← pow_succ']

/-- **Equation (13.11)** of [quarteroni2000numerical]. Let $\nu, \Delta t \in \mathbb{R}$. The
forward Euler iterates $(I - \nu \Delta t A_{fd})^k u^0$ tend to $0$ as $k \to \infty$ for every
$u^0 \in \mathbb{R}^{n-1}$ if and only if
$$\rho(I - \nu \Delta t A_{fd}) < 1.$$

The spectral radius $\rho$ is computed over $\mathbb{C}$, by `Matrix.complexSpectralRadius`.

**Reading.** The asymptotic stability criterion is for convergence from every initial vector.
The matrix equivalence admits arbitrary real coefficients. -/
theorem equation_13_11 (ν Δt : ℝ) :
    (∀ u₀ : Fin (n - 1) → ℝ,
        Tendsto (fun k : ℕ => ((1 - (ν * Δt) • laplacianFD n) ^ k) *ᵥ u₀) atTop (𝓝 0)) ↔
      Matrix.complexSpectralRadius (1 - (ν * Δt) • laplacianFD n) < 1 :=
  (Matrix.tendsto_pow_zero_iff_forall_mulVec _).symm.trans
    (Matrix.tendsto_pow_iff_complexSpectralRadius_lt_one _)

/-- **Section 13.2** of [quarteroni2000numerical], the eigenvalues of $A_{fd}$ (the display after
(13.11)). Let $n \ge 1$ and $h = 1/n$. A real number $\mu$ is an eigenvalue of $A_{fd}$ if and
only if
$$\mu = \frac{4}{h^2} \sin^2\Bigl(\frac{i \pi h}{2}\Bigr) \quad \text{for some } i \in \{1,
  \ldots, n - 1\}.$$

This is also Exercise 3 of Chapter 12. In Lean the index `i : Fin (n - 1)` stands for $i + 1$,
and the formula is $4 n^2 \sin^2((i + 1) \pi / (2n))$. -/
theorem laplacianFD_hasEigenvalue_iff (hn : 0 < n) (μ : ℝ) :
    Module.End.HasEigenvalue (Matrix.toEuclideanLin (laplacianFD n)) μ ↔
      ∃ i : Fin (n - 1),
        μ = 4 * (n : ℝ) ^ 2 * Real.sin ((((i : ℕ) : ℝ) + 1) * π / (2 * n)) ^ 2 := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hcast : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
    have h1 : (1 : ℕ) ≤ n := hn
    push_cast [h1]
    ring
  rw [Matrix.hasEigenvalue_toEuclideanLin_iff, laplacianFD,
    FiniteDifference.mem_spectrum_smul_symmTridiagonalToeplitz_iff (pow_pos hn' 2) μ]
  refine exists_congr fun k => ?_
  rw [hcast]
  exact ⟨fun h => by rw [h]; ring, fun h => by rw [h]; ring⟩

/-- **Section 13.2** of [quarteroni2000numerical], the largest eigenvalue of $A_{fd}$. For
$n \in \mathbb{N}$ and $h = 1/n$, it is
$$\mu_{\max} = \frac{4}{h^2} \sin^2\Bigl(\frac{(n - 1) \pi h}{2}\Bigr).$$

The definition is $4 n^2 \sin^2((n - 1) \pi / (2n))$. At $n = 0$ it is $0$.

**Reading.** At $n=1$ the empty interior matrix is assigned the sentinel value zero. -/
noncomputable def laplacianFDMaxEigenvalue (n : ℕ) : ℝ :=
  4 * (n : ℝ) ^ 2 * Real.sin (((n : ℝ) - 1) * π / (2 * n)) ^ 2

/-- Let $n \ge 1$ and $h = 1/n$. The largest eigenvalue of $A_{fd}$ satisfies $\mu_{\max} < 4/h^2$,
because $\sin((n - 1) \pi h / 2) < 1$. -/
theorem laplacianFDMaxEigenvalue_lt (hn : 0 < n) :
    laplacianFDMaxEigenvalue n < 4 * (n : ℝ) ^ 2 := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  set x : ℝ := ((n : ℝ) - 1) * π / (2 * n) with hx
  have hxlt : x < π / 2 := by
    rw [hx, div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [Real.pi_pos]
  have hx0 : 0 ≤ x := by
    have hnum : (0 : ℝ) ≤ ((n : ℝ) - 1) * π := by nlinarith [Real.pi_pos]
    rw [hx]
    positivity
  have hcos : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hxlt⟩
  have hsq : Real.sin x ^ 2 < 1 := by nlinarith [Real.sin_sq_add_cos_sq x]
  have hpos : (0 : ℝ) < 4 * (n : ℝ) ^ 2 := by nlinarith [pow_pos hn' 2]
  rw [laplacianFDMaxEigenvalue, ← hx]
  linarith [mul_lt_mul_of_pos_left hsq hpos]

/-- Let $n \ge 1$, $h = 1/n$ and $\nu, \Delta t \in \mathbb{R}$. Then
$$\nu \Delta t A_{fd} = \Delta t \Bigl(\frac{\nu}{h^2} \operatorname{tridiag}(-1, 2,
  -1)\Bigr).$$
This writes the iteration matrix of forward Euler in the form that the backbone stability
theorem uses. -/
theorem smul_laplacianFD_eq (hn : 0 < n) (ν Δt : ℝ) :
    (ν * Δt) • laplacianFD n
      = Δt • ((ν / ((1 : ℝ) / n) ^ 2) • Matrix.symmTridiagonalToeplitz (n - 1) (-1) 2) := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [laplacianFD, smul_smul, smul_smul]
  congr 1
  field_simp

/-- **Section 13.2** of [quarteroni2000numerical], the exact stability condition for forward Euler.
Let $n \ge 1$, $\nu > 0$ and $\Delta t > 0$, and let $\mu_{\max}$ be the largest eigenvalue of
$A_{fd}$. Then
$$\rho(I - \nu \Delta t A_{fd}) < 1 \iff \Delta t\, \nu\, \mu_{\max} < 2.$$

**Correction.** Corrects alleged iff using the exact finite-grid eigenvalue.
-/
theorem equation_13_11_iff (hn : 0 < n) {ν Δt : ℝ} (hν : 0 < ν) (hΔt : 0 < Δt) :
    Matrix.complexSpectralRadius (1 - (ν * Δt) • laplacianFD n) < 1 ↔
      Δt * (ν * laplacianFDMaxEigenvalue n) < 2 := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hh : (0 : ℝ) < 1 / (n : ℝ) := by positivity
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    have h1 : (1 : ℕ) ≤ n := hn
    push_cast [h1]
    ring
  have heq : Δt * (4 * ν / ((1 : ℝ) / n) ^ 2 *
        Real.sin (((n : ℝ) - 1) * π / (2 * ((n : ℝ) - 1 + 1))) ^ 2)
      = Δt * (ν * laplacianFDMaxEigenvalue n) := by
    rw [laplacianFDMaxEigenvalue, show (2 : ℝ) * ((n : ℝ) - 1 + 1) = 2 * n by ring]
    field_simp
  rw [← equation_13_11, smul_laplacianFD_eq hn,
    FiniteDifference.forwardEuler_heat_tendsto_iff (n - 1) hν hh hΔt, hcast, heq]

/-- **Section 13.2** of [quarteroni2000numerical], the stability condition $\Delta t < h^2/(2\nu)$.
Let $n \ge 1$, $h = 1/n$, $\nu > 0$ and $0 < \Delta t \le h^2/(2\nu)$. Then for every
$u^0 \in \mathbb{R}^{n-1}$ the forward Euler iterates tend to zero:
$$(I - \nu \Delta t A_{fd})^k u^0 \to 0 \quad (k \to \infty).$$

**Correction.** The source states that forward Euler is asymptotically stable if and only if
$\Delta t < h^2/(2\nu)$. The condition is sufficient, even with equality, but it is not
necessary. The exact condition is $\Delta t < 2/(\nu \mu_{\max})$ (see
`QuarteroniSaccoSaleri.Chapter13.equation_13_11_iff`), and $\mu_{\max} < 4/h^2$ strictly (see
`QuarteroniSaccoSaleri.Chapter13.laplacianFDMaxEigenvalue_lt`), so the exact threshold is
slightly larger than $h^2/(2\nu)$.

The hypothesis is written as $\Delta t \le 1/(2 \nu n^2)$. -/
theorem equation_13_11_of_le (hn : 0 < n) {ν Δt : ℝ} (hν : 0 < ν) (hΔt : 0 < Δt)
    (hle : Δt ≤ 1 / (2 * ν * (n : ℝ) ^ 2)) (u₀ : Fin (n - 1) → ℝ) :
    Tendsto (fun k : ℕ => ((1 - (ν * Δt) • laplacianFD n) ^ k) *ᵥ u₀) atTop (𝓝 0) := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hh : (0 : ℝ) < 1 / (n : ℝ) := by positivity
  have hle' : Δt ≤ ((1 : ℝ) / n) ^ 2 / (2 * ν) := by
    have hfa : ((1 : ℝ) / n) ^ 2 / (2 * ν) = 1 / (2 * ν * (n : ℝ) ^ 2) := by
      field_simp
    rw [hfa]
    exact hle
  rw [smul_laplacianFD_eq hn]
  exact FiniteDifference.forwardEuler_heat_tendsto_of_le (n - 1) hν hh hΔt hle' u₀

/-- **Section 13.2** of [quarteroni2000numerical], backward Euler (the display after (13.11)). Let
$n \ge 1$, $\nu > 0$ and $\Delta t > 0$. Then for every $u^0 \in \mathbb{R}^{n-1}$ the backward
Euler iterates tend to zero:
$$\bigl((I + \nu \Delta t A_{fd})^{-1}\bigr)^k u^0 \to 0 \quad (k \to \infty).$$
So backward Euler is unconditionally asymptotically stable. The eigenvalues
$1/(1 + \nu \Delta t \mu_i)$ of the iteration matrix lie in $(0, 1)$. -/
theorem backwardEuler_tendsto (hn : 0 < n) {ν Δt : ℝ} (hν : 0 < ν) (hΔt : 0 < Δt)
    (u₀ : Fin (n - 1) → ℝ) :
    Tendsto (fun k : ℕ => (((1 + (ν * Δt) • laplacianFD n)⁻¹) ^ k) *ᵥ u₀) atTop (𝓝 0) := by
  have h := FiniteDifference.backwardEuler_tendsto (M := 1) (A := ν • laplacianFD n)
    Matrix.PosDef.one (posDef_smul_laplacianFD hn hν) hΔt u₀
  have hamp : FiniteDifference.thetaAmplification (1 : Matrix (Fin (n - 1)) (Fin (n - 1)) ℝ)
      (ν • laplacianFD n) 1 Δt = (1 + (ν * Δt) • laplacianFD n)⁻¹ := by
    rw [FiniteDifference.thetaAmplification]
    simp [smul_smul, mul_comm]
  rwa [hamp] at h

/-! ### Exercise 1 of Chapter 13: the accuracy of the $\theta$-method -/

/-- **Exercise 1 of Chapter 13** of [quarteroni2000numerical], the local truncation error of the
$\theta$-method. Section 13.2 cites it for the claim that the local truncation error is of the
order of $\Delta t + h^2$ if $\theta \neq 1/2$, and of the order of $\Delta t^2 + h^2$ if
$\theta = 1/2$. Let $u, f : \mathbb{R}^2 \to \mathbb{R}$, where $u$ has iterated partial
derivatives $D_{ij} = \partial_x^i \partial_t^j u$ of all orders, and $u_t - \nu u_{xx} = f$ on
all of $\mathbb{R}^2$. Let $\nu, \theta, M \in \mathbb{R}$, with $|D_{ij}| \le M$ on
$\mathbb{R}^2$ for all $i + j \le 4$. Let $0 < \Delta t \le 1$ and $\Delta x > 0$, and write
$\delta_x^2 v(x) = (v(x + \Delta x) - 2 v(x) + v(x - \Delta x)) / \Delta x^2$. For
$x, t \in \mathbb{R}$, let $R$ be the residual of the $\theta$-scheme (13.9) at the node
$(x, t)$:
$$R = \frac{u(x, t + \Delta t) - u(x, t)}{\Delta t} - \nu \bigl[\theta \delta_x^2 u(x, t +
  \Delta t) + (1 - \theta) \delta_x^2 u(x, t)\bigr] - \bigl[\theta f(x, t + \Delta t) + (1 -
  \theta) f(x, t)\bigr].$$
Then
$$|R| \le M \Bigl(\frac{1}{2} + \frac{3 |\theta|}{2}\Bigr) \Delta t + |\nu| (|\theta| + |1 -
  \theta|) \frac{M}{12} \Delta x^2,$$
and for $\theta = 1/2$
$$|R| \le \frac{5}{12} M \Delta t^2 + |\nu| \frac{M}{12} \Delta x^2.$$

The family $D$ is `HasPartialDerivs u D`. The proof splits $R$ into a time part and a space
part. The heat equation at the two time levels turns the source terms into $\nu$ times the
defects $\delta_x^2 u - u_{xx}$, which are $O(\Delta x^2)$ by
`FiniteDifference.Hyperbolic.abs_secondDiff_fst_sub_le`. The time part is $O(\Delta t)$ in
general, and for $\theta = 1/2$ it is the defect of the trapezoidal rule, $O(\Delta t^2)$.

**Reading.** The exercise mentions the scalar Cauchy problem but its requested $h^2$ term is
spatial. The statement analyzes the full heat-scheme residual under explicit global smoothness
and derivative bounds. -/
theorem exercise_13_1 {u f : ℝ → ℝ → ℝ} {D : ℕ → ℕ → ℝ → ℝ → ℝ} {ν θ M Δt Δx : ℝ}
    (hD : HasPartialDerivs u D) (hΔt : 0 < Δt) (hΔt1 : Δt ≤ 1) (hΔx : 0 < Δx)
    (hheat : ∀ y s, D 0 1 y s - ν * D 2 0 y s = f y s)
    (hM : ∀ i j, i + j ≤ 4 → ∀ y s, |D i j y s| ≤ M) (x t : ℝ) :
    |(u x (t + Δt) - u x t) / Δt
          - ν * (θ * ((u (x + Δx) (t + Δt) - 2 * u x (t + Δt) + u (x - Δx) (t + Δt)) / Δx ^ 2)
            + (1 - θ) * ((u (x + Δx) t - 2 * u x t + u (x - Δx) t) / Δx ^ 2))
          - (θ * f x (t + Δt) + (1 - θ) * f x t)|
        ≤ M * (1 / 2 + 3 / 2 * |θ|) * Δt + |ν| * (|θ| + |1 - θ|) * M / 12 * Δx ^ 2 ∧
      |(u x (t + Δt) - u x t) / Δt
          - ν * (1 / 2 * ((u (x + Δx) (t + Δt) - 2 * u x (t + Δt) + u (x - Δx) (t + Δt)) / Δx ^ 2)
            + (1 - 1 / 2) * ((u (x + Δx) t - 2 * u x t + u (x - Δx) t) / Δx ^ 2))
          - (1 / 2 * f x (t + Δt) + (1 - 1 / 2) * f x t)|
        ≤ 5 / 12 * M * Δt ^ 2 + |ν| * M / 12 * Δx ^ 2 := by
  have hu : D 0 0 = u := hD.eq_zero_zero
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 0 (by norm_num) x t)
  have hEp : |(u (x + Δx) (t + Δt) - 2 * u x (t + Δt) + u (x - Δx) (t + Δt)) / Δx ^ 2
      - D 2 0 x (t + Δt)| ≤ M * Δx ^ 2 / 12 := by
    have h := Hyperbolic.abs_secondDiff_fst_sub_le (i := 0) (j := 0) hD
      (hM 4 0 (by norm_num)) hΔx x (t + Δt)
    rwa [hu] at h
  have hE0 : |(u (x + Δx) t - 2 * u x t + u (x - Δx) t) / Δx ^ 2 - D 2 0 x t|
      ≤ M * Δx ^ 2 / 12 := by
    have h := Hyperbolic.abs_secondDiff_fst_sub_le (i := 0) (j := 0) hD
      (hM 4 0 (by norm_num)) hΔx x t
    rwa [hu] at h
  have hT1 : |u x (t + Δt) - u x t - Δt * D 0 1 x t| ≤ M * Δt ^ 2 / 2 := by
    have h := Hyperbolic.abs_taylor_snd_one (i := 0) (j := 0) hD (hM 0 2 (by norm_num)) x t Δt
    rwa [hu] at h
  have hT2 : |D 0 1 x (t + Δt) - D 0 1 x t - Δt * D 0 2 x t| ≤ M * Δt ^ 2 / 2 :=
    Hyperbolic.abs_taylor_snd_one (i := 0) (j := 1) hD (hM 0 3 (by norm_num)) x t Δt
  have hT3 : |u x (t + Δt) - u x t - Δt * D 0 1 x t - Δt ^ 2 / 2 * D 0 2 x t|
      ≤ M * Δt ^ 3 / 6 := by
    have h := Hyperbolic.abs_taylor_snd_two (i := 0) (j := 0) hD (hM 0 3 (by norm_num)) x t Δt
    rw [hu, abs_of_pos hΔt] at h
    exact h
  have hD02 : |D 0 2 x t| ≤ M := hM 0 2 (by norm_num) x t
  have hsplit : ∀ c : ℝ, (u x (t + Δt) - u x t) / Δt
        - ν * (c * ((u (x + Δx) (t + Δt) - 2 * u x (t + Δt) + u (x - Δx) (t + Δt)) / Δx ^ 2)
          + (1 - c) * ((u (x + Δx) t - 2 * u x t + u (x - Δx) t) / Δx ^ 2))
        - (c * f x (t + Δt) + (1 - c) * f x t)
      = ((u x (t + Δt) - u x t) / Δt - c * D 0 1 x (t + Δt) - (1 - c) * D 0 1 x t)
        - ν * (c * ((u (x + Δx) (t + Δt) - 2 * u x (t + Δt) + u (x - Δx) (t + Δt)) / Δx ^ 2
              - D 2 0 x (t + Δt))
          + (1 - c) * ((u (x + Δx) t - 2 * u x t + u (x - Δx) t) / Δx ^ 2 - D 2 0 x t)) := by
    intro c
    rw [← hheat x (t + Δt), ← hheat x t]
    ring
  have hspace : ∀ c : ℝ, |ν * (c * ((u (x + Δx) (t + Δt) - 2 * u x (t + Δt)
        + u (x - Δx) (t + Δt)) / Δx ^ 2 - D 2 0 x (t + Δt))
      + (1 - c) * ((u (x + Δx) t - 2 * u x t + u (x - Δx) t) / Δx ^ 2 - D 2 0 x t))|
      ≤ |ν| * (|c| + |1 - c|) * M / 12 * Δx ^ 2 := by
    intro c
    rw [abs_mul]
    have hb : |c * ((u (x + Δx) (t + Δt) - 2 * u x (t + Δt) + u (x - Δx) (t + Δt)) / Δx ^ 2
          - D 2 0 x (t + Δt))
        + (1 - c) * ((u (x + Δx) t - 2 * u x t + u (x - Δx) t) / Δx ^ 2 - D 2 0 x t)|
        ≤ (|c| + |1 - c|) * M / 12 * Δx ^ 2 := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul]
      have h1 := mul_le_mul_of_nonneg_left hEp (abs_nonneg c)
      have h2 := mul_le_mul_of_nonneg_left hE0 (abs_nonneg (1 - c))
      nlinarith [h1, h2]
    exact (mul_le_mul_of_nonneg_left hb (abs_nonneg ν)).trans (le_of_eq (by ring))
  constructor
  · rw [hsplit θ]
    refine (abs_sub _ _).trans (add_le_add ?_ (hspace θ))
    have hA : (u x (t + Δt) - u x t) / Δt - θ * D 0 1 x (t + Δt) - (1 - θ) * D 0 1 x t
        = ((u x (t + Δt) - u x t - Δt * D 0 1 x t) / Δt)
          - θ * (D 0 1 x (t + Δt) - D 0 1 x t) := by
      field_simp
      ring
    rw [hA]
    have hq1 : |(u x (t + Δt) - u x t - Δt * D 0 1 x t) / Δt| ≤ M * Δt / 2 := by
      rw [abs_div, abs_of_pos hΔt, div_le_iff₀ hΔt]
      nlinarith [hT1]
    have hq2 : |D 0 1 x (t + Δt) - D 0 1 x t| ≤ 3 / 2 * (M * Δt) := by
      have h := (abs_add_le (D 0 1 x (t + Δt) - D 0 1 x t - Δt * D 0 2 x t) (Δt * D 0 2 x t)).trans
        (add_le_add hT2 (le_of_eq (abs_mul Δt (D 0 2 x t))))
      have h2 : |Δt| * |D 0 2 x t| ≤ Δt * M := by
        rw [abs_of_pos hΔt]
        exact mul_le_mul_of_nonneg_left hD02 hΔt.le
      have h3 : |D 0 1 x (t + Δt) - D 0 1 x t| ≤ M * Δt ^ 2 / 2 + |Δt| * |D 0 2 x t| := by
        have he : D 0 1 x (t + Δt) - D 0 1 x t - Δt * D 0 2 x t + Δt * D 0 2 x t
            = D 0 1 x (t + Δt) - D 0 1 x t := by ring
        rw [he] at h
        exact h
      nlinarith [h3, h2, mul_nonneg (mul_nonneg hM0 hΔt.le) (by linarith : (0 : ℝ) ≤ 1 - Δt)]
    have hq3 := mul_le_mul_of_nonneg_left hq2 (abs_nonneg θ)
    refine (abs_sub _ _).trans ?_
    rw [abs_mul]
    nlinarith [hq1, hq3]
  · rw [hsplit (1 / 2)]
    have hsp : |ν| * (|(1 : ℝ) / 2| + |1 - 1 / 2|) * M / 12 * Δx ^ 2 = |ν| * M / 12 * Δx ^ 2 := by
      rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2),
        abs_of_pos (by norm_num : (0 : ℝ) < 1 - 1 / 2)]
      ring
    refine (abs_sub _ _).trans (add_le_add ?_ (hsp ▸ hspace (1 / 2)))
    have hA : (u x (t + Δt) - u x t) / Δt - 1 / 2 * D 0 1 x (t + Δt) - (1 - 1 / 2) * D 0 1 x t
        = ((u x (t + Δt) - u x t - Δt * D 0 1 x t - Δt ^ 2 / 2 * D 0 2 x t)
            - Δt / 2 * (D 0 1 x (t + Δt) - D 0 1 x t - Δt * D 0 2 x t)) / Δt := by
      field_simp
      ring
    rw [hA, abs_div, abs_of_pos hΔt, div_le_iff₀ hΔt]
    have hb := (abs_sub _ _).trans (add_le_add hT3
      (le_of_eq (abs_mul (Δt / 2) (D 0 1 x (t + Δt) - D 0 1 x t - Δt * D 0 2 x t))))
    have hd : |Δt / 2| * |D 0 1 x (t + Δt) - D 0 1 x t - Δt * D 0 2 x t|
        ≤ Δt / 2 * (M * Δt ^ 2 / 2) := by
      rw [abs_div, abs_of_pos hΔt, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      exact mul_le_mul_of_nonneg_left hT2 (by positivity)
    nlinarith [hb, hd]

end QuarteroniSaccoSaleri.Chapter13
