/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Numlib.Analysis.ODE.Gronwall
import Numlib.Analysis.PDE.Heat.Energy
import NumlibSurface.QuarteroniSaccoSaleri.Chapter12.Section02

/-!
# Quarteroni, Sacco and Saleri, Section 13.1: The heat equation

This module formalizes Section 13.1 of [quarteroni2000numerical]. The initial boundary value problem
(13.1)–(13.4) is $u_t + Lu = f$ with $Lu = -\nu u_{xx}$ on $(0, 1) \times (0, T)$, the homogeneous
Dirichlet conditions $u(0, t) = u(1, t) = 0$ (13.2) and the initial datum $u(x, 0) = u_0(x)$ (13.3).
It is stated for classical solutions on the closed rectangle $[0, 1] \times [0, T]$. For $\nu = 1$,
$f = 0$ and a finite sine sum as datum, the separated solution (13.5)
$$u(x, t) = \sum_n c_n e^{-(n\pi)^2 t} \sin(n\pi x)$$
is a classical solution, and its coefficients are the sine coefficients
$c_n = 2 \int_0^1 u_0(x) \sin(n\pi x) \, dx$ of the datum. With the energy
$E(t) = \int_0^1 u(x, t)^2 \, dx$ and the source energy $F(t) = \int_0^1 f(x, t)^2 \, dx$, every
classical solution with $\nu > 0$ satisfies the a priori estimate (13.7)
$$E(t) \le e^{-\gamma t} E(0) + \frac{1}{\gamma} \int_0^t e^{\gamma(s - t)} F(s) \, ds, \qquad
  \gamma = \frac{\nu}{C_P^2} = 2\nu.$$
The proofs specialize `Numlib.Analysis.PDE.Heat.Energy`.

## Main definitions

* (13.1)–(13.4), `QuarteroniSaccoSaleri.Chapter13.IsHeatSolutionWith`: a classical solution with
  given partial derivatives.
* (13.1)–(13.4), `QuarteroniSaccoSaleri.Chapter13.IsHeatSolution`: a classical solution of the heat
  equation.
* (13.5), `QuarteroniSaccoSaleri.Chapter13.sineDatum`: the finite sine sum
  $\sum_{n < N} c_n \sin(n\pi x)$.
* (13.5), `QuarteroniSaccoSaleri.Chapter13.sineSolution`: the finite separated solution
  $\sum_{n < N} c_n e^{-(n\pi)^2 t} \sin(n\pi x)$.
* Section 13.1, `QuarteroniSaccoSaleri.Chapter13.energy`: the energy
  $E(t) = \int_0^1 u(x, t)^2 \, dx$.

## Main results

* (13.5), `QuarteroniSaccoSaleri.Chapter13.equation_13_5`: the finite separated solution is a
  classical solution.
* Section 13.1, `QuarteroniSaccoSaleri.Chapter13.integral_sin_mul_sin`: $\int_0^1 \sin(m\pi x)
  \sin(n\pi x) \, dx = \delta_{mn}/2$.
* (13.5), `QuarteroniSaccoSaleri.Chapter13.equation_13_5_coeff`: the coefficients are
  $c_n = 2 \int_0^1 u_0(x) \sin(n\pi x) \, dx$.
* (13.7), `QuarteroniSaccoSaleri.Chapter13.equation_13_7`: the a priori energy estimate.

## Proof outline

The proof of (13.7) follows the book: integration by parts in $x$, the Cauchy–Schwarz inequality,
the Poincaré inequality (12.16), the Young inequality (12.40) and the differential Gronwall lemma.
Two steps differ from the book. First, a classical solution is jointly continuous on the rectangle
(`Heat.IsClassicalSolutionIccWith.continuousOn`); the definition does not assume this, and the mean
value inequality gives it from the bounded partial derivatives. Second, the interchange of
differentiation and integration is done in integrated form: $E$ is shown to be a primitive by
Fubini's theorem (`Heat.IsClassicalSolutionIccWith.energy_sub_eq`), not differentiated under the
integral sign, because Mathlib's differentiation under the integral needs a two-sided derivative and
the estimate is needed from $t = 0$.

## Conventions

* A function of space and time is `u : ℝ → ℝ → ℝ`, written `u x t` with space first, as the book
  writes $u(x, t)$.
* A classical solution has the partial derivatives $u_t$, $u_x$, $u_{xx}$ at every point of
  $[0, 1] \times [0, T]$, one-sided at the edges, and they are continuous on the closed rectangle.
  This is what the book's derivation of the energy estimate uses. The derivatives are named in
  `QuarteroniSaccoSaleri.Chapter13.IsHeatSolutionWith` and quantified existentially in
  `QuarteroniSaccoSaleri.Chapter13.IsHeatSolution`.
* The source energy $F(t)$ is the energy of $f$, `QuarteroniSaccoSaleri.Chapter13.energy f t`.

## Deviations from the source

* **Equations (13.1)–(13.4)** (reading). The classical solution uses a closed finite time
  interval and requires continuous partial derivatives and the PDE on the closed spatial
  interval, including at time zero. See `QuarteroniSaccoSaleri.Chapter13.IsHeatSolutionWith`.
* **Equation (13.5)** (specialization). The initial data and solution are finite sine sums. The
  coefficient identity concerns the retained nonzero frequencies. See
  `QuarteroniSaccoSaleri.Chapter13.equation_13_5_coeff`.
* **Equation (13.7)** (specialization). The finite-time estimate uses $\gamma=2\nu$ for the
  Dirichlet problem. See `QuarteroniSaccoSaleri.Chapter13.equation_13_7`.

## Not formalized

* **(13.5) for a general initial datum.** Only finite sine sums are treated; the infinite series for
  a general datum is classical Fourier theory.
-/

open Set Filter Topology intervalIntegral
open scoped Real

namespace QuarteroniSaccoSaleri.Chapter13

/-! ### The classical Dirichlet problem (13.1)–(13.4) -/

/-- **Equations (13.1)–(13.4)** of [quarteroni2000numerical], with the derivatives named. The
function $u$ is a **classical solution** on $[0, 1] \times [0, T]$ with diffusivity $\nu$,
source $f$, initial datum $u_0$ and partial derivatives $u_t$, $u_x$, $u_{xx}$ if:

* at every $(x, t) \in [0, 1] \times [0, T]$, $u_t(x, t)$ is the derivative of $u(x, \cdot)$
  within $[0, T]$, $u_x(x, t)$ is the derivative of $u(\cdot, t)$ within $[0, 1]$,
  $u_{xx}(x, t)$ is the derivative of $u_x(\cdot, t)$ within $[0, 1]$, and
  $u_t - \nu u_{xx} = f$;
* $u_t$, $u_x$ and $u_{xx}$ are continuous on $[0, 1] \times [0, T]$;
* $u(0, t) = u(1, t) = 0$ for $t \in [0, T]$;
* $u(x, 0) = u_0(x)$ for $x \in [0, 1]$.

The derivatives within a closed interval are one-sided at its endpoints. The definition is
`Heat.IsClassicalSolutionIccWith`.

**Reading.** The PDE and derivative continuity are required on the closed rectangle, including
the spatial endpoints and initial time. -/
abbrev IsHeatSolutionWith (ν T : ℝ) (f : ℝ → ℝ → ℝ) (u₀ : ℝ → ℝ) (u ut ux uxx : ℝ → ℝ → ℝ) :
    Prop :=
  Heat.IsClassicalSolutionIccWith ν T f u₀ u ut ux uxx

/-- **Equations (13.1)–(13.4)** of [quarteroni2000numerical], the classical Dirichlet problem for
the heat equation. The function $u$ is a **classical solution** of $u_t - \nu u_{xx} = f$ on
$[0, 1] \times [0, T]$ with $u(0, t) = u(1, t) = 0$ and $u(x, 0) = u_0(x)$ if there are partial
derivatives $u_t$, $u_x$, $u_{xx}$ for which
`QuarteroniSaccoSaleri.Chapter13.IsHeatSolutionWith` holds.

The definition is `Heat.IsClassicalSolutionIcc`.

**Reading.** The closed-rectangle interpretation is
`QuarteroniSaccoSaleri.Chapter13.IsHeatSolutionWith` with existentially quantified derivatives. -/
abbrev IsHeatSolution (ν T : ℝ) (f : ℝ → ℝ → ℝ) (u₀ : ℝ → ℝ) (u : ℝ → ℝ → ℝ) : Prop :=
  Heat.IsClassicalSolutionIcc ν T f u₀ u

/-! ### The sine-series solution (13.5) -/

/-- **Equation (13.5)** of [quarteroni2000numerical], the initial datum. For $N \in \mathbb{N}$ and
coefficients $c_n$, the finite sine sum
$$u_0(x) = \sum_{n = 0}^{N - 1} c_n \sin(n\pi x).$$

The term $n = 0$ vanishes.

**Specialization.** The datum is assumed to be a finite sine expansion. -/
noncomputable def sineDatum (N : ℕ) (c : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range N, c k * Real.sin (k * π * x)

/-- **Equation (13.5)** of [quarteroni2000numerical], the separated solution. For $N \in \mathbb{N}$
and coefficients $c_n$, the finite sum
$$u(x, t) = \sum_{n = 0}^{N - 1} c_n e^{-(n\pi)^2 t} \sin(n\pi x).$$

**Specialization.** The source uses an infinite expansion. The sum here retains finitely many
terms and the zero-frequency term vanishes. -/
noncomputable def sineSolution (N : ℕ) (c : ℕ → ℝ) (x t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range N, c k * Real.exp (-((k : ℝ) * π) ^ 2 * t) * Real.sin (k * π * x)

/-- **Equation (13.5)** of [quarteroni2000numerical] for a finite sine datum. Let
$N \in \mathbb{N}$, let $c_n$ be real coefficients and let $T$ be real. Then $u(x, t) = \sum_{n
< N} c_n e^{-(n\pi)^2 t} \sin(n\pi x)$ is a classical solution of (13.1)–(13.4) on
$[0, 1] \times [0, T]$ with $\nu = 1$, $f = 0$ and the initial datum
$u_0(x) = \sum_{n < N} c_n \sin(n\pi x)$.

The book gives the infinite series for a general datum; that case is not formalized.

**Specialization.** The result proves the classical solution property only for the finite
expansion. -/
theorem equation_13_5 (N : ℕ) (c : ℕ → ℝ) (T : ℝ) :
    IsHeatSolution 1 T (fun _ _ => 0) (sineDatum N c) (sineSolution N c) := by
  have hexp : ∀ a s : ℝ, HasDerivAt (fun r : ℝ => Real.exp (a * r)) (a * Real.exp (a * s)) s :=
    fun a s => by simpa [mul_comm] using ((hasDerivAt_id' (x := s)).const_mul a).exp
  have hsin : ∀ b y : ℝ, HasDerivAt (fun z : ℝ => Real.sin (b * z)) (b * Real.cos (b * y)) y :=
    fun b y => by simpa [mul_comm] using ((hasDerivAt_id' (x := y)).const_mul b).sin
  have hcos : ∀ b y : ℝ, HasDerivAt (fun z : ℝ => Real.cos (b * z)) (-(b * Real.sin (b * y))) y :=
    fun b y => by simpa [mul_comm] using ((hasDerivAt_id' (x := y)).const_mul b).cos
  refine ⟨fun x t => ∑ k ∈ Finset.range N,
      c k * (-((k : ℝ) * π) ^ 2 * Real.exp (-((k : ℝ) * π) ^ 2 * t)) * Real.sin (k * π * x),
    fun x t => ∑ k ∈ Finset.range N,
      c k * Real.exp (-((k : ℝ) * π) ^ 2 * t) * ((k : ℝ) * π * Real.cos (k * π * x)),
    fun x t => ∑ k ∈ Finset.range N,
      c k * Real.exp (-((k : ℝ) * π) ^ 2 * t) * ((k : ℝ) * π *
        -((k : ℝ) * π * Real.sin (k * π * x))), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine fun x _ t _ => ⟨?_, ?_, ?_, ?_⟩
    · refine HasDerivAt.hasDerivWithinAt ?_
      exact HasDerivAt.fun_sum fun k _ =>
        (((hexp (-((k : ℝ) * π) ^ 2) t).const_mul (c k)).mul_const (Real.sin (k * π * x)))
    · refine HasDerivAt.hasDerivWithinAt ?_
      exact HasDerivAt.fun_sum fun k _ =>
        ((hsin ((k : ℝ) * π) x).const_mul (c k * Real.exp (-((k : ℝ) * π) ^ 2 * t)))
    · refine HasDerivAt.hasDerivWithinAt ?_
      exact HasDerivAt.fun_sum fun k _ =>
        (((hcos ((k : ℝ) * π) x).const_mul ((k : ℝ) * π)).const_mul
          (c k * Real.exp (-((k : ℝ) * π) ^ 2 * t)))
    · rw [one_mul, sub_eq_zero]
      exact Finset.sum_congr rfl fun k _ => by ring
  · fun_prop
  · fun_prop
  · fun_prop
  · exact fun t _ => ⟨by simp [sineSolution], by simp [sineSolution, Real.sin_nat_mul_pi]⟩
  · exact fun x _ => by simp [sineSolution, sineDatum]

/-- **Section 13.1** of [quarteroni2000numerical], orthogonality of the sines on $(0, 1)$. For
natural numbers $m$ and $n$ with $n \neq 0$,
$$\int_0^1 \sin(m\pi x) \sin(n\pi x) \, dx = \begin{cases} 1/2 & \text{if } m = n, \\ 0 &
  \text{otherwise.} \end{cases}$$

This gives the formula for the coefficients $c_n$ of (13.5). The product is
$(\cos((m - n)\pi x) - \cos((m + n)\pi x))/2$, and $\int_0^1 \cos(k\pi x) \, dx = 0$ for every
nonzero integer $k$. -/
theorem integral_sin_mul_sin (m : ℕ) {n : ℕ} (hn : n ≠ 0) :
    (∫ x in (0 : ℝ)..1, Real.sin (m * π * x) * Real.sin (n * π * x))
      = if m = n then 1 / 2 else 0 := by
  have hsin : ∀ b y : ℝ, HasDerivAt (fun z : ℝ => Real.sin (b * z)) (b * Real.cos (b * y)) y :=
    fun b y => by simpa [mul_comm] using ((hasDerivAt_id' (x := y)).const_mul b).sin
  have hcont : ∀ c : ℝ, Continuous fun x : ℝ => Real.cos (c * x) :=
    fun c => Real.continuous_cos.comp (continuous_const.mul continuous_id)
  have hint : ∀ c : ℝ,
      IntervalIntegrable (fun x : ℝ => Real.cos (c * x)) MeasureTheory.volume 0 1 :=
    fun c => (hcont c).intervalIntegrable _ _
  have hcosint : ∀ c : ℝ, c ≠ 0 → (∫ x in (0 : ℝ)..1, Real.cos (c * x)) = Real.sin c / c := by
    intro c hc
    have hd : ∀ x ∈ uIcc (0 : ℝ) 1,
        HasDerivAt (fun y : ℝ => Real.sin (c * y) / c) (Real.cos (c * x)) x := by
      intro x _
      have h := (hsin c x).div_const c
      rwa [mul_div_cancel_left₀ _ hc] at h
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hint c)]
    simp
  have hprod : ∀ x : ℝ, Real.sin (m * π * x) * Real.sin (n * π * x)
      = (Real.cos (((m : ℝ) - n) * π * x) - Real.cos (((m : ℝ) + n) * π * x)) / 2 := by
    intro x
    have h1 : ((m : ℝ) - n) * π * x = (m : ℝ) * π * x - (n : ℝ) * π * x := by ring
    have h2 : ((m : ℝ) + n) * π * x = (m : ℝ) * π * x + (n : ℝ) * π * x := by ring
    rw [h1, h2, Real.cos_sub, Real.cos_add]
    ring
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hmnpos : (0 : ℝ) < (m : ℝ) + n := by
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hsum : (∫ x in (0 : ℝ)..1, Real.cos (((m : ℝ) + n) * π * x)) = 0 := by
    rw [hcosint _ (ne_of_gt (mul_pos hmnpos Real.pi_pos))]
    have hc : ((m : ℝ) + n) * π = ((m + n : ℕ) : ℝ) * π := by push_cast; ring
    rw [hc, Real.sin_nat_mul_pi, zero_div]
  rw [intervalIntegral.integral_congr (g := fun x =>
      (Real.cos (((m : ℝ) - n) * π * x) - Real.cos (((m : ℝ) + n) * π * x)) / 2)
      (fun x _ => hprod x),
    intervalIntegral.integral_div, intervalIntegral.integral_sub (hint _) (hint _), hsum]
  by_cases hmn : m = n
  · subst hmn
    simp
  · have hne : ((m : ℝ) - n) * π ≠ 0 := by
      have h0 : ((m : ℝ) - n) ≠ 0 := by
        simp only [sub_ne_zero]
        exact_mod_cast hmn
      exact mul_ne_zero h0 Real.pi_ne_zero
    rw [hcosint _ hne]
    have hcast : ((m : ℝ) - n) * π = (((m : ℤ) - n : ℤ) : ℝ) * π := by push_cast; ring
    rw [hcast, Real.sin_int_mul_pi, zero_div]
    simp [hmn]

/-- **Equation (13.5)** of [quarteroni2000numerical], the coefficients. Let
$u_0(x) = \sum_{k < N} c_k \sin(k\pi x)$ be a finite sine sum. Then for $1 \le n < N$,
$$c_n = 2 \int_0^1 u_0(x) \sin(n\pi x) \, dx.$$

The book states this formula for a general datum.

**Specialization.** The coefficient formula is asserted for nonzero frequencies present in the
finite expansion. -/
theorem equation_13_5_coeff (N : ℕ) (c : ℕ → ℝ) {n : ℕ} (hn : n ≠ 0) (hnN : n < N) :
    c n = 2 * ∫ x in (0 : ℝ)..1, sineDatum N c x * Real.sin (n * π * x) := by
  have hint : ∀ k : ℕ, IntervalIntegrable
      (fun x : ℝ => c k * (Real.sin (k * π * x) * Real.sin (n * π * x)))
      MeasureTheory.volume 0 1 := fun k =>
    (((Real.continuous_sin.comp (continuous_const.mul continuous_id)).mul
      (Real.continuous_sin.comp (continuous_const.mul continuous_id))).const_mul
      (c k)).intervalIntegrable _ _
  have hcongr : ∀ x ∈ uIcc (0 : ℝ) 1, sineDatum N c x * Real.sin (n * π * x)
      = ∑ k ∈ Finset.range N, c k * (Real.sin (k * π * x) * Real.sin (n * π * x)) := by
    intro x _
    rw [sineDatum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hmem : n ∈ Finset.range N := Finset.mem_range.2 hnN
  rw [intervalIntegral.integral_congr hcongr,
    intervalIntegral.integral_finsetSum fun k _ => hint k,
    Finset.sum_eq_single_of_mem n hmem fun k _ hkn => by
      rw [intervalIntegral.integral_const_mul, integral_sin_mul_sin k hn]
      simp [hkn],
    intervalIntegral.integral_const_mul]
  have hdiag : (∫ x in (0 : ℝ)..1, Real.sin (n * π * x) * Real.sin (n * π * x)) = 1 / 2 := by
    rw [integral_sin_mul_sin n hn]
    simp
  rw [hdiag]
  ring

/-! ### The energy and the a priori estimate (13.7) -/

/-- **Section 13.1** of [quarteroni2000numerical], the energy. For a function $u$ of space and time,
$$E(t) = \int_0^1 u(x, t)^2 \, dx.$$

The source energy $F(t) = \int_0^1 f(x, t)^2 \, dx$ of the same section is
`QuarteroniSaccoSaleri.Chapter13.energy f t`. The definition is `Heat.energy`. -/
noncomputable abbrev energy (u : ℝ → ℝ → ℝ) (t : ℝ) : ℝ := Heat.energy u t

/-- **Equation (13.7)** of [quarteroni2000numerical], the a priori energy estimate. Let $\nu > 0$
and $T \ge 0$, and let $u$ be a classical solution of (13.1)–(13.4) on $[0, 1] \times [0, T]$
with source $f$ and initial datum $u_0$. Then for every $t \in [0, T]$
$$E(t) \le e^{-\gamma t} E(0) + \frac{1}{\gamma} \int_0^t e^{\gamma(s - t)} F(s) \, ds, \qquad
  \gamma = \frac{\nu}{C_P^2} = 2\nu,$$
where $E(t) = \int_0^1 u(x, t)^2 \, dx$ and $F(t) = \int_0^1 f(x, t)^2 \, dx$. In particular,
for $f = 0$ the energy decays exponentially.

The proof is `Heat.IsClassicalSolutionIcc.energy_le`. It follows the steps of the book, with the
interchange of differentiation and integration done in integrated form by Fubini's theorem. The
factor $1/\gamma$ is written inside the integral.

**Specialization.** The result uses the closed-rectangle Dirichlet problem and the explicit
constant $\gamma=2\nu$. -/
theorem equation_13_7 {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) {f : ℝ → ℝ → ℝ} {u₀ : ℝ → ℝ}
    {u : ℝ → ℝ → ℝ} (hu : IsHeatSolution ν T f u₀ u) {t : ℝ} (ht : t ∈ Icc 0 T) :
    energy u t ≤ Real.exp (-(2 * ν) * t) * energy u 0
      + ∫ s in (0 : ℝ)..t, Real.exp (2 * ν * (s - t)) * (energy f s / (2 * ν)) :=
  Heat.IsClassicalSolutionIcc.energy_le hν hT hu ht

end QuarteroniSaccoSaleri.Chapter13
