/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.QuarteroniSaccoSaleri.Chapter13.Section08

/-!
# Quarteroni, Sacco and Saleri, Section 13.9: Dissipation and dispersion

This module formalizes §13.9 and §13.9.1 of [quarteroni2000numerical], on the dissipation and the
dispersion of finite difference schemes for the transport equation $u_t + a u_x = 0$ (13.26). Per
time step, the exact solution multiplies the $k$-th harmonic $e^{ikx}$ by $g_k = e^{-iak\Delta t}$
(13.54). With the phase angle $\varphi_k = k \Delta x$ and $\lambda = \Delta t / \Delta x$, this is
$g_k = e^{-ia\lambda\varphi_k}$ (13.55), and $|g_k| = 1$. A numerical scheme multiplies the harmonic
by its amplification factor $\gamma_k$ instead. The amplification error $\varepsilon_a(k) =
|\gamma_k| / |g_k| = |\gamma_k|$ measures the dissipation, and the dispersion error
$\varepsilon_d(k) = \omega / (ka) = -\arg \gamma_k / (a \lambda \varphi_k)$, the ratio of the
numerical phase speed to $a$, measures the dispersion.

Section 13.9.1 associates with each scheme an equivalent (modified) equation
$v_t + a v_x = \mu v_{xx} + \nu v_{xxx}$ (13.56). The second-order term is dissipative and the
third-order term is dispersive: the Fourier mode solution is $v(x, t) = e^{-\mu k^2 t} e^{ik[x -
(a + \nu k^2)t]}$ (13.63), so $\mu$ damps the amplitude, more strongly at high $k$, and $\nu$
changes the phase speed to $a + \nu k^2$. A scheme solves its equivalent equation to a higher order
than the transport equation. The coefficients $\mu$ and $\nu$ of Table 13.2 for the upwind,
Lax–Friedrichs and Lax–Wendroff schemes are the content of (13.59), (13.60) and Exercise 13.8. The
proofs specialize `Numlib.FiniteDifference.Hyperbolic`.

## Main definitions

* Section 13.9, `QuarteroniSaccoSaleri.Chapter13.amplificationError`: the amplification error
  $\varepsilon_a = |\gamma|$ of an amplification factor $\gamma$.
* Section 13.9, `QuarteroniSaccoSaleri.Chapter13.dispersionError`: the dispersion error
  $\varepsilon_d = -\arg \gamma / (a \lambda \varphi)$.
* Equation (13.56), `QuarteroniSaccoSaleri.Chapter13.equation_13_56`: the classical solutions of the
  equivalent equation $v_t + a v_x = \mu v_{xx} + \nu v_{xxx}$.

## Main results

* Equations (13.54)–(13.55), `QuarteroniSaccoSaleri.Chapter13.equation_13_54`:
  $g_k = e^{-iak\Delta t}$, $g_k^n = e^{-iakn\Delta t}$ and $g_k = e^{-ia\lambda\varphi_k}$.
* Section 13.9, `QuarteroniSaccoSaleri.Chapter13.amplificationError_exact`: if
  $0 < |a \lambda \varphi_k| < \pi$, the exact factor has $|g_k| = 1$, $\varepsilon_a = 1$ and
  $\varepsilon_d = 1$.
* Equations (13.57)–(13.58), `QuarteroniSaccoSaleri.Chapter13.equation_13_57`: the Taylor expansions
  of the residual of the upwind scheme for $a > 0$.
* Equation (13.59), `QuarteroniSaccoSaleri.Chapter13.equation_13_59`: for
  $\mu = a \Delta x / 2 - a^2 \Delta t / 2$, a solution of $v_t + a v_x = \mu v_{xx}$ leaves the
  upwind scheme a residual $O(\Delta t^2 + \Delta t \Delta x + \Delta x^2)$.
* Equation (13.60) and Table 13.2, `QuarteroniSaccoSaleri.Chapter13.equation_13_60`: for fixed
  $\lambda$ and the upwind coefficients $\mu$ and $\nu$ of Table 13.2, a solution of (13.56) leaves
  the upwind scheme a residual $O(\Delta x^3)$.
* Equations (13.61)–(13.63), `QuarteroniSaccoSaleri.Chapter13.equation_13_63`: the Fourier mode
  solution $e^{-\mu k^2 t} e^{ik[x - (a + \nu k^2)t]}$ of (13.56).
* Exercise 13.8 and Table 13.2, `QuarteroniSaccoSaleri.Chapter13.exercise_13_8`: the statement of
  (13.60) for the Lax–Friedrichs and the Lax–Wendroff schemes.

## Implementation notes

* The residual of a scheme on a smooth function $v(x, t)$ is `FiniteDifference.Hyperbolic.residual`:
  the amount by which $v$ fails to satisfy the difference equation, divided by $\Delta t$. The
  results on the equivalent equations are bounds on this residual, with explicit constants in place
  of $O(\cdot)$.
* The partial derivatives of $v$ are a family `D : ℕ → ℕ → ℝ → ℝ → ℝ` with `HasPartialDerivs v D`,
  where `D i j` is $\partial_x^i \partial_t^j v$. The bounds on the derivatives are hypotheses on
  this family.
* The dispersion error uses the principal argument $\arg \gamma \in (-\pi, \pi]$, and it is $0$ when
  $a \lambda \varphi = 0$, by the convention for division by zero.

## Deviations from the source

* **Equation (13.58)** (typo). The source prints the term $a (v_x + (\Delta x / 2) v_{xx})$; the
  backward difference gives $a (v_x - (\Delta x / 2) v_{xx})$. See
  `QuarteroniSaccoSaleri.Chapter13.equation_13_57`.
* **Text after (13.60)** (correction). The text gives $\nu = (a/6)(a^2 \Delta t^2 - \Delta x^2)$ for
  the upwind scheme, which disagrees with Table 13.2; the statement uses the value of the table. See
  `QuarteroniSaccoSaleri.Chapter13.equation_13_60`.

## Not formalized

* **Figures 13.7–13.9.** They are plots.
-/

open FiniteDifference

namespace QuarteroniSaccoSaleri.Chapter13

/-! ### The exact amplification factor and the two errors -/

/-- **Equations (13.54)–(13.55)** of [quarteroni2000numerical]. Let
$a, \Delta t, \Delta x \in \mathbb{R}$ with $\Delta x \neq 0$, let
$\lambda = \Delta t / \Delta x$, and let $k \in \mathbb{Z}$. The exact amplification factor
$g_k$ of the $k$-th harmonic satisfies
$$g_k = e^{-iak\Delta t}, \qquad g_k^n = e^{-iakn\Delta t} \quad (n \in \mathbb{N}), \qquad
  g_k = e^{-ia\lambda\varphi_k},$$
where $\varphi_k = k \Delta x$ is the phase angle.

The factor $g_k$ is `FiniteDifference.Hyperbolic.exactAmplification a Δt k`, which is defined as
$e^{-iak\Delta t}$, so the first clause holds by definition. The phase angle is
`FiniteDifference.Hyperbolic.phaseAngle k Δx`. -/
theorem equation_13_54 {Δt Δx lam : ℝ} (hΔx : Δx ≠ 0) (hlam : lam = Δt / Δx) (a : ℝ) (k : ℤ) :
    Hyperbolic.exactAmplification a Δt k = Complex.exp (-(Complex.I * a * k * Δt)) ∧
      (∀ n : ℕ, Hyperbolic.exactAmplification a Δt k ^ n
          = Complex.exp (-(Complex.I * a * k * ((n : ℝ) * Δt)))) ∧
        Hyperbolic.exactAmplification a Δt k
          = Complex.exp (-(Complex.I * ((a * lam * Hyperbolic.phaseAngle k Δx : ℝ) : ℂ))) :=
  ⟨rfl, Hyperbolic.exactAmplification_pow a Δt k,
    Hyperbolic.exactAmplification_eq_phaseAngle hΔx hlam a k⟩

/-- **Section 13.9** of [quarteroni2000numerical], the amplification error. The **amplification
error** of an amplification factor $\gamma \in \mathbb{C}$ is $\varepsilon_a = |\gamma|$.

The source defines $\varepsilon_a(k) = |\gamma_k| / |g_k|$ for the factor $\gamma_k$ of the
$k$-th harmonic. This is $|\gamma_k|$, because $|g_k| = 1$. The definition is
`FiniteDifference.Hyperbolic.amplificationError`. -/
noncomputable def amplificationError (γ : ℂ) : ℝ := Hyperbolic.amplificationError γ

/-- **Section 13.9** of [quarteroni2000numerical], the dispersion error. Let
$a, \lambda, \varphi \in \mathbb{R}$ and $\gamma \in \mathbb{C}$. The **dispersion error** is
$$\varepsilon_d = -\frac{\arg \gamma}{a \lambda \varphi}.$$
For the factor $\gamma_k = |\gamma_k| e^{-i\omega\Delta t}$ of the $k$-th harmonic and
$\varphi = \varphi_k$, it is the ratio $\omega / (ka)$ of the numerical phase speed to the exact
speed $a$.

Here $\arg$ is the principal argument `Complex.arg`, with values in $(-\pi, \pi]$. When
$a \lambda \varphi = 0$ the value is $0$, by the convention for division by zero. The definition
is `FiniteDifference.Hyperbolic.dispersionError`. -/
noncomputable def dispersionError (a lam phi : ℝ) (γ : ℂ) : ℝ :=
  Hyperbolic.dispersionError a lam phi γ

/-- **Section 13.9** of [quarteroni2000numerical], the exact factor has modulus $1$. Let
$a, \lambda, \Delta t, \Delta x \in \mathbb{R}$ with $\Delta x \neq 0$ and
$\lambda = \Delta t / \Delta x$, and let $k \in \mathbb{Z}$ with
$0 < |a \lambda \varphi_k| < \pi$, where $\varphi_k = k \Delta x$. Then the exact amplification
factor $g_k$ has no dissipation and no dispersion:
$$|g_k| = 1, \qquad \varepsilon_a(g_k) = 1, \qquad \varepsilon_d(g_k) = 1.$$

The condition $|a \lambda \varphi_k| < \pi$ makes the phase of $g_k$ unambiguous, so that
$\arg g_k = -a \lambda \varphi_k$, and the condition $a \lambda \varphi_k \neq 0$ excludes the
division by zero. The first two clauses hold without these conditions. -/
theorem amplificationError_exact {a lam Δt Δx : ℝ} {k : ℤ} (hΔx : Δx ≠ 0)
    (hlam : lam = Δt / Δx) (h0 : a * lam * Hyperbolic.phaseAngle k Δx ≠ 0)
    (hpi : |a * lam * Hyperbolic.phaseAngle k Δx| < Real.pi) :
    ‖Hyperbolic.exactAmplification a Δt k‖ = 1 ∧
      amplificationError (Hyperbolic.exactAmplification a Δt k) = 1 ∧
        dispersionError a lam (Hyperbolic.phaseAngle k Δx)
          (Hyperbolic.exactAmplification a Δt k) = 1 :=
  ⟨Hyperbolic.norm_exactAmplification a Δt k,
    Hyperbolic.amplificationError_exactAmplification a Δt k,
    Hyperbolic.dispersionError_exactAmplification hΔx hlam h0 hpi⟩

/-! ### Section 13.9.1: the equivalent equations -/

/-- **Equation (13.56)** of [quarteroni2000numerical]. Let $a, \mu, \nu \in \mathbb{R}$. A function
$v = v(x, t)$ on $\mathbb{R}^2$ is a **classical solution of the equivalent equation**
$$v_t + a v_x = \mu v_{xx} + \nu v_{xxx}$$
if $v$, $v_x$ and $v_{xx}$ are differentiable on the whole plane and the equation holds at every
point $(x, t)$.

The term $\mu v_{xx}$ is dissipative and the term $\nu v_{xxx}$ is dispersive. The definition is
`FiniteDifference.Hyperbolic.IsModifiedSolution`, where the derivatives are functions given with
`Transport.HasPartialsOn Set.univ`. -/
def equation_13_56 (a mu nu : ℝ) (v : ℝ → ℝ → ℝ) : Prop :=
  Hyperbolic.IsModifiedSolution a mu nu v

/-- **Equations (13.61)–(13.63)** of [quarteroni2000numerical]. Let $a, \mu, \nu \in \mathbb{R}$ and
$k \in \mathbb{Z}$, and let $\sigma = -\mu k^2 - ik(a + \nu k^2)$. Then
$$\sigma + a(ik) = \mu (ik)^2 + \nu (ik)^3,$$
and for all $x, t \in \mathbb{R}$
$$e^{ikx + \sigma t} = e^{-\mu k^2 t} e^{ik[x - (a + \nu k^2)t]}, \qquad
  |e^{ikx + \sigma t}| = e^{-\mu k^2 t},$$
and $e^{ikx + \sigma t} = e^{ikx}$ at $t = 0$.

The first relation is the condition under which the exponential function
$v(x, t) = e^{ikx + \sigma t}$ satisfies the equivalent equation (13.56), and the second is
(13.63). So $\mu$ damps the amplitude, more strongly for higher frequencies, and $\nu$ changes
the speed of propagation from $a$ to $a + \nu k^2$. For $\mu = \nu = 0$ the mode is
$e^{ik(x - at)}$ (13.62).

The theorem states the algebraic relation for $\sigma$; it does not state that $v$ solves
(13.56) in the sense of `QuarteroniSaccoSaleri.Chapter13.equation_13_56`. -/
theorem equation_13_63 (a mu nu : ℝ) (k : ℤ) :
    -(mu * (k : ℂ) ^ 2) - Complex.I * k * (a + nu * (k : ℂ) ^ 2)
          + a * (Complex.I * k)
        = mu * (Complex.I * (k : ℂ)) ^ 2 + nu * (Complex.I * (k : ℂ)) ^ 3 ∧
      (∀ x t : ℝ, Complex.exp (Complex.I * k * x
            + (-(mu * (k : ℂ) ^ 2) - Complex.I * k * (a + nu * (k : ℂ) ^ 2)) * t)
          = (Real.exp (-(mu * (k : ℝ) ^ 2) * t) : ℂ)
            * Complex.exp (Complex.I * k * ((x : ℂ) - (a + nu * (k : ℝ) ^ 2) * t))) ∧
        (∀ x : ℝ, Complex.exp (Complex.I * k * x
            + (-(mu * (k : ℂ) ^ 2) - Complex.I * k * (a + nu * (k : ℂ) ^ 2)) * (0 : ℝ))
          = Complex.exp (Complex.I * k * x)) ∧
          ∀ x t : ℝ, ‖Complex.exp (Complex.I * k * x
              + (-(mu * (k : ℂ) ^ 2) - Complex.I * k * (a + nu * (k : ℂ) ^ 2)) * t)‖
            = Real.exp (-(mu * (k : ℝ) ^ 2) * t) := by
  have hI2 : (Complex.I * (k : ℂ)) ^ 2 = -((k : ℂ) ^ 2) := by
    rw [mul_pow, Complex.I_sq]; ring
  have hI3 : (Complex.I * (k : ℂ)) ^ 3 = -(Complex.I * (k : ℂ) ^ 3) := by
    rw [mul_pow, show Complex.I ^ 3 = -Complex.I by rw [pow_succ, Complex.I_sq]; ring]; ring
  refine ⟨by rw [hI2, hI3]; ring, fun x t => ?_, fun x => by norm_num, fun x t => ?_⟩
  · rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  · rw [Complex.norm_exp]
    congr 1
    have hre : ((k : ℂ) ^ 2).re = (k : ℝ) ^ 2 := by
      rw [show ((k : ℂ) ^ 2) = ((k ^ 2 : ℤ) : ℂ) from by push_cast; ring, Complex.intCast_re]
      push_cast
      ring
    have him : ((k : ℂ) ^ 2).im = 0 := by
      rw [show ((k : ℂ) ^ 2) = ((k ^ 2 : ℤ) : ℂ) from by push_cast; ring, Complex.intCast_im]
    simp [Complex.add_re, Complex.mul_re, Complex.mul_im, hre, him]
    try ring

/-- **Equations (13.57)–(13.58)** of [quarteroni2000numerical]. Let $a > 0$, $\Delta t > 0$,
$\Delta x > 0$ and $\lambda = \Delta t / \Delta x$. Let $v = v(x, t)$ have partial derivatives
of all orders, with $|\partial_x^i \partial_t^j v| \le M_2$ everywhere for $i + j = 2$ and
$|\partial_x^i \partial_t^j v| \le M_3$ everywhere for $i + j = 3$. Let $R(x, t)$ be the
residual of the upwind scheme (13.41) on $v$. Then for all $x, t$
$$R(x, t) = \frac{v(x, t + \Delta t) - v(x, t)}{\Delta t} + a \frac{v(x, t) - v(x - \Delta x,
  t)}{\Delta x},$$
$$|R - (v_t + a v_x)| \le \frac{\Delta t}{2} M_2 + \frac{a \Delta x}{2} M_2,$$
$$\Bigl|R - \Bigl(v_t + \frac{\Delta t}{2} v_{tt} + a v_x - \frac{a \Delta x}{2}
  v_{xx}\Bigr)\Bigr| \le \frac{\Delta t^2}{6} M_3 + \frac{a \Delta x^2}{6} M_3.$$
The second estimate is (13.57) and the third is (13.58).

**Typo.** The source prints (13.58) with the term $a (v_x + (\Delta x / 2) v_{xx})$. The
backward difference $[v(x, t) - v(x - \Delta x, t)] / \Delta x$ is
$v_x - (\Delta x / 2) v_{xx} + O(\Delta x^2)$, and the minus sign gives the coefficient
$\mu = a \Delta x / 2 - a^2 \Delta t / 2$ of (13.59).

The derivatives are the family `D` with `HasPartialDerivs v D`, where `D i j` is
$\partial_x^i \partial_t^j v$. The residual is `FiniteDifference.Hyperbolic.residual` for the
stencil `FiniteDifference.Hyperbolic.upwind a lam`. -/
theorem equation_13_57 {v : ℝ → ℝ → ℝ} {D : ℕ → ℕ → ℝ → ℝ → ℝ} {a M₂ M₃ Δt Δx lam : ℝ}
    (hD : HasPartialDerivs v D) (ha : 0 < a) (hΔt : 0 < Δt) (hΔx : 0 < Δx)
    (hlam : lam = Δt / Δx) (hM₂ : ∀ i j, i + j = 2 → ∀ y s, |D i j y s| ≤ M₂)
    (hM₃ : ∀ i j, i + j = 3 → ∀ y s, |D i j y s| ≤ M₃) (x t : ℝ) :
    Hyperbolic.residual (Hyperbolic.upwind a lam) Δt Δx v x t
        = (v x (t + Δt) - v x t) / Δt + a * ((v x t - v (x - Δx) t) / Δx) ∧
      |Hyperbolic.residual (Hyperbolic.upwind a lam) Δt Δx v x t - (D 0 1 x t + a * D 1 0 x t)|
        ≤ Δt / 2 * M₂ + a * Δx / 2 * M₂ ∧
      |Hyperbolic.residual (Hyperbolic.upwind a lam) Δt Δx v x t
          - (D 0 1 x t + Δt / 2 * D 0 2 x t + a * D 1 0 x t - a * Δx / 2 * D 2 0 x t)|
        ≤ Δt ^ 2 / 6 * M₃ + a * Δx ^ 2 / 6 * M₃ := by
  refine ⟨?_, Hyperbolic.abs_residual_upwind_sub_le hD ha hΔt hΔx hlam hM₂ x t,
    Hyperbolic.abs_residual_upwind_sub_le_two hD ha hΔt hΔx hlam hM₃ x t⟩
  subst hlam
  rw [Hyperbolic.upwind_eq_of_pos ha, Hyperbolic.residual_threePoint]
  field_simp
  ring

/-- **Equation (13.59)** of [quarteroni2000numerical]. Let $a > 0$, $\Delta t > 0$, $\Delta x > 0$,
$\lambda = \Delta t / \Delta x$ and $\mu = a \Delta x / 2 - a^2 \Delta t / 2$. Let $v$ be a
classical solution of $v_t + a v_x = \mu v_{xx}$, which is (13.56) with $\nu = 0$, and let $v$
have partial derivatives of all orders, with $|\partial_x^i \partial_t^j v| \le M$ everywhere
for $i + j = 3$. Then the residual $R$ of the upwind scheme on $v$ satisfies, for all $x, t$,
$$|R(x, t)| \le M (1 + a)^3 (\Delta t^2 + \Delta t \Delta x + \Delta x^2).$$

A solution of the transport equation itself leaves the upwind scheme a residual of order
$O(\Delta t + \Delta x)$ (Table 13.1). So the upwind scheme solves the equation with the
dissipative term $\mu v_{xx}$ to second order. -/
theorem equation_13_59 {v : ℝ → ℝ → ℝ} {D : ℕ → ℕ → ℝ → ℝ → ℝ} {a mu M Δt Δx lam : ℝ}
    (hD : HasPartialDerivs v D) (ha : 0 < a) (hΔt : 0 < Δt) (hΔx : 0 < Δx)
    (hlam : lam = Δt / Δx) (hmu : mu = a * Δx / 2 - a ^ 2 * Δt / 2)
    (hv : equation_13_56 a mu 0 v) (hM : ∀ i j, i + j = 3 → ∀ y s, |D i j y s| ≤ M) (x t : ℝ) :
    |Hyperbolic.residual (Hyperbolic.upwind a lam) Δt Δx v x t|
      ≤ M * (1 + a) ^ 3 * (Δt ^ 2 + Δt * Δx + Δx ^ 2) :=
  Hyperbolic.abs_residual_upwind_le_of_isModifiedSolution hD ha hΔt hΔx hlam hmu hv hM x t

/-- **Equation (13.60)** and **Table 13.2** of [quarteroni2000numerical], upwind scheme. Let
$a > 0$, $\Delta t > 0$, $\Delta x > 0$, $\lambda = \Delta t / \Delta x$, and
$$\mu = \frac{a \Delta x}{2} - \frac{a^2 \Delta t}{2}, \qquad
  \nu = -\frac{a}{6} (\Delta x^2 - 3a \Delta x \Delta t + 2a^2 \Delta t^2).$$
Let $v$ be a classical solution of the equivalent equation (13.56) with these coefficients, and
let $v$ have partial derivatives of all orders, with $|\partial_x^i \partial_t^j v| \le M$
everywhere for $i + j \le 5$. Then the residual $R$ of the upwind scheme on $v$ satisfies, for
all $x, t$,
$$|R(x, t)| \le M \Bigl(\frac{\Delta t (\mu^2 + |a| |\nu| + |\mu| |\nu| + |\nu|)}{2} +
  \frac{\Delta t^2 (a^2 + |a| + 1)(|\mu| + |\nu|)}{6} + \frac{\Delta t^3}{24} + \frac{\lambda a
  \Delta x^4}{24 \Delta t}\Bigr).$$
For fixed $\lambda$ we have $\Delta t = \lambda \Delta x$, $\mu = O(\Delta x)$ and
$\nu = O(\Delta x^2)$, so the bound is $O(\Delta x^3)$, one order better than (13.59).

**Correction.** The text after (13.60) gives $\nu = (a/6)(a^2 \Delta t^2 - \Delta x^2)$, which
disagrees with Table 13.2. The value of the table, the Warming–Hyett coefficient, is the correct
one and is used here. The text drops the contribution $-2a\mu \, \partial_{xxx}$ when it
substitutes for $v_{tt}$. -/
theorem equation_13_60 {v : ℝ → ℝ → ℝ} {D : ℕ → ℕ → ℝ → ℝ → ℝ} {a mu nu M Δt Δx lam : ℝ}
    (hD : HasPartialDerivs v D) (ha : 0 < a) (hΔt : 0 < Δt) (hΔx : 0 < Δx)
    (hlam : lam = Δt / Δx) (hmu : mu = a * Δx / 2 - a ^ 2 * Δt / 2)
    (hnu : nu = -(a / 6) * (Δx ^ 2 - 3 * a * Δx * Δt + 2 * a ^ 2 * Δt ^ 2))
    (hv : equation_13_56 a mu nu v) (hM : ∀ i j, i + j ≤ 5 → ∀ y s, |D i j y s| ≤ M) (x t : ℝ) :
    |Hyperbolic.residual (Hyperbolic.upwind a lam) Δt Δx v x t|
      ≤ M * (Δt * (mu ^ 2 + |a| * |nu| + |mu| * |nu| + |nu|) / 2
          + Δt ^ 2 * (a ^ 2 + |a| + 1) * (|mu| + |nu|) / 6
          + Δt ^ 3 / 24 + lam * a * Δx ^ 4 / (24 * Δt)) :=
  Hyperbolic.abs_residual_upwind_le_of_isModifiedSolution_third hD ha hΔt hΔx hlam hmu hnu hv hM
    x t

/-- **Exercise 13.8** and **Table 13.2** of [quarteroni2000numerical], Lax–Friedrichs and
Lax–Wendroff schemes. Let $a \in \mathbb{R}$, $\Delta t > 0$, $\Delta x > 0$ and
$\lambda = \Delta t / \Delta x$, and let
$$\mu = \frac{\Delta x^2}{2 \Delta t} (1 - (a\lambda)^2), \qquad
  \nu = \frac{a \Delta x^2}{3} (1 - (a\lambda)^2), \qquad
  \nu' = \frac{a \Delta x^2}{6} ((a\lambda)^2 - 1).$$
Let $v$ be a classical solution of (13.56) with the coefficients $\mu$ and $\nu$, and let $w$ be
a classical solution of (13.56) with the coefficients $0$ and $\nu'$. Let $v$ and $w$ have
partial derivatives of all orders, with $|\partial_x^i \partial_t^j v| \le M$ and
$|\partial_x^i \partial_t^j w| \le M$ everywhere for $i + j \le 5$. Then for all $x, t$ the
residual $R_{LF}$ of the Lax–Friedrichs scheme (13.39) on $v$ and the residual $R_{LW}$ of the
Lax–Wendroff scheme (13.40) on $w$ satisfy
$$|R_{LF}(x, t)| \le M \Bigl(\frac{\Delta t (\mu^2 + |a| |\nu| + |\mu| |\nu| + |\nu|)}{2} +
  \frac{\Delta t^2 (a^2 + |a| + 1)(|\mu| + |\nu|)}{6} + \frac{\Delta t^3}{24} + \frac{(1 +
  |\lambda a|) \Delta x^4}{24 \Delta t}\Bigr),$$
$$|R_{LW}(x, t)| \le M \Bigl(\frac{\Delta t (|a| |\nu'| + |\nu'|)}{2} + \frac{\Delta t^2 (a^2 +
  |a| + 1) |\nu'|}{6} + \frac{\Delta t^3}{24} + \frac{|\lambda a| (1 + |\lambda a|) \Delta
  x^4}{24 \Delta t}\Bigr).$$
For fixed $\lambda$ both bounds are $O(\Delta x^3)$.

The Lax–Wendroff scheme is second-order accurate, so its equivalent equation has no dissipative
term: its coefficient $\mu$ is $0$. The schemes are
`QuarteroniSaccoSaleri.Chapter13.equation_13_39` and
`QuarteroniSaccoSaleri.Chapter13.equation_13_40`. -/
theorem exercise_13_8 {v w : ℝ → ℝ → ℝ} {D E : ℕ → ℕ → ℝ → ℝ → ℝ}
    {a mu nu nu' M Δt Δx lam : ℝ} (hD : HasPartialDerivs v D) (hE : HasPartialDerivs w E)
    (hΔt : 0 < Δt) (hΔx : 0 < Δx) (hlam : lam = Δt / Δx)
    (hmu : mu = Δx ^ 2 / (2 * Δt) * (1 - (a * lam) ^ 2))
    (hnu : nu = a * Δx ^ 2 / 3 * (1 - (a * lam) ^ 2))
    (hnu' : nu' = a * Δx ^ 2 / 6 * ((a * lam) ^ 2 - 1))
    (hv : equation_13_56 a mu nu v) (hw : equation_13_56 a 0 nu' w)
    (hM : ∀ i j, i + j ≤ 5 → ∀ y s, |D i j y s| ≤ M)
    (hM' : ∀ i j, i + j ≤ 5 → ∀ y s, |E i j y s| ≤ M) (x t : ℝ) :
    |Hyperbolic.residual (equation_13_39 a lam) Δt Δx v x t|
        ≤ M * (Δt * (mu ^ 2 + |a| * |nu| + |mu| * |nu| + |nu|) / 2
            + Δt ^ 2 * (a ^ 2 + |a| + 1) * (|mu| + |nu|) / 6
            + Δt ^ 3 / 24 + (1 + |lam * a|) * Δx ^ 4 / (24 * Δt)) ∧
      |Hyperbolic.residual (equation_13_40 a lam) Δt Δx w x t|
        ≤ M * (Δt * (|a| * |nu'| + |nu'|) / 2 + Δt ^ 2 * (a ^ 2 + |a| + 1) * |nu'| / 6
            + Δt ^ 3 / 24 + |lam * a| * (1 + |lam * a|) * Δx ^ 4 / (24 * Δt)) :=
  ⟨Hyperbolic.abs_residual_laxFriedrichs_le_of_isModifiedSolution hD hΔt hΔx hlam hmu hnu hv hM
      x t,
    Hyperbolic.abs_residual_laxWendroff_le_of_isModifiedSolution hE hΔt hΔx hlam hnu' hw hM' x t⟩

end QuarteroniSaccoSaleri.Chapter13
