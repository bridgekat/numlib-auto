/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.QuarteroniSaccoSaleri.Chapter11.Section04
import NumlibSurface.QuarteroniSaccoSaleri.Chapter11.Section08

/-!
# Quarteroni, Sacco and Saleri, Section 11.12: Exercises

This module formalizes the exercises of Section 11.12 of [quarteroni2000numerical] that the main
text of Chapter 11 uses. Exercise 1 shows that Heun's method has order two, and Exercise 2 that the
Crank–Nicolson method has order two (11.90). Exercise 3 solves a difference equation whose
characteristic polynomial has a double root and a pair of complex conjugate roots. Exercise 4 proves
the form (11.32) of the solutions of a difference equation with simple roots, and Exercise 5 that
the matrix $R$ of (11.37) is then nonsingular. Exercise 12 writes Heun's method and the modified
Euler method (11.91) as two-stage Runge–Kutta methods.

The results restate `Numlib.ODE.OneStep`, `Numlib.Algebra.LinearRecurrence` and
`Numlib.ODE.RungeKutta`. The closed form of Exercise 3 is verified in this module.

## Main definitions

* Equation (11.91), `QuarteroniSaccoSaleri.Chapter11.equation_11_91`: the increment of the modified
  Euler method.

## Main results

* Exercise 11.1, `QuarteroniSaccoSaleri.Chapter11.exercise_11_1`: Heun's method has order two.
* Exercise 11.2, `QuarteroniSaccoSaleri.Chapter11.exercise_11_2`: the Crank–Nicolson method has
  order two.
* Exercise 11.3, `QuarteroniSaccoSaleri.Chapter11.exercise_11_3`: the closed-form solution of the
  difference equation $u_{n+4} - 6u_{n+3} + 14u_{n+2} - 16u_{n+1} + 8u_n = n$.
* Exercise 11.4, `QuarteroniSaccoSaleri.Chapter11.exercise_11_4`: with simple roots, every solution
  has the form (11.32).
* Exercise 11.5, `QuarteroniSaccoSaleri.Chapter11.exercise_11_5`: with simple roots, the matrix $R$
  of (11.37) is nonsingular.
* Exercise 11.12, `QuarteroniSaccoSaleri.Chapter11.exercise_11_12`: the Butcher arrays of Heun's
  method and of the modified Euler method.

## Conventions

* As in Sections 11.3 and 11.8, a solution is $C^3$ on the closed horizon, and its derivatives are
  `derivWithin` and `iteratedDerivWithin` on that interval. The Lipschitz constant $L \ge 0$ of $f$
  in $y$ is uniform on $[t_0, t_0 + T]$.

## Deviations from the source

* **Exercises 11.1 and 11.2** (reading). The order results are for the supplied $C^3$ solution
  on a finite interval and assume explicit derivative bounds. `exercise_11_1` also assumes a
  Lipschitz field. `exercise_11_2` gives a local error bound without the mean-value point in
  (11.90).
* **Exercises 11.4 and 11.5** (generalization). The representation theorem uses a field in which
  the $k$ distinct roots are supplied. The matrix theorem over any field needs only distinct
  inputs.
* **Exercise 11.3** (typo). The source prints $\sin(\pi/4)$ for $\sin(n\pi/4)$ in the solution. See
  `QuarteroniSaccoSaleri.Chapter11.exercise_11_3`.

## Not formalized

* **Exercises 11.6–11.11 and 11.13–11.15.** The main text does not cite them.
* **Equation (11.90)** in its mean-value form, with the intermediate point $\xi_n$. Only the bound
  on the truncation error is formalized, in `QuarteroniSaccoSaleri.Chapter11.exercise_11_2`.
-/

open Set Filter Topology Asymptotics ODE ODE.OneStep
open Finset (range)

namespace QuarteroniSaccoSaleri.Chapter11

variable {f : ℝ → ℝ → ℝ} {t₀ T h t y₀ : ℝ} {y : ℝ → ℝ} {n : ℕ}

/-! ### Exercises 1–2: Heun and Crank–Nicolson have order two -/

/-- **Exercise 11.1** of [quarteroni2000numerical]. Heun's method (11.10) has order $2$. Let $T > 0$
and $L \ge 0$, and let $f$ satisfy $|f(t, y_1) - f(t, y_2)| \le L |y_1 - y_2|$ for
$t \in [t_0, t_0 + T]$ and all $y_1, y_2$. Let $y \in C^3([t_0, t_0 + T])$ solve the Cauchy
problem $y' = f(t, y)$, $y(t_0) = y_0$ on $[t_0, t_0 + T]$, with $|y''| \le M_2$ and
$|y'''| \le M_3$ on $[t_0, t_0 + T]$. Then:

* for every $h > 0$ and every $n < N_h = \lfloor T / h \rfloor$, the local truncation error of
  Heun's method satisfies
$$|\tau_{n+1}(h)| \le \frac{h^2}{12} M_3 + \frac{h^2}{4} L M_2;$$
* Heun's method has order $2$ (11.14) along $y$.

The proof follows the hint of the source: it splits $h \tau_{n+1} = E_1 + E_2$, where $E_1$ is
the error of the trapezoidal quadrature and $E_2$ the error of the forward Euler step inside
$f$. It specializes `ODE.OneStep.norm_lte_heun_le` and `ODE.OneStep.hasOrderFor_heun`.

**Reading.** States the order and the local error bound along the supplied $C^3$ solution under
the indicated derivative bounds. For Crank–Nicolson the book gives a mean-value expression with
an intermediate point. -/
theorem exercise_11_1 (hT : 0 < T) {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ t ∈ Icc t₀ (t₀ + T), ∀ y₁ y₂ : ℝ, |f t y₁ - f t y₂| ≤ L * |y₁ - y₂|)
    (hy : cauchyProblem f t₀ y₀ (Icc t₀ (t₀ + T)) y) (hy3 : ContDiffOn ℝ 3 y (Icc t₀ (t₀ + T)))
    {M₂ M₃ : ℝ} (hM₂ : ∀ s ∈ Icc t₀ (t₀ + T), |iteratedDerivWithin 2 y (Icc t₀ (t₀ + T)) s| ≤ M₂)
    (hM₃ : ∀ s ∈ Icc t₀ (t₀ + T), |iteratedDerivWithin 3 y (Icc t₀ (t₀ + T)) s| ≤ M₃) :
    (∀ h : ℝ, 0 < h → ∀ n, n < gridCount T h →
      |equation_11_12 (equation_11_10 f) h y t₀ n| ≤ h ^ 2 / 12 * M₃ + h ^ 2 / 4 * L * M₂) ∧
    equation_11_14 (equation_11_10 f) t₀ T y 2 := by
  obtain ⟨-, h2, h3⟩ := hasDerivWithinAt_iteratedDerivWithin_of_contDiffOn_three (by linarith) hy3
  have h2' : ∀ s ∈ Icc t₀ (t₀ + T), HasDerivWithinAt (fun s => f s (y s))
      (iteratedDerivWithin 2 y (Icc t₀ (t₀ + T)) s) (Icc t₀ (t₀ + T)) s := fun s hs =>
    (h2 s hs).congr (fun s' hs' => (derivWithin_eq_of_cauchyProblem hT hy hs').symm)
      (derivWithin_eq_of_cauchyProblem hT hy hs).symm
  have hlip' : ∀ t ∈ Icc t₀ (t₀ + T), LipschitzWith ⟨L, hL⟩ (f t) := fun t ht =>
    LipschitzWith.of_dist_le_mul fun y₁ y₂ => by
      rw [Real.dist_eq, Real.dist_eq]
      exact hlip t ht y₁ y₂
  refine ⟨fun h hh n hn => ?_, hasOrderFor_heun hy.2 h2' h3 hM₂ hM₃ hlip'⟩
  exact norm_lte_heun_le hy.2 h2' h3 hM₂ hM₃ hlip' hh (node_mem_Icc_of_lt hh hn)
    (node_add_mem_Icc_of_lt hh hn)

/-- **Exercise 11.2** of [quarteroni2000numerical]. The Crank–Nicolson method (11.9) has order $2$.
Let $T > 0$, and let $y \in C^3([t_0, t_0 + T])$ solve the Cauchy problem $y' = f(t, y)$,
$y(t_0) = y_0$ on $[t_0, t_0 + T]$, with $|y'''| \le M_3$ on $[t_0, t_0 + T]$. Then:

* for every $h > 0$ and every $n < N_h = \lfloor T / h \rfloor$, the local truncation error
  satisfies $|\tau_{n+1}(h)| \le (h^2/12) M_3$;
* the Crank–Nicolson method has order $2$ (11.14) along $y$, so (11.9) agrees with (11.90) up to
  $O(h^2)$.

The bound is the norm form of (11.90),
$$\frac{y_{n+1} - y_n}{h} = \frac{f(t_n, y_n) + f(t_{n+1}, y_{n+1})}{2} - \frac{h^2}{12}
  y'''(\xi_n),$$
where the source writes the remainder as $f''(\xi_n, y(\xi_n))$, the second derivative of
$s \mapsto f(s, y(s)) = y'(s)$. The mean-value form with the intermediate point $\xi_n$ is not
formalized. The proof specializes `ODE.OneStep.norm_lte_crankNicolson_le` and
`ODE.OneStep.hasOrderFor_crankNicolson`.

**Reading.** States the order and the local error bound along the supplied $C^3$ solution under
the indicated derivative bounds. For Crank–Nicolson the book gives a mean-value expression with
an intermediate point. -/
theorem exercise_11_2 (hT : 0 < T) (hy : cauchyProblem f t₀ y₀ (Icc t₀ (t₀ + T)) y)
    (hy3 : ContDiffOn ℝ 3 y (Icc t₀ (t₀ + T))) {M₃ : ℝ}
    (hM₃ : ∀ s ∈ Icc t₀ (t₀ + T), |iteratedDerivWithin 3 y (Icc t₀ (t₀ + T)) s| ≤ M₃) :
    (∀ h : ℝ, 0 < h → ∀ n, n < gridCount T h →
      |equation_11_12 (equation_11_9 f) h y t₀ n| ≤ h ^ 2 / 12 * M₃) ∧
    equation_11_14 (equation_11_9 f) t₀ T y 2 := by
  obtain ⟨-, h2, h3⟩ := hasDerivWithinAt_iteratedDerivWithin_of_contDiffOn_three (by linarith) hy3
  have h2' : ∀ s ∈ Icc t₀ (t₀ + T), HasDerivWithinAt (fun s => f s (y s))
      (iteratedDerivWithin 2 y (Icc t₀ (t₀ + T)) s) (Icc t₀ (t₀ + T)) s := fun s hs =>
    (h2 s hs).congr (fun s' hs' => (derivWithin_eq_of_cauchyProblem hT hy hs').symm)
      (derivWithin_eq_of_cauchyProblem hT hy hs).symm
  refine ⟨fun h hh n hn => ?_, hasOrderFor_crankNicolson hy.2 h2' h3 hM₃⟩
  exact norm_lte_crankNicolson_le hy.2 h2' h3 hM₃ hh (node_mem_Icc_of_lt hh hn)
    (node_add_mem_Icc_of_lt hh hn)

/-! ### Exercise 3: a difference equation with complex conjugate roots -/

/-- The closed-form solution of Exercise 11.3:
$$u_n = 2^n \Big(\frac{n}{4} - 1\Big) + 2^{(n-2)/2} \sin\Big(\frac{n\pi}{4}\Big) + n + 2.$$

**Correction.** The sinusoidal term uses $\sin(n\pi/4)$. The printed $\sin(\pi/4)$ would
already violate the value $u_0=1$. -/
noncomputable def exercise_11_3_sol (n : ℕ) : ℝ :=
  2 ^ n * (n / 4 - 1) + (2 : ℝ) ^ (((n : ℝ) - 2) / 2) * Real.sin (n * Real.pi / 4) + n + 2

/-- The difference equation of Exercise 11.3 is an equation (11.28). A sequence $(u_n)$ solves
(11.28) with the coefficients $\alpha = (8, -16, 14, -6)$ and the right-hand side
$\varphi_m = m - 4$ if and only if
$$u_{n+4} - 6u_{n+3} + 14u_{n+2} - 16u_{n+1} + 8u_n = n \qquad \text{for every } n.$$
-/
theorem exercise_11_3_iff (u : ℕ → ℝ) :
    (equation_11_28 (![8, -16, 14, -6] : Fin 4 → ℝ)).IsSolutionWith (fun m => (m : ℝ) - 4) u ↔
      ∀ n, u (n + 4) - 6 * u (n + 3) + 14 * u (n + 2) - 16 * u (n + 1) + 8 * u n = n := by
  rw [equation_11_28_iff]
  refine forall_congr' fun n => ?_
  simp only [Fin.sum_univ_four, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero,
    Fin.val_one, Fin.val_two, add_zero]
  have e : ((3 : Fin 4) : ℕ) = 3 := rfl
  rw [e]
  push_cast
  constructor <;> intro H <;> linear_combination H

/-- The power in the solution of Exercise 11.3 is $2^{(n-2)/2} = (\sqrt{2})^n / 2$ for
$n \in \mathbb{N}$. -/
theorem exercise_11_3_rpow (n : ℕ) : (2 : ℝ) ^ (((n : ℝ) - 2) / 2) = Real.sqrt 2 ^ n / 2 := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
    show ((n : ℝ) - 2) / 2 = 1 / 2 * n - 1 by ring, Real.rpow_sub (by norm_num), Real.rpow_one]

/-- The imaginary part of $(1 + i)^n$, used in Exercise 11.3, is $\operatorname{Im}(1 + i)^n =
(\sqrt{2})^n \sin(n\pi/4)$, because $(1 + i)^n = (\sqrt{2})^n e^{in\pi/4}$. It is the real
solution of the homogeneous equation that belongs to the conjugate pair of roots $1 \pm i$. -/
theorem exercise_11_3_im (n : ℕ) :
    ((1 + Complex.I) ^ n).im = Real.sqrt 2 ^ n * Real.sin (n * Real.pi / 4) := by
  have h2 : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num
  have h1 : (1 + Complex.I) = (Real.sqrt 2 : ℂ) * Complex.exp ((Real.pi / 4 : ℝ) * Complex.I) := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_four,
      Real.sin_pi_div_four]
    push_cast
    linear_combination (-(1 + Complex.I) / 2) * h2
  rw [h1, mul_pow, ← Complex.exp_nat_mul, ← Complex.ofReal_pow, ← Complex.ofReal_natCast,
    ← mul_assoc, ← Complex.ofReal_mul, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im,
    mul_div_assoc]

/-- The sequence $w_n = 2^{(n-2)/2} \sin(n\pi/4)$ of Exercise 11.3 solves the homogeneous equation:
$$w_{n+4} - 6w_{n+3} + 14w_{n+2} - 16w_{n+1} + 8w_n = 0 \qquad \text{for every } n.$$

The sequence is $\operatorname{Im}(1 + i)^n / 2$, and $1 + i$ is a root of the characteristic
polynomial $(r - 2)^2 (r^2 - 2r + 2)$. -/
theorem exercise_11_3_sin_rec (n : ℕ) :
    let w : ℕ → ℝ := fun n => (2 : ℝ) ^ (((n : ℝ) - 2) / 2) * Real.sin (n * Real.pi / 4)
    w (n + 4) - 6 * w (n + 3) + 14 * w (n + 2) - 16 * w (n + 1) + 8 * w n = 0 := by
  intro w
  have hw : ∀ m, w m = ((1 + Complex.I) ^ m).im / 2 := fun m => by
    simp only [w]
    rw [exercise_11_3_rpow, exercise_11_3_im]
    ring
  have hz : (1 + Complex.I) ^ (n + 4) - 6 * (1 + Complex.I) ^ (n + 3) +
      14 * (1 + Complex.I) ^ (n + 2) - 16 * (1 + Complex.I) ^ (n + 1) + 8 * (1 + Complex.I) ^ n
      = 0 := by
    have hI : Complex.I ^ 2 = -1 := Complex.I_sq
    linear_combination (1 + Complex.I) ^ n * (Complex.I - 1) ^ 2 * hI
  have := congrArg Complex.im hz
  simp only [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.re_ofNat, Complex.im_ofNat,
    zero_mul, add_zero, Complex.zero_im] at this
  simp only [hw]
  linarith

/-- **Exercise 11.3** of [quarteroni2000numerical]. The solution of
$$u_{n+4} - 6u_{n+3} + 14u_{n+2} - 16u_{n+1} + 8u_n = n$$
with $u_0 = 1$, $u_1 = 2$, $u_2 = 3$ and $u_3 = 4$ is
$$u_n = 2^n \Big(\frac{n}{4} - 1\Big) + 2^{(n-2)/2} \sin\Big(\frac{n\pi}{4}\Big) + n + 2.$$
That is, this sequence solves the equation and has these starting values, and every solution
with these starting values is equal to it.

**Typo.** The source prints $\sin(\pi/4)$ in place of $\sin(n\pi/4)$.

The equation is (11.28) with $\alpha = (8, -16, 14, -6)$ and $\varphi_m = m - 4$, as in
`QuarteroniSaccoSaleri.Chapter11.exercise_11_3_iff`. The characteristic polynomial is
$(r - 2)^2 (r^2 - 2r + 2)$. The double root $2$ gives the solutions $2^n$ and $n 2^n$, the
conjugate pair $1 \pm i = \sqrt{2} e^{\pm i\pi/4}$ gives the real solution
$2^{n/2} \sin(n\pi/4)$, and $n + 2$ is a particular solution. -/
theorem exercise_11_3 :
    (equation_11_28 (![8, -16, 14, -6] : Fin 4 → ℝ)).IsSolutionWith (fun m => (m : ℝ) - 4)
      exercise_11_3_sol ∧
    (exercise_11_3_sol 0 = 1 ∧ exercise_11_3_sol 1 = 2 ∧ exercise_11_3_sol 2 = 3 ∧
      exercise_11_3_sol 3 = 4) ∧
    ∀ u : ℕ → ℝ,
      (equation_11_28 (![8, -16, 14, -6] : Fin 4 → ℝ)).IsSolutionWith (fun m => (m : ℝ) - 4) u →
      u 0 = 1 → u 1 = 2 → u 2 = 3 → u 3 = 4 → ∀ n, u n = exercise_11_3_sol n := by
  have hrec : ∀ n, exercise_11_3_sol (n + 4) - 6 * exercise_11_3_sol (n + 3) +
      14 * exercise_11_3_sol (n + 2) - 16 * exercise_11_3_sol (n + 1) + 8 * exercise_11_3_sol n
      = n := by
    intro n
    have hs := exercise_11_3_sin_rec n
    simp only at hs
    simp only [exercise_11_3_sol]
    push_cast at hs ⊢
    linear_combination hs
  have hinit : exercise_11_3_sol 0 = 1 ∧ exercise_11_3_sol 1 = 2 ∧ exercise_11_3_sol 2 = 3 ∧
      exercise_11_3_sol 3 = 4 := by
    have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    have h3 : Real.sin (3 * Real.pi / 4) = Real.sqrt 2 / 2 := by
      rw [show 3 * Real.pi / 4 = Real.pi - Real.pi / 4 by ring, Real.sin_pi_sub,
        Real.sin_pi_div_four]
    have h2 : Real.sin (2 * Real.pi / 4) = 1 := by
      rw [show 2 * Real.pi / 4 = Real.pi / 2 by ring, Real.sin_pi_div_two]
    simp only [exercise_11_3_sol, exercise_11_3_rpow]
    refine ⟨?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num [Real.sin_pi_div_four]
      nlinarith [hsq]
    · norm_num [h2]
    · norm_num [h3]
      nlinarith [hsq]
  refine ⟨(exercise_11_3_iff _).2 hrec, hinit, fun u hu h0 h1 h2 h3 => ?_⟩
  rw [exercise_11_3_iff] at hu
  obtain ⟨g0, g1, g2, g3⟩ := hinit
  have key : ∀ n, u n = exercise_11_3_sol n ∧ u (n + 1) = exercise_11_3_sol (n + 1) ∧
      u (n + 2) = exercise_11_3_sol (n + 2) ∧ u (n + 3) = exercise_11_3_sol (n + 3) := by
    intro n
    induction n with
    | zero => exact ⟨by rw [h0, g0], by rw [h1, g1], by rw [h2, g2], by rw [h3, g3]⟩
    | succ n ih =>
      obtain ⟨e0, e1, e2, e3⟩ := ih
      refine ⟨e1, e2, e3, ?_⟩
      have hu' := hu n
      have hg' := hrec n
      rw [show n + 1 + 3 = n + 4 from rfl]
      linear_combination hu' - hg' + 6 * e3 - 14 * e2 + 16 * e1 - 8 * e0
  exact fun n => (key n).1

/-! ### Exercises 4–5: simple roots -/

/-- **Exercise 11.4** of [quarteroni2000numerical]. Let $K$ be a field, let $\alpha \in K^k$, and
let $r_1, \dots, r_k \in K$ be distinct roots of the characteristic polynomial $\Pi$ (11.30) of
the difference equation (11.28), so that they are its $k$ simple roots. Let $(u_n)$ solve the
homogeneous equation (11.28). Then:

* there is exactly one $\gamma \in K^k$ with $u_n = \sum_{j=1}^k \gamma_j r_j^n$ for every $n$,
  which is the form (11.32);
* every such $\gamma$ solves the Vandermonde system $\sum_{i=1}^k \gamma_i r_i^j = u_j$ for
  $j = 0, \dots, k - 1$.

The proof specializes `LinearRecurrence.eq_sum_smul_pow_of_injective_roots`.

**Generalization.** Works over any field. For the determinant claim it suffices that the matrix
arguments are distinct. -/
theorem exercise_11_4 {K : Type*} [Field K] {k : ℕ} (α : Fin k → K) {r : Fin k → K}
    (hr : Function.Injective r) (hroot : ∀ j, (equation_11_30 α).IsRoot (r j)) {u : ℕ → K}
    (hu : (equation_11_28 α).IsSolution u) :
    (∃! γ : Fin k → K, ∀ n, u n = ∑ j, γ j * r j ^ n) ∧
      ∀ γ : Fin k → K, (∀ n, u n = ∑ j, γ j * r j ^ n) →
        ∀ j : Fin k, ∑ i, γ i * r i ^ (j : ℕ) = u j := by
  have hroot' : ∀ j, (equation_11_28 α).charPoly.IsRoot (r j) := fun j => by
    rw [← equation_11_30_eq]
    exact hroot j
  refine ⟨?_, fun γ hγ j => (hγ j).symm⟩
  have := (equation_11_28 α).eq_sum_smul_pow_of_injective_roots hr hroot' hu
  simp only [smul_eq_mul] at this
  exact this

/-- **Exercise 11.5** of [quarteroni2000numerical]. Let $K$ be a field and let
$r_1, \dots, r_k \in K$ be distinct. Then the matrix $R = (r_m^i)_{i, m}$ of (11.37) is
nonsingular: $\det R \neq 0$.

The source takes the $r_m$ to be the simple roots of the characteristic polynomial; the
statement does not need this. $R$ is the transpose of the Vandermonde matrix of
$r_1, \dots, r_k$, whose determinant $\prod_{i < j} (r_j - r_i)$ is not zero. The proof
specializes `LinearRecurrence.det_vandermonde_transpose_ne_zero` and
`Matrix.det_vandermonde_ne_zero_iff`.

**Generalization.** Works over any field. For the determinant claim it suffices that the matrix
arguments are distinct. -/
theorem exercise_11_5 {K : Type*} [Field K] {k : ℕ} {r : Fin k → K} (hr : Function.Injective r) :
    (equation_11_37_matrix r).det ≠ 0 := by
  rw [equation_11_37_matrix_eq]
  exact LinearRecurrence.det_vandermonde_transpose_ne_zero hr

/-! ### Exercise 12: the two-stage explicit methods -/

/-- **Equation (11.91)** of [quarteroni2000numerical]. The **modified Euler method** is
$$u_{n+1} = u_n + h f\Big(t_n + \frac{h}{2},\ u_n + \frac{h}{2} f_n\Big).$$

The definition is the increment of the explicit tableau `ODE.ButcherTableau.modifiedEuler`. -/
noncomputable def equation_11_91 (f : ℝ → ℝ → ℝ) : OneStep.Increment ℝ :=
  ButcherTableau.modifiedEuler.explicitIncrement f

/-- **Equation (11.91)** of [quarteroni2000numerical], unfolded. The increment of the modified Euler
method at $(t, u)$ with step $h$ is $f(t + h/2, u + (h/2) f(t, u))$. -/
theorem equation_11_91_apply (f : ℝ → ℝ → ℝ) (t u v h : ℝ) :
    equation_11_91 f t u v h = f (t + h / 2) (u + h / 2 * f t u) := by
  rw [equation_11_91, ButcherTableau.explicitIncrement_modifiedEuler, smul_eq_mul]

/-- **Exercise 11.12** of [quarteroni2000numerical]. Heun's method (11.10) is the explicit two-stage
Runge–Kutta method with Butcher array
$$c = (0, 1), \qquad A = \begin{bmatrix} 0 & 0 \\ 1 & 0 \end{bmatrix}, \qquad b =
  \Big(\frac{1}{2}, \frac{1}{2}\Big),$$
and the modified Euler method (11.91) is the explicit two-stage Runge–Kutta method with
$$c = \Big(0, \frac{1}{2}\Big), \qquad A = \begin{bmatrix} 0 & 0 \\ 1/2 & 0 \end{bmatrix},
  \qquad b = (0, 1).$$
In both cases the tableau is explicit and satisfies (11.72), its increment (11.70) is the
increment of the method, and the orbits of (11.71) are the orbits of the method.

The proof specializes `ODE.ButcherTableau.explicitIncrement_heun` and
`ODE.ButcherTableau.explicitIncrement_modifiedEuler`. -/
theorem exercise_11_12 :
    (ButcherTableau.heun.c = ![0, 1] ∧ ButcherTableau.heun.A = !![0, 0; 1, 0] ∧
      ButcherTableau.heun.b = ![1 / 2, 1 / 2] ∧ equation_11_71_explicit ButcherTableau.heun ∧
      equation_11_72 ButcherTableau.heun ∧
      equation_11_70_increment ButcherTableau.heun f = equation_11_10 f ∧
      ∀ u : ℕ → ℝ, equation_11_71 ButcherTableau.heun f h t₀ u ↔
        OneStep.IsOrbit (OneStep.ofIncrement (equation_11_10 f)) h t₀ u) ∧
    (ButcherTableau.modifiedEuler.c = ![0, 1 / 2] ∧
      ButcherTableau.modifiedEuler.A = !![0, 0; 1 / 2, 0] ∧
      ButcherTableau.modifiedEuler.b = ![0, 1] ∧
      equation_11_71_explicit ButcherTableau.modifiedEuler ∧
      equation_11_72 ButcherTableau.modifiedEuler ∧
      equation_11_70_increment ButcherTableau.modifiedEuler f = equation_11_91 f ∧
      ∀ u : ℕ → ℝ, equation_11_71 ButcherTableau.modifiedEuler f h t₀ u ↔
        OneStep.IsOrbit (OneStep.ofIncrement (equation_11_91 f)) h t₀ u) := by
  refine ⟨⟨rfl, rfl, rfl, ButcherTableau.heun_isExplicit, ButcherTableau.heun_isRowSum,
    ButcherTableau.explicitIncrement_heun f, fun u => ?_⟩,
    ⟨rfl, rfl, rfl, ButcherTableau.modifiedEuler_isExplicit, ButcherTableau.modifiedEuler_isRowSum,
      rfl, fun u => ?_⟩⟩
  · rw [equation_11_71, ButcherTableau.stepRel_eq_ofIncrement _ ButcherTableau.heun_isExplicit,
      ButcherTableau.explicitIncrement_heun]
    rfl
  · rw [equation_11_71,
      ButcherTableau.stepRel_eq_ofIncrement _ ButcherTableau.modifiedEuler_isExplicit]
    rfl

end QuarteroniSaccoSaleri.Chapter11
