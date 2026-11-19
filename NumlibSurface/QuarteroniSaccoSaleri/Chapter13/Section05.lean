/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.PDE.Transport

/-!
# Quarteroni, Sacco and Saleri, Section 13.5: A scalar transport problem

This module formalizes Section 13.5 of [quarteroni2000numerical], the scalar transport equation. The
Cauchy problem (13.26), $u_t + a u_x = 0$ on $\mathbb{R} \times [0, \infty)$ with
$u(\cdot, 0) = u_0$, has the travelling wave $u(x, t) = u_0(x - at)$ as its only solution. The
reason is the characteristic curves (13.27), the integral curves $x' = a$ of the speed field: a
solution is constant along them, because $\frac{d}{dt} u(x(t), t) = u_t + u_x x' = 0$ there. For the
general problem (13.28), $u_t + a u_x + a_0 u = f$ with coefficients that depend on $(x, t)$, the
same chain rule gives the ordinary differential equation $\frac{d}{dt} u(x(t), t) = f - a_0 u$ along
a characteristic. Example 13.3 is the Burgers equation (13.29) with a piecewise linear datum: the
characteristic from $(x_0, 0)$ is the line $x_0 + t u_0(x_0)$, and these lines are pairwise disjoint
exactly while $t < 1$.

The definitions and theorems specialize `Transport.IsSolution`, `Transport.IsCharacteristic` and
their theorems in the backbone module `Numlib.Analysis.PDE.Transport`.

## Main definitions

* (13.26), `QuarteroniSaccoSaleri.Chapter13.equation_13_26`: a classical solution of
  $u_t + a u_x = 0$ with the datum $u_0$.
* (13.27), `QuarteroniSaccoSaleri.Chapter13.equation_13_27`: the characteristic curve
  $x' = a(x, t)$, $x(0) = x_0$.
* Example 13.3, `QuarteroniSaccoSaleri.Chapter13.burgersDatum`: the piecewise linear initial datum
  of the Burgers equation.

## Main results

* Section 13.5, `QuarteroniSaccoSaleri.Chapter13.equation_13_26_solution`: for a differentiable
  datum, $u(x, t) = u_0(x - at)$ is the unique solution of (13.26).
* Section 13.5, `QuarteroniSaccoSaleri.Chapter13.equation_13_27_line`: for a constant speed $a$, the
  characteristics are the lines $x(t) = x_0 + at$.
* Section 13.5, `QuarteroniSaccoSaleri.Chapter13.equation_13_27_const_along`: a solution of (13.26)
  satisfies $u(x_0 + at, t) = u_0(x_0)$.
* (13.28), `QuarteroniSaccoSaleri.Chapter13.equation_13_28`: along a characteristic, a solution of
  the general problem satisfies $\frac{d}{dt} u(x(t), t) = f - a_0 u$.
* Example 13.3, `QuarteroniSaccoSaleri.Chapter13.burgersDatum_sub_le`: the datum is nonincreasing
  and $1$-Lipschitz.
* Example 13.3, `QuarteroniSaccoSaleri.Chapter13.example_13_3`: the characteristics are the lines
  $x_0 + t u_0(x_0)$, and the map $x_0 \mapsto x_0 + t u_0(x_0)$ is injective if and only if
  $t < 1$.

## Implementation notes

* A solution is classical on the closed half plane $\mathbb{R} \times [0, \infty)$: the partial
  derivatives are derivatives within that set, so they are one-sided at $t = 0$. The same holds for
  the derivative of a characteristic at $t = 0$.

## Deviations from the source

* **Equations (13.26)–(13.28)** (reading). Classical transport solutions use full within
  differentiability in space and time on the closed half-plane and satisfy the equation at time
  zero. The characteristic definitions and derivative identities likewise include time zero. See
  `QuarteroniSaccoSaleri.Chapter13.equation_13_26` and
  `QuarteroniSaccoSaleri.Chapter13.equation_13_28`.

## Not formalized

* Inflow points. The source treats them in prose.
* Weak solutions. The source treats them in prose.
-/

open Set

namespace QuarteroniSaccoSaleri.Chapter13

/-! ### The Cauchy problem (13.26) -/

/-- **Equation (13.26)** of [quarteroni2000numerical]. Let $a \in \mathbb{R}$ and
$u_0 : \mathbb{R} \to \mathbb{R}$. A function $u : \mathbb{R} \times \mathbb{R} \to \mathbb{R}$
is a **classical solution** of the Cauchy problem
$$u_t + a u_x = 0 \quad \text{on } \mathbb{R} \times [0, \infty), \qquad u(x, 0) = u_0(x),$$
if $u$ has partial derivatives $u_x$ and $u_t$ on $\mathbb{R} \times [0, \infty)$ that satisfy
the equation at every point of that set, and the initial condition holds for all $x$.

The definition is `Transport.IsSolution` with the constant speed $a$, and with zero coefficient
$a_0$ and zero source $f$.

**Reading.** Full within differentiability and the PDE are required on the closed half-plane,
including at $t=0$. -/
def equation_13_26 (a : ℝ) (u₀ : ℝ → ℝ) (u : ℝ → ℝ → ℝ) : Prop :=
  Transport.IsSolution (fun _ _ => a) 0 0 u₀ u

/-- **Section 13.5** of [quarteroni2000numerical], the solution of (13.26). Let $a \in \mathbb{R}$
and let $u_0 : \mathbb{R} \to \mathbb{R}$ be differentiable. Then the travelling wave
$u(x, t) = u_0(x - at)$ is a solution of (13.26), and every solution $u$ of (13.26) satisfies
$u(x, t) = u_0(x - at)$ for all $x$ and all $t \ge 0$.

**Reading.** The initial datum is differentiable, and uniqueness is among the within-
differentiable solutions of `QuarteroniSaccoSaleri.Chapter13.equation_13_26`. -/
theorem equation_13_26_solution {a : ℝ} {u₀ : ℝ → ℝ} (hu₀ : Differentiable ℝ u₀) :
    equation_13_26 a u₀ (fun x t => u₀ (x - a * t)) ∧
      ∀ u : ℝ → ℝ → ℝ, equation_13_26 a u₀ u → ∀ (x t : ℝ), 0 ≤ t → u x t = u₀ (x - a * t) :=
  ⟨Transport.isSolution_comp_sub hu₀, fun _ hu x _ ht => hu.eq_comp_sub x ht⟩

/-! ### The characteristic curves (13.27) -/

/-- **Equation (13.27)** of [quarteroni2000numerical]. Let $a : \mathbb{R} \times \mathbb{R} \to
\mathbb{R}$ and $x_0 \in \mathbb{R}$. A function $x : \mathbb{R} \to \mathbb{R}$ is the
**characteristic curve** of the speed field $a$ through $x_0$ if $x(0) = x_0$ and
$$x'(t) = a(x(t), t) \quad \text{for all } t \ge 0.$$

The derivative is taken within $[0, \infty)$, so it is one-sided at $t = 0$. The definition is
`Transport.IsCharacteristic`.

**Generalization.** The speed may vary with position and time, and the within derivative is
required also at time zero. -/
def equation_13_27 (a : ℝ → ℝ → ℝ) (x₀ : ℝ) (x : ℝ → ℝ) : Prop :=
  Transport.IsCharacteristic a x₀ x

/-- **Section 13.5** of [quarteroni2000numerical], the characteristics of a constant speed. Let
$a, x_0 \in \mathbb{R}$. Then $x(t) = x_0 + at$ is a characteristic curve (13.27) of the
constant speed field $a$ through $x_0$, and every such characteristic curve $x$ satisfies
$x(t) = x_0 + at$ for all $t \ge 0$. -/
theorem equation_13_27_line (a x₀ : ℝ) :
    equation_13_27 (fun _ _ => a) x₀ (fun t => x₀ + a * t) ∧
      ∀ x : ℝ → ℝ, equation_13_27 (fun _ _ => a) x₀ x → ∀ t : ℝ, 0 ≤ t → x t = x₀ + a * t :=
  ⟨Transport.characteristic_const a x₀, fun _ hx _ ht => hx.eq_of_const ht⟩

/-- **Section 13.5** of [quarteroni2000numerical], constancy along the characteristics. Let
$a \in \mathbb{R}$, $u_0 : \mathbb{R} \to \mathbb{R}$, and let $u$ be a solution of (13.26).
Then for every $x_0 \in \mathbb{R}$ and every $t \ge 0$,
$$u(x_0 + at, t) = u_0(x_0).$$

This is the statement $\frac{d}{dt} u(x(t), t) = 0$ along the characteristic $x(t) = x_0 + at$. -/
theorem equation_13_27_const_along {a : ℝ} {u₀ : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hu : equation_13_26 a u₀ u) (x₀ : ℝ) {t : ℝ} (ht : 0 ≤ t) : u (x₀ + a * t) t = u₀ x₀ :=
  hu.comp_characteristic_const (Transport.characteristic_const a x₀) ht

/-- **Equation (13.28)** of [quarteroni2000numerical]. Let $a, a_0, f : \mathbb{R} \times \mathbb{R}
\to \mathbb{R}$ and $u_0 : \mathbb{R} \to \mathbb{R}$, and let $u$ be a classical solution of
the general transport problem $u_t + a u_x + a_0 u = f$ on $\mathbb{R} \times [0, \infty)$ with
$u(\cdot, 0) = u_0$. Let $x$ be the characteristic curve (13.27) of $a$ through some $x_0$. Then
for every $t \ge 0$ the function $s \mapsto u(x(s), s)$ has the derivative
$$\frac{d}{dt} u(x(t), t) = f(x(t), t) - a_0(x(t), t)\, u(x(t), t)$$
within $[0, \infty)$ at $t$.

The solution is `Transport.IsSolution a a₀ f u₀ u`.

**Reading.** The characteristic identity uses a within derivative on $[0,\infty)$, including at
time zero. -/
theorem equation_13_28 {a a₀ f : ℝ → ℝ → ℝ} {u₀ : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hu : Transport.IsSolution a a₀ f u₀ u) {x₀ : ℝ} {x : ℝ → ℝ}
    (hx : equation_13_27 a x₀ x) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s => u (x s) s) (f (x t) t - a₀ (x t) t * u (x t) t) (Ici 0) t :=
  hu.hasDerivAt_comp_characteristic hx ht

/-! ### Example 13.3, the Burgers equation -/

/-- **Example 13.3** of [quarteroni2000numerical], the initial datum. The datum of the Burgers
equation is
$$u_0(x) = \begin{cases} 1, & x \le 0, \\ 1 - x, & 0 < x \le 1, \\ 0, & x > 1. \end{cases}$$
-/
noncomputable def burgersDatum (x : ℝ) : ℝ := if x ≤ 0 then 1 else if x ≤ 1 then 1 - x else 0

/-- **Example 13.3** of [quarteroni2000numerical], monotonicity of the datum. For real numbers
$x \le y$,
$$0 \le u_0(x) - u_0(y) \le y - x,$$
so the datum $u_0$ is nonincreasing and $1$-Lipschitz. -/
theorem burgersDatum_sub_le {x y : ℝ} (hxy : x ≤ y) :
    0 ≤ burgersDatum x - burgersDatum y ∧ burgersDatum x - burgersDatum y ≤ y - x := by
  unfold burgersDatum
  split_ifs <;> constructor <;> linarith

/-- **Example 13.3** of [quarteroni2000numerical] (the Burgers equation (13.29)). Let $u_0$ be the
datum of Example 13.3. Then:

* for every $x_0 \in \mathbb{R}$, the line $x(t) = x_0 + u_0(x_0) t$ is the characteristic curve
  (13.27) through $x_0$ of the constant speed $u_0(x_0)$;
* for $0 \le t < 1$, the map $x_0 \mapsto x_0 + t u_0(x_0)$ is injective, so the characteristics
  do not meet before time $1$;
* for $t \ge 1$, this map is not injective.

The speed $u_0(x_0)$ is the value of the solution, which is constant along the characteristic.
For $t \ge 1$ the characteristics from $x_0 = 0$ and $x_0 = t$ meet at time $t$; at $t = 1$
these are the characteristics from $0$ and $1$. -/
theorem example_13_3 :
    (∀ x₀ : ℝ, equation_13_27 (fun _ _ => burgersDatum x₀) x₀
        (fun t => x₀ + burgersDatum x₀ * t)) ∧
      (∀ t : ℝ, 0 ≤ t → t < 1 → Function.Injective fun x₀ : ℝ => x₀ + t * burgersDatum x₀) ∧
      ∀ t : ℝ, 1 ≤ t → ¬Function.Injective fun x₀ : ℝ => x₀ + t * burgersDatum x₀ := by
  refine ⟨fun x₀ => Transport.characteristic_const _ x₀, fun t ht0 ht1 => ?_, fun t ht => ?_⟩
  · refine StrictMono.injective fun x y hxy => ?_
    obtain ⟨h1, h2⟩ := burgersDatum_sub_le hxy.le
    nlinarith [mul_le_mul_of_nonneg_left h2 ht0]
  · intro h
    have h0 : burgersDatum 0 = 1 := by unfold burgersDatum; norm_num
    have ht0 : burgersDatum t = 0 := by
      unfold burgersDatum
      split_ifs with h2 h3
      · linarith
      · linarith
      · rfl
    have := h (a₁ := (0 : ℝ)) (a₂ := t) (by simp [h0, ht0])
    linarith

end QuarteroniSaccoSaleri.Chapter13
