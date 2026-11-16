/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Numlib.Analysis.Calculus.ContDiffOnIcc
import Numlib.ODE.RungeKutta
import NumlibSurface.QuarteroniSaccoSaleri.Chapter11.Section01
import NumlibSurface.QuarteroniSaccoSaleri.Chapter11.Section02

/-!
# Quarteroni, Sacco and Saleri, Section 11.3: Analysis of One-Step Methods

This module formalizes Section 11.3 of [quarteroni2000numerical]. A one-step method for the Cauchy
problem $y' = f(t, y)$, $y(t_0) = y_0$, on $[t_0, t_0 + T]$ computes
$u_{n+1} = u_n + h \Phi(t_n, u_n, f_n; h)$ (11.11) on the nodes $t_n = t_0 + nh$, $0 \le n \le N_h$,
where $\Phi$ is the increment function. Along the exact solution $y$, the local truncation error
$\tau_{n+1}(h)$ is defined by $y_{n+1} = y_n + h \Phi(t_n, y_n, f(t_n, y_n); h) + h \tau_{n+1}(h)$
(11.12), and the global truncation error is $\tau(h) = \max_n |\tau_{n+1}(h)|$. The method is
consistent if $\tau(h) \to 0$ and has order $p$ if $\tau(h) = O(h^p)$ (11.14). The section proves
the consistency criterion (11.13) and the order $1$ of forward Euler, then zero-stability under the
Lipschitz condition (11.18) on $\Phi$ (Theorem 11.1, with the discrete Gronwall lemma, Lemma 11.2)
and convergence of consistent zero-stable methods (Theorem 11.2, with the estimate (11.20) and the
forward Euler bound (11.22)).

The last part treats absolute stability. The test problem (11.24) is $y' = \lambda y$, $y(0) = 1$,
with $\lambda \in \mathbb{C}$. A method is absolutely stable for a step $h$ if its solution of the
test problem tends to $0$ (Definition 11.6), and the region of absolute stability is the set
$\mathcal{A}$ of the values $z = h\lambda$ for which this holds (11.26). The module computes
$\mathcal{A}$ for forward Euler (11.27), backward Euler, Crank–Nicolson and Heun's method, proves
Examples 11.1 and 11.2, decides which of these methods are A-stable, and proves Remark 11.2 for the
explicit Runge–Kutta methods. The proofs specialize the backbone modules `Numlib.ODE.OneStep` (at
$E = \mathbb{R}$, and at $E = \mathbb{C}$ for the test problem),
`Numlib.Analysis.ODE.DiscreteGronwall` and `Numlib.ODE.RungeKutta`.

## Main definitions

* Equation (11.11), `QuarteroniSaccoSaleri.Chapter11.equation_11_11`: $u$ is the sequence that the
  one-step method with increment $\Phi$ computes from $u_0 = y_0$.
* Equation (11.12), `QuarteroniSaccoSaleri.Chapter11.equation_11_12`: the local truncation error
  $\tau_{n+1}(h)$.
* Section 11.3, `QuarteroniSaccoSaleri.Chapter11.globalTruncationError`: the global truncation error
  $\tau(h) = \max_n |\tau_{n+1}(h)|$.
* Section 11.3, `QuarteroniSaccoSaleri.Chapter11.consistent`: the method is consistent along $y$ if
  $\tau(h) \to 0$ as $h \to 0$.
* Equation (11.14), `QuarteroniSaccoSaleri.Chapter11.equation_11_14`: the method has order $p$ along
  $y$ if $\tau(h) = O(h^p)$.
* Definition 11.4, `QuarteroniSaccoSaleri.Chapter11.definition_11_4`: zero-stability, by the
  perturbed recursion (11.16) and the estimate (11.15).
* Equation (11.18), `QuarteroniSaccoSaleri.Chapter11.equation_11_18`: $\Phi$ is Lipschitz in $u$
  with a constant $\Lambda$ that does not depend on $h$ or $t$.
* Definition 11.5, `QuarteroniSaccoSaleri.Chapter11.definition_11_5`: convergence,
  $|u_n - y_n| \le C(h)$ with $C(h) \to 0$.
* Definition 11.5, `QuarteroniSaccoSaleri.Chapter11.definition_11_5_order`: convergence with order
  $p$, $|u_n - y_n| \le \mathcal{C} h^p$.
* Equation (11.24), `QuarteroniSaccoSaleri.Chapter11.testProblem`: the test problem
  $y' = \lambda y$.
* Definition 11.6, `QuarteroniSaccoSaleri.Chapter11.definition_11_6`: absolute stability for
  $\lambda$ and the step $h$.
* Equation (11.26), `QuarteroniSaccoSaleri.Chapter11.equation_11_26`: the region of absolute
  stability $\mathcal{A}$.
* Section 11.3.3, `QuarteroniSaccoSaleri.Chapter11.aStable`: A-stability,
  $\mathcal{A} \cap \mathbb{C}^- = \mathbb{C}^-$.

## Main results

* Equation (11.13), `QuarteroniSaccoSaleri.Chapter11.equation_11_13`: if
  $\Phi(t, y(t), \cdot\,; h) \to f(t, y(t))$ uniformly in $t$ as $h \to 0$, the method is
  consistent.
* Section 11.3, `QuarteroniSaccoSaleri.Chapter11.forwardEuler_order_one_lte`: for forward Euler,
  $|\tau_{n+1}(h)| \le (M/2) h$ with $M = \max |y''|$.
* Section 11.3, `QuarteroniSaccoSaleri.Chapter11.forwardEuler_order_one`: forward Euler has order
  $1$.
* Theorem 11.1, `QuarteroniSaccoSaleri.Chapter11.theorem_11_1`: under (11.18), the method is
  zero-stable.
* Theorem 11.1, `QuarteroniSaccoSaleri.Chapter11.theorem_11_1_estimate`: the bound $|z_n - u_n| \le
  (1 + nh) \varepsilon e^{nh\Lambda}$ of the proof.
* Lemma 11.2, `QuarteroniSaccoSaleri.Chapter11.lemma_11_2`: the discrete Gronwall lemma.
* Theorem 11.2, `QuarteroniSaccoSaleri.Chapter11.theorem_11_2`: the estimate (11.20), $|y_n - u_n|
  \le (|y_0 - u_0| + nh\tau(h)) e^{nh\Lambda}$.
* Theorem 11.2, `QuarteroniSaccoSaleri.Chapter11.theorem_11_2_convergent`: a consistent method that
  satisfies (11.18) is convergent.
* Theorem 11.2, `QuarteroniSaccoSaleri.Chapter11.theorem_11_2_order`: a method of order $p$ that
  satisfies (11.18) is convergent with order $p$.
* Equation (11.22), `QuarteroniSaccoSaleri.Chapter11.equation_11_22`: the error bound $|e_{n+1}| \le
  ((e^{L(t_{n+1} - t_0)} - 1)/L) (M/2) h$ of forward Euler.
* Equation (11.27), `QuarteroniSaccoSaleri.Chapter11.equation_11_27`: forward Euler is absolutely
  stable if and only if $h\lambda \in \mathbb{C}^-$ and $0 < h < -2
  \operatorname{Re}(\lambda)/|\lambda|^2$.
* Example 11.1, `QuarteroniSaccoSaleri.Chapter11.example_11_1`: for $\lambda = -5$, forward Euler is
  absolutely stable if and only if $h < 2/5$.
* Section 11.3, `QuarteroniSaccoSaleri.Chapter11.backwardEuler_absStabilityRegion`: the region of
  backward Euler is $|1 - z| > 1$.
* Example 11.2, `QuarteroniSaccoSaleri.Chapter11.example_11_2`: backward Euler does not oscillate on
  $y' = -5y$, and it computes a decaying solution of $y' = 5y$ for every $h > 2/5$.
* Section 11.3, `QuarteroniSaccoSaleri.Chapter11.crankNicolson_absStabilityRegion`: the region of
  Crank–Nicolson is the left half-plane.
* Section 11.3, `QuarteroniSaccoSaleri.Chapter11.heun_absStabilityRegion`: the region of Heun's
  method is $|1 + z + z^2/2| < 1$.
* Section 11.3.3, `QuarteroniSaccoSaleri.Chapter11.aStable_backwardEuler`,
  `QuarteroniSaccoSaleri.Chapter11.aStable_crankNicolson`,
  `QuarteroniSaccoSaleri.Chapter11.not_aStable_forwardEuler`,
  `QuarteroniSaccoSaleri.Chapter11.not_aStable_heun`: backward Euler and Crank–Nicolson are
  A-stable, and forward Euler and Heun's method are not.
* Remark 11.2, `QuarteroniSaccoSaleri.Chapter11.remark_11_2`: an explicit consistent Runge–Kutta
  method is not A-stable, and its region of absolute stability is bounded.

## Conventions

* An increment function is `Φ : ODE.OneStep.Increment ℝ`, and `Φ t u v h` is $\Phi(t, u, f; h)$ with
  the evaluations of $f$ built in. The third argument $v$ is the new value $u_{n+1}$; an explicit
  $\Phi$ does not depend on it.
* The nodes $t_n = t_0 + nh$ are `QuarteroniSaccoSaleri.Chapter11.grid t₀ h n`, and the number of
  steps $N_h = \lfloor T/h \rfloor$ is `QuarteroniSaccoSaleri.Chapter11.gridCount T h`.
* "$y \in C^2([t_0, t_0 + T])$" is `ContDiffOn ℝ 2 y (Icc t₀ (t₀ + T))`, and $y''$ is
  `iteratedDerivWithin 2 y (Icc t₀ (t₀ + T))`.
* The limit $h \to 0$ is the limit $h \to 0^+$, along the filter `𝓝[>] 0`.

## Implementation notes

* The $C^2$ solutions of the book are converted to the hypotheses of the backbone, which name the
  derivatives explicitly, by `hasDerivWithinAt_derivWithin_of_contDiffOn_two`.

## Deviations from the source

* **Equation (11.13)** (reading). The condition "for all $t_n$" is read uniformly in
  $t \in [t_0, t_0 + T]$. See `QuarteroniSaccoSaleri.Chapter11.equation_11_13`.
* **Definition 11.6** (reading). An absolutely stable method must also compute a sequence from every
  initial value, so that the steps at which an implicit method has no solution are excluded and not
  admitted vacuously. See `QuarteroniSaccoSaleri.Chapter11.definition_11_6`.
* **Equation (11.26)** (reading). The value $z = h\lambda$ does not fix $h$ and $\lambda$;
  $z \in \mathcal{A}$ means absolute stability for every factorization $z = h\lambda$ with $h > 0$.
  See `QuarteroniSaccoSaleri.Chapter11.equation_11_26`.

## Not formalized

* **Remark 11.2 for general explicit one-step methods** (Widlund's theorem). Only the case of the
  explicit Runge–Kutta methods is formalized.
-/

open Set Filter Topology Asymptotics ODE ODE.OneStep
open Finset (range)

namespace QuarteroniSaccoSaleri.Chapter11

variable {f : ℝ → ℝ → ℝ} {Φ : ODE.OneStep.Increment ℝ} {t₀ T h h₀ Λ y₀ : ℝ} {y : ℝ → ℝ} {n : ℕ}

/-- Let $y$ solve the Cauchy problem $y' = f(t, y)$, $y(t_0) = y_0$, on $[t_0, t_0 + T]$ with
$T > 0$. Then for every $s \in [t_0, t_0 + T]$ the derivative of $y$ within the interval is the
field, $y'(s) = f(s, y(s))$.

The derivative within the interval is `derivWithin y (Icc t₀ (t₀ + T)) s`. The hypothesis
$T > 0$ makes this derivative unique at the end points. -/
theorem derivWithin_eq_of_cauchyProblem (hT : 0 < T)
    (hy : cauchyProblem f t₀ y₀ (Icc t₀ (t₀ + T)) y) {s : ℝ} (hs : s ∈ Icc t₀ (t₀ + T)) :
    derivWithin y (Icc t₀ (t₀ + T)) s = f s (y s) :=
  (hy.2 s hs).derivWithin (uniqueDiffOn_Icc (by linarith) s hs)

/-! ### The increment function and the truncation error -/

/-- **Equation (11.11)** of [quarteroni2000numerical], the general one-step method. Let $\Phi$ be an
increment function, $h \in \mathbb{R}$ and $t_0, y_0 \in \mathbb{R}$. A sequence $(u_n)$ **is
computed by the method (11.11)** if $u_0 = y_0$ and
$$u_{n+1} = u_n + h \Phi(t_n, u_n, f_n; h), \qquad n \ge 0.$$

The sequence is an orbit of the step relation `ODE.OneStep.ofIncrement Φ` with step $h$ from
$t_0$. The increment receives the new value $u_{n+1}$ as its third argument, so the definition
also covers implicit methods. -/
def equation_11_11 (Φ : ODE.OneStep.Increment ℝ) (h t₀ y₀ : ℝ) (u : ℕ → ℝ) : Prop :=
  IsOrbit (ofIncrement Φ) h t₀ u ∧ u 0 = y₀

/-- **Equation (11.11)** of [quarteroni2000numerical], in explicit form. A sequence $(u_n)$ is
computed by the method (11.11) if and only if $u_0 = y_0$ and
$u_{n+1} = u_n + h \Phi(t_n, u_n, u_{n+1}; h)$ for every $n$. -/
theorem equation_11_11_iff (u : ℕ → ℝ) :
    equation_11_11 Φ h t₀ y₀ u ↔
      u 0 = y₀ ∧ ∀ n, u (n + 1) = u n + h * Φ (grid t₀ h n) (u n) (u (n + 1)) h := by
  rw [equation_11_11, isOrbit_ofIncrement_iff, and_comm]
  rfl

/-- **Equation (11.11)** of [quarteroni2000numerical], for an explicit increment. If $\Phi$ is
explicit (Definition 11.3), a sequence $(u_n)$ is computed by the method (11.11) if and only if
$u_n$ is the $n$-th value of the explicit iteration $u_{n+1} = u_n + h \Phi(t_n, u_n, u_n; h)$
from $u_0 = y_0$.

The explicit iteration is the second component of `ODE.OneStep.iterate Φ h t₀ y₀ n`. -/
theorem equation_11_11_iterate (hex : definition_11_3 Φ) (u : ℕ → ℝ) :
    equation_11_11 Φ h t₀ y₀ u ↔ ∀ n, u n = (iterate Φ h t₀ y₀ n).2 := by
  constructor
  · rintro ⟨hu, hu0⟩ n
    rw [eq_iterate_of_isOrbit hex hu n, hu0]
  · intro hu
    have hu' : u = fun n => (iterate Φ h t₀ y₀ n).2 := funext hu
    rw [hu']
    exact ⟨isOrbit_iterate hex y₀, rfl⟩

/-- Forward Euler (11.7) is the instance $\Phi(t_n, u_n, f_n; h) = f_n$ of (11.11): its increment is
$\Phi(t, u, v; h) = f(t, u)$. -/
theorem equation_11_11_forwardEuler (f : ℝ → ℝ → ℝ) (t u v h : ℝ) :
    equation_11_7 f t u v h = f t u :=
  rfl

/-- Heun's method (11.10) is the instance $\Phi(t_n, u_n, f_n; h) = \frac{1}{2}(f_n + f(t_n + h,
u_n + h f_n))$ of (11.11): its increment is $\Phi(t, u, v; h) = \frac{1}{2}(f(t, u) + f(t + h,
u + h f(t, u)))$. -/
theorem equation_11_11_heun (f : ℝ → ℝ → ℝ) (t u v h : ℝ) :
    equation_11_10 f t u v h = 1 / 2 * (f t u + f (t + h) (u + h * f t u)) := by
  simp [equation_11_10, heun]

/-- **Equation (11.12)** of [quarteroni2000numerical], the local truncation error. Let $\Phi$ be an
increment function, $h \in \mathbb{R}$, $y : \mathbb{R} \to \mathbb{R}$ and
$t_0 \in \mathbb{R}$. The **local truncation error** at the node $t_{n+1}$ is
$$\tau_{n+1}(h) = \frac{y_{n+1} - y_n}{h} - \Phi(t_n, y_n, y_{n+1}; h), \qquad y_n = y(t_n),$$
so that $y_{n+1} = y_n + h \Phi(t_n, y_n, f(t_n, y_n); h) + h \tau_{n+1}(h)$.

The definition is `ODE.OneStep.lte` at the node $t_n$. For $h = 0$ the quotient is $0$, by the
convention $0^{-1} = 0$. -/
noncomputable def equation_11_12 (Φ : ODE.OneStep.Increment ℝ) (h : ℝ) (y : ℝ → ℝ) (t₀ : ℝ)
    (n : ℕ) : ℝ :=
  lte Φ h y (grid t₀ h n)

/-- **Equation (11.12)** of [quarteroni2000numerical]. Let $h \neq 0$. For every function $y$, every
increment $\Phi$ and every $n$,
$$y_{n+1} = y_n + h \Phi(t_n, y_n, y_{n+1}; h) + h \tau_{n+1}(h).$$
-/
theorem equation_11_12_spec (hh : h ≠ 0) (Φ : ODE.OneStep.Increment ℝ) (y : ℝ → ℝ) (t₀ : ℝ)
    (n : ℕ) :
    y (grid t₀ h (n + 1)) = y (grid t₀ h n) +
      h * Φ (grid t₀ h n) (y (grid t₀ h n)) (y (grid t₀ h (n + 1))) h +
        h * equation_11_12 Φ h y t₀ n := by
  rw [grid, grid, node_succ]
  exact lte_spec hh y _

/-- **Section 11.3** of [quarteroni2000numerical], the global truncation error. Let $\Phi$ be an
increment function, $t_0, T \in \mathbb{R}$, $y : \mathbb{R} \to \mathbb{R}$ and
$h \in \mathbb{R}$. The **global truncation error** is
$$\tau(h) = \max_{0 \le n \le N_h - 1} |\tau_{n+1}(h)|.$$

The definition is `ODE.OneStep.globalLte`. If $N_h = 0$, the maximum is over the empty set, and
$\tau(h) = 0$. -/
noncomputable def globalTruncationError (Φ : ODE.OneStep.Increment ℝ) (t₀ T : ℝ) (y : ℝ → ℝ)
    (h : ℝ) : ℝ :=
  globalLte Φ t₀ T y h

/-- The global truncation error $\tau(h)$ is the supremum of $|\tau_{n+1}(h)|$ over the $N_h$
indices $0 \le n < N_h$. -/
theorem globalTruncationError_eq (Φ : ODE.OneStep.Increment ℝ) (t₀ T : ℝ) (y : ℝ → ℝ) (h : ℝ) :
    globalTruncationError Φ t₀ T y h = ⨆ n : Fin (gridCount T h), |equation_11_12 Φ h y t₀ n| :=
  rfl

/-- **Section 11.3** of [quarteroni2000numerical], consistency. Let $\Phi$ be an increment function,
$t_0, T \in \mathbb{R}$ and $y : \mathbb{R} \to \mathbb{R}$. The method is **consistent** along
$y$ if its truncation error is infinitesimal with respect to $h$:
$$\lim_{h \to 0^+} \tau(h) = 0.$$

The definition is `ODE.OneStep.IsConsistentFor`. In the book, $y$ is the solution of the Cauchy
problem. -/
def consistent (Φ : ODE.OneStep.Increment ℝ) (t₀ T : ℝ) (y : ℝ → ℝ) : Prop :=
  IsConsistentFor Φ t₀ T y

/-- A method is consistent along $y$ if and only if $\tau(h) \to 0$ as $h \to 0^+$. -/
theorem consistent_iff :
    consistent Φ t₀ T y ↔ Tendsto (globalTruncationError Φ t₀ T y) (𝓝[>] 0) (𝓝 0) :=
  Iff.rfl

/-- **Equation (11.14)** of [quarteroni2000numerical], the order of a method. Let $\Phi$ be an
increment function, $t_0, T \in \mathbb{R}$, $y : \mathbb{R} \to \mathbb{R}$ and
$p \in \mathbb{N}$. The method **has order $p$** along $y$ if
$$\tau(h) = O(h^p) \qquad \text{as } h \to 0^+.$$

The definition is `ODE.OneStep.HasOrderFor`. -/
def equation_11_14 (Φ : ODE.OneStep.Increment ℝ) (t₀ T : ℝ) (y : ℝ → ℝ) (p : ℕ) : Prop :=
  HasOrderFor Φ t₀ T y p

/-- A method has order $p$ along $y$ if and only if $\tau(h) = O(h^p)$ as $h \to 0^+$. -/
theorem equation_11_14_iff {p : ℕ} :
    equation_11_14 Φ t₀ T y p ↔ globalTruncationError Φ t₀ T y =O[𝓝[>] 0] fun h => h ^ p :=
  Iff.rfl

/-- **Equation (11.13)** of [quarteroni2000numerical], the consistency criterion. Let $f$ be
continuous on $[t_0, t_0 + T] \times \mathbb{R}$, and let $y$ solve the Cauchy problem
$y' = f(t, y)$, $y(t_0) = y_0$, on $[t_0, t_0 + T]$. Let $\Phi$ be an increment function such
that for every $\varepsilon > 0$ there is $\eta > 0$ with
$$|\Phi(t, y(t), y(t + h); h) - f(t, y(t))| \le \varepsilon$$
for all $h \in (0, \eta]$ and all $t$ with $t, t + h \in [t_0, t_0 + T]$. Then the method is
consistent along $y$.

**Reading.** The book asks that $\Phi(t_n, y_n, f(t_n, y_n); h) \to f(t_n, y_n)$ as $h \to 0$
for all $t_n$. This is read uniformly in $t \in [t_0, t_0 + T]$, which is what
$\tau(h) = \max_n |\tau_{n+1}(h)| \to 0$ needs.

The proof specializes `ODE.OneStep.isConsistentFor_of_tendsto_increment`. -/
theorem equation_11_13 (hf : ContinuousOn (Function.uncurry f) (Icc t₀ (t₀ + T) ×ˢ univ))
    (hy : cauchyProblem f t₀ y₀ (Icc t₀ (t₀ + T)) y)
    (hΦ : ∀ ε > 0, ∃ η > 0, ∀ h ∈ Ioc 0 η, ∀ t ∈ Icc t₀ (t₀ + T), t + h ∈ Icc t₀ (t₀ + T) →
      |Φ t (y t) (y (t + h)) h - f t (y t)| ≤ ε) :
    consistent Φ t₀ T y :=
  isConsistentFor_of_tendsto_increment hy.2
    (hf.comp (continuousOn_id.prodMk (HasDerivWithinAt.continuousOn hy.2))
      fun _ hs => ⟨hs, mem_univ _⟩) hΦ

/-- **Section 11.3** of [quarteroni2000numerical], the truncation error of forward Euler. Let
$T > 0$, let $y \in C^2([t_0, t_0 + T])$ solve the Cauchy problem $y' = f(t, y)$,
$y(t_0) = y_0$, on $[t_0, t_0 + T]$, and let $|y''(s)| \le M$ for all $s \in [t_0, t_0 + T]$.
Then for every $h > 0$ and every $n < N_h$ the local truncation error of forward Euler satisfies
$$|\tau_{n+1}(h)| \le \frac{M}{2} h.$$

The book writes $\tau_{n+1}(h) = \frac{h}{2} y''(\xi)$. The proof specializes
`ODE.OneStep.norm_lte_forwardEuler_le`. -/
theorem forwardEuler_order_one_lte (hT : 0 < T) (hy : cauchyProblem f t₀ y₀ (Icc t₀ (t₀ + T)) y)
    (hy2 : ContDiffOn ℝ 2 y (Icc t₀ (t₀ + T))) {M : ℝ}
    (hM : ∀ s ∈ Icc t₀ (t₀ + T), |iteratedDerivWithin 2 y (Icc t₀ (t₀ + T)) s| ≤ M) (hh : 0 < h)
    (hn : n < gridCount T h) : |equation_11_12 (equation_11_7 f) h y t₀ n| ≤ M / 2 * h := by
  obtain ⟨-, h2⟩ := hasDerivWithinAt_derivWithin_of_contDiffOn_two (by linarith) hy2
  have h2' : ∀ s ∈ Icc t₀ (t₀ + T), HasDerivWithinAt (fun s => f s (y s))
      (iteratedDerivWithin 2 y (Icc t₀ (t₀ + T)) s) (Icc t₀ (t₀ + T)) s := fun s hs =>
    (h2 s hs).congr (fun s' hs' => (derivWithin_eq_of_cauchyProblem hT hy hs').symm)
      (derivWithin_eq_of_cauchyProblem hT hy hs).symm
  have := norm_lte_forwardEuler_le hy.2 h2' hM hh (node_mem_Icc_of_lt hh hn)
    (node_add_mem_Icc_of_lt hh hn)
  rw [Real.norm_eq_abs] at this
  change |lte (forwardEuler f) h y (node t₀ h n)| ≤ M / 2 * h
  linarith

/-- **Section 11.3** of [quarteroni2000numerical], forward Euler has order one. Let $T > 0$, let
$y \in C^2([t_0, t_0 + T])$ solve the Cauchy problem $y' = f(t, y)$, $y(t_0) = y_0$, on
$[t_0, t_0 + T]$, and let $|y''(s)| \le M$ for all $s \in [t_0, t_0 + T]$. Then forward Euler
has order $1$ along $y$ in the sense of (11.14).

The proof specializes `ODE.OneStep.hasOrderFor_forwardEuler`. -/
theorem forwardEuler_order_one (hT : 0 < T) (hy : cauchyProblem f t₀ y₀ (Icc t₀ (t₀ + T)) y)
    (hy2 : ContDiffOn ℝ 2 y (Icc t₀ (t₀ + T))) {M : ℝ}
    (hM : ∀ s ∈ Icc t₀ (t₀ + T), |iteratedDerivWithin 2 y (Icc t₀ (t₀ + T)) s| ≤ M) :
    equation_11_14 (equation_11_7 f) t₀ T y 1 :=
  hasOrderFor_of_forall_norm_lte_le (C := M / 2) fun h hh n hn => by
    rw [pow_one, Real.norm_eq_abs]
    exact forwardEuler_order_one_lte hT hy hy2 hM hh hn

/-! ### Zero-stability -/

/-- **Definition 11.4** of [quarteroni2000numerical] (zero-stability of one-step methods). Let
$\Phi$ be an increment function and $t_0, T, y_0 \in \mathbb{R}$. The method (11.11) is
**zero-stable** for the Cauchy problem with datum $y_0$ on $[t_0, t_0 + T]$ if there are
$h_0 > 0$ and $C > 0$ with the following property. Let $h \in (0, h_0]$ and $\varepsilon \ge 0$,
and let $|\delta_k| \le \varepsilon$ for $0 \le k \le N_h$. Let $(u_n)$ solve the recursion
(11.17), $u_{n+1} = u_n + h \Phi(t_n, u_n, u_{n+1}; h)$ with $u_0 = y_0$, and let $(z_n)$ solve
the perturbed recursion (11.16),
$$z_{n+1} = z_n + h \bigl(\Phi(t_n, z_n, z_{n+1} - h\delta_{n+1}; h) + \delta_{n+1}\bigr),
  \qquad z_0 = y_0 + \delta_0.$$
Then (11.15) holds:
$$|z_n - u_n| \le C \varepsilon, \qquad 0 \le n \le N_h.$$

The definition is `ODE.OneStep.IsZeroStable` for the step relation `ODE.OneStep.ofIncrement Φ`.
For an implicit $\Phi$, the new value in the perturbed recursion is $z_{n+1} - h\delta_{n+1}$;
for an explicit $\Phi$ this argument does not matter (see
`QuarteroniSaccoSaleri.Chapter11.definition_11_4_iff`). -/
def definition_11_4 (Φ : ODE.OneStep.Increment ℝ) (t₀ T y₀ : ℝ) : Prop :=
  IsZeroStable (ofIncrement Φ) t₀ T y₀

/-- **Definition 11.4** of [quarteroni2000numerical], for an explicit increment. Let $\Phi$ be
explicit (Definition 11.3). Then the method is zero-stable for the datum $y_0$ on
$[t_0, t_0 + T]$ if and only if there are $h_0 > 0$ and $C > 0$ such that for all
$h \in (0, h_0]$, all $\varepsilon \ge 0$ and all $(\delta_k)$ with $|\delta_k| \le \varepsilon$
for $k \le N_h$, every solution $u$ of (11.17),
$$u_{n+1} = u_n + h \Phi(t_n, u_n, f(t_n, u_n); h), \qquad u_0 = y_0,$$
and every solution $z$ of (11.16),
$$z_{n+1} = z_n + h \bigl(\Phi(t_n, z_n, f(t_n, z_n); h) + \delta_{n+1}\bigr), \qquad z_0 =
  y_0 + \delta_0,$$
satisfy $|z_n - u_n| \le C\varepsilon$ for $0 \le n \le N_h$.

In the Lean statement, $\Phi(t_n, u_n, f(t_n, u_n); h)$ is `Φ (grid t₀ h n) (u n) (u n) h`. -/
theorem definition_11_4_iff (hex : definition_11_3 Φ) :
    definition_11_4 Φ t₀ T y₀ ↔
      ∃ h₀ : ℝ, 0 < h₀ ∧ ∃ C : ℝ, 0 < C ∧ ∀ h ∈ Ioc 0 h₀, ∀ ε : ℝ, 0 ≤ ε → ∀ δ : ℕ → ℝ,
        (∀ k ≤ gridCount T h, |δ k| ≤ ε) → ∀ u z : ℕ → ℝ,
          (u 0 = y₀ ∧ ∀ n, u (n + 1) = u n + h * Φ (grid t₀ h n) (u n) (u n) h) →
          (z 0 = y₀ + δ 0 ∧
            ∀ n, z (n + 1) = z n + h * (Φ (grid t₀ h n) (z n) (z n) h + δ (n + 1))) →
          ∀ n ≤ gridCount T h, |z n - u n| ≤ C * ε := by
  simp only [definition_11_4, IsZeroStable, Real.norm_eq_abs, isOrbit_ofIncrement_iff,
    isOrbitWith_ofIncrement_iff, smul_eq_mul]
  refine exists_congr fun h₀ => and_congr_right fun _ => exists_congr fun C =>
    and_congr_right fun _ => forall₂_congr fun h _ => forall₂_congr fun ε _ =>
    forall₂_congr fun δ _ => forall₂_congr fun u z => ?_
  constructor
  · intro H hu hz
    refine H (fun n => (hu.2 n).trans ?_) hu.1 (fun n => (hz.2 n).trans ?_) hz.1
    · rw [hex (grid t₀ h n) (u n) (u n) (u (n + 1)) h]
      rfl
    · rw [hex (grid t₀ h n) (z n) (z n) (z (n + 1) - h * δ (n + 1)) h]
      simp only [grid]
      ring
  · intro H hu hu0 hz hz0
    refine H ⟨hu0, fun n => (hu n).trans ?_⟩ ⟨hz0, fun n => (hz n).trans ?_⟩
    · rw [hex (node t₀ h n) (u n) (u (n + 1)) (u n) h]
      rfl
    · rw [hex (node t₀ h n) (z n) (z (n + 1) - h * δ (n + 1)) (z n) h]
      simp only [grid]
      ring

/-- **Equation (11.18)** of [quarteroni2000numerical], the Lipschitz hypothesis of Theorem 11.1. Let
$\Phi$ be an increment function and $t_0, T, h_0, \Lambda \in \mathbb{R}$. The increment $\Phi$
**satisfies (11.18)** if
$$|\Phi(t, u, w; h) - \Phi(t, v, w'; h)| \le \Lambda |u - v|$$
for all $h \in (0, h_0]$, all $t \in [t_0, t_0 + T]$ and all $u, v, w, w' \in \mathbb{R}$.

The definition is `ODE.OneStep.LipschitzIncrement`. The constant $\Lambda$ does not depend on
$h$, on the node $t$, or on the third argument $w$. For an explicit $\Phi$ the third argument is
inert; for an implicit $\Phi$ the condition asks that the dependence on the new value be
absorbed into $\Lambda$. -/
def equation_11_18 (Φ : ODE.OneStep.Increment ℝ) (t₀ T h₀ Λ : ℝ) : Prop :=
  LipschitzIncrement Φ t₀ T h₀ Λ

/-- **Equation (11.18)** of [quarteroni2000numerical], for an explicit increment. If $\Phi$ is
explicit (Definition 11.3), then $\Phi$ satisfies (11.18) if and only if $|\Phi(t, u, u; h) -
\Phi(t, z, z; h)| \le \Lambda |u - z|$ for all $h \in (0, h_0]$, all $t \in [t_0, t_0 + T]$ and
all $u, z \in \mathbb{R}$. -/
theorem equation_11_18_iff (hex : definition_11_3 Φ) :
    equation_11_18 Φ t₀ T h₀ Λ ↔ ∀ h ∈ Ioc 0 h₀, ∀ t ∈ Icc t₀ (t₀ + T), ∀ u z : ℝ,
      |Φ t u u h - Φ t z z h| ≤ Λ * |u - z| := by
  simp only [equation_11_18, LipschitzIncrement, Real.norm_eq_abs]
  refine forall₂_congr fun h _ => forall₂_congr fun t _ => forall_congr' fun u =>
    forall_congr' fun z => ⟨fun H => H _ _, fun H w w' => ?_⟩
  rw [hex _ _ w u, hex _ _ w' z]
  exact H

/-- **Theorem 11.1** of [quarteroni2000numerical] (zero-stability). Let $T \ge 0$, $h_0 > 0$ and
$\Lambda > 0$, and let the increment function $\Phi$ satisfy (11.18) with the constants $h_0$
and $\Lambda$. Then for every datum $y_0 \in \mathbb{R}$ the method (11.11) is zero-stable on
$[t_0, t_0 + T]$ (Definition 11.4).

The book states the theorem for the explicit method (11.11). The Lean statement has no
explicitness hypothesis; for an implicit $\Phi$, (11.18) is uniform in the third argument. The
constant of zero-stability is $C = (1 + T) e^{\Lambda T}$. The proof specializes
`ODE.OneStep.isZeroStable_of_lipschitzIncrement`. -/
theorem theorem_11_1 (hT : 0 ≤ T) (hh₀ : 0 < h₀) (hΛ : 0 < Λ) (hlip : equation_11_18 Φ t₀ T h₀ Λ)
    (y₀ : ℝ) : definition_11_4 Φ t₀ T y₀ :=
  isZeroStable_of_lipschitzIncrement hT hh₀ hlip hΛ.le y₀

/-- **Theorem 11.1** of [quarteroni2000numerical], the estimate in the proof. Let $\Lambda > 0$, let
$\Phi$ satisfy (11.18) with the constants $h_0$ and $\Lambda$, let $h \in (0, h_0]$, and let
$|\delta_k| \le \varepsilon$ for $0 \le k \le N_h$. Let $u$ solve the recursion (11.17) with
$u_0 = y_0$, and let $z$ solve the perturbed recursion (11.16) with $z_0 = y_0 + \delta_0$. Then
for $0 \le n \le N_h$,
$$|z_n - u_n| \le (1 + hn) \, \varepsilon \, e^{nh\Lambda}.$$

The book writes $w_n^{(h)} = z_n^{(h)} - u_n^{(h)}$. The recursions are `ODE.OneStep.IsOrbit`
and `ODE.OneStep.IsOrbitWith` for `ODE.OneStep.ofIncrement Φ`. The proof specializes
`ODE.OneStep.norm_sub_le_of_lipschitzIncrement`. -/
theorem theorem_11_1_estimate (hΛ : 0 < Λ) (hlip : equation_11_18 Φ t₀ T h₀ Λ) (hh : h ∈ Ioc 0 h₀)
    {ε : ℝ} {δ : ℕ → ℝ} (hδ : ∀ k ≤ gridCount T h, |δ k| ≤ ε) {u z : ℕ → ℝ}
    (hu : IsOrbit (ofIncrement Φ) h t₀ u) (hu0 : u 0 = y₀)
    (hz : IsOrbitWith (ofIncrement Φ) h t₀ δ z) (hz0 : z 0 = y₀ + δ 0) (hn : n ≤ gridCount T h) :
    |z n - u n| ≤ (1 + h * n) * ε * Real.exp (n * h * Λ) := by
  have := norm_sub_le_of_lipschitzIncrement hlip hΛ.le hh (fun k hk => by
    rw [Real.norm_eq_abs]; exact hδ k hk) hu hu0 hz hz0 hn
  rw [Real.norm_eq_abs] at this
  rw [mul_comm h (n : ℝ)]
  exact this

/-- **Lemma 11.2** of [quarteroni2000numerical] (discrete Gronwall lemma). Let $(k_n)$ be a sequence
with $k_n \ge 0$, let $(\varphi_n)$ and $(p_n)$ be sequences with $p_n \ge 0$, and let
$g_0 \ge 0$. Suppose that $\varphi_0 \le g_0$ and
$$\varphi_n \le g_0 + \sum_{s=0}^{n-1} p_s + \sum_{s=0}^{n-1} k_s \varphi_s, \qquad n \ge 1.$$
Then for every $n \ge 1$,
$$\varphi_n \le \Bigl(g_0 + \sum_{s=0}^{n-1} p_s\Bigr) \exp\Bigl(\sum_{s=0}^{n-1} k_s\Bigr).$$

The proof specializes `Gronwall.discrete_sum`. -/
theorem lemma_11_2 {φ k p : ℕ → ℝ} {g₀ : ℝ} (hk : ∀ n, 0 ≤ k n) (hφ₀ : φ 0 ≤ g₀)
    (hφ : ∀ n, 1 ≤ n → φ n ≤ g₀ + ∑ s ∈ range n, p s + ∑ s ∈ range n, k s * φ s) (hg₀ : 0 ≤ g₀)
    (hp : ∀ n, 0 ≤ p n) :
    ∀ n, 1 ≤ n → φ n ≤ (g₀ + ∑ s ∈ range n, p s) * Real.exp (∑ s ∈ range n, k s) := fun n _ =>
  Gronwall.discrete_sum hg₀ hk hp (fun m => by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simpa using hφ₀
    · exact hφ m hm) n

/-! ### Convergence -/

/-- **Definition 11.5** of [quarteroni2000numerical] (convergence). Let $S$ be a one-step method,
given as a step relation, let $t_0, T, y_0 \in \mathbb{R}$, and let $y$ be the solution of the
Cauchy problem. The method is **convergent** if there are a function $C(h)$ with $C(h) \to 0$ as
$h \to 0^+$ and an $h_0 > 0$ such that for every $h \in (0, h_0]$, every sequence $(u_n)$
computed by $S$ with step $h$ from $u_0 = y_0$ satisfies
$$|u_n - y_n| \le C(h), \qquad 0 \le n \le N_h.$$

The definition is `ODE.OneStep.IsConvergentFor`. A step relation `S h t u v` says that $v$ is an
admissible value at $t + h$ after the value $u$ at $t$; it covers both increment functions and
implicit Runge–Kutta methods. -/
def definition_11_5 (S : ODE.OneStep.StepRel ℝ) (t₀ T y₀ : ℝ) (y : ℝ → ℝ) : Prop :=
  IsConvergentFor S t₀ T y₀ y

/-- **Definition 11.5** of [quarteroni2000numerical], convergence with order $p$. Let $S$ be a
one-step method, given as a step relation, let $t_0, T, y_0 \in \mathbb{R}$, let $y$ be the
solution of the Cauchy problem, and let $p \in \mathbb{N}$. The method is **convergent with
order $p$** if there are $\mathcal{C} > 0$ and $h_0 > 0$ such that for every $h \in (0, h_0]$,
every sequence $(u_n)$ computed by $S$ with step $h$ from $u_0 = y_0$ satisfies
$$|u_n - y_n| \le \mathcal{C} h^p, \qquad 0 \le n \le N_h.$$

The definition is `ODE.OneStep.IsConvergentWithOrderFor`. -/
def definition_11_5_order (S : ODE.OneStep.StepRel ℝ) (t₀ T y₀ : ℝ) (y : ℝ → ℝ) (p : ℕ) : Prop :=
  IsConvergentWithOrderFor S t₀ T y₀ y p

/-- A method is convergent (Definition 11.5) if and only if there are $C(h) \to 0$ as $h \to 0^+$
and $h_0 > 0$ such that for every $h \in (0, h_0]$, every orbit $u$ of the method with step $h$
from $u_0 = y_0$ satisfies $|u_n - y(t_n)| \le C(h)$ for $0 \le n \le N_h$. -/
theorem definition_11_5_iff {S : ODE.OneStep.StepRel ℝ} :
    definition_11_5 S t₀ T y₀ y ↔ ∃ C : ℝ → ℝ, Tendsto C (𝓝[>] 0) (𝓝 0) ∧
      ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ h ∈ Ioc 0 h₀, ∀ u : ℕ → ℝ, IsOrbit S h t₀ u → u 0 = y₀ →
        ∀ n ≤ gridCount T h, |u n - y (grid t₀ h n)| ≤ C h := by
  simp only [definition_11_5, IsConvergentFor, Real.norm_eq_abs, grid, gridCount]

/-- A method is convergent with order $p$ if and only if there are $\mathcal{C} > 0$ and $h_0 > 0$
such that for every $h \in (0, h_0]$, every orbit $u$ of the method with step $h$ from
$u_0 = y_0$ satisfies $|u_n - y(t_n)| \le \mathcal{C} h^p$ for $0 \le n \le N_h$. -/
theorem definition_11_5_order_iff {S : ODE.OneStep.StepRel ℝ} {p : ℕ} :
    definition_11_5_order S t₀ T y₀ y p ↔ ∃ C : ℝ, 0 < C ∧
      ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ h ∈ Ioc 0 h₀, ∀ u : ℕ → ℝ, IsOrbit S h t₀ u → u 0 = y₀ →
        ∀ n ≤ gridCount T h, |u n - y (grid t₀ h n)| ≤ C * h ^ p := by
  simp only [definition_11_5_order, IsConvergentWithOrderFor, Real.norm_eq_abs, grid, gridCount]

/-- **Theorem 11.2** of [quarteroni2000numerical], the estimate (11.20). Let $\Lambda > 0$, let
$\Phi$ satisfy (11.18) with the constants $h_0$ and $\Lambda$, and let $h \in (0, h_0]$. Let
$y : \mathbb{R} \to \mathbb{R}$, and let $(u_n)$ be computed by the method (11.11) with step $h$
from an arbitrary $u_0$. Then for $0 \le n \le N_h$,
$$|y_n - u_n| \le \bigl(|y_0 - u_0| + nh\,\tau(h)\bigr) e^{nh\Lambda},$$
where $y_n = y(t_n)$ and $\tau(h)$ is the global truncation error along $y$.

The estimate holds for every function $y$; in the book, $y$ is the solution of the Cauchy
problem. The proof specializes `ODE.OneStep.norm_sub_le_globalLte`. -/
theorem theorem_11_2 (hΛ : 0 < Λ) (hlip : equation_11_18 Φ t₀ T h₀ Λ) (hh : h ∈ Ioc 0 h₀)
    {u : ℕ → ℝ} (hu : IsOrbit (ofIncrement Φ) h t₀ u) (hn : n ≤ gridCount T h) :
    |y (grid t₀ h n) - u n| ≤
      (|y t₀ - u 0| + n * h * globalTruncationError Φ t₀ T y h) * Real.exp (n * h * Λ) := by
  have := norm_sub_le_globalLte hlip hΛ.le hh hu y hn
  rwa [Real.norm_eq_abs, Real.norm_eq_abs] at this

/-- **Theorem 11.2** of [quarteroni2000numerical], convergence. Let $T \ge 0$, $h_0 > 0$ and
$\Lambda > 0$, let $\Phi$ satisfy (11.18) with the constants $h_0$ and $\Lambda$, and let the
method be consistent along $y$. Then the method (11.11) is convergent for the datum
$y_0 = y(t_0)$ (Definition 11.5).

Consistency is the consistency assumption (11.13) of the book. The proof specializes
`ODE.OneStep.isConvergentFor_of_isConsistentFor`. -/
theorem theorem_11_2_convergent (hT : 0 ≤ T) (hh₀ : 0 < h₀) (hΛ : 0 < Λ)
    (hlip : equation_11_18 Φ t₀ T h₀ Λ) (hcons : consistent Φ t₀ T y) :
    definition_11_5 (ofIncrement Φ) t₀ T (y t₀) y :=
  isConvergentFor_of_isConsistentFor hT hh₀ hlip hΛ.le hcons

/-- **Theorem 11.2** of [quarteroni2000numerical], order of convergence. Let $T \ge 0$, $h_0 > 0$
and $\Lambda > 0$, let $\Phi$ satisfy (11.18) with the constants $h_0$ and $\Lambda$, and let
the method have order $p$ along $y$ (11.14). Then the method (11.11) is convergent with order
$p$ for the datum $y_0 = y(t_0)$.

The proof specializes `ODE.OneStep.isConvergentWithOrderFor_of_hasOrderFor`. -/
theorem theorem_11_2_order (hT : 0 ≤ T) (hh₀ : 0 < h₀) (hΛ : 0 < Λ)
    (hlip : equation_11_18 Φ t₀ T h₀ Λ) {p : ℕ} (hord : equation_11_14 Φ t₀ T y p) :
    definition_11_5_order (ofIncrement Φ) t₀ T (y t₀) y p :=
  isConvergentWithOrderFor_of_hasOrderFor hT hh₀ hlip hΛ.le hord

/-- **Equation (11.22)** of [quarteroni2000numerical], the error bound of forward Euler. Let $L > 0$
and $T > 0$, and let $|f(t, y_1) - f(t, y_2)| \le L |y_1 - y_2|$ for all $t \in [t_0, t_0 + T]$
and $y_1, y_2 \in \mathbb{R}$. Let $y \in C^2([t_0, t_0 + T])$ solve the Cauchy problem
$y' = f(t, y)$, $y(t_0) = y_0$, on $[t_0, t_0 + T]$, with $|y''(s)| \le M$ for all
$s \in [t_0, t_0 + T]$. Let $h > 0$, and let $(u_n)$ be computed by forward Euler with step $h$
from $u_0 = y_0$. Then for every $n$ with $n + 1 \le N_h$,
$$|e_{n+1}| = |y_{n+1} - u_{n+1}| \le \frac{e^{L(t_{n+1} - t_0)} - 1}{L} \, \frac{M}{2} \, h.$$

The proof specializes `ODE.OneStep.norm_sub_le_forwardEuler`. -/
theorem equation_11_22 {L : ℝ} (hL : 0 < L)
    (hlip : ∀ t ∈ Icc t₀ (t₀ + T), ∀ y₁ y₂ : ℝ, |f t y₁ - f t y₂| ≤ L * |y₁ - y₂|) (hT : 0 < T)
    (hy : cauchyProblem f t₀ y₀ (Icc t₀ (t₀ + T)) y) (hy2 : ContDiffOn ℝ 2 y (Icc t₀ (t₀ + T)))
    {M : ℝ} (hM : ∀ s ∈ Icc t₀ (t₀ + T), |iteratedDerivWithin 2 y (Icc t₀ (t₀ + T)) s| ≤ M)
    (hh : 0 < h) {u : ℕ → ℝ} (hu : equation_11_11 (equation_11_7 f) h t₀ y₀ u)
    (hn : n + 1 ≤ gridCount T h) :
    |y (grid t₀ h (n + 1)) - u (n + 1)| ≤
      (Real.exp (L * (grid t₀ h (n + 1) - t₀)) - 1) / L * (M / 2 * h) := by
  obtain ⟨-, h2⟩ := hasDerivWithinAt_derivWithin_of_contDiffOn_two (by linarith) hy2
  have h2' : ∀ s ∈ Icc t₀ (t₀ + T), HasDerivWithinAt (fun s => f s (y s))
      (iteratedDerivWithin 2 y (Icc t₀ (t₀ + T)) s) (Icc t₀ (t₀ + T)) s := fun s hs =>
    (h2 s hs).congr (fun s' hs' => (derivWithin_eq_of_cauchyProblem hT hy hs').symm)
      (derivWithin_eq_of_cauchyProblem hT hy hs).symm
  have hlip' : ∀ t ∈ Icc t₀ (t₀ + T), LipschitzWith ⟨L, hL.le⟩ (f t) := fun t ht =>
    LipschitzWith.of_dist_le_mul fun v₁ v₂ => by
      rw [Real.dist_eq, Real.dist_eq]
      exact hlip t ht v₁ v₂
  have := norm_sub_le_forwardEuler hlip' hL hy.2 h2' hM hh hu.1 (hu.2.trans hy.1.symm) hn
  rw [Real.norm_eq_abs] at this
  rw [grid, node, add_sub_cancel_left]
  exact this

/-! ### Absolute stability -/

/-- **Equation (11.24)** of [quarteroni2000numerical], the test problem. For
$\lambda \in \mathbb{C}$, the **test problem** is
$$y'(t) = \lambda y(t), \quad t > 0, \qquad y(0) = 1.$$
The definition gives its field $f(t, y) = \lambda y$ on $\mathbb{C}$.

The field is `ODE.testField λ`. -/
def testProblem (lam : ℂ) : ℝ → ℂ → ℂ := testField lam

/-- **Equation (11.24)** of [quarteroni2000numerical], the solution of the test problem. For
$\lambda \in \mathbb{C}$, the function $y(t) = e^{\lambda t}$ solves $y' = \lambda y$ on all of
$\mathbb{R}$ with $y(0) = 1$. -/
theorem testProblem_solution (lam : ℂ) :
    ODE.IsSolutionOn (testProblem lam) 0 1 univ fun t : ℝ => Complex.exp (lam * t) :=
  ⟨by simp, fun t _ => (hasDerivAt_exp_testField lam t).hasDerivWithinAt⟩

/-- **Equation (11.24)** of [quarteroni2000numerical], decay of the solution. For
$\lambda \in \mathbb{C}$, $|e^{\lambda t}| \to 0$ as $t \to +\infty$ if and only if
$\operatorname{Re} \lambda < 0$. -/
theorem testProblem_tendsto_iff (lam : ℂ) :
    Tendsto (fun t : ℝ => ‖Complex.exp (lam * t)‖) atTop (𝓝 0) ↔ lam.re < 0 := by
  have e : ∀ t : ℝ, ‖Complex.exp (lam * t)‖ = Real.exp (lam.re * t) := fun t => by
    rw [Complex.norm_exp]
    simp
  simp only [e]
  constructor
  · intro H
    by_contra hre
    push Not at hre
    have h1 : ∀ᶠ t : ℝ in atTop, (1 : ℝ) ≤ Real.exp (lam.re * t) := by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      exact Real.one_le_exp (mul_nonneg hre ht)
    have := ge_of_tendsto H h1
    linarith
  · intro hre
    exact Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg hre)

/-- **Definition 11.6** of [quarteroni2000numerical] (absolute stability). Let $M$ be a numerical
method, $\lambda \in \mathbb{C}$ and $h \in \mathbb{R}$. The method is **absolutely stable** for
$\lambda$ and the step $h$ if, applied to the test problem (11.24) with step $h$, it computes a
sequence with (11.25):
$$|u_n| \to 0 \qquad \text{as } t_n \to +\infty.$$

**Reading.** The definition requires that every initial value $u_0 \in \mathbb{C}$ have a
sequence computed by the method from $u_0$, and that every such sequence tend to $0$. So the
steps at which an implicit method has no solution are excluded, and are not admitted vacuously.

The definition is `ODE.OneStep.IsAbsStable` for the step relation of $M$ on the field
`QuarteroniSaccoSaleri.Chapter11.testProblem λ`, with $t_0 = 0$. -/
def definition_11_6 (M : ODE.OneStep.Method ℂ) (lam : ℂ) (h : ℝ) : Prop :=
  IsAbsStable (M (testProblem lam)) h

/-- **Equation (11.26)** of [quarteroni2000numerical], the region of absolute stability. For a
numerical method $M$, the **region of absolute stability** is
$$\mathcal{A} = \{z = h\lambda \in \mathbb{C} : \text{(11.25) is satisfied}\}.$$

**Reading.** The value $z$ does not determine $h$ and $\lambda$. The definition puts $z$ in
$\mathcal{A}$ if the method is absolutely stable for every factorization $z = h\lambda$ with
$h > 0$. For the methods of this section, absolute stability depends on $h$ and $\lambda$ only
through $h\lambda$, and $\mathcal{A}$ is the set of $z$ for which the method is absolutely
stable with $h = 1$ and $\lambda = z$.

The definition is `ODE.OneStep.absStabilityRegion`. -/
def equation_11_26 (M : ODE.OneStep.Method ℂ) : Set ℂ := absStabilityRegion M

/-- Let $M$ be a numerical method and $z \in \mathbb{C}$. Then $z$ lies in the region of absolute
stability $\mathcal{A}$ of $M$ if and only if $M$ is absolutely stable for $\lambda = z/h$ and
the step $h$, for every $h > 0$. -/
theorem mem_equation_11_26_iff {M : ODE.OneStep.Method ℂ} {z : ℂ} :
    z ∈ equation_11_26 M ↔ ∀ h : ℝ, 0 < h → definition_11_6 M (z / h) h :=
  Iff.rfl

/-- **Equation (11.27)** of [quarteroni2000numerical], forward Euler on the test problem. Let
$\lambda \in \mathbb{C}$ and $h \in \mathbb{R}$. If $(u_n)$ is computed by forward Euler with
step $h$ on the test problem (11.24) from $u_0 = 1$, then $u_n = (1 + h\lambda)^n$ for every
$n$. -/
theorem equation_11_27_orbit {lam : ℂ} {u : ℕ → ℂ}
    (hu : IsOrbit (ofIncrement (forwardEuler (testProblem lam))) h 0 u) (hu0 : u 0 = 1) (n : ℕ) :
    u n = (1 + h * lam) ^ n := by
  rw [forwardEuler_testField_orbit hu n, hu0, mul_one]

/-- **Equation (11.27)** of [quarteroni2000numerical]. Let $\lambda \in \mathbb{C}$ and $h > 0$.
Forward Euler with step $h$ is absolutely stable for $\lambda$ if and only if
$$h\lambda \in \mathbb{C}^- \quad \text{and} \quad h < -\frac{2
  \operatorname{Re}(\lambda)}{|\lambda|^2},$$
where $\mathbb{C}^-$ is the open left half-plane. Both conditions are equivalent to
$|1 + h\lambda| < 1$.

The proof uses `ODE.OneStep.mem_absStabilityRegion_forwardEuler_iff` and
`ODE.OneStep.isAbsStable_forwardEuler_iff`. -/
theorem equation_11_27 {lam : ℂ} (hh : 0 < h) :
    definition_11_6 (fun f => ofIncrement (forwardEuler f)) lam h ↔
      ((h : ℂ) * lam).re < 0 ∧ h < -2 * lam.re / ‖lam‖ ^ 2 := by
  have hre : ((h : ℂ) * lam).re = h * lam.re := by simp
  rw [definition_11_6, testProblem, hre, mul_neg_iff,
    or_iff_left (by push Not; intro hneg; linarith)]
  constructor
  · intro H
    have hlam : lam.re < 0 := by
      by_contra hre'
      push Not at hre'
      rw [isAbsStable_iff_mem_absStabilityRegion (M := fun f => ofIncrement (forwardEuler f))
        forwardEuler_scaleInvariant hh, mem_absStabilityRegion_forwardEuler_iff,
        ← sq_lt_one_iff₀ (norm_nonneg _), Complex.sq_norm, Complex.normSq_apply] at H
      simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, Complex.mul_re,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero,
        zero_add] at H
      nlinarith [mul_nonneg hh.le hre', sq_nonneg (h * lam.im), sq_nonneg (h * lam.re)]
    exact ⟨⟨hh, hlam⟩, (isAbsStable_forwardEuler_iff hh hlam).1 H⟩
  · rintro ⟨⟨-, hlam⟩, H⟩
    exact (isAbsStable_forwardEuler_iff hh hlam).2 H

/-- **Example 11.1** of [quarteroni2000numerical]. Consider the test problem $y' = -5y$, $y(0) = 1$,
and let $h > 0$. Forward Euler with step $h$ is absolutely stable for this problem if and only
if $h < 2/5$.

This is condition (11.27) for $\lambda = -5$. -/
theorem example_11_1 (hh : 0 < h) :
    definition_11_6 (fun f => ofIncrement (forwardEuler f)) (-5) h ↔ h < 2 / 5 := by
  rw [definition_11_6, testProblem, isAbsStable_forwardEuler_iff hh (by norm_num)]
  norm_num

/-- **Section 11.3** of [quarteroni2000numerical], backward Euler on the test problem. Let
$h \in \mathbb{R}$. Then:

* for every $\lambda \in \mathbb{C}$ with $h\lambda \neq 1$, a sequence $(u_n)$ computed by
  backward Euler with step $h$ on the test problem from $u_0 = 1$ is $u_n = 1/(1 - h\lambda)^n$;
* the region of absolute stability of backward Euler is the exterior of the unit disc with
  centre $1$: $z \in \mathcal{A}$ if and only if $|1 - z| > 1$.

The second part specializes `ODE.OneStep.mem_absStabilityRegion_backwardEuler_iff`. -/
theorem backwardEuler_absStabilityRegion :
    (∀ {lam : ℂ} {u : ℕ → ℂ}, (h : ℂ) * lam ≠ 1 →
      IsOrbit (ofIncrement (backwardEuler (testProblem lam))) h 0 u → u 0 = 1 →
        ∀ n, u n = 1 / (1 - h * lam) ^ n) ∧
      ∀ z : ℂ, z ∈ equation_11_26 (fun f => ofIncrement (backwardEuler f)) ↔ 1 < ‖1 - z‖ :=
  ⟨fun hne hu hu0 n => by rw [backwardEuler_testField_orbit hne hu n, hu0, mul_one, inv_pow,
    one_div], fun z => mem_absStabilityRegion_backwardEuler_iff z⟩

/-- **Example 11.2** of [quarteroni2000numerical], decay. Let $h > 0$. Backward Euler applied to
$y' = 5y$, $y(0) = 1$, with step $h$ is absolutely stable, that is $5h$ lies in its region of
absolute stability, if and only if $h > 2/5$. So for every $h > 2/5$ the computed solution
decays to $0$, although the exact solution $e^{5t}$ tends to infinity. -/
theorem example_11_2_decay (hh : 0 < h) :
    ((5 * h : ℝ) : ℂ) ∈ equation_11_26 (fun f => ofIncrement (backwardEuler f)) ↔ 2 / 5 < h := by
  rw [equation_11_26, mem_absStabilityRegion_backwardEuler_iff, ← Complex.ofReal_one,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, lt_abs]
  constructor
  · rintro (H | H) <;> linarith
  · intro H; right; linarith

/-- **Example 11.2** of [quarteroni2000numerical], no oscillation. Let $h > 0$, and let $(u_n)$ be
computed by backward Euler with step $h$ on $y' = -5y$ from $u_0 = 1$. Then
$u_n = (1 + 5h)^{-n}$ for every $n$, and the real sequence $(1 + 5h)^{-n}$ is positive and
decreasing. -/
theorem example_11_2_no_oscillation (hh : 0 < h) {u : ℕ → ℂ}
    (hu : IsOrbit (ofIncrement (backwardEuler (testProblem (-5)))) h 0 u) (hu0 : u 0 = 1) :
    (∀ n, u n = (((1 + 5 * h)⁻¹ ^ n : ℝ) : ℂ)) ∧ (∀ n, 0 < (1 + 5 * h)⁻¹ ^ n) ∧
      Antitone fun n : ℕ => (1 + 5 * h)⁻¹ ^ n := by
  have hne : (h : ℂ) * (-5) ≠ 1 := by
    intro H
    have := congrArg Complex.re H
    simp at this
    linarith
  refine ⟨fun n => ?_, fun n => by positivity, ?_⟩
  · rw [backwardEuler_testField_orbit hne hu n, hu0, mul_one]
    push_cast
    ring
  · refine antitone_nat_of_succ_le fun n => ?_
    rw [pow_succ]
    exact mul_le_of_le_one_right (by positivity) (inv_le_one_of_one_le₀ (by linarith))

/-- **Example 11.2** of [quarteroni2000numerical]. Let $h > 0$. Then:

* backward Euler applied to $y' = 5y$, $y(0) = 1$, is absolutely stable for the step $h$ if and
  only if $h > 2/5$, although the exact solution $e^{5t}$ tends to infinity;
* every sequence $(u_n)$ computed by backward Euler with step $h$ on $y' = -5y$ from $u_0 = 1$
  is $u_n = (1 + 5h)^{-n}$, a positive decreasing sequence, so the method produces no
  oscillation.

This is the conjunction of `QuarteroniSaccoSaleri.Chapter11.example_11_2_decay` and
`QuarteroniSaccoSaleri.Chapter11.example_11_2_no_oscillation`. -/
theorem example_11_2 (hh : 0 < h) :
    (((5 * h : ℝ) : ℂ) ∈ equation_11_26 (fun f => ofIncrement (backwardEuler f)) ↔ 2 / 5 < h) ∧
      ∀ u : ℕ → ℂ, IsOrbit (ofIncrement (backwardEuler (testProblem (-5)))) h 0 u → u 0 = 1 →
        (∀ n, u n = (((1 + 5 * h)⁻¹ ^ n : ℝ) : ℂ)) ∧ (∀ n, 0 < (1 + 5 * h)⁻¹ ^ n) ∧
          Antitone fun n : ℕ => (1 + 5 * h)⁻¹ ^ n :=
  ⟨example_11_2_decay hh, fun _ hu hu0 => example_11_2_no_oscillation hh hu hu0⟩

/-- **Section 11.3** of [quarteroni2000numerical], Crank–Nicolson on the test problem. Let
$h \in \mathbb{R}$. Then:

* for every $\lambda \in \mathbb{C}$ with $h\lambda \neq 2$, a sequence $(u_n)$ computed by
  Crank–Nicolson with step $h$ on the test problem from $u_0 = 1$ is
$$u_n = \left(\frac{1 + h\lambda/2}{1 - h\lambda/2}\right)^n;$$
* the region of absolute stability of Crank–Nicolson is the open left half-plane:
  $z \in \mathcal{A}$ if and only if $\operatorname{Re} z < 0$.

The second part specializes `ODE.OneStep.mem_absStabilityRegion_crankNicolson_iff`. -/
theorem crankNicolson_absStabilityRegion :
    (∀ {lam : ℂ} {u : ℕ → ℂ}, (h : ℂ) * lam ≠ 2 →
      IsOrbit (ofIncrement (crankNicolson (testProblem lam))) h 0 u → u 0 = 1 →
        ∀ n, u n = ((1 + 1 / 2 * lam * h) / (1 - 1 / 2 * lam * h)) ^ n) ∧
      ∀ z : ℂ, z ∈ equation_11_26 (fun f => ofIncrement (crankNicolson f)) ↔ z.re < 0 :=
  ⟨fun hne hu hu0 n => by
    rw [crankNicolson_testField_orbit hne hu n, hu0, mul_one]
    ring_nf, fun z => mem_absStabilityRegion_crankNicolson_iff z⟩

/-- **Section 11.3** of [quarteroni2000numerical], Heun's method on the test problem. Let
$h \in \mathbb{R}$. Then:

* for every $\lambda \in \mathbb{C}$, a sequence $(u_n)$ computed by Heun's method with step $h$
  on the test problem from $u_0 = 1$ is $u_n = (1 + h\lambda + (h\lambda)^2/2)^n$;
* the region of absolute stability of Heun's method is
  $\{z \in \mathbb{C} : |1 + z + z^2/2| < 1\}$;
* a real number $x$ lies in the region of Heun's method if and only if it lies in the region of
  forward Euler.

By (11.27), the common restriction to the real axis is the interval $(-2, 0)$. The second part
specializes `ODE.OneStep.mem_absStabilityRegion_heun_iff`. -/
theorem heun_absStabilityRegion :
    (∀ {lam : ℂ} {u : ℕ → ℂ}, IsOrbit (ofIncrement (heun (testProblem lam))) h 0 u → u 0 = 1 →
      ∀ n, u n = (1 + h * lam + (h * lam) ^ 2 / 2) ^ n) ∧
      (∀ z : ℂ, z ∈ equation_11_26 (fun f => ofIncrement (heun f)) ↔ ‖1 + z + z ^ 2 / 2‖ < 1) ∧
      ∀ x : ℝ, (x : ℂ) ∈ equation_11_26 (fun f => ofIncrement (heun f)) ↔
        (x : ℂ) ∈ equation_11_26 (fun f => ofIncrement (forwardEuler f)) :=
  ⟨fun hu hu0 n => by rw [heun_testField_orbit hu n, hu0, mul_one],
    fun z => mem_absStabilityRegion_heun_iff z, fun x => by
      rw [equation_11_26, equation_11_26, ofReal_mem_absStabilityRegion_heun_iff,
        ofReal_mem_absStabilityRegion_forwardEuler_iff]⟩

/-- **Section 11.3.3** of [quarteroni2000numerical], A-stability. A numerical method is **A-stable**
if
$$\mathcal{A} \cap \mathbb{C}^- = \mathbb{C}^-,$$
that is, if for $\operatorname{Re} \lambda < 0$ condition (11.25) is satisfied for all values of
$h$.

The definition is `ODE.OneStep.IsAStable`: every $z$ with $\operatorname{Re} z < 0$ lies in
$\mathcal{A}$. -/
def aStable (M : ODE.OneStep.Method ℂ) : Prop := IsAStable M

/-- **Section 11.3.3** of [quarteroni2000numerical]. A numerical method is A-stable if and only if
$\mathcal{A} \cap \mathbb{C}^- = \mathbb{C}^-$, where $\mathbb{C}^- = \{z \in \mathbb{C} :
\operatorname{Re} z < 0\}$. -/
theorem aStable_iff {M : ODE.OneStep.Method ℂ} :
    aStable M ↔ equation_11_26 M ∩ {z : ℂ | z.re < 0} = {z : ℂ | z.re < 0} := by
  rw [aStable, IsAStable, inter_eq_right]
  rfl

/-- **Section 11.3.3** of [quarteroni2000numerical]. Backward Euler is A-stable. -/
theorem aStable_backwardEuler : aStable fun f => ofIncrement (backwardEuler f) :=
  isAStable_backwardEuler

/-- **Section 11.3.3** of [quarteroni2000numerical]. Crank–Nicolson is A-stable. -/
theorem aStable_crankNicolson : aStable fun f => ofIncrement (crankNicolson f) :=
  isAStable_crankNicolson

/-- **Section 11.3.3** of [quarteroni2000numerical]. Forward Euler is not A-stable; it is only
conditionally stable. -/
theorem not_aStable_forwardEuler : ¬ aStable fun f => ofIncrement (forwardEuler f) :=
  not_isAStable_forwardEuler

/-- **Section 11.3.3** of [quarteroni2000numerical]. Heun's method is not A-stable; it is only
conditionally stable. -/
theorem not_aStable_heun : ¬ aStable fun f => ofIncrement (heun f) :=
  not_isAStable_heun

/-- **Remark 11.2** of [quarteroni2000numerical], for the explicit Runge–Kutta methods. Let
$(A, b, c)$ be an explicit Butcher tableau with $s$ stages that is consistent, $\sum_i b_i = 1$.
Then the Runge–Kutta method of the tableau is not A-stable, and its region of absolute stability
is bounded.

The book states that there are no explicit unconditionally absolutely stable schemes. The
explicit Runge–Kutta methods of Section 11.8 are the explicit one-step schemes of this form. The
remark for arbitrary explicit one-step schemes (Widlund's theorem) is not formalized. The first
part specializes `ODE.ButcherTableau.not_isAStable_of_isExplicit`. -/
theorem remark_11_2 {s : ℕ} (tab : ODE.ButcherTableau s) (hex : tab.IsExplicit)
    (hb : ∑ i, tab.b i = 1) :
    ¬ aStable tab.stepRel ∧ Bornology.IsBounded (equation_11_26 tab.stepRel) :=
  ⟨tab.not_isAStable_of_isExplicit hex hb, tab.isBounded_absStabilityRegion hex hb⟩

end QuarteroniSaccoSaleri.Chapter11
