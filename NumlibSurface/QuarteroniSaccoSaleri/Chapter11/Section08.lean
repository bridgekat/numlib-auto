/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.ODE.RungeKutta
import NumlibSurface.QuarteroniSaccoSaleri.Chapter11.Section03

/-!
# Quarteroni, Sacco and Saleri, Section 11.8: Runge–Kutta Methods

This module formalizes Section 11.8 of [quarteroni2000numerical] for the scalar Cauchy problem
$y' = f(t, y)$. An $s$-stage Runge–Kutta method with Butcher array $(A, b, c)$,
$A \in \mathbb{R}^{s \times s}$, $b, c \in \mathbb{R}^s$, advances on the grid $t_n = t_0 + nh$ by
$$u_{n+1} = u_n + h \sum_{i=1}^s b_i K_i, \qquad K_i = f\Big(t_n + c_i h,\ u_n + h \sum_{j=1}^s
  a_{ij} K_j\Big).$$
The module states the method (11.70)–(11.71), the row-sum condition (11.72), and the explicit,
semi-implicit and implicit methods. It proves that an explicit method is consistent if and only if
$\sum_i b_i = 1$, and that it is then zero-stable and convergent. It states the classical four-stage
method (11.73) and proves its order four, the two-stage order conditions of Section 11.8.1, the
embedded pairs (11.76) and the Runge–Kutta–Fehlberg pair of Section 11.8.2, the implicit methods of
Section 11.8.3, and the stability function $R(z) = 1 + z b^T (I - zA)^{-1} \mathbf{1}$ with the
regions of absolute stability of Section 11.8.4. Of Property 11.4 only the first clause is proved:
an explicit $s$-stage method has order at most $s$.

The proofs specialize `Numlib.ODE.RungeKutta` at the state space $\mathbb{R}$, and at $\mathbb{C}$
for the test problem $y' = \lambda y$. The one-step theory of Section 11.3, in
`NumlibSurface.QuarteroniSaccoSaleri.Chapter11.Section03`, supplies the notions of truncation error,
order, zero-stability, convergence and absolute stability.

## Main definitions

* Equations (11.70)–(11.71), `QuarteroniSaccoSaleri.Chapter11.equation_11_71` and
  `QuarteroniSaccoSaleri.Chapter11.equation_11_70_increment`: the orbits of a Runge–Kutta method,
  and the increment function of an explicit one.
* Equation (11.72), `QuarteroniSaccoSaleri.Chapter11.equation_11_72`: the row-sum condition
  $c_i = \sum_j a_{ij}$.
* Section 11.8, `QuarteroniSaccoSaleri.Chapter11.equation_11_71_explicit`,
  `QuarteroniSaccoSaleri.Chapter11.equation_11_71_semiImplicit` and
  `QuarteroniSaccoSaleri.Chapter11.implicitRungeKutta`: explicit, semi-implicit and implicit
  methods.
* Section 11.8, `QuarteroniSaccoSaleri.Chapter11.rungeKutta_lte`: the local truncation error of an
  explicit method.
* Equation (11.73), `QuarteroniSaccoSaleri.Chapter11.equation_11_73`: the classical four-stage
  method.
* Equation (11.76), `QuarteroniSaccoSaleri.Chapter11.equation_11_76`,
  `QuarteroniSaccoSaleri.Chapter11.equation_11_76_errorIndicator` and
  `QuarteroniSaccoSaleri.Chapter11.rkf45`: embedded pairs, their error indicator, and the
  Runge–Kutta–Fehlberg 4(5) pair.
* Section 11.8.4, `QuarteroniSaccoSaleri.Chapter11.stabilityFunction`: the stability function
  $R(z)$.

## Main results

* Section 11.8, `QuarteroniSaccoSaleri.Chapter11.rungeKutta_consistent_iff`: an explicit method with
  nodes in $[0, 1]$ is consistent if and only if $\sum_i b_i = 1$.
* Section 11.8, `QuarteroniSaccoSaleri.Chapter11.rungeKutta_convergent`: an explicit method is
  zero-stable, and a consistent one is convergent, with the order of its consistency.
* Property 11.4, first clause, `QuarteroniSaccoSaleri.Chapter11.property_11_4_order_le_stages`: an
  explicit $s$-stage method of order $q$ has $q \le s$.
* Equation (11.73), `QuarteroniSaccoSaleri.Chapter11.equation_11_73_step` and
  `QuarteroniSaccoSaleri.Chapter11.equation_11_73_order`: the classical method written out, and its
  order four.
* Section 11.8.1, `QuarteroniSaccoSaleri.Chapter11.twoStageOrderConditions`: a two-stage explicit
  method has order two if and only if $b_1 + b_2 = 1$ and $c_2 b_2 = 1/2$.
* Equation (11.76), `QuarteroniSaccoSaleri.Chapter11.equation_11_76_errorIndicator_eq` and
  `QuarteroniSaccoSaleri.Chapter11.rkf45_spec`: the error indicator is the difference of the two
  solutions of a pair, and the coefficients of the Fehlberg pair.
* Section 11.8.3, `QuarteroniSaccoSaleri.Chapter11.gaussLegendre_tableaux`,
  `QuarteroniSaccoSaleri.Chapter11.radau_tableaux`,
  `QuarteroniSaccoSaleri.Chapter11.lobatto_tableaux` and
  `QuarteroniSaccoSaleri.Chapter11.dirk_tableau`: the Gauss–Legendre, Radau, Lobatto and DIRK
  tableaux.
* Equation (11.77), `QuarteroniSaccoSaleri.Chapter11.equation_11_77`: on $y' = \lambda y$ one step
  is $u_{n+1} = R(h\lambda) u_n$.
* Section 11.8.4, `QuarteroniSaccoSaleri.Chapter11.rungeKutta_absStable_iff`: the region of absolute
  stability is $\{z : |R(z)| < 1\}$ where $I - zA$ is invertible.
* Section 11.8.4, `QuarteroniSaccoSaleri.Chapter11.rungeKutta_explicit_stabilityFunction`: for an
  explicit method $R$ is a polynomial, the region of absolute stability is bounded, and the method
  is not A-stable.

## Conventions

* A method is a Butcher array `tab : ODE.ButcherTableau s`, with $A$ = `tab.A`, $b$ = `tab.b` and
  $c$ = `tab.c`. Lean indexes the stages by `Fin s`, from $0$; the prose indexes them from $1$.
* The step relation `tab.stepRel f` is an `ODE.OneStep.Method`, so Definitions 11.4–11.6 of Section
  11.3 apply to it without change. An explicit method is also handled through its increment function
  `tab.explicitIncrement f` (11.70).
* The nodes are assumed to lie in $[0, 1]$ wherever the field is controlled only on the horizon.

## Deviations from the source

* **Equations (11.70)–(11.72), truncation error, and convergence** (reading). The orbit uses
  stage witnesses and does not require the row-sum condition. The explicit recursion ignores
  entries on or above the diagonal, including on tableaux outside its intended scope, and agrees
  with the orbit relation for explicit tableaux. The truncation formula uses any curve. The
  consistency and convergence theorems give explicit hypotheses on stage times, field regularity
  and the exact startup.
* **Section 11.8.1 and equation (11.73)** (reading). The two-stage necessity test uses the
  constant and linear time fields. The sufficiency and RK4 order theorems use an exact curve
  with the stated differentiability and global bounds on field derivatives.
* **Equation (11.76)** (reading). The embedded pair records common stage data and two weight
  vectors, without order assumptions. The error indicator gives their exact one-step difference,
  without a bound on how closely that difference estimates the lower method's local error.
* **Section 11.8.3, implicit tableaux** (partial). The Gauss–Legendre theorem gives the two
  printed methods and their displayed collocation conditions. The Radau result treats the second
  and third arrays, and the Lobatto result treats the first array. The DIRK identity permits all
  real $\mu$ and does not enforce $3\mu^3-3\mu-1=0$. These declarations give coefficient and
  step identities without the printed general order claims.
* **Equation (11.77) and Section 11.8.4** (reading). Lean's stages $K_i$ are slopes, equal to
  $\lambda$ times the stage values in (11.77). The update equivalence assumes that $I-h\lambda
  A$ is invertible, while `stabilityFunction` uses a total inverse. Boundedness for the explicit
  stability region is stated under $\sum_i b_i=1$.
* **Section 11.8.2, the Fehlberg error coefficients** (reading). The printed tableau's last row
  equals $\hat b-b$, as stated by `QuarteroniSaccoSaleri.Chapter11.rkf45_spec`. The preceding text
  defines $E=b-\hat b$, the sign used by
  `QuarteroniSaccoSaleri.Chapter11.equation_11_76_errorIndicator`.
* **Section 11.8.4, absolute stability** (correction). The source gives the region as
  $\{z : |R(z)| < 1\}$ without assuming that $I - zA$ is invertible. See
  `QuarteroniSaccoSaleri.Chapter11.rungeKutta_absStable_iff`.
* **Section 11.8.4, the stability function of an explicit method of order $s$** (generalization).
  The source states $R(z) = \sum_{k=0}^s z^k / k!$ for $s = 1, \dots, 4$; it is proved for every
  $s$. See `QuarteroniSaccoSaleri.Chapter11.rungeKutta_explicit_stabilityFunction`.
* **Property 11.4, first clause** (generalization). Order $q$ along the single solution $e^t$ of
  $y' = y$ is enough. See `QuarteroniSaccoSaleri.Chapter11.property_11_4_order_le_stages`.

## Not formalized

* **Property 11.4**, the clauses after the first: no explicit $s$-stage method has order $s$ when
  $s \ge 5$, and the least number of stages of an explicit method of order $1, \dots, 8$ is
  $1, 2, 3, 4, 6, 7, 9, 11$. The source states them without proof, citing Butcher (1987). They rest
  on the order conditions indexed by rooted trees and on B-series, which the backbone does not have:
  the clause $s \ge 5$ is Butcher's case analysis of these conditions (see [hairer1993solving],
  Section II.5), and the minimal stage numbers also need a method that attains each number.
* **Remarks 11.4–11.5.**
* **Equations (11.74)–(11.75)**, the step-doubling error estimates. The source states them as
  heuristics.
* **The maximal orders of the implicit methods** of Section 11.8.3: $2s$ for Gauss–Legendre,
  $2s - 1$ for Radau and $2s - 2$ for Lobatto. The source quotes them from Butcher (1987) without
  proof, and they need the same B-series theory.
* **The order four of the three-stage DIRK method** of Section 11.8.3.
-/

open Set Filter Topology Asymptotics Matrix ODE ODE.OneStep
open Finset (range)

namespace QuarteroniSaccoSaleri.Chapter11

variable {f : ℝ → ℝ → ℝ} {t₀ T h h₀ t y₀ : ℝ} {y : ℝ → ℝ} {n s : ℕ}

/-! ### (11.70)–(11.72): the method, its Butcher array and the row-sum condition -/

/-- **Equation (11.71)** of [quarteroni2000numerical]. Let $(A, b, c)$ be the Butcher array of an
$s$-stage Runge–Kutta method, let $f : \mathbb{R} \times \mathbb{R} \to \mathbb{R}$, and let
$h, t_0 \in \mathbb{R}$, with the grid $t_n = t_0 + nh$. A sequence $(u_n)_{n \ge 0}$ is an
**orbit of the Runge–Kutta method** if for every $n$ there are stages $K_1, \dots, K_s$ with
$$K_i = f\Big(t_n + c_i h,\ u_n + h \sum_{j=1}^s a_{ij} K_j\Big) \quad (i = 1, \dots, s), \qquad
  u_{n+1} = u_n + h \sum_{i=1}^s b_i K_i.$$

The definition is `ODE.OneStep.IsOrbit` for the step relation `ODE.ButcherTableau.stepRel` of
`tab : ODE.ButcherTableau s`. No initial value is imposed, and for an implicit method the stages
need only exist, not be unique. `QuarteroniSaccoSaleri.Chapter11.equation_11_71_iff` unfolds the
definition.

**Reading.** The stage equations are witnesses for each step. No row-sum, existence, or
uniqueness assumption is built into the tableau or orbit. -/
def equation_11_71 (tab : ButcherTableau s) (f : ℝ → ℝ → ℝ) (h t₀ : ℝ) (u : ℕ → ℝ) : Prop :=
  IsOrbit (tab.stepRel f) h t₀ u

/-- **Equation (11.71)** of [quarteroni2000numerical], unfolded. A sequence $(u_n)$ is an orbit of
the Runge–Kutta method (11.71) with Butcher array $(A, b, c)$ if and only if for every $n$ there
is $K \in \mathbb{R}^s$ with
$$K_i = f\Big(t_n + c_i h,\ u_n + h \sum_{j=1}^s a_{ij} K_j\Big) \quad \text{for all } i, \qquad
  u_{n+1} = u_n + h \sum_{i=1}^s b_i K_i.$$

**Reading.** The stage equations are witnesses for each step. No row-sum, existence, or
uniqueness assumption is built into the tableau or orbit. -/
theorem equation_11_71_iff (tab : ButcherTableau s) (u : ℕ → ℝ) :
    equation_11_71 tab f h t₀ u ↔ ∀ n, ∃ K : Fin s → ℝ,
      (∀ i, K i = f (grid t₀ h n + tab.c i * h) (u n + h * ∑ j, tab.A i j * K j)) ∧
        u (n + 1) = u n + h * ∑ i, tab.b i * K i := by
  rw [equation_11_71, isOrbit_iff]
  simp only [ButcherTableau.stepRel_apply, ButcherTableau.IsStages, smul_eq_mul, grid]

/-- **Equation (11.72)** of [quarteroni2000numerical]. The Butcher array $(A, b, c)$ satisfies the
**row-sum condition** if
$$c_i = \sum_{j=1}^s a_{ij}, \qquad i = 1, \dots, s.$$

The source assumes this condition throughout Section 11.8. The definition is
`ODE.ButcherTableau.IsRowSum`. -/
def equation_11_72 (tab : ButcherTableau s) : Prop :=
  tab.IsRowSum

/-- **Equation (11.72)** of [quarteroni2000numerical], unfolded. The row-sum condition holds if and
only if $c_i = \sum_{j=1}^s a_{ij}$ for every $i$. -/
theorem equation_11_72_iff (tab : ButcherTableau s) :
    equation_11_72 tab ↔ ∀ i, tab.c i = ∑ j, tab.A i j :=
  Iff.rfl

/-- **Section 11.8** of [quarteroni2000numerical], explicit methods. A Runge–Kutta method is
**explicit** if $a_{ij} = 0$ for $j \ge i$, so that each stage $K_i$ is computed from the
previous stages $K_1, \dots, K_{i-1}$.

The definition is `ODE.ButcherTableau.IsExplicit`. -/
def equation_11_71_explicit (tab : ButcherTableau s) : Prop :=
  tab.IsExplicit

/-- **Section 11.8** of [quarteroni2000numerical], semi-implicit methods. A Runge–Kutta method is
**semi-implicit** if $a_{ij} = 0$ for $j > i$, so that each stage $K_i$ solves one equation in
$K_i$ alone, once $K_1, \dots, K_{i-1}$ are known.

The definition is `ODE.ButcherTableau.IsSemiImplicit`. -/
def equation_11_71_semiImplicit (tab : ButcherTableau s) : Prop :=
  tab.IsSemiImplicit

/-- **Section 11.8** of [quarteroni2000numerical], implicit methods. A Runge–Kutta method is
**implicit** if it is not explicit, that is, if $a_{ij} \neq 0$ for some $j \ge i$.

The source uses the term in Section 11.8 and in Section 11.8.3. -/
def implicitRungeKutta (tab : ButcherTableau s) : Prop :=
  ¬ tab.IsExplicit

/-- **Section 11.8** of [quarteroni2000numerical], the shapes of the Butcher array. Let $(A, b, c)$
be a Butcher array. Then:

* the method is explicit if and only if $a_{ij} = 0$ for all $i \le j$;
* the method is semi-implicit if and only if $a_{ij} = 0$ for all $i < j$;
* the method is implicit if and only if $a_{ij} \neq 0$ for some $i \le j$;
* an explicit method is semi-implicit. -/
theorem equation_11_71_shapes (tab : ButcherTableau s) :
    (equation_11_71_explicit tab ↔ ∀ i j : Fin s, i ≤ j → tab.A i j = 0) ∧
    (equation_11_71_semiImplicit tab ↔ ∀ i j : Fin s, i < j → tab.A i j = 0) ∧
    (implicitRungeKutta tab ↔ ¬ ∀ i j : Fin s, i ≤ j → tab.A i j = 0) ∧
    (equation_11_71_explicit tab → equation_11_71_semiImplicit tab) :=
  ⟨Iff.rfl, Iff.rfl, Iff.rfl, fun hex => hex.isSemiImplicit⟩

/-- **Equation (11.70)** of [quarteroni2000numerical]. For a Butcher array $(A, b, c)$ and $f :
\mathbb{R} \times \mathbb{R} \to \mathbb{R}$, the **increment function of the explicit method**
is
$$F(t, u, h; f) = \sum_{i=1}^s b_i K_i, \qquad K_i = f\Big(t + c_i h,\ u + h \sum_{j < i} a_{ij}
  K_j\Big),$$
with the stages computed in the order $i = 1, \dots, s$.

The definition is `ODE.ButcherTableau.explicitIncrement`. It uses only the entries $a_{ij}$ with
$j < i$, so it is defined for every Butcher array, and it is the increment of the method when
the method is explicit.

**Reading.** The explicit stage recursion ignores entries on or above the diagonal. It is
defined for any array and agrees with the Runge–Kutta orbit when the array is explicit. -/
noncomputable def equation_11_70_increment (tab : ButcherTableau s) (f : ℝ → ℝ → ℝ) :
    OneStep.Increment ℝ :=
  tab.explicitIncrement f

/-- **Section 11.8** of [quarteroni2000numerical], explicit methods as one-step methods. Let the
Runge–Kutta method with Butcher array $(A, b, c)$ be explicit. Then a sequence $(u_n)$ is an
orbit of (11.71) if and only if it solves the one-step method (11.11)
$u_{n+1} = u_n + h F(t_n, u_n, h; f)$ with the increment (11.70) and the initial value $u_0$.
Moreover, for all $t, v \in \mathbb{R}$ the stages of the increment are
$$K_i = f\Big(t + c_i h,\ v + h \sum_{j < i} a_{ij} K_j\Big).$$

**Reading.** The explicit stage recursion ignores entries on or above the diagonal. It is
defined for any array and agrees with the Runge–Kutta orbit when the array is explicit. -/
theorem equation_11_71_explicit_iff (tab : ButcherTableau s) (hex : equation_11_71_explicit tab)
    (u : ℕ → ℝ) :
    (equation_11_71 tab f h t₀ u ↔ equation_11_11 (equation_11_70_increment tab f) h t₀ (u 0) u) ∧
    ∀ (t v : ℝ) (i : Fin s), tab.explicitStages f h t v i = f (t + tab.c i * h)
      (v + h * ∑ j, if j < i then tab.A i j * tab.explicitStages f h t v j else 0) := by
  refine ⟨?_, fun t v i => ?_⟩
  · rw [equation_11_71, equation_11_11, tab.stepRel_eq_ofIncrement hex, equation_11_70_increment]
    exact ⟨fun H => ⟨H, rfl⟩, fun H => H.1⟩
  · rw [ButcherTableau.explicitStages_apply]
    simp only [smul_eq_mul]

/-! ### The truncation error, consistency and convergence -/

/-- **Section 11.8** of [quarteroni2000numerical], the local truncation error of an explicit method.
Let $y : \mathbb{R} \to \mathbb{R}$ and $t_n = t_0 + nh$. The **local truncation error**
$\tau_{n+1}(h)$ of the Runge–Kutta method is the local truncation error (11.12) of the increment
(11.70):
$$h \tau_{n+1}(h) = y(t_{n+1}) - y(t_n) - h F(t_n, y(t_n), h; f).$$

For $h = 0$ the definition gives $\tau_{n+1}(0) = -F(t_n, y(t_n), 0; f)$, because Lean sets
$0^{-1} = 0$. `QuarteroniSaccoSaleri.Chapter11.rungeKutta_lte_spec` gives the displayed identity
for $h \neq 0$.

**Generalization.** Extends the residual formula to arbitrary curves via the explicit stage
recursion. The residual identity uses a nonzero step. -/
noncomputable def rungeKutta_lte (tab : ButcherTableau s) (f : ℝ → ℝ → ℝ) (h : ℝ) (y : ℝ → ℝ)
    (t₀ : ℝ) (n : ℕ) : ℝ :=
  equation_11_12 (equation_11_70_increment tab f) h y t₀ n

/-- **Section 11.8** of [quarteroni2000numerical], the local truncation error unfolded. Let
$h \neq 0$, let $y : \mathbb{R} \to \mathbb{R}$, and let $K_i$ be the stages (11.70) at
$(t_n, y(t_n))$. Then
$$y(t_{n+1}) = y(t_n) + h \sum_{i=1}^s b_i K_i + h \tau_{n+1}(h).$$

**Generalization.** Extends the residual formula to arbitrary curves via the explicit stage
recursion. The residual identity uses a nonzero step. -/
theorem rungeKutta_lte_spec (hh : h ≠ 0) (tab : ButcherTableau s) (y : ℝ → ℝ) (t₀ : ℝ) (n : ℕ) :
    y (grid t₀ h (n + 1)) = y (grid t₀ h n) +
      h * ∑ i, tab.b i * tab.explicitStages f h (grid t₀ h n) (y (grid t₀ h n)) i +
        h * rungeKutta_lte tab f h y t₀ n :=
  equation_11_12_spec hh (equation_11_70_increment tab f) y t₀ n

/-- **Section 11.8** of [quarteroni2000numerical], consistency of explicit methods. Let $(A, b, c)$
be a Butcher array with $c_i \in [0, 1]$ for every $i$. The following are equivalent:

* for all $f : \mathbb{R} \times \mathbb{R} \to \mathbb{R}$, $L \in \mathbb{R}$,
  $t_0 \in \mathbb{R}$, $T > 0$, $y_0 \in \mathbb{R}$ and $y : \mathbb{R} \to \mathbb{R}$: if
  $f$ is continuous on $[t_0, t_0 + T + 1] \times \mathbb{R}$, satisfies
  $|f(s, y_1) - f(s, y_2)| \le L |y_1 - y_2|$ for $s \in [t_0, t_0 + T + 1]$ and all $y_1, y_2$,
  and $y$ solves the Cauchy problem $y' = f(t, y)$, $y(t_0) = y_0$ on $[t_0, t_0 + T]$, then the
  increment (11.70) is consistent along $y$ on $[t_0, t_0 + T]$;
* $\sum_{i=1}^s b_i = 1$.

The source cites Lambert (1991) for this result. The field is controlled on the larger interval
$[t_0, t_0 + T + 1]$ because the stages are evaluated at $t_n + c_i h$, which can lie beyond
$t_0 + T$. Consistency is `QuarteroniSaccoSaleri.Chapter11.consistent`: the largest local
truncation error on the grid tends to $0$ as $h \to 0^+$. The statement does not assume that the
method is explicit, because the increment (11.70) uses only the strictly lower triangle of $A$.
The proof specializes `ODE.ButcherTableau.isConsistentFor_of_sum_b_eq_one` and
`ODE.ButcherTableau.sum_b_eq_one_of_isConsistentFor`.

**Reading.** This equivalence tests consistency across exact curves for continuous, uniformly
Lipschitz fields and stage times in the stated interval. A single exact curve does not suffice
for necessity. -/
theorem rungeKutta_consistent_iff (tab : ButcherTableau s) (hc : ∀ i, tab.c i ∈ Icc (0 : ℝ) 1) :
    (∀ (f : ℝ → ℝ → ℝ) (L : ℝ) (t₀ T y₀ : ℝ) (y : ℝ → ℝ), 0 < T →
      ContinuousOn (Function.uncurry f) (Icc t₀ (t₀ + T + 1) ×ˢ univ) →
      (∀ s ∈ Icc t₀ (t₀ + T + 1), ∀ y₁ y₂ : ℝ, |f s y₁ - f s y₂| ≤ L * |y₁ - y₂|) →
      cauchyProblem f t₀ y₀ (Icc t₀ (t₀ + T)) y →
      consistent (equation_11_70_increment tab f) t₀ T y) ↔ ∑ i, tab.b i = 1 := by
  constructor
  · intro H
    refine tab.sum_b_eq_one_of_isConsistentFor (t₀ := 0) (T := 1) one_pos ?_
    exact H (fun _ _ => 1) 0 0 1 0 id one_pos continuousOn_const (fun _ _ _ _ => by simp)
      ⟨rfl, fun t _ => (hasDerivWithinAt_id t _)⟩
  · intro hb f L t₀ T y₀ y _ hf hlip hy
    exact tab.isConsistentFor_of_sum_b_eq_one (L := Real.toNNReal L) hc hb hf (fun s hs =>
      LipschitzWith.of_dist_le_mul fun y₁ y₂ => by
        rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal']
        exact (hlip s hs y₁ y₂).trans
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))) hy.2

/-- **Section 11.8** of [quarteroni2000numerical], convergence of explicit methods ("since RK
methods are one-step methods, consistency implies stability and, in turn, convergence"). Let the
Runge–Kutta method with Butcher array $(A, b, c)$ be explicit, with $c_i \in [0, 1]$ for every
$i$. Let $T \ge 0$ and $h_0 > 0$, and let $f$ satisfy
$|f(t, y_1) - f(t, y_2)| \le L |y_1 - y_2|$ for $t \in [t_0, t_0 + T + h_0]$ and all $y_1, y_2$.
Let $y : \mathbb{R} \to \mathbb{R}$. Then:

* the increment (11.70) is zero-stable (Definition 11.4) on $[t_0, t_0 + T]$ for every initial
  value $y_0$;
* if the increment is consistent along $y$, the method is convergent (Definition 11.5) to $y$
  from $u_0 = y(t_0)$;
* for every $p \in \mathbb{N}$, if the increment has order $p$ (11.14) along $y$, the method
  converges to $y$ with order $p$.

The function $y$ need not be a solution of the Cauchy problem: consistency along $y$ is all that
is used. The increment is Lipschitz in $u$, so Theorem 11.1 and Theorem 11.2 of Section 11.3
apply. The proof specializes `ODE.ButcherTableau.lipschitzIncrement_explicit`,
`ODE.ButcherTableau.isZeroStable_explicit` and `ODE.ButcherTableau.isConvergentFor_explicit`.

**Reading.** Assumes an explicit tableau, stage fractions in $[0,1]$, and a uniform Lipschitz
bound on the field. Convergence is stated for exact starting data. -/
theorem rungeKutta_convergent (tab : ButcherTableau s) (hex : equation_11_71_explicit tab)
    (hc : ∀ i, tab.c i ∈ Icc (0 : ℝ) 1) {L : ℝ}
    (hlip : ∀ t ∈ Icc t₀ (t₀ + T + h₀), ∀ y₁ y₂ : ℝ, |f t y₁ - f t y₂| ≤ L * |y₁ - y₂|)
    (hT : 0 ≤ T) (hh₀ : 0 < h₀) :
    (∀ y₀ : ℝ, definition_11_4 (equation_11_70_increment tab f) t₀ T y₀) ∧
    (consistent (equation_11_70_increment tab f) t₀ T y →
      definition_11_5 (tab.stepRel f) t₀ T (y t₀) y) ∧
    ∀ p : ℕ, equation_11_14 (equation_11_70_increment tab f) t₀ T y p →
      definition_11_5_order (tab.stepRel f) t₀ T (y t₀) y p := by
  have hlip' : ∀ t ∈ Icc t₀ (t₀ + T + h₀), LipschitzWith (Real.toNNReal L) (f t) := fun t ht =>
    LipschitzWith.of_dist_le_mul fun y₁ y₂ => by
      rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal']
      exact (hlip t ht y₁ y₂).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))
  have hΛ : (0 : ℝ) ≤ (∑ i, |tab.b i|) * (Real.toNNReal L : ℝ) *
      (1 + h₀ * (Real.toNNReal L : ℝ) * tab.entrySum) ^ s := by
    have := tab.entrySum_nonneg
    positivity
  refine ⟨fun y₀ => ?_, fun hcons => ?_, fun p hord => ?_⟩
  · have := tab.isZeroStable_explicit hex hc hlip' hT hh₀ y₀
    rwa [tab.stepRel_eq_ofIncrement hex] at this
  · exact tab.isConvergentFor_explicit hex hc hlip' hT hh₀ hcons
  · rw [definition_11_5_order, tab.stepRel_eq_ofIncrement hex]
    exact isConvergentWithOrderFor_of_hasOrderFor hT hh₀ (tab.lipschitzIncrement_explicit hc hlip')
      hΛ hord

/-! ### (11.73): the classical method -/

/-- **Equation (11.73)** of [quarteroni2000numerical], the classical explicit four-stage method:
$$u_{n+1} = u_n + \frac{h}{6} (K_1 + 2K_2 + 2K_3 + K_4),$$
with $K_1 = f(t_n, u_n)$, $K_2 = f(t_n + h/2, u_n + (h/2) K_1)$,
$K_3 = f(t_n + h/2, u_n + (h/2) K_2)$ and $K_4 = f(t_{n+1}, u_n + h K_3)$.

The definition is `ODE.rk4`. Its order four is
`QuarteroniSaccoSaleri.Chapter11.equation_11_73_order`. -/
noncomputable def equation_11_73 : ButcherTableau 4 :=
  rk4

/-- **Equation (11.73)** of [quarteroni2000numerical], written out. The classical method has the
Butcher array
$$A = \begin{bmatrix} 0 & 0 & 0 & 0 \\ 1/2 & 0 & 0 & 0 \\ 0 & 1/2 & 0 & 0 \\ 0 & 0 & 1 & 0
  \end{bmatrix}, \qquad b = (1/6, 1/3, 1/3, 1/6), \qquad c = (0, 1/2, 1/2, 1).$$
It is explicit and satisfies the row-sum condition (11.72). A sequence $(u_n)$ is an orbit of
the method if and only if for every $n$
$$u_{n+1} = u_n + \frac{h}{6} (K_1 + 2K_2 + 2K_3 + K_4)$$
with $K_1 = f(t_n, u_n)$, $K_2 = f(t_n + h/2, u_n + (h/2) K_1)$,
$K_3 = f(t_n + h/2, u_n + (h/2) K_2)$ and $K_4 = f(t_n + h, u_n + h K_3)$, all written out in
the Lean statement. -/
theorem equation_11_73_step :
    equation_11_73.A = !![0, 0, 0, 0; 1 / 2, 0, 0, 0; 0, 1 / 2, 0, 0; 0, 0, 1, 0] ∧
    equation_11_73.b = ![1 / 6, 1 / 3, 1 / 3, 1 / 6] ∧ equation_11_73.c = ![0, 1 / 2, 1 / 2, 1] ∧
    equation_11_71_explicit equation_11_73 ∧ equation_11_72 equation_11_73 ∧
    ∀ u : ℕ → ℝ, equation_11_71 equation_11_73 f h t₀ u ↔ ∀ n,
      u (n + 1) = u n + h / 6 * (f (grid t₀ h n) (u n) +
        2 * f (grid t₀ h n + h / 2) (u n + h / 2 * f (grid t₀ h n) (u n)) +
        2 * f (grid t₀ h n + h / 2)
          (u n + h / 2 * f (grid t₀ h n + h / 2) (u n + h / 2 * f (grid t₀ h n) (u n))) +
        f (grid t₀ h n + h) (u n + h * f (grid t₀ h n + h / 2)
          (u n + h / 2 * f (grid t₀ h n + h / 2) (u n + h / 2 * f (grid t₀ h n) (u n))))) := by
  refine ⟨rfl, rfl, rfl, rk4_isExplicit, rk4_isRowSum, fun u => ?_⟩
  rw [equation_11_71, equation_11_73, rk4.stepRel_eq_ofIncrement rk4_isExplicit,
    isOrbit_ofIncrement_iff]
  refine forall_congr' fun n => ?_
  rw [explicitIncrement_rk4]
  simp only [smul_eq_mul, grid]
  constructor <;> intro H <;> rw [H] <;> ring

/-! ### §11.8.1: the two-stage order conditions -/

/-- **Section 11.8.1** of [quarteroni2000numerical], the two-stage order conditions. Let $(A, b, c)$
be the Butcher array of a two-stage explicit method that satisfies (11.72). Then:

* if the method has order $2$ along the solution $y(t) = t$ of $y' = 1$ on every interval
  $[t_0, t_0 + T]$ with $T > 0$, and along the solution $y(t) = t^2$ of $y' = 2t$ on $[0, 1]$,
  then $b_1 + b_2 = 1$ and $c_2 b_2 = 1/2$;
* if $b_1 + b_2 = 1$ and $c_2 b_2 = 1/2$, then the method has order $2$ (11.14) along every
  solution $y \in C^3([t_0, t_0 + T])$, $T > 0$, of a Cauchy problem $y' = f(t, y)$,
  $y(t_0) = y_0$, whose field $f$ is $C^2$ on $\mathbb{R} \times \mathbb{R}$ with
  $\|D^2 f\| \le M_2$ everywhere;
* Heun's method and the modified Euler method satisfy $b_1 + b_2 = 1$ and $c_2 b_2 = 1/2$.

The necessity is read from the two test problems
(`ODE.ButcherTableau.orderTwoConditions_of_hasOrderFor`). The sufficiency is
`ODE.ButcherTableau.hasOrderFor_two_of`, which makes rigorous the Taylor expansions of $K_2$ and
$y_{n+1}$ in the source. Heun's method is `ODE.ButcherTableau.heun` and the modified Euler
method is `ODE.ButcherTableau.modifiedEuler`.

**Reading.** The order estimates make the regularity of the solution curve and uniform
derivative bounds on the field explicit. -/
theorem twoStageOrderConditions (tab : ButcherTableau 2) (hex : equation_11_71_explicit tab)
    (hrow : equation_11_72 tab) :
    ((∀ (t₀ T : ℝ), 0 < T →
      equation_11_14 (equation_11_70_increment tab fun _ _ => 1) t₀ T id 2) →
      equation_11_14 (equation_11_70_increment tab fun t _ => 2 * t) 0 1 (fun t => t ^ 2) 2 →
      tab.b 0 + tab.b 1 = 1 ∧ tab.c 1 * tab.b 1 = 1 / 2) ∧
    (tab.b 0 + tab.b 1 = 1 → tab.c 1 * tab.b 1 = 1 / 2 →
      ∀ (f : ℝ → ℝ → ℝ) (M₂ : ℝ), ContDiff ℝ 2 (Function.uncurry f) →
      (∀ p : ℝ × ℝ, ‖fderiv ℝ (fderiv ℝ (Function.uncurry f)) p‖ ≤ M₂) →
      ∀ (t₀ T y₀ : ℝ) (y : ℝ → ℝ), 0 < T → cauchyProblem f t₀ y₀ (Icc t₀ (t₀ + T)) y →
      ContDiffOn ℝ 3 y (Icc t₀ (t₀ + T)) →
      equation_11_14 (equation_11_70_increment tab f) t₀ T y 2) ∧
    (ButcherTableau.heun.b 0 + ButcherTableau.heun.b 1 = 1 ∧
      ButcherTableau.heun.c 1 * ButcherTableau.heun.b 1 = 1 / 2) ∧
    (ButcherTableau.modifiedEuler.b 0 + ButcherTableau.modifiedEuler.b 1 = 1 ∧
      ButcherTableau.modifiedEuler.c 1 * ButcherTableau.modifiedEuler.b 1 = 1 / 2) := by
  have hc0 : tab.c 0 = 0 := by
    rw [hrow 0, Fin.sum_univ_two, hex 0 0 le_rfl, hex 0 1 (by decide), add_zero]
  refine ⟨fun h1 h2 => tab.orderTwoConditions_of_hasOrderFor hc0 one_pos (h1 0 1 one_pos) h2,
    fun hb hcb f M₂ hf hM₂ t₀ T y₀ y hT hy hy3 => ?_, ?_, ?_⟩
  · have hF : ∀ p, HasFDerivAt (Function.uncurry f) (fderiv ℝ (Function.uncurry f) p) p :=
      fun p => (hf.differentiable (by norm_num) p).hasFDerivAt
    have hf' := hf
    have h2 : (2 : WithTop ℕ∞) = 1 + 1 := rfl
    rw [h2, contDiff_succ_iff_fderiv] at hf'
    have hF' : ∀ p, HasFDerivAt (fderiv ℝ (Function.uncurry f))
        (fderiv ℝ (fderiv ℝ (Function.uncurry f)) p) p := fun p =>
      (hf'.2.2.differentiable one_ne_zero p).hasFDerivAt
    obtain ⟨-, h2, h3⟩ := hasDerivWithinAt_iteratedDerivWithin_of_contDiffOn_three (by linarith) hy3
    obtain ⟨M₃, hM₃⟩ := (isCompact_Icc (a := t₀) (b := t₀ + T)).exists_bound_of_continuousOn
      (hy3.continuousOn_iteratedDerivWithin (m := 3) le_rfl (uniqueDiffOn_Icc (by linarith)))
    have h2' : ∀ s ∈ Icc t₀ (t₀ + T), HasDerivWithinAt (fun s => f s (y s))
        (iteratedDerivWithin 2 y (Icc t₀ (t₀ + T)) s) (Icc t₀ (t₀ + T)) s := fun s hs =>
      (h2 s hs).congr (fun s' hs' => (derivWithin_eq_of_cauchyProblem hT hy hs').symm)
        (derivWithin_eq_of_cauchyProblem hT hy hs).symm
    exact tab.hasOrderFor_two_of hex hrow hb hcb hF hF' hM₂ hy.2 h2' h3 hM₃
  · norm_num [ButcherTableau.heun]
  · norm_num [ButcherTableau.modifiedEuler]

/-! ### The order of the classical method (11.73) -/

/-- **Equation (11.73)** of [quarteroni2000numerical], order four. Let $f$ be $C^4$ on
$\mathbb{R} \times \mathbb{R}$, with $\|D^k f\| \le M_k$ everywhere for $k = 1, 2, 3, 4$. Let
$T > 0$, and let $y \in C^5([t_0, t_0 + T])$ solve the Cauchy problem $y' = f(t, y)$,
$y(t_0) = y_0$ on $[t_0, t_0 + T]$. Then the classical method (11.73) has order $4$ along $y$:
$$\tau(h) = O(h^4) \quad \text{as } h \to 0^+.$$

The source introduces (11.73) in Section 11.8 as an example of a fourth-order method and derives
it in Section 11.8.1 by keeping all the Taylor terms up to the fifth. The statement is the
scalar case of `ODE.rk4_hasOrderFor`: the derivatives $D^k f$ are the iterated `fderiv` of
$(t, v) \mapsto f(t, v)$, and $y'', \dots, y^{(5)}$ are the `iteratedDerivWithin` of $y$ on
$[t_0, t_0 + T]$. The bounds on the derivatives of $f$ make the constant uniform over the
horizon. That a $C^4$ field has $C^5$ solutions is assumed rather than derived, as in
`QuarteroniSaccoSaleri.Chapter11.twoStageOrderConditions`.

**Reading.** The order estimates make the regularity of the solution curve and uniform
derivative bounds on the field explicit. -/
theorem equation_11_73_order {M₁ M₂ M₃ M₄ : ℝ} (hf : ContDiff ℝ 4 (Function.uncurry f))
    (hM₁ : ∀ p : ℝ × ℝ, ‖fderiv ℝ (Function.uncurry f) p‖ ≤ M₁)
    (hM₂ : ∀ p : ℝ × ℝ, ‖fderiv ℝ (fderiv ℝ (Function.uncurry f)) p‖ ≤ M₂)
    (hM₃ : ∀ p : ℝ × ℝ, ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (Function.uncurry f))) p‖ ≤ M₃)
    (hM₄ : ∀ p : ℝ × ℝ,
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (Function.uncurry f)))) p‖ ≤ M₄)
    (hT : 0 < T) (hy : cauchyProblem f t₀ y₀ (Icc t₀ (t₀ + T)) y)
    (hy5 : ContDiffOn ℝ 5 y (Icc t₀ (t₀ + T))) :
    equation_11_14 (equation_11_70_increment equation_11_73 f) t₀ T y 4 := by
  have h4 : (4 : WithTop ℕ∞) = 3 + 1 := rfl
  have h3 : (3 : WithTop ℕ∞) = 2 + 1 := rfl
  have h2 : (2 : WithTop ℕ∞) = 1 + 1 := rfl
  have hf' := hf
  rw [h4, contDiff_succ_iff_fderiv] at hf'
  obtain ⟨hd₀, -, hf3⟩ := hf'
  rw [h3, contDiff_succ_iff_fderiv] at hf3
  obtain ⟨hd₁, -, hf2⟩ := hf3
  rw [h2, contDiff_succ_iff_fderiv] at hf2
  obtain ⟨hd₂, -, hf1⟩ := hf2
  have hd₃ := hf1.differentiable one_ne_zero
  have hlt : t₀ < t₀ + T := by linarith
  have hy₂ : ∀ s ∈ Icc t₀ (t₀ + T), HasDerivWithinAt (fun s => f s (y s))
      (iteratedDerivWithin 2 y (Icc t₀ (t₀ + T)) s) (Icc t₀ (t₀ + T)) s := fun s hs => by
    have h := hasDerivWithinAt_iteratedDerivWithin_of_contDiffOn hlt hy5 (j := 1) (by norm_num) hs
    rw [iteratedDerivWithin_one] at h
    exact h.congr (fun s' hs' => (derivWithin_eq_of_cauchyProblem hT hy hs').symm)
      (derivWithin_eq_of_cauchyProblem hT hy hs).symm
  obtain ⟨M₅, hM₅⟩ := (isCompact_Icc (a := t₀) (b := t₀ + T)).exists_bound_of_continuousOn
    (hy5.continuousOn_iteratedDerivWithin (m := 5) le_rfl (uniqueDiffOn_Icc hlt))
  exact rk4_hasOrderFor (fun p => (hd₀ p).hasFDerivAt) (fun p => (hd₁ p).hasFDerivAt)
    (fun p => (hd₂ p).hasFDerivAt) (fun p => (hd₃ p).hasFDerivAt) hM₁ hM₂ hM₃ hM₄ hy.2 hy₂
    (fun s hs => hasDerivWithinAt_iteratedDerivWithin_of_contDiffOn hlt hy5 (by norm_num) hs)
    (fun s hs => hasDerivWithinAt_iteratedDerivWithin_of_contDiffOn hlt hy5 (by norm_num) hs)
    (fun s hs => hasDerivWithinAt_iteratedDerivWithin_of_contDiffOn hlt hy5 (by norm_num) hs)
    hM₅

/-! ### §11.8.2: embedded pairs -/

/-- **Equation (11.76)** of [quarteroni2000numerical]. An **embedded pair** consists of two
$s$-stage Runge–Kutta methods of orders $p$ and $p + 1$ that share the matrix $A$, the nodes $c$
and so the stages, and that have weights $b$ and $\hat{b}$.

The definition is `ODE.EmbeddedPair s`. The orders are not part of the structure.

**Reading.** Stores weights without order conditions and proves the exact difference of two
steps. The accuracy of this difference as a local error estimate is outside the claim. -/
abbrev equation_11_76 (s : ℕ) := EmbeddedPair s

/-- **Equation (11.76)** of [quarteroni2000numerical], the error indicator. For an embedded pair,
the **error indicator** at $(t, u)$ is
$$h \sum_{i=1}^s E_i K_i, \qquad E = b - \hat{b},$$
where $K_i$ are the explicit stages at $(t, u)$. It is the difference of the two solutions, and
it estimates the local error of the lower-order method without further evaluations of $f$.

The definition is `ODE.EmbeddedPair.errorIndicator`.

**Reading.** Stores weights without order conditions and proves the exact difference of two
steps. The accuracy of this difference as a local error estimate is outside the claim. -/
noncomputable def equation_11_76_errorIndicator (P : equation_11_76 s) (f : ℝ → ℝ → ℝ) (h t u : ℝ) :
    ℝ :=
  P.errorIndicator f h t u

/-- **Equation (11.76)** of [quarteroni2000numerical], the error indicator as a difference. For an
embedded pair and all $h, t, u \in \mathbb{R}$, the error indicator equals
$h \sum_i (b_i - \hat{b}_i) K_i$ with the explicit stages $K_i$ at $(t, u)$, and it equals
$$\big(u + h F_b(t, u, h; f)\big) - \big(u + h F_{\hat{b}}(t, u, h; f)\big),$$
the difference of the two steps of the pair from $(t, u)$, where $F_b$ and $F_{\hat{b}}$ are the
increments (11.70) of the two methods.

The proof specializes `ODE.EmbeddedPair.errorIndicator_eq_sub`.

**Reading.** Stores weights without order conditions and proves the exact difference of two
steps. The accuracy of this difference as a local error estimate is outside the claim. -/
theorem equation_11_76_errorIndicator_eq (P : equation_11_76 s) (f : ℝ → ℝ → ℝ) (h t u : ℝ) :
    equation_11_76_errorIndicator P f h t u = h * ∑ i, (P.b i - P.bhat i) *
        P.toButcherTableau.explicitStages f h t u i ∧
      equation_11_76_errorIndicator P f h t u =
        (u + h * equation_11_70_increment P.toButcherTableau f t u u h) -
          (u + h * equation_11_70_increment P.toTableauHat f t u u h) :=
  ⟨rfl, P.errorIndicator_eq_sub f h t u⟩

/-- **Section 11.8.2** of [quarteroni2000numerical], the Runge–Kutta–Fehlberg 4(5) pair. It is the
six-stage embedded pair with the standard Fehlberg coefficients, in which the weights $b$ give
the fourth-order method and the weights $\hat{b}$ give the fifth-order method.

The definition is `ODE.rkf45`. -/
noncomputable def rkf45 : equation_11_76 6 :=
  ODE.rkf45

/-- **Section 11.8.2** of [quarteroni2000numerical], the coefficients of the Fehlberg pair. The pair
`QuarteroniSaccoSaleri.Chapter11.rkf45` is explicit and satisfies (11.72), both weight vectors
sum to $1$, and
$$\hat{b} - b = \Big(\frac{1}{360},\ 0,\ -\frac{128}{4275},\ -\frac{2197}{75240},\
  \frac{1}{50},\ \frac{2}{55}\Big).$$

The last row of the printed tableau equals $\hat b-b$. The prose defines $E=b-\hat b$.

**Reading.** Matches the printed last row, which is bhat−b despite prose defining E=b−bhat.
-/
theorem rkf45_spec :
    equation_11_71_explicit rkf45.toButcherTableau ∧ equation_11_72 rkf45.toButcherTableau ∧
    (∑ i, rkf45.b i = 1 ∧ ∑ i, rkf45.bhat i = 1) ∧
    (fun i => rkf45.bhat i - rkf45.b i) =
      ![1 / 360, 0, -128 / 4275, -2197 / 75240, 1 / 50, 2 / 55] :=
  ⟨rkf45_isExplicit, rkf45_isRowSum, rkf45_sum_b, rkf45_bhat_sub_b⟩

/-! ### §11.8.3: implicit methods -/

/-- **Section 11.8.3** of [quarteroni2000numerical], the Gauss–Legendre methods. The following hold.

* The one-stage Gauss–Legendre method is the implicit midpoint rule: $v$ is a step from $u$ at
  $t$ if and only if $v = u + h f(t + h/2, (u + v)/2)$. It is implicit, and $\sum_i b_i = 1$ and
  $\sum_i b_i c_i = 1/2$.
* The two-stage Gauss–Legendre method has
$$c = \Big(\frac{1}{2} - \frac{\sqrt{3}}{6},\ \frac{1}{2} + \frac{\sqrt{3}}{6}\Big), \qquad A =
  \begin{bmatrix} 1/4 & 1/4 - \sqrt{3}/6 \\ 1/4 + \sqrt{3}/6 & 1/4 \end{bmatrix}, \qquad b =
  \Big(\frac{1}{2}, \frac{1}{2}\Big).$$
* The two-stage method satisfies the collocation identities
  $\sum_j c_j^{k-1} a_{ij} = c_i^k / k$ and $\sum_j c_j^{k-1} b_j = 1/k$ for $k = 1, 2$.

The source gives the implicit midpoint rule order two, for which the two sums of the first item
are the order conditions, and the two-stage method order four; these orders are not formalized.
The nodes of the two-stage method are the roots of the Legendre polynomial $L_2$ in the variable
$x = 2c - 1$. The tableaux are `ODE.ButcherTableau.implicitMidpoint` and
`ODE.ButcherTableau.gaussLegendre2`. The maximal order $2s$, which the source quotes without
proof, is not formalized.

**Partial.** Gives the two schemes and the moment conditions through the stated stage count. It
does not establish the general $2s$ order claim.

**Reading.** Same implicit midpoint and two-stage coefficients and moment conditions; no order
theorem.
-/
theorem gaussLegendre_tableaux :
    (∀ (h t u v : ℝ), ButcherTableau.implicitMidpoint.stepRel f h t u v ↔
      v = u + h * f (t + h / 2) (2⁻¹ * (u + v))) ∧
    implicitRungeKutta ButcherTableau.implicitMidpoint ∧
    (∑ i, ButcherTableau.implicitMidpoint.b i = 1 ∧
      ∑ i, ButcherTableau.implicitMidpoint.b i * ButcherTableau.implicitMidpoint.c i = 1 / 2) ∧
    ButcherTableau.gaussLegendre2.c = ![1 / 2 - Real.sqrt 3 / 6, 1 / 2 + Real.sqrt 3 / 6] ∧
    ButcherTableau.gaussLegendre2.A =
      !![1 / 4, 1 / 4 - Real.sqrt 3 / 6; 1 / 4 + Real.sqrt 3 / 6, 1 / 4] ∧
    ButcherTableau.gaussLegendre2.b = ![1 / 2, 1 / 2] ∧
    ((∀ i, ∑ j, ButcherTableau.gaussLegendre2.A i j = ButcherTableau.gaussLegendre2.c i) ∧
      (∀ i, ∑ j, ButcherTableau.gaussLegendre2.c j * ButcherTableau.gaussLegendre2.A i j =
        ButcherTableau.gaussLegendre2.c i ^ 2 / 2) ∧
      ∑ j, ButcherTableau.gaussLegendre2.b j = 1 ∧
      ∑ j, ButcherTableau.gaussLegendre2.c j * ButcherTableau.gaussLegendre2.b j = 1 / 2) := by
  refine ⟨fun h t u v => ?_, fun hex => ?_, ButcherTableau.implicitMidpoint_orderConditions, rfl,
    rfl, rfl, ButcherTableau.gaussLegendre2_collocation⟩
  · rw [ButcherTableau.stepRel_implicitMidpoint_iff]
    simp only [smul_eq_mul]
  · have := hex 0 0 le_rfl
    simp [ButcherTableau.implicitMidpoint] at this

/-- **Section 11.8.3** of [quarteroni2000numerical], the Radau methods. The one-stage Radau IIA
method, with $A = (1)$, $b = (1)$ and $c = (1)$, has the step relation of the backward Euler
method (11.8), and it is implicit. The two-stage Radau IIA method has
$$c = \Big(\frac{1}{3}, 1\Big), \qquad A = \begin{bmatrix} 5/12 & -1/12 \\ 3/4 & 1/4
  \end{bmatrix}, \qquad b = \Big(\frac{3}{4}, \frac{1}{4}\Big),$$
and it is implicit.

The source gives the two-stage method order three. The tableaux are
`ODE.ButcherTableau.radauIIA1` and `ODE.ButcherTableau.radauIIA2`. The maximal order $2s - 1$ is
not formalized.

**Partial.** Gives the backward Euler and two-stage Radau arrays. The text also shows an
endpoint-first one-stage array.

**Reading.** Includes middle and right tableaux, without the first or order proof.
-/
theorem radau_tableaux :
    ButcherTableau.radauIIA1.stepRel f = OneStep.ofIncrement (equation_11_8 f) ∧
    implicitRungeKutta ButcherTableau.radauIIA1 ∧
    ButcherTableau.radauIIA2.c = ![1 / 3, 1] ∧
    ButcherTableau.radauIIA2.A = !![5 / 12, -1 / 12; 3 / 4, 1 / 4] ∧
    ButcherTableau.radauIIA2.b = ![3 / 4, 1 / 4] ∧ implicitRungeKutta ButcherTableau.radauIIA2 := by
  refine ⟨ButcherTableau.stepRel_radauIIA1 f, fun hex => ?_, rfl, rfl, rfl, fun hex => ?_⟩
  · have := hex 0 0 le_rfl
    simp [ButcherTableau.radauIIA1] at this
  · have := hex 0 0 le_rfl
    simp [ButcherTableau.radauIIA2] at this

/-- **Section 11.8.3** of [quarteroni2000numerical], the Lobatto methods. The two-stage Lobatto IIIA
method has
$$c = (0, 1), \qquad A = \begin{bmatrix} 0 & 0 \\ 1/2 & 1/2 \end{bmatrix}, \qquad b =
  \Big(\frac{1}{2}, \frac{1}{2}\Big).$$
Its step relation is that of the Crank–Nicolson method (11.9), and it is implicit.

The tableau is `ODE.ButcherTableau.lobattoIIIA2`. The maximal order $2s - 2$ is not formalized.

**Partial.** Gives the first printed Lobatto array and its equivalence with Crank–Nicolson.

**Reading.** Includes only Crank–Nicolson of the three printed tableaux.
-/
theorem lobatto_tableaux :
    ButcherTableau.lobattoIIIA2.stepRel f = OneStep.ofIncrement (equation_11_9 f) ∧
    ButcherTableau.lobattoIIIA2.c = ![0, 1] ∧
    ButcherTableau.lobattoIIIA2.A = !![0, 0; 1 / 2, 1 / 2] ∧
    ButcherTableau.lobattoIIIA2.b = ![1 / 2, 1 / 2] ∧
    implicitRungeKutta ButcherTableau.lobattoIIIA2 := by
  refine ⟨ButcherTableau.stepRel_lobattoIIIA2 f, rfl, rfl, rfl, fun hex => ?_⟩
  have := hex 1 1 le_rfl
  simp [ButcherTableau.lobattoIIIA2] at this

/-- **Section 11.8.3** of [quarteroni2000numerical], the three-stage DIRK method. For
$\mu \in \mathbb{R}$ the tableau `ODE.ButcherTableau.dirk3 μ` has
$$c = \Big(\frac{1 + \mu}{2},\ \frac{1}{2},\ \frac{1 - \mu}{2}\Big), \qquad A = \begin{bmatrix}
  (1 + \mu)/2 & 0 & 0 \\ -\mu/2 & (1 + \mu)/2 & 0 \\ 1 + \mu & -1 - 2\mu & (1 + \mu)/2
  \end{bmatrix}, \qquad b = \Big(\frac{1}{6\mu^2},\ 1 - \frac{1}{3\mu^2},\
  \frac{1}{6\mu^2}\Big),$$
and it is semi-implicit.

The source takes $\mu$ to be a root of $3\mu^3 - 3\mu - 1 = 0$; the statement holds for every
$\mu$. Its order four is not formalized.

**Generalization.** The tableau and its lower triangularity are stated for every real $\mu$.
The printed family requires $3\mu^3-3\mu-1=0$. -/
theorem dirk_tableau (μ : ℝ) :
    (ButcherTableau.dirk3 μ).c = ![(1 + μ) / 2, 1 / 2, (1 - μ) / 2] ∧
    (ButcherTableau.dirk3 μ).A =
      !![(1 + μ) / 2, 0, 0; -μ / 2, (1 + μ) / 2, 0; 1 + μ, -1 - 2 * μ, (1 + μ) / 2] ∧
    (ButcherTableau.dirk3 μ).b = ![1 / (6 * μ ^ 2), 1 - 1 / (3 * μ ^ 2), 1 / (6 * μ ^ 2)] ∧
    equation_11_71_semiImplicit (ButcherTableau.dirk3 μ) :=
  ⟨rfl, rfl, rfl, ButcherTableau.dirk3_isSemiImplicit μ⟩

/-! ### §11.8.4: the stability function and absolute stability -/

/-- **Section 11.8.4** of [quarteroni2000numerical]. The **stability function** of a Runge–Kutta
method with Butcher array $(A, b, c)$ is
$$R(z) = 1 + z\, b^T (I - zA)^{-1} \mathbf{1}, \qquad z \in \mathbb{C},$$
where $\mathbf{1}$ is the vector of ones.

The definition is `ODE.ButcherTableau.stabilityFunction`. It uses the Mathlib inverse, which is
$0$ on a singular matrix, so $R(z) = 1$ when $I - zA$ is singular.

**Reading.** Uses the total matrix inverse in the definition and requires invertibility for the
step equivalence. The slope variables are $\lambda$ times the stage values used in the source. -/
noncomputable def stabilityFunction (tab : ButcherTableau s) (z : ℂ) : ℂ :=
  tab.stabilityFunction z

/-- **Equation (11.77)** of [quarteroni2000numerical], the method on the test problem. Let
$(A, b, c)$ be a Butcher array, $h \in \mathbb{R}$ and $\lambda \in \mathbb{C}$, and apply the
method to $y' = \lambda y$. Then:

* for all $t \in \mathbb{R}$, $u \in \mathbb{C}$ and $K \in \mathbb{C}^s$, the vector $K$ is a
  vector of stages at $(t, u)$ if and only if $(I - h\lambda A) K = \lambda u \mathbf{1}$;
* if $I - h\lambda A$ is invertible, then $v$ is a step from $u$ if and only if
  $v = R(h\lambda) u$;
* $R(z) = 1 + z\, b^T (I - zA)^{-1} \mathbf{1}$ for every $z \in \mathbb{C}$.

The test problem is `QuarteroniSaccoSaleri.Chapter11.testProblem`. The proof specializes
`ODE.ButcherTableau.isStages_testField_iff` and `ODE.ButcherTableau.stepRel_testField_iff`.

**Reading.** Uses the total matrix inverse in the definition and requires invertibility for the
step equivalence. The slope variables are $\lambda$ times the stage values used in the source. -/
theorem equation_11_77 (tab : ButcherTableau s) (lam : ℂ) :
    (∀ (t : ℝ) (u : ℂ) (K : Fin s → ℂ), tab.IsStages (testProblem lam) h t u K ↔
      (1 - ((h : ℂ) * lam) • tab.complexA) *ᵥ K = (lam * u) • fun _ => (1 : ℂ)) ∧
    (IsUnit (1 - ((h : ℂ) * lam) • tab.complexA) → ∀ (t : ℝ) (u v : ℂ),
      tab.stepRel (testProblem lam) h t u v ↔ v = stabilityFunction tab (h * lam) * u) ∧
    ∀ z : ℂ, stabilityFunction tab z =
      1 + z * (tab.complexB ⬝ᵥ ((1 - z • tab.complexA)⁻¹ *ᵥ fun _ => 1)) :=
  ⟨fun _ _ K => tab.isStages_testField_iff K,
    fun hinv t u v => tab.stepRel_testField_iff hinv t u v, fun _ => rfl⟩

/-- **Section 11.8.4** of [quarteroni2000numerical], absolute stability of Runge–Kutta methods. Let
$(A, b, c)$ be a Butcher array with stability function $R$. Then:

* for all $\lambda \in \mathbb{C}$ and $h > 0$ with $I - h\lambda A$ invertible, the method is
  absolutely stable (Definition 11.6) for $y' = \lambda y$ with step $h$ if and only if
  $|R(h\lambda)| < 1$;
* for every $z \in \mathbb{C}$ with $I - zA$ invertible, $z$ lies in the region of absolute
  stability $\mathcal{A}$ of (11.26) if and only if $|R(z)| < 1$;
* if the method is explicit, then $z \in \mathcal{A}$ if and only if $|R(z)| < 1$, for every
  $z \in \mathbb{C}$.

**Correction.** The source gives the region of absolute stability as $\mathcal{A} = \{z \in
\mathbb{C} : |R(z)| < 1\}$ without a condition on $I - zA$. The characterization is stated here
only where $I - zA$ is invertible, as in
`ODE.ButcherTableau.mem_absStabilityRegion_iff_of_isUnit`, because the condition is needed. For
an explicit method the matrix $I - zA$ is always invertible.

The proof specializes `ODE.ButcherTableau.mem_absStabilityRegion_iff_of_isUnit` and
`ODE.ButcherTableau.mem_absStabilityRegion_iff_of_isExplicit`. -/
theorem rungeKutta_absStable_iff (tab : ButcherTableau s) :
    (∀ (lam : ℂ) (h : ℝ), 0 < h → IsUnit (1 - ((h : ℂ) * lam) • tab.complexA) →
      (definition_11_6 tab.stepRel lam h ↔ ‖stabilityFunction tab (h * lam)‖ < 1)) ∧
    (∀ z : ℂ, IsUnit (1 - z • tab.complexA) →
      (z ∈ equation_11_26 tab.stepRel ↔ ‖stabilityFunction tab z‖ < 1)) ∧
    (equation_11_71_explicit tab →
      ∀ z : ℂ, z ∈ equation_11_26 tab.stepRel ↔ ‖stabilityFunction tab z‖ < 1) := by
  refine ⟨fun lam h hh hinv => ?_, fun z hz => tab.mem_absStabilityRegion_iff_of_isUnit hz,
    fun hex z => tab.mem_absStabilityRegion_iff_of_isExplicit hex z⟩
  rw [definition_11_6, testProblem,
    isAbsStable_iff_mem_absStabilityRegion (M := tab.stepRel) tab.testField_scaleInvariant hh]
  exact tab.mem_absStabilityRegion_iff_of_isUnit hinv

/-- **Section 11.8.4** of [quarteroni2000numerical], explicit methods. Let the Runge–Kutta method
with Butcher array $(A, b, c)$ be explicit, with stability function $R$. Then:

* $R(z) = \det(I - zA + z \mathbf{1} b^T)$ and $\det(I - zA) = 1$ for every $z \in \mathbb{C}$,
  so $R(z) = \det(I - zA + z \mathbf{1} b^T) / \det(I - zA)$;
* $R$ agrees with the polynomial `ODE.ButcherTableau.stabilityPolynomial` of the tableau;
* if $\sum_i b_i = 1$, the region of absolute stability $\mathcal{A}$ is bounded and the method
  is not A-stable;
* if the method has order $s$ (11.14) along the solution $e^t$ of $y' = y$ on $[0, 1]$, then
  $R(z) = \sum_{k=0}^s z^k / k!$ for every $z$;
* the classical method (11.73) has $R(z) = 1 + z + z^2/2 + z^3/6 + z^4/24$.

**Generalization.** The source states $R(z) = \sum_{k=0}^s z^k / k!$ for $s = 1, \dots, 4$,
where explicit $s$-stage methods of order $s$ exist. It is proved here for every $s$.

The polynomial `ODE.ButcherTableau.stabilityPolynomial` has degree at most $s$. The proof
specializes `ODE.ButcherTableau.stabilityFunction_eq_det_of_isExplicit`,
`ODE.ButcherTableau.det_one_sub_smul_complexA`,
`ODE.ButcherTableau.isBounded_absStabilityRegion`,
`ODE.ButcherTableau.not_isAStable_of_isExplicit`,
`ODE.ButcherTableau.stabilityFunction_eq_truncExp_of_hasOrder` and `ODE.stabilityFunction_rk4`.

**Reading.** The boundedness conclusion assumes $\sum_i b_i=1$. The truncated exponential
formula holds for arbitrary stage count under the order condition on the scalar exponential
test. -/
theorem rungeKutta_explicit_stabilityFunction (tab : ButcherTableau s)
    (hex : equation_11_71_explicit tab) :
    (∀ z : ℂ, stabilityFunction tab z = (1 - z • tab.complexA +
      z • (Matrix.replicateCol Unit (fun _ => (1 : ℂ)) *
        Matrix.replicateRow Unit tab.complexB)).det ∧ (1 - z • tab.complexA).det = 1) ∧
    (∀ z : ℂ, stabilityFunction tab z = tab.stabilityPolynomial.eval z) ∧
    (∑ i, tab.b i = 1 →
      Bornology.IsBounded (equation_11_26 tab.stepRel) ∧ ¬ aStable tab.stepRel) ∧
    (equation_11_14 (equation_11_70_increment tab fun _ y => y) 0 1 Real.exp s →
      ∀ z : ℂ, stabilityFunction tab z = ∑ k ∈ range (s + 1), z ^ k / k.factorial) ∧
    ∀ z : ℂ, stabilityFunction equation_11_73 z = 1 + z + z ^ 2 / 2 + z ^ 3 / 6 + z ^ 4 / 24 :=
  ⟨fun z => ⟨tab.stabilityFunction_eq_det_of_isExplicit hex z, tab.det_one_sub_smul_complexA hex z⟩,
    fun z => tab.stabilityFunction_eq_eval hex z,
    fun hb => ⟨tab.isBounded_absStabilityRegion hex hb, tab.not_isAStable_of_isExplicit hex hb⟩,
    fun hord z => tab.stabilityFunction_eq_truncExp_of_hasOrder hex hord z,
    fun z => stabilityFunction_rk4 z⟩

/-! ### Property 11.4: the order of an explicit method is at most its number of stages -/

/-- As $h \to 0^+$, $h^q = O(h^p)$ for $p \le q$. -/
private theorem isBigO_pow_of_le {p q : ℕ} (hpq : p ≤ q) :
    (fun h : ℝ => h ^ q) =O[𝓝[>] 0] fun h : ℝ => h ^ p := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [Ioc_mem_nhdsGT zero_lt_one] with h hh
  rw [Real.norm_of_nonneg (pow_nonneg hh.1.le _), Real.norm_of_nonneg (pow_nonneg hh.1.le _),
    one_mul]
  exact pow_le_pow_of_le_one hh.1.le hh.2 hpq

/-- A method of order $q$ (11.14) along $y$ has order $p$ along $y$ for every $p \le q$. -/
private theorem equation_11_14_of_le {Φ : OneStep.Increment ℝ} {t₀ T : ℝ} {y : ℝ → ℝ} {p q : ℕ}
    (hpq : p ≤ q) (hord : equation_11_14 Φ t₀ T y q) : equation_11_14 Φ t₀ T y p :=
  equation_11_14_iff.2 ((equation_11_14_iff.1 hord).trans (isBigO_pow_of_le hpq))

/-- If an explicit method has order $m$ along the solution $e^t$ of $y' = y$ on $[0, 1]$, then
$R(h) - e^h = O(h^{m+1})$ as $h \to 0^+$, because one step from $1$ on this problem is $R(h)$. -/
private theorem isBigO_stabilityFunction_sub_exp {m : ℕ} (tab : ButcherTableau s)
    (hex : tab.IsExplicit)
    (hord : OneStep.HasOrderFor (tab.explicitIncrement fun _ y => y) 0 1 Real.exp m) :
    (fun h : ℝ => tab.stabilityFunction h - Complex.exp h) =O[𝓝[>] 0]
      fun h : ℝ => h ^ (m + 1) := by
  have hmul : (fun h : ℝ => h * OneStep.globalLte (tab.explicitIncrement fun _ y => y)
      0 1 Real.exp h) =O[𝓝[>] 0] fun h : ℝ => h ^ (m + 1) := by
    have := (isBigO_refl (fun h : ℝ => h) (𝓝[>] 0)).mul hord
    refine this.congr' EventuallyEq.rfl (Eventually.of_forall fun h => ?_)
    simp [pow_succ']
  refine (IsBigO.of_bound 1 ?_).trans hmul
  filter_upwards [Ioc_mem_nhdsGT zero_lt_one] with h hh
  have hN : 0 < gridCount 1 h := (le_gridCount_iff zero_le_one hh.1).2 (by simpa using hh.2)
  have hle := OneStep.norm_lte_le_globalLte (Φ := tab.explicitIncrement fun _ y => y) (t₀ := 0)
    (T := 1) (y := Real.exp) hN
  rw [node_zero] at hle
  have e : tab.stabilityFunction h - Complex.exp h =
      -((h * OneStep.lte (tab.explicitIncrement fun _ y => y) h Real.exp 0 : ℝ) : ℂ) := by
    rw [tab.stabilityFunction_ofReal hex, ← Complex.ofReal_exp, ← Complex.ofReal_sub,
      ← Complex.ofReal_neg]
    congr 1
    simp only [OneStep.lte, smul_eq_mul, zero_add, Real.exp_zero]
    have : tab.explicitIncrement (fun _ y => y) 0 1 (Real.exp h) h =
        tab.explicitIncrement (fun _ y => y) 0 1 1 h := rfl
    rw [this]
    have hne : h ≠ 0 := hh.1.ne'
    field_simp
    ring
  rw [e, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos hh.1, one_mul,
    Real.norm_eq_abs, abs_mul, abs_of_pos hh.1, abs_of_nonneg (OneStep.globalLte_nonneg _)]
  exact mul_le_mul_of_nonneg_left hle hh.1.le

/-- As $h \to 0^+$, $e^h - \sum_{k=0}^m h^k / k! = O(h^{m+1})$. -/
private theorem isBigO_exp_sub_truncExp (m : ℕ) :
    (fun h : ℝ => Complex.exp h - ∑ k ∈ range (m + 1), (h : ℂ) ^ k / k.factorial) =O[𝓝[>] 0]
      fun h : ℝ => h ^ (m + 1) := by
  refine IsBigO.of_bound ((m.succ.succ : ℝ) * ((m.succ.factorial : ℝ) * (m.succ : ℝ))⁻¹) ?_
  filter_upwards [Ioc_mem_nhdsGT zero_lt_one] with h hh
  have hx : ‖(h : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg hh.1.le]
    exact hh.2
  have := Complex.exp_bound hx (Nat.succ_pos m)
  rw [Complex.norm_real, Real.norm_of_nonneg hh.1.le] at this
  rw [Real.norm_of_nonneg (pow_pos hh.1 _).le, mul_comm]
  exact this

/-- If an explicit $s$-stage method has order $m \ge s$ along the solution $e^t$ of $y' = y$ on
$[0, 1]$, its stability polynomial is $\sum_{k=0}^m X^k / k!$.

**Reading.** Truncated polynomial identity at arbitrary tested order m≥s.
-/
private theorem stabilityPolynomial_eq_truncExp {m : ℕ} (tab : ButcherTableau s)
    (hex : tab.IsExplicit) (hsm : s ≤ m)
    (hord : OneStep.HasOrderFor (tab.explicitIncrement fun _ y => y) 0 1 Real.exp m) :
    tab.stabilityPolynomial =
      ∑ k ∈ range (m + 1), Polynomial.C ((k.factorial : ℂ)⁻¹) * Polynomial.X ^ k := by
  have hSeval : ∀ w : ℂ, (∑ k ∈ range (m + 1),
      Polynomial.C ((k.factorial : ℂ)⁻¹) * Polynomial.X ^ k).eval w =
        ∑ k ∈ range (m + 1), w ^ k / k.factorial := by
    intro w
    rw [Polynomial.eval_finsetSum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
      div_eq_mul_inv, mul_comm]
  have hQdeg : (tab.stabilityPolynomial -
      ∑ k ∈ range (m + 1), Polynomial.C ((k.factorial : ℂ)⁻¹) * Polynomial.X ^ k).natDegree
        ≤ m := by
    refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · refine Polynomial.natDegree_add_le_of_degree_le (by simp) ?_
      refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
      exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans
        ((Finset.mem_range.1 hk).trans_le hsm)
    · refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
      exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans
        (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))
  have hQ : tab.stabilityPolynomial -
      ∑ k ∈ range (m + 1), Polynomial.C ((k.factorial : ℂ)⁻¹) * Polynomial.X ^ k = 0 := by
    refine Polynomial.eq_zero_of_isBigO_pow_succ m _ hQdeg ?_
    refine ((isBigO_stabilityFunction_sub_exp tab hex hord).add
      (isBigO_exp_sub_truncExp m)).congr' (Eventually.of_forall fun h => ?_) EventuallyEq.rfl
    change tab.stabilityFunction h - Complex.exp h +
        (Complex.exp h - ∑ k ∈ range (m + 1), (h : ℂ) ^ k / k.factorial) =
      Polynomial.eval (h : ℂ) (tab.stabilityPolynomial -
        ∑ k ∈ range (m + 1), Polynomial.C ((k.factorial : ℂ))⁻¹ * Polynomial.X ^ k)
    rw [Polynomial.eval_sub, hSeval, tab.stabilityFunction_eq_eval hex, sub_add_sub_cancel]
  exact sub_eq_zero.1 hQ

/-- **Property 11.4** of [quarteroni2000numerical], first clause (Butcher's first order barrier).
Let the $s$-stage Runge–Kutta method with Butcher array $(A, b, c)$ be explicit. If the method
has order $q$ (11.14) along the solution $e^t$ of the test problem $y' = y$ on $[0, 1]$, then
$q \le s$.

**Generalization.** The source states that the order of an explicit $s$-stage method is at most
$s$. Here the order is needed only along one solution of $y' = y$; this is also the form in
which Table 11.1 of the source, for $s = 1, \dots, 4$, is read.

The proof is the argument of Section 11.8.4, not Butcher's. For an explicit method $R$ is a
polynomial of degree at most $s$
(`QuarteroniSaccoSaleri.Chapter11.rungeKutta_explicit_stabilityFunction`), and one step from $1$
on $y' = y$ is $R(h)$, so order $q$ gives $R(h) - e^h = O(h^{q+1})$. If $q > s$, then $R$ would
be $\sum_{k \le s+1} X^k / k!$, whose coefficient $1/(s+1)!$ in degree $s + 1$ is not zero. The
other clauses of Property 11.4 are not formalized. -/
theorem property_11_4_order_le_stages {q : ℕ} (tab : ButcherTableau s)
    (hex : equation_11_71_explicit tab)
    (hord : equation_11_14 (equation_11_70_increment tab fun _ y => y) 0 1 Real.exp q) :
    q ≤ s := by
  by_contra hq
  rw [not_le] at hq
  have hord' : OneStep.HasOrderFor (tab.explicitIncrement fun _ y => y) 0 1 Real.exp (s + 1) :=
    equation_11_14_of_le hq hord
  have hP := stabilityPolynomial_eq_truncExp tab hex (Nat.le_succ s) hord'
  have hcoeff : tab.stabilityPolynomial.coeff (s + 1) = (((s + 1).factorial : ℂ))⁻¹ := by
    rw [hP, Polynomial.finsetSum_coeff, Finset.sum_eq_single (s + 1)]
    · simp
    · intro k _ hk
      simp [Ne.symm hk]
    · intro h
      exact absurd (Finset.mem_range.2 (by omega)) h
  have hdeg : tab.stabilityPolynomial.natDegree ≤ s := by
    simp only [ODE.ButcherTableau.stabilityPolynomial]
    refine Polynomial.natDegree_add_le_of_degree_le (by simp) ?_
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
    exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (Finset.mem_range.1 hk)
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)] at hcoeff
  exact inv_ne_zero (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero (s + 1))) hcoeff.symm

end QuarteroniSaccoSaleri.Chapter11
