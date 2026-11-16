/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecificLimits.Normed
import Numlib.Analysis.Calculus.Taylor
import Numlib.Analysis.ODE.DiscreteGronwall

/-!
# One-step methods for the Cauchy problem

This module develops the theory of one-step methods for the Cauchy problem $y' = f(t, y)$,
$y(t_0) = y_0$, with values in a real normed space $E$. It follows §11.2–11.3 of
[quarteroni2000numerical]; §10.2 of [kress1998numerical] gives the same theory. On the horizon
$I = [t_0, t_0 + T]$, the grid has the nodes $t_n = t_0 + nh$ for
$0 \le n \le N_h = \lfloor T/h \rfloor$. A method is given by an increment function $\Phi$ through
$u_{n+1} = u_n + h\,\Phi(t_n, u_n, u_{n+1}; h)$, or more generally by a step relation, which says
which values $u_{n+1}$ are admissible from $u_n$. Along a curve $y$, the local truncation error is
$\tau_{n+1}(h) = (y(t_{n+1}) - y(t_n))/h - \Phi(t_n, y(t_n), y(t_{n+1}); h)$ and the global
truncation error is $\tau(h) = \max_{n < N_h} \|\tau_{n+1}(h)\|$. The method is consistent along $y$
if $\tau(h) \to 0$ as $h \to 0^+$, and it has order $p$ if $\tau(h) = O(h^p)$.

The module proves the zero-stability theorem (Theorem 11.1) and the convergence theorem (Theorem
11.2) for an increment that is Lipschitz in the state, with the error bound (11.20). It defines the
forward Euler, backward Euler, Crank–Nicolson, Heun and θ-methods and bounds their local truncation
errors: the two Euler methods have order $1$, Crank–Nicolson and Heun's method have order $2$, and
the θ-method has order $1$. Finally it treats absolute stability on the test equation
$y' = \lambda y$ (§11.3.3). The regions of absolute stability of forward Euler, backward Euler,
Crank–Nicolson and Heun's method are $|1 + z| < 1$, $|1 - z| > 1$, $\operatorname{Re} z < 0$ and
$|1 + z + z^2/2| < 1$. Hence backward Euler and Crank–Nicolson are A-stable, and forward Euler and
Heun's method are not.

## Main definitions

* `ODE.gridCount`: the number of steps $N_h = \lfloor T/h \rfloor$ on the horizon $T$.
* `ODE.node`: the grid node $t_n = t_0 + nh$.
* `ODE.OneStep.Increment`: an increment function $\Phi(t, u, v; h)$.
* `ODE.OneStep.StepRel`: a step relation, which says which values are admissible after one step.
* `ODE.OneStep.ofIncrement`: the step relation $v = u + h\,\Phi(t, u, v; h)$ of an increment
  function.
* `ODE.OneStep.IsOrbit`: a sequence whose consecutive terms are related by the step relation.
* `ODE.OneStep.IsOrbitWith`: an orbit perturbed by $h\delta_{n+1}$ at each step, as in (11.16).
* `ODE.OneStep.lte`: the local truncation error $\tau_{n+1}(h)$ of (11.12).
* `ODE.OneStep.globalLte`: the global truncation error $\tau(h)$.
* `ODE.OneStep.IsConsistentFor`: consistency, $\tau(h) \to 0$ as $h \to 0^+$.
* `ODE.OneStep.HasOrderFor`: order $p$, $\tau(h) = O(h^p)$.
* `ODE.OneStep.IsZeroStable`: zero-stability, Definition 11.4.
* `ODE.OneStep.LipschitzIncrement`: the Lipschitz hypothesis (11.18) on the increment.
* `ODE.OneStep.IsConvergentFor`: convergence, Definition 11.5.
* `ODE.OneStep.IsConvergentWithOrderFor`: convergence with order $p$, Definition 11.5.
* `ODE.OneStep.forwardEuler`: the forward Euler method (11.7).
* `ODE.OneStep.backwardEuler`: the backward Euler method (11.8).
* `ODE.OneStep.crankNicolson`: the Crank–Nicolson method (11.9).
* `ODE.OneStep.heun`: Heun's method (11.10).
* `ODE.OneStep.theta`: the θ-method, which contains the Euler methods and Crank–Nicolson.
* `ODE.testField`: the field $f(t, y) = \lambda y$ of the test equation (11.24).
* `ODE.OneStep.IsAbsStable`: absolute stability, Definition 11.6.
* `ODE.OneStep.absStabilityRegion`: the region of absolute stability (11.26).
* `ODE.OneStep.IsAStable`: A-stability, the left half-plane lies in the region of absolute
  stability.

## Main results

* `ODE.OneStep.isConsistentFor_of_tendsto_increment`: the consistency criterion (11.13).
* `ODE.OneStep.norm_sub_le_of_lipschitzIncrement_of_succ_eq`: two recursions with a Lipschitz
  increment, one of them perturbed by $h\delta_{n+1}$ with $\|\delta_k\| \le \varepsilon$, differ by
  at most $(\|z_0 - u_0\| + nh\varepsilon)\,e^{nh\Lambda}$.
* `ODE.OneStep.isZeroStable_of_lipschitzIncrement`: a Lipschitz increment gives a zero-stable method
  (Theorem 11.1).
* `ODE.OneStep.norm_sub_le_globalLte`: the error bound $\|y(t_n) - u_n\| \le (\|y(t_0) - u_0\| +
  nh\,\tau(h))\,e^{nh\Lambda}$ (11.20).
* `ODE.OneStep.isConvergentFor_of_isConsistentFor`: consistency and a Lipschitz increment give
  convergence (Theorem 11.2).
* `ODE.OneStep.isConvergentWithOrderFor_of_hasOrderFor`: order $p$ and a Lipschitz increment give
  convergence with order $p$ (Theorem 11.2).
* `ODE.OneStep.hasOrderFor_forwardEuler`, `ODE.OneStep.hasOrderFor_backwardEuler`: the Euler methods
  have order $1$.
* `ODE.OneStep.hasOrderFor_crankNicolson`, `ODE.OneStep.hasOrderFor_heun`: Crank–Nicolson and Heun's
  method have order $2$.
* `ODE.OneStep.hasOrderFor_theta`: the θ-method has order $1$.
* `ODE.OneStep.norm_sub_le_forwardEuler`: the direct error bound (11.22) for forward Euler.
* `ODE.OneStep.mem_absStabilityRegion_forwardEuler_iff`: the region of forward Euler is
  $|1 + z| < 1$ (11.27).
* `ODE.OneStep.mem_absStabilityRegion_backwardEuler_iff`: the region of backward Euler is
  $|1 - z| > 1$.
* `ODE.OneStep.mem_absStabilityRegion_crankNicolson_iff`: the region of Crank–Nicolson is
  $\operatorname{Re} z < 0$.
* `ODE.OneStep.mem_absStabilityRegion_heun_iff`: the region of Heun's method is
  $|1 + z + z^2/2| < 1$.
* `ODE.OneStep.isAStable_backwardEuler`, `ODE.OneStep.isAStable_crankNicolson`: backward Euler and
  Crank–Nicolson are A-stable.
* `ODE.OneStep.not_isAStable_forwardEuler`, `ODE.OneStep.not_isAStable_heun`: forward Euler and
  Heun's method are not A-stable.

## Proof outline

Theorems 11.1 and 11.2 rest on one estimate. Let two recursions use the same increment, and let one
of them be perturbed by $h\delta_{n+1}$ at each step. Their difference $w_n$ satisfies $\|w_{n+1}\|
\le (1 + h\Lambda)\|w_n\| + h\varepsilon$, and the discrete Gronwall lemma
`Gronwall.discrete_sum_const_of_le` bounds it. Theorem 11.1 is the case of two orbits. Theorem 11.2
is the case where the perturbed recursion is the exact solution, whose perturbations are its local
truncation errors (`ODE.OneStep.lte_spec`). The truncation errors of the elementary methods come
from the Taylor bounds `norm_sub_sub_smul_le_mul_sq_div_two` and
`norm_sub_sub_smul_add_le_mul_pow_three_div_twelve` of `Numlib.Analysis.Calculus.Taylor`. On the
test equation, every orbit of each of the four methods is a geometric sequence $u_n = r^n u_0$, and
the method is absolutely stable if and only if $|r| < 1$.

## Implementation notes

* An increment function is a map `Φ : ℝ → E → E → ℝ → E`, applied as `Φ t u v h`. The source writes
  $\Phi(t_n, u_n, f_n; h)$ with $f_n = f(t_n, u_n)$ as a separate argument. Here the field $f$ is
  part of $\Phi$ (`ODE.OneStep.forwardEuler f`, `ODE.OneStep.heun f`, …), which carries the same
  information.
* A method is a step relation `S h t u v : Prop` rather than a function, because the step of an
  implicit method solves an equation that may have no solution or several, and because implicit
  Runge–Kutta methods are relations by nature. A `ODE.OneStep.Method` maps the field $f$ to a step
  relation.
* The explicit map `ODE.OneStep.step` and its iterates `ODE.OneStep.iterate` on the states $(t, u)$
  are the function form of an explicit method. `ODE.OneStep.isOrbit_iterate` and
  `ODE.OneStep.eq_iterate_of_isOrbit` connect them with the orbits of the step relation.
* Truncation errors, consistency and order are properties of a pair of a method and a curve. In
  every use the curve is the solution of the Cauchy problem, but the definitions do not require it.
* `ODE.OneStep.LipschitzIncrement` asks for the Lipschitz bound uniformly in the third argument of
  $\Phi$. With equal second arguments, the bound forces $\Phi(t, u, w; h)$ to be independent of $w$
  for $t \in I$ and $h \in (0, h_0]$. So Theorems 11.1 and 11.2 here apply to increments that are
  explicit on this range.
* `ODE.OneStep.IsConvergentFor` has a step-size threshold $h_0$ that Definition 11.5 does not have.
  The hypothesis (11.18) of Theorem 11.2 holds only for small steps, and this forces the threshold.
* The Taylor bounds take explicit derivative functions on a closed interval. This is weaker than
  $C^2$ or $C^3$ regularity, and it is what the mean value inequality needs.
* `ODE.OneStep.IsAbsStable` requires that every initial value has an orbit. This excludes the
  singular parameters of the implicit methods, where the only orbit is $0$.
  `ODE.OneStep.absStabilityRegion` is the set of $z$ such that every factorization $z = h\lambda$
  with $h > 0$ is absolutely stable. This is a precise form of "the set of $h\lambda$ for which
  (11.25) holds" for a method that might not depend on $h\lambda$ alone. For the methods of this
  module, the region is the slice $h = 1$ (`ODE.OneStep.absStabilityRegion_eq_of_scaleInvariant`).
-/

open Set Filter Topology Asymptotics
open Finset (range)

namespace ODE

/-! ### The grid -/

section Grid

variable {T h : ℝ} {n : ℕ}

/-- The number of steps $N_h = \lfloor T/h \rfloor$ of size $h$ on the horizon $T$ (§11.2 of
[quarteroni2000numerical]). For $T \ge 0$ and $h > 0$ it is the largest $n$ with $nh \le T$, so
that the nodes $t_0 + nh$ with $n \le N_h$ lie in $[t_0, t_0 + T]$.

The floor is `Nat.floor`, so $N_h = 0$ when $T/h < 0$. -/
noncomputable def gridCount (T h : ℝ) : ℕ := ⌊T / h⌋₊

/-- Let $T \ge 0$ and $h > 0$. For every natural number $n$, $n \le N_h$ if and only if $nh \le T$.
-/
theorem le_gridCount_iff (hT : 0 ≤ T) (hh : 0 < h) : n ≤ gridCount T h ↔ (n : ℝ) * h ≤ T := by
  rw [gridCount, Nat.le_floor_iff (div_nonneg hT hh.le), le_div_iff₀ hh]

/-- Let $T \ge 0$ and $h > 0$. Then $N_h h \le T$: the last node lies in the horizon. -/
theorem gridCount_mul_le (hT : 0 ≤ T) (hh : 0 < h) : (gridCount T h : ℝ) * h ≤ T :=
  (le_gridCount_iff hT hh).1 le_rfl

/-- Let $T < 0$ and $h > 0$. Then $N_h = 0$: a negative horizon has no steps. -/
theorem gridCount_eq_zero_of_neg (hT : T < 0) (hh : 0 < h) : gridCount T h = 0 :=
  Nat.floor_of_nonpos (div_nonpos_of_nonpos_of_nonneg hT.le hh.le)

/-- Let $h > 0$. If $n < N_h$ for some natural number $n$, then $T \ge 0$. -/
theorem nonneg_of_lt_gridCount (hh : 0 < h) (hn : n < gridCount T h) : 0 ≤ T := by
  by_contra hT
  rw [gridCount_eq_zero_of_neg (not_le.1 hT) hh] at hn
  exact absurd hn (Nat.not_lt_zero _)

/-- Let $T \ge 0$ and $h > 0$. If $n \le N_h$, then $nh \le T$. -/
theorem mul_le_of_le_gridCount (hT : 0 ≤ T) (hh : 0 < h) (hn : n ≤ gridCount T h) :
    (n : ℝ) * h ≤ T :=
  (le_gridCount_iff hT hh).1 hn

/-- The grid node $t_n = t_0 + nh$. -/
def node (t₀ h : ℝ) (n : ℕ) : ℝ := t₀ + n * h

/-- The first grid node is $t_0$. -/
@[simp] theorem node_zero (t₀ h : ℝ) : node t₀ h 0 = t₀ := by simp [node]

/-- Consecutive grid nodes differ by the step: $t_{n+1} = t_n + h$. -/
theorem node_succ (t₀ h : ℝ) (n : ℕ) : node t₀ h (n + 1) = node t₀ h n + h := by
  simp only [node, Nat.cast_succ]; ring

/-- Let $T \ge 0$ and $h > 0$. If $n \le N_h$, then $t_n \in [t_0, t_0 + T]$. -/
theorem node_mem_Icc {t₀ : ℝ} (hT : 0 ≤ T) (hh : 0 < h) (hn : n ≤ gridCount T h) :
    node t₀ h n ∈ Icc t₀ (t₀ + T) := by
  have h1 := (le_gridCount_iff hT hh).1 hn
  have h2 : (0 : ℝ) ≤ n * h := by positivity
  simp only [node, mem_Icc]
  constructor <;> linarith

/-- Let $h > 0$. If $n < N_h$, then $t_n \in [t_0, t_0 + T]$.

No sign condition on $T$ is needed, because $n < N_h$ forces $T \ge 0$. -/
theorem node_mem_Icc_of_lt {t₀ : ℝ} (hh : 0 < h) (hn : n < gridCount T h) :
    node t₀ h n ∈ Icc t₀ (t₀ + T) :=
  node_mem_Icc (nonneg_of_lt_gridCount hh hn) hh hn.le

/-- Let $h > 0$. If $n < N_h$, then $t_n + h \in [t_0, t_0 + T]$: the right end $t_{n+1}$ of a step
that starts before the last node lies in the horizon. -/
theorem node_add_mem_Icc_of_lt {t₀ : ℝ} (hh : 0 < h) (hn : n < gridCount T h) :
    node t₀ h n + h ∈ Icc t₀ (t₀ + T) := by
  rw [← node_succ]
  exact node_mem_Icc (nonneg_of_lt_gridCount hh hn) hh hn

end Grid

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace OneStep

/-! ### Methods, step relations and orbits -/

/-- An **increment function** $\Phi(t, u, v; h)$, a map from
$\mathbb{R} \times E \times E \times \mathbb{R}$ to $E$. It defines the one-step method
$$u_{n+1} = u_n + h\,\Phi(t_n, u_n, u_{n+1}; h)$$
of (11.11) of [quarteroni2000numerical]. The third argument $v$ is the new value $u_{n+1}$, so
that implicit methods are increment functions too.

The Lean argument order is `Φ t u v h`. -/
abbrev Increment (E : Type*) := ℝ → E → E → ℝ → E

/-- A one-step method as a **step relation**: $S(h, t, u, v)$ says that $v$ is an admissible value
at time $t + h$ from the value $u$ at time $t$. That $u_{n+1}$ depends only on $u_n$ is
Definition 11.2 of [quarteroni2000numerical].

The Lean argument order is `S h t u v`. Increment functions give step relations by
`ODE.OneStep.ofIncrement`. Implicit Runge–Kutta methods give step relations directly. -/
abbrev StepRel (E : Type*) := ℝ → ℝ → E → E → Prop

/-- A **numerical method**: a rule that assigns a step relation to each vector field
$f : \mathbb{R} \times E \to E$. -/
abbrev Method (E : Type*) := (ℝ → E → E) → StepRel E

variable {Φ : Increment E} {S : StepRel E} {h t₀ T h₀ Λ : ℝ} {n : ℕ}

/-- An increment function $\Phi$ is **explicit** if $\Phi(t, u, v; h)$ does not depend on $v$, so
that $u_{n+1}$ is computed directly from $u_n$ (Definition 11.3 of [quarteroni2000numerical]). A
method is implicit if it is not explicit. -/
def IsExplicit (Φ : Increment E) : Prop := ∀ t u v w h, Φ t u v h = Φ t u w h

/-- The step relation of an increment function $\Phi$: $v$ is admissible from $u$ at time $t$ with
step $h$ if $v = u + h\,\Phi(t, u, v; h)$. -/
def ofIncrement (Φ : Increment E) : StepRel E := fun h t u v => v = u + h • Φ t u v h

/-- The step relation of an increment function $\Phi$ holds if and only if
$v = u + h\,\Phi(t, u, v; h)$. -/
theorem ofIncrement_apply {t : ℝ} {u v : E} :
    ofIncrement Φ h t u v ↔ v = u + h • Φ t u v h := Iff.rfl

/-- One explicit step on the state $(t, u)$: the new state is $(t + h, u + h\,\Phi(t, u, u; h))$.

For an explicit $\Phi$ the third argument does not matter. For an implicit $\Phi$ this map
evaluates $\Phi$ at the old value, which is a predictor, not the method. -/
def step (Φ : Increment E) (h : ℝ) (s : ℝ × E) : ℝ × E := (s.1 + h, s.2 + h • Φ s.1 s.2 s.2 h)

/-- The $n$-th state $(t_n, u_n)$ of the explicit iteration of `ODE.OneStep.step` from $(t_0, y_0)$.
-/
def iterate (Φ : Increment E) (h t₀ : ℝ) (y₀ : E) (n : ℕ) : ℝ × E := (step Φ h)^[n] (t₀, y₀)

/-- The explicit iteration starts at $(t_0, y_0)$. -/
@[simp] theorem iterate_zero (y₀ : E) : iterate Φ h t₀ y₀ 0 = (t₀, y₀) := rfl

/-- The state $n + 1$ of the explicit iteration is one step from the state $n$. -/
theorem iterate_succ (y₀ : E) (n : ℕ) :
    iterate Φ h t₀ y₀ (n + 1) = step Φ h (iterate Φ h t₀ y₀ n) :=
  Function.iterate_succ_apply' _ _ _

/-- The time component of the $n$-th state of the explicit iteration is the grid node
$t_n = t_0 + nh$. -/
theorem iterate_fst (y₀ : E) (n : ℕ) : (iterate Φ h t₀ y₀ n).1 = node t₀ h n := by
  induction n with
  | zero => simp
  | succ n ih => rw [iterate_succ, node_succ, ← ih]; rfl

/-- A **perturbed orbit** of a step relation $S$ with step $h$ from time $t_0$, with perturbations
$(\delta_n)$ ((11.16) of [quarteroni2000numerical]): a sequence $(z_n)$ such that, for every
$n$, the value $z_{n+1} - h\delta_{n+1}$ is admissible from $z_n$ at time $t_n$. That is,
$z_{n+1}$ is a step from $z_n$ plus $h\delta_{n+1}$.

Only the terms $\delta_{n+1}$ enter the definition. The term $\delta_0$ is the perturbation of
the initial datum, $z_0 = y_0 + \delta_0$, and each use states this condition separately. -/
def IsOrbitWith (S : StepRel E) (h t₀ : ℝ) (δ : ℕ → E) (z : ℕ → E) : Prop :=
  ∀ n, S h (node t₀ h n) (z n) (z (n + 1) - h • δ (n + 1))

/-- An **orbit** of a step relation $S$ with step $h$ from time $t_0$: a sequence $(u_n)$ such that
$u_{n+1}$ is admissible from $u_n$ at time $t_n$ for every $n$. This is the unperturbed
recursion (11.11), (11.17) of [quarteroni2000numerical], and it is `ODE.OneStep.IsOrbitWith`
with $\delta = 0$. -/
def IsOrbit (S : StepRel E) (h t₀ : ℝ) (u : ℕ → E) : Prop := IsOrbitWith S h t₀ 0 u

/-- A sequence $(u_n)$ is an orbit of $S$ if and only if $S(h, t_n, u_n, u_{n+1})$ holds for every
$n$. -/
theorem isOrbit_iff {u : ℕ → E} : IsOrbit S h t₀ u ↔ ∀ n, S h (node t₀ h n) (u n) (u (n + 1)) := by
  simp [IsOrbit, IsOrbitWith]

/-- A sequence $(u_n)$ is an orbit of the step relation of an increment function $\Phi$ if and only
if
$$u_{n+1} = u_n + h\,\Phi(t_n, u_n, u_{n+1}; h) \quad \text{for every } n,$$
the recursion (11.11) of [quarteroni2000numerical]. -/
theorem isOrbit_ofIncrement_iff {u : ℕ → E} :
    IsOrbit (ofIncrement Φ) h t₀ u ↔
      ∀ n, u (n + 1) = u n + h • Φ (node t₀ h n) (u n) (u (n + 1)) h :=
  isOrbit_iff

/-- A sequence $(z_n)$ is a perturbed orbit of the step relation of an increment function $\Phi$,
with perturbations $(\delta_n)$, if and only if for every $n$
$$z_{n+1} = z_n + h\,\Phi(t_n, z_n, z_{n+1} - h\delta_{n+1}; h) + h\delta_{n+1},$$
the recursion (11.16) of [quarteroni2000numerical]. -/
theorem isOrbitWith_ofIncrement_iff {δ z : ℕ → E} :
    IsOrbitWith (ofIncrement Φ) h t₀ δ z ↔
      ∀ n, z (n + 1) = z n + h • Φ (node t₀ h n) (z n) (z (n + 1) - h • δ (n + 1)) h +
        h • δ (n + 1) := by
  simp only [IsOrbitWith, ofIncrement, sub_eq_iff_eq_add]

/-- If $\Phi$ is explicit, then the values $u_n$ of the explicit iteration from $(t_0, y_0)$ form an
orbit of the step relation of $\Phi$. -/
theorem isOrbit_iterate (hex : IsExplicit Φ) (y₀ : E) :
    IsOrbit (ofIncrement Φ) h t₀ fun n => (iterate Φ h t₀ y₀ n).2 := by
  rw [isOrbit_ofIncrement_iff]
  intro n
  rw [iterate_succ, step, ← iterate_fst (Φ := Φ) (h := h) y₀ n]
  exact congrArg _ (congrArg _ (hex _ _ _ _ _))

/-- If $\Phi$ is explicit, then every orbit $(u_n)$ of the step relation of $\Phi$ is the explicit
iteration from its initial value: $u_n$ is the second component of the $n$-th state of the
iteration from $(t_0, u_0)$. -/
theorem eq_iterate_of_isOrbit (hex : IsExplicit Φ) {u : ℕ → E}
    (hu : IsOrbit (ofIncrement Φ) h t₀ u) (n : ℕ) : u n = (iterate Φ h t₀ (u 0) n).2 := by
  rw [isOrbit_ofIncrement_iff] at hu
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [hu n, ih, iterate_succ, step, iterate_fst]
    exact congrArg _ (congrArg _ (hex _ _ _ _ _))

/-! ### Local and global truncation error, consistency, order -/

/-- The **local truncation error** of the increment function $\Phi$ along a curve
$y : \mathbb{R} \to E$ at time $t$ with step $h$:
$$\tau(t; h) = \frac{y(t + h) - y(t)}{h} - \Phi(t, y(t), y(t + h); h).$$
At $t = t_n$ this is $\tau_{n+1}(h)$ of (11.12) of [quarteroni2000numerical].

The quotient is `h⁻¹ • (y (t + h) - y t)`, so at $h = 0$ the first term is $0$. The curve is the
solution of the Cauchy problem in every use, but the definition does not require it. -/
noncomputable def lte (Φ : Increment E) (h : ℝ) (y : ℝ → E) (t : ℝ) : E :=
  h⁻¹ • (y (t + h) - y t) - Φ t (y t) (y (t + h)) h

/-- Let $h \neq 0$. Every curve $y$ satisfies the scheme up to $h$ times its local truncation error:
$$y(t + h) = y(t) + h\,\Phi(t, y(t), y(t + h); h) + h\,\tau(t; h).$$
-/
theorem lte_spec (hh : h ≠ 0) (y : ℝ → E) (t : ℝ) :
    y (t + h) = y t + h • Φ t (y t) (y (t + h)) h + h • lte Φ h y t := by
  simp only [lte, smul_sub, smul_smul, mul_inv_cancel₀ hh, one_smul]
  abel

/-- The **global truncation error** of $\Phi$ along the curve $y$ on the horizon $[t_0, t_0 + T]$:
$$\tau(h) = \max_{0 \le n \le N_h - 1} \|\tau_{n+1}(h)\|, \qquad \tau_{n+1}(h) = \tau(t_n; h).$$
It is $0$ when $N_h = 0$.

The maximum is the supremum over `Fin (ODE.gridCount T h)`, which is $0$ for the empty index
set. -/
noncomputable def globalLte (Φ : Increment E) (t₀ T : ℝ) (y : ℝ → E) (h : ℝ) : ℝ :=
  ⨆ n : Fin (gridCount T h), ‖lte Φ h y (node t₀ h n)‖

/-- If $n < N_h$, then the local truncation error at the node $t_n$ satisfies
$\|\tau(t_n; h)\| \le \tau(h)$. -/
theorem norm_lte_le_globalLte {y : ℝ → E} (hn : n < gridCount T h) :
    ‖lte Φ h y (node t₀ h n)‖ ≤ globalLte Φ t₀ T y h :=
  le_ciSup (f := fun n : Fin (gridCount T h) => ‖lte Φ h y (node t₀ h n)‖)
    (Finite.bddAbove_range _) ⟨n, hn⟩

/-- The global truncation error is nonnegative: $\tau(h) \ge 0$. -/
theorem globalLte_nonneg (y : ℝ → E) : 0 ≤ globalLte Φ t₀ T y h :=
  Real.iSup_nonneg fun _ => norm_nonneg _

/-- Let $C \ge 0$. If $\|\tau(t_n; h)\| \le C$ for every $n < N_h$, then $\tau(h) \le C$. -/
theorem globalLte_le {y : ℝ → E} {C : ℝ} (hC : 0 ≤ C)
    (hle : ∀ n < gridCount T h, ‖lte Φ h y (node t₀ h n)‖ ≤ C) : globalLte Φ t₀ T y h ≤ C :=
  Real.iSup_le (fun i => hle i i.2) hC

/-- The increment function $\Phi$ is **consistent** along the curve $y$ on $[t_0, t_0 + T]$ if the
global truncation error tends to zero with the step: $\tau(h) \to 0$ as $h \to 0^+$ (§11.3 of
[quarteroni2000numerical]). -/
def IsConsistentFor (Φ : Increment E) (t₀ T : ℝ) (y : ℝ → E) : Prop :=
  Tendsto (globalLte Φ t₀ T y) (𝓝[>] 0) (𝓝 0)

/-- The increment function $\Phi$ has **order** $p$ along the curve $y$ on $[t_0, t_0 + T]$ if
$\tau(h) = O(h^p)$ as $h \to 0^+$ ((11.14) of [quarteroni2000numerical]). -/
def HasOrderFor (Φ : Increment E) (t₀ T : ℝ) (y : ℝ → E) (p : ℕ) : Prop :=
  globalLte Φ t₀ T y =O[𝓝[>] 0] fun h => h ^ p

/-- Let $p \ge 1$. If $\Phi$ has order $p$ along $y$, then $\Phi$ is consistent along $y$. -/
theorem HasOrderFor.isConsistentFor {y : ℝ → E} {p : ℕ} (hp : 1 ≤ p)
    (hΦ : HasOrderFor Φ t₀ T y p) : IsConsistentFor Φ t₀ T y :=
  hΦ.trans_tendsto <| ((continuous_pow p).tendsto' 0 0
    (by simp [zero_pow (Nat.one_le_iff_ne_zero.1 hp)])).mono_left nhdsWithin_le_nhds

/-- Let $p$ be a natural number and $C$ a real number. If
$$\|\tau(t_n; h)\| \le C h^p \quad \text{for every } h > 0 \text{ and every } n < N_h,$$
then $\Phi$ has order $p$ along $y$. -/
theorem hasOrderFor_of_forall_norm_lte_le {y : ℝ → E} {p : ℕ} {C : ℝ}
    (hle : ∀ h > 0, ∀ n < gridCount T h, ‖lte Φ h y (node t₀ h n)‖ ≤ C * h ^ p) :
    HasOrderFor Φ t₀ T y p := by
  refine IsBigO.of_bound (max C 0) (eventually_nhdsWithin_of_forall fun h (hh : 0 < h) => ?_)
  rw [Real.norm_of_nonneg (globalLte_nonneg _), Real.norm_of_nonneg (by positivity)]
  refine globalLte_le (by positivity) fun n hn => (hle h hh n hn).trans ?_
  exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)

/-! ### The consistency criterion (11.13) -/

section Criterion

variable {f : ℝ → E → E} {y : ℝ → E}

/-- Let $I = [t_0, t_0 + T]$, let $y$ have the derivative $f(s, y(s))$ within $I$ at every
$s \in I$, and let $s \mapsto f(s, y(s))$ be continuous on $I$. Then the difference quotients of
$y$ converge to the derivative uniformly on $I$: for every $\varepsilon > 0$ there is $\eta > 0$
such that
$$\Bigl\| \frac{y(t + h) - y(t)}{h} - f(t, y(t)) \Bigr\| \le \varepsilon$$
for every $h \in (0, \eta]$ and every $t$ with $t, t + h \in I$.

This is the uniform first-order Taylor bound `exists_forall_norm_sub_sub_smul_le`, divided by
$h$. -/
theorem exists_forall_norm_sub_smul_le_of_continuousOn
    (hy : ∀ s ∈ Icc t₀ (t₀ + T), HasDerivWithinAt y (f s (y s)) (Icc t₀ (t₀ + T)) s)
    (hf : ContinuousOn (fun s => f s (y s)) (Icc t₀ (t₀ + T))) {ε : ℝ} (hε : 0 < ε) :
    ∃ η > 0, ∀ h ∈ Ioc 0 η, ∀ t ∈ Icc t₀ (t₀ + T), t + h ∈ Icc t₀ (t₀ + T) →
      ‖h⁻¹ • (y (t + h) - y t) - f t (y t)‖ ≤ ε := by
  obtain ⟨η, hη, hη'⟩ := exists_forall_norm_sub_sub_smul_le (y' := fun s => f s (y s)) hy hf hε
  refine ⟨η, hη, fun h hh t ht hth => ?_⟩
  have key := hη' t ht h hth (by rw [abs_of_pos hh.1]; exact hh.2)
  rw [abs_of_pos hh.1] at key
  have e : h⁻¹ • (y (t + h) - y t) - f t (y t) = h⁻¹ • (y (t + h) - y t - h • f t (y t)) := by
    rw [smul_sub h⁻¹ (y (t + h) - y t) (h • f t (y t)), smul_smul, inv_mul_cancel₀ hh.1.ne',
      one_smul]
  rw [e, norm_smul, norm_inv, Real.norm_of_nonneg hh.1.le]
  calc h⁻¹ * ‖y (t + h) - y t - h • f t (y t)‖ ≤ h⁻¹ * (ε * h) :=
        mul_le_mul_of_nonneg_left key (inv_nonneg.2 hh.1.le)
    _ = ε := by rw [mul_comm ε, ← mul_assoc, inv_mul_cancel₀ hh.1.ne', one_mul]

/-- The **consistency criterion** ((11.13) of [quarteroni2000numerical]). Let $I = [t_0, t_0 + T]$,
let $y$ have the derivative $f(s, y(s))$ within $I$ at every $s \in I$, and let
$s \mapsto f(s, y(s))$ be continuous on $I$. Suppose that the increment converges to the field
along $y$, uniformly in time: for every $\varepsilon > 0$ there is $\eta > 0$ such that
$$\|\Phi(t, y(t), y(t + h); h) - f(t, y(t))\| \le \varepsilon$$
for every $h \in (0, \eta]$ and every $t$ with $t, t + h \in I$. Then $\Phi$ is consistent along
$y$.

The source asks for this convergence "for all $t_n$". It must be read uniformly in $t$, because
$\tau(h)$ is a maximum over the grid. -/
theorem isConsistentFor_of_tendsto_increment
    (hy : ∀ s ∈ Icc t₀ (t₀ + T), HasDerivWithinAt y (f s (y s)) (Icc t₀ (t₀ + T)) s)
    (hf : ContinuousOn (fun s => f s (y s)) (Icc t₀ (t₀ + T)))
    (hΦ : ∀ ε > 0, ∃ η > 0, ∀ h ∈ Ioc 0 η, ∀ t ∈ Icc t₀ (t₀ + T), t + h ∈ Icc t₀ (t₀ + T) →
      ‖Φ t (y t) (y (t + h)) h - f t (y t)‖ ≤ ε) :
    IsConsistentFor Φ t₀ T y := by
  rw [IsConsistentFor, Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨η₁, hη₁, h₁⟩ := exists_forall_norm_sub_smul_le_of_continuousOn hy hf
    (half_pos (half_pos hε))
  obtain ⟨η₂, hη₂, h₂⟩ := hΦ (ε / 2 / 2) (half_pos (half_pos hε))
  refine ⟨min η₁ η₂, lt_min hη₁ hη₂, fun h (hh : 0 < h) hdist => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_pos hh] at hdist
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (globalLte_nonneg _)]
  refine lt_of_le_of_lt (globalLte_le (by positivity) fun n hn => ?_) (by linarith : ε / 2 < ε)
  have ht := node_mem_Icc_of_lt (t₀ := t₀) hh hn
  have hth := node_add_mem_Icc_of_lt (t₀ := t₀) hh hn
  have e : lte Φ h y (node t₀ h n) =
      (h⁻¹ • (y (node t₀ h n + h) - y (node t₀ h n)) - f (node t₀ h n) (y (node t₀ h n))) -
        (Φ (node t₀ h n) (y (node t₀ h n)) (y (node t₀ h n + h)) h -
          f (node t₀ h n) (y (node t₀ h n))) := by
    simp only [lte]; abel
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  have k1 := h₁ h ⟨hh, hdist.le.trans (min_le_left _ _)⟩ _ ht hth
  have k2 := h₂ h ⟨hh, hdist.le.trans (min_le_right _ _)⟩ _ ht hth
  linarith

end Criterion

/-! ### Zero-stability: Theorem 11.1 -/

/-- **Zero-stability** of the step relation $S$ for the datum $y_0$ on the horizon $T$ (Definition
11.4 of [quarteroni2000numerical]): there are $h_0 > 0$ and $C > 0$ with the following property.
Let $h \in (0, h_0]$, let $\varepsilon \ge 0$, and let $(\delta_n)$ satisfy
$\|\delta_k\| \le \varepsilon$ for every $k \le N_h$. Let $(u_n)$ be an orbit of $S$ with
$u_0 = y_0$, and let $(z_n)$ be a perturbed orbit of $S$ with perturbations $(\delta_n)$ and
$z_0 = y_0 + \delta_0$. Then $\|z_n - u_n\| \le C\varepsilon$ for every $n \le N_h$.

The constant $C$ may depend on $T$, but not on $h$, $\varepsilon$ or $\delta$. -/
def IsZeroStable (S : StepRel E) (t₀ T : ℝ) (y₀ : E) : Prop :=
  ∃ h₀ : ℝ, 0 < h₀ ∧ ∃ C : ℝ, 0 < C ∧ ∀ h ∈ Ioc 0 h₀, ∀ ε : ℝ, 0 ≤ ε → ∀ δ : ℕ → E,
    (∀ k ≤ gridCount T h, ‖δ k‖ ≤ ε) → ∀ u z : ℕ → E, IsOrbit S h t₀ u → u 0 = y₀ →
      IsOrbitWith S h t₀ δ z → z 0 = y₀ + δ 0 → ∀ n ≤ gridCount T h, ‖z n - u n‖ ≤ C * ε

/-- The Lipschitz hypothesis (11.18) of Theorem 11.1 of [quarteroni2000numerical]: $\Phi$ is
$\Lambda$-Lipschitz in its second argument, uniformly in the time, the step and the third
argument. That is,
$$\|\Phi(t, u, w; h) - \Phi(t, v, w'; h)\| \le \Lambda \|u - v\|$$
for every $h \in (0, h_0]$, every $t \in [t_0, t_0 + T]$ and all $u, v, w, w' \in E$.

The third arguments $w$ and $w'$ are independent. With $u = v$ the condition gives
$\Phi(t, u, w; h) = \Phi(t, u, w'; h)$, so it holds only for an increment that is explicit for
these $t$ and $h$. -/
def LipschitzIncrement (Φ : Increment E) (t₀ T h₀ Λ : ℝ) : Prop :=
  ∀ h ∈ Ioc 0 h₀, ∀ t ∈ Icc t₀ (t₀ + T), ∀ u v w w', ‖Φ t u w h - Φ t v w' h‖ ≤ Λ * ‖u - v‖

/-- Let $\Phi$ satisfy `ODE.OneStep.LipschitzIncrement` with a constant $\Lambda \ge 0$, let
$h \in (0, h_0]$ and $\varepsilon \ge 0$. Let the sequences $(u_n)$ and $(z_n)$ satisfy
$$u_{n+1} = u_n + h\,\Phi(t_n, u_n, v_n; h), \qquad z_{n+1} = z_n + h\,\Phi(t_n, z_n, v'_n; h) +
  h\delta_{n+1}$$
for every $n$, with arbitrary sequences $(v_n)$ and $(v'_n)$ in the third argument, and let
$\|\delta_k\| \le \varepsilon$ for $1 \le k \le N_h$. Then for every $n \le N_h$,
$$\|z_n - u_n\| \le (\|z_0 - u_0\| + nh\varepsilon)\, e^{nh\Lambda}.$$
This is the estimate behind Theorems 11.1 and 11.2 of [quarteroni2000numerical].

The difference $w_n = z_n - u_n$ satisfies $\|w_{n+1}\| \le (1 + h\Lambda)\|w_n\| +
h\varepsilon$ for $n < N_h$. Hence $\|w_n\| \le \|w_0\| + nh\varepsilon + h\Lambda \sum_{j<n}
\|w_j\|$, which is the inequality (11.19), and the discrete Gronwall lemma
`Gronwall.discrete_sum_const_of_le` concludes. -/
theorem norm_sub_le_of_lipschitzIncrement_of_succ_eq (hlip : LipschitzIncrement Φ t₀ T h₀ Λ)
    (hΛ : 0 ≤ Λ) (hh : h ∈ Ioc 0 h₀) {ε : ℝ} (hε : 0 ≤ ε) {u z v v' δ : ℕ → E}
    (hu : ∀ m, u (m + 1) = u m + h • Φ (node t₀ h m) (u m) (v m) h)
    (hz : ∀ m, z (m + 1) = z m + h • Φ (node t₀ h m) (z m) (v' m) h + h • δ (m + 1))
    (hδ : ∀ k, 1 ≤ k → k ≤ gridCount T h → ‖δ k‖ ≤ ε) (hn : n ≤ gridCount T h) :
    ‖z n - u n‖ ≤ (‖z 0 - u 0‖ + n * h * ε) * Real.exp (n * h * Λ) := by
  have hstep : ∀ m < gridCount T h,
      ‖z (m + 1) - u (m + 1)‖ ≤ ‖z m - u m‖ + h * Λ * ‖z m - u m‖ + h * ε := by
    intro m hm
    have hnode : node t₀ h m ∈ Icc t₀ (t₀ + T) := node_mem_Icc_of_lt hh.1 hm
    have hw : z (m + 1) - u (m + 1) = (z m - u m) +
        h • (Φ (node t₀ h m) (z m) (v' m) h - Φ (node t₀ h m) (u m) (v m) h) + h • δ (m + 1) := by
      rw [hz m, hu m, smul_sub]; abel
    have hh0 : 0 ≤ h := hh.1.le
    rw [hw]
    refine norm_add₃_le.trans ?_
    rw [norm_smul, norm_smul, Real.norm_of_nonneg hh0, mul_assoc h Λ]
    gcongr
    · exact hlip h hh _ hnode _ _ _ _
    · exact hδ (m + 1) (by omega) hm
  have hsum : ∀ m ≤ gridCount T h,
      ‖z m - u m‖ ≤ ‖z 0 - u 0‖ + m * h * ε + h * Λ * ∑ j ∈ range m, ‖z j - u j‖ := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      have ih := ih (Nat.le_of_succ_le hm)
      rw [Finset.sum_range_succ, mul_add, Nat.cast_succ]
      have := hstep m hm
      nlinarith
  exact Gronwall.discrete_sum_const_of_le (norm_nonneg _) hh.1.le hε hΛ hsum hn

/-- The **zero-stability estimate**. Let $\Phi$ satisfy `ODE.OneStep.LipschitzIncrement` with a
constant $\Lambda \ge 0$, let $h \in (0, h_0]$, and let $\|\delta_k\| \le \varepsilon$ for every
$k \le N_h$. Let $(u_n)$ be an orbit of the step relation of $\Phi$ with $u_0 = y_0$, and let
$(z_n)$ be a perturbed orbit with perturbations $(\delta_n)$ and $z_0 = y_0 + \delta_0$. Then
for every $n \le N_h$,
$$\|z_n - u_n\| \le (1 + nh)\,\varepsilon\, e^{nh\Lambda}.$$
This is the quantitative form of Theorem 11.1 of [quarteroni2000numerical]. -/
theorem norm_sub_le_of_lipschitzIncrement (hlip : LipschitzIncrement Φ t₀ T h₀ Λ) (hΛ : 0 ≤ Λ)
    (hh : h ∈ Ioc 0 h₀) {ε : ℝ} {δ : ℕ → E} (hδ : ∀ k ≤ gridCount T h, ‖δ k‖ ≤ ε) {u z : ℕ → E}
    {y₀ : E} (hu : IsOrbit (ofIncrement Φ) h t₀ u) (hu0 : u 0 = y₀)
    (hz : IsOrbitWith (ofIncrement Φ) h t₀ δ z) (hz0 : z 0 = y₀ + δ 0) (hn : n ≤ gridCount T h) :
    ‖z n - u n‖ ≤ (1 + n * h) * ε * Real.exp (n * h * Λ) := by
  have hε : 0 ≤ ε := (norm_nonneg _).trans (hδ 0 (Nat.zero_le _))
  have h0 : ‖z 0 - u 0‖ ≤ ε := by rw [hz0, hu0, add_sub_cancel_left]; exact hδ 0 (Nat.zero_le _)
  rw [isOrbit_ofIncrement_iff] at hu
  rw [isOrbitWith_ofIncrement_iff] at hz
  have key := norm_sub_le_of_lipschitzIncrement_of_succ_eq hlip hΛ hh hε hu hz
    (fun k _ hk => hδ k hk) hn
  refine key.trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
  nlinarith

/-- The **zero-stability theorem**. Let $T \ge 0$ and $h_0 > 0$, and let $\Phi$ satisfy
`ODE.OneStep.LipschitzIncrement` on $[t_0, t_0 + T]$ and $(0, h_0]$ with a constant
$\Lambda \ge 0$. Then the step relation of $\Phi$ is zero-stable for every datum $y_0$. This is
Theorem 11.1 of [quarteroni2000numerical].

The constant of `ODE.OneStep.IsZeroStable` is $C = (1 + T)\,e^{\Lambda T}$. -/
theorem isZeroStable_of_lipschitzIncrement (hT : 0 ≤ T) (hh₀ : 0 < h₀)
    (hlip : LipschitzIncrement Φ t₀ T h₀ Λ) (hΛ : 0 ≤ Λ) (y₀ : E) :
    IsZeroStable (ofIncrement Φ) t₀ T y₀ := by
  refine ⟨h₀, hh₀, (1 + T) * Real.exp (Λ * T), by positivity,
    fun h hh ε hε δ hδ u z hu hu0 hz hz0 n hn => ?_⟩
  refine (norm_sub_le_of_lipschitzIncrement hlip hΛ hh hδ hu hu0 hz hz0 hn).trans ?_
  have hnh : (n : ℝ) * h ≤ T := mul_le_of_le_gridCount hT hh.1 hn
  have h1 : (1 + n * h) * ε ≤ (1 + T) * ε := by gcongr
  have h2 : Real.exp (n * h * Λ) ≤ Real.exp (Λ * T) := by
    rw [Real.exp_le_exp, mul_comm Λ T]; exact mul_le_mul_of_nonneg_right hnh hΛ
  calc (1 + n * h) * ε * Real.exp (n * h * Λ) ≤ (1 + T) * ε * Real.exp (Λ * T) := by
        gcongr
    _ = (1 + T) * Real.exp (Λ * T) * ε := by ring

/-! ### Convergence: Theorem 11.2 -/

/-- **Convergence** of the step relation $S$ to the curve $y$ from the datum $y_0$ on
$[t_0, t_0 + T]$ (Definition 11.5 of [quarteroni2000numerical]): there are a function $C$ with
$C(h) \to 0$ as $h \to 0^+$ and a threshold $h_0 > 0$ such that for every $h \in (0, h_0]$,
every orbit $(u_n)$ of $S$ with step $h$ and $u_0 = y_0$ satisfies $\|u_n - y(t_n)\| \le C(h)$
for every $n \le N_h$.

The threshold $h_0$ is not part of the definition in the source. It is needed because the
hypothesis (11.18) of Theorem 11.2 holds only for small steps. -/
def IsConvergentFor (S : StepRel E) (t₀ T : ℝ) (y₀ : E) (y : ℝ → E) : Prop :=
  ∃ C : ℝ → ℝ, Tendsto C (𝓝[>] 0) (𝓝 0) ∧ ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ h ∈ Ioc 0 h₀, ∀ u : ℕ → E,
    IsOrbit S h t₀ u → u 0 = y₀ → ∀ n ≤ gridCount T h, ‖u n - y (node t₀ h n)‖ ≤ C h

/-- **Convergence with order $p$** of the step relation $S$ to the curve $y$ from the datum $y_0$ on
$[t_0, t_0 + T]$ (Definition 11.5 of [quarteroni2000numerical], second part): there are $C > 0$
and $h_0 > 0$ such that for every $h \in (0, h_0]$, every orbit $(u_n)$ of $S$ with step $h$ and
$u_0 = y_0$ satisfies $\|u_n - y(t_n)\| \le C h^p$ for every $n \le N_h$. -/
def IsConvergentWithOrderFor (S : StepRel E) (t₀ T : ℝ) (y₀ : E) (y : ℝ → E) (p : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ h ∈ Ioc 0 h₀, ∀ u : ℕ → E,
    IsOrbit S h t₀ u → u 0 = y₀ → ∀ n ≤ gridCount T h, ‖u n - y (node t₀ h n)‖ ≤ C * h ^ p

/-- Let $p \ge 1$. Convergence with order $p$ implies convergence. -/
theorem IsConvergentWithOrderFor.isConvergentFor {y₀ : E} {y : ℝ → E} {p : ℕ} (hp : 1 ≤ p)
    (hS : IsConvergentWithOrderFor S t₀ T y₀ y p) : IsConvergentFor S t₀ T y₀ y := by
  obtain ⟨C, -, h₀, hh₀, hC⟩ := hS
  refine ⟨fun h => C * h ^ p, ?_, h₀, hh₀, hC⟩
  have : Tendsto (fun h : ℝ => C * h ^ p) (𝓝 0) (𝓝 (C * 0 ^ p)) :=
    (continuous_const.mul (continuous_pow p)).tendsto 0
  rw [zero_pow (by omega), mul_zero] at this
  exact this.mono_left nhdsWithin_le_nhds

/-- The **convergence estimate** (11.20) of Theorem 11.2 of [quarteroni2000numerical]. Let $\Phi$
satisfy `ODE.OneStep.LipschitzIncrement` with a constant $\Lambda \ge 0$, let $h \in (0, h_0]$,
let $(u_n)$ be an orbit of the step relation of $\Phi$, and let $y$ be any curve. Then for every
$n \le N_h$,
$$\|y(t_n) - u_n\| \le (\|y(t_0) - u_0\| + nh\,\tau(h))\, e^{nh\Lambda},$$
where $\tau(h)$ is the global truncation error along $y$.

The curve enters only through its truncation errors. By `ODE.OneStep.lte_spec`, the values
$y(t_n)$ form a perturbed recursion with the perturbations $\delta_{n+1} = \tau_{n+1}(h)$. -/
theorem norm_sub_le_globalLte (hlip : LipschitzIncrement Φ t₀ T h₀ Λ) (hΛ : 0 ≤ Λ)
    (hh : h ∈ Ioc 0 h₀) {u : ℕ → E} (hu : IsOrbit (ofIncrement Φ) h t₀ u) (y : ℝ → E)
    (hn : n ≤ gridCount T h) :
    ‖y (node t₀ h n) - u n‖ ≤
      (‖y t₀ - u 0‖ + n * h * globalLte Φ t₀ T y h) * Real.exp (n * h * Λ) := by
  rw [isOrbit_ofIncrement_iff] at hu
  have hz : ∀ m, (fun k => y (node t₀ h k)) (m + 1) = (fun k => y (node t₀ h k)) m +
      h • Φ (node t₀ h m) ((fun k => y (node t₀ h k)) m) ((fun k => y (node t₀ h (k + 1))) m) h +
        h • (fun k => lte Φ h y (node t₀ h (k - 1))) (m + 1) := by
    intro m
    simp only [Nat.add_sub_cancel]
    rw [node_succ]
    exact lte_spec hh.1.ne' y _
  have key := norm_sub_le_of_lipschitzIncrement_of_succ_eq (z := fun k => y (node t₀ h k))
    (v' := fun k => y (node t₀ h (k + 1))) (δ := fun k => lte Φ h y (node t₀ h (k - 1)))
    hlip hΛ hh (globalLte_nonneg (Φ := Φ) (t₀ := t₀) (T := T) (h := h) y) hu hz
    (fun k hk1 hk => ?_) hn
  · simpa using key
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    exact norm_lte_le_globalLte hk

/-- **Consistency and a Lipschitz increment give convergence.** Let $T \ge 0$ and $h_0 > 0$, let
$\Phi$ satisfy `ODE.OneStep.LipschitzIncrement` with a constant $\Lambda \ge 0$, and let $\Phi$
be consistent along the curve $y$. Then the step relation of $\Phi$ converges to $y$ from the
datum $y(t_0)$. This is Theorem 11.2 of [quarteroni2000numerical].

The function of `ODE.OneStep.IsConvergentFor` is $C(h) = T\,\tau(h)\,e^{\Lambda T}$. -/
theorem isConvergentFor_of_isConsistentFor (hT : 0 ≤ T) (hh₀ : 0 < h₀)
    (hlip : LipschitzIncrement Φ t₀ T h₀ Λ) (hΛ : 0 ≤ Λ) {y : ℝ → E}
    (hcons : IsConsistentFor Φ t₀ T y) : IsConvergentFor (ofIncrement Φ) t₀ T (y t₀) y := by
  refine ⟨fun h => T * globalLte Φ t₀ T y h * Real.exp (Λ * T), ?_, h₀, hh₀,
    fun h hh u hu hu0 n hn => ?_⟩
  · have := (hcons.const_mul T).mul_const (Real.exp (Λ * T))
    simpa using this
  · rw [norm_sub_rev]
    refine (norm_sub_le_globalLte hlip hΛ hh hu y hn).trans ?_
    rw [hu0, sub_self, norm_zero, zero_add]
    have hnh : (n : ℝ) * h ≤ T := mul_le_of_le_gridCount hT hh.1 hn
    have h2 : Real.exp (n * h * Λ) ≤ Real.exp (Λ * T) := by
      rw [Real.exp_le_exp, mul_comm Λ T]; exact mul_le_mul_of_nonneg_right hnh hΛ
    exact mul_le_mul (mul_le_mul_of_nonneg_right hnh (globalLte_nonneg _)) h2
      (Real.exp_pos _).le (mul_nonneg hT (globalLte_nonneg _))

/-- **Order of convergence.** Let $T \ge 0$ and $h_0 > 0$, and let $\Phi$ satisfy
`ODE.OneStep.LipschitzIncrement` with a constant $\Lambda \ge 0$. If $\Phi$ has order $p$ along
the curve $y$, then the step relation of $\Phi$ converges to $y$ with order $p$ from the datum
$y(t_0)$. This is the second part of Theorem 11.2 of [quarteroni2000numerical]. -/
theorem isConvergentWithOrderFor_of_hasOrderFor (hT : 0 ≤ T) (hh₀ : 0 < h₀)
    (hlip : LipschitzIncrement Φ t₀ T h₀ Λ) (hΛ : 0 ≤ Λ) {y : ℝ → E} {p : ℕ}
    (hord : HasOrderFor Φ t₀ T y p) :
    IsConvergentWithOrderFor (ofIncrement Φ) t₀ T (y t₀) y p := by
  obtain ⟨c, hc, hbig⟩ := hord.exists_pos
  obtain ⟨h₁, hh₁, hIoc⟩ := mem_nhdsGT_iff_exists_Ioc_subset.1 hbig.bound
  refine ⟨T * c * Real.exp (Λ * T) + 1, by positivity, min h₀ h₁, lt_min hh₀ hh₁,
    fun h hh u hu hu0 n hn => ?_⟩
  have hh0 : h ∈ Ioc 0 h₀ := ⟨hh.1, hh.2.trans (min_le_left _ _)⟩
  have hτ : globalLte Φ t₀ T y h ≤ c * h ^ p := by
    have h' : ‖globalLte Φ t₀ T y h‖ ≤ c * ‖h ^ p‖ := hIoc ⟨hh.1, hh.2.trans (min_le_right _ _)⟩
    rwa [Real.norm_of_nonneg (globalLte_nonneg _), Real.norm_of_nonneg (pow_nonneg hh.1.le p)]
      at h'
  rw [norm_sub_rev]
  refine (norm_sub_le_globalLte hlip hΛ hh0 hu y hn).trans ?_
  rw [hu0, sub_self, norm_zero, zero_add]
  have hnh : (n : ℝ) * h ≤ T := mul_le_of_le_gridCount hT hh.1 hn
  have h2 : Real.exp (n * h * Λ) ≤ Real.exp (Λ * T) := by
    rw [Real.exp_le_exp, mul_comm Λ T]; exact mul_le_mul_of_nonneg_right hnh hΛ
  have hp : 0 ≤ h ^ p := pow_nonneg hh.1.le p
  calc n * h * globalLte Φ t₀ T y h * Real.exp (n * h * Λ)
      ≤ T * (c * h ^ p) * Real.exp (Λ * T) := by
        gcongr
        exact globalLte_nonneg _
    _ = T * c * Real.exp (Λ * T) * h ^ p := by ring
    _ ≤ (T * c * Real.exp (Λ * T) + 1) * h ^ p := by nlinarith

/-! ### The elementary methods -/

section Methods

variable {f : ℝ → E → E} {y y'' y''' : ℝ → E} {M M₂ M₃ : ℝ} {t : ℝ} {L : NNReal}

/-- The **forward Euler method** ((11.7) of [quarteroni2000numerical]): the explicit increment
$\Phi(t, u, v; h) = f(t, u)$, that is, $u_{n+1} = u_n + h f(t_n, u_n)$. -/
def forwardEuler (f : ℝ → E → E) : Increment E := fun t u _ _ => f t u

/-- The **backward Euler method** ((11.8) of [quarteroni2000numerical]): the implicit increment
$\Phi(t, u, v; h) = f(t + h, v)$, that is, $u_{n+1} = u_n + h f(t_{n+1}, u_{n+1})$. -/
def backwardEuler (f : ℝ → E → E) : Increment E := fun t _ v h => f (t + h) v

/-- The **Crank–Nicolson method**, or trapezoidal method ((11.9) of [quarteroni2000numerical]): the
implicit increment
$$\Phi(t, u, v; h) = \tfrac12 \bigl(f(t, u) + f(t + h, v)\bigr).$$
-/
noncomputable def crankNicolson (f : ℝ → E → E) : Increment E :=
  fun t u v h => (2 : ℝ)⁻¹ • (f t u + f (t + h) v)

/-- **Heun's method** ((11.10) of [quarteroni2000numerical]): the explicit increment
$$\Phi(t, u, v; h) = \tfrac12 \bigl(f(t, u) + f(t + h, u + h f(t, u))\bigr).$$
It is the Crank–Nicolson method with the new value predicted by forward Euler. -/
noncomputable def heun (f : ℝ → E → E) : Increment E :=
  fun t u _ h => (2 : ℝ)⁻¹ • (f t u + f (t + h) (u + h • f t u))

/-- The **θ-method** with parameter $\theta \in \mathbb{R}$: the increment $\Phi(t, u, v; h) = (1 -
\theta) f(t, u) + \theta f(t + h, v)$. It contains forward Euler ($\theta = 0$), Crank–Nicolson
($\theta = 1/2$) and backward Euler ($\theta = 1$). It is the time discretization of the
parabolic problems of §13.2–13.3 of [quarteroni2000numerical]. It is explicit for $\theta = 0$;
for $\theta \neq 0$ it uses the new value. -/
noncomputable def theta (f : ℝ → E → E) (θ : ℝ) : Increment E :=
  fun t u v h => (1 - θ) • f t u + θ • f (t + h) v

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The forward Euler increment is explicit. -/
theorem isExplicit_forwardEuler (f : ℝ → E → E) : IsExplicit (forwardEuler f) :=
  fun _ _ _ _ _ => rfl

/-- Heun's increment is explicit. -/
theorem isExplicit_heun (f : ℝ → E → E) : IsExplicit (heun f) := fun _ _ _ _ _ => rfl

/-- The θ-method with $\theta = 0$ is the forward Euler method. -/
@[simp] theorem theta_zero (f : ℝ → E → E) : theta f 0 = forwardEuler f := by
  ext t u v h; simp [theta, forwardEuler]

/-- The θ-method with $\theta = 1$ is the backward Euler method. -/
@[simp] theorem theta_one (f : ℝ → E → E) : theta f 1 = backwardEuler f := by
  ext t u v h; simp [theta, backwardEuler]

/-- The θ-method with $\theta = 1/2$ is the Crank–Nicolson method. -/
theorem theta_half (f : ℝ → E → E) : theta f (1 / 2) = crankNicolson f := by
  ext t u v h; simp [theta, crankNicolson, smul_add]; norm_num

omit [NormedSpace ℝ E] in
/-- Let $L \ge 0$, and let $f(t, \cdot)$ be $L$-Lipschitz for every $t \in [t_0, t_0 + T]$. Then for
every $h_0$, the forward Euler increment satisfies `ODE.OneStep.LipschitzIncrement` on
$[t_0, t_0 + T]$ and $(0, h_0]$ with the constant $L$. -/
theorem lipschitzIncrement_forwardEuler (hf : ∀ t ∈ Icc t₀ (t₀ + T), LipschitzWith L (f t))
    (h₀ : ℝ) : LipschitzIncrement (forwardEuler f) t₀ T h₀ L :=
  fun _ _ t ht u v _ _ => (hf t ht).norm_sub_le u v

/-- Let $L \ge 0$ and $h_0 \ge 0$, and let $f(t, \cdot)$ be $L$-Lipschitz for every
$t \in [t_0, t_0 + T + h_0]$. Then Heun's increment satisfies `ODE.OneStep.LipschitzIncrement`
on $[t_0, t_0 + T]$ and $(0, h_0]$ with the constant $L(1 + h_0 L/2)$.

The interval of the hypothesis is longer by $h_0$, because Heun's method evaluates $f$ at time
$t + h$. -/
theorem lipschitzIncrement_heun (hf : ∀ t ∈ Icc t₀ (t₀ + T + h₀), LipschitzWith L (f t))
    (hh₀ : 0 ≤ h₀) : LipschitzIncrement (heun f) t₀ T h₀ (L * (1 + h₀ * L / 2)) := by
  intro h hh t ht u v _ _
  have ht' : t ∈ Icc t₀ (t₀ + T + h₀) := ⟨ht.1, by linarith [ht.2]⟩
  have hth : t + h ∈ Icc t₀ (t₀ + T + h₀) := ⟨by linarith [ht.1, hh.1], by linarith [ht.2, hh.2]⟩
  simp only [heun]
  rw [← smul_sub, norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2⁻¹)]
  have e : f t u + f (t + h) (u + h • f t u) - (f t v + f (t + h) (v + h • f t v)) =
      (f t u - f t v) + (f (t + h) (u + h • f t u) - f (t + h) (v + h • f t v)) := by abel
  rw [e]
  have h1 : ‖f t u - f t v‖ ≤ L * ‖u - v‖ := (hf t ht').norm_sub_le u v
  have h2 : ‖f (t + h) (u + h • f t u) - f (t + h) (v + h • f t v)‖ ≤
      L * ((1 + h * L) * ‖u - v‖) := by
    refine ((hf _ hth).norm_sub_le _ _).trans (mul_le_mul_of_nonneg_left ?_ L.coe_nonneg)
    have e2 : u + h • f t u - (v + h • f t v) = (u - v) + h • (f t u - f t v) := by
      rw [smul_sub]; abel
    rw [e2]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_of_nonneg hh.1.le]
    nlinarith [mul_le_mul_of_nonneg_left h1 hh.1.le]
  have hL : (0 : ℝ) ≤ L := L.coe_nonneg
  have hh' : h ≤ h₀ := hh.2
  have hn : 0 ≤ ‖u - v‖ := norm_nonneg _
  calc 2⁻¹ * ‖f t u - f t v + (f (t + h) (u + h • f t u) - f (t + h) (v + h • f t v))‖
      ≤ 2⁻¹ * (L * ‖u - v‖ + L * ((1 + h * L) * ‖u - v‖)) := by
        gcongr
        exact (norm_add_le _ _).trans (add_le_add h1 h2)
    _ ≤ L * (1 + h₀ * L / 2) * ‖u - v‖ := by
        nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hL hL) hn) (sub_nonneg.2 hh')]

/-- Let $h \neq 0$. The local truncation error is $h^{-1}$ times the residual of the scheme along
the curve:
$$\tau(t; h) = h^{-1} \bigl(y(t + h) - y(t) - h\,\Phi(t, y(t), y(t + h); h)\bigr).$$
-/
theorem lte_eq_inv_smul (hh : h ≠ 0) (y : ℝ → E) (t : ℝ) :
    lte Φ h y t = h⁻¹ • (y (t + h) - y t - h • Φ t (y t) (y (t + h)) h) := by
  simp only [lte, smul_sub, smul_smul, inv_mul_cancel₀ hh, one_smul]

/-- **Forward Euler has order one**, local form. Let $I = [t_0, t_0 + T]$. Let $y$ have the
derivative $f(s, y(s))$ within $I$ at every $s \in I$, let $y''(s)$ be the derivative of
$s \mapsto f(s, y(s))$ within $I$, and let $\|y''(s)\| \le M$ for $s \in I$. If $h > 0$ and
$t, t + h \in I$, then the local truncation error of forward Euler satisfies
$$\|\tau(t; h)\| \le \frac{h}{2} M.$$

The source writes $\tau_{n+1}(h) = \frac{h}{2} y''(\xi)$. In a normed space there is no such
point $\xi$ in general, and the bound is the form of this identity that holds there. -/
theorem norm_lte_forwardEuler_le
    (hy : ∀ s ∈ Icc t₀ (t₀ + T), HasDerivWithinAt y (f s (y s)) (Icc t₀ (t₀ + T)) s)
    (hy' : ∀ s ∈ Icc t₀ (t₀ + T), HasDerivWithinAt (fun s => f s (y s)) (y'' s) (Icc t₀ (t₀ + T)) s)
    (hM : ∀ s ∈ Icc t₀ (t₀ + T), ‖y'' s‖ ≤ M) (hh : 0 < h) (ht : t ∈ Icc t₀ (t₀ + T))
    (hth : t + h ∈ Icc t₀ (t₀ + T)) : ‖lte (forwardEuler f) h y t‖ ≤ h / 2 * M := by
  have hsub : Icc t (t + h) ⊆ Icc t₀ (t₀ + T) := Icc_subset_Icc ht.1 hth.2
  have key := norm_sub_sub_smul_le_mul_sq_div_two (y' := fun s => f s (y s)) (by linarith)
    (fun s hs => (hy s (hsub hs)).mono hsub) (fun s hs => (hy' s (hsub hs)).mono hsub)
    (fun s hs => hM s (hsub hs))
  rw [add_sub_cancel_left] at key
  have key' : ‖y (t + h) - y t - h • forwardEuler f t (y t) (y (t + h)) h‖ ≤ M * h ^ 2 / 2 := key
  rw [lte_eq_inv_smul hh.ne', norm_smul, norm_inv, Real.norm_of_nonneg hh.le]
  calc h⁻¹ * ‖y (t + h) - y t - h • forwardEuler f t (y t) (y (t + h)) h‖
      ≤ h⁻¹ * (M * h ^ 2 / 2) := by gcongr
    _ = h / 2 * M := by field_simp

/-- **Backward Euler has order one**, local form. Let $I = [t_0, t_0 + T]$. Let $y$ have the
derivative $f(s, y(s))$ within $I$ at every $s \in I$, let $y''(s)$ be the derivative of
$s \mapsto f(s, y(s))$ within $I$, and let $\|y''(s)\| \le M$ for $s \in I$. If $h > 0$ and
$t, t + h \in I$, then the local truncation error of backward Euler satisfies
$$\|\tau(t; h)\| \le \frac{h}{2} M.$$

The proof uses the Taylor bound at $t + h$, backward in time. -/
theorem norm_lte_backwardEuler_le
    (hy : ∀ s ∈ Icc t₀ (t₀ + T), HasDerivWithinAt y (f s (y s)) (Icc t₀ (t₀ + T)) s)
    (hy' : ∀ s ∈ Icc t₀ (t₀ + T), HasDerivWithinAt (fun s => f s (y s)) (y'' s) (Icc t₀ (t₀ + T)) s)
    (hM : ∀ s ∈ Icc t₀ (t₀ + T), ‖y'' s‖ ≤ M) (hh : 0 < h) (ht : t ∈ Icc t₀ (t₀ + T))
    (hth : t + h ∈ Icc t₀ (t₀ + T)) : ‖lte (backwardEuler f) h y t‖ ≤ h / 2 * M := by
  have hsub : Icc t (t + h) ⊆ Icc t₀ (t₀ + T) := Icc_subset_Icc ht.1 hth.2
  have key := norm_sub_sub_smul_le_mul_sq_div_two' (y' := fun s => f s (y s)) (by linarith)
    (fun s hs => (hy s (hsub hs)).mono hsub) (fun s hs => (hy' s (hsub hs)).mono hsub)
    (fun s hs => hM s (hsub hs))
  rw [add_sub_cancel_left, sub_add_cancel_left, neg_smul, sub_neg_eq_add] at key
  rw [lte_eq_inv_smul hh.ne', norm_smul, norm_inv, Real.norm_of_nonneg hh.le]
  have e : y (t + h) - y t - h • backwardEuler f t (y t) (y (t + h)) h =
      -(y t - y (t + h) + h • f (t + h) (y (t + h))) := by
    simp only [backwardEuler]; abel
  rw [e, norm_neg]
  calc h⁻¹ * ‖y t - y (t + h) + h • f (t + h) (y (t + h))‖ ≤ h⁻¹ * (M * h ^ 2 / 2) := by gcongr
    _ = h / 2 * M := by field_simp

/-- **Crank–Nicolson has order two**, local form (Exercise 11.2 and (11.90) of
[quarteroni2000numerical]). Let $I = [t_0, t_0 + T]$. Let $y$ have the derivative $f(s, y(s))$
within $I$ at every $s \in I$, let $y''(s)$ be the derivative of $s \mapsto f(s, y(s))$ and
$y'''(s)$ the derivative of $y''$ within $I$, and let $\|y'''(s)\| \le M_3$ for $s \in I$. If
$h > 0$ and $t, t + h \in I$, then the local truncation error of Crank–Nicolson satisfies
$$\|\tau(t; h)\| \le \frac{h^2}{12} M_3.$$

The source writes the error with $\frac{h^2}{12} f''(\xi, y(\xi))$. This is the second
derivative of $s \mapsto f(s, y(s)) = y'(s)$, that is, $y'''$. -/
theorem norm_lte_crankNicolson_le
    (hy : ∀ s ∈ Icc t₀ (t₀ + T), HasDerivWithinAt y (f s (y s)) (Icc t₀ (t₀ + T)) s)
    (hy' : ∀ s ∈ Icc t₀ (t₀ + T), HasDerivWithinAt (fun s => f s (y s)) (y'' s) (Icc t₀ (t₀ + T)) s)
    (hy'' : ∀ s ∈ Icc t₀ (t₀ + T), HasDerivWithinAt y'' (y''' s) (Icc t₀ (t₀ + T)) s)
    (hM : ∀ s ∈ Icc t₀ (t₀ + T), ‖y''' s‖ ≤ M₃) (hh : 0 < h) (ht : t ∈ Icc t₀ (t₀ + T))
    (hth : t + h ∈ Icc t₀ (t₀ + T)) : ‖lte (crankNicolson f) h y t‖ ≤ h ^ 2 / 12 * M₃ := by
  have hsub : Icc t (t + h) ⊆ Icc t₀ (t₀ + T) := Icc_subset_Icc ht.1 hth.2
  have key := norm_sub_sub_smul_add_le_mul_pow_three_div_twelve (y' := fun s => f s (y s))
    (by linarith) (fun s hs => (hy s (hsub hs)).mono hsub)
    (fun s hs => (hy' s (hsub hs)).mono hsub) (fun s hs => (hy'' s (hsub hs)).mono hsub)
    (fun s hs => hM s (hsub hs))
  rw [add_sub_cancel_left] at key
  rw [lte_eq_inv_smul hh.ne', norm_smul, norm_inv, Real.norm_of_nonneg hh.le]
  have e : y (t + h) - y t - h • crankNicolson f t (y t) (y (t + h)) h =
      y (t + h) - y t - (h / 2) • (f t (y t) + f (t + h) (y (t + h))) := by
    simp only [crankNicolson, smul_smul, div_eq_mul_inv]
  rw [e]
  calc h⁻¹ * ‖y (t + h) - y t - (h / 2) • (f t (y t) + f (t + h) (y (t + h)))‖
      ≤ h⁻¹ * (M₃ * h ^ 3 / 12) := by gcongr
    _ = h ^ 2 / 12 * M₃ := by field_simp

/-- **Heun's method has order two**, local form (Exercise 11.1 of [quarteroni2000numerical]). Let
$I = [t_0, t_0 + T]$. Let $y$ have the derivative $f(s, y(s))$ within $I$ at every $s \in I$,
let $y''(s)$ be the derivative of $s \mapsto f(s, y(s))$ and $y'''(s)$ the derivative of $y''$
within $I$, with $\|y''(s)\| \le M_2$ and $\|y'''(s)\| \le M_3$ for $s \in I$, and let
$f(s, \cdot)$ be $L$-Lipschitz for $s \in I$. If $h > 0$ and $t, t + h \in I$, then the local
truncation error of Heun's method satisfies
$$\|\tau(t; h)\| \le \frac{h^2}{12} M_3 + \frac{h^2}{4} L M_2.$$

The residual of Heun's method is the Crank–Nicolson residual plus $\frac{h}{2} \bigl(f(t + h,
y(t + h)) - f(t + h, y(t) + h f(t, y(t)))\bigr)$. The Lipschitz constant times the forward Euler
residual bounds the second term. -/
theorem norm_lte_heun_le
    (hy : ∀ s ∈ Icc t₀ (t₀ + T), HasDerivWithinAt y (f s (y s)) (Icc t₀ (t₀ + T)) s)
    (hy' : ∀ s ∈ Icc t₀ (t₀ + T), HasDerivWithinAt (fun s => f s (y s)) (y'' s) (Icc t₀ (t₀ + T)) s)
    (hy'' : ∀ s ∈ Icc t₀ (t₀ + T), HasDerivWithinAt y'' (y''' s) (Icc t₀ (t₀ + T)) s)
    (hM₂ : ∀ s ∈ Icc t₀ (t₀ + T), ‖y'' s‖ ≤ M₂) (hM₃ : ∀ s ∈ Icc t₀ (t₀ + T), ‖y''' s‖ ≤ M₃)
    (hf : ∀ s ∈ Icc t₀ (t₀ + T), LipschitzWith L (f s)) (hh : 0 < h) (ht : t ∈ Icc t₀ (t₀ + T))
    (hth : t + h ∈ Icc t₀ (t₀ + T)) :
    ‖lte (heun f) h y t‖ ≤ h ^ 2 / 12 * M₃ + h ^ 2 / 4 * L * M₂ := by
  have hsub : Icc t (t + h) ⊆ Icc t₀ (t₀ + T) := Icc_subset_Icc ht.1 hth.2
  have k3 := norm_sub_sub_smul_add_le_mul_pow_three_div_twelve (y' := fun s => f s (y s))
    (by linarith) (fun s hs => (hy s (hsub hs)).mono hsub)
    (fun s hs => (hy' s (hsub hs)).mono hsub) (fun s hs => (hy'' s (hsub hs)).mono hsub)
    (fun s hs => hM₃ s (hsub hs))
  have k2 := norm_sub_sub_smul_le_mul_sq_div_two (y' := fun s => f s (y s)) (by linarith)
    (fun s hs => (hy s (hsub hs)).mono hsub) (fun s hs => (hy' s (hsub hs)).mono hsub)
    (fun s hs => hM₂ s (hsub hs))
  rw [add_sub_cancel_left] at k3 k2
  have kL : ‖f (t + h) (y (t + h)) - f (t + h) (y t + h • f t (y t))‖ ≤
      L * (M₂ * h ^ 2 / 2) := by
    refine ((hf _ hth).norm_sub_le _ _).trans (mul_le_mul_of_nonneg_left ?_ L.coe_nonneg)
    simpa [sub_sub] using k2
  rw [lte_eq_inv_smul hh.ne', norm_smul, norm_inv, Real.norm_of_nonneg hh.le]
  have e : y (t + h) - y t - h • heun f t (y t) (y (t + h)) h =
      (y (t + h) - y t - (h / 2) • (f t (y t) + f (t + h) (y (t + h)))) +
        (h / 2) • (f (t + h) (y (t + h)) - f (t + h) (y t + h • f t (y t))) := by
    simp only [heun, smul_smul, div_eq_mul_inv, smul_add, smul_sub]; abel
  rw [e]
  calc h⁻¹ * ‖(y (t + h) - y t - (h / 2) • (f t (y t) + f (t + h) (y (t + h)))) +
        (h / 2) • (f (t + h) (y (t + h)) - f (t + h) (y t + h • f t (y t)))‖
      ≤ h⁻¹ * (M₃ * h ^ 3 / 12 + h / 2 * (L * (M₂ * h ^ 2 / 2))) := by
        gcongr
        refine (norm_add_le _ _).trans (add_le_add k3 ?_)
        rw [norm_smul, Real.norm_of_nonneg (by positivity)]
        gcongr
    _ = h ^ 2 / 12 * M₃ + h ^ 2 / 4 * L * M₂ := by field_simp; ring

/-- **Local truncation error of the θ-method.** Let $I = [t_0, t_0 + T]$. Let $y$ have the
derivative $f(s, y(s))$ within $I$ at every $s \in I$, let $y''(s)$ be the derivative of
$s \mapsto f(s, y(s))$ and $y'''(s)$ the derivative of $y''$ within $I$, with
$\|y''(s)\| \le M_2$ and $\|y'''(s)\| \le M_3$ for $s \in I$. If $h > 0$ and $t, t + h \in I$,
then the local truncation error of the θ-method satisfies
$$\|\tau(t; h)\| \le |\theta - \tfrac12|\, M_2 h + \frac{h^2}{12} M_3.$$
This gives order $1$ for $\theta \neq 1/2$ and order $2$ for $\theta = 1/2$, where the first
term vanishes and the bound is that of Crank–Nicolson. It is the time part of the truncation
error estimate of Exercise 13.1 of [quarteroni2000numerical].

No Lipschitz condition on $f$ is needed. The residual is the Crank–Nicolson residual plus
$h(\frac12 - \theta)(y'(t + h) - y'(t))$, and the mean value inequality bounds the second term
by $|\frac12 - \theta| M_2 h^2$. -/
theorem norm_lte_theta_le {θ : ℝ}
    (hy : ∀ s ∈ Icc t₀ (t₀ + T), HasDerivWithinAt y (f s (y s)) (Icc t₀ (t₀ + T)) s)
    (hy' : ∀ s ∈ Icc t₀ (t₀ + T), HasDerivWithinAt (fun s => f s (y s)) (y'' s) (Icc t₀ (t₀ + T)) s)
    (hy'' : ∀ s ∈ Icc t₀ (t₀ + T), HasDerivWithinAt y'' (y''' s) (Icc t₀ (t₀ + T)) s)
    (hM₂ : ∀ s ∈ Icc t₀ (t₀ + T), ‖y'' s‖ ≤ M₂) (hM₃ : ∀ s ∈ Icc t₀ (t₀ + T), ‖y''' s‖ ≤ M₃)
    (hh : 0 < h) (ht : t ∈ Icc t₀ (t₀ + T)) (hth : t + h ∈ Icc t₀ (t₀ + T)) :
    ‖lte (theta f θ) h y t‖ ≤ |θ - 1 / 2| * M₂ * h + h ^ 2 / 12 * M₃ := by
  have hsub : Icc t (t + h) ⊆ Icc t₀ (t₀ + T) := Icc_subset_Icc ht.1 hth.2
  have k3 := norm_sub_sub_smul_add_le_mul_pow_three_div_twelve (y' := fun s => f s (y s))
    (by linarith) (fun s hs => (hy s (hsub hs)).mono hsub)
    (fun s hs => (hy' s (hsub hs)).mono hsub) (fun s hs => (hy'' s (hsub hs)).mono hsub)
    (fun s hs => hM₃ s (hsub hs))
  rw [add_sub_cancel_left] at k3
  have k1 : ‖f (t + h) (y (t + h)) - f t (y t)‖ ≤ M₂ * h := by
    have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := fun s => f s (y s))
      (fun s hs => (hy' s (hsub hs)).mono hsub) (fun s hs => hM₂ s (hsub hs)) (convex_Icc _ _)
      (left_mem_Icc.2 (by linarith)) (right_mem_Icc.2 (by linarith))
    rwa [add_sub_cancel_left, Real.norm_of_nonneg hh.le] at this
  rw [lte_eq_inv_smul hh.ne', norm_smul, norm_inv, Real.norm_of_nonneg hh.le]
  have e : y (t + h) - y t - h • theta f θ t (y t) (y (t + h)) h =
      (y (t + h) - y t - (h / 2) • (f t (y t) + f (t + h) (y (t + h)))) +
        (h * (1 / 2 - θ)) • (f (t + h) (y (t + h)) - f t (y t)) := by
    simp only [theta]
    module
  rw [e]
  calc h⁻¹ * ‖(y (t + h) - y t - (h / 2) • (f t (y t) + f (t + h) (y (t + h)))) +
        (h * (1 / 2 - θ)) • (f (t + h) (y (t + h)) - f t (y t))‖
      ≤ h⁻¹ * (M₃ * h ^ 3 / 12 + h * |1 / 2 - θ| * (M₂ * h)) := by
        gcongr
        refine (norm_add_le _ _).trans (add_le_add k3 ?_)
        rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_pos hh]
        gcongr
    _ = |θ - 1 / 2| * M₂ * h + h ^ 2 / 12 * M₃ := by
        rw [abs_sub_comm θ]; field_simp; ring

end Methods

/-! ### Orders of the elementary methods, and the direct forward Euler bound -/

section Orders

variable {f : ℝ → E → E} {y y'' y''' : ℝ → E} {M M₂ M₃ : ℝ} {L : NNReal}

/-- **Forward Euler has order one.** Let $I = [t_0, t_0 + T]$. Let $y$ have the derivative
$f(s, y(s))$ within $I$ at every $s \in I$, let $y''(s)$ be the derivative of
$s \mapsto f(s, y(s))$ within $I$, and let $\|y''(s)\| \le M$ for $s \in I$. Then forward Euler
has order $1$ along $y$ on $I$. -/
theorem hasOrderFor_forwardEuler
    (hy : ∀ s ∈ Icc t₀ (t₀ + T), HasDerivWithinAt y (f s (y s)) (Icc t₀ (t₀ + T)) s)
    (hy' : ∀ s ∈ Icc t₀ (t₀ + T), HasDerivWithinAt (fun s => f s (y s)) (y'' s) (Icc t₀ (t₀ + T)) s)
    (hM : ∀ s ∈ Icc t₀ (t₀ + T), ‖y'' s‖ ≤ M) : HasOrderFor (forwardEuler f) t₀ T y 1 :=
  hasOrderFor_of_forall_norm_lte_le (C := M / 2) fun h hh n hn => by
    rw [show M / 2 * h ^ 1 = h / 2 * M by ring]
    exact norm_lte_forwardEuler_le hy hy' hM hh (node_mem_Icc_of_lt hh hn)
      (node_add_mem_Icc_of_lt hh hn)

/-- **Backward Euler has order one.** Let $I = [t_0, t_0 + T]$. Let $y$ have the derivative
$f(s, y(s))$ within $I$ at every $s \in I$, let $y''(s)$ be the derivative of
$s \mapsto f(s, y(s))$ within $I$, and let $\|y''(s)\| \le M$ for $s \in I$. Then backward Euler
has order $1$ along $y$ on $I$. -/
theorem hasOrderFor_backwardEuler
    (hy : ∀ s ∈ Icc t₀ (t₀ + T), HasDerivWithinAt y (f s (y s)) (Icc t₀ (t₀ + T)) s)
    (hy' : ∀ s ∈ Icc t₀ (t₀ + T), HasDerivWithinAt (fun s => f s (y s)) (y'' s) (Icc t₀ (t₀ + T)) s)
    (hM : ∀ s ∈ Icc t₀ (t₀ + T), ‖y'' s‖ ≤ M) : HasOrderFor (backwardEuler f) t₀ T y 1 :=
  hasOrderFor_of_forall_norm_lte_le (C := M / 2) fun h hh n hn => by
    rw [show M / 2 * h ^ 1 = h / 2 * M by ring]
    exact norm_lte_backwardEuler_le hy hy' hM hh (node_mem_Icc_of_lt hh hn)
      (node_add_mem_Icc_of_lt hh hn)

/-- **Crank–Nicolson has order two.** Let $I = [t_0, t_0 + T]$. Let $y$ have the derivative
$f(s, y(s))$ within $I$ at every $s \in I$, let $y''(s)$ be the derivative of
$s \mapsto f(s, y(s))$ and $y'''(s)$ the derivative of $y''$ within $I$, and let
$\|y'''(s)\| \le M_3$ for $s \in I$. Then Crank–Nicolson has order $2$ along $y$ on $I$. -/
theorem hasOrderFor_crankNicolson
    (hy : ∀ s ∈ Icc t₀ (t₀ + T), HasDerivWithinAt y (f s (y s)) (Icc t₀ (t₀ + T)) s)
    (hy' : ∀ s ∈ Icc t₀ (t₀ + T), HasDerivWithinAt (fun s => f s (y s)) (y'' s) (Icc t₀ (t₀ + T)) s)
    (hy'' : ∀ s ∈ Icc t₀ (t₀ + T), HasDerivWithinAt y'' (y''' s) (Icc t₀ (t₀ + T)) s)
    (hM : ∀ s ∈ Icc t₀ (t₀ + T), ‖y''' s‖ ≤ M₃) : HasOrderFor (crankNicolson f) t₀ T y 2 :=
  hasOrderFor_of_forall_norm_lte_le (C := M₃ / 12) fun h hh n hn => by
    rw [show M₃ / 12 * h ^ 2 = h ^ 2 / 12 * M₃ by ring]
    exact norm_lte_crankNicolson_le hy hy' hy'' hM hh (node_mem_Icc_of_lt hh hn)
      (node_add_mem_Icc_of_lt hh hn)

/-- **Heun's method has order two** (Exercise 11.1 of [quarteroni2000numerical]). Let
$I = [t_0, t_0 + T]$. Let $y$ have the derivative $f(s, y(s))$ within $I$ at every $s \in I$,
let $y''(s)$ be the derivative of $s \mapsto f(s, y(s))$ and $y'''(s)$ the derivative of $y''$
within $I$, with $\|y''(s)\| \le M_2$ and $\|y'''(s)\| \le M_3$ for $s \in I$, and let
$f(s, \cdot)$ be $L$-Lipschitz for $s \in I$. Then Heun's method has order $2$ along $y$ on $I$. -/
theorem hasOrderFor_heun
    (hy : ∀ s ∈ Icc t₀ (t₀ + T), HasDerivWithinAt y (f s (y s)) (Icc t₀ (t₀ + T)) s)
    (hy' : ∀ s ∈ Icc t₀ (t₀ + T), HasDerivWithinAt (fun s => f s (y s)) (y'' s) (Icc t₀ (t₀ + T)) s)
    (hy'' : ∀ s ∈ Icc t₀ (t₀ + T), HasDerivWithinAt y'' (y''' s) (Icc t₀ (t₀ + T)) s)
    (hM₂ : ∀ s ∈ Icc t₀ (t₀ + T), ‖y'' s‖ ≤ M₂) (hM₃ : ∀ s ∈ Icc t₀ (t₀ + T), ‖y''' s‖ ≤ M₃)
    (hf : ∀ s ∈ Icc t₀ (t₀ + T), LipschitzWith L (f s)) : HasOrderFor (heun f) t₀ T y 2 :=
  hasOrderFor_of_forall_norm_lte_le (C := M₃ / 12 + L * M₂ / 4) fun h hh n hn => by
    rw [show (M₃ / 12 + L * M₂ / 4) * h ^ 2 = h ^ 2 / 12 * M₃ + h ^ 2 / 4 * L * M₂ by ring]
    exact norm_lte_heun_le hy hy' hy'' hM₂ hM₃ hf hh (node_mem_Icc_of_lt hh hn)
      (node_add_mem_Icc_of_lt hh hn)

/-- **The θ-method has order one** for every $\theta \in \mathbb{R}$. Let $I = [t_0, t_0 + T]$. Let
$y$ have the derivative $f(s, y(s))$ within $I$ at every $s \in I$, let $y''(s)$ be the
derivative of $s \mapsto f(s, y(s))$ and $y'''(s)$ the derivative of $y''$ within $I$, with
$\|y''(s)\| \le M_2$ and $\|y'''(s)\| \le M_3$ for $s \in I$. Then the θ-method has order $1$
along $y$ on $I$.

For $\theta = 1/2$ the order is $2$, by `ODE.OneStep.hasOrderFor_crankNicolson` and
`ODE.OneStep.theta_half`. -/
theorem hasOrderFor_theta {θ : ℝ}
    (hy : ∀ s ∈ Icc t₀ (t₀ + T), HasDerivWithinAt y (f s (y s)) (Icc t₀ (t₀ + T)) s)
    (hy' : ∀ s ∈ Icc t₀ (t₀ + T), HasDerivWithinAt (fun s => f s (y s)) (y'' s) (Icc t₀ (t₀ + T)) s)
    (hy'' : ∀ s ∈ Icc t₀ (t₀ + T), HasDerivWithinAt y'' (y''' s) (Icc t₀ (t₀ + T)) s)
    (hM₂ : ∀ s ∈ Icc t₀ (t₀ + T), ‖y'' s‖ ≤ M₂) (hM₃ : ∀ s ∈ Icc t₀ (t₀ + T), ‖y''' s‖ ≤ M₃) :
    HasOrderFor (theta f θ) t₀ T y 1 := by
  -- for `h ≤ 1` the bound is linear in `h`; the `O`-statement only sees small `h`
  refine IsBigO.of_bound (|θ - 1 / 2| * max M₂ 0 + max M₃ 0 / 12) ?_
  filter_upwards [Ioc_mem_nhdsGT (zero_lt_one' ℝ)] with h hh
  have hh0 : 0 ≤ h := hh.1.le
  rw [Real.norm_of_nonneg (globalLte_nonneg _), pow_one, Real.norm_of_nonneg hh0]
  refine globalLte_le (by positivity) fun n hn => ?_
  refine (norm_lte_theta_le hy hy' hy'' hM₂ hM₃ hh.1 (node_mem_Icc_of_lt hh.1 hn)
    (node_add_mem_Icc_of_lt hh.1 hn)).trans ?_
  have h1 : h ^ 2 / 12 * M₃ ≤ max M₃ 0 / 12 * h := by
    have : h ^ 2 ≤ h := by nlinarith [hh.1, hh.2]
    calc h ^ 2 / 12 * M₃ ≤ h ^ 2 / 12 * max M₃ 0 := by gcongr; exact le_max_left _ _
      _ ≤ h / 12 * max M₃ 0 := by gcongr
      _ = max M₃ 0 / 12 * h := by ring
  have h2 : |θ - 1 / 2| * M₂ * h ≤ |θ - 1 / 2| * max M₂ 0 * h := by
    gcongr; exact le_max_left _ _
  linarith

/-- The **direct error bound for forward Euler** ((11.22) of [quarteroni2000numerical]), which does
not use the discrete Gronwall lemma. Let $I = [t_0, t_0 + T]$, let $L > 0$, and let
$f(s, \cdot)$ be $L$-Lipschitz for $s \in I$. Let $y$ have the derivative $f(s, y(s))$ within
$I$ at every $s \in I$, let $y''(s)$ be the derivative of $s \mapsto f(s, y(s))$ within $I$, and
let $\|y''(s)\| \le M$ for $s \in I$. Let $h > 0$, and let $(u_n)$ be an orbit of forward Euler
with step $h$ and $u_0 = y(t_0)$. Then for every $n \le N_h$,
$$\|y(t_n) - u_n\| \le \frac{e^{Lnh} - 1}{L} \cdot \frac{M}{2} h.$$

The error $e_n$ satisfies $\|e_{n+1}\| \le h\,\tau(h) + (1 + hL)\|e_n\|$. This unrolls to
$\|e_n\| \le \frac{(1 + hL)^n - 1}{L} \tau(h)$, and $1 + hL \le e^{hL}$. With $s = nh$, the
bound is sharper than (11.20) by the factor $(e^{Ls} - 1)/(Ls) \le e^{Ls}$. -/
theorem norm_sub_le_forwardEuler (hf : ∀ s ∈ Icc t₀ (t₀ + T), LipschitzWith L (f s))
    (hL : 0 < (L : ℝ))
    (hy : ∀ s ∈ Icc t₀ (t₀ + T), HasDerivWithinAt y (f s (y s)) (Icc t₀ (t₀ + T)) s)
    (hy' : ∀ s ∈ Icc t₀ (t₀ + T), HasDerivWithinAt (fun s => f s (y s)) (y'' s) (Icc t₀ (t₀ + T)) s)
    (hM : ∀ s ∈ Icc t₀ (t₀ + T), ‖y'' s‖ ≤ M) (hh : 0 < h) {u : ℕ → E}
    (hu : IsOrbit (ofIncrement (forwardEuler f)) h t₀ u) (hu0 : u 0 = y t₀)
    (hn : n ≤ gridCount T h) :
    ‖y (node t₀ h n) - u n‖ ≤ (Real.exp (L * (n * h)) - 1) / L * (M / 2 * h) := by
  rw [isOrbit_ofIncrement_iff] at hu
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp [hu0]
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM t₀ (left_mem_Icc.2 (by
    linarith [nonneg_of_lt_gridCount hh (lt_of_lt_of_le hpos hn)])))
  -- the geometric bound
  have hgeom : ∀ m ≤ gridCount T h,
      ‖y (node t₀ h m) - u m‖ ≤ ((1 + h * L) ^ m - 1) / L * (M / 2 * h) := by
    intro m
    induction m with
    | zero => intro _; simp [hu0]
    | succ m ih =>
      intro hm
      have ih := ih (Nat.le_of_succ_le hm)
      have hmem := node_mem_Icc_of_lt (t₀ := t₀) hh hm
      have hmem' := node_add_mem_Icc_of_lt (t₀ := t₀) hh hm
      have hτ := norm_lte_forwardEuler_le hy hy' hM hh hmem hmem'
      have hlip : ‖f (node t₀ h m) (y (node t₀ h m)) - f (node t₀ h m) (u m)‖ ≤
          L * ‖y (node t₀ h m) - u m‖ := (hf _ hmem).norm_sub_le _ _
      have e : y (node t₀ h (m + 1)) - u (m + 1) =
          h • lte (forwardEuler f) h y (node t₀ h m) + (y (node t₀ h m) - u m) +
            h • (f (node t₀ h m) (y (node t₀ h m)) - f (node t₀ h m) (u m)) := by
        rw [hu m, node_succ, lte_spec hh.ne' (Φ := forwardEuler f) y (node t₀ h m)]
        simp only [forwardEuler, smul_sub]
        abel
      rw [e]
      refine norm_add₃_le.trans ?_
      rw [norm_smul, norm_smul, Real.norm_of_nonneg hh.le]
      have hstep : h * ‖lte (forwardEuler f) h y (node t₀ h m)‖ + ‖y (node t₀ h m) - u m‖ +
          h * ‖f (node t₀ h m) (y (node t₀ h m)) - f (node t₀ h m) (u m)‖ ≤
          h * (h / 2 * M) + (1 + h * L) * ‖y (node t₀ h m) - u m‖ := by
        nlinarith [mul_le_mul_of_nonneg_left hlip hh.le, mul_le_mul_of_nonneg_left hτ hh.le]
      refine hstep.trans ?_
      calc h * (h / 2 * M) + (1 + h * L) * ‖y (node t₀ h m) - u m‖
          ≤ h * (h / 2 * M) + (1 + h * L) * (((1 + h * L) ^ m - 1) / L * (M / 2 * h)) := by
            gcongr
        _ = ((1 + h * L) ^ (m + 1) - 1) / L * (M / 2 * h) := by
            field_simp
            ring
  refine (hgeom n hn).trans ?_
  have hexp : (1 + h * L) ^ n ≤ Real.exp (L * (n * h)) := by
    calc (1 + h * L) ^ n ≤ Real.exp (h * L) ^ n := by
          gcongr
          linarith [Real.add_one_le_exp (h * L)]
      _ = Real.exp (L * (n * h)) := by rw [← Real.exp_nat_mul]; ring_nf
  gcongr

end Orders

/-! ### Absolute stability on the test equation -/

end OneStep

/-- The vector field $f(t, y) = \lambda y$ on $\mathbb{C}$ of the test equation $y' = \lambda y$
((11.24) of [quarteroni2000numerical]), for $\lambda \in \mathbb{C}$. -/
def testField (lam : ℂ) : ℝ → ℂ → ℂ := fun _ y => lam * y

/-- For $\lambda \in \mathbb{C}$, the function $t \mapsto e^{\lambda t}$ on $\mathbb{R}$ solves the
test equation: its derivative at $t$ is $\lambda e^{\lambda t}$. -/
theorem hasDerivAt_exp_testField (lam : ℂ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp (lam * t))
      (testField lam t (Complex.exp (lam * t))) t := by
  have h1 : HasDerivAt (fun z : ℂ => Complex.exp (lam * z)) (Complex.exp (lam * t) * lam) t := by
    have := (Complex.hasDerivAt_exp (lam * t)).comp (t : ℂ) ((hasDerivAt_id (t : ℂ)).const_mul lam)
    simpa [Function.comp_def] using this
  exact h1.comp_ofReal.congr_deriv (by simp [testField, mul_comm])

namespace OneStep

/-- **Absolute stability** of a step relation $S$ on $\mathbb{C}$ with step $h$ (Definition 11.6 of
[quarteroni2000numerical]): every initial value $u_0 \in \mathbb{C}$ has an orbit of $S$ from
time $0$, and every orbit of $S$ from time $0$ tends to $0$. The step relation is meant to be a
method applied to the test equation.

The existence clause matters for implicit methods at their singular parameter: backward Euler at
$h\lambda = 1$ and Crank–Nicolson at $h\lambda = 2$. There the only orbit is $0$, and without
the clause the method would be absolutely stable for this trivial reason. -/
def IsAbsStable (S : StepRel ℂ) (h : ℝ) : Prop :=
  (∀ u₀ : ℂ, ∃ u : ℕ → ℂ, IsOrbit S h 0 u ∧ u 0 = u₀) ∧
    ∀ u : ℕ → ℂ, IsOrbit S h 0 u → Tendsto u atTop (𝓝 0)

/-- The **region of absolute stability** $\mathcal{A}$ of a method $M$ ((11.26) of
[quarteroni2000numerical]): the set of $z \in \mathbb{C}$ such that, for every $h > 0$, the
method applied to the test equation with $\lambda = z/h$ is absolutely stable with step $h$.

The source defines the region as the set of $h\lambda$ for which (11.25) holds. For a method
that might not depend on $h\lambda$ alone, this definition asks for every factorization
$z = h\lambda$ with $h > 0$. For a method that depends on $h\lambda$ alone, the region is the
slice $h = 1$ (`ODE.OneStep.absStabilityRegion_eq_of_scaleInvariant`). -/
def absStabilityRegion (M : Method ℂ) : Set ℂ :=
  {z | ∀ h : ℝ, 0 < h → IsAbsStable (M (testField (z / h))) h}

/-- A method is **A-stable** (§11.3.3 of [quarteroni2000numerical]) if its region of absolute
stability contains the open left half-plane: $\operatorname{Re} z < 0$ implies
$z \in \mathcal{A}$. The source writes this as $\mathcal{A} \cap \mathbb{C}^- = \mathbb{C}^-$. -/
def IsAStable (M : Method ℂ) : Prop := ∀ z : ℂ, z.re < 0 → z ∈ absStabilityRegion M

variable {M : Method ℂ} {h : ℝ}

/-- Let $S$ and $S'$ be step relations on $\mathbb{C}$ and $h, h'$ real. If $S$ with step $h$ and
$S'$ with step $h'$ have the same orbits from time $0$, then $S$ is absolutely stable with step
$h$ if and only if $S'$ is absolutely stable with step $h'$. -/
theorem isAbsStable_congr {S S' : StepRel ℂ} {h h' : ℝ}
    (hS : ∀ u, IsOrbit S h 0 u ↔ IsOrbit S' h' 0 u) : IsAbsStable S h ↔ IsAbsStable S' h' := by
  simp only [IsAbsStable, hS]

/-- Let $M$ be a method whose orbits on the test equation depend on $(h, \lambda)$ only through
$h\lambda$: for every $h > 0$ and every $\lambda$, a sequence is an orbit of $M$ applied to
$y' = \lambda y$ with step $h$ if and only if it is an orbit of $M$ applied to $y' = h\lambda y$
with step $1$. Then the region of absolute stability is the slice $h = 1$: $z \in \mathcal{A}$
if and only if $M$ applied to $y' = zy$ is absolutely stable with step $1$. -/
theorem absStabilityRegion_eq_of_scaleInvariant
    (hM : ∀ h > 0, ∀ lam u, IsOrbit (M (testField lam)) h 0 u ↔
      IsOrbit (M (testField (h * lam))) 1 0 u) :
    absStabilityRegion M = {z | IsAbsStable (M (testField z)) 1} := by
  ext z
  simp only [absStabilityRegion, mem_ofPred_eq]
  constructor
  · intro hz
    simpa using hz 1 one_pos
  · intro hz h hh
    rw [isAbsStable_congr (hM h hh (z / h)), mul_div_cancel₀ _ (Complex.ofReal_ne_zero.2 hh.ne')]
    exact hz

/-- Let $M$ be a method whose orbits on the test equation depend on $(h, \lambda)$ only through
$h\lambda$, as in `ODE.OneStep.absStabilityRegion_eq_of_scaleInvariant`. Let $h > 0$ and
$\lambda \in \mathbb{C}$. Then $M$ applied to $y' = \lambda y$ is absolutely stable with step
$h$ if and only if $h\lambda \in \mathcal{A}$. -/
theorem isAbsStable_iff_mem_absStabilityRegion
    (hM : ∀ h > 0, ∀ lam u, IsOrbit (M (testField lam)) h 0 u ↔
      IsOrbit (M (testField (h * lam))) 1 0 u) (hh : 0 < h) (lam : ℂ) :
    IsAbsStable (M (testField lam)) h ↔ (h : ℂ) * lam ∈ absStabilityRegion M := by
  rw [absStabilityRegion_eq_of_scaleInvariant hM, mem_ofPred_eq]
  exact isAbsStable_congr (hM h hh lam)

/-- Let $r \in \mathbb{C}$, and let $S$ be a step relation whose orbits from time $0$ with step $h$
are exactly the geometric sequences with ratio $r$: the sequence $(r^n u_0)$ is an orbit for
every $u_0$, and every orbit satisfies $u_n = r^n u_0$. Then $S$ is absolutely stable with step
$h$ if and only if $|r| < 1$. -/
theorem isAbsStable_iff_norm_lt_one {S : StepRel ℂ} {r : ℂ}
    (hex : ∀ u₀ : ℂ, IsOrbit S h 0 fun n => r ^ n * u₀)
    (hall : ∀ u, IsOrbit S h 0 u → ∀ n, u n = r ^ n * u 0) : IsAbsStable S h ↔ ‖r‖ < 1 := by
  constructor
  · rintro ⟨-, hdecay⟩
    have := hdecay _ (hex 1)
    simp only [mul_one] at this
    exact tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.1 this
  · intro hr
    refine ⟨fun u₀ => ⟨_, hex u₀, by simp⟩, fun u hu => ?_⟩
    have : Tendsto (fun n => r ^ n * u 0) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hr).mul_const (u 0)
    exact this.congr fun n => (hall u hu n).symm

/-- If every orbit of $S$ from time $0$ with step $h$ is identically zero, then $S$ is not
absolutely stable with step $h$: the initial value $1$ has no orbit. -/
theorem not_isAbsStable_of_forall_eq_zero {S : StepRel ℂ}
    (hall : ∀ u, IsOrbit S h 0 u → ∀ n, u n = 0) : ¬ IsAbsStable S h := by
  rintro ⟨hex, -⟩
  obtain ⟨u, hu, hu0⟩ := hex 1
  exact one_ne_zero (hu0.symm.trans (hall u hu 0))

section FourMethods

variable {lam : ℂ} {u : ℕ → ℂ} {h : ℝ}

/-- Every orbit of forward Euler on the test equation $y' = \lambda y$ with step $h$ satisfies
$u_n = (1 + h\lambda)^n u_0$. -/
theorem forwardEuler_testField_orbit
    (hu : IsOrbit (ofIncrement (forwardEuler (testField lam))) h 0 u) (n : ℕ) :
    u n = (1 + h * lam) ^ n * u 0 := by
  rw [isOrbit_ofIncrement_iff] at hu
  induction n with
  | zero => simp
  | succ n ih => rw [hu n, ih]; simp only [forwardEuler, testField, Complex.real_smul]; ring

/-- For every $\lambda, u_0 \in \mathbb{C}$ and every real $h$, the sequence $(1 + h\lambda)^n u_0$
is an orbit of forward Euler on the test equation $y' = \lambda y$ with step $h$. -/
theorem isOrbit_forwardEuler_testField (lam : ℂ) (h : ℝ) (u₀ : ℂ) :
    IsOrbit (ofIncrement (forwardEuler (testField lam))) h 0 fun n => (1 + h * lam) ^ n * u₀ := by
  rw [isOrbit_ofIncrement_iff]
  intro n
  simp only [forwardEuler, testField, Complex.real_smul]
  ring

/-- Let $h > 0$. A sequence is an orbit of forward Euler on $y' = \lambda y$ with step $h$ if and
only if it is an orbit of forward Euler on $y' = h\lambda y$ with step $1$. -/
theorem forwardEuler_scaleInvariant (h : ℝ) (_ : 0 < h) (lam : ℂ) (u : ℕ → ℂ) :
    IsOrbit (ofIncrement (forwardEuler (testField lam))) h 0 u ↔
      IsOrbit (ofIncrement (forwardEuler (testField (h * lam)))) 1 0 u := by
  simp only [isOrbit_ofIncrement_iff, forwardEuler, testField, Complex.real_smul,
    Complex.ofReal_one, one_mul]
  refine forall_congr' fun n => ?_
  constructor <;> intro H <;> linear_combination H

/-- **The region of absolute stability of forward Euler** ((11.27) of [quarteroni2000numerical]) is
the open disc of radius $1$ about $-1$: $z \in \mathcal{A}$ if and only if $|1 + z| < 1$. -/
theorem mem_absStabilityRegion_forwardEuler_iff (z : ℂ) :
    z ∈ absStabilityRegion (fun f => ofIncrement (forwardEuler f)) ↔ ‖1 + z‖ < 1 := by
  rw [absStabilityRegion_eq_of_scaleInvariant forwardEuler_scaleInvariant, mem_ofPred_eq]
  refine isAbsStable_iff_norm_lt_one (r := 1 + z) (fun u₀ => ?_) (fun u hu n => ?_)
  · simpa using isOrbit_forwardEuler_testField z 1 u₀
  · simpa using forwardEuler_testField_orbit hu n

/-- Let $h > 0$ and $\operatorname{Re} \lambda < 0$. Forward Euler on the test equation
$y' = \lambda y$ is absolutely stable with step $h$ if and only if
$$h < \frac{-2 \operatorname{Re} \lambda}{|\lambda|^2}.$$
This is the second form of (11.27) of [quarteroni2000numerical]. -/
theorem isAbsStable_forwardEuler_iff (hh : 0 < h) (hlam : lam.re < 0) :
    IsAbsStable (ofIncrement (forwardEuler (testField lam))) h ↔ h < -2 * lam.re / ‖lam‖ ^ 2 := by
  rw [isAbsStable_iff_mem_absStabilityRegion (M := fun f => ofIncrement (forwardEuler f))
    forwardEuler_scaleInvariant hh, mem_absStabilityRegion_forwardEuler_iff]
  have hlam0 : 0 < ‖lam‖ ^ 2 := by
    have : lam ≠ 0 := fun h0 => by simp [h0] at hlam
    positivity
  rw [lt_div_iff₀ hlam0, ← sq_lt_one_iff₀ (norm_nonneg _), Complex.sq_norm, Complex.sq_norm,
    Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero, zero_add]
  constructor <;> intro H <;> nlinarith [hh]

/-- Let $h\lambda \neq 1$. Every orbit of backward Euler on the test equation $y' = \lambda y$ with
step $h$ satisfies $u_n = (1 - h\lambda)^{-n} u_0$. -/
theorem backwardEuler_testField_orbit (hne : (h : ℂ) * lam ≠ 1)
    (hu : IsOrbit (ofIncrement (backwardEuler (testField lam))) h 0 u) (n : ℕ) :
    u n = (1 - h * lam)⁻¹ ^ n * u 0 := by
  rw [isOrbit_ofIncrement_iff] at hu
  have hne' : (1 : ℂ) - h * lam ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
  induction n with
  | zero => simp
  | succ n ih =>
    have := hu n
    simp only [backwardEuler, testField, Complex.real_smul] at this
    have e : (1 - h * lam) * u (n + 1) = u n := by linear_combination this
    calc u (n + 1) = (1 - h * lam)⁻¹ * u n := by
          rw [← e, ← mul_assoc, inv_mul_cancel₀ hne', one_mul]
      _ = (1 - h * lam)⁻¹ ^ (n + 1) * u 0 := by rw [ih, pow_succ]; ring

/-- Let $h\lambda = 1$, the singular parameter. Every orbit of backward Euler on the test equation
$y' = \lambda y$ with step $h$ is identically zero. -/
theorem backwardEuler_testField_orbit_eq_zero (heq : (h : ℂ) * lam = 1)
    (hu : IsOrbit (ofIncrement (backwardEuler (testField lam))) h 0 u) (n : ℕ) : u n = 0 := by
  rw [isOrbit_ofIncrement_iff] at hu
  have := hu n
  simp only [backwardEuler, testField, Complex.real_smul, ← mul_assoc] at this
  linear_combination -this - u (n + 1) * heq

/-- Let $h\lambda \neq 1$. For every $u_0 \in \mathbb{C}$, the sequence $(1 - h\lambda)^{-n} u_0$ is
an orbit of backward Euler on the test equation $y' = \lambda y$ with step $h$. -/
theorem isOrbit_backwardEuler_testField (hne : (h : ℂ) * lam ≠ 1) (u₀ : ℂ) :
    IsOrbit (ofIncrement (backwardEuler (testField lam))) h 0
      fun n => (1 - h * lam)⁻¹ ^ n * u₀ := by
  rw [isOrbit_ofIncrement_iff]
  intro n
  have hne' : (1 : ℂ) - h * lam ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
  simp only [backwardEuler, testField, Complex.real_smul, pow_succ]
  field_simp
  ring

/-- Let $h > 0$. A sequence is an orbit of backward Euler on $y' = \lambda y$ with step $h$ if and
only if it is an orbit of backward Euler on $y' = h\lambda y$ with step $1$. -/
theorem backwardEuler_scaleInvariant (h : ℝ) (_ : 0 < h) (lam : ℂ) (u : ℕ → ℂ) :
    IsOrbit (ofIncrement (backwardEuler (testField lam))) h 0 u ↔
      IsOrbit (ofIncrement (backwardEuler (testField (h * lam)))) 1 0 u := by
  simp only [isOrbit_ofIncrement_iff, backwardEuler, testField, Complex.real_smul,
    Complex.ofReal_one, one_mul]
  refine forall_congr' fun n => ?_
  constructor <;> intro H <;> linear_combination H

/-- **The region of absolute stability of backward Euler** is the exterior of the closed disc of
radius $1$ about $1$: $z \in \mathcal{A}$ if and only if $|1 - z| > 1$.

The existence clause of `ODE.OneStep.IsAbsStable` excludes the point $z = 1$. -/
theorem mem_absStabilityRegion_backwardEuler_iff (z : ℂ) :
    z ∈ absStabilityRegion (fun f => ofIncrement (backwardEuler f)) ↔ 1 < ‖1 - z‖ := by
  rw [absStabilityRegion_eq_of_scaleInvariant backwardEuler_scaleInvariant, mem_ofPred_eq]
  by_cases hz : z = 1
  · subst hz
    refine ⟨fun H => absurd H (not_isAbsStable_of_forall_eq_zero fun u hu n =>
      backwardEuler_testField_orbit_eq_zero (h := 1) (lam := 1) (by simp) hu n),
      fun H => absurd H (by simp)⟩
  · have hne : ((1 : ℝ) : ℂ) * z ≠ 1 := by simpa using hz
    rw [isAbsStable_iff_norm_lt_one (r := (1 - z)⁻¹) (fun u₀ => ?_) (fun u hu n => ?_)]
    · rw [norm_inv, inv_lt_one₀ (norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hz)))]
    · simpa using isOrbit_backwardEuler_testField hne u₀
    · simpa using backwardEuler_testField_orbit hne hu n

/-- **Backward Euler is A-stable.** -/
theorem isAStable_backwardEuler : IsAStable fun f => ofIncrement (backwardEuler f) := by
  intro z hz
  rw [mem_absStabilityRegion_backwardEuler_iff, ← sq_lt_sq₀ zero_le_one (norm_nonneg _),
    Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, zero_sub, one_pow]
  nlinarith [sq_nonneg z.im]

/-- Let $h\lambda \neq 2$. Every orbit of Crank–Nicolson on the test equation $y' = \lambda y$ with
step $h$ satisfies
$$u_n = \left(\frac{1 + h\lambda/2}{1 - h\lambda/2}\right)^n u_0.$$
-/
theorem crankNicolson_testField_orbit (hne : (h : ℂ) * lam ≠ 2)
    (hu : IsOrbit (ofIncrement (crankNicolson (testField lam))) h 0 u) (n : ℕ) :
    u n = ((1 + h * lam / 2) / (1 - h * lam / 2)) ^ n * u 0 := by
  rw [isOrbit_ofIncrement_iff] at hu
  have hne' : (1 : ℂ) - h * lam / 2 ≠ 0 := by
    intro h0
    apply hne
    linear_combination (-2 : ℂ) * h0
  induction n with
  | zero => simp
  | succ n ih =>
    have := hu n
    simp only [crankNicolson, testField, Complex.real_smul] at this
    push_cast at this
    have e : (1 - h * lam / 2) * u (n + 1) = (1 + h * lam / 2) * u n := by
      linear_combination this
    calc u (n + 1) = (1 + h * lam / 2) / (1 - h * lam / 2) * u n := by
          rw [div_mul_eq_mul_div, eq_div_iff hne', ← e]; ring
      _ = ((1 + h * lam / 2) / (1 - h * lam / 2)) ^ (n + 1) * u 0 := by rw [ih, pow_succ]; ring

/-- Let $h\lambda = 2$, the singular parameter. Every orbit of Crank–Nicolson on the test equation
$y' = \lambda y$ with step $h$ is identically zero. -/
theorem crankNicolson_testField_orbit_eq_zero (heq : (h : ℂ) * lam = 2)
    (hu : IsOrbit (ofIncrement (crankNicolson (testField lam))) h 0 u) (n : ℕ) : u n = 0 := by
  rw [isOrbit_ofIncrement_iff] at hu
  have := hu n
  simp only [crankNicolson, testField, Complex.real_smul] at this
  push_cast at this
  linear_combination (-1 / 2 : ℂ) * this - (u n + u (n + 1)) / 4 * heq

/-- Let $h\lambda \neq 2$. For every $u_0 \in \mathbb{C}$, the sequence $\left(\frac{1 +
h\lambda/2}{1 - h\lambda/2}\right)^n u_0$ is an orbit of Crank–Nicolson on the test equation
$y' = \lambda y$ with step $h$. -/
theorem isOrbit_crankNicolson_testField (hne : (h : ℂ) * lam ≠ 2) (u₀ : ℂ) :
    IsOrbit (ofIncrement (crankNicolson (testField lam))) h 0
      fun n => ((1 + h * lam / 2) / (1 - h * lam / 2)) ^ n * u₀ := by
  rw [isOrbit_ofIncrement_iff]
  intro n
  simp only [crankNicolson, testField, Complex.real_smul, pow_succ]
  push_cast
  field_simp
  ring

/-- Let $h > 0$. A sequence is an orbit of Crank–Nicolson on $y' = \lambda y$ with step $h$ if and
only if it is an orbit of Crank–Nicolson on $y' = h\lambda y$ with step $1$. -/
theorem crankNicolson_scaleInvariant (h : ℝ) (_ : 0 < h) (lam : ℂ) (u : ℕ → ℂ) :
    IsOrbit (ofIncrement (crankNicolson (testField lam))) h 0 u ↔
      IsOrbit (ofIncrement (crankNicolson (testField (h * lam)))) 1 0 u := by
  simp only [isOrbit_ofIncrement_iff, crankNicolson, testField, Complex.real_smul,
    Complex.ofReal_one, one_mul]
  refine forall_congr' fun n => ?_
  constructor <;> intro H <;> linear_combination H

/-- **The region of absolute stability of Crank–Nicolson** is the open left half-plane:
$z \in \mathcal{A}$ if and only if $\operatorname{Re} z < 0$.

The existence clause of `ODE.OneStep.IsAbsStable` excludes the point $z = 2$. -/
theorem mem_absStabilityRegion_crankNicolson_iff (z : ℂ) :
    z ∈ absStabilityRegion (fun f => ofIncrement (crankNicolson f)) ↔ z.re < 0 := by
  rw [absStabilityRegion_eq_of_scaleInvariant crankNicolson_scaleInvariant, mem_ofPred_eq]
  by_cases hz : z = 2
  · subst hz
    refine ⟨fun H => absurd H (not_isAbsStable_of_forall_eq_zero fun u hu n =>
      crankNicolson_testField_orbit_eq_zero (h := 1) (lam := 2) (by simp) hu n),
      fun H => absurd H (by norm_num)⟩
  · have hne : ((1 : ℝ) : ℂ) * z ≠ 2 := by simpa using hz
    have hne' : (1 : ℂ) - z / 2 ≠ 0 := by
      intro h0
      apply hz
      linear_combination (-2 : ℂ) * h0
    rw [isAbsStable_iff_norm_lt_one (r := (1 + z / 2) / (1 - z / 2)) (fun u₀ => ?_)
      (fun u hu n => ?_)]
    · rw [norm_div, div_lt_one (norm_pos_iff.2 hne'), ← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _),
        Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
      simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.one_re,
        Complex.one_im, Complex.div_ofNat_re, Complex.div_ofNat_im, zero_add, zero_sub]
      constructor <;> intro H <;> nlinarith [H]
    · simpa using isOrbit_crankNicolson_testField hne u₀
    · simpa using crankNicolson_testField_orbit hne hu n

/-- **Crank–Nicolson is A-stable.** -/
theorem isAStable_crankNicolson : IsAStable fun f => ofIncrement (crankNicolson f) :=
  fun z hz => (mem_absStabilityRegion_crankNicolson_iff z).2 hz

/-- Every orbit of Heun's method on the test equation $y' = \lambda y$ with step $h$ satisfies
$u_n = (1 + h\lambda + (h\lambda)^2/2)^n u_0$. -/
theorem heun_testField_orbit (hu : IsOrbit (ofIncrement (heun (testField lam))) h 0 u) (n : ℕ) :
    u n = (1 + h * lam + (h * lam) ^ 2 / 2) ^ n * u 0 := by
  rw [isOrbit_ofIncrement_iff] at hu
  induction n with
  | zero => simp
  | succ n ih =>
    rw [hu n, ih]
    simp only [heun, testField, Complex.real_smul]
    push_cast
    ring

/-- For every $\lambda, u_0 \in \mathbb{C}$ and every real $h$, the sequence
$(1 + h\lambda + (h\lambda)^2/2)^n u_0$ is an orbit of Heun's method on the test equation
$y' = \lambda y$ with step $h$. -/
theorem isOrbit_heun_testField (lam : ℂ) (h : ℝ) (u₀ : ℂ) :
    IsOrbit (ofIncrement (heun (testField lam))) h 0
      fun n => (1 + h * lam + (h * lam) ^ 2 / 2) ^ n * u₀ := by
  rw [isOrbit_ofIncrement_iff]
  intro n
  simp only [heun, testField, Complex.real_smul]
  push_cast
  ring

/-- Let $h > 0$. A sequence is an orbit of Heun's method on $y' = \lambda y$ with step $h$ if and
only if it is an orbit of Heun's method on $y' = h\lambda y$ with step $1$. -/
theorem heun_scaleInvariant (h : ℝ) (_ : 0 < h) (lam : ℂ) (u : ℕ → ℂ) :
    IsOrbit (ofIncrement (heun (testField lam))) h 0 u ↔
      IsOrbit (ofIncrement (heun (testField (h * lam)))) 1 0 u := by
  simp only [isOrbit_ofIncrement_iff, heun, testField, Complex.real_smul, Complex.ofReal_one,
    one_mul]
  refine forall_congr' fun n => ?_
  constructor <;> intro H <;> linear_combination H

/-- **The region of absolute stability of Heun's method**: $z \in \mathcal{A}$ if and only if
$|1 + z + z^2/2| < 1$. -/
theorem mem_absStabilityRegion_heun_iff (z : ℂ) :
    z ∈ absStabilityRegion (fun f => ofIncrement (heun f)) ↔ ‖1 + z + z ^ 2 / 2‖ < 1 := by
  rw [absStabilityRegion_eq_of_scaleInvariant heun_scaleInvariant, mem_ofPred_eq]
  refine isAbsStable_iff_norm_lt_one (r := 1 + z + z ^ 2 / 2) (fun u₀ => ?_) (fun u hu n => ?_)
  · simpa using isOrbit_heun_testField z 1 u₀
  · simpa using heun_testField_orbit hu n

/-- **Forward Euler is not A-stable**: the point $z = -3$ lies in the open left half-plane but not
in the region of absolute stability. -/
theorem not_isAStable_forwardEuler : ¬ IsAStable fun f => ofIncrement (forwardEuler f) := by
  intro H
  have := (mem_absStabilityRegion_forwardEuler_iff (-3)).1 (H (-3) (by norm_num))
  norm_num at this

/-- **Heun's method is not A-stable**: the point $z = -3$ lies in the open left half-plane but not
in the region of absolute stability. -/
theorem not_isAStable_heun : ¬ IsAStable fun f => ofIncrement (heun f) := by
  intro H
  have := (mem_absStabilityRegion_heun_iff (-3)).1 (H (-3) (by norm_num))
  norm_num at this

/-- For real $x$, $x$ lies in the region of absolute stability of forward Euler if and only if
$x \in (-2, 0)$. -/
theorem ofReal_mem_absStabilityRegion_forwardEuler_iff (x : ℝ) :
    (x : ℂ) ∈ absStabilityRegion (fun f => ofIncrement (forwardEuler f)) ↔ x ∈ Ioo (-2) 0 := by
  rw [mem_absStabilityRegion_forwardEuler_iff, ← Complex.ofReal_one, ← Complex.ofReal_add,
    Complex.norm_real, Real.norm_eq_abs, abs_lt, mem_Ioo]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- For real $x$, $x$ lies in the region of absolute stability of Heun's method if and only if
$x \in (-2, 0)$, as for forward Euler (§11.3.3 of [quarteroni2000numerical]). -/
theorem ofReal_mem_absStabilityRegion_heun_iff (x : ℝ) :
    (x : ℂ) ∈ absStabilityRegion (fun f => ofIncrement (heun f)) ↔ x ∈ Ioo (-2) 0 := by
  rw [mem_absStabilityRegion_heun_iff]
  have e : (1 : ℂ) + x + (x : ℂ) ^ 2 / 2 = ((1 + x + x ^ 2 / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [e, Complex.norm_real, Real.norm_eq_abs, abs_lt, mem_Ioo]
  constructor
  · rintro ⟨-, h2⟩
    constructor <;> nlinarith [h2]
  · rintro ⟨h1, h2⟩
    constructor <;> nlinarith [h1, h2]

end FourMethods

end OneStep

end ODE
