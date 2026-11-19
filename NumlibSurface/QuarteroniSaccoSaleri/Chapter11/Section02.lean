/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.ODE.OneStep

/-!
# Quarteroni, Sacco and Saleri, Section 11.2: One-step numerical methods

This module formalizes Section 11.2 of [quarteroni2000numerical]. The interval $[t_0, t_0 + T]$ is
discretized by the nodes $t_n = t_0 + nh$, $n = 0, \dots, N_h$, where $N_h$ is the largest integer
with $t_{N_h} \le t_0 + T$. Definition 11.2 separates one-step methods from multistep methods. The
four elementary one-step methods are forward Euler (11.7), backward Euler (11.8), Crank–Nicolson
(11.9) and Heun (11.10), written as the book writes them. Definition 11.3 separates explicit methods
from implicit methods, and the module proves the book's classification of the four methods.

All statements are the scalar case $E = \mathbb{R}$ of `Numlib.ODE.OneStep`. The grid is `ODE.node`
and `ODE.gridCount`. A one-step method is a step relation `ODE.OneStep.StepRel ℝ`; for the methods
of this chapter it is the relation `ODE.OneStep.ofIncrement Φ` of an increment function
`Φ : ODE.OneStep.Increment ℝ`. The four methods are `ODE.OneStep.forwardEuler`,
`ODE.OneStep.backwardEuler`, `ODE.OneStep.crankNicolson` and `ODE.OneStep.heun`.

## Main definitions

* Section 11.2, `QuarteroniSaccoSaleri.Chapter11.grid` and
  `QuarteroniSaccoSaleri.Chapter11.gridCount`: the nodes $t_n$ and their number $N_h$.
* Definition 11.2, `QuarteroniSaccoSaleri.Chapter11.definition_11_2`: the one-step method with
  increment function $\Phi$, as a rule that produces $u_{n+1}$ from $u_n$.
* Equations (11.7)–(11.10), `QuarteroniSaccoSaleri.Chapter11.equation_11_7`,
  `QuarteroniSaccoSaleri.Chapter11.equation_11_8`, `QuarteroniSaccoSaleri.Chapter11.equation_11_9`
  and `QuarteroniSaccoSaleri.Chapter11.equation_11_10`: the four methods, as increment functions.
* Definition 11.3, `QuarteroniSaccoSaleri.Chapter11.definition_11_3`: the method is explicit.

## Main results

* Section 11.2, `QuarteroniSaccoSaleri.Chapter11.grid_gridCount_le` and
  `QuarteroniSaccoSaleri.Chapter11.lt_grid_gridCount_succ`: $N_h$ is the largest $n$ with
  $t_n \le t_0 + T$.
* Definition 11.2, `QuarteroniSaccoSaleri.Chapter11.definition_11_2_iff`: the recursion
  $u_{n+1} = u_n + h\Phi(t_n, u_n, u_{n+1}; h)$.
* Equations (11.7)–(11.10), `QuarteroniSaccoSaleri.Chapter11.equation_11_7_iterate`,
  `QuarteroniSaccoSaleri.Chapter11.equation_11_8_orbit`,
  `QuarteroniSaccoSaleri.Chapter11.equation_11_9_orbit` and
  `QuarteroniSaccoSaleri.Chapter11.equation_11_10_iterate`: the four methods unfolded to the
  recursions of the book.
* Definition 11.3, `QuarteroniSaccoSaleri.Chapter11.definition_11_3_forwardEuler`,
  `QuarteroniSaccoSaleri.Chapter11.definition_11_3_heun`,
  `QuarteroniSaccoSaleri.Chapter11.definition_11_3_backwardEuler` and
  `QuarteroniSaccoSaleri.Chapter11.definition_11_3_crankNicolson`: (11.7) and (11.10) are explicit,
  and (11.8) and (11.9) are implicit.

## Conventions

* The book's $f_n = f(t_n, u_n)$ is written out.
* An increment function takes the arguments `Φ t u v h`, where `v` is the new value $u_{n+1}$. An
  explicit method does not use `v`, so implicit methods are increment functions too.
* A sequence $u : \mathbb{N} \to \mathbb{R}$ produced by an increment function is an orbit,
  `ODE.OneStep.IsOrbit (ODE.OneStep.ofIncrement Φ) h t₀ u`. The explicit iteration from $y_0$ is
  `ODE.OneStep.iterate Φ h t₀ y₀`, whose second component is $u_n$.

## Deviations from the source

* **Section 11.2, grid and equations (11.7)–(11.10)** (generalization). The grid expression and
  recurrence identities extend to all natural indices and real steps. The positive-step grid
  maximality claims also hold for $T=0$. The orbit predicate gives the recursion without fixing
  the starting value, while `iterate` starts from $y_0$.
* **Definitions 11.2 and 11.3** (reading). `definition_11_2` constructs a one-step relation from
  a supplied increment. `definition_11_3` tests whether this increment depends on the new state.
  The backward Euler and Crank–Nicolson results exhibit $f(t,y)=y$ as a dependence witness.
  Particular fields independent of $y$ can give explicit increments.
-/

open Set ODE ODE.OneStep

namespace QuarteroniSaccoSaleri.Chapter11

variable {f : ℝ → ℝ → ℝ} {t₀ T h y₀ : ℝ} {n : ℕ}

/-! ### The grid -/

/-- **Section 11.2** of [quarteroni2000numerical], the discretization nodes. For
$t_0, h \in \mathbb{R}$ and $n \in \mathbb{N}$ the **node** is $t_n = t_0 + nh$.

The definition is `ODE.node`.

**Generalization.** The node formula uses all natural indices and arbitrary real spacing. -/
def grid (t₀ h : ℝ) (n : ℕ) : ℝ := ODE.node t₀ h n

/-- For $t_0, h \in \mathbb{R}$ and $n \in \mathbb{N}$, the node is $t_n = t_0 + nh$.

**Generalization.** The node formula uses all natural indices and arbitrary real spacing. -/
theorem grid_eq (t₀ h : ℝ) (n : ℕ) : grid t₀ h n = t₀ + n * h := rfl

/-- **Section 11.2** of [quarteroni2000numerical], the number of steps. For $T, h \in \mathbb{R}$
the **number of steps** is $N_h = \lfloor T/h \rfloor$, the natural-number floor of $T/h$, which
is $0$ when $T/h < 0$. For $T \ge 0$ and $h > 0$ it is the largest integer $n$ with
$t_n \le t_0 + T$, by `QuarteroniSaccoSaleri.Chapter11.grid_gridCount_le` and
`QuarteroniSaccoSaleri.Chapter11.lt_grid_gridCount_succ`.

The definition is `ODE.gridCount`.

**Generalization.** The count is the natural floor of $T/h$. Its maximality properties allow
$T=0$ for $h>0$. -/
noncomputable def gridCount (T h : ℝ) : ℕ := ODE.gridCount T h

/-- **Section 11.2** of [quarteroni2000numerical]. Let $T \ge 0$ and $h > 0$. Then
$t_{N_h} \le t_0 + T$.

**Generalization.** The count is the natural floor of $T/h$. Its maximality properties allow
$T=0$ for $h>0$. -/
theorem grid_gridCount_le (hT : 0 ≤ T) (hh : 0 < h) : grid t₀ h (gridCount T h) ≤ t₀ + T :=
  (node_mem_Icc hT hh le_rfl).2

/-- **Section 11.2** of [quarteroni2000numerical], maximality of $N_h$. Let $T \ge 0$ and $h > 0$.
Then $t_0 + T < t_{N_h + 1}$.

**Generalization.** The count is the natural floor of $T/h$. Its maximality properties allow
$T=0$ for $h>0$. -/
theorem lt_grid_gridCount_succ (hT : 0 ≤ T) (hh : 0 < h) :
    t₀ + T < grid t₀ h (gridCount T h + 1) := by
  have : ¬ ((gridCount T h + 1 : ℕ) : ℝ) * h ≤ T := fun hle =>
    absurd ((le_gridCount_iff hT hh).2 hle) (Nat.not_succ_le_self _)
  rw [grid_eq]
  push Not at this
  linarith

/-! ### One-step methods -/

/-- **Definition 11.2** of [quarteroni2000numerical] (one-step methods). A numerical method is a
**one-step method** if $u_{n+1}$ depends only on $u_n$. The one-step methods of this chapter are
given by an increment function $\Phi$ built from the field $f$, through the rule
$$u_{n+1} = u_n + h \Phi(t_n, u_n, u_{n+1}; h).$$

The method is the map that sends $f$ to the step relation `ODE.OneStep.ofIncrement (Φ f)`. It is
an `ODE.OneStep.Method ℝ`.

**Reading.** Constructs a one-step relation from a supplied increment. The orbit equation is
required at all indices and leaves the initial value free. -/
def definition_11_2 (Φ : (ℝ → ℝ → ℝ) → ODE.OneStep.Increment ℝ) : ODE.OneStep.Method ℝ :=
  fun f => ODE.OneStep.ofIncrement (Φ f)

/-- **Definition 11.2** of [quarteroni2000numerical], unfolded. Let $\Phi$ build an increment
function from the field $f$, and let $u : \mathbb{N} \to \mathbb{R}$. Then $u$ is an orbit of
the one-step method with step $h$ from $t_0$ if and only if for every $n \in \mathbb{N}$
$$u_{n+1} = u_n + h \Phi(t_n, u_n, u_{n+1}; h).$$
So $u_{n+1}$ is determined by $u_n$, $t_n$, $h$ and $f$.

**Reading.** Constructs a one-step relation from a supplied increment. The orbit equation is
required at all indices and leaves the initial value free. -/
theorem definition_11_2_iff (Φ : (ℝ → ℝ → ℝ) → ODE.OneStep.Increment ℝ) (u : ℕ → ℝ) :
    IsOrbit (definition_11_2 Φ f) h t₀ u ↔
      ∀ n, u (n + 1) = u n + h * Φ f (grid t₀ h n) (u n) (u (n + 1)) h :=
  isOrbit_ofIncrement_iff

/-- **Equation (11.7)** of [quarteroni2000numerical], the forward Euler method
$u_{n+1} = u_n + h f_n$. Its increment function is $\Phi(t, u, v; h) = f(t, u)$.

The definition is `ODE.OneStep.forwardEuler`. -/
def equation_11_7 (f : ℝ → ℝ → ℝ) : ODE.OneStep.Increment ℝ := forwardEuler f

/-- **Equation (11.7)** of [quarteroni2000numerical], the forward Euler iteration. For $f :
\mathbb{R} \times \mathbb{R} \to \mathbb{R}$, $h, t_0, y_0 \in \mathbb{R}$ and
$n \in \mathbb{N}$, the values $u_n$ of the iteration from $u_0 = y_0$ satisfy
$$u_{n+1} = u_n + h f(t_n, u_n).$$

**Generalization.** The recursion holds at every natural index with any real step. An orbit
predicate leaves the initial value free, whereas the explicit iteration starts from its
supplied value. -/
theorem equation_11_7_iterate (f : ℝ → ℝ → ℝ) (h t₀ y₀ : ℝ) (n : ℕ) :
    (iterate (equation_11_7 f) h t₀ y₀ (n + 1)).2 =
      (iterate (equation_11_7 f) h t₀ y₀ n).2 +
        h * f (grid t₀ h n) (iterate (equation_11_7 f) h t₀ y₀ n).2 := by
  rw [iterate_succ, step, iterate_fst]
  rfl

/-- **Equation (11.8)** of [quarteroni2000numerical], the backward Euler method
$u_{n+1} = u_n + h f_{n+1}$. Its increment function is $\Phi(t, u, v; h) = f(t + h, v)$.

The definition is `ODE.OneStep.backwardEuler`. -/
def equation_11_8 (f : ℝ → ℝ → ℝ) : ODE.OneStep.Increment ℝ := backwardEuler f

/-- **Equation (11.8)** of [quarteroni2000numerical], the backward Euler recursion. A sequence
$u : \mathbb{N} \to \mathbb{R}$ is an orbit of the backward Euler method with step $h$ from
$t_0$ if and only if for every $n \in \mathbb{N}$
$$u_{n+1} = u_n + h f(t_{n+1}, u_{n+1}).$$

**Generalization.** The recursion holds at every natural index with any real step. An orbit
predicate leaves the initial value free, whereas the explicit iteration starts from its
supplied value. -/
theorem equation_11_8_orbit (u : ℕ → ℝ) :
    IsOrbit (ofIncrement (equation_11_8 f)) h t₀ u ↔
      ∀ n, u (n + 1) = u n + h * f (grid t₀ h (n + 1)) (u (n + 1)) := by
  rw [isOrbit_ofIncrement_iff]
  refine forall_congr' fun n => ?_
  rw [grid, node_succ]
  rfl

/-- **Equation (11.9)** of [quarteroni2000numerical], the Crank–Nicolson (trapezoidal) method
$u_{n+1} = u_n + \frac{h}{2}(f_n + f_{n+1})$. Its increment function is $\Phi(t, u, v; h) =
\frac{1}{2}(f(t, u) + f(t + h, v))$.

The definition is `ODE.OneStep.crankNicolson`. -/
noncomputable def equation_11_9 (f : ℝ → ℝ → ℝ) : ODE.OneStep.Increment ℝ := crankNicolson f

/-- **Equation (11.9)** of [quarteroni2000numerical], the Crank–Nicolson recursion. A sequence
$u : \mathbb{N} \to \mathbb{R}$ is an orbit of the Crank–Nicolson method with step $h$ from
$t_0$ if and only if for every $n \in \mathbb{N}$
$$u_{n+1} = u_n + \frac{h}{2}\bigl(f(t_n, u_n) + f(t_{n+1}, u_{n+1})\bigr).$$

**Generalization.** The recursion holds at every natural index with any real step. An orbit
predicate leaves the initial value free, whereas the explicit iteration starts from its
supplied value. -/
theorem equation_11_9_orbit (u : ℕ → ℝ) :
    IsOrbit (ofIncrement (equation_11_9 f)) h t₀ u ↔
      ∀ n, u (n + 1) =
        u n + h / 2 * (f (grid t₀ h n) (u n) + f (grid t₀ h (n + 1)) (u (n + 1))) := by
  rw [isOrbit_ofIncrement_iff]
  refine forall_congr' fun n => ?_
  rw [grid, grid, node_succ]
  simp only [equation_11_9, crankNicolson, smul_eq_mul]
  ring_nf

/-- **Equation (11.10)** of [quarteroni2000numerical], Heun's method $u_{n+1} = u_n +
\frac{h}{2}\bigl(f_n + f(t_{n+1}, u_n + h f_n)\bigr)$. Its increment function is $\Phi(t, u, v;
h) = \frac{1}{2}\bigl(f(t, u) + f(t + h, u + h f(t, u))\bigr)$.

The definition is `ODE.OneStep.heun`. -/
noncomputable def equation_11_10 (f : ℝ → ℝ → ℝ) : ODE.OneStep.Increment ℝ := heun f

/-- **Equation (11.10)** of [quarteroni2000numerical], Heun's iteration. For $f : \mathbb{R} \times
\mathbb{R} \to \mathbb{R}$, $h, t_0, y_0 \in \mathbb{R}$ and $n \in \mathbb{N}$, the values
$u_n$ of the iteration from $u_0 = y_0$ satisfy
$$u_{n+1} = u_n + \frac{h}{2}\bigl(f(t_n, u_n) + f(t_{n+1}, u_n + h f(t_n, u_n))\bigr).$$

**Generalization.** The recursion holds at every natural index with any real step. An orbit
predicate leaves the initial value free, whereas the explicit iteration starts from its
supplied value. -/
theorem equation_11_10_iterate (f : ℝ → ℝ → ℝ) (h t₀ y₀ : ℝ) (n : ℕ) :
    (iterate (equation_11_10 f) h t₀ y₀ (n + 1)).2 =
      (iterate (equation_11_10 f) h t₀ y₀ n).2 +
        h / 2 * (f (grid t₀ h n) (iterate (equation_11_10 f) h t₀ y₀ n).2 +
          f (grid t₀ h (n + 1)) ((iterate (equation_11_10 f) h t₀ y₀ n).2 +
            h * f (grid t₀ h n) (iterate (equation_11_10 f) h t₀ y₀ n).2)) := by
  rw [iterate_succ, step, iterate_fst, grid, grid, node_succ]
  simp only [equation_11_10, heun, smul_eq_mul]
  ring_nf

/-- **Definition 11.3** of [quarteroni2000numerical] (explicit and implicit methods). The one-step
method with increment function $\Phi$ is **explicit** if $u_{n+1}$ can be computed directly from
$u_n$, that is, if $\Phi(t, u, v; h)$ does not depend on its third argument $v = u_{n+1}$.
Otherwise the method is **implicit**, and $u_{n+1}$ depends on itself through $f$.

The definition is `ODE.OneStep.IsExplicit`.

**Reading.** For the supplied one-step increment, explicitness means independence of its new-
state argument for all choices of the other arguments. -/
def definition_11_3 (Φ : ODE.OneStep.Increment ℝ) : Prop := ODE.OneStep.IsExplicit Φ

/-- **Definition 11.3** of [quarteroni2000numerical], forward Euler. For every field $f$, the
forward Euler method (11.7) is explicit. -/
theorem definition_11_3_forwardEuler (f : ℝ → ℝ → ℝ) : definition_11_3 (equation_11_7 f) :=
  isExplicit_forwardEuler f

/-- **Definition 11.3** of [quarteroni2000numerical], Heun's method. For every field $f$, Heun's
method (11.10) is explicit. -/
theorem definition_11_3_heun (f : ℝ → ℝ → ℝ) : definition_11_3 (equation_11_10 f) :=
  isExplicit_heun f

/-- **Definition 11.3** of [quarteroni2000numerical], backward Euler. The backward Euler method
(11.8) is implicit: for the field $f(t, y) = y$ its increment function depends on $u_{n+1}$.

**Reading.** The statement establishes dependence for the witness field $f(t,y)=y$. A field
independent of $y$ gives an increment independent of the new state. -/
theorem definition_11_3_backwardEuler : ¬ definition_11_3 (equation_11_8 fun _ y => y) := by
  intro hex
  have := hex 0 0 0 1 0
  simp [equation_11_8, backwardEuler] at this

/-- **Definition 11.3** of [quarteroni2000numerical], Crank–Nicolson. The Crank–Nicolson method
(11.9) is implicit: for the field $f(t, y) = y$ its increment function depends on $u_{n+1}$.

**Reading.** The statement establishes dependence for the witness field $f(t,y)=y$. A field
independent of $y$ gives an increment independent of the new state. -/
theorem definition_11_3_crankNicolson : ¬ definition_11_3 (equation_11_9 fun _ y => y) := by
  intro hex
  have := hex 0 0 0 1 0
  simp [equation_11_9, crankNicolson] at this

end QuarteroniSaccoSaleri.Chapter11
