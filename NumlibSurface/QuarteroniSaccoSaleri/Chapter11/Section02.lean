import Numlib.ODE.OneStep

/-!
# Quarteroni–Sacco–Saleri §11.2: one-step numerical methods

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*,
Springer, 2000, §11.2.

The discretization of `[t₀, t₀ + T]` by the nodes `t_n = t₀ + n h`, `n = 0, …, N_h`, with `N_h`
the largest integer such that `t_{N_h} ≤ t₀ + T`; Definition 11.2 (one-step versus multistep
methods); the four elementary one-step methods — forward Euler (11.7), backward Euler (11.8),
Crank–Nicolson (11.9) and Heun (11.10) — written as the book writes them; and Definition 11.3
(explicit versus implicit methods), with the book's classification of the four.

Everything is the scalar case `E = ℝ` of `Numlib/ODE/OneStep`: the grid is `ODE.node` and
`ODE.gridCount`, a one-step method is a step relation `ODE.OneStep.StepRel ℝ` — for the methods
of this chapter the relation `ODE.OneStep.ofIncrement Φ` of an increment function
`Φ : ODE.OneStep.Increment ℝ` — and the four methods are `ODE.OneStep.forwardEuler`,
`backwardEuler`, `crankNicolson`, `heun`.

## Main definitions

* `grid t₀ h n`, `gridCount T h` — the nodes `t_n` and their number `N_h`.
* `definition_11_2 Φ` — the one-step method with increment function `Φ`, as a rule producing
  `u_{n+1}` from `u_n`.
* `equation_11_7 f`, `equation_11_8 f`, `equation_11_9 f`, `equation_11_10 f` — the four
  methods, as increment functions.
* `definition_11_3 Φ` — the method is explicit.

## Main results

* `grid_gridCount_le`, `lt_grid_gridCount_succ` — `N_h` is the largest `n` with `t_n ≤ t₀ + T`.
* `equation_11_7_iterate`, `equation_11_8_orbit`, `equation_11_9_orbit`, `equation_11_10_iterate`
  — the four methods unfolded to the book's recursions.
* `definition_11_3_forwardEuler`, `definition_11_3_heun`, `definition_11_3_backwardEuler`,
  `definition_11_3_crankNicolson` — (11.7) and (11.10) are explicit, (11.8) and (11.9) are not.

## Conventions

The book's `f_n = f(t_n, u_n)` is written out; an increment function takes the arguments
`Φ t u v h` where `v` is the new value `u_{n+1}` (inert for an explicit method), so that implicit
methods are increment functions too. An orbit `u : ℕ → ℝ` of an increment function is
`ODE.OneStep.IsOrbit (ODE.OneStep.ofIncrement Φ) h t₀ u`, and the explicit iteration from `y₀` is
`ODE.OneStep.iterate Φ h t₀ y₀`.
-/

open Set ODE ODE.OneStep

namespace QuarteroniSaccoSaleri.Chapter11

variable {f : ℝ → ℝ → ℝ} {t₀ T h y₀ : ℝ} {n : ℕ}

/-! ### The grid -/

/-- **The discretization nodes** `t_n = t₀ + n h` of §11.2 (`ODE.node`). -/
def grid (t₀ h : ℝ) (n : ℕ) : ℝ := ODE.node t₀ h n

/-- `t_n = t₀ + n h`. -/
theorem grid_eq (t₀ h : ℝ) (n : ℕ) : grid t₀ h n = t₀ + n * h := rfl

/-- **The number of steps** `N_h`, the maximum integer such that `t_{N_h} ≤ t₀ + T`
(`ODE.gridCount`). -/
noncomputable def gridCount (T h : ℝ) : ℕ := ODE.gridCount T h

/-- `t_{N_h} ≤ t₀ + T`. -/
theorem grid_gridCount_le (hT : 0 ≤ T) (hh : 0 < h) : grid t₀ h (gridCount T h) ≤ t₀ + T :=
  (node_mem_Icc hT hh le_rfl).2

/-- `N_h` is maximal: `t₀ + T < t_{N_h + 1}`. -/
theorem lt_grid_gridCount_succ (hT : 0 ≤ T) (hh : 0 < h) :
    t₀ + T < grid t₀ h (gridCount T h + 1) := by
  have : ¬ ((gridCount T h + 1 : ℕ) : ℝ) * h ≤ T := fun hle =>
    absurd ((le_gridCount_iff hT hh).2 hle) (Nat.not_succ_le_self _)
  rw [grid_eq]
  push Not at this
  linarith

/-! ### One-step methods -/

/-- **Definition 11.2 (one-step methods)**: a numerical method is a one-step method if
`u_{n+1}` depends only on `u_n`. The one-step methods of this chapter are the step relations
`ODE.OneStep.ofIncrement (Φ f)` of an increment function `Φ` built from the field `f`: this is
the rule `u_{n+1} = u_n + h Φ(t_n, u_n, u_{n+1}; h)`, an `ODE.OneStep.Method ℝ`. -/
def definition_11_2 (Φ : (ℝ → ℝ → ℝ) → ODE.OneStep.Increment ℝ) : ODE.OneStep.Method ℝ :=
  fun f => ODE.OneStep.ofIncrement (Φ f)

/-- The one-step method with increment `Φ`, unfolded: `u_{n+1}` is determined by `u_n` (and
`t_n`, `h`, `f`) through `u_{n+1} = u_n + h Φ(t_n, u_n, u_{n+1}; h)`. -/
theorem definition_11_2_iff (Φ : (ℝ → ℝ → ℝ) → ODE.OneStep.Increment ℝ) (u : ℕ → ℝ) :
    IsOrbit (definition_11_2 Φ f) h t₀ u ↔
      ∀ n, u (n + 1) = u n + h * Φ f (grid t₀ h n) (u n) (u (n + 1)) h :=
  isOrbit_ofIncrement_iff

/-- **Forward Euler (11.7)**, `u_{n+1} = u_n + h f_n`: `ODE.OneStep.forwardEuler`. -/
def equation_11_7 (f : ℝ → ℝ → ℝ) : ODE.OneStep.Increment ℝ := forwardEuler f

/-- The forward Euler iteration: `u_{n+1} = u_n + h f(t_n, u_n)`. -/
theorem equation_11_7_iterate (f : ℝ → ℝ → ℝ) (h t₀ y₀ : ℝ) (n : ℕ) :
    (iterate (equation_11_7 f) h t₀ y₀ (n + 1)).2 =
      (iterate (equation_11_7 f) h t₀ y₀ n).2 +
        h * f (grid t₀ h n) (iterate (equation_11_7 f) h t₀ y₀ n).2 := by
  rw [iterate_succ, step, iterate_fst]
  rfl

/-- **Backward Euler (11.8)**, `u_{n+1} = u_n + h f_{n+1}`: `ODE.OneStep.backwardEuler`. -/
def equation_11_8 (f : ℝ → ℝ → ℝ) : ODE.OneStep.Increment ℝ := backwardEuler f

/-- The backward Euler recursion: `u_{n+1} = u_n + h f(t_{n+1}, u_{n+1})`. -/
theorem equation_11_8_orbit (u : ℕ → ℝ) :
    IsOrbit (ofIncrement (equation_11_8 f)) h t₀ u ↔
      ∀ n, u (n + 1) = u n + h * f (grid t₀ h (n + 1)) (u (n + 1)) := by
  rw [isOrbit_ofIncrement_iff]
  refine forall_congr' fun n => ?_
  rw [grid, node_succ]
  rfl

/-- **Crank–Nicolson (11.9)**, the trapezoidal method `u_{n+1} = u_n + (h/2) (f_n + f_{n+1})`:
`ODE.OneStep.crankNicolson`. -/
noncomputable def equation_11_9 (f : ℝ → ℝ → ℝ) : ODE.OneStep.Increment ℝ := crankNicolson f

/-- The Crank–Nicolson recursion: `u_{n+1} = u_n + (h/2) (f(t_n, u_n) + f(t_{n+1}, u_{n+1}))`. -/
theorem equation_11_9_orbit (u : ℕ → ℝ) :
    IsOrbit (ofIncrement (equation_11_9 f)) h t₀ u ↔
      ∀ n, u (n + 1) =
        u n + h / 2 * (f (grid t₀ h n) (u n) + f (grid t₀ h (n + 1)) (u (n + 1))) := by
  rw [isOrbit_ofIncrement_iff]
  refine forall_congr' fun n => ?_
  rw [grid, grid, node_succ]
  simp only [equation_11_9, crankNicolson, smul_eq_mul]
  ring_nf

/-- **Heun's method (11.10)**, `u_{n+1} = u_n + (h/2) (f_n + f(t_{n+1}, u_n + h f_n))`:
`ODE.OneStep.heun`. -/
noncomputable def equation_11_10 (f : ℝ → ℝ → ℝ) : ODE.OneStep.Increment ℝ := heun f

/-- Heun's iteration: `u_{n+1} = u_n + (h/2) (f(t_n, u_n) + f(t_{n+1}, u_n + h f(t_n, u_n)))`. -/
theorem equation_11_10_iterate (f : ℝ → ℝ → ℝ) (h t₀ y₀ : ℝ) (n : ℕ) :
    (iterate (equation_11_10 f) h t₀ y₀ (n + 1)).2 =
      (iterate (equation_11_10 f) h t₀ y₀ n).2 +
        h / 2 * (f (grid t₀ h n) (iterate (equation_11_10 f) h t₀ y₀ n).2 +
          f (grid t₀ h (n + 1)) ((iterate (equation_11_10 f) h t₀ y₀ n).2 +
            h * f (grid t₀ h n) (iterate (equation_11_10 f) h t₀ y₀ n).2)) := by
  rw [iterate_succ, step, iterate_fst, grid, grid, node_succ]
  simp only [equation_11_10, heun, smul_eq_mul]
  ring_nf

/-- **Definition 11.3 (explicit and implicit methods)**: the one-step method with increment
`Φ` is explicit if `u_{n+1}` can be computed directly from `u_n`, i.e. `Φ` does not depend on
its third argument `u_{n+1}` (`ODE.OneStep.IsExplicit`); it is implicit otherwise, `u_{n+1}`
then depending on itself through `f`. -/
def definition_11_3 (Φ : ODE.OneStep.Increment ℝ) : Prop := ODE.OneStep.IsExplicit Φ

/-- Forward Euler (11.7) is explicit. -/
theorem definition_11_3_forwardEuler (f : ℝ → ℝ → ℝ) : definition_11_3 (equation_11_7 f) :=
  isExplicit_forwardEuler f

/-- Heun's method (11.10) is explicit. -/
theorem definition_11_3_heun (f : ℝ → ℝ → ℝ) : definition_11_3 (equation_11_10 f) :=
  isExplicit_heun f

/-- Backward Euler (11.8) is implicit: for the field `f(t, y) = y` its increment depends on
`u_{n+1}`. -/
theorem definition_11_3_backwardEuler : ¬ definition_11_3 (equation_11_8 fun _ y => y) := by
  intro hex
  have := hex 0 0 0 1 0
  simp [equation_11_8, backwardEuler] at this

/-- Crank–Nicolson (11.9) is implicit: for the field `f(t, y) = y` its increment depends on
`u_{n+1}`. -/
theorem definition_11_3_crankNicolson : ¬ definition_11_3 (equation_11_9 fun _ y => y) := by
  intro hex
  have := hex 0 0 0 1 0
  simp [equation_11_9, crankNicolson] at this

end QuarteroniSaccoSaleri.Chapter11
