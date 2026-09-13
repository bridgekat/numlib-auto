import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Numlib.ODE.RungeKutta
import NumlibSurface.QuarteroniSaccoSaleri.Chapter11.Section01
import NumlibSurface.QuarteroniSaccoSaleri.Chapter11.Section02

/-!
# Quarteroni–Sacco–Saleri §11.3: analysis of one-step methods

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*,
Springer, 2000, §11.3.

The general explicit one-step method (11.11) `u_{n+1} = u_n + h Φ(t_n, u_n, f_n; h)` with its
increment function; the local truncation error `τ_{n+1}(h)` defined by (11.12) and the global one
`τ(h) = max_n |τ_{n+1}(h)|`; consistency (`τ(h) → 0`), the criterion (11.13), and order `p`
(11.14), with forward Euler of order 1; zero-stability (Definition 11.4, (11.15)–(11.17)), Theorem
11.1 with its Lipschitz hypothesis (11.18), the discrete Gronwall lemma (Lemma 11.2); convergence
(Definition 11.5), Theorem 11.2 with the estimate (11.20), and the direct forward Euler bound
(11.22); the test problem (11.24), absolute stability (Definition 11.6), the region `𝒜` (11.26),
the regions of the four elementary methods ((11.27), the backward Euler, Crank–Nicolson and Heun
regions), Examples 11.1–11.2, A-stability, and Remark 11.2 for the explicit Runge–Kutta methods.

Everything is the scalar case `E = ℝ` of `Numlib/ODE/OneStep` and `Numlib/ODE/Gronwall` — the
test equation on `E = ℂ` — with `Numlib/ODE/RungeKutta` for Remark 11.2. The book's `C²`
solutions are bridged to the explicit-derivative hypotheses of the backbone by
`hasDerivWithinAt_derivWithin_of_contDiffOn_two`.

## Main definitions

* `equation_11_11 Φ h t₀ y₀ u` — `u` is the sequence produced by the method (11.11) from `y₀`.
* `equation_11_12 Φ h y t₀ n`, `globalTruncationError Φ t₀ T y h` — `τ_{n+1}(h)` and `τ(h)`.
* `consistent Φ t₀ T y`, `equation_11_14 Φ t₀ T y p` — consistency and order `p` along `y`.
* `definition_11_4 Φ t₀ T y₀`, `equation_11_18 Φ t₀ T h₀ Λ` — zero-stability and the Lipschitz
  hypothesis of Theorem 11.1.
* `definition_11_5 S t₀ T y₀ y`, `definition_11_5_order S t₀ T y₀ y p` — convergence, with order.
* `testProblem λ`, `definition_11_6 M λ h`, `equation_11_26 M`, `aStable M` — the test problem,
  absolute stability, its region, and A-stability.

## Main results

* `equation_11_13` — the consistency criterion.
* `forwardEuler_order_one_lte`, `forwardEuler_order_one` — forward Euler has order 1.
* `theorem_11_1`, `theorem_11_1_estimate`, `lemma_11_2` — zero-stability.
* `theorem_11_2`, `theorem_11_2_convergent`, `theorem_11_2_order`, `equation_11_22` — convergence.
* `equation_11_27`, `example_11_1`, `backwardEuler_absStabilityRegion`, `example_11_2`,
  `crankNicolson_absStabilityRegion`, `heun_absStabilityRegion`,
  `aStable_backwardEuler`, `aStable_crankNicolson`, `not_aStable_forwardEuler`,
  `not_aStable_heun`, `remark_11_2` — absolute stability.

## Conventions

An increment function is `Φ : ODE.OneStep.Increment ℝ`, `Φ t u v h`, with the book's `f_n`
built in and the third argument the new value (inert for an explicit `Φ`); `y ∈ C²([t₀, t₀ + T])`
is `ContDiffOn ℝ 2 y (Icc t₀ (t₀ + T))` and `y''` is `iteratedDerivWithin 2 y (Icc t₀ (t₀ + T))`.
The book's (11.13) "for all `t_n`" is read uniformly in `t ∈ [t₀, t₀ + T]`, which is what
`τ(h) = max_n |τ_{n+1}(h)| → 0` needs. The region `𝒜` is the set of `z = hλ` for which every
factorization `z = hλ`, `h > 0`, gives an absolutely stable method; for the methods of this
section it is the `h = 1` slice (see `Numlib/ODE/OneStep`).
-/

open Set Filter Topology Asymptotics ODE ODE.OneStep
open Finset (range)

namespace QuarteroniSaccoSaleri.Chapter11

variable {f : ℝ → ℝ → ℝ} {Φ : ODE.OneStep.Increment ℝ} {t₀ T h h₀ Λ y₀ : ℝ} {y : ℝ → ℝ} {n : ℕ}

/-! ### From `C²` regularity to explicit derivatives -/

/-- A `C²` function on `[a, b]`, `a < b`, has the derivatives `y' = derivWithin y [a, b]` and
`y'' = iteratedDerivWithin 2 y [a, b]` within `[a, b]` at every point of `[a, b]`; the bridge from
the book's regularity hypotheses to the explicit-derivative hypotheses of `Numlib/ODE/OneStep`.
TODO(backbone): a calculus module should hold this. -/
theorem hasDerivWithinAt_derivWithin_of_contDiffOn_two {a b : ℝ} (hlt : a < b) {y : ℝ → ℝ}
    (hy : ContDiffOn ℝ 2 y (Icc a b)) :
    (∀ s ∈ Icc a b, HasDerivWithinAt y (derivWithin y (Icc a b) s) (Icc a b) s) ∧
      ∀ s ∈ Icc a b, HasDerivWithinAt (derivWithin y (Icc a b))
        (iteratedDerivWithin 2 y (Icc a b) s) (Icc a b) s := by
  have h2 : (2 : WithTop ℕ∞) = 1 + 1 := rfl
  rw [h2, contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Icc hlt)] at hy
  refine ⟨fun s hs => (hy.1 s hs).hasDerivWithinAt, fun s hs => ?_⟩
  have := ((hy.2.2.differentiableOn one_ne_zero) s hs).hasDerivWithinAt
  rwa [iteratedDerivWithin_succ, iteratedDerivWithin_one]

/-- Along a solution of the Cauchy problem on `[t₀, t₀ + T]`, `T > 0`, the derivative within the
interval is the field: `derivWithin y [t₀, t₀ + T] s = f(s, y(s))`. -/
theorem derivWithin_eq_of_cauchyProblem (hT : 0 < T)
    (hy : cauchyProblem f t₀ y₀ (Icc t₀ (t₀ + T)) y) {s : ℝ} (hs : s ∈ Icc t₀ (t₀ + T)) :
    derivWithin y (Icc t₀ (t₀ + T)) s = f s (y s) :=
  (hy.2 s hs).derivWithin (uniqueDiffOn_Icc (by linarith) s hs)

/-! ### The increment function and the truncation error -/

/-- **The general explicit one-step method (11.11)**: `u_{n+1} = u_n + h Φ(t_n, u_n, f_n; h)`
for `0 ≤ n`, `u_0 = y_0`; `u` is an orbit of `ODE.OneStep.ofIncrement Φ` from `y₀`. -/
def equation_11_11 (Φ : ODE.OneStep.Increment ℝ) (h t₀ y₀ : ℝ) (u : ℕ → ℝ) : Prop :=
  IsOrbit (ofIncrement Φ) h t₀ u ∧ u 0 = y₀

/-- (11.11), unfolded. -/
theorem equation_11_11_iff (u : ℕ → ℝ) :
    equation_11_11 Φ h t₀ y₀ u ↔
      u 0 = y₀ ∧ ∀ n, u (n + 1) = u n + h * Φ (grid t₀ h n) (u n) (u (n + 1)) h := by
  rw [equation_11_11, isOrbit_ofIncrement_iff, and_comm]
  rfl

/-- For an explicit increment, (11.11) is the iteration `ODE.OneStep.iterate Φ h t₀ y₀`. -/
theorem equation_11_11_iterate (hex : definition_11_3 Φ) (u : ℕ → ℝ) :
    equation_11_11 Φ h t₀ y₀ u ↔ ∀ n, u n = (iterate Φ h t₀ y₀ n).2 := by
  constructor
  · rintro ⟨hu, hu0⟩ n
    rw [eq_iterate_of_isOrbit hex hu n, hu0]
  · intro hu
    have hu' : u = fun n => (iterate Φ h t₀ y₀ n).2 := funext hu
    rw [hu']
    exact ⟨isOrbit_iterate hex y₀, rfl⟩

/-- Forward Euler is the instance `Φ(t_n, u_n, f_n; h) = f_n` of (11.11). -/
theorem equation_11_11_forwardEuler (f : ℝ → ℝ → ℝ) (t u v h : ℝ) :
    equation_11_7 f t u v h = f t u :=
  rfl

/-- Heun's method is the instance `Φ(t_n, u_n, f_n; h) = (f_n + f(t_n + h, u_n + h f_n)) / 2` of
(11.11). -/
theorem equation_11_11_heun (f : ℝ → ℝ → ℝ) (t u v h : ℝ) :
    equation_11_10 f t u v h = 1 / 2 * (f t u + f (t + h) (u + h * f t u)) := by
  simp [equation_11_10, heun]

/-- **The local truncation error (11.12)** `τ_{n+1}(h)` at the node `t_{n+1}`, defined by
`y_{n+1} = y_n + h Φ(t_n, y_n, f(t_n, y_n); h) + h τ_{n+1}(h)` along the exact solution `y`;
`ODE.OneStep.lte` at the node `t_n`. -/
noncomputable def equation_11_12 (Φ : ODE.OneStep.Increment ℝ) (h : ℝ) (y : ℝ → ℝ) (t₀ : ℝ)
    (n : ℕ) : ℝ :=
  lte Φ h y (grid t₀ h n)

/-- (11.12): `y_{n+1} = y_n + h Φ(t_n, y_n, f(t_n, y_n); h) + h τ_{n+1}(h)`. -/
theorem equation_11_12_spec (hh : h ≠ 0) (Φ : ODE.OneStep.Increment ℝ) (y : ℝ → ℝ) (t₀ : ℝ)
    (n : ℕ) :
    y (grid t₀ h (n + 1)) = y (grid t₀ h n) +
      h * Φ (grid t₀ h n) (y (grid t₀ h n)) (y (grid t₀ h (n + 1))) h +
        h * equation_11_12 Φ h y t₀ n := by
  rw [grid, grid, node_succ]
  exact lte_spec hh y _

/-- **The global truncation error** `τ(h) = max_{0 ≤ n ≤ N_h - 1} |τ_{n+1}(h)|`;
`ODE.OneStep.globalLte`. -/
noncomputable def globalTruncationError (Φ : ODE.OneStep.Increment ℝ) (t₀ T : ℝ) (y : ℝ → ℝ)
    (h : ℝ) : ℝ :=
  globalLte Φ t₀ T y h

/-- `τ(h)` is the maximum of the `|τ_{n+1}(h)|` over the `N_h` steps. -/
theorem globalTruncationError_eq (Φ : ODE.OneStep.Increment ℝ) (t₀ T : ℝ) (y : ℝ → ℝ) (h : ℝ) :
    globalTruncationError Φ t₀ T y h = ⨆ n : Fin (gridCount T h), |equation_11_12 Φ h y t₀ n| :=
  rfl

/-- **Consistency** (§11.3): the method is consistent if its local truncation error is
infinitesimal with respect to `h`, `τ(h) → 0` as `h → 0`; `ODE.OneStep.IsConsistentFor` along
the solution `y`. -/
def consistent (Φ : ODE.OneStep.Increment ℝ) (t₀ T : ℝ) (y : ℝ → ℝ) : Prop :=
  IsConsistentFor Φ t₀ T y

/-- Consistency, unfolded: `lim_{h → 0} τ(h) = 0`. -/
theorem consistent_iff :
    consistent Φ t₀ T y ↔ Tendsto (globalTruncationError Φ t₀ T y) (𝓝[>] 0) (𝓝 0) :=
  Iff.rfl

/-- **Order `p` (11.14)**: `τ(h) = O(h^p)` as `h → 0`; `ODE.OneStep.HasOrderFor`. -/
def equation_11_14 (Φ : ODE.OneStep.Increment ℝ) (t₀ T : ℝ) (y : ℝ → ℝ) (p : ℕ) : Prop :=
  HasOrderFor Φ t₀ T y p

/-- (11.14), unfolded. -/
theorem equation_11_14_iff {p : ℕ} :
    equation_11_14 Φ t₀ T y p ↔ globalTruncationError Φ t₀ T y =O[𝓝[>] 0] fun h => h ^ p :=
  Iff.rfl

/-- **The consistency criterion (11.13)**: if `y ∈ C¹` solves the Cauchy problem on
`[t₀, t₀ + T]` for a continuous `f`, and `Φ(t_n, y_n, f(t_n, y_n); h) → f(t_n, y_n)` as `h → 0`,
uniformly in `t_n ∈ [t₀, t₀ + T]`, then the method is consistent;
`ODE.OneStep.isConsistentFor_of_tendsto_increment`. -/
theorem equation_11_13 (hf : ContinuousOn (Function.uncurry f) (Icc t₀ (t₀ + T) ×ˢ univ))
    (hy : cauchyProblem f t₀ y₀ (Icc t₀ (t₀ + T)) y)
    (hΦ : ∀ ε > 0, ∃ η > 0, ∀ h ∈ Ioc 0 η, ∀ t ∈ Icc t₀ (t₀ + T), t + h ∈ Icc t₀ (t₀ + T) →
      |Φ t (y t) (y (t + h)) h - f t (y t)| ≤ ε) :
    consistent Φ t₀ T y :=
  isConsistentFor_of_tendsto_increment hy.2
    (hf.comp (continuousOn_id.prodMk (HasDerivWithinAt.continuousOn hy.2))
      fun _ hs => ⟨hs, mem_univ _⟩) hΦ

/-- **Forward Euler has order one** (§11.3): if `y ∈ C²([t₀, t₀ + T])` solves the Cauchy problem
and `M = max |y''|`, then `|τ_{n+1}(h)| ≤ (M/2) h` for every step of every grid — the book's
`τ_{n+1}(h) = (h/2) y''(ξ)`; `ODE.OneStep.norm_lte_forwardEuler_le`. -/
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

/-- **Forward Euler has order one** (§11.3, (11.14) with `p = 1`) along a `C²` solution;
`ODE.OneStep.hasOrderFor_forwardEuler`. -/
theorem forwardEuler_order_one (hT : 0 < T) (hy : cauchyProblem f t₀ y₀ (Icc t₀ (t₀ + T)) y)
    (hy2 : ContDiffOn ℝ 2 y (Icc t₀ (t₀ + T))) {M : ℝ}
    (hM : ∀ s ∈ Icc t₀ (t₀ + T), |iteratedDerivWithin 2 y (Icc t₀ (t₀ + T)) s| ≤ M) :
    equation_11_14 (equation_11_7 f) t₀ T y 1 :=
  hasOrderFor_of_forall_norm_lte_le (C := M / 2) fun h hh n hn => by
    rw [pow_one, Real.norm_eq_abs]
    exact forwardEuler_order_one_lte hT hy hy2 hM hh hn

/-! ### Zero-stability -/

/-- **Definition 11.4 (zero-stability of one-step methods)**: the method (11.11) is zero-stable
for the Cauchy problem with datum `y₀` on `[t₀, t₀ + T]` if there are `h₀ > 0` and `C > 0` such
that for all `h ∈ (0, h₀]`, `|z_n^{(h)} - u_n^{(h)}| ≤ C ε` for `0 ≤ n ≤ N_h` (11.15), whenever
`z` solves the perturbed recursion (11.16) and `u` the recursion (11.17) with `|δ_k| ≤ ε` for
`0 ≤ k ≤ N_h`; `ODE.OneStep.IsZeroStable`. -/
def definition_11_4 (Φ : ODE.OneStep.Increment ℝ) (t₀ T y₀ : ℝ) : Prop :=
  IsZeroStable (ofIncrement Φ) t₀ T y₀

/-- Definition 11.4 for an explicit increment, in the book's terms: the perturbed recursion
(11.16) is `z_{n+1} = z_n + h (Φ(t_n, z_n, f(t_n, z_n); h) + δ_{n+1})`, `z_0 = y_0 + δ_0`, and the
unperturbed one (11.17) is `u_{n+1} = u_n + h Φ(t_n, u_n, f(t_n, u_n); h)`, `u_0 = y_0`. -/
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

/-- **The Lipschitz hypothesis (11.18) of Theorem 11.1**: the increment function is Lipschitz
continuous with respect to its second argument, with a constant `Λ` independent of `h ∈ (0, h₀]`
and of the nodes `t_j ∈ [t₀, t₀ + T]`; `ODE.OneStep.LipschitzIncrement`. -/
def equation_11_18 (Φ : ODE.OneStep.Increment ℝ) (t₀ T h₀ Λ : ℝ) : Prop :=
  LipschitzIncrement Φ t₀ T h₀ Λ

/-- (11.18) for an explicit increment, in the book's terms. -/
theorem equation_11_18_iff (hex : definition_11_3 Φ) :
    equation_11_18 Φ t₀ T h₀ Λ ↔ ∀ h ∈ Ioc 0 h₀, ∀ t ∈ Icc t₀ (t₀ + T), ∀ u z : ℝ,
      |Φ t u u h - Φ t z z h| ≤ Λ * |u - z| := by
  simp only [equation_11_18, LipschitzIncrement, Real.norm_eq_abs]
  refine forall₂_congr fun h _ => forall₂_congr fun t _ => forall_congr' fun u =>
    forall_congr' fun z => ⟨fun H => H _ _, fun H w w' => ?_⟩
  rw [hex _ _ w u, hex _ _ w' z]
  exact H

/-- **Theorem 11.1 (zero-stability)**: if the increment function `Φ` of the explicit one-step
method (11.11) satisfies (11.18) with constants `h₀ > 0`, `Λ > 0`, then the method is zero-stable
for every datum on the horizon `T ≥ 0`, with `C = (1 + T) e^{ΛT}`;
`ODE.OneStep.isZeroStable_of_lipschitzIncrement`. -/
theorem theorem_11_1 (hT : 0 ≤ T) (hh₀ : 0 < h₀) (hΛ : 0 < Λ) (hlip : equation_11_18 Φ t₀ T h₀ Λ)
    (y₀ : ℝ) : definition_11_4 Φ t₀ T y₀ :=
  isZeroStable_of_lipschitzIncrement hT hh₀ hlip hΛ.le y₀

/-- **The estimate in the proof of Theorem 11.1**: under (11.18), for `h ∈ (0, h₀]` and
perturbations `|δ_k| ≤ ε`, `0 ≤ k ≤ N_h`, the solutions `z` of (11.16) and `u` of (11.17)
satisfy `|w_n^{(h)}| ≤ (1 + h n) ε e^{n h Λ}` for `n ≤ N_h`;
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

/-- **Lemma 11.2 (discrete Gronwall)**: let `k_n` be a nonnegative sequence and `φ_n` a sequence
with `φ_0 ≤ g_0` and `φ_n ≤ g_0 + ∑_{s<n} p_s + ∑_{s<n} k_s φ_s` for `n ≥ 1`. If `g_0 ≥ 0` and
`p_n ≥ 0` for all `n`, then `φ_n ≤ (g_0 + ∑_{s<n} p_s) exp (∑_{s<n} k_s)` for `n ≥ 1`;
`Gronwall.discrete_sum`. -/
theorem lemma_11_2 {φ k p : ℕ → ℝ} {g₀ : ℝ} (hk : ∀ n, 0 ≤ k n) (hφ₀ : φ 0 ≤ g₀)
    (hφ : ∀ n, 1 ≤ n → φ n ≤ g₀ + ∑ s ∈ range n, p s + ∑ s ∈ range n, k s * φ s) (hg₀ : 0 ≤ g₀)
    (hp : ∀ n, 0 ≤ p n) :
    ∀ n, 1 ≤ n → φ n ≤ (g₀ + ∑ s ∈ range n, p s) * Real.exp (∑ s ∈ range n, k s) := fun n _ =>
  Gronwall.discrete_sum hg₀ hk hp (fun m => by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simpa using hφ₀
    · exact hφ m hm) n

/-! ### Convergence -/

/-- **Definition 11.5 (convergence)**: the method `S` is convergent for the Cauchy problem with
datum `y₀` and solution `y` if `|u_n - y_n| ≤ C(h)` for all `n = 0, …, N_h`, where `C(h)` is an
infinitesimal with respect to `h` (for the orbits from `u_0 = y_0` and steps `h ≤ h₀`);
`ODE.OneStep.IsConvergentFor`. -/
def definition_11_5 (S : ODE.OneStep.StepRel ℝ) (t₀ T y₀ : ℝ) (y : ℝ → ℝ) : Prop :=
  IsConvergentFor S t₀ T y₀ y

/-- **Definition 11.5, convergence with order `p`**: `C(h) = 𝒞 h^p` for some `𝒞 > 0`;
`ODE.OneStep.IsConvergentWithOrderFor`. -/
def definition_11_5_order (S : ODE.OneStep.StepRel ℝ) (t₀ T y₀ : ℝ) (y : ℝ → ℝ) (p : ℕ) : Prop :=
  IsConvergentWithOrderFor S t₀ T y₀ y p

/-- Definition 11.5, unfolded. -/
theorem definition_11_5_iff {S : ODE.OneStep.StepRel ℝ} :
    definition_11_5 S t₀ T y₀ y ↔ ∃ C : ℝ → ℝ, Tendsto C (𝓝[>] 0) (𝓝 0) ∧
      ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ h ∈ Ioc 0 h₀, ∀ u : ℕ → ℝ, IsOrbit S h t₀ u → u 0 = y₀ →
        ∀ n ≤ gridCount T h, |u n - y (grid t₀ h n)| ≤ C h := by
  simp only [definition_11_5, IsConvergentFor, Real.norm_eq_abs, grid, gridCount]

/-- Convergence with order `p`, unfolded. -/
theorem definition_11_5_order_iff {S : ODE.OneStep.StepRel ℝ} {p : ℕ} :
    definition_11_5_order S t₀ T y₀ y p ↔ ∃ C : ℝ, 0 < C ∧
      ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ h ∈ Ioc 0 h₀, ∀ u : ℕ → ℝ, IsOrbit S h t₀ u → u 0 = y₀ →
        ∀ n ≤ gridCount T h, |u n - y (grid t₀ h n)| ≤ C * h ^ p := by
  simp only [definition_11_5_order, IsConvergentWithOrderFor, Real.norm_eq_abs, grid, gridCount]

/-- **Theorem 11.2 (convergence), the estimate (11.20)**: under the assumptions of Theorem 11.1,
for `h ∈ (0, h₀]`, an orbit `u` of (11.11) (from any `u_0`) and the solution `y`,
`|y_n - u_n| ≤ (|y_0 - u_0| + n h τ(h)) e^{n h Λ}` for `n ≤ N_h`;
`ODE.OneStep.norm_sub_le_globalLte`. -/
theorem theorem_11_2 (hΛ : 0 < Λ) (hlip : equation_11_18 Φ t₀ T h₀ Λ) (hh : h ∈ Ioc 0 h₀)
    {u : ℕ → ℝ} (hu : IsOrbit (ofIncrement Φ) h t₀ u) (hn : n ≤ gridCount T h) :
    |y (grid t₀ h n) - u n| ≤
      (|y t₀ - u 0| + n * h * globalTruncationError Φ t₀ T y h) * Real.exp (n * h * Λ) := by
  have := norm_sub_le_globalLte hlip hΛ.le hh hu y hn
  rwa [Real.norm_eq_abs, Real.norm_eq_abs] at this

/-- **Theorem 11.2, convergence**: under the assumptions of Theorem 11.1 (`T ≥ 0`), if the
method is consistent along the solution `y` (the consistency assumption (11.13)) and the orbits
start from `u_0 = y_0`, the method is convergent; `ODE.OneStep.isConvergentFor_of_isConsistentFor`.
-/
theorem theorem_11_2_convergent (hT : 0 ≤ T) (hh₀ : 0 < h₀) (hΛ : 0 < Λ)
    (hlip : equation_11_18 Φ t₀ T h₀ Λ) (hcons : consistent Φ t₀ T y) :
    definition_11_5 (ofIncrement Φ) t₀ T (y t₀) y :=
  isConvergentFor_of_isConsistentFor hT hh₀ hlip hΛ.le hcons

/-- **Theorem 11.2, order of convergence**: under the assumptions of Theorem 11.1, a method of
order `p` along `y` is convergent with order `p` from `u_0 = y_0`;
`ODE.OneStep.isConvergentWithOrderFor_of_hasOrderFor`. -/
theorem theorem_11_2_order (hT : 0 ≤ T) (hh₀ : 0 < h₀) (hΛ : 0 < Λ)
    (hlip : equation_11_18 Φ t₀ T h₀ Λ) {p : ℕ} (hord : equation_11_14 Φ t₀ T y p) :
    definition_11_5_order (ofIncrement Φ) t₀ T (y t₀) y p :=
  isConvergentWithOrderFor_of_hasOrderFor hT hh₀ hlip hΛ.le hord

/-- **The forward Euler error bound (11.22)**: if `f` is `L`-Lipschitz in `y` on `[t₀, t₀ + T]`
(`L > 0`), `y ∈ C²([t₀, t₀ + T])` solves the Cauchy problem with `|y''| ≤ M`, and `u` is the
forward Euler sequence with `u_0 = y_0`, then
`|e_{n+1}| = |y_{n+1} - u_{n+1}| ≤ ((e^{L (t_{n+1} - t₀)} - 1) / L) (M / 2) h` for all
`n + 1 ≤ N_h`; `ODE.OneStep.norm_sub_le_forwardEuler`. -/
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

/-- **The test problem (11.24)**: `y'(t) = λ y(t)` for `t > 0`, `y(0) = 1`, with `λ ∈ ℂ`;
its field is `ODE.testField λ`. -/
def testProblem (lam : ℂ) : ℝ → ℂ → ℂ := testField lam

/-- The solution of the test problem is `y(t) = e^{λt}`. -/
theorem testProblem_solution (lam : ℂ) :
    ODE.IsSolutionOn (testProblem lam) 0 1 univ fun t : ℝ => Complex.exp (lam * t) :=
  ⟨by simp, fun t _ => (hasDerivAt_exp_testField lam t).hasDerivWithinAt⟩

/-- `|y(t)| → 0` as `t → +∞` iff `Re λ < 0`. -/
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

/-- **Definition 11.6 (absolute stability)**: a numerical method for approximating the test
problem (11.24) with step `h` is absolutely stable if `|u_n| → 0` as `t_n → +∞` (11.25);
`ODE.OneStep.IsAbsStable` (which also asks that every datum have an orbit, so that the singular
parameters of the implicit methods are excluded rather than vacuously admitted). -/
def definition_11_6 (M : ODE.OneStep.Method ℂ) (lam : ℂ) (h : ℝ) : Prop :=
  IsAbsStable (M (testProblem lam)) h

/-- **The region of absolute stability (11.26)**: `𝒜 = {z = hλ ∈ ℂ : (11.25) is satisfied}`;
`ODE.OneStep.absStabilityRegion`. -/
def equation_11_26 (M : ODE.OneStep.Method ℂ) : Set ℂ := absStabilityRegion M

/-- (11.26), unfolded: `z ∈ 𝒜` iff the method is absolutely stable for every factorization
`z = hλ` with `h > 0`. -/
theorem mem_equation_11_26_iff {M : ODE.OneStep.Method ℂ} {z : ℂ} :
    z ∈ equation_11_26 M ↔ ∀ h : ℝ, 0 < h → definition_11_6 M (z / h) h :=
  Iff.rfl

/-- **Forward Euler on the test problem (11.27)**: `u_n = (1 + hλ)^n`. -/
theorem equation_11_27_orbit {lam : ℂ} {u : ℕ → ℂ}
    (hu : IsOrbit (ofIncrement (forwardEuler (testProblem lam))) h 0 u) (hu0 : u 0 = 1) (n : ℕ) :
    u n = (1 + h * lam) ^ n := by
  rw [forwardEuler_testField_orbit hu n, hu0, mul_one]

/-- **(11.27)**: forward Euler with step `h > 0` is absolutely stable for `y' = λy` iff
`|1 + hλ| < 1`, i.e. iff `hλ ∈ ℂ⁻` and `0 < h < -2 Re(λ) / |λ|²`;
`ODE.OneStep.mem_absStabilityRegion_forwardEuler_iff`,
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

/-- **Example 11.1**: for `y' = -5y`, `y(0) = 1`, condition (11.27) reads `0 < h < 2/5`: forward
Euler with step `h > 0` is absolutely stable iff `h < 2/5`. -/
theorem example_11_1 (hh : 0 < h) :
    definition_11_6 (fun f => ofIncrement (forwardEuler f)) (-5) h ↔ h < 2 / 5 := by
  rw [definition_11_6, testProblem, isAbsStable_forwardEuler_iff hh (by norm_num)]
  norm_num

/-- **Backward Euler on the test problem**: `u_n = 1 / (1 - hλ)^n` (for `hλ ≠ 1`), and the
region of absolute stability is the exterior of the unit circle of centre `(1, 0)`:
`z ∈ 𝒜 ↔ |1 - z| > 1`; `ODE.OneStep.mem_absStabilityRegion_backwardEuler_iff`. -/
theorem backwardEuler_absStabilityRegion :
    (∀ {lam : ℂ} {u : ℕ → ℂ}, (h : ℂ) * lam ≠ 1 →
      IsOrbit (ofIncrement (backwardEuler (testProblem lam))) h 0 u → u 0 = 1 →
        ∀ n, u n = 1 / (1 - h * lam) ^ n) ∧
      ∀ z : ℂ, z ∈ equation_11_26 (fun f => ofIncrement (backwardEuler f)) ↔ 1 < ‖1 - z‖ :=
  ⟨fun hne hu hu0 n => by rw [backwardEuler_testField_orbit hne hu n, hu0, mul_one, inv_pow,
    one_div], fun z => mem_absStabilityRegion_backwardEuler_iff z⟩

/-- **Example 11.2, decay**: backward Euler applied to `y' = 5y`, `y(0) = 1`, computes a solution
that decays to zero for every step `h > 2/5`, although the exact solution `e^{5t}` tends to
infinity: `5h ∈ 𝒜` iff `h > 2/5` (for `h > 0`). -/
theorem example_11_2_decay (hh : 0 < h) :
    ((5 * h : ℝ) : ℂ) ∈ equation_11_26 (fun f => ofIncrement (backwardEuler f)) ↔ 2 / 5 < h := by
  rw [equation_11_26, mem_absStabilityRegion_backwardEuler_iff, ← Complex.ofReal_one,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, lt_abs]
  constructor
  · rintro (H | H) <;> linarith
  · intro H; right; linarith

/-- **Example 11.2, no oscillation**: backward Euler applied to `y' = -5y`, `y(0) = 1`, gives
`u_n = (1 + 5h)^{-n}`, a positive decreasing sequence for every `h > 0`. -/
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

/-- **Example 11.2**: backward Euler applied to `y' = -5y`, `y(0) = 1`, produces no oscillation
for any `h > 0` (its solution `(1 + 5h)^{-n}` is positive and decreasing), while applied to
`y' = 5y`, `y(0) = 1`, it computes a solution decaying to zero for every `h > 2/5`, although the
exact solution tends to infinity. -/
theorem example_11_2 (hh : 0 < h) :
    (((5 * h : ℝ) : ℂ) ∈ equation_11_26 (fun f => ofIncrement (backwardEuler f)) ↔ 2 / 5 < h) ∧
      ∀ u : ℕ → ℂ, IsOrbit (ofIncrement (backwardEuler (testProblem (-5)))) h 0 u → u 0 = 1 →
        (∀ n, u n = (((1 + 5 * h)⁻¹ ^ n : ℝ) : ℂ)) ∧ (∀ n, 0 < (1 + 5 * h)⁻¹ ^ n) ∧
          Antitone fun n : ℕ => (1 + 5 * h)⁻¹ ^ n :=
  ⟨example_11_2_decay hh, fun _ hu hu0 => example_11_2_no_oscillation hh hu hu0⟩

/-- **Crank–Nicolson on the test problem**: `u_n = ((1 + hλ/2) / (1 - hλ/2))^n` (for `hλ ≠ 2`),
and (11.25) holds for every `hλ ∈ ℂ⁻`: the region of absolute stability is the left half-plane;
`ODE.OneStep.mem_absStabilityRegion_crankNicolson_iff`. -/
theorem crankNicolson_absStabilityRegion :
    (∀ {lam : ℂ} {u : ℕ → ℂ}, (h : ℂ) * lam ≠ 2 →
      IsOrbit (ofIncrement (crankNicolson (testProblem lam))) h 0 u → u 0 = 1 →
        ∀ n, u n = ((1 + 1 / 2 * lam * h) / (1 - 1 / 2 * lam * h)) ^ n) ∧
      ∀ z : ℂ, z ∈ equation_11_26 (fun f => ofIncrement (crankNicolson f)) ↔ z.re < 0 :=
  ⟨fun hne hu hu0 n => by
    rw [crankNicolson_testField_orbit hne hu n, hu0, mul_one]
    ring_nf, fun z => mem_absStabilityRegion_crankNicolson_iff z⟩

/-- **Heun's method on the test problem**: `u_n = (1 + hλ + (hλ)²/2)^n`, the region of absolute
stability is `{z : |1 + z + z²/2| < 1}`, and its restriction to the real axis is the interval
`(-2, 0)`, the same as forward Euler's; `ODE.OneStep.mem_absStabilityRegion_heun_iff`. -/
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

/-- **A-stability** (§11.3.3): a method is A-stable if `𝒜 ∩ ℂ⁻ = ℂ⁻`, i.e. if for `Re(λ) < 0`
condition (11.25) is satisfied for all values of `h`; `ODE.OneStep.IsAStable`. -/
def aStable (M : ODE.OneStep.Method ℂ) : Prop := IsAStable M

/-- A-stability, as the book writes it: `𝒜 ∩ ℂ⁻ = ℂ⁻`. -/
theorem aStable_iff {M : ODE.OneStep.Method ℂ} :
    aStable M ↔ equation_11_26 M ∩ {z : ℂ | z.re < 0} = {z : ℂ | z.re < 0} := by
  rw [aStable, IsAStable, inter_eq_right]
  rfl

/-- Backward Euler is A-stable. -/
theorem aStable_backwardEuler : aStable fun f => ofIncrement (backwardEuler f) :=
  isAStable_backwardEuler

/-- Crank–Nicolson is A-stable. -/
theorem aStable_crankNicolson : aStable fun f => ofIncrement (crankNicolson f) :=
  isAStable_crankNicolson

/-- Forward Euler is only conditionally stable: it is not A-stable. -/
theorem not_aStable_forwardEuler : ¬ aStable fun f => ofIncrement (forwardEuler f) :=
  not_isAStable_forwardEuler

/-- Heun's method is only conditionally stable: it is not A-stable. -/
theorem not_aStable_heun : ¬ aStable fun f => ofIncrement (heun f) :=
  not_isAStable_heun

/-- **Remark 11.2** ("there are no explicit unconditionally absolutely stable schemes"), for
the explicit one-step schemes of the book's own general form, the explicit Runge–Kutta methods of
§11.8: an explicit consistent Butcher tableau is never A-stable, and its region of absolute
stability is bounded; `ODE.ButcherTableau.not_isAStable_of_isExplicit`. The remark for arbitrary
explicit one-step schemes (Widlund's theorem) is not formalized. -/
theorem remark_11_2 {s : ℕ} (tab : ODE.ButcherTableau s) (hex : tab.IsExplicit)
    (hb : ∑ i, tab.b i = 1) :
    ¬ aStable tab.stepRel ∧ Bornology.IsBounded (equation_11_26 tab.stepRel) :=
  ⟨tab.not_isAStable_of_isExplicit hex hb, tab.isBounded_absStabilityRegion hex hb⟩

end QuarteroniSaccoSaleri.Chapter11
