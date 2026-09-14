import Numlib.ODE.RungeKutta
import NumlibSurface.QuarteroniSaccoSaleri.Chapter11.Section03

/-!
# Quarteroni–Sacco–Saleri §11.8: Runge–Kutta methods

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*,
Springer, 2000, §11.8.

The general `s`-stage Runge–Kutta method (11.70)–(11.71) with its Butcher array, the row-sum
condition (11.72), explicit, semi-implicit and implicit methods; the local truncation error, the
consistency condition `∑ b_i = 1`, zero-stability and convergence of the explicit methods; the
classical method (11.73); the two-stage order conditions of §11.8.1; embedded pairs (11.76) and
the Runge–Kutta–Fehlberg pair (§11.8.2); the implicit families of §11.8.3; the stability function
(11.77) and the regions of absolute stability (§11.8.4).

Everything is the scalar case `E = ℝ` of `Numlib/ODE/RungeKutta` (the test problem on `ℂ`), with
the one-step theory of §11.3. Butcher's order barriers (Property 11.4), the order four of the
classical method (`ODE.rk4_hasOrderFor`, open in the backbone), Remarks 11.4–11.5, the
step-doubling estimates (11.74)–(11.75) and the maximal orders of the implicit families are not
formalized.

## Main definitions

* `equation_11_71 tab f h t₀ u`, `equation_11_70_increment tab f` — the orbits of an RK method
  and the increment of an explicit one.
* `equation_11_72 tab`, `equation_11_71_explicit tab`, `equation_11_71_semiImplicit tab`,
  `implicitRungeKutta tab` — the row-sum condition and the shapes of tableaux.
* `rungeKutta_lte tab f h y t₀ n` — the local truncation error.
* `equation_11_73` — the classical method.
* `equation_11_76 s`, `equation_11_76_errorIndicator P f h t u`, `rkf45` — embedded pairs.
* `stabilityFunction tab z` — the stability function `R`.

## Main results

* `rungeKutta_consistent_iff`, `rungeKutta_convergent` — consistency and convergence.
* `equation_11_73_step`, `twoStageOrderConditions` — the classical method and the two-stage
  order conditions.
* `gaussLegendre_tableaux`, `radau_tableaux`, `lobatto_tableaux`, `dirk_tableau` — §11.8.3.
* `equation_11_77`, `rungeKutta_absStable_iff`, `rungeKutta_explicit_stabilityFunction` —
  absolute stability.

## Conventions

A method is a Butcher array `tab : ODE.ButcherTableau s` with `A = tab.A`, `b = tab.b`,
`c = tab.c`; its step relation `tab.stepRel f` is a `OneStep.Method`, so Definitions 11.4–11.6 of
§11.3 apply verbatim. The explicit methods are handled through their increment function
`tab.explicitIncrement f` (11.70). The nodes are assumed to lie in `[0, 1]` wherever the field is
only controlled on the horizon.
-/

open Set Filter Topology Asymptotics Matrix ODE ODE.OneStep
open Finset (range)

namespace QuarteroniSaccoSaleri.Chapter11

variable {f : ℝ → ℝ → ℝ} {t₀ T h h₀ t y₀ : ℝ} {y : ℝ → ℝ} {n s : ℕ}

/-! ### (11.70)–(11.72): the method, its Butcher array and the row-sum condition -/

/-- **The `s`-stage Runge–Kutta method (11.70)–(11.71)**: `u_{n+1} = u_n + h F(t_n, u_n, h; f)`
with `F = ∑_{i=1}^s b_i K_i` and the stages `K_i = f(t_n + c_i h, u_n + h ∑_{j=1}^s a_ij K_j)`,
for the Butcher array `(A, b, c)`, `tab : ODE.ButcherTableau s`; `u` is an orbit of the step
relation `tab.stepRel f`. -/
def equation_11_71 (tab : ButcherTableau s) (f : ℝ → ℝ → ℝ) (h t₀ : ℝ) (u : ℕ → ℝ) : Prop :=
  IsOrbit (tab.stepRel f) h t₀ u

/-- (11.70)–(11.71), unfolded: at every step there are stages `K` with
`K_i = f(t_n + c_i h, u_n + h ∑_j a_ij K_j)` and `u_{n+1} = u_n + h ∑_i b_i K_i`. -/
theorem equation_11_71_iff (tab : ButcherTableau s) (u : ℕ → ℝ) :
    equation_11_71 tab f h t₀ u ↔ ∀ n, ∃ K : Fin s → ℝ,
      (∀ i, K i = f (grid t₀ h n + tab.c i * h) (u n + h * ∑ j, tab.A i j * K j)) ∧
        u (n + 1) = u n + h * ∑ i, tab.b i * K i := by
  rw [equation_11_71, isOrbit_iff]
  simp only [ButcherTableau.stepRel_apply, ButcherTableau.IsStages, smul_eq_mul, grid]

/-- **The row-sum condition (11.72)** `c_i = ∑_{j=1}^s a_ij`, assumed throughout §11.8;
`ODE.ButcherTableau.IsRowSum`. -/
def equation_11_72 (tab : ButcherTableau s) : Prop :=
  tab.IsRowSum

/-- (11.72), unfolded. -/
theorem equation_11_72_iff (tab : ButcherTableau s) :
    equation_11_72 tab ↔ ∀ i, tab.c i = ∑ j, tab.A i j :=
  Iff.rfl

/-- **Explicit methods**: `a_ij = 0` for `j ≥ i`, so that each `K_i` is computed from the
previous stages; `ODE.ButcherTableau.IsExplicit`. -/
def equation_11_71_explicit (tab : ButcherTableau s) : Prop :=
  tab.IsExplicit

/-- **Semi-implicit methods**: `a_ij = 0` for `j > i`, so that each `K_i` solves one equation in
itself; `ODE.ButcherTableau.IsSemiImplicit`. -/
def equation_11_71_semiImplicit (tab : ButcherTableau s) : Prop :=
  tab.IsSemiImplicit

/-- **Implicit methods**: the tableaux that are not explicit (§11.8, §11.8.3). -/
def implicitRungeKutta (tab : ButcherTableau s) : Prop :=
  ¬ tab.IsExplicit

/-- The shapes, unfolded; an explicit method is semi-implicit. -/
theorem equation_11_71_shapes (tab : ButcherTableau s) :
    (equation_11_71_explicit tab ↔ ∀ i j : Fin s, i ≤ j → tab.A i j = 0) ∧
    (equation_11_71_semiImplicit tab ↔ ∀ i j : Fin s, i < j → tab.A i j = 0) ∧
    (implicitRungeKutta tab ↔ ¬ ∀ i j : Fin s, i ≤ j → tab.A i j = 0) ∧
    (equation_11_71_explicit tab → equation_11_71_semiImplicit tab) :=
  ⟨Iff.rfl, Iff.rfl, Iff.rfl, fun hex => hex.isSemiImplicit⟩

/-- **The increment function (11.70) of an explicit method**, `F(t, u, h; f) = ∑_i b_i K_i` with
the explicitly computed stages; `ODE.ButcherTableau.explicitIncrement`. -/
noncomputable def equation_11_70_increment (tab : ButcherTableau s) (f : ℝ → ℝ → ℝ) :
    OneStep.Increment ℝ :=
  tab.explicitIncrement f

/-- For an explicit tableau, (11.71) is the one-step method (11.11) with the increment (11.70),
and the stages are `K_i = f(t_n + c_i h, u_n + h ∑_{j<i} a_ij K_j)`. -/
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

/-- **The local truncation error of an explicit RK method**,
`h τ_{n+1}(h) = y_{n+1} - y_n - h F(t_n, y_n, h; f)`: (11.12) for the increment (11.70). -/
noncomputable def rungeKutta_lte (tab : ButcherTableau s) (f : ℝ → ℝ → ℝ) (h : ℝ) (y : ℝ → ℝ)
    (t₀ : ℝ) (n : ℕ) : ℝ :=
  equation_11_12 (equation_11_70_increment tab f) h y t₀ n

/-- The local truncation error, unfolded. -/
theorem rungeKutta_lte_spec (hh : h ≠ 0) (tab : ButcherTableau s) (y : ℝ → ℝ) (t₀ : ℝ) (n : ℕ) :
    y (grid t₀ h (n + 1)) = y (grid t₀ h n) +
      h * ∑ i, tab.b i * tab.explicitStages f h (grid t₀ h n) (y (grid t₀ h n)) i +
        h * rungeKutta_lte tab f h y t₀ n :=
  equation_11_12_spec hh (equation_11_70_increment tab f) y t₀ n

/-- **Consistency of an explicit RK method** (§11.8): with nodes in `[0, 1]`, the method is
consistent — `τ(h) → 0` along the solution of every Cauchy problem with `f` continuous and
Lipschitz in `y` (on a slightly larger horizon, where the stages are evaluated) — iff
`∑_{i=1}^s b_i = 1`; `ODE.ButcherTableau.isConsistentFor_of_sum_b_eq_one`,
`ODE.ButcherTableau.sum_b_eq_one_of_isConsistentFor`. The book cites [Lam91]. Order `p` along a
solution is `τ(h) = O(h^p)`, (11.14) for the increment (11.70). -/
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

/-- **"Since RK methods are one-step methods, consistency implies stability and, in turn,
convergence"** (§11.8): an explicit RK method with nodes in `[0, 1]` applied to a problem whose
field is Lipschitz in `y` on `[t₀, t₀ + T + h₀]` has a Lipschitz increment, hence is zero-stable
(Theorem 11.1, Definition 11.4) for every datum; if it is consistent along the solution `y` it is
convergent (Theorem 11.2, Definition 11.5) from `u_0 = y(t₀)`, and if it has order `p` along `y`
it converges with order `p`; `ODE.ButcherTableau.lipschitzIncrement_explicit`,
`ODE.ButcherTableau.isZeroStable_explicit`, `ODE.ButcherTableau.isConvergentFor_explicit`. -/
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

/-- **The classical explicit four-stage method of order four (11.73)**,
`u_{n+1} = u_n + (h/6)(K₁ + 2K₂ + 2K₃ + K₄)`, `K₁ = f_n`, `K₂ = f(t_n + h/2, u_n + (h/2)K₁)`,
`K₃ = f(t_n + h/2, u_n + (h/2)K₂)`, `K₄ = f(t_{n+1}, u_n + hK₃)`; `ODE.rk4`. Its order four
(`equation_11_73_order`) rests on `ODE.rk4_hasOrderFor`, open in the backbone. -/
noncomputable def equation_11_73 : ButcherTableau 4 :=
  rk4

/-- (11.73), written out: the Butcher array, and the step of the method. -/
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

/-- A `C³` function on `[a, b]`, `a < b`, has the derivatives `y'`, `y''`, `y'''` within `[a, b]`
given by `derivWithin` and `iteratedDerivWithin`; the three-level form of
`hasDerivWithinAt_derivWithin_of_contDiffOn_two`. -/
theorem hasDerivWithinAt_iteratedDerivWithin_of_contDiffOn_three {a b : ℝ} (hlt : a < b)
    {y : ℝ → ℝ} (hy : ContDiffOn ℝ 3 y (Icc a b)) :
    (∀ s ∈ Icc a b, HasDerivWithinAt y (derivWithin y (Icc a b) s) (Icc a b) s) ∧
    (∀ s ∈ Icc a b, HasDerivWithinAt (derivWithin y (Icc a b))
      (iteratedDerivWithin 2 y (Icc a b) s) (Icc a b) s) ∧
    ∀ s ∈ Icc a b, HasDerivWithinAt (iteratedDerivWithin 2 y (Icc a b))
      (iteratedDerivWithin 3 y (Icc a b) s) (Icc a b) s := by
  have h3 : (3 : WithTop ℕ∞) = 2 + 1 := rfl
  rw [h3, contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Icc hlt)] at hy
  obtain ⟨h1, h2⟩ := hasDerivWithinAt_derivWithin_of_contDiffOn_two hlt hy.2.2
  refine ⟨fun s hs => (hy.1 s hs).hasDerivWithinAt, fun s hs => ?_, fun s hs => ?_⟩
  · have := h1 s hs
    rwa [show iteratedDerivWithin 2 y (Icc a b) = derivWithin (derivWithin y (Icc a b)) (Icc a b)
      by rw [iteratedDerivWithin_succ, iteratedDerivWithin_one]]
  · have := h2 s hs
    rwa [show iteratedDerivWithin 2 y (Icc a b) = derivWithin (derivWithin y (Icc a b)) (Icc a b)
      by rw [iteratedDerivWithin_succ, iteratedDerivWithin_one],
      show iteratedDerivWithin 3 y (Icc a b) =
        iteratedDerivWithin 2 (derivWithin y (Icc a b)) (Icc a b) from
        iteratedDerivWithin_succ']

/-- **The two-stage order conditions (§11.8.1)**: a two-stage explicit RK method satisfying
(11.72) has order two iff `b₁ + b₂ = 1` and `c₂ b₂ = 1/2`. The necessity is read on the test
problems `y' = 1` and `y' = 2t` (`ODE.ButcherTableau.orderTwoConditions_of_hasOrderFor`); the
sufficiency holds along every `C³` solution of a problem whose field is `C²` with bounded second
derivative (`ODE.ButcherTableau.hasOrderFor_two_of`, the book's Taylor expansions of `K₂` and
`y_{n+1}`). Heun's method (`ODE.ButcherTableau.heun`) and the modified Euler method
(`ODE.ButcherTableau.modifiedEuler`) satisfy them. -/
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

/-! ### §11.8.2: embedded pairs -/

/-- **An embedded pair (11.76)**: two RK methods of orders `p` and `p + 1` sharing `A`, `c` and
the stages, with weights `b` and `b̂`; `ODE.EmbeddedPair s`. -/
abbrev equation_11_76 (s : ℕ) := EmbeddedPair s

/-- **The error indicator of an embedded pair**, `h ∑_i E_i K_i` with `E = b - b̂`: the difference
of the two solutions, which estimates the local error of the lower-order method without extra
evaluations of `f`; `ODE.EmbeddedPair.errorIndicator`. -/
noncomputable def equation_11_76_errorIndicator (P : equation_11_76 s) (f : ℝ → ℝ → ℝ) (h t u : ℝ) :
    ℝ :=
  P.errorIndicator f h t u

/-- The error indicator is `u_{n+1} - û_{n+1}`, the difference of the two steps of the pair from
`(t_n, u_n)`; `ODE.EmbeddedPair.errorIndicator_eq_sub`. -/
theorem equation_11_76_errorIndicator_eq (P : equation_11_76 s) (f : ℝ → ℝ → ℝ) (h t u : ℝ) :
    equation_11_76_errorIndicator P f h t u = h * ∑ i, (P.b i - P.bhat i) *
        P.toButcherTableau.explicitStages f h t u i ∧
      equation_11_76_errorIndicator P f h t u =
        (u + h * equation_11_70_increment P.toButcherTableau f t u u h) -
          (u + h * equation_11_70_increment P.toTableauHat f t u u h) :=
  ⟨rfl, P.errorIndicator_eq_sub f h t u⟩

/-- **The Runge–Kutta–Fehlberg 4(5) pair (§11.8.2)** with the standard coefficients (the book's
table is damaged in the source): `b` is the fourth-order method, `b̂` the fifth-order one;
`ODE.rkf45`. -/
noncomputable def rkf45 : equation_11_76 6 :=
  ODE.rkf45

/-- The Fehlberg pair: explicit, satisfying (11.72), with both weight vectors summing to `1`, and
the error coefficients `b̂ - b = (1/360, 0, -128/4275, -2197/75240, 1/50, 2/55)` (the book writes
`E = b - b̂` for the same numbers). -/
theorem rkf45_spec :
    equation_11_71_explicit rkf45.toButcherTableau ∧ equation_11_72 rkf45.toButcherTableau ∧
    (∑ i, rkf45.b i = 1 ∧ ∑ i, rkf45.bhat i = 1) ∧
    (fun i => rkf45.bhat i - rkf45.b i) =
      ![1 / 360, 0, -128 / 4275, -2197 / 75240, 1 / 50, 2 / 55] :=
  ⟨rkf45_isExplicit, rkf45_isRowSum, rkf45_sum_b, rkf45_bhat_sub_b⟩

/-! ### §11.8.3: implicit methods -/

/-- **The Gauss–Legendre methods (§11.8.3)**: the one-stage method is the implicit midpoint rule
`u_{n+1} = u_n + h f(t_n + h/2, (u_n + u_{n+1})/2)` (order two:
`∑ b = 1`, `∑ b c = 1/2`), and the two-stage method of order four has
`c = (1/2 ∓ √3/6)`, `A = !![1/4, 1/4 - √3/6; 1/4 + √3/6, 1/4]`, `b = (1/2, 1/2)`, the nodes being
the roots of the Legendre polynomial `L₂` in `x = 2c - 1`, with the collocation identities
`∑_j c_j^{k-1} a_ij = c_i^k / k`, `∑_j c_j^{k-1} b_j = 1/k`, `k = 1, 2`;
`ODE.ButcherTableau.implicitMidpoint`, `ODE.ButcherTableau.gaussLegendre2`. The maximal order
`2s` is quoted by the book without proof and is not formalized. -/
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

/-- **The Radau methods (§11.8.3)**: the one-stage Radau IIA tableau `A = (1)`, `b = (1)`,
`c = (1)` is backward Euler (11.8), and the two-stage tableau of order three is
`c = (1/3, 1)`, `A = !![5/12, -1/12; 3/4, 1/4]`, `b = (3/4, 1/4)`;
`ODE.ButcherTableau.radauIIA1`, `ODE.ButcherTableau.radauIIA2`. The maximal order `2s - 1` is
not formalized. -/
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

/-- **The Lobatto methods (§11.8.3)**: the two-stage Lobatto IIIA tableau `c = (0, 1)`,
`A = !![0, 0; 1/2, 1/2]`, `b = (1/2, 1/2)` is Crank–Nicolson (11.9);
`ODE.ButcherTableau.lobattoIIIA2`. The maximal order `2s - 2` is not formalized. -/
theorem lobatto_tableaux :
    ButcherTableau.lobattoIIIA2.stepRel f = OneStep.ofIncrement (equation_11_9 f) ∧
    ButcherTableau.lobattoIIIA2.c = ![0, 1] ∧
    ButcherTableau.lobattoIIIA2.A = !![0, 0; 1 / 2, 1 / 2] ∧
    ButcherTableau.lobattoIIIA2.b = ![1 / 2, 1 / 2] ∧
    implicitRungeKutta ButcherTableau.lobattoIIIA2 := by
  refine ⟨ButcherTableau.stepRel_lobattoIIIA2 f, rfl, rfl, rfl, fun hex => ?_⟩
  have := hex 1 1 le_rfl
  simp [ButcherTableau.lobattoIIIA2] at this

/-- **The three-stage DIRK method (§11.8.3)** with `μ` a root of `3μ³ - 3μ - 1 = 0`:
`c = ((1+μ)/2, 1/2, (1-μ)/2)`, `A = !![(1+μ)/2, 0, 0; -μ/2, (1+μ)/2, 0; 1+μ, -1-2μ, (1+μ)/2]`,
`b = (1/(6μ²), 1 - 1/(3μ²), 1/(6μ²))`, a semi-implicit tableau; `ODE.ButcherTableau.dirk3`. Its
order four is not formalized. -/
theorem dirk_tableau (μ : ℝ) :
    (ButcherTableau.dirk3 μ).c = ![(1 + μ) / 2, 1 / 2, (1 - μ) / 2] ∧
    (ButcherTableau.dirk3 μ).A =
      !![(1 + μ) / 2, 0, 0; -μ / 2, (1 + μ) / 2, 0; 1 + μ, -1 - 2 * μ, (1 + μ) / 2] ∧
    (ButcherTableau.dirk3 μ).b = ![1 / (6 * μ ^ 2), 1 - 1 / (3 * μ ^ 2), 1 / (6 * μ ^ 2)] ∧
    equation_11_71_semiImplicit (ButcherTableau.dirk3 μ) :=
  ⟨rfl, rfl, rfl, ButcherTableau.dirk3_isSemiImplicit μ⟩

/-! ### §11.8.4: the stability function and absolute stability -/

/-- **The stability function** `R(z) = 1 + z bᵀ (I - zA)⁻¹ 𝟙` of a Runge–Kutta method;
`ODE.ButcherTableau.stabilityFunction`. -/
noncomputable def stabilityFunction (tab : ButcherTableau s) (z : ℂ) : ℂ :=
  tab.stabilityFunction z

/-- **(11.77), the method on the test problem**: the stages of the method on `y' = λy` at `u_n`
satisfy `(I - hλ A) K = λ u_n 𝟙`, and when `I - hλA` is invertible the step is
`u_{n+1} = R(hλ) u_n` with `R(z) = 1 + z bᵀ (I - zA)⁻¹ 𝟙`;
`ODE.ButcherTableau.isStages_testField_iff`, `ODE.ButcherTableau.stepRel_testField_iff`. -/
theorem equation_11_77 (tab : ButcherTableau s) (lam : ℂ) :
    (∀ (t : ℝ) (u : ℂ) (K : Fin s → ℂ), tab.IsStages (testProblem lam) h t u K ↔
      (1 - ((h : ℂ) * lam) • tab.complexA) *ᵥ K = (lam * u) • fun _ => (1 : ℂ)) ∧
    (IsUnit (1 - ((h : ℂ) * lam) • tab.complexA) → ∀ (t : ℝ) (u v : ℂ),
      tab.stepRel (testProblem lam) h t u v ↔ v = stabilityFunction tab (h * lam) * u) ∧
    ∀ z : ℂ, stabilityFunction tab z =
      1 + z * (tab.complexB ⬝ᵥ ((1 - z • tab.complexA)⁻¹ *ᵥ fun _ => 1)) :=
  ⟨fun _ _ K => tab.isStages_testField_iff K,
    fun hinv t u v => tab.stepRel_testField_iff hinv t u v, fun _ => rfl⟩

/-- **Absolute stability of Runge–Kutta methods (§11.8.4)**: when `I - hλA` is invertible, the
method with step `h > 0` is absolutely stable for `y' = λy` iff `|R(hλ)| < 1`, and its region of
absolute stability is `𝒜 = {z : |R(z)| < 1}` on the set where `I - zA` is invertible — an
invertibility clause the book omits, which is genuinely needed (see the backbone); for an
explicit method it is automatic; `ODE.ButcherTableau.mem_absStabilityRegion_iff_of_isUnit`,
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

/-- **Explicit methods (§11.8.4)**: `R(z) = det(I - zA + z 𝟙 bᵀ) / det(I - zA)` with
`det(I - zA) = 1`, so `R` is a polynomial in `z` (of degree at most `s`) and `𝒜` can never be
unbounded: a consistent explicit method has a bounded region and is not A-stable; for an
explicit `s`-stage method of order `s` (along `y' = y` on `[0, 1]`), `R(z) = ∑_{k=0}^s z^k / k!`
— the book states this for `s = 1, …, 4`, where such methods exist — and in particular
`R_{rk4}(z) = 1 + z + z²/2 + z³/6 + z⁴/24`;
`ODE.ButcherTableau.stabilityFunction_eq_det_of_isExplicit`,
`ODE.ButcherTableau.det_one_sub_smul_complexA`, `ODE.ButcherTableau.isBounded_absStabilityRegion`,
`ODE.ButcherTableau.not_isAStable_of_isExplicit`,
`ODE.ButcherTableau.stabilityFunction_eq_truncExp_of_hasOrder`, `ODE.stabilityFunction_rk4`. -/
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

end QuarteroniSaccoSaleri.Chapter11
