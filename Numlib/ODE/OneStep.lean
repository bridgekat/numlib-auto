import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecificLimits.Normed
import Numlib.ODE.Gronwall

/-!
# One-step methods for the Cauchy problem

One-step methods for `y' = f(t, y)`, `y(t₀) = y₀`, on a real normed space `E`
([quarteroni2000numerical] §11.2–11.3; [kress1998numerical] §10.2 states the same theory).

**The grid.** `ODE.node t₀ h n = t₀ + n h` and `ODE.gridCount T h = ⌊T / h⌋₊`, the books' `t_n` and
`N_h`, the largest `n` with `t_n ≤ t₀ + T`.

**Methods.** An *increment function* `Φ : ℝ → E → E → ℝ → E`, `Φ t u v h`, defines the method
`u_{n+1} = u_n + h Φ(t_n, u_n, u_{n+1}; h)`; it is *explicit* when it ignores `v`
(`OneStep.IsExplicit`). The books' `Φ(t_n, u_n, f_n; h)` carries `f_n = f(t_n, u_n)` as a separate
argument; here `f` is baked into `Φ` (`forwardEuler f`, `heun f`, …), which is the same
information. Behind the increment functions sits the *step relation* `S h t u v : Prop` ("`v` is
admissible at `t + h` from `u` at `t`"), `OneStep.ofIncrement Φ h t u v ↔ v = u + h • Φ t u v h`,
because an implicit method's step is the solution of an equation that may have none or several,
and because implicit Runge–Kutta methods are relations by nature. A `Method` is a rule
`(ℝ → E → E) → StepRel E` from the field to the relation. The explicit `step`/`iterate` on states
`(t, u)` is the function form of an explicit method, connected to the relational orbit by
`OneStep.isOrbit_iterate` and `OneStep.eq_iterate_of_isOrbit`.

**Orbits.** `IsOrbitWith S h t₀ δ z` is the perturbed recursion
`S h t_n (z n) (z (n+1) - h δ_{n+1})` of [quarteroni2000numerical] (11.16), and
`IsOrbit S h t₀ u = IsOrbitWith S h t₀ 0 u` the unperturbed one, (11.11)/(11.17).

**Truncation error.** `lte Φ h y t = (y (t + h) - y t) / h - Φ t (y t) (y (t + h)) h` is the local
truncation error `τ_{n+1}(h)` of (11.12) at `t = t_n`, `globalLte Φ t₀ T y h = ⨆_{n < N_h} ‖lte …‖`
is `τ(h)`; consistency along `y` is `τ(h) → 0` along `𝓝[>] 0`, order `p` is `τ(h) = O(h^p)`. These
are properties of the pair (method, curve): the curve is the solution of the Cauchy problem in
every use, but nothing here needs it to be.

**Zero-stability and convergence.** `IsZeroStable S t₀ T y₀` is Definition 11.4 of
[quarteroni2000numerical] verbatim; `LipschitzIncrement Φ t₀ T h₀ Λ` is its hypothesis (11.18),
Lipschitz continuity in the second argument uniformly in the time, the step and the third
argument. The one estimate behind Theorems 11.1 and 11.2 is
`norm_sub_le_of_lipschitzIncrement_of_succ_eq`: two recursions driven by the same increment,
one of them perturbed by `h δ_{n+1}`, differ by at most `(‖z₀ - u₀‖ + n h ε) e^{n h Λ}`, by the
discrete Gronwall lemma (`Gronwall.discrete_sum_const_of_le`). Theorem 11.1 is the case of two
orbits; Theorem 11.2 is the case where the perturbed recursion is the exact solution, whose
perturbations are its local truncation errors (`lte_spec`), and gives (11.20), convergence
(Definition 11.5, `IsConvergentFor`, with the step-size threshold `h₀` that (11.18) forces) and
convergence with order `p`.

**The elementary methods** forward Euler, backward Euler, Crank–Nicolson, Heun and the θ-method
`theta f θ` that contains the first three, their Lipschitz constants in terms of that of `f`, and
their local truncation errors from the Taylor bounds `norm_sub_sub_smul_le_mul_sq_div_two` and
`norm_sub_sub_smul_add_le_mul_pow_three_div_twelve` (stated for explicit derivative functions on
a closed interval, which is weaker than `C²`/`C³` regularity and is what the mean value
inequality needs): the Euler methods have order 1 with constant `M₂ / 2`, Crank–Nicolson order 2
with `M₃ / 12` ([quarteroni2000numerical] Exercise 11.2), Heun order 2 (Exercise 11.1), the
θ-method order 1 with `|θ - 1/2| M₂` plus the Crank–Nicolson term.

**Absolute stability** (§11.3.3). The test equation `testField λ = fun _ y => λ * y` on `ℂ`;
`IsAbsStable S h` says every initial value has an orbit and every orbit tends to zero
(Definition 11.6; the existence clause excludes the singular parameters of the implicit methods,
where the only orbit is `0`). The region of absolute stability (11.26) is
`absStabilityRegion M = {z | ∀ h > 0, IsAbsStable (M (testField (z / h))) h}`, the set of `z`
all of whose factorizations `z = hλ` are absolutely stable, which is the honest reading of "the
set of `hλ` for which (11.25) holds" for a method that might not depend on `hλ` alone; for the
methods of this file it coincides with the `h = 1` slice
(`absStabilityRegion_eq_of_scaleInvariant`).
`IsAStable M` is `{z | z.re < 0} ⊆ absStabilityRegion M`. The four regions: `‖1 + z‖ < 1`,
`‖1 - z‖ > 1`, `Re z < 0`, `‖1 + z + z²/2‖ < 1`; backward Euler and Crank–Nicolson are A-stable,
forward Euler and Heun are not.
-/

open Set Filter Topology Asymptotics
open Finset (range)

/-! ### Taylor bounds with explicit derivatives on a closed interval

Second- and third-order Taylor remainder bounds for a curve `y : ℝ → E` on `Icc a b` given by
*derivative functions* `y'`, `y''`, `y'''` with `HasDerivWithinAt … (Icc a b)`, rather than by a
`ContDiffOn` hypothesis and `iteratedDerivWithin`. They are what the truncation-error estimates
of one-step methods need and are proved by the comparison lemma
`image_norm_le_of_norm_deriv_right_le_deriv_boundary`. They are Mathlib-shaped and belong in a
calculus module; they live here until one exists. -/

section Taylor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {a b M : ℝ} {y y' y'' y''' : ℝ → E}

/-- Reflecting a curve with derivative `y'` on `Icc a b` through the midpoint gives a curve with
derivative `-y' (a + b - s)` on `Icc a b`. -/
theorem hasDerivWithinAt_comp_const_sub_Icc
    (hy : ∀ s ∈ Icc a b, HasDerivWithinAt y (y' s) (Icc a b) s) {s : ℝ} (hs : s ∈ Icc a b) :
    HasDerivWithinAt (fun s => y (a + b - s)) (-y' (a + b - s)) (Icc a b) s := by
  have hmem : a + b - s ∈ Icc a b := ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have h1 : HasDerivWithinAt (fun s : ℝ => a + b - s) (-1) (Icc a b) s :=
    (hasDerivWithinAt_id s (Icc a b)).const_sub (a + b)
  have hmaps : MapsTo (fun s : ℝ => a + b - s) (Icc a b) (Icc a b) := fun x hx =>
    ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have := (hy _ hmem).scomp s h1 hmaps
  simpa [Function.comp_def, neg_one_smul] using this

/-- **Second-order Taylor bound, forward form**: if `y'` is the derivative of `y` and `y''` that
of `y'` on `Icc a b`, with `‖y''‖ ≤ M` there, then
`‖y b - y a - (b - a) • y' a‖ ≤ M (b - a)² / 2`. -/
theorem norm_sub_sub_smul_le_mul_sq_div_two (hab : a ≤ b)
    (hy : ∀ s ∈ Icc a b, HasDerivWithinAt y (y' s) (Icc a b) s)
    (hy' : ∀ s ∈ Icc a b, HasDerivWithinAt y' (y'' s) (Icc a b) s)
    (hM : ∀ s ∈ Icc a b, ‖y'' s‖ ≤ M) :
    ‖y b - y a - (b - a) • y' a‖ ≤ M * (b - a) ^ 2 / 2 := by
  have hg : ∀ s ∈ Icc a b, HasDerivWithinAt (fun s => y s - y a - (s - a) • y' a)
      (y' s - y' a) (Icc a b) s := by
    intro s hs
    have := ((hy s hs).sub_const (y a)).sub
      (((hasDerivWithinAt_id s (Icc a b)).sub_const a).smul_const (y' a))
    exact this.congr_deriv (by simp)
  have hbound : ∀ s ∈ Icc a b, ‖y' s - y' a‖ ≤ M * (s - a) := by
    intro s hs
    have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hy' hM (convex_Icc a b)
      (left_mem_Icc.2 hab) hs
    rwa [Real.norm_of_nonneg (by linarith [hs.1])] at this
  have hB : ∀ s, HasDerivAt (fun s => M * (s - a) ^ 2 / 2) (M * (s - a)) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => (s - a) ^ 2) (2 * (s - a)) s := by
      have := (hasDerivAt_pow 2 (s - a)).comp s ((hasDerivAt_id s).sub_const a)
      simpa [Function.comp_def] using this
    exact ((h1.const_mul M).div_const 2).congr_deriv (by ring)
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary (f' := fun s => y' s - y' a)
    (HasDerivWithinAt.continuousOn hg)
    (fun s hs => (hg s (Ico_subset_Icc_self hs)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hs))
    (B := fun s => M * (s - a) ^ 2 / 2) (B' := fun s => M * (s - a)) (by simp) hB
    (fun s hs => hbound s (Ico_subset_Icc_self hs)) (right_mem_Icc.2 hab)
  simpa using key

/-- **Second-order Taylor bound, backward form**: under the hypotheses of
`norm_sub_sub_smul_le_mul_sq_div_two`, `‖y a - y b - (a - b) • y' b‖ ≤ M (b - a)² / 2`. -/
theorem norm_sub_sub_smul_le_mul_sq_div_two' (hab : a ≤ b)
    (hy : ∀ s ∈ Icc a b, HasDerivWithinAt y (y' s) (Icc a b) s)
    (hy' : ∀ s ∈ Icc a b, HasDerivWithinAt y' (y'' s) (Icc a b) s)
    (hM : ∀ s ∈ Icc a b, ‖y'' s‖ ≤ M) :
    ‖y a - y b - (a - b) • y' b‖ ≤ M * (b - a) ^ 2 / 2 := by
  have hy1 : ∀ s ∈ Icc a b, HasDerivWithinAt (fun s => y (a + b - s)) (-y' (a + b - s))
      (Icc a b) s := fun s hs => hasDerivWithinAt_comp_const_sub_Icc hy hs
  have hy2 : ∀ s ∈ Icc a b, HasDerivWithinAt (fun s => -y' (a + b - s)) (y'' (a + b - s))
      (Icc a b) s := fun s hs =>
    (hasDerivWithinAt_comp_const_sub_Icc hy' hs).neg.congr_deriv (neg_neg _)
  have hM2 : ∀ s ∈ Icc a b, ‖y'' (a + b - s)‖ ≤ M := fun s hs =>
    hM _ ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have := norm_sub_sub_smul_le_mul_sq_div_two hab hy1 hy2 hM2
  simp only [add_sub_cancel_right, add_sub_cancel_left, smul_neg, ← neg_smul, neg_sub] at this
  exact this

/-- **Third-order Taylor bound for the trapezoidal rule**: if `y'`, `y''`, `y'''` are the
successive derivatives of `y` on `Icc a b` with `‖y'''‖ ≤ M` there, then
`‖y b - y a - ((b - a) / 2) • (y' a + y' b)‖ ≤ M (b - a)³ / 12`. This is the Peano-kernel
bound of the trapezoidal rule for `∫_a^b y' = y b - y a`, obtained here without integrals: the
residual `g s = y s - y a - ((s - a)/2) (y' a + y' s)` has derivative
`(1/2) (y' s - y' a - (s - a) y'' s)`, a backward second-order remainder of `y'` bounded by
`M (s - a)² / 4`, and the comparison with `M (s - a)³ / 12` concludes. -/
theorem norm_sub_sub_smul_add_le_mul_pow_three_div_twelve (hab : a ≤ b)
    (hy : ∀ s ∈ Icc a b, HasDerivWithinAt y (y' s) (Icc a b) s)
    (hy' : ∀ s ∈ Icc a b, HasDerivWithinAt y' (y'' s) (Icc a b) s)
    (hy'' : ∀ s ∈ Icc a b, HasDerivWithinAt y'' (y''' s) (Icc a b) s)
    (hM : ∀ s ∈ Icc a b, ‖y''' s‖ ≤ M) :
    ‖y b - y a - ((b - a) / 2) • (y' a + y' b)‖ ≤ M * (b - a) ^ 3 / 12 := by
  have hg : ∀ s ∈ Icc a b, HasDerivWithinAt (fun s => y s - y a - ((s - a) / 2) • (y' a + y' s))
      ((1 / 2 : ℝ) • (y' s - y' a - (s - a) • y'' s)) (Icc a b) s := by
    intro s hs
    have h1 : HasDerivWithinAt (fun s : ℝ => (s - a) / 2) (1 / 2) (Icc a b) s :=
      ((hasDerivWithinAt_id s (Icc a b)).sub_const a).div_const 2
    have := ((hy s hs).sub_const (y a)).sub (h1.smul ((hy' s hs).const_add (y' a)))
    refine this.congr_deriv ?_
    module
  have hbound : ∀ s ∈ Icc a b, ‖(1 / 2 : ℝ) • (y' s - y' a - (s - a) • y'' s)‖ ≤
      M * (s - a) ^ 2 / 4 := by
    intro s hs
    have hsub : Icc a s ⊆ Icc a b := Icc_subset_Icc_right hs.2
    have := norm_sub_sub_smul_le_mul_sq_div_two' (y := y') (y' := y'') (y'' := y''') hs.1
      (fun u hu => (hy' u (hsub hu)).mono hsub) (fun u hu => (hy'' u (hsub hu)).mono hsub)
      (fun u hu => hM u (hsub hu))
    rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    have e : y' s - y' a - (s - a) • y'' s = -(y' a - y' s - (a - s) • y'' s) := by
      rw [← neg_sub s a, neg_smul]; abel
    rw [e, norm_neg]
    linarith
  have hB : ∀ s, HasDerivAt (fun s => M * (s - a) ^ 3 / 12) (M * (s - a) ^ 2 / 4) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => (s - a) ^ 3) (3 * (s - a) ^ 2) s := by
      have := (hasDerivAt_pow 3 (s - a)).comp s ((hasDerivAt_id s).sub_const a)
      simpa [Function.comp_def] using this
    exact ((h1.const_mul M).div_const 12).congr_deriv (by ring)
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (f' := fun s => (1 / 2 : ℝ) • (y' s - y' a - (s - a) • y'' s))
    (HasDerivWithinAt.continuousOn hg)
    (fun s hs => (hg s (Ico_subset_Icc_self hs)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hs))
    (B := fun s => M * (s - a) ^ 3 / 12) (B' := fun s => M * (s - a) ^ 2 / 4) (by simp) hB
    (fun s hs => hbound s (Ico_subset_Icc_self hs)) (right_mem_Icc.2 hab)
  simpa using key

end Taylor

namespace ODE

/-! ### The grid -/

section Grid

variable {T h : ℝ} {n : ℕ}

/-- The number `N_h = ⌊T / h⌋₊` of steps of size `h` whose nodes `t₀ + n h`, `n ≤ N_h`, lie in
`[t₀, t₀ + T]` ([quarteroni2000numerical] §11.2). -/
noncomputable def gridCount (T h : ℝ) : ℕ := ⌊T / h⌋₊

/-- `n ≤ N_h` iff `n h ≤ T`. -/
theorem le_gridCount_iff (hT : 0 ≤ T) (hh : 0 < h) : n ≤ gridCount T h ↔ (n : ℝ) * h ≤ T := by
  rw [gridCount, Nat.le_floor_iff (div_nonneg hT hh.le), le_div_iff₀ hh]

/-- The last node stays in the horizon: `N_h h ≤ T`. -/
theorem gridCount_mul_le (hT : 0 ≤ T) (hh : 0 < h) : (gridCount T h : ℝ) * h ≤ T :=
  (le_gridCount_iff hT hh).1 le_rfl

/-- A negative horizon has no steps. -/
theorem gridCount_eq_zero_of_neg (hT : T < 0) (hh : 0 < h) : gridCount T h = 0 :=
  Nat.floor_of_nonpos (div_nonpos_of_nonpos_of_nonneg hT.le hh.le)

/-- If some node index is below `N_h`, the horizon is nonnegative. -/
theorem nonneg_of_lt_gridCount (hh : 0 < h) (hn : n < gridCount T h) : 0 ≤ T := by
  by_contra hT
  rw [gridCount_eq_zero_of_neg (not_le.1 hT) hh] at hn
  exact absurd hn (Nat.not_lt_zero _)

/-- If `n ≤ N_h` then `n h ≤ T`. -/
theorem mul_le_of_le_gridCount (hT : 0 ≤ T) (hh : 0 < h) (hn : n ≤ gridCount T h) :
    (n : ℝ) * h ≤ T :=
  (le_gridCount_iff hT hh).1 hn

/-- The grid node `t_n = t₀ + n h`. -/
def node (t₀ h : ℝ) (n : ℕ) : ℝ := t₀ + n * h

/-- The first node is `t₀`. -/
@[simp] theorem node_zero (t₀ h : ℝ) : node t₀ h 0 = t₀ := by simp [node]

/-- Consecutive nodes differ by the step. -/
theorem node_succ (t₀ h : ℝ) (n : ℕ) : node t₀ h (n + 1) = node t₀ h n + h := by
  simp only [node, Nat.cast_succ]; ring

/-- The nodes `t_n`, `n ≤ N_h`, lie in the horizon `[t₀, t₀ + T]`. -/
theorem node_mem_Icc {t₀ : ℝ} (hT : 0 ≤ T) (hh : 0 < h) (hn : n ≤ gridCount T h) :
    node t₀ h n ∈ Icc t₀ (t₀ + T) := by
  have h1 := (le_gridCount_iff hT hh).1 hn
  have h2 : (0 : ℝ) ≤ n * h := by positivity
  simp only [node, mem_Icc]
  constructor <;> linarith

/-- A node strictly before the last one lies in the horizon. -/
theorem node_mem_Icc_of_lt {t₀ : ℝ} (hh : 0 < h) (hn : n < gridCount T h) :
    node t₀ h n ∈ Icc t₀ (t₀ + T) :=
  node_mem_Icc (nonneg_of_lt_gridCount hh hn) hh hn.le

/-- The right end `t_n + h = t_{n+1}` of a step starting before the last node lies in the
horizon. -/
theorem node_add_mem_Icc_of_lt {t₀ : ℝ} (hh : 0 < h) (hn : n < gridCount T h) :
    node t₀ h n + h ∈ Icc t₀ (t₀ + T) := by
  rw [← node_succ]
  exact node_mem_Icc (nonneg_of_lt_gridCount hh hn) hh hn

end Grid

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace OneStep

/-! ### Methods, step relations and orbits -/

/-- An increment function `Φ t u v h` for the method `u_{n+1} = u_n + h Φ(t_n, u_n, u_{n+1}; h)`
([quarteroni2000numerical] (11.11)), with the new value `v = u_{n+1}` available so that implicit
methods are increment functions too. -/
abbrev Increment (E : Type*) := ℝ → E → E → ℝ → E

/-- A one-step method as a *step relation*: `S h t u v` says that `v` is an admissible value at
time `t + h` given the value `u` at time `t` ([quarteroni2000numerical] Definition 11.2:
`u_{n+1}` depends only on `u_n`). Increment functions give relations by `ofIncrement`; implicit
Runge–Kutta methods give relations directly. -/
abbrev StepRel (E : Type*) := ℝ → ℝ → E → E → Prop

/-- A numerical method: the rule producing the step relation from the vector field `f`. -/
abbrev Method (E : Type*) := (ℝ → E → E) → StepRel E

variable {Φ : Increment E} {S : StepRel E} {h t₀ T h₀ Λ : ℝ} {n : ℕ}

/-- An increment function is **explicit** when it does not depend on the new value, so that
`u_{n+1}` is computed directly from `u_n` ([quarteroni2000numerical] Definition 11.3); a method
is implicit when it is not explicit. -/
def IsExplicit (Φ : Increment E) : Prop := ∀ t u v w h, Φ t u v h = Φ t u w h

/-- The step relation `v = u + h Φ(t, u, v; h)` of an increment function. -/
def ofIncrement (Φ : Increment E) : StepRel E := fun h t u v => v = u + h • Φ t u v h

/-- The step relation of an increment function, unfolded. -/
theorem ofIncrement_apply {t : ℝ} {u v : E} :
    ofIncrement Φ h t u v ↔ v = u + h • Φ t u v h := Iff.rfl

/-- One explicit step on the state `(t, u)`: `(t + h, u + h Φ(t, u, u; h))`. For an explicit `Φ`
the third argument is irrelevant; for an implicit one this is a predictor evaluation, not the
method. -/
def step (Φ : Increment E) (h : ℝ) (s : ℝ × E) : ℝ × E := (s.1 + h, s.2 + h • Φ s.1 s.2 s.2 h)

/-- The `n`-th state `(t_n, u_n)` of the explicit iteration from `(t₀, y₀)`. -/
def iterate (Φ : Increment E) (h t₀ : ℝ) (y₀ : E) (n : ℕ) : ℝ × E := (step Φ h)^[n] (t₀, y₀)

/-- The iteration starts at `(t₀, y₀)`. -/
@[simp] theorem iterate_zero (y₀ : E) : iterate Φ h t₀ y₀ 0 = (t₀, y₀) := rfl

/-- One more iterate is one more step. -/
theorem iterate_succ (y₀ : E) (n : ℕ) :
    iterate Φ h t₀ y₀ (n + 1) = step Φ h (iterate Φ h t₀ y₀ n) :=
  Function.iterate_succ_apply' _ _ _

/-- The time component of the iteration is the grid node. -/
theorem iterate_fst (y₀ : E) (n : ℕ) : (iterate Φ h t₀ y₀ n).1 = node t₀ h n := by
  induction n with
  | zero => simp
  | succ n ih => rw [iterate_succ, node_succ, ← ih]; rfl

/-- A **perturbed orbit** ([quarteroni2000numerical] (11.16)): `z_{n+1} - h δ_{n+1}` is admissible
from `z_n`, i.e. `z_{n+1}` is the step from `z_n` plus `h δ_{n+1}`. Only `δ (n + 1)` enters; `δ 0`
is the perturbation of the initial datum, `z 0 = y₀ + δ 0`, imposed separately. -/
def IsOrbitWith (S : StepRel E) (h t₀ : ℝ) (δ : ℕ → E) (z : ℕ → E) : Prop :=
  ∀ n, S h (node t₀ h n) (z n) (z (n + 1) - h • δ (n + 1))

/-- An **orbit** of the step relation with step `h` from time `t₀`, the unperturbed recursion
([quarteroni2000numerical] (11.11), (11.17)). -/
def IsOrbit (S : StepRel E) (h t₀ : ℝ) (u : ℕ → E) : Prop := IsOrbitWith S h t₀ 0 u

/-- An orbit, unfolded: every consecutive pair is admissible. -/
theorem isOrbit_iff {u : ℕ → E} : IsOrbit S h t₀ u ↔ ∀ n, S h (node t₀ h n) (u n) (u (n + 1)) := by
  simp [IsOrbit, IsOrbitWith]

/-- An orbit of an increment function is the recursion `u_{n+1} = u_n + h Φ(t_n, u_n, u_{n+1}; h)`
([quarteroni2000numerical] (11.11)). -/
theorem isOrbit_ofIncrement_iff {u : ℕ → E} :
    IsOrbit (ofIncrement Φ) h t₀ u ↔
      ∀ n, u (n + 1) = u n + h • Φ (node t₀ h n) (u n) (u (n + 1)) h := by
  simp [IsOrbit, IsOrbitWith, ofIncrement]

/-- A perturbed orbit of an increment function is the recursion
`z_{n+1} = z_n + h Φ(t_n, z_n, z_{n+1} - h δ_{n+1}; h) + h δ_{n+1}`
([quarteroni2000numerical] (11.16)). -/
theorem isOrbitWith_ofIncrement_iff {δ z : ℕ → E} :
    IsOrbitWith (ofIncrement Φ) h t₀ δ z ↔
      ∀ n, z (n + 1) = z n + h • Φ (node t₀ h n) (z n) (z (n + 1) - h • δ (n + 1)) h +
        h • δ (n + 1) := by
  simp only [IsOrbitWith, ofIncrement, sub_eq_iff_eq_add]

/-- For an explicit increment, the iteration is an orbit. -/
theorem isOrbit_iterate (hex : IsExplicit Φ) (y₀ : E) :
    IsOrbit (ofIncrement Φ) h t₀ fun n => (iterate Φ h t₀ y₀ n).2 := by
  rw [isOrbit_ofIncrement_iff]
  intro n
  rw [iterate_succ, step, ← iterate_fst (Φ := Φ) (h := h) y₀ n]
  exact congrArg _ (congrArg _ (hex _ _ _ _ _))

/-- For an explicit increment, an orbit is the iteration from its initial value. -/
theorem eq_iterate_of_isOrbit (hex : IsExplicit Φ) {u : ℕ → E}
    (hu : IsOrbit (ofIncrement Φ) h t₀ u) (n : ℕ) : u n = (iterate Φ h t₀ (u 0) n).2 := by
  rw [isOrbit_ofIncrement_iff] at hu
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [hu n, ih, iterate_succ, step, iterate_fst]
    exact congrArg _ (congrArg _ (hex _ _ _ _ _))

/-! ### Local and global truncation error, consistency, order -/

/-- The **local truncation error** ([quarteroni2000numerical] (11.12)) of the increment `Φ` along
the curve `y` at `t`: `τ = (y (t + h) - y t) / h - Φ(t, y t, y (t + h); h)`, the books'
`τ_{n+1}(h)` at `t = t_n`. -/
noncomputable def lte (Φ : Increment E) (h : ℝ) (y : ℝ → E) (t : ℝ) : E :=
  h⁻¹ • (y (t + h) - y t) - Φ t (y t) (y (t + h)) h

/-- The exact curve satisfies the scheme up to `h` times its local truncation error. -/
theorem lte_spec (hh : h ≠ 0) (y : ℝ → E) (t : ℝ) :
    y (t + h) = y t + h • Φ t (y t) (y (t + h)) h + h • lte Φ h y t := by
  simp only [lte, smul_sub, smul_smul, mul_inv_cancel₀ hh, one_smul]
  abel

/-- The **global truncation error** `τ(h) = max_{0 ≤ n ≤ N_h - 1} ‖τ_{n+1}(h)‖` (a finite
supremum, `0` when `N_h = 0`). -/
noncomputable def globalLte (Φ : Increment E) (t₀ T : ℝ) (y : ℝ → E) (h : ℝ) : ℝ :=
  ⨆ n : Fin (gridCount T h), ‖lte Φ h y (node t₀ h n)‖

/-- Every local truncation error on the grid is bounded by the global one. -/
theorem norm_lte_le_globalLte {y : ℝ → E} (hn : n < gridCount T h) :
    ‖lte Φ h y (node t₀ h n)‖ ≤ globalLte Φ t₀ T y h :=
  le_ciSup (f := fun n : Fin (gridCount T h) => ‖lte Φ h y (node t₀ h n)‖)
    (Finite.bddAbove_range _) ⟨n, hn⟩

/-- The global truncation error is nonnegative. -/
theorem globalLte_nonneg (y : ℝ → E) : 0 ≤ globalLte Φ t₀ T y h :=
  Real.iSup_nonneg fun _ => norm_nonneg _

/-- A uniform bound on the local truncation errors bounds the global one. -/
theorem globalLte_le {y : ℝ → E} {C : ℝ} (hC : 0 ≤ C)
    (hle : ∀ n < gridCount T h, ‖lte Φ h y (node t₀ h n)‖ ≤ C) : globalLte Φ t₀ T y h ≤ C :=
  Real.iSup_le (fun i => hle i i.2) hC

/-- **Consistency** of `Φ` along the curve `y` on `[t₀, t₀ + T]`: the global truncation error
tends to zero with the step ([quarteroni2000numerical] §11.3). -/
def IsConsistentFor (Φ : Increment E) (t₀ T : ℝ) (y : ℝ → E) : Prop :=
  Tendsto (globalLte Φ t₀ T y) (𝓝[>] 0) (𝓝 0)

/-- **Order `p`** along `y` ([quarteroni2000numerical] (11.14)): `τ(h) = O(h^p)` as `h → 0⁺`. -/
def HasOrderFor (Φ : Increment E) (t₀ T : ℝ) (y : ℝ → E) (p : ℕ) : Prop :=
  globalLte Φ t₀ T y =O[𝓝[>] 0] fun h => h ^ p

/-- A method of positive order is consistent. -/
theorem HasOrderFor.isConsistentFor {y : ℝ → E} {p : ℕ} (hp : 1 ≤ p)
    (hΦ : HasOrderFor Φ t₀ T y p) : IsConsistentFor Φ t₀ T y :=
  hΦ.trans_tendsto <| ((continuous_pow p).tendsto' 0 0
    (by simp [zero_pow (Nat.one_le_iff_ne_zero.1 hp)])).mono_left nhdsWithin_le_nhds

/-- A uniform bound `‖τ_{n+1}(h)‖ ≤ C h^p` on the local truncation errors for every `h > 0` gives
order `p`. -/
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

/-- Along a `C¹` solution, the difference quotients converge to the derivative uniformly on the
interval: for every `ε > 0` there is `η > 0` such that
`‖(y (t + h) - y t) / h - f t (y t)‖ ≤ ε` whenever `0 < h ≤ η` and `t, t + h ∈ [t₀, t₀ + T]`. This
is the uniform continuity of `y' = f(·, y ·)` on the compact interval together with the mean
value inequality. -/
theorem exists_forall_norm_sub_smul_le_of_continuousOn
    (hy : ∀ s ∈ Icc t₀ (t₀ + T), HasDerivWithinAt y (f s (y s)) (Icc t₀ (t₀ + T)) s)
    (hf : ContinuousOn (fun s => f s (y s)) (Icc t₀ (t₀ + T))) {ε : ℝ} (hε : 0 < ε) :
    ∃ η > 0, ∀ h ∈ Ioc 0 η, ∀ t ∈ Icc t₀ (t₀ + T), t + h ∈ Icc t₀ (t₀ + T) →
      ‖h⁻¹ • (y (t + h) - y t) - f t (y t)‖ ≤ ε := by
  obtain ⟨η, hη, hunif⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hf) ε hε
  refine ⟨η / 2, half_pos hη, fun h hh t ht hth => ?_⟩
  have hsub : Icc t (t + h) ⊆ Icc t₀ (t₀ + T) := Icc_subset_Icc ht.1 hth.2
  have hne : h ≠ 0 := hh.1.ne'
  have hinv : 0 ≤ h⁻¹ := inv_nonneg.2 hh.1.le
  -- the mean value inequality on `s ↦ y s - s • f t (y t)`
  have hg : ∀ s ∈ Icc t (t + h), HasDerivWithinAt (fun s => y s - s • f t (y t))
      (f s (y s) - f t (y t)) (Icc t (t + h)) s := fun s hs =>
    ((hy s (hsub hs)).mono hsub).sub
      (((hasDerivWithinAt_id s _).smul_const (f t (y t))).congr_deriv (one_smul ℝ _))
  have hbound : ∀ s ∈ Icc t (t + h), ‖f s (y s) - f t (y t)‖ ≤ ε := by
    intro s hs
    have := hunif s (hsub hs) t ht (by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hs.1, hs.2, hh.2])
    rw [dist_eq_norm] at this
    exact this.le
  have key := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hg hbound (convex_Icc _ _)
    (left_mem_Icc.2 (by linarith [hh.1])) (right_mem_Icc.2 (by linarith [hh.1]))
  rw [add_sub_cancel_left, Real.norm_of_nonneg hh.1.le] at key
  have e : h⁻¹ • (y (t + h) - y t) - f t (y t) =
      h⁻¹ • ((y (t + h) - (t + h) • f t (y t)) - (y t - t • f t (y t))) := by
    have e1 : (y (t + h) - (t + h) • f t (y t)) - (y t - t • f t (y t)) =
        (y (t + h) - y t) - h • f t (y t) := by
      rw [add_smul]; abel
    rw [e1, smul_sub h⁻¹ (y (t + h) - y t) (h • f t (y t)), smul_smul, inv_mul_cancel₀ hne,
      one_smul]
  rw [e, norm_smul, norm_inv, Real.norm_of_nonneg hh.1.le]
  calc h⁻¹ * ‖y (t + h) - (t + h) • f t (y t) - (y t - t • f t (y t))‖ ≤ h⁻¹ * (ε * h) :=
        mul_le_mul_of_nonneg_left key hinv
    _ = ε := by field_simp

/-- **The consistency criterion** ([quarteroni2000numerical] (11.13)): if `y` is a `C¹`
solution of `y' = f(t, y)` on `[t₀, t₀ + T]` and the increment converges to the field along
the solution, `Φ(t, y t, y (t + h); h) → f(t, y t)` as `h → 0⁺`, *uniformly* in `t` (over the
pairs `t, t + h` in the interval — the book's "for all `t_n`" must be read uniformly for
`τ(h) = max_n ‖τ_{n+1}(h)‖ → 0`), then `Φ` is consistent along `y`. -/
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

/-- **Zero-stability** ([quarteroni2000numerical] Definition 11.4) of the step relation `S` for
the problem with datum `y₀` on the horizon `T`: there are `h₀ > 0` and `C > 0` such that for every
`h ∈ (0, h₀]`, every perturbation `δ` bounded by `ε` on the grid, an orbit `u` from `y₀` and a
perturbed orbit `z` from `y₀ + δ 0` satisfy `‖z n - u n‖ ≤ C ε` for `n ≤ N_h`. `C` may depend on
`T` but not on `h`, `ε`, `δ`. -/
def IsZeroStable (S : StepRel E) (t₀ T : ℝ) (y₀ : E) : Prop :=
  ∃ h₀ : ℝ, 0 < h₀ ∧ ∃ C : ℝ, 0 < C ∧ ∀ h ∈ Ioc 0 h₀, ∀ ε : ℝ, 0 ≤ ε → ∀ δ : ℕ → E,
    (∀ k ≤ gridCount T h, ‖δ k‖ ≤ ε) → ∀ u z : ℕ → E, IsOrbit S h t₀ u → u 0 = y₀ →
      IsOrbitWith S h t₀ δ z → z 0 = y₀ + δ 0 → ∀ n ≤ gridCount T h, ‖z n - u n‖ ≤ C * ε

/-- The hypothesis (11.18) of [quarteroni2000numerical] Theorem 11.1: `Φ` is `Λ`-Lipschitz in
its second argument, uniformly in `t ∈ [t₀, t₀ + T]`, in the third argument and in
`h ∈ (0, h₀]`. For an explicit increment the third argument is inert; for an implicit one the
condition asks that the dependence on the new value be absorbed into `Λ`. -/
def LipschitzIncrement (Φ : Increment E) (t₀ T h₀ Λ : ℝ) : Prop :=
  ∀ h ∈ Ioc 0 h₀, ∀ t ∈ Icc t₀ (t₀ + T), ∀ u v w w', ‖Φ t u w h - Φ t v w' h‖ ≤ Λ * ‖u - v‖

/-- **The estimate behind Theorems 11.1 and 11.2 of [quarteroni2000numerical]**: let `Φ` be
`Λ`-Lipschitz in the sense of `LipschitzIncrement`, `0 ≤ Λ`, `h ∈ (0, h₀]`, and let `u` and `z`
satisfy `u (n+1) = u n + h Φ(t_n, u n, v n; h)` and
`z (n+1) = z n + h Φ(t_n, z n, v' n; h) + h δ (n+1)` (the third arguments `v`, `v'` are
arbitrary), with `‖δ k‖ ≤ ε` for `1 ≤ k ≤ N_h`. Then for `n ≤ N_h`,
`‖z n - u n‖ ≤ (‖z 0 - u 0‖ + n h ε) exp (n h Λ)`.

Proof: `w_n = z_n - u_n` satisfies `‖w_{n+1}‖ ≤ (1 + h Λ) ‖w_n‖ + h ε` for `n < N_h`, hence
`‖w_n‖ ≤ ‖w_0‖ + n h ε + h Λ ∑_{j<n} ‖w_j‖` (the inequality (11.19)), and the discrete Gronwall
lemma `Gronwall.discrete_sum_const_of_le` concludes. -/
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

/-- **Zero-stability estimate** ([quarteroni2000numerical] Theorem 11.1, quantitative form): for
a `Λ`-Lipschitz increment, `h ∈ (0, h₀]` and perturbations `‖δ k‖ ≤ ε` for `k ≤ N_h`, an orbit `u`
from `y₀` and a `δ`-perturbed orbit `z` from `y₀ + δ 0` satisfy
`‖z n - u n‖ ≤ (1 + n h) ε exp (n h Λ)` for `n ≤ N_h`. -/
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

/-- **Zero-stability** ([quarteroni2000numerical] Theorem 11.1): an increment `Λ`-Lipschitz in
the sense of `LipschitzIncrement` on the horizon `T ≥ 0` gives a zero-stable method for every
datum, with `C = (1 + T) exp (Λ T)`. -/
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

/-- **Convergence** ([quarteroni2000numerical] Definition 11.5) of the step relation `S` to the
curve `y` from the datum `y₀`: for some `h₀ > 0` and some `C : ℝ → ℝ` with `C h → 0` as `h → 0⁺`,
every orbit from `y₀` with step `h ∈ (0, h₀]` is within `C h` of the curve at every grid node
`n ≤ N_h`. The threshold `h₀`, absent from the book's definition, is forced by the hypothesis
(11.18) of Theorem 11.2, which only holds for small steps. -/
def IsConvergentFor (S : StepRel E) (t₀ T : ℝ) (y₀ : E) (y : ℝ → E) : Prop :=
  ∃ C : ℝ → ℝ, Tendsto C (𝓝[>] 0) (𝓝 0) ∧ ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ h ∈ Ioc 0 h₀, ∀ u : ℕ → E,
    IsOrbit S h t₀ u → u 0 = y₀ → ∀ n ≤ gridCount T h, ‖u n - y (node t₀ h n)‖ ≤ C h

/-- **Convergence with order `p`** ([quarteroni2000numerical] Definition 11.5, second clause):
the bound is `𝒞 h^p`. -/
def IsConvergentWithOrderFor (S : StepRel E) (t₀ T : ℝ) (y₀ : E) (y : ℝ → E) (p : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ h ∈ Ioc 0 h₀, ∀ u : ℕ → E,
    IsOrbit S h t₀ u → u 0 = y₀ → ∀ n ≤ gridCount T h, ‖u n - y (node t₀ h n)‖ ≤ C * h ^ p

/-- Convergence with a positive order is convergence. -/
theorem IsConvergentWithOrderFor.isConvergentFor {y₀ : E} {y : ℝ → E} {p : ℕ} (hp : 1 ≤ p)
    (hS : IsConvergentWithOrderFor S t₀ T y₀ y p) : IsConvergentFor S t₀ T y₀ y := by
  obtain ⟨C, -, h₀, hh₀, hC⟩ := hS
  refine ⟨fun h => C * h ^ p, ?_, h₀, hh₀, hC⟩
  have : Tendsto (fun h : ℝ => C * h ^ p) (𝓝 0) (𝓝 (C * 0 ^ p)) :=
    (continuous_const.mul (continuous_pow p)).tendsto 0
  rw [zero_pow (by omega), mul_zero] at this
  exact this.mono_left nhdsWithin_le_nhds

/-- **The convergence estimate (11.20)** of [quarteroni2000numerical] Theorem 11.2: for a
`Λ`-Lipschitz increment, `h ∈ (0, h₀]`, an orbit `u` and *any* curve `y`,
`‖y (t_n) - u n‖ ≤ (‖y t₀ - u 0‖ + n h τ(h)) exp (n h Λ)` for `n ≤ N_h`. The curve enters only
through its truncation errors: it is a perturbed recursion with `δ_{n+1} = τ_{n+1}(h)`
(`lte_spec`). -/
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

/-- **Consistency and a Lipschitz increment give convergence** ([quarteroni2000numerical]
Theorem 11.2), with `C h = T τ(h) exp (Λ T)` and the orbits started at `y t₀`. -/
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

/-- **Order of convergence** ([quarteroni2000numerical] Theorem 11.2): a `Λ`-Lipschitz increment
of order `p` along `y` is convergent with order `p` from the datum `y t₀`. -/
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

/-- **Forward Euler** ([quarteroni2000numerical] (11.7)): `Φ = f(t, u)`, explicit. -/
def forwardEuler (f : ℝ → E → E) : Increment E := fun t u _ _ => f t u

/-- **Backward Euler** ([quarteroni2000numerical] (11.8)): `Φ = f(t + h, v)`, implicit. -/
def backwardEuler (f : ℝ → E → E) : Increment E := fun t _ v h => f (t + h) v

/-- **Crank–Nicolson**, the trapezoidal method ([quarteroni2000numerical] (11.9)):
`Φ = (f(t, u) + f(t + h, v)) / 2`, implicit. -/
noncomputable def crankNicolson (f : ℝ → E → E) : Increment E :=
  fun t u v h => (2 : ℝ)⁻¹ • (f t u + f (t + h) v)

/-- **Heun's method** ([quarteroni2000numerical] (11.10)):
`Φ = (f(t, u) + f(t + h, u + h f(t, u))) / 2`, explicit — Crank–Nicolson with the new value
predicted by forward Euler. -/
noncomputable def heun (f : ℝ → E → E) : Increment E :=
  fun t u _ h => (2 : ℝ)⁻¹ • (f t u + f (t + h) (u + h • f t u))

/-- **The θ-method**, `Φ = (1 - θ) f(t, u) + θ f(t + h, v)`: the one-parameter family behind
forward Euler (`θ = 0`), Crank–Nicolson (`θ = 1/2`) and backward Euler (`θ = 1`), and the time
discretization of the parabolic problems of [quarteroni2000numerical] §13.2–13.3; explicit for
`θ = 0`, implicit otherwise. -/
noncomputable def theta (f : ℝ → E → E) (θ : ℝ) : Increment E :=
  fun t u v h => (1 - θ) • f t u + θ • f (t + h) v

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Forward Euler is explicit. -/
theorem isExplicit_forwardEuler (f : ℝ → E → E) : IsExplicit (forwardEuler f) :=
  fun _ _ _ _ _ => rfl

/-- Heun's method is explicit. -/
theorem isExplicit_heun (f : ℝ → E → E) : IsExplicit (heun f) := fun _ _ _ _ _ => rfl

/-- The θ-method with `θ = 0` is forward Euler. -/
@[simp] theorem theta_zero (f : ℝ → E → E) : theta f 0 = forwardEuler f := by
  ext t u v h; simp [theta, forwardEuler]

/-- The θ-method with `θ = 1` is backward Euler. -/
@[simp] theorem theta_one (f : ℝ → E → E) : theta f 1 = backwardEuler f := by
  ext t u v h; simp [theta, backwardEuler]

/-- The θ-method with `θ = 1/2` is Crank–Nicolson. -/
theorem theta_half (f : ℝ → E → E) : theta f (1 / 2) = crankNicolson f := by
  ext t u v h; simp [theta, crankNicolson, smul_add]; norm_num

omit [NormedSpace ℝ E] in
/-- Forward Euler inherits the Lipschitz constant of the field. -/
theorem lipschitzIncrement_forwardEuler (hf : ∀ t ∈ Icc t₀ (t₀ + T), LipschitzWith L (f t))
    (h₀ : ℝ) : LipschitzIncrement (forwardEuler f) t₀ T h₀ L :=
  fun _ _ t ht u v _ _ => (hf t ht).norm_sub_le u v

/-- Heun's method is Lipschitz with constant `L (1 + h₀ L / 2)` when the field is `L`-Lipschitz
on the enlarged interval `[t₀, t₀ + T + h₀]` (the inner evaluation is at `t + h`). -/
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

/-- The local truncation error as `h⁻¹` times the residual of the scheme along the curve. -/
theorem lte_eq_inv_smul (hh : h ≠ 0) (y : ℝ → E) (t : ℝ) :
    lte Φ h y t = h⁻¹ • (y (t + h) - y t - h • Φ t (y t) (y (t + h)) h) := by
  simp only [lte, smul_sub, smul_smul, inv_mul_cancel₀ hh, one_smul]

/-- **Forward Euler has order one**: if `y' = f(·, y ·)` on `[t₀, t₀ + T]`, `y''` is the
derivative of `y'` there and `‖y''‖ ≤ M`, then for `0 < h` with `t, t + h ∈ [t₀, t₀ + T]`,
`‖τ(h)‖ ≤ (h / 2) M` — the books' `τ_{n+1}(h) = (h/2) y''(ξ)` in the norm form a normed space
allows. -/
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

/-- **Backward Euler has order one**: under the hypotheses of `norm_lte_forwardEuler_le`,
`‖τ(h)‖ ≤ (h / 2) M`, by the backward Taylor bound at `t + h`. -/
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

/-- **Crank–Nicolson has order two** ([quarteroni2000numerical] Exercise 11.2, (11.90)): if
`y' = f(·, y ·)`, `y''` and `y'''` are the successive derivatives on `[t₀, t₀ + T]` with
`‖y'''‖ ≤ M₃`, then `‖τ(h)‖ ≤ (h² / 12) M₃` for `0 < h`, `t, t + h ∈ [t₀, t₀ + T]`. The books'
`(h²/12) f''(ξ, y(ξ))` means the second derivative of `s ↦ f(s, y(s)) = y'(s)`, i.e. `y'''`. -/
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

/-- **Heun's method has order two** ([quarteroni2000numerical] Exercise 11.1): with the
hypotheses of `norm_lte_crankNicolson_le`, `‖y''‖ ≤ M₂`, and `f t` `L`-Lipschitz for
`t ∈ [t₀, t₀ + T]`, `‖τ(h)‖ ≤ (h² / 12) M₃ + (h² / 4) L M₂`. The residual is the Crank–Nicolson
residual plus `(h/2) (f(t+h, y(t+h)) - f(t+h, y t + h f(t, y t)))`, and the second term is
bounded by the Lipschitz constant times the forward Euler residual. -/
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
  have hL : (0 : ℝ) ≤ L := L.coe_nonneg
  calc h⁻¹ * ‖(y (t + h) - y t - (h / 2) • (f t (y t) + f (t + h) (y (t + h)))) +
        (h / 2) • (f (t + h) (y (t + h)) - f (t + h) (y t + h • f t (y t)))‖
      ≤ h⁻¹ * (M₃ * h ^ 3 / 12 + h / 2 * (L * (M₂ * h ^ 2 / 2))) := by
        gcongr
        refine (norm_add_le _ _).trans (add_le_add k3 ?_)
        rw [norm_smul, Real.norm_of_nonneg (by positivity)]
        gcongr
    _ = h ^ 2 / 12 * M₃ + h ^ 2 / 4 * L * M₂ := by field_simp; ring

/-- **Local truncation error of the θ-method**: with the hypotheses of `norm_lte_heun_le` on
`y` (but no Lipschitz condition), `‖τ(h)‖ ≤ |θ - 1/2| M₂ h + (h² / 12) M₃`: order 1 for
`θ ≠ 1/2` and order 2 for `θ = 1/2`, where the first term vanishes and the bound is that of
Crank–Nicolson. The residual is the Crank–Nicolson residual plus
`h (1/2 - θ) (y'(t + h) - y'(t))`, and the mean value inequality bounds the second term by
`h |1/2 - θ| M₂ h`. This is the time half of the truncation-error estimate of
[quarteroni2000numerical] Exercise 13.1. -/
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

/-- **Forward Euler has order one** along a solution with a bounded second derivative. -/
theorem hasOrderFor_forwardEuler
    (hy : ∀ s ∈ Icc t₀ (t₀ + T), HasDerivWithinAt y (f s (y s)) (Icc t₀ (t₀ + T)) s)
    (hy' : ∀ s ∈ Icc t₀ (t₀ + T), HasDerivWithinAt (fun s => f s (y s)) (y'' s) (Icc t₀ (t₀ + T)) s)
    (hM : ∀ s ∈ Icc t₀ (t₀ + T), ‖y'' s‖ ≤ M) : HasOrderFor (forwardEuler f) t₀ T y 1 :=
  hasOrderFor_of_forall_norm_lte_le (C := M / 2) fun h hh n hn => by
    rw [show M / 2 * h ^ 1 = h / 2 * M by ring]
    exact norm_lte_forwardEuler_le hy hy' hM hh (node_mem_Icc_of_lt hh hn)
      (node_add_mem_Icc_of_lt hh hn)

/-- **Backward Euler has order one** along a solution with a bounded second derivative. -/
theorem hasOrderFor_backwardEuler
    (hy : ∀ s ∈ Icc t₀ (t₀ + T), HasDerivWithinAt y (f s (y s)) (Icc t₀ (t₀ + T)) s)
    (hy' : ∀ s ∈ Icc t₀ (t₀ + T), HasDerivWithinAt (fun s => f s (y s)) (y'' s) (Icc t₀ (t₀ + T)) s)
    (hM : ∀ s ∈ Icc t₀ (t₀ + T), ‖y'' s‖ ≤ M) : HasOrderFor (backwardEuler f) t₀ T y 1 :=
  hasOrderFor_of_forall_norm_lte_le (C := M / 2) fun h hh n hn => by
    rw [show M / 2 * h ^ 1 = h / 2 * M by ring]
    exact norm_lte_backwardEuler_le hy hy' hM hh (node_mem_Icc_of_lt hh hn)
      (node_add_mem_Icc_of_lt hh hn)

/-- **Crank–Nicolson has order two** along a solution with a bounded third derivative. -/
theorem hasOrderFor_crankNicolson
    (hy : ∀ s ∈ Icc t₀ (t₀ + T), HasDerivWithinAt y (f s (y s)) (Icc t₀ (t₀ + T)) s)
    (hy' : ∀ s ∈ Icc t₀ (t₀ + T), HasDerivWithinAt (fun s => f s (y s)) (y'' s) (Icc t₀ (t₀ + T)) s)
    (hy'' : ∀ s ∈ Icc t₀ (t₀ + T), HasDerivWithinAt y'' (y''' s) (Icc t₀ (t₀ + T)) s)
    (hM : ∀ s ∈ Icc t₀ (t₀ + T), ‖y''' s‖ ≤ M₃) : HasOrderFor (crankNicolson f) t₀ T y 2 :=
  hasOrderFor_of_forall_norm_lte_le (C := M₃ / 12) fun h hh n hn => by
    rw [show M₃ / 12 * h ^ 2 = h ^ 2 / 12 * M₃ by ring]
    exact norm_lte_crankNicolson_le hy hy' hy'' hM hh (node_mem_Icc_of_lt hh hn)
      (node_add_mem_Icc_of_lt hh hn)

/-- **Heun's method has order two** ([quarteroni2000numerical] Exercise 11.1). -/
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

/-- **The θ-method has order one** for every `θ` (and order two for `θ = 1/2`, which is
`hasOrderFor_crankNicolson` through `theta_half`). -/
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

/-- **The direct forward Euler error bound** ([quarteroni2000numerical] (11.22)), without the
discrete Gronwall lemma: if `f s` is `L`-Lipschitz for `s ∈ [t₀, t₀ + T]`, `0 < L`, `y` is a
solution with `‖y''‖ ≤ M` there and `u` is the forward Euler orbit with `u 0 = y t₀`, then for
`n ≤ N_h`, `‖y (t_n) - u n‖ ≤ ((e^{L n h} - 1) / L) (M / 2) h`. The recursion
`‖e_{n+1}‖ ≤ h τ(h) + (1 + h L) ‖e_n‖` unrolls to `((1 + hL)^n - 1) / L · τ(h)`, and
`1 + hL ≤ e^{hL}`. Sharper than (11.20) by the factor `(e^{Ls} - 1) / (L s) ≤ e^{Ls}`. -/
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
      have hpow : 0 ≤ (1 + h * L) ^ m - 1 := by
        have : 1 ≤ (1 + h * L) ^ m := one_le_pow₀ (by linarith [mul_nonneg hh.le L.coe_nonneg])
        linarith
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
  have hpos : 0 ≤ M / 2 * h := by positivity
  gcongr

end Orders

/-! ### Absolute stability on the test equation -/

end OneStep

/-- The test equation `y' = λ y` ([quarteroni2000numerical] (11.24)) as a vector field on `ℂ`. -/
def testField (lam : ℂ) : ℝ → ℂ → ℂ := fun _ y => lam * y

/-- The solution `e^{λ t}` of the test equation. -/
theorem hasDerivAt_exp_testField (lam : ℂ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp (lam * t))
      (testField lam t (Complex.exp (lam * t))) t := by
  have h1 : HasDerivAt (fun z : ℂ => Complex.exp (lam * z)) (Complex.exp (lam * t) * lam) t := by
    have := (Complex.hasDerivAt_exp (lam * t)).comp (t : ℂ) ((hasDerivAt_id (t : ℂ)).const_mul lam)
    simpa [Function.comp_def] using this
  exact h1.comp_ofReal.congr_deriv (by simp [testField, mul_comm])

namespace OneStep

/-- **Absolute stability** ([quarteroni2000numerical] Definition 11.6) of a step relation on `ℂ`
with step `h` — meant to be a method applied to the test equation: every initial value has an
orbit, and every orbit tends to zero. The existence clause matters for implicit methods at their
singular parameter (backward Euler at `hλ = 1`, Crank–Nicolson at `hλ = 2`), where the only
orbit is `0` and stability must not hold by vacuity. -/
def IsAbsStable (S : StepRel ℂ) (h : ℝ) : Prop :=
  (∀ u₀ : ℂ, ∃ u : ℕ → ℂ, IsOrbit S h 0 u ∧ u 0 = u₀) ∧
    ∀ u : ℕ → ℂ, IsOrbit S h 0 u → Tendsto u atTop (𝓝 0)

/-- The **region of absolute stability** ([quarteroni2000numerical] (11.26)) of a method: the
set of `z = hλ` such that the method applied to `y' = λ y` with step `h` is absolutely stable
for every factorization of `z`. For scale-invariant methods this is the `h = 1` slice
(`absStabilityRegion_eq_of_scaleInvariant`). -/
def absStabilityRegion (M : Method ℂ) : Set ℂ :=
  {z | ∀ h : ℝ, 0 < h → IsAbsStable (M (testField (z / h))) h}

/-- **A-stability** ([quarteroni2000numerical] §11.3.3): the region of absolute stability
contains the open left half-plane, `𝒜 ∩ ℂ⁻ = ℂ⁻`. -/
def IsAStable (M : Method ℂ) : Prop := ∀ z : ℂ, z.re < 0 → z ∈ absStabilityRegion M

variable {M : Method ℂ} {h : ℝ}

/-- Absolute stability only depends on the set of orbits. -/
theorem isAbsStable_congr {S S' : StepRel ℂ} {h h' : ℝ}
    (hS : ∀ u, IsOrbit S h 0 u ↔ IsOrbit S' h' 0 u) : IsAbsStable S h ↔ IsAbsStable S' h' := by
  simp only [IsAbsStable, hS]

/-- For a method whose orbits on the test equation depend on `(h, λ)` only through `hλ`, the
region of absolute stability is the `h = 1` slice `{z | IsAbsStable (M (testField z)) 1}`. -/
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

/-- For a scale-invariant method, absolute stability with step `h` at `λ` is membership of `hλ`
in the region. -/
theorem isAbsStable_iff_mem_absStabilityRegion
    (hM : ∀ h > 0, ∀ lam u, IsOrbit (M (testField lam)) h 0 u ↔
      IsOrbit (M (testField (h * lam))) 1 0 u) (hh : 0 < h) (lam : ℂ) :
    IsAbsStable (M (testField lam)) h ↔ (h : ℂ) * lam ∈ absStabilityRegion M := by
  rw [absStabilityRegion_eq_of_scaleInvariant hM, mem_ofPred_eq]
  exact isAbsStable_congr (hM h hh lam)

/-- A step relation whose orbits from `u₀` are exactly the geometric sequences `r ^ n u₀` is
absolutely stable iff `‖r‖ < 1`. -/
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

/-- A step relation all of whose orbits vanish identically is not absolutely stable (the
existence clause fails at `u₀ = 1`). -/
theorem not_isAbsStable_of_forall_eq_zero {S : StepRel ℂ}
    (hall : ∀ u, IsOrbit S h 0 u → ∀ n, u n = 0) : ¬ IsAbsStable S h := by
  rintro ⟨hex, -⟩
  obtain ⟨u, hu, hu0⟩ := hex 1
  exact one_ne_zero (hu0.symm.trans (hall u hu 0))

section FourMethods

variable {lam : ℂ} {u : ℕ → ℂ} {h : ℝ}

/-- The orbits of forward Euler on the test equation: `u_n = (1 + hλ)^n u₀`. -/
theorem forwardEuler_testField_orbit
    (hu : IsOrbit (ofIncrement (forwardEuler (testField lam))) h 0 u) (n : ℕ) :
    u n = (1 + h * lam) ^ n * u 0 := by
  rw [isOrbit_ofIncrement_iff] at hu
  induction n with
  | zero => simp
  | succ n ih => rw [hu n, ih]; simp only [forwardEuler, testField, Complex.real_smul]; ring

/-- Forward Euler on the test equation has an orbit from every datum. -/
theorem isOrbit_forwardEuler_testField (lam : ℂ) (h : ℝ) (u₀ : ℂ) :
    IsOrbit (ofIncrement (forwardEuler (testField lam))) h 0 fun n => (1 + h * lam) ^ n * u₀ := by
  rw [isOrbit_ofIncrement_iff]
  intro n
  simp only [forwardEuler, testField, Complex.real_smul]
  ring

/-- Forward Euler on the test equation depends on `(h, λ)` only through `hλ`. -/
theorem forwardEuler_scaleInvariant (h : ℝ) (_ : 0 < h) (lam : ℂ) (u : ℕ → ℂ) :
    IsOrbit (ofIncrement (forwardEuler (testField lam))) h 0 u ↔
      IsOrbit (ofIncrement (forwardEuler (testField (h * lam)))) 1 0 u := by
  simp only [isOrbit_ofIncrement_iff, forwardEuler, testField, Complex.real_smul,
    Complex.ofReal_one, one_mul]
  refine forall_congr' fun n => ?_
  constructor <;> intro H <;> linear_combination H

/-- **The region of absolute stability of forward Euler** ([quarteroni2000numerical] (11.27)):
the open disc of radius `1` about `-1`. -/
theorem mem_absStabilityRegion_forwardEuler_iff (z : ℂ) :
    z ∈ absStabilityRegion (fun f => ofIncrement (forwardEuler f)) ↔ ‖1 + z‖ < 1 := by
  rw [absStabilityRegion_eq_of_scaleInvariant forwardEuler_scaleInvariant, mem_ofPred_eq]
  refine isAbsStable_iff_norm_lt_one (r := 1 + z) (fun u₀ => ?_) (fun u hu n => ?_)
  · simpa using isOrbit_forwardEuler_testField z 1 u₀
  · simpa using forwardEuler_testField_orbit hu n

/-- **Forward Euler on the test equation with `Re λ < 0`** is absolutely stable with step `h > 0`
iff `h < -2 Re λ / |λ|²`, the second form of [quarteroni2000numerical] (11.27). -/
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

/-- The orbits of backward Euler on the test equation, `hλ ≠ 1`: `u_n = (1 - hλ)^{-n} u₀`. -/
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

/-- At the singular parameter `hλ = 1` the only orbit of backward Euler is `0`. -/
theorem backwardEuler_testField_orbit_eq_zero (heq : (h : ℂ) * lam = 1)
    (hu : IsOrbit (ofIncrement (backwardEuler (testField lam))) h 0 u) (n : ℕ) : u n = 0 := by
  rw [isOrbit_ofIncrement_iff] at hu
  have := hu n
  simp only [backwardEuler, testField, Complex.real_smul, ← mul_assoc] at this
  linear_combination -this - u (n + 1) * heq

/-- Backward Euler on the test equation, `hλ ≠ 1`, has an orbit from every datum. -/
theorem isOrbit_backwardEuler_testField (hne : (h : ℂ) * lam ≠ 1) (u₀ : ℂ) :
    IsOrbit (ofIncrement (backwardEuler (testField lam))) h 0
      fun n => (1 - h * lam)⁻¹ ^ n * u₀ := by
  rw [isOrbit_ofIncrement_iff]
  intro n
  have hne' : (1 : ℂ) - h * lam ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
  simp only [backwardEuler, testField, Complex.real_smul, pow_succ]
  field_simp
  ring

/-- Backward Euler on the test equation depends on `(h, λ)` only through `hλ`. -/
theorem backwardEuler_scaleInvariant (h : ℝ) (_ : 0 < h) (lam : ℂ) (u : ℕ → ℂ) :
    IsOrbit (ofIncrement (backwardEuler (testField lam))) h 0 u ↔
      IsOrbit (ofIncrement (backwardEuler (testField (h * lam)))) 1 0 u := by
  simp only [isOrbit_ofIncrement_iff, backwardEuler, testField, Complex.real_smul,
    Complex.ofReal_one, one_mul]
  refine forall_congr' fun n => ?_
  constructor <;> intro H <;> linear_combination H

/-- **The region of absolute stability of backward Euler**: the exterior of the closed disc of
radius `1` about `1`. The point `z = 1` is excluded by the existence clause. -/
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

/-- The orbits of Crank–Nicolson on the test equation, `hλ ≠ 2`:
`u_n = ((1 + hλ/2) / (1 - hλ/2))^n u₀`. -/
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

/-- At the singular parameter `hλ = 2` the only orbit of Crank–Nicolson is `0`. -/
theorem crankNicolson_testField_orbit_eq_zero (heq : (h : ℂ) * lam = 2)
    (hu : IsOrbit (ofIncrement (crankNicolson (testField lam))) h 0 u) (n : ℕ) : u n = 0 := by
  rw [isOrbit_ofIncrement_iff] at hu
  have := hu n
  simp only [crankNicolson, testField, Complex.real_smul] at this
  push_cast at this
  linear_combination (-1 / 2 : ℂ) * this - (u n + u (n + 1)) / 4 * heq

/-- Crank–Nicolson on the test equation, `hλ ≠ 2`, has an orbit from every datum. -/
theorem isOrbit_crankNicolson_testField (hne : (h : ℂ) * lam ≠ 2) (u₀ : ℂ) :
    IsOrbit (ofIncrement (crankNicolson (testField lam))) h 0
      fun n => ((1 + h * lam / 2) / (1 - h * lam / 2)) ^ n * u₀ := by
  rw [isOrbit_ofIncrement_iff]
  intro n
  have hne' : (1 : ℂ) - h * lam / 2 ≠ 0 := by
    intro h0
    apply hne
    linear_combination (-2 : ℂ) * h0
  simp only [crankNicolson, testField, Complex.real_smul, pow_succ]
  push_cast
  field_simp
  ring

/-- Crank–Nicolson on the test equation depends on `(h, λ)` only through `hλ`. -/
theorem crankNicolson_scaleInvariant (h : ℝ) (_ : 0 < h) (lam : ℂ) (u : ℕ → ℂ) :
    IsOrbit (ofIncrement (crankNicolson (testField lam))) h 0 u ↔
      IsOrbit (ofIncrement (crankNicolson (testField (h * lam)))) 1 0 u := by
  simp only [isOrbit_ofIncrement_iff, crankNicolson, testField, Complex.real_smul,
    Complex.ofReal_one, one_mul]
  refine forall_congr' fun n => ?_
  constructor <;> intro H <;> linear_combination H

/-- **The region of absolute stability of Crank–Nicolson**: the open left half-plane. The point
`z = 2` is excluded by the existence clause. -/
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

/-- The orbits of Heun's method on the test equation: `u_n = (1 + hλ + (hλ)²/2)^n u₀`. -/
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

/-- Heun's method on the test equation has an orbit from every datum. -/
theorem isOrbit_heun_testField (lam : ℂ) (h : ℝ) (u₀ : ℂ) :
    IsOrbit (ofIncrement (heun (testField lam))) h 0
      fun n => (1 + h * lam + (h * lam) ^ 2 / 2) ^ n * u₀ := by
  rw [isOrbit_ofIncrement_iff]
  intro n
  simp only [heun, testField, Complex.real_smul]
  push_cast
  ring

/-- Heun's method on the test equation depends on `(h, λ)` only through `hλ`. -/
theorem heun_scaleInvariant (h : ℝ) (_ : 0 < h) (lam : ℂ) (u : ℕ → ℂ) :
    IsOrbit (ofIncrement (heun (testField lam))) h 0 u ↔
      IsOrbit (ofIncrement (heun (testField (h * lam)))) 1 0 u := by
  simp only [isOrbit_ofIncrement_iff, heun, testField, Complex.real_smul, Complex.ofReal_one,
    one_mul]
  refine forall_congr' fun n => ?_
  constructor <;> intro H <;> linear_combination H

/-- **The region of absolute stability of Heun's method**: `‖1 + z + z²/2‖ < 1`. -/
theorem mem_absStabilityRegion_heun_iff (z : ℂ) :
    z ∈ absStabilityRegion (fun f => ofIncrement (heun f)) ↔ ‖1 + z + z ^ 2 / 2‖ < 1 := by
  rw [absStabilityRegion_eq_of_scaleInvariant heun_scaleInvariant, mem_ofPred_eq]
  refine isAbsStable_iff_norm_lt_one (r := 1 + z + z ^ 2 / 2) (fun u₀ => ?_) (fun u hu n => ?_)
  · simpa using isOrbit_heun_testField z 1 u₀
  · simpa using heun_testField_orbit hu n

/-- **Forward Euler is not A-stable**: `z = -3` lies in the left half-plane and outside the
region. -/
theorem not_isAStable_forwardEuler : ¬ IsAStable fun f => ofIncrement (forwardEuler f) := by
  intro H
  have := (mem_absStabilityRegion_forwardEuler_iff (-3)).1 (H (-3) (by norm_num))
  norm_num at this

/-- **Heun's method is not A-stable**: `z = -3` lies in the left half-plane and outside the
region. -/
theorem not_isAStable_heun : ¬ IsAStable fun f => ofIncrement (heun f) := by
  intro H
  have := (mem_absStabilityRegion_heun_iff (-3)).1 (H (-3) (by norm_num))
  norm_num at this

/-- The real trace of the forward Euler region is the interval `(-2, 0)`. -/
theorem ofReal_mem_absStabilityRegion_forwardEuler_iff (x : ℝ) :
    (x : ℂ) ∈ absStabilityRegion (fun f => ofIncrement (forwardEuler f)) ↔ x ∈ Ioo (-2) 0 := by
  rw [mem_absStabilityRegion_forwardEuler_iff, ← Complex.ofReal_one, ← Complex.ofReal_add,
    Complex.norm_real, Real.norm_eq_abs, abs_lt, mem_Ioo]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- The real trace of Heun's region is the interval `(-2, 0)`, the same as forward Euler's
([quarteroni2000numerical] §11.3.3). -/
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
