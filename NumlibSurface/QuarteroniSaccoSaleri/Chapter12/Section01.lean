import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Numlib.Analysis.Calculus.ContDiffOnIcc

/-!
# Quarteroni–Sacco–Saleri §12.1: a model problem

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*,
Springer, 2000, §12.1.

The two-point boundary value problem `-u''(x) = f(x)` for `0 < x < 1` with `u(0) = u(1) = 0`,
(12.1)–(12.2), is solved in closed form: for `u ∈ C²([0, 1])` the fundamental theorem of calculus
and the boundary conditions give the representation `u(x) = ∫₀¹ G(x, s) f(s) ds` (12.3) with the
*Green's function* `G(x, s) = s (1 - x)` for `s ≤ x` and `x (1 - s)` for `x ≤ s` (12.4), which is
continuous, symmetric, nonnegative, vanishes when `x` or `s` is `0` or `1`, and has
`∫₀¹ G(x, s) ds = x (1 - x) / 2`. Hence for every `f ∈ C⁰([0, 1])` the problem has a unique
solution `u ∈ C²([0, 1])`, given by (12.3); it is nonnegative when `f` is (the *monotonicity
property*), and it satisfies the *maximum principle* `‖u‖_∞ ≤ ‖f‖_∞ / 8` (12.5).

The section is classical calculus on `[0, 1]` and rests on Mathlib alone — interval integrals and
the fundamental theorem of calculus — with no backbone module behind it; the Green's function
reappears in §12.2 as `h⁻¹` times the inverse of the finite difference matrix.

## Main definitions

* `greenFunction x s` — the Green's function `G(x, s)` of (12.4).
* `IsSolution f u` — `u ∈ C²([0, 1])` solves (12.1)–(12.2) with datum `f`.

## Main results

* `greenFunction_symm`, `greenFunction_nonneg`, `greenFunction_zero_left`, …,
  `continuous_greenFunction`, `integral_greenFunction` — the properties of `G` listed after (12.4).
* `equation_12_3_solution` — the function `x ↦ ∫₀¹ G(x, s) f(s) ds` is a `C²` solution of
  (12.1)–(12.2) for every `f ∈ C⁰([0, 1])`.
* `equation_12_3` — every `C²` solution is given by (12.3); `IsSolution.eqOn` is the uniqueness
  behind it and `equation_12_3_existsUnique` the book's conclusion, existence and uniqueness.
* `IsSolution.contDiffOn_of_contDiffOn` — the regularity `f ∈ C^m` implies `u ∈ C^{m+2}`.
* `equation_12_3_monotone` — the monotonicity property: `f ≥ 0` implies `u ≥ 0`.
* `equation_12_5` — the maximum principle `‖u‖_∞ ≤ ‖f‖_∞ / 8`, and `equation_12_5_of_forall_le`
  the same with any bound `M` on `|f|` in place of `‖f‖_∞`.

## Proof route

The book derives (12.3) by integrating (12.1) twice and fixing the two constants by (12.2). The
route here is the reverse: `equation_12_3_solution` differentiates `v(x) = ∫₀¹ G(x, s) f(s) ds`
twice by splitting the integral at the kink `s = x`, `v(x) = (1 - x) ∫₀ˣ s f + x ∫ₓ¹ (1 - s) f`, and
using the fundamental theorem of calculus in each endpoint (`integral_hasDerivWithinAt_right`,
`integral_hasDerivWithinAt_left`); then `IsSolution.eqOn` says two `C²` solutions agree, since
their difference has vanishing second derivative and vanishes at both ends, and (12.3) is the
combination of the two. The general calculus lemmas the argument needs and Mathlib does not state
— that within-derivative data on `[a, b]` gives `ContDiffOn ℝ 2`, the interior second derivative of
such a function, the interior derivatives of a `C²` function on `[a, b]`, and that a function with
zero second derivative vanishing at both ends vanishes — are in
`Numlib/Analysis/Calculus/ContDiffOnIcc`.

## Conventions

`u ∈ C²([0, 1])` is `ContDiffOn ℝ 2 u (Icc 0 1)` for `u : ℝ → ℝ`, and `u''(x)` at an interior
point is `iteratedDeriv 2 u x`; `f ∈ C⁰([0, 1])` is `ContinuousOn f (Icc 0 1)`. The book writes
`f ∈ C⁰(0, 1)` in the maximum principle; continuity on the closed interval is what (12.3) used and
what makes `‖f‖_∞` finite, and it is assumed throughout. The maximum norm `‖g‖_∞ = max_{[0,1]} |g|`
of a real function is written `sSup ((fun s => |g s|) '' Icc 0 1)`, and the bound `‖u‖_∞ ≤ C` as
`∀ x ∈ Icc 0 1, |u x| ≤ C`.
-/

open Set Filter Topology intervalIntegral

namespace QuarteroniSaccoSaleri.Chapter12

/-! ### The Green's function (12.4) -/

/-- **The Green's function (12.4)** of the boundary value problem (12.1)–(12.2):
`G(x, s) = s (1 - x)` if `0 ≤ s ≤ x` and `G(x, s) = x (1 - s)` if `x ≤ s ≤ 1` (the two
expressions agree at `s = x`). It is defined by the same two expressions on all of `ℝ × ℝ`. -/
noncomputable def greenFunction (x s : ℝ) : ℝ := if s ≤ x then s * (1 - x) else x * (1 - s)

variable {x s : ℝ}

/-- The first branch of (12.4): `G(x, s) = s (1 - x)` for `s ≤ x`. -/
theorem greenFunction_of_le (h : s ≤ x) : greenFunction x s = s * (1 - x) := by
  simp [greenFunction, h]

/-- The second branch of (12.4): `G(x, s) = x (1 - s)` for `x ≤ s`. -/
theorem greenFunction_of_ge (h : x ≤ s) : greenFunction x s = x * (1 - s) := by
  unfold greenFunction
  split_ifs with h'
  · rw [le_antisymm h' h]
  · rfl

/-- The Green's function in one formula, `G(x, s) = min (x, s) (1 - max (x, s))`. -/
theorem greenFunction_eq_min_mul (x s : ℝ) : greenFunction x s = min x s * (1 - max x s) := by
  rcases le_total s x with h | h
  · rw [greenFunction_of_le h, min_eq_right h, max_eq_left h]
  · rw [greenFunction_of_ge h, min_eq_left h, max_eq_right h]

/-- `G` is symmetric: `G(x, s) = G(s, x)` (for all `x, s`, in particular in `[0, 1]`). -/
theorem greenFunction_symm (x s : ℝ) : greenFunction x s = greenFunction s x := by
  rw [greenFunction_eq_min_mul, greenFunction_eq_min_mul, min_comm, max_comm]

/-- `G` is nonnegative on `[0, 1] × [0, 1]`. -/
theorem greenFunction_nonneg (hx : x ∈ Icc 0 1) (hs : s ∈ Icc 0 1) : 0 ≤ greenFunction x s := by
  rw [greenFunction_eq_min_mul]
  exact mul_nonneg (le_min hx.1 hs.1) (sub_nonneg.2 (max_le hx.2 hs.2))

/-- `G(0, s) = 0` for `s ≥ 0`. -/
theorem greenFunction_zero_left (hs : 0 ≤ s) : greenFunction 0 s = 0 := by
  rw [greenFunction_of_ge hs, zero_mul]

/-- `G(1, s) = 0` for `s ≤ 1`. -/
theorem greenFunction_one_left (hs : s ≤ 1) : greenFunction 1 s = 0 := by
  rw [greenFunction_of_le hs, sub_self, mul_zero]

/-- `G(x, 0) = 0` for `x ≥ 0`. -/
theorem greenFunction_zero_right (hx : 0 ≤ x) : greenFunction x 0 = 0 := by
  rw [greenFunction_symm, greenFunction_zero_left hx]

/-- `G(x, 1) = 0` for `x ≤ 1`. -/
theorem greenFunction_one_right (hx : x ≤ 1) : greenFunction x 1 = 0 := by
  rw [greenFunction_symm, greenFunction_one_left hx]

/-- `G` is continuous on `ℝ × ℝ`: its two branches agree along the diagonal `s = x`. -/
theorem continuous_greenFunction : Continuous fun p : ℝ × ℝ => greenFunction p.1 p.2 := by
  unfold greenFunction
  exact Continuous.if_le (by fun_prop) (by fun_prop) continuous_snd continuous_fst
    fun p hp => by rw [hp]

/-- For fixed `x`, `s ↦ G(x, s)` is continuous (and piecewise linear). -/
theorem continuous_greenFunction_right (x : ℝ) : Continuous (greenFunction x) :=
  continuous_greenFunction.comp (continuous_const.prodMk continuous_id)

/-- For fixed `s`, `x ↦ G(x, s)` is continuous (and piecewise linear). -/
theorem continuous_greenFunction_left (s : ℝ) : Continuous fun x => greenFunction x s :=
  continuous_greenFunction.comp (continuous_id.prodMk continuous_const)

/-- `∫₀¹ G(x, s) ds = x (1 - x) / 2` for `x ∈ [0, 1]`. -/
theorem integral_greenFunction (hx : x ∈ Icc 0 1) :
    ∫ s in (0 : ℝ)..1, greenFunction x s = x * (1 - x) / 2 := by
  have hc : Continuous (greenFunction x) := continuous_greenFunction_right x
  rw [← integral_add_adjacent_intervals (hc.intervalIntegrable 0 x) (hc.intervalIntegrable x 1)]
  have h1 : ∫ s in (0 : ℝ)..x, greenFunction x s = ∫ s in (0 : ℝ)..x, s * (1 - x) :=
    integral_congr fun s hs => by
      rw [uIcc_of_le hx.1] at hs
      exact greenFunction_of_le hs.2
  have h2 : ∫ s in x..1, greenFunction x s = ∫ s in x..1, x * (1 - s) :=
    integral_congr fun s hs => by
      rw [uIcc_of_le hx.2] at hs
      exact greenFunction_of_ge hs.1
  rw [h1, h2, integral_mul_const, integral_id, integral_const_mul,
    integral_sub intervalIntegrable_const (continuous_id'.intervalIntegrable _ _), integral_const,
    integral_id, smul_eq_mul]
  ring

/-! ### The boundary value problem (12.1)–(12.2) -/

/-- **The boundary value problem (12.1)–(12.2).** `u ∈ C²([0, 1])` is a solution with datum `f`
when `-u''(x) = f(x)` for `0 < x < 1` (12.1) and `u(0) = u(1) = 0` (12.2). -/
structure IsSolution (f u : ℝ → ℝ) : Prop where
  /-- `u ∈ C²([0, 1])`. -/
  contDiffOn : ContDiffOn ℝ 2 u (Icc 0 1)
  /-- (12.1): `-u''(x) = f(x)` for `0 < x < 1`. -/
  equation_12_1 : ∀ x ∈ Ioo 0 1, -iteratedDeriv 2 u x = f x
  /-- (12.2), left end: `u(0) = 0`. -/
  equation_12_2_left : u 0 = 0
  /-- (12.2), right end: `u(1) = 0`. -/
  equation_12_2_right : u 1 = 0

/-! ### The representation formula (12.3) -/

variable {f u : ℝ → ℝ}

/-- The integral of (12.3) split at the kink `s = x` of the Green's function: for `x ∈ [0, 1]`,
`∫₀¹ G(x, s) f(s) ds = (1 - x) ∫₀ˣ s f(s) ds + x ∫ₓ¹ (1 - s) f(s) ds`. -/
theorem integral_greenFunction_mul_eq (hf : ContinuousOn f (Icc 0 1)) (hx : x ∈ Icc 0 1) :
    ∫ s in (0 : ℝ)..1, greenFunction x s * f s
      = (1 - x) * (∫ s in (0 : ℝ)..x, s * f s) + x * ∫ s in x..1, (1 - s) * f s := by
  have hcont : ContinuousOn (fun s => greenFunction x s * f s) (Icc 0 1) :=
    (continuous_greenFunction_right x).continuousOn.mul hf
  rw [← integral_add_adjacent_intervals
    ((hcont.mono (Icc_subset_Icc le_rfl hx.2)).intervalIntegrable_of_Icc hx.1)
    ((hcont.mono (Icc_subset_Icc hx.1 le_rfl)).intervalIntegrable_of_Icc hx.2)]
  congr 1
  · rw [← integral_const_mul]
    refine integral_congr fun s hs => ?_
    rw [uIcc_of_le hx.1] at hs
    rw [greenFunction_of_le hs.2]
    ring
  · rw [← integral_const_mul]
    refine integral_congr fun s hs => ?_
    rw [uIcc_of_le hx.2] at hs
    rw [greenFunction_of_ge hs.1]
    ring

/-- **(12.3), the existence half.** For every `f ∈ C⁰([0, 1])`, the function
`u(x) = ∫₀¹ G(x, s) f(s) ds` is a solution of (12.1)–(12.2) in `C²([0, 1])`.

Splitting the integral at `s = x` (`integral_greenFunction_mul_eq`) and differentiating each piece
by the fundamental theorem of calculus gives `u'(x) = ∫ₓ¹ (1 - s) f(s) ds - ∫₀ˣ s f(s) ds` and then
`u''(x) = -(1 - x) f(x) - x f(x) = -f(x)`, at every point of `[0, 1]` as a derivative within the
interval. -/
theorem equation_12_3_solution (hf : ContinuousOn f (Icc 0 1)) :
    IsSolution f fun x => ∫ s in (0 : ℝ)..1, greenFunction x s * f s := by
  -- the two primitives and their derivatives within `[0, 1]`
  have hgA : ContinuousOn (fun s => s * f s) (Icc 0 1) := continuousOn_id.mul hf
  have hgB : ContinuousOn (fun s => (1 - s) * f s) (Icc 0 1) :=
    (continuousOn_const.sub continuousOn_id).mul hf
  have hA : ∀ x ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun x => ∫ s in (0 : ℝ)..x, s * f s) (x * f x) (Icc 0 1) x := by
    intro x hx
    have : Fact (x ∈ Icc (0 : ℝ) 1) := ⟨hx⟩
    exact integral_hasDerivWithinAt_right (s := Icc 0 1) (t := Icc 0 1)
      ((hgA.mono (Icc_subset_Icc le_rfl hx.2)).intervalIntegrable_of_Icc hx.1)
      (hgA.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc x) (hgA x hx)
  have hB : ∀ x ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun x => ∫ s in x..1, (1 - s) * f s) (-((1 - x) * f x)) (Icc 0 1) x := by
    intro x hx
    have : Fact (x ∈ Icc (0 : ℝ) 1) := ⟨hx⟩
    exact integral_hasDerivWithinAt_left (s := Icc 0 1) (t := Icc 0 1)
      ((hgB.mono (Icc_subset_Icc hx.1 le_rfl)).intervalIntegrable_of_Icc hx.2)
      (hgB.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc x) (hgB x hx)
  -- the first derivative of `u`
  have hu₁ : ∀ x ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun x => ∫ s in (0 : ℝ)..1, greenFunction x s * f s)
        ((∫ s in x..1, (1 - s) * f s) - ∫ s in (0 : ℝ)..x, s * f s) (Icc 0 1) x := by
    intro x hx
    have h := (((hasDerivWithinAt_id x (Icc 0 1)).const_sub 1).mul (hA x hx)).add
      ((hasDerivWithinAt_id x (Icc 0 1)).mul (hB x hx))
    refine (h.congr_deriv ?_).congr (fun y hy => integral_greenFunction_mul_eq hf hy)
      (integral_greenFunction_mul_eq hf hx)
    simp only [id]
    ring
  -- the second derivative of `u`
  have hu₂ : ∀ x ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun x => (∫ s in x..1, (1 - s) * f s) - ∫ s in (0 : ℝ)..x, s * f s)
        (-f x) (Icc 0 1) x := by
    intro x hx
    refine ((hB x hx).sub (hA x hx)).congr_deriv ?_
    ring
  refine ⟨contDiffOn_two_of_hasDerivWithinAt (uniqueDiffOn_Icc zero_lt_one) hu₁ hu₂ hf.neg,
    fun x hx => ?_, ?_, ?_⟩
  · rw [iteratedDeriv_two_eq_of_hasDerivWithinAt hu₁ hu₂ hx, neg_neg]
  · rw [integral_congr (g := fun _ => (0 : ℝ)) fun s hs => ?_, integral_zero]
    rw [uIcc_of_le zero_le_one] at hs
    rw [greenFunction_zero_left hs.1, zero_mul]
  · rw [integral_congr (g := fun _ => (0 : ℝ)) fun s hs => ?_, integral_zero]
    rw [uIcc_of_le zero_le_one] at hs
    rw [greenFunction_one_left hs.2, zero_mul]

/-- **Uniqueness for (12.1)–(12.2).** Two `C²` solutions with the same datum agree on `[0, 1]`:
their difference has vanishing second derivative in `(0, 1)` and vanishes at both ends. -/
theorem IsSolution.eqOn {v : ℝ → ℝ} (hu : IsSolution f u) (hv : IsSolution f v) :
    EqOn u v (Icc 0 1) := by
  have hcu := hu.contDiffOn.continuousOn_derivWithin (uniqueDiffOn_Icc zero_lt_one) one_le_two
  have hcv := hv.contDiffOn.continuousOn_derivWithin (uniqueDiffOn_Icc zero_lt_one) one_le_two
  have key := eqOn_zero_of_hasDerivAt_zero zero_le_one
    (w := fun y => u y - v y) (w₁ := fun y => derivWithin u (Icc 0 1) y - derivWithin v (Icc 0 1) y)
    (hu.contDiffOn.continuousOn.sub hv.contDiffOn.continuousOn) (hcu.sub hcv)
    (fun y hy => (hasDerivAt_of_contDiffOn_two hu.contDiffOn hy).1.sub
      (hasDerivAt_of_contDiffOn_two hv.contDiffOn hy).1)
    (fun y hy => ((hasDerivAt_of_contDiffOn_two hu.contDiffOn hy).2.sub
      (hasDerivAt_of_contDiffOn_two hv.contDiffOn hy).2).congr_deriv (by
        rw [neg_eq_iff_eq_neg.1 (hu.equation_12_1 y hy), neg_eq_iff_eq_neg.1
          (hv.equation_12_1 y hy), sub_self]))
    (by rw [hu.equation_12_2_left, hv.equation_12_2_left, sub_zero])
    (by rw [hu.equation_12_2_right, hv.equation_12_2_right, sub_zero])
  intro y hy
  exact sub_eq_zero.1 (key hy)

/-- **(12.3).** If `u ∈ C²([0, 1])` satisfies the differential equation (12.1) and the boundary
conditions (12.2), with `f ∈ C⁰([0, 1])`, then

`u(x) = ∫₀¹ G(x, s) f(s) ds`, `x ∈ [0, 1]`,

with the Green's function `G` of (12.4). The book integrates (12.1) twice and fixes the constants
by (12.2); here the right-hand side is a solution (`equation_12_3_solution`) and solutions are
unique (`IsSolution.eqOn`). -/
theorem equation_12_3 (hf : ContinuousOn f (Icc 0 1)) (hu : IsSolution f u) (hx : x ∈ Icc 0 1) :
    u x = ∫ s in (0 : ℝ)..1, greenFunction x s * f s :=
  hu.eqOn (equation_12_3_solution hf) hx

/-- **§12.1, the conclusion drawn from (12.3):** for every `f ∈ C⁰([0, 1])` there is a unique
solution `u ∈ C²([0, 1])` of the boundary value problem (12.1)–(12.2), and it admits the
representation (12.3). Uniqueness is on `[0, 1]`, the only place where a solution is
constrained. -/
theorem equation_12_3_existsUnique (hf : ContinuousOn f (Icc 0 1)) :
    ∃ u : ℝ → ℝ, IsSolution f u ∧
      (∀ x ∈ Icc 0 1, u x = ∫ s in (0 : ℝ)..1, greenFunction x s * f s) ∧
      ∀ v, IsSolution f v → EqOn v u (Icc 0 1) :=
  ⟨_, equation_12_3_solution hf, fun _ _ => rfl, fun _ hv => hv.eqOn (equation_12_3_solution hf)⟩

/-- **§12.1, regularity.** Further smoothness of `u` can be derived by (12.1): if
`f ∈ C^m([0, 1])` for some `m ≥ 0` then the solution `u` of (12.1)–(12.2) is in `C^{m+2}([0, 1])`.
The second derivative of `u` within `[0, 1]` agrees with `-f` in the interior by (12.1), hence on
the closed interval by continuity, and `u ∈ C^{m+2}` is `u'' ∈ C^m`. -/
theorem IsSolution.contDiffOn_of_contDiffOn {m : ℕ} (hu : IsSolution f u)
    (hf : ContDiffOn ℝ m f (Icc 0 1)) : ContDiffOn ℝ (m + 2) u (Icc 0 1) := by
  have hs : UniqueDiffOn ℝ (Icc (0 : ℝ) 1) := uniqueDiffOn_Icc zero_lt_one
  have h₂ := hu.contDiffOn
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiffOn_succ_iff_derivWithin hs] at h₂
  obtain ⟨hdiff, -, h₁⟩ := h₂
  rw [contDiffOn_one_iff_derivWithin hs] at h₁
  obtain ⟨hdiff₁, hcont₂⟩ := h₁
  -- the second derivative within `[0, 1]` is `-f` on all of `[0, 1]`
  have heq : EqOn (derivWithin (derivWithin u (Icc 0 1)) (Icc 0 1)) (fun x => -f x) (Icc 0 1) := by
    refine EqOn.of_subset_closure (fun x hx => ?_) hcont₂ hf.continuousOn.neg
      Ioo_subset_Icc_self (by rw [closure_Ioo zero_ne_one])
    rw [derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2),
      (hasDerivAt_of_contDiffOn_two hu.contDiffOn hx).2.deriv,
      neg_eq_iff_eq_neg.1 (hu.equation_12_1 x hx)]
  rw [show ((m : WithTop ℕ∞) + 2) = (m + 1) + 1 by rw [add_assoc, one_add_one_eq_two],
    contDiffOn_succ_iff_derivWithin hs]
  refine ⟨hdiff, fun h => absurd h (by simp), ?_⟩
  rw [contDiffOn_succ_iff_derivWithin hs]
  exact ⟨hdiff₁, fun h => absurd h (by simp), hf.neg.congr fun x hx => heq hx⟩

/-! ### The monotonicity property and the maximum principle (12.5) -/

/-- **The monotonicity property (§12.1, after (12.4)).** If `f ∈ C⁰([0, 1])` is nonnegative, then
the solution `u` of (12.1)–(12.2) is nonnegative on `[0, 1]`: by (12.3), since `G(x, s) ≥ 0` for
all `x, s ∈ [0, 1]`. -/
theorem equation_12_3_monotone (hf : ContinuousOn f (Icc 0 1)) (hf0 : ∀ s ∈ Icc 0 1, 0 ≤ f s)
    (hu : IsSolution f u) : ∀ x ∈ Icc 0 1, 0 ≤ u x := by
  intro x hx
  rw [equation_12_3 hf hu hx]
  exact integral_nonneg zero_le_one fun s hs => mul_nonneg (greenFunction_nonneg hx hs) (hf0 s hs)

/-- **The maximum principle (12.5), with an explicit bound.** For `f ∈ C⁰([0, 1])` with
`|f| ≤ M` on `[0, 1]` and `u` the solution of (12.1)–(12.2), `|u(x)| ≤ M / 8` on `[0, 1]`:
since `G` is nonnegative, `|u(x)| ≤ ∫₀¹ G(x, s) |f(s)| ds ≤ M ∫₀¹ G(x, s) ds = M x (1 - x) / 2`. -/
theorem equation_12_5_of_forall_le (hf : ContinuousOn f (Icc 0 1)) (hu : IsSolution f u) {M : ℝ}
    (hM : ∀ s ∈ Icc 0 1, |f s| ≤ M) : ∀ x ∈ Icc 0 1, |u x| ≤ M / 8 := by
  intro x hx
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 ⟨le_rfl, zero_le_one⟩)
  have hcont : ContinuousOn (fun s => greenFunction x s * f s) (Icc 0 1) :=
    (continuous_greenFunction_right x).continuousOn.mul hf
  rw [equation_12_3 hf hu hx]
  calc |∫ s in (0 : ℝ)..1, greenFunction x s * f s|
      ≤ ∫ s in (0 : ℝ)..1, |greenFunction x s * f s| := abs_integral_le_integral_abs zero_le_one
    _ ≤ ∫ s in (0 : ℝ)..1, greenFunction x s * M := by
        refine integral_mono_on zero_le_one (hcont.abs.intervalIntegrable_of_Icc zero_le_one)
          (((continuous_greenFunction_right x).continuousOn.mul
            continuousOn_const).intervalIntegrable_of_Icc zero_le_one) fun s hs => ?_
        rw [abs_mul, abs_of_nonneg (greenFunction_nonneg hx hs)]
        exact mul_le_mul_of_nonneg_left (hM s hs) (greenFunction_nonneg hx hs)
    _ = x * (1 - x) / 2 * M := by rw [integral_mul_const, integral_greenFunction hx]
    _ ≤ M / 8 := by nlinarith [sq_nonneg (2 * x - 1), hM0]

/-- **The maximum principle (12.5).** For `f ∈ C⁰([0, 1])` and `u` the solution of
(12.1)–(12.2),

`‖u‖_∞ ≤ (1/8) ‖f‖_∞`,

where `‖g‖_∞ = max_{0 ≤ x ≤ 1} |g(x)|` is the maximum norm: every `|u(x)|`, `x ∈ [0, 1]`, is at
most `(1/8) max_{[0,1]} |f|`. The book writes `f ∈ C⁰(0, 1)` here; continuity on the closed
interval is what (12.3) used and what makes `‖f‖_∞` finite. -/
theorem equation_12_5 (hf : ContinuousOn f (Icc 0 1)) (hu : IsSolution f u) :
    ∀ x ∈ Icc 0 1, |u x| ≤ (1 / 8) * sSup ((fun s => |f s|) '' Icc 0 1) := by
  have hbdd : BddAbove ((fun s => |f s|) '' Icc 0 1) :=
    (isCompact_Icc.image_of_continuousOn hf.abs).bddAbove
  intro x hx
  rw [one_div_mul_eq_div]
  exact equation_12_5_of_forall_le hf hu (fun s hs => le_csSup hbdd (mem_image_of_mem _ hs)) x hx

end QuarteroniSaccoSaleri.Chapter12
