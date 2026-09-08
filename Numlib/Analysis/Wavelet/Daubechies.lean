import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination

/-!
# The Daubechies `D4` scaling function

Upstreaming candidate: nothing here is specific to numerical analysis.

This module constructs the continuous, compactly supported function `φ : ℝ → ℝ` with

* `φ x = 0` off `[0, 3]`,
* `φ x = (1+√3)/4 φ(2x) + (3+√3)/4 φ(2x-1) + (3-√3)/4 φ(2x-2) + (1-√3)/4 φ(2x-3)`,
* `φ 1 = (1+√3)/2` and `φ 2 = (1-√3)/2`,

and shows that its support is exactly `[0, 3]`.  This is the first Daubechies scaling function
beyond the Haar one, the fixed point of the **cascade operator** attached to the four-tap mask
`((1+√3)/4, (3+√3)/4, (3-√3)/4, (1-√3)/4)`.

## The construction

Existence is proved by iterating the cascade operator `T` from the piecewise-linear function
`approx0` that already carries the right values at the integers, and showing that the iterates
converge uniformly.  `T` is *not* a contraction for the supremum norm — the mask has
`∑_k |p_k| = (3+√3)/2 > 1` — and the standard remedy is a bound on the joint spectral radius of the
two matrices that drive the iteration.  For this mask that bound is explicit and elementary, and
`cascade_bound` is the whole of it.

Write `w(y) = (h y, h (y+1), h (y+2))` for `y ∈ [0,1]`.  A function `h` vanishing off `[0,3]`
satisfies `w(y) = T₀ w(2y)` on `[0,1/2]` and `w(y) = T₁ w(2y-1)` on `[1/2,1]`, for two explicit
`3 × 3` matrices whose columns each sum to `1` (`cascade_left`, `cascade_right`).  Both fix the
direction `(1,1,1)`, so the interesting action is on the plane `E = {v : v₀ + v₁ + v₂ = 0}`, which
is where the *difference* of two consecutive cascade iterates lives — that is what the partition of
unity `f x + f (x+1) + f (x+2) = 1`, preserved by the iteration, is for.  On `E`, in the norm

`N v = max |v₀| (2 |v₂|)`,

both `T₀` and `T₁` have operator norm at most `√3/2 < 1`, and the two bounds are attained:
`T₀` gives exactly `√3/2` and `T₁` gives `(5+√3)/8`.  That is `cascade_bound`, and it makes the
increments of the cascade iteration decay geometrically.

## The support

`scalingFun_support` is the sharp form of the support statement, and needs a second idea.
Pairing `w(y)`
against a covector `u` and running the two relations backwards, `⟪w(y), u⟫` on a dyadic interval
`[m/2ⁿ, (m+1)/2ⁿ]` is `⟪w(z), u'⟫` on all of `[0,1]`, where `u'` is the image of `u` under a product
of the two transposed matrices.  Both transposes are injective (`covector_left_eq_zero`,
`covector_right_eq_zero`), and `w(0), w(1/2), w(1)` span `ℝ³` (`covector_eq_zero`), so `u' ≠ 0`
forces `⟪w(z), u'⟫` to be somewhere nonzero.  Taking `u` to be a coordinate covector, `φ` cannot
vanish identically on any nondegenerate subinterval of `[0,3]`.

## Main statements

* `exists_scalingFun`: the existence theorem, in the form the properties are usually quoted.
* `scalingFun` and its properties: `scalingFun_continuous`, `scalingFun_refine`,
  `scalingFun_support`, and `scalingFun_isApprox`, which bundles the vanishing off `[0,3]`, the
  values `(1±√3)/2` at `1` and `2`, and the partition of unity.
* `scalingFun_one_half`, `scalingFun_three_halves`, `scalingFun_five_halves`: the values at the
  first half-integers, which the span argument needs.

## References

The mask, the normalisation and the support are Atkinson–Han [AtkinsonHan2009], §4.5, (4.5.5)–
(4.5.7); the construction is Daubechies' [Daubechies1988].
-/

noncomputable section

open Set

namespace Daubechies

/-! ### Arithmetic of `√3` -/

private theorem sqrt3_mul_self : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)

private theorem one_lt_sqrt3 : (1 : ℝ) < √3 := by
  nlinarith [sqrt3_mul_self, Real.sqrt_nonneg 3]

private theorem sqrt3_lt_two : √3 < 2 := by
  nlinarith [sqrt3_mul_self, Real.sqrt_nonneg 3]

/-! ### The cascade operator -/

/-- The **cascade operator** of the Daubechies `D4` mask: `T f (x)` is
`(1+√3)/4 f(2x) + (3+√3)/4 f(2x-1) + (3-√3)/4 f(2x-2) + (1-√3)/4 f(2x-3)`.  The scaling function
is its fixed point. -/
def cascade (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  (1 + √3) / 4 * f (2 * x) + (3 + √3) / 4 * f (2 * x - 1) + (3 - √3) / 4 * f (2 * x - 2)
    + (1 - √3) / 4 * f (2 * x - 3)

theorem cascade_apply (f : ℝ → ℝ) (x : ℝ) :
    cascade f x = (1 + √3) / 4 * f (2 * x) + (3 + √3) / 4 * f (2 * x - 1)
      + (3 - √3) / 4 * f (2 * x - 2) + (1 - √3) / 4 * f (2 * x - 3) := rfl

/-- The cascade operator is linear, and in particular commutes with subtraction. This is what makes
the *increments* of the iteration satisfy the same recurrence as the iterates themselves. -/
theorem cascade_sub (f g : ℝ → ℝ) :
    cascade (fun x => f x - g x) = fun x => cascade f x - cascade g x := by
  funext x
  simp only [cascade_apply]
  ring

/-- The cascade operator preserves continuity, being a finite linear combination of dilates. -/
theorem cascade_continuous {f : ℝ → ℝ} (hf : Continuous f) : Continuous (cascade f) := by
  change Continuous fun x => cascade f x
  simp only [cascade_apply]
  fun_prop

/-! ### The two-scale relations -/

section Relations

variable {f : ℝ → ℝ} (hle : ∀ x : ℝ, x ≤ 0 → f x = 0) (hge : ∀ x : ℝ, 3 ≤ x → f x = 0)

include hle hge

/-- On `[0, 1/2]` the cascade of `f` at `x`, `x+1`, `x+2` is a fixed matrix applied to the values
of `f` at `2x`, `2x+1`, `2x+2`. -/
theorem cascade_left {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    cascade f x = (1 + √3) / 4 * f (2 * x) ∧
      cascade f (x + 1) = (1 + √3) / 4 * f (2 * x + 2) + (3 + √3) / 4 * f (2 * x + 1)
        + (3 - √3) / 4 * f (2 * x) ∧
      cascade f (x + 2) = (3 - √3) / 4 * f (2 * x + 2) + (1 - √3) / 4 * f (2 * x + 1) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [cascade_apply, hle (2 * x - 1) (by linarith), hle (2 * x - 2) (by linarith),
      hle (2 * x - 3) (by linarith)]
    ring
  · have e0 : f (2 * (x + 1)) = f (2 * x + 2) := by congr 1; ring
    have e1 : f (2 * (x + 1) - 1) = f (2 * x + 1) := by congr 1; ring
    have e2 : f (2 * (x + 1) - 2) = f (2 * x) := by congr 1; ring
    have e3 : f (2 * (x + 1) - 3) = f (2 * x - 1) := by congr 1; ring
    rw [cascade_apply, e0, e1, e2, e3, hle (2 * x - 1) (by linarith)]
    ring
  · have e0 : f (2 * (x + 2)) = f (2 * x + 4) := by congr 1; ring
    have e1 : f (2 * (x + 2) - 1) = f (2 * x + 3) := by congr 1; ring
    have e2 : f (2 * (x + 2) - 2) = f (2 * x + 2) := by congr 1; ring
    have e3 : f (2 * (x + 2) - 3) = f (2 * x + 1) := by congr 1; ring
    rw [cascade_apply, e0, e1, e2, e3, hge (2 * x + 4) (by linarith),
      hge (2 * x + 3) (by linarith)]
    ring

/-- On `[1/2, 1]` the cascade of `f` at `x`, `x+1`, `x+2` is a fixed matrix applied to the values
of `f` at `2x-1`, `2x`, `2x+1`. -/
theorem cascade_right {x : ℝ} (hx0 : 1 / 2 ≤ x) (hx1 : x ≤ 1) :
    cascade f x = (1 + √3) / 4 * f (2 * x) + (3 + √3) / 4 * f (2 * x - 1) ∧
      cascade f (x + 1) = (3 + √3) / 4 * f (2 * x + 1) + (3 - √3) / 4 * f (2 * x)
        + (1 - √3) / 4 * f (2 * x - 1) ∧
      cascade f (x + 2) = (1 - √3) / 4 * f (2 * x + 1) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [cascade_apply, hle (2 * x - 2) (by linarith), hle (2 * x - 3) (by linarith)]
    ring
  · have e0 : f (2 * (x + 1)) = f (2 * x + 2) := by congr 1; ring
    have e1 : f (2 * (x + 1) - 1) = f (2 * x + 1) := by congr 1; ring
    have e2 : f (2 * (x + 1) - 2) = f (2 * x) := by congr 1; ring
    have e3 : f (2 * (x + 1) - 3) = f (2 * x - 1) := by congr 1; ring
    rw [cascade_apply, e0, e1, e2, e3, hge (2 * x + 2) (by linarith)]
    ring
  · have e0 : f (2 * (x + 2)) = f (2 * x + 4) := by congr 1; ring
    have e1 : f (2 * (x + 2) - 1) = f (2 * x + 3) := by congr 1; ring
    have e2 : f (2 * (x + 2) - 2) = f (2 * x + 2) := by congr 1; ring
    have e3 : f (2 * (x + 2) - 3) = f (2 * x + 1) := by congr 1; ring
    rw [cascade_apply, e0, e1, e2, e3, hge (2 * x + 4) (by linarith),
      hge (2 * x + 3) (by linarith), hge (2 * x + 2) (by linarith)]
    ring

end Relations

/-! ### The invariants of the iteration -/

/-- The properties the cascade iteration preserves: continuity, vanishing off `[0,3]`, the values
`(1±√3)/2` at `1` and `2`, and the partition of unity `f x + f (x+1) + f (x+2) = 1` on `[0,1]`. -/
structure IsApprox (f : ℝ → ℝ) : Prop where
  continuous : Continuous f
  zero_of_le : ∀ x : ℝ, x ≤ 0 → f x = 0
  zero_of_ge : ∀ x : ℝ, 3 ≤ x → f x = 0
  val_one : f 1 = (1 + √3) / 2
  val_two : f 2 = (1 - √3) / 2
  sum_eq_one : ∀ x ∈ Icc (0 : ℝ) 1, f x + f (x + 1) + f (x + 2) = 1

namespace IsApprox

variable {f : ℝ → ℝ} (h : IsApprox f)
include h

theorem val_zero : f 0 = 0 := h.zero_of_le 0 le_rfl

theorem val_three : f 3 = 0 := h.zero_of_ge 3 le_rfl

theorem eq_zero_of_lt_or_gt {x : ℝ} (hx : x < 0 ∨ 3 < x) : f x = 0 := by
  rcases hx with hx | hx
  · exact h.zero_of_le x hx.le
  · exact h.zero_of_ge x hx.le

/-- The cascade operator preserves all the invariants. -/
theorem cascade : IsApprox (Daubechies.cascade f) := by
  refine ⟨cascade_continuous h.continuous, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [cascade_apply, h.zero_of_le (2 * x) (by linarith), h.zero_of_le (2 * x - 1) (by linarith),
      h.zero_of_le (2 * x - 2) (by linarith), h.zero_of_le (2 * x - 3) (by linarith)]
    ring
  · intro x hx
    rw [cascade_apply, h.zero_of_ge (2 * x) (by linarith), h.zero_of_ge (2 * x - 1) (by linarith),
      h.zero_of_ge (2 * x - 2) (by linarith), h.zero_of_ge (2 * x - 3) (by linarith)]
    ring
  · have e0 : f (2 * (1 : ℝ)) = f 2 := by congr 1; ring
    have e1 : f (2 * (1 : ℝ) - 1) = f 1 := by congr 1; ring
    have e2 : f (2 * (1 : ℝ) - 2) = f 0 := by congr 1; ring
    rw [cascade_apply, e0, e1, e2, h.val_one, h.val_two, h.val_zero,
      h.zero_of_le (2 * (1 : ℝ) - 3) (by norm_num)]
    ring
  · have e0 : f (2 * (2 : ℝ)) = f 4 := by congr 1; ring
    have e1 : f (2 * (2 : ℝ) - 1) = f 3 := by congr 1; ring
    have e2 : f (2 * (2 : ℝ) - 2) = f 2 := by congr 1; ring
    have e3 : f (2 * (2 : ℝ) - 3) = f 1 := by congr 1; ring
    rw [cascade_apply, e0, e1, e2, e3, h.val_one, h.val_two, h.val_three,
      h.zero_of_ge (4 : ℝ) (by norm_num)]
    ring
  · rintro x ⟨hx0, hx1⟩
    rcases le_total x (1 / 2) with hh | hh
    · obtain ⟨e1, e2, e3⟩ := cascade_left h.zero_of_le h.zero_of_ge hx0 hh
      rw [e1, e2, e3]
      linear_combination h.sum_eq_one (2 * x) ⟨by linarith, by linarith⟩
    · obtain ⟨e1, e2, e3⟩ := cascade_right h.zero_of_le h.zero_of_ge hh hx1
      have hs := h.sum_eq_one (2 * x - 1) ⟨by linarith, by linarith⟩
      have c1 : f (2 * x - 1 + 1) = f (2 * x) := by congr 1; ring
      have c2 : f (2 * x - 1 + 2) = f (2 * x + 1) := by congr 1; ring
      rw [c1, c2] at hs
      rw [e1, e2, e3]
      linear_combination hs

end IsApprox

/-! ### The contraction estimate -/

/-- **The joint-spectral-radius bound for the `D4` mask.**  If `h` vanishes off `[0,3]`, has
`h y + h (y+1) + h (y+2) = 0` on `[0,1]`, and satisfies `|h y| ≤ B` and `2 |h (y+2)| ≤ B` there,
then the same bounds hold for `cascade h` with `B` replaced by `(√3/2) B`.

This is the estimate that makes the cascade iteration converge; `√3/2 < 1` is what matters. -/
theorem cascade_bound {h : ℝ → ℝ} (hle : ∀ x : ℝ, x ≤ 0 → h x = 0)
    (hge : ∀ x : ℝ, 3 ≤ x → h x = 0) (hsum : ∀ x ∈ Icc (0 : ℝ) 1, h x + h (x + 1) + h (x + 2) = 0)
    {B : ℝ} (hb1 : ∀ x ∈ Icc (0 : ℝ) 1, |h x| ≤ B) (hb2 : ∀ x ∈ Icc (0 : ℝ) 1, 2 * |h (x + 2)| ≤ B)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    |cascade h x| ≤ √3 / 2 * B ∧ 2 * |cascade h (x + 2)| ≤ √3 / 2 * B := by
  obtain ⟨hx0, hx1⟩ := hx
  have hB : 0 ≤ B := le_trans (abs_nonneg _) (hb1 0 ⟨le_rfl, by norm_num⟩)
  have hs1 := one_lt_sqrt3
  have hs2 := sqrt3_lt_two
  rcases le_total x (1 / 2) with hh | hh
  · have hmem : (2 * x) ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    obtain ⟨e1, -, e3⟩ := cascade_left hle hge hx0 hh
    have ha : |h (2 * x)| ≤ B := hb1 _ hmem
    have hc : |h (2 * x + 2)| ≤ B / 2 := by
      have hb' : 2 * |h (2 * x + 2)| ≤ B := hb2 _ hmem
      linarith
    constructor
    · rw [e1, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ (1 + √3) / 4)]
      nlinarith [mul_nonneg (sub_nonneg.mpr ha) (by linarith : (0 : ℝ) ≤ 1 + √3),
        mul_nonneg hB (by linarith : (0 : ℝ) ≤ √3 - 1)]
    · have key : cascade h (x + 2) = 1 / 2 * h (2 * x + 2) + (√3 - 1) / 4 * h (2 * x) := by
        rw [e3]
        linear_combination ((1 - √3) / 4) * hsum (2 * x) hmem
      rw [key]
      have habs : |1 / 2 * h (2 * x + 2) + (√3 - 1) / 4 * h (2 * x)|
          ≤ 1 / 2 * |h (2 * x + 2)| + (√3 - 1) / 4 * |h (2 * x)| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2),
          abs_of_nonneg (by linarith : (0 : ℝ) ≤ (√3 - 1) / 4)]
      nlinarith [mul_nonneg (sub_nonneg.mpr ha) (by linarith : (0 : ℝ) ≤ √3 - 1)]
  · have hmem : (2 * x - 1) ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    obtain ⟨e1, -, e3⟩ := cascade_right hle hge hh hx1
    have ha : |h (2 * x - 1)| ≤ B := hb1 _ hmem
    have hc : |h (2 * x + 1)| ≤ B / 2 := by
      have hb' : 2 * |h (2 * x - 1 + 2)| ≤ B := hb2 _ hmem
      have he : h (2 * x - 1 + 2) = h (2 * x + 1) := by congr 1; ring
      rw [he] at hb'
      linarith
    have hsum' : h (2 * x - 1) + h (2 * x) + h (2 * x + 1) = 0 := by
      have hz := hsum (2 * x - 1) hmem
      have c1 : h (2 * x - 1 + 1) = h (2 * x) := by congr 1; ring
      have c2 : h (2 * x - 1 + 2) = h (2 * x + 1) := by congr 1; ring
      rw [c1, c2] at hz
      exact hz
    constructor
    · have key : cascade h x = 1 / 2 * h (2 * x - 1) + -((1 + √3) / 4) * h (2 * x + 1) := by
        rw [e1]
        linear_combination ((1 + √3) / 4) * hsum'
      rw [key]
      have habs : |1 / 2 * h (2 * x - 1) + -((1 + √3) / 4) * h (2 * x + 1)|
          ≤ 1 / 2 * |h (2 * x - 1)| + (1 + √3) / 4 * |h (2 * x + 1)| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2),
          abs_of_nonpos (by linarith : -((1 + √3) / 4) ≤ 0)]
        linarith
      nlinarith [mul_nonneg (sub_nonneg.mpr hc) (by linarith : (0 : ℝ) ≤ 1 + √3),
        sqrt3_mul_self, mul_nonneg hB (by nlinarith [sqrt3_mul_self] : (0 : ℝ) ≤ 3 * √3 - 5)]
    · rw [e3, abs_mul, abs_of_nonpos (by linarith : (1 - √3) / 4 ≤ 0)]
      nlinarith [mul_nonneg (sub_nonneg.mpr hc) (by linarith : (0 : ℝ) ≤ √3 - 1),
        abs_nonneg (h (2 * x + 1))]

/-! ### The starting function of the iteration -/

/-- The unit hat function `max 0 (1 - |t|)`, supported on `[-1, 1]`. -/
def hat (t : ℝ) : ℝ := max 0 (1 - |t|)

theorem hat_continuous : Continuous hat := by
  change Continuous fun t => max 0 (1 - |t|)
  fun_prop

theorem hat_of_one_le {t : ℝ} (ht : 1 ≤ |t|) : hat t = 0 := max_eq_left (by linarith)

theorem hat_of_le_one {t : ℝ} (ht : |t| ≤ 1) : hat t = 1 - |t| := max_eq_right (by linarith)

/-- The starting function of the cascade iteration: the piecewise-linear function with knots at
`0, 1, 2, 3` and values `0, (1+√3)/2, (1-√3)/2, 0` there.  It already satisfies every invariant of
`IsApprox`, the partition of unity included. -/
def approx0 (x : ℝ) : ℝ := (1 + √3) / 2 * hat (x - 1) + (1 - √3) / 2 * hat (x - 2)

theorem approx0_apply (x : ℝ) :
    approx0 x = (1 + √3) / 2 * hat (x - 1) + (1 - √3) / 2 * hat (x - 2) := rfl

/-- The starting function of the iteration already satisfies every invariant, which is the point of
placing its two hat functions at `1` and `2` with the prescribed heights. -/
theorem approx0_isApprox : IsApprox approx0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · change Continuous fun x => (1 + √3) / 2 * hat (x - 1) + (1 - √3) / 2 * hat (x - 2)
    exact ((hat_continuous.comp (continuous_id.sub continuous_const)).const_mul _).add
      ((hat_continuous.comp (continuous_id.sub continuous_const)).const_mul _)
  · intro x hx
    rw [approx0_apply, hat_of_one_le (t := x - 1) (by rw [abs_of_nonpos (by linarith)]; linarith),
      hat_of_one_le (t := x - 2) (by rw [abs_of_nonpos (by linarith)]; linarith)]
    ring
  · intro x hx
    rw [approx0_apply, hat_of_one_le (t := x - 1) (by rw [abs_of_nonneg (by linarith)]; linarith),
      hat_of_one_le (t := x - 2) (by rw [abs_of_nonneg (by linarith)]; linarith)]
    ring
  · have e1 : hat ((1 : ℝ) - 1) = 1 := by
      rw [show (1 : ℝ) - 1 = 0 by norm_num, hat_of_le_one (t := 0) (by norm_num)]
      norm_num
    have e2 : hat ((1 : ℝ) - 2) = 0 := by
      refine hat_of_one_le (t := (1 : ℝ) - 2) ?_
      rw [show (1 : ℝ) - 2 = -1 by norm_num]
      norm_num
    rw [approx0_apply, e1, e2]
    ring
  · have e1 : hat ((2 : ℝ) - 1) = 0 := by
      refine hat_of_one_le (t := (2 : ℝ) - 1) ?_
      rw [show (2 : ℝ) - 1 = 1 by norm_num]
      norm_num
    have e2 : hat ((2 : ℝ) - 2) = 1 := by
      rw [show (2 : ℝ) - 2 = 0 by norm_num, hat_of_le_one (t := 0) (by norm_num)]
      norm_num
    rw [approx0_apply, e1, e2]
    ring
  · rintro x ⟨hx0, hx1⟩
    have a1 : hat (x - 1) = x := by
      rw [hat_of_le_one (t := x - 1) (by rw [abs_of_nonpos (by linarith)]; linarith),
        abs_of_nonpos (by linarith : x - 1 ≤ 0)]
      ring
    have a2 : hat (x - 2) = 0 :=
      hat_of_one_le (t := x - 2) (by rw [abs_of_nonpos (by linarith)]; linarith)
    have b1 : hat (x + 1 - 1) = 1 - x := by
      have e : x + 1 - 1 = x := by ring
      rw [e, hat_of_le_one (t := x) (by rw [abs_of_nonneg hx0]; linarith), abs_of_nonneg hx0]
    have b2 : hat (x + 1 - 2) = x := by
      have e : x + 1 - 2 = x - 1 := by ring
      rw [e, a1]
    have c1 : hat (x + 2 - 1) = 0 := by
      have e : x + 2 - 1 = x + 1 := by ring
      rw [e]
      exact hat_of_one_le (t := x + 1) (by rw [abs_of_nonneg (by linarith)]; linarith)
    have c2 : hat (x + 2 - 2) = 1 - x := by
      have e : x + 2 - 2 = x := by ring
      rw [e, hat_of_le_one (t := x) (by rw [abs_of_nonneg hx0]; linarith), abs_of_nonneg hx0]
    rw [approx0_apply, approx0_apply, approx0_apply, a1, a2, b1, b2, c1, c2]
    ring

/-! ### The cascade iterates and their increments -/

/-- The cascade iterates started from `approx0`. -/
def approxSeq : ℕ → ℝ → ℝ
  | 0 => approx0
  | n + 1 => cascade (approxSeq n)

theorem approxSeq_isApprox : ∀ n : ℕ, IsApprox (approxSeq n)
  | 0 => approx0_isApprox
  | n + 1 => (approxSeq_isApprox n).cascade

/-- The increment of the cascade iteration. -/
def delta (n : ℕ) (x : ℝ) : ℝ := approxSeq (n + 1) x - approxSeq n x

theorem delta_apply (n : ℕ) (x : ℝ) : delta n x = approxSeq (n + 1) x - approxSeq n x := rfl

/-- The increments obey the cascade recurrence themselves, by linearity of `cascade`. This is what
turns the contraction estimate `cascade_bound` into geometric decay. -/
theorem delta_succ (n : ℕ) : delta (n + 1) = cascade (delta n) := by
  have h : delta n = fun x => approxSeq (n + 1) x - approxSeq n x := rfl
  rw [h, cascade_sub]
  rfl

theorem delta_continuous (n : ℕ) : Continuous (delta n) :=
  ((approxSeq_isApprox (n + 1)).continuous).sub ((approxSeq_isApprox n).continuous)

theorem delta_zero_of_le (n : ℕ) (x : ℝ) (hx : x ≤ 0) : delta n x = 0 := by
  rw [delta_apply, (approxSeq_isApprox (n + 1)).zero_of_le x hx,
    (approxSeq_isApprox n).zero_of_le x hx, sub_zero]

theorem delta_zero_of_ge (n : ℕ) (x : ℝ) (hx : 3 ≤ x) : delta n x = 0 := by
  rw [delta_apply, (approxSeq_isApprox (n + 1)).zero_of_ge x hx,
    (approxSeq_isApprox n).zero_of_ge x hx, sub_zero]

/-- The increments lie in the plane `v₀ + v₁ + v₂ = 0`, both iterates having the same partition of
unity. This is the subspace on which the two cascade matrices contract. -/
theorem delta_sum (n : ℕ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    delta n x + delta n (x + 1) + delta n (x + 2) = 0 := by
  have h1 := (approxSeq_isApprox (n + 1)).sum_eq_one x hx
  have h2 := (approxSeq_isApprox n).sum_eq_one x hx
  simp only [delta_apply]
  linarith

theorem delta_val_one (n : ℕ) : delta n 1 = 0 := by
  rw [delta_apply, (approxSeq_isApprox (n + 1)).val_one, (approxSeq_isApprox n).val_one, sub_self]

theorem delta_val_two (n : ℕ) : delta n 2 = 0 := by
  rw [delta_apply, (approxSeq_isApprox (n + 1)).val_two, (approxSeq_isApprox n).val_two, sub_self]

/-! ### Geometric decay of the increments -/

private theorem delta_bound_step {B : ℝ}
    (h0 : ∀ x ∈ Icc (0 : ℝ) 1, |delta 0 x| ≤ B)
    (h0' : ∀ x ∈ Icc (0 : ℝ) 1, 2 * |delta 0 (x + 2)| ≤ B) (n : ℕ) :
    ∀ x ∈ Icc (0 : ℝ) 1,
      |delta n x| ≤ (√3 / 2) ^ n * B ∧ 2 * |delta n (x + 2)| ≤ (√3 / 2) ^ n * B := by
  induction n with
  | zero =>
    intro x hx
    simpa using ⟨h0 x hx, h0' x hx⟩
  | succ n ih =>
    intro x hx
    have hb1 : ∀ y ∈ Icc (0 : ℝ) 1, |delta n y| ≤ (√3 / 2) ^ n * B := fun y hy => (ih y hy).1
    have hb2 : ∀ y ∈ Icc (0 : ℝ) 1, 2 * |delta n (y + 2)| ≤ (√3 / 2) ^ n * B :=
      fun y hy => (ih y hy).2
    have hkey := cascade_bound (delta_zero_of_le n) (delta_zero_of_ge n)
      (fun y hy => delta_sum n hy) hb1 hb2 hx
    rw [delta_succ]
    constructor
    · refine hkey.1.trans (le_of_eq ?_)
      ring
    · refine hkey.2.trans (le_of_eq ?_)
      ring

private theorem exists_delta_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (n : ℕ) (x : ℝ), |delta n x| ≤ (√3 / 2) ^ n * B := by
  obtain ⟨C, hC⟩ := IsCompact.exists_bound_of_continuousOn (s := Icc (0 : ℝ) 3) isCompact_Icc
    (f := delta 0) (delta_continuous 0).continuousOn
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 0 ⟨le_rfl, by norm_num⟩)
  have h0 : ∀ x ∈ Icc (0 : ℝ) 1, |delta 0 x| ≤ 2 * C := by
    rintro x ⟨hx0, hx1⟩
    have := hC x ⟨hx0, by linarith⟩
    rw [Real.norm_eq_abs] at this
    linarith
  have h0' : ∀ x ∈ Icc (0 : ℝ) 1, 2 * |delta 0 (x + 2)| ≤ 2 * C := by
    rintro x ⟨hx0, hx1⟩
    have := hC (x + 2) ⟨by linarith, by linarith⟩
    rw [Real.norm_eq_abs] at this
    linarith
  refine ⟨3 * C, by linarith, fun n x => ?_⟩
  have hmain := delta_bound_step h0 h0' n
  have hpow : 0 ≤ (√3 / 2) ^ n := by positivity
  rcases le_or_gt x 0 with hx | hx
  · rw [delta_zero_of_le n x hx, abs_zero]
    have : 0 ≤ (√3 / 2) ^ n * (3 * C) := by positivity
    linarith
  rcases le_or_gt 3 x with hx3 | hx3
  · rw [delta_zero_of_ge n x hx3, abs_zero]
    have : 0 ≤ (√3 / 2) ^ n * (3 * C) := by positivity
    linarith
  rcases le_or_gt x 1 with h1 | h1
  · have := (hmain x ⟨hx.le, h1⟩).1
    nlinarith [mul_nonneg hpow hC0]
  rcases le_or_gt x 2 with h2 | h2
  · have hmem : x - 1 ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    have hs := delta_sum n hmem
    have c1 : delta n (x - 1 + 1) = delta n x := by congr 1; ring
    have c2 : delta n (x - 1 + 2) = delta n (x + 1) := by congr 1; ring
    rw [c1, c2] at hs
    have hA := (hmain (x - 1) hmem).1
    have hB2 := (hmain (x - 1) hmem).2
    rw [c2] at hB2
    have habs : |delta n x| ≤ |delta n (x - 1)| + |delta n (x + 1)| := by
      have e : delta n x = -delta n (x - 1) + -delta n (x + 1) := by linarith
      rw [e]
      refine (abs_add_le _ _).trans ?_
      rw [abs_neg, abs_neg]
    nlinarith [abs_nonneg (delta n (x - 1)), abs_nonneg (delta n (x + 1))]
  · have hmem : x - 2 ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    have hB2 := (hmain (x - 2) hmem).2
    have c3 : delta n (x - 2 + 2) = delta n x := by congr 1; ring
    rw [c3] at hB2
    nlinarith [abs_nonneg (delta n x), mul_nonneg hpow hC0]

/-! ### The limit -/

private theorem sqrt3_div_two_lt_one : √3 / 2 < 1 := by linarith [sqrt3_lt_two]

private theorem sqrt3_div_two_nonneg : (0 : ℝ) ≤ √3 / 2 := by positivity

/-- The **Daubechies `D4` scaling function**: the uniform limit of the cascade iterates. -/
def scalingFun (x : ℝ) : ℝ := approx0 x + ∑' n : ℕ, delta n x

theorem scalingFun_apply (x : ℝ) : scalingFun x = approx0 x + ∑' n : ℕ, delta n x := rfl

private theorem summable_delta_bound {B : ℝ} : Summable (fun n : ℕ => (√3 / 2) ^ n * B) :=
  ((summable_geometric_of_lt_one sqrt3_div_two_nonneg sqrt3_div_two_lt_one)).mul_right B

private theorem summable_delta (x : ℝ) : Summable (fun n : ℕ => delta n x) := by
  obtain ⟨B, -, hB⟩ := exists_delta_bound
  exact Summable.of_norm_bounded summable_delta_bound (fun n => by
    rw [Real.norm_eq_abs]; exact hB n x)

/-- The cascade iterates converge pointwise to the scaling function, the telescoping sum of the
increments being exactly `approxSeq N - approx0`. -/
theorem approxSeq_tendsto (x : ℝ) :
    Filter.Tendsto (fun N : ℕ => approxSeq N x) Filter.atTop (nhds (scalingFun x)) := by
  have hsum := (summable_delta x).hasSum.tendsto_sum_nat
  have he : ∀ N : ℕ, approx0 x + ∑ n ∈ Finset.range N, delta n x = approxSeq N x := by
    intro N
    have := Finset.sum_range_sub (fun n : ℕ => approxSeq n x) N
    simp only [← delta_apply] at this
    rw [this]
    change approx0 x + (approxSeq N x - approxSeq 0 x) = approxSeq N x
    have h0 : approxSeq 0 x = approx0 x := rfl
    rw [h0]
    ring
  have hconst : Filter.Tendsto (fun _ : ℕ => approx0 x) Filter.atTop (nhds (approx0 x)) :=
    tendsto_const_nhds
  have h2 := hconst.add hsum
  rw [scalingFun_apply]
  simpa only [he] using h2

/-- The scaling function is continuous: the increments are bounded by a geometric series, so the
cascade iterates converge *uniformly*. -/
theorem scalingFun_continuous : Continuous scalingFun := by
  obtain ⟨B, -, hB⟩ := exists_delta_bound
  refine (approx0_isApprox.continuous).add (continuous_tsum delta_continuous
    (u := fun n : ℕ => (√3 / 2) ^ n * B) summable_delta_bound (fun n x => ?_))
  rw [Real.norm_eq_abs]
  exact hB n x

/-- The limit inherits every invariant of the iteration: it is continuous, vanishes off `[0,3]`,
takes the values `(1±√3)/2` at `1` and `2`, and satisfies the partition of unity. -/
theorem scalingFun_isApprox : IsApprox scalingFun := by
  refine ⟨scalingFun_continuous, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have : ∀ n : ℕ, delta n x = 0 := fun n => delta_zero_of_le n x hx
    simp only [scalingFun, this, tsum_zero, add_zero]
    exact approx0_isApprox.zero_of_le x hx
  · intro x hx
    have : ∀ n : ℕ, delta n x = 0 := fun n => delta_zero_of_ge n x hx
    simp only [scalingFun, this, tsum_zero, add_zero]
    exact approx0_isApprox.zero_of_ge x hx
  · simp only [scalingFun, delta_val_one, tsum_zero, add_zero]
    exact approx0_isApprox.val_one
  · simp only [scalingFun, delta_val_two, tsum_zero, add_zero]
    exact approx0_isApprox.val_two
  · intro x hx
    have hconst : Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop (nhds 1) := tendsto_const_nhds
    refine tendsto_nhds_unique ?_ hconst
    have := ((approxSeq_tendsto x).add (approxSeq_tendsto (x + 1))).add
      (approxSeq_tendsto (x + 2))
    refine this.congr (fun N => ?_)
    exact (approxSeq_isApprox N).sum_eq_one x hx

/-- The scaling function satisfies the four-term scaling equation (the `D4` refinement
equation). -/
theorem scalingFun_refine (x : ℝ) :
    scalingFun x = (1 + √3) / 4 * scalingFun (2 * x) + (3 + √3) / 4 * scalingFun (2 * x - 1)
      + (3 - √3) / 4 * scalingFun (2 * x - 2) + (1 - √3) / 4 * scalingFun (2 * x - 3) := by
  have hlim : Filter.Tendsto (fun N : ℕ => cascade (approxSeq N) x) Filter.atTop
      (nhds (cascade scalingFun x)) := by
    simp only [cascade_apply]
    exact ((((approxSeq_tendsto (2 * x)).const_mul _).add
      ((approxSeq_tendsto (2 * x - 1)).const_mul _)).add
      ((approxSeq_tendsto (2 * x - 2)).const_mul _)).add
      ((approxSeq_tendsto (2 * x - 3)).const_mul _)
  have hlim2 : Filter.Tendsto (fun N : ℕ => cascade (approxSeq N) x) Filter.atTop
      (nhds (scalingFun x)) := (approxSeq_tendsto x).comp (Filter.tendsto_add_atTop_nat 1)
  rw [← cascade_apply]
  exact tendsto_nhds_unique hlim2 hlim

/-! ### Values at the first dyadic points -/

theorem cascade_scalingFun (x : ℝ) : cascade scalingFun x = scalingFun x :=
  (scalingFun_refine x).symm

/-- `φ(1/2) = (2 + √3)/4`, read off the refinement equation at `1/2`, where only the term
`f(2x - 1) = f 0` and the term `f(2x) = f 1` survive. -/
theorem scalingFun_one_half : scalingFun (1 / 2) = (2 + √3) / 4 := by
  have h := scalingFun_refine (1 / 2)
  rw [show (2 : ℝ) * (1 / 2) = 1 by norm_num, show (1 : ℝ) - 1 = 0 by norm_num,
    show (1 : ℝ) - 2 = -1 by norm_num, show (1 : ℝ) - 3 = -2 by norm_num,
    scalingFun_isApprox.val_one, scalingFun_isApprox.val_zero,
    scalingFun_isApprox.zero_of_le (-1) (by norm_num),
    scalingFun_isApprox.zero_of_le (-2) (by norm_num)] at h
  rw [h]
  linear_combination sqrt3_mul_self / 8

/-- `φ(3/2) = 0`, read off the refinement equation at `3/2`. -/
theorem scalingFun_three_halves : scalingFun (3 / 2) = 0 := by
  have h := scalingFun_refine (3 / 2)
  rw [show (2 : ℝ) * (3 / 2) = 3 by norm_num, show (3 : ℝ) - 1 = 2 by norm_num,
    show (3 : ℝ) - 2 = 1 by norm_num, show (3 : ℝ) - 3 = 0 by norm_num,
    scalingFun_isApprox.val_one, scalingFun_isApprox.val_two, scalingFun_isApprox.val_zero,
    scalingFun_isApprox.val_three] at h
  rw [h]
  linear_combination (-1 / 4 : ℝ) * sqrt3_mul_self

/-- `φ(5/2) = (2 - √3)/4`, read off the refinement equation at `5/2`. Together with
`scalingFun_one_half` and `scalingFun_three_halves` this gives the three half-integer values that
the span argument behind `scalingFun_support` needs. -/
theorem scalingFun_five_halves : scalingFun (5 / 2) = (2 - √3) / 4 := by
  have h := scalingFun_refine (5 / 2)
  rw [show (2 : ℝ) * (5 / 2) = 5 by norm_num, show (5 : ℝ) - 1 = 4 by norm_num,
    show (5 : ℝ) - 2 = 3 by norm_num, show (5 : ℝ) - 3 = 2 by norm_num,
    scalingFun_isApprox.val_two, scalingFun_isApprox.val_three,
    scalingFun_isApprox.zero_of_ge 4 (by norm_num),
    scalingFun_isApprox.zero_of_ge 5 (by norm_num)] at h
  rw [h]
  linear_combination sqrt3_mul_self / 8

/-! ### Pairing against a covector -/

/-- The pairing of the vector `(φ y, φ (y+1), φ (y+2))` against a covector `(u₀, u₁, u₂)`. -/
private def pairing (u₀ u₁ u₂ y : ℝ) : ℝ :=
  u₀ * scalingFun y + u₁ * scalingFun (y + 1) + u₂ * scalingFun (y + 2)

private theorem pairing_apply (u₀ u₁ u₂ y : ℝ) :
    pairing u₀ u₁ u₂ y = u₀ * scalingFun y + u₁ * scalingFun (y + 1)
      + u₂ * scalingFun (y + 2) := rfl

private theorem refine_left {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    scalingFun x = (1 + √3) / 4 * scalingFun (2 * x) ∧
      scalingFun (x + 1) = (1 + √3) / 4 * scalingFun (2 * x + 2)
        + (3 + √3) / 4 * scalingFun (2 * x + 1) + (3 - √3) / 4 * scalingFun (2 * x) ∧
      scalingFun (x + 2) = (3 - √3) / 4 * scalingFun (2 * x + 2)
        + (1 - √3) / 4 * scalingFun (2 * x + 1) := by
  obtain ⟨e1, e2, e3⟩ := cascade_left scalingFun_isApprox.zero_of_le
    scalingFun_isApprox.zero_of_ge hx0 hx1
  rw [cascade_scalingFun] at e1 e2 e3
  exact ⟨e1, e2, e3⟩

private theorem refine_right {x : ℝ} (hx0 : 1 / 2 ≤ x) (hx1 : x ≤ 1) :
    scalingFun x = (1 + √3) / 4 * scalingFun (2 * x)
        + (3 + √3) / 4 * scalingFun (2 * x - 1) ∧
      scalingFun (x + 1) = (3 + √3) / 4 * scalingFun (2 * x + 1)
        + (3 - √3) / 4 * scalingFun (2 * x) + (1 - √3) / 4 * scalingFun (2 * x - 1) ∧
      scalingFun (x + 2) = (1 - √3) / 4 * scalingFun (2 * x + 1) := by
  obtain ⟨e1, e2, e3⟩ := cascade_right scalingFun_isApprox.zero_of_le
    scalingFun_isApprox.zero_of_ge hx0 hx1
  rw [cascade_scalingFun] at e1 e2 e3
  exact ⟨e1, e2, e3⟩

private theorem pairing_left (u₀ u₁ u₂ : ℝ) {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 2) :
    pairing u₀ u₁ u₂ y = pairing ((1 + √3) / 4 * u₀ + (3 - √3) / 4 * u₁)
      ((3 + √3) / 4 * u₁ + (1 - √3) / 4 * u₂) ((1 + √3) / 4 * u₁ + (3 - √3) / 4 * u₂) (2 * y) := by
  obtain ⟨e1, e2, e3⟩ := refine_left hy0 hy1
  rw [pairing_apply, pairing_apply, e1, e2, e3]
  ring

private theorem pairing_right (u₀ u₁ u₂ : ℝ) {y : ℝ} (hy0 : 1 / 2 ≤ y) (hy1 : y ≤ 1) :
    pairing u₀ u₁ u₂ y = pairing ((3 + √3) / 4 * u₀ + (1 - √3) / 4 * u₁)
      ((1 + √3) / 4 * u₀ + (3 - √3) / 4 * u₁) ((3 + √3) / 4 * u₁ + (1 - √3) / 4 * u₂)
      (2 * y - 1) := by
  obtain ⟨e1, e2, e3⟩ := refine_right hy0 hy1
  have c1 : scalingFun (2 * y - 1 + 1) = scalingFun (2 * y) := by congr 1; ring
  have c2 : scalingFun (2 * y - 1 + 2) = scalingFun (2 * y + 1) := by congr 1; ring
  rw [pairing_apply, pairing_apply, e1, e2, e3, c1, c2]
  ring

/-! ### Injectivity of the transposes, and the span of `w(0), w(1/2), w(1)` -/

private theorem eq_zero_of_mul_eq_zero {u c : ℝ} (hc : c ≠ 0) (h : u * c = 0) : u = 0 := by
  rcases mul_eq_zero.mp h with h' | h'
  · exact h'
  · exact absurd h' hc

private theorem covector_left_eq_zero {u₀ u₁ u₂ : ℝ}
    (e1 : (1 + √3) / 4 * u₀ + (3 - √3) / 4 * u₁ = 0)
    (e2 : (3 + √3) / 4 * u₁ + (1 - √3) / 4 * u₂ = 0)
    (e3 : (1 + √3) / 4 * u₁ + (3 - √3) / 4 * u₂ = 0) : u₀ = 0 ∧ u₁ = 0 ∧ u₂ = 0 := by
  have hs := one_lt_sqrt3
  have hs2 := sqrt3_lt_two
  have h2 : -(1 / 2 : ℝ) * u₂ = 0 := by
    linear_combination ((1 + √3) / 4) * e2 - ((3 + √3) / 4) * e3
  have hu2 : u₂ = 0 := by linarith
  have hu1 : u₁ = 0 :=
    eq_zero_of_mul_eq_zero (c := (3 + √3) / 4) (by intro hc; nlinarith)
      (by linear_combination e2 - ((1 - √3) / 4) * hu2)
  have hu0 : u₀ = 0 :=
    eq_zero_of_mul_eq_zero (c := (1 + √3) / 4) (by intro hc; nlinarith)
      (by linear_combination e1 - ((3 - √3) / 4) * hu1)
  exact ⟨hu0, hu1, hu2⟩

private theorem covector_right_eq_zero {u₀ u₁ u₂ : ℝ}
    (e1 : (3 + √3) / 4 * u₀ + (1 - √3) / 4 * u₁ = 0)
    (e2 : (1 + √3) / 4 * u₀ + (3 - √3) / 4 * u₁ = 0)
    (e3 : (3 + √3) / 4 * u₁ + (1 - √3) / 4 * u₂ = 0) : u₀ = 0 ∧ u₁ = 0 ∧ u₂ = 0 := by
  have hs := one_lt_sqrt3
  have hs2 := sqrt3_lt_two
  have h2 : -(1 / 2 : ℝ) * u₁ = 0 := by
    linear_combination ((1 + √3) / 4) * e1 - ((3 + √3) / 4) * e2
  have hu1 : u₁ = 0 := by linarith
  have hu0 : u₀ = 0 :=
    eq_zero_of_mul_eq_zero (c := (3 + √3) / 4) (by intro hc; nlinarith)
      (by linear_combination e1 - ((1 - √3) / 4) * hu1)
  have hu2 : u₂ = 0 :=
    eq_zero_of_mul_eq_zero (c := (1 - √3) / 4) (by intro hc; nlinarith)
      (by linear_combination e3 - ((3 + √3) / 4) * hu1)
  exact ⟨hu0, hu1, hu2⟩

private theorem covector_eq_zero {u₀ u₁ u₂ : ℝ} (h0 : pairing u₀ u₁ u₂ 0 = 0)
    (hh : pairing u₀ u₁ u₂ (1 / 2) = 0) (h1 : pairing u₀ u₁ u₂ 1 = 0) :
    u₀ = 0 ∧ u₁ = 0 ∧ u₂ = 0 := by
  have hs := one_lt_sqrt3
  have hs2 := sqrt3_lt_two
  rw [pairing_apply, show (0 : ℝ) + 1 = 1 by norm_num, show (0 : ℝ) + 2 = 2 by norm_num,
    scalingFun_isApprox.val_zero, scalingFun_isApprox.val_one,
    scalingFun_isApprox.val_two] at h0
  rw [pairing_apply, show (1 : ℝ) / 2 + 1 = 3 / 2 by norm_num,
    show (1 : ℝ) / 2 + 2 = 5 / 2 by norm_num, scalingFun_one_half, scalingFun_three_halves,
    scalingFun_five_halves] at hh
  rw [pairing_apply, show (1 : ℝ) + 1 = 2 by norm_num, show (1 : ℝ) + 2 = 3 by norm_num,
    scalingFun_isApprox.val_one, scalingFun_isApprox.val_two,
    scalingFun_isApprox.val_three] at h1
  have key : (4 - 2 * √3) * u₂ = 0 := by
    linear_combination (1 - √3) * h0 - (1 + √3) * h1 + 4 * hh + ((u₀ - u₂) / 2) * sqrt3_mul_self
  have hu2 : u₂ = 0 := by
    rcases mul_eq_zero.mp key with h | h
    · exact absurd h (by intro hc; linarith)
    · exact h
  have hu1 : u₁ = 0 :=
    eq_zero_of_mul_eq_zero (c := (1 + √3) / 2) (by intro hc; nlinarith)
      (by linear_combination h0 - ((1 - √3) / 2) * hu2)
  have hu0 : u₀ = 0 :=
    eq_zero_of_mul_eq_zero (c := (1 + √3) / 2) (by intro hc; nlinarith)
      (by linear_combination h1 - ((1 - √3) / 2) * hu1)
  exact ⟨hu0, hu1, hu2⟩

/-! ### No covector pairing vanishes on a dyadic interval -/

private theorem pairing_dyadic : ∀ (n m : ℕ), m < 2 ^ n → ∀ u₀ u₁ u₂ : ℝ,
    (∀ y : ℝ, (m : ℝ) ≤ y * 2 ^ n → y * 2 ^ n ≤ (m : ℝ) + 1 → pairing u₀ u₁ u₂ y = 0) →
    u₀ = 0 ∧ u₁ = 0 ∧ u₂ = 0 := by
  intro n
  induction n with
  | zero =>
    intro m hm u₀ u₁ u₂ h
    have hm0 : m = 0 := by simpa using hm
    subst hm0
    refine covector_eq_zero (h 0 ?_ ?_) (h (1 / 2) ?_ ?_) (h 1 ?_ ?_) <;> norm_num
  | succ n ih =>
    intro m hm u₀ u₁ u₂ h
    have hpow : (0 : ℝ) < 2 ^ n := by positivity
    have hsplit : (2 : ℝ) ^ (n + 1) = 2 * 2 ^ n := by ring
    have hmnn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    rcases le_or_gt (m + 1) (2 ^ n) with hcase | hcase
    · have hmn : m < 2 ^ n := by omega
      have hmr : (m : ℝ) + 1 ≤ 2 ^ n := by exact_mod_cast hcase
      obtain ⟨a0, a1, a2⟩ := ih m hmn ((1 + √3) / 4 * u₀ + (3 - √3) / 4 * u₁)
        ((3 + √3) / 4 * u₁ + (1 - √3) / 4 * u₂) ((1 + √3) / 4 * u₁ + (3 - √3) / 4 * u₂)
        (by
          intro z hz1 hz2
          have hz0 : 0 ≤ z := by nlinarith
          have hzle : z ≤ 1 := by nlinarith
          have hkey := pairing_left u₀ u₁ u₂ (y := z / 2) (by linarith) (by linarith)
          rw [show (2 : ℝ) * (z / 2) = z by ring] at hkey
          rw [← hkey]
          refine h (z / 2) ?_ ?_
          · rw [hsplit]; nlinarith
          · rw [hsplit]; nlinarith)
      exact covector_left_eq_zero a0 a1 a2
    · have hmn : m - 2 ^ n < 2 ^ n := by omega
      have hmr : ((m - 2 ^ n : ℕ) : ℝ) + 1 ≤ 2 ^ n := by
        have hnat : (m - 2 ^ n) + 1 ≤ 2 ^ n := by
          have h2 : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
          omega
        exact_mod_cast hnat
      have hcast : (m : ℝ) = ((m - 2 ^ n : ℕ) : ℝ) + 2 ^ n := by
        have hnat : m = (m - 2 ^ n) + 2 ^ n := by omega
        rw [show ((m : ℕ) : ℝ) = (((m - 2 ^ n) + 2 ^ n : ℕ) : ℝ) by rw [← hnat]]
        push_cast
        ring
      have hmnn' : (0 : ℝ) ≤ ((m - 2 ^ n : ℕ) : ℝ) := Nat.cast_nonneg _
      obtain ⟨a0, a1, a2⟩ := ih (m - 2 ^ n) hmn ((3 + √3) / 4 * u₀ + (1 - √3) / 4 * u₁)
        ((1 + √3) / 4 * u₀ + (3 - √3) / 4 * u₁) ((3 + √3) / 4 * u₁ + (1 - √3) / 4 * u₂)
        (by
          intro z hz1 hz2
          have hz0 : 0 ≤ z := by nlinarith
          have hzle : z ≤ 1 := by nlinarith
          have hkey := pairing_right u₀ u₁ u₂ (y := (z + 1) / 2) (by linarith) (by linarith)
          rw [show (2 : ℝ) * ((z + 1) / 2) - 1 = z by ring] at hkey
          rw [← hkey]
          refine h ((z + 1) / 2) ?_ ?_
          · rw [hsplit, hcast]; nlinarith
          · rw [hsplit, hcast]; nlinarith)
      exact covector_right_eq_zero a0 a1 a2

private theorem exists_pairing_ne_zero {u₀ u₁ u₂ : ℝ} (hu : ¬(u₀ = 0 ∧ u₁ = 0 ∧ u₂ = 0))
    {a b : ℝ} (hab : a < b) (ha : 0 ≤ a) (hb : b ≤ 1) :
    ∃ y ∈ Icc a b, pairing u₀ u₁ u₂ y ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hba : 0 < b - a := by linarith
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (2 / (b - a)) (by norm_num : (1 : ℝ) < 2)
  have hpow : (0 : ℝ) < 2 ^ n := by positivity
  have hn' : 2 < (b - a) * 2 ^ n := by
    rw [div_lt_iff₀ hba] at hn
    linarith
  have hmle : a * 2 ^ n ≤ ((⌈a * 2 ^ n⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have hmlt : ((⌈a * 2 ^ n⌉₊ : ℕ) : ℝ) < a * 2 ^ n + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hmb : ((⌈a * 2 ^ n⌉₊ : ℕ) : ℝ) + 1 ≤ b * 2 ^ n := by nlinarith
  have hmn : ⌈a * 2 ^ n⌉₊ < 2 ^ n := by
    have h1 : ((⌈a * 2 ^ n⌉₊ : ℕ) : ℝ) < ((2 ^ n : ℕ) : ℝ) := by push_cast; nlinarith
    exact_mod_cast h1
  refine hu (pairing_dyadic n ⌈a * 2 ^ n⌉₊ hmn u₀ u₁ u₂ ?_)
  intro y hy1 hy2
  refine hcon y ⟨?_, ?_⟩
  · nlinarith
  · nlinarith

/-! ### The support -/

private theorem exists_ne_zero {p q : ℝ} (hpq : p < q) (hp : 0 ≤ p) (hq : q ≤ 3) :
    ∃ y ∈ Icc p q, scalingFun y ≠ 0 := by
  have hr0 : (0 : ℝ) ≤ (p + q) / 2 := by linarith
  have hr3 : (p + q) / 2 < 3 := by linarith
  obtain ⟨k, hk⟩ : ∃ k : ℕ, ⌊(p + q) / 2⌋₊ = k := ⟨_, rfl⟩
  have hjle : (k : ℝ) ≤ (p + q) / 2 := hk ▸ Nat.floor_le hr0
  have hjlt : (p + q) / 2 < (k : ℝ) + 1 := hk ▸ Nat.lt_floor_add_one _
  have hj3 : k < 3 := by
    by_contra hc
    push Not at hc
    have h3 : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hc
    linarith
  obtain ⟨a, b, hab, ha0, hb1, hpa, hbq⟩ :
      ∃ a b : ℝ, a < b ∧ 0 ≤ a ∧ b ≤ 1 ∧ p ≤ a + (k : ℝ) ∧ b + (k : ℝ) ≤ q := by
    refine ⟨max p (k : ℝ) - (k : ℝ), min q ((k : ℝ) + 1) - (k : ℝ), ?_, ?_, ?_, ?_, ?_⟩
    · have h1 : max p (k : ℝ) ≤ (p + q) / 2 := max_le (by linarith) hjle
      have h2 : (p + q) / 2 < min q ((k : ℝ) + 1) := lt_min (by linarith) hjlt
      linarith
    · have := le_max_right p (k : ℝ); linarith
    · have := min_le_right q ((k : ℝ) + 1); linarith
    · have := le_max_left p (k : ℝ); linarith
    · have := min_le_left q ((k : ℝ) + 1); linarith
  interval_cases k
  · norm_num at hpa hbq
    obtain ⟨y, hy, hne⟩ := exists_pairing_ne_zero (u₀ := 1) (u₁ := 0) (u₂ := 0)
      (by simp) hab ha0 hb1
    have hp0 : pairing 1 0 0 y = scalingFun y := by rw [pairing_apply]; ring
    rw [hp0] at hne
    exact ⟨y, ⟨by linarith [hy.1], by linarith [hy.2]⟩, hne⟩
  · norm_num at hpa hbq
    obtain ⟨y, hy, hne⟩ := exists_pairing_ne_zero (u₀ := 0) (u₁ := 1) (u₂ := 0)
      (by simp) hab ha0 hb1
    have hp0 : pairing 0 1 0 y = scalingFun (y + 1) := by rw [pairing_apply]; ring
    rw [hp0] at hne
    exact ⟨y + 1, ⟨by linarith [hy.1], by linarith [hy.2]⟩, hne⟩
  · norm_num at hpa hbq
    obtain ⟨y, hy, hne⟩ := exists_pairing_ne_zero (u₀ := 0) (u₁ := 0) (u₂ := 1)
      (by simp) hab ha0 hb1
    have hp0 : pairing 0 0 1 y = scalingFun (y + 2) := by rw [pairing_apply]; ring
    rw [hp0] at hne
    exact ⟨y + 2, ⟨by linarith [hy.1], by linarith [hy.2]⟩, hne⟩

/-- **The support of the Daubechies `D4` scaling function is exactly `[0, 3]`.**  The inclusion is
by construction; the reverse needs that `φ` cannot vanish identically on a nondegenerate
subinterval of `[0, 3]`, which is `exists_ne_zero`. -/
theorem scalingFun_support : closure (Function.support scalingFun) = Icc 0 3 := by
  refine Subset.antisymm (closure_minimal (fun x hx => ?_) isClosed_Icc) ?_
  · by_contra hc
    simp only [mem_Icc, not_and_or, not_le] at hc
    refine hx (scalingFun_isApprox.eq_zero_of_lt_or_gt ?_)
    rcases hc with hc | hc
    · exact Or.inl hc
    · exact Or.inr hc
  · rintro x ⟨hx0, hx3⟩
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hd : 0 < min (ε / 2) 1 := lt_min (by linarith) one_pos
    have hd2 : min (ε / 2) 1 ≤ ε / 2 := min_le_left _ _
    have hd1 : min (ε / 2) 1 ≤ 1 := min_le_right _ _
    rcases lt_or_ge x 3 with hlt | hge
    · obtain ⟨y, hy, hne⟩ := exists_ne_zero (p := x) (q := min (x + min (ε / 2) 1) 3)
        (lt_min (by linarith) hlt) hx0 (min_le_right _ _)
      refine ⟨y, hne, ?_⟩
      have h1 := hy.1
      have h2 := hy.2.trans (min_le_left (x + min (ε / 2) 1) 3)
      rw [Real.dist_eq, abs_of_nonpos (by linarith)]
      linarith
    · have hx3' : x = 3 := le_antisymm hx3 hge
      subst hx3'
      obtain ⟨y, hy, hne⟩ := exists_ne_zero (p := 3 - min (ε / 2) 1) (q := 3)
        (by linarith) (by linarith) le_rfl
      refine ⟨y, hne, ?_⟩
      have h1 := hy.1
      have h2 := hy.2
      rw [Real.dist_eq, abs_of_nonneg (by linarith)]
      linarith

/-! ### The existence theorem -/

/-- **Existence of the Daubechies `D4` scaling function.**  There is a continuous `φ : ℝ → ℝ`
whose support is exactly `[0, 3]`, satisfying the four-term scaling equation, and normalised by
`φ 1 = (1+√3)/2` and `φ 2 = (1-√3)/2`. -/
theorem exists_scalingFun :
    ∃ φ : ℝ → ℝ, Continuous φ ∧ (∀ x : ℝ, x < 0 ∨ 3 < x → φ x = 0) ∧
      closure (Function.support φ) = Icc 0 3 ∧
      (∀ x : ℝ, φ x = (1 + √3) / 4 * φ (2 * x) + (3 + √3) / 4 * φ (2 * x - 1)
        + (3 - √3) / 4 * φ (2 * x - 2) + (1 - √3) / 4 * φ (2 * x - 3)) ∧
      φ 1 = (1 + √3) / 2 ∧ φ 2 = (1 - √3) / 2 :=
  ⟨scalingFun, scalingFun_continuous, fun _ hx => scalingFun_isApprox.eq_zero_of_lt_or_gt hx,
    scalingFun_support, scalingFun_refine, scalingFun_isApprox.val_one,
    scalingFun_isApprox.val_two⟩

end Daubechies
