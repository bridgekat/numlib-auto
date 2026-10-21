import Numlib.Analysis.Calculus.NormPowerSmoothness
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# A capped quadratic potential

This even convex function agrees with `x² / 2` on `[-1,1]`, interpolates by a cubic
on each adjacent unit interval, and is affine outside `[-2,2]`. A finite difference
of translated absolute cubes makes its global `C²` regularity explicit.
-/

open Filter Topology

noncomputable section

namespace CappedQuadratic

/-- The capped quadratic, expressed as a finite difference of absolute cubes. -/
def value (x : ℝ) : ℝ :=
  (|x - 2| ^ 3 + |x + 2| ^ 3 - |x - 1| ^ 3 - |x + 1| ^ 3 - 14) / 12

/-- The first derivative of the capped quadratic. -/
def first (x : ℝ) : ℝ :=
  ((x - 2) * |x - 2| + (x + 2) * |x + 2| -
    (x - 1) * |x - 1| - (x + 1) * |x + 1|) / 4

/-- The second derivative of the capped quadratic. -/
def second (x : ℝ) : ℝ := max 0 (min 1 (2 - |x|))

/-- The capped quadratic is even. -/
@[simp] theorem value_neg (x : ℝ) : value (-x) = value x := by
  unfold value
  rw [show -x - 2 = -(x + 2) by ring_nf, show -x - 1 = -(x + 1) by ring_nf]
  rw [show -x + 2 = -(x - 2) by ring_nf, show -x + 1 = -(x - 1) by ring_nf]
  simp only [abs_neg]
  ring_nf

/-- The first derivative is odd. -/
@[simp] theorem first_neg (x : ℝ) : first (-x) = -first x := by
  unfold first
  rw [show -x - 2 = -(x + 2) by ring_nf, show -x - 1 = -(x + 1) by ring_nf]
  rw [show -x + 2 = -(x - 2) by ring_nf, show -x + 1 = -(x - 1) by ring_nf]
  simp only [abs_neg]
  ring_nf

/-- The second derivative is even. -/
@[simp] theorem second_neg (x : ℝ) : second (-x) = second x := by
  simp [second]

/-- On the central interval the potential is exactly quadratic. -/
theorem value_eq_of_abs_le_one {x : ℝ} (hx : |x| ≤ 1) : value x = x ^ 2 / 2 := by
  obtain ⟨hl, hu⟩ := abs_le.mp hx
  simp only [value, abs_of_nonpos (show x - 2 ≤ 0 by linarith),
    abs_of_nonneg (show 0 ≤ x + 2 by linarith),
    abs_of_nonpos (show x - 1 ≤ 0 by linarith),
    abs_of_nonneg (show 0 ≤ x + 1 by linarith)]
  ring_nf

/-- On the central interval the first derivative is the identity. -/
theorem first_eq_of_abs_le_one {x : ℝ} (hx : |x| ≤ 1) : first x = x := by
  obtain ⟨hl, hu⟩ := abs_le.mp hx
  simp only [first, abs_of_nonpos (show x - 2 ≤ 0 by linarith),
    abs_of_nonneg (show 0 ≤ x + 2 by linarith),
    abs_of_nonpos (show x - 1 ≤ 0 by linarith),
    abs_of_nonneg (show 0 ≤ x + 1 by linarith)]
  ring_nf

/-- The second derivative equals one on the central interval. -/
theorem second_eq_of_abs_le_one {x : ℝ} (hx : |x| ≤ 1) : second x = 1 := by
  simp [second, min_eq_left (show 1 ≤ 2 - |x| by linarith)]

/-- The cubic interpolation formula between radii one and two. -/
theorem value_eq_of_one_le_abs_le_two {x : ℝ} (hl : 1 ≤ |x|) (hu : |x| ≤ 2) :
    value x = |x| ^ 2 / 2 - (|x| - 1) ^ 3 / 6 := by
  wlog hx : 0 ≤ x generalizing x
  · simpa using this (x := -x) (by simpa) (by simpa) (by linarith)
  rw [abs_of_nonneg hx] at hl hu ⊢
  simp only [value, abs_of_nonpos (show x - 2 ≤ 0 by linarith),
    abs_of_nonneg (show 0 ≤ x + 2 by linarith),
    abs_of_nonneg (show 0 ≤ x - 1 by linarith),
    abs_of_nonneg (show 0 ≤ x + 1 by linarith)]
  ring_nf

/-- Outside radius two the potential grows affinely in the absolute value. -/
theorem value_eq_of_two_le_abs {x : ℝ} (hx : 2 ≤ |x|) :
    value x = 3 * |x| / 2 - 7 / 6 := by
  wlog h : 0 ≤ x generalizing x
  · simpa using this (x := -x) (by simpa) (by linarith)
  rw [abs_of_nonneg h] at hx ⊢
  simp only [value, abs_of_nonneg (show 0 ≤ x - 2 by linarith),
    abs_of_nonneg (show 0 ≤ x + 2 by linarith),
    abs_of_nonneg (show 0 ≤ x - 1 by linarith),
    abs_of_nonneg (show 0 ≤ x + 1 by linarith)]
  ring_nf

/-- The second derivative is the clipped tent function. -/
theorem second_eq_clamp (x : ℝ) : second x = max 0 (min 1 (2 - |x|)) := rfl

/-- The absolute-value finite difference representing the second derivative. -/
theorem second_eq_abs (x : ℝ) :
    second x = (|x - 2| + |x + 2| - |x - 1| - |x + 1|) / 2 := by
  wlog hx : 0 ≤ x generalizing x
  · have h := this (-x) (by linarith)
    rw [second_neg] at h
    rw [show -x - 2 = -(x + 2) by ring_nf, show -x - 1 = -(x + 1) by ring_nf,
      show -x + 2 = -(x - 2) by ring_nf, show -x + 1 = -(x - 1) by ring_nf] at h
    simp only [abs_neg] at h
    linarith
  rcases le_total x 1 with h | h
  · rw [second_eq_of_abs_le_one (by simpa [abs_of_nonneg hx] using h)]
    simp only [abs_of_nonpos (show x - 2 ≤ 0 by linarith),
      abs_of_nonneg (show 0 ≤ x + 2 by linarith),
      abs_of_nonpos (show x - 1 ≤ 0 by linarith),
      abs_of_nonneg (show 0 ≤ x + 1 by linarith)]
    ring_nf
  · rcases le_total x 2 with h2 | h2
    · simp only [second, abs_of_nonneg hx,
        min_eq_right (show 2 - x ≤ 1 by linarith),
        max_eq_right (show 0 ≤ 2 - x by linarith),
        abs_of_nonpos (show x - 2 ≤ 0 by linarith),
        abs_of_nonneg (show 0 ≤ x + 2 by linarith),
        abs_of_nonneg (show 0 ≤ x - 1 by linarith),
        abs_of_nonneg (show 0 ≤ x + 1 by linarith)]
      ring_nf
    · simp only [second, abs_of_nonneg hx,
        min_eq_right (show 2 - x ≤ 1 by linarith),
        max_eq_left (show 2 - x ≤ 0 by linarith),
        abs_of_nonneg (show 0 ≤ x - 2 by linarith),
        abs_of_nonneg (show 0 ≤ x + 2 by linarith),
        abs_of_nonneg (show 0 ≤ x - 1 by linarith),
        abs_of_nonneg (show 0 ≤ x + 1 by linarith)]
      ring_nf

/-- The derivative of the signed square exists even at its zero. -/
theorem hasDerivAt_mul_abs (x : ℝ) :
    HasDerivAt (fun y : ℝ => y * |y|) (2 * |x|) x := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · convert (hasDerivAt_id x).mul (hasDerivAt_abs_neg hx) using 1
    · rfl
    · simp only [id_eq, one_mul, mul_neg_one, abs_of_neg hx]
      ring_nf
  · subst x
    rw [hasDerivAt_iff_tendsto_slope]
    have ht := continuous_abs.continuousAt.tendsto.mono_left
      (show 𝓝[≠] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)
    convert ht.congr' ?_ using 1 <;> try simp
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hy' : y ≠ 0 := hy
    simp [slope, hy']
  · convert (hasDerivAt_id x).mul (hasDerivAt_abs_pos hx) using 1
    · rfl
    · simp only [id_eq, one_mul, mul_one, abs_of_pos hx]
      ring_nf

/-- The derivative of the absolute cube, with an ordinary natural power. -/
theorem hasDerivAt_abs_cube (x : ℝ) :
    HasDerivAt (fun y : ℝ => |y| ^ 3) (3 * (x * |x|)) x := by
  convert hasDerivAt_abs_rpow x (p := 3) (by norm_num) using 1 <;>
    norm_num [Real.rpow_natCast, mul_comm, mul_left_comm, mul_assoc]

/-- The displayed first jet is the actual derivative at every point. -/
theorem hasDerivAt_value (x : ℝ) : HasDerivAt value (first x) x := by
  have hd (a : ℝ) := (hasDerivAt_abs_cube (x + a)).comp x ((hasDerivAt_id x).add_const a)
  convert (((((hd (-2)).add (hd 2)).sub (hd (-1))).sub (hd 1)).sub_const 14).div_const 12
    using 1
  · funext y
    dsimp [value]
    simp only [sub_eq_add_neg]
  · dsimp [first]
    ring_nf

/-- The displayed second jet is the actual derivative of the first jet everywhere. -/
theorem hasDerivAt_first (x : ℝ) : HasDerivAt first (second x) x := by
  have hd (a : ℝ) := (hasDerivAt_mul_abs (x + a)).comp x ((hasDerivAt_id x).add_const a)
  rw [second_eq_abs]
  convert ((((hd (-2)).add (hd 2)).sub (hd (-1))).sub (hd 1)).div_const 4
    using 1
  · funext y
    dsimp [first]
    simp only [sub_eq_add_neg]
  · simp only [sub_eq_add_neg]
    ring_nf

/-- The ordinary derivative equals the named first jet. -/
@[simp] theorem deriv_value : deriv value = first := funext fun x => (hasDerivAt_value x).deriv

/-- The ordinary derivative of the first jet equals the named second jet. -/
@[simp] theorem deriv_first : deriv first = second := funext fun x => (hasDerivAt_first x).deriv

/-- The potential is globally twice continuously differentiable, including all joins. -/
theorem contDiff_value : ContDiff ℝ 2 value := by
  have hc : ContDiff ℝ 2 (fun x : ℝ => |x| ^ 3) := by
    convert contDiff_norm_rpow_of_lt (E := ℝ) (n := 2) (r := 3) (by norm_num) using 1
    norm_num [Real.norm_eq_abs, Real.rpow_natCast]
  have hd (a : ℝ) : ContDiff ℝ 2 (fun x : ℝ => |x + a| ^ 3) :=
    hc.comp (contDiff_id.add contDiff_const)
  convert (((((hd (-2)).add (hd 2)).sub (hd (-1))).sub (hd 1)).sub
    (contDiff_const (c := (14 : ℝ)))).div_const 12 using 1
  funext y
  dsimp [value]
  simp only [sub_eq_add_neg]

/-- The first derivative on the positive interpolation interval. -/
theorem first_eq_of_one_le_of_le_two {x : ℝ} (hl : 1 ≤ x) (hu : x ≤ 2) :
    first x = x - (x - 1) ^ 2 / 2 := by
  simp only [first, abs_of_nonpos (show x - 2 ≤ 0 by linarith),
    abs_of_nonneg (show 0 ≤ x + 2 by linarith),
    abs_of_nonneg (show 0 ≤ x - 1 by linarith),
    abs_of_nonneg (show 0 ≤ x + 1 by linarith)]
  ring_nf

/-- The first derivative is constant on the positive affine tail. -/
theorem first_eq_of_two_le {x : ℝ} (hx : 2 ≤ x) : first x = 3 / 2 := by
  simp only [first, abs_of_nonneg (show 0 ≤ x - 2 by linarith),
    abs_of_nonneg (show 0 ≤ x + 2 by linarith),
    abs_of_nonneg (show 0 ≤ x - 1 by linarith),
    abs_of_nonneg (show 0 ≤ x + 1 by linarith)]
  ring_nf

/-- The capped quadratic is everywhere nonnegative. -/
theorem value_nonneg (x : ℝ) : 0 ≤ value x := by
  rcases le_total |x| 1 with h | h
  · rw [value_eq_of_abs_le_one h]
    positivity
  · rcases le_total |x| 2 with h2 | h2
    · rw [value_eq_of_one_le_abs_le_two h h2]
      have hp : (|x| - 1) ^ 3 ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
      have hs : 1 ≤ |x| ^ 2 := by nlinarith [abs_nonneg x]
      linarith
    · rw [value_eq_of_two_le_abs h2]
      linarith

/-- The magnitude of the first derivative never exceeds three halves. -/
theorem abs_first_le (x : ℝ) : |first x| ≤ 3 / 2 := by
  wlog hx : 0 ≤ x generalizing x
  · simpa using this (-x) (by linarith)
  rcases le_total x 1 with h | h
  · rw [first_eq_of_abs_le_one (by simpa [abs_of_nonneg hx] using h), abs_of_nonneg hx]
    linarith
  · rcases le_total x 2 with h2 | h2
    · rw [first_eq_of_one_le_of_le_two h h2, abs_le]
      constructor <;> nlinarith [sq_nonneg (x - 2),
        mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr h2)]
    · rw [first_eq_of_two_le h2]
      norm_num

/-- The second derivative is nonnegative. -/
theorem second_nonneg (x : ℝ) : 0 ≤ second x := le_max_left _ _

/-- The second derivative never exceeds one. -/
theorem second_le_one (x : ℝ) : second x ≤ 1 := by
  exact max_le (by norm_num) (min_le_left _ _)

/-- The magnitude of the second derivative never exceeds one. -/
theorem abs_second_le (x : ℝ) : |second x| ≤ 1 := by
  rw [abs_of_nonneg (second_nonneg x)]
  exact second_le_one x

/-- The second derivative has global Lipschitz constant one. -/
theorem lipschitz_second : LipschitzWith 1 second := by
  have h : LipschitzWith 1 (fun x : ℝ => 2 - |x|) := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    simpa only [NNReal.coe_one, one_mul, Real.dist_eq, sub_sub_sub_cancel_left,
      abs_sub_comm] using abs_abs_sub_abs_le_abs_sub x y
  exact (h.const_min 1).const_max 0

/-- The first jet is continuously differentiable, including all joins. -/
theorem contDiff_first : ContDiff ℝ 1 first := by
  rw [contDiff_one_iff_deriv, deriv_first]
  exact ⟨fun x => (hasDerivAt_first x).differentiableAt, lipschitz_second.continuous⟩

/-- The first derivative is monotone. -/
theorem monotone_first : Monotone first := by
  apply monotone_of_deriv_nonneg (fun x => (hasDerivAt_first x).differentiableAt)
  simpa only [deriv_first] using second_nonneg

/-- The capped quadratic is convex on the real line. -/
theorem convexOn_value : ConvexOn ℝ Set.univ value := by
  apply Monotone.convexOn_univ_of_deriv (fun x => (hasDerivAt_value x).differentiableAt)
  simpa only [deriv_value] using monotone_first

/-- The potential has global Lipschitz constant three halves. -/
theorem lipschitz_value : LipschitzWith (3 / 2) value := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun x => (hasDerivAt_value x).differentiableAt)
  intro x
  rw [(hasDerivAt_value x).deriv]
  exact_mod_cast abs_first_le x

/-- The first derivative has global Lipschitz constant one. -/
theorem lipschitz_first : LipschitzWith 1 first := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun x => (hasDerivAt_first x).differentiableAt)
  intro x
  rw [(hasDerivAt_first x).deriv]
  exact_mod_cast abs_second_le x

/-- The potential vanishes at the origin. -/
@[simp] theorem value_zero : value 0 = 0 := by
  norm_num [value]

/-- The first derivative vanishes at the origin. -/
@[simp] theorem first_zero : first 0 = 0 := by
  norm_num [first]

/-- The second derivative at the origin equals one. -/
@[simp] theorem second_zero : second 0 = 1 := by
  norm_num [second]

end CappedQuadratic
