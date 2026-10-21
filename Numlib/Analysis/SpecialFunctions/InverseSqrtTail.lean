import Numlib.Analysis.Calculus.PiecewiseDerivatives
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# A positive inverse square root tail

A rational continuation on the left of one extends the inverse square root to a positive
`C²` function on the real line. The named first and second derivatives have global
quantitative bounds, including a Lipschitz second derivative despite its corner at one.
-/

open Set Filter
open scoped Topology ContDiff

/-- Two real differentiable branches with matching values and derivatives glue at a closed
left half-line. Only the common boundary point is asserted here. -/
theorem hasDerivAt_ite_le_of_eq {f g : ℝ → ℝ} {a d : ℝ}
    (hf : HasDerivAt f d a) (hg : HasDerivAt g d a) (hfg : f a = g a) :
    HasDerivAt (fun x => if x ≤ a then f x else g x) d a := by
  change HasDerivAt (joinAt a f g) d a
  simpa only [ite_eq_left le_rfl] using
    (hasDerivAt_joinAt hf hg hfg (fun _ => rfl))

namespace InverseSqrtTail

/-- Positive rational continuation of `x ^ (-1/2)` to the entire real line. -/
noncomputable def value (x : ℝ) : ℝ :=
  if x ≤ 1 then (12 - 7 * x) / 8 + 3 / (8 * (2 - x)) else x ^ (-(1 / 2 : ℝ))

/-- The first derivative of the positive inverse square root continuation. -/
noncomputable def first (x : ℝ) : ℝ :=
  if x ≤ 1 then -(7 / 8 : ℝ) + 3 / (8 * (2 - x) ^ 2)
  else -(1 / 2 : ℝ) * x ^ (-(3 / 2 : ℝ))

/-- The second derivative of the positive inverse square root continuation. -/
noncomputable def second (x : ℝ) : ℝ :=
  if x ≤ 1 then 3 / (4 * (2 - x) ^ 3) else (3 / 4 : ℝ) * x ^ (-(5 / 2 : ℝ))

/-- Left-hand formula for the value. -/
theorem value_of_le_one {x : ℝ} (hx : x ≤ 1) :
    value x = (12 - 7 * x) / 8 + 3 / (8 * (2 - x)) := ite_eq_left hx

/-- Right-hand formula for the value, including the common boundary. -/
theorem value_of_one_le {x : ℝ} (hx : 1 ≤ x) : value x = x ^ (-(1 / 2 : ℝ)) := by
  rcases hx.eq_or_lt with rfl | hx
  · norm_num [value]
  · exact ite_eq_right (not_le.mpr hx)

/-- Left-hand formula for the first derivative. -/
theorem first_of_le_one {x : ℝ} (hx : x ≤ 1) :
    first x = -(7 / 8 : ℝ) + 3 / (8 * (2 - x) ^ 2) := ite_eq_left hx

/-- Right-hand formula for the first derivative, including the common boundary. -/
theorem first_of_one_le {x : ℝ} (hx : 1 ≤ x) :
    first x = -(1 / 2 : ℝ) * x ^ (-(3 / 2 : ℝ)) := by
  rcases hx.eq_or_lt with rfl | hx
  · norm_num [first]
  · exact ite_eq_right (not_le.mpr hx)

/-- Left-hand formula for the second derivative. -/
theorem second_of_le_one {x : ℝ} (hx : x ≤ 1) :
    second x = 3 / (4 * (2 - x) ^ 3) := ite_eq_left hx

/-- Right-hand formula for the second derivative, including the common boundary. -/
theorem second_of_one_le {x : ℝ} (hx : 1 ≤ x) :
    second x = (3 / 4 : ℝ) * x ^ (-(5 / 2 : ℝ)) := by
  rcases hx.eq_or_lt with rfl | hx
  · norm_num [second]
  · exact ite_eq_right (not_le.mpr hx)

/-- Value at the joining point. -/
@[simp] theorem value_one : value 1 = 1 := by norm_num [value]

/-- First derivative at the joining point. -/
@[simp] theorem first_one : first 1 = -(1 / 2 : ℝ) := by norm_num [first]

/-- Second derivative at the joining point. -/
@[simp] theorem second_one : second 1 = (3 / 4 : ℝ) := by norm_num [second]

/-- Derivative of the rational branch of the value, away from its pole. -/
theorem hasDerivAt_left_value {x : ℝ} (hx : x ≠ 2) :
    HasDerivAt (fun y : ℝ => (12 - 7 * y) / 8 + 3 / (8 * (2 - y)))
      (-(7 / 8 : ℝ) + 3 / (8 * (2 - x) ^ 2)) x := by
  have hn : 2 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  convert (((hasDerivAt_const x (12 : ℝ)).sub ((hasDerivAt_id x).const_mul 7)).div_const 8).add
    ((hasDerivAt_const x (3 : ℝ)).div
      (((hasDerivAt_const x (2 : ℝ)).sub (hasDerivAt_id x)).const_mul 8)
      (mul_ne_zero (by norm_num) hn)) using 1
  · ext y
    dsimp
  · dsimp
    field_simp [hn]
    ring

/-- Derivative of the rational branch of the first derivative, away from its pole. -/
theorem hasDerivAt_left_first {x : ℝ} (hx : x ≠ 2) :
    HasDerivAt (fun y : ℝ => -(7 / 8 : ℝ) + 3 / (8 * (2 - y) ^ 2))
      (3 / (4 * (2 - x) ^ 3)) x := by
  have hn : 2 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  convert (hasDerivAt_const x (-(7 / 8 : ℝ))).add
    ((hasDerivAt_const x (3 : ℝ)).div
      ((((hasDerivAt_const x (2 : ℝ)).sub (hasDerivAt_id x)).pow 2).const_mul 8)
      (mul_ne_zero (by norm_num) (pow_ne_zero _ hn))) using 1
  · ext y
    dsimp
  · dsimp
    field_simp [hn]
    ring

/-- Derivative of the rational branch of the second derivative, away from its pole. -/
theorem hasDerivAt_left_second {x : ℝ} (hx : x ≠ 2) :
    HasDerivAt (fun y : ℝ => 3 / (4 * (2 - y) ^ 3))
      (9 / (4 * (2 - x) ^ 4)) x := by
  have hn : 2 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  convert (hasDerivAt_const x (3 : ℝ)).div
    ((((hasDerivAt_const x (2 : ℝ)).sub (hasDerivAt_id x)).pow 3).const_mul 4)
    (mul_ne_zero (by norm_num) (pow_ne_zero _ hn)) using 1
  · ext y
    dsimp
  · dsimp
    field_simp [hn]
    ring

/-- Derivative of the inverse square root branch. -/
theorem hasDerivAt_right_value {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ => y ^ (-(1 / 2 : ℝ)))
      (-(1 / 2 : ℝ) * x ^ (-(3 / 2 : ℝ))) x := by
  convert Real.hasDerivAt_rpow_const (Or.inl hx) (p := -(1 / 2 : ℝ)) using 1
  norm_num

/-- Derivative of the first derivative on the inverse square root branch. -/
theorem hasDerivAt_right_first {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ => -(1 / 2 : ℝ) * y ^ (-(3 / 2 : ℝ)))
      ((3 / 4 : ℝ) * x ^ (-(5 / 2 : ℝ))) x := by
  convert (Real.hasDerivAt_rpow_const (Or.inl hx) (p := -(3 / 2 : ℝ))).const_mul
    (-(1 / 2 : ℝ)) using 1
  norm_num
  ring

/-- Derivative of the second derivative on the inverse square root branch. -/
theorem hasDerivAt_right_second {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ => (3 / 4 : ℝ) * y ^ (-(5 / 2 : ℝ)))
      (-(15 / 8 : ℝ) * x ^ (-(7 / 2 : ℝ))) x := by
  convert (Real.hasDerivAt_rpow_const (Or.inl hx) (p := -(5 / 2 : ℝ))).const_mul
    (3 / 4 : ℝ) using 1
  norm_num
  ring

/-- The displayed first derivative is the derivative at every real point. -/
theorem hasDerivAt_value (x : ℝ) : HasDerivAt value (first x) x := by
  rcases lt_trichotomy x 1 with hx | rfl | hx
  · rw [first_of_le_one hx.le]
    apply (hasDerivAt_left_value (by linarith : x ≠ 2)).congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds hx] with y hy
    exact value_of_le_one hy.le
  · rw [first_one]
    apply hasDerivAt_ite_le_of_eq
    · convert hasDerivAt_left_value (by norm_num : (1 : ℝ) ≠ 2) using 1
      norm_num
    · convert hasDerivAt_right_value (by norm_num : (1 : ℝ) ≠ 0) using 1
      norm_num
    · norm_num
  · rw [first_of_one_le hx.le]
    apply (hasDerivAt_right_value (by linarith : x ≠ 0)).congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hx] with y hy
    exact value_of_one_le hy.le

/-- The displayed second derivative is the derivative of `first` everywhere. -/
theorem hasDerivAt_first (x : ℝ) : HasDerivAt first (second x) x := by
  rcases lt_trichotomy x 1 with hx | rfl | hx
  · rw [second_of_le_one hx.le]
    apply (hasDerivAt_left_first (by linarith : x ≠ 2)).congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds hx] with y hy
    exact first_of_le_one hy.le
  · rw [second_one]
    apply hasDerivAt_ite_le_of_eq
    · convert hasDerivAt_left_first (by norm_num : (1 : ℝ) ≠ 2) using 1
      norm_num
    · convert hasDerivAt_right_first (by norm_num : (1 : ℝ) ≠ 0) using 1
      norm_num
    · norm_num
  · rw [second_of_one_le hx.le]
    apply (hasDerivAt_right_first (by linarith : x ≠ 0)).congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hx] with y hy
    exact first_of_one_le hy.le

/-- Positivity of the continuation, including its entire rational branch. -/
theorem value_pos (x : ℝ) : 0 < value x := by
  by_cases hx : x ≤ 1
  · rw [value_of_le_one hx]
    have hbase : 0 < 2 - x := by linarith
    have hnum : 0 < 12 - 7 * x := by linarith
    positivity
  · rw [value_of_one_le (le_of_not_ge hx)]
    exact Real.rpow_pos_of_pos (by linarith) _

/-- Nonnegativity of the continuation. -/
theorem value_nonneg (x : ℝ) : 0 ≤ value x := (value_pos x).le

/-- The first derivative is nonpositive. -/
theorem first_nonpos (x : ℝ) : first x ≤ 0 := by
  by_cases hx : x ≤ 1
  · rw [first_of_le_one hx]
    have hb : 1 ≤ 2 - x := by linarith
    have hp : 1 ≤ (2 - x) ^ 2 := one_le_pow₀ hb
    have hd : 0 < 8 * (2 - x) ^ 2 := by positivity
    have hq : 3 / (8 * (2 - x) ^ 2) ≤ (3 / 8 : ℝ) := by
      apply (div_le_iff₀ hd).2
      nlinarith
    linarith
  · rw [first_of_one_le (le_of_not_ge hx)]
    exact mul_nonpos_of_nonpos_of_nonneg (by norm_num) (Real.rpow_nonneg (by linarith) _)

/-- A global bound for the absolute first derivative. -/
theorem abs_first_le (x : ℝ) : |first x| ≤ (7 / 8 : ℝ) := by
  rw [abs_of_nonpos (first_nonpos x)]
  by_cases hx : x ≤ 1
  · rw [first_of_le_one hx]
    have hq : 0 ≤ 3 / (8 * (2 - x) ^ 2) := by positivity
    linarith
  · rw [first_of_one_le (le_of_not_ge hx)]
    have hp := Real.rpow_le_one_of_one_le_of_nonpos (le_of_not_ge hx)
      (by norm_num : -(3 / 2 : ℝ) ≤ 0)
    nlinarith

/-- The second derivative is nonnegative. -/
theorem second_nonneg (x : ℝ) : 0 ≤ second x := by
  by_cases hx : x ≤ 1
  · rw [second_of_le_one hx]
    have hb : 0 < 2 - x := by linarith
    positivity
  · rw [second_of_one_le (le_of_not_ge hx)]
    exact mul_nonneg (by norm_num) (Real.rpow_nonneg (by linarith) _)

/-- A global bound for the second derivative. -/
theorem abs_second_le (x : ℝ) : |second x| ≤ (3 / 4 : ℝ) := by
  rw [abs_of_nonneg (second_nonneg x)]
  by_cases hx : x ≤ 1
  · rw [second_of_le_one hx]
    have hb : 1 ≤ 2 - x := by linarith
    have hp : 1 ≤ (2 - x) ^ 3 := one_le_pow₀ hb
    have hd : 0 < 4 * (2 - x) ^ 3 := by positivity
    apply (div_le_iff₀ hd).2
    nlinarith
  · rw [second_of_one_le (le_of_not_ge hx)]
    have hp := Real.rpow_le_one_of_one_le_of_nonpos (le_of_not_ge hx)
      (by norm_num : -(5 / 2 : ℝ) ≤ 0)
    nlinarith

/-- The continuation is globally `7/8`-Lipschitz. -/
theorem lipschitz_value : LipschitzWith (7 / 8) value := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun x => (hasDerivAt_value x).differentiableAt)
  intro x
  apply NNReal.coe_le_coe.mp
  simpa only [coe_nnnorm, (hasDerivAt_value x).deriv, Real.norm_eq_abs,
    NNReal.coe_div, NNReal.coe_ofNat] using abs_first_le x

/-- The first derivative is globally `3/4`-Lipschitz. -/
theorem lipschitz_first : LipschitzWith (3 / 4) first := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun x => (hasDerivAt_first x).differentiableAt)
  intro x
  apply NNReal.coe_le_coe.mp
  simpa only [coe_nnnorm, (hasDerivAt_first x).deriv, Real.norm_eq_abs,
    NNReal.coe_div, NNReal.coe_ofNat] using abs_second_le x

/-- Left one-sided third derivative, including the join. -/
theorem hasDerivWithinAt_second_left {x : ℝ} (hx : x ≤ 1) :
    HasDerivWithinAt second (9 / (4 * (2 - x) ^ 4)) (Iic 1) x := by
  apply (hasDerivAt_left_second (by linarith : x ≠ 2)).hasDerivWithinAt.congr
  · exact fun _ hy => second_of_le_one hy
  · exact second_of_le_one hx

/-- Right one-sided third derivative, including the join. -/
theorem hasDerivWithinAt_second_right {x : ℝ} (hx : 1 ≤ x) :
    HasDerivWithinAt second (-(15 / 8 : ℝ) * x ^ (-(7 / 2 : ℝ))) (Ici 1) x := by
  apply (hasDerivAt_right_second (by linarith : x ≠ 0)).hasDerivWithinAt.congr
  · exact fun _ hy => second_of_one_le hy
  · exact second_of_one_le hx

/-- The second derivative is `9/4`-Lipschitz on the rational half-line. -/
theorem lipschitzOnWith_second_left : LipschitzOnWith (9 / 4) second (Iic 1) := by
  apply (convex_Iic (1 : ℝ)).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun x hx => hasDerivWithinAt_second_left hx)
  intro x hx
  change x ≤ 1 at hx
  apply NNReal.coe_le_coe.mp
  simp only [coe_nnnorm, Real.norm_eq_abs, NNReal.coe_div, NNReal.coe_ofNat]
  have hb : 1 ≤ 2 - x := by linarith
  have hp : 1 ≤ (2 - x) ^ 4 := one_le_pow₀ hb
  have hd : 0 < 4 * (2 - x) ^ 4 := by positivity
  rw [abs_of_pos (by positivity : 0 < 9 / (4 * (2 - x) ^ 4))]
  apply (div_le_iff₀ hd).2
  nlinarith

/-- The second derivative is `9/4`-Lipschitz on the inverse square root half-line. -/
theorem lipschitzOnWith_second_right : LipschitzOnWith (9 / 4) second (Ici 1) := by
  apply (convex_Ici (1 : ℝ)).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun x hx => hasDerivWithinAt_second_right hx)
  intro x hx
  change 1 ≤ x at hx
  apply NNReal.coe_le_coe.mp
  simp only [coe_nnnorm, Real.norm_eq_abs, NNReal.coe_div, NNReal.coe_ofNat]
  have hp := Real.rpow_le_one_of_one_le_of_nonpos hx
    (by norm_num : -(7 / 2 : ℝ) ≤ 0)
  have hn := Real.rpow_nonneg (by linarith : 0 ≤ x) (-(7 / 2 : ℝ))
  rw [abs_of_nonpos (mul_nonpos_of_nonpos_of_nonneg (by norm_num) hn)]
  nlinarith

/-- The second derivative is globally `9/4`-Lipschitz. The proof splits at one and does
not require existence of a third derivative at that point. -/
theorem lipschitz_second : LipschitzWith (9 / 4) second := by
  have h := LipschitzWith.joinAt lipschitzOnWith_second_left lipschitzOnWith_second_right rfl
  have heq : joinAt 1 second second = second := by
    ext x
    exact ite_self _
  rwa [heq] at h

/-- The global continuation is twice continuously differentiable. -/
theorem contDiff_value : ContDiff ℝ 2 value := by
  have hd1 : deriv value = first := funext fun x => (hasDerivAt_value x).deriv
  have hd2 : deriv first = second := funext fun x => (hasDerivAt_first x).deriv
  have hc1 : ContDiff ℝ 1 first := by
    rw [contDiff_one_iff_deriv, hd2]
    exact ⟨fun x => (hasDerivAt_first x).differentiableAt, lipschitz_second.continuous⟩
  rw [show (2 : ℕ∞ω) = 1 + 1 from rfl, contDiff_succ_iff_deriv, hd1]
  exact ⟨fun x => (hasDerivAt_value x).differentiableAt, by norm_num, hc1⟩

/-- The tail's second derivative decreases on the right half-line. -/
theorem antitoneOn_second : AntitoneOn second (Ici 1) := by
  intro x hx y hy hxy
  change 1 ≤ x at hx
  rw [second_of_one_le hx, second_of_one_le hy]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_nonpos (by linarith) hxy (by norm_num)) (by norm_num)

/-- The tail's first derivative increases on the right half-line. -/
theorem monotoneOn_first : MonotoneOn first (Ici 1) := by
  intro x hx y hy hxy
  change 1 ≤ x at hx
  rw [first_of_one_le hx, first_of_one_le hy]
  exact mul_le_mul_of_nonpos_left
    (Real.rpow_le_rpow_of_nonpos (by linarith) hxy (by norm_num)) (by norm_num)

/-- The slope on the right lies below its tangent line at the left endpoint. -/
theorem first_add_le {y s : ℝ} (hy : 1 ≤ y) (hs : 0 ≤ s) :
    first (y + s) ≤ first y + second y * s := by
  have h := (convex_Ici y).image_sub_le_mul_sub_of_deriv_le
    lipschitz_first.continuous.continuousOn
    (fun z _ => (hasDerivAt_first z).differentiableAt.differentiableWithinAt)
    (C := second y) (fun z hz => ?_) y (by simp) (y + s) (by simp [hs]) (by linarith)
  · simp only [add_sub_cancel_left] at h
    linarith
  · rw [(hasDerivAt_first z).deriv]
    have hz' : y ≤ z := interior_subset hz
    exact antitoneOn_second hy (hy.trans hz') hz'

/-- Positive increments in the tail have a nonpositive second-order Taylor remainder. -/
theorem taylor_upper {y s : ℝ} (hy : 1 ≤ y) (hs : 0 ≤ s) :
    value (y + s) ≤ value y + first y * s + second y * s ^ 2 / 2 := by
  let F : ℝ → ℝ := fun z =>
    value z - value y - first y * (z - y) - second y * (z - y) ^ 2 / 2
  have hF (z : ℝ) : HasDerivAt F (first z - first y - second y * (z - y)) z := by
    convert ((hasDerivAt_value z).sub_const (value y)).sub
      (HasDerivAt.const_mul (first y) ((hasDerivAt_id z).sub_const y)) |>.sub
      ((HasDerivAt.const_mul (second y) (((hasDerivAt_id z).sub_const y).pow 2)).div_const 2)
      using 1
    · ext w
      dsimp [F]
    · dsimp
      ring
  have h := (convex_Ici y).image_sub_le_mul_sub_of_deriv_le
    (fun z _ => (hF z).continuousAt.continuousWithinAt)
    (fun z _ => (hF z).differentiableAt.differentiableWithinAt)
    (C := 0) (fun z hz => ?_) y (by simp) (y + s) (by simp [hs]) (by linarith)
  · dsimp [F] at h
    nlinarith
  · rw [(hF z).deriv]
    have hz' : y ≤ z := interior_subset hz
    have hd := first_add_le hy (sub_nonneg.mpr hz')
    rw [add_sub_cancel] at hd
    linarith

/-- The rational branch expressed as a positive extension of its quadratic jet at one. -/
theorem value_of_le_one_taylor {x : ℝ} (hx : x ≤ 1) :
    value x = 1 + (1 - x) / 2 + 3 * (1 - x) ^ 2 / (8 * (2 - x)) := by
  rw [value_of_le_one hx]
  have hn : 2 - x ≠ 0 := by linarith
  field_simp
  ring

/-- The first derivative is exactly the named scalar jet. -/
@[simp] theorem deriv_value : deriv value = first :=
  funext fun x => (hasDerivAt_value x).deriv

/-- The derivative of the first derivative is exactly the named second jet. -/
@[simp] theorem deriv_first : deriv first = second :=
  funext fun x => (hasDerivAt_first x).deriv

/-- The second jet is strictly positive everywhere. -/
theorem second_pos (x : ℝ) : 0 < second x := by
  by_cases hx : x ≤ 1
  · rw [second_of_le_one hx]
    have hb : 0 < 2 - x := by linarith
    positivity
  · rw [second_of_one_le (le_of_not_ge hx)]
    exact mul_pos (by norm_num) (Real.rpow_pos_of_pos (by linarith) _)

/-- The first jet is strictly negative on the inverse square root half-line. -/
theorem first_neg_of_one_le {x : ℝ} (hx : 1 ≤ x) : first x < 0 := by
  rw [first_of_one_le hx]
  exact mul_neg_of_neg_of_pos (by norm_num) (Real.rpow_pos_of_pos (by linarith) _)

end InverseSqrtTail
