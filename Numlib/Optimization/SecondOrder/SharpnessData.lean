import Numlib.Optimization.SecondOrder.OracleMethod

/-!
# Primitive scalar second-order sharpness data

The prescribed scalar jets match the source lower-bound construction. The
actual shifted residual equation and the method's spectral rule force every
trial displacement to be positive and comparable to the square root of the
requested accuracy. No trajectory or complexity conclusion is assumed.
-/

namespace ShiftedNewton.Sharpness

/-- The source objective value prescribed at the kth query. -/
noncomputable def value (t : ℝ) (k : ℕ) : ℝ := 1 - (k : ℝ) * t ^ 3 / 2

/-- The genuine first jet prescribed at the kth query. -/
noncomputable def first (t : ℝ) (k : ℕ) : ℝ := -2 * t ^ 2 * value t k

/-- The genuine second jet prescribed at the kth query. -/
noncomputable def second (t : ℝ) (k : ℕ) : ℝ := 4 * t * (value t k) ^ 2

/-- The exact source stopping horizon written in the square-root accuracy. -/
noncomputable def horizon (t : ℝ) : ℕ := ⌈1 / t ^ 3⌉₊

/-- The exact source horizon is strictly positive. -/
theorem horizon_pos {t : ℝ} (ht : 0 < t) : 0 < horizon t := by
  rw [horizon, Nat.pos_iff_ne_zero, ne_eq, Nat.ceil_eq_zero]
  exact not_le_of_gt (by positivity)

/-- Every prescribed value through the terminal query is positive and at most one. -/
theorem value_bounds {t : ℝ} (ht : 0 < t) (ht1 : t < 1)
    {k : ℕ} (hk : k ≤ horizon t) : 0 < value t k ∧ value t k ≤ 1 := by
  have ht3 : 0 < t ^ 3 := by positivity
  have hc := Nat.ceil_lt_add_one (show 0 ≤ 1 / t ^ 3 by positivity)
  have hm := mul_lt_mul_of_pos_right hc ht3
  have hp : t ^ 3 < 1 := pow_lt_one₀ ht.le ht1 (by decide)
  have he : (1 / t ^ 3 + 1) * t ^ 3 = 1 + t ^ 3 := by field_simp
  rw [he] at hm
  have hkR : (k : ℝ) ≤ horizon t := by exact_mod_cast hk
  have hmk := mul_le_mul_of_nonneg_right hkR ht3.le
  have hk0 : 0 ≤ (k : ℝ) * t ^ 3 := by positivity
  dsimp only [horizon] at hmk
  dsimp only [value]
  constructor <;> nlinarith

/-- Every nonterminal prescribed objective value is strictly greater than one half. -/
theorem half_lt_value {t : ℝ} (ht : 0 < t) {k : ℕ} (hk : k < horizon t) :
    1 / 2 < value t k := by
  have hh : (k : ℝ) < 1 / t ^ 3 := Nat.lt_ceil.mp hk
  have hm := (lt_div_iff₀ (show 0 < t ^ 3 by positivity)).mp hh
  dsimp [value]
  linarith

/-- The terminal prescribed gradient passes exactly the requested accuracy. -/
theorem terminal_first_le {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    |first t (horizon t)| ≤ t ^ 2 := by
  have hb := value_bounds ht ht1 (le_refl (horizon t))
  have hc := Nat.le_ceil (1 / t ^ 3)
  have hm := (div_le_iff₀ (show 0 < t ^ 3 by positivity)).mp hc
  change 1 ≤ (horizon t : ℝ) * t ^ 3 at hm
  have hv : value t (horizon t) ≤ 1 / 2 := by dsimp [value];nlinarith
  have hneg : -2 * t ^ 2 * value t (horizon t) ≤ 0 := by
    have hp : 0 ≤ 2 * t ^ 2 * value t (horizon t) := by have := hb.1;positivity
    nlinarith
  rw [first, abs_of_nonpos hneg]
  have hp := mul_le_mul_of_nonneg_left hv (sq_nonneg t)
  nlinarith

/-- Every earlier actual prescribed first derivative strictly fails the requested tolerance. -/
theorem accuracy_lt_first {t : ℝ} (ht : 0 < t) {k : ℕ} (hk : k < horizon t) :
    t ^ 2 < |first t k| := by
  have hv := half_lt_value ht hk
  have hneg : -2 * t ^ 2 * value t k ≤ 0 := by
    have hp : 0 ≤ 2 * t ^ 2 * value t k := by positivity
    nlinarith
  rw [first, abs_of_nonpos hneg]
  nlinarith [sq_pos_of_pos ht]

/-- The positive objective level makes the Hessian dominate the square-root gradient term. -/
theorem spectral_max {t v : ℝ} (ht : 0 < t) (hv : 1 / 2 ≤ v) :
    max |4 * t * v ^ 2| (Real.sqrt |-2 * t ^ 2 * v|) = 4 * t * v ^ 2 := by
  have hv0 : 0 < v := by linarith
  have hH : 0 < 4 * t * v ^ 2 := by positivity
  have hg : -2 * t ^ 2 * v ≤ 0 := by
    have hp : 0 ≤ 2 * t ^ 2 * v := by positivity
    nlinarith
  rw [abs_of_pos hH, abs_of_nonpos hg, show - (-2 * t ^ 2 * v) = 2 * t ^ 2 * v by ring]
  apply max_eq_left
  apply (Real.sqrt_le_iff).mpr
  refine ⟨hH.le, ?_⟩
  have hv3 : (1 / 2 : ℝ) ^ 3 ≤ v ^ 3 := pow_le_pow_left₀ (by norm_num) hv 3
  have hm := mul_le_mul_of_nonneg_left (show 2 ≤ 16 * v ^ 3 by nlinarith)
    (show 0 ≤ t ^ 2 * v by positivity)
  nlinarith

/-- The primitive actual shifted equation and spectral bound force a positive
step between fixed multiples of the square-root accuracy. -/
theorem shifted_step_bounds {t v lambda r s κrg κlambda : ℝ}
    (ht : 0 < t) (hv : 1 / 2 ≤ v) (hv1 : v ≤ 1)
    (hg1 : κrg < 1) (hκ : 1 < κlambda)
    (hlambda : 0 ≤ lambda)
    (heq : (4 * t * v ^ 2 + lambda) * s = 2 * t ^ 2 * v + r)
    (hr : |r| ≤ κrg * (2 * t ^ 2 * v))
    (hshift : 4 * t * v ^ 2 + lambda ≤ κlambda * (4 * t * v ^ 2)) :
    0 < s ∧ (1 - κrg) / (2 * κlambda) * t ≤ s ∧ s ≤ (1 + κrg) * t := by
  have hv0 : 0 < v := by linarith
  have hH : 0 < 4 * t * v ^ 2 + lambda := by positivity
  have hnum : 0 < 2 * t ^ 2 * v + r := by
    have hp : 0 < (1 - κrg) * (2 * t ^ 2 * v) := by positivity
    linarith [(abs_le.mp hr).1]
  have hs : 0 < s := (mul_pos_iff_of_pos_left hH).mp (by rw [heq]; exact hnum)
  have htv : 0 < 2 * t * v := by positivity
  have hu : (2 * t * v) * (2 * v * s) ≤ (2 * t * v) * ((1 + κrg) * t) := by
    nlinarith [(abs_le.mp hr).2, mul_nonneg hlambda hs.le]
  have hu' := le_of_mul_le_mul_left hu htv
  have hs2 : s ≤ 2 * v * s := by nlinarith [mul_nonneg (show 0 ≤ 2 * v - 1 by linarith) hs.le]
  have hl := mul_le_mul_of_nonneg_right hshift hs.le
  have hl' : (2 * t * v) * ((1 - κrg) * t) ≤ (2 * t * v) * (2 * κlambda * v * s) := by
    nlinarith [(abs_le.mp hr).1]
  have hl'' := le_of_mul_le_mul_left hl' htv
  have hvstep := mul_le_mul_of_nonneg_right hv1
    (show 0 ≤ 2 * κlambda * s by positivity)
  refine ⟨hs, ?_, hs2.trans hu'⟩
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (show 0 < 2 * κlambda by positivity)).mpr
  nlinarith

end ShiftedNewton.Sharpness
