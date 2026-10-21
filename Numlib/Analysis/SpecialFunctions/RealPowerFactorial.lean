import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Finite-product factorials of real powers

This normalization extends the ordinary factorial by multiplying the positive fractional
part shifts. It is useful for differentiating radial real powers and integrating Taylor
kernels. Its values between zero and one are one.
-/

noncomputable section
open scoped Nat

namespace Real

/-- A finite-product factorial, with the natural floor truncating the product. -/
def powerFactorial (r : ℝ) : ℝ :=
  ∏ i ∈ Finset.range ⌊r⌋₊, ((i + 1 : ℕ) + r - (⌊r⌋₊ : ℝ))

/-- Every factor is positive on the nonnegative domain. -/
theorem powerFactorial_pos {r : ℝ} (hr : 0 ≤ r) : 0 < powerFactorial r := by
  apply Finset.prod_pos
  intro i _
  have hf := Nat.floor_le hr
  have hi : (0 : ℝ) < (i + 1 : ℕ) := by positivity
  linarith

/-- The finite-product factorial agrees with the ordinary factorial at natural numbers. -/
@[simp] theorem powerFactorial_natCast (n : ℕ) : powerFactorial (n : ℝ) = n ! := by
  simp only [powerFactorial, Nat.floor_natCast, add_sub_cancel_right]
  norm_cast
  exact Finset.prod_range_add_one_eq_factorial n

/-- Adding one multiplies the finite-product factorial by the new exponent. -/
theorem powerFactorial_add_one {r : ℝ} (hr : 0 ≤ r) :
    powerFactorial (r + 1) = (r + 1) * powerFactorial r := by
  unfold powerFactorial
  rw [Nat.floor_add_one hr, Finset.prod_range_succ]
  have hprod : (∏ i ∈ Finset.range ⌊r⌋₊,
      ((i + 1 : ℕ) + (r + 1) - ((⌊r⌋₊ + 1 : ℕ) : ℝ))) =
      ∏ i ∈ Finset.range ⌊r⌋₊, ((i + 1 : ℕ) + r - (⌊r⌋₊ : ℝ)) := by
    apply Finset.prod_congr rfl
    intro i _
    push_cast
    ring
  rw [hprod, show (((⌊r⌋₊ + 1 : ℕ) : ℝ) + (r + 1) -
    ((⌊r⌋₊ + 1 : ℕ) : ℝ)) = r + 1 by ring, mul_comm]

/-- Removing one exponent divides off its coefficient, including at integral endpoints. -/
theorem powerFactorial_sub_one {r : ℝ} (hr : 1 ≤ r) :
    powerFactorial r = r * powerFactorial (r - 1) := by
  simpa using powerFactorial_add_one (r := r - 1) (by linarith)

/-- A truncated falling product is the quotient of two finite-product factorials. -/
theorem powerFactorial_sub_nat {r : ℝ} {j : ℕ} (hjr : (j : ℝ) ≤ r) :
    powerFactorial r = (∏ i ∈ Finset.range j, (r - (i : ℝ))) *
      powerFactorial (r - j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hjr' : (j : ℝ) ≤ r := by push_cast at hjr; linarith
    rw [ih hjr', Finset.prod_range_succ]
    have hrec := powerFactorial_sub_one (r := r - j) (by push_cast at hjr ⊢; linarith)
    rw [hrec, show r - (j : ℝ) - 1 = r - ((j + 1 : ℕ) : ℝ) by push_cast; ring,
      mul_assoc]

/-- Exponents in the unit interval have an empty product or the single factor one. -/
theorem powerFactorial_eq_one {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1) :
    powerFactorial β = 1 := by
  rcases hβ1.eq_or_lt with rfl | hlt
  · simpa using powerFactorial_natCast 1
  · simp [powerFactorial, Nat.floor_eq_zero.mpr hlt]

/-- The normalization used by sharp Hölder Taylor estimates is this same factorial. -/
theorem powerFactorial_nat_add {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1) (n : ℕ) :
    powerFactorial ((n : ℝ) + β) =
      ∏ i ∈ Finset.range n, (((i + 1 : ℕ) : ℝ) + β) := by
  induction n with
  | zero => simpa using powerFactorial_eq_one hβ hβ1
  | succ n ih =>
    have he : ((n + 1 : ℕ) : ℝ) + β = ((n : ℝ) + β) + 1 := by push_cast; ring
    rw [he, powerFactorial_add_one (by positivity), ih, Finset.prod_range_succ]
    push_cast
    ring

/-- The one-derivative coefficient can be written using a shifted factorial. -/
theorem div_powerFactorial_mul {r a : ℝ} (hr : 1 ≤ r) :
    a / powerFactorial r * r = a / powerFactorial (r - 1) := by
  rw [powerFactorial_sub_one hr]
  have hn : r ≠ 0 := by linarith
  rw [mul_comm r (powerFactorial (r - 1)), div_mul_eq_div_div, div_mul_cancel₀ _ hn]

/-- The second-derivative coefficient can be written using a twice shifted factorial. -/
theorem div_powerFactorial_mul_mul {r a : ℝ} (hr : 2 ≤ r) :
    a / powerFactorial r * r * (r - 1) = a / powerFactorial (r - 2) := by
  rw [div_powerFactorial_mul (by linarith : 1 ≤ r),
    div_powerFactorial_mul (by linarith : 1 ≤ r - 1)]
  congr 2
  ring

end Real
