/-
Upstreaming candidate: finite exponential-series estimates using the ordered-field factorial
bounds in Mathlib.Analysis.Complex.Exponential. No optimization-specific assumptions are used.
-/
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
/-!
# Bounds for finite exponential sums

Finite sums of `x ^ i / i!` for `0 ≤ x ≤ 1` admit upper bounds independent of the truncation
index. Reciprocal-factorial tail bounds give the estimates directly, including at `x = 0`.
-/

open scoped BigOperators
namespace Real

/-- A finite tail of reciprocal factorials admits a bound independent of its upper limit. -/
theorem sum_Icc_inv_factorial_le (n m : ℕ) (hn : 0 < n) :
    (∑ i ∈ Finset.Icc n m, (1 : ℝ) / i.factorial) ≤
      (n + 1 : ℕ) / ((n.factorial : ℝ) * n) := by
  convert Complex.sum_div_factorial_le (α := ℝ) n (m + 1) hn using 1
  congr 1
  ext i
  simp only [Finset.mem_Icc, Finset.mem_filter, Finset.mem_range]
  omega

/-- The positive-degree terms of a finite exponential sum on the unit interval. -/
theorem sum_Icc_pow_div_factorial_le_two_mul {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (m : ℕ) :
    (∑ i ∈ Finset.Icc 1 m, x ^ i / i.factorial) ≤ 2 * x := by
  calc
    (∑ i ∈ Finset.Icc 1 m, x ^ i / i.factorial) ≤
        ∑ i ∈ Finset.Icc 1 m, x * (1 / (i.factorial : ℝ)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hi1 := (Finset.mem_Icc.1 hi).1
      have hp : x ^ i ≤ x := by
        simpa using pow_le_pow_of_le_one hx0 hx1 hi1
      simpa [div_eq_mul_inv] using div_le_div_of_nonneg_right hp (Nat.cast_nonneg i.factorial)
    _ = x * ∑ i ∈ Finset.Icc 1 m, (1 / (i.factorial : ℝ)) := by rw [Finset.mul_sum]
    _ ≤ x * 2 := by
      apply mul_le_mul_of_nonneg_left _ hx0
      simpa using sum_Icc_inv_factorial_le 1 m (by decide)
    _ = 2 * x := mul_comm _ _

/-- A finite exponential sum on the unit interval, including its constant term. -/
theorem sum_range_pow_div_factorial_le_one_add_two_mul {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (m : ℕ) :
    (∑ i ∈ Finset.range (m + 1), x ^ i / i.factorial) ≤ 1 + 2 * x := by
  have hdecomp := Finset.sum_range_eq_add_Ico
    (fun i : ℕ => x ^ i / (i.factorial : ℝ)) (Nat.succ_pos m)
  rw [hdecomp]
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]
  have heq : Finset.Ico 1 (m + 1) = Finset.Icc 1 m := by ext i; simp
  rw [heq]
  linarith [sum_Icc_pow_div_factorial_le_two_mul hx0 hx1 m]

/-- A shifted finite exponential sum on the unit interval. -/
theorem sum_Icc_shift_pow_div_factorial_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    {j p : ℕ} (hjp : j ≤ p) :
    (∑ i ∈ Finset.Icc j p, x ^ (i - j) / (i - j).factorial) ≤ 1 + 2 * x := by
  have heq : Finset.Icc j p = Finset.Ico j (p + 1) := by ext i; simp
  rw [heq, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel_left]
  have hn : p + 1 - j = p - j + 1 := by omega
  rw [hn]
  exact sum_range_pow_div_factorial_le_one_add_two_mul hx0 hx1 (p - j)

/-- A higher-order finite tail of an exponential sum on the unit interval. -/
theorem sum_Icc_pow_div_factorial_le_tail {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (j p : ℕ) :
    (∑ i ∈ Finset.Icc (j + 1) (p + 1), x ^ i / i.factorial) ≤
      2 * x ^ (j + 1) / j.factorial := by
  have hfactor : ((j + 1 + 1 : ℕ) : ℝ) /
      (((j + 1).factorial : ℝ) * (j + 1)) ≤ 2 / (j.factorial : ℝ) := by
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
    have hf : 0 < (j.factorial : ℝ) := by positivity
    apply (div_le_div_iff₀ (by positivity) hf).2
    push_cast
    have hp : (j : ℝ) + 1 + 1 ≤ 2 * ((j : ℝ) + 1) * ((j : ℝ) + 1) := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hp hf.le]
  calc
    (∑ i ∈ Finset.Icc (j + 1) (p + 1), x ^ i / i.factorial) ≤
        ∑ i ∈ Finset.Icc (j + 1) (p + 1), x ^ (j + 1) * (1 / (i.factorial : ℝ)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hp := pow_le_pow_of_le_one hx0 hx1 (Finset.mem_Icc.1 hi).1
      simpa [div_eq_mul_inv] using div_le_div_of_nonneg_right hp (Nat.cast_nonneg i.factorial)
    _ = x ^ (j + 1) * ∑ i ∈ Finset.Icc (j + 1) (p + 1), (1 / (i.factorial : ℝ)) := by
      rw [Finset.mul_sum]
    _ ≤ x ^ (j + 1) * (((j + 1 + 1 : ℕ) : ℝ) /
        (((j + 1).factorial : ℝ) * (j + 1))) :=
      mul_le_mul_of_nonneg_left (by
        simpa only [Nat.cast_add, Nat.cast_one] using
          sum_Icc_inv_factorial_le (j + 1) (p + 1) (by omega)) (pow_nonneg hx0 _)
    _ ≤ x ^ (j + 1) * (2 / (j.factorial : ℝ)) :=
      mul_le_mul_of_nonneg_left hfactor (pow_nonneg hx0 _)
    _ = 2 * x ^ (j + 1) / j.factorial := by ring

/-- A positive-order exponential tail has a bound with the preceding factorial. -/
theorem sum_Icc_pow_div_factorial_le_tail_of_pos {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) {j : ℕ} (hj : 0 < j) (p : ℕ) :
    (∑ i ∈ Finset.Icc (j + 1) p, x ^ i / i.factorial) ≤
      x ^ (j + 1) / j.factorial := by
  have hfactor : ((j + 1 + 1 : ℕ) : ℝ) /
      (((j + 1).factorial : ℝ) * (j + 1)) ≤ 1 / (j.factorial : ℝ) := by
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
    have hf : 0 < (j.factorial : ℝ) := by positivity
    apply (div_le_div_iff₀ (by positivity) hf).2
    push_cast
    have hp : (j : ℝ) + 1 + 1 ≤ ((j : ℝ) + 1) * ((j : ℝ) + 1) := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hp hf.le]
  calc _ ≤ ∑ i ∈ Finset.Icc (j + 1) p, x ^ (j + 1) * (1 / (i.factorial : ℝ)) := by
        apply Finset.sum_le_sum
        intro i hi
        have hp := pow_le_pow_of_le_one hx0 hx1 (Finset.mem_Icc.mp hi).1
        simpa only [div_eq_mul_inv, one_mul] using
          div_le_div_of_nonneg_right hp (Nat.cast_nonneg i.factorial)
    _ = x ^ (j + 1) * ∑ i ∈ Finset.Icc (j + 1) p, (1 / (i.factorial : ℝ)) := by
        rw [Finset.mul_sum]
    _ ≤ x ^ (j + 1) * (((j + 1 + 1 : ℕ) : ℝ) /
        (((j + 1).factorial : ℝ) * (j + 1))) :=
      mul_le_mul_of_nonneg_left (by
        simpa only [Nat.cast_add, Nat.cast_one] using
          sum_Icc_inv_factorial_le (j + 1) p (by omega)) (pow_nonneg hx0 _)
    _ ≤ x ^ (j + 1) * (1 / (j.factorial : ℝ)) :=
      mul_le_mul_of_nonneg_left hfactor (pow_nonneg hx0 _)
    _ = _ := by ring

end Real
