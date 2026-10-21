import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

/-!
# Logarithmic stopping counts for geometric decay

The natural ceiling treats a nonpositive logarithmic numerator as zero. An independent
finite termination bound may always cap the geometric stopping count.
-/

noncomputable section
namespace GeometricStopping

/-- The number of decay factors sufficient to reduce a positive ratio below one. -/
def decayCount (A q : ℝ) : ℕ := ⌈Real.log A / Real.log q⁻¹⌉₊

/-- Ratios at most one need no decay factors. -/
theorem decayCount_eq_zero {A q : ℝ} (hA : 0 < A) (hA1 : A ≤ 1)
    (hq : 0 < q) (hq1 : q < 1) : decayCount A q = 0 := by
  apply Nat.ceil_eq_zero.mpr
  exact div_nonpos_of_nonpos_of_nonneg (Real.log_nonpos hA.le hA1)
    (Real.log_nonneg (by simpa using (one_le_inv₀ hq).mpr hq1.le))

/-- The ceiling logarithm actually makes the geometric product at most one. -/
theorem mul_pow_decayCount_le_one {A q : ℝ} (hA : 0 < A)
    (hq : 0 < q) (hq1 : q < 1) : A * q ^ decayCount A q ≤ 1 := by
  have hlog : 0 < Real.log q⁻¹ := Real.log_pos ((one_lt_inv₀ hq).mpr hq1)
  have hc := (div_le_iff₀ hlog).mp (Nat.le_ceil (Real.log A / Real.log q⁻¹))
  have hp : 0 < A * q ^ decayCount A q := mul_pos hA (pow_pos hq _)
  apply (Real.log_le_log_iff hp zero_lt_one).mp
  rw [Real.log_one, Real.log_mul hA.ne' (pow_pos hq _).ne', Real.log_pow]
  change Real.log A ≤ (decayCount A q : ℝ) * Real.log q⁻¹ at hc
  rw [Real.log_inv] at hc
  nlinarith

/-- A geometric residual estimate attains its tolerance at the stated logarithmic count. -/
theorem mul_pow_decayCount_le {B eps q : ℝ} (hB : 0 < B) (heps : 0 < eps)
    (hq : 0 < q) (hq1 : q < 1) :
    B * q ^ decayCount (B / eps) q ≤ eps := by
  have h := mul_pow_decayCount_le_one (div_pos hB heps) hq hq1
  apply (div_le_one heps).mp
  convert h using 1
  ring

/-- If exact termination occurs at `grade`, the first successful dimension is bounded by
both the logarithmic count and the grade. `R m` is the residual after dimension `m+1`. -/
theorem exists_index_le_min {grade : ℕ} (hgrade : 0 < grade)
    {R : ℕ → ℝ} {B eps q : ℝ} (hB : 0 < B) (heps : 0 < eps)
    (hq : 0 < q) (hq1 : q < 1)
    (hdecay : ∀ m, m + 1 ≤ grade → R m ≤ B * q ^ m)
    (hfinal : R (grade - 1) = 0) :
    ∃ m, m + 1 ≤ min (decayCount (B / eps) q + 1) grade ∧ R m ≤ eps := by
  by_cases h : decayCount (B / eps) q + 1 ≤ grade
  · refine ⟨decayCount (B / eps) q, by simp [h], ?_⟩
    exact (hdecay _ h).trans (mul_pow_decayCount_le hB heps hq hq1)
  · refine ⟨grade - 1, ?_, ?_⟩
    · simpa only [Nat.sub_add_cancel hgrade, le_min_iff, le_refl, and_true] using
        Nat.le_of_lt (lt_of_not_ge h)
    · rw [hfinal]
      exact heps.le

end GeometricStopping
