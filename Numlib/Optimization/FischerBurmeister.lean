import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith

/-! # The Fischer–Burmeister complementarity residual -/

namespace Numlib.Optimization

/-- The Fischer–Burmeister residual vanishes when two nonnegative arguments are complementary. -/
noncomputable def fischerBurmeister (a b : ℝ) : ℝ :=
  √(a ^ 2 + b ^ 2) - a - b

/-- Vanishing of the Fischer–Burmeister residual characterizes scalar complementarity. -/
theorem fischerBurmeister_eq_zero_iff {a b : ℝ} :
    fischerBurmeister a b = 0 ↔ 0 ≤ a ∧ 0 ≤ b ∧ a * b = 0 := by
  unfold fischerBurmeister
  constructor
  · intro h
    have hs : √(a ^ 2 + b ^ 2) = a + b := by linarith
    have hsum : 0 ≤ a + b := by
      rw [← hs]
      exact Real.sqrt_nonneg _
    have hsq := Real.sq_sqrt (add_nonneg (sq_nonneg a) (sq_nonneg b))
    rw [hs] at hsq
    have hab : a * b = 0 := by nlinarith
    rcases mul_eq_zero.mp hab with ha | hb
    · exact ⟨by simp [ha], by simpa [ha] using hsum, hab⟩
    · exact ⟨by simpa [hb] using hsum, by simp [hb], hab⟩
  · rintro ⟨ha, hb, hab⟩
    rcases mul_eq_zero.mp hab with h | h
    · simp [h, Real.sqrt_sq hb]
    · simp [h, Real.sqrt_sq ha]

end Numlib.Optimization
