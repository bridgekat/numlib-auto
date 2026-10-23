import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic
/-!
# Natural logarithmic budgets for geometric decay

Natural ceilings include the case where the tolerance already exceeds the
initial envelope. A finite-grade exactness bound can be combined with the
logarithmic budget without imposing a small-tolerance hypothesis.
-/

namespace GeometricDecay
/-- The natural logarithmic budget clamps a negative displayed ceiling at zero. -/
noncomputable def budget (C ε q : ℝ) : ℕ := ⌈Real.log (C / ε) / Real.log q⁻¹⌉₊

/-- An actual geometric sequence falls below the tolerance at its logarithmic budget,
including a large tolerance where the natural budget is zero. -/
theorem bound_at_budget {C ε q : ℝ} (hC : 0 ≤ C) (hε : 0 < ε)
    (hq : 0 < q) (hq1 : q < 1) : C * q ^ budget C ε q ≤ ε := by
  rcases hC.eq_or_lt with hzero | hpos
  · simp only [← hzero, zero_mul]
    exact hε.le
  have hlog : 0 < Real.log q⁻¹ := Real.log_pos ((one_lt_inv₀ hq).mpr hq1)
  have hn : Real.log (C / ε) / Real.log q⁻¹ ≤ (budget C ε q : ℝ) :=
    Nat.le_ceil _
  have hh : Real.log C - Real.log ε ≤ (budget C ε q : ℝ) * -Real.log q := by
    simpa only [Real.log_div hpos.ne' hε.ne', Real.log_inv] using
      (div_le_iff₀ hlog).mp hn
  have he : Real.log (C * q ^ budget C ε q) ≤ Real.log ε := by
    rw [Real.log_mul hpos.ne' (pow_ne_zero _ hq.ne'), Real.log_pow]
    nlinarith
  exact (Real.log_le_log_iff (mul_pos hpos (pow_pos hq _)) hε).mp he

/-- A finite residual sequence satisfying geometric bounds reaches the tolerance by the
smaller of the logarithmic budget and its exact terminal grade. Indices start at zero. -/
theorem exists_le_min_grade {C ε q : ℝ} (hC : 0 ≤ C) (hε : 0 < ε)
    (hq : 0 < q) (hq1 : q < 1) (R : ℕ → ℝ) {G : ℕ} (hG : 0 < G)
    (hexact : R (G - 1) = 0) (hbound : ∀ m < G, R m ≤ C * q ^ m) :
    ∃ m : ℕ, m < G ∧ m + 1 ≤ min (budget C ε q + 1) G ∧ R m ≤ ε := by
  by_cases hn : budget C ε q < G
  · refine ⟨budget C ε q, hn, ?_, ?_⟩
    · omega
    · exact (hbound _ hn).trans (bound_at_budget hC hε hq hq1)
  · refine ⟨G - 1, by omega, ?_, ?_⟩
    · omega
    · rw [hexact]
      exact hε.le
end GeometricDecay
