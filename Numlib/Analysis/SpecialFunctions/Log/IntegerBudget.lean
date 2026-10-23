import Numlib.Analysis.SpecialFunctions.Log.GeometricBudget
import Mathlib.Tactic
/-!
# A domain obstruction for unrestricted integer logarithmic budgets

At a sufficiently large positive tolerance the literal integer ceiling plus
one equals minus one. Natural ceilings or explicit smallness domains avoid
this numerical obstruction.
-/

namespace GeometricDecay
/-- The unrestricted integer version of a logarithmic budget can be negative at a positive
tolerance, even when the prefactor is positive and the contraction factor lies in `(0,1)`. -/
theorem exists_negative_integer_budget {C q : ℝ} (hC : 0 < C) (hq : 0 < q) (hq1 : q < 1) :
    ∃ ε : ℝ, 0 < ε ∧ (⌈Real.log (C / ε) / Real.log q⁻¹⌉ : ℤ) + 1 = -1 := by
  let ε := C / q ^ 2
  have hε : 0 < ε := by dsimp [ε]; positivity
  refine ⟨ε, hε, ?_⟩
  have hratio : C / ε = q ^ 2 := by
    dsimp [ε]
    field_simp
  have hlog : Real.log q ≠ 0 := by
    have hi := Real.log_pos ((one_lt_inv₀ hq).mpr hq1)
    rw [Real.log_inv] at hi
    linarith
  have he : Real.log (C / ε) / Real.log q⁻¹ = -2 := by
    rw [hratio, Real.log_pow, Real.log_inv]
    field_simp
    ring
  rw [he]
  norm_num
end GeometricDecay
