import Numlib.Krylov.Convergence.ChebyshevFactor
import Mathlib.Tactic

/-!
# Integer logarithmic budgets at unrestricted relative tolerances

An integer ceiling can be negative. A natural ceiling explicitly enforces the
nonnegative iteration budget required when tolerances have no upper restriction.
-/

namespace Krylov
/-- An unrestricted relative tolerance can make the printed integer logarithmic budget negative. -/
theorem exists_negative_logarithmic_budget {C K : ℝ} (hC : 0 < C) (hK : 1 < K) :
    ∃ θ > 0, (⌈Real.log (C / θ) /
      Real.log ((Real.sqrt K + 1) / (Real.sqrt K - 1))⌉ : ℤ) + 1 = -1 := by
  let q := (Real.sqrt K + 1) / (Real.sqrt K - 1)
  have hs : 1 < Real.sqrt K := by
    rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)]
    simpa using hK
  have hq : 1 < q := by
    apply (lt_div_iff₀ (by linarith : 0 < Real.sqrt K - 1)).mpr
    linarith
  have hq0 : 0 < q := zero_lt_one.trans hq
  have hl : Real.log q ≠ 0 := ne_of_gt (Real.log_pos hq)
  refine ⟨C * q ^ 2, by positivity, ?_⟩
  change (⌈Real.log (C / (C * q ^ 2)) / Real.log q⌉ : ℤ) + 1 = -1
  have he : C / (C * q ^ 2) = (q ^ 2)⁻¹ := by field_simp
  rw [he, Real.log_inv, Real.log_pow]
  have hd : -(2 * Real.log q) / Real.log q = (-2 : ℝ) := by field_simp
  norm_num only [Nat.cast_ofNat] at *
  rw [hd]
  norm_num
end Krylov
