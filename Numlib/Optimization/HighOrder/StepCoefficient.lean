import Numlib.Optimization.HighOrder.StepPowers

/-!
# Coefficients in normalized Taylor-criticality obstructions

The normalized coefficient is positive, decreases with the derivative order,
and has an exact relation to the factorial-normalized obstruction. These
facts let one choose a common radius coefficient before all accuracies.
-/

namespace HighOrderStep

/-- The normalized coefficient in the order-`j` Taylor-criticality obstruction. -/
noncomputable def criticalityCoefficient (θ C : ℝ) (j : ℕ) : ℝ :=
  (1 - θ) / (2 * (j.factorial : ℝ) * C)

/-- On the normalized parameter range every obstruction coefficient lies in `(0,1]`. -/
theorem criticalityCoefficient_mem {θ C : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1)
    (hC : 1 ≤ C) (j : ℕ) :
    0 < criticalityCoefficient θ C j ∧ criticalityCoefficient θ C j ≤ 1 := by
  have hfac : (1 : ℝ) ≤ j.factorial := by exact_mod_cast Nat.factorial_pos j
  unfold criticalityCoefficient
  constructor
  · positivity
  · apply (div_le_one (by positivity)).mpr
    nlinarith

/-- The obstruction coefficient decreases with the derivative order. -/
theorem criticalityCoefficient_antitone {θ C : ℝ} (hθ1 : θ ≤ 1) (hC : 0 < C)
    {i j : ℕ} (hij : i ≤ j) :
    criticalityCoefficient θ C j ≤ criticalityCoefficient θ C i := by
  have hfac : (i.factorial : ℝ) ≤ j.factorial := by exact_mod_cast Nat.factorial_le hij
  unfold criticalityCoefficient
  exact div_le_div_of_nonneg_left (sub_nonneg.mpr hθ1) (by positivity)
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfac (by norm_num)) hC.le)

/-- The source factorial-normalized obstruction is exactly its normalized
mixed-sum counterpart, with no loss in the coefficient. -/
theorem two_mul_criticalityCoefficient_le_sum {θ C ε δ b : ℝ} (hC : 0 < C) (j : ℕ)
    (hbound : (1 - θ) * ε * δ ^ j / j.factorial ≤ C * b) :
    2 * criticalityCoefficient θ C j * ε * δ ^ j ≤ b := by
  have he : C * (2 * criticalityCoefficient θ C j * ε * δ ^ j) =
      (1 - θ) * ε * δ ^ j / j.factorial := by
    unfold criticalityCoefficient
    field_simp
  apply (mul_le_mul_iff_right₀ hC).mp
  rw [he]
  exact hbound

end HighOrderStep
