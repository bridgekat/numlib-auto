import Numlib.Optimization.EvaluationComplexity.TrialUpdates

/-!
# Threshold bounds with accuracy-only regularization iterations

Trial updates obey the usual three intervals. Accuracy-only iterations preserve
the parameter. A proved very-successful threshold therefore bounds all endpoints.
-/

namespace EvaluationComplexity.TrialRegularizationUpdates
variable {T : Set ℕ} {σ ρ : ℕ → ℝ} {η₁ η₂ γ₁ γ₂ γ₃ σmin : ℝ} {N : ℕ}

/-- A very-successful threshold bounds every parameter, including across
accuracy-only steps that leave it unchanged. -/
theorem le_max_initial_threshold
    (h : TrialRegularizationUpdates T σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin N)
    {threshold : ℝ} (hgood : ∀ i < N, i ∈ T → threshold ≤ σ i → η₂ ≤ ρ i)
    {i : ℕ} (hi : i ≤ N) : σ i ≤ max (σ 0) (γ₃ * threshold) := by
  classical
  induction i with
  | zero => exact le_max_left _ _
  | succ i ih =>
    have hp := ih (by omega)
    by_cases hT : i ∈ T
    · have hu := h.update i (by omega) hT
      by_cases h₂ : η₂ ≤ ρ i
      · rw [ite_eq_left h₂] at hu
        exact hu.2.trans hp
      · have hsmall : σ i < threshold :=
          lt_of_not_ge (fun hh => h₂ (hgood i (by omega) hT hh))
        have hγ₃ : 0 < γ₃ := (zero_lt_one.trans h.one_lt_gamma2).trans h.gamma2_lt_gamma3
        have hup : σ (i + 1) ≤ γ₃ * σ i := by
          rw [ite_eq_right h₂] at hu
          split_ifs at hu with h₁
          · exact hu.2.trans (mul_le_mul_of_nonneg_right h.gamma2_lt_gamma3.le
              (h.pos (by omega)).le)
          · exact hu.2
        exact hup.trans ((mul_le_mul_of_nonneg_left hsmall.le hγ₃.le).trans
          (le_max_right _ _))
    · rw [h.inactive_eq (by omega) hT]
      exact hp

end EvaluationComplexity.TrialRegularizationUpdates
