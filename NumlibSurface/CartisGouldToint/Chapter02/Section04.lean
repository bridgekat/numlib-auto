import NumlibSurface.CartisGouldToint.Chapter02.Section03

/-!
# Cartis–Gould–Toint, Section 2.4: regularization iteration counts

Lemma 2.4.1 follows from the three-case update (2.4.4) independently of the chosen
objective model. Successful-iteration counts use the preceding section's prefix
convention, with `N` updates from `σ₀` to `σ_N`.
-/

namespace CartisGouldToint

/-- **Lemma 2.4.1.** An upper bound on the current regularization parameter and
the AR1 update rule control the total updates in terms of successful updates.
Only the exact parameter-update component of AR1 is required. -/
theorem lemma_2_4_1 {σ ρ : ℕ → ℝ} {η₁ η₂ γ₁ γ₂ γ₃ σmin σmax : ℝ} {N : ℕ}
    (h : EvaluationComplexity.RegularizationParameterUpdates σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin N)
    (hmax : σ N ≤ σmax) :
    (N : ℝ) ≤ (successfulIterations ρ η₁ N).card *
        (1 + |Real.log γ₁| / Real.log γ₂) +
      Real.log (σmax / σ 0) / Real.log γ₂ :=
  EvaluationComplexity.iteration_bound_of_parameter_upper (S := {i | η₁ ≤ ρ i})
    (fun _ hi => h.pos hi) h.gamma1_pos h.gamma1_lt_one h.one_lt_gamma2 hmax
    (fun _ hi hs => h.successful_ge hi hs)
    (fun _ hi hu => h.unsuccessful_ge hi hu)

end CartisGouldToint
