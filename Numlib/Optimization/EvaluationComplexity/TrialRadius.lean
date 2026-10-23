import Numlib.Optimization.EvaluationComplexity.TrialUpdates

/-!
# Radius floors on trial prefixes

Operational trust-region updates preserve a floor determined by a cap and a
scaled model-gap bound whenever sufficiently small trial radii are very successful.
Accuracy-only iterations leave the radius unchanged.
-/

namespace EvaluationComplexity.TrialTrustRegionUpdates
variable {T : Set ℕ} {δ ρ : ℕ → ℝ} {η₁ η₂ γ₁ γ₂ γ₃ δmax : ℝ} {N : ℕ}

/-- Restricting a finite update trace preserves all primitive update rules. -/
theorem restrict (h : TrialTrustRegionUpdates T δ ρ η₁ η₂ γ₁ γ₂ γ₃ δmax N)
    {M : ℕ} (hM : M ≤ N) : TrialTrustRegionUpdates T δ ρ η₁ η₂ γ₁ γ₂ γ₃ δmax M :=
  { h with
    update := fun i hi => h.update i (hi.trans_le hM)
    inactive := fun i hi => h.inactive i (hi.trans_le hM) }

/-- Every permitted update contracts by at most the smallest radius factor. -/
theorem gamma1_mul_le (h : TrialTrustRegionUpdates T δ ρ η₁ η₂ γ₁ γ₂ γ₃ δmax N)
    {i : ℕ} (hi : i < N) : γ₁ * δ i ≤ δ (i + 1) := by
  have hγ : γ₁ ≤ 1 := h.gamma1_le_gamma2.trans h.gamma2_lt_one.le
  by_cases hT : i ∈ T
  · have hu := h.update i hi hT
    split_ifs at hu
    · exact (mul_le_of_le_one_left (h.pos (by omega)).le hγ).trans hu.1
    · exact (mul_le_mul_of_nonneg_right h.gamma1_le_gamma2 (h.pos (by omega)).le).trans hu.1
    · exact hu.1
  · rw [h.inactive_eq hi hT]
    exact mul_le_of_le_one_left (h.pos (by omega)).le hγ

/-- A very successful trial does not shrink its radius. -/
theorem le_next_of_very_successful
    (h : TrialTrustRegionUpdates T δ ρ η₁ η₂ γ₁ γ₂ γ₃ δmax N)
    {i : ℕ} (hi : i < N) (hT : i ∈ T) (hvery : η₂ ≤ ρ i) : δ i ≤ δ (i + 1) := by
  have hu := h.update i hi hT
  have hu' : δ (i + 1) ∈ Set.Icc (δ i) (min δmax (γ₃ * δ i)) := by
    simpa only [ite_eq_left hvery] using hu
  exact hu'.1

/-- A small-radius success implication gives a uniform floor through a fixed
prefix. The gap lower bound is required only on actual trial iterations. -/
theorem min_cap_scaled_gap_le
    (h : TrialTrustRegionUpdates T δ ρ η₁ η₂ γ₁ γ₂ γ₃ δmax N)
    {θ c κ μ : ℝ} (hθ : 0 ≤ θ) (hinit : θ ≤ δ 0) (hc : 0 ≤ c)
    (hκ : κ ≤ γ₁ * c) (hμ : 0 ≤ μ) (g : ℕ → ℝ)
    (hgap : ∀ i < N, i ∈ T → μ ≤ g i)
    (hgood : ∀ i < N, i ∈ T → δ i ≤ min θ (c * g i) → η₂ ≤ ρ i)
    {k : ℕ} (hk : k ≤ N) : min (γ₁ * θ) (κ * μ) ≤ δ k := by
  induction k with
  | zero =>
    have hγ : γ₁ ≤ 1 := h.gamma1_le_gamma2.trans h.gamma2_lt_one.le
    exact (min_le_left _ _).trans ((mul_le_of_le_one_left hθ hγ).trans hinit)
  | succ k ih =>
    have hprev := ih (by omega)
    by_cases hT : k ∈ T
    · by_cases hlarge : min (γ₁ * θ) (κ * μ) ≤ γ₁ * δ k
      · exact hlarge.trans (h.gamma1_mul_le (by omega))
      · have hlt : γ₁ * δ k < min (γ₁ * θ) (κ * μ) := lt_of_not_ge hlarge
        have hcap : δ k ≤ θ := by
          have hh := hlt.trans_le (min_le_left _ _)
          nlinarith [h.gamma1_pos]
        have hscale : δ k ≤ c * g k := by
          have hh := hlt.trans_le (min_le_right _ _)
          have hm := mul_le_mul_of_nonneg_right hκ hμ
          have hg := mul_le_mul_of_nonneg_left (hgap k (by omega) hT)
            (mul_nonneg h.gamma1_pos.le hc)
          nlinarith [h.gamma1_pos]
        exact hprev.trans (h.le_next_of_very_successful (by omega) hT
          (hgood k (by omega) hT (le_min hcap hscale)))
    · rw [h.inactive_eq (by omega) hT]
      exact hprev

end EvaluationComplexity.TrialTrustRegionUpdates
