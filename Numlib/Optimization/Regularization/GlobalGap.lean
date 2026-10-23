import Numlib.Optimization.Regularization.GlobalStep

/-!
# Positive global-gap fractions for actual model returns

At an attained global model minimum, every strictly improving return achieves
some positive fraction of the global available decrease. A zero-decrease return
has that property precisely when zero itself globally minimizes the model.
-/

namespace ModelDecrease
variable {E : Type*} [NormedAddCommGroup E]

/-- Every strictly improving return achieves a positive fraction of an attained
global model gap, with that fraction at most one. -/
theorem exists_fraction_of_strict_decrease {m : E → ℝ} {s tstar : E}
    (hmin : ∀ t, m tstar ≤ m t) (hs : m s < m 0) :
    ∃ μ : ℝ, 0 < μ ∧ μ ≤ 1 ∧ ApproximateGlobalStep m μ s := by
  let Δ := m 0 - m s
  let G := m 0 - m tstar
  have hΔ : 0 < Δ := sub_pos.mpr hs
  have hΔG : Δ ≤ G := sub_le_sub_left (hmin s) (m 0)
  have hG : 0 < G := hΔ.trans_le hΔG
  refine ⟨Δ / G, div_pos hΔ hG, (div_le_one hG).mpr hΔG, ?_⟩
  apply (approximateGlobalStep_iff_of_isMin (div_nonneg hΔ.le hG.le) hmin).mpr
  change Δ / G * G ≤ Δ
  rw [div_mul_cancel₀ _ hG.ne']

/-- At an attained global minimum, positive global-gap approximation adds no
restriction to strict returns. At zero decrease it exactly requires global
minimality of zero. -/
theorem exists_fraction_iff_of_isMin {m : E → ℝ} {s tstar : E}
    (hmin : ∀ t, m tstar ≤ m t) :
    (∃ μ : ℝ, 0 < μ ∧ μ ≤ 1 ∧ ApproximateGlobalStep m μ s) ↔
      m s < m 0 ∨ (m s = m 0 ∧ ∀ t, m 0 ≤ m t) := by
  constructor
  · rintro ⟨μ, hμ, _, hm⟩
    have hle : m s ≤ m 0 := by
      have hz := hm 0
      simpa only [sub_self, mul_zero, sub_nonneg] using hz
    rcases lt_or_eq_of_le hle with hs | hs
    · exact Or.inl hs
    · exact Or.inr ⟨hs, hm.isGlobalMin_zero hμ hs.symm⟩
  · rintro (hs | ⟨hs, hz⟩)
    · exact exists_fraction_of_strict_decrease hmin hs
    · refine ⟨1, zero_lt_one, le_rfl, ?_⟩
      intro t
      simpa only [one_mul, hs, sub_self, sub_nonpos] using hz t

end ModelDecrease
