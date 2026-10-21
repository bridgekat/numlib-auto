/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.MeasureTheory.Integral.MeanValue`, beside
`exists_eq_const_mul_setIntegral_of_ae_nonneg`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Order.IntermediateValue

/-!
# A mean value theorem for integrals with a moving point

`MeasureTheory.exists_integral_eq_mul_integral`: if `ω` has constant sign on a convex carrier `s`
of a measure `μ` on `ℝ` and every `t ∈ s` has some `ξ_t ∈ s` with `e t = D ξ_t * ω t`, `D`
continuous on `s`, then `∫ e ∂μ = D ξ * ∫ ω ∂μ` for one `ξ ∈ s`. Unlike Mathlib's
`exists_eq_const_mul_setIntegral_of_ae_nonneg`, no measurability of `t ↦ ξ_t` is asked for, which
is the situation of every interpolation remainder.
-/

namespace MeasureTheory

variable {μ : Measure ℝ}

/-- A function of constant sign on a carrier `s` of `μ` whose integral vanishes is `μ`-almost
everywhere zero. -/
private theorem ae_eq_zero_of_integral_eq_zero {s : Set ℝ} (hsupp : μ sᶜ = 0) {g : ℝ → ℝ}
    (hg : Integrable g μ) (hsign : (∀ t ∈ s, 0 ≤ g t) ∨ ∀ t ∈ s, g t ≤ 0)
    (h0 : ∫ t, g t ∂μ = 0) : g =ᵐ[μ] 0 := by
  have hae : ∀ᵐ t ∂μ, t ∈ s := by
    rw [MeasureTheory.ae_iff]; exact hsupp
  rcases hsign with hs | hs
  · exact (integral_eq_zero_iff_of_nonneg_ae (by filter_upwards [hae] with t ht using hs t ht)
      hg).mp h0
  · have h := (integral_eq_zero_iff_of_nonneg_ae (f := fun t => -g t)
      (by filter_upwards [hae] with t ht using neg_nonneg.mpr (hs t ht)) hg.neg).mp
      (by rw [integral_neg, h0, neg_zero])
    filter_upwards [h] with t ht
    simpa using ht

/-- **A mean value theorem for integrals with a moving point.** Let `ω` be of constant sign on a
convex carrier `s` of `μ`, and let `e` be such that every `t ∈ s` has some `ξ_t ∈ s` with
`e t = D ξ_t * ω t`, for a function `D` continuous on `s`. Then `∫ e ∂μ = D ξ * ∫ ω ∂μ` for one
`ξ ∈ s`.

For `e = D * ω` with `ξ_t = t` this is the first mean value theorem for integrals; the point of the
statement is that `t ↦ ξ_t` need not be measurable, which is the situation of every interpolation
remainder. If `∫ ω ∂μ = 0` then `ω`, and with it `e`, vanishes almost everywhere, and any `ξ`
works. Otherwise put `c = ∫ e ∂μ / ∫ ω ∂μ`: were `D - c` of one strict sign on `s`, the function
`e - c ω = (D ξ_t - c) ω` would be of constant sign with zero integral, hence almost everywhere
zero, and so would `ω` be; so `D` takes values on both sides of `c` on `s`, and the intermediate
value theorem finishes. -/
theorem exists_integral_eq_mul_integral {s : Set ℝ} (hs : Convex ℝ s) (hne : s.Nonempty)
    (hsupp : μ sᶜ = 0) {e ω D : ℝ → ℝ} (he : Integrable e μ) (hω : Integrable ω μ)
    (hD : ContinuousOn D s) (hsign : (∀ t ∈ s, 0 ≤ ω t) ∨ ∀ t ∈ s, ω t ≤ 0)
    (hpt : ∀ t ∈ s, ∃ ξ ∈ s, e t = D ξ * ω t) :
    ∃ ξ ∈ s, ∫ t, e t ∂μ = D ξ * ∫ t, ω t ∂μ := by
  have hae : ∀ᵐ t ∂μ, t ∈ s := by
    rw [MeasureTheory.ae_iff]; exact hsupp
  choose! ξ hξ heq using hpt
  by_cases hI : ∫ t, ω t ∂μ = 0
  · obtain ⟨t₀, ht₀⟩ := hne
    refine ⟨t₀, ht₀, ?_⟩
    rw [hI, mul_zero]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [ae_eq_zero_of_integral_eq_zero hsupp hω hsign hI, hae] with t ht hts
    simp only [heq t hts, ht, Pi.zero_apply, mul_zero]
  set c : ℝ := (∫ t, e t ∂μ) / ∫ t, ω t ∂μ with hc
  have hce : ∫ t, e t ∂μ = c * ∫ t, ω t ∂μ := by rw [hc, div_mul_cancel₀ _ hI]
  -- `D - c` cannot keep one strict sign `σ` on `s`
  have key : ∀ σ : ℝ, (∀ ξ' ∈ s, 0 < σ * (D ξ' - c)) → False := by
    intro σ hpos
    have hg : Integrable (fun t => σ * (e t - c * ω t)) μ :=
      (he.sub (hω.const_mul c)).const_mul σ
    have hg0 : ∫ t, σ * (e t - c * ω t) ∂μ = 0 := by
      rw [integral_const_mul, integral_sub he (hω.const_mul c), integral_const_mul, hce, sub_self,
        mul_zero]
    have hgt : ∀ t ∈ s, σ * (e t - c * ω t) = σ * (D (ξ t) - c) * ω t := fun t ht => by
      rw [heq t ht]; ring
    have hgsign : (∀ t ∈ s, 0 ≤ σ * (e t - c * ω t)) ∨ ∀ t ∈ s, σ * (e t - c * ω t) ≤ 0 := by
      rcases hsign with h | h
      · exact Or.inl fun t ht => by
          rw [hgt t ht]; exact mul_nonneg (hpos _ (hξ t ht)).le (h t ht)
      · exact Or.inr fun t ht => by
          rw [hgt t ht]; exact mul_nonpos_of_nonneg_of_nonpos (hpos _ (hξ t ht)).le (h t ht)
    refine hI (integral_eq_zero_of_ae ?_)
    filter_upwards [ae_eq_zero_of_integral_eq_zero hsupp hg hgsign hg0, hae] with t ht hts
    have h := hgt t hts
    rw [ht, Pi.zero_apply] at h
    rw [Pi.zero_apply]
    exact (mul_eq_zero.mp h.symm).resolve_left (hpos _ (hξ t hts)).ne'
  have hA : ∃ ξ₁ ∈ s, D ξ₁ ≤ c := by
    by_contra h
    push Not at h
    exact key 1 fun ξ' hξ' => by linarith [h ξ' hξ']
  have hB : ∃ ξ₂ ∈ s, c ≤ D ξ₂ := by
    by_contra h
    push Not at h
    exact key (-1) fun ξ' hξ' => by linarith [h ξ' hξ']
  obtain ⟨ξ₁, hξ₁, h₁⟩ := hA
  obtain ⟨ξ₂, hξ₂, h₂⟩ := hB
  have hsub : Set.uIcc ξ₁ ξ₂ ⊆ s := hs.ordConnected.uIcc_subset hξ₁ hξ₂
  obtain ⟨ξ₀, hξ₀, hξ₀eq⟩ :=
    intermediate_value_uIcc (hD.mono hsub) (Set.mem_uIcc.mpr (Or.inl ⟨h₁, h₂⟩))
  exact ⟨ξ₀, hsub hξ₀, by rw [hce, hξ₀eq]⟩

end MeasureTheory
