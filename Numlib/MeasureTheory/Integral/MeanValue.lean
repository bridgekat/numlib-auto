/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
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

Let $\mu$ be a measure on $\mathbb{R}$ that is carried by a nonempty convex set $s$, that is,
$\mu(\mathbb{R} \setminus s) = 0$. Let $\omega$ be an integrable function of constant sign on $s$,
let $D$ be continuous on $s$, and let $e$ be an integrable function such that every $t \in s$ has
some $\xi_t \in s$ with $e(t) = D(\xi_t) \, \omega(t)$. Then there is one $\xi \in s$ with
$$\int e \, d\mu = D(\xi) \int \omega \, d\mu.$$
Unlike Mathlib's `exists_eq_const_mul_setIntegral_of_ae_nonneg`, the result does not ask for the
map $t \mapsto \xi_t$ to be measurable. This is the situation of every interpolation remainder.

## Main results

* `MeasureTheory.exists_integral_eq_mul_integral`: the statement above.
-/

namespace MeasureTheory

variable {μ : Measure ℝ}

/-- If $\mu(\mathbb{R} \setminus s) = 0$ and an integrable function $g$ has constant sign on $s$ and
integral $0$, then $g = 0$ $\mu$-almost everywhere. -/
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

/-- **A mean value theorem for integrals with a moving point.** Let $\mu$ be a measure on
$\mathbb{R}$, and let $s \subseteq \mathbb{R}$ be a nonempty convex set with
$\mu(\mathbb{R} \setminus s) = 0$. Let $e, \omega, D \colon \mathbb{R} \to \mathbb{R}$, where
$e$ and $\omega$ are $\mu$-integrable, $D$ is continuous on $s$, and either $\omega \ge 0$ on
$s$ or $\omega \le 0$ on $s$. If for every $t \in s$ there is $\xi_t \in s$ with
$e(t) = D(\xi_t) \, \omega(t)$, then there is $\xi \in s$ with
$$\int e \, d\mu = D(\xi) \int \omega \, d\mu.$$

For $e = D \omega$ and $\xi_t = t$ this is the first mean value theorem for integrals. The map
$t \mapsto \xi_t$ need not be measurable, and this is the situation of every interpolation
remainder.

If $\int \omega \, d\mu = 0$, then $\omega$ and $e$ vanish almost everywhere, and every $\xi$
works. Otherwise let $c = \int e \, d\mu / \int \omega \, d\mu$. If $D - c$ had one strict sign
on $s$, then $e - c \omega = (D(\xi_t) - c) \, \omega$ would have constant sign and integral
$0$, so it would vanish almost everywhere, and so would $\omega$. Hence $D$ takes values on both
sides of $c$ on $s$, and the intermediate value theorem gives $\xi$. -/
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
