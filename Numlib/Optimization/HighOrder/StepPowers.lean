import Numlib.Analysis.SpecialFunctions.Pow.MixedSum

/-!
# Step powers forced by Taylor-criticality obstructions

The two mixed-sum estimates yield the sharp low-order power and a uniform
high-order power. In the short-step branch the radius coefficient must also
be bounded by the obstruction coefficient; taking their minimum always
satisfies this requirement without changing the accuracy exponents.
-/

namespace HighOrderStep

/-- When the step is shorter than the positive radius, the mixed-sum
obstruction bounds the `p-j+1` step power from below. -/
theorem pow_lower_of_step_le_radius {p j : ℕ} (hjp : j ≤ p)
    {s δ a ε : ℝ} (hs : 0 ≤ s) (hδ : 0 < δ) (hsδ : s ≤ δ)
    (hbound : 2 * a * ε * δ ^ j ≤
      ∑ i ∈ Finset.range j, δ ^ (i + 1) * s ^ (p - (i + 1) + 1) /
        (i + 1).factorial) : a * ε ≤ s ^ (p - j + 1) := by
  have hh := hbound.trans (Real.sum_range_mixed_pow_le_two_top hjp hs hδ.le hsδ)
  apply (mul_le_mul_iff_left₀ (pow_pos hδ j)).mp
  nlinarith only [hh]

/-- When the positive radius is shorter than the step, the mixed-sum
obstruction bounds the `p` step power from below using that radius. -/
theorem pow_lower_of_radius_le_step {p j : ℕ} (hj : 1 ≤ j) (hjp : j ≤ p)
    {s δ a ε : ℝ} (hs : 0 ≤ s) (hδ : 0 < δ) (hδs : δ ≤ s)
    (hbound : 2 * a * ε * δ ^ j ≤
      ∑ i ∈ Finset.range j, δ ^ (i + 1) * s ^ (p - (i + 1) + 1) /
        (i + 1).factorial) : a * ε * δ ^ (j - 1) ≤ s ^ p := by
  have hh := hbound.trans (Real.sum_range_mixed_pow_le_two_first hjp hs hδ.le hδs)
  have he : δ ^ j = δ ^ (j - 1) * δ := by rw [←pow_succ, Nat.sub_add_cancel hj]
  rw [he] at hh
  apply (mul_le_mul_iff_left₀ hδ).mp
  nlinarith only [hh]

/-- A positive order at most the model degree satisfies the exponent
comparison needed to transfer the low-order step power to the high-order one. -/
theorem degree_le_order_mul_complement {p j : ℕ} (hj : 1 ≤ j) (hjp : j ≤ p) :
    p ≤ (p - j + 1) * j := by
  have hp := Nat.sub_add_cancel hjp
  have hj' := Nat.sub_add_cancel hj
  nlinarith [Nat.zero_le ((p - j) * (j - 1))]

/-- A common radius coefficient below the obstruction coefficient makes the
source high-order power implication valid in both relative-size branches. -/
theorem pow_lower_of_mixed_sum {p j : ℕ} (hj : 1 ≤ j) (hjp : j ≤ p)
    {s δ a κ ε : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) (hδ : 0 < δ)
    (ha : 0 ≤ a) (hκ : 0 ≤ κ) (hκa : κ ≤ a) (hε : 0 ≤ ε)
    (hfloor : κ * ε ≤ δ)
    (hbound : 2 * a * ε * δ ^ j ≤
      ∑ i ∈ Finset.range j, δ ^ (i + 1) * s ^ (p - (i + 1) + 1) /
        (i + 1).factorial) : a * κ ^ (j - 1) * ε ^ j ≤ s ^ p := by
  rcases le_total s δ with hsδ | hδs
  · have hb := pow_lower_of_step_le_radius hjp hs hδ hsδ hbound
    have hc := pow_le_pow_left₀ (mul_nonneg ha hε) hb j
    rw [mul_pow, ←pow_mul] at hc
    have horder := degree_le_order_mul_complement hj hjp
    have hsp := pow_le_pow_of_le_one hs hs1 horder
    have hcoef : a * κ ^ (j - 1) ≤ a ^ j := by
      calc _ ≤ a * a ^ (j - 1) :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hκ hκa _) ha
        _ = _ := by rw [mul_comm, ←pow_succ, Nat.sub_add_cancel hj]
    exact (mul_le_mul_of_nonneg_right hcoef (pow_nonneg hε _)).trans (hc.trans hsp)
  · have hb := pow_lower_of_radius_le_step hj hjp hs hδ hδs hbound
    have hpow := pow_le_pow_left₀ (mul_nonneg hκ hε) hfloor (j - 1)
    have hh := mul_le_mul_of_nonneg_left hpow (mul_nonneg ha hε)
    have he : a * κ ^ (j - 1) * ε ^ j = a * ε * (κ * ε) ^ (j - 1) := by
      have hεpow : ε ^ j = ε ^ (j - 1) * ε := by
        rw [←pow_succ, Nat.sub_add_cancel hj]
      rw [hεpow, mul_pow]
      ring
    rw [he]
    exact hh.trans hb

/-- A natural-power step lower bound gives the corresponding separated
real-power accuracy bound, including zero coefficients and zero accuracy. -/
theorem rpow_mul_le_of_pow {p j : ℕ} (hp : 0 < p) {a ε s : ℝ}
    (ha : 0 ≤ a) (hε : 0 ≤ ε) (hs : 0 ≤ s) (hbound : a * ε ^ j ≤ s ^ p) :
    a ^ (1 / (p : ℝ)) * ε ^ ((j : ℝ) / p) ≤ s := by
  have hh := (Real.rpow_inv_le_iff_of_pos (mul_nonneg ha (pow_nonneg hε _)) hs
    (show (0 : ℝ) < p by exact_mod_cast hp)).mpr
      (by simpa only [Real.rpow_natCast] using hbound)
  have he : (a * ε ^ j) ^ ((p : ℝ)⁻¹) =
      a ^ (1 / (p : ℝ)) * ε ^ ((j : ℝ) / p) := by
    rw [Real.mul_rpow ha (pow_nonneg hε _), ←Real.rpow_natCast ε j,
      ←Real.rpow_mul hε]
    simp only [div_eq_mul_inv, one_mul]
  rw [he] at hh
  exact hh

end HighOrderStep
