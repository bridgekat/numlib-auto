import Numlib.Optimization.HighOrder.StepCoefficient

/-!
# Composite step powers from weighted Taylor obstructions

A residual value error contributes an extra penalty-degree power to the
Taylor criticality obstruction. Splitting the step size relative to the radius
gives a common accuracy-power floor. Unit-radius first-order tests retain the
sharper first-order rate.
-/

namespace CompositeStep
/-- The normalized coefficient for a weighted Taylor obstruction with a value remainder. -/
noncomputable def coefficient (θ C B : ℝ) (j : ℕ) : ℝ :=
  (1 - θ) / ((j.factorial : ℝ) * (2 * C + B))

/-- Every normalized coefficient lies in the unit interval away from zero. -/
theorem coefficient_mem {θ C B : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1)
    (hC : 1 ≤ C) (hB : 0 ≤ B) (j : ℕ) :
    0 < coefficient θ C B j ∧ coefficient θ C B j ≤ 1 := by
  have hf : (1 : ℝ) ≤ j.factorial := by exact_mod_cast Nat.factorial_pos _
  unfold coefficient
  constructor
  · positivity
  · apply (div_le_one (by positivity)).mpr
    nlinarith

/-- Increasing the derivative order decreases the normalized coefficient. -/
theorem coefficient_antitone {θ C B : ℝ} (hθ : θ ≤ 1) (hC : 0 < C) (hB : 0 ≤ B)
    {i j : ℕ} (hij : i ≤ j) : coefficient θ C B j ≤ coefficient θ C B i := by
  have hf : (i.factorial : ℝ) ≤ j.factorial := by exact_mod_cast Nat.factorial_le hij
  unfold coefficient
  exact div_le_div_of_nonneg_left (sub_nonneg.mpr hθ) (by positivity)
    (mul_le_mul_of_nonneg_right hf (by positivity))

/-- The normalized obstruction is the exact source left-hand side after scaling. -/
theorem coefficient_identity {θ C B : ℝ} (hD : 0 < 2 * C + B) (j : ℕ) (ε δ : ℝ) :
    (2 * C + B) * (coefficient θ C B j * ε * δ ^ j) =
      (1 - θ) * ε * δ ^ j / j.factorial := by
  unfold coefficient
  field_simp

/-- With a positive radius floor, the actual mixed step obstruction forces the
composite accuracy power `j+1` in the full penalty power `p+1`. -/
theorem power_lower_of_obstruction {p j : ℕ} (hj : 1 ≤ j) (hjp : j ≤ p)
    {θ C B a κ ε δ s : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hC : 1 ≤ C) (hB : 0 ≤ B)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (haγ : a ≤ coefficient θ C B j) (haκ : a ≤ κ)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) (hs : 0 ≤ s)
    (hfloor : s ≤ 1 → κ * ε ≤ δ)
    (hbound : (1 - θ) * ε * δ ^ j / j.factorial ≤
      C * (∑ i ∈ Finset.range j, δ ^ (i + 1) * s ^ (p - (i + 1) + 1) /
        (i + 1).factorial) + B * s ^ (p + 1)) :
    a ^ (j + 1) * ε ^ (j + 1) ≤ s ^ (p + 1) := by
  have hD : 0 < 2 * C + B := by linarith
  have hγ := (coefficient_mem hθ hθ1 hC hB j).1.le
  by_cases hs1 : s ≤ 1
  · rcases le_total s δ with hsδ | hδs
    · have hsum := Real.sum_range_mixed_pow_le_two_top hjp hs hδ.le hsδ
      have hpen : s ^ (p + 1) ≤ δ ^ j * s ^ (p - j + 1) := by
        have he : p + 1 = j + (p - j + 1) := by omega
        rw [he, pow_add]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hsδ _) (by positivity)
      have hscaled : (2 * C + B) *
          (coefficient θ C B j * ε * δ ^ j) ≤
          (2 * C + B) * (δ ^ j * s ^ (p - j + 1)) := by
        rw [coefficient_identity hD]
        exact hbound.trans (by
          have hc := mul_le_mul_of_nonneg_left hsum (by linarith : 0 ≤ C)
          have hb := mul_le_mul_of_nonneg_left hpen hB
          nlinarith only [hc, hb])
      have hp : coefficient θ C B j * ε ≤ s ^ (p - j + 1) := by
        have ht := (mul_le_mul_iff_right₀ hD).mp hscaled
        apply (mul_le_mul_iff_left₀ (pow_pos hδ j)).mp
        convert ht using 1
        ring
      have hraise := pow_le_pow_left₀ (mul_nonneg hγ hε) hp (j + 1)
      rw [mul_pow, ← pow_mul] at hraise
      have hexp : p + 1 ≤ (p - j + 1) * (j + 1) := by
        have he := HighOrderStep.degree_le_order_mul_complement
          (p := p + 1) (j := j + 1) (by omega) (by omega)
        simpa only [show p + 1 - (j + 1) + 1 = p - j + 1 by omega] using he
      have hsorder := pow_le_pow_of_le_one hs hs1 hexp
      exact (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha haγ _) (pow_nonneg hε _)).trans
        (hraise.trans hsorder)
    · have hsum := Real.sum_range_mixed_pow_le_two_first hjp hs hδ.le hδs
      have hscaled : (2 * C + B) *
          (coefficient θ C B j * ε * δ ^ j) ≤ (2 * C + B) * s ^ (p + 1) := by
        rw [coefficient_identity hD]
        exact hbound.trans (by
          have hc := mul_le_mul_of_nonneg_left hsum (by linarith : 0 ≤ C)
          have hd := mul_le_mul_of_nonneg_right hδs (pow_nonneg hs p)
          rw [← pow_succ'] at hd
          have hh := mul_le_mul_of_nonneg_left hd (by linarith : 0 ≤ 2 * C)
          nlinarith only [hc, hh])
      have hp := (mul_le_mul_iff_right₀ hD).mp hscaled
      have haf : a * ε ≤ δ :=
        (mul_le_mul_of_nonneg_right haκ hε).trans (hfloor hs1)
      have hmul := mul_le_mul (mul_le_mul_of_nonneg_right haγ hε)
        (pow_le_pow_left₀ (mul_nonneg ha hε) haf j) (pow_nonneg (mul_nonneg ha hε) j)
        (mul_nonneg hγ hε)
      have he : a ^ (j + 1) * ε ^ (j + 1) = a * ε * (a * ε) ^ j := by
        rw [mul_pow, pow_succ, pow_succ]
        ring
      rw [he]
      exact hmul.trans hp
  · have hcoef : a ^ (j + 1) * ε ^ (j + 1) ≤ 1 := by
      exact (mul_le_mul (pow_le_one₀ ha ha1) (pow_le_one₀ hε hε1)
        (pow_nonneg hε _) zero_le_one).trans_eq (by ring)
    exact hcoef.trans (one_le_pow₀ (not_le.mp hs1).le)
/-- A first-order obstruction at unit radius gives the sharper power `p`.
This bound also covers steps larger than one. -/
theorem power_lower_of_unit_obstruction {p : ℕ} {θ C B ε s : ℝ}
    (hθ : 0 < θ) (hθ1 : θ < 1) (hC : 1 ≤ C) (hB : 0 ≤ B)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hs : 0 ≤ s)
    (hbound : (1 - θ) * ε ≤ C * s ^ p + B * s ^ (p + 1)) :
    coefficient θ C B 1 * ε ≤ s ^ p := by
  by_cases hs1 : s ≤ 1
  · have hpow : s ^ (p + 1) ≤ s ^ p := by
      exact pow_le_pow_of_le_one hs hs1 (by omega)
    have hscaled : (2 * C + B) * (coefficient θ C B 1 * ε) ≤
        (2 * C + B) * s ^ p := by
      have he := coefficient_identity (θ := θ) (by linarith : 0 < 2 * C + B) 1 ε 1
      norm_num only [one_pow, Nat.factorial_one, Nat.cast_one, div_one, mul_one] at he
      rw [he]
      have hb := mul_le_mul_of_nonneg_left hpow hB
      have hc : 0 ≤ C * s ^ p := mul_nonneg (by linarith) (pow_nonneg hs _)
      nlinarith
    exact (mul_le_mul_iff_right₀ (by linarith : 0 < 2 * C + B)).mp hscaled
  · have hγ := coefficient_mem hθ hθ1 hC hB 1
    exact ((mul_le_mul_of_nonneg_right hγ.2 hε).trans (by simpa using hε1)).trans
      (one_le_pow₀ (not_le.mp hs1).le)

/-- A single coefficient chosen before the derivative order gives a common
penalty-power floor for every order up to `q`. -/
theorem uniform_power_lower_of_obstruction {p q j : ℕ}
    (hj : 1 ≤ j) (hjq : j ≤ q) (hqp : q ≤ p)
    {θ C B a κ ε δ s : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1)
    (hC : 1 ≤ C) (hB : 0 ≤ B) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (haγ : a ≤ coefficient θ C B q) (haκ : a ≤ κ)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) (hs : 0 ≤ s)
    (hfloor : s ≤ 1 → κ * ε ≤ δ)
    (hbound : (1 - θ) * ε * δ ^ j / j.factorial ≤
      C * (∑ i ∈ Finset.range j, δ ^ (i + 1) * s ^ (p - (i + 1) + 1) /
        (i + 1).factorial) + B * s ^ (p + 1)) :
    a ^ (q + 1) * ε ^ (j + 1) ≤ s ^ (p + 1) := by
  have hγ := haγ.trans (coefficient_antitone hθ1.le (by linarith) hB hjq)
  have hpow := power_lower_of_obstruction hj (hjq.trans hqp) hθ hθ1 hC hB
    ha ha1 hγ haκ hε hε1 hδ hs hfloor hbound
  exact (mul_le_mul_of_nonneg_right
    (pow_le_pow_of_le_one ha ha1 (by omega : j + 1 ≤ q + 1))
    (pow_nonneg hε _)).trans hpow

end CompositeStep
