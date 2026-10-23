import Numlib.Analysis.SpecialFunctions.Pow.ImplicitRecurrence

/-!
# Explicit power decrease of nonnegative gaps

The decrease is evaluated at the current gap. It implies an implicit decrease,
while exponents below one force exact finite attainment of zero. The positive
threshold separates the two nonunit exponent regimes.
-/

namespace ExplicitGap
open Set Filter Topology
variable {b : ℕ → ℝ} {c τ : ℝ}

/-- Every explicit power decrease makes nonnegative gaps nonincreasing. -/
theorem antitone (hc : 0 < c) (hb : ∀ n, 0 ≤ b n)
    (hstep : ∀ n, b (n + 1) + c * b n ^ τ ≤ b n) : Antitone b := by
  apply antitone_nat_of_succ_le
  intro n
  have hh := hstep n
  have hp := mul_nonneg hc.le (Real.rpow_nonneg (hb n) τ)
  linarith

/-- Current-gap decrease also gives a valid implicit next-gap decrease. -/
theorem implicit_decrease (hc : 0 < c) (hτ : 0 < τ) (hb : ∀ n, 0 ≤ b n)
    (hstep : ∀ n, b (n + 1) + c * b n ^ τ ≤ b n) (n : ℕ) :
    b (n + 1) + c * b (n + 1) ^ τ ≤ b n := by
  have hpow := Real.rpow_le_rpow (hb (n + 1))
    (antitone hc hb hstep (Nat.le_succ n)) hτ.le
  have hm := mul_le_mul_of_nonneg_left hpow hc.le
  linarith [hstep n]

/-- Every explicit positive power-decreasing gap sequence converges to zero. -/
theorem tendsto_zero (hc : 0 < c) (hτ : 0 < τ) (hb : ∀ n, 0 ≤ b n)
    (hstep : ∀ n, b (n + 1) + c * b n ^ τ ≤ b n) : Tendsto b atTop (nhds 0) :=
  ImplicitGap.tendsto_zero hc hτ hb (implicit_decrease hc hτ hb hstep)

/-- A positive current gap must satisfy the normalized threshold inequality. -/
theorem coefficient_le_power (hb : ∀ n, 0 ≤ b n)
    (hstep : ∀ n, b (n + 1) + c * b n ^ τ ≤ b n) {n : ℕ} (hn : 0 < b n) :
    c ≤ b n ^ (1 - τ) := by
  have hh : c * b n ^ τ ≤ b n := by linarith [hstep n, hb (n + 1)]
  apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hn τ)).mp
  have he : b n ^ τ * b n ^ (1 - τ) = b n := by
    rw [←Real.rpow_add hn]
    norm_num
  calc
    c * b n ^ τ ≤ b n := hh
    _ = b n ^ (1 - τ) * b n ^ τ := by rw [mul_comm, he]

/-- The positive boundary between the possible current-gap ranges. -/
noncomputable def threshold (c τ : ℝ) : ℝ := c ^ (1 / (1 - τ))

/-- A positive coefficient gives a positive threshold in either exponent regime. -/
theorem threshold_pos (hc : 0 < c) (τ : ℝ) : 0 < threshold c τ :=
  Real.rpow_pos_of_pos hc _

/-- Raising the threshold to the normalizing power recovers the coefficient. -/
theorem threshold_power (hc : 0 < c) (hτ : τ ≠ 1) :
    threshold c τ ^ (1 - τ) = c := by
  have hne : 1 - τ ≠ 0 := sub_ne_zero.mpr (Ne.symm hτ)
  rw [threshold, ←Real.rpow_mul hc.le, one_div_mul_cancel hne, Real.rpow_one]

/-- Below exponent one every positive gap is at least the fixed positive threshold. -/
theorem threshold_le_of_pos (hc : 0 < c) (hτ : τ < 1) (hb : ∀ n, 0 ≤ b n)
    (hstep : ∀ n, b (n + 1) + c * b n ^ τ ≤ b n) {n : ℕ} (hn : 0 < b n) :
    threshold c τ ≤ b n := by
  have hp := Real.rpow_le_rpow hc.le (coefficient_le_power hb hstep hn)
    (show 0 ≤ 1 / (1 - τ) by positivity)
  rw [←Real.rpow_mul hn.le, mul_one_div_cancel (sub_pos.mpr hτ).ne', Real.rpow_one] at hp
  exact hp

/-- Above exponent one every positive gap lies below the fixed threshold. -/
theorem le_threshold_of_pos (hc : 0 < c) (hτ : 1 < τ) (hb : ∀ n, 0 ≤ b n)
    (hstep : ∀ n, b (n + 1) + c * b n ^ τ ≤ b n) {n : ℕ} (hn : 0 < b n) :
    b n ≤ threshold c τ := by
  have hp := Real.rpow_le_rpow_of_nonpos hc
    (coefficient_le_power hb hstep hn)
    (show 1 / (1 - τ) ≤ 0 from one_div_nonpos.mpr (by linarith))
  rw [←Real.rpow_mul hn.le, mul_one_div_cancel (by linarith : 1 - τ ≠ 0),
    Real.rpow_one] at hp
  exact hp

/-- At the threshold the coefficient times the current power equals the gap. -/
theorem threshold_balance (hc : 0 < c) (hτ : τ ≠ 1) :
    c * threshold c τ ^ τ = threshold c τ := by
  calc
    _ = threshold c τ ^ (1 - τ) * threshold c τ ^ τ := by rw [threshold_power hc hτ]
    _ = _ := by rw [←Real.rpow_add (threshold_pos hc τ)]; norm_num

/-- At the boundary, the next actual gap is exactly zero. -/
theorem next_zero_of_eq_threshold (hc : 0 < c) (hτ : τ ≠ 1) (hb : ∀ n, 0 ≤ b n)
    (hstep : ∀ n, b (n + 1) + c * b n ^ τ ≤ b n) {n : ℕ}
    (hn : b n = threshold c τ) : b (n + 1) = 0 := by
  have he := threshold_balance hc hτ
  have hh := hstep n
  rw [hn, he] at hh
  exact le_antisymm (by linarith) (hb (n + 1))

/-- A subunit exponent forces exact finite attainment, rather than merely
an asymptotic superlinear upper rate. -/
theorem exists_zero (hc : 0 < c) (hτ : 0 < τ) (hτ1 : τ < 1)
    (hb : ∀ n, 0 ≤ b n) (hstep : ∀ n, b (n + 1) + c * b n ^ τ ≤ b n) :
    ∃ n, b n = 0 := by
  have ht := tendsto_zero hc hτ hb hstep
  have hpos := threshold_pos hc τ
  have hevent : ∀ᶠ n in atTop, b n < threshold c τ := (tendsto_order.mp ht).2 _ hpos
  obtain ⟨n, hn⟩ := hevent.exists
  refine ⟨n, ?_⟩
  by_contra hz
  have hbpos : 0 < b n := lt_of_le_of_ne (hb n) (Ne.symm hz)
  exact (not_lt_of_ge (threshold_le_of_pos hc hτ1 hb hstep hbpos)) hn

/-- The source current-gap factor identity includes a zero gap without division. -/
theorem factor_step (hτ : 0 < τ) (hb : ∀ n, 0 ≤ b n)
    (hstep : ∀ n, b (n + 1) + c * b n ^ τ ≤ b n) (n : ℕ) :
    b (n + 1) ≤ b n * (1 - c * b n ^ (τ - 1)) := by
  have he : b n * b n ^ (τ - 1) = b n ^ τ := by
    rcases (hb n).eq_or_lt with hz | hp
    · rw [←hz, zero_mul, Real.zero_rpow hτ.ne']
    · calc
        _ = b n ^ (1 : ℝ) * b n ^ (τ - 1) := by rw [Real.rpow_one]
        _ = _ := by rw [←Real.rpow_add hp]; norm_num
  calc
    b (n + 1) ≤ b n - c * b n ^ τ := by linarith [hstep n]
    _ = _ := by rw [←he]; ring

/-- With unit exponent the explicit update gives its exact linear factor. -/
theorem linear_step (hstep : ∀ n, b (n + 1) + c * b n ^ (1 : ℝ) ≤ b n) (n : ℕ) :
    b (n + 1) ≤ (1 - c) * b n := by
  have hh := hstep n
  rw [Real.rpow_one] at hh
  linarith

/-- A positive gap cannot coexist with a unit-exponent coefficient greater than one. -/
theorem linear_coefficient_le_one (hb : ∀ n, 0 ≤ b n)
    (hstep : ∀ n, b (n + 1) + c * b n ^ (1 : ℝ) ≤ b n) {n : ℕ} (hn : 0 < b n) :
    c ≤ 1 := by
  have hh := linear_step hstep n
  nlinarith [hb (n + 1)]

/-- Every positive gap below the unit-exponent regime consumes at least one
threshold unit of actual decrease. -/
theorem decrease_ge_threshold (hc : 0 < c) (hτ : 0 < τ) (hτ1 : τ < 1)
    (hb : ∀ n, 0 ≤ b n) (hstep : ∀ n, b (n + 1) + c * b n ^ τ ≤ b n)
    {n : ℕ} (hn : 0 < b n) : threshold c τ ≤ b n - b (n + 1) := by
  have hp := Real.rpow_le_rpow (threshold_pos hc τ).le
    (threshold_le_of_pos hc hτ1 hb hstep hn) hτ.le
  have hm := mul_le_mul_of_nonneg_left hp hc.le
  rw [threshold_balance hc hτ1.ne] at hm
  linarith [hstep n]

/-- Exact finite attainment has a uniform budget depending only on the initial
gap and the positive threshold, with the first zero retained explicitly. -/
theorem exists_zero_le_budget (hc : 0 < c) (hτ : 0 < τ) (hτ1 : τ < 1)
    (hb : ∀ n, 0 ≤ b n) (hstep : ∀ n, b (n + 1) + c * b n ^ τ ≤ b n) :
    ∃ K : ℕ, b K = 0 ∧ (∀ k < K, 0 < b k) ∧
      (K : ℝ) ≤ b 0 / threshold c τ := by
  classical
  have hex := exists_zero hc hτ hτ1 hb hstep
  let K := Nat.find hex
  have hzero : b K = 0 := Nat.find_spec hex
  have hfirst : ∀ k < K, 0 < b k := fun k hk =>
    lt_of_le_of_ne (hb k) (Ne.symm (Nat.find_min hex hk))
  have hsum : (K : ℝ) * threshold c τ ≤ b 0 - b K := by
    calc
      _ = ∑ _k ∈ Finset.range K, threshold c τ := by simp
      _ ≤ ∑ k ∈ Finset.range K, (b k - b (k + 1)) := by
        exact Finset.sum_le_sum (fun k hk => decrease_ge_threshold hc hτ hτ1 hb hstep
          (hfirst k (Finset.mem_range.mp hk)))
      _ = _ := Finset.sum_range_sub' b K
  refine ⟨K, hzero, hfirst, (le_div_iff₀ (threshold_pos hc τ)).mpr ?_⟩
  simpa only [hzero, sub_zero] using hsum

/-- Above exponent one the positive implicit orbit gives a sublinear upper
envelope. Actual explicit sequences may reach zero earlier. -/
theorem sublinear_envelope (hc : 0 < c) (hτ : 1 < τ) (hb : ∀ n, 0 ≤ b n)
    (hstep : ∀ n, b (n + 1) + c * b n ^ τ ≤ b n) :
    (∀ n, b n = 0) ∨ ∃ t : ℕ → ℝ, (∀ n, 0 < t n) ∧
      (∀ n, b n ≤ t n) ∧ Tendsto t atTop (nhds 0) ∧
      Tendsto (fun n => t (n + 1) / t n) atTop (nhds 1) := by
  have ht : 0 < τ := zero_lt_one.trans hτ
  rcases (hb 0).eq_or_lt with hz | hp
  · left
    intro n
    exact le_antisymm (((antitone hc hb hstep) (Nat.zero_le n)).trans_eq hz.symm) (hb n)
  · right
    exact ⟨ImplicitGap.orbit c τ (b 0), ImplicitGap.orbit_pos hc ht hp,
      ImplicitGap.le_orbit hc ht hb (implicit_decrease hc ht hb hstep),
      ImplicitGap.orbit_tendsto_zero hc ht hp.le, ImplicitGap.orbit_sublinear_ratio hc hτ hp⟩

end ExplicitGap
