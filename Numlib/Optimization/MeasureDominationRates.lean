import Numlib.Optimization.MeasureDomination
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Quantitative rates for scalar descent

Reciprocal powers turn superunit descent exponents into linear growth of a potential.
The implicit estimate splits large drops from comparable consecutive gaps.
-/

namespace Optimization.MeasureDomination

/-- The reciprocal-power potential lies above its tangent at the larger argument. -/
theorem reciprocal_rpow_difference {v w τ : ℝ} (hv : 0 < v) (hvw : v ≤ w)
    (hτ : 1 < τ) :
    (τ - 1) * (w - v) / w ^ τ ≤ v ^ (1 - τ) - w ^ (1 - τ) := by
  rcases hvw.eq_or_lt with rfl | hvw
  · simp
  have hw : 0 < w := hv.trans hvw
  obtain ⟨c, hc, he⟩ := exists_hasDerivAt_eq_slope
    (fun x : ℝ => x ^ (1 - τ)) (fun x => (1 - τ) * x ^ ((1 - τ) - 1)) hvw
    (by
      apply ContinuousOn.rpow_const continuousOn_id
      intro x hx
      exact Or.inl (ne_of_gt (hv.trans_le hx.1)))
    (fun x hx => Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt (hv.trans hx.1))))
  have hc0 : 0 < c := hv.trans hc.1
  have hp := Real.rpow_le_rpow_of_nonpos hc0 hc.2.le (by linarith : -τ ≤ 0)
  have hm := mul_le_mul_of_nonpos_left hp (by linarith : 1 - τ ≤ 0)
  have he' : (1 - τ) * c ^ (-τ) * (w - v) = w ^ (1 - τ) - v ^ (1 - τ) := by
    have heq : (1 - τ) - 1 = -τ := by ring
    rw [heq] at he
    exact (eq_div_iff (ne_of_gt (sub_pos.mpr hvw))).mp he
  have hmul := mul_le_mul_of_nonneg_right hm (sub_nonneg.mpr hvw.le)
  rw [he', Real.rpow_neg hw.le] at hmul
  rw [div_eq_mul_inv]
  nlinarith

/-- Explicit polynomial descent increases the reciprocal-power potential by a fixed amount. -/
theorem explicit_recurrence_potential {u : ℕ → ℝ} {a τ : ℝ}
    (ha : 0 < a) (hτ : 1 < τ) (hu : ∀ k, 0 ≤ u k)
    (hstep : ∀ k, u (k + 1) ≤ u k - a * u k ^ τ)
    {k : ℕ} (hk : 0 < u k) :
    u 0 ^ (1 - τ) + (k : ℝ) * (a * (τ - 1)) ≤ u k ^ (1 - τ) := by
  have hm := explicit_recurrence_antitone ha.le hu hstep
  have hpos : ∀ j ≤ k, 0 < u j := fun j hj => hk.trans_le (hm hj)
  have hp : ∀ j < k, a * (τ - 1) ≤ u (j + 1) ^ (1 - τ) - u j ^ (1 - τ) := by
    intro j hj
    have hj0 := hpos j (by omega)
    have hdiff := reciprocal_rpow_difference (hpos (j + 1) (by omega))
      (hm (by omega : j ≤ j + 1)) hτ
    have hden : 0 < u j ^ τ := Real.rpow_pos_of_pos hj0 _
    have hd : a ≤ (u j - u (j + 1)) / u j ^ τ :=
      (le_div_iff₀ hden).2 (by linarith [hstep j])
    have hh := mul_le_mul_of_nonneg_left hd (by linarith : 0 ≤ τ - 1)
    rw [← mul_div_assoc] at hh
    simpa [mul_comm] using hh.trans hdiff
  have hsum := Finset.sum_le_sum (s := Finset.range k) (fun j hj => hp j (Finset.mem_range.mp hj))
  rw [Finset.sum_range_sub (fun j => u j ^ (1 - τ)) k] at hsum
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  linarith

/-- Polynomial upper decay for explicit descent, with exact zeros included. -/
theorem explicit_recurrence_polynomial_bound {u : ℕ → ℝ} {a τ : ℝ}
    (ha : 0 < a) (hτ : 1 < τ) (hu : ∀ k, 0 ≤ u k)
    (hstep : ∀ k, u (k + 1) ≤ u k - a * u k ^ τ) (k : ℕ) :
    u k ≤ (u 0 ^ (1 - τ) + (k : ℝ) * (a * (τ - 1))) ^ (-1 / (τ - 1)) := by
  by_cases hk : u k = 0
  · rw [hk]
    exact Real.rpow_nonneg (by
      have hpow := Real.rpow_nonneg (hu 0) (1 - τ)
      have hmul : 0 ≤ (k : ℝ) * (a * (τ - 1)) := mul_nonneg (Nat.cast_nonneg _)
        (mul_nonneg ha.le (by linarith))
      linarith) _
  have hk0 : 0 < u k := lt_of_le_of_ne (hu k) (Ne.symm hk)
  have hstart := (explicit_recurrence_antitone ha.le hu hstep) (Nat.zero_le k)
  have hu0 : 0 < u 0 := hk0.trans_le hstart
  have hpot := explicit_recurrence_potential ha hτ hu hstep hk0
  have hb : 0 < u 0 ^ (1 - τ) + (k : ℝ) * (a * (τ - 1)) := by positivity
  have hr := Real.rpow_le_rpow_of_nonpos hb hpot
    (div_nonpos_of_nonpos_of_nonneg (by norm_num) (by linarith) : -1 / (τ - 1) ≤ 0)
  have he : (1 - τ) * (-1 / (τ - 1)) = 1 := by field_simp [ne_of_gt (sub_pos.mpr hτ)]; ring
  rwa [← Real.rpow_mul hk0.le, he, Real.rpow_one] at hr

/-- Implicit descent of a nonnegative sequence is monotone. -/
theorem implicit_recurrence_antitone {u : ℕ → ℝ} {a τ : ℝ}
    (ha : 0 ≤ a) (hu : ∀ k, 0 ≤ u k)
    (hstep : ∀ k, u (k + 1) + a * u (k + 1) ^ τ ≤ u k) : Antitone u := by
  apply antitone_nat_of_succ_le
  intro k
  have hp := mul_nonneg ha (Real.rpow_nonneg (hu (k + 1)) τ)
  linarith [hstep k]

/-- A uniform positive increment for the implicit reciprocal-power potential.
Large relative drops and comparable consecutive gaps are handled separately. -/
theorem implicit_recurrence_potential_step {v w M a τ : ℝ}
    (hv : 0 < v) (hwM : w ≤ M) (ha : 0 < a) (hτ : 1 < τ)
    (hstep : v + a * v ^ τ ≤ w) :
    min (a * (τ - 1) / 2 ^ τ)
      (((1 / 2 : ℝ) ^ (1 - τ) - 1) * M ^ (1 - τ)) ≤
      v ^ (1 - τ) - w ^ (1 - τ) := by
  have hpv : 0 < v ^ τ := Real.rpow_pos_of_pos hv _
  have hvw : v ≤ w := by nlinarith
  have hw : 0 < w := hv.trans_le hvw
  have hM : 0 < M := hw.trans_le hwM
  by_cases hcomp : w ≤ 2 * v
  · apply (min_le_left _ _).trans
    have hpw : 0 < w ^ τ := Real.rpow_pos_of_pos hw _
    have hp2 : 0 < (2 : ℝ) ^ τ := Real.rpow_pos_of_pos (by norm_num) _
    have hpow := Real.rpow_le_rpow hw.le hcomp (by linarith : 0 ≤ τ)
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hv.le] at hpow
    have hdec : a * v ^ τ ≤ w - v := by linarith
    have hratio : a / 2 ^ τ ≤ (w - v) / w ^ τ := by
      apply (div_le_div_iff₀ hp2 hpw).2
      nlinarith
    have hh := mul_le_mul_of_nonneg_left hratio (by linarith : 0 ≤ τ - 1)
    rw [← mul_div_assoc, ← mul_div_assoc] at hh
    simpa [mul_comm] using hh.trans (reciprocal_rpow_difference hv hvw hτ)
  · apply (min_le_right _ _).trans
    have hhalf : v ≤ w * (1 / 2) := by linarith
    have hpow := Real.rpow_le_rpow_of_nonpos hv hhalf (by linarith : 1 - τ ≤ 0)
    rw [Real.mul_rpow hw.le (by norm_num : (0 : ℝ) ≤ 1 / 2)] at hpow
    have hfactor : 0 < (1 / 2 : ℝ) ^ (1 - τ) - 1 := by
      have := Real.one_lt_rpow_of_pos_of_lt_one_of_neg
        (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
        (by linarith : 1 - τ < 0)
      linarith
    have hbound := Real.rpow_le_rpow_of_nonpos hw hwM (by linarith : 1 - τ ≤ 0)
    have hh := mul_le_mul_of_nonneg_left hbound hfactor.le
    nlinarith

/-- The potential increment used in the polynomial implicit rate. -/
noncomputable def implicitPolynomialConstant (M a τ : ℝ) : ℝ :=
  min (a * (τ - 1) / 2 ^ τ)
    (((1 / 2 : ℝ) ^ (1 - τ) - 1) * M ^ (1 - τ))

/-- The implicit polynomial rate constant is positive for positive initial gap. -/
theorem implicitPolynomialConstant_pos {M a τ : ℝ}
    (hM : 0 < M) (ha : 0 < a) (hτ : 1 < τ) :
    0 < implicitPolynomialConstant M a τ := by
  apply lt_min
  · exact div_pos (mul_pos ha (sub_pos.mpr hτ)) (Real.rpow_pos_of_pos (by norm_num) _)
  · apply mul_pos _ (Real.rpow_pos_of_pos hM _)
    exact sub_pos.mpr (Real.one_lt_rpow_of_pos_of_lt_one_of_neg (by norm_num)
      (by norm_num) (by linarith))

/-- Polynomial upper decay for implicit descent. The constant depends on the initial gap;
this accommodates arbitrarily large relative drops and exact zeros. -/
theorem implicit_recurrence_polynomial_bound {u : ℕ → ℝ} {a τ : ℝ}
    (ha : 0 < a) (hτ : 1 < τ) (hu : ∀ k, 0 ≤ u k)
    (hstep : ∀ k, u (k + 1) + a * u (k + 1) ^ τ ≤ u k) (k : ℕ) :
    u k ≤ (u 0 ^ (1 - τ) + (k : ℝ) *
      implicitPolynomialConstant (u 0) a τ) ^ (-1 / (τ - 1)) := by
  have hm := implicit_recurrence_antitone ha.le hu hstep
  by_cases hk : u k = 0
  · rw [hk]
    apply Real.rpow_nonneg
    have hconst : 0 ≤ implicitPolynomialConstant (u 0) a τ := by
      unfold implicitPolynomialConstant
      apply le_min
      · positivity
      · apply mul_nonneg _ (Real.rpow_nonneg (hu 0) _)
        have := Real.one_lt_rpow_of_pos_of_lt_one_of_neg
          (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
          (by linarith : 1 - τ < 0)
        linarith
    exact add_nonneg (Real.rpow_nonneg (hu 0) _)
      (mul_nonneg (Nat.cast_nonneg _) hconst)
  have hk0 : 0 < u k := lt_of_le_of_ne (hu k) (Ne.symm hk)
  have hpos : ∀ j ≤ k, 0 < u j := fun j hj => hk0.trans_le (hm hj)
  have hp : ∀ j < k, implicitPolynomialConstant (u 0) a τ ≤
      u (j + 1) ^ (1 - τ) - u j ^ (1 - τ) := by
    intro j hj
    exact implicit_recurrence_potential_step (hpos (j + 1) (by omega))
      (hm (Nat.zero_le j)) ha hτ (hstep j)
  have hsum := Finset.sum_le_sum (s := Finset.range k)
    (fun j hj => hp j (Finset.mem_range.mp hj))
  rw [Finset.sum_range_sub (fun j => u j ^ (1 - τ)) k] at hsum
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  have hb : 0 < u 0 ^ (1 - τ) + (k : ℝ) *
      implicitPolynomialConstant (u 0) a τ := by
    exact add_pos_of_pos_of_nonneg
      (Real.rpow_pos_of_pos (hpos 0 (Nat.zero_le k)) _)
      (mul_nonneg (Nat.cast_nonneg _)
        (implicitPolynomialConstant_pos (hpos 0 (Nat.zero_le k)) ha hτ).le)
  have hr := Real.rpow_le_rpow_of_nonpos hb (by linarith :
      u 0 ^ (1 - τ) + (k : ℝ) * implicitPolynomialConstant (u 0) a τ ≤ u k ^ (1 - τ))
    (div_nonpos_of_nonpos_of_nonneg (by norm_num) (by linarith) : -1 / (τ - 1) ≤ 0)
  have he : (1 - τ) * (-1 / (τ - 1)) = 1 := by
    field_simp [ne_of_gt (sub_pos.mpr hτ)]; ring
  rwa [← Real.rpow_mul hk0.le, he, Real.rpow_one] at hr

/-- A ceiling count for polynomial upper decay. -/
noncomputable def polynomialIterationCount (δ τ ε : ℝ) : ℕ :=
  ⌈ε ^ (1 - τ) / δ⌉₊

/-- A reciprocal-power upper bound gives a finite tolerance count of order
`ε ^ (-(τ - 1))`. -/
theorem polynomial_tolerance {u : ℕ → ℝ} {A δ τ ε : ℝ}
    (hA : 0 ≤ A) (hδ : 0 < δ) (hτ : 1 < τ) (hε : 0 < ε)
    (hbound : ∀ k, u k ≤ (A + (k : ℝ) * δ) ^ (-1 / (τ - 1)))
    {k : ℕ} (hk : polynomialIterationCount δ τ ε ≤ k) : u k ≤ ε := by
  have hc : ε ^ (1 - τ) / δ ≤ (k : ℝ) :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr hk)
  have hpow : ε ^ (1 - τ) ≤ A + (k : ℝ) * δ := by
    have := (div_le_iff₀ hδ).mp hc
    linarith
  have hr := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hε _) hpow
    (div_nonpos_of_nonpos_of_nonneg (by norm_num) (by linarith) : -1 / (τ - 1) ≤ 0)
  have he : (1 - τ) * (-1 / (τ - 1)) = 1 := by
    field_simp [ne_of_gt (sub_pos.mpr hτ)]; ring
  rw [← Real.rpow_mul hε.le, he, Real.rpow_one] at hr
  exact (hbound k).trans hr

/-- Explicit polynomial descent reaches every positive tolerance within a power-law budget. -/
theorem explicit_recurrence_polynomial_tolerance {u : ℕ → ℝ} {a τ ε : ℝ}
    (ha : 0 < a) (hτ : 1 < τ) (hε : 0 < ε) (hu : ∀ k, 0 ≤ u k)
    (hstep : ∀ k, u (k + 1) ≤ u k - a * u k ^ τ)
    {k : ℕ} (hk : polynomialIterationCount (a * (τ - 1)) τ ε ≤ k) : u k ≤ ε :=
  polynomial_tolerance (Real.rpow_nonneg (hu 0) _) (mul_pos ha (sub_pos.mpr hτ))
    hτ hε (explicit_recurrence_polynomial_bound ha hτ hu hstep) hk

/-- Implicit polynomial descent reaches every positive tolerance within a power-law budget.
The zero initial-gap case is stated separately to avoid dividing by a vanishing rate constant. -/
theorem implicit_recurrence_polynomial_tolerance {u : ℕ → ℝ} {a τ ε : ℝ}
    (ha : 0 < a) (hτ : 1 < τ) (hε : 0 < ε) (hu : ∀ k, 0 ≤ u k)
    (hstep : ∀ k, u (k + 1) + a * u (k + 1) ^ τ ≤ u k)
    {k : ℕ} (hk : u 0 = 0 ∨
      polynomialIterationCount (implicitPolynomialConstant (u 0) a τ) τ ε ≤ k) :
    u k ≤ ε := by
  rcases hk with hzero | hk
  · have := implicit_recurrence_antitone ha.le hu hstep (Nat.zero_le k)
    rw [hzero] at this
    exact this.trans hε.le
  · by_cases hzero : u 0 = 0
    · have := implicit_recurrence_antitone ha.le hu hstep (Nat.zero_le k)
      rw [hzero] at this
      exact this.trans hε.le
    apply polynomial_tolerance (Real.rpow_nonneg (hu 0) _) _ hτ hε
      (implicit_recurrence_polynomial_bound ha hτ hu hstep) hk
    exact implicitPolynomialConstant_pos (lt_of_le_of_ne (hu 0) (Ne.symm hzero)) ha hτ

/-- Iterating a power contraction gives the superlinear upper envelope. -/
theorem power_contraction_bound {u : ℕ → ℝ} {p q : ℝ}
    (hp : 0 ≤ p) (hu : ∀ k, 0 ≤ u k) (hq : 0 ≤ q) (hstart : u 0 ≤ q)
    (hstep : ∀ k, u (k + 1) ≤ u k ^ p) (k : ℕ) :
    u k ≤ q ^ (p ^ k) := by
  induction k with
  | zero => simpa using hstart
  | succ k ih =>
    calc
      u (k + 1) ≤ u k ^ p := hstep k
      _ ≤ (q ^ (p ^ k)) ^ p := Real.rpow_le_rpow (hu k) ih hp
      _ = q ^ (p ^ (k + 1)) := by rw [← Real.rpow_mul hq, pow_succ]

/-- After entering a scale below one, implicit subunit-power descent has a
superlinear upper envelope. The entry point may be shifted arbitrarily. -/
theorem implicit_recurrence_power_envelope {u : ℕ → ℝ} {a τ B q : ℝ}
    (hτ : 0 < τ) (hB : 0 < B) (hq : 0 ≤ q)
    (hscale : a * B ^ τ = B) (hu : ∀ k, 0 ≤ u k)
    (hstep : ∀ k, u (k + 1) + a * u (k + 1) ^ τ ≤ u k)
    (m : ℕ) (hentry : u m ≤ B * q) (k : ℕ) :
    u (m + k) ≤ B * q ^ ((1 / τ) ^ k) := by
  have hn : ∀ j, 0 ≤ u (m + j) / B := fun j => div_nonneg (hu _) hB.le
  have hs : ∀ j, u (m + (j + 1)) / B ≤ (u (m + j) / B) ^ (1 / τ) := by
    intro j
    have hj := hstep (m + j)
    rw [show m + j + 1 = m + (j + 1) by omega] at hj
    have hid : (u (m + (j + 1)) / B) ^ τ = a * u (m + (j + 1)) ^ τ / B := by
      rw [Real.div_rpow (hu _) hB.le]
      apply (div_eq_div_iff (ne_of_gt (Real.rpow_pos_of_pos hB _)) hB.ne').2
      calc
        _ = u (m + (j + 1)) ^ τ * (a * B ^ τ) := by rw [hscale]
        _ = _ := by ring
    have hr : u (m + (j + 1)) / B + 1 * (u (m + (j + 1)) / B) ^ τ ≤
        u (m + j) / B := by
      rw [one_mul, hid, ← add_div]
      exact (div_le_div_iff_of_pos_right hB).2 hj
    simpa using implicit_recurrence_rpow_step (hn (j + 1))
      (by norm_num : (0 : ℝ) < 1) hτ hr
  have hh := power_contraction_bound (by positivity : 0 ≤ 1 / τ) hn hq
    ((div_le_iff₀ hB).2 (by simpa [mul_comm] using hentry)) hs k
  exact (div_le_iff₀ hB).mp hh |>.trans_eq (mul_comm _ _)

/-- A positive threshold is reached in finitely many implicit steps. This coarse entry
budget is independent of the final tolerance used in a subsequent local rate. -/
theorem implicit_recurrence_entry {u : ℕ → ℝ} {a τ t : ℝ}
    (ha : 0 < a) (hτ : 0 < τ) (ht : 0 < t) (hu : ∀ k, 0 ≤ u k)
    (hstep : ∀ k, u (k + 1) + a * u (k + 1) ^ τ ≤ u k) :
    ∃ m ≤ ⌊u 0 / (a * t ^ τ)⌋₊ + 1, u m ≤ t := by
  have hδ : 0 < a * t ^ τ := mul_pos ha (Real.rpow_pos_of_pos ht _)
  have hdec : ∀ n, (∀ j ≤ n, ¬ u (j + 1) ≤ t) →
      a * t ^ τ ≤ u n - u (n + 1) := by
    intro n hn
    have hnext : t < u (n + 1) := lt_of_not_ge (hn n le_rfl)
    have hp := Real.rpow_le_rpow ht.le hnext.le hτ.le
    have hh := mul_le_mul_of_nonneg_left hp ha.le
    linarith [hstep n]
  obtain ⟨k, hk, hentry, -⟩ := EvaluationComplexity.exists_first_of_decrease
    (P := fun k => u (k + 1) ≤ t) hδ hu hdec
  exact ⟨k + 1, by simpa using Nat.add_le_add_right hk 1, hentry⟩

/-- A logarithm-of-logarithm tolerance count for a superlinear upper envelope. -/
noncomputable def superlinearIterationCount (B q p ε : ℝ) : ℕ :=
  geometricIterationCount (Real.log (B / ε)) p (-Real.log q)

/-- The double-power upper envelope reaches a positive tolerance within the explicit
logarithm-of-logarithm count, with a zero-count branch for large tolerances. -/
theorem superlinear_tolerance {u : ℕ → ℝ} {B q p ε : ℝ}
    (hB : 0 < B) (hq0 : 0 < q) (hq1 : q < 1) (hp : 1 < p) (hε : 0 < ε)
    (hbound : ∀ k, u k ≤ B * q ^ (p ^ k)) {k : ℕ}
    (hk : superlinearIterationCount B q p ε ≤ k) : u k ≤ ε := by
  have hlogq : 0 < -Real.log q := neg_pos.mpr (Real.log_neg hq0 hq1)
  have hh := geometric_tolerance hp hlogq (u := fun j => Real.log (B / ε) / p ^ j)
    (fun _ => le_rfl) hk
  have hpower : 0 < p ^ k := pow_pos (by linarith) _
  have hlog := (div_le_iff₀ hpower).mp hh
  have htarget : Real.log (B * q ^ (p ^ k)) ≤ Real.log ε := by
    rw [Real.log_mul hB.ne' (Real.rpow_pos_of_pos hq0 _).ne', Real.log_rpow hq0,
      Real.log_div hB.ne' hε.ne'] at *
    nlinarith
  exact (hbound k).trans ((Real.log_le_log_iff (mul_pos hB
    (Real.rpow_pos_of_pos hq0 _)) hε).mp htarget)

/-- Implicit subunit-power descent enters a fixed scale in a finite number of steps,
then admits a superlinear envelope and a logarithm-of-logarithm tolerance budget. -/
theorem implicit_recurrence_superlinear_bound {u : ℕ → ℝ} {a τ : ℝ}
    (ha : 0 < a) (hτ0 : 0 < τ) (hτ1 : τ < 1) (hu : ∀ k, 0 ≤ u k)
    (hstep : ∀ k, u (k + 1) + a * u (k + 1) ^ τ ≤ u k) :
    let B := a ^ (1 / (1 - τ))
    ∃ m ≤ ⌊u 0 / (a * (B / 2) ^ τ)⌋₊ + 1,
      (∀ k, u (m + k) ≤ B * (1 / 2 : ℝ) ^ ((1 / τ) ^ k)) ∧
      (∀ ε > 0, ∀ k, superlinearIterationCount B (1 / 2) (1 / τ) ε ≤ k →
        u (m + k) ≤ ε) := by
  dsimp only
  let B := a ^ (1 / (1 - τ))
  have hB : 0 < B := Real.rpow_pos_of_pos ha _
  have hscale : a * B ^ τ = B := by
    dsimp [B]
    rw [← Real.rpow_mul ha.le]
    conv_lhs => lhs; rw [← Real.rpow_one a]
    rw [← Real.rpow_add ha]
    congr 1
    field_simp [ne_of_gt (sub_pos.mpr hτ1)]
    ring
  obtain ⟨m, hm, hentry⟩ := implicit_recurrence_entry ha hτ0 (by positivity : 0 < B / 2)
    hu hstep
  have henv := implicit_recurrence_power_envelope hτ0 hB
    (by norm_num : (0 : ℝ) ≤ 1 / 2) hscale hu hstep m (by simpa [div_eq_mul_inv] using hentry)
  refine ⟨m, hm, henv, ?_⟩
  intro ε hε k hk
  exact superlinear_tolerance hB (by norm_num) (by norm_num)
    ((one_lt_div hτ0).2 hτ1) hε henv hk

/-- A positive entry of a superunit explicit recurrence is at most its feasibility threshold. -/
theorem explicit_recurrence_positive_gap_upper_bound {u : ℕ → ℝ} {a τ : ℝ}
    (ha : 0 < a) (hτ : 1 < τ) (hu : ∀ k, 0 ≤ u k)
    (hstep : ∀ k, u (k + 1) ≤ u k - a * u k ^ τ)
    {k : ℕ} (hk : 0 < u k) : u k ≤ a ^ (1 / (1 - τ)) := by
  have hpower : a ≤ u k ^ (1 - τ) := by
    rw [Real.rpow_sub hk, Real.rpow_one]
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hk τ)).2
    linarith [hstep k, hu (k + 1)]
  have hh := Real.rpow_le_rpow_of_nonpos ha hpower
    (div_nonpos_of_nonneg_of_nonpos zero_le_one (by linarith) : 1 / (1 - τ) ≤ 0)
  have he : (1 - τ) * (1 / (1 - τ)) = 1 := by
    field_simp [ne_of_lt (sub_neg.mpr hτ)]
  rwa [← Real.rpow_mul hk.le, he, Real.rpow_one] at hh

/-- At the feasibility threshold, the next gap of explicit descent is exactly zero. -/
theorem explicit_recurrence_threshold_zero {u : ℕ → ℝ} {a τ : ℝ}
    (ha : 0 < a) (hτ : τ ≠ 1) (hu : ∀ k, 0 ≤ u k)
    (hstep : ∀ k, u (k + 1) ≤ u k - a * u k ^ τ)
    {k : ℕ} (hk : u k = a ^ (1 / (1 - τ))) : u (k + 1) = 0 := by
  have hid : a * (a ^ (1 / (1 - τ))) ^ τ = a ^ (1 / (1 - τ)) := by
    rw [← Real.rpow_mul ha.le]
    conv_lhs => lhs; rw [← Real.rpow_one a]
    rw [← Real.rpow_add ha]
    congr 1
    field_simp [sub_ne_zero.mpr (Ne.symm hτ)]
    ring
  have hh := hstep k
  rw [hk, hid, sub_self] at hh
  exact le_antisymm hh (hu (k + 1))

/-- The three upper-rate regimes of implicit scalar descent, allowing faster decay and zeros. -/
structure ImplicitRateBounds (u : ℕ → ℝ) (a τ : ℝ) : Prop where
  subunit : τ < 1 →
    ∃ m ≤ ⌊u 0 / (a * (a ^ (1 / (1 - τ)) / 2) ^ τ)⌋₊ + 1,
      ∀ k, u (m + k) ≤ a ^ (1 / (1 - τ)) * (1 / 2 : ℝ) ^ ((1 / τ) ^ k)
  linear : τ = 1 → ∀ k, u k ≤ u 0 * (1 + a) ^ (-(k : ℝ))
  polynomial : 1 < τ → ∀ k, u k ≤ (u 0 ^ (1 - τ) + (k : ℝ) *
    implicitPolynomialConstant (u 0) a τ) ^ (-1 / (τ - 1))

/-- Nonnegative implicit descent has all three upper-rate regimes. -/
theorem implicit_recurrence_rate_bounds {u : ℕ → ℝ} {a τ : ℝ}
    (ha : 0 < a) (hτ : 0 < τ) (hu : ∀ k, 0 ≤ u k)
    (hstep : ∀ k, u (k + 1) + a * u (k + 1) ^ τ ≤ u k) :
    ImplicitRateBounds u a τ := by
  refine ⟨?_, ?_, fun ht => implicit_recurrence_polynomial_bound ha ht hu hstep⟩
  · intro ht
    obtain ⟨m, hm, henv, -⟩ := implicit_recurrence_superlinear_bound ha hτ ht hu hstep
    exact ⟨m, hm, henv⟩
  · intro ht
    subst τ
    exact implicit_recurrence_linear_bound ha (by simpa only [Real.rpow_one] using hstep)

/-- Upper-rate regimes and feasibility thresholds for explicit scalar descent. -/
structure ExplicitRateBounds (u : ℕ → ℝ) (a τ : ℝ) : Prop where
  linear : τ = 1 → (0 < u 0 → a ≤ 1) ∧
    (a = 1 → u 1 = 0) ∧ (a < 1 → ∀ k, u k ≤ u 0 * (1 - a) ^ k)
  subunit : τ < 1 → (0 < u 0 → a ^ (1 / (1 - τ)) ≤ u 0) ∧
    (u 0 = a ^ (1 / (1 - τ)) → u 1 = 0) ∧
    ∀ k, ⌊u 0 / a ^ (1 / (1 - τ))⌋₊ + 1 ≤ k → u k = 0
  polynomial : 1 < τ → (0 < u 0 → u 0 ≤ a ^ (1 / (1 - τ))) ∧
    (u 0 = a ^ (1 / (1 - τ)) → u 1 = 0) ∧
    ∀ k, u k ≤ (u 0 ^ (1 - τ) + (k : ℝ) * (a * (τ - 1))) ^ (-1 / (τ - 1))
  positive_subunit : τ < 1 → ∀ k, 0 < u k → a ^ (1 / (1 - τ)) ≤ u k

/-- Explicit descent has the three rates, the initial-gap feasibility thresholds,
and exact termination after a threshold equality. -/
theorem explicit_recurrence_rate_bounds {u : ℕ → ℝ} {a τ : ℝ}
    (ha : 0 < a) (hτ : 0 < τ) (hu : ∀ k, 0 ≤ u k)
    (hstep : ∀ k, u (k + 1) ≤ u k - a * u k ^ τ) :
    ExplicitRateBounds u a τ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ht
    subst τ
    have hs : ∀ k, u (k + 1) ≤ u k - a * u k := by
      simpa only [Real.rpow_one] using hstep
    refine ⟨?_, ?_, fun ht => explicit_recurrence_linear_bound_of_lt_one ht hs⟩
    · intro hpos
      by_contra hh
      have hz := explicit_recurrence_eq_zero_of_one_lt (lt_of_not_ge hh) hu hs 0
      linarith
    · intro he
      exact explicit_recurrence_eq_zero_of_one_le he.ge hu hs 0
  · intro ht
    exact ⟨fun hpos => explicit_recurrence_positive_gap_lower_bound ha ht hu hstep hpos,
      fun he => explicit_recurrence_threshold_zero ha ht.ne hu hstep he,
      explicit_recurrence_finite_termination ha hτ ht hu hstep⟩
  · intro ht
    exact ⟨fun hpos => explicit_recurrence_positive_gap_upper_bound ha ht hu hstep hpos,
      fun he => explicit_recurrence_threshold_zero ha ht.ne' hu hstep he,
      explicit_recurrence_polynomial_bound ha ht hu hstep⟩
  · intro ht k hk
    exact explicit_recurrence_positive_gap_lower_bound ha ht hu hstep hk

end Optimization.MeasureDomination
