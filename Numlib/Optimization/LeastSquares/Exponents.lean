import Numlib.Optimization.LeastSquares.Cascading
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Good cascading residual exponents

Order comparison, exact logarithmic thresholds and positive odd factorizations
give all six residual-power choices. The geometric identity handles the
positive even two-adic valuation in the third-order zero-exponent case.
-/

namespace LeastSquares
/-- Higher enabled orders have smaller residual exponents when the residual
power is at least one. -/
theorem cascadingExponent_antitone {p i j k : ℕ} {ℓ : ℝ}
    (hℓ : 1 ≤ ℓ) (hjk : j ≤ k) (hkp : k ≤ p) :
    cascadingExponent p ℓ i k ≤ cascadingExponent p ℓ i j := by
  have hjp : j ≤ p := hjk.trans hkp
  have hMj : (0 : ℝ) < (p + 1 - j : ℕ) := by exact_mod_cast (show 0 < p + 1 - j by omega)
  have hMk : (0 : ℝ) < (p + 1 - k : ℕ) := by exact_mod_cast (show 0 < p + 1 - k by omega)
  have hjcast : ((p + 1 - j : ℕ) : ℝ) = (p : ℝ) + 1 - j := by
    rw [Nat.cast_sub (by omega)]; push_cast; rfl
  have hkcast : ((p + 1 - k : ℕ) : ℝ) = (p : ℝ) + 1 - k := by
    rw [Nat.cast_sub (by omega)]; push_cast; rfl
  have hjkR : (j : ℝ) ≤ k := by exact_mod_cast hjk
  have hratio : (j : ℝ) / (p + 1 - j : ℕ) ≤ (k : ℝ) / (p + 1 - k : ℕ) := by
    apply (div_le_div_iff₀ hMj hMk).mpr
    rw [hjcast, hkcast]
    nlinarith [show (0 : ℝ) ≤ p by positivity]
  unfold cascadingExponent
  have hh := mul_le_mul_of_nonneg_right hratio (sub_nonneg.mpr hℓ)
  simpa only [div_mul_eq_mul_div, mul_comm (ℓ - 1)] using sub_le_sub_left hh _

/-- The exponent for `ℓ=p/j` is a difference of reciprocal positive integers. -/
theorem cascadingExponent_div_order {p i j : ℕ} (hj : 0 < j) (hjp : j ≤ p) :
    cascadingExponent p ((p : ℝ) / j) i j =
      1 / (p + 1 - j : ℕ) - 1 / (2 : ℝ) ^ i := by
  have hMj : (0 : ℝ) < (p + 1 - j : ℕ) := by exact_mod_cast (show 0 < p + 1 - j by omega)
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj
  have hjcast : ((p + 1 - j : ℕ) : ℝ) = (p : ℝ) + 1 - j := by
    rw [Nat.cast_sub (by omega)]; push_cast; rfl
  unfold cascadingExponent
  rw [hjcast]
  field_simp [show (p : ℝ) + 1 - j ≠ 0 by rw [← hjcast]; exact hMj.ne']
  ring

/-- The exact logarithmic threshold gives positive exponents at and below the target order. -/
theorem cascadingExponent_pos_of_log {p i j : ℕ} (hj : 0 < j) (hjp : j ≤ p)
    (hi : Real.logb 2 (p + 1 - j : ℕ) < i) :
    0 < cascadingExponent p ((p : ℝ) / j) i j := by
  have hMj : (0 : ℝ) < (p + 1 - j : ℕ) := by exact_mod_cast (show 0 < p + 1 - j by omega)
  have ht := (Real.logb_lt_iff_lt_rpow (by norm_num : (1 : ℝ) < 2) hMj).mp hi
  rw [Real.rpow_natCast] at ht
  rw [cascadingExponent_div_order hj hjp]
  exact sub_pos.mpr (one_div_lt_one_div_of_lt hMj ht)

/-- Positive residual powers give strict order separation between first and higher exponents. -/
theorem cascadingExponent_strictAntitone {p i j k : ℕ} {ℓ : ℝ}
    (hℓ : 1 < ℓ) (hjk : j < k) (hkp : k ≤ p) :
    cascadingExponent p ℓ i k < cascadingExponent p ℓ i j := by
  have hjp : j ≤ p := hjk.le.trans hkp
  have hMj : (0 : ℝ) < (p + 1 - j : ℕ) := by exact_mod_cast (show 0 < p + 1 - j by omega)
  have hMk : (0 : ℝ) < (p + 1 - k : ℕ) := by exact_mod_cast (show 0 < p + 1 - k by omega)
  have hjcast : ((p + 1 - j : ℕ) : ℝ) = (p : ℝ) + 1 - j := by
    rw [Nat.cast_sub (by omega)]; push_cast; rfl
  have hkcast : ((p + 1 - k : ℕ) : ℝ) = (p : ℝ) + 1 - k := by
    rw [Nat.cast_sub (by omega)]; push_cast; rfl
  have hjkR : (j : ℝ) < k := by exact_mod_cast hjk
  have hratio : (j : ℝ) / (p + 1 - j : ℕ) < (k : ℝ) / (p + 1 - k : ℕ) := by
    apply (div_lt_div_iff₀ hMj hMk).mpr
    rw [hjcast, hkcast]
    nlinarith [show (0 : ℝ) ≤ p by positivity]
  unfold cascadingExponent
  have hh := mul_lt_mul_of_pos_right hratio (sub_pos.mpr hℓ)
  simpa only [div_mul_eq_mul_div, mul_comm (ℓ - 1)] using sub_lt_sub_left hh _

/-- The exact zero-exponent residual power for each enabled order. -/
theorem cascadingExponent_zero {p i j : ℕ} (hj : 0 < j) (hjp : j ≤ p) :
    cascadingExponent p (1 + ((p + 1 - j : ℕ) : ℝ) / j *
      (1 - 1 / (2 : ℝ) ^ i)) i j = 0 := by
  have hMj : (0 : ℝ) < (p + 1 - j : ℕ) := by exact_mod_cast (show 0 < p + 1 - j by omega)
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj
  unfold cascadingExponent
  field_simp
  ring

/-- An exact positive factorization supplies both a zero exponent and a power above one. -/
theorem cascadingExponent_zero_of_factorization {p i j : ℕ} {c : ℝ}
    (hj : 0 < j) (hjp : j ≤ p) (hi : 0 < i) (hc : 0 < c)
    (hfac : ((p + 1 - j : ℕ) : ℝ) = (j : ℝ) * c * (2 : ℝ) ^ i) :
    cascadingExponent p (1 + c * ((2 : ℝ) ^ i - 1)) i j = 0 ∧
      1 < 1 + c * ((2 : ℝ) ^ i - 1) := by
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj
  have htwo : 0 < (2 : ℝ) ^ i := by positivity
  have htwo1 : (1 : ℝ) < (2 : ℝ) ^ i := one_lt_pow₀ (by norm_num) hi.ne'
  have heq : 1 + c * ((2 : ℝ) ^ i - 1) =
      1 + ((p + 1 - j : ℕ) : ℝ) / j * (1 - 1 / (2 : ℝ) ^ i) := by
    rw [hfac]
    field_simp
  refine ⟨?_, by nlinarith [mul_pos hc (sub_pos.mpr htwo1)]⟩
  rw [heq]
  exact cascadingExponent_zero hj hjp

/-- The even geometric sum in (5.1.43) is one third of the corresponding power minus one. -/
theorem three_mul_even_geometric_sum (j : ℕ) :
    3 * (∑ k ∈ Finset.range j, (2 : ℝ) ^ (2 * k)) = (2 : ℝ) ^ (2 * j) - 1 := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    rw [Nat.mul_succ, pow_add]
    norm_num
    ring
end LeastSquares

namespace LeastSquares
/-- All six residual-exponent choices of Lemma 5.1.6. Odd factors and the
positive even valuation in the zero cases are explicit. -/
theorem cascadingExponent_choices {p : ℕ} (hp : 0 < p) :
    (∀ i : ℕ, Real.logb 2 (p : ℝ) < i →
      0 < LeastSquares.cascadingExponent p p i 1) ∧
    (∀ o i : ℕ, Odd o → Even p → p = o * 2 ^ i →
      LeastSquares.cascadingExponent p (1 + (o : ℝ) * ((2 : ℝ)^i - 1)) i 1 = 0 ∧
        1 < 1 + (o : ℝ) * ((2 : ℝ)^i - 1)) ∧
    (∀ i : ℕ, Even p → Real.logb 2 (p - 1 : ℕ) < i →
      0 < LeastSquares.cascadingExponent p ((p : ℝ) / 2) i 1 ∧
      0 < LeastSquares.cascadingExponent p ((p : ℝ) / 2) i 2) ∧
    (∀ o i : ℕ, Odd o → 4 ∣ p - 1 → p - 1 = o * 2 ^ (i + 1) →
      LeastSquares.cascadingExponent p (1 + (o : ℝ) * ((2 : ℝ)^i - 1)) i 2 = 0 ∧
      0 < LeastSquares.cascadingExponent p (1 + (o : ℝ) * ((2 : ℝ)^i - 1)) i 1 ∧
      1 < 1 + (o : ℝ) * ((2 : ℝ)^i - 1)) ∧
    (∀ i : ℕ, 3 ∣ p → Real.logb 2 (p - 2 : ℕ) < i →
      0 < LeastSquares.cascadingExponent p ((p : ℝ) / 3) i 1 ∧
      0 < LeastSquares.cascadingExponent p ((p : ℝ) / 3) i 2 ∧
      0 < LeastSquares.cascadingExponent p ((p : ℝ) / 3) i 3) ∧
    (∀ o i : ℕ, Odd o → 0 < i → Even i → p - 2 = o * 2 ^ i →
      let ℓ := 1 + (o : ℝ) * ∑ k ∈ Finset.range (i / 2), (2 : ℝ)^(2 * k)
      LeastSquares.cascadingExponent p ℓ i 3 = 0 ∧
      0 < LeastSquares.cascadingExponent p ℓ i 1 ∧
      0 < LeastSquares.cascadingExponent p ℓ i 2 ∧ 1 < ℓ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    simpa only [Nat.add_sub_cancel, Nat.cast_one, div_one] using
      LeastSquares.cascadingExponent_pos_of_log (j := 1) (by omega) hp
        (by simpa only [Nat.add_sub_cancel] using hi)
  · intro o i ho heven hfac
    have hi : 0 < i := by
      by_contra hh
      have hi0 : i = 0 := by omega
      have hpo : p = o := by simpa only [hi0, pow_zero, mul_one] using hfac
      have h₁ := Nat.even_iff.mp heven
      have h₂ := Nat.odd_iff.mp ho
      omega
    have hoR : (0 : ℝ) < o := by exact_mod_cast ho.pos
    apply LeastSquares.cascadingExponent_zero_of_factorization (j := 1)
      (by omega) hp hi hoR
    simpa only [Nat.add_sub_cancel, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
      Nat.cast_one, one_mul] using congrArg (fun a : ℕ => (a : ℝ)) hfac
  · intro i heven hi
    have hp2 : 2 ≤ p := by
      have h := Nat.even_iff.mp heven
      omega
    have ht : 0 < LeastSquares.cascadingExponent p ((p : ℝ) / 2) i 2 :=
      LeastSquares.cascadingExponent_pos_of_log (j := 2) (by omega) hp2
        (by simpa only [show p + 1 - 2 = p - 1 by omega] using hi)
    have hℓ : 1 ≤ (p : ℝ) / 2 := by
      have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp2
      linarith
    exact ⟨ht.trans_le (LeastSquares.cascadingExponent_antitone hℓ (by decide) hp2), ht⟩
  · intro o i ho hdiv hfac
    have hoR : (0 : ℝ) < o := by exact_mod_cast ho.pos
    have hi : 0 < i := by
      by_contra hh
      have hi0 : i = 0 := by omega
      have hf : p - 1 = o * 2 := by simpa [hi0] using hfac
      obtain ⟨w, hw⟩ := hdiv
      have hodd := Nat.odd_iff.mp ho
      omega
    have hp2 : 2 ≤ p := by
      have hpos := Nat.mul_pos ho.pos (pow_pos (by decide : 0 < (2 : ℕ)) (i + 1))
      omega
    have hz := LeastSquares.cascadingExponent_zero_of_factorization (p := p) (i := i)
      (j := 2) (c := (o : ℝ)) (by decide) hp2 hi hoR (by
        have hf := congrArg (fun a : ℕ => (a : ℝ)) hfac
        simp only [Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_mul, Nat.cast_pow,
          Nat.cast_ofNat, Nat.cast_one] at hf
        rw [show p + 1 - 2 = p - 1 by omega, Nat.cast_sub (by omega)]
        push_cast
        rw [pow_succ] at hf
        nlinarith)
    refine ⟨hz.1, ?_, hz.2⟩
    have ht := LeastSquares.cascadingExponent_strictAntitone (p := p) (i := i)
      (j := 1) (k := 2) hz.2 (by decide) hp2
    rwa [hz.1] at ht
  · intro i hdiv hi
    have hp3 : 3 ≤ p := Nat.le_of_dvd hp hdiv
    have ht : 0 < LeastSquares.cascadingExponent p ((p : ℝ) / 3) i 3 :=
      LeastSquares.cascadingExponent_pos_of_log (j := 3) (by omega) hp3
        (by simpa only [show p + 1 - 3 = p - 2 by omega] using hi)
    have hℓ : 1 ≤ (p : ℝ) / 3 := by
      have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp3
      linarith
    exact ⟨ht.trans_le (LeastSquares.cascadingExponent_antitone hℓ (by decide) hp3),
      ht.trans_le (LeastSquares.cascadingExponent_antitone hℓ (by decide) hp3), ht⟩
  · intro o i ho hi heven hfac
    obtain ⟨j, hj⟩ := heven
    have hij : i = 2 * j := by omega
    clear hj
    subst i
    have hjpos : 0 < j := by omega
    have hp3 : 3 ≤ p := by
      have hpos := Nat.mul_pos ho.pos (pow_pos (by decide : 0 < (2 : ℕ)) (2 * j))
      omega
    have hoR : (0 : ℝ) < (o : ℝ) / 3 := div_pos (by exact_mod_cast ho.pos) (by norm_num)
    have hz := LeastSquares.cascadingExponent_zero_of_factorization (p := p) (i := 2 * j)
      (j := 3) (c := (o : ℝ) / 3) (by decide) hp3 (by omega) hoR (by
        have hf := congrArg (fun a : ℕ => (a : ℝ)) hfac
        simpa only [show p + 1 - 3 = p - 2 by omega, Nat.cast_mul, Nat.cast_pow,
          Nat.cast_ofNat, mul_div_cancel₀ _ (by norm_num : (3 : ℝ) ≠ 0)] using hf)
    have hsum := LeastSquares.three_mul_even_geometric_sum j
    have heq : 1 + (o : ℝ) * (∑ k ∈ Finset.range j, (2 : ℝ) ^ (2 * k)) =
        1 + ((o : ℝ) / 3) * ((2 : ℝ) ^ (2 * j) - 1) := by nlinarith
    simp only [Nat.mul_div_cancel_left _ (by decide : 0 < (2 : ℕ))]
    rw [heq]
    refine ⟨hz.1, ?_, ?_, hz.2⟩
    · have ht := LeastSquares.cascadingExponent_strictAntitone (p := p) (i := 2 * j)
        (j := 1) (k := 3) hz.2 (by decide) hp3
      rwa [hz.1] at ht
    · have ht := LeastSquares.cascadingExponent_strictAntitone (p := p) (i := 2 * j)
        (j := 2) (k := 3) hz.2 (by decide) hp3
      rwa [hz.1] at ht
end LeastSquares
