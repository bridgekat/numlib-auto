import Numlib.Optimization.TransverseTailWindow

/-!
# Dyadic lower lengths for transverse tails

A fixed natural-power family of tolerances gives an available tail length growing faster
than every fixed multiple of the three-halves rate. These are analytic length estimates;
operational oracle counts require an actual execution containing the prescribed trials.
-/

noncomputable section
namespace Optimization.TransverseDyadicRates
open TransverseObjective TransversePrelude TransverseTailWindow

/-- The natural-power tolerance family, equal to two to the power minus six times the index. -/
def epsilon (m : ℕ) : ℝ := ((2 : ℝ) ^ (6 * m))⁻¹

/-- Every member of the natural-power tolerance family is strictly positive. -/
theorem epsilon_pos (m : ℕ) : 0 < epsilon m := by unfold epsilon; positivity

/-- From index three onward the tolerances lie in the required small range. -/
theorem epsilon_le {m : ℕ} (hm : 3 ≤ m) : epsilon m ≤ 1 / 65536 := by
  have hp : (65536 : ℝ) ≤ (2 : ℝ) ^ (6 * m) := by
    calc
      (65536 : ℝ) = 2 ^ (16 : ℕ) := by norm_num
      _ ≤ 2 ^ (6 * m) := pow_le_pow_right₀ (by norm_num) (by omega)
  simpa [epsilon, one_div] using inv_anti₀ (by norm_num : (0 : ℝ) < 65536) hp

/-- The natural-power formula agrees with the usual negative real-power notation. -/
theorem epsilon_eq_rpow (m : ℕ) : epsilon m = (2 : ℝ) ^ (-6 * (m : ℝ)) := by
  rw [show -6 * (m : ℝ) = -((6 * m : ℕ) : ℝ) by push_cast; ring,
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
  rfl

/-- The tail slope at the comparison natural power is exactly half the tolerance. -/
theorem slope_pow (m : ℕ) :
    TransversePrelude.slope ((2 : ℝ) ^ (4 * m)) = epsilon m / 2 := by
  rw [slope_eq (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))]
  have he : ((2 : ℝ) ^ (4 * m)) ^ (-(3 / 2 : ℝ)) = epsilon m := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    rw [epsilon_eq_rpow]
    congr 1
    push_cast
    ring
  rw [he]
  ring

/-- The actual first crossing lies strictly beyond the comparison natural power. -/
theorem pow_lt_crossing (m : ℕ) :
    (2 : ℝ) ^ (4 * m) < ordinate (crossingIndex (epsilon m) (epsilon_pos m)) := by
  by_contra hn
  have hm := antitoneOn_slope (one_le_ordinate _)
    (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)) (le_of_not_gt hn)
  rw [slope_pow] at hm
  have hc := slope_crossingIndex_le (epsilon_pos m)
  linarith [epsilon_pos m]

/-- The injection endpoint also lies strictly beyond the comparison natural power. -/
theorem pow_lt_injectionOrdinate (m : ℕ) :
    (2 : ℝ) ^ (4 * m) < injectionOrdinate (epsilon m) (epsilon_pos m) := by
  unfold injectionOrdinate
  linarith [pow_lt_crossing m, epsilon_pos m]

/-- The unfloored half length dominates the tenth-power scale. -/
theorem lower_length (m : ℕ) :
    (2 : ℝ) ^ (10 * m) / 16 <
      injectionOrdinate (epsilon m) (epsilon_pos m) / (16 * epsilon m) := by
  have he : (2 : ℝ) ^ (10 * m) * epsilon m = (2 : ℝ) ^ (4 * m) := by
    rw [epsilon, show 10 * m = 4 * m + 6 * m by omega, pow_add]
    field_simp
  apply (lt_div_iff₀ (show 0 < 16 * epsilon m by positivity [epsilon_pos m])).mpr
  nlinarith [pow_lt_injectionOrdinate m]

/-- The actual available integer tail length exceeds the tenth-power scale. -/
theorem tailCount_lower {m : ℕ} (hm : 3 ≤ m) :
    (2 : ℝ) ^ (10 * m) / 16 <
      (TransverseTailWindow.tailCount (epsilon m) (epsilon_pos m) : ℝ) :=
  (lower_length m).trans_le
    (TransverseTailWindow.tailCount_lower (epsilon_pos m) (epsilon_le hm))

/-- The proposed three-halves scale is the ninth natural-power scale in this family. -/
theorem epsilon_rate (m : ℕ) :
    epsilon m ^ (-(3 / 2 : ℝ)) = (2 : ℝ) ^ (9 * m) := by
  rw [epsilon_eq_rpow, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    ← Real.rpow_natCast]
  congr 1
  push_cast
  ring

/-- Every fixed multiple and additive correction to the ninth-power rate is eventually
smaller than the tenth-power lower length. The chosen index can exceed any lower limit. -/
theorem exists_pow_lower_gt (A C : ℝ) (M : ℕ) : ∃ m : ℕ, M ≤ m ∧
    A * (2 : ℝ) ^ (9 * m) + C < (2 : ℝ) ^ (10 * m) / 16 := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (16 * (|A| + |C| + 1))
    (by norm_num : (1 : ℝ) < 2)
  let m := max M n
  have hnm : n ≤ m := le_max_right _ _
  have hm : 16 * (|A| + |C| + 1) < (2 : ℝ) ^ m :=
    hn.trans_le (pow_le_pow_right₀ (by norm_num) hnm)
  have hp : 1 ≤ (2 : ℝ) ^ (9 * m) := one_le_pow₀ (by norm_num)
  have hc : C ≤ |C| * (2 : ℝ) ^ (9 * m) := by
    calc
      C ≤ |C| := le_abs_self C
      _ ≤ |C| * (2 : ℝ) ^ (9 * m) := by nlinarith [abs_nonneg C]
  have ha := mul_le_mul_of_nonneg_right (le_abs_self A)
    (show 0 ≤ (2 : ℝ) ^ (9 * m) by positivity)
  have hf : |A| + |C| < (2 : ℝ) ^ m / 16 := by linarith
  refine ⟨m, le_max_left _ _, ?_⟩
  calc
    A * (2 : ℝ) ^ (9 * m) + C ≤ (|A| + |C|) * (2 : ℝ) ^ (9 * m) := by
      nlinarith
    _ < ((2 : ℝ) ^ m / 16) * (2 : ℝ) ^ (9 * m) :=
      mul_lt_mul_of_pos_right hf (by positivity)
    _ = (2 : ℝ) ^ (10 * m) / 16 := by
      rw [show 10 * m = m + 9 * m by omega, pow_add]
      ring

/-- The available integer tail length exceeds every fixed proposed three-halves rate. -/
theorem exists_tailCount_gt (A C : ℝ) (M : ℕ) : ∃ m : ℕ, max 3 M ≤ m ∧
    A * epsilon m ^ (-(3 / 2 : ℝ)) + C <
      (TransverseTailWindow.tailCount (epsilon m) (epsilon_pos m) : ℝ) := by
  obtain ⟨m, hm, hrate⟩ := exists_pow_lower_gt A C (max 3 M)
  refine ⟨m, hm, ?_⟩
  rw [epsilon_rate]
  exact hrate.trans (tailCount_lower ((le_max_left _ _).trans hm))

/-- A linear index correction is also dominated by the ninth-power scale. -/
theorem linear_le_rate (E : ℝ) (m : ℕ) :
    E * (m : ℝ) ≤ |E| * (2 : ℝ) ^ (9 * m) := by
  have hm : (m : ℝ) ≤ (2 : ℝ) ^ m := by
    simpa only [show (2 : ℝ) - 1 = 1 by norm_num, div_one] using
      m.cast_le_pow_div_sub (by norm_num : (1 : ℝ) < 2)
  have hp : (2 : ℝ) ^ m ≤ (2 : ℝ) ^ (9 * m) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  calc
    E * (m : ℝ) ≤ |E| * (m : ℝ) :=
      mul_le_mul_of_nonneg_right (le_abs_self E) (by positivity)
    _ ≤ |E| * (2 : ℝ) ^ (9 * m) :=
      mul_le_mul_of_nonneg_left (hm.trans hp) (abs_nonneg E)

/-- Every fixed rate with a linear index correction is exceeded by an available tail. -/
theorem exists_tailCount_gt_linear (A E F : ℝ) (M : ℕ) : ∃ m : ℕ, max 3 M ≤ m ∧
    A * epsilon m ^ (-(3 / 2 : ℝ)) + E * (m : ℝ) + F <
      (TransverseTailWindow.tailCount (epsilon m) (epsilon_pos m) : ℝ) := by
  obtain ⟨m, hm, hrate⟩ := exists_tailCount_gt (A + |E|) F M
  refine ⟨m, hm, ?_⟩
  rw [epsilon_rate] at hrate ⊢
  have hl := linear_le_rate E m
  nlinarith

/-- The absolute logarithm of the tolerance is exactly linear in the family index. -/
theorem abs_log_epsilon (m : ℕ) : |Real.log (epsilon m)| = 6 * (m : ℝ) * Real.log 2 := by
  rw [epsilon, Real.log_inv, Real.log_pow, abs_neg,
    abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num)))]
  push_cast
  ring

/-- The available integer tail length exceeds every fixed proposed rate with an
additional absolute-logarithmic correction. -/
theorem exists_tailCount_gt_log (A E F : ℝ) (M : ℕ) : ∃ m : ℕ, max 3 M ≤ m ∧
    A * epsilon m ^ (-(3 / 2 : ℝ)) + E * |Real.log (epsilon m)| + F <
      (TransverseTailWindow.tailCount (epsilon m) (epsilon_pos m) : ℝ) := by
  obtain ⟨m, hm, hrate⟩ := exists_tailCount_gt_linear A (E * (6 * Real.log 2)) F M
  refine ⟨m, hm, ?_⟩
  rw [abs_log_epsilon]
  convert hrate using 1
  ring

end Optimization.TransverseDyadicRates
