import Numlib.Analysis.FlatGaussian
import Numlib.Analysis.Polynomial.GaussianBounds
import Mathlib.RingTheory.Polynomial.Hermite.Gaussian

/-!
# Uniform derivative bounds for the flat Gaussian cutoff

The coefficient sum uses the existing finite-support polynomial representation.
The cutoff derivative polynomials have degree at most three times the order and
coefficient sum at most `3 ^ n * n!`. These bounds hold simultaneously for every order.
-/

noncomputable section
open Polynomial Real Finset

namespace Analysis.FlatGaussian

/-- The polynomial in the order-`n` cutoff derivative has degree at most `3n`. -/
theorem natDegree_cutoffPolynomial_le (n : ℕ) : (cutoffPolynomial n).natDegree ≤ 3 * n := by
  induction n with
  | zero => simp [cutoffPolynomial]
  | succ n ih =>
    rw [cutoffPolynomial]
    apply (natDegree_sub_le _ _).trans
    apply max_le
    · have h := (natDegree_mul_le (p := (2 * X ^ 3 : ℝ[X])) (q := cutoffPolynomial n))
      have h₂ : (2 * X ^ 3 : ℝ[X]).natDegree ≤ 3 := by compute_degree!
      omega
    · have h := (natDegree_mul_le (p := (X ^ 2 : ℝ[X])) (q := (cutoffPolynomial n).derivative))
      have h₂ : (X ^ 2 : ℝ[X]).natDegree = 2 := by simp
      have h₃ := natDegree_derivative_le (cutoffPolynomial n)
      omega

/-- The cutoff derivative polynomials have a factorial coefficient-sum bound. -/
theorem coeffNorm_cutoffPolynomial_le (n : ℕ) :
    (cutoffPolynomial n).coeffNorm ≤ (3 : ℝ) ^ n * n.factorial := by
  induction n with
  | zero => simp [cutoffPolynomial]
  | succ n ih =>
    calc
      _ ≤ (2 * X ^ 3 * cutoffPolynomial n).coeffNorm +
          (X ^ 2 * (cutoffPolynomial n).derivative).coeffNorm := coeffNorm_sub_le _ _
      _ = 2 * (cutoffPolynomial n).coeffNorm + (cutoffPolynomial n).derivative.coeffNorm := by
        rw [mul_assoc, show (2 : ℝ[X]) = C (2 : ℝ) by exact (map_ofNat C 2).symm, coeffNorm_C_mul]
        simp
      _ ≤ 2 * (cutoffPolynomial n).coeffNorm + (3 * n : ℝ) * (cutoffPolynomial n).coeffNorm := by
        gcongr
        exact (coeffNorm_derivative_le _).trans (by
          exact mul_le_mul_of_nonneg_right
            (by exact_mod_cast natDegree_cutoffPolynomial_le n) (coeffNorm_nonneg _))
      _ ≤ (3 * (n + 1) : ℝ) * ((3 : ℝ) ^ n * n.factorial) := by
        have hn := coeffNorm_nonneg (cutoffPolynomial n)
        nlinarith
      _ = (3 : ℝ) ^ (n + 1) * (n + 1).factorial := by
        rw [pow_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
        ring

/-- Every positive-order derivative of the actual cutoff has an explicit uniform growth bound. -/
theorem norm_iteratedDeriv_cutoff_le {n : ℕ} (hn : 1 ≤ n) (x : ℝ) :
    ‖iteratedDeriv n cutoff x‖ ≤
      exp ((5 / 2 : ℝ) * n * log n + ((5 / 2 : ℝ) * log 3) * n) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hn
  by_cases hx : x ≤ 0
  · rw [iteratedDeriv_cutoff_eq_zero n hx, norm_zero]
    positivity
  · rw [iteratedDeriv_cutoff, norm_mul, cutoff_eq_exp (lt_of_not_ge hx),
      norm_of_nonneg (exp_pos _).le]
    calc
      _ ≤ (cutoffPolynomial n).coeffNorm * exp ((3 * n : ℝ) / 2 * log (3 * n)) := by
        simpa only [neg_one_mul, div_one, Nat.cast_mul, Nat.cast_ofNat] using
          norm_eval_mul_exp_neg_mul_sq_le (cutoffPolynomial n)
            (N := 3 * n) (a := 1) (by omega) (natDegree_cutoffPolynomial_le n)
            (by norm_num) (by norm_cast; omega) x⁻¹
      _ ≤ ((3 : ℝ) ^ n * (n : ℝ) ^ n) * exp ((3 * n : ℝ) / 2 * log (3 * n)) := by
        apply mul_le_mul_of_nonneg_right _ (exp_pos _).le
        exact (coeffNorm_cutoffPolynomial_le n).trans (mul_le_mul_of_nonneg_left
          (by exact_mod_cast Nat.factorial_le_pow n) (by positivity))
      _ = _ := by
        rw [log_mul (by norm_num : (3 : ℝ) ≠ 0) hnpos.ne']
        rw [show (3 : ℝ) ^ n = exp ((n : ℝ) * log 3) by rw [exp_nat_mul, exp_log (by norm_num)],
          show (n : ℝ) ^ n = exp ((n : ℝ) * log n) by rw [exp_nat_mul, exp_log hnpos],
          ← exp_add, ← exp_add]
        congr 1
        ring

/-- Positive-order derivatives of the Gaussian have uniform all-order growth bounds. -/
theorem norm_iteratedDeriv_gaussian_le {n : ℕ} (hn : 1 ≤ n) (x : ℝ) :
    ‖iteratedDeriv n gaussian x‖ ≤
      exp ((3 / 2 : ℝ) * n * log n + ((1 / 2 : ℝ) * log 2) * n) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hm : ((hermite n).map (algebraMap ℤ ℝ)).coeffNorm = (hermite n).coeffNorm := by
    apply coeffNorm_map_of_norm_preserving
    intro a
    simp [Int.norm_eq_abs]
  rw [iteratedDeriv_eq_iterate]
  change ‖deriv^[n] (fun y : ℝ ↦ exp (-(y ^ 2 / 2))) x‖ ≤ _
  rw [deriv_gaussian_eq_hermite_mul_gaussian, norm_mul, norm_mul]
  simp only [norm_pow, norm_neg, norm_one, one_pow, one_mul,
    norm_of_nonneg (exp_pos _).le]
  calc
    _ ≤ ((hermite n).map (algebraMap ℤ ℝ)).coeffNorm *
        exp ((n : ℝ) / 2 * log (n / (1 / 2 : ℝ))) := by
      convert norm_eval_mul_exp_neg_mul_sq_le ((hermite n).map (algebraMap ℤ ℝ))
        hn (natDegree_map_le.trans (by simp)) (by norm_num : (0 : ℝ) < 1 / 2)
        (by linarith : (1 / 2 : ℝ) ≤ n) x using 1
      · simp only [eval_map_algebraMap]
        congr 2
        ring
    _ ≤ (n : ℝ) ^ n * exp ((n : ℝ) / 2 * log (n / (1 / 2 : ℝ))) := by
      apply mul_le_mul_of_nonneg_right _ (exp_pos _).le
      rw [hm]
      exact (coeffNorm_hermite_le n).trans (by exact_mod_cast Nat.factorial_le_pow n)
    _ = _ := by
      rw [show (n : ℝ) ^ n = exp ((n : ℝ) * log n) by rw [exp_nat_mul, exp_log hnpos],
        ← exp_add, show (n : ℝ) / (1 / 2) = 2 * n by ring,
        log_mul (by norm_num : (2 : ℝ) ≠ 0) hnpos.ne']
      congr 1
      ring

/-- The first derivative of the primitive is the scaled Gaussian density. -/
theorem deriv_primitive_eq_gaussian : deriv primitive = fun x ↦ exp (1 / 2 : ℝ) * gaussian x := by
  funext x
  rw [deriv_primitive, gaussian, ← exp_add]
  congr 1
  ring

/-- Every positive derivative of the primitive is an actual Gaussian derivative. -/
theorem iteratedDeriv_primitive_succ (n : ℕ) (x : ℝ) :
    iteratedDeriv (n + 1) primitive x = exp (1 / 2 : ℝ) * iteratedDeriv n gaussian x := by
  rw [iteratedDeriv_succ', deriv_primitive_eq_gaussian,
    iteratedDeriv_const_mul_field]

/-- The primitive has an explicit simultaneous bound on every positive-order derivative. -/
theorem norm_iteratedDeriv_primitive_succ_le (n : ℕ) (x : ℝ) :
    ‖iteratedDeriv (n + 1) primitive x‖ ≤
      exp ((3 / 2 : ℝ) * (n + 1) * log (n + 1) + (1 + log 2) * (n + 1)) := by
  rw [iteratedDeriv_primitive_succ, norm_mul, norm_of_nonneg (exp_pos _).le]
  have hlog2 : 0 ≤ log (2 : ℝ) := log_nonneg (by norm_num)
  by_cases hn : n = 0
  · subst n
    simp only [iteratedDeriv_zero, Nat.cast_zero, zero_add, log_one, mul_zero, zero_add,
      mul_one, gaussian]
    calc
      _ ≤ exp (1 / 2 : ℝ) * 1 := by
        apply mul_le_mul_of_nonneg_left _ (exp_pos _).le
        rw [norm_of_nonneg (exp_pos _).le]
        apply exp_le_one_iff.mpr
        nlinarith [sq_nonneg x]
      _ ≤ _ := by rw [mul_one]; apply exp_le_exp.mpr; linarith
  · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    have hn1r : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have hlogn : 0 ≤ log (n : ℝ) := log_nonneg hn1r
    have hlog : log (n : ℝ) ≤ log (n + 1 : ℝ) :=
      log_le_log (by positivity) (by linarith)
    calc
      _ ≤ exp (1 / 2 : ℝ) *
          exp ((3 / 2 : ℝ) * n * log n + ((1 / 2 : ℝ) * log 2) * n) :=
        mul_le_mul_of_nonneg_left (norm_iteratedDeriv_gaussian_le hn1 x) (exp_pos _).le
      _ ≤ _ := by
        rw [← exp_add]
        apply exp_le_exp.mpr
        have hm : (n : ℝ) * log n ≤ (n + 1 : ℝ) * log (n + 1 : ℝ) :=
          mul_le_mul (by linarith) hlog hlogn (by positivity)
        nlinarith

/-- All positive-order primitive derivatives satisfy one explicit uniform growth estimate. -/
theorem norm_iteratedDeriv_primitive_le {n : ℕ} (hn : 1 ≤ n) (x : ℝ) :
    ‖iteratedDeriv n primitive x‖ ≤
      exp ((3 / 2 : ℝ) * n * log n + (1 + log 2) * n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hn)
  simpa only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] using
    norm_iteratedDeriv_primitive_succ_le m x

end Analysis.FlatGaussian
