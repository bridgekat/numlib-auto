import Numlib.Analysis.Polynomial.CoefficientNorm
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RingTheory.Polynomial.Hermite.Basic

/-!
# Polynomial-weighted Gaussian bounds

An elementary logarithmic estimate bounds every monomial up to a given degree
against a scaled Gaussian. Summing with the coefficient norm yields a uniform
polynomial estimate without any unspecified order-dependent constants.
-/

noncomputable section
open Real Finset

namespace Polynomial

/-- Powers times a Gaussian are bounded uniformly by its degree and scale. -/
theorem _root_.Real.pow_mul_exp_neg_mul_sq_le {N k : ℕ} {a : ℝ} (hN : 1 ≤ N)
    (hk : k ≤ N) (ha : 0 < a) (hNa : a ≤ N) (x : ℝ) :
    |x| ^ k * exp (-a * x ^ 2) ≤ exp ((N : ℝ) / 2 * log (N / a)) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hN
  have hlarge (z : ℝ) (hz : 0 < z) :
      z ^ N * exp (-a * z ^ 2) ≤ exp ((N : ℝ) / 2 * log (N / a)) := by
    have hl := log_le_sub_one_of_pos
      (div_pos (mul_pos ha (sq_pos_of_pos hz)) hNpos)
    rw [log_div (mul_pos ha (sq_pos_of_pos hz)).ne' hNpos.ne',
      log_mul ha.ne' (sq_pos_of_pos hz).ne', log_pow] at hl
    have hm := mul_le_mul_of_nonneg_left hl hNpos.le
    have he : (N : ℝ) * log z - a * z ^ 2 ≤ (N : ℝ) / 2 * log (N / a) := by
      have heq : (N : ℝ) * (a * z ^ 2 / N - 1) = a * z ^ 2 - N := by field_simp
      rw [heq] at hm
      rw [log_div hNpos.ne' ha.ne']
      nlinarith
    calc
      _ = exp ((N : ℝ) * log z - a * z ^ 2) := by
        rw [sub_eq_add_neg, exp_add, exp_nat_mul, exp_log hz]
        congr 2
        ring
      _ ≤ _ := exp_le_exp.mpr he
  by_cases hx : |x| ≤ 1
  · calc
      _ ≤ 1 * 1 := mul_le_mul (pow_le_one₀ (abs_nonneg x) hx)
        (exp_le_one_iff.mpr (by nlinarith [sq_nonneg x])) (exp_pos _).le (by norm_num)
      _ ≤ _ := by
        simpa using one_le_exp (mul_nonneg (by positivity)
          (log_nonneg ((le_div_iff₀ ha).mpr (by simpa using hNa))))
  · calc
      _ ≤ |x| ^ N * exp (-a * x ^ 2) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (le_of_not_ge hx) hk) (exp_pos _).le
      _ = |x| ^ N * exp (-a * |x| ^ 2) := by rw [sq_abs]
      _ ≤ _ := hlarge |x| (lt_trans zero_lt_one (lt_of_not_ge hx))

/-- A coefficient-sum and degree bound control a polynomial times a scaled Gaussian. -/
theorem norm_eval_mul_exp_neg_mul_sq_le (p : ℝ[X]) {N : ℕ} {a : ℝ}
    (hN : 1 ≤ N) (hd : p.natDegree ≤ N) (ha : 0 < a) (hNa : a ≤ N) (x : ℝ) :
    ‖p.eval x‖ * exp (-a * x ^ 2) ≤ p.coeffNorm * exp ((N : ℝ) / 2 * log (N / a)) := by
  have he : p.eval x = ∑ i ∈ p.support, p.coeff i * x ^ i := by
    rw [eval_eq_sum, Polynomial.sum]
  rw [he, coeffNorm, Polynomial.sum, Finset.sum_mul]
  calc
    _ ≤ (∑ i ∈ p.support, ‖p.coeff i * x ^ i‖) * exp (-a * x ^ 2) :=
      mul_le_mul_of_nonneg_right (norm_sum_le _ _) (exp_pos _).le
    _ = ∑ i ∈ p.support, ‖p.coeff i‖ * (|x| ^ i * exp (-a * x ^ 2)) := by
      simp_rw [Finset.sum_mul, norm_mul, norm_pow, Real.norm_eq_abs, mul_assoc]
    _ ≤ _ := Finset.sum_le_sum fun i hi ↦
      mul_le_mul_of_nonneg_left (pow_mul_exp_neg_mul_sq_le hN
        ((le_natDegree_of_mem_supp i hi).trans hd) ha hNa x) (norm_nonneg _)

/-- The probabilists' Hermite polynomials have factorially bounded coefficient sums. -/
theorem coeffNorm_hermite_le (n : ℕ) : (hermite n).coeffNorm ≤ (n.factorial : ℝ) := by
  induction n with
  | zero => simp [hermite_zero]
  | succ n ih =>
    rw [hermite_succ]
    calc
      _ ≤ (X * hermite n).coeffNorm + (hermite n).derivative.coeffNorm := coeffNorm_sub_le _ _
      _ ≤ (hermite n).coeffNorm + (n : ℝ) * (hermite n).coeffNorm := by
        rw [coeffNorm_X_mul]
        exact add_le_add le_rfl (by
          simpa only [natDegree_hermite] using (coeffNorm_derivative_le (hermite n)))
      _ ≤ (n + 1 : ℝ) * (n.factorial : ℝ) := by
        nlinarith [coeffNorm_nonneg (hermite n)]
      _ = ((n + 1).factorial : ℝ) := by
        rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]

end Polynomial
