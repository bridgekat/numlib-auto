import Numlib.Analysis.Calculus.NormPowerCoefficientBounds
import Numlib.Analysis.Calculus.SecondOrderMaximumPrinciple
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Tactic

/-!
# Radial derivative polynomials

Normalized directional derivatives of a norm power are polynomials in the cosine of
its direction. Their differential equation gives a sharp bound on the unit interval.
-/

noncomputable section

open Polynomial
open scoped Polynomial

/-- The polynomial giving the normalized directional derivative of a radial power. -/
noncomputable def radialDerivativePolynomial (a : ℝ) : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => C (a - n) * X * radialDerivativePolynomial a n +
      (1 - X ^ 2) * (radialDerivativePolynomial a n).derivative
termination_by structural n => n

/-- The initial radial derivative polynomial is constant one. -/
@[simp] theorem radialDerivativePolynomial_zero (a : ℝ) :
    radialDerivativePolynomial a 0 = 1 := rfl

/-- Differentiation of the radius and of the directional cosine gives this recurrence. -/
theorem radialDerivativePolynomial_succ (a : ℝ) (n : ℕ) :
    radialDerivativePolynomial a (n + 1) =
      C (a - n) * X * radialDerivativePolynomial a n +
        (1 - X ^ 2) * (radialDerivativePolynomial a n).derivative := rfl

/-- The differential operator whose nullspace contains a radial derivative polynomial. -/
def radialPolynomialODE (a : ℝ) (n : ℕ) (P : ℝ[X]) : ℝ[X] :=
  (1 - X ^ 2) * P.derivative.derivative + C (a - 1) * X * P.derivative -
    C ((n : ℝ) * (a - n)) * P

/-- The raising recurrence intertwines the differential operators in consecutive orders. -/
theorem radialPolynomialODE_raise (a : ℝ) (n : ℕ) (P : ℝ[X]) :
    radialPolynomialODE a (n + 1) (C (a - n) * X * P + (1 - X ^ 2) * P.derivative) =
      (1 - X ^ 2) * (radialPolynomialODE a n P).derivative +
        C (a - n - 2) * X * radialPolynomialODE a n P := by
  simp [radialPolynomialODE, derivative_mul, derivative_pow, map_sub, map_mul, map_add]
  simp only [C_ofNat]
  ring

/-- The polynomial differential equation for each normalized radial derivative. -/
theorem radialDerivativePolynomial_ode (a : ℝ) (n : ℕ) :
    radialPolynomialODE a n (radialDerivativePolynomial a n) = 0 := by
  induction n with
  | zero => simp [radialPolynomialODE]
  | succ n ih =>
    rw [radialDerivativePolynomial_succ, radialPolynomialODE_raise, ih]
    simp

/-- The radial endpoint is the falling product of the exponent. -/
theorem radialDerivativePolynomial_eval_one (a : ℝ) (n : ℕ) :
    (radialDerivativePolynomial a n).eval 1 = ∏ i : Fin n, (a - i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [radialDerivativePolynomial_succ]
    simp only [eval_add, eval_mul, eval_C, eval_X, eval_sub, eval_one, eval_pow,
      one_pow, sub_self, zero_mul, add_zero, mul_one, ih, Fin.prod_univ_castSucc,
      Fin.val_castSucc, Fin.val_last]
    ring

/-- The opposite radial endpoint has the expected parity. -/
theorem radialDerivativePolynomial_eval_neg_one (a : ℝ) (n : ℕ) :
    (radialDerivativePolynomial a n).eval (-1) =
      (-1) ^ n * ∏ i : Fin n, (a - i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [radialDerivativePolynomial_succ]
    simp only [eval_add, eval_mul, eval_C, eval_X, eval_sub, eval_one, eval_pow,
      ih, Fin.prod_univ_castSucc,
      Fin.val_castSucc, Fin.val_last, pow_succ]
    ring

/-- Evaluation turns the polynomial equation into its scalar differential equation. -/
theorem radialDerivativePolynomial_ode_eval (a : ℝ) (n : ℕ) (t : ℝ) :
    (1 - t ^ 2) * (radialDerivativePolynomial a n).derivative.derivative.eval t +
        (a - 1) * t * (radialDerivativePolynomial a n).derivative.eval t =
      (n : ℝ) * (a - n) * (radialDerivativePolynomial a n).eval t := by
  have h := congrArg (fun P : ℝ[X] => P.eval t) (radialDerivativePolynomial_ode a n)
  simpa [radialPolynomialODE, sub_eq_zero] using h

/-- The falling product is positive strictly below the exponent. -/
theorem fallingProduct_pos_of_lt {a : ℝ} {n : ℕ} (hn : (n : ℝ) < a) :
    0 < ∏ i : Fin n, (a - i) := by
  rw [Fin.prod_univ_eq_prod_range (fun i : ℕ => a - i),
    ← descPochhammer_eval_eq_prod_range]
  exact descPochhammer_pos (by linarith)

/-- On the unit interval every normalized radial derivative is bounded sharply by
its radial endpoint, provided its order is strictly below the exponent. -/
theorem abs_radialDerivativePolynomial_eval_le {a : ℝ} {n : ℕ} (hn : (n : ℝ) < a)
    {t : ℝ} (ht : t ∈ Set.Icc (-1) 1) :
    |(radialDerivativePolynomial a n).eval t| ≤ ∏ i : Fin n, (a - i) := by
  rcases n with _ | n
  · simp
  let P := radialDerivativePolynomial a (n + 1)
  have hd : deriv (fun t => P.eval t) = fun t => P.derivative.eval t :=
    funext fun _ => P.deriv
  have hdd : deriv (fun t => P.derivative.eval t) =
      fun t => P.derivative.derivative.eval t := funext fun _ => P.derivative.deriv
  apply abs_le_of_second_order_ode (f := fun t => P.eval t)
    (A := fun t => 1 - t ^ 2) (B := fun t => (a - 1) * t)
    (c := ((n + 1 : ℕ) : ℝ) * (a - ((n + 1 : ℕ) : ℝ))) (by norm_num)
    P.continuous.continuousOn (mul_pos (by positivity) (by exact sub_pos.mpr hn))
    (fun x hx => by nlinarith [hx.1, hx.2]) ?_ ?_ ?_ t ht
  · intro x _
    rw [hd, hdd]
    exact radialDerivativePolynomial_ode_eval a (n + 1) x
  · change |(radialDerivativePolynomial a (n + 1)).eval (-1)| ≤ _
    rw [radialDerivativePolynomial_eval_neg_one, abs_mul,
      abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_pos (fallingProduct_pos_of_lt hn)]
  · change |(radialDerivativePolynomial a (n + 1)).eval 1| ≤ _
    rw [radialDerivativePolynomial_eval_one, abs_of_pos (fallingProduct_pos_of_lt hn)]

/-- The differential equation gives a three-term recurrence with no derivatives. -/
theorem radialDerivativePolynomial_succ_succ (a : ℝ) (n : ℕ) :
    radialDerivativePolynomial a (n + 2) =
      C (a - 2 * n - 2) * X * radialDerivativePolynomial a (n + 1) +
        C (((n + 1 : ℕ) : ℝ) * (a - n)) * radialDerivativePolynomial a n := by
  have h := radialDerivativePolynomial_ode a n
  have he (P : ℝ[X]) :
      C (a - (n + 1)) * X * (C (a - n) * X * P + (1 - X ^ 2) * P.derivative) +
        (1 - X ^ 2) * (C (a - n) * X * P + (1 - X ^ 2) * P.derivative).derivative =
      C (a - 2 * n - 2) * X * (C (a - n) * X * P + (1 - X ^ 2) * P.derivative) +
        C (((n + 1 : ℕ) : ℝ) * (a - n)) * P +
        (1 - X ^ 2) * radialPolynomialODE a n P := by
    simp [radialPolynomialODE, derivative_mul, derivative_pow, map_sub, map_mul, map_add]
    simp only [C_ofNat]
    ring
  rw [show n + 2 = (n + 1) + 1 by omega, radialDerivativePolynomial_succ,
    radialDerivativePolynomial_succ a n]
  push_cast at *
  rw [he, h, mul_zero, add_zero]

/-- The polynomial is the actual derivative jet of a quadratic radial power at zero. -/
theorem iteratedDeriv_quadratic_rpow_zero_eq_polynomial (a b : ℝ) (n : ℕ) :
    iteratedDeriv n (fun t : ℝ => (1 + 2 * b * t + t ^ 2) ^ (a / 2)) 0 =
      (radialDerivativePolynomial a n).eval b := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one =>
    have hd := ((((hasDerivAt_id (0 : ℝ)).const_mul (2 * b)).const_add 1).add
      ((hasDerivAt_id (0 : ℝ)).pow 2)).rpow_const (p := a / 2) (Or.inl (by norm_num))
    change HasDerivAt (fun t : ℝ => (1 + 2 * b * t + t ^ 2) ^ (a / 2)) _ 0 at hd
    rw [iteratedDeriv_one, hd.deriv, radialDerivativePolynomial_succ]
    simp
    ring
  | more n hn hn1 =>
    rw [iteratedDeriv_quadratic_rpow_succ_succ, hn, hn1,
      radialDerivativePolynomial_succ_succ]
    simp only [eval_add, eval_mul, eval_C, eval_X]
    push_cast
    ring
