import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic

/-!
# Exponents for residual-root decrease

The algebraic comparison is stated for real model degree and derivative order. Concrete
natural-number choices additionally enforce smoothness and admissible derivative orders.
-/

noncomputable section
namespace Optimization

/-- Exponent of the residual norm in a derivative-order root-potential decrease bound. -/
def residualDescentExponent (p ell : ℝ) (i : ℕ) (j : ℝ) : ℝ :=
  ((2 : ℝ) ^ i - 1) / (2 : ℝ) ^ i - j * (ell - 1) / (p - j + 1)

/-- The root contribution is one minus the inverse power of two. -/
theorem residualDescentExponent_eq_sub_inv (p ell : ℝ) (i : ℕ) (j : ℝ) :
    residualDescentExponent p ell i j =
      1 - 1 / (2 : ℝ) ^ i - j * (ell - 1) / (p - j + 1) := by
  unfold residualDescentExponent
  rw [sub_div, div_self (by positivity : (2 : ℝ) ^ i ≠ 0)]

/-- Choosing `ell = p / j` leaves an elementary reciprocal difference. -/
theorem residualDescentExponent_div_order {p j : ℝ} (hj : j ≠ 0)
    (hD : p - j + 1 ≠ 0) (i : ℕ) :
    residualDescentExponent p (p / j) i j = 1 / (p - j + 1) - 1 / (2 : ℝ) ^ i := by
  rw [residualDescentExponent_eq_sub_inv]
  field_simp
  ring

/-- The simple choice has a positive residual exponent precisely above its power threshold. -/
theorem residualDescentExponent_pos_div_order {p j : ℝ} (hj : j ≠ 0)
    (hD : 0 < p - j + 1) {i : ℕ} (hi : p - j + 1 < (2 : ℝ) ^ i) :
    0 < residualDescentExponent p (p / j) i j := by
  rw [residualDescentExponent_div_order hj hD.ne']
  exact sub_pos.mpr (one_div_lt_one_div_of_lt hD hi)

/-- The logarithmic form of the simple parameter choice gives a positive exponent. -/
theorem residualDescentExponent_pos_div_order_of_logb {p j : ℝ} (hj : j ≠ 0)
    (hD : 0 < p - j + 1) {i : ℕ} (hi : Real.logb 2 (p - j + 1) < i) :
    0 < residualDescentExponent p (p / j) i j := by
  apply residualDescentExponent_pos_div_order hj hD
  simpa only [Real.rpow_natCast] using
    (Real.logb_lt_iff_lt_rpow (by norm_num : (1 : ℝ) < 2) hD).mp hi

/-- Solving for the residual exponent gives an exact zero. -/
theorem residualDescentExponent_eq_zero_of_choice {p ell j : ℝ} (hj : j ≠ 0)
    (hD : p - j + 1 ≠ 0) (i : ℕ)
    (hell : ell = 1 + ((2 : ℝ) ^ i - 1) * (p - j + 1) / (j * (2 : ℝ) ^ i)) :
    residualDescentExponent p ell i j = 0 := by
  rw [hell, residualDescentExponent]
  field_simp
  ring

/-- Exact difference of the exponents at two derivative orders. -/
theorem residualDescentExponent_sub {p ell j k : ℝ}
    (hj : p - j + 1 ≠ 0) (hk : p - k + 1 ≠ 0) (i : ℕ) :
    residualDescentExponent p ell i j - residualDescentExponent p ell i k =
      (k - j) * (p + 1) * (ell - 1) / ((p - j + 1) * (p - k + 1)) := by
  unfold residualDescentExponent
  field_simp
  ring

/-- Earlier derivative orders have strictly larger exponents. -/
theorem residualDescentExponent_strictAnti_order {p ell j k : ℝ}
    (hjk : j < k) (hD : 0 < p - k + 1) (hp : 0 < p + 1) (hell : 1 < ell) (i : ℕ) :
    residualDescentExponent p ell i k < residualDescentExponent p ell i j := by
  have hj : 0 < p - j + 1 := by linarith
  have h := residualDescentExponent_sub hj.ne' hD.ne' i (ell := ell)
  have hh : 0 < (k - j) * (p + 1) * (ell - 1) /
      ((p - j + 1) * (p - k + 1)) := by positivity
  linarith

/-- The third-order geometric sum is exactly one third of the root-power numerator. -/
theorem three_mul_sum_two_pow_even (j : ℕ) :
    3 * (∑ k ∈ Finset.range j, (2 : ℝ) ^ (2 * k)) = (2 : ℝ) ^ (2 * j) - 1 := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    rw [show 2 * (j + 1) = 2 * j + 2 by omega, pow_add]
    norm_num
    ring

/-- The residual exponent is the difference between the cascade denominator and the
residual scaling in the powered derivative measure. -/
theorem residualDescentExponent_eq_power_difference {p ell j : ℝ}
    (hD : p - j + 1 ≠ 0) (i : ℕ) :
    residualDescentExponent p ell i j = ell - 1 / (2 : ℝ) ^ i -
      (ell - 1) * ((p + 1) / (p - j + 1)) := by
  unfold residualDescentExponent
  field_simp
  ring

/-- The six natural-degree parameter choices, with all earlier-order positivity conclusions. -/
theorem residualDescentExponent_good_choices {p i : ℕ} {ell : ℝ} (hp : 1 ≤ p) (hell : 1 < ell) :
    (ell = p → Real.logb 2 p < i → 0 < residualDescentExponent (p : ℝ) ell i 1) ∧
    ((∃ o : ℕ, Odd o ∧ p = o * 2 ^ i ∧ ell = 1 + (o : ℝ) * ((2 : ℝ) ^ i - 1)) →
      residualDescentExponent (p : ℝ) ell i 1 = 0 ∧ 1 < ell) ∧
    (Even p → ell = (p : ℝ) / 2 → Real.logb 2 ((p : ℝ) - 1) < i →
      0 < residualDescentExponent (p : ℝ) ell i 1 ∧ 0 < residualDescentExponent (p : ℝ) ell i 2) ∧
    (4 ∣ p - 1 →
      (∃ o : ℕ, Odd o ∧ p - 1 = o * 2 ^ (i + 1) ∧
        ell = 1 + (o : ℝ) * ((2 : ℝ) ^ i - 1)) →
      0 < residualDescentExponent (p : ℝ) ell i 1 ∧ residualDescentExponent (p : ℝ) ell i 2 = 0 ∧
        1 < ell) ∧
    (3 ∣ p → ell = (p : ℝ) / 3 → Real.logb 2 ((p : ℝ) - 2) < i →
      0 < residualDescentExponent (p : ℝ) ell i 1 ∧ 0 < residualDescentExponent (p : ℝ) ell i 2 ∧
        0 < residualDescentExponent (p : ℝ) ell i 3) ∧
    ((∃ o h : ℕ, Odd o ∧ 0 < h ∧ i = 2 * h ∧ p - 2 = o * 2 ^ i ∧
      ell = 1 + (o : ℝ) * ∑ k ∈ Finset.range h, (2 : ℝ) ^ (2 * k)) →
      0 < residualDescentExponent (p : ℝ) ell i 1 ∧ 0 < residualDescentExponent (p : ℝ) ell i 2 ∧
        residualDescentExponent (p : ℝ) ell i 3 = 0 ∧ 1 < ell) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hT : (2 : ℝ) ^ i ≠ 0 := by positivity
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro he hi
    subst ell
    simpa only [div_one, sub_self, zero_add] using
      residualDescentExponent_pos_div_order_of_logb (p := (p : ℝ))
        (j := 1) (by norm_num) (by linarith) (by simpa using hi)
  · rintro ⟨o, _, hpo, he⟩
    have hpr : (p : ℝ) = o * (2 : ℝ) ^ i := by exact_mod_cast hpo
    refine ⟨?_, hell⟩
    apply residualDescentExponent_eq_zero_of_choice (by norm_num)
      (by simpa using hp0.ne')
    rw [he, hpr]
    field_simp
    ring
  · intro _ he hi
    have hpr : (2 : ℝ) < p := by linarith
    have h2 : 0 < residualDescentExponent p ell i 2 := by
      rw [he]
      exact residualDescentExponent_pos_div_order_of_logb (by norm_num)
        (by linarith) (by convert hi using 1; congr 1; ring)
    have h12 := residualDescentExponent_strictAnti_order
      (p := (p : ℝ)) (ell := ell) (j := 1) (k := 2)
      (by norm_num) (by linarith) (by linarith) hell i
    exact ⟨h2.trans h12, h2⟩
  · rintro _ ⟨o, ho, hpo, he⟩
    have hpm : 2 ≤ p := by
      have hpos : 0 < o * 2 ^ (i + 1) := Nat.mul_pos ho.pos (by positivity)
      omega
    have hpmr : (2 : ℝ) ≤ p := by exact_mod_cast hpm
    have hpr : (p : ℝ) - 1 = o * (2 : ℝ) ^ (i + 1) := by
      exact_mod_cast hpo
    have h2 : residualDescentExponent p ell i 2 = 0 := by
      apply residualDescentExponent_eq_zero_of_choice (by norm_num) (by linarith)
      rw [he, show (p : ℝ) - 2 + 1 = (p : ℝ) - 1 by ring, hpr, pow_succ]
      field_simp
    have h12 := residualDescentExponent_strictAnti_order
      (p := (p : ℝ)) (ell := ell) (j := 1) (k := 2)
      (by norm_num) (by linarith) (by linarith) hell i
    exact ⟨by linarith, h2, hell⟩
  · intro _ he hi
    have hpr : (3 : ℝ) < p := by linarith
    have h3 : 0 < residualDescentExponent p ell i 3 := by
      rw [he]
      exact residualDescentExponent_pos_div_order_of_logb (by norm_num)
        (by linarith) (by convert hi using 1; congr 1; ring)
    have h23 := residualDescentExponent_strictAnti_order
      (p := (p : ℝ)) (ell := ell) (j := 2) (k := 3)
      (by norm_num) (by linarith) (by linarith) hell i
    have h13 := residualDescentExponent_strictAnti_order
      (p := (p : ℝ)) (ell := ell) (j := 1) (k := 3)
      (by norm_num) (by linarith) (by linarith) hell i
    exact ⟨h3.trans h13, h3.trans h23, h3⟩
  · rintro ⟨o, h, ho, _, rfl, hpo, he⟩
    have hpm : 3 ≤ p := by
      have hpos : 0 < o * 2 ^ (2 * h) := Nat.mul_pos ho.pos (by positivity)
      omega
    have hpmr : (3 : ℝ) ≤ p := by exact_mod_cast hpm
    have hpr : (p : ℝ) - 2 = o * (2 : ℝ) ^ (2 * h) := by
      have hh := congrArg (fun n : ℕ => (n : ℝ)) hpo
      simpa only [Nat.cast_sub (by omega : 2 ≤ p), Nat.cast_mul, Nat.cast_pow,
        Nat.cast_ofNat] using hh
    have hsum := three_mul_sum_two_pow_even h
    have h3 : residualDescentExponent p ell (2 * h) 3 = 0 := by
      apply residualDescentExponent_eq_zero_of_choice (by norm_num) (by linarith)
      rw [he, show (p : ℝ) - 3 + 1 = (p : ℝ) - 2 by ring, hpr]
      congr 1
      apply (eq_div_iff (by positivity : (3 : ℝ) * 2 ^ (2 * h) ≠ 0)).2
      nlinarith [hsum]
    have h23 := residualDescentExponent_strictAnti_order
      (p := (p : ℝ)) (ell := ell) (j := 2) (k := 3)
      (by norm_num) (by linarith) (by linarith) hell (2 * h)
    have h13 := residualDescentExponent_strictAnti_order
      (p := (p : ℝ)) (ell := ell) (j := 1) (k := 3)
      (by norm_num) (by linarith) (by linarith) hell (2 * h)
    exact ⟨by linarith,
      by linarith, h3, hell⟩


end Optimization
