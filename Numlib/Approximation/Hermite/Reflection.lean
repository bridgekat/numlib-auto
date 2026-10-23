import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Tactic

/-!
# Reflection of polynomial jets on a finite interval

Reflection about the midpoint preserves every absolute derivative bound and every
Lipschitz constant. Odd jets change sign and even jets keep their sign, including
at the exchanged endpoints.
-/

namespace Hermite
open Polynomial Set
open scoped NNReal

/-- Reflection of a real polynomial across the midpoint of `[0,W]`. -/
noncomputable def reflectPolynomial (Q : ℝ[X]) (W : ℝ) : ℝ[X] := Q.comp (C W - X)

/-- Evaluation of the reflected polynomial is evaluation at the reflected argument. -/
@[simp] theorem eval_reflectPolynomial (Q : ℝ[X]) (W t : ℝ) :
    (reflectPolynomial Q W).eval t = Q.eval (W - t) := by
  simp [reflectPolynomial]

/-- Every actual derivative of the reflected polynomial has its exact parity sign. -/
theorem iteratedDeriv_reflectPolynomial (Q : ℝ[X]) (W : ℝ) (j : ℕ) (t : ℝ) :
    iteratedDeriv j (reflectPolynomial Q W).eval t =
      (-1 : ℝ) ^ j * iteratedDeriv j Q.eval (W - t) := by
  have heq : (reflectPolynomial Q W).eval = fun z => Q.eval (W - z) := by
    funext z
    exact eval_reflectPolynomial Q W z
  rw [heq]
  simpa only [smul_eq_mul] using congrFun (iteratedDeriv_comp_const_sub j Q.eval W) t

/-- Reflection preserves the absolute value of every actual derivative. -/
theorem abs_iteratedDeriv_reflectPolynomial (Q : ℝ[X]) (W : ℝ) (j : ℕ) (t : ℝ) :
    |iteratedDeriv j (reflectPolynomial Q W).eval t| =
      |iteratedDeriv j Q.eval (W - t)| := by
  rw [iteratedDeriv_reflectPolynomial, abs_mul]
  simp

/-- Reflection maps every point of the interval to another point of that interval. -/
theorem sub_mem_Icc {W t : ℝ} (ht : t ∈ Icc 0 W) : W - t ∈ Icc 0 W := by
  constructor <;> linarith [ht.1, ht.2]

/-- Every interval bound on an absolute derivative is preserved with the same constant. -/
theorem abs_iteratedDeriv_reflectPolynomial_le {Q : ℝ[X]} {W B : ℝ} {j : ℕ}
    (h : ∀ t ∈ Icc 0 W, |iteratedDeriv j Q.eval t| ≤ B) :
    ∀ t ∈ Icc 0 W, |iteratedDeriv j (reflectPolynomial Q W).eval t| ≤ B := by
  intro t ht
  rw [abs_iteratedDeriv_reflectPolynomial]
  exact h _ (sub_mem_Icc ht)

/-- A pointwise norm formulation of the same-constant derivative Lipschitz bound. -/
theorem norm_iteratedDeriv_reflectPolynomial_sub_le {Q : ℝ[X]} {W L : ℝ} {p : ℕ}
    (h : ∀ x ∈ Icc 0 W, ∀ y ∈ Icc 0 W,
      ‖iteratedDeriv p Q.eval x - iteratedDeriv p Q.eval y‖ ≤ L * ‖x - y‖) :
    ∀ x ∈ Icc 0 W, ∀ y ∈ Icc 0 W,
      ‖iteratedDeriv p (reflectPolynomial Q W).eval x -
        iteratedDeriv p (reflectPolynomial Q W).eval y‖ ≤ L * ‖x - y‖ := by
  intro x hx y hy
  rw [iteratedDeriv_reflectPolynomial, iteratedDeriv_reflectPolynomial, ←mul_sub, norm_mul]
  simp only [norm_pow, norm_neg, norm_one, one_pow, one_mul]
  have hh := h _ (sub_mem_Icc hx) _ (sub_mem_Icc hy)
  simpa only [show W - x - (W - y) = -(x - y) by ring, norm_neg] using hh

/-- Reflection preserves a derivative's Lipschitz bound on the interval exactly. -/
theorem iteratedDeriv_reflectPolynomial_lipschitzOnWith {Q : ℝ[X]} {W : ℝ}
    {p : ℕ} {K : ℝ≥0} (h : LipschitzOnWith K (iteratedDeriv p Q.eval) (Icc 0 W)) :
    LipschitzOnWith K (iteratedDeriv p (reflectPolynomial Q W).eval) (Icc 0 W) := by
  rw [lipschitzOnWith_iff_norm_sub_le] at h ⊢
  intro x hx y hy
  rw [iteratedDeriv_reflectPolynomial, iteratedDeriv_reflectPolynomial, ←mul_sub, norm_mul]
  simp only [norm_pow, norm_neg, norm_one, one_pow, one_mul]
  have hh := h (sub_mem_Icc hx) (sub_mem_Icc hy)
  simpa only [show W - x - (W - y) = -(x - y) by ring, norm_neg] using hh

/-- The initial derivative jet of the reflection comes from the terminal original jet. -/
@[simp] theorem iteratedDeriv_reflectPolynomial_zero (Q : ℝ[X]) (W : ℝ) (j : ℕ) :
    iteratedDeriv j (reflectPolynomial Q W).eval 0 =
      (-1 : ℝ) ^ j * iteratedDeriv j Q.eval W := by
  simp only [iteratedDeriv_reflectPolynomial, sub_zero]

/-- The terminal derivative jet of the reflection comes from the initial original jet. -/
@[simp] theorem iteratedDeriv_reflectPolynomial_end (Q : ℝ[X]) (W : ℝ) (j : ℕ) :
    iteratedDeriv j (reflectPolynomial Q W).eval W =
      (-1 : ℝ) ^ j * iteratedDeriv j Q.eval 0 := by
  simp only [iteratedDeriv_reflectPolynomial, sub_self]

/-- A flat initial jet and sign-adjusted terminal jet reflect to the desired initial
jet and flat terminal jet. Both endpoint values are included as order zero. -/
theorem reflectPolynomial_endpoint_jets {Q : ℝ[X]} {W a : ℝ} {b : ℕ → ℝ} {p : ℕ}
    (hleft : ∀ j ≤ p, iteratedDeriv j Q.eval 0 = if j = 0 then a else 0)
    (hright : ∀ j ≤ p, iteratedDeriv j Q.eval W = (-1 : ℝ) ^ j * b j) :
    (∀ j ≤ p, iteratedDeriv j (reflectPolynomial Q W).eval 0 = b j) ∧
      ∀ j ≤ p, iteratedDeriv j (reflectPolynomial Q W).eval W = if j = 0 then a else 0 := by
  constructor
  · intro j hj
    rw [iteratedDeriv_reflectPolynomial_zero, hright j hj, ←mul_assoc, ←pow_add]
    simp [←two_mul, pow_mul]
  · intro j hj
    rw [iteratedDeriv_reflectPolynomial_end, hleft j hj]
    split_ifs with hj0
    · subst j
      simp
    · simp

end Hermite
