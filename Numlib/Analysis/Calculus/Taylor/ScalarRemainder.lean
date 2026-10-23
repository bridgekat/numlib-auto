/-
Upstreaming candidate: scalar Taylor remainders with ordinary iterated derivatives.
Natural home: Mathlib.Analysis.Calculus.Taylor. No optimization-specific assumptions are used.
-/
import Numlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-!
# Scalar Taylor remainder identities

The Lagrange and integral remainder formulas are stated with ordinary derivatives. The
integral identity subtracts the highest Taylor term, expressing the remainder using only
variation of the highest derivative, as required for Hölder and Lipschitz estimates.
-/

open Set
open scoped BigOperators

/-- Taylor's Lagrange remainder with ordinary derivatives, including coincident endpoints.
Smoothness near the expansion point determines the two-sided Taylor coefficients, while
smoothness on the interval suffices for the intermediate-point remainder. -/
theorem exists_sub_sum_eq_iteratedDeriv_mul {f : ℝ → ℝ} {n : ℕ} {a b : ℝ}
    (ha : ContDiffAt ℝ n f a) (hf : ContDiffOn ℝ (n + 1) f (uIcc a b)) :
    ∃ ξ ∈ uIcc a b, f b -
        (∑ i ∈ Finset.range (n + 1), (b - a) ^ i / i.factorial * iteratedDeriv i f a) =
      iteratedDeriv (n + 1) f ξ * (b - a) ^ (n + 1) / (n + 1).factorial := by
  by_cases hab : a = b
  · subst b
    refine ⟨a, by simp, ?_⟩
    simp [Finset.sum_range_succ', pow_succ]
  · obtain ⟨ξ, hξ, heq⟩ := exists_taylorWithinEval_add_iteratedDeriv_mul hab hf
    refine ⟨ξ, Ioo_subset_Icc_self hξ, ?_⟩
    rw [taylorWithinEval_eq_sum_of_contDiffAt hab ha] at heq
    linarith

/-- The remainder after degree `n + 1` is the integral of the variation of the highest
derivative against the Taylor kernel. Smoothness on a neighborhood of each interval point
ensures that all derivatives, including those at the endpoints, are two-sided derivatives. -/
theorem sub_sum_eq_integral_iteratedDeriv_sub {f : ℝ → ℝ} {n : ℕ} {h : ℝ}
    (hf : ∀ x ∈ uIcc 0 h, ContDiffAt ℝ (n + 1) f x) :
    f h - (∑ i ∈ Finset.range (n + 2), h ^ i / i.factorial * iteratedDeriv i f 0) =
      1 / (n.factorial : ℝ) * ∫ ξ in 0..h,
        (h - ξ) ^ n * (iteratedDeriv (n + 1) f ξ - iteratedDeriv (n + 1) f 0) := by
  by_cases hh : h = 0
  · subst h
    simp [Finset.sum_range_succ', pow_succ]
  have hne : (0 : ℝ) ≠ h := Ne.symm hh
  have hu : UniqueDiffOn ℝ (uIcc 0 h) := uniqueDiffOn_uIcc hne
  have hfOn : ContDiffOn ℝ (n + 1) f (uIcc 0 h) :=
    fun x hx => (hf x hx).contDiffWithinAt
  have ha : ContDiffAt ℝ n f 0 :=
    (hf 0 left_mem_uIcc).of_le (by exact_mod_cast Nat.le_succ n)
  have hderiv : ∀ x ∈ uIcc 0 h,
      iteratedDerivWithin (n + 1) f (uIcc 0 h) x = iteratedDeriv (n + 1) f x := by
    intro x hx
    exact iteratedDerivWithin_eq_iteratedDeriv hu (hf x hx) hx
  have hrem := taylor_integral_remainder hfOn
  rw [taylorWithinEval_eq_sum_of_contDiffAt hne ha] at hrem
  simp only [sub_zero] at hrem
  have hrem' : f h - (∑ i ∈ Finset.range (n + 1),
      h ^ i / i.factorial * iteratedDeriv i f 0) =
      ∫ ξ in 0..h, (h - ξ) ^ n / n.factorial * iteratedDeriv (n + 1) f ξ := by
    rw [hrem]
    apply intervalIntegral.integral_congr
    intro ξ hξ
    change ((h - ξ) ^ n / n.factorial) •
      iteratedDerivWithin (n + 1) f (uIcc 0 h) ξ = _
    rw [hderiv ξ hξ, smul_eq_mul]
  have hcont : ContinuousOn (iteratedDeriv (n + 1) f) (uIcc 0 h) := by
    apply (hfOn.continuousOn_iteratedDerivWithin (by rfl) hu).congr
    intro x hx
    exact (hderiv x hx).symm
  have hI1 : IntervalIntegrable (fun ξ =>
      (h - ξ) ^ n / n.factorial * iteratedDeriv (n + 1) f ξ)
      MeasureTheory.volume 0 h :=
    (ContinuousOn.mul (by fun_prop) hcont).intervalIntegrable
  have hI2 : IntervalIntegrable (fun ξ : ℝ =>
      (h - ξ) ^ n / n.factorial * iteratedDeriv (n + 1) f 0)
      MeasureTheory.volume 0 h := (by fun_prop : Continuous _).intervalIntegrable _ _
  have hkernel : ∫ ξ in 0..h, (h - ξ) ^ n = h ^ (n + 1) / (n + 1) := by
    rw [intervalIntegral.integral_comp_sub_left (fun ξ : ℝ => ξ ^ n) h]
    simp [integral_pow]
  have hconst : ∫ ξ in 0..h,
      (h - ξ) ^ n / n.factorial * iteratedDeriv (n + 1) f 0 =
      h ^ (n + 1) / (n + 1).factorial * iteratedDeriv (n + 1) f 0 := by
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_div, hkernel,
      Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, div_div]
  have hsplit : (fun ξ => (h - ξ) ^ n / n.factorial * iteratedDeriv (n + 1) f ξ -
      (h - ξ) ^ n / n.factorial * iteratedDeriv (n + 1) f 0) =
      (fun ξ => (1 / (n.factorial : ℝ)) *
        ((h - ξ) ^ n * (iteratedDeriv (n + 1) f ξ - iteratedDeriv (n + 1) f 0))) :=
    funext fun ξ => by ring
  rw [← intervalIntegral.integral_const_mul, ← hsplit,
    intervalIntegral.integral_sub hI1 hI2, hconst, ← hrem', Finset.sum_range_succ]
  ring
