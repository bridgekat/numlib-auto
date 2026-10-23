import Numlib.Analysis.Calculus.TaylorModel
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Scalar Taylor coefficients

The actual multilinear Taylor model on the real line is the usual finite
polynomial in actual scalar iterated derivatives, with factorial normalization.
-/

namespace TaylorModel

/-- Scalar Taylor evaluation uses the actual scalar derivative coefficients. -/
theorem eval_eq_sum_iteratedDeriv (f : ℝ → ℝ) (p : ℕ) (x t : ℝ) :
    eval f p x t = ∑ i ∈ Finset.range (p + 1),
      t ^ i * iteratedDeriv i f x / i.factorial := by
  rw [eval_eq_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod]
  simp [smul_eq_mul, div_eq_mul_inv, mul_comm]

end TaylorModel
