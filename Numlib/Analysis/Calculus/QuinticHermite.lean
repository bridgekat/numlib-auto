import Numlib.Analysis.Calculus.HermiteInterpolationBounds
import Mathlib.Tactic.IntervalCases

/-!
# Explicit quintic Hermite interpolation

The six coefficients match actual value, first derivative and second derivative at both ends
of the unit interval. Residuals measure only the correction to the left quadratic Taylor
polynomial; bounding them does not control the initial jet.
-/

noncomputable section
open Polynomial

namespace Hermite

/-- Right endpoint discrepancies against the left quadratic Taylor polynomial. -/
def quinticResidual (a b : ℕ → ℝ) : ℕ → ℝ
  | 0 => b 0 - a 0 - a 1 - a 2 / 2
  | 1 => b 1 - a 1 - a 2
  | 2 => b 2 - a 2
  | _ => 0

/-- The six explicit coefficients, with zero extension beyond degree five. -/
def quinticCoefficient (a b : ℕ → ℝ) : ℕ → ℝ
  | 0 => a 0
  | 1 => a 1
  | 2 => a 2 / 2
  | 3 => 10 * quinticResidual a b 0 - 4 * quinticResidual a b 1 + quinticResidual a b 2 / 2
  | 4 => -15 * quinticResidual a b 0 + 7 * quinticResidual a b 1 - quinticResidual a b 2
  | 5 => 6 * quinticResidual a b 0 - 3 * quinticResidual a b 1 + quinticResidual a b 2 / 2
  | _ => 0

/-- The actual six-term polynomial. -/
def quinticPolynomial (a b : ℕ → ℝ) : ℝ[X] :=
  ∑ i ∈ Finset.range 6, quinticCoefficient a b i • (X : ℝ[X]) ^ i

/-- The finite monomial sum has degree at most five, also for degenerate data. -/
theorem natDegree_quinticPolynomial_le (a b : ℕ → ℝ) :
    (quinticPolynomial a b).natDegree ≤ 5 := by
  apply natDegree_sum_le_of_forall_le
  intro i hi
  exact (natDegree_smul_le _ _).trans (by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hi))

/-- The six actual polynomial coefficients are the explicit formulas. Together with the
degree bound this characterizes every coefficient. -/
@[simp] theorem coeff_quinticPolynomial (a b : ℕ → ℝ) {i : ℕ} (hi : i < 6) :
    (quinticPolynomial a b).coeff i = quinticCoefficient a b i := by
  interval_cases i <;> simp [quinticPolynomial, Finset.sum_range_succ, coeff_one, coeff_X]

/-- The actual derivative jets of the polynomial match at both endpoints. -/
theorem iteratedDeriv_quinticPolynomial_endpoints (a b : ℕ → ℝ) {j : ℕ} (hj : j ≤ 2) :
    iteratedDeriv j (fun t => (quinticPolynomial a b).eval t) 0 = a j ∧
      iteratedDeriv j (fun t => (quinticPolynomial a b).eval t) 1 = b j := by
  simp only [Polynomial.iteratedDeriv_eval]
  interval_cases j <;> constructor <;>
    norm_num [quinticPolynomial, Finset.sum_range_succ, quinticCoefficient, quinticResidual,
      Function.iterate_succ_apply', derivative_pow] <;> ring

/-- Residuals agree with the generic Hermite interpolation discrepancy. -/
theorem quinticResidual_eq_endpointTaylor_discrepancy (a b : ℕ → ℝ)
    {j : ℕ} (hj : j ≤ 2) : quinticResidual a b j =
      b j - (derivative^[j] (endpointTaylor 2 a)).eval 1 := by
  interval_cases j <;>
    norm_num [quinticResidual, endpointTaylor, jetPoly, Finset.sum_range_succ,
      Function.iterate_succ_apply', derivative_pow] <;> ring

end Hermite
