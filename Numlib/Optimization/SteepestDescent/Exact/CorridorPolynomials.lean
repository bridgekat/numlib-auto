import Numlib.Optimization.SteepestDescent.Exact.CorridorGrid
import Numlib.Approximation.Hermite.PolynomialPrefix

/-!
# Actual source corridor interval polynomials

The quintic smooth step controls the narrowing width and alternating center.
A separate quintic slope correction produces the prescribed scalar objective
jets. Scaling uses the actual positive finite grid interval length.
-/

open Polynomial Set
noncomputable section
namespace ExactSteepestDescent.Corridor

/-- The quintic endpoint-flat smooth step used by the source corridor walls. -/
def smoothStep : ℝ[X] := C 10 * X ^ 3 - C 15 * X ^ 4 + C 6 * X ^ 5

/-- The quintic source correction changing the scalar endpoint slope only. -/
def slopeCorrection : ℝ[X] := -C 4 * X ^ 3 + C 7 * X ^ 4 - C 3 * X ^ 5

/-- The actual polynomial width on a source interval, in translated coordinates. -/
def widthPolynomial (P : Parameters) (k : ℕ) : ℝ[X] :=
  C (amplitude P k) - C (widthIncrement P) *
    smoothStep.comp (C (amplitude P k)⁻¹ * X)

/-- The actual polynomial center on a source interval, in translated coordinates. -/
def centerPolynomial (P : Parameters) (k : ℕ) : ℝ[X] :=
  C (centerValue P k) + C ((-1 : ℝ) ^ k * widthIncrement P / 2) *
    smoothStep.comp (C (amplitude P k)⁻¹ * X)

/-- The actual scalar objective polynomial on a source interval. -/
def scalarPolynomial (P : Parameters) (k : ℕ) : ℝ[X] :=
  C (scalarValue P k) - C (amplitude P k) * X +
    C (amplitude P k * widthIncrement P) *
      slopeCorrection.comp (C (amplitude P k)⁻¹ * X)

/-- The width jets are a prescribed value and two zero derivatives. -/
def widthJet (P : Parameters) (k j : ℕ) : ℝ := if j = 0 then amplitude P k else 0

/-- The center jets are a prescribed value and two zero derivatives. -/
def centerJet (P : Parameters) (k j : ℕ) : ℝ := if j = 0 then centerValue P k else 0

/-- The scalar jets prescribe the objective value, negative width and zero Hessian. -/
def scalarJet (P : Parameters) (k j : ℕ) : ℝ :=
  if j = 0 then scalarValue P k else if j = 1 then -amplitude P k else 0

/-- Actual width-polynomial derivatives at the left endpoint match the source jets. -/
theorem widthPolynomial_left (P : Parameters) (k j : ℕ) (hj : j ≤ 2) :
    iteratedDeriv j (widthPolynomial P k).eval 0 = widthJet P k j := by
  rw [Polynomial.iteratedDeriv_eval]
  interval_cases j <;>
    norm_num [widthPolynomial, smoothStep, widthJet, Function.iterate_succ_apply',
      derivative_add, derivative_sub, derivative_mul, derivative_pow, derivative_C,
      derivative_X, add_comp, sub_comp, mul_comp, pow_comp]

/-- Actual center-polynomial derivatives at the left endpoint match the source jets. -/
theorem centerPolynomial_left (P : Parameters) (k j : ℕ) (hj : j ≤ 2) :
    iteratedDeriv j (centerPolynomial P k).eval 0 = centerJet P k j := by
  rw [Polynomial.iteratedDeriv_eval]
  interval_cases j <;>
    norm_num [centerPolynomial, smoothStep, centerJet, Function.iterate_succ_apply',
      derivative_add, derivative_sub, derivative_mul, derivative_pow, derivative_C,
      derivative_X, add_comp, sub_comp, mul_comp, pow_comp]

/-- Actual scalar-polynomial derivatives at the left endpoint match the source jets. -/
theorem scalarPolynomial_left (P : Parameters) (k j : ℕ) (hj : j ≤ 2) :
    iteratedDeriv j (scalarPolynomial P k).eval 0 = scalarJet P k j := by
  rw [Polynomial.iteratedDeriv_eval]
  interval_cases j <;>
    norm_num [scalarPolynomial, slopeCorrection, scalarJet, Function.iterate_succ_apply',
      derivative_add, derivative_sub, derivative_mul, derivative_pow, derivative_C,
      derivative_X, add_comp, sub_comp, mul_comp, pow_comp, neg_comp]

/-- Actual width-polynomial derivatives at the right endpoint match the next source jets. -/
theorem widthPolynomial_right (P : Parameters) {k : ℕ} (hk : k < P.horizon)
    (j : ℕ) (hj : j ≤ 2) :
    iteratedDeriv j (widthPolynomial P k).eval (amplitude P k) = widthJet P (k + 1) j := by
  have ha := (amplitude_pos P hk.le).ne'
  rw [Polynomial.iteratedDeriv_eval]
  interval_cases j <;>
    simp [widthPolynomial, smoothStep, widthJet, amplitude_succ,
      Function.iterate_succ_apply', derivative_add, derivative_sub, derivative_mul,
      derivative_pow, derivative_C, derivative_X, add_comp, sub_comp, mul_comp, pow_comp]
    <;> field_simp [ha]
  all_goals ring_nf
  all_goals simp_all

/-- Actual center-polynomial derivatives match the next alternating source center. -/
theorem centerPolynomial_right (P : Parameters) {k : ℕ} (hk : k < P.horizon)
    (j : ℕ) (hj : j ≤ 2) :
    iteratedDeriv j (centerPolynomial P k).eval (amplitude P k) = centerJet P (k + 1) j := by
  have ha := (amplitude_pos P hk.le).ne'
  rw [Polynomial.iteratedDeriv_eval]
  interval_cases j <;>
    simp [centerPolynomial, smoothStep, centerJet, centerValue_succ,
      Function.iterate_succ_apply', derivative_add, derivative_sub, derivative_mul,
      derivative_pow, derivative_C, derivative_X, add_comp, sub_comp, mul_comp, pow_comp]
    <;> field_simp [ha]
  all_goals ring_nf
  all_goals simp_all

/-- Actual scalar-polynomial derivatives match all three next source jets. -/
theorem scalarPolynomial_right (P : Parameters) {k : ℕ} (hk : k < P.horizon)
    (j : ℕ) (hj : j ≤ 2) :
    iteratedDeriv j (scalarPolynomial P k).eval (amplitude P k) = scalarJet P (k + 1) j := by
  have ha := (amplitude_pos P hk.le).ne'
  rw [Polynomial.iteratedDeriv_eval]
  interval_cases j <;>
    simp [scalarPolynomial, slopeCorrection, scalarJet, scalarValue_succ, amplitude_succ,
      Function.iterate_succ_apply', derivative_add, derivative_sub, derivative_mul,
      derivative_pow, derivative_C, derivative_X, add_comp, sub_comp, mul_comp, pow_comp,
      neg_comp]
    <;> field_simp [ha]
  all_goals ring_nf
  all_goals simp_all


/-- The actual width polynomial has the degree required for quintic uniqueness. -/
theorem widthPolynomial_degree (P : Parameters) (k : ℕ) :
    (widthPolynomial P k).degree < (6 : WithBot ℕ) := by
  unfold widthPolynomial smoothStep
  simp only [sub_comp, add_comp, mul_comp, pow_comp, C_comp, X_comp]
  compute_degree!

/-- The actual center polynomial has the degree required for quintic uniqueness. -/
theorem centerPolynomial_degree (P : Parameters) (k : ℕ) :
    (centerPolynomial P k).degree < (6 : WithBot ℕ) := by
  unfold centerPolynomial smoothStep
  simp only [sub_comp, add_comp, mul_comp, pow_comp, C_comp, X_comp]
  compute_degree!

/-- The actual scalar polynomial has the degree required for quintic uniqueness. -/
theorem scalarPolynomial_degree (P : Parameters) (k : ℕ) :
    (scalarPolynomial P k).degree < (6 : WithBot ℕ) := by
  unfold scalarPolynomial slopeCorrection
  simp only [sub_comp, add_comp, mul_comp, pow_comp, neg_comp, C_comp, X_comp]
  compute_degree!

/-- Genuine endpoint jets identify the source width polynomial with the
canonical Hermite interpolant, without assuming the interpolation identity. -/
theorem widthPolynomial_eq_endpoint (P : Parameters) {k : ℕ} (hk : k < P.horizon) :
    widthPolynomial P k = Hermite.endpointPolynomial 2 (amplitude P k)
      (widthJet P k) (widthJet P (k + 1)) := by
  apply Hermite.endpointPolynomial_eq_of_jets (amplitude_pos P hk.le).ne'
    (widthJet P k) (widthJet P (k + 1)) (widthPolynomial_degree P k)
  · intro j hj
    simpa only [Polynomial.iteratedDeriv_eval] using widthPolynomial_left P k j hj
  · intro j hj
    simpa only [Polynomial.iteratedDeriv_eval] using widthPolynomial_right P hk j hj

/-- Genuine endpoint jets identify the alternating center polynomial with the
canonical Hermite interpolant. -/
theorem centerPolynomial_eq_endpoint (P : Parameters) {k : ℕ} (hk : k < P.horizon) :
    centerPolynomial P k = Hermite.endpointPolynomial 2 (amplitude P k)
      (centerJet P k) (centerJet P (k + 1)) := by
  apply Hermite.endpointPolynomial_eq_of_jets (amplitude_pos P hk.le).ne'
    (centerJet P k) (centerJet P (k + 1)) (centerPolynomial_degree P k)
  · intro j hj
    simpa only [Polynomial.iteratedDeriv_eval] using centerPolynomial_left P k j hj
  · intro j hj
    simpa only [Polynomial.iteratedDeriv_eval] using centerPolynomial_right P hk j hj

/-- Genuine endpoint jets identify the scalar objective polynomial with the
canonical Hermite interpolant. -/
theorem scalarPolynomial_eq_endpoint (P : Parameters) {k : ℕ} (hk : k < P.horizon) :
    scalarPolynomial P k = Hermite.endpointPolynomial 2 (amplitude P k)
      (scalarJet P k) (scalarJet P (k + 1)) := by
  apply Hermite.endpointPolynomial_eq_of_jets (amplitude_pos P hk.le).ne'
    (scalarJet P k) (scalarJet P (k + 1)) (scalarPolynomial_degree P k)
  · intro j hj
    simpa only [Polynomial.iteratedDeriv_eval] using scalarPolynomial_left P k j hj
  · intro j hj
    simpa only [Polynomial.iteratedDeriv_eval] using scalarPolynomial_right P hk j hj

end ExactSteepestDescent.Corridor
