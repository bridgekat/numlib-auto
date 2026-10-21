import NumlibSurface.CartisGouldToint.Chapter13.Section01.ARqpIDA
import Numlib.Optimization.InexactTaylorModelDerivatives
import NumlibSurface.CartisGouldToint.Chapter12.Section02

/-!
# Chapter 13, Section 1: genuine shifted approximate model gaps

The finite supplied tensors determine the actual derivatives and Taylor gaps of their
regularized polynomial. Equations (13.1.49) and (13.1.50) therefore apply without assuming
that the approximate tensors are the derivatives of a surrogate objective. The step-power
estimate explicitly requires accuracy through order `p`, as (13.1.46) does. The literal
Algorithm 13.1.2 check through order `q` cannot supply this when `q<p`.
-/

noncomputable section
open scoped Nat
namespace CartisGouldToint.Chapter13.Section01
open Optimization InexactRegularization InexactTaylorModels TaylorCriticality

variable {n : ℕ}

/-- Exact tensors recover the earlier source regularized Taylor model. -/
theorem inexactRegularizedModel_exact (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (p : ℕ) (x : EuclideanSpace ℝ (Fin n)) (σ : ℝ) :
    inexactRegularizedModel (f x) (fun i => iteratedFDeriv ℝ i f x) p σ =
      Chapter12.Section02.regularizedTaylorModel f p x σ := by
  rw [Chapter12.Section02.regularizedTaylorModel_eq_model]
  funext s
  change regularizedPolynomial (f x) (fun i => iteratedFDeriv ℝ i f x) p σ s =
    HigherOrderRegularization.model f p x σ s
  rw [regularizedPolynomial, polynomial_iteratedFDeriv]
  unfold HigherOrderRegularization.model
  ring

/-- Equation (13.1.49) for genuine shifted model gaps. Every supplied order through `p`
meets (13.1.46); on a short step this follows from the separately named all-`p` check.
The literal `q` check is insufficient when `q<p`, as witnessed by
`InexactRegularization.exists_stepAccurate_not_all_orders`. -/
theorem arqpida_allp_shifted_model_gap_error {P : ARqpIDAParameters}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (O : ImplicitAccuracyOracle f P.p)
    (x s : EuclideanSpace ℝ (Fin n)) (h : ℕ → ℝ) {σ K δ : ℝ}
    (hK : 0 ≤ K) (hδ : 0 ≤ δ) (hs : ‖s‖ < 1)
    (haccurate : StepAccurate P P.p h s)
    (hcoeff : ∀ i ∈ Finset.Icc 1 P.p,
      ‖O.derivative x h i - iteratedFDeriv ℝ i f x‖ ≤ K * h i)
    {j : ℕ} (hjp : j ≤ P.p) :
    |Chapter12.Section01.taylorCriticality
        (inexactRegularizedModel (f x) (O.derivative x h) P.p σ) j δ s -
      Chapter12.Section01.taylorCriticality
        (Chapter12.Section02.regularizedTaylorModel f P.p x σ) j δ s| ≤
      3 * K * P.kappaStep * ∑ l ∈ Finset.Icc 1 j,
        δ ^ l * ‖s‖ ^ (P.p - l + 1) / (l ! : ℝ) := by
  have herr : ∀ i ∈ Finset.Icc 1 P.p,
      ‖O.derivative x h i - iteratedFDeriv ℝ i f x‖ ≤
        K * P.kappaStep * ‖s‖ ^ (P.p - i + 1) := by
    intro i hi
    have ha := (StepAccurate.short_iff hs).mp haccurate i hi
    exact (hcoeff i hi).trans (by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left ha hK)
  have hb := regularizedPolynomial_gap_error_le_step_power hjp (f x) (f x)
    (O.derivative x h) (fun i => iteratedFDeriv ℝ i f x) σ s hK P.kappaStep_pos.le hδ herr
  rw [← inexactRegularizedModel_exact f P.p x σ]
  simpa only [Chapter12.Section01.taylorCriticality, Chapter12.Section01.taylorDecrement] using hb

/-- When `p=q`, the literal short-step check covers every model coefficient and gives
the same shifted-gap estimate. Equality of the two degrees is explicit. -/
theorem arqpida_literal_shifted_model_gap_error_of_degree_eq {P : ARqpIDAParameters}
    (hpq : P.p = P.q) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (O : ImplicitAccuracyOracle f P.p) (x s : EuclideanSpace ℝ (Fin n))
    (h : ℕ → ℝ) {σ K δ : ℝ} (hK : 0 ≤ K) (hδ : 0 ≤ δ) (hs : ‖s‖ < 1)
    (haccurate : StepAccurate P P.q h s)
    (hcoeff : ∀ i ∈ Finset.Icc 1 P.p,
      ‖O.derivative x h i - iteratedFDeriv ℝ i f x‖ ≤ K * h i)
    {j : ℕ} (hjp : j ≤ P.p) :
    |Chapter12.Section01.taylorCriticality
        (inexactRegularizedModel (f x) (O.derivative x h) P.p σ) j δ s -
      Chapter12.Section01.taylorCriticality
        (Chapter12.Section02.regularizedTaylorModel f P.p x σ) j δ s| ≤
      3 * K * P.kappaStep * ∑ l ∈ Finset.Icc 1 j,
        δ ^ l * ‖s‖ ^ (P.p - l + 1) / (l ! : ℝ) := by
  exact arqpida_allp_shifted_model_gap_error f O x s h hK hδ hs
    (by simpa only [hpq] using haccurate) hcoeff hjp

/-- Equation (13.1.50): uniform requested accuracy controls the genuine shifted model
gaps on the unit ball. No step-dependent accuracy check is used in this estimate. -/
theorem arqpida_shifted_model_gap_error_uniform {P : ARqpIDAParameters}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (O : ImplicitAccuracyOracle f P.p)
    (x s : EuclideanSpace ℝ (Fin n)) (h : ℕ → ℝ) {σ K H δ : ℝ}
    (hK : 0 ≤ K) (hH : 0 ≤ H) (hδ : δ ∈ Set.Icc (0 : ℝ) 1) (hs : ‖s‖ ≤ 1)
    (hh : ∀ i ∈ Finset.Icc 1 P.p, h i ≤ H)
    (hcoeff : ∀ i ∈ Finset.Icc 1 P.p,
      ‖O.derivative x h i - iteratedFDeriv ℝ i f x‖ ≤ K * h i)
    {j : ℕ} (hjp : j ≤ P.p) :
    |Chapter12.Section01.taylorCriticality
        (inexactRegularizedModel (f x) (O.derivative x h) P.p σ) j δ s -
      Chapter12.Section01.taylorCriticality
        (Chapter12.Section02.regularizedTaylorModel f P.p x σ) j δ s| ≤ 6 * K * H := by
  have hb := regularizedPolynomial_gap_error_le_uniform hjp (f x) (f x)
    (O.derivative x h) (fun i => iteratedFDeriv ℝ i f x) σ s (mul_nonneg hK hH) hs hδ
    (fun i hi => (hcoeff i hi).trans (mul_le_mul_of_nonneg_left (hh i hi) hK))
  rw [← inexactRegularizedModel_exact f P.p x σ]
  simpa only [Chapter12.Section01.taylorCriticality, Chapter12.Section01.taylorDecrement,
    mul_assoc] using hb

end CartisGouldToint.Chapter13.Section01
