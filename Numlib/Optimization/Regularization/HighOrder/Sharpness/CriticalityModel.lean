import Numlib.Optimization.Regularization.HighOrder.Sharpness.Model
import Numlib.Optimization.Regularization.Monomial

/-!
# Actual global monomial models for high-order sharpness

The prescribed actual jets give a balanced monomial model. Weighted powers
prove that its chosen step is a genuine global minimum for every order, without
assuming stationary points are global minima. Low-order criticality checks at
global model minima admit literal unit radii and no reduction steps.
-/

namespace HighOrderRegularization.Sharpness
open Polynomial

/-- The actual regularized model of the uniform Hermite construction is an
exact balanced monomial on both positive and negative trials. -/
theorem model_eq_balanced {f : ℝ → ℝ} {p r N k : ℕ} {t : ℝ}
    (hr : 0 < r) (hrp : r ≤ p) (h : MatchesJets f p r N (amplitude p r) t)
    (hk : k < N) (u : ℝ) :
    HighOrderRegularization.model f p (point t k) (parameter p) u =
      jet p r N (amplitude p r) t k 0 + coefficient p *
        (|u| ^ (p + 1) / (p + 1 : ℕ) - t ^ (p - r + 1) * u ^ r / r) := by
  rw [HighOrderRegularization.model_eq, eval_of_matches h hk.le,
    initialPolynomial_eq hr hrp hk]
  simp only [eval_sub, eval_C, eval_mul, eval_pow, eval_X, Real.norm_eq_abs]
  have ha := amplitude_div_factorial hr p
  have hp : parameter p / ((p + 1).factorial : ℝ) = coefficient p / (p + 1 : ℕ) := by
    rw [parameter, Nat.factorial_succ, Nat.cast_mul]
    field_simp
  rw [hp]
  have hat : amplitude p r * t ^ balance p r / (r.factorial : ℝ) =
      (coefficient p / r) * t ^ (p - r + 1) := by
    rw [← ha]
    unfold balance
    ring
  rw [hat]
  ring

/-- The actual chosen monomial step globally minimizes every nonterminal model
in the uniform Hermite lower-bound family, for arbitrary criticality order. -/
theorem model_global_min {f : ℝ → ℝ} {p r N k : ℕ} {t : ℝ}
    (hr : 0 < r) (hrp : r ≤ p) (h : MatchesJets f p r N (amplitude p r) t)
    (hk : k < N) (ht : 0 ≤ t) (u : ℝ) :
    HighOrderRegularization.model f p (point t k) (parameter p) t ≤
      HighOrderRegularization.model f p (point t k) (parameter p) u := by
  rw [model_eq_balanced hr hrp h hk, model_eq_balanced hr hrp h hk]
  exact MonomialRegularization.global_min hr hrp ht (coefficient_pos p).le u

end HighOrderRegularization.Sharpness
