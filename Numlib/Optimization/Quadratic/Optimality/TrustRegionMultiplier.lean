import Numlib.Optimization.Quadratic.Optimality.TrustRegion
import Mathlib.Tactic
/-!
# The actual multiplier at a true trust-region minimizer

A nonzero right side makes the stationary scalar shift unique. It is therefore
the nonnegative, complementary multiplier supplied by global minimality.
-/

namespace QuadraticOptimality
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
/-- The actual stationary shift at a nontrivial true trust-region minimizer is its
nonnegative complementary multiplier, with a positive-semidefinite shifted operator. -/
theorem trust_region_stationary_shift {A : E →L[ℝ] E} (hA : A.toLinearMap.IsSymmetric)
    {g : E} (hg : g ≠ 0) (x : E) {Δ : ℝ} (hΔ : 0 < Δ) (hx : ‖x‖ ≤ Δ)
    (hmin : ∀ z, ‖z‖ ≤ Δ → model A g x ≤ model A g z)
    {τ : ℝ} (hsolve : A x + τ • x = -g) :
    0 ≤ τ ∧ (∀ v, 0 ≤ inner ℝ ((A + τ • ContinuousLinearMap.id ℝ E) v) v) ∧
      τ * (‖x‖ ^ 2 - Δ ^ 2) = 0 := by
  obtain ⟨μ, hμ, hs, hPSD, hcomp⟩ := necessary_trust_region hA g x hΔ hx hmin
  have hx0 : x ≠ 0 := by
    intro he
    rw [he, map_zero, smul_zero, add_zero] at hsolve
    exact hg (neg_eq_zero.mp hsolve.symm)
  have hs' : A x + μ • x = -g := by
    calc _ = (g + A x) + μ • x - g := by abel
      _ = -g := by rw [hs]; simp
  have ht : τ = μ := smul_left_injective ℝ hx0 (add_left_cancel (hsolve.trans hs'.symm))
  subst τ
  exact ⟨hμ, hPSD, hcomp⟩
end QuadraticOptimality
