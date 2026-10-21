import Numlib.Optimization.KrylovSubproblemMonotonicity

/-!
# Secular brackets from actual Lanczos solves

Comparing an actual trial shifted solution with the actual stationary radial solution
certifies which side of its multiplier the trial lies on. The argument uses the
proved inverse-norm monotonicity, with no assumed root or residual certificate.
-/

noncomputable section
namespace Optimization.KrylovSubproblem
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The norm of an actual positive definite Lanczos solve certifies a radial secular
bracket. Both stationary systems and both shifts are actual algebraic systems. -/
theorem lanczos_regularization_shift_bracket (A : E →ₗ[ℝ] E) (g : E)
    {m : ℕ} {sigma r lambda : ℝ} (hsigma : 0 ≤ sigma) (hr : 2 < r)
    {x y : EuclideanSpace ℝ (Fin (m + 1))}
    (hx : ∀ i, (Lanczos.tridiag A g (m + 1)).mulVec x i + lambda * x i =
      -(if i = 0 then ‖g‖ else 0))
    (hy : ∀ i, (Lanczos.tridiag A g (m + 1)).mulVec y i +
      (sigma * ‖y‖ ^ (r - 2)) * y i = -(if i = 0 then ‖g‖ else 0))
    (hpx : (Lanczos.tridiag A g (m + 1) + lambda • 1).PosDef)
    (hpy : (Lanczos.tridiag A g (m + 1) + (sigma * ‖y‖ ^ (r - 2)) • 1).PosDef) :
    (lambda < sigma * ‖x‖ ^ (r - 2) → lambda < sigma * ‖y‖ ^ (r - 2)) ∧
      (sigma * ‖x‖ ^ (r - 2) < lambda → sigma * ‖y‖ ^ (r - 2) < lambda) := by
  constructor
  · intro htest
    by_contra h
    have hn := lanczos_stationary_norm_le_of_shift_le A g le_rfl (le_of_not_gt h)
      hx hy hpx hpy
    exact (not_lt_of_ge ((mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (norm_nonneg _) hn (by linarith)) hsigma).trans
        (le_of_not_gt h))) htest
  · intro htest
    by_contra h
    have hn := lanczos_stationary_norm_le_of_shift_le A g le_rfl (le_of_not_gt h)
      hy hx hpy hpx
    exact (not_lt_of_ge ((le_of_not_gt h).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (norm_nonneg _) hn (by linarith)) hsigma))) htest

end Optimization.KrylovSubproblem
