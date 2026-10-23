import Numlib.Optimization.Newton.Sharpness

/-!
# Cartis–Gould–Toint, Section 3.1: slow Newton convergence

The lower bound is realized by a one-dimensional Hermite family with positive
Hessians at every iterate. It uses the actual Newton equation and strictly
decreasing objective values. The gradient Lipschitz constant, Hessian norm bound,
and objective budget are uniform before the accuracy is chosen. Every objective
also has a globally Lipschitz Hessian, with a constant allowed to depend on the
accuracy. This is an alternative witness for the source's existence theorem.
-/

namespace CartisGouldToint

/-- Algorithm 3.1.1: actual Newton steps with positive Hessians and the true
first-order stopping test. -/
abbrev newtonRun {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (f : E → ℝ) (x s : ℕ → E) (ε : ℝ) (N : ℕ) : Prop :=
  NewtonMinimization.Run f x s ε N

open NewtonMinimization NewtonMinimization.Sharpness in
/-- **Theorem 3.1.1.** Newton's method can require strictly more than
`ceil(ε⁻²)` function, gradient, and Hessian evaluations. The witness starts at
zero, decreases strictly at every step, and first satisfies the actual gradient
stopping test at the last point. Uniform objective and gradient Lipschitz bounds
precede every accuracy request. The Hessian is positive at all nonterminal nodes
and globally Lipschitz for each objective. Its evaluations are counted only when
the Newton gradient test fails, as in the source program. -/
theorem theorem_3_1_1 :
    ∃ H ≥ 1, ∃ G>0, ∀ ε : ℝ, 0<ε → ε ≤ 1 → ∃ f : ℝ → ℝ,
      ContDiff ℝ 2 f ∧ (∀ z, -G ≤ f z) ∧ f 0 - (-G) ≤ 2 * G ∧
      (∀ z, ‖SecondOrderTrustRegion.hessian f z‖ ≤ H) ∧
      (∀ z w, ‖gradient f z - gradient f w‖ ≤ H * ‖z - w‖) ∧
      (∃ L ≥ 1, ∀ z w,
        ‖iteratedFDeriv ℝ 2 f z - iteratedFDeriv ℝ 2 f w‖ ≤ L * ‖z - w‖) ∧
      newtonRun f (point ε) (fun _ => 2 * ε) ε (horizon ε) ∧ point ε 0 = 0 ∧
      (∀ k<horizon ε, f (point ε (k + 1))<f (point ε k)) ∧
      ‖gradient f (point ε (horizon ε))‖ ≤ ε ∧
      ⌈1 / ε ^ 2⌉₊ < horizon ε ∧
      ⌈1 / ε ^ 2⌉₊ < functionEvaluations (horizon ε) ∧
      ⌈1 / ε ^ 2⌉₊ < gradientEvaluations (horizon ε) ∧
      ⌈1 / ε ^ 2⌉₊ < hessianEvaluations (horizon ε) :=
  NewtonMinimization.Sharpness.exists_slow_newton_objective

end CartisGouldToint
