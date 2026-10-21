import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# Full-step Newton runs

The iteration solves the genuine Hessian linear system in the dual space and accepts the
full step. Finite runs record failed gradient tests and the first successful stopping test.
Separate oracles are counted separately: the method does not query objective values.
-/

noncomputable section
namespace Optimization.Newton

/-- A finite full-step Newton run, including its first successful gradient test. The Hessian
linear system is expressed in the dual space, without choosing a total inverse. -/
structure IsRun {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) (ε : ℝ) (x s : ℕ → E) (N : ℕ) : Prop where
  active : ∀ k < N, ε < ‖gradient f (x k)‖
  terminal : ‖gradient f (x N)‖ ≤ ε
  equation : ∀ k < N, ∀ u, fderiv ℝ (fderiv ℝ f) (x k) (s k) u = -fderiv ℝ f (x k) u
  iterate : ∀ k < N, x (k + 1) = x k + s k

/-- The method queries the gradient at every iterate, including its terminal test. -/
def gradientEvaluations (N : ℕ) : ℕ := N + 1

/-- The method queries the Hessian once for each computed step, before the terminal test. -/
def hessianEvaluations (N : ℕ) : ℕ := N

/-- The full-step method has no objective-value oracle calls. -/
def functionEvaluations (_N : ℕ) : ℕ := 0

end Optimization.Newton
