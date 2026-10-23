import Numlib.Optimization.Sharpness.Curvature
import Numlib.Approximation.Hermite.Endpoint

/-!
# Uniform Hermite interpolation data for curvature sharpness

The exact scalar Taylor polynomial in the execution construction is the canonical
initial Hermite polynomial. This identifies the genuine polynomial-derivative residuals
used for global interpolation, with a single constant before all accuracy requests.
-/

namespace CurvatureSharpness

/-- The initial Hermite polynomial evaluates to the actual finite Taylor sum. -/
theorem initialPolynomial_eval_eq (ε t : ℝ) (N i : ℕ) :
    (Hermite.initialPolynomial 2 (jet ε t N i)).eval = initialTaylor ε t N i := by
  funext s
  exact Hermite.initialPolynomial_eval 2 (jet ε t N i) s

/-- Polynomial derivatives of the initial Hermite interpolant are exactly the actual
scalar derivatives of the prescribed Taylor function. -/
theorem initialPolynomial_derivative_eq (ε t : ℝ) (N i j : ℕ) (s : ℝ) :
    (Polynomial.derivative^[j] (Hermite.initialPolynomial 2 (jet ε t N i))).eval s =
      iteratedDeriv j (initialTaylor ε t N i) s := by
  have he := congrFun (Polynomial.iteratedDeriv_eval
    (Hermite.initialPolynomial 2 (jet ε t N i)) j) s
  rw [initialPolynomial_eval_eq] at he
  exact he.symm

/-- The difference of consecutive grid points is precisely the positive step length. -/
theorem grid_succ_sub (t : ℝ) (i : ℕ) : grid t (i + 1) - grid t i = t := by
  simp only [grid, Nat.cast_add, Nat.cast_one]
  ring

/-- All hypotheses for global Hermite interpolation hold with the fixed constant two.
Neither the interval count nor the accuracy occurs in this constant. -/
theorem uniform_Hermite_data {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    0 < horizon ε ∧
      (∀ i j : ℕ, i < j → j ≤ horizon ε → grid ε i < grid ε j) ∧
      (∀ k < horizon ε, grid ε (k + 1) - grid ε k ≤ 2) ∧
      (∀ k < horizon ε, ∀ j ≤ 2, |jet ε ε (horizon ε) k j| ≤ 2) ∧
      (∀ k < horizon ε, ∀ j ≤ 2,
        |jet ε ε (horizon ε) (k + 1) j -
          (Polynomial.derivative^[j]
            (Hermite.initialPolynomial 2 (jet ε ε (horizon ε) k))).eval
              (grid ε (k + 1) - grid ε k)| ≤
            2 * (grid ε (k + 1) - grid ε k) ^ (2 - j + 1)) := by
  obtain ⟨hN, hmono, hjets, hres⟩ := unit_step_uniform_bounds hε hε1
  refine ⟨hN, fun _ _ hij _ => hmono hij, ?_, ?_, ?_⟩
  · intro k hk
    rw [grid_succ_sub]
    linarith
  · intro k hk j hj
    exact hjets k hk.le j hj
  · intro k hk j hj
    rw [grid_succ_sub, initialPolynomial_derivative_eq]
    exact hres k hk j hj

end CurvatureSharpness
