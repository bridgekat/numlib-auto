import Numlib.Analysis.Calculus.NormPowerBounds

/-!
# Factorial quotient bounds for norm-power derivatives

The sharp falling-factorial estimate has an equivalent ordinary factorial quotient form.
-/

noncomputable section
open scoped Nat

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {p j : ℕ}

/-- The full falling-factorial radial estimate in factorial quotient form. -/
theorem norm_iteratedFDeriv_norm_pow_le_factorial (hj : j ≤ p) (s : E) :
    ‖iteratedFDeriv ℝ j (fun z : E => ‖z‖ ^ (p + 1)) s‖ ≤
      ((p + 1)! : ℝ) / ((p - j + 1)! : ℝ) * ‖s‖ ^ (p - j + 1) := by
  have hf : ((p - j + 1)! : ℝ) * (Nat.descFactorial (p + 1) j : ℝ) =
      ((p + 1)! : ℝ) := by
    have h := Nat.factorial_mul_descFactorial (by omega : j ≤ p + 1)
    rw [show p + 1 - j = p - j + 1 by omega] at h
    exact_mod_cast h
  have he : (Nat.descFactorial (p + 1) j : ℝ) =
      ((p + 1)! : ℝ) / ((p - j + 1)! : ℝ) := by
    apply (eq_div_iff (by positivity)).mpr
    nlinarith only [hf]
  simpa only [he, show p + 1 - j = p - j + 1 by omega] using
    norm_iteratedFDeriv_norm_pow_le_of_le hj s
