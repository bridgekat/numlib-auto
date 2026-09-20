/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas`, beside `deriv_comp_add_const`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# The derivatives of a periodic function are periodic

`Function.Periodic.deriv` and `Function.Periodic.iteratedDeriv`: for `f : ℝ → F` periodic with
period `T`, so are `deriv f` and every `iteratedDeriv n f`, by `deriv_comp_add_const`. Mathlib has
no periodicity lemma for `deriv`.
-/

namespace Function.Periodic

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The derivative of a periodic function is periodic. -/
theorem deriv {f : ℝ → F} {T : ℝ} (h : Function.Periodic f T) :
    Function.Periodic (_root_.deriv f) T := by
  intro x
  have hfun : (fun y => f (y + T)) = f := funext h
  have := deriv_comp_add_const f T x
  rw [hfun] at this
  exact this.symm

/-- Every iterated derivative of a periodic function is periodic. -/
theorem iteratedDeriv {f : ℝ → F} {T : ℝ} (h : Function.Periodic f T) (n : ℕ) :
    Function.Periodic (_root_.iteratedDeriv n f) T := by
  induction n with
  | zero => simpa using h
  | succ n ih => rw [iteratedDeriv_succ]; exact ih.deriv

end Function.Periodic
