import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Traces restricted to descent directions

The next point may be unchanged or lie along a direction whose actual directional
derivative is negative. This primitive restriction is weaker than any additional
step-length or acceptance rule. It already prevents escape from a stationary point.
-/

namespace LineSearch
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
/-- A trace that either stays in place or moves along a direction with a negative
actual directional derivative. -/
def DescentTrace (f : E → ℝ) (x : ℕ → E) : Prop :=
  ∀ k, x (k + 1) = x k ∨ ∃ (v : E) (t : ℝ),
    deriv (fun a : ℝ => f (x k + a • v)) 0 < 0 ∧ x (k + 1) = x k + t • v
/-- Staying at the initial point is a permitted trace, so the primitive trace class is nonempty. -/
theorem descentTrace_const (f : E → ℝ) (x : E) : DescentTrace f (fun _ => x) :=
  fun _ => Or.inl rfl

/-- No trace using descent directions can leave a point whose directional derivatives vanish. -/
theorem DescentTrace.eq_initial {f : E → ℝ} {x : ℕ → E} (hx : DescentTrace f x)
    (hzero : ∀ v, deriv (fun a : ℝ => f (x 0 + a • v)) 0 = 0) (k : ℕ) :
    x k = x 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rcases hx k with hstay | ⟨v, t, hv, _⟩
    · exact hstay.trans ih
    · rw [ih, hzero v] at hv
      exact (lt_irrefl 0 hv).elim
end LineSearch
