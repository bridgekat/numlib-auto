import Numlib.Optimization.Regularization.Inexact.Explicit.Run

/-!
# Initial-radius alternatives for actual ordered checks

If no initial computed test fails, every radius loop accepts its first candidate.
Thus all radii are unchanged and the ordered check passes every order. This
alternative separates genuine model failure from explicit accuracy failure.
-/

namespace InexactRegularization
open InexactTrustRegion
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- An actual sequential check either fails a computed test at an inherited
radius or passes every test without any radius reductions. -/
theorem StepOneComputation.initial_alternative {q p : ℕ}
    {A : FormalMultilinearSeries ℝ E ℝ} {σ ζ : ℝ}
    {ε initial reduced : Fin q → ℝ} {reference : E}
    {direction : Fin q → ℕ → E} {count : Fin q → ℕ} {selected : Option (Fin q)}
    (h : StepOneComputation A p σ ζ ε initial reduced reference direction count selected) :
    (∃ a, ζ / 2 * ε a * initial a ^ modelOrder a / (modelOrder a).factorial <
      TaylorModel.jetDecrement A (modelOrder a) (direction a 0)) ∨
    (selected = none ∧ (∀ a, count a = 0) ∧ reduced = initial) := by
  classical
  by_cases hbad : ∃ a, ζ / 2 * ε a * initial a ^ modelOrder a /
      (modelOrder a).factorial < TaylorModel.jetDecrement A (modelOrder a) (direction a 0)
  · exact Or.inl hbad
  · right
    have hpass : ∀ a, TaylorModel.jetDecrement A (modelOrder a) (direction a 0) ≤
        ζ / 2 * ε a * initial a ^ modelOrder a / (modelOrder a).factorial := by
      simpa only [not_exists, not_lt] using hbad
    have hcount : ∀ a, count a = 0 := by
      intro a
      by_contra ha
      have hreject := h.rejected a 0 (Nat.pos_of_ne_zero ha)
      apply hreject
      left
      simpa only [BacktrackingGradient.step, pow_zero, div_one] using hpass a
    have hradius : reduced = initial := by
      funext a
      rw [h.radius_eq a, hcount a]
      simp only [BacktrackingGradient.step, pow_zero, div_one]
    refine ⟨?_, hcount, hradius⟩
    cases hs : selected with
    | none => rfl
    | some a =>
      have hout := h.outcome
      rw [hs] at hout
      have hfail := hout.2.1
      rw [hout.1, hcount a, hradius] at hfail
      exact (not_lt_of_ge (hpass a) hfail).elim

end InexactRegularization
