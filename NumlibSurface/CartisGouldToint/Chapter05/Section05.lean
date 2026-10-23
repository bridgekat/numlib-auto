import Numlib.Optimization.Regularization.Universal.Run

/-!
# Universal regularization with real powers

The source finite factorial and actual model tests are retained. Optional
second-order accuracy disables its derivative test explicitly. Trial-point
stopping is checked before acceptance, and the parameter has no added floor.
The final row of the printed update table is read using the surrounding prose:
failure of either the ratio or a length test increases the parameter.
-/
namespace CartisGouldToint
/-- Algorithm5.5.1: a genuine prefix before trial-point termination. -/
abbrev universalArpRun {n p : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (P : UniversalRegularization.Settings p) (ε1 : ℝ) (ε2 : Option ℝ)
    (D : UniversalRegularization.Data (EuclideanSpace ℝ (Fin n))) (N : ℕ) : Prop :=
  UniversalRegularization.Run f P ε1 ε2 D N

/-- **Lemma5.5.1.** Every actual computed model step gives the stated Taylor
prediction decrease, with the finite factorial of its real power. This holds
also for the terminal trial, which is checked before acceptance. -/
theorem lemma_5_5_1 {n p : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {P : UniversalRegularization.Settings p} {ε2 : Option ℝ}
    {x s : EuclideanSpace ℝ (Fin n)} {σ : ℝ}
    (h : UniversalRegularization.Step f P ε2 x s σ) :
    σ / Real.finiteFactorial P.r * ‖s‖ ^ P.r ≤
      f x - TaylorModel.eval f p x s := h.taylor_decrease.le
end CartisGouldToint
