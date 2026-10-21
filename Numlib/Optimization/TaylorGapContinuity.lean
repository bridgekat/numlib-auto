import Numlib.Optimization.TaylorOptimality

/-!
# Continuity of Taylor optimality gaps

Smooth dependence of the Taylor coefficients makes the decrement jointly continuous in
its expansion point and displacement. Maximizing over a fixed compact displacement ball
preserves continuity in the expansion point.
-/

open scoped Nat
open Set Metric
namespace Optimization.TaylorCriticality
open RegularizedTaylorModel
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A smooth function's Taylor model is jointly continuous in its base point and displacement. -/
theorem continuous_taylorModel_joint {f : E → ℝ} {p : ℕ} (hf : ContDiff ℝ p f) :
    Continuous (fun z : E × E => taylorModel f p z.1 z.2) := by
  unfold taylorModel
  apply continuous_finsetSum
  intro i hi
  have hi' : (i : WithTop ℕ∞) ≤ p := by
    exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  exact (continuous_const : Continuous (fun _ : E × E => ((i ! : ℝ)⁻¹))).smul
    (((hf.continuous_iteratedFDeriv hi').comp continuous_fst).eval
      (continuous_pi fun _ => continuous_snd))

/-- Taylor decrements are jointly continuous when their coefficients vary continuously. -/
theorem continuous_taylorDecrement_joint {f : E → ℝ} {p : ℕ} (hf : ContDiff ℝ p f) :
    Continuous (fun z : E × E => taylorDecrement f p z.1 z.2) := by
  simp only [taylorDecrement_eq]
  exact (hf.continuous.comp continuous_fst).sub (continuous_taylorModel_joint hf)

/-- The Taylor gap on a fixed ball is continuous as the expansion point varies. -/
theorem continuous_gapOn_taylorDecrement [ProperSpace E] {f : E → ℝ} {p : ℕ}
    (hf : ContDiff ℝ p f) (δ : ℝ) :
    Continuous (fun x : E => gapOn (taylorDecrement f p x) (closedBall 0 δ)) := by
  exact (isCompact_closedBall (0 : E) δ).continuous_sSup
    (continuous_taylorDecrement_joint hf)

end Optimization.TaylorCriticality
