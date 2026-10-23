import Numlib.Optimization.Composite.Run
import Numlib.Optimization.Composite.SmoothReduction

/-!
# Actual smooth executions inside the composite class

A zero residual preserves actual models, ratios and generalized Taylor tests.
First-order smooth runs therefore lift to composite runs, with the same actual
points and evaluation schedule. Strict failed computed tests are retained.
-/

namespace Composite
open InexactTrustRegion
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Actual smooth model computations furnish detailed composite step returns
for a zero residual, with the same computed radius and a positive global gap. -/
theorem exists_stepOutput_of_smooth {f : E → ℝ} {h : F → ℝ} (hh : h 0 = 0)
    {p q : ℕ} {θ ζ σ : ℝ} {ε δ : Fin q → ℝ} {x s : E}
    (hc : ModelSolve.StepComputation (HighOrderRegularization.model f p x σ)
      modelOrder θ ζ ε s δ) :
    ∃ (μ : ℝ) (d : Fin q → E),
      StepOutput f (fun _ => (0 : F)) h p θ ζ ε x s σ μ δ d := by
  obtain ⟨μ, hμ, hμ1, hgap⟩ := hc.fraction
  have he : regularizedModel f (fun _ => (0 : F)) h p x σ =
      HighOrderRegularization.model f p x σ := by
    funext t
    exact regularizedModel_zero_residual f hh p x σ t
  have hres : residualModel (fun _ : E => (0 : F)) p x = fun _ => 0 := by
    funext t
    exact eval_zero_residual p x t
  rcases hc.result with ⟨hlarge, _⟩ | ⟨_, point, direction, count, last, hlast⟩
  · refine ⟨μ, fun _ => 0, hμ, hμ1, ?_, hc.radius_mem, ?_⟩
    · rwa [he]
    · intro hs
      exact (not_lt_of_ge hs.le hlarge).elim
  · refine ⟨μ, last, hμ, hμ1, ?_, hc.radius_mem, ?_⟩
    · rwa [he]
    · intro _ a
      rw [hres, criticality_zero_residual _ hh, decrement_zero_residual _ hh]
      exact ⟨(hlast a).2.2.2.2.1, (hlast a).2.2.2.2.2⟩

/-- A genuine first-order smooth run with strict failed computed tests lifts
to a zero-residual composite run without changing its points or counters. -/
theorem exists_run_of_smooth {f : E → ℝ} {h : F → ℝ} (hh : h 0 = 0)
    {p N : ℕ} {P : Settings p 1} {ε : Fin 1 → ℝ}
    {D : HighOrderRegularization.ExecutionData E 1}
    (hr : HighOrderRegularization.Run f P ε D N)
    (hstrict : ∀ k ≤ N, ∀ a, D.selected k = some a →
      P.zeta * ε a * D.radius k a ^ modelOrder a / (modelOrder a).factorial <
        TaylorModel.decrement f (modelOrder a) (D.point k) (D.direction k a)) :
    ∃ C : ExecutionData E 1, C.toExecutionData = D ∧
      Run f (fun _ => (0 : F)) h P ε C N := by
  classical
  have hall : ∀ k, ∃ (μ : ℝ) (d : Fin 1 → E),
      k ≤ N → D.selected k ≠ none →
      StepOutput f (fun _ => (0 : F)) h p P.theta P.zeta ε
        (D.point k) (D.step k) (D.parameter k) μ (D.solvedRadius k) d := by
    intro k
    by_cases hk : k ≤ N ∧ D.selected k ≠ none
    · obtain ⟨μ, d, hd⟩ := exists_stepOutput_of_smooth hh (hr.step_two k hk.1 hk.2)
      exact ⟨μ, d, fun _ _ => hd⟩
    · exact ⟨1, fun _ => 0, fun h1 h2 => (hk ⟨h1, h2⟩).elim⟩
  choose μ d hd using hall
  let C : ExecutionData E 1 := ⟨D, μ, d⟩
  refine ⟨C, rfl, ?_⟩
  refine { accuracy_pos := hr.accuracy_pos
           accuracy_le_one := hr.accuracy_le_one
           initial_parameter := hr.initial_parameter
           initial_radii := hr.initial_radii
           modelTrace := ?_
           check := ?_
           step_two := hd
           continues := hr.continues
           point_update := hr.modelTrace.point_update
           radius_update := hr.radius_update }
  · refine ⟨hr.modelTrace.updates, ?_, ?_⟩
    · intro k hk
      simpa only [C, regularizedModel_zero_residual f hh] using hr.modelTrace.improvement k hk
    · intro k hk
      change D.ratio k = (f (D.point k) + h 0 - (f (D.point k + D.step k) + h 0)) /
        (taylorModel f (fun _ => (0 : F)) h p (D.point k) 0 -
          taylorModel f (fun _ => (0 : F)) h p (D.point k) (D.step k))
      rw [hh]
      simp only [add_zero, taylorModel_zero_residual f hh, TaylorModel.eval_zero]
      simpa only [HighOrderRegularization.ratio, TaylorModel.decrement, TaylorModel.eval_zero]
        using hr.modelTrace.ratio k hk
  · intro k hk
    have hc := hr.check k hk
    have hguard (a : Fin 1) : ∀ b, D.selected k = some b → a ≤ b := by
      intro b _
      exact le_of_eq (Subsingleton.elim _ _)
    constructor
    · intro a
      exact hc.feasible a (hguard a)
    · intro a
      rw [criticality_zero_residual f hh, decrement_zero_residual f hh]
      exact hc.approximation a (hguard a)
    · intro hn a
      rw [decrement_zero_residual f hh]
      exact (hc.passed hn a).le
    · intro a ha
      rw [decrement_zero_residual f hh]
      exact hstrict k hk a ha

end Composite
