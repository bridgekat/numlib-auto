import Numlib.Optimization.Constrained.TwoPhase.Geometry
import Numlib.Optimization.Constrained.TargetFamily
import Numlib.Optimization.Regularization.HighOrder.ParameterOn

/-!
# Uniform actual merit and parameter bounds across all inner calls

The bounded objective range confines every actual target to a fixed interval.
The actual affine target family then has a common highest-derivative Lipschitz
constant, and feasible model acceptance gives a common parameter cap. Constants
are chosen before every requested accuracy, execution and inner call.
-/

namespace Constrained.TwoPhase
open Set TaylorModel
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F]

/-- Every actual inner iterate lies in the unit augmented residual merit level,
derived from initial residual geometry and actual accepted objective decreases. -/
theorem PhaseTwoRun.inner_merit_le_half {p : ℕ} {closedReset : Bool}
    {f : E → ℝ} {c : E → F} {C : Set E} {P : ConvexRegularization.Settings p}
    {ε₀ ε₁ θ : ℝ} {D : Data E} {N k i : ℕ}
    (h : PhaseTwoRun closedReset f c C P ε₀ ε₁ θ D N)
    (hk : k < N) (hi : i ≤ D.length k) :
    targetMerit f c (D.target k) ((D.inner k).point i) ≤ (1 / 2 : ℝ) := by
  have ho := (h.inner_run k hk).objective_le (Nat.zero_le i) hi
  rw [h.inner_start k hk] at ho
  apply ho.trans
  rw [targetMerit_eq_residual]
  have hn := (h.invariants hk.le).2.trans h.primal_le_one
  nlinarith [norm_nonneg (residual f c (D.target k) (D.point k))]

/-- The source merit assumptions give uniform actual highest-derivative
Lipschitzness and a common bound on every inner regularization parameter.
Both literal and closed-reset executions are covered, including initial and
terminal inner parameters. No componentwise derivative bounds are imposed. -/
theorem exists_uniform_bounds {p : ℕ} {f : E → ℝ} {c : E → F}
    {C S : Set E} (hS : IsOpen S) (hCS : C ⊆ S) (hC : Convex ℝ C)
    (P : ConvexRegularization.Settings p)
    (hmu : ∀ t : ℝ, ContDiffOn ℝ p (targetMerit f c t) S)
    (hlip : ∀ t : ℝ, ∃ L ≥ 0, ∀ x ∈ C, ∀ y ∈ C,
      ‖iteratedFDeriv ℝ p (targetMerit f c t) x -
        iteratedFDeriv ℝ p (targetMerit f c t) y‖ ≤ L * ‖x - y‖)
    {β flow fup : ℝ}
    (hfb : ∀ x ∈ C, ‖c x‖ ≤ β → flow ≤ f x ∧ f x ≤ fup) :
    ∃ L ≥ 0, ∃ σmax > P.sigmaMin,
      ∀ (ε₀ ε₁ θ : ℝ) (D : Data E) (N : ℕ) (closedReset : Bool),
        PhaseTwoRun closedReset f c C P ε₀ ε₁ θ D N → ε₀ ≤ β →
        (∀ k ≤ N, ∀ x ∈ C, ∀ y ∈ C,
          ‖iteratedFDeriv ℝ p (targetMerit f c (D.target k)) x -
            iteratedFDeriv ℝ p (targetMerit f c (D.target k)) y‖ ≤ L * ‖x - y‖) ∧
        (∀ k < N, ∀ i ≤ D.length k, (D.inner k).parameter i ≤ σmax) := by
  obtain ⟨L0, hL0, hl0⟩ := hlip 0
  obtain ⟨L1, hL1, hl1⟩ := hlip 1
  obtain ⟨L, hL, hl⟩ := exists_targetMerit_uniform_lipschitz P.order_pos hS hCS
    (hmu 0) (hmu 1) hL0 hL1 hl0 hl1 (flow - 1) fup
  let cap := max P.sigmaInitial (P.gamma3 * L / (1 - P.eta2))
  have hcap : P.sigmaMin ≤ cap := P.sigmaMin_le_initial.trans (le_max_left _ _)
  refine ⟨L, hL, cap + 1, by dsimp [cap] at *; linarith, ?_⟩
  intro ε₀ ε₁ θ D N closedReset h hβ
  have hcommon : ∀ k ≤ N, ∀ x ∈ C, ∀ y ∈ C,
      ‖iteratedFDeriv ℝ p (targetMerit f c (D.target k)) x -
        iteratedFDeriv ℝ p (targetMerit f c (D.target k)) y‖ ≤ L * ‖x - y‖ := by
    intro k hk
    exact hl (D.target k) (h.target_bounds hβ hfb hk)
  refine ⟨hcommon, ?_⟩
  intro k hk i hi
  have hin := h.inner_run k hk
  have hb := hin.modelTrace.parameter_le_on hS hCS hC (hmu (D.target k)) hL
    (hcommon k hk.le) (fun j hj => hin.mem hj.le) hin.feasible_trial hi
  rw [hin.initial_parameter] at hb
  exact hb.trans (by change cap ≤ cap + 1; linarith)

end Constrained.TwoPhase
