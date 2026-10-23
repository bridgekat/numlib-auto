import Numlib.Optimization.Constrained.TwoPhase.Geometry
import Numlib.Optimization.Constrained.TargetCriticality
import Numlib.Optimization.Constrained.FirstOrderCriticality

/-!
# Actual termination certificates for the closed-reset two-phase algorithm

Including residual equality in the reset guard forces every terminating return
to satisfy normalized merit criticality. The final positive residual and
nonnegative target gap then yield either infeasible criticality or the genuine
scaled Lagrangian inequality, on the same feasible displacement set.
-/

namespace Constrained.TwoPhase
open Set TaylorModel
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [ProperSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]

omit [ProperSpace E] in
/-- At a zero objective-target gap the actual target merit and the actual
constraint least-squares merit have the same constrained first-order measure. -/
theorem firstCriticality_targetMerit_of_gap_zero {f : E → ℝ} {c : E → F} {x : E}
    (hf : DifferentiableAt ℝ f x) (hc : DifferentiableAt ℝ c x)
    {t : ℝ} (ht : f x - t = 0) (C : Set E) :
    firstCriticality (targetMerit f c t) C x =
      firstCriticality (fun z => ‖c z‖ ^ 2 / 2) C x := by
  apply constrainedCriticality_one_congr_fderiv
  rw [(hasFDerivAt_targetMerit hf hc t).fderiv, ht, zero_smul, add_zero]
  have hd := hc.hasFDerivAt.norm_sq.const_smul (1 / 2 : ℝ)
  have he : (fun z => ‖c z‖ ^ 2 / 2) = (1 / 2 : ℝ) • (fun z => ‖c z‖ ^ 2) := by
    funext z
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [he, hd.fderiv]
  ext d
  simp [innerSL_apply_apply, smul_eq_mul]

omit [ProperSpace E] [InnerProductSpace ℝ F] in
/-- Every corrected outer return leaves its updated residual strictly above
`θ ε₀`, including the equality case which now triggers a full reset. -/
theorem CorrectedPhaseTwoRun.residual_gt {p : ℕ} {f : E → ℝ} {c : E → F}
    {C : Set E} {P : ConvexRegularization.Settings p} {ε₀ ε₁ θ : ℝ}
    {D : Data E} {N k : ℕ} (h : PhaseTwoRun true f c C P ε₀ ε₁ θ D N)
    (hk : k < N) :
    θ * ε₀ < ‖residual f c (D.target (k + 1)) (D.point (k + 1))‖ := by
  by_cases hr : ResetGuard true f c ε₀ θ (D.target k) (D.point (k + 1))
  · rw [h.reset_residual hk hr]
    exact mul_lt_of_lt_one_left h.primal_pos h.theta_lt_one
  · have hg : θ * ε₀ < ‖residual f c (D.target k) (D.point (k + 1))‖ := by
      simpa only [ResetGuard, ite_true, not_le] using hr
    by_cases hover : f (D.point (k + 1)) < D.target k
    · rw [(h.reflection_residual hk hr hover).1]
      exact hg
    · rw [h.target_update k hk, nextTarget, ite_eq_right hr, ite_eq_right hover]
      exact hg

/-- The repaired Phase2 stopping rule gives exactly the source's two possible
first-order conclusions, with an explicit actual multiplier in the feasible case. -/
theorem CorrectedPhaseTwoRun.termination {p : ℕ} {f : E → ℝ} {c : E → F}
    {C : Set E} {P : ConvexRegularization.Settings p} {ε₀ ε₁ θ : ℝ}
    {D : Data E} {N k : ℕ} (h : PhaseTwoRun true f c C P ε₀ ε₁ θ D N)
    (hC : IsClosed C) (hk : k < N)
    (hf : DifferentiableAt ℝ f (D.point (k + 1)))
    (hc : DifferentiableAt ℝ c (D.point (k + 1)))
    (hs : StopAfter true f c C ε₀ ε₁ θ (D.target k) (D.point (k + 1))) :
    (firstCriticality (fun z => ‖c z‖ ^ 2 / 2) C (D.point (k + 1)) ≤
        ε₁ * ‖c (D.point (k + 1))‖ ∧ θ * ε₀ < ‖c (D.point (k + 1))‖) ∨
      (∃ y : F, firstCriticality (vectorLagrangian f c y) C (D.point (k + 1)) ≤
        ε₁ * multiplierNorm y ∧ ‖c (D.point (k + 1))‖ ≤ ε₀) := by
  have htarget := CorrectedPhaseTwoRun.target_of_stop h hk hs
  have hres := CorrectedPhaseTwoRun.residual_gt h hk
  have hgap := (h.invariants (show k + 1 ≤ N by omega)).1
  by_cases hz : f (D.point (k + 1)) - D.target (k + 1) = 0
  · left
    have hn : ‖residual f c (D.target (k + 1)) (D.point (k + 1))‖ =
        ‖c (D.point (k + 1))‖ := by
      rw [residual_norm, hz]
      simp
    rw [MeritTarget, firstCriticality_targetMerit_of_gap_zero hf hc hz C, hn] at htarget
    exact ⟨htarget, by simpa only [hn] using hres⟩
  · right
    have hp : 0 < f (D.point (k + 1)) - D.target (k + 1) := lt_of_le_of_ne hgap
      (Ne.symm hz)
    refine ⟨targetMultiplier f c (D.target (k + 1)) (D.point (k + 1)), ?_,
      (h.component_bounds (by omega)).1⟩
    have hh := lagrangian_first_order_of_targetMerit hf hc hp hC
      (h.mem (by omega)) zero_le_one (by
        simpa only [MeritTarget, firstCriticality, residual_norm, mul_one] using htarget)
    simpa only [firstCriticality, mul_one] using hh

omit [ProperSpace E] [InnerProductSpace ℝ F] in
/-- Phase1's literal return disjunction and actual infeasible exit guard imply
its precise scaled feasibility-criticality certificate for any chosen power. -/
theorem phase_one_termination {c : E → F} {Φ : E → ℝ} {C : Set E}
    {x : E} {ε₀ ε₁ θ ℓ : ℝ}
    (hr : ‖c x‖ ≤ θ * ε₀ ∨ firstCriticality Φ C x ≤ ε₁ * ‖c x‖ ^ (ℓ - 1))
    (hs : θ * ε₀ < ‖c x‖) :
    firstCriticality Φ C x ≤ ε₁ * ‖c x‖ ^ (ℓ - 1) ∧ θ * ε₀ < ‖c x‖ :=
  ⟨hr.resolve_left (not_le_of_gt hs), hs⟩

end Constrained.TwoPhase
