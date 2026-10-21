import Numlib.Optimization.CoupledCubic
import NumlibSurface.CartisGouldToint.Chapter14.Section02

/-!
# Chapter 14, Section 2: fixed analytic data for the coupled cubic

The same compact box, polynomial, initial point, and open neighborhood satisfy the complete
source bounded-jet assumptions before any choice of tolerances. Comparisons extend from
every point of the initial feasible sublevel set to every point of the neighborhood.
-/

noncomputable section
open Set Metric Optimization
namespace CartisGouldToint.Chapter14.Section02
open CoupledCubic

/-- The fixed box lies strictly inside the full open comparison neighborhood. -/
theorem coupledCubic_box_subset_neighborhood : box ⊆ ball 0 5 :=
  box_subset_closedBall.trans (closedBall_subset_ball (by norm_num))

/-- The fixed initial point is feasible. -/
theorem coupledCubic_initial_feasible : point 1 0 1 ∈ box := by
  rw [point_mem_box]
  norm_num

/-- Fixed constants at least one give all source positive-order bounded-jet assumptions
for the entire initial feasible sublevel set, with every comparison point in the open ball. -/
theorem coupledCubic_smoothBoundedJets :
    ∃ L B : ℕ → ℝ, (∀ j, 1 ≤ L j) ∧ (∀ j, 1 ≤ B j) ∧
      SmoothBoundedJetsOnLevelSet objective box (point 1 0 1) 2 false (ball 0 5) L B := by
  obtain ⟨L, B, hL, hB, h⟩ := CoupledCubic.exists_anchoredBoundedJets
  refine ⟨L, B, hL, hB, ?_⟩
  exact ⟨h.mono_centers (fun _ hx => hx.1), coupledCubic_initial_feasible,
    coupledCubic_box_subset_neighborhood, fun j _ _ => hL j, fun j _ _ => hB j⟩

/-- The same fixed polynomial also satisfies the stronger source assumptions including
order-zero Lipschitz continuity. All bounds remain fixed before every tolerance vector. -/
theorem coupledCubic_smoothBoundedJets_includeValue :
    ∃ L B : ℕ → ℝ, (∀ j, 1 ≤ L j) ∧ (∀ j, 1 ≤ B j) ∧
      SmoothBoundedJetsOnLevelSet objective box (point 1 0 1) 2 true (ball 0 5) L B := by
  obtain ⟨L, B, hL, hB, h⟩ := CoupledCubic.exists_anchoredBoundedJets
  obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : Space) 5).exists_bound_of_continuousOn
    (((contDiff_objective 1).fderiv_right (m := 0) (by norm_num)).continuous.continuousOn)
  let L' : ℕ → ℝ := fun j => if j = 0 then max 1 K else L j
  have hL' (j : ℕ) : 1 ≤ L' j := by
    dsimp [L']
    split_ifs
    · exact le_max_left _ _
    · exact hL j
  have hjets : ConstrainedTaylorCriticality.HasAnchoredBoundedJets objective 2 box
      (ball 0 5) true L' B := by
    refine ⟨h.isOpen, h.convex, h.centers_subset, h.contDiffOn,
      fun j _ _ => zero_le_one.trans (hL' j), h.bound_nonneg, h.bound, ?_⟩
    intro j _ hj x hx y hy d
    by_cases hj0 : j = 0
    · subst j
      have hx' : x ∈ closedBall (0 : Space) 5 :=
        closedBall_subset_closedBall (by norm_num) (box_subset_closedBall hx)
      have hy' : y ∈ closedBall (0 : Space) 5 := ball_subset_closedBall hy
      have hv := (convex_closedBall (0 : Space) 5).norm_image_sub_le_of_norm_fderiv_le
        (fun z _ => (contDiff_objective 1).differentiable (by norm_num) z)
        (fun z hz => (hK z hz).trans (le_max_right 1 K)) hx' hy'
      simpa only [sub_apply, iteratedFDeriv_zero_apply, pow_zero, mul_one, L', ite_eq_left rfl]
        using hv
    · have hj1 : 1 ≤ j := by omega
      simpa only [L', ite_eq_right hj0] using h.lipschitz j (Or.inl hj1) hj x hx y hy d
  exact ⟨L', B, hL', hB, hjets.mono_centers (fun _ hx => hx.1),
    coupledCubic_initial_feasible, coupledCubic_box_subset_neighborhood,
    fun j _ _ => hL' j, fun j _ _ => hB j⟩

end CartisGouldToint.Chapter14.Section02
