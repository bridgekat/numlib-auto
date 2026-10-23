import Numlib.Optimization.HighOrder.ModelSolve.Halving
import Numlib.Optimization.Regularization.ModelBounds
import Numlib.Optimization.Regularization.GlobalStep

/-!
# Uniform finite criticality solves for actual regularized tensor models

A genuine global model minimizer exists by coercivity. If its norm is at most
one, actual derivative bounds yield finite first-passing criticality loops in
every requested order. Their radius floors share one positive constant chosen
before the tensor jet, penalty parameter and all requested accuracies.
-/

namespace ModelSolve
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {ι : Type*}

/-- The positive order radii from actual halving loops stay above a common
accuracy multiple, for a constant fixed before all model data and accuracies.
The selected step is a genuine global minimizer, so it also meets every allowed
fraction-of-global-improvement rule. The large-step alternative uses a strict
inequality; at norm exactly one the actual criticality tests are retained. -/
theorem exists_uniform_regularized_solve (p : ℕ) {S D : ℝ}
    (hS : 0 ≤ S) (hD : 0 ≤ D) :
    ∃ κ > 0, κ ≤ 1 ∧ ∀ σ : ℝ, 0 < σ → σ ≤ S →
      ∀ A : FormalMultilinearSeries ℝ E ℝ,
        (∀ i, 2 ≤ i → i ≤ p → ‖A i‖ ≤ D) →
      ∀ θ ζ : ℝ, 0 < θ → θ ≤ 1 → 0 < ζ → ζ ≤ 1 →
      ∀ (order : ι → ℕ), (∀ a, 0 < order a ∧ order a ≤ p) →
      ∀ (ε : ι → ℝ), (∀ a, 0 < ε a ∧ ε a ≤ 1) →
      ∃ s : E,
        (∀ t : E, ModelDecrease.penalized (TaylorModel.ofJet A p) p σ s ≤
          ModelDecrease.penalized (TaylorModel.ofJet A p) p σ t) ∧
        (∀ μ : ℝ, 0 ≤ μ → μ ≤ 1 →
          ModelDecrease.ApproximateGlobalStep
            (ModelDecrease.penalized (TaylorModel.ofJet A p) p σ) μ s) ∧
        (1 < ‖s‖ ∨ ∃ (d : ι → ℕ → E) (N : ι → ℕ), ∀ a,
          (∀ t, ‖d a t‖ ≤ BacktrackingGradient.step 1 t ∧
            ζ * TaylorModel.criticality
              (ModelDecrease.penalized (TaylorModel.ofJet A p) p σ)
              (order a) s (BacktrackingGradient.step 1 t) ≤
              TaylorModel.decrement (ModelDecrease.penalized (TaylorModel.ofJet A p) p σ)
                (order a) s (d a t)) ∧
          CriticalHalvingRun (ModelDecrease.penalized (TaylorModel.ofJet A p) p σ)
            (order a) s (ζ * θ * ε a) 1 (d a) (N a) ∧
          κ * (ζ * θ * ε a) ≤ BacktrackingGradient.step 1 (N a) ∧
          (∀ t ≤ N a, BacktrackingGradient.step 1 (N a) ≤ BacktrackingGradient.step 1 t ∧
            BacktrackingGradient.step 1 t ≤ 1) ∧
          (order a ≤ 2 → N a = 0)) := by
  obtain ⟨B, hB, hbound⟩ :=
    ModelDecrease.exists_uniform_penalized_derivative_bound (E := E) p hS hD
  let κ := min (1 / (8 * B)) 1
  have hκ : 0 < κ := lt_min (by positivity) zero_lt_one
  refine ⟨κ, hκ, min_le_right _ _, ?_⟩
  intro σ hσ hσS A hA θ ζ hθ hθ1 hζ hζ1 order horder ε hε
  let m := ModelDecrease.penalized (TaylorModel.ofJet A p) p σ
  obtain ⟨s, hs⟩ := ModelDecrease.exists_minimizer_ofJet A p hσ
  have hfrac : ∀ μ : ℝ, 0 ≤ μ → μ ≤ 1 →
      ModelDecrease.ApproximateGlobalStep m μ s := by
    intro μ hμ hμ1 t
    have hdrop : 0 ≤ m 0 - m s := sub_nonneg.mpr (hs 0)
    calc μ * (m 0 - m t) ≤ μ * (m 0 - m s) :=
          mul_le_mul_of_nonneg_left (sub_le_sub_left (hs t) _) hμ
      _ ≤ m 0 - m s := mul_le_of_le_one_left hdrop hμ1
  refine ⟨s, hs, hfrac, ?_⟩
  by_cases hlarge : 1 < ‖s‖
  · exact Or.inl hlarge
  · right
    have hs1 : ‖s‖ ≤ 1 := not_lt.mp hlarge
    obtain ⟨hder, hlip⟩ := hbound σ hσ.le hσS A hA
    have hall : ∀ a : ι, ∃ (d : ℕ → E) (N : ℕ),
        (∀ t, ‖d t‖ ≤ BacktrackingGradient.step 1 t ∧
          ζ * TaylorModel.criticality m (order a) s (BacktrackingGradient.step 1 t) ≤
            TaylorModel.decrement m (order a) s (d t)) ∧
        CriticalHalvingRun m (order a) s (ζ * θ * ε a) 1 d N ∧
        κ * (ζ * θ * ε a) ≤ BacktrackingGradient.step 1 N ∧
        (∀ t ≤ N, BacktrackingGradient.step 1 N ≤ BacktrackingGradient.step 1 t ∧
          BacktrackingGradient.step 1 t ≤ 1) ∧
        (order a ≤ 2 → N = 0) := by
      intro a
      have hα : 0 < ζ * θ * ε a := mul_pos (mul_pos hζ hθ) (hε a).1
      obtain ⟨d, N, hd, hrun, hfloor, hprefix, hlow⟩ :=
        exists_attaining_criticalHalvingRun (horder a).1 (horder a).2
          (ModelDecrease.contDiff_penalized_ofJet A p p le_rfl σ) hB.le hB le_rfl hα hζ1
          hlip s hs (fun n hn hnp => hder n (by have := (horder a).1; omega) hnp s hs1)
          zero_lt_one le_rfl
      refine ⟨d, N, hd, hrun, ?_, hprefix, hlow⟩
      apply le_trans _ hfloor
      apply le_min
      · have hh := mul_le_mul_of_nonneg_right (min_le_left (1 / (8 * B)) 1) hα.le
        simpa only [div_mul_eq_mul_div, one_mul] using hh
      · exact (mul_le_of_le_one_left hα.le (min_le_right (1 / (8 * B)) 1)).trans
          (by
            have hzθ : ζ * θ ≤ 1 := by
              simpa only [one_mul] using mul_le_mul hζ1 hθ1 hθ.le zero_le_one
            simpa only [one_mul] using mul_le_mul hzθ (hε a).2 (hε a).1.le zero_le_one)
    choose d N hd using hall
    exact ⟨d, N, hd⟩

/-- Actual globally minimizing regularized steps have either norm greater than
one or positive criticality radii with a common accuracy floor. Every
criticality and decrement test is derived from the finite actual halving loops;
first- and second-order radii equal one. -/
theorem exists_uniform_regularized_critical_step (p : ℕ) {S D : ℝ}
    (hS : 0 ≤ S) (hD : 0 ≤ D) :
    ∃ κ > 0, κ ≤ 1 ∧ ∀ σ : ℝ, 0 < σ → σ ≤ S →
      ∀ A : FormalMultilinearSeries ℝ E ℝ,
        (∀ i, 2 ≤ i → i ≤ p → ‖A i‖ ≤ D) →
      ∀ θ ζ : ℝ, 0 < θ → θ ≤ 1 → 0 < ζ → ζ ≤ 1 →
      ∀ (order : ι → ℕ), (∀ a, 0 < order a ∧ order a ≤ p) →
      ∀ (ε : ι → ℝ), (∀ a, 0 < ε a ∧ ε a ≤ 1) →
      ∃ s : E,
        (∀ t : E, ModelDecrease.penalized (TaylorModel.ofJet A p) p σ s ≤
          ModelDecrease.penalized (TaylorModel.ofJet A p) p σ t) ∧
        (∀ μ : ℝ, 0 ≤ μ → μ ≤ 1 →
          ModelDecrease.ApproximateGlobalStep
            (ModelDecrease.penalized (TaylorModel.ofJet A p) p σ) μ s) ∧
        (1 < ‖s‖ ∨ ∃ (δ : ι → ℝ) (d : ι → E), ∀ a,
          (0 < δ a ∧ δ a ≤ 1) ∧ κ * (ζ * θ * ε a) ≤ δ a ∧
          (order a ≤ 2 → δ a = 1) ∧ ‖d a‖ ≤ δ a ∧
          ζ * TaylorModel.criticality
            (ModelDecrease.penalized (TaylorModel.ofJet A p) p σ) (order a) s (δ a) ≤
            TaylorModel.decrement (ModelDecrease.penalized (TaylorModel.ofJet A p) p σ)
              (order a) s (d a) ∧
          TaylorModel.decrement (ModelDecrease.penalized (TaylorModel.ofJet A p) p σ)
              (order a) s (d a) ≤ ζ * θ * ε a * δ a ^ order a / (order a).factorial ∧
          TaylorModel.criticality (ModelDecrease.penalized (TaylorModel.ofJet A p) p σ)
              (order a) s (δ a) ≤ θ * ε a * δ a ^ order a / (order a).factorial) := by
  obtain ⟨κ, hκ, hκ1, hsolve⟩ :=
    exists_uniform_regularized_solve (E := E) (ι := ι) p hS hD
  refine ⟨κ, hκ, hκ1, ?_⟩
  intro σ hσ hσS A hA θ ζ hθ hθ1 hζ hζ1 order horder ε hε
  obtain ⟨s, hs, hfrac, hcase⟩ := hsolve σ hσ hσS A hA θ ζ hθ hθ1 hζ hζ1
    order horder ε hε
  refine ⟨s, hs, hfrac, ?_⟩
  rcases hcase with hlarge | ⟨d, N, hrun⟩
  · exact Or.inl hlarge
  · refine Or.inr ⟨fun a => BacktrackingGradient.step 1 (N a), fun a => d a (N a), ?_⟩
    intro a
    obtain ⟨hd, hr, hfloor, hprefix, hlow⟩ := hrun a
    refine ⟨⟨BacktrackingGradient.step_pos zero_lt_one _,
      (hprefix _ le_rfl).2⟩, hfloor, ?_, (hd _).1, (hd _).2, hr.passes,
      hr.criticality_le_of_approximation hζ (hd _).2⟩
    intro ha
    change BacktrackingGradient.step 1 (N a) = 1
    rw [hlow ha]
    simp

end ModelSolve
