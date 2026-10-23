import Numlib.Optimization.HighOrder.ModelSolve.Uniform
import Numlib.Optimization.Regularization.ModelSharp

/-!
# Finite actual regularized model solves with the printed radius floor

Coercivity gives a genuine global minimizer, which is an allowed fraction-one
model solve. Sharp integer norm-power derivatives give the printed coefficient
in every finite actual first-passing criticality loop. At norm exactly one the
criticality tests are retained, consistent with the strict large-step exit in
the step-existence statement.
-/

namespace ModelSolve
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {ι : Type*}

/-- A genuine finite model solve satisfies every step-existence conclusion
with the exact printed coefficient `zeta*theta/(8*(3*D+sigma))`.
All low-order radii equal one, including on the large-step branch. -/
theorem exists_regularized_solve_sharp (A : FormalMultilinearSeries ℝ E ℝ) (p : ℕ)
    {D σ θ ζ : ℝ} (hD : 1 ≤ D) (hσ : 0 < σ)
    (hA : ∀ i, 2 ≤ i → i ≤ p → ‖A i‖ ≤ D)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (order : ι → ℕ) (horder : ∀ a, 0 < order a ∧ order a ≤ p)
    (ε : ι → ℝ) (hε : ∀ a, 0 < ε a ∧ ε a ≤ 1) :
    ∃ (s : E) (δ : ι → ℝ),
      (∀ t, ModelDecrease.penalized (TaylorModel.ofJet A p) p σ s ≤
        ModelDecrease.penalized (TaylorModel.ofJet A p) p σ t) ∧
      (∀ μ : ℝ, 0 ≤ μ → μ ≤ 1 → ModelDecrease.ApproximateGlobalStep
        (ModelDecrease.penalized (TaylorModel.ofJet A p) p σ) μ s) ∧
      (∀ a, 0 < δ a ∧ δ a ≤ 1) ∧ (∀ a, order a ≤ 2 → δ a = 1) ∧
      (1 < ‖s‖ ∨ ∃ d : ι → E, ∀ a,
        ζ * θ / (8 * (3 * D + σ)) * ε a ≤ δ a ∧ ‖d a‖ ≤ δ a ∧
        ζ * TaylorModel.criticality (ModelDecrease.penalized (TaylorModel.ofJet A p) p σ)
          (order a) s (δ a) ≤
          TaylorModel.decrement (ModelDecrease.penalized (TaylorModel.ofJet A p) p σ)
            (order a) s (d a) ∧
        TaylorModel.decrement (ModelDecrease.penalized (TaylorModel.ofJet A p) p σ)
          (order a) s (d a) ≤ ζ * θ * ε a * δ a ^ order a / (order a).factorial ∧
        TaylorModel.criticality (ModelDecrease.penalized (TaylorModel.ofJet A p) p σ)
          (order a) s (δ a) ≤ θ * ε a * δ a ^ order a / (order a).factorial) := by
  classical
  let m := ModelDecrease.penalized (TaylorModel.ofJet A p) p σ
  let B := 3 * D + σ
  have hB : 0 < B := by dsimp [B]; linarith
  have hf : ContDiff ℝ p m := ModelDecrease.contDiff_penalized_ofJet A p p le_rfl σ
  have hlip := ModelDecrease.norm_sub_iteratedFDeriv_penalized_ofJet_le A p hσ.le
  obtain ⟨s, hs⟩ := ModelDecrease.exists_minimizer_ofJet A p hσ
  have hfrac : ∀ μ : ℝ, 0 ≤ μ → μ ≤ 1 →
      ModelDecrease.ApproximateGlobalStep m μ s := by
    intro μ hμ hμ1
    apply (ModelDecrease.approximateGlobalStep_iff_of_isMin hμ hs).mpr
    exact mul_le_of_le_one_left (sub_nonneg.mpr (hs 0)) hμ1
  by_cases hlarge : 1 < ‖s‖
  · exact ⟨s, fun _ => 1, hs, hfrac, fun _ => ⟨zero_lt_one, le_rfl⟩,
      fun _ _ => rfl, Or.inl hlarge⟩
  · have hs1 : ‖s‖ ≤ 1 := not_lt.mp hlarge
    have hall : ∀ a, ∃ (d : ℕ → E) (N : ℕ),
        (∀ t, ‖d t‖ ≤ BacktrackingGradient.step 1 t ∧
          ζ * TaylorModel.criticality m (order a) s (BacktrackingGradient.step 1 t) ≤
            TaylorModel.decrement m (order a) s (d t)) ∧
        CriticalHalvingRun m (order a) s (ζ * θ * ε a) 1 d N ∧
        min (ζ * θ * ε a / (8 * B)) 1 ≤ BacktrackingGradient.step 1 N ∧
        (∀ t ≤ N, BacktrackingGradient.step 1 N ≤ BacktrackingGradient.step 1 t ∧
          BacktrackingGradient.step 1 t ≤ 1) ∧
        (order a ≤ 2 → N = 0) := by
      intro a
      exact exists_attaining_criticalHalvingRun (horder a).1 (horder a).2 hf hσ.le hB
        (by dsimp [B]; linarith) (mul_pos (mul_pos hζ hθ) (hε a).1) hζ1 hlip s hs
        (fun n hn hnp => ModelDecrease.norm_iteratedFDeriv_penalized_ofJet_le_three_mul_add
          A hnp hσ.le (zero_le_one.trans hD)
          (fun i hni hip => hA i (by have := (horder a).1; omega) hip) hs1)
        zero_lt_one le_rfl
    choose d N hd using hall
    let δ : ι → ℝ := fun a => BacktrackingGradient.step 1 (N a)
    refine ⟨s, δ, hs, hfrac, ?_, ?_, Or.inr ⟨fun a => d a (N a), ?_⟩⟩
    · intro a
      exact ⟨BacktrackingGradient.step_pos zero_lt_one _, (hd a).2.2.2.1 _ le_rfl |>.2⟩
    · intro a ha
      dsimp [δ]
      rw [(hd a).2.2.2.2 ha]
      simp
    · intro a
      obtain ⟨hdir, hrun, hfloor, hprefix, hlow⟩ := hd a
      have hα : ζ * θ * ε a ≤ 1 := by
        have ht := mul_le_mul hζ1 hθ1 hθ.le zero_le_one
        have he := mul_le_mul ht (hε a).2 (hε a).1.le (by norm_num)
        simpa only [one_mul] using he
      have hsmall : ζ * θ * ε a / (8 * B) ≤ 1 :=
        (div_le_one (by positivity)).mpr (by dsimp [B]; linarith)
      have hfloor' := (min_eq_left hsmall) ▸ hfloor
      refine ⟨?_, (hdir _).1, (hdir _).2, hrun.passes,
        hrun.criticality_le_of_approximation hζ (hdir _).2⟩
      simpa only [div_mul_eq_mul_div, mul_assoc] using hfloor'

end ModelSolve
