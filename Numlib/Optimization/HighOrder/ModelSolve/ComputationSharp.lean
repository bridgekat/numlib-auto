import Numlib.Optimization.HighOrder.ModelSolve.Computation
import Numlib.Optimization.Regularization.ModelSharp

/-!
# Sharp floors for primitive regularized model computations

Actual polynomial jets and norm-power derivatives supply the sharp model
bounds. Every changing-candidate finite radius computation then retains the
printed floor, and coercivity constructs a genuine permitted computation.
-/

namespace ModelSolve
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {ι : Type*}

/-- Every primitive regularized-model computation retains the printed radius
floor, derived from its actual halving guards and sharp model derivatives. -/
theorem StepComputation.radius_lower_penalized (A : FormalMultilinearSeries ℝ E ℝ)
    {p : ℕ} {order : ι → ℕ} {σ θ ζ D : ℝ} {ε δ : ι → ℝ} {s : E}
    (h : StepComputation (ModelDecrease.penalized (TaylorModel.ofJet A p) p σ)
      order θ ζ ε s δ)
    (hσ : 0 ≤ σ) (hD : 1 ≤ D)
    (hA : ∀ i, 2 ≤ i → i ≤ p → ‖A i‖ ≤ D)
    (horder : ∀ a, 0 < order a ∧ order a ≤ p)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hζ1 : ζ ≤ 1)
    (hε : ∀ a, 0 < ε a ∧ ε a ≤ 1) (hs : ‖s‖ ≤ 1) (a : ι) :
    ζ * θ / (8 * (3 * D + σ)) * ε a ≤ δ a := by
  let B := 3 * D + σ
  have hB : 0 < B := by dsimp [B]; linarith
  have htop := ModelDecrease.norm_sub_iteratedFDeriv_penalized_ofJet_le A p hσ
  have hlip : ∀ u v,
      ‖iteratedFDeriv ℝ p (ModelDecrease.penalized (TaylorModel.ofJet A p) p σ) u -
        iteratedFDeriv ℝ p (ModelDecrease.penalized (TaylorModel.ofJet A p) p σ) v‖ ≤
          B * ‖u - v‖ := fun u v => (htop u v).trans
            (mul_le_mul_of_nonneg_right (by dsimp [B]; linarith) (norm_nonneg _))
  have hf := ModelDecrease.contDiff_penalized_ofJet A p p le_rfl σ
  have hder : ∀ n, 2 ≤ n → n ≤ p → ∀ x : E, ‖x‖ ≤ 1 →
      ‖iteratedFDeriv ℝ n
        (ModelDecrease.penalized (TaylorModel.ofJet A p) p σ) x‖ ≤ B := fun n hn hnp x hx =>
    ModelDecrease.norm_iteratedFDeriv_penalized_ofJet_le_three_mul_add A hnp hσ
      (zero_le_one.trans hD) (fun i hni hip => hA i (hn.trans hni) hip) hx
  have hb := h.radius_lower hB hf hlip hder horder hs a
  have hnum : ζ * θ * ε a ≤ 1 := by
    have hzθ := mul_le_mul hζ1 hθ1 hθ.le zero_le_one
    have hzθε := mul_le_mul hzθ (hε a).2 (hε a).1.le (by norm_num)
    simpa only [one_mul] using hzθε
  have hsmall : ζ * θ * ε a / (8 * B) ≤ 1 :=
    (div_le_one (by positivity)).mpr (by dsimp [B]; linarith)
  rw [min_eq_left hsmall] at hb
  simpa only [div_mul_eq_mul_div, mul_assoc] using hb

/-- Every positive regularization of a finite jet admits an actual primitive
model computation, by coercivity, exact global minimization and finite Taylor
halving tests. No solver certificate is assumed. -/
theorem exists_penalized_stepComputation (A : FormalMultilinearSeries ℝ E ℝ)
    (p : ℕ) {σ θ ζ D : ℝ} (hσ : 0 < σ) (hD : 1 ≤ D)
    (hA : ∀ i, 2 ≤ i → i ≤ p → ‖A i‖ ≤ D)
    (order : ι → ℕ) (horder : ∀ a, 0 < order a ∧ order a ≤ p)
    (hθ : 0 < θ) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (ε : ι → ℝ) (hε : ∀ a, 0 < ε a) :
    ∃ (s : E) (δ : ι → ℝ), StepComputation
      (ModelDecrease.penalized (TaylorModel.ofJet A p) p σ) order θ ζ ε s δ := by
  obtain ⟨s, hs⟩ := ModelDecrease.exists_minimizer_ofJet A p hσ
  let B := 3 * D + σ
  have hB : 0 < B := by dsimp [B]; linarith
  have htop := ModelDecrease.norm_sub_iteratedFDeriv_penalized_ofJet_le A p hσ.le
  have hlip : ∀ u v,
      ‖iteratedFDeriv ℝ p (ModelDecrease.penalized (TaylorModel.ofJet A p) p σ) u -
        iteratedFDeriv ℝ p (ModelDecrease.penalized (TaylorModel.ofJet A p) p σ) v‖ ≤
          B * ‖u - v‖ := fun u v => (htop u v).trans
            (mul_le_mul_of_nonneg_right (by dsimp [B]; linarith) (norm_nonneg _))
  obtain ⟨δ, hδ⟩ := exists_stepComputation_of_isMin
    (ModelDecrease.contDiff_penalized_ofJet A p p le_rfl σ) hB hlip
    (fun n hn hnp x hx => ModelDecrease.norm_iteratedFDeriv_penalized_ofJet_le_three_mul_add
      A hnp hσ.le (zero_le_one.trans hD) (fun i hni hip => hA i (hn.trans hni) hip) hx)
    order horder hθ hζ hζ1 ε hε s hs
  exact ⟨s, δ, hδ⟩

end ModelSolve
