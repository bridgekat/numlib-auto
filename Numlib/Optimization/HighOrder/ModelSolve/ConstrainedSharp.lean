import Numlib.Optimization.HighOrder.ModelSolve.ConstrainedComputation
import Numlib.Optimization.Regularization.ModelSharp

/-!
# Genuine finite constrained model solves with sharp radius floors

Actual norm-power and Taylor tensor bounds give the constant 3D+sigma. Closed
convex feasible sets admit actual globally minimizing model steps, constructed
feasible Taylor directions and finite first-passing halvings. All returned
radius floors are derived, with a uniform coefficient before every accuracy.
-/

namespace ModelSolve
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {ι : Type*}

/-- Every primitive regularized-model computation retains the printed radius
floor, derived from its actual halving guards and sharp model derivatives. -/
theorem ConstrainedStepComputation.radius_lower_penalized (A : FormalMultilinearSeries ℝ E ℝ)
    {p : ℕ} {order : ι → ℕ} {σ θ ζ D : ℝ} {ε δ : ι → ℝ} {s : E}
    {C : Set E}
    (h : ConstrainedStepComputation (ModelDecrease.penalized (TaylorModel.ofJet A p) p σ) C
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
theorem exists_penalized_constrained_stepComputation (A : FormalMultilinearSeries ℝ E ℝ)
    (p : ℕ) {C : Set E} (hC : IsClosed C) (hconv : Convex ℝ C)
    (hzero : (0 : E) ∈ C) {σ θ ζ D : ℝ} (hσ : 0 < σ) (hD : 1 ≤ D)
    (hA : ∀ i, 2 ≤ i → i ≤ p → ‖A i‖ ≤ D)
    (order : ι → ℕ) (horder : ∀ a, 0 < order a ∧ order a ≤ p)
    (hθ : 0 < θ) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (ε : ι → ℝ) (hε : ∀ a, 0 < ε a) :
    ∃ (s : E) (δ : ι → ℝ), ConstrainedStepComputation
      (ModelDecrease.penalized (TaylorModel.ofJet A p) p σ) C order θ ζ ε s δ := by
  obtain ⟨s, hsC, hs⟩ := ModelDecrease.exists_minimizerOn_ofJet A p hC hzero hσ
  let B := 3 * D + σ
  have hB : 0 < B := by dsimp [B]; linarith
  have htop := ModelDecrease.norm_sub_iteratedFDeriv_penalized_ofJet_le A p hσ.le
  have hlip : ∀ u v,
      ‖iteratedFDeriv ℝ p (ModelDecrease.penalized (TaylorModel.ofJet A p) p σ) u -
        iteratedFDeriv ℝ p (ModelDecrease.penalized (TaylorModel.ofJet A p) p σ) v‖ ≤
          B * ‖u - v‖ := fun u v => (htop u v).trans
            (mul_le_mul_of_nonneg_right (by dsimp [B]; linarith) (norm_nonneg _))
  obtain ⟨δ, hδ⟩ := exists_constrained_stepComputation_of_isMinOn
    (ModelDecrease.contDiff_penalized_ofJet A p p le_rfl σ) hB hlip
    (fun n hn hnp x hx => ModelDecrease.norm_iteratedFDeriv_penalized_ofJet_le_three_mul_add
      A hnp hσ.le (zero_le_one.trans hD) (fun i hni hip => hA i (hn.trans hni) hip) hx)
    hC hconv order horder hθ hζ hζ1 ε hε s hsC hs
  exact ⟨s, δ, hδ⟩


/-- One fixed positive coefficient, before every feasible set, jet, penalty
parameter and accuracy vector, bounds all radii of a genuinely constructed
finite constrained detailed model computation. -/
theorem exists_uniform_penalized_constrained_stepComputation (p : ℕ)
    {D S : ℝ} (hD : 1 ≤ D) (hS : 0 ≤ S) :
    ∃ κ > 0, κ ≤ 1 ∧ ∀ {C : Set E}, IsClosed C → Convex ℝ C → (0 : E) ∈ C →
      ∀ (A : FormalMultilinearSeries ℝ E ℝ),
        (∀ i, 2 ≤ i → i ≤ p → ‖A i‖ ≤ D) →
      ∀ σ : ℝ, 0 < σ → σ ≤ S →
      ∀ θ ζ : ℝ, 0 < θ → θ ≤ 1 → 0 < ζ → ζ ≤ 1 →
      ∀ (order : ι → ℕ), (∀ a, 0 < order a ∧ order a ≤ p) →
      ∀ (ε : ι → ℝ), (∀ a, 0 < ε a ∧ ε a ≤ 1) →
      ∃ (s : E) (δ : ι → ℝ),
        ConstrainedStepComputation (ModelDecrease.penalized (TaylorModel.ofJet A p) p σ)
          C order θ ζ ε s δ ∧ ∀ a, κ * (ζ * θ * ε a) ≤ δ a := by
  let κ := 1 / (8 * (3 * D + S))
  have hden : 1 ≤ 8 * (3 * D + S) := by linarith
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hκ1 : κ ≤ 1 := (div_le_one (by linarith)).mpr hden
  refine ⟨κ, hκ, hκ1, ?_⟩
  intro C hC hconv hzero A hA σ hσ hσS θ ζ hθ hθ1 hζ hζ1 order horder ε hε
  obtain ⟨s, δ, hs⟩ := exists_penalized_constrained_stepComputation A p hC hconv hzero
    hσ hD hA order horder hθ hζ hζ1 ε (fun a => (hε a).1)
  refine ⟨s, δ, hs, fun a => ?_⟩
  by_cases hsmall : ‖s‖ ≤ 1
  · have hr := hs.radius_lower_penalized A hσ.le hD hA horder hθ hθ1 hζ1 hε hsmall a
    have hc : ζ * θ / (8 * (3 * D + S)) ≤ ζ * θ / (8 * (3 * D + σ)) :=
      div_le_div_of_nonneg_left (mul_pos hζ hθ).le (by linarith) (by linarith)
    have hh := (mul_le_mul_of_nonneg_right hc (hε a).1.le).trans hr
    convert hh using 1
    dsimp [κ]
    ring
  · have hδ : δ a = 1 := by
      rcases hs.result with ⟨_, hδ⟩ | ⟨hn, _⟩
      · exact hδ a
      · exact (hsmall hn).elim
    rw [hδ]
    have ht : ζ * θ ≤ 1 := by
      simpa only [one_mul] using mul_le_mul hζ1 hθ1 hθ.le zero_le_one
    have he : ζ * θ * ε a ≤ 1 := by
      simpa only [one_mul] using mul_le_mul ht (hε a).2 (hε a).1.le zero_le_one
    exact (mul_le_of_le_one_left (mul_pos (mul_pos hζ hθ) (hε a).1).le hκ1).trans he

end ModelSolve
