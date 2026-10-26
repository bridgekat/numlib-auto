import Numlib.Optimization.TrustRegion.Inexact.Selection
import Numlib.Optimization.Regularization.Constrained.ModelMinimum
import Numlib.Optimization.Regularization.Constrained.GlobalStep
import Numlib.Optimization.Constrained.LocalCriticality
import Numlib.Optimization.Regularization.HighOrder.Origin

/-!
# Genuine constrained optimality from zero model returns

A positive feasible global-gap rule makes zero a true constrained model
minimum. The actual finite-order Peano remainder supplies positive radii;
actual model-origin derivatives transfer the certificate to the objective.
This works at every requested order and does not postulate unit second radii.
-/

namespace HighOrderRegularization
open Set TaylorModel
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Genuine objective and regularized-model Taylor criticalities agree at
their centers on exactly the same translated feasible displacement balls. -/
theorem constrainedCriticality_model_zero_order {f : E → ℝ} {p j : ℕ} {x : E}
    (hf : ContDiffAt ℝ p f x) (hjp : j ≤ p) (σ δ : ℝ) (X : Set E) :
    constrainedCriticality (model f p x σ) j (feasibleDisplacements X x) 0 δ =
      constrainedCriticality f j X x δ := by
  have hd : decrement (model f p x σ) j 0 = decrement f j x := by
    funext d
    rw [decrement_eq, decrement_eq, model_zero, eval_model_zero hf hjp]
  rw [constrainedCriticality, hd, constrainedCriticality]
  congr 1
  ext d
  simp only [feasibleDisplacements, mem_ofPred_eq, zero_add]

/-- A zero-decrease positive-fraction feasible model solve gives a true
constrained all-order approximate optimality certificate at legal positive
radii. Every model derivative and local-minimum implication is derived. -/
theorem zero_step_constrained_optimality {f : E → ℝ} {p q : ℕ} {x s : E}
    (hqp : q ≤ p) (hf : ContDiffAt ℝ p f x) {X : Set E} (hX : IsClosed X)
    (hx : x ∈ X) {σ μ : ℝ} (hμ : 0 < μ)
    (hsolve : ModelDecrease.ApproximateGlobalStepOn (model f p x σ)
      (feasibleDisplacements X x) μ s)
    (hzero : model f p x σ 0 = model f p x σ s)
    (ε : Fin q → ℝ) (hε : ∀ a, 0 < ε a) :
    ∃ δ : Fin q → ℝ, (∀ a, 0 < δ a ∧ δ a ≤ 1) ∧ ∀ a,
      constrainedCriticality f (InexactTrustRegion.modelOrder a) X x (δ a) ≤
        ε a * δ a ^ InexactTrustRegion.modelOrder a /
          (InexactTrustRegion.modelOrder a).factorial := by
  have hC : IsClosed (feasibleDisplacements X x) :=
    hX.preimage (continuous_const.add continuous_id)
  have h0 : (0 : E) ∈ feasibleDisplacements X x := by simpa using hx
  have hmin := hsolve.isMinOn_zero hμ hzero
  have haj (a : Fin q) : InexactTrustRegion.modelOrder a ≤ p := by
    have := a.isLt
    unfold InexactTrustRegion.modelOrder
    omega
  obtain ⟨δ, d, hδ, hb⟩ := exists_constrained_criticality_radii_of_isMinOn hC h0 hmin
    InexactTrustRegion.modelOrder
    (fun a => by unfold InexactTrustRegion.modelOrder; omega)
    (fun a => ModelDecrease.contDiff_penalized_ofJet (ftaylorSeries ℝ f x) p
      (InexactTrustRegion.modelOrder a) (haj a) σ)
    (θ := 1) (ζ := 1) zero_lt_one le_rfl ε hε
  refine ⟨δ, hδ, fun a => ?_⟩
  have hh := (hb a).2.2.2
  have hm : constrainedCriticality (model f p x σ) (InexactTrustRegion.modelOrder a)
      (feasibleDisplacements X x) 0 (δ a) ≤
        ε a * δ a ^ InexactTrustRegion.modelOrder a /
          (InexactTrustRegion.modelOrder a).factorial := by
    have hh' := (hb a).2.2.1.trans hh
    simpa only [one_mul] using hh'
  rwa [constrainedCriticality_model_zero_order hf (haj a)] at hm

end HighOrderRegularization

namespace ModelDecrease
open Set TaylorModel
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- An actual constrained global model minimizer and feasible attaining Taylor
directions satisfy every requested positive-order normalized criticality test.
The radii are genuinely constructed; no quantitative radius floor is asserted. -/
theorem exists_constrained_minimizer_with_criticality_ofJet {ι : Type*}
    (A : FormalMultilinearSeries ℝ E ℝ) (p : ℕ) (order : ι → ℕ)
    (horder : ∀ a, 0 < order a ∧ order a ≤ p)
    {C : Set E} (hC : IsClosed C) (hzero : (0 : E) ∈ C)
    {σ θ ζ : ℝ} (hσ : 0 < σ) (hθ : 0 < θ) (hζ : ζ ≤ 1)
    (ε : ι → ℝ) (hε : ∀ a, 0 < ε a) :
    ∃ s ∈ C, IsMinOn (penalized (ofJet A p) p σ) C s ∧
      ∃ (δ : ι → ℝ) (d : ι → E), (∀ a, 0 < δ a ∧ δ a ≤ 1) ∧ ∀ a,
        s + d a ∈ C ∧ ‖d a‖ ≤ δ a ∧
        ζ * constrainedCriticality (penalized (ofJet A p) p σ) (order a) C s (δ a) ≤
          decrement (penalized (ofJet A p) p σ) (order a) s (d a) ∧
        decrement (penalized (ofJet A p) p σ) (order a) s (d a) ≤
          θ * ε a * δ a ^ order a / (order a).factorial := by
  obtain ⟨s, hs, hmin⟩ := exists_minimizerOn_ofJet A p hC hzero hσ
  obtain ⟨δ, d, hδ, hb⟩ := exists_constrained_criticality_radii_of_isMinOn hC hs hmin
    order (fun a => (horder a).1)
    (fun a => contDiff_penalized_ofJet A p (order a) (horder a).2 σ) hθ hζ ε hε
  exact ⟨s, hs, hmin, δ, d, hδ, hb⟩

end ModelDecrease
