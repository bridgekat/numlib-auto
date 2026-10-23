import Numlib.Optimization.Regularization.Convex.FirstOrderStep
import Numlib.Optimization.Regularization.HighOrder.Origin
import Numlib.Optimization.Regularization.ModelMinimumOn

/-!
# Genuine feasible model steps for first-order constrained regularization

A positive norm-power penalty attains its minimum on the closed feasible
translation. Convex first-order optimality gives zero actual model criticality.
At an objective point with positive true criticality, the attained model value
is strictly smaller than its value at zero, so it is a permitted genuine step.
-/



namespace HighOrderRegularization
open Set TaylorModel
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The genuine model and objective constrained first-order criticalities
agree at their centers on the same actual feasible displacements. -/
theorem constrainedCriticality_model_zero {f : E → ℝ} {p : ℕ} {x : E}
    (hf : ContDiffAt ℝ p f x) (hp : 1 ≤ p) (σ : ℝ) (C : Set E) (δ : ℝ) :
    constrainedCriticality (model f p x σ) 1 (feasibleDisplacements C x) 0 δ =
      constrainedCriticality f 1 C x δ := by
  have hd : decrement (model f p x σ) 1 0 = decrement f 1 x := by
    funext d
    rw [decrement_eq, decrement_eq, model_zero, eval_model_zero hf hp]
  rw [constrainedCriticality, constrainedCriticality, hd]
  congr 2
  ext d
  simp only [Set.mem_inter_iff, mem_feasibleDisplacements, zero_add]

/-- At every feasible point with positive actual first-order measure, a genuine
nonzero feasible regularized model step exists with strict model improvement
and zero actual constrained model criticality. -/
theorem exists_constrained_first_order_step {f : E → ℝ} {p : ℕ} (hp : 1 ≤ p)
    {C : Set E} (hclosed : IsClosed C) (hconv : Convex ℝ C) {x : E} (hx : x ∈ C)
    (hf : ContDiffAt ℝ p f x) {σ : ℝ} (hσ : 0 < σ)
    (hcrit : 0 < constrainedCriticality f 1 C x 1) :
    ∃ s : E, x + s ∈ C ∧ s ≠ 0 ∧
      IsMinOn (model f p x σ) (feasibleDisplacements C x) s ∧
      model f p x σ s < model f p x σ 0 ∧
      constrainedCriticality (model f p x σ) 1 (feasibleDisplacements C x) s 1 = 0 := by
  let M := feasibleDisplacements C x
  have hM : IsClosed M := hclosed.preimage (continuous_const.add continuous_id)
  have hMconv : Convex ℝ M := by
    exact hconv.translate_preimage_right x
  have hzero : (0 : E) ∈ M := by simpa [M] using hx
  obtain ⟨s, hs, hmin⟩ := ModelDecrease.exists_minimizer_ofJet_on
    (fun j => iteratedFDeriv ℝ j f x) p hσ hM ⟨0, hzero⟩
  change IsMinOn (model f p x σ) M s at hmin
  have hdiff : Differentiable ℝ (model f p x σ) := by
    exact (ModelDecrease.contDiff_penalized_ofJet
      (fun j => iteratedFDeriv ℝ j f x) p 1 hp σ).differentiable one_ne_zero
  have hle : model f p x σ s ≤ model f p x σ 0 := hmin hzero
  have hlt : model f p x σ s < model f p x σ 0 := by
    by_contra hn
    have he : model f p x σ s = model f p x σ 0 := le_antisymm hle (not_lt.mp hn)
    have hmin0 : IsMinOn (model f p x σ) M 0 := by
      intro y hy
      rw [←he]
      exact hmin hy
    have hz := constrainedCriticality_one_eq_zero_of_isMinOn hM hMconv hzero
      hmin0 (hdiff 0) zero_le_one
    rw [constrainedCriticality_model_zero hf hp σ C 1] at hz
    exact (ne_of_gt hcrit) hz
  refine ⟨s, hs, ?_, hmin, hlt,
    constrainedCriticality_one_eq_zero_of_isMinOn hM hMconv hs hmin (hdiff s) zero_le_one⟩
  intro hz
  subst s
  exact (lt_irrefl _) hlt

end HighOrderRegularization
