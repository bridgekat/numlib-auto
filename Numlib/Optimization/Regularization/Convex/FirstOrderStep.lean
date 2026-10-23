import Numlib.Optimization.Constrained.FirstOrderModel
import Numlib.Optimization.Regularization.Convex.ScaledRun
import Numlib.Optimization.Regularization.HighOrder.Step

/-!
# Actual constrained first-order step and successful-decrease bounds

Sharp Taylor derivative errors and the genuine norm-power derivative transfer
actual model criticality to original objective criticality. Scaled model tests
then give the exact factorial step and decrease constants on convex domains.
-/

namespace ConvexRegularization
open Set TaylorModel HighOrderRegularization
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The sharp genuine Taylor gradient error on the source convex domain. -/
theorem norm_first_error_le_on {p : ℕ} (hp : 1 ≤ p) {f : E → ℝ} {C S : Set E}
    (hS : IsOpen S) (hCS : C ⊆ S) (hC : Convex ℝ C) (hf : ContDiffOn ℝ p f S)
    {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ y ∈ C, ∀ z ∈ C,
      ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ L * ‖y - z‖)
    {x s : E} (hx : x ∈ C) (hxs : x + s ∈ C) :
    ‖fderiv ℝ f (x + s) - fderiv ℝ (eval f p x) s‖ ≤
      L / p.factorial * ‖s‖ ^ p := by
  have hh := norm_iteratedFDeriv_sub_eval_le_lipschitz (j := 1)
    hS hCS hC hf hL hlip hp hx hxs
  rw [show p - 1 + 1 = p by omega] at hh
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  have ht := (iteratedFDeriv ℝ 1 f (x + s) -
    iteratedFDeriv ℝ 1 (eval f p x) s).le_opNorm (fun _ => v)
  simp only [sub_apply, iteratedFDeriv_one_apply, Fin.prod_const, pow_one] at ht
  have hm := mul_le_mul_of_nonneg_right hh (norm_nonneg v)
  convert ht.trans hm using 1
  ring

/-- The actual regularized-model derivative error includes the genuine
norm-power penalty with its exact source factorial coefficient. -/
theorem norm_model_first_error_le_on {p : ℕ} (hp : 1 ≤ p) {f : E → ℝ} {C S : Set E}
    (hS : IsOpen S) (hCS : C ⊆ S) (hC : Convex ℝ C) (hf : ContDiffOn ℝ p f S)
    {L σ : ℝ} (hL : 0 ≤ L) (hσ : 0 ≤ σ)
    (hlip : ∀ y ∈ C, ∀ z ∈ C,
      ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ L * ‖y - z‖)
    {x s : E} (hx : x ∈ C) (hxs : x + s ∈ C) (hs : s ≠ 0) :
    ‖fderiv ℝ f (x + s) - fderiv ℝ (model f p x σ) s‖ ≤
      (L + σ) / p.factorial * ‖s‖ ^ p := by
  rw [fderiv_model f p x σ hs]
  have he : fderiv ℝ f (x + s) -
      (fderiv ℝ (eval f p x) s +
        (σ / (p + 1).factorial) • fderiv ℝ (fun z : E => ‖z‖ ^ (p + 1)) s) =
      (fderiv ℝ f (x + s) - fderiv ℝ (eval f p x) s) -
        (σ / (p + 1).factorial) • fderiv ℝ (fun z : E => ‖z‖ ^ (p + 1)) s := by abel
  rw [he]
  exact (norm_sub_le _ _).trans ((add_le_add
    (norm_first_error_le_on hp hS hCS hC hf hL hlip hx hxs)
    (norm_first_penalty hp hσ s).le).trans_eq (by ring))

variable [ProperSpace E] {p : ℕ} {f : E → ℝ} {C S : Set E} {P : Settings p}
  {ε L : ℝ} {D : Data E} {N : ℕ}

/-- The actual endpoint criticality has the precise first-order multiplier
used in the source scaled-step bound. -/
theorem ScaledRun.trial_criticality_le (h : ScaledRun f C P ε D N)
    (hclosed : IsClosed C) (hS : IsOpen S) (hCS : C ⊆ S) (hC : Convex ℝ C)
    (hf : ContDiffOn ℝ p f S) (hL : 0 ≤ L)
    (hlip : ∀ y ∈ C, ∀ z ∈ C,
      ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ L * ‖y - z‖)
    {i : ℕ} (hi : i < N) :
    constrainedCriticality f 1 C (D.point i + D.step i) 1 ≤
      ((L + D.parameter i) / p.factorial + P.theta) * ‖D.step i‖ ^ p := by
  have hb := constrainedCriticality_one_le_model (f := f)
    (m := model f p (D.point i) (D.parameter i)) hclosed (h.feasible_trial i hi)
  have he := norm_model_first_error_le_on P.order_pos hS hCS hC hf hL
    (h.modelTrace.updates.pos hi.le).le hlip (h.mem hi.le) (h.feasible_trial i hi)
    (h.modelTrace.step_ne_zero hi)
  exact (hb.trans (add_le_add (h.model_test i hi) he)).trans_eq (by ring)

/-- The accepted actual step bounds the endpoint constrained measure with the
exact printed coefficient from(4.1.31). -/
theorem ScaledRun.step_lower (h : ScaledRun f C P ε D N)
    (hclosed : IsClosed C) (hS : IsOpen S) (hCS : C ⊆ S) (hC : Convex ℝ C)
    (hf : ContDiffOn ℝ p f S) (hL : 0 < L)
    (hlip : ∀ y ∈ C, ∀ z ∈ C,
      ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ L * ‖y - z‖)
    {i : ℕ} (hi : i < N) (hs : P.eta1 ≤ D.ratio i) :
    stepConstant p L (max P.sigmaInitial (P.gamma3 * L / (1 - P.eta2))) P.theta *
      constrainedCriticality f 1 C (D.point (i + 1)) 1 ≤ ‖D.step i‖ ^ p := by
  rw [h.modelTrace.successful_point hi hs]
  apply stepConstant_mul_le hL
    (P.sigmaMin_pos.le.trans (P.sigmaMin_le_initial.trans (le_max_left _ _)))
    (by have := P.theta_lower; have := P.tau_pos; linarith)
    (h.parameter_le hS hCS hC hf hL.le hlip hi.le) (pow_nonneg (norm_nonneg _) _)
  exact h.trial_criticality_le hclosed hS hCS hC hf hL.le hlip hi

/-- Every successful scaled-test iteration gives the full source decrease in
the actual endpoint constrained criticality, with the exact κ₁ of(4.1.32). -/
theorem ScaledRun.successful_decrease (h : ScaledRun f C P ε D N)
    (hclosed : IsClosed C) (hS : IsOpen S) (hCS : C ⊆ S) (hC : Convex ℝ C)
    (hf : ContDiffOn ℝ p f S) (hL : 0 < L)
    (hlip : ∀ y ∈ C, ∀ z ∈ C,
      ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ L * ‖y - z‖)
    {i : ℕ} (hi : i < N) (hs : P.eta1 ≤ D.ratio i) :
    decreaseConstant p p P.eta1 P.sigmaMin L
      (max P.sigmaInitial (P.gamma3 * L / (1 - P.eta2))) P.theta *
      constrainedCriticality f 1 C (D.point (i + 1)) 1 ^ (((p + 1 : ℕ) : ℝ) / p) ≤
        f (D.point i) - f (D.point (i + 1)) := by
  exact h.modelTrace.decrease_of_step_lower hi hs P.order_pos
    (stepConstant_pos p hL
      (P.sigmaMin_pos.le.trans (P.sigmaMin_le_initial.trans (le_max_left _ _)))
      (by have := P.theta_lower; have := P.tau_pos; linarith)).le
    (constrainedCriticality_nonneg f 1 hclosed (h.mem (by omega)) zero_le_one)
    (h.step_lower hclosed hS hCS hC hf hL hlip hi hs)

end ConvexRegularization
