import Numlib.Optimization.InexactRegularizationRadii

/-!
# True-gap transfer for supplied regularization models

A returned short step gives actual model-gap bounds. Errors in all supplied coefficient
orders transfer these to the exact regularized model, and the Taylor remainder transfers
them to the next objective point. The checked orders remain explicit: a literal check
through `q<p` does not provide the coefficient hypotheses of this estimate.
-/

noncomputable section
open scoped Nat
namespace Optimization.InexactRegularization
open InexactTaylorModels TaylorCriticality
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- A returned short step bounds every genuine supplied-model Taylor gap. -/
theorem InnerResult.gap_le {P : Parameters} {c : ℝ} {A : Coefficients E}
    {σ : ℝ} {δ : ℕ → ℝ} {d : E} (s : InnerResult P c A σ δ d)
    (hs : ‖s.step‖ < 1) {j : ℕ} (hj : 1 ≤ j) (hjq : j ≤ P.q) :
    gapOn (taylorDecrement (regularizedPolynomial c A P.p σ) j s.step)
      (Metric.closedBall 0 (s.radii j)) ≤
        P.theta * P.epsilon j * s.radii j ^ j / (j ! : ℝ) := by
  rcases s.quality with hl | hq
  · exact (not_le_of_gt hs hl.1).elim
  · obtain ⟨d, hd, ht⟩ := hq j hj hjq
    have hf := hd.fraction_le
    have he : P.fraction * P.theta * P.epsilon j * s.radii j ^ j / (j ! : ℝ) =
        P.fraction * (P.theta * P.epsilon j * s.radii j ^ j / (j ! : ℝ)) := by ring
    rw [he] at ht
    nlinarith [P.fraction_pos]

/-- A true failed next-point criterion gives the transfer inequality from actual returned
model tests and all-order step-dependent tensor accuracy. There is no assumed step-size,
true-decrease or iteration-count conclusion. -/
theorem InnerResult.transfer_of_true_gap_failure
    {P : Parameters} {f : E → ℝ} {x : E} {A : Coefficients E} {σ S L K : ℝ}
    {δ : ℕ → ℝ} (I : Inspection P (f x) A σ δ) (hq : I.order ≤ P.q)
    (s : InnerResult P (f x) A σ I.radii (I.direction hq))
    (hf : HigherOrderRegularization.DiagonalLipschitz f P.p L)
    (hK : 0 ≤ K) (hσ : 0 ≤ σ) (hS : σ ≤ S)
    (hδ : HigherOrderApproximateRegularization.ValidRadii P.toParameters δ)
    (hs : ‖s.step‖ < 1)
    (hcoeff : ∀ i ∈ Finset.Icc 1 P.p,
      ‖A i - iteratedFDeriv ℝ i f x‖ ≤ K * P.kappaStep * ‖s.step‖ ^ (P.p - i + 1))
    (hfail : ¬HigherOrderApproximateRegularization.SatisfiesCriteria
      P.toParameters f (x + s.step) s.radii) :
    ∃ j, 1 ≤ j ∧ j ≤ P.q ∧
      (1 - P.theta) * P.epsilon j * s.radii j ^ j / (j ! : ℝ) ≤
        (L + S + 3 * K * P.kappaStep) * ∑ l ∈ Finset.Icc 1 j,
          s.radii j ^ l * ‖s.step‖ ^ (P.p - l + 1) / (l ! : ℝ) := by
  obtain ⟨j, hj, hjq, hbad⟩ :=
    HigherOrderApproximateRegularization.not_satisfiesCriteria_iff.mp hfail
  refine ⟨j, hj, hjq, ?_⟩
  have hv := s.valid_radii (I.valid_radii hδ) j hj hjq
  have hne := (s.decrement_pos I hq hσ hδ).2.2
  have hgap := gapOn_le_gapOn_add (Δ := taylorDecrement f j (x + s.step))
    (η := (L + S) * ∑ l ∈ Finset.Icc 1 j,
      s.radii j ^ l * ‖s.step‖ ^ (P.p - l + 1) / (l ! : ℝ))
    (isCompact_closedBall (0 : E) (s.radii j)) ⟨0, by simpa using hv.1.le⟩
    (continuous_taylorDecrement (HigherOrderRegularization.model f P.p x σ) j
      s.step).continuousOn (fun d hd => by
      have hb := HigherOrderApproximateRegularization.taylorDecrement_sub_model_le
        (x := x) hf (P.order_pos.trans P.order_le) (hjq.trans P.order_le)
        hne hσ hS d (by simpa using hd)
      linarith only [(abs_le.mp hb).2])
  have hpert := regularizedPolynomial_gap_error_le_step_power (hjq.trans P.order_le)
    (f x) (f x) A (fun i => iteratedFDeriv ℝ i f x) σ s.step hK P.kappaStep_pos.le
    hv.1.le hcoeff
  have he : regularizedPolynomial (f x) (fun i => iteratedFDeriv ℝ i f x) P.p σ =
      HigherOrderRegularization.model f P.p x σ := by
    funext z
    rw [regularizedPolynomial, polynomial_iteratedFDeriv]
    unfold HigherOrderRegularization.model
    ring
  rw [he] at hpert
  have hm := s.gap_le hs hj hjq
  have hbound := (abs_le.mp hpert).1
  have ht : (1 - P.theta) * P.epsilon j * s.radii j ^ j / (j ! : ℝ) =
      P.epsilon j * s.radii j ^ j / (j ! : ℝ) -
        P.theta * P.epsilon j * s.radii j ^ j / (j ! : ℝ) := by ring
  rw [ht]
  nlinarith only [hgap, hm, hbad, hbound]

end Optimization.InexactRegularization
