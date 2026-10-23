import Numlib.Optimization.Regularization.Inexact.CriticalityError
import Numlib.Optimization.Regularization.Inexact.RunVerified

/-!
# True-criticality obstructions after actual successful regularization trials

The literal short-step guard gives all-degree relative tensor errors. Actual
point and radius updates transfer the computed model tests to the next
iterate. Failure of true approximate optimality there forces the weighted
step-power inequality used by the complexity argument.
-/

namespace InexactRegularization
open InexactTrustRegion
section General
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {p q : ℕ} {f : E → ℝ} {P : Settings p q} {ε : Fin q → ℝ}
  {D : ExecutionData E q} {N : ℕ}

/-- The actual short-step request guard yields the sharper source tensor-error
coefficient `errorBound*stepCoefficient`, through every model derivative order. -/
theorem Run.short_tensor_error (h : Run f P ε D N) {k : ℕ} (hk : k < N)
    (ht : k ∈ D.trials) (hs : ‖D.step k‖ < 1) {i : ℕ} (hi : 1 ≤ i) (hip : i ≤ p) :
    ‖D.jet k i - iteratedFDeriv ℝ i f (D.point k)‖ ≤
      (P.errorBound * P.stepCoefficient) * ‖D.step k‖ ^ (p - i + 1) := by
  have hr := h.toModelTrace.short_request k hk ht hs i hi hip
  have hh := (h.oracle_all k hk.le i hi hip).trans
    (mul_le_mul_of_nonneg_left hr (P.errorCoefficient_nonneg i hi hip))
  have hc := mul_le_mul_of_nonneg_right (P.errorCoefficient_le i hi hip)
    (mul_nonneg P.stepCoefficient_pos.le (pow_nonneg (norm_nonneg (D.step k)) (p - i + 1)))
  exact hh.trans (by simpa only [mul_assoc] using hc)

end General
section Hilbert
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {p q : ℕ} {f : E → ℝ} {P : Settings p q} {ε : Fin q → ℝ}
  {D : ExecutionData E q} {N : ℕ}

/-- Failure of true approximate optimality after an actual successful short
trial forces the source weighted step-power obstruction in some order. The
only parameter bound is a genuine current cap; no model-derivative identity,
criticality comparison or step-length conclusion is assumed. -/
theorem Run.criticality_obstruction (h : Run f P ε D N) (hf : ContDiff ℝ p f)
    {L S : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ u v, ‖iteratedFDeriv ℝ p f u - iteratedFDeriv ℝ p f v‖ ≤ L * ‖u - v‖)
    {k : ℕ} (hk : k < N) (ht : k ∈ D.trials) (haccepted : P.eta1 ≤ D.ratio k)
    (hs : ‖D.step k‖ < 1) (hS : D.parameter k ≤ S)
    (hnot : ¬OptimalityAt f ε (D.point (k + 1)) (D.startRadius (k + 1))) :
    ∃ a, (1 - P.theta) * ε a * D.startRadius (k + 1) a ^ modelOrder a /
        (modelOrder a).factorial ≤
      (L + S + 3 * P.errorBound * P.stepCoefficient) *
        ∑ i ∈ Finset.range (modelOrder a), D.startRadius (k + 1) a ^ (i + 1) *
          ‖D.step k‖ ^ (p - (i + 1) + 1) / (i + 1).factorial := by
  classical
  have hk1 : k + 1 ≤ N := by omega
  have hpoint : D.point (k + 1) = D.point k + D.step k := by
    rw [h.point_trial k hk ht, ite_eq_left haccepted]
  have hradius : D.startRadius (k + 1) = D.solvedRadius k := by
    rw [h.radius_trial k hk ht, ite_eq_left ⟨haccepted, hs⟩]
  have hfail : ∃ a, ε a * D.startRadius (k + 1) a ^ modelOrder a /
      (modelOrder a).factorial <
        TaylorModel.criticality f (modelOrder a) (D.point (k + 1))
          (D.startRadius (k + 1) a) := by
    by_contra hn
    have hh : ∀ a, TaylorModel.criticality f (modelOrder a) (D.point (k + 1))
        (D.startRadius (k + 1) a) ≤ ε a * D.startRadius (k + 1) a ^ modelOrder a /
          (modelOrder a).factorial := fun a => not_lt.mp (fun ha => hn ⟨a, ha⟩)
    exact hnot ⟨h.startRadius_mem hk1, hh⟩
  obtain ⟨a, ha⟩ := hfail
  refine ⟨a, ?_⟩
  rw [hpoint, hradius] at ha
  rw [hradius]
  have hq := P.order_le
  have horder : modelOrder a ≤ p := by unfold modelOrder; omega
  have hδ : 0 ≤ D.solvedRadius k a := by
    rw [←hradius]
    exact (h.startRadius_mem hk1 a).1.le
  have hK := mul_nonneg P.errorBound_nonneg P.stepCoefficient_pos.le
  have herr := criticality_le_model_add_error f hf horder hL hK (h.updates.pos hk.le).le hδ
    hlip (D.jet k) (D.point k) (D.step k) (fun i hi hip => h.short_tensor_error hk ht hs hi hip)
  have hm := (h.step_two k hk ((h.trial_rule k hk).mp ht).1).criticality P.zeta_pos hs a
  change TaylorModel.criticality
    (ModelDecrease.penalized (TaylorModel.ofJet (D.jet k) p) p (D.parameter k))
    (modelOrder a) (D.step k) (D.solvedRadius k a) ≤
      P.theta * ε a * D.solvedRadius k a ^ modelOrder a / (modelOrder a).factorial at hm
  have hsum : 0 ≤ ∑ i ∈ Finset.range (modelOrder a), D.solvedRadius k a ^ (i + 1) *
      ‖D.step k‖ ^ (p - (i + 1) + 1) / (i + 1).factorial :=
    Finset.sum_nonneg fun _ _ => by positivity
  have hcap := mul_le_mul_of_nonneg_right
    (show L + D.parameter k + 3 * (P.errorBound * P.stepCoefficient) ≤
      L + S + 3 * P.errorBound * P.stepCoefficient by nlinarith) hsum
  have he : (1 - P.theta) * ε a * D.solvedRadius k a ^ modelOrder a /
      (modelOrder a).factorial = ε a * D.solvedRadius k a ^ modelOrder a /
        (modelOrder a).factorial -
          P.theta * ε a * D.solvedRadius k a ^ modelOrder a / (modelOrder a).factorial := by ring
  rw [he]
  linarith

end Hilbert
end InexactRegularization
