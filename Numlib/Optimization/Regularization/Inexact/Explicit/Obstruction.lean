import Numlib.Optimization.Regularization.Inexact.Explicit.Selection
import Numlib.Optimization.Regularization.Inexact.CriticalityError

/-!
# Computed criticality errors after explicit-accuracy trials

Successful short trials preserve all derivative requests. Their literal request
guard controls both the old model errors and the fresh oracle at the next point.
Consequently the next computed jet has a genuine all-order comparison with the
actual regularized model, including its penalty derivatives.
-/

namespace InexactRegularization.Explicit
open InexactTrustRegion
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
namespace Run
variable {p q : ℕ} {f : E → ℝ} {P : Settings p q} {ε : Fin q → ℝ}
  {D : ExecutionData E q} {N : ℕ}

/-- Actual short-step requests control the next computed derivative's error
relative to the current regularized model at its accepted step. -/
theorem next_jet_sub_model_le (h : Run f P ε D N) (hf : ContDiff ℝ p f)
    {L S : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ u v, ‖iteratedFDeriv ℝ p f u - iteratedFDeriv ℝ p f v‖ ≤ L * ‖u - v‖)
    {k i : ℕ} (hk : k < N) (ht : k ∈ D.trials) (ha : P.eta1 ≤ D.ratio k)
    (hs : ‖D.step k‖ < 1) (hS : D.parameter k ≤ S) (hi : 1 ≤ i) (hip : i ≤ p) :
    ‖D.jet (k + 1) i - iteratedFDeriv ℝ i
      (model (D.jet k) p (D.parameter k)) (D.step k)‖ ≤
        (L + S + 4 * P.stepCoefficient) * ‖D.step k‖ ^ (p - i + 1) := by
  have hreq := h.toFunctionTrace.short_request k hk ht hs
  have herr : ∀ j, 1 ≤ j → j ≤ p →
      ‖D.jet k j - iteratedFDeriv ℝ j f (D.point k)‖ ≤
        P.stepCoefficient * ‖D.step k‖ ^ (p - j + 1) :=
    fun j hj hjp => (h.oracle_le_request hk.le hj hjp).trans (hreq j hj hjp)
  have hm := norm_derivative_sub_model_le_power f hf hi hip hL
    P.stepCoefficient_pos.le (h.updates.pos hk.le).le hlip
    (D.jet k) (D.point k) (D.step k) herr
  have hn := h.oracle_le_request (show k + 1 ≤ N by omega) hi hip
  rw [h.accuracy_trial k hk ht i hi hip,
    h.point_trial k hk ht, ite_eq_left ha] at hn
  have hnext := hn.trans (hreq i hi hip)
  have heq : D.jet (k + 1) i -
      iteratedFDeriv ℝ i (model (D.jet k) p (D.parameter k)) (D.step k) =
      (D.jet (k + 1) i - iteratedFDeriv ℝ i f (D.point k + D.step k)) +
      (iteratedFDeriv ℝ i f (D.point k + D.step k) -
        iteratedFDeriv ℝ i (model (D.jet k) p (D.parameter k)) (D.step k)) := by abel
  rw [heq]
  apply (norm_add_le _ _).trans
  have hpow := pow_nonneg (norm_nonneg (D.step k)) (p - i + 1)
  change ‖iteratedFDeriv ℝ i f (D.point k + D.step k) -
    iteratedFDeriv ℝ i (model (D.jet k) p (D.parameter k)) (D.step k)‖ ≤ _ at hm
  nlinarith

/-- The next computed criticality is controlled by the actual current model
criticality and a weighted trial-length error with a fixed genuine cap. -/
theorem next_criticality_le_model_add_error (h : Run f P ε D N) (hf : ContDiff ℝ p f)
    {L S δ : ℝ} (hL : 0 ≤ L) (hδ : 0 ≤ δ)
    (hlip : ∀ u v, ‖iteratedFDeriv ℝ p f u - iteratedFDeriv ℝ p f v‖ ≤ L * ‖u - v‖)
    {k j : ℕ} (hk : k < N) (ht : k ∈ D.trials) (ha : P.eta1 ≤ D.ratio k)
    (hs : ‖D.step k‖ < 1) (hS : D.parameter k ≤ S) (hjp : j ≤ p) :
    TaylorModel.jetCriticality (D.jet (k + 1)) j δ ≤
      TaylorModel.criticality (model (D.jet k) p (D.parameter k)) j (D.step k) δ +
        (L + S + 4 * P.stepCoefficient) *
          ∑ i ∈ Finset.range j, δ ^ (i + 1) * ‖D.step k‖ ^ (p - (i + 1) + 1) /
            (i + 1).factorial := by
  have hh := TaylorModel.abs_jetCriticality_sub_le (D.jet (k + 1))
    (ftaylorSeries ℝ (model (D.jet k) p (D.parameter k)) (D.step k)) j hδ
    (fun i => (L + S + 4 * P.stepCoefficient) * ‖D.step k‖ ^ (p - i + 1))
    (fun i hi hij => h.next_jet_sub_model_le hf hL hlip hk ht ha hs hS hi (hij.trans hjp))
  simp only [TaylorModel.jetCriticality_ftaylorSeries] at hh
  have he : (∑ i ∈ Finset.range j,
      (L + S + 4 * P.stepCoefficient) * ‖D.step k‖ ^ (p - (i + 1) + 1) *
        δ ^ (i + 1) / (i + 1).factorial) =
      (L + S + 4 * P.stepCoefficient) *
        ∑ i ∈ Finset.range j, δ ^ (i + 1) * ‖D.step k‖ ^ (p - (i + 1) + 1) /
          (i + 1).factorial := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he] at hh
  have hu := (abs_le.mp hh).2
  linarith


/-- Failure of the literal next stopping check forces an effective-margin
obstruction at an inherited radius. Initial computed failure and explicit
budget failure are both derived from the actual ordered check. -/
theorem nonstopping_obstruction (h : Run f P ε D N) (hf : ContDiff ℝ p f)
    {L S : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ u v, ‖iteratedFDeriv ℝ p f u - iteratedFDeriv ℝ p f v‖ ≤ L * ‖u - v‖)
    {k : ℕ} (hk : k < N) (ht : k ∈ D.trials) (ha : P.eta1 ≤ D.ratio k)
    (hs : ‖D.step k‖ < 1) (hS : D.parameter k ≤ S)
    (hnot : ¬StopsAt P ε D (k + 1)) :
    ∃ a, (P.zeta / 2 - P.theta) * ε a * D.startRadius (k + 1) a ^ modelOrder a /
        (modelOrder a).factorial ≤
      (L + S + 4 * P.stepCoefficient) *
        ∑ i ∈ Finset.range (modelOrder a), D.startRadius (k + 1) a ^ (i + 1) *
          ‖D.step k‖ ^ (p - (i + 1) + 1) / (i + 1).factorial := by
  classical
  have hk1 : k + 1 ≤ N := by omega
  have hrad : D.startRadius (k + 1) = D.solvedRadius k := by
    rw [h.radius_trial k hk ht, ite_eq_left ⟨ha, hs⟩]
  have hmodel : ∀ a, TaylorModel.criticality (model (D.jet k) p (D.parameter k))
      (modelOrder a) (D.step k) (D.startRadius (k + 1) a) ≤
      P.theta * ε a * D.startRadius (k + 1) a ^ modelOrder a /
        (modelOrder a).factorial := by
    intro a
    rw [hrad]
    exact (h.step_two k hk ((h.trial_rule k hk).mp ht).1).criticality P.zeta_pos hs a
  rcases (h.step_one (k + 1) hk1).initial_alternative with hbad | ⟨hnone, _, heq⟩
  · obtain ⟨a, hfail⟩ := hbad
    refine ⟨a, ?_⟩
    have hfeas := (h.step_one (k + 1) hk1).feasible a 0
    simp only [BacktrackingGradient.step, pow_zero, div_one] at hfeas
    have hcrit := TaylorModel.jetDecrement_le_jetCriticality (D.jet (k + 1))
      (modelOrder a) hfeas
    have hq := P.order_le
    have horder : modelOrder a ≤ p := by unfold modelOrder; omega
    have herr := h.next_criticality_le_model_add_error hf hL
      (h.startRadius_mem hk1 a).1.le hlip hk ht ha hs hS horder
    have hm := hmodel a
    have he : (P.zeta / 2 - P.theta) * ε a *
        D.startRadius (k + 1) a ^ modelOrder a / (modelOrder a).factorial =
        P.zeta / 2 * ε a * D.startRadius (k + 1) a ^ modelOrder a /
          (modelOrder a).factorial - P.theta * ε a *
            D.startRadius (k + 1) a ^ modelOrder a / (modelOrder a).factorial := by ring
    rw [he]
    linarith
  · have hfail : ∃ a, P.zeta / 2 * ε a * D.startRadius (k + 1) a ^ modelOrder a /
        (modelOrder a).factorial <
          tensorErrorBudget (D.accuracy (k + 1)) (modelOrder a)
            (D.startRadius (k + 1) a) := by
      by_contra hn
      apply hnot
      refine ⟨hnone, ?_⟩
      intro a
      rw [heq]
      exact not_lt.mp (fun hb => hn ⟨a, hb⟩)
    obtain ⟨a, hfail⟩ := hfail
    refine ⟨a, ?_⟩
    have hreq := h.toFunctionTrace.short_request k hk ht hs
    have hb : tensorErrorBudget (D.accuracy (k + 1)) (modelOrder a)
        (D.startRadius (k + 1) a) ≤ P.stepCoefficient *
          ∑ i ∈ Finset.range (modelOrder a), D.startRadius (k + 1) a ^ (i + 1) *
            ‖D.step k‖ ^ (p - (i + 1) + 1) / (i + 1).factorial := by
      unfold tensorErrorBudget
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i hi
      have hiq : i + 1 ≤ q := by
        have := Finset.mem_range.mp hi
        unfold modelOrder at this
        omega
      rw [h.accuracy_trial k hk ht (i + 1) (by omega) (hiq.trans P.order_le)]
      have hh := mul_le_mul_of_nonneg_right
        (hreq (i + 1) (by omega) (hiq.trans P.order_le))
        (pow_nonneg (h.startRadius_mem hk1 a).1.le (i + 1))
      have hh' := div_le_div_of_nonneg_right hh
        (Nat.cast_nonneg (i + 1).factorial : (0 : ℝ) ≤ (i + 1).factorial)
      convert hh' using 1; ring
    have hS0 : 0 ≤ S := (h.updates.pos hk.le).le.trans hS
    have hsum : 0 ≤ ∑ i ∈ Finset.range (modelOrder a),
        D.startRadius (k + 1) a ^ (i + 1) *
          ‖D.step k‖ ^ (p - (i + 1) + 1) / (i + 1).factorial :=
      Finset.sum_nonneg fun _ _ => by
        have := (h.startRadius_mem hk1 a).1
        positivity
    have hc := mul_le_mul_of_nonneg_right
      (show P.stepCoefficient ≤ L + S + 4 * P.stepCoefficient by
        have := P.stepCoefficient_pos; linarith) hsum
    have ht0 : 0 ≤ P.theta * ε a * D.startRadius (k + 1) a ^ modelOrder a /
        (modelOrder a).factorial := by
      have := P.theta_pos
      have := h.accuracy_pos a
      have := (h.startRadius_mem hk1 a).1
      positivity
    have he : (P.zeta / 2 - P.theta) * ε a *
        D.startRadius (k + 1) a ^ modelOrder a / (modelOrder a).factorial =
        P.zeta / 2 * ε a * D.startRadius (k + 1) a ^ modelOrder a /
          (modelOrder a).factorial - P.theta * ε a *
            D.startRadius (k + 1) a ^ modelOrder a / (modelOrder a).factorial := by ring
    rw [he]
    linarith

end Run
end InexactRegularization.Explicit
