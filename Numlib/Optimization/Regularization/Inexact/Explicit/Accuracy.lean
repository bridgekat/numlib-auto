import Numlib.Optimization.Regularization.Inexact.Explicit.Radius
import Numlib.Optimization.Regularization.Inexact.RunAccuracy

/-!
# Actual explicit-accuracy reduction budgets

Once the positive geometric request envelope is below the fixed request and
verification cutoff, every accuracy-only branch passes the literal EDA stop.
Thus failed stopping checks bound the number of genuine accuracy reductions.
-/

namespace InexactRegularization.Explicit
open InexactTrustRegion EvaluationComplexity Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace Run
variable {p q : ℕ} {f : E → ℝ} {P : Settings p q} {ε : Fin q → ℝ}
  {D : ExecutionData E q} {N : ℕ}

/-- Every actual request lies below the positive geometric envelope, even if
some or all initial requests are zero. -/
theorem request_le_envelope (h : Run f P ε D N) {k i : ℕ} (hk : k ≤ N)
    (hi : 1 ≤ i) (hip : i ≤ p) : D.accuracy k i ≤ accuracyEnvelope P.toSettings
      D.trials k := by
  classical
  have hu := accuracyEnvelope_updates P.toSettings D.trials N
  induction k with
  | zero =>
    exact (h.initial_accuracy i hi hip).2.trans (by
      simp only [accuracyEnvelope, successfulIterations, Finset.range_zero,
        Finset.filter_empty, Finset.card_empty, pow_zero, mul_one]
      exact le_max_left _ _)
  | succ k ih =>
    have hp := ih (by omega)
    rw [hu.update k (by omega)]
    by_cases ht : k ∈ D.trials
    · rw [ite_eq_right (by simpa), h.accuracy_trial k (by omega) ht i hi hip]
      exact hp
    · rw [ite_eq_left (by simpa), h.accuracy_improvement k (by omega) ht i hi hip]
      exact mul_le_mul_of_nonneg_left hp P.reduction_pos.le


/-- Below explicit verification and request cutoffs, either actual route to
an accuracy-only iteration certifies true approximate optimality at the actual
checked radii. The radius floor is a theorem prerequisite, not a trace field. -/
theorem accuracy_only_implies_stop (h : Run f P ε D N)
    {κ M K H : ℝ} (hκ : 0 ≤ κ) (hκ1 : κ ≤ 1) (hM : 1 ≤ M)
    (hK : 0 < K) (hKbound : P.errorBound ≤ K) (hH : 0 ≤ H)
    {k : ℕ} (hk : k < N) (ht : k ∉ D.trials)
    (hfloor : ∀ a, κ * ε a ≤ D.checkedRadius k a)
    (hjet : ∀ i, 1 ≤ i → i ≤ p → ‖D.jet k i‖ ≤ M)
    (haccuracy : ∀ i, 1 ≤ i → i ≤ p → D.accuracy k i ≤ H)
    (hverify : H ≤ verificationThreshold q P.zeta κ K (minimumAccuracy P.order_pos ε))
    (hrequests : H ≤ P.stepCoefficient *
      referenceStepThreshold q P.zeta κ M (minimumAccuracy P.order_pos ε) ^ p) :
    StopsAt P ε D k := by
  let μ := minimumAccuracy P.order_pos ε
  have hμ : 0 < μ := minimumAccuracy_pos P.order_pos h.accuracy_pos
  have hμ1 : μ ≤ 1 := (minimumAccuracy_le P.order_pos ε ⟨0, P.order_pos⟩).trans
    (h.accuracy_le_one _)
  have hμε : ∀ a, μ ≤ ε a := minimumAccuracy_le P.order_pos ε
  have hfloorμ : ∀ a, κ * μ ≤ D.checkedRadius k a := fun a =>
    (mul_le_mul_of_nonneg_left (hμε a) hκ).trans (hfloor a)
  by_cases hselected : D.selected k = none
  · refine ⟨hselected, ?_⟩
    intro a
    exact tensorErrorBudget_le_of_radius_floor (show modelOrder a ≤ q from a.isLt)
      (h.checkedRadius_mem hk.le a).1.le (h.checkedRadius_mem hk.le a).2 P.zeta_pos.le
      hκ hκ1 hK hμ.le hμ1 (hμε a) hH (hfloorμ a) hverify
      (D.accuracy k) (by
        intro i hi hiq
        have hip : i ≤ p := hiq.trans (show modelOrder a ≤ q from a.isLt) |>.trans P.order_le
        have hK1 : (1 : ℝ) ≤ K := by
          simpa only [P.known_error_bound] using hKbound
        exact (haccuracy i hi hip).trans (by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right hK1 hH))
  · obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp hselected
    have hone := h.step_one k hk.le
    rw [ha] at hone
    have href : P.zeta / 4 * μ * D.checkedRadius k a ^ modelOrder a /
        (modelOrder a).factorial ≤ model (D.jet k) p (D.parameter k) 0 -
          model (D.jet k) p (D.parameter k) (D.reference k) := by
      apply le_trans _ hone.outcome.2.2.1
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hμε a) (div_nonneg P.zeta_pos.le (by norm_num)))
        (pow_nonneg (h.checkedRadius_mem hk.le a).1.le _)) (Nat.cast_nonneg _)
    have hall := requests_of_reference (D.jet k) (show modelOrder a ≤ q from a.isLt)
      (h.updates.pos hk.le).le P.zeta_pos.le P.zeta_le_one hκ hκ1 hM hμ.le hμ1
      P.stepCoefficient_pos.le (hfloorμ a) (D.reference k) (D.step k) hjet href
      (h.step_two k hk hselected).comparison hrequests (D.accuracy k) haccuracy
    exact (ht ((h.trial_rule k hk).mpr ⟨hselected, Or.inr hall⟩)).elim

end Run

namespace Run
variable {p q : ℕ} {f : E → ℝ} {P : Settings p q} {ε : Fin q → ℝ}
  {D : ExecutionData E q} {N : ℕ}

/-- Before true approximate optimality, actual accuracy-only iterations are
logarithmically bounded by the explicit positive verification/request cutoff.
The positive envelope handles initially zero requests without division by zero. -/
theorem accuracy_reductions_le (h : Run f P ε D N) {κ M K : ℝ}
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hM : 1 ≤ M) (hK : 0 < K)
    (hKbound : P.errorBound ≤ K)
    (hfloor : ∀ k < N, ∀ a, κ * ε a ≤ D.checkedRadius k a)
    (hjet : ∀ k < N, ∀ i, 1 ≤ i → i ≤ p → ‖D.jet k i‖ ≤ M)
    (hnonterminal : ∀ k < N, ¬StopsAt P ε D k) :
    ((successfulIterations D.trialsᶜ N).card : ℝ) ≤ 1 +
      |Real.log (regularizedAccuracyThreshold P.toSettings κ M K (minimumAccuracy P.order_pos ε) /
        envelopeInitial P.toSettings)| / |Real.log P.reduction| := by
  let μ := minimumAccuracy P.order_pos ε
  let τ := regularizedAccuracyThreshold P.toSettings κ M K μ
  have hμ : 0 < μ := minimumAccuracy_pos P.order_pos h.accuracy_pos
  have hμ1 : μ ≤ 1 := (minimumAccuracy_le P.order_pos ε ⟨0, P.order_pos⟩).trans
    (h.accuracy_le_one _)
  have hτ : 0 < τ := regularizedAccuracyThreshold_pos P.toSettings hκ
    (zero_lt_one.trans_le hM) hK hμ
  have hu := accuracyEnvelope_updates P.toSettings D.trials N
  have hbranch : ∀ k < N, k ∈ D.trialsᶜ → τ < accuracyEnvelope P.toSettings
    D.trials k := by
    intro k hk ht
    by_contra hn
    have hsmall : accuracyEnvelope P.toSettings D.trials k ≤ τ := not_lt.mp hn
    have htarget := h.accuracy_only_implies_stop hκ.le hκ1 hM hK hKbound
      (hu.pos hk.le).le hk ht (hfloor k hk) (hjet k hk)
      (fun i hi hip => h.request_le_envelope hk.le hi hip)
      (hsmall.trans (regularizedAccuracyThreshold_le_verification P.toSettings hκ.le hK
        hμ.le hμ1))
      (hsmall.trans (regularizedAccuracyThreshold_le_requests P.toSettings hμ.le))
    exact hnonterminal k hk htarget
  have hc := hu.reductions_le hτ hbranch
  simpa only [accuracyEnvelope, successfulIterations, Finset.range_zero, Finset.filter_empty,
    Finset.card_empty, pow_zero, mul_one] using hc

end Run

namespace Run
variable {p q : ℕ} {f : E → ℝ} {P : Settings p q} {ε : Fin q → ℝ}
  {D : ExecutionData E q} {N : ℕ}

/-- Actual accuracy-only iterations have an explicit affine logarithmic bound
in the minimum requested accuracy, with fixed positive denominator and no
positivity assumption on the oracle's error bound or initial requests. -/
theorem accuracy_reductions_le_log (h : Run f P ε D N) {κ M K : ℝ}
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hM : 1 ≤ M) (hK : 0 < K)
    (hKbound : P.errorBound ≤ K)
    (hfloor : ∀ k < N, ∀ a, κ * ε a ≤ D.checkedRadius k a)
    (hjet : ∀ k < N, ∀ i, 1 ≤ i → i ≤ p → ‖D.jet k i‖ ≤ M)
    (hnonterminal : ∀ k < N, ¬StopsAt P ε D k) :
    ((successfulIterations D.trialsᶜ N).card : ℝ) ≤
      (p * (q + 1) : ℕ) / |Real.log P.reduction| *
        |Real.log (minimumAccuracy P.order_pos ε)| +
      (1 + |Real.log (regularizedAccuracyCoefficient P.toSettings κ M K / envelopeInitial
        P.toSettings)| /
        |Real.log P.reduction|) := by
  have hh := h.accuracy_reductions_le hκ hκ1 hM hK hKbound hfloor hjet hnonterminal
  have hμ := minimumAccuracy_pos P.order_pos h.accuracy_pos
  rw [log_regularizedAccuracyThreshold_ratio P.toSettings hκ (zero_lt_one.trans_le hM) hK
    hμ] at hh
  have habs := abs_add_le
    (Real.log (regularizedAccuracyCoefficient P.toSettings κ M K / envelopeInitial P.toSettings))
    ((p * (q + 1) : ℕ) * Real.log (minimumAccuracy P.order_pos ε))
  have hcast : (0 : ℝ) ≤ ((p * (q + 1) : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [abs_mul, abs_of_nonneg hcast] at habs
  apply hh.trans
  calc _ ≤ 1 + (|Real.log (regularizedAccuracyCoefficient P.toSettings κ M K /
    envelopeInitial P.toSettings)| +
        (p * (q + 1) : ℕ) * |Real.log (minimumAccuracy P.order_pos ε)|) /
          |Real.log P.reduction| := add_le_add (le_refl 1)
            (div_le_div_of_nonneg_right habs (abs_nonneg _))
    _ = _ := by ring

end Run

end InexactRegularization.Explicit
