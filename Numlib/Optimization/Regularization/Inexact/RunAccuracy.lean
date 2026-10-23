import Numlib.Optimization.Regularization.Inexact.RunRadius
import Numlib.Optimization.EvaluationComplexity.AccuracyUpdates

/-!
# Verified criticality and accuracy-only branches of actual regularization runs

True approximate optimality uses the actual start or checked radii, both
positive and at most one. A positive geometric envelope bounds every requested
accuracy, including initially zero requests. The two genuine routes to an
accuracy-only iteration become impossible below the verification/request cutoff
unless a true approximate minimizer has already been reached.
-/

namespace InexactRegularization
open InexactTrustRegion EvaluationComplexity Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Actual normalized Taylor criticality at a vector of legal positive radii. -/
structure OptimalityAt {q : ℕ} (f : E → ℝ) (ε : Fin q → ℝ)
    (x : E) (δ : Fin q → ℝ) : Prop where
  radius_mem : ∀ a, 0 < δ a ∧ δ a ≤ 1
  criticality : ∀ a, TaylorModel.criticality f (modelOrder a) x (δ a) ≤
    ε a * δ a ^ modelOrder a / (modelOrder a).factorial

/-- A true approximate minimizer at one of the actual radius vectors produced
by the execution's current optimality check. -/
def TargetAt {q : ℕ} (f : E → ℝ)
    (ε : Fin q → ℝ) (D : ExecutionData E q) (k : ℕ) : Prop :=
  OptimalityAt f ε (D.point k) (D.startRadius k) ∨
    OptimalityAt f ε (D.point k) (D.checkedRadius k)

/-- The target is precisely true criticality at the actual start or checked radii. -/
theorem targetAt_iff {q : ℕ} (f : E → ℝ) (ε : Fin q → ℝ)
    (D : ExecutionData E q) (k : ℕ) :
    TargetAt f ε D k ↔ OptimalityAt f ε (D.point k) (D.startRadius k) ∨
      OptimalityAt f ε (D.point k) (D.checkedRadius k) := Iff.rfl

/-- A positive envelope initial cap also covers the exact-zero request case. -/
noncomputable def envelopeInitial {p q : ℕ} (P : Settings p q) : ℝ := max P.initialCap 1

/-- The geometric accuracy envelope after the actual number of accuracy-only updates. -/
noncomputable def accuracyEnvelope {p q : ℕ} (P : Settings p q) (T : Set ℕ) (k : ℕ) : ℝ :=
  envelopeInitial P * P.reduction ^ (successfulIterations Tᶜ k).card

/-- The positive envelope obeys genuine multiplicative updates on exactly the
accuracy-only iterations, for every finite prefix. -/
theorem accuracyEnvelope_updates {p q : ℕ} (P : Settings p q) (T : Set ℕ) (N : ℕ) :
    AccuracyUpdates Tᶜ (accuracyEnvelope P T) P.reduction N := by
  classical
  refine ⟨?_, P.reduction_pos, P.reduction_lt_one, ?_⟩
  · simp only [accuracyEnvelope, successfulIterations, Finset.range_zero,
      Finset.filter_empty, Finset.card_empty, pow_zero, mul_one]
    exact zero_lt_one.trans_le (le_max_right _ _)
  · intro k _
    rw [accuracyEnvelope, card_successful_succ]
    split_ifs with hk
    · rw [pow_succ]
      simp only [accuracyEnvelope]
      ring
    · simp only [Nat.add_zero, accuracyEnvelope]

namespace Run
variable {p q : ℕ} {f : E → ℝ} {P : Settings p q} {ε : Fin q → ℝ}
  {D : ExecutionData E q} {N : ℕ}

/-- Every actual request lies below the positive geometric envelope, even if
some or all initial requests are zero. -/
theorem request_le_envelope (h : Run f P ε D N) {k i : ℕ} (hk : k ≤ N)
    (hi : 1 ≤ i) (hip : i ≤ p) : D.accuracy k i ≤ accuracyEnvelope P D.trials k := by
  classical
  have hu := accuracyEnvelope_updates P D.trials N
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

variable [ProperSpace E]

/-- Below explicit verification and request cutoffs, either actual route to
an accuracy-only iteration certifies true approximate optimality at the actual
checked radii. The radius floor is a theorem prerequisite, not a trace field. -/
theorem accuracy_only_implies_target (h : Run f P ε D N)
    {κ M K H : ℝ} (hκ : 0 ≤ κ) (hκ1 : κ ≤ 1) (hM : 1 ≤ M)
    (hK : 0 < K) (hKbound : P.errorBound ≤ K) (hH : 0 ≤ H)
    {k : ℕ} (hk : k < N) (ht : k ∉ D.trials)
    (hfloor : ∀ a, κ * ε a ≤ D.checkedRadius k a)
    (hjet : ∀ i, 1 ≤ i → i ≤ p → ‖D.jet k i‖ ≤ M)
    (haccuracy : ∀ i, 1 ≤ i → i ≤ p → D.accuracy k i ≤ H)
    (hverify : H ≤ verificationThreshold q P.zeta κ K (minimumAccuracy P.order_pos ε))
    (hrequests : H ≤ P.stepCoefficient *
      referenceStepThreshold q P.zeta κ M (minimumAccuracy P.order_pos ε) ^ p) :
    TargetAt f ε D k := by
  let μ := minimumAccuracy P.order_pos ε
  have hμ : 0 < μ := minimumAccuracy_pos P.order_pos h.accuracy_pos
  have hμ1 : μ ≤ 1 := (minimumAccuracy_le P.order_pos ε ⟨0, P.order_pos⟩).trans
    (h.accuracy_le_one _)
  have hμε : ∀ a, μ ≤ ε a := minimumAccuracy_le P.order_pos ε
  have hfloorμ : ∀ a, κ * μ ≤ D.checkedRadius k a := fun a =>
    (mul_le_mul_of_nonneg_left (hμε a) hκ).trans (hfloor a)
  by_cases hselected : D.selected k = none
  · right
    have hone := h.step_one k hk.le
    rw [hselected] at hone
    refine ⟨h.checkedRadius_mem hk.le, ?_⟩
    apply hone.true_optimality P.zeta_pos P.zeta_le_one h.accuracy_pos
      (h.startRadius_mem hk.le) (fun _ => K * H) ?_ f (D.point k) ?_
    · intro a
      exact tensorErrorBudget_le_of_radius_floor (show modelOrder a ≤ q from a.isLt)
        (h.checkedRadius_mem hk.le a).1.le (h.checkedRadius_mem hk.le a).2 P.zeta_pos.le
        hκ hκ1 hK hμ.le hμ1 (hμε a) hH (hfloorμ a) hverify
        (fun _ => K * H) (fun _ _ _ => le_rfl)
    · intro i hi hiq
      have hip := hiq.trans P.order_le
      have herr := h.oracle_all k hk.le i hi hip
      exact herr.trans ((mul_le_mul_of_nonneg_left (haccuracy i hi hip)
        (P.errorCoefficient_nonneg i hi hip)).trans
          (mul_le_mul_of_nonneg_right ((P.errorCoefficient_le i hi hip).trans hKbound) hH))
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

/-- The accuracy coefficient is fixed before the requested optimality
accuracies. Its two terms enforce true verification and all-degree requests. -/
noncomputable def regularizedAccuracyCoefficient {p q : ℕ} (P : Settings p q)
    (κ M K : ℝ) : ℝ :=
  min (P.zeta * κ ^ q / (4 * (q.factorial : ℝ) * K))
    (P.stepCoefficient * (P.zeta * κ ^ q / (8 * (q.factorial : ℝ) * M)) ^ p)

/-- The common positive accuracy cutoff uses the model-degree power of the
minimum requested accuracy. -/
noncomputable def regularizedAccuracyThreshold {p q : ℕ} (P : Settings p q)
    (κ M K μ : ℝ) : ℝ := regularizedAccuracyCoefficient P κ M K * μ ^ (p * (q + 1))

/-- Positive fixed coefficients and minimum accuracy give a positive cutoff. -/
theorem regularizedAccuracyThreshold_pos {p q : ℕ} (P : Settings p q)
    {κ M K μ : ℝ} (hκ : 0 < κ) (hM : 0 < M) (hK : 0 < K) (hμ : 0 < μ) :
    0 < regularizedAccuracyThreshold P κ M K μ := by
  have hζ := P.zeta_pos
  have hκs := P.stepCoefficient_pos
  unfold regularizedAccuracyThreshold regularizedAccuracyCoefficient
  positivity

/-- The polynomial cutoff implies the per-order true-criticality verification
budget, since the model degree is positive and the accuracy is at most one. -/
theorem regularizedAccuracyThreshold_le_verification {p q : ℕ} (P : Settings p q)
    {κ M K μ : ℝ} (hκ : 0 ≤ κ) (hK : 0 < K) (hμ : 0 ≤ μ) (hμ1 : μ ≤ 1) :
    regularizedAccuracyThreshold P κ M K μ ≤ verificationThreshold q P.zeta κ K μ := by
  have hp : 1 ≤ p := P.order_pos.trans_le P.order_le
  have hexp : q + 1 ≤ p * (q + 1) := by
    simpa only [one_mul] using Nat.mul_le_mul_right (q + 1) hp
  have hpow := pow_le_pow_of_le_one hμ hμ1 hexp
  have hcoef : 0 ≤ P.zeta * κ ^ q / (4 * (q.factorial : ℝ) * K) :=
    div_nonneg (mul_nonneg P.zeta_pos.le (pow_nonneg hκ _)) (by positivity)
  unfold regularizedAccuracyThreshold regularizedAccuracyCoefficient verificationThreshold
  exact mul_le_mul (min_le_left _ _) hpow (pow_nonneg hμ _) hcoef

/-- The same polynomial cutoff enforces all relative derivative requests
through degree `p`; the exponent is `p*(q+1)`. -/
theorem regularizedAccuracyThreshold_le_requests {p q : ℕ} (P : Settings p q)
    {κ M K μ : ℝ} (hμ : 0 ≤ μ) :
    regularizedAccuracyThreshold P κ M K μ ≤
      P.stepCoefficient * referenceStepThreshold q P.zeta κ M μ ^ p := by
  unfold regularizedAccuracyThreshold regularizedAccuracyCoefficient referenceStepThreshold
  rw [mul_pow, ← pow_mul, Nat.mul_comm (q + 1) p, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (min_le_right _ _) (pow_nonneg hμ _)

namespace Run
variable {p q : ℕ} {f : E → ℝ} {P : Settings p q} {ε : Fin q → ℝ}
  {D : ExecutionData E q} {N : ℕ} [ProperSpace E]

/-- Before true approximate optimality, actual accuracy-only iterations are
logarithmically bounded by the explicit positive verification/request cutoff.
The positive envelope handles initially zero requests without division by zero. -/
theorem accuracy_reductions_le (h : Run f P ε D N) {κ M K : ℝ}
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hM : 1 ≤ M) (hK : 0 < K)
    (hKbound : P.errorBound ≤ K)
    (hfloor : ∀ k < N, ∀ a, κ * ε a ≤ D.checkedRadius k a)
    (hjet : ∀ k < N, ∀ i, 1 ≤ i → i ≤ p → ‖D.jet k i‖ ≤ M)
    (hnonterminal : ∀ k < N, ¬TargetAt f ε D k) :
    ((successfulIterations D.trialsᶜ N).card : ℝ) ≤ 1 +
      |Real.log (regularizedAccuracyThreshold P κ M K (minimumAccuracy P.order_pos ε) /
        envelopeInitial P)| / |Real.log P.reduction| := by
  let μ := minimumAccuracy P.order_pos ε
  let τ := regularizedAccuracyThreshold P κ M K μ
  have hμ : 0 < μ := minimumAccuracy_pos P.order_pos h.accuracy_pos
  have hμ1 : μ ≤ 1 := (minimumAccuracy_le P.order_pos ε ⟨0, P.order_pos⟩).trans
    (h.accuracy_le_one _)
  have hτ : 0 < τ := regularizedAccuracyThreshold_pos P hκ (zero_lt_one.trans_le hM) hK hμ
  have hu := accuracyEnvelope_updates P D.trials N
  have hbranch : ∀ k < N, k ∈ D.trialsᶜ → τ < accuracyEnvelope P D.trials k := by
    intro k hk ht
    by_contra hn
    have hsmall : accuracyEnvelope P D.trials k ≤ τ := not_lt.mp hn
    have htarget := h.accuracy_only_implies_target hκ.le hκ1 hM hK hKbound
      (hu.pos hk.le).le hk ht (hfloor k hk) (hjet k hk)
      (fun i hi hip => h.request_le_envelope hk.le hi hip)
      (hsmall.trans (regularizedAccuracyThreshold_le_verification P hκ.le hK hμ.le hμ1))
      (hsmall.trans (regularizedAccuracyThreshold_le_requests P hμ.le))
    exact hnonterminal k hk htarget
  have hc := hu.reductions_le hτ hbranch
  simpa only [accuracyEnvelope, successfulIterations, Finset.range_zero, Finset.filter_empty,
    Finset.card_empty, pow_zero, mul_one] using hc

end Run

/-- The exact cutoff ratio has an affine logarithm in the minimum requested
accuracy, with every coefficient independent of that accuracy. -/
theorem log_regularizedAccuracyThreshold_ratio {p q : ℕ} (P : Settings p q)
    {κ M K μ : ℝ} (hκ : 0 < κ) (hM : 0 < M) (hK : 0 < K) (hμ : 0 < μ) :
    Real.log (regularizedAccuracyThreshold P κ M K μ / envelopeInitial P) =
      Real.log (regularizedAccuracyCoefficient P κ M K / envelopeInitial P) +
        (p * (q + 1) : ℕ) * Real.log μ := by
  have hC : 0 < regularizedAccuracyCoefficient P κ M K := by
    simpa only [regularizedAccuracyThreshold, one_pow, mul_one] using
      regularizedAccuracyThreshold_pos P hκ hM hK zero_lt_one
  have hE : 0 < envelopeInitial P := zero_lt_one.trans_le (le_max_right _ _)
  rw [show regularizedAccuracyThreshold P κ M K μ / envelopeInitial P =
      (regularizedAccuracyCoefficient P κ M K / envelopeInitial P) * μ ^ (p * (q + 1)) by
    unfold regularizedAccuracyThreshold; ring]
  rw [Real.log_mul (div_pos hC hE).ne' (pow_pos hμ _).ne', Real.log_pow]

namespace Run
variable {p q : ℕ} {f : E → ℝ} {P : Settings p q} {ε : Fin q → ℝ}
  {D : ExecutionData E q} {N : ℕ} [ProperSpace E]

/-- Actual accuracy-only iterations have an explicit affine logarithmic bound
in the minimum requested accuracy, with fixed positive denominator and no
positivity assumption on the oracle's error bound or initial requests. -/
theorem accuracy_reductions_le_log (h : Run f P ε D N) {κ M K : ℝ}
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hM : 1 ≤ M) (hK : 0 < K)
    (hKbound : P.errorBound ≤ K)
    (hfloor : ∀ k < N, ∀ a, κ * ε a ≤ D.checkedRadius k a)
    (hjet : ∀ k < N, ∀ i, 1 ≤ i → i ≤ p → ‖D.jet k i‖ ≤ M)
    (hnonterminal : ∀ k < N, ¬TargetAt f ε D k) :
    ((successfulIterations D.trialsᶜ N).card : ℝ) ≤
      (p * (q + 1) : ℕ) / |Real.log P.reduction| *
        |Real.log (minimumAccuracy P.order_pos ε)| +
      (1 + |Real.log (regularizedAccuracyCoefficient P κ M K / envelopeInitial P)| /
        |Real.log P.reduction|) := by
  have hh := h.accuracy_reductions_le hκ hκ1 hM hK hKbound hfloor hjet hnonterminal
  have hμ := minimumAccuracy_pos P.order_pos h.accuracy_pos
  rw [log_regularizedAccuracyThreshold_ratio P hκ (zero_lt_one.trans_le hM) hK hμ] at hh
  have habs := abs_add_le
    (Real.log (regularizedAccuracyCoefficient P κ M K / envelopeInitial P))
    ((p * (q + 1) : ℕ) * Real.log (minimumAccuracy P.order_pos ε))
  have hcast : (0 : ℝ) ≤ ((p * (q + 1) : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [abs_mul, abs_of_nonneg hcast] at habs
  apply hh.trans
  calc _ ≤ 1 + (|Real.log (regularizedAccuracyCoefficient P κ M K / envelopeInitial P)| +
        (p * (q + 1) : ℕ) * |Real.log (minimumAccuracy P.order_pos ε)|) /
          |Real.log P.reduction| := add_le_add (le_refl 1)
            (div_le_div_of_nonneg_right habs (abs_nonneg _))
    _ = _ := by ring

end Run

end InexactRegularization
