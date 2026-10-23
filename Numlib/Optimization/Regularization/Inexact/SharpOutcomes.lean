import Numlib.Optimization.Regularization.Inexact.SharpFloors
import Numlib.Optimization.Regularization.Inexact.RunAccuracy

/-!
# Exact Step2 outcomes and trial requests in actual regularization executions

The maximum is the actual inclusive prefix maximum of the regularization
parameters. Radius conclusions include every intermediate Step1 halving.
The sufficient request condition applies after Step1 selects an order and
enters Step2; at a stationary point Step1 can instead pass directly to an
accuracy-only iteration.
-/

namespace InexactRegularization
open InexactTrustRegion
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The actual inclusive finite-prefix maximum of the parameter sequence. -/
noncomputable def prefixParameterMax (σ : ℕ → ℝ) (k : ℕ) : ℝ :=
  (Finset.range (k + 1)).sup' (by simp) σ

/-- Every actual parameter through the prefix endpoint is below its maximum. -/
theorem parameter_le_prefixParameterMax (σ : ℕ → ℝ) {i k : ℕ} (hi : i ≤ k) :
    σ i ≤ prefixParameterMax σ k :=
  Finset.le_sup' σ (Finset.mem_range.mpr (by omega))

/-- The actual prefix maximum is characterized by a common bound on all its entries. -/
theorem prefixParameterMax_le_iff (σ : ℕ → ℝ) (k : ℕ) (S : ℝ) :
    prefixParameterMax σ k ≤ S ↔ ∀ i ≤ k, σ i ≤ S := by
  unfold prefixParameterMax
  rw [Finset.sup'_le_iff]
  simp only [Finset.mem_range]
  constructor <;> intro h i hi <;> exact h i (by omega)

/-- The printed sufficient accuracy cutoff uses all derivative orders through
`p`, with the repaired all-degree request range when `q < p`. -/
noncomputable def trialAccuracyThreshold {p q : ℕ} (P : Settings p q) (M S μ : ℝ) : ℝ :=
  P.stepCoefficient *
    (P.zeta * (stepRadiusCoefficient P.zeta P.theta M S) ^ q /
      (12 * (q.factorial : ℝ) * max M S)) ^ p * μ ^ (p * (q + 1))

namespace Run
variable {p q : ℕ} {f : E → ℝ} {P : Settings p q} {ε : Fin q → ℝ}
  {D : ExecutionData E q} {N : ℕ}

omit [FiniteDimensional ℝ E] in
/-- Every intermediate Step1 halving radius lies between its actual inherited
and final checked radii. In particular the printed radius chain holds
throughout the actual Step1 loop, not only at its final output. -/
theorem intermediate_radius_bounds (h : Run f P ε D N) {k : ℕ} (hk : k ≤ N)
    (a : Fin q) {t : ℕ} (ht : t ≤ D.checkCount k a) :
    D.checkedRadius k a ≤ BacktrackingGradient.step (D.startRadius k a) t ∧
      BacktrackingGradient.step (D.startRadius k a) t ≤ D.startRadius k a := by
  have hpos := (h.startRadius_mem hk a).1.le
  constructor
  · rw [(h.step_one k hk).radius_eq a]
    exact BacktrackingGradient.step_antitone hpos ht
  · simpa only [BacktrackingGradient.step, pow_zero, div_one] using
      BacktrackingGradient.step_antitone hpos (Nat.zero_le t)

/-- The exact radius chain uses the actual inclusive parameter maximum at
this iteration; all bounds derive from the actual prefix update rules. -/
theorem radius_floor_sharp_prefix (h : Run f P ε D N) {M : ℝ} (hM : 1 ≤ M)
    (hjet : ∀ k ≤ N, ∀ i, 2 ≤ i → i ≤ p → ‖D.jet k i‖ ≤ M)
    {k : ℕ} (hk : k ≤ N) :
    (∀ a, stepRadiusCoefficient P.zeta P.theta M (prefixParameterMax D.parameter k) * ε a ≤
      D.checkedRadius k a) ∧
    (∀ a, stepRadiusCoefficient P.zeta P.theta M (prefixParameterMax D.parameter k) * ε a ≤
      D.startRadius k a) := by
  have hr := (h.restrict hk).radius_floor_sharp hM
    (fun i hi => parameter_le_prefixParameterMax D.parameter hi)
    (fun i hi => hjet i (hi.trans hk))
  exact ⟨hr.2.1 k le_rfl, hr.1 k le_rfl⟩

/-- Actual Step2 model comparison, low-order radii and the exact printed
high-order radius floor hold for every permitted small return. -/
theorem stepTwo_outcomes (h : Run f P ε D N) {M : ℝ} (hM : 1 ≤ M)
    (hjet : ∀ k ≤ N, ∀ i, 2 ≤ i → i ≤ p → ‖D.jet k i‖ ≤ M)
    {k : ℕ} (hk : k < N) (hselected : D.selected k ≠ none) :
    D.step k ≠ 0 ∧
      ((1 ≤ ‖D.step k‖ ∧ D.solvedRadius k = D.checkedRadius k) ∨
      (‖D.step k‖ < 1 ∧ ∀ a,
        TaylorModel.criticality (model (D.jet k) p (D.parameter k)) (modelOrder a)
          (D.step k) (D.solvedRadius k a) ≤
            P.theta * ε a * D.solvedRadius k a ^ modelOrder a / (modelOrder a).factorial ∧
        (modelOrder a ≤ 2 → D.solvedRadius k a = 1) ∧
        stepRadiusCoefficient P.zeta P.theta M (D.parameter k) * ε a ≤
          D.solvedRadius k a)) := by
  have htwo := h.step_two k hk hselected
  have hnonzero : D.step k ≠ 0 := by
    obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp hselected
    have hone := h.step_one k hk.le
    rw [ha] at hone
    exact htwo.nonzero (hone.reference_improvement P.zeta_pos (h.accuracy_pos a)
      (h.startRadius_mem hk.le))
  refine ⟨hnonzero, ?_⟩
  rcases htwo.result with hlarge | ⟨hs, _⟩
  · exact Or.inl hlarge
  · right
    refine ⟨hs, fun a => ⟨htwo.criticality P.zeta_pos hs a, ?_⟩⟩
    have hqp := P.order_le
    have hr := htwo.radius_lower_sharp (h.updates.pos hk.le).le hM (hjet k hk.le)
      P.theta_pos P.theta_lt_one.le P.zeta_pos P.zeta_le_one
      (fun a => ⟨h.accuracy_pos a, h.accuracy_le_one a⟩)
      (fun a => ⟨by unfold modelOrder; omega, by unfold modelOrder; omega⟩) hs a
    exact ⟨hr.2, hr.1⟩

omit [FiniteDimensional ℝ E] in
/-- Every actual short Step2 computation supplies its feasible directions and
both inequalities of the computed model-criticality test. -/
theorem stepTwo_directions (h : Run f P ε D N) {k : ℕ} (hk : k < N)
    (hselected : D.selected k ≠ none) (hs : ‖D.step k‖ < 1) :
    ∃ d : Fin q → E, ∀ a, ‖d a‖ ≤ D.solvedRadius k a ∧
      P.zeta * TaylorModel.criticality (model (D.jet k) p (D.parameter k))
        (modelOrder a) (D.step k) (D.solvedRadius k a) ≤
          TaylorModel.decrement (model (D.jet k) p (D.parameter k))
            (modelOrder a) (D.step k) (d a) ∧
      TaylorModel.decrement (model (D.jet k) p (D.parameter k))
        (modelOrder a) (D.step k) (d a) ≤
          P.zeta * P.theta * ε a * D.solvedRadius k a ^ modelOrder a /
            (modelOrder a).factorial := by
  rcases (h.step_two k hk hselected).result with hlarge | ⟨_, point, direction, count, last, hr⟩
  · exact (not_lt_of_ge hlarge.1 hs).elim
  · exact ⟨last, fun a => (hr a).2.2.2.2⟩

/-- The printed request cutoff forces a trial after Step1 actually selects an
order. This premise preserves the source's Step2 context; no trial is claimed
at an already verified stationary point passing all Step1 tests. -/
theorem trial_of_stepTwo_accuracy (h : Run f P ε D N) {M : ℝ} (hM : 1 ≤ M)
    (hjet : ∀ k ≤ N, ∀ i, 1 ≤ i → i ≤ p → ‖D.jet k i‖ ≤ M)
    {k : ℕ} (hk : k < N) (hselected : D.selected k ≠ none)
    (haccuracy : ∀ i, 1 ≤ i → i ≤ p → D.accuracy k i ≤
      trialAccuracyThreshold P M (prefixParameterMax D.parameter k)
        (minimumAccuracy P.order_pos ε)) : k ∈ D.trials := by
  let S := prefixParameterMax D.parameter k
  let H := max M S
  let κ := stepRadiusCoefficient P.zeta P.theta M S
  let μ := minimumAccuracy P.order_pos ε
  have hH : 1 ≤ H := hM.trans (le_max_left _ _)
  have hκ := stepRadiusCoefficient_mem (σ := S) P.zeta_pos P.zeta_le_one
    P.theta_pos P.theta_lt_one.le hM
  have hζ := P.zeta_pos
  have hκpos : 0 < κ := hκ.1
  have hHpos : 0 < H := zero_lt_one.trans_le hH
  have hμ : 0 < μ := minimumAccuracy_pos P.order_pos h.accuracy_pos
  have hμ1 : μ ≤ 1 := (minimumAccuracy_le P.order_pos ε ⟨0, P.order_pos⟩).trans
    (h.accuracy_le_one _)
  have hfloor := (h.radius_floor_sharp_prefix hM
    (fun k hk i hi hip => hjet k hk i (by omega) hip) hk.le).1
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp hselected
  have hone := h.step_one k hk.le
  rw [ha] at hone
  have href : P.zeta / 4 * μ * D.checkedRadius k a ^ modelOrder a /
      (modelOrder a).factorial ≤ model (D.jet k) p (D.parameter k) 0 -
        model (D.jet k) p (D.parameter k) (D.reference k) := by
    apply le_trans _ hone.outcome.2.2.1
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (minimumAccuracy_le P.order_pos ε a) (by positivity))
      (pow_nonneg (h.checkedRadius_mem hk.le a).1.le _)
  have hcut : trialAccuracyThreshold P M S μ ≤
      P.stepCoefficient * referenceStepThreshold q P.zeta κ H μ ^ p := by
    have hbase : P.zeta * κ ^ q / (12 * (q.factorial : ℝ) * H) ≤
        P.zeta * κ ^ q / (8 * (q.factorial : ℝ) * H) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (by
        have hp : 0 ≤ (q.factorial : ℝ) * H := by positivity
        nlinarith)
    unfold trialAccuracyThreshold referenceStepThreshold
    rw [mul_pow, ← pow_mul, Nat.mul_comm (q + 1) p, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hbase _)
        P.stepCoefficient_pos.le)
      (pow_nonneg hμ.le _)
  have hall := requests_of_reference (D.jet k) (show modelOrder a ≤ q from a.isLt)
    (h.updates.pos hk.le).le P.zeta_pos.le P.zeta_le_one hκ.1.le hκ.2 hH hμ.le hμ1
    P.stepCoefficient_pos.le
    ((mul_le_mul_of_nonneg_left (minimumAccuracy_le P.order_pos ε a) hκ.1.le).trans
      (hfloor a)) (D.reference k) (D.step k)
    (fun i hi hip => (hjet k hk.le i hi hip).trans (le_max_left _ _)) href
    (h.step_two k hk hselected).comparison hcut (D.accuracy k) haccuracy
  exact (h.trial_rule k hk).mpr ⟨hselected, Or.inr hall⟩

end Run
end InexactRegularization
