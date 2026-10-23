import Numlib.Optimization.Regularization.Inexact.Run

/-!
# Uniform radius floors for actual inexact regularization executions

Primitive Step1 halving failures and Step2 reduction tests each preserve a
uniform floor. Actual accepted, rejected and accuracy-only radius updates
propagate it through every finite execution. The constant precedes all
requested accuracies and computed execution data.
-/

namespace InexactRegularization
open InexactTrustRegion
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Every inherited, checked and solved radius of a genuine execution retains
a common positive accuracy coefficient. Only actual tensor and parameter caps
are supplied; all radius conclusions are derived from the operational tests. -/
theorem exists_uniform_execution_radius_floor {p q : ℕ} (P : Settings p q)
    {S M : ℝ} (hS : 0 ≤ S) (hM : 0 < M) :
    ∃ κ > 0, κ ≤ 1 ∧ ∀ (f : E → ℝ) (ε : Fin q → ℝ)
      (D : ExecutionData E q) (N : ℕ),
      Run f P ε D N → (∀ k ≤ N, D.parameter k ≤ S) →
      (∀ k ≤ N, ∀ i, 2 ≤ i → i ≤ p → ‖D.jet k i‖ ≤ M) →
      (∀ k ≤ N, ∀ a, κ * ε a ≤ D.startRadius k a) ∧
      (∀ k ≤ N, ∀ a, κ * ε a ≤ D.checkedRadius k a) ∧
      (∀ k < N, D.selected k ≠ none → ∀ a, κ * ε a ≤ D.solvedRadius k a) ∧
      (∀ k < N, D.selected k ≠ none → ‖D.step k‖ < 1 → ∀ a,
        modelOrder a ≤ 2 → D.solvedRadius k a = 1) := by
  obtain ⟨B, hB, hbounds⟩ :=
    ModelDecrease.exists_uniform_penalized_derivative_bound (E := E) p hS hM.le
  have hζ := P.zeta_pos
  have hθ := P.theta_pos
  have hqp := P.order_le
  let H := max M S
  have hH : 0 < H := hM.trans_le (le_max_left _ _)
  let κ := min 1 (min (P.zeta / (16 * H)) (P.zeta * P.theta / (8 * B)))
  have hκ : 0 < κ := lt_min zero_lt_one (lt_min (by positivity) (by positivity))
  have hκ1 : κ ≤ 1 := min_le_left _ _
  have hκcheck : κ ≤ P.zeta / (16 * H) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hκsolve : κ ≤ P.zeta * P.theta / (8 * B) :=
    (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨κ, hκ, hκ1, ?_⟩
  intro f ε D N h hparam hjet
  have hcheck : ∀ k ≤ N, (∀ a, κ * ε a ≤ D.startRadius k a) →
      ∀ a, κ * ε a ≤ D.checkedRadius k a := by
    intro k hk hprev a
    have hr := (h.step_one k hk).radius_lower P.order_le hM (h.updates.pos hk).le
      (hjet k hk) (h.startRadius_mem hk) a
    apply le_trans _ hr
    refine le_min ?_ (hprev a)
    have hmax : max M (D.parameter k) ≤ H := max_le_max le_rfl (hparam k hk)
    have hkcoef : κ ≤ P.zeta / (16 * max M (D.parameter k)) :=
      hκcheck.trans (div_le_div_of_nonneg_left P.zeta_pos.le
        (by positivity) (mul_le_mul_of_nonneg_left hmax (by norm_num)))
    have hh := mul_le_mul_of_nonneg_right hkcoef (h.accuracy_pos a).le
    simpa only [div_mul_eq_mul_div] using hh
  have hsolve : ∀ k < N, D.selected k ≠ none → ‖D.step k‖ < 1 → ∀ a,
      κ * ε a ≤ D.solvedRadius k a ∧
        (modelOrder a ≤ 2 → D.solvedRadius k a = 1) := by
    intro k hk hselected hs a
    obtain ⟨hder, hlip⟩ := hbounds (D.parameter k) (h.updates.pos hk.le).le
      (hparam k hk.le) (D.jet k) (hjet k hk.le)
    have hh := (h.step_two k hk hselected).radius_lower hB
      (ModelDecrease.contDiff_penalized_ofJet (D.jet k) p p le_rfl (D.parameter k))
      hlip hder (fun a => ⟨by unfold modelOrder; omega, by unfold modelOrder; omega⟩) hs a
    refine ⟨le_trans ?_ hh.1, hh.2⟩
    apply le_min
    · have hg := mul_le_mul_of_nonneg_right hκsolve (h.accuracy_pos a).le
      simpa only [div_mul_eq_mul_div, mul_assoc] using hg
    · exact (mul_le_of_le_one_left (h.accuracy_pos a).le hκ1).trans (h.accuracy_le_one a)
  have hstart : ∀ k ≤ N, ∀ a, κ * ε a ≤ D.startRadius k a := by
    intro k hk
    induction k with
    | zero =>
      intro a
      exact (mul_le_of_le_one_left (h.accuracy_pos a).le hκ1).trans (h.initial_radii a).1
    | succ k ih =>
      have hprev := ih (by omega)
      by_cases ht : k ∈ D.trials
      · rw [h.radius_trial k (by omega) ht]
        split_ifs with hsuccess
        · exact fun a => (hsolve k (by omega) ((h.trial_rule k (by omega)).mp ht).1
            hsuccess.2 a).1
        · exact hcheck k (by omega) hprev
      · rw [h.radius_inactive k (by omega) ht]
        exact hprev
  refine ⟨hstart, fun k hk => hcheck k hk (hstart k hk), ?_, ?_⟩
  · intro k hk hselected
    by_cases hs : ‖D.step k‖ < 1
    · exact fun a => (hsolve k hk hselected hs a).1
    · rcases (h.step_two k hk hselected).result with ⟨_, heq⟩ | ⟨hsmall, _⟩
      · rw [heq]
        exact hcheck k hk.le (hstart k hk.le)
      · exact (hs hsmall).elim
  · intro k hk hselected hs a
    exact (hsolve k hk hselected hs a).2

/-- Actual objective regularity, primitive oracle/request rules and the
corrected parameter threshold supply all caps needed for the uniform execution
radius floor. Its coefficient precedes every requested accuracy and execution. -/
theorem exists_uniform_actual_execution_radius_floor {p q : ℕ} (P : Settings p q)
    (f : E → ℝ) (hf : ContDiff ℝ p f) {L : ℝ} (hL : 1 ≤ L)
    (hlip : ∀ i, i ≤ p → ∀ x y,
      ‖iteratedFDeriv ℝ i f x - iteratedFDeriv ℝ i f y‖ ≤ L * ‖x - y‖) :
    ∃ κ > 0, κ ≤ 1 ∧ ∀ (ε : Fin q → ℝ) (D : ExecutionData E q) (N : ℕ),
      Run f P ε D N →
      (∀ k ≤ N, ∀ a, κ * ε a ≤ D.startRadius k a) ∧
      (∀ k ≤ N, ∀ a, κ * ε a ≤ D.checkedRadius k a) ∧
      (∀ k < N, D.selected k ≠ none → ∀ a, κ * ε a ≤ D.solvedRadius k a) ∧
      (∀ k < N, D.selected k ≠ none → ‖D.step k‖ < 1 → ∀ a,
        modelOrder a ≤ 2 → D.solvedRadius k a = 1) := by
  let S := max P.sigmaInitial
    (P.gamma3 * parameterCoefficient P.toOracleSettings L / (1 - P.eta2))
  let M := L + P.errorBound * P.initialCap
  have hS : 0 ≤ S :=
    (P.sigmaMin_pos.le.trans P.sigmaMin_le_initial).trans (le_max_left _ _)
  have hM : 0 < M := by
    dsimp only [M]
    have hprod := mul_nonneg P.errorBound_nonneg P.initialCap_nonneg
    linarith
  obtain ⟨κ, hκ, hκ1, hr⟩ := exists_uniform_execution_radius_floor (E := E) P hS hM
  refine ⟨κ, hκ, hκ1, ?_⟩
  intro ε D N h
  exact hr f ε D N h
    (fun k hk => h.parameter_le hf (zero_le_one.trans hL) (hlip p le_rfl) hk)
    (fun k hk i hi hip => h.tensor_norm_le (zero_le_one.trans hL)
      (fun j hj => hlip j hj.le) hk (by omega) hip)

end InexactRegularization
