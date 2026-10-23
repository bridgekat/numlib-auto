import Numlib.Optimization.Regularization.Inexact.Explicit.Run
import Numlib.Optimization.Regularization.Inexact.SharpFloors

/-!
# Derived sharp EDA execution radius floors

Primitive Step1 and Step2 halving guards preserve the sharp common floor
through actual approximate-objective acceptance, rejection and accuracy-only
updates. No parameter acceptance formula is required in this propagation.
-/

namespace InexactRegularization.Explicit
open InexactTrustRegion
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

namespace Run
variable {p q : ℕ} {f : E → ℝ} {P : Settings p q} {ε : Fin q → ℝ}
  {D : ExecutionData E q} {N : ℕ}

/-- Every actual inherited, checked and solved radius retains the exact
coefficient fixed by a cap on the penalty parameters in this finite prefix. -/
theorem radius_floor_sharp (h : Run f P ε D N) {M S : ℝ} (hM : 1 ≤ M)
    (hparam : ∀ k ≤ N, D.parameter k ≤ S)
    (hjet : ∀ k ≤ N, ∀ i, 2 ≤ i → i ≤ p → ‖D.jet k i‖ ≤ M) :
    (∀ k ≤ N, ∀ a, stepRadiusCoefficient P.zeta P.theta M S * ε a ≤
      D.startRadius k a) ∧
    (∀ k ≤ N, ∀ a, stepRadiusCoefficient P.zeta P.theta M S * ε a ≤
      D.checkedRadius k a) ∧
    (∀ k < N, D.selected k ≠ none → ∀ a,
      stepRadiusCoefficient P.zeta P.theta M S * ε a ≤ D.solvedRadius k a) ∧
    (∀ k < N, D.selected k ≠ none → ‖D.step k‖ < 1 → ∀ a,
      modelOrder a ≤ 2 → D.solvedRadius k a = 1) := by
  let H := max M S
  let κ := stepRadiusCoefficient P.zeta P.theta M S
  have hH : 0 < H := zero_lt_one.trans_le (hM.trans (le_max_left _ _))
  have hκ := stepRadiusCoefficient_mem (σ := S) P.zeta_pos P.zeta_le_one P.theta_pos
    P.theta_lt_one.le hM
  have hκcheck : κ ≤ P.zeta / (16 * H) := by
    have hprod : P.zeta * P.theta ≤ P.zeta :=
      mul_le_of_le_one_right P.zeta_pos.le P.theta_lt_one.le
    calc κ ≤ P.zeta / (24 * H) :=
          div_le_div_of_nonneg_right hprod (by positivity)
      _ ≤ P.zeta / (16 * H) := div_le_div_of_nonneg_left P.zeta_pos.le
          (by positivity) (by nlinarith)
  have hqp := P.order_le
  have hcheck : ∀ k ≤ N, (∀ a, κ * ε a ≤ D.startRadius k a) →
      ∀ a, κ * ε a ≤ D.checkedRadius k a := by
    intro k hk hprev a
    have hr := (h.step_one k hk).radius_lower P.order_le (zero_lt_one.trans_le hM)
      (h.updates.pos hk).le (hjet k hk) (h.startRadius_mem hk) a
    apply le_trans _ hr
    refine le_min ?_ (hprev a)
    have hmax : max M (D.parameter k) ≤ H := max_le_max le_rfl (hparam k hk)
    have hc : κ ≤ P.zeta / (16 * max M (D.parameter k)) :=
      hκcheck.trans (div_le_div_of_nonneg_left P.zeta_pos.le
        (by positivity) (mul_le_mul_of_nonneg_left hmax (by norm_num)))
    simpa only [div_mul_eq_mul_div] using
      mul_le_mul_of_nonneg_right hc (h.accuracy_pos a).le
  have hsolve : ∀ k < N, D.selected k ≠ none → ‖D.step k‖ < 1 → ∀ a,
      κ * ε a ≤ D.solvedRadius k a ∧
        (modelOrder a ≤ 2 → D.solvedRadius k a = 1) := by
    intro k hk hselected hs a
    have hr := (h.step_two k hk hselected).radius_lower_sharp (h.updates.pos hk.le).le hM
      (hjet k hk.le) P.theta_pos P.theta_lt_one.le P.zeta_pos P.zeta_le_one
      (fun a => ⟨h.accuracy_pos a, h.accuracy_le_one a⟩)
      (fun a => ⟨by unfold modelOrder; omega, by unfold modelOrder; omega⟩) hs a
    refine ⟨le_trans ?_ hr.1, hr.2⟩
    apply mul_le_mul_of_nonneg_right _ (h.accuracy_pos a).le
    unfold stepRadiusCoefficient
    exact div_le_div_of_nonneg_left (mul_nonneg P.zeta_pos.le P.theta_pos.le)
      (by positivity) (mul_le_mul_of_nonneg_left
        (max_le_max le_rfl (hparam k hk.le)) (by norm_num))
  have hstart : ∀ k ≤ N, ∀ a, κ * ε a ≤ D.startRadius k a := by
    intro k hk
    induction k with
    | zero =>
      intro a
      exact (mul_le_of_le_one_left (h.accuracy_pos a).le hκ.2).trans (h.initial_radii a).1
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

end Run
end InexactRegularization.Explicit
