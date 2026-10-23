import Numlib.Optimization.Regularization.ModelSharp
import Numlib.Optimization.Regularization.Inexact.Run

/-!
# Exact radius floors for actual inexact regularization steps

The sharp model derivative bound `3 * max D σ` gives the printed denominator
24 directly. Primitive Step1 and Step2 tests then propagate that floor through
accepted trials, rejected trials and accuracy-only iterations.
-/

namespace InexactRegularization
open InexactTrustRegion
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The exact radius coefficient from the maximum tensor and penalty bound. -/
noncomputable def stepRadiusCoefficient (ζ θ D σ : ℝ) : ℝ := ζ * θ / (24 * max D σ)

/-- The exact coefficient is positive and at most one on the algorithm's
normalized range, with a tensor cap of at least one. -/
theorem stepRadiusCoefficient_mem {ζ θ D σ : ℝ} (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hD : 1 ≤ D) :
    0 < stepRadiusCoefficient ζ θ D σ ∧ stepRadiusCoefficient ζ θ D σ ≤ 1 := by
  have hH : 1 ≤ max D σ := hD.trans (le_max_left _ _)
  have hnum : ζ * θ ≤ 1 := by nlinarith
  unfold stepRadiusCoefficient
  constructor
  · positivity
  · apply (div_le_one (by positivity : 0 < 24 * max D σ)).mpr
    linarith

/-- Actual reduction tests force the exact printed small-step radius floor,
while the first two orders keep radius one. No exact minimizer is assumed. -/
theorem StepTwoComputation.radius_lower_sharp {ι : Type*}
    {A : FormalMultilinearSeries ℝ E ℝ} {p : ℕ} {order : ι → ℕ}
    {σ θ ζ D : ℝ} {ε initial δ : ι → ℝ} {reference s : E}
    (h : StepTwoComputation A p order σ θ ζ ε reference initial s δ)
    (hσ : 0 ≤ σ) (hD : 1 ≤ D)
    (hA : ∀ i, 2 ≤ i → i ≤ p → ‖A i‖ ≤ D)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hε : ∀ a, 0 < ε a ∧ ε a ≤ 1)
    (horder : ∀ a, 0 < order a ∧ order a ≤ p) (hs : ‖s‖ < 1) (a : ι) :
    stepRadiusCoefficient ζ θ D σ * ε a ≤ δ a ∧
      (order a ≤ 2 → δ a = 1) := by
  let H := max D σ
  have hH : 0 < H := zero_lt_one.trans_le (hD.trans (le_max_left _ _))
  have hh := h.radius_lower (B := 3 * H) (by positivity)
    (ModelDecrease.contDiff_penalized_ofJet A p p le_rfl σ)
    (fun u v => (ModelDecrease.norm_sub_iteratedFDeriv_penalized_ofJet_le A p hσ u v).trans
      (mul_le_mul_of_nonneg_right (by dsimp [H]; linarith [le_max_right D σ])
        (norm_nonneg _)))
    (fun n hn hnp x hx => ModelDecrease.norm_iteratedFDeriv_penalized_ofJet_le_three_max
      A hnp hσ (fun i hni hip => hA i (by omega) hip) hx)
    horder hs a
  refine ⟨le_trans ?_ hh.1, hh.2⟩
  apply le_min
  · unfold stepRadiusCoefficient H
    ring_nf
    exact le_rfl
  · exact (mul_le_of_le_one_left (hε a).1.le
      (stepRadiusCoefficient_mem hζ hζ1 hθ hθ1 hD).2).trans (hε a).2

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
end InexactRegularization
