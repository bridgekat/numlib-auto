import Numlib.Optimization.Constrained.LinearRadius
import Numlib.Optimization.Regularization.Constrained.StepPowers
import Numlib.Optimization.Regularization.HighOrder.CriticalityCounting

/-!
# All-order constrained detailed-solver evaluation complexity

Derived feasible model computations, parameter caps and actual successful
objective decreases give a finite first true certificate. Every constant is
chosen before all requested accuracies and execution arrays. Counts include
the initial objective and derivative calls. Global smoothness and globally
Lipschitz derivatives are explicit correction hypotheses; local anchored
smoothness alone is not asserted to satisfy this theorem.
-/

namespace ConstrainedRegularization
open Set InexactTrustRegion EvaluationComplexity
open HighOrderRegularization
  (parameterCap parameterCap_pos trialCountFactor one_le_trialCountFactor trialCountOffset)
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
namespace Run
variable {p q : ℕ} {f : E → ℝ} {X : Set E} {P : Settings p q}
  {ε : Fin q → ℝ} {D : ExecutionData E q} {N : ℕ}

/-- A lower objective bound controls every success in a prefix whose endpoint
also precedes the target, using only actual objective decreases and updates. -/
theorem successful_card_le_of_no_target_endpoint (h : Run f X P ε D N) (hX : IsClosed X)
    (hf : ContDiff ℝ p f) {L flow : ℝ} (hL : 1 ≤ L)
    (hlip : ∀ i, 1 ≤ i → i ≤ p → ∀ y z,
      ‖iteratedFDeriv ℝ i f y - iteratedFDeriv ℝ i f z‖ ≤ L * ‖y - z‖)
    (hlow : flow ≤ f (D.point N)) (hnot : ∀ k ≤ N, ¬TargetAt f X P ε D k) :
    ((successfulIterations {i | P.eta1 ≤ D.ratio i} N).card : ℝ) ≤
      (f (D.point 0) - flow) /
        (commonDecreaseCoefficient P L (parameterCap P L) * accuracyFactor P ε) := by
  apply card_successful_le_gap_div (S := {i | P.eta1 ≤ D.ratio i})
    (f := fun i => f (D.point i)) (k := N)
    (mul_pos (commonDecreaseCoefficient_pos P hL (parameterCap_pos P L).le)
      (accuracyFactor_pos P h.accuracy_pos)) hlow
  · intro i hi hsuccess
    exact h.function_decrease_uniform hX hf hL hlip hi hsuccess (hnot (i + 1) (by omega))
  · intro i hi hsuccess
    change ¬P.eta1 ≤ D.ratio i at hsuccess
    have hx : D.point (i + 1) = D.point i := by
      rw [h.modelTrace.point_update i hi, ite_eq_right hsuccess]
    exact hx ▸ le_rfl

/-- At most one extra success first reaches the target, retaining initialized
and endpoint derivative evaluation counts. -/
theorem successful_card_le (h : Run f X P ε D N) (hX : IsClosed X)
    (hf : ContDiff ℝ p f) {L flow : ℝ} (hL : 1 ≤ L)
    (hlip : ∀ i, 1 ≤ i → i ≤ p → ∀ y z,
      ‖iteratedFDeriv ℝ i f y - iteratedFDeriv ℝ i f z‖ ≤ L * ‖y - z‖)
    (hlow : ∀ x ∈ X, flow ≤ f x) (hnot : ∀ k < N, ¬TargetAt f X P ε D k) :
    ((successfulIterations {i | P.eta1 ≤ D.ratio i} N).card : ℝ) ≤
      (f (D.point 0) - flow) /
        (commonDecreaseCoefficient P L (parameterCap P L) * accuracyFactor P ε) + 1 := by
  have hden : 0 < commonDecreaseCoefficient P L (parameterCap P L) * accuracyFactor P ε :=
    mul_pos (commonDecreaseCoefficient_pos P hL (parameterCap_pos P L).le)
      (accuracyFactor_pos P h.accuracy_pos)
  cases N with
  | zero =>
    simp only [successfulIterations, Finset.range_zero, Finset.filter_empty,
      Finset.card_empty, Nat.cast_zero]
    exact le_add_of_le_of_nonneg
      (div_nonneg (sub_nonneg.mpr (hlow _ (h.point_mem (by omega)))) hden.le) zero_le_one
  | succ n =>
    have hc := (h.restrict (Nat.le_succ n)).successful_card_le_of_no_target_endpoint hX hf
      hL hlip (hlow _ (h.point_mem (by omega))) (fun k hk => hnot k (by omega))
    have hcard : (successfulIterations {i | P.eta1 ≤ D.ratio i} (n + 1)).card ≤
        (successfulIterations {i | P.eta1 ≤ D.ratio i} n).card + 1 := by
      rw [card_successful_succ]
      split_ifs <;> omega
    have hcast : ((successfulIterations {i | P.eta1 ≤ D.ratio i} (n + 1)).card : ℝ) ≤
        (successfulIterations {i | P.eta1 ≤ D.ratio i} n).card + 1 := by exact_mod_cast hcard
    linarith


/-- Actual finite executions before the first target obey the total trial
budget derived from successful decreases and operational parameter updates. -/
theorem iterations_le {p q : ℕ} {f : E → ℝ} {P : Settings p q}
    {X : Set E} {ε : Fin q → ℝ} {D : ExecutionData E q} {N : ℕ}
    (h : Run f X P ε D N) (hX : IsClosed X) (hf : ContDiff ℝ p f) {L flow : ℝ} (hL : 1 ≤ L)
    (hlip : ∀ i, 1 ≤ i → i ≤ p → ∀ y z,
      ‖iteratedFDeriv ℝ i f y - iteratedFDeriv ℝ i f z‖ ≤ L * ‖y - z‖)
    (hlow : ∀ x ∈ X, flow ≤ f x) (hnot : ∀ k < N, ¬TargetAt f X P ε D k) :
    (N : ℝ) ≤ trialCountFactor P * ((f (D.point 0) - flow) /
      (commonDecreaseCoefficient P L (parameterCap P L) * accuracyFactor P ε) + 1) +
        trialCountOffset P L := by
  have hp : 1 ≤ p := P.order_pos.trans_le P.order_le
  have ht := iteration_bound_of_parameter_upper
    (S := {i | P.eta1 ≤ D.ratio i}) (fun i hi => h.modelTrace.updates.pos hi)
    P.gamma1_pos P.gamma1_lt_one P.one_lt_gamma2
    (h.parameter_le hf hL (hlip p hp le_rfl) le_rfl)
    (fun i hi hs => h.modelTrace.updates.successful_ge hi hs)
    (fun i hi hu => h.modelTrace.updates.unsuccessful_ge hi hu)
  rw [h.initial_parameter] at ht
  have hs := h.successful_card_le hX hf hL hlip hlow hnot
  have hfac : 0 ≤ trialCountFactor P := zero_le_one.trans (one_le_trialCountFactor P)
  have hh := mul_le_mul_of_nonneg_right hs hfac
  change (N : ℝ) ≤ (successfulIterations {i | P.eta1 ≤ D.ratio i} N).card *
    trialCountFactor P + trialCountOffset P L at ht
  exact ht.trans (by nlinarith)


end Run

/-- Every consistent actual execution reaches a first finite target.
No stopping index, decrease floor or iteration bound is assumed. -/
theorem exists_target {p q : ℕ} {f : E → ℝ} {P : Settings p q}
    {X : Set E} {ε : Fin q → ℝ} {D : ExecutionData E q}
    (hprefix : ∀ N, (∀ k < N, ¬TargetAt f X P ε D k) → Run f X P ε D N)
    (hX : IsClosed X) (hf : ContDiff ℝ p f) {L flow : ℝ} (hL : 1 ≤ L)
    (hlip : ∀ i, 1 ≤ i → i ≤ p → ∀ y z,
      ‖iteratedFDeriv ℝ i f y - iteratedFDeriv ℝ i f z‖ ≤ L * ‖y - z‖)
    (hlow : ∀ x ∈ X, flow ≤ f x) :
    ∃ K, TargetAt f X P ε D K ∧ Run f X P ε D K ∧ ∀ k < K, ¬TargetAt f X P ε D k := by
  classical
  have hex : ∃ K, TargetAt f X P ε D K := by
    by_contra hn
    push Not at hn
    let bound := trialCountFactor P * ((f (D.point 0) - flow) /
      (commonDecreaseCoefficient P L (parameterCap P L) * accuracyFactor P ε) + 1) +
        trialCountOffset P L
    obtain ⟨N, hN⟩ := exists_nat_gt bound
    have h := hprefix N (fun k _ => hn k)
    exact (not_le_of_gt hN) (h.iterations_le hX hf hL hlip hlow (fun k _ => hn k))
  exact ⟨Nat.find hex, Nat.find_spec hex, hprefix _ (fun k hk => Nat.find_min hex hk),
    fun k hk => Nat.find_min hex hk⟩


/-- Genuine constrained detailed-solver executions attain all-order Taylor
certificates with uniform initialized objective and derivative evaluation
budgets. The rate factor is min_j epsilon_j^(j(p+1)/p), including q=1's sharp
(p+1)/p rate. Constants precede all accuracies and computed executions. -/
theorem evaluation_complexity {p q : ℕ} (f : E → ℝ) (X : Set E)
    (hX : IsClosed X) (P : Settings p q) (x₀ : E) (hx₀ : x₀ ∈ X)
    (hf : ContDiff ℝ p f) {L flow : ℝ} (hL : 1 ≤ L)
    (hlip : ∀ i, 1 ≤ i → i ≤ p → ∀ y z,
      ‖iteratedFDeriv ℝ i f y - iteratedFDeriv ℝ i f z‖ ≤ L * ‖y - z‖)
    (hlow : ∀ x ∈ X, flow ≤ f x) :
    ∃ κs > 0, ∃ κa > 0, ∃ κc > 0,
      ∀ (ε : Fin q → ℝ) (D : ExecutionData E q), D.point 0 = x₀ →
      (∀ N, (∀ k < N, ¬TargetAt f X P ε D k) → Run f X P ε D N) →
      ∃ (K : ℕ) (δ : Fin q → ℝ), Run f X P ε D K ∧ TargetAt f X P ε D K ∧
        (∀ k < K, ¬TargetAt f X P ε D k) ∧ OptimalityAt f X ε (D.point K) δ ∧
        ((K + 1 : ℕ) : ℝ) ≤ κa * (f x₀ - flow) / accuracyFactor P ε + κc ∧
        (((successfulIterations {i | P.eta1 ≤ D.ratio i} K).card + 1 : ℕ) : ℝ) ≤
          κs * (f x₀ - flow) / accuracyFactor P ε + 2 := by
  let c := commonDecreaseCoefficient P L (parameterCap P L)
  let κs := 1 / c
  let κa := trialCountFactor P / c
  let κc := trialCountFactor P + |trialCountOffset P L| + 2
  have hc : 0 < c := commonDecreaseCoefficient_pos P hL (parameterCap_pos P L).le
  have hfac : 0 < trialCountFactor P := zero_lt_one.trans_le (one_le_trialCountFactor P)
  refine ⟨κs, div_pos zero_lt_one hc, κa, div_pos hfac hc, κc, by
    dsimp [κc]; positivity, ?_⟩
  intro ε D hinit hprefix
  obtain ⟨K, htarget, hrun, hfirst⟩ := exists_target hprefix hX hf hL hlip hlow
  obtain ⟨δ, hopt⟩ := hrun.target_optimality hX hf.contDiffAt htarget
  have ht := hrun.iterations_le hX hf hL hlip hlow hfirst
  have hs := hrun.successful_card_le hX hf hL hlip hlow hfirst
  rw [hinit] at ht hs
  have hrate := accuracyFactor_pos P hrun.accuracy_pos
  have hgap : 0 ≤ (f x₀ - flow) / (c * accuracyFactor P ε) :=
    div_nonneg (sub_nonneg.mpr (hlow x₀ hx₀)) (mul_pos hc hrate).le
  have hea : κa * (f x₀ - flow) / accuracyFactor P ε =
      trialCountFactor P * ((f x₀ - flow) / (c * accuracyFactor P ε)) := by
    dsimp only [κa]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hes : κs * (f x₀ - flow) / accuracyFactor P ε =
      (f x₀ - flow) / (c * accuracyFactor P ε) := by
    dsimp only [κs]
    simp only [div_eq_mul_inv, one_mul, mul_inv_rev]
    ring
  refine ⟨K, δ, hrun, htarget, hfirst, hopt, ?_, ?_⟩
  · rw [hea]
    dsimp only [κc]
    norm_num only [Nat.cast_add, Nat.cast_one]
    change (K : ℝ) ≤ trialCountFactor P *
      ((f x₀ - flow) / (c * accuracyFactor P ε) + 1) + trialCountOffset P L at ht
    nlinarith [le_abs_self (trialCountOffset P L)]
  · rw [hes]
    norm_num only [Nat.cast_add, Nat.cast_one]
    change _ ≤ (f x₀ - flow) /
      (commonDecreaseCoefficient P L (parameterCap P L) * accuracyFactor P ε) + 2
    linarith

/-- Genuine all-order constrained complexity also certifies every requested
first-order measure at the unit radius when the feasible set is convex. -/
theorem evaluation_complexity_with_unit_first {p q : ℕ} (f : E → ℝ) (X : Set E)
    (hX : IsClosed X) (hconv : Convex ℝ X) (P : Settings p q) (x₀ : E) (hx₀ : x₀ ∈ X)
    (hf : ContDiff ℝ p f) {L flow : ℝ} (hL : 1 ≤ L)
    (hlip : ∀ i, 1 ≤ i → i ≤ p → ∀ y z,
      ‖iteratedFDeriv ℝ i f y - iteratedFDeriv ℝ i f z‖ ≤ L * ‖y - z‖)
    (hlow : ∀ x ∈ X, flow ≤ f x) :
    ∃ κs > 0, ∃ κa > 0, ∃ κc > 0,
      ∀ (ε : Fin q → ℝ) (D : ExecutionData E q), D.point 0 = x₀ →
      (∀ N, (∀ k < N, ¬TargetAt f X P ε D k) → Run f X P ε D N) →
      ∃ (K : ℕ) (δ : Fin q → ℝ), Run f X P ε D K ∧ TargetAt f X P ε D K ∧
        (∀ k < K, ¬TargetAt f X P ε D k) ∧ OptimalityAt f X ε (D.point K) δ ∧
        (∀ a, modelOrder a = 1 → TaylorModel.constrainedCriticality f 1 X (D.point K) 1 ≤
          ε a) ∧
        ((K + 1 : ℕ) : ℝ) ≤ κa * (f x₀ - flow) / accuracyFactor P ε + κc ∧
        (((successfulIterations {i | P.eta1 ≤ D.ratio i} K).card + 1 : ℕ) : ℝ) ≤
          κs * (f x₀ - flow) / accuracyFactor P ε + 2 := by
  obtain ⟨κs, hs, κa, ha, κc, hc, hall⟩ :=
    evaluation_complexity f X hX P x₀ hx₀ hf hL hlip hlow
  refine ⟨κs, hs, κa, ha, κc, hc, ?_⟩
  intro ε D hinit hprefix
  obtain ⟨K, δ, hr, ht, hfirst, hopt, hF, hD⟩ := hall ε D hinit hprefix
  refine ⟨K, δ, hr, ht, hfirst, hopt, ?_, hF, hD⟩
  intro a hj
  have hb := hopt.2.2 a
  rw [hj, pow_one, Nat.factorial_one, Nat.cast_one, div_one] at hb
  exact TaylorModel.constrainedCriticality_one_unit_le_of_radius hX hconv hopt.1
    (hopt.2.1 a).1 (hopt.2.1 a).2 hb

end ConstrainedRegularization
