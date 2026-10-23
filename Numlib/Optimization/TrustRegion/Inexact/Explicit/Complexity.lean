import Numlib.Optimization.TrustRegion.Inexact.Explicit.Run
/-!
# Literal stopping and evaluation complexity for explicit trust regions

Actual accepted objective decreases bound successful trials. The operational
radius floor bounds all trials, and verified computed checks bound accuracy-only
iterations before literal stopping. An Archimedean argument gives the first
actual stop. Every complexity coefficient is fixed before all requested
accuracies and execution data. Objective requests exclude initialization;
positive-order derivative requests include it.
-/

namespace InexactTrustRegion.Explicit
open Set EvaluationComplexity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
/-- At most two objective evaluations occur on each trial; Step0 omits the initial
  objective call. -/
noncomputable def functionEvaluations (T : Set ℕ) (N : ℕ) : ℕ :=
  2 * (successfulIterations T N).card
namespace Run
variable {q : ℕ} {f : E → ℝ} {P : Settings q} {ε : Fin q → ℝ}
  {D : ExecutionData E q} {N : ℕ}
/-- Actual accepted EDA trials have a fixed positive true objective decrease coefficient. -/
theorem function_decrease (h : Run f P ε D N) (hf : ContDiff ℝ q f) {L : ℝ} (hL : 1 ≤ L)
    (hlip : ∀ a, 1 ≤ a → a ≤ q → ∀ u v,
      ‖iteratedFDeriv ℝ a f u - iteratedFDeriv ℝ a f v‖ ≤ L * ‖u - v‖)
    {i : ℕ} (hi : i < N) (hT : i ∈ D.trials) (haccept : P.eta1 ≤ D.ratio i) :
    P.eta1 * (P.zeta * (positiveRadiusCoefficient P.toImplicit L / 2)) ^ (q + 1) /
      (2 * (q.factorial : ℝ)) * minimumAccuracy P.order_pos ε ^ (q + 1) ≤
        f (D.point i) - f (D.point (i + 1)) := by
  have hκ := positiveRadiusCoefficient_properties P.toImplicit hL
  have hupper := hκ.2.2
  simp only [P.known_unit_bound, mul_one] at hupper
  exact h.toFunctionModelTrace.function_decrease hf hL hlip hκ.1.le hupper
    P.function_acceptance_margin h.point_trial hi hT haccept
/-- Rejected and accuracy-only iterations preserve the actual objective value. -/
theorem objective_eq_of_not_successful (h : Run f P ε D N)
    {i : ℕ} (hi : i < N) (hS : i ∉ successfulSet D.trials D.ratio P.eta1) :
    f (D.point (i + 1)) = f (D.point i) := by
  by_cases hT : i ∈ D.trials
  · rw [h.point_trial i hi hT, ite_eq_right (fun ha => hS ⟨hT, ha⟩)]
  · rw [h.point_inactive i hi hT]
/-- The bounded-below objective and actual accepted decreases bound all successful trials. -/
theorem successful_card_le (h : Run f P ε D N) (hf : ContDiff ℝ q f) {L flow : ℝ}
  (hL : 1 ≤ L)
    (hlip : ∀ a, 1 ≤ a → a ≤ q → ∀ u v,
      ‖iteratedFDeriv ℝ a f u - iteratedFDeriv ℝ a f v‖ ≤ L * ‖u - v‖)
    (hlow : flow ≤ f (D.point N)) :
    ((successfulIterations (successfulSet D.trials D.ratio P.eta1) N).card : ℝ) ≤
      successfulConstant P.toImplicit L * (f (D.point 0) - flow) /
        minimumAccuracy P.order_pos ε ^ (q + 1) := by
  let κ := positiveRadiusCoefficient P.toImplicit L
  let μ := minimumAccuracy P.order_pos ε
  let d := P.eta1 * (P.zeta * (κ / 2)) ^ (q + 1) /
    (2 * (q.factorial : ℝ)) * μ ^ (q + 1)
  have hκ := positiveRadiusCoefficient_properties P.toImplicit hL
  have hμ := minimumAccuracy_pos P.order_pos h.accuracy_pos
  have hη := P.eta1_pos
  have hζ := P.zeta_pos
  have hκpos := hκ.1
  have hd : 0 < d := by dsimp [d]; positivity
  have hb := card_successful_le_gap_div (S := successfulSet D.trials D.ratio P.eta1)
    (f := fun i => f (D.point i)) (k := N) hd hlow
    (fun i hi hS => h.function_decrease hf hL hlip hi hS.1 hS.2)
    (fun i hi hS => (h.objective_eq_of_not_successful hi hS).le)
  convert hb using 1
  unfold successfulConstant
  dsimp [d, κ, μ]
  field_simp
/-- Actual geometric accuracy reductions give a logarithmic budget before literal stopping. -/
theorem accuracy_card_le (h : Run f P ε D N) (hf : ContDiff ℝ q f) {L : ℝ} (hL : 1 ≤ L)
    (hlip : ∀ a, a ≤ q → ∀ u v,
      ‖iteratedFDeriv ℝ a f u - iteratedFDeriv ℝ a f v‖ ≤ L * ‖u - v‖) :
    ((successfulIterations D.trialsᶜ N).card : ℝ) ≤
      (q * (q + 1) : ℕ) * |Real.log (minimumAccuracy P.order_pos ε)| / |Real.log P.reduction| +
        |Real.log (accuracyCoefficient P.toImplicit L / P.initialCap)| / |Real.log
          P.reduction| + 1 := by
  let μ := minimumAccuracy P.order_pos ε
  let τ := accuracyCoefficient P.toImplicit L * μ ^ (q * (q + 1))
  have hμ := minimumAccuracy_pos P.order_pos h.accuracy_pos
  have hcoef := accuracyCoefficient_pos P.toImplicit hL
  have hτ : 0 < τ := mul_pos hcoef (pow_pos hμ _)
  have hu : AccuracyUpdates D.trialsᶜ (accuracyCap P.toImplicit D.trials) P.reduction
    N := accuracyCap_updates
  have hb := hu.reductions_le hτ (fun i hi hT =>
    h.accuracy_branch_large hf hL hlip hi hT )
  have hinit : accuracyCap P.toImplicit D.trials 0 = P.initialCap := by simp
    [accuracyCap, successfulIterations]
  rw [hinit] at hb
  have heq : Real.log (τ / P.initialCap) =
      (q * (q + 1) : ℕ) * Real.log μ + Real.log (accuracyCoefficient P.toImplicit L /
        P.initialCap) := by
    rw [Real.log_div hτ.ne' P.initialCap_pos.ne']
    dsimp [τ]
    rw [Real.log_mul hcoef.ne' (pow_pos hμ _).ne', Real.log_pow,
      Real.log_div hcoef.ne' P.initialCap_pos.ne']
    ring
  have habs : |Real.log (τ / P.initialCap)| ≤
      (q * (q + 1) : ℕ) * |Real.log μ| +
        |Real.log (accuracyCoefficient P.toImplicit L / P.initialCap)| := by
    rw [heq]
    have hn : |((q * (q + 1) : ℕ) : ℝ)| = ((q * (q + 1) : ℕ) : ℝ) :=
      abs_of_nonneg (Nat.cast_nonneg _)
    simpa only [abs_mul, hn] using
      abs_add_le (((q * (q + 1) : ℕ) : ℝ) * Real.log μ)
        (Real.log (accuracyCoefficient P.toImplicit L / P.initialCap))
  have hp := (abs_pos.mpr (Real.log_neg P.reduction_pos P.reduction_lt_one).ne).le
  have hd := div_le_div_of_nonneg_right habs hp
  dsimp [μ] at hd
  calc _ ≤ 1 + |Real.log (τ / P.initialCap)| / |Real.log P.reduction| := hb
    _ ≤ _ := by rw [add_div] at hd; linarith
/-- Actual radius updates and the proved endpoint floor bound all objective trials. -/
theorem trial_card_le (h : Run f P ε D N) (hf : ContDiff ℝ q f) {L flow : ℝ} (hL : 1 ≤ L)
    (hlip : ∀ a, 1 ≤ a → a ≤ q → ∀ u v,
      ‖iteratedFDeriv ℝ a f u - iteratedFDeriv ℝ a f v‖ ≤ L * ‖u - v‖)
    (hlow : flow ≤ f (D.point N)) :
    ((successfulIterations D.trials N).card : ℝ) ≤
      successfulConstant P.toImplicit L * HighOrderTrustRegion.iterationFactor P.gamma2 P.gamma3 *
        (f (D.point 0) - flow) / minimumAccuracy P.order_pos ε ^ (q + 1) +
      |Real.log (minimumAccuracy P.order_pos ε)| / |Real.log P.gamma2| +
      |Real.log (P.zeta * (positiveRadiusCoefficient P.toImplicit L / 2) / D.radius 0)| /
        |Real.log P.gamma2| := by
  let μ := minimumAccuracy P.order_pos ε
  let κ := positiveRadiusCoefficient P.toImplicit L / 2
  let δmin := P.zeta * κ * μ
  have hκp := positiveRadiusCoefficient_properties P.toImplicit hL
  have hκ : 0 < κ := div_pos hκp.1 (by norm_num)
  have hμ : 0 < μ := minimumAccuracy_pos P.order_pos h.accuracy_pos
  have hζ := P.zeta_pos
  have hδmin : 0 < δmin := by dsimp [δmin]; positivity
  have hfloor : δmin ≤ D.radius N := (h.radius_floor hf hL hlip le_rfl).trans (min_le_right _ _)
  have hb := iteration_bound_of_parameter_lower_on_trials
    (S := successfulSet D.trials D.ratio P.eta1) (T := D.trials) (δ := D.radius)
    (fun _ hi => hi.1) (fun i hi => h.updates.pos hi)
    (lt_of_lt_of_le (by norm_num) P.one_le_gamma3)
    (P.gamma1_pos.trans_le P.gamma1_le_gamma2) P.gamma2_lt_one hfloor hδmin
    (fun i hi hS => h.updates.successful_le hi hS.1 hS.2)
    (fun i hi hT hS => h.updates.unsuccessful_le hi hT (fun ha => hS ⟨hT, ha⟩))
    (fun i hi hT => h.updates.inactive_eq hi hT)
  have hs := h.successful_card_le hf hL hlip hlow
  have hγlog : 0 ≤ Real.log P.gamma3 := Real.log_nonneg P.one_le_gamma3
  have hfactor : 0 ≤ HighOrderTrustRegion.iterationFactor P.gamma2 P.gamma3 := by
    unfold HighOrderTrustRegion.iterationFactor
    positivity
  have hh := mul_le_mul_of_nonneg_right hs hfactor
  have hfixed : 0 < P.zeta * κ / D.radius 0 := div_pos (mul_pos P.zeta_pos hκ)
    h.updates.initial_pos
  have heq : Real.log (δmin / D.radius 0) = Real.log μ + Real.log (P.zeta * κ / D.radius 0) := by
    have hid : δmin / D.radius 0 = μ * (P.zeta * κ / D.radius 0) := by dsimp [δmin]; ring
    rw [hid, Real.log_mul hμ.ne' hfixed.ne']
  have hlog := abs_add_le (Real.log μ) (Real.log (P.zeta * κ / D.radius 0))
  rw [← heq] at hlog
  have hdiv := div_le_div_of_nonneg_right hlog (abs_nonneg (Real.log P.gamma2))
  dsimp [μ, κ] at hdiv
  have hsum := add_le_add hh hdiv
  dsimp [HighOrderTrustRegion.iterationFactor] at hsum
  calc _ ≤ (successfulIterations (successfulSet D.trials D.ratio P.eta1) N).card *
        (1 + Real.log P.gamma3 / |Real.log P.gamma2|) +
        |Real.log (δmin / D.radius 0)| / |Real.log P.gamma2| := hb
    _ ≤ _ := by
      rw [add_div] at hsum
      dsimp [HighOrderTrustRegion.iterationFactor]
      convert hsum using 1; ring

/-- The trial and accuracy-only budgets bound every iteration before literal stopping. -/
theorem iterations_le (h : Run f P ε D N) (hf : ContDiff ℝ q f) {L flow : ℝ} (hL : 1 ≤ L)
    (hlip : ∀ a, a ≤ q → ∀ u v,
      ‖iteratedFDeriv ℝ a f u - iteratedFDeriv ℝ a f v‖ ≤ L * ‖u - v‖)
    (hlow : flow ≤ f (D.point N)) :
    (N : ℝ) ≤
      successfulConstant P.toImplicit L * HighOrderTrustRegion.iterationFactor P.gamma2 P.gamma3 *
        (f (D.point 0) - flow) / minimumAccuracy P.order_pos ε ^ (q + 1) +
      |Real.log (minimumAccuracy P.order_pos ε)| / |Real.log P.gamma2| +
      |Real.log (P.zeta * (positiveRadiusCoefficient P.toImplicit L / 2) / D.radius 0)| /
        |Real.log P.gamma2| +
      (q * (q + 1) : ℕ) * |Real.log (minimumAccuracy P.order_pos ε)| / |Real.log P.reduction| +
      |Real.log (accuracyCoefficient P.toImplicit L / P.initialCap)| / |Real.log
        P.reduction| + 1 := by
  have ht := h.trial_card_le hf hL (fun a _ ha => hlip a ha) hlow
  have ha := h.accuracy_card_le hf hL hlip
  have hp : (N : ℝ) = (successfulIterations D.trials N).card +
      (successfulIterations D.trialsᶜ N).card := by
    exact_mod_cast (card_successful_add_card_unsuccessful D.trials N).symm
  rw [hp]
  linarith
/-- Two actual objective requests per trial give the complete objective-evaluation budget. -/
theorem functionEvaluations_le (h : Run f P ε D N) (hf : ContDiff ℝ q f)
    {L flow : ℝ} (hL : 1 ≤ L)
    (hlip : ∀ a, 1 ≤ a → a ≤ q → ∀ u v,
      ‖iteratedFDeriv ℝ a f u - iteratedFDeriv ℝ a f v‖ ≤ L * ‖u - v‖)
    (hlow : flow ≤ f (D.point N)) :
    (functionEvaluations D.trials N : ℝ) ≤
      2 * successfulConstant P.toImplicit L * HighOrderTrustRegion.iterationFactor
        P.gamma2 P.gamma3 *
        (f (D.point 0) - flow) / minimumAccuracy P.order_pos ε ^ (q + 1) +
      2 * |Real.log (minimumAccuracy P.order_pos ε)| / |Real.log P.gamma2| +
      2 * |Real.log (P.zeta * (positiveRadiusCoefficient P.toImplicit L / 2) / D.radius 0)| /
        |Real.log P.gamma2| := by
  have ht := h.trial_card_le hf hL hlip hlow
  simp only [functionEvaluations, Nat.cast_mul, Nat.cast_ofNat]
  have hh := mul_le_mul_of_nonneg_left ht (by norm_num : (0 : ℝ) ≤ 2)
  convert hh using 1; ring
/-- Derivative requests count initialization, accepted endpoints and accuracy improvements,
including the last threshold-crossing reduction. -/
theorem derivativeEvaluations_le (h : Run f P ε D N) (hf : ContDiff ℝ q f)
    {L flow : ℝ} (hL : 1 ≤ L)
    (hlip : ∀ a, a ≤ q → ∀ u v,
      ‖iteratedFDeriv ℝ a f u - iteratedFDeriv ℝ a f v‖ ≤ L * ‖u - v‖)
    (hlow : flow ≤ f (D.point N)) :
    (InexactTrustRegion.derivativeEvaluations D.trials D.ratio P.eta1 N : ℝ) ≤
      successfulConstant P.toImplicit L * (f (D.point 0) - flow) /
        minimumAccuracy P.order_pos ε ^ (q + 1) +
      (q * (q + 1) : ℕ) * |Real.log (minimumAccuracy P.order_pos ε)| / |Real.log P.reduction| +
      |Real.log (accuracyCoefficient P.toImplicit L / P.initialCap)| / |Real.log
        P.reduction| + 2 := by
  have hs := h.successful_card_le hf hL (fun a _ ha => hlip a ha) hlow
  have ha := h.accuracy_card_le hf hL hlip
  simp only [InexactTrustRegion.derivativeEvaluations, Nat.cast_add, Nat.cast_one]
  linarith
end Run
/-- Consistent primitive executions reach a first actual verified stopping index finitely. -/
theorem exists_stopping {q : ℕ} {f : E → ℝ} {P : Settings q}
    {ε : Fin q → ℝ} {D : ExecutionData E q}
    (hprefix : ∀ N, (∀ i < N, ¬StopsAt P ε D i) → Run f P ε D N)
    (hf : ContDiff ℝ q f) {L flow : ℝ} (hL : 1 ≤ L)
    (hlip : ∀ a, a ≤ q → ∀ u v,
      ‖iteratedFDeriv ℝ a f u - iteratedFDeriv ℝ a f v‖ ≤ L * ‖u - v‖)
    (hlow : ∀ y, flow ≤ f y) :
    ∃ K, StopsAt P ε D K ∧ Run f P ε D K ∧ ∀ i < K, ¬StopsAt P ε D i := by
  classical
  have hex : ∃ K, StopsAt P ε D K := by
    by_contra hn
    push Not at hn
    let μ := minimumAccuracy P.order_pos ε
    let bound := successfulConstant P.toImplicit L *
      HighOrderTrustRegion.iterationFactor P.gamma2 P.gamma3 * (f (D.point 0) - flow) /
        μ ^ (q + 1) + |Real.log μ| / |Real.log P.gamma2| +
      |Real.log (P.zeta * (positiveRadiusCoefficient P.toImplicit L / 2) / D.radius 0)| /
        |Real.log P.gamma2| +
      (q * (q + 1) : ℕ) * |Real.log μ| / |Real.log P.reduction| +
      |Real.log (accuracyCoefficient P.toImplicit L / P.initialCap)| / |Real.log P.reduction| + 1
    obtain ⟨N, hN⟩ := exists_nat_gt bound
    have h := (hprefix N (fun i _ => hn i)).iterations_le hf hL hlip (hlow _)
    exact (not_le_of_gt hN) h
  refine ⟨Nat.find hex, Nat.find_spec hex, hprefix _ ?_, ?_⟩ <;>
    intro i hi <;> exact Nat.find_min hex hi

variable [ProperSpace E]
/-- Full uniform TRqEDA evaluation complexity: all positive constants precede every
accuracy request and execution. The first literal stop certifies all true Taylor
criticality measures at its legal actual radius. Objective counts use at most
two requests per trial; derivative counts include initialization. -/
theorem evaluation_complexity {q : ℕ} (f : E → ℝ) (P : Settings q) (x₀ : E)
    {Δ₀ L flow : ℝ} (hL : 1 ≤ L) (hf : ContDiff ℝ q f)
    (hlip : ∀ a, a ≤ q → ∀ u v,
      ‖iteratedFDeriv ℝ a f u - iteratedFDeriv ℝ a f v‖ ≤ L * ‖u - v‖)
    (hlow : ∀ y, flow ≤ f y) :
    ∃ κA > 0, ∃ κB > 0, ∃ κC > 0, ∃ κE > 0, ∃ κF > 0,
      ∀ (ε : Fin q → ℝ) (D : ExecutionData E q),
      D.point 0 = x₀ → D.radius 0 = Δ₀ →
      (∀ N, (∀ i < N, ¬StopsAt P ε D i) → Run f P ε D N) →
      ∃ K, StopsAt P ε D K ∧ optimalityRadius P.theta (D.radius K) ∈ Ioc 0 1 ∧
        (∀ a : Fin q, TaylorModel.criticality f (modelOrder a) (D.point K)
          (optimalityRadius P.theta (D.radius K)) ≤
            ε a * optimalityRadius P.theta (D.radius K) ^ modelOrder a / (modelOrder
              a).factorial) ∧
        Run f P ε D K ∧ (∀ i < K, ¬StopsAt P ε D i) ∧
        (functionEvaluations D.trials K : ℝ) ≤
          κA * (f x₀ - flow) / minimumAccuracy P.order_pos ε ^ (q + 1) +
          κB * |Real.log (minimumAccuracy P.order_pos ε)| + κC ∧
        (InexactTrustRegion.derivativeEvaluations D.trials D.ratio P.eta1 K : ℝ) ≤
          κA * (f x₀ - flow) / minimumAccuracy P.order_pos ε ^ (q + 1) +
          κE * |Real.log (minimumAccuracy P.order_pos ε)| + κF := by
  let κ := positiveRadiusCoefficient P.toImplicit L / 2
  let F := HighOrderTrustRegion.iterationFactor P.gamma2 P.gamma3
  let κA := 2 * successfulConstant P.toImplicit L * F
  let κB := 2 / |Real.log P.gamma2|
  let κC := 2 * |Real.log (P.zeta * κ / Δ₀)| / |Real.log P.gamma2| + 1
  let κE := ((q * (q + 1) : ℕ) : ℝ) / |Real.log P.reduction|
  let κF := |Real.log (accuracyCoefficient P.toImplicit L / P.initialCap)| /
    |Real.log P.reduction| + 2
  have hκ : 0 < κ := div_pos (positiveRadiusCoefficient_properties P.toImplicit hL).1
    (by norm_num)
  have hγ2 : 0 < P.gamma2 := P.gamma1_pos.trans_le P.gamma1_le_gamma2
  have hlog2 : 0 < |Real.log P.gamma2| := abs_pos.mpr (Real.log_neg hγ2 P.gamma2_lt_one).ne
  have hlogh : 0 < |Real.log P.reduction| :=
    abs_pos.mpr (Real.log_neg P.reduction_pos P.reduction_lt_one).ne
  have hlog3 : 0 ≤ Real.log P.gamma3 := Real.log_nonneg P.one_le_gamma3
  have hF : 1 ≤ F := by
    dsimp [F, HighOrderTrustRegion.iterationFactor]
    exact le_add_of_nonneg_right (div_nonneg hlog3 hlog2.le)
  have hS : 0 < successfulConstant P.toImplicit L := by
    have hz := P.zeta_pos
    have he := P.eta1_pos
    unfold successfulConstant
    have hh := (positiveRadiusCoefficient_properties P.toImplicit hL).1
    positivity
  have hm : (0 : ℝ) < ((q * (q + 1) : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos P.order_pos (by omega : 0 < q + 1)
  refine ⟨κA, by dsimp [κA]; positivity, κB, div_pos (by norm_num) hlog2,
    κC, by dsimp [κC]; positivity, κE, div_pos hm hlogh,
    κF, by dsimp [κF]; positivity, ?_⟩
  intro ε D hx hΔ hprefix
  obtain ⟨K, hstop, hrun, hbefore⟩ := exists_stopping hprefix hf hL hlip hlow
  have hrad : optimalityRadius P.theta (D.radius K) ∈ Ioc 0 1 :=
    ⟨lt_min P.theta_pos (hrun.updates.pos le_rfl),
      (min_le_left _ _).trans P.theta_le_one⟩
  refine ⟨K, hstop, hrad, hrun.stopped_optimality le_rfl hstop, hrun, hbefore, ?_, ?_⟩
  · have hb := hrun.functionEvaluations_le hf hL (fun a _ ha => hlip a ha) (hlow _)
    rw [hx, hΔ] at hb
    dsimp [κA, κB, κC, F, κ]
    rw [div_mul_eq_mul_div]
    linarith
  · have hb := hrun.derivativeEvaluations_le hf hL hlip (hlow _)
    rw [hx] at hb
    have hG : 0 ≤ f x₀ - flow := sub_nonneg.mpr (hlow x₀)
    have hμ := minimumAccuracy_pos P.order_pos hrun.accuracy_pos
    have hleading : successfulConstant P.toImplicit L * (f x₀ - flow) /
        minimumAccuracy P.order_pos ε ^ (q + 1) ≤
      κA * (f x₀ - flow) / minimumAccuracy P.order_pos ε ^ (q + 1) := by
      apply div_le_div_of_nonneg_right _ (pow_nonneg hμ.le _)
      apply mul_le_mul_of_nonneg_right _ hG
      dsimp [κA]
      nlinarith
    dsimp [κE, κF]
    rw [div_mul_eq_mul_div]
    linarith

end InexactTrustRegion.Explicit
