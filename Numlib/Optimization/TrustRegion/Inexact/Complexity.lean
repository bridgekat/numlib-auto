import Numlib.Optimization.TrustRegion.Inexact.Run

/-!
# Finite evaluation budgets for implicit dynamic accuracy

Actual accepted objective decreases bound successful trials. Operational radius
updates bound all objective trials, while actual accuracy branches and their
multiplicative request reductions give a separate logarithmic derivative budget.
-/

namespace InexactTrustRegion
open Set EvaluationComplexity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Successful objective trials among the model-based trial set. -/
def successfulSet (T : Set ℕ) (ρ : ℕ → ℝ) (η₁ : ℝ) : Set ℕ := {i | i ∈ T
  ∧ η₁ ≤ ρ i}

/-- Objective calls consist of initialization and one actual objective trial per trial index. -/
noncomputable def functionEvaluations (T : Set ℕ) (N : ℕ) : ℕ :=
  (successfulIterations T N).card + 1

/-- Each derivative order is evaluated initially and after successes or actual
accuracy improvements. The run's unchanged-jet rule supplies rejected-step reuse. -/
noncomputable def derivativeEvaluations (T : Set ℕ) (ρ : ℕ → ℝ) (η₁ : ℝ) (N
  : ℕ) : ℕ :=
  (successfulIterations (successfulSet T ρ η₁) N).card +
    (successfulIterations Tᶜ N).card + 1

/-- Fixed reciprocal accepted-decrease coefficient, independent of requested accuracy. -/
noncomputable def successfulConstant {q : ℕ} (P : Settings q) (L : ℝ) : ℝ :=
  2 * (q.factorial : ℝ) /
    (P.eta1 * (P.zeta * (positiveRadiusCoefficient P L / 2)) ^ (q + 1))

namespace Run
variable {q : ℕ} {f : E → ℝ} {P : Settings q} {ε : Fin q → ℝ}
  {A : ℕ → FormalMultilinearSeries ℝ E ℝ} {T : Set ℕ} {j : ℕ → Fin q}
  {x d s : ℕ → E} {Δ ρ : ℕ → ℝ} {accuracy : ℕ → ℕ → ℝ} {N : ℕ}

/-- Unsuccessful and accuracy-only iterations leave the actual objective unchanged. -/
theorem objective_eq_of_not_successful (h : Run f P ε A T j x d s Δ ρ accuracy N)
    {i : ℕ} (hi : i < N) (hS : i ∉ successfulSet T ρ P.eta1) : f (x (i + 1)) = f (x i) := by
  by_cases hT : i ∈ T
  · rw [h.point_trial i hi hT, ite_eq_right (fun ha => hS ⟨hT, ha⟩)]
  · rw [h.point_inactive i hi hT]

/-- The actual objective budget bounds accepted trials by the source inverse power. -/
theorem successful_card_le (h : Run f P ε A T j x d s Δ ρ accuracy N)
    (hf : ContDiff ℝ q f) {L flow : ℝ} (hL : 1 ≤ L)
    (hlip : ∀ a, 1 ≤ a → a ≤ q → ∀ u v,
      ‖iteratedFDeriv ℝ a f u - iteratedFDeriv ℝ a f v‖ ≤ L * ‖u - v‖)
    (hlow : flow ≤ f (x N)) :
    ((successfulIterations (successfulSet T ρ P.eta1) N).card : ℝ) ≤
      successfulConstant P L * (f (x 0) - flow) / minimumAccuracy P.order_pos ε ^ (q + 1) := by
  let κ := positiveRadiusCoefficient P L
  let μ := minimumAccuracy P.order_pos ε
  let d := P.eta1 * (P.zeta * (κ / 2)) ^ (q + 1) /
    (2 * (q.factorial : ℝ)) * μ ^ (q + 1)
  have hκ := positiveRadiusCoefficient_properties P hL
  have hμ := minimumAccuracy_pos P.order_pos h.accuracy_pos
  have hη := P.eta1_pos
  have hζ := P.zeta_pos
  have hκpos := hκ.1
  have hd : 0 < d := by dsimp [d]; positivity
  have hb := card_successful_le_gap_div (S := successfulSet T ρ P.eta1)
    (f := fun i => f (x i)) (k := N) hd hlow
    (fun i hi hS => h.toExecutionTrace.function_decrease hf hL hlip
      hκ.1.le hκ.2.1 hκ.2.2 hi hS.1 hS.2)
    (fun i hi hS => (h.objective_eq_of_not_successful hi hS).le)
  convert hb using 1
  unfold successfulConstant
  dsimp [d, κ, μ]
  field_simp

end Run
variable [ProperSpace E]
namespace Run
variable {q : ℕ} {f : E → ℝ} {P : Settings q} {ε : Fin q → ℝ}
  {A : ℕ → FormalMultilinearSeries ℝ E ℝ} {T : Set ℕ} {j : ℕ → Fin q}
  {x d s : ℕ → E} {Δ ρ : ℕ → ℝ} {accuracy : ℕ → ℕ → ℝ} {N : ℕ}

/-- Actual accuracy-only branches require at most logarithmically many reductions.
The additive one includes the final reduction crossing the sufficient threshold. -/
theorem accuracy_card_le (h : Run f P ε A T j x d s Δ ρ accuracy N)
    (hf : ContDiff ℝ q f) {L : ℝ} (hL : 1 ≤ L)
    (hlip : ∀ a, a ≤ q → ∀ u v,
      ‖iteratedFDeriv ℝ a f u - iteratedFDeriv ℝ a f v‖ ≤ L * ‖u - v‖)
    (hnot : ∀ i < N, NotOptimal f ε (x i) (optimalityRadius P.theta (Δ i))) :
    ((successfulIterations Tᶜ N).card : ℝ) ≤
      (q * (q + 1) : ℕ) * |Real.log (minimumAccuracy P.order_pos ε)| / |Real.log P.reduction| +
        |Real.log (accuracyCoefficient P L / P.initialCap)| / |Real.log P.reduction| + 1 := by
  let μ := minimumAccuracy P.order_pos ε
  let τ := accuracyCoefficient P L * μ ^ (q * (q + 1))
  have hμ := minimumAccuracy_pos P.order_pos h.accuracy_pos
  have hcoef := accuracyCoefficient_pos P hL
  have hτ : 0 < τ := mul_pos hcoef (pow_pos hμ _)
  have hu : AccuracyUpdates Tᶜ (accuracyCap P T) P.reduction N := accuracyCap_updates
  have hb := hu.reductions_le hτ (fun i hi hT =>
    h.accuracy_branch_large hf hL hlip hi hT (hnot i hi))
  have hinit : accuracyCap P T 0 = P.initialCap := by simp [accuracyCap, successfulIterations]
  rw [hinit] at hb
  have heq : Real.log (τ / P.initialCap) =
      (q * (q + 1) : ℕ) * Real.log μ + Real.log (accuracyCoefficient P L / P.initialCap) := by
    rw [Real.log_div hτ.ne' P.initialCap_pos.ne']
    dsimp [τ]
    rw [Real.log_mul hcoef.ne' (pow_pos hμ _).ne', Real.log_pow,
      Real.log_div hcoef.ne' P.initialCap_pos.ne']
    ring
  have habs : |Real.log (τ / P.initialCap)| ≤
      (q * (q + 1) : ℕ) * |Real.log μ| +
        |Real.log (accuracyCoefficient P L / P.initialCap)| := by
    rw [heq]
    have hn : |((q * (q + 1) : ℕ) : ℝ)| = ((q * (q + 1) : ℕ) : ℝ) :=
      abs_of_nonneg (Nat.cast_nonneg _)
    simpa only [abs_mul, hn] using
      abs_add_le (((q * (q + 1) : ℕ) : ℝ) * Real.log μ)
        (Real.log (accuracyCoefficient P L / P.initialCap))
  have hp := (abs_pos.mpr (Real.log_neg P.reduction_pos P.reduction_lt_one).ne).le
  have hd := div_le_div_of_nonneg_right habs hp
  dsimp [μ] at hd
  calc _ ≤ 1 + |Real.log (τ / P.initialCap)| / |Real.log P.reduction| := hb
    _ ≤ _ := by rw [add_div] at hd; linarith


omit [ProperSpace E] in
/-- The actual endpoint radius and three-case updates bound objective evaluations,
including initialization, by the source inverse-power and logarithmic terms. -/
theorem functionEvaluations_le (h : Run f P ε A T j x d s Δ ρ accuracy N)
    (hf : ContDiff ℝ q f) {L flow : ℝ} (hL : 1 ≤ L)
    (hlip : ∀ a, 1 ≤ a → a ≤ q → ∀ u v,
      ‖iteratedFDeriv ℝ a f u - iteratedFDeriv ℝ a f v‖ ≤ L * ‖u - v‖)
    (hlow : flow ≤ f (x N)) :
    (functionEvaluations T N : ℝ) ≤
      successfulConstant P L * HighOrderTrustRegion.iterationFactor P.gamma2 P.gamma3 *
        (f (x 0) - flow) / minimumAccuracy P.order_pos ε ^ (q + 1) +
      |Real.log (minimumAccuracy P.order_pos ε)| / |Real.log P.gamma2| +
      |Real.log (P.zeta * (positiveRadiusCoefficient P L / 2) / Δ 0)| /
        |Real.log P.gamma2| + 1 := by
  let μ := minimumAccuracy P.order_pos ε
  let κ := positiveRadiusCoefficient P L / 2
  let δmin := P.zeta * κ * μ
  have hκp := positiveRadiusCoefficient_properties P hL
  have hκ : 0 < κ := div_pos hκp.1 (by norm_num)
  have hμ : 0 < μ := minimumAccuracy_pos P.order_pos h.accuracy_pos
  have hζ := P.zeta_pos
  have hδmin : 0 < δmin := by dsimp [δmin]; positivity
  have hfloor : δmin ≤ Δ N := (h.radius_floor hf hL hlip le_rfl).trans (min_le_right _ _)
  have hb := iteration_bound_of_parameter_lower_on_trials
    (S := successfulSet T ρ P.eta1) (T := T) (δ := Δ)
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
  have hfixed : 0 < P.zeta * κ / Δ 0 := div_pos (mul_pos P.zeta_pos hκ) h.updates.initial_pos
  have heq : Real.log (δmin / Δ 0) = Real.log μ + Real.log (P.zeta * κ / Δ 0) := by
    have hid : δmin / Δ 0 = μ * (P.zeta * κ / Δ 0) := by dsimp [δmin]; ring
    rw [hid, Real.log_mul hμ.ne' hfixed.ne']
  have hlog := abs_add_le (Real.log μ) (Real.log (P.zeta * κ / Δ 0))
  rw [← heq] at hlog
  have hdiv := div_le_div_of_nonneg_right hlog (abs_nonneg (Real.log P.gamma2))
  dsimp [μ, κ] at hdiv
  have hsum := add_le_add hh hdiv
  dsimp [HighOrderTrustRegion.iterationFactor] at hsum
  have hcard : (functionEvaluations T N : ℝ) = (successfulIterations T N).card + 1 := by
    simp only [functionEvaluations, Nat.cast_add, Nat.cast_one]
  rw [hcard]
  calc _ ≤ (successfulIterations (successfulSet T ρ P.eta1) N).card *
        (1 + Real.log P.gamma3 / |Real.log P.gamma2|) +
        |Real.log (δmin / Δ 0)| / |Real.log P.gamma2| + 1 := by linarith [hb]
    _ ≤ _ := by
      rw [add_div] at hsum
      dsimp [HighOrderTrustRegion.iterationFactor]
      convert add_le_add_right hsum 1 using 1 <;> ring

/-- Derivative calls include initialization, successful endpoints and the last
accuracy reduction; no initial or threshold-crossing evaluation is omitted. -/
theorem derivativeEvaluations_le (h : Run f P ε A T j x d s Δ ρ accuracy N)
    (hf : ContDiff ℝ q f) {L flow : ℝ} (hL : 1 ≤ L)
    (hlip : ∀ a, a ≤ q → ∀ u v,
      ‖iteratedFDeriv ℝ a f u - iteratedFDeriv ℝ a f v‖ ≤ L * ‖u - v‖)
    (hlow : flow ≤ f (x N))
    (hnot : ∀ i < N, NotOptimal f ε (x i) (optimalityRadius P.theta (Δ i))) :
    (derivativeEvaluations T ρ P.eta1 N : ℝ) ≤
      successfulConstant P L * (f (x 0) - flow) / minimumAccuracy P.order_pos ε ^ (q + 1) +
      (q * (q + 1) : ℕ) * |Real.log (minimumAccuracy P.order_pos ε)| / |Real.log P.reduction| +
      |Real.log (accuracyCoefficient P L / P.initialCap)| / |Real.log P.reduction| + 2 := by
  have hs := h.successful_card_le hf hL (fun a _ ha => hlip a ha) hlow
  have ha := h.accuracy_card_le hf hL hlip hnot
  simp only [derivativeEvaluations, Nat.cast_add, Nat.cast_one]
  linarith

/-- Before true optimality, the whole iteration count is bounded by the sum of
the operational objective-trial and accuracy-improvement budgets. -/
theorem iterations_le (h : Run f P ε A T j x d s Δ ρ accuracy N)
    (hf : ContDiff ℝ q f) {L flow : ℝ} (hL : 1 ≤ L)
    (hlip : ∀ a, a ≤ q → ∀ u v,
      ‖iteratedFDeriv ℝ a f u - iteratedFDeriv ℝ a f v‖ ≤ L * ‖u - v‖)
    (hlow : flow ≤ f (x N))
    (hnot : ∀ i < N, NotOptimal f ε (x i) (optimalityRadius P.theta (Δ i))) :
    (N : ℝ) ≤
      successfulConstant P L * HighOrderTrustRegion.iterationFactor P.gamma2 P.gamma3 *
        (f (x 0) - flow) / minimumAccuracy P.order_pos ε ^ (q + 1) +
      |Real.log (minimumAccuracy P.order_pos ε)| / |Real.log P.gamma2| +
      |Real.log (P.zeta * (positiveRadiusCoefficient P L / 2) / Δ 0)| /
        |Real.log P.gamma2| +
      (q * (q + 1) : ℕ) * |Real.log (minimumAccuracy P.order_pos ε)| / |Real.log P.reduction| +
      |Real.log (accuracyCoefficient P L / P.initialCap)| / |Real.log P.reduction| + 2 := by
  have hfcount := h.functionEvaluations_le hf hL (fun a _ ha => hlip a ha) hlow
  have hacount := h.accuracy_card_le hf hL hlip hnot
  have hpart : (N : ℝ) = (successfulIterations T N).card + (successfulIterations Tᶜ
    N).card := by
    exact_mod_cast (card_successful_add_card_unsuccessful T N).symm
  rw [hpart]
  simp only [functionEvaluations, Nat.cast_add, Nat.cast_one] at hfcount
  linarith

end Run

/-- Every consistent operational execution reaches true all-order approximate
optimality at a first finite index, whether or not the IDA algorithm can observe it. -/
theorem exists_approximate_optimality {q : ℕ} {f : E → ℝ} {P : Settings q}
    {ε : Fin q → ℝ} {A : ℕ → FormalMultilinearSeries ℝ E ℝ} {T : Set ℕ}
    {j : ℕ → Fin q} {x d s : ℕ → E} {Δ ρ : ℕ → ℝ} {accuracy : ℕ → ℕ → ℝ}
    (hprefix : ∀ N, (∀ i < N, NotOptimal f ε (x i) (optimalityRadius P.theta (Δ i))) →
      Run f P ε A T j x d s Δ ρ accuracy N)
    (hf : ContDiff ℝ q f) {L flow : ℝ} (hL : 1 ≤ L)
    (hlip : ∀ a, a ≤ q → ∀ u v,
      ‖iteratedFDeriv ℝ a f u - iteratedFDeriv ℝ a f v‖ ≤ L * ‖u - v‖)
    (hlow : ∀ y, flow ≤ f y) :
    ∃ K, (∀ a : Fin q, TaylorModel.criticality f (modelOrder a) (x K)
      (optimalityRadius P.theta (Δ K)) ≤
        ε a * optimalityRadius P.theta (Δ K) ^ modelOrder a / (modelOrder a).factorial) ∧
      Run f P ε A T j x d s Δ ρ accuracy K ∧
      ∀ i < K, NotOptimal f ε (x i) (optimalityRadius P.theta (Δ i)) := by
  classical
  have hex : ∃ K, ¬NotOptimal f ε (x K) (optimalityRadius P.theta (Δ K)) := by
    by_contra hn
    push Not at hn
    let μ := minimumAccuracy P.order_pos ε
    let bound := successfulConstant P L * HighOrderTrustRegion.iterationFactor P.gamma2 P.gamma3 *
      (f (x 0) - flow) / μ ^ (q + 1) + |Real.log μ| / |Real.log P.gamma2| +
      |Real.log (P.zeta * (positiveRadiusCoefficient P L / 2) / Δ 0)| / |Real.log P.gamma2| +
      (q * (q + 1) : ℕ) * |Real.log μ| / |Real.log P.reduction| +
      |Real.log (accuracyCoefficient P L / P.initialCap)| / |Real.log P.reduction| + 2
    obtain ⟨N, hN⟩ := exists_nat_gt bound
    have h := (hprefix N (fun i _ => hn i)).iterations_le hf hL hlip (hlow _) (fun i _ => hn i)
    exact (not_le_of_gt hN) h
  refine ⟨Nat.find hex, ?_, hprefix _ ?_, ?_⟩
  · exact not_not.mp (Nat.find_spec hex)
  · intro i hi
    exact not_not.mp (Nat.find_min hex hi)
  · intro i hi
    exact not_not.mp (Nat.find_min hex hi)


/-- Uniform evaluation complexity for genuine implicit-dynamic-accuracy runs.
Every positive coefficient is fixed before all accuracy requests. Both counters
include initialization, and the derivative additive constant includes the final
threshold-crossing accuracy reduction. Exact tensor oracles are included. -/
theorem evaluation_complexity {q : ℕ} (f : E → ℝ) (P : Settings q) (x₀ : E)
    {Δ₀ L flow : ℝ} (hL : 1 ≤ L) (hf : ContDiff ℝ q f)
    (hlip : ∀ a, a ≤ q → ∀ u v,
      ‖iteratedFDeriv ℝ a f u - iteratedFDeriv ℝ a f v‖ ≤ L * ‖u - v‖)
    (hlow : ∀ y, flow ≤ f y) :
    ∃ κA > 0, ∃ κB > 0, ∃ κC > 0, ∃ κE > 0, ∃ κF > 0,
      ∀ (ε : Fin q → ℝ) (A : ℕ → FormalMultilinearSeries ℝ E ℝ) (T : Set ℕ)
        (j : ℕ → Fin q) (x d s : ℕ → E) (Δ ρ : ℕ → ℝ) (accuracy : ℕ →
          ℕ → ℝ),
      x 0 = x₀ → Δ 0 = Δ₀ →
      (∀ N, (∀ i < N, NotOptimal f ε (x i) (optimalityRadius P.theta (Δ i))) →
        Run f P ε A T j x d s Δ ρ accuracy N) →
      ∃ K, optimalityRadius P.theta (Δ K) ∈ Ioc 0 1 ∧
        (∀ a : Fin q, TaylorModel.criticality f (modelOrder a) (x K)
          (optimalityRadius P.theta (Δ K)) ≤
          ε a * optimalityRadius P.theta (Δ K) ^ modelOrder a / (modelOrder a).factorial) ∧
        Run f P ε A T j x d s Δ ρ accuracy K ∧
        (∀ i < K, NotOptimal f ε (x i) (optimalityRadius P.theta (Δ i))) ∧
        (functionEvaluations T K : ℝ) ≤
          κA * (f x₀ - flow) / minimumAccuracy P.order_pos ε ^ (q + 1) +
          κB * |Real.log (minimumAccuracy P.order_pos ε)| + κC ∧
        (derivativeEvaluations T ρ P.eta1 K : ℝ) ≤
          κA * (f x₀ - flow) / minimumAccuracy P.order_pos ε ^ (q + 1) +
          κE * |Real.log (minimumAccuracy P.order_pos ε)| + κF := by
  let κ := positiveRadiusCoefficient P L / 2
  let F := HighOrderTrustRegion.iterationFactor P.gamma2 P.gamma3
  let κA := successfulConstant P L * F
  let κB := 1 / |Real.log P.gamma2|
  let κC := |Real.log (P.zeta * κ / Δ₀)| / |Real.log P.gamma2| + 1
  let κE := ((q * (q + 1) : ℕ) : ℝ) / |Real.log P.reduction|
  let κF := |Real.log (accuracyCoefficient P L / P.initialCap)| / |Real.log P.reduction| + 2
  have hκ : 0 < κ := div_pos (positiveRadiusCoefficient_properties P hL).1 (by norm_num)
  have hγ2 : 0 < P.gamma2 := P.gamma1_pos.trans_le P.gamma1_le_gamma2
  have hlog2 : 0 < |Real.log P.gamma2| := abs_pos.mpr (Real.log_neg hγ2 P.gamma2_lt_one).ne
  have hlogh : 0 < |Real.log P.reduction| :=
    abs_pos.mpr (Real.log_neg P.reduction_pos P.reduction_lt_one).ne
  have hlog3 : 0 ≤ Real.log P.gamma3 := Real.log_nonneg P.one_le_gamma3
  have hF : 1 ≤ F := by
    dsimp [F, HighOrderTrustRegion.iterationFactor]
    exact le_add_of_nonneg_right (div_nonneg hlog3 hlog2.le)
  have hS : 0 < successfulConstant P L := by
    have hz := P.zeta_pos
    have he := P.eta1_pos
    unfold successfulConstant
    have hh := (positiveRadiusCoefficient_properties P hL).1
    positivity
  have hm : (0 : ℝ) < ((q * (q + 1) : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos P.order_pos (by omega : 0 < q + 1)
  refine ⟨κA, mul_pos hS (by linarith), κB, div_pos (by norm_num) hlog2,
    κC, ?_, κE, div_pos hm hlogh, κF, ?_, ?_⟩
  · dsimp [κC]
    positivity
  · dsimp [κF]
    positivity
  · intro ε A T j x d s Δ ρ accuracy hx hΔ hprefix
    obtain ⟨K, hopt, hrun, hbefore⟩ := exists_approximate_optimality hprefix hf hL hlip hlow
    have hrad : optimalityRadius P.theta (Δ K) ∈ Ioc 0 1 :=
      ⟨lt_min P.theta_pos (hrun.updates.pos le_rfl),
        (min_le_left _ _).trans P.theta_le_one⟩
    have hfcount := hrun.functionEvaluations_le hf hL (fun a _ ha => hlip a ha) (hlow _)
    have hdcount := hrun.derivativeEvaluations_le hf hL hlip (hlow _) hbefore
    have hG : 0 ≤ f x₀ - flow := sub_nonneg.mpr (hlow x₀)
    have hμ : 0 < minimumAccuracy P.order_pos ε := minimumAccuracy_pos P.order_pos
      hrun.accuracy_pos
    have hleading : successfulConstant P L * (f x₀ - flow) /
        minimumAccuracy P.order_pos ε ^ (q + 1) ≤
        κA * (f x₀ - flow) / minimumAccuracy P.order_pos ε ^ (q + 1) := by
      apply div_le_div_of_nonneg_right _ (pow_nonneg hμ.le _)
      exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hS.le hF) hG
    refine ⟨K, hrad, hopt, hrun, hbefore, ?_, ?_⟩
    · rw [hx, hΔ] at hfcount
      convert hfcount using 1; dsimp [κA, κB, κC, κ, F]; ring
    · rw [hx] at hdcount
      calc _ ≤ successfulConstant P L * (f x₀ - flow) /
            minimumAccuracy P.order_pos ε ^ (q + 1) +
            (q * (q + 1) : ℕ) * |Real.log (minimumAccuracy P.order_pos ε)| /
              |Real.log P.reduction| +
            |Real.log (accuracyCoefficient P L / P.initialCap)| / |Real.log P.reduction| +
              2 := hdcount
        _ ≤ _ := by
          dsimp [κE, κF]
          have hh := add_le_add_right hleading
            (((q * (q + 1) : ℕ) : ℝ) * |Real.log (minimumAccuracy P.order_pos ε)| /
              |Real.log P.reduction| +
              |Real.log (accuracyCoefficient P L / P.initialCap)| / |Real.log P.reduction| + 2)
          convert hh using 1 <;> ring

end InexactTrustRegion
