import Numlib.Optimization.LeastSquares.Budget
import Numlib.Optimization.Regularization.HighOrder.Complexity
import Numlib.Optimization.EvaluationComplexity.Decrease

/-!
# Corrected finite-third-order ARpLE evaluation complexity

Actual dyadic-root residual decreases consume a finite budget. Real parameter
updates bound all trials, and consistent prefixes reach a first true stopping
point. All constants precede the four requested accuracies and every execution;
initialized function and every residual-derivative count are exact.
-/

namespace LeastSquares.FiniteRun
open HighOrderRegularization EvaluationComplexity
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F]
variable {r : E → F} {ℓ L β : ℝ} {p : ℕ} {x s u : ℕ → E} {μ σ ρ : ℕ → ℝ}
  {M : ℕ → Set E} {η₁ η₂ γ₁ γ₂ γ₃ σmin θ₁ θ₂ θ₃ ε₀ ε₁
    ε₂ ε₃ : ℝ} {N : ℕ}

/-- The finite dyadic-root residual budget bounds all accepted trials, including the final one. -/
theorem successful_card_le
    (h : FiniteRun false r ℓ p x s u μ σ ρ M η₁ η₂ γ₁ γ₂ γ₃ σmin
      θ₁ θ₂ θ₃ ε₀ ε₁ ε₂ ε₃ N)
    (hf : ContDiff ℝ p (powerObjective r ℓ)) (hL : 0 < L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ p (powerObjective r ℓ) y -
      iteratedFDeriv ℝ p (powerObjective r ℓ) z‖ ≤ L * ‖y - z‖)
    (hβ : 0 < β) (hβ1 : β < 1) (a : ℕ)
    (hι₁ : 0 ≤ cascadingExponent p ℓ a 1) (hι₂ : 0 ≤ cascadingExponent p ℓ a 2)
    (hι₃ : 0 ≤ cascadingExponent p ℓ a 3) :
    ((successfulIterations {i | η₁ ≤ ρ i} N).card : ℝ) ≤
      rootSuccessfulIterationConstant p ℓ a (σ 0) σmin η₁ η₂ γ₃ L θ₁ θ₂
        θ₃ β *
        rootBudget p ℓ a ‖r (x 0)‖ / rootAccuracyFactor p a ε₀ ε₁ ε₂ ε₃ + 1 := by
  have hσ := h.trace.updates.pos (Nat.zero_le N)
  have hc := rootDecreaseCoefficient_pos (η₂ := η₂) (γ₃ := γ₃) p ℓ a hσ
    h.trace.updates.min_pos
    h.trace.updates.eta1_pos hL h.theta_first_pos h.theta_second_pos h.theta_third_pos hβ hβ1
  have hinv := inverse_rootDecreaseCoefficient (η₂ := η₂) (γ₃ := γ₃) p ℓ a
    hσ h.trace.updates.min_pos
    h.trace.updates.eta1_pos hL h.theta_first_pos h.theta_second_pos h.theta_third_pos hβ hβ1
  have hKS : 0 < rootSuccessfulIterationConstant p ℓ a (σ 0) σmin η₁ η₂ γ₃ L
    θ₁ θ₂ θ₃ β :=
    hinv ▸ one_div_pos.mpr hc
  have hA := rootAccuracyFactor_pos p a h.accuracy_global_pos h.accuracy_first_pos
    (h.accuracy_second_pos ε₂ rfl) (h.accuracy_third_pos ε₃ rfl)
  have hD := rootDenominator_pos p ℓ a ‖r (x 0)‖
  cases N with
  | zero =>
    simp only [successfulIterations, Finset.range_zero, Finset.filter_empty,
      Finset.card_empty, Nat.cast_zero]
    have hb := rootBudget_nonneg (norm_nonneg (r (x 0))) p ℓ a
    positivity
  | succ k =>
    have hd := div_pos (mul_pos hc hA) hD
    have hcount := card_successful_le_gap_div
      (S := {i | η₁ ≤ ρ i}) (f := fun i => ‖r (x i)‖ ^ (1 / (2 : ℝ) ^ a))
      (flow := 0) (k := k) hd (Real.rpow_nonneg (norm_nonneg _) _)
      (fun i hi hs => h.successful_root_decrease hf hL hlip hβ hβ1 a hι₁ hι₂ hι₃
        (by omega) hs)
      (fun i hi hu => by
        change ¬η₁ ≤ ρ i at hu
        rw [h.trace.point_update i (by omega), ite_eq_right hu])
    have hsucc : ((successfulIterations {i | η₁ ≤ ρ i} (k + 1)).card : ℝ) ≤
        (successfulIterations {i | η₁ ≤ ρ i} k).card + 1 := by
      exact_mod_cast card_successful_succ_le {i | η₁ ≤ ρ i} k
    have hR : 0 < ‖r (x 0)‖ :=
      h.accuracy_global_pos.trans (h.residual_gt_accuracy (by omega))
    have heq : (‖r (x 0)‖ ^ (1 / (2 : ℝ) ^ a) - 0) /
        (rootDecreaseCoefficient p ℓ a (σ 0) σmin η₁ η₂ γ₃ L θ₁ θ₂ θ₃ β *
          rootAccuracyFactor p a ε₀ ε₁ ε₂ ε₃ / rootDenominator p ℓ a ‖r (x 0)‖) =
        rootSuccessfulIterationConstant p ℓ a (σ 0) σmin η₁ η₂ γ₃ L θ₁
          θ₂ θ₃ β *
          rootBudget p ℓ a ‖r (x 0)‖ / rootAccuracyFactor p a ε₀ ε₁ ε₂ ε₃ := by
      rw [← hinv, ← rootBudget_eq hR p ℓ a]
      simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, sub_zero]
      ring
    rw [heq] at hcount
    exact hsucc.trans (add_le_add hcount le_rfl)

/-- The actual regularization parameter updates turn the accepted-trial budget into a
  total-trial bound. -/
theorem iterations_le
    (h : FiniteRun false r ℓ p x s u μ σ ρ M η₁ η₂ γ₁ γ₂ γ₃ σmin
      θ₁ θ₂ θ₃ ε₀ ε₁ ε₂ ε₃ N)
    (hf : ContDiff ℝ p (powerObjective r ℓ)) (hL : 0 < L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ p (powerObjective r ℓ) y -
      iteratedFDeriv ℝ p (powerObjective r ℓ) z‖ ≤ L * ‖y - z‖)
    (hβ : 0 < β) (hβ1 : β < 1) (a : ℕ)
    (hι₁ : 0 ≤ cascadingExponent p ℓ a 1) (hι₂ : 0 ≤ cascadingExponent p ℓ a 2)
    (hι₃ : 0 ≤ cascadingExponent p ℓ a 3) :
    (N : ℝ) ≤
      (rootSuccessfulIterationConstant p ℓ a (σ 0) σmin η₁ η₂ γ₃ L θ₁
        θ₂ θ₃ β *
        rootBudget p ℓ a ‖r (x 0)‖ / rootAccuracyFactor p a ε₀ ε₁ ε₂ ε₃ + 1) *
          (1 + |Real.log γ₁| / Real.log γ₂) +
        Real.log (max (σ 0) (γ₃ * L / (1 - η₂)) / σ 0) / Real.log γ₂ := by
  have ht := iteration_bound_of_parameter_upper
    (S := {i | η₁ ≤ ρ i}) (fun _ hi => h.trace.updates.pos hi)
    h.trace.updates.gamma1_pos h.trace.updates.gamma1_lt_one
    h.trace.updates.one_lt_gamma2 (h.trace.parameter_le hf hL.le hlip le_rfl)
    (fun _ hi hs => h.trace.updates.successful_ge hi hs)
    (fun _ hi hu => h.trace.updates.unsuccessful_ge hi hu)
  have hlog := Real.log_pos h.trace.updates.one_lt_gamma2
  have hA : 0 ≤ 1 + |Real.log γ₁| / Real.log γ₂ := by positivity
  exact ht.trans (add_le_add (mul_le_mul_of_nonneg_right
    (h.successful_card_le hf hL hlip hβ hβ1 a hι₁ hι₂ hι₃) hA) le_rfl)
end LeastSquares.FiniteRun

namespace LeastSquares
open HighOrderRegularization EvaluationComplexity
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F]

/-- The true normalized small-curvature unit directions in (5.1.7). -/
def smallResidualCurvatureDirections (r : E → F) (ℓ : ℝ) (x : E) (ε₂ : ℝ) : Set E :=
  {v | ‖v‖ = 1 ∧ directionalSecondMeasure r ℓ x v ≤ ε₂}

/-- Each residual derivative order1..p is evaluated initially and at accepted endpoints only. -/
noncomputable def derivativeEvaluations (ρ : ℕ → ℝ) (η₁ : ℝ) (p j N : ℕ) : ℕ :=
  if 1 ≤ j ∧ j ≤ p then HighOrderRegularization.derivativeEvaluations ρ η₁ N else 0

/-- The exact initialized evaluation schedule for each requested residual derivative order. -/
theorem derivativeEvaluations_eq (ρ : ℕ → ℝ) (η₁ : ℝ) {p j : ℕ}
    (hj : 1 ≤ j) (hjp : j ≤ p) (N : ℕ) :
    derivativeEvaluations ρ η₁ p j N = (successfulIterations {i | η₁ ≤ ρ i}
      N).card + 1 := by
  simp only [derivativeEvaluations, ite_eq_left (show 1 ≤ j ∧ j ≤ p from ⟨hj, hjp⟩),
    HighOrderRegularization.derivativeEvaluations_eq]

namespace FiniteRun
variable {r : E → F} {ℓ : ℝ} {p : ℕ} {x s u : ℕ → E} {μ σ ρ : ℕ → ℝ}
  {M : ℕ → Set E} {η₁ η₂ γ₁ γ₂ γ₃ σmin θ₁ θ₂ θ₃ ε₀ ε₁
    ε₂ ε₃ : ℝ} {N : ℕ}

/-- Actual repaired termination gives either the global residual test or all normalized
optimality bounds with the returned actual model directions contained in the true unit set. -/
theorem terminal_guarantees
    (h : FiniteRun false r ℓ p x s u μ σ ρ M η₁ η₂ γ₁ γ₂ γ₃ σmin
      θ₁ θ₂ θ₃ ε₀ ε₁ ε₂ ε₃ N)
    (hs : finiteStop r ℓ (x N) (μ N) (M N) ε₀ ε₁ ε₂ ε₃) :
    ‖r (x N)‖ ≤ ε₀ ∨
      firstMeasure r ℓ (x N) ≤ ε₁ ∧ -ε₂ ≤ secondMeasure r ℓ (x N) (μ N) ∧
      returnedDirections (secondMeasure r ℓ (x N) (μ N)) ε₂ (M N) ⊆
        smallResidualCurvatureDirections r ℓ (x N) ε₂ ∧
      ∀ v ∈ returnedDirections (secondMeasure r ℓ (x N) (μ N)) ε₂ (M N),
        thirdMeasure r ℓ (x N) v ≤ ε₃ := by
  rcases hs with hr | ⟨hg, hs | ⟨hμ, hchecks⟩⟩
  · exact Or.inl hr
  · refine Or.inr ⟨hg, ?_, ?_, ?_⟩
    · linarith [h.accuracy_second_pos ε₂ rfl]
    · simp [returnedDirections, hs]
    · simp [returnedDirections, hs]
  · refine Or.inr ⟨hg, hμ, ?_, ?_⟩
    · intro v hv
      have hv' := (mem_returnedDirections_iff.mp hv).2
      exact ⟨h.directions_unit le_rfl hv', (hchecks v hv').2⟩
    · intro v hv
      exact (hchecks v (mem_returnedDirections_iff.mp hv).2).1
end FiniteRun

/-- Consistent actual ARpLE execution prefixes reach their first repaired finite-order stop. -/
theorem exists_finite_termination {r : E → F} {ℓ L β : ℝ} {p a : ℕ}
    {x s u : ℕ → E} {μ σ ρ : ℕ → ℝ} {M : ℕ → Set E}
    {η₁ η₂ γ₁ γ₂ γ₃ σmin θ₁ θ₂ θ₃ ε₀ ε₁ ε₂ ε₃ : ℝ}
    (hprefix : ∀ N, (∀ i < N, ¬finiteStop r ℓ (x i) (μ i) (M i) ε₀ ε₁ ε₂ ε₃) →
      FiniteRun false r ℓ p x s u μ σ ρ M η₁ η₂ γ₁ γ₂ γ₃ σmin
        θ₁ θ₂ θ₃ ε₀ ε₁ ε₂ ε₃ N)
    (hf : ContDiff ℝ p (powerObjective r ℓ)) (hL : 0 < L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ p (powerObjective r ℓ) y -
      iteratedFDeriv ℝ p (powerObjective r ℓ) z‖ ≤ L * ‖y - z‖)
    (hβ : 0 < β) (hβ1 : β < 1)
    (hι₁ : 0 ≤ cascadingExponent p ℓ a 1) (hι₂ : 0 ≤ cascadingExponent p ℓ a 2)
    (hι₃ : 0 ≤ cascadingExponent p ℓ a 3) :
    ∃ K, finiteStop r ℓ (x K) (μ K) (M K) ε₀ ε₁ ε₂ ε₃ ∧
      FiniteRun false r ℓ p x s u μ σ ρ M η₁ η₂ γ₁ γ₂ γ₃ σmin
        θ₁ θ₂ θ₃ ε₀ ε₁ ε₂ ε₃ K ∧
      ∀ i < K, ¬finiteStop r ℓ (x i) (μ i) (M i) ε₀ ε₁ ε₂ ε₃ := by
  classical
  have hex : ∃ K, finiteStop r ℓ (x K) (μ K) (M K) ε₀ ε₁ ε₂ ε₃ := by
    by_contra hn
    have hnon := not_exists.mp hn
    let bound :=
      (rootSuccessfulIterationConstant p ℓ a (σ 0) σmin η₁ η₂ γ₃ L θ₁
        θ₂ θ₃ β *
        rootBudget p ℓ a ‖r (x 0)‖ / rootAccuracyFactor p a ε₀ ε₁ ε₂ ε₃ + 1) *
          (1 + |Real.log γ₁| / Real.log γ₂) +
        Real.log (max (σ 0) (γ₃ * L / (1 - η₂)) / σ 0) / Real.log γ₂
    obtain ⟨N, hN⟩ := exists_nat_gt bound
    exact (not_le_of_gt hN)
      ((hprefix N (fun i _ => hnon i)).iterations_le hf hL hlip hβ hβ1 a hι₁ hι₂ hι₃)
  have hnon : ∀ i < Nat.find hex, ¬finiteStop r ℓ (x i) (μ i) (M i) ε₀ ε₁ ε₂ ε₃ :=
    fun i hi => Nat.find_min hex hi
  exact ⟨Nat.find hex, Nat.find_spec hex, hprefix _ hnon, hnon⟩

/-- Accuracy-independent printed constants precede all four accuracies and every actual
finite-third-order ARpLE execution. The first true stopping point satisfies the complete
normalized optimality alternative and all initialized residual/derivative evaluation bounds. -/
theorem exists_uniform_finite_complexity {r : E → F} (p a : ℕ) (ℓ : ℝ)
    {σinit σmin η₁ η₂ γ₁ γ₂ γ₃ L θ₁ θ₂ θ₃ β : ℝ}
    (hf : ContDiff ℝ p (powerObjective r ℓ)) (hL : 0 < L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ p (powerObjective r ℓ) y -
      iteratedFDeriv ℝ p (powerObjective r ℓ) z‖ ≤ L * ‖y - z‖)
    (hσ : 0 < σinit) (hmin : 0 < σmin) (hη : 0 < η₁) (hγ₂ : 1 < γ₂)
    (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂) (hθ₃ : 0 < θ₃) (hβ : 0 < β) (hβ1 : β < 1)
    (hι₁ : 0 ≤ cascadingExponent p ℓ a 1) (hι₂ : 0 ≤ cascadingExponent p ℓ a 2)
    (hι₃ : 0 ≤ cascadingExponent p ℓ a 3) :
    ∃ κS > 0, ∃ κA > 0, ∃ κC > 0,
      κS = rootSuccessfulIterationConstant p ℓ a σinit σmin η₁ η₂ γ₃ L θ₁
        θ₂ θ₃ β ∧
      κA = κS * (1 + |Real.log γ₁| / Real.log γ₂) ∧
      κC = |Real.log γ₁| / Real.log γ₂ +
        Real.log (max σinit (γ₃ * L / (1 - η₂)) / σinit) / Real.log γ₂ + 2 ∧
      ∀ ε₀ ε₁ ε₂ ε₃ : ℝ, ∀ x s u : ℕ → E,
      ∀ μ σ ρ : ℕ → ℝ, ∀ M : ℕ → Set E, σ 0 = σinit →
      (∀ N, (∀ i < N, ¬finiteStop r ℓ (x i) (μ i) (M i) ε₀ ε₁ ε₂ ε₃) →
        FiniteRun false r ℓ p x s u μ σ ρ M η₁ η₂ γ₁ γ₂ γ₃ σmin
          θ₁ θ₂ θ₃ ε₀ ε₁ ε₂ ε₃ N) →
      ∃ K, finiteStop r ℓ (x K) (μ K) (M K) ε₀ ε₁ ε₂ ε₃ ∧
        FiniteRun false r ℓ p x s u μ σ ρ M η₁ η₂ γ₁ γ₂ γ₃ σmin
          θ₁ θ₂ θ₃ ε₀ ε₁ ε₂ ε₃ K ∧
        (∀ i < K, ¬finiteStop r ℓ (x i) (μ i) (M i) ε₀ ε₁ ε₂ ε₃) ∧
        (‖r (x K)‖ ≤ ε₀ ∨
          firstMeasure r ℓ (x K) ≤ ε₁ ∧ -ε₂ ≤ secondMeasure r ℓ (x K) (μ K) ∧
          returnedDirections (secondMeasure r ℓ (x K) (μ K)) ε₂ (M K) ⊆
            smallResidualCurvatureDirections r ℓ (x K) ε₂ ∧
          ∀ v ∈ returnedDirections (secondMeasure r ℓ (x K) (μ K)) ε₂ (M K),
            thirdMeasure r ℓ (x K) v ≤ ε₃) ∧
        (functionEvaluations K : ℝ) ≤
          κA * rootBudget p ℓ a ‖r (x 0)‖ / rootAccuracyFactor p a ε₀ ε₁
            ε₂ ε₃ + κC ∧
        ∀ j : ℕ, 1 ≤ j → j ≤ p → (derivativeEvaluations ρ η₁ p j K : ℝ) ≤
          κS * rootBudget p ℓ a ‖r (x 0)‖ / rootAccuracyFactor p a ε₀ ε₁
            ε₂ ε₃ + 2 := by
  let κS := rootSuccessfulIterationConstant p ℓ a σinit σmin η₁ η₂ γ₃ L
    θ₁ θ₂ θ₃ β
  have hc := rootDecreaseCoefficient_pos (η₂ := η₂) (γ₃ := γ₃) p ℓ a hσ hmin hη hL
    hθ₁ hθ₂ hθ₃ hβ hβ1
  have hinv := inverse_rootDecreaseCoefficient (η₂ := η₂) (γ₃ := γ₃) p ℓ a
    hσ hmin hη hL
    hθ₁ hθ₂ hθ₃ hβ hβ1
  have hKS : 0 < κS := by
    dsimp only [κS]
    rw [← hinv]
    exact one_div_pos.mpr hc
  have hlog : 0 < Real.log γ₂ := Real.log_pos hγ₂
  have hfac : 0 < 1 + |Real.log γ₁| / Real.log γ₂ := by positivity
  have hmax : 1 ≤ max σinit (γ₃ * L / (1 - η₂)) / σinit :=
    (le_div_iff₀ hσ).mpr (by simpa only [one_mul] using le_max_left σinit _)
  have hlogmax : 0 ≤ Real.log (max σinit (γ₃ * L / (1 - η₂)) / σinit) :=
    Real.log_nonneg hmax
  refine ⟨κS, hKS, κS * (1 + |Real.log γ₁| / Real.log γ₂), mul_pos hKS hfac,
    |Real.log γ₁| / Real.log γ₂ +
      Real.log (max σinit (γ₃ * L / (1 - η₂)) / σinit) / Real.log γ₂ + 2,
    by positivity, rfl, rfl, rfl, ?_⟩
  intro ε₀ ε₁ ε₂ ε₃ x s u μ σ ρ M hσ0 hprefix
  obtain ⟨K, hs, hrun, hnon⟩ := exists_finite_termination hprefix hf hL hlip hβ hβ1
    hι₁ hι₂ hι₃
  have hcount := hrun.successful_card_le hf hL hlip hβ hβ1 a hι₁ hι₂ hι₃
  have htotal := hrun.iterations_le hf hL hlip hβ hβ1 a hι₁ hι₂ hι₃
  rw [hσ0] at hcount htotal
  refine ⟨K, hs, hrun, hnon, hrun.terminal_guarantees hs, ?_, ?_⟩
  · rw [functionEvaluations_eq, Nat.cast_add, Nat.cast_one]
    dsimp only [κS] at *
    have heq : (rootSuccessfulIterationConstant p ℓ a σinit σmin η₁ η₂ γ₃ L
      θ₁ θ₂ θ₃ β *
        rootBudget p ℓ a ‖r (x 0)‖ / rootAccuracyFactor p a ε₀ ε₁ ε₂ ε₃ + 1) *
          (1 + |Real.log γ₁| / Real.log γ₂) +
        Real.log (max σinit (γ₃ * L / (1 - η₂)) / σinit) / Real.log γ₂ + 1 =
        rootSuccessfulIterationConstant p ℓ a σinit σmin η₁ η₂ γ₃ L θ₁
          θ₂ θ₃ β *
          (1 + |Real.log γ₁| / Real.log γ₂) * rootBudget p ℓ a ‖r (x 0)‖ /
            rootAccuracyFactor p a ε₀ ε₁ ε₂ ε₃ +
          (|Real.log γ₁| / Real.log γ₂ +
            Real.log (max σinit (γ₃ * L / (1 - η₂)) / σinit) / Real.log γ₂ + 2)
              := by ring
    rw [← heq]
    linarith
  · intro j hj hjp
    rw [derivativeEvaluations_eq ρ η₁ hj hjp, Nat.cast_add, Nat.cast_one]
    dsimp only [κS] at *
    linarith
end LeastSquares
