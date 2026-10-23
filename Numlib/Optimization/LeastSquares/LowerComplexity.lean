import Numlib.Optimization.LeastSquares.LowerBudget

/-!
# Lower-order ARpLE termination and evaluation complexity

The genuine program stops at its first actual normalized optimality test.
Constants are fixed before every enabled accuracy and every execution.
-/

namespace LeastSquares.LowerRun
open HighOrderRegularization EvaluationComplexity
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F]
variable {literal second : Bool} {r : E → F} {ℓ L β : ℝ} {p : ℕ} {x s u : ℕ →
  E} {μ σ ρ : ℕ → ℝ}
  {M : ℕ → Set E} {η₁ η₂ γ₁ γ₂ γ₃ σmin θ₁ θ₂ θ₃ ε₀ ε₁
    ε₂ : ℝ} {N : ℕ}

/-- The finite dyadic-root residual budget bounds all accepted trials, including the final one. -/
theorem successful_card_le
    (h : LowerRun literal second r ℓ p x s u μ σ ρ M η₁ η₂ γ₁ γ₂ γ₃ σmin
      θ₁ θ₂ θ₃ ε₀ ε₁ ε₂ N)
    (hε₂ : 0 < ε₂)
    (hf : ContDiff ℝ p (powerObjective r ℓ)) (hL : 0 < L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ p (powerObjective r ℓ) y -
      iteratedFDeriv ℝ p (powerObjective r ℓ) z‖ ≤ L * ‖y - z‖)
    (hβ : 0 < β) (hβ1 : β < 1) (a : ℕ)
    (hι₁ : 0 ≤ cascadingExponent p ℓ a 1) (hι₂ : second = true → 0 ≤
      cascadingExponent p ℓ a 2) :
    ((successfulIterations {i | η₁ ≤ ρ i} N).card : ℝ) ≤
      lowerSuccessfulIterationConstant second p ℓ a (σ 0) σmin η₁ η₂ γ₃ L θ₁
        θ₂ β *
        lowerBudget second p ℓ a ‖r (x 0)‖ / lowerAccuracyFactor second p a ε₀
          ε₁ ε₂ + 1 := by
  have hσ := h.trace.updates.pos (Nat.zero_le N)
  have hc := lowerDecreaseCoefficient_pos (η₂ := η₂) (γ₃ := γ₃) second p ℓ a
    hσ h.trace.updates.min_pos
    h.trace.updates.eta1_pos hL h.theta_first_pos h.theta_second_pos hβ hβ1
  have hinv := inverse_lowerDecreaseCoefficient (η₂ := η₂) (γ₃ := γ₃) second p
    ℓ a hσ h.trace.updates.min_pos
    h.trace.updates.eta1_pos hL h.theta_first_pos h.theta_second_pos hβ hβ1
  have hKS : 0 < lowerSuccessfulIterationConstant second p ℓ a (σ 0) σmin η₁ η₂
    γ₃ L θ₁ θ₂ β :=
    hinv ▸ one_div_pos.mpr hc
  have hA := lowerAccuracyFactor_pos second p a h.accuracy_global_pos h.accuracy_first_pos hε₂
  have hD := lowerDenominator_pos second p ℓ a ‖r (x 0)‖
  cases N with
  | zero =>
    simp only [successfulIterations, Finset.range_zero, Finset.filter_empty,
      Finset.card_empty, Nat.cast_zero]
    have hb := lowerBudget_nonneg (norm_nonneg (r (x 0))) second p ℓ a
    positivity
  | succ k =>
    have hd := div_pos (mul_pos hc hA) hD
    have hcount := card_successful_le_gap_div
      (S := {i | η₁ ≤ ρ i}) (f := fun i => ‖r (x i)‖ ^ (1 / (2 : ℝ) ^ a))
      (flow := 0) (k := k) hd (Real.rpow_nonneg (norm_nonneg _) _)
      (fun i hi hs => h.successful_root_decrease hε₂ hf hL hlip hβ hβ1 a hι₁ hι₂
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
        (lowerDecreaseCoefficient second p ℓ a (σ 0) σmin η₁ η₂ γ₃ L θ₁ θ₂ β *
          lowerAccuracyFactor second p a ε₀ ε₁ ε₂ / lowerDenominator second p ℓ a
            ‖r (x 0)‖) =
        lowerSuccessfulIterationConstant second p ℓ a (σ 0) σmin η₁ η₂ γ₃ L
          θ₁ θ₂ β *
          lowerBudget second p ℓ a ‖r (x 0)‖ / lowerAccuracyFactor second p a ε₀
            ε₁ ε₂ := by
      rw [← hinv, ← lowerBudget_eq hR second p ℓ a]
      simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, sub_zero]
      ring
    rw [heq] at hcount
    exact hsucc.trans (add_le_add hcount le_rfl)

/-- The actual regularization parameter updates turn the accepted-trial budget into a
  total-trial bound. -/
theorem iterations_le
    (h : LowerRun literal second r ℓ p x s u μ σ ρ M η₁ η₂ γ₁ γ₂ γ₃ σmin
      θ₁ θ₂ θ₃ ε₀ ε₁ ε₂ N)
    (hε₂ : 0 < ε₂)
    (hf : ContDiff ℝ p (powerObjective r ℓ)) (hL : 0 < L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ p (powerObjective r ℓ) y -
      iteratedFDeriv ℝ p (powerObjective r ℓ) z‖ ≤ L * ‖y - z‖)
    (hβ : 0 < β) (hβ1 : β < 1) (a : ℕ)
    (hι₁ : 0 ≤ cascadingExponent p ℓ a 1) (hι₂ : second = true → 0 ≤
      cascadingExponent p ℓ a 2) :
    (N : ℝ) ≤
      (lowerSuccessfulIterationConstant second p ℓ a (σ 0) σmin η₁ η₂ γ₃ L
        θ₁ θ₂ β *
        lowerBudget second p ℓ a ‖r (x 0)‖ / lowerAccuracyFactor second p a ε₀
          ε₁ ε₂ + 1) *
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
    (h.successful_card_le hε₂ hf hL hlip hβ hβ1 a hι₁ hι₂) hA) le_rfl)
end LeastSquares.LowerRun


namespace LeastSquares
open HighOrderRegularization EvaluationComplexity
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F]
/-- Consistent actual ARpLE execution prefixes reach their first lower-order stop. -/
theorem exists_lower_termination {r : E → F} {ℓ L β : ℝ} {literal second : Bool} {p a : ℕ}
    {x s u : ℕ → E} {μ σ ρ : ℕ → ℝ} {M : ℕ → Set E}
    {η₁ η₂ γ₁ γ₂ γ₃ σmin θ₁ θ₂ θ₃ ε₀ ε₁ ε₂ : ℝ}
    (hε₂ : 0 < ε₂)
    (hprefix : ∀ N, (∀ i < N, ¬lowerStop second r ℓ (x i) (μ i) ε₀ ε₁ ε₂) →
      LowerRun literal second r ℓ p x s u μ σ ρ M η₁ η₂ γ₁ γ₂ γ₃ σmin
        θ₁ θ₂ θ₃ ε₀ ε₁ ε₂ N)
    (hf : ContDiff ℝ p (powerObjective r ℓ)) (hL : 0 < L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ p (powerObjective r ℓ) y -
      iteratedFDeriv ℝ p (powerObjective r ℓ) z‖ ≤ L * ‖y - z‖)
    (hβ : 0 < β) (hβ1 : β < 1)
    (hι₁ : 0 ≤ cascadingExponent p ℓ a 1) (hι₂ : second = true → 0 ≤
      cascadingExponent p ℓ a 2) :
    ∃ K, lowerStop second r ℓ (x K) (μ K) ε₀ ε₁ ε₂ ∧
      LowerRun literal second r ℓ p x s u μ σ ρ M η₁ η₂ γ₁ γ₂ γ₃ σmin
        θ₁ θ₂ θ₃ ε₀ ε₁ ε₂ K ∧
      ∀ i < K, ¬lowerStop second r ℓ (x i) (μ i) ε₀ ε₁ ε₂ := by
  classical
  have hex : ∃ K, lowerStop second r ℓ (x K) (μ K) ε₀ ε₁ ε₂ := by
    by_contra hn
    have hnon := not_exists.mp hn
    let bound :=
      (lowerSuccessfulIterationConstant second p ℓ a (σ 0) σmin η₁ η₂ γ₃ L
        θ₁ θ₂ β *
        lowerBudget second p ℓ a ‖r (x 0)‖ / lowerAccuracyFactor second p a ε₀
          ε₁ ε₂ + 1) *
          (1 + |Real.log γ₁| / Real.log γ₂) +
        Real.log (max (σ 0) (γ₃ * L / (1 - η₂)) / σ 0) / Real.log γ₂
    obtain ⟨N, hN⟩ := exists_nat_gt bound
    exact (not_le_of_gt hN)
      ((hprefix N (fun i _ => hnon i)).iterations_le hε₂ hf hL hlip hβ hβ1 a hι₁ hι₂)
  have hnon : ∀ i < Nat.find hex, ¬lowerStop second r ℓ (x i) (μ i) ε₀ ε₁ ε₂ :=
    fun i hi => Nat.find_min hex hi
  exact ⟨Nat.find hex, Nat.find_spec hex, hprefix _ hnon, hnon⟩

/-- Accuracy-independent constants precede every enabled accuracy and every actual
lower-order ARpLE execution. The first true stopping point satisfies the normalized
optimality alternative and all initialized residual/derivative evaluation bounds. -/
theorem exists_uniform_lower_complexity {r : E → F} (literal second : Bool) (p a : ℕ)
  (ℓ : ℝ)
    {σinit σmin η₁ η₂ γ₁ γ₂ γ₃ L θ₁ θ₂ θ₃ β : ℝ}
    (hf : ContDiff ℝ p (powerObjective r ℓ)) (hL : 0 < L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ p (powerObjective r ℓ) y -
      iteratedFDeriv ℝ p (powerObjective r ℓ) z‖ ≤ L * ‖y - z‖)
    (hσ : 0 < σinit) (hmin : 0 < σmin) (hη : 0 < η₁) (hγ₂ : 1 < γ₂)
    (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂) (hβ : 0 < β) (hβ1 : β < 1)
    (hι₁ : 0 ≤ cascadingExponent p ℓ a 1) (hι₂ : second = true → 0 ≤
      cascadingExponent p ℓ a 2) :
    ∃ κS > 0, ∃ κA > 0, ∃ κC > 0,
      κS = lowerSuccessfulIterationConstant second p ℓ a σinit σmin η₁ η₂ γ₃ L
        θ₁ θ₂ β ∧
      κA = κS * (1 + |Real.log γ₁| / Real.log γ₂) ∧
      κC = |Real.log γ₁| / Real.log γ₂ +
        Real.log (max σinit (γ₃ * L / (1 - η₂)) / σinit) / Real.log γ₂ + 2 ∧
      ∀ ε₀ ε₁ ε₂ : ℝ, 0 < ε₂ → ∀ x s u : ℕ → E,
      ∀ μ σ ρ : ℕ → ℝ, ∀ M : ℕ → Set E, σ 0 = σinit →
      (∀ N, (∀ i < N, ¬lowerStop second r ℓ (x i) (μ i) ε₀ ε₁ ε₂) →
        LowerRun literal second r ℓ p x s u μ σ ρ M η₁ η₂ γ₁ γ₂ γ₃ σmin
          θ₁ θ₂ θ₃ ε₀ ε₁ ε₂ N) →
      ∃ K, lowerStop second r ℓ (x K) (μ K) ε₀ ε₁ ε₂ ∧
        LowerRun literal second r ℓ p x s u μ σ ρ M η₁ η₂ γ₁ γ₂ γ₃ σmin
          θ₁ θ₂ θ₃ ε₀ ε₁ ε₂ K ∧
        (∀ i < K, ¬lowerStop second r ℓ (x i) (μ i) ε₀ ε₁ ε₂) ∧
        (functionEvaluations K : ℝ) ≤
          κA * lowerBudget second p ℓ a ‖r (x 0)‖ / lowerAccuracyFactor second p a
            ε₀ ε₁ ε₂ + κC ∧
        ∀ j : ℕ, 1 ≤ j → j ≤ p → (derivativeEvaluations ρ η₁ p j K : ℝ) ≤
          κS * lowerBudget second p ℓ a ‖r (x 0)‖ / lowerAccuracyFactor second p a
            ε₀ ε₁ ε₂ + 2 := by
  let κS := lowerSuccessfulIterationConstant second p ℓ a σinit σmin η₁ η₂ γ₃
    L θ₁ θ₂ β
  have hc := lowerDecreaseCoefficient_pos (η₂ := η₂) (γ₃ := γ₃) second p ℓ a
    hσ hmin hη hL
    hθ₁ hθ₂ hβ hβ1
  have hinv := inverse_lowerDecreaseCoefficient (η₂ := η₂) (γ₃ := γ₃) second p
    ℓ a hσ hmin hη hL
    hθ₁ hθ₂ hβ hβ1
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
  intro ε₀ ε₁ ε₂ hε₂ x s u μ σ ρ M hσ0 hprefix
  obtain ⟨K, hs, hrun, hnon⟩ := exists_lower_termination hε₂ hprefix hf hL hlip hβ
    hβ1 hι₁ hι₂
  have hcount := hrun.successful_card_le hε₂ hf hL hlip hβ hβ1 a hι₁ hι₂
  have htotal := hrun.iterations_le hε₂ hf hL hlip hβ hβ1 a hι₁ hι₂
  rw [hσ0] at hcount htotal
  refine ⟨K, hs, hrun, hnon, ?_, ?_⟩
  · rw [functionEvaluations_eq, Nat.cast_add, Nat.cast_one]
    dsimp only [κS] at *
    have heq : (lowerSuccessfulIterationConstant second p ℓ a σinit σmin η₁ η₂
      γ₃ L θ₁ θ₂ β *
        lowerBudget second p ℓ a ‖r (x 0)‖ / lowerAccuracyFactor second p a ε₀
          ε₁ ε₂ + 1) *
          (1 + |Real.log γ₁| / Real.log γ₂) +
        Real.log (max σinit (γ₃ * L / (1 - η₂)) / σinit) / Real.log γ₂ + 1 =
        lowerSuccessfulIterationConstant second p ℓ a σinit σmin η₁ η₂ γ₃ L
          θ₁ θ₂ β *
          (1 + |Real.log γ₁| / Real.log γ₂) * lowerBudget second p ℓ a ‖r (x 0)‖ /
            lowerAccuracyFactor second p a ε₀ ε₁ ε₂ +
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
