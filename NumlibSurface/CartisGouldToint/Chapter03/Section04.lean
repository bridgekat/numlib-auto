import Numlib.Optimization.TrustRegion.Regularized.FirstOrder
import Numlib.Optimization.TrustRegion.Regularized.Solve

/-!
# Cartis–Gould–Toint, Section 3.4: regularized trust-region models

The TR epsilon trace uses actual Taylor derivatives, objective ratios and
accepted/rejected updates. First-order mode explicitly disables the second
stopping test; finite-second-order mode uses genuine least Hessian eigenpairs.
The model and radius bounds imply the printed decrease estimates. The normalization
`L ≥ 1` in the radius floor is the source's f.HL convention.
-/

namespace CartisGouldToint

/-- Algorithm3.4.1, TR epsilon, with both stopping modes and all primitive
step, actual-model, ratio, point-update and radius-update rules. -/
abbrev trEpsilonRun {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (f : E → ℝ) (x s u : ℕ → E) (μ Δ ρ : ℕ → ℝ)
    (η₁ η₂ γ₁ γ₂ γ₃ θ εstar ε₁ : ℝ) (ε₂ : WithTop ℝ) (N : ℕ) : Prop :=
  RegularizedTrustRegion.Run f x s u μ Δ ρ η₁ η₂ γ₁ γ₂ γ₃ θ εstar ε₁ ε₂ N

/-- The actual regularized second-order Taylor model (3.4.1). -/
noncomputable abbrev trEpsilonModel {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (x : E) (εstar : ℝ) (s : E) : ℝ :=
  RegularizedTrustRegion.model f x εstar s

/-- The accuracy-independent objective-decrease coefficient (3.4.15). -/
noncomputable abbrev trEpsilonDecreaseCoefficient (η₁ η₂ γ₁ L θ : ℝ) : ℝ :=
  RegularizedTrustRegion.decreaseCoefficient η₁ η₂ γ₁ L θ

/-- **Lemma3.4.1.** Every computed TR epsilon step has the Taylor decrement (3.4.7). -/
theorem lemma_3_4_1 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {f : E → ℝ} {x s u : ℕ → E} {μ Δ ρ : ℕ → ℝ}
    {η₁ η₂ γ₁ γ₂ γ₃ θ εstar ε₁ : ℝ} {ε₂ : WithTop ℝ} {N : ℕ}
    (h : trEpsilonRun f x s u μ Δ ρ η₁ η₂ γ₁ γ₂ γ₃ θ εstar ε₁ ε₂ N) :
    ∀ i < N, εstar / 2 * ‖s i‖ ^ 2 ≤
      TaylorModel.eval f 2 (x i) 0 - TaylorModel.eval f 2 (x i) (s i) :=
  fun i hi => (RegularizedTrustRegion.model_decrease (h.improvement i hi)).le

/-- **Lemma3.4.2.** Small radii imply very successful acceptance and a
nondecreasing next radius; every actual radius has the global floor (3.4.9). -/
theorem lemma_3_4_2 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {f : E → ℝ} {x s u : ℕ → E} {μ Δ ρ : ℕ → ℝ}
    {η₁ η₂ γ₁ γ₂ γ₃ θ εstar ε₁ L : ℝ} {ε₂ : WithTop ℝ} {N : ℕ}
    (h : trEpsilonRun f x s u μ Δ ρ η₁ η₂ γ₁ γ₂ γ₃ θ εstar ε₁ ε₂ N)
    (hf : ContDiff ℝ 2 f) (hL : 1 ≤ L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤
      L * ‖y - z‖) :
    (∀ i < N, Δ i < 3 * (1 - η₂) / L * εstar →
      η₂ ≤ ρ i ∧ η₁ ≤ ρ i ∧ Δ i ≤ Δ (i + 1)) ∧
    (∀ i ≤ N, (1 - η₂) * γ₁ / L * εstar ≤ Δ i) :=
  ⟨fun _ hi hs => h.toModelTrace.successful_and_nondecreasing hf
      (zero_lt_one.trans_le hL) hlip hi hs,
    fun _ hi => h.toModelTrace.radius_floor hf hL hlip hi⟩

/-- **Lemma3.4.3.** An accepted strictly interior step satisfies (3.4.10).
The proof differentiates the actual model and uses the sharp trial-gradient error. -/
theorem lemma_3_4_3 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {f : E → ℝ} {x s u : ℕ → E} {μ Δ ρ : ℕ → ℝ}
    {η₁ η₂ γ₁ γ₂ γ₃ θ εstar ε₁ L : ℝ} {ε₂ : WithTop ℝ} {N i : ℕ}
    (h : trEpsilonRun f x s u μ Δ ρ η₁ η₂ γ₁ γ₂ γ₃ θ εstar ε₁ ε₂ N)
    (hf : ContDiff ℝ 2 f) (hL : 0 ≤ L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤
      L * ‖y - z‖) (hi : i < N) (ha : η₁ ≤ ρ i) (hs : ‖s i‖ < Δ i) :
    (Real.sqrt (1 + 2 * (L + θ)))⁻¹ *
      min εstar (‖gradient f (x (i + 1))‖ * εstar⁻¹) ≤ ‖s i‖ :=
  h.interior_step_lower hf hL hlip hi ha hs

/-- **Lemma3.4.4.** Both accepted-step decrease branches (3.4.13)–(3.4.14)
hold with the exact common coefficient (3.4.15). -/
theorem lemma_3_4_4 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {f : E → ℝ} {x s u : ℕ → E} {μ Δ ρ : ℕ → ℝ}
    {η₁ η₂ γ₁ γ₂ γ₃ θ εstar ε₁ L : ℝ} {ε₂ : WithTop ℝ} {N i : ℕ}
    (h : trEpsilonRun f x s u μ Δ ρ η₁ η₂ γ₁ γ₂ γ₃ θ εstar ε₁ ε₂ N)
    (hf : ContDiff ℝ 2 f) (hL : 1 ≤ L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤
      L * ‖y - z‖) (hi : i < N) (ha : η₁ ≤ ρ i) :
    (‖s i‖ < Δ i → trEpsilonDecreaseCoefficient η₁ η₂ γ₁ L θ *
      min (εstar ^ 3) (‖gradient f (x (i + 1))‖ ^ 2 * εstar⁻¹) ≤
        f (x i) - f (x (i + 1))) ∧
    (‖s i‖ = Δ i → trEpsilonDecreaseCoefficient η₁ η₂ γ₁ L θ * εstar ^ 3 ≤
      f (x i) - f (x (i + 1))) :=
  ⟨h.successful_decrease_interior hf (zero_le_one.trans hL) hlip hi ha,
    h.successful_decrease_boundary hf hL hlip hi ha⟩

/-- **Theorem3.4.5.** Fixed source constants precede every requested accuracy
and every consistent first-order-only TR epsilon execution. The first actual
stopping point meets both initialized derivative-call bounds, and the objective
calls satisfy the exact `epsilon^(-3/2)` plus half-logarithm bound. -/
theorem theorem_3_4_5 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (f : E → ℝ) (x₀ : E)
    {Δ₀ η₁ η₂ γ₁ γ₂ γ₃ θ L flow : ℝ}
    (_hΔ₀ : 0 < Δ₀) (hη₁ : 0 < η₁) (hη₂ : η₂ < 1) (hγ₁ : 0 < γ₁)
    (hγ₂ : 0 < γ₂) (hγ₂1 : γ₂ < 1) (hγ₃ : 1 < γ₃) (hθ : 0 < θ)
    (hf : ContDiff ℝ 2 f) (hL : 1 ≤ L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤
      L * ‖y - z‖) (hlow : ∀ y, flow ≤ f y) :
    ∃ κS > 0, ∃ κA > 0, ∃ κB > 0, ∃ κC > 0,
      κS = 2 / η₁ * max (L ^ 2 / (γ₁ ^ 2 * (1 - η₂) ^ 2))
        (1 + 2 * (L + θ)) ∧
      κA = κS * (1 + Real.log γ₃ / |Real.log γ₂|) ∧
      κB = 1 / (2 * |Real.log γ₂|) ∧
      κC = (Real.log γ₃ + |Real.log ((1 - η₂) * γ₁ / (Δ₀ * L))|) /
        |Real.log γ₂| + 2 ∧
      ∀ ε₁ : ℝ, 0 < ε₁ → ε₁ ≤ 1 →
      ∀ (x s u : ℕ → E) (μ Δ ρ : ℕ → ℝ), x 0 = x₀ → Δ 0 = Δ₀ →
      (∀ N, (∀ i < N, ¬RegularizedTrustRegion.Stopped f (x i) (μ i) ε₁ ⊤) →
        trEpsilonRun f x s u μ Δ ρ η₁ η₂ γ₁ γ₂ γ₃ θ
          (Real.sqrt ε₁) ε₁ ⊤ N) →
      ∃ K, ‖gradient f (x K)‖ ≤ ε₁ ∧
        (∀ i < K, ε₁ < ‖gradient f (x i)‖) ∧
        trEpsilonRun f x s u μ Δ ρ η₁ η₂ γ₁ γ₂ γ₃ θ
          (Real.sqrt ε₁) ε₁ ⊤ K ∧
        (RegularizedTrustRegion.functionEvaluations K : ℝ) ≤
          κA * (f x₀ - flow) / ε₁ ^ (3 / 2 : ℝ) + κB * |Real.log ε₁| + κC ∧
        (RegularizedTrustRegion.derivativeEvaluations ρ η₁ K : ℝ) ≤
          κS * (f x₀ - flow) / ε₁ ^ (3 / 2 : ℝ) + 2 ∧
        (RegularizedTrustRegion.derivativeEvaluations ρ η₁ K : ℝ) ≤
          κS * (f x₀ - flow) / ε₁ ^ (3 / 2 : ℝ) + 2 := by
  let c := RegularizedTrustRegion.decreaseCoefficient η₁ η₂ γ₁ L θ
  let S := 1 / c
  let A := 1 + Real.log γ₃ / |Real.log γ₂|
  let B := 1 / (2 * |Real.log γ₂|)
  let C := (Real.log γ₃ + |Real.log ((1 - η₂) * γ₁ / (Δ₀ * L))|) /
    |Real.log γ₂| + 2
  have hc : 0 < c := RegularizedTrustRegion.decreaseCoefficient_pos hη₁ hη₂ hγ₁
    (zero_lt_one.trans_le hL) hθ.le
  have hlog3 := Real.log_pos hγ₃
  have hlog2 : 0 < |Real.log γ₂| := abs_pos.mpr (Real.log_neg hγ₂ hγ₂1).ne
  have hS : 0 < S := by dsimp [S]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨S, hS, S * A, mul_pos hS hA, B, hB, C, hC, ?_, rfl, rfl, rfl, ?_⟩
  · exact RegularizedTrustRegion.inv_decreaseCoefficient_eq hη₁ hη₂ hγ₁
      (zero_lt_one.trans_le hL) hθ.le
  · intro ε₁ _hε₁ _hε₁1 x s u μ Δ ρ hx hΔ hprefix
    obtain ⟨K, hstop, hK, _⟩ := RegularizedTrustRegion.exists_firstOrder_termination
      hprefix hf hL hlip hlow
    have hg := ((RegularizedTrustRegion.stopped_iff _ _ _ _ _).mp hstop).1
    have hD := hK.firstOrder_successful_card_le rfl hf hL hlip hlow
    have hD' : (RegularizedTrustRegion.derivativeEvaluations ρ η₁ K : ℝ) ≤
        S * (f x₀ - flow) / ε₁ ^ (3 / 2 : ℝ) + 2 := by
      rw [hx] at hD
      simp only [RegularizedTrustRegion.derivativeEvaluations, Nat.cast_add, Nat.cast_one]
      calc
        _ ≤ (f x₀ - flow) / (c * ε₁ ^ (3 / 2 : ℝ)) + 1 + 1 :=
          add_le_add hD le_rfl
        _ = _ := by dsimp [S]; ring
    refine ⟨K, hg, fun _ hi => hK.gradient_gt_of_disabled rfl hi, hK, ?_, hD', hD'⟩
    have hb := hK.firstOrder_iterations_le rfl hf hL hlip hlow
    rw [hx, hΔ] at hb
    simp only [RegularizedTrustRegion.functionEvaluations, Nat.cast_add, Nat.cast_one]
    calc
      (K : ℝ) + 1 ≤ ((f x₀ - flow) / (c * ε₁ ^ (3 / 2 : ℝ)) + 1) * A +
          (|Real.log ((1 - η₂) * γ₁ / (L * Δ₀))| + |Real.log ε₁| / 2) /
            |Real.log γ₂| + 1 := add_le_add hb le_rfl
      _ = _ := by dsimp [S, A, B, C]; rw [mul_comm Δ₀ L]; ring

end CartisGouldToint
