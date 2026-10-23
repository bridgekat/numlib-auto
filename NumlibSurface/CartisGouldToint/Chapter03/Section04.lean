import Numlib.Optimization.TrustRegion.Regularized.Decrease

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

end CartisGouldToint
