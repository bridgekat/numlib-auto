import Numlib.Optimization.TrustRegion.Regularized.InitialBudget
import Numlib.Optimization.Descent.LowerPoint
import Numlib.Optimization.Regularization.InexactNewton.Step
import Numlib.Optimization.Regularization.InexactNewton.Counting
import Numlib.Optimization.TrustRegion.Regularized.Solve

/-!
# Cartis–Gould–Toint, Section 3.4: regularized second-order methods

The TR epsilon trace uses actual Taylor derivatives, objective ratios and
accepted/rejected updates. First-order mode explicitly disables the second
stopping test; finite-second-order mode uses genuine least Hessian eigenpairs.
The model and radius bounds imply the printed decrease estimates. The normalization
`L ≥ 1` in the radius floor is the source's f.HL convention.
The finite-second-order companion uses twice the printed leading coefficient
and an initialized derivative allowance of two. Retaining the initial credit or
using a fixed lower objective point also proves the canonical existential theorem
with its printed allowance of one. Both arguments follow the literal
current-curvature boundary rule, rather than the proof's next-point inference.

The iRN trace retains the actual model derivatives, projected stopping tests and
coupled regularization updates. Varying subspaces represent the column spaces of
the source's orthonormal matrices; their least curvatures are actual Rayleigh minima.
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

/-- A corrected companion to **Theorem3.4.6**, for the literal current-curvature
boundary rule. The credited-objective argument gives leading coefficient twice
(3.4.20) and initialized derivative allowance `+2`. The printed proof's
next-curvature-to-previous-boundary inference is not used. All constants precede
both accuracies, the actual first joint stopping point and every execution. -/
theorem theorem_3_4_6_corrected {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (f : E → ℝ) (x₀ : E)
    {Δ₀ η₁ η₂ γ₁ γ₂ γ₃ θ L flow : ℝ}
    (_hΔ₀ : 0 < Δ₀) (hη₁ : 0 < η₁) (hη₂ : η₂ < 1) (hγ₁ : 0 < γ₁)
    (hγ₂ : 0 < γ₂) (hγ₂1 : γ₂ < 1) (hγ₃ : 1 < γ₃) (hθ : 0 < θ)
    (hf : ContDiff ℝ 2 f) (hL : 1 ≤ L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤
      L * ‖y - z‖) (hlow : ∀ y, flow ≤ f y) :
    ∃ κS > 0, ∃ κA > 0, ∃ κD > 0, ∃ κC > 0,
      κS = 4 / η₁ * max (L ^ 2 / (γ₁ ^ 2 * (1 - η₂) ^ 2))
        (1 + 2 * (L + θ)) ∧
      κA = κS * (1 + Real.log γ₃ / |Real.log γ₂|) ∧
      κD = 1 / |Real.log γ₂| ∧
      κC = (Real.log γ₃ + |Real.log ((1 - η₂) * γ₁ / (Δ₀ * L))|) /
        |Real.log γ₂| + 2 ∧
      ∀ ε₁ : ℝ, 0 < ε₁ → ε₁ ≤ 1 →
      ∀ ε₂ : ℝ, 0 < ε₂ → ε₂ ≤ 1 →
      ∀ (x s u : ℕ → E) (μ Δ ρ : ℕ → ℝ), x 0 = x₀ → Δ 0 = Δ₀ →
      (∀ N, (∀ i < N,
        ¬RegularizedTrustRegion.Stopped f (x i) (μ i) ε₁ (ε₂ : WithTop ℝ)) →
        trEpsilonRun f x s u μ Δ ρ η₁ η₂ γ₁ γ₂ γ₃ θ
          ε₂ ε₁ (ε₂ : WithTop ℝ) N) →
      ∃ K, ‖gradient f (x K)‖ ≤ ε₁ ∧ -ε₂ ≤ μ K ∧
        (∀ i < K, ε₁ < ‖gradient f (x i)‖ ∨ μ i < -ε₂) ∧
        trEpsilonRun f x s u μ Δ ρ η₁ η₂ γ₁ γ₂ γ₃ θ
          ε₂ ε₁ (ε₂ : WithTop ℝ) K ∧
        (RegularizedTrustRegion.functionEvaluations K : ℝ) ≤
          κA * (f x₀ - flow) / RegularizedTrustRegion.secondOrderScale ε₁ ε₂ +
            κD * |Real.log ε₂| + κC ∧
        (RegularizedTrustRegion.derivativeEvaluations ρ η₁ K : ℝ) ≤
          κS * (f x₀ - flow) / RegularizedTrustRegion.secondOrderScale ε₁ ε₂ + 2 ∧
        (RegularizedTrustRegion.derivativeEvaluations ρ η₁ K : ℝ) ≤
          κS * (f x₀ - flow) / RegularizedTrustRegion.secondOrderScale ε₁ ε₂ + 2 := by
  let c := RegularizedTrustRegion.decreaseCoefficient η₁ η₂ γ₁ L θ
  let S := 2 / c
  let A := 1 + Real.log γ₃ / |Real.log γ₂|
  let B := 1 / |Real.log γ₂|
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
  · have hi := RegularizedTrustRegion.inv_decreaseCoefficient_eq hη₁ hη₂ hγ₁
      (zero_lt_one.trans_le hL) hθ.le
    calc S = 2 * (1 / c) := by dsimp [S]; ring
      _ = _ := by rw [hi]; ring
  · intro ε₁ _hε₁ _hε₁1 ε₂ _hε₂ _hε₂1 x s u μ Δ ρ hx hΔ hprefix
    obtain ⟨K, hstop, hK, _⟩ := RegularizedTrustRegion.exists_secondOrder_termination
      hprefix hf hL hlip hlow
    have htests := (RegularizedTrustRegion.stopped_iff _ _ _ _ _).mp hstop
    have hg := htests.1
    have hμ := htests.2 ε₂ rfl
    have hD := hK.secondOrder_successful_card_le rfl hf hL hlip hlow
    have hD' : (RegularizedTrustRegion.derivativeEvaluations ρ η₁ K : ℝ) ≤
        S * (f x₀ - flow) / RegularizedTrustRegion.secondOrderScale ε₁ ε₂ + 2 := by
      rw [hx] at hD
      simp only [RegularizedTrustRegion.derivativeEvaluations, Nat.cast_add, Nat.cast_one]
      calc
        _ ≤ 2 * (f x₀ - flow) /
            (c * RegularizedTrustRegion.secondOrderScale ε₁ ε₂) + 1 + 1 :=
          add_le_add hD le_rfl
        _ = _ := by dsimp [S]; ring
    refine ⟨K, hg, hμ, fun _ hi => hK.finite_failure rfl hi, hK, ?_, hD', hD'⟩
    have hb := hK.secondOrder_iterations_le rfl hf hL hlip hlow
    rw [hx, hΔ] at hb
    simp only [RegularizedTrustRegion.functionEvaluations, Nat.cast_add, Nat.cast_one]
    calc
      (K : ℝ) + 1 ≤ (2 * (f x₀ - flow) /
          (c * RegularizedTrustRegion.secondOrderScale ε₁ ε₂) + 1) * A +
          (|Real.log ((1 - η₂) * γ₁ / (L * Δ₀))| + |Real.log ε₂|) /
            |Real.log γ₂| + 1 := add_le_add hb le_rfl
      _ = _ := by dsimp [S, A, B, C]; rw [mul_comm Δ₀ L]; ring

/-- The actual iRN quadratic Taylor model (3.4.27), with multiplier shift. -/
noncomputable abbrev irnModel {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (x : E) (ℓ : ℝ) (s : E) : ℝ :=
  RegularizedTrustRegion.model f x ℓ s

/-- The source's least projected Hessian eigenvalue, represented as the true
minimum Rayleigh form on the subspace spanned by orthonormal columns of `Q`. -/
abbrev irnLeastCurvatureOn {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (x : E) (V : Submodule ℝ E) (μ : ℝ) : Prop :=
  InexactRegularizedNewton.IsLeastCurvatureOn f x V μ

/-- Algorithm3.4.2, iRN, including both stopping modes, actual model derivative
checks, varying projected subspaces and the coupled lower/upper updates. Finite
mode computes the endpoint model step before its projected curvature test. -/
abbrev inexactRegularizedNewtonRun {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (f : E → ℝ) (x s : ℕ → E)
    (V : ℕ → Submodule ℝ E) (μ ℓ σL σU ρ : ℕ → ℝ)
    (η γ₁ γ₂ σmin σmax κ₁ κ₂ κ₃ κ₄ ε₁ : ℝ)
    (ε₂ : WithTop ℝ) (N : ℕ) : Prop :=
  InexactRegularizedNewton.Run f x s V μ ℓ σL σU ρ η γ₁ γ₂ σmin σmax
    κ₁ κ₂ κ₃ κ₄ ε₁ ε₂ N

/-- The exact accuracy-independent upper regularization bound (3.4.38). -/
noncomputable abbrev irnUpperRegularizationBound (σmax γ₂ η κ₂ L : ℝ) : ℝ :=
  InexactRegularizedNewton.upperBound σmax γ₂ η κ₂ L

section InexactNewton
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {f : E → ℝ} {x s : ℕ → E} {V : ℕ → Submodule ℝ E} {μ ℓ σL σU ρ : ℕ → ℝ}
  {η γ₁ γ₂ σmin σmax κ₁ κ₂ κ₃ κ₄ ε₁ L : ℝ} {ε₂ : WithTop ℝ} {N : ℕ}

/-- **Lemma3.4.7.** The source multiplier threshold guarantees actual cubic
objective descent and success. Nonzero trial steps follow from the operational
stopping and model tests, including finite-mode projected curvature. -/
theorem lemma_3_4_7
    (h : inexactRegularizedNewtonRun f x s V μ ℓ σL σU ρ η γ₁ γ₂ σmin σmax
      κ₁ κ₂ κ₃ κ₄ ε₁ ε₂ N) (hf : ContDiff ℝ 2 f) (hL : 0 ≤ L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤
      L * ‖y - z‖) :
    ∀ i < N, (2 * η + κ₂ + L) * ‖s i‖ ≤ ℓ i → η ≤ ρ i :=
  fun _ hi hs => h.successful_of_large_multiplier hf hL hlip hi hs

/-- **Lemma3.4.8.** The literal coupled iRN updates imply the uniform cap
(3.4.38) at every endpoint, without assuming this cap in the execution. -/
theorem lemma_3_4_8
    (h : inexactRegularizedNewtonRun f x s V μ ℓ σL σU ρ η γ₁ γ₂ σmin σmax
      κ₁ κ₂ κ₃ κ₄ ε₁ ε₂ N) (hf : ContDiff ℝ 2 f) (hL : 0 ≤ L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤
      L * ‖y - z‖) :
    ∀ i ≤ N, σU i ≤ irnUpperRegularizationBound σmax γ₂ η κ₂ L :=
  fun _ hi => h.upper_le hf hL hlip hi

/-- **Lemma3.4.9.** Accepted steps satisfy (3.4.39) for the actual next gradient.
The true least projected curvature satisfies (3.4.40) whenever the actual model
curvature test is imposed; finite-mode executions supply this test themselves.
The optional formulation also covers imposing (3.4.32) in first-order-only mode. -/
theorem lemma_3_4_9
    (h : inexactRegularizedNewtonRun f x s V μ ℓ σL σU ρ η γ₁ γ₂ σmin σmax
      κ₁ κ₂ κ₃ κ₄ ε₁ ε₂ N) (hf : ContDiff ℝ 2 f) (hL : 0 ≤ L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤
      L * ‖y - z‖) {i : ℕ} (hi : i < N) (ha : η ≤ ρ i) :
    (2 / (L + 4 * irnUpperRegularizationBound σmax γ₂ η κ₂ L + 2 * κ₃) *
      ‖gradient f (x (i + 1))‖ ≤ ‖s i‖ ^ 2) ∧
    (ε₂ ≠ ⊤ →
      -(κ₄ + irnUpperRegularizationBound σmax γ₂ η κ₂ L)⁻¹ * μ i ≤ ‖s i‖) ∧
    (∀ ν : ℝ, irnLeastCurvatureOn f (x i) (V i) ν →
      (∀ v : E, v ∈ V i → ‖v‖ = 1 →
        -κ₄ * ‖s i‖ ≤
          iteratedFDeriv ℝ 2 (irnModel f (x i) (ℓ i)) (s i) (fun _ => v)) →
      -(κ₄ + irnUpperRegularizationBound σmax γ₂ η κ₂ L)⁻¹ * ν ≤ ‖s i‖) :=
  ⟨h.step_lower hf hL hlip hi ha,
    fun hfinite => h.finite_projected_step_lower hf hL hlip hi.le hfinite,
    fun _ he hc => h.projected_step_lower hf hL hlip hi.le (Or.inl hi) he hc⟩

end InexactNewton

/-- **Theorem3.4.6**, the full finite-second-order complexity statement. The
constants are fixed before the global lower bound, both accuracies and every
execution. Retaining the initial potential credit, or absorbing its startup unit
using a fixed lower objective point, gives the printed initialized derivative
allowance `+1`. This uses larger proof constants than (3.4.20); the theorem itself
only asserts the existence of positive constants. -/
theorem theorem_3_4_6 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (f : E → ℝ) (x₀ : E)
    {Δ₀ η₁ η₂ γ₁ γ₂ γ₃ θ L : ℝ}
    (_hΔ₀ : 0 < Δ₀) (hη₁ : 0 < η₁) (hη₂ : η₂ < 1) (hγ₁ : 0 < γ₁)
    (hγ₂ : 0 < γ₂) (hγ₂1 : γ₂ < 1) (hγ₃ : 1 < γ₃) (hθ : 0 < θ)
    (hf : ContDiff ℝ 2 f) (hL : 1 ≤ L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤
      L * ‖y - z‖) :
    ∃ κS > 0, ∃ κA > 0, ∃ κD > 0, ∃ κC > 0,
      ∀ flow : ℝ, (∀ y, flow ≤ f y) →
      ∀ ε₁ : ℝ, 0 < ε₁ → ε₁ ≤ 1 →
      ∀ ε₂ : ℝ, 0 < ε₂ → ε₂ ≤ 1 →
      ∀ (x s u : ℕ → E) (μ Δ ρ : ℕ → ℝ), x 0 = x₀ → Δ 0 = Δ₀ →
      (∀ N, (∀ i < N,
        ¬RegularizedTrustRegion.Stopped f (x i) (μ i) ε₁ (ε₂ : WithTop ℝ)) →
        trEpsilonRun f x s u μ Δ ρ η₁ η₂ γ₁ γ₂ γ₃ θ
          ε₂ ε₁ (ε₂ : WithTop ℝ) N) →
      ∃ K, ‖gradient f (x K)‖ ≤ ε₁ ∧ -ε₂ ≤ μ K ∧
        (∀ i < K, ε₁ < ‖gradient f (x i)‖ ∨ μ i < -ε₂) ∧
        trEpsilonRun f x s u μ Δ ρ η₁ η₂ γ₁ γ₂ γ₃ θ
          ε₂ ε₁ (ε₂ : WithTop ℝ) K ∧
        (RegularizedTrustRegion.functionEvaluations K : ℝ) ≤
          κA * (f x₀ - flow) / RegularizedTrustRegion.secondOrderScale ε₁ ε₂ +
            κD * |Real.log ε₂| + κC ∧
        (RegularizedTrustRegion.derivativeEvaluations ρ η₁ K : ℝ) ≤
          κS * (f x₀ - flow) / RegularizedTrustRegion.secondOrderScale ε₁ ε₂ + 1 ∧
        (RegularizedTrustRegion.derivativeEvaluations ρ η₁ K : ℝ) ≤
          κS * (f x₀ - flow) / RegularizedTrustRegion.secondOrderScale ε₁ ε₂ + 1 := by
  obtain ⟨δ, hδ, hgap⟩ : ∃ δ > 0, ∀ flow : ℝ, (∀ y, flow ≤ f y) →
      gradient f x₀ ≠ 0 → δ ≤ f x₀ - flow := by
    by_cases hg : gradient f x₀ = 0
    · exact ⟨1, zero_lt_one, fun _ _ hn => (hn hg).elim⟩
    · obtain ⟨y, hy⟩ := Descent.exists_lt_of_gradient_ne_zero
        (hf.differentiable (by norm_num)).differentiableAt hg
      exact ⟨f x₀ - f y, sub_pos.mpr hy, fun _ hlo _ => sub_le_sub_left (hlo y) _⟩
  let c := RegularizedTrustRegion.decreaseCoefficient η₁ η₂ γ₁ L θ
  let S := 2 / c + 1 / δ
  let A := 1 + Real.log γ₃ / |Real.log γ₂|
  let B := 1 / |Real.log γ₂|
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
  refine ⟨S, hS, S * A, mul_pos hS hA, B, hB, C, hC, ?_⟩
  intro flow hlow ε₁ _hε₁ _hε₁1 ε₂ _hε₂ hε₂1 x s u μ Δ ρ hx hΔ hprefix
  obtain ⟨K, hstop, hK, _⟩ := RegularizedTrustRegion.exists_secondOrder_termination
    hprefix hf hL hlip hlow
  have htests := (RegularizedTrustRegion.stopped_iff _ _ _ _ _).mp hstop
  have hD := hK.secondOrder_successful_card_le_with_gap rfl hf hL hlip hlow hδ
    (by simpa only [hx] using hgap flow hlow) hε₂1
  have hD' : (RegularizedTrustRegion.derivativeEvaluations ρ η₁ K : ℝ) ≤
      S * (f x₀ - flow) / RegularizedTrustRegion.secondOrderScale ε₁ ε₂ + 1 := by
    rw [hx] at hD
    simpa only [RegularizedTrustRegion.derivativeEvaluations, Nat.cast_add, Nat.cast_one]
      using add_le_add hD (le_refl (1 : ℝ))
  refine ⟨K, htests.1, htests.2 ε₂ rfl, fun _ hi => hK.finite_failure rfl hi,
    hK, ?_, hD', hD'⟩
  have hb := hK.secondOrder_iterations_le rfl hf hL hlip hlow
  rw [hx, hΔ] at hb
  have hS0 : 2 / c ≤ S := by
    have hh : 0 ≤ 1 / δ := by positivity
    dsimp only [S]
    linarith
  have ha : 0 < RegularizedTrustRegion.secondOrderScale ε₁ ε₂ :=
    RegularizedTrustRegion.secondOrderScale_pos _hε₁ _hε₂
  have hlead : 2 * (f x₀ - flow) /
      (c * RegularizedTrustRegion.secondOrderScale ε₁ ε₂) ≤
      S * (f x₀ - flow) / RegularizedTrustRegion.secondOrderScale ε₁ ε₂ := by
    calc
      _ = (2 / c) * (f x₀ - flow) /
          RegularizedTrustRegion.secondOrderScale ε₁ ε₂ := by ring
      _ ≤ _ := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hS0 (sub_nonneg.mpr (hlow _))) ha.le
  simp only [RegularizedTrustRegion.functionEvaluations, Nat.cast_add, Nat.cast_one]
  calc
    (K : ℝ) + 1 ≤ (2 * (f x₀ - flow) /
        (c * RegularizedTrustRegion.secondOrderScale ε₁ ε₂) + 1) * A +
        (|Real.log ((1 - η₂) * γ₁ / (L * Δ₀))| + |Real.log ε₂|) /
          |Real.log γ₂| + 1 := add_le_add hb le_rfl
    _ ≤ (S * (f x₀ - flow) / RegularizedTrustRegion.secondOrderScale ε₁ ε₂ + 1) * A +
        (|Real.log ((1 - η₂) * γ₁ / (L * Δ₀))| + |Real.log ε₂|) /
          |Real.log γ₂| + 1 := by gcongr
    _ = _ := by dsimp [A, B, C]; rw [mul_comm Δ₀ L]; ring

/-- **Lemma3.4.10.** Between consecutive accepted trials, the number of actual
rejected trials is bounded by the printed logarithmic allowance. The underlying
bound also covers initial and terminal rejected blocks. -/
theorem lemma_3_4_10 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {f : E → ℝ} {x s : ℕ → E} {V : ℕ → Submodule ℝ E}
    {μ ℓ σL σU ρ : ℕ → ℝ}
    {η γ₁ γ₂ σmin σmax κ₁ κ₂ κ₃ κ₄ ε₁ L : ℝ}
    {ε₂ : WithTop ℝ} {N i j : ℕ}
    (h : inexactRegularizedNewtonRun f x s V μ ℓ σL σU ρ η γ₁ γ₂ σmin σmax
      κ₁ κ₂ κ₃ κ₄ ε₁ ε₂ N)
    (hf : ContDiff ℝ 2 f) (hL : 0 ≤ L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤
      L * ‖y - z‖) (hij : i < j) (hj : j < N)
    (_hiaccepted : η ≤ ρ i) (_hjaccepted : η ≤ ρ j)
    (hconsecutive : ∀ k, i < k → k < j → ¬η ≤ ρ k) :
    ((j - i - 1 : ℕ) : ℝ) ≤
      Real.log (irnUpperRegularizationBound σmax γ₂ η κ₂ L / σmin) /
        Real.log γ₁ + 1 := by
  have hh := h.rejected_block_le hf hL hlip (a := i + 1) (b := j) (by omega) hj.le
    (fun k hk hjk => hconsecutive k (by omega) hjk)
  simpa only [show j - (i + 1) = j - i - 1 by omega] using hh

end CartisGouldToint
