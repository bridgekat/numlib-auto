import Numlib.Optimization.TrustRegion.FirstOrder
import Numlib.Optimization.LineSearch.Sharpness

/-!
# A sharp first-order trust-region example

Unit steepest-descent steps passing the half-Armijo test are also valid TR1
steps for the identity quadratic operator. The quadratic model predicts half
the linear decrease, so every such trial is very successful. The initial radius
is the fixed number two, independent of the requested accuracy.
-/

open Set QuadraticTrustRegion EvaluationComplexity

namespace FirstOrderTrustRegion
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The identity model's unconstrained minimizer is exactly the negative gradient. -/
theorem cauchyPoint_identity (f₀ : ℝ) (g : E) {Δ : ℝ} (hg : ‖g‖ ≤ Δ) :
    IsCauchyPoint f₀ g (ContinuousLinearMap.id ℝ E) Δ (-g) := by
  have he (u : ℝ) : model f₀ g (ContinuousLinearMap.id ℝ E) (-(u • g)) =
      f₀ + (u ^ 2 / 2 - u) * ‖g‖ ^ 2 := by
    simp only [model, ContinuousLinearMap.id_apply, inner_neg_right,
      inner_neg_left, inner_smul_right, inner_smul_left, real_inner_self_eq_norm_sq,
      starRingEnd_apply, star_trivial]
    ring
  refine ⟨1, by norm_num, by simpa using hg, by simp, ?_⟩
  intro u _
  change model f₀ g (ContinuousLinearMap.id ℝ E) (-(1 • g)) ≤
    model f₀ g (ContinuousLinearMap.id ℝ E) (-(u • g))
  rw [he 1, he u]
  nlinarith [mul_nonneg (sq_nonneg (u - 1)) (sq_nonneg ‖g‖)]

/-- The identity quadratic model predicts precisely half the squared gradient norm. -/
theorem identity_model_decrement (f₀ : ℝ) (g : E) :
    model f₀ g (ContinuousLinearMap.id ℝ E) 0 -
      model f₀ g (ContinuousLinearMap.id ℝ E) (-g) = ‖g‖ ^ 2 / 2 := by
  simp only [model, ContinuousLinearMap.id_apply, inner_zero_right,
    inner_neg_left, inner_neg_right, real_inner_self_eq_norm_sq, neg_neg]
  ring

/-- The objective-based acceptance ratio for the identity-model gradient step. -/
noncomputable def gradientStepRatio (f : E → ℝ) (g : E → E) (x : ℕ → E) (i : ℕ) : ℝ :=
  (f (x i) - f (x i - g (x i))) / (‖g (x i)‖ ^ 2 / 2)

/-- A zero-halving unit half-Armijo run is an actual TR1 run with identity
quadratic operators and fixed radius two. The ratio is derived from actual values. -/
theorem run_of_unit_backtracking {f : E → ℝ} {g : E → E} {x : ℕ → E}
    {η₁ η₂ γ₁ γ₂ γ₃ ε : ℝ} {N : ℕ}
    (hη₁ : 0 < η₁) (hη : η₁ ≤ η₂) (hη₂ : η₂ < 1)
    (hγ₁ : 0 < γ₁) (hγ : γ₁ ≤ γ₂) (hγ₂ : γ₂ < 1) (hγ₃ : 1 < γ₃)
    (hB : BacktrackingGradient.Run f g x (fun _ => 0) (1 / 2) 1 ε N)
    (hg : ∀ i < N, ‖g (x i)‖ ≤ 2) :
    Run f g x (fun i => -g (x i)) (fun i => -g (x i))
      (fun _ => ContinuousLinearMap.id ℝ E) (fun _ => 2) (gradientStepRatio f g x)
      η₁ η₂ γ₁ γ₂ γ₃ ε N ∧ ∀ i < N, 1 ≤ gradientStepRatio f g x i := by
  have hvery (i : ℕ) (hi : i < N) : 1 ≤ gradientStepRatio f g x i := by
    have hp : 0 < ‖g (x i)‖ := hB.accuracy_pos.trans (hB.not_terminated i hi)
    have hdec : ‖g (x i)‖ ^ 2 / 2 ≤ f (x i) - f (x i - g (x i)) := by
      simpa [BacktrackingGradient.Accepts, BacktrackingGradient.step_zero, LineSearch.Armijo,
        innerSL_apply_apply, real_inner_self_eq_norm_sq, sub_eq_add_neg, div_eq_inv_mul]
        using (show _ ≤ _ from sub_le_sub_left (hB.accepts i hi) (f (x i)))
    exact (le_div_iff₀ (by positivity : 0 < ‖g (x i)‖ ^ 2 / 2)).mpr (by simpa using hdec)
  have hrun : Run f g x (fun i => -g (x i)) (fun i => -g (x i))
      (fun _ => ContinuousLinearMap.id ℝ E) (fun _ => 2) (gradientStepRatio f g x)
      η₁ η₂ γ₁ γ₂ γ₃ ε N := by
    refine ⟨hB.derivative, ?_, hB.accuracy_pos, hB.not_terminated, ?_, ?_, ?_, ?_, ?_⟩
    · refine ⟨by norm_num, hη₁, hη, hη₂, hγ₁, hγ, hγ₂, hγ₃, ?_⟩
      intro i hi
      rw [ite_eq_left (hη₂.le.trans (hvery i hi))]
      exact ⟨le_rfl, by nlinarith⟩
    · intro i hi
      exact cauchyPoint_identity _ _ (hg i hi)
    · intro i hi
      simpa only [norm_neg] using hg i hi
    · intro i hi
      exact le_rfl
    · intro i hi
      rw [identity_model_decrement]
      simp only [gradientStepRatio, sub_eq_add_neg]
    · intro i hi
      rw [ite_eq_left (hη.trans (hη₂.le.trans (hvery i hi)))]
      simpa only [BacktrackingGradient.step_zero, one_smul, sub_eq_add_neg] using hB.update i hi
  exact ⟨hrun, hvery⟩

/-- Function calls consist of initialization and one objective evaluation per trial. -/
def functionEvaluations (N : ℕ) : ℕ := N + 1

/-- Gradient calls consist of initialization and one call per accepted trial. -/
noncomputable def gradientEvaluations (ρ : ℕ → ℝ) (η₁ : ℝ) (N : ℕ) : ℕ :=
  (successfulIterations {i | η₁ ≤ ρ i} N).card + 1

/-- A fixed-radius, uniformly smooth bounded-gap TR1 example attaining the
inverse-square lower bound, with a uniformly bounded identity model operator. -/
theorem exists_slow_run {η₁ η₂ γ₁ γ₂ γ₃ : ℝ}
    (hη₁ : 0 < η₁) (hη : η₁ ≤ η₂) (hη₂ : η₂ < 1)
    (hγ₁ : 0 < γ₁) (hγ : γ₁ ≤ γ₂) (hγ₂ : γ₂ < 1) (hγ₃ : 1 < γ₃)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ (f g : ℝ → ℝ) (x : ℕ → ℝ) (ρ : ℕ → ℝ) (N : ℕ),
      ContDiff ℝ 1 f ∧ (∀ y, HasFDerivAt f (innerSL ℝ (g y)) y) ∧
      (∀ y z, ‖g y - g z‖ ≤ 4 * ‖y - z‖) ∧
      (∀ y, 0 ≤ f y) ∧ f (x 0) ≤ 8 ∧ x 0 = 0 ∧
      N = ⌈1 / ε ^ 2⌉₊ ∧
      Run f g x (fun i => -g (x i)) (fun i => -g (x i))
        (fun _ => ContinuousLinearMap.id ℝ ℝ) (fun _ => 2) ρ η₁ η₂ γ₁ γ₂ γ₃ ε N ∧
      (∀ i < N, 1 ≤ ρ i) ∧ ‖g (x N)‖ = ε ∧
      ‖ContinuousLinearMap.id ℝ ℝ‖ ≤ 1 ∧
      1 / ε ^ 2 ≤ (N : ℝ) ∧
      functionEvaluations N = N + 1 ∧ gradientEvaluations ρ η₁ N = N + 1 ∧
      1 / ε ^ 2 ≤ (functionEvaluations N : ℝ) ∧
      1 / ε ^ 2 ≤ (gradientEvaluations ρ η₁ N : ℝ) := by
  let N := ⌈1 / ε ^ 2⌉₊
  let X := 2 * ε * (N : ℝ)
  let x := fun i : ℕ => 2 * ε * (i : ℝ)
  let f := BacktrackingGradient.plateauObjective (1 / 2) ε X
  let g := BacktrackingGradient.plateauGradient (1 / 2) ε X
  let ρ := gradientStepRatio f g x
  have hN : 0 < N := Nat.ceil_pos.mpr (by positivity)
  have hp : BacktrackingGradient.Run f g x (fun _ => 0) (1 / 2) 1 ε N ∧
      ‖g (x N)‖ = ε ∧ f (x 0) = 4 * ε ^ 2 * N := by
    simpa only [mul_one, one_mul, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] using
      BacktrackingGradient.plateau_run (by norm_num : (0 : ℝ) < 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1) (by norm_num : (0 : ℝ) < 1) hε hN
  have hg : ∀ i < N, ‖g (x i)‖ ≤ 2 := by
    intro i hi
    have hleft : x i ≤ X - (1 / 2) * ε := by
      simpa only [mul_one, one_mul, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] using
        BacktrackingGradient.plateau_orbit_linear (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (by norm_num : (0 : ℝ) < 1) hε hi
    have hl := BacktrackingGradient.plateau_linear (by norm_num : (0 : ℝ) < 1 / 2) hε.le hleft
    have hgi : g (x i) = -2 * ε := hl.2
    rw [hgi, norm_mul, norm_neg, Real.norm_ofNat, Real.norm_of_nonneg hε.le]
    linarith
  obtain ⟨hrun, hvery⟩ := run_of_unit_backtracking hη₁ hη hη₂ hγ₁ hγ hγ₂ hγ₃ hp.1 hg
  have hprod : (N : ℝ) * ε ^ 2 ≤ 2 := by
    have hc : (N : ℝ) < 1 / ε ^ 2 + 1 := Nat.ceil_lt_add_one (by positivity)
    have hm := mul_lt_mul_of_pos_right hc (sq_pos_of_pos hε)
    have hid : (1 / ε ^ 2 + 1) * ε ^ 2 = 1 + ε ^ 2 := by field_simp
    rw [hid] at hm
    nlinarith
  have hcard : (successfulIterations {i | η₁ ≤ ρ i} N).card = N := by
    have hset : successfulIterations {i | η₁ ≤ ρ i} N = Finset.range N := by
      ext i
      rw [mem_successfulIterations, Finset.mem_range]
      exact ⟨fun hi => hi.1, fun hi => ⟨hi, hη.trans (hη₂.le.trans (hvery i hi))⟩⟩
    rw [hset, Finset.card_range]
  have hcount : 1 / ε ^ 2 ≤ (N : ℝ) := Nat.le_ceil _
  refine ⟨f, g, x, ρ, N, BacktrackingGradient.contDiff_plateauObjective _ _ _, hp.1.derivative,
    ?_, BacktrackingGradient.plateauObjective_nonneg (by norm_num) hε.le X,
    by rw [hp.2.2]; nlinarith, by simp [x], rfl, hrun, hvery, hp.2.1,
    ContinuousLinearMap.norm_id_le, hcount, rfl, ?_, ?_, ?_⟩
  · intro y z
    simpa only [show (2 : ℝ) / (1 / 2) = 4 by norm_num] using
      BacktrackingGradient.plateauGradient_lipschitz (by norm_num : (0 : ℝ) < 1 / 2) ε X y z
  · simp only [gradientEvaluations, hcard]
  · simpa only [functionEvaluations, Nat.cast_add, Nat.cast_one] using
      hcount.trans (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1))
  · simp only [gradientEvaluations, hcard, Nat.cast_add, Nat.cast_one]
    linarith

end FirstOrderTrustRegion
