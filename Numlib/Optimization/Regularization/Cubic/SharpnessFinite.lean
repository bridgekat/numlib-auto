import Numlib.Optimization.Sharpness.Curvature
import Numlib.Optimization.Regularization.Cubic.Sharpness

/-!
# The plateau execution with both AR2 stopping tests

The smooth first-order plateau also satisfies the actual second-order cubic-model
condition. Its terminal objective Hessian is positive. Thus the same slow first-order
execution remains a genuine AR2 execution for every positive second-order tolerance.
-/

namespace CubicRegularization
open Set TaylorModel

/-- The cubic-model Hessian on the linear plateau is positive semidefinite at every
positive scalar trial step. -/
theorem smoothPlateau_model_curvature {r ε X z t σ : ℝ}
    (hr : 0 < r) (hz : z ≤ X) (ht : 0 < t) (hσ : 0 ≤ σ) (v : ℝ) :
    0 ≤ iteratedFDeriv ℝ 2 (model (smoothPlateau r ε X) z σ) t (fun _ => v) := by
  rw [iteratedFDeriv_two_apply,
    fderiv_fderiv_model (contDiff_smoothPlateau r ε X).contDiffAt]
  simp only [add_apply]
  rw [secondDerivative_smoothPlateau_eq_zero hr ε X z hz, zero_apply, zero_apply, zero_add,
    penaltySecondDerivative_apply, Real.norm_of_nonneg ht.le]
  simp only [RCLike.inner_apply, conj_trivial]
  have he : σ / 2 * (t * (v * v) + (v * t) * (v * t) / t) = σ * t * v ^ 2 := by
    field_simp
    ring
  rw [he]
  positivity

/-- The complete smooth-plateau execution passes the second model test and terminates
with nonnegative actual Hessian, for every positive second-order tolerance. -/
theorem plateau_finiteRun {η₁ η₂ γ₁ γ₂ γ₃ θ₁ θ₂ σ ε₁ ε₂ t : ℝ} {N : ℕ}
    (hη₁ : 0 < η₁) (hη : η₁ ≤ η₂) (hη₂ : η₂ < 1)
    (hγ₁ : 0 < γ₁) (hγ₁1 : γ₁ < 1) (hγ₂ : 1 < γ₂) (hγ₃ : γ₂ < γ₃)
    (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂) (hσ : 0 < σ)
    (hε₁ : 0 < ε₁) (hε₁1 : ε₁ ≤ 1) (hε₂ : 0 < ε₂) (hε₂1 : ε₂ ≤ 1)
    (ht : 0 < t) (hscale : σ * t ^ 2 = 4 * ε₁) (hN : 0 < N) :
    let r := t * (1 - η₂)
    let X := (N : ℝ) * t - r
    let f := smoothPlateau r ε₁ X
    let x := fun i : ℕ => (i : ℝ) * t
    let ρ := plateauRatio f x t
    let μ := fun i => iteratedDeriv 2 f (x i)
    FiniteRun f x (fun _ => t) (fun _ => 1) μ (fun _ => σ) ρ
      η₁ η₂ γ₁ γ₂ γ₃ σ θ₁ θ₂ ε₁ ε₂ N ∧
      (∀ i < N, η₂ ≤ ρ i) ∧
      ‖fderiv ℝ f (x N)‖ = ε₁ ∧ 0 ≤ μ N ∧
      ∀ i < N, ε₁ < ‖fderiv ℝ f (x i)‖ := by
  let r := t * (1 - η₂)
  let X := (N : ℝ) * t - r
  let f := smoothPlateau r ε₁ X
  let x := fun i : ℕ => (i : ℝ) * t
  let ρ := plateauRatio f x t
  let μ := fun i => iteratedDeriv 2 f (x i)
  obtain ⟨hfirst, hvery, hterm⟩ := plateau_firstOrderRun hη₁ hη hη₂ hγ₁ hγ₁1 hγ₂ hγ₃
    hθ₁ hσ hε₁ hε₁1 ht hscale hN
  have hr : 0 < r := mul_pos ht (sub_pos.mpr hη₂)
  have hrt : r < t := by dsimp [r]; nlinarith [hη₁.trans_le hη]
  have hxleft : ∀ i < N, x i ≤ X := by
    intro i hi
    have hi' : (i : ℝ) + 1 ≤ N := by exact_mod_cast hi
    dsimp [x, X]
    nlinarith
  have hfinite : FiniteRun f x (fun _ => t) (fun _ => 1) μ (fun _ => σ) ρ
      η₁ η₂ γ₁ γ₂ γ₃ σ θ₁ θ₂ ε₁ ε₂ N := by
    refine ⟨hfirst.trace, hθ₁, hθ₂, hε₁, hε₁1, hε₂, hε₂1,
      (fun i _ => CurvatureSharpness.leastEigenpair f (x i)), ?_,
      hfirst.stationary, ?_, hfirst.step⟩
    · intro i hi
      exact Or.inl (hfirst.not_terminated i hi)
    · intro i hi v hv
      exact (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hθ₂.le) (norm_nonneg t)).trans
        (smoothPlateau_model_curvature hr (hxleft i hi) ht hσ.le v)
  refine ⟨hfinite, hvery, hterm, ?_, hfirst.not_terminated⟩
  change 0 ≤ iteratedDeriv 2 (smoothPlateau r ε₁ X) (x N)
  have hxN : x N = X + r := by dsimp [x, X]; ring
  rw [iteratedDeriv_two_smoothPlateau, hxN, (smoothPlateau_at_middle hr ε₁ X).2.2]
  positivity

set_option maxHeartbeats 800000 in
/-- Uniformly regular, bounded-gap objectives force the full first-order sharpness
bound with both finite AR2 stopping tests enabled. The regularity constant and initial
objective budget are independent of both accuracies. All three initialized counters
meet the inverse first-accuracy lower bound. -/
theorem exists_slow_finiteRun_first_branch {η₁ η₂ γ₁ γ₂ γ₃ θ θ₂ σ : ℝ}
    (hη₁ : 0 < η₁) (hη : η₁ ≤ η₂) (hη₂ : η₂ < 1)
    (hγ₁ : 0 < γ₁) (hγ₁1 : γ₁ < 1) (hγ₂ : 1 < γ₂) (hγ₃ : γ₂ < γ₃)
    (hθ : 0 < θ) (hθ₂ : 0 < θ₂) (hσ : 0 < σ) :
    ∃ L ≥ 1, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∀ ε₂ : ℝ, 0 < ε₂ → ε₂ ≤ 1 →
      ∃ (f : ℝ → ℝ) (x : ℕ → ℝ) (t : ℝ) (ρ : ℕ → ℝ) (N : ℕ),
        x 0 = 0 ∧ ContDiff ℝ 2 f ∧ (∀ z, 0 ≤ f z) ∧
        (∀ z w, ‖iteratedFDeriv ℝ 2 f z - iteratedFDeriv ℝ 2 f w‖ ≤ L * ‖z - w‖) ∧
        f (x 0) ≤ 8 / Real.sqrt σ ∧
        N = ⌈1 / ε ^ (3 / 2 : ℝ)⌉₊ ∧
        FiniteRun f x (fun _ => t) (fun _ => 1)
          (fun i => iteratedDeriv 2 f (x i)) (fun _ => σ) ρ
          η₁ η₂ γ₁ γ₂ γ₃ σ θ θ₂ ε ε₂ N ∧
        (∀ i < N, η₂ ≤ ρ i) ∧ ‖fderiv ℝ f (x N)‖ = ε ∧
        0 ≤ iteratedDeriv 2 f (x N) ∧
        (∀ i < N, ¬(‖fderiv ℝ f (x i)‖ ≤ ε ∧ -ε₂ ≤ iteratedDeriv 2 f (x i))) ∧
        1 / ε ^ (3 / 2 : ℝ) ≤ N ∧
        1 / ε ^ (3 / 2 : ℝ) ≤ (functionEvaluations N : ℝ) ∧
        1 / ε ^ (3 / 2 : ℝ) ≤
          (gradientEvaluations ρ η₁ N : ℝ) ∧
        1 / ε ^ (3 / 2 : ℝ) ≤ (hessianEvaluations ρ η₁ N : ℝ) := by
  let a := 1 - η₂
  have ha : 0 < a := sub_pos.mpr hη₂
  refine ⟨1 + 2 * σ / a ^ 2, by
    have hh : 0 ≤ 2 * σ / a ^ 2 := by positivity
    linarith, ?_⟩
  intro ε hε hε1 ε₂ hε₂ hε₂1
  let e := Real.sqrt ε
  let b := Real.sqrt σ
  let t := 2 * e / b
  let r := t * a
  let N := ⌈1 / ε ^ (3 / 2 : ℝ)⌉₊
  let X := (N : ℝ) * t - r
  let f := smoothPlateau r ε X
  let x := fun i : ℕ => (i : ℝ) * t
  let ρ := plateauRatio f x t
  have he : 0 < e := Real.sqrt_pos.mpr hε
  have hb : 0 < b := Real.sqrt_pos.mpr hσ
  have he2 : e ^ 2 = ε := Real.sq_sqrt hε.le
  have hb2 : b ^ 2 = σ := Real.sq_sqrt hσ.le
  have ht : 0 < t := by dsimp [t]; positivity
  have hr : 0 < r := mul_pos ht ha
  have hpow : ε ^ (3 / 2 : ℝ) = ε * e := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hε,
      Real.rpow_one, ← Real.sqrt_eq_rpow]
  have hscale : σ * t ^ 2 = 4 * ε := by
    dsimp [t]
    rw [div_pow, mul_pow, hb2, mul_div_cancel₀ _ hσ.ne']
    nlinarith
  have hN : 0 < N := Nat.ceil_pos.mpr (by positivity)
  have hrun := plateau_finiteRun hη₁ hη hη₂ hγ₁ hγ₁1 hγ₂ hγ₃
    hθ hθ₂ hσ hε hε1 hε₂ hε₂1 ht hscale hN
  change FiniteRun f x (fun _ => t) (fun _ => 1)
    (fun i => iteratedDeriv 2 f (x i)) (fun _ => σ) ρ
    η₁ η₂ γ₁ γ₂ γ₃ σ θ θ₂ ε ε₂ N ∧ _ at hrun
  classical
  have hcard : (EvaluationComplexity.successfulIterations {i | η₁ ≤ ρ i} N).card = N := by
    unfold EvaluationComplexity.successfulIterations
    change ((Finset.range N).filter (fun i => η₁ ≤ ρ i)).card = N
    have hall : ∀ i ∈ Finset.range N, η₁ ≤ ρ i :=
      fun i hi => hη.trans (hrun.2.1 i (Finset.mem_range.mp hi))
    rw [Finset.filter_eq_self.mpr hall]
    exact Finset.card_range N
  have hcount : 1 / ε ^ (3 / 2 : ℝ) ≤ (N : ℝ) := Nat.le_ceil _
  refine ⟨f, x, t, ρ, N, by simp [x], contDiff_smoothPlateau r ε X,
    smoothPlateau_nonneg hr hε.le X, ?_, ?_, rfl, hrun.1, hrun.2.1,
    hrun.2.2.1, hrun.2.2.2.1, ?_, hcount, ?_, ?_, ?_⟩
  · intro z w
    have hc : 8 * ε / r ^ 2 = 2 * σ / a ^ 2 := by
      apply (div_eq_div_iff (by positivity : r ^ 2 ≠ 0) (by positivity : a ^ 2 ≠ 0)).mpr
      dsimp [r]
      nlinarith [hscale]
    rw [← add_zero (1 + 2 * σ / a ^ 2)]
    calc
      _ ≤ (8 * ε / r ^ 2) * ‖z - w‖ := smoothPlateau_tensor_lipschitz hr hε.le X z w
      _ ≤ _ := by rw [hc]; nlinarith [norm_nonneg (z - w)]
  · have hx0 : x 0 = 0 := by simp [x]
    have hX : 0 ≤ X := by
      have hn : 1 ≤ (N : ℝ) := by exact_mod_cast hN
      have ha1 : a < 1 := by dsimp [a]; linarith
      dsimp [X, r]
      nlinarith
    rw [hx0]
    change smoothPlateau r ε X 0 ≤ _
    rw [(smoothPlateau_on_left hr ε X 0 hX).1]
    have he1 : e ≤ 1 := by
      dsimp [e]
      exact (Real.sqrt_le_one).mpr hε1
    have hprod : ε * e ≤ 1 := by nlinarith
    have hceil : (N : ℝ) < 1 / (ε * e) + 1 := by
      have hh : (N : ℝ) < 1 / ε ^ (3 / 2 : ℝ) + 1 := Nat.ceil_lt_add_one (by positivity)
      simpa only [hpow] using hh
    have hNprod : (N : ℝ) * (ε * e) ≤ 2 := by
      have hh := (mul_lt_mul_iff_left₀ (mul_pos hε he)).mpr hceil
      rw [add_mul, one_mul, div_mul_cancel₀ _ (mul_pos hε he).ne'] at hh
      nlinarith
    apply (le_div_iff₀ hb).mpr
    have hid : (2 * ε * (X + r - 0)) * b = 4 * (N : ℝ) * (ε * e) := by
      dsimp [X, r, t]
      field_simp
      ring
    rw [hid]
    nlinarith
  · intro i hi hstop
    exact (not_le_of_gt (hrun.2.2.2.2 i hi)) hstop.1
  · simp only [functionEvaluations, Nat.cast_add, Nat.cast_one]
    linarith
  · simp only [gradientEvaluations, derivativeEvaluations, hcard, Nat.cast_add, Nat.cast_one]
    linarith
  · simp only [hessianEvaluations, derivativeEvaluations, hcard, Nat.cast_add, Nat.cast_one]
    linarith

end CubicRegularization
