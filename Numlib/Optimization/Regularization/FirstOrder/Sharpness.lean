import Numlib.Optimization.Regularization.FirstOrder
import Numlib.Optimization.LineSearch.Sharpness
import Mathlib.Tactic

/-!
# Sharpness of first-order adaptive regularization

An actual zero-halving Armijo run at threshold `η₂` gives an AR1 run at fixed
regularization parameter `σmin`, with step `−σmin⁻¹∇f`. The achieved objective
reduction determines the true ratio, and Armijo acceptance proves that ratio is
at least `η₂`; the very-successful update therefore permits the parameter to stay
at its floor. Applying this conversion to the explicit plateau objective gives
an accuracy-independent Lipschitz constant and initial objective budget, while
requiring `ceil(ε⁻²)` iterations and one more function and gradient evaluation.
-/

namespace FirstOrderRegularization
open EvaluationComplexity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual ratio of objective reduction to unregularized model reduction. -/
noncomputable def actualRatio (f : E → ℝ) (g : E → E) (x : ℕ → E) (σ : ℕ → ℝ)
    (i : ℕ) : ℝ :=
  σ i * (f (x i) - f (x i - (σ i)⁻¹ • g (x i))) / ‖g (x i)‖ ^ 2

/-- The actual-ratio formula, including its positive-parameter trial point. -/
@[simp]
theorem actualRatio_apply (f : E → ℝ) (g : E → E) (x : ℕ → E) (σ : ℕ → ℝ) (i : ℕ) :
    actualRatio f g x σ i =
      σ i * (f (x i) - f (x i - (σ i)⁻¹ • g (x i))) / ‖g (x i)‖ ^ 2 := rfl

/-- A zero-halving Armijo run at threshold `η₂` is a very successful AR1 run
with constant regularization parameter, whose ratios use actual objective values. -/
theorem constant_run_of_backtracking
    {f : E → ℝ} {g : E → E} {x : ℕ → E} {η₁ η₂ γ₁ γ₂ γ₃ σmin ε : ℝ} {N : ℕ}
    (hσ : 0 < σmin) (hη₁ : 0 < η₁) (hη : η₁ ≤ η₂)
    (hγ₁0 : 0 < γ₁) (hγ₁1 : γ₁ < 1) (hγ₂ : 1 < γ₂) (hγ₃ : γ₂ < γ₃)
    (hB : BacktrackingGradient.Run f g x (fun _ => 0) η₂ σmin⁻¹ ε N) :
    Run f g x (fun _ => σmin) (actualRatio f g x (fun _ => σmin))
      η₁ η₂ γ₁ γ₂ γ₃ σmin ε N ∧
    ∀ i < N, η₂ ≤ actualRatio f g x (fun _ => σmin) i := by
  have hvery (i : ℕ) (hi : i < N) : η₂ ≤ actualRatio f g x (fun _ => σmin) i := by
    have hdec : η₂ * σmin⁻¹ * ‖g (x i)‖ ^ 2 ≤
        f (x i) - f (x i - σmin⁻¹ • g (x i)) := by
      simpa [BacktrackingGradient.Accepts,BacktrackingGradient.step_zero,LineSearch.Armijo,
        innerSL_apply_apply,real_inner_self_eq_norm_sq,smul_neg,sub_eq_add_neg]
        using (show _ ≤ _ from sub_le_sub_left (hB.accepts i hi) (f (x i)))
    have hnorm : 0 < ‖g (x i)‖ := hB.accuracy_pos.trans (hB.not_terminated i hi)
    apply (le_div_iff₀ (sq_pos_of_pos hnorm)).mpr
    calc
      η₂ * ‖g (x i)‖ ^ 2 = σmin * (η₂ * σmin⁻¹ * ‖g (x i)‖ ^ 2) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hdec hσ.le
  refine ⟨⟨hB.derivative,?_,hB.accuracy_pos,hB.not_terminated,?_,?_⟩,hvery⟩
  · refine ⟨hσ,le_rfl,hη₁,hη,hB.alpha_lt_one,hγ₁0,hγ₁1,hγ₂,hγ₃,?_⟩
    intro i hi
    rw [ite_eq_left (hvery i hi)]
    exact ⟨max_le le_rfl (mul_le_of_le_one_left hσ.le hγ₁1.le),le_rfl⟩
  · intro i hi
    rfl
  · intro i hi
    rw [ite_eq_left (hη.trans (hvery i hi))]
    simpa using hB.update i hi

/-- Function evaluations include the initialization and every trial objective. -/
def Run.functionEvaluations (N : ℕ) : ℕ := N + 1

/-- The function evaluation count includes initialization. -/
@[simp]
theorem Run.functionEvaluations_eq (N : ℕ) : Run.functionEvaluations N = N + 1 := rfl

/-- Gradient evaluations include initialization and the gradients at accepted points. -/
noncomputable def Run.gradientEvaluations (ρ : ℕ → ℝ) (η₁ : ℝ) (N : ℕ) : ℕ :=
  (successfulIterations {i | η₁ ≤ ρ i} N).card + 1

/-- Every successful update contributes one gradient evaluation. -/
theorem Run.gradientEvaluations_eq_of_all_successful {ρ : ℕ → ℝ} {η₁ : ℝ} {N : ℕ}
    (h : ∀ i < N, η₁ ≤ ρ i) : Run.gradientEvaluations ρ η₁ N = N + 1 := by
  have hset : successfulIterations {i | η₁ ≤ ρ i} N = Finset.range N := by
    ext i
    rw [mem_successfulIterations,Finset.mem_range]
    exact ⟨fun hi => hi.1,fun hi => ⟨hi,h i hi⟩⟩
  simp [Run.gradientEvaluations,hset]

/-- AR1 can need at least `ε⁻²` evaluations on a uniformly smooth bounded-below
objective, while keeping its regularization parameter fixed at its positive floor. -/
theorem exists_slow_run {η₁ η₂ γ₁ γ₂ γ₃ σmin : ℝ}
    (hσ : 0 < σmin) (hη₁ : 0 < η₁) (hη : η₁ ≤ η₂) (hη₂ : η₂ < 1)
    (hγ₁0 : 0 < γ₁) (hγ₁1 : γ₁ < 1) (hγ₂ : 1 < γ₂) (hγ₃ : γ₂ < γ₃) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ (f g : ℝ → ℝ) (x : ℕ → ℝ) (ρ : ℕ → ℝ) (N : ℕ),
        ContDiff ℝ 1 f ∧ (∀ y, HasFDerivAt f (innerSL ℝ (g y)) y) ∧
        (∀ y z, ‖g y - g z‖ ≤ L * ‖y - z‖) ∧
        (∀ y, 0 ≤ f y) ∧ f (x 0) ≤ 8 / σmin ∧ x 0 = 0 ∧
        N = ⌈1 / ε ^ 2⌉₊ ∧
        Run f g x (fun _ => σmin) ρ η₁ η₂ γ₁ γ₂ γ₃ σmin ε N ∧
        (∀ i < N, η₂ ≤ ρ i) ∧ ‖g (x N)‖ = ε ∧ (1 / ε ^ 2 : ℝ) ≤ N ∧
        Run.functionEvaluations N = N + 1 ∧
        Run.gradientEvaluations ρ η₁ N = N + 1 ∧
        (1 / ε ^ 2 : ℝ) ≤ Run.functionEvaluations N ∧
        (1 / ε ^ 2 : ℝ) ≤ Run.gradientEvaluations ρ η₁ N := by
  obtain ⟨L,hL,hslow⟩ := BacktrackingGradient.exists_slow_run
    (hη₁.trans_le hη) hη₂ (inv_pos.mpr hσ)
  refine ⟨L,hL,?_⟩
  intro ε hε hε1
  obtain ⟨f,g,x,N,hf,hderiv,hLip,hlo,hbudget,hx0,hN,hB,hstop,hNl,_,_,_⟩ := hslow ε hε hε1
  obtain ⟨hAR,hvery⟩ := constant_run_of_backtracking hσ hη₁ hη hγ₁0 hγ₁1 hγ₂ hγ₃ hB
  let ρ := actualRatio f g x (fun _ => σmin)
  have hG : Run.gradientEvaluations ρ η₁ N = N + 1 :=
    Run.gradientEvaluations_eq_of_all_successful (fun i hi => hη.trans (hvery i hi))
  have hcount : (1 / ε ^ 2 : ℝ) ≤ (N + 1 : ℕ) := hNl.trans (by simp)
  refine ⟨f,g,x,ρ,N,hf,hderiv,hLip,hlo,?_,hx0,hN,hAR,hvery,hstop,hNl,rfl,hG,hcount,?_⟩
  · simpa [div_eq_mul_inv] using hbudget
  · rw [hG]
    exact hcount
end FirstOrderRegularization
