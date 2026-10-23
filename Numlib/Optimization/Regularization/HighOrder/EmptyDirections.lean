import Numlib.Optimization.Sharpness.Curvature
import Numlib.Optimization.Regularization.HighOrder.Step
import Numlib.Approximation.Hermite.Global
import Numlib.Analysis.Calculus.TaylorModel.Scalar


/-!
# An empty-direction obstruction in literal third-order ARp termination

For p = 3 a globally bounded C³ objective has initial jets `(4,-2,0,0)`
and a flat terminal jet at one. Its actual initial model is
`4 - 2s + s⁴/2`. The unit step is stationary, strictly improving, and accepted
with actual ratio two. Its model Hessian is six, so its inherited small-curvature
direction set is empty at θ₂ = 1. The printed nonempty-set stopping guard rejects
the flat endpoint, while every subsequent positive-parameter model is minimized
at zero. All parameter settings and actual model tests satisfy their source ranges.
-/

open Polynomial Set
namespace HighOrderRegularization
namespace EmptyDirections

/-- A two-point jet exhibiting the empty inherited model-direction obstruction. -/
def jet (k j : ℕ) : ℝ :=
  if k = 0 then if j = 0 then 4 else if j = 1 then -2 else 0 else 0

/-- The initial scalar interpolation jet is `(4,-2,0,0,...)`. -/
@[simp] theorem jet_zero (j : ℕ) :
    jet 0 j = if j = 0 then 4 else if j = 1 then -2 else 0 := rfl

/-- All scalar interpolation jets after the initial point vanish. -/
@[simp] theorem jet_succ (k j : ℕ) : jet (k + 1) j = 0 := by simp [jet]

/-- Both residuals and all prescribed jets obey a fixed Hermite bound. -/
theorem jet_residual {k j : ℕ} (hk : k < 1) (hj : j ≤ 3) :
    |jet (k + 1) j - (derivative^[j] (Hermite.initialPolynomial 3 (jet k))).eval 1| ≤
      4 * (1 : ℝ) ^ (3 - j + 1) := by
  have hk0 : k = 0 := by omega
  subst k
  have hpoly : Hermite.initialPolynomial 3 (jet 0) = C 4 - C 2 * X := by
    norm_num [Hermite.initialPolynomial, Hermite.jetPoly, Finset.sum_range_succ, jet]
    ring
  rw [hpoly]
  interval_cases j <;> norm_num [jet, Function.iterate_succ_apply]

/-- A bounded globally smooth objective realizes the two actual jets,
with globally Lipschitz D³. -/
theorem exists_objective :
    ∃ (f : ℝ → ℝ) (L B : ℝ), 1 ≤ L ∧ 0 < B ∧ ContDiff ℝ 3 f ∧
      (∀ x, |f x| ≤ B) ∧
      (∀ x y, ‖iteratedFDeriv ℝ 3 f x - iteratedFDeriv ℝ 3 f y‖ ≤ L * ‖x - y‖) ∧
      (∀ (k : ℕ), k ≤ 1 → ∀ j ≤ 3, iteratedDeriv j f (k : ℝ) = jet k j) := by
  obtain ⟨L,hL,B,hB,H⟩ := Hermite.exists_uniform_interpolant 3 4 (by norm_num)
  obtain ⟨f,hf,hLip,hjets,hbound⟩ := H 1 (by norm_num) (fun k => (k : ℝ)) jet
    (by intro i j hij _; exact_mod_cast hij)
    (by intro k hk j hj; simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_left]
      using jet_residual hk hj)
  refine ⟨f,max 1 L,B,le_max_left _ _,hB,hf,?_,?_,hjets⟩
  · have hdata : ((∀ k < 1, ∀ j ≤ 3, |jet k j| ≤ 4) ∧
        ∀ k < 1, (k + 1 : ℕ) - (k : ℝ) ≤ 4) := by
      constructor
      · intro k hk j hj
        have hk0 : k = 0 := by omega
        subst k
        interval_cases j <;> norm_num [jet]
      · intro k _
        simp
    intro x
    simpa only [iteratedDeriv_zero] using hbound hdata 0 (by omega) x
  · intro x y
    rw [norm_iteratedFDeriv_sub_eq_norm_iteratedDeriv_sub]
    exact (hLip.norm_sub_le x y).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))

/-- The actual first regularized model is a quartic with a strict minimum at one. -/
noncomputable def initialModelPolynomial : ℝ[X] := C 4 - C 2 * X + C (1 / 2) * X ^ 4

/-- The initial regularized model has the stated quartic scalar formula. -/
theorem initialModelPolynomial_eval (t : ℝ) :
    initialModelPolynomial.eval t = 4 - 2 * t + (1 / 2) * t ^ 4 := by
  simp [initialModelPolynomial]

/-- The actual model follows from the prescribed objective derivatives. -/
theorem model_initial {f : ℝ → ℝ}
    (hj : ∀ j ≤ 3, iteratedDeriv j f 0 = jet 0 j) :
    model f 3 0 12 = initialModelPolynomial.eval := by
  funext t
  rw [model_eq, TaylorModel.eval_eq_sum_iteratedDeriv]
  norm_num [Finset.sum_range_succ, hj, jet, initialModelPolynomial]
  have ha : |t| ^ 4 = t ^ 4 := by
    calc |t| ^ 4 = (|t| ^ 2) ^ 2 := by ring
         _ = (t ^ 2) ^ 2 := by rw [sq_abs]
         _ = t ^ 4 := by ring
  rw [ha]
  ring

/-- The initial model has derivative zero and actual Hessian six at the unit step. -/
theorem initialModel_derivatives :
    iteratedDeriv 1 initialModelPolynomial.eval 1 = 0 ∧
      iteratedDeriv 2 initialModelPolynomial.eval 1 = 6 := by
  constructor <;> rw [Polynomial.iteratedDeriv_eval] <;>
    norm_num [initialModelPolynomial, Function.iterate_succ_apply]

/-- The model direction set at this accepted endpoint is empty. -/
theorem smallModelDirections_empty {f : ℝ → ℝ}
    (hj : ∀ j ≤ 3, iteratedDeriv j f 0 = jet 0 j) :
    smallModelDirections f 3 0 1 12 1 = ∅ := by
  ext v
  simp only [mem_smallModelDirections_iff, mem_empty_iff_false, iff_false]
  rintro ⟨hv,hsmall⟩
  rw [model_initial hj, iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod,
    initialModel_derivatives.2] at hsmall
  have hv2 : v ^ 2 = 1 := by
    have hsq := congrArg (fun t : ℝ => t ^ 2) hv
    simpa only [Real.norm_eq_abs, sq_abs, one_pow] using hsq
  norm_num [Fin.prod_const, hv2] at hsmall

/-- Every genuine model stationarity test is satisfied, including the third-order test
on its empty small-curvature set. -/
theorem stepConditions {f : ℝ → ℝ}
    (hj : ∀ j ≤ 3, iteratedDeriv j f 0 = jet 0 j) :
    StepConditions f 3 0 1 12 1 1 1 := by
  refine ⟨?_,?_,?_⟩
  · rw [model_initial hj, ←norm_deriv_eq_norm_fderiv, ←iteratedDeriv_one,
      initialModel_derivatives.1]
    norm_num
  · intro v hv
    rw [model_initial hj, iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod,
      initialModel_derivatives.2]
    simp only [Fin.prod_const, smul_eq_mul]
    norm_num
    nlinarith [sq_nonneg v]
  · intro v hv
    rw [smallModelDirections_empty hj] at hv
    exact False.elim hv

/-- At the terminal flat jet, every positive-parameter model is minimized at zero. -/
theorem no_next_improvement {f : ℝ → ℝ}
    (hj : ∀ j ≤ 3, iteratedDeriv j f 1 = 0) {σ : ℝ} (hσ : 0 ≤ σ) :
    ¬ ∃ s : ℝ, model f 3 1 σ s < model f 3 1 σ 0 := by
  rintro ⟨s,hs⟩
  rw [model_eq, model_eq, TaylorModel.eval_eq_sum_iteratedDeriv,
    TaylorModel.eval_eq_sum_iteratedDeriv] at hs
  norm_num [Finset.sum_range_succ, hj] at hs
  have hh : 0 ≤ σ / 24 * |s| ^ 4 := by positivity
  linarith

/-- A one-step accepted trajectory from zero to one. -/
def point (k : ℕ) : ℝ := if k = 0 then 0 else 1

@[simp] theorem point_zero : point 0 = 0 := rfl

@[simp] theorem point_succ (k : ℕ) : point (k + 1) = 1 := by simp [point]

/-- The true acceptance ratio is two for the prescribed objective and derivative values. -/
theorem actual_ratio {f : ℝ → ℝ}
    (hjets : ∀ (k : ℕ), k ≤ 1 → ∀ j ≤ 3, iteratedDeriv j f (k : ℝ) = jet k j) :
    ratio f 3 0 1 = 2 := by
  have hj0 : ∀ j ≤ 3, iteratedDeriv j f 0 = jet 0 j := by simpa using hjets 0 (by omega)
  have h0 : f 0 = 4 := by simpa [jet] using hjets 0 (by omega) 0 (by omega)
  have h1 : f 1 = 0 := by simpa [jet] using hjets 1 le_rfl 0 (by omega)
  rw [ratio_eq, TaylorModel.decrement_eq, TaylorModel.eval_eq_sum_iteratedDeriv]
  norm_num [Finset.sum_range_succ, hj0, jet, h0, h1]

/-- A genuine legal accepted AR3 trial, with fixed legal update settings and actual ratio. -/
theorem modelTrace {f : ℝ → ℝ}
    (hjets : ∀ (k : ℕ), k ≤ 1 → ∀ j ≤ 3, iteratedDeriv j f (k : ℝ) = jet k j) :
    ModelTrace f 3 point (fun _ => 1) (fun _ => 12) (fun _ => 2)
      (1 / 4) (3 / 4) (1 / 2) 2 3 12 1 := by
  have hj0 : ∀ j ≤ 3, iteratedDeriv j f 0 = jet 0 j := by simpa using hjets 0 (by omega)
  refine ⟨by norm_num, ?_, ?_, ?_, ?_⟩
  · refine ⟨by norm_num,le_refl _,by norm_num,by norm_num,by norm_num,
      by norm_num,by norm_num,by norm_num,by norm_num,?_⟩
    intro i _
    norm_num
  · intro i hi
    have hi0 : i = 0 := by omega
    subst i
    change model f 3 0 12 1 < model f 3 0 12 0
    rw [model_initial hj0]
    norm_num [initialModelPolynomial]
  · intro i hi
    have hi0 : i = 0 := by omega
    subst i
    exact (actual_ratio hjets).symm
  · intro i hi
    have hi0 : i = 0 := by omega
    subst i
    norm_num [point]

/-- The literal finite-third-order stopping test, including the nonempty-set guard.
The one-dimensional least Hessian eigenvalue is the actual second derivative. -/
def literalStop (f : ℝ → ℝ) (x : ℝ) (M : Set ℝ) (ε₁ ε₂ ε₃ : ℝ) : Prop :=
  ‖deriv f x‖ ≤ ε₁ ∧
    (ε₂ < iteratedDeriv 2 f x ∨
      (-ε₂ ≤ iteratedDeriv 2 f x ∧ M.Nonempty ∧
        ∀ v ∈ M, |iteratedFDeriv ℝ 3 f x (fun _ => v)| ≤ ε₃ ∧
          |iteratedFDeriv ℝ 2 f x (fun _ => v)| ≤ ε₂))

/-- With no inherited directions, the literal test accepts only the strict-Hessian branch. -/
@[simp] theorem literalStop_empty_iff (f : ℝ → ℝ) (x ε₁ ε₂ ε₃ : ℝ) :
    literalStop f x ∅ ε₁ ε₂ ε₃ ↔
      ‖deriv f x‖ ≤ ε₁ ∧ ε₂ < iteratedDeriv 2 f x := by simp [literalStop]

/-- The actual initial gradient forces an attempted step under unit tolerances. -/
theorem not_initial_stop {f : ℝ → ℝ}
    (hj : ∀ j ≤ 3, iteratedDeriv j f 0 = jet 0 j) (M : Set ℝ) :
    ¬ literalStop f 0 M 1 1 1 := by
  have hg : deriv f 0 = -2 := by simpa [jet, iteratedDeriv_one] using hj 1 (by omega)
  simp [literalStop, hg]

/-- The literal stopping guard rejects the flat terminal jet when inherited directions are empty. -/
theorem not_terminal_stop {f : ℝ → ℝ}
    (hj0 : ∀ j ≤ 3, iteratedDeriv j f 0 = jet 0 j)
    (hj1 : ∀ j ≤ 3, iteratedDeriv j f 1 = 0) :
    ¬ literalStop f 1 (smallModelDirections f 3 0 1 12 1) 1 1 1 := by
  rw [smallModelDirections_empty hj0]
  simp [literalStop, hj1 2 (by omega)]

/-- The printed ARp nonempty-set guard can reject a genuine accepted stationary
endpoint at which no further strict model improvement is possible. The objective
is globally bounded, C³, and has globally Lipschitz D³; all settings and actual
model step tests are legal. Removing the nonempty-set guard admits the vacuous
third-direction test and avoids this obstruction. -/
theorem exists_stuck_execution :
    ∃ (f : ℝ → ℝ) (L B : ℝ), 1 ≤ L ∧ 0 < B ∧ ContDiff ℝ 3 f ∧
      (∀ x, |f x| ≤ B) ∧
      (∀ x y, ‖iteratedFDeriv ℝ 3 f x - iteratedFDeriv ℝ 3 f y‖ ≤ L * ‖x - y‖) ∧
      ModelTrace f 3 point (fun _ => 1) (fun _ => 12) (fun _ => 2)
        (1 / 4) (3 / 4) (1 / 2) 2 3 12 1 ∧
      StepConditions f 3 0 1 12 1 1 1 ∧
      smallModelDirections f 3 0 1 12 1 = ∅ ∧
      (∀ M : Set ℝ, ¬ literalStop f 0 M 1 1 1) ∧
      ¬ literalStop f 1 (smallModelDirections f 3 0 1 12 1) 1 1 1 ∧
      (∀ j ≤ 3, iteratedDeriv j f 1 = 0) ∧
      SecondOrderTrustRegion.IsLeastEigenpair f 1 0 1 ∧
      (∀ σ : ℝ, 0 ≤ σ → ¬ ∃ s : ℝ, model f 3 1 σ s < model f 3 1 σ 0) := by
  obtain ⟨f,L,B,hL,hB,hf,hbound,hLip,hjets⟩ := exists_objective
  have hj0 : ∀ j ≤ 3, iteratedDeriv j f 0 = jet 0 j := by simpa using hjets 0 (by omega)
  have hj1 : ∀ j ≤ 3, iteratedDeriv j f 1 = 0 := by simpa [jet] using hjets 1 le_rfl
  refine ⟨f,L,B,hL,hB,hf,hbound,hLip,modelTrace hjets,stepConditions hj0,
    smallModelDirections_empty hj0,not_initial_stop hj0,not_terminal_stop hj0 hj1,
    hj1,?_,fun _ hσ => no_next_improvement hj1 hσ⟩
  simpa only [hj1 2 (by omega)] using CurvatureSharpness.leastEigenpair f 1

end EmptyDirections
end HighOrderRegularization
