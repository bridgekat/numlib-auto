import Numlib.Optimization.ConstrainedSmoothnessAlgebra
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Least-squares objectives with a scalar target

The target enters a squared residual affinely, apart from an additive constant. Smoothness
of the two target functions at zero and one therefore controls every bounded target family.
-/

noncomputable section
namespace Optimization.TargetLeastSquares

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] {f : E → ℝ} {c : E → F}

/-- The half squared residual obtained by adjoining `f x - t` to a constraint residual. -/
def objective (f : E → ℝ) (c : E → F) (t : ℝ) (x : E) : ℝ :=
  (‖c x‖ ^ 2 + (f x - t) ^ 2) / 2

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Every scalar-target least-squares objective is nonnegative. -/
theorem objective_nonneg (f : E → ℝ) (c : E → F) (t : ℝ) (x : E) :
    0 ≤ objective f c t x := by unfold objective; positivity

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The entire target family is an affine combination of targets zero and one, plus a constant. -/
theorem objective_affine_target (f : E → ℝ) (c : E → F) (t : ℝ) :
    objective f c t = fun x => (1 - t) * objective f c 0 x +
      t * objective f c 1 x + t * (t - 1) / 2 := by
  funext x
  unfold objective
  ring

open ConstrainedRegularization

/-- Two fixed derivative Lipschitz bounds control an arbitrary target. -/
theorem smoothOn_of_two_targets {C : Set E} {p : ℕ} {L₀ L₁ : ℝ}
    (h₀ : SmoothOn (objective f c 0) C p L₀)
    (h₁ : SmoothOn (objective f c 1) C p L₁) (t : ℝ) :
    SmoothOn (objective f c t) C p (|1 - t| * L₀ + |t| * L₁) := by
  rw [objective_affine_target]
  exact ((h₀.const_mul (1 - t)).add (h₁.const_mul t)).add_const (t * (t - 1) / 2)

/-- Bounded targets have one explicit highest-derivative Lipschitz constant. -/
theorem smoothOn_of_abs_target_le {C : Set E} {p : ℕ} {L₀ L₁ B t : ℝ}
    (h₀ : SmoothOn (objective f c 0) C p L₀)
    (h₁ : SmoothOn (objective f c 1) C p L₁) (ht : |t| ≤ B) :
    SmoothOn (objective f c t) C p ((1 + B) * L₀ + B * L₁) := by
  apply (smoothOn_of_two_targets h₀ h₁ t).mono_constant
  have hsub : |1 - t| ≤ 1 + |t| := by
    simpa only [sub_eq_add_neg, abs_one, abs_neg] using abs_add_le (1 : ℝ) (-t)
  exact add_le_add (mul_le_mul_of_nonneg_right (hsub.trans (by linarith)) h₀.nonneg)
    (mul_le_mul_of_nonneg_right ht h₁.nonneg)

/-- An interval of target values has an explicit uniform derivative bound. -/
theorem smoothOn_of_target_mem_Icc {C : Set E} {p : ℕ} {L₀ L₁ a b t : ℝ}
    (h₀ : SmoothOn (objective f c 0) C p L₀)
    (h₁ : SmoothOn (objective f c 1) C p L₁) (ht : t ∈ Set.Icc a b) :
    SmoothOn (objective f c t) C p
      ((1 + max |a| |b|) * L₀ + max |a| |b| * L₁) := by
  apply smoothOn_of_abs_target_le h₀ h₁
  apply abs_le.mpr
  constructor
  · have ha := le_max_left |a| |b|
    have haa := neg_abs_le a
    linarith [ht.1]
  · exact ht.2.trans ((le_abs_self b).trans (le_max_right |a| |b|))

section Derivative
variable [InnerProductSpace ℝ F] {x : E} {f' : E →L[ℝ] ℝ} {c' : E →L[ℝ] F}

/-- The derivative combines the true constraint residual and objective-target residual. -/
theorem objective_hasFDerivAt (hf : HasFDerivAt f f' x) (hc : HasFDerivAt c c' x)
    (t : ℝ) : HasFDerivAt (objective f c t)
      ((innerSL ℝ (c x)).comp c' + (f x - t) • f') x := by
  convert (hc.norm_sq.add ((hf.sub_const t).pow 2)).const_mul (1 / 2) using 1
  · funext z
    unfold objective
    simp only [Pi.add_apply]
    ring
  · ext v
    simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply,
            innerSL_apply_apply, smul_eq_mul, Nat.reduceSub, pow_one]
    ring

end Derivative
end Optimization.TargetLeastSquares
