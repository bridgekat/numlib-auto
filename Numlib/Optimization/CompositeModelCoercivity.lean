import Numlib.Optimization.TaylorModelGrowth
import Numlib.Optimization.CompositeRegularization

/-!
# Coercivity of actual regularized composite Taylor models

The scalar and vector Taylor polynomials grow at most as the model degree. A normalized
Lipschitz composition preserves that bound, so the positive radial term of one higher degree
dominates. Every sublevel is compact in a proper space and the global minimum is attained.
-/

noncomputable section
open scoped Nat NNReal
open Set Metric
namespace Optimization.CompositeTaylorModels
open RegularizedTaylorModel
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The actual composite polynomial is dominated by a common degree power outside the
unit ball. Normalization and Lipschitz continuity suffice for this growth bound. -/
theorem abs_model_le (f : E → ℝ) (c : E → F) (h : LipschitzSubadditiveComposition F)
    (p : ℕ) (x s : E) (hs : 1 ≤ ‖s‖) :
    |model f c h p x s| ≤
      (normCoefficientBound f p x + h.constant * normCoefficientBound c p x) * ‖s‖ ^ p := by
  calc
    _ ≤ |taylorModel f p x s| + |h (taylorModel c p x s)| := abs_add_le _ _
    _ ≤ normCoefficientBound f p x * ‖s‖ ^ p +
        h.constant * (normCoefficientBound c p x * ‖s‖ ^ p) := by
      apply add_le_add (by simpa only [Real.norm_eq_abs] using norm_taylorModel_le f p x s hs)
      exact (h.abs_apply_le _).trans (mul_le_mul_of_nonneg_left
        (norm_taylorModel_le c p x s hs) h.constant.coe_nonneg)
    _ = _ := by ring

/-- Positive regularization makes the actual composite model eventually exceed any
prescribed real value. The bound comes from its polynomial coefficients. -/
theorem regularizedModel_eventually_ge (f : E → ℝ) (c : E → F)
    (h : LipschitzSubadditiveComposition F) (p : ℕ) (x : E) {σ : ℝ}
    (hσ : 0 < σ) (b : ℝ) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ s : E, R ≤ ‖s‖ → b ≤ regularizedModel f c h p x σ s := by
  have he := eventually_ge_regularized_of_lower_bound (a := σ / ((p + 1)! : ℝ)) p
    (div_pos hσ (by positivity))
    (fun s hs => (abs_le.mp (abs_model_le f c h p x s hs)).1) b
  simpa only [regularizedModel, div_mul_eq_mul_div] using he

/-- The actual regularized composite model is continuous, including at its origin. -/
theorem continuous_regularizedModel (f : E → ℝ) (c : E → F)
    (h : LipschitzSubadditiveComposition F) (p : ℕ) (x : E) (σ : ℝ) :
    Continuous (regularizedModel f c h p x σ) :=
  (continuous_model f c h.lipschitz p x).add
    ((continuous_const.mul (continuous_norm.pow _)).div_const _)

/-- Positive actual composite regularization has compact sublevels in a proper space. -/
theorem isCompact_regularizedModel_sublevel [ProperSpace E] (f : E → ℝ) (c : E → F)
    (h : LipschitzSubadditiveComposition F) (p : ℕ) (x : E) {σ : ℝ} (hσ : 0 < σ) (b : ℝ) :
    IsCompact {s | regularizedModel f c h p x σ s ≤ b} := by
  apply isCompact_of_isClosed_isBounded
    (isClosed_le (continuous_regularizedModel f c h p x σ) continuous_const)
  obtain ⟨R, _, hb⟩ := regularizedModel_eventually_ge f c h p x hσ (b + 1)
  apply (isBounded_closedBall (x := (0 : E)) (r := R)).subset
  intro s hs
  have hn : ‖s‖ ≤ R := by
    by_contra hn
    have := hb s (le_of_lt (lt_of_not_ge hn))
    change regularizedModel f c h p x σ s ≤ b at hs
    linarith
  simpa only [mem_closedBall, dist_zero_right] using hn

/-- The actual positive regularized composite model attains its global minimum. -/
theorem exists_regularizedModel_minimizer [ProperSpace E] (f : E → ℝ) (c : E → F)
    (h : LipschitzSubadditiveComposition F) (p : ℕ) (x : E) {σ : ℝ} (hσ : 0 < σ) :
    ∃ z : E, ∀ t : E, regularizedModel f c h p x σ z ≤ regularizedModel f c h p x σ t := by
  let w := regularizedModel f c h p x σ
  obtain ⟨z, hz, hmin⟩ := (isCompact_regularizedModel_sublevel f c h p x hσ (w 0)).exists_isMinOn
    ⟨0, by dsimp [w]; exact le_rfl⟩ (continuous_regularizedModel f c h p x σ).continuousOn
  refine ⟨z, fun t => ?_⟩
  by_cases ht : w t ≤ w 0
  · exact hmin ht
  · exact hz.trans (le_of_not_ge ht)

end Optimization.CompositeTaylorModels
