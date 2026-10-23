import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-!
# Algebraic model-decrease estimates

A regularization penalty converts improvement of a penalized model into a lower bound on the
unpenalized model decrement. A scaled decrement converts a failing normalized optimality test
into a uniform positive lower bound. These estimates depend on arithmetic and norms alone.
-/

namespace ModelDecrease

variable {E : Type*} [NormedAddCommGroup E]

/-- Add the norm-power penalty of degree `p+1` to an arbitrary real-valued model. -/
noncomputable def penalized (m : E → ℝ) (p : ℕ) (σ : ℝ) (s : E) : ℝ :=
  m s + σ / ((p + 1).factorial : ℝ) * ‖s‖ ^ (p + 1)

@[simp] theorem penalized_zero (m : E → ℝ) (p : ℕ) (σ : ℝ) :
    penalized m p σ 0 = m 0 := by
  simp [penalized]

/-- Any nonincreasing penalized-model step provides at least the norm-power penalty in the
unpenalized model decrement. No differentiability of the model is needed. -/
theorem penalty_le_decrement (m : E → ℝ) (p : ℕ) (σ : ℝ) (s : E)
    (hs : penalized m p σ s ≤ penalized m p σ 0) :
    σ / ((p + 1).factorial : ℝ) * ‖s‖ ^ (p + 1) ≤ m 0 - m s := by
  simp only [penalized_zero] at hs
  unfold penalized at hs
  linarith

/-- Strict improvement of the penalized model makes its norm-power penalty
strictly smaller than the unpenalized model decrease. -/
theorem penalty_lt_decrement (m : E → ℝ) (p : ℕ) (σ : ℝ) (s : E)
    (hs : penalized m p σ s < penalized m p σ 0) :
    σ / ((p + 1).factorial : ℝ) * ‖s‖ ^ (p + 1) < m 0 - m s := by
  simp only [penalized_zero] at hs
  unfold penalized at hs
  linarith

/-- A strictly positive improvement of the penalized model makes the unpenalized decrement
strictly positive when the regularization parameter is nonnegative. -/
theorem decrement_pos (m : E → ℝ) (p : ℕ) {σ : ℝ} (hσ : 0 ≤ σ) (d s : E)
    (hd : penalized m p σ d < penalized m p σ 0)
    (hs : penalized m p σ s ≤ penalized m p σ d) :
    0 < m 0 - m s := by
  have hpen : 0 ≤ σ / ((p + 1).factorial : ℝ) * ‖s‖ ^ (p + 1) :=
    mul_nonneg (div_nonneg hσ (Nat.cast_nonneg _)) (pow_nonneg (norm_nonneg _) _)
  have hstep := lt_of_le_of_lt hs hd
  simp only [penalized_zero] at hstep
  unfold penalized at hstep
  linarith

/-- Scaled model decrement used in normalized optimality tests. -/
noncomputable def scaled (a δ : ℝ) (j : ℕ) : ℝ := (j.factorial : ℝ) * a / δ ^ j

/-- Rescaling a decrement back to its original radius recovers the decrement. -/
theorem scaled_mul_radius (a : ℝ) {δ : ℝ} (hδ : 0 < δ) (j : ℕ) :
    scaled a δ j * δ ^ j / (j.factorial : ℝ) = a := by
  have hfact : (j.factorial : ℝ) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
  unfold scaled
  field_simp

/-- A failing normalized test yields a lower bound for its scaled decrement. -/
theorem le_scaled_of_test {a δ ε ζ : ℝ} (j : ℕ) (hδ : 0 < δ)
    (htest : ζ * ε * δ ^ j / (j.factorial : ℝ) < a) :
    ζ * ε ≤ scaled a δ j := by
  have hfact : (0 : ℝ) < j.factorial := by exact_mod_cast j.factorial_pos
  have hr : 0 < δ ^ j / (j.factorial : ℝ) := div_pos (pow_pos hδ _) hfact
  have hid := scaled_mul_radius a hδ j
  apply le_of_lt
  apply (mul_lt_mul_iff_of_pos_right hr).mp
  calc ζ * ε * (δ ^ j / (j.factorial : ℝ)) =
      ζ * ε * δ ^ j / (j.factorial : ℝ) := by ring
    _ < a := htest
    _ = scaled a δ j * (δ ^ j / (j.factorial : ℝ)) := by
      rw [← mul_div_assoc]
      exact hid.symm

end ModelDecrease
