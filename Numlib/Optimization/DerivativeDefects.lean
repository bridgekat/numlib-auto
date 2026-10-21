import Numlib.Optimization.HessianCurvatureContinuity

/-!
# Derivative defects

Gradient and negative-curvature defects characterize low-order stationary conditions.
A normalized third directional defect records the third derivative on the Hessian kernel;
no continuity of this kernel-dependent defect as the base point varies is asserted.
-/

noncomputable section
namespace Optimization.DerivativeDefects

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The first derivative defect of a gradient vector. -/
def first (g : E) : ℝ := ‖g‖

/-- The nonnegative part of negative least curvature. -/
def second (H : E →L[ℝ] E →L[ℝ] ℝ) : ℝ := max 0 (-leastCurvature H)

/-- The normalized absolute third derivative in directions annihilated by the Hessian.
The zero direction contributes zero, so the defining set is always nonempty. -/
def third (H : E →L[ℝ] E →L[ℝ] ℝ)
    (T : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) : ℝ :=
  sSup {v | ∃ d : E, H d = 0 ∧ v = |T d d d| / ‖d‖ ^ 3}

/-- A trilinear form is bounded by its iterated operator norm on a diagonal. -/
theorem abs_diagonal_le (T : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (d : E) :
    |T d d d| ≤ ‖T‖ * ‖d‖ ^ 3 := by
  have h₁ := (T d d).le_opNorm d
  have h₂ := (T d).le_opNorm d
  have h₃ := T.le_opNorm d
  rw [Real.norm_eq_abs] at h₁
  calc
    _ ≤ ‖T d d‖ * ‖d‖ := h₁
    _ ≤ (‖T d‖ * ‖d‖) * ‖d‖ := mul_le_mul_of_nonneg_right h₂ (norm_nonneg _)
    _ ≤ ((‖T‖ * ‖d‖) * ‖d‖) * ‖d‖ := by gcongr
    _ = _ := by ring

/-- Every normalized trilinear diagonal value is bounded by the tensor norm. -/
theorem normalized_diagonal_le (T : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (d : E) :
    |T d d d| / ‖d‖ ^ 3 ≤ ‖T‖ := by
  by_cases hd : d = 0
  · simp [hd]
  · exact (div_le_iff₀ (pow_pos (norm_pos_iff.mpr hd) 3)).mpr (abs_diagonal_le T d)

/-- The defining set for the third defect is bounded above. -/
theorem third_bddAbove (H : E →L[ℝ] E →L[ℝ] ℝ)
    (T : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :
    BddAbove {v | ∃ d : E, H d = 0 ∧ v = |T d d d| / ‖d‖ ^ 3} := by
  refine ⟨‖T‖, ?_⟩
  rintro v ⟨d, _, rfl⟩
  exact normalized_diagonal_le T d

/-- The third defect is nonnegative. -/
theorem third_nonneg (H : E →L[ℝ] E →L[ℝ] ℝ)
    (T : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) : 0 ≤ third H T := by
  apply le_csSup (third_bddAbove H T)
  exact ⟨0, by simp⟩

/-- A bound on the third defect is exactly a bound on every normalized kernel direction. -/
theorem third_le_iff (H : E →L[ℝ] E →L[ℝ] ℝ)
    (T : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (a : ℝ) :
    third H T ≤ a ↔ ∀ d : E, H d = 0 → |T d d d| / ‖d‖ ^ 3 ≤ a := by
  constructor
  · intro h d hd
    exact (le_csSup (third_bddAbove H T) ⟨d, hd, rfl⟩).trans h
  · intro h
    apply csSup_le
    · exact ⟨0, 0, by simp⟩
    · rintro v ⟨d, hd, rfl⟩
      exact h d hd

/-- The kernel-restricted third defect is bounded by the full tensor norm. -/
theorem third_le_norm (H : E →L[ℝ] E →L[ℝ] ℝ)
    (T : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) : third H T ≤ ‖T‖ :=
  (third_le_iff H T ‖T‖).mpr (fun d _ => normalized_diagonal_le T d)

/-- Vanishing third defect is equivalent to the full third directional kernel condition. -/
@[simp] theorem third_eq_zero_iff (H : E →L[ℝ] E →L[ℝ] ℝ)
    (T : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :
    third H T = 0 ↔ ∀ d : E, H d = 0 → T d d d = 0 := by
  constructor
  · intro h d hd
    by_cases hd0 : d = 0
    · simp [hd0]
    · have hv := (third_le_iff H T 0).mp h.le d hd
      have := (div_le_iff₀ (pow_pos (norm_pos_iff.mpr hd0) 3)).mp hv
      exact abs_eq_zero.mp (le_antisymm (by simpa using this) (abs_nonneg _))
  · intro h
    apply le_antisymm _ (third_nonneg H T)
    apply (third_le_iff H T 0).mpr
    intro d hd
    simp [h d hd]

omit [InnerProductSpace ℝ E] in
/-- Vanishing gradient defect characterizes a zero gradient. -/
@[simp] theorem first_eq_zero_iff (g : E) : first g = 0 ↔ g = 0 := norm_eq_zero

/-- Vanishing curvature defect characterizes a positive semidefinite bilinear form. -/
@[simp] theorem second_eq_zero_iff [Nontrivial E] (H : E →L[ℝ] E →L[ℝ] ℝ) :
    second H = 0 ↔ ∀ d : E, 0 ≤ H d d := by
  rw [second, max_eq_left_iff, neg_nonpos, le_leastCurvature_iff]
  simp

omit [InnerProductSpace ℝ E] in
/-- The gradient defect is nonnegative. -/
theorem first_nonneg (g : E) : 0 ≤ first g := norm_nonneg _

/-- The curvature defect is nonnegative. -/
theorem second_nonneg (H : E →L[ℝ] E →L[ℝ] ℝ) : 0 ≤ second H := le_max_left _ _

omit [InnerProductSpace ℝ E] in
/-- The gradient defect is continuous. -/
theorem continuous_first : Continuous (first (E := E)) := continuous_norm

/-- The negative-curvature defect is continuous in its Hessian argument. -/
theorem continuous_second [Nontrivial E] : Continuous (second (E := E)) :=
  continuous_const.max continuous_leastCurvature.neg

/-- The three derivative defects, indexed by orders minus one. -/
def measures (g : E) (H : E →L[ℝ] E →L[ℝ] ℝ)
    (T : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) : Fin 3 → ℝ := ![first g, second H, third H T]

/-- The first component of the defect vector. -/
@[simp] theorem measures_first (g : E) (H : E →L[ℝ] E →L[ℝ] ℝ)
    (T : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) : measures g H T 0 = first g := rfl

/-- The second component of the defect vector. -/
@[simp] theorem measures_second (g : E) (H : E →L[ℝ] E →L[ℝ] ℝ)
    (T : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) : measures g H T 1 = second H := rfl

/-- The third component of the defect vector. -/
@[simp] theorem measures_third (g : E) (H : E →L[ℝ] E →L[ℝ] ℝ)
    (T : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) : measures g H T 2 = third H T := rfl

/-- Only explicitly selected orders are tested against their tolerances. -/
def Satisfies (active : Finset (Fin 3)) (ε ω : Fin 3 → ℝ) : Prop :=
  ∀ j ∈ active, ω j ≤ ε j

/-- Membership in the activated tolerance test. -/
@[simp] theorem satisfies_iff (active : Finset (Fin 3)) (ε ω : Fin 3 → ℝ) :
    Satisfies active ε ω ↔ ∀ j ∈ active, ω j ≤ ε j := Iff.rfl

end Optimization.DerivativeDefects
