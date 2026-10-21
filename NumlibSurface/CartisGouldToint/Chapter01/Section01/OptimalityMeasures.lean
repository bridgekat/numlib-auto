import Numlib.Optimization.DerivativeDefects
import NumlibSurface.CartisGouldToint.Chapter01.Section01

/-!
# Chapter 1: unconstrained derivative defects

The first two entries are the displayed criticality measures in Section 1.1.2.6. The third
entry is an ancillary normalized third directional defect on the Hessian kernel. It encodes
the third necessary condition, but is not asserted continuous as the base point varies.
Optional orders are activated by a finite set, without arithmetic involving infinity.
-/

noncomputable section
namespace CartisGouldToint.Chapter01.Section01

variable {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)

/-- Gradient norm, negative minimum-Hessian-eigenvalue part, and normalized third directional
kernel defect, indexed by order minus one. The third entry is not a continuity claim. -/
def optimalityMeasures (x : EuclideanSpace ℝ (Fin n)) : Fin 3 → ℝ :=
  Optimization.DerivativeDefects.measures (gradient f x) (fderiv ℝ (fderiv ℝ f) x)
    (fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x)

/-- The first entry is exactly the gradient norm. -/
@[simp] theorem optimalityMeasures_first (x : EuclideanSpace ℝ (Fin n)) :
    optimalityMeasures f x 0 = ‖gradient f x‖ := rfl

/-- The second entry is the nonnegative part of negative least Hessian curvature. -/
@[simp] theorem optimalityMeasures_second (x : EuclideanSpace ℝ (Fin n)) :
    optimalityMeasures f x 1 = max 0 (-Optimization.leastCurvature
      (fderiv ℝ (fderiv ℝ f) x)) := rfl

/-- The third entry records the actual third derivative on the actual Hessian kernel. -/
@[simp] theorem optimalityMeasures_third (x : EuclideanSpace ℝ (Fin n)) :
    optimalityMeasures f x 2 = Optimization.DerivativeDefects.third
      (fderiv ℝ (fderiv ℝ f) x) (fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x) := rfl

/-- Each selected order is tested against its own finite tolerance. -/
def MeetsOptimalityTolerances (active : Finset (Fin 3)) (ε : Fin 3 → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  Optimization.DerivativeDefects.Satisfies active ε (optimalityMeasures f x)

/-- The activated stopping test has precisely the selected component inequalities. -/
@[simp] theorem meetsOptimalityTolerances_iff (active : Finset (Fin 3)) (ε : Fin 3 → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    MeetsOptimalityTolerances f active ε x ↔ ∀ j ∈ active, optimalityMeasures f x j ≤ ε j :=
  Iff.rfl

/-- Every entry of the vector of derivative defects is nonnegative. -/
theorem optimalityMeasures_nonneg (x : EuclideanSpace ℝ (Fin n)) (j : Fin 3) :
    0 ≤ optimalityMeasures f x j := by
  fin_cases j
  · exact norm_nonneg _
  · exact Optimization.DerivativeDefects.second_nonneg _
  · exact Optimization.DerivativeDefects.third_nonneg _ _

/-- Zero first defect is exactly first-order stationarity. -/
@[simp] theorem optimalityMeasures_first_eq_zero (x : EuclideanSpace ℝ (Fin n)) :
    optimalityMeasures f x 0 = 0 ↔ gradient f x = 0 := norm_eq_zero

/-- Zero second defect is exactly Hessian positive semidefiniteness. -/
@[simp] theorem optimalityMeasures_second_eq_zero [NeZero n]
    (x : EuclideanSpace ℝ (Fin n)) :
    optimalityMeasures f x 1 = 0 ↔ ∀ d, 0 ≤ fderiv ℝ (fderiv ℝ f) x d d :=
  Optimization.DerivativeDefects.second_eq_zero_iff _

/-- Zero third defect is exactly the third directional kernel condition. -/
@[simp] theorem optimalityMeasures_third_eq_zero (x : EuclideanSpace ℝ (Fin n)) :
    optimalityMeasures f x 2 = 0 ↔ ∀ d, fderiv ℝ (fderiv ℝ f) x d = 0 →
      fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x d d d = 0 :=
  Optimization.DerivativeDefects.third_eq_zero_iff _ _

/-- Under the first smoothness assumption, the displayed gradient measure is continuous. -/
theorem continuous_optimalityMeasures_first (hf : ContDiff ℝ 1 f) :
    Continuous (fun x => optimalityMeasures f x 0) := by
  have hD : Continuous (fderiv ℝ f) := (hf.fderiv_right (m := 0) (by norm_num)).continuous
  exact ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.continuous.comp hD).norm

/-- Under the second smoothness assumption, the displayed curvature measure is continuous. -/
theorem continuous_optimalityMeasures_second [NeZero n] (hf : ContDiff ℝ 2 f) :
    Continuous (fun x => optimalityMeasures f x 1) := by
  have hD : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hDD : Continuous (fderiv ℝ (fderiv ℝ f)) :=
    (hD.fderiv_right (m := 0) (by norm_num)).continuous
  exact Optimization.DerivativeDefects.continuous_second.comp hDD

/-- The earlier source necessary conditions imply all three defects vanish at a local minimum. -/
theorem optimalityMeasures_eq_zero_of_isLocalMin [NeZero n]
    (hf : ContDiff ℝ 3 f) {x : EuclideanSpace ℝ (Fin n)} (hx : IsLocalMin f x) :
    optimalityMeasures f x = 0 := by
  have h := theorem_1_1_1 f x
  funext j
  fin_cases j
  · exact (optimalityMeasures_first_eq_zero f x).mpr (h.1 (hf.of_le (by norm_num)) hx)
  · exact (optimalityMeasures_second_eq_zero f x).mpr (h.2.1 (hf.of_le (by norm_num)) hx)
  · exact (optimalityMeasures_third_eq_zero f x).mpr (h.2.2.1 hf hx)

end CartisGouldToint.Chapter01.Section01
