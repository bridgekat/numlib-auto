/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.InnerProductSpace.PiL2`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Coordinate directions of Euclidean space

Facts about the coordinate directions `EuclideanSpace.single i 1` of `EuclideanSpace ℝ ι`:

* `EuclideanSpace.inner_single_smul_single_of_ne`, `EuclideanSpace.norm_smul_single`: inner
  products and norms of multiples of coordinate directions;
* `EuclideanSpace.eq_inner_single_smul_of_forall_ne`,
  `EuclideanSpace.norm_eq_abs_inner_single_of_forall_ne`: a vector orthogonal to all coordinate
  directions but one is a multiple of that direction, and its norm is the absolute value of the
  corresponding coordinate;
* `EuclideanSpace.eq_inner_single_smul`, `EuclideanSpace.norm_eq_abs_inner_single`: the case of
  `ℝ¹`, where every vector is a multiple of the coordinate direction.
-/

open scoped RealInnerProductSpace

namespace EuclideanSpace

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem inner_single_smul_single_of_ne {i j : ι} (h : i ≠ j) (c : ℝ) :
    ⟪single i (1 : ℝ), c • single j (1 : ℝ)⟫ = 0 := by
  simp [inner_single_left, h]

theorem inner_single_single_of_ne {i j : ι} (h : i ≠ j) :
    ⟪single i (1 : ℝ), single j (1 : ℝ)⟫ = 0 := by
  simpa using inner_single_smul_single_of_ne h 1

theorem norm_smul_single (i : ι) (c : ℝ) : ‖c • single i (1 : ℝ)‖ = |c| := by
  rw [norm_smul, PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs]

/-- A vector orthogonal to every coordinate direction other than the `i`-th is a multiple of the
`i`-th coordinate direction. -/
theorem eq_inner_single_smul_of_forall_ne {i : ι} {v : EuclideanSpace ℝ ι}
    (hv : ∀ j, j ≠ i → ⟪single j (1 : ℝ), v⟫ = 0) :
    v = ⟪single i (1 : ℝ), v⟫ • single i (1 : ℝ) := by
  ext j
  by_cases hj : j = i
  · subst hj; simp [inner_single_left]
  · have := hv j hj
    simp only [inner_single_left, map_one, one_mul] at this
    simp [hj, this]

/-- The norm of a vector orthogonal to every coordinate direction other than the `i`-th is the
absolute value of its `i`-th coordinate. -/
theorem norm_eq_abs_inner_single_of_forall_ne {i : ι} {v : EuclideanSpace ℝ ι}
    (hv : ∀ j, j ≠ i → ⟪single j (1 : ℝ), v⟫ = 0) : ‖v‖ = |⟪single i (1 : ℝ), v⟫| := by
  conv_lhs => rw [eq_inner_single_smul_of_forall_ne hv]
  exact norm_smul_single i _

/-- Every vector of `ℝ¹` is a multiple of the coordinate direction `single 0 1`. -/
theorem eq_inner_single_smul (v : EuclideanSpace ℝ (Fin 1)) :
    v = ⟪single 0 (1 : ℝ), v⟫ • single 0 (1 : ℝ) :=
  eq_inner_single_smul_of_forall_ne fun j hj => absurd (Subsingleton.elim j 0) hj

/-- The norm of `ℝ¹` is the absolute value of the coordinate along `single 0 1`. -/
theorem norm_eq_abs_inner_single (v : EuclideanSpace ℝ (Fin 1)) :
    ‖v‖ = |⟪single 0 (1 : ℝ), v⟫| :=
  norm_eq_abs_inner_single_of_forall_ne fun j hj => absurd (Subsingleton.elim j 0) hj

theorem inner_single_sq (v : EuclideanSpace ℝ (Fin 1)) :
    ⟪single 0 (1 : ℝ), v⟫ ^ 2 = ‖v‖ ^ 2 := by
  rw [norm_eq_abs_inner_single, sq_abs]

end EuclideanSpace
