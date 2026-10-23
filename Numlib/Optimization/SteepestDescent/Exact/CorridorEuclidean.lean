import Numlib.Optimization.SteepestDescent.Exact.CorridorDerivatives
import Numlib.Analysis.Calculus.Gradient.Bounds
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The actual Euclidean corridor objective and its uniform derivatives

The coordinate map from the Euclidean plane into the Cartesian plane is a linear
contraction. Actual tensor norms therefore transfer without an extra constant.
This gives all six source partial derivative bounds and the global Lipschitz
bound for the genuine Euclidean gradient.
-/

open Set
noncomputable section
namespace ExactSteepestDescent.Corridor

/-- The actual coordinate map from the Euclidean plane to its Cartesian coordinates. -/
def euclideanCoordinates : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ × ℝ :=
  (EuclideanSpace.proj (𝕜 := ℝ) 0).prod (EuclideanSpace.proj (𝕜 := ℝ) 1)

/-- Cartesian maximum norm is bounded by the Euclidean norm of the same coordinates. -/
theorem norm_euclideanCoordinates_le : ‖euclideanCoordinates‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  change ‖(z 0,z 1)‖ ≤ 1*‖z‖
  simp only [Prod.norm_def,one_mul,max_le_iff]
  exact ⟨PiLp.norm_apply_le z 0,PiLp.norm_apply_le z 1⟩

/-- The genuine corridor term on the Euclidean plane. -/
def euclideanResidual (P : Parameters) : EuclideanSpace ℝ (Fin 2) → ℝ :=
  residualCorridor P ∘ euclideanCoordinates

/-- The actual source objective on the Euclidean plane. -/
def euclideanObjective (P : Parameters) : EuclideanSpace ℝ (Fin 2) → ℝ :=
  objective P ∘ euclideanCoordinates

/-- Actual Euclidean corridor regularity follows from the true coordinate map. -/
theorem contDiff_euclideanResidual (P : Parameters) : ContDiff ℝ 2 (euclideanResidual P) :=
  (contDiff_residualCorridor P).comp euclideanCoordinates.contDiff

/-- Actual Euclidean objective regularity follows from the true coordinate map. -/
theorem contDiff_euclideanObjective (P : Parameters) : ContDiff ℝ 2 (euclideanObjective P) :=
  (contDiff_objective P).comp euclideanCoordinates.contDiff

/-- All genuine Euclidean corridor derivative tensors through order two are uniformly bounded. -/
theorem euclideanResidual_derivatives_bounded : ∃ B > 0, ∀ (P : Parameters),
    ∀ j ≤ 2, ∀ z : EuclideanSpace ℝ (Fin 2),
      ‖iteratedFDeriv ℝ j (euclideanResidual P) z‖ ≤ B := by
  obtain ⟨B,hB,H⟩ := residualCorridor_derivatives_bounded
  refine ⟨B,hB,?_⟩
  intro P j hj z
  exact (norm_iteratedFDeriv_comp_linearMap_le (contDiff_residualCorridor P)
    euclideanCoordinates norm_euclideanCoordinates_le (by exact_mod_cast hj) z).trans
      (H P j hj (euclideanCoordinates z))

/-- The value, both actual first partial derivatives and all four second partial
entries have a common global bound. This includes all six quantities in the
source connector-strip assertion. -/
theorem euclideanResidual_partials_bounded : ∃ B > 0, ∀ (P : Parameters),
    ∀ z : EuclideanSpace ℝ (Fin 2),
      |euclideanResidual P z| ≤ B ∧
      (∀ i : Fin 2, |fderiv ℝ (euclideanResidual P) z
        (EuclideanSpace.basisFun (Fin 2) ℝ i)| ≤ B) ∧
      ∀ i j : Fin 2, |iteratedFDeriv ℝ 2 (euclideanResidual P) z
        ![EuclideanSpace.basisFun (Fin 2) ℝ i,EuclideanSpace.basisFun (Fin 2) ℝ j]| ≤ B := by
  obtain ⟨B,hB,H⟩ := euclideanResidual_derivatives_bounded
  refine ⟨B,hB,?_⟩
  intro P z
  refine ⟨?_,?_,?_⟩
  · simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] using H P 0 (by omega) z
  · intro i
    have hb : ‖fderiv ℝ (euclideanResidual P) z‖ ≤ B := by
      simpa only [norm_iteratedFDeriv_one] using H P 1 (by omega) z
    have he := (fderiv ℝ (euclideanResidual P) z).le_opNorm
      (EuclideanSpace.basisFun (Fin 2) ℝ i)
    simpa only [Real.norm_eq_abs,OrthonormalBasis.norm_eq_one,mul_one] using
      he.trans (mul_le_mul_of_nonneg_right hb (norm_nonneg _))
  · intro i j
    have he := (iteratedFDeriv ℝ 2 (euclideanResidual P) z).le_opNorm
      ![EuclideanSpace.basisFun (Fin 2) ℝ i,EuclideanSpace.basisFun (Fin 2) ℝ j]
    simpa only [Real.norm_eq_abs,Fin.prod_univ_two,Matrix.cons_val_zero,
      Matrix.cons_val_one,OrthonormalBasis.norm_eq_one,mul_one] using
      he.trans (mul_le_mul_of_nonneg_right (H P 2 le_rfl z) (by positivity))

/-- The actual Euclidean objective has a uniform Hessian tensor bound. -/
theorem euclideanObjective_second_bounded : ∃ B > 0, ∀ (P : Parameters),
    ∀ z : EuclideanSpace ℝ (Fin 2),
      ‖iteratedFDeriv ℝ 2 (euclideanObjective P) z‖ ≤ B := by
  obtain ⟨B,hB,H⟩ := objective_second_bounded
  refine ⟨B,hB,?_⟩
  intro P z
  exact (norm_iteratedFDeriv_comp_linearMap_le (contDiff_objective P)
    euclideanCoordinates norm_euclideanCoordinates_le le_rfl z).trans
      (H P (euclideanCoordinates z))

/-- The true Euclidean gradient has a common global Lipschitz constant,
chosen before all accuracies and finite construction data. -/
theorem euclideanObjective_gradient_lipschitz : ∃ L > 0, ∀ (P : Parameters),
    ∀ x y : EuclideanSpace ℝ (Fin 2),
      ‖gradient (euclideanObjective P) x - gradient (euclideanObjective P) y‖ ≤
        L * ‖x-y‖ := by
  obtain ⟨L,hL,H⟩ := euclideanObjective_second_bounded
  exact ⟨L,hL,fun P => norm_gradient_sub_le_of_iteratedFDeriv_two_le
    (contDiff_euclideanObjective P) (H P)⟩

end ExactSteepestDescent.Corridor
