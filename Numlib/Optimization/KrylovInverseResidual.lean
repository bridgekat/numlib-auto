import Numlib.Optimization.KrylovSubproblemReduction

/-!
# Lanczos residuals as actual inverse entries

The existing exact residual norm and an actual nonsingular reduced shifted solve give
the inverse-entry identity, including zero residual at the Krylov grade.
-/

noncomputable section
open scoped InnerProductSpace
namespace Optimization.KrylovSubproblem
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {A : E →ₗ[ℝ] E} {g : E}

/-- Each coordinate of the actual reduced shifted solve is the corresponding first-column
inverse entry times the negative norm of the starting vector. -/
theorem lanczos_solution_coordinate_eq_inv {m : ℕ} {lambda : ℝ}
    {y : EuclideanSpace ℝ (Fin (m + 1))}
    (hy : ∀ i, (Lanczos.tridiag A g (m + 1)).mulVec y i + lambda * y i =
      -(if i = 0 then ‖g‖ else 0))
    (hunit : IsUnit (Lanczos.tridiag A g (m + 1) + lambda • 1)) (i : Fin (m + 1)) :
    y i = -‖g‖ * (Lanczos.tridiag A g (m + 1) + lambda • 1)⁻¹ i 0 := by
  have hs : Matrix.toEuclideanLin (Lanczos.tridiag A g (m + 1) + lambda • 1) y =
      (-‖g‖) • EuclideanSpace.single 0 1 := by
    ext j
    by_cases hj : j = 0 <;>
      simpa only [hj, ite_true, ite_false, mul_one, mul_zero, neg_zero,
        Matrix.toLpLin_apply, WithLp.ofLp_toLp, Matrix.add_mulVec,
        Matrix.smul_mulVec, Matrix.one_mulVec, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul, PiLp.smul_apply, PiLp.single_apply] using hy j
  have he := congrArg (Matrix.toEuclideanLin
    (Lanczos.tridiag A g (m + 1) + lambda • 1)⁻¹) hs
  rw [Matrix.toEuclideanLin_nonsing_inv_mul_apply hunit, map_smul] at he
  have hi := congrArg (fun z : EuclideanSpace ℝ (Fin (m + 1)) => z i) he
  simpa [Matrix.toEuclideanLin_apply] using hi

/-- The full exact residual norm equals both the last-coordinate expression and the
first-column inverse expression. Both identities include the grade endpoint. -/
theorem lanczos_shifted_residual_norm_eq_inv (hA : A.IsSymmetric) (hg : g ≠ 0)
    [FiniteDimensional ℝ (Krylov.fullSubspace A g)]
    {m : ℕ} (hm : m + 1 ≤ Krylov.grade A g) {lambda : ℝ}
    (y : EuclideanSpace ℝ (Fin (m + 1)))
    (hy : ∀ i, (Lanczos.tridiag A g (m + 1)).mulVec y i + lambda * y i =
      -(if i = 0 then ‖g‖ else 0))
    (hunit : IsUnit (Lanczos.tridiag A g (m + 1) + lambda • 1)) :
    ‖g + A (lanczosStep A g y) + lambda • lanczosStep A g y‖ =
        Lanczos.beta A g m * |y (Fin.last m)| ∧
      Lanczos.beta A g m * |y (Fin.last m)| =
        Lanczos.beta A g m * ‖g‖ *
          |(Lanczos.tridiag A g (m + 1) + lambda • 1)⁻¹ (Fin.last m) 0| := by
  refine ⟨lanczos_shifted_residual_norm hA hg m hm y _ hy, ?_⟩
  rw [lanczos_solution_coordinate_eq_inv hy hunit, abs_mul, abs_neg,
    abs_of_nonneg (norm_nonneg g), mul_assoc]

end Optimization.KrylovSubproblem
