import Numlib.Optimization.KrylovSubproblem

/-!
# Actual Lanczos coordinates of reduced subproblems

The isometric Arnoldi basis compresses the symmetric operator to the existing Lanczos
tridiagonal matrix and the starting gradient to its first coordinate. These identities
identify the represented quadratic subproblems with their actual tridiagonal reductions.
-/

noncomputable section
open scoped InnerProductSpace
namespace Optimization.KrylovSubproblem
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {A : E →ₗ[ℝ] E} {g : E} [FiniteDimensional ℝ (Krylov.fullSubspace A g)]

/-- A coordinate unit vector maps to its actual Arnoldi/Lanczos basis vector. -/
theorem lanczosEmbedding_single {m : ℕ} (hm : m ≤ Krylov.grade A g) (i : Fin m) :
    lanczosEmbedding A g hm (EuclideanSpace.single i 1) = Arnoldi.vec A g i := by
  rw [lanczosEmbedding_apply, lanczosStep]
  simp

variable [CompleteSpace E]

/-- The adjoint coordinates of any vector are its actual inner products with the Lanczos
basis vectors. -/
theorem adjoint_lanczosEmbedding_apply {m : ℕ} (hm : m ≤ Krylov.grade A g) (z : E)
    (i : Fin m) :
    (lanczosEmbedding A g hm).toContinuousLinearMap.adjoint z i =
      ⟪Arnoldi.vec A g i, z⟫_ℝ := by
  calc
    _ = ⟪EuclideanSpace.single i 1,
        (lanczosEmbedding A g hm).toContinuousLinearMap.adjoint z⟫_ℝ := by
      simp only [EuclideanSpace.inner_single_left, map_one, one_mul]
    _ = ⟪lanczosEmbedding A g hm (EuclideanSpace.single i 1), z⟫_ℝ :=
      ContinuousLinearMap.adjoint_inner_right _ _ _
    _ = _ := by rw [lanczosEmbedding_single]

omit [CompleteSpace E] [FiniteDimensional ℝ (Krylov.fullSubspace A g)] in
/-- The actual Lanczos tensor coefficients are the entries of its tridiagonal matrix. -/
theorem inner_vec_apply_eq_tridiag (hA : A.IsSymmetric) {m : ℕ} (i j : Fin m) :
    ⟪Arnoldi.vec A g i, A (Arnoldi.vec A g j)⟫_ℝ = Lanczos.tridiag A g m i j := by
  have h := congrArg (fun T : Matrix (Fin m) (Fin m) ℝ => T i j)
    (Lanczos.hessenbergSq_eq_map_tridiag g hA m)
  simpa only [Arnoldi.hessenbergSq, Matrix.of_apply, Matrix.map_apply, Arnoldi.coeff,
    RCLike.algebraMap_eq_ofReal, RCLike.ofReal_real_eq_id, id_eq] using h

/-- The actual compressed Hessian acts by the existing Lanczos tridiagonal matrix. -/
theorem compressedHessian_lanczosEmbedding_apply {H : E →L[ℝ] E}
    (hA : A.IsSymmetric) (hHA : H.toLinearMap = A) {m : ℕ}
    (hm : m ≤ Krylov.grade A g) (y : EuclideanSpace ℝ (Fin m)) (i : Fin m) :
    compressedHessian (lanczosEmbedding A g hm) H y i =
      (Lanczos.tridiag A g m).mulVec y i := by
  change (lanczosEmbedding A g hm).toContinuousLinearMap.adjoint
    (H (lanczosEmbedding A g hm y)) i = _
  rw [adjoint_lanczosEmbedding_apply, lanczosEmbedding_apply]
  have he : H (lanczosStep A g y) = A (lanczosStep A g y) :=
    congrArg (fun B : E →ₗ[ℝ] E => B (lanczosStep A g y)) hHA
  rw [he, lanczosStep, map_sum, inner_sum]
  simp only [map_smul, real_inner_smul_right]
  simp_rw [inner_vec_apply_eq_tridiag hA]
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The compressed initial gradient has exactly its first-coordinate representation. -/
theorem adjoint_lanczosEmbedding_start {m : ℕ} (hm : m + 1 ≤ Krylov.grade A g)
    (i : Fin (m + 1)) :
    (lanczosEmbedding A g hm).toContinuousLinearMap.adjoint g i =
      if i = 0 then ‖g‖ else 0 := by
  have hg : g ≠ 0 := by
    intro hg
    simp only [hg, Krylov.grade_zero] at hm
    omega
  have he : g = ‖g‖ • Arnoldi.vec A g 0 := by
    rw [Arnoldi.vec_zero A g hg, smul_smul]
    change g = (‖g‖ * ‖g‖⁻¹) • g
    rw [mul_inv_cancel₀ (norm_ne_zero_iff.mpr hg), one_smul]
  rw [adjoint_lanczosEmbedding_apply]
  have hscalar := congrArg (fun z : E => ⟪Arnoldi.vec A g i, z⟫_ℝ) he
  rw [real_inner_smul_right] at hscalar
  rw [hscalar]
  by_cases hi : i = 0
  · subst i
    simp only [Fin.val_zero, inner_self_eq_norm_sq_to_K, RCLike.ofReal_real_eq_id, id_eq,
      Arnoldi.norm_vec_eq_one_of_lt_grade A g (by omega : 0 < Krylov.grade A g),
      one_pow, mul_one, ite_true]
  · have hn : (i : ℕ) ≠ 0 := by intro h; apply hi; exact Fin.ext h
    rw [Arnoldi.inner_vec_eq_zero A g hn, mul_zero, ite_eq_right hi]

omit [CompleteSpace E] [FiniteDimensional ℝ (Krylov.fullSubspace A g)] in
/-- The full Lanczos relation, using the actual unnormalized next residual, is valid even
at breakdown. -/
theorem lanczos_apply_sub (hA : A.IsSymmetric) (m : ℕ) (y : Fin (m + 1) → ℝ) :
    A (lanczosStep A g y) - lanczosStep A g ((Lanczos.tridiag A g (m + 1)).mulVec y) =
      y (Fin.last m) • Arnoldi.w A g m := by
  have he : y (Fin.last m) • Arnoldi.w A g m =
      (Lanczos.beta A g m * y (Fin.last m)) • Arnoldi.vec A g (m + 1) := by
    rw [Arnoldi.w_eq_norm_smul_vec, smul_smul]
    change (y (Fin.last m) * ‖Arnoldi.w A g m‖) • _ =
      (‖Arnoldi.w A g m‖ * y (Fin.last m)) • _
    rw [mul_comm]
  have hh := Lanczos.apply_sum g hA m y
  simp only [RCLike.algebraMap_eq_ofReal, RCLike.ofReal_real_eq_id, Matrix.map_id, id_eq] at hh
  change A (lanczosStep A g y) =
    lanczosStep A g ((Lanczos.tridiag A g (m + 1)).mulVec y) + _ at hh
  rw [← he] at hh
  rw [hh]
  abel

end Optimization.KrylovSubproblem
