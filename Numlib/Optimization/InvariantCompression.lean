import Numlib.Optimization.KrylovSubproblem

/-!
# Invariant isometric compression

A symmetric operator restricted to an invariant isometric range commutes with taking
adjoint coordinates. Positive semidefinite shifts survive compression, including
singular full-space shifts.
-/

noncomputable section
open scoped InnerProductSpace
namespace Optimization.KrylovSubproblem
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace E] [CompleteSpace F]

/-- Compression to an invariant isometric range commutes with taking adjoint coordinates. -/
theorem compressedHessian_adjoint_of_invariant (Q : F →ₗᵢ[ℝ] E) {H : E →L[ℝ] E}
    (hH : H.IsSymmetric) (hinv : ∀ v, H (Q v) ∈ Set.range Q) (z : E) :
    compressedHessian Q H (Q.toContinuousLinearMap.adjoint z) =
      Q.toContinuousLinearMap.adjoint (H z) := by
  apply ext_inner_left ℝ
  intro v
  change ⟪v, Q.toContinuousLinearMap.adjoint
      (H (Q (Q.toContinuousLinearMap.adjoint z)))⟫_ℝ =
    ⟪v, Q.toContinuousLinearMap.adjoint (H z)⟫_ℝ
  rw [ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.adjoint_inner_right]
  change ⟪Q v, H (Q (Q.toContinuousLinearMap.adjoint z))⟫_ℝ = ⟪Q v, H z⟫_ℝ
  calc
    _ = ⟪H (Q v), Q (Q.toContinuousLinearMap.adjoint z)⟫_ℝ := (hH _ _).symm
    _ = ⟪H (Q v), z⟫_ℝ := by
      obtain ⟨w, hw⟩ := hinv v
      rw [← hw, Q.inner_map_map, ContinuousLinearMap.adjoint_inner_right]
      rfl
    _ = _ := hH _ _

/-- Isometric compression preserves positive semidefinite shifts. No invertibility is needed. -/
theorem compressedHessian_shift_isPositive (Q : F →ₗᵢ[ℝ] E) {H : E →L[ℝ] E}
    {lambda : ℝ} (hpos : (H + lambda • ContinuousLinearMap.id ℝ E).IsPositive) :
    (compressedHessian Q H + lambda • ContinuousLinearMap.id ℝ F).IsPositive := by
  have h := hpos.adjoint_conj Q.toContinuousLinearMap
  convert h using 1
  ext x
  change compressedHessian Q H x + lambda • x =
    Q.toContinuousLinearMap.adjoint (H (Q x) + lambda • Q x)
  rw [map_add, map_smul]
  congr 1
  rw [show Q.toContinuousLinearMap.adjoint (Q x) = x from
    congrArg (fun T : F →L[ℝ] F => T x) Q.adjoint_comp_self]

end Optimization.KrylovSubproblem
