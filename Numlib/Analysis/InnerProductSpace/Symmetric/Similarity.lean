/-
Upstreaming candidate: general material with no numerical-analysis-specific content.
Natural home: `Mathlib.Analysis.InnerProductSpace`.
-/
import Numlib.Analysis.InnerProductSpace.Coercive
import Mathlib.Tactic

/-!
# Norm bounds under a similarity to a symmetric operator

Actual eigenvectors transported by a linear equivalence bound the spectrum
by the ordinary operator norm in the original normed space.
-/

namespace ContinuousLinearMap
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- A finite-dimensional symmetric operator has norm at most that of any similar bounded
operator. -/
theorem norm_le_norm_of_similar {A : F →L[ℝ] F} (hA : A.toLinearMap.IsSymmetric)
    (B : E →L[ℝ] E) (J : F ≃ₗ[ℝ] E) (hJ : ∀ x, J (A x) = B (J x)) : ‖A‖ ≤
      ‖B‖ := by
  apply norm_le_of_isSymmetricBoundedBy (norm_nonneg B)
  apply (hA.isSymmetricBoundedBy_iff_forall_hasEigenvalue (-‖B‖) ‖B‖).mpr
  intro μ hμ
  obtain ⟨v, hv, hv0⟩ := hμ.exists_hasEigenvector
  rw [Module.End.mem_eigenspace_iff] at hv
  change A v = μ • v at hv
  have hBv : B (J v) = μ • J v := by rw [←hJ, hv, map_smul]
  have hn : 0 < ‖J v‖ := norm_pos_iff.mpr (by intro he; apply hv0; exact J.injective (by
    simpa using he))
  have hh := B.le_opNorm (J v)
  rw [hBv, norm_smul, Real.norm_eq_abs] at hh
  have hbound : |μ| ≤ ‖B‖ := (mul_le_mul_iff_left₀ hn).mp hh
  simpa only [RCLike.re_to_real, Set.mem_Icc] using abs_le.mp hbound
end ContinuousLinearMap
