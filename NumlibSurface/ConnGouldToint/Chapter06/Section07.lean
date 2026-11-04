/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.InnerProductSpace.SingularValues
import NumlibSurface.ConnGouldToint.Chapter06.Section01

/-! # Variable scaling -/

namespace ConnGouldToint.Chapter06

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The objective in scaled step coordinates, as defined in (6.7.2). -/
def scaledObjective (f : E → ℝ) (x : E) (S : E ≃ₗ[ℝ] E) (w : E) : ℝ :=
  f (x + S w)

/-- The scaled trust-region norm is the ambient norm of the inverse-scaled vector in (6.7.9). -/
noncomputable def scaledTrustNorm (S : E ≃ₗ[ℝ] E) : Seminorm ℝ E :=
  (normSeminorm ℝ E).comp S.symm.toLinearMap

/-- The scaled trust region (6.7.8) is the image of the ambient ball
under the scaling map. -/
theorem scaledTrustRegion_eq_image (S : E ≃ₗ[ℝ] E) (Δ : ℝ) :
    {s | scaledTrustNorm S s ≤ Δ} = S '' Metric.closedBall (0 : E) Δ := by
  ext s
  change ‖S.symm s‖ ≤ Δ ↔ _
  constructor
  · intro h
    exact ⟨S.symm s, by simpa [Metric.mem_closedBall, dist_zero_right] using h,
      S.apply_symm_apply s⟩
  · rintro ⟨w, hw, rfl⟩
    simpa only [LinearEquiv.symm_apply_apply, Metric.mem_closedBall, dist_zero_right] using hw

/-- The two squared norm formulas in (6.7.9). -/
theorem scaledTrustNorm_sq [CompleteSpace E] (S : E ≃L[ℝ] E) (s : E) :
    scaledTrustNorm S.toLinearEquiv s ^ 2 = ⟪S.symm s, S.symm s⟫ ∧
      ⟪S.symm s, S.symm s⟫ =
        ⟪s, S.symm.toContinuousLinearMap.adjoint (S.symm s)⟫ := by
  refine ⟨(real_inner_self_eq_norm_sq (S.symm s)).symm, ?_⟩
  exact (S.symm.toContinuousLinearMap.adjoint_inner_right s (S.symm s)).symm

/-- Theorem 6.7.1. Uniform singular-value bounds for the scaling maps imply
the two uniform norm comparisons of AN.1. -/
theorem theorem_6_7_1 [FiniteDimensional ℝ E] [Nontrivial E]
    (S : ℕ → E ≃ₗ[ℝ] E) {κ : ℝ} (hκ : 1 ≤ κ)
    (hmin : ∀ k, 1 / κ ≤ (S k).toLinearMap.singularValues (Module.finrank ℝ E - 1))
    (hmax : ∀ k, (S k).toLinearMap.singularValues 0 ≤ κ) :
    ∀ k v, ‖v‖ / κ ≤ scaledTrustNorm (S k) v ∧ scaledTrustNorm (S k) v ≤ κ * ‖v‖ := by
  intro k v
  have hκ' : 0 < κ := zero_lt_one.trans_le hκ
  let T := (S k).toLinearMap
  let u := (S k).symm v
  have hTu : T u = v := (S k).apply_symm_apply v
  change ‖v‖ / κ ≤ ‖u‖ ∧ ‖u‖ ≤ κ * ‖v‖
  constructor
  · apply (div_le_iff₀ hκ').mpr
    calc
      ‖v‖ = ‖T u‖ := by rw [hTu]
      _ ≤ T.singularValues 0 * ‖u‖ := T.norm_apply_le_singularValues_zero_mul u
      _ ≤ κ * ‖u‖ := mul_le_mul_of_nonneg_right (hmax k) (norm_nonneg u)
      _ = ‖u‖ * κ := mul_comm _ _
  · let n := Module.finrank ℝ E
    have hn : 0 < n := Module.finrank_pos
    obtain ⟨V, hV, hlow⟩ := (T.isGreatest_singularValues (k := n - 1) (by omega)).1
    have htop : V = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [hV]; omega)
    have h := (mul_le_mul_of_nonneg_right (hmin k) (show 0 ≤ ‖u‖ from norm_nonneg u)).trans
      (hlow u (htop ▸ Submodule.mem_top))
    rw [hTu, one_div, ← div_eq_inv_mul] at h
    exact (div_le_iff₀ hκ').mp h |>.trans_eq (mul_comm _ _)

end ConnGouldToint.Chapter06
