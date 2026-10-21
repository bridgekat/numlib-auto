import NumlibSurface.CartisGouldToint.Chapter10.Section03.Monotonicity
import Numlib.Optimization.KrylovStopping

/-!
# Trust-region Lanczos stopping counts

The logarithmic stopping count concerns the actual metric residual of the actual
associated reduced trust-region solutions. Any uniform shifted condition-number
bound may be used; the maximum of the actual condition numbers is one such bound.
-/

noncomputable section
open Set Optimization.KrylovSubproblem Optimization.QuadraticSubproblem
open CartisGouldToint.Chapter08.Section01 CartisGouldToint.Chapter08.Section02
open CartisGouldToint.Chapter10.Section02
namespace CartisGouldToint.Chapter10.Section03
variable {n : ℕ} {H M : Matrix (Fin n) (Fin n) ℝ}
  {g : EuclideanSpace ℝ (Fin n)}

/-- Corollary 10.3.3: the requested actual dual residual tolerance is reached within
both the logarithmic count and the Krylov grade. The nonnegative natural ceiling
handles a small logarithmic numerator, and condition number one takes one step.
The enclosures may be exact extreme eigenvalues or any valid spectral enclosures. -/
theorem corollary_10_3_3 (hH : H.IsSymm) (hM : M.PosDef) (hg : g ≠ 0)
    {delta C eps kappa : ℝ} (hdelta : 0 < delta) (hC0 : 0 ≤ C)
    (hC : ∀ z, ‖secularHessian H hM z‖ ≤ C * ‖z‖) (heps : 0 < eps)
    (hkappa : 1 ≤ kappa)
    (y : (m : ℕ) → EuclideanSpace ℝ (Fin (m + 1)))
    (lambda a b : ℕ → ℝ)
    (hKKT : ∀ m, m + 1 ≤ Krylov.grade (secularHessian H hM)
      (hM.isPreconditioner_toEuclideanLin.toEnergy (Matrix.toEuclideanLin M⁻¹ g)) →
      IsTrustRegionLanczosMultiplier H hM g delta (lambda m) (y m))
    (hB : ∀ m, m + 1 ≤ Krylov.grade (secularHessian H hM)
      (hM.isPreconditioner_toEuclideanLin.toEnergy (Matrix.toEuclideanLin M⁻¹ g)) →
      0 < a m ∧ a m ≤ b m ∧ b m / a m ≤ kappa ∧
        (Matrix.toEuclideanLin
          (Lanczos.tridiag (secularHessian H hM)
            (hM.isPreconditioner_toEuclideanLin.toEnergy (Matrix.toEuclideanLin M⁻¹ g))
            (m + 1) + lambda m • 1)).IsSymmetricBoundedBy (a m) (b m)) :
    ∃ m, m + 1 ≤ min (lanczosStoppingCount (2 * C * kappa * delta / eps) kappa)
        (Krylov.grade (secularHessian H hM)
          (hM.isPreconditioner_toEuclideanLin.toEnergy (Matrix.toEuclideanLin M⁻¹ g))) ∧
      weightedNorm M⁻¹ (trustRegionLanczosResidual g H M (lambda m)
        (lanczosPrimalStep H hM g (y m))) ≤ eps := by
  let A := secularHessian H hM
  let z := hM.isPreconditioner_toEuclideanLin.toEnergy (Matrix.toEuclideanLin M⁻¹ g)
  let grade := Krylov.grade A z
  have hz : z ≠ 0 := by
    intro he
    have he' := hM.isPreconditioner_toEuclideanLin.toEnergy.map_eq_zero_iff.mp he
    apply hg
    simpa only [map_zero, hM.isPreconditioner_toEuclideanLin.apply_inv] using
      congrArg (Matrix.toEuclideanLin M) he'
  have hgrade : 0 < grade := Krylov.grade_pos_of_ne_zero A z hz
  have hcount : 1 ≤ lanczosStoppingCount (2 * C * kappa * delta / eps) kappa := by
    unfold lanczosStoppingCount
    split <;> omega
  have hres (m : ℕ) (hm : m + 1 ≤ grade) :
      weightedNorm M⁻¹ (trustRegionLanczosResidual g H M (lambda m)
        (lanczosPrimalStep H hM g (y m))) ≤
          2 * C * kappa * delta * chebyshevRate kappa ^ m := by
    obtain ⟨ha, hab, hk, hs⟩ := hB m hm
    have h := theorem_10_3_2 hH hM hg hm ha hab hC0 hC (hKKT m hm) hs
    change _ ≤ 2 * C * (b m / a m) * delta * chebyshevRate (b m / a m) ^ m at h
    apply h.trans
    have hk1 : 1 ≤ b m / a m := (one_le_div ha).mpr hab
    gcongr
    · exact pow_nonneg (chebyshevRate_nonneg hk1) m
    · exact chebyshevRate_nonneg hk1
    · exact chebyshevRate_mono hk
  have hfinal (m : ℕ) (hm : m + 1 = grade) :
      weightedNorm M⁻¹ (trustRegionLanczosResidual g H M (lambda m)
        (lanczosPrimalStep H hM g (y m))) = 0 := by
    have ht := (hKKT m hm.le).2.2.1
    have hp := (hKKT m hm.le).2.2.2.1
    have hs := lanczos_shift_posDef_of_stationary hz hm.le (lambda m) ht hp
    rw [trustRegionLanczosResidual, ← lanczosPrimalStep_residual_norm hM (y m),
      lanczos_shifted_residual_eq_zero_of_grade (secularHessian_isSymmetric hH hM) hz
        hm (y m) (lambda m) hs.1, norm_zero]
  rcases eq_or_lt_of_le hkappa with hkappa | hkappa
  · have hg1 : grade = 1 := by
      apply le_antisymm _ hgrade
      by_contra h
      change ¬grade ≤ 1 at h
      have hm : 1 + 1 ≤ grade := by omega
      obtain ⟨ha, hab, hk, hs⟩ := hB 1 hm
      have hle := grade_le_one_of_scalar_second_shift ha hab (by simpa [← hkappa] using hk) hs
      exact h (by exact hle)
    refine ⟨0, le_min hcount hgrade, ?_⟩
    rw [hfinal 0 hg1.symm]
    exact heps.le
  · rcases hC0.eq_or_lt with hCzero | hCpos
    · refine ⟨0, le_min hcount hgrade, ?_⟩
      have h := hres 0 hgrade
      simp only [← hCzero, mul_zero, zero_mul] at h
      exact h.trans heps.le
    · obtain ⟨m, hbound, ht⟩ := GeometricStopping.exists_index_le_min
        (R := fun m => weightedNorm M⁻¹ (trustRegionLanczosResidual g H M (lambda m)
          (lanczosPrimalStep H hM g (y m))))
        (B := 2 * C * kappa * delta) hgrade
        (mul_pos (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hCpos) (by linarith)) hdelta)
        heps (chebyshevRate_pos hkappa) (chebyshevRate_lt_one kappa)
        hres (hfinal (grade - 1) (by omega))
      refine ⟨m, ?_, ht⟩
      rwa [lanczosStoppingCount_eq hkappa]

end CartisGouldToint.Chapter10.Section03
