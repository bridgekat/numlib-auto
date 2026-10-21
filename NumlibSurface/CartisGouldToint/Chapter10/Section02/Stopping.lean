import NumlibSurface.CartisGouldToint.Chapter10.Section02.Monotonicity
import Numlib.Optimization.KrylovStopping

/-!
# Relative regularized Lanczos stopping counts

The full-space upper Rayleigh bound and actual multiplier monotonicity bound each
reduced step away from zero. Combining this lower bound with geometric residual
decay gives the source relative stopping test with the logarithmic grade cap.
-/

noncomputable section
open scoped InnerProductSpace
open Set Optimization.KrylovSubproblem Optimization.QuadraticSubproblem
open CartisGouldToint.Chapter08.Section01 CartisGouldToint.Chapter08.Section02
namespace CartisGouldToint.Chapter10.Section02
variable {n : ℕ} {H M : Matrix (Fin n) (Fin n) ℝ}
  {g : EuclideanSpace ℝ (Fin n)}

/-- The energy-space initial gradient has exactly the original dual metric norm. -/
theorem norm_energyGradient (hM : M.PosDef) :
    ‖hM.isPreconditioner_toEuclideanLin.toEnergy (Matrix.toEuclideanLin M⁻¹ g)‖ =
      weightedNorm M⁻¹ g := by
  rw [← Real.sqrt_sq (norm_nonneg _),
    hM.isPreconditioner_toEuclideanLin.norm_toEnergy_inv_sq]
  rfl

/-- Corollary 10.2.3: actual regularized Lanczos steps attain the source relative
gradient test within the logarithmic count and the grade. `L` may be the largest
generalized eigenvalue, and `kappa` may be the maximum actual shifted condition
number. The full-space minimizer is arbitrary, including a singular hard case. -/
theorem corollary_10_2_3 (hH : H.IsSymm) (hM : M.PosDef) (hg : g ≠ 0)
    {sigma r theta C L kappa : ℝ} (hsigma : 0 < sigma) (hr : 2 < r)
    (htheta : 0 < theta) (hC0 : 0 ≤ C)
    (hC : ∀ z, ‖secularHessian H hM z‖ ≤ C * ‖z‖)
    (hupper : ∀ z, ⟪secularHessian H hM z, z⟫_ℝ ≤ L * ‖z‖ ^ 2)
    (hkappa : 1 ≤ kappa)
    (y : (m : ℕ) → EuclideanSpace ℝ (Fin (m + 1))) (a b : ℕ → ℝ)
    (hmin : ∀ m, m + 1 ≤ Krylov.grade (secularHessian H hM)
      (hM.isPreconditioner_toEuclideanLin.toEnergy (Matrix.toEuclideanLin M⁻¹ g)) →
      IsMinOn (reducedLanczosModel H hM g m sigma r) univ (y m))
    (hB : ∀ m, m + 1 ≤ Krylov.grade (secularHessian H hM)
      (hM.isPreconditioner_toEuclideanLin.toEnergy (Matrix.toEuclideanLin M⁻¹ g)) →
      0 < a m ∧ a m ≤ b m ∧ b m / a m ≤ kappa ∧
        (Matrix.toEuclideanLin
          (Lanczos.tridiag (secularHessian H hM)
            (hM.isPreconditioner_toEuclideanLin.toEnergy (Matrix.toEuclideanLin M⁻¹ g))
            (m + 1) + reducedRegularizationMultiplier sigma r (y m) • 1)).IsSymmetricBoundedBy
              (a m) (b m))
    {s : EuclideanSpace ℝ (Fin n)} (hs : regularizedMinimizer g H M sigma r s) :
    let lambdaStar := sigma * weightedNorm M s ^ (r - 2)
    let A := (4 * C * kappa / theta) * (lambdaStar / sigma) ^ (1 / (r - 2)) *
      ((L + lambdaStar) / weightedNorm M⁻¹ g) ^ 2
    ∃ m, m + 1 ≤ min (lanczosStoppingCount A kappa)
        (Krylov.grade (secularHessian H hM)
          (hM.isPreconditioner_toEuclideanLin.toEnergy (Matrix.toEuclideanLin M⁻¹ g))) ∧
      weightedNorm M⁻¹ (g + Matrix.toEuclideanLin H (lanczosPrimalStep H hM g (y m)) +
        reducedRegularizationMultiplier sigma r (y m) •
          Matrix.toEuclideanLin M (lanczosPrimalStep H hM g (y m))) ≤
        (theta / 2) * weightedNorm M (lanczosPrimalStep H hM g (y m)) ^ 2 := by
  let T := secularHessian H hM
  let z := hM.isPreconditioner_toEuclideanLin.toEnergy (Matrix.toEuclideanLin M⁻¹ g)
  let grade := Krylov.grade T z
  let S := weightedNorm M s
  let nu := sigma * S ^ (r - 2)
  let U := L + nu
  let G := ‖z‖
  have hz : z ≠ 0 := by
    intro he
    have he' := hM.isPreconditioner_toEuclideanLin.toEnergy.map_eq_zero_iff.mp he
    apply hg
    simpa only [map_zero, hM.isPreconditioner_toEuclideanLin.apply_inv] using
      congrArg (Matrix.toEuclideanLin M) he'
  have hG : 0 < G := norm_pos_iff.mpr hz
  have hgrade : 0 < grade := Krylov.grade_pos_of_ne_zero T z hz
  have hS0 : 0 ≤ S := by
    change 0 ≤ weightedNorm M s
    rw [← norm_toEnergy_eq_weightedNorm hM]
    exact norm_nonneg _
  have hroot : (nu / sigma) ^ (1 / (r - 2)) = S := by
    dsimp only [nu]
    rw [mul_div_cancel_left₀ _ hsigma.ne', one_div,
      Real.rpow_rpow_inv hS0 (by linarith : r - 2 ≠ 0)]
  have hcomp (m : ℕ) (hm : m + 1 ≤ grade) :
      reducedRegularizationMultiplier sigma r (y m) ≤ nu ∧ ‖y m‖ ≤ S := by
    have h := lemma_10_2_1 hH hM hg le_rfl hm hsigma hr (hmin m hm) (hmin m hm) hs
    exact ⟨h.2.1, by simpa only [lanczosPrimalStep_weightedNorm hM hm] using h.2.2.2⟩
  have hlow (m : ℕ) (hm : m + 1 ≤ grade) : 0 < U ∧ G / U ≤ ‖y m‖ := by
    obtain ⟨ha, _, _, hspec⟩ := hB m hm
    have hstat := (reducedRegularizationMultiplier_spec hM hg hm hsigma.le hr (hmin m hm)).1
    exact lanczos_stationary_norm_lower_bound
      (H := T.toContinuousLinearMap) (secularHessian_isSymmetric hH hM) hm ha
      (hcomp m hm).1 hupper hspec hstat
  have hU : 0 < U := (hlow 0 hgrade).1
  have hS : 0 < S := (div_pos hG hU).trans_le ((hlow 0 hgrade).2.trans (hcomp 0 hgrade).2)
  let eps := theta / 2 * (G / U) ^ 2
  have heps : 0 < eps := mul_pos (div_pos htheta (by norm_num)) (pow_pos (div_pos hG hU) 2)
  let R : ℕ → ℝ := fun m => weightedNorm M⁻¹
    (g + Matrix.toEuclideanLin H (lanczosPrimalStep H hM g (y m)) +
      reducedRegularizationMultiplier sigma r (y m) •
        Matrix.toEuclideanLin M (lanczosPrimalStep H hM g (y m)))
  have hres (m : ℕ) (hm : m + 1 ≤ grade) :
      R m ≤ 2 * C * kappa * S * chebyshevRate kappa ^ m := by
    obtain ⟨ha, hab, hk, hspec⟩ := hB m hm
    have h := theorem_10_2_2 hH hM hg hm hsigma hr ha hab hC0 hC (hmin m hm) hspec
    have hrootm : (reducedRegularizationMultiplier sigma r (y m) / sigma) ^
        (1 / (r - 2)) = ‖y m‖ := by
      rw [reducedRegularizationMultiplier, mul_div_cancel_left₀ _ hsigma.ne', one_div,
        Real.rpow_rpow_inv (norm_nonneg _) (by linarith : r - 2 ≠ 0)]
    rw [hrootm] at h
    change R m ≤ 2 * C * (b m / a m) * ‖y m‖ * chebyshevRate (b m / a m) ^ m at h
    apply h.trans
    have hk1 : 1 ≤ b m / a m := (one_le_div ha).mpr hab
    gcongr
    · exact pow_nonneg (chebyshevRate_nonneg hk1) m
    · exact (hcomp m hm).2
    · exact chebyshevRate_nonneg hk1
    · exact chebyshevRate_mono hk
  have hfinal (m : ℕ) (hm : m + 1 = grade) : R m = 0 := by
    have hstat := (reducedRegularizationMultiplier_spec hM hg hm.le hsigma.le hr
      (hmin m hm.le)).1
    dsimp only [R]
    rw [← lanczosPrimalStep_residual_norm hM (y m),
      lanczos_shifted_residual_eq_zero_of_grade (secularHessian_isSymmetric hH hM) hz
        hm (y m) _ hstat, norm_zero]
  have hAeq : 2 * C * kappa * S / eps =
      (4 * C * kappa / theta) * (nu / sigma) ^ (1 / (r - 2)) *
        ((L + nu) / weightedNorm M⁻¹ g) ^ 2 := by
    rw [hroot, ← norm_energyGradient hM]
    change 2 * C * kappa * S / (theta / 2 * (G / U) ^ 2) =
      4 * C * kappa / theta * S * (U / G) ^ 2
    field_simp
    ring
  have hcount : 1 ≤ lanczosStoppingCount (2 * C * kappa * S / eps) kappa := by
    unfold lanczosStoppingCount
    split <;> omega
  have hex : ∃ m, m + 1 ≤ min (lanczosStoppingCount (2 * C * kappa * S / eps) kappa) grade ∧
      R m ≤ eps := by
    rcases eq_or_lt_of_le hkappa with hkappa | hkappa
    · have hg1 : grade = 1 := by
        apply le_antisymm _ hgrade
        by_contra h
        change ¬grade ≤ 1 at h
        have hm : 1 + 1 ≤ grade := by omega
        obtain ⟨ha, hab, hk, hspec⟩ := hB 1 hm
        exact h (grade_le_one_of_scalar_second_shift ha hab (by simpa [← hkappa] using hk) hspec)
      refine ⟨0, le_min hcount hgrade, ?_⟩
      rw [hfinal 0 hg1.symm]
      exact heps.le
    · rcases hC0.eq_or_lt with hCzero | hCpos
      · refine ⟨0, le_min hcount hgrade, ?_⟩
        have h := hres 0 hgrade
        simp only [← hCzero, mul_zero, zero_mul] at h
        exact h.trans heps.le
      · rw [lanczosStoppingCount_eq hkappa]
        exact GeometricStopping.exists_index_le_min hgrade
          (mul_pos (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hCpos) (by linarith)) hS)
          heps (chebyshevRate_pos hkappa) (chebyshevRate_lt_one kappa)
          hres (hfinal (grade - 1) (by omega))
  obtain ⟨m, hm, ht⟩ := hex
  refine ⟨m, ?_, ?_⟩
  · change m + 1 ≤ min (lanczosStoppingCount _ kappa) grade
    rwa [← hAeq]
  · have hmgrade : m + 1 ≤ grade := (le_min_iff.mp hm).2
    rw [lanczosPrimalStep_weightedNorm hM hmgrade]
    exact ht.trans (mul_le_mul_of_nonneg_left
      ((sq_le_sq₀ (div_nonneg hG.le hU.le) (norm_nonneg _)).mpr (hlow m hmgrade).2)
      (div_nonneg htheta.le (by norm_num)))

end CartisGouldToint.Chapter10.Section02
