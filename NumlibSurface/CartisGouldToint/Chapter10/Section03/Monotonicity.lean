import NumlibSurface.CartisGouldToint.Chapter10.Section03
import NumlibSurface.CartisGouldToint.Chapter10.Section02.Monotonicity

/-!
# Metric trust-region Lanczos monotonicity

The actual associated multipliers and metric step norms increase along the Lanczos
compressions and remain bounded by every full-space associated solution. Singular
full-space hard cases are included without a uniqueness assumption.
-/

noncomputable section
open Set Optimization.KrylovSubproblem Optimization.QuadraticSubproblem
open CartisGouldToint.Chapter08.Section01 CartisGouldToint.Chapter08.Section02
open CartisGouldToint.Chapter10.Section02
namespace CartisGouldToint.Chapter10.Section03
variable {n : ℕ} {H M : Matrix (Fin n) (Fin n) ℝ}
  {g : EuclideanSpace ℝ (Fin n)}

/-- The actual full-space metric associated multiplier conditions from Theorem 8.2.7. -/
def IsTrustRegionFullMultiplier (g : EuclideanSpace ℝ (Fin n))
    (H M : Matrix (Fin n) (Fin n) ℝ) (delta lambda : ℝ)
    (s : EuclideanSpace ℝ (Fin n)) : Prop :=
  weightedNorm M s ≤ delta ∧ 0 ≤ lambda ∧
    Matrix.toEuclideanLin (H + lambda • M) s = -g ∧ (H + lambda • M).PosSemidef ∧
      lambda * (weightedNorm M s ^ 2 - delta ^ 2) = 0

/-- Every actual metric associated solution gives the exact energy-space shift conditions. -/
theorem IsTrustRegionFullMultiplier.energyConditions (hH : H.IsSymm) (hM : M.PosDef)
    {delta lambda : ℝ} {s : EuclideanSpace ℝ (Fin n)}
    (hs : IsTrustRegionFullMultiplier g H M delta lambda s) :
    let hp := hM.isPreconditioner_toEuclideanLin
    TrustRegionShiftConditions (hp.toEnergy (Matrix.toEuclideanLin M⁻¹ g))
      (energyHessian hp (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) H))
      delta lambda (hp.toEnergy s) := by
  let hp := hM.isPreconditioner_toEuclideanLin
  have hn : ‖hp.toEnergy s‖ = weightedNorm M s := norm_toEnergy_eq_weightedNorm hM s
  refine ⟨hn.le.trans hs.1, hs.2.1, ?_, ?_, ?_⟩
  · apply (energy_stationary_iff hp g
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) H) s lambda).mpr
    exact (metric_shift_stationary_iff lambda).mpr hs.2.2.1
  · apply (isPositive_energy_shift_iff hp hH.isSymmetric_toEuclideanLin lambda).mpr
    simpa only [← toEuclideanLin_metric_shift, Matrix.isPositive_toEuclideanLin_iff]
      using hs.2.2.2.1
  · change lambda * (‖hp.toEnergy s‖ ^ 2 - delta ^ 2) = 0
    rw [hn]
    exact hs.2.2.2.2

/-- The source full-space global minimizer definition is equivalent to the existence of an
associated metric multiplier. This includes singular shifted Hessians. -/
theorem isMinOn_full_trustRegion_iff (hH : H.IsSymm) (hM : M.PosDef)
    {delta : ℝ} (hdelta : 0 < delta) {s : EuclideanSpace ℝ (Fin n)} :
    trustRegionMinimizer g H M delta s ↔
      ∃ lambda, IsTrustRegionFullMultiplier g H M delta lambda s := by
  simpa only [IsTrustRegionFullMultiplier, exists_and_left] using
    (theorem_8_2_7 hH hM hdelta (g := g) (s := s)).1

/-- Lemma 10.3.1: actual nested metric trust-region steps have increasing norms and
associated multipliers, bounded by every full-space associated solution. -/
theorem lemma_10_3_1 (hH : H.IsSymm) (hM : M.PosDef) (hg : g ≠ 0)
    {k l : ℕ} (hkl : k + 1 ≤ l + 1)
    (hl : l + 1 ≤ Krylov.grade (secularHessian H hM)
      (hM.isPreconditioner_toEuclideanLin.toEnergy (Matrix.toEuclideanLin M⁻¹ g)))
    {delta lambda mu nu : ℝ}
    {x : EuclideanSpace ℝ (Fin (k + 1))} {y : EuclideanSpace ℝ (Fin (l + 1))}
    {s : EuclideanSpace ℝ (Fin n)}
    (hx : IsTrustRegionLanczosMultiplier H hM g delta lambda x)
    (hy : IsTrustRegionLanczosMultiplier H hM g delta mu y)
    (hs : IsTrustRegionFullMultiplier g H M delta nu s) :
    lambda ≤ mu ∧ mu ≤ nu ∧
      weightedNorm M (lanczosPrimalStep H hM g x) ≤
        weightedNorm M (lanczosPrimalStep H hM g y) ∧
      weightedNorm M (lanczosPrimalStep H hM g y) ≤ weightedNorm M s := by
  let hp := hM.isPreconditioner_toEuclideanLin
  have hb : hp.toEnergy (Matrix.toEuclideanLin M⁻¹ g) ≠ 0 := by
    intro hzero
    have hz := hp.toEnergy.map_eq_zero_iff.mp hzero
    apply hg
    simpa only [map_zero, hp.apply_inv] using congrArg (Matrix.toEuclideanLin M) hz
  have h := lanczos_trustRegion_norm_mono (secularHessian_isSymmetric hH hM) hb hkl hl
    (TrustRegionShiftConditions.iff.mpr hx) (TrustRegionShiftConditions.iff.mpr hy)
    (hs.energyConditions hH hM)
  have hn : ‖hp.toEnergy s‖ = weightedNorm M s := norm_toEnergy_eq_weightedNorm hM s
  rw [hn] at h
  simpa only [lanczosPrimalStep_weightedNorm hM (hkl.trans hl),
    lanczosPrimalStep_weightedNorm hM hl] using h

end CartisGouldToint.Chapter10.Section03
