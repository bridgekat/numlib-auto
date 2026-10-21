import NumlibSurface.CartisGouldToint.Chapter10.Section02
import Numlib.Optimization.KrylovSubproblemMonotonicity

/-!
# Metric regularized Lanczos monotonicity

Actual reduced global minimizers have nondecreasing radial multipliers and metric norms.
Every full-space global minimizer bounds them, including singular hard cases outside the
full Krylov subspace. Energy transport preserves the arbitrary positive definite metric.
-/

noncomputable section
open Set Optimization.KrylovSubproblem Optimization.QuadraticSubproblem
open CartisGouldToint.Chapter08.Section01 CartisGouldToint.Chapter08.Section02
namespace CartisGouldToint.Chapter10.Section02
variable {n : ℕ} {H M : Matrix (Fin n) (Fin n) ℝ}
  {g : EuclideanSpace ℝ (Fin n)}

/-- The actual energy transport norm is exactly the source metric norm. -/
theorem norm_toEnergy_eq_weightedNorm (hM : M.PosDef) (s : EuclideanSpace ℝ (Fin n)) :
    ‖hM.isPreconditioner_toEuclideanLin.toEnergy s‖ = weightedNorm M s := by
  rw [WithEnergy.norm_equiv, weightedNorm_eq_energyNorm]

/-- The actual represented Lanczos primal step has the metric norm of its reduced coordinates. -/
theorem lanczosPrimalStep_weightedNorm (hM : M.PosDef) {m : ℕ}
    (hm : m + 1 ≤ Krylov.grade (secularHessian H hM)
      (hM.isPreconditioner_toEuclideanLin.toEnergy (Matrix.toEuclideanLin M⁻¹ g)))
    (y : EuclideanSpace ℝ (Fin (m + 1))) :
    weightedNorm M (lanczosPrimalStep H hM g y) = ‖y‖ := by
  rw [← norm_toEnergy_eq_weightedNorm hM]
  change ‖hM.isPreconditioner_toEuclideanLin.toEnergy
    (hM.isPreconditioner_toEuclideanLin.toEnergy.symm
      (lanczosStep (secularHessian H hM)
        (hM.isPreconditioner_toEuclideanLin.toEnergy (Matrix.toEuclideanLin M⁻¹ g)) y))‖ = _
  rw [hM.isPreconditioner_toEuclideanLin.toEnergy.apply_symm_apply,
    ← lanczosEmbedding_apply _ _ hm]
  exact (lanczosEmbedding _ _ hm).norm_map y

/-- Lemma 10.2.1: actual nested Lanczos global minimizers have increasing multipliers and
metric norms, bounded by those of every full-space weighted global minimizer. -/
theorem lemma_10_2_1 (hH : H.IsSymm) (hM : M.PosDef) (hg : g ≠ 0)
    {k l : ℕ} (hkl : k + 1 ≤ l + 1)
    (hl : l + 1 ≤ Krylov.grade (secularHessian H hM)
      (hM.isPreconditioner_toEuclideanLin.toEnergy (Matrix.toEuclideanLin M⁻¹ g)))
    {sigma r : ℝ} (hsigma : 0 < sigma) (hr : 2 < r)
    {x : EuclideanSpace ℝ (Fin (k + 1))} {y : EuclideanSpace ℝ (Fin (l + 1))}
    {s : EuclideanSpace ℝ (Fin n)}
    (hx : IsMinOn (reducedLanczosModel H hM g k sigma r) univ x)
    (hy : IsMinOn (reducedLanczosModel H hM g l sigma r) univ y)
    (hs : regularizedMinimizer g H M sigma r s) :
    reducedRegularizationMultiplier sigma r x ≤ reducedRegularizationMultiplier sigma r y ∧
      reducedRegularizationMultiplier sigma r y ≤ sigma * weightedNorm M s ^ (r - 2) ∧
      weightedNorm M (lanczosPrimalStep H hM g x) ≤
        weightedNorm M (lanczosPrimalStep H hM g y) ∧
      weightedNorm M (lanczosPrimalStep H hM g y) ≤ weightedNorm M s := by
  let hp := hM.isPreconditioner_toEuclideanLin
  have hb : hp.toEnergy (Matrix.toEuclideanLin M⁻¹ g) ≠ 0 := by
    intro hzero
    have hz := hp.toEnergy.map_eq_zero_iff.mp hzero
    apply hg
    simpa only [map_zero, hp.apply_inv] using congrArg (Matrix.toEuclideanLin M) hz
  have hs' : IsMinOn (weightedPowerQuadratic g
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) H) (Matrix.toEuclideanLin M)
      sigma r) univ s := by
    simpa only [regularizedMinimizer, regularizedModel_eq_weightedPowerQuadratic] using hs
  have hse := (isMinOn_energy_power_iff hp g
    (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) H) sigma r s).mpr hs'
  have h := lanczos_regularized_norm_mono (secularHessian_isSymmetric hH hM) hb
    hkl hl hsigma.le hr hx hy hse
  have hn : ‖hp.toEnergy s‖ = weightedNorm M s := norm_toEnergy_eq_weightedNorm hM s
  rw [hn] at h
  simpa only [reducedRegularizationMultiplier,
    lanczosPrimalStep_weightedNorm hM (hkl.trans hl),
    lanczosPrimalStep_weightedNorm hM hl] using h

end CartisGouldToint.Chapter10.Section02
