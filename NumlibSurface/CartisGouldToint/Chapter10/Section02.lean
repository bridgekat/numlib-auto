import NumlibSurface.CartisGouldToint.Chapter10.Section01
import Numlib.Optimization.Quadratic.Krylov.RegularizationMonotonicity
import Numlib.Optimization.Quadratic.Optimality.RegularizationMetric

/-!
# Actual Lanczos regularization gradient decay

The computed global subproblem minimizer yields its actual shifted solve and
positive-definite projected matrix. Inverse decay then gives the exact source
bound in the inverse-metric norm. The norm-similarity equality in (B.10.4) is
replaced by the sufficient proved inequality; no extra spectral assumption is
added. Grade termination and condition number one are included.
-/

open Krylov QuadraticOptimality.Metric QuadraticRegularization.Metric
open scoped Matrix ComplexOrder
namespace CartisGouldToint
variable {n : ℕ}
variable (H M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
  (hM : M.toLinearMap.IsSymmetricCoercive)

/-- **Theorem 10.2.2.** The true model gradient at the actual subspace minimizer
has bound (10.2.9). Its multiplier is `sigma*norm(y)^(r - 2)`, the actual metric
radius is `norm(y)`, and its condition number uses the actual extreme projected
eigenvalues. The formula remains valid at condition number one. -/
theorem theorem_10_2_2 (hH : H.toLinearMap.IsSymmetric)
    {g : EuclideanSpace ℝ (Fin n)} (hg : g ≠ 0) {m : ℕ}
    (hm : m + 1 ≤ grade (hessian M hM H).toLinearMap (gradient M hM g))
    (y : EuclideanSpace ℝ (Fin (m + 1))) {σ r : ℝ} (hσ : 0 < σ) (hr : 2 < r)
    (hmin : ∀ z, lanczosRegularizationModel H M hM g m σ r y ≤
      lanczosRegularizationModel H M hM g m σ r z) :
    let A := hessian M hM H
    let b := gradient M hM g
    let τ := σ * ‖y‖ ^ (r - 2)
    let hT := Lanczos.shifted_tridiag_isHermitian A.toLinearMap b (m + 1) τ
    let κ := hT.greatestEigenvalue / hT.leastEigenvalue
    let s := toOriginal M hM (lanczosSubspaceData H M hM g hm y)
    energyNorm M.inverse.toLinearMap (H s + τ • M s + g) ≤
      2 * ‖M.inverse.comp H‖ * κ * (τ / σ) ^ (1 / (r - 2)) *
        ((Real.sqrt κ - 1) / (Real.sqrt κ + 1)) ^ m := by
  let A := hessian M hM H
  let b := gradient M hM g
  have hb : b ≠ 0 := gradient_ne_zero M hM hg
  have hsym : A.toLinearMap.IsSymmetric := hessian_symmetric M hM hH
  have hsolve := QuadraticKrylov.projected_optimality A.toLinearMap hb hm y hr hmin
  have hbound := QuadraticKrylov.regularized_gradient_bound A hb hsym hm y hσ hr hmin
  dsimp only at hbound
  rw [QuadraticKrylov.norm_fderiv_regularized A b hsym hr σ] at hbound
  have hn := (Lanczos.basisEmbedding A.toLinearMap b hm).norm_map y
  rw [hn] at hbound
  have he := norm_residual M hM H g (σ * ‖y‖ ^ (r - 2))
    (lanczosSubspaceData H M hM g hm y)
  change ‖A (Lanczos.basisEmbedding A.toLinearMap b hm y) +
    (σ * ‖y‖ ^ (r - 2)) • Lanczos.basisEmbedding A.toLinearMap b hm y + b‖ = _ at he
  rw [he] at hbound
  apply hbound.trans
  have hlo := hsolve.2.isHermitian.leastEigenvalue_pos hsolve.2
  have hle := hsolve.2.isHermitian.leastEigenvalue_le_greatest
  have hk : 1 ≤ hsolve.2.isHermitian.greatestEigenvalue /
      hsolve.2.isHermitian.leastEigenvalue := (one_le_div hlo).mpr hle
  have hq : 0 ≤ (Real.sqrt (hsolve.2.isHermitian.greatestEigenvalue /
      hsolve.2.isHermitian.leastEigenvalue) - 1) /
      (Real.sqrt (hsolve.2.isHermitian.greatestEigenvalue /
      hsolve.2.isHermitian.leastEigenvalue) + 1) := by
    apply div_nonneg _ (by positivity)
    have hh : 1 ≤ Real.sqrt (hsolve.2.isHermitian.greatestEigenvalue /
      hsolve.2.isHermitian.leastEigenvalue) := by
      rw [Real.le_sqrt (by norm_num) (zero_le_one.trans hk)]
      simpa using hk
    linarith
  have hnorm := norm_hessian_le M hM hH
  gcongr
/-- **Lemma 10.2.1.** Genuine global regularization minimizers in nested Lanczos
spaces have ordered radial multipliers and metric norms, each bounded by a true
full-space minimizer. The full model is represented in the actual energy inner
product; `Metric.regularized_eq` identifies the original objective exactly. -/
theorem lemma_10_2_1 (hH : H.toLinearMap.IsSymmetric)
    {g : EuclideanSpace ℝ (Fin n)} (hg : g ≠ 0) {m l : ℕ} (hml : m ≤ l)
    (hl : l + 1 ≤ grade (hessian M hM H).toLinearMap (gradient M hM g))
    (y : EuclideanSpace ℝ (Fin (m + 1))) (z : EuclideanSpace ℝ (Fin (l + 1)))
    (x : WithEnergy M.toLinearMap hM) {σ r : ℝ} (hσ : 0 < σ) (hr : 2 < r)
    (hminy : ∀ w, lanczosRegularizationModel H M hM g m σ r y ≤
      lanczosRegularizationModel H M hM g m σ r w)
    (hminz : ∀ w, lanczosRegularizationModel H M hM g l σ r z ≤
      lanczosRegularizationModel H M hM g l σ r w)
    (hminx : ∀ w, QuadraticOptimality.regularized (hessian M hM H) (gradient M hM g) σ r x ≤
      QuadraticOptimality.regularized (hessian M hM H) (gradient M hM g) σ r w) :
    let hm := (Nat.add_le_add_right hml 1).trans hl
    let sy := toOriginal M hM (lanczosSubspaceData H M hM g hm y)
    let sz := toOriginal M hM (lanczosSubspaceData H M hM g hl z)
    let sx := toOriginal M hM x
    let τ := σ * energyNorm M.toLinearMap sy ^ (r - 2)
    let μ := σ * energyNorm M.toLinearMap sz ^ (r - 2)
    let ν := σ * energyNorm M.toLinearMap sx ^ (r - 2)
    τ ≤ μ ∧ μ ≤ ν ∧ energyNorm M.toLinearMap sy ≤ energyNorm M.toLinearMap sz ∧
      energyNorm M.toLinearMap sz ≤ energyNorm M.toLinearMap sx := by
  have hb := gradient_ne_zero M hM hg
  have hsym := hessian_symmetric M hM hH
  have hpair := QuadraticKrylov.norm_le_norm_of_projected_regularized_min
    (hessian M hM H).toLinearMap hb hsym hml hl y z hσ hr hminy hminz
  have hzsolve := (QuadraticKrylov.projected_optimality
    (hessian M hM H).toLinearMap hb hl z hr hminz).1
  have hstar := QuadraticKrylov.norm_le_norm_of_regularized_ambient_min
    (hessian M hM H) hb hsym hl z x hσ hr hzsolve hminx
  have hτμ := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (norm_nonneg _) hpair (by linarith : 0 ≤ r - 2)) hσ.le
  have hμν := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (norm_nonneg _) hstar (by linarith : 0 ≤ r - 2)) hσ.le
  change σ * ‖lanczosSubspaceData H M hM g ((Nat.add_le_add_right hml 1).trans hl) y‖ ^
      (r - 2) ≤ σ * ‖lanczosSubspaceData H M hM g hl z‖ ^ (r - 2) ∧
    σ * ‖lanczosSubspaceData H M hM g hl z‖ ^ (r - 2) ≤ σ * ‖x‖ ^ (r - 2) ∧
    ‖lanczosSubspaceData H M hM g ((Nat.add_le_add_right hml 1).trans hl) y‖ ≤
      ‖lanczosSubspaceData H M hM g hl z‖ ∧ ‖lanczosSubspaceData H M hM g hl z‖ ≤ ‖x‖
  simpa only [(lanczosSubspaceData H M hM g
    ((Nat.add_le_add_right hml 1).trans hl)).norm_map,
      (lanczosSubspaceData H M hM g hl).norm_map] using ⟨hτμ, hμν, hpair, hstar⟩

end CartisGouldToint
