import NumlibSurface.CartisGouldToint.Chapter10.Section01
import Numlib.Optimization.Quadratic.Krylov.Regularization

/-!
# Actual Lanczos regularization gradient decay

The computed global subproblem minimizer yields its actual shifted solve and
positive - definite projected matrix. Inverse decay then gives the exact source
bound in the inverse - metric norm. The norm - similarity equality in (B.10.4) is
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
end CartisGouldToint
