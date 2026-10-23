import NumlibSurface.CartisGouldToint.Chapter10.Section01
import Numlib.Optimization.Quadratic.Krylov.RegularizationMonotonicity
import Numlib.Optimization.Quadratic.Optimality.RegularizationMetric
import Numlib.Optimization.Quadratic.Krylov.RegularizationConvergence
import Numlib.Optimization.Quadratic.Optimality.MetricSpectrum

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

/-- **Corollary 10.2.3 with a natural ceiling.** Genuine Lanczos regularization
minimizers reach the true relative model-gradient test with the exact printed
logarithmic coefficient and actual maximum condition number. Natural rounding
covers a negative logarithmic count; condition number one terminates in one step. -/
theorem corollary_10_2_3_corrected (hnpos : 0 < n) (hH : H.toLinearMap.IsSymmetric)
    {g : EuclideanSpace ℝ (Fin n)} (hg : g ≠ 0) {G : ℕ}
    (hG : G + 1 = grade (hessian M hM H).toLinearMap (gradient M hM g))
    (Y : (i : Fin (G + 1)) → EuclideanSpace ℝ (Fin (i.val + 1)))
    (x : WithEnergy M.toLinearMap hM) {σ r θ : ℝ}
    (hσ : 0 < σ) (hr : 2 < r) (hθ : 0 < θ)
    (hmin : ∀ i w, lanczosRegularizationModel H M hM g i.val σ r (Y i) ≤
      lanczosRegularizationModel H M hM g i.val σ r w)
    (hx : ∀ w, QuadraticOptimality.regularized (hessian M hM H) (gradient M hM g) σ r x ≤
      QuadraticOptimality.regularized (hessian M hM H) (gradient M hM g) σ r w) :
    let shifts := fun i => σ * ‖Y i‖ ^ (r - 2)
    let K := Lanczos.maxCondition (hessian M hM H).toLinearMap (gradient M hM g) G shifts
    let t := σ * ‖x‖ ^ (r - 2)
    let U := QuadraticOptimality.Metric.greatestEigenvalue M hM H hH (by
      simpa only [finrank_euclideanSpace, Fintype.card_fin] using hnpos)
    ∃ i : Fin (G + 1), i.val + 1 ≤ min
      (if K = 1 then 1 else
        ⌈Real.log (4 * ‖M.inverse.comp H‖ * K / θ * (t / σ) ^ (1 / (r - 2)) *
          ((U + t) / energyNorm M.inverse.toLinearMap g) ^ 2) /
          Real.log ((Real.sqrt K + 1) / (Real.sqrt K - 1))⌉₊ + 1) (G + 1) ∧
      let s := toOriginal M hM (lanczosSubspaceData H M hM g (by omega) (Y i))
      energyNorm M.inverse.toLinearMap (H s + shifts i • M s + g) ≤
        θ / 2 * energyNorm M.toLinearMap s ^ 2 := by
  let A := hessian M hM H
  let b := gradient M hM g
  let shifts := fun i : Fin (G + 1) => σ * ‖Y i‖ ^ (r - 2)
  let K := Lanczos.maxCondition A.toLinearMap b G shifts
  let t := σ * ‖x‖ ^ (r - 2)
  let U := QuadraticOptimality.Metric.greatestEigenvalue M hM H hH (by
    simpa only [finrank_euclideanSpace, Fintype.card_fin] using hnpos)
  let C := 2 * ‖M.inverse.comp H‖ * K * ‖x‖
  let ε := θ / 2 * (‖b‖ / (U + t)) ^ 2
  have hsym := hessian_symmetric M hM hH
  have hupper := inner_hessian_le_greatestEigenvalue M hM H hH (by
    simpa only [finrank_euclideanSpace, Fintype.card_fin] using hnpos)
  have hb := gradient_ne_zero M hM hg
  obtain ⟨i, hi, hhit⟩ := QuadraticKrylov.regularized_relative_gradient_hitting A hb hsym
    hG Y x hσ hr (norm_hessian_le M hM hH) hθ hupper hmin hx
  have hrad : (t / σ) ^ (1 / (r - 2)) = ‖x‖ := by
    dsimp [t]
    rw [mul_div_cancel_left₀ _ hσ.ne', ←Real.rpow_mul (norm_nonneg _),
      mul_one_div_cancel (by linarith : r - 2 ≠ 0), Real.rpow_one]
  have hratio : C / ε = 4 * ‖M.inverse.comp H‖ * K / θ * (t / σ) ^ (1 / (r - 2)) *
      ((U + t) / energyNorm M.inverse.toLinearMap g) ^ 2 := by
    rw [hrad, ← norm_gradient M hM g]
    dsimp [C, ε, b]
    field_simp
    ring
  refine ⟨i, ?_, ?_⟩
  · change i.val + 1 ≤ min
      (if K = 1 then 1 else ⌈Real.log _ /
        Real.log ((Real.sqrt K + 1) / (Real.sqrt K - 1))⌉₊ + 1) (G + 1)
    change i.val + 1 ≤ min
      (if K = 1 then 1 else GeometricDecay.budget C ε (Krylov.chebyshevFactor K) + 1)
        (G + 1) at hi
    simpa only [Krylov.budget_chebyshevFactor, hratio] using hi
  · have higrade : i.val + 1 ≤ grade A.toLinearMap b := by dsimp [A, b]; omega
    rw [QuadraticKrylov.norm_fderiv_regularized A b hsym hr σ,
      (Lanczos.basisEmbedding A.toLinearMap b higrade).norm_map] at hhit
    have he := norm_residual M hM H g (shifts i)
      (lanczosSubspaceData H M hM g (by omega) (Y i))
    change ‖A (Lanczos.basisEmbedding A.toLinearMap b higrade (Y i)) + shifts i •
      Lanczos.basisEmbedding A.toLinearMap b higrade (Y i) + b‖ = _ at he
    change _ ≤ θ / 2 * ‖lanczosSubspaceData H M hM g (by omega) (Y i)‖ ^ 2
    rw [(lanczosSubspaceData H M hM g (by omega)).norm_map]
    exact he.symm.trans_le hhit

end CartisGouldToint
