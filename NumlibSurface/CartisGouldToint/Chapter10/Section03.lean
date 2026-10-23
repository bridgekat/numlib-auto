import NumlibSurface.CartisGouldToint.Chapter10.Section01
import Numlib.Optimization.Quadratic.Krylov.TrustRegion

/-!
# Trust-region minimization in actual preconditioned Lanczos spaces

The constrained subproblem is the genuine projected quadratic on a Euclidean
ball. Its actual multiplier and actual projected eigenvalues give the source
residual bound in the dual metric norm.
-/

open Krylov QuadraticOptimality.Metric QuadraticRegularization.Metric
open scoped Matrix ComplexOrder
namespace CartisGouldToint
variable {n : ℕ}
variable (H M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
  (hM : M.toLinearMap.IsSymmetricCoercive)

/-- The actual projected quadratic objective (10.1.5) in a Lanczos space of dimension
`m + 1`; the trust-region constraint is the ordinary coordinate ball. -/
noncomputable def lanczosTrustRegionModel (g : EuclideanSpace ℝ (Fin n))
    (m : ℕ) (y : EuclideanSpace ℝ (Fin (m + 1))) :=
  QuadraticKrylov.projectedQuadratic (hessian M hM H).toLinearMap (gradient M hM g) m y

/-- **Theorem 10.3.2.** A true constrained Lanczos minimizer satisfies the exact residual
bound in the inverse metric norm. The shift is its actual stationary multiplier, and the
condition number uses the genuine extreme projected eigenvalues. Global minimality derives
positive definiteness; neither it nor the residual estimate is assumed. -/
theorem theorem_10_3_2 (hH : H.toLinearMap.IsSymmetric)
    {g : EuclideanSpace ℝ (Fin n)} (hg : g ≠ 0) {m : ℕ}
    (hm : m + 1 ≤ grade (hessian M hM H).toLinearMap (gradient M hM g))
    (y : EuclideanSpace ℝ (Fin (m + 1))) {Δ : ℝ} (hΔ : 0 < Δ) (hy : ‖y‖ ≤ Δ)
    (hmin : ∀ z, ‖z‖ ≤ Δ → lanczosTrustRegionModel H M hM g m y ≤
      lanczosTrustRegionModel H M hM g m z)
    {τ : ℝ} (hsolve : Matrix.toEuclideanLin
      (Lanczos.tridiag (hessian M hM H).toLinearMap (gradient M hM g) (m + 1) + τ • 1) y =
      -(‖gradient M hM g‖ • PiLp.single 2 (0 : Fin (m + 1)) (1 : ℝ))) :
    let A := hessian M hM H
    let b := gradient M hM g
    let hT := Lanczos.shifted_tridiag_isHermitian A.toLinearMap b (m + 1) τ
    let κ := hT.greatestEigenvalue / hT.leastEigenvalue
    let s := toOriginal M hM (lanczosSubspaceData H M hM g hm y)
    energyNorm M.inverse.toLinearMap (H s + τ • M s + g) ≤
      2 * ‖M.inverse.comp H‖ * κ * Δ *
        ((Real.sqrt κ - 1) / (Real.sqrt κ + 1)) ^ m := by
  let A := hessian M hM H
  let b := gradient M hM g
  have hb : b ≠ 0 := gradient_ne_zero M hM hg
  have hsym : A.toLinearMap.IsSymmetric := hessian_symmetric M hM hH
  have hPD := (QuadraticKrylov.projected_trust_region_optimality A.toLinearMap hb hm y
    hΔ hy hmin hsolve).2.1
  have hbound := QuadraticKrylov.trust_region_residual_bound A hb hsym hm y
    hΔ hy hmin hsolve
  dsimp only at hbound
  have he := norm_residual M hM H g τ (lanczosSubspaceData H M hM g hm y)
  change ‖A (Lanczos.basisEmbedding A.toLinearMap b hm y) +
    τ • Lanczos.basisEmbedding A.toLinearMap b hm y + b‖ = _ at he
  rw [he] at hbound
  apply hbound.trans
  have hk : 1 ≤ hPD.isHermitian.greatestEigenvalue / hPD.isHermitian.leastEigenvalue :=
    (one_le_div (hPD.isHermitian.leastEigenvalue_pos hPD)).mpr
      hPD.isHermitian.leastEigenvalue_le_greatest
  have hsqrt : 1 ≤ Real.sqrt (hPD.isHermitian.greatestEigenvalue /
      hPD.isHermitian.leastEigenvalue) := by
    rw [Real.le_sqrt (by norm_num) (zero_le_one.trans hk)]
    simpa using hk
  have hq : 0 ≤ (Real.sqrt (hPD.isHermitian.greatestEigenvalue /
      hPD.isHermitian.leastEigenvalue) - 1) /
      (Real.sqrt (hPD.isHermitian.greatestEigenvalue /
      hPD.isHermitian.leastEigenvalue) + 1) := by positivity
  have hnorm := norm_hessian_le M hM hH
  gcongr
/-- **Lemma 10.3.1.** Actual nested constrained Lanczos minimizers have ordered multipliers
and metric norms, bounded by those of an actual full-space trust-region minimizer. The full
quadratic is represented in the genuine metric inner product; `Metric.model_eq` identifies
it with the original objective. Interior and singular ambient shifted systems are included. -/
theorem lemma_10_3_1 (hH : H.toLinearMap.IsSymmetric)
    {g : EuclideanSpace ℝ (Fin n)} (hg : g ≠ 0) {m l : ℕ} (hml : m ≤ l)
    (hl : l + 1 ≤ grade (hessian M hM H).toLinearMap (gradient M hM g))
    (y : EuclideanSpace ℝ (Fin (m + 1))) (z : EuclideanSpace ℝ (Fin (l + 1)))
    (x : WithEnergy M.toLinearMap hM) {Δ : ℝ} (hΔ : 0 < Δ)
    (hy : ‖y‖ ≤ Δ) (hz : ‖z‖ ≤ Δ) (hx : ‖x‖ ≤ Δ)
    (hminy : ∀ w, ‖w‖ ≤ Δ → lanczosTrustRegionModel H M hM g m y ≤
      lanczosTrustRegionModel H M hM g m w)
    (hminz : ∀ w, ‖w‖ ≤ Δ → lanczosTrustRegionModel H M hM g l z ≤
      lanczosTrustRegionModel H M hM g l w)
    (hminx : ∀ w, ‖w‖ ≤ Δ →
      QuadraticOptimality.model (hessian M hM H) (gradient M hM g) x ≤
        QuadraticOptimality.model (hessian M hM H) (gradient M hM g) w)
    {τ μ ν : ℝ}
    (hsolvey : Matrix.toEuclideanLin
      (Lanczos.tridiag (hessian M hM H).toLinearMap (gradient M hM g) (m + 1) + τ • 1) y =
      -(‖gradient M hM g‖ • PiLp.single 2 (0 : Fin (m + 1)) (1 : ℝ)))
    (hsolvez : Matrix.toEuclideanLin
      (Lanczos.tridiag (hessian M hM H).toLinearMap (gradient M hM g) (l + 1) + μ • 1) z =
      -(‖gradient M hM g‖ • PiLp.single 2 (0 : Fin (l + 1)) (1 : ℝ)))
    (hsolvex : hessian M hM H x + ν • x = -(gradient M hM g)) :
    let hm := (Nat.add_le_add_right hml 1).trans hl
    let sy := toOriginal M hM (lanczosSubspaceData H M hM g hm y)
    let sz := toOriginal M hM (lanczosSubspaceData H M hM g hl z)
    let sx := toOriginal M hM x
    τ ≤ μ ∧ μ ≤ ν ∧ energyNorm M.toLinearMap sy ≤ energyNorm M.toLinearMap sz ∧
      energyNorm M.toLinearMap sz ≤ energyNorm M.toLinearMap sx := by
  have hh := QuadraticKrylov.trust_region_nested_minimizers (hessian M hM H)
    (gradient_ne_zero M hM hg) (hessian_symmetric M hM hH) hml hl y z x hΔ hy hz hx
    hminy hminz hminx hsolvey hsolvez hsolvex
  change τ ≤ μ ∧ μ ≤ ν ∧
    ‖lanczosSubspaceData H M hM g ((Nat.add_le_add_right hml 1).trans hl) y‖ ≤
      ‖lanczosSubspaceData H M hM g hl z‖ ∧
        ‖lanczosSubspaceData H M hM g hl z‖ ≤ ‖x‖
  simpa only [(lanczosSubspaceData H M hM g
    ((Nat.add_le_add_right hml 1).trans hl)).norm_map,
      (lanczosSubspaceData H M hM g hl).norm_map] using hh

end CartisGouldToint
