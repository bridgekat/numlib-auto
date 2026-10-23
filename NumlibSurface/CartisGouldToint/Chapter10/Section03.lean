import NumlibSurface.CartisGouldToint.Chapter10.Section01
import Numlib.Optimization.Quadratic.Krylov.TrustRegion
import Numlib.Optimization.Quadratic.Krylov.TrustRegionConvergence

/-!
# Trust-region minimization in actual preconditioned Lanczos spaces

The constrained subproblem is the genuine projected quadratic on a Euclidean
ball. Its actual multiplier and actual projected eigenvalues give the source
residual bound in the dual metric norm. The corrected iteration bound uses a
natural ceiling and a separately proved condition-one branch. The literal
integer count holds on the explicit small-tolerance domain corresponding to
the source qualification immediately before Theorem 10.3.2 (OCR line 10959).
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

/-- **Corollary 10.3.3, corrected large-tolerance form.** Actual constrained Lanczos
minimizers reach a residual tolerance within the minimum of the exact grade and the source
logarithmic count with a natural ceiling. The actual maximum condition number one gives
one-step termination. A natural ceiling clamps the logarithmic part at zero; the literal
integer ceiling is stated below on the explicit source small-tolerance domain. -/
theorem corollary_10_3_3_corrected (hH : H.toLinearMap.IsSymmetric)
    {g : EuclideanSpace ℝ (Fin n)} (hg : g ≠ 0) {G : ℕ}
    (hG : G + 1 = grade (hessian M hM H).toLinearMap (gradient M hM g))
    (ys : (i : Fin (G + 1)) → EuclideanSpace ℝ (Fin (i.val + 1)))
    (shifts : Fin (G + 1) → ℝ) {Δ : ℝ} (hΔ : 0 < Δ)
    (hfeas : ∀ i, ‖ys i‖ ≤ Δ)
    (hmin : ∀ i z, ‖z‖ ≤ Δ → lanczosTrustRegionModel H M hM g i.val (ys i) ≤
      lanczosTrustRegionModel H M hM g i.val z)
    (hsolve : ∀ i, Matrix.toEuclideanLin
      (Lanczos.tridiag (hessian M hM H).toLinearMap (gradient M hM g) (i.val + 1) +
        shifts i • 1) (ys i) =
        -(‖gradient M hM g‖ • PiLp.single 2 (0 : Fin (i.val + 1)) (1 : ℝ)))
    {ε : ℝ} (hε : 0 < ε) :
    let K := Lanczos.maxCondition (hessian M hM H).toLinearMap (gradient M hM g) G shifts
    ∃ i : Fin (G + 1),
      i.val + 1 ≤ min
        (if K = 1 then 1 else
          ⌈Real.log (2 * ‖M.inverse.comp H‖ * K * Δ / ε) /
            Real.log ((Real.sqrt K + 1) / (Real.sqrt K - 1))⌉₊ + 1) (G + 1) ∧
      let s := toOriginal M hM (lanczosSubspaceData H M hM g
        (by omega : i.val + 1 ≤ grade (hessian M hM H).toLinearMap (gradient M hM g))
        (ys i))
      energyNorm M.inverse.toLinearMap (H s + shifts i • M s + g) ≤ ε := by
  let A := hessian M hM H
  let b := gradient M hM g
  obtain ⟨i, hi, hr⟩ := QuadraticKrylov.trust_region_exists_residual_le A
    (gradient_ne_zero M hM hg) (hessian_symmetric M hM hH) hG ys shifts hΔ hfeas hmin
      hsolve (norm_hessian_le M hM hH) hε
  refine ⟨i, ?_, ?_⟩
  · simpa only [Krylov.budget_chebyshevFactor] using hi
  · have he := norm_residual M hM H g (shifts i)
      (lanczosSubspaceData H M hM g (by omega) (ys i))
    have higrade : i.val + 1 ≤ grade A.toLinearMap b := by
      dsimp only [A, b]
      omega
    change ‖A (Lanczos.basisEmbedding A.toLinearMap b higrade (ys i)) + shifts i •
      Lanczos.basisEmbedding A.toLinearMap b higrade (ys i) + b‖ = _ at he
    exact he.symm.trans_le hr

/-- **Corollary 10.3.3.** The literal integer-ceiling count holds on the explicit sufficient
small-tolerance domain `epsilon ≤ 2*norm(M⁻¹H)*kappaMax*Delta`. This makes precise the source's
“suitably small epsilon” qualification immediately before Theorem 10.3.2. A genuine maximum
condition number of one gives one-step termination. The natural-ceiling companion above
covers all positive tolerances. -/
theorem corollary_10_3_3 (hH : H.toLinearMap.IsSymmetric)
    {g : EuclideanSpace ℝ (Fin n)} (hg : g ≠ 0) {G : ℕ}
    (hG : G + 1 = grade (hessian M hM H).toLinearMap (gradient M hM g))
    (ys : (i : Fin (G + 1)) → EuclideanSpace ℝ (Fin (i.val + 1)))
    (shifts : Fin (G + 1) → ℝ) {Δ : ℝ} (hΔ : 0 < Δ)
    (hfeas : ∀ i, ‖ys i‖ ≤ Δ)
    (hmin : ∀ i z, ‖z‖ ≤ Δ → lanczosTrustRegionModel H M hM g i.val (ys i) ≤
      lanczosTrustRegionModel H M hM g i.val z)
    (hsolve : ∀ i, Matrix.toEuclideanLin
      (Lanczos.tridiag (hessian M hM H).toLinearMap (gradient M hM g) (i.val + 1) +
        shifts i • 1) (ys i) =
        -(‖gradient M hM g‖ • PiLp.single 2 (0 : Fin (i.val + 1)) (1 : ℝ)))
    {ε : ℝ} (hε : 0 < ε)
    (hsmall : Lanczos.maxCondition (hessian M hM H).toLinearMap (gradient M hM g)
        G shifts = 1 ∨ ε ≤ 2 * ‖M.inverse.comp H‖ *
          Lanczos.maxCondition (hessian M hM H).toLinearMap (gradient M hM g) G shifts * Δ) :
    let K := Lanczos.maxCondition (hessian M hM H).toLinearMap (gradient M hM g) G shifts
    ∃ i : Fin (G + 1),
      (i.val : ℤ) + 1 ≤ min
        (if K = 1 then 1 else
          (⌈Real.log (2 * ‖M.inverse.comp H‖ * K * Δ / ε) /
            Real.log ((Real.sqrt K + 1) / (Real.sqrt K - 1))⌉ : ℤ) + 1) (G + 1) ∧
      let s := toOriginal M hM (lanczosSubspaceData H M hM g
        (by omega : i.val + 1 ≤ grade (hessian M hM H).toLinearMap (gradient M hM g))
        (ys i))
      energyNorm M.inverse.toLinearMap (H s + shifts i • M s + g) ≤ ε := by
  let A := hessian M hM H
  let b := gradient M hM g
  let K := Lanczos.maxCondition A.toLinearMap b G shifts
  obtain ⟨i, hi, hr⟩ := corollary_10_3_3_corrected H M hM hH hg hG ys shifts hΔ hfeas
    hmin hsolve hε
  change i.val + 1 ≤ min
    (if K = 1 then 1 else
      ⌈Real.log (2 * ‖M.inverse.comp H‖ * K * Δ / ε) /
        Real.log ((Real.sqrt K + 1) / (Real.sqrt K - 1))⌉₊ + 1) (G + 1) at hi
  refine ⟨i, ?_, hr⟩
  change (i.val : ℤ) + 1 ≤ min
    (if K = 1 then 1 else
      (⌈Real.log (2 * ‖M.inverse.comp H‖ * K * Δ / ε) /
        Real.log ((Real.sqrt K + 1) / (Real.sqrt K - 1))⌉ : ℤ) + 1) (G + 1)
  by_cases hone : K = 1
  · have hn : i.val + 1 ≤ min 1 (G + 1) := by
      simpa only [ite_eq_left hone] using hi
    rw [ite_eq_left hone]
    exact_mod_cast hn
  · have hPD := (QuadraticKrylov.projected_trust_region_optimality A.toLinearMap
      (gradient_ne_zero M hM hg) (by dsimp only [A, b]; omega) (ys 0)
      hΔ (hfeas 0) (hmin 0) (hsolve 0)).2.1
    have hK : 1 ≤ K := (Lanczos.one_le_conditionNumber A.toLinearMap b 0
      (shifts 0) hPD).trans (Lanczos.conditionNumber_le_maxCondition A.toLinearMap b G shifts 0)
    have hKpos : 1 < K := lt_of_le_of_ne hK (Ne.symm hone)
    have hsqrt : 1 < Real.sqrt K := by
      rw [Real.lt_sqrt (by norm_num)]
      simpa using hKpos
    have hden : 0 < Real.log ((Real.sqrt K + 1) / (Real.sqrt K - 1)) := by
      apply Real.log_pos
      apply (one_lt_div (by linarith : 0 < Real.sqrt K - 1)).mpr
      linarith
    have hsm : ε ≤ 2 * ‖M.inverse.comp H‖ * K * Δ := hsmall.resolve_left hone
    have hnum : 0 ≤ Real.log (2 * ‖M.inverse.comp H‖ * K * Δ / ε) :=
      Real.log_nonneg ((one_le_div hε).mpr hsm)
    have hc := Int.natCast_ceil_eq_ceil (div_nonneg hnum hden.le)
    have hn : i.val + 1 ≤ min
        (⌈Real.log (2 * ‖M.inverse.comp H‖ * K * Δ / ε) /
          Real.log ((Real.sqrt K + 1) / (Real.sqrt K - 1))⌉₊ + 1) (G + 1) := by
      simpa only [ite_eq_right hone] using hi
    have hz : (i.val : ℤ) + 1 ≤ min
        ((⌈Real.log (2 * ‖M.inverse.comp H‖ * K * Δ / ε) /
          Real.log ((Real.sqrt K + 1) / (Real.sqrt K - 1))⌉₊ : ℤ) + 1) (G + 1) := by
      exact_mod_cast hn
    rw [ite_eq_right hone]
    simpa only [hc] using hz

end CartisGouldToint
