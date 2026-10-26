import NumlibSurface.CartisGouldToint.Chapter10.Section02

/-!
# Cartis–Gould–Toint §10.3: The trust-region case

Surface file for [cartis2022evaluation] §10.3: the Krylov subspace solutions `sₖ = Qₖ s̄ₖ` of the
trust-region subproblem, where `s̄ₖ` globally minimizes the reduced problem (10.1.5)
`γ₁ ⟪e₁, s̄⟫ + ½ ⟪s̄, Tₖ s̄⟫` over `‖s̄‖ ≤ Δ`, with Lagrange multiplier `λₖ` (the multiplier
conditions of Theorem 8.2.7 for the data `(γ₁ e₁, Tₖ, Iₖ)`, `Chapter08.IsTrustRegionKKT`).

## Main results

* `lemma_10_3_1` — the multipliers and norms increase with `k`, and `Tₖ + λₖ Iₖ` is positive
  definite.
* `theorem_10_3_2` — the residual bound.
* `corollary_10_3_3` — the iteration bound for the test (10.3.2).
* `start_10_3` — the one-dimensional start.

## Implementation notes

As in §10.2, `‖M⁻¹H‖` is the operator norm induced by `‖·‖_M`, i.e. `‖Subproblem.scaledOp H hM‖`.

## Corrections to the source

* Corollary 10.3.3: the printed `⌈log(2‖M⁻¹H‖κ*Δ/ε) / log((√κ* + 1)/(√κ* - 1))⌉ + 1` is
  unsatisfiable when the logarithm is negative (large `ε`) and undefined for `κ* = 1`; the ceiling
  is read as `⌈·⌉₊` and for `κ* = 1` the test holds at some `k ≤ min(2, grade)`. The hypothesis
  `g ≠ 0` is needed.
-/

open Matrix Set
open scoped RealInnerProductSpace

namespace CartisGouldToint.Chapter10

open Subproblem CartisGouldToint.Chapter08 CartisGouldToint.Chapter09

variable {n : ℕ} {H M : Matrix (Fin n) (Fin n) ℝ} {g : EuclideanSpace ℝ (Fin n)}

/-- **The reduced multiplier is a multiplier of the subproblem on `𝒦ₖ`.** If `λ` is a
trust-region multiplier of `s̄` for the reduced data `(Qₖᵀ g, Tₖ, Iₖ)` (`1 ≤ k ≤ grade`), then,
`M⁻¹`-transported, `λ` is a trust-region multiplier of `Qₖ s̄` for the compressed data on the
Krylov subspace `𝒦ₖ` of the scaled operator. -/
theorem isTrustRegionMultiplier_krylov_of_kkt (hH : H.IsHermitian) (hM : M.PosDef) {k : ℕ}
    (hk1 : 1 ≤ k) (hk : k ≤ gradeHM H M g) {Δ lam : ℝ} (hΔ : 0 < Δ)
    {sbar : EuclideanSpace ℝ (Fin k)}
    (h : IsTrustRegionKKT (lanczosGrad hM H g k) (lanczosTridiag hM H g k) 1 Δ sbar lam) :
    IsTrustRegionMultiplier
      ((Krylov.subspace (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM)
        (scaledGrad hM g) k).orthogonalProjectionOnto (scaledGrad hM g))
      (compressionL (scaledOp H hM)
        (Krylov.subspace (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM) (scaledGrad hM g) k))
      Δ ⟨toScaled hM (toEuclideanLin (lanczosBasis hM H g k) sbar),
        toScaled_lanczosBasis_mem hM sbar⟩ lam := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hT := isSymmetric_scaledOp (hM := hM) hH
  have hb := ne_zero_of_le_gradeHM hM hk1 hk
  have hm : m + 1 ≤ Krylov.grade (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM)
      (scaledGrad hM g) := by rw [← gradeHM_eq hM]; exact hk
  set K := Krylov.subspace (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM)
    (scaledGrad hM g) (m + 1)
  have hx := toScaled_lanczosBasis (H := H) (g := g) hM sbar
  -- the reduced shifted system in coordinates
  have hsys : (Lanczos.tridiag (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM)
      (scaledGrad hM g) (m + 1) + lam • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)) *ᵥ
        WithLp.ofLp sbar = -(Pi.single 0 ‖scaledGrad hM g‖ : Fin (m + 1) → ℝ) := by
    have := congrArg WithLp.ofLp h.shifted
    rw [lanczosGrad_eq hM hk1, mNorm_inv_eq_norm_scaledGrad hM] at this
    rw [← lanczosTridiag]
    simpa [toEuclideanLin_apply, Matrix.add_mulVec, Matrix.smul_mulVec] using this
  obtain ⟨hrel, -, hquad, -⟩ := krylov_lanczos_coordinates hT hb hm (WithLp.ofLp sbar)
    (WithLp.ofLp sbar) lam
  have hnorm : ‖toScaled hM (toEuclideanLin (lanczosBasis hM H g (m + 1)) sbar)‖ = ‖sbar‖ := by
    rw [← mNorm_eq_norm_toScaled hM, mNorm_lanczosBasis hM hk]
  refine ⟨h.nonneg, ?_, ?_, ?_⟩
  · rw [compressionL_shifted_iff]
    intro v hv
    rw [hx, hrel, hsys, neg_add_cancel]
    simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero, zero_add, real_inner_smul_left]
    rw [Submodule.inner_left_of_mem_orthogonal hv (Arnoldi.vec_mem_orthogonal _ _ _), mul_zero]
  · rw [ContinuousLinearMap.isPositive_add_smul_one_iff (isSymmetric_compressionL hT)]
    intro v
    rw [real_inner_comm, inner_compressionL_add_smul_apply]
    have hv := eq_sum_inner_vec (H := scaledOp H hM) v.2
    rw [hv, (krylov_lanczos_coordinates hT hb hm _ _ lam).2.2.1, ← lanczosTridiag]
    simpa using h.posSemidef.dotProduct_mulVec_nonneg _
  · have hc := h.complementarity
    rw [← mul_mNorm_sub_eq_zero_iff 1 hΔ, mNorm_one] at hc
    exact (congrArg (fun x => lam * (x - Δ)) hnorm).trans hc

/-- **Lemma 10.3.1 of [cartis2022evaluation] (Nested subspace trust-region solutions norm
increase).** Let `H` be symmetric, `M` positive definite, `Δ > 0`, `1 ≤ k ≤ ℓ ≤ grade(M⁻¹H, M⁻¹g)`;
let `s̄ₖ`, `s̄ℓ` be global solutions of (10.1.5) with Lagrange multipliers `λₖ`, `λℓ`,
`sₖ = Qₖ s̄ₖ`, `sℓ = Qℓ s̄ℓ`, and let `s*` be a global solution of (8.1.2) with multiplier `λ*`.
Then `λₖ ≤ λℓ ≤ λ*` and `‖sₖ‖_M ≤ ‖sℓ‖_M ≤ ‖s*‖_M`. Moreover `Tₖ + λₖ Iₖ` is positive definite (no
hard case in the subspace), so `s̄ₖ` is the unique solution of (10.1.5). -/
theorem lemma_10_3_1 (hH : H.IsHermitian) (hM : M.PosDef) {Δ : ℝ} (hΔ : 0 < Δ) {k ℓ : ℕ}
    (hk : 1 ≤ k) (hkℓ : k ≤ ℓ) (hℓ : ℓ ≤ gradeHM H M g)
    {sbark : EuclideanSpace ℝ (Fin k)} {sbarl : EuclideanSpace ℝ (Fin ℓ)} {lamk laml : ℝ}
    (hsk : IsTrustRegionSolution (lanczosGrad hM H g k) (lanczosTridiag hM H g k) 1 Δ sbark)
    (hmk : IsTrustRegionKKT (lanczosGrad hM H g k) (lanczosTridiag hM H g k) 1 Δ sbark lamk)
    (hsl : IsTrustRegionSolution (lanczosGrad hM H g ℓ) (lanczosTridiag hM H g ℓ) 1 Δ sbarl)
    (hml : IsTrustRegionKKT (lanczosGrad hM H g ℓ) (lanczosTridiag hM H g ℓ) 1 Δ sbarl laml)
    {sstar : EuclideanSpace ℝ (Fin n)} {lamstar : ℝ} (hstar : IsTrustRegionSolution g H M Δ sstar)
    (hmstar : IsTrustRegionKKT g H M Δ sstar lamstar) :
    (lamk ≤ laml ∧ laml ≤ lamstar) ∧
      mNorm M (toEuclideanLin (lanczosBasis hM H g k) sbark) ≤
        mNorm M (toEuclideanLin (lanczosBasis hM H g ℓ) sbarl) ∧
      mNorm M (toEuclideanLin (lanczosBasis hM H g ℓ) sbarl) ≤ mNorm M sstar ∧
      (lanczosTridiag hM H g k + lamk • (1 : Matrix (Fin k) (Fin k) ℝ)).PosDef ∧
      ∀ u, IsTrustRegionSolution (lanczosGrad hM H g k) (lanczosTridiag hM H g k) 1 Δ u →
        u = sbark := by
  have hT := isSymmetric_scaledOp (hM := hM) hH
  have hk' : k ≤ gradeHM H M g := hkℓ.trans hℓ
  have hb := ne_zero_of_le_gradeHM hM hk hk'
  have hmk' := isTrustRegionMultiplier_krylov_of_kkt hH hM hk hk' hΔ hmk
  have hml' := isTrustRegionMultiplier_krylov_of_kkt hH hM (hk.trans hkℓ) hℓ hΔ hml
  have hnk : ‖toScaled hM (toEuclideanLin (lanczosBasis hM H g k) sbark)‖ ≤ Δ := by
    rw [← mNorm_eq_norm_toScaled hM, mNorm_lanczosBasis hM hk', ← mNorm_one]; exact hsk.1
  have hnl : ‖toScaled hM (toEuclideanLin (lanczosBasis hM H g ℓ) sbarl)‖ ≤ Δ := by
    rw [← mNorm_eq_norm_toScaled hM, mNorm_lanczosBasis hM hℓ, ← mNorm_one]; exact hsl.1
  have hns : ‖toScaled hM sstar‖ ≤ Δ := by rw [← mNorm_eq_norm_toScaled hM]; exact hstar.1
  obtain ⟨hlam, h1, h2⟩ := krylov_multiplier_mono_trustRegion hT hΔ hk hkℓ
    (toScaled_lanczosBasis_mem hM sbark) hnk hmk' (toScaled_lanczosBasis_mem hM sbarl) hnl hml'
    ((isTrustRegionKKT_iff_scaled hM hΔ).1 hmstar) hns
  simp only [← mNorm_eq_norm_toScaled hM] at h1 h2
  have hpd : (lanczosTridiag hM H g k + lamk • (1 : Matrix (Fin k) (Fin k) ℝ)).PosDef := by
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    exact posDef_tridiag_add hT hb (by rw [← gradeHM_eq hM]; exact hk')
      (neg_leftmost_lt_of_isTrustRegionMultiplier_krylov hT hb hk
        (toScaled_lanczosBasis_mem hM sbark) hmk').1
  exact ⟨hlam, h1, h2, hpd, fun u hu => eq_of_isTrustRegionKKT_of_posDef
    (lanczosTridiag_isHermitian hM k) PosDef.one hΔ hmk hsk.1 hpd hu⟩

/-- **Theorem 10.3.2 of [cartis2022evaluation] (Bound on the residual at the subspace
minimizer).** Let `H` be symmetric, `M` positive definite, `Δ > 0`, `1 ≤ k ≤ grade(M⁻¹H, M⁻¹g)`,
let `s̄ₖ` be a global solution of (10.1.5) with Lagrange multiplier `λₖ`, `sₖ = Qₖ s̄ₖ`, and `κₖ`
the condition number (10.2.8) at `λₖ`. Then the residual (10.3.1) `rₖ = g + (H + λₖ M) sₖ`
satisfies `‖rₖ‖_{M⁻¹} ≤ 2 ‖M⁻¹H‖ κₖ Δ ((√κₖ - 1)/(√κₖ + 1))^{k-1}`, `‖M⁻¹H‖` the operator norm
induced by `‖·‖_M`. -/
theorem theorem_10_3_2 (hH : H.IsHermitian) (hM : M.PosDef) {Δ : ℝ} (hΔ : 0 < Δ) {k : ℕ}
    (hk1 : 1 ≤ k) (hk : k ≤ gradeHM H M g) {sbar : EuclideanSpace ℝ (Fin k)} {lam : ℝ}
    (hs : IsTrustRegionSolution (lanczosGrad hM H g k) (lanczosTridiag hM H g k) 1 Δ sbar)
    (hm : IsTrustRegionKKT (lanczosGrad hM H g k) (lanczosTridiag hM H g k) 1 Δ sbar lam) :
    mNorm M⁻¹ (g + toEuclideanLin (H + lam • M) (toEuclideanLin (lanczosBasis hM H g k) sbar)) ≤
      2 * ‖scaledOp H hM‖ *
        conditionNumber_10_2_8 hM H g k lam * Δ *
        ((√(conditionNumber_10_2_8 hM H g k lam) - 1) /
          (√(conditionNumber_10_2_8 hM H g k lam) + 1)) ^ (k - 1) := by
  have hT := isSymmetric_scaledOp (hM := hM) hH
  have hb := ne_zero_of_le_gradeHM hM hk1 hk
  have hm' := isTrustRegionMultiplier_krylov_of_kkt hH hM hk1 hk hΔ hm
  have hn : ‖toScaled hM (toEuclideanLin (lanczosBasis hM H g k) sbar)‖ ≤ Δ := by
    rw [← mNorm_eq_norm_toScaled hM, mNorm_lanczosBasis hM hk, ← mNorm_one]; exact hs.1
  have hbound := krylov_residual_bound_trustRegion hT hb hk1 (toScaled_lanczosBasis_mem hM sbar)
    hn hm'
  have hres : toEuclideanLin (H + lam • M) (toEuclideanLin (lanczosBasis hM H g k) sbar) =
      toEuclideanLin H (toEuclideanLin (lanczosBasis hM H g k) sbar) +
        lam • toEuclideanLin M (toEuclideanLin (lanczosBasis hM H g k) sbar) := by
    rw [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply]
  rw [hres, ← add_assoc, mNorm_inv_gradient hM, conditionNumber_eq_krylovCond hH hM hk]
  exact hbound

/-- **Corollary 10.3.3 of [cartis2022evaluation] (Iteration bound for the trust-region subspace
approximation)**, corrected. Let `H` be symmetric, `M` positive definite, `g ≠ 0`, `Δ > 0`,
`ε > 0`; for `1 ≤ k ≤ grade(M⁻¹H, M⁻¹g)` let `s̄ₖ` be a global solution of (10.1.5) with Lagrange
multiplier `λₖ`, `sₖ = Qₖ s̄ₖ`, and let `κ*` be (10.2.10). Then the test (10.3.2)
`‖g + (H + λₖ M) sₖ‖_{M⁻¹} ≤ ε` holds for some
`1 ≤ k ≤ min(⌈log(2‖M⁻¹H‖κ*Δ/ε) / log((√κ* + 1)/(√κ* - 1))⌉₊ + 1, grade)` when `κ* > 1`, and for
some `1 ≤ k ≤ min(2, grade)` when `κ* = 1`. -/
theorem corollary_10_3_3 (hH : H.IsHermitian) (hM : M.PosDef) (hg : g ≠ 0) {Δ ε : ℝ}
    (hΔ : 0 < Δ) (hε : 0 < ε) {sbar : (k : ℕ) → EuclideanSpace ℝ (Fin k)} {lam : ℕ → ℝ}
    (hs : ∀ k, 1 ≤ k → k ≤ gradeHM H M g →
      IsTrustRegionSolution (lanczosGrad hM H g k) (lanczosTridiag hM H g k) 1 Δ (sbar k) ∧
        IsTrustRegionKKT (lanczosGrad hM H g k) (lanczosTridiag hM H g k) 1 Δ (sbar k) (lam k))
    {s : ℕ → EuclideanSpace ℝ (Fin n)}
    (hsk : ∀ k, s k = toEuclideanLin (lanczosBasis hM H g k) (sbar k)) :
    (1 < kappaStar hM H g lam →
      ∃ k, 1 ≤ k ∧
        k ≤ min (⌈Real.log (2 * ‖scaledOp H hM‖ *
            kappaStar hM H g lam * Δ / ε) /
          Real.log ((√(kappaStar hM H g lam) + 1) / (√(kappaStar hM H g lam) - 1))⌉₊ + 1)
          (gradeHM H M g) ∧
        mNorm M⁻¹ (g + toEuclideanLin (H + lam k • M) (s k)) ≤ ε) ∧
    (kappaStar hM H g lam = 1 →
      ∃ k, 1 ≤ k ∧ k ≤ min 2 (gradeHM H M g) ∧
        mNorm M⁻¹ (g + toEuclideanLin (H + lam k • M) (s k)) ≤ ε) := by
  have hT := isSymmetric_scaledOp (hM := hM) hH
  have hb := scaledGrad_ne_zero (hM := hM) hg
  set κs := kappaStar hM H g lam
  set G := gradeHM H M g
  have hGeq : G = Krylov.grade (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM)
      (scaledGrad hM g) := gradeHM_eq hM
  have hG : 1 ≤ G := by rw [hGeq]; exact Krylov.grade_pos_of_ne_zero _ _ hb
  have hS : ∀ k, toScaled hM (s k) ∈
      Krylov.subspace (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM) (scaledGrad hM g) k :=
    fun k => hsk k ▸ toScaled_lanczosBasis_mem hM (sbar k)
  have hmul : ∀ k, 1 ≤ k → k ≤ Krylov.grade (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] _)
      (scaledGrad hM g) → ‖toScaled hM (s k)‖ ≤ Δ ∧ IsTrustRegionMultiplier
        ((Krylov.subspace (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] _)
          (scaledGrad hM g) k).orthogonalProjectionOnto (scaledGrad hM g))
        (compressionL (scaledOp H hM) _) Δ ⟨toScaled hM (s k), hS k⟩ (lam k) := fun k hk1 hk => by
    rw [← hGeq] at hk
    obtain ⟨h1, h2⟩ := hs k hk1 hk
    have := isTrustRegionMultiplier_krylov_of_kkt hH hM hk1 hk hΔ h2
    simp only [← hsk k] at this
    refine ⟨?_, this⟩
    rw [← mNorm_eq_norm_toScaled hM, hsk k, mNorm_lanczosBasis hM hk, ← mNorm_one]; exact h1.1
  have hκs : ∀ k, 1 ≤ k → k ≤ Krylov.grade (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] _)
      (scaledGrad hM g) → krylovCond hT (scaledGrad hM g) k (lam k) ≤ κs := fun k hk1 hk => by
    rw [← hGeq] at hk
    rw [← conditionNumber_eq_krylovCond hH hM hk]
    exact le_kappaStar hM lam hk1 hk
  have hκ1 : 1 ≤ κs := by
    refine le_trans ?_ (hκs 1 le_rfl (hGeq ▸ hG))
    exact one_le_krylovCond hT (neg_leftmost_lt_of_isTrustRegionMultiplier_krylov hT hb le_rfl
      (hS 1) (hmul 1 le_rfl (hGeq ▸ hG)).2).1
  obtain ⟨hP, hPG, -, -⟩ := krylov_iteration_bound_trustRegion hT hb hε hS hmul hκs
  rw [← hGeq] at hP hPG
  have htest : ∀ k,
      ‖scaledGrad hM g + scaledOp H hM (toScaled hM (s k)) + lam k • toScaled hM (s k)‖ =
      mNorm M⁻¹ (g + toEuclideanLin (H + lam k • M) (s k)) := fun k => by
    rw [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, ← add_assoc,
      mNorm_inv_gradient hM]
  simp only [htest] at hP hPG
  set A := 2 * ‖scaledOp H hM‖ * κs * Δ / ε
  have hP' : ∀ k, 1 ≤ k → k ≤ G → A * convFactor κs ^ (k - 1) ≤ 1 →
      mNorm M⁻¹ (g + toEuclideanLin (H + lam k • M) (s k)) ≤ ε := fun k hk1 hk hA => by
    refine hP k hk1 hk ?_
    have hq := convFactor_nonneg hκ1
    have : 0 ≤ κs := by linarith
    simp only [A] at hA
    rw [div_mul_eq_mul_div, div_le_one hε] at hA
    refine le_trans ?_ hA
    gcongr
  obtain ⟨h1, h2⟩ := exists_le_min_of_geometric hG hP' hPG
  refine ⟨fun hκ => ?_, fun hκ => h2 (by rw [hκ, convFactor_one])⟩
  have := h1 (convFactor_pos hκ) (convFactor_lt_one κs)
  rwa [convFactor, one_div_div] at this

/-- The quadratic `γ s + ½ ρ s²` with a multiplier: if `λ ≥ 0`, `γ + (ρ + λ) s = 0`,
`ρ + λ > 0` and `λ (|s| - Δ) = 0`, then `s` (with `|s| ≤ Δ`) is the unique global minimizer over
`[-Δ, Δ]`. -/
theorem scalar_trustRegion_unique {γ ρ Δ lam s : ℝ} (hlam : 0 ≤ lam)
    (hshift : γ + (ρ + lam) * s = 0)
    (hpos : 0 < ρ + lam) (hcompl : lam * (|s| - Δ) = 0) (hs : |s| ≤ Δ) (u : ℝ) :
    (|u| ≤ Δ ∧ ∀ v, |v| ≤ Δ → γ * u + 1 / 2 * ρ * u ^ 2 ≤ γ * v + 1 / 2 * ρ * v ^ 2) ↔ u = s := by
  have hγ : γ = -((ρ + lam) * s) := by linarith
  have hs2 : lam * s ^ 2 = lam * Δ ^ 2 := by
    rcases eq_or_ne lam 0 with h | h
    · rw [h]; ring
    · have : |s| = Δ := by
        have := mul_eq_zero.1 hcompl; rcases this with h' | h'
        · exact absurd h' h
        · linarith
      rw [← sq_abs s, this]
  -- `f(v) - f(s) = ½ (ρ + λ) (v - s)² + ½ λ (Δ² - v²)`
  have key : ∀ v, γ * v + 1 / 2 * ρ * v ^ 2 - (γ * s + 1 / 2 * ρ * s ^ 2) =
      1 / 2 * (ρ + lam) * (v - s) ^ 2 + 1 / 2 * lam * (Δ ^ 2 - v ^ 2) := fun v => by
    rw [hγ]; linear_combination (1 / 2 : ℝ) * hs2
  have hle : ∀ v, |v| ≤ Δ → γ * s + 1 / 2 * ρ * s ^ 2 ≤ γ * v + 1 / 2 * ρ * v ^ 2 := by
    intro v hv
    have h1 : v ^ 2 ≤ Δ ^ 2 := by
      rw [← sq_abs v]; exact pow_le_pow_left₀ (abs_nonneg _) hv 2
    have := key v
    nlinarith [sq_nonneg (v - s), mul_nonneg hlam (sub_nonneg.2 h1)]
  constructor
  · rintro ⟨hu, humin⟩
    have h1 := humin s hs
    have h2 : u ^ 2 ≤ Δ ^ 2 := by
      rw [← sq_abs u]; exact pow_le_pow_left₀ (abs_nonneg _) hu 2
    have := key u
    have h3 : (u - s) ^ 2 ≤ 0 := by
      nlinarith [sq_nonneg (u - s), mul_nonneg hlam (sub_nonneg.2 h2)]
    have : u - s = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1
      (le_antisymm h3 (sq_nonneg _))
    linarith
  · rintro rfl
    exact ⟨hs, hle⟩

/-- **Starting the trust-region Lanczos process** ([cartis2022evaluation], end of §10.3). For
`k = 1` the problem (10.1.5) is `min {γ₁ s + ½ ρ₁ s² : |s| ≤ Δ}`, with `γ₁ ≠ 0`, `Δ > 0`.
(i) If `ρ₁ > 0` and `|γ₁/ρ₁| ≤ Δ`, its unique solution is `s̄₁ = -γ₁/ρ₁`, with multiplier
`λ₁ = 0`.
(ii) Otherwise its unique solution is `s̄₁ = -(γ₁/|γ₁|) Δ`, with multiplier
`λ₁ = -ρ₁ + |γ₁|/Δ > 0`.
"Multiplier" means `λ₁ ≥ 0`, `γ₁ + (ρ₁ + λ₁) s̄₁ = 0`, `ρ₁ + λ₁ > 0` and `λ₁ (|s̄₁| - Δ) = 0`. -/
theorem start_10_3 {γ₁ ρ₁ Δ : ℝ} (hγ : γ₁ ≠ 0) (hΔ : 0 < Δ) :
    (0 < ρ₁ ∧ |γ₁ / ρ₁| ≤ Δ →
      (∀ u, (|u| ≤ Δ ∧ ∀ v, |v| ≤ Δ →
          γ₁ * u + 1 / 2 * ρ₁ * u ^ 2 ≤ γ₁ * v + 1 / 2 * ρ₁ * v ^ 2) ↔ u = -γ₁ / ρ₁) ∧
        γ₁ + (ρ₁ + 0) * (-γ₁ / ρ₁) = 0 ∧ 0 < ρ₁ + 0 ∧ (0 : ℝ) * (|-γ₁ / ρ₁| - Δ) = 0) ∧
    (¬ (0 < ρ₁ ∧ |γ₁ / ρ₁| ≤ Δ) →
      (∀ u, (|u| ≤ Δ ∧ ∀ v, |v| ≤ Δ →
          γ₁ * u + 1 / 2 * ρ₁ * u ^ 2 ≤ γ₁ * v + 1 / 2 * ρ₁ * v ^ 2) ↔
        u = -(γ₁ / |γ₁|) * Δ) ∧
        0 < -ρ₁ + |γ₁| / Δ ∧ γ₁ + (ρ₁ + (-ρ₁ + |γ₁| / Δ)) * (-(γ₁ / |γ₁|) * Δ) = 0 ∧
        0 < ρ₁ + (-ρ₁ + |γ₁| / Δ) ∧ (-ρ₁ + |γ₁| / Δ) * (|-(γ₁ / |γ₁|) * Δ| - Δ) = 0) := by
  have hγa : 0 < |γ₁| := abs_pos.2 hγ
  constructor
  · rintro ⟨hρ, hle⟩
    have hshift : γ₁ + (ρ₁ + 0) * (-γ₁ / ρ₁) = 0 := by field_simp; ring
    refine ⟨fun u => scalar_trustRegion_unique le_rfl hshift (by linarith) (by ring)
      (by rwa [neg_div, abs_neg]) u, hshift, by linarith, by ring⟩
  · intro hnot
    have habs : |-(γ₁ / |γ₁|) * Δ| = Δ := by
      rw [abs_mul, abs_neg, abs_div, abs_abs, div_self hγa.ne', one_mul, abs_of_pos hΔ]
    have hlam : 0 < -ρ₁ + |γ₁| / Δ := by
      by_cases hρ : 0 < ρ₁
      · have : Δ < |γ₁ / ρ₁| := not_le.1 fun h => hnot ⟨hρ, h⟩
        rw [abs_div, abs_of_pos hρ, lt_div_iff₀ hρ] at this
        rw [lt_neg_add_iff_add_lt, add_zero, lt_div_iff₀ hΔ]
        linarith
      · have : 0 < |γ₁| / Δ := div_pos hγa hΔ
        linarith
    have hshift : γ₁ + (ρ₁ + (-ρ₁ + |γ₁| / Δ)) * (-(γ₁ / |γ₁|) * Δ) = 0 := by
      field_simp; ring
    have hpos : 0 < ρ₁ + (-ρ₁ + |γ₁| / Δ) := by rw [add_neg_cancel_left]; exact div_pos hγa hΔ
    have hcompl : (-ρ₁ + |γ₁| / Δ) * (|-(γ₁ / |γ₁|) * Δ| - Δ) = 0 := by
      rw [habs, sub_self, mul_zero]
    exact ⟨fun u => scalar_trustRegion_unique hlam.le hshift hpos hcompl habs.le u, hlam, hshift,
      hpos, hcompl⟩

end CartisGouldToint.Chapter10
