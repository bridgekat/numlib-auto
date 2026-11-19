/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.CartisGouldToint.Chapter10.Section02

/-!
# Cartis, Gould and Toint, Section 10.3: The trust-region case

This module formalizes §10.3 of [cartis2022evaluation]: the Krylov subspace solutions of the
trust-region subproblem (8.1.2). Let $H \in \mathbb{R}^{n \times n}$ be symmetric,
$M \in \mathbb{R}^{n \times n}$ positive definite and $\Delta > 0$. On the Krylov subspace
$\mathcal{K}_k = \mathcal{K}(M^{-1}H, M^{-1}g, k)$ with the Lanczos basis $Q_k$ and the Lanczos
tridiagonal matrix $T_k$ of §10.1, the subspace solution is $s_k = Q_k \bar{s}_k$, where $\bar{s}_k$
is a global solution of the reduced problem (10.1.5)
$$\min_{\bar{s} \in \mathbb{R}^k} \; \gamma_1 \langle e_1, \bar{s} \rangle + \tfrac12 \langle
  \bar{s}, T_k \bar{s} \rangle \quad\text{subject to}\quad \|\bar{s}\| \le \Delta,$$
with a Lagrange multiplier $\lambda_k$ in the sense of Theorem 8.2.7 for the data
$(\gamma_1 e_1, T_k, I_k)$.

The module proves that the multipliers and the norms $\|s_k\|_M$ increase with $k$ and that
$T_k + \lambda_k I_k$ is positive definite (Lemma 10.3.1), bounds the residual
$g + (H + \lambda_k M) s_k$ in terms of the condition number $\kappa_k$ of (10.2.8) (Theorem
10.3.2), bounds the number of Lanczos iterations before the residual test (10.3.2) holds (Corollary
10.3.3), and solves the one-dimensional problem that starts the process. The proofs use the backbone
module `Numlib.Optimization.Subproblem.KrylovConvergence`.

## Main results

* Lemma 10.3.1, `CartisGouldToint.Chapter10.lemma_10_3_1`: the multipliers $\lambda_k$ and the norms
  $\|s_k\|_M$ increase with $k$, and $T_k + \lambda_k I_k$ is positive definite.
* Theorem 10.3.2, `CartisGouldToint.Chapter10.theorem_10_3_2`: the residual $r_k$ of (10.3.1) decays
  like $((\sqrt{\kappa_k} - 1)/(\sqrt{\kappa_k} + 1))^{k-1}$.
* Corollary 10.3.3, `CartisGouldToint.Chapter10.corollary_10_3_3`: the test (10.3.2) holds after a
  number of iterations of order $\log(2 \|M^{-1}H\| \kappa_* \Delta / \epsilon) /
  \log((\sqrt{\kappa_*} + 1)/(\sqrt{\kappa_*} - 1))$.
* §10.3, start of the Lanczos process, `CartisGouldToint.Chapter10.start_10_3`: the solution and the
  multiplier of the one-dimensional problem for $k = 1$.

## Conventions

* A Lagrange multiplier $\lambda$ of a step $s$ is `CartisGouldToint.Chapter08.IsTrustRegionKKT`:
  $\lambda \ge 0$, $(H + \lambda M) s = -g$, $H + \lambda M$ positive semidefinite, and
  $\lambda (\|s\|_M^2 - \Delta^2) = 0$. A global solution of (10.1.5) is
  `CartisGouldToint.Chapter08.IsTrustRegionSolution` for the data $Q_k^T g$, $T_k$ and $I_k$.

## Implementation notes

* As in §10.2, $\|M^{-1}H\|$ is the operator norm of $M^{-1}H$ induced by $\|\cdot\|_M$, that is,
  the norm of `Subproblem.scaledOp H hM`.

## Deviations from the source

* **Corollary 10.3.3** (correction). The printed bound $\lceil \log(2 \|M^{-1}H\| \kappa_* \Delta /
  \epsilon) / \log((\sqrt{\kappa_*} + 1)/(\sqrt{\kappa_*} - 1)) \rceil + 1$ can be below $1$
  and is undefined for $\kappa_* = 1$. The ceiling is $\lceil \cdot \rceil_+$,
  the case $\kappa_* = 1$ gives some $k \le \min(2, \text{grade})$, and the hypothesis $g \neq 0$ is
  added. See `CartisGouldToint.Chapter10.corollary_10_3_3`.
-/

open Matrix Set
open scoped RealInnerProductSpace

namespace CartisGouldToint.Chapter10

open Subproblem CartisGouldToint.Chapter08 CartisGouldToint.Chapter09

variable {n : ℕ} {H M : Matrix (Fin n) (Fin n) ℝ} {g : EuclideanSpace ℝ (Fin n)}

/-- Let $H$ be symmetric, $M$ positive definite, $\Delta > 0$ and $1 \le k \le
\operatorname{grade}(M^{-1}H, M^{-1}g)$. If $\lambda$ is a trust-region multiplier of
$\bar{s} \in \mathbb{R}^k$ for the reduced data $(Q_k^T g, T_k, I_k)$, then $\lambda$ is a
trust-region multiplier of $Q_k \bar{s}$ for the subproblem on $\mathcal{K}_k$ in the $M$-inner
product space: the data are the orthogonal projection of $M^{-1}g$ onto $\mathcal{K}_k$ and the
compression of $M^{-1}H$ to $\mathcal{K}_k$.

The multiplier conditions on $\mathcal{K}_k$ are `Subproblem.IsTrustRegionMultiplier`, and the
compression is `Subproblem.compressionL`. -/
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
    rw [← lanczosTridiag_def]
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
    rw [hv, (krylov_lanczos_coordinates hT hb hm _ _ lam).2.2.1, ← lanczosTridiag_def]
    simpa using h.posSemidef.dotProduct_mulVec_nonneg _
  · have hc := h.complementarity
    rw [← mul_mNorm_sub_eq_zero_iff 1 hΔ, mNorm_one] at hc
    exact (congrArg (fun x => lam * (x - Δ)) hnorm).trans hc

/-- **Lemma 10.3.1** of [cartis2022evaluation] (nested subspace trust-region solutions increase in
norm). Let $H \in \mathbb{R}^{n \times n}$ be symmetric, $M \in \mathbb{R}^{n \times n}$
positive definite, $\Delta > 0$ and $1 \le k \le \ell \le \operatorname{grade}(M^{-1}H,
M^{-1}g)$. Let $\bar{s}_k$ and $\bar{s}_\ell$ be global solutions of the reduced problems
(10.1.5) of dimensions $k$ and $\ell$, with Lagrange multipliers $\lambda_k$ and $\lambda_\ell$,
and let $s_k = Q_k \bar{s}_k$ and $s_\ell = Q_\ell \bar{s}_\ell$. Let $s_*$ be a global solution
of the trust-region subproblem (8.1.2) with Lagrange multiplier $\lambda_*$. Then
$$\lambda_k \le \lambda_\ell \le \lambda_* \quad\text{and}\quad \|s_k\|_M \le \|s_\ell\|_M \le
  \|s_*\|_M.$$
Moreover $T_k + \lambda_k I_k$ is positive definite, so the hard case cannot occur in the
subspace, and $\bar{s}_k$ is the unique global solution of (10.1.5). -/
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

/-- **Theorem 10.3.2** of [cartis2022evaluation] (bound on the residual at the subspace minimizer).
Let $H \in \mathbb{R}^{n \times n}$ be symmetric, $M \in \mathbb{R}^{n \times n}$ positive
definite, $\Delta > 0$ and $1 \le k \le \operatorname{grade}(M^{-1}H, M^{-1}g)$. Let $\bar{s}_k$
be a global solution of the reduced problem (10.1.5) with Lagrange multiplier $\lambda_k$, let
$s_k = Q_k \bar{s}_k$, and let $\kappa_k = \kappa_k(\lambda_k)$ be the condition number
(10.2.8). Then the residual $r_k = g + (H + \lambda_k M) s_k$ of (10.3.1) satisfies
$$\|r_k\|_{M^{-1}} \le 2 \|M^{-1}H\| \, \kappa_k \Delta \Bigl(\frac{\sqrt{\kappa_k} -
  1}{\sqrt{\kappa_k} + 1}\Bigr)^{k-1}.$$

The norm $\|M^{-1}H\|$ is the operator norm induced by $\|\cdot\|_M$, the norm of
`Subproblem.scaledOp H hM`. -/
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

/-- **Corollary 10.3.3** of [cartis2022evaluation] (iteration bound for the trust-region subspace
approximation). Let $H \in \mathbb{R}^{n \times n}$ be symmetric,
$M \in \mathbb{R}^{n \times n}$ positive definite, $g \neq 0$, $\Delta > 0$ and $\epsilon > 0$.
For every $1 \le k \le \operatorname{grade}(M^{-1}H, M^{-1}g)$ let $\bar{s}_k$ be a global
solution of the reduced problem (10.1.5) with Lagrange multiplier $\lambda_k$, and let
$s_k = Q_k \bar{s}_k$. Let $\kappa_*$ be the largest condition number (10.2.10) for these
multipliers. If $\kappa_* > 1$, the test (10.3.2)
$$\|g + (H + \lambda_k M) s_k\|_{M^{-1}} \le \epsilon$$
holds for some $k$ with
$$1 \le k \le \min\Bigl(\Bigl\lceil \frac{\log(2 \|M^{-1}H\| \kappa_* \Delta /
  \epsilon)}{\log((\sqrt{\kappa_*} + 1)/(\sqrt{\kappa_*} - 1))} \Bigr\rceil_+ + 1, \;
  \operatorname{grade}(M^{-1}H, M^{-1}g)\Bigr).$$
If $\kappa_* = 1$, it holds for some $1 \le k \le \min(2, \operatorname{grade}(M^{-1}H,
M^{-1}g))$.

**Correction.** The source prints the bound $\lceil \log(2 \|M^{-1}H\| \kappa_* \Delta /
\epsilon) / \log((\sqrt{\kappa_*} + 1)/(\sqrt{\kappa_*} - 1)) \rceil + 1$. The bound can be
below $1$ for a sufficiently large $\epsilon$ and is undefined for $\kappa_* = 1$.
Here the ceiling is
$\lceil x \rceil_+ = \max(\lceil x \rceil, 0)$, the case $\kappa_* = 1$ is stated separately,
and the hypothesis $g \neq 0$, which the proof needs, is added.

The norm $\|M^{-1}H\|$ is the operator norm induced by $\|\cdot\|_M$. The logarithm is
`Real.log`. -/
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
  rwa [convFactor_def, one_div_div] at this

/-- Let $\gamma, \rho, \Delta, \lambda, s \in \mathbb{R}$ with $\lambda \ge 0$,
$\gamma + (\rho + \lambda) s = 0$, $\rho + \lambda > 0$, $\lambda (|s| - \Delta) = 0$ and
$|s| \le \Delta$. Then $s$ is the unique global minimizer of $\gamma u + \frac12 \rho u^2$ over
$|u| \le \Delta$. -/
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

/-- **Section 10.3** of [cartis2022evaluation], end of the section: the start of the trust-region
Lanczos process. For $k = 1$ the reduced problem (10.1.5) is
$$\min \bigl\{ \gamma_1 s + \tfrac12 \rho_1 s^2 : |s| \le \Delta \bigr\}.$$
Let $\gamma_1, \rho_1 \in \mathbb{R}$ with $\gamma_1 \neq 0$, and let $\Delta > 0$. Call
$\lambda_1$ a multiplier of $\bar{s}_1$ if $\lambda_1 \ge 0$,
$\gamma_1 + (\rho_1 + \lambda_1) \bar{s}_1 = 0$, $\rho_1 + \lambda_1 > 0$ and
$\lambda_1 (|\bar{s}_1| - \Delta) = 0$.

1. If $\rho_1 > 0$ and $|\gamma_1/\rho_1| \le \Delta$, the unique global solution is
   $\bar{s}_1 = -\gamma_1/\rho_1$, and $\lambda_1 = 0$ is a multiplier of it.
2. Otherwise the unique global solution is $\bar{s}_1 = -(\gamma_1/|\gamma_1|) \Delta$, and
   $\lambda_1 = -\rho_1 + |\gamma_1|/\Delta > 0$ is a multiplier of it. -/
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
