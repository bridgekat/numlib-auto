/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.CartisGouldToint.Chapter11.Section01

/-!
# Cartis, Gould and Toint, Section 11.2: Trust-region radius and regularization weight updates

This module formalizes §11.2 of [cartis2022evaluation]: the asymptotic correspondence between the
trust-region radius $\Delta$ and the regularization weight $\sigma$. Let $H$ be symmetric and $M$
positive definite. If $s(\Delta)$ is a step of the trust-region subproblem (8.1.2) with Lagrange
multiplier $\lambda(\Delta)$, then $\lambda(\Delta) \Delta \to \|g\|_{M^{-1}}$ as $\Delta \to 0^+$,
that is, $\lambda \approx \|g\|_{M^{-1}} / \Delta$ (11.2.3). For the regularization subproblem
(8.1.3) of order $r > 2$, the multiplier $\lambda(\sigma) = \sigma \|s(\sigma)\|_M^{r-2}$ behaves
like $\sigma^{1/(r-1)} \|g\|_{M^{-1}}^{(r-2)/(r-1)}$ as $\sigma \to \infty$ (11.2.4).

A trust-region step with a positive multiplier $\lambda$ is a regularization step for the weight
$\sigma(\Delta) = \lambda / \Delta^{r-2}$. This weight satisfies
$\sigma \approx \|g\|_{M^{-1}} / \Delta^{r-1}$ (11.2.5), and shrinking the radius by a factor
$\gamma$ multiplies the weight by about $\gamma^{-(r-1)}$, which is the rule (11.2.6). The proofs
use the multiplier theory of Chapter 8.

## Main results

* (11.2.3), `CartisGouldToint.Chapter11.trMultiplier_asymptotics`: $|\lambda(\Delta) \Delta -
  \|g\|_{M^{-1}}| \le \|M^{-1}H\|_2 \Delta$, where $\|M^{-1}H\|_2$ is the Euclidean operator norm,
  so $\lambda(\Delta) \Delta \to \|g\|_{M^{-1}}$ as $\Delta \to 0^+$.
* (11.2.5)–(11.2.6), `CartisGouldToint.Chapter11.radius_weight_correspondence`: a trust-region step
  with multiplier $\lambda > 0$ is the regularization step for
  $\sigma(\Delta) = \lambda / \Delta^{r-2}$, $\sigma(\Delta) \Delta^{r-1} / \|g\|_{M^{-1}} \to 1$,
  and $\sigma(\gamma \Delta)/\sigma(\Delta) \to \gamma^{-(r-1)}$.
* (11.2.4), `CartisGouldToint.Chapter11.regMultiplier_asymptotics`: $\lambda(\sigma) /
  (\sigma^{1/(r-1)} \|g\|_{M^{-1}}^{(r-2)/(r-1)}) \to 1$ as $\sigma \to \infty$.

## Deviations from the source

* **(11.2.3) and (11.2.5)** (typo). Both are printed inverted. The correct forms are
  $\lambda \approx \|g\|_{M^{-1}} / \Delta$ (printed $\Delta / \|g\|_{M^{-1}}$) and
  $\sigma \approx \|g\|_{M^{-1}} / \Delta^{r-1}$ (printed $\Delta^{r-1} / \|g\|_{M^{-1}}$), as the
  derivation, the "fidelity" $\sigma \Delta^2 / \|g\|_{M^{-1}} \to 1$ of Table 11.2.1 and the rule
  (11.2.6) confirm. See `CartisGouldToint.Chapter11.trMultiplier_asymptotics` and
  `CartisGouldToint.Chapter11.radius_weight_correspondence`.

## Not formalized

* The practical update rules (11.2.1)–(11.2.2), which are parameter choices for the algorithms of
  Chapter 3.
-/

open Matrix Set Filter Topology
open scoped RealInnerProductSpace

namespace CartisGouldToint.Chapter11

open Subproblem CartisGouldToint.Chapter08 CartisGouldToint.Chapter10

variable {n : ℕ} {H M : Matrix (Fin n) (Fin n) ℝ} {g : EuclideanSpace ℝ (Fin n)}

/-- If $|f(\Delta) - L| \le C \Delta$ for every $\Delta > 0$, then $f(\Delta) \to L$ as
$\Delta \to 0^+$. -/
private theorem tendsto_of_abs_sub_le {f : ℝ → ℝ} {L C : ℝ} (h : ∀ Δ, 0 < Δ → |f Δ - L| ≤ C * Δ) :
    Tendsto f (𝓝[>] 0) (𝓝 L) := by
  have hlo : Tendsto (fun Δ => L - C * Δ) (𝓝[>] (0 : ℝ)) (𝓝 L) := by
    have : Tendsto (fun Δ : ℝ => L - C * Δ) (𝓝 0) (𝓝 (L - C * 0)) :=
      (continuous_const.sub (continuous_const.mul continuous_id)).tendsto 0
    rw [mul_zero, sub_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hhi : Tendsto (fun Δ => L + C * Δ) (𝓝[>] (0 : ℝ)) (𝓝 L) := by
    have : Tendsto (fun Δ : ℝ => L + C * Δ) (𝓝 0) (𝓝 (L + C * 0)) :=
      (continuous_const.add (continuous_const.mul continuous_id)).tendsto 0
    rw [mul_zero, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_ <;>
    filter_upwards [self_mem_nhdsWithin] with Δ hΔ <;>
    have := abs_le.1 (h Δ hΔ) <;> linarith [this.1, this.2]

/-- **Equation (11.2.3)** of [cartis2022evaluation], the trust-region multiplier for small radii.
Let $H \in \mathbb{R}^{n \times n}$ be symmetric and $M \in \mathbb{R}^{n \times n}$ positive
definite. For every $\Delta > 0$ let $s(\Delta)$ satisfy $\|s(\Delta)\|_M \le \Delta$, and let
$\lambda(\Delta)$ be a Lagrange multiplier of $s(\Delta)$ for the trust-region subproblem
(8.1.2) in the sense of Theorem 8.2.7; for example, $s(\Delta)$ can be a global solution. Then
for every $\Delta > 0$
$$\bigl|\lambda(\Delta) \Delta - \|g\|_{M^{-1}}\bigr| \le \|M^{-1}H\|_2 \, \Delta,$$
and therefore $\lambda(\Delta) \Delta \to \|g\|_{M^{-1}}$ as $\Delta \to 0^+$, that is,
$\lambda \approx \|g\|_{M^{-1}} / \Delta$.

**Typo.** The source prints $\lambda \approx \Delta / \|g\|_{M^{-1}}$, which is inverted. The
derivation in the source gives $\|g\|_{M^{-1}} / \Delta$.

The norm $\|M^{-1}H\|_2$ is the Euclidean operator norm of the matrix $M^{-1}H$. The multiplier
conditions are `CartisGouldToint.Chapter08.IsTrustRegionKKT`. -/
theorem trMultiplier_asymptotics (hH : H.IsHermitian) (hM : M.PosDef)
    {s : ℝ → EuclideanSpace ℝ (Fin n)} {lam : ℝ → ℝ}
    (hs : ∀ Δ, 0 < Δ → IsTrustRegionKKT g H M Δ (s Δ) (lam Δ) ∧ mNorm M (s Δ) ≤ Δ) :
    (∀ Δ, 0 < Δ → |lam Δ * Δ - mNorm M⁻¹ g| ≤
      ‖LinearMap.toContinuousLinearMap (toEuclideanLin (M⁻¹ * H))‖ * Δ) ∧
    Tendsto (fun Δ => lam Δ * Δ) (𝓝[>] 0) (𝓝 (mNorm M⁻¹ g)) := by
  have hA := norm_scaledOp_le (hM := hM) hH
  have hbound : ∀ Δ, 0 < Δ → |lam Δ * Δ - mNorm M⁻¹ g| ≤
      ‖LinearMap.toContinuousLinearMap (toEuclideanLin (M⁻¹ * H))‖ * Δ := by
    intro Δ hΔ
    obtain ⟨hk, hn⟩ := hs Δ hΔ
    have h := (isTrustRegionKKT_iff_scaled hM hΔ).1 hk
    rw [mNorm_eq_norm_toScaled hM] at hn
    rw [mNorm_inv_eq_norm_scaledGrad hM]
    set S := toScaled hM (s Δ)
    set b := scaledGrad hM g
    have hsh : lam Δ • S = -(b + scaledOp H hM S) := by
      have := h.shifted
      simp only [_root_.add_apply, _root_.smul_apply, one_apply_eq_self] at this
      rw [neg_add', ← this]; abel
    have hAS : ‖scaledOp H hM S‖ ≤
        ‖LinearMap.toContinuousLinearMap (toEuclideanLin (M⁻¹ * H))‖ * Δ :=
      ((scaledOp H hM).le_opNorm S).trans (mul_le_mul hA hn (norm_nonneg _) (norm_nonneg _))
    rcases eq_or_ne (lam Δ) 0 with h0 | h0
    · rw [h0, zero_smul, eq_comm, neg_eq_zero, add_eq_zero_iff_eq_neg] at hsh
      rw [h0, zero_mul, zero_sub, abs_neg, abs_of_nonneg (norm_nonneg _), hsh, norm_neg]
      exact hAS
    · have hSΔ : ‖S‖ = Δ := by
        have := h.complementarity
        have := (mul_eq_zero.1 this).resolve_left h0
        linarith
      have hl : lam Δ * Δ = ‖b + scaledOp H hM S‖ := by
        rw [show lam Δ * Δ = lam Δ * ‖S‖ by rw [hSΔ], ← Real.norm_of_nonneg h.nonneg,
          ← norm_smul, hsh, norm_neg]
      rw [hl]
      refine (abs_norm_sub_norm_le _ _).trans ?_
      rw [add_sub_cancel_left]; exact hAS
  exact ⟨hbound, tendsto_of_abs_sub_le hbound⟩

/-- **Equations (11.2.5)–(11.2.6)** of [cartis2022evaluation], the radius–weight correspondence. Let
$H \in \mathbb{R}^{n \times n}$ be symmetric, $M \in \mathbb{R}^{n \times n}$ positive definite
and $r > 2$.

1. Let $\Delta > 0$, and let $s$ with $\|s\|_M \le \Delta$ have a Lagrange multiplier
   $\lambda > 0$ for the trust-region subproblem (8.1.2). Then $s$ is a global minimizer of the
   regularization subproblem (8.1.3) with the weight $\sigma(\Delta) = \lambda / \Delta^{r-2}$
   and the order $r$. This is the converse of Theorem 8.2.8.
2. Let $g \neq 0$, and for every $\Delta > 0$ let $s(\Delta)$ and $\lambda(\Delta)$ be as in
   `CartisGouldToint.Chapter11.trMultiplier_asymptotics`, with $\sigma(\Delta) = \lambda(\Delta)
   / \Delta^{r-2}$. Then $\sigma(\Delta) \Delta^{r-1} / \|g\|_{M^{-1}} \to 1$ as
   $\Delta \to 0^+$, which is the "fidelity" of Table 11.2.1, that is,
   $\sigma \approx \|g\|_{M^{-1}} / \Delta^{r-1}$. Moreover, for every $\gamma > 0$,
   $\sigma(\gamma \Delta)/\sigma(\Delta) \to \gamma^{-(r-1)}$ as $\Delta \to 0^+$, which is the
   rule (11.2.6).

**Typo.** The source prints (11.2.5) as $\sigma \approx \Delta^{r-1} / \|g\|_{M^{-1}}$, which is
inverted. The derivation, Table 11.2.1 and the rule (11.2.6) all give
$\|g\|_{M^{-1}} / \Delta^{r-1}$. -/
theorem radius_weight_correspondence (hH : H.IsHermitian) (hM : M.PosDef) {r : ℝ} (hr : 2 < r) :
    (∀ {Δ lam : ℝ} {s : EuclideanSpace ℝ (Fin n)}, 0 < Δ → IsTrustRegionKKT g H M Δ s lam →
      mNorm M s ≤ Δ → 0 < lam → IsRegularizationSolution g H M (lam / Δ ^ (r - 2)) r s) ∧
    (g ≠ 0 → ∀ {s : ℝ → EuclideanSpace ℝ (Fin n)} {lam : ℝ → ℝ},
      (∀ Δ, 0 < Δ → IsTrustRegionKKT g H M Δ (s Δ) (lam Δ) ∧ mNorm M (s Δ) ≤ Δ) →
      Tendsto (fun Δ => lam Δ / Δ ^ (r - 2) * Δ ^ (r - 1) / mNorm M⁻¹ g) (𝓝[>] 0) (𝓝 1) ∧
      ∀ γ, 0 < γ → Tendsto (fun Δ => (lam (γ * Δ) / (γ * Δ) ^ (r - 2)) / (lam Δ / Δ ^ (r - 2)))
        (𝓝[>] 0) (𝓝 (γ ^ (-(r - 1))))) := by
  -- `λ/Δ^{r-2} · Δ^{r-1} = λ Δ`
  have hpow : ∀ Δ : ℝ, 0 < Δ → Δ ^ (r - 1) = Δ ^ (r - 2) * Δ := fun Δ hΔ => by
    rw [show r - 1 = (r - 2) + 1 by ring, Real.rpow_add hΔ, Real.rpow_one]
  have hσ : ∀ (Δ l : ℝ), 0 < Δ → l / Δ ^ (r - 2) * Δ ^ (r - 1) = l * Δ := fun Δ l hΔ => by
    rw [hpow Δ hΔ]; field_simp [(Real.rpow_pos_of_pos hΔ (r - 2)).ne']
  refine ⟨fun {Δ lam s} hΔ hk hs hl => ?_, fun hg {s lam} hs => ?_⟩
  · have hsΔ : mNorm M s = Δ := by
      have := (mul_eq_zero.1 hk.complementarity).resolve_left hl.ne'
      exact (sq_eq_sq₀ (mNorm_nonneg _ _) hΔ.le).1 (by linarith)
    have hpos := Real.rpow_pos_of_pos hΔ (r - 2)
    have hlam : lam / Δ ^ (r - 2) * mNorm M s ^ (r - 2) = lam := by
      rw [hsΔ]; field_simp
    refine isRegularizationSolution_of_shifted hH hM (div_pos hl hpos) hr ?_ ?_
    · rw [hlam]; exact hk.shifted
    · rw [hlam]; exact hk.posSemidef
  · obtain ⟨hbound, htend⟩ := trMultiplier_asymptotics hH hM hs
    have hgpos : 0 < mNorm M⁻¹ g := by
      rw [mNorm_inv_eq_norm_scaledGrad hM]; exact norm_pos_iff.2 (scaledGrad_ne_zero hg)
    constructor
    · have : Tendsto (fun Δ => lam Δ * Δ / mNorm M⁻¹ g) (𝓝[>] 0) (𝓝 1) := by
        have := htend.div_const (mNorm M⁻¹ g)
        rwa [div_self hgpos.ne'] at this
      refine this.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with Δ hΔ
      rw [hσ Δ (lam Δ) hΔ]
    · intro γ hγ
      have hγt : Tendsto (fun Δ => lam (γ * Δ) * (γ * Δ)) (𝓝[>] 0) (𝓝 (mNorm M⁻¹ g)) :=
        tendsto_of_abs_sub_le (C := ‖LinearMap.toContinuousLinearMap
          (toEuclideanLin (M⁻¹ * H))‖ * γ) fun Δ hΔ => by
          rw [mul_assoc]; exact hbound _ (mul_pos hγ hΔ)
      have hq := (hγt.div htend hgpos.ne').mul_const (γ ^ (-(r - 1)))
      rw [div_self hgpos.ne', one_mul] at hq
      refine hq.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with Δ hΔ
      have hΔ' : 0 < Δ := hΔ
      have hγΔ := mul_pos hγ hΔ'
      have e1 : lam (γ * Δ) / (γ * Δ) ^ (r - 2) =
          lam (γ * Δ) * (γ * Δ) / (γ * Δ) ^ (r - 1) := by
        rw [hpow _ hγΔ]; field_simp [(Real.rpow_pos_of_pos hγΔ (r - 2)).ne']
      have e2 : lam Δ / Δ ^ (r - 2) = lam Δ * Δ / Δ ^ (r - 1) := by
        rw [hpow _ hΔ']; field_simp [(Real.rpow_pos_of_pos hΔ' (r - 2)).ne']
      simp only [Pi.div_apply]
      rw [e1, e2, Real.mul_rpow hγ.le hΔ'.le, Real.rpow_neg hγ.le]
      have := (Real.rpow_pos_of_pos hγ (r - 1)).ne'
      have := (Real.rpow_pos_of_pos hΔ' (r - 1)).ne'
      have := hΔ'.ne'
      by_cases h0 : lam Δ = 0
      · simp [h0]
      · field_simp

/-- For $r > 2$ and $t \ge 0$, $t^{r-2} t = t^{r-1}$. -/
private theorem rpow_sub_two_mul_self {r t : ℝ} (hr : 2 < r) (ht : 0 ≤ t) :
    t ^ (r - 2) * t = t ^ (r - 1) := by
  rcases eq_or_lt_of_le ht with rfl | ht
  · rw [Real.zero_rpow (by linarith), Real.zero_rpow (by linarith), zero_mul]
  · rw [show r - 1 = (r - 2) + 1 by ring, Real.rpow_add ht, Real.rpow_one]

/-- **Equation (11.2.4)** of [cartis2022evaluation], the regularization multiplier for large
weights. Let $H \in \mathbb{R}^{n \times n}$ be symmetric, $M \in \mathbb{R}^{n \times n}$
positive definite, $g \neq 0$ and $r > 2$. For every $\sigma > 0$ let $s(\sigma)$ be a global
minimizer of the regularization subproblem (8.1.3), with the multiplier
$\lambda(\sigma) = \sigma \|s(\sigma)\|_M^{r-2}$. Then
$$\frac{\lambda(\sigma)}{\sigma^{1/(r-1)} \|g\|_{M^{-1}}^{(r-2)/(r-1)}} \to 1 \qquad \text{as }
  \sigma \to \infty.$$
-/
theorem regMultiplier_asymptotics (hH : H.IsHermitian) (hM : M.PosDef) (hg : g ≠ 0) {r : ℝ}
    (hr : 2 < r) {s : ℝ → EuclideanSpace ℝ (Fin n)}
    (hs : ∀ σ, 0 < σ → IsRegularizationSolution g H M σ r (s σ)) :
    Tendsto (fun σ => σ * mNorm M (s σ) ^ (r - 2) /
      (σ ^ (1 / (r - 1)) * mNorm M⁻¹ g ^ ((r - 2) / (r - 1)))) atTop (𝓝 1) := by
  set C := ‖scaledOp H hM‖
  set β := mNorm M⁻¹ g with hβdef
  have hβeq : β = ‖scaledGrad hM g‖ := mNorm_inv_eq_norm_scaledGrad hM g
  have hβ : 0 < β := by rw [hβeq]; exact norm_pos_iff.2 (scaledGrad_ne_zero hg)
  set t : ℝ → ℝ := fun σ => mNorm M (s σ)
  set N : ℝ → ℝ := fun σ => ‖scaledGrad hM g + scaledOp H hM (toScaled hM (s σ))‖
  have ht0 : ∀ σ, 0 ≤ t σ := fun σ => mNorm_nonneg _ _
  -- the optimality condition: `σ t^{r-1} = N` and `|N - β| ≤ C t`
  have hkey : ∀ σ, 0 < σ → σ * t σ ^ (r - 1) = N σ ∧ |N σ - β| ≤ C * t σ := by
    intro σ hσ
    have hmin := (isRegularizationSolution_iff_scaled hM).1 (hs σ hσ)
    obtain ⟨h1, -⟩ := (isMinOn_regModel_iff (isSymmetric_scaledOp hH) hσ hr).1 hmin
    set S := toScaled hM (s σ)
    have htS : t σ = ‖S‖ := mNorm_eq_norm_toScaled hM _
    simp only [_root_.add_apply, _root_.smul_apply, one_apply_eq_self] at h1
    have hsh : (σ * ‖S‖ ^ (r - 2)) • S = -(scaledGrad hM g + scaledOp H hM S) := by
      rw [neg_add', ← h1]; abel
    constructor
    · have := congrArg norm hsh
      rw [norm_neg, norm_smul, Real.norm_of_nonneg (by positivity)] at this
      rw [htS, ← rpow_sub_two_mul_self hr (norm_nonneg _), ← mul_assoc]
      exact this
    · rw [hβeq, htS]
      refine (abs_norm_sub_norm_le _ _).trans ?_
      rw [add_sub_cancel_left]
      exact (scaledOp H hM).le_opNorm S
  -- `t → 0`
  have htend : Tendsto t atTop (𝓝 0) := by
    have hp : 0 < 1 / (r - 1) := by apply div_pos one_pos; linarith
    have hbnd : ∀ σ, C + β < σ → t σ ≤ (β + C) ^ (1 / (r - 1)) * σ ^ (-(1 / (r - 1))) := by
      intro σ hσ
      have hσ0 : 0 < σ := by have := norm_nonneg (scaledOp H hM); linarith
      obtain ⟨h1, h2⟩ := hkey σ hσ0
      have hN : N σ ≤ β + C * t σ := by have := (abs_le.1 h2).2; linarith
      have ht1 : t σ < 1 := by
        by_contra hge
        push Not at hge
        have hpow : t σ ≤ t σ ^ (r - 1) := by
          conv_lhs => rw [← Real.rpow_one (t σ)]
          exact Real.rpow_le_rpow_of_exponent_le hge (by linarith)
        have : σ * t σ ≤ β + C * t σ := by nlinarith
        nlinarith [norm_nonneg (scaledOp H hM)]
      have hC0 : 0 ≤ C := norm_nonneg _
      have htp : t σ ^ (r - 1) ≤ (β + C) / σ := by
        rw [le_div_iff₀ hσ0]; nlinarith [ht0 σ]
      have := Real.rpow_le_rpow (Real.rpow_nonneg (ht0 σ) _) htp hp.le
      rw [← Real.rpow_mul (ht0 σ), mul_one_div_cancel (by linarith), Real.rpow_one,
        Real.div_rpow (by linarith) hσ0.le, div_eq_mul_inv, ← Real.rpow_neg hσ0.le] at this
      exact this
    have hlim : Tendsto (fun σ : ℝ => (β + C) ^ (1 / (r - 1)) * σ ^ (-(1 / (r - 1)))) atTop
        (𝓝 0) := by
      simpa using (tendsto_rpow_neg_atTop hp).const_mul ((β + C) ^ (1 / (r - 1)))
    refine squeeze_zero' (Eventually.of_forall ht0) ?_ hlim
    filter_upwards [eventually_gt_atTop (C + β)] with σ hσ using hbnd σ hσ
  -- `N → β`
  have hNt : Tendsto N atTop (𝓝 β) := by
    have hlo : Tendsto (fun σ => β - C * t σ) atTop (𝓝 β) := by
      simpa using tendsto_const_nhds.sub (htend.const_mul C)
    have hhi : Tendsto (fun σ => β + C * t σ) atTop (𝓝 β) := by
      simpa using tendsto_const_nhds.add (htend.const_mul C)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_ <;>
      filter_upwards [eventually_gt_atTop 0] with σ hσ <;>
      have := abs_le.1 (hkey σ hσ).2 <;> linarith [this.1, this.2]
  -- the ratio is `(N/β)^{(r-2)/(r-1)}`
  set q := (r - 2) / (r - 1)
  have hlim : Tendsto (fun σ => N σ ^ q / β ^ q) atTop (𝓝 1) := by
    have := ((Real.continuousAt_rpow_const β q (Or.inl hβ.ne')).tendsto.comp hNt).div_const
      (β ^ q)
    rwa [div_self (Real.rpow_pos_of_pos hβ q).ne'] at this
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with σ hσ
  have hr1 : r - 1 ≠ 0 := by linarith
  have hNq : N σ ^ q = σ ^ q * t σ ^ (r - 2) := by
    rw [← (hkey σ hσ).1, Real.mul_rpow hσ.le (Real.rpow_nonneg (ht0 σ) _),
      ← Real.rpow_mul (ht0 σ)]
    congr 2; simp only [q]; field_simp
  have hσq : σ ^ q * σ ^ (1 / (r - 1)) = σ := by
    rw [← Real.rpow_add hσ, show q + 1 / (r - 1) = 1 by simp only [q]; field_simp; ring,
      Real.rpow_one]
  have hσp := (Real.rpow_pos_of_pos hσ (1 / (r - 1))).ne'
  have hβq := (Real.rpow_pos_of_pos hβ q).ne'
  change N σ ^ q / β ^ q = σ * t σ ^ (r - 2) / (σ ^ (1 / (r - 1)) * β ^ q)
  rw [hNq, div_eq_div_iff hβq (mul_ne_zero hσp hβq)]
  linear_combination (t σ ^ (r - 2) * β ^ q) * hσq

end CartisGouldToint.Chapter11
