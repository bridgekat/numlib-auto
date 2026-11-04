/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.ConnGouldToint.Chapter15.Section03
import NumlibSurface.ConnGouldToint.Chapter15.Section04

/-! # Full and partial SQP corrections

The small-step estimates expose the Taylor remainders and uniform
bounds used in the proof. The fast rate is stated for a trapped run
whose multiplier estimates converge. The second-order result requires
that the run eventually remain in every neighborhood of its finite
cluster set, as follows for a relatively compact run.
-/

open Filter Topology Asymptotics
open scoped RealInnerProductSpace

namespace ConnGouldToint.Chapter15

variable {E Z : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]

omit [InnerProductSpace ℝ E] in
/-- Lemma 15.4.13. The full-correction estimate from Lemma 15.3.6
is little-o in the squared step length when the joint error vanishes
and the primal error is comparable to the standard step length. -/
theorem lemma_15_4_13 (m φ e ex : ℕ → ℝ) (s : ℕ → E) {C K : ℝ}
    (hC : 0 ≤ C) (hex : ∀ k, 0 ≤ ex k) (he : ∀ k, 0 ≤ e k)
    (hlim : Tendsto e atTop (𝓝 0))
    (hstep : ∀ᶠ k in atTop, ex k ≤ K * ‖s k‖)
    (herr : ∀ᶠ k in atTop, |φ k - m k| ≤ C * (ex k ^ 2 * e k)) :
    ∀ ε > 0, ∀ᶠ k in atTop, |φ k - m k| ≤ ε * ‖s k‖ ^ 2 := by
  intro ε hε
  have hsmall : ∀ᶠ k in atTop, C * K ^ 2 * e k < ε := by
    have h : Tendsto (fun k => C * K ^ 2 * e k) atTop (𝓝 0) := by
      simpa only [mul_zero] using hlim.const_mul (C * K ^ 2)
    exact h.eventually (gt_mem_nhds hε)
  filter_upwards [hstep, herr, hsmall] with k hk herror hsmall
  refine herror.trans ?_
  calc
    _ ≤ C * ((K * ‖s k‖) ^ 2 * e k) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hex k) hk 2) (he k)) hC
    _ = (C * K ^ 2 * e k) * ‖s k‖ ^ 2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hsmall.le (sq_nonneg _)

/-- Lemma 15.4.14. The two partial-correction KKT systems cancel
the leading linear objective term. The remaining error comes from
the two Taylor remainders, the multiplier mismatch, and the corrected
constraint residual. This bound is little-o in the squared step
length when the respective coefficients tend to zero. -/
theorem lemma_15_4_14 (g u v : E) (H : E →L[ℝ] E) (A : E →L[ℝ] Z)
    (cs cz y yPC : Z) (m f₁ f₂ : ℝ) {σ r B L T R : ℝ}
    (hσ : 0 ≤ σ) (hH : H.toLinearMap.IsSymmetric)
    (hpartial : ∃ ell : Z, (∀ w, ⟪H u, w⟫ = ⟪ell, A w⟫) ∧ A u = -cs)
    (hcomp : (∀ w, ⟪g + H v, w⟫ = ⟪yPC, A w⟫) ∧ A v = 0)
    (hres : ‖cs‖ ≤ B * r ^ 2) (hcorr : ‖cz‖ ≤ R * r ^ 2)
    (hmodel : |f₁ - ⟪y, cs⟫ - m| ≤ L * r ^ 2)
    (hTaylor : |f₂ - f₁ - ⟪g, u⟫| ≤ T * r ^ 2) :
    |f₂ + σ * ‖cz‖ - m| ≤ (L + T + B * ‖y - yPC‖ + σ * R) * r ^ 2 := by
  obtain ⟨ell, hu, hAu⟩ := hpartial
  have hzero : ⟪H v, u⟫ = 0 := by
    have hs : ⟪H v, u⟫ = ⟪H u, v⟫ := (hH v u).trans (real_inner_comm (H u) v)
    rw [hs, hu, hcomp.2, inner_zero_right]
  have hstat := hcomp.1 u
  rw [inner_add_left, hzero, add_zero, hAu, inner_neg_right] at hstat
  have hinner : |⟪y - yPC, cs⟫| ≤ ‖y - yPC‖ * (B * r ^ 2) :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hres (norm_nonneg _))
  rw [show f₂ + σ * ‖cz‖ - m =
    (f₁ - ⟪y, cs⟫ - m) + (f₂ - f₁ - ⟪g, u⟫) + ⟪y - yPC, cs⟫ + σ * ‖cz‖ by
      rw [inner_sub_left, hstat]
      ring]
  have hp : |σ * ‖cz‖| ≤ σ * (R * r ^ 2) := by
    rw [abs_of_nonneg (mul_nonneg hσ (norm_nonneg _))]
    exact mul_le_mul_of_nonneg_left hcorr hσ
  exact ((abs_add_le _ _).trans (add_le_add
    ((abs_add_le _ _).trans (add_le_add
      ((abs_add_le _ _).trans (add_le_add hmodel hTaylor)) hinner)) hp)).trans_eq (by ring)

omit [InnerProductSpace ℝ E] in
/-- Theorem 15.4.15, local rate for the full-correction algorithm.
The standard-step estimates apply when a sufficiently late iterate
lies in the local neighborhood. The accepted successor is the SQP
trial or its full correction. A late entry into the neighborhood
and convergence of the multiplier estimates suffice to trap the tail. -/
theorem theorem_15_4_15 (x s u : ℕ → E) (xstar : E) (ey : ℕ → ℝ)
    {M D r : ℝ} (hM : 0 ≤ M) (hD : 0 ≤ D) (hr : 0 < r)
    (hey : ∀ k, 0 ≤ ey k) (hylim : Tendsto ey atTop (𝓝 0))
    (hvisit : ∃ᶠ k in atTop, ‖x k - xstar‖ < r)
    (hlocal : ∀ᶠ k in atTop, ‖x k - xstar‖ < r →
      (x (k + 1) = x k + s k ∨ x (k + 1) = x k + s k + u k) ∧
      ‖x k + s k - xstar‖ ≤ M * (‖x k - xstar‖ + ey k) * ‖x k - xstar‖ ∧
      ‖u k‖ ≤ D * (‖x k - xstar‖ + ey k) * ‖x k - xstar‖)
    (hsmall : (M + D) * (r + r) ≤ 1 / 2) :
    Chapter03.ConvergesQSuperlinearly x xstar ∧
      ((∃ C ≥ 0, ∀ᶠ k in atTop, ey k ≤ C * ‖x k - xstar‖) →
        Chapter03.ConvergesQQuadratically x xstar) := by
  let e (k : ℕ) := ‖x k - xstar‖
  have hrec : ∀ᶠ k in atTop, e k < r → e (k + 1) ≤ (M + D) * (e k + ey k) * e k := by
    filter_upwards [hlocal] with k hk
    intro h
    obtain ⟨hstep, hmain, hcor⟩ := hk h
    rcases hstep with hstep | hstep
    · dsimp [e]
      rw [hstep]
      refine hmain.trans ?_
      have hd : 0 ≤ D * (‖x k - xstar‖ + ey k) * ‖x k - xstar‖ := by
        exact mul_nonneg (mul_nonneg hD (add_nonneg (norm_nonneg _) (hey k))) (norm_nonneg _)
      linarith only [hd]
    · dsimp [e]
      rw [hstep, show x k + s k + u k - xstar = (x k + s k - xstar) + u k by abel]
      exact (norm_add_le _ _).trans (by linarith only [hmain, hcor])
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hrec.and (hylim.eventually_lt_const hr))
  obtain ⟨J, hJ, hentry⟩ := frequently_atTop.mp hvisit N
  have hhalf (k : ℕ) (hk : J ≤ k) (hne : e k < r) : e (k + 1) ≤ (1 / 2) * e k := by
    obtain ⟨hstep, hy⟩ := hN k (hJ.trans hk)
    have hcoef := (mul_le_mul_of_nonneg_left (add_le_add hne.le hy.le) (add_nonneg hM hD)).trans hsmall
    exact (hstep hne).trans (mul_le_mul_of_nonneg_right hcoef (norm_nonneg _))
  have hstay (k : ℕ) (hk : J ≤ k) : e k < r := by
    induction k, hk using Nat.le_induction with
    | base => exact hentry
    | succ k hk ih =>
      exact (hhalf k hk ih).trans_lt (by linarith only [ih, show 0 ≤ e k from norm_nonneg _])
  have hgeom (j : ℕ) : e (J + j) ≤ (1 / 2 : ℝ) ^ j * e J := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Nat.add_succ, pow_succ]
      have hk : J ≤ J + j := Nat.le_add_right _ _
      exact (hhalf _ hk (hstay _ hk)).trans
        ((mul_le_mul_of_nonneg_left ih (by norm_num)).trans_eq (by ring))
  have hlim : Tendsto x atTop (𝓝 xstar) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have hshift : Tendsto (fun j => e (J + j)) atTop (𝓝 0) := by
      refine squeeze_zero (fun _ => norm_nonneg _) hgeom ?_
      simpa only [zero_mul] using
        (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)).mul_const (e J)
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨I, hI⟩ := Metric.tendsto_atTop.mp hshift ε hε
    refine ⟨J + I, fun k hk => ?_⟩
    have h := hI (k - J) (by omega)
    rwa [Nat.add_sub_of_le (by omega : J ≤ k)] at h
  have hrates : ∀ᶠ k in atTop, e (k + 1) ≤ (M + D) * (e k + ey k) * e k := by
    filter_upwards [hrec, eventually_ge_atTop J] with k hk hj
    exact hk (hstay k hj)
  refine ⟨⟨hlim, IsLittleO.of_bound fun ε hε => ?_⟩, fun hq => ?_⟩
  · have hlim' : Tendsto e atTop (𝓝 0) := tendsto_iff_norm_sub_tendsto_zero.mp hlim
    have hcoeff : Tendsto (fun k => (M + D) * (e k + ey k)) atTop (𝓝 0) := by
      simpa only [zero_add, mul_zero] using (hlim'.add hylim).const_mul (M + D)
    filter_upwards [hrates, hcoeff.eventually_lt_const hε] with k hk hc
    exact hk.trans (mul_le_mul_of_nonneg_right hc.le (norm_nonneg _))
  · obtain ⟨C, hC, hrate⟩ := hq
    refine ⟨hlim, (M + D) * (1 + C), ?_⟩
    filter_upwards [hrates, hrate] with k hk hc
    refine hk.trans ?_
    change ey k ≤ C * e k at hc
    calc
      _ ≤ (M + D) * (e k + C * e k) * e k :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (add_le_add le_rfl hc) (add_nonneg hM hD))
          (show 0 ≤ e k from norm_nonneg _)
      _ = (M + D) * (1 + C) * e k ^ 2 := by ring


/-- Relative compactness supplies the cluster-set coverage needed by
Theorem 15.4.16. Only continuity of the reduced curvature at the
cluster points is needed. -/
theorem sqp_curvature_tail_of_compact {X ι : Type*} [TopologicalSpace X]
    (z : ℕ → X) (zstar : ι → X) (curvature : X → ℝ) {U : Set X}
    (hU : IsCompact U) (hmem : ∀ᶠ k in atTop, z k ∈ U)
    (hcluster : ∀ x ∈ U, MapClusterPt x atTop z → x ∈ Set.range zstar)
    (hcont : ∀ i, ContinuousAt curvature (zstar i)) (a : ℝ)
    (ha : ∀ i, curvature (zstar i) < a) :
    ∀ᶠ k in atTop, curvature (z k) ≤ a := by
  have ht := hU.tendsto_nhdsSet_of_mapClusterPt hmem hcluster
  have hn : {x | curvature x < a} ∈ 𝓝ˢ (Set.range zstar) := by
    rw [mem_nhdsSet_iff_forall]
    rintro _ ⟨i, rfl⟩
    exact (hcont i).eventually (gt_mem_nhds (ha i))
  exact (ht.eventually hn).mono (fun _ h => h.le)

omit [InnerProductSpace ℝ E] in
/-- If the coefficient in the partial-correction bound tends to zero,
the accepted corrected merit agrees with the model to little-o of
the squared step length, as in (15.4.84). -/
theorem sqp_partialCorrection_eventually_small_error (φ m coeff : ℕ → ℝ) (s : ℕ → E)
    (hcoeff : Tendsto coeff atTop (𝓝 0))
    (herr : ∀ᶠ k in atTop, |φ k - m k| ≤ coeff k * ‖s k‖ ^ 2) :
    ∀ ε > 0, ∀ᶠ k in atTop, |φ k - m k| ≤ ε * ‖s k‖ ^ 2 := by
  intro ε hε
  filter_upwards [herr, hcoeff.eventually_lt_const hε] with k hk hc
  exact hk.trans (mul_le_mul_of_nonneg_right hc.le (sq_nonneg _))

end ConnGouldToint.Chapter15
