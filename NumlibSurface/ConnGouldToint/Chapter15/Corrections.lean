/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.ConnGouldToint.Chapter15.Section03
import NumlibSurface.ConnGouldToint.Chapter15.Section04

/-!
# Conn, Gould and Toint, Section 15.4: Full and partial second-order corrections

This module formalizes the local estimates of Section 15.4 of [conn2000trust] for SQP iterations
with second-order corrections. A full correction or a partial correction is added to an SQP trial
step $s_k$ when the trial alone fails the merit test. Lemmas 15.4.13 and 15.4.14 show that the merit
value at the corrected trial agrees with the model value up to $o(\|s_k\|^2)$, for the full and for
the partial correction. Theorem 15.4.15 shows that a run whose accepted step is eventually the SQP
trial or its full correction, and whose multiplier estimates converge, converges Q-superlinearly,
and Q-quadratically when the multiplier error is of the order of the primal error. A last result
supplies the tail hypothesis of Theorem 15.4.16 for a run that eventually stays in a compact set.
The estimates take the Taylor and residual bounds of the proofs as hypotheses, in the quantitative
form of `NumlibSurface.ConnGouldToint.Chapter15.Section03`.

## Main results

* Lemma 15.4.13, `ConnGouldToint.Chapter15.lemma_15_4_13`: a merit error of order (primal
  error)$^2 \times$ (joint error) is $o(\|s_k\|^2)$ when the joint error tends to zero and the
  primal error is $O(\|s_k\|)$.
* Lemma 15.4.14, `ConnGouldToint.Chapter15.lemma_15_4_14`: the merit error at a partial correction
  is at most $(L + T + B\|y - y^{PC}\| + \sigma R) r^2$.
* Lemma 15.4.14 and equation (15.4.84),
  `ConnGouldToint.Chapter15.sqp_partialCorrection_eventually_small_error`: a bound $c_k \|s_k\|^2$
  with $c_k \to 0$ is $o(\|s_k\|^2)$.
* Theorem 15.4.15, `ConnGouldToint.Chapter15.theorem_15_4_15`: Q-superlinear convergence, and
  Q-quadratic convergence when the multiplier error is $O(\|x_k - x_*\|)$.
* Proof of Theorem 15.4.16, `ConnGouldToint.Chapter15.sqp_curvature_tail_of_compact`: a function
  that is continuous at the cluster points and below $a$ there is eventually at most $a$ along a run
  that eventually stays in a compact set.

## Implementation notes

* The sequences of merit values, model values and errors are real sequences indexed by `ℕ`. Their
  relation to an algorithm run is not part of the statements. The convergence rates are
  `ConnGouldToint.Chapter03.ConvergesQSuperlinearly` and
  `ConnGouldToint.Chapter03.ConvergesQQuadratically`.
* `ConnGouldToint.Chapter15.sqp_curvature_tail_of_compact` gives the hypothesis of
  `ConnGouldToint.Chapter15.theorem_15_4_16` that the run is eventually controlled by its cluster
  set. Only continuity of the curvature at the cluster points is needed.

## Deviations from the source

* **Explicit rate hypotheses.** Lemma 15.4.13 exposes the step-to-error and full-correction bounds
  needed for the asymptotic estimate. See `ConnGouldToint.Chapter15.lemma_15_4_13`.
* **Explicit correction estimates.** Lemma 15.4.14 and its asymptotic form give explicit Taylor and
  multiplier-gap bounds for the two corrections. See `ConnGouldToint.Chapter15.lemma_15_4_14`,
  `ConnGouldToint.Chapter15.sqp_partialCorrection_eventually_small_error`.
* **Explicit trapping and local bounds.** Theorem 15.4.15 makes late visits, trapping, accepted
  standard steps or corrections, and local error bounds explicit. See
  `ConnGouldToint.Chapter15.theorem_15_4_15`.
* **Compactness repair.** The proof of Theorem 15.4.16 uses compactness and continuity explicitly to
  pass from cluster neighborhoods to a tail estimate. See
  `ConnGouldToint.Chapter15.sqp_curvature_tail_of_compact`.
* **Lemma 15.4.13** (reading). The bound of Lemma 15.3.6 and the comparison of the primal error with
  the step length are explicit hypotheses. See `ConnGouldToint.Chapter15.lemma_15_4_13`.
* **Lemma 15.4.14** (reading). The two Taylor remainders, the residual bounds and the two correction
  systems are explicit hypotheses. See `ConnGouldToint.Chapter15.lemma_15_4_14`.
* **Theorem 15.4.15** (reading). The theorem is stated for a run that enters a small neighborhood
  late enough, whose accepted step there is the SQP trial or its full correction with explicit
  standard-step estimates, and whose multiplier estimates converge. See
  `ConnGouldToint.Chapter15.theorem_15_4_15`.
-/

open Filter Topology Asymptotics
open scoped RealInnerProductSpace

namespace ConnGouldToint.Chapter15

variable {E Z : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]

omit [InnerProductSpace ℝ E] in
/-- **Lemma 15.4.13** of [conn2000trust]. Let $(s_k)$ be a sequence in a normed group $E$, and let
$(\varphi_k)$, $(m_k)$, $(e_k)$ and $(e^x_k)$ be real sequences with $e_k \ge 0$, $e^x_k \ge 0$
and $e_k \to 0$. Let $C \ge 0$ and $K$ be real numbers. Suppose that for all sufficiently large
$k$,
$$e^x_k \le K \|s_k\| \quad \text{and} \quad |\varphi_k - m_k| \le C (e^x_k)^2 e_k.$$
Then for every $\varepsilon > 0$ and all sufficiently large $k$,
$|\varphi_k - m_k| \le \varepsilon \|s_k\|^2$.

**Reading.** The statement isolates the asymptotic step of the source. The full-correction
estimate of Lemma 15.3.6 and the comparison of the primal error with the step length enter as
hypotheses.

In the application, $\varphi_k$ is the merit value at the fully corrected trial, $m_k$ the model
value, $e^x_k$ the primal error and $e_k$ the joint primal-dual error. The second bound is the
conclusion of `ConnGouldToint.Chapter15.lemma_15_3_6`.

**Reading.** The estimate uses an explicit comparison of primal error with step length and a
quantitative full-correction error bound before taking the little-o limit.
-/
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

/-- **Lemma 15.4.14** of [conn2000trust]. Let $E$ and $Z$ be real inner product spaces, let
$H : E \to E$ be a symmetric continuous linear map and $A : E \to Z$ a continuous linear map.
Let $g, u, v \in E$, $c_s, c_z, y, y^{PC} \in Z$, and let $m, f_1, f_2, \sigma, r, B, L, T, R$
be real numbers with $\sigma \ge 0$. Suppose that $u$ solves the partial-correction system and
$v$ solves the composite system:
$$Hu = A^* \ell, \quad Au = -c_s \quad \text{for some } \ell \in Z, \qquad g + Hv = A^* y^{PC},
  \quad Av = 0.$$
Suppose also that
$$\|c_s\| \le B r^2, \quad \|c_z\| \le R r^2, \quad |f_1 - \langle y, c_s\rangle - m| \le L r^2,
  \quad |f_2 - f_1 - \langle g, u\rangle| \le T r^2.$$
Then
$$|f_2 + \sigma \|c_z\| - m| \le (L + T + B \|y - y^{PC}\| + \sigma R)\, r^2.$$

**Reading.** The two Taylor remainders, the residual bounds and the two correction systems of
the proof are explicit hypotheses.

The two systems cancel the linear term $\langle g, u\rangle$ up to the multiplier mismatch
$\|y - y^{PC}\|$. In the application, $f_2 + \sigma\|c_z\|$ is the merit value at the partially
corrected trial, $m$ is the model value and $r$ is the step length, so the bound is $o(r^2)$
when the coefficients tend to zero. The adjoint equations are stated weakly:
$\langle Hu, w\rangle = \langle \ell, Aw\rangle$ and $\langle g + Hv, w\rangle = \langle y^{PC},
Aw\rangle$ for all $w \in E$.

**Correction.** The partial and full correction systems, Taylor residual bounds, and multiplier-gap
coefficient are explicit. A separate asymptotic result makes the estimate arbitrarily small as that
coefficient tends to zero.
-/
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
/-- **Theorem 15.4.15** of [conn2000trust]. Let $(x_k)$, $(s_k)$ and $(u_k)$ be sequences in a
normed group $E$, let $x_* \in E$, and let $(e^y_k)$ be a sequence of nonnegative reals with
$e^y_k \to 0$. Let $M, D \ge 0$ and $r > 0$ satisfy $2r(M + D) \le 1/2$. Suppose that
$\|x_k - x_*\| < r$ for infinitely many $k$, and that for all sufficiently large $k$ with
$\|x_k - x_*\| < r$:

* $x_{k+1} = x_k + s_k$ or $x_{k+1} = x_k + s_k + u_k$;
* $\|x_k + s_k - x_*\| \le M (\|x_k - x_*\| + e^y_k) \|x_k - x_*\|$;
* $\|u_k\| \le D (\|x_k - x_*\| + e^y_k) \|x_k - x_*\|$.

Then $x_k \to x_*$ Q-superlinearly. If moreover there is $C \ge 0$ with
$e^y_k \le C \|x_k - x_*\|$ for all sufficiently large $k$, then $x_k \to x_*$ Q-quadratically.

**Reading.** The source states the local rate for the algorithm with full corrections. Here the
standing local assumptions are explicit: the run enters the neighborhood late enough, the
accepted step there is the SQP trial or its full correction, the trial and the correction
satisfy the standard-step estimates, and the multiplier errors converge. These conditions trap
the tail of the run in the neighborhood.

The sequence $s_k$ is the SQP trial step, $u_k$ the full correction and $e^y_k$ the multiplier
error. The rates are `ConnGouldToint.Chapter03.ConvergesQSuperlinearly` and
`ConnGouldToint.Chapter03.ConvergesQQuadratically`.

**Reading.** The theorem assumes arbitrarily late neighborhood visits, trapping and eventual
acceptance of the standard step or full correction. The multiplier gap tends to zero, with separate
rate bounds for the quadratic conclusion.
-/
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
    have hcoef := (mul_le_mul_of_nonneg_left (add_le_add hne.le hy.le) (add_nonneg hM hD)).trans
      hsmall
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
        (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
          (by norm_num)).mul_const (e J)
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


/-- A compactness lemma for the proof of Theorem 15.4.16 of [conn2000trust]. Let $X$ be a
topological space, $(z_k)$ a sequence in $X$, $(z^*_i)_{i \in \iota}$ a family of points of $X$
and $\kappa : X \to \mathbb{R}$. Suppose that $z_k$ lies in a compact set $U$ for all
sufficiently large $k$, that every cluster point of $(z_k)$ in $U$ is one of the points $z^*_i$,
that $\kappa$ is continuous at each $z^*_i$, and that $\kappa(z^*_i) < a$ for all $i$. Then
$\kappa(z_k) \le a$ for all sufficiently large $k$.

This gives the tail hypothesis of `ConnGouldToint.Chapter15.theorem_15_4_16` for a relatively
compact run. Only continuity of the reduced curvature at the cluster points is needed.

**Reading.** Compactness, continuity and the local cluster-neighborhood estimates are explicit
hypotheses for obtaining the uniform tail bound.
-/
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
/-- **Lemma 15.4.14** of [conn2000trust], asymptotic form, as in (15.4.84). Let $(s_k)$ be a
sequence in a normed group $E$, and let $(\varphi_k)$, $(m_k)$ and $(c_k)$ be real sequences
with $c_k \to 0$. If $|\varphi_k - m_k| \le c_k \|s_k\|^2$ for all sufficiently large $k$, then
for every $\varepsilon > 0$ and all sufficiently large $k$,
$|\varphi_k - m_k| \le \varepsilon \|s_k\|^2$.

In the application, $\varphi_k$ is the merit value at the accepted partially corrected trial,
$m_k$ the model value, and $c_k$ the coefficient of `ConnGouldToint.Chapter15.lemma_15_4_14`.

**Correction.** The partial and full correction systems, Taylor residual bounds, and multiplier-gap
coefficient are explicit. A separate asymptotic result makes the estimate arbitrarily small as that
coefficient tends to zero.
-/
theorem sqp_partialCorrection_eventually_small_error (φ m coeff : ℕ → ℝ) (s : ℕ → E)
    (hcoeff : Tendsto coeff atTop (𝓝 0))
    (herr : ∀ᶠ k in atTop, |φ k - m k| ≤ coeff k * ‖s k‖ ^ 2) :
    ∀ ε > 0, ∀ᶠ k in atTop, |φ k - m k| ≤ ε * ‖s k‖ ^ 2 := by
  intro ε hε
  filter_upwards [herr, hcoeff.eventually_lt_const hε] with k hk hc
  exact hk.trans (mul_le_mul_of_nonneg_right hc.le (sq_nonneg _))

end ConnGouldToint.Chapter15
