/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.ConnGouldToint.Chapter09.Section01
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# Conn, Gould and Toint, Section 9.3: Convergence to second-order critical points

This module formalizes the second-order theory of conditional models in Section 9.3 of
[conn2000trust]. A model $m$ of $f$ is **second-order valid** on the ball $B(x, \delta)$ if it is
valid in the sense of Section 9.1 with a constant $\kappa_1$ and also satisfies
$|f(z) - m(z)| \le \kappa_2 \delta^3$ on the ball (9.3.1). For a positive radius, second-order
validity gives a Hessian error of order $\delta$ at the center (Theorem 9.3.1), so the model
Hessians approach the objective Hessians when the radii tend to zero (Corollary 9.3.2). Theorem
9.3.3 shows that a point where the model gradients and the negative model curvature are controlled
by a vanishing sequence is a second-order critical point of $f$. The criticality test of Algorithm
9.3.1 combines the model gradient with the negative model curvature. The infinite refinement loop of
the corrected algorithm supplies the hypotheses of Theorem 9.3.3.

The Hessian $\nabla^2 f(x)$ is the bilinear map $(u, v) \mapsto \nabla^2 f(x)[u, v]$, and the third
derivative is $\nabla^3 f$. The validity condition of Section 9.1 is
`ConnGouldToint.Chapter09.modelValidOnBall` from `NumlibSurface.ConnGouldToint.Chapter09.Section01`.

## Main definitions

* Equation (9.3.1), `ConnGouldToint.Chapter09.modelSecondOrderValidOnBall`: validity together with
  the error bound $\kappa_2 \delta^3$ on the ball.
* Algorithm 9.3.1, `ConnGouldToint.Chapter09.secondOrderModelCriticality`: the criticality measure
  $\max\{\|\nabla m(x)\|, -\lambda\}$ for a curvature lower bound $\lambda$.
* Algorithm 9.3.1, `ConnGouldToint.Chapter09.secondOrderModelPasses`: the model is second-order
  valid on a ball of positive radius at most $\mu$ times the criticality measure.
* Algorithm 9.3.1, `ConnGouldToint.Chapter09.secondOrderRefinementRadius`: the next radius in the
  refinement loop, which stays positive at zero model criticality.
* Algorithm 9.3.1, `ConnGouldToint.Chapter09.SecondOrderModelRefinement`: an infinite trace of the
  refinement loop in which every test fails.

## Main results

* Theorem 9.3.1, `ConnGouldToint.Chapter09.theorem_9_3_1_of_hessian_lipschitz`: under Lipschitz
  bounds on the Hessians at the center, second-order validity gives a Hessian error of order
  $\delta$.
* Theorem 9.3.1, `ConnGouldToint.Chapter09.theorem_9_3_1`: the same bound under bounds on the third
  derivatives.
* `ConnGouldToint.Chapter09.second_order_zero_radius_counterexample`: at radius $0$, second-order
  validity gives no bound on the Hessian error.
* Corollary 9.3.2, `ConnGouldToint.Chapter09.corollary_9_3_2`: if the model gradients tend to zero
  and the models are eventually second-order valid on balls of radius at most
  $\mu \|\nabla m_k(x_k)\|$, the Hessian errors tend to zero.
* Theorem 9.3.3, `ConnGouldToint.Chapter09.theorem_9_3_3`: the point is first-order critical and its
  Hessian is positive semidefinite.
* Algorithm 9.3.1, `ConnGouldToint.Chapter09.SecondOrderModelRefinement.tendsto_radius`: the radii
  of the refinement loop tend to zero.
* Theorem 9.3.3, `ConnGouldToint.Chapter09.theorem_9_3_3_of_refinement`: an infinite refinement loop
  ends at a second-order critical point.

## Deviations from the source

* **Theorem 9.3.1** (generalization). The Hessian estimate uses real normed spaces and a
  centered Taylor difference. The proof variant assumes a Hessian bound relative to the
  center in place of a bounded third derivative. Its constant includes the factor from
  polarization in a normed space.
* **Theorem 9.3.1** (correction). The radius of the ball must be positive. At radius $0$,
  second-order validity gives no Hessian bound. See
  `ConnGouldToint.Chapter09.second_order_zero_radius_counterexample`.
* **Equation (9.3.4)** (correction). The model curvature can stay negative at every refinement. The
  proof of Theorem 9.3.3 needs only a lower bound on the model curvature that tends to zero. See
  `ConnGouldToint.Chapter09.theorem_9_3_3`.
* **Algorithm 9.3.1** (correction). At zero model criticality the printed radius is zero. The
  corrected loop keeps refining at a positive radius, so that the derivative estimates still apply.
  See `ConnGouldToint.Chapter09.secondOrderRefinementRadius`.
-/

open Filter Topology

namespace ConnGouldToint.Chapter09

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Equation (9.3.1)** of [conn2000trust]. Let $f, m : E \to \mathbb{R}$, $x \in E$ and
$\delta, \kappa_1, \kappa_2 \in \mathbb{R}$. The model $m$ is **second-order valid** for $f$ on
$B(x, \delta)$ if it is valid on $B(x, \delta)$ with constant $\kappa_1$ (9.1.1)–(9.1.2) and
$$|f(z) - m(z)| \le \kappa_2 \delta^3 \quad \text{for all } z \text{ with } \|z - x\| \le
  \delta.$$

**Reading.** Same quadratic and cubic model error bounds on arbitrary real normed-space balls.
-/
def modelSecondOrderValidOnBall (f m : E → ℝ) (x : E) (δ κ₁ κ₂ : ℝ) : Prop :=
  modelValidOnBall f m x δ κ₁ ∧
    ∀ z ∈ Metric.closedBall x δ, |f z - m z| ≤ κ₂ * δ ^ 3

private theorem opNorm_le_of_diagonal {B : E →L[ℝ] E →L[ℝ] ℝ} {K : ℝ}
    (hK : 0 ≤ K) (hsymm : ∀ u v, B u v = B v u)
    (hdiag : ∀ u, |B u u| ≤ K * ‖u‖ ^ 2) : ‖B‖ ≤ 2 * K := by
  have hunit (u v : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) : |B u v| ≤ 2 * K := by
    have hadd : ‖u + v‖ ≤ 2 := by
      exact (norm_add_le u v).trans (by rw [hu, hv]; norm_num)
    have hsub : ‖u - v‖ ≤ 2 := by
      exact (norm_sub_le u v).trans (by rw [hu, hv]; norm_num)
    have h₁ := (hdiag (u + v)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hadd 2) hK)
    have h₂ := (hdiag (u - v)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hsub 2) hK)
    simp only [map_add, map_sub, add_apply, sub_apply,
      hsymm v u, abs_le] at h₁ h₂ ⊢
    constructor <;> linarith [h₁.1, h₁.2, h₂.1, h₂.2]
  apply B.opNorm_le_bound (by positivity)
  intro u
  apply (B u).opNorm_le_bound (by positivity)
  intro v
  by_cases hu : u = 0
  · simp [hu]
  by_cases hv : v = 0
  · simp [hv]
  have hun := norm_ne_zero_iff.mpr hu
  have hvn := norm_ne_zero_iff.mpr hv
  have hnorm (z : E) (hz : ‖z‖ ≠ 0) : ‖‖z‖⁻¹ • z‖ = 1 := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity), inv_mul_cancel₀ hz]
  have h := hunit (‖u‖⁻¹ • u) (‖v‖⁻¹ • v) (hnorm u hun) (hnorm v hvn)
  simp only [map_smul, smul_apply, smul_eq_mul,
    abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ ‖u‖⁻¹),
    abs_of_nonneg (by positivity : 0 ≤ ‖v‖⁻¹)] at h
  rw [Real.norm_eq_abs]
  convert mul_le_mul_of_nonneg_left h (show 0 ≤ ‖u‖ * ‖v‖ by positivity) using 1
  · field_simp
  · ring

/-- **Theorem 9.3.1** of [conn2000trust], form with Lipschitz Hessians. Let
$f, m : E \to \mathbb{R}$ be twice continuously differentiable, let $\delta > 0$,
$\kappa_2 \ge 0$, $L_f \ge 0$ and $L_m \ge 0$, and suppose that for all $z \in E$
$$\|\nabla^2 f(z) - \nabla^2 f(x)\| \le L_f \|z - x\|, \qquad \|\nabla^2 m(z) - \nabla^2 m(x)\|
  \le L_m \|z - x\|.$$
If $m$ is second-order valid for $f$ on $B(x, \delta)$ with constants $\kappa_1$ and $\kappa_2$,
then
$$\|\nabla^2 f(x) - \nabla^2 m(x)\| \le 2 \left(4 \kappa_2 + \tfrac{1}{3}(L_f + L_m)\right)
  \delta.$$

**Correction.** The hypothesis $\delta > 0$ is necessary; see
`ConnGouldToint.Chapter09.second_order_zero_radius_counterexample`.

The proof uses a centered difference, which removes the constant and linear Taylor terms. Hence
the bound holds even when $f(x) \neq m(x)$, within the validity bound. The Hessians are
`fderiv ℝ (fderiv ℝ f) x` and `fderiv ℝ (fderiv ℝ m) x`, with the operator norm of bilinear
maps. -/
theorem theorem_9_3_1_of_hessian_lipschitz {f m : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hm : ContDiff ℝ 2 m) {x : E} {δ κ₁ κ₂ Lf Lm : ℝ} (hδ : 0 < δ)
    (hκ : 0 ≤ κ₂) (hLf : 0 ≤ Lf) (hLm : 0 ≤ Lm)
    (hF : ∀ z, ‖fderiv ℝ (fderiv ℝ f) z - fderiv ℝ (fderiv ℝ f) x‖ ≤ Lf * ‖z - x‖)
    (hM : ∀ z, ‖fderiv ℝ (fderiv ℝ m) z - fderiv ℝ (fderiv ℝ m) x‖ ≤ Lm * ‖z - x‖)
    (hv : modelSecondOrderValidOnBall f m x δ κ₁ κ₂) :
    ‖fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ m) x‖ ≤
      2 * (4 * κ₂ + (Lf + Lm) / 3) * δ := by
  let B := fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ m) x
  let K := 4 * κ₂ + (Lf + Lm) / 3
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hstep (s : E) (hs : ‖s‖ = δ) : |B s s| ≤ K * δ ^ 3 := by
    have hball (t : E) (ht : ‖t‖ = δ) : x + t ∈ Metric.closedBall x δ := by
      rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, ht]
    have h₀ := abs_le.mp (hv.2 x (Metric.mem_closedBall_self hδ.le))
    have hn : ‖-s‖ = δ := by simpa using hs
    have h₁ := abs_le.mp (hv.2 (x + s) (hball s hs))
    have h₂ := abs_le.mp (hv.2 (x + -s) (hball (-s) hn))
    have rem {g : E → ℝ} (hg : ContDiff ℝ 2 g) {L : ℝ}
        (hL : ∀ z, ‖fderiv ℝ (fderiv ℝ g) z - fderiv ℝ (fderiv ℝ g) x‖ ≤ L * ‖z - x‖)
        (t : E) (ht : ‖t‖ = δ) :
        |g (x + t) - (g x + fderiv ℝ g x t + (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ g) x t t)| ≤
          (1 / 6 : ℝ) * L * δ ^ 3 := by
      rw [← ht]
      exact abs_sub_secondOrder_le_of_lipschitzAt_segment isOpen_univ hg.contDiffOn
        (fun _ _ ↦ Set.mem_univ _) (fun z _ ↦ hL z)
    have hf₁ := abs_le.mp (rem hf hF s hs)
    have hf₂ := abs_le.mp (rem hf hF (-s) hn)
    have hm₁ := abs_le.mp (rem hm hM s hs)
    have hm₂ := abs_le.mp (rem hm hM (-s) hn)
    simp only [map_neg, neg_apply, neg_neg] at hf₂ hm₂
    rw [abs_le]
    dsimp [B, K]
    simp only [sub_apply]
    constructor <;>
      linarith [h₀.1, h₀.2, h₁.1, h₁.2, h₂.1, h₂.2, hf₁.1, hf₁.2, hf₂.1, hf₂.2,
        hm₁.1, hm₁.2, hm₂.1, hm₂.2]
  rw [mul_assoc]
  apply opNorm_le_of_diagonal (mul_nonneg hK hδ.le)
  · intro u v
    exact congrArg₂ Sub.sub ((hf.contDiffAt.isSymmSndFDerivAt (by simp)).eq u v)
      ((hm.contDiffAt.isSymmSndFDerivAt (by simp)).eq u v)
  · intro u
    by_cases hu : u = 0
    · simp [hu]
    have hnu : 0 < ‖u‖ := norm_pos_iff.mpr hu
    let a := δ / ‖u‖
    have ha : 0 < a := by dsimp [a]; positivity
    have hs : ‖a • u‖ = δ := by
      rw [norm_smul, Real.norm_of_nonneg ha.le]
      exact div_mul_cancel₀ _ hnu.ne'
    have h := hstep (a • u) hs
    simp only [map_smul, smul_apply, smul_eq_mul,
      abs_mul, abs_mul, abs_of_pos ha] at h
    apply (mul_le_mul_iff_of_pos_left (sq_pos_of_pos ha)).mp
    calc
      a ^ 2 * |B u u| ≤ K * δ ^ 3 := by nlinarith only [h]
      _ = a ^ 2 * (K * δ * ‖u‖ ^ 2) := by dsimp [a]; field_simp

noncomputable local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

/-- **Theorem 9.3.1** of [conn2000trust]. Let $f : E \to \mathbb{R}$ be three times continuously
differentiable, and let $m : E \to \mathbb{R}$ be differentiable with differentiable first and
second derivatives. Let $\delta > 0$, $\kappa_2 \ge 0$, $L_f \ge 0$ and $L_m \ge 0$, with
$\|\nabla^3 f(z)\| \le L_f$ and $\|\nabla^3 m(z)\| \le L_m$ for all $z \in E$. If $m$ is
second-order valid for $f$ on $B(x, \delta)$ with constants $\kappa_1$ and $\kappa_2$, then
$$\|\nabla^2 f(x) - \nabla^2 m(x)\| \le 2 \left(4 \kappa_2 + \tfrac{1}{3}(L_f + L_m)\right)
  \delta.$$

**Correction.** The hypothesis $\delta > 0$ is necessary; see
`ConnGouldToint.Chapter09.second_order_zero_radius_counterexample`.

The model Hessian is differentiable, hence continuous, as the Taylor estimate requires. The
proof reduces to `ConnGouldToint.Chapter09.theorem_9_3_1_of_hessian_lipschitz`. -/
theorem theorem_9_3_1 {f m : E → ℝ} (hf : ContDiff ℝ 3 f)
    (hm : Differentiable ℝ m) (hDm₁ : Differentiable ℝ (fderiv ℝ m))
    (hDm₂ : Differentiable ℝ (fderiv ℝ (fderiv ℝ m)))
    {x : E} {δ κ₁ κ₂ Lf Lm : ℝ} (hδ : 0 < δ) (hκ : 0 ≤ κ₂)
    (hLf : 0 ≤ Lf) (hLm : 0 ≤ Lm)
    (hF : ∀ z, ‖fderiv ℝ (fderiv ℝ (fderiv ℝ f)) z‖ ≤ Lf)
    (hM : ∀ z, ‖fderiv ℝ (fderiv ℝ (fderiv ℝ m)) z‖ ≤ Lm)
    (hv : modelSecondOrderValidOnBall f m x δ κ₁ κ₂) :
    ‖fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ m) x‖ ≤
      2 * (4 * κ₂ + (Lf + Lm) / 3) * δ := by
  have hDf : ContDiff ℝ 2 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hD2f : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ f)) := hDf.fderiv_right (by norm_num)
  have lip {g : E → E →L[ℝ] E →L[ℝ] ℝ} (hg : Differentiable ℝ g) {L : ℝ}
      (hL : ∀ z, ‖fderiv ℝ g z‖ ≤ L) (z : E) : ‖g z - g x‖ ≤ L * ‖z - x‖ :=
    Convex.norm_image_sub_le_of_norm_fderiv_le (fun y _ ↦ hg y) (fun y _ ↦ hL y)
      (convex_univ : Convex ℝ (Set.univ : Set E)) (Set.mem_univ x) (Set.mem_univ z)
  have hCm : ContDiff ℝ 2 m := by
    rw [show (2 : WithTop ℕ∞) = 1 + 1 by norm_num, contDiff_succ_iff_fderiv]
    refine ⟨hm, by simp, contDiff_one_iff_fderiv.mpr ⟨hDm₁, hDm₂.continuous⟩⟩
  exact theorem_9_3_1_of_hessian_lipschitz (hf.of_le (by norm_num)) hCm hδ hκ hLf hLm
    (lip (hD2f.differentiable (by norm_num)) hF) (lip hDm₂ hM) hv

/-- **Corollary 9.3.2** of [conn2000trust]. Let $f : E \to \mathbb{R}$ be three times continuously
differentiable, and let the models $m_k : E \to \mathbb{R}$ be differentiable with
differentiable first and second derivatives. Let $\kappa_2 \ge 0$, $L_f \ge 0$ and $L_m \ge 0$,
with $\|\nabla^3 f(z)\| \le L_f$ and $\|\nabla^3 m_k(z)\| \le L_m$ for all $k$ and $z$. Let
$x_k \in E$ and $\delta_k \in \mathbb{R}$. Suppose that for all sufficiently large $k$,
$0 < \delta_k \le \mu \|\nabla m_k(x_k)\|$ and $m_k$ is second-order valid for $f$ on
$B(x_k, \delta_k)$ with constants $\kappa_1$ and $\kappa_2$. If $\|\nabla m_k(x_k)\| \to 0$,
then
$$\|\nabla^2 f(x_k) - \nabla^2 m_k(x_k)\| \to 0.$$

The modified acceptance test of the algorithm provides the eventual second-order validity on
balls of positive radius at most a multiple of the model gradient norm.

**Reading.** Uses explicit hypotheses for accepted positive radii and uniform normed-space bounds.
-/
theorem corollary_9_3_2 {f : E → ℝ} (hf : ContDiff ℝ 3 f) {m : ℕ → E → ℝ}
    (hm : ∀ k, Differentiable ℝ (m k))
    (hDm₁ : ∀ k, Differentiable ℝ (fderiv ℝ (m k)))
    (hDm₂ : ∀ k, Differentiable ℝ (fderiv ℝ (fderiv ℝ (m k))))
    {x : ℕ → E} {δ : ℕ → ℝ} {κ₁ κ₂ Lf Lm μ : ℝ}
    (hκ : 0 ≤ κ₂) (hLf : 0 ≤ Lf) (hLm : 0 ≤ Lm)
    (hF : ∀ z, ‖fderiv ℝ (fderiv ℝ (fderiv ℝ f)) z‖ ≤ Lf)
    (hM : ∀ k z, ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (m k))) z‖ ≤ Lm)
    (hvalid : ∀ᶠ k in atTop, 0 < δ k ∧ δ k ≤ μ * ‖fderiv ℝ (m k) (x k)‖ ∧
      modelSecondOrderValidOnBall f (m k) (x k) (δ k) κ₁ κ₂)
    (hg : Tendsto (fun k ↦ ‖fderiv ℝ (m k) (x k)‖) atTop (𝓝 0)) :
    Tendsto (fun k ↦
      ‖fderiv ℝ (fderiv ℝ f) (x k) - fderiv ℝ (fderiv ℝ (m k)) (x k)‖) atTop (𝓝 0) := by
  let C := 2 * (4 * κ₂ + (Lf + Lm) / 3)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hc : Tendsto (fun _ : ℕ ↦ C * μ) atTop (𝓝 (C * μ)) := tendsto_const_nhds
  have hlim : Tendsto (fun k ↦ (C * μ) * ‖fderiv ℝ (m k) (x k)‖) atTop (𝓝 0) := by
    simpa only [mul_zero] using hc.mul hg
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ hlim
  filter_upwards [hvalid] with k hk
  have he := theorem_9_3_1 hf (hm k) (hDm₁ k) (hDm₂ k) hk.1 hκ hLf hLm hF (hM k) hk.2.2
  calc
    _ ≤ C * δ k := he
    _ ≤ C * (μ * ‖fderiv ℝ (m k) (x k)‖) := mul_le_mul_of_nonneg_left hk.2.1 hC
    _ = _ := (mul_assoc C μ _).symm

/-- **Theorem 9.3.3** of [conn2000trust]. Let $f : E \to \mathbb{R}$ be three times continuously
differentiable, and let the models $m_k : E \to \mathbb{R}$ be differentiable with
differentiable first and second derivatives. Let $\kappa_1 > 0$ and
$\kappa_2, B_f, B_m, L_f, L_m \ge 0$, with $\|\nabla^2 f(z)\| \le B_f$,
$\|\nabla^2 m_k(z)\| \le B_m$, $\|\nabla^3 f(z)\| \le L_f$ and $\|\nabla^3 m_k(z)\| \le L_m$ for
all $k$ and $z$. Let $x \in E$, and let $\delta_k$ and $\tau_k$ be real sequences with
$\tau_k \to 0$. Suppose that for all sufficiently large $k$, $0 < \delta_k \le \mu \tau_k$,
$m_k$ is second-order valid for $f$ on $B(x, \delta_k)$ with constants $\kappa_1$ and
$\kappa_2$, and $\|\nabla m_k(x)\| \le \tau_k$. Suppose also that for every $v \in E$,
eventually
$$-\tau_k \|v\|^2 \le \nabla^2 m_k(x)[v, v].$$
Then $\nabla f(x) = 0$ and $\nabla^2 f(x)[v, v] \ge 0$ for all $v \in E$.

**Correction.** The printed condition (9.3.4) on the model curvature does not hold for the
refinement loop: the model curvature can stay negative at every refinement. The proof needs only
the lower curvature bound $-\tau_k$, which tends to zero.

The sequence $\tau_k$ bounds both the model gradient norm and the negative model curvature, as
in an infinite refinement loop of Algorithm 9.3.1; see
`ConnGouldToint.Chapter09.theorem_9_3_3_of_refinement`. -/
theorem theorem_9_3_3 {f : E → ℝ} (hf : ContDiff ℝ 3 f) {m : ℕ → E → ℝ}
    (hm : ∀ k, Differentiable ℝ (m k))
    (hDm₁ : ∀ k, Differentiable ℝ (fderiv ℝ (m k)))
    (hDm₂ : ∀ k, Differentiable ℝ (fderiv ℝ (fderiv ℝ (m k))))
    {x : E} {δ τ : ℕ → ℝ} {κ₁ κ₂ Bf Bm Lf Lm μ : ℝ}
    (hκ₁ : 0 < κ₁) (hκ₂ : 0 ≤ κ₂) (hBf : 0 ≤ Bf) (hBm : 0 ≤ Bm)
    (hLf : 0 ≤ Lf) (hLm : 0 ≤ Lm)
    (hF₂ : ∀ z, ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ Bf)
    (hM₂ : ∀ k z, ‖fderiv ℝ (fderiv ℝ (m k)) z‖ ≤ Bm)
    (hF₃ : ∀ z, ‖fderiv ℝ (fderiv ℝ (fderiv ℝ f)) z‖ ≤ Lf)
    (hM₃ : ∀ k z, ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (m k))) z‖ ≤ Lm)
    (hvalid : ∀ᶠ k in atTop, 0 < δ k ∧ δ k ≤ μ * τ k ∧
      modelSecondOrderValidOnBall f (m k) x (δ k) κ₁ κ₂)
    (hgrad : ∀ᶠ k in atTop, ‖fderiv ℝ (m k) x‖ ≤ τ k)
    (hcurv : ∀ v, ∀ᶠ k in atTop, -(τ k) * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (m k)) x v v)
    (hτ : Tendsto τ atTop (𝓝 0)) :
    fderiv ℝ f x = 0 ∧ ∀ v, 0 ≤ fderiv ℝ (fderiv ℝ f) x v v := by
  let Cg := 2 * κ₁ + (Bf + Bm) / 2
  let Ch := 2 * (4 * κ₂ + (Lf + Lm) / 3)
  have hCg : 0 ≤ Cg := by dsimp [Cg]; positivity
  have hCh : 0 ≤ Ch := by dsimp [Ch]; positivity
  constructor
  · apply norm_le_zero_iff.mp
    have hlim : Tendsto (fun k ↦ (1 + Cg * μ) * τ k) atTop (𝓝 0) := by
      simpa only [mul_zero] using tendsto_const_nhds.mul hτ (f := fun _ ↦ 1 + Cg * μ)
    apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
    filter_upwards [hvalid, hgrad] with k hv hg
    have he := theorem_9_1_1 (hf.of_le (by norm_num)) (hm k) (hDm₁ k)
      hv.1 hκ₁ hBf hBm hF₂ (hM₂ k) hv.2.2.1
    let a := fderiv ℝ f x
    let b := fderiv ℝ (m k) x
    calc
      ‖a‖ ≤ ‖a - b‖ + ‖b‖ := by simpa only [sub_add_cancel] using norm_add_le (a - b) b
      _ ≤ Cg * δ k + τ k := add_le_add he hg
      _ ≤ Cg * (μ * τ k) + τ k := add_le_add (mul_le_mul_of_nonneg_left hv.2.1 hCg) le_rfl
      _ = _ := by ring
  · intro v
    have hlim : Tendsto (fun k ↦ -((1 + Ch * μ) * ‖v‖ ^ 2) * τ k) atTop (𝓝 0) := by
      simpa only [mul_zero] using
        tendsto_const_nhds.mul hτ (f := fun _ ↦ -((1 + Ch * μ) * ‖v‖ ^ 2))
    apply le_of_tendsto_of_tendsto hlim tendsto_const_nhds
    filter_upwards [hvalid, hcurv v] with k hv hc
    have he := theorem_9_3_1 hf (hm k) (hDm₁ k) (hDm₂ k) hv.1 hκ₂ hLf hLm hF₃ (hM₃ k) hv.2.2
    let A := fderiv ℝ (fderiv ℝ f) x
    let B := fderiv ℝ (fderiv ℝ (m k)) x
    let D := A - B
    have hd : |D v v| ≤ Ch * (μ * τ k) * ‖v‖ ^ 2 := calc
      |D v v| = ‖D v v‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖D v‖ * ‖v‖ := (D v).le_opNorm v
      _ ≤ (‖D‖ * ‖v‖) * ‖v‖ :=
        mul_le_mul_of_nonneg_right (D.le_opNorm v) (norm_nonneg _)
      _ = ‖D‖ * ‖v‖ ^ 2 := by ring
      _ ≤ Ch * (μ * τ k) * ‖v‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (he.trans (mul_le_mul_of_nonneg_left hv.2.1 hCh)) (sq_nonneg _)
    have hd' := (abs_le.mp hd).1
    change -(Ch * (μ * τ k) * ‖v‖ ^ 2) ≤ A v v - B v v at hd'
    change -(τ k) * ‖v‖ ^ 2 ≤ B v v at hc
    change -((1 + Ch * μ) * ‖v‖ ^ 2) * τ k ≤ A v v
    calc
      _ = -(Ch * (μ * τ k) * ‖v‖ ^ 2) + (-(τ k) * ‖v‖ ^ 2) := by ring
      _ ≤ (A v v - B v v) + B v v := add_le_add hd' hc
      _ = _ := sub_add_cancel _ _

/-- Second-order validity on a ball of radius $0$ gives no control of the Hessian error. On
$\mathbb{R}$, the model $m = 0$ is second-order valid for $f(x) = x^2$ on $B(0, 0)$ with
constants $1$ and $1$, but $f''(0) \neq m''(0)$. This shows that the hypothesis $\delta > 0$ of
Theorem 9.3.1 is necessary.

**Reading.** At zero radius cubic validity can hold with different Hessians.
-/
theorem second_order_zero_radius_counterexample :
    modelSecondOrderValidOnBall (fun x : ℝ ↦ x ^ 2) (fun _ ↦ 0) 0 0 1 1 ∧
      fderiv ℝ (fderiv ℝ (fun x : ℝ ↦ x ^ 2)) 0 ≠
        fderiv ℝ (fderiv ℝ (fun _ : ℝ ↦ (0 : ℝ))) 0 := by
  constructor
  · constructor <;> intro z hz <;> have hz₀ : z = 0 := by simpa using hz
    all_goals simp [hz₀]
  · let f := fun x : ℝ ↦ x ^ 2
    have hf : ContDiff ℝ 2 f := contDiff_id.pow 2
    have hDf : Differentiable ℝ (fderiv ℝ f) :=
      (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
    have hfirst : (fun x ↦ fderiv ℝ f x 1) = fun x ↦ 2 * x := by
      funext x
      rw [fderiv_apply_one_eq_deriv]
      change deriv (fun y : ℝ ↦ y ^ 2) x = _
      rw [deriv_pow_field]
      norm_num
    have hsecond : deriv (fun x ↦ fderiv ℝ f x 1) 0 = 2 := by
      rw [hfirst]
      simpa only [id_eq, mul_one] using ((hasDerivAt_id (0 : ℝ)).const_mul (2 : ℝ)).deriv
    change fderiv ℝ (fderiv ℝ f) 0 ≠
      fderiv ℝ (fderiv ℝ (Function.const ℝ (0 : ℝ))) 0
    rw [fderiv_const]
    change fderiv ℝ (fderiv ℝ f) 0 ≠
      fderiv ℝ (Function.const ℝ (0 : ℝ →L[ℝ] ℝ)) 0
    rw [fderiv_const]
    intro h
    rw [deriv_clm_apply (hDf 0) (differentiableAt_const (1 : ℝ)),
      ← fderiv_apply_one_eq_deriv, h] at hsecond
    simp at hsecond

/-- **Algorithm 9.3.1** of [conn2000trust], criticality measure. For a model $m : E \to \mathbb{R}$,
a point $x$ and a lower bound $\lambda$ on the curvature of $m$ at $x$, the **second-order model
criticality** is
$$\max\{\|\nabla m(x)\|, -\lambda\}.$$
-/
noncomputable def secondOrderModelCriticality (m : E → ℝ) (x : E) (curvature : ℝ) : ℝ :=
  max ‖fderiv ℝ m x‖ (-curvature)

/-- **Algorithm 9.3.1** of [conn2000trust], validity test. The model $m$ **passes** the second-order
test at $x$, with constants $\kappa_1, \kappa_2, \mu$ and curvature bound $\lambda$, if there is
$\delta > 0$ with $\delta \le \mu \max\{\|\nabla m(x)\|, -\lambda\}$ such that $m$ is
second-order valid for $f$ on $B(x, \delta)$ with constants $\kappa_1$ and $\kappa_2$.

The certificate radius $\delta$ must be positive.

**Reading.** Test insists on strictly positive radius.
-/
def secondOrderModelPasses (f m : E → ℝ) (x : E) (κ₁ κ₂ μ curvature : ℝ) : Prop :=
  ∃ δ > 0, δ ≤ μ * secondOrderModelCriticality m x curvature ∧
    modelSecondOrderValidOnBall f m x δ κ₁ κ₂

/-- **Algorithm 9.3.1** of [conn2000trust], refinement radius. For
$\alpha, \mu, \delta, \tau \in \mathbb{R}$, the **refinement radius** is $\alpha \mu \tau$ if
$\tau > 0$, and $\alpha \delta$ otherwise. Here $\delta$ is the current radius and $\tau$ the
current model criticality.

**Correction.** At zero model criticality, the printed target radius $\alpha \mu \tau$ is zero.
The definition shrinks the current positive radius instead, so that the estimates for positive
radii still apply. -/
noncomputable def secondOrderRefinementRadius (α μ δ τ : ℝ) : ℝ :=
  α * (if 0 < τ then μ * τ else δ)

/-- **Algorithm 9.3.1** of [conn2000trust], infinite refinement trace at a fixed point $x \in E$,
with constants $\kappa_1, \kappa_2, \mu, \alpha, \varepsilon$. A **second-order model
refinement** consists of models $m_k : E \to \mathbb{R}$, radii $\delta_k$ and curvature bounds
$\lambda_k$, for $k \in \mathbb{N}$, such that for every $k$: $\delta_k > 0$; $m_k$ is
second-order valid for $f$ on $B(x, \delta_k)$; $\|\nabla m_k(x)\| \le \varepsilon$;
$\lambda_k \|v\|^2 \le \nabla^2 m_k(x)[v, v]$ for all $v$; $m_k$ fails the second-order test
with curvature bound $\lambda_k$; and $\delta_{k+1}$ is the refinement radius for $\delta_k$ and
the criticality $\max\{\|\nabla m_k(x)\|, -\lambda_k\}$.

The trace starts at a validity certificate of positive radius, and each model is tested again
after the refinement.

**Correction.** Abstract infinite trace for the corrected positive-radius loop.
-/
structure SecondOrderModelRefinement (f : E → ℝ) (x : E) (κ₁ κ₂ μ α ε : ℝ) where
  /-- The model $m_k$ after $k$ refinements. -/
  model : ℕ → E → ℝ
  /-- The radius $\delta_k$ of the validity certificate of $m_k$. -/
  radius : ℕ → ℝ
  /-- The lower bound $\lambda_k$ on the curvature of $m_k$ at $x$. -/
  leastCurvature : ℕ → ℝ
  /-- Each radius is positive: $\delta_k > 0$. -/
  radius_pos : ∀ k, 0 < radius k
  /-- The model $m_k$ is second-order valid for $f$ on $B(x, \delta_k)$ with constants $\kappa_1$
  and $\kappa_2$. -/
  valid : ∀ k, modelSecondOrderValidOnBall f (model k) x (radius k) κ₁ κ₂
  /-- The model gradient is small: $\|\nabla m_k(x)\| \le \varepsilon$. -/
  small_gradient : ∀ k, ‖fderiv ℝ (model k) x‖ ≤ ε
  /-- The curvature bound holds: $\lambda_k \|v\|^2 \le \nabla^2 m_k(x)[v, v]$ for all $v \in E$. -/
  curvature_bound : ∀ k v, leastCurvature k * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (model k)) x v v
  /-- The model $m_k$ fails the second-order validity test with curvature bound $\lambda_k$. -/
  test_fails : ∀ k, ¬ secondOrderModelPasses f (model k) x κ₁ κ₂ μ (leastCurvature k)
  /-- The next radius is the refinement radius for $\delta_k$ and the criticality of $m_k$. -/
  refine_radius : ∀ k, radius (k + 1) = secondOrderRefinementRadius α μ (radius k)
    (secondOrderModelCriticality (model k) x (leastCurvature k))

namespace SecondOrderModelRefinement

variable {f : E → ℝ} {x : E} {κ₁ κ₂ μ α ε : ℝ}

/-- A failed test gives $\mu \max\{\|\nabla m_k(x)\|, -\lambda_k\} < \delta_k$.

**Reading.** Failed test on a valid positive-radius trace yields a strict criticality bound.
-/
private theorem criticality_lt (run : SecondOrderModelRefinement f x κ₁ κ₂ μ α ε) (k : ℕ) :
    μ * secondOrderModelCriticality (run.model k) x (run.leastCurvature k) < run.radius k :=
  lt_of_not_ge fun h ↦ run.test_fails k ⟨run.radius k, run.radius_pos k, h, run.valid k⟩

/-- **Algorithm 9.3.1** of [conn2000trust], radius decay. If $0 \le \alpha < 1$, the radii
$\delta_k$ of a second-order model refinement tend to zero.

Each refinement multiplies the radius by at most $\alpha$, also in the branch with zero
criticality.

**Correction.** Geometric radius decay for the corrected loop.
-/
theorem tendsto_radius (run : SecondOrderModelRefinement f x κ₁ κ₂ μ α ε)
    (hα : 0 ≤ α) (hα₁ : α < 1) : Tendsto run.radius atTop (𝓝 0) := by
  have hstep (k : ℕ) : run.radius (k + 1) ≤ α * run.radius k := by
    rw [run.refine_radius k, secondOrderRefinementRadius]
    apply mul_le_mul_of_nonneg_left _ hα
    split
    · exact (run.criticality_lt k).le
    · rfl
  have hbound (k : ℕ) : run.radius k ≤ run.radius 0 * α ^ k := by
    induction k with
    | zero => simp
    | succ k ih =>
      calc
        _ ≤ α * run.radius k := hstep k
        _ ≤ α * (run.radius 0 * α ^ k) := mul_le_mul_of_nonneg_left ih hα
        _ = _ := by rw [pow_succ]; ring
  refine squeeze_zero (fun k ↦ (run.radius_pos k).le) hbound ?_
  simpa only [mul_zero] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one hα hα₁).const_mul (run.radius 0)

end SecondOrderModelRefinement

/-- **Theorem 9.3.3** of [conn2000trust], for the corrected Algorithm 9.3.1. Let a second-order
model refinement for $f$ at $x$ be given, with $\mu > 0$ and $0 \le \alpha < 1$. Let $f$ be
three times continuously differentiable, and let the models $m_k$ be differentiable with
differentiable first and second derivatives. Let $\kappa_1 > 0$ and
$\kappa_2, B_f, B_m, L_f, L_m \ge 0$, with $\|\nabla^2 f(z)\| \le B_f$,
$\|\nabla^2 m_k(z)\| \le B_m$, $\|\nabla^3 f(z)\| \le L_f$ and $\|\nabla^3 m_k(z)\| \le L_m$ for
all $k$ and $z$. Then $\nabla f(x) = 0$ and $\nabla^2 f(x)[v, v] \ge 0$ for all $v \in E$.

The proof applies `ConnGouldToint.Chapter09.theorem_9_3_3` with $\tau_k = \delta_k / \mu$. A
failed test makes $\delta_k / \mu$ an upper bound on both the model gradient norm and the
negative curvature.

**Correction.** Second-order criticality derived from the corrected positive-radius loop.
-/
theorem theorem_9_3_3_of_refinement {f : E → ℝ} {x : E} {κ₁ κ₂ μ α ε Bf Bm Lf Lm : ℝ}
    (run : SecondOrderModelRefinement f x κ₁ κ₂ μ α ε)
    (hμ : 0 < μ) (hα : 0 ≤ α) (hα₁ : α < 1) (hf : ContDiff ℝ 3 f)
    (hm : ∀ k, Differentiable ℝ (run.model k))
    (hDm₁ : ∀ k, Differentiable ℝ (fderiv ℝ (run.model k)))
    (hDm₂ : ∀ k, Differentiable ℝ (fderiv ℝ (fderiv ℝ (run.model k))))
    (hκ₁ : 0 < κ₁) (hκ₂ : 0 ≤ κ₂) (hBf : 0 ≤ Bf) (hBm : 0 ≤ Bm)
    (hLf : 0 ≤ Lf) (hLm : 0 ≤ Lm)
    (hF₂ : ∀ z, ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ Bf)
    (hM₂ : ∀ k z, ‖fderiv ℝ (fderiv ℝ (run.model k)) z‖ ≤ Bm)
    (hF₃ : ∀ z, ‖fderiv ℝ (fderiv ℝ (fderiv ℝ f)) z‖ ≤ Lf)
    (hM₃ : ∀ k z, ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (run.model k))) z‖ ≤ Lm) :
    fderiv ℝ f x = 0 ∧ ∀ v, 0 ≤ fderiv ℝ (fderiv ℝ f) x v v := by
  let τ (k : ℕ) := run.radius k / μ
  have hτ : Tendsto τ atTop (𝓝 0) := by
    simpa only [zero_div] using (run.tendsto_radius hα hα₁).div_const μ
  have hcrit (k : ℕ) :
      secondOrderModelCriticality (run.model k) x (run.leastCurvature k) ≤ τ k := by
    apply (le_div_iff₀ hμ).mpr
    rw [mul_comm]
    exact (run.criticality_lt k).le
  apply theorem_9_3_3 (δ := run.radius) (τ := τ) (μ := μ) hf hm hDm₁ hDm₂ hκ₁ hκ₂
    hBf hBm hLf hLm hF₂ hM₂ hF₃ hM₃ _ _ _ hτ
  · exact Eventually.of_forall fun k ↦
      ⟨run.radius_pos k, by dsimp [τ]; rw [← mul_div_assoc, mul_div_cancel_left₀ _ hμ.ne'],
        run.valid k⟩
  · exact Eventually.of_forall fun k ↦ (le_max_left _ _).trans (hcrit k)
  · intro v
    apply Eventually.of_forall
    intro k
    have hl := (le_max_right _ _).trans (hcrit k)
    exact (mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg ‖v‖)).trans
      (run.curvature_bound k v)

end ConnGouldToint.Chapter09
