/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.ConnGouldToint.Chapter15.Corrections

/-!
# Conn, Gould and Toint, Section 15.4: Byrd–Omojokun SQP convergence

This module formalizes the convergence theorems for the Byrd–Omojokun composite-step SQP method in
[conn2000trust], Section 15.4, Theorems 15.4.22–15.4.25. At iteration $k$ the step is the sum of a
normal step $n_k$, which reduces the linearized constraint violation, and a tangential step, which
reduces the model in reduced coordinates. With the reduced-coordinate map $N_k^T$, the criticality
measure is $\|N_k^T g_k\|$. The predicted decrease of the merit function $f(x) + \sigma \|c(x)\|$
splits as
$$d_k = d^T_k + \sigma_{k+1} d^N_k - \langle g_k, n_k \rangle - \tfrac12 \langle n_k, H_k n_k
  \rangle,$$
and the penalty update enforces (15.4.7), $\nu \sigma_{k+1} d^N_k \le d_k$.

Theorem 15.4.22 shows that, if the constraint values tend to zero, the penalty parameter stabilizes
and the reduced gradient tends to zero. Theorem 15.4.23 extends this to the method with a
second-order correction step (Algorithm 15.4.6) and derives feasibility from a uniform rank
condition. Theorem 15.4.24 gives Q-superlinear and Q-quadratic local convergence, and Theorem
15.4.25 gives a second-order condition at a cluster point. The statements use uniform bounds on the
error of the full trial and on the variation of the accepted steps, from the corrected convergence
results of Section 15.4 (`ConnGouldToint.Chapter15.SQPTangentialRun`). The original trial determines
the agreement between the model and the merit function, and the accepted trial, possibly corrected,
determines the decrease of the merit function.

## Main definitions

* Theorem 15.4.22, `ConnGouldToint.Chapter15.ByrdOmojokunTangentialData`: the model and penalty data
  of a run.

## Main results

* Equation (15.4.7), `ConnGouldToint.Chapter15.ByrdOmojokunTangentialData.model_penalty`: the
  penalty update gives $\nu \sigma_{k+1} d^N_k \le d_k$.
* Theorem 15.4.22, `ConnGouldToint.Chapter15.theorem_15_4_22`: stabilization of the penalty
  parameter and convergence of the reduced gradient.
* Theorem 15.4.23, `ConnGouldToint.Chapter15.theorem_15_4_23`: feasibility and convergence of the
  reduced gradient with a second-order correction.
* Theorem 15.4.24, `ConnGouldToint.Chapter15.theorem_15_4_24`: Q-superlinear and Q-quadratic local
  convergence.
* Theorem 15.4.25, `ConnGouldToint.Chapter15.theorem_15_4_25`: nonnegative curvature at a
  first-order cluster point.

## Deviations from the source

* **Theorem 15.4.23** (typo). The printed statement refers to the wrong algorithm; the theorem
  concerns Algorithm 15.4.6, the method with the second-order correction. See
  `ConnGouldToint.Chapter15.theorem_15_4_23`.
* **Theorem 15.4.25** (correction). The argument uses the cluster point of maximal curvature, with a
  corrected curvature margin, and the coverage of the tail by the cluster set is a hypothesis. See
  `ConnGouldToint.Chapter15.theorem_15_4_25`.
-/

open Filter Topology
open scoped RealInnerProductSpace

namespace ConnGouldToint.Chapter15

open Chapter06

variable {E Y Z : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- **Theorem 15.4.22** of [conn2000trust], the data of a run. For constraint values $c_k$,
gradients $g_k$, normal steps $n_k$, Hessians $H_k$, reduced-coordinate maps $N_k^T$, penalty
parameters $\sigma_k$, normal, tangential and total predicted decreases $d^N_k$, $d^T_k$, $d_k$,
shifted merit values $v_k$, radii $\Delta_k$, actual reductions of the original trials and
successful iterations $S$, the data consist of:

* a stabilized SQP tail `ConnGouldToint.Chapter15.SQPTangentialRun` for the criticality measures
  $\|N_k^T g_k\|$ and $\|N_k^T (g_k + H_k n_k)\|$, with the actual reductions of the original
  trials in the ratio test;
* uniform bounds $\|g_k\| \le G$, $\|H_k\| \le B$, $\|N_k^T\| \le D$ and $\|c_k\| \le U$;
* the normal decrease bound $b_N \|n_k\| \le d^N_k \le \|c_k\|$ with $b_N > 0$, and
  $d^T_k \ge 0$;
* the penalty update of Step 2 of Algorithm 15.4.1 with constants $\tau_1 \ge 0$ and
  $\tau_2 > 0$, starting from $\sigma_0 > 0$, whose required value is the maximum of a bounded
  auxiliary value and, if $d^N_k > 0$, the threshold (15.4.8) for $\nu \in (0, 1)$;
* the splitting $d_k = d^T_k + \sigma_{k+1} d^N_k - \langle g_k, n_k \rangle - \frac12 \langle
  n_k, H_k n_k \rangle$;
* the tangential Cauchy decrease $\kappa w_k \min\{b \Delta_k, w_k / \beta\} \le d^T_k$ with
  $w_k = \|N_k^T (g_k + H_k n_k)\|$ and $\kappa, b, \beta > 0$;
* the error bound $|\mathrm{original}_k - d_k| \le C (1 + \sigma_{k+1}) \Delta_k^2$ for the
  original trial.

The original, uncorrected trial determines the small-radius guarantee, and the accepted trial
determines the decrease of the merit function. -/
structure ByrdOmojokunTangentialData (P : BTRParams)
    (c : ℕ → Y) (g n : ℕ → E) (H : ℕ → E →L[ℝ] E) (NT : ℕ → E →L[ℝ] Z)
    (σ dN dT d v Δ original : ℕ → ℝ) (S : Set ℕ) where
  /-- The stabilized SQP tail for the criticality measures $\|N_k^T g_k\|$ and
  $\|N_k^T (g_k + H_k n_k)\|$. -/
  run : SQPTangentialRun P (fun k => ‖NT k (g k)‖) (fun k => ‖NT k (g k + H k (n k))‖)
    v Δ d original S
  /-- The bound $G$ on the gradients. -/
  G : ℝ
  /-- The bound $B$ on the Hessians. -/
  B : ℝ
  /-- The bound $U$ on the constraint values. -/
  U : ℝ
  /-- The bound $D$ on the reduced-coordinate maps. -/
  D : ℝ
  /-- The constant $b_N$ of the normal decrease bound. -/
  bN : ℝ
  /-- The fraction $\nu$ in the penalty condition (15.4.7). -/
  ν : ℝ
  /-- The multiplicative constant $\tau_1$ of the penalty update. -/
  τ₁ : ℝ
  /-- The additive constant $\tau_2$ of the penalty update. -/
  τ₂ : ℝ
  /-- The constant $C$ of the error bound for the original trial. -/
  C : ℝ
  /-- The constant $\kappa$ of the tangential Cauchy decrease. -/
  κ : ℝ
  /-- The constant $b$ of the tangential Cauchy decrease. -/
  b : ℝ
  /-- The curvature constant $\beta$ of the tangential Cauchy decrease. -/
  β : ℝ
  /-- The auxiliary lower bounds for the required penalty parameter. -/
  auxiliary : ℕ → ℝ
  /-- The upper bound of the auxiliary values. -/
  auxiliaryBound : ℝ
  /-- The gradient bound is nonnegative. -/
  G_nonneg : 0 ≤ G
  /-- The Hessian bound is nonnegative. -/
  B_nonneg : 0 ≤ B
  /-- The constraint bound is nonnegative. -/
  U_nonneg : 0 ≤ U
  /-- The bound on the reduced-coordinate maps is nonnegative. -/
  D_nonneg : 0 ≤ D
  /-- The constant $b_N$ is positive. -/
  bN_pos : 0 < bN
  /-- The fraction $\nu$ is positive. -/
  ν_pos : 0 < ν
  /-- The fraction $\nu$ is less than one. -/
  ν_lt_one : ν < 1
  /-- The constant $\tau_1$ is nonnegative. -/
  τ₁_nonneg : 0 ≤ τ₁
  /-- The constant $\tau_2$ is positive. -/
  τ₂_pos : 0 < τ₂
  /-- The constant $C$ is nonnegative. -/
  C_nonneg : 0 ≤ C
  /-- The constant $\kappa$ is positive. -/
  κ_pos : 0 < κ
  /-- The constant $b$ is positive. -/
  b_pos : 0 < b
  /-- The constant $\beta$ is positive. -/
  β_pos : 0 < β
  /-- The initial penalty parameter is positive. -/
  penalty_initial : 0 < σ 0
  /-- The gradients satisfy $\|g_k\| \le G$. -/
  gradient_bound : ∀ k, ‖g k‖ ≤ G
  /-- The Hessians satisfy $\|H_k\| \le B$. -/
  hessian_bound : ∀ k, ‖H k‖ ≤ B
  /-- The reduced-coordinate maps satisfy $\|N_k^T\| \le D$. -/
  reduced_map_bound : ∀ k, ‖NT k‖ ≤ D
  /-- The constraint values satisfy $\|c_k\| \le U$. -/
  constraint_bound : ∀ k, ‖c k‖ ≤ U
  /-- The normal decrease satisfies $b_N \|n_k\| \le d^N_k \le \|c_k\|$. -/
  normal_decrease : ∀ k, bN * ‖n k‖ ≤ dN k ∧ dN k ≤ ‖c k‖
  /-- The tangential decrease is nonnegative. -/
  tangential_nonneg : ∀ k, 0 ≤ dT k
  /-- The auxiliary values are bounded above. -/
  auxiliary_bound : ∀ k, auxiliary k ≤ auxiliaryBound
  /-- The penalty parameter follows the update of Step 2 of Algorithm 15.4.1. The required value is
  the auxiliary value if $d^N_k = 0$, and otherwise the maximum of the auxiliary value and the
  threshold (15.4.8). -/
  penalty_update : ∀ k,
    let dq := -⟪g k, n k⟫ - (1 / 2) * ⟪n k, H k (n k)⟫
    let required := if dN k = 0 then auxiliary k
      else max (auxiliary k) (sqpPenaltyThreshold ν (dN k) (dT k) dq)
    σ (k + 1) = sqpPenaltyUpdate τ₁ τ₂ required (σ k)
  /-- The total predicted decrease splits as $d_k = d^T_k + \sigma_{k+1} d^N_k - \langle g_k, n_k
  \rangle - \frac12 \langle n_k, H_k n_k \rangle$. -/
  model_split : ∀ k, d k = dT k + σ (k + 1) * dN k +
    (-⟪g k, n k⟫ - (1 / 2) * ⟪n k, H k (n k)⟫)
  /-- The tangential decrease satisfies $\kappa w_k \min\{b \Delta_k, w_k / \beta\} \le d^T_k$, with
  $w_k = \|N_k^T (g_k + H_k n_k)\|$. -/
  tangential_cauchy : ∀ k,
    let w := ‖NT k (g k + H k (n k))‖
    κ * w * min (b * Δ k) (w / β) ≤ dT k
  /-- The actual reduction of the original trial satisfies $|\mathrm{original}_k - d_k| \le C (1 +
  \sigma_{k+1}) \Delta_k^2$. -/
  original_error : ∀ k, |original k - d k| ≤ C * (1 + σ (k + 1)) * Δ k ^ 2

omit [NormedSpace ℝ Y] in
/-- **Equation (15.4.7)** of [conn2000trust]. For every $k$, the data of a run satisfy
$$\nu \sigma_{k+1} d^N_k \le d_k.$$

If $d^N_k = 0$, the normal decrease bound forces $n_k = 0$, and then $d_k = d^T_k \ge 0$. -/
theorem ByrdOmojokunTangentialData.model_penalty {P : BTRParams}
    {c : ℕ → Y} {g n : ℕ → E} {H : ℕ → E →L[ℝ] E} {NT : ℕ → E →L[ℝ] Z}
    {σ dN dT d v Δ original : ℕ → ℝ} {S : Set ℕ}
    (data : ByrdOmojokunTangentialData P c g n H NT σ dN dT d v Δ original S) (k : ℕ) :
    data.ν * σ (k + 1) * dN k ≤ d k := by
  by_cases hzero : dN k = 0
  · have hn : n k = 0 := by
      by_contra h
      have hp := mul_pos data.bN_pos (norm_pos_iff.mpr h)
      exact (not_le_of_gt hp) ((data.normal_decrease k).1.trans_eq hzero)
    simpa only [data.model_split, hzero, mul_zero, add_zero, hn, inner_zero_right,
      neg_zero, map_zero, sub_zero] using data.tangential_nonneg k
  let dq := -⟪g k, n k⟫ - (1 / 2) * ⟪n k, H k (n k)⟫
  let threshold := sqpPenaltyThreshold data.ν (dN k) (dT k) dq
  have hd : 0 < dN k := lt_of_le_of_ne
    ((mul_nonneg data.bN_pos.le (norm_nonneg _)).trans (data.normal_decrease k).1) (Ne.symm hzero)
  have hσ : threshold ≤ σ (k + 1) := by
    rw [data.penalty_update, ite_eq_right hzero]
    change threshold ≤ sqpPenaltyUpdate data.τ₁ data.τ₂ (max (data.auxiliary k) threshold) (σ k)
    unfold sqpPenaltyUpdate
    split_ifs with h
    · exact (le_max_right _ _).trans h
    · exact (le_max_right _ _).trans (le_max_left _ _)
  rw [data.model_split]
  exact (sqpPenaltyThreshold_le_iff data.ν_lt_one hd).mp hσ

omit [NormedSpace ℝ Y] in
/-- **Theorem 15.4.22** of [conn2000trust]. Let the data of a run be given, with $c_k \to 0$. Let
$L \ge 0$ with
$$\|N_k^T g_k\| - \|N_{k+1}^T g_{k+1}\| \le L \Delta_k \text{ for } k \in S, \qquad \|N_{k+1}^T
  g_{k+1}\| = \|N_k^T g_k\| \text{ for } k \notin S.$$
Then there are $\sigma_{\max} > 0$, $\kappa > 0$ and $j$ such that
$\sigma_{k+1} = \sigma_{\max}$ and $\kappa d^T_k \le d_k$ for all $k \ge j$, and
$$\|N_k^T g_k\| \to 0.$$

Feasibility makes the normal perturbation vanish. The penalty parameter then stabilizes, and on
the stabilized tail the total predicted decrease dominates a fixed fraction of the tangential
decrease. -/
theorem theorem_15_4_22 {P : BTRParams}
    {c : ℕ → Y} {g n : ℕ → E} {H : ℕ → E →L[ℝ] E} {NT : ℕ → E →L[ℝ] Z}
    {σ dN dT d v Δ original : ℕ → ℝ} {S : Set ℕ}
    (data : ByrdOmojokunTangentialData P c g n H NT σ dN dT d v Δ original S)
    (hc : Tendsto c atTop (𝓝 0))
    {L : ℝ} (hL : 0 ≤ L)
    (hmove : ∀ k ∈ S, ‖NT k (g k)‖ - ‖NT (k + 1) (g (k + 1))‖ ≤ L * Δ k)
    (hstay : ∀ k ∉ S, ‖NT (k + 1) (g (k + 1))‖ = ‖NT k (g k)‖) :
    (∃ σmax > 0, ∃ κ > 0, ∃ j, ∀ k ≥ j, σ (k + 1) = σmax ∧ κ * dT k ≤ d k) ∧
      Tendsto (fun k => ‖NT k (g k)‖) atTop (𝓝 0) := by
  have hN (k : ℕ) (_ : 0 ≤ k) : data.bN * ‖n k‖ ≤ dN k ∧ dN k ≤ data.U :=
    ⟨(data.normal_decrease k).1, (data.normal_decrease k).2.trans (data.constraint_bound k)⟩
  obtain ⟨σmax, hσ, B₀, hB₀, j, hj⟩ := theorem_15_4_8 g n H dN dT σ data.auxiliary
    data.G_nonneg data.B_nonneg data.U_nonneg data.bN_pos data.ν_lt_one
    data.τ₁_nonneg data.τ₂_pos data.penalty_initial data.gradient_bound
    data.hessian_bound hN data.tangential_nonneg data.auxiliary_bound data.penalty_update
  let κ := data.ν * σmax / (data.ν * σmax + B₀)
  have hκ : 0 < κ := by dsimp [κ]; positivity [data.ν_pos]
  have hdom (k : ℕ) (hk : j ≤ k) : κ * dT k ≤ d k := by
    obtain ⟨hstable, hmodel⟩ := hj k hk
    have h₁ : dT k + (σmax - B₀) * dN k ≤ d k := by
      rw [data.model_split, ← hstable]
      exact hmodel
    have h₂ : data.ν * σmax * dN k ≤ d k := by
      rw [← hstable]
      exact data.model_penalty k
    exact (lemma_15_4_9 data.ν_pos hσ hB₀
      ((mul_nonneg data.bN_pos.le (norm_nonneg _)).trans (data.normal_decrease k).1)
      h₁ h₂).2
  refine ⟨⟨σmax, hσ, κ, hκ, j, fun k hk => ⟨(hj k hk).1, hdom k hk⟩⟩, ?_⟩
  have hn : Tendsto n atTop (𝓝 0) := by
    have hc' : Tendsto (fun k => ‖c k‖) atTop (𝓝 0) := tendsto_zero_iff_norm_tendsto_zero.mp hc
    refine squeeze_zero_norm' (a := fun k => ‖c k‖ / data.bN)
      (Eventually.of_forall fun k => (le_div_iff₀ data.bN_pos).mpr ?_) ?_
    · rw [mul_comm]
      exact (data.normal_decrease k).1.trans (data.normal_decrease k).2
    · simpa only [zero_div] using hc'.div_const data.bN
  apply theorem_15_4_11 data.run (mul_pos hκ data.κ_pos) data.b_pos data.β_pos
    (mul_nonneg data.C_nonneg (by positivity : 0 ≤ 1 + σmax))
    (sqpReducedGradient_perturbation g n H NT data.D_nonneg data.hessian_bound
      data.reduced_map_bound hn) ?_ ?_ hL hmove hstay
  · filter_upwards [eventually_ge_atTop j] with k hk
    simpa only [mul_assoc] using
      (mul_le_mul_of_nonneg_left (data.tangential_cauchy k) hκ.le).trans (hdom k hk)
  · filter_upwards [eventually_ge_atTop j] with k hk
    simpa only [(hj k hk).1] using data.original_error k

omit [NormedSpace ℝ Y] in
/-- **Theorem 15.4.23** of [conn2000trust], for the Byrd–Omojokun method with second-order
correction. Let the data of a run be given for the constraint values $c(x_k)$ and the merit
function $\phi_k(x) = f(x) + \sigma_{k+1} \|c(x)\|$. Let $f(x_k) \ge f_{\min}$, let
$m, \kappa_N, c_{\max}, \beta_N, \xi_N > 0$ and $L, \xi, \chi \ge 0$, and suppose that for all
$k$ and $i, j$:

* $m \|c(x_k)\| \le \|a(x_k)\|$ (uniform rank), where $a$ is the normal criticality measure;
* $\kappa_N (\|a(x_k)\| / c_{\max}) \min\{\xi_N \Delta_k, \|a(x_k)\| / \beta_N\} \le d^N_k$;
* $\mathrm{original}_k = \phi_k(x_k) - \phi_k(x_k + s_k)$, and
  $\eta_1 d_k \le \phi_k(x_k) - \phi_k(x_{k+1})$ for $k \in S$;
* for $k \in S$, $x_{k+1}$ is $x_k + s_k$ or $x_k + s_k + u_k$ with a correction
  $\|u_k\| \le \chi \Delta_k$, as in (15.4.155), and $x_{k+1} = x_k$ for $k \notin S$;
* $\|s_k\| \le \xi \Delta_k$;
* $\|a(x_i) - a(x_j)\| \le L \|x_i - x_j\|$ and $\big|\|N_i^T g_i\| - \|N_j^T g_j\|\big| \le L
  \|x_i - x_j\|$.

Then $a(x_k) \to 0$, $c(x_k) \to 0$, the conclusions of Theorem 15.4.22 hold, and
$\|N_k^T g_k\| \to 0$.

**Typo.** The printed theorem refers to the wrong algorithm. It concerns Algorithm 15.4.6, the
Byrd–Omojokun method with the second-order correction step.

The original trial gives the model agreement, and the selected trial gives the actual decrease.
The uniform rank condition transfers normal criticality to feasibility, after which the
tangential estimates apply with the same models. -/
theorem theorem_15_4_23 {P : BTRParams}
    (f : E → ℝ) (c : E → Y) (a : E → E) (x s correction g n : ℕ → E)
    (H : ℕ → E →L[ℝ] E) (NT : ℕ → E →L[ℝ] Z)
    {σ dN dT d v Δ original : ℕ → ℝ} {S : Set ℕ}
    (data : ByrdOmojokunTangentialData P (c ∘ x) g n H NT σ dN dT d v Δ original S)
    {fmin m κN cmax βN ξN L ξ χ : ℝ}
    (hm : 0 < m) (hκN : 0 < κN) (hcmax : 0 < cmax) (hβN : 0 < βN) (hξN : 0 < ξN)
    (hL : 0 ≤ L) (hξ : 0 ≤ ξ) (hχ : 0 ≤ χ)
    (hf : ∀ k, fmin ≤ f (x k))
    (hrank : ∀ k, m * ‖c (x k)‖ ≤ ‖a (x k)‖)
    (hpredN : ∀ k, κN * (‖a (x k)‖ / cmax) * min (ξN * Δ k) (‖a (x k)‖ / βN) ≤ dN k)
    (horiginal : ∀ k, original k =
      sqpMerit f c (σ (k + 1)) (x k) - sqpMerit f c (σ (k + 1)) (x k + s k))
    (haccepted : ∀ k ∈ S, P.η₁ * d k ≤ sqpMerit f c (σ (k + 1)) (x k) -
      sqpMerit f c (σ (k + 1)) (x (k + 1)))
    (hchosen : ∀ k ∈ S, x (k + 1) = x k + s k ∨ x (k + 1) = x k + s k + correction k)
    (hstep : ∀ k, ‖s k‖ ≤ ξ * Δ k)
    (hcorrection : ∀ k ∈ S, x (k + 1) = x k + s k + correction k → ‖correction k‖ ≤ χ * Δ k)
    (hreject : ∀ k ∉ S, x (k + 1) = x k)
    (haLip : ∀ i j, ‖a (x i) - a (x j)‖ ≤ L * ‖x i - x j‖)
    (hgLip : ∀ i j, |‖NT i (g i)‖ - ‖NT j (g j)‖| ≤ L * ‖x i - x j‖) :
    Tendsto (fun k => a (x k)) atTop (𝓝 0) ∧ Tendsto (c ∘ x) atTop (𝓝 0) ∧
      (∃ σmax > 0, ∃ κ > 0, ∃ j, ∀ k ≥ j, σ (k + 1) = σmax ∧ κ * dT k ≤ d k) ∧
      Tendsto (fun k => ‖NT k (g k)‖) atTop (𝓝 0) := by
  have hσmono : Monotone σ := monotone_nat_of_le_succ fun k => by
    rw [data.penalty_update, sqpPenaltyUpdate]
    split_ifs <;> first
      | exact le_rfl
      | exact (le_add_of_nonneg_right data.τ₂_pos.le).trans
          ((le_max_right _ _).trans (le_max_right _ _))
  have hσpos (k : ℕ) : 0 < σ (k + 1) :=
    data.penalty_initial.trans_le (hσmono (Nat.zero_le _))
  have htravel (k : ℕ) (hk : k ∈ S) : ‖x k - x (k + 1)‖ ≤ (ξ + χ) * Δ k := by
    rw [norm_sub_rev]
    rcases hchosen k hk with h | h
    · rw [h, add_sub_cancel_left]
      exact (hstep k).trans (by linarith only [mul_nonneg hχ (data.run.radius_pos k).le])
    · rw [h, show x k + s k + correction k - x k = s k + correction k by abel]
      exact (norm_add_le _ _).trans (by
        linarith only [hstep k, hcorrection k hk h,
          show (ξ + χ) * Δ k = ξ * Δ k + χ * Δ k by ring])
  have hscale (k : ℕ) (hk : k ∈ S) : L * ‖x k - x (k + 1)‖ ≤ (L * (ξ + χ)) * Δ k := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (htravel k hk) hL
  have hL' := mul_nonneg hL (add_nonneg hξ hχ)
  have ha : Tendsto (fun k => a (x k)) atTop (𝓝 0) := by
    refine sqp_normal_criticality_of_accepted_decrease f c a x s (fun k => σ (k + 1)) d Δ S
      P.eta₁_pos P.eta₂_lt_one (mul_pos data.ν_pos hκN) hcmax hβN hξN data.C_nonneg hL'
      data.penalty_initial P.gamma₁_pos
      (P.gamma₁_pos.le.trans P.gamma₁_le_gamma₂) P.gamma₂_lt_one hf
      (fun k => hσmono (Nat.zero_le _)) (fun _ _ hij => hσmono (Nat.succ_le_succ hij))
      data.run.radius_pos ?_ ?_ data.run.radius_lower haccepted ?_
      (fun k hk => ⟨hreject k hk, data.run.radius_rejected k hk⟩) ?_
    · intro k
      have hp := mul_le_mul_of_nonneg_left (hpredN k) (mul_nonneg data.ν_pos.le (hσpos k).le)
      exact (by simpa only [mul_left_comm, mul_comm, mul_assoc] using
        hp.trans (data.model_penalty k))
    · intro k
      rw [← abs_neg, neg_sub, show sqpMerit f c (σ (k + 1)) (x k) - d k -
        sqpMerit f c (σ (k + 1)) (x k + s k) = original k - d k by rw [horiginal]; ring]
      simpa only [mul_assoc] using data.original_error k
    · intro k hk
      apply data.run.very_successful k
      simpa only [horiginal, Optimization.reductionRatio] using hk
    · intro k hk
      exact ((norm_sub_norm_le _ _).trans (haLip k (k + 1))).trans (hscale k hk)
  have hc : Tendsto (c ∘ x) atTop (𝓝 0) :=
    corollary_15_4_20 (c ∘ x) (a ∘ x) hm hrank ha
  refine ⟨ha, hc, theorem_15_4_22 data hc hL' ?_ ?_⟩
  · intro k hk
    exact ((le_abs_self _).trans (hgLip k (k + 1))).trans (hscale k hk)
  · intro k hk
    have h := hgLip k (k + 1)
    rw [hreject k hk, sub_self, norm_zero, mul_zero] at h
    exact (sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm h (abs_nonneg _)))).symm

omit [InnerProductSpace ℝ E] in
/-- **Theorem 15.4.24** of [conn2000trust]. Let $E$ be a real normed space, and let $x_k$, steps
$s_k$, corrections $u_k$, standard normal and tangential steps $n_k, t_k \to 0$, multiplier
errors $e_k \ge 0$ with $e_k \to 0$, and radii $\Delta_k > 0$ be given. Let $M, D \ge 0$ and
$r, r_0, \gamma, \xi_N, \xi_T > 0$ with $(M + D) \cdot 2r \le 1/2$. Suppose that
$\|x_k - x_*\| < r$ for infinitely many $k$, $\gamma \Delta_k \le \Delta_{k+1}$ for all $k$, and
eventually $\Delta_k \le r_0$ implies $\Delta_k \le \Delta_{k+1}$. Suppose also that, for all
large $k$ with $\|x_k - x_*\| < r$, $\|n_k\| \le \xi_N \Delta_k$ and
$\|t_k\| \le \xi_T \Delta_k$, the next iterate is $x_k + s_k$ or $x_k + s_k + u_k$, and
$$\|x_k + s_k - x_*\| \le M (\|x_k - x_*\| + e_k) \|x_k - x_*\|, \qquad \|u_k\| \le D (\|x_k -
  x_*\| + e_k) \|x_k - x_*\|.$$
Then $x_k \to x_*$ Q-superlinearly. If moreover $e_k \le C \|x_k - x_*\|$ eventually for some
$C \ge 0$, then $x_k \to x_*$ Q-quadratically.

The nonshrinkage rule for small radii keeps the radius bounded below, so the vanishing standard
steps fit in their trust regions. The trapping and step bounds are hypotheses. -/
theorem theorem_15_4_24 (x s u nStandard tStandard : ℕ → E) (xstar : E) (ey Δ : ℕ → ℝ)
    {M D r r₀ γ ξN ξT : ℝ} (hM : 0 ≤ M) (hD : 0 ≤ D) (hr : 0 < r) (hr₀ : 0 < r₀)
    (hγ : 0 < γ) (hξN : 0 < ξN) (hξT : 0 < ξT)
    (hey : ∀ k, 0 ≤ ey k) (hylim : Tendsto ey atTop (𝓝 0))
    (hvisit : ∃ᶠ k in atTop, ‖x k - xstar‖ < r)
    (hΔ : ∀ k, 0 < Δ k) (hnext : ∀ k, γ * Δ k ≤ Δ (k + 1))
    (hkeep : ∀ᶠ k in atTop, Δ k ≤ r₀ → Δ k ≤ Δ (k + 1))
    (hn : Tendsto nStandard atTop (𝓝 0)) (ht : Tendsto tStandard atTop (𝓝 0))
    (hlocal : ∀ᶠ k in atTop, ‖x k - xstar‖ < r →
      ‖nStandard k‖ ≤ ξN * Δ k → ‖tStandard k‖ ≤ ξT * Δ k →
      (x (k + 1) = x k + s k ∨ x (k + 1) = x k + s k + u k) ∧
      ‖x k + s k - xstar‖ ≤ M * (‖x k - xstar‖ + ey k) * ‖x k - xstar‖ ∧
      ‖u k‖ ≤ D * (‖x k - xstar‖ + ey k) * ‖x k - xstar‖)
    (hsmall : (M + D) * (r + r) ≤ 1 / 2) :
    Chapter03.ConvergesQSuperlinearly x xstar ∧
      ((∃ C ≥ 0, ∀ᶠ k in atTop, ey k ≤ C * ‖x k - xstar‖) →
        Chapter03.ConvergesQQuadratically x xstar) := by
  obtain ⟨K, hK⟩ := eventually_atTop.mp hkeep
  let floor := min (Δ K) (γ * r₀)
  have hfloor : 0 < floor := lt_min (hΔ K) (mul_pos hγ hr₀)
  have hbound (k : ℕ) (hk : K ≤ k) : floor ≤ Δ k := by
    induction k, hk using Nat.le_induction with
    | base => exact min_le_left _ _
    | succ k hk ih =>
      by_cases hh : Δ k ≤ r₀
      · exact ih.trans (hK k hk hh)
      · exact (min_le_right _ _).trans
          ((mul_le_mul_of_nonneg_left (le_of_not_ge hh) hγ.le).trans (hnext k))
  have hn' := tendsto_zero_iff_norm_tendsto_zero.mp hn
  have ht' := tendsto_zero_iff_norm_tendsto_zero.mp ht
  apply theorem_15_4_15 x s u xstar ey hM hD hr hey hylim hvisit ?_ hsmall
  filter_upwards [hlocal, eventually_ge_atTop K,
    hn'.eventually_lt_const (mul_pos hξN hfloor), ht'.eventually_lt_const (mul_pos hξT hfloor)]
    with k hk hK' hn₀ ht₀ hx
  exact hk hx (hn₀.le.trans (mul_le_mul_of_nonneg_left (hbound k hK') hξN.le))
    (ht₀.le.trans (mul_le_mul_of_nonneg_left (hbound k hK') hξT.le))

/-- **Theorem 15.4.25** of [conn2000trust], for the second-order Byrd–Omojokun method. Let $z_k$ lie
eventually in a compact set $U$ of a topological space, and let every cluster point of $(z_k)$
in $U$ be one of finitely many points $z^*_i$, $i \in \iota$, with $\iota$ nonempty. Let the
curvature function be continuous at each $z^*_i$, and let each $z^*_i$ be first-order critical.
Let $a, b, \kappa, \beta > 0$ and $C \ge 0$. Suppose that the merit values $v_k \ge 0$ are
nonincreasing, $\Delta_k > 0$, $\gamma_1 \Delta_k \le \Delta_{k+1}$, and
$\Delta_{k+1} \le \gamma_2 \Delta_k$ for $k \notin S$, and that:

* for $k$ in the set of normal iterations, $a \Delta_k \le \|n_k\|$ and
  $|\mathrm{original}_k - d_k| \le C \Delta_k^2$;
* $b \|n_k\| \le d^N_k$, $\kappa d^N_k \le d_k$ and $\kappa d^T_k \le d_k$ for all $k$;
* for the other $k$, $\beta (-\mathrm{curvature}(z_k)) \Delta_k^2 \le d^T_k$, and for every
  $\epsilon > 0$ there is $r > 0$ such that eventually $\Delta_k \le r$ implies
  $|\mathrm{corrected}_k - d_k| \le \epsilon \Delta_k^2$;
* $\eta_1 d_k \le v_k - v_{k+1}$ for $k \in S$;
* $k \in S$ and $\Delta_k \le \Delta_{k+1}$ if $\mathrm{original}_k / d_k \ge \eta_2$, and, for
  $k$ not a normal iteration, also if $\mathrm{original}_k / d_k \ge \eta_1$, or if
  $\mathrm{original}_k / d_k < \eta_1$ and $\mathrm{corrected}_k / d_k \ge \eta_2$.

Then some $z^*_i$ is first-order critical with $\mathrm{curvature}(z^*_i) \ge 0$.

**Correction.** The argument uses the cluster point of maximal curvature, with a corrected
curvature margin. The coverage of the tail by the finitely many cluster points is a hypothesis;
relative compactness of the iterates supplies it.

The branch with a large normal step and the branch with negative curvature give the sufficient
decrease. The original or the corrected acceptance ratio decides which trial is accepted. -/
theorem theorem_15_4_25 {X ι : Type*} [TopologicalSpace X] [Fintype ι] [Nonempty ι]
    {P : BTRParams} (z : ℕ → X) (zstar : ι → X) (curvature : X → ℝ)
    (firstOrder : ι → Prop) (v Δ d dN dT nNorm original corrected : ℕ → ℝ)
    (S normal : Set ℕ) {U : Set X}
    (hU : IsCompact U) (hmem : ∀ᶠ k in atTop, z k ∈ U)
    (hcluster : ∀ x ∈ U, MapClusterPt x atTop z → x ∈ Set.range zstar)
    (hcont : ∀ i, ContinuousAt curvature (zstar i))
    (hfirst : ∀ i, firstOrder i)
    {a b κ β C : ℝ} (ha : 0 < a) (hb : 0 < b) (hκ : 0 < κ) (hβ : 0 < β) (hC : 0 ≤ C)
    (hv : ∀ k, 0 ≤ v k) (hmono : Antitone v) (hΔ : ∀ k, 0 < Δ k)
    (hnext : ∀ k, P.γ₁ * Δ k ≤ Δ (k + 1))
    (hrej : ∀ k ∉ S, Δ (k + 1) ≤ P.γ₂ * Δ k)
    (hnormal : ∀ k ∈ normal, a * Δ k ≤ nNorm k)
    (hN : ∀ k, b * nNorm k ≤ dN k)
    (hNmodel : ∀ k, κ * dN k ≤ d k)
    (hT : ∀ k ∉ normal, β * (-curvature (z k)) * Δ k ^ 2 ≤ dT k)
    (hTmodel : ∀ k, κ * dT k ≤ d k)
    (herror : ∀ k ∈ normal, |original k - d k| ≤ C * Δ k ^ 2)
    (hcorrected : ∀ ε > 0, ∃ r > 0, ∀ᶠ k in atTop, k ∉ normal → Δ k ≤ r →
      |corrected k - d k| ≤ ε * Δ k ^ 2)
    (hmerit : ∀ k ∈ S, P.η₁ * d k ≤ v k - v (k + 1))
    (hvery : ∀ k, P.η₂ ≤ original k / d k → k ∈ S ∧ Δ k ≤ Δ (k + 1))
    (haccepted : ∀ k ∉ normal, P.η₁ ≤ original k / d k → k ∈ S ∧ Δ k ≤ Δ (k + 1))
    (hcor : ∀ k ∉ normal, original k / d k < P.η₁ →
      P.η₂ ≤ corrected k / d k → k ∈ S ∧ Δ k ≤ Δ (k + 1)) :
    ∃ i, firstOrder i ∧ 0 ≤ curvature (zstar i) := by
  refine theorem_15_4_16 firstOrder (curvature ∘ zstar) (curvature ∘ z) v Δ S
    P.gamma₁_pos (P.gamma₁_pos.le.trans P.gamma₁_le_gamma₂) P.gamma₂_lt_one
    hfirst (sqp_curvature_tail_of_compact z zstar curvature hU hmem hcluster hcont)
    hv hmono hΔ hnext hrej ?_
  refine sqp_secondOrder_correction_progress (P := P) (curvature ∘ z) v Δ d original corrected S normal
    (mul_pos (mul_pos hκ hb) ha) (mul_pos hκ hβ) hC hΔ ?_ ?_
    herror hcorrected hmerit hvery haccepted hcor
  · intro k hk
    have h := mul_le_mul_of_nonneg_left (hnormal k hk) hb.le
    have hh := mul_le_mul_of_nonneg_left (h.trans (hN k)) hκ.le
    linarith only [hh, hNmodel k,
      show κ * b * a * Δ k = κ * (b * (a * Δ k)) by ring]
  · intro k hk
    have h := mul_le_mul_of_nonneg_left (hT k hk) hκ.le
    exact (by simpa only [Function.comp_apply, mul_assoc] using h.trans (hTmodel k))

end ConnGouldToint.Chapter15
