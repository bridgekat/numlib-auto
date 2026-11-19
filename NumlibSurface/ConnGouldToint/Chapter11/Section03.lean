/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.ConnGouldToint.Chapter11.Section02
import NumlibSurface.ConnGouldToint.Chapter10.Section01

/-!
# Conn, Gould and Toint, Section 11.3: Nonmonotone and corrected nonsmooth iterations

This module formalizes two variants of the nonsmooth trust-region method from Section 11.3 of
[conn2000trust]. Theorem 11.3.1 applies the nonmonotone acceptance rule of Algorithm 10.1.1 to a
locally Lipschitz objective. The cumulative rule bounds the sum of the accepted predicted decreases,
and near a nonstationary limit point the capped expansion rule and uniform model agreement keep the
radius away from zero, so every limit point is Clarke stationary. Algorithm 11.3.1 adds to each
trial step $s_k$ a correction $c_k$ that does not increase the objective at $x_k + s_k$, but keeps
the predicted decrease of the original step $s_k$ in the ratio. Theorem 11.3.2 shows that every
limit point of such a run is Clarke stationary.

The local radius argument of Lemma 11.2.4 is isolated in
`ConnGouldToint.Chapter11.radius_floor_of_local_expansion`, which also covers corrected steps. The
nonmonotone run is `ConnGouldToint.Chapter10.NonmonotoneRun` of
`NumlibSurface.ConnGouldToint.Chapter10.Section01`. The optional correction steps of this module are
also used by Algorithms 15.3.1 and 16.2.1.

## Main definitions

* Algorithms 15.3.1 and 16.2.1, Step 2, `ConnGouldToint.Chapter11.selectOptionalCorrection` and
  `ConnGouldToint.Chapter11.OptionalCorrectionStep`: a proposed correction is kept exactly when it
  does not increase the objective at the original trial.
* Algorithm 11.3.1, `ConnGouldToint.Chapter11.NonsmoothCorrectionRun`: an infinite run with
  corrections and the original prediction.
* Algorithms 11.3.1, 15.3.1 and 16.2.1,
  `ConnGouldToint.Chapter11.NonsmoothCorrectionRun.ofOptionalCorrectionSteps`: optional correction
  steps give a run of Algorithm 11.3.1.

## Main results

* Lemma 11.2.4 and Theorems 11.3.1–11.3.2,
  `ConnGouldToint.Chapter11.radius_floor_of_local_expansion`: forced expansion at small radii near
  $z$ gives a positive lower bound on the radii near $z$.
* Theorem 11.3.1, `ConnGouldToint.Chapter11.theorem_11_3_1`: every limit point of a nonmonotone
  nonsmooth run is Clarke stationary.
* Algorithms 11.3.1, 15.3.1 and 16.2.1,
  `ConnGouldToint.Chapter11.OptionalCorrectionStep.selected_bounds`: the selected correction
  satisfies the enlarged radius and does not increase the objective.
* Algorithms 11.3.1, 15.3.1 and 16.2.1,
  `ConnGouldToint.Chapter11.OptionalCorrectionStep.original_ratio_le`: with the original prediction,
  the selected correction does not decrease the ratio.
* Theorem 11.3.2, `ConnGouldToint.Chapter11.theorem_11_3_2`: every limit point of a run of Algorithm
  11.3.1 is Clarke stationary.

## Implementation notes

* The steps satisfy the explicit bound $\|s_k\| \le \Delta_k$ in the norm of $E$, and the corrected
  steps satisfy $\|s_k + c_k\| \le \tau \Delta_k$ for a fixed enlargement $\tau$.

## Deviations from the source

* **Theorems 11.3.1 and 11.3.2** (correction). Both assume uniform normalized agreement of the
  models (11.2.1), as the corrected Lemma 11.2.3 does. See `ConnGouldToint.Chapter11.theorem_11_3_1`
  and `ConnGouldToint.Chapter11.theorem_11_3_2`.
* **Algorithm 11.3.1** (correction). The very-successful expansion uses the capped lower bound
  from the corrected (11.1.16), keeping the update feasible at the maximum radius.
* **Algorithms 15.3.1 and 16.2.1** (generalization). The optional correction takes arbitrary
  base and correction models. The proposal must reduce its own model, meet the enlarged
  radius, and leave the trial objective no larger. The denominator uses the base prediction.
-/

open Filter Topology Metric Set Optimization
open ConnGouldToint.Chapter10

namespace ConnGouldToint.Chapter11

variable {E P : Type*} [NormedAddCommGroup E]

/-- **Lemma 11.2.4** of [conn2000trust], radius estimate, as used in Theorems 11.3.1 and 11.3.2. Let
$E$ be a normed additive group, let $(x_k)$ be a sequence in $E$ and $(\Delta_k)$ a sequence of
positive radii, and let $\varepsilon, T, K, \gamma_1 > 0$ and $\gamma_3 > 1$. Assume that
$\Delta_{k+1} \ge \gamma_1 \Delta_k$ and $\|x_{k+1} - x_k\| \le K \Delta_k$ for all $k$, and
that $\Delta_{k+1} \ge \gamma_3 \Delta_k$ whenever $\|x_k - z\| < \varepsilon$ and
$\Delta_k < T$. Then there is $r > 0$ with $\Delta_k \ge r$ for every $k$ with
$\|x_k - z\| < \varepsilon/2$.

The constant $K$ allows composite steps that are bounded by a fixed multiple of the radius.

**Reading.** Abstract expansion and step-length estimates on a normed additive group give a positive
local floor.
-/
theorem radius_floor_of_local_expansion {x : ℕ → E} {z : E} {Δ : ℕ → ℝ}
    {ε T K γ₁ γ₃ : ℝ} (hε : 0 < ε) (hT : 0 < T) (hK : 0 < K)
    (hγ₁ : 0 < γ₁) (hγ₃ : 1 < γ₃)
    (hΔ : ∀ k, 0 < Δ k) (hnext : ∀ k, γ₁ * Δ k ≤ Δ (k + 1))
    (hstep : ∀ k, dist (x k) (x (k + 1)) ≤ K * Δ k)
    (hexp : ∀ k, x k ∈ ball z ε → Δ k < T → γ₃ * Δ k ≤ Δ (k + 1)) :
    ∃ r > 0, ∀ k, x k ∈ ball z (ε / 2) → r ≤ Δ k := by
  let C := max (K / γ₁) (K / (γ₃ - 1))
  have hC₁ : K / γ₁ ≤ C := le_max_left _ _
  have hC₂ : K / (γ₃ - 1) ≤ C := le_max_right _ _
  have hC : 0 < C := (div_pos hK hγ₁).trans_le hC₁
  have hCexp : C + K ≤ C * γ₃ := by
    have h := (div_le_iff₀ (sub_pos.mpr hγ₃)).mp hC₂
    linarith only [h]
  let D := min (Δ 0) (γ₁ * T)
  have hD : 0 < D := lt_min (hΔ 0) (mul_pos hγ₁ hT)
  let bad (k : ℕ) := Δ k < D ∧ dist (x k) z + C * Δ k < ε
  have hback (k : ℕ) (hn : bad (k + 1)) : bad k := by
    have hsmall : Δ k < T := lt_of_mul_lt_mul_left
      ((hnext k).trans_lt (hn.1.trans_le (min_le_right _ _))) hγ₁.le
    have hpre : K * Δ k ≤ C * Δ (k + 1) := by
      have h := (le_div_iff₀ hγ₁).mpr (by simpa only [mul_comm] using hnext k)
      calc
        _ ≤ K * (Δ (k + 1) / γ₁) := mul_le_mul_of_nonneg_left h hK.le
        _ = (K / γ₁) * Δ (k + 1) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hC₁ (hΔ (k + 1)).le
    have hdist := (dist_triangle (x k) (x (k + 1)) z).trans (add_le_add (hstep k) le_rfl)
    have hnear : x k ∈ ball z ε := by
      rw [mem_ball]
      linarith only [hdist, hpre, hn.2]
    have hg := hexp k hnear hsmall
    have hnondec : Δ k ≤ Δ (k + 1) :=
      (le_mul_of_one_le_left (hΔ k).le hγ₃.le).trans hg
    have hbudget : (C + K) * Δ k ≤ C * Δ (k + 1) := calc
      _ ≤ (C * γ₃) * Δ k := mul_le_mul_of_nonneg_right hCexp (hΔ k).le
      _ = C * (γ₃ * Δ k) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hg hC.le
    exact ⟨hnondec.trans_lt hn.1, by linarith only [hdist, hbudget, hn.2]⟩
  have hgood (k : ℕ) : ¬ bad k := by
    induction k with
    | zero => exact fun h ↦ not_lt_of_ge (min_le_left _ _) h.1
    | succ k ih => exact fun h ↦ ih (hback k h)
  refine ⟨min D (ε / (2 * C)), lt_min hD (div_pos hε (by positivity)), ?_⟩
  intro k hk
  by_contra! hr
  have hdist := mem_ball.1 hk
  have hrD : Δ k < D := hr.trans_le (min_le_left _ _)
  have hrε := (lt_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hC)).mp
    (hr.trans_le (min_le_right _ _))
  exact hgood k ⟨hrD, by linarith only [hdist, hrε]⟩

/-- **Proofs of Theorems 11.3.1–11.3.2** of [conn2000trust].

**Reading.** Abstract entry-and-exit argument with an explicit accepted-decrease budget.
-/
private theorem no_noncritical_cluster_of_predicted_sum {x : ℕ → E} {z : E}
    {S : Set ℕ} {pred Δ : ℕ → ℝ} {ε r d γ : ℝ}
    (hε : 0 < ε) (hr : 0 < r) (hd : 0 < d) (hγ : 0 ≤ γ) (hγ' : γ < 1)
    (hfloor : ∀ k, x k ∈ ball z ε → r ≤ Δ k)
    (hpred : ∀ k, x k ∈ ball z ε → d ≤ pred k)
    (hsum : Summable (acceptedDecrease S pred))
    (hstay : ∀ k ∉ S, x (k + 1) = x k) (hshrink : ∀ k ∉ S, Δ (k + 1) ≤ γ * Δ k)
    {j : ℕ → ℕ} (hj : StrictMono j) (hz : Tendsto (x ∘ j) atTop (𝓝 z)) : False := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hsum.tendsto_atTop_zero.eventually_lt_const hd)
  obtain ⟨i, hi, hiz⟩ := ((hj.tendsto_atTop.eventually_ge_atTop N).and
    (hz.eventually (ball_mem_nhds z hε))).exists
  let n := j i
  have hfail (k : ℕ) (hk : N ≤ k) (hx : x k ∈ ball z ε) : k ∉ S := by
    intro hs
    have h := hN k hk
    classical
    rw [acceptedDecrease, ite_eq_left hs] at h
    exact h.not_ge (hpred k hx)
  have htail (p : ℕ) : x (n + p) = x n ∧ Δ (n + p) ≤ γ ^ p * Δ n := by
    induction p with
    | zero => simp
    | succ p ih =>
      have hf := hfail (n + p) (hi.trans (Nat.le_add_right _ _)) (ih.1.symm ▸ hiz)
      refine ⟨?_, ?_⟩
      · rw [Nat.add_succ, hstay _ hf, ih.1]
      · rw [Nat.add_succ, pow_succ, mul_comm (γ ^ p), mul_assoc]
        exact (hshrink _ hf).trans (mul_le_mul_of_nonneg_left ih.2 hγ)
  have ht : Tendsto (fun p : ℕ ↦ γ ^ p * Δ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hγ hγ').mul_const (Δ n)
  obtain ⟨p, hp⟩ := (ht.eventually_lt_const hr).exists
  exact hp.not_ge ((hfloor _ ((htail p).1.symm ▸ hiz)).trans (htail p).2)

private theorem summable_of_bounded_accepted_decrease {S : Set ℕ} {pred : ℕ → ℝ} {B : ℝ}
    (hp : ∀ k, 0 ≤ pred k)
    (hbound : ∀ n, ∑ k ∈ Finset.range n, acceptedDecrease S pred k ≤ B) :
    Summable (acceptedDecrease S pred) := by
  apply summable_of_sum_range_le (c := B) ?_ hbound
  intro k
  classical
  by_cases hk : k ∈ S
  · simpa [acceptedDecrease, hk] using hp k
  · simp [acceptedDecrease, hk]

variable [InnerProductSpace ℝ E] [CompleteSpace E]

/-- **Theorem 11.3.1** of [conn2000trust]. Let $E$ be a real Hilbert space, let
$f : E \to \mathbb{R}$ be bounded below, and consider a run of the nonmonotone Algorithm 10.1.1
with parameters $B$ and model parameters $p_k$ such that $m(x_k, p_k, s) = m_k(x_k + s)$ for all
$k$ and $s$. Let the parameters $Q$ satisfy (11.1.15), and assume that $\|s_k\| \le \Delta_k$
and that $\Delta_{k+1} \ge \min\{\gamma_3 \Delta_k, \Delta_{\max}\}$ whenever the ratio of
iteration $k$ is at least $\eta_2$, both with the constants of $Q$. Let $z$ be the limit of a
subsequence $x_{j(k)}$, let $f$ be Lipschitz on a neighborhood of $z$, and let the models match
the value of $f$ (11.1.1) and have uniform normalized agreement with $f$ at $z$. Let
$\varepsilon, \delta, \kappa > 0$ with
$$\kappa \|g^*(x_k)\| \min\{\delta, \Delta_k\} \le m_k(x_k) - m_k(x_k + s_k) \quad
  \text{whenever } \|x_k - z\| < \varepsilon.$$
Then $z$ is Clarke stationary: $0 \in \partial f(z)$.

**Correction.** The source assumes only pointwise model agreement. The statement assumes uniform
normalized agreement, as in the corrected Lemma 11.2.3.

The cumulative nonmonotone acceptance rule bounds the sum of the accepted predicted decreases.
Near a nonstationary limit point, the capped expansion rule and the uniform agreement prevent
the radius from tending to zero. -/
theorem theorem_11_3_1 {Q : NonsmoothTRParams} {f : E → ℝ} {m : E → P → E → ℝ}
    {B : Chapter06.BTRParams} (run : NonmonotoneRun f B)
    (parameter : ℕ → P) (hmodel : ∀ k s, m (run.x k) (parameter k) s =
      run.model k (run.x k + s))
    (hstep : ∀ k, ‖run.s k‖ ≤ run.Δ k)
    (hexpand : ∀ k, Q.η₂ ≤ run.ratio k → min (Q.γ₃ * run.Δ k) Q.Δmax ≤ run.Δ (k + 1))
    (hlower : BddBelow (range f))
    {z : E} {U : Set E} {L : NNReal} (hU : U ∈ 𝓝 z) (hL : LipschitzOnWith L f U)
    (hmatch : modelValueMatches f m) (herr : UniformNormalizedModelAgreementAt f m z)
    {ε δ κ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hκ : 0 < κ)
    (hAA : ∀ k, run.x k ∈ ball z ε → κ * ‖minimumNormSubgradient f (run.x k)‖ *
      min δ (run.Δ k) ≤ run.predictedDecrease k)
    {j : ℕ → ℕ} (hj : StrictMono j) (hz : Tendsto (run.x ∘ j) atTop (𝓝 z)) :
    (0 : E) ∈ clarkeSubgradient f z := by
  by_contra hn
  obtain ⟨e, T, he, hT, hforce⟩ :=
    lemma_11_2_3 hU hL hn hmatch herr Q.eta₂_lt_one hκ hδ
  let e₀ := min e ε
  let T₀ := min T (Q.Δmax / Q.γ₃)
  have hγ₃ : 0 < Q.γ₃ := zero_lt_one.trans Q.gamma₃_gt_one
  have hnext (k : ℕ) : B.γ₁ * run.Δ k ≤ run.Δ (k + 1) := by
    have hu := run.radius_update k
    by_cases h₂ : B.η₂ ≤ run.ratio k
    · exact (mul_le_of_le_one_left (run.delta_pos k).le
        (B.gamma₁_le_gamma₂.trans B.gamma₂_lt_one.le)).trans (hu.very_successful h₂)
    by_cases h₁ : B.η₁ ≤ run.ratio k
    · exact (mul_le_mul_of_nonneg_right B.gamma₁_le_gamma₂ (run.delta_pos k).le).trans
        (hu.successful h₁ (lt_of_not_ge h₂)).1
    · exact (hu.unsuccessful (lt_of_not_ge h₁)).1
  have hmove (k : ℕ) : dist (run.x k) (run.x (k + 1)) ≤ 1 * run.Δ k := by
    by_cases hs : k ∈ run.successful
    · rw [run.accepted_update k hs, dist_comm, dist_eq_norm, add_sub_cancel_left, one_mul]
      exact hstep k
    · rw [run.rejected_update k hs, dist_self, one_mul]
      exact (run.delta_pos k).le
  obtain ⟨r, hr, hfloor⟩ := radius_floor_of_local_expansion (lt_min he hε)
    (lt_min hT (div_pos Q.radiusMax_pos hγ₃)) zero_lt_one B.gamma₁_pos Q.gamma₃_gt_one
    run.delta_pos hnext hmove (ε := e₀) (T := T₀) (by
      intro k hk hd
      have ha := hforce (run.x k) (ball_subset_ball (min_le_left _ _) hk) (parameter k)
        (run.Δ k) (run.delta_pos k) (hd.trans_le (min_le_left _ _)) (run.s k) (hstep k) (by
          simpa only [hmodel, add_zero, NonmonotoneRun.predictedDecrease] using
            hAA k (ball_subset_ball (min_le_right _ _) hk))
      simp only [hmodel, add_zero] at ha
      have hr := hexpand k (ha.trans (le_max_right _ _))
      have hcap : Q.γ₃ * run.Δ k ≤ Q.Δmax := by
        rw [mul_comm]
        exact (le_div_iff₀ hγ₃).mp (hd.le.trans (min_le_right _ _))
      rw [min_eq_left hcap] at hr
      exact hr)
  obtain ⟨eg, a, heg, ha, hg⟩ := lemma_11_1_2 hU hL hn
  let e₁ := min (e₀ / 2) (min eg ε)
  have he₁ : 0 < e₁ := lt_min (half_pos (lt_min he hε)) (lt_min heg hε)
  let d := κ * a * min δ r
  have hd : 0 < d := mul_pos (mul_pos hκ ha) (lt_min hδ hr)
  have hpred (k : ℕ) (hk : run.x k ∈ ball z e₁) : d ≤ run.predictedDecrease k := by
    have h₁ := hfloor k (ball_subset_ball (min_le_left _ _) hk)
    have h₂ := hg (run.x k) (ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _)) hk)
    have h₃ := hAA k (ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _)) hk)
    exact (mul_le_mul (mul_le_mul_of_nonneg_left h₂ hκ.le) (min_le_min le_rfl h₁)
      (le_min hδ.le hr.le) (by positivity)).trans h₃
  obtain ⟨F, hF⟩ := hlower
  have hsum : Summable (acceptedDecrease run.successful run.predictedDecrease) := by
    apply summable_of_bounded_accepted_decrease (B := (f (run.x 0) - F) / B.η₁)
      (fun k ↦ (run.predicted_pos k).le)
    intro n
    apply (le_div_iff₀ B.eta₁_pos).mpr
    cases n with
    | zero => simpa using sub_nonneg.mpr (hF (mem_range_self (run.x 0)))
    | succ k =>
      have hc := accepted_predicted_sum_le run.successful (fun i ↦ f (run.x i))
        (fun i ↦ f (run.x i + run.s i)) run.predictedDecrease run.reference
        run.reference_schedule.1 run.predicted_pos
        (fun i hi ↦ (run.accepted_iff i).mp hi)
        (fun i hi ↦ congrArg f (run.accepted_update i hi))
        (fun i hi ↦ congrArg f (run.rejected_update i hi)) k
      rw [mul_comm]
      exact hc.trans
        (sub_le_sub_left (hF (mem_range_self (run.x (k + 1)))) _)
  exact no_noncritical_cluster_of_predicted_sum he₁ hr hd
    (B.gamma₁_pos.trans_le B.gamma₁_le_gamma₂).le B.gamma₂_lt_one
    (fun k hk ↦ hfloor k (ball_subset_ball (min_le_left _ _) hk)) hpred hsum
    run.rejected_update (fun k hk ↦ ((run.radius_update k).unsuccessful
      (lt_of_not_ge (fun h ↦ hk ((run.accepted_iff k).mpr h)))).2) hj hz


/-- **Algorithms 15.3.1 and 16.2.1** of [conn2000trust], Steps 2a–2b. The **selected correction**
for a trial $x + s$ and an optional proposal $d$ is $d$ if a proposal exists and
$f(x + s + d) \le f(x + s)$, and $0$ otherwise.

So a skipped or rejected correction is zero.

**Reading.** Abstracts the model-specific objective test to any objective and optional proposed
step.
-/
noncomputable def selectOptionalCorrection (f : E → ℝ) (x s : E) (proposal : Option E) : E :=
  match proposal with
  | none => 0
  | some d => if f (x + s + d) ≤ f (x + s) then d else 0

/-- **Algorithms 15.3.1 and 16.2.1** of [conn2000trust], Step 2. An **optional correction step** at
$x$ with trial step $s$, radius $\Delta \ge 0$ and enlargement $\tau > 1$ consists of the facts
that $p(s) \le \Delta$, that the original step meets the decrease benchmark
$0 \le r \le m(0) - m(s)$, that every proposed correction $d$ satisfies
$m_{CS}(d) \le m_{CS}(0)$ and $p(s + d) \le \tau \Delta$, and that the correction is the
selected correction.

Here $m$ is the model of the trial step, $m_{CS}$ the model of the correction, $p$ the
trust-region norm, and $r$ the current sufficient-decrease benchmark. A proposed correction must
reduce its own model and fit in the enlarged radius before the comparison of the objective
values.

**Correction.** Abstract base and correction models and a supplied decrease benchmark.
-/
structure OptionalCorrectionStep (f m mCS : E → ℝ) (p : E → ℝ)
    (x s : E) (Δ τ required : ℝ) (proposal : Option E) (correction : E) : Prop where
  /-- The radius is nonnegative: $\Delta \ge 0$. -/
  radius_nonneg : 0 ≤ Δ
  /-- The enlargement factor is larger than one: $\tau > 1$. -/
  enlargement_gt_one : 1 < τ
  /-- The original step lies in the trust region: $p(s) \le \Delta$. -/
  original_radius : p s ≤ Δ
  /-- The decrease benchmark is nonnegative: $r \ge 0$. -/
  required_nonneg : 0 ≤ required
  /-- The original step meets the decrease benchmark: $r \le m(0) - m(s)$. -/
  original_decrease : required ≤ m 0 - m s
  /-- Every proposed correction $d$ reduces its model, $m_{CS}(d) \le m_{CS}(0)$, and satisfies
  $p(s + d) \le \tau \Delta$. -/
  proposal_valid : ∀ d, proposal = some d → mCS d ≤ mCS 0 ∧ p (s + d) ≤ τ * Δ
  /-- The correction is the selected correction for the proposal. -/
  selected : correction = selectOptionalCorrection f x s proposal

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- **Algorithms 11.3.1, 15.3.1 and 16.2.1** of [conn2000trust]. The selected correction $c$ of an
optional correction step satisfies the enlarged radius, $p(s + c) \le \tau \Delta$, and does not
increase the objective at the original trial, $f(x + s + c) \le f(x + s)$.

This also holds when the correction is reset to zero.

**Reading.** Bounds for the selected optional step using general objective and model premises.
-/
theorem OptionalCorrectionStep.selected_bounds
    {f m mCS : E → ℝ} {p : E → ℝ} {x s : E} {Δ τ required : ℝ}
    {proposal : Option E} {correction : E}
    (h : OptionalCorrectionStep f m mCS p x s Δ τ required proposal correction) :
    p (s + correction) ≤ τ * Δ ∧ f (x + (s + correction)) ≤ f (x + s) := by
  have hbase : p s ≤ τ * Δ :=
    h.original_radius.trans (le_mul_of_one_le_left h.radius_nonneg h.enlargement_gt_one.le)
  cases proposal with
  | none =>
    rw [h.selected]
    simpa [selectOptionalCorrection] using hbase
  | some d =>
    rw [h.selected]
    by_cases hd : f (x + s + d) ≤ f (x + s)
    · simp only [selectOptionalCorrection, ite_eq_left hd]
      exact ⟨(h.proposal_valid d rfl).2, by simpa only [add_assoc] using hd⟩
    · simp only [selectOptionalCorrection, ite_eq_right hd, add_zero, le_refl, and_true]
      exact hbase

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- **Algorithms 11.3.1, 15.3.1 and 16.2.1** of [conn2000trust]. For an optional correction step
with selected correction $c$, the ratios with the original prediction $m(0) - m(s)$ satisfy
$$\frac{f(x) - f(x + s)}{m(0) - m(s)} \le \frac{f(x) - f(x + s + c)}{m(0) - m(s)}.$$
So the correction can only improve the reduction ratio when the prediction comes from the
original step.

**Reading.** Abstract comparison with the original ratio for positive prediction.
-/
theorem OptionalCorrectionStep.original_ratio_le
    {f m mCS : E → ℝ} {p : E → ℝ} {x s : E} {Δ τ required : ℝ}
    {proposal : Option E} {correction : E}
    (h : OptionalCorrectionStep f m mCS p x s Δ τ required proposal correction) :
    reductionRatio f x s (m 0 - m s) ≤
      reductionRatio f x (s + correction) (m 0 - m s) := by
  unfold reductionRatio
  exact div_le_div_of_nonneg_right (sub_le_sub_left h.selected_bounds.2 _)
    (h.required_nonneg.trans h.original_decrease)

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- **Algorithm 11.3.1** of [conn2000trust], with (11.3.4)–(11.3.5). An infinite run of the
nonsmooth trust-region algorithm with corrections, for parameters (11.1.15), an objective $f$
and models $m(x, p, \cdot)$, consists of iterates $x_k$, steps $s_k$, corrections $c_k$, radii
$\Delta_k$ with $0 < \Delta_0 \le \Delta_{\max}$, model parameters $p_k$ and an enlargement
$\tau \ge 1$, such that $\|s_k\| \le \Delta_k$, $\|s_k + c_k\| \le \tau \Delta_k$,
$f(x_k + s_k + c_k) \le f(x_k + s_k)$ and $m(x_k, p_k, 0) - m(x_k, p_k, s_k) \ge 0$. The ratio
$$\rho_k = \frac{f(x_k) - f(x_k + s_k + c_k)}{m(x_k, p_k, 0) - m(x_k, p_k, s_k)}$$
uses the corrected trial and the original prediction. The next iterate is $x_k + s_k + c_k$ if
$\rho_k \ge \eta_1$ and $x_k$ otherwise, and the radius is updated by (11.1.16) with $\rho_k$.

**Correction.** Corrected capped radius update for the extended trial trace.
-/
structure NonsmoothCorrectionRun (Q : NonsmoothTRParams) (f : E → ℝ)
    (m : E → P → E → ℝ) where
  /-- The iterates $x_k$. -/
  x : ℕ → E
  /-- The trial steps $s_k$. -/
  s : ℕ → E
  /-- The corrections $c_k$. -/
  correction : ℕ → E
  /-- The trust-region radii $\Delta_k$. -/
  Δ : ℕ → ℝ
  /-- The model parameters $p_k$. -/
  parameter : ℕ → P
  /-- The initial radius is positive: $\Delta_0 > 0$. -/
  radius_initial_pos : 0 < Δ 0
  /-- The initial radius is at most the cap: $\Delta_0 \le \Delta_{\max}$. -/
  radius_initial_le : Δ 0 ≤ Q.Δmax
  /-- Each original step lies in the trust region: $\|s_k\| \le \Delta_k$. -/
  step_bound : ∀ k, ‖s k‖ ≤ Δ k
  /-- The enlargement factor $\tau$ of the corrected steps. -/
  enlargement : ℝ
  /-- The enlargement factor is at least one: $\tau \ge 1$. -/
  enlargement_ge_one : 1 ≤ enlargement
  /-- Each corrected step lies in the enlarged region: $\|s_k + c_k\| \le \tau \Delta_k$. -/
  corrected_bound : ∀ k, ‖s k + correction k‖ ≤ enlargement * Δ k
  /-- Each correction does not increase the objective: $f(x_k + s_k + c_k) \le f(x_k + s_k)$. -/
  improves : ∀ k, f (x k + s k + correction k) ≤ f (x k + s k)
  /-- The predicted decrease of the original step is nonnegative. -/
  pred_nonneg : ∀ k, 0 ≤ m (x k) (parameter k) 0 - m (x k) (parameter k) (s k)
  /-- The next iterate is $x_k + s_k + c_k$ if $\rho_k \ge \eta_1$, and $x_k$ otherwise. -/
  next_x : ∀ k, x (k + 1) =
    if Q.η₁ ≤ reductionRatio f (x k) (s k + correction k)
      (m (x k) (parameter k) 0 - m (x k) (parameter k) (s k))
    then x k + (s k + correction k) else x k
  /-- The next radius is a legal update (11.1.16) of $\Delta_k$ for $\rho_k$. -/
  next_radius : ∀ k, NonsmoothRadiusUpdate Q
    (reductionRatio f (x k) (s k + correction k)
      (m (x k) (parameter k) 0 - m (x k) (parameter k) (s k))) (Δ k) (Δ (k + 1))

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- **Algorithms 11.3.1, 15.3.1 and 16.2.1** of [conn2000trust]. Optional correction steps with the
norm of $E$ as trust-region norm, an enlargement $\tau > 1$, an initial radius
$0 < \Delta_0 \le \Delta_{\max}$, the iterate update by the acceptance test with $\eta_1$ and
the radius update (11.1.16) form a run of Algorithm 11.3.1.

The iterate and radius updates use the selected trial $s_k + c_k$ and the original prediction
$m(x_k, p_k, 0) - m(x_k, p_k, s_k)$.

**Correction.** Uses abstract options and the ambient norm to construct the corrected run.
-/
def NonsmoothCorrectionRun.ofOptionalCorrectionSteps
    {Q : NonsmoothTRParams} {f : E → ℝ} {m : E → P → E → ℝ}
    (x s correction : ℕ → E) (Δ required : ℕ → ℝ) (parameter : ℕ → P)
    (mCS : ℕ → E → ℝ) (proposal : ℕ → Option E) (τ : ℝ) (hτ : 1 < τ)
    (hΔ₀ : 0 < Δ 0) (hcap : Δ 0 ≤ Q.Δmax)
    (htrial : ∀ k, OptionalCorrectionStep f (m (x k) (parameter k)) (mCS k) (fun d ↦ ‖d‖)
      (x k) (s k) (Δ k) τ (required k) (proposal k) (correction k))
    (hnext : ∀ k, x (k + 1) = acceptStep Q.η₁ f (x k) (s k + correction k)
      (m (x k) (parameter k) 0 - m (x k) (parameter k) (s k)))
    (hrad : ∀ k, NonsmoothRadiusUpdate Q
      (reductionRatio f (x k) (s k + correction k)
        (m (x k) (parameter k) 0 - m (x k) (parameter k) (s k))) (Δ k) (Δ (k + 1))) :
    NonsmoothCorrectionRun Q f m where
  x := x
  s := s
  correction := correction
  Δ := Δ
  parameter := parameter
  radius_initial_pos := hΔ₀
  radius_initial_le := hcap
  step_bound k := (htrial k).original_radius
  enlargement := τ
  enlargement_ge_one := hτ.le
  corrected_bound k := (htrial k).selected_bounds.1
  improves k := by simpa only [add_assoc] using (htrial k).selected_bounds.2
  pred_nonneg k := (htrial k).required_nonneg.trans (htrial k).original_decrease
  next_x := hnext
  next_radius := hrad

/-- **Theorem 11.3.2** of [conn2000trust]. Let $E$ be a real Hilbert space and consider a run of
Algorithm 11.3.1. Let $z$ be the limit of a subsequence $x_{j(k)}$, let $f$ be Lipschitz on a
neighborhood of $z$, and let the models match the value of $f$ (11.1.1) and have uniform
normalized agreement with $f$ at $z$. Let $\varepsilon, \delta, \kappa > 0$ with
$$\kappa \|g^*(x_k)\| \min\{\delta, \Delta_k\} \le m(x_k, p_k, 0) - m(x_k, p_k, s_k) \quad
  \text{whenever } \|x_k - z\| < \varepsilon.$$
Then $z$ is Clarke stationary: $0 \in \partial f(z)$.

**Correction.** The source assumes only pointwise model agreement. The statement assumes uniform
normalized agreement, as in the corrected Lemma 11.2.3.

The correction only improves the numerator of the ratio, and the fixed enlargement only changes
the displacement coefficient in the local radius estimate. The convergent subsequence supplies
the lower bound on the objective that the sum of the accepted decreases needs. -/
theorem theorem_11_3_2 {Q : NonsmoothTRParams} {f : E → ℝ} {m : E → P → E → ℝ}
    (run : NonsmoothCorrectionRun Q f m) {z : E} {U : Set E} {L : NNReal}
    (hU : U ∈ 𝓝 z) (hL : LipschitzOnWith L f U) (hmatch : modelValueMatches f m)
    (herr : UniformNormalizedModelAgreementAt f m z)
    {ε δ κ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hκ : 0 < κ)
    (hAA : ∀ k, run.x k ∈ ball z ε → κ * ‖minimumNormSubgradient f (run.x k)‖ *
      min δ (run.Δ k) ≤ m (run.x k) (run.parameter k) 0 - m (run.x k) (run.parameter k) (run.s k))
    {j : ℕ → ℕ} (hj : StrictMono j) (hz : Tendsto (run.x ∘ j) atTop (𝓝 z)) :
    (0 : E) ∈ clarkeSubgradient f z := by
  by_contra hn
  let pred (k : ℕ) := m (run.x k) (run.parameter k) 0 - m (run.x k) (run.parameter k) (run.s k)
  let ρ (k : ℕ) := reductionRatio f (run.x k) (run.s k + run.correction k) (pred k)
  let S : Set ℕ := {k | Q.η₁ ≤ ρ k}
  have hg₃ : 0 < Q.γ₃ := zero_lt_one.trans Q.gamma₃_gt_one
  have hg₁ : 0 < Q.γ₁ := (one_div_pos.mpr hg₃).trans_le Q.inv_gamma₃_le_gamma₁
  have hγ₁ : Q.γ₁ ≤ 1 := Q.gamma₁_le_gamma₂.trans Q.gamma₂_lt_one.le
  have hbound : ∀ k, 0 < run.Δ k ∧ run.Δ k ≤ Q.Δmax := by
    intro k
    induction k with
    | zero => exact ⟨run.radius_initial_pos, run.radius_initial_le⟩
    | succ k ih =>
      have hu := run.next_radius k
      by_cases h₂ : Q.η₂ ≤ ρ k
      · exact ⟨(lt_min (mul_pos hg₃ ih.1) Q.radiusMax_pos).trans_le (hu.very_successful h₂).1,
          (hu.very_successful h₂).2⟩
      by_cases h₁ : Q.η₁ ≤ ρ k
      · obtain ⟨ha, hb⟩ := hu.successful h₁ (lt_of_not_ge h₂)
        exact ⟨(mul_pos (hg₁.trans_le Q.gamma₁_le_gamma₂) ih.1).trans_le ha, hb.trans ih.2⟩
      · obtain ⟨ha, hb⟩ := hu.unsuccessful (lt_of_not_ge h₁)
        exact ⟨(mul_pos hg₁ ih.1).trans_le ha, (hb.trans
          (mul_le_of_le_one_left ih.1.le Q.gamma₂_lt_one.le)).trans ih.2⟩
  have hnext (k : ℕ) : Q.γ₁ * run.Δ k ≤ run.Δ (k + 1) := by
    have hu := run.next_radius k
    by_cases h₂ : Q.η₂ ≤ ρ k
    · exact (le_min (mul_le_mul_of_nonneg_right (hγ₁.trans Q.gamma₃_gt_one.le) (hbound k).1.le)
        ((mul_le_of_le_one_left (hbound k).1.le hγ₁).trans (hbound k).2)).trans
        (hu.very_successful h₂).1
    by_cases h₁ : Q.η₁ ≤ ρ k
    · exact (mul_le_mul_of_nonneg_right Q.gamma₁_le_gamma₂ (hbound k).1.le).trans
        (hu.successful h₁ (lt_of_not_ge h₂)).1
    · exact (hu.unsuccessful (lt_of_not_ge h₁)).1
  have hstay (k : ℕ) (hk : k ∉ S) : run.x (k + 1) = run.x k := by
    have h : ¬ Q.η₁ ≤ ρ k := hk
    rw [run.next_x, ite_eq_right h]
  have htake (k : ℕ) (hk : k ∈ S) : run.x (k + 1) = run.x k + (run.s k + run.correction k) := by
    have h : Q.η₁ ≤ ρ k := hk
    rw [run.next_x, ite_eq_left h]
  have hstep (k : ℕ) : dist (run.x k) (run.x (k + 1)) ≤ run.enlargement * run.Δ k := by
    by_cases hs : k ∈ S
    · rw [htake k hs, dist_comm, dist_eq_norm, add_sub_cancel_left]
      exact run.corrected_bound k
    · rw [hstay k hs, dist_self]
      exact mul_nonneg (zero_le_one.trans run.enlargement_ge_one) (hbound k).1.le
  obtain ⟨e, T, he, hT, hforce⟩ :=
    lemma_11_2_3 hU hL hn hmatch herr Q.eta₂_lt_one hκ hδ
  let e₀ := min e ε
  let T₀ := min T (Q.Δmax / Q.γ₃)
  obtain ⟨r, hr, hfloor⟩ := radius_floor_of_local_expansion (lt_min he hε)
    (lt_min hT (div_pos Q.radiusMax_pos hg₃)) (zero_lt_one.trans_le run.enlargement_ge_one)
    hg₁ Q.gamma₃_gt_one (fun k ↦ (hbound k).1) hnext hstep (ε := e₀) (T := T₀) (by
      intro k hk hrad
      have ha := hforce (run.x k) (ball_subset_ball (min_le_left _ _) hk) (run.parameter k)
        (run.Δ k) (hbound k).1 (hrad.trans_le (min_le_left _ _)) (run.s k) (run.step_bound k)
        (hAA k (ball_subset_ball (min_le_right _ _) hk))
      have hb : Q.η₂ ≤ ρ k := ha.trans (div_le_div_of_nonneg_right
        (sub_le_sub_left (by simpa only [add_assoc] using run.improves k) _) (run.pred_nonneg k))
      have hc := ((run.next_radius k).very_successful hb).1
      have hcap : Q.γ₃ * run.Δ k ≤ Q.Δmax := by
        rw [mul_comm]
        exact (le_div_iff₀ hg₃).mp (hrad.le.trans (min_le_right _ _))
      rwa [min_eq_left hcap] at hc)
  obtain ⟨eg, a, heg, ha, hg⟩ := lemma_11_1_2 hU hL hn
  let e₁ := min (e₀ / 2) (min eg ε)
  have he₁ : 0 < e₁ := lt_min (half_pos (lt_min he hε)) (lt_min heg hε)
  let d := κ * a * min δ r
  have hd : 0 < d := mul_pos (mul_pos hκ ha) (lt_min hδ hr)
  have hpred (k : ℕ) (hk : run.x k ∈ ball z e₁) : d ≤ pred k := by
    have h₁ := hfloor k (ball_subset_ball (min_le_left _ _) hk)
    have h₂ := hg (run.x k) (ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _)) hk)
    have h₃ := hAA k (ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _)) hk)
    exact (mul_le_mul (mul_le_mul_of_nonneg_left h₂ hκ.le) (min_le_min le_rfl h₁)
      (le_min hδ.le hr.le) (by positivity)).trans h₃
  have hdrop (k : ℕ) :
      Q.η₁ * acceptedDecrease S pred k ≤ f (run.x k) - f (run.x (k + 1)) := by
    classical
    by_cases hs : k ∈ S
    · have hp : 0 < pred k := by
        have hh : Q.η₁ ≤ ρ k := hs
        by_contra! h
        have he := le_antisymm h (run.pred_nonneg k)
        have hz : ρ k = 0 := by simp [ρ, reductionRatio, he]
        exact Q.eta₁_pos.not_ge (hz ▸ hh)
      rw [acceptedDecrease, ite_eq_left hs, htake k hs]
      exact (le_reductionRatio_iff hp).mp hs
    · rw [acceptedDecrease, ite_eq_right hs, hstay k hs, mul_zero, sub_self]
  have hmono : Antitone (fun k ↦ f (run.x k)) := by
    apply antitone_nat_of_succ_le
    intro k
    apply sub_nonneg.mp
    refine (mul_nonneg Q.eta₁_pos.le ?_).trans (hdrop k)
    classical
    by_cases hk : k ∈ S <;> simp [acceptedDecrease, hk, pred, run.pred_nonneg]
  have hlim : Tendsto (fun i ↦ f (run.x (j i))) atTop (𝓝 (f z)) :=
    (hL.continuousOn.continuousAt hU).tendsto.comp hz
  have hlower (k : ℕ) : f z ≤ f (run.x k) :=
    le_of_tendsto hlim ((hj.tendsto_atTop.eventually_ge_atTop k).mono fun _ hi ↦ hmono hi)
  have hsum : Summable (acceptedDecrease S pred) := by
    apply summable_of_bounded_accepted_decrease (B := (f (run.x 0) - f z) / Q.η₁)
      run.pred_nonneg
    intro n
    apply (le_div_iff₀ Q.eta₁_pos).mpr
    rw [mul_comm, Finset.mul_sum]
    calc
      _ ≤ ∑ k ∈ Finset.range n, (f (run.x k) - f (run.x (k + 1))) :=
        Finset.sum_le_sum fun k _ ↦ hdrop k
      _ = -(∑ k ∈ Finset.range n, (f (run.x (k + 1)) - f (run.x k))) := by
        rw [← Finset.sum_neg_distrib]
        simp only [neg_sub]
      _ = f (run.x 0) - f (run.x n) := by rw [Finset.sum_range_sub (fun k ↦ f (run.x k)) n, neg_sub]
      _ ≤ _ := sub_le_sub_left (hlower n) _
  exact no_noncritical_cluster_of_predicted_sum he₁ hr hd
    (hg₁.le.trans Q.gamma₁_le_gamma₂) Q.gamma₂_lt_one
    (fun k hk ↦ hfloor k (ball_subset_ball (min_le_left _ _) hk)) hpred hsum hstay
    (fun k hk ↦ ((run.next_radius k).unsuccessful (lt_of_not_ge (show ¬ Q.η₁ ≤ ρ k from hk))).2)
    hj hz

end ConnGouldToint.Chapter11
