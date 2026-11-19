/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.ConnGouldToint.Chapter06.Section05

/-!
# Conn, Gould and Toint, Section 6.6: Exploiting negative curvature

This module formalizes Section 6.6 of [conn2000trust], which proves convergence of the basic
trust-region algorithm to second-order critical points. When the model Hessian has a negative
curvature $\tau < 0$ along a direction $u$, a step along $u$ to the trust-region boundary (the
eigenpoint) decreases a quadratic model by at least a multiple of $|\tau| \Delta^2$ (Theorem 6.6.1),
and a geometric backtracking search along $u$ finds such a decrease for a general model with a
Lipschitz Hessian (Theorem 6.6.2). Assumption AA.2 asks for a model decrease
$\kappa |\tau| \min\{\tau^2, \Delta^2\}$ whenever the model curvature $\tau$ is negative. Under AA.2
and a model error that is $o(\Delta^2)$ on small radii, the objective curvature is above every
negative threshold infinitely often (Theorem 6.6.4). Hence some limit point is second-order critical
(Theorem 6.6.5), an isolated limit point is second-order critical (Theorem 6.6.7), and, if the
radius must grow after very successful iterations (assumption AA.3), every limit point is
second-order critical (Theorem 6.6.8).

Here the curvature of the objective at $x$ is a function $\lambda(x)$, and the model curvature at
iteration $k$ is a number $\tau_k$ with $|\lambda(x_k) - \tau_k| \to 0$. For actual Hessians,
$\lambda$ is the least curvature $\inf_{\|u\| = 1} D^2 f(x)(u, u)$, which is the least Hessian
eigenvalue in a Euclidean space.

## Main definitions

* Equation (6.6.8), `ConnGouldToint.Chapter06.eigenTrialTime`: the trial times $q^j$ of the
  negative-curvature search.
* Equation (6.6.9), `ConnGouldToint.Chapter06.EigenTrialAccepted`: the acceptance test of a trial
  along the negative-curvature ray.
* Assumption AA.2, `ConnGouldToint.Chapter06.HasNegativeCurvatureDecrease`: the model decrease
  $\kappa |\tau| \min\{\tau^2, \Delta^2\}$ when the model curvature $\tau$ is negative.
* `ConnGouldToint.Chapter06.smallRadiusModelAgreement`: the model error on late iterations with
  small radii is at most $\varepsilon \Delta_k^2$.
* Equation (6.6.20), `ConnGouldToint.Chapter06.leastUnitCurvature`: the least curvature
  $\inf_{\|u\| = 1} H(u, u)$ of a Hessian $H$.
* Assumption AA.3, `ConnGouldToint.Chapter06.HasForcedRadiusExpansion`: the radius grows
  geometrically after a very successful iteration below a cap.
* Equations (6.6.43)–(6.6.48), `ConnGouldToint.Chapter06.curvatureExpansionThreshold`,
  `ConnGouldToint.Chapter06.curvatureExitRadius` and
  `ConnGouldToint.Chapter06.negativeCurvatureDropFloor`: the radii and the decrease floor in the
  proof of Theorem 6.6.8.

## Main results

* Theorem 6.6.1, `ConnGouldToint.Chapter06.theorem_6_6_1`: on a quadratic ray with negative
  curvature, the endpoint minimizes the model and gives the decrease (6.6.5).
* Theorem 6.6.1, `ConnGouldToint.Chapter06.theorem_6_6_1_quadraticModel`: the same for the quadratic
  model (6.1.7) at the eigenpoint.
* Theorem 6.6.2, `ConnGouldToint.Chapter06.theorem_6_6_2`: with a Lipschitz model Hessian, the first
  accepted backtracking trial gives a decrease uniform in the curvature and the ray length.
* Theorem 6.6.2, `ConnGouldToint.Chapter06.theorem_6_6_2_of_taylor_bound`: the same from a cubic
  Taylor bound along the ray.
* Theorem 6.6.3, `ConnGouldToint.Chapter06.theorem_6_6_3`: if the point is not first-order critical
  or the curvature is negative, the step is nonzero and decreases the model.
* Theorem 6.6.4, `ConnGouldToint.Chapter06.theorem_6_6_4`: the objective curvature is above every
  negative threshold infinitely often.
* Theorem 6.6.5, `ConnGouldToint.Chapter06.theorem_6_6_5`: in a compact set, some limit point is
  first-order critical with nonnegative curvature.
* Theorems 6.6.4 and 6.6.5, `ConnGouldToint.Chapter06.theorem_6_6_5_of_hessians`: the same with
  actual Hessians, so the limit has a positive semidefinite Hessian.
* Lemma 6.6.6, `ConnGouldToint.Chapter06.lemma_6_6_6`: near a limit with negative curvature, the
  radii tend to zero along the subsequence.
* Lemma 6.6.6, `ConnGouldToint.Chapter06.lemma_6_6_6_successful`: successful iterations with
  uniformly negative model curvature have vanishing radii.
* Theorem 6.6.7, `ConnGouldToint.Chapter06.theorem_6_6_7`: an isolated limit point is second-order
  critical.
* Theorem 6.6.8, `ConnGouldToint.Chapter06.theorem_6_6_8`: under AA.3, every limit point is
  second-order critical.

## Proof outline

For Theorems 6.6.7 and 6.6.8, suppose that the model curvature is at most $-a < 0$ near a limit
point $z$. Every successful iteration there decreases the objective by a fixed multiple of
$\min\{a^2, \Delta_k^2\}$, so the successful radii tend to zero, while small radii force very
successful iterations. Near an isolated limit, the iterates must leave and return to a neighborhood
of $z$ infinitely often, and each excursion costs a fixed decrease of the objective. Under AA.3, the
radii grow geometrically while they are small, so a block of very successful iterations either
reaches a fixed radius or moves a fixed distance, and again the objective decreases by a fixed
amount. Both contradict a lower bound on $f$.

## Conventions

* The objective and model curvatures are given as a function `curv : E → ℝ` and a sequence
  `τ : ℕ → ℝ`, linked by $|\lambda(x_k) - \tau_k| \to 0$. This hypothesis replaces the Hessian
  agreement of AM.5 in the abstract results; `ConnGouldToint.Chapter06.theorem_6_6_5_of_hessians`
  derives it from AM.5.
* The estimate $|f(x_k + s_k) - m_k(x_k + s_k)| = o(\Delta_k^2)$ on small radii is the explicit
  hypothesis `ConnGouldToint.Chapter06.smallRadiusModelAgreement`.

## Implementation notes

* The proof of Lemma 6.6.6 treats a rejected trial by following the unchanged iterate to its first
  successful trial, and by bounding the radius at that trial.
* The least curvature `ConnGouldToint.Chapter06.leastUnitCurvature` is $0$ on the zero space, where
  the unit sphere is empty. The results about it assume that $E$ is nontrivial.

## Deviations from the source

* **Theorems 6.6.1–6.6.2** (generalization). The eigenstep decrease uses a quadratic ray with
  explicit slope and curvature. The line-search estimate uses a bound on the ray or objective
  Taylor data along the trial segment in a real normed space.
* **Theorem 6.6.3** (correction). The decrease guarantee assumes a nonzero model gradient or
  negative model curvature at the current iterate. The source tests objective second-order
  criticality. Assumption AM.5 is asymptotic and does not ensure the sign of the current model
  curvature. The decrease predicate allows any positive decrease constant.
* **Theorem 6.6.4** (reading). The model error estimate on small radii is an explicit hypothesis. It
  follows from uniform variation of the objective and model Hessians on small trial segments. See
  `ConnGouldToint.Chapter06.theorem_6_6_4`.
* **Theorems 6.6.5–6.6.8 and Lemma 6.6.6** (generalization). The convergence lemmas work with real
  normed spaces and abstract curvature functions. They carry the required model error, compactness
  or local radius expansion as explicit hypotheses. The Hessian specialization takes the infimum
  of the Hessian quadratic form over the unit sphere.
-/

open Filter Set Topology

namespace ConnGouldToint.Chapter06

/-- **Equation (6.6.8)** of [conn2000trust]. For a contraction factor $q$, the $j$-th **trial time**
of the negative-curvature search is $q^j$, for $j = 0, 1, 2, \dots$ -/
def eigenTrialTime (q : ℝ) (j : ℕ) : ℝ := q ^ j

/-- **Equation (6.6.9)** of [conn2000trust]. Let $r : \mathbb{R} \to \mathbb{R}$ be the model along
a ray, $t \mapsto m(x + t u)$, with $U = \|u\|$. The trial $j$ is **accepted** if
$$r(q^j) \le r(0) + b \tau (q^j U)^2.$$

For a negative curvature $\tau < 0$ and $b > 0$, this asks for a decrease of at least
$b |\tau| (q^j U)^2$. -/
def EigenTrialAccepted (ray : ℝ → ℝ) (q b τ U : ℝ) (j : ℕ) : Prop :=
  ray (eigenTrialTime q j) ≤ ray 0 + b * τ * (eigenTrialTime q j * U) ^ 2

/-- **Theorem 6.6.1** of [conn2000trust], with (6.6.3)–(6.6.5). Let $r : \mathbb{R} \to \mathbb{R}$
be a quadratic $r(t) = r(0) + t g + t^2 h / 2$ with $g \le 0$. Let $\kappa > 0$, $\tau < 0$ and
$U > 0$ with $h \le \kappa \tau U^2$. Then $t = 1$ minimizes $r$ on $(0, 1]$, and
$$r(0) - r(1) \ge -\tfrac12 \kappa \tau U^2.$$

**Reading.** Scalar quadratic ray with supplied slope and negative curvature.
-/
theorem theorem_6_6_1 {ray : ℝ → ℝ} {g h κ τ U : ℝ}
    (hg : g ≤ 0) (hκ : 0 < κ) (hτ : τ < 0) (hU : 0 < U)
    (hh : h ≤ κ * τ * U ^ 2) (hray : ∀ t, ray t = ray 0 + t * g + t ^ 2 * h / 2) :
    IsMinOn ray (Ioc 0 1) 1 ∧ -(1 / 2 : ℝ) * κ * τ * U ^ 2 ≤ ray 0 - ray 1 := by
  have hneg : h < 0 := hh.trans_lt (mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hκ hτ)
    (sq_pos_of_pos hU))
  refine ⟨?_, ?_⟩
  · apply isMinOn_iff.mpr
    intro t ht
    have hsq : t ^ 2 ≤ 1 := by nlinarith [mul_nonneg ht.1.le (sub_nonneg.mpr ht.2)]
    have hlin := mul_le_mul_of_nonpos_right ht.2 hg
    have hquad := mul_le_mul_of_nonpos_right hsq hneg.le
    rw [hray 1, hray t]
    linarith
  · rw [hray 1]
    linarith

/-- **Theorem 6.6.1** of [conn2000trust], for the quadratic model (6.1.7). Let $F$ be a real inner
product space, $p$ a seminorm on $F$, $H : F \to F$ linear, $c \in \mathbb{R}$ and $g, u \in F$.
Let $\kappa > 0$, $\tau < 0$ and $\Delta > 0$, with $p(u) = \Delta$,
$\langle g, u \rangle \le 0$ and $\langle u, H u \rangle \le \kappa \tau \|u\|^2$. Let $q(s) =
c + \langle g, s \rangle + \frac12 \langle s, H s \rangle$. Then $t = 1$ minimizes
$t \mapsto q(t u)$ on $(0, 1]$, and
$$c - q(u) \ge -\tfrac12 \kappa \tau \, \nu(u)^2 \Delta^2,$$
where $\nu(u) = \|u\| / p(u)$ is the ratio (6.4.2).

The ratio converts the trust-region radius to the Euclidean length of the eigenpoint step, as in
(6.6.2).

**Reading.** Abstract quadratic model and seminorm-scaled boundary.
-/
theorem theorem_6_6_1_quadraticModel {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (p : Seminorm ℝ F) (H : F →ₗ[ℝ] F) (c : ℝ) (g u : F) {κ τ Δ : ℝ}
    (hκ : 0 < κ) (hτ : τ < 0) (hΔ : 0 < Δ) (hp : p u = Δ)
    (hg : inner ℝ g u ≤ 0) (hh : inner ℝ u (H u) ≤ κ * τ * ‖u‖ ^ 2) :
    IsMinOn (fun t : ℝ ↦ quadraticModel c g H (t • u)) (Ioc 0 1) 1 ∧
      -(1 / 2 : ℝ) * κ * τ * (stepNormRatio p u) ^ 2 * Δ ^ 2 ≤
        c - quadraticModel c g H u := by
  have hu : u ≠ 0 := fun h ↦ by simp [h, hΔ.ne] at hp
  obtain ⟨hmin, hdec⟩ := theorem_6_6_1 (ray := fun t : ℝ ↦ quadraticModel c g H (t • u))
    hg hκ hτ (norm_pos_iff.mpr hu) hh (by
      intro t
      simp only [quadraticModel, zero_smul, map_zero, inner_zero_right,
        mul_zero, add_zero, map_smul, real_inner_smul_right, real_inner_smul_left]
      ring)
  refine ⟨hmin, ?_⟩
  have he : stepNormRatio p u * Δ = ‖u‖ := by
    rw [stepNormRatio, hp]
    exact div_mul_cancel₀ _ hΔ.ne'
  simpa only [zero_smul, quadraticModel, inner_zero_right, map_zero, mul_zero,
    add_zero, one_smul] using
    (show -(1 / 2 : ℝ) * κ * τ * (stepNormRatio p u) ^ 2 * Δ ^ 2 ≤ _ from
      (show -(1 / 2 : ℝ) * κ * τ * (stepNormRatio p u) ^ 2 * Δ ^ 2 =
          -(1 / 2 : ℝ) * κ * τ * ‖u‖ ^ 2 by rw [← he, mul_pow]; ring).le.trans hdec)

/-- **Proofs of Theorems 6.6.2 and 12.4.6** of [conn2000trust], geometric backtracking estimate. Let
$0 < q < 1$, $a > 0$, $U \in \mathbb{R}$, and let $A$ be a set of indices that contains every
$j$ with $q^j U \le a$. Then there is a first index $j \in A$ (no $i < j$ lies in $A$), and
$$\min\{U, q a\} \le q^j U.$$

**Reading.** Backtracking argument takes an abstract acceptance predicate from a sufficient length
bound.
-/
theorem exists_first_eigenTrial_of_small_length {q U a : ℝ}
    (hq : 0 < q) (hq' : q < 1) (ha : 0 < a) {accept : ℕ → Prop}
    (haccept : ∀ j, eigenTrialTime q j * U ≤ a → accept j) :
    ∃ j, accept j ∧ (∀ i < j, ¬ accept i) ∧ min U (q * a) ≤ eigenTrialTime q j * U := by
  have ht : Tendsto (fun j : ℕ ↦ eigenTrialTime q j * U) atTop (𝓝 0) := by
    simpa only [eigenTrialTime, zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hq.le hq').mul_const U
  obtain ⟨i, hi⟩ := (ht.eventually_lt_const ha).exists
  have hex : ∃ j, accept j := ⟨i, haccept i hi.le⟩
  classical
  let j := Nat.find hex
  have hfirst (k : ℕ) (hk : k < j) : ¬ accept k := Nat.find_min hex hk
  refine ⟨j, Nat.find_spec hex, hfirst, ?_⟩
  cases hj : j with
  | zero => simp [eigenTrialTime]
  | succ k =>
    have hk : a < eigenTrialTime q k * U :=
      lt_of_not_ge (fun h ↦ hfirst k (hj ▸ Nat.lt_succ_self k) (haccept k h))
    have hh := mul_lt_mul_of_pos_left hk hq
    apply (min_le_right U (q * a)).trans
    simp only [eigenTrialTime, pow_succ] at hh ⊢
    nlinarith only [hh]

/-- **Theorem 6.6.2** of [conn2000trust], from a cubic Taylor bound along the ray. Let
$r : \mathbb{R} \to \mathbb{R}$, $0 < q < 1$, $b > 0$ with $b < \kappa / 2$, $\tau < 0$,
$U > 0$, $R > 0$, $g \le 0$ and $h \le \kappa \tau U^2$. Suppose that
$$r(t) \le r(0) + t g + \tfrac12 t^2 h + R (t U)^3 \quad \text{for all } t \in (0, 1].$$
Then there is a first trial $j$ accepted by the test (6.6.9), and
$$r(0) - r(q^j) \ge b \min\Bigl\{1, \frac{q (\kappa / 2 - b)}{R}\Bigr\}^2 |\tau| \min\{\tau^2,
  U^2\}.$$

**Reading.** Explicit ray Taylor bound suffices for the backtracking estimate.
-/
theorem theorem_6_6_2_of_taylor_bound {ray : ℝ → ℝ} {q b κ τ U R g h : ℝ}
    (hq : 0 < q) (hq' : q < 1) (hb : 0 < b) (hbκ : b < κ / 2)
    (hτ : τ < 0) (hU : 0 < U) (hR : 0 < R) (hg : g ≤ 0)
    (hh : h ≤ κ * τ * U ^ 2)
    (hray : ∀ t ∈ Ioc (0 : ℝ) 1,
      ray t ≤ ray 0 + t * g + t ^ 2 * h / 2 + R * (t * U) ^ 3) :
    ∃ j, EigenTrialAccepted ray q b τ U j ∧
      (∀ i < j, ¬ EigenTrialAccepted ray q b τ U i) ∧
      (b * min 1 (q * (κ / 2 - b) / R) ^ 2) * (-τ) * min (τ ^ 2) (U ^ 2) ≤
        ray 0 - ray (eigenTrialTime q j) := by
  let margin := κ / 2 - b
  have hm : 0 < margin := sub_pos.mpr hbκ
  have htime (j : ℕ) : eigenTrialTime q j ∈ Ioc (0 : ℝ) 1 :=
    ⟨pow_pos hq _, pow_le_one₀ hq.le hq'.le⟩
  have haccept (j : ℕ) (hs : R * (eigenTrialTime q j * U) ≤ margin * (-τ)) :
      EigenTrialAccepted ray q b τ U j := by
    let t := eigenTrialTime q j
    have ht := htime j
    have hcurv := mul_le_mul_of_nonneg_left hh (sq_nonneg t)
    have hlin := mul_nonpos_of_nonneg_of_nonpos ht.1.le hg
    have hcube := mul_le_mul_of_nonneg_right hs (sq_nonneg (t * U))
    exact (hray t ht).trans (by dsimp [margin] at hcube; nlinarith only [hcurv, hlin, hcube])
  let a := margin * (-τ) / R
  have ha : 0 < a := div_pos (mul_pos hm (neg_pos.mpr hτ)) hR
  obtain ⟨j, hj, hfirst, hlength⟩ := exists_first_eigenTrial_of_small_length hq hq' ha
    (fun i hi ↦ haccept i (by
      have hh := (le_div_iff₀ hR).mp hi
      linarith only [hh, show R * (eigenTrialTime q i * U) = (eigenTrialTime q i * U) * R
        by ring]))
  refine ⟨j, hj, hfirst, ?_⟩
  let c := q * margin / R
  have hc : 0 < c := div_pos (mul_pos hq hm) hR
  have hlength' : min U (c * (-τ)) ≤ eigenTrialTime q j * U := by
    have heq : c * (-τ) = q * a := by dsimp [c, a]; ring
    simpa only [heq] using hlength
  have hscale : min 1 c * min U (-τ) ≤ min U (c * (-τ)) := by
    have hmin : 0 ≤ min U (-τ) := le_min hU.le (neg_nonneg.mpr hτ.le)
    apply le_min
    · exact (mul_le_of_le_one_left hmin (min_le_left 1 c)).trans (min_le_left U (-τ))
    · exact mul_le_mul (min_le_right 1 c) (min_le_right U (-τ)) hmin hc.le
  have hsquare := pow_le_pow_left₀
    (mul_nonneg (le_min zero_le_one hc.le) (le_min hU.le (neg_nonneg.mpr hτ.le)))
    (hscale.trans hlength') 2
  have hminτ : (min U (-τ)) ^ 2 = min (τ ^ 2) (U ^ 2) := by
    rcases le_total U (-τ) with h | h
    · rw [min_eq_left h, min_eq_right (by nlinarith)]
    · rw [min_eq_right h, min_eq_left (by nlinarith)]; ring
  rw [mul_pow, hminτ] at hsquare
  have hprod := mul_le_mul_of_nonneg_left hsquare (mul_nonneg hb.le (neg_nonneg.mpr hτ.le))
  unfold EigenTrialAccepted at hj
  change b * (min 1 c) ^ 2 * (-τ) * min (τ ^ 2) (U ^ 2) ≤ _
  linarith only [hj, hprod]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Theorem 6.6.2** of [conn2000trust], with (6.6.11)–(6.6.12). Let $E$ be a real normed space,
$S \subseteq E$ open, and $m : E \to \mathbb{R}$ twice continuously differentiable on $S$. Let
$x, u \in E$ with $u \neq 0$ and $x + t u \in S$ for $t \in [0, 1]$. Let $0 < q < 1$, $b > 0$
with $b < \kappa / 2$, $\tau < 0$ and $\gamma > 0$. Suppose that
$\|D^2 m(z) - D^2 m(x)\| \le \gamma \|z - x\|$ for all $z \in S$, that $Dm(x) u \le 0$, and that
$D^2 m(x)(u, u) \le \kappa \tau \|u\|^2$. Then the search along $t \mapsto m(x + t u)$ with
$U = \|u\|$ has a first accepted trial $j$ for the test (6.6.9), and
$$m(x) - m(x + q^j u) \ge b \min\Bigl\{1, \frac{q (\kappa / 2 - b)}{\gamma / 6}\Bigr\}^2 |\tau|
  \min\{\tau^2, \|u\|^2\}.$$

The Lipschitz bound on the Hessian gives the cubic Taylor remainder $(\gamma / 6) \|t u\|^3$ of
`ConnGouldToint.Chapter06.theorem_6_6_2_of_taylor_bound`.

**Reading.** Uses Fréchet derivatives and objective Taylor data along the trial segment.
-/
theorem theorem_6_6_2 {S : Set E} (hS : IsOpen S) {m : E → ℝ} (hm : ContDiffOn ℝ 2 m S)
    {x u : E} {q b κ τ γ : ℝ} (hq : 0 < q) (hq' : q < 1) (hb : 0 < b)
    (hbκ : b < κ / 2) (hτ : τ < 0) (hu : u ≠ 0) (hγ : 0 < γ)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, x + t • u ∈ S)
    (hlip : ∀ z ∈ S, ‖fderiv ℝ (fderiv ℝ m) z - fderiv ℝ (fderiv ℝ m) x‖ ≤ γ * ‖z - x‖)
    (hg : fderiv ℝ m x u ≤ 0) (hh : fderiv ℝ (fderiv ℝ m) x u u ≤ κ * τ * ‖u‖ ^ 2) :
    ∃ j, EigenTrialAccepted (fun t ↦ m (x + t • u)) q b τ ‖u‖ j ∧
      (∀ i < j, ¬ EigenTrialAccepted (fun t ↦ m (x + t • u)) q b τ ‖u‖ i) ∧
      (b * min 1 (q * (κ / 2 - b) / (γ / 6)) ^ 2) * (-τ) * min (τ ^ 2) (‖u‖ ^ 2) ≤
        m x - m (x + eigenTrialTime q j • u) := by
  obtain ⟨j, hj, hfirst, hdec⟩ := theorem_6_6_2_of_taylor_bound
    (ray := fun t ↦ m (x + t • u)) hq hq' hb hbκ hτ (norm_pos_iff.mpr hu)
    (show 0 < γ / 6 by positivity) hg hh (by
      intro t ht
      have hseg' (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) : x + a • (t • u) ∈ S := by
        rw [smul_smul]
        exact hseg _ ⟨mul_nonneg ha.1 ht.1.le, (mul_le_of_le_one_left ht.1.le ha.2).trans ht.2⟩
      have hbound := le_of_abs_le
        (abs_sub_secondOrder_le_of_lipschitzAt_segment hS hm hseg' hlip)
      simp only [zero_smul, add_zero, map_smul, smul_eq_mul, norm_smul,
        Real.norm_of_nonneg ht.1.le] at hbound ⊢
      simp only [smul_apply, smul_eq_mul] at hbound
      nlinarith only [hbound])
  exact ⟨j, hj, hfirst, by simpa using hdec⟩

omit [NormedSpace ℝ E] in
/-- **Assumption AA.2** of [conn2000trust], Section 6.6.3. A model $m$, a center $x$ and a step $s$
give a **negative-curvature decrease** with curvature $\tau$, radius $\Delta$ and constant
$\kappa$ if $\kappa > 0$ and
$$\tau < 0 \implies \kappa |\tau| \min\{\tau^2, \Delta^2\} \le m(x) - m(x + s).$$

**Reading.** Supplied curvature measure and an arbitrary positive decrease constant.
-/
def HasNegativeCurvatureDecrease (m : E → ℝ) (x s : E) (τ Δ κ : ℝ) : Prop :=
  0 < κ ∧ (τ < 0 → κ * |τ| * min (τ ^ 2) (Δ ^ 2) ≤ m x - m (x + s))

omit [NormedSpace ℝ E] in
/-- **Theorem 6.6.3** of [conn2000trust]. Let $m : E \to \mathbb{R}$, $x, s, g \in E$, $\beta > 0$
and $\Delta > 0$. Suppose that $g \neq 0$ or $\tau < 0$, that the step satisfies the sufficient
decrease condition $\kappa_1 \|g\| \min\{\|g\| / \beta, \Delta\} \le m(x) - m(x + s)$ with
$0 < \kappa_1 < 1$, and that it satisfies AA.2 with curvature $\tau$ and constant $\kappa_2$.
Then $m(x + s) < m(x)$ and $s \neq 0$.

**Reading.** Assumes nonzero model gradient or negative model curvature directly at the current
iterate.
-/
theorem theorem_6_6_3 {m : E → ℝ} {x s g : E} {β Δ τ κ₁ κ₂ : ℝ}
    (hβ : 0 < β) (hΔ : 0 < Δ) (hcrit : g ≠ 0 ∨ τ < 0)
    (hfirst : HasSufficientModelDecrease m x s g β Δ κ₁)
    (hsecond : HasNegativeCurvatureDecrease m x s τ Δ κ₂) :
    m (x + s) < m x ∧ s ≠ 0 := by
  have hpred : 0 < m x - m (x + s) := by
    rcases hcrit with hg | hτ
    · have hgn := norm_pos_iff.mpr hg
      exact (mul_pos (mul_pos hfirst.1.1 hgn) (lt_min (div_pos hgn hβ) hΔ)).trans_le hfirst.2
    · have ha : 0 < |τ| := abs_pos.mpr hτ.ne
      exact (mul_pos (mul_pos hsecond.1 ha)
        (lt_min (sq_pos_of_ne_zero hτ.ne) (sq_pos_of_pos hΔ))).trans_le (hsecond.2 hτ)
  exact ⟨sub_pos.mp hpred, fun hs ↦ by simp [hs] at hpred⟩

omit [NormedSpace ℝ E] in
/-- **Equations (6.6.21) and (6.6.28)** of [conn2000trust]. Suppose that $m$, $x$ and $s$ satisfy
AA.2 with curvature $\tau$, radius $\Delta$ and constant $\kappa$. If $a > 0$,
$0 \le r \le \Delta$ and $\tau \le -a$, then
$$\kappa a \min\{a^2, r^2\} \le m(x) - m(x + s).$$
-/
theorem negativeCurvatureDecrease_lower_bound {m : E → ℝ} {x s : E} {τ Δ κ a r : ℝ}
    (hsecond : HasNegativeCurvatureDecrease m x s τ Δ κ)
    (ha : 0 < a) (hr : 0 ≤ r) (hrad : r ≤ Δ) (hτ : τ ≤ -a) :
    κ * a * min (a ^ 2) (r ^ 2) ≤ m x - m (x + s) := by
  have hτneg : τ < 0 := hτ.trans_lt (neg_lt_zero.mpr ha)
  have habs : a ≤ |τ| := by rw [abs_of_neg hτneg]; linarith
  have hsq : a ^ 2 ≤ τ ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ ha.le habs 2
  exact (mul_le_mul (mul_le_mul_of_nonneg_left habs hsecond.1.le)
    (min_le_min hsq (pow_le_pow_left₀ hr hrad 2))
    (le_min (sq_nonneg _) (sq_nonneg _)) (mul_nonneg hsecond.1.le (abs_nonneg _))).trans
    (hsecond.2 hτneg)

variable {f : E → ℝ} {P : BTRParams} {sufficient : ℕ → (E → ℝ) → E → E → Prop}


/-- **Equations (6.6.44), (6.6.46) and (6.6.48)** of [conn2000trust]. The **decrease floor** for a
ratio threshold $\eta$, a constant $\kappa$, a curvature bound $a$ and a radius bound $r$ is
$$\eta \kappa a \min\{a^2, r^2\}.$$

In the displays of the source, $a$ is half the absolute value of the limiting curvature, and $r$
is a lower bound on the radius of the successful iteration. -/
noncomputable def negativeCurvatureDropFloor (η κ a r : ℝ) : ℝ :=
  η * (κ * a * min (a ^ 2) (r ^ 2))

/-- **Equations (6.6.44), (6.6.46) and (6.6.48)** of [conn2000trust]. If $\eta, \kappa, a, r > 0$,
then the decrease floor $\eta \kappa a \min\{a^2, r^2\}$ is positive. -/
theorem negativeCurvatureDropFloor_pos {η κ a r : ℝ}
    (hη : 0 < η) (hκ : 0 < κ) (ha : 0 < a) (hr : 0 < r) :
    0 < negativeCurvatureDropFloor η κ a r :=
  mul_pos hη (mul_pos (mul_pos hκ ha) (lt_min (sq_pos_of_pos ha) (sq_pos_of_pos hr)))

/-- **Equations (6.6.44), (6.6.46) and (6.6.48)** of [conn2000trust]. Consider a run of the basic
trust-region algorithm, and let $p \le k \le q$ with $k$ successful. Let $a > 0$,
$0 \le r \le \Delta_k$ and $\tau \le -a$, and suppose that iteration $k$ satisfies AA.2 with
curvature $\tau$ and constant $\kappa$. Then
$$\eta_1 \kappa a \min\{a^2, r^2\} \le f(x_p) - f(x_{q+1}).$$

One successful step therefore gives the decrease floor for the whole block of iterations from
$p$ to $q$. -/
theorem objective_drop_floor_of_successful_between (run : BTRRun f P sufficient)
    {p k q : ℕ} (hpk : p ≤ k) (hkq : k ≤ q) (hs : k ∈ run.successful)
    {τ κ a r : ℝ} (ha : 0 < a) (hr : 0 ≤ r) (hrad : r ≤ run.Δ k) (hτ : τ ≤ -a)
    (hsecond : HasNegativeCurvatureDecrease (run.model k) (run.x k) (run.s k)
      τ (run.Δ k) κ) :
    negativeCurvatureDropFloor P.η₁ κ a r ≤ f (run.x p) - f (run.x (q + 1)) := by
  have hdrop := (mul_le_mul_of_nonneg_left
    (negativeCurvatureDecrease_lower_bound hsecond ha hr hrad hτ) P.eta₁_pos.le).trans
      (run.objective_drop_of_successful hs)
  exact hdrop.trans (sub_le_sub (run.objective_antitone hpk)
    (run.objective_antitone (Nat.succ_le_succ hkq)))

/-- **Proof of Theorem 6.6.4** of [conn2000trust], uniform model error on small radii. A run of the
basic trust-region algorithm has **small-radius model agreement** if for every $\varepsilon > 0$
there is $\delta > 0$ such that, for all large $k$,
$$\Delta_k \le \delta \implies |f(x_k + s_k) - m_k(x_k + s_k)| \le \varepsilon \Delta_k^2.$$

**Reading.** Makes uniform small-radius trial error a separate hypothesis.
-/
def smallRadiusModelAgreement (run : BTRRun f P sufficient) : Prop :=
  ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ᶠ k in atTop, run.Δ k ≤ δ →
    |f (run.x k + run.s k) - run.model k (run.x k + run.s k)| ≤ ε * run.Δ k ^ 2

/-- **Proof of Theorem 6.6.4** of [conn2000trust], small-radius model error by the argument of Lemma
6.5.3. Consider a run of the basic trust-region algorithm for a twice continuously
differentiable $f$. Suppose that, for all $k$, $m_k$ and $Dm_k$ are differentiable on the
segment $[x_k, x_k + s_k]$, $f(x_k) = m_k(x_k)$ and $Df(x_k) = Dm_k(x_k)$. Suppose that
$\|Df(x_k)\| \to 0$, that the models satisfy AM.5, and that $\|s_k\| \le K \Delta_k$ for all $k$
with $K > 0$. Suppose finally that for every $\varepsilon > 0$ there is $\delta > 0$ such that,
for every $k$ with $\Delta_k \le \delta$ and every $z \in [x_k, x_k + s_k]$,
$$\|D^2 f(z) - D^2 f(x_k)\| + \|D^2 m_k(z) - D^2 m_k(x_k)\| \le \varepsilon.$$
Then the run has small-radius model agreement.

**Reading.** Uses uniform Hessian variation on small trial segments.
-/
theorem smallRadiusModelAgreement_of_hessians (run : BTRRun f P sufficient)
    (hf : ContDiff ℝ 2 f)
    (hm : ∀ k z, z ∈ segment ℝ (run.x k) (run.x k + run.s k) →
      DifferentiableAt ℝ (run.model k) z)
    (hDm : ∀ k z, z ∈ segment ℝ (run.x k) (run.x k + run.s k) →
      DifferentiableAt ℝ (fderiv ℝ (run.model k)) z)
    (hval : ∀ k, f (run.x k) = run.model k (run.x k))
    (hgrad : ∀ k, fderiv ℝ f (run.x k) = fderiv ℝ (run.model k) (run.x k))
    (hcrit : Tendsto (fun k ↦ ‖fderiv ℝ f (run.x k)‖) atTop (𝓝 0))
    (hagree : ModelHessianAgreement f run.model run.x)
    {K : ℝ} (hK : 0 < K) (hstep : ∀ k, ‖run.s k‖ ≤ K * run.Δ k)
    (hvar : ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ k, run.Δ k ≤ δ →
      ∀ z ∈ segment ℝ (run.x k) (run.x k + run.s k),
        ‖fderiv ℝ (fderiv ℝ f) z - fderiv ℝ (fderiv ℝ f) (run.x k)‖ +
        ‖fderiv ℝ (fderiv ℝ (run.model k)) z -
          fderiv ℝ (fderiv ℝ (run.model k)) (run.x k)‖ ≤ ε) :
    smallRadiusModelAgreement run := by
  intro ε hε
  let a := ε / K ^ 2
  have ha : 0 < a := by dsimp [a]; positivity
  obtain ⟨δ, hδ, hv⟩ := hvar a ha
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [(hagree hcrit).eventually (gt_mem_nhds ha)] with k hc hk
  have hB (z : E) (hz : z ∈ segment ℝ (run.x k) (run.x k + run.s k)) :
      ‖fderiv ℝ (fderiv ℝ f) z - fderiv ℝ (fderiv ℝ (run.model k)) z‖ ≤ 2 * a := by
    let F := fderiv ℝ (fderiv ℝ f)
    let M := fderiv ℝ (fderiv ℝ (run.model k))
    change ‖F z - M z‖ ≤ 2 * a
    rw [show F z - M z = (F z - F (run.x k)) + (F (run.x k) - M (run.x k)) -
      (M z - M (run.x k)) by abel]
    have htriangle := norm_sub_le ((F z - F (run.x k)) + (F (run.x k) - M (run.x k)))
      (M z - M (run.x k))
    have hsum := norm_add_le (F z - F (run.x k)) (F (run.x k) - M (run.x k))
    change ‖F (run.x k) - M (run.x k)‖ < a at hc
    have hv' := hv k hk z hz
    change ‖F z - F (run.x k)‖ + ‖M z - M (run.x k)‖ ≤ a at hv'
    linarith only [htriangle, hsum, hc, hv']
  calc
    _ ≤ (1 / 2 : ℝ) * (2 * a) * ‖run.s k‖ ^ 2 :=
      abs_model_error_le hf (hval k) (hgrad k) (hm k) (hDm k) hB
    _ ≤ (1 / 2 : ℝ) * (2 * a) * (K * run.Δ k) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hstep k) 2) (by positivity)
    _ = ε * run.Δ k ^ 2 := by dsimp [a]; field_simp

private theorem objective_drop_tendsto_zero (run : BTRRun f P sufficient)
    (hlower : BddBelow (range f)) :
    Tendsto (fun k ↦ f (run.x k) - f (run.x (k + 1))) atTop (𝓝 0) := by
  have ht := tendsto_atTop_ciInf run.objective_antitone
    (hlower.mono (show range (f ∘ run.x) ⊆ range f from fun _ ⟨k, hk⟩ ↦ ⟨run.x k, hk⟩))
  simpa only [Function.comp_apply, sub_self] using ht.sub (ht.comp (tendsto_add_atTop_nat 1))

/-- **Theorem 6.6.4 proof** of [conn2000trust].

**Reading.** Uses explicit uniform small-radius model agreement.
-/
private theorem eventually_small_radius_very_successful (run : BTRRun f P sufficient)
    (hval : ∀ k, f (run.x k) = run.model k (run.x k))
    (herr : smallRadiusModelAgreement run) {τ : ℕ → ℝ} {κ a : ℝ} (hκ : 0 < κ) (ha : 0 < a)
    (hsecond : ∀ k, HasNegativeCurvatureDecrease (run.model k) (run.x k) (run.s k)
      (τ k) (run.Δ k) κ) :
    ∃ δ > (0 : ℝ), ∀ᶠ k in atTop, τ k ≤ -a → run.Δ k ≤ δ → k ∈ run.verySuccessful := by
  have hη : 0 < 1 - P.η₂ := sub_pos.mpr P.eta₂_lt_one
  obtain ⟨δ, hδ, hd⟩ := herr ((1 - P.η₂) * (κ * a)) (by positivity)
  refine ⟨min a δ, lt_min ha hδ, ?_⟩
  filter_upwards [hd] with k hk hτ hrad
  have hrad' := hrad.trans (min_le_left a δ)
  have hsq := pow_le_pow_left₀ (run.delta_pos k).le hrad' 2
  have hp := negativeCurvatureDecrease_lower_bound (hsecond k) ha (run.delta_pos k).le le_rfl hτ
  rw [min_eq_right hsq] at hp
  have he : |f (run.x k + run.s k) -
      (f (run.x k) - (run.model k (run.x k) - run.model k (run.x k + run.s k)))| ≤
      (1 - P.η₂) * (run.model k (run.x k) - run.model k (run.x k + run.s k)) := by
    rw [hval k, sub_sub_cancel]
    exact (hk (hrad.trans (min_le_right a δ))).trans (by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hp hη.le)
  simpa only [sub_sub_cancel, BTRRun.verySuccessful, Set.mem_ofPred_eq, btrRatio] using
    Optimization.le_reductionRatio_of_abs_sub_le (run.predicted_pos k) he

private theorem radius_upper_bound_of_rejections (run : BTRRun f P sufficient) (N : ℕ)
    (hfail : ∀ k ≥ N, k ∉ run.successful) (j : ℕ) :
    run.Δ (N + j) ≤ P.γ₂ ^ j * run.Δ N := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hh := ((run.radius_update (N + j)).unsuccessful
      (lt_of_not_ge (hfail (N + j) (Nat.le_add_right _ _)))).2
    rw [Nat.add_succ, pow_succ]
    exact hh.trans (by
      rw [mul_comm (P.γ₂ ^ j), mul_assoc]
      exact mul_le_mul_of_nonneg_left ih (P.gamma₁_pos.trans_le P.gamma₁_le_gamma₂).le)

/-- **Theorem 6.6.4** of [conn2000trust], in the form of a frequent lower bound. Consider a run of
the basic trust-region algorithm for $f$ bounded below, with $f(x_k) = m_k(x_k)$ for all $k$ and
with small-radius model agreement. Let $\lambda_k$ and $\tau_k$ be real sequences with
$|\lambda_k - \tau_k| \to 0$, and let $\kappa > 0$. Suppose that every iteration satisfies AA.2
with curvature $\tau_k$ and constant $\kappa$. Then for every $\varepsilon > 0$,
$$\lambda_k > -\varepsilon \quad \text{for infinitely many } k,$$
that is, $\limsup_k \lambda_k \ge 0$.

**Reading.** The proof in the source uses a model error of order $o(\Delta_k^2)$ on small radii.
The statement assumes this estimate explicitly, as
`ConnGouldToint.Chapter06.smallRadiusModelAgreement`. It follows from uniform variation of the
objective and model Hessians on small trial segments, by
`ConnGouldToint.Chapter06.smallRadiusModelAgreement_of_hessians` or
`ConnGouldToint.Chapter06.smallRadiusModelAgreement_of_uniformHessians`.

In the source, $\lambda_k$ is the least eigenvalue of $\nabla^2 f(x_k)$ and $\tau_k$ is that of
the model Hessian; the hypothesis $|\lambda_k - \tau_k| \to 0$ stands for AM.5. -/
theorem theorem_6_6_4 (run : BTRRun f P sufficient) {curv τ : ℕ → ℝ} {κ : ℝ} (hκ : 0 < κ)
    (hval : ∀ k, f (run.x k) = run.model k (run.x k))
    (hlower : BddBelow (range f)) (herr : smallRadiusModelAgreement run)
    (hagree : Tendsto (fun k ↦ |curv k - τ k|) atTop (𝓝 0))
    (hsecond : ∀ k, HasNegativeCurvatureDecrease (run.model k) (run.x k) (run.s k)
      (τ k) (run.Δ k) κ) :
    ∀ ε > (0 : ℝ), ∃ᶠ k in atTop, -ε < curv k := by
  intro ε hε
  by_contra! hneg
  have hcurv : ∀ᶠ k in atTop, curv k ≤ -ε := hneg
  let a := ε / 2
  have ha : 0 < a := by dsimp [a]; positivity
  have hτ : ∀ᶠ k in atTop, τ k ≤ -a := by
    filter_upwards [hcurv, hagree.eventually (gt_mem_nhds ha)] with k hk hdiff
    have h := neg_abs_le (curv k - τ k)
    dsimp [a] at *
    linarith only [hk, hdiff, h]
  obtain ⟨δ, hδ, hvery⟩ := eventually_small_radius_very_successful run hval herr hκ ha hsecond
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hτ.and hvery)
  let r := min (P.γ₁ * δ) (run.Δ N)
  have hr : 0 < r := lt_min (mul_pos P.gamma₁_pos hδ) (run.delta_pos N)
  have hrad (k : ℕ) (hk : N ≤ k) : r ≤ run.Δ k := by
    have h := run.delta_lower_bound_from N (θ := δ)
      (fun j hj hr ↦ (hN j hj).2 (hN j hj).1 hr) (k - N)
    change r ≤ run.Δ (N + (k - N)) at h
    simpa only [Nat.add_sub_of_le hk] using h
  let d := negativeCurvatureDropFloor P.η₁ κ a r
  have hd : 0 < d := negativeCurvatureDropFloor_pos P.eta₁_pos hκ ha hr
  obtain ⟨M, hM⟩ := eventually_atTop.mp
    ((objective_drop_tendsto_zero run hlower).eventually (gt_mem_nhds hd))
  let L := max N M
  have hfail (k : ℕ) (hk : L ≤ k) : k ∉ run.successful := by
    intro hs
    have hkN := (le_max_left N M).trans hk
    have hp := negativeCurvatureDecrease_lower_bound (hsecond k) ha hr.le (hrad k hkN)
      (hN k hkN).1
    have hv := (mul_le_mul_of_nonneg_left hp P.eta₁_pos.le).trans
      (run.objective_drop_of_successful hs)
    exact (hM k ((le_max_right N M).trans hk)).not_ge hv
  have hlim : Tendsto (fun j : ℕ ↦ P.γ₂ ^ j * run.Δ L) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (P.gamma₁_pos.trans_le P.gamma₁_le_gamma₂).le P.gamma₂_lt_one).mul_const (run.Δ L)
  obtain ⟨j, hj⟩ := (hlim.eventually (gt_mem_nhds hr)).exists
  exact hj.not_ge ((hrad _ ((le_max_left N M).trans (Nat.le_add_right L j))).trans
    (radius_upper_bound_of_rejections run L hfail j))

/-- **Theorem 6.6.5** of [conn2000trust]. Consider a run of the basic trust-region algorithm whose
iterates lie in a compact set $K$. Let $\lambda : E \to \mathbb{R}$ be continuous, let $Df$ be
continuous, and suppose that $\|Df(x_k)\| \to 0$ and that for every $\varepsilon > 0$,
$\lambda(x_k) > -\varepsilon$ for infinitely many $k$. Then there are $z \in K$ and a
subsequence $x_{k_i} \to z$ with
$$Df(z) = 0 \quad \text{and} \quad \lambda(z) \ge 0.$$

**Reading.** Abstract continuous curvature on a real normed space and explicit first-order and
frequent curvature bounds.
-/
theorem theorem_6_6_5 (run : BTRRun f P sufficient) {curv : E → ℝ} (hcurv : Continuous curv)
    {K : Set E} (hK : IsCompact K) (hx : ∀ k, run.x k ∈ K)
    (hgrad : Continuous (fderiv ℝ f))
    (hcrit : Tendsto (fun k ↦ ‖fderiv ℝ f (run.x k)‖) atTop (𝓝 0))
    (hfreq : ∀ ε > (0 : ℝ), ∃ᶠ k in atTop, -ε < curv (run.x k)) :
    ∃ z ∈ K, ∃ j : ℕ → ℕ, StrictMono j ∧ Tendsto (run.x ∘ j) atTop (𝓝 z) ∧
      fderiv ℝ f z = 0 ∧ 0 ≤ curv z := by
  let e (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  obtain ⟨j, hj, hjcurv⟩ := extraction_forall_of_frequently fun n : ℕ ↦ hfreq (e n) (by
    dsimp [e]; positivity)
  obtain ⟨z, hz, i, hi, hzi⟩ := hK.isSeqCompact (fun n ↦ hx (j n))
  let q := j ∘ i
  have hq : StrictMono q := hj.comp hi
  have hzq : Tendsto (run.x ∘ q) atTop (𝓝 z) := hzi
  have hnorm := (hgrad.norm.continuousAt.tendsto.comp hzq :
    Tendsto (fun n ↦ ‖fderiv ℝ f (run.x (q n))‖) atTop (𝓝 ‖fderiv ℝ f z‖))
  have hstat := norm_eq_zero.mp (tendsto_nhds_unique hnorm (hcrit.comp hq.tendsto_atTop))
  have he : Tendsto (fun n ↦ -e (i n)) atTop (𝓝 0) := by
    have he' : Tendsto (e ∘ i) atTop (𝓝 0) :=
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hi.tendsto_atTop
    simpa only [Function.comp_apply, neg_zero] using he'.neg
  have hcurvq : Tendsto (fun n ↦ curv (run.x (q n))) atTop (𝓝 (curv z)) :=
    hcurv.continuousAt.tendsto.comp hzq
  exact ⟨z, hz, q, hq, hzq, hstat, le_of_tendsto_of_tendsto he hcurvq
    (Eventually.of_forall fun n ↦ (hjcurv (i n)).le)⟩

/-- **Lemma 6.6.6** of [conn2000trust], for successful iterations as in its proof. Consider a run of
the basic trust-region algorithm for $f$ bounded below. Let $\kappa > 0$, $a > 0$, and suppose
that every iteration satisfies AA.2 with curvature $\tau_k$ and constant $\kappa$. Then for
every $\varepsilon > 0$, for all large $k$: if $k$ is successful and $\tau_k \le -a$, then
$\Delta_k < \varepsilon$.

**Reading.** States the successful-subsequence case of the proof separately with explicit error
control.
-/
theorem lemma_6_6_6_successful (run : BTRRun f P sufficient) (hlower : BddBelow (range f))
    {τ : ℕ → ℝ} {κ a : ℝ} (hκ : 0 < κ) (ha : 0 < a)
    (hsecond : ∀ k, HasNegativeCurvatureDecrease (run.model k) (run.x k) (run.s k)
      (τ k) (run.Δ k) κ) :
    ∀ ε > (0 : ℝ), ∀ᶠ k in atTop, k ∈ run.successful → τ k ≤ -a → run.Δ k < ε := by
  intro ε hε
  let d := P.η₁ * (κ * a * min (a ^ 2) (ε ^ 2))
  have hd : 0 < d := mul_pos P.eta₁_pos (mul_pos (mul_pos hκ ha)
    (lt_min (sq_pos_of_pos ha) (sq_pos_of_pos hε)))
  filter_upwards [(objective_drop_tendsto_zero run hlower).eventually (gt_mem_nhds hd)] with k hk
  intro hs hτ
  by_contra! hrad
  have hp := negativeCurvatureDecrease_lower_bound (hsecond k) ha hε.le hrad hτ
  exact hk.not_ge ((mul_le_mul_of_nonneg_left hp P.eta₁_pos.le).trans
    (run.objective_drop_of_successful hs))

private theorem stationary_of_subsequence (run : BTRRun f P sufficient) {z : E}
    {j : ℕ → ℕ} (hj : StrictMono j) (hz : Tendsto (run.x ∘ j) atTop (𝓝 z))
    (hgrad : Continuous (fderiv ℝ f))
    (hcrit : Tendsto (fun k ↦ ‖fderiv ℝ f (run.x k)‖) atTop (𝓝 0)) :
    fderiv ℝ f z = 0 := by
  exact norm_eq_zero.mp (tendsto_nhds_unique (hgrad.norm.continuousAt.tendsto.comp hz)
    (hcrit.comp hj.tendsto_atTop))

/-- **Theorem 6.6.7 proof** of [conn2000trust].

**Reading.** Uses abstract continuous objective curvature and vanishing model discrepancy.
-/
private theorem eventually_modelCurvature_negative_near (run : BTRRun f P sufficient)
    {curv : E → ℝ} {τ : ℕ → ℝ} {z : E} (hcurv : ContinuousAt curv z)
    (hagree : Tendsto (fun k ↦ |curv (run.x k) - τ k|) atTop (𝓝 0))
    {a : ℝ} (ha : 0 < a) (hz : curv z < -(2 * a)) :
    ∃ r > (0 : ℝ), ∀ᶠ k in atTop, dist (run.x k) z < r → τ k ≤ -a := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hcurv.tendsto.eventually_lt_const hz)
  refine ⟨r, hr, ?_⟩
  filter_upwards [hagree.eventually_lt_const ha] with k hk hdist
  have hval : curv (run.x k) < -(2 * a) := hball hdist
  linarith only [hval, hk, neg_abs_le (curv (run.x k) - τ k)]

private theorem iterate_dist_le_of_successful (run : BTRRun f P sufficient) {k : ℕ}
    (hk : k ∈ run.successful) : dist (run.x (k + 1)) (run.x k) ≤ ‖run.s k‖ := by
  have hratio : P.η₁ ≤ btrRatio f (run.model k) (run.x k) (run.s k) := hk
  rw [run.iterate_update, Optimization.acceptStep_of_le hratio, dist_eq_norm,
    add_sub_cancel_left]

private theorem exists_successful_at_same_iterate (run : BTRRun f P sufficient)
    (N : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (hforce : ∀ k ≥ N, run.x k = run.x N → run.Δ k ≤ δ → k ∈ run.successful) :
    ∃ k ≥ N, run.x k = run.x N ∧ k ∈ run.successful := by
  by_contra! h
  have hfails (j : ℕ) : run.x (N + j) = run.x N ∧ N + j ∉ run.successful := by
    induction j with
    | zero => exact ⟨by simp, h _ (by simp) (by simp)⟩
    | succ j ih =>
      have hx : run.x (N + (j + 1)) = run.x N := by
        rw [Nat.add_succ, run.iterate_eq_of_unsuccessful ih.2, ih.1]
      exact ⟨hx, h _ (Nat.le_add_right _ _) hx⟩
  have hfail (k : ℕ) (hk : N ≤ k) : k ∉ run.successful := by
    simpa only [Nat.add_sub_of_le hk] using (hfails (k - N)).2
  have ht : Tendsto (fun j : ℕ ↦ P.γ₂ ^ j * run.Δ N) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (P.gamma₁_pos.trans_le P.gamma₁_le_gamma₂).le P.gamma₂_lt_one).mul_const (run.Δ N)
  obtain ⟨j, hj⟩ := (ht.eventually_lt_const hδ).exists
  exact (hfails j).2 (hforce _ (Nat.le_add_right _ _) (hfails j).1
    ((radius_upper_bound_of_rejections run N hfail j).trans hj.le))

/-- **Lemma 6.6.6** of [conn2000trust], with (6.6.24)–(6.6.25). Consider a run of the basic
trust-region algorithm for $f$ bounded below, with $f(x_k) = m_k(x_k)$ for all $k$ and with
small-radius model agreement. Let $x_{k_i} \to z$ for a strictly increasing sequence $(k_i)$.
Let $\lambda : E \to \mathbb{R}$ be continuous at $z$ with $\lambda(z) < 0$, and let
$|\lambda(x_k) - \tau_k| \to 0$. Suppose that every iteration satisfies AA.2 with curvature
$\tau_k$ and a constant $\kappa > 0$. Then
$$\Delta_{k_i} \to 0 \quad \text{and} \quad \tau_{k_i} \le \lambda(z) / 2 \text{ for all large }
  i.$$

The subsequence may contain rejected trials. For a rejected trial, the proof follows the
unchanged iterate to its first successful trial. The radius at that trial cannot be smaller than
the small-radius acceptance threshold by more than the contraction factor of one step.

**Reading.** Abstract model curvature and explicit uniform model error.
-/
theorem lemma_6_6_6 (run : BTRRun f P sufficient) {z : E}
    {j : ℕ → ℕ} (hj : StrictMono j) (hz : Tendsto (run.x ∘ j) atTop (𝓝 z))
    {curv : E → ℝ} (hcurv : ContinuousAt curv z) (hneg : curv z < 0) {τ : ℕ → ℝ}
    (hagree : Tendsto (fun k ↦ |curv (run.x k) - τ k|) atTop (𝓝 0))
    (hval : ∀ k, f (run.x k) = run.model k (run.x k))
    (hlower : BddBelow (range f)) (herr : smallRadiusModelAgreement run)
    {κ : ℝ} (hκ : 0 < κ)
    (hsecond : ∀ k, HasNegativeCurvatureDecrease (run.model k) (run.x k) (run.s k)
      (τ k) (run.Δ k) κ) :
    Tendsto (run.Δ ∘ j) atTop (𝓝 0) ∧ ∀ᶠ i in atTop, τ (j i) ≤ curv z / 2 := by
  let a := -curv z / 2
  have ha : 0 < a := div_pos (neg_pos.mpr hneg) (by norm_num)
  have haz : curv z < -(2 * (a / 2)) := by dsimp [a]; linarith
  obtain ⟨r, hr, hnear⟩ :=
    eventually_modelCurvature_negative_near run hcurv hagree (half_pos ha) haz
  obtain ⟨δ, hδ, hvery⟩ :=
    eventually_small_radius_very_successful run hval herr hκ (half_pos ha) hsecond
  have hτlim : Tendsto (τ ∘ j) atTop (𝓝 (curv z)) := by
    have ht : Tendsto (fun i ↦ curv (run.x (j i)) - τ (j i)) atTop (𝓝 0) := by
      apply squeeze_zero_norm
      · intro i
        rfl
      · exact hagree.comp hj.tendsto_atTop
    have hc : Tendsto (fun i ↦ curv (run.x (j i))) atTop (𝓝 (curv z)) :=
      hcurv.tendsto.comp hz
    change Tendsto (fun i ↦ τ (j i)) atTop (𝓝 (curv z))
    simpa only [sub_sub_cancel, sub_zero] using hc.sub ht
  refine ⟨?_, (hτlim.eventually_lt_const (by linarith : curv z < curv z / 2)).mono
    fun _ h ↦ h.le⟩
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let b := min ε (P.γ₁ * δ)
  have hb : 0 < b := lt_min hε (mul_pos P.gamma₁_pos hδ)
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((hnear.and hvery).and (lemma_6_6_6_successful run hlower hκ (half_pos ha) hsecond b hb))
  filter_upwards [hj.tendsto_atTop.eventually_ge_atTop N,
    hz.eventually (Metric.ball_mem_nhds z hr)] with i hi hiz
  let n := j i
  have hforce (k : ℕ) (hk : n ≤ k) (hx : run.x k = run.x n) :
      τ k ≤ -(a / 2) := (hN k (hi.trans hk)).1.1 (by rwa [hx])
  have hforce' (k : ℕ) (hk : n ≤ k) (hx : run.x k = run.x n) (hd : run.Δ k ≤ δ) :
      k ∈ run.successful := run.verySuccessful_subset_successful
    ((hN k (hi.trans hk)).1.2 (hforce k hk hx) hd)
  obtain ⟨k, hk, _, hs⟩ := exists_successful_at_same_iterate run n hδ hforce'
  have hex : ∃ l, n + l ∈ run.successful :=
    ⟨k - n, by simpa only [Nat.add_sub_of_le hk] using hs⟩
  classical
  let l := Nat.find hex
  have hls : n + l ∈ run.successful := Nat.find_spec hex
  have hfail (p : ℕ) (hp : p < l) : n + p ∉ run.successful := Nat.find_min hex hp
  have hx (p : ℕ) (hp : p ≤ l) : run.x (n + p) = run.x n := by
    induction p with
    | zero => simp
    | succ p ih =>
      rw [Nat.add_succ, run.iterate_eq_of_unsuccessful (hfail p (Nat.lt_of_succ_le hp))]
      exact ih ((Nat.le_succ p).trans hp)
  have hlN := hi.trans (Nat.le_add_right n l)
  have hsmall := (hN _ hlN).2 hls (hforce _ (Nat.le_add_right n l) (hx _ le_rfl))
  have hlzero : l = 0 := by
    cases hl : l with
    | zero => rfl
    | succ p =>
      exfalso
      have hp : p < l := hl ▸ Nat.lt_succ_self p
      have hrad : δ < run.Δ (n + p) := lt_of_not_ge fun h ↦
        hfail p hp (hforce' _ (Nat.le_add_right _ _) (hx _ hp.le) h)
      have hlow := ((run.radius_update (n + p)).unsuccessful (lt_of_not_ge (hfail p hp))).1
      have hh : b ≤ run.Δ (n + l) := by
        rw [hl, Nat.add_succ]
        exact (min_le_right _ _).trans
          ((mul_le_mul_of_nonneg_left hrad.le P.gamma₁_pos.le).trans hlow)
      exact hsmall.not_ge hh
  rw [hlzero, Nat.add_zero] at hsmall
  change dist (run.Δ n) 0 < ε
  simpa only [dist_zero_right, Real.norm_eq_abs, abs_of_pos (run.delta_pos n)] using
    hsmall.trans_le (min_le_left _ _)

/-- **Proofs of Theorems 6.6.7 and 8.1.4** of [conn2000trust], local curvature argument. Let $E$ be
a proper metric space, so that closed balls are compact. Consider a run of the basic
trust-region algorithm for $f$ bounded below, with $f(x_k) = m_k(x_k)$, $\|s_k\| \le K \Delta_k$
for all $k$ with $K > 0$, and small-radius model agreement. Suppose that every iteration
satisfies AA.2 with curvature $\tau_k$ and a constant $\kappa > 0$. Let $x_{k_i} \to z$ for a
strictly increasing sequence $(k_i)$, and suppose that $z$ is an isolated limit point: there is
$r > 0$ such that every limit $y$ of a subsequence with $\|y - z\| < r$ equals $z$. Then there
are no $a > 0$ and $r' > 0$ such that $\tau_k \le -a$ for all large $k$ with $\|x_k - z\| < r'$.

**Reading.** Abstract curvature and properness of the ambient normed space.
-/
theorem not_negative_curvature_near_isolated_limit [ProperSpace E] (run : BTRRun f P sufficient)
    {z : E}
    {j : ℕ → ℕ} (hj : StrictMono j) (hz : Tendsto (run.x ∘ j) atTop (𝓝 z))
    (hiso : ∃ r > (0 : ℝ), ∀ y, dist y z < r → ∀ i : ℕ → ℕ,
      StrictMono i → Tendsto (run.x ∘ i) atTop (𝓝 y) → y = z)
    {τ : ℕ → ℝ} {a κ K : ℝ} (ha : 0 < a) (hκ : 0 < κ) (hK : 0 < K)
    (hval : ∀ k, f (run.x k) = run.model k (run.x k))
    (hlower : BddBelow (range f)) (herr : smallRadiusModelAgreement run)
    (hstep : ∀ k, ‖run.s k‖ ≤ K * run.Δ k)
    (hsecond : ∀ k, HasNegativeCurvatureDecrease (run.model k) (run.x k) (run.s k)
      (τ k) (run.Δ k) κ)
    (hlocal : ∃ r > (0 : ℝ), ∀ᶠ k in atTop, dist (run.x k) z < r → τ k ≤ -a) :
    False := by
  obtain ⟨r₀, hr₀, hlocal⟩ := hlocal
  obtain ⟨r₁, hr₁, h₁⟩ := hiso
  let r := min r₀ r₁
  have hr : 0 < r := lt_min hr₀ hr₁
  have hgap : ∀ᶠ k in atTop, dist (run.x k) z ≤ r / 4 ∨ r / 2 ≤ dist (run.x k) z := by
    by_contra! hbad
    obtain ⟨i, hi, hib⟩ := extraction_of_frequently_atTop hbad
    let A := Metric.closedBall z (r / 2) ∩ {y : E | r / 4 ≤ dist y z}
    have hA : IsCompact A := (isCompact_closedBall _ _).inter_right
      (isClosed_le continuous_const (continuous_id.dist continuous_const))
    obtain ⟨y, hy, p, hp, hyp⟩ := hA.isSeqCompact
      (fun n ↦ ⟨(hib n).2.le, (hib n).1.le⟩)
    have hy' := h₁ y (lt_of_le_of_lt hy.1 (by dsimp [r] at *; linarith [min_le_right r₀ r₁]))
      (i ∘ p) (hi.comp hp) hyp
    subst y
    exact (not_le_of_gt (div_pos hr (by norm_num : (0 : ℝ) < 4))) (by simpa using hy.2)
  let e := r / (4 * K)
  have he : 0 < e := div_pos hr (by positivity)
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((hlocal.and hgap).and (lemma_6_6_6_successful run hlower hκ ha hsecond e he))
  have hnear₀ : ∃ k ≥ N, dist (run.x k) z ≤ r / 4 := by
    obtain ⟨i, hiN, hiz⟩ := ((hj.tendsto_atTop.eventually_ge_atTop N).and
      (hz.eventually (Metric.ball_mem_nhds z (div_pos hr (by norm_num : (0 : ℝ) < 4))))).exists
    exact ⟨j i, hiN, (show dist (run.x (j i)) z < r / 4 from hiz).le⟩
  obtain ⟨k, hkN, hk⟩ := hnear₀
  have hnear (n : ℕ) : dist (run.x (k + n)) z ≤ r / 4 := by
    induction n with
    | zero => simpa only [Nat.add_zero] using hk
    | succ n ih =>
      have hnN := hkN.trans (Nat.le_add_right k n)
      by_cases hs : k + n ∈ run.successful
      · have ht := (hN _ hnN).1.1
          (ih.trans_lt (by linarith [min_le_left r₀ r₁]))
        have hrad := (hN _ hnN).2 hs ht
        have hs' := (iterate_dist_le_of_successful run hs).trans (hstep (k + n))
        have hs'' : dist (run.x (k + n + 1)) (run.x (k + n)) < r / 4 := by
          apply hs'.trans_lt
          calc
            K * run.Δ (k + n) < K * e := mul_lt_mul_of_pos_left hrad hK
            _ = r / 4 := by dsimp [e]; field_simp
        have hdist := dist_triangle (run.x (k + n + 1)) (run.x (k + n)) z
        rw [Nat.add_succ]
        exact ((hN _ (hnN.trans (Nat.le_succ _))).1.2).resolve_right (by linarith)
      · rw [Nat.add_succ, run.iterate_eq_of_unsuccessful hs]
        exact ih
  have hτ : ∀ᶠ n in atTop, τ n ≤ -a := eventually_atTop.mpr ⟨k, fun n hn ↦ by
    have hh := hnear (n - k)
    rw [Nat.add_sub_of_le hn] at hh
    exact (hN n (hkN.trans hn)).1.1 (hh.trans_lt (by linarith [min_le_left r₀ r₁]))⟩
  have hfre := theorem_6_6_4 run (curv := τ) (τ := τ) hκ hval hlower herr (by simp) hsecond a ha
  exact hfre (hτ.mono fun _ h => not_lt_of_ge h)

/-- **Theorem 6.6.7** of [conn2000trust]. Let $E$ be a proper metric space, so that closed balls are
compact. Consider a run of the basic trust-region algorithm for $f$ bounded below with
continuous $Df$, with $f(x_k) = m_k(x_k)$, $\|s_k\| \le K \Delta_k$ for all $k$ with $K > 0$,
and small-radius model agreement. Suppose that $\|Df(x_k)\| \to 0$ and that every iteration
satisfies AA.2 with curvature $\tau_k$ and a constant $\kappa > 0$. Let $x_{k_i} \to z$ for a
strictly increasing sequence $(k_i)$, where $z$ is an isolated limit point: there is $r > 0$
such that every limit $y$ of a subsequence with $\|y - z\| < r$ equals $z$. Let
$\lambda : E \to \mathbb{R}$ be continuous at $z$ with $|\lambda(x_k) - \tau_k| \to 0$. Then
$$Df(z) = 0 \quad \text{and} \quad \lambda(z) \ge 0.$$

The small-radius conclusion of Lemma 6.6.6 is needed only for the successful steps.

**Reading.** Uses proper normed spaces, abstract curvature, and explicit model error control.
-/
theorem theorem_6_6_7 [ProperSpace E] (run : BTRRun f P sufficient) {z : E}
    {j : ℕ → ℕ} (hj : StrictMono j) (hz : Tendsto (run.x ∘ j) atTop (𝓝 z))
    (hiso : ∃ r > (0 : ℝ), ∀ y, dist y z < r → ∀ i : ℕ → ℕ,
      StrictMono i → Tendsto (run.x ∘ i) atTop (𝓝 y) → y = z)
    {curv : E → ℝ} (hcurv : ContinuousAt curv z) {τ : ℕ → ℝ}
    (hagree : Tendsto (fun k ↦ |curv (run.x k) - τ k|) atTop (𝓝 0))
    (hgrad : Continuous (fderiv ℝ f))
    (hcrit : Tendsto (fun k ↦ ‖fderiv ℝ f (run.x k)‖) atTop (𝓝 0))
    (hval : ∀ k, f (run.x k) = run.model k (run.x k))
    (hlower : BddBelow (range f)) (herr : smallRadiusModelAgreement run)
    {κ K : ℝ} (hκ : 0 < κ) (hK : 0 < K) (hstep : ∀ k, ‖run.s k‖ ≤ K * run.Δ k)
    (hsecond : ∀ k, HasNegativeCurvatureDecrease (run.model k) (run.x k) (run.s k)
      (τ k) (run.Δ k) κ) :
    fderiv ℝ f z = 0 ∧ 0 ≤ curv z := by
  refine ⟨stationary_of_subsequence run hj hz hgrad hcrit, ?_⟩
  by_contra! hneg
  let a := -curv z / 4
  have ha : 0 < a := div_pos (neg_pos.mpr hneg) (by norm_num)
  have haz : curv z < -(2 * a) := by dsimp [a]; linarith
  obtain ⟨r, hr, hnear⟩ := eventually_modelCurvature_negative_near run hcurv hagree ha haz
  exact not_negative_curvature_near_isolated_limit run hj hz hiso ha hκ hK hval hlower herr hstep
    hsecond ⟨r, hr, hnear⟩

/-- **Assumption AA.3** of [conn2000trust], preceding Theorem 6.6.8. A run of the basic trust-region
algorithm has **forced radius expansion** with factors $\gamma_3, \gamma_4$ and cap $\Delta_c$
if $1 < \gamma_3 \le \gamma_4$, $\Delta_c > 0$, and every very successful iteration $k$ with
$\Delta_k \le \Delta_c$ has
$$\gamma_3 \Delta_k \le \Delta_{k+1} \le \gamma_4 \Delta_k.$$
-/
def HasForcedRadiusExpansion (run : BTRRun f P sufficient) (γ₃ γ₄ cap : ℝ) : Prop :=
  1 < γ₃ ∧ γ₃ ≤ γ₄ ∧ 0 < cap ∧ ∀ k ∈ run.verySuccessful, run.Δ k ≤ cap →
    γ₃ * run.Δ k ≤ run.Δ (k + 1) ∧ run.Δ (k + 1) ≤ γ₄ * run.Δ k


/-- **Equation (6.6.43)** of [conn2000trust]. For an expansion cap $\Delta_c$ and a small-radius
acceptance threshold $\theta$, the **expansion threshold** is $\min\{\Delta_c, \theta\}$. -/
def curvatureExpansionThreshold (cap θ : ℝ) : ℝ := min cap θ

/-- **Equations (6.6.43)–(6.6.46)** of [conn2000trust], decrease at the first crossing of the
expansion threshold. Consider a run of the basic trust-region algorithm with forced radius
expansion (factors $\gamma_3, \gamma_4$, cap $\Delta_c$), and let $\theta > 0$ and
$\bar\Delta = \min\{\Delta_c, \theta\}$. Let $p \le j \le q$ with $p$ successful. Suppose that:

* every $k$ with $p \le k \le q$ and $\Delta_k \le \theta$ is very successful;
* $\Delta_k \le \bar\Delta$ for $p \le k < j$, and $\Delta_j > \bar\Delta$;
* $a > 0$ and $\tau_k \le -a$ for $p \le k \le q$, and every iteration satisfies AA.2 with
  curvature $\tau_k$ and constant $\kappa$.

If $j$ is successful, then $\eta_1 \kappa a \min\{a^2, \bar\Delta^2\} \le f(x_p) - f(x_{q+1})$.
If $j$ is not successful, then $\eta_1 \kappa a \min\{a^2, (\bar\Delta / \gamma_4)^2\} \le
f(x_p) - f(x_{q+1})$.

In the second case the bound comes from the preceding very successful iteration and its radius
lower bound. -/
theorem objective_drop_at_first_curvature_threshold_crossing (run : BTRRun f P sufficient)
    {p j q : ℕ} (hp : p ∈ run.successful) (hpj : p ≤ j) (hjq : j ≤ q)
    {γ₃ γ₄ cap θ : ℝ} (hexp : HasForcedRadiusExpansion run γ₃ γ₄ cap) (hθ : 0 < θ)
    (hsmall : ∀ k, p ≤ k → k ≤ q → run.Δ k ≤ θ → k ∈ run.verySuccessful)
    (hfirst : ∀ k, p ≤ k → k < j → run.Δ k ≤ curvatureExpansionThreshold cap θ)
    (hcross : curvatureExpansionThreshold cap θ < run.Δ j)
    {τ : ℕ → ℝ} {κ a : ℝ} (ha : 0 < a)
    (hτ : ∀ k, p ≤ k → k ≤ q → τ k ≤ -a)
    (hsecond : ∀ k, HasNegativeCurvatureDecrease (run.model k) (run.x k) (run.s k)
      (τ k) (run.Δ k) κ) :
    (j ∈ run.successful → negativeCurvatureDropFloor P.η₁ κ a
      (curvatureExpansionThreshold cap θ) ≤ f (run.x p) - f (run.x (q + 1))) ∧
    (j ∉ run.successful → negativeCurvatureDropFloor P.η₁ κ a
      (curvatureExpansionThreshold cap θ / γ₄) ≤ f (run.x p) - f (run.x (q + 1))) := by
  obtain ⟨hγ₃, hγ₄, hcap, hgrow⟩ := hexp
  have hγ : 0 < γ₄ := by linarith
  have ht : 0 < curvatureExpansionThreshold cap θ := lt_min hcap hθ
  constructor
  · intro hs
    exact objective_drop_floor_of_successful_between run hpj hjq hs ha ht.le hcross.le
      (hτ j hpj hjq) (hsecond j)
  · intro hs
    have hpj' : p < j := lt_of_le_of_ne hpj (fun h ↦ hs (h ▸ hp))
    let k := j - 1
    have hpk : p ≤ k := by dsimp [k]; omega
    have hkj : k < j := by dsimp [k]; omega
    have hkq : k ≤ q := hkj.le.trans hjq
    have hbound := hfirst k hpk hkj
    have hv := hsmall k hpk hkq (hbound.trans (min_le_right _ _))
    have hstep := (hgrow k hv (hbound.trans (min_le_left _ _))).2
    have he : k + 1 = j := by dsimp [k]; omega
    rw [he] at hstep
    exact objective_drop_floor_of_successful_between run hpk hkq
      (run.verySuccessful_subset_successful hv) ha (div_nonneg ht.le hγ.le)
      ((div_le_iff₀ hγ).mpr (by simpa [mul_comm] using hcross.le.trans hstep))
      (hτ k hpk hkq) (hsecond k)

/-- **Proof of Theorem 6.6.8** of [conn2000trust], the radius bound preceding (6.6.48). For a growth
factor $\gamma$, a neighborhood radius $R$ and a norm bound $K$, the **exit radius** is
$$\frac{(\gamma - 1) R}{2 \gamma K}.$$

Its value is $0$ when $\gamma K = 0$. -/
noncomputable def curvatureExitRadius (growth neighborhood normBound : ℝ) : ℝ :=
  (growth - 1) * neighborhood / (2 * growth * normBound)

/-- **Equations (6.6.42), (6.6.47) and (6.6.48)** of [conn2000trust]. Consider a run of the basic
trust-region algorithm, and let $p, n \in \mathbb{N}$, $\gamma > 1$, $R > 0$ and $K > 0$.
Suppose that $\gamma \Delta_{p+i} \le \Delta_{p+i+1}$ for $i < n$, that
$$\frac{R}{2} \le K \sum_{i=0}^{n} \Delta_{p+i},$$
and that iteration $p + n$ is successful and satisfies AA.2 with a curvature $\tau \le -a$,
$a > 0$, and constant $\kappa$. Then
$$\eta_1 \kappa a \min\{a^2, \rho^2\} \le f(x_p) - f(x_{p+n+1}), \qquad \rho =
  \frac{(\gamma - 1) R}{2 \gamma K}.$$

So a block of geometrically growing radii whose total length reaches $R / (2K)$ gives a fixed
objective decrease. -/
theorem objective_drop_of_curvature_expansion_block (run : BTRRun f P sufficient)
    (p n : ℕ) {γ R K : ℝ} (hγ : 1 < γ) (hR : 0 < R) (hK : 0 < K)
    (hgrow : ∀ i < n, γ * run.Δ (p + i) ≤ run.Δ (p + (i + 1)))
    (hpath : R / 2 ≤ K * ∑ i ∈ Finset.range (n + 1), run.Δ (p + i))
    (hs : p + n ∈ run.successful) {τ κ a : ℝ} (ha : 0 < a) (hτ : τ ≤ -a)
    (hsecond : HasNegativeCurvatureDecrease (run.model (p + n)) (run.x (p + n))
      (run.s (p + n)) τ (run.Δ (p + n)) κ) :
    negativeCurvatureDropFloor P.η₁ κ a (curvatureExitRadius γ R K) ≤
      f (run.x p) - f (run.x (p + n + 1)) := by
  have htel (m : ℕ) (hm : m ≤ n) :
      (γ - 1) * ∑ i ∈ Finset.range m, run.Δ (p + i) ≤ run.Δ (p + m) - run.Δ p := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, mul_add]
      have hh := hgrow m (by omega)
      have hi := ih (by omega)
      linarith only [hh, hi]
  have hsum :
      (γ - 1) * (∑ i ∈ Finset.range (n + 1), run.Δ (p + i)) ≤ γ * run.Δ (p + n) := by
    rw [Finset.sum_range_succ, mul_add]
    have ht := htel n le_rfl
    linarith only [ht, run.delta_pos p]
  have hscaled := (mul_le_mul_of_nonneg_left hpath (sub_nonneg.mpr hγ.le)).trans
    (show (γ - 1) * (K * ∑ i ∈ Finset.range (n + 1), run.Δ (p + i)) ≤
        K * (γ * run.Δ (p + n)) by
      rw [mul_left_comm (γ - 1)]
      exact mul_le_mul_of_nonneg_left hsum hK.le)
  have hrad : curvatureExitRadius γ R K ≤ run.Δ (p + n) := by
    unfold curvatureExitRadius
    apply (div_le_iff₀ (by positivity)).mpr
    linarith only [hscaled]
  exact objective_drop_floor_of_successful_between run (Nat.le_add_right _ _) le_rfl hs ha
    (by unfold curvatureExitRadius; positivity) hrad hτ hsecond

omit [NormedSpace ℝ E] in
/-- **Proofs of Theorems 6.6.8 and 13.12.6** of [conn2000trust], local forced-expansion argument.
Let $x_k \in E$ and $\Delta_k > 0$, let $S \subseteq \mathbb{N}$ (the accepted iterations), and
let $x_{k_i} \to z$ for a strictly increasing sequence $(k_i)$. Let $0 < \gamma < 1$,
$1 < \gamma_3 \le \gamma_4$, and $\Delta_c, K, r, \delta > 0$. The following cannot hold
together:

* for $k \notin S$, $x_{k+1} = x_k$ and $\Delta_{k+1} \le \gamma \Delta_k$;
* for $k \in S$, $\|x_{k+1} - x_k\| \le K \Delta_k$;
* for all large $k$ with $\|x_k - z\| < r$ and $\Delta_k \le \delta$, $k \in S$;
* for all large $k$ with $\|x_k - z\| < r$, $\Delta_k \le \delta$ and $\Delta_k \le \Delta_c$,
  $\gamma_3 \Delta_k \le \Delta_{k+1} \le \gamma_4 \Delta_k$;
* for every $\varepsilon > 0$, for all large $k$ with $\|x_k - z\| < r$ and $k \in S$,
  $\Delta_k < \varepsilon$.

So a neighborhood cannot force acceptance at small radii, force small radii on accepted trials,
and force geometric expansion of small radii at the same time.

**Reading.** Abstract forced-expansion argument with explicit local acceptability and curvature
premises.
-/
theorem false_of_local_radius_expansion {x : ℕ → E} {Δ : ℕ → ℝ} {S : Set ℕ}
    {z : E} {j : ℕ → ℕ} (hj : StrictMono j) (hz : Tendsto (x ∘ j) atTop (𝓝 z))
    {γ γ₃ γ₄ cap K r δ : ℝ} (hγ : 0 < γ) (hγ₁ : γ < 1)
    (hγ₃ : 1 < γ₃) (hγ₄ : γ₃ ≤ γ₄) (hcap : 0 < cap)
    (hK : 0 < K) (hr : 0 < r) (hδ : 0 < δ) (hΔ : ∀ k, 0 < Δ k)
    (hstay : ∀ k ∉ S, x (k + 1) = x k)
    (hshrink : ∀ k ∉ S, Δ (k + 1) ≤ γ * Δ k)
    (hstep : ∀ k ∈ S, dist (x (k + 1)) (x k) ≤ K * Δ k)
    (hvery : ∀ᶠ k in atTop, dist (x k) z < r → Δ k ≤ δ → k ∈ S)
    (hgrow : ∀ᶠ k in atTop, dist (x k) z < r → Δ k ≤ δ → Δ k ≤ cap →
      γ₃ * Δ k ≤ Δ (k + 1) ∧ Δ (k + 1) ≤ γ₄ * Δ k)
    (hsmall : ∀ ε > 0, ∀ᶠ k in atTop, dist (x k) z < r → k ∈ S → Δ k < ε) :
    False := by
  have hγ₄' : 0 < γ₄ := zero_lt_one.trans (hγ₃.trans_le hγ₄)
  let C := K / (γ₃ - 1)
  have hC : 0 < C := div_pos hK (sub_pos.mpr hγ₃)
  have hCK : C * (γ₃ - 1) = K := div_mul_cancel₀ _ (sub_pos.mpr hγ₃).ne'
  let ε := min cap (min (δ / γ₄) (r / (2 * (C + K))))
  have hε : 0 < ε := lt_min hcap (lt_min (div_pos hδ hγ₄') (div_pos hr (by positivity)))
  have hεcap : ε ≤ cap := min_le_left _ _
  have hεδ : γ₄ * ε ≤ δ := by
    have hh := (min_le_right cap _).trans (min_le_left (δ / γ₄) (r / (2 * (C + K))))
    rw [mul_comm]
    exact (le_div_iff₀ hγ₄').mp hh
  have hεr : (C + K) * ε ≤ r / 2 := by
    have hh := (min_le_right cap _).trans (min_le_right (δ / γ₄) (r / (2 * (C + K))))
    have he := (le_div_iff₀ (show 0 < 2 * (C + K) by positivity)).mp hh
    linarith only [he]
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hvery.and ((hsmall ε hε).and hgrow))
  obtain ⟨i, hi, hiz⟩ := ((hj.tendsto_atTop.eventually_ge_atTop N).and
    (hz.eventually (Metric.ball_mem_nhds z (half_pos hr)))).exists
  have hzi : dist (x (j i)) z < r / 2 := hiz
  have hex : ∃ n, j i + n ∈ S := by
    by_contra! hn
    have hx (n : ℕ) : x (j i + n) = x (j i) := by
      induction n with
      | zero => simp
      | succ n ih => exact (hstay _ (hn n)).trans ih
    have hp (n : ℕ) : Δ (j i + n) ≤ γ ^ n * Δ (j i) := by
      induction n with
      | zero => simp
      | succ n ih =>
        have hh := (hshrink _ (hn n)).trans (mul_le_mul_of_nonneg_left ih hγ.le)
        simpa only [pow_succ, mul_assoc, mul_left_comm, Nat.add_assoc] using hh
    have ht : Tendsto (fun n : ℕ => γ ^ n * Δ (j i)) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hγ.le hγ₁).mul_const (Δ (j i))
    obtain ⟨n, hnδ⟩ := (ht.eventually_lt_const hδ).exists
    apply hn n
    exact (hN _ (hi.trans (Nat.le_add_right _ _))).1 (by rw [hx]; linarith)
      ((hp n).trans hnδ.le)
  classical
  let n := Nat.find hex
  let k := j i + n
  have hk : j i ≤ k := Nat.le_add_right _ _
  have hks : k ∈ S := Nat.find_spec hex
  have hstay' (m : ℕ) (hm : m ≤ n) : x (j i + m) = x (j i) := by
    induction m with
    | zero => simp
    | succ m ih =>
      exact (hstay _ (Nat.find_min hex (by omega))).trans (ih (by omega))
  have hxk : x k = x (j i) := hstay' n le_rfl
  have hzk : dist (x k) z < r / 2 := by rwa [hxk]
  have hkN := hi.trans hk
  have hinv (n : ℕ) : k + n ∈ S ∧ Δ (k + n) < ε ∧
      dist (x (k + n)) z ≤ dist (x k) z + C * (Δ (k + n) - Δ k) ∧
      γ₃ ^ n * Δ k ≤ Δ (k + n) := by
    induction n with
    | zero =>
      simp only [sub_self, mul_zero, add_zero, pow_zero, one_mul]
      exact ⟨hks, (hN _ hkN).2.1 (by linarith) hks, le_rfl, le_rfl⟩
    | succ n ih =>
      obtain ⟨hs, hrad, hdist, hgeom⟩ := ih
      let m := k + n
      have hmn := hkN.trans (Nat.le_add_right k n)
      have hmn' := hmn.trans (Nat.le_succ m)
      have hd : dist (x m) z < r := by
        have hCε := mul_lt_mul_of_pos_left hrad hC
        have hKε : 0 ≤ K * ε := mul_nonneg hK.le hε.le
        have hbase : 0 ≤ C * Δ k := mul_nonneg hC.le (hΔ k).le
        linarith only [hdist, hCε, hKε, hbase, hεr, hzk]
      have hradδ : Δ m ≤ δ := hrad.le.trans ((le_mul_of_one_le_left hε.le
        (hγ₃.le.trans hγ₄)).trans hεδ)
      obtain ⟨hg, hg'⟩ := (hN _ hmn).2.2 hd hradδ (hrad.le.trans hεcap)
      have hstep' := hstep m hs
      have hdist' := dist_triangle (x (m + 1)) (x m) z
      have hmove : dist (x (m + 1)) z < r := by
        have hCe := mul_lt_mul_of_pos_left hrad hC
        have hKe := mul_lt_mul_of_pos_left hrad hK
        have hbase : 0 ≤ C * Δ k := mul_nonneg hC.le (hΔ k).le
        linarith only [hdist, hdist', hstep', hCe, hKe, hbase, hεr, hzk]
      have hrad' : Δ (m + 1) ≤ δ := hg'.trans
        ((mul_le_mul_of_nonneg_left hrad.le hγ₄'.le).trans hεδ)
      have hs' := (hN _ hmn').1 hmove hrad'
      rw [Nat.add_succ]
      refine ⟨hs', (hN _ hmn').2.1 hmove hs', ?_, ?_⟩
      · have hgrowth := mul_le_mul_of_nonneg_left hg hC.le
        linarith only [hdist, hdist', hstep', hgrowth,
          congrArg (fun a : ℝ ↦ a * Δ m) hCK]
      · rw [pow_succ, mul_comm (γ₃ ^ n), mul_assoc]
        exact (mul_le_mul_of_nonneg_left hgeom (zero_lt_one.trans hγ₃).le).trans hg
  have ht : Tendsto (fun n : ℕ ↦ γ₃ ^ n * Δ k) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt hγ₃).atTop_mul_const (hΔ k)
  obtain ⟨n, hn⟩ := (ht.eventually_ge_atTop ε).exists
  exact (hinv n).2.1.not_ge (hn.trans (hinv n).2.2.2)


/-- **Proofs of Theorems 6.6.8 and 8.1.5** of [conn2000trust], local curvature argument. Consider a
run of the basic trust-region algorithm for $f$ bounded below with forced radius expansion, with
$f(x_k) = m_k(x_k)$, $\|s_k\| \le K \Delta_k$ for all $k$ with $K > 0$, and small-radius model
agreement. Suppose that every iteration satisfies AA.2 with curvature $\tau_k$ and a constant
$\kappa > 0$, and let $x_{k_i} \to z$ for a strictly increasing sequence $(k_i)$. Then there are
no $a > 0$ and $r > 0$ such that $\tau_k \le -a$ for all large $k$ with $\|x_k - z\| < r$.

**Reading.** Uses abstract curvature and an explicit small-radius model error estimate.
-/
theorem not_negative_curvature_near_limit_of_forced_expansion (run : BTRRun f P sufficient) {z : E}
    {j : ℕ → ℕ} (hj : StrictMono j) (hz : Tendsto (run.x ∘ j) atTop (𝓝 z))
    {τ : ℕ → ℝ} {a κ K : ℝ} (ha : 0 < a) (hκ : 0 < κ) (hK : 0 < K)
    (hval : ∀ k, f (run.x k) = run.model k (run.x k))
    (hlower : BddBelow (range f)) (herr : smallRadiusModelAgreement run)
    (hstep : ∀ k, ‖run.s k‖ ≤ K * run.Δ k)
    (hsecond : ∀ k, HasNegativeCurvatureDecrease (run.model k) (run.x k) (run.s k)
      (τ k) (run.Δ k) κ)
    {γ₃ γ₄ cap : ℝ} (hexpand : HasForcedRadiusExpansion run γ₃ γ₄ cap)
    (hlocal : ∃ r > (0 : ℝ), ∀ᶠ k in atTop, dist (run.x k) z < r → τ k ≤ -a) :
    False := by
  obtain ⟨r, hr, hnear⟩ := hlocal
  obtain ⟨δ, hδ, hvery⟩ := eventually_small_radius_very_successful run hval herr hκ ha hsecond
  obtain ⟨hγ₃, hγ₄, hcap, hgrow⟩ := hexpand
  refine false_of_local_radius_expansion hj hz
    (P.gamma₁_pos.trans_le P.gamma₁_le_gamma₂) P.gamma₂_lt_one hγ₃ hγ₄ hcap hK hr hδ
    run.delta_pos (fun _ hk => run.iterate_eq_of_unsuccessful hk)
    (fun k hk => ((run.radius_update k).unsuccessful (lt_of_not_ge hk)).2)
    (fun k hk => (iterate_dist_le_of_successful run hk).trans (hstep k)) ?_ ?_ ?_
  · filter_upwards [hnear, hvery] with k hn hv hr hd
    exact run.verySuccessful_subset_successful (hv (hn hr) hd)
  · filter_upwards [hnear, hvery] with k hn hv hr hd hc
    exact hgrow k (hv (hn hr) hd) hc
  · intro ε hε
    filter_upwards [hnear, lemma_6_6_6_successful run hlower hκ ha hsecond ε hε] with k hn hs hr hk
    exact hs hk (hn hr)

/-- **Theorem 6.6.8** of [conn2000trust]. Consider a run of the basic trust-region algorithm for $f$
bounded below with continuous $Df$ and with forced radius expansion (AA.3). Suppose that
$f(x_k) = m_k(x_k)$ and $\|s_k\| \le K \Delta_k$ for all $k$ with $K > 0$, that the run has
small-radius model agreement, that $\|Df(x_k)\| \to 0$, and that every iteration satisfies AA.2
with curvature $\tau_k$ and a constant $\kappa > 0$. Let $x_{k_i} \to z$ for a strictly
increasing sequence $(k_i)$, and let $\lambda : E \to \mathbb{R}$ be continuous at $z$ with
$|\lambda(x_k) - \tau_k| \to 0$. Then
$$Df(z) = 0 \quad \text{and} \quad \lambda(z) \ge 0.$$

Near a limit with negative curvature, consecutive very successful trials have displacements
controlled by the growth of the radius, which gives a fixed decrease of the objective.

**Reading.** Uses abstract curvature, explicit error control, and explicit radius expansion.
-/
theorem theorem_6_6_8 (run : BTRRun f P sufficient) {z : E}
    {j : ℕ → ℕ} (hj : StrictMono j) (hz : Tendsto (run.x ∘ j) atTop (𝓝 z))
    {curv : E → ℝ} (hcurv : ContinuousAt curv z) {τ : ℕ → ℝ}
    (hagree : Tendsto (fun k ↦ |curv (run.x k) - τ k|) atTop (𝓝 0))
    (hgrad : Continuous (fderiv ℝ f))
    (hcrit : Tendsto (fun k ↦ ‖fderiv ℝ f (run.x k)‖) atTop (𝓝 0))
    (hval : ∀ k, f (run.x k) = run.model k (run.x k))
    (hlower : BddBelow (range f)) (herr : smallRadiusModelAgreement run)
    {κ K γ₃ γ₄ cap : ℝ} (hκ : 0 < κ) (hK : 0 < K) (hstep : ∀ k, ‖run.s k‖ ≤ K * run.Δ k)
    (hsecond : ∀ k, HasNegativeCurvatureDecrease (run.model k) (run.x k) (run.s k)
      (τ k) (run.Δ k) κ) (hexpand : HasForcedRadiusExpansion run γ₃ γ₄ cap) :
    fderiv ℝ f z = 0 ∧ 0 ≤ curv z := by
  refine ⟨stationary_of_subsequence run hj hz hgrad hcrit, ?_⟩
  by_contra! hneg
  let a := -curv z / 4
  have ha : 0 < a := div_pos (neg_pos.mpr hneg) (by norm_num)
  have haz : curv z < -(2 * a) := by dsimp [a]; linarith
  obtain ⟨r, hr, hnear⟩ := eventually_modelCurvature_negative_near run hcurv hagree ha haz
  exact not_negative_curvature_near_limit_of_forced_expansion run hj hz ha hκ hK hval hlower herr
    hstep hsecond hexpand ⟨r, hr, hnear⟩

/-- **Proof of Theorem 6.6.4** of [conn2000trust], small-radius model error from AM.6 and uniform
continuity of the objective Hessian. Consider a run of the basic trust-region algorithm for a
twice continuously differentiable $f$ with twice continuously differentiable models $m_k$.
Suppose that $f(x_k) = m_k(x_k)$ and $Df(x_k) = Dm_k(x_k)$ for all $k$, that
$\|Df(x_k)\| \to 0$, and that the models satisfy AM.5. Let $S$ contain every segment
$[x_k, x_k + s_k]$, and suppose that $D^2 f$ is uniformly continuous on $S$. Let $K, L > 0$ with
$\|s_k\| \le K \Delta_k$ and
$$\|D^2 m_k(z) - D^2 m_k(x_k)\| \le L \|z - x_k\| \quad \text{for all } z \in [x_k, x_k +
  s_k].$$
Then the run has small-radius model agreement.

**Reading.** Uniform objective and model Hessian variation plus center agreement suffice.
-/
theorem smallRadiusModelAgreement_of_uniformHessians (run : BTRRun f P sufficient)
    (hf : ContDiff ℝ 2 f) (hm : ∀ k, ContDiff ℝ 2 (run.model k))
    (hval : ∀ k, f (run.x k) = run.model k (run.x k))
    (hgrad : ∀ k, fderiv ℝ f (run.x k) = fderiv ℝ (run.model k) (run.x k))
    (hcrit : Tendsto (fun k ↦ ‖fderiv ℝ f (run.x k)‖) atTop (𝓝 0))
    (hagree : ModelHessianAgreement f run.model run.x)
    {S : Set E} (hS : ∀ k, segment ℝ (run.x k) (run.x k + run.s k) ⊆ S)
    (hunif : ∀ ε > (0 : ℝ), ∃ r > (0 : ℝ), ∀ x ∈ S, ∀ y ∈ S, ‖x - y‖ ≤ r →
      ‖fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) y‖ ≤ ε)
    {K L : ℝ} (hK : 0 < K) (hL : 0 < L) (hstep : ∀ k, ‖run.s k‖ ≤ K * run.Δ k)
    (hlip : ∀ k z, z ∈ segment ℝ (run.x k) (run.x k + run.s k) →
      ‖fderiv ℝ (fderiv ℝ (run.model k)) z -
        fderiv ℝ (fderiv ℝ (run.model k)) (run.x k)‖ ≤ L * ‖z - run.x k‖) :
    smallRadiusModelAgreement run := by
  apply smallRadiusModelAgreement_of_hessians run hf
    (fun k z _ ↦ (hm k).differentiable (by norm_num) z)
    (fun k z _ ↦ ((hm k).fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) z)
    hval hgrad hcrit hagree hK hstep
  intro ε hε
  obtain ⟨r, hr, hcont⟩ := hunif (ε / 2) (half_pos hε)
  let δ := min (r / K) (ε / (2 * L * K))
  have hδ : 0 < δ := lt_min (div_pos hr hK) (div_pos hε (by positivity))
  refine ⟨δ, hδ, fun k hk z hz ↦ ?_⟩
  have hdist : ‖z - run.x k‖ ≤ ‖run.s k‖ := by
    rw [segment_eq_image] at hz
    obtain ⟨t, ht, rfl⟩ := hz
    dsimp only
    rw [smul_add, ← add_assoc, ← add_smul, sub_add_cancel, one_smul, add_sub_cancel_left,
      norm_smul, Real.norm_of_nonneg ht.1]
    exact mul_le_of_le_one_left (norm_nonneg _) ht.2
  have hd := hdist.trans (hstep k)
  have hd' := hd.trans (mul_le_mul_of_nonneg_left hk hK.le)
  have hr' : K * δ ≤ r := by
    rw [mul_comm]
    exact (le_div_iff₀ hK).mp (min_le_left _ _)
  have hF := hcont z (hS k hz) (run.x k) (hS k (left_mem_segment ..))
    (hd'.trans hr')
  have hM := (hlip k z hz).trans (mul_le_mul_of_nonneg_left hd' hL.le)
  have hδ' := (le_div_iff₀ (show 0 < 2 * L * K by positivity)).mp
    (min_le_right (r / K) (ε / (2 * L * K)))
  linarith only [hF, hM, hδ',
    show δ * (2 * L * K) = 2 * (L * (K * δ)) by ring]

/-- **Equation (6.6.20)** of [conn2000trust], least Hessian curvature. For a continuous bilinear
form $H$ on $E$, such as a Hessian, the **least unit curvature** is
$$\inf_{\|u\| = 1} H(u, u).$$

In a finite-dimensional Euclidean space it is the least eigenvalue of the Hessian. Its value is
$0$ when $E = 0$, where the unit sphere is empty.

**Reading.** Infimum over the abstract normed sphere replaces the least Euclidean Hessian
eigenvalue.
-/
noncomputable def leastUnitCurvature (H : E →L[ℝ] E →L[ℝ] ℝ) : ℝ :=
  ⨅ u : Metric.sphere (0 : E) 1, H u u

private theorem abs_hessian_apply_unit_le (H : E →L[ℝ] E →L[ℝ] ℝ)
    (u : Metric.sphere (0 : E) 1) : |H u u| ≤ ‖H‖ := by
  have hu : ‖(u : E)‖ = 1 := norm_eq_of_mem_sphere u
  have h₁ := (H u).le_opNorm (u : E)
  have h₂ := H.le_opNorm (u : E)
  simpa only [hu, mul_one, Real.norm_eq_abs] using h₁.trans
    (mul_le_mul_of_nonneg_right h₂ (norm_nonneg _))

private theorem bddBelow_hessian_apply_unit (H : E →L[ℝ] E →L[ℝ] ℝ) :
    BddBelow (range (fun u : Metric.sphere (0 : E) 1 ↦ H u u)) :=
  ⟨-‖H‖, fun _ ⟨u, hu⟩ ↦ hu ▸ (neg_le_neg (abs_hessian_apply_unit_le H u)).trans (neg_abs_le _)⟩

/-- **Proof of Theorem 6.6.4** of [conn2000trust], spectral comparison from AM.5. Let $E$ be a
nontrivial real normed space and $H, M$ continuous bilinear forms on $E$. Then
$$\Bigl|\inf_{\|u\| = 1} H(u, u) - \inf_{\|u\| = 1} M(u, u)\Bigr| \le \|H - M\|.$$

**Reading.** Operator perturbation estimate for Rayleigh infima instead of least eigenvalues.
-/
theorem abs_sub_leastUnitCurvature_le [Nontrivial E] (H M : E →L[ℝ] E →L[ℝ] ℝ) :
    |leastUnitCurvature H - leastUnitCurvature M| ≤ ‖H - M‖ := by
  let : Nonempty (Metric.sphere (0 : E) 1) :=
    (NormedSpace.sphere_nonempty.mpr zero_le_one).coe_sort
  have hle (A B : E →L[ℝ] E →L[ℝ] ℝ) :
      leastUnitCurvature A - ‖A - B‖ ≤ leastUnitCurvature B := by
    apply le_ciInf
    intro u
    have hh := ciInf_le (bddBelow_hessian_apply_unit A) u
    have hu := (le_abs_self ((A - B) u u)).trans (abs_hessian_apply_unit_le (A - B) u)
    change (⨅ v : Metric.sphere (0 : E) 1, A v v) - ‖A - B‖ ≤ B u u
    simp only [sub_apply] at hu
    linarith only [hh, hu]
  rw [abs_sub_le_iff]
  exact ⟨by linarith only [hle H M], by linarith only [hle M H, norm_sub_rev M H]⟩

/-- **Proof of Theorem 6.6.5** of [conn2000trust], second-order criticality. Let $E$ be a nontrivial
real normed space and $H$ a continuous bilinear form on $E$. Then
$\inf_{\|u\| = 1} H(u, u) \ge 0$ if and only if $H(v, v) \ge 0$ for all $v \in E$.

**Reading.** Nonnegative infimum is equivalent to nonnegative Hessian quadratic form in an abstract
space.
-/
theorem leastUnitCurvature_nonneg_iff [Nontrivial E] (H : E →L[ℝ] E →L[ℝ] ℝ) :
    0 ≤ leastUnitCurvature H ↔ ∀ v : E, 0 ≤ H v v := by
  let : Nonempty (Metric.sphere (0 : E) 1) :=
    (NormedSpace.sphere_nonempty.mpr zero_le_one).coe_sort
  constructor
  · intro h v
    by_cases hv : v = 0
    · simp [hv]
    have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv
    let u : Metric.sphere (0 : E) 1 :=
      ⟨‖v‖⁻¹ • v, mem_sphere_zero_iff_norm.mpr (by
        rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hvn.le), inv_mul_cancel₀ hvn.ne'])⟩
    have hq : 0 ≤ H u u := h.trans (ciInf_le (bddBelow_hessian_apply_unit H) u)
    change 0 ≤ H (‖v‖⁻¹ • v) (‖v‖⁻¹ • v) at hq
    simp only [map_smul, smul_apply, smul_eq_mul] at hq
    have heq : ‖v‖ ^ 2 * (‖v‖⁻¹ * (‖v‖⁻¹ * H v v)) = H v v := by field_simp
    rw [← heq]
    positivity
  · intro h
    exact le_ciInf fun u ↦ h u

/-- **Proofs of Theorems 6.6.5 and 10.3.1** of [conn2000trust], continuity of the curvature. On a
nontrivial real normed space $E$, the least unit curvature $H \mapsto \inf_{\|u\| = 1} H(u, u)$
is continuous for the operator norm on continuous bilinear forms.

**Reading.** Continuity of the Rayleigh infimum on any nontrivial real normed space.
-/
theorem continuous_leastUnitCurvature [Nontrivial E] :
    Continuous (leastUnitCurvature (E := E)) := by
  have h : LipschitzWith 1 (leastUnitCurvature (E := E)) := by
    apply LipschitzWith.of_dist_le_mul
    intro H M
    rw [NNReal.coe_one, one_mul, Real.dist_eq, dist_eq_norm]
    exact abs_sub_leastUnitCurvature_le H M
  exact h.continuous

/-- **Theorems 6.6.4 and 6.6.5** of [conn2000trust], for the objective and model Hessians. Let $E$
be a nontrivial real normed space, and consider a run of the basic trust-region algorithm for a
twice continuously differentiable $f$ bounded below, with iterates in a compact set $K$. Suppose
that $\|Df(x_k)\| \to 0$, that $f(x_k) = m_k(x_k)$ for all $k$, that the run has small-radius
model agreement, and that the models satisfy AM.5. Let $\kappa > 0$, and suppose that every
iteration satisfies AA.2 with the model curvature $\tau_k = \inf_{\|u\| = 1} D^2 m_k(x_k)(u, u)$
and constant $\kappa$. Then there are $z \in K$ and a strictly increasing sequence $(k_i)$ with
$x_{k_i} \to z$,
$$Df(z) = 0 \quad \text{and} \quad D^2 f(z)(v, v) \ge 0 \text{ for all } v \in E.$$

AM.5 controls the difference of the least curvatures by
`ConnGouldToint.Chapter06.abs_sub_leastUnitCurvature_le`.

**Reading.** Abstract Hessian specialization uses a small-radius error hypothesis and curvature
infima.
-/
theorem theorem_6_6_5_of_hessians [Nontrivial E] (run : BTRRun f P sufficient)
    {K : Set E} (hK : IsCompact K) (hx : ∀ k, run.x k ∈ K) (hf : ContDiff ℝ 2 f)
    (hcrit : Tendsto (fun k ↦ ‖fderiv ℝ f (run.x k)‖) atTop (𝓝 0))
    (hval : ∀ k, f (run.x k) = run.model k (run.x k))
    (hlower : BddBelow (range f)) (herr : smallRadiusModelAgreement run)
    (hagree : ModelHessianAgreement f run.model run.x) {κ : ℝ} (hκ : 0 < κ)
    (hsecond : ∀ k, HasNegativeCurvatureDecrease (run.model k) (run.x k) (run.s k)
      (leastUnitCurvature (fderiv ℝ (fderiv ℝ (run.model k)) (run.x k))) (run.Δ k) κ) :
    ∃ z ∈ K, ∃ j : ℕ → ℕ, StrictMono j ∧ Tendsto (run.x ∘ j) atTop (𝓝 z) ∧
      fderiv ℝ f z = 0 ∧ ∀ v, 0 ≤ fderiv ℝ (fderiv ℝ f) z v v := by
  let curv (z : E) := leastUnitCurvature (fderiv ℝ (fderiv ℝ f) z)
  let τ (k : ℕ) := leastUnitCurvature (fderiv ℝ (fderiv ℝ (run.model k)) (run.x k))
  have hdf : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hc : Continuous curv :=
    continuous_leastUnitCurvature.comp (hdf.continuous_fderiv (by norm_num))
  have ha : Tendsto (fun k ↦ |curv (run.x k) - τ k|) atTop (𝓝 0) :=
    squeeze_zero (fun _ ↦ abs_nonneg _) (fun _ ↦ abs_sub_leastUnitCurvature_le _ _) (hagree hcrit)
  obtain ⟨z, hz, j, hj, hjz, hg, hH⟩ := theorem_6_6_5 run hc hK hx
    (hf.continuous_fderiv (by norm_num)) hcrit
    (theorem_6_6_4 run hκ hval hlower herr ha hsecond)
  exact ⟨z, hz, j, hj, hjz, hg, (leastUnitCurvature_nonneg_iff _).mp hH⟩

end ConnGouldToint.Chapter06
