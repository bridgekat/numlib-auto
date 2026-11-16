/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.ConnGouldToint.Chapter06.Section06
import NumlibSurface.ConnGouldToint.Chapter13.Section02

/-!
# Conn, Gould and Toint, Section 13.3: Constrained Cauchy and eigenpoints

This module formalizes the second primal barrier inner algorithm of Section 13.3 of [conn2000trust]
and the model decrease at its constrained Cauchy point and constrained eigenpoint. At an interior
iterate $x$ with boundary distance $d = \operatorname{dist}(x, \partial C)$, the trust-region radius
$\Delta$ is reduced to $\hat\Delta = \min\{\Delta, (1 - \sigma) d\}$, so that every step of length
at most $\hat\Delta$ passes the fraction-to-boundary test with fraction $\sigma$. The Cauchy and
eigenpoint arguments of Chapter 6 then apply with $\hat\Delta$ in place of $\Delta$. The proofs
specialize `ConnGouldToint.Chapter06.theorem_6_3_1` and use the boundary separation of Theorem
13.2.1, `ConnGouldToint.Chapter13.PrimalBarrierInnerRun.boundary_separation`.

## Main definitions

* Equation (13.3.2), `ConnGouldToint.Chapter13.HasConstrainedBarrierDecrease`: the first- and
  second-order model decrease test with the reduced radius $\hat\Delta$.
* Algorithm 13.3.1, `ConnGouldToint.Chapter13.SecondPrimalBarrierInnerRun`: a run of the inner
  algorithm whose trials pass the fraction-to-boundary test and satisfy (13.3.2).
* Equations (13.3.3) and (13.3.20), `ConnGouldToint.Chapter13.constrainedBarrierRadius`: the reduced
  radius $\hat\Delta = \min\{\Delta, (1 - \sigma) d\}$.
* Equations (13.3.5)–(13.3.6), `ConnGouldToint.Chapter13.IsConstrainedBarrierCauchyStep`: the
  constrained Cauchy step minimizes the model along $-g$ within the reduced radius.
* Equation (13.3.20), `ConnGouldToint.Chapter13.IsConstrainedBarrierEigenstep`: the constrained
  eigenstep minimizes the model on the segment from $0$ to a negative-curvature direction $u$.

## Main results

* Theorem 13.3.1, `ConnGouldToint.Chapter13.theorem_13_3_1`: the constrained Cauchy step of a
  quadratic model decreases it by at least $\frac12 \|g\| \min\{\|g\| / (1 + \|H\|), \hat\Delta\}$.
* Corollary 13.3.2, `ConnGouldToint.Chapter13.corollary_13_3_2`: along a run of Algorithm 13.3.1,
  the constrained Cauchy decrease is bounded below uniformly in terms of the truncated gradient
  measure $\min\{\|g_j\|, (1 - \sigma) \kappa_{\rm mdb}\}$.
* Theorem 13.3.3, `ConnGouldToint.Chapter13.theorem_13_3_3`: the constrained eigenstep decreases a
  quadratic model by at least $-\frac12 \kappa \tau \hat\Delta^2$.

## Implementation notes

* The trust region and the distance to the boundary are measured in the same norm, the norm of the
  inner product space $E$.

## Deviations from the source

* **Corollary 13.3.2** (correction). The corollary uses the corrected hypothesis of Theorem 13.2.1:
  the objective is bounded below along the iterates. See
  `ConnGouldToint.Chapter13.corollary_13_3_2`.
-/

open Filter Metric Set
open scoped Topology

namespace ConnGouldToint.Chapter13

open Chapter06

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Equations (13.3.3) and (13.3.20)** of [conn2000trust]. For a trust-region radius $\Delta$, a
fraction $\sigma$ and a boundary distance $d$, the **reduced radius** is
$$\hat\Delta = \min\{\Delta, (1 - \sigma) d\}.$$

It is the radius of the arcs in (13.3.3) and (13.3.20). The trust region and the boundary
distance are measured in the same norm. -/
def constrainedBarrierRadius (Δ σ d : ℝ) : ℝ := min Δ ((1 - σ) * d)

/-- **Equations (13.3.5)–(13.3.6)** of [conn2000trust]. Let $m$ be a model, written as a function of
the displacement $s$ from the current iterate, and let $g$ be its gradient. A displacement $s$
is a **constrained Cauchy step** if it minimizes $m$ over the arc
$$\{-t g : t \ge 0,\ \|t g\| \le \min\{\Delta, (1 - \sigma) d\}\}$$
and lies on this arc.

This is `ConnGouldToint.Chapter06.IsCauchyPoint` for the norm of $E$ and the radius
`ConnGouldToint.Chapter13.constrainedBarrierRadius`. -/
def IsConstrainedBarrierCauchyStep (m : E → ℝ) (g : E) (Δ σ d : ℝ) (s : E) : Prop :=
  IsCauchyPoint m (normSeminorm ℝ E) g (constrainedBarrierRadius Δ σ d) s

/-- **Equation (13.3.2)** of [conn2000trust]. A step $s$ from $x$ satisfies the **constrained
barrier decrease test** for the model $m$, the gradient $g$, the curvature bound $\beta$, the
least-curvature measure $\tau$ and the constant $\kappa$ if
$$m(x) - m(x + s) \ge \kappa \max\left\{\|g\| \min\left\{\frac{\|g\|}{\beta},
  \hat\Delta\right\},\ -\tau \min\{\tau^2, \hat\Delta^2\}\right\},$$
where $\hat\Delta = \min\{\Delta, (1 - \sigma) d\}$ is the reduced radius for the radius
$\Delta$, the fraction $\sigma$ and the boundary distance $d$. -/
def HasConstrainedBarrierDecrease (m : E → ℝ) (x s g : E) (β Δ σ d τ κ : ℝ) : Prop :=
  κ * max (‖g‖ * min (‖g‖ / β) (constrainedBarrierRadius Δ σ d))
    (-τ * min (τ ^ 2) (constrainedBarrierRadius Δ σ d ^ 2)) ≤ m x - m (x + s)

/-- **Algorithm 13.3.1** of [conn2000trust]. Let $E$ be a real Hilbert space, let $C \subseteq E$,
let $\sigma \in (0, 1)$, and let $\varphi : E \to \mathbb{R}$ be the barrier objective. A **run
of Algorithm 13.3.1** for a fixed barrier parameter is a run of Algorithm 13.2.1
(`ConnGouldToint.Chapter13.PrimalBarrierInnerRun`) together with the following data and
conditions for each iteration $j$:
* the model splits as $m_j = m^f_j + m^b_j$ into an objective model and a barrier model;
* $g_j = \nabla m_j(x_j)$, $\beta_j = 1 + \sup\{\|\nabla^2 m_j(y)\| : \|y - x_j\| \le
  \Delta_j\}$ and $\tau_j = \min\{0, \inf_{\|v\| = 1} \nabla^2 m_j(x_j)[v, v]\}$;
* the trial point $x_j + s_j$ passes the interior and fraction-to-boundary test (13.3.1);
* the step satisfies the decrease test (13.3.2) with $d = \operatorname{dist}(x_j, \partial C)$
  and a fixed constant $\kappa > 0$.

Since every trial passes the fraction-to-boundary test, the ratio and the radius rules agree
with those of Algorithm 13.2.1. The supremum and the infimum are `sSup` and `sInf` on
$\mathbb{R}$, so they are $0$ for an unbounded or an empty set. -/
structure SecondPrimalBarrierInnerRun [CompleteSpace E] (P : BTRParams) (C : Set E) (σ : ℝ) (φ : E → ℝ)
    extends PrimalBarrierInnerRun P C σ φ where
  /-- The fraction $\sigma$ of the fraction-to-boundary test lies in $(0, 1)$. -/
  fraction : σ ∈ Ioo (0 : ℝ) 1
  /-- The objective models $m^f_j$. -/
  objectiveModel : ℕ → E → ℝ
  /-- The barrier models $m^b_j$. -/
  barrierModel : ℕ → E → ℝ
  /-- The model of the barrier objective is the sum $m_j = m^f_j + m^b_j$. -/
  model_split : ∀ j, model j = objectiveModel j + barrierModel j
  /-- The model gradients $g_j$. -/
  g : ℕ → E
  /-- The model curvature bounds $\beta_j$. -/
  β : ℕ → ℝ
  /-- The nonpositive least-curvature measures $\tau_j$. -/
  τ : ℕ → ℝ
  /-- The constant $\kappa$ of the decrease test (13.3.2). -/
  κ : ℝ
  /-- The constant $\kappa$ is positive. -/
  decrease_constant : 0 < κ
  /-- The vector $g_j$ is the gradient of $m_j$ at $x_j$. -/
  gradient_model : ∀ j, g j = gradient (model j) (x j)
  /-- The curvature bound is $\beta_j = 1 + \sup\{\|\nabla^2 m_j(y)\| : \|y - x_j\| \le \Delta_j\}$.
  -/
  curvature_model : ∀ j, β j = 1 + sSup
    ((fun y ↦ ‖fderiv ℝ (fderiv ℝ (model j)) y‖) '' closedBall (x j) (Δ j))
  /-- The least-curvature measure is $\tau_j = \min\{0, \inf_{\|v\| = 1} \nabla^2 m_j(x_j)[v, v]\}$.
  -/
  nonpositive_least_curvature : ∀ j, τ j = min 0
    (sInf ((fun v ↦ fderiv ℝ (fderiv ℝ (model j)) (x j) v v) '' sphere 0 1))
  /-- The trial point $x_j + s_j$ passes the interior and fraction-to-boundary test (13.3.1). -/
  trial_admissible : ∀ j, BarrierAdmissibleTrial C σ (x j) (x j + s j)
  /-- The step $s_j$ satisfies the decrease test (13.3.2) with the boundary distance
  $\operatorname{dist}(x_j, \partial C)$. -/
  sufficient_decrease : ∀ j,
    HasConstrainedBarrierDecrease (model j) (x j) (s j) (g j) (β j) (Δ j) σ
      (infDist (x j) (frontier C)) (τ j) κ

/-- **Theorem 13.3.1** of [conn2000trust]. Let $E$ be a real inner product space, let
$c \in \mathbb{R}$, $g \in E$, and let $H$ be a continuous linear operator on $E$. Consider the
quadratic model $m(s) = c + \langle g, s\rangle + \frac12 \langle s, H s\rangle$. Let
$\Delta \ge 0$, $\sigma \le 1$ and $d \ge 0$, and let $s$ be a constrained Cauchy step of $m$
with the reduced radius $\hat\Delta = \min\{\Delta, (1 - \sigma) d\}$. Then
$$c - m(s) \ge \frac12 \|g\| \min\left\{\frac{\|g\|}{1 + \|H\|}, \hat\Delta\right\}.$$

The constrained Cauchy decrease is the ordinary Cauchy decrease of a quadratic model with the
reduced radius. The number $1 + \|H\|$ is `ConnGouldToint.Chapter06.quadraticCurvatureBound`,
and the proof specializes `ConnGouldToint.Chapter06.theorem_6_3_1`. -/
theorem theorem_13_3_1 (c : ℝ) (g : E) (H : E →L[ℝ] E) {Δ σ d : ℝ}
    (hΔ : 0 ≤ Δ) (hσ : σ ≤ 1) (hd : 0 ≤ d) {s : E}
    (hs : IsConstrainedBarrierCauchyStep (quadraticModel c g H.toLinearMap) g Δ σ d s) :
    (1 / 2) * ‖g‖ * min (‖g‖ / quadraticCurvatureBound H) (constrainedBarrierRadius Δ σ d) ≤
      c - quadraticModel c g H.toLinearMap s := by
  by_cases hg : g = 0
  · obtain ⟨t, _, rfl, _⟩ := hs.2
    simp [hg, quadraticModel]
  have h := theorem_6_3_1 c g H (normSeminorm ℝ E)
    (fun _ hv ↦ norm_eq_zero.mp hv)
    (le_min hΔ (mul_nonneg (sub_nonneg.mpr hσ) hd)) hs
  simpa [constrainedBarrierRadius, cauchyNormRatio, norm_ne_zero_iff.mpr hg] using h

/-- **Corollary 13.3.2** of [conn2000trust]. Let $E$ be a real Hilbert space, let $C \subseteq E$,
and consider a run of Algorithm 13.3.1 for the barrier objective $f + b$ with fraction $\sigma$,
iterates $x_j$, radii $\Delta_j$, models $m_j$ and model gradients $g_j$. Assume that
$f(x_j) \ge L$ for all $j$, that $b$ satisfies AC.8, and that each model is quadratic,
$m_j(x_j + v) = m_j(x_j) + \langle g_j, v\rangle + \frac12 \langle v, H_j v\rangle$ with a
continuous linear operator $H_j$. Let $s^C_j$ be a constrained Cauchy step of
$v \mapsto m_j(x_j + v)$ with the boundary distance $\operatorname{dist}(x_j, \partial C)$. Then
there are constants $\kappa_{\rm mdc} > 0$ and $\kappa_{\rm mdb} > 0$ such that, for all $j$,
$\operatorname{dist}(x_j, \partial C) \ge \kappa_{\rm mdb}$ and, with $\pi_j = \min\{\|g_j\|,
(1 - \sigma) \kappa_{\rm mdb}\}$,
$$m_j(x_j) - m_j(x_j + s^C_j) \ge \kappa_{\rm mdc} \pi_j \min\left\{\frac{\pi_j}{1 + \|H_j\|},
  \Delta_j\right\}.$$

**Correction.** The statement carries the corrected hypothesis of Theorem 13.2.1, the lower
bound $f(x_j) \ge L$ on the objective along the run. This bound gives the clearance
$\kappa_{\rm mdb}$ of (13.3.19); see `ConnGouldToint.Chapter13.theorem_13_2_1`.

The truncated gradient measure $\pi_j$ thus satisfies the decrease bound of AA.1b. AC.8 is
`ConnGouldToint.Chapter13.BarrierDivergesAtBoundary`. The proof takes $\kappa_{\rm mdc} = 1/2$
and combines `ConnGouldToint.Chapter13.PrimalBarrierInnerRun.boundary_separation` with
`ConnGouldToint.Chapter13.theorem_13_3_1`. -/
theorem corollary_13_3_2 [CompleteSpace E] {P : BTRParams} {C : Set E} {σ : ℝ} {f b : E → ℝ}
    (r : SecondPrimalBarrierInnerRun P C σ (f + b)) {L : ℝ} (hf : ∀ j, L ≤ f (r.x j))
    (hb : BarrierDivergesAtBoundary C b) (H : ℕ → E →L[ℝ] E)
    (hm : ∀ j v, r.model j (r.x j + v) =
      quadraticModel (r.model j (r.x j)) (r.g j) (H j).toLinearMap v)
    (sC : ℕ → E)
    (hs : ∀ j, IsConstrainedBarrierCauchyStep (fun v ↦ r.model j (r.x j + v)) (r.g j)
      (r.Δ j) σ (infDist (r.x j) (frontier C)) (sC j)) :
    ∃ κmdc > 0, ∃ κmdb > 0, ∀ j, κmdb ≤ infDist (r.x j) (frontier C) ∧
      let π := min ‖r.g j‖ ((1 - σ) * κmdb)
      κmdc * π * min (π / quadraticCurvatureBound (H j)) (r.Δ j) ≤
        r.model j (r.x j) - r.model j (r.x j + sC j) := by
  obtain ⟨ε, hε, hdist⟩ := r.toPrimalBarrierInnerRun.boundary_separation hf hb
  refine ⟨1 / 2, by norm_num, ε, hε.1, fun j ↦ ⟨hdist j, ?_⟩⟩
  dsimp only
  let π := min ‖r.g j‖ ((1 - σ) * ε)
  let β := quadraticCurvatureBound (H j)
  have hβ : 1 ≤ β := by unfold β quadraticCurvatureBound; linarith [norm_nonneg (H j)]
  have hβ' : 0 < β := zero_lt_one.trans_le hβ
  have hΔ := (norm_nonneg _).trans (r.step_feasible j)
  have hπ : 0 ≤ π := le_min (norm_nonneg _) (by positivity [r.fraction.2, hε.1])
  have hbound : π / β ≤ (1 - σ) * infDist (r.x j) (frontier C) := calc
    π / β ≤ π := (div_le_self hπ hβ)
    _ ≤ (1 - σ) * ε := min_le_right _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (hdist j) (sub_nonneg.mpr r.fraction.2.le)
  have hmin : min (π / β) (r.Δ j) ≤
      min (‖r.g j‖ / β) (constrainedBarrierRadius (r.Δ j) σ (infDist (r.x j) (frontier C))) := by
    exact le_min ((min_le_left _ _).trans (div_le_div_of_nonneg_right (min_le_left _ _) hβ'.le))
      (le_min (min_le_right _ _) ((min_le_left _ _).trans hbound))
  have hmodel : (fun v ↦ r.model j (r.x j + v)) =
      quadraticModel (r.model j (r.x j)) (r.g j) (H j).toLinearMap := funext (hm j)
  have hsj := hs j
  rw [hmodel] at hsj
  have hc := theorem_13_3_1 (r.model j (r.x j)) (r.g j) (H j) hΔ r.fraction.2.le
    infDist_nonneg hsj
  rw [← hm] at hc
  exact (mul_le_mul (mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num)) hmin
    (le_min (div_nonneg hπ hβ'.le) hΔ) (by positivity)).trans hc

/-- **Equation (13.3.20)** of [conn2000trust], constrained eigenpoint. Let $m$ be a model written as
a function of the displacement, and let $u \in E$ be a direction. A displacement $s$ is a
**constrained eigenstep** if it minimizes $m$ over the segment $\{t u : t \in [0, 1]\}$ and lies
on this segment. -/
def IsConstrainedBarrierEigenstep (m : E → ℝ) (u s : E) : Prop :=
  IsMinOn m ((fun t : ℝ ↦ t • u) '' Icc 0 1) s ∧ s ∈ (fun t : ℝ ↦ t • u) '' Icc 0 1

/-- **Theorem 13.3.3** of [conn2000trust]. Let $E$ be a real inner product space, let
$c \in \mathbb{R}$, $g, u \in E$, and let $H$ be a linear operator on $E$. Consider the
quadratic model $m(s) = c + \langle g, s\rangle + \frac12 \langle s, H s\rangle$ and the reduced
radius $\hat\Delta = \min\{\Delta, (1 - \sigma) d\}$. Let $\kappa \in (0, 1]$ and $\tau < 0$.
Assume that
$$\langle u, g\rangle \le 0, \qquad \|u\| = \hat\Delta, \qquad \langle u, H u\rangle \le \kappa
  \tau \hat\Delta^2,$$
and let $s$ be a constrained eigenstep of $m$ along $u$. Then
$$c - m(s) \ge -\frac12 \kappa \tau \hat\Delta^2.$$

The three conditions on $u$ are the conditions in (13.3.20) and the inequality that follows it.
The decrease at the constrained eigenpoint dominates the decrease at the end $u$ of the
negative-curvature segment. -/
theorem theorem_13_3_3 (c : ℝ) (g u : E) (H : E →ₗ[ℝ] E) {Δ σ d κ τ : ℝ}
    (_hκ : κ ∈ Ioc (0 : ℝ) 1) (_hτ : τ < 0)
    (hg : inner ℝ u g ≤ 0) (_hu : ‖u‖ = constrainedBarrierRadius Δ σ d)
    (hh : inner ℝ u (H u) ≤ κ * τ * constrainedBarrierRadius Δ σ d ^ 2)
    {s : E} (hs : IsConstrainedBarrierEigenstep (quadraticModel c g H) u s) :
    -(1 / 2 : ℝ) * κ * τ * constrainedBarrierRadius Δ σ d ^ 2 ≤ c - quadraticModel c g H s := by
  have hmin : quadraticModel c g H s ≤ quadraticModel c g H u :=
    isMinOn_iff.mp hs.1 _ ⟨1, ⟨zero_le_one, le_rfl⟩, one_smul ℝ u⟩
  rw [real_inner_comm] at hg
  simp only [quadraticModel] at hmin ⊢
  linarith

end ConnGouldToint.Chapter13
