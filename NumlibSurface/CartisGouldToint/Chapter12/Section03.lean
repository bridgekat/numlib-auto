/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.CartisGouldToint.Chapter12.Section02

/-!
# Cartis, Gould and Toint, Section 12.3: Inexact global minimization in the ARqp algorithm

This module formalizes Section 12.3 of [cartis2022evaluation], which has no numbered results,
together with the relaxed Step 2 that the Notes to Section 12.2.2 propose. Step 2 of the algorithm
ARqp (Algorithm 12.2.2) must give a sufficient decrease of the Taylor model at the successful
iterations. Section 12.3 observes that a step can be accepted, with the model decrease (12.2.27),
without the check (12.2.29) of approximate model optimality, as soon as it achieves the sufficient
decrease $\Delta T_{f,p}(x_k, s_k) \ge \kappa_{\mathrm{decr}} \varepsilon_{\min}^{\omega}$ (12.3.1),
or is long, $\|s_k\| \ge \kappa_{\mathrm{decr}}^{1/(p+1)} \varepsilon_{\min}^{\omega/(p+1)}$
(12.3.2). For a long step, the sufficient decrease follows from Lemma 4.1.1. The Notes to Section
12.2.2 propose the same relaxation for long steps and state that "this modification does not affect
the conclusions of the complexity theorem".

This module makes that claim precise. ARqp with the relaxed Step 2 is a run predicate, and every
ARqp run is such a run. For every $\omega \ge \pi_q$, the bounds of Theorem 12.2.14 hold for these
runs, with $\kappa_{\Delta m}$ replaced by $\min(\kappa_{\Delta m}, \kappa_{\mathrm{decr}},
\sigma_{\min} \kappa_{\mathrm{decr}}/(p+1)!)$ and $\min_j \varepsilon_j^{\pi_j}$ replaced by
$\varepsilon_{\min}^{\omega}$. The proofs specialize the analysis of
`Numlib.Optimization.ModelBased.HighOrder.ARqpComplexity` and the results of
`NumlibSurface.CartisGouldToint.Chapter12.Section02`.

## Main definitions

* Section 12.3, (12.3.1)–(12.3.2), `CartisGouldToint.Chapter12.ARqpRelaxedStep`: the relaxed Step 2,
  which accepts a step with the Step-2 conditions of ARqp, or with the sufficient decrease (12.3.1),
  or a long step (12.3.2).
* Section 12.3, `CartisGouldToint.Chapter12.IsARqpSufficientDecreaseRun`: a run of ARqp with the
  relaxed Step 2.

## Main results

* Section 12.3, `CartisGouldToint.Chapter12.IsARqpSufficientDecreaseRun.of_algorithm_12_2_2`: every
  ARqp run is a run with the relaxed Step 2.
* Notes to Section 12.2.2, `CartisGouldToint.Chapter12.complexity_arqpSufficientDecrease`: the
  evaluation complexity bounds of Theorem 12.2.14 hold for ARqp with the relaxed Step 2, with
  $\varepsilon_{\min}^{\omega}$ for every $\omega \ge \pi_q$.

## Conventions

* $\varepsilon_{\min} = \min(1, \min_{j \in [1:q]} \varepsilon_j)$ is `Optimization.finMin 1 ε q`.
  For $\varepsilon \in (0, 1]^q$ it is $\min_j \varepsilon_j$, as in (12.2.7).
* The other notation is that of `NumlibSurface.CartisGouldToint.Chapter12.Section02`.

## Deviations from the source

* **(12.3.1)** (reading). The source prints $\Delta T_{f,j}(x_k, s_k) \ge \kappa_{\mathrm{decr}}
  \varepsilon_j^{\omega}$ "for some $j$". The library reads it with the decrease
  $\Delta T_{f,p}(x_k, s_k)$ that the ratio and the complexity analysis use, and with
  $\varepsilon_{\min}^{\omega}$ as in (12.3.2). See `CartisGouldToint.Chapter12.ARqpRelaxedStep`.
* **Complexity of the relaxed method** (reading). The source takes $\omega = \pi_q$ and says only
  that the conclusions of Theorem 12.2.14 are not affected. The library states the bounds for every
  $\omega \ge \pi_q$, in terms of $\varepsilon_{\min}^{\omega}$ instead of
  $\min_j \varepsilon_j^{\pi_j}$. See
  `CartisGouldToint.Chapter12.complexity_arqpSufficientDecrease`.

## Not formalized

* The qualitative discussion of the premature termination of Algorithm 12.2.3 and of the
  practicality of global polynomial minimization.
-/

open Set Metric Filter Optimization
open scoped Nat

namespace CartisGouldToint.Chapter12

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Section 12.3** of [cartis2022evaluation], the relaxed Step 2 of ARqp. Let $M$ be the model
data of one ARqp iteration at the iterate $x$, with the model $m$ and the predicted decrease
$\Delta T_{f,p}(x, \cdot)$. Let $\kappa_{\mathrm{decr}}, \omega \in \mathbb{R}$ and
$\varepsilon_{\min} = \min(1, \min_{j \in [1:q]} \varepsilon_j)$. A step $s$ with radii
$\delta_{s,j}$ and displacements $d^m_j$ satisfies the **relaxed Step 2** if it satisfies the
Step-2 conditions of ARqp (`Optimization.ARqpStep` with no constraints), or if all of the
following hold: $m(s) \le m(0)$; $m(s) = m(0)$ only if $0$ is a global minimizer of $m$;
$\delta_{s,j} \in (0, 1]$ for $j \in [1:q]$; and
$$\Delta T_{f,p}(x, s) \ge \kappa_{\mathrm{decr}} \varepsilon_{\min}^{\omega} \quad
  \text{(12.3.1)} \qquad \text{or} \qquad \|s\| \ge \kappa_{\mathrm{decr}}^{1/(p+1)}
  \varepsilon_{\min}^{\omega/(p+1)} \quad \text{(12.3.2)}.$$

**Reading.** The source prints (12.3.1) as $\Delta T_{f,j}(x_k, s_k) \ge \kappa_{\mathrm{decr}}
\varepsilon_j^{\omega}$ "for some $j$". Here it is read with the decrease
$\Delta T_{f,p}(x_k, s_k)$ that the ratio (12.2.30) and the complexity analysis use, and with
$\varepsilon_{\min}^{\omega}$ as in (12.3.2).

The predicted decrease is the field `Optimization.ARqpData.pred`, which is
$\Delta T_{f,p}(x, \cdot)$ for the exact model data `Optimization.ARqpData.ofTaylor`. The
condition that $m(s) = m(0)$ only at a global model minimizer $0$ is the normalization of Step 2
in `Optimization.IsARqpRun`. -/
def ARqpRelaxedStep (P : ARqpParams) (p q : ℕ) (ε : ℕ → ℝ) (κdecr ω : ℝ) (M : ARqpData E)
    (x s : E) (δs : ℕ → ℝ) (dm : ℕ → E) : Prop :=
  ARqpStep univ P q ε M x s δs dm ∨
    (M.model s ≤ M.model 0 ∧ (M.model s = M.model 0 → IsMinOn M.model univ 0) ∧
      (∀ j ∈ Finset.Icc 1 q, 0 < δs j ∧ δs j ≤ 1) ∧
      (κdecr * finMin 1 ε q ^ ω ≤ M.pred s ∨
        κdecr ^ (1 / ((p + 1 : ℕ) : ℝ)) * finMin 1 ε q ^ (ω / ((p + 1 : ℕ) : ℝ)) ≤ ‖s‖))

/-- **Section 12.3** of [cartis2022evaluation], ARqp with the relaxed Step 2. A run of ARqp with the
relaxed Step 2 for $f$, constants $P$, model degree $p$, order $q$, tolerances $\varepsilon$,
initial radii $\delta_0$ and constants $\kappa_{\mathrm{decr}}$, $\omega$ consists of iterates
$x_k$, steps $s_k$, weights $\sigma_k$, Step-1 radii $\delta_{k,j}$ and displacements $d_{k,j}$,
and Step-2 radii $\delta_{s_k,j}$ and displacements $d^m_{k,j}$. It obeys the rules of Algorithm
12.2.2 (`CartisGouldToint.Chapter12.algorithm_12_2_2`), with Step 2 replaced by the relaxed Step
2 `CartisGouldToint.Chapter12.ARqpRelaxedStep`: Steps 2–4 form an adaptive-regularization run
that stops when the Step-1 test passes or $m_k(s_k) = m_k(0)$; the initial radii are $\delta_0$;
at every iteration reached, $d_{k,j}$ is a $\varsigma$-approximate optimality displacement of
radius $\delta_{k,j}$ for $j \in [1:q]$; and before termination, a successful iteration sets
$\delta_{k+1} = \delta_{s_k}$, while an unsuccessful iteration keeps $\delta_{k+1} = \delta_k$
and $d_{k+1} = d_k$.

The structure has the fields of `Optimization.IsARqpRun` with $X = E$, except that the Step-2
condition is the relaxed one. -/
structure IsARqpSufficientDecreaseRun (f : E → ℝ) (P : ARqpParams) (p q : ℕ) (ε δ₀ : ℕ → ℝ)
    (κdecr ω : ℝ) (x s : ℕ → E) (σ : ℕ → ℝ) (δ δs : ℕ → ℕ → ℝ) (d dm : ℕ → ℕ → E) : Prop where
  /-- Steps 2–4 form an adaptive-regularization run with the Step-1 test, the relaxed Step 2, and
  the Step-2 termination test $m_k(s_k) = m_k(0)$. -/
  toIsARRun : IsARRun P.toARParams (arqpStop₁ P q ε (arqpData f p x σ) δ d)
    (fun k => ARqpRelaxedStep P p q ε κdecr ω (arqpData f p x σ k) (x k) (s k) (δs k) (dm k))
    (arqpStop₂ (arqpData f p x σ) s) (arqpRho f p x s σ) x s σ
  /-- The initial radii are $\delta_0$. -/
  delta_zero : δ 0 = δ₀
  /-- Step 1: at every iteration $k$ reached, $d_{k,j}$ is a $\varsigma$-approximate optimality
  displacement of radius $\delta_{k,j}$ for the Taylor decrement $\Delta T_{f,j}(x_k, \cdot)$,
  for $j \in [1:q]$. -/
  witness : ∀ k, (∀ i < k, ¬ arqpStop f P p q ε x s σ δ d i) → ∀ j ∈ Finset.Icc 1 q,
    IsApproxMeasureStep ((ftaylorSeries ℝ f (x k)).taylorDecrement j) (δ k j) univ P.ς (d k j)
  /-- Step 3: before termination, a successful iteration inherits the Step-2 radii, and an
  unsuccessful iteration keeps the radii and the Step-1 displacements. -/
  radii : UntilHit (arqpStop f P p q ε x s σ δ d) fun k =>
    (P.η₁ ≤ arqpRho f p x s σ k → δ (k + 1) = δs k) ∧
      (¬ P.η₁ ≤ arqpRho f p x s σ k → δ (k + 1) = δ k ∧ d (k + 1) = d k)

variable {f : E → ℝ} {P : ARqpParams} {p q : ℕ} {ε δ₀ : ℕ → ℝ} {κdecr ω : ℝ} {x s : ℕ → E}
  {σ : ℕ → ℝ} {δ δs : ℕ → ℕ → ℝ} {d dm : ℕ → ℕ → E} {L : ℕ → ℝ}

/-- **Section 12.3** of [cartis2022evaluation], ARqp runs are relaxed runs. For all
$\kappa_{\mathrm{decr}}$ and $\omega$, every run of ARqp
(`CartisGouldToint.Chapter12.algorithm_12_2_2`) is, with the same sequences, a run with the
relaxed Step 2 (`CartisGouldToint.Chapter12.IsARqpSufficientDecreaseRun`). -/
theorem IsARqpSufficientDecreaseRun.of_algorithm_12_2_2
    (h : algorithm_12_2_2 f P p q ε δ₀ x s σ δ δs d dm) :
    IsARqpSufficientDecreaseRun f P p q ε δ₀ κdecr ω x s σ δ δs d dm := by
  have hU : ∀ y : E, {e : E | y + e ∈ (univ : Set E)} = univ := fun y => by ext; simp
  refine ⟨h.toIsARRun.mono fun k hk => Or.inl hk, h.delta_zero, fun k hk j hj => ?_, h.radii⟩
  have := h.witness k hk j hj
  rwa [hU] at this

namespace IsARqpSufficientDecreaseRun

variable (h : IsARqpSufficientDecreaseRun f P p q ε δ₀ κdecr ω x s σ δ δs d dm)
include h

/-- Before termination the model decreases strictly: if the termination test fails at every
$i \le k$, then $m_k(s_k) < m_k(0)$. -/
theorem model_lt {k : ℕ} (hk : ∀ i ≤ k, ¬ arqpStop f P p q ε x s σ δ d i) :
    arqpModel f p x σ k (s k) < arqpModel f p x σ k 0 := by
  have hstep := h.toIsARRun.step_of_forall_le hk
  have hle : arqpModel f p x σ k (s k) ≤ arqpModel f p x σ k 0 := hstep.elim (·.model_le) (·.1)
  exact lt_of_le_of_ne hle fun h2 => hk k le_rfl (Or.inr h2)

/-- If the termination test fails at every $i \le k$, the Step-2 radii satisfy
$\delta_{s_k,j} \in (0, 1]$ for $j \in [1:q]$. -/
theorem stepRadii_mem {k : ℕ} (hk : ∀ i ≤ k, ¬ arqpStop f P p q ε x s σ δ d i) :
    ∀ j ∈ Finset.Icc 1 q, 0 < δs k j ∧ δs k j ≤ 1 := by
  rcases h.toIsARRun.step_of_forall_le hk with hs | hs
  · exact fun j hj => ⟨hs.radius_pos j hj, hs.radius_le_one j hj⟩
  · exact hs.2.2.1

/-- If $\delta_{0,j} \in (0, 1]$ for $j \in [1:q]$, then $\delta_{k,j} \in (0, 1]$ for $j \in [1:q]$
at every iteration $k$ reached, that is, when the termination test fails at every $i < k$. -/
theorem delta_mem (hδ₀ : ∀ j ∈ Finset.Icc 1 q, 0 < δ₀ j ∧ δ₀ j ≤ 1) :
    ∀ k, (∀ i < k, ¬ arqpStop f P p q ε x s σ δ d i) →
      ∀ j ∈ Finset.Icc 1 q, 0 < δ k j ∧ δ k j ≤ 1 := by
  intro k
  induction k with
  | zero => exact fun _ => by rw [h.delta_zero]; exact hδ₀
  | succ k ih =>
    intro hk j hj
    have hk' : ∀ i ≤ k, ¬ arqpStop f P p q ε x s σ δ d i := fun i hi => hk i (by omega)
    obtain ⟨hs, hu⟩ := h.radii k hk'
    by_cases hρ : P.η₁ ≤ arqpRho f p x s σ k
    · rw [hs hρ]; exact h.stepRadii_mem hk' j hj
    · rw [(hu hρ).1]; exact ih (fun i hi => hk' i hi.le) j hj

/-- Under f.D1pL with $p \ge 1$, the weights satisfy $\sigma_{\min} \le \sigma_k \le \sigma_{\max}$
at every iteration $k$ reached, where $\sigma_{\max} = \max(\sigma_0, \gamma_3 L_{f,p}/(1 -
\eta_2))$ (`Optimization.arSigmaMax`). This is Lemma 4.1.2 of [cartis2022evaluation] for the
relaxed run. -/
theorem sigma_le (hf : AssumptionD1pL f p L) (hp : 1 ≤ p) :
    ∀ k, (∀ i < k, ¬ arqpStop f P p q ε x s σ δ d i) →
      P.σmin ≤ σ k ∧ σ k ≤ arSigmaMax P.toARParams (L p) := by
  intro k hk
  have := IsARRun.sigma_le (f := f) (p := p) (x := x) (s := s) h.toIsARRun (C := univ)
    convex_univ (fun y _ => hf.contDiff.contDiffAt) (hf.lipschitz p (Finset.mem_Icc.2 ⟨hp, le_rfl⟩))
    (mem_univ _) (fun k hk _ => ⟨mem_univ _, h.model_lt hk⟩) k hk
  exact ⟨this.2.1, this.2.2⟩

/-- After a successful iteration $k$ before termination, $x_{k+1} = x_k + s_k$ and
$\delta_{k+1} = \delta_{s_k}$, and for $j \in [1:q]$ the displacement $d_{k+1,j}$ is a
$\varsigma$-approximate optimality displacement of radius $\delta_{s_k,j}$ for the Taylor
decrement $\Delta T_{f,j}(x_k + s_k, \cdot)$. -/
theorem next {k : ℕ} (hk : ∀ i ≤ k, ¬ arqpStop f P p q ε x s σ δ d i)
    (hs : P.η₁ ≤ arqpRho f p x s σ k) :
    x (k + 1) = x k + s k ∧ δ (k + 1) = δs k ∧
      (∀ j ∈ Finset.Icc 1 q, IsApproxMeasureStep
        ((ftaylorSeries ℝ f (x k + s k)).taylorDecrement j) (δs k j) univ P.ς (d (k + 1) j)) := by
  have hx1 := h.toIsARRun.eq_add_of_succ hk hs
  have hδ1 := (h.radii k hk).1 hs
  refine ⟨hx1, hδ1, fun j hj => ?_⟩
  have hw := h.witness (k + 1) (fun i hi => hk i (by omega)) j hj
  rwa [hx1, hδ1] at hw

end IsARqpSufficientDecreaseRun

/-- The exponents $\pi_j$ of Lemma 12.2.13 (`CartisGouldToint.Chapter12.arqpPi`) are nondecreasing
in the order: $\pi_j \le \pi_{j'}$ for $j \le j' \le p$. -/
theorem arqpPi_mono {p q j j' : ℕ} (hjj' : j ≤ j') (hj' : j' ≤ p) :
    arqpPi p q j ≤ arqpPi p q j' := by
  unfold arqpPi arqpPiOf
  split_ifs
  · apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact_mod_cast (show p - j' + 1 ≤ p - j + 1 by omega)
  · gcongr

/-- **Section 12.3** of [cartis2022evaluation], with the Notes to Section 12.2.2 (complexity of ARqp
with the relaxed Step 2). Let $f : \mathbb{R}^n \to \mathbb{R}$ satisfy f.Bb with the lower
bound $f_{\mathrm{low}}$ and f.D1pL with the constants $L_{f,j}$. Let $1 \le q \le p$,
$\varepsilon \in (0, 1]^q$, $\delta_0 \in (0, 1]^q$, $\sigma_{\min} > 0$, $\theta < \varsigma$,
$\kappa_{\mathrm{decr}} > 0$ and $\omega \ge \pi_q$. Consider a run of ARqp with the relaxed
Step 2 that satisfies the radii hypotheses of Theorem 12.2.14 at every iteration $k$ before
termination whose step satisfies the Step-2 conditions of ARqp: if $q \le 2$, then
$\delta_{s_k,j} = 1$ for $j \in [1:q]$; if $q > 2$ and $\|s_k\| < 1$, then $\delta_{s_k,j} \ge
\kappa_\delta(\sigma_k) \varepsilon_j$ for $j \in [1:q]$ (12.2.50). Then the run terminates at
some iteration $k_\varepsilon$, the point $x_{k_\varepsilon}$ is an
$(\varepsilon, \delta_\varepsilon)$-approximate $q$-th order minimizer of $f$ for some
$\delta_\varepsilon \in (0, 1]^q$, and the numbers of evaluations of $f$ and of its derivatives
are at most
$$\kappa^a \frac{f(x_0) - f_{\mathrm{low}}}{\varepsilon_{\min}^{\omega}} + \kappa^c \qquad
  \text{and} \qquad \kappa^s \frac{f(x_0) - f_{\mathrm{low}}}{\varepsilon_{\min}^{\omega}} +
  2,$$
where $\kappa' = \min(\kappa_{\Delta m}, \kappa_{\mathrm{decr}}, \sigma_{\min}
\kappa_{\mathrm{decr}}/(p+1)!)$, $\kappa^s = 1/(\eta_1 \kappa')$, $\kappa^a = \kappa^s (1 +
|\log \gamma_1|/\log \gamma_2)$, and $\kappa^c$ is the constant of Theorem 12.2.14.

**Reading.** The source takes $\omega = \pi_q$, the exponent of Theorem 12.2.14, and states only
that the relaxation "does not affect the conclusions of the complexity theorem". The theorem
states the bounds for every $\omega \ge \pi_q$, with $\varepsilon_{\min}^{\omega}$ in place of
$\min_j \varepsilon_j^{\pi_j}$ and $\kappa'$ in place of $\kappa_{\Delta m}$.

Here $\kappa_\delta(\sigma) = \varsigma \theta/(8 (3 L_f + \sigma))$, with
$L_f = \max(1, \max_j L_{f,j})$. The counts are `Optimization.funEvalCount` and
`Optimization.derivEvalCount` of the successful iterations. A long step (12.3.2) gives the
decrease $\sigma_{\min} \kappa_{\mathrm{decr}} \varepsilon_{\min}^{\omega}/(p+1)!$ by Lemma 4.1.1.
The Lean counterparts of the constants are:
* $\varepsilon_{\min} = \min(1, \min_j \varepsilon_j)$ is `Optimization.finMin 1 ε q`;
* $\kappa_{\Delta m}$ is `CartisGouldToint.Chapter12.arqpKappaDm`;
* $\kappa_\delta$ is `Optimization.arqpKappaDelta`;
* $\kappa^c$ is `Optimization.kappaCARqp`. -/
theorem complexity_arqpSufficientDecrease {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {x s : ℕ → EuclideanSpace ℝ (Fin n)} {d dm : ℕ → ℕ → EuclideanSpace ℝ (Fin n)} {flow : ℝ}
    (hb : Chapter02.AssumptionBb f flow) (hf : AssumptionD1pL f p L) (hq : 1 ≤ q) (hqp : q ≤ p)
    (hσmin : 0 < P.σmin) (hθς : P.θ < P.ς) (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1)
    (hδ₀ : ∀ j ∈ Finset.Icc 1 q, 0 < δ₀ j ∧ δ₀ j ≤ 1) (hκ : 0 < κdecr) (hω : arqpPi p q q ≤ ω)
    (h : IsARqpSufficientDecreaseRun f P p q ε δ₀ κdecr ω x s σ δ δs d dm)
    (hrad : (q ≤ 2 → ∀ k, (∀ i ≤ k, ¬ arqpStop f P p q ε x s σ δ d i) →
        ARqpStep univ P q ε (arqpData f p x σ k) (x k) (s k) (δs k) (dm k) →
        ∀ j ∈ Finset.Icc 1 q, δs k j = 1) ∧
      (2 < q → ∀ k, (∀ i ≤ k, ¬ arqpStop f P p q ε x s σ δ d i) →
        ARqpStep univ P q ε (arqpData f p x σ k) (x k) (s k) (δs k) (dm k) → ‖s k‖ < 1 →
        ∀ j ∈ Finset.Icc 1 q, arqpKappaDelta P (finMax 1 L p) (σ k) * ε j ≤ δs k j)) :
    ∃ kε, IsFirstHit (arqpStop f P p q ε x s σ δ d) kε ∧
      (∃ δε : ℕ → ℝ, IsEpsDeltaApproxMinimizer f q ε δε (x kε)) ∧
      (funEvalCount kε : ℝ) ≤
        1 / (P.η₁ * min (arqpKappaDm P L p q) (min κdecr (P.σmin / ((p + 1)! : ℝ) * κdecr))) *
          (1 + |Real.log P.γ₁| / Real.log P.γ₂) * (f (x 0) - flow) / finMin 1 ε q ^ ω +
          kappaCARqp P L p ∧
      (derivEvalCount (fun k => P.η₁ ≤ arqpRho f p x s σ k) kε : ℝ) ≤
        1 / (P.η₁ * min (arqpKappaDm P L p q) (min κdecr (P.σmin / ((p + 1)! : ℝ) * κdecr))) *
          (f (x 0) - flow) / finMin 1 ε q ^ ω + 2 := by
  have hp : 1 ≤ p := hq.trans hqp
  have hLp : 1 ≤ L p := hf.one_le p (Finset.mem_Icc.2 ⟨hp, le_rfl⟩)
  have hL1 : 1 ≤ finMax 1 L p := one_le_finMax
  set εm := finMin 1 ε q with hεm_def
  have hεm : 0 < εm := finMin_pos one_pos fun j hj => (hε j hj).1
  have hεm1 : εm ≤ 1 := finMin_le_left
  set X := εm ^ ω with hX
  have hX0 : 0 < X := Real.rpow_pos_of_pos hεm _
  have hfacp : (0 : ℝ) < (p + 1)! := by positivity
  set κ' := min (arqpKappaDm P L p q) (min κdecr (P.σmin / ((p + 1)! : ℝ) * κdecr)) with hκ'
  have hκDm := arqpKappaDm_pos (q := q) hσmin hθς hLp
  have hκ'0 : 0 < κ' := lt_min hκDm (lt_min hκ (by positivity))
  have hη := P.η₁_pos
  have hπ0 : ∀ j, 0 ≤ arqpPi p q j := fun j => arqpPiOf_nonneg _ p j
  have hω0 : 0 ≤ ω := (hπ0 q).trans hω
  -- `ε_min^ω ≤ min_j ε_j^{π_j}`
  have hXm : X ≤ finMin 1 (fun j => ε j ^ arqpPi p q j) q := by
    refine le_finMin (Real.rpow_le_one hεm.le hεm1 hω0) fun j hj => ?_
    have hjq := (Finset.mem_Icc.1 hj).2
    calc X ≤ εm ^ arqpPi p q q := Real.rpow_le_rpow_of_exponent_ge hεm hεm1 hω
      _ ≤ εm ^ arqpPi p q j :=
          Real.rpow_le_rpow_of_exponent_ge hεm hεm1 (arqpPi_mono hjq hqp)
      _ ≤ ε j ^ arqpPi p q j := Real.rpow_le_rpow hεm.le (finMin_le hj) (hπ0 j)
  -- the decrease at successful iterations followed by a non-terminating one
  have hdec : ∀ k, (∀ i ≤ k + 1, ¬ arqpStop f P p q ε x s σ δ d i) →
      P.η₁ ≤ arqpRho f p x s σ k → P.η₁ * (κ' * X) ≤ f (x k) - f (x (k + 1)) := by
    intro k hk hs
    have hk' : ∀ i ≤ k, ¬ arqpStop f P p q ε x s σ δ d i := fun i hi => hk i (by omega)
    have hσ := h.sigma_le hf hp k fun i hi => hk' i hi.le
    have hlt := h.model_lt hk'
    have hT := lt_taylorDecrement_of_regularizedModel_lt hlt
    have hσ0 : 0 ≤ σ k := P.σmin_nonneg.trans hσ.1
    have hpos : 0 < (ftaylorSeries ℝ f (x k)).taylorDecrement p (s k) :=
      lt_of_le_of_lt (by positivity) hT
    have hmain : κ' * X ≤ (ftaylorSeries ℝ f (x k)).taylorDecrement p (s k) := by
      rcases h.toIsARRun.step_of_forall_le hk' with hst | ⟨-, -, -, hd | hlong⟩
      · obtain ⟨hx1, hδ1, hw⟩ := h.next hk' hs
        have hfail : ¬ MeasureTestPasses
            (fun j => (ftaylorSeries ℝ f (x k + s k)).taylorDecrement j) q P.ς ε (δs k)
            (d (k + 1)) := by
          intro ht
          refine hk (k + 1) le_rfl (Or.inl ?_)
          change MeasureTestPasses (fun j => (ftaylorSeries ℝ f (x (k + 1))).taylorDecrement j)
            q P.ς ε (δ (k + 1)) (d (k + 1))
          rwa [hx1, hδ1]
        have hrad' : (q ≤ 2 → ∀ j ∈ Finset.Icc 1 q, δs k j = 1) ∧
            (2 < q → 1 ≤ ‖s k‖ ∨ ∀ j ∈ Finset.Icc 1 q,
              arqpKappaDelta P (finMax 1 L p) (arSigmaMax P.toARParams (L p)) * ε j ≤
                δs k j) := by
          refine ⟨fun hq2 => hrad.1 hq2 k hk' hst, fun hq2 => ?_⟩
          by_cases hlong : 1 ≤ ‖s k‖
          · exact Or.inl hlong
          refine Or.inr fun j hj => le_trans ?_ (hrad.2 hq2 k hk' hst (not_le.1 hlong) j hj)
          exact mul_le_mul_of_nonneg_right (arqpKappaDelta_anti P hL1 hσ0 hσ.2)
            (hε j hj).1.le
        have hU : {e : EuclideanSpace ℝ (Fin n) | x k + s k + e ∈ (univ : Set _)} = univ := by
          ext; simp
        have hTop := hf.toLipschitzDerivsAnchored_top hp univ
        have := ARqpStep.taylorDecrement_ge hTop (hf.one_le_top hp)
          subset_rfl hq hqp hθς hε (mem_univ _) hσ.1 hσ.2 hst hlt (by rw [hU]; exact hw)
          hfail (u := q ≤ 2)
          ⟨hrad'.1, fun h' => hrad'.2 (not_le.1 h')⟩
        calc κ' * X ≤ arqpKappaDm P L p q * finMin 1 (fun j => ε j ^ arqpPi p q j) q :=
              mul_le_mul (min_le_left _ _) hXm hX0.le hκDm.le
          _ ≤ _ := this
      · calc κ' * X ≤ κdecr * X :=
              mul_le_mul_of_nonneg_right ((min_le_right _ _).trans (min_le_left _ _)) hX0.le
          _ ≤ _ := hd
      · have hn : ((p + 1 : ℕ) : ℝ) ≠ 0 := by positivity
        have hpow : κdecr * X ≤ ‖s k‖ ^ (p + 1) := by
          have := pow_le_pow_left₀ (by positivity) hlong (p + 1)
          refine le_trans (le_of_eq ?_) this
          rw [mul_pow, ← Real.rpow_natCast (κdecr ^ _), ← Real.rpow_natCast (εm ^ _),
            ← Real.rpow_mul hκ.le, ← Real.rpow_mul hεm.le, one_div_mul_cancel hn,
            div_mul_cancel₀ _ hn, Real.rpow_one]
        calc κ' * X ≤ P.σmin / ((p + 1)! : ℝ) * κdecr * X :=
              mul_le_mul_of_nonneg_right ((min_le_right _ _).trans (min_le_right _ _)) hX0.le
          _ = P.σmin / ((p + 1)! : ℝ) * (κdecr * X) := by ring
          _ ≤ σ k / ((p + 1)! : ℝ) * ‖s k‖ ^ (p + 1) := by
              gcongr
              exact hσ.1
          _ ≤ _ := hT.le
    have := (h.toIsARRun.sub_ge_of_succ (w := f)
      (pred := fun k => (ftaylorSeries ℝ f (x k)).taylorDecrement p (s k)) hk' rfl hpos hs).2
    exact (mul_le_mul_of_nonneg_left hmain hη.le).trans this
  have hδ : 0 < P.η₁ * (κ' * X) := by positivity
  obtain ⟨kε, hk, hF, hD⟩ := h.toIsARRun.exists_isFirstHit_of_decrease
    (σmax := arSigmaMax P.toARParams (L p)) (fun k hk => (h.sigma_le hf hp k hk).2)
    (V := fun k => f (x k)) (Vlow := flow) hδ
    (fun k hk => by
      have hσ := h.toIsARRun.sigma_pos (K := k) (fun i hi => hk i hi.le) k le_rfl
      have hT := lt_taylorDecrement_of_regularizedModel_lt (h.model_lt hk)
      exact (h.toIsARRun.accept k hk).le (w := f) rfl (lt_of_le_of_lt (by positivity) hT))
    (fun k _ => hb (x k)) hdec
  have hlog := P.toARParams.log_γ₂_pos
  refine ⟨kε, hk, ?_, hF.trans_eq ?_, hD.trans_eq ?_⟩
  · by_cases h1 : arqpStop₁ P q ε (arqpData f p x σ) δ d kε
    · exact ⟨δ kε, fun j hj => ⟨hε j hj, h.delta_mem hδ₀ kε hk.2 j hj⟩,
        MeasureTestPasses.isEpsDeltaApprox P.ς_pos (h.witness kε hk.2) h1⟩
    · have h2 : arqpStop₂ (arqpData f p x σ) s kε := hk.1.resolve_left h1
      have hσ : 0 < σ kε := h.toIsARRun.sigma_pos hk.2 kε le_rfl
      have hU : {e : EuclideanSpace ℝ (Fin n) | x kε + e ∈ (univ : Set _)} = univ := by
        ext; simp
      have hmin : IsMinOn (arqpModel f p x σ kε) univ 0 := by
        rcases h.toIsARRun.step kε hk.2 h1 with hst | hst
        · have := hst.isMinOn_of_eq h2
          rwa [hU] at this
        · exact hst.2.1 h2
      exact ⟨_, isEpsDeltaApproxMinimizer_of_isMinOn_zero hf hqp hε hσ hmin⟩
  · rw [kappaCARqp]
    field_simp
  · field_simp

end CartisGouldToint.Chapter12
