/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Optimization.Constrained.TwoPhase.HighOrder.Examples.SlowDecay
import Numlib.Optimization.ModelBased.HighOrder.TRqComplexity

/-!
# Long two-phase runs with a trust-region inner method

This file builds runs of the two-phase method TPqp-GC ([cartis2022evaluation], Algorithm 14.3.2)
whose inner method is TRq with a feasible set. The data are those of
`Numlib.Optimization.Constrained.TwoPhase.HighOrder.Examples.SlowDecay`, with the objective $f = 0$,
the feasible set $X = \{v : v_1 \ge 1\}$ and $\nu = \tfrac12 \|c\|^2$. There are two cases.

* With the constraint $c(v) = (1, v_1^{-1/8}, v_2)$ and $x_0 = (2, 0)$, $\|c\| \ge 1$ everywhere, so
  the run ends in Phase 1. Its first inner call on $\nu$, with tolerances $\varepsilon_j/2$, is the
  long run of `Constrained.TwoPhaseExample.SlowDecay.exists_long_run`.
* With the constraint $c_2(v) = (v_1^{-1/8}, v_2)$ and $x_0 = (256, 0)$,
  $\|c_2(x_0)\| = 1/2 = \theta \varepsilon_0$ for $\theta = 1/2$ and $\varepsilon_0 = 1$, so Phase 2
  is entered at once. Its target is $t_1 = -\sqrt3/2$, and $\mu(\cdot, t_1)$ differs from
  $\tfrac12 \|c\|^2$ by a constant on $X$. Phase 2 consists of one inner call, the same long run,
  followed by termination in case (c).

In both cases the call makes at least $2^{22M} - 2^{18M} - 2^{10M}$ successful iterations for the
tolerances $\varepsilon_1 = 2^{-10M}$ and $\varepsilon_2 = 2^{-5M}$, while
$$\max\Bigl[\varepsilon_0^{-1},\ \max_j \varepsilon_0^{-j} \varepsilon_j^{-(j+1)}\Bigr] \le 2^{20M}
  \quad \text{and} \quad |\log(\varepsilon_0 \varepsilon_{\min})| \le 10M.$$
Hence no bound of the form $\kappa\,(1 + |\log(\varepsilon_0 \varepsilon_{\min})|)
\max[\varepsilon_0^{-1}, \max_j \varepsilon_0^{-j} \varepsilon_j^{-(j+1)}]$ holds for these runs.

## Main results

* `Constrained.TwoPhaseExample.SlowDecay.exists_isTRqOutputCost`: a terminating TRq call on $\nu$
  from $(2, 0)$ uses at least $2^{22M} - 2^{18M} - 2^{10M} + 1$ derivative evaluations.
* `Constrained.TwoPhaseExample.SlowDecay.exists_isHighOrderTargetRun`: a run of Phase 2 from
  $(256, 0)$ with TRq calls uses at least $2^{22M} - 2^{18M} - 2^{10M} + 1$ derivative evaluations.
* `Constrained.TwoPhaseExample.SlowDecay.finMax_tol_le` and
  `Constrained.TwoPhaseExample.SlowDecay.abs_log_tol_le`: the order is at most $2^{20M}$ and the
  logarithmic term is at most $10M$.
* `Constrained.TwoPhaseExample.SlowDecay.not_le_of_count`: such a count exceeds every bound
  $\kappa\,(1 + \Lambda)\,O$ with $\Lambda \le 10M$ and $O \le 2^{20M}$, for $M$ large.

## Implementation notes

* The smoothness of $\nu$ on the sublevel set of $x_0$, in the form of anchored Lipschitz
  derivatives (`LipschitzDerivsAnchored`), is a hypothesis of the two main statements.
-/

open Set Metric Filter
open scoped Nat ContDiff Topology

namespace Constrained.TwoPhaseExample.SlowDecay

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-- **A long terminating inner call on $\nu$ from $(2, 0)$.** Let $q \ge 2$ and $M \ge 1$, and let
the tolerances satisfy $\varepsilon_j \in (0, 1]$ for $j \in [1 : q]$,
$\varepsilon_1 = 2^{-10M}/2$ and $\varepsilon_2 = 2^{-5M}/2$. Assume that
$\nu = \tfrac12 \|c\|^2$ satisfies `LipschitzDerivsAnchored` with the open set
$X_0 = \{v : v_1 > 1/2\}$, the anchors $\{z \in X : \|c(z)\| \le \|c(x_0)\|\}$ for
$x_0 = (2, 0)$, the orders $1, \dots, q$ and the constants $L$. Then there is a terminating call
of TRq with a feasible set on $\nu$ from $x_0$, with the parameters
`Constrained.TwoPhaseExample.SlowDecay.params` and threshold $\vartheta = 1$, that returns a
point $y \in X$ and a radius $\delta \in (0, 1]$ such that $y$ is
$(\varepsilon, \delta)$-approximately optimal of order $q$ for $\nu$ on $X$, and that uses
$$n_D \ge 2^{22M} - 2^{18M} - 2^{10M} + 1$$
derivative evaluations.

The difference $2^{22M} - 2^{18M} - 2^{10M}$ is in natural numbers. -/
theorem exists_isTRqOutputCost {q : ℕ} (hq : 2 ≤ q) {M : ℕ} (hM : 1 ≤ M) {ε : ℕ → ℝ}
    (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1) (h1 : ε 1 = (1 / 2) ^ (10 * M) / 2)
    (h2 : ε 2 = (1 / 2) ^ (5 * M) / 2) {L : ℕ → ℝ}
    (hν : LipschitzDerivsAnchored (halfSqNorm con) openHalfPlane
      {z ∈ halfPlane | ‖con z‖ ≤ ‖con (pt 2 0)‖} 1 q L) :
    ∃ (y : ℝ²) (δ : ℝ) (nF nD : ℕ),
      Optimization.IsTRqOutputCost (halfSqNorm con) halfPlane params q ε 1 (pt 2 0) y
        (fun _ => δ) nF nD ∧ y ∈ halfPlane ∧ δ ∈ Ioc 0 1 ∧
      Optimization.IsEpsDeltaApprox (ftaylorSeries ℝ (halfSqNorm con) y) {e | y + e ∈ halfPlane}
        q ε (fun _ => δ) ∧
      2 ^ (22 * M) - 2 ^ (18 * M) - 2 ^ (10 * M) + 1 ≤ nD := by
  obtain ⟨x, s, Δ, jk, d, T, hx0, hrun, hns, hcount⟩ := exists_long_run hq hM h1 h2 le_rfl
    (by rw [h1]; exact tol_lt_slope_two hM)
  have h1q : 1 ∈ Finset.Icc 1 q := Finset.mem_Icc.2 ⟨le_rfl, by omega⟩
  have hϑ : Optimization.finMin 1 ε q ≤ 1 := (Optimization.finMin_le h1q).trans (hε 1 h1q).2
  have hx0X : x 0 ∈ halfPlane := by rw [hx0]; exact pt_mem_halfPlane (by norm_num)
  have hA : ∀ z ∈ halfPlane, halfSqNorm con z ≤ halfSqNorm con (x 0) →
      z ∈ {z ∈ halfPlane | ‖con z‖ ≤ ‖con (pt 2 0)‖} := fun z hz hzx => by
    rw [hx0] at hzx
    exact ⟨hz, halfSqNorm_le_halfSqNorm_iff.1 hzx⟩
  obtain ⟨kε, hhit, hmem, hrad, hcert, -, -⟩ := Optimization.IsTRqRun.complexity
    (flow := 0) (fun z _ => by rw [halfSqNorm_apply]; positivity) hν halfPlane_subset hA hx0X hε
    hϑ le_rfl hrun
  have hkT : T ≤ kε := by
    by_contra h
    exact hns kε (by omega) hhit.1
  refine ⟨x kε, min (Δ kε) 1, _, _, ⟨x, s, Δ, jk, d, kε, hrun, hhit, hx0, rfl, fun _ _ => rfl, rfl,
    rfl⟩, hmem, hrad, hcert, ?_⟩
  rw [Optimization.derivEvalCount]
  refine Nat.add_le_add_right (hcount.trans (Finset.card_le_card ?_)) 1
  exact Finset.filter_subset_filter _ (Finset.range_subset_range.2 hkT)

open Classical in
/-- **A long Phase 2 with one inner call.** Let $q \ge 2$ and $M \ge 2$, and let the tolerances
satisfy $\varepsilon_j \in (0, 1]$ for $j \in [0 : q]$, $\varepsilon_0 = 1$,
$\varepsilon_1 = 2^{-10M}$ and $\varepsilon_2 = 2^{-5M}$. Assume that $\nu = \tfrac12 \|c\|^2$
satisfies `LipschitzDerivsAnchored` with the open set $X_0 = \{v : v_1 > 1/2\}$, the anchors
$\{z \in X : \|c(z)\| \le \|c(x_0)\|\}$ for $x_0 = (256, 0)$, the orders $1, \dots, q$ and the
constants $L$. Then there is a run of Phase 2 of a high-order target-following method for the
objective $f = 0$, the constraint $c_2$ and the feasible set $X$, with $\theta = \beta = 1/2$,
started at $x_0$, with the following properties:

* every inner call at a reached outer iteration $k \ge 1$ is a call of TRq with a feasible set,
  with the parameters `Constrained.TwoPhaseExample.SlowDecay.params`, threshold $\vartheta = 1$
  and tolerances $\beta \|r(x_k, t_k)\| \varepsilon_j$;
* at every outer iteration $k_\varepsilon$ at which Phase 2 ends, the number of derivative
  evaluations is at least $2^{22M} - 2^{18M} - 2^{10M} + 1$.

The difference $2^{22M} - 2^{18M} - 2^{10M}$ is in natural numbers. -/
theorem exists_isHighOrderTargetRun {q : ℕ} (hq : 2 ≤ q) {M : ℕ} (hM : 2 ≤ M) {ε : ℕ → ℝ}
    (hε : ∀ j ∈ Finset.range (q + 1), 0 < ε j ∧ ε j ≤ 1) (h0 : ε 0 = 1)
    (h1 : ε 1 = (1 / 2) ^ (10 * M)) (h2 : ε 2 = (1 / 2) ^ (5 * M)) {L : ℕ → ℝ}
    (hν : LipschitzDerivsAnchored (halfSqNorm con) openHalfPlane
      {z ∈ halfPlane | ‖con z‖ ≤ ‖con (pt 256 0)‖} 1 q L) :
    ∃ D : HighOrderTargetSeq ℝ²,
      IsHighOrderTargetRun (fun _ => 0) con₂ halfPlane q (1 / 2) (1 / 2) ε (pt 256 0) D ∧
      (∀ k, 1 ≤ k → D.Before (fun _ => 0) con₂ halfPlane q (1 / 2) ε k →
        Optimization.IsTRqCallOut (targetMerit (fun _ => 0) con₂ (D.t k)) halfPlane params q
          (fun j => 1 / 2 * targetResidual (fun _ => 0) con₂ (D.t k) (D.x k) * ε j) 1 (D.xi k)
          (D.e k) (D.succ k) (D.δ (k + 1))) ∧
      ∀ kε, D.IsEnd (fun _ => 0) con₂ halfPlane q (1 / 2) ε kε →
        ((2 ^ (22 * M) - 2 ^ (18 * M) - 2 ^ (10 * M) : ℕ) : ℝ) + 1 ≤ D.derivEvals kε := by
  set x₀ := pt 256 0 with hx₀
  have hcx₀ : ‖con₂ x₀‖ = 1 / 2 := norm_con₂_x₀
  have hx₀X : x₀ ∈ halfPlane := pt_mem_halfPlane (by norm_num)
  obtain ⟨t₁, ht₁⟩ : ∃ t₁ : ℝ, t₁ = (fun _ : ℝ² => (0 : ℝ)) x₀ - √(ε 0 ^ 2 - ‖con₂ x₀‖ ^ 2) :=
    ⟨_, rfl⟩
  have ht₁sq : t₁ ^ 2 = 3 / 4 := by
    rw [ht₁, h0, hcx₀]
    simp only [zero_sub, neg_sq]
    rw [Real.sq_sqrt (by norm_num)]
    norm_num
  set G := targetMerit (fun _ : ℝ² => (0 : ℝ)) con₂ t₁ with hG
  have hres_ge : ∀ v, 1 / 2 ≤ targetResidual (fun _ : ℝ² => (0 : ℝ)) con₂ t₁ v :=
    fun v => by
    have h := targetResidual_sq (f := fun _ : ℝ² => (0 : ℝ)) (c := con₂) (t := t₁)
      (x := v)
    have hn := targetResidual_nonneg (f := fun _ : ℝ² => (0 : ℝ)) (c := con₂)
      (t := t₁) (x := v)
    nlinarith [sq_nonneg ‖con₂ v‖]
  have hres0 : targetResidual (fun _ : ℝ² => (0 : ℝ)) con₂ t₁ x₀ = 1 := by
    have h := targetResidual_sq (f := fun _ : ℝ² => (0 : ℝ)) (c := con₂) (t := t₁)
      (x := x₀)
    have hn := targetResidual_nonneg (f := fun _ : ℝ² => (0 : ℝ)) (c := con₂)
      (t := t₁) (x := x₀)
    rw [hcx₀] at h
    nlinarith
  set ε' : ℕ → ℝ := fun j =>
    1 / 2 * targetResidual (fun _ : ℝ² => (0 : ℝ)) con₂ t₁ x₀ * ε j with hε'
  have hε'j : ∀ j, ε' j = ε j / 2 := fun j => by simp only [hε', hres0]; ring
  have hεI : ∀ j ∈ Finset.Icc 1 q, 0 < ε j ∧ ε j ≤ 1 := fun j hj =>
    hε j (Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.mem_Icc.1 hj).2))
  -- the run of TRq-SC on `½‖c‖²`
  obtain ⟨x, s, Δ, jk, d, T, hx0, hrunF, hns, hcount⟩ := exists_long_run hq
    (by omega : 1 ≤ M) (ε := ε') (by rw [hε'j, h1]) (by rw [hε'j, h2]) (a₀ := 256) (by norm_num)
    (by rw [hε'j, h1]; exact tol_lt_slope_256 hM)
  have hε'I : ∀ j ∈ Finset.Icc 1 q, ε' j ∈ Ioc 0 1 := fun j hj => by
    rw [hε'j]
    have := hεI j hj
    exact ⟨by linarith, by linarith⟩
  have h1q : 1 ∈ Finset.Icc 1 q := Finset.mem_Icc.2 ⟨le_rfl, by omega⟩
  have hϑ' : Optimization.finMin 1 ε' q ≤ 1 := (Optimization.finMin_le h1q).trans (hε'I 1 h1q).2
  have hx0X : x 0 ∈ halfPlane := by rw [hx0]; exact hx₀X
  have hA : ∀ z ∈ halfPlane, halfSqNorm con z ≤ halfSqNorm con (x 0) →
      z ∈ {z ∈ halfPlane | ‖con z‖ ≤ ‖con x₀‖} := fun z hz hzx => by
    rw [hx0] at hzx
    exact ⟨hz, halfSqNorm_le_halfSqNorm_iff.1 hzx⟩
  obtain ⟨kε, hhit, hmem, hrad, hcert, -, -⟩ := Optimization.IsTRqRun.complexity
    (flow := 0) (fun z _ => by rw [halfSqNorm_apply]; positivity) hν
    halfPlane_subset hA hx0X hε'I hϑ' le_rfl
    hrunF
  have hkT : T ≤ kε := by
    by_contra h
    exact hns kε (by omega) hhit.1
  -- the same run on `μ(·, t₁)`
  have hT : ∀ y ∈ halfPlane, ∀ j, (ftaylorSeries ℝ G y).taylorDecrement j =
      (ftaylorSeries ℝ (halfSqNorm con) y).taylorDecrement j := fun y hy j =>
    taylorDecrement_targetMerit_con₂ t₁ (lt_of_lt_of_le one_pos hy) j
  have hD : ∀ y ∈ halfPlane, ∀ z ∈ halfPlane, G y - G z = halfSqNorm con y - halfSqNorm con z :=
    fun y _ z _ => by rw [hG, targetMerit_con₂, targetMerit_con₂]; ring
  obtain ⟨hrunG, hiff, hrho⟩ := hrunF.congr_of_taylorDecrement_eq hT hD hx0X
  have hhitG : Optimization.IsFirstHit
      (Optimization.trqTest (fun k => ftaylorSeries ℝ G (x k)) params q ε' 1 Δ d) kε :=
    ⟨(hiff kε hhit.2).2 hhit.1, fun i hi hGi =>
      hhit.2 i hi ((hiff i fun j hj => hhit.2 j (hj.trans hi)).1 hGi)⟩
  set δo : ℝ := min (Δ kε) 1 with hδo
  -- the Phase-2 sequences
  obtain ⟨Dx, hDx⟩ : ∃ Dx : ℕ → ℝ², ∀ k, Dx k = if k ≤ 1 then x₀ else x kε := ⟨_, fun _ => rfl⟩
  set D : HighOrderTargetSeq ℝ² := ⟨Dx, fun _ => t₁, fun _ _ => δo, fun _ => x, fun _ => kε,
    fun _ i => params.η₁ ≤ Optimization.trqRatio G (fun k => ftaylorSeries ℝ G (x k)) x s jk i⟩
    with hDdef
  have hDx1 : D.x 1 = x₀ := by simp [hDdef, hDx]
  have hDx2 : D.x 2 = x kε := by simp [hDdef, hDx]
  have hnotKa : ¬ D.IsKa (fun _ => 0) con₂ (1 / 2) ε 1 := by
    change ¬ (targetResidual _ _ t₁ (D.x 2) < 1 / 2 * ε 0)
    rw [h0, mul_one]
    exact not_lt.2 (hres_ge _)
  have hnotKb : ¬ D.IsKb (fun _ => 0) con₂ (1 / 2) ε 1 := by
    rintro ⟨-, hlt⟩
    change (0 : ℝ) < t₁ at hlt
    have : t₁ ≤ 0 := by rw [ht₁]; simp
    linarith
  have hstop1 : D.Stop (fun _ => 0) con₂ halfPlane q (1 / 2) ε 1 := Or.inl ⟨hnotKa, hnotKb⟩
  have hbef : ∀ k, 1 ≤ k → D.Before (fun _ => 0) con₂ halfPlane q (1 / 2) ε k → k = 1 :=
    fun k hk hb => by
    by_contra hne
    exact hb 1 le_rfl (by omega) hstop1
  have hcertG : ∀ j ∈ Finset.Icc 1 q, Optimization.taylorMeasure (ftaylorSeries ℝ G (x kε)) j δo
      {e | x kε + e ∈ halfPlane} ≤ ε j * targetResidual (fun _ => 0) con₂ t₁
        (x kε) * δo ^ j / j ! := fun j hj => by
    have hcj := hcert j hj
    have e : Optimization.taylorMeasure (ftaylorSeries ℝ G (x kε)) j δo {e | x kε + e ∈ halfPlane}
        = Optimization.taylorMeasure (ftaylorSeries ℝ (halfSqNorm con) (x kε)) j δo
          {e | x kε + e ∈ halfPlane} := by
      simp only [Optimization.taylorMeasure_eq_sSup, hT _ hmem j]
    rw [e]
    refine hcj.trans ?_
    rw [hε'j]
    have hεj := (hεI j hj).1
    have hδ0 : 0 ≤ δo := hrad.1.le
    have := hres_ge (x kε)
    have : ε j / 2 ≤ ε j * targetResidual (fun _ => 0) con₂ t₁ (x kε) := by
      nlinarith
    gcongr
  have hphase2 : IsHighOrderTargetRun (fun _ => 0) con₂ halfPlane q (1 / 2) (1 / 2) ε x₀ D := by
    refine ⟨by norm_num, by norm_num, by norm_num, le_rfl, fun j hj => (hε j hj).1,
      fun j hj => (hε j hj).2, hx₀X, by rw [hcx₀, h0]; norm_num, hDx1, ht₁,
      fun k hk hb => ?_, fun k hk hb => ?_, fun k hk hb => ?_, fun k hk hb => ?_,
      fun k hk hb => ?_, fun k hk hb i hi => ?_, fun k hk hb i hi => ?_,
      fun k hk hb ha => ?_, fun k hk hb hb' => ?_⟩
    · obtain rfl := hbef k hk hb; rw [hDx2]; exact hmem
    · obtain rfl := hbef k hk hb; exact fun _ _ => hrad
    · obtain rfl := hbef k hk hb
      refine Or.inr (Or.inr fun j hj => ?_)
      rw [hDx2]
      exact hcertG j hj
    · obtain rfl := hbef k hk hb; rw [hDx1]; exact hx0
    · obtain rfl := hbef k hk hb; rw [hDx2]
    · obtain rfl := hbef k hk hb
      exact Optimization.IsTRqRun.apply_succ_le hrunG (fun j hj => (hε'I j hj).1.le) zero_le_one
        fun l hl => hhitG.2 l (lt_of_le_of_lt hl hi)
    · obtain rfl := hbef k hk hb
      rw [h0, mul_one]; exact hres_ge _
    · obtain rfl := hbef k hk hb; exact absurd ha hnotKa
    · obtain rfl := hbef k hk hb; exact absurd hb' hnotKb
  refine ⟨D, hphase2, fun k hk hb => ?_, fun kε' hend => ?_⟩
  · -- the inner calls
    obtain rfl := hbef k hk hb
    rw [hDx1]
    exact ⟨x, s, Δ, jk, d, kε, hrunG, hhitG, le_rfl, fun _ _ => rfl, fun _ _ => Iff.rfl,
      fun _ _ => rfl⟩
  · -- the derivative evaluations
    obtain rfl : kε' = 1 := hbef kε' hend.1 hend.2.2
    have hsucc : 2 ^ (22 * M) - 2 ^ (18 * M) - 2 ^ (10 * M) ≤ D.succCount 1 := by
      refine hcount.trans (Finset.card_le_card fun i hi => ?_)
      rw [Finset.mem_filter] at hi ⊢
      have hiT := Finset.mem_range.1 hi.1
      refine ⟨Finset.mem_range.2 (by change i < kε; omega), ?_⟩
      change params.η₁ ≤ Optimization.trqRatio G (fun k => ftaylorSeries ℝ G (x k)) x s jk i
      rw [hrho i fun l hl => hhit.2 l (by omega)]
      exact hi.2
    rw [HighOrderTargetSeq.derivEvals_eq_sum, Finset.Icc_self, Finset.sum_singleton]
    push_cast
    have : ((2 ^ (22 * M) - 2 ^ (18 * M) - 2 ^ (10 * M) : ℕ) : ℝ) ≤ (D.succCount 1 : ℝ) := by
      exact_mod_cast hsucc
    linarith


/-- At the tolerances `Constrained.TwoPhaseExample.SlowDecay.tol M`, the largest term of the order
is at most $2^{20M}$:
$$\max\Bigl[\varepsilon_0^{-1},\ \max_{j \in [1 : q]} \varepsilon_0^{1 - (j+1)}
  \varepsilon_j^{-(j+1)}\Bigr] \le 2^{20M}.$$
-/
theorem finMax_tol_le {q : ℕ} (M : ℕ) :
    Optimization.finMax (tol M 0)⁻¹
      (fun j => tol M 0 ^ (1 - ((j : ℝ) + 1)) * tol M j ^ (-((j : ℝ) + 1))) q ≤ 2 ^ (20 * M) := by
  have h0 : tol M 0 = 1 := by simp [tol]
  have h1M : (1 : ℝ) ≤ 2 ^ (20 * M) := one_le_pow₀ (by norm_num)
  refine Optimization.finMax_le (by rw [h0, inv_one]; exact h1M) fun j hj => ?_
  rw [h0, Real.one_rpow, one_mul]
  have hj1 := (Finset.mem_Icc.1 hj).1
  by_cases hj1' : j = 1
  · subst hj1'
    have e : -((((1 : ℕ) : ℝ)) + 1) = -((2 : ℕ) : ℝ) := by norm_num
    rw [e, show tol M 1 = (1 / 2) ^ (10 * M) by simp [tol], half_pow_rpow_neg]
    rw [show 10 * M * 2 = 20 * M by ring]
  · by_cases hj2 : j = 2
    · subst hj2
      have e : -((((2 : ℕ) : ℝ)) + 1) = -((3 : ℕ) : ℝ) := by norm_num
      rw [e, show tol M 2 = (1 / 2) ^ (5 * M) by simp [tol], half_pow_rpow_neg]
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    · rw [show tol M j = 1 by simp [tol, hj1', hj2], Real.one_rpow]
      exact h1M

/-- At the tolerances `Constrained.TwoPhaseExample.SlowDecay.tol M`, with $q \ge 2$, the logarithmic
term satisfies
$$|\log(\varepsilon_0 \varepsilon_{\min})| \le 10M,$$
where $\varepsilon_{\min} = \min\{1, \min_{j \in [1 : q]} \varepsilon_j\}$. Its value is
$10M \log 2$. -/
theorem abs_log_tol_le {q : ℕ} (hq : 2 ≤ q) (M : ℕ) :
    |Real.log (tol M 0 * Optimization.finMin 1 (tol M) q)| ≤ 10 * M := by
  have h0 : tol M 0 = 1 := by simp [tol]
  have h1q : 1 ∈ Finset.Icc 1 q := Finset.mem_Icc.2 ⟨le_rfl, by omega⟩
  have hmin : Optimization.finMin 1 (tol M) q = (1 / 2) ^ (10 * M) := by
    refine le_antisymm ((Optimization.finMin_le h1q).trans_eq (by simp [tol]))
      (Optimization.le_finMin (pow_le_one₀ (by norm_num) (by norm_num)) fun j hj => ?_)
    unfold tol
    split_ifs
    · exact le_rfl
    · exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    · exact pow_le_one₀ (by norm_num) (by norm_num)
  rw [h0, one_mul, hmin, Real.log_pow, one_div, Real.log_inv, abs_mul, abs_neg,
    abs_of_pos (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
  have hl := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  rw [Nat.abs_cast]
  push_cast
  have : (0 : ℝ) ≤ 10 * M := by positivity
  nlinarith

/-- **A count against a logarithmically weighted order.** Let $\kappa \in \mathbb{R}$ and
$M \in \mathbb{N}$ with $M > 20|\kappa| + 20$, let $0 \le \Lambda \le 10M$ and
$0 \le O \le 2^{20M}$, and let $N \ge 2^{22M} - 2^{18M} - 2^{10M} + 1$. Then
$$N > \kappa\,(1 + \Lambda)\,O.$$

The difference $2^{22M} - 2^{18M} - 2^{10M}$ is in natural numbers. -/
theorem not_le_of_count {κ Λ O N : ℝ} {M : ℕ} (hM : 20 * |κ| + 20 < M) (hΛ0 : 0 ≤ Λ)
    (hΛ : Λ ≤ 10 * M) (hO0 : 0 ≤ O) (hO : O ≤ 2 ^ (20 * M))
    (hN : ((2 ^ (22 * M) - 2 ^ (18 * M) - 2 ^ (10 * M) : ℕ) : ℝ) + 1 ≤ N) :
    ¬ N ≤ κ * (1 + Λ) * O := by
  have hM1 : 1 ≤ M := by
    have : (1 : ℝ) < M := by linarith [abs_nonneg κ]
    exact_mod_cast this.le
  have hR : κ * (1 + Λ) * O ≤ |κ| * (1 + 10 * M) * 2 ^ (20 * M) := by
    have hX : 0 ≤ (1 + Λ) * O := by positivity
    rw [mul_assoc, mul_assoc]
    refine (mul_le_mul_of_nonneg_right (le_abs_self κ) hX).trans
      (mul_le_mul_of_nonneg_left ?_ (abs_nonneg κ))
    exact mul_le_mul (by linarith) hO hO0 (by positivity)
  have hKs1 : 2 ^ (18 * M) ≤ 2 ^ (22 * M) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hKle : 2 ^ (18 * M) + 2 ^ (10 * M) ≤ 2 ^ (22 * M) := by
    have a1 : 2 ^ (18 * M) ≤ 2 ^ (22 * M - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have a2 : 2 ^ (10 * M) ≤ 2 ^ (22 * M - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have a3 : 2 ^ (22 * M) = 2 * 2 ^ (22 * M - 1) := by
      rw [← pow_succ']; congr 1; omega
    omega
  have hKs2 : 2 ^ (10 * M) ≤ 2 ^ (22 * M) - 2 ^ (18 * M) :=
    Nat.le_sub_of_add_le (by rw [add_comm]; exact hKle)
  rw [Nat.cast_sub hKs2, Nat.cast_sub hKs1] at hN
  push_cast at hN
  have h18 : (2 : ℝ) ^ (18 * M) * 4 ≤ 2 ^ (22 * M) := by
    rw [show 22 * M = 18 * M + 2 + (4 * M - 2) by omega, pow_add, pow_add]
    have : (1 : ℝ) ≤ 2 ^ (4 * M - 2) := one_le_pow₀ (by norm_num)
    have : (0 : ℝ) < 2 ^ (18 * M) := by positivity
    nlinarith
  have h10 : (2 : ℝ) ^ (10 * M) ≤ 2 ^ (18 * M) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hfin := mul_two_pow_lt hM
  intro h
  linarith

end Constrained.TwoPhaseExample.SlowDecay
