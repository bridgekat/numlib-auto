/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Optimization.LogBarrier
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Tactic.FinCases

/-!
# Conn, Gould and Toint, Section 13.1: the logarithmic barrier

This module formalizes the logarithmic barrier method of Section 13.1 of [conn2000trust]. For a
barrier parameter $\mu > 0$ the barrier objective is $f(x) - \mu \sum_i \log x_i$ on the positive
orthant, and the outer iteration of Algorithm 13.1.1 minimizes it approximately for a sequence of
parameters $\mu_k \to 0$. The module records the outer iteration, the barrier term (13.1.2) and the
barrier objective (13.1.1), and it decides when the logarithmic barrier satisfies assumption AC.8:
the barrier tends to $+\infty$ along sequences that approach the boundary. The divergence result
specializes `Optimization.tendsto_logBarrier_of_bounded_of_infDist_frontier` from
`Numlib.Optimization.LogBarrier`.

## Main definitions

* Algorithm 13.1.1, `ConnGouldToint.Chapter13.BarrierOuterRun`: an infinite run of the outer barrier
  iteration, with each inner minimization given by a solver relation.
* Equation (13.1.2), `ConnGouldToint.Chapter13.logBarrier`: the barrier term $-\mu \sum_i \log x_i$.
* Equation (13.1.1), `ConnGouldToint.Chapter13.logBarrierObjective`: the barrier objective
  $f(x) - \mu \sum_i \log x_i$.

## Main results

* Algorithm 13.1.1, `ConnGouldToint.Chapter13.BarrierOuterRun.interior_iterate`: every outer iterate
  lies in the relative interior of the feasible set.
* AC.8 for (13.1.2), `ConnGouldToint.Chapter13.logBarrier_boundary_divergence`: along a sequence of
  positive vectors with bounded coordinates whose distance to the boundary of the orthant tends to
  zero, the barrier term tends to $+\infty$.
* `ConnGouldToint.Chapter13.logBarrier_unbounded_boundary_counterexample`: without the bound on the
  coordinates, the barrier term can stay equal to $0$ while the distance to the boundary tends to
  zero.

## Deviations from the source

* **Algorithm 13.1.1** (generalization). An inner run may stop at index $0$ when its starting point
  already passes the stopping test, while the text uses a positive terminal index. See
  `ConnGouldToint.Chapter13.BarrierOuterRun`.
* **AC.8 for the logarithmic barrier** (correction). The source states that (13.1.2) satisfies AC.8.
  This holds only along sequences with bounded coordinates, because a coordinate that tends to
  infinity can cancel the logarithm of a coordinate that tends to zero. See
  `ConnGouldToint.Chapter13.logBarrier_boundary_divergence` and
  `ConnGouldToint.Chapter13.logBarrier_unbounded_boundary_counterexample`.
-/

open Filter Metric
open scoped BigOperators Topology

namespace ConnGouldToint.Chapter13

/-- **Algorithm 13.1.1** of [conn2000trust] (outer barrier iteration). Let $E$ be a real vector
space with a topology, let $C \subseteq E$, let $\varphi(x, \mu)$ be a barrier objective, and
let `solves` be a relation that says when a finite sequence $y_0, \dots, y_N$ is an accepted
inner run for the parameter $\mu$ and the objective $y \mapsto \varphi(y, \mu)$. A run of the
algorithm consists of outer iterates $x_k$, parameters $\mu_k$, inner runs $(y_{k,j})_j$ and
terminal indices $N_k$ such that $x_0$ lies in the relative interior $\operatorname{ri} C$,
$\mu_k > 0$ and $\mu_k \to 0$, each inner run starts in $\operatorname{ri} C$, is accepted by
`solves` for $\mu_k$ and ends at a point $y_{k,N_k} \in \operatorname{ri} C$, and
$x_{k+1} = y_{k,N_k}$.

**Generalization.** The text uses a positive terminal index for the inner runs. Here an inner
run may stop at index $N_k = 0$ when its starting point already passes the stopping test.

The relative interior is `intrinsicInterior ℝ C`. The starting point $y_{k,0}$ of an inner run
can be chosen independently of the previous outer iterate $x_k$. -/
structure BarrierOuterRun {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    (C : Set E) (φ : E → ℝ → ℝ)
    (solves : ℝ → (E → ℝ) → (ℕ → E) → ℕ → Prop) where
  /-- The outer iterates $x_k$. -/
  x : ℕ → E
  /-- The barrier parameters $\mu_k$. -/
  μ : ℕ → ℝ
  /-- The inner iterates: `inner k j` is the point $y_{k,j}$ of the $k$-th inner run. -/
  inner : ℕ → ℕ → E
  /-- The terminal index $N_k$ of the $k$-th inner run. -/
  stopIndex : ℕ → ℕ
  /-- The initial point $x_0$ lies in the relative interior of $C$. -/
  initial_interior : x 0 ∈ intrinsicInterior ℝ C
  /-- Each barrier parameter $\mu_k$ is positive. -/
  parameter_pos : ∀ k, 0 < μ k
  /-- The barrier parameters tend to zero. -/
  parameter_limit : Tendsto μ atTop (𝓝 0)
  /-- Each inner run starts in the relative interior of $C$. -/
  inner_start_interior : ∀ k, inner k 0 ∈ intrinsicInterior ℝ C
  /-- The $k$-th inner run, stopped at index $N_k$, is accepted by the solver relation for the
  parameter $\mu_k$ and the objective $y \mapsto \varphi(y, \mu_k)$. -/
  inner_solved : ∀ k, solves (μ k) (fun y ↦ φ y (μ k)) (inner k) (stopIndex k)
  /-- The terminal point $y_{k,N_k}$ of each inner run lies in the relative interior of $C$. -/
  inner_finish_interior : ∀ k, inner k (stopIndex k) ∈ intrinsicInterior ℝ C
  /-- The next outer iterate is the terminal point of the inner run: $x_{k+1} = y_{k,N_k}$. -/
  outer_update : ∀ k, x (k + 1) = inner k (stopIndex k)

/-- **Algorithm 13.1.1** of [conn2000trust], feasibility of the output. In a run of Algorithm 13.1.1
on the set $C$, every outer iterate $x_k$ lies in the relative interior of $C$.

The case $k = 0$ is a field of the run, and the case $k + 1$ follows from the update
$x_{k+1} = y_{k,N_k}$. -/
theorem BarrierOuterRun.interior_iterate {E : Type*} [TopologicalSpace E] [AddCommGroup E]
    [Module ℝ E]
    {C : Set E} {φ : E → ℝ → ℝ} {solves : ℝ → (E → ℝ) → (ℕ → E) → ℕ → Prop}
    (r : BarrierOuterRun C φ solves) (k : ℕ) : r.x k ∈ intrinsicInterior ℝ C := by
  cases k with
  | zero => exact r.initial_interior
  | succ k =>
    rw [r.outer_update]
    exact r.inner_finish_interior k

/-- **Equation (13.1.2)** of [conn2000trust]. For $x \in \mathbb{R}^n$ and $\mu \in \mathbb{R}$, the
**logarithmic barrier term** is
$$-\mu \sum_{i=1}^n \log x_i.$$

The definition is `Optimization.logBarrier μ x`. It is meant for vectors with positive
coordinates. At other vectors it uses the Mathlib convention for `Real.log`: $\log 0 = 0$ and
$\log x = \log |x|$ for $x < 0$. -/
noncomputable abbrev logBarrier {ι : Type*} [Fintype ι] (x : ι → ℝ) (μ : ℝ) : ℝ :=
  Optimization.logBarrier μ x

/-- **Equation (13.1.1)** of [conn2000trust]. For an objective $f : \mathbb{R}^n \to \mathbb{R}$, a
point $x$ and a parameter $\mu$, the **logarithmic barrier objective** is
$$f(x) - \mu \sum_{i=1}^n \log x_i,$$
the sum of $f$ and the barrier term `ConnGouldToint.Chapter13.logBarrier`. -/
noncomputable def logBarrierObjective {ι : Type*} [Fintype ι]
    (f : (ι → ℝ) → ℝ) (x : ι → ℝ) (μ : ℝ) : ℝ :=
  f x + logBarrier x μ

/-- **Section 13.1** of [conn2000trust], assumption AC.8 for the logarithmic barrier (13.1.2). Let
$n \ge 1$, $\mu > 0$ and $M \in \mathbb{R}$. Let $(x_j)$ be a sequence in $\mathbb{R}^n$ with
$0 < (x_j)_i \le M$ for all $j$ and $i$, and suppose that the distance from $x_j$ to the
boundary of the nonnegative orthant tends to zero. Then
$$-\mu \sum_{i=1}^n \log (x_j)_i \to +\infty.$$

**Correction.** The source states that (13.1.2) satisfies AC.8 for all sequences of positive
vectors that approach the boundary. This fails without the bound $M$ on the coordinates. See
`ConnGouldToint.Chapter13.logBarrier_unbounded_boundary_counterexample`.

The boundary is `frontier (Optimization.nonnegativeOrthant ι)`, and the distance is
`Metric.infDist` for the supremum norm. The proof specializes
`Optimization.tendsto_logBarrier_of_bounded_of_infDist_frontier`. -/
theorem logBarrier_boundary_divergence {ι : Type*} [Fintype ι] [Nonempty ι]
    {μ M : ℝ} (hμ : 0 < μ) {x : ℕ → ι → ℝ}
    (hx : ∀ n i, 0 < x n i) (hbounded : ∀ n i, x n i ≤ M)
    (ht : Tendsto (fun n ↦ infDist (x n) (frontier (Optimization.nonnegativeOrthant ι)))
      atTop (𝓝 0)) :
    Tendsto (fun n ↦ logBarrier (x n) μ) atTop atTop :=
  Optimization.tendsto_logBarrier_of_bounded_of_infDist_frontier hμ hx hbounded ht

/-- **Section 13.1** of [conn2000trust], counterexample to AC.8 for the logarithmic barrier
(13.1.2). There is a sequence $(x_j)$ in $\mathbb{R}^2$ with positive coordinates whose distance
to the boundary of the nonnegative orthant tends to zero, such that the barrier term with
$\mu = 1$ satisfies $-\log (x_j)_1 - \log (x_j)_2 = 0$ for every $j$. In particular the barrier
term does not tend to $+\infty$.

The sequence is $x_j = (1/(j+1), j+1)$: the second coordinate tends to infinity and cancels the
logarithm of the first coordinate, which tends to zero. -/
theorem logBarrier_unbounded_boundary_counterexample :
    ∃ x : ℕ → Fin 2 → ℝ, (∀ n i, 0 < x n i) ∧
      Tendsto (fun n ↦ infDist (x n) (frontier (Optimization.nonnegativeOrthant (Fin 2))))
        atTop (𝓝 0) ∧
      (∀ n, logBarrier (x n) 1 = 0) ∧
      ¬ Tendsto (fun n ↦ logBarrier (x n) 1) atTop atTop := by
  let x (n : ℕ) (i : Fin 2) := if i = 0 then 1 / ((n : ℝ) + 1) else (n : ℝ) + 1
  let y (n : ℕ) (i : Fin 2) := if i = 0 then (0 : ℝ) else (n : ℝ) + 1
  have hy (n : ℕ) : y n ∈ frontier (Optimization.nonnegativeOrthant (Fin 2)) := by
    apply Optimization.mem_frontier_nonnegativeOrthant.mpr
    refine ⟨fun i ↦ ?_, 0, by simp [y]⟩
    by_cases hi : i = 0
    · simpa only [y, ite_eq_left hi] using (le_rfl : (0 : ℝ) ≤ 0)
    · simpa only [y, ite_eq_right hi] using (show 0 ≤ (n : ℝ) + 1 by positivity)
  have hdist (n : ℕ) : infDist (x n) (frontier (Optimization.nonnegativeOrthant (Fin 2))) ≤
      1 / ((n : ℝ) + 1) := by
    refine (infDist_le_dist_of_mem (hy n)).trans ((dist_pi_le_iff (by positivity)).mpr ?_)
    intro i
    fin_cases i
    · change dist (1 / ((n : ℝ) + 1)) 0 ≤ _
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
    · change dist ((n : ℝ) + 1) ((n : ℝ) + 1) ≤ _
      rw [dist_self]
      positivity
  have hb (n : ℕ) : logBarrier (x n) 1 = 0 := by
    simp [Optimization.logBarrier, Fin.sum_univ_two, x]
  refine ⟨x, fun n i ↦ ?_, ?_, hb, ?_⟩
  · by_cases hi : i = 0
    · simpa only [x, ite_eq_left hi] using (show 0 < 1 / ((n : ℝ) + 1) by positivity)
    · simpa only [x, ite_eq_right hi] using (show 0 < (n : ℝ) + 1 by positivity)
  · exact squeeze_zero' (Eventually.of_forall fun _ ↦ infDist_nonneg)
      (Eventually.of_forall hdist) tendsto_one_div_add_atTop_nhds_zero_nat
  · intro h
    obtain ⟨n, hn⟩ := (Filter.tendsto_atTop.mp h (1 : ℝ)).exists
    rw [hb] at hn
    norm_num at hn

end ConnGouldToint.Chapter13
