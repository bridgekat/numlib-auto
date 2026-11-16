/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Optimization.Constrained.TwoPhase.HighOrder.Basic
import Numlib.Optimization.Constrained.TwoPhase.HighOrder.Complexity
import Numlib.Optimization.Constrained.TargetMeritTaylor
import Numlib.Analysis.Calculus.MultivariateTaylor.Coord
import Numlib.Optimization.Optimality.CurveConditions
import Numlib.Analysis.InnerProductSpace.EuclideanProd

/-!
# A Phase-2 run that stops at once on an interval

This module gives runs of Phase 2 of the two-phase method TPqp-GC of [cartis2022evaluation],
Algorithm 14.3.2 (`Constrained.IsHighOrderTargetRun`), that terminate at the first outer iteration.
The problem is posed on $\mathbb{R}^1$ with the simple constraint set $X = [-1, 1]$ and the zero
constraint $c \equiv 0$, so that the Lagrangian is the objective and the multiplier estimate
vanishes. The stationary Phase-2 data `Constrained.TwoPhaseExample.Interval.seq` have every iterate
$0$, every target $-\varepsilon_0$, every radius $1$ and no inner iterations. For every objective
$g$ with $g(0) = 0$ for which the criticality test (14.3.34) holds at $0$ for the target
$-\varepsilon_0$, they form a run from $x_1 = 0$, and this run terminates at the first outer
iteration, in case (c), with the output target $-\varepsilon_0$.

For $\varepsilon_0 = 1/100$ and $\varepsilon_j = 1$ ($j \ge 1$), the quadratic objective
$f(x) = x/4 - \tfrac{25}{8} x^2$ passes the criticality test of order $q = 2$, and the cubic
objective $f(x) = x/12 - \tfrac{25}{72} x^2 + \tfrac{625}{216} x^3$ passes the criticality test of
order $q = 3$. Indeed $\nabla^2 \mu(0) = \nabla f(0)^2 + \varepsilon_0 \nabla^2 f(0) = 0$, and also
$\nabla^3 \mu(0) = 0$ for the cubic objective. Yet the measure $\phi_q$ of order $q$ at $0$ on
$X \cap \ker \nabla c(0)$ with radius $1$ is larger than $\tfrac12 (1 + \phi_1 \|\nabla f(0)\|)$ for
the quadratic objective and larger than $\tfrac16 (1 + 3 \phi_1 (\|\nabla f(0)\| + \|\nabla^2
f(0)\|))$ for the cubic objective, where $\phi_1$ is the first-order measure at $0$ on $X$. These
two runs refute the bounds (14.3.43) and (14.3.46) of Lemma 14.3.5 of [cartis2022evaluation]
(`CartisGouldToint.Chapter14.lemma_14_3_5_counterexample`).

## Main definitions

* `Constrained.TwoPhaseExample.Interval.interval`, `Constrained.TwoPhaseExample.Interval.con`: the
  set $X = [-1, 1]$ and the constraint $c \equiv 0$.
* `Constrained.TwoPhaseExample.Interval.seq`: the stationary Phase-2 data.
* `Constrained.TwoPhaseExample.Interval.quad`, `Constrained.TwoPhaseExample.Interval.cubic`: the
  quadratic and the cubic objective.
* `Constrained.TwoPhaseExample.Interval.tol`: the tolerances $\varepsilon_0 = 1/100$ and
  $\varepsilon_j = 1$ for $j \ge 1$.

## Main results

* `Constrained.TwoPhaseExample.Interval.isHighOrderTargetRun`: the stationary data form a run of
  Phase 2.
* `Constrained.TwoPhaseExample.Interval.isEnd_one`,
  `Constrained.TwoPhaseExample.Interval.targetOut_one`: the run terminates at the first outer
  iteration with the output target $-\varepsilon_0$.
* `Constrained.TwoPhaseExample.Interval.isEndCritContract`: its calls satisfy the end-criticality
  contract.
* `Constrained.TwoPhaseExample.Interval.targetCrit_quad`,
  `Constrained.TwoPhaseExample.Interval.targetCrit_cubic`: the criticality tests of order $2$ and
  $3$ hold at $0$.
* `Constrained.TwoPhaseExample.Interval.quad_lt_taylorMeasure_two`,
  `Constrained.TwoPhaseExample.Interval.cubic_lt_taylorMeasure_three`: the measure of order $q$
  exceeds the bound of order $q$.

## Implementation notes

* A point $x \in \mathbb{R}^1$ (`EuclideanSpace ℝ (Fin 1)`) has the single coordinate `x 0`, which
  the comments write as $x$.
* The criticality tests use the tolerances $\varepsilon_j / 2$ (`fun j => tol j * (1 / 2)`), and the
  run uses $\theta = \beta = 1/2$.
-/

open Set Metric
open scoped Nat RealInnerProductSpace
open Constrained (innerLagrangian)

namespace Constrained.TwoPhaseExample.Interval

local notation "ℝ¹" => EuclideanSpace ℝ (Fin 1)


/-- The simple constraint set $X = [-1, 1]$: the set of $x \in \mathbb{R}^1$ with $|x| \le 1$. -/
def interval : Set ℝ¹ := {x | |x 0| ≤ 1}

/-- The zero equality constraint $c \equiv 0$, with values in $\mathbb{R}^1$. -/
def con : ℝ¹ → ℝ¹ := fun _ => 0

/-- The **stationary Phase-2 data** for $\varepsilon_0 \in \mathbb{R}$: every outer iterate is $0$,
every target is $-\varepsilon_0$, every optimality radius is $1$, and every inner call makes no
iterations, so that its only iterate is its starting point $0$. -/
noncomputable def seq (ε₀ : ℝ) : HighOrderTargetSeq ℝ¹ :=
  ⟨fun _ => 0, fun _ => -ε₀, fun _ _ => 1, fun _ _ => 0, fun _ => 0, fun _ _ => False⟩

/-- Let $g : \mathbb{R}^1 \to \mathbb{R}$ satisfy $g(0) = 0$, and let $\varepsilon_0 \ge 0$. For the
objective $g$ and $c \equiv 0$, $\|r(0, -\varepsilon_0)\| = \varepsilon_0$. -/
theorem targetResidual_zero {g : ℝ¹ → ℝ} (hg0 : g 0 = 0) {ε₀ : ℝ} (hε₀ : 0 ≤ ε₀) :
    Constrained.targetResidual g con (-ε₀) 0 = ε₀ := by
  simp [Constrained.targetResidual_def, con, hg0, Real.sqrt_sq hε₀]

/-! ### The stationary run -/

section Run

variable {g : ℝ¹ → ℝ} {q : ℕ} {ε : ℕ → ℝ}

/-- Let $g(0) = 0$ and $\varepsilon_0 > 0$. No outer iteration $k$ of the stationary data is in
$\mathcal{K}_a$ for the objective $g$ and $\theta = 1/2$, since $\|r(x_{k+1}, t_k)\| =
\varepsilon_0 \ge \theta \varepsilon_0$. -/
theorem not_isKa (hg0 : g 0 = 0) (hε0 : 0 < ε 0) (k : ℕ) :
    ¬ (seq (ε 0)).IsKa g con (1 / 2) ε k := fun h => by
  simp only [HighOrderTargetSeq.isKa_iff, seq] at h
  rw [targetResidual_zero hg0 hε0.le] at h
  linarith

/-- Let $g(0) = 0$ and $\varepsilon_0 > 0$. No outer iteration $k$ of the stationary data is in
$\mathcal{K}_b$ for the objective $g$ and $\theta = 1/2$, since $g(x_{k+1}) = 0$ is not smaller
than $t_k = -\varepsilon_0$. -/
theorem not_isKb (hg0 : g 0 = 0) (hε0 : 0 < ε 0) (k : ℕ) :
    ¬ (seq (ε 0)).IsKb g con (1 / 2) ε k := fun h => by
  simp only [HighOrderTargetSeq.isKb_iff, seq, hg0] at h
  linarith [h.2]

/-- **The stationary run.** Let $g : \mathbb{R}^1 \to \mathbb{R}$ satisfy $g(0) = 0$, let
$q \in \mathbb{N}$, and let $\varepsilon_j \in (0, 1]$ for $j \in [0, q]$. Assume that the
criticality test (14.3.34) holds at $0$ for the target $-\varepsilon_0$, with the tolerances
$\varepsilon_j$ and all radii $1$. Then the stationary data
`Constrained.TwoPhaseExample.Interval.seq ε₀` form a run of Phase 2
(`Constrained.IsHighOrderTargetRun`) for the objective $g$, the constraint $c \equiv 0$ and the
set $X = [-1, 1]$, from $x_1 = 0$, with $\theta = \beta = 1/2$.

The Step-0 target is $t_1 = g(0) - \sqrt{\varepsilon_0^2 - \|c(0)\|^2} = -\varepsilon_0$, and
every call satisfies the third test of (14.3.32) by the hypothesis on the criticality test. -/
theorem isHighOrderTargetRun (hg0 : g 0 = 0) (hε : ∀ j ∈ Finset.range (q + 1), 0 < ε j)
    (hε1 : ∀ j ∈ Finset.range (q + 1), ε j ≤ 1)
    (hcrit : targetCrit g con interval q ε (-ε 0) 0 (fun _ => 1)) :
    IsHighOrderTargetRun g con interval q (1 / 2) (1 / 2) ε 0 (seq (ε 0)) := by
  have hε0 : 0 < ε 0 := hε 0 (by simp)
  have hmem0 : (0 : ℝ¹) ∈ interval := by simp [interval]
  refine ⟨by norm_num, by norm_num, by norm_num, le_rfl, hε, hε1, hmem0,
    by simp only [con, norm_zero]; positivity, rfl, ?_, fun _ _ _ => hmem0,
    fun _ _ _ _ _ => ⟨one_pos, le_rfl⟩, fun _ _ _ => Or.inr (Or.inr hcrit),
    fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ i hi => absurd hi (Nat.not_lt_zero _),
    fun _ _ _ i hi => absurd hi (Nat.not_lt_zero _),
    fun k _ _ h => absurd h (not_isKa hg0 hε0 k), fun k _ _ h => absurd h (not_isKb hg0 hε0 k)⟩
  simp [seq, con, hg0, Real.sqrt_sq hε0.le]

/-- **The stationary run stops at once.** Let $g(0) = 0$ and $\varepsilon_0 > 0$. For every $q$,
Phase 2 with the stationary data, the objective $g$ and $\theta = 1/2$ terminates at the outer
iteration $1$ (`Constrained.HighOrderTargetSeq.IsEnd`).

The outer iteration $1$ is neither in $\mathcal{K}_a$ nor in $\mathcal{K}_b$, so Phase 2 stops
in case (c). -/
theorem isEnd_one (hg0 : g 0 = 0) (hε0 : 0 < ε 0) :
    (seq (ε 0)).IsEnd g con interval q (1 / 2) ε 1 :=
  ⟨le_rfl, Or.inl ⟨not_isKa hg0 hε0 1, not_isKb hg0 hε0 1⟩, fun j h1 hj => absurd hj (by omega)⟩

/-- **The output target.** Let $g(0) = 0$ and $\varepsilon_0 > 0$. For the stationary data, the
objective $g$ and $\theta = 1/2$, the output target at the outer iteration $1$ is
$-\varepsilon_0$.

In case (c) the output target is the current target $t_1$
(`Constrained.HighOrderTargetSeq.targetOut`). -/
theorem targetOut_one (hg0 : g 0 = 0) (hε0 : 0 < ε 0) :
    (seq (ε 0)).targetOut g con (1 / 2) ε 1 = -ε 0 :=
  (HighOrderTargetSeq.targetOut_of_not (not_isKa hg0 hε0 1) (not_isKb hg0 hε0 1)).trans rfl

/-- **The end-criticality contract holds.** For every objective $g$, every $q$, all tolerances
$\varepsilon_j$, every $\kappa_{\mathrm{decr}}$ and all exponents $\pi_j$, the calls of the
stationary data satisfy the end-criticality contract
`Constrained.HighOrderTargetSeq.IsEndCritContract` with $\theta = \beta = 1/2$ and
$\kappa_{\mathrm{uns}} = \kappa_{\mathrm{unc}} = 1$.

The calls make no iterations, so the contract reduces to the count condition $e_k = 0 \le
\kappa_{\mathrm{uns}} \cdot 0 + \kappa_{\mathrm{unc}} = 1$. -/
theorem isEndCritContract (κdecr : ℝ) (π : ℕ → ℝ) :
    (seq (ε 0)).IsEndCritContract g con interval q (1 / 2) (1 / 2) ε κdecr 1 1 π :=
  ⟨fun k _ _ => by simp only [seq, Nat.cast_zero, one_mul]; positivity,
    fun k _ _ i hi => absurd hi (Nat.not_lt_zero _),
    fun k _ _ i hi => absurd hi (Nat.not_lt_zero _)⟩

end Run

/-- With $c \equiv 0$, the Lagrangian $\mathcal{L}(\cdot, y) = g - \langle y, c(\cdot) \rangle$ is
the objective $g$ for every multiplier $y \in \mathbb{R}^1$. -/
theorem innerLagrangian_con (g : ℝ¹ → ℝ) (y : ℝ¹) : innerLagrangian g con y = g := by
  funext x; simp [con]

/-- With $c \equiv 0$, the multiplier estimate $-c(0)/(g(0) - t)$ at $0$ is $0$ for every objective
$g$ and every target $t$. -/
theorem targetMultiplier_con (g : ℝ¹ → ℝ) (t : ℝ) :
    Constrained.targetMultiplier g con t 0 = 0 := by
  simp [Constrained.targetMultiplier_def, con]

/-- The derivative of $c \equiv 0$ at $0$ is zero. -/
theorem fderiv_con : fderiv ℝ con 0 = 0 := by
  unfold con; simp

private theorem contDiff_coord : ContDiff ℝ ⊤ (fun x : ℝ¹ => x 0) := contDiff_piLp_apply (p := 2)

private theorem abs_le_one_of_mem_closedBall {d : ℝ¹} (hd : d ∈ closedBall (0 : ℝ¹) 1) :
    |d 0| ≤ 1 := by
  rw [← EuclideanSpace.norm_eq_abs_fin_one]; exact mem_closedBall_zero_iff.1 hd

/-- Let $g : \mathbb{R}^1 \to \mathbb{R}$ and $A \in \mathbb{R}$ satisfy $\nabla g(0)[d] = A d$ for
all $d$. The first-order measure of $g$ at $0$ on $X(0) = \{d : 0 + d \in X\}$ with radius $1$
is at most $|A|$. -/
theorem taylorMeasure_one_le {g : ℝ¹ → ℝ} {A : ℝ} (hA : ∀ d, fderiv ℝ g 0 d = A * d 0) :
    Optimization.taylorMeasure (ftaylorSeries ℝ g 0) 1 1 {d | 0 + d ∈ interval} ≤ |A| := by
  rw [Optimization.taylorMeasure]
  refine Optimization.decrementMeasure_le ⟨0, mem_closedBall_self zero_le_one, by simp [interval]⟩
    fun d hd => ?_
  rw [FormalMultilinearSeries.taylorDecrement_one_apply]
  simp only [ftaylorSeries, iteratedFDeriv_one_apply, hA]
  have := abs_le_one_of_mem_closedBall hd.1
  calc -(A * d 0) ≤ |A * d 0| := neg_le_abs _
    _ = |A| * |d 0| := abs_mul _ _
    _ ≤ |A| * 1 := mul_le_mul_of_nonneg_left this (abs_nonneg _)
    _ = |A| := mul_one _

/-- Let $g : \mathbb{R}^1 \to \mathbb{R}$ and $A \in \mathbb{R}$ satisfy $\nabla g(0)[d] = A d$ for
all $d$. Then $\|\nabla g(0)\| \le |A|$. -/
theorem norm_fderiv_le {g : ℝ¹ → ℝ} {A : ℝ} (hA : ∀ d, fderiv ℝ g 0 d = A * d 0) :
    ‖fderiv ℝ g 0‖ ≤ |A| := by
  refine (EuclideanSpace.norm_clm_fin_one_le _).trans ?_
  simp [hA]

/-! ### The quadratic objective, $q = 2$ -/

/-- The **quadratic objective** $f(x) = x/4 - \tfrac{25}{8} x^2$ on $\mathbb{R}^1$.

Its derivatives at $0$ are $\nabla f(0) = 1/4$ and $\nabla^2 f(0) = -25/4$. -/
noncomputable def quad : ℝ¹ → ℝ := fun x => x 0 / 4 - 25 / 8 * x 0 ^ 2

/-- The **tolerances** $\varepsilon_0 = 1/100$ and $\varepsilon_j = 1$ for $j \ge 1$. -/
noncomputable def tol : ℕ → ℝ := fun j => if j = 0 then 1 / 100 else 1

/-- $\varepsilon_0 = 1/100$. -/
theorem tol_zero : tol 0 = 1 / 100 := rfl

/-- $\varepsilon_j = 1$ for $j \ne 0$. -/
theorem tol_of_ne {j : ℕ} (hj : j ≠ 0) : tol j = 1 := by simp [tol, hj]

/-- The tolerances are positive: $\varepsilon_j > 0$ for every $j$. -/
theorem tol_pos (j : ℕ) : 0 < tol j := by unfold tol; split_ifs <;> norm_num

/-- The tolerances are at most $1$: $\varepsilon_j \le 1$ for every $j$. -/
theorem tol_le_one (j : ℕ) : tol j ≤ 1 := by unfold tol; split_ifs <;> norm_num

/-- The quadratic objective is of class $C^\omega$ (analytic), which is `ContDiff ℝ ⊤`. -/
theorem contDiff_quad : ContDiff ℝ ⊤ quad :=
  (contDiff_coord.div_const 4).sub (contDiff_const.mul (contDiff_coord.pow 2))

private theorem quad_ray (d : ℝ¹) (s : ℝ) :
    quad (0 + s • d) = quad 0 + ∑ i ∈ Finset.Icc 1 2,
      s ^ i * (if i = 1 then d 0 / 4 else -(25 / 8) * d 0 ^ 2) := by
  simp [quad, Finset.sum_Icc_succ_top]
  ring

/-- For the quadratic objective, $\nabla f(0)[d] = d/4$ for all $d$. -/
theorem fderiv_quad (d : ℝ¹) : fderiv ℝ quad 0 d = 1 / 4 * d 0 := by
  have := Optimization.iteratedFDeriv_apply_diag_eq_of_poly (N := 2)
    (contDiff_quad.contDiffAt.of_le le_top) (Filter.Eventually.of_forall (quad_ray d)) 1
    (by simp)
  rw [iteratedFDeriv_one_apply] at this
  rw [this]; simp; ring

/-- A sufficient condition for the criticality test (14.3.34) at $0$ for the target $-1/100$ with
the tolerances $\varepsilon_j/2$ and the radii $1$: $g(0) = 0$, $g$ is analytic,
$\mu(\cdot, -1/100) = (g + 1/100)^2/2$ is a polynomial of degree $N \ge q$ along every ray with
coefficients $a_d(i)$, and the partial sums $-\sum_{i=1}^j a_d(i)$ are at most
$\varepsilon_j \varepsilon_0 / (2 \cdot j!)$ for $|d| \le 1$ and $j \in [1, q]$. -/
private theorem targetCrit_of_poly {g : ℝ¹ → ℝ} (hg0 : g 0 = 0) (hg : ContDiff ℝ ⊤ g)
    {q N : ℕ} (hqN : q ≤ N) (a : ℝ¹ → ℕ → ℝ)
    (hpoly : ∀ (d : ℝ¹) (s : ℝ), (g (0 + s • d) + 1 / 100) ^ 2 / 2 =
      (g 0 + 1 / 100) ^ 2 / 2 + ∑ i ∈ Finset.Icc 1 N, s ^ i * a d i)
    (hle : ∀ d : ℝ¹, |d 0| ≤ 1 → ∀ j ∈ Finset.Icc 1 q,
      -∑ i ∈ Finset.Icc 1 j, a d i ≤ tol j * (1 / 2) * tol 0 * 1 ^ j / j !) :
    targetCrit g con interval q (fun j => tol j * (1 / 2)) (-tol 0) 0 (fun _ => 1) := by
  intro j hj
  have he : Constrained.targetMerit g con (-tol 0) = fun x => (g x + 1 / 100) ^ 2 / 2 := by
    funext x; simp [Constrained.targetMerit_def, con, tol_zero]
  have hsm : ContDiffAt ℝ N (Constrained.targetMerit g con (-tol 0)) 0 := by
    rw [he]
    exact (((hg.add contDiff_const).pow 2).div_const 2).contDiffAt.of_le le_top
  rw [Optimization.taylorMeasure]
  refine Optimization.decrementMeasure_le ⟨0, mem_closedBall_self zero_le_one, by simp [interval]⟩
    fun d hd => ?_
  rw [Optimization.taylorDecrement_eq_of_poly (a := a d) hsm (fun s => by rw [he]; exact hpoly d s)
      ((Finset.mem_Icc.1 hj).2.trans hqN), targetResidual_zero hg0 (tol_pos 0).le]
  exact hle d (abs_le_one_of_mem_closedBall hd.1) j hj

/-- **The criticality test of order $2$ holds for the quadratic objective.** For the quadratic
objective $f$, the constraint $c \equiv 0$ and $X = [-1, 1]$, the criticality test (14.3.34) of
order $q = 2$ holds at $0$ for the target $-\varepsilon_0 = -1/100$, with the tolerances
$\varepsilon_j / 2$ and all radii $1$.

At $0$ one has $\nabla \mu(0) = (f(0) + \varepsilon_0) \nabla f(0) = 1/400$ and $\nabla^2
\mu(0) = \nabla f(0)^2 + \varepsilon_0 \nabla^2 f(0) = 1/16 - 1/16 = 0$. -/
theorem targetCrit_quad :
    targetCrit quad con interval 2 (fun j => tol j * (1 / 2)) (-tol 0) 0 (fun _ => 1) :=
  targetCrit_of_poly (by simp [quad]) contDiff_quad (N := 4) (by norm_num)
    (fun d i => if i = 1 then d 0 / 400 else if i = 2 then 0 else
      if i = 3 then -(25 / 32) * d 0 ^ 3 else 625 / 128 * d 0 ^ 4)
    (fun d s => by simp [quad, Finset.sum_Icc_succ_top]; ring) fun d hd j hj => by
      rw [abs_le] at hd
      obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hj
      interval_cases j <;> simp [Finset.sum_Icc_succ_top, tol] <;> linarith

private theorem neg_single_mem :
    -EuclideanSpace.single (0 : Fin 1) (1 : ℝ) ∈
      closedBall (0 : ℝ¹) 1 ∩ ({d | 0 + d ∈ interval} ∩ {d | fderiv ℝ con 0 d = 0}) := by
  refine ⟨mem_closedBall_zero_iff.2 (by simp), by simp [interval],
    by simp [fderiv_con]⟩

/-- For every $g : \mathbb{R}^1 \to \mathbb{R}$, the first-order measure of $g$ at $0$ on $X(0)$
with radius $1$ is nonnegative. -/
theorem taylorMeasure_one_nonneg (g : ℝ¹ → ℝ) :
    0 ≤ Optimization.taylorMeasure (ftaylorSeries ℝ g 0) 1 1 {d | 0 + d ∈ interval} :=
  Optimization.taylorMeasure_nonneg _ 1 (by simp [interval]) zero_le_one

/-- The second-order measure of the quadratic objective at $0$ on $X(0) \cap \ker \nabla c(0)$ with
radius $1$ is at least $27/8$, the decrease $1/4 + 25/8$ along $d = -1$. -/
theorem le_taylorMeasure_two_quad :
    27 / 8 ≤ Optimization.taylorMeasure (ftaylorSeries ℝ quad 0) 2 1
    ({d | 0 + d ∈ interval} ∩ {d | fderiv ℝ con 0 d = 0}) := by
  refine le_trans ?_ (Optimization.taylorDecrement_le_taylorMeasure _ 2 neg_single_mem)
  rw [Optimization.taylorDecrement_eq_of_poly (N := 2) (contDiff_quad.contDiffAt.of_le le_top)
    (quad_ray _) le_rfl]
  simp [Finset.sum_Icc_succ_top]
  norm_num

/-! ### The cubic objective, $q = 3$ -/

/-- The **cubic objective** $f(x) = x/12 - \tfrac{25}{72} x^2 + \tfrac{625}{216} x^3$ on
$\mathbb{R}^1$.

Its derivatives at $0$ are $\nabla f(0) = 1/12$, $\nabla^2 f(0) = -25/36$ and
$\nabla^3 f(0) = 625/36$. -/
noncomputable def cubic : ℝ¹ → ℝ := fun x => x 0 / 12 - 25 / 72 * x 0 ^ 2 + 625 / 216 * x 0 ^ 3

/-- The cubic objective is of class $C^\omega$ (analytic), which is `ContDiff ℝ ⊤`. -/
theorem contDiff_cubic : ContDiff ℝ ⊤ cubic :=
  ((contDiff_coord.div_const 12).sub (contDiff_const.mul (contDiff_coord.pow 2))).add
    (contDiff_const.mul (contDiff_coord.pow 3))

private theorem cubic_ray (d : ℝ¹) (s : ℝ) :
    cubic (0 + s • d) = cubic 0 + ∑ i ∈ Finset.Icc 1 3,
      s ^ i * (if i = 1 then d 0 / 12 else if i = 2 then -(25 / 72) * d 0 ^ 2
        else 625 / 216 * d 0 ^ 3) := by
  simp [cubic, Finset.sum_Icc_succ_top]
  ring

/-- For the cubic objective, $\nabla f(0)[d] = d/12$ for all $d$. -/
theorem fderiv_cubic (d : ℝ¹) : fderiv ℝ cubic 0 d = 1 / 12 * d 0 := by
  have := Optimization.iteratedFDeriv_apply_diag_eq_of_poly (N := 3)
    (contDiff_cubic.contDiffAt.of_le le_top) (Filter.Eventually.of_forall (cubic_ray d)) 1
    (by simp)
  rw [iteratedFDeriv_one_apply] at this
  rw [this]; simp; ring

/-- For the cubic objective, $\|\nabla^2 f(0)\| \le 25/36$. -/
theorem norm_iteratedFDeriv_two_cubic_le : ‖iteratedFDeriv ℝ 2 cubic 0‖ ≤ 25 / 36 := by
  refine (EuclideanSpace.norm_multilinear_fin_one_le _).trans ?_
  rw [Optimization.iteratedFDeriv_apply_diag_eq_of_poly (N := 3)
    (contDiff_cubic.contDiffAt.of_le le_top) (Filter.Eventually.of_forall (cubic_ray _)) 2
    (by simp)]
  simp [Nat.factorial]
  norm_num

/-- **The criticality test of order $3$ holds for the cubic objective.** For the cubic objective
$f$, the constraint $c \equiv 0$ and $X = [-1, 1]$, the criticality test (14.3.34) of order
$q = 3$ holds at $0$ for the target $-\varepsilon_0 = -1/100$, with the tolerances
$\varepsilon_j / 2$ and all radii $1$.

At $0$ one has $\nabla^2 \mu(0) = \nabla f(0)^2 + \varepsilon_0 \nabla^2 f(0) = 0$ and $\nabla^3
\mu(0) = 3 \nabla f(0) \nabla^2 f(0) + \varepsilon_0 \nabla^3 f(0) = 0$. -/
theorem targetCrit_cubic :
    targetCrit cubic con interval 3 (fun j => tol j * (1 / 2)) (-tol 0) 0 (fun _ => 1) :=
  targetCrit_of_poly (by simp [cubic]) contDiff_cubic (N := 6) (by norm_num)
    (fun d i => if i = 1 then d 0 / 1200 else if i = 2 then 0 else if i = 3 then 0 else
      if i = 4 then 3125 / 10368 * d 0 ^ 4 else if i = 5 then -(15625 / 15552) * d 0 ^ 5 else
      390625 / 93312 * d 0 ^ 6)
    (fun d s => by simp [cubic, Finset.sum_Icc_succ_top]; ring) fun d hd j hj => by
      rw [abs_le] at hd
      obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hj
      interval_cases j <;> simp [Finset.sum_Icc_succ_top, tol, Nat.factorial] <;> linarith

/-- The third-order measure of the cubic objective at $0$ on $X(0) \cap \ker \nabla c(0)$ with
radius $1$ is at least $718/216$, the decrease along $d = -1$. -/
theorem le_taylorMeasure_three_cubic :
    718 / 216 ≤ Optimization.taylorMeasure (ftaylorSeries ℝ cubic 0) 3 1
    ({d | 0 + d ∈ interval} ∩ {d | fderiv ℝ con 0 d = 0}) := by
  refine le_trans ?_ (Optimization.taylorDecrement_le_taylorMeasure _ 3 neg_single_mem)
  rw [Optimization.taylorDecrement_eq_of_poly (N := 3) (contDiff_cubic.contDiffAt.of_le le_top)
    (cubic_ray _) le_rfl]
  simp [Finset.sum_Icc_succ_top]
  norm_num

/-- The set $X$ lies in the open ball $B(0, 2)$. -/
theorem interval_subset_ball : interval ⊆ ball (0 : ℝ¹) 2 := fun x hx => by
  rw [mem_ball_zero_iff, EuclideanSpace.norm_eq_abs_fin_one]
  exact lt_of_le_of_lt hx (by norm_num)

/-! ### The measure inequalities -/

/-- **The second-order measure exceeds the bound of order $2$.** For the quadratic objective $f$,
$$\tfrac12 \bigl(1 + \phi_1 \|\nabla f(0)\|\bigr) < \phi_2,$$
where $\phi_1$ is the first-order measure of $f$ at $0$ on $X(0) = \{d : 0 + d \in X\}$ with
radius $1$, and $\phi_2$ is the second-order measure of $f$ at $0$ on
$X(0) \cap \ker \nabla c(0)$ with radius $1$.

The left side is at most $\tfrac12 (1 + 1/16) = 17/32$, since $\phi_1 \le 1/4$ and
$\|\nabla f(0)\| \le 1/4$, while $\phi_2 \ge 27/8$. The left side is the right-hand side of
(14.3.43) of [cartis2022evaluation] for $\varepsilon_2 = 1$, the multiplier $0$ and the radius
$1$. -/
theorem quad_lt_taylorMeasure_two :
    (1 + Optimization.taylorMeasure (ftaylorSeries ℝ quad 0) 1 1 {d | 0 + d ∈ interval} *
        ‖fderiv ℝ quad 0‖) / 2 <
      Optimization.taylorMeasure (ftaylorSeries ℝ quad 0) 2 1
        ({d | 0 + d ∈ interval} ∩ {d | fderiv ℝ con 0 d = 0}) := by
  have h1 := taylorMeasure_one_le fderiv_quad
  have h2 := norm_fderiv_le fderiv_quad
  have h0 := taylorMeasure_one_nonneg quad
  have hl := le_taylorMeasure_two_quad
  rw [abs_of_pos (by norm_num)] at h1 h2
  have : Optimization.taylorMeasure (ftaylorSeries ℝ quad 0) 1 1 {d | 0 + d ∈ interval} *
      ‖fderiv ℝ quad 0‖ ≤ 1 / 4 * (1 / 4) := mul_le_mul h1 h2 (norm_nonneg _) (by norm_num)
  linarith

/-- **The third-order measure exceeds the bound of order $3$.** For the cubic objective $f$,
$$\tfrac16 \bigl(1 + 3 \phi_1 (\|\nabla f(0)\| + \|\nabla^2 f(0)\|)\bigr) < \phi_3,$$
where $\phi_1$ is the first-order measure of $f$ at $0$ on $X(0) = \{d : 0 + d \in X\}$ with
radius $1$, and $\phi_3$ is the third-order measure of $f$ at $0$ on
$X(0) \cap \ker \nabla c(0)$ with radius $1$.

The left side is at most $\tfrac16 (1 + 3 \cdot \tfrac1{12} (\tfrac1{12} + \tfrac{25}{36})) =
43/216$, while $\phi_3 \ge 718/216$. The left side is the right-hand side of (14.3.46) of
[cartis2022evaluation] for $\varepsilon_3 = 1$, the multiplier $0$ and the radius $1$. -/
theorem cubic_lt_taylorMeasure_three :
    (1 + 3 * Optimization.taylorMeasure (ftaylorSeries ℝ cubic 0) 1 1 {d | 0 + d ∈ interval} *
        (‖fderiv ℝ cubic 0‖ + ‖iteratedFDeriv ℝ 2 cubic 0‖)) / 6 <
      Optimization.taylorMeasure (ftaylorSeries ℝ cubic 0) 3 1
        ({d | 0 + d ∈ interval} ∩ {d | fderiv ℝ con 0 d = 0}) := by
  have h1 := taylorMeasure_one_le fderiv_cubic
  have h2 := norm_fderiv_le fderiv_cubic
  have h3 := norm_iteratedFDeriv_two_cubic_le
  have h0 := taylorMeasure_one_nonneg cubic
  have hl := le_taylorMeasure_three_cubic
  rw [abs_of_pos (by norm_num)] at h1 h2
  have : Optimization.taylorMeasure (ftaylorSeries ℝ cubic 0) 1 1 {d | 0 + d ∈ interval} *
      (‖fderiv ℝ cubic 0‖ + ‖iteratedFDeriv ℝ 2 cubic 0‖) ≤ 1 / 12 * (1 / 12 + 25 / 36) :=
    mul_le_mul h1 (by linarith) (by positivity) (by norm_num)
  nlinarith

end Constrained.TwoPhaseExample.Interval
