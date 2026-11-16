/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Optimization.Constrained.TwoPhase.HighOrder.Examples.Box
import Numlib.Optimization.ModelBased.HighOrder.ARqpCCall
import Numlib.Optimization.Optimality.CurveConditions
import Numlib.Analysis.InnerProductSpace.NormPowIteratedFDeriv

/-!
# A Phase-2 run with ARqp inner calls on the square

This module gives runs of Phase 2 of the two-phase method TPqp-GC of [cartis2022evaluation],
Algorithm 14.3.2 (`Constrained.IsHighOrderTargetRun`), whose inner calls are calls of the
adaptive-regularization method ARqp, and which take about $(\varepsilon_0 \varepsilon_1)^{-1}$
evaluations. The problem is that of
`Numlib.Optimization.Constrained.TwoPhase.HighOrder.Examples.Box` with the objective
$f(x) = x_1 - x_2/16$, the constraint $c(x) = x_1^2/2$ and the set $X = [-1, 1]^2$. The merit
function $\mu(x, t) = \tfrac12 \|r(x, t)\|^2 = x_1^4/8 + (f(x) - t)^2/2$ is a quartic polynomial, so
its Taylor models of degree $p \ge 4$ are exact, and every ratio of an adaptive-regularization step
is $1$. The run shows that Theorem 14.3.9 of [cartis2022evaluation] fails for runs of ARqp-SC that
re-initialise, at every Step 2, the parameter of Step 2.1 of Algorithm 14.1.2, when $q \in \{1, 2\}$
and $p \ge q + 3$ (`CartisGouldToint.Chapter14.theorem_14_3_9_arqp_counterexample`).

Let $u > 0$ be small and let $M \ge 1$ satisfy $u^3 M \le 1/64$. The tolerances are
$\varepsilon_0 = u^2/2 + u^3/2$, $\varepsilon_1 = 3u/2$ and $\varepsilon_j = 1$ for $j \ge 2$, and
the constants are $\theta = \beta = 1/2$. Phase 2 starts at $x_1 = (0, 0)$ and has $M + 1$ outer
iterations. Each outer iteration is a single successful iteration of ARqp (ARqpC with $c = 0$ and
$h = 0$, `Optimization.IsARqpCallOut`), whose step is an approximate critical point of the
regularized model with a small model decrease. The first call moves to a point $(u, \cdot)$. The
next $M - 1$ calls move along $x_2$ to points with $f(x_{k+1}) = t_k - E_k$, where $E_k \approx
u^3/2 \approx 2 \varepsilon_0 \varepsilon_1 / 3$; these are case-(b) iterations, and the criticality
test (14.3.34) fails after the target update. The last call reaches a point $(-3u/4, \cdot)$, where
the criticality test holds with $f > t$. The number of evaluations, $M + 2$, is of order
$(\varepsilon_0 \varepsilon_1)^{-1}$. With $u = 1/(4N^5)$ and $M = N^{15}$ it exceeds $C
\max[\varepsilon_0^{-1}, \max_j \varepsilon_0^{1-\pi_j} \varepsilon_j^{-\pi_j}]$ for the exponents
$\pi_j = j(p+1)/p$, $q \in \{1, 2\}$ and $p \ge q + 3$, when $N$ is large compared with $C$.

## Main definitions

* `Constrained.TwoPhaseExample.stepIter`: the iterates $x, x + s, x + s, \dots$ of a call that makes
  one step.
* `Constrained.TwoPhaseExample.BoxARqp.params`: the adaptive-regularization constants.
* `Constrained.TwoPhaseExample.BoxARqp.tol`, `Constrained.TwoPhaseExample.BoxARqp.target`,
  `Constrained.TwoPhaseExample.BoxARqp.iter`, `Constrained.TwoPhaseExample.BoxARqp.seq`: the
  tolerances, the targets, the outer iterates and the Phase-2 data of the run.

## Main results

* `Constrained.TwoPhaseExample.isARqpCallOut_one_step`: sufficient conditions for a one-step call of
  ARqp.
* `Constrained.TwoPhaseExample.BoxARqp.taylorSum_targetMerit`: the Taylor models of $\mu(\cdot, t)$
  of degree $p \ge 4$ are exact.
* `Constrained.TwoPhaseExample.BoxARqp.isARqpCallOut_step`: sufficient conditions for a one-step
  ARqp call on the square.
* `Constrained.TwoPhaseExample.BoxARqp.isARqpCallOut_run`: every inner call of the run is a one-step
  ARqp call.
* `Constrained.TwoPhaseExample.BoxARqp.isEnd_iff`: Phase 2 terminates exactly at the outer iteration
  $M + 1$.
* `Constrained.TwoPhaseExample.BoxARqp.isHighOrderTargetRun`: the data form a run of Phase 2.
* `Constrained.TwoPhaseExample.BoxARqp.isARqpCallOut_calls`: the inner calls of the run are ARqp
  calls, in the form that the run classes of Phase 2 use.
* `Constrained.TwoPhaseExample.BoxARqp.order_le_pow`: the orders along the tolerances for
  $u = 1/(4N^5)$ are at most $128 N^{14}$.
* `Constrained.TwoPhaseExample.BoxARqp.exists_params`: the choice of $N$ for a given constant $C$.

## Implementation notes

* The coordinates $x_1$ and $x_2$ of $x \in \mathbb{R}^2$ are `x 0` and `x 1`. The objective is
  `Constrained.TwoPhaseExample.Box.obj (1 / 16)`, written `objG` in this module.
* ARqp is realized as ARqpC with the zero constraint $c = 0 : E \to G$ into a normed space $G$,
  which is a parameter of the results on calls.
-/

open Set Metric
open scoped Nat RealInnerProductSpace ContDiff

namespace Constrained.TwoPhaseExample

/-! ### One-step calls of ARqp -/

section OneStepCall

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (G : Type*)
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The iterates $x, x + s, x + s, \dots$ of a call that makes one step $s$ from $x$: the iterate
$0$ is $x$, and every later iterate is $x + s$. -/
noncomputable def stepIter (x s : E) : ℕ → E := fun i => if i = 0 then x else x + s

/-- **A one-step call of ARqp.** Let $E$ be a real inner product space, $F : E \to \mathbb{R}$
bounded below on $X \subseteq E$, $1 \le q \le p$, $P$ the constants of ARqp with initial
regularization $\sigma_0$, model-optimality factor $\theta$ and measure fraction $\varsigma$,
and $\varepsilon_j \in (0, 1]$ for $j \in [1, q]$. Let $x \in X$ and $s \in E$ with
$x + s \in X$ and $\|s\| < 1$, and assume:

* the Taylor model of degree $p$ of $F$ at $x$ is exact: $T_p(x, v) = F(x + v)$ for all $v$;
* the regularized model $m(s) = T_p(x, s) + \sigma_0 \|s\|^{p+1}/(p+1)!$ satisfies
  $m(s) < F(x)$;
* for $j \in [1, q]$, $d_0(j)$ is a $\varsigma$-approximate measure step with radius $1$ of
  $\Delta T_j(x, \cdot)$ on $\{e : x + e \in X\}$, and for some $j \in [1, q]$, $\varsigma
  \varepsilon_j / j! < \Delta T_j(x, d_0(j))$, so the Step-1 test fails at $x$;
* for $j \in [1, q]$, $d_m(j)$ is a $\varsigma$-approximate measure step with radius $1$ of the
  $j$-th Taylor decrement of $m$ at $s$ on $\{e : x + s + e \in X\}$, and this decrement at
  $d_m(j)$ is at most $\varsigma \theta \varepsilon_j / j!$;
* for $j \in [1, q]$, $d_1(j)$ is a $\varsigma$-approximate measure step with radius $1$ of
  $\Delta T_j(x + s, \cdot)$ on $\{e : x + s + e \in X\}$, and $\Delta T_j(x + s, d_1(j)) \le
  \varsigma \varepsilon_j / j!$, so the Step-1 test holds at $x + s$.

Then the iterates $x, x + s$ form a call of ARqp on $F$ over $X$ with the tolerances
$\varepsilon$ (`Optimization.IsARqpCallOut`), of length $1$, whose only iteration is successful
and whose returned radii are $1$.

ARqp is ARqpC with $c = 0 : E \to G$ and $h = 0$, all initial radii $1$. The detailed Step 2
returns the step $s$, the iteration is very successful because the ratio is $1$, and the run
terminates at $x + s$. -/
theorem isARqpCallOut_one_step {F : E → ℝ} {X : Set E} {p q : ℕ} (hq : 1 ≤ q) (hqp : q ≤ p)
    {P : Optimization.ARqpParams} {ε : ℕ → ℝ} (hε : ∀ j ∈ Finset.Icc 1 q, 0 < ε j ∧ ε j ≤ 1)
    {x s : E} {d₀ d₁ dm : ℕ → E} (hx : x ∈ X)
    (hxs : x + s ∈ X) (hs1 : ‖s‖ < 1)
    (hTay : ∀ v, (ftaylorSeries ℝ F x).taylorSum p v = F (x + v)) (hlow : BddBelow (F '' X))
    (hmod : Optimization.regularizedModel (ftaylorSeries ℝ F x) p P.σ₀ s < F x)
    (hd₀ : ∀ j ∈ Finset.Icc 1 q, Optimization.IsApproxMeasureStep
      ((ftaylorSeries ℝ F x).taylorDecrement j) 1 {e | x + e ∈ X} P.ς (d₀ j))
    (hfail : ∃ j ∈ Finset.Icc 1 q, P.ς * ε j / j ! < (ftaylorSeries ℝ F x).taylorDecrement j (d₀ j))
    (hdm : ∀ j ∈ Finset.Icc 1 q, Optimization.IsApproxMeasureStep ((ftaylorSeries ℝ
      (Optimization.regularizedModel (ftaylorSeries ℝ F x) p P.σ₀) s).taylorDecrement j) 1
      {e | x + s + e ∈ X} P.ς (dm j) ∧
      (ftaylorSeries ℝ (Optimization.regularizedModel (ftaylorSeries ℝ F x) p P.σ₀)
        s).taylorDecrement j (dm j) ≤ P.ς * P.θ * ε j / j !)
    (hd₁ : ∀ j ∈ Finset.Icc 1 q, Optimization.IsApproxMeasureStep
      ((ftaylorSeries ℝ F (x + s)).taylorDecrement j) 1 {e | x + s + e ∈ X} P.ς (d₁ j))
    (hpass : ∀ j ∈ Finset.Icc 1 q,
      (ftaylorSeries ℝ F (x + s)).taylorDecrement j (d₁ j) ≤ P.ς * ε j / j !) :
    Optimization.IsARqpCallOut G F X p q P ε (stepIter x s) 1 (fun _ => True) (fun _ => 1) := by
  set xs := stepIter x s with hxs_def
  set ss : ℕ → E := fun _ => s
  set σs : ℕ → ℝ := fun _ => P.σ₀
  set δ : ℕ → ℕ → ℝ := fun _ _ => 1
  set dd : ℕ → ℕ → E := fun i j => if i = 0 then d₀ j else d₁ j
  set dmm : ℕ → ℕ → E := fun _ j => dm j
  have hx0 : xs 0 = x := rfl
  have hx1 : xs 1 = x + s := rfl
  have hT0 : (ftaylorSeries ℝ F x).taylorSum p 0 = F x := by rw [hTay, add_zero]
  have hm0 : Optimization.regularizedModel (ftaylorSeries ℝ F x) p P.σ₀ 0 = F x :=
    Optimization.regularizedModel_ftaylorSeries_zero_right p P.σ₀ F x
  have hreg : 0 ≤ P.σ₀ / ((p + 1)! : ℝ) * ‖s‖ ^ (p + 1) := by
    have := P.σ₀_pos; positivity
  have hFs : F (x + s) < F x := by
    rw [Optimization.regularizedModel_def, hTay] at hmod; linarith
  have hpred : (ftaylorSeries ℝ F x).taylorDecrement p s = F x - F (x + s) := by
    rw [FormalMultilinearSeries.taylorDecrement, hTay, hTay, add_zero]
  have hρ : Optimization.arqpRho F p xs ss σs 0 = 1 := by
    rw [Optimization.arqpRho_eq, hx0]
    simp only [ss, hpred]
    exact div_self (by linarith)
  -- the Step-1 tests
  have h1stop :
      Optimization.arqpStop₁ P q ε (Optimization.arqpData F p xs σs) δ dd 1 := by
    intro j hj
    simpa [dd, δ, hx1] using hpass j hj
  have hn1 : ¬ Optimization.arqpStop₁ P q ε (Optimization.arqpData F p xs σs) δ dd 0
      := by
    intro h
    obtain ⟨j, hj, hlt⟩ := hfail
    have := h j hj
    simp [dd, δ, hx0] at this
    linarith
  have hn2 : ¬ Optimization.arqpStop₂ (Optimization.arqpData F p xs σs) ss 0 := by
    intro h
    simp only [Optimization.arqpStop₂_iff, Optimization.arqpData_model, hx0, ss, σs] at h
    rw [h, hm0] at hmod
    exact lt_irrefl _ hmod
  have hNot0 : ¬ Optimization.arqpStop F P p q ε xs ss σs δ dd 0 := by
    rintro (h | h)
    · exact hn1 h
    · exact hn2 h
  have hStop1 : Optimization.arqpStop F P p q ε xs ss σs δ dd 1 := Or.inl h1stop
  -- the model is bounded below on the feasible steps
  have hbdd : BddBelow (Optimization.regularizedModel (ftaylorSeries ℝ F x) p P.σ₀ ''
      {v | x + v ∈ X}) := by
    obtain ⟨b, hb⟩ := hlow
    refine ⟨b, forall_mem_image.2 fun v hv => ?_⟩
    rw [Optimization.regularizedModel_def, hTay]
    have := hb (mem_image_of_mem F hv)
    have : 0 ≤ P.σ₀ / ((p + 1)! : ℝ) * ‖v‖ ^ (p + 1) := by have := P.σ₀_pos; positivity
    linarith
  -- the ARqp run
  have hrun : Optimization.IsARqpRun F X P q ε (fun _ => 1) (Optimization.arqpData F p xs σs) xs
      ss σs δ δ dd dmm := by
    refine ⟨⟨rfl, fun k hk h1 => ?_, fun k hk => ?_⟩, hx, rfl, fun k hk => ?_, fun k hk => ?_⟩
    · rcases k with _ | _ | k
      · refine ⟨by simpa [hx0, ss] using hxs, ?_, fun h => ?_, fun _ _ => one_pos,
          fun _ _ => le_rfl, Or.inr fun j hj => ?_⟩
        · simp only [Optimization.arqpData_model, hx0, ss, σs, hm0]
          exact hmod.le
        · simp only [Optimization.arqpData_model, hx0, ss, σs,
            hm0] at h
          exact absurd h hmod.ne
        · simp only [Optimization.arqpData_modelDec, hx0, ss, σs,
            dmm, δ]
          exact ⟨(hdm j hj).1, by simpa using (hdm j hj).2⟩
      · exact absurd h1stop h1
      · exact absurd hStop1 (hk 1 (by omega))
    · rcases k with _ | k
      · have := Optimization.arAcceptance_of_one_le P.toARParams (ρ := 1) le_rfl x s
          (σ := P.σ₀) P.σmin_le_σ₀ P.σ₀_pos.le
        change Optimization.ARAcceptance P.toARParams (Optimization.arqpRho F p xs ss σs 0) (xs 0)
          (ss 0) (xs 1) (σs 0) (σs 1)
        rw [hρ, hx0, hx1]
        exact this
      · exact absurd hStop1 (hk 1 (by omega))
    · intro j hj
      rcases k with _ | _ | k
      · exact hd₀ j hj
      · exact hd₁ j hj
      · exact absurd hStop1 (hk 1 (by omega))
    · rcases k with _ | k
      · have hρ' : Optimization.arqpRatio F (Optimization.arqpData F p xs σs) xs ss 0 = 1 := hρ
        refine ⟨fun _ => rfl, fun h => absurd ?_ h⟩
        rw [hρ']
        exact P.η₁_le_η₂.trans P.η₂_lt_one.le
      · exact absurd hStop1 (hk 1 (by omega))
  -- the ARqpC run with `c = 0`, `h = 0`
  have hr : Optimization.IsARqpCRun F (0 : E → G) 0 X p q P
      (Optimization.compositeHalvingSet (0 : G → ℝ) X) ε (fun _ => 1) xs ss σs δ δ dd dmm := by
    refine Optimization.IsARqpCRun.of_isARqpRun_zero hq hqp hε (fun _ _ => ⟨one_pos, le_rfl⟩)
      hrun fun k hk hns => ?_
    rcases k with _ | _ | k
    · simp only [hx0, ss, σs]
      exact Optimization.IsDetailedStepOutput.of_short_step hq hxs hbdd (by rw [hm0]; exact hmod)
        hs1 fun j hj => ⟨(hdm j hj).1.1, (hdm j hj).1.2, (hdm j hj).2⟩
    · exact absurd h1stop hns
    · exact absurd hStop1 (hk 1 (by omega))
  refine ⟨xs, ss, σs, δ, δ, dd, dmm, 1, hr,
    ⟨Optimization.arqpcStop_zero_iff.2 hStop1, fun j hj => ?_⟩,
    le_rfl, fun i _ => rfl, fun i hi => ?_, Or.inl fun j _ => rfl⟩
  · obtain rfl : j = 0 := by omega
    exact Optimization.arqpcStop_zero_iff.not.2 hNot0
  · obtain rfl : i = 0 := by omega
    rw [Optimization.arqpRatio_zero, hρ]
    exact iff_of_true trivial (P.η₁_le_η₂.trans P.η₂_lt_one.le)

end OneStepCall

namespace BoxARqp

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-- The objective $f(x) = x_1 - x_2/16$ of the example,
`Constrained.TwoPhaseExample.Box.obj (1 / 16)`. -/
local notation "objG" => Box.obj (1 / 16)

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-! ### The data -/

/-- $f(a, b) = a - b/16$. -/
theorem obj_pt (a b : ℝ) : objG (pt a b) = a - b / 16 := by rw [Box.obj_pt]; ring

/-- The first-order Taylor decrement of $\mu(\cdot, t)$ at $y$ along $d$ is
$$-\nabla \mu(y, t)[d] = -\bigl(y_1^3/2 + (f(y) - t)\bigr) d_1 + \frac{f(y) - t}{16}\, d_2.$$
-/
theorem taylorDecrement_one_eq (y : ℝ²) (t : ℝ) (d : ℝ²) :
    (ftaylorSeries ℝ (Constrained.targetMerit objG Box.con t) y).taylorDecrement 1 d =
      -(y 0 ^ 3 / 2 + (objG y - t)) * d 0 + (objG y - t) / 16 * d 1 := by
  rw [Box.taylorDecrement_one]; ring

/-- $\mu(y, t) = y_1^4/8 + (f(y) - t)^2/2$. -/
theorem targetMerit_eq (y : ℝ²) (t : ℝ) :
    Constrained.targetMerit objG Box.con t y = y 0 ^ 4 / 8 + (objG y - t) ^ 2 / 2 := by
  rw [Constrained.targetMerit_def, Box.norm_con]
  ring

/-- For every target $t$, $\mu(\cdot, t)$ is of class $C^\omega$ (analytic), which is
`ContDiff ℝ ⊤`. -/
theorem contDiff_targetMerit (t : ℝ) : ContDiff ℝ ⊤ (Constrained.targetMerit objG Box.con t) :=
  contDiff_iff_contDiffAt.2 fun _ =>
    Constrained.contDiffAt_targetMerit (Box.contDiff_obj _).contDiffAt Box.contDiff_con.contDiffAt

/-- The coefficients $a_i$ of the quartic polynomial $\tau \mapsto \mu(y + \tau s, t)$:
$a_1 = y_1^3 s_1 / 2 + (f(y) - t)(s_1 - s_2/16)$,
$a_2 = 3 y_1^2 s_1^2 / 4 + (s_1 - s_2/16)^2/2$, $a_3 = y_1 s_1^3 / 2$, $a_4 = s_1^4/8$, and
$a_i = 0$ for every other $i$. -/
noncomputable def meritCoeff (y s : ℝ²) (t : ℝ) (i : ℕ) : ℝ :=
  if i = 1 then y 0 ^ 3 * s 0 / 2 + (objG y - t) * (s 0 - s 1 / 16)
  else if i = 2 then 3 * y 0 ^ 2 * s 0 ^ 2 / 4 + (s 0 - s 1 / 16) ^ 2 / 2
  else if i = 3 then y 0 * s 0 ^ 3 / 2
  else if i = 4 then s 0 ^ 4 / 8 else 0

/-- For $p \ge 4$, $\mu(y + \tau s, t) = \mu(y, t) + \sum_{i=1}^p \tau^i a_i$, with the coefficients
$a_i$ of `Constrained.TwoPhaseExample.BoxARqp.meritCoeff`. -/
theorem targetMerit_add_smul {p : ℕ} (hp : 4 ≤ p) (y s : ℝ²) (t τ : ℝ) :
    Constrained.targetMerit objG Box.con t (y + τ • s) =
      Constrained.targetMerit objG Box.con t y + ∑ i ∈ Finset.Icc 1 p, τ ^ i * meritCoeff y s t i
          := by
  have hsub : Finset.Icc 1 4 ⊆ Finset.Icc 1 p := Finset.Icc_subset_Icc le_rfl hp
  rw [← Finset.sum_subset hsub fun i hi hi' => by
    have h1 := Finset.mem_Icc.1 hi
    have h2 : ¬ (1 ≤ i ∧ i ≤ 4) := fun h => hi' (Finset.mem_Icc.2 h)
    have : i ≠ 1 ∧ i ≠ 2 ∧ i ≠ 3 ∧ i ≠ 4 := by omega
    simp [meritCoeff, this.1, this.2.1, this.2.2.1, this.2.2.2]]
  rw [show Finset.Icc 1 4 = ({1, 2, 3, 4} : Finset ℕ) by decide]
  simp only [targetMerit_eq, Box.obj_apply, meritCoeff, PiLp.add_apply, PiLp.smul_apply,
      smul_eq_mul]
  simp [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton]
  ring

/-- **The Taylor model of $\mu(\cdot, t)$ of degree $p \ge 4$ is exact.** For $p \ge 4$,
$y, s \in \mathbb{R}^2$ and $t \in \mathbb{R}$,
$$T_p(y, s) = \mu(y + s, t),$$
where $T_p(y, \cdot)$ is the Taylor polynomial of degree $p$ of $\mu(\cdot, t)$ at $y$.

The Taylor polynomial is `FormalMultilinearSeries.taylorSum` of `ftaylorSeries ℝ
(Constrained.targetMerit objG Box.con t) y`. -/
theorem taylorSum_targetMerit {p : ℕ} (hp : 4 ≤ p) (y : ℝ²) (t : ℝ) (s : ℝ²) :
    (ftaylorSeries ℝ (Constrained.targetMerit objG Box.con t) y).taylorSum p s =
      Constrained.targetMerit objG Box.con t (y + s) := by
  rw [← taylorPolynomial_eq_taylorSum]
  exact Optimization.taylorPolynomial_eq_self_of_poly
    ((contDiff_targetMerit t).contDiffAt.of_le (by exact_mod_cast le_top))
    (targetMerit_add_smul hp y s t)

/-- The coefficient $\sigma \|s\|^{p-1} / p!$ for which the gradient of the regularization term
$\sigma \|s\|^{p+1}/(p+1)!$ at $s$ is this coefficient times $s$.

It is computed with the real factorial `Optimization.realFactorial` and a real exponent. -/
noncomputable def regCoeff (p : ℕ) (σ : ℝ) (s : ℝ²) : ℝ :=
  σ / Optimization.realFactorial ((p : ℝ) + 1 - 1) * ‖s‖ ^ ((p : ℝ) + 1 - 2)

/-- Let $p \ge 4$ and let $m(s) = \mu(y + s, t) + \sigma \|s\|^{p+1}/(p+1)!$ be the regularized
model of $\mu(\cdot, t)$ at $y$. The first-order Taylor decrement of $m$ at $s$ along $d$ is the
first-order Taylor decrement of $\mu(\cdot, t)$ at $y + s$ along $d$ minus
$c \langle s, d \rangle$, where $c = \sigma \|s\|^{p-1}/p!$ is
`Constrained.TwoPhaseExample.BoxARqp.regCoeff p σ s`. -/
theorem taylorDecrement_one_model {p : ℕ} (hp : 4 ≤ p) (y s d : ℝ²) (t σ : ℝ) :
    (ftaylorSeries ℝ (Optimization.regularizedModel
        (ftaylorSeries ℝ (Constrained.targetMerit objG Box.con t) y) p σ) s).taylorDecrement 1 d =
      (ftaylorSeries ℝ (Constrained.targetMerit objG Box.con t) (y + s)).taylorDecrement 1 d -
        regCoeff p σ s * (s 0 * d 0 + s 1 * d 1) := by
  rw [FormalMultilinearSeries.taylorDecrement_one_apply,
    FormalMultilinearSeries.taylorDecrement_one_apply]
  simp only [ftaylorSeries, iteratedFDeriv_one_apply]
  have hr : (1 : ℝ) < (p : ℝ) + 1 := by
    have : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
    linarith
  rw [Optimization.regularizedModel_eq_powRegularizedModel,
    Optimization.fderiv_powRegularizedModel hr]
  have hT : (ftaylorSeries ℝ (Constrained.targetMerit objG Box.con t) y).taylorSum p =
      fun v => Constrained.targetMerit objG Box.con t (y + v) :=
    funext (taylorSum_targetMerit hp y t)
  rw [hT, fderiv_comp_add_left]
  simp only [add_apply, smul_apply, innerSL_apply_apply,
    smul_eq_mul]
  rw [show (inner ℝ s d : ℝ) = s 0 * d 0 + s 1 * d 1 by
    simp [PiLp.inner_apply, Fin.sum_univ_two]; ring]
  unfold regCoeff
  ring

/-- For $j \le 4$, the Taylor decrement of order $j$ of $\mu(\cdot, t)$ at $y$ along $d$ is
$\Delta T_j(y, d) = -\sum_{i=1}^j a_i$, with the coefficients $a_i$ of
`Constrained.TwoPhaseExample.BoxARqp.meritCoeff y d t`. -/
theorem taylorDecrement_eq_meritCoeff {j : ℕ} (hj : j ≤ 4) (y d : ℝ²) (t : ℝ) :
    (ftaylorSeries ℝ (Constrained.targetMerit objG Box.con t) y).taylorDecrement j d =
      -∑ i ∈ Finset.Icc 1 j, meritCoeff y d t i := by
  rw [FormalMultilinearSeries.taylorDecrement, ← taylorPolynomial_eq_taylorSum,
    taylorPolynomial_zero_right,
    Optimization.taylorPolynomial_eq_of_poly (N := 4) (a := meritCoeff y d t)
      ((contDiff_targetMerit t).contDiffAt.of_le (by exact_mod_cast le_top))
      (Filter.Eventually.of_forall fun τ => by
        simpa [one_mul] using targetMerit_add_smul le_rfl y d t τ) hj]
  ring

/-- **The second-order decrement of $\mu(\cdot, t)$ is at most the first-order one**, since
$\mu(\cdot, t)$ is convex along every line: $\Delta T_2(y, d) = \Delta T_1(y, d) - a_2$ with
$a_2 = 3 y_1^2 d_1^2/4 + (d_1 - d_2/16)^2/2 \ge 0$. -/
theorem taylorDecrement_two_le (y d : ℝ²) (t : ℝ) :
    (ftaylorSeries ℝ (Constrained.targetMerit objG Box.con t) y).taylorDecrement 2 d ≤
      (ftaylorSeries ℝ (Constrained.targetMerit objG Box.con t) y).taylorDecrement 1 d := by
  rw [taylorDecrement_eq_meritCoeff (by norm_num), taylorDecrement_eq_meritCoeff (by norm_num)]
  rw [show Finset.Icc 1 2 = ({1, 2} : Finset ℕ) by decide]
  simp [meritCoeff]
  nlinarith [sq_nonneg (d 0 - d 1 / 16), sq_nonneg (y 0 * d 0)]

/-- The second derivative of $\mu(\cdot, t)$ is positive semidefinite:
$\nabla^2 \mu(y, t)[d, d] \ge 0$ for all $y$ and $d$. -/
theorem iteratedFDeriv_two_targetMerit_nonneg (y d : ℝ²) (t : ℝ) :
    0 ≤ iteratedFDeriv ℝ 2 (Constrained.targetMerit objG Box.con t) y (fun _ => d) := by
  have h := taylorDecrement_two_le y d t
  rw [FormalMultilinearSeries.taylorDecrement_eq, FormalMultilinearSeries.taylorDecrement_eq,
    show Finset.Icc 1 2 = ({1, 2} : Finset ℕ) by decide] at h
  simp only [Finset.Icc_self, Finset.sum_singleton, ftaylorSeries] at h
  rw [Finset.sum_insert (by decide), Finset.sum_singleton] at h
  norm_num at h
  linarith

/-- **The second-order decrement of the model is at most the first-order one plus
$\sigma \|s\|^3/2$.** Let $p \ge 4$, $\sigma \ge 0$, and $s, d \in \mathbb{R}^2$ with
$\|s\| \le 1$ and $\|d\| \le 1$. For the regularized model $m$ of $\mu(\cdot, t)$ at $y$ of
degree $p$ with the parameter $\sigma$, the second-order Taylor decrement of $m$ at $s$ along
$d$ is at most its first-order Taylor decrement plus $\sigma \|s\|^3/2$.

The Hessian of $\mu$ is positive semidefinite, and the Hessian of the regularization term has
norm at most $\sigma \|s\|^{p-1}/(p-1)!$. -/
theorem taylorDecrement_two_model_le {p : ℕ} (hp : 4 ≤ p) {σ : ℝ} (hσ : 0 ≤ σ) (y : ℝ²) (t : ℝ) {s
    d : ℝ²}
    (hs : ‖s‖ ≤ 1) (hd : ‖d‖ ≤ 1) :
    (ftaylorSeries ℝ (Optimization.regularizedModel
        (ftaylorSeries ℝ (Constrained.targetMerit objG Box.con t) y) p σ) s).taylorDecrement 2 d ≤
      (ftaylorSeries ℝ (Optimization.regularizedModel
        (ftaylorSeries ℝ (Constrained.targetMerit objG Box.con t) y) p σ) s).taylorDecrement 1 d +
        σ * ‖s‖ ^ 3 / 2 := by
  set m := Optimization.regularizedModel
    (ftaylorSeries ℝ (Constrained.targetMerit objG Box.con t) y) p σ with hm
  have e : (ftaylorSeries ℝ m s).taylorDecrement 2 d =
      (ftaylorSeries ℝ m s).taylorDecrement 1 d - 1 / 2 * iteratedFDeriv ℝ 2 m s (fun _ => d) := by
    rw [FormalMultilinearSeries.taylorDecrement_eq, FormalMultilinearSeries.taylorDecrement_eq,
      show Finset.Icc 1 2 = ({1, 2} : Finset ℕ) by decide, Finset.sum_insert (by decide),
      Finset.sum_singleton, Finset.Icc_self, Finset.sum_singleton]
    simp only [ftaylorSeries]
    norm_num
    ring
  have hT : (ftaylorSeries ℝ (Constrained.targetMerit objG Box.con t) y).taylorSum p =
      fun v => Constrained.targetMerit objG Box.con t (y + v) :=
    funext (taylorSum_targetMerit hp y t)
  have e2 : iteratedFDeriv ℝ 2 m s (fun _ => d) =
      iteratedFDeriv ℝ 2 (Constrained.targetMerit objG Box.con t) (y + s) (fun _ => d) +
        σ / ((p + 1)! : ℝ) * iteratedFDeriv ℝ 2 (fun y : ℝ² => ‖y‖ ^ (p + 1)) s (fun _ => d) := by
    rw [hm, Optimization.iteratedFDeriv_regularizedModel (Or.inl (by omega)), hT,
      iteratedFDeriv_comp_add_left]
    simp only [add_apply, smul_apply, smul_eq_mul]
  rw [e, e2]
  have h1 := iteratedFDeriv_two_targetMerit_nonneg (y + s) d t
  have h2 := abs_iteratedFDeriv_norm_pow_apply_le (E := ℝ²) (r := p + 1) (ℓ := 2) (by omega)
    (s := s) (Or.inr (by omega)) d
  have hf : ((p + 1)! : ℝ) / ((p + 1 - 2)! : ℝ) ≤ ((p + 1)! : ℝ) := by
    apply div_le_self (by positivity)
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero _)
  have hs3 : ‖s‖ ^ (p + 1 - 2) ≤ ‖s‖ ^ 3 := pow_le_pow_of_le_one (norm_nonneg _) hs (by omega)
  have hd2 : ‖d‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) hd
  have hb : |iteratedFDeriv ℝ 2 (fun y : ℝ² => ‖y‖ ^ (p + 1)) s (fun _ => d)| ≤
      ((p + 1)! : ℝ) * ‖s‖ ^ 3 := by
    refine h2.trans ?_
    calc ((p + 1)! : ℝ) / ((p + 1 - 2)! : ℝ) * ‖s‖ ^ (p + 1 - 2) * ‖d‖ ^ 2
        ≤ ((p + 1)! : ℝ) * ‖s‖ ^ 3 * 1 := by gcongr
      _ = _ := mul_one _
  have hc : σ / ((p + 1)! : ℝ) * iteratedFDeriv ℝ 2 (fun y : ℝ² => ‖y‖ ^ (p + 1)) s
      (fun _ => d) ≥ -(σ * ‖s‖ ^ 3) := by
    have hpf : (0 : ℝ) < ((p + 1)! : ℝ) := by positivity
    have := neg_abs_le (iteratedFDeriv ℝ 2 (fun y : ℝ² => ‖y‖ ^ (p + 1)) s (fun _ => d))
    have h3 : σ / ((p + 1)! : ℝ) * (-(((p + 1)! : ℝ) * ‖s‖ ^ 3)) = -(σ * ‖s‖ ^ 3) := by
      field_simp
    rw [ge_iff_le, ← h3]
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  linarith

/-- **A witness from a maximizer.** Let $D$ be derivative data on $\mathbb{R}^2$,
$j \in \mathbb{N}$, $S \subseteq \mathbb{R}^2$ closed with $0 \in S$, and $\varsigma \le 1$.
Then the Taylor decrement $\Delta T_j$ of $D$ attains its supremum over
$\{d : \|d\| \le 1\} \cap S$ at some $d$, and this $d$ is a $\varsigma$-approximate measure step
of $\Delta T_j$ on $S$ with radius $1$. -/
theorem exists_isApproxMeasureStep_eq (D : FormalMultilinearSeries ℝ ℝ² ℝ) (j : ℕ) {S : Set ℝ²}
    (hS : IsClosed S) (h0 : (0 : ℝ²) ∈ S) {ς : ℝ} (hς : ς ≤ 1) :
    ∃ d, Optimization.IsApproxMeasureStep (D.taylorDecrement j) 1 S ς d ∧
      D.taylorDecrement j d = Optimization.decrementMeasure (D.taylorDecrement j) 1 S := by
  obtain ⟨d, hd, hdM⟩ := Optimization.exists_decrementMeasure_eq hS h0 zero_le_one
    (D.continuous_taylorDecrement j).continuousOn
  have hM := Optimization.taylorMeasure_nonneg D j h0 zero_le_one
  exact ⟨d, ⟨hd, by rw [hdM]; exact mul_le_of_le_one_left hM hς⟩, hdM⟩

/-! ### The constants -/

/-- The adaptive-regularization constants of the example: $\sigma_0 = \sigma_{\min} = 10^{-6}$,
$\eta_1 = 1/4$, $\eta_2 = 3/4$, $\gamma_1 = 1/2$, $\gamma_2 = 2$, $\gamma_3 = 3$, $\theta = 1/4$
and $\varsigma = 1/2$, so that $\theta < \varsigma$. -/
noncomputable def params : Optimization.ARqpParams where
  σ₀ := 1 / 10 ^ 6
  σmin := 1 / 10 ^ 6
  η₁ := 1 / 4
  η₂ := 3 / 4
  γ₁ := 1 / 2
  γ₂ := 2
  γ₃ := 3
  σ₀_pos := by norm_num
  σmin_nonneg := by norm_num
  σmin_le_σ₀ := le_rfl
  η₁_pos := by norm_num
  η₁_le_η₂ := by norm_num
  η₂_lt_one := by norm_num
  γ₁_pos := by norm_num
  γ₁_lt_one := by norm_num
  one_lt_γ₂ := by norm_num
  γ₂_le_γ₃ := by norm_num
  θ := 1 / 4
  ς := 1 / 2
  θ_pos := by norm_num
  θ_lt_one := by norm_num
  ς_pos := by norm_num
  ς_le_one := by norm_num

/-- The constants satisfy $\sigma_{\min} = 10^{-6}$. -/
theorem params_σmin : params.σmin = 1 / 10 ^ 6 := rfl

/-- The constants satisfy $\theta < \varsigma$. -/
theorem params_θ_lt_ς : params.θ < params.ς := by norm_num [params]


/-! ### One-step calls on the square -/

/-- For $p \ge 4$, $\sigma \ge 0$ and $\|s\| \le 1$, the coefficient $c = \sigma \|s\|^{p-1}/p!$ of
`Constrained.TwoPhaseExample.BoxARqp.regCoeff` satisfies $0 \le c \le \sigma \|s\|^3/24$. -/
theorem regCoeff_mem {p : ℕ} (hp : 4 ≤ p) {σ : ℝ} (hσ : 0 ≤ σ) {s : ℝ²} (hs : ‖s‖ ≤ 1) :
    0 ≤ regCoeff p σ s ∧ regCoeff p σ s ≤ σ * ‖s‖ ^ 3 / 24 := by
  have e1 : (p : ℝ) + 1 - 1 = (p : ℝ) := by ring
  have e2 : (p : ℝ) + 1 - 2 = ((p - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  unfold regCoeff
  rw [e1, e2, Optimization.realFactorial_natCast, Real.rpow_natCast]
  have hf : (24 : ℝ) ≤ (p ! : ℝ) := by
    have := Nat.factorial_le hp
    exact_mod_cast this
  have hpow : ‖s‖ ^ (p - 1) ≤ ‖s‖ ^ 3 := pow_le_pow_of_le_one (norm_nonneg _) hs (by omega)
  have hn : 0 ≤ ‖s‖ ^ (p - 1) := by positivity
  refine ⟨by positivity, ?_⟩
  calc σ / (p ! : ℝ) * ‖s‖ ^ (p - 1) ≤ σ / 24 * ‖s‖ ^ 3 := by
        gcongr
    _ = σ * ‖s‖ ^ 3 / 24 := by ring

/-- For $p \ge 4$, $\sigma \ge 0$ and $\|s\| \le 1$, $\sigma \|s\|^{p+1}/(p+1)! \le \sigma
\|s\|^5/120$. -/
theorem reg_le {p : ℕ} (hp : 4 ≤ p) {σ : ℝ} (hσ : 0 ≤ σ) {s : ℝ²} (hs : ‖s‖ ≤ 1) :
    σ / ((p + 1)! : ℝ) * ‖s‖ ^ (p + 1) ≤ σ * ‖s‖ ^ 5 / 120 := by
  have hf : (120 : ℝ) ≤ ((p + 1)! : ℝ) := by
    have := Nat.factorial_le (show 5 ≤ p + 1 by omega)
    exact_mod_cast this
  have hpow : ‖s‖ ^ (p + 1) ≤ ‖s‖ ^ 5 := pow_le_pow_of_le_one (norm_nonneg _) hs (by omega)
  calc σ / ((p + 1)! : ℝ) * ‖s‖ ^ (p + 1) ≤ σ / 120 * ‖s‖ ^ 5 := by
        gcongr
    _ = σ * ‖s‖ ^ 5 / 120 := by ring

/-- **A one-step ARqp call on the square.** Let $p \ge 4$ and $q \in \{1, 2\}$, let
$t \in \mathbb{R}$, and let $x = (x_a, x_b)$ and $x' = (y_a, y_b)$ be points of $[-1/2, 1/2]^2$
with $L = |y_a - x_a| + |y_b - x_b| \le 1/2$. Write $F = x_a - x_b/16 - t = f(x) - t$ and
$F' = y_a - y_b/16 - t = f(x') - t$, and assume $F \ge 0$ and $x_a \ge 0$. Let $\varepsilon$ be
tolerances with $\varepsilon_1 = T_1 \in (0, 1]$, and with $\varepsilon_2 = T_2$ if $q \ge 2$,
where $T_2 \in (0, 1]$ and $T_1/4 + 10^{-6} L^3/2 \le T_2/16$. Let $g \in \{1, -1\}$. Assume:

* (Step 1 fails at $x$) $T_1 < x_a^3/2 + F + F/16$;
* (model decrease) $y_a^4/8 + F'^2/2 + 10^{-6} L^5/120 < x_a^4/8 + F^2/2$, that is, $\mu(x', t)$
  plus the bound $\sigma_0 L^5/120$ on the regularization term is smaller than $\mu(x, t)$;
* (signs) $g (y_a^3/2 + F') \ge 0$, $g F' \le 0$, $g (y_a - x_a) \ge 0$ and
  $g (y_b - x_b) \ge 0$;
* (criticality at $x'$) $g (y_a^3/2 + F') - g F'/16 + 10^{-6} L^4/24 \le T_1/4$.

Then the iterates $x, x', x', \dots$ form a call of ARqp on $\mu(\cdot, t)$ over $X$ with the
constants `Constrained.TwoPhaseExample.BoxARqp.params` and the tolerances $\varepsilon$
(`Optimization.IsARqpCallOut`), of length $1$, whose only iteration is successful and whose
returned radii are $1$.

The gradient of $\mu(\cdot, t)$ at $x'$ is $(y_a^3/2 + F', -F'/16)$. The last two conditions say
that it has the signs of $g$ and that its $\ell^1$-norm plus $\sigma_0 L^4/24$ is at most
$T_1/4$, which gives the model criticality and the Step-1 test at $x'$. At order $2$ the
decrements are bounded through `Constrained.TwoPhaseExample.BoxARqp.taylorDecrement_two_le` and
`Constrained.TwoPhaseExample.BoxARqp.taylorDecrement_two_model_le`, and the witnesses are
maximizers. The proof applies `Constrained.TwoPhaseExample.isARqpCallOut_one_step`. -/
theorem isARqpCallOut_step {p q : ℕ} (hp : 4 ≤ p) (hq1 : 1 ≤ q) (hq2 : q ≤ 2)
    {t xa xb ya yb T₁ T₂ g : ℝ} {ε : ℕ → ℝ} (hT : ε 1 = T₁) (hT2 : 2 ≤ q → ε 2 = T₂)
    (hT20 : 0 < T₂) (hT21 : T₂ ≤ 1)
    (hT12 : T₁ / 4 + 1 / 10 ^ 6 * (|ya - xa| + |yb - xb|) ^ 3 / 2 ≤ T₂ / 16)
    (hxa : |xa| ≤ 1 / 2) (hxb : |xb| ≤ 1 / 2) (hya : |ya| ≤ 1 / 2) (hyb : |yb| ≤ 1 / 2)
    (hL : |ya - xa| + |yb - xb| ≤ 1 / 2) (hT0 : 0 < T₁) (hT1 : T₁ ≤ 1)
    (hF0 : 0 ≤ xa - xb / 16 - t) (hxa0 : 0 ≤ xa)
    (hfail : T₁ < xa ^ 3 / 2 + (xa - xb / 16 - t) + (xa - xb / 16 - t) / 16)
    (hmod : ya ^ 4 / 8 + (ya - yb / 16 - t) ^ 2 / 2 +
      1 / 10 ^ 6 * (|ya - xa| + |yb - xb|) ^ 5 / 120 < xa ^ 4 / 8 + (xa - xb / 16 - t) ^ 2 / 2)
    (hg : g = 1 ∨ g = -1) (hgA : 0 ≤ g * (ya ^ 3 / 2 + (ya - yb / 16 - t)))
    (hgF : g * (ya - yb / 16 - t) ≤ 0) (hgs0 : 0 ≤ g * (ya - xa)) (hgs1 : 0 ≤ g * (yb - xb))
    (hcrit : g * (ya ^ 3 / 2 + (ya - yb / 16 - t)) - g * (ya - yb / 16 - t) / 16 +
      1 / 10 ^ 6 * (|ya - xa| + |yb - xb|) ^ 4 / 24 ≤ T₁ / 4) :
    Optimization.IsARqpCallOut G (Constrained.targetMerit objG Box.con t) Box.square p q params ε
      (fun i => if i = 0 then pt xa xb else pt ya yb) 1 (fun _ => True) (fun _ => 1) := by
  have hg1 : |g| = 1 := by rcases hg with rfl | rfl <;> simp
  set s := pt ya yb - pt xa xb with hs_def
  have hs : s = pt (ya - xa) (yb - xb) := pt_sub _ _ _ _
  have hxs : pt xa xb + s = pt ya yb := by rw [hs_def]; abel
  have hsL : ‖s‖ ≤ |ya - xa| + |yb - xb| := by rw [hs]; exact norm_pt_le_add _ _
  have hs1 : ‖s‖ ≤ 1 := by linarith
  have hσ : params.σ₀ = 1 / 10 ^ 6 := rfl
  have hς : params.ς = 1 / 2 := rfl
  have hθ : params.θ = 1 / 4 := rfl
  have hxi : (fun i => if i = 0 then pt xa xb else pt ya yb) = stepIter (pt xa xb) s := by
    funext i; rcases i with _ | i
    · rfl
    · simp [stepIter, hxs]
  rw [hxi]
  have hmemx : pt xa xb ∈ Box.square := Box.pt_mem_square (hxa.trans (by norm_num)) (hxb.trans (by
      norm_num))
  have hmemy : pt ya yb ∈ Box.square := Box.pt_mem_square (hya.trans (by norm_num)) (hyb.trans (by
      norm_num))
  have hS : ∀ {a b : ℝ}, |a| ≤ 1 / 2 → |b| ≤ 1 / 2 → ∀ {c d : ℝ}, |c| ≤ 1 / 2 → |d| ≤ 1 / 2 →
      pt c d ∈ {e | pt a b + e ∈ Box.square} := fun {a b} ha hb {c d} hc hd => by
    simp only [mem_ofPred_eq, pt_add, pt_zero, pt_one]
    exact Box.pt_mem_square ((abs_add_le _ _).trans (by linarith)) ((abs_add_le _ _).trans (by
        linarith))
  have h0S : ∀ {a b : ℝ}, |a| ≤ 1 / 2 → |b| ≤ 1 / 2 → (0 : ℝ²) ∈ {e | pt a b + e ∈ Box.square} :=
    fun {a b} ha hb => by
      simp only [mem_ofPred_eq, add_zero]
      exact Box.pt_mem_square (ha.trans (by norm_num)) (hb.trans (by norm_num))
  have hhalf : |(1 / 2 : ℝ)| ≤ 1 / 2 := by norm_num
  have hhalf' : |(-1 / 2 : ℝ)| ≤ 1 / 2 := by norm_num
  have hgw : |-g / 2| ≤ 1 / 2 := by rw [abs_div, abs_neg, hg1]; norm_num
  obtain ⟨hc0, hc1⟩ := regCoeff_mem hp (σ := params.σ₀) (by rw [hσ]; norm_num) hs1
  have hcL : regCoeff p params.σ₀ s * (|ya - xa| + |yb - xb|) ≤
      1 / 10 ^ 6 * (|ya - xa| + |yb - xb|) ^ 4 / 24 := by
    have h3 : ‖s‖ ^ 3 ≤ (|ya - xa| + |yb - xb|) ^ 3 := pow_le_pow_left₀ (norm_nonneg _) hsL 3
    have hL0 : 0 ≤ |ya - xa| + |yb - xb| := by positivity
    calc regCoeff p params.σ₀ s * (|ya - xa| + |yb - xb|)
        ≤ params.σ₀ * ‖s‖ ^ 3 / 24 * (|ya - xa| + |yb - xb|) :=
          mul_le_mul_of_nonneg_right hc1 hL0
      _ ≤ 1 / 10 ^ 6 * (|ya - xa| + |yb - xb|) ^ 3 / 24 * (|ya - xa| + |yb - xb|) := by
          rw [hσ]; gcongr
      _ = _ := by ring
  have hgabs : ∀ z : ℝ, 0 ≤ -g * z → |z| = -g * z := fun z hz => by
    rcases hg with rfl | rfl
    · simp only [neg_mul, one_mul] at hz ⊢; exact abs_of_nonpos (by linarith)
    · simp only [neg_neg, one_mul] at hz ⊢; exact abs_of_nonneg hz
  have hgle : ∀ z : ℝ, g * z ≤ |z| := fun z => by
    rcases hg with rfl | rfl
    · simp only [one_mul]; exact le_abs_self z
    · simp only [neg_one_mul]; exact neg_le_abs z
  have hs0 : s 0 = ya - xa := by rw [hs, pt_zero]
  have hs1' : s 1 = yb - xb := by rw [hs, pt_one]
  have hΔm : ∀ d : ℝ², (ftaylorSeries ℝ (Optimization.regularizedModel (ftaylorSeries ℝ
      (Constrained.targetMerit objG Box.con t) (pt xa xb)) p params.σ₀) s).taylorDecrement 1 d =
      (-(ya ^ 3 / 2 + (ya - yb / 16 - t)) - regCoeff p params.σ₀ s * (ya - xa)) * d 0 +
        ((ya - yb / 16 - t) / 16 - regCoeff p params.σ₀ s * (yb - xb)) * d 1 := fun d => by
    rw [taylorDecrement_one_model hp, hxs, taylorDecrement_one_eq, obj_pt, hs0, hs1']
    simp only [pt_zero]
    ring
  have hΔ' : ∀ d : ℝ², (ftaylorSeries ℝ (Constrained.targetMerit objG Box.con t)
      (pt xa xb + s)).taylorDecrement 1 d =
      -(ya ^ 3 / 2 + (ya - yb / 16 - t)) * d 0 + (ya - yb / 16 - t) / 16 * d 1 := fun d => by
    rw [hxs, taylorDecrement_one_eq, obj_pt]; simp only [pt_zero]
  have hgs0' : 0 ≤ regCoeff p params.σ₀ s * (g * (ya - xa)) := mul_nonneg hc0 hgs0
  have hgs1' : 0 ≤ regCoeff p params.σ₀ s * (g * (yb - xb)) := mul_nonneg hc0 hgs1
  have hab0 : |-(ya ^ 3 / 2 + (ya - yb / 16 - t)) - regCoeff p params.σ₀ s * (ya - xa)| =
      -g * (-(ya ^ 3 / 2 + (ya - yb / 16 - t)) - regCoeff p params.σ₀ s * (ya - xa)) :=
    hgabs _ (by
      have e : -g * (-(ya ^ 3 / 2 + (ya - yb / 16 - t)) - regCoeff p params.σ₀ s * (ya - xa)) =
        g * (ya ^ 3 / 2 + (ya - yb / 16 - t)) + regCoeff p params.σ₀ s * (g * (ya - xa)) := by ring
      rw [e]; linarith)
  have hab1 : |(ya - yb / 16 - t) / 16 - regCoeff p params.σ₀ s * (yb - xb)| =
      -g * ((ya - yb / 16 - t) / 16 - regCoeff p params.σ₀ s * (yb - xb)) :=
    hgabs _ (by
      have e : -g * ((ya - yb / 16 - t) / 16 - regCoeff p params.σ₀ s * (yb - xb)) =
        -(g * (ya - yb / 16 - t)) / 16 + regCoeff p params.σ₀ s * (g * (yb - xb)) := by ring
      rw [e]; linarith)
  have hab0' : |-(ya ^ 3 / 2 + (ya - yb / 16 - t))| = -g * -(ya ^ 3 / 2 + (ya - yb / 16 - t)) :=
    hgabs _ (by rw [neg_mul_neg]; exact hgA)
  have hab1' : |(ya - yb / 16 - t) / 16| = -g * ((ya - yb / 16 - t) / 16) :=
    hgabs _ (by
      have e : -g * ((ya - yb / 16 - t) / 16) = -(g * (ya - yb / 16 - t)) / 16 := by ring
      rw [e]; linarith)
  have hsg : g * (ya - xa) + g * (yb - xb) ≤ |ya - xa| + |yb - xb| :=
    add_le_add (hgle _) (hgle _)
  have hcs : regCoeff p params.σ₀ s * (g * (ya - xa) + g * (yb - xb)) ≤
      regCoeff p params.σ₀ s * (|ya - xa| + |yb - xb|) := mul_le_mul_of_nonneg_left hsg hc0
  -- the order-`2` witnesses: maximizers
  have hSc : ∀ z : ℝ², IsClosed {e : ℝ² | z + e ∈ Box.square} := fun z =>
    Box.isClosed_square.preimage (continuous_const.add continuous_id)
  have hς1 : params.ς ≤ 1 := params.ς_le_one
  obtain ⟨w₀, hw₀, -⟩ := exists_isApproxMeasureStep_eq (ftaylorSeries ℝ
    (Constrained.targetMerit objG Box.con t) (pt xa xb)) 2 (hSc _) (h0S hxa hxb) hς1
  obtain ⟨wm, hwm, hwm'⟩ := exists_isApproxMeasureStep_eq (ftaylorSeries ℝ
    (Optimization.regularizedModel (ftaylorSeries ℝ (Constrained.targetMerit objG Box.con t)
      (pt xa xb)) p params.σ₀) s) 2 (hSc (pt xa xb + s)) (by rw [hxs]; exact h0S hya hyb) hς1
  obtain ⟨w₁, hw₁, hw₁'⟩ := exists_isApproxMeasureStep_eq (ftaylorSeries ℝ
    (Constrained.targetMerit objG Box.con t) (pt xa xb + s)) 2 (hSc (pt xa xb + s))
    (by rw [hxs]; exact h0S hya hyb) hς1
  have hj12 : ∀ j ∈ Finset.Icc 1 q, j = 1 ∨ (j = 2 ∧ 2 ≤ q) := fun j hj => by
    have := Finset.mem_Icc.1 hj; omega
  have hgsum : g * (ya ^ 3 / 2 + (ya - yb / 16 - t)) - g * (ya - yb / 16 - t) / 16 ≤
      T₁ / 4 := by
    have : 0 ≤ 1 / 10 ^ 6 * (|ya - xa| + |yb - xb|) ^ 4 / 24 := by positivity
    linarith
  -- order-2 bounds
  have hm2 : Optimization.decrementMeasure ((ftaylorSeries ℝ (Optimization.regularizedModel
      (ftaylorSeries ℝ (Constrained.targetMerit objG Box.con t) (pt xa xb)) p params.σ₀)
        s).taylorDecrement 2) 1 {e | pt xa xb + s + e ∈ Box.square} ≤ T₂ / 16 := by
    refine Optimization.decrementMeasure_le ⟨0, mem_closedBall_self zero_le_one,
      by rw [hxs]; exact h0S hya hyb⟩ fun d hd => ?_
    have hd1 : ‖d‖ ≤ 1 := mem_closedBall_zero_iff.1 hd.1
    have h2 := taylorDecrement_two_model_le hp (σ := params.σ₀) (by rw [hσ]; norm_num) (pt xa xb)
        t hs1 hd1
    have h1 := lin_le (-(ya ^ 3 / 2 + (ya - yb / 16 - t)) - regCoeff p params.σ₀ s * (ya - xa))
      ((ya - yb / 16 - t) / 16 - regCoeff p params.σ₀ s * (yb - xb)) hd1
    rw [← hΔm, hab0, hab1] at h1
    have h3 : ‖s‖ ^ 3 ≤ (|ya - xa| + |yb - xb|) ^ 3 := pow_le_pow_left₀ (norm_nonneg _) hsL 3
    have e : -g * (-(ya ^ 3 / 2 + (ya - yb / 16 - t)) - regCoeff p params.σ₀ s * (ya - xa)) +
        -g * ((ya - yb / 16 - t) / 16 - regCoeff p params.σ₀ s * (yb - xb)) =
        g * (ya ^ 3 / 2 + (ya - yb / 16 - t)) - g * (ya - yb / 16 - t) / 16 +
          regCoeff p params.σ₀ s * (g * (ya - xa) + g * (yb - xb)) := by ring
    rw [e] at h1
    have h4 : params.σ₀ * ‖s‖ ^ 3 / 2 ≤ 1 / 10 ^ 6 * (|ya - xa| + |yb - xb|) ^ 3 / 2 := by
      rw [hσ]; gcongr
    linarith
  have hμ2 : Optimization.decrementMeasure ((ftaylorSeries ℝ (Constrained.targetMerit objG Box.con
      t)
      (pt xa xb + s)).taylorDecrement 2) 1 {e | pt xa xb + s + e ∈ Box.square} ≤ T₁ / 4 := by
    refine Optimization.decrementMeasure_le ⟨0, mem_closedBall_self zero_le_one,
      by rw [hxs]; exact h0S hya hyb⟩ fun d hd => ?_
    have hd1 : ‖d‖ ≤ 1 := mem_closedBall_zero_iff.1 hd.1
    have h2 := taylorDecrement_two_le (pt xa xb + s) d t
    have h1 := lin_le (-(ya ^ 3 / 2 + (ya - yb / 16 - t))) ((ya - yb / 16 - t) / 16) hd1
    rw [← hΔ', hab0', hab1'] at h1
    have e : -g * -(ya ^ 3 / 2 + (ya - yb / 16 - t)) + -g * ((ya - yb / 16 - t) / 16) =
        g * (ya ^ 3 / 2 + (ya - yb / 16 - t)) - g * (ya - yb / 16 - t) / 16 := by ring
    rw [e] at h1
    linarith
  refine isARqpCallOut_one_step G hq1 (by omega) (P := params) (fun j hj => ?_)
    hmemx (by rw [hxs]; exact hmemy) (by linarith) (taylorSum_targetMerit hp _ t)
    ⟨0, forall_mem_image.2 fun _ _ => Constrained.targetMerit_nonneg⟩ ?_
    (d₀ := fun j => if j = 1 then pt (-1 / 2) (1 / 2) else w₀) ?_ ⟨1, by simp; omega, ?_⟩
    (dm := fun j => if j = 1 then pt (-g / 2) (-g / 2) else wm) ?_
    (d₁ := fun j => if j = 1 then pt (-g / 2) (-g / 2) else w₁) ?_ ?_
  · rcases hj12 j hj with rfl | ⟨rfl, h2⟩
    · rw [hT]; exact ⟨hT0, hT1⟩
    · rw [hT2 h2]; exact ⟨hT20, hT21⟩
  · -- the model decreases
    rw [Optimization.regularizedModel_def, taylorSum_targetMerit hp, hxs, targetMerit_eq,
        targetMerit_eq]
    simp only [pt_zero, obj_pt]
    rw [hσ]
    have := reg_le hp (σ := params.σ₀) (by rw [hσ]; norm_num) hs1
    have h5 : ‖s‖ ^ 5 ≤ (|ya - xa| + |yb - xb|) ^ 5 := pow_le_pow_left₀ (norm_nonneg _) hsL 5
    rw [hσ] at this
    linarith
  · -- Step 1 at `x`: the witnesses
    intro j hj
    rcases hj12 j hj with rfl | ⟨rfl, -⟩
    · simp only [↓reduceIte]
      refine isApproxMeasureStep_lin (a := -(xa ^ 3 / 2 + (xa - xb / 16 - t))) (b := (xa - xb / 16
          - t) / 16)
        (fun d => by rw [taylorDecrement_one_eq, obj_pt]; simp only [pt_zero]) (h0S hxa hxb)
        (norm_pt_le hhalf' hhalf) (hS hxa hxb hhalf' hhalf) ?_
      rw [taylorDecrement_one_eq, obj_pt]
      simp only [pt_zero, pt_one]
      rw [abs_neg, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
      linarith
    · simpa using hw₀
  · -- Step 1 fails at `x`
    simp only [↓reduceIte]
    rw [taylorDecrement_one_eq, obj_pt, hς, hT]
    simp only [pt_zero, pt_one]
    norm_num
    linarith
  · -- the model witnesses at `s`
    intro j hj
    rcases hj12 j hj with rfl | ⟨rfl, hq2'⟩
    · simp only [↓reduceIte]
      refine ⟨?_, ?_⟩
      · rw [hς]
        refine isApproxMeasureStep_lin hΔm (by rw [hxs]; exact h0S hya hyb) (norm_pt_le hgw hgw)
          (by rw [hxs]; exact hS hya hyb hgw hgw) ?_
        rw [hΔm, hab0, hab1]
        simp only [pt_zero, pt_one]
        ring_nf
        exact le_rfl
      · rw [hΔm, hς, hθ, hT]
        simp only [pt_zero, pt_one]
        have e : (-(ya ^ 3 / 2 + (ya - yb / 16 - t)) - regCoeff p params.σ₀ s * (ya - xa)) * (-g /
            2) +
            ((ya - yb / 16 - t) / 16 - regCoeff p params.σ₀ s * (yb - xb)) * (-g / 2) =
            (g * (ya ^ 3 / 2 + (ya - yb / 16 - t)) - g * (ya - yb / 16 - t) / 16 +
              regCoeff p params.σ₀ s * (g * (ya - xa) + g * (yb - xb))) / 2 := by ring
        rw [e]
        norm_num
        linarith
    · simp only [show (2 : ℕ) ≠ 1 by norm_num, ↓reduceIte]
      refine ⟨hwm, ?_⟩
      rw [hwm', hς, hθ, hT2 hq2']
      norm_num
      linarith
  · -- Step 1 at `x + s`: the witnesses
    intro j hj
    rcases hj12 j hj with rfl | ⟨rfl, -⟩
    · simp only [↓reduceIte]
      rw [hς]
      refine isApproxMeasureStep_lin hΔ' (by rw [hxs]; exact h0S hya hyb) (norm_pt_le hgw hgw)
        (by rw [hxs]; exact hS hya hyb hgw hgw) ?_
      rw [hΔ', hab0', hab1']
      simp only [pt_zero, pt_one]
      ring_nf
      exact le_rfl
    · simpa using hw₁
  · -- Step 1 holds at `x + s`
    intro j hj
    rcases hj12 j hj with rfl | ⟨rfl, h2⟩
    · simp only [↓reduceIte]
      rw [hΔ', hς, hT]
      simp only [pt_zero, pt_one]
      have e : -(ya ^ 3 / 2 + (ya - yb / 16 - t)) * (-g / 2) + (ya - yb / 16 - t) / 16 * (-g / 2) =
          (g * (ya ^ 3 / 2 + (ya - yb / 16 - t)) - g * (ya - yb / 16 - t) / 16) / 2 := by ring
      rw [e]
      norm_num
      linarith
    · simp only [show (2 : ℕ) ≠ 1 by norm_num, ↓reduceIte]
      rw [hw₁', hς, hT2 h2]
      norm_num
      have : 0 ≤ 1 / 10 ^ 6 * (|ya - xa| + |yb - xb|) ^ 3 / 2 := by positivity
      linarith

/-! ### The run -/

/-- The **tolerances** $\varepsilon_0 = u^2/2 + u^3/2$, $\varepsilon_1 = 3u/2$ and
$\varepsilon_j = 1$ for $j \ge 2$, for a parameter $u \in \mathbb{R}$. -/
noncomputable def tol (u : ℝ) (j : ℕ) : ℝ :=
  if j = 0 then u ^ 2 / 2 + u ^ 3 / 2 else if j = 1 then 3 * u / 2 else 1

/-- $\varepsilon_0 = u^2/2 + u^3/2$. -/
theorem tol_zero {u : ℝ} : tol u 0 = u ^ 2 / 2 + u ^ 3 / 2 := by simp [tol]

/-- $\varepsilon_1 = 3u/2$. -/
theorem tol_one {u : ℝ} : tol u 1 = 3 * u / 2 := by simp [tol]

/-- $\varepsilon_2 = 1$. -/
theorem tol_two {u : ℝ} : tol u 2 = 1 := by simp [tol]

/-- For $u > 0$, the tolerances are positive: $\varepsilon_j > 0$ for every $j$. -/
theorem tol_pos {u : ℝ} (hu : 0 < u) (j : ℕ) : 0 < tol u j := by
  unfold tol; split_ifs <;> positivity

/-- For $0 < u \le 1/7$, the tolerances are at most $1$: $\varepsilon_j \le 1$ for every $j$. -/
theorem tol_le_one {u : ℝ} (hu : 0 < u) (hu7 : u ≤ 1 / 7) (j : ℕ) : tol u j ≤ 1 := by
  unfold tol; split_ifs <;> nlinarith [pow_pos hu 2, pow_pos hu 3]


section Run

variable (u : ℝ) (M : ℕ)

/-- The overshoot $E_k = \tfrac{u^3}{2} \bigl(1 - k/(64 (M + 1))\bigr)$: the $k$-th call ends this
far below its target, for $k \le M$. -/
noncomputable def overshoot (k : ℕ) : ℝ := u ^ 3 / 2 * (1 - k / (64 * (M + 1)))

/-- The **targets**
$$t_k = -\varepsilon_0 - u^3 (k - 1) + \frac{u^3 k (k - 1)}{128 (M + 1)}, \qquad \varepsilon_0 =
  u^2/2 + u^3/2.$$

They satisfy $t_{k+1} = t_k - 2 E_k$ (`Constrained.TwoPhaseExample.BoxARqp.target_succ`). -/
noncomputable def target (k : ℕ) : ℝ :=
  -(u ^ 2 / 2 + u ^ 3 / 2) - u ^ 3 * ((k : ℝ) - 1) + u ^ 3 * ((k : ℝ) * (k - 1)) / (128 * (M + 1))

/-- The amount $f(x_{M+2}) - t_{M+1} = 27 u^3/128 = (3u/4)^3/2$ by which the last call ends above
its target. -/
noncomputable def finalGap : ℝ := 27 * u ^ 3 / 128

open Classical in
/-- The first coordinate $a_k$ of the point reached by the $k$-th call: $u$ for $k \le M$, and
$-3u/4$ for $k > M$. -/
noncomputable def landFst (k : ℕ) : ℝ := if k ≤ M then u else -3 * u / 4

open Classical in
/-- The value $F_k = f(x_{k+1}) - t_k$ at the end of the $k$-th call: $-E_k$ for $k \le M$, and
$27 u^3/128$ for $k > M$. -/
noncomputable def landGap (k : ℕ) : ℝ := if k ≤ M then -overshoot u M k else finalGap u

/-- The **outer iterates**: $x_1 = (0, 0)$, and $x_{k+1} = (a_k, 16 (a_k - t_k - F_k))$ for
$k \ge 1$, with $a_k$ of `Constrained.TwoPhaseExample.BoxARqp.landFst` and $F_k$ of
`Constrained.TwoPhaseExample.BoxARqp.landGap`. Then $f(x_{k+1}) = t_k + F_k$.

The unused value at $k = 0$ is also $(0, 0)$. -/
noncomputable def iter : ℕ → ℝ²
  | 0 => pt 0 0
  | k + 1 => if k = 0 then pt 0 0 else
      pt (landFst u M k) (16 * (landFst u M k - target u M k - landGap u M k))

/-- The **Phase-2 data** of the run: the outer iterates of
`Constrained.TwoPhaseExample.BoxARqp.iter`, the targets of
`Constrained.TwoPhaseExample.BoxARqp.target`, all optimality radii equal to $1$, and for each
$k$ an inner call that makes one successful iteration, from $x_k$ to $x_{k+1}$.

It is `Constrained.HighOrderTargetSeq.oneStep`. -/
noncomputable def seq : HighOrderTargetSeq ℝ² := HighOrderTargetSeq.oneStep (iter u M) (target u M)

end Run

section Facts

variable {u : ℝ} {M : ℕ}

/-- $t_1 = -\varepsilon_0$. -/
theorem target_one : target u M 1 = -(u ^ 2 / 2 + u ^ 3 / 2) := by simp [target]

/-- The target update of case (b): $t_{k+1} = t_k - 2 E_k$ for every $k$. -/
theorem target_succ (k : ℕ) : target u M (k + 1) = target u M k - 2 * overshoot u M k := by
  unfold target overshoot
  have : (64 * ((M : ℝ) + 1)) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- $x_1 = (0, 0)$. -/
theorem iter_one : iter u M 1 = pt 0 0 := by simp [iter]

/-- $x_{k+1} = (a_k, 16 (a_k - t_k - F_k))$ for $k \ge 1$, with $a_k$ of
`Constrained.TwoPhaseExample.BoxARqp.landFst` and $F_k$ of
`Constrained.TwoPhaseExample.BoxARqp.landGap`. -/
theorem iter_succ {k : ℕ} (hk : 1 ≤ k) :
    iter u M (k + 1) = pt (landFst u M k) (16 * (landFst u M k - target u M k - landGap u M k)) :=
        by
  simp [iter, show k ≠ 0 by omega]

/-- $f(x_{k+1}) = t_k + F_k$ for $k \ge 1$, with $F_k$ of
`Constrained.TwoPhaseExample.BoxARqp.landGap`. -/
theorem obj_iter_succ {k : ℕ} (hk : 1 ≤ k) :
    objG (iter u M (k + 1)) = target u M k + landGap u M k := by
  rw [iter_succ hk, obj_pt]; ring

/-- $a_k = u$ for $k \le M$. -/
theorem landFst_of_le {k : ℕ} (hk : k ≤ M) : landFst u M k = u := by simp [landFst, hk]

/-- $F_k = -E_k$ for $k \le M$. -/
theorem landGap_of_le {k : ℕ} (hk : k ≤ M) : landGap u M k = -overshoot u M k := by simp [landGap,
    hk]

/-- $a_{M+1} = -3u/4$. -/
theorem landFst_last : landFst u M (M + 1) = -3 * u / 4 := by simp [landFst]

/-- $F_{M+1} = 27 u^3/128$. -/
theorem landGap_last : landGap u M (M + 1) = finalGap u := by simp [landGap]

/-- For $k \in [1, M]$, $x_{k+1} = (u, 16 (u - t_k + E_k))$. -/
theorem iter_mid {k : ℕ} (hk1 : 1 ≤ k) (hkM : k ≤ M) :
    iter u M (k + 1) = pt u (16 * (u - target u M k + overshoot u M k)) := by
  rw [iter_succ hk1, landFst_of_le hkM, landGap_of_le hkM]; ring_nf

/-- The last iterate is $x_{M+2} = (-3u/4, 16 (-3u/4 - t_{M+1} - 27u^3/128))$. -/
theorem iter_last : iter u M (M + 1 + 1) =
    pt (-3 * u / 4) (16 * (-3 * u / 4 - target u M (M + 1) - finalGap u)) := by
  rw [iter_succ (by omega), landFst_last, landGap_last]

/-- For $k \in [1, M]$, $f(x_{k+1}) - t_{k+1} = E_k$: the call $k + 1$ starts this far above its
target. -/
theorem obj_iter_sub_target {k : ℕ} (hk1 : 1 ≤ k) (hkM : k ≤ M) :
    objG (iter u M (k + 1)) - target u M (k + 1) = overshoot u M k := by
  rw [obj_iter_succ hk1, landGap_of_le hkM, target_succ]; ring

variable (hu : 0 < u)
include hu

/-- For $u > 0$, $E_k \le u^3/2$ for every $k$. -/
theorem overshoot_le (k : ℕ) : overshoot u M k ≤ u ^ 3 / 2 := by
  unfold overshoot
  have : 0 ≤ (k : ℝ) / (64 * (M + 1)) := by positivity
  have : 0 < u ^ 3 / 2 := by positivity
  nlinarith

/-- For $u > 0$, $E_k \ge \tfrac{63}{64} \cdot \tfrac{u^3}{2}$ for $k \le M + 1$. -/
theorem le_overshoot {k : ℕ} (hk : k ≤ M + 1) : 63 / 64 * (u ^ 3 / 2) ≤ overshoot u M k := by
  unfold overshoot
  have hN : (0 : ℝ) < 64 * (M + 1) := by positivity
  have : (k : ℝ) / (64 * (M + 1)) ≤ 1 / 64 := by
    rw [div_le_iff₀ hN]
    have : (k : ℝ) ≤ M + 1 := by exact_mod_cast hk
    linarith
  have : 0 < u ^ 3 / 2 := by positivity
  nlinarith

/-- For $u > 0$, $E_k - E_{k+1} = u^3 / (128 (M + 1))$ for every $k$. -/
theorem overshoot_sub (k : ℕ) : overshoot u M k - overshoot u M (k + 1) = u ^ 3 / (128 * (M + 1))
    := by
  unfold overshoot
  have : (64 * ((M : ℝ) + 1)) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- For $u > 0$ and $k \in [1, M + 1]$, $-\varepsilon_0 - u^3 (k - 1) \le t_k \le -\varepsilon_0$.
-/
theorem target_mem {k : ℕ} (hk1 : 1 ≤ k) (hkM : k ≤ M + 1) :
    -(u ^ 2 / 2 + u ^ 3 / 2) - u ^ 3 * ((k : ℝ) - 1) ≤ target u M k ∧
      target u M k ≤ -(u ^ 2 / 2 + u ^ 3 / 2) := by
  unfold target
  have hN : (0 : ℝ) < 128 * (M + 1) := by positivity
  have hK1 : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hKM : (k : ℝ) ≤ M + 1 := by exact_mod_cast hkM
  have hu3 : 0 < u ^ 3 := by positivity
  have h0 : 0 ≤ u ^ 3 * ((k : ℝ) * (k - 1)) / (128 * (M + 1)) := by
    apply div_nonneg _ hN.le
    apply mul_nonneg hu3.le
    nlinarith
  have h1 : u ^ 3 * ((k : ℝ) * (k - 1)) / (128 * (M + 1)) ≤ u ^ 3 * ((k : ℝ) - 1) := by
    rw [div_le_iff₀ hN]
    have : ((k : ℝ) * (k - 1)) ≤ ((k : ℝ) - 1) * (128 * (M + 1)) := by nlinarith
    nlinarith
  constructor <;> linarith

end Facts

/-! ### The inner calls of the run are ARqp calls -/

/-- $\|r((a, b), t)\|^2 = (a^2/2)^2 + (a - b/16 - t)^2$. -/
theorem targetResidual_sq_pt (a b t : ℝ) :
    Constrained.targetResidual objG Box.con t (pt a b) ^ 2 =
      (a ^ 2 / 2) ^ 2 + (a - b / 16 - t) ^ 2 := by
  rw [Constrained.targetResidual_sq, Box.norm_con, obj_pt, pt_zero]

/-- The numerical inequality that shows that the Step-1 test fails at the start of the calls
$k \ge 2$. -/
private theorem num_fail {u E R : ℝ} (hu : 0 < u) (hu' : u ≤ 1 / 200) (hE0 : 0 ≤ E)
    (hE2 : E ≤ u ^ 3 / 2) (hRhi : R ≤ u ^ 2 / 2 + E) :
    1 / 2 * R * (3 * u / 2) < u ^ 3 / 2 + E + E / 16 := by
  have hu2 : u ^ 2 ≤ u / 200 := by nlinarith
  have : R * u ≤ (u ^ 2 / 2 + u ^ 3 / 2) * u := mul_le_mul_of_nonneg_right (by linarith) hu.le
  nlinarith [pow_pos hu 3]

/-- The numerical inequalities that `Constrained.TwoPhaseExample.BoxARqp.isARqpCallOut_step` needs
for the middle calls. -/
private theorem num_mid {u E E' R : ℝ} (hu : 0 < u) (hu' : u ≤ 1 / 200)
    (hE1 : 63 / 64 * (u ^ 3 / 2) ≤ E) (hE2 : E ≤ u ^ 3 / 2) (hE1' : 63 / 64 * (u ^ 3 / 2) ≤ E')
    (hE2' : E' ≤ u ^ 3 / 2) (hEE : u ^ 6 / 4 ≤ E - E') (hRlo : u ^ 2 / 2 ≤ R)
    (hRhi : R ≤ u ^ 2 / 2 + E) :
    1 / 2 * R * (3 * u / 2) < u ^ 3 / 2 + E + E / 16 ∧
    u ^ 4 / 8 + (-E') ^ 2 / 2 + 1 / 10 ^ 6 * (16 * (E + E')) ^ 5 / 120 <
      u ^ 4 / 8 + E ^ 2 / 2 ∧
    1 * (u ^ 3 / 2 + -E') - 1 * (-E') / 16 + 1 / 10 ^ 6 * (16 * (E + E')) ^ 4 / 24 ≤
      1 / 2 * R * (3 * u / 2) / 4 := by
  have hu2 : u ^ 2 ≤ u / 200 := by nlinarith
  have hu3p : 0 < u ^ 3 := by positivity
  have hS0 : 0 < E + E' := by linarith
  have hS1 : E + E' ≤ u ^ 3 := by linarith
  have hS4 : (E + E') ^ 4 ≤ (u ^ 3) ^ 4 := pow_le_pow_left₀ hS0.le hS1 4
  have hu6 : (u ^ 3) ^ 4 ≤ u ^ 6 / 1000 := by
    have : u ^ 6 ≤ 1 / 1000 := by
      have : u ^ 6 ≤ (1 / 200) ^ 6 := pow_le_pow_left₀ hu.le hu' 6
      linarith [show ((1 : ℝ) / 200) ^ 6 ≤ 1 / 1000 by norm_num]
    have e : (u ^ 3) ^ 4 = u ^ 6 * u ^ 6 := by ring
    rw [e]; nlinarith [pow_pos hu 6]
  refine ⟨?_, ?_, ?_⟩
  · have : R * u ≤ (u ^ 2 / 2 + u ^ 3 / 2) * u := mul_le_mul_of_nonneg_right (by linarith) hu.le
    nlinarith
  · have e5 : (16 * (E + E')) ^ 5 = 1048576 * (E + E') ^ 4 * (E + E') := by ring
    have h1 : (E + E') ^ 4 * (E + E') ≤ u ^ 6 / 1000 * (E + E') :=
      mul_le_mul_of_nonneg_right (hS4.trans hu6) hS0.le
    have h2 : (u ^ 6 / 4) * (E + E') ≤ (E - E') * (E + E') :=
      mul_le_mul_of_nonneg_right hEE hS0.le
    have h3 : 0 < u ^ 6 * (E + E') := by positivity
    rw [e5]
    nlinarith
  · have e4 : (16 * (E + E')) ^ 4 = 65536 * (E + E') ^ 4 := by ring
    have h6 : u ^ 6 ≤ u ^ 3 / 1000 := by
      have : u ^ 3 ≤ 1 / 1000 := by nlinarith
      nlinarith
    have : u ^ 2 / 2 * u ≤ R * u := mul_le_mul_of_nonneg_right hRlo hu.le
    rw [e4]
    nlinarith

/-- The numerical inequalities that `Constrained.TwoPhaseExample.BoxARqp.isARqpCallOut_step` needs
for the last call. -/
private theorem num_last {u E R : ℝ} (hu : 0 < u) (hu' : u ≤ 1 / 200)
    (hE1 : 63 / 64 * (u ^ 3 / 2) ≤ E) (hE2 : E ≤ u ^ 3 / 2) (hRlo : u ^ 2 / 2 ≤ R) :
    (-3 * u / 4) ^ 4 / 8 + (27 * u ^ 3 / 128) ^ 2 / 2 +
      1 / 10 ^ 6 * (7 * u / 4 + 16 * (7 * u / 4 - E + 27 * u ^ 3 / 128)) ^ 5 / 120 <
      u ^ 4 / 8 + E ^ 2 / 2 ∧
    -1 * ((-3 * u / 4) ^ 3 / 2 + 27 * u ^ 3 / 128) - -1 * (27 * u ^ 3 / 128) / 16 +
      1 / 10 ^ 6 * (7 * u / 4 + 16 * (7 * u / 4 - E + 27 * u ^ 3 / 128)) ^ 4 / 24 ≤
      1 / 2 * R * (3 * u / 2) / 4 := by
  have hu2 : u ^ 2 ≤ u / 200 := by nlinarith
  have hu3p : 0 < u ^ 3 := by positivity
  have hu3 : u ^ 3 ≤ u / 40000 := by nlinarith
  have hL0 : 0 ≤ 7 * u / 4 + 16 * (7 * u / 4 - E + 27 * u ^ 3 / 128) := by nlinarith
  have hL1 : 7 * u / 4 + 16 * (7 * u / 4 - E + 27 * u ^ 3 / 128) ≤ 30 * u := by nlinarith
  have hL5 := pow_le_pow_left₀ hL0 hL1 5
  have hL4 := pow_le_pow_left₀ hL0 hL1 4
  have e5 : (30 * u) ^ 5 = 24300000 * u ^ 5 := by ring
  have e4 : (30 * u) ^ 4 = 810000 * u ^ 4 := by ring
  have hu5 : u ^ 5 ≤ u ^ 4 / 200 := by nlinarith [pow_pos hu 4]
  have hu4 : u ^ 4 ≤ u ^ 3 / 200 := by nlinarith [pow_pos hu 3]
  have hu6 : u ^ 6 ≤ u ^ 4 / 40000 := by nlinarith [pow_pos hu 4]
  have hE0 : 0 ≤ E := by linarith
  refine ⟨?_, ?_⟩
  · have e1 : (-3 * u / 4) ^ 4 / 8 + (27 * u ^ 3 / 128) ^ 2 / 2 =
        81 / 2048 * u ^ 4 + 729 / 32768 * u ^ 6 := by ring
    rw [e1]
    nlinarith
  · have e1 : -1 * ((-3 * u / 4) ^ 3 / 2 + 27 * u ^ 3 / 128) - -1 * (27 * u ^ 3 / 128) / 16 =
        27 / 2048 * u ^ 3 := by ring
    rw [e1]
    have : u ^ 2 / 2 * u ≤ R * u := mul_le_mul_of_nonneg_right hRlo hu.le
    nlinarith

/-- The order-$2$ tolerance $T_2 = \|r\|/2$ is large enough: $T_1/4 + \sigma_0 L^3/2 \le T_2/16$. -/
private theorem num_T2 {u R L : ℝ} (hu : 0 < u) (hu' : u ≤ 1 / 200) (hR : u ^ 2 / 2 ≤ R)
    (hL0 : 0 ≤ L) (hL : L ≤ 30 * u) :
    1 / 2 * R * (3 * u / 2) / 4 + 1 / 10 ^ 6 * L ^ 3 / 2 ≤ 1 / 2 * R * 1 / 16 := by
  have h3 : L ^ 3 ≤ (30 * u) ^ 3 := pow_le_pow_left₀ hL0 hL 3
  have e : (30 * u) ^ 3 = 27000 * u ^ 3 := by ring
  have hR0 : 0 ≤ R := le_trans (by positivity) hR
  have hRu : u * R ≤ R / 200 := by nlinarith
  have hu3 : u ^ 3 ≤ u ^ 2 / 200 := by nlinarith [pow_pos hu 2]
  nlinarith

/-- The tolerances $\tfrac12 \|r(x_k, t_k)\| \varepsilon_j$ of the $k$-th inner call, which
correspond to $\beta = 1/2$. -/
noncomputable abbrev callTol (u : ℝ) (M k : ℕ) : ℕ → ℝ := fun j =>
  1 / 2 * Constrained.targetResidual objG Box.con (target u M k) (iter u M k) * tol u j

section Calls

variable {u : ℝ} {M : ℕ} (hu : 0 < u) (hu' : u ≤ 1 / 200) (hM : u ^ 3 * M ≤ 1 / 64)
  (hM1 : 1 ≤ M) {q : ℕ} (hq1 : 1 ≤ q) (hq2 : q ≤ 2)
include hu hu' hM hM1 hq1 hq2

omit hM in
/-- **The first call is a one-step ARqp call.** Let $0 < u \le 1/200$, $M \ge 1$, $q \in \{1, 2\}$
and $p \ge 4$. The first call, from $x_1 = (0, 0)$, where $f - t_1 = \varepsilon_0$, to
$x_2 = (u, \cdot)$, where $f - t_1 = -E_1$, is a call of ARqp on $\mu(\cdot, t_1)$ over $X$ with
the constants `Constrained.TwoPhaseExample.BoxARqp.params` and the tolerances
$\tfrac12 \|r(x_1, t_1)\| \varepsilon_j$, of length $1$, whose only iteration is successful and
whose returned radii are $1$. -/
theorem isARqpCallOut_first {p : ℕ} (hp : 4 ≤ p) :
    Optimization.IsARqpCallOut G (Constrained.targetMerit objG Box.con (target u M 1)) Box.square
        p q params
      (callTol u M 1) (fun i => if i = 0 then iter u M 1 else iter u M (1 + 1)) 1
      (fun _ => True) (fun _ => 1) := by
  set e0 := u ^ 2 / 2 + u ^ 3 / 2 with he0
  set E := overshoot u M 1 with hE
  have hE1 : 63 / 64 * (u ^ 3 / 2) ≤ E := le_overshoot hu (by omega)
  have hE2 : E ≤ u ^ 3 / 2 := overshoot_le hu 1
  have ht : target u M 1 = -e0 := target_one
  have hx2 : iter u M (1 + 1) = pt u (16 * (u + e0 + E)) := by
    rw [iter_mid le_rfl hM1, ht, ← hE]; congr 1; ring
  have hR : Constrained.targetResidual objG Box.con (target u M 1) (iter u M 1) = e0 := by
    have hsq := targetResidual_sq_pt 0 0 (target u M 1)
    rw [← iter_one (u := u) (M := M), ht] at hsq
    have h0 := Constrained.targetResidual_nonneg (f := objG) (c := Box.con) (t := target u M 1)
      (x := iter u M 1)
    rw [ht] at h0 ⊢
    have : 0 < e0 := by positivity
    nlinarith [sq_nonneg (Constrained.targetResidual objG Box.con (-e0) (iter u M 1) - e0)]
  have hT : callTol u M 1 1 = 1 / 2 * e0 * (3 * u / 2) := by
    simp only [callTol, hR, tol_one]
  have hu2 : u ^ 2 ≤ u / 200 := by nlinarith
  have hu3 : u ^ 3 ≤ u ^ 2 / 200 := by nlinarith
  have hu4 : u ^ 4 ≤ u ^ 3 / 200 := by nlinarith
  have hu3p : 0 < u ^ 3 := by positivity
  have hW0 : 0 ≤ 16 * (u + e0 + E) := by
    have : 0 ≤ E := by linarith
    positivity
  have hW1 : 16 * (u + e0 + E) ≤ 17 * u := by nlinarith
  have hL : |u - 0| + |16 * (u + e0 + E) - 0| ≤ 18 * u := by
    rw [sub_zero, sub_zero, abs_of_pos hu, abs_of_nonneg hW0]; linarith
  have hL0 : 0 ≤ |u - 0| + |16 * (u + e0 + E) - 0| := by positivity
  have hL5 : (|u - 0| + |16 * (u + e0 + E) - 0|) ^ 5 ≤ (18 * u) ^ 5 :=
    pow_le_pow_left₀ hL0 hL 5
  have hL4 : (|u - 0| + |16 * (u + e0 + E) - 0|) ^ 4 ≤ (18 * u) ^ 4 :=
    pow_le_pow_left₀ hL0 hL 4
  have hFy : u - 16 * (u + e0 + E) / 16 - target u M 1 = -E := by rw [ht]; ring
  have hFx : (0 : ℝ) - 0 / 16 - target u M 1 = e0 := by rw [ht]; ring
  rw [iter_one, hx2]
  have hT2 : 2 ≤ q → callTol u M 1 2 = 1 / 2 * e0 * 1 := fun _ => by
    simp only [callTol, hR, tol_two]
  have he0lo : u ^ 2 / 2 ≤ e0 := by linarith
  refine isARqpCallOut_step hp hq1 hq2 (t := target u M 1) (g := 1) hT hT2 (by positivity)
    (by linarith) (num_T2 hu hu' he0lo hL0 (by linarith)) (by norm_num) (by norm_num)
    (by rw [abs_of_pos hu]; linarith) (by rw [abs_of_nonneg hW0]; linarith) (by linarith)
    (by positivity) (by nlinarith) (by rw [hFx]; positivity) le_rfl ?_ ?_ (Or.inl rfl) ?_ ?_
    (by linarith) (by linarith) ?_
  · rw [hFx]; nlinarith
  · rw [hFy, hFx]
    have h5 : (18 * u) ^ 5 = 1889568 * u ^ 5 := by ring
    have hE6 : E ^ 2 ≤ u ^ 6 / 4 := by nlinarith
    have he2 : e0 ^ 2 = u ^ 4 / 4 + u ^ 5 / 2 + u ^ 6 / 4 := by rw [he0]; ring
    have : (0 : ℝ) ^ 4 = 0 := by norm_num
    nlinarith
  · rw [hFy]; linarith
  · rw [hFy]; linarith
  · rw [hFy]
    have h4 : (18 * u) ^ 4 = 104976 * u ^ 4 := by ring
    nlinarith

omit hq1 hq2 in
/-- Let $0 < u \le 1/200$, $M \ge 1$ and $u^3 M \le 1/64$. Then $u^3 (M + 1) \le 1/32$, so
$E_k - E_{k+1} = u^3/(128 (M + 1)) \ge u^6/4$. -/
theorem overshoot_sub_ge : u ^ 6 / 4 ≤ u ^ 3 / (128 * (M + 1)) := by
  have hN : (0 : ℝ) < 128 * (M + 1) := by positivity
  rw [le_div_iff₀ hN]
  have hu3 : u ^ 3 ≤ 1 / 64 := by nlinarith [pow_pos hu 2]
  have : u ^ 3 * ((M : ℝ) + 1) ≤ 1 / 32 := by nlinarith
  nlinarith [pow_pos hu 3]


/-- **The middle calls are one-step ARqp calls.** Let $0 < u \le 1/200$, $M \ge 1$,
$u^3 M \le 1/64$, $q \in \{1, 2\}$ and $p \ge 4$, and let $j \ge 1$ with $j + 1 \le M$. The call
$k = j + 1$, from $x_k = (u, \cdot)$, where $f - t_k = E_j$, to $x_{k+1} = (u, \cdot)$, where
$f - t_k = -E_{j+1}$, is a call of ARqp on $\mu(\cdot, t_k)$ over $X$ with the constants
`Constrained.TwoPhaseExample.BoxARqp.params` and the tolerances
$\tfrac12 \|r(x_k, t_k)\| \varepsilon_i$, of length $1$, whose only iteration is successful and
whose returned radii are $1$. -/
theorem isARqpCallOut_mid {p : ℕ} (hp : 4 ≤ p) {j : ℕ} (hj1 : 1 ≤ j) (hjM : j + 1 ≤ M) :
    Optimization.IsARqpCallOut G (Constrained.targetMerit objG Box.con (target u M (j + 1)))
        Box.square p q params
      (callTol u M (j + 1)) (fun i => if i = 0 then iter u M (j + 1) else iter u M (j + 1 + 1)) 1
      (fun _ => True) (fun _ => 1) := by
  set E := overshoot u M j with hE
  set E' := overshoot u M (j + 1) with hE'
  set t := target u M j with ht
  have hE1 : 63 / 64 * (u ^ 3 / 2) ≤ E := le_overshoot hu (by omega)
  have hE2 : E ≤ u ^ 3 / 2 := overshoot_le hu j
  have hE1' : 63 / 64 * (u ^ 3 / 2) ≤ E' := le_overshoot hu (by omega)
  have hE2' : E' ≤ u ^ 3 / 2 := overshoot_le hu (j + 1)
  have hEE : u ^ 6 / 4 ≤ E - E' := by
    rw [hE, hE', overshoot_sub hu]; exact overshoot_sub_ge hu hu' hM hM1
  have ht' : target u M (j + 1) = t - 2 * E := target_succ j
  obtain ⟨htlo, hthi⟩ := target_mem hu (u := u) (M := M) hj1 (by omega)
  rw [← ht] at htlo hthi
  have hjM' : u ^ 3 * ((j : ℝ) - 1) ≤ 1 / 64 := by
    have : ((j : ℝ) - 1) ≤ M := by
      have : (j : ℝ) ≤ M := by exact_mod_cast (show j ≤ M by omega)
      linarith
    nlinarith [pow_pos hu 3]
  set A := 16 * (u - t + E) with hA
  have hx1 : iter u M (j + 1) = pt u A := by rw [iter_mid hj1 (by omega)]
  have hx2 : iter u M (j + 1 + 1) = pt u (A + 16 * (E + E')) := by
    rw [iter_mid (by omega) hjM, ht', hA, ← hE']; congr 1; ring
  have hFx : u - A / 16 - target u M (j + 1) = E := by rw [ht', hA]; ring
  have hFy : u - (A + 16 * (E + E')) / 16 - target u M (j + 1) = -E' := by rw [ht', hA]; ring
  have hu2 : u ^ 2 ≤ u / 200 := by nlinarith
  have hu2p : 0 ≤ u ^ 2 := by positivity
  have hu3p : 0 < u ^ 3 := by positivity
  have hu3s : u ^ 3 ≤ 1 / 1000 := by nlinarith
  have hR := targetResidual_sq_pt u A (target u M (j + 1))
  rw [hFx] at hR
  obtain ⟨hRlo, hRhi⟩ := Real.le_and_le_add_of_sq_eq_add_sq Constrained.targetResidual_nonneg hR (by
      positivity)
    (by linarith)
  set R := Constrained.targetResidual objG Box.con (target u M (j + 1)) (pt u A) with hRdef
  have hT : callTol u M (j + 1) (1 : ℕ) = 1 / 2 * R * (3 * u / 2) := by
    simp only [callTol, hx1, tol_one, ← hRdef]
  have hA0 : 0 ≤ A := by rw [hA]; linarith
  have hA1 : A ≤ 3 / 8 := by rw [hA]; linarith
  have hS0 : 0 ≤ E + E' := by linarith
  have hL : |u - u| + |A + 16 * (E + E') - A| = 16 * (E + E') := by
    rw [sub_self, abs_zero, zero_add, add_sub_cancel_left, abs_of_nonneg (by linarith)]
  obtain ⟨n1, n2, n3⟩ := num_mid hu hu' hE1 hE2 hE1' hE2' hEE hRlo hRhi
  have hR0 : 0 < R := lt_of_lt_of_le (by positivity) hRlo
  have hT0 : 0 < 1 / 2 * R * (3 * u / 2) := by positivity
  have hT1 : 1 / 2 * R * (3 * u / 2) ≤ 1 := by
    have : R * u ≤ 1 * 1 := mul_le_mul (by linarith) (by linarith) hu.le zero_le_one
    linarith
  rw [hx1, hx2]
  have hT2 : 2 ≤ q → callTol u M (j + 1) 2 = 1 / 2 * R * 1 := fun _ => by
    rw [callTol, tol_two, hx1]
  have hu3u : u ^ 3 ≤ u := pow_le_of_le_one hu.le (by linarith) (by norm_num)
  exact isARqpCallOut_step hp hq1 hq2 (t := target u M (j + 1)) (g := 1) hT hT2 (by positivity)
    (by linarith) (num_T2 hu hu' hRlo (by rw [hL]; linarith) (by rw [hL]; linarith))
    (by rw [abs_of_pos hu]; linarith)
    (by rw [abs_of_nonneg hA0]; linarith) (by rw [abs_of_pos hu]; linarith)
    (by rw [abs_of_nonneg (by linarith)]; linarith) (by rw [hL]; linarith)
    hT0 hT1 (by rw [hFx]; linarith) hu.le (by rw [hFx]; exact n1)
    (by rw [hFy, hFx, hL]; exact n2) (Or.inl rfl) (by rw [hFy]; linarith) (by rw [hFy]; linarith)
    (by rw [sub_self]; linarith) (by linarith) (by rw [hFy, hL]; exact n3)

/-- **The last call is a one-step ARqp call.** Let $0 < u \le 1/200$, $M \ge 1$, $u^3 M \le 1/64$,
$q \in \{1, 2\}$ and $p \ge 4$. The call $k = M + 1$, from $x_k = (u, \cdot)$, where
$f - t_k = E_M$, to $x_{k+1} = (-3u/4, \cdot)$, where $f - t_k = (3u/4)^3/2$ and the first
coordinate of $\nabla \mu(\cdot, t_k)$ vanishes, is a call of ARqp on $\mu(\cdot, t_k)$ over $X$
with the constants `Constrained.TwoPhaseExample.BoxARqp.params` and the tolerances
$\tfrac12 \|r(x_k, t_k)\| \varepsilon_j$, of length $1$, whose only iteration is successful and
whose returned radii are $1$. -/
theorem isARqpCallOut_last {p : ℕ} (hp : 4 ≤ p) :
    Optimization.IsARqpCallOut G (Constrained.targetMerit objG Box.con (target u M (M + 1)))
        Box.square p q params
      (callTol u M (M + 1)) (fun i => if i = 0 then iter u M (M + 1) else iter u M (M + 1 + 1)) 1
      (fun _ => True) (fun _ => 1) := by
  set E := overshoot u M M with hE
  set t := target u M M with ht
  have hE1 : 63 / 64 * (u ^ 3 / 2) ≤ E := le_overshoot hu (by omega)
  have hE2 : E ≤ u ^ 3 / 2 := overshoot_le hu M
  have ht' : target u M (M + 1) = t - 2 * E := target_succ M
  obtain ⟨htlo, hthi⟩ := target_mem hu (u := u) (M := M) hM1 (by omega)
  rw [← ht] at htlo hthi
  have hjM' : u ^ 3 * ((M : ℝ) - 1) ≤ 1 / 64 := by nlinarith [pow_pos hu 3]
  set A := 16 * (u - t + E) with hA
  have hx1 : iter u M (M + 1) = pt u A := by rw [iter_mid hM1 le_rfl]
  have hx2 : iter u M (M + 1 + 1) =
      pt (-3 * u / 4) (A + 16 * (-(7 * u / 4) + E - 27 * u ^ 3 / 128)) := by
    rw [iter_last, ht', hA, finalGap]; congr 1; ring
  have hFx : u - A / 16 - target u M (M + 1) = E := by rw [ht', hA]; ring
  have hFy : -3 * u / 4 - (A + 16 * (-(7 * u / 4) + E - 27 * u ^ 3 / 128)) / 16 -
      target u M (M + 1) = 27 * u ^ 3 / 128 := by rw [ht', hA]; ring
  have hu2 : u ^ 2 ≤ u / 200 := by nlinarith
  have hu2p : 0 ≤ u ^ 2 := by positivity
  have hu3p : 0 < u ^ 3 := by positivity
  have hu3s : u ^ 3 ≤ 1 / 1000 := by nlinarith
  have hu3u : u ^ 3 ≤ u / 40000 := by nlinarith
  have hR := targetResidual_sq_pt u A (target u M (M + 1))
  rw [hFx] at hR
  obtain ⟨hRlo, hRhi⟩ := Real.le_and_le_add_of_sq_eq_add_sq Constrained.targetResidual_nonneg hR (by
      positivity)
    (by linarith)
  set R := Constrained.targetResidual objG Box.con (target u M (M + 1)) (pt u A) with hRdef
  have hT : callTol u M (M + 1) (1 : ℕ) = 1 / 2 * R * (3 * u / 2) := by
    simp only [callTol, hx1, tol_one, ← hRdef]
  have hA0 : 0 ≤ A := by rw [hA]; linarith
  have hA1 : A ≤ 3 / 8 := by rw [hA]; linarith
  have hL : |-3 * u / 4 - u| + |A + 16 * (-(7 * u / 4) + E - 27 * u ^ 3 / 128) - A| =
      7 * u / 4 + 16 * (7 * u / 4 - E + 27 * u ^ 3 / 128) := by
    rw [add_sub_cancel_left, abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    ring
  obtain ⟨n2, n3⟩ := num_last hu hu' hE1 hE2 hRlo
  have n1 := num_fail hu hu' (by linarith) hE2 hRhi
  have hR0 : 0 < R := lt_of_lt_of_le (by positivity) hRlo
  have hT0 : 0 < 1 / 2 * R * (3 * u / 2) := by positivity
  have hT1 : 1 / 2 * R * (3 * u / 2) ≤ 1 := by
    have : R * u ≤ 1 * 1 := mul_le_mul (by linarith) (by linarith) hu.le zero_le_one
    linarith
  rw [hx1, hx2]
  have hT2 : 2 ≤ q → callTol u M (M + 1) 2 = 1 / 2 * R * 1 := fun _ => by
    rw [callTol, tol_two, hx1]
  have hLb : 7 * u / 4 + 16 * (7 * u / 4 - E + 27 * u ^ 3 / 128) ≤ 30 * u := by linarith
  exact isARqpCallOut_step hp hq1 hq2 (t := target u M (M + 1)) (g := -1) hT hT2 (by positivity)
    (by linarith) (num_T2 hu hu' hRlo (by rw [hL]; linarith) (by rw [hL]; exact hLb))
    (by rw [abs_of_pos hu]; linarith)
    (by rw [abs_of_nonneg hA0]; linarith) (by rw [abs_of_nonpos (by linarith)]; linarith)
    (by rw [abs_le]; constructor <;> linarith) (by rw [hL]; linarith)
    hT0 hT1 (by rw [hFx]; linarith) hu.le (by rw [hFx]; exact n1)
    (by rw [hFy, hFx, hL]; exact n2) (Or.inr rfl) (by rw [hFy]; ring_nf; exact le_rfl)
    (by rw [hFy]; linarith) (by linarith) (by linarith) (by rw [hFy, hL]; exact n3)

/-- **Every inner call of the run is a one-step ARqp call.** Let $0 < u \le 1/200$, $M \ge 1$ and
$u^3 M \le 1/64$, let $q \in \{1, 2\}$ and $p \ge 4$, and let $k \in [1, M + 1]$. The iterates
$x_k, x_{k+1}, x_{k+1}, \dots$ form a call of ARqp (`Optimization.IsARqpCallOut`) on
$\mu(\cdot, t_k)$ over $X = [-1, 1]^2$, of degree $p$ and order $q$, with the constants
`Constrained.TwoPhaseExample.BoxARqp.params` and the tolerances
$\tfrac12 \|r(x_k, t_k)\| \varepsilon_j$; the call has length $1$, its only iteration is
successful, and its returned radii are $1$.

It combines `Constrained.TwoPhaseExample.BoxARqp.isARqpCallOut_first`,
`Constrained.TwoPhaseExample.BoxARqp.isARqpCallOut_mid` and
`Constrained.TwoPhaseExample.BoxARqp.isARqpCallOut_last`. -/
theorem isARqpCallOut_run {p : ℕ} (hp : 4 ≤ p) {k : ℕ} (hk1 : 1 ≤ k) (hkM : k ≤ M + 1) :
    Optimization.IsARqpCallOut G (Constrained.targetMerit objG Box.con (target u M k)) Box.square
        p q params
      (callTol u M k) (fun i => if i = 0 then iter u M k else iter u M (k + 1)) 1
      (fun _ => True) (fun _ => 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · exact isARqpCallOut_first hu hu' hM1 hq1 hq2 hp
  rcases Nat.lt_or_ge j M with hjM | hjM
  · exact isARqpCallOut_mid hu hu' hM hM1 hq1 hq2 hp hj hjM
  · obtain rfl : j = M := by omega
    exact isARqpCallOut_last hu hu' hM hM1 hq1 hq2 hp

end Calls

/-! ### The outer run -/

section Outer

variable {u : ℝ} {M : ℕ} (hu : 0 < u) (hu' : u ≤ 1 / 200) (hM : u ^ 3 * M ≤ 1 / 64)
  (hM1 : 1 ≤ M) {q : ℕ} (hq1 : 1 ≤ q) (hq2 : q ≤ 2)

include hu hu' hM in
/-- Let $0 < u \le 1/200$ and $u^3 M \le 1/64$. The iterates $x_k$ with $k \in [1, M + 2]$ lie in
$[-1/2, 1/2]^2$, hence in $X$. -/
theorem iter_mem {k : ℕ} (hk1 : 1 ≤ k) (hkM : k ≤ M + 2) : iter u M k ∈ Box.square := by
  have hu2 : u ^ 2 ≤ u / 200 := by nlinarith
  have hu3p : 0 < u ^ 3 := by positivity
  have hu3s : u ^ 3 ≤ 1 / 1000 := by nlinarith
  have hu2p : 0 ≤ u ^ 2 := by positivity
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [iter_one]; exact Box.pt_mem_square (by norm_num) (by norm_num)
  have hE1 : 63 / 64 * (u ^ 3 / 2) ≤ overshoot u M j := le_overshoot hu (by omega)
  have hE2 : overshoot u M j ≤ u ^ 3 / 2 := overshoot_le hu j
  obtain ⟨htlo, hthi⟩ := target_mem hu (u := u) (M := M) hj (by omega)
  have hjM' : u ^ 3 * ((j : ℝ) - 1) ≤ 1 / 64 := by
    have : ((j : ℝ) - 1) ≤ M := by
      have : (j : ℝ) ≤ M + 1 := by exact_mod_cast (show j ≤ M + 1 by omega)
      linarith
    nlinarith
  rcases Nat.lt_or_ge j (M + 1) with hjM | hjM
  · rw [iter_mid hj (by omega)]
    exact Box.pt_mem_square (by rw [abs_of_pos hu]; linarith)
      (by rw [abs_le]; constructor <;> linarith)
  · obtain rfl : j = M + 1 := by omega
    rw [iter_last, finalGap]
    exact Box.pt_mem_square (by rw [abs_le]; constructor <;> linarith)
      (by rw [abs_le]; constructor <;> linarith)

omit hM hM1 in
include hu hu' in
/-- For $0 < u \le 1/200$, $\theta \varepsilon_0 \le u^2/4 + u^3/4 \le 9u^2/32$ with $\theta = 1/2$.
-/
theorem half_tol_zero_le : 1 / 2 * tol u 0 ≤ 9 * u ^ 2 / 32 := by
  rw [tol_zero]; nlinarith [pow_pos hu 2]

include hu hu' in
/-- For $0 < u \le 1/200$ and $k \ge 1$, $\|r(x_{k+1}, t_k)\| \ge \theta \varepsilon_0$ with
$\theta = 1/2$. -/
theorem half_tol_le_targetResidual_succ {k : ℕ} (hk1 : 1 ≤ k) :
    1 / 2 * tol u 0 ≤ Constrained.targetResidual objG Box.con (target u M k) (iter u M (k + 1)) :=
        by
  have hθ := half_tol_zero_le hu hu'
  have h := Constrained.norm_le_targetResidual (f := objG) (c := Box.con) (t := target u M k)
    (x := iter u M (k + 1))
  have h' : ‖Box.con (iter u M (k + 1))‖ = landFst u M k ^ 2 / 2 := by
    rw [Box.norm_con, iter_succ hk1, pt_zero]
  have hA2 : 9 * u ^ 2 / 32 ≤ landFst u M k ^ 2 / 2 := by
    unfold landFst; split_ifs
    · nlinarith [pow_pos hu 2]
    · nlinarith [pow_pos hu 2]
  linarith

include hu hu' in
/-- For $0 < u \le 1/200$ and $k \in [1, M + 1]$, $\|r(x_k, t_k)\| \ge \theta \varepsilon_0$ with
$\theta = 1/2$, at the start of every call. -/
theorem half_tol_le_targetResidual {k : ℕ} (hk1 : 1 ≤ k) (hkM : k ≤ M + 1) :
    1 / 2 * tol u 0 ≤ Constrained.targetResidual objG Box.con (target u M k) (iter u M k) := by
  have hθ := half_tol_zero_le hu hu'
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · have h := Constrained.abs_sub_le_targetResidual (f := objG) (c := Box.con) (t := target u M (0
      + 1))
      (x := iter u M (0 + 1))
    have e : objG (iter u M (0 + 1)) - target u M (0 + 1) = tol u 0 := by
      rw [zero_add, iter_one, obj_pt, target_one, tol_zero]; ring
    rw [e, abs_of_pos (tol_pos hu 0)] at h
    have := tol_pos hu 0
    linarith
  · have h := Constrained.norm_le_targetResidual (f := objG) (c := Box.con) (t := target u M (j +
      1))
      (x := iter u M (j + 1))
    have h' : ‖Box.con (iter u M (j + 1))‖ = u ^ 2 / 2 := by
      rw [Box.norm_con, iter_mid hj (by omega), pt_zero]
    nlinarith [pow_pos hu 2]

include hu hu' in
/-- For $0 < u \le 1/200$, no outer iteration $k \ge 1$ is in $\mathcal{K}_a$ for $\theta = 1/2$. -/
theorem not_isKa {k : ℕ} (hk1 : 1 ≤ k) : ¬ (seq u M).IsKa objG Box.con (1 / 2) (tol u) k :=
  not_lt.2 (half_tol_le_targetResidual_succ hu hu' hk1)

include hu hu' in
/-- For $0 < u \le 1/200$, the outer iterations $k \in [1, M]$ are in $\mathcal{K}_b$ for
$\theta = 1/2$. -/
theorem isKb {k : ℕ} (hk1 : 1 ≤ k) (hkM : k ≤ M) :
    (seq u M).IsKb objG Box.con (1 / 2) (tol u) k := by
  refine ⟨half_tol_le_targetResidual_succ hu hu' hk1, ?_⟩
  change objG (iter u M (k + 1)) < target u M k
  rw [obj_iter_succ hk1, landGap_of_le hkM]
  have := le_overshoot hu (M := M) (k := k) (by omega)
  have : 0 < u ^ 3 := by positivity
  linarith

include hu in
/-- For $u > 0$, the outer iteration $M + 1$ is not in $\mathcal{K}_b$ for $\theta = 1/2$, since
$f(x_{M+2}) > t_{M+1}$. -/
theorem not_isKb_last : ¬ (seq u M).IsKb objG Box.con (1 / 2) (tol u) (M + 1) := by
  intro h
  have h2 := h.2
  change objG (iter u M (M + 1 + 1)) < target u M (M + 1) at h2
  rw [obj_iter_succ (by omega), landGap_last, finalGap] at h2
  have : 0 < u ^ 3 := by positivity
  linarith

include hu hu' hM hq1 in
/-- Let $0 < u \le 1/200$, $u^3 M \le 1/64$ and $q \ge 1$. For $k \in [1, M]$, the criticality test
(14.3.34) of order $q$ fails at $(x_{k+1}, t_{k+1})$ with the radii $1$: along $-e_1$ the
decrease is $u^3/2 + E_k > \varepsilon_1 \|r(x_{k+1}, t_{k+1})\|$. -/
theorem not_targetCrit_succ {k : ℕ} (hk1 : 1 ≤ k) (hkM : k ≤ M) :
    ¬ targetCrit objG Box.con Box.square q (tol u) (target u M (k + 1)) (iter u M (k + 1)) (fun _
        => 1) := by
  intro h
  have h1 := h 1 (Finset.mem_Icc.2 ⟨le_rfl, hq1⟩)
  simp only [one_pow, mul_one, Nat.factorial_one, Nat.cast_one, div_one] at h1
  have hmem := iter_mem hu hu' hM (k := k + 1) (by omega) (by omega)
  have hx : iter u M (k + 1) = pt u (16 * (u - target u M k + overshoot u M k)) := iter_mid hk1 hkM
  have hS : pt (-1) 0 ∈ {d | iter u M (k + 1) + d ∈ Box.square} := by
    simp only [mem_ofPred_eq]
    rw [hx] at hmem ⊢
    rw [pt_add]
    simp only [pt_zero, pt_one, add_zero]
    obtain ⟨-, h2⟩ := hmem
    simp only [pt_one] at h2
    exact Box.pt_mem_square (by rw [abs_le]; constructor <;> linarith) h2
  have hd : pt (-1) 0 ∈ closedBall (0 : ℝ²) 1 := by
    rw [mem_closedBall_zero_iff]
    exact (norm_pt_le_add _ _).trans (by norm_num)
  have hlow := Optimization.taylorDecrement_le_taylorMeasure
    (ftaylorSeries ℝ (Constrained.targetMerit objG Box.con (target u M (k + 1))) (iter u M (k +
        1))) 1
    (δ := 1) (d := pt (-1) 0) ⟨hd, hS⟩
  have hx0 : iter u M (k + 1) 0 = u := by rw [hx, pt_zero]
  rw [taylorDecrement_one_eq, obj_iter_sub_target hk1 hkM] at hlow
  simp only [pt_zero, pt_one, hx0] at hlow
  rw [tol_one] at h1
  have hE1 := le_overshoot hu (M := M) (k := k) (by omega)
  have hE2 := overshoot_le hu (M := M) k
  have hsq := targetResidual_sq_pt u (16 * (u - target u M k + overshoot u M k)) (target u M (k +
      1))
  have hF : u - 16 * (u - target u M k + overshoot u M k) / 16 - target u M (k + 1) = overshoot u
      M k := by
    rw [target_succ]; ring
  rw [hF] at hsq
  obtain ⟨-, hRhi⟩ := Real.le_and_le_add_of_sq_eq_add_sq Constrained.targetResidual_nonneg hsq (by
      positivity)
    (by linarith)
  rw [← hx] at hRhi
  have hu2 : u ^ 2 ≤ u / 200 := by nlinarith
  have : 3 * u / 2 * Constrained.targetResidual objG Box.con (target u M (k + 1)) (iter u M (k +
      1)) ≤
      3 * u / 2 * (u ^ 2 / 2 + overshoot u M k) := by gcongr
  have : u * overshoot u M k ≤ u * (u ^ 3 / 2) := mul_le_mul_of_nonneg_left hE2 hu.le
  nlinarith [pow_pos hu 3, pow_pos hu 4]

include hu hu' hM hq2 in
/-- Let $0 < u \le 1/200$, $u^3 M \le 1/64$ and $q \le 2$. The criticality test (14.3.34) of order
$q$ holds at $(x_{M+2}, t_{M+1})$ with the radii $1$: the gradient of $\mu(\cdot, t_{M+1})$
there is $(0, -(3u/4)^3/32)$. -/
theorem targetCrit_last :
    targetCrit objG Box.con Box.square q (tol u) (target u M (M + 1)) (iter u M (M + 1 + 1)) (fun
        _ => 1) := by
  intro j hj
  have hj12 : j = 1 ∨ j = 2 := by have := Finset.mem_Icc.1 hj; omega
  simp only [one_pow, mul_one]
  have hx := iter_last (u := u) (M := M)
  set B := 16 * (-3 * u / 4 - target u M (M + 1) - finalGap u)
  have hF : -3 * u / 4 - B / 16 - target u M (M + 1) = finalGap u := by ring
  have h0 : (0 : ℝ²) ∈ {d | iter u M (M + 1 + 1) + d ∈ Box.square} := by
    simpa using iter_mem hu hu' hM (k := M + 1 + 1) (by omega) le_rfl
  have hup := decrementMeasure_lin_le (Δ := (ftaylorSeries ℝ (Constrained.targetMerit objG Box.con
    (target u M (M + 1))) (iter u M (M + 1 + 1))).taylorDecrement 1)
    (a := -((-3 * u / 4) ^ 3 / 2 + finalGap u)) (b := finalGap u / 16)
    (fun d => by rw [taylorDecrement_one_eq, hx, obj_pt, pt_zero, hF]) h0
  have h := Constrained.norm_le_targetResidual (f := objG) (c := Box.con) (t := target u M (M + 1))
    (x := iter u M (M + 1 + 1))
  have h' : ‖Box.con (iter u M (M + 1 + 1))‖ = 9 * u ^ 2 / 32 := by
    rw [Box.norm_con, hx, pt_zero]; ring
  have e : -((-3 * u / 4) ^ 3 / 2 + finalGap u) = 0 := by rw [finalGap]; ring
  rw [e, abs_zero, zero_add, abs_of_pos (by rw [finalGap]; positivity)] at hup
  have hR : 9 * u ^ 2 / 32 ≤
      Constrained.targetResidual objG Box.con (target u M (M + 1)) (iter u M (M + 1 + 1)) := by
          linarith
  rcases hj12 with rfl | rfl
  · refine (show Optimization.taylorMeasure _ 1 1 _ ≤ _ from hup).trans ?_
    rw [tol_one, finalGap]
    have : 3 * u / 2 * (9 * u ^ 2 / 32) ≤ 3 * u / 2 *
        Constrained.targetResidual objG Box.con (target u M (M + 1)) (iter u M (M + 1 + 1)) := by
      gcongr
    norm_num
    nlinarith [pow_pos hu 3]
  · have h2 : Optimization.taylorMeasure (ftaylorSeries ℝ (Constrained.targetMerit objG Box.con
        (target u M (M + 1))) (iter u M (M + 1 + 1))) 2 1 {d | iter u M (M + 1 + 1) + d ∈
            Box.square} ≤
        finalGap u / 16 := by
      refine Optimization.decrementMeasure_le ⟨0, mem_closedBall_self zero_le_one, h0⟩
        fun d hd => (taylorDecrement_two_le _ d _).trans ?_
      exact (Optimization.le_decrementMeasure
        (Optimization.bddAbove_taylorDecrement _ 1 1 _) hd).trans hup
    refine h2.trans ?_
    rw [tol_two, finalGap]
    norm_num
    nlinarith [pow_pos hu 3]

include hu hu' in
/-- For $0 < u \le 1/200$ and every $q$, Phase 2 stops at the outer iteration $M + 1$, in case (c),
for $\theta = 1/2$. -/
theorem stop_last : (seq u M).Stop objG Box.con Box.square q (1 / 2) (tol u) (M + 1) :=
  Or.inl ⟨not_isKa hu hu' (by omega), not_isKb_last hu⟩

include hu hu' hM hq1 in
/-- Let $0 < u \le 1/200$, $u^3 M \le 1/64$ and $q \ge 1$. Phase 2 does not stop at the outer
iterations $k \in [1, M]$, for $\theta = 1/2$. -/
theorem not_stop {k : ℕ} (hk1 : 1 ≤ k) (hkM : k ≤ M) :
    ¬ (seq u M).Stop objG Box.con Box.square q (1 / 2) (tol u) k := by
  rintro (⟨-, hb⟩ | ⟨-, hm⟩)
  · exact hb (isKb hu hu' hk1 hkM)
  · exact not_targetCrit_succ hu hu' hM hq1 hk1 hkM hm

include hu hu' hM hq1 in
/-- Let $0 < u \le 1/200$, $u^3 M \le 1/64$ and $q \ge 1$. No outer iteration $j \in [1, M + 1)$
terminates Phase 2, for $\theta = 1/2$. -/
theorem before_last : (seq u M).Before objG Box.con Box.square q (1 / 2) (tol u) (M + 1) :=
  fun _ hj1 hjM => not_stop hu hu' hM hq1 hj1 (by omega)

include hu hu' in
/-- For $0 < u \le 1/200$ and every $q$, every outer iteration $k$ that is reached, for
$\theta = 1/2$, satisfies $k \le M + 1$. -/
theorem le_of_before {k : ℕ} (h : (seq u M).Before objG Box.con Box.square q (1 / 2) (tol u) k) :
    k ≤ M + 1 := by
  by_contra hk
  exact h (M + 1) (by omega) (by omega) (stop_last hu hu')

include hu hu' hM hq1 in
/-- Let $0 < u \le 1/200$, $u^3 M \le 1/64$ and $q \ge 1$. Phase 2 terminates at the outer iteration
$M + 1$, for $\theta = 1/2$. -/
theorem isEnd : (seq u M).IsEnd objG Box.con Box.square q (1 / 2) (tol u) (M + 1) :=
  ⟨by omega, stop_last hu hu', before_last hu hu' hM hq1⟩

include hu hu' hM hq1 in
/-- **Phase 2 terminates exactly at $M + 1$.** Let $0 < u \le 1/200$, $u^3 M \le 1/64$ and
$q \ge 1$. For the data `Constrained.TwoPhaseExample.BoxARqp.seq u M` with $\theta = 1/2$ and
the tolerances `Constrained.TwoPhaseExample.BoxARqp.tol u`, Phase 2 terminates at the outer
iteration $k$ (`Constrained.HighOrderTargetSeq.IsEnd`) if and only if $k = M + 1$. -/
theorem isEnd_iff {k : ℕ} : (seq u M).IsEnd objG Box.con Box.square q (1 / 2) (tol u) k ↔ k = M +
    1 := by
  refine ⟨fun h => ?_, fun h => h ▸ isEnd hu hu' hM hq1⟩
  have hle := le_of_before hu hu' h.2.2
  rcases Nat.lt_or_ge k (M + 1) with hlt | hge
  · exact absurd h.2.1 (not_stop hu hu' hM hq1 h.1 (by omega))
  · omega

include hu hu' hM hM1 hq1 hq2 in
/-- **The data form a run of Phase 2.** Let $0 < u \le 1/200$, $M \ge 1$ and $u^3 M \le 1/64$, and
let $q \in \{1, 2\}$. The data `Constrained.TwoPhaseExample.BoxARqp.seq u M` form a run of Phase
2 (`Constrained.IsHighOrderTargetRun`) for the objective $f(x) = x_1 - x_2/16$, the constraint
$c$ and the set $X$, from $x_1 = (0, 0)$, with $\theta = \beta = 1/2$ and the tolerances
`Constrained.TwoPhaseExample.BoxARqp.tol u`. -/
theorem isHighOrderTargetRun :
    IsHighOrderTargetRun objG Box.con Box.square q (1 / 2) (1 / 2) (tol u) (pt 0 0) (seq u M) := by
  have hu7 : u ≤ 1 / 7 := by linarith
  have hc1 : ‖Box.con (pt 0 0)‖ = 0 := by rw [Box.norm_con]; simp
  rw [← iter_one (u := u) (M := M)]
  refine isHighOrderTargetRun_oneStep (by norm_num) (by norm_num) (by norm_num) le_rfl
    (fun j _ => tol_pos hu j) (fun j _ => tol_le_one hu hu7 j)
    (by rw [iter_one]; exact Box.pt_mem_square (by norm_num) (by norm_num)) ?_ ?_
    (fun k hk1 hk => iter_mem hu hu' hM (by omega) (by have := le_of_before hu hu' hk; omega))
    (fun k hk1 hk => ?_) (fun k hk1 hk => Optimization.IsARqpCallOut.antitone
      (isARqpCallOut_run (G := ℝ) (p := 4) hu hu' hM hM1 hq1 hq2 le_rfl hk1
        (le_of_before hu hu' hk)) 0 one_pos)
    (fun k hk1 hk => half_tol_le_targetResidual hu hu' hk1 (le_of_before hu hu' hk))
    (fun k hk1 _ ha => absurd ha (not_isKa hu hu' hk1)) fun k hk1 hk hb => ?_
  · rw [iter_one, hc1]; exact (mul_pos (by norm_num) (tol_pos hu 0)).le
  · rw [iter_one, hc1, target_one, obj_pt, tol_zero]
    rw [show (u ^ 2 / 2 + u ^ 3 / 2) ^ 2 - (0 : ℝ) ^ 2 = (u ^ 2 / 2 + u ^ 3 / 2) ^ 2 by ring,
      Real.sqrt_sq (by positivity)]
    ring
  · rcases Nat.lt_or_ge k (M + 1) with hlt | hge
    · exact Or.inr (Or.inl (isKb hu hu' hk1 (by omega)).2)
    · obtain rfl : k = M + 1 := by have := le_of_before hu hu' hk; omega
      exact Or.inr (Or.inr (targetCrit_last hu hu' hM hq2))
  · have hlt : k ≤ M := by
      by_contra h
      exact not_isKb_last hu ((show k = M + 1 by have := le_of_before hu hu' hk; omega) ▸ hb)
    rw [obj_iter_succ hk1, landGap_of_le hlt, target_succ]
    ring

include hu hu' hM hM1 hq1 hq2 in
/-- **Every inner call of the run is a one-step ARqp call.** Let $0 < u \le 1/200$, $M \ge 1$ and
$u^3 M \le 1/64$, let $q \in \{1, 2\}$ and $p \ge 4$. For every outer iteration $k \ge 1$ that
is reached, with $\theta = 1/2$, the iterates, the successful iterations and the returned radii
of the $k$-th inner call of `Constrained.TwoPhaseExample.BoxARqp.seq u M` are those of a call of
ARqp (`Optimization.IsARqpCallOut`) on $\mu(\cdot, t_k)$ over $X$ with the constants
`Constrained.TwoPhaseExample.BoxARqp.params` and the tolerances
$\tfrac12 \|r(x_k, t_k)\| \varepsilon_j$, which correspond to $\beta = 1/2$.

This is the form in which the run classes of Phase 2 with ARqp calls state their hypothesis on
the calls. It follows from `Constrained.TwoPhaseExample.BoxARqp.isARqpCallOut_run`, since every
outer iteration that is reached is at most $M + 1$. -/
theorem isARqpCallOut_calls {p : ℕ} (hp : 4 ≤ p) :
    ∀ k, 1 ≤ k → (seq u M).Before objG Box.con Box.square q (1 / 2) (tol u) k →
      Optimization.IsARqpCallOut G (Constrained.targetMerit objG Box.con ((seq u M).t k))
        Box.square p q params
        (fun j => 1 / 2 * Constrained.targetResidual objG Box.con ((seq u M).t k) ((seq u M).x k) *
          tol u j) ((seq u M).xi k) ((seq u M).e k) ((seq u M).succ k) ((seq u M).δ (k + 1)) :=
  fun _ hk1 hk => isARqpCallOut_run hu hu' hM hM1 hq1 hq2 hp hk1 (le_of_before hu hu' hk)

end Outer

/-! ### The order of the number of evaluations -/

/-- Let $\varepsilon, B > 0$, $a \in \mathbb{R}$ and $c \ge 0$. If $\varepsilon \ge B^{-a}$, then
$\varepsilon^{-c} \le B^{a c}$. -/
theorem rpow_neg_le {ε B a c : ℝ} (hε : 0 < ε) (hB : 0 < B) (h : (B ^ a)⁻¹ ≤ ε) (hc : 0 ≤ c) :
    ε ^ (-c) ≤ B ^ (a * c) := by
  have hBa : 0 < B ^ a := Real.rpow_pos_of_pos hB a
  have hi : ε⁻¹ ≤ B ^ a := by
    have := inv_anti₀ (inv_pos.2 hBa) h
    rwa [inv_inv] at this
  rw [Real.rpow_neg hε.le, ← Real.inv_rpow hε.le, Real.rpow_mul hB.le]
  exact Real.rpow_le_rpow (inv_pos.2 hε).le hi hc

/-- **One term of the order.** Let $\varepsilon_0, \varepsilon_j > 0$, $B \ge 1$, $a \in \mathbb{R}$
and $\pi \ge 1$. If $\varepsilon_0 \ge B^{-5}$, $\varepsilon_j \ge B^{-a}$ and
$5 (\pi - 1) + a \pi \le 7$, then $\varepsilon_0^{1-\pi} \varepsilon_j^{-\pi} \le B^7$. -/
theorem term_le_pow {ε₀ εj B a π : ℝ} (h0 : 0 < ε₀) (hj : 0 < εj) (hB : 1 ≤ B)
    (h0B : (B ^ (5 : ℝ))⁻¹ ≤ ε₀) (hjB : (B ^ a)⁻¹ ≤ εj) (hπ : 1 ≤ π)
    (hπ7 : 5 * (π - 1) + a * π ≤ 7) : ε₀ ^ (1 - π) * εj ^ (-π) ≤ B ^ (7 : ℝ) := by
  have hB0 : 0 < B := by linarith
  have h1 : ε₀ ^ (1 - π) ≤ B ^ (5 * (π - 1)) := by
    rw [show 1 - π = -(π - 1) by ring]; exact rpow_neg_le h0 hB0 h0B (by linarith)
  have h2 : εj ^ (-π) ≤ B ^ (a * π) := rpow_neg_le hj hB0 hjB (by linarith)
  calc ε₀ ^ (1 - π) * εj ^ (-π) ≤ B ^ (5 * (π - 1)) * B ^ (a * π) :=
        mul_le_mul h1 h2 (Real.rpow_nonneg hj.le _) (Real.rpow_nonneg hB0.le _)
    _ = B ^ (5 * (π - 1) + a * π) := (Real.rpow_add hB0 _ _).symm
    _ ≤ B ^ (7 : ℝ) := Real.rpow_le_rpow_of_exponent_le hB hπ7

/-- **The orders along the tolerances of the run.** Let $q \in \{1, 2\}$, $p \ge q + 3$ and
$N \ge 1$, and let $\varepsilon_j$ be the tolerances `Constrained.TwoPhaseExample.BoxARqp.tol u`
for $u = 1/(4N^5)$. With the exponents $\pi_j = j(p+1)/p$,
$$\max\Bigl[\varepsilon_0^{-1}, \max_{j \in [1, q]} \varepsilon_0^{1-\pi_j}
  \varepsilon_j^{-\pi_j}\Bigr] \le 128 N^{14} \quad \text{and} \quad \max\Bigl[0, \max_{j \in
  [1, q]} \varepsilon_0^{1-\pi_j} \varepsilon_j^{-\pi_j}\Bigr] \le 128 N^{14}.$$

The maxima are `Optimization.finMax`, and the exponents are `Optimization.arqpPiOf False p j`.
The proof applies `Constrained.TwoPhaseExample.BoxARqp.term_le_pow` with $B = 2N^2$, using
$\varepsilon_0 \ge B^{-5}$, $\varepsilon_1 \ge B^{-3}$ and $\varepsilon_2 = 1$. -/
theorem order_le_pow {p q N : ℕ} (hq1 : 1 ≤ q) (hq2 : q ≤ 2) (hpq : q + 3 ≤ p) (hN : 1 ≤ N) :
    Optimization.finMax (tol (1 / (4 * N ^ 5)) 0)⁻¹ (fun j => tol (1 / (4 * N ^ 5)) 0 ^
        (1 - Optimization.arqpPiOf False p j) *
        tol (1 / (4 * N ^ 5)) j ^ (-Optimization.arqpPiOf False p j)) q ≤ 128 * (N : ℝ) ^ 14 ∧
      Optimization.finMax 0 (fun j => tol (1 / (4 * N ^ 5)) 0 ^
        (1 - Optimization.arqpPiOf False p j) *
        tol (1 / (4 * N ^ 5)) j ^ (-Optimization.arqpPiOf False p j)) q ≤
        128 * (N : ℝ) ^ 14 := by
  set u : ℝ := 1 / (4 * N ^ 5) with hu_def
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  set B : ℝ := 2 * (N : ℝ) ^ 2 with hB_def
  have hB1 : 1 ≤ B := by nlinarith
  have hB0 : 0 < B := by linarith
  have hB7 : B ^ (7 : ℝ) = 128 * (N : ℝ) ^ 14 := by
    rw [show (7 : ℝ) = ((7 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, hB_def]; ring
  have hu : 0 < u := by positivity
  have hε0 : (B ^ (5 : ℝ))⁻¹ ≤ tol u 0 := by
    rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, tol_zero]
    have : (B ^ 5)⁻¹ = u ^ 2 / 2 := by rw [hB_def, hu_def]; field_simp; ring
    rw [this]; have := pow_pos hu 3; linarith
  have hε1 : (B ^ (3 : ℝ))⁻¹ ≤ tol u 1 := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, tol_one, hB_def, hu_def]
    rw [inv_le_comm₀ (by positivity) (by positivity)]
    field_simp
    nlinarith [pow_pos hNp 5, pow_pos hNp 6]
  have hπ : ∀ l ∈ Finset.Icc 1 q, 1 ≤ Optimization.arqpPiOf False p l := fun l hl => by
    have := Finset.mem_Icc.1 hl
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
    have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast this.1
    simp only [Optimization.arqpPiOf, ite_false]
    rw [le_div_iff₀ hp0]; nlinarith
  have hterm : ∀ l ∈ Finset.Icc 1 q, tol u 0 ^ (1 - Optimization.arqpPiOf False p l) *
      tol u l ^ (-Optimization.arqpPiOf False p l) ≤ B ^ (7 : ℝ) := fun l hl => by
    have hl := Finset.mem_Icc.1 hl
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
    have hpq' : (q : ℝ) + 3 ≤ p := by exact_mod_cast hpq
    rcases (show l = 1 ∨ l = 2 by omega) with rfl | rfl
    · refine term_le_pow (tol_pos hu 0) (tol_pos hu 1) hB1 hε0 hε1
        (hπ 1 (Finset.mem_Icc.2 ⟨le_rfl, hq1⟩)) ?_
      simp only [Optimization.arqpPiOf, ite_false, Nat.cast_one, one_mul]
      have hp4 : (4 : ℝ) ≤ p := by have : (1 : ℝ) ≤ q := by exact_mod_cast hq1
                                   linarith
      have : ((p : ℝ) + 1) / p ≤ 5 / 4 := by rw [div_le_iff₀ hp0]; linarith
      linarith
    · have hq2' : (q : ℝ) = 2 := by exact_mod_cast (show q = 2 by omega)
      have h2 : tol u 2 = 1 := tol_two
      rw [h2, Real.one_rpow, mul_one]
      have hπ2 : Optimization.arqpPiOf False p 2 ≤ 12 / 5 := by
        simp only [Optimization.arqpPiOf, ite_false]
        rw [div_le_iff₀ hp0]; push_cast; linarith
      have hπ1 := hπ 2 (Finset.mem_Icc.2 ⟨by norm_num, by omega⟩)
      calc tol u 0 ^ (1 - Optimization.arqpPiOf False p 2)
          ≤ B ^ (5 * (Optimization.arqpPiOf False p 2 - 1)) := by
            rw [show 1 - Optimization.arqpPiOf False p 2 =
              -(Optimization.arqpPiOf False p 2 - 1) by ring]
            exact rpow_neg_le (tol_pos hu 0) hB0 hε0 (by linarith)
        _ ≤ B ^ (7 : ℝ) := Real.rpow_le_rpow_of_exponent_le hB1 (by linarith)
  have h0 : (tol u 0)⁻¹ ≤ B ^ (7 : ℝ) := by
    have := rpow_neg_le (c := 1) (tol_pos hu 0) hB0 hε0 zero_le_one
    rw [Real.rpow_neg_one, mul_one] at this
    exact this.trans (Real.rpow_le_rpow_of_exponent_le hB1 (by norm_num))
  rw [← hB7]
  exact ⟨Optimization.finMax_le h0 hterm,
    Optimization.finMax_le (Real.rpow_nonneg hB0.le _) hterm⟩

/-- **The parameters for a constant $C$.** For every $C \in \mathbb{R}$ there is $N \in \mathbb{N}$
with $N \ge 3$ and $C \cdot 128 N^{14} < N^{15}$ such that, if $C \ge 1$, the tolerances
`Constrained.TwoPhaseExample.BoxARqp.tol u` for $u = 1/(4N^5)$ satisfy
$\varepsilon_0 \le C^{-1}$ and $\varepsilon_1 \le C^{-1}$.

The proof takes $N = \lceil 128 |C| \rceil + 3$. With $M = N^{15}$, the condition
$u^3 M \le 1/64$ of the run holds with equality. -/
theorem exists_params (C : ℝ) : ∃ N : ℕ, 3 ≤ N ∧ C * (128 * (N : ℝ) ^ 14) < (N : ℝ) ^ 15 ∧
    (1 ≤ C → tol (1 / (4 * N ^ 5)) 0 ≤ C⁻¹ ∧ tol (1 / (4 * N ^ 5)) 1 ≤ C⁻¹) := by
  refine ⟨⌈128 * |C|⌉₊ + 3, by omega, ?_, fun hC => ?_⟩
  · set N : ℕ := ⌈128 * |C|⌉₊ + 3
    have hN : 128 * |C| + 2 < (N : ℝ) := by
      have := Nat.le_ceil (128 * |C|); push_cast [N]; linarith
    have hNp : (0 : ℝ) < N := by linarith [abs_nonneg C]
    have h14 : (0 : ℝ) < (N : ℝ) ^ 14 := by positivity
    calc C * (128 * (N : ℝ) ^ 14) ≤ |C| * (128 * (N : ℝ) ^ 14) :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
      _ = 128 * |C| * (N : ℝ) ^ 14 := by ring
      _ < N * (N : ℝ) ^ 14 := mul_lt_mul_of_pos_right (by linarith) h14
      _ = (N : ℝ) ^ 15 := by ring
  · set N : ℕ := ⌈128 * |C|⌉₊ + 3
    have hN : 128 * |C| + 2 < (N : ℝ) := by
      have := Nat.le_ceil (128 * |C|); push_cast [N]; linarith
    have hCN : C ≤ N := by linarith [le_abs_self C, abs_nonneg C]
    have hNp : (1 : ℝ) ≤ N := by linarith
    set u : ℝ := 1 / (4 * N ^ 5)
    have hu : 0 < u := by positivity
    have hN5 : (N : ℝ) ≤ (N : ℝ) ^ 5 := le_self_pow₀ hNp (by norm_num)
    have hu1 : u ≤ 1 := by
      apply div_le_one_of_le₀ (by nlinarith) (by positivity)
    have hNinv : 3 * u / 2 ≤ (N : ℝ)⁻¹ := by
      have : 3 * u / 2 = 3 / (8 * (N : ℝ) ^ 5) := by simp only [u]; field_simp; ring
      rw [this, div_le_iff₀ (by positivity)]
      field_simp
      nlinarith
    have hCi : (N : ℝ)⁻¹ ≤ C⁻¹ := inv_anti₀ (by linarith) hCN
    have hε1 : tol u 1 ≤ C⁻¹ := by rw [tol_one]; linarith
    refine ⟨?_, hε1⟩
    rw [tol_zero]
    nlinarith [pow_pos hu 2, pow_pos hu 3]

end BoxARqp

end Constrained.TwoPhaseExample
