/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Optimization.Constrained.TwoPhase.HighOrder.Complexity

/-!
# Phase-2 sequences with one-step inner calls

This file treats the simplest data of Phase 2 of a high-order target-following method (Algorithm
14.3.2 of [cartis2022evaluation]), for the problem of minimizing $f(x)$ subject to $x \in X$ and
$c(x) = 0$. The data consist of outer iterates $x_k$ and targets $t_k$, all optimality radii equal
to $1$, and inner calls that each make exactly one successful iteration, from $x_k$ to $x_{k+1}$. Up
to outer iteration $k$, such data use $k + 1$ evaluations of $(f, c)$ and $k + 1$ evaluations of the
derivatives.

Write $r(x, t) = (c(x), f(x) - t)$ for the target residual and $\mu(x, t) = \tfrac12 \|r(x, t)\|^2$
for the merit function. The data are a run of Phase 2 as soon as each step satisfies the conditions
of Steps 1–2 of the algorithm. The merit-decrease contracts of the inner method hold for these data
whenever every call ends at a point that is exempt from the decrease.

## Main definitions

* `Constrained.HighOrderTargetSeq.oneStep`: the Phase-2 data with iterates $x$, targets $t$, radii
  $1$ and one-step inner calls.

## Main results

* `Constrained.HighOrderTargetSeq.funEvals_oneStep` and
  `Constrained.HighOrderTargetSeq.derivEvals_oneStep`: $k + 1$ evaluations of the functions and of
  the derivatives up to outer iteration $k$.
* `Constrained.HighOrderTargetSeq.isEndCritContract_oneStep` and
  `Constrained.HighOrderTargetSeq.isInnerTestContract_oneStep`: the two merit-decrease contracts
  hold if every call ends at an exempt point.
* `Constrained.isHighOrderTargetRun_oneStep`: the conditions under which the one-step data are a run
  of Phase 2.
-/

open Finset
open scoped Nat

namespace Constrained

variable {E F : Type*}

namespace HighOrderTargetSeq

/-- The Phase-2 data with outer iterates $x_k$, targets $t_k$ and all optimality radii equal to $1$,
in which the $k$-th inner call makes one successful iteration, from $x_k$ to $x_{k+1}$. The
inner iterates are $x_{k,0} = x_k$ and $x_{k,i} = x_{k+1}$ for $i \ge 1$, and each call has
length $e_k = 1$. -/
def oneStep (x : ℕ → E) (t : ℕ → ℝ) : HighOrderTargetSeq E :=
  ⟨x, t, fun _ _ => 1, fun k i => if i = 0 then x k else x (k + 1), fun _ => 1, fun _ _ => True⟩

variable (x : ℕ → E) (t : ℕ → ℝ)

/-- The outer iterates of `Constrained.HighOrderTargetSeq.oneStep x t` are $x$. -/
@[simp] theorem oneStep_x : (oneStep x t).x = x := rfl

/-- The targets of `Constrained.HighOrderTargetSeq.oneStep x t` are $t$. -/
@[simp] theorem oneStep_t : (oneStep x t).t = t := rfl

/-- All optimality radii of `Constrained.HighOrderTargetSeq.oneStep x t` are $1$. -/
@[simp] theorem oneStep_δ (k j : ℕ) : (oneStep x t).δ k j = 1 := rfl

/-- Every inner call of `Constrained.HighOrderTargetSeq.oneStep x t` has length $1$. -/
@[simp] theorem oneStep_e (k : ℕ) : (oneStep x t).e k = 1 := rfl

/-- Every inner iteration of `Constrained.HighOrderTargetSeq.oneStep x t` is successful. -/
@[simp] theorem oneStep_succ (k i : ℕ) : (oneStep x t).succ k i := trivial

/-- The $k$-th inner call of `Constrained.HighOrderTargetSeq.oneStep x t` starts at $x_k$. -/
@[simp] theorem oneStep_xi_zero (k : ℕ) : (oneStep x t).xi k 0 = x k := rfl

/-- The first inner iterate after the start of the $k$-th call of
`Constrained.HighOrderTargetSeq.oneStep x t` is $x_{k+1}$. -/
@[simp] theorem oneStep_xi_one (k : ℕ) : (oneStep x t).xi k 1 = x (k + 1) := rfl

/-- For one-step inner calls, Phase 2 uses $k + 1$ evaluations of $(f, c)$ up to outer iteration
$k$: one at $x_1$ and one per call. -/
theorem funEvals_oneStep (k : ℕ) : (oneStep x t).funEvals k = k + 1 := by
  simp [funEvals_eq_sum, add_comm]

/-- For one-step inner calls, the $k$-th inner call has exactly one successful iteration. -/
@[simp] theorem succCount_oneStep (k : ℕ) : (oneStep x t).succCount k = 1 := by
  classical
  rw [succCount_eq_card_filter, Finset.card_eq_one]
  exact ⟨0, Finset.eq_singleton_iff_unique_mem.2 ⟨Finset.mem_filter.2 ⟨by simp, trivial⟩,
    fun i hi => by simpa using (Finset.mem_filter.1 hi).1⟩⟩

/-- For one-step inner calls, Phase 2 uses $k + 1$ evaluations of the derivatives of $(f, c)$ up to
outer iteration $k$: one at $x_1$ and one per call. -/
theorem derivEvals_oneStep (k : ℕ) : (oneStep x t).derivEvals k = k + 1 := by
  simp [derivEvals_eq_sum, add_comm]

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]

variable {f : E → ℝ} {c : E → F} {X : Set E} {q : ℕ} {θ β : ℝ} {ε : ℕ → ℝ} {x t}

/-- **The end-criticality contract for one-step calls.** Let $\kappa_{\mathrm{uns}} +
\kappa_{\mathrm{unc}} \ge 1$. Assume that for every outer iteration $k \ge 1$ that is reached,
the new iterate $x_{k+1}$ passes the criticality test (14.3.34) of [cartis2022evaluation] for
the old target $t_k$ with radii $1$. Then the merit contract
`Constrained.HighOrderTargetSeq.IsEndCritContract` holds for the one-step data, for every
$\kappa_{\mathrm{decr}}$ and every exponent sequence $\pi$.

The only successful iteration of each call is its last one, and it ends at a point that passes
the test, so it is exempt from the decrease condition of the contract. -/
theorem isEndCritContract_oneStep {κdecr κuns κunc : ℝ} {π : ℕ → ℝ} (hκ : 1 ≤ κuns + κunc)
    (hcrit : ∀ k, 1 ≤ k → (oneStep x t).Before f c X q θ ε k →
      targetCrit f c X q ε (t k) (x (k + 1)) (fun _ => 1)) :
    (oneStep x t).IsEndCritContract f c X q θ β ε κdecr κuns κunc π :=
  ⟨fun _ _ _ => by simp; linarith, fun _ _ _ _ _ hs => absurd trivial hs,
    fun k hk1 hk i hi _ hcont _ => by
      obtain rfl : i = 0 := by simpa using hi
      rcases hcont with h | h
      · simp at h
      · exact absurd (hcrit k hk1 hk) h⟩

/-- **The inner-test contract for one-step calls.** Let $\kappa_{\mathrm{uns}} +
\kappa_{\mathrm{unc}} \ge 1$, and let $\rho_j \le 1$ for $j \in [1 : q]$. Assume that for every
outer iteration $k \ge 1$ that is reached, the call ends at a point that passes the inner
method's own termination test (14.3.19) of [cartis2022evaluation],
`Constrained.HighOrderTargetSeq.InnerTest`. Then the merit contract
`Constrained.HighOrderTargetSeq.IsInnerTestContract` with radii $\rho$ holds for the one-step
data, for every $\kappa_{\mathrm{decr}}$ and every exponent sequence $\pi$.

The only successful iteration of each call is exempt from the decrease condition, and the radii
$1$ are at least $\rho_j$. -/
theorem isInnerTestContract_oneStep {κdecr κuns κunc : ℝ} {π ρ : ℕ → ℝ}
    (hκ : 1 ≤ κuns + κunc) (hρ : ∀ j ∈ Finset.Icc 1 q, ρ j ≤ 1)
    (htest : ∀ k, 1 ≤ k → (oneStep x t).Before f c X q θ ε k →
      (oneStep x t).InnerTest f c X q β ε k) :
    (oneStep x t).IsInnerTestContract f c X q θ β ε κdecr κuns κunc π ρ :=
  ⟨⟨fun _ _ _ => by simp; linarith, fun _ _ _ _ _ hs => absurd trivial hs,
    fun k hk1 hk i hi _ hcont _ => by
      obtain rfl : i = 0 := by simpa using hi
      rcases hcont with h | h
      · simp at h
      · exact absurd (htest k hk1 hk) h⟩,
    fun _ _ _ _ _ j hj => hρ j hj⟩

end HighOrderTargetSeq

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] {f : E → ℝ} {c : E → F}
  {X : Set E} {q : ℕ} {θ β : ℝ} {ε : ℕ → ℝ}

/-- **Runs with one-step inner calls.** The data `Constrained.HighOrderTargetSeq.oneStep x t` are a
run of Phase 2 of Algorithm 14.3.2 of [cartis2022evaluation] from $x_1$ under the following
conditions. The first two conditions are on the constants and on Step 0. Each of the other
conditions is required at every outer iteration $k \ge 1$ that is reached.

* The constants are admissible: $0 < \theta < 1$, $0 < \beta \le \theta$, and
  $0 < \varepsilon_j \le 1$ for $j \in [0 : q]$.
* Step 0 holds: $x_1 \in X$, $\|c(x_1)\| \le \theta \varepsilon_0$, and $t_1 = f(x_1) -
  \sqrt{\varepsilon_0^2 - \|c(x_1)\|^2}$.
* The new iterate is feasible: $x_{k+1} \in X$.
* $x_{k+1}$ satisfies (14.3.32) with radii $1$: $\|r(x_{k+1}, t_k)\| < \theta \varepsilon_0$, or
  $f(x_{k+1}) < t_k$, or $x_{k+1}$ passes the criticality test (14.3.34) for $t_k$.
* The step does not increase the merit function: $\mu(x_{k+1}, t_k) \le \mu(x_k, t_k)$.
* The residual at the start of the call is not small:
  $\|r(x_k, t_k)\| \ge \theta \varepsilon_0$.
* The target updates hold: $t_{k+1} = f(x_{k+1}) - \sqrt{\varepsilon_0^2 - \|c(x_{k+1})\|^2}$ in
  case (a), which is (14.3.33), and $t_{k+1} = 2 f(x_{k+1}) - t_k$ in case (b), which is
  (14.3.35). -/
theorem isHighOrderTargetRun_oneStep {x : ℕ → E} {t : ℕ → ℝ} (hθ : 0 < θ) (hθ1 : θ < 1)
    (hβ : 0 < β) (hβθ : β ≤ θ) (hε : ∀ j ∈ Finset.range (q + 1), 0 < ε j)
    (hε1 : ∀ j ∈ Finset.range (q + 1), ε j ≤ 1) (hx1 : x 1 ∈ X) (hc1 : ‖c (x 1)‖ ≤ θ * ε 0)
    (ht1 : t 1 = f (x 1) - √(ε 0 ^ 2 - ‖c (x 1)‖ ^ 2))
    (hmem : ∀ k, 1 ≤ k → (HighOrderTargetSeq.oneStep x t).Before f c X q θ ε k →
      x (k + 1) ∈ X)
    (hout : ∀ k, 1 ≤ k → (HighOrderTargetSeq.oneStep x t).Before f c X q θ ε k →
      targetResidual f c (t k) (x (k + 1)) < θ * ε 0 ∨ f (x (k + 1)) < t k ∨
        targetCrit f c X q ε (t k) (x (k + 1)) (fun _ => 1))
    (hmono : ∀ k, 1 ≤ k → (HighOrderTargetSeq.oneStep x t).Before f c X q θ ε k →
      targetMerit f c (t k) (x (k + 1)) ≤ targetMerit f c (t k) (x k))
    (hres : ∀ k, 1 ≤ k → (HighOrderTargetSeq.oneStep x t).Before f c X q θ ε k →
      θ * ε 0 ≤ targetResidual f c (t k) (x k))
    (ha : ∀ k, 1 ≤ k → (HighOrderTargetSeq.oneStep x t).Before f c X q θ ε k →
      (HighOrderTargetSeq.oneStep x t).IsKa f c θ ε k →
      t (k + 1) = f (x (k + 1)) - √(ε 0 ^ 2 - ‖c (x (k + 1))‖ ^ 2))
    (hb : ∀ k, 1 ≤ k → (HighOrderTargetSeq.oneStep x t).Before f c X q θ ε k →
      (HighOrderTargetSeq.oneStep x t).IsKb f c θ ε k → t (k + 1) = 2 * f (x (k + 1)) - t k) :
    IsHighOrderTargetRun f c X q θ β ε (x 1) (HighOrderTargetSeq.oneStep x t) :=
  ⟨hθ, hθ1, hβ, hβθ, hε, hε1, hx1, hc1, rfl, ht1, hmem, fun _ _ _ _ _ => ⟨one_pos, le_rfl⟩, hout,
    fun _ _ _ => rfl, fun _ _ _ => rfl,
    fun k hk1 hk i hi => by obtain rfl : i = 0 := by simpa using hi
                            exact hmono k hk1 hk,
    fun k hk1 hk i hi => by obtain rfl : i = 0 := by simpa using hi
                            exact hres k hk1 hk, ha, hb⟩

end Constrained
