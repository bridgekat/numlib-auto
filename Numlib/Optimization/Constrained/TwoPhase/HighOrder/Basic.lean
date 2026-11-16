/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Optimization.Constrained.TwoPhase.Complexity

/-!
# High-order target-following runs

This file sets up Phase 2 of the two-phase method TPqp-GC (Algorithm 14.3.2 of
[cartis2022evaluation]) for the problem of minimizing $f(x)$ subject to $x \in X$ and $c(x) = 0$,
with $f : E \to \mathbb{R}$ and $c : E \to F$ on a normed space $E$. As in the generic outer loop of
`Numlib.Optimization.Constrained.TwoPhase.Run`, Phase 2 follows decreasing targets $t_k$ and calls
an inner method on the merit function $\mu(\cdot, t) = \frac12 \|r(\cdot, t)\|^2$
(`Constrained.targetMerit`), where $r(x, t) = (c(x), f(x) - t)$. The criticality test is the test
(14.3.34) of order $q$: at the output $y$ of an inner call, for a target $t$ and optimality radii
$\delta$,
$$\phi^{\delta_j}_{\mu, X(y), j}(y, t) \le \varepsilon_j \|r(y, t)\| \frac{\delta_j^j}{j!} \quad
  \text{for } j = 1, \dots, q,$$
where $\phi$ is the Taylor measure on the feasible displacements $X(y) = \{d \mid y + d \in X\}$
(`Optimization.taylorMeasure`). The tolerances are a sequence
$\varepsilon : \mathbb{N} \to \mathbb{R}$, and $\varepsilon_0$ is the primal tolerance.

The file defines the data and the run predicate, maps them to the generic outer loop, and constructs
runs from an inner oracle. Write $\mathcal{K}_a$ and $\mathcal{K}_b$ for the outer iterations in
case (a) and in case (b).

## Main definitions

* `Constrained.targetCrit`: the criticality test (14.3.34).
* `Constrained.HighOrderTargetSeq`: the outer iterates, targets, optimality radii, inner iterates,
  call lengths and successful inner iterations.
* `Constrained.HighOrderTargetSeq.toTargetFollowingSeq`: the data of the generic outer loop, with
  the tests `Constrained.HighOrderTargetSeq.IsKa`, `Constrained.HighOrderTargetSeq.IsKb` and
  `Constrained.targetCrit`.
* `Constrained.HighOrderTargetSeq.InnerTest`: the termination test (14.3.19) of the inner method
  called with the tolerances $\beta \|r(x_k, t_k)\| \varepsilon_j$.
* `Constrained.HighOrderTargetSeq.succCount`, `Constrained.HighOrderTargetSeq.kaCount`,
  `Constrained.HighOrderTargetSeq.kbCount`, `Constrained.HighOrderTargetSeq.funEvals`,
  `Constrained.HighOrderTargetSeq.derivEvals`, `Constrained.HighOrderTargetSeq.targetOut`,
  `Constrained.HighOrderTargetSeq.goodCount`, `Constrained.HighOrderTargetSeq.badCount`: the counts
  and the output target of Phase 2.
* `Constrained.IsHighOrderTargetRun`: the data form a run of Phase 2 from $x_1$.
* `Constrained.InnerCall`: the data of one inner call.

## Main results

* `Constrained.IsHighOrderTargetRun.toRun`: a run is a run of the generic outer loop.
* `Constrained.IsHighOrderTargetRun.output_spec`: the output satisfies (14.3.48), (14.3.49) and
  (14.3.52).
* `Constrained.IsHighOrderTargetRun.kaCount_le`: Lemma 7.2.4, $|\mathcal{K}_a| \le
  (f_{\mathrm{up}} - f_{\mathrm{low}} + 1)/((1 - \theta)\varepsilon_0)$.
* `Constrained.HighOrderTargetSeq.exists_run_of_oracle`: an inner oracle that produces admissible
  calls from every admissible point yields a run whose calls are produced by the oracle.

## Implementation notes

* The data `Constrained.HighOrderTargetSeq` add only the optimality radii and the successful inner
  iterations to the data of the generic outer loop. Through
  `Constrained.HighOrderTargetSeq.toTargetFollowingSeq` and
  `Constrained.IsHighOrderTargetRun.toRun`, every counting and termination statement of
  `Numlib.Optimization.Constrained.TwoPhase.Run` and
  `Numlib.Optimization.Constrained.TwoPhase.Complexity` applies to a high-order run. The termination
  predicates `Stop`, `Before` and `IsEnd` are reducible abbreviations of the generic ones.
* The counts that use only some of the tests are taken on
  `Constrained.HighOrderTargetSeq.toCountSeq`, the same data with only those tests.
* `Constrained.targetCrit` is stated in unfolded form (`Constrained.targetCrit_iff`). It is the
  $(\varepsilon, \delta)$-approximate criticality `Optimization.IsEpsDeltaApprox` of $\mu(\cdot, t)$
  with the tolerances scaled by $\|r(y, t)\|$ (`Constrained.targetCrit_iff_isEpsDeltaApprox`).
* The construction `Constrained.HighOrderTargetSeq.exists_run_of_oracle` is generic in an extra
  property `Good` of the calls. So each realization of the inner method (regularization, trust
  region, and others) yields runs whose calls carry the certificates of that method.
* Step 2(a) uses the strict test $\|r(x_{k+1}, t_k)\| < \theta\varepsilon_0$
  (`Constrained.HighOrderTargetSeq.IsKa`). The inner calls are described by their iterates:
  $\mu(\cdot, t_k)$ does not increase along a call, and a call stops as soon as
  $\|r(\cdot, t_k)\| < \theta\varepsilon_0$. With this rule every successful iteration except the
  last one of a call counts in the telescoping argument.
-/

open Finset
open scoped Nat

namespace Constrained

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]

/-! ### The criticality test -/

section Crit

/-- **The criticality test (14.3.34)** of [cartis2022evaluation] at the point $y$, for the target
$t$ and the optimality radii $\delta$: for every $j = 1, \dots, q$,
$$\phi^{\delta_j}_{\mu, X(y), j}(y, t) \le \varepsilon_j \|r(y, t)\| \frac{\delta_j^j}{j!},$$
where $\phi^{\delta_j}_{\mu, X(y), j}(y, t)$ is the Taylor measure of order $j$ and radius
$\delta_j$ of $\mu(\cdot, t) = \frac12 \|r(\cdot, t)\|^2$ at $y$ over the feasible displacements
$X(y) = \{d \mid y + d \in X\}$.

This is also the third stopping test of (14.3.32). The measure is `Optimization.taylorMeasure`
of the Taylor series of `Constrained.targetMerit f c t` at $y$. By
`Constrained.targetCrit_iff_isEpsDeltaApprox`, the test is the
$(\varepsilon', \delta)$-approximate criticality of order $q$ of $\mu(\cdot, t)$ for the
tolerances $\varepsilon'_j = \varepsilon_j \|r(y, t)\|$. -/
def targetCrit (f : E → ℝ) (c : E → F) (X : Set E) (q : ℕ) (ε : ℕ → ℝ) (t : ℝ) (y : E)
    (δ : ℕ → ℝ) : Prop :=
  ∀ j ∈ Finset.Icc 1 q,
    Optimization.taylorMeasure (ftaylorSeries ℝ (targetMerit f c t) y) j (δ j) {d | y + d ∈ X} ≤
      ε j * targetResidual f c t y * δ j ^ j / j !

variable {f : E → ℝ} {c : E → F} {X : Set E} {q : ℕ} {ε ε' : ℕ → ℝ} {t : ℝ} {y : E}
  {δ : ℕ → ℝ}

/-- The criticality test holds if and only if $\phi^{\delta_j}_{\mu, X(y), j}(y, t) \le
\varepsilon_j \|r(y, t)\| \delta_j^j/j!$ for every $j = 1, \dots, q$. -/
theorem targetCrit_iff :
    targetCrit f c X q ε t y δ ↔ ∀ j ∈ Finset.Icc 1 q,
      Optimization.taylorMeasure (ftaylorSeries ℝ (targetMerit f c t) y) j (δ j)
        {d | y + d ∈ X} ≤ ε j * targetResidual f c t y * δ j ^ j / j ! :=
  Iff.rfl

/-- The criticality test at $(y, t)$ with radii $\delta$ is the $(\varepsilon', \delta)$-approximate
criticality of order $q$ (`Optimization.IsEpsDeltaApprox`) of $\mu(\cdot, t)$ at $y$ over the
feasible displacements $\{d \mid y + d \in X\}$, for the tolerances
$\varepsilon'_j = \varepsilon_j \|r(y, t)\|$. -/
theorem targetCrit_iff_isEpsDeltaApprox :
    targetCrit f c X q ε t y δ ↔ Optimization.IsEpsDeltaApprox
      (ftaylorSeries ℝ (targetMerit f c t) y) {d | y + d ∈ X} q
      (fun j => ε j * targetResidual f c t y) δ :=
  Iff.rfl

/-- The criticality test is monotone in the tolerances. If the test holds with tolerances
$\varepsilon'$, and $\varepsilon'_j \le \varepsilon_j$ and $\delta_j \ge 0$ for every
$j = 1, \dots, q$, then the test holds with tolerances $\varepsilon$. -/
theorem targetCrit.mono (h : targetCrit f c X q ε' t y δ) (hε : ∀ j ∈ Finset.Icc 1 q, ε' j ≤ ε j)
    (hδ : ∀ j ∈ Finset.Icc 1 q, 0 ≤ δ j) : targetCrit f c X q ε t y δ := fun j hj =>
  (h j hj).trans (by
    have := hδ j hj
    have := targetResidual_nonneg (f := f) (c := c) (t := t) (x := y)
    gcongr
    exact hε j hj)

end Crit

/-! ### The data of Phase 2 -/

/-- The **data of Phase 2** of a high-order target-following method (Algorithm 14.3.2 of
[cartis2022evaluation]), indexed by the outer iteration $k \ge 1$. The data consist of the outer
iterates $x_k$, the targets $t_k$, the optimality radii $\delta_{k,j}$, and, for the $k$-th call
of the inner method on $\mu(\cdot, t_k)$, its iterates $x_{k,i}$, its number $e_k$ of iterations
and its successful iterations.

The values at $k = 0$ are not used. -/
structure HighOrderTargetSeq (E : Type*) where
  /-- The outer iterates $x_k$. -/
  x : ℕ → E
  /-- The targets $t_k$. -/
  t : ℕ → ℝ
  /-- The optimality radii $\delta_{k,j}$ for the orders $j = 1, \dots, q$. -/
  δ : ℕ → ℕ → ℝ
  /-- The iterates $x_{k,i}$ of the $k$-th inner call. -/
  xi : ℕ → ℕ → E
  /-- The number $e_k$ of iterations of the $k$-th inner call. -/
  e : ℕ → ℕ
  /-- The successful iterations: `succ k i` says that iteration $i$ of the $k$-th inner call is
  successful. -/
  succ : ℕ → ℕ → Prop

namespace HighOrderTargetSeq

variable (f : E → ℝ) (c : E → F) (X : Set E) (q : ℕ) (θ β : ℝ) (ε : ℕ → ℝ)
  (D : HighOrderTargetSeq E)

/-- Outer iteration $k$ is in $\mathcal{K}_a$ ((14.3.36) of [cartis2022evaluation]), that is, Step
2(a) occurs: $\|r(x_{k+1}, t_k)\| < \theta\varepsilon_0$. -/
def IsKa (k : ℕ) : Prop := targetResidual f c (D.t k) (D.x (k + 1)) < θ * ε 0

/-- Outer iteration $k$ is in $\mathcal{K}_b$, that is, Step 2(b) occurs:
$\|r(x_{k+1}, t_k)\| \ge \theta\varepsilon_0$ and $f(x_{k+1}) < t_k$. -/
def IsKb (k : ℕ) : Prop :=
  θ * ε 0 ≤ targetResidual f c (D.t k) (D.x (k + 1)) ∧ f (D.x (k + 1)) < D.t k

/-- The data of Phase 2 as data of the generic target-following outer loop
(`Constrained.TargetFollowingSeq`). The tests are $\mathcal{K}_a$, $\mathcal{K}_b$, and, for a
target $\tau$, the criticality test (14.3.34) at $(x_{k+1}, \tau)$ with the radii
$\delta_{k+1}$. -/
def toTargetFollowingSeq : TargetFollowingSeq E where
  x := D.x
  t := D.t
  xi := D.xi
  e := D.e
  Ka := D.IsKa f c θ ε
  Kb := D.IsKb f c θ ε
  crit k τ := targetCrit f c X q ε τ (D.x (k + 1)) (D.δ (k + 1))

/-- The criticality test (14.3.34) at the output $x_{k+1}$ of the $k$-th inner call for the old
target $t_k$, with the radii $\delta_{k+1}$. This is the third stopping test of (14.3.32). -/
abbrev EndCrit (k : ℕ) : Prop := targetCrit f c X q ε (D.t k) (D.x (k + 1)) (D.δ (k + 1))

/-- Phase 2 terminates at outer iteration $k$: in case (c), or in case (a) or (b) when the
criticality test (14.3.34) holds at $(x_{k+1}, t_{k+1})$ with the radii $\delta_{k+1}$. -/
abbrev Stop (k : ℕ) : Prop := (D.toTargetFollowingSeq f c X q θ ε).Stop k

/-- Outer iteration $k$ is reached: no outer iteration $j \in [1, k)$ terminates Phase 2. -/
abbrev Before (k : ℕ) : Prop := (D.toTargetFollowingSeq f c X q θ ε).Before k

/-- Phase 2 terminates at outer iteration $k_\varepsilon \ge 1$: the iteration $k_\varepsilon$ is
reached and terminates Phase 2. -/
abbrev IsEnd (kε : ℕ) : Prop := (D.toTargetFollowingSeq f c X q θ ε).IsEnd kε

/-- The data of Phase 2 as data of the generic outer loop, with given tests `Ka`, `Kb` and a
criticality test that never holds. The counts that involve only some of the tests are taken on
these data; no count of the outer loop involves the criticality test. -/
def toCountSeq (Ka Kb : ℕ → Prop) : TargetFollowingSeq E where
  x := D.x
  t := D.t
  xi := D.xi
  e := D.e
  Ka := Ka
  Kb := Kb
  crit _ _ := False

/-- The **output target** $t_\varepsilon$ of Phase 2 when it terminates at outer iteration $k$:
$t_{k+1}$ in case (a) or (b), and $t_k$ in case (c). The output point is
$x_\varepsilon = x_{k+1}$. -/
noncomputable abbrev targetOut (k : ℕ) : ℝ :=
  (D.toCountSeq (D.IsKa f c θ ε) (D.IsKb f c θ ε)).targetOut k

/-- The output target is the output target of the generic outer loop on
`Constrained.HighOrderTargetSeq.toTargetFollowingSeq`. -/
theorem targetOut_eq (k : ℕ) :
    D.targetOut f c θ ε k = (D.toTargetFollowingSeq f c X q θ ε).targetOut k := rfl

/-- **The termination test (14.3.19) of the inner method** at the end of the $k$-th call: for every
$j = 1, \dots, q$,
$$\phi^{\delta_{k+1,j}}_{\mu, X(x_{k+1}), j}(x_{k+1}, t_k) \le \beta \|r(x_k, t_k)\|
  \varepsilon_j \frac{\delta_{k+1,j}^j}{j!}.$$

The $k$-th call is $\mathrm{INNER}(\mu(\cdot, t_k), X, q, x_k, \beta \|r(x_k, t_k)\|
\varepsilon)$ of Step 1 of Algorithm 14.3.2 of [cartis2022evaluation]. When $\beta \le \theta$
and $\|r(x_{k+1}, t_k)\| \ge \theta\varepsilon_0$, the tolerance of this test is at most the
tolerance of (14.3.34) at $(x_{k+1}, t_k)$. -/
def InnerTest (k : ℕ) : Prop :=
  ∀ j ∈ Finset.Icc 1 q,
    Optimization.taylorMeasure (ftaylorSeries ℝ (targetMerit f c (D.t k)) (D.x (k + 1))) j
        (D.δ (k + 1) j) {d | D.x (k + 1) + d ∈ X} ≤
      β * targetResidual f c (D.t k) (D.x k) * ε j * D.δ (k + 1) j ^ j / j !

/-! ### Counts -/

/-- The number of successful iterations of the $k$-th inner call. -/
noncomputable abbrev succCount (k : ℕ) : ℕ :=
  (D.toCountSeq (fun _ => False) fun _ => False).succCount D.succ k

/-- The number $|\mathcal{K}_a \cap [1, K)|$ of outer iterations in $\mathcal{K}_a$ among
$1, \dots, K - 1$. -/
noncomputable abbrev kaCount (K : ℕ) : ℕ :=
  (D.toCountSeq (D.IsKa f c θ ε) fun _ => False).kaCount K

/-- The number $|\mathcal{K}_b \cap [1, K)|$ of outer iterations in $\mathcal{K}_b$ among
$1, \dots, K - 1$. -/
noncomputable abbrev kbCount (K : ℕ) : ℕ :=
  (D.toCountSeq (fun _ => False) (D.IsKb f c θ ε)).kbCount K

/-- The number of evaluations of $(f, c)$ in Phase 2 up to outer iteration $k$:
$1 + \sum_{j=1}^{k} e_j$, one evaluation at $x_1$ and one per inner iteration. -/
noncomputable abbrev funEvals (k : ℕ) : ℕ :=
  (D.toCountSeq (fun _ => False) fun _ => False).funEvals k

/-- The number of evaluations of the derivatives of $(f, c)$ in Phase 2 up to outer iteration $k$:
one evaluation at $x_1$ and one per successful inner iteration. -/
noncomputable abbrev derivEvals (k : ℕ) : ℕ :=
  (D.toCountSeq (fun _ => False) fun _ => False).derivEvals D.succ k

/-- A **good** inner iteration $(k, i)$ for the exemption by the criticality test (14.3.34) at the
old target: it is successful, it is not the last iteration of a call whose output passes
`Constrained.HighOrderTargetSeq.EndCrit`, and its new iterate has residual
$\|r(x_{k,i+1}, t_k)\| \ge \theta\varepsilon_0$. These are the iterations that the proof of
Lemma 14.3.8 of [cartis2022evaluation] counts. -/
abbrev IsGood (k i : ℕ) : Prop :=
  (D.toTargetFollowingSeq f c X q θ ε).IsGood f c θ (ε 0) D.succ (D.EndCrit f c X q ε) k i

/-- The number of good iterations of the $k$-th inner call. -/
noncomputable abbrev goodCount (k : ℕ) : ℕ :=
  (D.toTargetFollowingSeq f c X q θ ε).goodCount f c θ (ε 0) D.succ (D.EndCrit f c X q ε) k

/-- A **bad** outer iteration: $k \in \mathcal{K}_b$ and its inner call contains no good iteration.
-/
abbrev IsBad (k : ℕ) : Prop :=
  (D.toTargetFollowingSeq f c X q θ ε).IsBad f c θ (ε 0) D.succ (D.EndCrit f c X q ε) k

/-- The number of bad outer iterations among $1, \dots, K - 1$. -/
noncomputable abbrev badCount (K : ℕ) : ℕ :=
  (D.toTargetFollowingSeq f c X q θ ε).badCount f c θ (ε 0) D.succ (D.EndCrit f c X q ε) K

variable {f c X q θ ε D}

/-- The number of successful iterations of the $k$-th call is the one of the generic outer loop on
`Constrained.HighOrderTargetSeq.toTargetFollowingSeq`. -/
theorem succCount_eq (k : ℕ) :
    D.succCount k = (D.toTargetFollowingSeq f c X q θ ε).succCount D.succ k := rfl

/-- The number of case-(a) iterations is the one of the generic outer loop on
`Constrained.HighOrderTargetSeq.toTargetFollowingSeq`. -/
theorem kaCount_eq (K : ℕ) :
    D.kaCount f c θ ε K = (D.toTargetFollowingSeq f c X q θ ε).kaCount K := rfl

/-- The number of case-(b) iterations is the one of the generic outer loop on
`Constrained.HighOrderTargetSeq.toTargetFollowingSeq`. -/
theorem kbCount_eq (K : ℕ) :
    D.kbCount f c θ ε K = (D.toTargetFollowingSeq f c X q θ ε).kbCount K := rfl

/-- The number of evaluations of $(f, c)$ is the one of the generic outer loop on
`Constrained.HighOrderTargetSeq.toTargetFollowingSeq`. -/
theorem funEvals_eq (k : ℕ) :
    D.funEvals k = (D.toTargetFollowingSeq f c X q θ ε).funEvals k := rfl

/-- The number of derivative evaluations is the one of the generic outer loop on
`Constrained.HighOrderTargetSeq.toTargetFollowingSeq`. -/
theorem derivEvals_eq (k : ℕ) :
    D.derivEvals k = (D.toTargetFollowingSeq f c X q θ ε).derivEvals D.succ k := rfl

section Tests

omit [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Outer iteration $k$ is in $\mathcal{K}_a$ if and only if
$\|r(x_{k+1}, t_k)\| < \theta\varepsilon_0$. -/
theorem isKa_iff {k : ℕ} :
    D.IsKa f c θ ε k ↔ targetResidual f c (D.t k) (D.x (k + 1)) < θ * ε 0 := Iff.rfl

/-- Outer iteration $k$ is in $\mathcal{K}_b$ if and only if
$\|r(x_{k+1}, t_k)\| \ge \theta\varepsilon_0$ and $f(x_{k+1}) < t_k$. -/
theorem isKb_iff {k : ℕ} :
    D.IsKb f c θ ε k ↔
      θ * ε 0 ≤ targetResidual f c (D.t k) (D.x (k + 1)) ∧ f (D.x (k + 1)) < D.t k := Iff.rfl

/-- The number of successful iterations of the $k$-th call is the cardinality of the set of
successful $i \in [0, e_k)$, for every decidability instance of the predicate. -/
theorem succCount_eq_card_filter (k : ℕ) [DecidablePred (D.succ k)] :
    D.succCount k = ((Finset.range (D.e k)).filter (D.succ k)).card :=
  TargetFollowingSeq.succCount_eq_card_filter k

/-- In case (a) or (b), the output target of an outer iteration $k$ is $t_{k+1}$. -/
theorem targetOut_of_ka_or_kb {k : ℕ} (h : D.IsKa f c θ ε k ∨ D.IsKb f c θ ε k) :
    D.targetOut f c θ ε k = D.t (k + 1) :=
  TargetFollowingSeq.targetOut_of_ka_or_kb h

/-- In case (c), that is, neither in case (a) nor in case (b), the output target of an outer
iteration $k$ is $t_k$. -/
theorem targetOut_of_not {k : ℕ} (ha : ¬ D.IsKa f c θ ε k) (hb : ¬ D.IsKb f c θ ε k) :
    D.targetOut f c θ ε k = D.t k :=
  TargetFollowingSeq.targetOut_of_not ha hb

/-- The number of case-(a) iterations among $1, \dots, K - 1$ is the cardinality of
$\mathcal{K}_a \cap [1, K)$, for every decidability instance of the predicate. -/
theorem kaCount_eq_card_filter (K : ℕ) [DecidablePred (D.IsKa f c θ ε)] :
    D.kaCount f c θ ε K = ((Finset.Ico 1 K).filter (D.IsKa f c θ ε)).card :=
  letI : DecidablePred (D.toCountSeq (D.IsKa f c θ ε) fun _ => False).Ka := ‹_›
  TargetFollowingSeq.kaCount_eq_card_filter K

/-- The number of case-(b) iterations among $1, \dots, K - 1$ is the cardinality of
$\mathcal{K}_b \cap [1, K)$, for every decidability instance of the predicate. -/
theorem kbCount_eq_card_filter (K : ℕ) [DecidablePred (D.IsKb f c θ ε)] :
    D.kbCount f c θ ε K = ((Finset.Ico 1 K).filter (D.IsKb f c θ ε)).card :=
  letI : DecidablePred (D.toCountSeq (fun _ => False) (D.IsKb f c θ ε)).Kb := ‹_›
  TargetFollowingSeq.kbCount_eq_card_filter K

/-- The number of evaluations of $(f, c)$ up to outer iteration $k$ is $1 + \sum_{j=1}^{k} e_j$. -/
theorem funEvals_eq_sum (k : ℕ) : D.funEvals k = 1 + ∑ j ∈ Finset.Icc 1 k, D.e j := rfl

/-- The number of derivative evaluations up to outer iteration $k$ is
$1 + \sum_{j=1}^{k} |\mathcal{S}_j|$, where $|\mathcal{S}_j|$ is the number of successful
iterations of the $j$-th call. -/
theorem derivEvals_eq_sum (k : ℕ) :
    D.derivEvals k = 1 + ∑ j ∈ Finset.Icc 1 k, D.succCount j := rfl

end Tests

/-- The termination test (14.3.19) of the inner method holds at the end of the $k$-th call if and
only if $\phi^{\delta_{k+1,j}}_{\mu, X(x_{k+1}), j}(x_{k+1}, t_k) \le \beta \|r(x_k, t_k)\|
\varepsilon_j \delta_{k+1,j}^j/j!$ for every $j = 1, \dots, q$. -/
theorem innerTest_iff {β : ℝ} {k : ℕ} :
    D.InnerTest f c X q β ε k ↔ ∀ j ∈ Finset.Icc 1 q,
      Optimization.taylorMeasure (ftaylorSeries ℝ (targetMerit f c (D.t k)) (D.x (k + 1))) j
          (D.δ (k + 1) j) {d | D.x (k + 1) + d ∈ X} ≤
        β * targetResidual f c (D.t k) (D.x k) * ε j * D.δ (k + 1) j ^ j / j ! := Iff.rfl

end HighOrderTargetSeq

/-! ### The run predicate -/

/-- **A run of Phase 2 of a high-order target-following method** (Phase 2 of Algorithm 14.3.2 of
[cartis2022evaluation], TPqp-GC), started at $x_1 \in X$ with
$\|c(x_1)\| \le \theta\varepsilon_0$. The constants satisfy $\theta \in (0, 1)$,
$\beta \in (0, \theta]$ and $\varepsilon_j \in (0, 1]$ for $j = 0, \dots, q$. The data $D$ form
a run if:

* Step 0: $x_1$ is the first outer iterate and $t_1 = f(x_1) - \sqrt{\varepsilon_0^2 -
  \|c(x_1)\|^2}$;
* Step 1, for every outer iteration $k \ge 1$ that is reached: $x_{k+1} \in X$, the radii
  satisfy $\delta_{k+1,j} \in (0, 1]$ for $j = 1, \dots, q$, and the output condition (14.3.32)
  holds, that is, $\|r(x_{k+1}, t_k)\| < \theta\varepsilon_0$, or $f(x_{k+1}) < t_k$, or the
  criticality test (14.3.34) holds at $(x_{k+1}, t_k)$ with the radii $\delta_{k+1}$;
* Step 1, the inner call: its iterates satisfy $x_{k,0} = x_k$ and $x_{k,e_k} = x_{k+1}$, they
  do not increase $\mu(\cdot, t_k)$, and $\|r(x_{k,i}, t_k)\| \ge \theta\varepsilon_0$ for every
  $i < e_k$;
* Step 2: the target update is (14.3.33) in case (a) and (14.3.35) in case (b).

Termination is `Constrained.HighOrderTargetSeq.Stop`. -/
structure IsHighOrderTargetRun (f : E → ℝ) (c : E → F) (X : Set E) (q : ℕ) (θ β : ℝ)
    (ε : ℕ → ℝ) (x₁ : E) (D : HighOrderTargetSeq E) : Prop where
  /-- $\theta > 0$. -/
  θ_pos : 0 < θ
  /-- $\theta < 1$. -/
  θ_lt_one : θ < 1
  /-- $\beta > 0$. -/
  β_pos : 0 < β
  /-- $\beta \le \theta$. -/
  β_le_θ : β ≤ θ
  /-- $\varepsilon_j > 0$ for $j = 0, \dots, q$. -/
  ε_pos : ∀ j ∈ Finset.range (q + 1), 0 < ε j
  /-- $\varepsilon_j \le 1$ for $j = 0, \dots, q$. -/
  ε_le_one : ∀ j ∈ Finset.range (q + 1), ε j ≤ 1
  /-- The starting point satisfies $x_1 \in X$. -/
  mem_one : x₁ ∈ X
  /-- Phase 1 ended with $\|c(x_1)\| \le \theta\varepsilon_0$. -/
  norm_one_le : ‖c x₁‖ ≤ θ * ε 0
  /-- Phase 2 starts at $x_1$. -/
  x_one : D.x 1 = x₁
  /-- Step 0: $t_1 = f(x_1) - \sqrt{\varepsilon_0^2 - \|c(x_1)\|^2}$. -/
  t_one : D.t 1 = f x₁ - √(ε 0 ^ 2 - ‖c x₁‖ ^ 2)
  /-- Step 1: the new iterate $x_{k+1}$ lies in $X$. -/
  mem_succ : ∀ k, 1 ≤ k → D.Before f c X q θ ε k → D.x (k + 1) ∈ X
  /-- Step 1: the radii $\delta_{k+1,j}$ lie in $(0, 1]$. -/
  radius_mem : ∀ k, 1 ≤ k → D.Before f c X q θ ε k →
    ∀ j ∈ Finset.Icc 1 q, 0 < D.δ (k + 1) j ∧ D.δ (k + 1) j ≤ 1
  /-- Step 1: the output condition (14.3.32) holds at $x_{k+1}$. -/
  output : ∀ k, 1 ≤ k → D.Before f c X q θ ε k →
    targetResidual f c (D.t k) (D.x (k + 1)) < θ * ε 0 ∨ f (D.x (k + 1)) < D.t k ∨
      targetCrit f c X q ε (D.t k) (D.x (k + 1)) (D.δ (k + 1))
  /-- Step 1: the inner call starts at $x_k$. -/
  inner_zero : ∀ k, 1 ≤ k → D.Before f c X q θ ε k → D.xi k 0 = D.x k
  /-- Step 1: the inner call ends at $x_{k+1}$. -/
  inner_end : ∀ k, 1 ≤ k → D.Before f c X q θ ε k → D.xi k (D.e k) = D.x (k + 1)
  /-- Step 1: the inner method does not increase $\mu(\cdot, t_k)$. -/
  inner_mono : ∀ k, 1 ≤ k → D.Before f c X q θ ε k → ∀ i < D.e k,
    targetMerit f c (D.t k) (D.xi k (i + 1)) ≤ targetMerit f c (D.t k) (D.xi k i)
  /-- Step 1: the call stops as soon as $\|r(\cdot, t_k)\| < \theta\varepsilon_0$, so the residual
  is at least $\theta\varepsilon_0$ before the last iterate. -/
  inner_residual_ge : ∀ k, 1 ≤ k → D.Before f c X q θ ε k → ∀ i < D.e k,
    θ * ε 0 ≤ targetResidual f c (D.t k) (D.xi k i)
  /-- Step 2(a): the target update (14.3.33), $t_{k+1} = f(x_{k+1}) - \sqrt{\varepsilon_0^2 -
  \|c(x_{k+1})\|^2}$. -/
  t_succ_a : ∀ k, 1 ≤ k → D.Before f c X q θ ε k → D.IsKa f c θ ε k →
    D.t (k + 1) = f (D.x (k + 1)) - √(ε 0 ^ 2 - ‖c (D.x (k + 1))‖ ^ 2)
  /-- Step 2(b): the target update (14.3.35), $t_{k+1} = 2 f(x_{k+1}) - t_k$. -/
  t_succ_b : ∀ k, 1 ≤ k → D.Before f c X q θ ε k → D.IsKb f c θ ε k →
    D.t (k + 1) = 2 * f (D.x (k + 1)) - D.t k

namespace IsHighOrderTargetRun

variable {f : E → ℝ} {c : E → F} {X : Set E} {q : ℕ} {θ β : ℝ} {ε : ℕ → ℝ} {x₁ : E}
  {D : HighOrderTargetSeq E} (h : IsHighOrderTargetRun f c X q θ β ε x₁ D)
include h

/-- In a run, the primal tolerance satisfies $\varepsilon_0 > 0$. -/
theorem ε₀_pos : 0 < ε 0 := h.ε_pos 0 (by simp)

/-- In a run, $\varepsilon_j > 0$ for every $j = 1, \dots, q$. -/
theorem ε_pos' {j : ℕ} (hj : j ∈ Finset.Icc 1 q) : 0 < ε j :=
  h.ε_pos j (Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.mem_Icc.1 hj).2))

/-- In a run, the primal tolerance satisfies $\varepsilon_0 \le 1$. -/
theorem ε₀_le_one : ε 0 ≤ 1 := h.ε_le_one 0 (by simp)

/-- **A high-order target-following run is a run of the generic outer loop.** If $D$ is a run of
Phase 2 of TPqp-GC, then `Constrained.HighOrderTargetSeq.toTargetFollowingSeq` of $D$ is a
`Constrained.IsTargetFollowingRun` with the same $f$, $c$, $\theta$, $\varepsilon_0$, $X$ and
$x_1$.

The test of Step 2(a) is the strict test $\|r(x_{k+1}, t_k)\| < \theta\varepsilon_0$. -/
theorem toRun :
    IsTargetFollowingRun f c θ (ε 0) X x₁ (D.toTargetFollowingSeq f c X q θ ε) where
  θ_pos := h.θ_pos
  θ_lt_one := h.θ_lt_one
  ε₀_pos := h.ε₀_pos
  ε₀_le_one := h.ε₀_le_one
  residual_le_of_ka _ ha := le_of_lt ha
  le_residual_of_not_ka _ ha := not_lt.1 ha
  kb_iff _ := and_congr_left' not_lt.symm
  mem_one := h.mem_one
  norm_one_le := h.norm_one_le
  x_one := h.x_one
  t_one := h.t_one
  mem_succ := h.mem_succ
  output := h.output
  inner_zero := h.inner_zero
  inner_end := h.inner_end
  inner_mono k hk1 hk i hi := targetMerit_le_targetMerit_iff.1 (h.inner_mono k hk1 hk i hi)
  inner_residual_ge := h.inner_residual_ge
  t_succ_a := h.t_succ_a
  t_succ_b := h.t_succ_b

/-- In a run, $\mu(\cdot, t_k)$ is nonincreasing along the $k$-th inner call:
$\mu(x_{k,j}, t_k) \le \mu(x_{k,i}, t_k)$ for $i \le j \le e_k$, for every outer iteration
$k \ge 1$ that is reached. -/
theorem inner_merit_antitone {k : ℕ} (hk1 : 1 ≤ k) (hk : D.Before f c X q θ ε k) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ D.e k) :
    targetMerit f c (D.t k) (D.xi k j) ≤ targetMerit f c (D.t k) (D.xi k i) :=
  h.toRun.inner_merit_antitone hk1 hk hij hj

/-- In a run, $\|r(\cdot, t_k)\|$ is nonincreasing along the $k$-th inner call:
$\|r(x_{k,j}, t_k)\| \le \|r(x_{k,i}, t_k)\|$ for $i \le j \le e_k$, for every outer iteration
$k \ge 1$ that is reached. -/
theorem inner_residual_antitone {k : ℕ} (hk1 : 1 ≤ k) (hk : D.Before f c X q θ ε k) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ D.e k) :
    targetResidual f c (D.t k) (D.xi k j) ≤ targetResidual f c (D.t k) (D.xi k i) :=
  h.toRun.inner_residual_antitone hk1 hk hij hj

/-- In a run, $\|r(x_{k+1}, t_k)\| \le \|r(x_k, t_k)\|$ for every outer iteration $k \ge 1$ that is
reached. -/
theorem residual_succ_le {k : ℕ} (hk1 : 1 ≤ k) (hk : D.Before f c X q θ ε k) :
    targetResidual f c (D.t k) (D.x (k + 1)) ≤ targetResidual f c (D.t k) (D.x k) :=
  h.toRun.residual_succ_le hk1 hk

/-- In a run, $\|r(x_k, t_k)\| \le \varepsilon_0$ for every outer iteration $k \ge 1$ that is
reached. -/
theorem residual_le {k : ℕ} (hk1 : 1 ≤ k) (hk : D.Before f c X q θ ε k) :
    targetResidual f c (D.t k) (D.x k) ≤ ε 0 :=
  h.toRun.residual_le hk1 hk

/-- In a run, $x_k \in X$ for every outer iteration $k \ge 1$ that is reached. -/
theorem x_mem : ∀ k, 1 ≤ k → D.Before f c X q θ ε k → D.x k ∈ X :=
  h.toRun.x_mem

/-- **The outer bookkeeping of Phase 2.** In a run, the outer iterates, the targets and the case-(a)
test form a target sequence (`Constrained.IsTargetSequence`) up to every outer iteration $K$
that is reached. Hence Lemmas 7.2.3 and 7.2.4 of [cartis2022evaluation] hold for the run. -/
theorem isTargetSequence {K : ℕ} (hK : D.Before f c X q θ ε K) :
    IsTargetSequence f c θ (ε 0) D.x D.t (D.IsKa f c θ ε) K :=
  h.toRun.isTargetSequence hK

/-- **The output of Phase 2** ((14.3.48), (14.3.49) and (14.3.52) of [cartis2022evaluation]). Let
Phase 2 terminate at outer iteration $k_\varepsilon$, with output point
$x_\varepsilon = x_{k_\varepsilon + 1}$, output target $t_\varepsilon$
(`Constrained.HighOrderTargetSeq.targetOut`) and radii $\delta_\varepsilon =
\delta_{k_\varepsilon + 1}$. Then
$$\theta\varepsilon_0 \le \|r(x_\varepsilon, t_\varepsilon)\| \le \varepsilon_0, \qquad
  t_\varepsilon \le f(x_\varepsilon),$$
and the criticality test (14.3.34) holds at $(x_\varepsilon, t_\varepsilon)$ with the radii
$\delta_\varepsilon$. -/
theorem output_spec {kε : ℕ} (hend : D.IsEnd f c X q θ ε kε) :
    θ * ε 0 ≤ targetResidual f c (D.targetOut f c θ ε kε) (D.x (kε + 1)) ∧
      targetResidual f c (D.targetOut f c θ ε kε) (D.x (kε + 1)) ≤ ε 0 ∧
      D.targetOut f c θ ε kε ≤ f (D.x (kε + 1)) ∧
      targetCrit f c X q ε (D.targetOut f c θ ε kε) (D.x (kε + 1)) (D.δ (kε + 1)) :=
  (h.toRun.output_spec hend).2

/-- **Lemma 7.2.4** of [cartis2022evaluation] for high-order runs. Assume that
$f_{\mathrm{low}} \le f(z) \le f_{\mathrm{up}}$ for every $z \in X$ with
$\|c(z)\| \le \varepsilon_0$ (assumption f.B.Fb). Then every outer iteration $K \ge 1$ that is
reached satisfies
$$|\mathcal{K}_a \cap [1, K)| \le \frac{f_{\mathrm{up}} - f_{\mathrm{low}} + 1}{(1 -
  \theta)\varepsilon_0}.$$
-/
theorem kaCount_le {flow fup : ℝ} (hB : ∀ z ∈ X, ‖c z‖ ≤ ε 0 → flow ≤ f z ∧ f z ≤ fup) {K : ℕ}
    (hK1 : 1 ≤ K) (hK : D.Before f c X q θ ε K) :
    (D.kaCount f c θ ε K : ℝ) ≤ (fup - flow + 1) / ((1 - θ) * ε 0) :=
  h.toRun.kaCount_le hB hK1 hK

end IsHighOrderTargetRun

/-! ### Construction of runs from an inner oracle -/

section Construction

/-- The data of one inner call of Phase 2: its iterates, its length, its successful iterations and
its returned optimality radii. -/
structure InnerCall (E : Type*) where
  /-- The iterates $x_0, x_1, \dots$ of the call. -/
  xi : ℕ → E
  /-- The number $e$ of iterations of the call. -/
  e : ℕ
  /-- The successful iterations of the call. -/
  succ : ℕ → Prop
  /-- The returned optimality radii $\delta_j$. -/
  δ : ℕ → ℝ

variable {f : E → ℝ} {c : E → F} {X : Set E} {q : ℕ} {θ β : ℝ} {ε : ℕ → ℝ}

open Classical in
/-- **Construction of runs of Phase 2 from an inner oracle.** Let $\theta \in (0, 1)$,
$\beta \in (0, \theta]$, $\varepsilon_j \in (0, 1]$ for $j = 0, \dots, q$, and $x_1 \in X$ with
$\|c(x_1)\| \le \theta\varepsilon_0$. Let `Good` be a property of a point $x$, a target $t$ and
a call $o$. Suppose that for every admissible pair $(x, t)$, that is, $x \in X$,
$\theta\varepsilon_0 \le \|r(x, t)\| \le \varepsilon_0$ and $t \le f(x)$, there is a call $o$
with $e$ iterations such that:

* the call starts at $o_0 = x$ and ends at a point $o_e \in X$ with radii $\delta_j \in (0, 1]$
  for $j = 1, \dots, q$;
* at $o_e$ one of the three tests of (14.3.32) holds: $\|r(o_e, t)\| < \theta\varepsilon_0$, or
  $f(o_e) < t$, or the criticality test (14.3.34) at $(o_e, t)$ with the radii $\delta$;
* the iterates do not increase $\mu(\cdot, t)$, and $\|r(o_i, t)\| \ge \theta\varepsilon_0$ for
  every $i < e$;
* $\|r(o_e, t)\| \le \|r(x, t)\|$;
* the property `Good x t o` holds.

Then there is a run of Phase 2 from $x_1$ such that, for every outer iteration $k \ge 1$ that is
reached, the pair $(x_k, t_k)$ is admissible and the $k$-th call, with the radii $\delta_{k+1}$,
has the property `Good` at $(x_k, t_k)$. -/
theorem HighOrderTargetSeq.exists_run_of_oracle (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβ0 : 0 < β)
    (hβθ : β ≤ θ) (hε : ∀ j ∈ Finset.range (q + 1), 0 < ε j ∧ ε j ≤ 1) {x₁ : E} (hx₁ : x₁ ∈ X)
    (hc₁ : ‖c x₁‖ ≤ θ * ε 0) (Good : E → ℝ → InnerCall E → Prop)
    (hgood : ∀ x t, x ∈ X → θ * ε 0 ≤ targetResidual f c t x →
      targetResidual f c t x ≤ ε 0 → t ≤ f x → ∃ o : InnerCall E,
        o.xi 0 = x ∧ o.xi o.e ∈ X ∧ (∀ j ∈ Finset.Icc 1 q, 0 < o.δ j ∧ o.δ j ≤ 1) ∧
        (targetResidual f c t (o.xi o.e) < θ * ε 0 ∨ f (o.xi o.e) < t ∨
          targetCrit f c X q ε t (o.xi o.e) o.δ) ∧
        (∀ i < o.e, targetMerit f c t (o.xi (i + 1)) ≤ targetMerit f c t (o.xi i)) ∧
        (∀ i < o.e, θ * ε 0 ≤ targetResidual f c t (o.xi i)) ∧
        targetResidual f c t (o.xi o.e) ≤ targetResidual f c t x ∧
        Good x t o) :
    ∃ D : HighOrderTargetSeq E, IsHighOrderTargetRun f c X q θ β ε x₁ D ∧
      ∀ k, 1 ≤ k → D.Before f c X q θ ε k →
        (D.x k ∈ X ∧ θ * ε 0 ≤ targetResidual f c (D.t k) (D.x k) ∧
          targetResidual f c (D.t k) (D.x k) ≤ ε 0 ∧ D.t k ≤ f (D.x k)) ∧
        Good (D.x k) (D.t k) ⟨D.xi k, D.e k, D.succ k, D.δ (k + 1)⟩ := by
  have hε₀ := hε 0 (by simp)
  let Valid : E × ℝ → Prop := fun a => a.1 ∈ X ∧
    θ * ε 0 ≤ targetResidual f c a.2 a.1 ∧ targetResidual f c a.2 a.1 ≤ ε 0 ∧ a.2 ≤ f a.1
  have hcall : ∀ a : E × ℝ, ∃ o : InnerCall E, Valid a → o.xi 0 = a.1 ∧ o.xi o.e ∈ X ∧
      (∀ j ∈ Finset.Icc 1 q, 0 < o.δ j ∧ o.δ j ≤ 1) ∧
      (targetResidual f c a.2 (o.xi o.e) < θ * ε 0 ∨ f (o.xi o.e) < a.2 ∨
        targetCrit f c X q ε a.2 (o.xi o.e) o.δ) ∧
      (∀ i < o.e, targetMerit f c a.2 (o.xi (i + 1)) ≤ targetMerit f c a.2 (o.xi i)) ∧
      (∀ i < o.e, θ * ε 0 ≤ targetResidual f c a.2 (o.xi i)) ∧
      targetResidual f c a.2 (o.xi o.e) ≤ targetResidual f c a.2 a.1 ∧
      Good a.1 a.2 o := by
    intro a
    by_cases ha : Valid a
    · obtain ⟨o, ho⟩ := hgood a.1 a.2 ha.1 ha.2.1 ha.2.2.1 ha.2.2.2
      exact ⟨o, fun _ => ho⟩
    · exact ⟨⟨fun _ => a.1, 0, fun _ => False, fun _ => 1⟩, fun h' => absurd h' ha⟩
  choose call hcall using hcall
  -- the target update of Step 2
  let tupd : E × ℝ → ℝ := fun a =>
    if targetResidual f c a.2 ((call a).xi (call a).e) < θ * ε 0 then
      f ((call a).xi (call a).e) - √(ε 0 ^ 2 - ‖c ((call a).xi (call a).e)‖ ^ 2)
    else if f ((call a).xi (call a).e) < a.2 then 2 * f ((call a).xi (call a).e) - a.2 else a.2
  let next : E × ℝ → E × ℝ := fun a => ((call a).xi (call a).e, tupd a)
  let G : ℕ → E × ℝ := fun k =>
    Nat.rec (x₁, f x₁ - √(ε 0 ^ 2 - ‖c x₁‖ ^ 2)) (fun _ a => next a) k
  let D : HighOrderTargetSeq E :=
    { x := fun k => (G (k - 1)).1
      t := fun k => (G (k - 1)).2
      δ := fun k => (call (G (k - 2))).δ
      xi := fun k => (call (G (k - 1))).xi
      e := fun k => (call (G (k - 1))).e
      succ := fun k => (call (G (k - 1))).succ }
  -- the invariant along Phase 2
  have hθε : θ * ε 0 ≤ ε 0 := by nlinarith
  have hinv : ∀ j, D.Before f c X q θ ε (j + 1) → Valid (G j) := by
    intro j
    induction j with
    | zero =>
      intro _
      have hc' : ‖c x₁‖ ≤ ε 0 := hc₁.trans hθε
      have hr : targetResidual f c (G 0).2 (G 0).1 = ε 0 := targetResidual_sub_sqrt hε₀.1.le hc'
      exact ⟨hx₁, hr ▸ hθε, hr.le, by
        change f x₁ - √(ε 0 ^ 2 - ‖c x₁‖ ^ 2) ≤ f x₁
        linarith [Real.sqrt_nonneg (ε 0 ^ 2 - ‖c x₁‖ ^ 2)]⟩
    | succ j ih =>
      intro hb
      have hbj : D.Before f c X q θ ε (j + 1) := hb.mono (by omega)
      have hv := ih hbj
      obtain ⟨-, hmem, -, -, -, -, hres, -⟩ := hcall (G j) hv
      have hns : ¬ D.Stop f c X q θ ε (j + 1) := hb (j + 1) (by omega) (by omega)
      have hab := TargetFollowingSeq.ka_or_kb_of_not_stop hns
      change Valid (next (G j))
      refine ⟨hmem, ?_⟩
      rcases hab with ha | hb'
      · have ha' : targetResidual f c (G j).2 ((call (G j)).xi (call (G j)).e) < θ * ε 0 := ha
        have hc' : ‖c ((call (G j)).xi (call (G j)).e)‖ ≤ ε 0 :=
          (norm_le_targetResidual.trans ha'.le).trans hθε
        have ht : (next (G j)).2 = f ((call (G j)).xi (call (G j)).e) -
            √(ε 0 ^ 2 - ‖c ((call (G j)).xi (call (G j)).e)‖ ^ 2) := by
          simp only [next, tupd, ite_eq_left ha']
        have hr : targetResidual f c (next (G j)).2 (next (G j)).1 = ε 0 := by
          rw [ht]
          exact targetResidual_sub_sqrt hε₀.1.le hc'
        refine ⟨hr ▸ hθε, hr.le, ?_⟩
        rw [ht]
        linarith [Real.sqrt_nonneg (ε 0 ^ 2 - ‖c ((call (G j)).xi (call (G j)).e)‖ ^ 2)]
      · obtain ⟨hge, hlt⟩ := hb'
        have hge' : θ * ε 0 ≤ targetResidual f c (G j).2 ((call (G j)).xi (call (G j)).e) := hge
        have hlt' : f ((call (G j)).xi (call (G j)).e) < (G j).2 := hlt
        have ht : (next (G j)).2 = 2 * f ((call (G j)).xi (call (G j)).e) - (G j).2 := by
          simp only [next, tupd, ite_eq_right (not_lt.2 hge'), ite_eq_left hlt']
        have hr : targetResidual f c (next (G j)).2 (next (G j)).1 =
            targetResidual f c (G j).2 ((call (G j)).xi (call (G j)).e) := by
          rw [ht]
          exact targetResidual_two_mul_sub
        refine ⟨hr ▸ hge', hr ▸ hres.trans hv.2.2.1, ?_⟩
        rw [ht]
        change 2 * f ((call (G j)).xi (call (G j)).e) - (G j).2 ≤ f ((call (G j)).xi (call (G j)).e)
        linarith
  have hspec : ∀ k, 1 ≤ k → D.Before f c X q θ ε k → ∃ j, k = j + 1 ∧ Valid (G j) :=
    fun k hk1 hk => by
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hk1
      exact ⟨j, rfl, hinv j hk⟩
  refine ⟨D, ⟨hθ0, hθ1, hβ0, hβθ, fun j hj => (hε j hj).1, fun j hj => (hε j hj).2, hx₁, hc₁,
    rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro k hk1 hk
    obtain ⟨j, rfl, hv⟩ := hspec k hk1 hk
    exact (hcall _ hv).2.1
  · intro k hk1 hk
    obtain ⟨j, rfl, hv⟩ := hspec k hk1 hk
    exact (hcall _ hv).2.2.1
  · intro k hk1 hk
    obtain ⟨j, rfl, hv⟩ := hspec k hk1 hk
    exact (hcall _ hv).2.2.2.1
  · intro k hk1 hk
    obtain ⟨j, rfl, hv⟩ := hspec k hk1 hk
    exact (hcall _ hv).1
  · intro k hk1 hk
    obtain ⟨j, rfl, hv⟩ := hspec k hk1 hk
    rfl
  · intro k hk1 hk
    obtain ⟨j, rfl, hv⟩ := hspec k hk1 hk
    exact (hcall _ hv).2.2.2.2.1
  · intro k hk1 hk
    obtain ⟨j, rfl, hv⟩ := hspec k hk1 hk
    exact (hcall _ hv).2.2.2.2.2.1
  · intro k hk1 hk ha
    obtain ⟨j, rfl, hv⟩ := hspec k hk1 hk
    exact ite_eq_left ha
  · intro k hk1 hk hb
    obtain ⟨j, rfl, hv⟩ := hspec k hk1 hk
    obtain ⟨hge, hlt⟩ := hb
    exact (ite_eq_right (not_lt.2 hge)).trans (ite_eq_left hlt)
  · intro k hk1 hk
    obtain ⟨j, rfl, hv⟩ := hspec k hk1 hk
    exact ⟨hv, (hcall _ hv).2.2.2.2.2.2.2⟩

end Construction

end Constrained
