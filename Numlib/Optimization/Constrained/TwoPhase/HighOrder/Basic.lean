import Numlib.Optimization.Constrained.TwoPhase.Complexity

/-!
# High-order target-following runs

Phase 2 of the two-phase method TPqp-GC (Algorithm 14.3.2 of [cartis2022evaluation]) for
`min f(x)` subject to `x ∈ X`, `c(x) = 0`, with `f : E → ℝ`, `c : E → F` on a normed space `E`
(`F` an inner product space), follows decreasing targets `t_k` as the generic outer loop of
`Numlib.Optimization.Constrained.TwoPhase.Run`, with the criticality test of order `q`
(14.3.34): at the output `y` of an inner call, for a target `t` and optimality radii `δ`,
`φ^{δ_j}_{μ,X(y),j}(y, t) ≤ ε_j ‖r(y, t)‖ δ_j^j/j!` for `j ∈ [1 : q]`, where `μ(·, t)` is the
merit function `½ ‖r(·, t)‖²` (`Constrained.targetMerit`) and `φ` the Taylor measure on the
feasible displacements (`Optimization.taylorMeasure`). The tolerances are `ε : ℕ → ℝ`, `ε₀ = ε 0`
being the primal one.

This file defines the data and the run predicate, maps them to the generic outer loop, and
constructs runs from an inner oracle.

## Main definitions

* `Constrained.targetCrit f c X q ε t y δ`: the criticality test (14.3.34);
* `Constrained.HighOrderTargetSeq E`: outer iterates, targets, optimality radii, inner iterates,
  call lengths and successful inner iterations;
* `Constrained.HighOrderTargetSeq.toTargetFollowingSeq`: the data of the generic outer loop, with
  the tests `IsKa`, `IsKb` and `targetCrit`;
* `Constrained.HighOrderTargetSeq.InnerTest`: the termination test (14.3.19) of the inner method
  called with tolerances `β ‖r(x_k, t_k)‖ ε_j`;
* `Constrained.HighOrderTargetSeq.succCount`, `kaCount`, `kbCount`, `funEvals`, `derivEvals`,
  `targetOut`, `goodCount`, `badCount`: the counts and the output target of Phase 2, those of the
  generic outer loop on `toCountSeq` (the data with only the tests a count uses) or on
  `toTargetFollowingSeq`;
* `Constrained.IsHighOrderTargetRun f c X q θ β ε x₁ D`: `D` is a run of Phase 2 from `x₁`;
* `Constrained.InnerCall E`: the data of one inner call.

## Main results

* `Constrained.IsHighOrderTargetRun.toRun`: a run is a run of the generic outer loop;
* `Constrained.IsHighOrderTargetRun.output_spec`: the output satisfies (14.3.48), (14.3.49) and
  (14.3.52);
* `Constrained.IsHighOrderTargetRun.kaCount_le`: Lemma 7.2.4,
  `|𝒦_a| ≤ (f_up - f_low + 1)/((1 - θ)ε₀)`;
* `Constrained.HighOrderTargetSeq.exists_run_of_oracle`: an inner oracle producing admissible
  calls from every admissible point yields a run whose calls are produced by the oracle.

## Implementation notes

The data `Constrained.HighOrderTargetSeq` only add the optimality radii and the successful inner
iterations to those of the generic outer loop; `toTargetFollowingSeq` and
`Constrained.IsHighOrderTargetRun.toRun` transfer every counting and termination statement of
`Numlib.Optimization.Constrained.TwoPhase.Run` and `…Complexity` to the high-order run, and the
termination predicates `Stop`, `Before`, `IsEnd` are reducible abbreviations of the generic ones.
`Constrained.targetCrit` is stated in unfolded form (`targetCrit_iff`) and is the
`(ε, δ)`-approximate criticality `Optimization.IsEpsDeltaApprox` of `μ(·, t)` with the
tolerances scaled by `‖r(y, t)‖` (`targetCrit_iff_isEpsDeltaApprox`). The construction
`Constrained.HighOrderTargetSeq.exists_run_of_oracle` is generic in an extra property `Good` of the
calls, so that each realization of the inner method (regularization, trust region, …) yields runs
whose calls carry the certificates of that method.

Step 2(a) uses the strict test `‖r(x_{k+1}, t_k)‖ < θε₀` (`IsKa`). The inner calls
are described by their iterates: `μ(·, t_k)` does not increase along a call, and a call is stopped
as soon as `‖r(·, t_k)‖ < θε₀` (this makes every successful iteration but the last one of a call
count in the telescoping argument).
-/

open Finset
open scoped Nat

namespace Constrained

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]

/-! ### The criticality test -/

section Crit

/-- **The criticality test (14.3.34)** of [cartis2022evaluation] (also the third stopping test of
(14.3.32)) at the point `y` for the target `t` with optimality radii `δ`:
`φ^{δ_j}_{μ,X(y),j}(y, t) ≤ ε_j ‖r(y, t)‖ δ_j^j/j!` for `j ∈ [1 : q]`, where
`μ(·, t) = targetMerit f c t` and `X(y) = {d | y + d ∈ X}` (`targetCrit_iff_isEpsDeltaApprox`:
the `(ε', δ)`-approximate `q`-th order criticality of `μ(·, t)` for the tolerances
`ε'_j = ε_j ‖r(y, t)‖`). -/
def targetCrit (f : E → ℝ) (c : E → F) (X : Set E) (q : ℕ) (ε : ℕ → ℝ) (t : ℝ) (y : E)
    (δ : ℕ → ℝ) : Prop :=
  ∀ j ∈ Finset.Icc 1 q,
    Optimization.taylorMeasure (ftaylorSeries ℝ (targetMerit f c t) y) j (δ j) {d | y + d ∈ X} ≤
      ε j * targetResidual f c t y * δ j ^ j / j !

variable {f : E → ℝ} {c : E → F} {X : Set E} {q : ℕ} {ε ε' : ℕ → ℝ} {t : ℝ} {y : E}
  {δ : ℕ → ℝ}

theorem targetCrit_iff :
    targetCrit f c X q ε t y δ ↔ ∀ j ∈ Finset.Icc 1 q,
      Optimization.taylorMeasure (ftaylorSeries ℝ (targetMerit f c t) y) j (δ j)
        {d | y + d ∈ X} ≤ ε j * targetResidual f c t y * δ j ^ j / j ! :=
  Iff.rfl

theorem targetCrit_iff_isEpsDeltaApprox :
    targetCrit f c X q ε t y δ ↔ Optimization.IsEpsDeltaApprox
      (ftaylorSeries ℝ (targetMerit f c t) y) {d | y + d ∈ X} q
      (fun j => ε j * targetResidual f c t y) δ :=
  Iff.rfl

/-- The criticality test is monotone in the tolerances. -/
theorem targetCrit.mono (h : targetCrit f c X q ε' t y δ) (hε : ∀ j ∈ Finset.Icc 1 q, ε' j ≤ ε j)
    (hδ : ∀ j ∈ Finset.Icc 1 q, 0 ≤ δ j) : targetCrit f c X q ε t y δ := fun j hj =>
  (h j hj).trans (by
    have := hδ j hj
    have := targetResidual_nonneg (f := f) (c := c) (t := t) (x := y)
    gcongr
    exact hε j hj)

end Crit

/-! ### The data of Phase 2 -/

/-- The sequences of Phase 2 of a high-order target-following method ([cartis2022evaluation],
Algorithm 14.3.2), indexed by the outer iteration `k ≥ 1` (values at `k = 0` are unused): outer
iterates `x k`, targets `t k`, optimality radii `δ k`, and for the `k`-th call of the inner method
on `μ(·, t_k)` its iterates `xi k i`, its number of iterations `e k` and its successful iterations
`succ k i`. -/
structure HighOrderTargetSeq (E : Type*) where
  /-- The outer iterates. -/
  x : ℕ → E
  /-- The targets. -/
  t : ℕ → ℝ
  /-- The optimality radii. -/
  δ : ℕ → ℕ → ℝ
  /-- The inner iterates. -/
  xi : ℕ → ℕ → E
  /-- The numbers of inner iterations. -/
  e : ℕ → ℕ
  /-- The successful inner iterations. -/
  succ : ℕ → ℕ → Prop

namespace HighOrderTargetSeq

variable (f : E → ℝ) (c : E → F) (X : Set E) (q : ℕ) (θ β : ℝ) (ε : ℕ → ℝ)
  (D : HighOrderTargetSeq E)

/-- Outer iteration `k` is in `𝒦_a` ((14.3.36) of [cartis2022evaluation]): Step 2(a) occurs,
`‖r(x_{k+1}, t_k)‖ < θε₀`. -/
def IsKa (k : ℕ) : Prop := targetResidual f c (D.t k) (D.x (k + 1)) < θ * ε 0

/-- Outer iteration `k` is in `𝒦_b`: Step 2(b) occurs, `‖r(x_{k+1}, t_k)‖ ≥ θε₀` and
`f(x_{k+1}) < t_k`. -/
def IsKb (k : ℕ) : Prop :=
  θ * ε 0 ≤ targetResidual f c (D.t k) (D.x (k + 1)) ∧ f (D.x (k + 1)) < D.t k

/-- The data of Phase 2 as data of the generic target-following outer loop
(`Constrained.TargetFollowingSeq`): the tests are `𝒦_a`, `𝒦_b` and the criticality test
(14.3.34) at `x_{k+1}` with the radii `δ_{k+1}`. -/
def toTargetFollowingSeq : TargetFollowingSeq E where
  x := D.x
  t := D.t
  xi := D.xi
  e := D.e
  Ka := D.IsKa f c θ ε
  Kb := D.IsKb f c θ ε
  crit k τ := targetCrit f c X q ε τ (D.x (k + 1)) (D.δ (k + 1))

/-- The criticality test (14.3.34) at the output `x_{k+1}` of the `k`-th inner call for the old
target `t_k`, with the radii `δ_{k+1}` (the third stopping test of (14.3.32)). -/
abbrev EndCrit (k : ℕ) : Prop := targetCrit f c X q ε (D.t k) (D.x (k + 1)) (D.δ (k + 1))

/-- Phase 2 terminates at outer iteration `k`: in case (c), or in cases (a)/(b) when (14.3.34)
holds at `(x_{k+1}, t_{k+1})` with the radii `δ_{k+1}`. -/
abbrev Stop (k : ℕ) : Prop := (D.toTargetFollowingSeq f c X q θ ε).Stop k

/-- No outer iteration `j ∈ [1, k)` has terminated Phase 2. -/
abbrev Before (k : ℕ) : Prop := (D.toTargetFollowingSeq f c X q θ ε).Before k

/-- Phase 2 terminates at outer iteration `kε ≥ 1`. -/
abbrev IsEnd (kε : ℕ) : Prop := (D.toTargetFollowingSeq f c X q θ ε).IsEnd kε

/-- The data of Phase 2 as data of the generic outer loop with the tests `Ka`, `Kb` and no
criticality test, on which the counts that involve only some of the tests are taken (the counts
of the outer loop do not involve the criticality test). -/
def toCountSeq (Ka Kb : ℕ → Prop) : TargetFollowingSeq E where
  x := D.x
  t := D.t
  xi := D.xi
  e := D.e
  Ka := Ka
  Kb := Kb
  crit _ _ := False

/-- The output target `t_ε` of Phase 2 terminating at outer iteration `k`: `t_{k+1}` in cases
(a)/(b) and `t_k` in case (c) (the output point is `x_ε = x_{k+1}`). -/
noncomputable abbrev targetOut (k : ℕ) : ℝ :=
  (D.toCountSeq (D.IsKa f c θ ε) (D.IsKb f c θ ε)).targetOut k

theorem targetOut_eq (k : ℕ) :
    D.targetOut f c θ ε k = (D.toTargetFollowingSeq f c X q θ ε).targetOut k := rfl

/-- **The termination test (14.3.19) of the inner method** at the end of the `k`-th call
([cartis2022evaluation], Algorithm 14.3.2, Step 1, the call
`INNER(μ(·, t_k), X, q, x_k, β ‖r(x_k, t_k)‖ ε)`):
`φ^{δ_{k+1,j}}_{μ,X(x_{k+1}),j}(x_{k+1}, t_k) ≤ β ‖r(x_k, t_k)‖ ε_j δ_{k+1,j}^j/j!` for
`j ∈ [1 : q]`. Its tolerance is at most that of (14.3.34) at `(x_{k+1}, t_k)` when `β ≤ θ` and
`‖r(x_{k+1}, t_k)‖ ≥ θε₀`. -/
def InnerTest (k : ℕ) : Prop :=
  ∀ j ∈ Finset.Icc 1 q,
    Optimization.taylorMeasure (ftaylorSeries ℝ (targetMerit f c (D.t k)) (D.x (k + 1))) j
        (D.δ (k + 1) j) {d | D.x (k + 1) + d ∈ X} ≤
      β * targetResidual f c (D.t k) (D.x k) * ε j * D.δ (k + 1) j ^ j / j !

/-! ### Counts -/

/-- The number of successful iterations of the `k`-th inner call. -/
noncomputable abbrev succCount (k : ℕ) : ℕ :=
  (D.toCountSeq (fun _ => False) fun _ => False).succCount D.succ k

/-- The number of outer iterations of `𝒦_a` among `[1, K)`. -/
noncomputable abbrev kaCount (K : ℕ) : ℕ :=
  (D.toCountSeq (D.IsKa f c θ ε) fun _ => False).kaCount K

/-- The number of outer iterations of `𝒦_b` among `[1, K)`. -/
noncomputable abbrev kbCount (K : ℕ) : ℕ :=
  (D.toCountSeq (fun _ => False) (D.IsKb f c θ ε)).kbCount K

/-- The number of evaluations of `(f, c)` in Phase 2 up to outer iteration `k`:
`1 + ∑_{j ∈ [1, k]} e_j` (one at `x₁` and one per inner iteration). -/
noncomputable abbrev funEvals (k : ℕ) : ℕ :=
  (D.toCountSeq (fun _ => False) fun _ => False).funEvals k

/-- The number of evaluations of the derivatives of `(f, c)` in Phase 2 up to outer iteration
`k`: one at `x₁` and one per successful inner iteration. -/
noncomputable abbrev derivEvals (k : ℕ) : ℕ :=
  (D.toCountSeq (fun _ => False) fun _ => False).derivEvals D.succ k

/-- A *good* inner iteration `(k, i)` for the exemption by (14.3.34) at the old target
([cartis2022evaluation], proof of Lemma 14.3.8): it is successful, it is not the last iteration
of a call ending at a point passing `EndCrit`, and its new iterate has residual `≥ θε₀`. -/
abbrev IsGood (k i : ℕ) : Prop :=
  (D.toTargetFollowingSeq f c X q θ ε).IsGood f c θ (ε 0) D.succ (D.EndCrit f c X q ε) k i

/-- The number of good iterations of the `k`-th inner call. -/
noncomputable abbrev goodCount (k : ℕ) : ℕ :=
  (D.toTargetFollowingSeq f c X q θ ε).goodCount f c θ (ε 0) D.succ (D.EndCrit f c X q ε) k

/-- A *bad* outer iteration: `k ∈ 𝒦_b` and its inner call contains no good iteration. -/
abbrev IsBad (k : ℕ) : Prop :=
  (D.toTargetFollowingSeq f c X q θ ε).IsBad f c θ (ε 0) D.succ (D.EndCrit f c X q ε) k

/-- The number of bad outer iterations among `[1, K)`. -/
noncomputable abbrev badCount (K : ℕ) : ℕ :=
  (D.toTargetFollowingSeq f c X q θ ε).badCount f c θ (ε 0) D.succ (D.EndCrit f c X q ε) K

variable {f c X q θ ε D}

theorem succCount_eq (k : ℕ) :
    D.succCount k = (D.toTargetFollowingSeq f c X q θ ε).succCount D.succ k := rfl

theorem kaCount_eq (K : ℕ) :
    D.kaCount f c θ ε K = (D.toTargetFollowingSeq f c X q θ ε).kaCount K := rfl

theorem kbCount_eq (K : ℕ) :
    D.kbCount f c θ ε K = (D.toTargetFollowingSeq f c X q θ ε).kbCount K := rfl

theorem funEvals_eq (k : ℕ) :
    D.funEvals k = (D.toTargetFollowingSeq f c X q θ ε).funEvals k := rfl

theorem derivEvals_eq (k : ℕ) :
    D.derivEvals k = (D.toTargetFollowingSeq f c X q θ ε).derivEvals D.succ k := rfl

section Tests

omit [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem isKa_iff {k : ℕ} :
    D.IsKa f c θ ε k ↔ targetResidual f c (D.t k) (D.x (k + 1)) < θ * ε 0 := Iff.rfl

theorem isKb_iff {k : ℕ} :
    D.IsKb f c θ ε k ↔
      θ * ε 0 ≤ targetResidual f c (D.t k) (D.x (k + 1)) ∧ f (D.x (k + 1)) < D.t k := Iff.rfl

theorem succCount_eq_card_filter (k : ℕ) [DecidablePred (D.succ k)] :
    D.succCount k = ((Finset.range (D.e k)).filter (D.succ k)).card :=
  TargetFollowingSeq.succCount_eq_card_filter k

theorem targetOut_of_ka_or_kb {k : ℕ} (h : D.IsKa f c θ ε k ∨ D.IsKb f c θ ε k) :
    D.targetOut f c θ ε k = D.t (k + 1) :=
  TargetFollowingSeq.targetOut_of_ka_or_kb h

theorem targetOut_of_not {k : ℕ} (ha : ¬ D.IsKa f c θ ε k) (hb : ¬ D.IsKb f c θ ε k) :
    D.targetOut f c θ ε k = D.t k :=
  TargetFollowingSeq.targetOut_of_not ha hb

theorem kaCount_eq_card_filter (K : ℕ) [DecidablePred (D.IsKa f c θ ε)] :
    D.kaCount f c θ ε K = ((Finset.Ico 1 K).filter (D.IsKa f c θ ε)).card :=
  letI : DecidablePred (D.toCountSeq (D.IsKa f c θ ε) fun _ => False).Ka := ‹_›
  TargetFollowingSeq.kaCount_eq_card_filter K

theorem kbCount_eq_card_filter (K : ℕ) [DecidablePred (D.IsKb f c θ ε)] :
    D.kbCount f c θ ε K = ((Finset.Ico 1 K).filter (D.IsKb f c θ ε)).card :=
  letI : DecidablePred (D.toCountSeq (fun _ => False) (D.IsKb f c θ ε)).Kb := ‹_›
  TargetFollowingSeq.kbCount_eq_card_filter K

theorem funEvals_eq_sum (k : ℕ) : D.funEvals k = 1 + ∑ j ∈ Finset.Icc 1 k, D.e j := rfl

theorem derivEvals_eq_sum (k : ℕ) :
    D.derivEvals k = 1 + ∑ j ∈ Finset.Icc 1 k, D.succCount j := rfl

end Tests

theorem innerTest_iff {β : ℝ} {k : ℕ} :
    D.InnerTest f c X q β ε k ↔ ∀ j ∈ Finset.Icc 1 q,
      Optimization.taylorMeasure (ftaylorSeries ℝ (targetMerit f c (D.t k)) (D.x (k + 1))) j
          (D.δ (k + 1) j) {d | D.x (k + 1) + d ∈ X} ≤
        β * targetResidual f c (D.t k) (D.x k) * ε j * D.δ (k + 1) j ^ j / j ! := Iff.rfl

end HighOrderTargetSeq

/-! ### The run predicate -/

/-- **A run of Phase 2 of a high-order target-following method** ([cartis2022evaluation],
Phase 2 of Algorithm 14.3.2, TPqp-GC), started at `x₁ ∈ X` with `‖c(x₁)‖ ≤ θε₀`, as a predicate
on the data `D`. Constants: `θ ∈ (0, 1)`, `β ∈ (0, θ]`, tolerances `ε_j ∈ (0, 1]`, `j ∈ [0 : q]`.
Step 0: `t₁ = f(x₁) - √(ε₀² - ‖c(x₁)‖²)`. For every outer iteration `k ≥ 1` reached: Step 1,
`x_{k+1} ∈ X` and radii `δ_{k+1} ∈ (0, 1]^q` satisfy (14.3.32), computed by a call of the inner
method on `μ(·, t_k)` from `x_k` whose iterates (`x_{k,0} = x_k`, `x_{k,e_k} = x_{k+1}`) do not
increase `μ(·, t_k)` and keep `‖r(·, t_k)‖ ≥ θε₀` before the last one; Step 2, the target updates
(14.3.33) in case (a) and (14.3.35) in case (b). Termination is `HighOrderTargetSeq.Stop`. -/
structure IsHighOrderTargetRun (f : E → ℝ) (c : E → F) (X : Set E) (q : ℕ) (θ β : ℝ)
    (ε : ℕ → ℝ) (x₁ : E) (D : HighOrderTargetSeq E) : Prop where
  θ_pos : 0 < θ
  θ_lt_one : θ < 1
  β_pos : 0 < β
  β_le_θ : β ≤ θ
  ε_pos : ∀ j ∈ Finset.range (q + 1), 0 < ε j
  ε_le_one : ∀ j ∈ Finset.range (q + 1), ε j ≤ 1
  /-- `x₁ ∈ X`. -/
  mem_one : x₁ ∈ X
  /-- Phase 1 ended with `‖c(x₁)‖ ≤ θε₀`. -/
  norm_one_le : ‖c x₁‖ ≤ θ * ε 0
  /-- Phase 2 starts at `x₁`. -/
  x_one : D.x 1 = x₁
  /-- Step 0. -/
  t_one : D.t 1 = f x₁ - √(ε 0 ^ 2 - ‖c x₁‖ ^ 2)
  /-- Step 1: the new iterate is feasible. -/
  mem_succ : ∀ k, 1 ≤ k → D.Before f c X q θ ε k → D.x (k + 1) ∈ X
  /-- Step 1: the radii lie in `(0, 1]`. -/
  radius_mem : ∀ k, 1 ≤ k → D.Before f c X q θ ε k →
    ∀ j ∈ Finset.Icc 1 q, 0 < D.δ (k + 1) j ∧ D.δ (k + 1) j ≤ 1
  /-- Step 1: the output condition (14.3.32). -/
  output : ∀ k, 1 ≤ k → D.Before f c X q θ ε k →
    targetResidual f c (D.t k) (D.x (k + 1)) < θ * ε 0 ∨ f (D.x (k + 1)) < D.t k ∨
      targetCrit f c X q ε (D.t k) (D.x (k + 1)) (D.δ (k + 1))
  /-- Step 1: the inner call starts at `x_k`. -/
  inner_zero : ∀ k, 1 ≤ k → D.Before f c X q θ ε k → D.xi k 0 = D.x k
  /-- Step 1: the inner call ends at `x_{k+1}`. -/
  inner_end : ∀ k, 1 ≤ k → D.Before f c X q θ ε k → D.xi k (D.e k) = D.x (k + 1)
  /-- Step 1: the inner method does not increase `μ(·, t_k)`. -/
  inner_mono : ∀ k, 1 ≤ k → D.Before f c X q θ ε k → ∀ i < D.e k,
    targetMerit f c (D.t k) (D.xi k (i + 1)) ≤ targetMerit f c (D.t k) (D.xi k i)
  /-- Step 1: the call is stopped as soon as `‖r(·, t_k)‖ < θε₀`. -/
  inner_residual_ge : ∀ k, 1 ≤ k → D.Before f c X q θ ε k → ∀ i < D.e k,
    θ * ε 0 ≤ targetResidual f c (D.t k) (D.xi k i)
  /-- Step 2(a): (14.3.33). -/
  t_succ_a : ∀ k, 1 ≤ k → D.Before f c X q θ ε k → D.IsKa f c θ ε k →
    D.t (k + 1) = f (D.x (k + 1)) - √(ε 0 ^ 2 - ‖c (D.x (k + 1))‖ ^ 2)
  /-- Step 2(b): (14.3.35). -/
  t_succ_b : ∀ k, 1 ≤ k → D.Before f c X q θ ε k → D.IsKb f c θ ε k →
    D.t (k + 1) = 2 * f (D.x (k + 1)) - D.t k

namespace IsHighOrderTargetRun

variable {f : E → ℝ} {c : E → F} {X : Set E} {q : ℕ} {θ β : ℝ} {ε : ℕ → ℝ} {x₁ : E}
  {D : HighOrderTargetSeq E} (h : IsHighOrderTargetRun f c X q θ β ε x₁ D)
include h

theorem ε₀_pos : 0 < ε 0 := h.ε_pos 0 (by simp)

theorem ε_pos' {j : ℕ} (hj : j ∈ Finset.Icc 1 q) : 0 < ε j :=
  h.ε_pos j (Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.mem_Icc.1 hj).2))

theorem ε₀_le_one : ε 0 ≤ 1 := h.ε_le_one 0 (by simp)

/-- **A high-order target-following run is a run of the generic outer loop**
(`Constrained.IsTargetFollowingRun`), with the strict test `‖r(x_{k+1}, t_k)‖ < θε₀` of
Step 2(a). -/
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

/-- `μ(·, t_k)` is nonincreasing along the `k`-th inner call. -/
theorem inner_merit_antitone {k : ℕ} (hk1 : 1 ≤ k) (hk : D.Before f c X q θ ε k) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ D.e k) :
    targetMerit f c (D.t k) (D.xi k j) ≤ targetMerit f c (D.t k) (D.xi k i) :=
  h.toRun.inner_merit_antitone hk1 hk hij hj

/-- `‖r(·, t_k)‖` is nonincreasing along the `k`-th inner call. -/
theorem inner_residual_antitone {k : ℕ} (hk1 : 1 ≤ k) (hk : D.Before f c X q θ ε k) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ D.e k) :
    targetResidual f c (D.t k) (D.xi k j) ≤ targetResidual f c (D.t k) (D.xi k i) :=
  h.toRun.inner_residual_antitone hk1 hk hij hj

/-- `‖r(x_{k+1}, t_k)‖ ≤ ‖r(x_k, t_k)‖`. -/
theorem residual_succ_le {k : ℕ} (hk1 : 1 ≤ k) (hk : D.Before f c X q θ ε k) :
    targetResidual f c (D.t k) (D.x (k + 1)) ≤ targetResidual f c (D.t k) (D.x k) :=
  h.toRun.residual_succ_le hk1 hk

/-- `‖r(x_k, t_k)‖ ≤ ε₀` at every outer iteration reached. -/
theorem residual_le {k : ℕ} (hk1 : 1 ≤ k) (hk : D.Before f c X q θ ε k) :
    targetResidual f c (D.t k) (D.x k) ≤ ε 0 :=
  h.toRun.residual_le hk1 hk

/-- The outer iterates stay in `X`. -/
theorem x_mem : ∀ k, 1 ≤ k → D.Before f c X q θ ε k → D.x k ∈ X :=
  h.toRun.x_mem

/-- **The outer bookkeeping of Phase 2** is a target sequence (`Constrained.IsTargetSequence`) up
to every outer iteration `K` reached; hence Lemmas 7.2.3 and 7.2.4 of [cartis2022evaluation]
hold. -/
theorem isTargetSequence {K : ℕ} (hK : D.Before f c X q θ ε K) :
    IsTargetSequence f c θ (ε 0) D.x D.t (D.IsKa f c θ ε) K :=
  h.toRun.isTargetSequence hK

/-- **The output of Phase 2** ([cartis2022evaluation], (14.3.48), (14.3.49), (14.3.52)): if
Phase 2 terminates at outer iteration `k_ε`, the output `x_ε = x_{k_ε+1}`, `t_ε = targetOut k_ε`
with radii `δ_ε = δ_{k_ε+1}` satisfies `θε₀ ≤ ‖r(x_ε, t_ε)‖ ≤ ε₀`, `f(x_ε) ≥ t_ε` and (14.3.34)
at `(x_ε, t_ε)`. -/
theorem output_spec {kε : ℕ} (hend : D.IsEnd f c X q θ ε kε) :
    θ * ε 0 ≤ targetResidual f c (D.targetOut f c θ ε kε) (D.x (kε + 1)) ∧
      targetResidual f c (D.targetOut f c θ ε kε) (D.x (kε + 1)) ≤ ε 0 ∧
      D.targetOut f c θ ε kε ≤ f (D.x (kε + 1)) ∧
      targetCrit f c X q ε (D.targetOut f c θ ε kε) (D.x (kε + 1)) (D.δ (kε + 1)) :=
  (h.toRun.output_spec hend).2

/-- **Lemma 7.2.4 for high-order runs** ([cartis2022evaluation]): under f.B.Fb
(`f_low ≤ f ≤ f_up` on the points of `X` with `‖c‖ ≤ ε₀`),
`|𝒦_a ∩ [1, K)| ≤ (f_up - f_low + 1)/((1 - θ)ε₀)`. -/
theorem kaCount_le {flow fup : ℝ} (hB : ∀ z ∈ X, ‖c z‖ ≤ ε 0 → flow ≤ f z ∧ f z ≤ fup) {K : ℕ}
    (hK1 : 1 ≤ K) (hK : D.Before f c X q θ ε K) :
    (D.kaCount f c θ ε K : ℝ) ≤ (fup - flow + 1) / ((1 - θ) * ε 0) :=
  h.toRun.kaCount_le hB hK1 hK

end IsHighOrderTargetRun

/-! ### Construction of runs from an inner oracle -/

section Construction

/-- The data of one inner call of Phase 2: iterates, length, successful iterations and returned
optimality radii. -/
structure InnerCall (E : Type*) where
  /-- The iterates of the call. -/
  xi : ℕ → E
  /-- The number of iterations of the call. -/
  e : ℕ
  /-- The successful iterations. -/
  succ : ℕ → Prop
  /-- The returned radii. -/
  δ : ℕ → ℝ

variable {f : E → ℝ} {c : E → F} {X : Set E} {q : ℕ} {θ β : ℝ} {ε : ℕ → ℝ}

open Classical in
/-- **Construction of Phase-2 runs from an inner oracle.** Let `θ ∈ (0, 1)`, `β ∈ (0, θ]`,
`ε_j ∈ (0, 1]` (`j ∈ [0 : q]`) and `x₁ ∈ X` with `‖c(x₁)‖ ≤ θε₀`. Suppose that from every
`(x, t)` with `x ∈ X`, `θε₀ ≤ ‖r(x, t)‖ ≤ ε₀` and `t ≤ f(x)` some call `o` (iterates from `x` not
increasing `μ(·, t)`, stopped as soon as `‖r(·, t)‖ < θε₀`, ending at a point of `X` with radii
in `(0, 1]` where one of the three tests of (14.3.32) holds) has the property `Good x t o`. Then
there is a run of Phase 2 from `x₁` whose `k`-th call, for every outer iteration `k ≥ 1` reached,
starts from an admissible point `(x_k, t_k)` and has the property `Good x_k t_k`. -/
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
