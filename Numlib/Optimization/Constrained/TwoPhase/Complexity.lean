/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Optimization.Constrained.TwoPhase.Run

/-!
# Evaluation complexity of the outer loop of two-phase target-following methods

This file bounds the number of outer iterations and the numbers of evaluations of Phase 2 of a
two-phase target-following method, for the problem of minimizing $f(x)$ subject to $x \in X$ and
$c(x) = 0$. The run is a `Constrained.IsTargetFollowingRun`: outer iterates $x_k$, targets $t_k$,
and for each outer iteration $k \ge 1$ an inner call with iterates
$x_{k,0} = x_k, \dots, x_{k,e_k} = x_{k+1}$ on the residual $\|r(\cdot, t_k)\|$, where
$r(x, t) = (c(x), f(x) - t)$. The inner calls satisfy a contract
(`Constrained.TargetFollowingSeq.IsInnerContract`): a bound on the length of a call by its number of
successful iterations, no move at unsuccessful iterations, and a residual decrease of at least
$\delta$ at every good iteration. The results are Lemmas 7.2.6 and 14.3.8 and Theorems 7.2.7 and
14.3.9 of [cartis2022evaluation] for Phase 2.

Fix an exemption test, a predicate on the outer iterations. An inner iteration $(k, i)$ is **good**
if it is successful, its new iterate has residual $\|r(x_{k,i+1}, t_k)\| \ge \theta\varepsilon_0$,
and it is not the last iteration of a call whose output passes the exemption test. An outer
iteration is **bad** if it is in case (b) and its call has no good iteration. Write $\mathcal{K}_a$
and $\mathcal{K}_b$ for the outer iterations in case (a) and in case (b), $\mathcal{S}_k$ and
$\mathcal{G}_k$ for the successful and the good iterations of the $k$-th call, $n_{\mathrm{bad}}(K)$
for the number of bad outer iterations in $[1, K)$, and $N_a = (f_{\mathrm{up}} - f_{\mathrm{low}} +
1)/((1 - \theta)\varepsilon_0)$. Here $f_{\mathrm{low}} \le f \le f_{\mathrm{up}}$ on the points of
$X$ with $\|c\| \le \varepsilon_0$ (assumption f.B.Fb of [cartis2022evaluation]). The main bound is
$K \le (N_a + 1)(G + 1) + n_{\mathrm{bad}}(K)$ for every outer iteration $K$ that is reached, where
$G \ge (1 - \theta)\varepsilon_0/\delta$.

## Main definitions

* `Constrained.TargetFollowingSeq.succCount`, `Constrained.TargetFollowingSeq.funEvals`,
  `Constrained.TargetFollowingSeq.derivEvals`, `Constrained.TargetFollowingSeq.kaCount`,
  `Constrained.TargetFollowingSeq.kbCount`: the counts of Phase 2.
* `Constrained.TargetFollowingSeq.IsGood`, `Constrained.TargetFollowingSeq.goodCount`,
  `Constrained.TargetFollowingSeq.IsBad`, `Constrained.TargetFollowingSeq.badCount`: the good inner
  iterations and the bad outer iterations for an exemption test.
* `Constrained.TargetFollowingSeq.IsInnerContract`: the contract of the inner method.
* `Constrained.kbMargin`: the margin $\eta = \theta(1 - \theta)\varepsilon_0/(1 + \theta)$.

## Main results

* `Constrained.TargetFollowingSeq.IsInnerContract.sum_goodCount_le`: the good inner iterations of
  the calls $1, \dots, K$ number at most $(1 - \theta)\varepsilon_0/\delta \cdot (|\mathcal{K}_a
  \cap [1, K)| + 1)$ ((7.2.39) and (14.3.71) of [cartis2022evaluation]).
* `Constrained.TargetFollowingSeq.le_counts`: $K \le |\mathcal{K}_a \cap [1, K)| + \sum_{k=1}^{K}
  |\mathcal{G}_k| + n_{\mathrm{bad}}(K) + 1$.
* `Constrained.TargetFollowingSeq.IsInnerContract.complexity`: Theorems 7.2.7 and 14.3.9 of
  [cartis2022evaluation] for Phase 2, with the number of bad outer iterations as a parameter.
* `Constrained.TargetFollowingSeq.IsInnerContract.complexity_of_badCount_le`: termination and the
  evaluation bounds, given a bound on the bad outer iterations.
* `Constrained.IsTargetFollowingRun.exempt_of_isBad`: if unsuccessful inner iterations do not move,
  the call of a bad outer iteration ends at a point that passes the exemption test.
* `Constrained.IsTargetFollowingRun.kbCount_le_of_drop`,
  `Constrained.IsTargetFollowingRun.card_kb_le_of_drop`: bounds on the case-(b) iterations that
  lower the target by a fixed amount.
* `Constrained.IsTargetFollowingRun.card_kb_le_of_margin`: the same bound when only the case-(b)
  iterations with a large margin lower the target; one iteration with a small margin is allowed
  between consecutive case-(a) iterations.

## Proof outline

The contract makes every good iteration lower $\|r(\cdot, t_k)\|$ by at least $\delta$. Between two
consecutive case-(a) iterations the residual above $\theta\varepsilon_0$ telescopes over the block
of outer iterations, so the good iterations number at most $(1 - \theta)\varepsilon_0/\delta \cdot
(|\mathcal{K}_a| + 1)$. Every successful inner iteration except the last one of its call is good.
Every case-(b) iteration whose call does not end at an exempt point contains a good iteration. Lemma
7.2.4 of [cartis2022evaluation] gives $|\mathcal{K}_a| \le N_a$. The bad outer iterations are not
bounded by this argument. A margin argument bounds them when the exemption test at the old target is
incompatible with the failure of the criticality test at the new target, unless the target drops by
a fixed amount (`Constrained.IsTargetFollowingRun.card_kb_le_of_margin`).
-/

open Finset

namespace Constrained

variable {E F : Type*} [NormedAddCommGroup F]

/-- The **margin** $\eta = \theta(1 - \theta)\varepsilon_0/(1 + \theta)$ of the bound on the
case-(b) iterations in `Constrained.IsTargetFollowingRun.card_kb_le_of_margin`.

It is the value of $\eta$ for which $\theta\varepsilon_0 - \theta(\theta\varepsilon_0 + \eta) =
\eta$. -/
noncomputable def kbMargin (θ ε₀ : ℝ) : ℝ := θ * (1 - θ) * ε₀ / (1 + θ)

/-- The margin is $\eta = \theta(1 - \theta)\varepsilon_0/(1 + \theta)$. -/
theorem kbMargin_def (θ ε₀ : ℝ) : kbMargin θ ε₀ = θ * (1 - θ) * ε₀ / (1 + θ) := rfl

/-- For $0 \le \theta \le 1$ and $\varepsilon_0 \ge 0$, the margin
$\theta(1 - \theta)\varepsilon_0/(1 + \theta)$ is nonnegative. -/
theorem kbMargin_nonneg {θ ε₀ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hε₀ : 0 ≤ ε₀) :
    0 ≤ kbMargin θ ε₀ := by
  unfold kbMargin
  have : 0 ≤ 1 - θ := by linarith
  positivity

namespace TargetFollowingSeq

variable (S : TargetFollowingSeq E)

section Counts

open Classical in
/-- The number $|\mathcal{S}_k|$ of **successful iterations** of the $k$-th inner call: the number
of $i \in [0, e_k)$ with `succ k i`. -/
noncomputable def succCount (succ : ℕ → ℕ → Prop) (k : ℕ) : ℕ :=
  ((range (S.e k)).filter (succ k)).card

/-- The number of **function evaluations** of Phase 2 up to outer iteration $k$:
$1 + \sum_{j=1}^{k} e_j$, one evaluation at $x_1$ and one per inner iteration. -/
noncomputable def funEvals (k : ℕ) : ℕ := 1 + ∑ j ∈ Icc 1 k, S.e j

/-- The number of **derivative evaluations** of Phase 2 up to outer iteration $k$:
$1 + \sum_{j=1}^{k} |\mathcal{S}_j|$, one evaluation at $x_1$ and one per successful inner
iteration. -/
noncomputable def derivEvals (succ : ℕ → ℕ → Prop) (k : ℕ) : ℕ :=
  1 + ∑ j ∈ Icc 1 k, S.succCount succ j

open Classical in
/-- The number $|\mathcal{K}_a \cap [1, K)|$ of **case-(a) iterations** among the outer iterations
$1, \dots, K - 1$. -/
noncomputable def kaCount (K : ℕ) : ℕ := ((Ico 1 K).filter S.Ka).card

open Classical in
/-- The number $|\mathcal{K}_b \cap [1, K)|$ of **case-(b) iterations** among the outer iterations
$1, \dots, K - 1$. -/
noncomputable def kbCount (K : ℕ) : ℕ := ((Ico 1 K).filter S.Kb).card

variable (f : E → ℝ) (c : E → F) (θ ε₀ : ℝ) (succ : ℕ → ℕ → Prop) (exempt : ℕ → Prop)

/-- A **good** inner iteration $(k, i)$ for the exemption test `exempt`: $i < e_k$, the iteration is
successful, either $i + 1 < e_k$ or the output of the $k$-th call fails the exemption test, and
the new iterate has residual $\|r(x_{k,i+1}, t_k)\| \ge \theta\varepsilon_0$.

These are the iterations that the proofs of Lemmas 7.2.6 and 14.3.8 of [cartis2022evaluation]
count. The predicate `exempt k` says that the output $x_{k+1}$ of the $k$-th call passes the
exemption test. -/
def IsGood (k i : ℕ) : Prop :=
  i < S.e k ∧ succ k i ∧ (i + 1 < S.e k ∨ ¬ exempt k) ∧
    θ * ε₀ ≤ targetResidual f c (S.t k) (S.xi k (i + 1))

open Classical in
/-- The number $|\mathcal{G}_k|$ of good iterations of the $k$-th inner call: the number of
$i \in [0, e_k)$ for which $(k, i)$ is good. -/
noncomputable def goodCount (k : ℕ) : ℕ :=
  ((range (S.e k)).filter (S.IsGood f c θ ε₀ succ exempt k)).card

/-- A **bad** outer iteration $k$: $k \in \mathcal{K}_b$ and the $k$-th call has no good iteration.
-/
def IsBad (k : ℕ) : Prop := S.Kb k ∧ S.goodCount f c θ ε₀ succ exempt k = 0

open Classical in
/-- The number $n_{\mathrm{bad}}(K)$ of bad outer iterations among $1, \dots, K - 1$. -/
noncomputable def badCount (K : ℕ) : ℕ :=
  ((Ico 1 K).filter (S.IsBad f c θ ε₀ succ exempt)).card

/-- **The contract of the inner method** of Phase 2, for the successful iterations `succ`, the
exemption test `exempt`, a residual decrease $\delta$ and constants $\kappa_{\mathrm{uns}}$,
$\kappa_{\mathrm{unc}}$. It holds if, for every outer iteration $k \ge 1$ that is reached:

* (count) $e_k \le \kappa_{\mathrm{uns}} |\mathcal{S}_k| + \kappa_{\mathrm{unc}}$, as in Lemma
  2.4.1 or (14.2.13) of [cartis2022evaluation];
* (stay) every unsuccessful inner iteration $i < e_k$ has $x_{k,i+1} = x_{k,i}$;
* (decrease) every good inner iteration $(k, i)$ has $\|r(x_{k,i}, t_k)\| - \|r(x_{k,i+1},
  t_k)\| \ge \delta$.

The decrease follows from the merit decreases of Lemmas 6.2.4 or 14.2.2 of
[cartis2022evaluation], through `Constrained.sub_ge_of_residual_decrease` or
`Constrained.sub_ge_of_merit_decrease`. An outer iteration $k$ is reached if no outer iteration
in $[1, k)$ terminates Phase 2 (`Constrained.TargetFollowingSeq.Before`). -/
structure IsInnerContract (δ κuns κunc : ℝ) : Prop where
  /-- The length of each call is at most $\kappa_{\mathrm{uns}} |\mathcal{S}_k| +
  \kappa_{\mathrm{unc}}$. -/
  count : ∀ k, 1 ≤ k → S.Before k → (S.e k : ℝ) ≤ κuns * S.succCount succ k + κunc
  /-- Unsuccessful inner iterations do not move the iterate. -/
  stay : ∀ k, 1 ≤ k → S.Before k → ∀ i < S.e k, ¬ succ k i → S.xi k (i + 1) = S.xi k i
  /-- Every good inner iteration lowers the residual $\|r(\cdot, t_k)\|$ by at least $\delta$. -/
  decrease : ∀ k, 1 ≤ k → S.Before k → ∀ i, S.IsGood f c θ ε₀ succ exempt k i →
    δ ≤ targetResidual f c (S.t k) (S.xi k i) - targetResidual f c (S.t k) (S.xi k (i + 1))

variable {S f c θ ε₀ succ exempt}

/-- An inner iteration $(k, i)$ is good if and only if $i < e_k$, it is successful, either
$i + 1 < e_k$ or the output of the $k$-th call fails the exemption test, and
$\|r(x_{k,i+1}, t_k)\| \ge \theta\varepsilon_0$. -/
theorem isGood_iff {k i : ℕ} :
    S.IsGood f c θ ε₀ succ exempt k i ↔ i < S.e k ∧ succ k i ∧ (i + 1 < S.e k ∨ ¬ exempt k) ∧
      θ * ε₀ ≤ targetResidual f c (S.t k) (S.xi k (i + 1)) :=
  Iff.rfl

/-- An outer iteration is bad if and only if it is in $\mathcal{K}_b$ and its call has no good
iteration. -/
theorem isBad_iff {k : ℕ} :
    S.IsBad f c θ ε₀ succ exempt k ↔ S.Kb k ∧ S.goodCount f c θ ε₀ succ exempt k = 0 :=
  Iff.rfl

/-- The number of good iterations of the $k$-th call is the cardinality of the set of good
$i \in [0, e_k)$, for every decidability instance of the predicate. -/
theorem goodCount_eq_card_filter (k : ℕ) [DecidablePred (S.IsGood f c θ ε₀ succ exempt k)] :
    S.goodCount f c θ ε₀ succ exempt k =
      ((range (S.e k)).filter (S.IsGood f c θ ε₀ succ exempt k)).card := by
  unfold goodCount; congr

/-- The $k$-th call has no good iteration if and only if no $i < e_k$ gives a good iteration
$(k, i)$. -/
theorem goodCount_eq_zero_iff {k : ℕ} :
    S.goodCount f c θ ε₀ succ exempt k = 0 ↔ ∀ i < S.e k, ¬ S.IsGood f c θ ε₀ succ exempt k i := by
  classical
  rw [goodCount_eq_card_filter, card_eq_zero, filter_eq_empty_iff]
  exact ⟨fun h i hi => h (mem_range.2 hi), fun h i hi => h i (mem_range.1 hi)⟩

/-- The number of bad outer iterations among $1, \dots, K - 1$ is the cardinality of the set of bad
$k \in [1, K)$, for every decidability instance of the predicate. -/
theorem badCount_eq_card_filter (K : ℕ) [DecidablePred (S.IsBad f c θ ε₀ succ exempt)] :
    S.badCount f c θ ε₀ succ exempt K = ((Ico 1 K).filter (S.IsBad f c θ ε₀ succ exempt)).card := by
  unfold badCount; congr

/-- The number of successful iterations of the $k$-th call is the cardinality of the set of
successful $i \in [0, e_k)$, for every decidability instance of the predicate. -/
theorem succCount_eq_card_filter (k : ℕ) [DecidablePred (succ k)] :
    S.succCount succ k = ((range (S.e k)).filter (succ k)).card := by
  unfold succCount; congr

/-- The number of case-(a) iterations among $1, \dots, K - 1$ is the cardinality of
$\mathcal{K}_a \cap [1, K)$, for every decidability instance of the predicate. -/
theorem kaCount_eq_card_filter (K : ℕ) [DecidablePred S.Ka] :
    S.kaCount K = ((Ico 1 K).filter S.Ka).card := by
  unfold kaCount; congr

/-- The number of case-(b) iterations among $1, \dots, K - 1$ is the cardinality of
$\mathcal{K}_b \cap [1, K)$, for every decidability instance of the predicate. -/
theorem kbCount_eq_card_filter (K : ℕ) [DecidablePred S.Kb] :
    S.kbCount K = ((Ico 1 K).filter S.Kb).card := by
  unfold kbCount; congr

/-- The number of derivative evaluations up to outer iteration $k$ is
$1 + \sum_{j=1}^{k} |\mathcal{S}_j|$, as a real number. -/
theorem derivEvals_eq (k : ℕ) :
    (S.derivEvals succ k : ℝ) = 1 + ∑ j ∈ Icc 1 k, (S.succCount succ j : ℝ) := by
  unfold derivEvals
  push_cast
  rfl

/-- A bad outer iteration is in case (b): $n_{\mathrm{bad}}(K) \le |\mathcal{K}_b \cap [1, K)|$. -/
theorem badCount_le_kbCount (K : ℕ) : S.badCount f c θ ε₀ succ exempt K ≤ S.kbCount K := by
  classical
  unfold badCount kbCount
  exact card_le_card fun k hk => by
    rw [mem_filter] at hk ⊢
    exact ⟨hk.1, hk.2.1⟩

/-- **Counting the outer iterations.** If the outer iteration $K$ is reached, then
$$K \le |\mathcal{K}_a \cap [1, K)| + \sum_{k=1}^{K} |\mathcal{G}_k| + n_{\mathrm{bad}}(K) +
  1.$$

Each outer iteration $k \in [1, K)$ does not terminate Phase 2, so it is in case (a), or it is
bad, or its call contains a good inner iteration. -/
theorem le_counts {K : ℕ} (hK : S.Before K) :
    K ≤ S.kaCount K + ∑ k ∈ Icc 1 K, S.goodCount f c θ ε₀ succ exempt k +
      S.badCount f c θ ε₀ succ exempt K + 1 := by
  classical
  have := le_card_add_sum_of_cover S.Ka (S.IsBad f c θ ε₀ succ exempt)
    (S.goodCount f c θ ε₀ succ exempt) (K := K) fun k hk => by
      have hk' := mem_Ico.1 hk
      rcases ka_or_kb_of_not_stop (hK.not_stop hk'.1 hk'.2) with ha | hb
      · exact Or.inl ha
      · by_cases hbad : S.IsBad f c θ ε₀ succ exempt k
        · exact Or.inr (Or.inl hbad)
        · exact Or.inr (Or.inr (Nat.one_le_iff_ne_zero.2 fun h0 => hbad ⟨hb, h0⟩))
  unfold kaCount badCount
  convert this

end Counts

end TargetFollowingSeq

namespace IsTargetFollowingRun

open TargetFollowingSeq

variable {f : E → ℝ} {c : E → F} {θ ε₀ : ℝ} {X : Set E} {x₁ : E} {S : TargetFollowingSeq E}
  {succ : ℕ → ℕ → Prop} {exempt : ℕ → Prop}

/-- Let $S$ be a run of Phase 2, and let $k \ge 1$ be an outer iteration that is reached. Then every
successful inner iteration of the $k$-th call except possibly the last one is good, for every
exemption test:
$$|\mathcal{S}_k| \le |\mathcal{G}_k| + 1.$$
-/
theorem succCount_le (h : IsTargetFollowingRun f c θ ε₀ X x₁ S) {k : ℕ} (hk1 : 1 ≤ k)
    (hk : S.Before k) :
    S.succCount succ k ≤ S.goodCount f c θ ε₀ succ exempt k + 1 := by
  classical
  unfold succCount goodCount
  refine (card_le_card (t := insert (S.e k - 1)
    ((range (S.e k)).filter (S.IsGood f c θ ε₀ succ exempt k))) ?_).trans (card_insert_le _ _)
  intro i hi
  rw [mem_filter, mem_range] at hi
  rw [mem_insert, mem_filter, mem_range]
  by_cases hi1 : i + 1 < S.e k
  · exact Or.inr ⟨hi.1, hi.1, hi.2, Or.inl hi1, h.inner_residual_ge k hk1 hk (i + 1) hi1⟩
  · left; omega

/-- For a run of Phase 2 and an outer iteration $K$ that is reached, $\sum_{k=1}^{K} |\mathcal{S}_k|
\le \sum_{k=1}^{K} |\mathcal{G}_k| + K$. -/
theorem sum_succCount_le (h : IsTargetFollowingRun f c θ ε₀ X x₁ S) {K : ℕ} (hK : S.Before K) :
    (∑ k ∈ Icc 1 K, (S.succCount succ k : ℝ)) ≤
      ∑ k ∈ Icc 1 K, (S.goodCount f c θ ε₀ succ exempt k : ℝ) + K := by
  have : ∑ k ∈ Icc 1 K, S.succCount succ k ≤
      ∑ k ∈ Icc 1 K, (S.goodCount f c θ ε₀ succ exempt k + 1) :=
    sum_le_sum fun k hk => h.succCount_le (mem_Icc.1 hk).1 (hK.mono (mem_Icc.1 hk).2)
  rw [sum_add_distrib, sum_const, Nat.card_Icc, smul_eq_mul, mul_one, Nat.add_sub_cancel] at this
  exact_mod_cast this

/-- **Lemma 7.2.4** of [cartis2022evaluation] for a run of Phase 2. Assume that
$f_{\mathrm{low}} \le f(z) \le f_{\mathrm{up}}$ for every $z \in X$ with
$\|c(z)\| \le \varepsilon_0$ (assumption f.B.Fb). Then every outer iteration $K \ge 1$ that is
reached satisfies
$$|\mathcal{K}_a \cap [1, K)| \le \frac{f_{\mathrm{up}} - f_{\mathrm{low}} + 1}{(1 -
  \theta)\varepsilon_0}.$$
-/
theorem kaCount_le (h : IsTargetFollowingRun f c θ ε₀ X x₁ S) {flow fup : ℝ}
    (hB : ∀ z ∈ X, ‖c z‖ ≤ ε₀ → flow ≤ f z ∧ f z ≤ fup) {K : ℕ} (hK1 : 1 ≤ K)
    (hK : S.Before K) : (S.kaCount K : ℝ) ≤ (fup - flow + 1) / ((1 - θ) * ε₀) := by
  classical
  have := (h.isTargetSequence hK).card_Ka_le h.θ_pos.le h.θ_lt_one h.ε₀_pos h.ε₀_le_one hK1
    (fun k hk1 hkK => h.x_mem k hk1 (hK.mono hkK)) hB
  unfold kaCount
  convert this

/-- Under assumption f.B.Fb, $f_{\mathrm{low}} \le f(x_1) \le f_{\mathrm{up}}$, so
$f_{\mathrm{up}} - f_{\mathrm{low}} + 1 > 0$. -/
theorem sub_add_one_pos (h : IsTargetFollowingRun f c θ ε₀ X x₁ S) {flow fup : ℝ}
    (hB : ∀ z ∈ X, ‖c z‖ ≤ ε₀ → flow ≤ f z ∧ f z ≤ fup) : 0 < fup - flow + 1 := by
  have := hB x₁ h.mem_one (h.norm_one_le.trans (mul_le_of_le_one_left h.ε₀_pos.le h.θ_lt_one.le))
  linarith [this.1, this.2]

/-- **Telescoping the targets of a run.** Under assumption f.B.Fb, let $K \ge 1$ be an outer
iteration that is reached, and let $S' \subseteq [1, K)$ be a set of outer iterations with
$t_k - t_{k+1} \ge \tau$ for every $k \in S'$. Then $|S'| \tau \le f_{\mathrm{up}} -
f_{\mathrm{low}} + 1$. -/
theorem card_mul_le_of_target_drop (h : IsTargetFollowingRun f c θ ε₀ X x₁ S) {flow fup : ℝ}
    (hB : ∀ z ∈ X, ‖c z‖ ≤ ε₀ → flow ≤ f z ∧ f z ≤ fup) {K : ℕ} (hK1 : 1 ≤ K)
    (hK : S.Before K) {S' : Finset ℕ} (hS : S' ⊆ Ico 1 K) {τ : ℝ}
    (hτ : ∀ k ∈ S', τ ≤ S.t k - S.t (k + 1)) : S'.card * τ ≤ fup - flow + 1 :=
  (h.isTargetSequence hK).card_mul_le_of_target_drop h.θ_pos.le h.θ_lt_one h.ε₀_pos h.ε₀_le_one
    hK1 (fun k hk1 hkK => h.x_mem k hk1 (hK.mono hkK)) hB hS hτ

open Classical in
/-- **The case-(b) iterations of a class $P$, from target drops.** Under assumption f.B.Fb, let
$\tau > 0$, and suppose that every outer iteration $k \ge 1$ in $\mathcal{K}_b$ with $P(k)$ that
does not terminate Phase 2 has $t_k - t_{k+1} \ge \tau$. Then every outer iteration $K \ge 1$
that is reached satisfies
$$|\{k \in [1, K) \mid k \in \mathcal{K}_b,\ P(k)\}| \le \frac{f_{\mathrm{up}} -
  f_{\mathrm{low}} + 1}{\tau}.$$
-/
theorem card_kb_le_of_drop (h : IsTargetFollowingRun f c θ ε₀ X x₁ S) {flow fup : ℝ}
    (hB : ∀ z ∈ X, ‖c z‖ ≤ ε₀ → flow ≤ f z ∧ f z ≤ fup) {P : ℕ → Prop} {τ : ℝ} (hτ0 : 0 < τ)
    (hdrop : ∀ k, 1 ≤ k → S.Before (k + 1) → S.Kb k → P k → τ ≤ S.t k - S.t (k + 1)) {K : ℕ}
    (hK1 : 1 ≤ K) (hK : S.Before K) :
    ((((Ico 1 K).filter (fun k => S.Kb k ∧ P k)).card : ℕ) : ℝ) ≤ (fup - flow + 1) / τ := by
  rw [le_div_iff₀ hτ0]
  refine h.card_mul_le_of_target_drop hB hK1 hK (filter_subset _ _) fun k hk => ?_
  rw [mem_filter, mem_Ico] at hk
  exact hdrop k hk.1.1 (hK.mono hk.1.2) hk.2.1 hk.2.2

/-- **The number of case-(b) iterations, from target drops.** Under assumption f.B.Fb, let
$\tau > 0$, and suppose that every outer iteration $k \ge 1$ in $\mathcal{K}_b$ that does not
terminate Phase 2 has $t_k - t_{k+1} \ge \tau$. Then every outer iteration $K \ge 1$ that is
reached satisfies
$$|\mathcal{K}_b \cap [1, K)| \le \frac{f_{\mathrm{up}} - f_{\mathrm{low}} + 1}{\tau}.$$
-/
theorem kbCount_le_of_drop (h : IsTargetFollowingRun f c θ ε₀ X x₁ S) {flow fup : ℝ}
    (hB : ∀ z ∈ X, ‖c z‖ ≤ ε₀ → flow ≤ f z ∧ f z ≤ fup) {τ : ℝ} (hτ0 : 0 < τ)
    (hdrop : ∀ k, 1 ≤ k → S.Before (k + 1) → S.Kb k → τ ≤ S.t k - S.t (k + 1)) {K : ℕ}
    (hK1 : 1 ≤ K) (hK : S.Before K) : (S.kbCount K : ℝ) ≤ (fup - flow + 1) / τ := by
  classical
  rw [le_div_iff₀ hτ0]
  refine h.card_mul_le_of_target_drop hB hK1 hK (filter_subset _ _) fun k hk => ?_
  rw [mem_filter, mem_Ico] at hk
  exact hdrop k hk.1.1 (hK.mono hk.1.2) hk.2

open Classical in
/-- **The case-(b) iterations of a class $P$, with a target drop at large margins.** Under
assumption f.B.Fb, let $0 \le \beta \le \theta$ and $\tau > 0$, and write $\eta = \theta(1 -
\theta)\varepsilon_0/(1 + \theta)$ (`Constrained.kbMargin`). Suppose that every outer iteration
$k \ge 1$ in $\mathcal{K}_b$ with $P(k)$ that does not terminate Phase 2 and whose margin
satisfies
$$\|r(x_{k+1}, t_k)\| - \beta \|r(x_k, t_k)\| \ge \eta$$
has $t_k - t_{k+1} \ge \tau$. Then every outer iteration $K \ge 1$ that is reached satisfies
$$|\{k \in [1, K) \mid k \in \mathcal{K}_b,\ P(k)\}| \le |\mathcal{K}_a \cap [1, K)| + 1 +
  \frac{f_{\mathrm{up}} - f_{\mathrm{low}} + 1}{\tau}.$$

This is the margin argument behind the bound on the case-(b) iterations of TPqp-GC. Between two
consecutive case-(a) iterations, at most one of these iterations has a margin smaller than
$\eta$. Indeed, let $k < k'$ both have margin smaller than $\eta$, with no case-(a) iteration
between them. Then $\|r(x_{k+1}, t_k)\| < \theta\varepsilon_0 + \eta$, the residual does not
increase from $k + 1$ to $k'$ (`Constrained.IsTargetFollowingRun.residual_le_of_forall_kb`), and
the margin at $k'$ is at least $\theta\varepsilon_0 - \theta(\theta\varepsilon_0 + \eta) =
\eta$. -/
theorem card_kb_le_of_margin (h : IsTargetFollowingRun f c θ ε₀ X x₁ S) {flow fup : ℝ}
    (hB : ∀ z ∈ X, ‖c z‖ ≤ ε₀ → flow ≤ f z ∧ f z ≤ fup) {P : ℕ → Prop} {β : ℝ} (hβ : 0 ≤ β)
    (hβθ : β ≤ θ) {τ : ℝ} (hτ0 : 0 < τ)
    (hdrop : ∀ k, 1 ≤ k → S.Before (k + 1) → S.Kb k → P k →
      kbMargin θ ε₀ ≤ targetResidual f c (S.t k) (S.x (k + 1)) -
        β * targetResidual f c (S.t k) (S.x k) →
      τ ≤ S.t k - S.t (k + 1))
    {K : ℕ} (hK1 : 1 ≤ K) (hK : S.Before K) :
    ((((Ico 1 K).filter (fun k => S.Kb k ∧ P k)).card : ℕ) : ℝ) ≤
      S.kaCount K + 1 + (fup - flow + 1) / τ := by
  have hε₀ := h.ε₀_pos
  have hθ0 := h.θ_pos
  have hθ1 := h.θ_lt_one
  set η := kbMargin θ ε₀ with hη
  have hηeq : η * (1 + θ) = θ * (1 - θ) * ε₀ := by
    rw [hη, kbMargin]; field_simp
  -- the margin of a case-(b) iteration
  set mg : ℕ → ℝ := fun k => targetResidual f c (S.t k) (S.x (k + 1)) -
    β * targetResidual f c (S.t k) (S.x k) with hmg
  set Kb := (Ico 1 K).filter (fun k => S.Kb k ∧ P k)
  set Sm := Kb.filter (fun k => mg k < η)
  set Bg := Kb.filter (fun k => ¬ mg k < η)
  have hsplit : Kb.card = Sm.card + Bg.card := (card_filter_add_card_filter_not _).symm
  -- the iterations with a large margin lower the target by at least `τ`
  have hBg : (Bg.card : ℝ) ≤ (fup - flow + 1) / τ := by
    rw [le_div_iff₀ hτ0]
    refine h.card_mul_le_of_target_drop hB hK1 hK
      ((filter_subset _ _).trans (filter_subset _ _)) fun k hk => ?_
    simp only [mem_filter, mem_Ico, not_lt] at hk
    obtain ⟨⟨⟨hk1, hkK⟩, hb, hP⟩, hm⟩ := hk
    exact hdrop k hk1 (hK.mono hkK) hb hP hm
  -- at most one iteration with a small margin between consecutive case-(a) iterations
  set g : ℕ → ℕ := fun k => Nat.findGreatest (fun j => 1 ≤ j ∧ S.Ka j) (k - 1)
  have hkey : ∀ k ∈ Sm, ∀ k' ∈ Sm, k < k' → g k ≠ g k' := by
    intro k hk k' hk' hlt hg
    simp only [Sm, Kb, mem_filter, mem_Ico] at hk hk'
    obtain ⟨⟨⟨hk1, hkK⟩, hb, -⟩, hm⟩ := hk
    obtain ⟨⟨⟨hk1', hkK'⟩, hb', -⟩, hm'⟩ := hk'
    have hnoKa : ∀ j, k ≤ j → j < k' → S.Kb j := by
      intro j hkj hjk'
      refine hK.kb_of_not_ka (hk1.trans hkj) (hjk'.trans hkK') fun hKa => ?_
      have h1 : j ≤ g k' := Nat.le_findGreatest (by omega) ⟨hk1.trans hkj, hKa⟩
      have h2 : g k ≤ k - 1 := Nat.findGreatest_le _
      omega
    have hkB : S.Before k := hK.mono hkK.le
    have hchain := h.residual_le_of_forall_kb (k := k + 1) (k' := k') (by omega) hlt
      (hK.mono hkK'.le) fun j hj hj' => hnoKa j (by omega) hj'
    rw [h.residual_succ_of_kb hk1 hkB hb] at hchain
    have hrk : targetResidual f c (S.t k) (S.x k) ≤ ε₀ := h.residual_le hk1 hkB
    have hr0 := targetResidual_nonneg (f := f) (c := c) (t := S.t k) (x := S.x k)
    simp only [hmg] at hm hm'
    have h1 : β * targetResidual f c (S.t k) (S.x k) ≤ θ * ε₀ := by
      calc β * targetResidual f c (S.t k) (S.x k) ≤
          θ * targetResidual f c (S.t k) (S.x k) := by gcongr
        _ ≤ θ * ε₀ := by gcongr
    have h2 : β * targetResidual f c (S.t k') (S.x k') ≤
        θ * targetResidual f c (S.t k) (S.x (k + 1)) := by
      calc β * targetResidual f c (S.t k') (S.x k') ≤
          θ * targetResidual f c (S.t k') (S.x k') := by
            gcongr; exact targetResidual_nonneg
        _ ≤ _ := by gcongr
    have h3 := h.le_residual_succ_of_kb hb'
    nlinarith
  have hSm : Sm.card ≤ S.kaCount K + 1 := by
    classical
    refine (card_le_card_of_injOn g (t := insert 0 ((Ico 1 K).filter S.Ka))
      (fun k hk => ?_) (fun k hk k' hk' hg => ?_)).trans (card_insert_le _ _)
    · have hk' : k ∈ Sm := hk
      simp only [Sm, Kb, mem_filter, mem_Ico] at hk'
      rw [coe_insert, coe_filter]
      by_cases h0 : g k = 0
      · exact Or.inl h0
      · right
        have hP := Nat.findGreatest_of_ne_zero rfl h0
        have hle : g k ≤ k - 1 := Nat.findGreatest_le _
        exact ⟨mem_Ico.2 ⟨hP.1, by omega⟩, hP.2⟩
    · rcases lt_trichotomy k k' with hlt | heq | hgt
      · exact absurd hg (hkey k hk k' hk' hlt)
      · exact heq
      · exact absurd hg.symm (hkey k' hk' k hk hgt)
  rw [hsplit]
  push_cast
  have : (Sm.card : ℝ) ≤ S.kaCount K + 1 := by exact_mod_cast hSm
  linarith

/-- Let the unsuccessful inner iterations of a run not move the iterate. If an outer iteration
$k \ge 1$ that is reached is in case (b), and its call does not end at a point that passes the
exemption test, then the call contains a good inner iteration: $|\mathcal{G}_k| \ge 1$.

The call has moved, since $f(x_{k+1}) < t_k \le f(x_k)$, and its last successful iteration is
good. -/
theorem one_le_goodCount (h : IsTargetFollowingRun f c θ ε₀ X x₁ S)
    (hstay : ∀ k, 1 ≤ k → S.Before k → ∀ i < S.e k, ¬ succ k i → S.xi k (i + 1) = S.xi k i)
    {k : ℕ} (hk1 : 1 ≤ k) (hk : S.Before k)
    (hb : S.Kb k) (hne : ¬ exempt k) : 1 ≤ S.goodCount f c θ ε₀ succ exempt k := by
  classical
  have hle := h.target_le hk1 hk
  have hmove : S.xi k (S.e k) ≠ S.xi k 0 := by
    rw [h.inner_end k hk1 hk, h.inner_zero k hk1 hk]
    intro heq
    have := h.lt_target_of_kb hb
    rw [heq] at this
    linarith
  obtain ⟨i, hi, hsucc, hxi⟩ := Optimization.exists_last_succ (succ := succ k) (S.e k)
    (hstay k hk1 hk) hmove
  rw [h.inner_end k hk1 hk] at hxi
  have hg : S.IsGood f c θ ε₀ succ exempt k i :=
    ⟨hi, hsucc, Or.inr hne, by rw [hxi]; exact h.le_residual_succ_of_kb hb⟩
  unfold goodCount
  exact card_pos.2 ⟨i, mem_filter.2 ⟨mem_range.2 hi, hg⟩⟩

/-- Let the unsuccessful inner iterations of a run not move the iterate. Then the call of a bad
outer iteration $k \ge 1$ that is reached ends at a point that passes the exemption test. -/
theorem exempt_of_isBad (h : IsTargetFollowingRun f c θ ε₀ X x₁ S)
    (hstay : ∀ k, 1 ≤ k → S.Before k → ∀ i < S.e k, ¬ succ k i → S.xi k (i + 1) = S.xi k i)
    {k : ℕ} (hk1 : 1 ≤ k) (hk : S.Before k)
    (hbad : S.IsBad f c θ ε₀ succ exempt k) : exempt k := by
  by_contra hne
  have := h.one_le_goodCount hstay hk1 hk hbad.1 hne
  rw [hbad.2] at this
  exact absurd this (by norm_num)

open Classical in
/-- Let the unsuccessful inner iterations of a run not move the iterate. Then a bad outer iteration
is a case-(b) iteration whose call ends at an exempt point: for every outer iteration $K$ that
is reached,
$$n_{\mathrm{bad}}(K) \le |\{k \in [1, K) \mid k \in \mathcal{K}_b,\ k \text{ is exempt}\}|.$$
-/
theorem badCount_le_card (h : IsTargetFollowingRun f c θ ε₀ X x₁ S)
    (hstay : ∀ k, 1 ≤ k → S.Before k → ∀ i < S.e k, ¬ succ k i → S.xi k (i + 1) = S.xi k i)
    {K : ℕ} (hK : S.Before K) :
    S.badCount f c θ ε₀ succ exempt K ≤ ((Ico 1 K).filter (fun k => S.Kb k ∧ exempt k)).card := by
  unfold badCount
  refine card_le_card fun k hk => ?_
  rw [mem_filter, mem_Ico] at hk ⊢
  exact ⟨hk.1, hk.2.1, h.exempt_of_isBad hstay hk.1.1 (hK.mono hk.1.2.le) hk.2⟩

end IsTargetFollowingRun

namespace TargetFollowingSeq.IsInnerContract

open TargetFollowingSeq

variable {f : E → ℝ} {c : E → F} {θ ε₀ : ℝ} {X : Set E} {x₁ : E} {S : TargetFollowingSeq E}
  {succ : ℕ → ℕ → Prop} {exempt : ℕ → Prop} {δ κuns κunc : ℝ}

/-- Under the contract, the good iterations of one call telescope: for every outer iteration
$k \ge 1$ that is reached,
$$|\mathcal{G}_k| \, \delta \le \max(\|r(x_k, t_k)\|, \theta\varepsilon_0) - \max(\|r(x_{k+1},
  t_k)\|, \theta\varepsilon_0).$$
-/
theorem goodCount_mul_le (hc : S.IsInnerContract f c θ ε₀ succ exempt δ κuns κunc)
    (h : IsTargetFollowingRun f c θ ε₀ X x₁ S) {k : ℕ} (hk1 : 1 ≤ k) (hk : S.Before k) :
    (S.goodCount f c θ ε₀ succ exempt k : ℝ) * δ ≤
      max (targetResidual f c (S.t k) (S.x k)) (θ * ε₀) -
        max (targetResidual f c (S.t k) (S.x (k + 1))) (θ * ε₀) := by
  classical
  have := Optimization.card_mul_le_sub_of_decrease
    («φ» := fun j => max (targetResidual f c (S.t k) (S.xi k j)) (θ * ε₀))
    (N := S.e k) (T := (range (S.e k)).filter (S.IsGood f c θ ε₀ succ exempt k)) (c := δ)
    (filter_subset _ _)
    (fun j hj => max_le_max (h.inner_residual_antitone hk1 hk j.le_succ hj) le_rfl)
    (fun j hj => by
      have hg := (mem_filter.1 hj).2
      have h1 := hg.2.2.2
      have h2 := h.inner_residual_antitone hk1 hk j.le_succ hg.1
      rw [max_eq_left h1, max_eq_left (h1.trans h2)]
      exact hc.decrease k hk1 hk j hg)
  rw [h.inner_zero k hk1 hk, h.inner_end k hk1 hk] at this
  unfold goodCount
  exact this

/-- **The good inner iterations of Phase 2.** Let the inner calls of a run of Phase 2 satisfy the
contract with residual decrease $\delta > 0$. Then every outer iteration $K \ge 1$ that is
reached satisfies
$$\sum_{k=1}^{K} |\mathcal{G}_k| \le \frac{(1 - \theta)\varepsilon_0}{\delta}
  \bigl(|\mathcal{K}_a \cap [1, K)| + 1\bigr).$$

This is (7.2.39) and (14.3.71) of [cartis2022evaluation], summed over the blocks of outer
iterations between consecutive case-(a) iterations. -/
theorem sum_goodCount_le (hc : S.IsInnerContract f c θ ε₀ succ exempt δ κuns κunc)
    (h : IsTargetFollowingRun f c θ ε₀ X x₁ S) (hδ : 0 < δ) {K : ℕ} (hK1 : 1 ≤ K)
    (hK : S.Before K) :
    (∑ k ∈ Icc 1 K, (S.goodCount f c θ ε₀ succ exempt k : ℝ)) ≤
      (1 - θ) * ε₀ / δ * (S.kaCount K + 1) := by
  classical
  have hsum := (h.isTargetSequence hK).sum_max_sub_le h.θ_pos.le h.θ_lt_one.le h.ε₀_pos.le hK1
  have h1 : ∑ k ∈ Icc 1 K, (S.goodCount f c θ ε₀ succ exempt k : ℝ) * δ ≤
      ∑ k ∈ Icc 1 K,
        (max (targetResidual f c (S.t k) (S.x k)) (θ * ε₀) -
          max (targetResidual f c (S.t k) (S.x (k + 1))) (θ * ε₀)) :=
    sum_le_sum fun k hk => hc.goodCount_mul_le h (mem_Icc.1 hk).1 (hK.mono (mem_Icc.1 hk).2)
  rw [← sum_mul] at h1
  have hka : (S.kaCount K : ℝ) = ((Ico 1 K).filter S.Ka).card := by unfold kaCount; congr
  rw [div_mul_eq_mul_div, le_div_iff₀ hδ, hka]
  linarith

/-- Under the contract, the number of function evaluations up to an outer iteration $K$ that is
reached satisfies
$$\mathrm{funEvals}(K) \le 1 + \kappa_{\mathrm{uns}} \sum_{k=1}^{K} |\mathcal{S}_k| +
  \kappa_{\mathrm{unc}} K.$$
-/
theorem funEvals_le (hc : S.IsInnerContract f c θ ε₀ succ exempt δ κuns κunc) {K : ℕ}
    (hK : S.Before K) :
    (S.funEvals K : ℝ) ≤ 1 + κuns * ∑ k ∈ Icc 1 K, (S.succCount succ k : ℝ) + κunc * K := by
  have hF : (S.funEvals K : ℝ) ≤ 1 + ∑ k ∈ Icc 1 K, (κuns * S.succCount succ k + κunc) := by
    unfold funEvals
    push_cast
    gcongr with k hk
    exact hc.count k (mem_Icc.1 hk).1 (hK.mono (mem_Icc.1 hk).2)
  rw [sum_add_distrib, ← mul_sum, sum_const, Nat.card_Icc, Nat.add_sub_cancel,
    nsmul_eq_mul] at hF
  linarith

/-- **Evaluation complexity of Phase 2.** Let the inner calls of a run of Phase 2 satisfy the
contract with residual decrease $\delta > 0$ and $\kappa_{\mathrm{uns}} \ge 0$. Assume that
$f_{\mathrm{low}} \le f(z) \le f_{\mathrm{up}}$ for every $z \in X$ with
$\|c(z)\| \le \varepsilon_0$ (assumption f.B.Fb). Let $G \ge (1 - \theta)\varepsilon_0/\delta$,
and write $N_a = (f_{\mathrm{up}} - f_{\mathrm{low}} + 1)/((1 - \theta)\varepsilon_0)$. Then:

* (i) every outer iteration $K \ge 1$ that is reached satisfies
  $K \le (N_a + 1)(G + 1) + n_{\mathrm{bad}}(K)$;
* (ii) if $n_{\mathrm{bad}}(K) \le B$ for every outer iteration $K$ that is reached, then Phase
  2 terminates at some outer iteration $k_\varepsilon \le (N_a + 1)(G + 1) + B$;
* (iii) if Phase 2 terminates at $k_\varepsilon$, it uses at most
  $1 + G(N_a + 1) + k_\varepsilon$ derivative evaluations and at most $1 +
  \kappa_{\mathrm{uns}}(G(N_a + 1) + k_\varepsilon) + \kappa_{\mathrm{unc}} k_\varepsilon$
  function evaluations.

This is Theorems 7.2.7 and 14.3.9 of [cartis2022evaluation] for Phase 2, with the number of bad
outer iterations as a parameter. -/
theorem complexity (hc : S.IsInnerContract f c θ ε₀ succ exempt δ κuns κunc)
    (h : IsTargetFollowingRun f c θ ε₀ X x₁ S) (hδ : 0 < δ) {G : ℝ}
    (hG : (1 - θ) * ε₀ / δ ≤ G) (hκuns : 0 ≤ κuns) {flow fup : ℝ}
    (hB : ∀ z ∈ X, ‖c z‖ ≤ ε₀ → flow ≤ f z ∧ f z ≤ fup) :
    (∀ K, 1 ≤ K → S.Before K →
      (K : ℝ) ≤ ((fup - flow + 1) / ((1 - θ) * ε₀) + 1) * (G + 1) +
        S.badCount f c θ ε₀ succ exempt K) ∧
    (∀ Bb : ℝ, (∀ K, S.Before K → (S.badCount f c θ ε₀ succ exempt K : ℝ) ≤ Bb) →
      ∃ kε, S.IsEnd kε ∧
        (kε : ℝ) ≤ ((fup - flow + 1) / ((1 - θ) * ε₀) + 1) * (G + 1) + Bb) ∧
    (∀ kε, S.IsEnd kε →
      (S.derivEvals succ kε : ℝ) ≤ 1 + G * ((fup - flow + 1) / ((1 - θ) * ε₀) + 1) + kε ∧
      (S.funEvals kε : ℝ) ≤
        1 + κuns * (G * ((fup - flow + 1) / ((1 - θ) * ε₀) + 1) + kε) + κunc * kε) := by
  classical
  set Na := (fup - flow + 1) / ((1 - θ) * ε₀)
  have hG0 : 0 ≤ G := le_trans (div_nonneg (mul_nonneg (sub_nonneg.2 h.θ_lt_one.le)
    h.ε₀_pos.le) hδ.le) hG
  have hgood : ∀ K, 1 ≤ K → S.Before K →
      (∑ k ∈ Icc 1 K, (S.goodCount f c θ ε₀ succ exempt k : ℝ)) ≤ G * (Na + 1) := by
    intro K hK1 hK
    have h1 := hc.sum_goodCount_le h hδ hK1 hK
    have h2 := h.kaCount_le hB hK1 hK
    exact h1.trans (mul_le_mul hG (by linarith) (by positivity) hG0)
  have hi : ∀ K, 1 ≤ K → S.Before K →
      (K : ℝ) ≤ (Na + 1) * (G + 1) + S.badCount f c θ ε₀ succ exempt K := by
    intro K hK1 hK
    have h1 : (K : ℝ) ≤ S.kaCount K + (∑ k ∈ Icc 1 K, (S.goodCount f c θ ε₀ succ exempt k : ℝ)) +
        S.badCount f c θ ε₀ succ exempt K + 1 := by exact_mod_cast le_counts hK
    have h2 := h.kaCount_le hB hK1 hK
    have h3 := hgood K hK1 hK
    nlinarith
  refine ⟨hi, fun Bb hBb => exists_isEnd_of_forall_le fun K hK1 hK =>
    (hi K hK1 hK).trans (by linarith [hBb K hK]), fun kε hend => ?_⟩
  obtain ⟨hk1, -, hbef⟩ := hend
  have hgood' := hgood kε hk1 hbef
  have hsucc := h.sum_succCount_le (succ := succ) (exempt := exempt) hbef
  refine ⟨by rw [derivEvals_eq]; linarith, (hc.funEvals_le hbef).trans ?_⟩
  have : κuns * ∑ k ∈ Icc 1 kε, (S.succCount succ k : ℝ) ≤ κuns * (G * (Na + 1) + kε) :=
    mul_le_mul_of_nonneg_left (hsucc.trans (by linarith)) hκuns
  linarith

/-- **Evaluation complexity of Phase 2, given a bound on the bad iterations.** Under the assumptions
of `Constrained.TargetFollowingSeq.IsInnerContract.complexity`, suppose that
$n_{\mathrm{bad}}(K) \le N_b$ for every outer iteration $K \ge 1$ that is reached. Then every
such $K$ satisfies $K \le (N_a + 1)(G + 1) + N_b$. Moreover Phase 2 terminates at some outer
iteration $k_\varepsilon \le (N_a + 1)(G + 1) + N_b$, and it uses at most
$1 + G(N_a + 1) + k_\varepsilon$ derivative evaluations and at most $1 +
\kappa_{\mathrm{uns}}(G(N_a + 1) + k_\varepsilon) + \kappa_{\mathrm{unc}} k_\varepsilon$
function evaluations. -/
theorem complexity_of_badCount_le (hc : S.IsInnerContract f c θ ε₀ succ exempt δ κuns κunc)
    (h : IsTargetFollowingRun f c θ ε₀ X x₁ S) (hδ : 0 < δ) {G : ℝ}
    (hG : (1 - θ) * ε₀ / δ ≤ G) (hκuns : 0 ≤ κuns) {flow fup : ℝ}
    (hB : ∀ z ∈ X, ‖c z‖ ≤ ε₀ → flow ≤ f z ∧ f z ≤ fup) {Nb : ℝ}
    (hNb : ∀ K, 1 ≤ K → S.Before K → (S.badCount f c θ ε₀ succ exempt K : ℝ) ≤ Nb) :
    (∀ K, 1 ≤ K → S.Before K →
      (K : ℝ) ≤ ((fup - flow + 1) / ((1 - θ) * ε₀) + 1) * (G + 1) + Nb) ∧
    ∃ kε, S.IsEnd kε ∧
      (kε : ℝ) ≤ ((fup - flow + 1) / ((1 - θ) * ε₀) + 1) * (G + 1) + Nb ∧
      (S.derivEvals succ kε : ℝ) ≤ 1 + G * ((fup - flow + 1) / ((1 - θ) * ε₀) + 1) + kε ∧
      (S.funEvals kε : ℝ) ≤
        1 + κuns * (G * ((fup - flow + 1) / ((1 - θ) * ε₀) + 1) + kε) + κunc * kε := by
  obtain ⟨hi, -, hiii⟩ := hc.complexity h hδ hG hκuns hB
  have hK : ∀ K, 1 ≤ K → S.Before K →
      (K : ℝ) ≤ ((fup - flow + 1) / ((1 - θ) * ε₀) + 1) * (G + 1) + Nb := fun K hK1 hKb =>
    (hi K hK1 hKb).trans (by linarith [hNb K hK1 hKb])
  obtain ⟨kε, hend, hkε⟩ := exists_isEnd_of_forall_le hK
  exact ⟨hK, kε, hend, hkε, hiii kε hend⟩

end TargetFollowingSeq.IsInnerContract

end Constrained
