/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Optimization.Constrained.TwoPhase.HighOrder.Basic
import Numlib.Optimization.ModelBased.HighOrder.Orders
import Numlib.Optimization.ModelBased.InexactTaylor

/-!
# Evaluation complexity of high-order target-following runs

This file bounds the number of outer iterations and the numbers of evaluations of Phase 2 of TPqp-GC
(Algorithm 14.3.2 of [cartis2022evaluation]), for a run (`Constrained.IsHighOrderTargetRun`) whose
inner calls satisfy a merit-decrease contract. The contract has the form of Lemmas 14.2.2 and 14.2.3
of [cartis2022evaluation] for the merit function $\mu(\cdot, t_k) = \frac12 \|r(\cdot, t_k)\|^2$. At
every outer iteration $k \ge 1$ that is reached, it asks: $e_k \le \kappa_{\mathrm{uns}}
|\mathcal{S}_k| + \kappa_{\mathrm{unc}}$, unsuccessful inner iterations do not move, and every
successful inner iteration whose new iterate has residual at least $\theta\varepsilon_0$, and which
is not the last iteration of a call ending at an exempt point, lowers the merit by at least
$\kappa_{\mathrm{decr}} \min_l (\beta \|r(x_k, t_k)\| \varepsilon_l)^{\pi_l}$. This is (14.2.11) for
the inner method called with the tolerances $\beta \|r(x_k, t_k)\| \varepsilon_l$. The results
follow Lemma 14.3.8 and Theorem 14.3.9 of [cartis2022evaluation] for Phase 2.

Two exemption tests occur: the criticality test (14.3.34) at the old target, and the termination
test (14.3.19) of the inner method. With the second test, a lower bound $\rho$ on the radii returned
by the case-(b) calls that pass it gives a bound on these calls. Then Phase 2 terminates within an
explicit bound, and the number of bad outer iterations is no longer a parameter. Write $N_a =
(f_{\mathrm{up}} - f_{\mathrm{low}} + 1)/((1 - \theta)\varepsilon_0)$, $G$ for the bound
`Constrained.goodBound` on the counted inner iterations of a block, and $\eta = \theta(1 -
\theta)\varepsilon_0/(1 + \theta)$ for the margin `Constrained.kbMargin`. Here
$f_{\mathrm{low}} \le f \le f_{\mathrm{up}}$ on the points of $X$ with $\|c\| \le \varepsilon_0$
(assumption f.B.Fb).

## Main definitions

* `Constrained.goodBound`, `Constrained.goodDecr`: the bound $\kappa^S (1 - \theta) M$ of (14.3.71)
  and the residual decrease of a counted inner iteration.
* `Constrained.HighOrderTargetSeq.IsMeritContract`: the merit-decrease contract for an exemption
  test. `Constrained.HighOrderTargetSeq.IsEndCritContract` and
  `Constrained.HighOrderTargetSeq.IsInnerTestContract` are its two instances.
* `Constrained.HighOrderTargetSeq.IsCertified`: every case-(b) call passes (14.3.19), with radii
  bounded below.

## Main results

* `Constrained.HighOrderTargetSeq.IsMeritContract.toContract`: the merit contract is a contract of
  the generic outer loop.
* `Constrained.IsHighOrderTargetRun.complexity`: Theorem 14.3.9 for Phase 2, with the number of bad
  outer iterations as a parameter.
* `Constrained.IsHighOrderTargetRun.target_drop_of_innerTest`,
  `Constrained.IsHighOrderTargetRun.card_kb_innerTest_le`: the case-(b) calls that pass (14.3.19)
  lower the target, and their number.
* `Constrained.IsHighOrderTargetRun.complexity_of_certified`,
  `Constrained.IsHighOrderTargetRun.complexity_of_certified_margin`: Phase 2 when every case-(b)
  call passes (14.3.19), for $\beta < \theta$ and for $\beta \le \theta$.
* `Constrained.IsHighOrderTargetRun.complexity_of_innerTest`: Phase 2 under the contract keyed on
  (14.3.19), for $\beta \le \theta$, without a bad-iteration parameter.
* `Constrained.HighOrderTargetSeq.IsEndCritContract.toInnerTestContract`,
  `Constrained.HighOrderTargetSeq.IsInnerTestContract.toEndCritContract`: the relation between the
  two contracts.
* `Constrained.IsHighOrderTargetRun.exists_const_order_of_innerTest` and its variants: with
  constants fixed before the tolerances, Phase 2 takes $O(\Omega)$ evaluations for every $\Omega$
  that dominates $\varepsilon_0^{-1}$, the terms $\varepsilon_0^{1 - \pi_j} \varepsilon_j^{-\pi_j}$
  and the bad-iteration terms $(\varepsilon_0 \varepsilon_j \rho'^{\,j-1}_j)^{-1}$.

## Proof outline

A merit decrease of the contract gives a residual decrease of at least `Constrained.goodDecr`
(`Constrained.sub_ge_of_merit_decrease`). So the merit contract is a residual-decrease contract of
the generic outer loop, and the counting of `Numlib.Optimization.Constrained.TwoPhase.Complexity`
applies. For the termination test (14.3.19), take a case-(b) call that ends at a point passing
(14.3.19) for the old target, while (14.3.34) fails at the new target. This call lowers the target
by an amount bounded below in terms of the margin $\|r(x_{k+1}, t_k)\| - \beta \|r(x_k, t_k)\|$. The
reason is that $\mu(\cdot, t_{k+1}) - \mu(\cdot, t_k)$ is $(t_k - t_{k+1}) f$ up to a constant. The
margin argument of the generic loop then bounds these calls.

## Implementation notes

* All counting is done on the residual-decrease contract
  `Constrained.TargetFollowingSeq.IsInnerContract` of the generic outer loop, through
  `Constrained.HighOrderTargetSeq.IsMeritContract.toContract`. The merit contract has the exemption
  test as a parameter, so the two exemptions share one structure:
  `Constrained.HighOrderTargetSeq.IsEndCritContract` is a reducible abbreviation of it, and
  `Constrained.HighOrderTargetSeq.IsInnerTestContract` extends it with the radius bound.
* The smoothness of $f$ and $c$ is assumed only at the points of $X$ (`ContDiffAt` there).
  Assumption f.B.Fb is $f_{\mathrm{low}} \le f \le f_{\mathrm{up}}$ on the points of $X$ with
  $\|c\| \le \varepsilon_0$.
* The results on target drops, and the order bounds that use them, assume that $c$ takes values in a
  real inner product space $F$.
* In the order bounds, the number $\Omega$ is the Lean variable `O`.
-/

open Finset
open scoped Nat

namespace Constrained

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]

/-! ### Constants -/

/-- The **bound** $G = \kappa^S (1 - \theta) M$ on the counted inner iterations of a block, with
$\kappa^S = \kappa_{\mathrm{decr}}^{-1} (\beta\theta)^{-\pi_{\max}}$:
$$G = \kappa_{\mathrm{decr}}^{-1} (\beta\theta)^{-\pi_{\max}} (1 - \theta) M.$$

This is the bound of (14.3.71) of [cartis2022evaluation]. In the applications, $M \ge \max_l
\varepsilon_0^{2 - \pi_l} \varepsilon_l^{-\pi_l}$. The power is the real power `Real.rpow`. -/
noncomputable def goodBound (κdecr β θ πmax M : ℝ) : ℝ :=
  κdecr⁻¹ * (β * θ) ^ (-πmax) * (1 - θ) * M

/-- The **residual decrease** $\kappa_{\mathrm{decr}} (\beta\theta)^{\pi_{\max}} \varepsilon_0 / M$
of a counted inner iteration under the merit contract.

When all constants are positive, `Constrained.goodBound` is $(1 - \theta)\varepsilon_0$ divided
by this decrease (`Constrained.goodBound_eq`). -/
noncomputable def goodDecr (κdecr β θ πmax M ε₀ : ℝ) : ℝ := κdecr * (β * θ) ^ πmax * ε₀ / M

section Constants

variable {κdecr β θ πmax M ε₀ : ℝ}

/-- If $\kappa_{\mathrm{decr}}$, $\beta$, $\theta$, $M$ and $\varepsilon_0$ are positive, then the
residual decrease $\kappa_{\mathrm{decr}} (\beta\theta)^{\pi_{\max}} \varepsilon_0 / M$ is
positive. -/
theorem goodDecr_pos (hκ : 0 < κdecr) (hβ : 0 < β) (hθ : 0 < θ) (hM : 0 < M) (hε₀ : 0 < ε₀) :
    0 < goodDecr κdecr β θ πmax M ε₀ := by
  unfold goodDecr; positivity

/-- If $\kappa_{\mathrm{decr}}$, $\beta$, $\theta$, $M$ and $\varepsilon_0$ are positive, then the
bound $G$ of (14.3.71) equals $(1 - \theta)\varepsilon_0$ divided by the residual decrease
$\kappa_{\mathrm{decr}} (\beta\theta)^{\pi_{\max}} \varepsilon_0 / M$. -/
theorem goodBound_eq (hκ : 0 < κdecr) (hβ : 0 < β) (hθ : 0 < θ) (hM : 0 < M) (hε₀ : 0 < ε₀) :
    goodBound κdecr β θ πmax M = (1 - θ) * ε₀ / goodDecr κdecr β θ πmax M ε₀ := by
  unfold goodBound goodDecr
  rw [Real.rpow_neg (by positivity)]
  have : 0 < (β * θ) ^ πmax := by positivity
  field_simp

end Constants

/-! ### Contracts of the inner method -/

namespace HighOrderTargetSeq

/-- **The merit-decrease contract of the inner method** for the exemption test `exempt`, with
constants $\kappa_{\mathrm{decr}}$, $\kappa_{\mathrm{uns}}$, $\kappa_{\mathrm{unc}}$ and
exponents $\pi$. It holds if, for every outer iteration $k \ge 1$ that is reached:

* (count) $e_k \le \kappa_{\mathrm{uns}} |\mathcal{S}_k| + \kappa_{\mathrm{unc}}$, where
  $\mathcal{S}_k$ is the set of successful inner iterations, as in Lemma 2.4.1 or (14.2.13) of
  [cartis2022evaluation];
* (stay) every unsuccessful inner iteration $i < e_k$ has $x_{k,i+1} = x_{k,i}$;
* (decrease) every successful inner iteration $i < e_k$ such that $i + 1 < e_k$ or the output of
  the call fails the exemption test, and such that
  $\|r(x_{k,i+1}, t_k)\| \ge \theta\varepsilon_0$, satisfies for some $l \in \{1, \dots, q\}$
$$\mu(x_{k,i}, t_k) - \mu(x_{k,i+1}, t_k) \ge \kappa_{\mathrm{decr}} (\beta \|r(x_k, t_k)\|
  \varepsilon_l)^{\pi_l}.$$

This is the form of Lemmas 14.2.2 and 14.2.3 of [cartis2022evaluation] for $\mu(\cdot, t_k)$,
with constants independent of $t_k$. The decrease is (14.2.11) for the inner method called with
the tolerances $\beta \|r(x_k, t_k)\| \varepsilon_l$. -/
structure IsMeritContract (f : E → ℝ) (c : E → F) (X : Set E) (q : ℕ) (θ β : ℝ) (ε : ℕ → ℝ)
    (D : HighOrderTargetSeq E) (exempt : ℕ → Prop) (κdecr κuns κunc : ℝ) (π : ℕ → ℝ) :
    Prop where
  /-- The length of each call is at most
  $\kappa_{\mathrm{uns}} |\mathcal{S}_k| + \kappa_{\mathrm{unc}}$. -/
  count : ∀ k, 1 ≤ k → D.Before f c X q θ ε k → (D.e k : ℝ) ≤ κuns * D.succCount k + κunc
  /-- Unsuccessful inner iterations do not move the iterate. -/
  stay : ∀ k, 1 ≤ k → D.Before f c X q θ ε k → ∀ i < D.e k, ¬ D.succ k i →
    D.xi k (i + 1) = D.xi k i
  /-- Every counted successful inner iteration lowers $\mu(\cdot, t_k)$ by at least
  $\kappa_{\mathrm{decr}} (\beta \|r(x_k, t_k)\| \varepsilon_l)^{\pi_l}$ for some $l \le q$. -/
  decrease : ∀ k, 1 ≤ k → D.Before f c X q θ ε k → ∀ i < D.e k, D.succ k i →
    (i + 1 < D.e k ∨ ¬ exempt k) →
    θ * ε 0 ≤ targetResidual f c (D.t k) (D.xi k (i + 1)) →
    ∃ l ∈ Finset.Icc 1 q,
      κdecr * (β * targetResidual f c (D.t k) (D.x k) * ε l) ^ π l ≤
        targetMerit f c (D.t k) (D.xi k i) - targetMerit f c (D.t k) (D.xi k (i + 1))

/-- **The merit contract that exempts the criticality test at the old target.** The exemption test
of `Constrained.HighOrderTargetSeq.IsMeritContract` is (14.3.34) at $(x_{k+1}, t_k)$ with the
radii $\delta_{k+1}$.

These are the decreases used by the proof of Lemma 14.3.8 of [cartis2022evaluation], "so long as
the third termination test in (14.3.32) has not been satisfied", (B.14.21). -/
abbrev IsEndCritContract (f : E → ℝ) (c : E → F) (X : Set E) (q : ℕ) (θ β : ℝ) (ε : ℕ → ℝ)
    (D : HighOrderTargetSeq E) (κdecr κuns κunc : ℝ) (π : ℕ → ℝ) : Prop :=
  D.IsMeritContract f c X q θ β ε (D.EndCrit f c X q ε) κdecr κuns κunc π

/-- **The merit contract that exempts the termination test of the inner method**, with radii bounded
below by $\rho$. It holds if:

* the merit contract `Constrained.HighOrderTargetSeq.IsMeritContract` holds with the exemption
  test (14.3.19) at the end of the call (`Constrained.HighOrderTargetSeq.InnerTest`);
* every case-(b) call that ends at a point passing (14.3.19) returns radii
  $\delta_{k+1,j} \ge \rho_j$ for $j = 1, \dots, q$.

This is Lemma 14.2.2 of [cartis2022evaluation] for the inner method on $\mu(\cdot, t_k)$, which
needs only that the method does not terminate at $x_{k,i+1}$. The calls may be cut by any test
of (14.3.32). -/
structure IsInnerTestContract (f : E → ℝ) (c : E → F) (X : Set E) (q : ℕ) (θ β : ℝ)
    (ε : ℕ → ℝ) (D : HighOrderTargetSeq E) (κdecr κuns κunc : ℝ) (π ρ : ℕ → ℝ) : Prop
    extends D.IsMeritContract f c X q θ β ε (D.InnerTest f c X q β ε) κdecr κuns κunc π where
  /-- A case-(b) call that ends at a point passing (14.3.19) returns radii at least $\rho$. -/
  radius_ge : ∀ k, 1 ≤ k → D.Before f c X q θ ε k → D.IsKb f c θ ε k →
    D.InnerTest f c X q β ε k → ∀ j ∈ Finset.Icc 1 q, ρ j ≤ D.δ (k + 1) j

/-- **Every case-(b) call passes the termination test of the inner method**, with radii bounded
below by $\rho$: at every outer iteration $k \ge 1$ in $\mathcal{K}_b$ that is reached,
$\delta_{k+1,j} \ge \rho_j$ for $j = 1, \dots, q$, and the test (14.3.19) holds at $x_{k+1}$.

This holds when the inner method is interrupted only by the first test of (14.3.32). A call that
ends in $\mathcal{K}_b$ has $\|r(x_{k+1}, t_k)\| \ge \theta\varepsilon_0$, so the method has
terminated. -/
structure IsCertified (f : E → ℝ) (c : E → F) (X : Set E) (q : ℕ) (θ β : ℝ) (ε : ℕ → ℝ)
    (D : HighOrderTargetSeq E) (ρ : ℕ → ℝ) : Prop where
  /-- Every case-(b) call returns radii at least $\rho$. -/
  radius_ge : ∀ k, 1 ≤ k → D.Before f c X q θ ε k → D.IsKb f c θ ε k →
    ∀ j ∈ Finset.Icc 1 q, ρ j ≤ D.δ (k + 1) j
  /-- Every case-(b) call ends at a point that passes (14.3.19). -/
  cert : ∀ k, 1 ≤ k → D.Before f c X q θ ε k → D.IsKb f c θ ε k → D.InnerTest f c X q β ε k

variable {f : E → ℝ} {c : E → F} {X : Set E} {q : ℕ} {θ β : ℝ} {ε : ℕ → ℝ}
  {D : HighOrderTargetSeq E} {κdecr κuns κunc : ℝ} {π ρ ρ' : ℕ → ℝ}

/-- If the contract keyed on (14.3.19) holds with radii $\rho$, and $\rho'_j \le \rho_j$ for
$j = 1, \dots, q$, then it holds with radii $\rho'$. -/
theorem IsInnerTestContract.mono_radius
    (h : D.IsInnerTestContract f c X q θ β ε κdecr κuns κunc π ρ)
    (hρ : ∀ j ∈ Finset.Icc 1 q, ρ' j ≤ ρ j) :
    D.IsInnerTestContract f c X q θ β ε κdecr κuns κunc π ρ' where
  toIsMeritContract := h.toIsMeritContract
  radius_ge k hk1 hk hb ht j hj := (hρ j hj).trans (h.radius_ge k hk1 hk hb ht j hj)

end HighOrderTargetSeq

namespace IsHighOrderTargetRun

variable {f : E → ℝ} {c : E → F} {X : Set E} {q : ℕ} {θ β : ℝ} {ε : ℕ → ℝ} {x₁ : E}
  {D : HighOrderTargetSeq E} {κdecr κuns κunc πmax M : ℝ} {π : ℕ → ℝ}

/-- In a run, let $\kappa_{\mathrm{decr}} > 0$, $0 \le \pi_l \le \pi_{\max}$ for $l = 1, \dots, q$,
and $M > 0$ with $\varepsilon_0^{2 - \pi_l} \varepsilon_l^{-\pi_l} \le M$ for $l = 1, \dots, q$.
Let $k \ge 1$ be an outer iteration that is reached and let $i < e_k$. If for some
$l \in \{1, \dots, q\}$
$$\mu(x_{k,i}, t_k) - \mu(x_{k,i+1}, t_k) \ge \kappa_{\mathrm{decr}} (\beta \|r(x_k, t_k)\|
  \varepsilon_l)^{\pi_l},$$
then the residual drops by at least the decrease $\kappa_{\mathrm{decr}}
(\beta\theta)^{\pi_{\max}} \varepsilon_0 / M$ of `Constrained.goodDecr`:
$$\|r(x_{k,i}, t_k)\| - \|r(x_{k,i+1}, t_k)\| \ge \frac{\kappa_{\mathrm{decr}}
  (\beta\theta)^{\pi_{\max}} \varepsilon_0}{M}.$$

The proof specializes `Constrained.sub_ge_of_merit_decrease`. -/
theorem residual_drop (h : IsHighOrderTargetRun f c X q θ β ε x₁ D) (hκ : 0 < κdecr)
    (hπ : ∀ l ∈ Finset.Icc 1 q, 0 ≤ π l ∧ π l ≤ πmax) (hM0 : 0 < M)
    (hM : ∀ l ∈ Finset.Icc 1 q, ε 0 ^ (2 - π l) * ε l ^ (-π l) ≤ M)
    {k : ℕ} (hk1 : 1 ≤ k) (hk : D.Before f c X q θ ε k) {i : ℕ} (hie : i < D.e k)
    (hdecr : ∃ l ∈ Finset.Icc 1 q,
      κdecr * (β * targetResidual f c (D.t k) (D.x k) * ε l) ^ π l ≤
        targetMerit f c (D.t k) (D.xi k i) - targetMerit f c (D.t k) (D.xi k (i + 1))) :
    goodDecr κdecr β θ πmax M (ε 0) ≤
      targetResidual f c (D.t k) (D.xi k i) - targetResidual f c (D.t k) (D.xi k (i + 1)) := by
  obtain ⟨l, hl, hdec⟩ := hdecr
  rw [targetMerit_eq, targetMerit_eq] at hdec
  have hρi := h.inner_residual_antitone hk1 hk (Nat.zero_le i) hie.le
  rw [h.inner_zero k hk1 hk] at hρi
  exact sub_ge_of_merit_decrease h.β_pos h.θ_pos
    (by have := h.β_le_θ; have := h.θ_lt_one; have := h.β_pos; nlinarith) h.ε₀_pos hκ
    (hπ l hl).1 (hπ l hl).2 (h.ε_pos' hl) hM0 (hM l hl)
    (h.toRun.le_residual_of_pos hk1 hk (Nat.zero_lt_of_lt hie)) (h.residual_le hk1 hk) hρi
    (h.inner_residual_antitone hk1 hk i.le_succ hie) hdec

end IsHighOrderTargetRun

namespace HighOrderTargetSeq.IsMeritContract

variable {f : E → ℝ} {c : E → F} {X : Set E} {q : ℕ} {θ β : ℝ} {ε : ℕ → ℝ} {x₁ : E}
  {D : HighOrderTargetSeq E} {exempt : ℕ → Prop} {κdecr κuns κunc πmax M : ℝ} {π : ℕ → ℝ}

/-- **The merit contract is a contract of the generic outer loop.** In a run, let the inner calls
satisfy the merit contract for an exemption test, with $\kappa_{\mathrm{decr}} > 0$,
$0 \le \pi_l \le \pi_{\max}$ and $M > 0$ with $\varepsilon_0^{2 - \pi_l} \varepsilon_l^{-\pi_l}
\le M$ for $l = 1, \dots, q$. Then the data of the generic outer loop satisfy
`Constrained.TargetFollowingSeq.IsInnerContract` with the same exemption test, the same
constants $\kappa_{\mathrm{uns}}$ and $\kappa_{\mathrm{unc}}$, and the residual decrease of
`Constrained.goodDecr`. -/
theorem toContract (hin : D.IsMeritContract f c X q θ β ε exempt κdecr κuns κunc π)
    (h : IsHighOrderTargetRun f c X q θ β ε x₁ D) (hκ : 0 < κdecr)
    (hπ : ∀ l ∈ Finset.Icc 1 q, 0 ≤ π l ∧ π l ≤ πmax) (hM0 : 0 < M)
    (hM : ∀ l ∈ Finset.Icc 1 q, ε 0 ^ (2 - π l) * ε l ^ (-π l) ≤ M) :
    (D.toTargetFollowingSeq f c X q θ ε).IsInnerContract f c θ (ε 0) D.succ exempt
      (goodDecr κdecr β θ πmax M (ε 0)) κuns κunc where
  count := hin.count
  stay := hin.stay
  decrease k hk1 hk i hi := h.residual_drop hκ hπ hM0 hM hk1 hk hi.1
    (hin.decrease k hk1 hk i hi.1 hi.2.1 hi.2.2.1 hi.2.2.2)

end HighOrderTargetSeq.IsMeritContract

/-! ### Complexity with the bad outer iterations as a parameter -/

namespace IsHighOrderTargetRun

open HighOrderTargetSeq

variable {f : E → ℝ} {c : E → F} {X : Set E} {q : ℕ} {θ β : ℝ} {ε : ℕ → ℝ} {x₁ : E}
  {D : HighOrderTargetSeq E} {exempt : ℕ → Prop} {κdecr κuns κunc πmax M : ℝ} {π : ℕ → ℝ}

/-- In a run, if $\kappa_{\mathrm{decr}} > 0$ and $M > 0$, then the residual decrease
$\kappa_{\mathrm{decr}} (\beta\theta)^{\pi_{\max}} \varepsilon_0 / M$ is positive. -/
theorem goodDecr_pos (h : IsHighOrderTargetRun f c X q θ β ε x₁ D) (hκ : 0 < κdecr)
    (hM0 : 0 < M) : 0 < goodDecr κdecr β θ πmax M (ε 0) :=
  Constrained.goodDecr_pos hκ h.β_pos h.θ_pos hM0 h.ε₀_pos

/-- In a run, if $\kappa_{\mathrm{decr}} > 0$ and $M > 0$, then the bound $G$ of (14.3.71) equals
$(1 - \theta)\varepsilon_0$ divided by the residual decrease $\kappa_{\mathrm{decr}}
(\beta\theta)^{\pi_{\max}} \varepsilon_0 / M$. -/
theorem goodBound_eq (h : IsHighOrderTargetRun f c X q θ β ε x₁ D) (hκ : 0 < κdecr)
    (hM0 : 0 < M) :
    goodBound κdecr β θ πmax M = (1 - θ) * ε 0 / goodDecr κdecr β θ πmax M (ε 0) :=
  Constrained.goodBound_eq hκ h.β_pos h.θ_pos hM0 h.ε₀_pos

/-- **Phase 2 of a high-order target-following run, with the bad outer iterations as a parameter.**
In a run, let the inner calls satisfy the merit contract for an exemption test, with
$\kappa_{\mathrm{decr}} > 0$, $\kappa_{\mathrm{uns}} \ge 0$, $0 \le \pi_l \le \pi_{\max}$, and
$M > 0$ with $\varepsilon_0^{2 - \pi_l} \varepsilon_l^{-\pi_l} \le M$ for $l = 1, \dots, q$.
Assume that $f_{\mathrm{low}} \le f(z) \le f_{\mathrm{up}}$ for every $z \in X$ with
$\|c(z)\| \le \varepsilon_0$ (assumption f.B.Fb). Write $N_a = (f_{\mathrm{up}} -
f_{\mathrm{low}} + 1)/((1 - \theta)\varepsilon_0)$, let $G$ be the bound
$\kappa_{\mathrm{decr}}^{-1} (\beta\theta)^{-\pi_{\max}} (1 - \theta) M$, and let
$n_{\mathrm{bad}}(K)$ be the number of bad outer iterations in $[1, K)$ for the exemption test.
Then:

* (i) every outer iteration $K \ge 1$ that is reached satisfies
  $K \le (N_a + 1)(G + 1) + n_{\mathrm{bad}}(K)$;
* (ii) if $n_{\mathrm{bad}}(K) \le B$ for every outer iteration $K$ that is reached, then Phase
  2 terminates at some outer iteration $k_\varepsilon \le (N_a + 1)(G + 1) + B$;
* (iii) if Phase 2 terminates at $k_\varepsilon$, it uses at most
  $1 + G(N_a + 1) + k_\varepsilon$ derivative evaluations and at most $1 +
  \kappa_{\mathrm{uns}}(G(N_a + 1) + k_\varepsilon) + \kappa_{\mathrm{unc}} k_\varepsilon$
  evaluations of $(f, c)$.

This is Theorem 14.3.9 of [cartis2022evaluation] for Phase 2, with the number of bad outer
iterations as a parameter. The proof specializes
`Constrained.TargetFollowingSeq.IsInnerContract.complexity`. -/
theorem complexity (h : IsHighOrderTargetRun f c X q θ β ε x₁ D)
    (hin : D.IsMeritContract f c X q θ β ε exempt κdecr κuns κunc π) (hκ : 0 < κdecr)
    (hκuns : 0 ≤ κuns) (hπ : ∀ l ∈ Finset.Icc 1 q, 0 ≤ π l ∧ π l ≤ πmax) (hM0 : 0 < M)
    (hM : ∀ l ∈ Finset.Icc 1 q, ε 0 ^ (2 - π l) * ε l ^ (-π l) ≤ M) {flow fup : ℝ}
    (hB : ∀ z ∈ X, ‖c z‖ ≤ ε 0 → flow ≤ f z ∧ f z ≤ fup) :
    (∀ K, 1 ≤ K → D.Before f c X q θ ε K →
      (K : ℝ) ≤ ((fup - flow + 1) / ((1 - θ) * ε 0) + 1) * (goodBound κdecr β θ πmax M + 1) +
        (D.toTargetFollowingSeq f c X q θ ε).badCount f c θ (ε 0) D.succ exempt K) ∧
    (∀ Bb : ℝ, (∀ K, D.Before f c X q θ ε K →
        ((D.toTargetFollowingSeq f c X q θ ε).badCount f c θ (ε 0) D.succ exempt K : ℝ) ≤ Bb) →
      ∃ kε, D.IsEnd f c X q θ ε kε ∧
        (kε : ℝ) ≤ ((fup - flow + 1) / ((1 - θ) * ε 0) + 1) *
          (goodBound κdecr β θ πmax M + 1) + Bb) ∧
    (∀ kε, D.IsEnd f c X q θ ε kε →
      (D.derivEvals kε : ℝ) ≤
        1 + goodBound κdecr β θ πmax M * ((fup - flow + 1) / ((1 - θ) * ε 0) + 1) + kε ∧
      (D.funEvals kε : ℝ) ≤
        1 + κuns * (goodBound κdecr β θ πmax M * ((fup - flow + 1) / ((1 - θ) * ε 0) + 1) +
          kε) + κunc * kε) :=
  (hin.toContract h hκ hπ hM0 hM).complexity h.toRun (h.goodDecr_pos hκ hM0)
    (h.goodBound_eq hκ hM0).ge hκuns hB

/-- **Phase 2 given a bound on the bad outer iterations.** Under the assumptions of
`Constrained.IsHighOrderTargetRun.complexity`, suppose that $n_{\mathrm{bad}}(K) \le N_b$ for
every outer iteration $K \ge 1$ that is reached. Then every such $K$ satisfies
$K \le (N_a + 1)(G + 1) + N_b$. Moreover Phase 2 terminates at some outer iteration
$k_\varepsilon \le (N_a + 1)(G + 1) + N_b$, and it uses at most $1 + G(N_a + 1) + k_\varepsilon$
derivative evaluations and at most $1 + \kappa_{\mathrm{uns}}(G(N_a + 1) + k_\varepsilon) +
\kappa_{\mathrm{unc}} k_\varepsilon$ evaluations of $(f, c)$. -/
theorem complexity_of_badCount_le (h : IsHighOrderTargetRun f c X q θ β ε x₁ D)
    (hin : D.IsMeritContract f c X q θ β ε exempt κdecr κuns κunc π) (hκ : 0 < κdecr)
    (hκuns : 0 ≤ κuns) (hπ : ∀ l ∈ Finset.Icc 1 q, 0 ≤ π l ∧ π l ≤ πmax) (hM0 : 0 < M)
    (hM : ∀ l ∈ Finset.Icc 1 q, ε 0 ^ (2 - π l) * ε l ^ (-π l) ≤ M) {flow fup : ℝ}
    (hB : ∀ z ∈ X, ‖c z‖ ≤ ε 0 → flow ≤ f z ∧ f z ≤ fup) {Nb : ℝ}
    (hNb : ∀ K, 1 ≤ K → D.Before f c X q θ ε K →
      ((D.toTargetFollowingSeq f c X q θ ε).badCount f c θ (ε 0) D.succ exempt K : ℝ) ≤ Nb) :
    (∀ K, 1 ≤ K → D.Before f c X q θ ε K →
      (K : ℝ) ≤ ((fup - flow + 1) / ((1 - θ) * ε 0) + 1) *
        (goodBound κdecr β θ πmax M + 1) + Nb) ∧
    ∃ kε, D.IsEnd f c X q θ ε kε ∧
      (kε : ℝ) ≤ ((fup - flow + 1) / ((1 - θ) * ε 0) + 1) *
        (goodBound κdecr β θ πmax M + 1) + Nb ∧
      (D.derivEvals kε : ℝ) ≤
        1 + goodBound κdecr β θ πmax M * ((fup - flow + 1) / ((1 - θ) * ε 0) + 1) + kε ∧
      (D.funEvals kε : ℝ) ≤
        1 + κuns * (goodBound κdecr β θ πmax M * ((fup - flow + 1) / ((1 - θ) * ε 0) + 1) +
          kε) + κunc * kε :=
  (hin.toContract h hκ hπ hM0 hM).complexity_of_badCount_le h.toRun (h.goodDecr_pos hκ hM0)
    (h.goodBound_eq hκ hM0).ge hκuns hB hNb

end IsHighOrderTargetRun

/-! ### The target drop of case-(b) iterations passing the inner method's test -/

section TargetDrop

variable [InnerProductSpace ℝ F]

/-- Let $f$ and $c$ be of class $C^q$ at $x$, with $\|\nabla^i f(x)\| \le B_f$ for
$i = 1, \dots, q$. Then for all targets $t$ and $t'$, the Taylor jets of $\mu(\cdot, t)$ and
$\mu(\cdot, t')$ at $x$ are $|t - t'| B_f$-close up to order $q$:
$$\|\nabla^i \mu(x, t) - \nabla^i \mu(x, t')\| \le |t - t'| B_f \quad \text{for } i = 1, \dots,
  q.$$

At the orders $i \ge 1$ the jets differ by $(t' - t) \nabla^i f(x)$
(`Constrained.iteratedFDeriv_targetMerit_eq_sub`). The statement is `Optimization.JetApprox` for
the two Taylor series. -/
theorem jetApprox_targetMerit {f : E → ℝ} {c : E → F} {x : E} {q : ℕ}
    (hf : ContDiffAt ℝ q f x) (hc : ContDiffAt ℝ q c x) {Bf : ℝ}
    (hB : ∀ i ∈ Finset.Icc 1 q, ‖iteratedFDeriv ℝ i f x‖ ≤ Bf) (t t' : ℝ) :
    Optimization.JetApprox (ftaylorSeries ℝ (targetMerit f c t') x)
      (ftaylorSeries ℝ (targetMerit f c t) x) q (fun _ => |t - t'| * Bf) := by
  intro i hi
  have hi1 : i ≠ 0 := by have := (Finset.mem_Icc.1 hi).1; omega
  have hiq : (i : WithTop ℕ∞) ≤ q := by exact_mod_cast (Finset.mem_Icc.1 hi).2
  have hfi := hf.of_le hiq
  have hci := hc.of_le hiq
  change ‖iteratedFDeriv ℝ i (targetMerit f c t) x - iteratedFDeriv ℝ i (targetMerit f c t') x‖ ≤
    |t - t'| * Bf
  rw [iteratedFDeriv_targetMerit_eq_sub (t := t) hi1 hfi hci,
    iteratedFDeriv_targetMerit_eq_sub (t := t') hi1 hfi hci, sub_sub_sub_cancel_left,
    ← sub_smul, norm_smul, Real.norm_eq_abs, abs_sub_comm]
  exact mul_le_mul_of_nonneg_left (hB i hi) (abs_nonneg _)

/-- If $d > 0$, $A_j \ge 0$ and $2 B_f \tau \le A_j$ for every $j \in J$, and $A_j < 2 B_f d$ for
some $j \in J$, then $\tau \le d$. -/
private theorem le_of_exists_lt {Bf τ d : ℝ} {A : ℕ → ℝ} {J : Finset ℕ} (hd : 0 < d)
    (hA : ∀ j ∈ J, 0 ≤ A j) (hτ : ∀ j ∈ J, 2 * Bf * τ ≤ A j) (h : ∃ j ∈ J, A j < 2 * Bf * d) :
    τ ≤ d := by
  obtain ⟨j, hj, hlt⟩ := h
  have hBf : 0 < 2 * Bf := by
    by_contra hneg
    push Not at hneg
    nlinarith [hA j hj]
  exact (lt_of_mul_lt_mul_left ((hτ j hj).trans_lt hlt) hBf.le).le

namespace IsHighOrderTargetRun

open HighOrderTargetSeq

variable {f : E → ℝ} {c : E → F} {X : Set E} {q : ℕ} {θ β : ℝ} {ε : ℕ → ℝ} {x₁ : E}
  {D : HighOrderTargetSeq E} {exempt : ℕ → Prop} {κdecr κuns κunc πmax M : ℝ} {π ρ : ℕ → ℝ}
  {Bf : ℝ}

/-- **A case-(b) outer iteration that passes the termination test of the inner method lowers the
target, with an explicit margin.** In a run, let $\rho_j \ge 0$ for $j = 1, \dots, q$, let $f$
and $c$ be of class $C^q$ at the points of $X$, and let $\|\nabla^i f(y)\| \le B_f$ for
$i = 1, \dots, q$ at the points $y \in X$ with $\|c(y)\| \le \varepsilon_0$. Let $k \ge 1$ be an
outer iteration in $\mathcal{K}_b$ that is reached and does not terminate Phase 2, whose new
iterate passes the test (14.3.19), with radii $\delta_{k+1,j} \ge \rho_j$. If
$$0 \le m \le \|r(x_{k+1}, t_k)\| - \beta \|r(x_k, t_k)\|,$$
then some order $j \in \{1, \dots, q\}$ satisfies
$$\frac{m \varepsilon_j \rho_j^{j-1}}{j!} < 2 B_f (t_k - t_{k+1}).$$

The number $m$ bounds the gap between the tolerance $\varepsilon_j \|r(x_{k+1}, t_{k+1})\|$ of
(14.3.34), which fails at the new target, and the tolerance
$\beta \|r(x_k, t_k)\| \varepsilon_j$ of (14.3.19), which holds at the old target. The test
(14.3.19) is `Constrained.HighOrderTargetSeq.InnerTest`. -/
theorem target_drop_of_innerTest (h : IsHighOrderTargetRun f c X q θ β ε x₁ D)
    (hρ : ∀ j ∈ Finset.Icc 1 q, 0 ≤ ρ j) (hf : ∀ y ∈ X, ContDiffAt ℝ q f y)
    (hc : ∀ y ∈ X, ContDiffAt ℝ q c y)
    (hBf : ∀ y ∈ X, ‖c y‖ ≤ ε 0 → ∀ i ∈ Finset.Icc 1 q, ‖iteratedFDeriv ℝ i f y‖ ≤ Bf)
    {k : ℕ} (hk1 : 1 ≤ k) (hk : D.Before f c X q θ ε (k + 1)) (hb : D.IsKb f c θ ε k)
    (hcert : D.InnerTest f c X q β ε k) (hrad : ∀ j ∈ Finset.Icc 1 q, ρ j ≤ D.δ (k + 1) j)
    {μm : ℝ} (hμ0 : 0 ≤ μm)
    (hμ : μm ≤ targetResidual f c (D.t k) (D.x (k + 1)) -
      β * targetResidual f c (D.t k) (D.x k)) :
    ∃ j ∈ Finset.Icc 1 q,
      μm * ε j * ρ j ^ (j - 1) / j ! < 2 * Bf * (D.t k - D.t (k + 1)) := by
  have hkB : D.Before f c X q θ ε k := hk.mono k.le_succ
  have hns : ¬ D.Stop f c X q θ ε k := hk k hk1 k.lt_succ_self
  have hncrit : ¬ targetCrit f c X q ε (D.t (k + 1)) (D.x (k + 1)) (D.δ (k + 1)) :=
    fun hm => hns (Or.inr ⟨Or.inr hb, hm⟩)
  rw [targetCrit_iff] at hncrit
  push Not at hncrit
  obtain ⟨j, hj, hlt⟩ := hncrit
  refine ⟨j, hj, ?_⟩
  have hjq : j ≤ q := (Finset.mem_Icc.1 hj).2
  have hj1 : 1 ≤ j := (Finset.mem_Icc.1 hj).1
  have hε₀ := h.ε₀_pos
  have hεj := h.ε_pos' hj
  obtain ⟨hδ0, hδ1⟩ := h.radius_mem k hk1 hkB j hj
  have hdrop : D.t (k + 1) < D.t k := h.toRun.target_succ_lt hk1 hk
  have hr' : targetResidual f c (D.t (k + 1)) (D.x (k + 1)) =
      targetResidual f c (D.t k) (D.x (k + 1)) := h.toRun.residual_succ_of_kb hk1 hkB hb
  have hrk : targetResidual f c (D.t k) (D.x k) ≤ ε 0 := h.residual_le hk1 hkB
  have hry : targetResidual f c (D.t k) (D.x (k + 1)) ≤ ε 0 :=
    (h.residual_succ_le hk1 hkB).trans hrk
  have hy : D.x (k + 1) ∈ X := h.mem_succ k hk1 hkB
  have hcy : ‖c (D.x (k + 1))‖ ≤ ε 0 := norm_le_targetResidual.trans hry
  have hBf0 : 0 ≤ Bf := (norm_nonneg _).trans (hBf _ hy hcy j hj)
  have hjet := jetApprox_targetMerit (t := D.t k) (t' := D.t (k + 1)) (hf _ hy)
    (hc _ hy) (hBf _ hy hcy)
  have h0 : (0 : E) ∈ {d | D.x (k + 1) + d ∈ X} := by
    change D.x (k + 1) + 0 ∈ X
    rw [add_zero]
    exact hy
  have hpert := Optimization.taylorMeasure_le_add_two_mul_of_jetApprox hjet hjq h0 hδ0.le hδ1
    (fun _ _ => le_rfl) (mul_nonneg (abs_nonneg _) hBf0)
  have hold := hcert j hj
  rw [abs_of_pos (sub_pos.2 hdrop)] at hpert
  have hfac : (0 : ℝ) < j ! := by positivity
  set δj := D.δ (k + 1) j
  -- `μm ε_j δ^j/j! < 2 B_f (t_k - t_{k+1}) δ`
  have key : μm * ε j * δj ^ j / j ! < 2 * Bf * (D.t k - D.t (k + 1)) * δj := by
    have e1 : μm * ε j * δj ^ j / j ! ≤
        (ε j * targetResidual f c (D.t (k + 1)) (D.x (k + 1)) * δj ^ j / j !) -
          (β * targetResidual f c (D.t k) (D.x k) * ε j * δj ^ j / j !) := by
      rw [hr']
      have : μm * ε j * δj ^ j / j ! ≤ (targetResidual f c (D.t k) (D.x (k + 1)) -
          β * targetResidual f c (D.t k) (D.x k)) * ε j * δj ^ j / j ! := by
        gcongr
      refine this.trans (le_of_eq ?_)
      ring
    have e4 : 2 * ((D.t k - D.t (k + 1)) * Bf) * δj = 2 * Bf * (D.t k - D.t (k + 1)) * δj := by
      ring
    linarith
  have hpow : δj ^ j = δj ^ (j - 1) * δj := by
    rw [← pow_succ]
    congr 1
    omega
  have key2 : μm * ε j * δj ^ (j - 1) / j ! < 2 * Bf * (D.t k - D.t (k + 1)) := by
    refine lt_of_mul_lt_mul_right ?_ hδ0.le
    calc μm * ε j * δj ^ (j - 1) / j ! * δj
        = μm * ε j * δj ^ j / j ! := by rw [hpow]; ring
      _ < _ := key
  have hρδ : ρ j ^ (j - 1) ≤ δj ^ (j - 1) :=
    pow_le_pow_left₀ (hρ j hj) (hrad j hj) _
  calc μm * ε j * ρ j ^ (j - 1) / j !
      ≤ μm * ε j * δj ^ (j - 1) / j ! := by
        gcongr
    _ < _ := key2

/-- **A case-(b) outer iteration lowers the target when every case-(b) call passes the inner test.**
In a run, let every case-(b) call pass (14.3.19) with radii $\delta_{k+1,j} \ge \rho_j \ge 0$
(`Constrained.HighOrderTargetSeq.IsCertified`). Let $f$ and $c$ be of class $C^q$ at the points
of $X$, and let $\|\nabla^i f(y)\| \le B_f$ for $i = 1, \dots, q$ at the points $y \in X$ with
$\|c(y)\| \le \varepsilon_0$. Then every outer iteration $k \ge 1$ in $\mathcal{K}_b$ that is
reached and does not terminate Phase 2 has an order $j \in \{1, \dots, q\}$ with
$$\frac{(\theta - \beta) \varepsilon_0 \varepsilon_j \rho_j^{j-1}}{j!} < 2 B_f (t_k -
  t_{k+1}).$$

The test (14.3.34) fails at $(x_{k+1}, t_{k+1})$, while (14.3.19) holds at $(x_{k+1}, t_k)$ with
the smaller tolerance $\beta \|r(x_k, t_k)\| \varepsilon_j \le \beta\varepsilon_0\varepsilon_j$. -/
theorem target_drop_of_certified (h : IsHighOrderTargetRun f c X q θ β ε x₁ D)
    (hcert : D.IsCertified f c X q θ β ε ρ) (hρ : ∀ j ∈ Finset.Icc 1 q, 0 ≤ ρ j)
    (hf : ∀ y ∈ X, ContDiffAt ℝ q f y) (hc : ∀ y ∈ X, ContDiffAt ℝ q c y)
    (hBf : ∀ y ∈ X, ‖c y‖ ≤ ε 0 → ∀ i ∈ Finset.Icc 1 q, ‖iteratedFDeriv ℝ i f y‖ ≤ Bf)
    {k : ℕ} (hk1 : 1 ≤ k) (hk : D.Before f c X q θ ε (k + 1)) (hb : D.IsKb f c θ ε k) :
    ∃ j ∈ Finset.Icc 1 q,
      (θ - β) * ε 0 * ε j * ρ j ^ (j - 1) / j ! < 2 * Bf * (D.t k - D.t (k + 1)) := by
  have hkB : D.Before f c X q θ ε k := hk.mono k.le_succ
  have hrk : targetResidual f c (D.t k) (D.x k) ≤ ε 0 := h.residual_le hk1 hkB
  have hβ := h.β_pos
  have hm : (θ - β) * ε 0 ≤ targetResidual f c (D.t k) (D.x (k + 1)) -
      β * targetResidual f c (D.t k) (D.x k) := by
    have := hb.1
    nlinarith
  exact h.target_drop_of_innerTest hρ hf hc hBf hk1 hk hb (hcert.cert k hk1 hkB hb)
    (hcert.radius_ge k hk1 hkB hb) (mul_nonneg (sub_nonneg.2 h.β_le_θ) h.ε₀_pos.le) hm

/-- **The number of case-(b) outer iterations when every case-(b) call passes the inner test, for
$\beta < \theta$.** Under the assumptions of
`Constrained.IsHighOrderTargetRun.target_drop_of_certified` and assumption f.B.Fb, let
$\tau > 0$ satisfy
$$2 B_f \tau \le \frac{(\theta - \beta) \varepsilon_0 \varepsilon_j \rho_j^{j-1}}{j!} \quad
  \text{for } j = 1, \dots, q.$$
Then every outer iteration $K \ge 1$ that is reached satisfies
$$|\mathcal{K}_b \cap [1, K)| \le \frac{f_{\mathrm{up}} - f_{\mathrm{low}} + 1}{\tau}.$$

Every case-(b) iteration before termination lowers the target by more than $\tau$, and the
targets stay in $[f_{\mathrm{low}} - 1, f_{\mathrm{up}}]$. The statement does not assume
$\beta < \theta$, but for $q \ge 1$ and $B_f > 0$ the hypothesis on $\tau$ can hold only if
$\beta < \theta$. -/
theorem kbCount_le_of_certified (h : IsHighOrderTargetRun f c X q θ β ε x₁ D)
    (hcert : D.IsCertified f c X q θ β ε ρ) (hρ : ∀ j ∈ Finset.Icc 1 q, 0 ≤ ρ j)
    (hf : ∀ y ∈ X, ContDiffAt ℝ q f y) (hc : ∀ y ∈ X, ContDiffAt ℝ q c y)
    (hBf : ∀ y ∈ X, ‖c y‖ ≤ ε 0 → ∀ i ∈ Finset.Icc 1 q, ‖iteratedFDeriv ℝ i f y‖ ≤ Bf)
    {τ : ℝ} (hτ0 : 0 < τ)
    (hτ : ∀ j ∈ Finset.Icc 1 q, 2 * Bf * τ ≤ (θ - β) * ε 0 * ε j * ρ j ^ (j - 1) / j !)
    {flow fup : ℝ} (hB : ∀ z ∈ X, ‖c z‖ ≤ ε 0 → flow ≤ f z ∧ f z ≤ fup)
    {K : ℕ} (hK1 : 1 ≤ K) (hK : D.Before f c X q θ ε K) :
    (D.kbCount f c θ ε K : ℝ) ≤ (fup - flow + 1) / τ :=
  h.toRun.kbCount_le_of_drop hB hτ0 (fun k hk1 hk hb =>
    le_of_exists_lt (sub_pos.2 (h.toRun.target_succ_lt hk1 hk))
      (fun j hj => by
        have := h.ε₀_pos; have := h.ε_pos' hj; have := hρ j hj; have := sub_nonneg.2 h.β_le_θ
        positivity) hτ
      (h.target_drop_of_certified hcert hρ hf hc hBf hk1 hk hb)) hK1 hK

open Classical in
/-- **The case-(b) outer iterations that pass the termination test of the inner method, for every
$\beta \le \theta$.** In a run, let every case-(b) call that passes (14.3.19) return radii
$\delta_{k+1,j} \ge \rho_j \ge 0$. Assume the smoothness assumptions of
`Constrained.IsHighOrderTargetRun.target_drop_of_innerTest` and assumption f.B.Fb. Write $\eta =
\theta(1 - \theta)\varepsilon_0/(1 + \theta)$ (`Constrained.kbMargin`), and let $\tau > 0$
satisfy $2 B_f \tau \le \eta \varepsilon_j \rho_j^{j-1}/j!$ for $j = 1, \dots, q$. Then every
outer iteration $K \ge 1$ that is reached satisfies
$$|\{k \in [1, K) \mid k \in \mathcal{K}_b,\ k \text{ passes (14.3.19)}\}| \le |\mathcal{K}_a
  \cap [1, K)| + 1 + \frac{f_{\mathrm{up}} - f_{\mathrm{low}} + 1}{\tau}.$$

The iterations with margin $\|r(x_{k+1}, t_k)\| - \beta \|r(x_k, t_k)\| \ge \eta$ lower the
target by more than $\tau$ (`Constrained.IsHighOrderTargetRun.target_drop_of_innerTest`).
Between two consecutive elements of $\mathcal{K}_a$, at most one of the iterations counted here
has a margin smaller than $\eta$ (`Constrained.IsTargetFollowingRun.card_kb_le_of_margin`). The
result includes the case $\beta = \theta$. -/
theorem card_kb_innerTest_le (h : IsHighOrderTargetRun f c X q θ β ε x₁ D)
    (hrad : ∀ k, 1 ≤ k → D.Before f c X q θ ε k → D.IsKb f c θ ε k →
      D.InnerTest f c X q β ε k → ∀ j ∈ Finset.Icc 1 q, ρ j ≤ D.δ (k + 1) j)
    (hρ : ∀ j ∈ Finset.Icc 1 q, 0 ≤ ρ j) (hf : ∀ y ∈ X, ContDiffAt ℝ q f y)
    (hc : ∀ y ∈ X, ContDiffAt ℝ q c y)
    (hBf : ∀ y ∈ X, ‖c y‖ ≤ ε 0 → ∀ i ∈ Finset.Icc 1 q, ‖iteratedFDeriv ℝ i f y‖ ≤ Bf)
    {τ : ℝ} (hτ0 : 0 < τ)
    (hτ : ∀ j ∈ Finset.Icc 1 q, 2 * Bf * τ ≤ kbMargin θ (ε 0) * ε j * ρ j ^ (j - 1) / j !)
    {flow fup : ℝ} (hB : ∀ z ∈ X, ‖c z‖ ≤ ε 0 → flow ≤ f z ∧ f z ≤ fup)
    {K : ℕ} (hK1 : 1 ≤ K) (hK : D.Before f c X q θ ε K) :
    ((((Finset.Ico 1 K).filter
        (fun k => D.IsKb f c θ ε k ∧ D.InnerTest f c X q β ε k)).card : ℕ) : ℝ) ≤
      D.kaCount f c θ ε K + 1 + (fup - flow + 1) / τ := by
  have hη0 := kbMargin_nonneg h.θ_pos.le h.θ_lt_one.le h.ε₀_pos.le
  exact h.toRun.card_kb_le_of_margin hB h.β_pos.le h.β_le_θ hτ0
    (fun k hk1 hk hb htest hm => le_of_exists_lt (sub_pos.2 (h.toRun.target_succ_lt hk1 hk))
      (fun j hj => by have := h.ε_pos' hj; have := hρ j hj; positivity) hτ
      (h.target_drop_of_innerTest hρ hf hc hBf hk1 hk hb htest
        (hrad k hk1 (hk.mono k.le_succ) hb htest) hη0 hm)) hK1 hK

/-- **The number of case-(b) outer iterations when every case-(b) call passes the inner test, for
every $\beta \le \theta$.** Under the assumptions of
`Constrained.IsHighOrderTargetRun.card_kb_innerTest_le`, with the radii of
`Constrained.HighOrderTargetSeq.IsCertified`, every outer iteration $K \ge 1$ that is reached
satisfies
$$|\mathcal{K}_b \cap [1, K)| \le |\mathcal{K}_a \cap [1, K)| + 1 + \frac{f_{\mathrm{up}} -
  f_{\mathrm{low}} + 1}{\tau}.$$
-/
theorem kbCount_le_of_certified_margin (h : IsHighOrderTargetRun f c X q θ β ε x₁ D)
    (hcert : D.IsCertified f c X q θ β ε ρ) (hρ : ∀ j ∈ Finset.Icc 1 q, 0 ≤ ρ j)
    (hf : ∀ y ∈ X, ContDiffAt ℝ q f y) (hc : ∀ y ∈ X, ContDiffAt ℝ q c y)
    (hBf : ∀ y ∈ X, ‖c y‖ ≤ ε 0 → ∀ i ∈ Finset.Icc 1 q, ‖iteratedFDeriv ℝ i f y‖ ≤ Bf)
    {τ : ℝ} (hτ0 : 0 < τ)
    (hτ : ∀ j ∈ Finset.Icc 1 q, 2 * Bf * τ ≤ kbMargin θ (ε 0) * ε j * ρ j ^ (j - 1) / j !)
    {flow fup : ℝ} (hB : ∀ z ∈ X, ‖c z‖ ≤ ε 0 → flow ≤ f z ∧ f z ≤ fup)
    {K : ℕ} (hK1 : 1 ≤ K) (hK : D.Before f c X q θ ε K) :
    (D.kbCount f c θ ε K : ℝ) ≤ D.kaCount f c θ ε K + 1 + (fup - flow + 1) / τ := by
  classical
  have := h.card_kb_innerTest_le (fun k hk1 hk hb _ => hcert.radius_ge k hk1 hk hb) hρ hf hc
    hBf hτ0 hτ hB hK1 hK
  refine le_trans (le_of_eq ?_) this
  rw [HighOrderTargetSeq.kbCount_eq_card_filter]
  have e : (Finset.Ico 1 K).filter (D.IsKb f c θ ε) = (Finset.Ico 1 K).filter
      (fun k => D.IsKb f c θ ε k ∧ D.InnerTest f c X q β ε k) := by
    refine Finset.filter_congr fun k hk => ⟨fun hb => ⟨hb, ?_⟩, fun h' => h'.1⟩
    rw [Finset.mem_Ico] at hk
    exact hcert.cert k hk.1 (hK.mono hk.2.le) hb
  rw [e]

/-- **Phase 2 when every case-(b) call passes the inner test, for $\beta < \theta$, without a
bad-iteration parameter.** In a run, let the inner calls satisfy a merit contract for some
exemption test, under the assumptions of `Constrained.IsHighOrderTargetRun.complexity`. Let
every case-(b) call pass (14.3.19) with radii $\delta_{k+1,j} \ge \rho_j \ge 0$
(`Constrained.HighOrderTargetSeq.IsCertified`). Let $f$ and $c$ be of class $C^q$ at the points
of $X$, let $\|\nabla^i f(y)\| \le B_f$ for $i = 1, \dots, q$ at the points $y \in X$ with
$\|c(y)\| \le \varepsilon_0$, and let $\tau > 0$ satisfy $2 B_f \tau \le (\theta - \beta)
\varepsilon_0 \varepsilon_j \rho_j^{j-1}/j!$ for $j = 1, \dots, q$. Write $N_b =
(f_{\mathrm{up}} - f_{\mathrm{low}} + 1)/\tau$. Then every outer iteration $K \ge 1$ that is
reached satisfies $K \le (N_a + 1)(G + 1) + N_b$. Moreover Phase 2 terminates at some outer
iteration $k_\varepsilon \le (N_a + 1)(G + 1) + N_b$, and it uses at most
$1 + G(N_a + 1) + k_\varepsilon$ derivative evaluations and at most $1 +
\kappa_{\mathrm{uns}}(G(N_a + 1) + k_\varepsilon) + \kappa_{\mathrm{unc}} k_\varepsilon$
evaluations of $(f, c)$. -/
theorem complexity_of_certified (h : IsHighOrderTargetRun f c X q θ β ε x₁ D)
    (hin : D.IsMeritContract f c X q θ β ε exempt κdecr κuns κunc π) (hκ : 0 < κdecr)
    (hκuns : 0 ≤ κuns) (hπ : ∀ l ∈ Finset.Icc 1 q, 0 ≤ π l ∧ π l ≤ πmax) (hM0 : 0 < M)
    (hM : ∀ l ∈ Finset.Icc 1 q, ε 0 ^ (2 - π l) * ε l ^ (-π l) ≤ M) {flow fup : ℝ}
    (hB : ∀ z ∈ X, ‖c z‖ ≤ ε 0 → flow ≤ f z ∧ f z ≤ fup)
    (hcert : D.IsCertified f c X q θ β ε ρ) (hρ : ∀ j ∈ Finset.Icc 1 q, 0 ≤ ρ j)
    (hf : ∀ y ∈ X, ContDiffAt ℝ q f y) (hc : ∀ y ∈ X, ContDiffAt ℝ q c y)
    (hBf : ∀ y ∈ X, ‖c y‖ ≤ ε 0 → ∀ i ∈ Finset.Icc 1 q, ‖iteratedFDeriv ℝ i f y‖ ≤ Bf)
    {τ : ℝ} (hτ0 : 0 < τ)
    (hτ : ∀ j ∈ Finset.Icc 1 q, 2 * Bf * τ ≤ (θ - β) * ε 0 * ε j * ρ j ^ (j - 1) / j !) :
    (∀ K, 1 ≤ K → D.Before f c X q θ ε K →
      (K : ℝ) ≤ ((fup - flow + 1) / ((1 - θ) * ε 0) + 1) *
        (goodBound κdecr β θ πmax M + 1) + (fup - flow + 1) / τ) ∧
    ∃ kε, D.IsEnd f c X q θ ε kε ∧
      (kε : ℝ) ≤ ((fup - flow + 1) / ((1 - θ) * ε 0) + 1) *
        (goodBound κdecr β θ πmax M + 1) + (fup - flow + 1) / τ ∧
      (D.derivEvals kε : ℝ) ≤
        1 + goodBound κdecr β θ πmax M * ((fup - flow + 1) / ((1 - θ) * ε 0) + 1) + kε ∧
      (D.funEvals kε : ℝ) ≤
        1 + κuns * (goodBound κdecr β θ πmax M * ((fup - flow + 1) / ((1 - θ) * ε 0) + 1) +
          kε) + κunc * kε :=
  h.complexity_of_badCount_le hin hκ hκuns hπ hM0 hM hB fun K hK1 hK =>
    (Nat.cast_le.2 (TargetFollowingSeq.badCount_le_kbCount K)).trans
      (h.kbCount_le_of_certified hcert hρ hf hc hBf hτ0 hτ hB hK1 hK)

/-- **Phase 2 when every case-(b) call passes the inner test, for every $\beta \le \theta$, without
a bad-iteration parameter.** Under the assumptions of
`Constrained.IsHighOrderTargetRun.complexity_of_certified`, with $\tau > 0$ that satisfies $2
B_f \tau \le \eta \varepsilon_j \rho_j^{j-1}/j!$ for $j = 1, \dots, q$ in place of the margin
$(\theta - \beta)\varepsilon_0$, where $\eta = \theta(1 - \theta)\varepsilon_0/(1 + \theta)$,
the same conclusions hold with
$$N_b = N_a + 1 + \frac{f_{\mathrm{up}} - f_{\mathrm{low}} + 1}{\tau}.$$

The proof uses `Constrained.IsHighOrderTargetRun.kbCount_le_of_certified_margin` and
`Constrained.IsHighOrderTargetRun.kaCount_le`. -/
theorem complexity_of_certified_margin (h : IsHighOrderTargetRun f c X q θ β ε x₁ D)
    (hin : D.IsMeritContract f c X q θ β ε exempt κdecr κuns κunc π) (hκ : 0 < κdecr)
    (hκuns : 0 ≤ κuns) (hπ : ∀ l ∈ Finset.Icc 1 q, 0 ≤ π l ∧ π l ≤ πmax) (hM0 : 0 < M)
    (hM : ∀ l ∈ Finset.Icc 1 q, ε 0 ^ (2 - π l) * ε l ^ (-π l) ≤ M) {flow fup : ℝ}
    (hB : ∀ z ∈ X, ‖c z‖ ≤ ε 0 → flow ≤ f z ∧ f z ≤ fup)
    (hcert : D.IsCertified f c X q θ β ε ρ) (hρ : ∀ j ∈ Finset.Icc 1 q, 0 ≤ ρ j)
    (hf : ∀ y ∈ X, ContDiffAt ℝ q f y) (hc : ∀ y ∈ X, ContDiffAt ℝ q c y)
    (hBf : ∀ y ∈ X, ‖c y‖ ≤ ε 0 → ∀ i ∈ Finset.Icc 1 q, ‖iteratedFDeriv ℝ i f y‖ ≤ Bf)
    {τ : ℝ} (hτ0 : 0 < τ)
    (hτ : ∀ j ∈ Finset.Icc 1 q, 2 * Bf * τ ≤ kbMargin θ (ε 0) * ε j * ρ j ^ (j - 1) / j !) :
    (∀ K, 1 ≤ K → D.Before f c X q θ ε K →
      (K : ℝ) ≤ ((fup - flow + 1) / ((1 - θ) * ε 0) + 1) *
        (goodBound κdecr β θ πmax M + 1) +
          ((fup - flow + 1) / ((1 - θ) * ε 0) + 1 + (fup - flow + 1) / τ)) ∧
    ∃ kε, D.IsEnd f c X q θ ε kε ∧
      (kε : ℝ) ≤ ((fup - flow + 1) / ((1 - θ) * ε 0) + 1) *
        (goodBound κdecr β θ πmax M + 1) +
          ((fup - flow + 1) / ((1 - θ) * ε 0) + 1 + (fup - flow + 1) / τ) ∧
      (D.derivEvals kε : ℝ) ≤
        1 + goodBound κdecr β θ πmax M * ((fup - flow + 1) / ((1 - θ) * ε 0) + 1) + kε ∧
      (D.funEvals kε : ℝ) ≤
        1 + κuns * (goodBound κdecr β θ πmax M * ((fup - flow + 1) / ((1 - θ) * ε 0) + 1) +
          kε) + κunc * kε :=
  h.complexity_of_badCount_le hin hκ hκuns hπ hM0 hM hB fun K hK1 hK =>
    (Nat.cast_le.2 (TargetFollowingSeq.badCount_le_kbCount K)).trans
      ((h.kbCount_le_of_certified_margin hcert hρ hf hc hBf hτ0 hτ hB hK1 hK).trans
        (by linarith [h.kaCount_le hB hK1 hK]))

end IsHighOrderTargetRun

end TargetDrop

/-! ### The two contracts and the complexity under the contract keyed on (14.3.19) -/

namespace HighOrderTargetSeq

variable {f : E → ℝ} {c : E → F} {X : Set E} {q : ℕ} {θ β : ℝ} {ε : ℕ → ℝ} {x₁ : E}
  {D : HighOrderTargetSeq E} {κdecr κuns κunc : ℝ} {π ρ : ℕ → ℝ}

/-- **From the contract that exempts (14.3.34) to the contract keyed on (14.3.19).** In a run, let
the inner calls satisfy `Constrained.HighOrderTargetSeq.IsEndCritContract`. Suppose that every
call that ends with $\|r(x_{k+1}, t_k)\| \ge \theta\varepsilon_0$ ends at a point that passes
(14.3.19), with radii $\delta_{k+1,j} \ge \rho_j$ for $j = 1, \dots, q$. Then the inner calls
satisfy `Constrained.HighOrderTargetSeq.IsInnerTestContract` with the radii $\rho$.

The hypothesis holds when the calls are interrupted only by the first test of (14.3.32). -/
theorem IsEndCritContract.toInnerTestContract
    (hin : D.IsEndCritContract f c X q θ β ε κdecr κuns κunc π)
    (h : IsHighOrderTargetRun f c X q θ β ε x₁ D)
    (hcert : ∀ k, 1 ≤ k → D.Before f c X q θ ε k →
      θ * ε 0 ≤ targetResidual f c (D.t k) (D.x (k + 1)) →
      D.InnerTest f c X q β ε k ∧ ∀ j ∈ Finset.Icc 1 q, ρ j ≤ D.δ (k + 1) j) :
    D.IsInnerTestContract f c X q θ β ε κdecr κuns κunc π ρ where
  count := hin.count
  stay := hin.stay
  decrease k hk1 hk i hi hs hcont hge := by
    by_cases hlt : i + 1 < D.e k
    · exact hin.decrease k hk1 hk i hi hs (Or.inl hlt) hge
    · have hie : i + 1 = D.e k := by omega
      rcases hcont with h' | h'
      · exact absurd h' hlt
      · have hge' : θ * ε 0 ≤ targetResidual f c (D.t k) (D.x (k + 1)) := by
          rw [← h.inner_end k hk1 hk, ← hie]; exact hge
        exact absurd (hcert k hk1 hk hge').1 h'
  radius_ge k hk1 hk hb _ := (hcert k hk1 hk hb.1).2

/-- **The contract keyed on (14.3.19) gives the contract that exempts (14.3.34).** In a run, if the
inner calls satisfy `Constrained.HighOrderTargetSeq.IsInnerTestContract`, then they satisfy
`Constrained.HighOrderTargetSeq.IsEndCritContract`.

Since $\beta \le \theta$ and $\|r(x_k, t_k)\| \le \varepsilon_0$, the test (14.3.19) at a point
with $\|r(x_{k+1}, t_k)\| \ge \theta\varepsilon_0$ implies (14.3.34) there. So every step that
the second contract exempts is exempted by the first. -/
theorem IsInnerTestContract.toEndCritContract
    (hin : D.IsInnerTestContract f c X q θ β ε κdecr κuns κunc π ρ)
    (h : IsHighOrderTargetRun f c X q θ β ε x₁ D) :
    D.IsEndCritContract f c X q θ β ε κdecr κuns κunc π where
  count := hin.count
  stay := hin.stay
  decrease k hk1 hk i hi hs hcont hge := by
    refine hin.decrease k hk1 hk i hi hs ?_ hge
    rcases hcont with h' | h'
    · exact Or.inl h'
    · by_cases hlt : i + 1 < D.e k
      · exact Or.inl hlt
      refine Or.inr fun htest => h' fun j hj => (htest j hj).trans ?_
      have hie : i + 1 = D.e k := by omega
      have hge' : θ * ε 0 ≤ targetResidual f c (D.t k) (D.x (k + 1)) := by
        rw [← h.inner_end k hk1 hk, ← hie]; exact hge
      have hrk : targetResidual f c (D.t k) (D.x k) ≤ ε 0 := h.residual_le hk1 hk
      have hβ := h.β_pos
      have hβθ := h.β_le_θ
      have hεj := h.ε_pos' hj
      have hδ := (h.radius_mem k hk1 hk j hj).1
      have hb : β * targetResidual f c (D.t k) (D.x k) ≤
          targetResidual f c (D.t k) (D.x (k + 1)) := by
        have : β * targetResidual f c (D.t k) (D.x k) ≤ θ * ε 0 := by
          calc _ ≤ θ * targetResidual f c (D.t k) (D.x k) := by
                gcongr; exact targetResidual_nonneg
            _ ≤ θ * ε 0 := by gcongr; exact h.θ_pos.le
        linarith
      have : β * targetResidual f c (D.t k) (D.x k) * ε j ≤
          ε j * targetResidual f c (D.t k) (D.x (k + 1)) := by nlinarith
      gcongr

end HighOrderTargetSeq

namespace IsHighOrderTargetRun

open HighOrderTargetSeq

variable [InnerProductSpace ℝ F] {f : E → ℝ} {c : E → F} {X : Set E} {q : ℕ} {θ β : ℝ}
  {ε : ℕ → ℝ} {x₁ : E} {D : HighOrderTargetSeq E} {κdecr κuns κunc πmax M : ℝ} {π ρ : ℕ → ℝ}
  {Bf : ℝ}

omit [InnerProductSpace ℝ F] in
open Classical in
/-- **Phase 2 under the contract keyed on (14.3.19), given a bound on the case-(b) iterations that
pass it.** In a run, let the inner calls satisfy
`Constrained.HighOrderTargetSeq.IsInnerTestContract`, under the assumptions of
`Constrained.IsHighOrderTargetRun.complexity`. Suppose that for every outer iteration $K \ge 1$
that is reached, the iterations $k \in [1, K) \cap \mathcal{K}_b$ that pass (14.3.19) number at
most $N_b$. Then every such $K$ satisfies $K \le (N_a + 1)(G + 1) + N_b$. Moreover Phase 2
terminates at some outer iteration $k_\varepsilon \le (N_a + 1)(G + 1) + N_b$, and it uses at
most $1 + G(N_a + 1) + k_\varepsilon$ derivative evaluations and at most $1 +
\kappa_{\mathrm{uns}}(G(N_a + 1) + k_\varepsilon) + \kappa_{\mathrm{unc}} k_\varepsilon$
evaluations of $(f, c)$.

The bad outer iterations for the exemption by (14.3.19) end at points that pass it
(`Constrained.IsTargetFollowingRun.badCount_le_card`). -/
theorem complexity_of_innerTest_card (h : IsHighOrderTargetRun f c X q θ β ε x₁ D)
    (hin : D.IsInnerTestContract f c X q θ β ε κdecr κuns κunc π ρ)
    (hκ : 0 < κdecr) (hκuns : 0 ≤ κuns) (hπ : ∀ l ∈ Finset.Icc 1 q, 0 ≤ π l ∧ π l ≤ πmax)
    (hM0 : 0 < M) (hM : ∀ l ∈ Finset.Icc 1 q, ε 0 ^ (2 - π l) * ε l ^ (-π l) ≤ M)
    {flow fup : ℝ} (hB : ∀ z ∈ X, ‖c z‖ ≤ ε 0 → flow ≤ f z ∧ f z ≤ fup)
    {Nb : ℝ} (hNb : ∀ K, 1 ≤ K → D.Before f c X q θ ε K →
      ((((Finset.Ico 1 K).filter
        (fun k => D.IsKb f c θ ε k ∧ D.InnerTest f c X q β ε k)).card : ℕ) : ℝ) ≤ Nb) :
    (∀ K, 1 ≤ K → D.Before f c X q θ ε K →
      (K : ℝ) ≤ ((fup - flow + 1) / ((1 - θ) * ε 0) + 1) *
        (goodBound κdecr β θ πmax M + 1) + Nb) ∧
    ∃ kε, D.IsEnd f c X q θ ε kε ∧
      (kε : ℝ) ≤ ((fup - flow + 1) / ((1 - θ) * ε 0) + 1) *
        (goodBound κdecr β θ πmax M + 1) + Nb ∧
      (D.derivEvals kε : ℝ) ≤
        1 + goodBound κdecr β θ πmax M * ((fup - flow + 1) / ((1 - θ) * ε 0) + 1) + kε ∧
      (D.funEvals kε : ℝ) ≤
        1 + κuns * (goodBound κdecr β θ πmax M * ((fup - flow + 1) / ((1 - θ) * ε 0) + 1) +
          kε) + κunc * kε :=
  h.complexity_of_badCount_le hin.toIsMeritContract hκ hκuns hπ hM0 hM hB fun K hK1 hK =>
    (Nat.cast_le.2 (h.toRun.badCount_le_card hin.stay hK)).trans (hNb K hK1 hK)

/-- **Phase 2 under the contract keyed on (14.3.19): termination within an explicit bound, without a
bad-iteration parameter, for every $\beta \le \theta$.** In a run, let the inner calls satisfy
`Constrained.HighOrderTargetSeq.IsInnerTestContract` with $\kappa_{\mathrm{decr}} > 0$,
$\kappa_{\mathrm{uns}} \ge 0$, $0 \le \pi_l \le \pi_{\max}$, radii $\rho_j \ge 0$, and $M > 0$
with $\varepsilon_0^{2 - \pi_l} \varepsilon_l^{-\pi_l} \le M$ for $l = 1, \dots, q$. Assume
f.B.Fb, let $f$ and $c$ be of class $C^q$ at the points of $X$, and let
$\|\nabla^i f(y)\| \le B_f$ for $i = 1, \dots, q$ at the points $y \in X$ with
$\|c(y)\| \le \varepsilon_0$. Let $\tau > 0$ satisfy $2 B_f \tau \le \eta \varepsilon_j
\rho_j^{j-1}/j!$ for $j = 1, \dots, q$, where $\eta = \theta(1 - \theta)\varepsilon_0/(1 +
\theta)$. Write
$$N_a = \frac{f_{\mathrm{up}} - f_{\mathrm{low}} + 1}{(1 - \theta)\varepsilon_0}, \qquad G =
  \kappa_{\mathrm{decr}}^{-1} (\beta\theta)^{-\pi_{\max}} (1 - \theta) M, \qquad N_b = N_a + 1 +
  \frac{f_{\mathrm{up}} - f_{\mathrm{low}} + 1}{\tau}.$$
Then every outer iteration $K \ge 1$ that is reached satisfies $K \le (N_a + 1)(G + 1) + N_b$.
Moreover Phase 2 terminates at some outer iteration $k_\varepsilon \le (N_a + 1)(G + 1) + N_b$,
and it uses at most $1 + G(N_a + 1) + k_\varepsilon$ derivative evaluations and at most $1 +
\kappa_{\mathrm{uns}}(G(N_a + 1) + k_\varepsilon) + \kappa_{\mathrm{unc}} k_\varepsilon$
evaluations of $(f, c)$.

This is Theorem 14.3.9 of [cartis2022evaluation] for Phase 2; the calls may be cut by any test
of (14.3.32). Every case-(b) iteration either ends at a point that passes (14.3.19), and at most
$N_b$ of these exist (`Constrained.IsHighOrderTargetRun.card_kb_innerTest_le`), or its call has
a counted successful iteration, namely its last one, and at most $G(N_a + 1)$ of these exist in
total. -/
theorem complexity_of_innerTest (h : IsHighOrderTargetRun f c X q θ β ε x₁ D)
    (hin : D.IsInnerTestContract f c X q θ β ε κdecr κuns κunc π ρ)
    (hκ : 0 < κdecr) (hκuns : 0 ≤ κuns) (hπ : ∀ l ∈ Finset.Icc 1 q, 0 ≤ π l ∧ π l ≤ πmax)
    (hM0 : 0 < M) (hM : ∀ l ∈ Finset.Icc 1 q, ε 0 ^ (2 - π l) * ε l ^ (-π l) ≤ M)
    {flow fup : ℝ} (hB : ∀ z ∈ X, ‖c z‖ ≤ ε 0 → flow ≤ f z ∧ f z ≤ fup)
    (hρ : ∀ j ∈ Finset.Icc 1 q, 0 ≤ ρ j) (hf : ∀ y ∈ X, ContDiffAt ℝ q f y)
    (hc : ∀ y ∈ X, ContDiffAt ℝ q c y)
    (hBf : ∀ y ∈ X, ‖c y‖ ≤ ε 0 → ∀ i ∈ Finset.Icc 1 q, ‖iteratedFDeriv ℝ i f y‖ ≤ Bf)
    {τ : ℝ} (hτ0 : 0 < τ)
    (hτ : ∀ j ∈ Finset.Icc 1 q, 2 * Bf * τ ≤ kbMargin θ (ε 0) * ε j * ρ j ^ (j - 1) / j !) :
    (∀ K, 1 ≤ K → D.Before f c X q θ ε K →
      (K : ℝ) ≤ ((fup - flow + 1) / ((1 - θ) * ε 0) + 1) *
        (goodBound κdecr β θ πmax M + 1) +
          ((fup - flow + 1) / ((1 - θ) * ε 0) + 1 + (fup - flow + 1) / τ)) ∧
    ∃ kε, D.IsEnd f c X q θ ε kε ∧
      (kε : ℝ) ≤ ((fup - flow + 1) / ((1 - θ) * ε 0) + 1) *
        (goodBound κdecr β θ πmax M + 1) +
          ((fup - flow + 1) / ((1 - θ) * ε 0) + 1 + (fup - flow + 1) / τ) ∧
      (D.derivEvals kε : ℝ) ≤
        1 + goodBound κdecr β θ πmax M * ((fup - flow + 1) / ((1 - θ) * ε 0) + 1) + kε ∧
      (D.funEvals kε : ℝ) ≤
        1 + κuns * (goodBound κdecr β θ πmax M * ((fup - flow + 1) / ((1 - θ) * ε 0) + 1) +
          kε) + κunc * kε := by
  classical
  exact h.complexity_of_innerTest_card hin hκ hκuns hπ hM0 hM hB fun K hK1 hK =>
    (h.card_kb_innerTest_le hin.radius_ge hρ hf hc hBf hτ0 hτ hB hK1 hK).trans
      (by linarith [h.kaCount_le hB hK1 hK])

end IsHighOrderTargetRun

/-! ### Order bounds with constants fixed before the tolerances -/

namespace IsHighOrderTargetRun

open HighOrderTargetSeq

variable [InnerProductSpace ℝ F] {f : E → ℝ} {c : E → F} {X : Set E} {q : ℕ} {θ β : ℝ}

omit [InnerProductSpace ℝ F] in
open Classical in
/-- **Phase 2 within an order bound, given a bound on the case-(b) iterations that pass (14.3.19).**
Fix $f$, $c$, $X$, $q \ge 1$, $\theta \in (0, 1)$, $\beta > 0$, $\kappa_{\mathrm{decr}} > 0$,
$\kappa_{\mathrm{uns}} \ge 0$, $\pi_{\max}$, $A \ge 0$ and $B_b \ge 0$. Then there are constants
$C_F, C_D, C_K \ge 0$ with the following property. Let $\kappa_{\mathrm{unc}} \ge 0$, and let
$D$ be a run whose inner calls satisfy `Constrained.HighOrderTargetSeq.IsInnerTestContract` with
the constants $\kappa_{\mathrm{decr}}$, $\kappa_{\mathrm{uns}}$, $\kappa_{\mathrm{unc}}$,
exponents $0 \le \pi_l \le \pi_{\max}$ and any radii. Assume f.B.Fb with
$f_{\mathrm{up}} - f_{\mathrm{low}} + 1 \le A$. Let $\Omega$ satisfy
$\varepsilon_0^{-1} \le \Omega$ and $\varepsilon_0^{1 - \pi_l} \varepsilon_l^{-\pi_l} \le
\Omega$ for $l = 1, \dots, q$. If for every outer iteration $K \ge 1$ that is reached, the
iterations $k \in [1, K) \cap \mathcal{K}_b$ that pass (14.3.19) number at most $B_b \Omega$,
then Phase 2 terminates at some outer iteration $k_\varepsilon \le C_K \Omega$, using at most
$C_F \Omega + \kappa_{\mathrm{unc}} k_\varepsilon$ evaluations of $(f, c)$ and at most
$C_D \Omega$ derivative evaluations.

This follows Lemma 14.3.8 and Theorem 14.3.9 of [cartis2022evaluation] for Phase 2. The proof
specializes `Constrained.IsHighOrderTargetRun.complexity_of_innerTest_card`. The constants do
not depend on the tolerances $\varepsilon$, the run, $\kappa_{\mathrm{unc}}$ or $\Omega$. -/
theorem exists_const_order_of_card (hq : 1 ≤ q)
    {κdecr κuns πmax A Bb : ℝ} (hκ : 0 < κdecr) (hκuns : 0 ≤ κuns) (hA : 0 ≤ A)
    (hBb : 0 ≤ Bb) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβ0 : 0 < β) :
    ∃ CF CD CK : ℝ, 0 ≤ CF ∧ 0 ≤ CD ∧ 0 ≤ CK ∧
      ∀ {ε : ℕ → ℝ} {x₁ : E} {D : HighOrderTargetSeq E} {π ρ : ℕ → ℝ} {flow fup O κunc : ℝ},
      0 ≤ κunc → IsHighOrderTargetRun f c X q θ β ε x₁ D →
      D.IsInnerTestContract f c X q θ β ε κdecr κuns κunc π ρ →
      (∀ l ∈ Finset.Icc 1 q, 0 ≤ π l ∧ π l ≤ πmax) →
      (∀ z ∈ X, ‖c z‖ ≤ ε 0 → flow ≤ f z ∧ f z ≤ fup) → fup - flow + 1 ≤ A →
      (ε 0)⁻¹ ≤ O → (∀ l ∈ Finset.Icc 1 q, ε 0 ^ (1 - π l) * ε l ^ (-π l) ≤ O) →
      (∀ K, 1 ≤ K → D.Before f c X q θ ε K →
        ((((Finset.Ico 1 K).filter
          (fun k => D.IsKb f c θ ε k ∧ D.InnerTest f c X q β ε k)).card : ℕ) : ℝ) ≤ Bb * O) →
      ∃ kε, D.IsEnd f c X q θ ε kε ∧ (D.funEvals kε : ℝ) ≤ CF * O + κunc * kε ∧
        (D.derivEvals kε : ℝ) ≤ CD * O ∧ (kε : ℝ) ≤ CK * O := by
  obtain ⟨a, ha_def⟩ : ∃ a, a = A / (1 - θ) := ⟨_, rfl⟩
  obtain ⟨g, hg_def⟩ : ∃ g, g = κdecr⁻¹ * (β * θ) ^ (-πmax) * (1 - θ) := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K, K = a * g * q + a + g * q + 1 + Bb := ⟨_, rfl⟩
  have h1θ : 0 < 1 - θ := by linarith
  have ha : 0 ≤ a := ha_def ▸ div_nonneg hA h1θ.le
  have hg : 0 ≤ g := by
    have := Real.rpow_nonneg (mul_pos hβ0 hθ0).le (-πmax)
    rw [hg_def]
    positivity
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hagq : 0 ≤ a * g * q := by positivity
  have hgq0 : 0 ≤ g * q := by positivity
  refine ⟨1 + κuns * (a * g * q + g * q + K), 1 + a * g * q + g * q + K, K,
    by positivity, by positivity, hK0,
    fun {ε x₁ D π ρ flow fup O κunc} hκunc h2 hin hπ hB hAf hO0 hOT hNb => ?_⟩
  have hε₀ := h2.ε₀_pos
  have hε₀1 : ε 0 ≤ 1 := h2.ε₀_le_one
  have hO1 : 1 ≤ O := ((one_le_inv₀ hε₀).2 hε₀1).trans hO0
  have hOnn : 0 ≤ O := zero_le_one.trans hO1
  -- the constant `M` of Lemma 14.3.8
  obtain ⟨M, hM_def⟩ : ∃ M, M = ∑ l ∈ Finset.Icc 1 q, ε 0 ^ (2 - π l) * ε l ^ (-π l) :=
    ⟨_, rfl⟩
  have hterm : ∀ l ∈ Finset.Icc 1 q, 0 < ε 0 ^ (2 - π l) * ε l ^ (-π l) := fun l hl =>
    mul_pos (Real.rpow_pos_of_pos hε₀ _) (Real.rpow_pos_of_pos (h2.ε_pos' hl) _)
  have hM0 : 0 < M := hM_def ▸ Finset.sum_pos hterm ⟨1, Finset.mem_Icc.2 ⟨le_rfl, hq⟩⟩
  have hM : ∀ l ∈ Finset.Icc 1 q, ε 0 ^ (2 - π l) * ε l ^ (-π l) ≤ M := fun l hl =>
    hM_def ▸ Finset.single_le_sum (f := fun l => ε 0 ^ (2 - π l) * ε l ^ (-π l))
      (fun i hi => (hterm i hi).le) hl
  have hMO : M ≤ q * (ε 0 * O) := by
    have : ∀ l ∈ Finset.Icc 1 q, ε 0 ^ (2 - π l) * ε l ^ (-π l) ≤ ε 0 * O := fun l hl => by
      rw [show 2 - π l = 1 + (1 - π l) by ring, Real.rpow_add hε₀, Real.rpow_one, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hOT l hl) hε₀.le
    have := Finset.sum_le_card_nsmul _ _ _ this
    rw [Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul] at this
    rw [hM_def]
    exact this
  obtain ⟨Na, hNa_def⟩ : ∃ Na, Na = (fup - flow + 1) / ((1 - θ) * ε 0) := ⟨_, rfl⟩
  have hNa : Na ≤ a * (ε 0)⁻¹ := by
    calc Na ≤ A / ((1 - θ) * ε 0) := hNa_def ▸ div_le_div_of_nonneg_right hAf (by positivity)
      _ = a * (ε 0)⁻¹ := by rw [ha_def]; field_simp
  obtain ⟨-, kε, hend, hkε, hD, hF⟩ := h2.complexity_of_innerTest_card hin hκ hκuns hπ hM0 hM hB
    hNb
  obtain ⟨G, hG_def⟩ : ∃ G, G = goodBound κdecr β θ πmax M := ⟨_, rfl⟩
  rw [← hNa_def, ← hG_def] at hkε hD hF
  have hGg : G = g * M := by rw [hG_def, hg_def, goodBound]
  have hGO : G ≤ g * q * (ε 0 * O) := by
    rw [hGg, mul_assoc]; exact mul_le_mul_of_nonneg_left hMO hg
  have hgq : 0 ≤ g * q := mul_nonneg hg (Nat.cast_nonneg q)
  have hεO : ε 0 * O ≤ O := mul_le_of_le_one_left hOnn hε₀1
  have hG1 : G ≤ g * q * O := hGO.trans (mul_le_mul_of_nonneg_left hεO hgq)
  have hG0 : 0 ≤ G := by rw [hGg]; exact mul_nonneg hg hM0.le
  have hNaO : Na ≤ a * O := hNa.trans (mul_le_mul_of_nonneg_left hO0 ha)
  have hGNa : G * (Na + 1) ≤ (a * g * q + g * q) * O := by
    have h1 : G * (Na + 1) ≤ G * (a * (ε 0)⁻¹ + 1) := by gcongr
    have h2' : G * (a * (ε 0)⁻¹) ≤ a * g * q * O := by
      calc G * (a * (ε 0)⁻¹) ≤ g * q * (ε 0 * O) * (a * (ε 0)⁻¹) :=
            mul_le_mul_of_nonneg_right hGO (mul_nonneg ha (inv_pos.2 hε₀).le)
        _ = a * g * q * O * (ε 0 * (ε 0)⁻¹) := by ring
        _ = a * g * q * O := by rw [mul_inv_cancel₀ hε₀.ne', mul_one]
    calc G * (Na + 1) ≤ G * (a * (ε 0)⁻¹ + 1) := h1
      _ = G * (a * (ε 0)⁻¹) + G := by ring
      _ ≤ a * g * q * O + g * q * O := add_le_add h2' hG1
      _ = (a * g * q + g * q) * O := by ring
  have hkK : (kε : ℝ) ≤ K * O := by
    have h1 : (Na + 1) * (G + 1) ≤ (a * g * q + a + g * q + 1) * O := by
      calc (Na + 1) * (G + 1) = G * (Na + 1) + Na + 1 := by ring
        _ ≤ (a * g * q + g * q) * O + a * O + O := by linarith
        _ = (a * g * q + a + g * q + 1) * O := by ring
    calc (kε : ℝ) ≤ (Na + 1) * (G + 1) + Bb * O := hkε
      _ ≤ (a * g * q + a + g * q + 1) * O + Bb * O := by linarith
      _ = K * O := by rw [hK]; ring
  refine ⟨kε, hend, ?_, ?_, hkK⟩
  · calc (D.funEvals kε : ℝ) ≤ 1 + κuns * (G * (Na + 1) + kε) + κunc * kε := hF
      _ ≤ O + κuns * ((a * g * q + g * q) * O + K * O) + κunc * kε := by gcongr
      _ = _ := by ring
  · calc (D.derivEvals kε : ℝ) ≤ 1 + G * (Na + 1) + kε := hD
      _ ≤ O + (a * g * q + g * q) * O + K * O := by gcongr
      _ = _ := by ring

open Classical in
/-- **Phase 2 within an order bound, with the count constant paid per outer iteration.** Fix $f$,
$c$, $X$, $q \ge 1$, $\theta \in (0, 1)$, $\beta > 0$, $\kappa_{\mathrm{decr}} > 0$,
$\kappa_{\mathrm{uns}} \ge 0$, $\kappa_\rho > 0$, $\pi_{\max}$, $B_f > 0$, $A \ge 0$ and
$b \ge 0$. Then there are constants $C_F, C_D, C_K \ge 0$ with the following property. Let
$\kappa_{\mathrm{unc}} \ge 0$, and let $D$ be a run whose inner calls satisfy
`Constrained.HighOrderTargetSeq.IsInnerTestContract` with the constants
$\kappa_{\mathrm{decr}}$, $\kappa_{\mathrm{uns}}$, $\kappa_{\mathrm{unc}}$, exponents
$0 \le \pi_l \le \pi_{\max}$ and radii $\rho_j = \kappa_\rho \rho'_j$ with $\rho'_j > 0$. Assume
f.B.Fb with $f_{\mathrm{up}} - f_{\mathrm{low}} + 1 \le A$, let $f$ and $c$ be of class $C^q$ at
the points of $X$, and let $\|\nabla^i f(y)\| \le B_f$ for $i = 1, \dots, q$ at the points
$y \in X$ with $\|c(y)\| \le \varepsilon_0$. Let $\Omega$ satisfy
$\varepsilon_0^{-1} \le \Omega$, $\varepsilon_0^{1 - \pi_l} \varepsilon_l^{-\pi_l} \le \Omega$
and $(\varepsilon_0 \varepsilon_j \rho'^{\,j-1}_j)^{-1} \le b \Omega$ for $j, l = 1, \dots, q$.
Then Phase 2 terminates at some outer iteration $k_\varepsilon \le C_K \Omega$, using at most
$C_F \Omega + \kappa_{\mathrm{unc}} k_\varepsilon$ evaluations of $(f, c)$ and at most
$C_D \Omega$ derivative evaluations.

This follows Lemma 14.3.8 and Theorem 14.3.9 of [cartis2022evaluation] for Phase 2. The
constants do not depend on the tolerances $\varepsilon$, the run, $\kappa_{\mathrm{unc}}$ or
$\Omega$. -/
theorem exists_const_order_of_innerTest_calls (hq : 1 ≤ q)
    {κdecr κuns κρ πmax Bf A b : ℝ}
    (hκ : 0 < κdecr) (hκuns : 0 ≤ κuns) (hκρ : 0 < κρ) (hBf0 : 0 < Bf)
    (hA : 0 ≤ A) (hb : 0 ≤ b) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβ0 : 0 < β) :
    ∃ CF CD CK : ℝ, 0 ≤ CF ∧ 0 ≤ CD ∧ 0 ≤ CK ∧
      ∀ {ε : ℕ → ℝ} {x₁ : E} {D : HighOrderTargetSeq E} {π ρ' : ℕ → ℝ} {flow fup O κunc : ℝ},
      0 ≤ κunc → IsHighOrderTargetRun f c X q θ β ε x₁ D →
      D.IsInnerTestContract f c X q θ β ε κdecr κuns κunc π (fun j => κρ * ρ' j) →
      (∀ j ∈ Finset.Icc 1 q, 0 < ρ' j) →
      (∀ l ∈ Finset.Icc 1 q, 0 ≤ π l ∧ π l ≤ πmax) →
      (∀ z ∈ X, ‖c z‖ ≤ ε 0 → flow ≤ f z ∧ f z ≤ fup) → fup - flow + 1 ≤ A →
      (∀ y ∈ X, ContDiffAt ℝ q f y) → (∀ y ∈ X, ContDiffAt ℝ q c y) →
      (∀ y ∈ X, ‖c y‖ ≤ ε 0 → ∀ i ∈ Finset.Icc 1 q, ‖iteratedFDeriv ℝ i f y‖ ≤ Bf) →
      (ε 0)⁻¹ ≤ O → (∀ l ∈ Finset.Icc 1 q, ε 0 ^ (1 - π l) * ε l ^ (-π l) ≤ O) →
      (∀ j ∈ Finset.Icc 1 q, (ε 0 * ε j * ρ' j ^ (j - 1))⁻¹ ≤ b * O) →
      ∃ kε, D.IsEnd f c X q θ ε kε ∧ (D.funEvals kε : ℝ) ≤ CF * O + κunc * kε ∧
        (D.derivEvals kε : ℝ) ≤ CD * O ∧ (kε : ℝ) ≤ CK * O := by
  obtain ⟨a, ha_def⟩ : ∃ a, a = A / (1 - θ) := ⟨_, rfl⟩
  obtain ⟨cj, hcj⟩ : ∃ cj : ℕ → ℝ,
      cj = fun j => 2 * Bf * j ! * (1 + θ) / (θ * (1 - θ) * κρ ^ (j - 1)) := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C, C = ∑ j ∈ Finset.Icc 1 q, cj j := ⟨_, rfl⟩
  have h1θ : 0 < 1 - θ := by linarith
  have ha : 0 ≤ a := ha_def ▸ div_nonneg hA h1θ.le
  have hcj0 : ∀ j, 0 ≤ cj j := fun j => by rw [hcj]; positivity
  have hC0 : 0 ≤ C := hC ▸ Finset.sum_nonneg fun j _ => hcj0 j
  have hbC : 0 ≤ b * C := mul_nonneg hb hC0
  obtain ⟨CF, CD, CK, hCF, hCD, hCK, hcard⟩ := exists_const_order_of_card
    (f := f) (c := c) (X := X) (θ := θ) (β := β) hq (πmax := πmax) hκ hκuns hA
    (Bb := a + 1 + A * (1 + b * C)) (by positivity) hθ0 hθ1 hβ0
  refine ⟨CF, CD, CK, hCF, hCD, hCK,
    fun {ε x₁ D π ρ' flow fup O κunc} hκunc h2 hin hρ' hπ hB hAf hf hc hBf hO0 hOT hOB =>
      hcard hκunc h2 hin hπ hB hAf hO0 hOT fun K hK1 hK => ?_⟩
  have hε₀ := h2.ε₀_pos
  have hε₀1 : ε 0 ≤ 1 := h2.ε₀_le_one
  have hO1 : 1 ≤ O := ((one_le_inv₀ hε₀).2 hε₀1).trans hO0
  have hOnn : 0 ≤ O := zero_le_one.trans hO1
  -- the target decrease `τ`
  obtain ⟨τj, hτj⟩ : ∃ τj : ℕ → ℝ,
      τj = fun j => kbMargin θ (ε 0) * ε j * (κρ * ρ' j) ^ (j - 1) / (2 * Bf * j !) :=
    ⟨_, rfl⟩
  obtain ⟨τ, hτ_def⟩ : ∃ τ, τ = Optimization.finMin 1 τj q := ⟨_, rfl⟩
  have hη : 0 < kbMargin θ (ε 0) := by unfold kbMargin; positivity
  have hτj0 : ∀ j ∈ Finset.Icc 1 q, 0 < τj j := fun j hj => by
    have := h2.ε_pos' hj
    have := hρ' j hj
    rw [hτj]
    positivity
  have hτ0 : 0 < τ := hτ_def ▸ Optimization.finMin_pos one_pos hτj0
  have hτ : ∀ j ∈ Finset.Icc 1 q,
      2 * Bf * τ ≤ kbMargin θ (ε 0) * ε j * (κρ * ρ' j) ^ (j - 1) / j ! := fun j hj => by
    have h1 : τ ≤ τj j := hτ_def ▸ Optimization.finMin_le (b := 1) hj (u := τj)
    have hfac : (0 : ℝ) < j ! := by positivity
    calc 2 * Bf * τ ≤ 2 * Bf * τj j := by gcongr
      _ = _ := by rw [hτj]; field_simp
  have hτinv : ∀ j ∈ Finset.Icc 1 q, (τj j)⁻¹ = cj j * (ε 0 * ε j * ρ' j ^ (j - 1))⁻¹ :=
    fun j hj => by
      have := h2.ε_pos' hj
      have := hρ' j hj
      rw [hτj, hcj]
      simp only [kbMargin]
      rw [mul_pow]
      field_simp
  have hAτ : (fup - flow + 1) / τ ≤ A * (1 + b * C) * O := by
    have h1 : (fup - flow + 1) / τ ≤ A * τ⁻¹ := by
      rw [div_eq_mul_inv]; exact mul_le_mul_of_nonneg_right hAf (inv_pos.2 hτ0).le
    have hsum : ∑ j ∈ Finset.Icc 1 q, (τj j)⁻¹ ≤ C * (b * O) := by
      rw [hC, Finset.sum_mul]
      exact Finset.sum_le_sum fun j hj => by
        rw [hτinv j hj]; exact mul_le_mul_of_nonneg_left (hOB j hj) (hcj0 j)
    have h2' : τ⁻¹ ≤ (1 + b * C) * O := by
      have := hτ_def ▸ Optimization.inv_finMin_one_le hτj0
      calc τ⁻¹ ≤ 1 + C * (b * O) := this.trans (by linarith)
        _ ≤ O + b * C * O := by nlinarith
        _ = (1 + b * C) * O := by ring
    calc (fup - flow + 1) / τ ≤ A * τ⁻¹ := h1
      _ ≤ A * ((1 + b * C) * O) := mul_le_mul_of_nonneg_left h2' hA
      _ = A * (1 + b * C) * O := by ring
  have hcard' := h2.card_kb_innerTest_le hin.radius_ge
    (fun j hj => by have := hρ' j hj; positivity) hf hc hBf hτ0 (hτ_def ▸ hτ) hB hK1 hK
  have hka : (D.kaCount f c θ ε K : ℝ) ≤ a * O := by
    refine (h2.kaCount_le hB hK1 hK).trans ?_
    calc (fup - flow + 1) / ((1 - θ) * ε 0) ≤ A / ((1 - θ) * ε 0) :=
          div_le_div_of_nonneg_right hAf (by positivity)
      _ = a * (ε 0)⁻¹ := by rw [ha_def]; field_simp
      _ ≤ a * O := mul_le_mul_of_nonneg_left hO0 ha
  have e : (a + 1 + A * (1 + b * C)) * O = a * O + O + A * (1 + b * C) * O := by ring
  rw [e]
  linarith

open Classical in
/-- **Phase 2 within an order bound, with a count constant chosen after the tolerances.** Under the
assumptions of `Constrained.IsHighOrderTargetRun.exists_const_order_of_innerTest_calls`, there
are constants $C_F, C_U, C_D \ge 0$ such that Phase 2 terminates using at most
$(C_F + C_U \kappa_{\mathrm{unc}}) \Omega$ evaluations of $(f, c)$ and at most $C_D \Omega$
derivative evaluations.

The constant $\kappa_{\mathrm{unc}}$ may depend on the tolerances $\varepsilon$, while $C_F$,
$C_U$ and $C_D$ do not. For example, inner calls that restart from a fixed trust-region radius
have a $\kappa_{\mathrm{unc}}$ that contains $|\log(\varepsilon_0 \varepsilon_{\min})|$. -/
theorem exists_const_order_of_innerTest_unc (hq : 1 ≤ q)
    {κdecr κuns κρ πmax Bf A b : ℝ}
    (hκ : 0 < κdecr) (hκuns : 0 ≤ κuns) (hκρ : 0 < κρ) (hBf0 : 0 < Bf)
    (hA : 0 ≤ A) (hb : 0 ≤ b) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβ0 : 0 < β) :
    ∃ CF CU CD : ℝ, 0 ≤ CF ∧ 0 ≤ CU ∧ 0 ≤ CD ∧
      ∀ {ε : ℕ → ℝ} {x₁ : E} {D : HighOrderTargetSeq E} {π ρ' : ℕ → ℝ} {flow fup O κunc : ℝ},
      0 ≤ κunc → IsHighOrderTargetRun f c X q θ β ε x₁ D →
      D.IsInnerTestContract f c X q θ β ε κdecr κuns κunc π (fun j => κρ * ρ' j) →
      (∀ j ∈ Finset.Icc 1 q, 0 < ρ' j) →
      (∀ l ∈ Finset.Icc 1 q, 0 ≤ π l ∧ π l ≤ πmax) →
      (∀ z ∈ X, ‖c z‖ ≤ ε 0 → flow ≤ f z ∧ f z ≤ fup) → fup - flow + 1 ≤ A →
      (∀ y ∈ X, ContDiffAt ℝ q f y) → (∀ y ∈ X, ContDiffAt ℝ q c y) →
      (∀ y ∈ X, ‖c y‖ ≤ ε 0 → ∀ i ∈ Finset.Icc 1 q, ‖iteratedFDeriv ℝ i f y‖ ≤ Bf) →
      (ε 0)⁻¹ ≤ O → (∀ l ∈ Finset.Icc 1 q, ε 0 ^ (1 - π l) * ε l ^ (-π l) ≤ O) →
      (∀ j ∈ Finset.Icc 1 q, (ε 0 * ε j * ρ' j ^ (j - 1))⁻¹ ≤ b * O) →
      ∃ kε, D.IsEnd f c X q θ ε kε ∧ (D.funEvals kε : ℝ) ≤ (CF + CU * κunc) * O ∧
        (D.derivEvals kε : ℝ) ≤ CD * O := by
  obtain ⟨CF, CD, CK, hCF, hCD, hCK, h⟩ := exists_const_order_of_innerTest_calls
    (f := f) (c := c) (X := X) hq hκ hκuns hκρ hBf0 hA hb hθ0 hθ1 hβ0 (πmax := πmax)
  refine ⟨CF, CK, CD, hCF, hCK, hCD,
    fun {ε x₁ D π ρ' flow fup O κunc} hκunc h2 hin hρ' hπ hB hAf hf hc hBf hO0 hOT hOB => ?_⟩
  obtain ⟨kε, hend, hF, hD, hK⟩ := h hκunc h2 hin hρ' hπ hB hAf hf hc hBf hO0 hOT hOB
  refine ⟨kε, hend, hF.trans ?_, hD⟩
  have := mul_le_mul_of_nonneg_left hK hκunc
  nlinarith

open Classical in
/-- **Phase 2 within an order bound, for every run that satisfies the contract keyed on (14.3.19).**
Fix $f$, $c$, $X$, $q \ge 1$, $\theta \in (0, 1)$, $\beta > 0$ and constants
$\kappa_{\mathrm{decr}} > 0$, $\kappa_{\mathrm{uns}} \ge 0$, $\kappa_{\mathrm{unc}} \ge 0$,
$\kappa_\rho > 0$, $\pi_{\max}$, $B_f > 0$, $A \ge 0$ and $b \ge 0$. Then there are constants
$C_F, C_D \ge 0$ with the following property. Let $D$ be a run, for any tolerances
$\varepsilon$, whose inner calls satisfy `Constrained.HighOrderTargetSeq.IsInnerTestContract`
with these constants, exponents $0 \le \pi_l \le \pi_{\max}$ and radii
$\rho_j = \kappa_\rho \rho'_j$ with $\rho'_j > 0$. Assume f.B.Fb with
$f_{\mathrm{up}} - f_{\mathrm{low}} + 1 \le A$, let $f$ and $c$ be of class $C^q$ at the points
of $X$, and let $\|\nabla^i f(y)\| \le B_f$ for $i = 1, \dots, q$ at the points $y \in X$ with
$\|c(y)\| \le \varepsilon_0$. Let $\Omega$ satisfy $\varepsilon_0^{-1} \le \Omega$,
$\varepsilon_0^{1 - \pi_l} \varepsilon_l^{-\pi_l} \le \Omega$ and $(\varepsilon_0 \varepsilon_j
\rho'^{\,j-1}_j)^{-1} \le b \Omega$ for $j, l = 1, \dots, q$; the last terms are the order of
the bad outer iterations. Then Phase 2 terminates at some outer iteration $k_\varepsilon$, using
at most $C_F \Omega$ evaluations of $(f, c)$ and at most $C_D \Omega$ derivative evaluations.

This is Theorem 14.3.9 of [cartis2022evaluation] for Phase 2. The proof specializes
`Constrained.IsHighOrderTargetRun.complexity_of_innerTest`. -/
theorem exists_const_order_of_innerTest (hq : 1 ≤ q)
    {κdecr κuns κunc κρ πmax Bf A b : ℝ}
    (hκ : 0 < κdecr) (hκuns : 0 ≤ κuns) (hκunc : 0 ≤ κunc) (hκρ : 0 < κρ) (hBf0 : 0 < Bf)
    (hA : 0 ≤ A) (hb : 0 ≤ b) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβ0 : 0 < β) :
    ∃ CF CD : ℝ, 0 ≤ CF ∧ 0 ≤ CD ∧
      ∀ {ε : ℕ → ℝ} {x₁ : E} {D : HighOrderTargetSeq E} {π ρ' : ℕ → ℝ} {flow fup O : ℝ},
      IsHighOrderTargetRun f c X q θ β ε x₁ D →
      D.IsInnerTestContract f c X q θ β ε κdecr κuns κunc π (fun j => κρ * ρ' j) →
      (∀ j ∈ Finset.Icc 1 q, 0 < ρ' j) →
      (∀ l ∈ Finset.Icc 1 q, 0 ≤ π l ∧ π l ≤ πmax) →
      (∀ z ∈ X, ‖c z‖ ≤ ε 0 → flow ≤ f z ∧ f z ≤ fup) → fup - flow + 1 ≤ A →
      (∀ y ∈ X, ContDiffAt ℝ q f y) → (∀ y ∈ X, ContDiffAt ℝ q c y) →
      (∀ y ∈ X, ‖c y‖ ≤ ε 0 → ∀ i ∈ Finset.Icc 1 q, ‖iteratedFDeriv ℝ i f y‖ ≤ Bf) →
      (ε 0)⁻¹ ≤ O → (∀ l ∈ Finset.Icc 1 q, ε 0 ^ (1 - π l) * ε l ^ (-π l) ≤ O) →
      (∀ j ∈ Finset.Icc 1 q, (ε 0 * ε j * ρ' j ^ (j - 1))⁻¹ ≤ b * O) →
      ∃ kε, D.IsEnd f c X q θ ε kε ∧ (D.funEvals kε : ℝ) ≤ CF * O ∧
        (D.derivEvals kε : ℝ) ≤ CD * O := by
  obtain ⟨CF, CU, CD, hCF, hCU, hCD, h⟩ :=
    exists_const_order_of_innerTest_unc (f := f) (c := c) (X := X) (θ := θ)
      (β := β) hq hκ hκuns hκρ hBf0 hA hb hθ0 hθ1 hβ0 (πmax := πmax)
  refine ⟨CF + CU * κunc, CD, by positivity, hCD, fun hP hR hρ hπ hB hAf hf hc hBf hO hOl
    hOb => ?_⟩
  exact h hκunc hP hR hρ hπ hB hAf hf hc hBf hO hOl hOb

end IsHighOrderTargetRun

end Constrained
