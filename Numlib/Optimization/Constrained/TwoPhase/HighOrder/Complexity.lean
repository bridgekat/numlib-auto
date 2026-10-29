import Numlib.Optimization.Constrained.TwoPhase.HighOrder.Basic
import Numlib.Optimization.ModelBased.HighOrder.Orders
import Numlib.Optimization.ModelBased.InexactTaylor

/-!
# Evaluation complexity of high-order target-following runs

For a run of Phase 2 of TPqp-GC (`Constrained.IsHighOrderTargetRun`, Algorithm 14.3.2 of
[cartis2022evaluation]) whose inner calls satisfy a merit-decrease contract (the form of
Lemmas 14.2.2–14.2.3 for `μ(·, t_k)`), this file bounds the number of outer iterations and the
evaluation counts (cf. Lemma 14.3.8 and Theorem 14.3.9 of [cartis2022evaluation], Phase 2).

The contract `HighOrderTargetSeq.IsMeritContract … exempt …` asks, at every outer iteration
`k ≥ 1` reached: `e_k ≤ κ_uns |𝒮_k| + κ_unc` (Lemma 2.4.1 or (14.2.13)), unsuccessful inner
iterations do not move, and every successful inner iteration `i` whose new iterate has residual
`≥ θε₀` and which is not the last iteration of a call ending at a point passing the exemption test
`exempt k` lowers the merit by `κ_decr min_l (β ‖r(x_k, t_k)‖ ε_l)^{π_l}` ((14.2.11) for the inner
method called with tolerances `β ‖r(x_k, t_k)‖ ε_l`). It is a residual-decrease contract of the
generic outer loop (`HighOrderTargetSeq.IsMeritContract.toContract`), so the counting of
`Numlib.Optimization.Constrained.TwoPhase.Complexity` applies; the number of bad outer iterations
(case (b), no counted inner iteration) remains a parameter (`IsHighOrderTargetRun.complexity`).

Two exemptions occur: the criticality test (14.3.34) at the old target
(`HighOrderTargetSeq.IsEndCritContract`),
and the termination test (14.3.19) of the inner method, together with a lower bound `ρ` on the
radii returned by case-(b) calls passing it (`HighOrderTargetSeq.IsInnerTestContract`, the form
in which Lemma 14.2.2 holds for runs of the inner method). A case-(b) call ending at a point
passing (14.3.19) for the old target, where (14.3.34) fails for the new one, lowers the target by
an amount bounded below in terms of the margin `‖r(x_{k+1}, t_k)‖ - β ‖r(x_k, t_k)‖`, since
`μ(·, t_{k+1}) - μ(·, t_k)` is `(t_k - t_{k+1})(f - f(x_{k+1}))` up to a constant
(`IsHighOrderTargetRun.target_drop_of_innerTest`). With the margin argument of the generic loop
this bounds those calls, and Phase 2 terminates within an explicit bound without a bad-iteration
parameter (`IsHighOrderTargetRun.complexity_of_innerTest`). The same holds for any merit contract
when every case-(b) call passes (14.3.19) (`HighOrderTargetSeq.IsCertified`,
`IsHighOrderTargetRun.complexity_of_certified`).

## Main definitions

* `Constrained.goodBound`, `Constrained.goodDecr`: the bound `κ^S (1 - θ) M` of (14.3.71) and the
  residual decrease of a counted inner iteration;
* `Constrained.HighOrderTargetSeq.IsMeritContract`: the merit-decrease contract for an exemption
  test; `IsEndCritContract`, `IsInnerTestContract`: its two instances;
* `Constrained.HighOrderTargetSeq.IsCertified`: every case-(b) call passes (14.3.19), with radii
  bounded below.

## Main results

* `Constrained.HighOrderTargetSeq.IsMeritContract.toContract`: the merit contract as a contract of
  the generic outer loop;
* `Constrained.IsHighOrderTargetRun.complexity`: Theorem 14.3.9 (Phase 2) with the number of bad
  outer iterations as a parameter;
* `Constrained.IsHighOrderTargetRun.target_drop_of_innerTest`,
  `Constrained.IsHighOrderTargetRun.card_kb_innerTest_le`: the target-drop margin argument;
* `Constrained.IsHighOrderTargetRun.complexity_of_certified`,
  `Constrained.IsHighOrderTargetRun.complexity_of_certified_margin`: Phase 2 under the
  certificate, for `β < θ` and for `β ≤ θ`;
* `Constrained.IsHighOrderTargetRun.complexity_of_innerTest`: Phase 2 under the contract keyed
  on (14.3.19), for `β ≤ θ`, without a bad-iteration parameter;
* `Constrained.HighOrderTargetSeq.IsEndCritContract.toInnerTestContract`,
  `Constrained.HighOrderTargetSeq.IsInnerTestContract.toEndCritContract`: the relation between
  the two contracts;
* `Constrained.IsHighOrderTargetRun.exists_const_order_of_innerTest` and its variants: with
  constants fixed before the tolerances, Phase 2 takes `O(O)` evaluations for every `O`
  dominating `ε₀^{-1}`, the terms `ε₀^{1-π_j} ε_j^{-π_j}` and the bad-iteration terms
  `(ε₀ ε_j ρ'_j^{j-1})^{-1}`.

## Implementation notes

All counting is done on the residual-decrease contract of the generic outer loop
(`Constrained.TargetFollowingSeq.IsInnerContract`), through
`Constrained.HighOrderTargetSeq.IsMeritContract.toContract` and
`Constrained.sub_ge_of_merit_decrease`; the merit contract is parametrized by the exemption test,
so the two exemptions share one structure (`IsEndCritContract` is a reducible abbreviation of it,
`IsInnerTestContract` extends it, for the exemption by (14.3.19), with the radius bound).

The smoothness of `f` and `c` is assumed only at the points of `X` (`ContDiffAt` there), and
f.B.Fb as `f_low ≤ f ≤ f_up` on the points of `X` with `‖c‖ ≤ ε₀`.
-/

open Finset
open scoped Nat

namespace Constrained

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]

/-! ### Constants -/

/-- The bound `G = κ^S (1 - θ) M` of (14.3.71) of [cartis2022evaluation] on the counted inner
iterations of a block, with `κ^S = κ_decr⁻¹ (βθ)^{-π_max}` and `M ≥ max_l ε₀^{2-π_l} ε_l^{-π_l}`. -/
noncomputable def goodBound (κdecr β θ πmax M : ℝ) : ℝ :=
  κdecr⁻¹ * (β * θ) ^ (-πmax) * (1 - θ) * M

/-- The residual decrease `κ_decr (βθ)^{π_max} ε₀ / M` of a counted inner iteration under the
merit contract (`goodBound = (1 - θ)ε₀ / goodDecr`). -/
noncomputable def goodDecr (κdecr β θ πmax M ε₀ : ℝ) : ℝ := κdecr * (β * θ) ^ πmax * ε₀ / M

section Constants

variable {κdecr β θ πmax M ε₀ : ℝ}

theorem goodDecr_pos (hκ : 0 < κdecr) (hβ : 0 < β) (hθ : 0 < θ) (hM : 0 < M) (hε₀ : 0 < ε₀) :
    0 < goodDecr κdecr β θ πmax M ε₀ := by
  unfold goodDecr; positivity

theorem goodBound_eq (hκ : 0 < κdecr) (hβ : 0 < β) (hθ : 0 < θ) (hM : 0 < M) (hε₀ : 0 < ε₀) :
    goodBound κdecr β θ πmax M = (1 - θ) * ε₀ / goodDecr κdecr β θ πmax M ε₀ := by
  unfold goodBound goodDecr
  rw [Real.rpow_neg (by positivity)]
  have : 0 < (β * θ) ^ πmax := by positivity
  field_simp

end Constants

/-! ### Contracts of the inner method -/

namespace HighOrderTargetSeq

/-- **The merit-decrease contract of the inner method** for the exemption test `exempt`
([cartis2022evaluation], Lemmas 14.2.2–14.2.3 for `μ(·, t_k)`, with constants independent of
`t_k`): for every outer iteration `k ≥ 1` reached,
* (count) `e_k ≤ κ_uns |𝒮_k| + κ_unc` ((14.2.13)), `𝒮_k` the successful inner iterations;
* (stay) unsuccessful inner iterations do not move;
* (decrease) every successful inner iteration `i` that is not the last one of a call ending at a
  point passing `exempt k` (`i + 1 < e_k` or `¬ exempt k`), and whose new iterate has residual
  `‖r(x_{k,i+1}, t_k)‖ ≥ θε₀`, decreases `μ(·, t_k)` by at least
  `κ_decr min_l (β ‖r(x_k, t_k)‖ ε_l)^{π_l}` ((14.2.11) for the inner method called with the
  tolerances `β ‖r(x_k, t_k)‖ ε_l`). -/
structure IsMeritContract (f : E → ℝ) (c : E → F) (X : Set E) (q : ℕ) (θ β : ℝ) (ε : ℕ → ℝ)
    (D : HighOrderTargetSeq E) (exempt : ℕ → Prop) (κdecr κuns κunc : ℝ) (π : ℕ → ℝ) :
    Prop where
  count : ∀ k, 1 ≤ k → D.Before f c X q θ ε k → (D.e k : ℝ) ≤ κuns * D.succCount k + κunc
  stay : ∀ k, 1 ≤ k → D.Before f c X q θ ε k → ∀ i < D.e k, ¬ D.succ k i →
    D.xi k (i + 1) = D.xi k i
  decrease : ∀ k, 1 ≤ k → D.Before f c X q θ ε k → ∀ i < D.e k, D.succ k i →
    (i + 1 < D.e k ∨ ¬ exempt k) →
    θ * ε 0 ≤ targetResidual f c (D.t k) (D.xi k (i + 1)) →
    ∃ l ∈ Finset.Icc 1 q,
      κdecr * (β * targetResidual f c (D.t k) (D.x k) * ε l) ^ π l ≤
        targetMerit f c (D.t k) (D.xi k i) - targetMerit f c (D.t k) (D.xi k (i + 1))

/-- **The merit contract exempting the criticality test at the old target** (the decreases used
by the proof of Lemma 14.3.8 of [cartis2022evaluation], "so long as the third termination test in
(14.3.32) has not been satisfied", (B.14.21)): the exemption is (14.3.34) at
`(x_{k+1}, t_k)` with the radii `δ_{k+1}`. -/
abbrev IsEndCritContract (f : E → ℝ) (c : E → F) (X : Set E) (q : ℕ) (θ β : ℝ) (ε : ℕ → ℝ)
    (D : HighOrderTargetSeq E) (κdecr κuns κunc : ℝ) (π : ℕ → ℝ) : Prop :=
  D.IsMeritContract f c X q θ β ε (D.EndCrit f c X q ε) κdecr κuns κunc π

/-- **The merit contract exempting the inner method's own test** (Lemma 14.2.2 of
[cartis2022evaluation] for the inner method on `μ(·, t_k)`, which needs only that the method does
not terminate at `x_{k,i+1}`), with radii bounded below by `ρ`: the exemption is (14.3.19) at
the end of the call (`HighOrderTargetSeq.InnerTest`), and a case-(b) call ending at a point
passing (14.3.19) returns radii `δ_{k+1,j} ≥ ρ_j`. The calls may be cut by any test of
(14.3.32). -/
structure IsInnerTestContract (f : E → ℝ) (c : E → F) (X : Set E) (q : ℕ) (θ β : ℝ)
    (ε : ℕ → ℝ) (D : HighOrderTargetSeq E) (κdecr κuns κunc : ℝ) (π ρ : ℕ → ℝ) : Prop
    extends D.IsMeritContract f c X q θ β ε (D.InnerTest f c X q β ε) κdecr κuns κunc π where
  radius_ge : ∀ k, 1 ≤ k → D.Before f c X q θ ε k → D.IsKb f c θ ε k →
    D.InnerTest f c X q β ε k → ∀ j ∈ Finset.Icc 1 q, ρ j ≤ D.δ (k + 1) j

/-- **Every case-(b) call passes the inner method's test** (14.3.19), with radii bounded below
by `ρ`: at every outer iteration `k ∈ 𝒦_b` reached, `δ_{k+1,j} ≥ ρ_j` and (14.3.19) holds at
`x_{k+1}`. This holds when the inner method is interrupted only by the first test of (14.3.32):
a call ending in `𝒦_b` has `‖r(x_{k+1}, t_k)‖ ≥ θε₀`, so the method has terminated. -/
structure IsCertified (f : E → ℝ) (c : E → F) (X : Set E) (q : ℕ) (θ β : ℝ) (ε : ℕ → ℝ)
    (D : HighOrderTargetSeq E) (ρ : ℕ → ℝ) : Prop where
  radius_ge : ∀ k, 1 ≤ k → D.Before f c X q θ ε k → D.IsKb f c θ ε k →
    ∀ j ∈ Finset.Icc 1 q, ρ j ≤ D.δ (k + 1) j
  cert : ∀ k, 1 ≤ k → D.Before f c X q θ ε k → D.IsKb f c θ ε k → D.InnerTest f c X q β ε k

variable {f : E → ℝ} {c : E → F} {X : Set E} {q : ℕ} {θ β : ℝ} {ε : ℕ → ℝ}
  {D : HighOrderTargetSeq E} {κdecr κuns κunc : ℝ} {π ρ ρ' : ℕ → ℝ}

/-- The contract keyed on (14.3.19) with radii `ρ` gives it with any smaller radii. -/
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

/-- An inner iteration with the merit decrease of the contract lowers the residual
`‖r(·, t_k)‖` by at least `goodDecr` (`Constrained.sub_ge_of_merit_decrease`). -/
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

/-- **The merit contract is a contract of the generic outer loop**
(`Constrained.TargetFollowingSeq.IsInnerContract`), with the residual decrease `goodDecr` and the
same exemption test. -/
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

theorem goodDecr_pos (h : IsHighOrderTargetRun f c X q θ β ε x₁ D) (hκ : 0 < κdecr)
    (hM0 : 0 < M) : 0 < goodDecr κdecr β θ πmax M (ε 0) :=
  Constrained.goodDecr_pos hκ h.β_pos h.θ_pos hM0 h.ε₀_pos

theorem goodBound_eq (h : IsHighOrderTargetRun f c X q θ β ε x₁ D) (hκ : 0 < κdecr)
    (hM0 : 0 < M) :
    goodBound κdecr β θ πmax M = (1 - θ) * ε 0 / goodDecr κdecr β θ πmax M (ε 0) :=
  Constrained.goodBound_eq hκ h.β_pos h.θ_pos hM0 h.ε₀_pos

/-- **Phase 2 of a high-order target-following run, with the bad outer iterations as a
parameter** (cf. [cartis2022evaluation], Theorem 14.3.9 for Phase 2). Let the inner calls
satisfy the merit contract for an exemption test `exempt` (`κ_decr > 0`, `κ_uns ≥ 0`,
`0 ≤ π_l ≤ π_max`, `M > 0` bounding `ε₀^{2-π_l} ε_l^{-π_l}` for `l ∈ [1 : q]`), and assume f.B.Fb
(`f_low ≤ f ≤ f_up` on the points of `X` with `‖c‖ ≤ ε₀`); write
`N_a = (f_up - f_low + 1)/((1 - θ)ε₀)` and `G = goodBound κ_decr β θ π_max M`. Then
(i) every outer iteration `K ≥ 1` reached satisfies `K ≤ (N_a + 1)(G + 1) + n_bad(K)`, `n_bad(K)`
the number of bad outer iterations in `[1, K)`;
(ii) if `n_bad` is bounded by `B`, Phase 2 terminates at some `k_ε ≤ (N_a + 1)(G + 1) + B`;
(iii) if Phase 2 terminates at `k_ε`, it uses at most `1 + G (N_a + 1) + k_ε` derivative
evaluations and at most `1 + κ_uns (G (N_a + 1) + k_ε) + κ_unc k_ε` evaluations of `(f, c)`. -/
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

/-- **Phase 2 given a bound on the bad outer iterations** (as `complexity`): if
`n_bad(K) ≤ N_b` at every outer iteration `K ≥ 1` reached, then every such `K` satisfies
`K ≤ (N_a + 1)(G + 1) + N_b`, and Phase 2 terminates at some `k_ε ≤ (N_a + 1)(G + 1) + N_b`,
using at most `1 + G (N_a + 1) + k_ε` derivative evaluations and
`1 + κ_uns (G (N_a + 1) + k_ε) + κ_unc k_ε` evaluations of `(f, c)`. -/
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

/-- The Taylor jets of `μ(·, t)` and `μ(·, t')` at `x` differ by `(t' - t) ∇^i f(x)` at the orders
`i ≥ 1` (`Constrained.iteratedFDeriv_targetMerit_eq_sub`): if `‖∇^i f(x)‖ ≤ B_f` for
`i ∈ [1 : q]`, they are `|t - t'| B_f`-close. -/
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

/-- From a strict bound `A_j < 2 B_f d` at some order `j` with `2 B_f τ ≤ A_j` at every order and
`A_j ≥ 0`, `d > 0`: `τ ≤ d`. -/
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

/-- **A case-(b) outer iteration passing the inner method's test lowers the target, with an
explicit margin.** Let `k ∈ 𝒦_b` be an outer iteration that does not terminate Phase 2, whose
new iterate passes (14.3.19) (`HighOrderTargetSeq.InnerTest` at `k`) with radii
`δ_{k+1,j} ≥ ρ_j ≥ 0`, with `f`, `c` of class `C^q` at the points of `X` and `‖∇^i f‖ ≤ B_f`
(`i ∈ [1 : q]`) at the points of `X` with `‖c‖ ≤ ε₀`. If
`0 ≤ m ≤ ‖r(x_{k+1}, t_k)‖ - β ‖r(x_k, t_k)‖` (the gap between the tolerance
`ε_j ‖r(x_{k+1}, t_{k+1})‖` of (14.3.34), which fails at the new target, and the tolerance
`β ‖r(x_k, t_k)‖ ε_j` of (14.3.19), which holds at the old one), then some order `j ∈ [1 : q]` has
`m ε_j ρ_j^{j-1}/j! < 2 B_f (t_k - t_{k+1})`. -/
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

/-- **A case-(b) outer iteration lowers the target under the certificate** (`IsCertified`, radii
`δ_{k+1,j} ≥ ρ_j ≥ 0`): since (14.3.34) fails at `(x_{k+1}, t_{k+1})` while (14.3.19), with the
smaller tolerance `β ‖r(x_k, t_k)‖ ε_j ≤ βε₀ε_j`, holds at `(x_{k+1}, t_k)`, some order
`j ∈ [1 : q]` has `(θ - β) ε₀ ε_j ρ_j^{j-1}/j! < 2 B_f (t_k - t_{k+1})`. -/
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

/-- **The number of case-(b) outer iterations under the certificate, for `β < θ`.** Under the
assumptions of `target_drop_of_certified` and f.B.Fb, if `τ > 0` satisfies
`2 B_f τ ≤ (θ - β) ε₀ ε_j ρ_j^{j-1}/j!` for every `j ∈ [1 : q]`, then every case-(b) iteration
before termination lowers the target by more than `τ`, and, the targets staying in
`[f_low - 1, f_up]`, `|𝒦_b ∩ [1, K)| ≤ (f_up - f_low + 1)/τ`. -/
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
/-- **The case-(b) outer iterations passing the inner method's test, for every `β ≤ θ`**
(including `β = θ`), when those calls return radii `δ_{k+1,j} ≥ ρ_j ≥ 0`, under the smoothness
assumptions of `target_drop_of_innerTest` and f.B.Fb. Write `η = θ(1 - θ)ε₀/(1 + θ)`
(`Constrained.kbMargin`) and let `τ > 0` satisfy `2 B_f τ ≤ η ε_j ρ_j^{j-1}/j!` for
`j ∈ [1 : q]`. Then their number in `[1, K)` is at most
`|𝒦_a ∩ [1, K)| + 1 + (f_up - f_low + 1)/τ`: those with margin
`‖r(x_{k+1}, t_k)‖ - β ‖r(x_k, t_k)‖ ≥ η` lower the target by more than `τ`
(`target_drop_of_innerTest`), and between two consecutive elements of `𝒦_a` there is at most one
other one (`Constrained.IsTargetFollowingRun.card_kb_le_of_margin`). -/
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

/-- **The number of case-(b) outer iterations under the certificate, for every `β ≤ θ`**: under
the assumptions of `card_kb_innerTest_le` with the radii of `IsCertified`,
`|𝒦_b ∩ [1, K)| ≤ |𝒦_a ∩ [1, K)| + 1 + (f_up - f_low + 1)/τ` (every case-(b) call passes the
inner method's test). -/
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
  unfold HighOrderTargetSeq.kbCount
  have e : (Finset.Ico 1 K).filter (D.IsKb f c θ ε) = (Finset.Ico 1 K).filter
      (fun k => D.IsKb f c θ ε k ∧ D.InnerTest f c X q β ε k) := by
    refine Finset.filter_congr fun k hk => ⟨fun hb => ⟨hb, ?_⟩, fun h' => h'.1⟩
    rw [Finset.mem_Ico] at hk
    exact hcert.cert k hk.1 (hK.mono hk.2.le) hb
  rw [e]

/-- **Phase 2 under the certificate, for `β < θ`, without a bad-iteration parameter.** Let the
inner calls satisfy a merit contract (any exemption test) and let every case-(b) call carry the
certificate `IsCertified` with radii `ρ_j ≥ 0`; under the assumptions of `complexity`, with `f`,
`c` of class `C^q` at the points of `X`, `‖∇^i f‖ ≤ B_f` (`i ∈ [1 : q]`) at the points of `X`
with `‖c‖ ≤ ε₀`, and `τ > 0` with `2 B_f τ ≤ (θ - β) ε₀ ε_j ρ_j^{j-1}/j!` (`j ∈ [1 : q]`), write
`N_b = (f_up - f_low + 1)/τ`: every outer iteration `K ≥ 1` reached satisfies
`K ≤ (N_a + 1)(G + 1) + N_b`, and Phase 2 terminates at some `k_ε ≤ (N_a + 1)(G + 1) + N_b`,
using at most `1 + G (N_a + 1) + k_ε` derivative evaluations and
`1 + κ_uns (G (N_a + 1) + k_ε) + κ_unc k_ε` evaluations of `(f, c)`. -/
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

/-- **Phase 2 under the certificate, for every `β ≤ θ`, without a bad-iteration parameter**: as
`complexity_of_certified`, with `τ > 0` satisfying `2 B_f τ ≤ η ε_j ρ_j^{j-1}/j!`
(`η = kbMargin θ ε₀`) in place of the margin `(θ - β)ε₀`, and
`N_b = N_a + 1 + (f_up - f_low + 1)/τ` (`kbCount_le_of_certified_margin` and `kaCount_le`). -/
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

/-- **From the contract exempting (14.3.34) to the one keyed on (14.3.19)**: if every call ending
with `‖r(x_{k+1}, t_k)‖ ≥ θε₀` ends at a point passing (14.3.19) with radii `δ_{k+1,j} ≥ ρ_j`
(calls are interrupted only by the first test of (14.3.32)), the contract exempting (14.3.34)
gives the contract keyed on (14.3.19). -/
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

/-- **The contract keyed on (14.3.19) gives the contract exempting (14.3.34)**: since `β ≤ θ` and
`‖r(x_k, t_k)‖ ≤ ε₀`, (14.3.19) at a point with `‖r(x_{k+1}, t_k)‖ ≥ θε₀` implies (14.3.34) there,
so every step exempted by the latter is exempted by the former. -/
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
/-- **Phase 2 under the contract keyed on (14.3.19), given a bound `N_b` on the case-(b)
iterations passing (14.3.19)**: with `N_a = (f_up - f_low + 1)/((1 - θ)ε₀)` and
`G = goodBound κ_decr β θ π_max M`, every outer iteration `K ≥ 1` reached has
`K ≤ (N_a + 1)(G + 1) + N_b`, and Phase 2 terminates at some `k_ε ≤ (N_a + 1)(G + 1) + N_b`,
using at most `1 + G (N_a + 1) + k_ε` derivative evaluations and
`1 + κ_uns (G (N_a + 1) + k_ε) + κ_unc k_ε` evaluations of `(f, c)` (the bad outer iterations
for the exemption by (14.3.19) end at points passing it,
`Constrained.IsTargetFollowingRun.badCount_le_card`). -/
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

/-- **Phase 2 under the contract keyed on (14.3.19): termination within an explicit bound
without a bad-iteration parameter, for every `β ≤ θ`** (cf. Theorem 14.3.9 of
[cartis2022evaluation] for Phase 2; the calls may be cut by any test of (14.3.32)). Assume
`κ_decr > 0`, `κ_uns ≥ 0`, `0 ≤ π_l ≤ π_max`, `M > 0` bounding `ε₀^{2-π_l} ε_l^{-π_l}`, f.B.Fb,
radii `ρ_j ≥ 0`, `f`, `c` of class `C^q` at the points of `X` with `‖∇^i f‖ ≤ B_f`
(`i ∈ [1 : q]`) at the points of `X` with `‖c‖ ≤ ε₀`, and `τ > 0` with
`2 B_f τ ≤ η ε_j ρ_j^{j-1}/j!` (`η = kbMargin θ ε₀`). Write
`N_a = (f_up - f_low + 1)/((1 - θ)ε₀)`, `G = goodBound κ_decr β θ π_max M` and
`N_b = N_a + 1 + (f_up - f_low + 1)/τ`. Every case-(b) iteration either ends at a point passing
(14.3.19) (at most `N_b` of them, `card_kb_innerTest_le`) or its call has a counted successful
iteration (its last one; these number at most `G (N_a + 1)` in total). Hence every outer iteration
`K ≥ 1` reached satisfies `K ≤ (N_a + 1)(G + 1) + N_b`, and Phase 2 terminates at some
`k_ε ≤ (N_a + 1)(G + 1) + N_b`, using at most `1 + G (N_a + 1) + k_ε` derivative evaluations and
`1 + κ_uns (G (N_a + 1) + k_ε) + κ_unc k_ε` evaluations of `(f, c)`. -/
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
/-- **Phase 2 within an order bound, given a bound on the case-(b) iterations passing (14.3.19)**
([cartis2022evaluation], Lemma 14.3.8 and Theorem 14.3.9, Phase 2): there are constants
`C_F, C_D, C_K ≥ 0` such that for every `κ_unc ≥ 0` and every run satisfying the contract keyed on
(14.3.19) with the constants `κ_decr`, `κ_uns`, `κ_unc` and any radii, if those iterations number
at most `B_b O` in every `[1, K)` reached, then Phase 2 terminates at some `k_ε ≤ C_K O` using at
most `C_F O + κ_unc k_ε` evaluations of `(f, c)` and `C_D O` derivative evaluations
(`complexity_of_innerTest_card`). -/
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
/-- **Phase 2 within an order bound, with the count constant paid per outer iteration**
([cartis2022evaluation], Lemma 14.3.8 and Theorem 14.3.9, Phase 2): there are constants
`C_F, C_D, C_K ≥ 0` such that for every `κ_unc ≥ 0` and every run satisfying the contract keyed on
(14.3.19) with the constants `κ_decr`, `κ_uns`, `κ_unc` and radii `ρ_j = κ_ρ ρ'_j` (`ρ'_j > 0`),
under the assumptions of `complexity_of_innerTest` with `f_up - f_low + 1 ≤ A`, and for every `O`
with `ε₀^{-1} ≤ O`, `ε₀^{1-π_l} ε_l^{-π_l} ≤ O` and `(ε₀ ε_j ρ'_j^{j-1})^{-1} ≤ b O`, Phase 2
terminates at some `k_ε ≤ C_K O` using at most `C_F O + κ_unc k_ε` evaluations of `(f, c)` and
`C_D O` derivative evaluations. -/
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
/-- **Phase 2 within an order bound, with a count constant chosen after the tolerances** (as
`exists_const_order_of_innerTest`, with `κ_unc` allowed to depend on `ε`): there are constants
`C_F, C_U, C_D ≥ 0` such that, under the assumptions of `exists_const_order_of_innerTest_calls`,
Phase 2 terminates using at most `(C_F + C_U κ_unc) O` evaluations of `(f, c)` and `C_D O`
derivative evaluations (inner calls restarting from a fixed trust-region radius have a `κ_unc`
containing `|log(ε₀ ε_min)|`). -/
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
/-- **Phase 2 within an order bound, for every run satisfying the contract keyed on (14.3.19)**
([cartis2022evaluation], Theorem 14.3.9, Phase 2). For constants `κ_decr > 0`, `κ_uns, κ_unc ≥ 0`,
`κ_ρ > 0`, `π_max`, `B_f > 0`, `A ≥ 0`, `b ≥ 0` and `θ ∈ (0, 1)`, `β > 0`, there are constants
`C_F`, `C_D` such that for all tolerances `ε` and every run satisfying the contract keyed on
(14.3.19) with these constants, exponents `0 ≤ π_l ≤ π_max` and radii `ρ_j = κ_ρ ρ'_j`
(`ρ'_j > 0`), under f.B.Fb with `f_up - f_low + 1 ≤ A`, `f`, `c` of class `C^q` at the points of
`X` with `‖∇^i f‖ ≤ B_f` at the points of `X` with `‖c‖ ≤ ε₀`, and for every `O` with
`ε₀^{-1} ≤ O`, `ε₀^{1-π_l} ε_l^{-π_l} ≤ O` and `(ε₀ ε_j ρ'_j^{j-1})^{-1} ≤ b O` (the order of the
bad outer iterations), Phase 2 terminates at some `k_ε` using at most `C_F O` evaluations of
`(f, c)` and `C_D O` derivative evaluations (`complexity_of_innerTest`). -/
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
