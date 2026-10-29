import Numlib.Optimization.Constrained.TwoPhase.Run

/-!
# Evaluation complexity of the outer loop of two-phase target-following methods

For a run of Phase 2 of a two-phase target-following method (`Constrained.IsTargetFollowingRun`)
whose inner calls satisfy a contract (`Constrained.TargetFollowingSeq.IsInnerContract`), this file
bounds the number of outer iterations and the evaluation counts ([cartis2022evaluation],
Lemmas 7.2.6 and 14.3.8, Theorems 7.2.7 and 14.3.9, corrected).

The argument: an inner iteration is *good* if it is successful, its new residual is at least
`θε₀`, and it is not the last iteration of a call that ends at a point passing the *exemption
test* `exempt k` (`TargetFollowingSeq.IsGood`). The contract guarantees that good iterations lower
the residual `‖r(·, t_k)‖` by at least `δ`; telescoping the residual above `θε₀` over the blocks of
outer iterations between consecutive case-(a) iterations bounds their total number by
`(1 - θ)ε₀/δ · (|𝒦_a| + 1)`. Every successful inner iteration but the last one of its call is
good, every case-(b) iteration whose call does not end at an exempt point contains a good
iteration, and `|𝒦_a| ≤ N_a = (f_up - f_low + 1)/((1 - θ)ε₀)` (Lemma 7.2.4). The remaining
*bad* outer iterations (case (b), no good iteration; their calls end at exempt points) are not
bounded by the book's argument; their number is a parameter of the complexity theorem. A
margin argument bounds them when the exemption test at the old target is incompatible with the
failure of the criticality test at the new one unless the target drops by a fixed amount
(`IsTargetFollowingRun.card_kb_le_of_margin`).

## Main definitions

* `Constrained.TargetFollowingSeq.succCount`, `funEvals`, `derivEvals`, `kaCount`, `kbCount`:
  the counts of Phase 2;
* `Constrained.TargetFollowingSeq.IsGood`, `goodCount`, `IsBad`, `badCount`: good inner iterations
  and bad outer iterations for an exemption test;
* `Constrained.TargetFollowingSeq.IsInnerContract`: the contract of the inner method;
* `Constrained.kbMargin`: the margin `θ(1 - θ)ε₀/(1 + θ)`.

## Main results

* `Constrained.TargetFollowingSeq.IsInnerContract.sum_goodCount_le`: the good inner iterations of
  `[1, K]` number at most `(1 - θ)ε₀/δ · (|𝒦_a ∩ [1, K)| + 1)` ((7.2.39), (14.3.71));
* `Constrained.TargetFollowingSeq.le_counts`: `K ≤ |𝒦_a| + ∑_k |good_k| + n_bad + 1`;
* `Constrained.TargetFollowingSeq.IsInnerContract.complexity`: the corrected Theorems 7.2.7 and
  14.3.9 (Phase 2) with the number of bad iterations as a parameter;
* `Constrained.TargetFollowingSeq.IsInnerContract.complexity_of_badCount_le`: termination and
  evaluation bounds given a bound on the bad iterations;
* `Constrained.IsTargetFollowingRun.exempt_of_isBad`: if unsuccessful inner iterations do not
  move, the call of a bad outer iteration ends at an exempt point;
* `Constrained.IsTargetFollowingRun.kbCount_le_of_drop`, `card_kb_le_of_drop`: bounds on the
  case-(b) iterations that lower the target by a fixed amount;
  `Constrained.IsTargetFollowingRun.card_kb_le_of_margin`: the same when only the iterations with
  a large margin lower the target, one small-margin iteration per block being allowed.
-/

open Finset

namespace Constrained

variable {E F : Type*} [NormedAddCommGroup F]

/-- The margin `η = θ(1 - θ)ε₀/(1 + θ)` of the bound on the case-(b) iterations
(`Constrained.IsTargetFollowingRun.card_kb_le_of_margin`). -/
noncomputable def kbMargin (θ ε₀ : ℝ) : ℝ := θ * (1 - θ) * ε₀ / (1 + θ)

theorem kbMargin_nonneg {θ ε₀ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hε₀ : 0 ≤ ε₀) :
    0 ≤ kbMargin θ ε₀ := by
  unfold kbMargin
  have : 0 ≤ 1 - θ := by linarith
  positivity

namespace TargetFollowingSeq

variable (S : TargetFollowingSeq E)

section Counts

open Classical in
/-- The number of successful iterations (`succ k i`) of the `k`-th inner call. -/
noncomputable def succCount (succ : ℕ → ℕ → Prop) (k : ℕ) : ℕ :=
  ((range (S.e k)).filter (succ k)).card

/-- The number of function evaluations of Phase 2 up to outer iteration `k`:
`1 + ∑_{j ∈ [1, k]} e_j` (one at `x₁` and one per inner iteration). -/
noncomputable def funEvals (k : ℕ) : ℕ := 1 + ∑ j ∈ Icc 1 k, S.e j

/-- The number of derivative evaluations of Phase 2 up to outer iteration `k`: one at `x₁` and
one per successful inner iteration. -/
noncomputable def derivEvals (succ : ℕ → ℕ → Prop) (k : ℕ) : ℕ :=
  1 + ∑ j ∈ Icc 1 k, S.succCount succ j

open Classical in
/-- The number of case-(a) iterations among the outer iterations `[1, K)`. -/
noncomputable def kaCount (K : ℕ) : ℕ := ((Ico 1 K).filter S.Ka).card

open Classical in
/-- The number of case-(b) iterations among the outer iterations `[1, K)`. -/
noncomputable def kbCount (K : ℕ) : ℕ := ((Ico 1 K).filter S.Kb).card

variable (f : E → ℝ) (c : E → F) (θ ε₀ : ℝ) (succ : ℕ → ℕ → Prop) (exempt : ℕ → Prop)

/-- A *good* inner iteration `(k, i)` for the exemption test `exempt` (the iterations counted by
the proofs of Lemmas 7.2.6 and 14.3.8 of [cartis2022evaluation]): it is successful, it is not the
last iteration of a call whose output passes `exempt k`, and its new iterate has residual
`‖r(x_{k,i+1}, t_k)‖ ≥ θε₀`. -/
def IsGood (k i : ℕ) : Prop :=
  i < S.e k ∧ succ k i ∧ (i + 1 < S.e k ∨ ¬ exempt k) ∧
    θ * ε₀ ≤ targetResidual f c (S.t k) (S.xi k (i + 1))

open Classical in
/-- The number of good iterations of the `k`-th inner call. -/
noncomputable def goodCount (k : ℕ) : ℕ :=
  ((range (S.e k)).filter (S.IsGood f c θ ε₀ succ exempt k)).card

/-- A *bad* outer iteration: case (b) and no good iteration in its call. -/
def IsBad (k : ℕ) : Prop := S.Kb k ∧ S.goodCount f c θ ε₀ succ exempt k = 0

open Classical in
/-- The number of bad outer iterations among `[1, K)`. -/
noncomputable def badCount (K : ℕ) : ℕ :=
  ((Ico 1 K).filter (S.IsBad f c θ ε₀ succ exempt)).card

/-- **The contract of the inner method** of Phase 2, for the successful iterations `succ`, the
exemption test `exempt`, a residual decrease `δ` and per-call constants `κ_uns`, `κ_unc`: for
every outer iteration `k ≥ 1` reached,
* (count) `e_k ≤ κ_uns |𝒮_k| + κ_unc` (Lemma 2.4.1 or (14.2.13) of [cartis2022evaluation]);
* (stay) unsuccessful inner iterations do not move;
* (decrease) every good inner iteration lowers the residual `‖r(·, t_k)‖` by at least `δ`
  (from the merit decreases of Lemmas 6.2.4 or 14.2.2, via `Constrained.sub_ge_of_residual_decrease`
  or `Constrained.sub_ge_of_merit_decrease`). -/
structure IsInnerContract (δ κuns κunc : ℝ) : Prop where
  count : ∀ k, 1 ≤ k → S.Before k → (S.e k : ℝ) ≤ κuns * S.succCount succ k + κunc
  stay : ∀ k, 1 ≤ k → S.Before k → ∀ i < S.e k, ¬ succ k i → S.xi k (i + 1) = S.xi k i
  decrease : ∀ k, 1 ≤ k → S.Before k → ∀ i, S.IsGood f c θ ε₀ succ exempt k i →
    δ ≤ targetResidual f c (S.t k) (S.xi k i) - targetResidual f c (S.t k) (S.xi k (i + 1))

variable {S f c θ ε₀ succ exempt}

theorem isGood_iff {k i : ℕ} :
    S.IsGood f c θ ε₀ succ exempt k i ↔ i < S.e k ∧ succ k i ∧ (i + 1 < S.e k ∨ ¬ exempt k) ∧
      θ * ε₀ ≤ targetResidual f c (S.t k) (S.xi k (i + 1)) :=
  Iff.rfl

theorem isBad_iff {k : ℕ} :
    S.IsBad f c θ ε₀ succ exempt k ↔ S.Kb k ∧ S.goodCount f c θ ε₀ succ exempt k = 0 :=
  Iff.rfl

theorem goodCount_eq_card_filter (k : ℕ) [DecidablePred (S.IsGood f c θ ε₀ succ exempt k)] :
    S.goodCount f c θ ε₀ succ exempt k =
      ((range (S.e k)).filter (S.IsGood f c θ ε₀ succ exempt k)).card := by
  unfold goodCount; congr

theorem goodCount_eq_zero_iff {k : ℕ} :
    S.goodCount f c θ ε₀ succ exempt k = 0 ↔ ∀ i < S.e k, ¬ S.IsGood f c θ ε₀ succ exempt k i := by
  classical
  rw [goodCount_eq_card_filter, card_eq_zero, filter_eq_empty_iff]
  exact ⟨fun h i hi => h (mem_range.2 hi), fun h i hi => h i (mem_range.1 hi)⟩

theorem badCount_eq_card_filter (K : ℕ) [DecidablePred (S.IsBad f c θ ε₀ succ exempt)] :
    S.badCount f c θ ε₀ succ exempt K = ((Ico 1 K).filter (S.IsBad f c θ ε₀ succ exempt)).card := by
  unfold badCount; congr

theorem derivEvals_eq (k : ℕ) :
    (S.derivEvals succ k : ℝ) = 1 + ∑ j ∈ Icc 1 k, (S.succCount succ j : ℝ) := by
  unfold derivEvals
  push_cast
  rfl

/-- A bad outer iteration is in case (b): `n_bad(K) ≤ |𝒦_b ∩ [1, K)|`. -/
theorem badCount_le_kbCount (K : ℕ) : S.badCount f c θ ε₀ succ exempt K ≤ S.kbCount K := by
  classical
  unfold badCount kbCount
  exact card_le_card fun k hk => by
    rw [mem_filter] at hk ⊢
    exact ⟨hk.1, hk.2.1⟩

/-- **Counting the outer iterations**: each outer iteration `k ∈ [1, K)` before termination is in
case (a), bad, or contains a good inner iteration, so
`K ≤ |𝒦_a ∩ [1, K)| + ∑_{k ∈ [1, K]} |good_k| + n_bad(K) + 1`. -/
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

/-- Every successful inner iteration except possibly the last one of its call is good:
`|𝒮_k| ≤ |good_k| + 1`. -/
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

/-- `∑_{k ∈ [1, K]} |𝒮_k| ≤ ∑_{k ∈ [1, K]} |good_k| + K`. -/
theorem sum_succCount_le (h : IsTargetFollowingRun f c θ ε₀ X x₁ S) {K : ℕ} (hK : S.Before K) :
    (∑ k ∈ Icc 1 K, (S.succCount succ k : ℝ)) ≤
      ∑ k ∈ Icc 1 K, (S.goodCount f c θ ε₀ succ exempt k : ℝ) + K := by
  have : ∑ k ∈ Icc 1 K, S.succCount succ k ≤
      ∑ k ∈ Icc 1 K, (S.goodCount f c θ ε₀ succ exempt k + 1) :=
    sum_le_sum fun k hk => h.succCount_le (mem_Icc.1 hk).1 (hK.mono (mem_Icc.1 hk).2)
  rw [sum_add_distrib, sum_const, Nat.card_Icc, smul_eq_mul, mul_one, Nat.add_sub_cancel] at this
  exact_mod_cast this

/-- **Lemma 7.2.4** for a run ([cartis2022evaluation]): under f.B.Fb (`f_low ≤ f ≤ f_up` on the
points of `X` with `‖c‖ ≤ ε₀`), `|𝒦_a ∩ [1, K)| ≤ (f_up - f_low + 1)/((1 - θ)ε₀)`. -/
theorem kaCount_le (h : IsTargetFollowingRun f c θ ε₀ X x₁ S) {flow fup : ℝ}
    (hB : ∀ z ∈ X, ‖c z‖ ≤ ε₀ → flow ≤ f z ∧ f z ≤ fup) {K : ℕ} (hK1 : 1 ≤ K)
    (hK : S.Before K) : (S.kaCount K : ℝ) ≤ (fup - flow + 1) / ((1 - θ) * ε₀) := by
  classical
  have := (h.isTargetSequence hK).card_Ka_le h.θ_pos.le h.θ_lt_one h.ε₀_pos h.ε₀_le_one hK1
    (fun k hk1 hkK => h.x_mem k hk1 (hK.mono hkK)) hB
  unfold kaCount
  convert this

/-- `f_low ≤ f(x₁) ≤ f_up` under f.B.Fb, so `f_up - f_low + 1 > 0`. -/
theorem sub_add_one_pos (h : IsTargetFollowingRun f c θ ε₀ X x₁ S) {flow fup : ℝ}
    (hB : ∀ z ∈ X, ‖c z‖ ≤ ε₀ → flow ≤ f z ∧ f z ≤ fup) : 0 < fup - flow + 1 := by
  have := hB x₁ h.mem_one (h.norm_one_le.trans (mul_le_of_le_one_left h.ε₀_pos.le h.θ_lt_one.le))
  linarith [this.1, this.2]

/-- **Telescoping the targets of a run**: if every outer iteration of `S' ⊆ [1, K)` lowers the
target by at least `τ`, then `|S'| τ ≤ f_up - f_low + 1` under f.B.Fb. -/
theorem card_mul_le_of_target_drop (h : IsTargetFollowingRun f c θ ε₀ X x₁ S) {flow fup : ℝ}
    (hB : ∀ z ∈ X, ‖c z‖ ≤ ε₀ → flow ≤ f z ∧ f z ≤ fup) {K : ℕ} (hK1 : 1 ≤ K)
    (hK : S.Before K) {S' : Finset ℕ} (hS : S' ⊆ Ico 1 K) {τ : ℝ}
    (hτ : ∀ k ∈ S', τ ≤ S.t k - S.t (k + 1)) : S'.card * τ ≤ fup - flow + 1 :=
  (h.isTargetSequence hK).card_mul_le_of_target_drop h.θ_pos.le h.θ_lt_one h.ε₀_pos h.ε₀_le_one
    hK1 (fun k hk1 hkK => h.x_mem k hk1 (hK.mono hkK)) hB hS hτ

open Classical in
/-- **The case-(b) iterations of a class `P` from target drops**: if every case-(b) outer
iteration of `P` before termination lowers the target by at least `τ > 0`, then they number at
most `(f_up - f_low + 1)/τ` in `[1, K)` under f.B.Fb. -/
theorem card_kb_le_of_drop (h : IsTargetFollowingRun f c θ ε₀ X x₁ S) {flow fup : ℝ}
    (hB : ∀ z ∈ X, ‖c z‖ ≤ ε₀ → flow ≤ f z ∧ f z ≤ fup) {P : ℕ → Prop} {τ : ℝ} (hτ0 : 0 < τ)
    (hdrop : ∀ k, 1 ≤ k → S.Before (k + 1) → S.Kb k → P k → τ ≤ S.t k - S.t (k + 1)) {K : ℕ}
    (hK1 : 1 ≤ K) (hK : S.Before K) :
    ((((Ico 1 K).filter (fun k => S.Kb k ∧ P k)).card : ℕ) : ℝ) ≤ (fup - flow + 1) / τ := by
  rw [le_div_iff₀ hτ0]
  refine h.card_mul_le_of_target_drop hB hK1 hK (filter_subset _ _) fun k hk => ?_
  rw [mem_filter, mem_Ico] at hk
  exact hdrop k hk.1.1 (hK.mono hk.1.2) hk.2.1 hk.2.2

/-- **The number of case-(b) iterations from target drops**: if every case-(b) outer iteration
before termination lowers the target by at least `τ > 0`, then
`|𝒦_b ∩ [1, K)| ≤ (f_up - f_low + 1)/τ` under f.B.Fb. -/
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
/-- **The case-(b) iterations of a class `P` with a target-drop guarantee at large margins**
(the margin argument behind the bound on the case-(b) iterations of TPqp-GC). Let `0 ≤ β ≤ θ`
and suppose that every case-(b) iteration `k` of `P` before termination whose margin
`‖r(x_{k+1}, t_k)‖ - β ‖r(x_k, t_k)‖` is at least `η = kbMargin θ ε₀` lowers the target by at
least `τ > 0`. Then the case-(b) iterations of `P` in `[1, K)` number at most
`|𝒦_a ∩ [1, K)| + 1 + (f_up - f_low + 1)/τ`: between consecutive case-(a) iterations at most one
of them has a smaller margin. Indeed, if `k < k'` both have margin `< η` with no case-(a)
iteration in between, then `‖r(x_{k+1}, t_k)‖ < θε₀ + η`, the residual does not increase from
`k + 1` to `k'` (`IsTargetFollowingRun.residual_le_of_forall_kb`), and the margin at `k'` is at
least `θε₀ - θ(θε₀ + η) = η`. -/
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

/-- A case-(b) iteration whose call does not end at an exempt point contains a good inner
iteration: its call moved (`f(x_{k+1}) < t_k ≤ f(x_k)`), and its last successful iteration is
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

/-- The call of a bad outer iteration ends at an exempt point. -/
theorem exempt_of_isBad (h : IsTargetFollowingRun f c θ ε₀ X x₁ S)
    (hstay : ∀ k, 1 ≤ k → S.Before k → ∀ i < S.e k, ¬ succ k i → S.xi k (i + 1) = S.xi k i)
    {k : ℕ} (hk1 : 1 ≤ k) (hk : S.Before k)
    (hbad : S.IsBad f c θ ε₀ succ exempt k) : exempt k := by
  by_contra hne
  have := h.one_le_goodCount hstay hk1 hk hbad.1 hne
  rw [hbad.2] at this
  exact absurd this (by norm_num)

open Classical in
/-- A bad outer iteration is a case-(b) iteration whose call ends at an exempt point:
`n_bad(K) ≤ |{k ∈ [1, K) | k ∈ 𝒦_b, exempt k}|`. -/
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

/-- The good iterations of one call telescope:
`|good_k| δ ≤ max(‖r(x_k, t_k)‖, θε₀) - max(‖r(x_{k+1}, t_k)‖, θε₀)`. -/
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

/-- **The good inner iterations of Phase 2** (the corrected (7.2.39) and (14.3.71) of
[cartis2022evaluation], summed over the blocks of outer iterations between consecutive case-(a)
iterations): for every outer iteration `K ≥ 1` reached, the good inner iterations of `[1, K]`
number at most `(1 - θ)ε₀/δ · (|𝒦_a ∩ [1, K)| + 1)`. -/
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

/-- The total number of inner iterations (function evaluations) from the per-call contract. -/
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

/-- **Evaluation complexity of Phase 2** ([cartis2022evaluation], Theorems 7.2.7 and 14.3.9 for
Phase 2, corrected). Let `S` be a run whose inner calls satisfy the contract with residual
decrease `δ > 0` and `κ_uns ≥ 0`; assume f.B.Fb (`f_low ≤ f ≤ f_up` on the points of `X` with
`‖c‖ ≤ ε₀`), and let `G ≥ (1 - θ)ε₀/δ` and `N_a = (f_up - f_low + 1)/((1 - θ)ε₀)`. Then
(i) every outer iteration `K ≥ 1` reached satisfies `K ≤ (N_a + 1)(G + 1) + n_bad(K)`, `n_bad(K)`
the number of bad outer iterations in `[1, K)`;
(ii) if `n_bad` is bounded by `B`, Phase 2 terminates at some `k_ε ≤ (N_a + 1)(G + 1) + B`;
(iii) if Phase 2 terminates at `k_ε`, it uses at most `1 + G (N_a + 1) + k_ε` derivative
evaluations and at most `1 + κ_uns (G (N_a + 1) + k_ε) + κ_unc k_ε` function evaluations. -/
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

/-- **Evaluation complexity of Phase 2 given a bound on the bad iterations**: under the
assumptions of `complexity`, if `n_bad(K) ≤ N_b` for every outer iteration `K ≥ 1` reached, then
every such `K` satisfies `K ≤ (N_a + 1)(G + 1) + N_b`, and Phase 2 terminates at some
`k_ε ≤ (N_a + 1)(G + 1) + N_b`, using at most `1 + G (N_a + 1) + k_ε` derivative evaluations and
`1 + κ_uns (G (N_a + 1) + k_ε) + κ_unc k_ε` function evaluations. -/
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
