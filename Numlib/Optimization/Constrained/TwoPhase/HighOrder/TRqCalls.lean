import Numlib.Optimization.Constrained.TwoPhase.HighOrder.Complexity
import Numlib.Optimization.Constrained.TargetMeritTaylor
import Numlib.Optimization.ModelBased.HighOrder.TRqCall
import Numlib.Analysis.SpecialFunctions.Log

/-!
# High-order target-following runs with trust-region inner calls

Phase 2 of a high-order target-following method (`Constrained.IsHighOrderTargetRun`,
[cartis2022evaluation], Algorithm 14.3.2) whose `k`-th inner call is a call of the trust-region
method TRq with a feasible set (`Optimization.IsTRqCallOut`) on the merit function `μ(·, t_k)`,
with threshold `ϑ` and tolerances `β ‖r(x_k, t_k)‖ ε_j`, cut at any iteration.

Every such run satisfies the inner-test contract of the inner method
(`Constrained.HighOrderTargetSeq.IsInnerTestContract`) with the exponents `π_j = q + 1` of the
decrease of TRq (Lemma 12.2.4), the `t`-independent constants of the call analysis
(`Optimization.trqCallKappaDecr`, `Optimization.trqKappaUns`), a count constant
`κ_unc⁰ + |log(ε₀ ε_min)|/|log γ₂|` (every call restarts from the radius `Δ₀` while its radii may
shrink to `κ_ρ ε'_min ≥ κ_ρ βθ ε₀ ε_min`) and radii `κ_ρ βθ ε₀ ε_min`. Runs with such calls exist
from every admissible starting point, and the cost of a terminating call of TRq on the
constraint violation `ν = ½ ‖c‖²` is bounded in terms of `|log(ε₀ ε_min)|`.

## Main definitions

* `Constrained.HighOrderTargetSeq.IsTRqCalls`: the inner calls are TRq calls;
* `Constrained.trqCallKappaUnc0`: the `ε`-independent part of the count constant;
* `Constrained.tolLogTerm q ε = |log(ε₀ ε_min)|`.

## Main results

* `Constrained.IsHighOrderTargetRun.call_tol`: the tolerances of the calls;
* `Constrained.IsHighOrderTargetRun.isInnerTestContract_of_isTRqCalls`: the inner-test contract;
* `Constrained.exists_innerCall_isTRqCallOut`: one call from every admissible point;
* `Constrained.exists_isHighOrderTargetRun_isTRqCalls`: runs with TRq calls exist;
* `Constrained.IsTRqOutputCost.cost_le_halfSqNorm`: the cost of a call on `ν` with tolerances
  `β₁ ‖c(y)‖ ε_j`.
-/

open Set
open scoped Nat

namespace Constrained

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]

/-- `a b ≤ 1` for `a ≤ 1` and `b ∈ [0, 1]`. -/
private theorem mul_le_one_of_le_one {a b : ℝ} (ha : a ≤ 1) (hb0 : 0 ≤ b) (hb : b ≤ 1) :
    a * b ≤ 1 :=
  (mul_le_of_le_one_left hb0 ha).trans hb

/-! ### The count constants -/

/-- The `ε`-independent part `κ_uns + (|log Δ₀| + |log κ_ρ| + |log(βθ)|)/|log γ₂|` of the count of
the iterations of one TRq call of Phase 2 (`Optimization.IsTRqCallOut.le_count`); the full count
adds `|log(ε₀ ε_min)|/|log γ₂|` (`tolLogTerm`). -/
noncomputable def trqCallKappaUnc0 (P : Optimization.TRqParams) (L : ℕ → ℝ) (ϑ M : ℝ) (q : ℕ)
    (β θ : ℝ) : ℝ :=
  Optimization.trqKappaUns P + (|Real.log P.Δ₀| +
    |Real.log (Optimization.trqCallKappaRad P L ϑ M q)| + |Real.log (β * θ)|) / |Real.log P.γ₂|

/-- The logarithmic term `|log(ε₀ ε_min)|`, `ε_min = min_{j ∈ [1 : q]} ε_j`. -/
noncomputable def tolLogTerm (q : ℕ) (ε : ℕ → ℝ) : ℝ :=
  |Real.log (ε 0 * Optimization.finMin 1 ε q)|

theorem tolLogTerm_def (q : ℕ) (ε : ℕ → ℝ) :
    tolLogTerm q ε = |Real.log (ε 0 * Optimization.finMin 1 ε q)| := rfl

theorem tolLogTerm_nonneg (q : ℕ) (ε : ℕ → ℝ) : 0 ≤ tolLogTerm q ε := abs_nonneg _

/-- The `ε`-independent part of the count constant is nonnegative. -/
theorem trqCallKappaUnc0_nonneg {P : Optimization.TRqParams} {L : ℕ → ℝ} {ϑ M : ℝ} {q : ℕ}
    (β θ : ℝ) : 0 ≤ trqCallKappaUnc0 P L ϑ M q β θ := by
  unfold trqCallKappaUnc0
  have := Optimization.one_le_trqKappaUns (P := P)
  have : 0 ≤ (|Real.log P.Δ₀| + |Real.log (Optimization.trqCallKappaRad P L ϑ M q)| +
    |Real.log (β * θ)|) / |Real.log P.γ₂| := by positivity
  linarith

/-! ### Runs whose inner calls are TRq calls -/

/-- **The inner calls of Phase 2 are TRq calls** ([cartis2022evaluation], Algorithm 14.3.2,
Step 1, with an inner method of trust-region type): for every outer iteration `k ≥ 1` reached,
the iterates, successful iterations and output radii `δ_{k+1}` of the `k`-th call are those of a
call of TRq on `μ(·, t_k)` with threshold `ϑ` and tolerances `β ‖r(x_k, t_k)‖ ε_j`
(`Optimization.IsTRqCallOut`), cut at any iteration. -/
def HighOrderTargetSeq.IsTRqCalls (f : E → ℝ) (c : E → F) (X : Set E) (q : ℕ)
    (P : Optimization.TRqParams) (ϑ θ β : ℝ) (ε : ℕ → ℝ) (D : HighOrderTargetSeq E) : Prop :=
  ∀ k, 1 ≤ k → D.Before f c X q θ ε k →
    Optimization.IsTRqCallOut (targetMerit f c (D.t k)) X P q
      (fun j => β * targetResidual f c (D.t k) (D.x k) * ε j) ϑ (D.xi k) (D.e k)
      (D.succ k) (D.δ (k + 1))

namespace IsHighOrderTargetRun

variable {f : E → ℝ} {c : E → F} {X : Set E} {q : ℕ} {P : Optimization.TRqParams}
  {ϑ θ β : ℝ} {ε : ℕ → ℝ} {x₁ : E} {D : HighOrderTargetSeq E}

/-- **The residual at the outer iterates is at least `θε₀`**: `‖r(x_k, t_k)‖ ≥ θε₀` for every
outer iteration `k ≥ 1` reached (`‖r(x_1, t_1)‖ = ε₀`, `‖r(x_{k+1}, t_{k+1})‖ = ε₀` after a
case-(a) iteration and `‖r(x_{k+1}, t_{k+1})‖ = ‖r(x_{k+1}, t_k)‖ ≥ θε₀` after a case-(b)
iteration). -/
theorem le_targetResidual (h : IsHighOrderTargetRun f c X q θ β ε x₁ D) :
    ∀ k, 1 ≤ k → D.Before f c X q θ ε k → θ * ε 0 ≤ targetResidual f c (D.t k) (D.x k) := by
  have hθε : θ * ε 0 ≤ ε 0 := mul_le_of_le_one_left h.ε₀_pos.le h.θ_lt_one.le
  intro k hk1
  induction k, hk1 using Nat.le_induction with
  | base =>
    intro _
    rw [h.t_one, h.x_one, targetResidual_sub_sqrt h.ε₀_pos.le (h.norm_one_le.trans hθε)]
    exact hθε
  | succ k hk1 _ =>
    intro hK
    have T := h.isTargetSequence hK
    have hs : ¬ D.Stop f c X q θ ε k := hK k hk1 (Nat.lt_succ_self k)
    rcases TargetFollowingSeq.ka_or_kb_of_not_stop hs with ha | hb
    · rw [T.residual_succ_of_Ka h.θ_lt_one.le h.ε₀_pos.le hk1 (Nat.lt_succ_self k) ha]
      exact hθε
    · have hna : ¬ D.IsKa f c θ ε k := fun ha => absurd hb.1 (not_le.2 ha)
      rw [T.residual_succ_of_not_Ka hk1 (Nat.lt_succ_self k) hna]
      exact hb.1

/-- The sublevel set of `μ(·, t_k)` at the start of the `k`-th call lies in
`{x ∈ X | ‖r(x, t_k)‖ ≤ 1}`, since `‖r(x_k, t_k)‖ ≤ ε₀ ≤ 1`. -/
private theorem call_mem_sublevel (h : IsHighOrderTargetRun f c X q θ β ε x₁ D) {k : ℕ}
    (hk1 : 1 ≤ k) (hk : D.Before f c X q θ ε k) :
    ∀ y ∈ X, targetMerit f c (D.t k) y ≤ targetMerit f c (D.t k) (D.xi k 0) →
      y ∈ {x | x ∈ X ∧ targetResidual f c (D.t k) x ≤ 1} := by
  intro y hy hyk
  rw [h.inner_zero k hk1 hk] at hyk
  exact ⟨hy, (targetMerit_le_targetMerit_iff.1 hyk).trans
    (((h.isTargetSequence hk).residual_le h.θ_lt_one.le h.ε₀_pos.le hk1 le_rfl).trans
      (h.ε_le_one 0 (by simp)))⟩

/-- **The tolerances of the calls**: the tolerances `ε'_j = β ‖r(x_k, t_k)‖ ε_j` of the `k`-th
call lie in `(0, 1]`, their minimum is at most `ϑ` when `β ≤ ϑ`, and at least `βθ ε₀ ε_min`. -/
theorem call_tol (h : IsHighOrderTargetRun f c X q θ β ε x₁ D) (hq : 1 ≤ q)
    (hβϑ : β ≤ ϑ) {k : ℕ} (hk1 : 1 ≤ k) (hk : D.Before f c X q θ ε k) :
    (∀ j ∈ Finset.Icc 1 q, β * targetResidual f c (D.t k) (D.x k) * ε j ∈ Ioc 0 1) ∧
    Optimization.finMin 1 (fun j => β * targetResidual f c (D.t k) (D.x k) * ε j) q ≤ ϑ ∧
    β * θ * (ε 0 * Optimization.finMin 1 ε q) ≤
      Optimization.finMin 1 (fun j => β * targetResidual f c (D.t k) (D.x k) * ε j) q := by
  set r := targetResidual f c (D.t k) (D.x k) with hr
  have hlo := h.le_targetResidual k hk1 hk
  have hε₀ := h.ε₀_pos
  have hε₀1 : ε 0 ≤ 1 := h.ε_le_one 0 (by simp)
  have hβ := h.β_pos
  have hθ := h.θ_pos
  have hβ1 : β ≤ 1 := h.β_le_θ.trans h.θ_lt_one.le
  have hhi : r ≤ ε 0 := (h.isTargetSequence hk).residual_le h.θ_lt_one.le hε₀.le hk1 le_rfl
  have hr0 : 0 < r := lt_of_lt_of_le (mul_pos hθ hε₀) hlo
  have hεj : ∀ j ∈ Finset.Icc 1 q, 0 < ε j ∧ ε j ≤ 1 := fun j hj =>
    ⟨h.ε_pos' hj, h.ε_le_one j (Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.mem_Icc.1 hj).2))⟩
  have hle : ∀ j ∈ Finset.Icc 1 q, β * r * ε j ≤ β := fun j hj => by
    have h1 : r * ε j ≤ 1 := by nlinarith [hεj j hj]
    nlinarith [hεj j hj]
  refine ⟨fun j hj => ⟨by have := (hεj j hj).1; positivity, (hle j hj).trans hβ1⟩, ?_, ?_⟩
  · exact (Optimization.finMin_le (Finset.mem_Icc.2 ⟨le_rfl, hq⟩)).trans
      ((hle 1 (Finset.mem_Icc.2 ⟨le_rfl, hq⟩)).trans hβϑ)
  · have hεm0 : 0 < Optimization.finMin 1 ε q :=
      Optimization.finMin_pos one_pos fun j hj => (hεj j hj).1
    have hεm1 : Optimization.finMin 1 ε q ≤ 1 := Optimization.finMin_le_left
    refine Optimization.le_finMin ?_ fun j hj => ?_
    · exact mul_le_one_of_le_one (mul_le_one_of_le_one hβ1 hθ.le h.θ_lt_one.le) (by positivity)
        (mul_le_one_of_le_one hε₀1 hεm0.le hεm1)
    · have h1 : θ * ε 0 * Optimization.finMin 1 ε q ≤ r * ε j :=
        mul_le_mul hlo (Optimization.finMin_le hj) hεm0.le hr0.le
      nlinarith

/-- **Runs with TRq calls satisfy the inner-test contract** ([cartis2022evaluation],
Lemmas 14.2.2–14.2.3, trust-region rows, applied to `μ(·, t_k)`), with the exponents
`π_l = q + 1` (the decrease of Lemma 12.2.4 is `κ_decr ε'_min^{q+1}`), the `t`-independent
constants `κ_decr = Optimization.trqCallKappaDecr P L ϑ M q`, `κ_uns = Optimization.trqKappaUns P`,
the count constant `κ_unc = κ_unc⁰ + |log(ε₀ ε_min)|/|log γ₂|` and radii
`ρ_j = κ_ρ βθ ε₀ ε_min`, when every `μ(·, t)` satisfies `LipschitzDerivsAnchored` with constants
`L` on `{x ∈ X | ‖r(x, t)‖ ≤ 1}` (inside `X₀ ⊇ X`) with derivatives of orders `0, …, q` bounded
by `M > 0` there, `1 ≤ q` and `β ≤ ϑ ≤ 1`. -/
theorem isInnerTestContract_of_isTRqCalls (h : IsHighOrderTargetRun f c X q θ β ε x₁ D)
    (hcalls : D.IsTRqCalls f c X q P ϑ θ β ε) (hq : 1 ≤ q) {X₀ : Set E} {L : ℕ → ℝ} {M : ℝ}
    (hμ : ∀ t, LipschitzDerivsAnchored (targetMerit f c t) X₀
      {x | x ∈ X ∧ targetResidual f c t x ≤ 1} 1 q L)
    (hμM : ∀ t, ∀ y ∈ {x | x ∈ X ∧ targetResidual f c t x ≤ 1}, Optimization.finMax 0
      (fun i => ‖iteratedFDeriv ℝ i (targetMerit f c t) y‖) q ≤ M) (hM0 : 0 < M)
    (hXX₀ : X ⊆ X₀) (hβϑ : β ≤ ϑ) (hϑ1 : ϑ ≤ 1) :
    D.IsInnerTestContract f c X q θ β ε (Optimization.trqCallKappaDecr P L ϑ M q)
      (Optimization.trqKappaUns P)
      (trqCallKappaUnc0 P L ϑ M q β θ + tolLogTerm q ε / |Real.log P.γ₂|)
      (fun _ => (q : ℝ) + 1)
      (fun _ => Optimization.trqCallKappaRad P L ϑ M q * β * θ *
        (ε 0 * Optimization.finMin 1 ε q)) := by
  have hϑ0 : 0 < ϑ := h.β_pos.trans_le hβϑ
  have hκR := Optimization.trqCallKappaRad_pos (P := P) (L := L) (q := q) hϑ0 hM0
  have hx : ∀ k, 1 ≤ k → D.Before f c X q θ ε k → D.xi k 0 ∈ X := fun k hk1 hk => by
    rw [h.inner_zero k hk1 hk]; exact h.x_mem k hk1 hk
  have hMk : ∀ k, 1 ≤ k → D.Before f c X q θ ε k → Optimization.finMax 0
      (fun i => ‖iteratedFDeriv ℝ i (targetMerit f c (D.t k)) (D.xi k 0)‖) q ≤ M :=
    fun k hk1 hk => hμM _ _ (h.call_mem_sublevel hk1 hk _ (hx k hk1 hk) le_rfl)
  refine ⟨⟨fun k hk1 hk => ?_, fun k hk1 hk => (hcalls k hk1 hk).eq_of_not_succ,
    fun k hk1 hk i hi hs _ _ => ?_⟩, fun k hk1 hk _ _ j hj => ?_⟩
  · -- the count, with the logarithm of the radius bound
    obtain ⟨htol, hϑ', hlow⟩ := h.call_tol hq hβϑ hk1 hk
    have hcount := (hcalls k hk1 hk).le_count (hμ (D.t k)) hXX₀
      (h.call_mem_sublevel hk1 hk) (hx k hk1 hk) (hMk k hk1 hk) hM0 htol hϑ' hϑ1
    have hε₀ := h.ε₀_pos
    have hε₀1 : ε 0 ≤ 1 := h.ε_le_one 0 (by simp)
    have hεm0 : 0 < Optimization.finMin 1 ε q :=
      Optimization.finMin_pos one_pos fun j hj => h.ε_pos' hj
    have hεm1 : Optimization.finMin 1 ε q ≤ 1 := Optimization.finMin_le_left
    have hβθ1 : β * θ ≤ 1 := by
      nlinarith [h.β_le_θ, h.θ_lt_one, h.β_pos, h.θ_pos]
    set b := Optimization.finMin 1 (fun j => β * targetResidual f c (D.t k) (D.x k) * ε j) q
    have hb0 : 0 < b := lt_of_lt_of_le (by have := h.β_pos; have := h.θ_pos; positivity) hlow
    have hlog : |Real.log (Optimization.trqCallKappaRad P L ϑ M q * b / P.Δ₀)| ≤
        |Real.log P.Δ₀| + |Real.log (Optimization.trqCallKappaRad P L ϑ M q)| +
          |Real.log (β * θ)| + tolLogTerm q ε := by
      rw [Real.log_div (mul_pos hκR hb0).ne' P.Δ₀_pos.ne', Real.log_mul hκR.ne' hb0.ne']
      have hlb := Real.abs_log_le_of_mul_le (mul_pos h.β_pos h.θ_pos) (mul_pos hε₀ hεm0) hβθ1
        (mul_le_one_of_le_one hε₀1 hεm0.le hεm1) hlow Optimization.finMin_le_left
      unfold tolLogTerm
      calc |Real.log (Optimization.trqCallKappaRad P L ϑ M q) + Real.log b - Real.log P.Δ₀| ≤
            |Real.log (Optimization.trqCallKappaRad P L ϑ M q)| + |Real.log b| +
              |Real.log P.Δ₀| := (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
        _ ≤ _ := by linarith
    have hg : 0 < |Real.log P.γ₂| := abs_pos.2 (Real.log_neg P.γ₂_pos P.γ₂_lt_one).ne
    classical
    rw [HighOrderTargetSeq.succCount_eq_card_filter]
    unfold trqCallKappaUnc0
    have : |Real.log (Optimization.trqCallKappaRad P L ϑ M q * b / P.Δ₀)| / |Real.log P.γ₂| ≤
        (|Real.log P.Δ₀| + |Real.log (Optimization.trqCallKappaRad P L ϑ M q)| +
          |Real.log (β * θ)|) / |Real.log P.γ₂| + tolLogTerm q ε / |Real.log P.γ₂| := by
      rw [← add_div]
      exact div_le_div_of_nonneg_right hlog hg.le
    linarith
  · -- the decrease, at an order `l` attaining `ε'_min`
    obtain ⟨htol, hϑ', -⟩ := h.call_tol hq hβϑ hk1 hk
    obtain ⟨l, hl, hmin⟩ := Optimization.exists_finMin_eq hq fun j hj => (htol j hj).2
    refine ⟨l, hl, ?_⟩
    have hdec := (hcalls k hk1 hk).decrease (hμ (D.t k)) hXX₀
      (h.call_mem_sublevel hk1 hk) (hx k hk1 hk) (hMk k hk1 hk) hM0 htol hϑ' hϑ1 i hi hs
    rw [hmin] at hdec
    have e : ((q : ℝ) + 1) = ((q + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [e, Real.rpow_natCast]
    exact hdec
  · -- the radii
    obtain ⟨htol, hϑ', hlow⟩ := h.call_tol hq hβϑ hk1 hk
    calc Optimization.trqCallKappaRad P L ϑ M q * β * θ * (ε 0 * Optimization.finMin 1 ε q) =
          Optimization.trqCallKappaRad P L ϑ M q * (β * θ * (ε 0 * Optimization.finMin 1 ε q)) :=
          by ring
      _ ≤ Optimization.trqCallKappaRad P L ϑ M q * Optimization.finMin 1
          (fun j => β * targetResidual f c (D.t k) (D.x k) * ε j) q :=
        mul_le_mul_of_nonneg_left hlow hκR.le
      _ ≤ D.δ (k + 1) j := (hcalls k hk1 hk).radius_ge (hμ (D.t k)) hXX₀
          (h.call_mem_sublevel hk1 hk) (hx k hk1 hk) (hMk k hk1 hk) htol hϑ' hϑ1 j hj

end IsHighOrderTargetRun

/-! ### Existence of runs with TRq calls -/

section Existence

variable [FiniteDimensional ℝ E] {f : E → ℝ} {c : E → F} {X : Set E} {q : ℕ} {ϑ θ β : ℝ}
  {ε : ℕ → ℝ}

open Classical in
/-- **One TRq call of Phase 2 exists** from every `(x, t)` with `x ∈ X` and
`θε₀ ≤ ‖r(x, t)‖ ≤ ε₀`: TRq on `μ(·, t)` with threshold `ϑ` and tolerances `β ‖r(x, t)‖ ε`
(which terminates, `Optimization.IsTRqRun.complexity`), stopped at its termination or as soon as
`‖r(·, t)‖ < θε₀` (`Optimization.exists_isTRqCallOut_of_stop`), returning the radii
`min(Δ_e, ϑ)`; its output satisfies the first or the criticality test of (14.3.32). -/
theorem exists_innerCall_isTRqCallOut {t : ℝ} {L : ℕ → ℝ} {X₀ : Set E}
    (hμ : LipschitzDerivsAnchored (targetMerit f c t) X₀
      {x | x ∈ X ∧ targetResidual f c t x ≤ 1} 1 q L) (hXX₀ : X ⊆ X₀)
    (P : Optimization.TRqParams) (hq : 1 ≤ q) (hX : IsClosed X) (hθ0 : 0 < θ) (hβ0 : 0 < β)
    (hβθ : β ≤ θ) (hβϑ : β ≤ ϑ) (hϑ1 : ϑ ≤ 1)
    (hε : ∀ j ∈ Finset.range (q + 1), 0 < ε j ∧ ε j ≤ 1) {x : E}
    (hx : x ∈ X) (hlo : θ * ε 0 ≤ targetResidual f c t x) (hhi : targetResidual f c t x ≤ ε 0) :
    ∃ o : InnerCall E, o.xi 0 = x ∧ o.xi o.e ∈ X ∧
      (∀ j ∈ Finset.Icc 1 q, 0 < o.δ j ∧ o.δ j ≤ 1) ∧
      (targetResidual f c t (o.xi o.e) < θ * ε 0 ∨ targetCrit f c X q ε t (o.xi o.e) o.δ) ∧
      (∀ i < o.e, targetMerit f c t (o.xi (i + 1)) ≤ targetMerit f c t (o.xi i)) ∧
      (∀ i < o.e, θ * ε 0 ≤ targetResidual f c t (o.xi i)) ∧
      targetResidual f c t (o.xi o.e) ≤ targetResidual f c t x ∧
      Optimization.IsTRqCallOut (targetMerit f c t) X P q
        (fun j => β * targetResidual f c t x * ε j) ϑ o.xi o.e o.succ o.δ := by
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = targetResidual f c t x := ⟨_, rfl⟩
  rw [← hρ] at hlo hhi ⊢
  have hεI : ∀ j ∈ Finset.Icc 1 q, 0 < ε j ∧ ε j ≤ 1 := fun j hj =>
    hε j (Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.mem_Icc.1 hj).2))
  have hε₀ := hε 0 (by simp)
  have hρ0 : 0 < ρ := lt_of_lt_of_le (mul_pos hθ0 hε₀.1) hlo
  have hβ1 : β ≤ 1 := hβϑ.trans hϑ1
  have hle : ∀ j ∈ Finset.Icc 1 q, β * ρ * ε j ≤ β := fun j hj => by
    have h1 : ρ * ε j ≤ 1 := by nlinarith [hεI j hj]
    nlinarith [hεI j hj]
  have hε' : ∀ j ∈ Finset.Icc 1 q, β * ρ * ε j ∈ Ioc 0 1 := fun j hj =>
    ⟨by have := (hεI j hj).1; positivity, (hle j hj).trans hβ1⟩
  have h1q : 1 ∈ Finset.Icc 1 q := Finset.mem_Icc.2 ⟨le_rfl, hq⟩
  have hϑ' : Optimization.finMin 1 (fun j => β * ρ * ε j) q ≤ ϑ :=
    (Optimization.finMin_le h1q).trans ((hle 1 h1q).trans hβϑ)
  have hS : ∀ y ∈ X, targetMerit f c t y ≤ targetMerit f c t x →
      y ∈ {x | x ∈ X ∧ targetResidual f c t x ≤ 1} := fun y hy hyx =>
    ⟨hy, (targetMerit_le_targetMerit_iff.1 hyx).trans ((hρ ▸ hhi).trans hε₀.2)⟩
  obtain ⟨xi, e, succ, δ, hcall, hx0, hmem, hδ, hmono, hdec, hlow, hend⟩ :=
    Optimization.exists_isTRqCallOut_of_stop (flow := 0) hX
      (fun y _ => targetMerit_nonneg) hμ hXX₀ hx hS hε' hϑ'
      hϑ1 P (fun y => targetResidual f c t y < θ * ε 0)
  refine ⟨⟨xi, e, succ, fun _ => δ⟩, hx0, hmem, fun _ _ => hδ, ?_, hmono,
    fun i hi => not_lt.1 (hlow i hi), ?_, hcall⟩
  · by_cases hlt : targetResidual f c t (xi e) < θ * ε 0
    · exact Or.inl hlt
    · -- the call has terminated: its certificate gives the criticality test
      refine Or.inr fun j hj => ((hend.resolve_left hlt) j hj).trans ?_
      have hge := not_lt.1 hlt
      have hεj := (hεI j hj).1
      have : β * ρ ≤ targetResidual f c t (xi e) := by nlinarith
      have : β * ρ * ε j ≤ ε j * targetResidual f c t (xi e) := by nlinarith
      change β * ρ * ε j * δ ^ j / (j ! : ℝ) ≤
        ε j * targetResidual f c t (xi e) * δ ^ j / (j ! : ℝ)
      have := hδ.1
      gcongr
  · rw [hρ]
    exact targetMerit_le_targetMerit_iff.1 hdec

/-- **Runs of Phase 2 with TRq calls exist** from every `x₁ ∈ X` with `‖c(x₁)‖ ≤ θε₀`, for a
closed `X`, `θ ∈ (0, 1)`, `0 < β ≤ θ`, `β ≤ ϑ ≤ 1` and `ε ∈ (0, 1]^{q+1}`, when every `μ(·, t)`
satisfies `LipschitzDerivsAnchored` on `{x ∈ X | ‖r(x, t)‖ ≤ 1}` inside `X₀ ⊇ X`: the calls of
`exists_innerCall_isTRqCallOut` in the construction `HighOrderTargetSeq.exists_run_of_oracle`. -/
theorem exists_isHighOrderTargetRun_isTRqCalls {L : ℕ → ℝ} {X₀ : Set E}
    (hμ : ∀ t, LipschitzDerivsAnchored (targetMerit f c t) X₀
      {x | x ∈ X ∧ targetResidual f c t x ≤ 1} 1 q L) (hXX₀ : X ⊆ X₀)
    (P : Optimization.TRqParams) (hq : 1 ≤ q) (hX : IsClosed X) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hβ0 : 0 < β) (hβθ : β ≤ θ) (hβϑ : β ≤ ϑ) (hϑ1 : ϑ ≤ 1)
    (hε : ∀ j ∈ Finset.range (q + 1), 0 < ε j ∧ ε j ≤ 1) {x₁ : E} (hx₁ : x₁ ∈ X)
    (hc₁ : ‖c x₁‖ ≤ θ * ε 0) :
    ∃ D : HighOrderTargetSeq E, IsHighOrderTargetRun f c X q θ β ε x₁ D ∧
      D.IsTRqCalls f c X q P ϑ θ β ε := by
  obtain ⟨D, hD, hcalls⟩ := HighOrderTargetSeq.exists_run_of_oracle hθ0 hθ1 hβ0 hβθ hε hx₁ hc₁
    (fun x t o => Optimization.IsTRqCallOut (targetMerit f c t) X P q
      (fun j => β * targetResidual f c t x * ε j) ϑ o.xi o.e o.succ o.δ)
    fun x t hx hlo hhi _ =>
      (exists_innerCall_isTRqCallOut (hμ t) hXX₀ P hq hX hθ0 hβ0 hβθ hβϑ hϑ1 hε hx hlo hhi).imp
        fun _ ⟨h0, h1, h2, h3, h4⟩ => ⟨h0, h1, h2, h3.imp_right Or.inr, h4⟩
  exact ⟨D, hD, fun k hk1 hk => (hcalls k hk1 hk).2⟩

end Existence

/-! ### The cost of a TRq call on the constraint violation -/

/-- **The cost of a terminating TRq call on `ν = ½ ‖c‖²`** with tolerances `ε'_j = β₁ ‖c(y)‖ ε_j`
(`j ∈ [1 : q]`) from a point `y ∈ X` with `θε₀ < ‖c(y)‖ ≤ ‖c(x₀)‖` ([cartis2022evaluation],
(14.3.20)–(14.3.21) for TRq with the exponents `q + 1`, in additive form): under
`LipschitzDerivsAnchored` for `ν` on `{z ∈ X | ‖c(z)‖ ≤ ‖c(x₀)‖}` (constants `L_ν`, derivatives
bounded by `M_ν > 0`), `ϑ ≤ 1`, `β₁ ‖c(x₀)‖ ≤ ϑ`, `θ, β₁ ∈ (0, 1)` and `ε ∈ (0, 1]^{q+1}`, the call
uses at most `κ^A ν(y)/ε'_min^{q+1} + κ^B (|log(β₁θ)| + |log(ε₀ ε_min)|) + κ^C` evaluations of `c`
and `κ^S ν(y)/ε'_min^{q+1} + 1` derivative evaluations
(`Optimization.IsTRqOutputCost.cost_le`). -/
theorem IsTRqOutputCost.cost_le_halfSqNorm {c : E → F} {X : Set E} {q : ℕ}
    {P : Optimization.TRqParams} {ϑ θ β₁ : ℝ} {ε ε' : ℕ → ℝ} {x₀ y y' : E} {δ : ℕ → ℝ}
    {nF nD : ℕ} {X₀ : Set E} {Lν : ℕ → ℝ} {Mν : ℝ}
    (hcall : Optimization.IsTRqOutputCost (halfSqNorm c) X P q ε' ϑ y y' δ nF nD) (hq : 1 ≤ q)
    (hν : LipschitzDerivsAnchored (halfSqNorm c) X₀ {z | z ∈ X ∧ ‖c z‖ ≤ ‖c x₀‖} 1 q Lν)
    (hνM : ∀ z ∈ {z | z ∈ X ∧ ‖c z‖ ≤ ‖c x₀‖},
      Optimization.finMax 0 (fun i => ‖iteratedFDeriv ℝ i (halfSqNorm c) z‖) q ≤ Mν)
    (hMν0 : 0 < Mν) (hXX₀ : X ⊆ X₀) (hϑ1 : ϑ ≤ 1) (hβ₁ϑ : β₁ * ‖c x₀‖ ≤ ϑ) (hθ0 : 0 < θ)
    (hθ1 : θ < 1) (hβ₁0 : 0 < β₁) (hβ₁1 : β₁ < 1)
    (hε : ∀ j ∈ Finset.range (q + 1), 0 < ε j ∧ ε j ≤ 1) (hy : y ∈ X)
    (hck : ‖c y‖ ≤ ‖c x₀‖) (hlo : θ * ε 0 < ‖c y‖)
    (hε' : ∀ j ∈ Finset.Icc 1 q, ε' j = β₁ * ‖c y‖ * ε j) :
    (nF : ℝ) ≤ Optimization.trqCallKappaA P Lν ϑ Mν q * halfSqNorm c y /
        Optimization.finMin 1 ε' q ^ (q + 1) +
        (Optimization.kappaBTRq P * (|Real.log (β₁ * θ)| + tolLogTerm q ε) +
          Optimization.trqCallKappaC P Lν ϑ Mν q) ∧
      (nD : ℝ) ≤ Optimization.trqCallKappaS P Lν ϑ Mν q * halfSqNorm c y /
        Optimization.finMin 1 ε' q ^ (q + 1) + 1 := by
  have hε₀ := hε 0 (by simp)
  have hεI : ∀ l ∈ Finset.Icc 1 q, 0 < ε l ∧ ε l ≤ 1 := fun l hl =>
    hε l (Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.mem_Icc.1 hl).2))
  have hεm0 : 0 < Optimization.finMin 1 ε q :=
    Optimization.finMin_pos one_pos fun j hj => (hεI j hj).1
  have hεm1 : Optimization.finMin 1 ε q ≤ 1 := Optimization.finMin_le_left
  have h1q : 1 ∈ Finset.Icc 1 q := Finset.mem_Icc.2 ⟨le_rfl, hq⟩
  obtain ⟨r, hr⟩ : ∃ x, x = ‖c y‖ := ⟨_, rfl⟩
  have hck0 := hck
  rw [← hr] at hck hlo hε'
  have hr0 : 0 < r := (mul_pos hθ0 hε₀.1).trans hlo
  have hle : ∀ j ∈ Finset.Icc 1 q, ε' j ≤ ϑ := fun j hj => by
    rw [hε' j hj]
    calc β₁ * r * ε j ≤ β₁ * ‖c x₀‖ * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hck hβ₁0.le) (hεI j hj).2 (hεI j hj).1.le
            (mul_nonneg hβ₁0.le (norm_nonneg _))
      _ ≤ ϑ := by rw [mul_one]; exact hβ₁ϑ
  have htol : ∀ j ∈ Finset.Icc 1 q, ε' j ∈ Ioc 0 1 := fun j hj =>
    ⟨by rw [hε' j hj]; have := (hεI j hj).1; positivity, (hle j hj).trans hϑ1⟩
  have hϑ' : Optimization.finMin 1 ε' q ≤ ϑ := (Optimization.finMin_le h1q).trans (hle 1 h1q)
  have hcall' := hcall.cost_le (flow := 0) (fun z _ => halfSqNorm_nonneg c z) hν hXX₀
    (fun z hz hzk => ⟨hz, (halfSqNorm_le_halfSqNorm_iff.1 hzk).trans hck0⟩)
    hy (hνM _ ⟨hy, hck0⟩) hMν0 htol hϑ' hϑ1
  simp only [sub_zero] at hcall'
  have hεm' : β₁ * θ * (ε 0 * Optimization.finMin 1 ε q) ≤ Optimization.finMin 1 ε' q := by
    refine Optimization.le_finMin ?_ fun j hj => ?_
    · exact mul_le_one_of_le_one (mul_le_one_of_le_one hβ₁1.le hθ0.le hθ1.le)
        (mul_pos hε₀.1 hεm0).le (mul_le_one_of_le_one hε₀.2 hεm0.le hεm1)
    · rw [hε' j hj]
      have : θ * ε 0 * Optimization.finMin 1 ε q ≤ r * ε j :=
        mul_le_mul hlo.le (Optimization.finMin_le hj) hεm0.le hr0.le
      calc β₁ * θ * (ε 0 * Optimization.finMin 1 ε q) =
            β₁ * (θ * ε 0 * Optimization.finMin 1 ε q) := by ring
        _ ≤ β₁ * (r * ε j) := mul_le_mul_of_nonneg_left this hβ₁0.le
        _ = β₁ * r * ε j := by ring
  have hlog : |Real.log (Optimization.finMin 1 ε' q)| ≤ |Real.log (β₁ * θ)| + tolLogTerm q ε :=
    Real.abs_log_le_of_mul_le (mul_pos hβ₁0 hθ0) (mul_pos hε₀.1 hεm0)
      (mul_le_one_of_le_one hβ₁1.le hθ0.le hθ1.le) (mul_le_one_of_le_one hε₀.2 hεm0.le hεm1)
      hεm' Optimization.finMin_le_left
  have hB0 : 0 ≤ Optimization.kappaBTRq P := Optimization.kappaBTRq_nonneg P
  have h2 := mul_le_mul_of_nonneg_left hlog hB0
  exact ⟨by linarith [hcall'.1], hcall'.2⟩

end Constrained
