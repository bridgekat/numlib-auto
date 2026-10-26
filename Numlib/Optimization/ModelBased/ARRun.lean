import Numlib.Optimization.Complexity.Existence
import Numlib.Optimization.Complexity.Telescoping
import Numlib.Optimization.ModelBased.RegularizationUpdate
import Numlib.Optimization.ModelBased.TaylorModel

/-!
# Generic runs of adaptive-regularization methods

Every adaptive-regularization (AR) method of [cartis2022evaluation] (Algorithms 2.4.1 AR1, 3.3.1
AR2, 4.1.1 ARp, 5.1.1 ARpLE, 5.5.1 ARp-H, 6.2.1 ARp-CC, 6.2.2 ARp1-CC, 6.3.1 ARpLE-CC, the inner
runs of 7.2.1, 12.2.2 ARqp, 14.1.1 ARqpC; per iteration also 13.1.2 ARqpIDA and 13.3.2 ARqpEDA)
shares Steps 3–4: given a ratio `ρ_k`, the trial point `x_k + s_k` is accepted iff `η₁ ≤ ρ_k`, and
the regularization weight is updated by (2.4.4) (`Optimization.ARUpdate`). Methods differ only in

* the Step-1 termination test `stop₁ k`, and an optional test `stop₂ k` evaluated after the step
  is computed (ARqp: `m_k(s_k) = m_k(0)`; ARp-H: the test at the trial point; `fun _ => False`
  otherwise);
* the Step-2 conditions on the step, `step k`;
* the ratio `ρ k`, normally `Optimization.taylorRatio f p x s k` (achieved over Taylor-predicted
  decrease).

## Main definitions

* `Optimization.ARParams`: the constants `σ₀, σ_min, η₁, η₂, γ₁, γ₂, γ₃` of (2.4.2).
* `Optimization.ARAcceptance P ρ x s x' σ σ'`: Steps 3–4 of one iteration.
* `Optimization.IsARRun P stop₁ step stop₂ ρ x s σ`: a run, the rules being imposed only before
  termination.
* `Optimization.taylorRatio f p x s k`: the ratio (2.4.3), (3.3.7), (4.1.15).
* `Optimization.arSigmaMax P L = max(σ₀, γ₃ L / (1 - η₂))`: the `σ_max` of (4.1.19).

## Main statements

* `Optimization.IsARRun.sigma_le_max`: the mechanism of Lemmas 2.4.2, 3.3.2, 4.1.2;
* `Optimization.IsARRun.sigma_le`: Lemma 4.1.2 for every AR method with exact Taylor models
  (also on a convex feasible set);
* `Optimization.IsARRun.sub_ge_of_succ`, `Optimization.IsARRun.sub_ge_of_succ_taylor`: the
  decrease on successful iterations ((4.1.37));
* `Optimization.IsARRun.succ_count`, `Optimization.IsARRun.le_succ_count`: Lemma 2.4.1;
* `Optimization.IsARRun.exists_isFirstHit_of_decrease`: the counting skeleton of the complexity
  theorems (Theorems 2.4.4, 3.3.5, 4.1.5, …), with the book's constants (4.1.46);
* `Optimization.exists_isARRun_prev`, `Optimization.exists_isARRun`: existence of runs when an
  admissible step exists whenever the test fails (the test may read the previous iteration, as
  ARp's third-order test does through `𝓜_k`).

Iterations that leave both the iterate and the weight unchanged (the accuracy-improving
iterations of Chapter 13) do not fit `IsARRun`; their per-iteration rules use `ARAcceptance`.
-/

open Set Finset
open scoped Nat

namespace Optimization

/-- The constants of an adaptive-regularization method ([cartis2022evaluation], (2.4.2), (3.3.3),
Step 0 of Algorithms 4.1.1, 6.2.1, 12.2.2, 13.1.2, 14.1.1): the initial weight `σ₀ > 0`, the lower
bound `σ_min ∈ [0, σ₀]`, the acceptance thresholds `0 < η₁ ≤ η₂ < 1` and the update factors
`0 < γ₁ < 1 < γ₂ ≤ γ₃`. (`σ_min = 0` is allowed for ARp-H, Algorithm 5.5.1; the book's strict
`γ₂ < γ₃` is never used.) -/
structure ARParams where
  /-- The initial regularization weight. -/
  σ₀ : ℝ
  /-- The lower bound on the regularization weight. -/
  σmin : ℝ
  /-- The threshold for successful iterations. -/
  η₁ : ℝ
  /-- The threshold for very successful iterations. -/
  η₂ : ℝ
  /-- The decrease factor of very successful iterations. -/
  γ₁ : ℝ
  /-- The increase factor (lower end for unsuccessful iterations). -/
  γ₂ : ℝ
  /-- The largest increase factor. -/
  γ₃ : ℝ
  /-- `σ₀ > 0`. -/
  σ₀_pos : 0 < σ₀
  /-- `σ_min ≥ 0`. -/
  σmin_nonneg : 0 ≤ σmin
  /-- `σ_min ≤ σ₀`. -/
  σmin_le_σ₀ : σmin ≤ σ₀
  /-- `η₁ > 0`. -/
  η₁_pos : 0 < η₁
  /-- `η₁ ≤ η₂`. -/
  η₁_le_η₂ : η₁ ≤ η₂
  /-- `η₂ < 1`. -/
  η₂_lt_one : η₂ < 1
  /-- `γ₁ > 0`. -/
  γ₁_pos : 0 < γ₁
  /-- `γ₁ < 1`. -/
  γ₁_lt_one : γ₁ < 1
  /-- `γ₂ > 1`. -/
  one_lt_γ₂ : 1 < γ₂
  /-- `γ₂ ≤ γ₃`. -/
  γ₂_le_γ₃ : γ₂ ≤ γ₃

namespace ARParams

variable (P : ARParams)

theorem γ₁_le_one : P.γ₁ ≤ 1 := P.γ₁_lt_one.le

theorem one_le_γ₂ : 1 ≤ P.γ₂ := P.one_lt_γ₂.le

theorem γ₂_pos : 0 < P.γ₂ := one_pos.trans P.one_lt_γ₂

theorem one_lt_γ₃ : 1 < P.γ₃ := P.one_lt_γ₂.trans_le P.γ₂_le_γ₃

theorem one_le_γ₃ : 1 ≤ P.γ₃ := P.one_lt_γ₃.le

theorem γ₃_pos : 0 < P.γ₃ := one_pos.trans P.one_lt_γ₃

theorem η₂_pos : 0 < P.η₂ := P.η₁_pos.trans_le P.η₁_le_η₂

theorem one_sub_η₂_pos : 0 < 1 - P.η₂ := sub_pos.2 P.η₂_lt_one

theorem log_γ₂_pos : 0 < Real.log P.γ₂ := Real.log_pos P.one_lt_γ₂

end ARParams

section Acceptance

variable {E : Type*} [Add E]

/-- Steps 3–4 of an adaptive-regularization method for one iteration ([cartis2022evaluation],
(2.4.3)–(2.4.4), (4.1.15)–(4.1.16), (12.2.30)–(12.2.31), (13.1.58)–(13.1.59), (14.1.15)–(14.1.16)):
given the ratio `ρ`, the new iterate `x'` is the trial point `x + s` if `η₁ ≤ ρ` and `x` otherwise,
and the new weight `σ'` satisfies the update rule (2.4.4). -/
def ARAcceptance (P : ARParams) (ρ : ℝ) (x s x' : E) (σ σ' : ℝ) : Prop :=
  x' = (if P.η₁ ≤ ρ then x + s else x) ∧ ARUpdate P.η₁ P.η₂ P.γ₁ P.γ₂ P.γ₃ P.σmin ρ σ σ'

variable {P : ARParams} {ρ : ℝ} {x s x' : E} {σ σ' : ℝ}

theorem arAcceptance_iff :
    ARAcceptance P ρ x s x' σ σ' ↔
      x' = (if P.η₁ ≤ ρ then x + s else x) ∧ ARUpdate P.η₁ P.η₂ P.γ₁ P.γ₂ P.γ₃ P.σmin ρ σ σ' :=
  Iff.rfl

namespace ARAcceptance

variable (h : ARAcceptance P ρ x s x' σ σ')
include h

/-- The weight update of an accepted iteration. -/
theorem update : ARUpdate P.η₁ P.η₂ P.γ₁ P.γ₂ P.γ₃ P.σmin ρ σ σ' := h.2

/-- A successful iteration moves to the trial point. -/
theorem eq_add (hρ : P.η₁ ≤ ρ) : x' = x + s := by
  rw [h.1, ite_eq_left hρ]

/-- An unsuccessful iteration keeps the iterate. -/
theorem eq_self (hρ : ρ < P.η₁) : x' = x := by
  rw [h.1, ite_eq_right (not_le.2 hρ)]

/-- The new iterate is the trial point or the old iterate. -/
theorem eq_add_or_eq_self : x' = x + s ∨ x' = x := by
  by_cases hρ : P.η₁ ≤ ρ
  · exact Or.inl (h.eq_add hρ)
  · exact Or.inr (h.eq_self (not_le.1 hρ))

/-- The update preserves positivity of the weight. -/
theorem pos (hσ : 0 < σ) : 0 < σ' := h.2.pos P.γ₁_pos P.γ₂_pos hσ

/-- The update preserves the lower bound `σ_min`. -/
theorem sigmaMin_le (hσ : P.σmin ≤ σ) : P.σmin ≤ σ' :=
  h.2.sigmaMin_le P.σmin_nonneg P.one_le_γ₂ hσ

/-- **Decrease on a successful iteration**: if `ρ = (w x - w (x + s)) / pred` with `pred > 0` and
`η₁ ≤ ρ`, then `w x - w x' ≥ η₁ pred`. -/
theorem sub_ge {w : E → ℝ} {pred : ℝ} (hρ : ρ = reductionRatio w x s pred) (hpred : 0 < pred)
    (hs : P.η₁ ≤ ρ) : P.η₁ * pred ≤ w x - w x' := by
  rw [h.eq_add hs]
  exact sub_le_of_le_reductionRatio hpred (hρ ▸ hs)

/-- The objective does not increase along an iteration whose ratio is a reduction ratio with a
positive predicted decrease. -/
theorem le {w : E → ℝ} {pred : ℝ} (hρ : ρ = reductionRatio w x s pred) (hpred : 0 < pred) :
    w x' ≤ w x := by
  by_cases hs : P.η₁ ≤ ρ
  · have := h.sub_ge hρ hpred hs
    nlinarith [P.η₁_pos]
  · rw [h.eq_self (not_le.1 hs)]

end ARAcceptance

/-- **Existence of the next weight**: for `σ ≥ σ_min`, the weight
`σ' = max(σ_min, γ₁ σ)` after a very successful iteration, `σ' = σ` after a successful one and
`σ' = γ₂ σ` after an unsuccessful one is admissible (the left ends of the intervals of (2.4.4));
it satisfies `σ' ≥ σ_min`, and `σ' > 0` if `σ > 0`. -/
theorem exists_arAcceptance (P : ARParams) (ρ : ℝ) (x s : E) {σ : ℝ} (hσ : P.σmin ≤ σ) :
    ∃ σ', ARAcceptance P ρ x s (if P.η₁ ≤ ρ then x + s else x) σ σ' ∧ P.σmin ≤ σ' ∧
      (0 < σ → 0 < σ') := by
  have hσ0 : 0 ≤ σ := P.σmin_nonneg.trans hσ
  have hγσ : P.γ₁ * σ ≤ σ := mul_le_of_le_one_left hσ0 P.γ₁_le_one
  have hacc : ARAcceptance P ρ x s (if P.η₁ ≤ ρ then x + s else x) σ
      (if P.η₂ ≤ ρ then max P.σmin (P.γ₁ * σ) else if P.η₁ ≤ ρ then σ else P.γ₂ * σ) := by
    refine ⟨rfl, ⟨fun h2 => ?_, fun h1 h2 => ?_, fun h1 => ?_⟩⟩
    · rw [ite_eq_left h2]
      exact ⟨le_rfl, max_le hσ hγσ⟩
    · rw [ite_eq_right (not_le.2 h2), ite_eq_left h1]
      exact ⟨le_rfl, le_mul_of_one_le_left hσ0 P.one_le_γ₂⟩
    · rw [ite_eq_right (not_le.2 (h1.trans_le P.η₁_le_η₂)), ite_eq_right (not_le.2 h1)]
      exact ⟨le_rfl, mul_le_mul_of_nonneg_right P.γ₂_le_γ₃ hσ0⟩
  refine ⟨_, hacc, hacc.sigmaMin_le hσ, hacc.pos⟩

end Acceptance

/-- The termination test of an AR run: the Step-1 test or the post-step test holds at iteration
`k`. -/
abbrev IsARRun.Stop (stop₁ stop₂ : ℕ → Prop) (k : ℕ) : Prop := stop₁ k ∨ stop₂ k

/-- Without a post-step test, "no termination before `k`" is "the Step-1 test fails before `k`". -/
@[simp]
theorem IsARRun.forall_lt_not_stop_iff {stop₁ : ℕ → Prop} {k : ℕ} :
    (∀ j < k, ¬ IsARRun.Stop stop₁ (fun _ => False) j) ↔ ∀ j < k, ¬ stop₁ j := by
  simp [IsARRun.Stop]

/-- Without a post-step test, "no termination up to `k`" is "the Step-1 test fails up to `k`". -/
@[simp]
theorem IsARRun.forall_le_not_stop_iff {stop₁ : ℕ → Prop} {k : ℕ} :
    (∀ j ≤ k, ¬ IsARRun.Stop stop₁ (fun _ => False) j) ↔ ∀ j ≤ k, ¬ stop₁ j := by
  simp [IsARRun.Stop]

/-- Without a post-step test, the termination index is the first hit of the Step-1 test. -/
@[simp]
theorem IsARRun.isFirstHit_stop_iff {stop₁ : ℕ → Prop} {k : ℕ} :
    IsFirstHit (IsARRun.Stop stop₁ fun _ => False) k ↔ IsFirstHit stop₁ k := by
  simp [isFirstHit_iff, IsARRun.Stop]

/-- A run of an adaptive-regularization method ([cartis2022evaluation], Algorithms 2.4.1, 3.3.1,
4.1.1, 12.2.2, Steps 2–4). `stop₁ k` is the Step-1 termination test at iteration `k`, `stop₂ k` a
termination test evaluated after the step has been computed (`fun _ => False` for most methods),
`step k` the Step-2 conditions on the trial step `s k`, and `ρ k` the ratio of iteration `k`. The
run terminates at the first `k` with `stop₁ k ∨ stop₂ k`. Iteration `k` is successful iff
`P.η₁ ≤ ρ k`. -/
structure IsARRun {E : Type*} [Add E] (P : ARParams) (stop₁ step stop₂ : ℕ → Prop) (ρ : ℕ → ℝ)
    (x s : ℕ → E) (σ : ℕ → ℝ) : Prop where
  /-- The initial weight. -/
  sigma_zero : σ 0 = P.σ₀
  /-- Step 2 is executed at every iteration reached whose Step-1 test fails (also at an iteration
  that then stops by `stop₂`). -/
  step : ∀ k, (∀ j < k, ¬ IsARRun.Stop stop₁ stop₂ j) → ¬ stop₁ k → step k
  /-- Steps 3–4 are executed at every iteration before termination. -/
  accept : UntilHit (IsARRun.Stop stop₁ stop₂)
    fun k => ARAcceptance P (ρ k) (x k) (s k) (x (k + 1)) (σ k) (σ (k + 1))

/-- The ratio (2.4.3), (3.3.7), (4.1.15) of [cartis2022evaluation] for exact Taylor models: the
achieved decrease `f(x_k) - f(x_k + s_k)` over the Taylor decrement
`T_{f,p}(x_k, 0) - T_{f,p}(x_k, s_k)`. -/
noncomputable def taylorRatio {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → ℝ)
    (p : ℕ) (x s : ℕ → E) (k : ℕ) : ℝ :=
  reductionRatio f (x k) (s k) ((ftaylorSeries ℝ f (x k)).taylorDecrement p (s k))

theorem taylorRatio_def {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → ℝ)
    (p : ℕ) (x s : ℕ → E) (k : ℕ) :
    taylorRatio f p x s k =
      reductionRatio f (x k) (s k) ((ftaylorSeries ℝ f (x k)).taylorDecrement p (s k)) :=
  rfl

/-- The upper bound `σ_max = max(σ₀, γ₃ L / (1 - η₂))` on the regularization weight
([cartis2022evaluation], (4.1.19); (3.3.13) for `p = 2`; AR1's (2.4.9) is
`arSigmaMax P (L / 2)`). -/
noncomputable def arSigmaMax (P : ARParams) (L : ℝ) : ℝ := max P.σ₀ (P.γ₃ * L / (1 - P.η₂))

theorem arSigmaMax_def (P : ARParams) (L : ℝ) :
    arSigmaMax P L = max P.σ₀ (P.γ₃ * L / (1 - P.η₂)) := rfl

theorem σ₀_le_arSigmaMax (P : ARParams) (L : ℝ) : P.σ₀ ≤ arSigmaMax P L := le_max_left _ _

theorem arSigmaMax_pos (P : ARParams) (L : ℝ) : 0 < arSigmaMax P L :=
  P.σ₀_pos.trans_le (σ₀_le_arSigmaMax P L)

theorem arSigmaMax_mono (P : ARParams) {L L' : ℝ} (h : L ≤ L') :
    arSigmaMax P L ≤ arSigmaMax P L' :=
  max_le_max le_rfl (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h P.γ₃_pos.le)
    P.one_sub_η₂_pos.le)

namespace IsARRun

section General

variable {E : Type*} [Add E] {P : ARParams} {stop₁ step stop₂ : ℕ → Prop} {ρ : ℕ → ℝ}
  {x s : ℕ → E} {σ : ℕ → ℝ} (h : IsARRun P stop₁ step stop₂ ρ x s σ)
include h

/-- A run with a stronger step condition is a run with a weaker one. -/
theorem mono {step' : ℕ → Prop} (hst : ∀ k, step k → step' k) :
    IsARRun P stop₁ step' stop₂ ρ x s σ :=
  ⟨h.sigma_zero, fun k hk h1 => hst k (h.step k hk h1), h.accept⟩

/-- Step 2 holds at every iteration before termination. -/
theorem step_of_forall_le {k : ℕ} (hk : ∀ j ≤ k, ¬ Stop stop₁ stop₂ j) : step k :=
  h.step k (fun j hj => hk j hj.le) fun h1 => hk k le_rfl (Or.inl h1)

/-- The weight update before termination. -/
theorem update {k : ℕ} (hk : ∀ j ≤ k, ¬ Stop stop₁ stop₂ j) :
    ARUpdate P.η₁ P.η₂ P.γ₁ P.γ₂ P.γ₃ P.σmin (ρ k) (σ k) (σ (k + 1)) :=
  (h.accept k hk).update

/-- A successful iteration before termination moves to the trial point. -/
theorem eq_add_of_succ {k : ℕ} (hk : ∀ j ≤ k, ¬ Stop stop₁ stop₂ j) (hs : P.η₁ ≤ ρ k) :
    x (k + 1) = x k + s k :=
  (h.accept k hk).eq_add hs

/-- An unsuccessful iteration before termination keeps the iterate. -/
theorem eq_of_not_succ {k : ℕ} (hk : ∀ j ≤ k, ¬ Stop stop₁ stop₂ j) (hs : ρ k < P.η₁) :
    x (k + 1) = x k :=
  (h.accept k hk).eq_self hs

private theorem updates {K : ℕ} (hK : ∀ j < K, ¬ Stop stop₁ stop₂ j) :
    ∀ k < K, ARUpdate P.η₁ P.η₂ P.γ₁ P.γ₂ P.γ₃ P.σmin (ρ k) (σ k) (σ (k + 1)) :=
  fun _ hk => h.update fun j hj => hK j (hj.trans_lt hk)

/-- The weights are positive up to (and including) the first termination index. -/
theorem sigma_pos {K : ℕ} (hK : ∀ j < K, ¬ Stop stop₁ stop₂ j) : ∀ k ≤ K, 0 < σ k :=
  pos_of_arUpdate P.γ₁_pos P.γ₂_pos (h.sigma_zero ▸ P.σ₀_pos) (h.updates hK)

/-- The weights stay above `σ_min` up to (and including) the first termination index. -/
theorem sigmaMin_le {K : ℕ} (hK : ∀ j < K, ¬ Stop stop₁ stop₂ j) : ∀ k ≤ K, P.σmin ≤ σ k :=
  le_sigma_of_arUpdate P.σmin_nonneg P.one_le_γ₂ (h.sigma_zero ▸ P.σmin_le_σ₀) (h.updates hK)

/-- **Upper bound on the regularization weight** for any AR run (the mechanism of
[cartis2022evaluation], Lemmas 2.4.2, 3.3.2, 4.1.2, 13.1.14, 14.1.6): if every iteration before
termination with `σ_k ≥ σ̄` is very successful, then up to (and including) the first termination
index, `σ_min ≤ σ_k`, `0 < σ_k` and `σ_k ≤ max(σ₀, γ₃ σ̄)`. -/
theorem sigma_le_max {σbar : ℝ}
    (hforce : ∀ k, (∀ j ≤ k, ¬ Stop stop₁ stop₂ j) → σbar ≤ σ k → P.η₂ ≤ ρ k) {K : ℕ}
    (hK : ∀ j < K, ¬ Stop stop₁ stop₂ j) :
    ∀ k ≤ K, P.σmin ≤ σ k ∧ 0 < σ k ∧ σ k ≤ max P.σ₀ (P.γ₃ * σbar) := by
  have hmax := sigma_le_max_of_arUpdate P.γ₁_pos P.γ₂_pos P.γ₂_le_γ₃ P.one_le_γ₃
    (h.sigma_zero ▸ P.σ₀_pos) (h.updates hK)
    (fun k hk => hforce k fun j hj => hK j (hj.trans_lt hk))
  rw [h.sigma_zero] at hmax
  exact fun k hk => ⟨h.sigmaMin_le hK k hk, h.sigma_pos hK k hk, hmax k hk⟩

/-- **The iterates stay in a set** `C` containing `x₀` and every accepted trial point: up to (and
including) the first termination index, `x_k ∈ C`. -/
theorem mem {C : Set E} (h0 : x 0 ∈ C)
    (hC : ∀ k, (∀ j ≤ k, ¬ Stop stop₁ stop₂ j) → x k ∈ C → P.η₁ ≤ ρ k → x k + s k ∈ C) :
    ∀ k, (∀ j < k, ¬ Stop stop₁ stop₂ j) → x k ∈ C := by
  intro k
  induction k with
  | zero => exact fun _ => h0
  | succ k ih =>
    intro hk
    have hk' : ∀ j ≤ k, ¬ Stop stop₁ stop₂ j := fun j hj => hk j (Nat.lt_succ_of_le hj)
    have hxk := ih fun j hj => hk' j hj.le
    by_cases hs : P.η₁ ≤ ρ k
    · rw [h.eq_add_of_succ hk' hs]
      exact hC k hk' hxk hs
    · rwa [h.eq_of_not_succ hk' (not_le.1 hs)]

/-- **Lemma 2.4.1** ([cartis2022evaluation]) for any AR run: if `k` is before termination and
`σ_{k+1} ≤ σmax`, then `k + 1 ≤ |𝒮_k| (1 + |log γ₁| / log γ₂) + log (σmax / σ₀) / log γ₂`, with
`𝒮_k = {j ≤ k | η₁ ≤ ρ_j}`. -/
theorem succ_count {σmax : ℝ} {k : ℕ} (hk : ∀ j ≤ k, ¬ Stop stop₁ stop₂ j)
    (hmax : σ (k + 1) ≤ σmax) :
    (k + 1 : ℝ) ≤
      (successSet (fun j => P.η₁ ≤ ρ j) k).card * (1 + |Real.log P.γ₁| / Real.log P.γ₂) +
        Real.log (σmax / P.σ₀) / Real.log P.γ₂ := by
  rw [← h.sigma_zero]
  exact succ_le_of_arUpdate P.γ₁_pos P.γ₁_le_one P.one_lt_γ₂ (h.sigma_zero ▸ P.σ₀_pos)
    (fun j hj => h.update fun i hi => hk i (hi.trans hj)) hmax

/-- **Lemma 2.4.1** ([cartis2022evaluation], (2.4.8)) with the book's indexing: if the run has not
terminated before `k` and `σ_k ≤ σmax`, then
`k ≤ |𝒮_k| (1 + |log γ₁| / log γ₂) + log (σmax / σ₀) / log γ₂`. -/
theorem le_succ_count {σmax : ℝ} {k : ℕ} (hk : ∀ j < k, ¬ Stop stop₁ stop₂ j)
    (hmax : σ k ≤ σmax) :
    (k : ℝ) ≤
      (successSet (fun j => P.η₁ ≤ ρ j) k).card * (1 + |Real.log P.γ₁| / Real.log P.γ₂) +
        Real.log (σmax / P.σ₀) / Real.log P.γ₂ := by
  rw [← h.sigma_zero]
  exact le_of_arUpdate P.γ₁_pos P.γ₁_le_one P.one_lt_γ₂ (h.sigma_zero ▸ P.σ₀_pos)
    (h.updates hk) hmax

/-- **Decrease on successful iterations** ([cartis2022evaluation], (4.1.37)): if, before
termination, `ρ_k` is the reduction ratio of an objective `w` with a positive predicted decrease
`pred_k` and the iteration is successful, then `x_{k+1} = x_k + s_k` and
`w(x_k) - w(x_{k+1}) ≥ η₁ pred_k`. -/
theorem sub_ge_of_succ {w : E → ℝ} {pred : ℕ → ℝ} {k : ℕ}
    (hk : ∀ j ≤ k, ¬ Stop stop₁ stop₂ j) (hρ : ρ k = reductionRatio w (x k) (s k) (pred k))
    (hpred : 0 < pred k) (hs : P.η₁ ≤ ρ k) :
    x (k + 1) = x k + s k ∧ P.η₁ * pred k ≤ w (x k) - w (x (k + 1)) :=
  ⟨h.eq_add_of_succ hk hs, (h.accept k hk).sub_ge hρ hpred hs⟩

/-- **Monotonicity of the objective**: if the ratios are reduction ratios of an objective `w` with
positive predicted decreases before termination, then `w ∘ x` is nonincreasing up to (and
including) the first termination index. -/
theorem objective_antitone {w : E → ℝ} {pred : ℕ → ℝ} {K : ℕ}
    (hK : ∀ j < K, ¬ Stop stop₁ stop₂ j)
    (hρ : ∀ k < K, ρ k = reductionRatio w (x k) (s k) (pred k)) (hpred : ∀ k < K, 0 < pred k) :
    ∀ i j, i ≤ j → j ≤ K → w (x j) ≤ w (x i) := by
  intro i j hij hjK
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j _ ih =>
    have hjK' : j < K := hjK
    exact ((h.accept j fun i hi => hK i (hi.trans_lt hjK')).le (hρ j hjK') (hpred j hjK')).trans
      (ih hjK'.le)

/-- The counting core of the complexity theorems: if the weights are bounded by `σmax` and the
number of successful iterations by `N ≥ 0` before termination, the run terminates with
`k_ε + 1 ≤ κA N + log(σmax/σ₀)/log γ₂ + 1` and `#derivative evaluations ≤ N + 1`. -/
private theorem exists_isFirstHit_of_card_le {σmax : ℝ}
    (hσmax : ∀ k, (∀ j < k, ¬ Stop stop₁ stop₂ j) → σ k ≤ σmax) {N : ℝ} (hN : 0 ≤ N)
    (hsucc : ∀ k, (∀ j ≤ k, ¬ Stop stop₁ stop₂ j) →
      ((successSet (fun j => P.η₁ ≤ ρ j) k).card : ℝ) ≤ N) :
    ∃ kε, IsFirstHit (Stop stop₁ stop₂) kε ∧
      (funEvalCount kε : ℝ) ≤ (1 + |Real.log P.γ₁| / Real.log P.γ₂) * N +
        Real.log (σmax / P.σ₀) / Real.log P.γ₂ + 1 ∧
      (derivEvalCount (fun k => P.η₁ ≤ ρ k) kε : ℝ) ≤ N + 1 := by
  have hσ₀ : P.σ₀ ≤ σmax := h.sigma_zero ▸ hσmax 0 fun _ h => absurd h (Nat.not_lt_zero _)
  have hlog := P.log_γ₂_pos
  have hA : 0 ≤ 1 + |Real.log P.γ₁| / Real.log P.γ₂ := by positivity
  have hB : 0 ≤ Real.log (σmax / P.σ₀) / Real.log P.γ₂ :=
    div_nonneg (Real.log_nonneg ((one_le_div P.σ₀_pos).2 hσ₀)) hlog.le
  refine exists_isFirstHit_evalCount_le_of_counting hA hN (by positivity) (fun k hk => ?_) hsucc
  have := h.succ_count hk (hσmax (k + 1) fun j hj => hk j (Nat.lt_succ_iff.1 hj))
  linarith

/-- **Complexity skeleton of AR methods** (the common end of the proofs of Theorems 2.4.4, 3.3.5,
4.1.5, 5.1.7, 6.2.3, 6.2.5, 6.3.1, 12.2.14, 14.1.10 of [cartis2022evaluation]). Let the weights be
bounded by `σmax ≥ σ₀` up to termination, and let `V` be a potential (e.g. `V_k = f(x_k)`) that is
nonincreasing before termination, bounded below by `Vlow` up to termination, and decreases by at
least `δ > 0` at every successful iteration `k` before termination such that `k + 1` is not the
termination index. Then the run terminates at some `k_ε` with
`#f-evaluations = k_ε + 1 ≤ κA (V₀ - Vlow)/δ + κC` and
`#derivative evaluations ≤ (V₀ - Vlow)/δ + 2`, where `κA = 1 + |log γ₁| / log γ₂` and
`κC = (|log γ₁| + log (σmax / σ₀)) / log γ₂ + 2` (the book's (4.1.46); the `2` accounts for the
initial evaluation and for the last successful iteration). (`σmax ≥ σ₀` follows from the bound at
`k = 0`.) -/
theorem exists_isFirstHit_of_decrease {σmax : ℝ}
    (hσmax : ∀ k, (∀ j < k, ¬ Stop stop₁ stop₂ j) → σ k ≤ σmax) {V : ℕ → ℝ} {Vlow δ : ℝ}
    (hδ : 0 < δ) (hmono : ∀ k, (∀ j ≤ k, ¬ Stop stop₁ stop₂ j) → V (k + 1) ≤ V k)
    (hlow : ∀ k, (∀ j < k, ¬ Stop stop₁ stop₂ j) → Vlow ≤ V k)
    (hdec : ∀ k, (∀ j ≤ k + 1, ¬ Stop stop₁ stop₂ j) → P.η₁ ≤ ρ k → δ ≤ V k - V (k + 1)) :
    ∃ kε, IsFirstHit (Stop stop₁ stop₂) kε ∧
      (funEvalCount kε : ℝ) ≤ (1 + |Real.log P.γ₁| / Real.log P.γ₂) * ((V 0 - Vlow) / δ) +
        ((|Real.log P.γ₁| + Real.log (σmax / P.σ₀)) / Real.log P.γ₂ + 2) ∧
      (derivEvalCount (fun k => P.η₁ ≤ ρ k) kε : ℝ) ≤ (V 0 - Vlow) / δ + 2 := by
  set succ := fun k => P.η₁ ≤ ρ k
  have hV0 : 0 ≤ V 0 - Vlow := sub_nonneg.2 (hlow 0 fun _ h => absurd h (Nat.not_lt_zero _))
  have hsucc : ∀ k, (∀ j ≤ k, ¬ Stop stop₁ stop₂ j) →
      ((successSet succ k).card : ℝ) ≤ (V 0 - Vlow) / δ + 1 := by
    intro k hk
    cases k with
    | zero =>
      have : (successSet succ 0).card ≤ 1 := card_successSet_le
      have : ((successSet succ 0).card : ℝ) ≤ 1 := by exact_mod_cast this
      have : (0 : ℝ) ≤ (V 0 - Vlow) / δ := div_nonneg hV0 hδ.le
      linarith
    | succ m =>
      have hcard := card_mul_le_of_decrease (c := δ) (k := m)
        (T := successSet succ m) successSet_subset_range
        (fun j hj => hmono j fun i hi => hk i (hi.trans (hj.trans m.le_succ)))
        (fun j hj => by
          rw [mem_successSet] at hj
          exact hdec j (fun i hi => hk i (hi.trans (Nat.succ_le_succ hj.1))) hj.2)
        (hlow (m + 1) fun j hj => hk j hj.le)
      have h1 : ((successSet succ m).card : ℝ) ≤ (V 0 - Vlow) / δ := by
        rw [le_div_iff₀ hδ]; linarith
      have h2 : ((successSet succ (m + 1)).card : ℝ) ≤ (successSet succ m).card + 1 := by
        exact_mod_cast card_successSet_add_one_le
      linarith
  obtain ⟨k, hk, hF, hD⟩ := h.exists_isFirstHit_of_card_le hσmax
    (by have := div_nonneg hV0 hδ.le; positivity) hsucc
  have hlog := P.log_γ₂_pos
  refine ⟨k, hk, hF.trans_eq ?_, hD.trans_eq ?_⟩
  · field_simp
    ring
  · ring

/-- **Complexity skeleton with the decrease at the current iterate** (the AR1 variant, the end of
the proof of Theorem 2.4.4 of [cartis2022evaluation]): as
`Optimization.IsARRun.exists_isFirstHit_of_decrease`, but with the decrease `δ` guaranteed at every
successful iteration `k` before termination (the test failing at `k` suffices). Then
`#f-evaluations ≤ κA (V₀ - Vlow)/δ + log (σmax / σ₀) / log γ₂ + 1` and
`#derivative evaluations ≤ (V₀ - Vlow)/δ + 1`, with `κA = 1 + |log γ₁| / log γ₂`. -/
theorem exists_isFirstHit_of_decrease_of_le {σmax : ℝ}
    (hσmax : ∀ k, (∀ j < k, ¬ Stop stop₁ stop₂ j) → σ k ≤ σmax) {V : ℕ → ℝ} {Vlow δ : ℝ}
    (hδ : 0 < δ) (hmono : ∀ k, (∀ j ≤ k, ¬ Stop stop₁ stop₂ j) → V (k + 1) ≤ V k)
    (hlow : ∀ k, (∀ j < k, ¬ Stop stop₁ stop₂ j) → Vlow ≤ V k)
    (hdec : ∀ k, (∀ j ≤ k, ¬ Stop stop₁ stop₂ j) → P.η₁ ≤ ρ k → δ ≤ V k - V (k + 1)) :
    ∃ kε, IsFirstHit (Stop stop₁ stop₂) kε ∧
      (funEvalCount kε : ℝ) ≤ (1 + |Real.log P.γ₁| / Real.log P.γ₂) * ((V 0 - Vlow) / δ) +
        Real.log (σmax / P.σ₀) / Real.log P.γ₂ + 1 ∧
      (derivEvalCount (fun k => P.η₁ ≤ ρ k) kε : ℝ) ≤ (V 0 - Vlow) / δ + 1 := by
  have hV0 : 0 ≤ V 0 - Vlow := sub_nonneg.2 (hlow 0 fun _ h => absurd h (Nat.not_lt_zero _))
  refine h.exists_isFirstHit_of_card_le hσmax (div_nonneg hV0 hδ.le) fun k hk => ?_
  have hcard := card_mul_le_of_decrease (c := δ) (k := k)
    (T := successSet (fun j => P.η₁ ≤ ρ j) k) successSet_subset_range
    (fun j hj => hmono j fun i hi => hk i (hi.trans hj))
    (fun j hj => by
      rw [mem_successSet] at hj
      exact hdec j (fun i hi => hk i (hi.trans hj.1)) hj.2)
    (hlow (k + 1) fun j hj => hk j (Nat.lt_succ_iff.1 hj))
  rw [le_div_iff₀ hδ]; linarith

omit h in
/-- In a run without post-step test, an iterate different from the starting point was reached by
a successful iteration: the last successful iteration `i < N` has `x_{i+1} = x_N`. -/
theorem exists_last_succ (h : IsARRun P stop₁ step (fun _ => False) ρ x s σ) :
    ∀ N, (∀ j < N, ¬ stop₁ j) → x N ≠ x 0 → ∃ i < N, P.η₁ ≤ ρ i ∧ x (i + 1) = x N := by
  intro N
  induction N with
  | zero => exact fun _ h0 => absurd rfl h0
  | succ N ih =>
    intro hN hne
    have hle : ∀ j ≤ N, ¬ IsARRun.Stop stop₁ (fun _ => False) j :=
      forall_le_not_stop_iff.2 fun j hj => hN j (Nat.lt_succ_of_le hj)
    by_cases hs : P.η₁ ≤ ρ N
    · exact ⟨N, N.lt_succ_self, hs, rfl⟩
    · have heq := h.eq_of_not_succ hle (not_le.1 hs)
      obtain ⟨i, hi, hsi, hxi⟩ := ih (fun j hj => hN j (hj.trans N.lt_succ_self))
        (heq ▸ hne)
      exact ⟨i, hi.trans N.lt_succ_self, hsi, hxi.trans heq.symm⟩

end General

section Taylor

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {P : ARParams}
  {stop₁ step stop₂ : ℕ → Prop} {x s : ℕ → E} {σ : ℕ → ℝ} {f : E → ℝ} {p : ℕ}

/-- **Decrease on successful iterations with exact Taylor models** ([cartis2022evaluation],
Lemma 4.1.1 and (4.1.37)): if, before termination, the step decreases the regularized model
`m_k` and iteration `k` is successful for the ratio `taylorRatio f p x s`, then
`x_{k+1} = x_k + s_k` and `f(x_k) - f(x_{k+1}) ≥ η₁ σ_k/(p+1)! ‖s_k‖^{p+1}`. -/
theorem sub_ge_of_succ_taylor (h : IsARRun P stop₁ step stop₂ (taylorRatio f p x s) x s σ)
    {k : ℕ} (hk : ∀ j ≤ k, ¬ Stop stop₁ stop₂ j)
    (hm : regularizedModel (ftaylorSeries ℝ f (x k)) p (σ k) (s k) <
      regularizedModel (ftaylorSeries ℝ f (x k)) p (σ k) 0)
    (hs : P.η₁ ≤ taylorRatio f p x s k) :
    x (k + 1) = x k + s k ∧
      P.η₁ * (σ k / ((p + 1)! : ℝ) * ‖s k‖ ^ (p + 1)) ≤ f (x k) - f (x (k + 1)) := by
  have hσ : 0 ≤ σ k := (h.sigma_pos (K := k) (fun j hj => hk j hj.le) k le_rfl).le
  have hdec := lt_taylorDecrement_of_regularizedModel_lt hm
  have hpos : 0 < (ftaylorSeries ℝ f (x k)).taylorDecrement p (s k) :=
    lt_of_le_of_lt (by positivity) hdec
  obtain ⟨heq, hge⟩ := h.sub_ge_of_succ (w := f)
    (pred := fun k => (ftaylorSeries ℝ f (x k)).taylorDecrement p (s k)) hk rfl hpos hs
  exact ⟨heq, (mul_le_mul_of_nonneg_left hdec.le P.η₁_pos.le).trans hge⟩

/-- **Lemma 4.1.2** ([cartis2022evaluation], (4.1.19)) for every AR method with exact Taylor
models, also on a convex feasible set (Section 6.2.2: "Lemmas 4.1.1 and 4.1.2 continue to hold").
Let `f` be `C^p` on a convex set `C ∋ x₀` with `L`-Lipschitz `∇^p f` there, and let every step
computed before termination keep the trial point in `C` and decrease the regularized model
(4.1.10). Then up to (and including) the first termination index, `x_k ∈ C`, `σ_min ≤ σ_k` and
`σ_k ≤ σ_max = max(σ₀, γ₃ L / (1 - η₂))`. (A post-step test `stop₂` such as ARqp's
`m_k(s_k) = m_k(0)` may be used to supply the strict model decrease before termination.) -/
theorem sigma_le (h : IsARRun P stop₁ step stop₂ (taylorRatio f p x s) x s σ) {C : Set E}
    {L : ℝ} (hC : Convex ℝ C) (hf : ∀ y ∈ C, ContDiffAt ℝ p f y)
    (hL : IteratedFDerivLipschitzOn f p L C) (hx0 : x 0 ∈ C)
    (hstep : ∀ k, (∀ j ≤ k, ¬ Stop stop₁ stop₂ j) → step k →
      x k + s k ∈ C ∧ regularizedModel (ftaylorSeries ℝ f (x k)) p (σ k) (s k) <
        regularizedModel (ftaylorSeries ℝ f (x k)) p (σ k) 0) :
    ∀ k, (∀ j < k, ¬ Stop stop₁ stop₂ j) → x k ∈ C ∧ P.σmin ≤ σ k ∧ σ k ≤ arSigmaMax P L := by
  have hmem := h.mem (C := C) hx0 fun k hk _ _ => (hstep k hk (h.step_of_forall_le hk)).1
  have hforce : ∀ k, (∀ j ≤ k, ¬ Stop stop₁ stop₂ j) → L / (1 - P.η₂) ≤ σ k →
      P.η₂ ≤ taylorRatio f p x s k := by
    intro k hk hσk
    obtain ⟨hxs, hm⟩ := hstep k hk (h.step_of_forall_le hk)
    have hσpos : 0 < σ k := h.sigma_pos (K := k) (fun j hj => hk j hj.le) k le_rfl
    have hdec := (lt_taylorDecrement_of_regularizedModel_lt hm).le
    have hfac : (0 : ℝ) < (p + 1)! := by positivity
    refine le_reductionRatio_of_lipschitz hC hf hL (hmem k fun j hj => hk j hj.le) hxs
      (ne_zero_of_regularizedModel_lt hm) (c := 1 / ((p + 1)! : ℝ)) (by positivity) hσpos
      (by rw [one_div_mul_eq_div]; exact hdec) ?_
    rw [div_le_iff₀ P.one_sub_η₂_pos] at hσk
    rw [mul_one_div_cancel hfac.ne', one_mul]
    exact hσk
  intro k hk
  obtain ⟨hmin, -, hmax⟩ := h.sigma_le_max hforce hk k le_rfl
  refine ⟨hmem k hk, hmin, hmax.trans_eq ?_⟩
  rw [arSigmaMax_def, mul_div_assoc]

end Taylor

end IsARRun

section Existence

/-- The previous iterate, weight and step of a run (`none` at iteration `0`): what a termination
test reading the previous iteration (such as ARp's third-order test through the set `𝓜_k` of
(4.1.14)) may depend on. -/
def prevIterate {E : Type*} (x s : ℕ → E) (σ : ℕ → ℝ) : ℕ → Option (E × ℝ × E)
  | 0 => none
  | k + 1 => some (x k, σ k, s k)

@[simp]
theorem prevIterate_zero {E : Type*} (x s : ℕ → E) (σ : ℕ → ℝ) : prevIterate x s σ 0 = none :=
  rfl

@[simp]
theorem prevIterate_succ {E : Type*} (x s : ℕ → E) (σ : ℕ → ℝ) (k : ℕ) :
    prevIterate x s σ (k + 1) = some (x k, σ k, s k) := rfl

variable {E : Type*} [Add E]

/-- **Existence of AR runs** whose termination test reads the current iterate and weight and the
previous iteration (as `prevIterate`). Let `Inv` be a property of iterates (e.g. membership in a
feasible set) and assume that at every iterate `y` with `Inv y`, every weight `σ ≥ σ_min`, `σ > 0`,
and every previous iteration at which the test fails, an admissible step `s` exists
(`stepOK y σ s`) with `Inv (y + s)`. Then from every `x₀` with `Inv x₀` there is a run with ratio
`ρ_k = R (x k) (σ k) (s k)` (any ratio function), along which `Inv` holds up to (and including)
termination. The new weights are the left ends of the intervals of (2.4.4). -/
theorem exists_isARRun_prev (P : ARParams) {Inv : E → Prop}
    {test : Option (E × ℝ × E) → E → ℝ → Prop} {stepOK : E → ℝ → E → Prop}
    (R : E → ℝ → E → ℝ)
    (hstep : ∀ prev y σ, Inv y → P.σmin ≤ σ → 0 < σ → ¬ test prev y σ →
      ∃ s, stepOK y σ s ∧ Inv (y + s))
    {x₀ : E} (hx₀ : Inv x₀) :
    ∃ x s : ℕ → E, ∃ σ : ℕ → ℝ, x 0 = x₀ ∧
      IsARRun P (fun k => test (prevIterate x s σ k) (x k) (σ k))
        (fun k => stepOK (x k) (σ k) (s k)) (fun _ => False) (fun k => R (x k) (σ k) (s k))
        x s σ ∧
      ∀ k, (∀ j < k, ¬ test (prevIterate x s σ j) (x j) (σ j)) → Inv (x k) := by
  classical
  -- states `(x_k, σ_k, s_k, previous iteration)`
  let good : Option (E × ℝ × E) → E → ℝ → E → Prop := fun prev y σ s =>
    ¬ test prev y σ → stepOK y σ s ∧ Inv (y + s)
  have hchoose : ∀ prev y σ, Inv y → P.σmin ≤ σ → 0 < σ → ∃ s, good prev y σ s := by
    intro prev y σ hy hσ hσ0
    by_cases ht : test prev y σ
    · exact ⟨y, fun h' => absurd ht h'⟩
    · obtain ⟨s, hs⟩ := hstep prev y σ hy hσ hσ0 ht
      exact ⟨s, fun _ => hs⟩
  obtain ⟨s₀, hs₀⟩ := hchoose none x₀ P.σ₀ hx₀ P.σmin_le_σ₀ P.σ₀_pos
  obtain ⟨r, hr0, hr⟩ := exists_run_of_forall_exists_of_invariant
    (α := E × ℝ × E × Option (E × ℝ × E))
    (init := fun a => a = (x₀, P.σ₀, s₀, none))
    (inv := fun _ a => Inv a.1 ∧ P.σmin ≤ a.2.1 ∧ 0 < a.2.1 ∧ good a.2.2.2 a.1 a.2.1 a.2.2.1)
    (stop := fun _ a => test a.2.2.2 a.1 a.2.1)
    (step := fun _ a b => ARAcceptance P (R a.1 a.2.1 a.2.2.1) a.1 a.2.2.1 b.1 a.2.1 b.2.1 ∧
      b.2.2.2 = some (a.1, a.2.1, a.2.2.1))
    ⟨_, rfl⟩
    (fun a ha => by
      subst ha
      exact ⟨hx₀, P.σmin_le_σ₀, P.σ₀_pos, hs₀⟩)
    (fun k a ha hnot => by
      obtain ⟨hInv, hmin, hpos, hgood⟩ := ha
      obtain ⟨hstepa, hInvs⟩ := hgood hnot
      obtain ⟨σ', hacc, hmin', hpos'⟩ :=
        exists_arAcceptance P (R a.1 a.2.1 a.2.2.1) a.1 a.2.2.1 hmin
      set x' := if P.η₁ ≤ R a.1 a.2.1 a.2.2.1 then a.1 + a.2.2.1 else a.1
      have hInv' : Inv x' := by
        rcases hacc.eq_add_or_eq_self with h' | h'
        · rw [h']; exact hInvs
        · rw [h']; exact hInv
      obtain ⟨s', hs'⟩ := hchoose (some (a.1, a.2.1, a.2.2.1)) x' σ' hInv' hmin' (hpos' hpos)
      exact ⟨(x', σ', s', some (a.1, a.2.1, a.2.2.1)), ⟨hInv', hmin', hpos' hpos, hs'⟩, hacc, rfl⟩)
  set x : ℕ → E := fun k => (r k).1
  set σ : ℕ → ℝ := fun k => (r k).2.1
  set s : ℕ → E := fun k => (r k).2.2.1
  have hprev : ∀ k, (∀ j < k, ¬ test (r j).2.2.2 (r j).1 (r j).2.1) →
      (r k).2.2.2 = prevIterate x s σ k := by
    intro k hk
    cases k with
    | zero => rw [hr0]; rfl
    | succ k => exact (hr k fun j hj => hk j (Nat.lt_succ_of_le hj)).2.2
  have hstopped : ∀ k, (∀ j < k, ¬ test (prevIterate x s σ j) (x j) (σ j)) →
      ∀ j < k, ¬ test (r j).2.2.2 (r j).1 (r j).2.1 := by
    intro k
    induction k with
    | zero => exact fun _ j hj => absurd hj (Nat.not_lt_zero _)
    | succ k ih =>
      intro hk j hj
      have ih' := ih fun i hi => hk i (hi.trans k.lt_succ_self)
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · exact ih' j hj
      · rw [hprev j ih']
        exact hk j j.lt_succ_self
  have hle : ∀ k, (∀ j ≤ k, ¬ (test (prevIterate x s σ j) (x j) (σ j) ∨ False)) →
      ∀ j ≤ k, ¬ test (r j).2.2.2 (r j).1 (r j).2.1 := by
    intro k hk j hj
    exact hstopped (k + 1) (fun i hi => fun h' => hk i (Nat.lt_succ_iff.1 hi) (Or.inl h')) j
      (Nat.lt_succ_of_le hj)
  refine ⟨x, s, σ, by simp [x, hr0], ⟨by simp [σ, hr0], ?_, ?_⟩, ?_⟩
  · intro k hk h1
    have hk' := hle k (fun j hj => by
      rcases hj.lt_or_eq with hj | rfl
      · exact hk j hj
      · simpa using h1)
    have hp := hprev k fun j hj => hk' j hj.le
    have hgood := (hr k hk').1.2.2.2
    exact (hgood (by rw [hp]; exact h1)).1
  · intro k hk
    exact (hr k (hle k hk)).2.1
  · intro k hk
    cases k with
    | zero => simpa [x, hr0] using hx₀
    | succ k =>
      have hk' := hstopped (k + 1) hk
      have hall : ∀ j ≤ k, ¬ test (r j).2.2.2 (r j).1 (r j).2.1 :=
        fun j hj => hk' j (Nat.lt_succ_of_le hj)
      obtain ⟨⟨hInv, -, -, hgood⟩, hacc, -⟩ := hr k hall
      rcases hacc.eq_add_or_eq_self with h' | h'
      · change Inv (r (k + 1)).1
        rw [h']
        exact (hgood (hall k le_rfl)).2
      · change Inv (r (k + 1)).1
        rw [h']
        exact hInv

/-- **Existence of AR runs** with a state-based ("Markov") termination test (AR1, AR2, ARp with
`q ≤ 2`, ARp-CC, ARp1-CC, ARpLE-CC, the inner runs of TPp-GC): if at every iterate `y` with
`Inv y` at which the test fails, and every weight `σ ≥ σ_min`, `σ > 0`, an admissible step exists
that keeps `Inv`, then from every `x₀` with `Inv x₀` there is a run, along which `Inv` holds up to
(and including) termination. -/
theorem exists_isARRun (P : ARParams) {Inv : E → Prop} {test : E → Prop}
    {stepOK : E → ℝ → E → Prop} (R : E → ℝ → E → ℝ)
    (hstep : ∀ y σ, Inv y → P.σmin ≤ σ → 0 < σ → ¬ test y → ∃ s, stepOK y σ s ∧ Inv (y + s))
    {x₀ : E} (hx₀ : Inv x₀) :
    ∃ x s : ℕ → E, ∃ σ : ℕ → ℝ, x 0 = x₀ ∧
      IsARRun P (fun k => test (x k)) (fun k => stepOK (x k) (σ k) (s k)) (fun _ => False)
        (fun k => R (x k) (σ k) (s k)) x s σ ∧
      ∀ k, (∀ j < k, ¬ test (x j)) → Inv (x k) :=
  exists_isARRun_prev P (test := fun _ y _ => test y) R
    (fun _ y σ hy hσ hσ0 ht => hstep y σ hy hσ hσ0 ht) hx₀

end Existence

end Optimization
