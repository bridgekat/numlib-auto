import Numlib.Optimization.ModelBased.TrustRegionUpdate
import Numlib.Optimization.ModelBased.RatioTest

/-!
# Generic runs of trust-region methods

Every trust-region (TR) method of [cartis2022evaluation] (Algorithms 2.3.1 TR1, 3.2.1 TR2,
3.4.1 TRε, 12.2.1 TRq and its simply constrained variant of §14.2; per iteration also the
trial iterations of 13.1.1 TRqIDA and 13.3.1 TRqEDA) shares Steps 3–4: given the ratio `ρ_k` of
achieved to predicted decrease, the trial point `x_k + s_k` is accepted iff `η₁ ≤ ρ_k`, and the
radius is updated by (2.3.7) (`Optimization.TRUpdate`). The methods differ only in the Step-1
termination test, the Step-2 conditions on the step (which include the trust-region constraint)
and the predicted decrease entering `ρ_k`.

* `Optimization.TRParams`: the constants `Δ₀, η₁, η₂, γ₁, γ₂, γ₃` of (2.3.3).
* `Optimization.TRAcceptance P ρ x s x' Δ Δ'`: Steps 3–4 of one iteration, with its API
  (`TRAcceptance.eq_add`, `TRAcceptance.eq_self`, `TRAcceptance.sub_ge`,
  `Optimization.exists_trAcceptance`).
* `Optimization.IsTRRun P stop step ρ x s Δ`: a run, the rules being imposed only before
  termination (`Optimization.UntilHit`).
* Consequences for every run: positivity and the lower bound on the radius
  (`IsTRRun.delta_ge`, the mechanism of Lemmas 2.3.4, 3.2.5, 12.2.3), the count of all iterations
  in terms of the successful ones (`IsTRRun.succ_count`, Lemma 2.3.1) and the decrease on
  successful iterations (`IsTRRun.sub_ge_of_succ`).

A cap `Δ_{k+1} ≤ Δ_max` (TRq) is an additional condition of the method-specific predicates; the
canonical successor radius of `Optimization.exists_trAcceptance` never exceeds `Δ_k`, so it is
compatible with any cap.
-/

namespace Optimization

/-- The constants of a trust-region method ([cartis2022evaluation], (2.3.3), Step 0 of
Algorithms 2.3.1, 12.2.1, 13.1.1): the initial radius `Δ₀ > 0`, the acceptance thresholds
`0 < η₁ ≤ η₂ < 1` and the radius factors `0 < γ₁ ≤ γ₂ < 1 ≤ γ₃`. -/
structure TRParams where
  /-- The initial trust-region radius. -/
  Δ₀ : ℝ
  /-- The threshold for successful iterations. -/
  η₁ : ℝ
  /-- The threshold for very successful iterations. -/
  η₂ : ℝ
  /-- The smallest shrinking factor. -/
  γ₁ : ℝ
  /-- The largest shrinking factor. -/
  γ₂ : ℝ
  /-- The largest expansion factor. -/
  γ₃ : ℝ
  /-- `Δ₀ > 0`. -/
  Δ₀_pos : 0 < Δ₀
  /-- `η₁ > 0`. -/
  η₁_pos : 0 < η₁
  /-- `η₁ ≤ η₂`. -/
  η₁_le_η₂ : η₁ ≤ η₂
  /-- `η₂ < 1`. -/
  η₂_lt_one : η₂ < 1
  /-- `γ₁ > 0`. -/
  γ₁_pos : 0 < γ₁
  /-- `γ₁ ≤ γ₂`. -/
  γ₁_le_γ₂ : γ₁ ≤ γ₂
  /-- `γ₂ < 1`. -/
  γ₂_lt_one : γ₂ < 1
  /-- `γ₃ ≥ 1`. -/
  one_le_γ₃ : 1 ≤ γ₃

namespace TRParams

variable (P : TRParams)

theorem γ₂_pos : 0 < P.γ₂ := P.γ₁_pos.trans_le P.γ₁_le_γ₂

theorem γ₁_le_one : P.γ₁ ≤ 1 := P.γ₁_le_γ₂.trans P.γ₂_lt_one.le

theorem γ₃_pos : 0 < P.γ₃ := one_pos.trans_le P.one_le_γ₃

theorem η₂_pos : 0 < P.η₂ := P.η₁_pos.trans_le P.η₁_le_η₂

theorem one_sub_η₂_pos : 0 < 1 - P.η₂ := sub_pos.2 P.η₂_lt_one

theorem γ₁_lt_one : P.γ₁ < 1 := P.γ₁_le_γ₂.trans_lt P.γ₂_lt_one

end TRParams

section Acceptance

variable {E : Type*} [Add E]

/-- Steps 3–4 of a trust-region method for one iteration ([cartis2022evaluation], (2.3.6)–(2.3.7),
(12.2.4)–(12.2.5), (13.1.16)–(13.1.17)): given the ratio `ρ`, the new iterate `x'` is the trial
point `x + s` if `η₁ ≤ ρ` and `x` otherwise, and the new radius `Δ'` satisfies the update rule
(2.3.7). -/
def TRAcceptance (P : TRParams) (ρ : ℝ) (x s x' : E) (Δ Δ' : ℝ) : Prop :=
  x' = (if P.η₁ ≤ ρ then x + s else x) ∧ TRUpdate P.η₁ P.η₂ P.γ₁ P.γ₂ P.γ₃ ρ Δ Δ'

variable {P : TRParams} {ρ : ℝ} {x s x' : E} {Δ Δ' : ℝ}

theorem trAcceptance_iff :
    TRAcceptance P ρ x s x' Δ Δ' ↔
      x' = (if P.η₁ ≤ ρ then x + s else x) ∧ TRUpdate P.η₁ P.η₂ P.γ₁ P.γ₂ P.γ₃ ρ Δ Δ' :=
  Iff.rfl

namespace TRAcceptance

variable (h : TRAcceptance P ρ x s x' Δ Δ')
include h

/-- The radius update of an accepted iteration. -/
theorem update : TRUpdate P.η₁ P.η₂ P.γ₁ P.γ₂ P.γ₃ ρ Δ Δ' := h.2

/-- A successful iteration moves to the trial point. -/
theorem eq_add (hρ : P.η₁ ≤ ρ) : x' = x + s := by
  rw [h.1, ite_eq_left hρ]

/-- An unsuccessful iteration keeps the iterate. -/
theorem eq_self (hρ : ρ < P.η₁) : x' = x := by
  rw [h.1, ite_eq_right (not_le.2 hρ)]

/-- The update preserves positivity of the radius. -/
theorem pos (hΔ : 0 < Δ) : 0 < Δ' :=
  h.2.pos P.γ₁_pos P.γ₁_le_γ₂ P.γ₁_le_one hΔ

/-- **Decrease on a successful iteration**: if `ρ = (f x - f (x + s)) / pred` with `pred > 0` and
`η₁ ≤ ρ`, then `f x - f x' ≥ η₁ pred`. -/
theorem sub_ge {f : E → ℝ} {pred : ℝ} (hρ : ρ = reductionRatio f x s pred) (hpred : 0 < pred)
    (hs : P.η₁ ≤ ρ) : P.η₁ * pred ≤ f x - f x' := by
  rw [h.eq_add hs]
  exact sub_le_of_le_reductionRatio hpred (hρ ▸ hs)

/-- The objective does not increase along an iteration whose ratio is a reduction ratio with
positive predicted decrease. -/
theorem le {f : E → ℝ} {pred : ℝ} (hρ : ρ = reductionRatio f x s pred) (hpred : 0 < pred) :
    f x' ≤ f x := by
  by_cases hs : P.η₁ ≤ ρ
  · have := h.sub_ge hρ hpred hs
    nlinarith [P.η₁_pos]
  · rw [h.eq_self (not_le.1 hs)]

end TRAcceptance

/-- **Existence of the next radius**: for `Δ ≥ 0` the radius `Δ' = γ₂ Δ` after an unsuccessful
iteration and `Δ' = Δ` otherwise is admissible. In particular `Δ' ≤ Δ`, so any cap
`Δ ≤ Δ_max` is preserved, and `Δ' > 0` if `Δ > 0`. -/
theorem exists_trAcceptance (P : TRParams) (ρ : ℝ) (x s : E) {Δ : ℝ} (hΔ : 0 ≤ Δ) :
    ∃ Δ', TRAcceptance P ρ x s (if P.η₁ ≤ ρ then x + s else x) Δ Δ' ∧ Δ' ≤ Δ ∧
      (0 < Δ → 0 < Δ') := by
  refine ⟨if ρ < P.η₁ then P.γ₂ * Δ else Δ, ⟨rfl, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro h2
    rw [ite_eq_right (not_lt.2 (P.η₁_le_η₂.trans h2))]
    exact ⟨le_rfl, le_mul_of_one_le_left hΔ P.one_le_γ₃⟩
  · intro h1 _
    rw [ite_eq_right (not_lt.2 h1)]
    exact ⟨mul_le_of_le_one_left hΔ P.γ₂_lt_one.le, le_rfl⟩
  · intro h1
    rw [ite_eq_left h1]
    exact ⟨mul_le_mul_of_nonneg_right P.γ₁_le_γ₂ hΔ, le_rfl⟩
  · split_ifs
    · exact mul_le_of_le_one_left hΔ P.γ₂_lt_one.le
    · exact le_rfl
  · intro hΔ'
    split_ifs
    · exact mul_pos P.γ₂_pos hΔ'
    · exact hΔ'

end Acceptance

/-- A run of a trust-region method ([cartis2022evaluation], Algorithms 2.3.1, 3.2.1, 3.4.1,
12.2.1, Steps 2–4): `stop k` is the Step-1 termination test at iteration `k`, `step k` the
Step-2 conditions on the trial step `s k` (including the trust-region constraint), and `ρ k` the
ratio of achieved to predicted decrease. Until termination, Step 2 holds and Steps 3–4 are
`Optimization.TRAcceptance`. Iteration `k` is successful iff `P.η₁ ≤ ρ k`. -/
structure IsTRRun {E : Type*} [Add E] (P : TRParams) (stop step : ℕ → Prop) (ρ : ℕ → ℝ)
    (x s : ℕ → E) (Δ : ℕ → ℝ) : Prop where
  /-- The initial radius. -/
  delta_zero : Δ 0 = P.Δ₀
  /-- Step 2 is executed at every iteration before termination. -/
  step : UntilHit stop step
  /-- Steps 3–4 are executed at every iteration before termination. -/
  accept : UntilHit stop fun k => TRAcceptance P (ρ k) (x k) (s k) (x (k + 1)) (Δ k) (Δ (k + 1))

namespace IsTRRun

variable {E : Type*} [Add E] {P : TRParams} {stop step : ℕ → Prop} {ρ : ℕ → ℝ} {x s : ℕ → E}
  {Δ : ℕ → ℝ} (h : IsTRRun P stop step ρ x s Δ)
include h

/-- A run with a stronger step condition is a run with a weaker one. -/
theorem mono {step' : ℕ → Prop} (hst : ∀ k, step k → step' k) :
    IsTRRun P stop step' ρ x s Δ :=
  ⟨h.delta_zero, h.step.mono hst, h.accept⟩

/-- The radius update before termination. -/
theorem update {k : ℕ} (hk : ∀ j ≤ k, ¬ stop j) :
    TRUpdate P.η₁ P.η₂ P.γ₁ P.γ₂ P.γ₃ (ρ k) (Δ k) (Δ (k + 1)) :=
  (h.accept k hk).update

/-- A successful iteration before termination moves to the trial point. -/
theorem eq_add_of_succ {k : ℕ} (hk : ∀ j ≤ k, ¬ stop j) (hs : P.η₁ ≤ ρ k) :
    x (k + 1) = x k + s k :=
  (h.accept k hk).eq_add hs

/-- An unsuccessful iteration before termination keeps the iterate. -/
theorem eq_of_not_succ {k : ℕ} (hk : ∀ j ≤ k, ¬ stop j) (hs : ρ k < P.η₁) :
    x (k + 1) = x k :=
  (h.accept k hk).eq_self hs

private theorem updates {K : ℕ} (hK : ∀ j < K, ¬ stop j) :
    ∀ k < K, TRUpdate P.η₁ P.η₂ P.γ₁ P.γ₂ P.γ₃ (ρ k) (Δ k) (Δ (k + 1)) :=
  fun _ hk => h.update fun j hj => hK j (hj.trans_lt hk)

/-- The radii are positive up to (and including) the first termination index: if the test
failed at every `j < K`, then `Δ k > 0` for all `k ≤ K`. -/
theorem delta_pos {K : ℕ} (hK : ∀ j < K, ¬ stop j) : ∀ k ≤ K, 0 < Δ k :=
  pos_of_trUpdate P.γ₁_pos P.γ₁_le_γ₂ P.γ₁_le_one (h.delta_zero ▸ P.Δ₀_pos) (h.updates hK)

/-- **Lower bound on the radius** for any TR run (the mechanism of [cartis2022evaluation],
Lemmas 2.3.4, 3.2.5, 12.2.3). Suppose the test failed at every `j < K`, the threshold `θ` is
nonincreasing on `[0, K]`, and every iteration `k < K` with `Δ_k < θ_k` is very successful. Then
`Δ_k ≥ min(Δ₀, γ₁ θ_k)` for all `k ≤ K`. -/
theorem delta_ge {θ : ℕ → ℝ} {K : ℕ} (hK : ∀ j < K, ¬ stop j)
    (hθ : ∀ k < K, θ (k + 1) ≤ θ k) (hforce : ∀ k < K, Δ k < θ k → P.η₂ ≤ ρ k) :
    ∀ k ≤ K, min P.Δ₀ (P.γ₁ * θ k) ≤ Δ k := by
  have := le_delta_of_trUpdate P.γ₁_pos P.γ₁_le_γ₂ P.γ₁_le_one (h.delta_zero ▸ P.Δ₀_pos)
    (h.updates hK) hθ hforce
  rwa [h.delta_zero] at this

/-- **Lower bound on the next radius**: under the hypotheses of `IsTRRun.delta_ge`,
`Δ_{k+1} ≥ min(Δ₀, γ₁ θ_k)` for all `k < K`. -/
theorem delta_succ_ge {θ : ℕ → ℝ} {K : ℕ} (hK : ∀ j < K, ¬ stop j)
    (hθ : ∀ k < K, θ (k + 1) ≤ θ k) (hforce : ∀ k < K, Δ k < θ k → P.η₂ ≤ ρ k) :
    ∀ k < K, min P.Δ₀ (P.γ₁ * θ k) ≤ Δ (k + 1) := by
  have := le_delta_succ_of_trUpdate P.γ₁_pos P.γ₁_le_γ₂ P.γ₁_le_one (h.delta_zero ▸ P.Δ₀_pos)
    (h.updates hK) hθ hforce
  rwa [h.delta_zero] at this

/-- **Lemma 2.3.1** ([cartis2022evaluation]) for any TR run: if the test failed at every `j ≤ k`
and `0 < Δmin ≤ Δ_{k+1}`, then
`k + 1 ≤ |𝒮_k| (1 + log γ₃ / |log γ₂|) + |log (Δmin / Δ₀)| / |log γ₂|`,
with `𝒮_k = {j ≤ k | η₁ ≤ ρ_j}`. -/
theorem succ_count {Δmin : ℝ} {k : ℕ} (hk : ∀ j ≤ k, ¬ stop j) (hmin : 0 < Δmin)
    (hΔmin : Δmin ≤ Δ (k + 1)) :
    (k + 1 : ℝ) ≤
      (successSet (fun j => P.η₁ ≤ ρ j) k).card * (1 + Real.log P.γ₃ / |Real.log P.γ₂|) +
        |Real.log (Δmin / P.Δ₀)| / |Real.log P.γ₂| := by
  rw [← h.delta_zero]
  exact succ_le_of_trUpdate P.γ₂_pos P.γ₂_lt_one P.one_le_γ₃
    (fun j hj => h.update fun i hi => hk i (hi.trans hj)) hmin hΔmin

/-- **Lemma 2.3.1** ([cartis2022evaluation], (2.3.11)) with the book's indexing: if the test
failed at every `j < k` and `0 < Δmin ≤ Δ_k`, then
`k ≤ |𝒮_k| (1 + log γ₃ / |log γ₂|) + |log (Δmin / Δ₀)| / |log γ₂|`. -/
theorem le_succ_count {Δmin : ℝ} {k : ℕ} (hk : ∀ j < k, ¬ stop j) (hmin : 0 < Δmin)
    (hΔmin : Δmin ≤ Δ k) :
    (k : ℝ) ≤
      (successSet (fun j => P.η₁ ≤ ρ j) k).card * (1 + Real.log P.γ₃ / |Real.log P.γ₂|) +
        |Real.log (Δmin / P.Δ₀)| / |Real.log P.γ₂| := by
  rw [← h.delta_zero]
  exact le_of_trUpdate P.γ₂_pos P.γ₂_lt_one P.one_le_γ₃ (h.updates hk) hmin hΔmin

/-- **Decrease on successful iterations**: if, before termination, `ρ_k` is the reduction ratio
of a positive predicted decrease `pred_k` and the iteration is successful, then
`x_{k+1} = x_k + s_k` and `f(x_k) - f(x_{k+1}) ≥ η₁ pred_k`. -/
theorem sub_ge_of_succ {f : E → ℝ} {pred : ℕ → ℝ} {k : ℕ} (hk : ∀ j ≤ k, ¬ stop j)
    (hρ : ρ k = reductionRatio f (x k) (s k) (pred k)) (hpred : 0 < pred k)
    (hs : P.η₁ ≤ ρ k) :
    x (k + 1) = x k + s k ∧ P.η₁ * pred k ≤ f (x k) - f (x (k + 1)) :=
  ⟨h.eq_add_of_succ hk hs, (h.accept k hk).sub_ge hρ hpred hs⟩

/-- **Monotonicity**: if the ratios are reduction ratios of positive predicted decreases at every
iteration before termination, then `f ∘ x` is nonincreasing up to (and including) the first
termination index: if the test failed at every `j < K`, then `f (x j) ≤ f (x i)` for
`i ≤ j ≤ K`. -/
theorem objective_antitone {f : E → ℝ} {pred : ℕ → ℝ} {K : ℕ} (hK : ∀ j < K, ¬ stop j)
    (hρ : ∀ k < K, ρ k = reductionRatio f (x k) (s k) (pred k)) (hpred : ∀ k < K, 0 < pred k) :
    ∀ i j, i ≤ j → j ≤ K → f (x j) ≤ f (x i) := by
  intro i j hij hjK
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j _ ih =>
    have hjK' : j < K := hjK
    exact ((h.accept j fun i hi => hK i (hi.trans_lt hjK')).le (hρ j hjK') (hpred j hjK')).trans
      (ih hjK'.le)

end IsTRRun

end Optimization
