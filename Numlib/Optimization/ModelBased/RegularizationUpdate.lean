import Numlib.Optimization.Complexity.ParameterCount

/-!
# The adaptive-regularization parameter update

The update of the regularization parameter of adaptive-regularization methods
([cartis2022evaluation], (2.4.4), stated identically for AR1, AR2 (3.3.8) and ARp (4.1.16); some
later variants, e.g. those of Section 5.5, use different rules and are not covered here):
with `0 < η₁ ≤ η₂ < 1`, `0 < γ₁ < 1 < γ₂ < γ₃` and `σ_min > 0`,
* `σ⁺ ∈ [max(σ_min, γ₁ σ), σ]` if `ρ ≥ η₂` (very successful iteration),
* `σ⁺ ∈ [σ, γ₂ σ]` if `ρ ∈ [η₁, η₂)` (successful iteration),
* `σ⁺ ∈ [γ₂ σ, γ₃ σ]` if `ρ < η₁` (unsuccessful iteration).

The rule is nondeterministic and is stated as the predicate `Optimization.ARUpdate`. Its
consequences shared by all chapters:
* `Optimization.pos_of_arUpdate`, `Optimization.le_sigma_of_arUpdate`: `σ_k > 0`, `σ_k ≥ σ_min`;
* `Optimization.sigma_le_max_of_arUpdate`: if `σ_k ≥ σ̄` forces a very successful iteration, then
  `σ_k ≤ max(σ_0, γ₃ σ̄)` (the mechanism of Lemmas 2.4.2, 3.3.2, 4.1.2);
* `Optimization.succ_le_of_arUpdate`, `Optimization.le_of_arUpdate`: the number of iterations is
  bounded in terms of the number of successful ones (Lemma 2.4.1).

Each hypothesis on the constants is stated only where it is used.
-/

namespace Optimization

/-- The adaptive-regularization update (2.4.4): `σ'` is an admissible successor of the
regularization parameter `σ` after an iteration with ratio `ρ`. -/
structure ARUpdate (η₁ η₂ γ₁ γ₂ γ₃ σmin ρ σ σ' : ℝ) : Prop where
  /-- Very successful iteration: `σ' ∈ [max(σmin, γ₁ σ), σ]`. -/
  very_successful : η₂ ≤ ρ → max σmin (γ₁ * σ) ≤ σ' ∧ σ' ≤ σ
  /-- Successful iteration: `σ' ∈ [σ, γ₂ σ]`. -/
  successful : η₁ ≤ ρ → ρ < η₂ → σ ≤ σ' ∧ σ' ≤ γ₂ * σ
  /-- Unsuccessful iteration: `σ' ∈ [γ₂ σ, γ₃ σ]`. -/
  unsuccessful : ρ < η₁ → γ₂ * σ ≤ σ' ∧ σ' ≤ γ₃ * σ

namespace ARUpdate

variable {η₁ η₂ γ₁ γ₂ γ₃ σmin ρ σ σ' : ℝ} (h : ARUpdate η₁ η₂ γ₁ γ₂ γ₃ σmin ρ σ σ')
include h

/-- At a very successful iteration the parameter does not increase. -/
theorem le_of_very_successful (hρ : η₂ ≤ ρ) : σ' ≤ σ := (h.very_successful hρ).2

/-- At a very successful iteration the new parameter is at least `σmin`. -/
theorem sigmaMin_le_of_very_successful (hρ : η₂ ≤ ρ) : σmin ≤ σ' :=
  (le_max_left _ _).trans (h.very_successful hρ).1

/-- At a successful iteration the parameter decreases by a factor at most `γ₁`. -/
theorem mul_le_of_le (hρ : η₁ ≤ ρ) (hγ₁ : γ₁ ≤ 1) (hσ : 0 ≤ σ) : γ₁ * σ ≤ σ' := by
  by_cases h2 : η₂ ≤ ρ
  · exact (le_max_right _ _).trans (h.very_successful h2).1
  · exact (mul_le_of_le_one_left hσ hγ₁).trans (h.successful hρ (not_le.1 h2)).1

/-- At an unsuccessful iteration the parameter increases by a factor at least `γ₂`. -/
theorem mul_le_of_lt (hρ : ρ < η₁) : γ₂ * σ ≤ σ' := (h.unsuccessful hρ).1

/-- At an iteration that is not very successful the parameter does not decrease. -/
theorem le_of_lt (hρ : ρ < η₂) (hγ₂ : 1 ≤ γ₂) (hσ : 0 ≤ σ) : σ ≤ σ' := by
  by_cases h1 : η₁ ≤ ρ
  · exact (h.successful h1 hρ).1
  · exact (le_mul_of_one_le_left hσ hγ₂).trans (h.mul_le_of_lt (not_le.1 h1))

/-- The parameter increases by a factor at most `γ₃`. -/
theorem le_mul (hγ₂₃ : γ₂ ≤ γ₃) (hγ₃ : 1 ≤ γ₃) (hσ : 0 ≤ σ) : σ' ≤ γ₃ * σ := by
  by_cases h1 : η₁ ≤ ρ
  · by_cases h2 : η₂ ≤ ρ
    · exact (h.le_of_very_successful h2).trans (le_mul_of_one_le_left hσ hγ₃)
    · exact (h.successful h1 (not_le.1 h2)).2.trans (mul_le_mul_of_nonneg_right hγ₂₃ hσ)
  · exact (h.unsuccessful (not_le.1 h1)).2

/-- The update preserves positivity. -/
theorem pos (hγ₁ : 0 < γ₁) (hγ₂ : 0 < γ₂) (hσ : 0 < σ) : 0 < σ' := by
  by_cases h1 : η₁ ≤ ρ
  · by_cases h2 : η₂ ≤ ρ
    · exact (mul_pos hγ₁ hσ).trans_le ((le_max_right _ _).trans (h.very_successful h2).1)
    · exact hσ.trans_le (h.successful h1 (not_le.1 h2)).1
  · exact (mul_pos hγ₂ hσ).trans_le (h.mul_le_of_lt (not_le.1 h1))

/-- The update preserves the lower bound `σmin`. -/
theorem sigmaMin_le (hmin : 0 ≤ σmin) (hγ₂ : 1 ≤ γ₂) (hσ : σmin ≤ σ) : σmin ≤ σ' := by
  by_cases h2 : η₂ ≤ ρ
  · exact h.sigmaMin_le_of_very_successful h2
  · exact hσ.trans (h.le_of_lt (not_le.1 h2) hγ₂ (hmin.trans hσ))

end ARUpdate

section sequence

variable {η₁ η₂ γ₁ γ₂ γ₃ σmin σbar σmax : ℝ} {ρ σ : ℕ → ℝ} {k K : ℕ}

/-- The regularization parameters stay positive. -/
theorem pos_of_arUpdate (hγ₁ : 0 < γ₁) (hγ₂ : 0 < γ₂) (hσ0 : 0 < σ 0)
    (h : ∀ k < K, ARUpdate η₁ η₂ γ₁ γ₂ γ₃ σmin (ρ k) (σ k) (σ (k + 1))) :
    ∀ k ≤ K, 0 < σ k := by
  intro k
  induction k with
  | zero => exact fun _ => hσ0
  | succ k ih => exact fun hk => (h k hk).pos hγ₁ hγ₂ (ih (Nat.le_of_succ_le hk))

/-- The regularization parameters stay above `σmin` ([cartis2022evaluation], proof of
Lemma 3.3.4). -/
theorem le_sigma_of_arUpdate (hmin : 0 ≤ σmin) (hγ₂ : 1 ≤ γ₂) (h0 : σmin ≤ σ 0)
    (h : ∀ k < K, ARUpdate η₁ η₂ γ₁ γ₂ γ₃ σmin (ρ k) (σ k) (σ (k + 1))) :
    ∀ k ≤ K, σmin ≤ σ k := by
  intro k
  induction k with
  | zero => exact fun _ => h0
  | succ k ih => exact fun hk => (h k hk).sigmaMin_le hmin hγ₂ (ih (Nat.le_of_succ_le hk))

/-- **Upper bound on the regularization parameter** (the mechanism of [cartis2022evaluation],
Lemmas 2.4.2, 3.3.2, 4.1.2). If every iteration `k < K` with `σ_k ≥ σbar` is very successful,
then `σ_k ≤ max(σ_0, γ₃ σbar)` for all `k ≤ K`. -/
theorem sigma_le_max_of_arUpdate (hγ₁ : 0 < γ₁) (hγ₂ : 0 < γ₂) (hγ₂₃ : γ₂ ≤ γ₃)
    (hγ₃ : 1 ≤ γ₃) (hσ0 : 0 < σ 0)
    (h : ∀ k < K, ARUpdate η₁ η₂ γ₁ γ₂ γ₃ σmin (ρ k) (σ k) (σ (k + 1)))
    (hforce : ∀ k < K, σbar ≤ σ k → η₂ ≤ ρ k) :
    ∀ k ≤ K, σ k ≤ max (σ 0) (γ₃ * σbar) := by
  have hpos := pos_of_arUpdate hγ₁ hγ₂ hσ0 h
  intro k
  induction k with
  | zero => exact fun _ => le_max_left _ _
  | succ k ih =>
    intro hk
    have hkK : k < K := hk
    by_cases hbar : σbar ≤ σ k
    · exact ((h k hkK).le_of_very_successful (hforce k hkK hbar)).trans (ih hkK.le)
    · calc σ (k + 1) ≤ γ₃ * σ k := (h k hkK).le_mul hγ₂₃ hγ₃ (hpos k hkK.le).le
        _ ≤ γ₃ * σbar := mul_le_mul_of_nonneg_left (not_le.1 hbar).le (zero_le_one.trans hγ₃)
        _ ≤ max (σ 0) (γ₃ * σbar) := le_max_right _ _

/-- **Lemma 2.4.1** ([cartis2022evaluation]) for the update (2.4.4), with successful iterations
`𝒮_k = {j ≤ k | η₁ ≤ ρ_j}`. If `σ_0 > 0`, `0 < γ₁ ≤ 1 < γ₂`, the update holds at every `j ≤ k`
and `σ_{k+1} ≤ σmax`, then
`k + 1 ≤ |𝒮_k| (1 + |log γ₁| / log γ₂) + log (σmax / σ_0) / log γ₂`. -/
theorem succ_le_of_arUpdate (hγ₁ : 0 < γ₁) (hγ₁1 : γ₁ ≤ 1) (hγ₂ : 1 < γ₂) (hσ0 : 0 < σ 0)
    (h : ∀ j ≤ k, ARUpdate η₁ η₂ γ₁ γ₂ γ₃ σmin (ρ j) (σ j) (σ (j + 1)))
    (hmax : σ (k + 1) ≤ σmax) :
    (k + 1 : ℝ) ≤
      (successSet (fun j => η₁ ≤ ρ j) k).card * (1 + |Real.log γ₁| / Real.log γ₂) +
        Real.log (σmax / σ 0) / Real.log γ₂ := by
  have hpos := pos_of_arUpdate (K := k + 1) hγ₁ (zero_lt_one.trans hγ₂) hσ0
    fun j hj => h j (Nat.lt_succ_iff.1 hj)
  exact succ_le_card_successSet_of_lower_ratio hσ0 hγ₁ hγ₁1 hγ₂
    (fun j hj hs => (h j hj).mul_le_of_le hs hγ₁1 (hpos j (hj.trans k.le_succ)).le)
    (fun j hj hs => (h j hj).mul_le_of_lt (not_le.1 hs)) hmax

/-- **Lemma 2.4.1** ([cartis2022evaluation], (2.4.8)) with the book's indexing: if `σ_0 > 0`,
`0 < γ₁ ≤ 1 < γ₂`, the update holds at every `j < k` and `σ_k ≤ σmax`, then
`k ≤ |𝒮_k| (1 + |log γ₁| / log γ₂) + log (σmax / σ_0) / log γ₂`. -/
theorem le_of_arUpdate (hγ₁ : 0 < γ₁) (hγ₁1 : γ₁ ≤ 1) (hγ₂ : 1 < γ₂) (hσ0 : 0 < σ 0)
    (h : ∀ j < k, ARUpdate η₁ η₂ γ₁ γ₂ γ₃ σmin (ρ j) (σ j) (σ (j + 1)))
    (hmax : σ k ≤ σmax) :
    (k : ℝ) ≤
      (successSet (fun j => η₁ ≤ ρ j) k).card * (1 + |Real.log γ₁| / Real.log γ₂) +
        Real.log (σmax / σ 0) / Real.log γ₂ := by
  have hpos := pos_of_arUpdate hγ₁ (zero_lt_one.trans hγ₂) hσ0 h
  exact le_card_successSet_of_lower_ratio hσ0 hγ₁ hγ₁1 hγ₂
    (fun j hj hs => (h j hj).mul_le_of_le hs hγ₁1 (hpos j hj.le).le)
    (fun j hj hs => (h j hj).mul_le_of_lt (not_le.1 hs)) hmax

end sequence

end Optimization
