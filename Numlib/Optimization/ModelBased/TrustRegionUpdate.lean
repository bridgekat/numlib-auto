import Numlib.Optimization.Complexity.ParameterCount

/-!
# The trust-region radius update

The update of the trust-region radius ([cartis2022evaluation], (2.3.7), identical in TR1, TR2
(3.2.12), TRε, TRq (12.2.5) and TRqIDA (13.1.17)): with `0 < η₁ ≤ η₂ < 1` and
`0 < γ₁ ≤ γ₂ < 1 < γ₃`,
* `Δ⁺ ∈ [Δ, γ₃ Δ]` if `ρ ≥ η₂` (very successful iteration),
* `Δ⁺ ∈ [γ₂ Δ, Δ]` if `ρ ∈ [η₁, η₂)` (successful iteration),
* `Δ⁺ ∈ [γ₁ Δ, γ₂ Δ]` if `ρ < η₁` (unsuccessful iteration).

The rule is nondeterministic and is stated as the predicate `Optimization.TRUpdate`; a cap
`Δ⁺ ≤ Δ_max` (TRq, TRqIDA) is an additional conjunct in the algorithms that use it. Consequences
shared by all chapters:
* `Optimization.pos_of_trUpdate`: `Δ_k > 0`;
* `Optimization.le_delta_of_trUpdate`: if `Δ_k < θ_k` forces a very successful iteration for a
  nonincreasing threshold `θ`, then `Δ_k ≥ min(Δ_0, γ₁ θ_k)` (the mechanism of Lemmas 2.3.4,
  3.2.5, 3.4.2), and `Optimization.le_delta_succ_of_trUpdate`: `Δ_{k+1} ≥ min(Δ_0, γ₁ θ_k)`
  (used for the exact constants of Theorem 2.3.7);
* `Optimization.succ_le_of_trUpdate`, `Optimization.le_of_trUpdate`: the number of iterations is
  bounded in terms of the number of successful ones while `Δ_k ≥ Δ_min > 0` (Lemma 2.3.1).

Each hypothesis on the constants is stated only where it is used.
-/

namespace Optimization

/-- The trust-region radius update (2.3.7): `Δ'` is an admissible successor of the radius `Δ`
after an iteration with ratio `ρ`. -/
structure TRUpdate (η₁ η₂ γ₁ γ₂ γ₃ ρ Δ Δ' : ℝ) : Prop where
  /-- Very successful iteration: `Δ' ∈ [Δ, γ₃ Δ]`. -/
  very_successful : η₂ ≤ ρ → Δ ≤ Δ' ∧ Δ' ≤ γ₃ * Δ
  /-- Successful iteration: `Δ' ∈ [γ₂ Δ, Δ]`. -/
  successful : η₁ ≤ ρ → ρ < η₂ → γ₂ * Δ ≤ Δ' ∧ Δ' ≤ Δ
  /-- Unsuccessful iteration: `Δ' ∈ [γ₁ Δ, γ₂ Δ]`. -/
  unsuccessful : ρ < η₁ → γ₁ * Δ ≤ Δ' ∧ Δ' ≤ γ₂ * Δ

namespace TRUpdate

variable {η₁ η₂ γ₁ γ₂ γ₃ ρ Δ Δ' : ℝ} (h : TRUpdate η₁ η₂ γ₁ γ₂ γ₃ ρ Δ Δ')
include h

/-- At a very successful iteration the radius does not decrease. -/
theorem le_of_very_successful (hρ : η₂ ≤ ρ) : Δ ≤ Δ' := (h.very_successful hρ).1

/-- At an iteration that is not very successful the radius does not increase. -/
theorem le_of_lt (hρ : ρ < η₂) (hγ₂ : γ₂ ≤ 1) (hΔ : 0 ≤ Δ) : Δ' ≤ Δ := by
  by_cases h1 : η₁ ≤ ρ
  · exact (h.successful h1 hρ).2
  · exact (h.unsuccessful (not_le.1 h1)).2.trans (mul_le_of_le_one_left hΔ hγ₂)

/-- The radius decreases by a factor at most `γ₁`. -/
theorem mul_le (hγ₁₂ : γ₁ ≤ γ₂) (hγ₁ : γ₁ ≤ 1) (hΔ : 0 ≤ Δ) : γ₁ * Δ ≤ Δ' := by
  by_cases h1 : η₁ ≤ ρ
  · by_cases h2 : η₂ ≤ ρ
    · exact (mul_le_of_le_one_left hΔ hγ₁).trans (h.le_of_very_successful h2)
    · exact (mul_le_mul_of_nonneg_right hγ₁₂ hΔ).trans (h.successful h1 (not_le.1 h2)).1
  · exact (h.unsuccessful (not_le.1 h1)).1

/-- At a successful iteration the radius increases by a factor at most `γ₃`. (No sign condition
on `Δ` is needed: at a successful but not very successful iteration `γ₂ Δ ≤ Δ` with `γ₂ < 1`
forces `Δ ≥ 0`.) -/
theorem le_mul_of_le (hρ : η₁ ≤ ρ) (hγ₂ : γ₂ < 1) (hγ₃ : 1 ≤ γ₃) : Δ' ≤ γ₃ * Δ := by
  by_cases h2 : η₂ ≤ ρ
  · exact (h.very_successful h2).2
  · obtain ⟨h₁, h₂⟩ := h.successful hρ (not_le.1 h2)
    have hΔ : 0 ≤ Δ := by nlinarith
    exact h₂.trans (le_mul_of_one_le_left hΔ hγ₃)

/-- At an unsuccessful iteration the radius decreases by a factor at least `γ₂`. -/
theorem le_mul_of_lt (hρ : ρ < η₁) : Δ' ≤ γ₂ * Δ := (h.unsuccessful hρ).2

/-- The update preserves positivity. -/
theorem pos (hγ₁ : 0 < γ₁) (hγ₁₂ : γ₁ ≤ γ₂) (hγ₁1 : γ₁ ≤ 1) (hΔ : 0 < Δ) : 0 < Δ' :=
  (mul_pos hγ₁ hΔ).trans_le (h.mul_le hγ₁₂ hγ₁1 hΔ.le)

end TRUpdate

section sequence

variable {η₁ η₂ γ₁ γ₂ γ₃ Δmin : ℝ} {ρ Δ θ : ℕ → ℝ} {k K : ℕ}

/-- The trust-region radii stay positive. -/
theorem pos_of_trUpdate (hγ₁ : 0 < γ₁) (hγ₁₂ : γ₁ ≤ γ₂) (hγ₁1 : γ₁ ≤ 1) (hΔ0 : 0 < Δ 0)
    (h : ∀ k < K, TRUpdate η₁ η₂ γ₁ γ₂ γ₃ (ρ k) (Δ k) (Δ (k + 1))) :
    ∀ k ≤ K, 0 < Δ k := by
  intro k
  induction k with
  | zero => exact fun _ => hΔ0
  | succ k ih => exact fun hk => (h k hk).pos hγ₁ hγ₁₂ hγ₁1 (ih (Nat.le_of_succ_le hk))

/-- **Lower bound on the trust-region radius** (the mechanism of [cartis2022evaluation],
Lemmas 2.3.4, 3.2.5, 3.4.2). Let `θ` be nonincreasing on `[0, K]`. If every iteration `k < K`
with `Δ_k < θ_k` is very successful, then `Δ_k ≥ min(Δ_0, γ₁ θ_k)` for all `k ≤ K`. -/
theorem le_delta_of_trUpdate (hγ₁ : 0 < γ₁) (hγ₁₂ : γ₁ ≤ γ₂) (hγ₁1 : γ₁ ≤ 1) (hΔ0 : 0 < Δ 0)
    (h : ∀ k < K, TRUpdate η₁ η₂ γ₁ γ₂ γ₃ (ρ k) (Δ k) (Δ (k + 1)))
    (hθ : ∀ k < K, θ (k + 1) ≤ θ k) (hforce : ∀ k < K, Δ k < θ k → η₂ ≤ ρ k) :
    ∀ k ≤ K, min (Δ 0) (γ₁ * θ k) ≤ Δ k := by
  have hpos := pos_of_trUpdate hγ₁ hγ₁₂ hγ₁1 hΔ0 h
  intro k
  induction k with
  | zero => exact fun _ => min_le_left _ _
  | succ k ih =>
    intro hk
    have hkK : k < K := hk
    have hγθ : γ₁ * θ (k + 1) ≤ γ₁ * θ k := mul_le_mul_of_nonneg_left (hθ k hkK) hγ₁.le
    by_cases hsmall : Δ k < θ k
    · calc min (Δ 0) (γ₁ * θ (k + 1)) ≤ min (Δ 0) (γ₁ * θ k) := min_le_min le_rfl hγθ
        _ ≤ Δ k := ih hkK.le
        _ ≤ Δ (k + 1) := (h k hkK).le_of_very_successful (hforce k hkK hsmall)
    · calc min (Δ 0) (γ₁ * θ (k + 1)) ≤ γ₁ * θ k := (min_le_right _ _).trans hγθ
        _ ≤ γ₁ * Δ k := mul_le_mul_of_nonneg_left (not_lt.1 hsmall) hγ₁.le
        _ ≤ Δ (k + 1) := (h k hkK).mul_le hγ₁₂ hγ₁1 (hpos k hkK.le).le

/-- **Lower bound on the next radius.** Under the hypotheses of
`Optimization.le_delta_of_trUpdate`, `Δ_{k+1} ≥ min(Δ_0, γ₁ θ_k)` for all `k < K` (with the
threshold at `k`, not `k + 1`). This sharper form gives the exact constants of
[cartis2022evaluation], Theorem 2.3.7. -/
theorem le_delta_succ_of_trUpdate (hγ₁ : 0 < γ₁) (hγ₁₂ : γ₁ ≤ γ₂) (hγ₁1 : γ₁ ≤ 1)
    (hΔ0 : 0 < Δ 0) (h : ∀ k < K, TRUpdate η₁ η₂ γ₁ γ₂ γ₃ (ρ k) (Δ k) (Δ (k + 1)))
    (hθ : ∀ k < K, θ (k + 1) ≤ θ k) (hforce : ∀ k < K, Δ k < θ k → η₂ ≤ ρ k) :
    ∀ k < K, min (Δ 0) (γ₁ * θ k) ≤ Δ (k + 1) := by
  intro k hk
  have hpos := pos_of_trUpdate hγ₁ hγ₁₂ hγ₁1 hΔ0 h
  by_cases hsmall : Δ k < θ k
  · exact (le_delta_of_trUpdate hγ₁ hγ₁₂ hγ₁1 hΔ0 h hθ hforce k hk.le).trans
      ((h k hk).le_of_very_successful (hforce k hk hsmall))
  · calc min (Δ 0) (γ₁ * θ k) ≤ γ₁ * θ k := min_le_right _ _
      _ ≤ γ₁ * Δ k := mul_le_mul_of_nonneg_left (not_lt.1 hsmall) hγ₁.le
      _ ≤ Δ (k + 1) := (h k hk).mul_le hγ₁₂ hγ₁1 (hpos k hk.le).le

/-- **Lemma 2.3.1** ([cartis2022evaluation]) for the update (2.3.7), with successful iterations
`𝒮_k = {j ≤ k | η₁ ≤ ρ_j}`. If `0 < γ₂ < 1 ≤ γ₃`, the update holds at every `j ≤ k` and
`0 < Δmin ≤ Δ_{k+1}`, then
`k + 1 ≤ |𝒮_k| (1 + log γ₃ / |log γ₂|) + |log (Δmin / Δ_0)| / |log γ₂|`. -/
theorem succ_le_of_trUpdate (hγ₂ : 0 < γ₂) (hγ₂1 : γ₂ < 1) (hγ₃ : 1 ≤ γ₃)
    (h : ∀ j ≤ k, TRUpdate η₁ η₂ γ₁ γ₂ γ₃ (ρ j) (Δ j) (Δ (j + 1)))
    (hmin : 0 < Δmin) (hΔmin : Δmin ≤ Δ (k + 1)) :
    (k + 1 : ℝ) ≤
      (successSet (fun j => η₁ ≤ ρ j) k).card * (1 + Real.log γ₃ / |Real.log γ₂|) +
        |Real.log (Δmin / Δ 0)| / |Real.log γ₂| :=
  succ_le_card_successSet_of_upper_ratio hγ₂ hγ₂1 hγ₃
    (fun j hj hs => (h j hj).le_mul_of_le hs hγ₂1 hγ₃)
    (fun j hj hs => (h j hj).le_mul_of_lt (not_le.1 hs)) hmin hΔmin

/-- **Lemma 2.3.1** ([cartis2022evaluation], (2.3.11)) with the book's indexing: if
`0 < γ₂ < 1 ≤ γ₃`, the update holds at every `j < k` and `0 < Δmin ≤ Δ_k`, then
`k ≤ |𝒮_k| (1 + log γ₃ / |log γ₂|) + |log (Δmin / Δ_0)| / |log γ₂|`. -/
theorem le_of_trUpdate (hγ₂ : 0 < γ₂) (hγ₂1 : γ₂ < 1) (hγ₃ : 1 ≤ γ₃)
    (h : ∀ j < k, TRUpdate η₁ η₂ γ₁ γ₂ γ₃ (ρ j) (Δ j) (Δ (j + 1)))
    (hmin : 0 < Δmin) (hΔmin : Δmin ≤ Δ k) :
    (k : ℝ) ≤
      (successSet (fun j => η₁ ≤ ρ j) k).card * (1 + Real.log γ₃ / |Real.log γ₂|) +
        |Real.log (Δmin / Δ 0)| / |Real.log γ₂| :=
  le_card_successSet_of_upper_ratio hγ₂ hγ₂1 hγ₃
    (fun j hj hs => (h j hj).le_mul_of_le hs hγ₂1 hγ₃)
    (fun j hj hs => (h j hj).le_mul_of_lt (not_le.1 hs)) hmin hΔmin

end sequence

end Optimization
