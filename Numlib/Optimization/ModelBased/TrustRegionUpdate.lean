/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Optimization.Complexity.ParameterCount

/-!
# The trust-region radius update

Trust-region methods update the radius $\Delta$ after each iteration according to the reduction
ratio $\rho$ of the iteration. This file formalizes the rule (2.3.7) of [cartis2022evaluation],
which is the same in TR1, TR2 (3.2.12), TRε, TRq (12.2.5) and TRqIDA (13.1.17). Let
$0 < \eta_1 \le \eta_2 < 1$ and $0 < \gamma_1 \le \gamma_2 < 1 < \gamma_3$. The new radius
$\Delta^+$ satisfies
$$\Delta^+ \in \begin{cases}
  [\Delta, \gamma_3 \Delta] & \text{if } \rho \ge \eta_2 \text{ (very successful iteration)}, \\
  [\gamma_2 \Delta, \Delta] & \text{if } \eta_1 \le \rho < \eta_2 \text{ (successful iteration)}, \\
  [\gamma_1 \Delta, \gamma_2 \Delta] & \text{if } \rho < \eta_1 \text{ (unsuccessful iteration)}.
  \end{cases}$$

The rule leaves a choice, so it is a predicate on $(\Delta, \Delta^+)$. Its consequences are shared
by all chapters: the radii stay positive; they stay at least $\min(\Delta_0, \gamma_1 \theta_k)$
when $\Delta_k < \theta_k$ forces a very successful iteration for a nonincreasing threshold
$\theta$; and the number of iterations is bounded in terms of the number of successful iterations
while $\Delta_k \ge \Delta_{\min} > 0$. The first two results also hold when some iterations leave
the radius unchanged, as the accuracy-improving iterations of Chapter 13 of [cartis2022evaluation]
do.

## Main definitions

* `Optimization.TRUpdate`: $\Delta'$ is an admissible successor of $\Delta$ under the rule (2.3.7)
  after an iteration with ratio $\rho$.

## Main results

* `Optimization.pos_of_trUpdate`: the radii $\Delta_k$ stay positive.
* `Optimization.le_delta_of_trUpdate`: if $\Delta_k < \theta_k$ forces a very successful iteration
  and $\theta$ is nonincreasing, then $\Delta_k \ge \min(\Delta_0, \gamma_1 \theta_k)$. This is the
  mechanism of Lemmas 2.3.4, 3.2.5 and 3.4.2 of [cartis2022evaluation].
* `Optimization.le_delta_succ_of_trUpdate`: under the same hypotheses, $\Delta_{k+1} \ge
  \min(\Delta_0, \gamma_1 \theta_k)$. This form gives the exact constants of Theorem 2.3.7 of
  [cartis2022evaluation].
* `Optimization.pos_of_trUpdate_of_neutral` and `Optimization.le_delta_of_trUpdate_of_neutral`: the
  same statements when some iterations leave the radius unchanged, as in Lemma 13.1.4 of
  [cartis2022evaluation]. The statements without unchanged iterations are special cases.
* `Optimization.succ_le_of_trUpdate` and `Optimization.le_of_trUpdate`: the number of iterations is
  bounded in terms of the number of successful iterations while $\Delta_k \ge \Delta_{\min} > 0$, as
  in Lemma 2.3.1 of [cartis2022evaluation].

## Implementation notes

* An upper bound $\Delta^+ \le \Delta_{\max}$, which TRq and TRqIDA impose, is not part of
  `Optimization.TRUpdate`. The algorithms that use it state it as an additional condition.
* Each hypothesis on the constants $\eta_i$ and $\gamma_i$ appears only in the results that use it.
-/

namespace Optimization

/-- The **trust-region radius update** (2.3.7) of [cartis2022evaluation]: $\Delta'$ is an admissible
successor of the radius $\Delta$ after an iteration with reduction ratio $\rho$. That is,
* if $\rho \ge \eta_2$, then $\Delta \le \Delta' \le \gamma_3 \Delta$;
* if $\eta_1 \le \rho < \eta_2$, then $\gamma_2 \Delta \le \Delta' \le \Delta$;
* if $\rho < \eta_1$, then $\gamma_1 \Delta \le \Delta' \le \gamma_2 \Delta$.

The structure puts no conditions on the constants. -/
structure TRUpdate (η₁ η₂ γ₁ γ₂ γ₃ ρ Δ Δ' : ℝ) : Prop where
  /-- At a very successful iteration ($\rho \ge \eta_2$), $\Delta \le \Delta' \le \gamma_3 \Delta$.
  -/
  very_successful : η₂ ≤ ρ → Δ ≤ Δ' ∧ Δ' ≤ γ₃ * Δ
  /-- At a successful iteration ($\eta_1 \le \rho < \eta_2$),
  $\gamma_2 \Delta \le \Delta' \le \Delta$. -/
  successful : η₁ ≤ ρ → ρ < η₂ → γ₂ * Δ ≤ Δ' ∧ Δ' ≤ Δ
  /-- At an unsuccessful iteration ($\rho < \eta_1$), $\gamma_1 \Delta \le \Delta' \le \gamma_2
  \Delta$. -/
  unsuccessful : ρ < η₁ → γ₁ * Δ ≤ Δ' ∧ Δ' ≤ γ₂ * Δ

namespace TRUpdate

variable {η₁ η₂ γ₁ γ₂ γ₃ ρ Δ Δ' : ℝ} (h : TRUpdate η₁ η₂ γ₁ γ₂ γ₃ ρ Δ Δ')
include h

/-- At a very successful iteration ($\rho \ge \eta_2$), the radius does not decrease:
$\Delta \le \Delta'$. -/
theorem le_of_very_successful (hρ : η₂ ≤ ρ) : Δ ≤ Δ' := (h.very_successful hρ).1

/-- At an iteration that is not very successful ($\rho < \eta_2$), the radius does not increase: if
$\gamma_2 \le 1$ and $\Delta \ge 0$, then $\Delta' \le \Delta$. -/
theorem le_of_lt (hρ : ρ < η₂) (hγ₂ : γ₂ ≤ 1) (hΔ : 0 ≤ Δ) : Δ' ≤ Δ := by
  by_cases h1 : η₁ ≤ ρ
  · exact (h.successful h1 hρ).2
  · exact (h.unsuccessful (not_le.1 h1)).2.trans (mul_le_of_le_one_left hΔ hγ₂)

/-- The radius decreases at most by the factor $\gamma_1$: if $\gamma_1 \le \gamma_2$,
$\gamma_1 \le 1$ and $\Delta \ge 0$, then $\gamma_1 \Delta \le \Delta'$. -/
theorem mul_le (hγ₁₂ : γ₁ ≤ γ₂) (hγ₁ : γ₁ ≤ 1) (hΔ : 0 ≤ Δ) : γ₁ * Δ ≤ Δ' := by
  by_cases h1 : η₁ ≤ ρ
  · by_cases h2 : η₂ ≤ ρ
    · exact (mul_le_of_le_one_left hΔ hγ₁).trans (h.le_of_very_successful h2)
    · exact (mul_le_mul_of_nonneg_right hγ₁₂ hΔ).trans (h.successful h1 (not_le.1 h2)).1
  · exact (h.unsuccessful (not_le.1 h1)).1

/-- At a successful iteration ($\rho \ge \eta_1$), the radius increases at most by the factor
$\gamma_3$: if $\gamma_2 < 1$ and $\gamma_3 \ge 1$, then $\Delta' \le \gamma_3 \Delta$.

No sign condition on $\Delta$ is needed. At a successful iteration that is not very successful,
$\gamma_2 \Delta \le \Delta$ with $\gamma_2 < 1$ forces $\Delta \ge 0$. -/
theorem le_mul_of_le (hρ : η₁ ≤ ρ) (hγ₂ : γ₂ < 1) (hγ₃ : 1 ≤ γ₃) : Δ' ≤ γ₃ * Δ := by
  by_cases h2 : η₂ ≤ ρ
  · exact (h.very_successful h2).2
  · obtain ⟨h₁, h₂⟩ := h.successful hρ (not_le.1 h2)
    have hΔ : 0 ≤ Δ := by nlinarith
    exact h₂.trans (le_mul_of_one_le_left hΔ hγ₃)

/-- At an unsuccessful iteration ($\rho < \eta_1$), the radius decreases at least by the factor
$\gamma_2$: $\Delta' \le \gamma_2 \Delta$. -/
theorem le_mul_of_lt (hρ : ρ < η₁) : Δ' ≤ γ₂ * Δ := (h.unsuccessful hρ).2

/-- The update preserves positivity: if $0 < \gamma_1 \le \gamma_2$, $\gamma_1 \le 1$ and
$\Delta > 0$, then $\Delta' > 0$. -/
theorem pos (hγ₁ : 0 < γ₁) (hγ₁₂ : γ₁ ≤ γ₂) (hγ₁1 : γ₁ ≤ 1) (hΔ : 0 < Δ) : 0 < Δ' :=
  (mul_pos hγ₁ hΔ).trans_le (h.mul_le hγ₁₂ hγ₁1 hΔ.le)

end TRUpdate

section sequence

variable {η₁ η₂ γ₁ γ₂ γ₃ Δmin : ℝ} {ρ Δ θ : ℕ → ℝ} {k K : ℕ}

/-- Let $0 < \gamma_1 \le \gamma_2$, $\gamma_1 \le 1$ and $\Delta_0 > 0$. Suppose that for every
$k < K$, either $\Delta_{k+1} = \Delta_k$ or $\Delta_{k+1}$ is an admissible successor of
$\Delta_k$ under the update (2.3.7) with ratio $\rho_k$. Then $\Delta_k > 0$ for all $k \le K$. -/
theorem pos_of_trUpdate_of_neutral (hγ₁ : 0 < γ₁) (hγ₁₂ : γ₁ ≤ γ₂) (hγ₁1 : γ₁ ≤ 1)
    (hΔ0 : 0 < Δ 0)
    (h : ∀ k < K, Δ (k + 1) = Δ k ∨ TRUpdate η₁ η₂ γ₁ γ₂ γ₃ (ρ k) (Δ k) (Δ (k + 1))) :
    ∀ k ≤ K, 0 < Δ k := by
  intro k
  induction k with
  | zero => exact fun _ => hΔ0
  | succ k ih =>
    intro hk
    rcases h k hk with he | hu
    · rw [he]; exact ih (Nat.le_of_succ_le hk)
    · exact hu.pos hγ₁ hγ₁₂ hγ₁1 (ih (Nat.le_of_succ_le hk))

/-- Let $0 < \gamma_1 \le \gamma_2$, $\gamma_1 \le 1$ and $\Delta_0 > 0$. If $\Delta_{k+1}$ is an
admissible successor of $\Delta_k$ under the update (2.3.7) with ratio $\rho_k$ for every
$k < K$, then $\Delta_k > 0$ for all $k \le K$. -/
theorem pos_of_trUpdate (hγ₁ : 0 < γ₁) (hγ₁₂ : γ₁ ≤ γ₂) (hγ₁1 : γ₁ ≤ 1) (hΔ0 : 0 < Δ 0)
    (h : ∀ k < K, TRUpdate η₁ η₂ γ₁ γ₂ γ₃ (ρ k) (Δ k) (Δ (k + 1))) :
    ∀ k ≤ K, 0 < Δ k :=
  pos_of_trUpdate_of_neutral hγ₁ hγ₁₂ hγ₁1 hΔ0 fun k hk => Or.inr (h k hk)

/-- **Lower bound on the trust-region radius, with unchanged iterations.** Let
$0 < \gamma_1 \le \gamma_2$, $\gamma_1 \le 1$ and $\Delta_0 > 0$. Let $(\theta_k)$ be a real
sequence with $\theta_{k+1} \le \theta_k$ for all $k < K$. Suppose that every iteration $k < K$
either leaves the radius unchanged, $\Delta_{k+1} = \Delta_k$, or satisfies the update (2.3.7)
with ratio $\rho_k$ and is very successful ($\rho_k \ge \eta_2$) whenever $\Delta_k < \theta_k$.
Then
$$\Delta_k \ge \min(\Delta_0, \gamma_1 \theta_k) \quad \text{for all } k \le K.$$

This is the mechanism of Lemma 13.1.4 of [cartis2022evaluation]. The iterations that leave the
radius unchanged are the accuracy-improving iterations of Chapter 13. -/
theorem le_delta_of_trUpdate_of_neutral (hγ₁ : 0 < γ₁) (hγ₁₂ : γ₁ ≤ γ₂) (hγ₁1 : γ₁ ≤ 1)
    (hΔ0 : 0 < Δ 0) (hθ : ∀ k < K, θ (k + 1) ≤ θ k)
    (h : ∀ k < K, Δ (k + 1) = Δ k ∨
      (TRUpdate η₁ η₂ γ₁ γ₂ γ₃ (ρ k) (Δ k) (Δ (k + 1)) ∧ (Δ k < θ k → η₂ ≤ ρ k))) :
    ∀ k ≤ K, min (Δ 0) (γ₁ * θ k) ≤ Δ k := by
  have hpos := pos_of_trUpdate_of_neutral hγ₁ hγ₁₂ hγ₁1 hΔ0 (ρ := ρ) (η₁ := η₁) (η₂ := η₂)
    (γ₃ := γ₃) fun k hk => (h k hk).imp id And.left
  intro k
  induction k with
  | zero => exact fun _ => min_le_left _ _
  | succ k ih =>
    intro hk
    have hkK : k < K := hk
    have hγθ : γ₁ * θ (k + 1) ≤ γ₁ * θ k := mul_le_mul_of_nonneg_left (hθ k hkK) hγ₁.le
    have hmono : min (Δ 0) (γ₁ * θ (k + 1)) ≤ Δ k :=
      (min_le_min le_rfl hγθ).trans (ih hkK.le)
    rcases h k hkK with he | ⟨hu, hforce⟩
    · rwa [he]
    by_cases hsmall : Δ k < θ k
    · exact hmono.trans (hu.le_of_very_successful (hforce hsmall))
    · calc min (Δ 0) (γ₁ * θ (k + 1)) ≤ γ₁ * θ k := (min_le_right _ _).trans hγθ
        _ ≤ γ₁ * Δ k := mul_le_mul_of_nonneg_left (not_lt.1 hsmall) hγ₁.le
        _ ≤ Δ (k + 1) := hu.mul_le hγ₁₂ hγ₁1 (hpos k hkK.le).le

/-- **Lower bound on the trust-region radius.** Let $0 < \gamma_1 \le \gamma_2$, $\gamma_1 \le 1$
and $\Delta_0 > 0$. Let $(\theta_k)$ be a real sequence with $\theta_{k+1} \le \theta_k$ for all
$k < K$. Suppose that $\Delta_{k+1}$ is an admissible successor of $\Delta_k$ under the update
(2.3.7) with ratio $\rho_k$ for every $k < K$, and that every iteration $k < K$ with
$\Delta_k < \theta_k$ is very successful ($\rho_k \ge \eta_2$). Then
$$\Delta_k \ge \min(\Delta_0, \gamma_1 \theta_k) \quad \text{for all } k \le K.$$

This is the mechanism of Lemmas 2.3.4, 3.2.5 and 3.4.2 of [cartis2022evaluation]. It is the
special case of `Optimization.le_delta_of_trUpdate_of_neutral` without unchanged iterations. -/
theorem le_delta_of_trUpdate (hγ₁ : 0 < γ₁) (hγ₁₂ : γ₁ ≤ γ₂) (hγ₁1 : γ₁ ≤ 1) (hΔ0 : 0 < Δ 0)
    (h : ∀ k < K, TRUpdate η₁ η₂ γ₁ γ₂ γ₃ (ρ k) (Δ k) (Δ (k + 1)))
    (hθ : ∀ k < K, θ (k + 1) ≤ θ k) (hforce : ∀ k < K, Δ k < θ k → η₂ ≤ ρ k) :
    ∀ k ≤ K, min (Δ 0) (γ₁ * θ k) ≤ Δ k :=
  le_delta_of_trUpdate_of_neutral hγ₁ hγ₁₂ hγ₁1 hΔ0 hθ fun k hk => Or.inr ⟨h k hk, hforce k hk⟩

/-- **Lower bound on the next radius.** Under the hypotheses of `Optimization.le_delta_of_trUpdate`,
$$\Delta_{k+1} \ge \min(\Delta_0, \gamma_1 \theta_k) \quad \text{for all } k < K,$$
with the threshold at $k$, not at $k + 1$.

This sharper form gives the exact constants of Theorem 2.3.7 of [cartis2022evaluation]. -/
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

/-- **Lemma 2.3.1** of [cartis2022evaluation] for the update (2.3.7), with $k + 1$ updates. Let
$\mathcal{S}_k = \{ j \le k : \rho_j \ge \eta_1 \}$ be the set of successful iterations up to
$k$. Let $0 < \gamma_2 < 1 \le \gamma_3$ and $\Delta_{\min} > 0$. Suppose that $\Delta_{j+1}$ is
an admissible successor of $\Delta_j$ under the update (2.3.7) with ratio $\rho_j$ for every
$j \le k$, and that $\Delta_{k+1} \ge \Delta_{\min}$. Then
$$k + 1 \le |\mathcal{S}_k| \left(1 + \frac{\log \gamma_3}{|\log \gamma_2|}\right) +
  \frac{1}{|\log \gamma_2|} \left|\log \frac{\Delta_{\min}}{\Delta_0}\right|.$$

The set $\mathcal{S}_k$ is `Optimization.successSet (fun j => η₁ ≤ ρ j) k`, and $\Delta_{\min}$
is `Δmin`. No sign condition on $\Delta_0$ is stated, and no condition on $\gamma_1$. -/
theorem succ_le_of_trUpdate (hγ₂ : 0 < γ₂) (hγ₂1 : γ₂ < 1) (hγ₃ : 1 ≤ γ₃)
    (h : ∀ j ≤ k, TRUpdate η₁ η₂ γ₁ γ₂ γ₃ (ρ j) (Δ j) (Δ (j + 1)))
    (hmin : 0 < Δmin) (hΔmin : Δmin ≤ Δ (k + 1)) :
    (k + 1 : ℝ) ≤
      (successSet (fun j => η₁ ≤ ρ j) k).card * (1 + Real.log γ₃ / |Real.log γ₂|) +
        |Real.log (Δmin / Δ 0)| / |Real.log γ₂| :=
  succ_le_card_successSet_of_upper_ratio hγ₂ hγ₂1 hγ₃
    (fun j hj hs => (h j hj).le_mul_of_le hs hγ₂1 hγ₃)
    (fun j hj hs => (h j hj).le_mul_of_lt (not_le.1 hs)) hmin hΔmin

/-- **Lemma 2.3.1** of [cartis2022evaluation], bound (2.3.11), with the indexing of the source. Let
$\mathcal{S}_k = \{ j \le k : \rho_j \ge \eta_1 \}$. Let $0 < \gamma_2 < 1 \le \gamma_3$ and
$\Delta_{\min} > 0$. Suppose that $\Delta_{j+1}$ is an admissible successor of $\Delta_j$ under
the update (2.3.7) with ratio $\rho_j$ for every $j < k$, and that $\Delta_k \ge \Delta_{\min}$.
Then
$$k \le |\mathcal{S}_k| \left(1 + \frac{\log \gamma_3}{|\log \gamma_2|}\right) + \frac{1}{|\log
  \gamma_2|} \left|\log \frac{\Delta_{\min}}{\Delta_0}\right|.$$

The set $\mathcal{S}_k$ is `Optimization.successSet (fun j => η₁ ≤ ρ j) k`. Its index range
$\{0, \dots, k\}$ includes $k$, so $|\mathcal{S}_k|$ counts iteration $k$ when
$\rho_k \ge \eta_1$, although the hypotheses do not use the update at $k$. -/
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
