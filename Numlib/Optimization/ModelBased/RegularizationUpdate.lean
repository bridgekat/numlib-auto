/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Optimization.Complexity.ParameterCount

/-!
# The adaptive-regularization parameter update

Adaptive-regularization methods update the regularization parameter $\sigma$ after each iteration
according to the reduction ratio $\rho$ of the iteration. This file formalizes the rule (2.4.4) of
[cartis2022evaluation], which is stated in the same form for AR1, for AR2 (3.3.8) and for ARp
(4.1.16). Let $0 < \eta_1 \le \eta_2 < 1$, $0 < \gamma_1 < 1 < \gamma_2 < \gamma_3$ and
$\sigma_{\min} > 0$. The new parameter $\sigma^+$ satisfies
$$\sigma^+ \in \begin{cases}
  [\max(\sigma_{\min}, \gamma_1 \sigma), \sigma] & \text{if } \rho \ge \eta_2
    \text{ (very successful iteration)}, \\
  [\sigma, \gamma_2 \sigma] & \text{if } \eta_1 \le \rho < \eta_2 \text{ (successful iteration)}, \\
  [\gamma_2 \sigma, \gamma_3 \sigma] & \text{if } \rho < \eta_1 \text{ (unsuccessful iteration)}.
  \end{cases}$$
Some later variants, for example those of Section 5.5 of [cartis2022evaluation], use different
rules, and this file does not cover them.

The rule leaves a choice, so it is a predicate on $(\sigma, \sigma^+)$. Its consequences are shared
by all chapters: the parameters stay positive and at least $\sigma_{\min}$; they stay below
$\max(\sigma_0, \gamma_3 \bar\sigma)$ when $\sigma_k \ge \bar\sigma$ forces a very successful
iteration; and the number of iterations is bounded in terms of the number of successful iterations.
Each result also holds when some iterations leave $\sigma$ unchanged, as the accuracy-improving
iterations of Chapter 13 of [cartis2022evaluation] do.

## Main definitions

* `Optimization.ARUpdate`: $\sigma'$ is an admissible successor of $\sigma$ under the rule (2.4.4)
  after an iteration with ratio $\rho$.

## Main results

* `Optimization.pos_of_arUpdate`: the parameters $\sigma_k$ stay positive.
* `Optimization.le_sigma_of_arUpdate`: the parameters stay at least $\sigma_{\min}$.
* `Optimization.sigma_le_max_of_arUpdate`: if $\sigma_k \ge \bar\sigma$ forces a very successful
  iteration, then $\sigma_k \le \max(\sigma_0, \gamma_3 \bar\sigma)$. This is the mechanism of
  Lemmas 2.4.2, 3.3.2 and 4.1.2 of [cartis2022evaluation].
* `Optimization.pos_of_arUpdate_of_neutral` and `Optimization.sigma_le_max_of_arUpdate_of_neutral`:
  the same statements when some iterations leave $\sigma$ unchanged. The statements without
  unchanged iterations are special cases.
* `Optimization.succ_le_of_arUpdate` and `Optimization.le_of_arUpdate`: the number of iterations is
  bounded in terms of the number of successful iterations, as in Lemma 2.4.1 of
  [cartis2022evaluation].

## Implementation notes

* Each hypothesis on the constants $\eta_i$, $\gamma_i$ and $\sigma_{\min}$ appears only in the
  results that use it.
* A sequence of parameters is a function `σ : ℕ → ℝ`, and the ratios are `ρ : ℕ → ℝ`.
-/

namespace Optimization

/-- The **adaptive-regularization update** (2.4.4) of [cartis2022evaluation]: $\sigma'$ is an
admissible successor of the regularization parameter $\sigma$ after an iteration with reduction
ratio $\rho$. That is,
* if $\rho \ge \eta_2$, then $\max(\sigma_{\min}, \gamma_1 \sigma) \le \sigma' \le \sigma$;
* if $\eta_1 \le \rho < \eta_2$, then $\sigma \le \sigma' \le \gamma_2 \sigma$;
* if $\rho < \eta_1$, then $\gamma_2 \sigma \le \sigma' \le \gamma_3 \sigma$.

The structure puts no conditions on the constants. In Lean, $\sigma_{\min}$ is `σmin`. -/
structure ARUpdate (η₁ η₂ γ₁ γ₂ γ₃ σmin ρ σ σ' : ℝ) : Prop where
  /-- At a very successful iteration ($\rho \ge \eta_2$), $\max(\sigma_{\min}, \gamma_1 \sigma) \le
  \sigma' \le \sigma$. -/
  very_successful : η₂ ≤ ρ → max σmin (γ₁ * σ) ≤ σ' ∧ σ' ≤ σ
  /-- At a successful iteration ($\eta_1 \le \rho < \eta_2$),
  $\sigma \le \sigma' \le \gamma_2 \sigma$. -/
  successful : η₁ ≤ ρ → ρ < η₂ → σ ≤ σ' ∧ σ' ≤ γ₂ * σ
  /-- At an unsuccessful iteration ($\rho < \eta_1$), $\gamma_2 \sigma \le \sigma' \le \gamma_3
  \sigma$. -/
  unsuccessful : ρ < η₁ → γ₂ * σ ≤ σ' ∧ σ' ≤ γ₃ * σ

namespace ARUpdate

variable {η₁ η₂ γ₁ γ₂ γ₃ σmin ρ σ σ' : ℝ} (h : ARUpdate η₁ η₂ γ₁ γ₂ γ₃ σmin ρ σ σ')
include h

/-- At a very successful iteration ($\rho \ge \eta_2$), the parameter does not increase:
$\sigma' \le \sigma$. -/
theorem le_of_very_successful (hρ : η₂ ≤ ρ) : σ' ≤ σ := (h.very_successful hρ).2

/-- At a very successful iteration ($\rho \ge \eta_2$), the new parameter is at least
$\sigma_{\min}$. -/
theorem sigmaMin_le_of_very_successful (hρ : η₂ ≤ ρ) : σmin ≤ σ' :=
  (le_max_left _ _).trans (h.very_successful hρ).1

/-- At a successful iteration ($\rho \ge \eta_1$), the parameter decreases at most by the factor
$\gamma_1$: if $\gamma_1 \le 1$ and $\sigma \ge 0$, then $\gamma_1 \sigma \le \sigma'$. -/
theorem mul_le_of_le (hρ : η₁ ≤ ρ) (hγ₁ : γ₁ ≤ 1) (hσ : 0 ≤ σ) : γ₁ * σ ≤ σ' := by
  by_cases h2 : η₂ ≤ ρ
  · exact (le_max_right _ _).trans (h.very_successful h2).1
  · exact (mul_le_of_le_one_left hσ hγ₁).trans (h.successful hρ (not_le.1 h2)).1

/-- At an unsuccessful iteration ($\rho < \eta_1$), the parameter increases at least by the factor
$\gamma_2$: $\gamma_2 \sigma \le \sigma'$. -/
theorem mul_le_of_lt (hρ : ρ < η₁) : γ₂ * σ ≤ σ' := (h.unsuccessful hρ).1

/-- At an iteration that is not very successful ($\rho < \eta_2$), the parameter does not decrease:
if $\gamma_2 \ge 1$ and $\sigma \ge 0$, then $\sigma \le \sigma'$. -/
theorem le_of_lt (hρ : ρ < η₂) (hγ₂ : 1 ≤ γ₂) (hσ : 0 ≤ σ) : σ ≤ σ' := by
  by_cases h1 : η₁ ≤ ρ
  · exact (h.successful h1 hρ).1
  · exact (le_mul_of_one_le_left hσ hγ₂).trans (h.mul_le_of_lt (not_le.1 h1))

/-- The parameter increases at most by the factor $\gamma_3$: if $\gamma_2 \le \gamma_3$,
$\gamma_3 \ge 1$ and $\sigma \ge 0$, then $\sigma' \le \gamma_3 \sigma$. -/
theorem le_mul (hγ₂₃ : γ₂ ≤ γ₃) (hγ₃ : 1 ≤ γ₃) (hσ : 0 ≤ σ) : σ' ≤ γ₃ * σ := by
  by_cases h1 : η₁ ≤ ρ
  · by_cases h2 : η₂ ≤ ρ
    · exact (h.le_of_very_successful h2).trans (le_mul_of_one_le_left hσ hγ₃)
    · exact (h.successful h1 (not_le.1 h2)).2.trans (mul_le_mul_of_nonneg_right hγ₂₃ hσ)
  · exact (h.unsuccessful (not_le.1 h1)).2

/-- The update preserves positivity: if $\gamma_1 > 0$, $\gamma_2 > 0$ and $\sigma > 0$, then
$\sigma' > 0$. -/
theorem pos (hγ₁ : 0 < γ₁) (hγ₂ : 0 < γ₂) (hσ : 0 < σ) : 0 < σ' := by
  by_cases h1 : η₁ ≤ ρ
  · by_cases h2 : η₂ ≤ ρ
    · exact (mul_pos hγ₁ hσ).trans_le ((le_max_right _ _).trans (h.very_successful h2).1)
    · exact hσ.trans_le (h.successful h1 (not_le.1 h2)).1
  · exact (mul_pos hγ₂ hσ).trans_le (h.mul_le_of_lt (not_le.1 h1))

/-- The update preserves the lower bound $\sigma_{\min}$: if $\sigma_{\min} \ge 0$, $\gamma_2 \ge 1$
and $\sigma \ge \sigma_{\min}$, then $\sigma' \ge \sigma_{\min}$. -/
theorem sigmaMin_le (hmin : 0 ≤ σmin) (hγ₂ : 1 ≤ γ₂) (hσ : σmin ≤ σ) : σmin ≤ σ' := by
  by_cases h2 : η₂ ≤ ρ
  · exact h.sigmaMin_le_of_very_successful h2
  · exact hσ.trans (h.le_of_lt (not_le.1 h2) hγ₂ (hmin.trans hσ))

end ARUpdate

section sequence

variable {η₁ η₂ γ₁ γ₂ γ₃ σmin σbar σmax : ℝ} {ρ σ : ℕ → ℝ} {k K : ℕ}

/-- Let $\gamma_1 > 0$, $\gamma_2 > 0$ and $\sigma_0 > 0$. Suppose that for every $k < K$, either
$\sigma_{k+1} = \sigma_k$ or $\sigma_{k+1}$ is an admissible successor of $\sigma_k$ under the
update (2.4.4) with ratio $\rho_k$. Then $\sigma_k > 0$ for all $k \le K$. -/
theorem pos_of_arUpdate_of_neutral (hγ₁ : 0 < γ₁) (hγ₂ : 0 < γ₂) (hσ0 : 0 < σ 0)
    (h : ∀ k < K, σ (k + 1) = σ k ∨ ARUpdate η₁ η₂ γ₁ γ₂ γ₃ σmin (ρ k) (σ k) (σ (k + 1))) :
    ∀ k ≤ K, 0 < σ k := by
  intro k
  induction k with
  | zero => exact fun _ => hσ0
  | succ k ih =>
    intro hk
    rcases h k hk with he | hu
    · rw [he]; exact ih (Nat.le_of_succ_le hk)
    · exact hu.pos hγ₁ hγ₂ (ih (Nat.le_of_succ_le hk))

/-- Let $\gamma_1 > 0$, $\gamma_2 > 0$ and $\sigma_0 > 0$. If $\sigma_{k+1}$ is an admissible
successor of $\sigma_k$ under the update (2.4.4) with ratio $\rho_k$ for every $k < K$, then
$\sigma_k > 0$ for all $k \le K$. -/
theorem pos_of_arUpdate (hγ₁ : 0 < γ₁) (hγ₂ : 0 < γ₂) (hσ0 : 0 < σ 0)
    (h : ∀ k < K, ARUpdate η₁ η₂ γ₁ γ₂ γ₃ σmin (ρ k) (σ k) (σ (k + 1))) :
    ∀ k ≤ K, 0 < σ k :=
  pos_of_arUpdate_of_neutral hγ₁ hγ₂ hσ0 fun k hk => Or.inr (h k hk)

/-- The regularization parameters stay at least $\sigma_{\min}$. Let $\sigma_{\min} \ge 0$,
$\gamma_2 \ge 1$ and $\sigma_0 \ge \sigma_{\min}$. If $\sigma_{k+1}$ is an admissible successor
of $\sigma_k$ under the update (2.4.4) with ratio $\rho_k$ for every $k < K$, then
$$\sigma_k \ge \sigma_{\min} \quad \text{for all } k \le K.$$

This is the argument in the proof of Lemma 3.3.4 of [cartis2022evaluation]. -/
theorem le_sigma_of_arUpdate (hmin : 0 ≤ σmin) (hγ₂ : 1 ≤ γ₂) (h0 : σmin ≤ σ 0)
    (h : ∀ k < K, ARUpdate η₁ η₂ γ₁ γ₂ γ₃ σmin (ρ k) (σ k) (σ (k + 1))) :
    ∀ k ≤ K, σmin ≤ σ k := by
  intro k
  induction k with
  | zero => exact fun _ => h0
  | succ k ih => exact fun hk => (h k hk).sigmaMin_le hmin hγ₂ (ih (Nat.le_of_succ_le hk))

/-- **Upper bound on the regularization parameter, with unchanged iterations.** Let $\gamma_1 > 0$,
$\gamma_2 > 0$, $\gamma_2 \le \gamma_3$, $\gamma_3 \ge 1$ and $\sigma_0 > 0$, and let
$\bar\sigma \in \mathbb{R}$. Suppose that every iteration $k < K$ either leaves the parameter
unchanged, $\sigma_{k+1} = \sigma_k$, or satisfies the update (2.4.4) with ratio $\rho_k$ and is
very successful ($\rho_k \ge \eta_2$) whenever $\sigma_k \ge \bar\sigma$. Then
$$\sigma_k \le \max(\sigma_0, \gamma_3 \bar\sigma) \quad \text{for all } k \le K.$$

This is the mechanism of the bound on $\sigma_k$ for the methods ARqpIDA and ARqpEDA, in Lemmas
13.1.14 and 13.3.5 of [cartis2022evaluation]. The iterations that leave $\sigma$ unchanged are
the accuracy-improving iterations of these methods. -/
theorem sigma_le_max_of_arUpdate_of_neutral (hγ₁ : 0 < γ₁) (hγ₂ : 0 < γ₂) (hγ₂₃ : γ₂ ≤ γ₃)
    (hγ₃ : 1 ≤ γ₃) (hσ0 : 0 < σ 0)
    (h : ∀ k < K, σ (k + 1) = σ k ∨
      (ARUpdate η₁ η₂ γ₁ γ₂ γ₃ σmin (ρ k) (σ k) (σ (k + 1)) ∧ (σbar ≤ σ k → η₂ ≤ ρ k))) :
    ∀ k ≤ K, σ k ≤ max (σ 0) (γ₃ * σbar) := by
  have hpos := pos_of_arUpdate_of_neutral hγ₁ hγ₂ hσ0 fun k hk => (h k hk).imp id And.left
  intro k
  induction k with
  | zero => exact fun _ => le_max_left _ _
  | succ k ih =>
    intro hk
    have hkK : k < K := hk
    rcases h k hkK with he | ⟨hu, hforce⟩
    · rw [he]; exact ih hkK.le
    by_cases hbar : σbar ≤ σ k
    · exact (hu.le_of_very_successful (hforce hbar)).trans (ih hkK.le)
    · calc σ (k + 1) ≤ γ₃ * σ k := hu.le_mul hγ₂₃ hγ₃ (hpos k hkK.le).le
        _ ≤ γ₃ * σbar := mul_le_mul_of_nonneg_left (not_le.1 hbar).le (zero_le_one.trans hγ₃)
        _ ≤ max (σ 0) (γ₃ * σbar) := le_max_right _ _

/-- **Upper bound on the regularization parameter.** Let $\gamma_1 > 0$, $\gamma_2 > 0$,
$\gamma_2 \le \gamma_3$, $\gamma_3 \ge 1$ and $\sigma_0 > 0$, and let
$\bar\sigma \in \mathbb{R}$. Suppose that $\sigma_{k+1}$ is an admissible successor of
$\sigma_k$ under the update (2.4.4) with ratio $\rho_k$ for every $k < K$, and that every
iteration $k < K$ with $\sigma_k \ge \bar\sigma$ is very successful ($\rho_k \ge \eta_2$). Then
$$\sigma_k \le \max(\sigma_0, \gamma_3 \bar\sigma) \quad \text{for all } k \le K.$$

This is the mechanism of Lemmas 2.4.2, 3.3.2 and 4.1.2 of [cartis2022evaluation]. It is the
special case of `Optimization.sigma_le_max_of_arUpdate_of_neutral` without unchanged iterations. -/
theorem sigma_le_max_of_arUpdate (hγ₁ : 0 < γ₁) (hγ₂ : 0 < γ₂) (hγ₂₃ : γ₂ ≤ γ₃)
    (hγ₃ : 1 ≤ γ₃) (hσ0 : 0 < σ 0)
    (h : ∀ k < K, ARUpdate η₁ η₂ γ₁ γ₂ γ₃ σmin (ρ k) (σ k) (σ (k + 1)))
    (hforce : ∀ k < K, σbar ≤ σ k → η₂ ≤ ρ k) :
    ∀ k ≤ K, σ k ≤ max (σ 0) (γ₃ * σbar) :=
  sigma_le_max_of_arUpdate_of_neutral hγ₁ hγ₂ hγ₂₃ hγ₃ hσ0 fun k hk =>
    Or.inr ⟨h k hk, hforce k hk⟩

/-- **Lemma 2.4.1** of [cartis2022evaluation] for the update (2.4.4), with $k + 1$ updates. Let
$\mathcal{S}_k = \{ j \le k : \rho_j \ge \eta_1 \}$ be the set of successful iterations up to
$k$. Let $0 < \gamma_1 \le 1 < \gamma_2$ and $\sigma_0 > 0$. Suppose that $\sigma_{j+1}$ is an
admissible successor of $\sigma_j$ under the update (2.4.4) with ratio $\rho_j$ for every
$j \le k$, and that $\sigma_{k+1} \le \sigma_{\max}$. Then
$$k + 1 \le |\mathcal{S}_k| \left(1 + \frac{|\log \gamma_1|}{\log \gamma_2}\right) +
  \frac{1}{\log \gamma_2} \log \frac{\sigma_{\max}}{\sigma_0}.$$

The set $\mathcal{S}_k$ is `Optimization.successSet (fun j => η₁ ≤ ρ j) k`, and $\sigma_{\max}$
is `σmax`. -/
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

/-- **Lemma 2.4.1** of [cartis2022evaluation], bound (2.4.8), with the indexing of the source. Let
$\mathcal{S}_k = \{ j \le k : \rho_j \ge \eta_1 \}$. Let $0 < \gamma_1 \le 1 < \gamma_2$ and
$\sigma_0 > 0$. Suppose that $\sigma_{j+1}$ is an admissible successor of $\sigma_j$ under the
update (2.4.4) with ratio $\rho_j$ for every $j < k$, and that $\sigma_k \le \sigma_{\max}$.
Then
$$k \le |\mathcal{S}_k| \left(1 + \frac{|\log \gamma_1|}{\log \gamma_2}\right) + \frac{1}{\log
  \gamma_2} \log \frac{\sigma_{\max}}{\sigma_0}.$$

The set $\mathcal{S}_k$ is `Optimization.successSet (fun j => η₁ ≤ ρ j) k`. Its index range
$\{0, \dots, k\}$ includes $k$, so $|\mathcal{S}_k|$ counts iteration $k$ when
$\rho_k \ge \eta_1$, although the hypotheses do not use the update at $k$. -/
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
