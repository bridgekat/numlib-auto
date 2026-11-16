/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Safeguarded interval reduction for the multiplier of a subproblem

Algorithm 9.2.1 of [cartis2022evaluation], which follows Moré and Sorensen and Section 7.3.6 of
[conn2000trust], looks for a multiplier $\lambda$ in the good set
$\mathcal{L} = (\lambda_s, \lambda_*]$. It keeps a bracket $[\lambda^L, \lambda^U]$ that contains
$\lambda_*$ and shrinks it. A trial value $\lambda_C \le \lambda_s$ (in the set $\mathcal{N}$)
raises the lower end, a trial value $\lambda_C > \lambda_*$ (in the set $\mathcal{G}$) lowers the
upper end, and the next trial value is a safeguarded convex or geometric combination of the two
ends. The run only tests in which of the three pieces of the partition $\mathbb{R} = (-\infty, a]
\cup (a, b] \cup (b, \infty)$ the trial value lies. Therefore this file formalizes the algorithm for
an arbitrary partition; for the subproblems, $a = \lambda_s$ and $b = \lambda_*$.

A run (`Subproblem.IsBracketRun`) consists of the sequences of lower ends, upper ends and trial
values. Each nondeterministic choice of the book is quantified existentially: the parameters
$\theta \in [\theta_L, \theta_U]$ and $\gamma \in \{0, 1\}$, the optional improvements
$-\lambda_E \le \lambda_s$ of the lower end, and the choice of the new trial value in the interval
(9.2.2). The run is constant once a trial value lies in $(a, b]$. The file proves that runs exist,
that the bracket contains $b$ and shrinks, that the width contracts by a uniform factor $\rho < 1$,
and that a run stops after an explicit number of steps when $a < b$ and the initial lower end is
below $b$.

## Main definitions

* `Subproblem.bracketEstimate`: the safeguarded trial value
  $\max(\gamma \sqrt{lu}, \, l + \theta (u - l))$ of the bracket $[l, u]$.
* `Subproblem.IsLowerUpdate`: a lower end $l$ either stays or becomes $\max(l, e)$ for an estimate
  $e \le a$.
* `Subproblem.IsBracketRun`: the sequences of lower ends, upper ends and trial values form a run of
  Algorithm 9.2.1.

## Main results

* `Subproblem.IsBracketRun.exists`: runs exist from any admissible initial bracket.
* `Subproblem.IsBracketRun.mem_of_le`: a run is constant after the first trial value in $(a, b]$.
* `Subproblem.IsBracketRun.invariant`: the bracket contains $b$, the lower ends increase, the upper
  ends decrease, and each trial value that does not stop the run lies in the bracket.
* `Subproblem.IsBracketRun.width_le`: after the first step, each step multiplies the width of the
  bracket by at most $\rho = \max(1 - \theta_L, \theta_U, 1/2) < 1$.
* `Subproblem.IsBracketRun.exists_mem`: if $a < b$ and the initial lower end is below $b$, the run
  stops, with an explicit bound on the number of steps.
* `Subproblem.IsBracketRun.tendsto_bracket_of_never_mem`: a run that never stops has ends and trial
  values that converge to $b$.
* `Subproblem.IsBracketRun.frequently_gt_of_eq`: if $a = b$ and the initial upper end exceeds $b$,
  trial values above $b$ occur infinitely often.

## Proof outline

The ratio of two successive widths is at most $\max(1 - \theta, \theta, \gamma \sqrt{\lambda^U} /
(\sqrt{\lambda^L} + \sqrt{\lambda^U}))$, which is not uniformly below $1$. But when the geometric
branch moves the upper end, it contracts the width by the factor $\sqrt{\lambda^L} /
(\sqrt{\lambda^L} + \sqrt{\lambda^U}) \le 1/2$, and this gives the uniform factor $\rho$. While the
run has not stopped, the bracket keeps a width of at least $b - \max(\lambda^L_0, a)$, which gives
the bound on the number of steps. Finite termination needs the initial lower end below $b$: if
$\lambda^L = \lambda_*$ at the start, a run need not stop, even when $\mathcal{L}$ is nonempty,
because every trial value exceeds $\lambda_*$ while the upper end does.
-/

open Set Filter
open scoped Topology

namespace Subproblem

/-- The safeguarded trial value of Algorithm 9.2.1 of [cartis2022evaluation] for the bracket
$[l, u]$:
$$\max\bigl(\gamma \sqrt{l u}, \; l + \theta (u - l)\bigr).$$
For $\gamma = 1$ it is the geometric mean of the ends, safeguarded by the convex combination
$l + \theta (u - l)$; for $\gamma = 0$ it is the convex combination alone when that is
nonnegative. -/
noncomputable def bracketEstimate (γ θ l u : ℝ) : ℝ := max (γ * √(l * u)) (l + θ * (u - l))

/-- An update $l \mapsto l'$ of the lower end of a bracket is **admissible for $a$** if $l' = l$, or
$l' = \max(l, e)$ for some estimate $e \le a$. In the book, $e = -\lambda_E$ for an upper bound
$\lambda_E \ge \lambda_1$ of the leftmost eigenvalue, so that $-\lambda_E \le \lambda_s$. -/
def IsLowerUpdate (a l l' : ℝ) : Prop := l' = l ∨ ∃ e ≤ a, l' = max l e

/-- A **run of Algorithm 9.2.1** of [cartis2022evaluation] for the partition $\mathbb{R} = (-\infty,
a] \cup (a, b] \cup (b, \infty)$ and the parameters $\theta_L$, $\theta_U$. It consists of
sequences $(l_k)$ of lower ends, $(u_k)$ of upper ends and $(c_k)$ of trial values with
$0 \le l_0 \le b \le u_0$, and at every step $k$:

* if $c_k \in (a, b]$, the run has stopped, and $l_{k+1} = l_k$, $u_{k+1} = u_k$,
  $c_{k+1} = c_k$;
* if $c_k \le a$, then $u_{k+1} = u_k$, the lower end $l_{k+1}$ is an admissible update
  (`Subproblem.IsLowerUpdate`) of $\max(l_k, c_k)$, and $c_{k+1}$ is the trial value
  (`Subproblem.bracketEstimate`) with parameters $(\gamma, \theta)$ of $[l_{k+1}, u_{k+1}]$ for
  some $\theta \in [\theta_L, \theta_U]$ and $\gamma \in \{0, 1\}$;
* if $c_k > b$, then $u_{k+1} = \min(u_k, c_k)$, the lower end $l_{k+1}$ is an admissible update
  of $l_k$, and $c_{k+1}$ lies in the interval (9.2.2) between the trial values for
  $(\gamma_1, \theta_l)$ and $(\gamma_2, \theta_u)$ of $[l_{k+1}, u_{k+1}]$, for some
  $\theta_l \le \theta_u$ in $[\theta_L, \theta_U]$ and $\gamma_1 \le \gamma_2$ in $\{0, 1\}$.

The condition $l_0 \le b \le u_0$ is (9.2.1) for the target $b$, and $l_0 \ge 0$ holds because
the multipliers are nonnegative. The structure does not require $\theta_L \le \theta_U$; the
theorems state the conditions on the parameters that they need. -/
structure IsBracketRun (a b θL θU : ℝ) (lo hi c : ℕ → ℝ) : Prop where
  /-- The initial lower end is nonnegative: $l_0 \ge 0$. -/
  nonneg : 0 ≤ lo 0
  /-- The initial lower end is at most the target: $l_0 \le b$, as in (9.2.1). -/
  lo_zero_le : lo 0 ≤ b
  /-- The initial upper end is at least the target: $b \le u_0$, as in (9.2.1). -/
  le_hi_zero : b ≤ hi 0
  /-- A trial value $c_k \in (a, b]$, that is, in $\mathcal{L}$, stops the run: $l_{k+1} = l_k$,
  $u_{k+1} = u_k$ and $c_{k+1} = c_k$. -/
  exit : ∀ k, c k ∈ Ioc a b → lo (k + 1) = lo k ∧ hi (k + 1) = hi k ∧ c (k + 1) = c k
  /-- A trial value $c_k \le a$, that is, in $\mathcal{N}$, keeps the upper end and raises the lower
  end to an admissible update of $\max(l_k, c_k)$; the next trial value is the trial value
  (`Subproblem.bracketEstimate`) with parameters $(\gamma, \theta)$ of the new bracket, for some
  $\theta \in [\theta_L, \theta_U]$ and $\gamma \in \{0, 1\}$. -/
  left : ∀ k, c k ≤ a → hi (k + 1) = hi k ∧ IsLowerUpdate a (max (lo k) (c k)) (lo (k + 1)) ∧
    ∃ θ ∈ Icc θL θU, ∃ γ ∈ ({0, 1} : Set ℝ),
      c (k + 1) = bracketEstimate γ θ (lo (k + 1)) (hi (k + 1))
  /-- A trial value $c_k > b$, that is, in $\mathcal{G}$, lowers the upper end to $\min(u_k, c_k)$
  and updates the lower end admissibly; the next trial value lies in the interval (9.2.2) of the
  new bracket, between the trial values (`Subproblem.bracketEstimate`) with parameters
  $(\gamma_1, \theta_l)$ and $(\gamma_2, \theta_u)$, for some $\theta_l \le \theta_u$ in
  $[\theta_L, \theta_U]$ and $\gamma_1 \le \gamma_2$ in $\{0, 1\}$. -/
  right : ∀ k, b < c k → hi (k + 1) = min (hi k) (c k) ∧ IsLowerUpdate a (lo k) (lo (k + 1)) ∧
    ∃ θl ∈ Icc θL θU, ∃ θu ∈ Icc θL θU, θl ≤ θu ∧ ∃ γ₁ ∈ ({0, 1} : Set ℝ),
      ∃ γ₂ ∈ ({0, 1} : Set ℝ), γ₁ ≤ γ₂ ∧
        c (k + 1) ∈ Icc (bracketEstimate γ₁ θl (lo (k + 1)) (hi (k + 1)))
          (bracketEstimate γ₂ θu (lo (k + 1)) (hi (k + 1)))

/-! ### The trial value -/

section Estimate

variable {γ θ l u : ℝ}

/-- The trial value is at least the convex combination: $l + \theta (u - l) \le \max(\gamma
\sqrt{lu}, l + \theta(u - l))$. -/
theorem le_bracketEstimate (γ θ l u : ℝ) : l + θ * (u - l) ≤ bracketEstimate γ θ l u :=
  le_max_right _ _

/-- For $\gamma \in \{0, 1\}$, the trial value is at most $\max(\sqrt{lu}, \, l + \theta (u - l))$.
-/
theorem bracketEstimate_le_max_sqrt (hγ : γ ∈ ({0, 1} : Set ℝ)) :
    bracketEstimate γ θ l u ≤ max √(l * u) (l + θ * (u - l)) := by
  refine max_le_max ?_ le_rfl
  rcases hγ with rfl | rfl <;> simp [Real.sqrt_nonneg]

/-- For $0 \le l \le u$, the geometric mean exceeds $l$ by at most half the width:
$\sqrt{lu} - l \le (u - l) / 2$. -/
theorem sqrt_mul_sub_le (hl : 0 ≤ l) (hlu : l ≤ u) : √(l * u) - l ≤ (u - l) / 2 := by
  have h : √(l * u) ≤ (l + u) / 2 :=
    (Real.sqrt_le_left (by linarith)).2 (by nlinarith [sq_nonneg (u - l)])
  linarith

/-- For $0 \le l \le u$, the geometric mean is at most the upper end: $\sqrt{lu} \le u$. -/
theorem sqrt_mul_le_right (hl : 0 ≤ l) (hlu : l ≤ u) : √(l * u) ≤ u :=
  (Real.sqrt_le_left (hl.trans hlu)).2 (by nlinarith)

/-- For $0 \le l \le u$, $\gamma \in \{0, 1\}$ and $\theta \in [0, 1]$, the trial value lies in
$[l, u]$. -/
theorem bracketEstimate_mem_Icc (hl : 0 ≤ l) (hlu : l ≤ u) (hγ : γ ∈ ({0, 1} : Set ℝ))
    (hθ : θ ∈ Icc (0 : ℝ) 1) : bracketEstimate γ θ l u ∈ Icc l u := by
  have hw : 0 ≤ u - l := sub_nonneg.2 hlu
  refine ⟨le_trans (by nlinarith [hθ.1]) (le_bracketEstimate γ θ l u),
    (bracketEstimate_le_max_sqrt hγ).trans (max_le (sqrt_mul_le_right hl hlu) ?_)⟩
  nlinarith [hθ.2]

end Estimate

/-- If $a \le a'$, an update of the lower end that is admissible for $a$ is admissible for $a'$,
because an estimate $e \le a$ also satisfies $e \le a'$. -/
theorem IsLowerUpdate.mono {a a' l l' : ℝ} (haa : a ≤ a') (h : IsLowerUpdate a l l') :
    IsLowerUpdate a' l l' := by
  rcases h with h | ⟨e, he, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨e, he.trans haa, h⟩

/-- An admissible update does not decrease the lower end: $l \le l'$. -/
theorem IsLowerUpdate.le {a l l' : ℝ} (h : IsLowerUpdate a l l') : l ≤ l' := by
  rcases h with rfl | ⟨e, -, rfl⟩
  · exact le_rfl
  · exact le_max_left _ _

/-- An update admissible for $a$ gives a lower end at most $\max(l, a)$. -/
theorem IsLowerUpdate.le_max {a l l' : ℝ} (h : IsLowerUpdate a l l') : l' ≤ max l a := by
  rcases h with rfl | ⟨e, he, rfl⟩
  · exact le_max_left _ _
  · exact max_le_max le_rfl he

/-! ### Existence -/

/-- One deterministic step of Algorithm 9.2.1 with $\theta = \theta_L$, $\gamma = 0$ and no
estimates of the lower end, on the state (lower end, upper end, trial value). -/
private noncomputable def bracketStep (a b θ : ℝ) (s : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  if a < s.2.2 ∧ s.2.2 ≤ b then s
  else if s.2.2 ≤ a then (max s.1 s.2.2, s.2.1, bracketEstimate 0 θ (max s.1 s.2.2) s.2.1)
  else (s.1, min s.2.1 s.2.2, bracketEstimate 0 θ s.1 (min s.2.1 s.2.2))

/-- **Runs exist.** Let $a \le b$ and $\theta_L \le \theta_U$. For all real numbers $l_0$, $u_0$,
$c_0$ with $0 \le l_0 \le b \le u_0$, there is a run of Algorithm 9.2.1 with lower end $l_0$,
upper end $u_0$ and trial value $c_0$ at step $0$.

The run constructed in the proof is deterministic: it takes $\theta = \theta_L$, $\gamma = 0$
and no estimates of the lower end. -/
theorem IsBracketRun.exists {a b θL θU lo₀ hi₀ c₀ : ℝ} (hab : a ≤ b) (hθ : θL ≤ θU)
    (h0 : 0 ≤ lo₀) (hlo : lo₀ ≤ b) (hhi : b ≤ hi₀) :
    ∃ lo hi c : ℕ → ℝ, IsBracketRun a b θL θU lo hi c ∧ lo 0 = lo₀ ∧ hi 0 = hi₀ ∧ c 0 = c₀ := by
  set s : ℕ → ℝ × ℝ × ℝ := fun k => (bracketStep a b θL)^[k] (lo₀, hi₀, c₀) with hs
  have hsucc : ∀ k, s (k + 1) = bracketStep a b θL (s k) := fun k => by
    simp only [hs, Function.iterate_succ_apply']
  have hθmem : θL ∈ Icc θL θU := ⟨le_rfl, hθ⟩
  have h0mem : (0 : ℝ) ∈ ({0, 1} : Set ℝ) := Or.inl rfl
  have e1 : ∀ k, (s k).2.2 ∈ Ioc a b → s (k + 1) = s k := fun k hk => by
    rw [hsucc, bracketStep, ite_eq_left (show a < (s k).2.2 ∧ (s k).2.2 ≤ b from hk)]
  have e2 : ∀ k, (s k).2.2 ≤ a → s (k + 1) = (max (s k).1 (s k).2.2, (s k).2.1,
      bracketEstimate 0 θL (max (s k).1 (s k).2.2) (s k).2.1) := fun k hk => by
    have hn : ¬ (a < (s k).2.2 ∧ (s k).2.2 ≤ b) := fun h => absurd hk (not_le.2 h.1)
    rw [hsucc, bracketStep, ite_eq_right hn, ite_eq_left hk]
  have e3 : ∀ k, b < (s k).2.2 → s (k + 1) = ((s k).1, min (s k).2.1 (s k).2.2,
      bracketEstimate 0 θL (s k).1 (min (s k).2.1 (s k).2.2)) := fun k hk => by
    have hn : ¬ (a < (s k).2.2 ∧ (s k).2.2 ≤ b) := fun h => absurd hk (not_lt.2 h.2)
    have hn' : ¬ (s k).2.2 ≤ a := fun h => absurd (h.trans hab) (not_le.2 hk)
    rw [hsucc, bracketStep, ite_eq_right hn, ite_eq_right hn']
  refine ⟨fun k => (s k).1, fun k => (s k).2.1, fun k => (s k).2.2, ⟨h0, hlo, hhi, ?_, ?_, ?_⟩,
    rfl, rfl, rfl⟩
  · intro k hk
    rw [e1 k hk]
    exact ⟨rfl, rfl, rfl⟩
  · intro k hk
    rw [e2 k hk]
    exact ⟨rfl, Or.inl rfl, θL, hθmem, 0, h0mem, rfl⟩
  · intro k hk
    rw [e3 k hk]
    exact ⟨rfl, Or.inl rfl, θL, hθmem, θL, hθmem, le_rfl, 0, h0mem, 0, h0mem, le_rfl,
      le_rfl, le_rfl⟩

/-! ### Invariants -/

namespace IsBracketRun

variable {a b θL θU : ℝ} {lo hi c : ℕ → ℝ} (h : IsBracketRun a b θL θU lo hi c)
include h

/-- **Exit is stable.** If the trial value $c_k$ of a run lies in $(a, b]$, then $c_n = c_k$,
$l_n = l_k$ and $u_n = u_k$ for all $n \ge k$. -/
theorem mem_of_le {k : ℕ} (hk : c k ∈ Ioc a b) {n : ℕ} (hkn : k ≤ n) :
    c n = c k ∧ lo n = lo k ∧ hi n = hi k := by
  induction n, hkn using Nat.le_induction with
  | base => exact ⟨rfl, rfl, rfl⟩
  | succ n _ ih =>
    obtain ⟨h1, h2, h3⟩ := h.exit n (ih.1 ▸ hk)
    exact ⟨h3.trans ih.1, h1.trans ih.2.1, h2.trans ih.2.2⟩

/-- One step of a run: $l_k \le l_{k+1} \le \max(l_k, a)$, $u_{k+1} \le u_k$, and $b \le u_k$
implies $b \le u_{k+1}$. -/
theorem step_bounds (k : ℕ) :
    lo k ≤ lo (k + 1) ∧ lo (k + 1) ≤ max (lo k) a ∧ hi (k + 1) ≤ hi k ∧
      (b ≤ hi k → b ≤ hi (k + 1)) := by
  rcases le_or_gt (c k) a with hca | hca
  · obtain ⟨hhi, hlo, -⟩ := h.left k hca
    refine ⟨(le_max_left _ _).trans hlo.le, hlo.le_max.trans ?_, hhi.le, fun hb => hhi ▸ hb⟩
    exact max_le (max_le (le_max_left _ _) (hca.trans (le_max_right _ _))) (le_max_right _ _)
  rcases le_or_gt (c k) b with hcb | hcb
  · obtain ⟨hlo, hhi, -⟩ := h.exit k ⟨hca, hcb⟩
    exact ⟨hlo.ge, hlo ▸ le_max_left _ _, hhi.le, fun hb => hhi ▸ hb⟩
  · obtain ⟨hhi, hlo, -⟩ := h.right k hcb
    exact ⟨hlo.le, hlo.le_max, hhi ▸ min_le_left _ _,
      fun hb => hhi ▸ le_min hb hcb.le⟩

/-- The lower ends of a run increase. -/
theorem monotone_lo : Monotone lo :=
  monotone_nat_of_le_succ fun k => (h.step_bounds k).1

/-- The upper ends of a run decrease. -/
theorem antitone_hi : Antitone hi :=
  antitone_nat_of_succ_le fun k => (h.step_bounds k).2.2.1

/-- The upper ends of a run stay at least $b$. -/
theorem le_hi (k : ℕ) : b ≤ hi k := by
  induction k with
  | zero => exact h.le_hi_zero
  | succ k ih => exact (h.step_bounds k).2.2.2 ih

/-- The lower ends of a run stay at most $\max(l_0, a)$. -/
theorem lo_le_max (k : ℕ) : lo k ≤ max (lo 0) a := by
  induction k with
  | zero => exact le_max_left _ _
  | succ k ih =>
    exact (h.step_bounds k).2.1.trans (max_le ih (le_max_right _ _))

/-- If $a \le b$, the lower ends of a run stay at most $b$. -/
theorem lo_le (hab : a ≤ b) (k : ℕ) : lo k ≤ b :=
  (h.lo_le_max k).trans (max_le h.lo_zero_le hab)

/-- The lower ends of a run stay nonnegative. -/
theorem lo_nonneg (k : ℕ) : 0 ≤ lo k :=
  h.nonneg.trans (h.monotone_lo (Nat.zero_le k))

/-- Let $a \le b$. If the trial value $c_{k+1}$ of a run does not lie in $(a, b]$, then the step
from $k$ did not stop the run, so $c_{k+1}$ comes from one of the two update formulas. Hence,
with $l = l_{k+1}$ and $u = u_{k+1}$,
$$l + \theta_L (u - l) \le c_{k+1} \le \max\bigl(\sqrt{lu}, \; l + \theta_U (u - l)\bigr).$$
-/
theorem estimate_bounds (hab : a ≤ b) {k : ℕ} (hk : c (k + 1) ∉ Ioc a b) :
    lo (k + 1) + θL * (hi (k + 1) - lo (k + 1)) ≤ c (k + 1) ∧
      c (k + 1) ≤ max √(lo (k + 1) * hi (k + 1)) (lo (k + 1) + θU * (hi (k + 1) - lo (k + 1))) := by
  have hw : 0 ≤ hi (k + 1) - lo (k + 1) :=
    sub_nonneg.2 ((h.lo_le hab _).trans (h.le_hi _))
  rcases le_or_gt (c k) a with hca | hca
  · obtain ⟨-, -, θ, hθ, γ, hγ, hc⟩ := h.left k hca
    rw [hc]
    exact ⟨le_trans (by nlinarith [hθ.1]) (le_bracketEstimate _ _ _ _),
      (bracketEstimate_le_max_sqrt hγ).trans (max_le_max le_rfl (by nlinarith [hθ.2]))⟩
  rcases le_or_gt (c k) b with hcb | hcb
  · exact absurd ((h.exit k ⟨hca, hcb⟩).2.2 ▸ ⟨hca, hcb⟩) hk
  · obtain ⟨-, -, θl, hθl, θu, hθu, -, γ₁, -, γ₂, hγ₂, -, hc⟩ := h.right k hcb
    exact ⟨le_trans (by nlinarith [hθl.1]) ((le_bracketEstimate _ _ _ _).trans hc.1),
      hc.2.trans ((bracketEstimate_le_max_sqrt hγ₂).trans
        (max_le_max le_rfl (by nlinarith [hθu.2])))⟩

/-- **Invariants of a run.** Let $a \le b$, $0 \le \theta_L$ and $\theta_U \le 1$. Then for every
run:

* $l_k \le b \le u_k$ for all $k$;
* the lower ends increase and the upper ends decrease;
* $l_k \le \max(l_0, a)$ for all $k$;
* for all $k$, if $c_{k+1} \notin (a, b]$, then $c_{k+1} \in [l_{k+1}, u_{k+1}]$. -/
theorem invariant (hab : a ≤ b) (hθL : 0 ≤ θL) (hθU : θU ≤ 1) :
    (∀ k, lo k ≤ b ∧ b ≤ hi k) ∧ Monotone lo ∧ Antitone hi ∧ (∀ k, lo k ≤ max (lo 0) a) ∧
      ∀ k, c (k + 1) ∉ Ioc a b → c (k + 1) ∈ Icc (lo (k + 1)) (hi (k + 1)) := by
  refine ⟨fun k => ⟨h.lo_le hab k, h.le_hi k⟩, h.monotone_lo, h.antitone_hi,
    h.lo_le_max, fun k hk => ?_⟩
  obtain ⟨h1, h2⟩ := h.estimate_bounds hab hk
  have hl := h.lo_nonneg (k + 1)
  have hlu := (h.lo_le hab (k + 1)).trans (h.le_hi (k + 1))
  have hw : 0 ≤ hi (k + 1) - lo (k + 1) := sub_nonneg.2 hlu
  exact ⟨le_trans (by nlinarith) h1, h2.trans (max_le (sqrt_mul_le_right hl hlu) (by nlinarith))⟩

/-- Let $a \le b$ and $\rho = \max(1 - \theta_L, \theta_U, 1/2)$. If the trial value $c_{k+1}$ of a
run does not lie in $(a, b]$, then
$$u_{k+2} - l_{k+2} \le \rho \, (u_{k+1} - l_{k+1}).$$
This is `Subproblem.IsBracketRun.width_le` with the index shifted by one. -/
theorem width_le_aux (hab : a ≤ b) {k : ℕ} (hk : c (k + 1) ∉ Ioc a b) :
    hi (k + 2) - lo (k + 2) ≤ max (1 - θL) (max θU (1 / 2)) * (hi (k + 1) - lo (k + 1)) := by
  obtain ⟨h1, h2⟩ := h.estimate_bounds hab hk
  have hl := h.lo_nonneg (k + 1)
  have hlu := (h.lo_le hab (k + 1)).trans (h.le_hi (k + 1))
  have hw : 0 ≤ hi (k + 1) - lo (k + 1) := sub_nonneg.2 hlu
  set ρ := max (1 - θL) (max θU (1 / 2))
  have hρ1 : (1 - θL) * (hi (k + 1) - lo (k + 1)) ≤ ρ * (hi (k + 1) - lo (k + 1)) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hw
  have hρ2 : θU * (hi (k + 1) - lo (k + 1)) ≤ ρ * (hi (k + 1) - lo (k + 1)) :=
    mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_right _ _)) hw
  have hρ3 : (hi (k + 1) - lo (k + 1)) / 2 ≤ ρ * (hi (k + 1) - lo (k + 1)) := by
    rw [div_eq_mul_one_div, mul_comm]
    exact mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_max_right _ _)) hw
  rcases le_or_gt (c (k + 1)) a with hca | hca
  · -- the lower end moves up to at least `c (k+1)`
    obtain ⟨hhi, hlo, -⟩ := h.left (k + 1) hca
    have : c (k + 1) ≤ lo (k + 2) := (le_max_right _ _).trans hlo.le
    rw [hhi]
    nlinarith
  · have hcb : b < c (k + 1) := by
      by_contra hcb
      exact hk ⟨hca, not_lt.1 hcb⟩
    -- the upper end moves down to at most `c (k+1)`
    obtain ⟨hhi, hlo, -⟩ := h.right (k + 1) hcb
    have hhi' : hi (k + 2) ≤ c (k + 1) := hhi ▸ min_le_right _ _
    have hlo' := hlo.le
    rcases le_max_iff.1 h2 with h2 | h2
    · have := sqrt_mul_sub_le hl hlu
      linarith
    · linarith

/-- **Width contraction.** Let $a \le b$ and $\rho = \max(1 - \theta_L, \theta_U, 1/2)$. For every
step $k \ge 1$ of a run with $c_k \notin (a, b]$,
$$u_{k+1} - l_{k+1} \le \rho \, (u_k - l_k).$$

The step $k = 0$ is excluded because the initial trial value $c_0$ is arbitrary and need not lie
in the bracket. -/
theorem width_le (hab : a ≤ b) {k : ℕ} (hk1 : 1 ≤ k) (hk : c k ∉ Ioc a b) :
    hi (k + 1) - lo (k + 1) ≤ max (1 - θL) (max θU (1 / 2)) * (hi k - lo k) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hk1
  exact h.width_le_aux hab hk

/-- **Finite termination.** Let $a < b$, $l_0 < b$ and $0 < \theta_L$, $\theta_U < 1$, and let
$\rho = \max(1 - \theta_L, \theta_U, 1/2)$. Then a run has a trial value $c_k \in (a, b]$ with
$$k \le \left\lceil \frac{\log\bigl((u_1 - l_1) / (b - \max(l_0, a))\bigr)}{\log(1 / \rho)}
  \right\rceil + 1.$$

The ceiling is `Nat.ceil`, which is $0$ for a negative argument. While the run has not stopped,
the bracket keeps a width of at least $b - \max(l_0, a) > 0$ and shrinks by the factor $\rho$ at
each step. -/
theorem exists_mem (hab : a < b) (hlo : lo 0 < b) (hθL : 0 < θL) (hθU : θU < 1) :
    ∃ k ≤ ⌈Real.log ((hi 1 - lo 1) / (b - max (lo 0) a)) /
        Real.log (1 / max (1 - θL) (max θU (1 / 2)))⌉₊ + 1, c k ∈ Ioc a b := by
  set ρ := max (1 - θL) (max θU (1 / 2)) with hρ
  set δ := b - max (lo 0) a with hδ
  set W := hi 1 - lo 1 with hW
  set N := ⌈Real.log (W / δ) / Real.log (1 / ρ)⌉₊ with hN
  have hρpos : 0 < ρ := lt_of_lt_of_le (by norm_num) ((le_max_right _ _).trans (le_max_right _ _))
  have hρ1 : ρ < 1 := max_lt (by linarith) (max_lt hθU (by norm_num))
  have hδpos : 0 < δ := sub_pos.2 (max_lt hlo hab)
  have hwidth : ∀ k, δ ≤ hi k - lo k := fun k => by
    have := h.lo_le_max k
    have := h.le_hi k
    linarith
  have hWpos : 0 < W := hδpos.trans_le (hwidth 1)
  by_contra hcon
  push Not at hcon
  -- the widths decay geometrically while the run has not stopped
  have hdecay : ∀ n ≤ N + 1, hi (n + 1) - lo (n + 1) ≤ ρ ^ n * W := by
    intro n hn
    induction n with
    | zero => simp [hW]
    | succ n ih =>
      have := h.width_le hab.le (Nat.le_add_left 1 n) (hcon (n + 1) hn)
      calc hi (n + 1 + 1) - lo (n + 1 + 1) ≤ ρ * (hi (n + 1) - lo (n + 1)) := this
        _ ≤ ρ * (ρ ^ n * W) := mul_le_mul_of_nonneg_left (ih (by omega)) hρpos.le
        _ = ρ ^ (n + 1) * W := by ring
  -- `ρ ^ N ≤ δ / W` by the choice of `N`
  have hlogρ : 0 < Real.log (1 / ρ) := Real.log_pos ((one_lt_div hρpos).2 hρ1)
  have hpowN : ρ ^ N ≤ δ / W := by
    have hceil : Real.log (W / δ) ≤ N * Real.log (1 / ρ) :=
      (div_le_iff₀ hlogρ).1 (Nat.le_ceil _)
    rw [← Real.log_le_log_iff (pow_pos hρpos N) (div_pos hδpos hWpos), Real.log_pow,
      Real.log_div hδpos.ne' hWpos.ne']
    rw [Real.log_div hWpos.ne' hδpos.ne', one_div, Real.log_inv] at hceil
    linarith
  have h1 := hdecay (N + 1) le_rfl
  have h2 := hwidth (N + 1 + 1)
  have : ρ ^ (N + 1) * W ≤ ρ * δ := by
    rw [pow_succ, mul_comm (ρ ^ N) ρ, mul_assoc]
    exact mul_le_mul_of_nonneg_left ((le_div_iff₀ hWpos).1 hpowN) hρpos.le
  nlinarith

/-- Let $a \le b$, $0 < \theta_L$ and $\theta_U < 1$. If no trial value of a run lies in $(a, b]$,
then the lower ends, the upper ends and the trial values all converge to $b$.

The widths of the brackets decay geometrically, with the factor $\rho$ of
`Subproblem.IsBracketRun.width_le`. -/
theorem tendsto_bracket_of_never_mem (hab : a ≤ b) (hθL : 0 < θL) (hθU : θU < 1)
    (hnever : ∀ k, c k ∉ Ioc a b) :
    Tendsto lo atTop (𝓝 b) ∧ Tendsto hi atTop (𝓝 b) ∧ Tendsto c atTop (𝓝 b) := by
  let ρ := max (1 - θL) (max θU (1 / 2))
  have hρ0 : 0 ≤ ρ := by
    exact (by norm_num : (0 : ℝ) ≤ 1 / 2).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hρ1 : ρ < 1 := max_lt (by linarith) (max_lt hθU (by norm_num))
  have hdecay (n : ℕ) : hi (n + 1) - lo (n + 1) ≤ ρ ^ n * (hi 1 - lo 1) := by
    induction n with
    | zero => simp
    | succ n ih =>
      calc
        _ ≤ ρ * (hi (n + 1) - lo (n + 1)) :=
          h.width_le hab (Nat.le_add_left 1 n) (hnever (n + 1))
        _ ≤ ρ * (ρ ^ n * (hi 1 - lo 1)) := mul_le_mul_of_nonneg_left ih hρ0
        _ = _ := by rw [pow_succ']; ring
  have htend (f : ℕ → ℝ)
      (hf : ∀ n, f (n + 1) ∈ Icc (lo (n + 1)) (hi (n + 1))) : Tendsto f atTop (𝓝 b) := by
    have hnorm (n : ℕ) : ‖f (n + 1) - b‖ ≤ hi (n + 1) - lo (n + 1) := by
      obtain ⟨hl, hu⟩ := hf n
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith [h.lo_le hab (n + 1), h.le_hi (n + 1)]
    apply (tendsto_add_atTop_iff_nat 1).mp
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => (hnorm n).trans (hdecay n)) ?_
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).mul_const (hi 1 - lo 1)
  have hlu (n : ℕ) : lo n ≤ hi n := (h.lo_le hab n).trans (h.le_hi n)
  exact ⟨htend lo fun n => ⟨le_rfl, hlu _⟩, htend hi fun n => ⟨hlu _, le_rfl⟩,
    htend c fun n => (h.invariant hab hθL.le hθU.le).2.2.2.2 n (hnever (n + 1))⟩

/-- Let $a = b$, so that the set $(a, b]$ of the stopping trial values is empty, and let $u_0 > b$,
$0 < \theta_L$ and $\theta_U < 1$. Then for every run there are infinitely many $k$ with
$c_k > b$. -/
theorem frequently_gt_of_eq (hab : a = b) (hhi : b < hi 0)
    (hθL : 0 < θL) (hθU : θU < 1) : ∃ᶠ k in atTop, b < c k := by
  subst b
  have hhi' (n : ℕ) : a < hi n := by
    induction n with
    | zero => exact hhi
    | succ n ih =>
      rcases le_or_gt (c n) a with hn | hn
      · rwa [(h.left n hn).1]
      · rw [(h.right n hn).1]
        exact lt_min ih hn
  by_contra hnot
  have he : ∀ᶠ k in atTop, c k ≤ a := by simpa only [Filter.Frequently, not_not, not_lt] using hnot
  obtain ⟨N, hN⟩ := eventually_atTop.mp he
  have hconst (n : ℕ) : hi (n + N) = hi N := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [show n + 1 + N = (n + N) + 1 by omega,
        (h.left (n + N) (hN _ (Nat.le_add_left _ _))).1, ih]
  have ht := (h.tendsto_bracket_of_never_mem le_rfl hθL hθU (fun n => by simp)).2.1
  have ht' := (tendsto_add_atTop_iff_nat N).mpr ht
  have htconst : Tendsto (fun n => hi (n + N)) atTop (𝓝 (hi N)) :=
    tendsto_const_nhds.congr fun n => (hconst n).symm
  exact (hhi' N).ne' (tendsto_nhds_unique htconst ht')

end IsBracketRun

end Subproblem
