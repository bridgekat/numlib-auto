/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Optimization.Subproblem.Bracketing
import NumlibSurface.CartisGouldToint.Chapter08.Section03

/-!
# Cartis, Gould and Toint, Section 9.2: Finding a point in $\mathcal{L}$

This module formalizes Section 9.2 of [cartis2022evaluation]. Algorithm 9.2.1 reduces a bracket
$[\lambda^L, \lambda^U]$ that contains the multiplier $\lambda^*$, by safeguarded trial values
$\lambda^C$, until a trial value lies in the set $\mathcal{L}$ of Section 8.3. A run only tests in
which of the sets $\mathcal{N}$, $\mathcal{L}$, $\mathcal{G}$ the trial values lie, so it is stated
for arbitrary sets. For the subproblems of Chapter 8 these sets are $(-\infty, \lambda_s]$,
$(\lambda_s, \lambda^*]$ and $(\lambda^*, \infty)$ (`CartisGouldToint.Chapter08.setL_reg_eq_Ioc`,
`CartisGouldToint.Chapter08.setL_tr_eq_Ioc`).

For such a partition, the brackets contain $\lambda^*$ and shrink, each step after the first
multiplies the bracket width by at most $\rho = \max(1 - \theta_L, \theta_U, 1/2) < 1$, and a trial
value in $\mathcal{L}$ is found after a number of steps logarithmic in the initial bracket width.
Under the partition, a run is a run of the backbone predicate `Subproblem.IsBracketRun` of
`Numlib.Optimization.Subproblem.Bracketing`, which carries the analysis.

## Main definitions

* Algorithm 9.2.1, `CartisGouldToint.Chapter09.algorithm_9_2_1`: a run of the safeguarded bracketing
  method for given sets $\mathcal{N}$, $\mathcal{L}$, $\mathcal{G}$.

## Main results

* Algorithm 9.2.1, `CartisGouldToint.Chapter09.algorithm_9_2_1.isBracketRun`: for an interval
  partition, a run is a run of `Subproblem.IsBracketRun`.
* Algorithm 9.2.1, `CartisGouldToint.Chapter09.algorithm_9_2_1_exists`: runs exist for any
  admissible initial data.
* Algorithm 9.2.1, `CartisGouldToint.Chapter09.algorithm_9_2_1_terminates`: the brackets contain
  $\lambda^*$ and contract, and a trial value in $\mathcal{L}$ is found in finitely many steps.
* Algorithm 9.2.1, `CartisGouldToint.Chapter09.algorithm_9_2_1_terminates_reg`: the same for the
  regularization subproblem (8.1.3).
* Algorithm 9.2.1, `CartisGouldToint.Chapter09.algorithm_9_2_1_terminates_tr`: the same for the
  trust-region subproblem (8.1.2).

## Deviations from the source

* **Algorithm 9.2.1, initial trial** (generalization). The initial trial can lie outside the
  initial bracket. The contraction estimate starts with the first safeguarded trial.
  See `CartisGouldToint.Chapter09.algorithm_9_2_1` and
  `CartisGouldToint.Chapter09.algorithm_9_2_1_terminates`.
* **Algorithm 9.2.1, contraction factor** (correction). The bound $\max(1 - \theta, \theta, \gamma
  \sqrt{\lambda^U}/(\sqrt{\lambda^L} + \sqrt{\lambda^U}))$ of the source is not uniformly below $1$;
  the uniform factor $\max(1 - \theta_L, \theta_U, 1/2)$ is used. See
  `CartisGouldToint.Chapter09.algorithm_9_2_1_terminates`.
* **Algorithm 9.2.1, finite termination** (correction). Termination needs the initial lower bound
  strictly below $\lambda^*$. See `CartisGouldToint.Chapter09.algorithm_9_2_1_terminates`.
-/

open Set

namespace CartisGouldToint.Chapter09

open Subproblem

/-- **Algorithm 9.2.1** of [cartis2022evaluation], a run. The algorithm finds a point of
$\mathcal{L}$. Let $\mathcal{N}, \mathcal{L}, \mathcal{G} \subseteq \mathbb{R}$ be the sets of a
subproblem, $\lambda^*$ its multiplier, $\lambda_1$ the leftmost eigenvalue of the pencil, and
$\theta_L, \theta_U \in \mathbb{R}$. Sequences of lower bounds $\lambda^L_k$, upper bounds
$\lambda^U_k$ and trial values $\lambda^C_k$ form a **run of Algorithm 9.2.1** if
$0 < \theta_L \le \theta_U < 1$, $0 \le \lambda^L_0 \le \lambda^* \le \lambda^U_0$ (9.2.1), and
at every step $k$:

* if $\lambda^C_k \in \mathcal{L}$, the run has stopped: the bounds and the trial value do not
  change;
* if $\lambda^C_k \in \mathcal{N}$, the upper bound does not change, the lower bound becomes
  $\max(\lambda^L_k, \lambda^C_k)$, possibly raised further to $\max(\cdot, -\lambda_E)$ for an
  estimate $\lambda_E \ge \lambda_1$, and $\lambda^C_{k+1} = \max\bigl(\gamma
  \sqrt{\lambda^L_{k+1} \lambda^U_{k+1}}, \lambda^L_{k+1} + \theta (\lambda^U_{k+1} -
  \lambda^L_{k+1})\bigr)$ for some $\theta \in [\theta_L, \theta_U]$ and $\gamma \in \{0, 1\}$;
* if $\lambda^C_k \in \mathcal{G}$, the upper bound becomes $\min(\lambda^U_k, \lambda^C_k)$,
  the lower bound is possibly raised to $\max(\lambda^L_k, -\lambda_E)$, and $\lambda^C_{k+1}$
  lies in the interval (9.2.2) between the two values of this formula for some
  $\theta_l \le \theta_u$ in $[\theta_L, \theta_U]$ and $\gamma_1 \le \gamma_2$ in $\{0, 1\}$.

The formula for the trial value is `Subproblem.bracketEstimate`. The optional raise by
$-\lambda_E$ with $\lambda_E \ge \lambda_1$ is `Subproblem.IsLowerUpdate (-λ₁)`.

**Generalization.** The surrounding prose starts with a trial already in the current bracket.
The run allows any initial trial because the updates keep $\lambda^*$ in the bracket and put
the next trial inside it. The termination results use the stated interval partition. -/
structure algorithm_9_2_1 (setN setL setG : Set ℝ) (lam₁ lamStar θL θU : ℝ)
    (lo hi c : ℕ → ℝ) : Prop where
  /-- The constants satisfy $0 < \theta_L \le \theta_U < 1$. -/
  theta : 0 < θL ∧ θL ≤ θU ∧ θU < 1
  /-- The initial lower bound is nonnegative: $\lambda^L_0 \ge 0$. -/
  nonneg : 0 ≤ lo 0
  /-- The initial lower bound satisfies $\lambda^L_0 \le \lambda^*$ (9.2.1). -/
  lo_zero_le : lo 0 ≤ lamStar
  /-- The initial upper bound satisfies $\lambda^* \le \lambda^U_0$ (9.2.1). -/
  le_hi_zero : lamStar ≤ hi 0
  /-- If $\lambda^C_k \in \mathcal{L}$, then the bounds and the trial value do not change at step
  $k$. -/
  exit : ∀ k, c k ∈ setL → lo (k + 1) = lo k ∧ hi (k + 1) = hi k ∧ c (k + 1) = c k
  /-- If $\lambda^C_k \in \mathcal{N}$, then the upper bound does not change, the lower bound is
  raised to at least $\max(\lambda^L_k, \lambda^C_k)$, and the next trial value is the
  safeguarded estimate for some $\theta \in [\theta_L, \theta_U]$ and $\gamma \in \{0, 1\}$. -/
  left : ∀ k, c k ∈ setN → hi (k + 1) = hi k ∧
    IsLowerUpdate (-lam₁) (max (lo k) (c k)) (lo (k + 1)) ∧
    ∃ θ ∈ Icc θL θU, ∃ γ ∈ ({0, 1} : Set ℝ),
      c (k + 1) = bracketEstimate γ θ (lo (k + 1)) (hi (k + 1))
  /-- If $\lambda^C_k \in \mathcal{G}$, then the upper bound becomes
  $\min(\lambda^U_k, \lambda^C_k)$, the lower bound is possibly raised, and the next trial value
  lies in the interval (9.2.2). -/
  right : ∀ k, c k ∈ setG → hi (k + 1) = min (hi k) (c k) ∧
    IsLowerUpdate (-lam₁) (lo k) (lo (k + 1)) ∧
    ∃ θl ∈ Icc θL θU, ∃ θu ∈ Icc θL θU, θl ≤ θu ∧ ∃ γ₁ ∈ ({0, 1} : Set ℝ),
      ∃ γ₂ ∈ ({0, 1} : Set ℝ), γ₁ ≤ γ₂ ∧
        c (k + 1) ∈ Icc (bracketEstimate γ₁ θl (lo (k + 1)) (hi (k + 1)))
          (bracketEstimate γ₂ θu (lo (k + 1)) (hi (k + 1)))

variable {setN setL setG : Set ℝ} {lam₁ lamStar θL θU : ℝ} {lo hi c : ℕ → ℝ}

/-- **Algorithm 9.2.1** of [cartis2022evaluation], reduction to the backbone. Let $a \in \mathbb{R}$
with $-\lambda_1 \le a$, as for $a = \lambda_s = \max(0, -\lambda_1)$, and let
$\mathcal{N} = (-\infty, a]$, $\mathcal{L} = (a, \lambda^*]$ and
$\mathcal{G} = (\lambda^*, \infty)$. Then every run of Algorithm 9.2.1 for these sets is a run
of `Subproblem.IsBracketRun` for $a$ and $\lambda^*$. -/
theorem algorithm_9_2_1.isBracketRun {a : ℝ}
    (h : algorithm_9_2_1 setN setL setG lam₁ lamStar θL θU lo hi c) (hN : setN = Iic a)
    (hL : setL = Ioc a lamStar) (hG : setG = Ioi lamStar) (ha : -lam₁ ≤ a) :
    IsBracketRun a lamStar θL θU lo hi c := by
  subst hN hL hG
  refine ⟨h.nonneg, h.lo_zero_le, h.le_hi_zero, h.exit, fun k hk => ?_, fun k hk => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := h.left k hk
    exact ⟨h1, h2.mono ha, h3⟩
  · obtain ⟨h1, h2, h3⟩ := h.right k hk
    exact ⟨h1, h2.mono ha, h3⟩

/-- The deterministic step of Algorithm 9.2.1 on states $(\lambda^L, \lambda^U, \lambda^C)$, with
$\theta = \theta_L$, $\gamma = 0$ and no eigenvalue estimates. -/
private noncomputable def bracketStepCanonical (a b θ : ℝ) (s : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  if a < s.2.2 ∧ s.2.2 ≤ b then s
  else if s.2.2 ≤ a then (max s.1 s.2.2, s.2.1, bracketEstimate 0 θ (max s.1 s.2.2) s.2.1)
  else (s.1, min s.2.1 s.2.2, bracketEstimate 0 θ s.1 (min s.2.1 s.2.2))

/-- **Algorithm 9.2.1** of [cartis2022evaluation], existence of runs. Let $a \le \lambda^*$, let
$\mathcal{N} = (-\infty, a]$, $\mathcal{L} = (a, \lambda^*]$ and
$\mathcal{G} = (\lambda^*, \infty)$, and let $0 < \theta_L \le \theta_U < 1$. For any initial
bounds with $0 \le \lambda^L_0 \le \lambda^* \le \lambda^U_0$ (9.2.1) and any initial trial
value $\lambda^C_0$, there is a run of Algorithm 9.2.1 with these initial values.

The run in the proof takes $\theta = \theta_L$, $\gamma = 0$ and no eigenvalue estimates. The
eigenvalue $\lambda_1$ is arbitrary here. The initial trial is allowed outside the bracket
(`CartisGouldToint.Chapter09.algorithm_9_2_1`).

**Reading.** Constructs a run for all admissible bounds, including trials outside the initial
bracket.
-/
theorem algorithm_9_2_1_exists {a lo₀ hi₀ c₀ : ℝ} (hN : setN = Iic a)
    (hL : setL = Ioc a lamStar) (hG : setG = Ioi lamStar) (hab : a ≤ lamStar)
    (hθ : 0 < θL ∧ θL ≤ θU ∧ θU < 1) (h0 : 0 ≤ lo₀) (hlo : lo₀ ≤ lamStar)
    (hhi : lamStar ≤ hi₀) :
    ∃ lo hi c : ℕ → ℝ, algorithm_9_2_1 setN setL setG lam₁ lamStar θL θU lo hi c ∧
      lo 0 = lo₀ ∧ hi 0 = hi₀ ∧ c 0 = c₀ := by
  subst hN hL hG
  set s : ℕ → ℝ × ℝ × ℝ := fun k => (bracketStepCanonical a lamStar θL)^[k] (lo₀, hi₀, c₀)
    with hs
  have hsucc : ∀ k, s (k + 1) = bracketStepCanonical a lamStar θL (s k) := fun k => by
    simp only [hs, Function.iterate_succ_apply']
  have hθmem : θL ∈ Icc θL θU := ⟨le_rfl, hθ.2.1⟩
  have h0mem : (0 : ℝ) ∈ ({0, 1} : Set ℝ) := Or.inl rfl
  refine ⟨fun k => (s k).1, fun k => (s k).2.1, fun k => (s k).2.2,
    ⟨hθ, h0, hlo, hhi, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_⟩, rfl, rfl, rfl⟩
  · rw [hsucc, bracketStepCanonical,
      ite_eq_left (show a < (s k).2.2 ∧ (s k).2.2 ≤ lamStar from hk)]
    exact ⟨rfl, rfl, rfl⟩
  · have hn : ¬ (a < (s k).2.2 ∧ (s k).2.2 ≤ lamStar) := fun h => absurd hk (not_le.2 h.1)
    rw [hsucc, bracketStepCanonical, ite_eq_right hn, ite_eq_left (show (s k).2.2 ≤ a from hk)]
    exact ⟨rfl, Or.inl rfl, θL, hθmem, 0, h0mem, rfl⟩
  · have hk' : lamStar < (s k).2.2 := hk
    have hn : ¬ (a < (s k).2.2 ∧ (s k).2.2 ≤ lamStar) := fun h => absurd hk' (not_lt.2 h.2)
    have hn' : ¬ (s k).2.2 ≤ a := fun h => absurd (h.trans hab) (not_le.2 hk')
    rw [hsucc, bracketStepCanonical, ite_eq_right hn, ite_eq_right hn']
    exact ⟨rfl, Or.inl rfl, θL, hθmem, θL, hθmem, le_rfl, 0, h0mem, 0, h0mem, le_rfl,
      le_rfl, le_rfl⟩

/-- **Algorithm 9.2.1** of [cartis2022evaluation], convergence and termination. Let
$a \in \mathbb{R}$ with $-\lambda_1 \le a \le \lambda^*$, and let $\mathcal{N} = (-\infty, a]$,
$\mathcal{L} = (a, \lambda^*]$ and $\mathcal{G} = (\lambda^*, \infty)$. Let
$(\lambda^L_k, \lambda^U_k, \lambda^C_k)$ be a run of Algorithm 9.2.1, and let
$\rho = \max(1 - \theta_L, \theta_U, 1/2)$. Then:

* $\lambda^L_k \le \lambda^* \le \lambda^U_k$ for all $k$, the lower bounds increase and the
  upper bounds decrease;
* $\rho < 1$, and for every $k \ge 1$ with $\lambda^C_k \notin \mathcal{L}$,
$$\lambda^U_{k+1} - \lambda^L_{k+1} \le \rho \, (\lambda^U_k - \lambda^L_k);$$
* if $a < \lambda^*$ (so $\mathcal{L}$ is nonempty) and $\lambda^L_0 < \lambda^*$, then
  $\lambda^C_k \in \mathcal{L}$ for some
$$k \le \left\lceil \frac{\log\bigl((\lambda^U_1 - \lambda^L_1)/(\lambda^* - \max(\lambda^L_0,
  a))\bigr)}{\log(1/\rho)} \right\rceil_+ + 1.$$

**Correction.** The source bounds the ratio of successive bracket widths by $\max(1 - \theta,
\theta, \gamma \sqrt{\lambda^U}/(\sqrt{\lambda^L} + \sqrt{\lambda^U}))$. This bound is valid but
not uniformly below $1$, so the uniform factor $\rho$ is used. The contraction estimate begins
at $k=1$, after the safeguard has selected a trial. The initial trial could be a bracket endpoint
that leaves the bracket unchanged, and a run freezes its bracket when it reaches $\mathcal{L}$.

**Correction.** Finite termination needs the hypothesis $\lambda^L_0 < \lambda^*$. If
$\lambda^L_0 = \lambda^*$, a run need not stop: while $\lambda^U_k > \lambda^*$, every trial
value exceeds $\lambda^*$ and lies in $\mathcal{G}$.

Here $\lceil x \rceil_+$ is `Nat.ceil`, which is $0$ for $x \le 0$. The proof specializes the
analysis of `Subproblem.IsBracketRun`. -/
theorem algorithm_9_2_1_terminates {a : ℝ}
    (h : algorithm_9_2_1 setN setL setG lam₁ lamStar θL θU lo hi c) (hN : setN = Iic a)
    (hL : setL = Ioc a lamStar) (hG : setG = Ioi lamStar) (ha : -lam₁ ≤ a)
    (hab : a ≤ lamStar) :
    (∀ k, lo k ≤ lamStar ∧ lamStar ≤ hi k) ∧ Monotone lo ∧ Antitone hi ∧
    max (1 - θL) (max θU (1 / 2)) < 1 ∧
    (∀ k, 1 ≤ k → c k ∉ setL →
      hi (k + 1) - lo (k + 1) ≤ max (1 - θL) (max θU (1 / 2)) * (hi k - lo k)) ∧
    (a < lamStar → lo 0 < lamStar →
      ∃ k ≤ ⌈Real.log ((hi 1 - lo 1) / (lamStar - max (lo 0) a)) /
        Real.log (1 / max (1 - θL) (max θU (1 / 2)))⌉₊ + 1, c k ∈ setL) := by
  have hb := h.isBracketRun hN hL hG ha
  obtain ⟨hθ0, -, hθ1⟩ := h.theta
  obtain ⟨hinv, hlo, hhi, -, -⟩ := hb.invariant hab hθ0.le hθ1.le
  refine ⟨hinv, hlo, hhi, ?_, fun k hk hc => hb.width_le hab hk (hL ▸ hc), fun hlt hlo0 => ?_⟩
  · exact max_lt (by linarith) (max_lt hθ1 (by norm_num))
  · rw [hL]; exact hb.exists_mem hlt hlo0 hθ0 hθ1

/-! ### The subproblems of Chapter 8 -/

open CartisGouldToint.Chapter08

variable {n : ℕ} {g : EuclideanSpace ℝ (Fin n)} {H M : Matrix (Fin n) (Fin n) ℝ}

/-- **Algorithm 9.2.1** of [cartis2022evaluation] for the regularization subproblem (8.1.3). Let $H$
be symmetric, $M$ symmetric positive definite, $\sigma > 0$ and $r > 2$. Let $s^*$ be a global
minimizer of (8.1.3), and let $\lambda^* = \sigma \|s^*\|_M^{r-2}$. Let
$(\lambda^L_k, \lambda^U_k, \lambda^C_k)$ be a run of Algorithm 9.2.1 for the sets
$\mathcal{N}$, $\mathcal{L}$, $\mathcal{G}$ of Section 8.3.1 and the leftmost eigenvalue
$\lambda_1$ of the pencil $(H, M)$. Then the conclusions of
`CartisGouldToint.Chapter09.algorithm_9_2_1_terminates` hold with $a = \lambda_s$: the brackets
contain $\lambda^*$ and are monotone, the width contracts by
$\rho = \max(1 - \theta_L, \theta_U, 1/2) < 1$ at each step $k \ge 1$ that has not stopped, and
if $\lambda_s < \lambda^*$ and $\lambda^L_0 < \lambda^*$, some $\lambda^C_k$ with
$$k \le \left\lceil \frac{\log\bigl((\lambda^U_1 - \lambda^L_1)/(\lambda^* - \max(\lambda^L_0,
  \lambda_s))\bigr)}{\log(1/\rho)} \right\rceil_+ + 1$$
lies in $\mathcal{L}$.

**Correction.** Retains the corrected contraction and the strict lower-bound condition with
regularization regions.
-/
theorem algorithm_9_2_1_terminates_reg (hH : H.IsHermitian) (hM : M.PosDef) {σ r : ℝ}
    (hσ : 0 < σ) (hr : 2 < r) {s : EuclideanSpace ℝ (Fin n)}
    (hs : IsRegularizationSolution g H M σ r s)
    (h : algorithm_9_2_1 (Chapter08.setN hH hM) (setL_reg hH hM g σ r) (setG_reg hH hM g σ r)
      (leftmostPencil hH hM) (σ * mNorm M s ^ (r - 2)) θL θU lo hi c) :
    (∀ k, lo k ≤ σ * mNorm M s ^ (r - 2) ∧ σ * mNorm M s ^ (r - 2) ≤ hi k) ∧ Monotone lo ∧
    Antitone hi ∧ max (1 - θL) (max θU (1 / 2)) < 1 ∧
    (∀ k, 1 ≤ k → c k ∉ setL_reg hH hM g σ r →
      hi (k + 1) - lo (k + 1) ≤ max (1 - θL) (max θU (1 / 2)) * (hi k - lo k)) ∧
    (lambdaS hH hM < σ * mNorm M s ^ (r - 2) → lo 0 < σ * mNorm M s ^ (r - 2) →
      ∃ k ≤ ⌈Real.log ((hi 1 - lo 1) / (σ * mNorm M s ^ (r - 2) - max (lo 0) (lambdaS hH hM))) /
        Real.log (1 / max (1 - θL) (max θU (1 / 2)))⌉₊ + 1, c k ∈ setL_reg hH hM g σ r) := by
  obtain ⟨hle, hL, hG, -, -⟩ := setL_reg_eq_Ioc hH hM hσ hr hs
  exact algorithm_9_2_1_terminates h rfl hL hG (neg_leftmostPencil_le_lambdaS hH hM) hle

/-- **Algorithm 9.2.1** of [cartis2022evaluation] for the trust-region subproblem (8.1.2). Let $H$
be symmetric, $M$ symmetric positive definite and $\Delta > 0$. Let $s^*$ be a global minimizer
of (8.1.2) with multiplier $\lambda^*$ in the sense of Theorem 8.2.7. Let
$(\lambda^L_k, \lambda^U_k, \lambda^C_k)$ be a run of Algorithm 9.2.1 for the sets
$\mathcal{N}$, $\mathcal{L}$, $\mathcal{G}$ of Section 8.3.2 and the leftmost eigenvalue
$\lambda_1$ of the pencil $(H, M)$. Then the conclusions of
`CartisGouldToint.Chapter09.algorithm_9_2_1_terminates` hold with $a = \lambda_s$: the brackets
contain $\lambda^*$ and are monotone, the width contracts by
$\rho = \max(1 - \theta_L, \theta_U, 1/2) < 1$ at each step $k \ge 1$ that has not stopped, and
if $\lambda_s < \lambda^*$ and $\lambda^L_0 < \lambda^*$, some $\lambda^C_k$ with
$$k \le \left\lceil \frac{\log\bigl((\lambda^U_1 - \lambda^L_1)/(\lambda^* - \max(\lambda^L_0,
  \lambda_s))\bigr)}{\log(1/\rho)} \right\rceil_+ + 1$$
lies in $\mathcal{L}$.

The multiplier conditions are `CartisGouldToint.Chapter08.IsTrustRegionKKT`.

**Correction.** Retains the corrected contraction and the strict lower-bound condition with
trust-region regions.
-/
theorem algorithm_9_2_1_terminates_tr (hH : H.IsHermitian) (hM : M.PosDef) {Δ : ℝ} (hΔ : 0 < Δ)
    {s : EuclideanSpace ℝ (Fin n)} (hs : IsTrustRegionSolution g H M Δ s) {lamStar : ℝ}
    (hkkt : IsTrustRegionKKT g H M Δ s lamStar)
    (h : algorithm_9_2_1 (Chapter08.setN hH hM) (setL_tr hH hM g Δ) (setG_tr hH hM g Δ)
      (leftmostPencil hH hM) lamStar θL θU lo hi c) :
    (∀ k, lo k ≤ lamStar ∧ lamStar ≤ hi k) ∧ Monotone lo ∧ Antitone hi ∧
    max (1 - θL) (max θU (1 / 2)) < 1 ∧
    (∀ k, 1 ≤ k → c k ∉ setL_tr hH hM g Δ →
      hi (k + 1) - lo (k + 1) ≤ max (1 - θL) (max θU (1 / 2)) * (hi k - lo k)) ∧
    (lambdaS hH hM < lamStar → lo 0 < lamStar →
      ∃ k ≤ ⌈Real.log ((hi 1 - lo 1) / (lamStar - max (lo 0) (lambdaS hH hM))) /
        Real.log (1 / max (1 - θL) (max θU (1 / 2)))⌉₊ + 1, c k ∈ setL_tr hH hM g Δ) := by
  obtain ⟨hle, hL, hG, -⟩ := setL_tr_eq_Ioc hH hM hΔ hs hkkt
  exact algorithm_9_2_1_terminates h rfl hL hG (neg_leftmostPencil_le_lambdaS hH hM) hle

end CartisGouldToint.Chapter09
