/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.CartisGouldToint.Chapter05.Section01
import NumlibSurface.CartisGouldToint.Chapter06.Section02

/-!
# Cartis, Gould and Toint, Section 6.3: Convexly constrained least-Euclidean-norm problems

This module formalizes Section 6.3 of [cartis2022evaluation]. The problem is
$\min_{x \in \mathcal{C}} \|r(x)\|$ for a residual $r : \mathbb{R}^n \to \mathbb{R}^m$ and a closed,
convex, nonempty set $\mathcal{C} \subseteq \mathbb{R}^n$. The algorithm ARpLE-CC (Algorithm 6.3.1)
applies the first-order convexly constrained method ARp1-CC (Algorithm 6.2.2) to
$\Phi_\ell(x) = \|r(x)\|^\ell / \ell$ of (5.1.3), and stops at the first iterate with
$$\|r(x)\| \le \epsilon_0 \quad \text{(6.3.1)} \qquad \text{or} \qquad
  \omega_{\Phi_\ell,\mathcal{C},1}(x) \le \epsilon_1 \|r(x)\|^{\ell - 1} \quad \text{(6.3.2)}.$$
Theorem 6.3.1 bounds the number of evaluations of $r$ and of its derivatives by a constant times
$\max[\|r_0\|^{1/2^i}, \|r_0\|^{1 - (\ell - 1)/p}] / \min[\epsilon_0^{1/2^i},
\epsilon_1^{(p+1)/p}]$.

The step conditions of ARp1-CC are the backbone `Optimization.IsFirstOrderCCStep`, and a run is an
instance of `Optimization.IsARRun`. The proof of Theorem 6.3.1 combines the decrease of Lemma 6.2.4
with the potential $\|r\|^{1/2^i}$ of (5.1.27).

## Main definitions

* `CartisGouldToint.Chapter06.PhiEll`: the objective $\Phi_\ell$ of (5.1.3) for a natural exponent
  $\ell$.
* Assumption Φℓ.DpL.C, `CartisGouldToint.Chapter06.AssumptionPhiDpLC`: $\Phi_\ell$ is $p$ times
  continuously differentiable near $\mathcal{C}$ and its $p$-th derivative is Lipschitz on
  $\mathcal{C}$.
* `CartisGouldToint.Chapter06.stopLE`: the termination test (6.3.1)–(6.3.2).
* Algorithm 6.3.1, `CartisGouldToint.Chapter06.algorithm_6_3_1`: a run of ARpLE-CC.

## Main results

* `CartisGouldToint.Chapter06.algorithm_6_3_1.exists_run`: ARpLE-CC runs exist from every feasible
  starting point.
* Equation (6.3.3), `CartisGouldToint.Chapter06.arpleCC_decrease`: the decrease of $\|r\|^\ell$ and
  of the potential $\|r\|^{1/2^i}$ on a successful iteration.
* Theorem 6.3.1, `CartisGouldToint.Chapter06.theorem_6_3_1`: the evaluation complexity of ARpLE-CC.

## Implementation notes

* The algorithmic constants are those of ARp-CC, `CartisGouldToint.Chapter06.ARpCCParams` of
  (6.2.7). Among the step termination constants only $\theta_1$ plays a role.

## Deviations from the source

* **Algorithm 6.3.1, input domain** (generalization). The run predicate accepts any natural
  $\ell,p$ and any real tolerances. The theorem supplies the source's positive degree and
  exponent restrictions. See `CartisGouldToint.Chapter06.algorithm_6_3_1`.
* **Test (6.3.2)** (reading). The source writes the quotient $\omega_{\Phi_\ell,\mathcal{C},1}(x) /
  \|r(x)\|^{\ell - 1} \le \epsilon_1$. The test is written multiplicatively, which avoids division
  by zero; the two forms agree whenever (6.3.1) fails and $\epsilon_0 \ge 0$. See
  `CartisGouldToint.Chapter06.stopLE`.
* **Equation (6.3.3) and the preceding display** (typo). The source multiplies the unscaled measure
  $\omega_{\Phi_\ell,\mathcal{C},1}(x_{k+1})^{(p+1)/p}$ by $\|r(x_{k+1})\|^{(\ell-1)(p+1)/p}$, which
  mixes the scaled and unscaled forms of (5.1.15). The decrease that holds is $\kappa_1 \ell \,
  \omega_{\Phi_\ell,\mathcal{C},1}(x_{k+1})^{(p+1)/p}$. The next estimate (6.3.3)
  uses the normalized measure, with its denominator accounted for by the
  multiplicative stopping inequality. See `CartisGouldToint.Chapter06.arpleCC_decrease`.
* **Theorem 6.3.1** (generalization). Only $\iota_1(p, \ell, i) \ge 0$ is used, which (5.1.38) and
  (5.1.39) each imply, and the theorem assumes only this. The assumption
  $\epsilon_0, \epsilon_1 \le 1$ of the source is not needed. See
  `CartisGouldToint.Chapter06.theorem_6_3_1`.
-/

open Set Optimization
open scoped Nat

namespace CartisGouldToint.Chapter06

variable {n m : ℕ}

set_option hygiene false in
local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)
set_option hygiene false in
local notation "ℝᵐ" => EuclideanSpace ℝ (Fin m)

/-- **Equation (5.1.3)** of [cartis2022evaluation], for Section 6.3. Let
$r : \mathbb{R}^n \to \mathbb{R}^m$ and $\ell \in \mathbb{N}$. The objective is
$$\Phi_\ell(x) = \frac{\|r(x)\|^\ell}{\ell}.$$

For $\ell = 0$ the division by zero gives $\Phi_0 = 0$. This is the same function as
`CartisGouldToint.Chapter05.Phi` of Chapter 5 with a real exponent
(`CartisGouldToint.Chapter06.PhiEll_eq_Phi`), and it is the backbone `Optimization.residualPow`.

**Generalization.** The same residual norm power is extended to the zero natural exponent by Lean
division.
-/
noncomputable abbrev PhiEll (r : ℝⁿ → ℝᵐ) (ℓ : ℕ) : ℝⁿ → ℝ :=
  residualPow r ℓ

/-- The objective $\Phi_\ell$ for a natural exponent $\ell$ is the objective
`CartisGouldToint.Chapter05.Phi` of Chapter 5 with the exponent $\ell$ viewed as a real number.

**Reading.** Identifies the residual objective with the real-exponent Chapter 5 definition,
including zero exponent.
-/
theorem PhiEll_eq_Phi (r : ℝⁿ → ℝᵐ) (ℓ : ℕ) : PhiEll r ℓ = Chapter05.Phi r ℓ :=
  rfl

/-- The objective at a point: $\Phi_\ell(x) = \|r(x)\|^\ell / \ell$.

**Reading.** The natural-power quotient gives the formula for every exponent including zero.
-/
theorem PhiEll_apply (r : ℝⁿ → ℝᵐ) (ℓ : ℕ) (x : ℝⁿ) : PhiEll r ℓ x = ‖r x‖ ^ ℓ / ℓ :=
  residualPow_natCast r ℓ x

/-- **Assumption Φℓ.DpL.C** of [cartis2022evaluation], Section 6.3. Let
$r : \mathbb{R}^n \to \mathbb{R}^m$, $\ell, p \in \mathbb{N}$,
$\mathcal{C} \subseteq \mathbb{R}^n$ and $L \in \mathbb{R}$. The assumption holds if $\Phi_\ell$
is $p$ times continuously differentiable on an open set $\mathcal{D} \supseteq \mathcal{C}$, and
its $p$-th derivative is Lipschitz continuous on $\mathcal{C}$ with constant $L \ge 0$.

It is assumption f.DpL.C, `CartisGouldToint.Chapter06.AssumptionDpLC`, for $f = \Phi_\ell$. The
norm of the derivative tensor is the operator norm. -/
abbrev AssumptionPhiDpLC (r : ℝⁿ → ℝᵐ) (ℓ : ℕ) (C : Set ℝⁿ) (p : ℕ) (L : ℝ) : Prop :=
  AssumptionDpLC (PhiEll r ℓ) C p L

/-- If $\Phi_\ell$ satisfies assumption Φℓ.DpL of Chapter 5 with constant $L$, then it satisfies
Φℓ.DpL.C with $\mathcal{C} = \mathbb{R}^n$ and the same constant. -/
theorem assumptionPhiDpLC_univ {r : ℝⁿ → ℝᵐ} {ℓ p : ℕ} {L : ℝ}
    (h : Chapter05.AssumptionPhiDpL r ℓ p L) : AssumptionPhiDpLC r ℓ univ p L :=
  ⟨h.nonneg, ⟨univ, isOpen_univ, subset_rfl, h.contDiff.contDiffOn⟩, h.lipschitz⟩

/-- **Algorithm 6.3.1** of [cartis2022evaluation], termination test (6.3.1)–(6.3.2). The test of
ARpLE-CC holds at $x$ if
$$\|r(x)\| \le \epsilon_0 \qquad \text{or} \qquad \omega_{\Phi_\ell,\mathcal{C},1}(x) \le
  \epsilon_1 \|r(x)\|^{\ell - 1}.$$

**Reading.** The source writes (6.3.2) as $\omega_{\Phi_\ell,\mathcal{C},1}(x) /
\|r(x)\|^{\ell - 1} \le \epsilon_1$. The multiplicative form avoids division by zero, and the
two forms agree whenever (6.3.1) fails and $\epsilon_0 \ge 0$.

The exponent $\ell - 1$ is subtraction in $\mathbb{N}$, so it is $0$ for $\ell = 0$. -/
def stopLE (r : ℝⁿ → ℝᵐ) (ℓ : ℕ) (C : Set ℝⁿ) (ε₀ ε₁ : ℝ) (x : ℝⁿ) : Prop :=
  ‖r x‖ ≤ ε₀ ∨ omega1 (PhiEll r ℓ) C x ≤ ε₁ * ‖r x‖ ^ (ℓ - 1)

/-- **Algorithm 6.3.1** of [cartis2022evaluation] (ARpLE-CC). Let
$r : \mathbb{R}^n \to \mathbb{R}^m$, $\ell, p \in \mathbb{N}$,
$\mathcal{C} \subseteq \mathbb{R}^n$, algorithmic constants $P$ of ARp-CC, and
$\epsilon_0, \epsilon_1 \in \mathbb{R}$. Sequences of iterates $x_k$, steps $s_k$ and
regularization weights $\sigma_k$ form a **run of ARpLE-CC** if $x_0 \in \mathcal{C}$ and they
form a run of ARp1-CC (Algorithm 6.2.2) for $f = \Phi_\ell$ with the termination test
(6.3.1)–(6.3.2). This means: at each iteration $k$ before termination, the model is the
regularized Taylor model (5.1.8) of $\Phi_\ell$ at $x_k$ of degree $p$ with weight $\sigma_k$,
the step satisfies $x_k + s_k \in \mathcal{C}$, $m_k(s_k) < m_k(0)$ and (6.2.29) with
$\theta_1$, the ratio is (4.1.15), and $x_{k+1}$ and $\sigma_{k+1}$ follow the update (4.1.16).

The run is `Optimization.IsARRun` with the step conditions `Optimization.IsFirstOrderCCStep`,
the ratio `Optimization.taylorRatio`, and the test `CartisGouldToint.Chapter06.stopLE`.

**Generalization.** The source uses $\ell\ge2$, a positive Taylor degree and positive
tolerances. The run predicate leaves these hypotheses to its callers. -/
structure algorithm_6_3_1 (r : ℝⁿ → ℝᵐ) (ℓ : ℕ) (C : Set ℝⁿ) (p : ℕ) (P : ARpCCParams)
    (ε₀ ε₁ : ℝ) (x s : ℕ → ℝⁿ) (σ : ℕ → ℝ) : Prop where
  /-- The initial point $x_0$ lies in $\mathcal{C}$. -/
  mem_zero : x 0 ∈ C
  /-- The sequences form a run of ARp1-CC for $\Phi_\ell$ with the termination test (6.3.1)–(6.3.2).
  -/
  run : IsARRun P.toARParams (fun k => stopLE r ℓ C ε₀ ε₁ (x k))
    (fun k => IsFirstOrderCCStep (PhiEll r ℓ) C p P.θ₁ (x k) (σ k) (s k)) (fun _ => False)
    (taylorRatio (PhiEll r ℓ) p x s) x s σ

/-- **Algorithm 6.3.1** of [cartis2022evaluation], existence of runs. Let $\mathcal{C}$ satisfy
C.CNe, let $\Phi_\ell$ be $p$ times continuously differentiable at every point of $\mathcal{C}$
with $p \ge 1$, and let $\epsilon_1 \ge 0$. Then for all algorithmic constants $P$, all
$\epsilon_0$ and every $x_0 \in \mathcal{C}$ there is a run of ARpLE-CC that starts at $x_0$.

When the test fails at $x_k$, then $\omega_{\Phi_\ell,\mathcal{C},1}(x_k) > 0$, so a global
minimizer of the model over the feasible steps is an admissible step
(`Optimization.exists_isFirstOrderCCStep`).

**Reading.** Constructs a run from local C^p at feasible points and a nonnegative first-order
tolerance, allowing arbitrary norm tolerance.
-/
theorem algorithm_6_3_1.exists_run {r : ℝⁿ → ℝᵐ} {ℓ : ℕ} {C : Set ℝⁿ} {p : ℕ} (P : ARpCCParams)
    {ε₀ ε₁ : ℝ} (hC : AssumptionCNe C) (hΦ : ∀ y ∈ C, ContDiffAt ℝ p (PhiEll r ℓ) y)
    (hp : 1 ≤ p) (hε₁ : 0 ≤ ε₁) {x₀ : ℝⁿ} (hx₀ : x₀ ∈ C) :
    ∃ x s : ℕ → ℝⁿ, ∃ σ : ℕ → ℝ, x 0 = x₀ ∧ algorithm_6_3_1 r ℓ C p P ε₀ ε₁ x s σ := by
  obtain ⟨x, s, σ, hx0, hrun, -⟩ := exists_isARRun P.toARParams (Inv := (· ∈ C))
    (test := stopLE r ℓ C ε₀ ε₁)
    (stepOK := fun y σ s => IsFirstOrderCCStep (PhiEll r ℓ) C p P.θ₁ y σ s)
    (fun y _ t => reductionRatio (PhiEll r ℓ) y t
      ((ftaylorSeries ℝ (PhiEll r ℓ) y).taylorDecrement p t))
    (fun y σ hy _ hσ ht => by
      have hω : 0 < omega1 (PhiEll r ℓ) C y := by
        simp only [stopLE, not_or, not_le] at ht
        exact lt_of_le_of_lt (by positivity) ht.2
      obtain ⟨s, -, hs, -⟩ := exists_isFirstOrderCCStep hC.isClosed hC.convex hy (hΦ y hy) hp
        hσ P.θ₁_pos.le hω
      exact ⟨s, hs, hs.mem⟩) hx₀
  exact ⟨x, s, σ, hx0, ⟨hx0 ▸ hx₀, hrun⟩⟩

namespace algorithm_6_3_1

variable {r : ℝⁿ → ℝᵐ} {ℓ : ℕ} {C : Set ℝⁿ} {p : ℕ} {P : ARpCCParams} {ε₀ ε₁ L : ℝ}
  {x s : ℕ → ℝⁿ} {σ : ℕ → ℝ}

/-- Along a run of ARpLE-CC, if the test fails at all iterations $j < k$, then
$x_k \in \mathcal{C}$. -/
theorem mem (h : algorithm_6_3_1 r ℓ C p P ε₀ ε₁ x s σ) {k : ℕ}
    (hk : ∀ j < k, ¬ stopLE r ℓ C ε₀ ε₁ (x j)) : x k ∈ C :=
  h.run.mem h.mem_zero (fun _ hk _ _ => (h.run.step_of_forall_le hk).mem) k
    (IsARRun.forall_lt_not_stop_iff.2 hk)

/-- Lemma 4.1.2 of [cartis2022evaluation] for ARpLE-CC, as Section 6.2.2 says that Lemmas 4.1.1 and
4.1.2 continue to hold. Let $\mathcal{C}$ satisfy C.CNe and $\Phi_\ell$ satisfy Φℓ.DpL.C with
constant $L$. Along a run of ARpLE-CC, if the test fails at all iterations $j < k$, then
$x_k \in \mathcal{C}$ and
$$\sigma_{\min} \le \sigma_k \le \sigma_{\max} = \max\left(\sigma_0, \frac{\gamma_3 L}{1 -
  \eta_2}\right).$$
-/
theorem sigma_le (h : algorithm_6_3_1 r ℓ C p P ε₀ ε₁ x s σ) (hC : AssumptionCNe C)
    (hΦ : AssumptionPhiDpLC r ℓ C p L) {k : ℕ} (hk : ∀ j < k, ¬ stopLE r ℓ C ε₀ ε₁ (x j)) :
    x k ∈ C ∧ P.σmin ≤ σ k ∧ σ k ≤ P.sigmaMax L :=
  arpcc_sigma_le h.run hC hΦ h.mem_zero (fun _ hstep => ⟨hstep.mem, hstep.decrease⟩) k hk

/-- Let $\ell \ge 1$. Along a run of ARpLE-CC, if the test fails at all iterations $j \le k$, then
$\|r(x_{k+1})\| \le \|r(x_k)\|$.

**Reading.** Residual monotonicity follows on accepted or rejected iterations and includes the
exponent-one case.
-/
theorem norm_succ_le (h : algorithm_6_3_1 r ℓ C p P ε₀ ε₁ x s σ) (hℓ : 1 ≤ ℓ) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ stopLE r ℓ C ε₀ ε₁ (x j)) : ‖r (x (k + 1))‖ ≤ ‖r (x k)‖ := by
  have hℓpos : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  by_cases hs : P.η₁ ≤ taylorRatio (PhiEll r ℓ) p x s k
  · obtain ⟨-, hdec⟩ := h.run.sub_ge_of_succ_taylor (IsARRun.forall_le_not_stop_iff.2 hk)
      (h.run.step_of_forall_le (IsARRun.forall_le_not_stop_iff.2 hk)).decrease hs
    have hσ : 0 ≤ σ k := (h.run.sigma_pos (K := k)
      (fun j hj => IsARRun.forall_le_not_stop_iff.2 hk j hj.le) k le_rfl).le
    have : 0 ≤ P.η₁ * (σ k / ((p + 1)! : ℝ) * ‖s k‖ ^ (p + 1)) := by
      have := P.η₁_pos; positivity
    have hle : PhiEll r ℓ (x (k + 1)) ≤ PhiEll r ℓ (x k) := by linarith
    rw [PhiEll_apply, PhiEll_apply, div_le_div_iff_of_pos_right hℓpos] at hle
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) (by omega)).1 hle
  · rw [h.run.eq_of_not_succ (IsARRun.forall_le_not_stop_iff.2 hk) (not_le.1 hs)]

/-- Let $\ell \ge 1$. Along a run of ARpLE-CC, if the test fails at all iterations $j < k$, then
$\|r(x_k)\| \le \|r(x_0)\|$.

**Reading.** Bounds the active residual by the initial residual with the same exponent-one
extension.
-/
theorem norm_le_norm_zero (h : algorithm_6_3_1 r ℓ C p P ε₀ ε₁ x s σ) (hℓ : 1 ≤ ℓ) :
    ∀ k, (∀ j < k, ¬ stopLE r ℓ C ε₀ ε₁ (x j)) → ‖r (x k)‖ ≤ ‖r (x 0)‖ := by
  intro k
  induction k with
  | zero => exact fun _ => le_rfl
  | succ k ih =>
    intro hk
    exact (h.norm_succ_le hℓ fun j hj => hk j (Nat.lt_succ_of_le hj)).trans
      (ih fun j hj => hk j (hj.trans k.lt_succ_self))

end algorithm_6_3_1

section Decrease

variable {r : ℝⁿ → ℝᵐ} {ℓ : ℕ} {C : Set ℝⁿ} {p : ℕ} {P : ARpCCParams} {ε₀ ε₁ L : ℝ}
  {x s : ℕ → ℝⁿ} {σ : ℕ → ℝ}

/-- **Equation (6.3.3)** of [cartis2022evaluation] and the display before it. Let $\mathcal{C}$
satisfy C.CNe, let $\Phi_\ell$ satisfy Φℓ.DpL.C with constant $L$, and let $p, \ell \ge 1$.
Consider a run of ARpLE-CC, and let $k$ be a successful iteration ($\rho_k \ge \eta_1$) such
that the test fails at all iterations $j \le k$. Then
$$\|r(x_k)\|^\ell - \|r(x_{k+1})\|^\ell \ge \kappa_1 \ell \,
  \omega_{\Phi_\ell,\mathcal{C},1}(x_{k+1})^{(p+1)/p},$$
with $\kappa_1$ of (4.1.32) for $L = L_{\Phi_\ell,p}$. If moreover the test fails at $x_{k+1}$,
then for every $i \in \mathbb{N}$ with $\iota_1 = (2^i - 1)/2^i - (\ell - 1)/p \ge 0$, every
$\beta \in (0, 1)$ and all $\epsilon_0, \epsilon_1 > 0$,
$$\|r(x_k)\|^{1/2^i} - \|r(x_{k+1})\|^{1/2^i} \ge \frac{\min(\kappa_{r0}, \kappa_{r1})
  \min(\epsilon_0^{1/2^i}, \epsilon_1^{(p+1)/p})}{\max(1, \|r(x_0)\|^{\iota_1})},$$
where $\kappa_{r0} = 1 - \beta^{1/2^i}$ and $\kappa_{r1} = \kappa_1 \beta^{(\ell-1)(p+1)/p} /
2^i$. The second bound is (6.3.3) together with (5.1.27).

**Typo.** The display before (6.3.3) in the source multiplies the unscaled measure
$\omega_{\Phi_\ell,\mathcal{C},1}(x_{k+1})^{(p+1)/p}$ by $\|r(x_{k+1})\|^{(\ell-1)(p+1)/p}$,
which mixes the scaled and unscaled forms of (5.1.15). Equation (6.3.3) then uses the
unscaled measure where the normalized measure is needed for the exponent $\iota_1$.
The Lean bound substitutes $\epsilon_1$ for the normalized measure when the next iterate
fails the stopping test and uses the initial norm in its denominator.

The first bound is Lemma 6.2.4 for $f = \Phi_\ell$. The constant $\kappa_1$ is
`CartisGouldToint.Chapter06.kappa1CC`. -/
theorem arpleCC_decrease (hC : AssumptionCNe C) (hΦ : AssumptionPhiDpLC r ℓ C p L)
    (h : algorithm_6_3_1 r ℓ C p P ε₀ ε₁ x s σ) (hp : 1 ≤ p) (hℓ : 1 ≤ ℓ) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ stopLE r ℓ C ε₀ ε₁ (x j)) (hs : P.η₁ ≤ taylorRatio (PhiEll r ℓ) p x s k) :
    ℓ * kappa1CC P L p * omega1 (PhiEll r ℓ) C (x (k + 1)) ^ (((p : ℝ) + 1) / p) ≤
        ‖r (x k)‖ ^ ℓ - ‖r (x (k + 1))‖ ^ ℓ ∧
      (¬ stopLE r ℓ C ε₀ ε₁ (x (k + 1)) → ∀ i : ℕ,
        0 ≤ ((2 : ℝ) ^ i - 1) / 2 ^ i - ((ℓ : ℝ) - 1) / p → ∀ β : ℝ, 0 < β → β < 1 →
        0 < ε₀ → 0 < ε₁ →
        min (1 - β ^ (1 / 2 ^ i : ℝ))
            (kappa1CC P L p * β ^ (((ℓ : ℝ) - 1) * (((p : ℝ) + 1) / p)) / 2 ^ i) *
          min (ε₀ ^ (1 / 2 ^ i : ℝ)) (ε₁ ^ (((p : ℝ) + 1) / p)) /
          max 1 (‖r (x 0)‖ ^ (((2 : ℝ) ^ i - 1) / 2 ^ i - ((ℓ : ℝ) - 1) / p)) ≤
        ‖r (x k)‖ ^ (1 / 2 ^ i : ℝ) - ‖r (x (k + 1))‖ ^ (1 / 2 ^ i : ℝ)) := by
  have hℓpos : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hk' : ∀ j ≤ k, ¬ IsARRun.Stop (fun k => stopLE r ℓ C ε₀ ε₁ (x k)) (fun _ => False) j :=
    fun j hj h' => h'.elim (hk j hj) id
  obtain ⟨hxk, hσ1, hσ2⟩ := h.sigma_le hC hΦ (k := k) fun j hj => hk j hj.le
  have hstep := h.run.step_of_forall_le hk'
  have hdec := hstep.sub_ge hC.convex hΦ.contDiffAt hΦ.lipschitz hΦ.nonneg hxk hp
    P.θ₁_pos.le P.σmin_nonneg hσ1 hσ2 P.η₁_pos hs
  rw [← h.run.eq_add_of_succ hk' hs, PhiEll_apply, PhiEll_apply] at hdec
  have hA : ℓ * kappa1CC P L p * omega1 (PhiEll r ℓ) C (x (k + 1)) ^ (((p : ℝ) + 1) / p) ≤
      ‖r (x k)‖ ^ ℓ - ‖r (x (k + 1))‖ ^ ℓ := by
    have h1 : ‖r (x k)‖ ^ ℓ / ℓ - ‖r (x (k + 1))‖ ^ ℓ / ℓ =
        (‖r (x k)‖ ^ ℓ - ‖r (x (k + 1))‖ ^ ℓ) / ℓ := by ring
    rw [h1, le_div_iff₀ hℓpos] at hdec
    rw [kappa1CC_def, omega1_def]
    linarith
  refine ⟨hA, fun hnot i hι β hβ0 hβ1 hε₀ hε₁ => ?_⟩
  simp only [stopLE, not_or, not_le] at hnot
  have hba := h.norm_succ_le hℓ hk
  have haR := h.norm_le_norm_zero hℓ k fun j hj => hk j hj.le
  exact rpow_inv_two_pow_sub_ge_min hp hℓ hι hβ0 hβ1 (kappa1CC_pos hΦ.nonneg) hε₀
    hε₁ haR hba hnot.1 hnot.2 (by linarith)

/-- Let $L \ge 0$, $\beta > 0$ and $i \in \mathbb{N}$. With $\kappa_{r1} = \kappa_1
\beta^{(\ell-1)(p+1)/p} / 2^i$,
$$\frac{1}{\kappa_{r1}} = \frac{2^i}{\beta^{(\ell-1)(p+1)/p}} \kappa^S_{\mathrm{ARp1CC}},$$
which is the form of the second entry of $\kappa^S_{\mathrm{ARpLE},1}$ in Theorem 6.3.1 of
[cartis2022evaluation]. Here $\kappa^S_{\mathrm{ARp1CC}}$ is
`CartisGouldToint.Chapter06.kappaSARp1CC`. -/
theorem one_div_kappa1CC_mul_rpow_div_two_pow (hL : 0 ≤ L) {β : ℝ} (hβ : 0 < β) (i : ℕ) :
    1 / (kappa1CC P L p * β ^ (((ℓ : ℝ) - 1) * (((p : ℝ) + 1) / p)) / 2 ^ i) =
      2 ^ i / β ^ (((ℓ : ℝ) - 1) * (((p : ℝ) + 1) / p)) * kappaSARp1CC P L p := by
  have h1 := kappa1CC_mul_kappaSARp1CC (P := P) hL p
  have := kappa1CC_pos (P := P) (p := p) hL
  have hβe : 0 < β ^ (((ℓ : ℝ) - 1) * (((p : ℝ) + 1) / p)) := Real.rpow_pos_of_pos hβ _
  have hS : kappaSARp1CC P L p = 1 / kappa1CC P L p := by
    rw [eq_div_iff this.ne', mul_comm]; exact h1
  rw [hS]
  field_simp

/-- **Theorem 6.3.1** of [cartis2022evaluation]. Let $p \ge 1$, $\ell \ge 2$ and $i \ge 0$ be
integers with
$$\iota_1 = \frac{2^i - 1}{2^i} - \frac{\ell - 1}{p} \ge 0,$$
let $\beta \in (0, 1)$, let $\mathcal{C}$ satisfy C.CNe, let $\Phi_\ell$ satisfy Φℓ.DpL.C with
constant $L$, and let $\epsilon_0, \epsilon_1 > 0$. Then every run of ARpLE-CC terminates: there
is a first index $k_\epsilon$ at which $\|r(x_{k_\epsilon})\| \le \epsilon_0$ or
$\omega_{\Phi_\ell,\mathcal{C},1}(x_{k_\epsilon}) \le \epsilon_1 \|r(x_{k_\epsilon})\|^{\ell -
1}$. With
$$R = \frac{\max[\|r_0\|^{1/2^i}, \|r_0\|^{1 - (\ell - 1)/p}]}{\min[\epsilon_0^{1/2^i},
  \epsilon_1^{(p+1)/p}]},$$
the number of evaluations of $r$ is at most $\kappa^A R + \kappa^C$, and the number of
evaluations of its derivatives is at most $\kappa^S R + 2$, where
$$\kappa^S = \max\left(\frac{1}{1 - \beta^{1/2^i}}, \frac{2^i}{\beta^{(\ell-1)(p+1)/p}}
  \frac{(p+1)!}{\eta_1 \sigma_{\min}} \left(\frac{L + \sigma_{\max} + \theta_1
  p!}{p!}\right)^{(p+1)/p}\right),$$
$\sigma_{\max} = \max(\sigma_0, \gamma_3 L / (1 - \eta_2))$ as in (5.1.60), $\kappa^A = \kappa^S
(1 + |\log \gamma_1| / \log \gamma_2)$, and $\kappa^C = (|\log \gamma_1| + \log(\sigma_{\max} /
\sigma_0)) / \log \gamma_2 + 2$ as in (5.1.61).

**Generalization.** The proof uses only $\iota_1 \ge 0$, which (5.1.38) and (5.1.39) each imply
(`CartisGouldToint.Chapter05.lemma_5_1_6`). The tolerances need only be positive.

The counts are `Optimization.funEvalCount` and `Optimization.derivEvalCount` for the
run of $\Phi_\ell$, and $r_0 = r(x_0)$. The source interprets the bounds as residual
and residual-derivative evaluations. That interpretation uses the smooth residual
of §6.3 and evaluates derivatives of $\Phi_\ell$ from those of $r$. -/
theorem theorem_6_3_1 {i : ℕ} (hp : 1 ≤ p) (hℓ : 2 ≤ ℓ)
    (hι : 0 ≤ ((2 : ℝ) ^ i - 1) / 2 ^ i - ((ℓ : ℝ) - 1) / p) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hC : AssumptionCNe C) (hΦ : AssumptionPhiDpLC r ℓ C p L)
    (h : algorithm_6_3_1 r ℓ C p P ε₀ ε₁ x s σ) (hε₀ : 0 < ε₀) (hε₁ : 0 < ε₁) :
    ∃ kε, IsFirstHit (fun k => stopLE r ℓ C ε₀ ε₁ (x k)) kε ∧
      (funEvalCount kε : ℝ) ≤
        max (1 / (1 - β ^ (1 / 2 ^ i : ℝ)))
            (2 ^ i / β ^ (((ℓ : ℝ) - 1) * (((p : ℝ) + 1) / p)) * kappaSARp1CC P L p) *
          (1 + |Real.log P.γ₁| / Real.log P.γ₂) *
          max (‖r (x 0)‖ ^ (1 / 2 ^ i : ℝ)) (‖r (x 0)‖ ^ (1 - ((ℓ : ℝ) - 1) / p)) /
          min (ε₀ ^ (1 / 2 ^ i : ℝ)) (ε₁ ^ (((p : ℝ) + 1) / p)) +
        ((|Real.log P.γ₁| + Real.log (P.sigmaMax L / P.σ₀)) / Real.log P.γ₂ + 2) ∧
      (derivEvalCount (fun k => P.η₁ ≤ taylorRatio (PhiEll r ℓ) p x s k) kε : ℝ) ≤
        max (1 / (1 - β ^ (1 / 2 ^ i : ℝ)))
            (2 ^ i / β ^ (((ℓ : ℝ) - 1) * (((p : ℝ) + 1) / p)) * kappaSARp1CC P L p) *
          max (‖r (x 0)‖ ^ (1 / 2 ^ i : ℝ)) (‖r (x 0)‖ ^ (1 - ((ℓ : ℝ) - 1) / p)) /
          min (ε₀ ^ (1 / 2 ^ i : ℝ)) (ε₁ ^ (((p : ℝ) + 1) / p)) + 2 := by
  have hL := hΦ.nonneg
  rw [← one_div_kappa1CC_mul_rpow_div_two_pow (ℓ := ℓ) hL hβ0 i]
  set α : ℝ := 1 / 2 ^ i with hαdef
  have hα : 0 < α := by positivity
  set R := ‖r (x 0)‖ with hRdef
  have hR0 : 0 ≤ R := norm_nonneg _
  set ι := ((2 : ℝ) ^ i - 1) / 2 ^ i - ((ℓ : ℝ) - 1) / p with hιdef
  set κr0 := 1 - β ^ α with hκr0def
  set κr1 := kappa1CC P L p * β ^ (((ℓ : ℝ) - 1) * (((p : ℝ) + 1) / p)) / 2 ^ i
  have hκr0 : 0 < κr0 := by have := Real.rpow_lt_one hβ0.le hβ1 hα; linarith
  have hκr1 : 0 < κr1 := by
    have := kappa1CC_pos (P := P) (p := p) hL; positivity
  set μ := min (ε₀ ^ α) (ε₁ ^ (((p : ℝ) + 1) / p)) with hμdef
  have hμ : 0 < μ := by positivity
  set δ := min κr0 κr1 * μ / max 1 (R ^ ι) with hδdef
  have hM1 : 0 < max 1 (R ^ ι) := one_pos.trans_le (le_max_left _ _)
  have hδ : 0 < δ := div_pos (mul_pos (lt_min hκr0 hκr1) hμ) hM1
  have hdec : ∀ k, (∀ j ≤ k + 1, ¬ IsARRun.Stop (fun k => stopLE r ℓ C ε₀ ε₁ (x k))
      (fun _ => False) j) → P.η₁ ≤ taylorRatio (PhiEll r ℓ) p x s k →
      δ ≤ ‖r (x k)‖ ^ α - ‖r (x (k + 1))‖ ^ α := by
    intro k hk hs
    have hk' : ∀ j ≤ k + 1, ¬ stopLE r ℓ C ε₀ ε₁ (x j) := fun j hj h' => hk j hj (Or.inl h')
    exact (arpleCC_decrease hC hΦ h hp (by omega) (fun j hj => hk' j (hj.trans k.le_succ))
      hs).2 (hk' (k + 1) le_rfl) i hι β hβ0 hβ1 hε₀ hε₁
  obtain ⟨kε, hfirst, hF, hD⟩ := h.run.exists_isFirstHit_of_decrease
    (σmax := P.sigmaMax L)
    (fun k hk => (h.sigma_le hC hΦ (k := k) fun j hj h' => hk j hj (Or.inl h')).2.2)
    (V := fun k => ‖r (x k)‖ ^ α) (Vlow := 0) hδ
    (fun k hk => Real.rpow_le_rpow (norm_nonneg _)
      (h.norm_succ_le (by omega) fun j hj h' => hk j hj (Or.inl h')) hα.le)
    (fun k _ => by positivity) hdec
  -- `‖r_0‖^{1/2^i}/δ ≤ κ^S M/μ`
  set κS := max (1 / κr0) (1 / κr1) with hκS
  have hmin : 1 / min κr0 κr1 ≤ κS := by
    rcases min_cases κr0 κr1 with ⟨hm, -⟩ | ⟨hm, -⟩
    · rw [hm]; exact le_max_left _ _
    · rw [hm]; exact le_max_right _ _
  have hp0 : (p : ℝ) ≠ 0 := by have : (1 : ℝ) ≤ p := by exact_mod_cast hp
                               positivity
  have hRM : R ^ α * max 1 (R ^ ι) ≤ max (R ^ α) (R ^ (1 - ((ℓ : ℝ) - 1) / p)) := by
    rw [mul_max_of_nonneg _ _ (Real.rpow_nonneg hR0 _), mul_one]
    refine max_le_max le_rfl ((Real.le_rpow_add hR0 _ _).trans_eq ?_)
    congr 1
    rw [hαdef, hιdef]; field_simp; ring
  have hratio : R ^ α / δ ≤ κS * max (R ^ α) (R ^ (1 - ((ℓ : ℝ) - 1) / p)) / μ := by
    have hmpos : 0 < min κr0 κr1 := lt_min hκr0 hκr1
    calc R ^ α / δ = 1 / min κr0 κr1 * (R ^ α * max 1 (R ^ ι)) / μ := by
          rw [hδdef]; field_simp
      _ ≤ κS * max (R ^ α) (R ^ (1 - ((ℓ : ℝ) - 1) / p)) / μ := by
          refine div_le_div_of_nonneg_right ?_ hμ.le
          exact mul_le_mul hmin hRM (by positivity) ((one_div_pos.2 hmpos).le.trans hmin)
  have hκA : 0 ≤ 1 + |Real.log P.γ₁| / Real.log P.γ₂ := by
    have := P.log_γ₂_pos; positivity
  refine ⟨kε, ?_, ?_, ?_⟩
  · simpa [isFirstHit_iff, IsARRun.Stop] using hfirst
  · simp only [sub_zero] at hF
    refine hF.trans ?_
    have := mul_le_mul_of_nonneg_left hratio hκA
    calc (1 + |Real.log P.γ₁| / Real.log P.γ₂) * (R ^ α / δ) +
          ((|Real.log P.γ₁| + Real.log (P.sigmaMax L / P.σ₀)) / Real.log P.γ₂ + 2)
        ≤ (1 + |Real.log P.γ₁| / Real.log P.γ₂) *
            (κS * max (R ^ α) (R ^ (1 - ((ℓ : ℝ) - 1) / p)) / μ) +
          ((|Real.log P.γ₁| + Real.log (P.sigmaMax L / P.σ₀)) / Real.log P.γ₂ + 2) :=
          by linarith
      _ = _ := by ring
  · simp only [sub_zero] at hD
    linarith

end Decrease

end CartisGouldToint.Chapter06
