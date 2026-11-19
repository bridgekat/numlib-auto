/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Optimization.Complexity.Telescoping
import Numlib.Optimization.ModelBased.QuadraticModel
import Numlib.Optimization.ModelBased.TRRun
import NumlibSurface.CartisGouldToint.Chapter02.Section02

/-!
# Cartis, Gould and Toint, Section 2.3: The trust-region method

This module formalizes §2.3 of [cartis2022evaluation]: the first-order trust-region algorithm TR1
for the minimization of a function $f : \mathbb{R}^n \to \mathbb{R}$. At iteration $k$ the method
computes a step $s_k$ in the trust region $\|s\| \le \Delta_k$ that decreases the quadratic model
(2.3.1)
$$m_k(s) = f(x_k) + \langle \nabla f(x_k), s \rangle + \tfrac12 \langle s, B_k s \rangle$$
at least as much as the Cauchy step does. It accepts the trial point $x_k + s_k$ when the ratio
$\rho_k$ of achieved to predicted decrease (2.3.6) is at least $\eta_1$, and it updates the radius
by (2.3.7). The method stops at the first iterate with $\|\nabla f(x_k)\| \le \epsilon$.

Under the assumptions f.Bb, f.gL and m.HBa, TR1 stops after $O(\epsilon^{-2})$ evaluations of $f$
and $\nabla f$ (Theorem 2.3.7), and this order is attained (Theorem 2.3.8). TR1 is an instance of
the generic trust-region run of `Numlib.Optimization.ModelBased.TRRun`, and the counting arguments
come from `Numlib.Optimization.Complexity.Telescoping`.

## Main definitions

* (2.3.1), `CartisGouldToint.Chapter02.tr1Model`: the quadratic model $m(s) = f(x) + \langle \nabla
  f(x), s \rangle + \frac12 \langle s, Bs \rangle$.
* (2.3.3), `CartisGouldToint.Chapter02.TR1Params`: the constants $\Delta_0$, $\eta_1, \eta_2$ and
  $\gamma_1, \gamma_2, \gamma_3$ of TR1.
* (2.3.4)–(2.3.5), `CartisGouldToint.Chapter02.tr1Step`: the step lies in the trust region and
  decreases the model at least as much as a Cauchy step.
* (2.3.6), `CartisGouldToint.Chapter02.tr1Ratio`: the ratio of achieved to predicted decrease.
* Algorithm 2.3.1, `CartisGouldToint.Chapter02.algorithm_2_3_1`: TR1 as a predicate on the sequences
  of a run.
* Assumption m.HBa, `CartisGouldToint.Chapter02.AssumptionMHBa`: the model operators satisfy
  $\|B_k\| \le \kappa_B$.

## Main results

* `CartisGouldToint.Chapter02.exists_algorithm_2_3_1`: a TR1 run exists for every starting point and
  every sequence of self-adjoint model operators.
* Lemma 2.3.1, `CartisGouldToint.Chapter02.lemma_2_3_1`: while $\Delta_k \ge \Delta_{\min}$, the
  number of iterations is bounded by a multiple of the number of successful iterations plus a
  constant.
* Lemma 2.3.2, `CartisGouldToint.Chapter02.lemma_2_3_2`: the Cauchy step decreases the model by at
  least $\frac12 \|\nabla f(x)\| \min(\|\nabla f(x)\|/(1 + \|B\|), \Delta)$.
* Lemma 2.3.2, `CartisGouldToint.Chapter02.lemma_2_3_2_pred_pos`: before termination the predicted
  decrease is positive.
* Lemma 2.3.3, `CartisGouldToint.Chapter02.lemma_2_3_3`: an iteration with a small enough radius is
  very successful.
* Lemma 2.3.4, `CartisGouldToint.Chapter02.lemma_2_3_4`: the radius is bounded below by a constant
  times the smallest gradient norm so far.
* Lemma 2.3.5, `CartisGouldToint.Chapter02.lemma_2_3_5`: the model decrease is at least
  $\kappa_{\mathrm{decr}} \|\nabla f(x_k)\| \min_{i \le k} \|\nabla f(x_i)\|$.
* Lemma 2.3.6, `CartisGouldToint.Chapter02.lemma_2_3_6`: before termination there are at most
  $\kappa^S_{\mathrm{TR1}} (f(x_0) - f_{\mathrm{low}})/\epsilon^2$ successful iterations.
* Theorem 2.3.7, `CartisGouldToint.Chapter02.theorem_2_3_7`: TR1 stops after $O(\epsilon^{-2})$
  evaluations of $f$ and of $\nabla f$, with the constants (2.3.21)–(2.3.23).
* Theorem 2.3.8, `CartisGouldToint.Chapter02.theorem_2_3_8`: there is a one-dimensional example on
  which TR1 needs exactly $\epsilon^{-2} + 1$ evaluations.

## Conventions

* $\mathbb{R}^n$ is `EuclideanSpace ℝ (Fin n)`.
* The book's symmetric matrix $B_k$ is a self-adjoint continuous linear operator on $\mathbb{R}^n$.
  Its norm $\|B_k\|$ is the operator norm, which is the spectral norm of the matrix.
* The set $\mathcal{S}_k = \{j \le k : \rho_j \ge \eta_1\}$ of successful iterations is
  `Optimization.successSet`.
* "Before termination at iteration $k$" means that the test $\|\nabla f(x_j)\| \le \epsilon$ fails
  for every $j \le k$.

## Implementation notes

* A TR1 run is `Optimization.IsTRRun` with the termination test $\|\nabla f(x_k)\| \le \epsilon$,
  the step condition `CartisGouldToint.Chapter02.tr1Step` and the ratio
  `CartisGouldToint.Chapter02.tr1Ratio`. Steps 3–4 are `Optimization.TRAcceptance`.
* The free choices of the algorithm (the operators $B_k$, the steps $s_k$ and the new radii within
  the ranges of (2.3.7)) are hypotheses of a run.

## Deviations from the source

* **Equations (2.3.1) and (2.3.6)** (generalization). The model formula accepts any
  linear operator, with symmetry imposed by the run. The ratio is total, with value $0$
  at zero predicted decrease. The Cauchy condition rules out that denominator before
  termination. See `CartisGouldToint.Chapter02.tr1Model` and
  `CartisGouldToint.Chapter02.tr1Ratio`.
* **Equation (2.3.5)** (reading). The Cauchy step is constrained by
  $t\|\nabla f(x_k)\|\le \Delta_k$, using the trust-region ball (2.3.2)
  centered at the current iterate to interpret the printed $\mathcal{R}_k$.
* **Lemma 2.3.4** (reading). The bound is stated for every iteration up to and including the
  termination index, where the run is defined. See `CartisGouldToint.Chapter02.lemma_2_3_4`.
* **Equations (2.3.17), (2.3.20), and (2.3.23)** (reading). The constants involving
  division by the initial gradient norm are totalized. When that norm vanishes the
  algorithm terminates immediately.
* **Lemma 2.3.5** (typo). The source writes the model decrease as $m_k(x_k) - m_k(x_k + s_k)$; it is
  $m_k(0) - m_k(s_k)$. See `CartisGouldToint.Chapter02.lemma_2_3_5`.
* **Theorem 2.3.8** (correction). With the printed $B_k = 2t^{-1}$ the Cauchy condition (2.3.4)
  fails. The example uses $B_k = t^{-1} I$ with $t = \Delta_0/2$, and then $\rho_k = 2$. See
  `CartisGouldToint.Chapter02.theorem_2_3_8`.
* **Theorem 2.3.8, tolerance and counts** (reading). The example assumes an integral
  $\epsilon^{-2}$ and counts the initial objective and gradient evaluations, for a total
  of $\epsilon^{-2}+1$ each.

## Not formalized

* **The relaxed Cauchy condition (2.3.8).** The source mentions $m_k(0) - m_k(s_k) \ge \kappa
  (m_k(0) - m_k(s_k^C))$ for some $\kappa \in (0, 1]$ as an alternative to (2.3.4). TR1 runs here
  use (2.3.4).
-/

open Set Finset Optimization Subproblem
open scoped RealInnerProductSpace

namespace CartisGouldToint.Chapter02

variable {n : ℕ}

/-- **Equation (2.3.3)** of [cartis2022evaluation]. The constants of Algorithm 2.3.1 consist of an
initial radius $\Delta_0 > 0$, acceptance thresholds $0 < \eta_1 \le \eta_2 < 1$ and radius
factors $0 < \gamma_1 \le \gamma_2 < 1 < \gamma_3$.

The structure extends `Optimization.TRParams`, which allows $\gamma_3 \ge 1$, by the strict
inequality $\gamma_3 > 1$. -/
structure TR1Params extends Optimization.TRParams where
  /-- The expansion factor satisfies $\gamma_3 > 1$. -/
  one_lt_γ₃ : 1 < γ₃

/-- **Equation (2.3.1)** of [cartis2022evaluation]. Let $f : \mathbb{R}^n \to \mathbb{R}$, let
$x \in \mathbb{R}^n$, and let $B$ be a continuous linear operator on $\mathbb{R}^n$. The
**quadratic model** of TR1 at $x$ is
$$m(s) = f(x) + \langle \nabla f(x), s \rangle + \tfrac12 \langle s, Bs \rangle.$$

The operator $B$ stands for the book's symmetric matrix $B_k$. The definition does not require
$B$ to be self-adjoint; a TR1 run does.

**Reading.** The model formula accepts an arbitrary linear operator, with symmetry imposed in the
algorithm.
-/
noncomputable def tr1Model (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n))
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (s : EuclideanSpace ℝ (Fin n)) : ℝ :=
  f x + ⟪gradient f x, s⟫ + 1 / 2 * ⟪s, B s⟫

section Model

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {x s : EuclideanSpace ℝ (Fin n)}
  {B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}

/-- The TR1 model is $f(x)$ plus the quadratic `Subproblem.quadModel` with gradient $\nabla f(x)$
and operator $B$: $m(s) = f(x) + \langle \nabla f(x), s \rangle + \frac12 \langle s, Bs
\rangle$. -/
theorem tr1Model_eq : tr1Model f x B s = f x + quadModel (gradient f x) B s := by
  rw [tr1Model, quadModel_def]; ring

/-- The model decrease is $m(0) - m(s) = -q(s)$, where $q$ is `Subproblem.quadModel` with gradient
$\nabla f(x)$ and operator $B$. -/
theorem tr1Model_zero_sub :
    tr1Model f x B 0 - tr1Model f x B s = -quadModel (gradient f x) B s := by
  rw [tr1Model_eq, tr1Model_eq, quadModel_zero]; ring

end Model

/-- Step 2 of Algorithm 2.3.1, conditions (2.3.4)–(2.3.5) of [cartis2022evaluation]. A step $s$ is a
**TR1 step** at $x$ with radius $\Delta$ if $\|s\| \le \Delta$ and $m(s) \le m(-t \nabla f(x))$
for some Cauchy step length $t$, where $m$ is the TR1 model and the Cauchy step length is in the
sense of `Optimization.IsCauchyStep`.

**Reading.** Uses explicit ball feasibility and the trust-region Cauchy minimization for the printed
region.
-/
def tr1Step (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (x : EuclideanSpace ℝ (Fin n))
    (Δ : ℝ) (s : EuclideanSpace ℝ (Fin n)) : Prop :=
  ‖s‖ ≤ Δ ∧ ∃ t, IsCauchyStep (gradient f x) B Δ t ∧
    tr1Model f x B s ≤ tr1Model f x B (-(t • gradient f x))

/-- A step $s$ is a TR1 step if and only if $\|s\| \le \Delta$ and $m(s) \le m(-t \nabla f(x))$ for
some Cauchy step length $t$.

**Reading.** Unfolds the ball constraint and strong Cauchy condition.
-/
theorem tr1Step_iff {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)} {x : EuclideanSpace ℝ (Fin n)}
    {Δ : ℝ} {s : EuclideanSpace ℝ (Fin n)} :
    tr1Step f B x Δ s ↔ ‖s‖ ≤ Δ ∧ ∃ t, IsCauchyStep (gradient f x) B Δ t ∧
      tr1Model f x B s ≤ tr1Model f x B (-(t • gradient f x)) :=
  Iff.rfl

/-- The ratio (2.3.6) of [cartis2022evaluation] of achieved to predicted decrease:
$$\rho = \frac{f(x) - f(x + s)}{m(0) - m(s)},$$
where $m$ is the TR1 model. Lean's division gives $\rho = 0$ when $m(0) = m(s)$.

**Reading.** Totalized ratio equals zero when the model decrease is zero.
-/
noncomputable def tr1Ratio (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n))
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (s : EuclideanSpace ℝ (Fin n)) : ℝ :=
  reductionRatio f x s (tr1Model f x B 0 - tr1Model f x B s)

/-- The TR1 ratio is `Optimization.reductionRatio` of $f$ at $x$ along $s$ with predicted decrease
$m(0) - m(s)$. -/
theorem tr1Ratio_def (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n))
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (s : EuclideanSpace ℝ (Fin n)) :
    tr1Ratio f x B s = reductionRatio f x s (tr1Model f x B 0 - tr1Model f x B s) :=
  rfl

/-- **Algorithm 2.3.1** of [cartis2022evaluation] (TR1). Let $f : \mathbb{R}^n \to \mathbb{R}$, let
the TR1 constants be given, and let $\epsilon \in \mathbb{R}$. Sequences of model operators
$B_k$, iterates $x_k$, trial steps $s_k$ and radii $\Delta_k$ form a **TR1 run** if
$\epsilon > 0$, every $B_k$ is self-adjoint, $\Delta_0$ is the initial radius of the constants,
and the following holds at every iteration $k$ at which the test
$\|\nabla f(x_j)\| \le \epsilon$ has failed for all $j \le k$.

* Step 2: $\|s_k\| \le \Delta_k$, and $s_k$ decreases the model $m_k$ at least as much as a
  Cauchy step (2.3.4)–(2.3.5).
* Step 3: $x_{k+1} = x_k + s_k$ if $\rho_k \ge \eta_1$, and $x_{k+1} = x_k$ otherwise, where
  $\rho_k$ is the ratio (2.3.6).
* Step 4: the radius update (2.3.7), that is, $\Delta_{k+1} \in [\Delta_k, \gamma_3 \Delta_k]$
  if $\rho_k \ge \eta_2$, $\Delta_{k+1} \in [\gamma_2 \Delta_k, \Delta_k]$ if
  $\eta_1 \le \rho_k < \eta_2$, and $\Delta_{k+1} \in [\gamma_1 \Delta_k, \gamma_2 \Delta_k]$ if
  $\rho_k < \eta_1$.

The run stops at the first $k$ with $\|\nabla f(x_k)\| \le \epsilon$, and nothing is required
after that. The structure is the generic run `Optimization.IsTRRun` with the step condition
`CartisGouldToint.Chapter02.tr1Step` and the ratio `CartisGouldToint.Chapter02.tr1Ratio`. -/
structure algorithm_2_3_1 (f : EuclideanSpace ℝ (Fin n) → ℝ) (P : TR1Params) (ε : ℝ)
    (B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (x s : ℕ → EuclideanSpace ℝ (Fin n)) (Δ : ℕ → ℝ) : Prop where
  /-- The accuracy level satisfies $\epsilon > 0$. -/
  ε_pos : 0 < ε
  /-- Every model operator $B_k$ is self-adjoint. -/
  symm : ∀ k, (B k : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)).IsSymmetric
  /-- Steps 1–4 hold in the form of the generic trust-region run `Optimization.IsTRRun`. -/
  run : IsTRRun P.toTRParams (fun k => ‖gradient f (x k)‖ ≤ ε)
    (fun k => tr1Step f (B k) (x k) (Δ k) (s k)) (fun k => tr1Ratio f (x k) (B k) (s k)) x s Δ

/-- Existence of runs of Algorithm 2.3.1 of [cartis2022evaluation]. Let
$f : \mathbb{R}^n \to \mathbb{R}$, let the TR1 constants be given, let $\epsilon > 0$, let
$(B_k)$ be a sequence of self-adjoint operators on $\mathbb{R}^n$, and let
$x_0 \in \mathbb{R}^n$. Then there is a TR1 run with the model operators $B_k$ that starts at
$x_0$.

The proof takes as step a global minimizer of the model in the trust region, which satisfies the
Cauchy condition (`Optimization.exists_isMinOn_quadModel_ball`). -/
theorem exists_algorithm_2_3_1 (f : EuclideanSpace ℝ (Fin n) → ℝ) (P : TR1Params) {ε : ℝ}
    (hε : 0 < ε) (B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hB : ∀ k, (B k : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)).IsSymmetric)
    (x₀ : EuclideanSpace ℝ (Fin n)) :
    ∃ x s Δ, x 0 = x₀ ∧ algorithm_2_3_1 f P ε B x s Δ := by
  obtain ⟨x, s, Δ, hx0, hrun, -⟩ := exists_isTRRun P.toTRParams (Inv := fun _ => True)
    (test := fun y => ‖gradient f y‖ ≤ ε) (stepOK := fun k y Δ s => tr1Step f (B k) y Δ s)
    (fun k y _ s => tr1Ratio f y (B k) s) (fun k y Δ _ hΔ _ => by
      obtain ⟨s, hs, -, hC, -⟩ := exists_isMinOn_quadModel_ball (gradient f y) (B k) hΔ.le
      obtain ⟨t, ht⟩ := exists_isCauchyStep (gradient f y) (B k) hΔ.le
      refine ⟨s, ⟨hs, t, ht, ?_⟩, trivial⟩
      rw [tr1Model_eq, tr1Model_eq]
      linarith [hC t ht]) trivial
  exact ⟨x, s, Δ, hx0, hε, hB, hrun⟩

/-- **Assumption m.HBa** of [cartis2022evaluation]. A sequence $(B_k)$ of continuous linear
operators on $\mathbb{R}^n$ satisfies m.HBa with constant $\kappa_B$ if $\kappa_B \ge 0$ and
$$\|B_k\| \le \kappa_B \quad \text{for all } k.$$

The norm is the operator norm, which is the spectral norm of the book's matrix $B_k$. -/
structure AssumptionMHBa (B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (κB : ℝ) : Prop where
  /-- The constant satisfies $\kappa_B \ge 0$. -/
  nonneg : 0 ≤ κB
  /-- Every model operator satisfies $\|B_k\| \le \kappa_B$. -/
  bound : ∀ k, ‖B k‖ ≤ κB

/-! ### The minimum gradient norm -/

/-- The smallest gradient norm along the first $k + 1$ iterates,
$\min_{0 \le i \le k} \|\nabla f(x_i)\|$. -/
noncomputable def gradMin (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : ℕ → EuclideanSpace ℝ (Fin n))
    (k : ℕ) : ℝ :=
  (range (k + 1)).inf' nonempty_range_add_one fun i => ‖gradient f (x i)‖

section GradMin

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {x : ℕ → EuclideanSpace ℝ (Fin n)} {k : ℕ}

/-- If $i \le k$, then $\min_{0 \le j \le k} \|\nabla f(x_j)\| \le \|\nabla f(x_i)\|$. -/
theorem gradMin_le {i : ℕ} (hi : i ≤ k) : gradMin f x k ≤ ‖gradient f (x i)‖ :=
  inf'_le _ (mem_range.2 (Nat.lt_succ_of_le hi))

/-- If $c \le \|\nabla f(x_i)\|$ for all $i \le k$, then
$c \le \min_{0 \le i \le k} \|\nabla f(x_i)\|$. -/
theorem le_gradMin {c : ℝ} (h : ∀ i ≤ k, c ≤ ‖gradient f (x i)‖) : c ≤ gradMin f x k :=
  le_inf' _ _ fun i hi => h i (Nat.lt_succ_iff.1 (mem_range.1 hi))

/-- The smallest gradient norm $\min_{0 \le i \le k} \|\nabla f(x_i)\|$ is nonnegative. -/
theorem gradMin_nonneg : 0 ≤ gradMin f x k :=
  le_gradMin fun _ _ => norm_nonneg _

/-- The smallest gradient norm does not increase with $k$: $\min_{i \le k + 1} \|\nabla f(x_i)\| \le
\min_{i \le k} \|\nabla f(x_i)\|$. -/
theorem gradMin_succ_le : gradMin f x (k + 1) ≤ gradMin f x k :=
  le_gradMin fun _ hi => gradMin_le (hi.trans k.le_succ)

/-- The smallest gradient norm satisfies $\min_{0 \le i \le k} \|\nabla f(x_i)\| \le \|\nabla
f(x_0)\|$. -/
theorem gradMin_le_zero : gradMin f x k ≤ ‖gradient f (x 0)‖ :=
  gradMin_le (Nat.zero_le k)

end GradMin

namespace algorithm_2_3_1

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {P : TR1Params} {ε : ℝ}
  {B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
  {x s : ℕ → EuclideanSpace ℝ (Fin n)} {Δ : ℕ → ℝ}

/-- In a TR1 run, if the termination test fails at every iteration $j < k$, then $\Delta_k > 0$. So
the radii are positive up to and including the termination index. -/
theorem delta_pos (h : algorithm_2_3_1 f P ε B x s Δ) {k : ℕ}
    (hk : ∀ j < k, ¬ ‖gradient f (x j)‖ ≤ ε) : 0 < Δ k :=
  h.run.delta_pos hk k le_rfl

end algorithm_2_3_1

/-! ### Lemmas 2.3.1–2.3.6 -/

section Lemmas

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {P : TR1Params} {ε L κB flow : ℝ}
  {B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
  {x s : ℕ → EuclideanSpace ℝ (Fin n)} {Δ : ℕ → ℝ}

/-- **Lemma 2.3.1** of [cartis2022evaluation]. Consider a TR1 run, and let $k$ be an iteration with
$\|\nabla f(x_j)\| > \epsilon$ for all $j < k$. Let $\Delta_{\min} > 0$ with
$\Delta_k \ge \Delta_{\min}$. Then (2.3.11) holds:
$$k \le |\mathcal{S}_k| \left( 1 + \frac{\log \gamma_3}{|\log \gamma_2|} \right) +
  \frac{|\log(\Delta_{\min}/\Delta_0)|}{|\log \gamma_2|},$$
where $\mathcal{S}_k = \{j \le k : \rho_j \ge \eta_1\}$ is the set of successful iterations up
to $k$.

The proof uses only the radius update (2.3.7). The set $\mathcal{S}_k$ is
`Optimization.successSet`. -/
theorem lemma_2_3_1 (h : algorithm_2_3_1 f P ε B x s Δ) {k : ℕ}
    (hk : ∀ j < k, ¬ ‖gradient f (x j)‖ ≤ ε) {Δmin : ℝ} (hmin : 0 < Δmin) (hΔ : Δmin ≤ Δ k) :
    (k : ℝ) ≤ (successSet (fun j => P.η₁ ≤ tr1Ratio f (x j) (B j) (s j)) k).card *
        (1 + Real.log P.γ₃ / |Real.log P.γ₂|) +
      |Real.log (Δmin / P.Δ₀)| / |Real.log P.γ₂| :=
  h.run.le_succ_count hk hmin hΔ

/-- **Lemma 2.3.2** of [cartis2022evaluation]. Let $f : \mathbb{R}^n \to \mathbb{R}$,
$x \in \mathbb{R}^n$, let $B$ be a continuous linear operator on $\mathbb{R}^n$, and let
$\Delta, t \in \mathbb{R}$. Assume that $t$ is a Cauchy step length for the radius $\Delta$:
$t \ge 0$, $t \|\nabla f(x)\| \le \Delta$, and $-t \nabla f(x)$ minimizes the model $m$ of
(2.3.1) along $-\nabla f(x)$ in the trust region. Then (2.3.12) holds:
$$m(0) - m(-t \nabla f(x)) \ge \frac12 \|\nabla f(x)\| \min\left( \frac{\|\nabla f(x)\|}{1 +
  \|B\|}, \Delta \right).$$

The operator $B$ need not be self-adjoint. The Cauchy step length is
`Optimization.IsCauchyStep`. -/
theorem lemma_2_3_2 (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n))
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) {Δ t : ℝ}
    (ht : IsCauchyStep (gradient f x) B Δ t) :
    1 / 2 * ‖gradient f x‖ * min (‖gradient f x‖ / (1 + ‖B‖)) Δ ≤
      tr1Model f x B 0 - tr1Model f x B (-(t • gradient f x)) := by
  rw [tr1Model_zero_sub]
  have := neg_quadModel_cauchy_ge ht
  linarith

/-- In a TR1 run, at every iteration $k$ before termination, the model decrease of the step
satisfies the Cauchy bound (2.3.12):
$$m_k(0) - m_k(s_k) \ge \frac12 \|\nabla f(x_k)\| \min\left( \frac{\|\nabla f(x_k)\|}{1 +
  \|B_k\|}, \Delta_k \right).$$
-/
theorem algorithm_2_3_1.cauchy_le_pred (h : algorithm_2_3_1 f P ε B x s Δ) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ ‖gradient f (x j)‖ ≤ ε) :
    1 / 2 * ‖gradient f (x k)‖ * min (‖gradient f (x k)‖ / (1 + ‖B k‖)) (Δ k) ≤
      tr1Model f (x k) (B k) 0 - tr1Model f (x k) (B k) (s k) := by
  obtain ⟨-, t, ht, hm⟩ := h.run.step k hk
  linarith [lemma_2_3_2 f (x k) (B k) ht]

/-- **Lemma 2.3.2** of [cartis2022evaluation], positivity of the predicted decrease. In a TR1 run,
let $k$ be an iteration with $\|\nabla f(x_j)\| > \epsilon$ for all $j \le k$. Then
$$m_k(0) - m_k(s_k) > 0,$$
so the denominator of the ratio (2.3.6) is positive. -/
theorem lemma_2_3_2_pred_pos (h : algorithm_2_3_1 f P ε B x s Δ) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ ‖gradient f (x j)‖ ≤ ε) :
    0 < tr1Model f (x k) (B k) 0 - tr1Model f (x k) (B k) (s k) := by
  have hg : 0 < ‖gradient f (x k)‖ := h.ε_pos.trans (not_le.1 (hk k le_rfl))
  have hΔ : 0 < Δ k := h.delta_pos fun j hj => hk j hj.le
  refine lt_of_lt_of_le ?_ (h.cauchy_le_pred hk)
  have : 0 < min (‖gradient f (x k)‖ / (1 + ‖B k‖)) (Δ k) := lt_min (by positivity) hΔ
  positivity

/-- One-iteration form of Lemma 2.3.3 of [cartis2022evaluation]. Assume f.gL with constant $L$. Let
$B$ be a continuous linear operator with $\|B\| \le \kappa_B$, let $\Delta > 0$,
$\nabla f(x) \neq 0$, $\eta \ge 0$ and $\Delta < (1 - \eta) \|\nabla f(x)\| / (2(L +
\kappa_B))$, and let $s$ be a TR1 step at $x$ with radius $\Delta$. Then the ratio (2.3.6)
satisfies $\rho \ge \eta$.

**Reading.** States the one-step ratio estimate with a free nonnegative threshold.
-/
theorem tr1Ratio_ge_of_tr1Step (hf : AssumptionGL f L) {x s : EuclideanSpace ℝ (Fin n)}
    {Bk : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)} {Δ η : ℝ}
    (hstep : tr1Step f Bk x Δ s) (hBk : ‖Bk‖ ≤ κB) (hΔ : 0 < Δ) (hg : 0 < ‖gradient f x‖)
    (hη : 0 ≤ η) (hΔk : Δ < (1 - η) * ‖gradient f x‖ / (2 * (L + κB))) :
    η ≤ tr1Ratio f x Bk s := by
  obtain ⟨hs, t, ht, hm⟩ := hstep
  have hsC : quadModel (gradient f x) Bk s ≤ quadModel (gradient f x) Bk (-(t • gradient f x)) := by
    rw [tr1Model_eq, tr1Model_eq] at hm; linarith
  rw [tr1Ratio, tr1Model_zero_sub]
  exact le_reductionRatio_trust_first_of_isCauchyStep convex_univ
    (fun y _ => hf.contDiff.contDiffAt) hf.iteratedFDerivLipschitzOn hf.one_le (mem_univ _)
    (mem_univ _) hBk ht hsC hs hΔ hg hη hΔk

/-- **Lemma 2.3.3** of [cartis2022evaluation]. Assume f.gL with constant $L$ and m.HBa with constant
$\kappa_B$, and consider a TR1 run. Let $k$ be an iteration with $\|\nabla f(x_j)\| > \epsilon$
for all $j \le k$, and assume (2.3.15):
$$\Delta_k < \frac{(1 - \eta_2) \|\nabla f(x_k)\|}{2(L + \kappa_B)}.$$
Then $\rho_k \ge \eta_2$, iteration $k$ is successful ($\rho_k \ge \eta_1$), and
$\Delta_{k+1} \ge \Delta_k$. -/
theorem lemma_2_3_3 (hf : AssumptionGL f L) (hB : AssumptionMHBa B κB)
    (h : algorithm_2_3_1 f P ε B x s Δ) {k : ℕ} (hk : ∀ j ≤ k, ¬ ‖gradient f (x j)‖ ≤ ε)
    (hΔk : Δ k < (1 - P.η₂) * ‖gradient f (x k)‖ / (2 * (L + κB))) :
    P.η₂ ≤ tr1Ratio f (x k) (B k) (s k) ∧ P.η₁ ≤ tr1Ratio f (x k) (B k) (s k) ∧
      Δ k ≤ Δ (k + 1) := by
  have hg : 0 < ‖gradient f (x k)‖ := h.ε_pos.trans (not_le.1 (hk k le_rfl))
  have hΔ : 0 < Δ k := h.delta_pos fun j hj => hk j hj.le
  have h2 : P.η₂ ≤ tr1Ratio f (x k) (B k) (s k) :=
    tr1Ratio_ge_of_tr1Step hf (h.run.step k hk) (hB.bound k) hΔ hg
      (P.η₁_pos.trans_le P.η₁_le_η₂).le hΔk
  exact ⟨h2, P.η₁_le_η₂.trans h2, (h.run.update hk).le_of_very_successful h2⟩

/-- The constant of the proof of Lemma 2.3.4,
$$\alpha = \frac{1 - \eta_2}{2(L + \kappa_B)} \min\left( 1, \frac{\Delta_0}{g_0} \right),$$
where $g_0$ stands for $\|\nabla f(x_0)\|$. Lean's division gives $\Delta_0 / 0 = 0$, so
$\alpha = 0$ when $g_0 = 0$.

**Reading.** The scalar coefficient matches when the initial gradient norm is positive and uses
total division otherwise.
-/
noncomputable def tr1Alpha (P : TR1Params) (L κB g₀ : ℝ) : ℝ :=
  (1 - P.η₂) / (2 * (L + κB)) * min 1 (P.Δ₀ / g₀)

section Alpha

variable {P : TR1Params} {L κB g₀ m : ℝ}

private theorem coef_nonneg (hL : 1 ≤ L) (hκ : 0 ≤ κB) : 0 ≤ (1 - P.η₂) / (2 * (L + κB)) :=
  div_nonneg (sub_nonneg.2 P.η₂_lt_one.le) (by linarith)

private theorem coef_le_one (hL : 1 ≤ L) (hκ : 0 ≤ κB) : (1 - P.η₂) / (2 * (L + κB)) ≤ 1 := by
  rw [div_le_one (by linarith)]
  linarith [P.η₁_pos, P.η₁_le_η₂]

private theorem min_nonneg (hg₀ : 0 ≤ g₀) : 0 ≤ min 1 (P.Δ₀ / g₀) :=
  le_min zero_le_one (div_nonneg P.Δ₀_pos.le hg₀)

/-- If $L \ge 1$, $\kappa_B \ge 0$ and $g_0 \ge 0$, then $\alpha \ge 0$. -/
theorem tr1Alpha_nonneg (hL : 1 ≤ L) (hκ : 0 ≤ κB) (hg₀ : 0 ≤ g₀) : 0 ≤ tr1Alpha P L κB g₀ :=
  mul_nonneg (coef_nonneg hL hκ) (min_nonneg hg₀)

/-- If $L \ge 1$, $\kappa_B \ge 0$ and $g_0 > 0$, then $\alpha > 0$. -/
theorem tr1Alpha_pos (hL : 1 ≤ L) (hκ : 0 ≤ κB) (hg₀ : 0 < g₀) : 0 < tr1Alpha P L κB g₀ :=
  mul_pos (div_pos (sub_pos.2 P.η₂_lt_one) (by linarith))
    (lt_min zero_lt_one (div_pos P.Δ₀_pos hg₀))

/-- If $L \ge 1$, $\kappa_B \ge 0$ and $0 \le m \le m'$, then $\alpha m \le (1 - \eta_2) m' / (2(L +
\kappa_B))$. -/
theorem tr1Alpha_mul_le (hL : 1 ≤ L) (hκ : 0 ≤ κB) (hm : 0 ≤ m) {m' : ℝ}
    (hmm' : m ≤ m') : tr1Alpha P L κB g₀ * m ≤ (1 - P.η₂) * m' / (2 * (L + κB)) := by
  rw [tr1Alpha, mul_div_right_comm]
  have h1 : min 1 (P.Δ₀ / g₀) * m ≤ m' := by
    calc min 1 (P.Δ₀ / g₀) * m ≤ 1 * m := mul_le_mul_of_nonneg_right (min_le_left _ _) hm
      _ ≤ m' := by rw [one_mul]; exact hmm'
  rw [mul_assoc]
  calc (1 - P.η₂) / (2 * (L + κB)) * (min 1 (P.Δ₀ / g₀) * m)
      ≤ (1 - P.η₂) / (2 * (L + κB)) * m' := mul_le_mul_of_nonneg_left h1 (coef_nonneg hL hκ)
    _ = (1 - P.η₂) / (2 * (L + κB)) * m' := rfl

/-- If $L \ge 1$, $\kappa_B \ge 0$ and $0 \le m \le g_0$, then $\alpha m \le \Delta_0$. -/
theorem tr1Alpha_mul_le_delta (hL : 1 ≤ L) (hκ : 0 ≤ κB) (hm : 0 ≤ m) (hmg : m ≤ g₀) :
    tr1Alpha P L κB g₀ * m ≤ P.Δ₀ := by
  have hg₀ : 0 ≤ g₀ := hm.trans hmg
  rcases hg₀.eq_or_lt with h0 | h0
  · have : m = 0 := le_antisymm (h0 ▸ hmg) hm
    rw [this, mul_zero]; exact P.Δ₀_pos.le
  have h1 : min 1 (P.Δ₀ / g₀) * m ≤ P.Δ₀ :=
    calc min 1 (P.Δ₀ / g₀) * m ≤ P.Δ₀ / g₀ * g₀ :=
          mul_le_mul (min_le_right _ _) hmg hm (div_nonneg P.Δ₀_pos.le h0.le)
      _ = P.Δ₀ := div_mul_cancel₀ _ h0.ne'
  rw [tr1Alpha, mul_assoc]
  calc (1 - P.η₂) / (2 * (L + κB)) * (min 1 (P.Δ₀ / g₀) * m) ≤ 1 * P.Δ₀ :=
        mul_le_mul (coef_le_one hL hκ) h1 (mul_nonneg (min_nonneg h0.le) hm) zero_le_one
    _ = P.Δ₀ := one_mul _

end Alpha

/-- Under f.gL and m.HBa, an iteration $j$ before termination with $\Delta_j < \alpha \min_{i \le j}
\|\nabla f(x_i)\|$ has $\rho_j \ge \eta_2$. -/
private theorem force (hf : AssumptionGL f L) (hB : AssumptionMHBa B κB)
    (h : algorithm_2_3_1 f P ε B x s Δ) {j : ℕ} (hj : ∀ i ≤ j, ¬ ‖gradient f (x i)‖ ≤ ε)
    (hΔ : Δ j < tr1Alpha P L κB ‖gradient f (x 0)‖ * gradMin f x j) :
    P.η₂ ≤ tr1Ratio f (x j) (B j) (s j) :=
  (lemma_2_3_3 hf hB h hj (hΔ.trans_le (tr1Alpha_mul_le hf.one_le hB.nonneg
    gradMin_nonneg (gradMin_le le_rfl)))).1

/-- **Lemma 2.3.4** of [cartis2022evaluation]. Assume f.gL with constant $L$ and m.HBa with constant
$\kappa_B$, and consider a TR1 run. Let $k$ be an iteration with $\|\nabla f(x_j)\| > \epsilon$
for all $j < k$. Then (2.3.17) holds:
$$\Delta_k \ge \gamma_1 \frac{1 - \eta_2}{2(L + \kappa_B)} \min\left( 1,
  \frac{\Delta_0}{\|\nabla f(x_0)\|} \right) \min_{0 \le i \le k} \|\nabla f(x_i)\|.$$

**Reading.** The bound is stated for every iteration $k$ up to and including the termination
index, where the run is defined.

The constant is $\gamma_1$ times `CartisGouldToint.Chapter02.tr1Alpha`, and the minimum is
`CartisGouldToint.Chapter02.gradMin`. -/
theorem lemma_2_3_4 (hf : AssumptionGL f L) (hB : AssumptionMHBa B κB)
    (h : algorithm_2_3_1 f P ε B x s Δ) {k : ℕ} (hk : ∀ j < k, ¬ ‖gradient f (x j)‖ ≤ ε) :
    P.γ₁ * tr1Alpha P L κB ‖gradient f (x 0)‖ * gradMin f x k ≤ Δ k := by
  set α' := tr1Alpha P L κB ‖gradient f (x 0)‖
  have hα' : 0 ≤ α' := tr1Alpha_nonneg hf.one_le hB.nonneg (norm_nonneg _)
  have hmin := h.run.delta_ge (θ := fun j => α' * gradMin f x j) hk
    (fun j _ => mul_le_mul_of_nonneg_left gradMin_succ_le hα')
    (fun j hj hΔ => force hf hB h (fun i hi => hk i (hi.trans_lt hj)) hΔ) k le_rfl
  have hle : P.γ₁ * (α' * gradMin f x k) ≤ P.Δ₀ :=
    (mul_le_of_le_one_left (mul_nonneg hα' gradMin_nonneg) P.γ₁_le_one).trans
      (tr1Alpha_mul_le_delta hf.one_le hB.nonneg gradMin_nonneg gradMin_le_zero)
  rw [min_eq_right hle] at hmin
  rw [mul_assoc]; exact hmin

/-- Lemma 2.3.4 of [cartis2022evaluation] for the next radius. Assume f.gL and m.HBa, and consider a
TR1 run with $\|\nabla f(x_j)\| > \epsilon$ for all $j \le k$. Then $\Delta_{k+1} \ge \gamma_1
\alpha \min_{0 \le i \le k} \|\nabla f(x_i)\|$, where $\alpha$ is
`CartisGouldToint.Chapter02.tr1Alpha`.

**Reading.** Combines the same coefficient with the previous gradient minimum to bound the next
radius.
-/
theorem lemma_2_3_4_succ (hf : AssumptionGL f L) (hB : AssumptionMHBa B κB)
    (h : algorithm_2_3_1 f P ε B x s Δ) {k : ℕ} (hk : ∀ j ≤ k, ¬ ‖gradient f (x j)‖ ≤ ε) :
    P.γ₁ * tr1Alpha P L κB ‖gradient f (x 0)‖ * gradMin f x k ≤ Δ (k + 1) := by
  set α' := tr1Alpha P L κB ‖gradient f (x 0)‖
  have hα' : 0 ≤ α' := tr1Alpha_nonneg hf.one_le hB.nonneg (norm_nonneg _)
  have hk' : ∀ j < k + 1, ¬ ‖gradient f (x j)‖ ≤ ε := fun j hj => hk j (Nat.lt_succ_iff.1 hj)
  have hmin := h.run.delta_succ_ge (θ := fun j => α' * gradMin f x j) hk'
    (fun j _ => mul_le_mul_of_nonneg_left gradMin_succ_le hα')
    (fun j hj hΔ => force hf hB h (fun i hi => hk' i (hi.trans_lt hj)) hΔ) k k.lt_succ_self
  have hle : P.γ₁ * (α' * gradMin f x k) ≤ P.Δ₀ :=
    (mul_le_of_le_one_left (mul_nonneg hα' gradMin_nonneg) P.γ₁_le_one).trans
      (tr1Alpha_mul_le_delta hf.one_le hB.nonneg gradMin_nonneg gradMin_le_zero)
  rw [min_eq_right hle] at hmin
  rw [mul_assoc]; exact hmin

/-- The constant of (2.3.20) of [cartis2022evaluation],
$$\kappa_{\mathrm{decr}} = \frac12 \min\left( \frac{1}{1 + \kappa_B}, \gamma_1 \frac{1 -
  \eta_2}{2(L + \kappa_B)} \min\left( 1, \frac{\Delta_0}{g_0} \right) \right),$$
where $g_0$ stands for $\|\nabla f(x_0)\|$.

**Reading.** Uses the totalized radius coefficient in the model-decrease constant.
-/
noncomputable def kappaDecrTR1 (P : TR1Params) (L κB g₀ : ℝ) : ℝ :=
  1 / 2 * min (1 / (1 + κB)) (P.γ₁ * tr1Alpha P L κB g₀)

/-- **Lemma 2.3.5** of [cartis2022evaluation]. Assume f.gL with constant $L$ and m.HBa with constant
$\kappa_B$, and consider a TR1 run. Let $k$ be an iteration with $\|\nabla f(x_j)\| > \epsilon$
for all $j \le k$. Then (2.3.19) holds:
$$m_k(0) - m_k(s_k) \ge \kappa_{\mathrm{decr}} \|\nabla f(x_k)\| \min_{0 \le i \le k} \|\nabla
  f(x_i)\|,$$
with the constant $\kappa_{\mathrm{decr}}$ of (2.3.20).

**Typo.** The source writes the model decrease as $m_k(x_k) - m_k(x_k + s_k)$. The model $m_k$
is a function of the step, so the decrease is $m_k(0) - m_k(s_k)$.

The constant is `CartisGouldToint.Chapter02.kappaDecrTR1` with $g_0 = \|\nabla f(x_0)\|$. -/
theorem lemma_2_3_5 (hf : AssumptionGL f L) (hB : AssumptionMHBa B κB)
    (h : algorithm_2_3_1 f P ε B x s Δ) {k : ℕ} (hk : ∀ j ≤ k, ¬ ‖gradient f (x j)‖ ≤ ε) :
    kappaDecrTR1 P L κB ‖gradient f (x 0)‖ * ‖gradient f (x k)‖ * gradMin f x k ≤
      tr1Model f (x k) (B k) 0 - tr1Model f (x k) (B k) (s k) := by
  set g := ‖gradient f (x k)‖
  set m := gradMin f x k
  set c := min (1 / (1 + κB)) (P.γ₁ * tr1Alpha P L κB ‖gradient f (x 0)‖)
  have hm : 0 ≤ m := gradMin_nonneg
  have hmg : m ≤ g := gradMin_le le_rfl
  have hκ := hB.nonneg
  have h1 : m * c ≤ g / (1 + ‖B k‖) := by
    calc m * c ≤ m * (1 / (1 + κB)) := mul_le_mul_of_nonneg_left (min_le_left _ _) hm
      _ = m / (1 + κB) := by ring
      _ ≤ g / (1 + ‖B k‖) := div_le_div₀ (hm.trans hmg) hmg (by positivity)
          (by linarith [hB.bound k])
  have h2 : m * c ≤ Δ k := by
    calc m * c ≤ m * (P.γ₁ * tr1Alpha P L κB ‖gradient f (x 0)‖) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) hm
      _ = P.γ₁ * tr1Alpha P L κB ‖gradient f (x 0)‖ * m := by ring
      _ ≤ Δ k := lemma_2_3_4 hf hB h fun j hj => hk j hj.le
  have h3 := h.cauchy_le_pred hk
  have h4 : 1 / 2 * g * (m * c) ≤ 1 / 2 * g * min (g / (1 + ‖B k‖)) (Δ k) :=
    mul_le_mul_of_nonneg_left (le_min h1 h2) (by positivity)
  calc kappaDecrTR1 P L κB ‖gradient f (x 0)‖ * g * m = 1 / 2 * g * (m * c) := by
        rw [kappaDecrTR1]; ring
    _ ≤ _ := h4.trans h3

/-- The constant of (2.3.21) of [cartis2022evaluation],
$$\kappa^S_{\mathrm{TR1}} = \frac{4(L + \kappa_B)}{\gamma_1 \eta_1 (1 - \eta_2)} \max\left( 1,
  \frac{g_0}{\Delta_0} \right),$$
where $g_0$ stands for $\|\nabla f(x_0)\|$. -/
noncomputable def kappaSTR1 (P : TR1Params) (L κB g₀ : ℝ) : ℝ :=
  4 * (L + κB) / (P.γ₁ * P.η₁ * (1 - P.η₂)) * max 1 (g₀ / P.Δ₀)

/-- If $L \ge 1$ and $\kappa_B \ge 0$, then $\kappa^S_{\mathrm{TR1}} \ge 0$. -/
theorem kappaSTR1_nonneg {P : TR1Params} {L κB g₀ : ℝ} (hL : 1 ≤ L) (hκ : 0 ≤ κB) :
    0 ≤ kappaSTR1 P L κB g₀ := by
  have := P.γ₁_pos; have := P.η₁_pos; have := sub_pos.2 P.η₂_lt_one
  unfold kappaSTR1
  have : 0 ≤ max 1 (g₀ / P.Δ₀) := zero_le_one.trans (le_max_left _ _)
  have : 0 ≤ L + κB := by linarith
  positivity

/-- If $L \ge 1$, $\kappa_B \ge 0$ and $g_0 > 0$, then $\eta_1 \kappa_{\mathrm{decr}}
\kappa^S_{\mathrm{TR1}} = 1$, that is, $\kappa^S_{\mathrm{TR1}} = (\eta_1
\kappa_{\mathrm{decr}})^{-1}$. This is the last step of the proof of Lemma 2.3.6. -/
theorem eta_mul_kappaDecrTR1 {P : TR1Params} {L κB g₀ : ℝ} (hL : 1 ≤ L) (hκ : 0 ≤ κB)
    (hg₀ : 0 < g₀) : P.η₁ * kappaDecrTR1 P L κB g₀ * kappaSTR1 P L κB g₀ = 1 := by
  have hγ := P.γ₁_pos; have hη := P.η₁_pos; have h1η := sub_pos.2 P.η₂_lt_one
  have hLκ : 0 < L + κB := by linarith
  have hmin : P.γ₁ * tr1Alpha P L κB g₀ ≤ 1 / (1 + κB) := by
    rw [tr1Alpha, le_div_iff₀ (by linarith)]
    have hc := coef_le_one (P := P) hL hκ
    have hm : min 1 (P.Δ₀ / g₀) ≤ 1 := min_le_left _ _
    have hm0 : 0 ≤ min 1 (P.Δ₀ / g₀) := min_nonneg hg₀.le
    have : (1 - P.η₂) / (2 * (L + κB)) * (1 + κB) ≤ 1 := by
      rw [div_mul_eq_mul_div, div_le_one (by linarith)]
      nlinarith [P.η₁_le_η₂]
    have hcn := coef_nonneg (P := P) hL hκ
    calc P.γ₁ * ((1 - P.η₂) / (2 * (L + κB)) * min 1 (P.Δ₀ / g₀)) * (1 + κB)
        = P.γ₁ * min 1 (P.Δ₀ / g₀) * ((1 - P.η₂) / (2 * (L + κB)) * (1 + κB)) := by ring
      _ ≤ 1 * 1 * 1 := by
        gcongr
        · exact P.γ₁_le_one
      _ = 1 := by norm_num
  have hmm : min 1 (P.Δ₀ / g₀) * max 1 (g₀ / P.Δ₀) = 1 := by
    have ha : 0 < P.Δ₀ / g₀ := div_pos P.Δ₀_pos hg₀
    have hinv : g₀ / P.Δ₀ = (P.Δ₀ / g₀)⁻¹ := (inv_div _ _).symm
    rw [hinv]
    rcases le_total 1 (P.Δ₀ / g₀) with h | h
    · rw [min_eq_left h, max_eq_left (inv_le_one_of_one_le₀ h), one_mul]
    · rw [min_eq_right h, max_eq_right ((one_le_inv₀ ha).2 h), mul_inv_cancel₀ ha.ne']
  rw [kappaDecrTR1, min_eq_right hmin, kappaSTR1, tr1Alpha]
  have : P.η₁ * (1 / 2 * (P.γ₁ * ((1 - P.η₂) / (2 * (L + κB)) * min 1 (P.Δ₀ / g₀)))) *
      (4 * (L + κB) / (P.γ₁ * P.η₁ * (1 - P.η₂)) * max 1 (g₀ / P.Δ₀)) =
      min 1 (P.Δ₀ / g₀) * max 1 (g₀ / P.Δ₀) := by
    field_simp
    ring
  rw [this, hmm]

/-- **Lemma 2.3.6** of [cartis2022evaluation]. Assume f.Bb with lower bound $f_{\mathrm{low}}$, f.gL
with constant $L$ and m.HBa with constant $\kappa_B$, and consider a TR1 run. Let $k$ be an
iteration with $\|\nabla f(x_j)\| > \epsilon$ for all $j \le k$. Then the number of successful
iterations up to $k$ satisfies (2.3.21):
$$|\mathcal{S}_k| \le \kappa^S_{\mathrm{TR1}} \frac{f(x_0) - f_{\mathrm{low}}}{\epsilon^2}.$$

The constant is `CartisGouldToint.Chapter02.kappaSTR1` with $g_0 = \|\nabla f(x_0)\|$, and
$\mathcal{S}_k$ is `Optimization.successSet`. -/
theorem lemma_2_3_6 (hb : AssumptionBb f flow) (hf : AssumptionGL f L)
    (hB : AssumptionMHBa B κB) (h : algorithm_2_3_1 f P ε B x s Δ) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ ‖gradient f (x j)‖ ≤ ε) :
    ((successSet (fun j => P.η₁ ≤ tr1Ratio f (x j) (B j) (s j)) k).card : ℝ) ≤
      kappaSTR1 P L κB ‖gradient f (x 0)‖ * (f (x 0) - flow) / ε ^ 2 := by
  set g₀ := ‖gradient f (x 0)‖
  have hε := h.ε_pos
  have hg₀ : 0 < g₀ := hε.trans (not_le.1 (hk 0 (Nat.zero_le k)))
  set κd := kappaDecrTR1 P L κB g₀
  have hκd : 0 ≤ κd := by
    have := tr1Alpha_nonneg (P := P) hf.one_le hB.nonneg hg₀.le
    have := hB.nonneg; have := P.γ₁_pos
    unfold κd kappaDecrTR1
    have : 0 ≤ min (1 / (1 + κB)) (P.γ₁ * tr1Alpha P L κB g₀) := le_min (by positivity)
      (by positivity)
    positivity
  have hdec : ∀ j ≤ k, P.η₁ ≤ tr1Ratio f (x j) (B j) (s j) →
      P.η₁ * κd * ε ^ 2 ≤ f (x j) - f (x (j + 1)) := by
    intro j hj hs
    have hj' : ∀ i ≤ j, ¬ ‖gradient f (x i)‖ ≤ ε := fun i hi => hk i (hi.trans hj)
    have hpred := lemma_2_3_2_pred_pos h hj'
    have hsub := (h.run.sub_ge_of_succ (f := f)
      (pred := fun j => tr1Model f (x j) (B j) 0 - tr1Model f (x j) (B j) (s j)) hj' rfl hpred
      hs).2
    have h5 := lemma_2_3_5 hf hB h hj'
    have hgj : ε ≤ ‖gradient f (x j)‖ := (not_le.1 (hj' j le_rfl)).le
    have hmj : ε ≤ gradMin f x j := le_gradMin fun i hi => (not_le.1 (hj' i hi)).le
    have : κd * ε ^ 2 ≤ κd * ‖gradient f (x j)‖ * gradMin f x j := by
      rw [mul_assoc, sq]
      exact mul_le_mul_of_nonneg_left (mul_le_mul hgj hmj hε.le (hε.le.trans hgj)) hκd
    have := mul_le_mul_of_nonneg_left (this.trans h5) P.η₁_pos.le
    linarith
  have hcard := card_successSet_mul_le_of_decrease (φ := fun j => f (x j))
    (fun j hj hs => by rw [h.run.eq_of_not_succ (fun i hi => hk i (hi.trans hj)) (not_le.1 hs)])
    hdec (hb (x (k + 1)))
  have hid := eta_mul_kappaDecrTR1 (P := P) hf.one_le hB.nonneg hg₀
  have hκS : 0 < kappaSTR1 P L κB g₀ := by
    rcases (kappaSTR1_nonneg (P := P) (g₀ := g₀) hf.one_le hB.nonneg).eq_or_lt with h0 | h0
    · rw [← h0, mul_zero] at hid; exact absurd hid zero_ne_one
    · exact h0
  rw [le_div_iff₀ (pow_pos hε 2)]
  have : P.η₁ * κd = 1 / kappaSTR1 P L κB g₀ := by
    rw [eq_div_iff hκS.ne']; exact hid
  rw [this] at hcard
  have := mul_le_mul_of_nonneg_left hcard hκS.le
  field_simp at this
  linarith

/-- The constant of (2.3.23) of [cartis2022evaluation],
$$\kappa^C_{\mathrm{TR1}} = \frac{\left| \log\left( \frac{\gamma_1 (1 - \eta_2)}{2 \Delta_0 (L +
  \kappa_B)} \min\left( 1, \frac{\Delta_0}{g_0} \right) \right) \right|}{|\log \gamma_2|} + 1,$$
where $g_0$ stands for $\|\nabla f(x_0)\|$.

**Reading.** Totalized quotient and logarithm define the constant even at zero initial gradient.
-/
noncomputable def kappaCTR1 (P : TR1Params) (L κB g₀ : ℝ) : ℝ :=
  |Real.log (P.γ₁ * (1 - P.η₂) / (2 * P.Δ₀ * (L + κB)) * min 1 (P.Δ₀ / g₀))| /
    |Real.log P.γ₂| + 1

/-- The constant $\kappa^C_{\mathrm{TR1}}$ equals $|\log(\gamma_1 \alpha / \Delta_0)| / |\log
\gamma_2| + 1$, where $\alpha$ is `CartisGouldToint.Chapter02.tr1Alpha`. -/
theorem kappaCTR1_eq (P : TR1Params) (L κB g₀ : ℝ) :
    kappaCTR1 P L κB g₀ =
      |Real.log (P.γ₁ * tr1Alpha P L κB g₀ / P.Δ₀)| / |Real.log P.γ₂| + 1 := by
  have := P.Δ₀_pos
  rw [kappaCTR1, tr1Alpha]
  congr 4
  field_simp

/-- **Theorem 2.3.7** of [cartis2022evaluation]. Assume f.Bb with lower bound $f_{\mathrm{low}}$,
f.gL with constant $L$ and m.HBa with constant $\kappa_B$, and consider a TR1 run. Then the run
terminates: there is a first iteration $k_\epsilon$ with
$\|\nabla f(x_{k_\epsilon})\| \le \epsilon$. Up to termination the method uses at most
$$\kappa^A \frac{f(x_0) - f_{\mathrm{low}}}{\epsilon^2} + \kappa^B |\log \epsilon| + \kappa^C$$
evaluations of $f$ and at most
$$\kappa^S \frac{f(x_0) - f_{\mathrm{low}}}{\epsilon^2} + 1$$
evaluations of $\nabla f$. Here $\kappa^S = \kappa^S_{\mathrm{TR1}}$ is the constant of
(2.3.21), $\kappa^A = \kappa^S (1 + \log \gamma_3 / |\log \gamma_2|)$ and
$\kappa^B = 1/|\log \gamma_2|$ are the constants of (2.3.22), and
$\kappa^C = \kappa^C_{\mathrm{TR1}}$ is the constant of (2.3.23).

The number of evaluations of $f$ is `Optimization.funEvalCount`, which is $k_\epsilon + 1$. The
number of evaluations of $\nabla f$ is `Optimization.derivEvalCount`: one at $x_0$ and one after
each successful iteration before $k_\epsilon$. The constants are evaluated at
$g_0 = \|\nabla f(x_0)\|$. -/
theorem theorem_2_3_7 (hb : AssumptionBb f flow) (hf : AssumptionGL f L)
    (hB : AssumptionMHBa B κB) (h : algorithm_2_3_1 f P ε B x s Δ) :
    ∃ kε, IsFirstHit (fun k => ‖gradient f (x k)‖ ≤ ε) kε ∧
      (funEvalCount kε : ℝ) ≤
        kappaSTR1 P L κB ‖gradient f (x 0)‖ * (1 + Real.log P.γ₃ / |Real.log P.γ₂|) *
            (f (x 0) - flow) / ε ^ 2 +
          1 / |Real.log P.γ₂| * |Real.log ε| + kappaCTR1 P L κB ‖gradient f (x 0)‖ ∧
      (derivEvalCount (fun k => P.η₁ ≤ tr1Ratio f (x k) (B k) (s k)) kε : ℝ) ≤
        kappaSTR1 P L κB ‖gradient f (x 0)‖ * (f (x 0) - flow) / ε ^ 2 + 1 := by
  set g₀ := ‖gradient f (x 0)‖
  set κS := kappaSTR1 P L κB g₀
  set A := 1 + Real.log P.γ₃ / |Real.log P.γ₂|
  set N := κS * (f (x 0) - flow) / ε ^ 2
  set c := |Real.log (P.γ₁ * tr1Alpha P L κB g₀ / P.Δ₀)|
  have hε := h.ε_pos
  have hlog2 : 0 < |Real.log P.γ₂| :=
    abs_pos.2 (Real.log_neg P.γ₂_pos P.γ₂_lt_one).ne
  have hA : 0 ≤ A := by
    have := Real.log_nonneg P.one_le_γ₃; positivity
  have hN : 0 ≤ N := by
    have := kappaSTR1_nonneg (P := P) (g₀ := g₀) hf.one_le hB.nonneg
    have := sub_nonneg.2 (hb (x 0)); positivity
  have hBnn : 0 ≤ 1 / |Real.log P.γ₂| * |Real.log ε| + c / |Real.log P.γ₂| := by positivity
  have hcount : ∀ k, (∀ j ≤ k, ¬ ‖gradient f (x j)‖ ≤ ε) →
      (k + 1 : ℝ) ≤ A * (successSet (fun k => P.η₁ ≤ tr1Ratio f (x k) (B k) (s k)) k).card +
        (1 / |Real.log P.γ₂| * |Real.log ε| + c / |Real.log P.γ₂|) := by
    -- the radius stays above `Δ_min = γ₁ α ε`
    intro k hk
    have hg₀ : 0 < g₀ := hε.trans (not_le.1 (hk 0 (Nat.zero_le k)))
    have hα := tr1Alpha_pos (P := P) (κB := κB) hf.one_le hB.nonneg hg₀
    have hγα : 0 < P.γ₁ * tr1Alpha P L κB g₀ := mul_pos P.γ₁_pos hα
    have hΔ : P.γ₁ * tr1Alpha P L κB g₀ * ε ≤ Δ (k + 1) :=
      (mul_le_mul_of_nonneg_left (le_gradMin fun i hi => (not_le.1 (hk i hi)).le)
        hγα.le).trans (lemma_2_3_4_succ hf hB h hk)
    have hcount := h.run.succ_count hk (mul_pos hγα hε) hΔ
    have hlog : |Real.log (P.γ₁ * tr1Alpha P L κB g₀ * ε / P.Δ₀)| ≤ c + |Real.log ε| := by
      have : P.γ₁ * tr1Alpha P L κB g₀ * ε / P.Δ₀ =
          P.γ₁ * tr1Alpha P L κB g₀ / P.Δ₀ * ε := by ring
      rw [this, Real.log_mul (div_pos hγα P.Δ₀_pos).ne' hε.ne']
      exact abs_add_le _ _
    have : |Real.log (P.γ₁ * tr1Alpha P L κB g₀ * ε / P.Δ₀)| / |Real.log P.γ₂| ≤
        1 / |Real.log P.γ₂| * |Real.log ε| + c / |Real.log P.γ₂| := by
      rw [div_le_iff₀ hlog2]
      field_simp
      linarith
    linarith
  obtain ⟨kε, hk, hF, hD⟩ := exists_isFirstHit_evalCount_le_of_counting hA hN (by positivity)
    hcount fun k hk => lemma_2_3_6 hb hf hB h hk
  refine ⟨kε, hk, ?_, hD⟩
  rw [kappaCTR1_eq]
  have : A * N = κS * A * (f (x 0) - flow) / ε ^ 2 := by ring
  linarith

end Lemmas

/-! ### Theorem 2.3.8 -/

/-- **Theorem 2.3.8** of [cartis2022evaluation] (sharpness of TR1). For all TR1 constants there are
$L \ge 1$, $f_{\mathrm{low}}$ and $\kappa_B \ge 0$ with the following property. Let
$\epsilon \in (0, 1]$ be such that $k_\epsilon = \epsilon^{-2}$ is an integer. Then there are a
function $f : \mathbb{R}^1 \to \mathbb{R}$ that satisfies f.Bb with $f_{\mathrm{low}}$ and f.gL
with $L$, and a TR1 run from $x_0 = 0$ whose model operators satisfy m.HBa with $\kappa_B$, such
that:

* $\rho_k = 2$ for all $k < k_\epsilon$, so every iteration is very successful;
* the run terminates exactly at iteration $k_\epsilon$;
* the run uses $k_\epsilon + 1$ evaluations of $f$ and $k_\epsilon + 1$ evaluations of
  $\nabla f$.

**Correction.** The discussion before the theorem uses $B_k = 2t^{-1}$. With this choice the
Cauchy step is half the step that the example takes, and the Cauchy condition (2.3.4) fails. The
example here uses $B_k = t^{-1} I$ with $t = \Delta_0/2$ and the constant radius
$\Delta_k = \Delta_0$. Its steps are the Cauchy steps $-t \nabla f(x_k)$, and then $\rho_k = 2$,
not $1$.

The condition that $\epsilon^{-2}$ is an integer is stated as $k_\epsilon \epsilon^2 = 1$ for a
natural number $k_\epsilon$. -/
theorem theorem_2_3_8 (P : TR1Params) :
    ∃ L flow κB : ℝ, 1 ≤ L ∧ 0 ≤ κB ∧ ∀ (ε : ℝ) (kε : ℕ), 0 < ε → ε ≤ 1 →
      (kε : ℝ) * ε ^ 2 = 1 →
      ∃ f : EuclideanSpace ℝ (Fin 1) → ℝ, AssumptionBb f flow ∧ AssumptionGL f L ∧
        ∃ (B : ℕ → EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1))
          (x s : ℕ → EuclideanSpace ℝ (Fin 1)) (Δ : ℕ → ℝ),
          x 0 = 0 ∧ AssumptionMHBa B κB ∧ algorithm_2_3_1 f P ε B x s Δ ∧
          (∀ k < kε, tr1Ratio f (x k) (B k) (s k) = 2) ∧
          IsFirstHit (fun k => ‖gradient f (x k)‖ ≤ ε) kε ∧
          funEvalCount kε = kε + 1 ∧
          derivEvalCount (fun k => P.η₁ ≤ tr1Ratio f (x k) (B k) (s k)) kε = kε + 1 := by
  set t := P.Δ₀ / 2
  have ht : 0 < t := half_pos P.Δ₀_pos
  obtain ⟨L, flow, hL, H⟩ := exists_slow_example ht
  refine ⟨L, flow, t⁻¹, hL, (inv_pos.2 ht).le, fun ε kε hε hε1 hkε => ?_⟩
  obtain ⟨f, hb, hgl, hfk⟩ := H ε kε hε hε1 hkε
  set x : ℕ → EuclideanSpace ℝ (Fin 1) := fun k => slowX t ε kε k • e₀
  set Bop : EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1) :=
    t⁻¹ • ContinuousLinearMap.id ℝ _
  set s : ℕ → EuclideanSpace ℝ (Fin 1) := fun k => -(t • gradient f (x k))
  have hhit : IsFirstHit (fun k => ‖gradient f (x k)‖ ≤ ε) kε :=
    isFirstHit_slow hε (fun _ _ => rfl) fun k hk => (hfk k hk).2
  have hbefore : ∀ k, (∀ j ≤ k, ¬ ‖gradient f (x j)‖ ≤ ε) → k < kε := fun k hk =>
    not_le.1 fun hle => hk kε hle hhit.test
  have hBop : ∀ u, Bop u = t⁻¹ • u := fun u => rfl
  have hq : ∀ (g : EuclideanSpace ℝ (Fin 1)) (τ : ℝ),
      quadModel g Bop (-(τ • g)) = -τ * ‖g‖ ^ 2 + τ ^ 2 / (2 * t) * ‖g‖ ^ 2 := by
    intro g τ
    rw [quadModel_neg_smul, hBop, inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  -- data at iteration `k < k_ε`
  have hg : ∀ k ≤ kε, ‖gradient f (x k)‖ = ε + slowOmega ε kε k := fun k hk => by
    simp only [x]
    rw [(hfk k hk).2, norm_smul, norm_e₀, mul_one, norm_neg, Real.norm_eq_abs, abs_of_nonneg]
    have : (k : ℝ) ≤ kε := by exact_mod_cast hk
    have : 0 ≤ slowOmega ε kε k := by rw [slowOmega_def]; positivity
    linarith
  have hω : ∀ k ≤ kε, slowOmega ε kε k ≤ ε := fun k hk => by
    have hk' : (k : ℝ) ≤ kε := by exact_mod_cast hk
    have hkε0 : (0 : ℝ) < kε := by
      rcases Nat.eq_zero_or_pos kε with h0 | h0
      · rw [h0] at hkε; norm_num at hkε
      · exact_mod_cast h0
    rw [slowOmega_def]
    rw [div_le_iff₀ hkε0]
    nlinarith
  have hstep : ∀ k < kε, x k + s k = x (k + 1) := fun k hk => by
    simp only [x, s]
    rw [(hfk k hk.le).2, slowX_succ]
    module
  have hpred : ∀ k < kε, tr1Model f (x k) Bop 0 - tr1Model f (x k) Bop (s k) =
      t / 2 * ‖gradient f (x k)‖ ^ 2 := fun k _ => by
    rw [tr1Model_zero_sub, hq]; field_simp; ring
  have hratio : ∀ k < kε, tr1Ratio f (x k) Bop (s k) = 2 := fun k hk => by
    have hgk : 0 < ‖gradient f (x k)‖ := by rw [hg k hk.le]; linarith [slowOmega_pos hε hk]
    have hfx : ∀ j ≤ kε, f (x j) = slowF t ε kε j := fun j hj => (hfk j hj).1
    rw [tr1Ratio, hpred k hk, reductionRatio_def, hstep k hk, hfx k hk.le, hfx (k + 1) hk,
      slowF_succ, ← hg k hk.le]
    field_simp
    ring
  have hrun : algorithm_2_3_1 f P ε (fun _ => Bop) x s fun _ => P.Δ₀ := by
    refine ⟨hε, fun _ u v => ?_, ⟨rfl, fun k hk => ?_, fun k hk => ?_⟩⟩
    · change ⟪Bop u, v⟫ = ⟪u, Bop v⟫
      rw [hBop, hBop, inner_smul_left, inner_smul_right]; simp
    · have hk := hbefore k hk
      have hgk : ‖gradient f (x k)‖ ≤ 2 := by
        rw [hg k hk.le]; linarith [hω k hk.le]
      have hts : t * ‖gradient f (x k)‖ ≤ P.Δ₀ := by
        have := mul_le_mul_of_nonneg_left hgk ht.le
        simp only [t] at this ⊢; linarith
      refine ⟨by simpa [s, norm_smul, abs_of_pos ht] using hts, t, ⟨ht.le, hts, fun τ _ _ => ?_⟩,
        le_rfl⟩
      rw [hq, hq]
      have : 0 ≤ (τ - t) ^ 2 / (2 * t) * ‖gradient f (x k)‖ ^ 2 := by positivity
      have e : -τ * ‖gradient f (x k)‖ ^ 2 + τ ^ 2 / (2 * t) * ‖gradient f (x k)‖ ^ 2 -
          (-t * ‖gradient f (x k)‖ ^ 2 + t ^ 2 / (2 * t) * ‖gradient f (x k)‖ ^ 2) =
          (τ - t) ^ 2 / (2 * t) * ‖gradient f (x k)‖ ^ 2 := by
        field_simp; ring
      linarith
    · have hk := hbefore k hk
      change TRAcceptance P.toTRParams (tr1Ratio f (x k) Bop (s k)) (x k) (s k) (x (k + 1))
        P.Δ₀ P.Δ₀
      rw [hratio k hk]
      have h1 : P.η₁ ≤ 2 := by linarith [P.η₁_le_η₂, P.η₂_lt_one]
      refine ⟨by rw [ite_eq_left h1, hstep k hk], fun _ => ⟨le_rfl, ?_⟩,
        fun _ h2 => absurd h2 (not_lt.2 (by linarith [P.η₂_lt_one])),
        fun h3 => absurd h3 (not_lt.2 h1)⟩
      exact le_mul_of_one_le_left P.Δ₀_pos.le P.one_le_γ₃
  refine ⟨f, hb, hgl, fun _ => Bop, x, s, fun _ => P.Δ₀, by simp [x, slowX],
    ⟨(inv_pos.2 ht).le, fun _ => ?_⟩, hrun, hratio, hhit, funEvalCount_eq kε, ?_⟩
  · calc ‖Bop‖ ≤ ‖t⁻¹‖ * ‖ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1))‖ := norm_smul_le _ _
      _ ≤ t⁻¹ * 1 := by
        rw [Real.norm_of_nonneg (inv_pos.2 ht).le]
        exact mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_id_le) (inv_pos.2 ht).le
      _ = t⁻¹ := mul_one _
  · classical
    rw [derivEvalCount_eq_count]
    have : Nat.count (fun k => P.η₁ ≤ tr1Ratio f (x k) Bop (s k)) kε = kε := by
      rw [Nat.count_eq_card_filter_range, filter_true_of_mem, card_range]
      intro k hk
      rw [hratio k (mem_range.1 hk)]
      linarith [P.η₁_le_η₂, P.η₂_lt_one]
    rw [this]

end CartisGouldToint.Chapter02
