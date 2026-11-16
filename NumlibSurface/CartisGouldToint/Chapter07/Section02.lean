/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Calculus.MultivariateTaylor.Remainder
import Numlib.Optimization.Constrained.TwoPhase.Complexity
import NumlibSurface.CartisGouldToint.Chapter06.Section03
import NumlibSurface.CartisGouldToint.Chapter07.Section01

/-!
# Cartis, Gould and Toint, Section 7.2: Finding first-order approximate minimizers

This module formalizes Section 7.2 of [cartis2022evaluation]. The problem is (7.1.1): minimize
$f(x)$ subject to $x \in \mathcal{C}$ and $c(x) = 0$, for $f : \mathbb{R}^n \to \mathbb{R}$,
$c : \mathbb{R}^n \to \mathbb{R}^m$ and a set $\mathcal{C} \subseteq \mathbb{R}^n$; the results that
need $\mathcal{C}$ closed, convex and nonempty assume C.CNe. For a target $t \in \mathbb{R}$ let
$r(x, t) = (c(x), f(x) - t)$, with norm $\|r(x, t)\| = \sqrt{\|c(x)\|^2 + (f(x) - t)^2}$ (7.2.4),
and let $\mu_2(x, t) = \frac{1}{2} \|r(x, t)\|^2$ (7.2.5). The two-phase target-following algorithm
TPp-GC (Algorithm 7.2.1) first applies ARpLE-CC (Algorithm 6.3.1) to $c$ to find a point
$x_1 \in \mathcal{C}$ with $\|c(x_1)\| \le \theta \epsilon_0$. In Phase 2, each outer iteration $k$
runs ARp1-CC (Algorithm 6.2.2) on $\mu_2(\cdot, t_k)$ until the test (7.2.10) holds, and then lowers
the target $t_k$. Lemma 7.2.1 gives the termination guarantees, Lemma 7.2.2 bounds the cost of Phase
1, and Lemmas 7.2.3–7.2.6 and Theorem 7.2.7 bound the cost of Phase 2. The source claims the order
$O(\max(\epsilon_0^{-1}, \epsilon_0^{-1/p} \epsilon_1^{-(p+1)/p}))$ of (7.2.50) for Phase 2. The
formal Theorem 7.2.7 has this order only when the number of bad outer iterations, which the source
does not bound, is bounded independently of $\epsilon_0$ and $\epsilon_1$; see the deviations below.

The residual $\|r(x, t)\|$ and the merit function $\mu_2(x, t)$ are the backbone
`Constrained.targetResidual f c t x` and `Constrained.targetMerit f c t x`. Phase 2 is an instance
of the target-following outer loop `Constrained.IsTargetFollowingRun` of the backbone, and its inner
ARp1-CC runs satisfy the contract `Constrained.TargetFollowingSeq.IsInnerContract`, from which the
backbone derives the counting of Lemma 7.2.6 and Theorem 7.2.7.

## Main definitions

* Assumption c.D1pL.C, `CartisGouldToint.Chapter07.AssumptionCD1pLC`: the constraint functions are
  $C^p$ near $\mathcal{C}$ with Lipschitz and bounded derivatives on $\mathcal{C}$.
* Assumption f.D1pL.C, `CartisGouldToint.Chapter07.AssumptionFD1pLC`: the same for the objective.
* Equation (7.2.7), `CartisGouldToint.Chapter07.nearFeasible`: the region of near feasibility
  $\mathcal{F}_\beta = \{x \in \mathcal{C} \mid \|c(x)\| \le \beta\}$.
* Assumption f.B.Fb, `CartisGouldToint.Chapter07.AssumptionBFb`:
  $f_{\mathrm{low}} \le f \le f_{\mathrm{up}}$ on $\mathcal{F}_\beta$.
* Assumption $\mu_2$.DpL.C, `CartisGouldToint.Chapter07.AssumptionMu2DpLC`: every $\mu_2(\cdot, t)$
  satisfies f.DpL.C on $\mathcal{C}$.
* Algorithm 7.2.1, `CartisGouldToint.Chapter07.TPpGCParams`: the constants of the algorithm.
* Equation (7.2.8), `CartisGouldToint.Chapter07.TPpGCTol`: the tolerances
  $0 < \epsilon_0 \le \min(1, \beta)$ and $0 < \epsilon_1 \le 1$.
* Equation (7.2.10), `CartisGouldToint.Chapter07.innerStop`: the termination test of the inner runs.
* Equation (7.2.12), `CartisGouldToint.Chapter07.targetCrit`: the test
  $\omega_{\mu_2,\mathcal{C},1}(x, t) \le \epsilon_1 \|r(x, t)\|$.
* Algorithm 7.2.1, `CartisGouldToint.Chapter07.Phase2Seq` and
  `CartisGouldToint.Chapter07.IsTPpGCPhase2`: the sequences of Phase 2 and Phase 2 as a run
  predicate.
* Equation (7.2.25), `CartisGouldToint.Chapter07.Phase2Seq.IsKa` and
  `CartisGouldToint.Chapter07.Phase2Seq.IsKb`: the sets $\mathcal{K}_a$ and $\mathcal{K}_b$ of outer
  iterations.
* Algorithm 7.2.1, Step 2, `CartisGouldToint.Chapter07.Phase2Seq.Stop`: the termination of Phase 2.
* Equation (7.2.47), `CartisGouldToint.Chapter07.kappaSGC`: the constant
  $\kappa^S_{\mathrm{ARpGC}}$.
* Equation (7.2.39), `CartisGouldToint.Chapter07.goodBound`: the bound $G$ on the good inner
  iterations between two consecutive iterations of $\mathcal{K}_a$.
* Algorithm 7.2.1, `CartisGouldToint.Chapter07.algorithm_7_2_1`: a whole run of TPp-GC.
* `CartisGouldToint.Chapter07.Phase2Seq.IsGood` and `CartisGouldToint.Chapter07.Phase2Seq.IsBad`:
  the good inner iterations and the bad outer iterations of Phase 2.

## Main results

* Lemma 7.2.1, `CartisGouldToint.Chapter07.lemma_7_2_1` and
  `CartisGouldToint.Chapter07.lemma_7_2_1_phase2`: the output of TPp-GC is a critical point of the
  infeasibility or an $(\epsilon_0, \epsilon_1)$-approximate first-order minimizer.
* Equations (7.2.17) and (7.2.20), `CartisGouldToint.Chapter07.IsTPpGCPhase2.output_spec`: the
  output $(x_\epsilon, t_\epsilon)$ of Phase 2 satisfies $x_\epsilon \in \mathcal{C}$, $\theta
  \epsilon_0 < \|r(x_\epsilon, t_\epsilon)\| \le \epsilon_0$, $f(x_\epsilon) \ge t_\epsilon$ and the
  criticality test (7.2.12).
* Lemma 7.2.2, `CartisGouldToint.Chapter07.lemma_7_2_2`: the evaluation counts of Phase 1.
* Lemma 7.2.3, `CartisGouldToint.Chapter07.lemma_7_2_3`: the targets decrease, the iterates stay
  near feasibility, and the targets lie in $[f_{\mathrm{low}} - 1, f_{\mathrm{up}}]$.
* Lemma 7.2.4, `CartisGouldToint.Chapter07.lemma_7_2_4`: $|\mathcal{K}_a| \le (f_{\mathrm{up}} -
  f_{\mathrm{low}} + 1) / ((1 - \theta) \epsilon_0)$.
* Lemma 7.2.5, `CartisGouldToint.Chapter07.lemma_7_2_5` and
  `CartisGouldToint.Chapter07.IsTPpGCPhase2.inner_sigma_le`: a uniform Lipschitz constant $L_\mu$
  for the merit functions, and the bound $\sigma_{\mu,\max}$ on the inner regularization parameters.
* Lemma 7.2.6, `CartisGouldToint.Chapter07.lemma_7_2_6` and
  `CartisGouldToint.Chapter07.lemma_7_2_6_of_mu2`: the counting of the inner iterations of Phase 2,
  corrected.
* Theorem 7.2.7, `CartisGouldToint.Chapter07.theorem_7_2_7_phase2`,
  `CartisGouldToint.Chapter07.theorem_7_2_7_phase2_of_mu2` and
  `CartisGouldToint.Chapter07.theorem_7_2_7`: the evaluation complexity of Phase 2 and of the whole
  algorithm, with the number of bad iterations as a parameter.
* Theorem 7.2.7, `CartisGouldToint.Chapter07.theorem_7_2_7_phase2_of_gradient_le` and
  `CartisGouldToint.Chapter07.theorem_7_2_7_of_gradient_le`: the same without the parameter when
  $\|\nabla f\|$ is bounded near feasibility.
* `CartisGouldToint.Chapter07.exists_innerRun`, `CartisGouldToint.Chapter07.exists_phase2` and
  `CartisGouldToint.Chapter07.algorithm_7_2_1_exists`: the inner runs, Phase 2 and the whole
  algorithm have runs.
* `CartisGouldToint.Chapter07.IsTPpGCPhase2.toRun` and
  `CartisGouldToint.Chapter07.IsTPpGCPhase2.toContract`: Phase 2 is a run of the backbone outer
  loop, and its inner runs satisfy the backbone contract.

## Proof outline

Each iteration of $\mathcal{K}_a$ lowers the target by at least $(1 - \theta) \epsilon_0$, and all
targets lie in $[f_{\mathrm{low}} - 1, f_{\mathrm{up}}]$; this bounds $|\mathcal{K}_a|$. Between two
consecutive iterations of $\mathcal{K}_a$ the residual $\|r\|$ stays between $\theta \epsilon_0$ and
$\epsilon_0$, and every good inner iteration lowers it by a fixed amount (Lemma 6.2.4); this bounds
the good iterations. Lemma 2.4.1, applied to each inner run, bounds all inner iterations by the
successful ones.

## Conventions

* $\mathbb{R}^n$ and $\mathbb{R}^m$ are `EuclideanSpace ℝ (Fin n)` and `EuclideanSpace ℝ (Fin m)`.
  The derivative tensors $\nabla^j g(x)$ are `iteratedFDeriv ℝ j g x`, with the operator norm of
  multilinear maps, and $\|\nabla f(x)\|$ is `‖iteratedFDeriv ℝ 1 f x‖`.
* $\omega_{h,\mathcal{C},1}$ is the first-order measure `CartisGouldToint.Chapter06.omega1` of
  (6.1.5).
* Outer iteration $k \ge 1$ is *reached* if no outer iteration $j \in [1, k)$ terminates Phase 2
  (`CartisGouldToint.Chapter07.Phase2Seq.Before`). Phase 2 terminates at $k_\epsilon$ if
  $k_\epsilon \ge 1$ is reached and terminates (`CartisGouldToint.Chapter07.Phase2Seq.IsEnd`).
* $f_{\mathrm{low}}$ and $f_{\mathrm{up}}$ are `flow` and `fup`.
* For the inner runs, write $A_1 = 1 + |\log \gamma_1| / \log \gamma_2$ and $C_1 =
  \log(\sigma_{\mu,\max} / \sigma_0) / \log \gamma_2$, the constants of Lemma 2.4.1.

## Implementation notes

* The algorithms are run predicates on sequences. The data of Phase 2 is
  `CartisGouldToint.Chapter07.Phase2Seq`, indexed by the outer iteration $k \ge 1$ and, for the
  inner runs, by $(k, i)$.
* The Lipschitz and boundedness constants of c.D1pL.C and f.D1pL.C are existentially quantified, as
  in the source. The constants $f_{\mathrm{low}}$ and $f_{\mathrm{up}}$ of f.B.Fb are explicit
  arguments.
* Phase 2 terminates at outer iteration $k$ in case (c), when $k$ is in neither $\mathcal{K}_a$ nor
  $\mathcal{K}_b$, or in cases (a) and (b) when (7.2.12) holds at $(x_{k+1}, t_{k+1})$. The output
  target is `CartisGouldToint.Chapter07.Phase2Seq.targetOut`.
* Phase 2 uses $1 + \sum_{j=1}^{k} e_j$ evaluations of $(f, c)$ and $1 +
  \sum_{j=1}^{k}|\{\text{successful inner iterations of run } j\}|$ evaluations of their derivatives
  up to outer iteration $k$.
* The complexity results come in three forms: with a uniform Lipschitz constant $L_\mu$ for the
  merit functions as a hypothesis, under the hypotheses $\mu_2$.DpL.C and f.B.Fb of the source
  (names ending in `_of_mu2`), and without the bad-iteration parameter (names ending in
  `_of_gradient_le`).

## Deviations from the source

* **Assumption f.B.Fb** (reading). The source states the assumption "if
  $\mathcal{F}_\beta \neq \emptyset$". For the universally quantified form used here the proviso is
  vacuous. See `CartisGouldToint.Chapter07.AssumptionBFb`.
* **Assumption f.D1pL.C** (typo). The source writes $\nabla^j_x f_i$. The objective is scalar, and
  $\nabla^j_x f$ is meant. See `CartisGouldToint.Chapter07.AssumptionFD1pLC`.
* **Algorithm 7.2.1, Phase 2, Step 1** (correction). Step 1 applies ARp1-CC (Algorithm 6.2.2), not
  ARp-CC, since the proof of Lemma 7.2.6 uses Lemma 6.2.4. See
  `CartisGouldToint.Chapter07.IsTPpGCPhase2`.
* **Algorithm 7.2.1, Step 2(a)** (correction). The source prints the test
  $\|r(x_{k+1}, t_k)\| < \theta \epsilon_0$, with which Lemma 7.2.1 fails. The test is
  $\|r(x_{k+1}, t_k)\| \le \theta \epsilon_0$. See `CartisGouldToint.Chapter07.Phase2Seq.IsKa`.
* **Lemma 7.2.2** (correction). The printed derivative-evaluation bound (7.2.24) lacks the term $+2$
  of Theorem 6.3.1, which is restored. See `CartisGouldToint.Chapter07.lemma_7_2_2`.
* **Lemma 7.2.5** (generalization). The hypothesis $\Phi_\ell$.DpL.C of the source is not needed.
  See `CartisGouldToint.Chapter07.lemma_7_2_5`.
* **Lemma 7.2.6** (correction). The block argument of the source omits the restart of $\sigma$ at
  $\sigma_0$ in every inner run and the $i = 0$ elements of $\mathcal{I}^s_k$, so that (7.2.39) can
  fail, and it gives no bound on the bad outer iterations. See
  `CartisGouldToint.Chapter07.lemma_7_2_6`.
* **Theorem 7.2.7** (correction). The number of bad outer iterations is a parameter of the
  statement; under bounded gradients it is bounded by $N_b = O(\epsilon_0^{-1} \epsilon_1^{-1})$,
  which is within the order of (7.2.50) for $\epsilon_0 = \epsilon_1$ if and only if $p \le 2$. The
  derivative count has a term $\epsilon_0^{-1}$ that (7.2.53) lacks, and whether (7.2.53) holds is
  open. See `CartisGouldToint.Chapter07.theorem_7_2_7` and
  `CartisGouldToint.Chapter07.theorem_7_2_7_of_gradient_le`.
* **Equation (7.2.47)** (generalization). The constant $\kappa^S_{\mathrm{ARpGC}} = \kappa_1^{-1}
  \theta^{-(p+1)/p}$ replaces the weaker $\kappa_1^{-1} \theta^{-(p+2)/p}$ of the source. See
  `CartisGouldToint.Chapter07.kappaSGC`.

## Not formalized

* **Section 7.2.3.** The discussion of penalty, augmented Lagrangian, barrier and SQP methods. It
  has no numbered results.
-/

open Set Optimization
open scoped Nat

namespace CartisGouldToint.Chapter07

variable {n m : ℕ}

set_option hygiene false in
local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

set_option hygiene false in
local notation "ℝᵐ" => EuclideanSpace ℝ (Fin m)

/-- Let $g : \mathbb{R}^n \to \mathbb{R}$, $\mathcal{C} \subseteq \mathbb{R}^n$ and
$p \in \mathbb{N}$. The function $g$ is **$p$ times differentiable with Lipschitz and bounded
derivatives on $\mathcal{C}$** if $g$ is $p$ times continuously differentiable on an open set
containing $\mathcal{C}$, and for each $j \in [1 : p]$ the derivative tensor $\nabla^j g$ is
Lipschitz continuous on $\mathcal{C}$ with some constant and bounded on $\mathcal{C}$ by some
constant.

This is the common form of the assumptions c.D1pL.C and f.D1pL.C of Section 7.2.2.1 of
[cartis2022evaluation]. -/
def IsD1pLOn (g : ℝⁿ → ℝ) (C : Set ℝⁿ) (p : ℕ) : Prop :=
  (∃ D, IsOpen D ∧ C ⊆ D ∧ ContDiffOn ℝ p g D) ∧
    ∀ j ∈ Finset.Icc 1 p, (∃ L, IteratedFDerivLipschitzOn g j L C) ∧
      ∃ B, ∀ x ∈ C, ‖iteratedFDeriv ℝ j g x‖ ≤ B

/-- **Assumption c.D1pL.C** of [cartis2022evaluation], Section 7.2.2.1. Let
$c : \mathbb{R}^n \to \mathbb{R}^m$, $\mathcal{C} \subseteq \mathbb{R}^n$ and
$p \in \mathbb{N}$. Each constraint function $c_i$, $i \in [1 : m]$, is $p$ times continuously
differentiable on an open set containing $\mathcal{C}$, and its derivative tensors
$\nabla^j c_i$, $j \in [1 : p]$, are Lipschitz continuous and bounded on $\mathcal{C}$.

The condition on each $c_i$ is `CartisGouldToint.Chapter07.IsD1pLOn`. -/
def AssumptionCD1pLC (c : ℝⁿ → ℝᵐ) (C : Set ℝⁿ) (p : ℕ) : Prop :=
  ∀ i, IsD1pLOn (fun x => c x i) C p

/-- **Assumption f.D1pL.C** of [cartis2022evaluation], Section 7.2.2.1. Let
$f : \mathbb{R}^n \to \mathbb{R}$, $\mathcal{C} \subseteq \mathbb{R}^n$ and $p \in \mathbb{N}$.
The objective $f$ is $p$ times continuously differentiable on an open set containing
$\mathcal{C}$, and its derivative tensors $\nabla^j f$, $j \in [1 : p]$, are Lipschitz
continuous and bounded on $\mathcal{C}$.

**Typo.** The source writes $\nabla^j_x f_i$. The objective is scalar, and $\nabla^j_x f$ is
meant.

The condition is `CartisGouldToint.Chapter07.IsD1pLOn` for $f$. -/
def AssumptionFD1pLC (f : ℝⁿ → ℝ) (C : Set ℝⁿ) (p : ℕ) : Prop :=
  IsD1pLOn f C p

/-- **Equation (7.2.7)** of [cartis2022evaluation]. Let $\mathcal{C} \subseteq \mathbb{R}^n$,
$c : \mathbb{R}^n \to \mathbb{R}^m$ and $\beta \in \mathbb{R}$. The **region of near
feasibility** is
$$\mathcal{F}_\beta = \{x \in \mathcal{C} \mid \|c(x)\| \le \beta\}.$$
-/
def nearFeasible (C : Set ℝⁿ) (c : ℝⁿ → ℝᵐ) (β : ℝ) : Set ℝⁿ := {x ∈ C | ‖c x‖ ≤ β}

/-- **Assumption f.B.Fb** of [cartis2022evaluation], Section 7.2.2.1. Let
$f : \mathbb{R}^n \to \mathbb{R}$, $c : \mathbb{R}^n \to \mathbb{R}^m$,
$\mathcal{C} \subseteq \mathbb{R}^n$ and $\beta, f_{\mathrm{low}}, f_{\mathrm{up}} \in
\mathbb{R}$. The objective is bounded on the region of near feasibility:
$$f_{\mathrm{low}} \le f(x) \le f_{\mathrm{up}} \quad \text{for every } x \in
  \mathcal{F}_\beta.$$

**Reading.** The source states the assumption "if $\mathcal{F}_\beta \neq \emptyset$". For the
universally quantified form used here this proviso is vacuous. The constants $f_{\mathrm{low}}$
and $f_{\mathrm{up}}$ are explicit arguments. -/
def AssumptionBFb (f : ℝⁿ → ℝ) (c : ℝⁿ → ℝᵐ) (C : Set ℝⁿ) (β flow fup : ℝ) : Prop :=
  ∀ x ∈ nearFeasible C c β, flow ≤ f x ∧ f x ≤ fup

variable {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {C : Set ℝⁿ} {x : ℝⁿ} {p : ℕ} {β β' flow fup : ℝ}

/-- The definition of `CartisGouldToint.Chapter07.IsD1pLOn`, unfolded: $g$ is $C^p$ on an open set
containing $\mathcal{C}$, and each $\nabla^j g$, $j \in [1 : p]$, is Lipschitz and bounded on
$\mathcal{C}$. -/
theorem isD1pLOn_iff {g : ℝⁿ → ℝ} :
    IsD1pLOn g C p ↔ (∃ D, IsOpen D ∧ C ⊆ D ∧ ContDiffOn ℝ p g D) ∧
      ∀ j ∈ Finset.Icc 1 p, (∃ L, IteratedFDerivLipschitzOn g j L C) ∧
        ∃ B, ∀ x ∈ C, ‖iteratedFDeriv ℝ j g x‖ ≤ B :=
  Iff.rfl

/-- The definition of c.D1pL.C, unfolded: each component $c_i$ satisfies
`CartisGouldToint.Chapter07.IsD1pLOn` on $\mathcal{C}$. -/
theorem assumptionCD1pLC_iff : AssumptionCD1pLC c C p ↔ ∀ i, IsD1pLOn (fun x => c x i) C p :=
  Iff.rfl

/-- The definition of f.D1pL.C, unfolded: $f$ satisfies `CartisGouldToint.Chapter07.IsD1pLOn` on
$\mathcal{C}$. -/
theorem assumptionFD1pLC_iff : AssumptionFD1pLC f C p ↔ IsD1pLOn f C p := Iff.rfl

/-- A point lies in $\mathcal{F}_\beta$ if and only if $x \in \mathcal{C}$ and $\|c(x)\| \le \beta$.
-/
theorem mem_nearFeasible : x ∈ nearFeasible C c β ↔ x ∈ C ∧ ‖c x‖ ≤ β := Iff.rfl

/-- The region of near feasibility is a subset of $\mathcal{C}$:
$\mathcal{F}_\beta \subseteq \mathcal{C}$. -/
theorem nearFeasible_subset : nearFeasible C c β ⊆ C := fun _ hx => hx.1

/-- The region of near feasibility grows with $\beta$: if $\beta \le \beta'$, then
$\mathcal{F}_\beta \subseteq \mathcal{F}_{\beta'}$. -/
theorem nearFeasible_mono (h : β ≤ β') : nearFeasible C c β ⊆ nearFeasible C c β' :=
  fun _ hx => ⟨hx.1, hx.2.trans h⟩

/-- The feasible set lies in every region of near feasibility with $\beta \ge 0$:
$\mathcal{F}(\mathcal{C}, c) \subseteq \mathcal{F}_\beta$. -/
theorem feasibleSet_subset_nearFeasible (hβ : 0 ≤ β) : feasibleSet C c ⊆ nearFeasible C c β :=
  fun _ hx => ⟨hx.1, by simpa [hx.2] using hβ⟩

/-- The definition of f.B.Fb, unfolded: $f_{\mathrm{low}} \le f(x) \le f_{\mathrm{up}}$ for every
$x \in \mathcal{C}$ with $\|c(x)\| \le \beta$. -/
theorem assumptionBFb_iff :
    AssumptionBFb f c C β flow fup ↔ ∀ x ∈ C, ‖c x‖ ≤ β → flow ≤ f x ∧ f x ≤ fup :=
  ⟨fun h x hx hc => h x ⟨hx, hc⟩, fun h x hx => h x hx.1 hx.2⟩

/-- If f.B.Fb holds with parameter $\beta$, it holds with every parameter $\beta' \le \beta$. -/
theorem AssumptionBFb.mono (h : AssumptionBFb f c C β flow fup) (hβ : β' ≤ β) :
    AssumptionBFb f c C β' flow fup :=
  fun x hx => h x (nearFeasible_mono hβ hx)

/-- If f.B.Fb holds with parameter $\beta$ and $\epsilon \le \beta$, then
$f_{\mathrm{low}} \le f(z) \le f_{\mathrm{up}}$ for every $z \in \mathcal{C}$ with
$\|c(z)\| \le \epsilon$.

This is the form that the target-following outer loop uses
(`Constrained.IsTargetFollowingRun.kaCount_le`). -/
theorem AssumptionBFb.of_le {ε : ℝ} (h : AssumptionBFb f c C β flow fup) (hε : ε ≤ β) :
    ∀ z ∈ C, ‖c z‖ ≤ ε → flow ≤ f z ∧ f z ≤ fup :=
  fun z hz hcz => h z ⟨hz, hcz.trans hε⟩

/-! ### The assumption $\mu_2$.DpL.C and the data of Algorithm 7.2.1 -/

/-- **Assumption $\mu_2$.DpL.C** of [cartis2022evaluation], Section 7.2.2.1. Let
$f : \mathbb{R}^n \to \mathbb{R}$, $c : \mathbb{R}^n \to \mathbb{R}^m$,
$\mathcal{C} \subseteq \mathbb{R}^n$ and $p \in \mathbb{N}$. For every target $t \in \mathbb{R}$
there is $L$ such that the merit function $\mu_2(\cdot, t) = \frac{1}{2} \|r(\cdot, t)\|^2$
satisfies f.DpL.C on $\mathcal{C}$ with constant $L$
(`CartisGouldToint.Chapter06.AssumptionDpLC`).

Footnote 53 of the source describes the assumption as $\Phi_\ell$.DpL.C for
$\Phi_\ell = \mu_2(\cdot, t)$. The constant may depend on $t$; Lemma 7.2.5
(`CartisGouldToint.Chapter07.lemma_7_2_5`) makes it uniform over a bounded interval of targets. -/
def AssumptionMu2DpLC (f : ℝⁿ → ℝ) (c : ℝⁿ → ℝᵐ) (C : Set ℝⁿ) (p : ℕ) : Prop :=
  ∀ t : ℝ, ∃ L, Chapter06.AssumptionDpLC (Constrained.targetMerit f c t) C p L

/-- **Algorithm 7.2.1** of [cartis2022evaluation], the constants of TPp-GC. An element consists of
the constants of the adaptive-regularization algorithms of Chapter 6
(`CartisGouldToint.Chapter06.ARpCCParams`), which both phases use, together with a factor
$\theta \in (0, 1)$ and the infeasibility bound $\beta > 0$ of $\mathcal{F}_\beta$.

Among the factors $\theta_1, \theta_2, \theta_3$ of `CartisGouldToint.Chapter06.ARpCCParams`,
only $\theta_1$ enters ARp1-CC and ARpLE-CC. -/
structure TPpGCParams extends toARpCCParams : Chapter06.ARpCCParams where
  /-- The factor $\theta$ of the tests $\|c(x)\| \le \theta \epsilon_0$ and
  $\|r(x, t)\| \le \theta \epsilon_0$. -/
  θ : ℝ
  /-- The infeasibility bound $\beta$ of $\mathcal{F}_\beta$. -/
  β : ℝ
  θ_pos : 0 < θ
  θ_lt_one : θ < 1
  β_pos : 0 < β

/-- **Equation (7.2.8)** of [cartis2022evaluation]. For the constants $P$ of TPp-GC, the tolerances
$\epsilon_0, \epsilon_1$ are **admissible** if
$$0 < \epsilon_0 \le \min(1, \beta), \qquad 0 < \epsilon_1 \le 1.$$
-/
structure TPpGCTol (P : TPpGCParams) (ε₀ ε₁ : ℝ) : Prop where
  ε₀_pos : 0 < ε₀
  ε₀_le_one : ε₀ ≤ 1
  ε₀_le_β : ε₀ ≤ P.β
  ε₁_pos : 0 < ε₁
  ε₁_le_one : ε₁ ≤ 1

/-- **Equation (7.2.10)** of [cartis2022evaluation], the termination test of the inner runs of Phase
2 of Algorithm 7.2.1. For a target $t$, a point $x$ passes the test if
$$\|r(x, t)\| \le \theta \epsilon_0, \quad \text{or} \quad f(x) < t, \quad \text{or} \quad
  \omega_{\mu_2,\mathcal{C},1}(x, t) \le \epsilon_1 \|r(x, t)\|.$$

Here $\omega_{\mu_2,\mathcal{C},1}(x, t)$ is `CartisGouldToint.Chapter06.omega1` of
$\mu_2(\cdot, t)$ at $x$. -/
def innerStop (f : ℝⁿ → ℝ) (c : ℝⁿ → ℝᵐ) (C : Set ℝⁿ) (θ ε₀ ε₁ t : ℝ) (x : ℝⁿ) : Prop :=
  Constrained.targetResidual f c t x ≤ θ * ε₀ ∨ f x < t ∨
    Chapter06.omega1 (Constrained.targetMerit f c t) C x ≤
      ε₁ * Constrained.targetResidual f c t x

/-- **Equation (7.2.12)** of [cartis2022evaluation]. For a target $t$, a point $x$ passes the
**criticality test** if
$$\omega_{\mu_2,\mathcal{C},1}(x, t) \le \epsilon_1 \|r(x, t)\|.$$
This is also the third test of (7.2.10). -/
def targetCrit (f : ℝⁿ → ℝ) (c : ℝⁿ → ℝᵐ) (C : Set ℝⁿ) (ε₁ t : ℝ) (x : ℝⁿ) : Prop :=
  Chapter06.omega1 (Constrained.targetMerit f c t) C x ≤ ε₁ * Constrained.targetResidual f c t x

/-- The test (7.2.10) holds if and only if $\|r(x, t)\| \le \theta \epsilon_0$, or $f(x) < t$, or
the criticality test (7.2.12) holds at $x$. -/
theorem innerStop_iff {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {C : Set ℝⁿ} {θ ε₀ ε₁ t : ℝ} {x : ℝⁿ} :
    innerStop f c C θ ε₀ ε₁ t x ↔ Constrained.targetResidual f c t x ≤ θ * ε₀ ∨ f x < t ∨
      targetCrit f c C ε₁ t x := Iff.rfl

/-- **Algorithm 7.2.1** of [cartis2022evaluation], the sequences of Phase 2. An element consists of
the outer iterates $x_k$, the targets $t_k$, and for each outer iteration $k$ the inner ARp1-CC
run on $\mu_2(\cdot, t_k)$: its iterates $x_{k,i}$, steps $s_{k,i}$, regularization parameters
$\sigma_{k,i}$ and length $e_k$.

The outer iterations are indexed by $k \ge 1$; the values at $k = 0$ are unused. -/
structure Phase2Seq (n : ℕ) where
  /-- The outer iterates $x_k$. -/
  X : ℕ → EuclideanSpace ℝ (Fin n)
  /-- The targets $t_k$. -/
  t : ℕ → ℝ
  /-- The inner iterates $x_{k,i}$. -/
  xi : ℕ → ℕ → EuclideanSpace ℝ (Fin n)
  /-- The inner steps $s_{k,i}$. -/
  si : ℕ → ℕ → EuclideanSpace ℝ (Fin n)
  /-- The inner regularization parameters $\sigma_{k,i}$. -/
  σi : ℕ → ℕ → ℝ
  /-- The lengths $e_k$ of the inner runs. -/
  e : ℕ → ℕ

namespace Phase2Seq

variable (f : ℝⁿ → ℝ) (c : ℝⁿ → ℝᵐ) (C : Set ℝⁿ) (p : ℕ) (P : TPpGCParams) (ε₀ ε₁ : ℝ)
  (D : Phase2Seq n)

/-- **Equation (7.2.25)** of [cartis2022evaluation], the set $\mathcal{K}_a$. Outer iteration $k$ is
in $\mathcal{K}_a$, that is, Step 2(a) occurs, if
$$\|r(x_{k+1}, t_k)\| \le \theta \epsilon_0.$$

**Correction.** The source enters Step 2(a) when $\|r(x_{k+1}, t_k)\| < \theta \epsilon_0$. With
the strict test, an inner run that stops with $\|r(x_{k+1}, t_k)\| = \theta \epsilon_0$ exactly,
$f(x_{k+1}) \ge t_k$ and a large criticality measure falls into Step 2(c). The algorithm then
terminates without the guarantee $\theta \epsilon_0 < \|r(x_\epsilon, t_\epsilon)\|$ of
(7.2.17), and Lemma 7.2.1 fails. With the test $\le$, the strict inequality
$\|c(x_\epsilon)\| > \theta \epsilon_0$ in (7.2.15) also follows; the printed proof gives only
$\ge$. -/
def IsKa (k : ℕ) : Prop := Constrained.targetResidual f c (D.t k) (D.X (k + 1)) ≤ P.θ * ε₀

/-- **Equation (7.2.25)** of [cartis2022evaluation], the set $\mathcal{K}_b$. Outer iteration $k$ is
in $\mathcal{K}_b$, that is, Step 2(b) occurs, if
$$\|r(x_{k+1}, t_k)\| > \theta \epsilon_0 \quad \text{and} \quad f(x_{k+1}) < t_k.$$
-/
def IsKb (k : ℕ) : Prop :=
  P.θ * ε₀ < Constrained.targetResidual f c (D.t k) (D.X (k + 1)) ∧ f (D.X (k + 1)) < D.t k

/-- The sequences of Phase 2 of TPp-GC as data of the target-following outer loop of the backbone
(`Constrained.TargetFollowingSeq`). The case tests are $\mathcal{K}_a$ and $\mathcal{K}_b$, and
the criticality test at outer iteration $k$ for a target $\tau$ is (7.2.12) at $x_{k+1}$. -/
def toTargetFollowingSeq : Constrained.TargetFollowingSeq ℝⁿ where
  x := D.X
  t := D.t
  xi := D.xi
  e := D.e
  Ka := D.IsKa f c P ε₀
  Kb := D.IsKb f c P ε₀
  crit k τ := targetCrit f c C ε₁ τ (D.X (k + 1))

/-- The sequences of Phase 2 as data of the outer loop of the backbone, with given case tests and a
criticality test that never holds. The evaluation counts and the count of $\mathcal{K}_a$ are
taken on this data, since they do not involve the criticality test. -/
def toCountSeq (Ka Kb : ℕ → Prop) : Constrained.TargetFollowingSeq ℝⁿ where
  x := D.X
  t := D.t
  xi := D.xi
  e := D.e
  Ka := Ka
  Kb := Kb
  crit _ _ := False

/-- **Algorithm 7.2.1** of [cartis2022evaluation], Step 2, termination. Phase 2 terminates at outer
iteration $k$ if $k$ is in neither $\mathcal{K}_a$ nor $\mathcal{K}_b$ (case (c)), or if
$k \in \mathcal{K}_a \cup \mathcal{K}_b$ and the criticality test (7.2.12) holds at
$(x_{k+1}, t_{k+1})$. -/
abbrev Stop (k : ℕ) : Prop := (D.toTargetFollowingSeq f c C P ε₀ ε₁).Stop k

/-- Outer iteration $k$ is reached: no outer iteration $j \in [1, k)$ terminates Phase 2. -/
abbrev Before (k : ℕ) : Prop := (D.toTargetFollowingSeq f c C P ε₀ ε₁).Before k

/-- Phase 2 terminates at outer iteration $k_\epsilon$: $k_\epsilon \ge 1$, outer iteration
$k_\epsilon$ is reached, and Phase 2 terminates there. -/
abbrev IsEnd (kε : ℕ) : Prop := (D.toTargetFollowingSeq f c C P ε₀ ε₁).IsEnd kε

/-- The output target $t_\epsilon$ of Phase 2 terminating at outer iteration $k$: $t_{k+1}$ in cases
(a) and (b), and $t_k$ in case (c). The output point is $x_\epsilon = x_{k+1}$. -/
noncomputable abbrev targetOut (k : ℕ) : ℝ :=
  (D.toCountSeq (D.IsKa f c P ε₀) (D.IsKb f c P ε₀)).targetOut k

/-- Inner iteration $i$ of the $k$-th inner run is successful: $\rho_{k,i} \ge \eta_1$, where
$\rho_{k,i}$ is the ratio (4.1.15) of the achieved to the predicted decrease of
$\mu_2(\cdot, t_k)$. -/
def InnerSucc (k i : ℕ) : Prop :=
  P.η₁ ≤ taylorRatio (Constrained.targetMerit f c (D.t k)) p (D.xi k) (D.si k) i

/-- The number of evaluations of $(f, c)$ in Phase 2 up to outer iteration $k$:
$1 + \sum_{j=1}^{k} e_j$, one at $x_1$ and one per inner iteration. -/
noncomputable abbrev funEvals (k : ℕ) : ℕ :=
  (D.toCountSeq (fun _ => False) fun _ => False).funEvals k

/-- The number of successful iterations $i < e_k$ of the $k$-th inner run. -/
noncomputable abbrev succCount (k : ℕ) : ℕ :=
  (D.toCountSeq (fun _ => False) fun _ => False).succCount (D.InnerSucc f c p P) k

/-- The number of evaluations of the derivatives of $(f, c)$ in Phase 2 up to outer iteration $k$:
one at $x_1$ and one per successful inner iteration. -/
noncomputable abbrev derivEvals (k : ℕ) : ℕ :=
  (D.toCountSeq (fun _ => False) fun _ => False).derivEvals (D.InnerSucc f c p P) k

/-- The number of outer iterations $k \in [1, K)$ in $\mathcal{K}_a$. -/
noncomputable abbrev kaCount (K : ℕ) : ℕ :=
  (D.toCountSeq (D.IsKa f c P ε₀) fun _ => False).kaCount K

/-- The exemption test of the counting of Phase 2, with tolerance $e_1$. Outer iteration $k$ is
exempt if $k \in \mathcal{K}_a$, or if
$$\omega_{\mu_2,\mathcal{C},1}(x_{k+1}, t_k) \le e_1 \|r(x_{k+1}, t_k)\|.$$
For $e_1 = \epsilon_1$ the second condition is the third test of (7.2.10). The last inner
iteration of an exempt outer iteration is not a good iteration. -/
def Exempt (e₁ : ℝ) (k : ℕ) : Prop :=
  D.IsKa f c P ε₀ k ∨ targetCrit f c C e₁ (D.t k) (D.X (k + 1))

/-- A **good** inner iteration $(k, i)$: $i < e_k$, iteration $i$ is successful, it is not the last
iteration of a run whose outer iteration is exempt
(`CartisGouldToint.Chapter07.Phase2Seq.Exempt` with tolerance $\epsilon_1$), and the new iterate
has $\|r(x_{k,i+1}, t_k)\| \ge \theta \epsilon_0$.

These are the iterations that the proof of Lemma 7.2.6 of [cartis2022evaluation] counts; Lemma
6.2.4 controls their decrease. For a Phase-2 run they are the successful iterations whose new
iterate fails the third test of (7.2.10) and has residual greater than $\theta \epsilon_0$
(`CartisGouldToint.Chapter07.IsTPpGCPhase2.isGood_iff`). -/
abbrev IsGood (k i : ℕ) : Prop :=
  (D.toTargetFollowingSeq f c C P ε₀ ε₁).IsGood f c P.θ ε₀ (D.InnerSucc f c p P)
    (D.Exempt f c C P ε₀ ε₁) k i

/-- The number of good iterations (`CartisGouldToint.Chapter07.Phase2Seq.IsGood`) of the $k$-th
inner run. -/
noncomputable abbrev goodCount (k : ℕ) : ℕ :=
  (D.toTargetFollowingSeq f c C P ε₀ ε₁).goodCount f c P.θ ε₀ (D.InnerSucc f c p P)
    (D.Exempt f c C P ε₀ ε₁) k

/-- A **bad** outer iteration $k$: $k \in \mathcal{K}_b$, and its inner run contains no good
iteration.

For a Phase-2 run the new iterate of a bad outer iteration passes the third test of (7.2.10) for
the old target, $\omega_{\mu_2,\mathcal{C},1}(x_{k+1}, t_k) \le \epsilon_1 \|r(x_{k+1}, t_k)\|$
(`CartisGouldToint.Chapter07.IsTPpGCPhase2.isBad_targetCrit`). The source gives no bound on the
number of such iterations. -/
abbrev IsBad (k : ℕ) : Prop :=
  (D.toTargetFollowingSeq f c C P ε₀ ε₁).IsBad f c P.θ ε₀ (D.InnerSucc f c p P)
    (D.Exempt f c C P ε₀ ε₁) k

/-- The number of bad outer iterations (`CartisGouldToint.Chapter07.Phase2Seq.IsBad`)
$k \in [1, K)$. -/
noncomputable abbrev badCount (K : ℕ) : ℕ :=
  (D.toTargetFollowingSeq f c C P ε₀ ε₁).badCount f c P.θ ε₀ (D.InnerSucc f c p P)
    (D.Exempt f c C P ε₀ ε₁) K

end Phase2Seq

/-- **Algorithm 7.2.1** of [cartis2022evaluation], Phase 2 (TPp-GC), as a predicate on the sequences
$D$ of Phase 2. Let $\epsilon_0, \epsilon_1$ satisfy (7.2.8), and let $x_1 \in \mathcal{C}$ with
$\|c(x_1)\| \le \theta \epsilon_0$ be the output of Phase 1. The sequences start at $x_1$, and:

* Step 0: $t_1 = f(x_1) - \sqrt{\epsilon_0^2 - \|c(x_1)\|^2}$;
* Step 1, for every outer iteration $k \ge 1$ that is reached: the inner run starts at
  $x_{k,0} = x_k$, is an ARp1-CC run (Algorithm 6.2.2) on $\mu_2(\cdot, t_k)$ with the
  termination test (7.2.10), stops at the first index $e_k$ at which the test holds, and
  $x_{k+1} = x_{k,e_k}$;
* Step 2(a): if $k \in \mathcal{K}_a$, then $t_{k+1} = f(x_{k+1}) - \sqrt{\epsilon_0^2 -
  \|c(x_{k+1})\|^2}$ (7.2.11);
* Step 2(b): if $k \in \mathcal{K}_b$, then $t_{k+1} = 2 f(x_{k+1}) - t_k$ (7.2.13).

**Correction.** The source applies ARp-CC (Algorithm 6.2.1) in Step 1. The proof of Lemma 7.2.6
uses Lemma 6.2.4, that is, the step rule (6.2.29) of ARp1-CC. The step rule (6.2.10) of ARp-CC,
with a fixed tolerance, does not fit the relative test of (7.2.10).

**Correction.** Step 2(a) is entered when $\|r(x_{k+1}, t_k)\| \le \theta \epsilon_0$; the
source prints $<$. See `CartisGouldToint.Chapter07.Phase2Seq.IsKa`.

The steps of the inner runs satisfy `Optimization.IsFirstOrderCCStep` with the factor
$\theta_1$, and the runs are `Optimization.IsARRun` with the ratio `Optimization.taylorRatio`.
Termination of Phase 2 is `CartisGouldToint.Chapter07.Phase2Seq.Stop`. -/
structure IsTPpGCPhase2 (f : ℝⁿ → ℝ) (c : ℝⁿ → ℝᵐ) (C : Set ℝⁿ) (p : ℕ) (P : TPpGCParams)
    (ε₀ ε₁ : ℝ) (x₁ : ℝⁿ) (D : Phase2Seq n) : Prop where
  /-- The tolerances satisfy (7.2.8). -/
  tol : TPpGCTol P ε₀ ε₁
  /-- The starting point lies in $\mathcal{C}$: $x_1 \in \mathcal{C}$. -/
  mem_one : x₁ ∈ C
  /-- Phase 1 ended with $\|c(x_1)\| \le \theta \epsilon_0$. -/
  norm_one_le : ‖c x₁‖ ≤ P.θ * ε₀
  /-- The first outer iterate is the starting point $x_1$. -/
  X_one : D.X 1 = x₁
  /-- Step 0: $t_1 = f(x_1) - \sqrt{\epsilon_0^2 - \|c(x_1)\|^2}$. -/
  t_one : D.t 1 = f x₁ - √(ε₀ ^ 2 - ‖c x₁‖ ^ 2)
  /-- Step 1: the inner run of a reached outer iteration $k$ starts at $x_{k,0} = x_k$. -/
  inner_zero : ∀ k, 1 ≤ k → D.Before f c C P ε₀ ε₁ k → D.xi k 0 = D.X k
  /-- Step 1: the inner run of a reached outer iteration $k$ is an ARp1-CC run on
  $\mu_2(\cdot, t_k)$ with the termination test (7.2.10). -/
  inner_run : ∀ k, 1 ≤ k → D.Before f c C P ε₀ ε₁ k →
    IsARRun P.toARParams (fun i => innerStop f c C P.θ ε₀ ε₁ (D.t k) (D.xi k i))
      (fun i => IsFirstOrderCCStep (Constrained.targetMerit f c (D.t k)) C p P.θ₁ (D.xi k i)
        (D.σi k i) (D.si k i)) (fun _ => False)
      (taylorRatio (Constrained.targetMerit f c (D.t k)) p (D.xi k) (D.si k)) (D.xi k) (D.si k)
      (D.σi k)
  /-- Step 1: the inner run of a reached outer iteration $k$ stops at the first index $e_k$ at which
  (7.2.10) holds. -/
  inner_hit : ∀ k, 1 ≤ k → D.Before f c C P ε₀ ε₁ k →
    IsFirstHit (fun i => innerStop f c C P.θ ε₀ ε₁ (D.t k) (D.xi k i)) (D.e k)
  /-- Step 1: $x_{k+1} = x_{k,e_k}$ for a reached outer iteration $k$. -/
  X_succ : ∀ k, 1 ≤ k → D.Before f c C P ε₀ ε₁ k → D.X (k + 1) = D.xi k (D.e k)
  /-- Step 2(a): if $k \in \mathcal{K}_a$, then $t_{k+1} = f(x_{k+1}) - \sqrt{\epsilon_0^2 -
  \|c(x_{k+1})\|^2}$ (7.2.11). -/
  t_succ_a : ∀ k, 1 ≤ k → D.Before f c C P ε₀ ε₁ k → D.IsKa f c P ε₀ k →
    D.t (k + 1) = f (D.X (k + 1)) - √(ε₀ ^ 2 - ‖c (D.X (k + 1))‖ ^ 2)
  /-- Step 2(b): if $k \in \mathcal{K}_b$, then $t_{k+1} = 2 f(x_{k+1}) - t_k$ (7.2.13). -/
  t_succ_b : ∀ k, 1 ≤ k → D.Before f c C P ε₀ ε₁ k → D.IsKb f c P ε₀ k →
    D.t (k + 1) = 2 * f (D.X (k + 1)) - D.t k

namespace Phase2Seq

variable {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {C : Set ℝⁿ} {P : TPpGCParams} {ε₀ ε₁ : ℝ}
  {D : Phase2Seq n}

/-- An outer iteration in $\mathcal{K}_b$ is not in $\mathcal{K}_a$. -/
theorem IsKb.not_isKa {k : ℕ} (h : D.IsKb f c P ε₀ k) : ¬ D.IsKa f c P ε₀ k :=
  fun ha => absurd ha (not_le.2 h.1)

end Phase2Seq

namespace IsTPpGCPhase2

variable {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {C : Set ℝⁿ} {p : ℕ} {P : TPpGCParams} {ε₀ ε₁ : ℝ}
  {x₁ : ℝⁿ} {D : Phase2Seq n}

section Inner

variable (h : IsTPpGCPhase2 f c C p P ε₀ ε₁ x₁ D) {k : ℕ} (hk1 : 1 ≤ k)
  (hk : D.Before f c C P ε₀ ε₁ k)
include h hk1 hk

/-- For a Phase-2 run and a reached outer iteration $k \ge 1$, no inner iterate $x_{k,i}$ with
$i < e_k$ passes the test (7.2.10). -/
theorem inner_not_stop {i : ℕ} (hi : i < D.e k) :
    ¬ innerStop f c C P.θ ε₀ ε₁ (D.t k) (D.xi k i) :=
  (h.inner_hit k hk1 hk).2 i hi

/-- For a Phase-2 run and a reached outer iteration $k \ge 1$, every inner step $s_{k,i}$ with
$i < e_k$ satisfies the step conditions of ARp1-CC for $\mu_2(\cdot, t_k)$. -/
theorem inner_step {i : ℕ} (hi : i < D.e k) :
    IsFirstOrderCCStep (Constrained.targetMerit f c (D.t k)) C p P.θ₁ (D.xi k i) (D.σi k i)
      (D.si k i) :=
  (h.inner_run k hk1 hk).step_of_forall_le
    (IsARRun.forall_le_not_stop_iff.2 fun _ hj => h.inner_not_stop hk1 hk (hj.trans_lt hi))

/-- For a Phase-2 run and a reached outer iteration $k \ge 1$, the inner regularization parameters
are positive: $\sigma_{k,i} > 0$ for $i \le e_k$. -/
theorem inner_sigma_pos {i : ℕ} (hi : i ≤ D.e k) : 0 < D.σi k i :=
  (h.inner_run k hk1 hk).sigma_pos (K := D.e k)
    (IsARRun.forall_lt_not_stop_iff.2 fun _ hj => h.inner_not_stop hk1 hk hj) i hi

/-- For a Phase-2 run and a reached outer iteration $k \ge 1$ with $x_k \in \mathcal{C}$, the inner
iterates stay in $\mathcal{C}$: $x_{k,i} \in \mathcal{C}$ for $i \le e_k$. -/
theorem inner_mem (hX : D.X k ∈ C) {i : ℕ} (hi : i ≤ D.e k) : D.xi k i ∈ C := by
  refine (h.inner_run k hk1 hk).mem (C := C) (by rw [h.inner_zero k hk1 hk]; exact hX)
    (fun j hj _ _ => ?_) i (IsARRun.forall_lt_not_stop_iff.2 fun _ hj =>
      h.inner_not_stop hk1 hk (hj.trans_le hi))
  exact ((h.inner_run k hk1 hk).step_of_forall_le hj).mem

/-- For a Phase-2 run and a reached outer iteration $k \ge 1$, the merit function is nonincreasing
along the inner run: $\mu_2(x_{k,j}, t_k) \le \mu_2(x_{k,i}, t_k)$ for $i \le j \le e_k$. -/
theorem inner_merit_antitone {i j : ℕ} (hij : i ≤ j) (hj : j ≤ D.e k) :
    Constrained.targetMerit f c (D.t k) (D.xi k j) ≤
      Constrained.targetMerit f c (D.t k) (D.xi k i) := by
  have hK := IsARRun.forall_lt_not_stop_iff.2 fun _ hj => h.inner_not_stop hk1 hk hj
  refine (h.inner_run k hk1 hk).objective_antitone
    (w := Constrained.targetMerit f c (D.t k))
    (pred := fun i => FormalMultilinearSeries.taylorDecrement
      (ftaylorSeries ℝ (Constrained.targetMerit f c (D.t k)) (D.xi k i)) p (D.si k i)) hK
    (fun _ _ => rfl) (fun i hi => ?_) i j hij hj
  have hd := lt_taylorDecrement_of_regularizedModel_lt (h.inner_step hk1 hk hi).decrease
  have := h.inner_sigma_pos hk1 hk hi.le
  exact lt_of_le_of_lt (by positivity) hd

/-- For a Phase-2 run and a reached outer iteration $k \ge 1$, the residual is nonincreasing along
the inner run: $\|r(x_{k,j}, t_k)\| \le \|r(x_{k,i}, t_k)\|$ for $i \le j \le e_k$. -/
theorem inner_resid_antitone {i j : ℕ} (hij : i ≤ j) (hj : j ≤ D.e k) :
    Constrained.targetResidual f c (D.t k) (D.xi k j) ≤
      Constrained.targetResidual f c (D.t k) (D.xi k i) :=
  Constrained.targetMerit_le_targetMerit_iff.1 (h.inner_merit_antitone hk1 hk hij hj)

/-- For a Phase-2 run and a reached outer iteration $k \ge 1$,
$\|r(x_{k+1}, t_k)\| \le \|r(x_k, t_k)\|$. -/
theorem resid_succ_le :
    Constrained.targetResidual f c (D.t k) (D.X (k + 1)) ≤
      Constrained.targetResidual f c (D.t k) (D.X k) := by
  have := h.inner_resid_antitone hk1 hk (Nat.zero_le _) le_rfl
  rwa [← h.X_succ k hk1 hk, h.inner_zero k hk1 hk] at this

/-- For a Phase-2 run and a reached outer iteration $k \ge 1$, an unsuccessful inner iteration
$i < e_k$ does not move: $x_{k,i+1} = x_{k,i}$. -/
theorem inner_stay {i : ℕ} (hi : i < D.e k) (hns : ¬ D.InnerSucc f c p P k i) :
    D.xi k (i + 1) = D.xi k i :=
  (h.inner_run k hk1 hk).eq_of_not_succ
    (IsARRun.forall_le_not_stop_iff.2 fun _ hj => h.inner_not_stop hk1 hk (hj.trans_lt hi))
    (not_le.1 hns)

/-- For a Phase-2 run and a reached outer iteration $k \ge 1$, an inner iterate $x_{k,i}$ with
$i < e_k$ fails the third test of (7.2.10). -/
theorem not_targetCrit_of_lt {i : ℕ} (hi : i < D.e k) :
    ¬ targetCrit f c C ε₁ (D.t k) (D.xi k i) := by
  have hns := h.inner_not_stop hk1 hk hi
  simp only [innerStop, not_or] at hns
  exact hns.2.2

/-- For a Phase-2 run and a reached outer iteration $k \ge 1$, an inner iterate $x_{k,i}$ with
$i < e_k$ has $\|r(x_{k,i}, t_k)\| > \theta \epsilon_0$. -/
theorem lt_residual_of_lt {i : ℕ} (hi : i < D.e k) :
    P.θ * ε₀ < Constrained.targetResidual f c (D.t k) (D.xi k i) := by
  have hns := h.inner_not_stop hk1 hk hi
  simp only [innerStop, not_or, not_le] at hns
  exact hns.1

/-- For a Phase-2 run and a reached outer iteration $k \ge 1$, the new outer iterate $x_{k+1}$
passes the test (7.2.10) for the target $t_k$. -/
theorem innerStop_succ : innerStop f c C P.θ ε₀ ε₁ (D.t k) (D.X (k + 1)) := by
  rw [h.X_succ k hk1 hk]
  exact (h.inner_hit k hk1 hk).1

end Inner

variable (h : IsTPpGCPhase2 f c C p P ε₀ ε₁ x₁ D)
include h

/-- For a Phase-2 run, every reached outer iterate lies in $\mathcal{C}$: $x_k \in \mathcal{C}$ for
every reached $k \ge 1$. -/
theorem X_mem : ∀ k, 1 ≤ k → D.Before f c C P ε₀ ε₁ k → D.X k ∈ C := by
  intro k hk1
  induction k, hk1 using Nat.le_induction with
  | base => intro _; rw [h.X_one]; exact h.mem_one
  | succ k hk1 ih =>
    intro hk
    have hk' := hk.mono k.le_succ
    rw [h.X_succ k hk1 hk']
    exact h.inner_mem hk1 hk' (ih hk') le_rfl

/-- Phase 2 of TPp-GC is a run of the target-following outer loop of the backbone. For a Phase-2 run
from $x_1$, the data `CartisGouldToint.Chapter07.Phase2Seq.toTargetFollowingSeq` satisfies
`Constrained.IsTargetFollowingRun` with the factor $\theta$, the tolerance $\epsilon_0$ and the
set $\mathcal{C}$.

The run uses the corrected test $\|r(x_{k+1}, t_k)\| \le \theta \epsilon_0$ of Step 2(a). -/
theorem toRun :
    Constrained.IsTargetFollowingRun f c P.θ ε₀ C x₁ (D.toTargetFollowingSeq f c C P ε₀ ε₁) where
  θ_pos := P.θ_pos
  θ_lt_one := P.θ_lt_one
  ε₀_pos := h.tol.ε₀_pos
  ε₀_le_one := h.tol.ε₀_le_one
  residual_le_of_ka _ ha := ha
  le_residual_of_not_ka _ ha := (not_le.1 ha).le
  kb_iff _ := and_congr_left' not_le.symm
  mem_one := h.mem_one
  norm_one_le := h.norm_one_le
  x_one := h.X_one
  t_one := h.t_one
  mem_succ k hk1 hk := by
    change D.X (k + 1) ∈ C
    rw [h.X_succ k hk1 hk]
    exact h.inner_mem hk1 hk (h.X_mem k hk1 hk) le_rfl
  output k hk1 hk := h.innerStop_succ hk1 hk
  inner_zero := h.inner_zero
  inner_end k hk1 hk := (h.X_succ k hk1 hk).symm
  inner_mono k hk1 hk i hi := h.inner_resid_antitone hk1 hk i.le_succ hi
  inner_residual_ge k hk1 hk i hi := (h.lt_residual_of_lt hk1 hk hi).le
  t_succ_a := h.t_succ_a
  t_succ_b := h.t_succ_b

/-- For a Phase-2 run and every reached outer iteration $K$, the outer iterates and targets form a
target sequence (`Constrained.IsTargetSequence`) up to $K$, with $\mathcal{K}_a$ given by
`CartisGouldToint.Chapter07.Phase2Seq.IsKa`. -/
theorem isTargetSequence {K : ℕ} (hK : D.Before f c C P ε₀ ε₁ K) :
    Constrained.IsTargetSequence f c P.θ ε₀ D.X D.t (D.IsKa f c P ε₀) K :=
  h.toRun.isTargetSequence hK

end IsTPpGCPhase2

/-! ### Lemmas 7.2.3–7.2.5 -/

section Lemmas

variable {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {C : Set ℝⁿ} {p : ℕ} {P : TPpGCParams} {ε₀ ε₁ : ℝ}
  {x₁ : ℝⁿ} {D : Phase2Seq n}

/-- **Lemma 7.2.3** of [cartis2022evaluation]. Consider a Phase-2 run of TPp-GC and a reached outer
iteration $K$. Then:

* $t_{k+1} < t_k$ for $k \in [1, K)$;
* $0 \le f(x_k) - t_k \le \epsilon_0$ and $\|c(x_k)\| \le \epsilon_0$ for $k \in [1, K]$
  ((7.2.26), (7.2.29));
* if $k \in [1, K)$ is in $\mathcal{K}_a$, then $\|r(x_{k+1}, t_{k+1})\| = \epsilon_0$ and
  $t_k - t_{k+1} \ge (1 - \theta) \epsilon_0$ ((7.2.27), (7.2.30));
* if $k \in [1, K)$ is in $\mathcal{K}_b$, then $\|r(x_{k+1}, t_{k+1})\| = \|r(x_{k+1}, t_k)\|
  \le \epsilon_0$ ((7.2.28));
* if f.B.Fb holds with parameter $\beta$ and constants $f_{\mathrm{low}}, f_{\mathrm{up}}$, then
  $t_k \in [f_{\mathrm{low}} - 1, f_{\mathrm{up}}]$ for $k \in [1, K]$ ((7.2.31)). -/
theorem lemma_7_2_3 (h : IsTPpGCPhase2 f c C p P ε₀ ε₁ x₁ D) {K : ℕ}
    (hK : D.Before f c C P ε₀ ε₁ K) :
    (∀ k, 1 ≤ k → k < K → D.t (k + 1) < D.t k) ∧
    (∀ k, 1 ≤ k → k ≤ K →
      0 ≤ f (D.X k) - D.t k ∧ f (D.X k) - D.t k ≤ ε₀ ∧ ‖c (D.X k)‖ ≤ ε₀) ∧
    (∀ k, 1 ≤ k → k < K → D.IsKa f c P ε₀ k →
      Constrained.targetResidual f c (D.t (k + 1)) (D.X (k + 1)) = ε₀ ∧
        (1 - P.θ) * ε₀ ≤ D.t k - D.t (k + 1)) ∧
    (∀ k, 1 ≤ k → k < K → D.IsKb f c P ε₀ k →
      Constrained.targetResidual f c (D.t (k + 1)) (D.X (k + 1)) =
          Constrained.targetResidual f c (D.t k) (D.X (k + 1)) ∧
        Constrained.targetResidual f c (D.t (k + 1)) (D.X (k + 1)) ≤ ε₀) ∧
    (∀ flow fup, AssumptionBFb f c C P.β flow fup →
      ∀ k, 1 ≤ k → k ≤ K → D.t k ∈ Icc (flow - 1) fup) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := (h.isTargetSequence hK).props P.θ_pos.le P.θ_lt_one h.tol.ε₀_pos
  refine ⟨h1, h2, h3, fun k hk1 hkK hb => h4 k hk1 hkK hb.not_isKa, fun flow fup hB =>
    h5 h.tol.ε₀_le_one C flow fup (fun k hk1 hkK => h.X_mem k hk1 (hK.mono hkK))
      (hB.of_le h.tol.ε₀_le_β)⟩

/-- **Lemma 7.2.4** of [cartis2022evaluation]. Assume f.B.Fb with parameter $\beta$ and constants
$f_{\mathrm{low}}, f_{\mathrm{up}}$. For a Phase-2 run of TPp-GC and every reached outer
iteration $K \ge 1$, the number of outer iterations $k \in [1, K)$ in $\mathcal{K}_a$ satisfies
$$|\mathcal{K}_a \cap [1, K)| \le \frac{f_{\mathrm{up}} - f_{\mathrm{low}} + 1}{(1 - \theta)
  \epsilon_0}.$$
-/
theorem lemma_7_2_4 (h : IsTPpGCPhase2 f c C p P ε₀ ε₁ x₁ D) {flow fup : ℝ}
    (hB : AssumptionBFb f c C P.β flow fup) {K : ℕ} (hK1 : 1 ≤ K)
    (hK : D.Before f c C P ε₀ ε₁ K) [DecidablePred (D.IsKa f c P ε₀)] :
    (((Finset.Ico 1 K).filter (D.IsKa f c P ε₀)).card : ℝ) ≤
      (fup - flow + 1) / ((1 - P.θ) * ε₀) :=
  (h.isTargetSequence hK).card_Ka_le P.θ_pos.le P.θ_lt_one h.tol.ε₀_pos h.tol.ε₀_le_one hK1
    (fun k hk1 hkK => h.X_mem k hk1 (hK.mono hkK)) (hB.of_le h.tol.ε₀_le_β)

/-- **Lemma 7.2.5** of [cartis2022evaluation], first part. Assume $\mu_2$.DpL.C and $p \ge 1$. For
every interval $[a, b]$ there is $L_\mu \ge 0$ such that $\mu_2(\cdot, t)$ satisfies f.DpL.C on
$\mathcal{C}$ with constant $L_\mu$ for every $t \in [a, b]$.

**Generalization.** The source also lists the hypothesis $\Phi_\ell$.DpL.C, which is not needed.

The lemma is applied with $[a, b] = [f_{\mathrm{low}} - 1, f_{\mathrm{up}}]$, which contains all
targets by Lemma 7.2.3. The constant is $\max(L_a, L_b)$, because $\mu_2(\cdot, t)$ is affine in
$t$ up to a term that does not depend on $x$; the "continuous dependence on $t$" of the source
would not suffice. -/
theorem lemma_7_2_5 (hμ : AssumptionMu2DpLC f c C p) (hp : 1 ≤ p) (a b : ℝ) :
    ∃ Lμ, 0 ≤ Lμ ∧ ∀ t ∈ Icc a b,
      Chapter06.AssumptionDpLC (Constrained.targetMerit f c t) C p Lμ := by
  obtain ⟨L₁, h₁⟩ := hμ a
  obtain ⟨L₂, h₂⟩ := hμ b
  refine ⟨max L₁ L₂, le_max_of_le_left h₁.nonneg, fun t ht => ⟨le_max_of_le_left h₁.nonneg, ?_,
    Constrained.iteratedFDerivHolderOn_targetMerit_of_mem_Icc (by omega) ht h₁.contDiffAt
      h₂.contDiffAt h₁.lipschitz h₂.lipschitz⟩⟩
  rcases ht.1.eq_or_lt with rfl | hat
  · exact h₁.contDiffOn
  obtain ⟨D₁, hD₁, hCD₁, hf₁⟩ := h₁.contDiffOn
  obtain ⟨D₂, hD₂, hCD₂, hf₂⟩ := h₂.contDiffOn
  refine ⟨D₁ ∩ D₂, hD₁.inter hD₂, subset_inter hCD₁ hCD₂, ?_⟩
  rw [Constrained.targetMerit_eq_lineMap (hat.trans_le ht.2)]
  exact (((hf₁.mono inter_subset_left).const_smul _).add
    ((hf₂.mono inter_subset_right).const_smul _)).add contDiffOn_const

end Lemmas

/-! ### Lemma 7.2.1 -/

section Termination

variable {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {C : Set ℝⁿ} {p : ℕ} {P : TPpGCParams} {ε₀ ε₁ : ℝ}
  {x₁ : ℝⁿ} {D : Phase2Seq n}

/-- **Equations (7.2.17) and (7.2.20)** of [cartis2022evaluation]. Let Phase 2 of TPp-GC terminate
at outer iteration $k_\epsilon$, with output $x_\epsilon = x_{k_\epsilon+1}$ and output target
$t_\epsilon$. Then $x_\epsilon \in \mathcal{C}$,
$$\theta \epsilon_0 < \|r(x_\epsilon, t_\epsilon)\| \le \epsilon_0, \qquad f(x_\epsilon) \ge
  t_\epsilon, \qquad \omega_{\mu_2,\mathcal{C},1}(x_\epsilon, t_\epsilon) \le \epsilon_1
  \|r(x_\epsilon, t_\epsilon)\|.$$

The strict lower bound uses the corrected test of Step 2(a)
(`CartisGouldToint.Chapter07.Phase2Seq.IsKa`). -/
theorem IsTPpGCPhase2.output_spec (h : IsTPpGCPhase2 f c C p P ε₀ ε₁ x₁ D) {kε : ℕ}
    (hend : D.IsEnd f c C P ε₀ ε₁ kε) :
    D.X (kε + 1) ∈ C ∧
      P.θ * ε₀ < Constrained.targetResidual f c (D.targetOut f c P ε₀ kε) (D.X (kε + 1)) ∧
      Constrained.targetResidual f c (D.targetOut f c P ε₀ kε) (D.X (kε + 1)) ≤ ε₀ ∧
      D.targetOut f c P ε₀ kε ≤ f (D.X (kε + 1)) ∧
      targetCrit f c C ε₁ (D.targetOut f c P ε₀ kε) (D.X (kε + 1)) := by
  classical
  obtain ⟨hX, -, hup, hle, hcrit⟩ := h.toRun.output_spec hend
  refine ⟨hX, ?_, hup, hle, hcrit⟩
  have hr : Constrained.targetResidual f c (D.targetOut f c P ε₀ kε) (D.X (kε + 1)) =
      if D.IsKa f c P ε₀ kε then ε₀ else Constrained.targetResidual f c (D.t kε) (D.X (kε + 1)) :=
    h.toRun.residual_targetOut hend.1 hend.2.2
  rw [hr]
  split_ifs with ha
  · have := P.θ_lt_one; have := h.tol.ε₀_pos; nlinarith
  · exact not_le.1 ha

/-- **Lemma 7.2.1** of [cartis2022evaluation], Phase 2. Let $f$ and $c$ be differentiable at every
point of $\mathcal{C}$. Let Phase 2 of TPp-GC terminate at outer iteration $k_\epsilon$, with
output $x_\epsilon = x_{k_\epsilon+1}$ and output target $t_\epsilon$. Then one of the following
holds:

* $f(x_\epsilon) = t_\epsilon$, $\omega_{\Phi_2,\mathcal{C},1}(x_\epsilon) \le \epsilon_1
  \|c(x_\epsilon)\|$ and $\|c(x_\epsilon)\| > \theta \epsilon_0$, where
  $\Phi_2 = \frac{1}{2} \|c\|^2$ (7.2.15);
* $f(x_\epsilon) > t_\epsilon$, and $x_\epsilon$ is an $(\epsilon_0, \epsilon_1)$-approximate
  first-order minimizer of (7.1.1) in the sense of (7.1.4), with the multiplier $y_\epsilon =
  -c(x_\epsilon) / (f(x_\epsilon) - t_\epsilon)$ ((7.2.16), (7.2.22)).

The printed proof gives only $\|c(x_\epsilon)\| \ge \theta \epsilon_0$ in (7.2.15); the strict
inequality follows from the corrected test of Step 2(a). The output also satisfies (7.2.17) and
(7.2.20) (`CartisGouldToint.Chapter07.IsTPpGCPhase2.output_spec`). The approximate minimizer is
`CartisGouldToint.Chapter07.IsApproxFirstOrderGC`, and the multiplier is
`Constrained.targetMultiplier`. -/
theorem lemma_7_2_1_phase2 (h : IsTPpGCPhase2 f c C p P ε₀ ε₁ x₁ D)
    (hf : ∀ x ∈ C, DifferentiableAt ℝ f x) (hc : ∀ x ∈ C, DifferentiableAt ℝ c x) {kε : ℕ}
    (hend : D.IsEnd f c C P ε₀ ε₁ kε) :
    (f (D.X (kε + 1)) = D.targetOut f c P ε₀ kε ∧
        Chapter06.omega1 (fun z => ‖c z‖ ^ 2 / 2) C (D.X (kε + 1)) ≤ ε₁ * ‖c (D.X (kε + 1))‖ ∧
        P.θ * ε₀ < ‖c (D.X (kε + 1))‖) ∨
      (D.targetOut f c P ε₀ kε < f (D.X (kε + 1)) ∧
        IsApproxFirstOrderGC f c C ε₀ ε₁ (D.X (kε + 1))
          (Constrained.targetMultiplier f c (D.targetOut f c P ε₀ kε) (D.X (kε + 1)))) := by
  obtain ⟨hX, hlow, hup, hle, hcrit⟩ := h.output_spec hend
  set x := D.X (kε + 1)
  set τ := D.targetOut f c P ε₀ kε
  rcases hle.eq_or_lt with heq | hlt
  · -- `f(x_ε) = t_ε`
    have hr : Constrained.targetResidual f c τ x = ‖c x‖ := by
      rw [heq]; exact Constrained.targetResidual_self
    refine Or.inl ⟨heq.symm, ?_, hr ▸ hlow⟩
    have hD : iteratedFDeriv ℝ 1 (Constrained.targetMerit f c τ) x =
        iteratedFDeriv ℝ 1 (fun z => ‖c z‖ ^ 2 / 2) x := by
      ext m
      rw [iteratedFDeriv_one_apply, iteratedFDeriv_one_apply,
        Constrained.fderiv_targetMerit_of_eq (hf x hX) (hc x hX) heq.symm]
    have := hcrit
    rw [targetCrit, Chapter06.omega1_def, hD, hr] at this
    exact this
  · -- `f(x_ε) > t_ε`
    refine Or.inr ⟨hlt, hX, Constrained.norm_le_targetResidual.trans hup, ?_⟩
    have hτ : 0 < f x - τ := sub_pos.2 hlt
    have heq := Constrained.formCriticality_targetMerit_eq_mul (hf x hX) (hc x hX) hlt
      (feasibleSteps C x)
    have hcr := hcrit
    rw [targetCrit, Chapter06.omega1_def, heq] at hcr
    rw [omegaL_def, Chapter06.omega1_def, ← Constrained.targetResidual_div_eq_sqrt hlt,
      mul_div_assoc', le_div_iff₀ hτ]
    simp only [lagrangianVec_def]
    linarith
end Termination

/-! ### Counting the inner iterations of Phase 2 (Lemma 7.2.6) -/

/-- **Equation (7.2.47)** of [cartis2022evaluation]. For the constants $P$ of TPp-GC, a Lipschitz
constant $L_\mu$ and $p \in \mathbb{N}$, the constant is
$$\kappa^S_{\mathrm{ARpGC}} = \kappa_1^{-1} \theta^{-(p+1)/p}, \qquad \kappa_1 = \frac{\eta_1
  \sigma_{\min}}{(p+1)!} \left(\frac{p!}{L_\mu + \sigma_{\mu,\max} + \theta_1
  p!}\right)^{(p+1)/p},$$
with $\kappa_1$ the constant of Lemma 6.2.4 (`CartisGouldToint.Chapter06.kappa1CC`) for the
merit functions $\mu_2(\cdot, t)$ and $\sigma_{\mu,\max} = \max(\sigma_0, \gamma_3 L_\mu / (1 -
\eta_2))$.

**Generalization.** The source has the weaker factor $\theta^{-(p+2)/p}$. The good iterations
are counted here by one telescoping over all outer iterations, which gives the factor
$\theta^{-(p+1)/p}$. -/
noncomputable def kappaSGC (P : TPpGCParams) (Lμ : ℝ) (p : ℕ) : ℝ :=
  (Chapter06.kappa1CC P.toARpCCParams Lμ p)⁻¹ * P.θ ^ (-(((p : ℝ) + 1) / p))

/-- **Equation (7.2.39)** of [cartis2022evaluation]. The bound on the number of good inner
iterations between two consecutive iterations of $\mathcal{K}_a$ is
$$G = \kappa^S_{\mathrm{ARpGC}} (1 - \theta) \epsilon_0^{(p-1)/p} \epsilon_1^{-(p+1)/p}.$$
-/
noncomputable def goodBound (P : TPpGCParams) (Lμ : ℝ) (p : ℕ) (ε₀ ε₁ : ℝ) : ℝ :=
  kappaSGC P Lμ p * (1 - P.θ) * ε₀ ^ (((p : ℝ) - 1) / p) * ε₁ ^ (-(((p : ℝ) + 1) / p))

/-- The decrease of the residual on a good inner iteration:
$$\delta = \kappa_1 \theta^{(p+1)/p} \epsilon_0^{1/p} \epsilon_1^{(p+1)/p}.$$
It satisfies $G = (1 - \theta) \epsilon_0 / \delta$ (`CartisGouldToint.Chapter07.goodBound_eq`). -/
noncomputable def goodDecr (P : TPpGCParams) (Lμ : ℝ) (p : ℕ) (ε₀ ε₁ : ℝ) : ℝ :=
  Chapter06.kappa1CC P.toARpCCParams Lμ p * P.θ ^ (((p : ℝ) + 1) / p) *
    (ε₀ ^ (((p : ℝ) + 1) / p - 1) * ε₁ ^ (((p : ℝ) + 1) / p))

/-- If $L_\mu \ge 0$, $\epsilon_0 > 0$ and $\epsilon_1 > 0$, then the decrease $\delta$ is positive.
-/
theorem goodDecr_pos {P : TPpGCParams} {Lμ ε₀ ε₁ : ℝ} (hL : 0 ≤ Lμ) (p : ℕ)
    (hε₀ : 0 < ε₀) (hε₁ : 0 < ε₁) : 0 < goodDecr P Lμ p ε₀ ε₁ := by
  have := Chapter06.kappa1CC_pos (P := P.toARpCCParams) (p := p) hL; have := P.θ_pos
  unfold goodDecr; positivity

/-- If $L_\mu \ge 0$, $p \ge 1$, $\epsilon_0 > 0$ and $\epsilon_1 > 0$, then
$G = (1 - \theta) \epsilon_0 / \delta$. -/
theorem goodBound_eq {P : TPpGCParams} {Lμ ε₀ ε₁ : ℝ} (hL : 0 ≤ Lμ) {p : ℕ}
    (hp : 1 ≤ p) (hε₀ : 0 < ε₀) (hε₁ : 0 < ε₁) :
    goodBound P Lμ p ε₀ ε₁ = (1 - P.θ) * ε₀ / goodDecr P Lμ p ε₀ ε₁ := by
  have hκ := Chapter06.kappa1CC_pos (P := P.toARpCCParams) (p := p) hL
  have hθ := P.θ_pos
  have h1 : ε₀ ^ (((p : ℝ) - 1) / p) = ε₀ ^ (1 : ℝ) / ε₀ ^ (((p : ℝ) + 1) / p - 1) := by
    rw [← Real.rpow_sub hε₀]
    congr 1
    have : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    field_simp; ring
  rw [goodBound, goodDecr, kappaSGC, Real.rpow_neg hθ.le, Real.rpow_neg hε₁.le, h1,
    Real.rpow_one]
  have : 0 < ε₀ ^ (((p : ℝ) + 1) / p - 1) := by positivity
  have : 0 < ε₁ ^ (((p : ℝ) + 1) / p) := by positivity
  have : 0 < P.θ ^ (((p : ℝ) + 1) / p) := by positivity
  field_simp

namespace IsTPpGCPhase2

section Counting

variable {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {C : Set ℝⁿ} {p : ℕ} {P : TPpGCParams} {ε₀ ε₁ : ℝ}
  {x₁ : ℝⁿ} {D : Phase2Seq n} (h : IsTPpGCPhase2 f c C p P ε₀ ε₁ x₁ D)
  {flow fup Lμ : ℝ} (hB : AssumptionBFb f c C P.β flow fup)
  (hL : ∀ t ∈ Icc (flow - 1) fup,
    Chapter06.AssumptionDpLC (Constrained.targetMerit f c t) C p Lμ)

include h hB in
/-- Assume f.B.Fb with parameter $\beta$ and constants $f_{\mathrm{low}}, f_{\mathrm{up}}$. For a
Phase-2 run, the target of every reached outer iteration $k \ge 1$ lies in
$[f_{\mathrm{low}} - 1, f_{\mathrm{up}}]$ ((7.2.31)). -/
theorem t_mem {k : ℕ} (hk1 : 1 ≤ k) (hk : D.Before f c C P ε₀ ε₁ k) :
    D.t k ∈ Icc (flow - 1) fup :=
  (lemma_7_2_3 h hk).2.2.2.2 flow fup hB k hk1 le_rfl

include h hB hL in
/-- Assume f.B.Fb and that $\mu_2(\cdot, t)$ satisfies f.DpL.C with constant $L_\mu$ for every
$t \in [f_{\mathrm{low}} - 1, f_{\mathrm{up}}]$. Then for a Phase-2 run, $L_\mu \ge 0$. -/
theorem Lμ_nonneg : 0 ≤ Lμ :=
  (hL _ (h.t_mem hB le_rfl Constrained.TargetFollowingSeq.before_one)).nonneg

include h hB hL in
/-- **Lemma 7.2.5** of [cartis2022evaluation], second part. Assume C.CNe and f.B.Fb, and that
$\mu_2(\cdot, t)$ satisfies f.DpL.C with constant $L_\mu$ for every
$t \in [f_{\mathrm{low}} - 1, f_{\mathrm{up}}]$. For a Phase-2 run of TPp-GC and a reached outer
iteration $k \ge 1$, the inner regularization parameters satisfy
$$\sigma_{\min} \le \sigma_{k,i} \le \sigma_{\mu,\max} = \max\left(\sigma_0, \frac{\gamma_3
  L_\mu}{1 - \eta_2}\right) \quad \text{for } i \le e_k.$$
-/
theorem inner_sigma_le (hC : Chapter06.AssumptionCNe C) {k : ℕ} (hk1 : 1 ≤ k)
    (hk : D.Before f c C P ε₀ ε₁ k) {i : ℕ} (hi : i ≤ D.e k) :
    P.σmin ≤ D.σi k i ∧ D.σi k i ≤ P.toARpCCParams.sigmaMax Lμ :=
  (Chapter06.arpcc_sigma_le (P := P.toARpCCParams) (h.inner_run k hk1 hk) hC
    (hL _ (h.t_mem hB hk1 hk)) (by rw [h.inner_zero k hk1 hk]; exact h.X_mem k hk1 hk)
    (fun _ hs => ⟨hs.mem, hs.decrease⟩) i
    (fun _ hj => h.inner_not_stop hk1 hk (hj.trans_le hi))).2

include h hB hL in
/-- The residual decrease of a good inner iteration ((7.2.43) and the display after (7.2.46) of
[cartis2022evaluation]). Assume C.CNe, f.B.Fb, $p \ge 1$, and that $\mu_2(\cdot, t)$ satisfies
f.DpL.C with constant $L_\mu$ for every $t \in [f_{\mathrm{low}} - 1, f_{\mathrm{up}}]$.
Consider a Phase-2 run, a reached outer iteration $k \ge 1$, a tolerance $e_1 > 0$, and a
successful inner iteration $i < e_k$ whose new iterate $y = x_{k,i+1}$ has
$\omega_{\mu_2,\mathcal{C},1}(y, t_k) > e_1 \|r(y, t_k)\|$ and
$\|r(y, t_k)\| \ge \theta \epsilon_0$. Then
$$\|r(x_{k,i}, t_k)\| - \|r(y, t_k)\| \ge \kappa_1 \theta^{(p+1)/p} \epsilon_0^{1/p}
  e_1^{(p+1)/p}.$$
-/
theorem decrease_of_not_targetCrit (hC : Chapter06.AssumptionCNe C) (hp : 1 ≤ p) {k : ℕ}
    (hk1 : 1 ≤ k) (hk : D.Before f c C P ε₀ ε₁ k) {i : ℕ} (hi : i < D.e k)
    (hs : D.InnerSucc f c p P k i) {e₁ : ℝ} (he₁ : 0 < e₁)
    (hncrit : ¬ targetCrit f c C e₁ (D.t k) (D.xi k (i + 1)))
    (hlow : P.θ * ε₀ ≤ Constrained.targetResidual f c (D.t k) (D.xi k (i + 1))) :
    goodDecr P Lμ p ε₀ e₁ ≤ Constrained.targetResidual f c (D.t k) (D.xi k i) -
      Constrained.targetResidual f c (D.t k) (D.xi k (i + 1)) := by
  have hdpl := hL _ (h.t_mem hB hk1 hk)
  have hxi := h.inner_mem hk1 hk (h.X_mem k hk1 hk) hi.le
  have hσ := h.inner_sigma_le hB hL hC hk1 hk hi.le
  have hsucc : D.xi k (i + 1) = D.xi k i + D.si k i :=
    (h.inner_run k hk1 hk).eq_add_of_succ
      (IsARRun.forall_le_not_stop_iff.2 fun _ hj => h.inner_not_stop hk1 hk (hj.trans_lt hi)) hs
  have hdec := (h.inner_step hk1 hk hi).sub_ge hC.convex hdpl.contDiffAt hdpl.lipschitz
    hdpl.nonneg hxi hp P.θ₁_pos.le P.σmin_nonneg hσ.1 hσ.2 P.η₁_pos hs
  rw [← hsucc] at hdec
  set ρ := Constrained.targetResidual f c (D.t k) (D.xi k i)
  set ρ' := Constrained.targetResidual f c (D.t k) (D.xi k (i + 1))
  have hω : e₁ * ρ' < Chapter06.omega1 (Constrained.targetMerit f c (D.t k)) C (D.xi k (i + 1)) :=
    lt_of_not_ge hncrit
  have hπ : 0 ≤ ((p : ℝ) + 1) / p := by positivity
  have hκ := Chapter06.kappa1CC_pos (P := P.toARpCCParams) (p := p) hdpl.nonneg
  have key : Chapter06.kappa1CC P.toARpCCParams Lμ p * (ρ' * e₁) ^ (((p : ℝ) + 1) / p) ≤
      ρ ^ 2 / 2 - ρ' ^ 2 / 2 := by
    rw [← Constrained.targetMerit_eq, ← Constrained.targetMerit_eq]
    refine le_trans ?_ hdec
    rw [Chapter06.kappa1CC_def]
    gcongr
    · exact hκ.le
    · exact mul_nonneg Constrained.targetResidual_nonneg he₁.le
    rw [mul_comm]
    exact hω.le
  have hρle : ρ ≤ ε₀ :=
    (h.inner_resid_antitone hk1 hk (Nat.zero_le i) hi.le).trans (by
      rw [h.inner_zero k hk1 hk]
      exact h.toRun.residual_le hk1 hk)
  exact Constrained.sub_ge_of_residual_decrease P.θ_pos P.θ_lt_one.le h.tol.ε₀_pos hκ hπ le_rfl
    he₁ hlow (h.inner_resid_antitone hk1 hk i.le_succ hi) hρle key

include h hB hL in
/-- Lemma 2.4.1 of [cartis2022evaluation] for one inner run. Assume C.CNe, f.B.Fb, and that
$\mu_2(\cdot, t)$ satisfies f.DpL.C with constant $L_\mu$ for every
$t \in [f_{\mathrm{low}} - 1, f_{\mathrm{up}}]$. For a Phase-2 run and a reached outer iteration
$k \ge 1$,
$$e_k \le A_1 |\{\text{successful iterations of run } k\}| + C_1, \qquad A_1 = 1 + \frac{|\log
  \gamma_1|}{\log \gamma_2}, \quad C_1 = \frac{\log(\sigma_{\mu,\max} / \sigma_0)}{\log
  \gamma_2}.$$

The bound holds per run because the regularization parameter restarts at $\sigma_0$ in every
inner run. -/
theorem e_le (hC : Chapter06.AssumptionCNe C) {k : ℕ} (hk1 : 1 ≤ k)
    (hk : D.Before f c C P ε₀ ε₁ k) :
    (D.e k : ℝ) ≤ (1 + |Real.log P.γ₁| / Real.log P.γ₂) * D.succCount f c p P k +
      Real.log (P.toARpCCParams.sigmaMax Lμ / P.σ₀) / Real.log P.γ₂ := by
  classical
  have hlog := P.toARParams.log_γ₂_pos
  have hC₁ : 0 ≤ Real.log (P.toARpCCParams.sigmaMax Lμ / P.σ₀) / Real.log P.γ₂ :=
    div_nonneg (Real.log_nonneg ((one_le_div P.σ₀_pos).2 (σ₀_le_arSigmaMax _ _))) hlog.le
  rcases hN : D.e k with _ | N
  · simp only [CharP.cast_eq_zero]
    have : 0 ≤ (1 + |Real.log P.γ₁| / Real.log P.γ₂) * (D.succCount f c p P k : ℝ) := by
      positivity
    linarith
  · have hle : ∀ j ≤ N, ¬ IsARRun.Stop
        (fun i => innerStop f c C P.θ ε₀ ε₁ (D.t k) (D.xi k i)) (fun _ => False) j :=
      IsARRun.forall_le_not_stop_iff.2 fun j hj => h.inner_not_stop hk1 hk (by omega)
    have := (h.inner_run k hk1 hk).succ_count hle
      (h.inner_sigma_le hB hL hC hk1 hk (by omega)).2
    have hS : successSet (fun j => P.η₁ ≤
        taylorRatio (Constrained.targetMerit f c (D.t k)) p (D.xi k) (D.si k) j) N =
        (Finset.range (D.e k)).filter (D.InnerSucc f c p P k) := by
      rw [successSet_eq_filter, hN]; rfl
    rw [hS] at this
    rw [Phase2Seq.succCount, Constrained.TargetFollowingSeq.succCount_eq_card_filter]
    dsimp only [Phase2Seq.toCountSeq]
    push_cast
    linarith

include h hB hL in
/-- The inner runs of Phase 2 satisfy the contract of the target-following outer loop. Assume C.CNe,
f.B.Fb, $p \ge 1$, and that $\mu_2(\cdot, t)$ satisfies f.DpL.C with constant $L_\mu$ for every
$t \in [f_{\mathrm{low}} - 1, f_{\mathrm{up}}]$. For every tolerance $e_1 \in (0, \epsilon_1]$
of the exemption test, a Phase-2 run satisfies `Constrained.TargetFollowingSeq.IsInnerContract`:
for every reached outer iteration, $e_k \le A_1 |\{\text{successful iterations of run } k\}| +
C_1$ (Lemma 2.4.1), unsuccessful inner iterations do not move, and every good iteration lowers
the residual by at least $\kappa_1 \theta^{(p+1)/p} \epsilon_0^{1/p} e_1^{(p+1)/p}$ (Lemma
6.2.4). -/
theorem toContract (hC : Chapter06.AssumptionCNe C) (hp : 1 ≤ p) {e₁ : ℝ} (he₁ : 0 < e₁)
    (he₁ε : e₁ ≤ ε₁) :
    (D.toTargetFollowingSeq f c C P ε₀ ε₁).IsInnerContract f c P.θ ε₀ (D.InnerSucc f c p P)
      (D.Exempt f c C P ε₀ e₁) (goodDecr P Lμ p ε₀ e₁)
      (1 + |Real.log P.γ₁| / Real.log P.γ₂)
      (Real.log (P.toARpCCParams.sigmaMax Lμ / P.σ₀) / Real.log P.γ₂) where
  count k hk1 hk := h.e_le hB hL hC hk1 hk
  stay k hk1 hk i hi hns := h.inner_stay hk1 hk hi hns
  decrease k hk1 hk i hg := by
    obtain ⟨hi, hs, hcont, hlow⟩ := hg
    change i < D.e k at hi
    change i + 1 < D.e k ∨ ¬ D.Exempt f c C P ε₀ e₁ k at hcont
    refine h.decrease_of_not_targetCrit hB hL hC hp hk1 hk hi hs he₁ ?_ hlow
    by_cases hi1 : i + 1 < D.e k
    · have hns := h.inner_not_stop hk1 hk hi1
      simp only [innerStop, not_or, not_le] at hns
      exact fun hcr => absurd (hcr.trans (by gcongr; exact Constrained.targetResidual_nonneg))
        (not_le.2 hns.2.2)
    · have he : i + 1 = D.e k := by omega
      rw [he, ← h.X_succ k hk1 hk]
      exact fun hcr => hcont.resolve_left hi1 (Or.inr hcr)

end Counting

section Good

variable {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {C : Set ℝⁿ} {p : ℕ} {P : TPpGCParams} {ε₀ ε₁ : ℝ}
  {x₁ : ℝⁿ} {D : Phase2Seq n} (h : IsTPpGCPhase2 f c C p P ε₀ ε₁ x₁ D)
include h

/-- The good iterations of Phase 2. For a Phase-2 run and a reached outer iteration $k \ge 1$, an
inner iteration $(k, i)$ is good (`CartisGouldToint.Chapter07.Phase2Seq.IsGood`) if and only if
$i < e_k$, iteration $i$ is successful, $x_{k,i+1}$ fails the third test of (7.2.10), and
$\|r(x_{k,i+1}, t_k)\| > \theta \epsilon_0$. -/
theorem isGood_iff {k : ℕ} (hk1 : 1 ≤ k) (hk : D.Before f c C P ε₀ ε₁ k) {i : ℕ} :
    D.IsGood f c C p P ε₀ ε₁ k i ↔ i < D.e k ∧ D.InnerSucc f c p P k i ∧
      ¬ targetCrit f c C ε₁ (D.t k) (D.xi k (i + 1)) ∧
        P.θ * ε₀ < Constrained.targetResidual f c (D.t k) (D.xi k (i + 1)) := by
  constructor
  · rintro ⟨hi, hs, hcont, -⟩
    change i < D.e k at hi
    change i + 1 < D.e k ∨ ¬ D.Exempt f c C P ε₀ ε₁ k at hcont
    by_cases hi1 : i + 1 < D.e k
    · exact ⟨hi, hs, h.not_targetCrit_of_lt hk1 hk hi1, h.lt_residual_of_lt hk1 hk hi1⟩
    · have he : i + 1 = D.e k := by omega
      have hex := hcont.resolve_left hi1
      simp only [Phase2Seq.Exempt, not_or, Phase2Seq.IsKa, not_le] at hex
      have hx : D.xi k (i + 1) = D.X (k + 1) := by rw [he, h.X_succ k hk1 hk]
      exact ⟨hi, hs, by rw [hx]; exact hex.2, by rw [hx]; exact hex.1⟩
  · rintro ⟨hi, hs, hnc, hlt⟩
    refine ⟨hi, hs, ?_, hlt.le⟩
    by_cases hi1 : i + 1 < D.e k
    · exact Or.inl hi1
    · have he : i + 1 = D.e k := by omega
      rw [he, ← h.X_succ k hk1 hk] at hnc hlt
      exact Or.inr fun hex => hex.elim (fun ha => absurd ha (not_le.2 hlt)) hnc

/-- For a Phase-2 run and a reached outer iteration $k \ge 1$ that is bad, the new iterate passes
the third test of (7.2.10) for the old target: $\omega_{\mu_2,\mathcal{C},1}(x_{k+1}, t_k) \le
\epsilon_1 \|r(x_{k+1}, t_k)\|$. -/
theorem isBad_targetCrit {k : ℕ} (hk1 : 1 ≤ k) (hk : D.Before f c C P ε₀ ε₁ k)
    (hbad : D.IsBad f c C p P ε₀ ε₁ k) : targetCrit f c C ε₁ (D.t k) (D.X (k + 1)) :=
  (h.toRun.exempt_of_isBad (fun _ hk1 hk _ hi hns => h.inner_stay hk1 hk hi hns) hk1 hk
    hbad).resolve_left hbad.1.not_isKa

end Good

end IsTPpGCPhase2

/-! ### Lemma 7.2.6 and the complexity of Phase 2 -/

section Complexity

variable {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {C : Set ℝⁿ} {p : ℕ} {P : TPpGCParams} {ε₀ ε₁ : ℝ}
  {x₁ : ℝⁿ} {D : Phase2Seq n} {flow fup Lμ : ℝ}

/-- **Lemma 7.2.6** of [cartis2022evaluation], corrected. Assume C.CNe, f.B.Fb, $p \ge 1$, and that
$\mu_2(\cdot, t)$ satisfies f.DpL.C with constant $L_\mu$ for every
$t \in [f_{\mathrm{low}} - 1, f_{\mathrm{up}}]$. For a Phase-2 run of TPp-GC and every reached
outer iteration $K \ge 1$:

* (i) for each $k \in [1, K]$, the $k$-th inner run has at most $g_k + 1$ successful iterations,
  where $g_k$ is its number of good iterations, and $e_k \le A_1 |\{\text{successful iterations
  of run } k\}| + C_1$;
* (ii) the number of good inner iterations satisfies $\sum_{k=1}^{K} g_k \le G (|\mathcal{K}_a
  \cap [1, K)| + 1)$, with $G$ of (7.2.39);
* (iii) $K \le |\mathcal{K}_a \cap [1, K)| + \sum_{k=1}^{K} g_k + |\{\text{bad } k \in [1,
  K)\}| + 1$.

**Correction.** The source bounds the number of successful inner iterations $|\mathcal{I}^s_k|$
by $G$ for each block of outer iterations between consecutive elements of $\mathcal{K}_a$. This
fails as printed. The argument omits the restart of $\sigma$ at $\sigma_0$ in every inner run,
so Lemma 2.4.1 is applied per run here. It counts the $i = 0$ elements of $\mathcal{I}^s_k$, so
(7.2.39) fails when its right-hand side is less than $1$. It also counts the last iterations of
runs that end on the third test of (7.2.10), for which no decrease is guaranteed. Finally, the
source gives no bound on the number of bad outer iterations of $\mathcal{K}_b$, whose inner runs
contain no good iteration.

The proof telescopes the decrease (7.2.43) of the residual over the blocks of outer iterations
between consecutive elements of $\mathcal{K}_a$. Under the hypotheses of the source the constant
$L_\mu$ exists (`CartisGouldToint.Chapter07.lemma_7_2_6_of_mu2`). -/
theorem lemma_7_2_6 (h : IsTPpGCPhase2 f c C p P ε₀ ε₁ x₁ D) (hC : Chapter06.AssumptionCNe C)
    (hp : 1 ≤ p) (hB : AssumptionBFb f c C P.β flow fup)
    (hL : ∀ t ∈ Icc (flow - 1) fup,
      Chapter06.AssumptionDpLC (Constrained.targetMerit f c t) C p Lμ)
    {K : ℕ} (hK1 : 1 ≤ K) (hK : D.Before f c C P ε₀ ε₁ K) :
    (∀ k, 1 ≤ k → k ≤ K →
      D.succCount f c p P k ≤ D.goodCount f c C p P ε₀ ε₁ k + 1 ∧
      (D.e k : ℝ) ≤ (1 + |Real.log P.γ₁| / Real.log P.γ₂) * D.succCount f c p P k +
        Real.log (P.toARpCCParams.sigmaMax Lμ / P.σ₀) / Real.log P.γ₂) ∧
    (∑ k ∈ Finset.Icc 1 K, D.goodCount f c C p P ε₀ ε₁ k : ℝ) ≤
      goodBound P Lμ p ε₀ ε₁ * (D.kaCount f c P ε₀ K + 1) ∧
    K ≤ D.kaCount f c P ε₀ K + ∑ k ∈ Finset.Icc 1 K, D.goodCount f c C p P ε₀ ε₁ k +
      D.badCount f c C p P ε₀ ε₁ K + 1 := by
  have hc := h.toContract hB hL hC hp h.tol.ε₁_pos le_rfl
  refine ⟨fun k hk1 hkK => ⟨h.toRun.succCount_le (succ := D.InnerSucc f c p P) hk1 (hK.mono hkK),
    h.e_le hB hL hC hk1 (hK.mono hkK)⟩, ?_, Constrained.TargetFollowingSeq.le_counts hK⟩
  rw [goodBound_eq (h.Lμ_nonneg hB hL) hp h.tol.ε₀_pos h.tol.ε₁_pos]
  exact_mod_cast hc.sum_goodCount_le h.toRun
    (goodDecr_pos (h.Lμ_nonneg hB hL) p h.tol.ε₀_pos h.tol.ε₁_pos) hK1 hK

/-- **Theorem 7.2.7** of [cartis2022evaluation], Phase 2, corrected. Assume C.CNe, f.B.Fb,
$p \ge 1$, and that $\mu_2(\cdot, t)$ satisfies f.DpL.C with constant $L_\mu$ for every
$t \in [f_{\mathrm{low}} - 1, f_{\mathrm{up}}]$. Let
$$N_a = \frac{f_{\mathrm{up}} - f_{\mathrm{low}} + 1}{(1 - \theta) \epsilon_0},$$
let $G$ be the bound (7.2.39), and let $A_1$, $C_1$ be the constants of Lemma 2.4.1. For every
Phase-2 run of TPp-GC:

* (i) every reached outer iteration $K \ge 1$ satisfies
  $K \le (N_a + 1)(G + 1) + n_{\mathrm{bad}}(K)$, where $n_{\mathrm{bad}}(K)$ is the number of
  bad outer iterations in $[1, K)$;
* (ii) if $n_{\mathrm{bad}}(K) \le M$ for every reached $K$, then Phase 2 terminates at an outer
  iteration $k_\epsilon \le (N_a + 1)(G + 1) + M$;
* (iii) if Phase 2 terminates at $k_\epsilon$, it uses at most $1 + G (N_a + 1) + k_\epsilon$
  evaluations of the derivatives and at most $1 + A_1 (G (N_a + 1) + k_\epsilon) + C_1
  k_\epsilon$ evaluations of $(f, c)$.

**Correction.** The source claims that Phase 2 terminates within the order (7.2.50) with no
condition. This claim rests on the gap of Lemma 7.2.6
(`CartisGouldToint.Chapter07.lemma_7_2_6`), and the statement carries the number of bad
iterations as a parameter. If $M$ does not depend on $\epsilon_0, \epsilon_1$, both counts are
$O(\max(\epsilon_0^{-1}, \epsilon_0^{-1/p} \epsilon_1^{-(p+1)/p}))$, the order of (7.2.50). The
derivative count contains a term of order $\epsilon_0^{-1}$, since every iteration of
$\mathcal{K}_a$ needs a successful inner iteration; the bound (7.2.53) of the source lacks this
term, and whether (7.2.53) holds is open. A bound without the parameter is
`CartisGouldToint.Chapter07.theorem_7_2_7_phase2_of_gradient_le`.

The output of Phase 2 satisfies Lemma 7.2.1 (`CartisGouldToint.Chapter07.lemma_7_2_1_phase2`). -/
theorem theorem_7_2_7_phase2 (h : IsTPpGCPhase2 f c C p P ε₀ ε₁ x₁ D)
    (hC : Chapter06.AssumptionCNe C) (hp : 1 ≤ p) (hB : AssumptionBFb f c C P.β flow fup)
    (hL : ∀ t ∈ Icc (flow - 1) fup,
      Chapter06.AssumptionDpLC (Constrained.targetMerit f c t) C p Lμ) :
    (∀ K, 1 ≤ K → D.Before f c C P ε₀ ε₁ K →
      (K : ℝ) ≤ ((fup - flow + 1) / ((1 - P.θ) * ε₀) + 1) * (goodBound P Lμ p ε₀ ε₁ + 1) +
        D.badCount f c C p P ε₀ ε₁ K) ∧
    (∀ M : ℝ, (∀ K, D.Before f c C P ε₀ ε₁ K → (D.badCount f c C p P ε₀ ε₁ K : ℝ) ≤ M) →
      ∃ kε, D.IsEnd f c C P ε₀ ε₁ kε ∧
        (kε : ℝ) ≤ ((fup - flow + 1) / ((1 - P.θ) * ε₀) + 1) * (goodBound P Lμ p ε₀ ε₁ + 1) +
          M) ∧
    (∀ kε, D.IsEnd f c C P ε₀ ε₁ kε →
      (D.derivEvals f c p P kε : ℝ) ≤
        1 + goodBound P Lμ p ε₀ ε₁ * ((fup - flow + 1) / ((1 - P.θ) * ε₀) + 1) + kε ∧
      (D.funEvals kε : ℝ) ≤
        1 + (1 + |Real.log P.γ₁| / Real.log P.γ₂) *
          (goodBound P Lμ p ε₀ ε₁ * ((fup - flow + 1) / ((1 - P.θ) * ε₀) + 1) + kε) +
          Real.log (P.toARpCCParams.sigmaMax Lμ / P.σ₀) / Real.log P.γ₂ * kε) := by
  obtain ⟨hi, hii, hiii⟩ := (h.toContract hB hL hC hp h.tol.ε₁_pos le_rfl).complexity h.toRun
    (goodDecr_pos (h.Lμ_nonneg hB hL) p h.tol.ε₀_pos h.tol.ε₁_pos)
    (goodBound_eq (h.Lμ_nonneg hB hL) hp h.tol.ε₀_pos h.tol.ε₁_pos).ge
    (by have := P.toARParams.log_γ₂_pos; positivity) (hB.of_le h.tol.ε₀_le_β)
  exact ⟨hi, hii, hiii⟩

/-- The first-order measure of $\mu_2(\cdot, t)$ is Lipschitz in the target. Let
$x \in \mathcal{C}$, and let $f$ and $c$ be $C^1$ at $x$. For all targets $t, t'$,
$$\omega_{\mu_2,\mathcal{C},1}(x, t') \le \omega_{\mu_2,\mathcal{C},1}(x, t) + |t - t'| \,
  \|\nabla f(x)\|.$$

The derivatives of $\mu_2(\cdot, t)$ and $\mu_2(\cdot, t')$ at $x$ differ by
$(t' - t) \nabla f(x)$. -/
theorem omega1_targetMerit_le_add {x : ℝⁿ} (hx : x ∈ C) (hf : ContDiffAt ℝ 1 f x)
    (hc : ContDiffAt ℝ 1 c x) (t t' : ℝ) :
    Chapter06.omega1 (Constrained.targetMerit f c t') C x ≤
      Chapter06.omega1 (Constrained.targetMerit f c t) C x +
        |t - t'| * ‖iteratedFDeriv ℝ 1 f x‖ := by
  have hT := Optimization.zero_mem_closedBall_inter (Optimization.zero_mem_feasibleSteps.2 hx)
  have hnorm : ‖iteratedFDeriv ℝ 1 (Constrained.targetMerit f c t') x -
      iteratedFDeriv ℝ 1 (Constrained.targetMerit f c t) x‖ =
        |t - t'| * ‖iteratedFDeriv ℝ 1 f x‖ := by
    rw [Constrained.iteratedFDeriv_targetMerit_eq_sub one_ne_zero hf hc,
      Constrained.iteratedFDeriv_targetMerit_eq_sub (t := t) one_ne_zero hf hc,
      sub_sub_sub_cancel_left, ← sub_smul, norm_smul, Real.norm_eq_abs]
  have h := (abs_le.1 (Optimization.abs_formCriticality_sub_le_norm
    (iteratedFDeriv ℝ 1 (Constrained.targetMerit f c t') x)
    (iteratedFDeriv ℝ 1 (Constrained.targetMerit f c t) x) ⟨0, hT⟩)).2
  rw [hnorm] at h
  rw [Chapter06.omega1_def, Chapter06.omega1_def]
  linarith

/-- **Theorem 7.2.7** of [cartis2022evaluation], Phase 2, without the bad-iteration parameter.
Assume C.CNe, f.B.Fb, $p \ge 1$, and that $\mu_2(\cdot, t)$ satisfies f.DpL.C with constant
$L_\mu$ for every $t \in [f_{\mathrm{low}} - 1, f_{\mathrm{up}}]$. Assume moreover that $f$ and
$c$ are $C^1$ at every point of $\mathcal{C}$, and that $\|\nabla f(x)\| \le B_f$ for every
$x \in \mathcal{C}$ with $\|c(x)\| \le \epsilon_0$. Let $\tau > 0$ with
$B_f \tau \le \epsilon_1 \theta \epsilon_0 / 2$, and let
$$N_a = \frac{f_{\mathrm{up}} - f_{\mathrm{low}} + 1}{(1 - \theta) \epsilon_0}, \qquad N_b =
  \frac{f_{\mathrm{up}} - f_{\mathrm{low}} + 1}{\tau},$$
and let $G'$ be the bound (7.2.39) with $\epsilon_1$ replaced by $\epsilon_1 / 2$, so that
$G' = 2^{(p+1)/p} G$. For every Phase-2 run of TPp-GC, every reached outer iteration $K \ge 1$
satisfies $K \le (N_a + 1)(G' + 1) + N_b$. Phase 2 terminates at some
$k_\epsilon \le (N_a + 1)(G' + 1) + N_b$, and it uses at most $1 + G' (N_a + 1) + k_\epsilon$
evaluations of the derivatives and at most $1 + A_1 (G' (N_a + 1) + k_\epsilon) + C_1
k_\epsilon$ evaluations of $(f, c)$.

**Correction.** This replaces the unconditional claim of the source; see
`CartisGouldToint.Chapter07.theorem_7_2_7_phase2`. For $\epsilon_0 = \epsilon_1 = \epsilon$, the
term $N_b = O(\epsilon^{-2})$ is within the order $O(\epsilon^{-(p+2)/p})$ of (7.2.50) if and
only if $p \le 2$.

The counting of `CartisGouldToint.Chapter07.theorem_7_2_7_phase2` is run with the sharper
exemption test $\omega_{\mu_2,\mathcal{C},1}(x_{k+1}, t_k) \le (\epsilon_1 / 2) \|r(x_{k+1},
t_k)\|$. The good iterations still decrease the residual (Lemma 6.2.4 with $\epsilon_1 / 2$). A
case-(b) iteration whose run ends at a point that passes the sharper test lowers the target by
more than $\tau$, because (7.2.12) fails at $t_{k+1}$ with the same residual and
$\omega_{\mu_2,\mathcal{C},1}(x, \cdot)$ is $B_f$-Lipschitz
(`CartisGouldToint.Chapter07.omega1_targetMerit_le_add`). -/
theorem theorem_7_2_7_phase2_of_gradient_le (h : IsTPpGCPhase2 f c C p P ε₀ ε₁ x₁ D)
    (hC : Chapter06.AssumptionCNe C) (hp : 1 ≤ p) (hB : AssumptionBFb f c C P.β flow fup)
    (hL : ∀ t ∈ Icc (flow - 1) fup,
      Chapter06.AssumptionDpLC (Constrained.targetMerit f c t) C p Lμ)
    (hf : ∀ x ∈ C, ContDiffAt ℝ 1 f x) (hc : ∀ x ∈ C, ContDiffAt ℝ 1 c x) {Bf : ℝ}
    (hBf : ∀ x ∈ C, ‖c x‖ ≤ ε₀ → ‖iteratedFDeriv ℝ 1 f x‖ ≤ Bf) {τ : ℝ} (hτ0 : 0 < τ)
    (hτ : Bf * τ ≤ ε₁ * (P.θ * ε₀) / 2) :
    (∀ K, 1 ≤ K → D.Before f c C P ε₀ ε₁ K →
      (K : ℝ) ≤ ((fup - flow + 1) / ((1 - P.θ) * ε₀) + 1) *
        (goodBound P Lμ p ε₀ (ε₁ / 2) + 1) + (fup - flow + 1) / τ) ∧
    ∃ kε, D.IsEnd f c C P ε₀ ε₁ kε ∧
      (kε : ℝ) ≤ ((fup - flow + 1) / ((1 - P.θ) * ε₀) + 1) *
        (goodBound P Lμ p ε₀ (ε₁ / 2) + 1) + (fup - flow + 1) / τ ∧
      (D.derivEvals f c p P kε : ℝ) ≤
        1 + goodBound P Lμ p ε₀ (ε₁ / 2) * ((fup - flow + 1) / ((1 - P.θ) * ε₀) + 1) + kε ∧
      (D.funEvals kε : ℝ) ≤
        1 + (1 + |Real.log P.γ₁| / Real.log P.γ₂) *
          (goodBound P Lμ p ε₀ (ε₁ / 2) * ((fup - flow + 1) / ((1 - P.θ) * ε₀) + 1) + kε) +
          Real.log (P.toARpCCParams.sigmaMax Lμ / P.σ₀) / Real.log P.γ₂ * kε := by
  classical
  have hε₁ := h.tol.ε₁_pos
  have hε₀ := h.tol.ε₀_pos
  have hc' := h.toContract hB hL hC hp (half_pos hε₁) (half_le_self hε₁.le)
  -- a case-(b) iteration ending at a point passing the sharper test lowers the target by `τ`
  have hdrop : ∀ k, 1 ≤ k → D.Before f c C P ε₀ ε₁ (k + 1) → D.IsKb f c P ε₀ k →
      targetCrit f c C (ε₁ / 2) (D.t k) (D.X (k + 1)) → τ ≤ D.t k - D.t (k + 1) := by
    intro k hk1 hk hb hex
    have hkB : D.Before f c C P ε₀ ε₁ k := hk.mono k.le_succ
    have hd : 0 < D.t k - D.t (k + 1) := sub_pos.2 (h.toRun.target_succ_lt hk1 hk)
    have hX : D.X (k + 1) ∈ C := h.toRun.mem_succ k hk1 hkB
    have hr : Constrained.targetResidual f c (D.t (k + 1)) (D.X (k + 1)) =
        Constrained.targetResidual f c (D.t k) (D.X (k + 1)) :=
      h.toRun.residual_succ_of_kb hk1 hkB hb
    have hrle : Constrained.targetResidual f c (D.t k) (D.X (k + 1)) ≤ ε₀ :=
      (h.toRun.residual_succ_le hk1 hkB).trans (h.toRun.residual_le hk1 hkB)
    have hncrit : ε₁ * Constrained.targetResidual f c (D.t k) (D.X (k + 1)) <
        Chapter06.omega1 (Constrained.targetMerit f c (D.t (k + 1))) C (D.X (k + 1)) := by
      rw [← hr]
      exact lt_of_not_ge fun hm => hk k hk1 k.lt_succ_self (Or.inr ⟨Or.inr hb, hm⟩)
    have hlip := omega1_targetMerit_le_add hX (hf _ hX) (hc _ hX) (D.t k) (D.t (k + 1))
    rw [abs_of_pos hd] at hlip
    have hBf' := hBf _ hX (Constrained.norm_le_targetResidual.trans hrle)
    have hlow : P.θ * ε₀ ≤ Constrained.targetResidual f c (D.t k) (D.X (k + 1)) :=
      h.toRun.le_residual_succ_of_kb hb
    have hex' : Chapter06.omega1 (Constrained.targetMerit f c (D.t k)) C (D.X (k + 1)) ≤
        ε₁ / 2 * Constrained.targetResidual f c (D.t k) (D.X (k + 1)) := hex
    have key : ε₁ * (P.θ * ε₀) / 2 < (D.t k - D.t (k + 1)) * Bf := by
      have : (D.t k - D.t (k + 1)) * ‖iteratedFDeriv ℝ 1 f (D.X (k + 1))‖ ≤
          (D.t k - D.t (k + 1)) * Bf := mul_le_mul_of_nonneg_left hBf' hd.le
      have := mul_le_mul_of_nonneg_left hlow hε₁.le
      linarith
    have hBf0 : 0 < Bf := by
      by_contra hneg
      push Not at hneg
      nlinarith [mul_pos hε₁ (mul_pos P.θ_pos hε₀)]
    exact (lt_of_mul_lt_mul_left (by linarith) hBf0.le).le
  refine hc'.complexity_of_badCount_le h.toRun
    (goodDecr_pos (h.Lμ_nonneg hB hL) p hε₀ (half_pos hε₁))
    (goodBound_eq (h.Lμ_nonneg hB hL) hp hε₀ (half_pos hε₁)).ge
    (by have := P.toARParams.log_γ₂_pos; positivity) (hB.of_le h.tol.ε₀_le_β)
    fun K hK1 hK => (Nat.cast_le.2 (h.toRun.badCount_le_card
      (fun _ hk1 hk _ hi hns => h.inner_stay hk1 hk hi hns) hK)).trans ?_
  exact h.toRun.card_kb_le_of_drop (hB.of_le h.tol.ε₀_le_β) hτ0
    (fun k hk1 hk hb hex => hdrop k hk1 hk hb (hex.resolve_left hb.not_isKa)) hK1 hK

end Complexity

/-! ### Existence of Phase 2 -/

section Existence

variable {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {C : Set ℝⁿ} {p : ℕ} {P : TPpGCParams} {ε₀ ε₁ : ℝ}

/-- The inner runs of Phase 2 of Algorithm 7.2.1 of [cartis2022evaluation] exist and terminate.
Assume C.CNe, $\mu_2$.DpL.C and $p \ge 1$, and let $\epsilon_0, \epsilon_1$ satisfy (7.2.8). For
every target $\tau$ and every $y \in \mathcal{C}$ there is an ARp1-CC run on
$\mu_2(\cdot, \tau)$ from $y$ with the termination test (7.2.10), the test holds at some first
index $e$, and the iterate at $e$ lies in $\mathcal{C}$.

While the test fails, $\omega_{\mu_2,\mathcal{C},1} > \epsilon_1 \theta \epsilon_0 > 0$. Then a
minimizer of the model over the feasible steps is an admissible step, and each successful
iteration decreases $\mu_2(\cdot, \tau) \ge 0$ by at least $\kappa_1 (\epsilon_1 \theta
\epsilon_0)^{(p+1)/p}$, as in Theorem 6.2.5. -/
theorem exists_innerRun (hC : Chapter06.AssumptionCNe C) (hμ : AssumptionMu2DpLC f c C p)
    (hp : 1 ≤ p) (htol : TPpGCTol P ε₀ ε₁) (τ : ℝ) {y : ℝⁿ} (hy : y ∈ C) :
    ∃ (xs ss : ℕ → ℝⁿ) (σs : ℕ → ℝ) (e : ℕ), xs 0 = y ∧
      IsARRun P.toARParams (fun i => innerStop f c C P.θ ε₀ ε₁ τ (xs i))
        (fun i => IsFirstOrderCCStep (Constrained.targetMerit f c τ) C p P.θ₁ (xs i) (σs i)
          (ss i)) (fun _ => False)
        (taylorRatio (Constrained.targetMerit f c τ) p xs ss) xs ss σs ∧
      IsFirstHit (fun i => innerStop f c C P.θ ε₀ ε₁ τ (xs i)) e ∧ xs e ∈ C := by
  obtain ⟨L, hdpl⟩ := hμ τ
  set μ := Constrained.targetMerit f c τ
  have hε₀ := htol.ε₀_pos
  have hε₁ := htol.ε₁_pos
  have hθ := P.θ_pos
  -- a failing test gives a large first-order measure
  have hbig : ∀ z, ¬ innerStop f c C P.θ ε₀ ε₁ τ z →
      ε₁ * (P.θ * ε₀) < Chapter06.omega1 μ C z := by
    intro z hz
    simp only [innerStop, not_or, not_le] at hz
    exact lt_of_le_of_lt (by gcongr; exact hz.1.le) hz.2.2
  obtain ⟨xs, ss, σs, hx0, hrun, hinv⟩ := exists_isARRun P.toARParams (Inv := (· ∈ C))
    (test := innerStop f c C P.θ ε₀ ε₁ τ) (stepOK := IsFirstOrderCCStep μ C p P.θ₁)
    (fun z _ t => reductionRatio μ z t ((ftaylorSeries ℝ μ z).taylorDecrement p t))
    (fun z σ hz _ hσ ht => by
      obtain ⟨s, -, hs, -⟩ := exists_isFirstOrderCCStep (θ := P.θ₁) hC.isClosed hC.convex hz
        (hdpl.contDiffAt z hz) hp hσ P.θ₁_pos.le
        ((by positivity : (0 : ℝ) < ε₁ * (P.θ * ε₀)).trans (hbig z ht))
      exact ⟨s, hs, hs.mem⟩) hy
  -- termination, as in Theorem 6.2.5
  have hσ : ∀ k, (∀ j < k, ¬ IsARRun.Stop (fun i => innerStop f c C P.θ ε₀ ε₁ τ (xs i))
      (fun _ => False) j) → xs k ∈ C ∧ P.σmin ≤ σs k ∧ σs k ≤ P.toARpCCParams.sigmaMax L :=
    fun k hk => Chapter06.arpcc_sigma_le (P := P.toARpCCParams) hrun hC hdpl (hx0 ▸ hy)
      (fun _ hs => ⟨hs.mem, hs.decrease⟩) k (IsARRun.forall_lt_not_stop_iff.1 hk)
  have hκ := Chapter06.kappa1CC_pos (P := P.toARpCCParams) (p := p) hdpl.nonneg
  have he : 0 < ((p : ℝ) + 1) / p := by
    have : (1 : ℝ) ≤ p := by exact_mod_cast hp
    positivity
  obtain ⟨e, he, -, -⟩ := hrun.exists_isFirstHit_of_decrease (σmax := P.toARpCCParams.sigmaMax L)
    (V := fun i => μ (xs i)) (Vlow := 0)
    (δ := Chapter06.kappa1CC P.toARpCCParams L p * (ε₁ * (P.θ * ε₀)) ^ (((p : ℝ) + 1) / p))
    (fun k hk => (hσ k hk).2.2) (by positivity)
    (fun k hk => (hrun.accept k hk).le (w := μ) rfl (by
      have := P.σmin_nonneg.trans (hσ k fun j hj => hk j hj.le).2.1
      exact lt_of_le_of_lt (by positivity) (lt_taylorDecrement_of_regularizedModel_lt
        (hrun.step_of_forall_le hk).decrease)))
    (fun k _ => Constrained.targetMerit_nonneg)
    (fun k hk hs => by
      have hk' : ∀ j ≤ k, ¬ IsARRun.Stop (fun i => innerStop f c C P.θ ε₀ ε₁ τ (xs i))
          (fun _ => False) j := fun j hj => hk j (hj.trans k.le_succ)
      obtain ⟨hxk, hmin, hmax⟩ := hσ k fun j hj => hk' j hj.le
      have hstep : IsFirstOrderCCStep μ C p P.θ₁ (xs k) (σs k) (ss k) :=
        hrun.step_of_forall_le hk'
      have hdec := hstep.sub_ge hC.convex hdpl.contDiffAt hdpl.lipschitz hdpl.nonneg hxk hp
        P.θ₁_pos.le P.σmin_nonneg hmin hmax P.η₁_pos hs
      rw [← hrun.eq_add_of_succ hk' hs] at hdec
      have hω := hbig _ (fun h' => hk (k + 1) le_rfl (Or.inl h'))
      refine le_trans ?_ hdec
      rw [Chapter06.kappa1CC_def]
      gcongr
      · exact (Chapter06.kappa1CC_pos (P := P.toARpCCParams) (p := p) hdpl.nonneg).le
      exact hω.le)
  have he' : IsFirstHit (fun i => innerStop f c C P.θ ε₀ ε₁ τ (xs i)) e :=
    ⟨he.1.resolve_right id, fun j hj h' => he.2 j hj (Or.inl h')⟩
  exact ⟨xs, ss, σs, e, hx0, hrun, he', hinv e he'.2⟩

/-- Existence of Phase 2 of Algorithm 7.2.1 of [cartis2022evaluation]. Assume C.CNe, $\mu_2$.DpL.C
and $p \ge 1$, and let $\epsilon_0, \epsilon_1$ satisfy (7.2.8). For every $x_1 \in \mathcal{C}$
with $\|c(x_1)\| \le \theta \epsilon_0$ there are sequences that form a Phase-2 run from $x_1$.

The outer sequence is built recursively from the inner runs of
`CartisGouldToint.Chapter07.exists_innerRun`. -/
theorem exists_phase2 (hC : Chapter06.AssumptionCNe C) (hμ : AssumptionMu2DpLC f c C p)
    (hp : 1 ≤ p) (htol : TPpGCTol P ε₀ ε₁) {x₁ : ℝⁿ} (hx₁ : x₁ ∈ C)
    (hc₁ : ‖c x₁‖ ≤ P.θ * ε₀) : ∃ D : Phase2Seq n, IsTPpGCPhase2 f c C p P ε₀ ε₁ x₁ D := by
  classical
  have hin : ∀ (y : ℝⁿ) (τ : ℝ), y ∈ C → ∃ r : (ℕ → ℝⁿ) × (ℕ → ℝⁿ) × (ℕ → ℝ) × ℕ,
      r.1 0 = y ∧
      IsARRun P.toARParams (fun i => innerStop f c C P.θ ε₀ ε₁ τ (r.1 i))
        (fun i => IsFirstOrderCCStep (Constrained.targetMerit f c τ) C p P.θ₁ (r.1 i)
          (r.2.2.1 i) (r.2.1 i)) (fun _ => False)
        (taylorRatio (Constrained.targetMerit f c τ) p r.1 r.2.1) r.1 r.2.1 r.2.2.1 ∧
      IsFirstHit (fun i => innerStop f c C P.θ ε₀ ε₁ τ (r.1 i)) r.2.2.2 ∧ r.1 r.2.2.2 ∈ C := by
    intro y τ hy
    obtain ⟨xs, ss, σs, e, h0, hr, he, hm⟩ := exists_innerRun hC hμ hp htol τ hy
    exact ⟨(xs, ss, σs, e), h0, hr, he, hm⟩
  choose! R hR using hin
  -- one outer iteration: the inner run, then the target update
  let next : ℝⁿ × ℝ → ℝⁿ × ℝ := fun st =>
    ((R st.1 st.2).1 (R st.1 st.2).2.2.2,
      if Constrained.targetResidual f c st.2 ((R st.1 st.2).1 (R st.1 st.2).2.2.2) ≤ P.θ * ε₀
      then f ((R st.1 st.2).1 (R st.1 st.2).2.2.2) -
        √(ε₀ ^ 2 - ‖c ((R st.1 st.2).1 (R st.1 st.2).2.2.2)‖ ^ 2)
      else 2 * f ((R st.1 st.2).1 (R st.1 st.2).2.2.2) - st.2)
  let S : ℕ → ℝⁿ × ℝ := fun j => Nat.rec (x₁, f x₁ - √(ε₀ ^ 2 - ‖c x₁‖ ^ 2))
    (fun _ st => next st) j
  have hS : ∀ j, S (j + 1) = next (S j) := fun _ => rfl
  have hmem : ∀ j, (S j).1 ∈ C := by
    intro j
    induction j with
    | zero => exact hx₁
    | succ j ih => rw [hS]; exact (hR _ _ ih).2.2.2
  let D : Phase2Seq n :=
    { X := fun k => (S (k - 1)).1
      t := fun k => (S (k - 1)).2
      xi := fun k => (R (S (k - 1)).1 (S (k - 1)).2).1
      si := fun k => (R (S (k - 1)).1 (S (k - 1)).2).2.1
      σi := fun k => (R (S (k - 1)).1 (S (k - 1)).2).2.2.1
      e := fun k => (R (S (k - 1)).1 (S (k - 1)).2).2.2.2 }
  have hX : ∀ k, 1 ≤ k → D.X (k + 1) = D.xi k (D.e k) := by
    intro k hk
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rfl
  have ht : ∀ k, 1 ≤ k → D.t (k + 1) =
      if Constrained.targetResidual f c (D.t k) (D.X (k + 1)) ≤ P.θ * ε₀
      then f (D.X (k + 1)) - √(ε₀ ^ 2 - ‖c (D.X (k + 1))‖ ^ 2)
      else 2 * f (D.X (k + 1)) - D.t k := by
    intro k hk
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rfl
  refine ⟨D, htol, hx₁, hc₁, rfl, rfl, fun k _ _ => (hR _ _ (hmem _)).1,
    fun k _ _ => (hR _ _ (hmem _)).2.1, fun k _ _ => (hR _ _ (hmem _)).2.2.1,
    fun k hk _ => hX k hk, fun k hk _ ha => ?_, fun k hk _ hb => ?_⟩
  · rw [ht k hk, ite_eq_left (show Constrained.targetResidual f c (D.t k) (D.X (k + 1)) ≤
      P.θ * ε₀ from ha)]
  · rw [ht k hk, ite_eq_right (show ¬ Constrained.targetResidual f c (D.t k) (D.X (k + 1)) ≤
      P.θ * ε₀ from hb.not_isKa)]

end Existence

/-! ### The whole algorithm -/

section Whole

variable {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {C : Set ℝⁿ} {p ℓ : ℕ} {P : TPpGCParams} {ε₀ ε₁ : ℝ}
  {x₀ : ℝⁿ} {y s : ℕ → ℝⁿ} {σ : ℕ → ℝ} {k₁ : ℕ} {D : Phase2Seq n}

/-- **Algorithm 7.2.1** of [cartis2022evaluation] (TPp-GC), a whole run. Let
$\epsilon_0, \epsilon_1$ satisfy (7.2.8). Phase 1 is an ARpLE-CC run (Algorithm 6.3.1) on the
constraint function $c$ from $x_0 \in \mathcal{C}$ with the tolerances
$(\theta \epsilon_0, \epsilon_1)$, stopped at the first index $k_1$ at which (7.2.9) holds, and
$x_1 = y_{k_1}$. If $\|c(x_1)\| > \theta \epsilon_0$, the algorithm terminates with
$x_\epsilon = x_1$. Otherwise Phase 2 (`CartisGouldToint.Chapter07.IsTPpGCPhase2`) is run from
$x_1$.

The test (7.2.9) is `CartisGouldToint.Chapter06.stopLE`. The evaluation counts of Phase 1 are
`Optimization.funEvalCount k₁` and `Optimization.derivEvalCount` of its successful iterations;
those of Phase 2 are `CartisGouldToint.Chapter07.Phase2Seq.funEvals` and
`CartisGouldToint.Chapter07.Phase2Seq.derivEvals`. -/
structure algorithm_7_2_1 (f : ℝⁿ → ℝ) (c : ℝⁿ → ℝᵐ) (C : Set ℝⁿ) (p ℓ : ℕ) (P : TPpGCParams)
    (ε₀ ε₁ : ℝ) (x₀ : ℝⁿ) (y s : ℕ → ℝⁿ) (σ : ℕ → ℝ) (k₁ : ℕ) (D : Phase2Seq n) : Prop where
  /-- The tolerances satisfy (7.2.8). -/
  tol : TPpGCTol P ε₀ ε₁
  /-- Phase 1 starts at $x_0$. -/
  start : y 0 = x₀
  /-- Phase 1 is an ARpLE-CC run on $c$ with the tolerances $(\theta \epsilon_0, \epsilon_1)$. -/
  phase1 : Chapter06.algorithm_6_3_1 c ℓ C p P.toARpCCParams (P.θ * ε₀) ε₁ y s σ
  /-- Phase 1 stops at $k_1$, the first index at which (7.2.9) holds, that is,
  $\|c(y_k)\| \le \theta \epsilon_0$ or $\omega_{\Phi_\ell,\mathcal{C},1}(y_k) \le \epsilon_1
  \|c(y_k)\|^{\ell-1}$; and $x_1 = y_{k_1}$. -/
  phase1_hit : IsFirstHit (fun k => Chapter06.stopLE c ℓ C (P.θ * ε₀) ε₁ (y k)) k₁
  /-- If $\|c(x_1)\| \le \theta \epsilon_0$, Phase 2 is run from $x_1 = y_{k_1}$. -/
  phase2 : ‖c (y k₁)‖ ≤ P.θ * ε₀ → IsTPpGCPhase2 f c C p P ε₀ ε₁ (y k₁) D

/-- The output $x_1$ of Phase 1 lies in $\mathcal{C}$. -/
theorem algorithm_7_2_1.mem_phase1 (h : algorithm_7_2_1 f c C p ℓ P ε₀ ε₁ x₀ y s σ k₁ D) :
    y k₁ ∈ C :=
  h.phase1.mem h.phase1_hit.2

/-- Existence of TPp-GC runs (Algorithm 7.2.1 of [cartis2022evaluation]). Assume C.CNe, $p \ge 1$,
$\ell \ge 2$, $\iota_1(p, \ell, i) = (2^i - 1)/2^i - (\ell - 1)/p \ge 0$ for some $i$,
$\Phi_\ell$.DpL.C for $c$ with some constant $L_\Phi$, and $\mu_2$.DpL.C, and let
$\epsilon_0, \epsilon_1$ satisfy (7.2.8). Then from every $x_0 \in \mathcal{C}$ there is a run
of TPp-GC.

Phase 1 exists by `CartisGouldToint.Chapter06.algorithm_6_3_1.exists_run` and terminates by
`CartisGouldToint.Chapter06.theorem_6_3_1`; Phase 2 exists by
`CartisGouldToint.Chapter07.exists_phase2`. -/
theorem algorithm_7_2_1_exists (hC : Chapter06.AssumptionCNe C) (hx₀ : x₀ ∈ C) (hp : 1 ≤ p)
    (hℓ : 2 ≤ ℓ) {i : ℕ} (hι : 0 ≤ ((2 : ℝ) ^ i - 1) / 2 ^ i - ((ℓ : ℝ) - 1) / p) {LΦ : ℝ}
    (hΦ : Chapter06.AssumptionPhiDpLC c ℓ C p LΦ) (hμ : AssumptionMu2DpLC f c C p)
    (htol : TPpGCTol P ε₀ ε₁) :
    ∃ (y s : ℕ → ℝⁿ) (σ : ℕ → ℝ) (k₁ : ℕ) (D : Phase2Seq n),
      algorithm_7_2_1 f c C p ℓ P ε₀ ε₁ x₀ y s σ k₁ D := by
  obtain ⟨y, s, σ, hy0, hrun⟩ := Chapter06.algorithm_6_3_1.exists_run (r := c) (ℓ := ℓ)
    (ε₀ := P.θ * ε₀) P.toARpCCParams hC hΦ.contDiffAt hp htol.ε₁_pos.le hx₀
  obtain ⟨k₁, hk₁, -, -⟩ := Chapter06.theorem_6_3_1 hp hℓ hι (β := 1 / 2) (by norm_num)
    (by norm_num) hC hΦ hrun (mul_pos P.θ_pos htol.ε₀_pos) htol.ε₁_pos
  have hmem : y k₁ ∈ C := hrun.mem hk₁.2
  by_cases hc : ‖c (y k₁)‖ ≤ P.θ * ε₀
  · obtain ⟨D, hD⟩ := exists_phase2 hC hμ hp htol hmem hc
    exact ⟨y, s, σ, k₁, D, htol, hy0, hrun, hk₁, fun _ => hD⟩
  · exact ⟨y, s, σ, k₁, ⟨fun _ => 0, fun _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ _ => 0,
      fun _ => 0⟩, htol, hy0, hrun, hk₁, fun h' => absurd h' hc⟩

/-- **Lemma 7.2.1** of [cartis2022evaluation], whole algorithm. Let $f$ and $c$ be differentiable at
every point of $\mathcal{C}$, and consider a run of TPp-GC.

* If the algorithm stops in Phase 1, that is, $\|c(x_1)\| > \theta \epsilon_0$, then
  $x_\epsilon = x_1 \in \mathcal{C}$ and $\omega_{\Phi_\ell,\mathcal{C},1}(x_\epsilon) \le
  \epsilon_1 \|c(x_\epsilon)\|^{\ell-1}$ (7.2.14).
* If it enters Phase 2 and Phase 2 terminates at outer iteration $k_\epsilon$, then
  $x_\epsilon = x_{k_\epsilon+1}$ satisfies (7.2.15) or (7.2.16), as in
  `CartisGouldToint.Chapter07.lemma_7_2_1_phase2`, with $\Phi_2 = \frac{1}{2} \|c\|^2$. -/
theorem lemma_7_2_1 (h : algorithm_7_2_1 f c C p ℓ P ε₀ ε₁ x₀ y s σ k₁ D)
    (hf : ∀ x ∈ C, DifferentiableAt ℝ f x) (hc : ∀ x ∈ C, DifferentiableAt ℝ c x) :
    (P.θ * ε₀ < ‖c (y k₁)‖ → y k₁ ∈ C ∧
      Chapter06.omega1 (Chapter06.PhiEll c ℓ) C (y k₁) ≤ ε₁ * ‖c (y k₁)‖ ^ (ℓ - 1)) ∧
    (‖c (y k₁)‖ ≤ P.θ * ε₀ → ∀ kε, D.IsEnd f c C P ε₀ ε₁ kε →
      (f (D.X (kε + 1)) = D.targetOut f c P ε₀ kε ∧
          Chapter06.omega1 (fun z => ‖c z‖ ^ 2 / 2) C (D.X (kε + 1)) ≤
            ε₁ * ‖c (D.X (kε + 1))‖ ∧
          P.θ * ε₀ < ‖c (D.X (kε + 1))‖) ∨
        (D.targetOut f c P ε₀ kε < f (D.X (kε + 1)) ∧
          IsApproxFirstOrderGC f c C ε₀ ε₁ (D.X (kε + 1))
            (Constrained.targetMultiplier f c (D.targetOut f c P ε₀ kε) (D.X (kε + 1))))) := by
  refine ⟨fun hgt => ⟨h.mem_phase1, ?_⟩, fun hle kε hend =>
    lemma_7_2_1_phase2 (h.phase2 hle) hf hc hend⟩
  rcases h.phase1_hit.1 with h' | h'
  · exact absurd h' (not_le.2 hgt)
  · exact h'

/-- **Lemma 7.2.2** of [cartis2022evaluation] (Phase 1). Assume C.CNe, $p \ge 1$, $\ell \ge 2$,
$\iota_1(p, \ell, i) = (2^i - 1)/2^i - (\ell - 1)/p \ge 0$, and $\Phi_\ell$.DpL.C for $c$ with
constant $L_\Phi$, and let $\beta \in (0, 1)$ be the analysis constant of Theorem 6.3.1. Write
$$\kappa = \max\left(\frac{1}{1 - \beta^{1/2^i}}, \frac{2^i}{\beta^{(\ell-1)(p+1)/p}}
  \kappa^S_{\mathrm{ARp1CC}}\right), \qquad R = \frac{\max(\|c(x_0)\|^{1/2^i},
  \|c(x_0)\|^{1-(\ell-1)/p})}{\min((\theta \epsilon_0)^{1/2^i}, \epsilon_1^{(p+1)/p})},$$
with $\kappa^S_{\mathrm{ARp1CC}}$ of Theorem 6.2.5 for $L_\Phi$, and let $\sigma_{\Phi,\max} =
\max(\sigma_0, \gamma_3 L_\Phi / (1 - \eta_2))$. Then Phase 1 stops at $x_1 = y_{k_1}$ with
$\|c(x_1)\| \le \theta \epsilon_0$ or $\omega_{\Phi_\ell,\mathcal{C},1}(x_1) \le \epsilon_1
\|c(x_1)\|^{\ell-1}$ (7.2.9), after at most
$$\kappa \left(1 + \frac{|\log \gamma_1|}{\log \gamma_2}\right) R + \frac{|\log \gamma_1| +
  \log(\sigma_{\Phi,\max} / \sigma_0)}{\log \gamma_2} + 2$$
evaluations of $c$ (7.2.23) and at most $\kappa R + 2$ evaluations of its derivatives (7.2.24).

**Correction.** The printed bound (7.2.24) lacks the term $+2$ of Theorem 6.3.1, which is
restored.

The number of evaluations of $c$ is `Optimization.funEvalCount k₁` $= k_1 + 1$, and the number
of derivative evaluations counts the initial one and one per successful iteration before $k_1$.
The constant $\kappa^S_{\mathrm{ARp1CC}}$ is `CartisGouldToint.Chapter06.kappaSARp1CC`. -/
theorem lemma_7_2_2 (h : algorithm_7_2_1 f c C p ℓ P ε₀ ε₁ x₀ y s σ k₁ D)
    (hC : Chapter06.AssumptionCNe C) (hp : 1 ≤ p) (hℓ : 2 ≤ ℓ) {i : ℕ}
    (hι : 0 ≤ ((2 : ℝ) ^ i - 1) / 2 ^ i - ((ℓ : ℝ) - 1) / p) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    {LΦ : ℝ} (hΦ : Chapter06.AssumptionPhiDpLC c ℓ C p LΦ) :
    (‖c (y k₁)‖ ≤ P.θ * ε₀ ∨
      Chapter06.omega1 (Chapter06.PhiEll c ℓ) C (y k₁) ≤ ε₁ * ‖c (y k₁)‖ ^ (ℓ - 1)) ∧
    (funEvalCount k₁ : ℝ) ≤
        max (1 / (1 - β ^ (1 / 2 ^ i : ℝ)))
            (2 ^ i / β ^ (((ℓ : ℝ) - 1) * (((p : ℝ) + 1) / p)) *
              Chapter06.kappaSARp1CC P.toARpCCParams LΦ p) *
          (1 + |Real.log P.γ₁| / Real.log P.γ₂) *
          max (‖c (x₀)‖ ^ (1 / 2 ^ i : ℝ)) (‖c (x₀)‖ ^ (1 - ((ℓ : ℝ) - 1) / p)) /
          min ((P.θ * ε₀) ^ (1 / 2 ^ i : ℝ)) (ε₁ ^ (((p : ℝ) + 1) / p)) +
        ((|Real.log P.γ₁| + Real.log (P.toARpCCParams.sigmaMax LΦ / P.σ₀)) / Real.log P.γ₂ + 2) ∧
    (derivEvalCount (fun k => P.η₁ ≤ taylorRatio (Chapter06.PhiEll c ℓ) p y s k) k₁ : ℝ) ≤
        max (1 / (1 - β ^ (1 / 2 ^ i : ℝ)))
            (2 ^ i / β ^ (((ℓ : ℝ) - 1) * (((p : ℝ) + 1) / p)) *
              Chapter06.kappaSARp1CC P.toARpCCParams LΦ p) *
          max (‖c (x₀)‖ ^ (1 / 2 ^ i : ℝ)) (‖c (x₀)‖ ^ (1 - ((ℓ : ℝ) - 1) / p)) /
          min ((P.θ * ε₀) ^ (1 / 2 ^ i : ℝ)) (ε₁ ^ (((p : ℝ) + 1) / p)) + 2 := by
  obtain ⟨kε, hkε, hF, hD⟩ := Chapter06.theorem_6_3_1 hp hℓ hι hβ0 hβ1 hC hΦ h.phase1
    (mul_pos P.θ_pos h.tol.ε₀_pos) h.tol.ε₁_pos
  rw [hkε.unique h.phase1_hit, h.start] at *
  exact ⟨h.phase1_hit.1, hF, hD⟩

end Whole

/-! ### Theorem 7.2.7 under the book's hypotheses -/

section BookHypotheses

variable {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {C : Set ℝⁿ} {p : ℕ} {P : TPpGCParams} {ε₀ ε₁ : ℝ}
  {x₁ : ℝⁿ} {D : Phase2Seq n} {flow fup : ℝ}

/-- **Lemma 7.2.6** of [cartis2022evaluation] under the hypotheses of the source. Assume C.CNe,
$p \ge 1$, f.B.Fb and $\mu_2$.DpL.C. Then there is $L_\mu \ge 0$ such that, for a Phase-2 run of
TPp-GC, the conclusions (i)–(iii) of `CartisGouldToint.Chapter07.lemma_7_2_6` hold for every
reached outer iteration $K \ge 1$.

**Correction.** As for `CartisGouldToint.Chapter07.lemma_7_2_6`.

The constant $L_\mu$ is given by Lemma 7.2.5 on $[f_{\mathrm{low}} - 1, f_{\mathrm{up}}]$. -/
theorem lemma_7_2_6_of_mu2 (h : IsTPpGCPhase2 f c C p P ε₀ ε₁ x₁ D)
    (hC : Chapter06.AssumptionCNe C) (hp : 1 ≤ p) (hB : AssumptionBFb f c C P.β flow fup)
    (hμ : AssumptionMu2DpLC f c C p) :
    ∃ Lμ, 0 ≤ Lμ ∧ ∀ K, 1 ≤ K → D.Before f c C P ε₀ ε₁ K →
      (∀ k, 1 ≤ k → k ≤ K →
        D.succCount f c p P k ≤ D.goodCount f c C p P ε₀ ε₁ k + 1 ∧
        (D.e k : ℝ) ≤ (1 + |Real.log P.γ₁| / Real.log P.γ₂) * D.succCount f c p P k +
          Real.log (P.toARpCCParams.sigmaMax Lμ / P.σ₀) / Real.log P.γ₂) ∧
      (∑ k ∈ Finset.Icc 1 K, D.goodCount f c C p P ε₀ ε₁ k : ℝ) ≤
        goodBound P Lμ p ε₀ ε₁ * (D.kaCount f c P ε₀ K + 1) ∧
      K ≤ D.kaCount f c P ε₀ K + ∑ k ∈ Finset.Icc 1 K, D.goodCount f c C p P ε₀ ε₁ k +
        D.badCount f c C p P ε₀ ε₁ K + 1 := by
  obtain ⟨Lμ, hL0, hL⟩ := lemma_7_2_5 hμ hp (flow - 1) fup
  exact ⟨Lμ, hL0, fun _ hK1 hK => lemma_7_2_6 h hC hp hB hL hK1 hK⟩

/-- **Theorem 7.2.7** of [cartis2022evaluation], Phase 2, under the hypotheses of the source. Assume
C.CNe, $p \ge 1$, f.B.Fb and $\mu_2$.DpL.C. Then there is $L_\mu \ge 0$ such that, for a Phase-2
run of TPp-GC, the conclusions (i)–(iii) of `CartisGouldToint.Chapter07.theorem_7_2_7_phase2`
hold.

**Correction.** As for `CartisGouldToint.Chapter07.theorem_7_2_7_phase2`: the number of bad
iterations is a parameter of the statement.

The constant $L_\mu$ is given by Lemma 7.2.5 on $[f_{\mathrm{low}} - 1, f_{\mathrm{up}}]$. -/
theorem theorem_7_2_7_phase2_of_mu2 (h : IsTPpGCPhase2 f c C p P ε₀ ε₁ x₁ D)
    (hC : Chapter06.AssumptionCNe C) (hp : 1 ≤ p) (hB : AssumptionBFb f c C P.β flow fup)
    (hμ : AssumptionMu2DpLC f c C p) :
    ∃ Lμ, 0 ≤ Lμ ∧
      (∀ K, 1 ≤ K → D.Before f c C P ε₀ ε₁ K →
        (K : ℝ) ≤ ((fup - flow + 1) / ((1 - P.θ) * ε₀) + 1) * (goodBound P Lμ p ε₀ ε₁ + 1) +
          D.badCount f c C p P ε₀ ε₁ K) ∧
      (∀ M : ℝ, (∀ K, D.Before f c C P ε₀ ε₁ K → (D.badCount f c C p P ε₀ ε₁ K : ℝ) ≤ M) →
        ∃ kε, D.IsEnd f c C P ε₀ ε₁ kε ∧
          (kε : ℝ) ≤ ((fup - flow + 1) / ((1 - P.θ) * ε₀) + 1) * (goodBound P Lμ p ε₀ ε₁ + 1) +
            M) ∧
      (∀ kε, D.IsEnd f c C P ε₀ ε₁ kε →
        (D.derivEvals f c p P kε : ℝ) ≤
          1 + goodBound P Lμ p ε₀ ε₁ * ((fup - flow + 1) / ((1 - P.θ) * ε₀) + 1) + kε ∧
        (D.funEvals kε : ℝ) ≤
          1 + (1 + |Real.log P.γ₁| / Real.log P.γ₂) *
            (goodBound P Lμ p ε₀ ε₁ * ((fup - flow + 1) / ((1 - P.θ) * ε₀) + 1) + kε) +
            Real.log (P.toARpCCParams.sigmaMax Lμ / P.σ₀) / Real.log P.γ₂ * kε) := by
  obtain ⟨Lμ, hL0, hL⟩ := lemma_7_2_5 hμ hp (flow - 1) fup
  exact ⟨Lμ, hL0, theorem_7_2_7_phase2 h hC hp hB hL⟩


/-- **Theorem 7.2.7** of [cartis2022evaluation], whole algorithm, corrected. Assume C.CNe,
$p \ge 1$, $\ell \ge 2$, $\iota_1(p, \ell, i) \ge 0$, $\Phi_\ell$.DpL.C for $c$ with constant
$L_\Phi$, $\mu_2$.DpL.C and f.B.Fb, and let $\beta \in (0, 1)$ be the analysis constant of
Theorem 6.3.1. For a run of TPp-GC:

* Phase 1 uses at most the numbers of evaluations (7.2.23) and (7.2.24) of
  `CartisGouldToint.Chapter07.lemma_7_2_2`;
* if $\|c(x_1)\| \le \theta \epsilon_0$, so that Phase 2 is entered, there is $L_\mu \ge 0$ for
  which Phase 2 satisfies the conclusions (i)–(iii) of
  `CartisGouldToint.Chapter07.theorem_7_2_7_phase2`.

**Correction.** The source states the total bounds (7.2.50)–(7.2.51) with no condition. They
rest on the gap of Lemma 7.2.6, and the statement carries the number of bad iterations of
$\mathcal{K}_b$ as a parameter. When this number is bounded independently of
$\epsilon_0, \epsilon_1$, the total counts are $O(\max(\epsilon_0^{-1/2^i}, \epsilon_0^{-1},
\epsilon_0^{-1/p} \epsilon_1^{-(p+1)/p}))$.

The total counts are the sums of the counts of the two phases. When the algorithm stops, its
output satisfies Lemma 7.2.1 (`CartisGouldToint.Chapter07.lemma_7_2_1`). The constant $L_\mu$ is
given by Lemma 7.2.5 on $[f_{\mathrm{low}} - 1, f_{\mathrm{up}}]$. -/
theorem theorem_7_2_7 {ℓ : ℕ} {x₀ : ℝⁿ} {y s : ℕ → ℝⁿ} {σ : ℕ → ℝ} {k₁ : ℕ}
    (h : algorithm_7_2_1 f c C p ℓ P ε₀ ε₁ x₀ y s σ k₁ D) (hC : Chapter06.AssumptionCNe C)
    (hp : 1 ≤ p) (hℓ : 2 ≤ ℓ) {i : ℕ} (hι : 0 ≤ ((2 : ℝ) ^ i - 1) / 2 ^ i - ((ℓ : ℝ) - 1) / p)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {LΦ : ℝ} (hΦ : Chapter06.AssumptionPhiDpLC c ℓ C p LΦ)
    (hμ : AssumptionMu2DpLC f c C p) {flow fup : ℝ} (hB : AssumptionBFb f c C P.β flow fup) :
    ((funEvalCount k₁ : ℝ) ≤
        max (1 / (1 - β ^ (1 / 2 ^ i : ℝ)))
            (2 ^ i / β ^ (((ℓ : ℝ) - 1) * (((p : ℝ) + 1) / p)) *
              Chapter06.kappaSARp1CC P.toARpCCParams LΦ p) *
          (1 + |Real.log P.γ₁| / Real.log P.γ₂) *
          max (‖c (x₀)‖ ^ (1 / 2 ^ i : ℝ)) (‖c (x₀)‖ ^ (1 - ((ℓ : ℝ) - 1) / p)) /
          min ((P.θ * ε₀) ^ (1 / 2 ^ i : ℝ)) (ε₁ ^ (((p : ℝ) + 1) / p)) +
        ((|Real.log P.γ₁| + Real.log (P.toARpCCParams.sigmaMax LΦ / P.σ₀)) / Real.log P.γ₂ + 2) ∧
      (derivEvalCount (fun k => P.η₁ ≤ taylorRatio (Chapter06.PhiEll c ℓ) p y s k) k₁ : ℝ) ≤
        max (1 / (1 - β ^ (1 / 2 ^ i : ℝ)))
            (2 ^ i / β ^ (((ℓ : ℝ) - 1) * (((p : ℝ) + 1) / p)) *
              Chapter06.kappaSARp1CC P.toARpCCParams LΦ p) *
          max (‖c (x₀)‖ ^ (1 / 2 ^ i : ℝ)) (‖c (x₀)‖ ^ (1 - ((ℓ : ℝ) - 1) / p)) /
          min ((P.θ * ε₀) ^ (1 / 2 ^ i : ℝ)) (ε₁ ^ (((p : ℝ) + 1) / p)) + 2) ∧
    (‖c (y k₁)‖ ≤ P.θ * ε₀ → ∃ Lμ, 0 ≤ Lμ ∧
      (∀ K, 1 ≤ K → D.Before f c C P ε₀ ε₁ K →
        (K : ℝ) ≤ ((fup - flow + 1) / ((1 - P.θ) * ε₀) + 1) * (goodBound P Lμ p ε₀ ε₁ + 1) +
          D.badCount f c C p P ε₀ ε₁ K) ∧
      (∀ M : ℝ, (∀ K, D.Before f c C P ε₀ ε₁ K → (D.badCount f c C p P ε₀ ε₁ K : ℝ) ≤ M) →
        ∃ kε, D.IsEnd f c C P ε₀ ε₁ kε ∧
          (kε : ℝ) ≤ ((fup - flow + 1) / ((1 - P.θ) * ε₀) + 1) * (goodBound P Lμ p ε₀ ε₁ + 1) +
            M) ∧
      (∀ kε, D.IsEnd f c C P ε₀ ε₁ kε →
        (D.derivEvals f c p P kε : ℝ) ≤
          1 + goodBound P Lμ p ε₀ ε₁ * ((fup - flow + 1) / ((1 - P.θ) * ε₀) + 1) + kε ∧
        (D.funEvals kε : ℝ) ≤
          1 + (1 + |Real.log P.γ₁| / Real.log P.γ₂) *
            (goodBound P Lμ p ε₀ ε₁ * ((fup - flow + 1) / ((1 - P.θ) * ε₀) + 1) + kε) +
            Real.log (P.toARpCCParams.sigmaMax Lμ / P.σ₀) / Real.log P.γ₂ * kε)) := by
  obtain ⟨-, hF, hD⟩ := lemma_7_2_2 h hC hp hℓ hι hβ0 hβ1 hΦ
  exact ⟨⟨hF, hD⟩, fun hle => theorem_7_2_7_phase2_of_mu2 (h.phase2 hle) hC hp hB hμ⟩

/-- **Theorem 7.2.7** of [cartis2022evaluation], whole algorithm, without the bad-iteration
parameter. Assume the hypotheses of `CartisGouldToint.Chapter07.theorem_7_2_7`: C.CNe,
$p \ge 1$, $\ell \ge 2$, $\iota_1(p, \ell, i) \ge 0$, $\Phi_\ell$.DpL.C for $c$, $\mu_2$.DpL.C,
f.B.Fb and $\beta \in (0, 1)$. Assume moreover that $f$ and $c$ are $C^1$ at every point of
$\mathcal{C}$, that $\|\nabla f(x)\| \le B_f$ for every $x \in \mathcal{C}$ with
$\|c(x)\| \le \epsilon_0$, and let $\tau > 0$ with
$B_f \tau \le \epsilon_1 \theta \epsilon_0 / 2$. For a run of TPp-GC:

* Phase 1 uses at most the numbers of evaluations (7.2.23) and (7.2.24) of
  `CartisGouldToint.Chapter07.lemma_7_2_2`;
* if $\|c(x_1)\| \le \theta \epsilon_0$, there is $L_\mu \ge 0$ for which Phase 2 terminates
  within the bounds of `CartisGouldToint.Chapter07.theorem_7_2_7_phase2_of_gradient_le`.

**Correction.** This replaces the unconditional claim of the source; see
`CartisGouldToint.Chapter07.theorem_7_2_7_phase2_of_gradient_le`.

The extra hypotheses follow from f.D1pL.C and c.D1pL.C
(`CartisGouldToint.Chapter07.gradient_hyps_of_D1pLC`). The constant $L_\mu$ is given by Lemma
7.2.5 on $[f_{\mathrm{low}} - 1, f_{\mathrm{up}}]$. -/
theorem theorem_7_2_7_of_gradient_le {ℓ : ℕ} {x₀ : ℝⁿ} {y s : ℕ → ℝⁿ} {σ : ℕ → ℝ} {k₁ : ℕ}
    (h : algorithm_7_2_1 f c C p ℓ P ε₀ ε₁ x₀ y s σ k₁ D) (hC : Chapter06.AssumptionCNe C)
    (hp : 1 ≤ p) (hℓ : 2 ≤ ℓ) {i : ℕ} (hι : 0 ≤ ((2 : ℝ) ^ i - 1) / 2 ^ i - ((ℓ : ℝ) - 1) / p)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {LΦ : ℝ} (hΦ : Chapter06.AssumptionPhiDpLC c ℓ C p LΦ)
    (hμ : AssumptionMu2DpLC f c C p) {flow fup : ℝ} (hB : AssumptionBFb f c C P.β flow fup)
    (hf : ∀ x ∈ C, ContDiffAt ℝ 1 f x) (hc : ∀ x ∈ C, ContDiffAt ℝ 1 c x) {Bf : ℝ}
    (hBf : ∀ x ∈ C, ‖c x‖ ≤ ε₀ → ‖iteratedFDeriv ℝ 1 f x‖ ≤ Bf) {τ : ℝ} (hτ0 : 0 < τ)
    (hτ : Bf * τ ≤ ε₁ * (P.θ * ε₀) / 2) :
    ((funEvalCount k₁ : ℝ) ≤
        max (1 / (1 - β ^ (1 / 2 ^ i : ℝ)))
            (2 ^ i / β ^ (((ℓ : ℝ) - 1) * (((p : ℝ) + 1) / p)) *
              Chapter06.kappaSARp1CC P.toARpCCParams LΦ p) *
          (1 + |Real.log P.γ₁| / Real.log P.γ₂) *
          max (‖c (x₀)‖ ^ (1 / 2 ^ i : ℝ)) (‖c (x₀)‖ ^ (1 - ((ℓ : ℝ) - 1) / p)) /
          min ((P.θ * ε₀) ^ (1 / 2 ^ i : ℝ)) (ε₁ ^ (((p : ℝ) + 1) / p)) +
        ((|Real.log P.γ₁| + Real.log (P.toARpCCParams.sigmaMax LΦ / P.σ₀)) / Real.log P.γ₂ + 2) ∧
      (derivEvalCount (fun k => P.η₁ ≤ taylorRatio (Chapter06.PhiEll c ℓ) p y s k) k₁ : ℝ) ≤
        max (1 / (1 - β ^ (1 / 2 ^ i : ℝ)))
            (2 ^ i / β ^ (((ℓ : ℝ) - 1) * (((p : ℝ) + 1) / p)) *
              Chapter06.kappaSARp1CC P.toARpCCParams LΦ p) *
          max (‖c (x₀)‖ ^ (1 / 2 ^ i : ℝ)) (‖c (x₀)‖ ^ (1 - ((ℓ : ℝ) - 1) / p)) /
          min ((P.θ * ε₀) ^ (1 / 2 ^ i : ℝ)) (ε₁ ^ (((p : ℝ) + 1) / p)) + 2) ∧
    (‖c (y k₁)‖ ≤ P.θ * ε₀ → ∃ Lμ, 0 ≤ Lμ ∧
      (∀ K, 1 ≤ K → D.Before f c C P ε₀ ε₁ K →
        (K : ℝ) ≤ ((fup - flow + 1) / ((1 - P.θ) * ε₀) + 1) *
          (goodBound P Lμ p ε₀ (ε₁ / 2) + 1) + (fup - flow + 1) / τ) ∧
      ∃ kε, D.IsEnd f c C P ε₀ ε₁ kε ∧
        (kε : ℝ) ≤ ((fup - flow + 1) / ((1 - P.θ) * ε₀) + 1) *
          (goodBound P Lμ p ε₀ (ε₁ / 2) + 1) + (fup - flow + 1) / τ ∧
        (D.derivEvals f c p P kε : ℝ) ≤
          1 + goodBound P Lμ p ε₀ (ε₁ / 2) * ((fup - flow + 1) / ((1 - P.θ) * ε₀) + 1) + kε ∧
        (D.funEvals kε : ℝ) ≤
          1 + (1 + |Real.log P.γ₁| / Real.log P.γ₂) *
            (goodBound P Lμ p ε₀ (ε₁ / 2) * ((fup - flow + 1) / ((1 - P.θ) * ε₀) + 1) + kε) +
            Real.log (P.toARpCCParams.sigmaMax Lμ / P.σ₀) / Real.log P.γ₂ * kε) := by
  obtain ⟨-, hF, hD⟩ := lemma_7_2_2 h hC hp hℓ hι hβ0 hβ1 hΦ
  refine ⟨⟨hF, hD⟩, fun hle => ?_⟩
  obtain ⟨Lμ, hL0, hL⟩ := lemma_7_2_5 hμ hp (flow - 1) fup
  exact ⟨Lμ, hL0, theorem_7_2_7_phase2_of_gradient_le (h.phase2 hle) hC hp hB hL hf hc hBf hτ0 hτ⟩

/-- Let $p \ge 1$, and assume f.D1pL.C and c.D1pL.C. Then $f$ and $c$ are $C^1$ at every point of
$\mathcal{C}$, and there is $B_f$ with $\|\nabla f(x)\| \le B_f$ for every $x \in \mathcal{C}$
with $\|c(x)\| \le \epsilon_0$. These are the extra hypotheses of
`CartisGouldToint.Chapter07.theorem_7_2_7_of_gradient_le`. -/
theorem gradient_hyps_of_D1pLC (hf : AssumptionFD1pLC f C p) (hc : AssumptionCD1pLC c C p)
    (hp : 1 ≤ p) :
    (∀ x ∈ C, ContDiffAt ℝ 1 f x) ∧ (∀ x ∈ C, ContDiffAt ℝ 1 c x) ∧
      ∃ Bf, ∀ x ∈ C, ‖c x‖ ≤ ε₀ → ‖iteratedFDeriv ℝ 1 f x‖ ≤ Bf := by
  have hp' : ((1 : ℕ) : WithTop ℕ∞) ≤ p := by exact_mod_cast hp
  have key : ∀ {g : ℝⁿ → ℝ}, IsD1pLOn g C p → ∀ x ∈ C, ContDiffAt ℝ 1 g x := by
    intro g hg x hx
    obtain ⟨U, hU, hCU, hgU⟩ := hg.1
    exact (hgU.contDiffAt (hU.mem_nhds (hCU hx))).of_le hp'
  refine ⟨key hf, fun x hx => contDiffAt_euclidean.2 fun j => key (hc j) x hx, ?_⟩
  obtain ⟨-, B, hB⟩ := hf.2 1 (Finset.mem_Icc.2 ⟨le_rfl, hp⟩)
  exact ⟨B, fun x hx _ => hB x hx⟩

end BookHypotheses

end CartisGouldToint.Chapter07
