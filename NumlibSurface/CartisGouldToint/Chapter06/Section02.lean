/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Calculus.MultivariateTaylor.Coord
import Numlib.Optimization.ModelBased.ConvexConstrained
import NumlibSurface.CartisGouldToint.Chapter02.Section04
import NumlibSurface.CartisGouldToint.Chapter06.Section01

/-!
# Cartis, Gould and Toint, Section 6.2: The ARp-CC algorithm and its complexity

This module formalizes Section 6.2 of [cartis2022evaluation]: adaptive regularization with $p$-th
order models over a closed convex set $\mathcal{C} \subseteq \mathbb{R}^n$. The algorithm ARp-CC
(Algorithm 6.2.1) seeks an approximate minimizer of order $q \in \{1, 2, 3\}$ within $\mathcal{C}$
in the sense of Section 6.1. At iteration $k$ the model is
$$m_k(s) = T_{f,p}(x_k, s) + \frac{\sigma_k}{(p+1)!} \|s\|^{p+1} \quad \text{(4.1.2)},$$
and the step $s_k$ must keep $x_k + s_k$ in $\mathcal{C}$, decrease the model, and make the model
measures (6.2.3)–(6.2.5) of order at most $q$ small. Lemmas 6.2.1 and 6.2.2 show that a successful
step either decreases $f$ by a fixed amount or leads to termination, and Theorem 6.2.3 bounds the
number of evaluations by $O(\max_j \epsilon_j^{-(p+1)/(p-j+1)})$. The first-order variant ARp1-CC
(Algorithm 6.2.2) replaces the step condition by $\omega_{m_k,\mathcal{M},1}(s_k) \le \theta_1
\|s_k\|^p$; Lemma 6.2.4 and Theorem 6.2.5 give its complexity $O(\epsilon_1^{-(p+1)/p})$.

The model is `Optimization.regularizedModel (ftaylorSeries ℝ f (x k)) p (σ k)`, and runs are
instances of the generic adaptive-regularization run `Optimization.IsARRun` with the ratio
`Optimization.taylorRatio`. The model counterparts (6.2.1)–(6.2.5) of the sets and measures of
Section 6.1 are `Optimization.restrictedSteps` and `Optimization.formCriticality` of the derivative
tensors of the model.

## Main definitions

* Equations (6.2.1)–(6.2.2), `CartisGouldToint.Chapter06.modelSteps₀`,
  `CartisGouldToint.Chapter06.modelSteps₁`, `CartisGouldToint.Chapter06.modelSteps₂`: the model sets
  $\mathcal{M}^0_k(s)$, $\mathcal{M}^1_k(s)$ and $\mathcal{M}^2_k(s)$.
* Equations (6.2.3)–(6.2.5), `CartisGouldToint.Chapter06.modelOmega1`,
  `CartisGouldToint.Chapter06.modelOmega2`, `CartisGouldToint.Chapter06.modelOmega3`: the model
  measures $\omega_{m_k,\mathcal{M},j}(s)$ for $j = 1, 2, 3$.
* Equation (6.2.7), `CartisGouldToint.Chapter06.ARpCCParams`: the algorithmic constants of ARp-CC.
* Equations (6.2.10)–(6.2.12), `CartisGouldToint.Chapter06.IsARpCCStep`: the conditions of Step 2 of
  ARp-CC.
* Algorithm 6.2.1, `CartisGouldToint.Chapter06.algorithm_6_2_1`: a run of ARp-CC.
* Assumption f.bB.C, `CartisGouldToint.Chapter06.AssumptionBbC`: $f$ is bounded below on
  $\mathcal{C}$.
* Assumption f.DpL.C, `CartisGouldToint.Chapter06.AssumptionDpLC`: $f$ is $p$ times continuously
  differentiable near $\mathcal{C}$, and its $p$-th derivative is Lipschitz on $\mathcal{C}$.
* Equations (6.2.14) and (6.2.16), `CartisGouldToint.Chapter06.omegaNext2`,
  `CartisGouldToint.Chapter06.omegaNext3`: the mixed measures $\omega_{k+1,2}$ and $\omega_{k+1,3}$.
* Lemma 6.2.2, `CartisGouldToint.Chapter06.kappaCC`: the constants $\kappa^{cc}_j$.
* Theorem 6.2.3, `CartisGouldToint.Chapter06.kappaSARpCC`, `CartisGouldToint.Chapter06.kappaAARpCC`,
  `CartisGouldToint.Chapter06.kappaCARpCC`, `CartisGouldToint.Chapter06.tolMin`: the constants
  $\kappa^S$, $\kappa^A$, $\kappa^C$ and the accuracy term $\min_j \epsilon_j^{(p+1)/(p-j+1)}$.
* Algorithm 6.2.2, `CartisGouldToint.Chapter06.algorithm_6_2_2`: a run of ARp1-CC.
* Theorem 6.2.5, `CartisGouldToint.Chapter06.kappa1CC`, `CartisGouldToint.Chapter06.kappaSARp1CC`,
  `CartisGouldToint.Chapter06.kappaAARp1CC`: the constants $\kappa_1$ of (4.1.32), $\kappa^S$ and
  $\kappa^A$ of ARp1-CC.

## Main results

* Algorithm 6.2.1, `CartisGouldToint.Chapter06.exists_algorithm_6_2_1_of_forall_exists_step`,
  `CartisGouldToint.Chapter06.exists_algorithm_6_2_1_one`: ARp-CC runs exist when Step 2 is always
  feasible, in particular for $q = 1$.
* Algorithm 6.2.1, `CartisGouldToint.Chapter06.algorithm_6_2_1_not_exists_step`: Step 2 can be
  infeasible for $q \ge 2$.
* Section 6.2.2, `CartisGouldToint.Chapter06.arpcc_sigma_le`,
  `CartisGouldToint.Chapter06.arpcc_sub_ge`: Lemmas 4.1.1 and 4.1.2 continue to hold.
* Lemma 6.2.1, `CartisGouldToint.Chapter06.lemma_6_2_1_i`,
  `CartisGouldToint.Chapter06.lemma_6_2_1_ii`, `CartisGouldToint.Chapter06.lemma_6_2_1_iii`,
  `CartisGouldToint.Chapter06.lemma_6_2_1_iv`: lower bounds on the step length and bounds on the
  model derivatives on a successful iteration.
* Lemma 6.2.2, `CartisGouldToint.Chapter06.lemma_6_2_2`: the decrease of $f$ on a successful
  iteration where an objective measure is large.
* Theorem 6.2.3, `CartisGouldToint.Chapter06.arpcc_decrease_of_not_test`,
  `CartisGouldToint.Chapter06.theorem_6_2_3`: the decrease on successful iterations and the
  evaluation complexity of ARp-CC.
* Algorithm 6.2.2, `CartisGouldToint.Chapter06.exists_algorithm_6_2_2`: ARp1-CC runs exist.
* Lemma 6.2.4, `CartisGouldToint.Chapter06.lemma_6_2_4`: the decrease of $f$ on a successful
  iteration of ARp1-CC.
* Theorem 6.2.5, `CartisGouldToint.Chapter06.theorem_6_2_5`: the evaluation complexity of ARp1-CC.

## Conventions

* The order of the sought minimizer is an explicit $q \in \{1, 2, 3\}$, and all tolerances are
  finite positive reals. The tests and the step conditions of order greater than $q$ are switched
  off.

## Deviations from the source

* **Model measures (6.2.3)–(6.2.5), (6.2.14) and (6.2.16)** (generalization). The supremum
  convention assigns zero on an empty direction set, as for the measures in §6.1.1.
* **Order of the sought minimizer** (reading). The source selects the order by infinite tolerances
  ($\epsilon_2 = \epsilon_3 = \infty$ for first order, $\epsilon_3 = \infty$ for second order). Here
  the order is an explicit $q \in \{1, 2, 3\}$. See `CartisGouldToint.Chapter06.algorithm_6_2_1`.
* **Orders and degree** (reading). Second order needs $p \ge 2$ and third order needs $p \ge 3$; all
  complexity results assume $q \le p$. The run predicate itself leaves this bound
  to its callers. See `CartisGouldToint.Chapter06.theorem_6_2_3`.
* **Algorithm 6.2.1, Step 2** (correction). For $q \ge 2$, Step 2 can be infeasible, even at a
  strict global minimizer of $f$ on $\mathcal{C}$. Theorem 6.2.3 holds for every run; runs exist for
  $q = 1$, and for $q \ge 2$ whenever Step 2 is always feasible. See
  `CartisGouldToint.Chapter06.algorithm_6_2_1_not_exists_step`.
* **Lemma 6.2.1, (6.2.18)–(6.2.19)** (correction). The bounds are proved only for $\|d\| \le 1$,
  which is what the proof through (6.2.23) gives and what the measures use. The unrestricted
  bounds can fail for an accepted step. See
  `CartisGouldToint.Chapter06.lemma_6_2_1_iv`.
* **Lemma 6.2.2** (typo). The prefactor of $\kappa^{cc}_j$ is $\eta_1 \sigma_{\min} / (p+1)!$, not
  $\eta_1 \sigma_{\min} / p!$. See `CartisGouldToint.Chapter06.lemma_6_2_2`.
* **Theorems 6.2.3 and 6.2.5** (generalization). The restriction $\epsilon_j \le 1$ is not needed.
  See `CartisGouldToint.Chapter06.theorem_6_2_3` and `CartisGouldToint.Chapter06.theorem_6_2_5`.
* **Existence of runs** (generalization). Assumption f.DpL.C asks for $f$ to be $p$ times
  continuously differentiable on an open set $\mathcal{D} \supseteq \mathcal{C}$. The existence
  theorems use only this property at the points of $\mathcal{C}$. See
  `CartisGouldToint.Chapter06.exists_algorithm_6_2_1_one` and
  `CartisGouldToint.Chapter06.exists_algorithm_6_2_2`.
-/

open Set Metric Optimization
open scoped Nat

namespace CartisGouldToint.Chapter06

variable {n : ℕ}

set_option hygiene false in
local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-! ### Assumptions and constants -/

/-- **Assumption f.bB.C** of [cartis2022evaluation], Section 6.2.2. A function
$f : \mathbb{R}^n \to \mathbb{R}$ is bounded below on $\mathcal{C}$ by $f_{\mathrm{low}}$ if
$f(x) \ge f_{\mathrm{low}}$ for all $x \in \mathcal{C}$. -/
def AssumptionBbC (f : ℝⁿ → ℝ) (C : Set ℝⁿ) (flow : ℝ) : Prop :=
  ∀ x ∈ C, flow ≤ f x

/-- Assumption f.bB.C holds if and only if $f(x) \ge f_{\mathrm{low}}$ for all $x \in \mathcal{C}$.
-/
theorem assumptionBbC_iff {f : ℝⁿ → ℝ} {C : Set ℝⁿ} {flow : ℝ} :
    AssumptionBbC f C flow ↔ ∀ x ∈ C, flow ≤ f x := Iff.rfl

/-- **Assumption f.DpL.C** of [cartis2022evaluation], Section 6.2.2. Let
$f : \mathbb{R}^n \to \mathbb{R}$, $\mathcal{C} \subseteq \mathbb{R}^n$, $p \in \mathbb{N}$ and
$L \in \mathbb{R}$. The assumption holds if $L \ge 0$, $f$ is $p$ times continuously
differentiable on an open set $\mathcal{D} \supseteq \mathcal{C}$, and the $p$-th derivative
tensor of $f$ is Lipschitz continuous on $\mathcal{C}$ with constant $L$.

The norm of the derivative tensor is the operator norm, as in (A.7). -/
structure AssumptionDpLC (f : ℝⁿ → ℝ) (C : Set ℝⁿ) (p : ℕ) (L : ℝ) : Prop where
  /-- The Lipschitz constant $L_{f,p}$ is nonnegative. -/
  nonneg : 0 ≤ L
  /-- The function $f$ is $p$ times continuously differentiable on an open set that contains
  $\mathcal{C}$. -/
  contDiffOn : ∃ D, IsOpen D ∧ C ⊆ D ∧ ContDiffOn ℝ p f D
  /-- The $p$-th derivative $\nabla^p f$ is Lipschitz continuous on $\mathcal{C}$ with constant $L$.
  -/
  lipschitz : IteratedFDerivLipschitzOn f p L C

/-- Assumption f.DpL.C holds if and only if $L \ge 0$, $f$ is $p$ times continuously differentiable
on an open set that contains $\mathcal{C}$, and $\nabla^p f$ is Lipschitz continuous on
$\mathcal{C}$ with constant $L$ (`IteratedFDerivLipschitzOn f p L C`). -/
theorem assumptionDpLC_iff {f : ℝⁿ → ℝ} {C : Set ℝⁿ} {p : ℕ} {L : ℝ} :
    AssumptionDpLC f C p L ↔ 0 ≤ L ∧ (∃ D, IsOpen D ∧ C ⊆ D ∧ ContDiffOn ℝ p f D) ∧
      IteratedFDerivLipschitzOn f p L C :=
  ⟨fun h => ⟨h.nonneg, h.contDiffOn, h.lipschitz⟩, fun ⟨h1, h2, h3⟩ => ⟨h1, h2, h3⟩⟩

/-- Under f.DpL.C, $f$ is $p$ times continuously differentiable at every point of $\mathcal{C}$. -/
theorem AssumptionDpLC.contDiffAt {f : ℝⁿ → ℝ} {C : Set ℝⁿ} {p : ℕ} {L : ℝ}
    (h : AssumptionDpLC f C p L) : ∀ y ∈ C, ContDiffAt ℝ p f y := by
  obtain ⟨D, hD, hCD, hf⟩ := h.contDiffOn
  exact fun y hy => hf.contDiffAt (hD.mem_nhds (hCD hy))

/-- **Equation (6.2.7)** of [cartis2022evaluation], the constants of Algorithm 6.2.1. A set of
**ARp-CC constants** consists of the constants of adaptive regularization, $\sigma_0 > 0$,
$\sigma_{\min} \in (0, \sigma_0]$, $0 < \eta_1 \le \eta_2 < 1$ and
$0 < \gamma_1 < 1 < \gamma_2 < \gamma_3$, together with
$\theta_1, \theta_2, \theta_3 \in (0, 1)$ and $\tau_1, \tau_2 \in (0, 1)$ such that
$$\frac{1 + \tau_1}{2} \le \theta_1, \qquad \frac{1 + \tau_2}{2} \le \theta_2.$$

The constants of adaptive regularization are `CartisGouldToint.Chapter02.ARParams`. -/
structure ARpCCParams extends toChapter02ARParams : Chapter02.ARParams where
  /-- The first-order model tolerance factor $\theta_1$. -/
  θ₁ : ℝ
  /-- The second-order model tolerance factor $\theta_2$. -/
  θ₂ : ℝ
  /-- The third-order model tolerance factor $\theta_3$. -/
  θ₃ : ℝ
  /-- The first-order restriction factor $\tau_1$ of (6.1.8). -/
  τ₁ : ℝ
  /-- The second-order restriction factor $\tau_2$ of (6.1.10). -/
  τ₂ : ℝ
  /-- The factor $\theta_1$ is positive. -/
  θ₁_pos : 0 < θ₁
  /-- The factor $\theta_1$ is less than $1$. -/
  θ₁_lt_one : θ₁ < 1
  /-- The factor $\theta_2$ is positive. -/
  θ₂_pos : 0 < θ₂
  /-- The factor $\theta_2$ is less than $1$. -/
  θ₂_lt_one : θ₂ < 1
  /-- The factor $\theta_3$ is positive. -/
  θ₃_pos : 0 < θ₃
  /-- The factor $\theta_3$ is less than $1$. -/
  θ₃_lt_one : θ₃ < 1
  /-- The factor $\tau_1$ is positive. -/
  τ₁_pos : 0 < τ₁
  /-- The factor $\tau_1$ is less than $1$. -/
  τ₁_lt_one : τ₁ < 1
  /-- The factor $\tau_2$ is positive. -/
  τ₂_pos : 0 < τ₂
  /-- The factor $\tau_2$ is less than $1$. -/
  τ₂_lt_one : τ₂ < 1
  /-- The inequality $(1 + \tau_1)/2 \le \theta_1$ holds. -/
  τ₁_le_θ₁ : (1 + τ₁) / 2 ≤ θ₁
  /-- The inequality $(1 + \tau_2)/2 \le \theta_2$ holds. -/
  τ₂_le_θ₂ : (1 + τ₂) / 2 ≤ θ₂

namespace ARpCCParams

variable (P : ARpCCParams)

/-- The bound $\sigma_{\max} = \max(\sigma_0, \gamma_3 L / (1 - \eta_2))$ of (4.1.19) on the
regularization weight. -/
noncomputable def sigmaMax (L : ℝ) : ℝ := arSigmaMax P.toARParams L

/-- The bound $\sigma_{\max}$ is positive. -/
theorem sigmaMax_pos (L : ℝ) : 0 < P.sigmaMax L := arSigmaMax_pos _ L

/-- The constants satisfy $1 - \theta_1 + \tau_1 \le \theta_1$, by (6.2.7). -/
theorem one_sub_θ₁_add_τ₁_le : 1 - P.θ₁ + P.τ₁ ≤ P.θ₁ := by linarith [P.τ₁_le_θ₁]

/-- The constants satisfy $1 - \theta_2 + \tau_2 \le \theta_2$, by (6.2.7). -/
theorem one_sub_θ₂_add_τ₂_le : 1 - P.θ₂ + P.τ₂ ≤ P.θ₂ := by linarith [P.τ₂_le_θ₂]

end ARpCCParams

/-! ### Model measures and the algorithm -/

/-- **Equation (6.2.1)** of [cartis2022evaluation], the set $\mathcal{M}^0_k$. Let
$\mathcal{C} \subseteq \mathbb{R}^n$ and $x, s \in \mathbb{R}^n$. The set of **feasible model
steps** at $s$ is $\mathcal{M}^0_k(s) = \mathcal{C}(x + s) = \{d \mid x + s + d \in
\mathcal{C}\}$. -/
noncomputable def modelSteps₀ (C : Set ℝⁿ) (x s : ℝⁿ) : Set ℝⁿ := feasibleSteps C (x + s)

/-- **Equation (6.2.1)** of [cartis2022evaluation], the set $\mathcal{M}^1_k$. Let
$f : \mathbb{R}^n \to \mathbb{R}$, $\mathcal{C} \subseteq \mathbb{R}^n$, $p \in \mathbb{N}$,
$\theta_1, \epsilon_1, \sigma \in \mathbb{R}$ and $x, s \in \mathbb{R}^n$, and let $m_k$ be the
regularized Taylor model of $f$ at $x$ of degree $p$ with weight $\sigma$. The set of
**first-order restricted model steps** is
$$\mathcal{M}^1_k(s) = \{d \in \mathcal{M}^0_k(s) \mid |\nabla_s m_k(s)[d]| \le \theta_1
  \epsilon_1\}.$$

The model $m_k$ is `Optimization.regularizedModel (ftaylorSeries ℝ f x) p σ`. -/
noncomputable def modelSteps₁ (f : ℝⁿ → ℝ) (C : Set ℝⁿ) (p : ℕ) (θ₁ ε₁ : ℝ) (x : ℝⁿ) (σ : ℝ)
    (s : ℝⁿ) : Set ℝⁿ :=
  restrictedSteps (iteratedFDeriv ℝ 1 (regularizedModel (ftaylorSeries ℝ f x) p σ) s) (θ₁ * ε₁)
    (modelSteps₀ C x s)

/-- **Equation (6.2.2)** of [cartis2022evaluation]. With the notation of (6.2.1) and
$\theta_2, \epsilon_2 \in \mathbb{R}$, the set of **second-order restricted model steps** is
$$\mathcal{M}^2_k(s) = \{d \in \mathcal{M}^1_k(s) \mid |\nabla^2_s m_k(s)[d]^2| \le \theta_2
  \epsilon_2\}.$$
-/
noncomputable def modelSteps₂ (f : ℝⁿ → ℝ) (C : Set ℝⁿ) (p : ℕ) (θ₁ θ₂ ε₁ ε₂ : ℝ) (x : ℝⁿ) (σ : ℝ)
    (s : ℝⁿ) : Set ℝⁿ :=
  restrictedSteps (iteratedFDeriv ℝ 2 (regularizedModel (ftaylorSeries ℝ f x) p σ) s) (θ₂ * ε₂)
    (modelSteps₁ f C p θ₁ ε₁ x σ s)

/-- **Equation (6.2.3)** of [cartis2022evaluation]. With the notation of (6.2.1), the **first-order
model measure** is
$$\omega_{m_k,\mathcal{M},1}(s) = -\min_{d \in \mathcal{M}^0_k(s) \cap \mathcal{B}} \nabla_s
  m_k(s)[d].$$

The minimum is the supremum `Optimization.formCriticality`, which gives zero
on an empty direction set as in §6.1.1.

**Reading.** Matches the negative minimum on the source domain and gives zero for an empty direction
set.
-/
noncomputable def modelOmega1 (f : ℝⁿ → ℝ) (C : Set ℝⁿ) (p : ℕ) (x : ℝⁿ) (σ : ℝ) (s : ℝⁿ) :
    ℝ :=
  formCriticality (iteratedFDeriv ℝ 1 (regularizedModel (ftaylorSeries ℝ f x) p σ) s)
    (modelSteps₀ C x s)

/-- **Equation (6.2.4)** of [cartis2022evaluation]. With the notation of (6.2.1), the **second-order
model measure** is
$$\omega_{m_k,\mathcal{M},2}(s) = -\min_{d \in \mathcal{M}^1_k(s) \cap \mathcal{B}} \nabla^2_s
  m_k(s)[d]^2.$$

The same empty-set convention as in `CartisGouldToint.Chapter06.modelOmega1` applies.

**Reading.** Uses the first model-restricted set and totalizes an empty intersection with the unit
ball.
-/
noncomputable def modelOmega2 (f : ℝⁿ → ℝ) (C : Set ℝⁿ) (p : ℕ) (θ₁ ε₁ : ℝ) (x : ℝⁿ) (σ : ℝ)
    (s : ℝⁿ) : ℝ :=
  formCriticality (iteratedFDeriv ℝ 2 (regularizedModel (ftaylorSeries ℝ f x) p σ) s)
    (modelSteps₁ f C p θ₁ ε₁ x σ s)

/-- **Equation (6.2.5)** of [cartis2022evaluation]. With the notation of (6.2.1) and (6.2.2), the
**third-order model measure** is
$$\omega_{m_k,\mathcal{M},3}(s) = -\min_{d \in \mathcal{M}^2_k(s) \cap \mathcal{B}} \nabla^3_s
  m_k(s)[d]^3.$$

The same empty-set convention as in `CartisGouldToint.Chapter06.modelOmega1` applies.

**Reading.** Uses the second model-restricted set and totalizes an empty intersection with the unit
ball.
-/
noncomputable def modelOmega3 (f : ℝⁿ → ℝ) (C : Set ℝⁿ) (p : ℕ) (θ₁ θ₂ ε₁ ε₂ : ℝ) (x : ℝⁿ)
    (σ : ℝ) (s : ℝⁿ) : ℝ :=
  formCriticality (iteratedFDeriv ℝ 3 (regularizedModel (ftaylorSeries ℝ f x) p σ) s)
    (modelSteps₂ f C p θ₁ θ₂ ε₁ ε₂ x σ s)

/-- **Equations (6.2.10)–(6.2.12)** of [cartis2022evaluation], Step 2 of Algorithm 6.2.1. Let
$f : \mathbb{R}^n \to \mathbb{R}$, $\mathcal{C} \subseteq \mathbb{R}^n$, $p, q \in \mathbb{N}$,
ARp-CC constants $P$, tolerances $\epsilon_1, \epsilon_2, \epsilon_3$, a point $x$ and a weight
$\sigma$, and let $m$ be the regularized Taylor model of $f$ at $x$ of degree $p$ with weight
$\sigma$. A step $s$ satisfies the **Step 2 conditions of ARp-CC** of order $q$ if
$x + s \in \mathcal{C}$, $m(s) < m(0)$,
$$\omega_{m,\mathcal{M},1}(s) \le \theta_1 \epsilon_1 \quad \text{(6.2.10)},$$
$\omega_{m,\mathcal{M},2}(s) \le \theta_2 \epsilon_2$ (6.2.11) if $q \ge 2$, and
$\omega_{m,\mathcal{M},3}(s) \le \theta_3 \epsilon_3$ (6.2.12) if $q \ge 3$. -/
structure IsARpCCStep (f : ℝⁿ → ℝ) (C : Set ℝⁿ) (p : ℕ) (P : ARpCCParams) (q : ℕ)
    (ε₁ ε₂ ε₃ : ℝ) (x : ℝⁿ) (σ : ℝ) (s : ℝⁿ) : Prop where
  /-- The trial point is feasible: $s \in \mathcal{C}(x)$. -/
  mem : x + s ∈ C
  /-- The step decreases the model: $m(s) < m(0)$. -/
  decrease : regularizedModel (ftaylorSeries ℝ f x) p σ s <
    regularizedModel (ftaylorSeries ℝ f x) p σ 0
  /-- The first-order model measure is small, (6.2.10). -/
  omega1_le : modelOmega1 f C p x σ s ≤ P.θ₁ * ε₁
  /-- For $q \ge 2$, the second-order model measure is small, (6.2.11). -/
  omega2_le : 2 ≤ q → modelOmega2 f C p P.θ₁ ε₁ x σ s ≤ P.θ₂ * ε₂
  /-- For $q \ge 3$, the third-order model measure is small, (6.2.12). -/
  omega3_le : 3 ≤ q → modelOmega3 f C p P.θ₁ P.θ₂ ε₁ ε₂ x σ s ≤ P.θ₃ * ε₃

/-- **Algorithm 6.2.1** of [cartis2022evaluation] (ARp-CC). Let $f : \mathbb{R}^n \to \mathbb{R}$,
$\mathcal{C} \subseteq \mathbb{R}^n$, $p, q \in \mathbb{N}$, ARp-CC constants $P$ and
$\epsilon_1, \epsilon_2, \epsilon_3 \in \mathbb{R}$. Sequences of iterates $x_k$, trial steps
$s_k$ and regularization weights $\sigma_k$ form a **run of ARp-CC of order $q$** if
$\epsilon_1, \epsilon_2, \epsilon_3 > 0$, $1 \le q \le 3$, $x_0 \in \mathcal{C}$, and they form
an adaptive-regularization run in which the Step 1 test is "$x_k$ is an approximate minimizer of
order $q$ within $\mathcal{C}$", the step $s_k$ satisfies the Step 2 conditions
(6.2.10)–(6.2.12), and Steps 3–4 use the ratio (4.1.15) and the update of the regularization
weight.

**Reading.** The source selects the order by infinite tolerances; here $q$ is explicit and the
tolerances are finite. The run predicate leaves $q \le p$ to the results that
use the derivatives of all requested orders.

The run is `Optimization.IsARRun` with the test `CartisGouldToint.Chapter06.IsApproxMinimizerCC`
for the factors $\tau_1, \tau_2$ of $P$, the step conditions
`CartisGouldToint.Chapter06.IsARpCCStep`, and the ratio `Optimization.taylorRatio f p`. -/
structure algorithm_6_2_1 (f : ℝⁿ → ℝ) (C : Set ℝⁿ) (p : ℕ) (P : ARpCCParams) (q : ℕ)
    (ε₁ ε₂ ε₃ : ℝ) (x s : ℕ → ℝⁿ) (σ : ℕ → ℝ) : Prop where
  /-- The tolerance $\epsilon_1$ is positive. -/
  ε₁_pos : 0 < ε₁
  /-- The tolerance $\epsilon_2$ is positive. -/
  ε₂_pos : 0 < ε₂
  /-- The tolerance $\epsilon_3$ is positive. -/
  ε₃_pos : 0 < ε₃
  /-- The order satisfies $q \ge 1$. -/
  one_le_q : 1 ≤ q
  /-- The order satisfies $q \le 3$. -/
  q_le_three : q ≤ 3
  /-- The initial point $x_0$ lies in $\mathcal{C}$. -/
  mem_zero : x 0 ∈ C
  /-- The sequences follow Steps 1–4 of the algorithm. -/
  run : IsARRun P.toARParams (fun k => IsApproxMinimizerCC f C P.τ₁ P.τ₂ q ε₁ ε₂ ε₃ (x k))
    (fun k => IsARpCCStep f C p P q ε₁ ε₂ ε₃ (x k) (σ k) (s k)) (fun _ => False)
    (taylorRatio f p x s) x s σ

/-- **Algorithm 6.2.2** of [cartis2022evaluation] (ARp1-CC). Let $f : \mathbb{R}^n \to \mathbb{R}$,
$\mathcal{C} \subseteq \mathbb{R}^n$, $p \in \mathbb{N}$, ARp-CC constants $P$ and
$\epsilon_1 \in \mathbb{R}$. Sequences $x_k$, $s_k$ and $\sigma_k$ form a **run of ARp1-CC** if
$\epsilon_1 > 0$, $x_0 \in \mathcal{C}$, and they form an adaptive-regularization run with the
Step 1 test $\omega_{f,\mathcal{C},1}(x_k) \le \epsilon_1$ and the step conditions
$x_k + s_k \in \mathcal{C}$, $m_k(s_k) < m_k(0)$ and
$$\omega_{m_k,\mathcal{M},1}(s_k) \le \theta_1 \|s_k\|^p \quad \text{(6.2.29)}.$$
This is ARp-CC for a first-order minimizer ($\epsilon_2 = \epsilon_3 = \infty$) with the
condition (6.2.10) replaced by (6.2.29).

The step conditions are `Optimization.IsFirstOrderCCStep`. -/
structure algorithm_6_2_2 (f : ℝⁿ → ℝ) (C : Set ℝⁿ) (p : ℕ) (P : ARpCCParams) (ε₁ : ℝ)
    (x s : ℕ → ℝⁿ) (σ : ℕ → ℝ) : Prop where
  /-- The tolerance $\epsilon_1$ is positive. -/
  ε₁_pos : 0 < ε₁
  /-- The initial point $x_0$ lies in $\mathcal{C}$. -/
  mem_zero : x 0 ∈ C
  /-- The sequences follow Steps 1–4 of the algorithm. -/
  run : IsARRun P.toARParams (fun k => omega1 f C (x k) ≤ ε₁)
    (fun k => IsFirstOrderCCStep f C p P.θ₁ (x k) (σ k) (s k)) (fun _ => False)
    (taylorRatio f p x s) x s σ

/-- **Equation (6.2.14)** of [cartis2022evaluation]. With the notation of (6.2.1), the **mixed
second-order measure** combines the objective tensor at $x + s$ with the model set:
$$\omega_{k+1,2} = -\min_{d \in \mathcal{M}^1_k(s) \cap \mathcal{B}} \nabla^2 f(x + s)[d]^2.$$

**Reading.** The objective Hessian is evaluated at the trial point on the model-defined first
restricted set, with an empty-set convention.
-/
noncomputable def omegaNext2 (f : ℝⁿ → ℝ) (C : Set ℝⁿ) (p : ℕ) (θ₁ ε₁ : ℝ) (x : ℝⁿ) (σ : ℝ)
    (s : ℝⁿ) : ℝ :=
  formCriticality (iteratedFDeriv ℝ 2 f (x + s)) (modelSteps₁ f C p θ₁ ε₁ x σ s)

/-- **Equation (6.2.16)** of [cartis2022evaluation]. With the notation of (6.2.1) and (6.2.2), the
**mixed third-order measure** is
$$\omega_{k+1,3} = -\min_{d \in \mathcal{M}^2_k(s) \cap \mathcal{B}} \nabla^3 f(x + s)[d]^3.$$

**Reading.** The objective third derivative is evaluated at the trial point on the model-defined
second restricted set, with an empty-set convention.
-/
noncomputable def omegaNext3 (f : ℝⁿ → ℝ) (C : Set ℝⁿ) (p : ℕ) (θ₁ θ₂ ε₁ ε₂ : ℝ) (x : ℝⁿ)
    (σ : ℝ) (s : ℝⁿ) : ℝ :=
  formCriticality (iteratedFDeriv ℝ 3 f (x + s)) (modelSteps₂ f C p θ₁ θ₂ ε₁ ε₂ x σ s)

section Membership

variable {f : ℝⁿ → ℝ} {C : Set ℝⁿ} {p : ℕ} {θ₁ θ₂ ε₁ ε₂ σ : ℝ} {x s d : ℝⁿ}

/-- A step $d$ lies in $\mathcal{M}^0_k(s)$ if and only if $x + s + d \in \mathcal{C}$. -/
theorem mem_modelSteps₀ : d ∈ modelSteps₀ C x s ↔ x + s + d ∈ C := Iff.rfl

/-- A step $d$ lies in $\mathcal{M}^1_k(s)$ if and only if $d \in \mathcal{M}^0_k(s)$ and
$|\nabla_s m_k(s)[d]| \le \theta_1 \epsilon_1$. -/
theorem mem_modelSteps₁ :
    d ∈ modelSteps₁ f C p θ₁ ε₁ x σ s ↔ d ∈ modelSteps₀ C x s ∧
      |iteratedFDeriv ℝ 1 (regularizedModel (ftaylorSeries ℝ f x) p σ) s (fun _ => d)| ≤
        θ₁ * ε₁ := Iff.rfl

/-- A step $d$ lies in $\mathcal{M}^2_k(s)$ if and only if $d \in \mathcal{M}^1_k(s)$ and
$|\nabla^2_s m_k(s)[d]^2| \le \theta_2 \epsilon_2$. -/
theorem mem_modelSteps₂ :
    d ∈ modelSteps₂ f C p θ₁ θ₂ ε₁ ε₂ x σ s ↔ d ∈ modelSteps₁ f C p θ₁ ε₁ x σ s ∧
      |iteratedFDeriv ℝ 2 (regularizedModel (ftaylorSeries ℝ f x) p σ) s (fun _ => d)| ≤
        θ₂ * ε₂ := Iff.rfl

/-- If $x + s \in \mathcal{C}$, then $0 \in \mathcal{M}^0_k(s)$. -/
theorem zero_mem_modelSteps₀ (h : x + s ∈ C) : 0 ∈ modelSteps₀ C x s := by
  simpa [mem_modelSteps₀] using h

/-- If $x + s \in \mathcal{C}$ and $\theta_1 \epsilon_1 \ge 0$, then $0 \in \mathcal{M}^1_k(s)$. -/
theorem zero_mem_modelSteps₁ (h : x + s ∈ C) (hε : 0 ≤ θ₁ * ε₁) :
    0 ∈ modelSteps₁ f C p θ₁ ε₁ x σ s :=
  (zero_mem_restrictedSteps le_rfl hε).2 (zero_mem_modelSteps₀ h)

/-- If $x + s \in \mathcal{C}$, $\theta_1 \epsilon_1 \ge 0$ and $\theta_2 \epsilon_2 \ge 0$, then
$0 \in \mathcal{M}^2_k(s)$. -/
theorem zero_mem_modelSteps₂ (h : x + s ∈ C) (hε₁ : 0 ≤ θ₁ * ε₁) (hε₂ : 0 ≤ θ₂ * ε₂) :
    0 ∈ modelSteps₂ f C p θ₁ θ₂ ε₁ ε₂ x σ s :=
  (zero_mem_restrictedSteps one_le_two hε₂).2 (zero_mem_modelSteps₁ h hε₁)

/-- The set $\mathcal{M}^0_k(s)$ is the set $\mathcal{C}(x + s)$ of feasible steps at $x + s$, so
$\omega_{m,\mathcal{M},1}(s)$ and $\omega_{f,\mathcal{C},1}(x + s)$ range over the same set. -/
theorem modelSteps₀_eq : modelSteps₀ C x s = feasibleSteps C (x + s) := rfl

end Membership

/-! ### Lemmas 4.1.1 and 4.1.2 for convexly constrained runs -/

section Generic

variable {f : ℝⁿ → ℝ} {C : Set ℝⁿ} {p : ℕ} {L : ℝ} {P : ARpCCParams}
  {test step : ℕ → Prop} {x s : ℕ → ℝⁿ} {σ : ℕ → ℝ}

/-- **Section 6.2.2** of [cartis2022evaluation], "Lemma 4.1.2 continues to hold". Let $\mathcal{C}$
satisfy C.CNe and $f$ satisfy f.DpL.C with constant $L$. Consider an adaptive-regularization run
with ratio (4.1.15), any termination test and any step conditions, such that
$x_0 \in \mathcal{C}$ and every step that satisfies the step conditions keeps $x_k + s_k$ in
$\mathcal{C}$ and decreases the model, $m_k(s_k) < m_k(0)$. If the test fails at all iterations
$j < k$, then $x_k \in \mathcal{C}$ and
$$\sigma_{\min} \le \sigma_k \le \sigma_{\max} = \max\left(\sigma_0, \frac{\gamma_3 L}{1 -
  \eta_2}\right).$$

This covers ARp-CC and ARp1-CC. -/
theorem arpcc_sigma_le
    (h : IsARRun P.toARParams test step (fun _ => False) (taylorRatio f p x s) x s σ)
    (hC : AssumptionCNe C) (hf : AssumptionDpLC f C p L) (hx0 : x 0 ∈ C)
    (hstep : ∀ k, step k → x k + s k ∈ C ∧
      regularizedModel (ftaylorSeries ℝ f (x k)) p (σ k) (s k) <
        regularizedModel (ftaylorSeries ℝ f (x k)) p (σ k) 0)
    (k : ℕ) (hk : ∀ j < k, ¬ test j) :
    x k ∈ C ∧ P.σmin ≤ σ k ∧ σ k ≤ P.sigmaMax L :=
  h.sigma_le hC.convex hf.contDiffAt hf.lipschitz hx0 (fun k _ hs => hstep k hs) k
    (IsARRun.forall_lt_not_stop_iff.2 hk)

/-- **Section 6.2.2** of [cartis2022evaluation], "Lemma 4.1.1 continues to hold", with the decrease
(4.1.37). Consider an adaptive-regularization run with ratio (4.1.15) in which every step that
satisfies the step conditions decreases the model. If the test fails at all iterations
$j \le k$, then
$$T_{f,p}(x_k, 0) - T_{f,p}(x_k, s_k) > \frac{\sigma_k}{(p+1)!} \|s_k\|^{p+1},$$
and if iteration $k$ is successful, then $x_{k+1} = x_k + s_k$ and
$$f(x_k) - f(x_{k+1}) \ge \frac{\eta_1 \sigma_{\min}}{(p+1)!} \|s_k\|^{p+1}.$$
-/
theorem arpcc_sub_ge
    (h : IsARRun P.toARParams test step (fun _ => False) (taylorRatio f p x s) x s σ)
    (hstep : ∀ k, step k →
      regularizedModel (ftaylorSeries ℝ f (x k)) p (σ k) (s k) <
        regularizedModel (ftaylorSeries ℝ f (x k)) p (σ k) 0)
    {k : ℕ} (hk : ∀ j ≤ k, ¬ test j) :
    σ k / ((p + 1)! : ℝ) * ‖s k‖ ^ (p + 1) <
        (ftaylorSeries ℝ f (x k)).taylorDecrement p (s k) ∧
      (P.η₁ ≤ taylorRatio f p x s k → x (k + 1) = x k + s k ∧
        P.η₁ * P.σmin / ((p + 1)! : ℝ) * ‖s k‖ ^ (p + 1) ≤ f (x k) - f (x (k + 1))) := by
  have hk' := IsARRun.forall_le_not_stop_iff.2 hk
  have hm := hstep k (h.step_of_forall_le hk')
  refine ⟨lt_taylorDecrement_of_regularizedModel_lt hm, fun hs => ?_⟩
  obtain ⟨heq, hge⟩ := h.sub_ge_of_succ_taylor hk' hm hs
  refine ⟨heq, le_trans ?_ hge⟩
  have hσ := h.sigmaMin_le (K := k) (fun j hj => hk' j hj.le) k le_rfl
  have := P.η₁_pos
  rw [mul_div_assoc, mul_assoc]
  gcongr

end Generic

/-! ### One-iteration estimates -/

section Estimates

variable {f : ℝⁿ → ℝ} {C : Set ℝⁿ} {p : ℕ} {L : ℝ}

/-- The core of (6.2.13), (6.2.15) and (6.2.17): if, for $j \le p$, the model measure of order $j$
over a set $T \ni 0$ is at most $\theta \epsilon$ while the objective measure exceeds
$\epsilon$, then $\|s\|^{p-j+1} > (p-j+1)! (1 - \theta) \epsilon / (L + \sigma_{\max})$. -/
private theorem pow_gt_of_lt_formCriticality (hf : AssumptionDpLC f C p L) (hC : Convex ℝ C)
    {x s : ℝⁿ} {σ σmax θ ε : ℝ} (hx : x ∈ C) (hxs : x + s ∈ C) (hσ : 0 ≤ σ)
    (hσmax : σ ≤ σmax) (hpos : 0 < L + σmax) {j : ℕ} (hj : j ≤ p) {T : Set ℝⁿ} (hT : 0 ∈ T)
    (hm : formCriticality (iteratedFDeriv ℝ j (regularizedModel (ftaylorSeries ℝ f x) p σ) s) T ≤
      θ * ε)
    (hlt : ε < formCriticality (iteratedFDeriv ℝ j f (x + s)) T) :
    ((p - j + 1)! : ℝ) * (1 - θ) / (L + σmax) * ε < ‖s‖ ^ (p - j + 1) := by
  have h1 := formCriticality_le_regularizedModel hC hf.contDiffAt hf.lipschitz hf.nonneg hx hxs
    hσ hj hT
  set N := ((p - j + 1)! : ℝ)
  set t := ‖s‖ ^ (p - j + 1)
  have hN : 0 < N := by positivity
  have ht : 0 ≤ t := by positivity
  have h2 : (L + σ) / N * t ≤ (L + σmax) / N * t := by gcongr
  have key : (1 - θ) * ε < (L + σmax) / N * t := by linarith
  rw [div_mul_eq_mul_div, lt_div_iff₀ hN] at key
  rw [div_mul_eq_mul_div, div_lt_iff₀ hpos]
  linarith

/-- The bound (6.2.23) on the unit ball: for $j \le p$ and $\|d\| \le 1$, $|\nabla^j m(s)[d]^j| \le
(L + \sigma_{\max}) \|s\|^{p-j+1} / (p-j+1)! + |\nabla^j f(x+s)[d]^j|$. -/
private theorem abs_model_le (hf : AssumptionDpLC f C p L) (hC : Convex ℝ C) {x s : ℝⁿ}
    {σ σmax : ℝ} (hx : x ∈ C) (hxs : x + s ∈ C) (hσ : 0 ≤ σ) (hσmax : σ ≤ σmax) {j : ℕ}
    (hj : j ≤ p) {d : ℝⁿ} (hd : ‖d‖ ≤ 1) :
    |iteratedFDeriv ℝ j (regularizedModel (ftaylorSeries ℝ f x) p σ) s (fun _ => d)| ≤
      (L + σmax) / ((p - j + 1)! : ℝ) * ‖s‖ ^ (p - j + 1) +
        |iteratedFDeriv ℝ j f (x + s) (fun _ => d)| := by
  have h1 := abs_iteratedFDeriv_sub_regularizedModel_le_of_mem_closedBall hC hf.contDiffAt
    hf.lipschitz hf.nonneg hx hxs hσ hj (d := d) (by simpa using hd)
  have h2 : (L + σ) / ((p - j + 1)! : ℝ) * ‖s‖ ^ (p - j + 1) ≤
      (L + σmax) / ((p - j + 1)! : ℝ) * ‖s‖ ^ (p - j + 1) := by gcongr
  have h3 := abs_sub_abs_le_abs_sub
    (iteratedFDeriv ℝ j (regularizedModel (ftaylorSeries ℝ f x) p σ) s (fun _ => d))
    (iteratedFDeriv ℝ j f (x + s) (fun _ => d))
  rw [abs_sub_comm] at h3
  linarith

/-- For $t \ge 0$ and $m \ne 0$, $(t^m)^{(p+1)/m} = t^{p+1}$. -/
private theorem pow_rpow_div {t : ℝ} (ht : 0 ≤ t) {m : ℕ} (hm : m ≠ 0) (p : ℕ) :
    (t ^ m) ^ (((p : ℝ) + 1) / m) = t ^ (p + 1) := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  rw [← Real.rpow_natCast t m, ← Real.rpow_mul ht, mul_div_cancel₀ _ hm', ← Real.rpow_natCast]
  push_cast; ring_nf

end Estimates

/-! ### Lemmas 6.2.1 and 6.2.2 -/

/-- **Lemma 6.2.2** of [cartis2022evaluation], the constants. Let $P$ be ARp-CC constants,
$L \in \mathbb{R}$, $p, j \in \mathbb{N}$ and $\theta \in \mathbb{R}$. The constant is
$$\kappa^{cc}_j = \frac{\eta_1 \sigma_{\min}}{(p+1)!} \left(\frac{(p-j+1)! (1 - \theta)}{L +
  \sigma_{\max}}\right)^{(p+1)/(p-j+1)},$$
used with $\theta = \theta_j$.

**Typo.** The source prints the prefactor $\eta_1 \sigma_{\min} / p!$. The decrease on a
successful iteration is $\eta_1 \sigma_{\min} \|s\|^{p+1} / (p+1)!$ (Lemma 4.1.1), so the
prefactor is $\eta_1 \sigma_{\min} / (p+1)!$; the constant $\kappa^S$ of Theorem 6.2.3 already
uses $(p+1)!$. -/
noncomputable def kappaCC (P : ARpCCParams) (L : ℝ) (p j : ℕ) (θ : ℝ) : ℝ :=
  P.η₁ * P.σmin / ((p + 1)! : ℝ) *
    (((p - j + 1)! : ℝ) * (1 - θ) / (L + P.sigmaMax L)) ^ (((p : ℝ) + 1) / ((p : ℝ) - j + 1))

namespace algorithm_6_2_1

variable {f : ℝⁿ → ℝ} {C : Set ℝⁿ} {p q : ℕ} {L : ℝ} {P : ARpCCParams} {ε₁ ε₂ ε₃ : ℝ}
  {x s : ℕ → ℝⁿ} {σ : ℕ → ℝ}

/-- Along a run of ARp-CC, if the test fails at all iterations $j \le k$, then the step $s_k$
satisfies the Step 2 conditions. -/
theorem step (h : algorithm_6_2_1 f C p P q ε₁ ε₂ ε₃ x s σ) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ IsApproxMinimizerCC f C P.τ₁ P.τ₂ q ε₁ ε₂ ε₃ (x j)) :
    IsARpCCStep f C p P q ε₁ ε₂ ε₃ (x k) (σ k) (s k) :=
  h.run.step_of_forall_le (IsARRun.forall_le_not_stop_iff.2 hk)

/-- Lemma 4.1.2 for ARp-CC runs (`CartisGouldToint.Chapter06.arpcc_sigma_le`): under C.CNe and
f.DpL.C, if the test fails at all iterations $j < k$, then $x_k \in \mathcal{C}$ and
$\sigma_{\min} \le \sigma_k \le \sigma_{\max}$. -/
theorem sigma_le (h : algorithm_6_2_1 f C p P q ε₁ ε₂ ε₃ x s σ) (hC : AssumptionCNe C)
    (hf : AssumptionDpLC f C p L) (k : ℕ)
    (hk : ∀ j < k, ¬ IsApproxMinimizerCC f C P.τ₁ P.τ₂ q ε₁ ε₂ ε₃ (x j)) :
    x k ∈ C ∧ P.σmin ≤ σ k ∧ σ k ≤ P.sigmaMax L :=
  arpcc_sigma_le h.run hC hf h.mem_zero (fun _ hs => ⟨hs.mem, hs.decrease⟩) k hk

/-- On a successful iteration before termination, $x_k$ and $x_{k+1} = x_k + s_k$ lie in
$\mathcal{C}$, $0 \le \sigma_k \le \sigma_{\max}$, and $f(x_k) - f(x_{k+1}) \ge \eta_1
\sigma_{\min} \|s_k\|^{p+1} / (p+1)!$. -/
private theorem succ_facts (h : algorithm_6_2_1 f C p P q ε₁ ε₂ ε₃ x s σ) (hC : AssumptionCNe C)
    (hf : AssumptionDpLC f C p L) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ IsApproxMinimizerCC f C P.τ₁ P.τ₂ q ε₁ ε₂ ε₃ (x j))
    (hs : P.η₁ ≤ taylorRatio f p x s k) :
    x k ∈ C ∧ x (k + 1) = x k + s k ∧ x k + s k ∈ C ∧ 0 ≤ σ k ∧ σ k ≤ P.sigmaMax L ∧
      P.η₁ * P.σmin / ((p + 1)! : ℝ) * ‖s k‖ ^ (p + 1) ≤ f (x k) - f (x (k + 1)) := by
  obtain ⟨hx, hmin, hmax⟩ := h.sigma_le hC hf k fun j hj => hk j hj.le
  obtain ⟨-, hsucc⟩ := arpcc_sub_ge h.run (fun _ hs => hs.decrease) hk
  obtain ⟨heq, hdec⟩ := hsucc hs
  exact ⟨hx, heq, (h.step hk).mem, P.σmin_nonneg.trans hmin, hmax, hdec⟩

/-- **Lemma 6.2.1** of [cartis2022evaluation], bound (6.2.13). Let $\mathcal{C}$ satisfy C.CNe, let
$f$ satisfy f.DpL.C with constant $L$, and let $p \ge 1$. Consider a run of ARp-CC, and let $k$
be a successful iteration such that the test fails at all iterations $j \le k$. If
$\omega_{f,\mathcal{C},1}(x_{k+1}) > \epsilon_1$, then
$$\|s_k\|^p > \frac{p! (1 - \theta_1)}{L + \sigma_{\max}} \epsilon_1.$$
-/
theorem _root_.CartisGouldToint.Chapter06.lemma_6_2_1_i
    (h : algorithm_6_2_1 f C p P q ε₁ ε₂ ε₃ x s σ) (hC : AssumptionCNe C)
    (hf : AssumptionDpLC f C p L) (hp : 1 ≤ p) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ IsApproxMinimizerCC f C P.τ₁ P.τ₂ q ε₁ ε₂ ε₃ (x j))
    (hs : P.η₁ ≤ taylorRatio f p x s k) (hω : ε₁ < omega1 f C (x (k + 1))) :
    (p ! : ℝ) * (1 - P.θ₁) / (L + P.sigmaMax L) * ε₁ < ‖s k‖ ^ p := by
  obtain ⟨hx, heq, hxs, hσ, hσmax, -⟩ := h.succ_facts hC hf hk hs
  have hpos : 0 < L + P.sigmaMax L := by linarith [hf.nonneg, P.sigmaMax_pos L]
  have := pow_gt_of_lt_formCriticality hf hC.convex hx hxs hσ hσmax hpos hp
    (zero_mem_modelSteps₀ hxs) (h.step hk).omega1_le (by rwa [heq] at hω)
  rwa [Nat.sub_add_cancel hp] at this

/-- **Lemma 6.2.1** of [cartis2022evaluation], bound (6.2.15). In the setting of
`CartisGouldToint.Chapter06.lemma_6_2_1_i`, let $2 \le q \le p$. If
$\omega_{k+1,2} > \epsilon_2$, then
$$\|s_k\|^{p-1} > \frac{(p-1)! (1 - \theta_2)}{L + \sigma_{\max}} \epsilon_2.$$
-/
theorem _root_.CartisGouldToint.Chapter06.lemma_6_2_1_ii
    (h : algorithm_6_2_1 f C p P q ε₁ ε₂ ε₃ x s σ) (hC : AssumptionCNe C)
    (hf : AssumptionDpLC f C p L) (hq : 2 ≤ q) (hqp : q ≤ p) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ IsApproxMinimizerCC f C P.τ₁ P.τ₂ q ε₁ ε₂ ε₃ (x j))
    (hs : P.η₁ ≤ taylorRatio f p x s k)
    (hω : ε₂ < omegaNext2 f C p P.θ₁ ε₁ (x k) (σ k) (s k)) :
    ((p - 1)! : ℝ) * (1 - P.θ₂) / (L + P.sigmaMax L) * ε₂ < ‖s k‖ ^ (p - 1) := by
  obtain ⟨hx, -, hxs, hσ, hσmax, -⟩ := h.succ_facts hC hf hk hs
  have hpos : 0 < L + P.sigmaMax L := by linarith [hf.nonneg, P.sigmaMax_pos L]
  have := pow_gt_of_lt_formCriticality hf hC.convex hx hxs hσ hσmax hpos (j := 2) (by omega)
    (zero_mem_modelSteps₁ hxs (mul_nonneg P.θ₁_pos.le h.ε₁_pos.le)) ((h.step hk).omega2_le hq) hω
  have e : p - 2 + 1 = p - 1 := by omega
  rwa [e] at this

/-- **Lemma 6.2.1** of [cartis2022evaluation], bound (6.2.17). In the setting of
`CartisGouldToint.Chapter06.lemma_6_2_1_i`, let $3 \le q \le p$. If
$\omega_{k+1,3} > \epsilon_3$, then
$$\|s_k\|^{p-2} > \frac{(p-2)! (1 - \theta_3)}{L + \sigma_{\max}} \epsilon_3.$$
-/
theorem _root_.CartisGouldToint.Chapter06.lemma_6_2_1_iii
    (h : algorithm_6_2_1 f C p P q ε₁ ε₂ ε₃ x s σ) (hC : AssumptionCNe C)
    (hf : AssumptionDpLC f C p L) (hq : 3 ≤ q) (hqp : q ≤ p) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ IsApproxMinimizerCC f C P.τ₁ P.τ₂ q ε₁ ε₂ ε₃ (x j))
    (hs : P.η₁ ≤ taylorRatio f p x s k)
    (hω : ε₃ < omegaNext3 f C p P.θ₁ P.θ₂ ε₁ ε₂ (x k) (σ k) (s k)) :
    ((p - 2)! : ℝ) * (1 - P.θ₃) / (L + P.sigmaMax L) * ε₃ < ‖s k‖ ^ (p - 2) := by
  obtain ⟨hx, -, hxs, hσ, hσmax, -⟩ := h.succ_facts hC hf hk hs
  have hpos : 0 < L + P.sigmaMax L := by linarith [hf.nonneg, P.sigmaMax_pos L]
  have := pow_gt_of_lt_formCriticality hf hC.convex hx hxs hσ hσmax hpos (j := 3) (by omega)
    (zero_mem_modelSteps₂ hxs (mul_nonneg P.θ₁_pos.le h.ε₁_pos.le)
      (mul_nonneg P.θ₂_pos.le h.ε₂_pos.le)) ((h.step hk).omega3_le hq) hω
  have e : p - 3 + 1 = p - 2 := by omega
  rwa [e] at this

/-- **Lemma 6.2.1** of [cartis2022evaluation], bounds (6.2.18)–(6.2.19). Let $\mathcal{C}$ satisfy
C.CNe and $f$ satisfy f.DpL.C with constant $L$. Consider a run of ARp-CC, and let $k$ be a
successful iteration such that the test fails at all iterations $j \le k$. If $p \ge 1$, then
for every $d \in \mathcal{C}^1(x_{k+1}, \epsilon_1)$ with $\|d\| \le 1$,
$$|\nabla_s m_k(s_k)[d]| \le \frac{L + \sigma_{\max}}{p!} \|s_k\|^p + \tau_1 \epsilon_1.$$
If $p \ge 2$, then for every $d \in \mathcal{C}^2(x_{k+1}, \epsilon_1, \epsilon_2)$ with
$\|d\| \le 1$,
$$|\nabla^2_s m_k(s_k)[d]^2| \le \frac{L + \sigma_{\max}}{(p-1)!} \|s_k\|^{p-1} + \tau_2
  \epsilon_2.$$

**Correction.** The source states both bounds for all $d$ in the restricted sets. Its proof,
through (6.2.23), covers only $\|d\| \le 1$, because the error term scales like $\|d\|^j$.
For $f(t)=t^3$ on $[0,\infty)$, the degree-three trial $x=1$, $s=-1$ and
$\sigma=1/10$ has $\rho=1$ and satisfies the first- and second-order model tests with
$\epsilon_1=1/10$. At $x+s=0$ both objective derivatives vanish, so the restricted
sets contain all $d\ge0$. The model has derivatives $-\sigma/6$ and $\sigma/2$ at
$s=-1$. Its directional forms are unbounded over these sets without the unit-ball bound.
Accordingly, the inclusions $\mathcal{C}^1(x_{k+1}, \epsilon_1) \subseteq \mathcal{M}^1_k(s_k)$
and $\mathcal{C}^2(x_{k+1}, \epsilon_1, \epsilon_2) \subseteq \mathcal{M}^2_k(s_k)$ in the proof
of Theorem 6.2.3 are used on $\mathcal{B}$, which is all that the measures see. -/
theorem _root_.CartisGouldToint.Chapter06.lemma_6_2_1_iv
    (h : algorithm_6_2_1 f C p P q ε₁ ε₂ ε₃ x s σ) (hC : AssumptionCNe C)
    (hf : AssumptionDpLC f C p L) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ IsApproxMinimizerCC f C P.τ₁ P.τ₂ q ε₁ ε₂ ε₃ (x j))
    (hs : P.η₁ ≤ taylorRatio f p x s k) :
    (1 ≤ p → ∀ d ∈ restrictedSteps₁ f C P.τ₁ ε₁ (x (k + 1)), ‖d‖ ≤ 1 →
      |iteratedFDeriv ℝ 1 (regularizedModel (ftaylorSeries ℝ f (x k)) p (σ k)) (s k)
          (fun _ => d)| ≤ (L + P.sigmaMax L) / (p ! : ℝ) * ‖s k‖ ^ p + P.τ₁ * ε₁) ∧
    (2 ≤ p → ∀ d ∈ restrictedSteps₂ f C P.τ₁ P.τ₂ ε₁ ε₂ (x (k + 1)), ‖d‖ ≤ 1 →
      |iteratedFDeriv ℝ 2 (regularizedModel (ftaylorSeries ℝ f (x k)) p (σ k)) (s k)
          (fun _ => d)| ≤
        (L + P.sigmaMax L) / ((p - 1)! : ℝ) * ‖s k‖ ^ (p - 1) + P.τ₂ * ε₂) := by
  obtain ⟨hx, heq, hxs, hσ, hσmax, -⟩ := h.succ_facts hC hf hk hs
  refine ⟨fun hp d hd hd1 => ?_, fun hp d hd hd1 => ?_⟩
  · have h1 := abs_model_le hf hC.convex hx hxs hσ hσmax hp hd1
    rw [Nat.sub_add_cancel hp] at h1
    rw [heq] at hd
    have := hd.2
    linarith
  · have h1 := abs_model_le hf hC.convex hx hxs hσ hσmax (j := 2) hp hd1
    have e : p - 2 + 1 = p - 1 := by omega
    rw [e] at h1
    rw [heq] at hd
    have := hd.2
    linarith

/-- On a successful iteration before termination, if $\|s_k\|^m > b \epsilon$ with $m \ne 0$ and
$b, \epsilon \ge 0$, then $f(x_k) - f(x_{k+1}) > \eta_1 \sigma_{\min} b^{(p+1)/m}
\epsilon^{(p+1)/m} / (p+1)!$, as in the proof of Lemma 4.1.4.

**Correction.** Isolates the shared successful objective estimate with the corrected factorial.
-/
private theorem decrease_gt (h : algorithm_6_2_1 f C p P q ε₁ ε₂ ε₃ x s σ)
    (hC : AssumptionCNe C) (hf : AssumptionDpLC f C p L) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ IsApproxMinimizerCC f C P.τ₁ P.τ₂ q ε₁ ε₂ ε₃ (x j))
    (hs : P.η₁ ≤ taylorRatio f p x s k) {m : ℕ} (hm : m ≠ 0) {b ε : ℝ} (hb : 0 ≤ b)
    (hε : 0 ≤ ε) (hlt : b * ε < ‖s k‖ ^ m) :
    P.η₁ * P.σmin / ((p + 1)! : ℝ) * (b ^ (((p : ℝ) + 1) / m) * ε ^ (((p : ℝ) + 1) / m)) <
      f (x k) - f (x (k + 1)) := by
  obtain ⟨-, -, -, -, -, hdec⟩ := h.succ_facts hC hf hk hs
  have hc : 0 < P.η₁ * P.σmin / ((p + 1)! : ℝ) := by
    have := P.η₁_pos; have := P.σmin_pos; positivity
  have he : 0 < ((p : ℝ) + 1) / m := by
    have : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
    positivity
  have h1 : (b * ε) ^ (((p : ℝ) + 1) / m) < ‖s k‖ ^ (p + 1) := by
    rw [← pow_rpow_div (norm_nonneg _) hm]
    exact Real.rpow_lt_rpow (mul_nonneg hb hε) hlt he
  rw [← Real.mul_rpow hb hε]
  calc _ < P.η₁ * P.σmin / ((p + 1)! : ℝ) * ‖s k‖ ^ (p + 1) := mul_lt_mul_of_pos_left h1 hc
    _ ≤ _ := hdec

/-- Lemma 6.2.2 for one order $j \le p$: on a successful iteration before termination, if
$\theta < 1$, $\epsilon \ge 0$ and $\|s_k\|^{p-j+1} > (p-j+1)! (1 - \theta) \epsilon / (L +
\sigma_{\max})$, then $f(x_k) - f(x_{k+1}) > \kappa^{cc}_j \epsilon^{(p+1)/(p-j+1)}$.

**Correction.** Packages the bound with the corrected indexed coefficient.
-/
private theorem decrease_gt_kappaCC (h : algorithm_6_2_1 f C p P q ε₁ ε₂ ε₃ x s σ)
    (hC : AssumptionCNe C) (hf : AssumptionDpLC f C p L) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ IsApproxMinimizerCC f C P.τ₁ P.τ₂ q ε₁ ε₂ ε₃ (x j))
    (hs : P.η₁ ≤ taylorRatio f p x s k) {j : ℕ} (hj : j ≤ p) {θ ε : ℝ} (hθ : θ < 1)
    (hε : 0 ≤ ε)
    (hlt : ((p - j + 1)! : ℝ) * (1 - θ) / (L + P.sigmaMax L) * ε < ‖s k‖ ^ (p - j + 1)) :
    kappaCC P L p j θ * ε ^ (((p : ℝ) + 1) / ((p : ℝ) - j + 1)) < f (x k) - f (x (k + 1)) := by
  have hpos : 0 < L + P.sigmaMax L := by linarith [hf.nonneg, P.sigmaMax_pos L]
  have hb : 0 ≤ ((p - j + 1)! : ℝ) * (1 - θ) / (L + P.sigmaMax L) := by
    have : 0 ≤ 1 - θ := by linarith
    positivity
  have := h.decrease_gt hC hf hk hs (by omega) hb hε hlt
  have hcast : (((p - j + 1 : ℕ)) : ℝ) = (p : ℝ) - j + 1 := by
    rw [Nat.cast_add, Nat.cast_sub hj, Nat.cast_one]
  rw [hcast] at this
  rw [kappaCC, mul_assoc]
  exact this

/-- **Lemma 6.2.2** of [cartis2022evaluation]. Let $\mathcal{C}$ satisfy C.CNe and $f$ satisfy
f.DpL.C with constant $L$. Consider a run of ARp-CC of order $q \le p$, and let $k$ be a
successful iteration such that the test fails at all iterations $j \le k$. With the constants
$\kappa^{cc}_j$ for $\theta = \theta_j$:
* if $\omega_{f,\mathcal{C},1}(x_{k+1}) > \epsilon_1$, then $f(x_k) - f(x_{k+1}) > \kappa^{cc}_1
  \epsilon_1^{(p+1)/p}$;
* if $q \ge 2$ and $\omega_{k+1,2} > \epsilon_2$, then $f(x_k) - f(x_{k+1}) > \kappa^{cc}_2
  \epsilon_2^{(p+1)/(p-1)}$;
* if $q \ge 3$ and $\omega_{k+1,3} > \epsilon_3$, then $f(x_k) - f(x_{k+1}) > \kappa^{cc}_3
  \epsilon_3^{(p+1)/(p-2)}$.

**Typo.** The source prints the prefactor $\eta_1 \sigma_{\min} / p!$ in $\kappa^{cc}_j$, which
overstates the decrease by the factor $p + 1$; the prefactor here is
$\eta_1 \sigma_{\min} / (p+1)!$.

The constants are `CartisGouldToint.Chapter06.kappaCC`. Since a run has $q \ge 1$, the
hypothesis $q \le p$ gives $p \ge 1$. -/
theorem _root_.CartisGouldToint.Chapter06.lemma_6_2_2
    (h : algorithm_6_2_1 f C p P q ε₁ ε₂ ε₃ x s σ) (hC : AssumptionCNe C)
    (hf : AssumptionDpLC f C p L) (hqp : q ≤ p) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ IsApproxMinimizerCC f C P.τ₁ P.τ₂ q ε₁ ε₂ ε₃ (x j))
    (hs : P.η₁ ≤ taylorRatio f p x s k) :
    (ε₁ < omega1 f C (x (k + 1)) →
      kappaCC P L p 1 P.θ₁ * ε₁ ^ (((p : ℝ) + 1) / p) < f (x k) - f (x (k + 1))) ∧
    (2 ≤ q → ε₂ < omegaNext2 f C p P.θ₁ ε₁ (x k) (σ k) (s k) →
      kappaCC P L p 2 P.θ₂ * ε₂ ^ (((p : ℝ) + 1) / ((p : ℝ) - 1)) <
        f (x k) - f (x (k + 1))) ∧
    (3 ≤ q → ε₃ < omegaNext3 f C p P.θ₁ P.θ₂ ε₁ ε₂ (x k) (σ k) (s k) →
      kappaCC P L p 3 P.θ₃ * ε₃ ^ (((p : ℝ) + 1) / ((p : ℝ) - 2)) <
        f (x k) - f (x (k + 1))) := by
  have hp : 1 ≤ p := h.one_le_q.trans hqp
  refine ⟨fun hω => ?_, fun hq hω => ?_, fun hq hω => ?_⟩
  · have h1 := lemma_6_2_1_i h hC hf hp hk hs hω
    have := h.decrease_gt_kappaCC hC hf hk hs hp P.θ₁_lt_one h.ε₁_pos.le
      (by rwa [Nat.sub_add_cancel hp])
    simpa using this
  · have h1 := lemma_6_2_1_ii h hC hf hq hqp hk hs hω
    have e : p - 2 + 1 = p - 1 := by omega
    have := h.decrease_gt_kappaCC hC hf hk hs (j := 2) (by omega) P.θ₂_lt_one h.ε₂_pos.le
      (by rwa [e])
    convert this using 3
    push_cast; ring
  · have h1 := lemma_6_2_1_iii h hC hf hq hqp hk hs hω
    have e : p - 3 + 1 = p - 2 := by omega
    have := h.decrease_gt_kappaCC hC hf hk hs (j := 3) (by omega) P.θ₃_lt_one h.ε₃_pos.le
      (by rwa [e])
    convert this using 3
    push_cast; ring

end algorithm_6_2_1

/-! ### Theorem 6.2.3 -/

/-- The $j$-th term of the maximum in the constant $\kappa^S_{\mathrm{ARpCC}}$ of Theorem 6.2.3 of
[cartis2022evaluation]: $((L + \sigma_{\max}) / ((p-j+1)! (1 - \theta)))^{(p+1)/(p-j+1)}$, used
with $\theta = \theta_j$. -/
noncomputable def ccFactor (P : ARpCCParams) (L : ℝ) (p j : ℕ) (θ : ℝ) : ℝ :=
  ((L + P.sigmaMax L) / (((p - j + 1)! : ℝ) * (1 - θ))) ^ (((p : ℝ) + 1) / ((p : ℝ) - j + 1))

/-- The maximum of the terms `CartisGouldToint.Chapter06.ccFactor` over the orders $j = 1, \dots, q$
with $\theta = \theta_j$; for $q \le 1$ it is the first term, and for $q \ge 3$ it is the
maximum of the three terms.

**Reading.** Selects the maximum over active orders; the printed display takes all three.
-/
noncomputable def ccMax (P : ARpCCParams) (L : ℝ) (p q : ℕ) : ℝ :=
  if q ≤ 1 then ccFactor P L p 1 P.θ₁
  else if q = 2 then max (ccFactor P L p 1 P.θ₁) (ccFactor P L p 2 P.θ₂)
  else max (max (ccFactor P L p 1 P.θ₁) (ccFactor P L p 2 P.θ₂)) (ccFactor P L p 3 P.θ₃)

/-- **Theorem 6.2.3** of [cartis2022evaluation], the constant $\kappa^S$. Let $P$ be ARp-CC
constants, $L \in \mathbb{R}$ and $p, q \in \mathbb{N}$. The constant is
$$\kappa^S_{\mathrm{ARpCC}} = \frac{(p+1)!}{\eta_1 \sigma_{\min}} \max_{j \in [1 : q]}
  \left(\frac{L + \sigma_{\max}}{(p-j+1)! (1 - \theta_j)}\right)^{(p+1)/(p-j+1)},$$
which is $1 / \min_j \kappa^{cc}_j$.

**Generalization.** Same factorial prefactor and maximum, generalized to active orders one through
three.
-/
noncomputable def kappaSARpCC (P : ARpCCParams) (L : ℝ) (p q : ℕ) : ℝ :=
  ((p + 1)! : ℝ) / (P.η₁ * P.σmin) * ccMax P L p q

/-- **Theorem 6.2.3** of [cartis2022evaluation], the constant $\kappa^A$. The constant is
$\kappa^A_{\mathrm{ARpCC}} = \kappa^S_{\mathrm{ARpCC}} (1 + |\log \gamma_1| / \log \gamma_2)$.

**Generalization.** Same logarithmic inflation of the successful-iteration constant generalized in
q.
-/
noncomputable def kappaAARpCC (P : ARpCCParams) (L : ℝ) (p q : ℕ) : ℝ :=
  kappaSARpCC P L p q * (1 + |Real.log P.γ₁| / Real.log P.γ₂)

/-- **Theorem 6.2.3** of [cartis2022evaluation], the constant $\kappa^C$. The constant is
$$\kappa^C_{\mathrm{ARpCC}} = \frac{|\log \gamma_1| + \log(\sigma_{\max} / \sigma_0)}{\log
  \gamma_2} + 2.$$
It is also the constant $\kappa^C_{\mathrm{ARp}}$ of (4.1.46) in Theorem 6.2.5. -/
noncomputable def kappaCARpCC (P : ARpCCParams) (L : ℝ) : ℝ :=
  (|Real.log P.γ₁| + Real.log (P.sigmaMax L / P.σ₀)) / Real.log P.γ₂ + 2

/-- **Theorem 6.2.3** of [cartis2022evaluation], the accuracy term. Let $p, q \in \mathbb{N}$ and
$\epsilon_1, \epsilon_2, \epsilon_3 \in \mathbb{R}$. The accuracy term is $\min_{j \in [1 : q]}
\epsilon_j^{(p+1)/(p-j+1)}$: it is $\epsilon_1^{(p+1)/p}$ for $q \le 1$,
$\min[\epsilon_1^{(p+1)/p}, \epsilon_2^{(p+1)/(p-1)}]$ for $q = 2$, and
$\min[\epsilon_1^{(p+1)/p}, \epsilon_2^{(p+1)/(p-1)}, \epsilon_3^{(p+1)/(p-2)}]$ for $q \ge 3$.

The exponents are real quotients; a zero denominator gives the exponent $0$.

**Reading.** Matches the minimum of all three powers for order three and omits inactive terms for
lower orders.
-/
noncomputable def tolMin (p q : ℕ) (ε₁ ε₂ ε₃ : ℝ) : ℝ :=
  if q ≤ 1 then ε₁ ^ (((p : ℝ) + 1) / p)
  else if q = 2 then min (ε₁ ^ (((p : ℝ) + 1) / p)) (ε₂ ^ (((p : ℝ) + 1) / ((p : ℝ) - 1)))
  else min (min (ε₁ ^ (((p : ℝ) + 1) / p)) (ε₂ ^ (((p : ℝ) + 1) / ((p : ℝ) - 1))))
    (ε₃ ^ (((p : ℝ) + 1) / ((p : ℝ) - 2)))

section Constants

variable {P : ARpCCParams} {L : ℝ} {p q : ℕ} {ε₁ ε₂ ε₃ : ℝ}

/-- If $L \ge 0$ and $\theta < 1$, then the term `CartisGouldToint.Chapter06.ccFactor` is positive.
-/
theorem ccFactor_pos (hL : 0 ≤ L) {j : ℕ} {θ : ℝ} (hθ : θ < 1) : 0 < ccFactor P L p j θ := by
  have := P.sigmaMax_pos L
  have : 0 < 1 - θ := by linarith
  unfold ccFactor
  positivity

/-- If $L \ge 0$, then the maximum `CartisGouldToint.Chapter06.ccMax` is positive.

**Reading.** The defined maximum is positive at each active order.
-/
theorem ccMax_pos (hL : 0 ≤ L) : 0 < ccMax P L p q := by
  have h1 := ccFactor_pos (P := P) (p := p) (j := 1) hL P.θ₁_lt_one
  unfold ccMax
  split_ifs
  · exact h1
  · exact lt_max_of_lt_left h1
  · exact lt_max_of_lt_left (lt_max_of_lt_left h1)

/-- If $L \ge 0$, then $\kappa^S_{\mathrm{ARpCC}} > 0$.

**Generalization.** Positivity of the generalized successful-iteration bound coefficient.
-/
theorem kappaSARpCC_pos (hL : 0 ≤ L) : 0 < kappaSARpCC P L p q := by
  have := P.η₁_pos; have := P.σmin_pos; have := ccMax_pos (P := P) (p := p) (q := q) hL
  unfold kappaSARpCC
  positivity

/-- If $\epsilon_1, \epsilon_2, \epsilon_3 > 0$, then the accuracy term
$\min_j \epsilon_j^{(p+1)/(p-j+1)}$ is positive.

**Generalization.** Positivity of the active tolerance denominator extends to all positive
tolerances.
-/
theorem tolMin_pos (h₁ : 0 < ε₁) (h₂ : 0 < ε₂) (h₃ : 0 < ε₃) : 0 < tolMin p q ε₁ ε₂ ε₃ := by
  unfold tolMin
  split_ifs <;> positivity

/-- If $L \ge 0$ and $\theta < 1$, then $\kappa^{cc}_j$ is $\eta_1 \sigma_{\min} / (p+1)!$ divided
by the $j$-th term `CartisGouldToint.Chapter06.ccFactor` of $\kappa^S_{\mathrm{ARpCC}}$.

**Correction.** Rewrites each corrected decrease coefficient through the reciprocal factor in the
proof.
-/
theorem kappaCC_eq (hL : 0 ≤ L) {j : ℕ} {θ : ℝ} (hθ : θ < 1) :
    kappaCC P L p j θ = P.η₁ * P.σmin / ((p + 1)! : ℝ) / ccFactor P L p j θ := by
  have := P.sigmaMax_pos L
  have : 0 < 1 - θ := by linarith
  rw [kappaCC, ccFactor, div_eq_mul_inv _ (_ ^ _), ← Real.inv_rpow (by positivity), inv_div]

/-- The bookkeeping of the proof of Theorem 6.2.3: if the $j$-th term is at most the maximum and the
accuracy term is at most $\epsilon^e$, then the accuracy term divided by
$\kappa^S_{\mathrm{ARpCC}}$ is at most $\kappa^{cc}_j \epsilon^e$.

**Correction.** The common decrease floor is at most any corrected active one-order decrease bound.
-/
private theorem div_kappaS_le (hL : 0 ≤ L) {j : ℕ} {θ ε e : ℝ} (hθ : θ < 1) (hε : 0 ≤ ε)
    (hF : ccFactor P L p j θ ≤ ccMax P L p q) (ht : tolMin p q ε₁ ε₂ ε₃ ≤ ε ^ e) :
    tolMin p q ε₁ ε₂ ε₃ / kappaSARpCC P L p q ≤ kappaCC P L p j θ * ε ^ e := by
  have hFpos := ccFactor_pos (P := P) (p := p) (j := j) hL hθ
  have hc : 0 ≤ P.η₁ * P.σmin / ((p + 1)! : ℝ) := by
    have := P.η₁_pos; have := P.σmin_pos; positivity
  have hM := hFpos.trans_le hF
  have he : 0 ≤ ε ^ e := Real.rpow_nonneg hε e
  rw [kappaCC_eq hL hθ, kappaSARpCC]
  have h1 : tolMin p q ε₁ ε₂ ε₃ / (((p + 1)! : ℝ) / (P.η₁ * P.σmin) * ccMax P L p q) =
      tolMin p q ε₁ ε₂ ε₃ * (P.η₁ * P.σmin / ((p + 1)! : ℝ) / ccMax P L p q) := by
    have := P.η₁_pos; have := P.σmin_pos
    field_simp
  rw [h1, mul_comm _ (ε ^ e)]
  calc tolMin p q ε₁ ε₂ ε₃ * (P.η₁ * P.σmin / ((p + 1)! : ℝ) / ccMax P L p q)
      ≤ ε ^ e * (P.η₁ * P.σmin / ((p + 1)! : ℝ) / ccMax P L p q) :=
        mul_le_mul_of_nonneg_right ht (by positivity)
    _ ≤ ε ^ e * (P.η₁ * P.σmin / ((p + 1)! : ℝ) / ccFactor P L p j θ) := by gcongr

private theorem ccFactor_one_le : ccFactor P L p 1 P.θ₁ ≤ ccMax P L p q := by
  unfold ccMax; split_ifs
  · exact le_rfl
  · exact le_max_left _ _
  · exact (le_max_left _ _).trans (le_max_left _ _)

private theorem ccFactor_two_le (hq : 2 ≤ q) : ccFactor P L p 2 P.θ₂ ≤ ccMax P L p q := by
  unfold ccMax; split_ifs
  · omega
  · exact le_max_right _ _
  · exact (le_max_right _ _).trans (le_max_left _ _)

private theorem ccFactor_three_le (hq : 3 ≤ q) : ccFactor P L p 3 P.θ₃ ≤ ccMax P L p q := by
  unfold ccMax; split_ifs
  · omega
  · omega
  · exact le_max_right _ _

private theorem tolMin_le_one : tolMin p q ε₁ ε₂ ε₃ ≤ ε₁ ^ (((p : ℝ) + 1) / p) := by
  unfold tolMin; split_ifs
  · exact le_rfl
  · exact min_le_left _ _
  · exact (min_le_left _ _).trans (min_le_left _ _)

private theorem tolMin_le_two (hq : 2 ≤ q) :
    tolMin p q ε₁ ε₂ ε₃ ≤ ε₂ ^ (((p : ℝ) + 1) / ((p : ℝ) - 1)) := by
  unfold tolMin; split_ifs
  · omega
  · exact min_le_right _ _
  · exact (min_le_left _ _).trans (min_le_right _ _)

private theorem tolMin_le_three (hq : 3 ≤ q) :
    tolMin p q ε₁ ε₂ ε₃ ≤ ε₃ ^ (((p : ℝ) + 1) / ((p : ℝ) - 2)) := by
  unfold tolMin; split_ifs
  · omega
  · omega
  · exact min_le_right _ _

end Constants

namespace algorithm_6_2_1

variable {f : ℝⁿ → ℝ} {C : Set ℝⁿ} {p q : ℕ} {L flow : ℝ} {P : ARpCCParams} {ε₁ ε₂ ε₃ : ℝ}
  {x s : ℕ → ℝⁿ} {σ : ℕ → ℝ}

/-- If $0 \le t \le N (1 - \theta) \epsilon / (L + \sigma_{\max})$ and $\sigma \le \sigma_{\max}$,
then $(L + \sigma) t / N \le (1 - \theta) \epsilon$. -/
private theorem err_le {σ σmax N t θ ε : ℝ} (hσ : σ ≤ σmax) (hpos : 0 < L + σmax) (hN : 0 < N)
    (ht0 : 0 ≤ t) (ht : t ≤ N * (1 - θ) / (L + σmax) * ε) :
    (L + σ) / N * t ≤ (1 - θ) * ε := by
  calc (L + σ) / N * t ≤ (L + σmax) / N * t := by gcongr
    _ ≤ (L + σmax) / N * (N * (1 - θ) / (L + σmax) * ε) := by gcongr
    _ = (1 - θ) * ε := by field_simp

/-- **Theorem 6.2.3** of [cartis2022evaluation], the decrease of its proof (the version of
(4.1.44)). Let $\mathcal{C}$ satisfy C.CNe and $f$ satisfy f.DpL.C with constant $L$. Consider a
run of ARp-CC of order $q \le p$, and let $k$ be a successful iteration such that the test fails
at all iterations $j \le k$ and also at $x_{k+1}$. Then
$$f(x_k) - f(x_{k+1}) \ge \frac{\min_j \epsilon_j^{(p+1)/(p-j+1)}}{\kappa^S_{\mathrm{ARpCC}}}.$$

If the step is long, that is, (6.2.27) fails or, for $q \ge 2$, (6.2.28) fails, the bound
follows from Lemma 4.1.1. Otherwise Lemma 6.2.1 and (6.2.7) give $\mathcal{C}^1(x_{k+1},
\epsilon_1) \cap \mathcal{B} \subseteq \mathcal{M}^1_k(s_k)$ and $\mathcal{C}^2(x_{k+1},
\epsilon_1, \epsilon_2) \cap \mathcal{B} \subseteq \mathcal{M}^2_k(s_k)$, so
$\omega_{f,\mathcal{C},2}(x_{k+1}, \epsilon_1) \le \omega_{k+1,2}$ and
$\omega_{f,\mathcal{C},3}(x_{k+1}, \epsilon_1, \epsilon_2) \le \omega_{k+1,3}$, and Lemma 6.2.2
applies to the measure that fails.

**Reading.** The next-iterate test yields the common decrease floor for the active order, using
unit-ball inclusions.
-/
theorem _root_.CartisGouldToint.Chapter06.arpcc_decrease_of_not_test
    (h : algorithm_6_2_1 f C p P q ε₁ ε₂ ε₃ x s σ)
    (hC : AssumptionCNe C) (hf : AssumptionDpLC f C p L) (hqp : q ≤ p) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ IsApproxMinimizerCC f C P.τ₁ P.τ₂ q ε₁ ε₂ ε₃ (x j))
    (hs : P.η₁ ≤ taylorRatio f p x s k)
    (hk1 : ¬ IsApproxMinimizerCC f C P.τ₁ P.τ₂ q ε₁ ε₂ ε₃ (x (k + 1))) :
    tolMin p q ε₁ ε₂ ε₃ / kappaSARpCC P L p q ≤ f (x k) - f (x (k + 1)) := by
  have hp : 1 ≤ p := h.one_le_q.trans hqp
  have hL := hf.nonneg
  obtain ⟨hx, heq, hxs, hσ, hσmax, -⟩ := h.succ_facts hC hf hk hs
  have hpos : 0 < L + P.sigmaMax L := by linarith [P.sigmaMax_pos L]
  have hε₁ := h.ε₁_pos
  have hε₂ := h.ε₂_pos
  have hε₃ := h.ε₃_pos
  have hl := lemma_6_2_2 h hC hf hqp hk hs
  -- the three ways to conclude
  have fin1 : kappaCC P L p 1 P.θ₁ * ε₁ ^ (((p : ℝ) + 1) / p) < f (x k) - f (x (k + 1)) →
      tolMin p q ε₁ ε₂ ε₃ / kappaSARpCC P L p q ≤ f (x k) - f (x (k + 1)) := fun h' =>
    (div_kappaS_le hL P.θ₁_lt_one hε₁.le ccFactor_one_le tolMin_le_one).trans h'.le
  have fin2 : 2 ≤ q → kappaCC P L p 2 P.θ₂ * ε₂ ^ (((p : ℝ) + 1) / ((p : ℝ) - 1)) <
      f (x k) - f (x (k + 1)) →
      tolMin p q ε₁ ε₂ ε₃ / kappaSARpCC P L p q ≤ f (x k) - f (x (k + 1)) := fun hq h' =>
    (div_kappaS_le hL P.θ₂_lt_one hε₂.le (ccFactor_two_le hq) (tolMin_le_two hq)).trans h'.le
  have fin3 : 3 ≤ q → kappaCC P L p 3 P.θ₃ * ε₃ ^ (((p : ℝ) + 1) / ((p : ℝ) - 2)) <
      f (x k) - f (x (k + 1)) →
      tolMin p q ε₁ ε₂ ε₃ / kappaSARpCC P L p q ≤ f (x k) - f (x (k + 1)) := fun hq h' =>
    (div_kappaS_le hL P.θ₃_lt_one hε₃.le (ccFactor_three_le hq) (tolMin_le_three hq)).trans h'.le
  have hx1 : x (k + 1) ∈ C := heq ▸ hxs
  rw [isApproxMinimizerCC_iff] at hk1
  -- first-order measure
  by_cases h1 : omega1 f C (x (k + 1)) ≤ ε₁
  swap
  · exact fin1 (hl.1 (lt_of_not_ge h1))
  -- long step with respect to (6.2.27)
  by_cases hl1 : ‖s k‖ ^ p ≤ (p ! : ℝ) * (1 - P.θ₁) / (L + P.sigmaMax L) * ε₁
  swap
  · have := h.decrease_gt_kappaCC hC hf hk hs hp P.θ₁_lt_one hε₁.le
      (by rw [Nat.sub_add_cancel hp]; exact lt_of_not_ge hl1)
    exact fin1 (by simpa using this)
  have hτ₁ : 0 ≤ P.τ₁ * ε₁ := mul_nonneg P.τ₁_pos.le hε₁.le
  have incl1 : closedBall 0 1 ∩ restrictedSteps₁ f C P.τ₁ ε₁ (x k + s k) ⊆
      modelSteps₁ f C p P.θ₁ ε₁ (x k) (σ k) (s k) := by
    refine inter_closedBall_restrictedSteps_subset_regularizedModel hC.convex hf.contDiffAt
      hf.lipschitz hL hx hxs hσ hp ?_
    rw [Nat.sub_add_cancel hp]
    have := err_le hσmax hpos (by positivity) (by positivity) hl1
    nlinarith [P.one_sub_θ₁_add_τ₁_le]
  have hne1 : (closedBall (0 : ℝⁿ) 1 ∩ restrictedSteps₁ f C P.τ₁ ε₁ (x k + s k)).Nonempty :=
    ⟨0, zero_mem_closedBall_inter (zero_mem_restrictedSteps₁ hxs hτ₁)⟩
  -- second-order measure
  by_cases h2 : 2 ≤ q → omega2 f C P.τ₁ (x (k + 1)) ε₁ ≤ ε₂
  swap
  · simp only [Classical.not_imp, not_le] at h2
    obtain ⟨hq, h2⟩ := h2
    refine fin2 hq (hl.2.1 hq (h2.trans_le ?_))
    rw [heq]
    exact formCriticality_mono _ hne1 incl1
  have hq3 : 3 ≤ q ∧ ε₃ < omega3 f C P.τ₁ P.τ₂ (x (k + 1)) ε₁ ε₂ := by
    by_contra hcon
    exact hk1 ⟨hx1, h1, h2, fun hq => le_of_not_gt fun h' => hcon ⟨hq, h'⟩⟩
  obtain ⟨hq, h3⟩ := hq3
  -- long step with respect to (6.2.28)
  by_cases hl2 : ‖s k‖ ^ (p - 1) ≤ ((p - 1)! : ℝ) * (1 - P.θ₂) / (L + P.sigmaMax L) * ε₂
  swap
  · have e : p - 2 + 1 = p - 1 := by omega
    have := h.decrease_gt_kappaCC hC hf hk hs (j := 2) (by omega) P.θ₂_lt_one hε₂.le
      (by rw [e]; exact lt_of_not_ge hl2)
    refine fin2 (by omega) (lt_of_eq_of_lt ?_ this)
    congr 2; push_cast; ring
  have hτ₂ : 0 ≤ P.τ₂ * ε₂ := mul_nonneg P.τ₂_pos.le hε₂.le
  have incl2 : closedBall 0 1 ∩ restrictedSteps₂ f C P.τ₁ P.τ₂ ε₁ ε₂ (x k + s k) ⊆
      modelSteps₂ f C p P.θ₁ P.θ₂ ε₁ ε₂ (x k) (σ k) (s k) := by
    rintro d ⟨hdB, hd⟩
    have hd1 : d ∈ modelSteps₁ f C p P.θ₁ ε₁ (x k) (σ k) (s k) := incl1 ⟨hdB, hd.1⟩
    refine inter_closedBall_restrictedSteps_subset_regularizedModel (j := 2)
      (T := modelSteps₁ f C p P.θ₁ ε₁ (x k) (σ k) (s k)) hC.convex hf.contDiffAt
      hf.lipschitz hL hx hxs hσ (by omega) ?_ ⟨hdB, hd1, hd.2⟩
    have e : p - 2 + 1 = p - 1 := by omega
    rw [e]
    have := err_le hσmax hpos (by positivity) (by positivity) hl2
    nlinarith [P.one_sub_θ₂_add_τ₂_le]
  have hne2 : (closedBall (0 : ℝⁿ) 1 ∩
      restrictedSteps₂ f C P.τ₁ P.τ₂ ε₁ ε₂ (x k + s k)).Nonempty :=
    ⟨0, zero_mem_closedBall_inter (zero_mem_restrictedSteps₂ hxs hτ₁ hτ₂)⟩
  refine fin3 hq (hl.2.2 hq (h3.trans_le ?_))
  rw [heq]
  exact formCriticality_mono _ hne2 incl2

end algorithm_6_2_1

namespace algorithm_6_2_1

variable {f : ℝⁿ → ℝ} {C : Set ℝⁿ} {p q : ℕ} {L flow : ℝ} {P : ARpCCParams} {ε₁ ε₂ ε₃ : ℝ}
  {x s : ℕ → ℝⁿ} {σ : ℕ → ℝ}

/-- **Theorem 6.2.3** of [cartis2022evaluation]. Let $\mathcal{C}$ satisfy C.CNe, let $f$ satisfy
f.DpL.C with constant $L$ and f.bB.C with $f_{\mathrm{low}}$, and let $q \le p$. Then every run
of ARp-CC of order $q$ terminates: there is a first iteration $k_\epsilon$ at which
$x_{k_\epsilon}$ is an approximate minimizer of order $q$ within $\mathcal{C}$. With the
accuracy term $m_\epsilon = \min_{j \in [1 : q]} \epsilon_j^{(p+1)/(p-j+1)}$, the number of
evaluations of $f$ is at most
$$\kappa^A_{\mathrm{ARpCC}} \frac{f(x_0) - f_{\mathrm{low}}}{m_\epsilon} +
  \kappa^C_{\mathrm{ARpCC}},$$
and the number of evaluations of the derivatives is at most $\kappa^S_{\mathrm{ARpCC}} (f(x_0) -
f_{\mathrm{low}}) / m_\epsilon + 2$. Hence the method needs
$O(\max_j \epsilon_j^{-(p+1)/(p-j+1)})$ evaluations.

**Reading.** The source states the case $q = 3$ and covers $q = 1, 2$ by infinite tolerances.

**Generalization.** The restriction $\epsilon_j \le 1$ of the source is not needed.

The constants are those of the source, with $\sigma_{\max}$ of (4.1.19). The counts are
`Optimization.funEvalCount` and `Optimization.derivEvalCount` of the successful iterations. -/
theorem _root_.CartisGouldToint.Chapter06.theorem_6_2_3
    (hC : AssumptionCNe C) (hf : AssumptionDpLC f C p L)
    (hb : AssumptionBbC f C flow) (hqp : q ≤ p) (h : algorithm_6_2_1 f C p P q ε₁ ε₂ ε₃ x s σ) :
    ∃ kε, IsFirstHit (fun k => IsApproxMinimizerCC f C P.τ₁ P.τ₂ q ε₁ ε₂ ε₃ (x k)) kε ∧
      (funEvalCount kε : ℝ) ≤
        kappaAARpCC P L p q * (f (x 0) - flow) / tolMin p q ε₁ ε₂ ε₃ + kappaCARpCC P L ∧
      (derivEvalCount (fun k => P.η₁ ≤ taylorRatio f p x s k) kε : ℝ) ≤
        kappaSARpCC P L p q * (f (x 0) - flow) / tolMin p q ε₁ ε₂ ε₃ + 2 := by
  have hS := kappaSARpCC_pos (P := P) (p := p) (q := q) hf.nonneg
  have ht := tolMin_pos (p := p) (q := q) h.ε₁_pos h.ε₂_pos h.ε₃_pos
  obtain ⟨kε, hk, hF, hD⟩ := h.run.exists_isFirstHit_of_decrease (σmax := P.sigmaMax L)
    (V := fun k => f (x k)) (Vlow := flow) (δ := tolMin p q ε₁ ε₂ ε₃ / kappaSARpCC P L p q)
    (fun k hk => (h.sigma_le hC hf k (IsARRun.forall_lt_not_stop_iff.1 hk)).2.2) (div_pos ht hS)
    (fun k hk => (h.run.accept k hk).le (w := f) rfl
      (lt_of_le_of_lt (by
          have := P.σmin_nonneg.trans
            (h.sigma_le hC hf k fun j hj => IsARRun.forall_le_not_stop_iff.1 hk j hj.le).2.1
          positivity)
        (arpcc_sub_ge h.run (fun _ hs => hs.decrease) (IsARRun.forall_le_not_stop_iff.1 hk)).1))
    (fun k hk => hb _ (h.sigma_le hC hf k (IsARRun.forall_lt_not_stop_iff.1 hk)).1)
    (fun k hk hs => by
      have hk' := IsARRun.forall_le_not_stop_iff.1 hk
      exact arpcc_decrease_of_not_test h hC hf hqp (fun j hj => hk' j (hj.trans k.le_succ)) hs
        (hk' (k + 1) le_rfl))
  have hN : (f (x 0) - flow) / (tolMin p q ε₁ ε₂ ε₃ / kappaSARpCC P L p q) =
      kappaSARpCC P L p q * (f (x 0) - flow) / tolMin p q ε₁ ε₂ ε₃ := by
    field_simp
  rw [hN] at hF hD
  refine ⟨kε, ⟨hk.1.resolve_right id, fun j hj h' => hk.2 j hj (Or.inl h')⟩, ?_, hD⟩
  refine hF.trans_eq ?_
  rw [kappaAARpCC, kappaCARpCC, kappaSARpCC]
  ring

end algorithm_6_2_1

/-! ### Existence of ARp-CC runs -/

section Existence

variable {f : ℝⁿ → ℝ} {C : Set ℝⁿ} {p q : ℕ} {P : ARpCCParams} {ε₁ ε₂ ε₃ : ℝ}

/-- **Algorithm 6.2.1** of [cartis2022evaluation], existence of runs when Step 2 is always feasible.
Let $\epsilon_1, \epsilon_2, \epsilon_3 > 0$ and $1 \le q \le 3$. Suppose that at every
$y \in \mathcal{C}$ that is not an approximate minimizer of order $q$, and for every
$\sigma \ge \sigma_{\min}$, some step satisfies the Step 2 conditions. Then for every
$x_0 \in \mathcal{C}$ there is a run of ARp-CC of order $q$ that starts at $x_0$.

The hypothesis can fail for $q \ge 2$
(`CartisGouldToint.Chapter06.algorithm_6_2_1_not_exists_step`).

**Reading.** The source's run construction is conditional on explicit admissible steps.
-/
theorem exists_algorithm_6_2_1_of_forall_exists_step (h₁ : 0 < ε₁) (h₂ : 0 < ε₂) (h₃ : 0 < ε₃)
    (hq : 1 ≤ q) (hq3 : q ≤ 3)
    (hstep : ∀ y ∈ C, ∀ σ, P.σmin ≤ σ → ¬ IsApproxMinimizerCC f C P.τ₁ P.τ₂ q ε₁ ε₂ ε₃ y →
      ∃ s, IsARpCCStep f C p P q ε₁ ε₂ ε₃ y σ s)
    {x₀ : ℝⁿ} (hx₀ : x₀ ∈ C) :
    ∃ x s σ, x 0 = x₀ ∧ algorithm_6_2_1 f C p P q ε₁ ε₂ ε₃ x s σ := by
  obtain ⟨x, s, σ, hx0, hrun, -⟩ := exists_isARRun P.toARParams (Inv := (· ∈ C))
    (test := IsApproxMinimizerCC f C P.τ₁ P.τ₂ q ε₁ ε₂ ε₃)
    (stepOK := IsARpCCStep f C p P q ε₁ ε₂ ε₃)
    (fun y _ t => reductionRatio f y t ((ftaylorSeries ℝ f y).taylorDecrement p t))
    (fun y σ hy hσ _ ht => by
      obtain ⟨s, hs⟩ := hstep y hy σ hσ ht
      exact ⟨s, hs, hs.mem⟩) hx₀
  exact ⟨x, s, σ, hx0, h₁, h₂, h₃, hq, hq3, hx0 ▸ hx₀, hrun⟩

/-- **Algorithm 6.2.1** of [cartis2022evaluation], existence of first-order runs. Let $\mathcal{C}$
satisfy C.CNe, let $f$ be $p$ times continuously differentiable at every point of $\mathcal{C}$
with $p \ge 1$, and let $\epsilon_1, \epsilon_2, \epsilon_3 > 0$. Then for every
$x_0 \in \mathcal{C}$ there is a run of ARp-CC of order $q = 1$ that starts at $x_0$.

**Generalization.** Differentiability is assumed only at the points of $\mathcal{C}$, not on an
open set $\mathcal{D} \supseteq \mathcal{C}$ as in f.DpL.C.

A global minimizer of the model over $\mathcal{C}(x_k)$ satisfies (6.2.10) with model measure
$0$ (`Optimization.exists_isFirstOrderCCStep`). -/
theorem exists_algorithm_6_2_1_one (hC : AssumptionCNe C) (hf : ∀ y ∈ C, ContDiffAt ℝ p f y)
    (hp : 1 ≤ p) (h₁ : 0 < ε₁) (h₂ : 0 < ε₂) (h₃ : 0 < ε₃) {x₀ : ℝⁿ} (hx₀ : x₀ ∈ C) :
    ∃ x s σ, x 0 = x₀ ∧ algorithm_6_2_1 f C p P 1 ε₁ ε₂ ε₃ x s σ := by
  refine exists_algorithm_6_2_1_of_forall_exists_step h₁ h₂ h₃ le_rfl (by norm_num)
    (fun y hy σ hσ ht => ?_) hx₀
  have hω : ε₁ < omega1 f C y := by
    by_contra h'
    exact ht ⟨hy, le_of_not_gt h', fun h => absurd h (by norm_num),
      fun h => absurd h (by norm_num)⟩
  obtain ⟨s, -, hs, hzero⟩ := exists_isFirstOrderCCStep (θ := P.θ₁) hC.isClosed hC.convex hy
    (hf y hy) hp (P.σmin_pos.trans_le hσ) P.θ₁_pos.le (h₁.trans hω)
  refine ⟨s, hs.mem, hs.decrease, ?_, fun h => absurd h (by norm_num),
    fun h => absurd h (by norm_num)⟩
  rw [modelOmega1, modelSteps₀_eq, hzero]
  exact mul_nonneg P.θ₁_pos.le h₁.le

end Existence

/-! ### ARp1-CC: Lemma 6.2.4 and Theorem 6.2.5 -/

/-- **Equation (4.1.32)** of [cartis2022evaluation], the constant used by Lemma 6.2.4. Let $P$ be
ARp-CC constants, $L \in \mathbb{R}$ and $p \in \mathbb{N}$. The constant is
$$\kappa_1 = \frac{\eta_1 \sigma_{\min}}{(p+1)!} \left(\frac{p!}{L + \sigma_{\max} + \theta_1
  p!}\right)^{(p+1)/p}.$$
-/
noncomputable def kappa1CC (P : ARpCCParams) (L : ℝ) (p : ℕ) : ℝ :=
  P.η₁ * P.σmin / ((p + 1)! : ℝ) *
    ((p ! : ℝ) / (L + P.sigmaMax L + P.θ₁ * p !)) ^ (((p : ℝ) + 1) / p)

/-- The definition of $\kappa_1$, unfolded. -/
theorem kappa1CC_def (P : ARpCCParams) (L : ℝ) (p : ℕ) :
    kappa1CC P L p = P.η₁ * P.σmin / ((p + 1)! : ℝ) *
      ((p ! : ℝ) / (L + P.sigmaMax L + P.θ₁ * p !)) ^ (((p : ℝ) + 1) / p) :=
  rfl

/-- **Theorem 6.2.5** of [cartis2022evaluation], the constant $\kappa^S$. The constant is
$$\kappa^S_{\mathrm{ARp1CC}} = \frac{(p+1)!}{\eta_1 \sigma_{\min}} \left(\frac{L +
  \sigma_{\max} + \theta_1 p!}{p!}\right)^{(p+1)/p},$$
which is $1 / \kappa_1$ for $L \ge 0$. -/
noncomputable def kappaSARp1CC (P : ARpCCParams) (L : ℝ) (p : ℕ) : ℝ :=
  ((p + 1)! : ℝ) / (P.η₁ * P.σmin) *
    ((L + P.sigmaMax L + P.θ₁ * p !) / (p ! : ℝ)) ^ (((p : ℝ) + 1) / p)

/-- **Theorem 6.2.5** of [cartis2022evaluation], the constant $\kappa^A$. The constant is
$\kappa^A_{\mathrm{ARp1CC}} = \kappa^S_{\mathrm{ARp1CC}} (1 + |\log \gamma_1| / \log \gamma_2)$. -/
noncomputable def kappaAARp1CC (P : ARpCCParams) (L : ℝ) (p : ℕ) : ℝ :=
  kappaSARp1CC P L p * (1 + |Real.log P.γ₁| / Real.log P.γ₂)

/-- If $L \ge 0$, then $\kappa_1 > 0$. -/
theorem kappa1CC_pos {P : ARpCCParams} {L : ℝ} {p : ℕ} (hL : 0 ≤ L) : 0 < kappa1CC P L p := by
  have := P.η₁_pos; have := P.σmin_pos; have := P.sigmaMax_pos L; have := P.θ₁_pos
  unfold kappa1CC; positivity

/-- If $L \ge 0$, then $\kappa_1 \kappa^S_{\mathrm{ARp1CC}} = 1$. -/
theorem kappa1CC_mul_kappaSARp1CC {P : ARpCCParams} {L : ℝ} (hL : 0 ≤ L) (p : ℕ) :
    kappa1CC P L p * kappaSARp1CC P L p = 1 := by
  have := P.η₁_pos; have := P.σmin_pos; have := P.sigmaMax_pos L; have := P.θ₁_pos
  have hK : 0 < L + P.sigmaMax L + P.θ₁ * p ! := by positivity
  rw [kappa1CC, kappaSARp1CC, ← inv_div (L + P.sigmaMax L + P.θ₁ * p !),
    Real.inv_rpow (by positivity)]
  have : 0 < ((L + P.sigmaMax L + P.θ₁ * p !) / (p ! : ℝ)) ^ (((p : ℝ) + 1) / p) := by
    positivity
  field_simp

section ARp1CC

variable {f : ℝⁿ → ℝ} {C : Set ℝⁿ} {p : ℕ} {P : ARpCCParams} {ε₁ : ℝ}

/-- **Algorithm 6.2.2** of [cartis2022evaluation], existence of runs. Let $\mathcal{C}$ satisfy
C.CNe, let $f$ be $p$ times continuously differentiable at every point of $\mathcal{C}$ with
$p \ge 1$, and let $\epsilon_1 > 0$. Then for every $x_0 \in \mathcal{C}$ there is a run of
ARp1-CC that starts at $x_0$.

**Generalization.** Differentiability is assumed only at the points of $\mathcal{C}$, not on an
open set $\mathcal{D} \supseteq \mathcal{C}$ as in f.DpL.C.

A global minimizer of the model over $\mathcal{C}(x_k)$ satisfies (6.2.29)
(`Optimization.exists_isFirstOrderCCStep`). -/
theorem exists_algorithm_6_2_2 (hC : AssumptionCNe C) (hf : ∀ y ∈ C, ContDiffAt ℝ p f y)
    (hp : 1 ≤ p) (h₁ : 0 < ε₁) {x₀ : ℝⁿ} (hx₀ : x₀ ∈ C) :
    ∃ x s σ, x 0 = x₀ ∧ algorithm_6_2_2 f C p P ε₁ x s σ := by
  obtain ⟨x, s, σ, hx0, hrun, -⟩ := exists_isARRun P.toARParams (Inv := (· ∈ C))
    (test := fun y => omega1 f C y ≤ ε₁) (stepOK := IsFirstOrderCCStep f C p P.θ₁)
    (fun y _ t => reductionRatio f y t ((ftaylorSeries ℝ f y).taylorDecrement p t))
    (fun y σ hy _ hσ ht => by
      obtain ⟨s, -, hs, -⟩ := exists_isFirstOrderCCStep (θ := P.θ₁) hC.isClosed hC.convex hy
        (hf y hy) hp hσ P.θ₁_pos.le (h₁.trans (lt_of_not_ge ht))
      exact ⟨s, hs, hs.mem⟩) hx₀
  exact ⟨x, s, σ, hx0, h₁, hx0 ▸ hx₀, hrun⟩

namespace algorithm_6_2_2

variable {x s : ℕ → ℝⁿ} {σ : ℕ → ℝ} {L flow : ℝ}

/-- Lemma 4.1.2 for ARp1-CC runs (`CartisGouldToint.Chapter06.arpcc_sigma_le`): under C.CNe and
f.DpL.C, if $\omega_{f,\mathcal{C},1}(x_j) > \epsilon_1$ for all $j < k$, then
$x_k \in \mathcal{C}$ and $\sigma_{\min} \le \sigma_k \le \sigma_{\max}$. -/
theorem sigma_le (h : algorithm_6_2_2 f C p P ε₁ x s σ) (hC : AssumptionCNe C)
    (hf : AssumptionDpLC f C p L) (k : ℕ) (hk : ∀ j < k, ¬ omega1 f C (x j) ≤ ε₁) :
    x k ∈ C ∧ P.σmin ≤ σ k ∧ σ k ≤ P.sigmaMax L :=
  arpcc_sigma_le h.run hC hf h.mem_zero (fun _ hs => ⟨hs.mem, hs.decrease⟩) k hk

/-- **Lemma 6.2.4** of [cartis2022evaluation]. Let $\mathcal{C}$ satisfy C.CNe, let $f$ satisfy
f.DpL.C with constant $L$, and let $p \ge 1$. Consider a run of ARp1-CC, and let $k$ be a
successful iteration such that $\omega_{f,\mathcal{C},1}(x_j) > \epsilon_1$ for all $j \le k$.
Then
$$f(x_k) - f(x_{k+1}) \ge \kappa_1 \, \omega_{f,\mathcal{C},1}(x_{k+1})^{(p+1)/p},$$
with $\kappa_1$ of (4.1.32). -/
theorem _root_.CartisGouldToint.Chapter06.lemma_6_2_4
    (h : algorithm_6_2_2 f C p P ε₁ x s σ) (hC : AssumptionCNe C)
    (hf : AssumptionDpLC f C p L) (hp : 1 ≤ p) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ omega1 f C (x j) ≤ ε₁) (hs : P.η₁ ≤ taylorRatio f p x s k) :
    kappa1CC P L p * omega1 f C (x (k + 1)) ^ (((p : ℝ) + 1) / p) ≤ f (x k) - f (x (k + 1)) := by
  have hk' := IsARRun.forall_le_not_stop_iff.2 hk
  obtain ⟨hx, hmin, hmax⟩ := h.sigma_le hC hf k fun j hj => hk j hj.le
  have hstep : IsFirstOrderCCStep f C p P.θ₁ (x k) (σ k) (s k) := h.run.step_of_forall_le hk'
  rw [h.run.eq_add_of_succ hk' hs]
  exact hstep.sub_ge hC.convex hf.contDiffAt hf.lipschitz hf.nonneg hx hp P.θ₁_pos.le
    P.σmin_nonneg hmin hmax P.η₁_pos hs

/-- **Theorem 6.2.5** of [cartis2022evaluation]. Let $\mathcal{C}$ satisfy C.CNe, let $f$ satisfy
f.DpL.C with constant $L$ and f.bB.C with $f_{\mathrm{low}}$, and let $p \ge 1$. Then every run
of ARp1-CC terminates at a first iteration $k_\epsilon$ with
$\omega_{f,\mathcal{C},1}(x_{k_\epsilon}) \le \epsilon_1$. The number of evaluations of $f$ is
at most
$$\kappa^A_{\mathrm{ARp1CC}} \frac{f(x_0) - f_{\mathrm{low}}}{\epsilon_1^{(p+1)/p}} +
  \kappa^C_{\mathrm{ARp}},$$
and the number of evaluations of the derivatives is at most $\kappa^S_{\mathrm{ARp1CC}}
(f(x_0) - f_{\mathrm{low}}) / \epsilon_1^{(p+1)/p} + 2$.

**Generalization.** The restriction $\epsilon_1 \le 1$ of the source is not needed.

The constant $\kappa^C_{\mathrm{ARp}}$ is `CartisGouldToint.Chapter06.kappaCARpCC`. -/
theorem _root_.CartisGouldToint.Chapter06.theorem_6_2_5
    (hC : AssumptionCNe C) (hf : AssumptionDpLC f C p L)
    (hb : AssumptionBbC f C flow) (hp : 1 ≤ p) (h : algorithm_6_2_2 f C p P ε₁ x s σ) :
    ∃ kε, IsFirstHit (fun k => omega1 f C (x k) ≤ ε₁) kε ∧
      (funEvalCount kε : ℝ) ≤
        kappaAARp1CC P L p * (f (x 0) - flow) / ε₁ ^ (((p : ℝ) + 1) / p) + kappaCARpCC P L ∧
      (derivEvalCount (fun k => P.η₁ ≤ taylorRatio f p x s k) kε : ℝ) ≤
        kappaSARp1CC P L p * (f (x 0) - flow) / ε₁ ^ (((p : ℝ) + 1) / p) + 2 := by
  have hL := hf.nonneg
  have hε := h.ε₁_pos
  have hκ := kappa1CC_mul_kappaSARp1CC (P := P) hL p
  have hκ1 : 0 < kappa1CC P L p := by
    have := P.η₁_pos; have := P.σmin_pos; have := P.sigmaMax_pos L; have := P.θ₁_pos
    unfold kappa1CC; positivity
  have he : 0 < ((p : ℝ) + 1) / p := by
    have : (0 : ℝ) < p := by exact_mod_cast hp
    positivity
  obtain ⟨kε, hk, hF, hD⟩ := h.run.exists_isFirstHit_of_decrease (σmax := P.sigmaMax L)
    (V := fun k => f (x k)) (Vlow := flow) (δ := kappa1CC P L p * ε₁ ^ (((p : ℝ) + 1) / p))
    (fun k hk => (h.sigma_le hC hf k (IsARRun.forall_lt_not_stop_iff.1 hk)).2.2) (by positivity)
    (fun k hk => (h.run.accept k hk).le (w := f) rfl
      (lt_of_le_of_lt (by
          have := P.σmin_nonneg.trans
            (h.sigma_le hC hf k fun j hj => IsARRun.forall_le_not_stop_iff.1 hk j hj.le).2.1
          positivity)
        (arpcc_sub_ge h.run (fun _ hs => hs.decrease) (IsARRun.forall_le_not_stop_iff.1 hk)).1))
    (fun k hk => hb _ (h.sigma_le hC hf k (IsARRun.forall_lt_not_stop_iff.1 hk)).1)
    (fun k hk hs => by
      have hk' := IsARRun.forall_le_not_stop_iff.1 hk
      refine le_trans ?_ (lemma_6_2_4 h hC hf hp (fun j hj => hk' j (hj.trans k.le_succ)) hs)
      gcongr
      exact (lt_of_not_ge (hk' (k + 1) le_rfl)).le)
  have hN : (f (x 0) - flow) / (kappa1CC P L p * ε₁ ^ (((p : ℝ) + 1) / p)) =
      kappaSARp1CC P L p * (f (x 0) - flow) / ε₁ ^ (((p : ℝ) + 1) / p) := by
    have : kappaSARp1CC P L p = (kappa1CC P L p)⁻¹ := (eq_inv_of_mul_eq_one_right hκ)
    rw [this]
    have : 0 < ε₁ ^ (((p : ℝ) + 1) / p) := by positivity
    field_simp
  rw [hN] at hF hD
  refine ⟨kε, ⟨hk.1.resolve_right id, fun j hj h' => hk.2 j hj (Or.inl h')⟩, ?_, hD⟩
  refine hF.trans_eq ?_
  rw [kappaAARp1CC, kappaCARpCC]
  ring

end algorithm_6_2_2

end ARp1CC

/-! ### Step 2 of ARp-CC may be infeasible -/

section Counterexample

/-- The derivative of $t \mapsto a t + b t^2 + c t^3$ is $t \mapsto a + 2 b t + 3 c t^2$. -/
private theorem deriv_cubic (a b c : ℝ) :
    deriv (fun t : ℝ => a * t + b * t ^ 2 + c * t ^ 3) =
      fun t => a + 2 * b * t + 3 * c * t ^ 2 := by
  funext t
  have := (((hasDerivAt_id' t).const_mul a).add ((hasDerivAt_pow 2 t).const_mul b)).add
    ((hasDerivAt_pow 3 t).const_mul c)
  refine this.deriv.trans ?_; push_cast; ring

/-- The first three derivatives of $t \mapsto a t + b t^2 + c t^3$ at $t$ are $a + 2 b t + 3 c t^2$,
$2 b + 6 c t$ and $6 c$. -/
private theorem iteratedDeriv_cubic (a b c t : ℝ) :
    iteratedDeriv 1 (fun t : ℝ => a * t + b * t ^ 2 + c * t ^ 3) t =
        a + 2 * b * t + 3 * c * t ^ 2 ∧
      iteratedDeriv 2 (fun t : ℝ => a * t + b * t ^ 2 + c * t ^ 3) t = 2 * b + 6 * c * t ∧
      iteratedDeriv 3 (fun t : ℝ => a * t + b * t ^ 2 + c * t ^ 3) t = 6 * c := by
  have h1 := deriv_cubic a b c
  have h2 : deriv (fun t : ℝ => a + 2 * b * t + 3 * c * t ^ 2) = fun t => 2 * b + 6 * c * t := by
    have := deriv_cubic (2 * b) (3 * c) 0
    funext t
    have e : (fun t : ℝ => a + 2 * b * t + 3 * c * t ^ 2) =
        fun t => (2 * b * t + 3 * c * t ^ 2 + 0 * t ^ 3) + a := by funext t; ring
    rw [e, deriv_add_const, this]; ring
  have h3 : deriv (fun t : ℝ => 2 * b + 6 * c * t) = fun _ => 6 * c := by
    funext t
    have := ((hasDerivAt_id t).const_mul (6 * c)).const_add (2 * b)
    simp
  refine ⟨?_, ?_, ?_⟩
  · rw [iteratedDeriv_one, h1]
  · rw [iteratedDeriv_succ, iteratedDeriv_one, h1, h2]
  · rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one, h1, h2, h3]

/-- **Algorithm 6.2.1** of [cartis2022evaluation], Step 2 can be infeasible for $q \ge 2$. Let $P$
be ARp-CC constants, let $\epsilon_1, \epsilon_2 > 0$, let $\epsilon_3 \in \mathbb{R}$, and let
$q \ge 2$. Then there are a set $\mathcal{C} \subseteq \mathbb{R}^1$ and a function
$f : \mathbb{R}^1 \to \mathbb{R}$ such that:
* $\mathcal{C}$ satisfies C.CNe, $f$ satisfies f.DpL.C with $p = 3$ and $L = 0$, and $f$
  satisfies f.bB.C with $f_{\mathrm{low}} = 0$;
* $0 \in \mathcal{C}$ and $f(0) < f(y)$ for every $y \in \mathcal{C}$ with $y \ne 0$, so $0$ is
  a strict global minimizer of $f$ on $\mathcal{C}$;
* $0$ is not an approximate minimizer of order $q$ within $\mathcal{C}$;
* for every $\sigma \ge 0$, no step satisfies the Step 2 conditions at $x = 0$ with $p = 3$;
* no run of ARp-CC with $p = 3$ starts at $x_0 = 0$.

**Correction.** The source asserts in Section 6.2.1 that the model measures (6.2.3)–(6.2.5)
"will all be small in the neighbourhood of any … global minimizer of $m_k$".
In the example below the model second-order measure at its global minimizer $0$
is at least $K$, since $\tau_1\epsilon_1<\theta_1\epsilon_1$ and the quartic
regularizer has zero Hessian at $0$. The approximate test ranges over ascent
directions with a small first derivative, and Step 2 also requires strict model decrease.
Theorem 6.2.3 holds for every run.

The example is $\mathcal{C} = \{x \mid x_1 \ge 0\}$ and
$f(x) = g x_1 - \frac{K}{2} x_1^2 + c x_1^3$ with $g = \tau_1 \epsilon_1$, $K = 2 \epsilon_2$
and $c = K^2 / (8 g)$. Then $\omega_{f,\mathcal{C},2}(0, \epsilon_1) \ge K > \epsilon_2$,
attained in the ascent direction $d = 1$, while $m(s) - m(0) = s(g - K s / 2 + c s^2) + \sigma
s^4 / 24 \ge 0$ for $s \ge 0$. -/
theorem algorithm_6_2_1_not_exists_step (P : ARpCCParams) {ε₁ ε₂ ε₃ : ℝ} (h₁ : 0 < ε₁)
    (h₂ : 0 < ε₂) {q : ℕ} (hq : 2 ≤ q) :
    ∃ (C : Set (EuclideanSpace ℝ (Fin 1))) (f : EuclideanSpace ℝ (Fin 1) → ℝ),
      AssumptionCNe C ∧ AssumptionDpLC f C 3 0 ∧ AssumptionBbC f C 0 ∧ (0 : _) ∈ C ∧
      (∀ y ∈ C, y ≠ 0 → f 0 < f y) ∧
      ¬ IsApproxMinimizerCC f C P.τ₁ P.τ₂ q ε₁ ε₂ ε₃ 0 ∧
      (∀ σ, 0 ≤ σ → ∀ s, ¬ IsARpCCStep f C 3 P q ε₁ ε₂ ε₃ 0 σ s) ∧
      ¬ ∃ x s σ, x 0 = 0 ∧ algorithm_6_2_1 f C 3 P q ε₁ ε₂ ε₃ x s σ := by
  set g := P.τ₁ * ε₁ with hg_def
  set K := 2 * ε₂ with hK_def
  set c := K ^ 2 / (8 * g) with hc_def
  have hg : 0 < g := mul_pos P.τ₁_pos h₁
  have hK : 0 < K := by positivity
  have hc : 0 < c := by positivity
  set h : ℝ → ℝ := fun t => g * t + (-K / 2) * t ^ 2 + c * t ^ 3 with hh_def
  have hh : ContDiff ℝ ⊤ h := by rw [hh_def]; fun_prop
  have hD : ∀ t, iteratedDeriv 1 h t = g + 2 * (-K / 2) * t + 3 * c * t ^ 2 ∧
      iteratedDeriv 2 h t = 2 * (-K / 2) + 6 * c * t ∧ iteratedDeriv 3 h t = 6 * c :=
    iteratedDeriv_cubic g (-K / 2) c
  set f : EuclideanSpace ℝ (Fin 1) → ℝ := fun y => h (y 0) with hf_def
  set C : Set (EuclideanSpace ℝ (Fin 1)) := {y | 0 ≤ y 0} with hC_def
  have hquad : ∀ t, g / 2 ≤ g + (-K / 2) * t + c * t ^ 2 := by
    intro t
    have : c * (8 * g) = K ^ 2 := by rw [hc_def]; field_simp
    nlinarith [sq_nonneg (K * t - 2 * g)]
  have hfval : ∀ y, f y = y 0 * (g + (-K / 2) * y 0 + c * y 0 ^ 2) := by
    intro y; simp only [hf_def, hh_def]; ring
  have hf0 : f 0 = 0 := by simp [hfval]
  have hfnn : ∀ y ∈ C, 0 ≤ f y := fun y hy => by
    rw [hfval]; exact mul_nonneg hy (by linarith [hquad (y 0)])
  have hdiag : ∀ k x d, iteratedFDeriv ℝ k f x (fun _ => d) = d 0 ^ k * iteratedDeriv k h (x 0) :=
    fun k x d => by
      rw [(hh.contDiffAt.of_le le_top).iteratedFDeriv_comp_coord_apply 0]; simp [mul_comm]
  -- the assumptions
  have hCNe : AssumptionCNe C := by
    refine ⟨isClosed_le continuous_const (by fun_prop), ?_, ⟨0, by simp [hC_def]⟩⟩
    intro x hx y hy a b ha hb _
    simp only [hC_def, mem_ofPred_eq, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at *
    positivity
  have hfC : ContDiff ℝ ⊤ f := by
    have := hh.comp (EuclideanSpace.proj (0 : Fin 1) :
      EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ).contDiff
    convert this using 1
    funext y; simp [hf_def]
  have hDpL : AssumptionDpLC f C 3 0 := by
    refine ⟨le_rfl, ⟨univ, isOpen_univ, subset_univ _,
      (hfC.of_le (by exact_mod_cast le_top)).contDiffOn⟩, ?_⟩
    intro x _ y _
    have : iteratedFDeriv ℝ 3 f x = iteratedFDeriv ℝ 3 f y := by
      ext m
      rw [(hh.contDiffAt.of_le le_top).iteratedFDeriv_comp_coord_apply 0,
        (hh.contDiffAt.of_le le_top).iteratedFDeriv_comp_coord_apply 0, (hD (x 0)).2.2,
        (hD (y 0)).2.2]
    simp [this]
  -- the strict minimizer
  have hstrict : ∀ y ∈ C, y ≠ 0 → f 0 < f y := by
    intro y hy hy0
    have hpos : 0 < y 0 := by
      refine lt_of_le_of_ne hy fun h0 => hy0 ?_
      ext i; fin_cases i; simp [← h0]
    rw [hf0, hfval]
    exact mul_pos hpos (by linarith [hquad (y 0)])
  -- the second-order test fails at `0`
  have hnot : ¬ IsApproxMinimizerCC f C P.τ₁ P.τ₂ q ε₁ ε₂ ε₃ 0 := by
    rintro ⟨-, -, h2, -⟩
    set e : EuclideanSpace ℝ (Fin 1) := EuclideanSpace.single 0 1
    have he : e 0 = 1 := by simp [e]
    have hmem : e ∈ Metric.closedBall 0 1 ∩ restrictedSteps₁ f C P.τ₁ ε₁ 0 := by
      refine ⟨by simp [e], ?_, ?_⟩
      · simp [mem_feasibleSteps, hC_def, he]
      · have : |g| ≤ P.τ₁ * ε₁ := by rw [abs_of_pos hg]
        rw [hdiag, he, (hD _).1]; simpa using this
    have := le_formCriticality (iteratedFDeriv ℝ 2 f 0) hmem
    rw [hdiag, he, (hD _).2.1] at this
    have h2' := h2 hq
    rw [omega2] at h2'
    norm_num at this
    linarith
  -- no admissible step at `0`
  have hnostep : ∀ σ, 0 ≤ σ → ∀ s, ¬ IsARpCCStep f C 3 P q ε₁ ε₂ ε₃ 0 σ s := by
    intro σ hσ s hs
    have hdec := hs.decrease
    have hsC : s ∈ C := by simpa using hs.mem
    rw [regularizedModel_ftaylorSeries_zero_right, hf0, regularizedModel_def,
      FormalMultilinearSeries.taylorSum_def] at hdec
    have hT : ∑ i ∈ Finset.range (3 + 1), ((i ! : ℝ))⁻¹ • ftaylorSeries ℝ f 0 i (fun _ => s) =
        f s := by
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, ftaylorSeries,
        hdiag, smul_eq_mul]
      rw [(hD _).1, (hD _).2.1, (hD _).2.2, iteratedDeriv_zero, hfval]
      simp only [hh_def, Nat.factorial, PiLp.zero_apply]
      push_cast
      ring
    rw [hT] at hdec
    have := hfnn s hsC
    have : 0 ≤ σ / ((3 + 1)! : ℝ) * ‖s‖ ^ (3 + 1) := by positivity
    linarith
  refine ⟨C, f, hCNe, hDpL, fun y hy => hf0 ▸ (hfnn y hy), by simp [hC_def], hstrict, hnot,
    hnostep, ?_⟩
  rintro ⟨x, s, σ, hx0, hrun⟩
  have hst := hrun.run.step 0 (fun j hj => absurd hj (Nat.not_lt_zero _))
    (by rw [hx0]; exact hnot)
  rw [hx0] at hst
  exact hnostep (σ 0) (hrun.run.sigma_zero ▸ P.σ₀_pos.le) (s 0) hst

end Counterexample

end CartisGouldToint.Chapter06
