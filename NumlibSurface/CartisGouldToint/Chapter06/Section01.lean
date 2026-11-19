/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Numlib.Optimization.Optimality.ConstrainedMeasure

/-!
# Cartis, Gould and Toint, Section 6.1: Problems with convex constraints

This module formalizes Section 6.1 of [cartis2022evaluation]. The problem is
$\min_{x \in \mathcal{C}} f(x)$ (6.1.1) for a smooth $f : \mathbb{R}^n \to \mathbb{R}$ and a set
$\mathcal{C} \subseteq \mathbb{R}^n$. The section states the standing assumption C.CNe that
$\mathcal{C}$ is closed, convex and nonempty, and it defines approximate criticality measures of
orders one to three. With the feasible steps $\mathcal{C}(x) = \{d \mid x + d \in \mathcal{C}\}$
(6.1.2) and the Euclidean unit ball $\mathcal{B}$ (6.1.3), the measures are
$$\omega_{f,\mathcal{C},1}(x) = -\min_{d \in \mathcal{C}(x) \cap \mathcal{B}} \nabla^1 f(x)[d],
  \qquad \omega_{f,\mathcal{C},2}(x, \alpha) = -\min_{d \in \mathcal{C}^1(x, \alpha) \cap
  \mathcal{B}} \nabla^2 f(x)[d]^2,$$
$$\omega_{f,\mathcal{C},3}(x, \alpha_1, \alpha_2) = -\min_{d \in \mathcal{C}^2(x, \alpha_1,
  \alpha_2) \cap \mathcal{B}} \nabla^3 f(x)[d]^3,$$
where $\mathcal{C}^1(x, \alpha) = \{d \in \mathcal{C}(x) \mid |\nabla^1 f(x)[d]| \le \tau_1
\alpha\}$ (6.1.8) and $\mathcal{C}^2(x, \alpha_1, \alpha_2) = \{d \in \mathcal{C}^1(x, \alpha_1)
\mid |\nabla^2 f(x)[d]^2| \le \tau_2 \alpha_2\}$ (6.1.10). A point $x \in \mathcal{C}$ is an
approximate minimizer of order $q$ when the first $q$ measures are below the tolerances (6.1.4),
(6.1.6).

All measures are instances of the backbone `Optimization.formCriticality`, and the restricted sets
are instances of `Optimization.restrictedSteps` from
`Numlib.Optimization.Optimality.ConstrainedMeasure`.

## Main definitions

* Assumption C.CNe, `CartisGouldToint.Chapter06.AssumptionCNe`: $\mathcal{C}$ is closed, convex and
  nonempty.
* Equations (6.1.4) and (6.1.6), `CartisGouldToint.Chapter06.IsApproxMinimizerCC`: $x$ is an
  approximate minimizer of order $q \in \{1, 2, 3\}$ of $f$ within $\mathcal{C}$.
* Equation (6.1.5), `CartisGouldToint.Chapter06.omega1`: the first-order measure
  $\omega_{f,\mathcal{C},1}(x)$.
* Equation (6.1.7), `CartisGouldToint.Chapter06.omega2`: the second-order measure
  $\omega_{f,\mathcal{C},2}(x, \alpha)$.
* Equation (6.1.8), `CartisGouldToint.Chapter06.restrictedSteps₁`: the restricted set
  $\mathcal{C}^1(x, \alpha)$.
* Equation (6.1.9), `CartisGouldToint.Chapter06.omega3`: the third-order measure
  $\omega_{f,\mathcal{C},3}(x, \alpha_1, \alpha_2)$.
* Equation (6.1.10), `CartisGouldToint.Chapter06.restrictedSteps₂`: the restricted set
  $\mathcal{C}^2(x, \alpha_1, \alpha_2)$.

## Main results

* `CartisGouldToint.Chapter06.not_assumptionCNe_imp_exists_minimizer`: C.CNe alone does not ensure
  that (6.1.1) has a solution.
* `CartisGouldToint.Chapter06.omega1_nonneg`, `CartisGouldToint.Chapter06.omega2_nonneg`,
  `CartisGouldToint.Chapter06.omega3_nonneg`: the three measures are nonnegative at feasible points.
* `CartisGouldToint.Chapter06.exists_omega1_eq`: under C.CNe the minimum in (6.1.5) is attained.
* `CartisGouldToint.Chapter06.omega1_eq_zero_iff`: on a convex set,
  $\omega_{f,\mathcal{C},1}(x) = 0$ if and only if $x$ satisfies the first-order condition (1.1.6).
* `CartisGouldToint.Chapter06.omega1_univ`,
  `CartisGouldToint.Chapter06.isApproxMinimizerCC_one_univ_iff`: without constraints the first-order
  measure is $\|\nabla f(x)\|$, and the first-order test is $\|\nabla f(x)\| \le \epsilon_1$.

## Conventions

* $\mathbb{R}^n$ is `EuclideanSpace ℝ (Fin n)`.
* $\nabla^j f(x)$ is `iteratedFDeriv ℝ j f x`.
* The order $q$ of the sought minimizer is explicit, in place of the infinite tolerances of the
  source: $\epsilon_2 = \epsilon_3 = \infty$ is $q = 1$, and $\epsilon_3 = \infty$ is $q = 2$.

## Implementation notes

* The minimum $-\min_{d \in T \cap \mathcal{B}} A[d]^j$ is `Optimization.formCriticality A T`, the
  supremum `sSup` in $\mathbb{R}$ of $-A[d]^j$ over $d \in T$ with $\|d\| \le 1$. Under C.CNe the
  supremum in $\omega_{f,\mathcal{C},1}(x)$ is attained at feasible points
  (`CartisGouldToint.Chapter06.exists_omega1_eq`). If no $d \in T$ has $\|d\| \le 1$, the value is
  $0$. For $T = \mathcal{C}(x)$ this happens only for $x \notin \mathcal{C}$, and for the restricted
  sets also when $\tau_1 \alpha < 0$ or $\tau_2 \alpha_2 < 0$; the measures carry no information in
  these cases.
* The feasible steps $\mathcal{C}(x)$ are `Optimization.feasibleSteps C x`.

## Deviations from the source

* **Start of Section 6.1** (correction). The source claims that C.CNe ensures that (6.1.1) has a
  solution. This is false: $f(x) = x$ on $\mathcal{C} = \mathbb{R}$ has no minimizer. See
  `CartisGouldToint.Chapter06.not_assumptionCNe_imp_exists_minimizer`.
* **Equations (6.1.4) and (6.1.6)** (reading). The source asks for approximate minimizers "within
  $\mathcal{C}$"; this is the explicit condition $x \in \mathcal{C}$. See
  `CartisGouldToint.Chapter06.IsApproxMinimizerCC`.
* **Domain of the measures and tests** (generalization). The measures give zero on an
  empty direction set. The predicates accept unrestricted real thresholds and an
  explicit natural order. The algorithm supplies the source's parameter ranges.
  See `CartisGouldToint.Chapter06.IsApproxMinimizerCC`.
* **End of Section 6.1.1** (correction). The third-order test in (6.1.9) can
  differ from (4.1.3) even in the unconstrained case. The former can detect
  directions inside the unit ball that the unit-sphere test omits.
  See `CartisGouldToint.Chapter06.omega3`.

## Not formalized

* The remarks on the continuity and discontinuity of $\omega_{f,\mathcal{C},2}(x, 0)$.
* The remarks on computational cost.
* The remarks on norms other than the Euclidean norm.
-/

open Set Metric
open scoped RealInnerProductSpace

namespace CartisGouldToint.Chapter06

variable {n : ℕ}

set_option hygiene false in
local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-- **Assumption C.CNe** of [cartis2022evaluation]. A set $\mathcal{C} \subseteq \mathbb{R}^n$
satisfies C.CNe if it is closed, convex and nonempty. -/
structure AssumptionCNe (C : Set ℝⁿ) : Prop where
  /-- The set $\mathcal{C}$ is closed. -/
  isClosed : IsClosed C
  /-- The set $\mathcal{C}$ is convex. -/
  convex : Convex ℝ C
  /-- The set $\mathcal{C}$ is nonempty. -/
  nonempty : C.Nonempty

/-- A set satisfies C.CNe if and only if it is closed, convex and nonempty. -/
theorem assumptionCNe_iff {C : Set ℝⁿ} :
    AssumptionCNe C ↔ IsClosed C ∧ Convex ℝ C ∧ C.Nonempty :=
  ⟨fun h => ⟨h.isClosed, h.convex, h.nonempty⟩, fun ⟨h₁, h₂, h₃⟩ => ⟨h₁, h₂, h₃⟩⟩

/-- **Section 6.1** of [cartis2022evaluation], claim that C.CNe ensures a solution, refuted. It is
not true that for every set $\mathcal{C} \subseteq \mathbb{R}^1$ that satisfies C.CNe and every
infinitely differentiable $f : \mathbb{R}^1 \to \mathbb{R}$ there is $x \in \mathcal{C}$ that
minimizes $f$ over $\mathcal{C}$.

**Correction.** The source claims at the start of Section 6.1 that C.CNe ensures that (6.1.1)
has a solution. The counterexample is $\mathcal{C} = \mathbb{R}$ and $f(x) = x$. -/
theorem not_assumptionCNe_imp_exists_minimizer :
    ¬ ∀ (C : Set (EuclideanSpace ℝ (Fin 1))) (f : EuclideanSpace ℝ (Fin 1) → ℝ),
      AssumptionCNe C → ContDiff ℝ ⊤ f → ∃ x ∈ C, IsMinOn f C x := by
  intro h
  obtain ⟨x, -, hx⟩ := h univ (fun x => x 0)
    ⟨isClosed_univ, convex_univ, univ_nonempty⟩ (by fun_prop)
  have := hx (mem_univ (x - EuclideanSpace.single 0 1))
  simp at this
  linarith

/-- **Equation (6.1.5)** of [cartis2022evaluation]. Let $f : \mathbb{R}^n \to \mathbb{R}$,
$\mathcal{C} \subseteq \mathbb{R}^n$ and $x \in \mathbb{R}^n$. The **first-order criticality
measure** is
$$\omega_{f,\mathcal{C},1}(x) = -\min_{d \in \mathcal{C}(x) \cap \mathcal{B}} \nabla^1
  f(x)[d],$$
where $\mathcal{C}(x) = \{d \mid x + d \in \mathcal{C}\}$ and $\mathcal{B}$ is the closed
Euclidean unit ball.

The minimum is the supremum `Optimization.formCriticality` of $-\nabla^1 f(x)[d]$ over
`Optimization.feasibleSteps C x`; it is $0$ if no feasible step lies in $\mathcal{B}$.

**Reading.** The original has the minus sign. The Lean supremum matches feasible minima and assigns
zero on an empty direction set.
-/
noncomputable def omega1 (f : ℝⁿ → ℝ) (C : Set ℝⁿ) (x : ℝⁿ) : ℝ :=
  Optimization.formCriticality (iteratedFDeriv ℝ 1 f x) (Optimization.feasibleSteps C x)

/-- The measure $\omega_{f,\mathcal{C},1}(x)$ is `Optimization.formCriticality` of $\nabla^1 f(x)$
over the feasible steps $\mathcal{C}(x)$.

**Reading.** Unfolds the same totalized first-order measure.
-/
theorem omega1_def (f : ℝⁿ → ℝ) (C : Set ℝⁿ) (x : ℝⁿ) :
    omega1 f C x =
      Optimization.formCriticality (iteratedFDeriv ℝ 1 f x) (Optimization.feasibleSteps C x) :=
  rfl

/-- **Equation (6.1.8)** of [cartis2022evaluation]. Let $f : \mathbb{R}^n \to \mathbb{R}$,
$\mathcal{C} \subseteq \mathbb{R}^n$, $\tau_1, \alpha \in \mathbb{R}$ and $x \in \mathbb{R}^n$.
The set of **first-order $\alpha$-restricted feasible steps** is
$$\mathcal{C}^1(x, \alpha) = \{d \in \mathcal{C}(x) \mid |\nabla^1 f(x)[d]| \le \tau_1
  \alpha\}.$$

The formula accepts all real parameters. The source uses $\tau_1\in(0,1)$ and $\alpha>0$.

**Generalization.** The printed absolute form restriction and feasibility condition extend to
arbitrary real threshold parameters.
-/
noncomputable def restrictedSteps₁ (f : ℝⁿ → ℝ) (C : Set ℝⁿ) (τ₁ α : ℝ) (x : ℝⁿ) : Set ℝⁿ :=
  Optimization.restrictedSteps (iteratedFDeriv ℝ 1 f x) (τ₁ * α) (Optimization.feasibleSteps C x)

/-- **Equation (6.1.7)** of [cartis2022evaluation]. Let $f : \mathbb{R}^n \to \mathbb{R}$,
$\mathcal{C} \subseteq \mathbb{R}^n$, $\tau_1, \alpha \in \mathbb{R}$ and $x \in \mathbb{R}^n$.
The **second-order criticality measure** is
$$\omega_{f,\mathcal{C},2}(x, \alpha) = -\min_{d \in \mathcal{C}^1(x, \alpha) \cap \mathcal{B}}
  \nabla^2 f(x)[d]^2,$$
with the restricted set $\mathcal{C}^1(x, \alpha)$ of (6.1.8).

The minimum is the supremum `Optimization.formCriticality`; it is $0$ if no step of
$\mathcal{C}^1(x, \alpha)$ lies in $\mathcal{B}$.

**Reading.** Matches the negative minimum of the Hessian quadratic form on the source domain; the
empty direction set is totalized.
-/
noncomputable def omega2 (f : ℝⁿ → ℝ) (C : Set ℝⁿ) (τ₁ : ℝ) (x : ℝⁿ) (α : ℝ) : ℝ :=
  Optimization.formCriticality (iteratedFDeriv ℝ 2 f x) (restrictedSteps₁ f C τ₁ α x)

/-- **Equation (6.1.10)** of [cartis2022evaluation]. Let $f : \mathbb{R}^n \to \mathbb{R}$,
$\mathcal{C} \subseteq \mathbb{R}^n$, $\tau_1, \tau_2, \alpha_1, \alpha_2 \in \mathbb{R}$ and
$x \in \mathbb{R}^n$. The set of **second-order $(\alpha_1, \alpha_2)$-restricted feasible
steps** is
$$\mathcal{C}^2(x, \alpha_1, \alpha_2) = \{d \in \mathcal{C}^1(x, \alpha_1) \mid |\nabla^2
  f(x)[d]^2| \le \tau_2 \alpha_2\}.$$

The formula accepts all real parameters. The source uses $\tau_2\in(0,1)$ and $\alpha_2>0$.

**Generalization.** The printed nested restriction extends to arbitrary real threshold parameters.
-/
noncomputable def restrictedSteps₂ (f : ℝⁿ → ℝ) (C : Set ℝⁿ) (τ₁ τ₂ α₁ α₂ : ℝ) (x : ℝⁿ) :
    Set ℝⁿ :=
  Optimization.restrictedSteps (iteratedFDeriv ℝ 2 f x) (τ₂ * α₂) (restrictedSteps₁ f C τ₁ α₁ x)

/-- **Equation (6.1.9)** of [cartis2022evaluation]. Let $f : \mathbb{R}^n \to \mathbb{R}$,
$\mathcal{C} \subseteq \mathbb{R}^n$, $\tau_1, \tau_2, \alpha_1, \alpha_2 \in \mathbb{R}$ and
$x \in \mathbb{R}^n$. The **third-order criticality measure** is
$$\omega_{f,\mathcal{C},3}(x, \alpha_1, \alpha_2) = -\min_{d \in \mathcal{C}^2(x, \alpha_1,
  \alpha_2) \cap \mathcal{B}} \nabla^3 f(x)[d]^3,$$
with the restricted set $\mathcal{C}^2(x, \alpha_1, \alpha_2)$ of (6.1.10).

The minimum is the supremum `Optimization.formCriticality`; it is $0$ if no step of
$\mathcal{C}^2(x, \alpha_1, \alpha_2)$ lies in $\mathcal{B}$.

**Correction.** The source claims the third-order test recovers (4.1.3) when
$\mathcal{C}=\mathbb{R}^n$ and the restricted-set thresholds are $\epsilon_1,\epsilon_2$.
For $f(u,v)=u^2/2+2v^2+4v^3/3$ at the origin, $\epsilon_2=1$ makes the unit
directions in (4.1.4) be $(\pm 1,0)$, where the third derivative vanishes.
The feasible direction $(0,-1/2)$ in the unit ball passes the same curvature
restriction and has third derivative $-1$. Equation (6.1.9) therefore fails the
test with $0<\epsilon_3<1$. -/
noncomputable def omega3 (f : ℝⁿ → ℝ) (C : Set ℝⁿ) (τ₁ τ₂ : ℝ) (x : ℝⁿ) (α₁ α₂ : ℝ) :
    ℝ :=
  Optimization.formCriticality (iteratedFDeriv ℝ 3 f x) (restrictedSteps₂ f C τ₁ τ₂ α₁ α₂ x)

/-- **Equations (6.1.4) and (6.1.6)** of [cartis2022evaluation], approximate minimizers within
$\mathcal{C}$. Let $f : \mathbb{R}^n \to \mathbb{R}$, $\mathcal{C} \subseteq \mathbb{R}^n$,
$\tau_1, \tau_2, \epsilon_1, \epsilon_2, \epsilon_3 \in \mathbb{R}$ and $q \in \mathbb{N}$. A
point $x$ is an **approximate minimizer of order $q$ of $f$ within $\mathcal{C}$** if
$x \in \mathcal{C}$ and
$$\omega_{f,\mathcal{C},1}(x) \le \epsilon_1, \qquad \omega_{f,\mathcal{C},2}(x, \epsilon_1) \le
  \epsilon_2 \ \text{ if } q \ge 2, \qquad \omega_{f,\mathcal{C},3}(x, \epsilon_1, \epsilon_2)
  \le \epsilon_3 \ \text{ if } q \ge 3.$$
For $q = 1$, $2$ and $3$ these are the first-, second- and third-order notions of Section 6.1.1
and of Step 1 of Algorithm 6.2.1.

**Reading.** The source asks for approximate minimizers "within $\mathcal{C}$"; this is the
condition $x \in \mathcal{C}$. The source switches off the higher-order tests with
$\epsilon_2 = \epsilon_3 = \infty$ (first order) or $\epsilon_3 = \infty$ (second order); here
the order $q$ is explicit instead.

**Generalization.** The predicate takes real thresholds, including zero, and any
natural order. The source uses positive tolerances and orders $1,2,3$. Here $q=0$
gives the first-order notion and $q>3$ gives the third-order notion. -/
def IsApproxMinimizerCC (f : ℝⁿ → ℝ) (C : Set ℝⁿ) (τ₁ τ₂ : ℝ) (q : ℕ) (ε₁ ε₂ ε₃ : ℝ)
    (x : ℝⁿ) : Prop :=
  x ∈ C ∧ omega1 f C x ≤ ε₁ ∧ (2 ≤ q → omega2 f C τ₁ x ε₁ ≤ ε₂) ∧
    (3 ≤ q → omega3 f C τ₁ τ₂ x ε₁ ε₂ ≤ ε₃)

variable {f : ℝⁿ → ℝ} {C : Set ℝⁿ} {x d : ℝⁿ} {τ₁ τ₂ α α₁ α₂ : ℝ}

/-- A step $d$ lies in $\mathcal{C}^1(x, \alpha)$ if and only if $x + d \in \mathcal{C}$ and
$|\nabla^1 f(x)[d]| \le \tau_1 \alpha$.

**Generalization.** Unfolds the restriction for the entire generalized parameter domain.
-/
theorem mem_restrictedSteps₁ :
    d ∈ restrictedSteps₁ f C τ₁ α x ↔
      x + d ∈ C ∧ |iteratedFDeriv ℝ 1 f x (fun _ => d)| ≤ τ₁ * α :=
  Iff.rfl

/-- A step $d$ lies in $\mathcal{C}^2(x, \alpha_1, \alpha_2)$ if and only if
$d \in \mathcal{C}^1(x, \alpha_1)$ and $|\nabla^2 f(x)[d]^2| \le \tau_2 \alpha_2$.

**Generalization.** Unfolds the second restricted set for the entire generalized parameter domain.
-/
theorem mem_restrictedSteps₂ :
    d ∈ restrictedSteps₂ f C τ₁ τ₂ α₁ α₂ x ↔
      d ∈ restrictedSteps₁ f C τ₁ α₁ x ∧ |iteratedFDeriv ℝ 2 f x (fun _ => d)| ≤ τ₂ * α₂ :=
  Iff.rfl

/-- The definition of an approximate minimizer of order $q$ within $\mathcal{C}$, unfolded:
$x \in \mathcal{C}$, $\omega_{f,\mathcal{C},1}(x) \le \epsilon_1$, $\omega_{f,\mathcal{C},2}(x,
\epsilon_1) \le \epsilon_2$ if $q \ge 2$, and $\omega_{f,\mathcal{C},3}(x, \epsilon_1,
\epsilon_2) \le \epsilon_3$ if $q \ge 3$.

**Generalization.** Unfolds the combined feasible approximate minimizer predicate with generalized
orders and threshold domains.
-/
theorem isApproxMinimizerCC_iff {q : ℕ} {ε₁ ε₂ ε₃ : ℝ} :
    IsApproxMinimizerCC f C τ₁ τ₂ q ε₁ ε₂ ε₃ x ↔
      x ∈ C ∧ omega1 f C x ≤ ε₁ ∧ (2 ≤ q → omega2 f C τ₁ x ε₁ ≤ ε₂) ∧
        (3 ≤ q → omega3 f C τ₁ τ₂ x ε₁ ε₂ ≤ ε₃) :=
  Iff.rfl

/-- If $x \in \mathcal{C}$ and $\tau_1 \alpha \ge 0$, then $0 \in \mathcal{C}^1(x, \alpha)$. -/
theorem zero_mem_restrictedSteps₁ (hx : x ∈ C) (hα : 0 ≤ τ₁ * α) :
    0 ∈ restrictedSteps₁ f C τ₁ α x :=
  (Optimization.zero_mem_restrictedSteps le_rfl hα).2 (Optimization.zero_mem_feasibleSteps.2 hx)

/-- If $x \in \mathcal{C}$, $\tau_1 \alpha_1 \ge 0$ and $\tau_2 \alpha_2 \ge 0$, then
$0 \in \mathcal{C}^2(x, \alpha_1, \alpha_2)$. -/
theorem zero_mem_restrictedSteps₂ (hx : x ∈ C) (hα₁ : 0 ≤ τ₁ * α₁) (hα₂ : 0 ≤ τ₂ * α₂) :
    0 ∈ restrictedSteps₂ f C τ₁ τ₂ α₁ α₂ x :=
  (Optimization.zero_mem_restrictedSteps one_le_two hα₂).2 (zero_mem_restrictedSteps₁ hx hα₁)

/-- If $x \in \mathcal{C}$, then $\omega_{f,\mathcal{C},1}(x) \ge 0$, as claimed after (6.1.5). -/
theorem omega1_nonneg (hx : x ∈ C) : 0 ≤ omega1 f C x :=
  Optimization.formCriticality_nonneg _ le_rfl (Optimization.zero_mem_feasibleSteps.2 hx)

/-- If $x \in \mathcal{C}$ and $\tau_1 \alpha \ge 0$, then
$\omega_{f,\mathcal{C},2}(x, \alpha) \ge 0$, as claimed after (6.1.7). -/
theorem omega2_nonneg (hx : x ∈ C) (hα : 0 ≤ τ₁ * α) : 0 ≤ omega2 f C τ₁ x α :=
  Optimization.formCriticality_nonneg _ one_le_two (zero_mem_restrictedSteps₁ hx hα)

/-- If $x \in \mathcal{C}$, $\tau_1 \alpha_1 \ge 0$ and $\tau_2 \alpha_2 \ge 0$, then
$\omega_{f,\mathcal{C},3}(x, \alpha_1, \alpha_2) \ge 0$, as claimed after (6.1.9). -/
theorem omega3_nonneg (hx : x ∈ C) (hα₁ : 0 ≤ τ₁ * α₁) (hα₂ : 0 ≤ τ₂ * α₂) :
    0 ≤ omega3 f C τ₁ τ₂ x α₁ α₂ :=
  Optimization.formCriticality_nonneg _ (by norm_num) (zero_mem_restrictedSteps₂ hx hα₁ hα₂)

/-- If $\mathcal{C}$ satisfies C.CNe and $x \in \mathcal{C}$, then the minimum in (6.1.5) is
attained: there is $d \in \mathcal{C}(x)$ with $\|d\| \le 1$ and $-\nabla^1 f(x)[d] =
\omega_{f,\mathcal{C},1}(x)$. -/
theorem exists_omega1_eq (hC : AssumptionCNe C) (hx : x ∈ C) :
    ∃ d ∈ Optimization.feasibleSteps C x ∩ closedBall 0 1,
      -iteratedFDeriv ℝ 1 f x (fun _ => d) = omega1 f C x := by
  obtain ⟨d, hd, h⟩ := Optimization.exists_formCriticality_eq (iteratedFDeriv ℝ 1 f x)
    (Optimization.isClosed_feasibleSteps hC.isClosed x)
    ⟨0, mem_closedBall_self zero_le_one, Optimization.zero_mem_feasibleSteps.2 hx⟩
  exact ⟨d, ⟨hd.2, hd.1⟩, h⟩

/-- Let $\mathcal{C}$ be convex and $x \in \mathcal{C}$. Then $\omega_{f,\mathcal{C},1}(x) = 0$ if
and only if $x$ satisfies the first-order condition (1.1.6) of Theorem 1.1.2 of
[cartis2022evaluation],
$$\langle \nabla f(x), y - x \rangle \ge 0 \quad \text{for all } y \in \mathcal{C}.$$

No differentiability is assumed: $\nabla f(x)$ is `gradient f x`, which is $0$ where $f$ is not
differentiable, and then both sides hold. -/
theorem omega1_eq_zero_iff (hC : Convex ℝ C) (hx : x ∈ C) :
    omega1 f C x = 0 ↔ ∀ y ∈ C, 0 ≤ ⟪gradient f x, y - x⟫ := by
  simp only [omega1, Optimization.formCriticality_fderiv_eq_zero_iff hC hx, gradient,
    InnerProductSpace.toDual_symm_apply]

/-- Without constraints the first-order measure is the norm of the gradient:
$\omega_{f,\mathbb{R}^n,1}(x) = \|\nabla f(x)\|$. This is the remark after (6.1.10) of
[cartis2022evaluation]. -/
theorem omega1_univ (f : ℝⁿ → ℝ) (x : ℝⁿ) : omega1 f univ x = ‖gradient f x‖ := by
  have h : Optimization.feasibleSteps (univ : Set ℝⁿ) x = univ := by
    ext; simp [Optimization.mem_feasibleSteps]
  rw [omega1, h, Optimization.formCriticality_iteratedFDeriv_one_univ,
    Optimization.norm_gradient_eq]

/-- Without constraints, $x$ is a first-order approximate minimizer within $\mathbb{R}^n$ in the
sense of (6.1.4) if and only if $\|\nabla f(x)\| \le \epsilon_1$, the unconstrained test
(2.1.2). -/
theorem isApproxMinimizerCC_one_univ_iff {ε₁ ε₂ ε₃ : ℝ} :
    IsApproxMinimizerCC f univ τ₁ τ₂ 1 ε₁ ε₂ ε₃ x ↔ ‖gradient f x‖ ≤ ε₁ := by
  simp [IsApproxMinimizerCC, omega1_univ]

end CartisGouldToint.Chapter06
