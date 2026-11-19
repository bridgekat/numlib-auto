/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Numlib.Optimization.Constrained
import Numlib.Optimization.Constrained.TargetResidual
import NumlibSurface.CartisGouldToint.Chapter01.Section01
import NumlibSurface.CartisGouldToint.Chapter06.Section01

/-!
# Cartis, Gould and Toint, Section 7.1: The general constrained problem

This module formalizes Section 7.1 of [cartis2022evaluation]. The problem is
$$\min_{x \in \mathcal{C}} f(x) \quad \text{subject to} \quad c(x) = 0 \qquad (7.1.1)$$
for $f : \mathbb{R}^n \to \mathbb{R}$, $c : \mathbb{R}^n \to \mathbb{R}^m$ and a set
$\mathcal{C} \subseteq \mathbb{R}^n$. Its Lagrangian is $\mathcal{L}(x, y) = f(x) - \langle y, c(x)
\rangle$ (1.1.1), and its feasible set is $\mathcal{F}(\mathcal{C}, c) = \{x \in \mathcal{C} \mid
c(x) = 0\}$. Theorem 7.1.1 says that a feasible minimizer of $\mathcal{L}(\cdot, y)$ minimizes $f$
over the feasible set. The first-order measure of the Lagrangian is
$\omega_{\mathcal{L},\mathcal{C},1}(x, y)$, the measure (6.1.5) of $\mathcal{L}(\cdot, y)$ over
$\mathcal{C}$. A first-order minimizer (7.1.3) has $\omega_{\mathcal{L},\mathcal{C},1}(x, y) = 0$
for some $y$, and an $(\epsilon_0, \epsilon_1)$-approximate one (7.1.4) has
$$\|c(x)\| \le \epsilon_0, \qquad \omega_{\mathcal{L},\mathcal{C},1}(x, y) \le \epsilon_1 \|(y,
  1)\|.$$

The Lagrangian is the backbone `Constrained.innerLagrangian`, and the measure is
`CartisGouldToint.Chapter06.omega1` of the Lagrangian.

## Main definitions

* Equation (1.1.1), `CartisGouldToint.Chapter07.lagrangianVec`: the Lagrangian $\mathcal{L}(x, y)$
  for vector-valued constraints.
* `CartisGouldToint.Chapter07.feasibleSet`: the feasible set $\mathcal{F}(\mathcal{S}, c)$.
* Equations (7.1.2)–(7.1.3), `CartisGouldToint.Chapter07.omegaL`: the first-order measure
  $\omega_{\mathcal{L},\mathcal{C},1}(x, y)$ of the Lagrangian.
* Equation (7.1.3), `CartisGouldToint.Chapter07.IsFirstOrderMinimizerGC`: a first-order minimizer of
  (7.1.1).
* Equation (7.1.4), `CartisGouldToint.Chapter07.IsApproxFirstOrderGC`: an
  $(\epsilon_0, \epsilon_1)$-approximate first-order minimizer of (7.1.1) with multiplier $y$.

## Main results

* Theorem 7.1.1, `CartisGouldToint.Chapter07.theorem_7_1_1`: a feasible minimizer of the Lagrangian
  over $\mathcal{S}$ minimizes $f$ over $\mathcal{F}(\mathcal{S}, c)$.
* `CartisGouldToint.Chapter07.omegaL_univ`: without the convex constraint,
  $\omega_{\mathcal{L},\mathbb{R}^n,1}(x, y) = \|\nabla f(x) - \nabla c(x)^T y\|$, the setting of
  (7.1.5).
* `CartisGouldToint.Chapter07.IsFirstOrderMinimizerGC.isApproxFirstOrderGC`: a first-order minimizer
  is an $(\epsilon_0, \epsilon_1)$-approximate one for all $\epsilon_0, \epsilon_1 \ge 0$.

## Conventions

* $\mathbb{R}^n$ and $\mathbb{R}^m$ are `EuclideanSpace ℝ (Fin n)` and `EuclideanSpace ℝ (Fin m)`.
  The transpose $\nabla c(x)^T$ is the adjoint `ContinuousLinearMap.adjoint (fderiv ℝ c x)`.
* The norm $\|(y, 1)\|$ is $\sqrt{\|y\|^2 + 1}$.

## Implementation notes

* The multiplier $y$ of (7.1.4) is an explicit argument of
  `CartisGouldToint.Chapter07.IsApproxFirstOrderGC`.

## Deviations from the source

* **Equation (7.1.1)** (generalization). The source takes $\mathcal{C}$ closed, bounded, nonempty
  and convex. The definitions and results of this section do not use these properties, and they are
  not imposed.
* **Theorem 7.1.1** (generalization). The source assumes that $\mathcal{S}$ is a closed subset of
  $\mathcal{C}$. Neither closedness nor $\mathcal{S} \subseteq \mathcal{C}$ is needed, and
  $\mathcal{C}$ does not occur in the statement. See `CartisGouldToint.Chapter07.theorem_7_1_1`.
* **Text after Theorem 7.1.1** (correction). A local minimizer over the ambient
  feasible set follows when $\mathcal{S}$ contains a relative neighborhood of $x_*$.
  The printed exclusion of the artificial boundary alone is insufficient.
* **Equation (7.1.2)** (generalization). The inherited measure is total outside
  the source's differentiability and feasibility assumptions. Its supremum over
  an empty feasible unit-ball set is zero. See `CartisGouldToint.Chapter07.omegaL`.
* **Equations (7.1.3)–(7.1.4)** (typo). The source evaluates $\mathcal{C}(x)$ and the gradient at a
  free $x$; they are evaluated at $x_*$ and $x_\epsilon$. See
  `CartisGouldToint.Chapter07.IsFirstOrderMinimizerGC` and
  `CartisGouldToint.Chapter07.IsApproxFirstOrderGC`.
* **Equation (7.1.3)** (reading). The source requires $c(x_*) = 0$ "for some $y_*$"; the feasibility
  $x_* \in \mathcal{C}$ is made explicit. See `CartisGouldToint.Chapter07.IsFirstOrderMinimizerGC`.

## Not formalized

* The heuristic perturbation argument after (7.1.5), with footnote 52, that motivates the scaling by
  $\|(y, 1)\|$.
-/

open Set
open scoped RealInnerProductSpace

namespace CartisGouldToint.Chapter07

variable {n m : ℕ}

set_option hygiene false in
local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

set_option hygiene false in
local notation "ℝᵐ" => EuclideanSpace ℝ (Fin m)

/-! ### The Lagrangian and the feasible set -/

/-- **Equation (1.1.1)** of [cartis2022evaluation], for vector-valued constraints. Let
$f : \mathbb{R}^n \to \mathbb{R}$ and $c : \mathbb{R}^n \to \mathbb{R}^m$. The **Lagrangian** at
$x \in \mathbb{R}^n$ with multiplier $y \in \mathbb{R}^m$ is
$$\mathcal{L}(x, y) = f(x) - \langle y, c(x) \rangle.$$
-/
noncomputable def lagrangianVec (f : ℝⁿ → ℝ) (c : ℝⁿ → ℝᵐ) (x : ℝⁿ) (y : ℝᵐ) : ℝ :=
  f x - ⟪y, c x⟫

variable {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {C S : Set ℝⁿ} {x : ℝⁿ} {y : ℝᵐ}

/-- The definition of the Lagrangian, unfolded: $\mathcal{L}(x, y) = f(x) - \langle y, c(x)
\rangle$. -/
theorem lagrangianVec_def : lagrangianVec f c x y = f x - ⟪y, c x⟫ := rfl

/-- The Lagrangian $\mathcal{L}(x, y)$ is the backbone Lagrangian
`Constrained.innerLagrangian f c y` evaluated at $x$. -/
theorem lagrangianVec_eq_innerLagrangian :
    lagrangianVec f c x y = Constrained.innerLagrangian f c y x := rfl

/-- The Lagrangian $\mathcal{L}(x, y)$ is the augmented Lagrangian $f(x) + \langle \lambda, c(x)
\rangle + \frac{1}{2} \alpha \|c(x)\|^2$ of `Constrained.augmented` with $\alpha = 0$ and
$\lambda = -y$. -/
theorem lagrangianVec_eq_augmented :
    lagrangianVec f c x y = Constrained.augmented f c 0 (-y) x :=
  Constrained.innerLagrangian_apply_eq_augmented f c y x

/-- The Lagrangian written componentwise: $\mathcal{L}(x, y) = f(x) - \sum_i y_i c_i(x)$, which is
`CartisGouldToint.Chapter01.lagrangian` for the components $c_i$ of $c$. -/
theorem lagrangianVec_eq_lagrangian :
    lagrangianVec f c x y = Chapter01.lagrangian f (fun i z => c z i) x (fun i => y i) := by
  simp [lagrangianVec, Chapter01.lagrangian_apply, PiLp.inner_apply, mul_comm]

/-- **Section 7.1** of [cartis2022evaluation], the feasible set. Let
$\mathcal{S} \subseteq \mathbb{R}^n$ and $c : \mathbb{R}^n \to \mathbb{R}^m$. The **feasible
set** is
$$\mathcal{F}(\mathcal{S}, c) = \{x \in \mathcal{S} \mid c(x) = 0\}.$$

**Reading.** Same feasible-set comprehension for an arbitrary ambient set.
-/
def feasibleSet (S : Set ℝⁿ) (c : ℝⁿ → ℝᵐ) : Set ℝⁿ := {x ∈ S | c x = 0}

/-- A point lies in $\mathcal{F}(\mathcal{S}, c)$ if and only if $x \in \mathcal{S}$ and $c(x) = 0$.

**Reading.** Unfolds membership for an arbitrary ambient set.
-/
theorem mem_feasibleSet : x ∈ feasibleSet S c ↔ x ∈ S ∧ c x = 0 := Iff.rfl

/-- The feasible set $\mathcal{F}(\mathcal{S}, c)$ is a subset of $\mathcal{S}$. -/
theorem feasibleSet_subset : feasibleSet S c ⊆ S := fun _ hx => hx.1

/-- **Theorem 7.1.1** of [cartis2022evaluation] (local sufficiency of the Lagrangian). Let
$f : \mathbb{R}^n \to \mathbb{R}$, $c : \mathbb{R}^n \to \mathbb{R}^m$,
$\mathcal{S} \subseteq \mathbb{R}^n$, $x_* \in \mathcal{S}$ and $y_* \in \mathbb{R}^m$. If $x_*$
minimizes $\mathcal{L}(\cdot, y_*)$ over $\mathcal{S}$ and $c(x_*) = 0$, then
$x_* \in \mathcal{F}(\mathcal{S}, c)$ and $x_*$ minimizes $f$ over
$\mathcal{F}(\mathcal{S}, c)$.

**Generalization.** The source assumes that $\mathcal{S}$ is a closed subset of $\mathcal{C}$.
Neither closedness nor $\mathcal{S} \subseteq \mathcal{C}$ is needed, and $\mathcal{C}$ does not
occur in the statement.

**Correction.** The subsequent local-optimality claim needs a relative neighborhood
of $x_*$ in $\mathcal{C}$. With $\mathcal{C}=[0,1]$, $\mathcal{S}=\{0\}$, $c=0$ and
$f(x)=-x$, the point $0$ lies outside $\partial\mathcal{S}\setminus\partial\mathcal{C}$.
It minimizes the Lagrangian over $\mathcal{S}$ and fails to minimize $f$ locally in
$\mathcal{F}(\mathcal{C},c)$. -/
theorem theorem_7_1_1 (hx : x ∈ S) (hmin : IsMinOn (fun z => lagrangianVec f c z y) S x)
    (hc : c x = 0) : x ∈ feasibleSet S c ∧ IsMinOn f (feasibleSet S c) x :=
  ⟨⟨hx, hc⟩, Constrained.isMinOn_of_isMinOn_sub_inner hc hmin⟩

/-! ### First-order measures and minimizers -/

/-- **Equations (7.1.2)–(7.1.3)** of [cartis2022evaluation]. Let $f : \mathbb{R}^n \to \mathbb{R}$,
$c : \mathbb{R}^n \to \mathbb{R}^m$, $\mathcal{C} \subseteq \mathbb{R}^n$, $x \in \mathbb{R}^n$
and $y \in \mathbb{R}^m$. The **first-order criticality measure of the Lagrangian** is the
measure (7.1.2) of $h = \mathcal{L}(\cdot, y)$,
$$\omega_{\mathcal{L},\mathcal{C},1}(x, y) = -\min_{d \in \mathcal{C}(x) \cap \mathcal{B}}
  \nabla_x^1 \mathcal{L}(x, y)[d].$$

The measure is `CartisGouldToint.Chapter06.omega1` of $\mathcal{L}(\cdot, y)$.
The source evaluates it on feasible points for a differentiable Lagrangian.
The Lean definition is total and gives zero when the feasible direction set inside
the unit ball is empty. Its nonnegativity theorem assumes $x\in\mathcal{C}$.

**Generalization.** Substitutes the Lagrangian for the objective and extends the supremum and
derivative conventions beyond the source domain.
-/
noncomputable def omegaL (f : ℝⁿ → ℝ) (c : ℝⁿ → ℝᵐ) (C : Set ℝⁿ) (x : ℝⁿ) (y : ℝᵐ) : ℝ :=
  Chapter06.omega1 (fun z => lagrangianVec f c z y) C x

/-- The measure $\omega_{\mathcal{L},\mathcal{C},1}(x, y)$ is the first-order measure
$\omega_{h,\mathcal{C},1}(x)$ of (6.1.5) for $h = \mathcal{L}(\cdot, y)$.

**Reading.** Unfolds the same totalized first-order Lagrangian quantity.
-/
theorem omegaL_def :
    omegaL f c C x y = Chapter06.omega1 (fun z => lagrangianVec f c z y) C x := rfl

/-- If $x \in \mathcal{C}$, then $\omega_{\mathcal{L},\mathcal{C},1}(x, y) \ge 0$. -/
theorem omegaL_nonneg (hx : x ∈ C) : 0 ≤ omegaL f c C x y :=
  Chapter06.omega1_nonneg hx

/-- Let $f$ and $c$ be differentiable at $x$. Then the gradient of the Lagrangian in $x$ is
$$\nabla_x \mathcal{L}(x, y) = \nabla f(x) - \nabla c(x)^T y,$$
where the transpose $\nabla c(x)^T$ is the adjoint of the derivative of $c$ at $x$. -/
theorem gradient_lagrangianVec (hf : DifferentiableAt ℝ f x) (hc : DifferentiableAt ℝ c x) :
    gradient (fun z => lagrangianVec f c z y) x =
      gradient f x - ContinuousLinearMap.adjoint (fderiv ℝ c x) y := by
  refine HasGradientAt.gradient ?_
  rw [hasGradientAt_iff_hasFDerivAt]
  refine (Constrained.hasFDerivAt_sub_inner y hf.hasFDerivAt hc.hasFDerivAt).congr_fderiv ?_
  ext v
  have hg := hf.hasGradientAt
  rw [hasGradientAt_iff_hasFDerivAt] at hg
  rw [hg.fderiv]
  simp [ContinuousLinearMap.adjoint_inner_left]

/-- Let $f$ and $c$ be differentiable at $x$. Without the convex constraint, the measure (7.1.2) of
the Lagrangian is the norm of its gradient,
$$\omega_{\mathcal{L},\mathbb{R}^n,1}(x, y) = \|\nabla f(x) - \nabla c(x)^T y\|.$$
This is the setting of (7.1.5) of [cartis2022evaluation]. -/
theorem omegaL_univ (hf : DifferentiableAt ℝ f x) (hc : DifferentiableAt ℝ c x) :
    omegaL f c univ x y = ‖gradient f x - ContinuousLinearMap.adjoint (fderiv ℝ c x) y‖ := by
  rw [omegaL, Chapter06.omega1_univ, gradient_lagrangianVec hf hc]

/-- **Equation (7.1.3)** of [cartis2022evaluation]. Let $f : \mathbb{R}^n \to \mathbb{R}$,
$c : \mathbb{R}^n \to \mathbb{R}^m$ and $\mathcal{C} \subseteq \mathbb{R}^n$. A point $x_*$ is a
**first-order minimizer** of (7.1.1) if $x_* \in \mathcal{C}$, $c(x_*) = 0$, and
$\omega_{\mathcal{L},\mathcal{C},1}(x_*, y_*) = 0$ for some multiplier $y_* \in \mathbb{R}^m$.

**Typo.** The source evaluates $\mathcal{C}(x)$ and the gradient at a free $x$; here they are
evaluated at $x_*$.

**Reading.** The source requires $c(x_*) = 0$ "for some $y_*$"; the feasibility
$x_* \in \mathcal{C}$ is made explicit. -/
def IsFirstOrderMinimizerGC (f : ℝⁿ → ℝ) (c : ℝⁿ → ℝᵐ) (C : Set ℝⁿ) (x : ℝⁿ) : Prop :=
  x ∈ C ∧ c x = 0 ∧ ∃ y, omegaL f c C x y = 0

/-- The definition of a first-order minimizer, unfolded: $x \in \mathcal{C}$, $c(x) = 0$, and
$\omega_{\mathcal{L},\mathcal{C},1}(x, y) = 0$ for some $y$.

**Correction.** Unfolds the corrected first-order conditions.
-/
theorem isFirstOrderMinimizerGC_iff :
    IsFirstOrderMinimizerGC f c C x ↔ x ∈ C ∧ c x = 0 ∧ ∃ y, omegaL f c C x y = 0 :=
  Iff.rfl

/-- **Equation (7.1.4)** of [cartis2022evaluation]. Let $f : \mathbb{R}^n \to \mathbb{R}$,
$c : \mathbb{R}^n \to \mathbb{R}^m$, $\mathcal{C} \subseteq \mathbb{R}^n$ and
$\epsilon_0, \epsilon_1 \in \mathbb{R}$. A point $x_\epsilon$ is an
**$(\epsilon_0, \epsilon_1)$-approximate first-order minimizer** of $f$ within
$\mathcal{F}(\mathcal{C}, c)$, with multiplier $y \in \mathbb{R}^m$, if
$x_\epsilon \in \mathcal{C}$ and
$$\|c(x_\epsilon)\| \le \epsilon_0, \qquad \omega_{\mathcal{L},\mathcal{C},1}(x_\epsilon, y) \le
  \epsilon_1 \|(y, 1)\|, \qquad \text{where } \|(y, 1)\| = \sqrt{\|y\|^2 + 1}.$$

**Typo.** The source evaluates $\mathcal{C}(x)$ and the gradient at a free $x$; here they are
evaluated at $x_\epsilon$.

The multiplier $y$ is an explicit argument. Quantifying existentially over $y$
gives the source condition. The real tolerance arguments also allow zero. -/
def IsApproxFirstOrderGC (f : ℝⁿ → ℝ) (c : ℝⁿ → ℝᵐ) (C : Set ℝⁿ) (ε₀ ε₁ : ℝ) (x : ℝⁿ)
    (y : ℝᵐ) : Prop :=
  x ∈ C ∧ ‖c x‖ ≤ ε₀ ∧ omegaL f c C x y ≤ ε₁ * √(‖y‖ ^ 2 + 1)

/-- The definition of an approximate first-order minimizer, unfolded: $x \in \mathcal{C}$,
$\|c(x)\| \le \epsilon_0$ and $\omega_{\mathcal{L},\mathcal{C},1}(x, y) \le \epsilon_1
\sqrt{\|y\|^2 + 1}$.

**Reading.** Unfolds the witness-specific feasibility and scaled stationarity inequalities.
-/
theorem isApproxFirstOrderGC_iff {ε₀ ε₁ : ℝ} :
    IsApproxFirstOrderGC f c C ε₀ ε₁ x y ↔
      x ∈ C ∧ ‖c x‖ ≤ ε₀ ∧ omegaL f c C x y ≤ ε₁ * √(‖y‖ ^ 2 + 1) :=
  Iff.rfl

/-- Let $\epsilon_0, \epsilon_1 \ge 0$. A first-order minimizer of (7.1.1) is an
$(\epsilon_0, \epsilon_1)$-approximate first-order minimizer for some multiplier $y$; the
multiplier of the first-order condition serves. -/
theorem IsFirstOrderMinimizerGC.isApproxFirstOrderGC {ε₀ ε₁ : ℝ}
    (h : IsFirstOrderMinimizerGC f c C x) (hε₀ : 0 ≤ ε₀) (hε₁ : 0 ≤ ε₁) :
    ∃ y, IsApproxFirstOrderGC f c C ε₀ ε₁ x y := by
  obtain ⟨hx, hc, y, hy⟩ := h
  exact ⟨y, hx, by simpa [hc] using hε₀, hy ▸ mul_nonneg hε₁ (Real.sqrt_nonneg _)⟩

end CartisGouldToint.Chapter07
