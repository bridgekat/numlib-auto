/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Numlib.Optimization.Constrained.SecondOrder
import Numlib.Optimization.Optimality.Approximate
import Numlib.Optimization.Optimality.ConvexSet

/-!
# Cartis, Gould and Toint, Section 1.1: Nonlinear optimization and optimality conditions

This module formalizes §1.1 of [cartis2022evaluation]: the problem classes of the book and their
optimality conditions. It treats the unconstrained problem $\min f(x)$ (Theorem 1.1.1), minimization
over a closed convex set $\mathcal{C}$ (Theorem 1.1.2), and minimization subject to equality
constraints $c(x) = 0$ (Theorem 1.1.3) or inequality constraints $c(x) \ge 0$ (Theorem 1.1.4), with
the Lagrangian $\mathcal{L}(x, y) = f(x) - \sum_i y_i c_i(x)$ of (1.1.1). It also defines the
criticality measures $\omega_1(x) = \|\nabla f(x)\|$ and $\omega_2(x) = \max(0,
-\lambda_{\min}[\nabla^2 f(x)])$ of §1.1.2.6. The proofs specialize the backbone modules
`Numlib.Optimization.Constrained.SecondOrder`, `Numlib.Optimization.Optimality.Approximate` and
`Numlib.Optimization.Optimality.ConvexSet`.

## Main definitions

* Equation (1.1.1), `CartisGouldToint.Chapter01.lagrangian`: the Lagrangian
  $\mathcal{L}(x, y) = f(x) - \sum_i y_i c_i(x)$.
* Section 1.1.2.5, `CartisGouldToint.Chapter01.activeSet`: the active set
  $\mathcal{A}(x) = \{i : c_i(x) = 0\}$.
* Equation (1.1.7), `CartisGouldToint.Chapter01.feasibleDirections`: the set
  $\mathcal{C}(x) = \{d : x + d \in \mathcal{C}\}$ of feasible displacements.
* Theorems 1.1.3 and 1.1.4, `CartisGouldToint.Chapter01.licq`: the linear independence constraint
  qualification, which is used for "a constraint qualification".
* Equation (1.1.5), `CartisGouldToint.Chapter01.hessianMinEig`: the least eigenvalue
  $\lambda_{\min}[\nabla^2 f(x)]$ of the Hessian.
* Section 1.1.2.6, `CartisGouldToint.Chapter01.omega₁` and `CartisGouldToint.Chapter01.omega₂`: the
  criticality measures $\omega_1$ and $\omega_2$.
* Equation (1.1.16), `CartisGouldToint.Chapter01.IsKKTPair`: the first-order conditions for
  inequality constraints.
* Equation (1.1.17), `CartisGouldToint.Chapter01.criticalConeN`: the cone $\mathcal{N}_+$.

## Main results

* Section 1.1.2.1, `CartisGouldToint.Chapter01.gradient_lagrangian` and
  `CartisGouldToint.Chapter01.iteratedFDeriv_two_lagrangian`: the gradient and the Hessian of the
  Lagrangian.
* Theorem 1.1.1, `CartisGouldToint.Chapter01.theorem_1_1_1_i` to
  `CartisGouldToint.Chapter01.theorem_1_1_1_iv`: the first-, second- and third-order necessary
  conditions and the second-order sufficient condition for unconstrained problems.
* Equation (1.1.5), `CartisGouldToint.Chapter01.omega_eq_zero_iff`: $\omega_1(x) = \omega_2(x) = 0$
  if and only if $\nabla f(x) = 0$ and $\nabla^2 f(x)$ is positive semidefinite.
* Theorem 1.1.2, `CartisGouldToint.Chapter01.theorem_1_1_2_i` to
  `CartisGouldToint.Chapter01.theorem_1_1_2_iv`: the necessary conditions and a corrected sufficient
  condition for minimization over a closed convex set.
* Theorem 1.1.2, `CartisGouldToint.Chapter01.theorem_1_1_2_iv_counterexample`: the printed
  sufficient condition is false.
* Theorem 1.1.3, `CartisGouldToint.Chapter01.theorem_1_1_3_i` to
  `CartisGouldToint.Chapter01.theorem_1_1_3_iii`: the optimality conditions for equality
  constraints.
* Theorem 1.1.4, `CartisGouldToint.Chapter01.theorem_1_1_4_i` to
  `CartisGouldToint.Chapter01.theorem_1_1_4_iii`: the optimality conditions for inequality
  constraints.

## Conventions

* Points are in $\mathbb{R}^n$, which is `EuclideanSpace ℝ (Fin n)`. The constraint map
  $c : \mathbb{R}^n \to \mathbb{R}^m$ is given by its components
  `c : Fin m → EuclideanSpace ℝ (Fin n) → ℝ`, and multipliers are `y : Fin m → ℝ`.
* The book's $f \in C^p$ is `ContDiff ℝ p f`, and $f \in C^p(\mathcal{S})$ for an open set
  $\mathcal{S}$ is `ContDiffOn ℝ p f 𝒮`.
* The second-order term $\langle d, \nabla^2 f(x) d\rangle$ is
  `iteratedFDeriv ℝ 2 f x (fun _ => d)`, and similarly for the third-order term.
* Local minimizers are `IsLocalMin` and `IsLocalMinOn` of Mathlib. Strict local minimizers are
  `Optimization.IsStrictLocalMin` and `Optimization.IsStrictLocalMinOn`.

## Implementation notes

* In the third-order condition of Theorem 1.1.1, the book's hypothesis $\nabla^2 f(x^*) d = 0$ is
  written as $\nabla^2 f(x^*)[d, w] = 0$ for all $w$.

## Deviations from the source

* **Theorem 1.1.2, sufficient condition** (correction). The printed condition, strict curvature on
  the nonzero $d \in \mathcal{C}(x^*)$ with $\langle d, \nabla f(x^*)\rangle = 0$, is not
  sufficient. The condition is stated on the tangent cone of $\mathcal{C}$ at $x^*$ instead; the two
  coincide for polyhedral $\mathcal{C}$. See `CartisGouldToint.Chapter01.theorem_1_1_2_iv` and
  `CartisGouldToint.Chapter01.theorem_1_1_2_iv_counterexample`.
* **Theorems 1.1.3 and 1.1.4, sufficient conditions (1.1.15) and (1.1.18)** (typo). The book
  quantifies over all $d$ of the relevant cone, including $d = 0$, for which the strict inequality
  fails; the conditions are stated for $d \neq 0$. See
  `CartisGouldToint.Chapter01.theorem_1_1_3_iii` and `CartisGouldToint.Chapter01.theorem_1_1_4_iii`.
* **Theorems 1.1.3 and 1.1.4, constraint qualification** (reading). The book leaves the constraint
  qualification unspecified; LICQ is used. See `CartisGouldToint.Chapter01.licq`.
* **Theorems 1.1.3 and 1.1.4, second-order necessary conditions** (generalization). The conditions
  (1.1.14) and (1.1.17) are proved for every multiplier vector that satisfies the first-order
  conditions; under LICQ there is exactly one. See `CartisGouldToint.Chapter01.theorem_1_1_3_ii` and
  `CartisGouldToint.Chapter01.theorem_1_1_4_ii`.

## Not formalized

* **The tensor-product notation (1.1.2).** `iteratedFDeriv` applied to vectors is used instead.
* **Equations (1.1.10)–(1.1.12) and (1.1.19)**, the equivalent forms with a minimum over
  $\mathcal{C}(x^*) \cap \{\|d\| \le 1\}$.
* **The projection form of (1.1.6)**, $\|P_{\mathcal{C}}[x^* - \nabla f(x^*)] - x^*\| = 0$.
* **The reduced-Hessian form of (1.1.14)–(1.1.15).**
* **The hardness remarks** on the optimality conditions.
-/

open Set Filter Topology
open scoped RealInnerProductSpace

namespace CartisGouldToint.Chapter01

variable {n m : ℕ}

/-! ### Gradients -/

section Gradient

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}

/-- For $f : \mathbb{R}^n \to \mathbb{R}$ and $x, d \in \mathbb{R}^n$,
$\langle d, \nabla f(x)\rangle = Df(x)[d]$. -/
private theorem inner_gradient (f : EuclideanSpace ℝ (Fin n) → ℝ) (x d : EuclideanSpace ℝ (Fin n)) :
    ⟪d, gradient f x⟫ = fderiv ℝ f x d := by
  rw [real_inner_comm, gradient, InnerProductSpace.toDual_symm_apply]

/-- The gradient $\nabla f(x)$ is $0$ if and only if the derivative $Df(x)$ is $0$. -/
theorem gradient_eq_zero_iff : gradient f x = 0 ↔ fderiv ℝ f x = 0 := by
  simp [gradient]

/-- A family of gradients $\nabla \varphi_i(x)$ is linearly independent if and only if the family of
derivatives $D\varphi_i(x)$ is linearly independent. -/
theorem linearIndependent_gradient_iff {ι : Type*} (φ : ι → EuclideanSpace ℝ (Fin n) → ℝ) :
    LinearIndependent ℝ (fun i => gradient (φ i) x) ↔
      LinearIndependent ℝ (fun i => fderiv ℝ (φ i) x) := by
  let e : StrongDual ℝ (EuclideanSpace ℝ (Fin n)) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.toLinearEquiv
  exact e.toLinearMap.linearIndependent_iff_of_injOn e.injective.injOn

end Gradient

/-! ### The Lagrangian -/

section Lagrangian

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {c : Fin m → EuclideanSpace ℝ (Fin n) → ℝ}
  {x : EuclideanSpace ℝ (Fin n)} {y : Fin m → ℝ}

/-- **Equation (1.1.1)** of [cartis2022evaluation]. For $f : \mathbb{R}^n \to \mathbb{R}$,
constraints $c_1, \dots, c_m : \mathbb{R}^n \to \mathbb{R}$, $x \in \mathbb{R}^n$ and
$y \in \mathbb{R}^m$, the **Lagrangian** is
$$\mathcal{L}(x, y) = f(x) - \sum_{i=1}^m y_i c_i(x).$$
-/
def lagrangian (f : EuclideanSpace ℝ (Fin n) → ℝ) (c : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (y : Fin m → ℝ) : ℝ :=
  f x - ∑ i, y i * c i x

/-- The Lagrangian is $\mathcal{L}(x, y) = f(x) - \sum_i y_i c_i(x)$. -/
theorem lagrangian_apply : lagrangian f c x y = f x - ∑ i, y i * c i x := rfl

/-- The Lagrangian of the book is the backbone Lagrangian $f + \sum_i \lambda_i c_i$,
`Constrained.lagrangian`, with the multipliers $\lambda = -y$. -/
theorem lagrangian_eq_constrained_lagrangian :
    lagrangian f c x y = Constrained.lagrangian f c x (-y) := by
  simp [lagrangian, Constrained.lagrangian_apply, Finset.sum_neg_distrib, sub_eq_add_neg]

/-- The Lagrangian of the book is the Lagrangian `Constrained.kktLagrangian` of the problem with the
inequality constraints $-c_i \le 0$ and the multipliers $y$, without equality constraints. -/
theorem kktLagrangian_eq_lagrangian (l : Empty → ℝ) :
    Constrained.kktLagrangian f (fun i : Empty => i.elim) (fun i => -c i) l y =
      fun z => lagrangian f c z y := by
  funext z
  simp [Constrained.kktLagrangian_apply, lagrangian, Finset.sum_neg_distrib, sub_eq_add_neg]

/-- The Lagrangian of the book is the Lagrangian `Constrained.kktLagrangian` of the problem with the
equality constraints $c_i = 0$ and the multipliers $-y$, without inequality constraints. -/
theorem kktLagrangian_eq_lagrangian_of_eq (g : Empty → EuclideanSpace ℝ (Fin n) → ℝ)
    (μ : Empty → ℝ) :
    Constrained.kktLagrangian f c g (-y) μ = fun z => lagrangian f c z y := by
  rw [Constrained.kktLagrangian_of_isEmpty]
  funext z
  rw [lagrangian_eq_constrained_lagrangian]

/-- If $f$ has the derivative $f'$ at $x$ and each $c_i$ has the derivative $c_i'$ at $x$, then
$z \mapsto \mathcal{L}(z, y)$ has the derivative $f' - \sum_i y_i c_i'$ at $x$. -/
theorem hasFDerivAt_lagrangian {f' : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ}
    {c' : Fin m → EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ} (hf : HasFDerivAt f f' x)
    (hc : ∀ i, HasFDerivAt (c i) (c' i) x) (y : Fin m → ℝ) :
    HasFDerivAt (fun z => lagrangian f c z y) (f' - ∑ i, y i • c' i) x :=
  hf.sub (HasFDerivAt.fun_sum fun i _ => (hc i).const_mul (y i))

/-- The gradient of the Lagrangian ([cartis2022evaluation], §1.1.2.1). If $f$ and all $c_i$ are
differentiable at $x$, then
$$\nabla_x \mathcal{L}(x, y) = \nabla f(x) - \sum_i y_i \nabla c_i(x).$$
-/
theorem gradient_lagrangian (hf : DifferentiableAt ℝ f x)
    (hc : ∀ i, DifferentiableAt ℝ (c i) x) (y : Fin m → ℝ) :
    gradient (fun z => lagrangian f c z y) x = gradient f x - ∑ i, y i • gradient (c i) x := by
  refine ext_inner_right ℝ fun d => ?_
  rw [inner_gradient_left, (hasFDerivAt_lagrangian hf.hasFDerivAt (fun i => (hc i).hasFDerivAt)
    y).fderiv, inner_sub_left, sum_inner, inner_gradient_left]
  simp [inner_smul_left]

/-- If $f$ and all $c_i$ are differentiable at $x$, then $\nabla_x \mathcal{L}(x, y) = 0$ if and
only if $Df(x) - \sum_i y_i Dc_i(x) = 0$. -/
theorem gradient_lagrangian_eq_zero_iff (hf : DifferentiableAt ℝ f x)
    (hc : ∀ i, DifferentiableAt ℝ (c i) x) :
    gradient (fun z => lagrangian f c z y) x = 0 ↔
      fderiv ℝ f x - ∑ i, y i • fderiv ℝ (c i) x = 0 := by
  rw [gradient_eq_zero_iff,
    (hasFDerivAt_lagrangian hf.hasFDerivAt (fun i => (hc i).hasFDerivAt) y).fderiv]

/-- The Hessian of the Lagrangian ([cartis2022evaluation], §1.1.2.1). If $f$ and all $c_i$ are twice
continuously differentiable at $x$, then
$$\nabla_{xx}^2 \mathcal{L}(x, y) = \nabla^2 f(x) - \sum_i y_i \nabla^2 c_i(x).$$
-/
theorem iteratedFDeriv_two_lagrangian (hf : ContDiffAt ℝ 2 f x)
    (hc : ∀ i, ContDiffAt ℝ 2 (c i) x) (y : Fin m → ℝ) :
    iteratedFDeriv ℝ 2 (fun z => lagrangian f c z y) x =
      iteratedFDeriv ℝ 2 f x - ∑ i, y i • iteratedFDeriv ℝ 2 (c i) x := by
  have e : (fun z => lagrangian f c z y) = f - ∑ i, y i • c i := by
    funext z
    simp [lagrangian, Finset.sum_apply]
  have hs : ContDiffAt ℝ 2 (∑ i, y i • c i) x := by
    rw [Finset.sum_fn]
    exact ContDiffAt.sum fun i _ => (hc i).const_smul (y i)
  rw [e, iteratedFDeriv_sub_apply hf hs,
    iteratedFDeriv_sum_apply (f := fun i => y i • c i) fun i _ => (hc i).const_smul (y i)]
  congr 1
  exact Finset.sum_congr rfl fun i _ => iteratedFDeriv_const_smul_apply (hc i)

end Lagrangian

/-! ### Active set, feasible directions, constraint qualification -/

section Sets

variable {c : Fin m → EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}

/-- **Section 1.1.2.5** of [cartis2022evaluation], the active set. For constraints $c_1, \dots, c_m$
and $x \in \mathbb{R}^n$, the **active set** is $\mathcal{A}(x) = \{i : c_i(x) = 0\}$. -/
def activeSet (c : Fin m → EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    Set (Fin m) :=
  {i | c i x = 0}

/-- An index $i$ is in the active set $\mathcal{A}(x)$ if and only if $c_i(x) = 0$. -/
@[simp]
theorem mem_activeSet {i : Fin m} : i ∈ activeSet c x ↔ c i x = 0 := Iff.rfl

/-- The active set of the constraints $c_i \ge 0$ is the backbone active set `Constrained.activeSet`
of the constraints $-c_i \le 0$. -/
theorem activeSet_eq_constrained_activeSet :
    activeSet c x = Constrained.activeSet (fun i => -c i) x := by
  ext i
  simp

/-- **Equation (1.1.7)** of [cartis2022evaluation]. For $\mathcal{C} \subseteq \mathbb{R}^n$ and
$x \in \mathbb{R}^n$, the set of **feasible displacements** is
$\mathcal{C}(x) = \{d : x + d \in \mathcal{C}\}$. -/
def feasibleDirections (C : Set (EuclideanSpace ℝ (Fin n))) (x : EuclideanSpace ℝ (Fin n)) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {d | x + d ∈ C}

/-- A vector $d$ is in $\mathcal{C}(x)$ if and only if $x + d \in \mathcal{C}$. -/
@[simp]
theorem mem_feasibleDirections {C : Set (EuclideanSpace ℝ (Fin n))} {d : EuclideanSpace ℝ (Fin n)} :
    d ∈ feasibleDirections C x ↔ x + d ∈ C := Iff.rfl

/-- **Theorems 1.1.3 and 1.1.4** of [cartis2022evaluation], the constraint qualification. The
**linear independence constraint qualification** (LICQ) holds at $x$ if the gradients
$\nabla c_i(x)$ of the active constraints $i \in \mathcal{A}(x)$ are linearly independent.

**Reading.** The book requires "a constraint qualification" in Theorems 1.1.3 and 1.1.4 without
saying which one; LICQ is used.

For equality constraints at a feasible point every constraint is active; see
`CartisGouldToint.Chapter01.licq_iff_of_forall_eq_zero`. -/
def licq (c : Fin m → EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  LinearIndependent ℝ (fun i : activeSet c x => gradient (c i) x)

/-- If $c_i(x) = 0$ for all $i$, then LICQ holds at $x$ if and only if all the gradients
$\nabla c_i(x)$ are linearly independent. -/
theorem licq_iff_of_forall_eq_zero (hx : ∀ i, c i x = 0) :
    licq c x ↔ LinearIndependent ℝ (fun i => gradient (c i) x) :=
  linearIndependent_equiv (Equiv.subtypeUnivEquiv hx)
    (f := fun i => gradient (c i) x)

/-- If $c_i(x) = 0$ for all $i$, then LICQ holds at $x$ if and only if $x$ is a regular point of the
equality constraints $c = 0$ in the sense of the backbone, `Constrained.IsRegularPoint`. -/
theorem licq_iff_isRegularPoint (hx : ∀ i, c i x = 0) :
    licq c x ↔ Constrained.IsRegularPoint c (fun i => fderiv ℝ (c i)) x := by
  rw [licq_iff_of_forall_eq_zero hx, linearIndependent_gradient_iff]
  exact ⟨fun h => ⟨hx, h⟩, fun h => h.2⟩

/-- If $c_i(x) \ge 0$ for all $i$, then LICQ holds at $x$ if and only if $x$ is a regular point of
the inequality constraints $-c_i \le 0$, without equality constraints, in the sense of the
backbone, `Constrained.IsRegularPointIneq`. -/
theorem licq_iff_isRegularPointIneq (hx : ∀ i, 0 ≤ c i x) :
    licq c x ↔ Constrained.IsRegularPointIneq (fun i : Empty => i.elim)
      (fun i : Empty => i.elim) (fun i => -c i) (fun i z => -fderiv ℝ (c i) z) x := by
  have hsum : (Sum.elim (fun i : Empty =>
      (i.elim : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) x)
      fun j : Constrained.activeSet (fun i => -c i) x => -fderiv ℝ (c j) x) =
      (fun j : activeSet c x => -fderiv ℝ (c j) x) ∘
        ((Equiv.emptySum Empty _).trans
          (Equiv.subtypeEquivRight fun j => by simp)) := by
    funext s
    rcases s with i | j
    · exact i.elim
    · rfl
  have e : licq c x ↔ LinearIndependent ℝ (fun j : activeSet c x => -fderiv ℝ (c j) x) := by
    rw [licq, linearIndependent_gradient_iff]
    exact (linearIndependent_neg_iff (v := fun j : activeSet c x => fderiv ℝ (c j) x)).symm
  rw [e, Constrained.isRegularPointIneq_iff, hsum, linearIndependent_equiv]
  simp [hx]

end Sets

/-! ### Theorem 1.1.1: unconstrained problems -/

section Unconstrained

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}

/-- **Theorem 1.1.1** of [cartis2022evaluation], first-order condition (1.1.4). Let
$f : \mathbb{R}^n \to \mathbb{R}$ be continuously differentiable, and let $x^*$ be a local
minimizer of $f$. Then $\nabla f(x^*) = 0$. -/
theorem theorem_1_1_1_i (_hf : ContDiff ℝ 1 f) (hmin : IsLocalMin f x) : gradient f x = 0 :=
  gradient_eq_zero_iff.2 hmin.fderiv_eq_zero

/-- **Theorem 1.1.1** of [cartis2022evaluation], second-order condition. Let
$f : \mathbb{R}^n \to \mathbb{R}$ be twice continuously differentiable, and let $x^*$ be a local
minimizer of $f$. Then $\nabla^2 f(x^*)$ is positive semidefinite:
$\langle d, \nabla^2 f(x^*) d\rangle \ge 0$ for all $d \in \mathbb{R}^n$.

Equivalently, $\lambda_{\min}[\nabla^2 f(x^*)] \ge 0$; see
`CartisGouldToint.Chapter01.hessianMinEig_nonneg_iff`. -/
theorem theorem_1_1_1_ii (hf : ContDiff ℝ 2 f) (hmin : IsLocalMin f x)
    (d : EuclideanSpace ℝ (Fin n)) : 0 ≤ iteratedFDeriv ℝ 2 f x (fun _ => d) :=
  hmin.iteratedFDeriv_two_apply_self_nonneg hf.contDiffAt d

/-- **Theorem 1.1.1** of [cartis2022evaluation], third-order condition. Let
$f : \mathbb{R}^n \to \mathbb{R}$ be three times continuously differentiable, let $x^*$ be a
local minimizer of $f$, and let $d \in \mathbb{R}^n$ with $\nabla^2 f(x^*) d = 0$. Then
$\nabla^3 f(x^*)[d]^3 = 0$.

The hypothesis $\nabla^2 f(x^*) d = 0$ is written as $\nabla^2 f(x^*)[d, w] = 0$ for all
$w \in \mathbb{R}^n$. -/
theorem theorem_1_1_1_iii (hf : ContDiff ℝ 3 f) (hmin : IsLocalMin f x)
    {d : EuclideanSpace ℝ (Fin n)} (hd : ∀ w, iteratedFDeriv ℝ 2 f x ![d, w] = 0) :
    iteratedFDeriv ℝ 3 f x (fun _ => d) = 0 :=
  Optimization.IsLocalMin.iteratedFDeriv_three_eq_zero hmin hf.contDiffAt
    ((apply_diag_eq_vec _ d).trans (hd d))

/-- **Theorem 1.1.1** of [cartis2022evaluation], sufficient condition. Let
$f : \mathbb{R}^n \to \mathbb{R}$ be twice continuously differentiable, and let
$x^* \in \mathbb{R}^n$ with $\nabla f(x^*) = 0$ and $\langle d, \nabla^2 f(x^*) d\rangle > 0$
for all $d \neq 0$. Then $x^*$ is a strict local minimizer of $f$. -/
theorem theorem_1_1_1_iv (hf : ContDiff ℝ 2 f) (hgrad : gradient f x = 0)
    (hpos : ∀ d, d ≠ 0 → 0 < iteratedFDeriv ℝ 2 f x (fun _ => d)) :
    Optimization.IsStrictLocalMin f x :=
  Optimization.isStrictLocalMin_of_fderiv_eq_zero_of_posDef hf.contDiffAt
    (gradient_eq_zero_iff.1 hgrad) hpos

end Unconstrained

/-! ### The least eigenvalue of the Hessian and criticality measures -/

section Measures

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}

/-- **Equation (1.1.5)** of [cartis2022evaluation], the least eigenvalue of the Hessian. For
$f : \mathbb{R}^n \to \mathbb{R}$ and $x \in \mathbb{R}^n$,
$$\lambda_{\min}[\nabla^2 f(x)] = \inf_{\|d\| = 1} \langle d, \nabla^2 f(x) d\rangle,$$
the least curvature of $f$ at $x$; it is $0$ when $n = 0$.

The definition is `minCurvature` of the second derivative, as in §A.5 of the book. If $f$ is
twice continuously differentiable at $x$, it is the least eigenvalue of the symmetric Hessian
matrix; see `CartisGouldToint.Chapter01.hessianMinEig_eq_iInf_eigenvalues`. -/
noncomputable def hessianMinEig (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  minCurvature (iteratedFDeriv ℝ 2 f x)

/-- The value $\lambda_{\min}[\nabla^2 f(x)]$ is `minCurvature` of the second derivative of $f$ at
$x$. -/
theorem hessianMinEig_def : hessianMinEig f x = minCurvature (iteratedFDeriv ℝ 2 f x) := rfl

/-- $\lambda_{\min}[\nabla^2 f(x)] \ge 0$ if and only if $\langle d, \nabla^2 f(x) d\rangle \ge 0$
for all $d$. -/
theorem hessianMinEig_nonneg_iff :
    0 ≤ hessianMinEig f x ↔ ∀ d, 0 ≤ iteratedFDeriv ℝ 2 f x (fun _ => d) :=
  minCurvature_nonneg_iff

/-- If $f$ is twice continuously differentiable at $x$, then $\lambda_{\min}[\nabla^2 f(x)]$ is the
least eigenvalue of the symmetric Hessian matrix `Optimization.hessianMatrix f x`
([cartis2022evaluation], (1.1.5) and §A.5). Both sides are $0$ when $n = 0$. -/
theorem hessianMinEig_eq_iInf_eigenvalues (hf : ContDiffAt ℝ 2 f x) :
    hessianMinEig f x = ⨅ i, (Optimization.hessianMatrix_isHermitian hf).eigenvalues i :=
  Optimization.minCurvature_iteratedFDeriv_two_eq_iInf_eigenvalues hf

/-- **Section 1.1.2.6** of [cartis2022evaluation], the first-order criticality measure. For
$f : \mathbb{R}^n \to \mathbb{R}$ and $x \in \mathbb{R}^n$, $\omega_1(x) = \|\nabla f(x)\|$.

The measure is meaningful only where $f$ is differentiable. Elsewhere `gradient` of Mathlib is
$0$ by convention, so $\omega_1(x) = 0$ there. -/
noncomputable def omega₁ (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ‖gradient f x‖

/-- **Section 1.1.2.6** of [cartis2022evaluation], the second-order criticality measure. For
$f : \mathbb{R}^n \to \mathbb{R}$ and $x \in \mathbb{R}^n$, $\omega_2(x) = \max(0,
-\lambda_{\min}[\nabla^2 f(x)])$. -/
noncomputable def omega₂ (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  max 0 (-hessianMinEig f x)

/-- The measure $\omega_2$ is the backbone second-order criticality measure
`Optimization.criticality₂`. -/
theorem omega₂_eq_criticality₂ : omega₂ f x = Optimization.criticality₂ f x := rfl

/-- $\omega_1(x) \ge 0$. -/
theorem omega₁_nonneg : 0 ≤ omega₁ f x := norm_nonneg _

/-- $\omega_2(x) \ge 0$. -/
theorem omega₂_nonneg : 0 ≤ omega₂ f x := le_max_left _ _

/-- **Equation (1.1.5)** of [cartis2022evaluation]. For $f : \mathbb{R}^n \to \mathbb{R}$ and
$x \in \mathbb{R}^n$, $\omega_1(x) = 0$ and $\omega_2(x) = 0$ if and only if $\nabla f(x) = 0$
and $\langle d, \nabla^2 f(x) d\rangle \ge 0$ for all $d$.

The right-hand side consists of the first two conditions of Theorem 1.1.1. -/
theorem omega_eq_zero_iff :
    omega₁ f x = 0 ∧ omega₂ f x = 0 ↔
      gradient f x = 0 ∧ ∀ d, 0 ≤ iteratedFDeriv ℝ 2 f x (fun _ => d) := by
  rw [omega₁, norm_eq_zero, omega₂_eq_criticality₂, Optimization.criticality₂_eq_zero_iff,
    minCurvature_nonneg_iff]

/-- If $f$ is twice continuously differentiable and $x$ is a local minimizer of $f$, then
$\omega_1(x) = 0$ and $\omega_2(x) = 0$ ([cartis2022evaluation], (1.1.5)). -/
theorem omega_eq_zero_of_isLocalMin (hf : ContDiff ℝ 2 f) (hmin : IsLocalMin f x) :
    omega₁ f x = 0 ∧ omega₂ f x = 0 :=
  omega_eq_zero_iff.2 ⟨theorem_1_1_1_i (hf.of_le (by norm_num)) hmin, theorem_1_1_1_ii hf hmin⟩

/-- If $f$ is continuously differentiable, then $\omega_1$ is continuous. -/
theorem continuous_omega₁ (hf : ContDiff ℝ 1 f) : Continuous (omega₁ f) :=
  ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.continuous.comp
    (hf.continuous_fderiv one_ne_zero)).norm

/-- If $f$ is twice continuously differentiable, then $\omega_2$ is continuous. -/
theorem continuous_omega₂ (hf : ContDiff ℝ 2 f) : Continuous (omega₂ f) := by
  have hH : Continuous fun z => iteratedFDeriv ℝ 2 f z := hf.continuous_iteratedFDeriv le_rfl
  have hL : LipschitzWith 1 (minCurvature :
      ContinuousMultilinearMap ℝ (fun _ : Fin 2 => EuclideanSpace ℝ (Fin n)) ℝ → ℝ) :=
    LipschitzWith.of_dist_le_mul fun A B => by
      rw [Real.dist_eq, dist_eq_norm, NNReal.coe_one, one_mul]
      exact abs_minCurvature_sub_le
  exact continuous_const.max (hL.continuous.comp hH).neg

end Measures

/-! ### Theorem 1.1.2: convex constraints -/

section ConvexSet

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {C S : Set (EuclideanSpace ℝ (Fin n))}
  {x : EuclideanSpace ℝ (Fin n)}

/-- **Theorem 1.1.2** of [cartis2022evaluation], first-order condition (1.1.6). Let
$\mathcal{C} \subseteq \mathbb{R}^n$ be nonempty, closed and convex, let
$\mathcal{S} \supseteq \mathcal{C}$ be open, let $f$ be continuously differentiable on
$\mathcal{S}$, and let $x^* \in \mathcal{C}$ be a local minimizer of $f$ in $\mathcal{C}$. Then
$\langle d, \nabla f(x^*)\rangle \ge 0$ for all $d \in \mathcal{C}(x^*)$. -/
theorem theorem_1_1_2_i (_hne : C.Nonempty) (_hcl : IsClosed C) (hC : Convex ℝ C)
    (hS : IsOpen S) (hCS : C ⊆ S) (hf : ContDiffOn ℝ 1 f S) (hx : x ∈ C)
    (hmin : IsLocalMinOn f C x) : ∀ d ∈ feasibleDirections C x, 0 ≤ ⟪d, gradient f x⟫ := by
  intro d hd
  rw [inner_gradient]
  exact Optimization.IsLocalMinOn.fderiv_apply_nonneg_of_convex hC hx hmin
    ((hf.contDiffAt (hS.mem_nhds (hCS hx))).differentiableAt (by norm_num)) hd

/-- **Theorem 1.1.2** of [cartis2022evaluation], second-order condition (1.1.8). Let
$\mathcal{C} \subseteq \mathbb{R}^n$ be nonempty, closed and convex, let
$\mathcal{S} \supseteq \mathcal{C}$ be open, let $f$ be twice continuously differentiable on
$\mathcal{S}$, and let $x^* \in \mathcal{C}$ be a local minimizer of $f$ in $\mathcal{C}$. Then
$\langle d, \nabla^2 f(x^*) d\rangle \ge 0$ for all $d \in \mathcal{C}(x^*)$ with
$\langle d, \nabla f(x^*)\rangle = 0$. -/
theorem theorem_1_1_2_ii (_hne : C.Nonempty) (_hcl : IsClosed C) (hC : Convex ℝ C)
    (hS : IsOpen S) (hCS : C ⊆ S) (hf : ContDiffOn ℝ 2 f S) (hx : x ∈ C)
    (hmin : IsLocalMinOn f C x) :
    ∀ d ∈ feasibleDirections C x, ⟪d, gradient f x⟫ = 0 →
      0 ≤ iteratedFDeriv ℝ 2 f x (fun _ => d) := by
  intro d hd hd1
  rw [inner_gradient] at hd1
  exact Optimization.IsLocalMinOn.iteratedFDeriv_two_nonneg_of_convex hC hx hmin
    (hf.contDiffAt (hS.mem_nhds (hCS hx))) hd hd1

/-- **Theorem 1.1.2** of [cartis2022evaluation], third-order condition (1.1.9). Let
$\mathcal{C} \subseteq \mathbb{R}^n$ be nonempty, closed and convex, let
$\mathcal{S} \supseteq \mathcal{C}$ be open, let $f$ be three times continuously differentiable
on $\mathcal{S}$, and let $x^* \in \mathcal{C}$ be a local minimizer of $f$ in $\mathcal{C}$.
Then $\nabla^3 f(x^*)[d]^3 \ge 0$ for all $d \in \mathcal{C}(x^*)$ with
$\langle d, \nabla f(x^*)\rangle = 0$ and $\langle d, \nabla^2 f(x^*) d\rangle = 0$. -/
theorem theorem_1_1_2_iii (_hne : C.Nonempty) (_hcl : IsClosed C) (hC : Convex ℝ C)
    (hS : IsOpen S) (hCS : C ⊆ S) (hf : ContDiffOn ℝ 3 f S) (hx : x ∈ C)
    (hmin : IsLocalMinOn f C x) :
    ∀ d ∈ feasibleDirections C x, ⟪d, gradient f x⟫ = 0 →
      iteratedFDeriv ℝ 2 f x (fun _ => d) = 0 → 0 ≤ iteratedFDeriv ℝ 3 f x (fun _ => d) := by
  intro d hd hd1 hd2
  rw [inner_gradient] at hd1
  exact Optimization.IsLocalMinOn.iteratedFDeriv_three_nonneg_of_convex hC hx hmin
    (hf.contDiffAt (hS.mem_nhds (hCS hx))) hd hd1 hd2

/-- **Theorem 1.1.2** of [cartis2022evaluation], sufficient condition. Let
$\mathcal{C} \subseteq \mathbb{R}^n$ be nonempty, closed and convex, let
$\mathcal{S} \supseteq \mathcal{C}$ be open, let $f$ be twice continuously differentiable on
$\mathcal{S}$, and let $x^* \in \mathcal{C}$ satisfy (1.1.6), that is,
$\langle d, \nabla f(x^*)\rangle \ge 0$ for all $d \in \mathcal{C}(x^*)$. Assume that
$\langle d, \nabla^2 f(x^*) d\rangle > 0$ for every nonzero $d$ in the tangent cone
$T_{\mathcal{C}}(x^*)$ with $\langle d, \nabla f(x^*)\rangle = 0$. Then $x^*$ is a strict local
minimizer of $f$ in $\mathcal{C}$.

**Correction.** The book assumes the curvature condition only for the nonzero
$d \in \mathcal{C}(x^*)$ with $\langle d, \nabla f(x^*)\rangle = 0$. This is not sufficient; see
`CartisGouldToint.Chapter01.theorem_1_1_2_iv_counterexample`. The tangent cone, the closure of
the cone generated by $\mathcal{C}(x^*)$, gives the correct sufficient condition. The two
conditions coincide for polyhedral $\mathcal{C}$.

The tangent cone is `tangentConeAt ℝ C x` of Mathlib. The proof does not use the hypotheses that
$\mathcal{C}$ is nonempty, closed and convex; they are kept to match the book. -/
theorem theorem_1_1_2_iv (_hne : C.Nonempty) (_hcl : IsClosed C) (_hC : Convex ℝ C)
    (hS : IsOpen S) (hCS : C ⊆ S) (hf : ContDiffOn ℝ 2 f S) (hx : x ∈ C)
    (hfo : ∀ d ∈ feasibleDirections C x, 0 ≤ ⟪d, gradient f x⟫)
    (hso : ∀ d ∈ tangentConeAt ℝ C x, d ≠ 0 → ⟪d, gradient f x⟫ = 0 →
      0 < iteratedFDeriv ℝ 2 f x (fun _ => d)) :
    Optimization.IsStrictLocalMinOn f C x := by
  refine Optimization.isStrictLocalMinOn_of_tangentCone (hf.contDiffAt (hS.mem_nhds (hCS hx)))
    (eventually_nhdsWithin_of_forall fun z hz => ?_) fun d hd hd0 hd1 => hso d hd hd0 ?_
  · have := hfo (z - x) (by simpa using hz)
    rwa [inner_gradient] at this
  · rwa [inner_gradient]

/-- **Theorem 1.1.2** of [cartis2022evaluation], the printed sufficient condition is false. In
$\mathbb{R}^2$ let $\mathcal{C} = \{x : x_0^2 \le x_1\}$ and $f(x) = x_1 - 2x_0^2$. Then
$\mathcal{C}$ is nonempty, closed and convex, $f$ is twice continuously differentiable,
$0 \in \mathcal{C}$, and the first-order condition (1.1.6) holds at $x^* = 0$. The book's
second-order hypothesis also holds at $0$: $\langle d, \nabla^2 f(0) d\rangle > 0$ for every
nonzero $d \in \mathcal{C}(0)$ with $\langle d, \nabla f(0)\rangle = 0$. But $0$ is not a local
minimizer of $f$ in $\mathcal{C}$.

The second-order hypothesis holds vacuously, since no nonzero $d \in \mathcal{C}(0)$ is
orthogonal to $\nabla f(0)$. The point $0$ is not a local minimizer because $f(t, t^2) = -t^2$.
The coordinates are indexed from $0$. -/
theorem theorem_1_1_2_iv_counterexample :
    let C : Set (EuclideanSpace ℝ (Fin 2)) := {x | x 0 ^ 2 ≤ x 1}
    let f : EuclideanSpace ℝ (Fin 2) → ℝ := fun x => x 1 - 2 * x 0 ^ 2
    C.Nonempty ∧ IsClosed C ∧ Convex ℝ C ∧ ContDiff ℝ 2 f ∧ (0 : EuclideanSpace ℝ (Fin 2)) ∈ C ∧
      (∀ d ∈ feasibleDirections C 0, 0 ≤ ⟪d, gradient f 0⟫) ∧
      (∀ d ∈ feasibleDirections C 0, d ≠ 0 → ⟪d, gradient f 0⟫ = 0 →
        0 < iteratedFDeriv ℝ 2 f 0 (fun _ => d)) ∧
      ¬ IsLocalMinOn f C 0 := by
  intro C f
  have hfd : ∀ d, fderiv ℝ f 0 d = d 1 := by
    intro d
    have h : HasFDerivAt f _ 0 :=
      (EuclideanSpace.proj (1 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).hasFDerivAt.sub
        (((EuclideanSpace.proj (0 : Fin 2) :
          EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).hasFDerivAt.pow 2).const_mul 2)
    rw [h.fderiv]
    simp
  refine ⟨⟨0, by simp [C]⟩, isClosed_le (by fun_prop) (by fun_prop), ?_, by fun_prop,
    by simp [C], ?_, ?_, ?_⟩
  · intro a ha b hb s t hs ht hst
    simp only [C, mem_ofPred_eq, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at ha hb ⊢
    have ht' : t = 1 - s := by linarith
    subst ht'
    nlinarith [mul_nonneg (mul_nonneg hs ht) (sq_nonneg (a 0 - b 0)),
      mul_le_mul_of_nonneg_left ha hs, mul_le_mul_of_nonneg_left hb ht]
  · intro d hd
    simp only [mem_feasibleDirections, zero_add, C, mem_ofPred_eq] at hd
    rw [inner_gradient, hfd]
    nlinarith [sq_nonneg (d 0)]
  · intro d hd hd0 h1
    simp only [mem_feasibleDirections, zero_add, C, mem_ofPred_eq] at hd
    rw [inner_gradient, hfd] at h1
    have h0 : d 0 = 0 := by nlinarith [sq_nonneg (d 0)]
    exact absurd (by ext i; fin_cases i <;> simp [h0, h1]) hd0
  · intro hmin
    let γ : ℝ → EuclideanSpace ℝ (Fin 2) := fun t =>
      (EuclideanSpace.equiv (Fin 2) ℝ).symm ![t, t ^ 2]
    have hγ0 : ∀ t, γ t 0 = t := fun t => by simp [γ]
    have hγ1 : ∀ t, γ t 1 = t ^ 2 := fun t => by simp [γ]
    have ht : Tendsto γ (𝓝[≠] 0) (𝓝[C] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_
        (Eventually.of_forall fun t => by simp [C, hγ0, hγ1])
      have hc : Continuous γ := by fun_prop
      have h0 : γ 0 = 0 := by ext i; fin_cases i <;> simp [hγ0, hγ1]
      exact (h0 ▸ hc.tendsto 0).mono_left nhdsWithin_le_nhds
    obtain ⟨t, htf, ht0⟩ := ((ht.eventually hmin).and self_mem_nhdsWithin).exists
    have ht0' : t ≠ 0 := ht0
    have : 0 < t ^ 2 := lt_of_le_of_ne (sq_nonneg t) (pow_ne_zero 2 ht0').symm
    simp only [f, hγ0, hγ1, PiLp.zero_apply] at htf
    nlinarith

end ConvexSet

/-! ### Theorem 1.1.3: equality constraints -/

section Equality

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {c : Fin m → EuclideanSpace ℝ (Fin n) → ℝ}
  {S : Set (EuclideanSpace ℝ (Fin n))} {x : EuclideanSpace ℝ (Fin n)}

/-- For $y \in \mathbb{R}^m$, $Df(x) + \sum_i (-y_i) Dc_i(x) = 0$ if and only if
$Df(x) - \sum_i y_i Dc_i(x) = 0$. -/
theorem stationary_neg_iff {y : Fin m → ℝ} :
    fderiv ℝ f x + ∑ i, (-y) i • fderiv ℝ (c i) x = 0 ↔
      fderiv ℝ f x - ∑ i, y i • fderiv ℝ (c i) x = 0 := by
  simp [neg_smul, Finset.sum_neg_distrib, ← sub_eq_add_neg]

/-- Let $f$ and all $c_i$ be differentiable at $x$. Then $x$ with the multipliers $-y$ is a
Karush–Kuhn–Tucker point of the backbone, `Constrained.IsKKTPoint`, for the equality constraints
$c = 0$ and no inequality constraints, if and only if $\nabla_x \mathcal{L}(x, y) = 0$ and
$c(x) = 0$. -/
theorem isKKTPoint_eq_iff (hf : DifferentiableAt ℝ f x) (hc : ∀ i, DifferentiableAt ℝ (c i) x)
    (g : Empty → EuclideanSpace ℝ (Fin n) → ℝ)
    (g' : Empty → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) (μ : Empty → ℝ)
    (y : Fin m → ℝ) :
    Constrained.IsKKTPoint (fderiv ℝ f) c (fun i => fderiv ℝ (c i)) g g' x (-y) μ ↔
      gradient (fun z => lagrangian f c z y) x = 0 ∧ ∀ i, c i x = 0 := by
  rw [gradient_lagrangian_eq_zero_iff hf hc]
  constructor
  · intro h
    refine ⟨?_, h.feasible_eq⟩
    have := h.stationary
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero] at this
    exact stationary_neg_iff.1 this
  · rintro ⟨h1, h2⟩
    refine ⟨h2, isEmptyElim, ?_, isEmptyElim, isEmptyElim⟩
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
    exact stationary_neg_iff.2 h1

/-- **Theorem 1.1.3** of [cartis2022evaluation], first-order condition (1.1.13). Let $\mathcal{S}$
be an open set that contains the feasible region $\{x : c(x) = 0\}$, let $f$ and all $c_i$ be
continuously differentiable on $\mathcal{S}$, and let $x^*$ with $c(x^*) = 0$ be a local
minimizer of $f$ in the feasible region at which LICQ holds. Then there is exactly one
$y^* \in \mathbb{R}^m$ with
$$\nabla_x \mathcal{L}(x^*, y^*) = 0 \quad \text{and} \quad c(x^*) = 0.$$

**Reading.** The book requires an unspecified constraint qualification; LICQ,
`CartisGouldToint.Chapter01.licq`, is used. -/
theorem theorem_1_1_3_i (hS : IsOpen S) (hFS : {x | ∀ i, c i x = 0} ⊆ S)
    (hf : ContDiffOn ℝ 1 f S) (hc : ∀ i, ContDiffOn ℝ 1 (c i) S) (hx : ∀ i, c i x = 0)
    (hmin : IsLocalMinOn f {x | ∀ i, c i x = 0} x) (hcq : licq c x) :
    ∃! y : Fin m → ℝ, gradient (fun z => lagrangian f c z y) x = 0 ∧ ∀ i, c i x = 0 := by
  have hxS : S ∈ 𝓝 x := hS.mem_nhds (hFS hx)
  have hfx := hf.contDiffAt hxS
  have hcx := fun i => (hc i).contDiffAt hxS
  have hfd : DifferentiableAt ℝ f x := hfx.differentiableAt (by norm_num)
  have hcd : ∀ i, DifferentiableAt ℝ (c i) x := fun i => (hcx i).differentiableAt (by norm_num)
  obtain ⟨l, hl, huniq⟩ := Constrained.existsUnique_multipliers_of_isLocalMinOn
    ((licq_iff_isRegularPoint hx).1 hcq) hmin (hfx.hasStrictFDerivAt (by norm_num))
    fun i => (hcx i).hasStrictFDerivAt (by norm_num)
  have key : ∀ y : Fin m → ℝ, gradient (fun z => lagrangian f c z y) x = 0 ↔
      fderiv ℝ f x + ∑ i, (-y) i • fderiv ℝ (c i) x = 0 := fun y => by
    rw [gradient_lagrangian_eq_zero_iff hfd hcd]
    simp [neg_smul, Finset.sum_neg_distrib, ← sub_eq_add_neg]
  refine ⟨-l, ⟨(key _).2 (by simpa using hl), hx⟩, fun y hy => ?_⟩
  rw [← huniq (-y) ((key y).1 hy.1), neg_neg]

/-- **Theorem 1.1.3** of [cartis2022evaluation], second-order necessary condition (1.1.14). Let
$\mathcal{S}$ be an open set that contains the feasible region $\{x : c(x) = 0\}$, let $f$ and
all $c_i$ be twice continuously differentiable on $\mathcal{S}$, and let $x^*$ with $c(x^*) = 0$
be a local minimizer of $f$ in the feasible region at which LICQ holds. Let $y \in \mathbb{R}^m$
with $\nabla_x \mathcal{L}(x^*, y) = 0$. Then $\langle d, \nabla_{xx}^2 \mathcal{L}(x^*, y)
d\rangle \ge 0$ for all $d$ with $\langle \nabla c_i(x^*), d\rangle = 0$ for all $i$.

**Generalization.** The book states the condition for the Lagrange multipliers of (1.1.13). It
is proved for every $y$ with $\nabla_x \mathcal{L}(x^*, y) = 0$; under LICQ there is exactly one
such $y$. -/
theorem theorem_1_1_3_ii (hS : IsOpen S) (hFS : {x | ∀ i, c i x = 0} ⊆ S)
    (hf : ContDiffOn ℝ 2 f S) (hc : ∀ i, ContDiffOn ℝ 2 (c i) S) (hx : ∀ i, c i x = 0)
    (hmin : IsLocalMinOn f {x | ∀ i, c i x = 0} x) (hcq : licq c x) (y : Fin m → ℝ)
    (hy : gradient (fun z => lagrangian f c z y) x = 0) (d : EuclideanSpace ℝ (Fin n))
    (hd : ∀ i, ⟪gradient (c i) x, d⟫ = 0) :
    0 ≤ iteratedFDeriv ℝ 2 (fun z => lagrangian f c z y) x (fun _ => d) := by
  have hxS : S ∈ 𝓝 x := hS.mem_nhds (hFS hx)
  have hfx := hf.contDiffAt hxS
  have hcx := fun i => (hc i).contDiffAt hxS
  have hfd : DifferentiableAt ℝ f x := hfx.differentiableAt (by norm_num)
  have hcd : ∀ i, DifferentiableAt ℝ (c i) x := fun i => (hcx i).differentiableAt (by norm_num)
  let g : Empty → EuclideanSpace ℝ (Fin n) → ℝ := fun i => i.elim
  let g' : Empty → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := fun i => i.elim
  let μ : Empty → ℝ := fun i => i.elim
  have hkkt := (isKKTPoint_eq_iff hfd hcd g g' μ y).2 ⟨hy, hx⟩
  have hreg := ((licq_iff_isRegularPoint hx).1 hcq).isRegularPointIneq g g'
  have hmin' : IsLocalMinOn f (Constrained.feasible c g) x := by
    rwa [Constrained.feasible_of_isEmpty]
  have := Constrained.secondOrder_necessary_of_isKKTPoint hkkt hreg hmin' hfx hcx isEmptyElim
    hfd.hasFDerivAt (fun i => (hcd i).hasFDerivAt) isEmptyElim d
    ⟨fun i => by rw [← inner_gradient_left]; exact hd i, isEmptyElim, isEmptyElim⟩
  rwa [kktLagrangian_eq_lagrangian_of_eq] at this

/-- **Theorem 1.1.3** of [cartis2022evaluation], sufficient condition (1.1.15). Let $\mathcal{S}$ be
an open set that contains the feasible region $\{x : c(x) = 0\}$, let $f$ and all $c_i$ be twice
continuously differentiable on $\mathcal{S}$, and let $x^*$ and $y^*$ satisfy (1.1.13):
$\nabla_x \mathcal{L}(x^*, y^*) = 0$ and $c(x^*) = 0$. If $\langle d, \nabla_{xx}^2
\mathcal{L}(x^*, y^*) d\rangle > 0$ for all $d \neq 0$ with
$\langle \nabla c_i(x^*), d\rangle = 0$ for all $i$, then $x^*$ is a strict local minimizer of
$f$ in the feasible region.

**Typo.** The book does not exclude $d = 0$, for which the strict inequality fails. -/
theorem theorem_1_1_3_iii (hS : IsOpen S) (hFS : {x | ∀ i, c i x = 0} ⊆ S)
    (hf : ContDiffOn ℝ 2 f S) (hc : ∀ i, ContDiffOn ℝ 2 (c i) S) {y : Fin m → ℝ}
    (hy : gradient (fun z => lagrangian f c z y) x = 0) (hx : ∀ i, c i x = 0)
    (hpos : ∀ d, d ≠ 0 → (∀ i, ⟪gradient (c i) x, d⟫ = 0) →
      0 < iteratedFDeriv ℝ 2 (fun z => lagrangian f c z y) x (fun _ => d)) :
    Optimization.IsStrictLocalMinOn f {x | ∀ i, c i x = 0} x := by
  have hxS : S ∈ 𝓝 x := hS.mem_nhds (hFS hx)
  have hfx := hf.contDiffAt hxS
  have hcx := fun i => (hc i).contDiffAt hxS
  have hfd : DifferentiableAt ℝ f x := hfx.differentiableAt (by norm_num)
  have hcd : ∀ i, DifferentiableAt ℝ (c i) x := fun i => (hcx i).differentiableAt (by norm_num)
  let g : Empty → EuclideanSpace ℝ (Fin n) → ℝ := fun i => i.elim
  let g' : Empty → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := fun i => i.elim
  let μ : Empty → ℝ := fun i => i.elim
  have hkkt := (isKKTPoint_eq_iff hfd hcd g g' μ y).2 ⟨hy, hx⟩
  have := Constrained.isStrictLocalMinOn_of_secondOrder_sufficient hkkt hfx hcx isEmptyElim
    hfd.hasFDerivAt (fun i => (hcd i).hasFDerivAt) isEmptyElim fun d hd hd0 => by
      rw [kktLagrangian_eq_lagrangian_of_eq]
      exact hpos d hd0 fun i => by rw [inner_gradient_left]; exact hd.1 i
  rwa [Constrained.feasible_of_isEmpty] at this

end Equality

/-! ### Theorem 1.1.4: inequality constraints -/

section Inequality

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {c : Fin m → EuclideanSpace ℝ (Fin n) → ℝ}
  {S : Set (EuclideanSpace ℝ (Fin n))} {x : EuclideanSpace ℝ (Fin n)} {y : Fin m → ℝ}

/-- **Equation (1.1.16)** of [cartis2022evaluation]. For the problem $\min f(x)$ subject to
$c(x) \ge 0$, a pair $(x, y)$ with $y \in \mathbb{R}^m$ satisfies the **first-order optimality
conditions** if
$$\nabla_x \mathcal{L}(x, y) = 0, \quad c(x) \ge 0, \quad y \ge 0 \quad \text{and} \quad \langle
  y, c(x)\rangle = 0.$$
-/
def IsKKTPair (f : EuclideanSpace ℝ (Fin n) → ℝ) (c : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (y : Fin m → ℝ) : Prop :=
  gradient (fun z => lagrangian f c z y) x = 0 ∧ (∀ i, 0 ≤ c i x) ∧ (∀ i, 0 ≤ y i) ∧
    ∑ i, y i * c i x = 0

/-- The pair $(x, y)$ satisfies (1.1.16) if and only if $\nabla_x \mathcal{L}(x, y) = 0$,
$c(x) \ge 0$, $y \ge 0$ and $\sum_i y_i c_i(x) = 0$. -/
theorem isKKTPair_iff : IsKKTPair f c x y ↔ gradient (fun z => lagrangian f c z y) x = 0 ∧
    (∀ i, 0 ≤ c i x) ∧ (∀ i, 0 ≤ y i) ∧ ∑ i, y i * c i x = 0 := Iff.rfl

/-- Let $f$ and all $c_i$ be differentiable at $x$. Then $(x, y)$ satisfies (1.1.16) if and only if
$x$ with the multipliers $y$ is a Karush–Kuhn–Tucker point of the backbone,
`Constrained.IsKKTPoint`, for the inequality constraints $-c_i \le 0$ and no equality
constraints. -/
theorem isKKTPair_iff_isKKTPoint (hf : DifferentiableAt ℝ f x)
    (hc : ∀ i, DifferentiableAt ℝ (c i) x) (l : Empty → ℝ) :
    IsKKTPair f c x y ↔ Constrained.IsKKTPoint (fderiv ℝ f) (fun i : Empty => i.elim)
      (fun i : Empty => i.elim) (fun i => -c i) (fun i z => -fderiv ℝ (c i) z) x l y := by
  rw [isKKTPair_iff, gradient_lagrangian_eq_zero_iff hf hc]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => mul_nonneg (h3 i) (h2 i)).1 h4
    exact ⟨isEmptyElim, fun j => neg_nonpos.2 (h2 j),
      by simpa [smul_neg, Finset.sum_neg_distrib, ← sub_eq_add_neg] using h1, h3,
      fun j => by simpa using hterm j (Finset.mem_univ j)⟩
  · intro h
    refine ⟨by simpa [smul_neg, Finset.sum_neg_distrib, ← sub_eq_add_neg] using h.stationary,
      fun j => neg_nonpos.1 (h.feasible_ineq j), h.nonneg,
      Finset.sum_eq_zero fun j _ => by simpa using h.complementary j⟩

/-- **Theorem 1.1.4** of [cartis2022evaluation], first-order conditions (1.1.16). Let $\mathcal{S}$
be an open set that contains the feasible region $\{x : c(x) \ge 0\}$, let $f$ and all $c_i$ be
continuously differentiable on $\mathcal{S}$, and let $x^*$ with $c(x^*) \ge 0$ be a local
minimizer of $f$ in the feasible region at which LICQ holds. Then there is exactly one
$y^* \in \mathbb{R}^m$ such that
$$\nabla_x \mathcal{L}(x^*, y^*) = 0, \quad c(x^*) \ge 0, \quad y^* \ge 0 \quad \text{and} \quad
  \langle y^*, c(x^*)\rangle = 0.$$

**Reading.** The book requires an unspecified constraint qualification; LICQ,
`CartisGouldToint.Chapter01.licq`, is used. -/
theorem theorem_1_1_4_i (hS : IsOpen S) (hFS : {x | ∀ i, 0 ≤ c i x} ⊆ S)
    (hf : ContDiffOn ℝ 1 f S) (hc : ∀ i, ContDiffOn ℝ 1 (c i) S) (hx : ∀ i, 0 ≤ c i x)
    (hmin : IsLocalMinOn f {x | ∀ i, 0 ≤ c i x} x) (hcq : licq c x) :
    ∃! y : Fin m → ℝ, IsKKTPair f c x y := by
  have hxS : S ∈ 𝓝 x := hS.mem_nhds (hFS hx)
  have hfx := hf.contDiffAt hxS
  have hcx := fun i => (hc i).contDiffAt hxS
  have hfd : DifferentiableAt ℝ f x := hfx.differentiableAt (by norm_num)
  have hcd : ∀ i, DifferentiableAt ℝ (c i) x := fun i => (hcx i).differentiableAt (by norm_num)
  have hreg := (licq_iff_isRegularPointIneq hx).1 hcq
  have hmin' : IsLocalMinOn f (Constrained.feasible (fun i : Empty => i.elim)
      (fun i => -c i)) x := by
    convert hmin using 1
    ext z
    simp
  obtain ⟨l, y, hkkt⟩ := Constrained.exists_kkt_of_isLocalMinOn hreg hmin' hfd.hasFDerivAt
    isEmptyElim fun i => ((hcx i).hasStrictFDerivAt (by norm_num)).neg
  refine ⟨y, (isKKTPair_iff_isKKTPoint hfd hcd l).2 hkkt, fun y' hy' => ?_⟩
  exact (Constrained.kkt_multipliers_unique hreg ((isKKTPair_iff_isKKTPoint hfd hcd l).1 hy')
    hkkt).2

/-- **Equation (1.1.17)** of [cartis2022evaluation], the cone $\mathcal{N}_+$. For constraints
$c_i$, a point $x$ and multipliers $y$, the cone $\mathcal{N}_+$ is the set of
$d \in \mathbb{R}^n$ such that for every active constraint $i \in \mathcal{A}(x)$,
$\langle d, \nabla c_i(x)\rangle = 0$ if $y_i > 0$ and $\langle d, \nabla c_i(x)\rangle \ge 0$
if $y_i = 0$. -/
def criticalConeN (c : Fin m → EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n))
    (y : Fin m → ℝ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {d | ∀ i ∈ activeSet c x, (0 < y i → ⟪d, gradient (c i) x⟫ = 0) ∧
    (y i = 0 → 0 ≤ ⟪d, gradient (c i) x⟫)}

/-- A vector $d$ is in $\mathcal{N}_+$ if and only if, for every $i \in \mathcal{A}(x)$,
$\langle d, \nabla c_i(x)\rangle = 0$ when $y_i > 0$ and $\langle d, \nabla c_i(x)\rangle \ge 0$
when $y_i = 0$. -/
theorem mem_criticalConeN {d : EuclideanSpace ℝ (Fin n)} :
    d ∈ criticalConeN c x y ↔ ∀ i ∈ activeSet c x, (0 < y i → ⟪d, gradient (c i) x⟫ = 0) ∧
      (y i = 0 → 0 ≤ ⟪d, gradient (c i) x⟫) := Iff.rfl

/-- The cone $\mathcal{N}_+$ is the backbone critical cone `Constrained.criticalCone` of the
constraints $-c_i \le 0$ with the multipliers $y$. -/
theorem criticalConeN_eq_criticalCone :
    criticalConeN c x y = Constrained.criticalCone (fun i : Empty => i.elim) (fun i => -c i)
      (fun i z => -fderiv ℝ (c i) z) x y := by
  ext d
  simp only [mem_criticalConeN, Constrained.mem_criticalCone, mem_activeSet,
    Constrained.mem_activeSet, Pi.neg_apply, inner_gradient, neg_apply,
    neg_eq_zero, neg_nonpos, IsEmpty.forall_iff, true_and]
  exact ⟨fun h => ⟨fun j hj hy => (h j hj).1 hy, fun j hj hy => (h j hj).2 hy⟩,
    fun h j hj => ⟨h.1 j hj, h.2 j hj⟩⟩

/-- **Theorem 1.1.4** of [cartis2022evaluation], second-order necessary condition (1.1.17). Let
$\mathcal{S}$ be an open set that contains the feasible region $\{x : c(x) \ge 0\}$, let $f$ and
all $c_i$ be twice continuously differentiable on $\mathcal{S}$, and let $x^*$ be a local
minimizer of $f$ in the feasible region at which LICQ holds. Let $y$ be such that $(x^*, y)$
satisfies (1.1.16). Then $\langle d, \nabla_{xx}^2 \mathcal{L}(x^*, y) d\rangle \ge 0$ for all
$d \in \mathcal{N}_+$.

**Generalization.** The book states the condition for the Lagrange multipliers of (1.1.16). It
is proved for every $y$ such that $(x^*, y)$ satisfies (1.1.16); under LICQ there is exactly one
such $y$.

The cone $\mathcal{N}_+$ is `CartisGouldToint.Chapter01.criticalConeN c x y`. -/
theorem theorem_1_1_4_ii (hS : IsOpen S) (hFS : {x | ∀ i, 0 ≤ c i x} ⊆ S)
    (hf : ContDiffOn ℝ 2 f S) (hc : ∀ i, ContDiffOn ℝ 2 (c i) S)
    (hmin : IsLocalMinOn f {x | ∀ i, 0 ≤ c i x} x) (hcq : licq c x) (hy : IsKKTPair f c x y) :
    ∀ d ∈ criticalConeN c x y,
      0 ≤ iteratedFDeriv ℝ 2 (fun z => lagrangian f c z y) x (fun _ => d) := by
  have hx := hy.2.1
  have hxS : S ∈ 𝓝 x := hS.mem_nhds (hFS hx)
  have hfx := hf.contDiffAt hxS
  have hcx := fun i => (hc i).contDiffAt hxS
  have hfd : DifferentiableAt ℝ f x := hfx.differentiableAt (by norm_num)
  have hcd : ∀ i, DifferentiableAt ℝ (c i) x := fun i => (hcx i).differentiableAt (by norm_num)
  have hreg := (licq_iff_isRegularPointIneq hx).1 hcq
  have hmin' : IsLocalMinOn f (Constrained.feasible (fun i : Empty => i.elim)
      (fun i => -c i)) x := by
    convert hmin using 1
    ext z
    simp
  have hkkt := (isKKTPair_iff_isKKTPoint hfd hcd (fun i => i.elim)).1 hy
  intro d hd
  rw [criticalConeN_eq_criticalCone] at hd
  have := Constrained.secondOrder_necessary_of_isKKTPoint hkkt hreg hmin' hfx isEmptyElim
    (fun i => (hcx i).neg) hfd.hasFDerivAt isEmptyElim (fun i => (hcd i).hasFDerivAt.neg) d hd
  rwa [kktLagrangian_eq_lagrangian] at this

/-- **Theorem 1.1.4** of [cartis2022evaluation], sufficient condition (1.1.18). Let $\mathcal{S}$ be
an open set that contains the feasible region $\{x : c(x) \ge 0\}$, let $f$ and all $c_i$ be
twice continuously differentiable on $\mathcal{S}$, and let $(x^*, y^*)$ satisfy (1.1.16). If
$\langle d, \nabla_{xx}^2 \mathcal{L}(x^*, y^*) d\rangle > 0$ for all nonzero
$d \in \mathcal{N}_+$, then $x^*$ is a strict local minimizer of $f$ in the feasible region.

**Typo.** The book does not exclude $d = 0$, for which the strict inequality fails. -/
theorem theorem_1_1_4_iii (hS : IsOpen S) (hFS : {x | ∀ i, 0 ≤ c i x} ⊆ S)
    (hf : ContDiffOn ℝ 2 f S) (hc : ∀ i, ContDiffOn ℝ 2 (c i) S) (hy : IsKKTPair f c x y)
    (hpos : ∀ d ∈ criticalConeN c x y, d ≠ 0 →
      0 < iteratedFDeriv ℝ 2 (fun z => lagrangian f c z y) x (fun _ => d)) :
    Optimization.IsStrictLocalMinOn f {x | ∀ i, 0 ≤ c i x} x := by
  have hx := hy.2.1
  have hxS : S ∈ 𝓝 x := hS.mem_nhds (hFS hx)
  have hfx := hf.contDiffAt hxS
  have hcx := fun i => (hc i).contDiffAt hxS
  have hfd : DifferentiableAt ℝ f x := hfx.differentiableAt (by norm_num)
  have hcd : ∀ i, DifferentiableAt ℝ (c i) x := fun i => (hcx i).differentiableAt (by norm_num)
  have hkkt := (isKKTPair_iff_isKKTPoint hfd hcd (fun i => i.elim)).1 hy
  have := Constrained.isStrictLocalMinOn_of_secondOrder_sufficient hkkt hfx isEmptyElim
    (fun i => (hcx i).neg) hfd.hasFDerivAt isEmptyElim (fun i => (hcd i).hasFDerivAt.neg)
    fun d hd hd0 => by
      rw [kktLagrangian_eq_lagrangian]
      exact hpos d (criticalConeN_eq_criticalCone ▸ hd) hd0
  convert this using 1
  ext z
  simp

end Inequality

end CartisGouldToint.Chapter01
