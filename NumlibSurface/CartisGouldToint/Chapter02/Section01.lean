/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Numlib.Analysis.Calculus.AnchoredLipschitzDerivs

/-!
# Cartis, Gould and Toint, Section 2.1: A requirement

This module formalizes §2.1 of [cartis2022evaluation]: the standing assumptions of Part IA on the
objective $f : \mathbb{R}^n \to \mathbb{R}$ of the unconstrained problem (2.1.1). Assumption f.Bb
says that $f$ is bounded below by a constant $f_{\mathrm{low}}$, f.C1 says that $f$ is continuously
differentiable, and f.gL says that moreover the gradient of $f$ is Lipschitz continuous with a
constant $L_{f,1} \ge 1$ (2.1.5). Under f.gL the second derivative is bounded by $L_{f,1}$ wherever
it exists. The assumptions are stated with the backbone module
`Numlib.Analysis.Calculus.AnchoredLipschitzDerivs`.

## Main definitions

* Assumption f.Bb, `CartisGouldToint.Chapter02.AssumptionBb`: $f(x) \ge f_{\mathrm{low}}$ for all
  $x$.
* Assumption f.C1, `CartisGouldToint.Chapter02.AssumptionC1`: $f$ is continuously differentiable.
* Assumption f.gL, `CartisGouldToint.Chapter02.AssumptionGL`: $f$ is continuously differentiable and
  its gradient is $L$-Lipschitz (2.1.5), with $L \ge 1$.

## Main results

* Equation (2.1.5), `CartisGouldToint.Chapter02.AssumptionGL.lipschitz` and
  `CartisGouldToint.Chapter02.AssumptionGL.of_lipschitz`: f.gL in the gradient form.
* Assumption f.gL, `CartisGouldToint.Chapter02.AssumptionGL.iteratedFDerivLipschitzOn`: under f.gL
  the first derivative, as a multilinear map, is $L$-Lipschitz on $\mathbb{R}^n$.
* Theorem A.8.5, `CartisGouldToint.Chapter02.AssumptionGL.norm_iteratedFDeriv_two_le`: under f.gL,
  $\|\nabla^2 f(x)\| \le L$ for all $x$.

## Conventions

* $\mathbb{R}^n$ is `EuclideanSpace ℝ (Fin n)`.

## Implementation notes

* f.gL is the anchored smoothness assumption `LipschitzDerivsAnchored` of order $1$ on the whole
  space, together with $L \ge 1$. The library states the smoothness assumptions of later chapters in
  the same way.

## Deviations from the source

* **Theorem A.8.5, forward implication** (generalization). Under f.gL the Hessian bound needs no
  second-order smoothness, with the iterated derivative set to zero where it does not exist. See
  `CartisGouldToint.Chapter02.AssumptionGL.norm_iteratedFDeriv_two_le`.

## Not formalized

* **Example 2.1.1**, the one-dimensional interpolation construction showing that f.Bb and f.C1
  alone admit no complexity bound.
-/

open Set

namespace CartisGouldToint.Chapter02

variable {n : ℕ}

/-- **Assumption f.Bb** of [cartis2022evaluation], §2.1. A function
$f : \mathbb{R}^n \to \mathbb{R}$ is **bounded below** by the constant $f_{\mathrm{low}}$ if
$f(x) \ge f_{\mathrm{low}}$ for all $x \in \mathbb{R}^n$. -/
def AssumptionBb (f : EuclideanSpace ℝ (Fin n) → ℝ) (flow : ℝ) : Prop :=
  ∀ x, flow ≤ f x

/-- **Assumption f.C1** of [cartis2022evaluation], §2.1. A function
$f : \mathbb{R}^n \to \mathbb{R}$ satisfies f.C1 if it is continuously differentiable on
$\mathbb{R}^n$. -/
def AssumptionC1 (f : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  ContDiff ℝ 1 f

/-- **Assumption f.gL** of [cartis2022evaluation], §2.1. A function
$f : \mathbb{R}^n \to \mathbb{R}$ satisfies f.gL with constant $L = L_{f,1}$ if $f$ is
continuously differentiable on $\mathbb{R}^n$, its gradient is Lipschitz continuous with
constant $L$ (2.1.5),
$$\|\nabla f(x) - \nabla f(y)\| \le L \|x - y\| \quad \text{for all } x, y \in \mathbb{R}^n,$$
and $L \ge 1$.

The definition is the anchored smoothness assumption `LipschitzDerivsAnchored` of order $1$ on
the whole space, together with $L \ge 1$. The gradient form is
`CartisGouldToint.Chapter02.AssumptionGL.lipschitz` and
`CartisGouldToint.Chapter02.AssumptionGL.of_lipschitz`. -/
abbrev AssumptionGL (f : EuclideanSpace ℝ (Fin n) → ℝ) (L : ℝ) : Prop :=
  LipschitzDerivsAnchored f univ univ 1 1 (fun _ => L) ∧ 1 ≤ L

/-- $f$ satisfies f.Bb with the constant $f_{\mathrm{low}}$ if and only if
$f(x) \ge f_{\mathrm{low}}$ for all $x$. -/
theorem assumptionBb_iff {f : EuclideanSpace ℝ (Fin n) → ℝ} {flow : ℝ} :
    AssumptionBb f flow ↔ ∀ x, flow ≤ f x :=
  Iff.rfl

/-- $f$ satisfies f.C1 if and only if $f$ is continuously differentiable. -/
theorem assumptionC1_iff {f : EuclideanSpace ℝ (Fin n) → ℝ} :
    AssumptionC1 f ↔ ContDiff ℝ 1 f :=
  Iff.rfl

/-- For $f : \mathbb{R}^n \to \mathbb{R}$ and $x, y \in \mathbb{R}^n$, $\|Df(x) - Df(y)\| = \|\nabla
f(x) - \nabla f(y)\|$. -/
theorem norm_fderiv_sub_fderiv (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x y : EuclideanSpace ℝ (Fin n)) :
    ‖fderiv ℝ f x - fderiv ℝ f y‖ = ‖gradient f x - gradient f y‖ := by
  rw [gradient, gradient, ← map_sub, LinearIsometryEquiv.norm_map]

/-- For $f : \mathbb{R}^n \to \mathbb{R}$ and $x, y \in \mathbb{R}^n$, the first iterated
derivative, a multilinear map with one argument, satisfies $\|\nabla^1 f(x) - \nabla^1 f(y)\| =
\|Df(x) - Df(y)\|$. -/
theorem norm_iteratedFDeriv_one_sub (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x y : EuclideanSpace ℝ (Fin n)) :
    ‖iteratedFDeriv ℝ 1 f x - iteratedFDeriv ℝ 1 f y‖ = ‖fderiv ℝ f x - fderiv ℝ f y‖ := by
  have e : ∀ z, iteratedFDeriv ℝ 1 f z =
      (continuousMultilinearCurryFin1 ℝ (EuclideanSpace ℝ (Fin n)) ℝ).symm (fderiv ℝ f z) := by
    intro z; ext m; simp
  rw [e, e, ← map_sub, LinearIsometryEquiv.norm_map]

namespace AssumptionGL

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {L : ℝ}

/-- If $f$ satisfies f.gL, then $f$ is continuously differentiable. -/
theorem contDiff (h : AssumptionGL f L) : ContDiff ℝ 1 f :=
  h.1.contDiff

/-- If $f$ satisfies f.gL with constant $L$, then $L \ge 1$. -/
theorem one_le (h : AssumptionGL f L) : 1 ≤ L :=
  h.2

/-- **Assumption f.gL** of [cartis2022evaluation], in the form of the backbone. If $f$ satisfies
f.gL with constant $L$, then the first derivative $\nabla^1 f$, as a multilinear map, is
Lipschitz continuous on $\mathbb{R}^n$ with constant $L$:
$$\|\nabla^1 f(x) - \nabla^1 f(y)\| \le L \|x - y\| \quad \text{for all } x, y.$$

The conclusion is `IteratedFDerivLipschitzOn f 1 L univ`, the form that the Taylor remainder
bounds of the backbone use. -/
theorem iteratedFDerivLipschitzOn (h : AssumptionGL f L) :
    IteratedFDerivLipschitzOn f 1 L univ :=
  (lipschitzDerivsAnchored_univ_top_iff.1 h.1).2

/-- If $f$ is continuously differentiable, $L \ge 1$, and the first derivative $\nabla^1 f$ is
Lipschitz continuous on $\mathbb{R}^n$ with constant $L$, then $f$ satisfies f.gL with constant
$L$. -/
theorem of_iteratedFDerivLipschitzOn (hf : ContDiff ℝ 1 f) (hL1 : 1 ≤ L)
    (hL : IteratedFDerivLipschitzOn f 1 L univ) : AssumptionGL f L :=
  ⟨lipschitzDerivsAnchored_univ_top_iff.2 ⟨hf, hL⟩, hL1⟩

/-- If $f$ satisfies f.gL with constant $L$, then $\|\nabla f(x) - \nabla f(y)\| \le L \|x - y\|$
for all $x, y$ ([cartis2022evaluation], (2.1.5)). -/
theorem lipschitz (h : AssumptionGL f L) (x y : EuclideanSpace ℝ (Fin n)) :
    ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖ := by
  rw [← norm_fderiv_sub_fderiv, ← norm_iteratedFDeriv_one_sub]
  exact iteratedFDerivLipschitzOn_iff.1 h.iteratedFDerivLipschitzOn x (mem_univ _) y (mem_univ _)

/-- If $f$ is continuously differentiable, $L \ge 1$, and
$\|\nabla f(x) - \nabla f(y)\| \le L \|x - y\|$ for all $x, y$, then $f$ satisfies f.gL with
constant $L$ ([cartis2022evaluation], (2.1.5)). -/
theorem of_lipschitz (hf : ContDiff ℝ 1 f) (hL1 : 1 ≤ L)
    (hL : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖) : AssumptionGL f L := by
  refine of_iteratedFDerivLipschitzOn hf hL1 (iteratedFDerivLipschitzOn_iff.2 fun x _ y _ => ?_)
  rw [norm_iteratedFDeriv_one_sub, norm_fderiv_sub_fderiv]
  exact hL x y

/-- If $f$ satisfies f.gL, then $f$ satisfies f.C1. -/
theorem assumptionC1 (h : AssumptionGL f L) : AssumptionC1 f :=
  h.contDiff

/-- If $f$ satisfies f.gL, then $f$ is differentiable. -/
theorem differentiable (h : AssumptionGL f L) : Differentiable ℝ f :=
  h.contDiff.differentiable one_ne_zero

/-- If $f$ satisfies f.gL with constant $L$, then $L > 0$. -/
theorem pos (h : AssumptionGL f L) : 0 < L :=
  zero_lt_one.trans_le h.one_le

/-- If $f$ satisfies f.gL with constant $L$, then $L \ge 0$. -/
theorem nonneg (h : AssumptionGL f L) : 0 ≤ L :=
  h.pos.le

/-- **Theorem A.8.5** of [cartis2022evaluation] for $p = 1$, one direction. If $f$ satisfies f.gL
with constant $L$, then $\|\nabla^2 f(x)\| \le L$ for every $x \in \mathbb{R}^n$, in the
operator norm.

**Generalization.** The theorem in the book assumes $f$ is twice continuously differentiable
when $p = 1$. The bound for a Lipschitz gradient follows from the derivative bound at every
point where the gradient is differentiable. Elsewhere, `iteratedFDeriv ℝ 2 f x` is $0$. -/
theorem norm_iteratedFDeriv_two_le (h : AssumptionGL f L) (x : EuclideanSpace ℝ (Fin n)) :
    ‖iteratedFDeriv ℝ 2 f x‖ ≤ L :=
  norm_iteratedFDeriv_succ_le_of_lipschitzOn isOpen_univ h.nonneg h.iteratedFDerivLipschitzOn
    (mem_univ x)

end AssumptionGL

end CartisGouldToint.Chapter02
