/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Topology.Instances.AddCircle.Real
import Numlib.Analysis.Complex.Harmonic
import Numlib.Analysis.Sobolev.Boundary.ContDiffDomain
import Numlib.Analysis.Sobolev.Boundary.Polygon
import Numlib.Analysis.Sobolev.DenyLions
import Numlib.Approximation.DividedDifference
import Numlib.IntegralEquations.Basic

/-!
# Atkinson and Han, Section 13.1: Green's theorem, the Kelvin transform and the double layer kernel

This module formalizes the parts of Section 13.1 of [han2009theoretical] that do not need the planar
potential theory of the section. Most of Section 13.1 is potential theory: the divergence theorem on
a piecewise smooth multiply connected region, Green's identities, the representation formula and the
jump relations of the layer potentials. The module proves the divergence theorem (Theorem 13.1.2) on
a bounded $C^1$ plane domain and on a triangulated polygon, the Neumann clause of Theorem 13.1.1 in
weak form, and the fact that the Kelvin transform preserves harmonicity (13.1.13). These results use
the surface measure, the normal, the divergence theorem and the trace of
`Numlib.Analysis.Sobolev.Boundary.ContDiffDomain` and `Numlib.Analysis.Sobolev.Boundary.Polygon`,
the Deny–Lions theory of `Numlib.Analysis.Sobolev.DenyLions`, and
`Numlib.Analysis.Complex.Harmonic`.

The main object of the module is the one that Section 13.2 computes with. After a regular $C^2$
parametrization $r(t) = (\xi(t), \eta(t))$ of the boundary, the double layer operator is an ordinary
integral operator with the kernel (13.1.33), $$k(t, s) = \frac{\eta'(s) (\xi(t) - \xi(s)) - \xi'(s)
(\eta(t) - \eta(s))}{|r(t) - r(s)|^2}.$$ This is a quotient $0/0$ on the diagonal: the numerator and
the denominator both vanish to second order there. By (13.1.34) the quotient extends continuously,
and $k(t, t)$ is minus half the signed curvature of the counterclockwise parametrization. With this
continuity, the double layer operator is compact, both on a parameter interval and on the space
$C_p(L)$ of continuous $L$-periodic functions that Section 13.2 uses. The compactness is
`IntegralOperator.isCompactOperator_fredholm` and `IntegralOperator.isCompactOperator_kernelCLM` of
`Numlib.IntegralEquations.Basic`.

## Main definitions

* (13.1.10) and (13.1.12), `AtkinsonHan.Chapter13.kelvin`: the Kelvin transform
  $\hat u = u \circ T$, with $T$ the inversion in the unit circle.
* (13.1.33)–(13.1.34), `AtkinsonHan.Chapter13.doubleLayerKernel`: the parametrized double layer
  kernel, written with divided differences so that it is continuous on the diagonal.
* Section 13.1.3, `AtkinsonHan.Chapter13.doubleLayerKernelCM`: the kernel as a continuous function
  on a parameter square $[a, b]^2$ on which the curve is regular and simple.
* Section 13.1.3, `AtkinsonHan.Chapter13.doubleLayerKernelCP`: the kernel of a regular simple closed
  curve of period $L$, as a continuous function on the torus $(\mathbb{R}/L\mathbb{Z})^2$.

## Main results

* Theorem 13.1.1, `AtkinsonHan.Chapter13.theorem_13_1_1_neumann_weak`: on a bounded connected $C^1$
  domain, the weak Neumann problem for the Laplace equation with data $f$ is solvable if and only if
  $\int_\Gamma f \, d\sigma = 0$, and the solution is unique up to a constant.
* Theorem 13.1.2, `AtkinsonHan.Chapter13.theorem_13_1_2`: the divergence theorem (13.1.4) with the
  inner normal, on a bounded $C^1$ plane domain.
* Theorem 13.1.2, `AtkinsonHan.Chapter13.theorem_13_1_2_polygon`: the divergence theorem (13.1.4)
  with the inner normal, on a triangulated polygon.
* (13.1.13), `AtkinsonHan.Chapter13.kelvin_harmonic`: the Kelvin transform of a harmonic function is
  harmonic.
* (13.1.33), `AtkinsonHan.Chapter13.equation_13_1_33`: off the diagonal the kernel is the quotient
  (13.1.33) of the book.
* (13.1.34), `AtkinsonHan.Chapter13.equation_13_1_34`: on the diagonal, $k(t, t) = (\eta'(t)
  \xi''(t) - \xi'(t) \eta''(t)) / (2 (\xi'(t)^2 + \eta'(t)^2))$.
* `AtkinsonHan.Chapter13.doubleLayerKernel_eq_neg_im_div`: off the diagonal, $k(t, s) =
  -\operatorname{Im}(r'(s) / (r(s) - r(t)))$, minus the rate of turning of the chord from $r(t)$ to
  $r(s)$.
* `AtkinsonHan.Chapter13.doubleLayerKernel_circle_self`: for the unit circle, $k(t, t) = -1/2$.
* Section 13.1.3, `AtkinsonHan.Chapter13.isCompactOperator_doubleLayer`: the double layer operator
  on $C[a, b]$ is compact.
* Section 13.1.3, `AtkinsonHan.Chapter13.isCompactOperator_doubleLayerCP`: the double layer operator
  of a closed curve on $C_p(L)$ is compact.

## Conventions

* The unit normal $n$ of the chapter is the inner normal $n = -\nu$, where $\nu$ is the outward
  normal `IsContDiffDomain.outwardNormal` of the backbone.
* The plane is identified with $\mathbb{C}$ in the Kelvin transform and in
  `AtkinsonHan.Chapter13.doubleLayerKernel_eq_neg_im_div`, with $r(s) = \xi(s) + i \eta(s)$.
* The parametrization $r$ is counterclockwise, as the book fixes it, so that the unit circle
  $r(t) = (\cos t, \sin t)$ has signed curvature $+1$.

## Implementation notes

* The kernel is defined by the quotient of divided differences $(\eta'(s) \xi[s, s, t] - \xi'(s)
  \eta[s, s, t]) / (\xi[s, t]^2 + \eta[s, t]^2)$ of `Numlib.Approximation.DividedDifference`, which
  is already continuous, and not by the displayed formula with a case distinction at $s = t$.
  `AtkinsonHan.Chapter13.equation_13_1_33` recovers the formula of the book off the diagonal, and
  `AtkinsonHan.Chapter13.equation_13_1_34` gives the diagonal value. Only the derivatives
  $\xi', \eta', \xi'', \eta''$ enter the definition.
* The kernel on the torus is not the descent of a biperiodic function. The kernel on the line is not
  separately $L$-periodic, because $k(t + L, t) = 0$ by (13.1.33), while $k(t, t)$ is minus half the
  signed curvature. The kernel is invariant under the diagonal translation
  $(t, s) \mapsto (t + L, s + L)$ (`AtkinsonHan.Chapter13.doubleLayerKernel_add_period`). So the
  kernel on the torus takes the representative of the difference $s - t$ in $[-L/2, L/2)$. Its
  continuity rests on the seam identity $k(t, t - L/2) = k(t, t + L/2)$
  (`AtkinsonHan.Chapter13.doubleLayerKernel_sub_half_period`) and on the fact that the compact
  rectangle $[0, L] \times [-L/2, L/2]$ maps onto the torus by a quotient map.
* In terms of $z \in \mathbb{C}$, the inversion in the unit circle is $T z = \overline{z^{-1}}$, so
  the harmonicity of the Kelvin transform is `InnerProductSpace.HarmonicAt.comp_analyticAt` and
  `InnerProductSpace.HarmonicAt.comp_conj`. In dimension two the Kelvin transform has no weight
  $\|x\|^{2 - d}$.

## Deviations from the source

* **Remark after (13.1.34)** (typo). The prose of the book says that $k(t, t)$ is one-half the
  curvature of $S$ at $r(t)$. The display (13.1.34) gives minus one-half the signed curvature, and
  the module follows the display. See `AtkinsonHan.Chapter13.doubleLayerKernel_circle_self`.
* **Theorem 13.1.1, Neumann clause** (reading). The book states the classical Neumann problem for
  continuous data on a $C^2$ boundary curve. The module states the weak Neumann problem with data in
  $L^2(\sigma)$ on a bounded connected $C^1$ domain of $\mathbb{R}^{d+1}$. See
  `AtkinsonHan.Chapter13.theorem_13_1_1_neumann_weak`.

## Not formalized

* **The identification of the double layer operator with the boundary integral** $\int_S \rho(Q) \,
  \frac{\partial}{\partial n_Q} \log |P - Q| \, dS_Q$. It needs the jump relations of the layer
  potentials.
* **Theorem 13.1.1, the classical clauses.** For continuous $f$ on a boundary $S$ with a twice
  continuously differentiable parametrization, the interior Dirichlet problem has a unique solution,
  and the interior Neumann problem has a solution, unique up to an additive constant, exactly when
  $\int_S f \, dS = 0$. The book quotes this from its Chapter 8. The Dirichlet problem with
  continuous data needs either an $H^1$ extension of $f$, that is $f \in H^{1/2}(S)$, and the range
  of the trace on a $C^1$ domain is not characterized in this library, or the layer potentials and
  their jump relations. The classical Neumann solution needs boundary regularity of the weak
  solution: the $H^2$ Neumann estimate of `Numlib.Analysis.PDE.Elliptic.Regularity` and a $C^2$
  version of it. Uniqueness for the Dirichlet problem is the maximum principle, Mathlib's
  `HarmonicContOnCl`, and is within reach.
* **Theorem 13.1.2 in the generality of the chapter**, on a multiply connected planar region whose
  boundary is a finite union of piecewise $C^2$ (or $C^1$) Jordan curves with corners. A region
  bounded by curves with corners that are neither straight nor $C^1$ is a Lipschitz domain, and the
  Lipschitz theory is out of scope. Nothing in the formalized part of the chapter depends on it.
* **The exterior Dirichlet and Neumann problems (13.1.14)–(13.1.23)**, for which the book uses the
  Kelvin transform. They rest on the classical clauses of Theorem 13.1.1, and on the removable
  singularity theorem for a bounded harmonic function on a punctured neighbourhood of the origin.
* **Green's representation formula and the jump relations of the layer potentials.** They are planar
  potential theory, which is out of scope.
-/

open Set

namespace AtkinsonHan.Chapter13

open DividedDifference

/-- **Equations (13.1.33)–(13.1.34)** of [han2009theoretical]. Let $r(t) = (\xi(t), \eta(t))$ be a
plane curve. With the first and second divided differences in their Hermite–Genocchi form,
$$\xi[s, t] = \int_0^1 \xi'(t + \theta (s - t)) \, d\theta, \qquad \xi[s, s, t] = \int_0^1 (1 -
\theta) \, \xi''(s + \theta (t - s)) \, d\theta,$$ and the same for $\eta$, the **parametrized
double layer kernel** is $$k(t, s) = \frac{\eta'(s) \, \xi[s, s, t] - \xi'(s) \, \eta[s, s,
t]}{\xi[s, t]^2 + \eta[s, t]^2}.$$

This is the second display of (13.1.33). Off the diagonal it equals the first display of
(13.1.33) (`AtkinsonHan.Chapter13.equation_13_1_33`), because the common factor $(t - s)^2$ of
its numerator and denominator is cancelled. On the diagonal it is minus half the signed
curvature (`AtkinsonHan.Chapter13.equation_13_1_34`). The definition takes the derivatives
$\xi', \eta', \xi'', \eta''$ as arguments, and only they enter. Where the denominator vanishes,
Lean's division gives the value $0$. The divided differences are `DividedDifference.firstOrder`
and `DividedDifference.secondOrder`. -/
noncomputable def doubleLayerKernel (ξ' η' ξ'' η'' : ℝ → ℝ) (t s : ℝ) : ℝ :=
  (η' s * secondOrder ξ'' s t - ξ' s * secondOrder η'' s t) /
    (firstOrder ξ' s t ^ 2 + firstOrder η' s t ^ 2)

variable {ξ η ξ' η' ξ'' η'' : ℝ → ℝ}

/-- **Equation (13.1.33)** of [han2009theoretical]. Let $\xi, \eta : \mathbb{R} \to \mathbb{R}$ be
twice differentiable, with continuous derivatives $\xi', \eta'$ and $\xi'', \eta''$. Then for
$s \neq t$ the kernel is the double layer kernel of the book, $$k(t, s) = \frac{\eta'(s)
(\xi(t) - \xi(s)) - \xi'(s) (\eta(t) - \eta(s))}{(\xi(t) - \xi(s))^2 + (\eta(t) - \eta(s))^2}.$$

Both sides are the same quotient with the common factor $(t - s)^2$ cancelled. So no regularity
or injectivity of the curve is needed, only $s \neq t$; where the chord $r(t) - r(s)$ vanishes,
both sides are $0$. -/
theorem equation_13_1_33 (hξ : ∀ x, HasDerivAt ξ (ξ' x) x) (hξ' : ∀ x, HasDerivAt ξ' (ξ'' x) x)
    (hη : ∀ x, HasDerivAt η (η' x) x) (hη' : ∀ x, HasDerivAt η' (η'' x) x)
    (hcξ' : Continuous ξ') (hcξ'' : Continuous ξ'') (hcη' : Continuous η')
    (hcη'' : Continuous η'') {s t : ℝ} (hst : s ≠ t) :
    doubleLayerKernel ξ' η' ξ'' η'' t s =
      (η' s * (ξ t - ξ s) - ξ' s * (η t - η s)) / ((ξ t - ξ s) ^ 2 + (η t - η s) ^ 2) := by
  have hd : t - s ≠ 0 := sub_ne_zero.2 (Ne.symm hst)
  have hA : ξ t - ξ s = (t - s) * firstOrder ξ' s t := by
    have h := sub_eq_mul_firstOrder hξ hcξ' s t
    linear_combination -h
  have hB : η t - η s = (t - s) * firstOrder η' s t := by
    have h := sub_eq_mul_firstOrder hη hcη' s t
    linear_combination -h
  have hP : ξ' s = firstOrder ξ' s t + (s - t) * secondOrder ξ'' s t := by
    have := sub_firstOrder_eq hξ hξ' hcξ' hcξ'' s t
    linarith
  have hQ : η' s = firstOrder η' s t + (s - t) * secondOrder η'' s t := by
    have := sub_firstOrder_eq hη hη' hcη' hcη'' s t
    linarith
  rw [hA, hB, doubleLayerKernel]
  have hnum : η' s * ((t - s) * firstOrder ξ' s t) - ξ' s * ((t - s) * firstOrder η' s t)
      = (t - s) ^ 2 * (η' s * secondOrder ξ'' s t - ξ' s * secondOrder η'' s t) := by
    rw [hP, hQ]
    ring
  have hden : ((t - s) * firstOrder ξ' s t) ^ 2 + ((t - s) * firstOrder η' s t) ^ 2
      = (t - s) ^ 2 * (firstOrder ξ' s t ^ 2 + firstOrder η' s t ^ 2) := by ring
  rw [hnum, hden, mul_div_mul_left _ _ (pow_ne_zero 2 hd)]

/-- Let $\xi, \eta : \mathbb{R} \to \mathbb{R}$ be twice differentiable, with continuous derivatives
$\xi', \eta'$ and $\xi'', \eta''$, and write the curve as
$r(s) = \xi(s) + i \eta(s) \in \mathbb{C}$. Then for $s \neq t$ the double layer kernel is
$$k(t, s) = -\operatorname{Im} \frac{r'(s)}{r(s) - r(t)}.$$

The quantity $\operatorname{Im}(r'(s) / (r(s) - r(t)))$ is $\frac{d}{ds} \arg(r(s) - r(t))$, so
the kernel is minus the rate at which the direction of the chord from $r(t)$ to $r(s)$ turns. As
in (13.1.33), the identity holds also where the chord vanishes, both sides being $0$ there. This
identity makes (13.2.20) and Exercise 13.2.5 a question of topology: along a counterclockwise
regular simple closed curve the chord direction turns by $\pi$ in total, so
$\int_0^L k(t, s) \, ds = -\pi$, the constant of the integral equation (13.1.32); and $|\int_0^L
k(t, s) \, ds| = \int_0^L |k(t, s)| \, ds$ exactly when the region is convex. Mathlib has
neither a continuous argument along a plane curve nor a turning number, and this is what
Exercise 13.2.5 needs. -/
theorem doubleLayerKernel_eq_neg_im_div (hξ : ∀ x, HasDerivAt ξ (ξ' x) x)
    (hξ' : ∀ x, HasDerivAt ξ' (ξ'' x) x) (hη : ∀ x, HasDerivAt η (η' x) x)
    (hη' : ∀ x, HasDerivAt η' (η'' x) x) (hcξ' : Continuous ξ') (hcξ'' : Continuous ξ'')
    (hcη' : Continuous η') (hcη'' : Continuous η'') {s t : ℝ} (hst : s ≠ t) :
    doubleLayerKernel ξ' η' ξ'' η'' t s
      = -(((ξ' s : ℂ) + (η' s : ℂ) * Complex.I) /
          (((ξ s : ℂ) + (η s : ℂ) * Complex.I) - ((ξ t : ℂ) + (η t : ℂ) * Complex.I))).im := by
  rw [equation_13_1_33 hξ hξ' hη hη' hcξ' hcξ'' hcη' hcη'' hst, Complex.div_im]
  simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.mul_I_re, Complex.mul_I_im, Complex.normSq_apply, zero_add, add_zero,
    neg_zero, div_sub_div_same]
  rw [← neg_div]
  congr 1 <;> ring

/-- **Equation (13.1.34)** of [han2009theoretical]. For all functions $\xi', \eta', \xi'', \eta''$
and every real $t$, the parametrized double layer kernel on the diagonal is $$k(t, t) =
\frac{\eta'(t) \xi''(t) - \xi'(t) \eta''(t)}{2 (\xi'(t)^2 + \eta'(t)^2)}.$$ For a
counterclockwise arclength parametrization the denominator is $2$, and the value is
$-\kappa(t)/2$, with $\kappa$ the signed curvature: on the unit circle $\kappa = 1$ and
$k(t, t) = -1/2$.

**Typo.** The prose of the book after (13.1.34) says that $k(t, t)$ is one-half the curvature,
without the minus sign. The display (13.1.34), which is stated here, is the one that agrees with
(13.1.33) and with the inner normal $n = (-\eta', \xi') / \sqrt{\xi'^2 + \eta'^2}$ that Section
13.1 fixes before (13.1.32). The sign matters: it makes the row integral
$\int_0^L k(t, s) \, ds$ equal to $-\pi$, so that (13.1.32) reads $(-\pi + K) u = g$, the form
of Section 13.2. See `AtkinsonHan.Chapter13.doubleLayerKernel_circle_self`.

At a point where $\xi'(t) = \eta'(t) = 0$, both sides are $0$ by Lean's division. The continuity
of the kernel on the diagonal makes the kernel of a regular $C^2$ curve continuous, and hence
the double layer operator compact. -/
theorem equation_13_1_34 (ξ' η' ξ'' η'' : ℝ → ℝ) (t : ℝ) :
    doubleLayerKernel ξ' η' ξ'' η'' t t =
      (η' t * ξ'' t - ξ' t * η'' t) / (2 * (ξ' t ^ 2 + η' t ^ 2)) := by
  rw [doubleLayerKernel, firstOrder_self, firstOrder_self, secondOrder_self, secondOrder_self,
    show η' t * (ξ'' t / 2) - ξ' t * (η'' t / 2) = (η' t * ξ'' t - ξ' t * η'' t) / 2 from by ring,
    div_div]

/-- For the counterclockwise unit circle $r(t) = (\cos t, \sin t)$, whose signed curvature is $1$,
the parametrized double layer kernel on the diagonal is $k(t, t) = -1/2$ for every $t$.

Off the diagonal, (13.1.33) gives the same constant $-1/2$ wherever the chord does not vanish,
so the row integral over a period is $-\pi$, and (13.1.32) is $(-\pi + K) u = g$, as the book
writes it. This computation fixes the sign of `AtkinsonHan.Chapter13.doubleLayerKernel`: the
prose of the book after (13.1.34), "one-half the curvature", would give $+1/2$ here and the row
integral $+\pi$. The derivatives are passed as $\xi' = -\sin$, $\eta' = \cos$, $\xi'' = -\cos$,
$\eta'' = -\sin$. -/
theorem doubleLayerKernel_circle_self (t : ℝ) :
    doubleLayerKernel (fun x => -Real.sin x) Real.cos (fun x => -Real.cos x)
      (fun x => -Real.sin x) t t = -(1 / 2) := by
  rw [equation_13_1_34]
  show (Real.cos t * -Real.cos t - -Real.sin t * -Real.sin t) /
    (2 * ((-Real.sin t) ^ 2 + Real.cos t ^ 2)) = -(1 / 2)
  rw [show Real.cos t * -Real.cos t - -Real.sin t * -Real.sin t
        = -(Real.sin t ^ 2 + Real.cos t ^ 2) from by ring,
    show (2 : ℝ) * ((-Real.sin t) ^ 2 + Real.cos t ^ 2)
        = 2 * (Real.sin t ^ 2 + Real.cos t ^ 2) from by ring,
    Real.sin_sq_add_cos_sq]
  norm_num

/-- Let $\xi', \eta', \xi'', \eta''$ be continuous, and let $p : X \to \mathbb{R}^2$ be continuous
on a topological space $X$, with $p(x) = (t, s)$. If $\xi[s, t]^2 + \eta[s, t]^2 \neq 0$ at
$p(x)$ for every $x$, then $x \mapsto k(p(x))$ is continuous.

The condition says that $|r(s) - r(t)|^2 / (s - t)^2$ is nonzero: on the diagonal it is the
regularity $\xi'(t)^2 + \eta'(t)^2 > 0$, and off the diagonal it is $r(s) \neq r(t)$. For a
regular simple closed curve of period $L$ it holds for all $s, t$ with $|s - t| < L$, and it
fails where $s - t$ is a nonzero multiple of $L$. -/
theorem continuous_doubleLayerKernel {X : Type*} [TopologicalSpace X] {p : X → ℝ × ℝ}
    (hcξ' : Continuous ξ') (hcξ'' : Continuous ξ'') (hcη' : Continuous η')
    (hcη'' : Continuous η'') (hp : Continuous p)
    (hD : ∀ x : X, firstOrder ξ' (p x).2 (p x).1 ^ 2 + firstOrder η' (p x).2 (p x).1 ^ 2 ≠ 0) :
    Continuous fun x => doubleLayerKernel ξ' η' ξ'' η'' (p x).1 (p x).2 := by
  have hswap : Continuous fun x => ((p x).2, (p x).1) := by fun_prop
  have h1 : Continuous fun x => firstOrder ξ' (p x).2 (p x).1 :=
    (continuous_firstOrder hcξ').comp hswap
  have h2 : Continuous fun x => firstOrder η' (p x).2 (p x).1 :=
    (continuous_firstOrder hcη').comp hswap
  have h3 : Continuous fun x => secondOrder ξ'' (p x).2 (p x).1 :=
    (continuous_secondOrder hcξ'').comp hswap
  have h4 : Continuous fun x => secondOrder η'' (p x).2 (p x).1 :=
    (continuous_secondOrder hcη'').comp hswap
  have hs : Continuous fun x => (p x).2 := continuous_snd.comp hp
  exact Continuous.div (((hcη'.comp hs).mul h3).sub ((hcξ'.comp hs).mul h4))
    ((h1.pow 2).add (h2.pow 2)) hD

/-- Let $a, b \in \mathbb{R}$, and let $\xi', \eta', \xi'', \eta''$ be continuous with
$\xi[s, t]^2 + \eta[s, t]^2 \neq 0$ for all $s, t \in [a, b]$, that is, the curve is regular and
simple on $[a, b]$. This is the parametrized double layer kernel $(t, s) \mapsto k(t, s)$ as a
continuous function on $[a, b] \times [a, b]$, the form that `IntegralOperator.fredholm` takes. -/
noncomputable def doubleLayerKernelCM {a b : ℝ} (ξ' η' ξ'' η'' : ℝ → ℝ) (hcξ' : Continuous ξ')
    (hcξ'' : Continuous ξ'') (hcη' : Continuous η') (hcη'' : Continuous η'')
    (hD : ∀ p : Icc a b × Icc a b,
      firstOrder ξ' (p.2 : ℝ) (p.1 : ℝ) ^ 2 + firstOrder η' (p.2 : ℝ) (p.1 : ℝ) ^ 2 ≠ 0) :
    C(Icc a b × Icc a b, ℝ) :=
  ⟨fun p => doubleLayerKernel ξ' η' ξ'' η'' (p.1 : ℝ) (p.2 : ℝ),
    continuous_doubleLayerKernel (p := fun p : Icc a b × Icc a b => ((p.1 : ℝ), (p.2 : ℝ)))
      hcξ' hcξ'' hcη' hcη'' (by fun_prop) hD⟩

/-- **Section 13.1.3** of [han2009theoretical], compactness of the double layer operator. Let
$a \le b$, and let $\xi', \eta', \xi'', \eta''$ be continuous with
$\xi[s, t]^2 + \eta[s, t]^2 \neq 0$ for all $s, t \in [a, b]$. Then the integral operator $$K
u(t) = \int_a^b k(t, s) \, u(s) \, ds$$ is a compact operator on $C[a, b]$.

This is the last sentence of Section 13.1.3, "the integral operator $K$ is a compact operator
from $C_p(L)$ to $C_p(L)$", on a parameter interval. Given the continuity of the kernel, which
rests on (13.1.34), it is `IntegralOperator.isCompactOperator_fredholm`. -/
theorem isCompactOperator_doubleLayer {a b : ℝ} (hab : a ≤ b) (ξ' η' ξ'' η'' : ℝ → ℝ)
    (hcξ' : Continuous ξ') (hcξ'' : Continuous ξ'') (hcη' : Continuous η')
    (hcη'' : Continuous η'')
    (hD : ∀ p : Icc a b × Icc a b,
      firstOrder ξ' (p.2 : ℝ) (p.1 : ℝ) ^ 2 + firstOrder η' (p.2 : ℝ) (p.1 : ℝ) ^ 2 ≠ 0) :
    IsCompactOperator
      (IntegralOperator.fredholm hab
        (doubleLayerKernelCM ξ' η' ξ'' η'' hcξ' hcξ'' hcη' hcη'' hD)) :=
  IntegralOperator.isCompactOperator_fredholm hab _

/-! ### The descent to a closed curve -/

section Closed

variable {L : ℝ}

/-- If $f'$ has period $L$, then the first divided difference is invariant under the diagonal
translation by $L$: $f[s + L, t + L] = f[s, t]$ for all $s, t$. It supports the descent of the
double layer kernel to a closed curve. -/
theorem firstOrder_add_period {f' : ℝ → ℝ} (hp : Function.Periodic f' L) (s t : ℝ) :
    firstOrder f' (s + L) (t + L) = firstOrder f' s t := by
  refine intervalIntegral.integral_congr fun θ _ => ?_
  rw [show s + L - (t + L) = s - t from by ring,
    show (s - t) * θ + (t + L) = (s - t) * θ + t + L from by ring, hp]

/-- If $f''$ has period $L$, then the second divided difference is invariant under the diagonal
translation by $L$: $f[s + L, s + L, t + L] = f[s, s, t]$ for all $s, t$. It supports the
descent of the double layer kernel to a closed curve. -/
theorem secondOrder_add_period {f'' : ℝ → ℝ} (hp : Function.Periodic f'' L) (s t : ℝ) :
    secondOrder f'' (s + L) (t + L) = secondOrder f'' s t := by
  refine intervalIntegral.integral_congr fun θ _ => ?_
  rw [show t + L - (s + L) = t - s from by ring,
    show (t - s) * θ + (s + L) = (t - s) * θ + s + L from by ring, hp]

/-- Let $\xi', \eta', \xi'', \eta''$ have period $L$. Then the parametrized double layer kernel is
invariant under the diagonal translation: $$k(t + L, s + L) = k(t, s)$$ for all $t, s$.

The kernel is not separately $L$-periodic in either argument: $k(t + L, t) = 0$, while $k(t, t)$
is minus half the signed curvature. The reason is that the divided differences divide by
$s - t$, and $s - t$ and $s - t - L$ are different divisors of the same vanishing chord. So the
kernel on the circle chooses the representative of the difference $s - t$, and it is not the
descent of a biperiodic function. -/
theorem doubleLayerKernel_add_period (hpξ' : Function.Periodic ξ' L)
    (hpη' : Function.Periodic η' L) (hpξ'' : Function.Periodic ξ'' L)
    (hpη'' : Function.Periodic η'' L) (t s : ℝ) :
    doubleLayerKernel ξ' η' ξ'' η'' (t + L) (s + L) = doubleLayerKernel ξ' η' ξ'' η'' t s := by
  rw [doubleLayerKernel, doubleLayerKernel, hpξ', hpη', secondOrder_add_period hpη'',
    secondOrder_add_period hpξ'', firstOrder_add_period hpξ', firstOrder_add_period hpη']

/-- If $f$ is differentiable on $\mathbb{R}$ with derivative $f'$ and $f$ has period $L$, then $f'$
has period $L$. -/
theorem periodic_of_hasDerivAt {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hp : Function.Periodic f L) : Function.Periodic f' L := by
  intro x
  have hshift : (fun y : ℝ => f (y + L)) = f := funext hp
  have h2 : HasDerivAt (fun y : ℝ => f (y + L)) (f' (x + L)) x :=
    HasDerivAt.comp_add_const x L (hf (x + L))
  rw [hshift] at h2
  exact h2.unique (hf x)

/-- **The seam identity.** Let $L > 0$, let $\xi, \eta$ be twice differentiable with continuous
derivatives $\xi', \eta', \xi'', \eta''$, and let $\xi, \eta$ have period $L$. Then for every
$t$, $$k(t, t - L/2) = k(t, t + L/2).$$

The two parameters are the same point of the closed curve, and both are off the diagonal, so
this follows from (13.1.33) and the periodicity of the parametrization. -/
theorem doubleLayerKernel_sub_half_period (hL : 0 < L) (hξ : ∀ x, HasDerivAt ξ (ξ' x) x)
    (hξ' : ∀ x, HasDerivAt ξ' (ξ'' x) x) (hη : ∀ x, HasDerivAt η (η' x) x)
    (hη' : ∀ x, HasDerivAt η' (η'' x) x) (hcξ' : Continuous ξ') (hcξ'' : Continuous ξ'')
    (hcη' : Continuous η') (hcη'' : Continuous η'') (hpξ : Function.Periodic ξ L)
    (hpη : Function.Periodic η L) (t : ℝ) :
    doubleLayerKernel ξ' η' ξ'' η'' t (t - L / 2)
      = doubleLayerKernel ξ' η' ξ'' η'' t (t + L / 2) := by
  have hpξ' : Function.Periodic ξ' L := periodic_of_hasDerivAt hξ hpξ
  have hpη' : Function.Periodic η' L := periodic_of_hasDerivAt hη hpη
  have hne1 : t - L / 2 ≠ t := by intro h; linarith
  have hne2 : t + L / 2 ≠ t := by intro h; linarith
  have hsum : t + L / 2 = (t - L / 2) + L := by ring
  rw [equation_13_1_33 hξ hξ' hη hη' hcξ' hcξ'' hcη' hcη'' hne1,
    equation_13_1_33 hξ hξ' hη hη' hcξ' hcξ'' hcη' hcη'' hne2, hsum, hpξ, hpη, hpξ', hpη']

/-- Let $L > 0$. The parametrized double layer kernel of a closed curve, as a function on the torus
$\mathbb{R}/L\mathbb{Z} \times \mathbb{R}/L\mathbb{Z}$: at a point $(T, S)$ it takes the
representative $t \in [0, L)$ of $T$ and the representative $d \in [-L/2, L/2)$ of $S - T$, and
its value is $k(t, t + d)$.

The choice of the representative of the difference makes this well defined, because the kernel
is invariant under the diagonal translation
(`AtkinsonHan.Chapter13.doubleLayerKernel_add_period`). -/
noncomputable def doubleLayerKernelCPFun (L : ℝ) [Fact (0 < L)] (ξ' η' ξ'' η'' : ℝ → ℝ)
    (p : AddCircle L × AddCircle L) : ℝ :=
  doubleLayerKernel ξ' η' ξ'' η'' (AddCircle.equivIco L 0 p.1)
    ((AddCircle.equivIco L 0 p.1 : ℝ) + (AddCircle.equivIco L (-(L / 2)) (p.2 - p.1) : ℝ))

variable [hL : Fact (0 < L)]

/-- Let $L > 0$. For $t \in [0, L)$ and $u \in [-L/2, L/2)$, the kernel on the torus at the point
$(t, t + u)$ equals the kernel $k(t, t + u)$ on the line. -/
theorem doubleLayerKernelCPFun_coe_of_mem {t u : ℝ} (ht : t ∈ Ico (0 : ℝ) L)
    (hu : u ∈ Ico (-(L / 2)) (L / 2)) :
    doubleLayerKernelCPFun L ξ' η' ξ'' η'' ((t : AddCircle L), ((t + u : ℝ) : AddCircle L))
      = doubleLayerKernel ξ' η' ξ'' η'' t (t + u) := by
  have hd : (((t + u : ℝ) : AddCircle L) - (t : AddCircle L)) = ((u : ℝ) : AddCircle L) := by
    rw [← AddCircle.coe_sub]
    congr 1
    ring
  have ht' : (AddCircle.equivIco L 0 (t : AddCircle L) : ℝ) = t :=
    AddCircle.equivIco_coe_of_mem (by simpa using ht)
  have hu' : (AddCircle.equivIco L (-(L / 2)) (((u : ℝ) : AddCircle L)) : ℝ) = u :=
    AddCircle.equivIco_coe_of_mem (by rw [show -(L / 2) + L = L / 2 from by ring]; exact hu)
  rw [doubleLayerKernelCPFun, hd, ht', hu']

/-- Let $L > 0$, let $\xi, \eta$ be twice differentiable with continuous derivatives
$\xi', \eta', \xi'', \eta''$, let $\xi, \eta$ have period $L$, and let
$\xi[t + u, t]^2 + \eta[t + u, t]^2 \neq 0$ for all $t$ and all $|u| \le L/2$. This is the
**parametrized double layer kernel of the closed curve** as a continuous function on the torus
$\mathbb{R}/L\mathbb{Z} \times \mathbb{R}/L\mathbb{Z}$.

The hypothesis on the divided differences says that the curve is regular and simple: on the
diagonal it is $\xi'(t)^2 + \eta'(t)^2 > 0$, and off the diagonal it is the injectivity of the
parametrization on a half period. This is the form that Section 13.2 uses: $C_p(L)$ is
`C(AddCircle L, ℝ)`, and `IntegralOperator.kernelCLM` of this kernel is the compact operator $K$
of (13.2.4). -/
noncomputable def doubleLayerKernelCP (L : ℝ) [Fact (0 < L)] {ξ η ξ' η' ξ'' η'' : ℝ → ℝ}
    (hξ : ∀ x, HasDerivAt ξ (ξ' x) x) (hξ' : ∀ x, HasDerivAt ξ' (ξ'' x) x)
    (hη : ∀ x, HasDerivAt η (η' x) x) (hη' : ∀ x, HasDerivAt η' (η'' x) x) (hcξ' : Continuous ξ')
    (hcξ'' : Continuous ξ'') (hcη' : Continuous η') (hcη'' : Continuous η'')
    (hpξ : Function.Periodic ξ L) (hpη : Function.Periodic η L)
    (hD : ∀ t u : ℝ, |u| ≤ L / 2 →
      firstOrder ξ' (t + u) t ^ 2
        + firstOrder η' (t + u) t ^ 2 ≠ 0) :
    C(AddCircle L × AddCircle L, ℝ) := by
  refine ⟨doubleLayerKernelCPFun L ξ' η' ξ'' η'', ?_⟩
  have hLpos : 0 < L := Fact.out
  have hpξ' : Function.Periodic ξ' L := periodic_of_hasDerivAt hξ hpξ
  have hpη' : Function.Periodic η' L := periodic_of_hasDerivAt hη hpη
  have hpξ'' : Function.Periodic ξ'' L := periodic_of_hasDerivAt hξ' hpξ'
  have hpη'' : Function.Periodic η'' L := periodic_of_hasDerivAt hη' hpη'
  set Θ : Icc (0 : ℝ) L × Icc (-(L / 2)) (L / 2) → AddCircle L × AddCircle L :=
    fun q => (((q.1 : ℝ) : AddCircle L), (((q.1 : ℝ) + (q.2 : ℝ) : ℝ) : AddCircle L)) with hΘ
  have hcoe : Continuous fun x : ℝ => (x : AddCircle L) := AddCircle.continuous_mk' L
  have hΘc : Continuous Θ := by
    rw [hΘ]
    exact (hcoe.comp (continuous_subtype_val.comp continuous_fst)).prodMk
      (hcoe.comp ((continuous_subtype_val.comp continuous_fst).add
        (continuous_subtype_val.comp continuous_snd)))
  have hΘs : Function.Surjective Θ := by
    rintro ⟨T, S⟩
    have ht : ((AddCircle.equivIco L 0 T : ℝ)) ∈ Ico (0 : ℝ) (0 + L) :=
      (AddCircle.equivIco L 0 T).2
    have hu : ((AddCircle.equivIco L (-(L / 2)) (S - T) : ℝ)) ∈ Ico (-(L / 2)) (-(L / 2) + L) :=
      (AddCircle.equivIco L (-(L / 2)) (S - T)).2
    refine ⟨(⟨(AddCircle.equivIco L 0 T : ℝ), ⟨ht.1, by linarith [ht.2]⟩⟩,
      ⟨(AddCircle.equivIco L (-(L / 2)) (S - T) : ℝ), ⟨hu.1, by linarith [hu.2]⟩⟩), ?_⟩
    have e1 : (((AddCircle.equivIco L 0 T : ℝ)) : AddCircle L) = T := AddCircle.coe_equivIco
    have e2 : ((((AddCircle.equivIco L 0 T : ℝ)
        + (AddCircle.equivIco L (-(L / 2)) (S - T) : ℝ) : ℝ)) : AddCircle L) = S := by
      rw [AddCircle.coe_add, AddCircle.coe_equivIco, AddCircle.coe_equivIco]
      abel
    exact Prod.ext e1 e2
  have hq : Topology.IsQuotientMap Θ := Topology.IsQuotientMap.of_surjective_continuous hΘs hΘc
  rw [hq.continuous_iff]
  -- the composite is the kernel of the line, read on the compact parameter rectangle
  have hIco : (-(L / 2)) ∈ Ico (-(L / 2)) (L / 2) := ⟨le_rfl, by linarith⟩
  have hkey : ∀ q : Icc (0 : ℝ) L × Icc (-(L / 2)) (L / 2),
      doubleLayerKernelCPFun L ξ' η' ξ'' η'' (Θ q)
        = doubleLayerKernel ξ' η' ξ'' η'' (q.1 : ℝ) ((q.1 : ℝ) + (q.2 : ℝ)) := by
    rintro ⟨⟨t, ht⟩, ⟨u, hu⟩⟩
    simp only [hΘ]
    -- reduce the difference to `[-L/2, L/2)`
    have hred : ∀ s : ℝ, s ∈ Ico (0 : ℝ) L →
        doubleLayerKernelCPFun L ξ' η' ξ'' η'' ((s : AddCircle L), ((s + u : ℝ) : AddCircle L))
          = doubleLayerKernel ξ' η' ξ'' η'' s (s + u) := by
      intro s hs
      rcases eq_or_lt_of_le hu.2 with hu2 | hu2
      · have hcoeq : ((s + u : ℝ) : AddCircle L) = ((s + -(L / 2) : ℝ) : AddCircle L) := by
          rw [show s + u = (s + -(L / 2)) + L from by rw [hu2]; ring, AddCircle.coe_add_period]
        rw [hcoeq, doubleLayerKernelCPFun_coe_of_mem hs hIco, hu2,
          show s + -(L / 2) = s - L / 2 from by ring,
          doubleLayerKernel_sub_half_period hLpos hξ hξ' hη hη' hcξ' hcξ'' hcη' hcη'' hpξ hpη s]
      · exact doubleLayerKernelCPFun_coe_of_mem hs ⟨hu.1, hu2⟩
    rcases eq_or_lt_of_le ht.2 with ht2 | ht2
    · have h0 : ((t : ℝ) : AddCircle L) = ((0 : ℝ) : AddCircle L) := by
        rw [ht2]
        simp [AddCircle.coe_period]
      have h1 : ((t + u : ℝ) : AddCircle L) = ((0 + u : ℝ) : AddCircle L) := by
        rw [ht2, show L + u = (0 + u) + L from by ring, AddCircle.coe_add_period]
      have hshift : doubleLayerKernel ξ' η' ξ'' η'' L (L + u)
          = doubleLayerKernel ξ' η' ξ'' η'' 0 (0 + u) := by
        have hs := doubleLayerKernel_add_period hpξ' hpη' hpξ'' hpη'' (0 : ℝ) (0 + u)
        rw [show (0 : ℝ) + L = L from by ring,
          show (0 : ℝ) + u + L = L + u from by ring] at hs
        exact hs
      rw [h0, h1, hred 0 ⟨le_rfl, hLpos⟩, ht2, hshift]
    · exact hred t ⟨ht.1, ht2⟩
  simp only [Function.comp_def, hkey]
  exact continuous_doubleLayerKernel hcξ' hcξ'' hcη' hcη''
    (p := fun q : Icc (0 : ℝ) L × Icc (-(L / 2)) (L / 2) => ((q.1 : ℝ), (q.1 : ℝ) + (q.2 : ℝ)))
    (by fun_prop) fun q => by
      simpa using hD (q.1 : ℝ) (q.2 : ℝ) (abs_le.2 ⟨q.2.2.1, q.2.2.2⟩)

/-- **Section 13.1.3** of [han2009theoretical], compactness of the double layer operator of a closed
curve. Under the hypotheses of `AtkinsonHan.Chapter13.doubleLayerKernelCP`, the integral
operator $$K u(t) = \int_0^L k(t, s) \, u(s) \, ds$$ is a compact operator on $C_p(L)$.

Here $C_p(L)$ is `C(AddCircle L, ℝ)`, and the integral is over the circle with its Haar measure
`MeasureTheory.volume`. The proof is `IntegralOperator.isCompactOperator_kernelCLM`. -/
theorem isCompactOperator_doubleLayerCP (L : ℝ) [Fact (0 < L)] {ξ η ξ' η' ξ'' η'' : ℝ → ℝ}
    (hξ : ∀ x, HasDerivAt ξ (ξ' x) x) (hξ' : ∀ x, HasDerivAt ξ' (ξ'' x) x)
    (hη : ∀ x, HasDerivAt η (η' x) x) (hη' : ∀ x, HasDerivAt η' (η'' x) x) (hcξ' : Continuous ξ')
    (hcξ'' : Continuous ξ'') (hcη' : Continuous η') (hcη'' : Continuous η'')
    (hpξ : Function.Periodic ξ L) (hpη : Function.Periodic η L)
    (hD : ∀ t u : ℝ, |u| ≤ L / 2 →
      firstOrder ξ' (t + u) t ^ 2 + firstOrder η' (t + u) t ^ 2 ≠ 0) :
    IsCompactOperator (IntegralOperator.kernelCLM MeasureTheory.volume
      (doubleLayerKernelCP L hξ hξ' hη hη' hcξ' hcξ'' hcη' hcη'' hpξ hpη hD)) :=
  IntegralOperator.isCompactOperator_kernelCLM _ _

end Closed

/-! ### Section 13.1.2: The Kelvin transform -/

section Kelvin

open InnerProductSpace

/-- **Equations (13.1.10) and (13.1.12)** of [han2009theoretical]. Inversion in the unit circle is
$T(x, y) = (x, y) / r^2$ with $r = |(x, y)|$, an involution of $\mathbb{R}^2 \setminus \{0\}$.
The **Kelvin transform** of a function $u$ on a planar region is $\hat u = u \circ T$.
Identifying the plane with $\mathbb{C}$, $\hat u(x) = u(x / \|x\|^2)$.

The book writes $\hat u(T P) = u(P)$, which is the same because $T \circ T$ is the identity. In
dimension two the transform carries no weight $\|x\|^{2 - d}$, so it is a plain composition. At
$x = 0$, Lean's division gives $\hat u(0) = u(0)$. -/
noncomputable def kelvin (u : ℂ → ℝ) (x : ℂ) : ℝ := u (x / (‖x‖ ^ 2 : ℝ))

/-- For every $z \in \mathbb{C}$, the inversion in the unit circle is $z / \|z\|^2 = (\bar z)^{-1}$.
The identity holds also at $z = 0$, where both sides are $0$. -/
theorem div_norm_sq_eq_inv_conj (z : ℂ) :
    z / ((‖z‖ ^ 2 : ℝ) : ℂ) = ((starRingEnd ℂ) z)⁻¹ := by
  rw [Complex.inv_def, Complex.conj_conj, Complex.normSq_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring

/-- **Equation (13.1.13)** of [han2009theoretical]. Let $x \in \mathbb{C}$ with $x \neq 0$. If
$u : \mathbb{C} \to \mathbb{R}$ is harmonic at the inverse point $T x = x / \|x\|^2$, then the
Kelvin transform $\hat u = u \circ T$ is harmonic at $x$.

The book computes $\Delta \hat u(\xi, \eta) = r^4 \Delta u(x, y)$, which turns the exterior
Dirichlet and Neumann problems on $D_e$ into interior problems on $T(D_e)$. Here
$T z = \overline{z^{-1}}$ is anticonformal, and the proof is that harmonicity survives
composition with an inversion and with a reflection:
`InnerProductSpace.HarmonicAt.comp_analyticAt` and `InnerProductSpace.HarmonicAt.comp_conj`. -/
theorem kelvin_harmonic {u : ℂ → ℝ} {x : ℂ} (hx : x ≠ 0)
    (hu : HarmonicAt u (x / ((‖x‖ ^ 2 : ℝ) : ℂ))) : HarmonicAt (kelvin u) x := by
  have hinv : AnalyticAt ℂ (fun z : ℂ => z⁻¹) x := (analyticAt_id (𝕜 := ℂ) (z := x)).inv hx
  have hconj : HarmonicAt (fun w : ℂ => u ((starRingEnd ℂ) w)) x⁻¹ := by
    refine InnerProductSpace.HarmonicAt.comp_conj ?_
    rwa [map_inv₀, ← div_norm_sq_eq_inv_conj]
  have hcomp := InnerProductSpace.HarmonicAt.comp_analyticAt
    (u := fun w : ℂ => u ((starRingEnd ℂ) w)) (g := fun z : ℂ => z⁻¹) hconj hinv
  have hfun : kelvin u = fun z : ℂ => u ((starRingEnd ℂ) z⁻¹) := by
    funext z
    rw [kelvin, div_norm_sq_eq_inv_conj, map_inv₀]
  rw [hfun]
  exact hcomp

end Kelvin

/-! ### Theorem 13.1.2: The divergence theorem with the inner normal -/

section Divergence

open MeasureTheory TopologicalSpace
open scoped InnerProductSpace

/-- **Theorem 13.1.2** of [han2009theoretical] (divergence theorem), on a bounded $C^1$ domain. Let
$\Omega \subseteq \mathbb{R}^2$ be a bounded open set with $C^1$ boundary $\Gamma$, with the
arclength measure $d\Gamma$ and the inner unit normal $n$. Let
$F : \mathbb{R}^2 \to \mathbb{R}^2$ be continuous on $\bar\Omega$ and $C^1$ up to the boundary.
Then $$\int_\Omega \nabla \cdot F \, d\Omega = -\int_\Gamma F \cdot n \, d\Gamma \qquad
(13.1.4).$$

The theorem is stated on a bounded $C^1$ domain only; the piecewise smooth multiply connected
region of the chapter is not covered. The domain is `IsContDiffDomain 1 Ω`, the measure
$d\Gamma$ is the measure `σ` of the boundary data `hΩ.boundaryData hb`, and the inner normal is
$n = -\nu$, with $\nu$ the outward normal `IsContDiffDomain.outwardNormal`. The proof is the
field `BoundaryData.integral_div_eq` of the boundary data, read with the sign convention of the
chapter. Green's identities (13.1.5)–(13.1.6) follow with $F = u \nabla w$
(`BoundaryData.integral_laplacian_mul_add_eq`), as the chapter derives them. -/
theorem theorem_13_1_2 {Ω : Opens (EuclideanSpace ℝ (Fin 2))}
    (hΩ : IsContDiffDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin 2))))
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin 2))))
    {F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    (hF₀ : ContinuousOn F (closure (Ω : Set (EuclideanSpace ℝ (Fin 2)))))
    (hF₁ : ContDiffOnClosure ℝ 1 F Ω) :
    ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin 2))), EuclideanSpace.div F x
      = -∫ x, ⟪F x, -(hΩ.boundaryData hb).ν x⟫_ℝ ∂(hΩ.boundaryData hb).σ := by
  simp only [inner_neg_right, integral_neg, neg_neg]
  exact (hΩ.boundaryData hb).integral_div_eq F hF₀ hF₁

/-- **Theorem 13.1.2** of [han2009theoretical] (divergence theorem), on a triangulated polygon. Let
$\Omega \subseteq \mathbb{R}^2$ be an open polygon with a triangulation, with the arclength
measure $d\Gamma$ and the inner unit normal $n$ of its boundary. Let
$F : \mathbb{R}^2 \to \mathbb{R}^2$ be continuous on $\bar\Omega$ and $C^1$ up to the boundary.
Then $$\int_\Omega \nabla \cdot F \, d\Omega = -\int_\Gamma F \cdot n \, d\Gamma.$$

This is the polygonal case of the remark of the chapter that boundaries need not be smooth. The
measure and the outward normal $\nu = -n$ are those of `Triangulation.boundaryData`. -/
theorem theorem_13_1_2_polygon {Ω : Opens (EuclideanSpace ℝ (Fin 2))} (𝒯 : Triangulation Ω)
    {F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    (hF₀ : ContinuousOn F (closure (Ω : Set (EuclideanSpace ℝ (Fin 2)))))
    (hF₁ : ContDiffOnClosure ℝ 1 F Ω) :
    ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin 2))), EuclideanSpace.div F x
      = -∫ x, ⟪F x, -𝒯.boundaryData.ν x⟫_ℝ ∂𝒯.boundaryData.σ := by
  simp only [inner_neg_right, integral_neg, neg_neg]
  exact 𝒯.boundaryData.integral_div_eq F hF₀ hF₁

end Divergence

/-! ### Theorem 13.1.1: the weak Neumann problem -/

section Neumann

open MeasureTheory TopologicalSpace
open scoped ContDiff ENNReal InnerProductSpace NNReal

variable {d : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

/-- The Euclidean space $\mathbb{R}^{d+1}$, as a local notation. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin (d + 1))

/-- Let $\Omega \subseteq \mathbb{R}^{d+1}$ be a bounded open set. There is an element of
$H^1(\Omega)$ that is equal to the constant $1$ almost everywhere on $\Omega$ and whose weak
first derivatives all vanish almost everywhere. It supports Theorem 13.1.1, where it is the test
function $v = 1$. -/
theorem exists_one (hb : Bornology.IsBounded (Ω : Set 𝔼)) :
    ∃ one : SobolevEuclidean (d + 1) 1 2 Ω,
      SobolevMultiIndex.fn one =ᵐ[volume.restrict (Ω : Set 𝔼)] (fun _ ↦ (1 : ℝ)) ∧
      ∀ i, (SobolevMultiIndex.weakDeriv one (MultiIndexLE.single i) : 𝔼 → ℝ)
        =ᵐ[volume.restrict (Ω : Set 𝔼)] fun _ ↦ 0 := by
  obtain ⟨one, hone⟩ : ∃ one : SobolevEuclidean (d + 1) 1 2 Ω,
      SobolevMultiIndex.fn one =ᵐ[volume.restrict (Ω : Set 𝔼)] fun _ ↦ (1 : ℝ) :=
    ((contDiffOn_const (c := (1 : ℝ))).contDiffOnClosure Ω.isOpen).memSobolevMultiIndex_of_isBounded
      Ω hb 2 |>.exists_sobolevMultiIndex
  refine ⟨one, hone, fun i ↦ ?_⟩
  have h := Elliptic.weakDeriv_single_ae_eq_fderiv_of_contDiffOn Ω
    (contDiffOn_const (c := (1 : ℝ))) hone i
  filter_upwards [h] with x hx
  simp only [hx, fderiv_fun_const, Pi.zero_apply, zero_apply]

/-- **The Poincaré–Wirtinger inequality.** Let $\Omega \subseteq \mathbb{R}^{d+1}$ be a bounded
connected $C^1$ domain. There is $C > 0$ such that $$\|v\|_{H^1(\Omega)} \le C \|\nabla
v\|_{L^2(\Omega)}$$ for every $v \in H^1(\Omega)$ with $\int_\Omega v = 0$.

It supports Theorem 13.1.1. The proof applies the Deny–Lions inequality
`SobolevEuclidean.exists_norm_le_topSeminorm_add_abs_of_isPreconnected` (Theorem 7.3.12 with the
one seminorm $|\int_\Omega v|$) on the extension domain $\Omega$
(`IsSobolevExtensionDomain.of_isContDiffDomain`): a constant with mean zero on a set of positive
measure is zero. -/
theorem exists_norm_le_gradNorm_of_integral_eq_zero (hΩ : IsContDiffDomain 1 (Ω : Set 𝔼))
    (hb : Bornology.IsBounded (Ω : Set 𝔼)) (hc : IsConnected (Ω : Set 𝔼)) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : SobolevEuclidean (d + 1) 1 2 Ω,
      ∫ x in (Ω : Set 𝔼), SobolevMultiIndex.fn v x = 0 →
        ‖v‖ ≤ C * SobolevMultiIndex.gradNorm v := by
  have hΩo := Ω.isOpen
  have hvol : volume (Ω : Set 𝔼) ≠ ⊤ := hb.measure_lt_top.ne
  have hvolpos : 0 < (volume (Ω : Set 𝔼)).toReal :=
    ENNReal.toReal_pos (hΩo.measure_pos volume hc.nonempty).ne' hvol
  obtain ⟨one, hone, -⟩ := exists_one hb
  -- the mean functional
  obtain ⟨ℓ₀, hℓ₀⟩ : ∃ ℓ₀ : SobolevEuclidean (d + 1) 1 2 Ω →L[ℝ] ℝ,
      ∀ v, ℓ₀ v = ∫ x in (Ω : Set 𝔼), SobolevMultiIndex.fn v x :=
    ⟨Elliptic.load Ω (SobolevMultiIndex.weakDeriv one 0), fun v ↦ by
      rw [Elliptic.load_apply]
      refine integral_congr_ae ?_
      filter_upwards [hone] with x hx
      change SobolevMultiIndex.fn one x * _ = _
      rw [hx, one_mul]⟩
  have hext : IsSobolevExtensionDomain (d + 1) 2 Ω :=
    IsSobolevExtensionDomain.of_isContDiffDomain hΩ
      (hb.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure).isBounded
  -- (H2): a constant of mean zero is zero
  have h2 : ∀ v : SobolevEuclidean (d + 1) 1 2 Ω,
      (∃ q ∈ MvPolynomial.restrictTotalDegree (Fin (d + 1)) ℝ 0,
        SobolevMultiIndex.fn v =ᵐ[volume.restrict (Ω : Set 𝔼)]
          fun x ↦ MvPolynomial.eval (fun i ↦ x i) q) → ℓ₀ v = 0 → v = 0 := by
    rintro v ⟨q, hq, hvq⟩ hℓv
    rw [MvPolynomial.mem_restrictTotalDegree, Nat.le_zero,
      MvPolynomial.totalDegree_eq_zero_iff_eq_C] at hq
    have hvc : SobolevMultiIndex.fn v =ᵐ[volume.restrict (Ω : Set 𝔼)] fun _ ↦ q.coeff 0 := by
      filter_upwards [hvq] with x hx
      rw [hx]
      conv_lhs => rw [hq]
      rw [MvPolynomial.eval_C]
    rw [hℓ₀, integral_congr_ae hvc, setIntegral_const, smul_eq_mul] at hℓv
    have hc0 : q.coeff 0 = 0 :=
      (mul_eq_zero.1 hℓv).resolve_left (by rw [measureReal_def]; exact hvolpos.ne')
    refine SobolevMultiIndex.ext_of_fn_ae_eq (hvc.trans ?_)
    rw [hc0]
    exact SobolevMultiIndex.fn_zero.symm
  have : Fact ((1 : ℝ≥0∞) ≤ ((2 : ℝ≥0) : ℝ≥0∞)) := ⟨by norm_num⟩
  obtain ⟨C, hC, hle⟩ := SobolevEuclidean.exists_norm_le_topSeminorm_add_abs_of_isPreconnected
    (k := 0) (p := 2) hext hvol hc.isPreconnected ℓ₀ fun v hv h0 ↦ h2 v hv h0
  refine ⟨C, hC, fun v hv ↦ ?_⟩
  have h := hle v
  have e : SobolevMultiIndex.topSeminorm ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
      (0 + 1) ((2 : ℝ≥0) : ℝ≥0∞) Ω volume v = SobolevMultiIndex.gradNorm v :=
    SobolevMultiIndex.topSeminorm_one_eq_gradNorm v
  have e2 : ℓ₀ v = 0 := by rw [hℓ₀]; exact hv
  rw [e] at h
  have h' : ‖v‖ ≤ C * (SobolevMultiIndex.gradNorm v + |ℓ₀ v|) := h
  rw [e2, abs_zero, add_zero] at h'
  exact h'

/-- Let $\Omega \subseteq \mathbb{R}^{d+1}$ be a preconnected open set, for example a connected one.
If $w \in H^1(\Omega)$ has $\|\nabla w\|_{L^2(\Omega)} = 0$, then $w$ is equal to a constant
almost everywhere on $\Omega$.

It supports the uniqueness clause of Theorem 13.1.1. The proof is the Deny–Lions theorem at
order one, `SobolevEuclidean.exists_mem_restrictTotalDegree_ae_eq_of_topSeminorm_eq_zero`, with
the polynomials of degree $0$. -/
theorem exists_fn_ae_eq_const_of_gradNorm_eq_zero (hc : IsPreconnected (Ω : Set 𝔼))
    {w : SobolevEuclidean (d + 1) 1 2 Ω} (hw : SobolevMultiIndex.gradNorm w = 0) :
    ∃ c : ℝ, SobolevMultiIndex.fn w =ᵐ[volume.restrict (Ω : Set 𝔼)] fun _ ↦ c := by
  have : Fact ((1 : ℝ≥0∞) ≤ ((2 : ℝ≥0) : ℝ≥0∞)) := ⟨by norm_num⟩
  have htop : SobolevMultiIndex.topSeminorm ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
      (0 + 1) ((2 : ℝ≥0) : ℝ≥0∞) Ω volume w = 0 := by
    have e : SobolevMultiIndex.topSeminorm ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
        (0 + 1) ((2 : ℝ≥0) : ℝ≥0∞) Ω volume w = SobolevMultiIndex.gradNorm w :=
      SobolevMultiIndex.topSeminorm_one_eq_gradNorm w
    rw [e]
    exact hw
  obtain ⟨q, hq, hwq⟩ :=
    SobolevEuclidean.exists_mem_restrictTotalDegree_ae_eq_of_topSeminorm_eq_zero (k := 0) (p := 2)
      hc htop
  rw [MvPolynomial.mem_restrictTotalDegree, Nat.le_zero,
    MvPolynomial.totalDegree_eq_zero_iff_eq_C] at hq
  have hwq' : SobolevMultiIndex.fn w =ᵐ[volume.restrict (Ω : Set 𝔼)]
      fun x ↦ MvPolynomial.eval (fun i ↦ x i) q := hwq
  refine ⟨q.coeff 0, ?_⟩
  filter_upwards [hwq'] with x hx
  rw [hx]
  conv_lhs => rw [hq]
  rw [MvPolynomial.eval_C]

/-- **Lax–Milgram on a kernel.** Let $\Omega \subseteq \mathbb{R}^{d+1}$ be open, let $\ell_0$ be a
bounded linear functional on $H^1(\Omega)$, and let $C > 0$ with $\|v\|_{H^1(\Omega)} \le C
\|\nabla v\|_{L^2(\Omega)}$ for every $v$ with $\ell_0(v) = 0$. Then for every bounded linear
functional $F$ on $H^1(\Omega)$ there is $u_0 \in H^1(\Omega)$ with $$\int_\Omega \nabla u_0
\cdot \nabla v \, dx = F(v) \quad \text{for every } v \text{ with } \ell_0(v) = 0.$$

It supports Theorem 13.1.1. The Dirichlet form $\int_\Omega \nabla u \cdot \nabla v \, dx$ is
`Elliptic.dirichletForm`, and the hypothesis makes it coercive on the kernel of $\ell_0$. The
proof is `IsGalerkinSolution.existsUnique_of_restrict`. -/
theorem exists_forall_dirichletForm_eq_of_ker {ℓ₀ : SobolevEuclidean (d + 1) 1 2 Ω →L[ℝ] ℝ}
    {C : ℝ} (hC : 0 < C)
    (hle : ∀ v : SobolevEuclidean (d + 1) 1 2 Ω, ℓ₀ v = 0 → ‖v‖ ≤ C * SobolevMultiIndex.gradNorm v)
    (F : SobolevEuclidean (d + 1) 1 2 Ω →L[ℝ] ℝ) :
    ∃ u₀ : SobolevEuclidean (d + 1) 1 2 Ω, ∀ v, ℓ₀ v = 0 → Elliptic.dirichletForm Ω u₀ v = F v := by
  have hcoer : ((Elliptic.dirichletForm Ω).restrict
      (LinearMap.ker (ℓ₀ : SobolevEuclidean (d + 1) 1 2 Ω →ₗ[ℝ] ℝ))).IsCoerciveWith
      (C⁻¹ ^ 2) := by
    rintro ⟨v, hv⟩
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hv
    have h1 := hle v hv
    have h2 : C⁻¹ * ‖v‖ ≤ SobolevMultiIndex.gradNorm v := by
      rw [inv_mul_le_iff₀ hC]
      exact h1
    simp only [SesqForm.restrict_apply, RCLike.re_to_real,
      Elliptic.dirichletForm_self_eq_gradNorm_sq]
    calc C⁻¹ ^ 2 * ‖v‖ ^ 2 = (C⁻¹ * ‖v‖) ^ 2 := by ring
      _ ≤ SobolevMultiIndex.gradNorm v ^ 2 := by gcongr
  have : CompleteSpace (LinearMap.ker (ℓ₀ : SobolevEuclidean (d + 1) 1 2 Ω →ₗ[ℝ] ℝ)) :=
    ℓ₀.isClosed_ker.completeSpace_coe
  obtain ⟨u₀, ⟨-, hu₀⟩, -⟩ := IsGalerkinSolution.existsUnique_of_restrict (ℓ := F)
    (by positivity) hcoer
  exact ⟨u₀, fun v hv ↦ hu₀ v (by rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]; exact hv)⟩

/-- **Lax–Milgram for the weak Neumann problem.** Let $\Omega \subseteq \mathbb{R}^{d+1}$ be a
bounded connected $C^1$ domain. Let $1 \in H^1(\Omega)$ denote an element that is equal to the
constant $1$ almost everywhere and satisfies $\int_\Omega \nabla u \cdot \nabla 1 \, dx = 0$ for
all $u \in H^1(\Omega)$. Let $F$ be a bounded linear functional on $H^1(\Omega)$ with
$F(1) = 0$. Then there is $u_0 \in H^1(\Omega)$ with $$\int_\Omega \nabla u_0 \cdot \nabla v \,
dx = F(v) \quad \text{for all } v \in H^1(\Omega).$$

It supports Theorem 13.1.1. The proof applies Lax–Milgram on the closed subspace of functions
with mean zero, where the Dirichlet form is coercive by the Poincaré–Wirtinger inequality
(`AtkinsonHan.Chapter13.exists_norm_le_gradNorm_of_integral_eq_zero` and
`AtkinsonHan.Chapter13.exists_forall_dirichletForm_eq_of_ker`), and the decomposition
$v = v_0 + c \cdot 1$ with $c = (\int_\Omega v) / |\Omega|$. -/
theorem exists_forall_dirichletForm_eq (hΩ : IsContDiffDomain 1 (Ω : Set 𝔼))
    (hb : Bornology.IsBounded (Ω : Set 𝔼)) (hc : IsConnected (Ω : Set 𝔼))
    {one : SobolevEuclidean (d + 1) 1 2 Ω}
    (hone : SobolevMultiIndex.fn one =ᵐ[volume.restrict (Ω : Set 𝔼)] fun _ ↦ (1 : ℝ))
    (hd1 : ∀ u : SobolevEuclidean (d + 1) 1 2 Ω, Elliptic.dirichletForm Ω u one = 0)
    (F : SobolevEuclidean (d + 1) 1 2 Ω →L[ℝ] ℝ) (hF1 : F one = 0) :
    ∃ u₀ : SobolevEuclidean (d + 1) 1 2 Ω, ∀ v, Elliptic.dirichletForm Ω u₀ v = F v := by
  have hΩo := Ω.isOpen
  have hvol : volume (Ω : Set 𝔼) ≠ ⊤ := hb.measure_lt_top.ne
  have hvolpos : 0 < (volume (Ω : Set 𝔼)).toReal :=
    ENNReal.toReal_pos (hΩo.measure_pos volume hc.nonempty).ne' hvol
  -- the mean functional
  obtain ⟨ℓ₀, hℓ₀⟩ : ∃ ℓ₀ : SobolevEuclidean (d + 1) 1 2 Ω →L[ℝ] ℝ,
      ∀ v, ℓ₀ v = ∫ x in (Ω : Set 𝔼), SobolevMultiIndex.fn v x :=
    ⟨Elliptic.load Ω (SobolevMultiIndex.weakDeriv one 0), fun v ↦ by
      rw [Elliptic.load_apply]
      refine integral_congr_ae ?_
      filter_upwards [hone] with x hx
      change SobolevMultiIndex.fn one x * _ = _
      rw [hx, one_mul]⟩
  have hℓ₀one : ℓ₀ one = (volume (Ω : Set 𝔼)).toReal := by
    rw [hℓ₀, integral_congr_ae hone, setIntegral_const, smul_eq_mul, mul_one]
    rfl
  obtain ⟨C, hC, hle⟩ := exists_norm_le_gradNorm_of_integral_eq_zero hΩ hb hc
  obtain ⟨u₀, hu₀⟩ := exists_forall_dirichletForm_eq_of_ker hC
    (fun v hv ↦ hle v (by rw [← hℓ₀]; exact hv)) F
  refine ⟨u₀, fun v ↦ ?_⟩
  -- `v = v₀ + c 1` with `v₀` of mean zero
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = ℓ₀ v / ℓ₀ one := ⟨_, rfl⟩
  have hℓ₀one' : ℓ₀ one ≠ 0 := by rw [hℓ₀one]; exact hvolpos.ne'
  have hv₀ : ℓ₀ (v - c • one) = 0 := by
    simp only [ℓ₀.map_sub v (c • one), ℓ₀.map_smul c one, smul_eq_mul]
    rw [hcdef, div_mul_cancel₀ _ hℓ₀one', sub_self]
  have e1 : Elliptic.dirichletForm Ω u₀ (v - c • one)
      = Elliptic.dirichletForm Ω u₀ v - c * Elliptic.dirichletForm Ω u₀ one := by
    simp only [(Elliptic.dirichletForm Ω u₀).map_sub v (c • one),
      (Elliptic.dirichletForm Ω u₀).map_smul c one, smul_eq_mul]
  have e2 : F (v - c • one) = F v - c * F one := by
    simp only [F.map_sub v (c • one), F.map_smul c one, smul_eq_mul]
  have e3 := hu₀ _ hv₀
  rw [e1, e2, hd1, hF1] at e3
  linarith

/-- **Theorem 13.1.1** of [han2009theoretical], the Neumann clause in weak form. Let
$\Omega \subseteq \mathbb{R}^{d+1}$ be a bounded connected $C^1$ domain with boundary $\Gamma$,
surface measure $\sigma$ and trace $\gamma : H^1(\Omega) \to L^2(\sigma)$. Let
$f \in L^2(\sigma)$. Then the weak Neumann problem (13.1.2) for $\Delta u = 0$ in $\Omega$,
$\partial u / \partial n = f$ on $\Gamma$, that is, to find $u \in H^1(\Omega)$ with
$$\int_\Omega \nabla u \cdot \nabla v \, dx = \int_\Gamma f \, \gamma v \, d\sigma \quad
\text{for all } v \in H^1(\Omega),$$ has a solution if and only if $$\int_\Gamma f \, d\sigma =
0 \qquad (13.1.3).$$ Any two solutions $u, u'$ satisfy $u' = u + c$ almost everywhere on
$\Omega$ for a constant $c$.

**Reading.** The book states Theorem 13.1.1 for the classical Neumann problem with continuous
data on a region with a $C^2$ boundary curve, and quotes it from its Chapter 8. Here it is the
weak problem with data in $L^2(\sigma)$, on a bounded connected $C^1$ domain in any dimension;
the plane case contains the region of the chapter. The classical clauses of the theorem are not
formalized.

The measure $\sigma$ is `hΩ.boundaryMeasure hb` and the trace is `hΩ.traceL hb 2`. The proof
tests with $v = 1$ for the necessity. The existence is
`AtkinsonHan.Chapter13.exists_forall_dirichletForm_eq`, because
$v \mapsto \int_\Gamma f \, \gamma v \, d\sigma$ is bounded and vanishes on the constants when
$\int_\Gamma f \, d\sigma = 0$. For the uniqueness, two solutions differ by $w$ with
$\int_\Omega |\nabla w|^2 = 0$, which is a constant on the connected $\Omega$
(`AtkinsonHan.Chapter13.exists_fn_ae_eq_const_of_gradNorm_eq_zero`). -/
theorem theorem_13_1_1_neumann_weak (hΩ : IsContDiffDomain 1 (Ω : Set 𝔼))
    (hb : Bornology.IsBounded (Ω : Set 𝔼)) (hc : IsConnected (Ω : Set 𝔼))
    (f : Lp ℝ 2 (hΩ.boundaryMeasure hb)) :
    ((∃ u : SobolevEuclidean (d + 1) 1 2 Ω, ∀ v : SobolevEuclidean (d + 1) 1 2 Ω,
        ∫ x in (Ω : Set 𝔼), ∑ i, SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x
          * SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i) x
        = ∫ x, f x * (hΩ.traceL hb 2 ENNReal.ofNat_ne_top v : 𝔼 → ℝ) x ∂(hΩ.boundaryMeasure hb))
      ↔ ∫ x, f x ∂(hΩ.boundaryMeasure hb) = 0) ∧
    ∀ u u' : SobolevEuclidean (d + 1) 1 2 Ω,
      (∀ v : SobolevEuclidean (d + 1) 1 2 Ω,
        ∫ x in (Ω : Set 𝔼), ∑ i, SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x
          * SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i) x
        = ∫ x, f x * (hΩ.traceL hb 2 ENNReal.ofNat_ne_top v : 𝔼 → ℝ) x
            ∂(hΩ.boundaryMeasure hb)) →
      (∀ v : SobolevEuclidean (d + 1) 1 2 Ω,
        ∫ x in (Ω : Set 𝔼), ∑ i, SobolevMultiIndex.weakDeriv u' (MultiIndexLE.single i) x
          * SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i) x
        = ∫ x, f x * (hΩ.traceL hb 2 ENNReal.ofNat_ne_top v : 𝔼 → ℝ) x
            ∂(hΩ.boundaryMeasure hb)) →
      ∃ c : ℝ, SobolevMultiIndex.fn u' =ᵐ[volume.restrict (Ω : Set 𝔼)]
        fun x ↦ SobolevMultiIndex.fn u x + c := by
  obtain ⟨one, hone, hdone⟩ := exists_one hb
  have hγone : (hΩ.traceL hb 2 ENNReal.ofNat_ne_top one : 𝔼 → ℝ) =ᵐ[hΩ.boundaryMeasure hb]
      fun _ ↦ (1 : ℝ) :=
    hΩ.traceL_ae_eq_of_continuousOn hb 2 ENNReal.ofNat_ne_top one hone continuousOn_const
  -- the Dirichlet form vanishes against `1`
  have hd1 : ∀ u : SobolevEuclidean (d + 1) 1 2 Ω, Elliptic.dirichletForm Ω u one = 0 := by
    intro u
    rw [Elliptic.dirichletForm_apply]
    rw [← integral_zero 𝔼 ℝ (μ := volume.restrict (Ω : Set 𝔼))]
    refine integral_congr_ae ?_
    filter_upwards [ae_all_iff.2 hdone] with x hx
    simp only [hx, mul_zero, Finset.sum_const_zero]
  -- the boundary functional `v ↦ ∫ f γv dσ`
  obtain ⟨Fσ, hFσ⟩ : ∃ Fσ : SobolevEuclidean (d + 1) 1 2 Ω →L[ℝ] ℝ,
      ∀ v, Fσ v = ∫ x, f x * (hΩ.traceL hb 2 ENNReal.ofNat_ne_top v : 𝔼 → ℝ) x
        ∂(hΩ.boundaryMeasure hb) :=
    ⟨(innerSL ℝ f).comp (hΩ.traceL hb 2 ENNReal.ofNat_ne_top), fun v ↦ by
      rw [ContinuousLinearMap.comp_apply, innerSL_apply_apply, L2.inner_eq_integral_mul]⟩
  have hFσone : Fσ one = ∫ x, f x ∂(hΩ.boundaryMeasure hb) := by
    rw [hFσ]
    refine integral_congr_ae ?_
    filter_upwards [hγone] with x hx
    rw [hx, mul_one]
  -- the problem in the backbone's vocabulary
  have hsol : ∀ u : SobolevEuclidean (d + 1) 1 2 Ω,
      (∀ v : SobolevEuclidean (d + 1) 1 2 Ω,
        ∫ x in (Ω : Set 𝔼), ∑ i, SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x
          * SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i) x
        = ∫ x, f x * (hΩ.traceL hb 2 ENNReal.ofNat_ne_top v : 𝔼 → ℝ) x
            ∂(hΩ.boundaryMeasure hb)) ↔
      ∀ v, Elliptic.dirichletForm Ω u v = Fσ v := fun u ↦ by
    simp only [Elliptic.dirichletForm_apply, hFσ]
  simp only [hsol]
  refine ⟨⟨fun ⟨u, hu⟩ ↦ ?_, fun hf ↦ ?_⟩, fun u u' hu hu' ↦ ?_⟩
  · -- necessity: test with `v = 1`
    rw [← hFσone, ← hu one, hd1]
  · -- existence
    exact exists_forall_dirichletForm_eq hΩ hb hc hone hd1 Fσ (hFσone.trans hf)
  · -- uniqueness up to a constant
    obtain ⟨w, hwdef⟩ : ∃ w : SobolevEuclidean (d + 1) 1 2 Ω, w = u' - u := ⟨_, rfl⟩
    have hw : ∀ v, Elliptic.dirichletForm Ω w v = 0 := fun v ↦ by
      rw [hwdef, map_sub, sub_apply, hu v, hu' v, sub_self]
    have hgrad : SobolevMultiIndex.gradNorm w = 0 := by
      have h := hw w
      rw [Elliptic.dirichletForm_self_eq_gradNorm_sq] at h
      exact pow_eq_zero_iff two_ne_zero |>.1 h
    obtain ⟨c, hwc⟩ := exists_fn_ae_eq_const_of_gradNorm_eq_zero hc.isPreconnected hgrad
    refine ⟨c, ?_⟩
    have e : u' = u + w := by rw [hwdef, add_sub_cancel]
    rw [e]
    filter_upwards [SobolevMultiIndex.fn_add u w, hwc] with x hx hx'
    rw [hx, Pi.add_apply, hx']

end Neumann

end AtkinsonHan.Chapter13
