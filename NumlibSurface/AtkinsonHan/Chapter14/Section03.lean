/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Approximation.DiskQuadrature
import Numlib.Approximation.Hyperinterpolation
import NumlibSurface.AtkinsonHan.Chapter14.Section02

/-!
# Atkinson and Han, Section 14.3: Hyperinterpolation

This module formalizes Section 14.3 of [han2009theoretical]. Hyperinterpolation is the orthogonal
projection $P_n$ of Section 14.2 with its integrals replaced by a quadrature rule. A rule with
weights $w_k$ and nodes $x_k$ gives the discrete inner product
$(f, g)_n = \sum_k w_k f(x_k) g(x_k)$. If the rule is exact on $\Pi_{2n}^d$, then
$(p, q)_n = (p, q)$ for $p, q \in \Pi_n^d$ (14.3.3). The hyperinterpolation operator $L_n f =
\sum_{m \le n} \sum_\ell (f, \varphi_{m,\ell})_n \, \varphi_{m,\ell}$ (14.3.4) is then a linear
projection onto $\Pi_n^d$ (14.3.5). The book builds one rule on the disk (14.3.1), Gauss–Legendre in
the radius and the trapezoidal rule in the angle, and this rule is exact on $\Pi_{2n}^2$.

The general statements are the backbone `Numlib.Approximation.Hyperinterpolation`, and the disk rule
is `Numlib.Approximation.DiskQuadrature`.

## Main definitions

* (14.3.4), `AtkinsonHan.Chapter14.hyperinterpolation`: the hyperinterpolation operator $L_n$.

## Main results

* (14.3.1), `AtkinsonHan.Chapter14.equation_14_3_1`: the disk rule has positive weights, radial
  nodes in $(0, 1)$, and is exact on $\Pi_{2n}^2$.
* (14.3.3), `AtkinsonHan.Chapter14.equation_14_3_3`: a rule exact on $\Pi_{2n}^d$ has
  $(p, q)_n = (p, q)$ for $p, q \in \Pi_n^d$.
* (14.3.4), `AtkinsonHan.Chapter14.hyperinterpolation_mem`: $L_n f \in \Pi_n^d$, with
  `AtkinsonHan.Chapter14.hyperinterpolation_add` and `AtkinsonHan.Chapter14.hyperinterpolation_smul`
  for the linearity.
* (14.3.5) and Exercise 14.3.1, `AtkinsonHan.Chapter14.equation_14_3_5`: $L_n p = p$ for every
  $p \in \Pi_n^d$, with `AtkinsonHan.Chapter14.equation_14_3_5_idem` for the idempotence.

## Conventions

* The family $\{\varphi_{m,\ell} : m \le n\}$ of the book is one family `φ` of polynomials,
  orthonormal in $L^2(\mu)$ and spanning $\Pi_n^d$. By Lemma 14.2.1, this is what orthonormal bases
  of the spaces $\mathcal{V}_m^d$, $m \le n$, give together.
* Exactness of a rule on $\Pi_m^d$ is `Approximation.IsExactOn μ w x m`, and the discrete inner
  product is `Approximation.discreteInner w x`.

## Deviations from the source

* **(14.3.3)–(14.3.5)** (generalization). The book uses its rule (14.3.1) on the disk. The results
  hold for every quadrature rule exact on $\Pi_{2n}^d$, for every weight measure on $\mathbb{R}^d$.
  See `AtkinsonHan.Chapter14.equation_14_3_3`.
* **(14.3.1)** (correction). The book states that the rule is exact on $\Pi_{2n+1}^2$. It is exact
  on $\Pi_{2n}^2$ only; for $n = 1$ it does not integrate $x^3$ exactly. See
  `AtkinsonHan.Chapter14.equation_14_3_1`.

## Not formalized

* **Section 14.3.1, (14.3.6)–(14.3.7)**, $\|L_n\|_{C \to C} = O(n \log n)$. It reduces to the same
  estimate on Jacobi polynomials as Theorem 14.2.4, with a discretization on top, and Mathlib has no
  Jacobi or Gegenbauer polynomials.
-/

open Approximation MeasureTheory MvPolynomial

namespace AtkinsonHan.Chapter14

variable {d N : ℕ} {K : Type*} [Fintype K] {μ : Measure (Fin d → ℝ)} {w : K → ℝ}
  {x : K → (Fin d → ℝ)} {φ : Fin N → MvPolynomial (Fin d) ℝ} {n : ℕ}

/-- **Equation (14.3.3)** of [han2009theoretical]. Let $\mu$ be a weight for polynomials on
$\mathbb{R}^d$, and let a quadrature rule with weights $w_k$ and nodes $x_k$ be exact for $\mu$
on $\Pi_{2n}^d$. Then for all $p, q \in \Pi_n^d$, $$(p, q)_n = \sum_k w_k \, p(x_k) \, q(x_k) =
\int p \, q \, d\mu = (p, q).$$

The reason is that $p q \in \Pi_{2n}^d$. The section rests on this identity.

**Reading.** Arbitrary quadrature exact to degree 2n for any admissible weight instead of the disk
rule.
-/
theorem equation_14_3_3 (hw : IsMvWeight μ) (hex : IsExactOn μ w x (2 * n))
    {p q : MvPolynomial (Fin d) ℝ} (hp : p ∈ polySpace d n) (hq : q ∈ polySpace d n) :
    discreteInner w x p q = inner ℝ (hw.toL2 p) (hw.toL2 q) :=
  discreteInner_eq_inner_toL2 hw hex (mem_polySpace_iff.1 hp) (mem_polySpace_iff.1 hq)

/-- **Equation (14.3.4)** of [han2009theoretical]. Let a quadrature rule have weights $w_k$ and
nodes $x_k$, and let $\varphi_1, \dots, \varphi_N$ be polynomials. The **hyperinterpolation
operator** maps a function $f : \mathbb{R}^d \to \mathbb{R}$ to the polynomial $$L_n f =
\sum_{i=1}^{N} (f, \varphi_i)_n \, \varphi_i, \qquad (f, \varphi_i)_n = \sum_k w_k \, f(x_k) \,
\varphi_i(x_k).$$

The book takes for $\varphi$ an orthonormal basis of $\Pi_n^d$, written $\{\varphi_{m,\ell}\}$;
the definition takes any finite family, and the theorems add the hypotheses. The definition is
`Approximation.hyperinterp`.

**Reading.** Arbitrary finite samples and polynomial family, with a total function as input.
-/
noncomputable def hyperinterpolation (w : K → ℝ) (x : K → (Fin d → ℝ))
    (φ : Fin N → MvPolynomial (Fin d) ℝ) (f : (Fin d → ℝ) → ℝ) : MvPolynomial (Fin d) ℝ :=
  hyperinterp w x φ f

/-- **Equation (14.3.4)** of [han2009theoretical]. If the family $\varphi$ spans $\Pi_n^d$, then
$L_n f \in \Pi_n^d$ for every function $f$.

**Reading.** Polynomial range follows from the supplied span for any quadrature family.
-/
theorem hyperinterpolation_mem (hspan : Submodule.span ℝ (Set.range φ) = polySpace d n)
    (f : (Fin d → ℝ) → ℝ) : hyperinterpolation w x φ f ∈ polySpace d n :=
  hspan ▸ hyperinterp_mem_span w x φ f

/-- **Equation (14.3.4)** of [han2009theoretical]. The operator $L_n$ is additive:
$L_n(f + g) = L_n f + L_n g$.

**Reading.** Additivity for the abstract quadrature construction.
-/
theorem hyperinterpolation_add (f g : (Fin d → ℝ) → ℝ) :
    hyperinterpolation w x φ (f + g) = hyperinterpolation w x φ f + hyperinterpolation w x φ g :=
  hyperinterp_add w x φ f g

/-- **Equation (14.3.4)** of [han2009theoretical]. The operator $L_n$ is homogeneous:
$L_n(c f) = c \, L_n f$ for every $c \in \mathbb{R}$.

**Reading.** Homogeneity for the abstract quadrature construction.
-/
theorem hyperinterpolation_smul (c : ℝ) (f : (Fin d → ℝ) → ℝ) :
    hyperinterpolation w x φ (c • f) = c • hyperinterpolation w x φ f :=
  hyperinterp_smul w x φ c f

/-- **Equation (14.3.5)** of [han2009theoretical], which is **Exercise 14.3.1**. Let $\mu$ be a
weight for polynomials on $\mathbb{R}^d$, let the quadrature rule be exact for $\mu$ on
$\Pi_{2n}^d$, and let $\varphi_1, \dots, \varphi_N$ be polynomials that span $\Pi_n^d$ and are
orthonormal in $L^2(\mu)$. Then $$L_n p = p \qquad \text{for every } p \in \Pi_n^d.$$

On $\Pi_n^d$ the discrete inner product is the continuous one by (14.3.3), so $L_n$ agrees there
with the orthogonal projection $P_n$, which is the identity on $\Pi_n^d$. With
`AtkinsonHan.Chapter14.hyperinterpolation_mem` and the linearity, $L_n$ is a linear projection
onto $\Pi_n^d$.

**Reading.** Reproduction for exact degree-2n quadrature on an arbitrary admissible weight.
-/
theorem equation_14_3_5 (hw : IsMvWeight μ) (hex : IsExactOn μ w x (2 * n))
    (hspan : Submodule.span ℝ (Set.range φ) = polySpace d n)
    (horth : Orthonormal ℝ fun i => hw.toL2 (φ i)) {p : MvPolynomial (Fin d) ℝ}
    (hp : p ∈ polySpace d n) :
    hyperinterpolation w x φ (fun y => eval y p) = p :=
  hyperinterp_eq_self hw hex
    (fun i => mem_polySpace_iff.1 (hspan ▸ Submodule.subset_span ⟨i, rfl⟩))
    horth (mem_polySpace_iff.1 hp) (hspan ▸ hp)

/-- **Equation (14.3.5)** of [han2009theoretical], idempotence. Under the hypotheses of
`AtkinsonHan.Chapter14.equation_14_3_5`, $L_n(L_n f) = L_n f$ for every function
$f : \mathbb{R}^d \to \mathbb{R}$, where $L_n$ is applied to the values of the polynomial
$L_n f$.

**Reading.** Idempotence on the abstract quadrature setting.
-/
theorem equation_14_3_5_idem (hw : IsMvWeight μ) (hex : IsExactOn μ w x (2 * n))
    (hspan : Submodule.span ℝ (Set.range φ) = polySpace d n)
    (horth : Orthonormal ℝ fun i => hw.toL2 (φ i)) (f : (Fin d → ℝ) → ℝ) :
    hyperinterpolation w x φ (fun y => eval y (hyperinterpolation w x φ f)) =
      hyperinterpolation w x φ f :=
  equation_14_3_5 hw hex hspan horth (hyperinterpolation_mem hspan f)

/-- **Equation (14.3.1)** of [han2009theoretical], the quadrature rule on the unit disk. For every
$n \in \mathbb{N}$ there are radial nodes $r_0, \dots, r_n \in (0, 1)$ and weights
$\omega_0, \dots, \omega_n > 0$ such that the rule $$\int_{\mathbb{B}_2} f \approx
\frac{2\pi}{2n + 1} \sum_{l=0}^{n} \sum_{m=0}^{2n} \omega_l \, r_l \, f(r_l \cos \theta_m, r_l
\sin \theta_m), \qquad \theta_m = \frac{2 \pi m}{2n + 1},$$ is exact on $\Pi_{2n}^2$. So all
$(n + 1)(2n + 1)$ weights $(2\pi / (2n + 1)) \, \omega_l r_l$ are positive.

**Correction.** The book states that the rule is exact on $\Pi_{2n+1}^2$. It is exact on
$\Pi_{2n}^2$ and not further. For $n = 1$ and $f = x^3$, the integral over the disk is $0$ by
symmetry, but the rule gives about $0.3055$. The reason is that $\cos^a \theta \sin^b \theta$
with $a + b = 2n + 1$ contains the frequencies $\pm(2n + 1)$, which the $2n + 1$ equispaced
angles do not annihilate; `Numlib.Approximation.DiskQuadrature` gives the mechanism. Nothing in
the chapter is weakened: (14.3.3), the only use of (14.3.1) in the book, applies the rule to
products of two elements of $\Pi_n^2$, and needs only $\Pi_{2n}^2$.

The nodes and weights $(r_l, \omega_l)$ come from the $(n + 1)$-point Gauss–Legendre rule on
$[0, 1]$. The angles are `Quadrature.angleNode (2 * n + 1) m`. Exactness on $\Pi_{2n}^2$ is the
hypothesis of `AtkinsonHan.Chapter14.equation_14_3_3`, and hence of (14.3.4) and (14.3.5), so
this rule is an instance of the whole section. -/
theorem equation_14_3_1 (n : ℕ) :
    ∃ ρ ω : Fin (n + 1) → ℝ, (∀ l, ρ l ∈ Set.Ioo (0 : ℝ) 1) ∧ (∀ l, 0 < ω l) ∧
      IsExactOn (MeasureTheory.volume.restrict Quadrature.unitDisk)
        (fun k : Fin (n + 1) × Fin (2 * n + 1) => 2 * Real.pi / (2 * n + 1) * (ω k.1 * ρ k.1))
        (fun k : Fin (n + 1) × Fin (2 * n + 1) =>
          ![ρ k.1 * Real.cos (Quadrature.angleNode (2 * n + 1) k.2),
            ρ k.1 * Real.sin (Quadrature.angleNode (2 * n + 1) k.2)])
        (2 * n) :=
  Quadrature.exists_diskRule n

end AtkinsonHan.Chapter14
