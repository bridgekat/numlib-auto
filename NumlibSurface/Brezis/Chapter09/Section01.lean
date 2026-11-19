/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Normed.Affine.Convex
import Numlib.Analysis.Sobolev.Calculus
import Numlib.Analysis.Sobolev.Friedrichs
import NumlibSurface.Brezis.Chapter03.Section05
import NumlibSurface.Brezis.Chapter03.Section06
import NumlibSurface.Brezis.Chapter04.Section03
import NumlibSurface.Brezis.Chapter04.Section04

/-!
# Brezis, Section 9.1: Definition and elementary properties of the Sobolev spaces $W^{1,p}(\Omega)$

This module formalizes Section 9.1 of [brezis2011functional], together with the closing paragraph
"The spaces $W^{m,p}(\Omega)$", on an open set $\Omega \subseteq \mathbb{R}^N$ with Lebesgue
measure. For $1 \le p \le \infty$ the Sobolev space $W^{1,p}(\Omega)$ consists of the functions
$u \in L^p(\Omega)$ that have weak partial derivatives $\partial u / \partial x_i \in L^p(\Omega)$,
that is, functions $g_i \in L^p(\Omega)$ with $\int_\Omega u \, \partial \varphi / \partial x_i =
-\int_\Omega g_i \varphi$ for every $\varphi \in C_c^\infty(\Omega)$. The source equips it with the
norm $\|u\|_p + \sum_i \|\partial u / \partial x_i\|_p$, and $H^1(\Omega) = W^{1,2}(\Omega)$ with
the scalar product $(u, v)_{H^1} = \int_\Omega uv + \sum_i \int_\Omega \partial_i u \, \partial_i
v$. The module proves that $W^{1,p}(\Omega)$ is a Banach space, reflexive for $1 < p < \infty$ and
separable for $p < \infty$ (Proposition 9.1), Friedrichs' approximation theorem (Theorem 9.2), the
characterizations of $W^{1,p}(\Omega)$ by duality and by translations (Proposition 9.3), the rules
for products, compositions and changes of variables (Propositions 9.4–9.6), and the elementary
properties of the spaces $W^{m,p}(\Omega)$.

The proofs specialize the backbone modules `Numlib.Analysis.Sobolev.MultiIndex`,
`Numlib.Analysis.Sobolev.Calculus` and `Numlib.Analysis.Sobolev.Friedrichs`. The backbone states its
theorems over a general finite-dimensional space with a Haar measure. This module instantiates them
on $\mathbb{R}^N$ and converts between the derivative as a field of linear maps and the partial
derivatives (`Brezis.Chapter09.exists_hasWeakFDerivOn_fn_gradient`).

## Main definitions

* Section 9.1, definition of $W^{1,p}(\Omega)$, `Brezis.Chapter09.sobolevSpace`: the functions of
  $L^p(\Omega)$ with weak partial derivatives in $L^p(\Omega)$, with the weak partial derivatives
  `Brezis.Chapter09.partialDeriv` and the gradient `Brezis.Chapter09.gradient`.
* Section 9.1, definition of $H^1(\Omega)$, `Brezis.Chapter09.hSpace`: the space $W^{1,2}(\Omega)$.
* Section 9.1, the norm of $W^{1,p}(\Omega)$, `Brezis.Chapter09.bookNorm`: $\|u\|_p + \sum_i
  \|\partial u / \partial x_i\|_p$.
* Section 9.1, definition of strong inclusion, `Brezis.Chapter09.IsStronglyIncluded`:
  $\omega \subset\subset \Omega$ if $\bar\omega \subseteq \Omega$ and $\bar\omega$ is compact.
* Proposition 9.3, the distance $\operatorname{dist}(\omega, \partial\Omega)$,
  `Brezis.Chapter09.edistFrontier`.
* Section 9.1, the spaces $W^{m,p}(\Omega)$, `Brezis.Chapter09.sobolevSpaceHigher`, with the norm
  `Brezis.Chapter09.bookNormHigher`.

## Main results

* Section 9.1, definition of $W^{1,p}(\Omega)$, `Brezis.Chapter09.sobolevSpace_iff`: a function is
  in $W^{1,p}(\Omega)$ if and only if it satisfies the defining condition of the source.
* Remark 1, `Brezis.Chapter09.remark_9_1` and `Brezis.Chapter09.remark_9_1_iff`: the test functions
  in the definition may be taken in $C_c^1(\Omega)$.
* Section 9.1, `Brezis.Chapter09.hInner` and `Brezis.Chapter09.hNorm`: the scalar product and the
  norm of $H^1(\Omega)$.
* Section 9.1, `Brezis.Chapter09.bookNorm_equiv`: the norm of the source is equivalent to the norm
  of the type.
* Proposition 9.1, `Brezis.Chapter09.proposition_9_1`: $W^{1,p}(\Omega)$ is a Banach space,
  reflexive for $1 < p < \infty$ and separable for $1 \le p < \infty$, and $H^1(\Omega)$ is a
  separable Hilbert space.
* Remark 2, `Brezis.Chapter09.remark_9_2`, `Brezis.Chapter09.remark_9_2_closure` and
  `Brezis.Chapter09.remark_9_2_converse`: a $C^1$ function with derivatives in $L^p$ is in
  $W^{1,p}(\Omega)$, and a function of $W^{1,p}(\Omega)$ with continuous weak derivatives is of
  class $C^1$.
* Remark 4(i), `Brezis.Chapter09.remark_9_4_i` and `Brezis.Chapter09.remark_9_4_i_bounded`:
  $W^{1,p}(\Omega)$ is closed under limits in $L^p$ with convergent, or for $p > 1$ bounded,
  gradients.
* Remark 4(ii), `Brezis.Chapter09.remark_9_4_ii` and `Brezis.Chapter09.remark_9_4_ii_cutoff`: the
  extension by zero of $\alpha u$ lies in $W^{1,p}(\mathbb{R}^N)$.
* Theorem 9.2 (Friedrichs), `Brezis.Chapter09.theorem_9_2` and `Brezis.Chapter09.theorem_9_2_univ`:
  approximation by functions of $C_c^\infty(\mathbb{R}^N)$.
* Lemma 9.1, `Brezis.Chapter09.lemma_9_1`: $\rho \star v \in W^{1,p}(\mathbb{R}^N)$ and
  $\partial_i(\rho \star v) = \rho \star \partial_i v$ for $\rho \in L^1(\mathbb{R}^N)$.
* Remark 5 (Meyers–Serrin), `Brezis.Chapter09.remark_9_5`: $C^\infty(\Omega) \cap W^{1,p}(\Omega)$
  is dense in $W^{1,p}(\Omega)$ for $p < \infty$.
* Proposition 9.3, `Brezis.Chapter09.proposition_9_3`: for $1 < p \le \infty$, membership in
  $W^{1,p}(\Omega)$, a duality bound, and a bound on translations are equivalent; the implications
  are `Brezis.Chapter09.proposition_9_3_i_ii`, `Brezis.Chapter09.proposition_9_3_ii_i`,
  `Brezis.Chapter09.proposition_9_3_i_iii` and `Brezis.Chapter09.proposition_9_3_iii_ii`, and the
  case $\Omega = \mathbb{R}^N$ is `Brezis.Chapter09.proposition_9_3_univ`.
* Remark 6, `Brezis.Chapter09.remark_9_6`: at $p = 1$ the implications (i) ⇒ (ii), (i) ⇒ (iii) and
  (iii) ⇒ (ii) of Proposition 9.3 hold.
* Remark 7, `Brezis.Chapter09.remark_9_7`, `Brezis.Chapter09.remark_9_7_convex` and
  `Brezis.Chapter09.remark_9_7_const`: functions of $W^{1,\infty}(\Omega)$ are continuous, Lipschitz
  on a convex $\Omega$, and $\nabla u = 0$ makes $u$ constant on each connected component.
* Proposition 9.4, `Brezis.Chapter09.proposition_9_4`: the product rule in
  $W^{1,p}(\Omega) \cap L^\infty(\Omega)$.
* Proposition 9.5, `Brezis.Chapter09.proposition_9_5`: the chain rule $\partial_i (G \circ u) = (G'
  \circ u) \partial_i u$.
* Proposition 9.6, `Brezis.Chapter09.proposition_9_6`: the change of variables formula.
* Section 9.1, the spaces $W^{m,p}(\Omega)$, `Brezis.Chapter09.sobolevSpaceHigher_iff`,
  `Brezis.Chapter09.sobolevSpaceHigher_iff_inductive`, `Brezis.Chapter09.sobolevSpaceHigher_banach`
  and `Brezis.Chapter09.hSpaceHigher`: the multi-index and the inductive definitions agree,
  $W^{m,p}(\Omega)$ is a Banach space, and $H^m(\Omega)$ is a Hilbert space.

## Notation

* `V ⊂⊂ Ω`, scoped in the namespace `Brezis`: `Brezis.Chapter09.IsStronglyIncluded V Ω`.

## Conventions

* The space $\mathbb{R}^N$ is `EuclideanSpace ℝ (Fin N)` with Lebesgue measure `volume`, and
  $\Omega$ is `Ω : Opens (EuclideanSpace ℝ (Fin N))`. The space $L^p(\Omega)$ is
  `Lp ℝ p (volume.restrict Ω)`.
* The standing assumption $1 \le p \le \infty$ is written `[Fact (1 ≤ p)]`.
* An element `u : sobolevSpace N p Ω` carries a function `SobolevMultiIndex.fn u`, defined up to
  a null set of $\Omega$. "The function $f$ belongs to $W^{1,p}(\Omega)$" is written
  `∃ v : sobolevSpace N p Ω, SobolevMultiIndex.fn v =ᵐ[volume.restrict Ω] f`.
* The weak partial derivative $\partial u / \partial x_i$ is `Brezis.Chapter09.partialDeriv u i`,
  the gradient $\nabla u$ is `Brezis.Chapter09.gradient u`, and $\|\nabla u\|_{L^p(\Omega)}$ is
  `eLpNorm (gradient u) p (volume.restrict Ω)`, with the Euclidean norm $|\nabla u|$ at each point.
* The test functions $C_c^\infty(\Omega)$ are `𝓓(Ω, ℝ)`. The basis vector $e_i$ is
  `EuclideanSpace.single i 1`, and $\partial \varphi / \partial x_i (x)$ is
  `fderiv ℝ φ x (EuclideanSpace.single i 1)`.
* The conjugate exponent $p'$ is `q` with `[p.HolderConjugate q]`. The estimates are stated in
  `ℝ≥0∞` with `eLpNorm`, a real constant $C$ as `ENNReal.ofReal C`, and $|h|$ as `‖h‖ₑ`.

## Implementation notes

* `Brezis.Chapter09.sobolevSpace` is an abbreviation of the backbone type
  `SobolevEuclidean N 1 p Ω`, so that every backbone lemma applies to it.
* For $p < \infty$ the norm of the type is $(\|u\|_p^p + \sum_i \|\partial u / \partial
  x_i\|_p^p)^{1/p}$, the equivalent norm that the source also mentions; for $p = \infty$ it is the
  maximum of these $N + 1$ norms. The norm $\|u\|_p + \sum_i \|\partial u / \partial x_i\|_p$ of the
  source is `Brezis.Chapter09.bookNorm`, equivalent to it by `Brezis.Chapter09.bookNorm_equiv`. At
  $p = 2$ the norm and the inner product of the type are those of $H^1(\Omega)$ in the source.

## Deviations from the source

* **Remark 2, "in particular"** (reading). The space $C^1(\bar\Omega)$ is read as the functions that
  are of class $C^1$ on $\bar\Omega$ in the sense of `ContDiffOn`. See
  `Brezis.Chapter09.remark_9_2_closure`.
* **Sobolev space definitions and norms** (reading and generalization). The type uses the
  equivalent product norm and is available for all exponents. The higher-order family includes
  orders zero and one. See `Brezis.Chapter09.sobolevSpace`, `Brezis.Chapter09.bookNorm_equiv` and
  `Brezis.Chapter09.sobolevSpaceHigher`.
* **Weak derivative identities** (generalization). The integration tests extend from coordinate
  directions to arbitrary tuples of directions. See
  `Brezis.Chapter09.integral_mul_iteratedFDeriv_eq_of_hasWeakIteratedLineDerivOn` and
  `Brezis.Chapter09.hasWeakIteratedLineDerivOn_of_forall`.
* **Remark 1** (typo). The definition uses smooth test functions. The remark exchanges the
  original and alternative test classes in its prose. See `Brezis.Chapter09.remark_9_1_iff`.
* **Remark 4(ii)** (reading). Both versions require smooth cutoffs, while the source uses
  $C^1$ cutoffs. See `Brezis.Chapter09.remark_9_4_ii` and
  `Brezis.Chapter09.remark_9_4_ii_cutoff`.
* **Proposition 9.3** (reading and generalization). The distance is extended-valued, and the
  translation bound on the whole space includes $p=1$. See `Brezis.Chapter09.edistFrontier`
  and `Brezis.Chapter09.proposition_9_3_univ`.
* **Remarks 5–7** (reading). The library gives the smooth density assertion, the endpoint
  implications apart from (ii) ⇒ (iii), and the geodesic estimate for convex sets. See
  `Brezis.Chapter09.remark_9_5`, `Brezis.Chapter09.remark_9_6` and
  `Brezis.Chapter09.remark_9_7_convex`.

## Not formalized

* **Remark 3.**
* **Remark 4(ii) for a cut-off function $\alpha$ of class $C^1$ that is not of class $C^\infty$.**
  Both forms of the remark are proved for smooth $\alpha$ only.
* **Remark 5, second claim**, that for a general $\Omega$ no sequence of $C_c^1(\mathbb{R}^N)$
  functions need converge to $u$ in $W^{1,p}(\Omega)$. It is a counterexample.
* **Remark 6, the implication (ii) ⇒ (iii) at $p = 1$, and the discussion of the functions of
  bounded variation.** It belongs to the theory of $BV$ functions.
* **Remark 7 on a nonconvex $\Omega$, with the geodesic distance.**
* **Remark 8.**
-/

open Filter MeasureTheory Metric Topology TopologicalSpace
open scoped ContDiff Convolution Distributions ENNReal

namespace Brezis.Chapter09

variable {N : ℕ}

/-- The space $\mathbb{R}^N$ of the source. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin N)

/-- The standard basis $(e_1, \dots, e_N)$ of $\mathbb{R}^N$, as a `Basis`. -/
local notation "𝔟" => OrthonormalBasis.toBasis (EuclideanSpace.basisFun (Fin N) ℝ)

/-! ### Weak derivatives along directions, in the form of the source -/

section Direction

variable {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-- Let $\Omega \subseteq \mathbb{R}^N$ be open, let $u, g : \mathbb{R}^N \to \mathbb{R}$, and let
$y = (y_1, \dots, y_n)$ be a tuple of $n$ directions in $\mathbb{R}^N$. If $g$ is a weak
derivative of $u$ along $y$ on $\Omega$, then for every $\varphi \in C_c^\infty(\Omega)$
$$\int_\Omega u \, D^n \varphi(x)(y_1, \dots, y_n) \, dx = (-1)^n \int_\Omega g \varphi \, dx.$$

This is the defining identity of `HasWeakIteratedLineDerivOn` in the form of
[brezis2011functional], Section 9.1, with the product written $u \cdot D^y \varphi$. The
derivative $D^n \varphi(x)(y_1, \dots, y_n)$ is `iteratedFDeriv ℝ n φ x y`.

**Generalization.** The derivative can be taken along any tuple of directions. The defining
 formulas in the source use coordinate directions. -/
theorem integral_mul_iteratedFDeriv_eq_of_hasWeakIteratedLineDerivOn {u g : 𝔼 → ℝ} {n : ℕ}
    {y : Fin n → 𝔼} (h : HasWeakIteratedLineDerivOn y u g Ω volume) (φ : 𝓓(Ω, ℝ)) :
    ∫ x in (Ω : Set 𝔼), u x * iteratedFDeriv ℝ n φ x y
      = (-1) ^ n * ∫ x in (Ω : Set 𝔼), g x * φ x := by
  have hs := Ω.isOpen.measurableSet
  have h1 := h.integral_smul_eq φ
  simp only [smul_eq_mul] at h1
  calc ∫ x in (Ω : Set 𝔼), u x * iteratedFDeriv ℝ n φ x y
      = ∫ x in (Ω : Set 𝔼), iteratedFDeriv ℝ n φ x y * u x :=
        setIntegral_congr_fun hs fun x _ ↦ mul_comm _ _
    _ = (-1) ^ n * ∫ x in (Ω : Set 𝔼), φ x * g x := h1
    _ = (-1) ^ n * ∫ x in (Ω : Set 𝔼), g x * φ x := by
        rw [setIntegral_congr_fun hs fun x _ ↦ mul_comm (φ x) (g x)]

/-- Let $\Omega \subseteq \mathbb{R}^N$ be open, let $u, g : \mathbb{R}^N \to \mathbb{R}$ be locally
integrable on $\Omega$, and let $y = (y_1, \dots, y_n)$ be a tuple of $n$ directions in
$\mathbb{R}^N$. If
$$\int_\Omega u \, D^n \varphi(x)(y_1, \dots, y_n) \, dx = (-1)^n \int_\Omega g \varphi \, dx$$
for every $\varphi \in C_c^\infty(\Omega)$, then $g$ is a weak derivative of $u$ along $y$ on
$\Omega$.

This is the converse of
`Brezis.Chapter09.integral_mul_iteratedFDeriv_eq_of_hasWeakIteratedLineDerivOn`: it builds
`HasWeakIteratedLineDerivOn` from the identity in the form of [brezis2011functional], Section
9.1.

**Generalization.** The converse test works for locally integrable functions and any tuple
 of directions. The Sobolev definition uses $L^p$ functions and coordinate directions. -/
theorem hasWeakIteratedLineDerivOn_of_forall {u g : 𝔼 → ℝ} {n : ℕ} {y : Fin n → 𝔼}
    (hu : LocallyIntegrableOn u Ω volume) (hg : LocallyIntegrableOn g Ω volume)
    (h : ∀ φ : 𝓓(Ω, ℝ), ∫ x in (Ω : Set 𝔼), u x * iteratedFDeriv ℝ n φ x y
      = (-1) ^ n * ∫ x in (Ω : Set 𝔼), g x * φ x) :
    HasWeakIteratedLineDerivOn y u g Ω volume := by
  have hs := Ω.isOpen.measurableSet
  refine ⟨hu, hg, fun φ ↦ ?_⟩
  simp only [smul_eq_mul]
  calc ∫ x in (Ω : Set 𝔼), iteratedFDeriv ℝ n φ x y * u x
      = ∫ x in (Ω : Set 𝔼), u x * iteratedFDeriv ℝ n φ x y :=
        setIntegral_congr_fun hs fun x _ ↦ mul_comm _ _
    _ = (-1) ^ n * ∫ x in (Ω : Set 𝔼), g x * φ x := h φ
    _ = (-1) ^ n * ∫ x in (Ω : Set 𝔼), φ x * g x := by
        rw [setIntegral_congr_fun hs fun x _ ↦ mul_comm (g x) (φ x)]

/-- Let $\Omega \subseteq \mathbb{R}^N$ be open, $u, g : \mathbb{R}^N \to \mathbb{R}$ and
$y \in \mathbb{R}^N$. If $g$ is a weak derivative of $u$ along $y$ on $\Omega$, then
$\int_\Omega u \, \partial_y \varphi = -\int_\Omega g \varphi$ for every
$\varphi \in C_c^\infty(\Omega)$, where $\partial_y \varphi(x) = D\varphi(x) y$.

**Generalization.** This is the first-order test for an arbitrary direction $y$. -/
theorem integral_mul_fderiv_eq_of_hasWeakIteratedLineDerivOn {u g : 𝔼 → ℝ} {y : 𝔼}
    (h : HasWeakIteratedLineDerivOn ![y] u g Ω volume) (φ : 𝓓(Ω, ℝ)) :
    ∫ x in (Ω : Set 𝔼), u x * fderiv ℝ φ x y = -∫ x in (Ω : Set 𝔼), g x * φ x := by
  have := integral_mul_iteratedFDeriv_eq_of_hasWeakIteratedLineDerivOn h φ
  simpa [iteratedFDeriv_one_apply] using this

/-- Let $\Omega \subseteq \mathbb{R}^N$ be open, let $u, g : \mathbb{R}^N \to \mathbb{R}$ be locally
integrable on $\Omega$, and let $y \in \mathbb{R}^N$. If $\int_\Omega u \, \partial_y \varphi =
-\int_\Omega g \varphi$ for every $\varphi \in C_c^\infty(\Omega)$, where
$\partial_y \varphi(x) = D\varphi(x) y$, then $g$ is a weak derivative of $u$ along $y$ on
$\Omega$.

**Generalization.** This is the converse test for locally integrable functions in an arbitrary
 direction $y$. -/
theorem hasWeakIteratedLineDerivOn_single_of_forall {u g : 𝔼 → ℝ} {y : 𝔼}
    (hu : LocallyIntegrableOn u Ω volume) (hg : LocallyIntegrableOn g Ω volume)
    (h : ∀ φ : 𝓓(Ω, ℝ), ∫ x in (Ω : Set 𝔼), u x * fderiv ℝ φ x y = -∫ x in (Ω : Set 𝔼), g x * φ x) :
    HasWeakIteratedLineDerivOn ![y] u g Ω volume :=
  hasWeakIteratedLineDerivOn_of_forall hu hg fun φ ↦ by
    simpa [iteratedFDeriv_one_apply] using h φ

end Direction

/-! ### The definition of $W^{1,p}(\Omega)$ -/

/-- **Section 9.1** of [brezis2011functional], definition of the Sobolev space $W^{1,p}(\Omega)$.
Let $\Omega \subseteq \mathbb{R}^N$ be open and $1 \le p \le \infty$. The **Sobolev space**
$W^{1,p}(\Omega)$ is the space of the functions $u \in L^p(\Omega)$ for which there are
$g_1, \dots, g_N \in L^p(\Omega)$ with
$$\int_\Omega u \frac{\partial \varphi}{\partial x_i} = -\int_\Omega g_i \varphi \qquad
  \text{for all } \varphi \in C_c^\infty(\Omega) \text{ and } i = 1, \dots, N.$$

The type is the backbone type `SobolevEuclidean N 1 p Ω`, the multi-index Sobolev space over the
standard basis of $\mathbb{R}^N$ with Lebesgue measure. An element is the family of $u$ and its
weak partial derivatives in $L^p(\Omega)$; `Brezis.Chapter09.sobolevSpace_iff` shows that the
functions of these elements are the functions of the definition. The type is defined for every
exponent $p \in [0, \infty]$, and the results assume $p \ge 1$. For $p < \infty$ the norm of the
type is $(\|u\|_p^p + \sum_i \|\partial u / \partial x_i\|_p^p)^{1/p}$
(`SobolevMultiIndex.norm_eq_sum`), the equivalent norm of the source. The norm that the source
puts on $W^{1,p}(\Omega)$ is `Brezis.Chapter09.bookNorm`.

**Reading.** The type is available for every exponent $p$. The Sobolev results impose
 $1 \le p$ as needed. The ambient norm is the equivalent product norm, with a maximum at
 $p = \infty$. The source's sum norm is `Brezis.Chapter09.bookNorm`. -/
noncomputable abbrev sobolevSpace (N : ℕ) (p : ℝ≥0∞) (Ω : Opens (EuclideanSpace ℝ (Fin N))) :
    Type :=
  SobolevEuclidean N 1 p Ω

variable {p : ℝ≥0∞} {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-- **Section 9.1** of [brezis2011functional], definition of the weak partial derivatives. For
$u \in W^{1,p}(\Omega)$ and $i = 1, \dots, N$, the **weak partial derivative**
$\partial u / \partial x_i$ is the function $g_i$ of the definition, as an element of
$L^p(\Omega)$.

The index $i$ runs over `Fin N`, that is, from $0$ to $N - 1$. The element is the component of
$u$ at the multi-index `MultiIndexLE.single i`. -/
noncomputable def partialDeriv (u : sobolevSpace N p Ω) (i : Fin N) :
    Lp ℝ p (volume.restrict (Ω : Set 𝔼)) :=
  SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i)

/-- **Section 9.1** of [brezis2011functional], the gradient. For $u \in W^{1,p}(\Omega)$, the
**gradient** is the vector field $\nabla u = (\partial u / \partial x_1, \dots, \partial u /
\partial x_N)$ from $\mathbb{R}^N$ to $\mathbb{R}^N$, defined up to a null set of $\Omega$.

The norm $\|\nabla u\|_{L^p(\Omega)}$ is `eLpNorm (gradient u) p (volume.restrict Ω)`, with the
Euclidean norm $|\nabla u(x)|$ at each point. -/
noncomputable def gradient (u : sobolevSpace N p Ω) (x : 𝔼) : 𝔼 :=
  WithLp.toLp 2 fun i ↦ partialDeriv u i x

/-- The $i$-th component of the gradient $\nabla u(x)$ is $\partial u / \partial x_i (x)$. -/
@[simp]
theorem gradient_apply (u : sobolevSpace N p Ω) (x : 𝔼) (i : Fin N) :
    gradient u x i = partialDeriv u i x :=
  rfl

/-- The $i$-th vector $e_i$ of the standard basis of $\mathbb{R}^N$ is `EuclideanSpace.single i 1`.
-/
theorem basisFun_toBasis_apply (i : Fin N) :
    (𝔟 : Fin N → 𝔼) i = EuclideanSpace.single i 1 := by
  simp

/-- Let $u \in W^{1,p}(\Omega)$ and $i = 1, \dots, N$. Then $\partial u / \partial x_i$ is a weak
derivative of $u$ along $e_i$ on $\Omega$, in the sense of `HasWeakIteratedLineDerivOn`.

This connects `Brezis.Chapter09.partialDeriv` to the backbone notion of a weak derivative along
a direction. -/
theorem hasWeakIteratedLineDerivOn_partialDeriv (u : sobolevSpace N p Ω) (i : Fin N) :
    HasWeakIteratedLineDerivOn ![EuclideanSpace.single i 1] (SobolevMultiIndex.fn u)
      (partialDeriv u i) Ω volume := by
  have := (SobolevMultiIndex.hasWeakIteratedLineDerivOn u (MultiIndexLE.single i)).of_perm
    (multiIndexTuple_single_perm (𝔟 : Fin N → 𝔼) i)
  rw [basisFun_toBasis_apply] at this
  exact this

/-- **Section 9.1** of [brezis2011functional], the defining identity of the weak partial
derivatives. For $u \in W^{1,p}(\Omega)$, $i = 1, \dots, N$ and every test function
$\varphi \in C_c^\infty(\Omega)$,
$$\int_\Omega u \frac{\partial \varphi}{\partial x_i} = -\int_\Omega \frac{\partial u}{\partial
  x_i} \varphi.$$
-/
theorem partialDeriv_spec (u : sobolevSpace N p Ω) (i : Fin N) (φ : 𝓓(Ω, ℝ)) :
    ∫ x in (Ω : Set 𝔼), SobolevMultiIndex.fn u x * fderiv ℝ φ x (EuclideanSpace.single i 1)
      = -∫ x in (Ω : Set 𝔼), partialDeriv u i x * φ x :=
  integral_mul_fderiv_eq_of_hasWeakIteratedLineDerivOn
    (hasWeakIteratedLineDerivOn_partialDeriv u i) φ

variable [Fact (1 ≤ p)]

/-- Let $1 \le p \le \infty$, let $u \in L^p(\Omega)$, and let $g_1, \dots, g_N \in L^p(\Omega)$ be
such that $g_i$ is a weak derivative of $u$ along $e_i$ on $\Omega$ for each $i$. Then there is
$v \in W^{1,p}(\Omega)$ whose function equals $u$ almost everywhere on $\Omega$, with
$\partial v / \partial x_i = g_i$ almost everywhere on $\Omega$ for each $i$.

This builds an element of `Brezis.Chapter09.sobolevSpace` from functions, for the definition of
$W^{1,p}(\Omega)$ in [brezis2011functional], Section 9.1. -/
theorem exists_sobolevSpace_of_hasWeakIteratedLineDerivOn {u : 𝔼 → ℝ}
    (hu : MemLp u p (volume.restrict (Ω : Set 𝔼))) {g : Fin N → 𝔼 → ℝ}
    (hg : ∀ i, HasWeakIteratedLineDerivOn ![EuclideanSpace.single i 1] u (g i) Ω volume)
    (hgp : ∀ i, MemLp (g i) p (volume.restrict (Ω : Set 𝔼))) :
    ∃ v : sobolevSpace N p Ω, SobolevMultiIndex.fn v =ᵐ[volume.restrict (Ω : Set 𝔼)] u ∧
      ∀ i, partialDeriv v i =ᵐ[volume.restrict (Ω : Set 𝔼)] g i := by
  have hp : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hmem : MemSobolevMultiIndex 𝔟 u 1 p Ω volume := by
    refine ⟨hu, fun α hα ↦ ?_⟩
    rcases MultiIndexLE.eq_zero_or_exists_eq_single (⟨α, hα⟩ : MultiIndexLE (Fin N) 1) with
      h0 | ⟨i, hi⟩
    · obtain rfl : α = 0 := congrArg Subtype.val h0
      exact ⟨u, HasWeakIteratedLineDerivOn.of_length_eq_zero (by simp) _
        (hu.locallyIntegrableOn hp), hu⟩
    · obtain rfl : α = Pi.single i 1 := congrArg Subtype.val hi
      have hperm := (multiIndexTuple_single_perm (𝔟 : Fin N → 𝔼) i).symm
      rw [basisFun_toBasis_apply] at hperm
      exact ⟨g i, (hg i).of_perm hperm, hgp i⟩
  obtain ⟨v, hv⟩ := hmem.exists_sobolevMultiIndex
  refine ⟨v, hv, fun i ↦ ?_⟩
  have h1 := (hasWeakIteratedLineDerivOn_partialDeriv v i).congr_ae hv
    (Filter.EventuallyEq.refl _ _)
  exact (ae_restrict_iff' Ω.isOpen.measurableSet).2 (h1.ae_eq (hg i))

omit [Fact (1 ≤ p)] in
/-- Let $u : \mathbb{R}^N \to \mathbb{R}$ belong to $W^{1,p}(\Omega)$ in the sense of the backbone
predicate `MemSobolevMultiIndex`, and let $g$ be a weak derivative of $u$ along $e_i$ on
$\Omega$. Then $g \in L^p(\Omega)$.

The weak derivative is unique almost everywhere, so the membership in $L^p(\Omega)$ of the weak
derivative that the predicate provides passes to $g$. This holds for every exponent $p$. -/
theorem memLp_of_memSobolevMultiIndex_of_hasWeakIteratedLineDerivOn {u g : 𝔼 → ℝ}
    (hu : MemSobolevMultiIndex 𝔟 u 1 p Ω volume) {i : Fin N}
    (hg : HasWeakIteratedLineDerivOn ![EuclideanSpace.single i 1] u g Ω volume) :
    MemLp g p (volume.restrict (Ω : Set 𝔼)) := by
  obtain ⟨w, hw, hwp⟩ := hu.2 (Pi.single i 1) (by simp)
  have hperm := multiIndexTuple_single_perm (𝔟 : Fin N → 𝔼) i
  rw [basisFun_toBasis_apply] at hperm
  exact hwp.ae_eq ((ae_restrict_iff' Ω.isOpen.measurableSet).2 ((hw.of_perm hperm).ae_eq hg))

/-- **Section 9.1** of [brezis2011functional], definition of $W^{1,p}(\Omega)$. Let
$1 \le p \le \infty$. A function $u : \mathbb{R}^N \to \mathbb{R}$ is, almost everywhere on
$\Omega$, the function of an element of $W^{1,p}(\Omega)$ if and only if $u \in L^p(\Omega)$ and
there are $g_1, \dots, g_N \in L^p(\Omega)$ with
$$\int_\Omega u \frac{\partial \varphi}{\partial x_i} = -\int_\Omega g_i \varphi$$
for every $\varphi \in C_c^\infty(\Omega)$ and every $i$.

Footnote 2 of the source, that the $g_i$ are unique almost everywhere, follows from
`Brezis.Chapter09.partialDeriv_spec` together with `HasWeakIteratedLineDerivOn.ae_eq`. -/
theorem sobolevSpace_iff (u : 𝔼 → ℝ) :
    (∃ v : sobolevSpace N p Ω, SobolevMultiIndex.fn v =ᵐ[volume.restrict (Ω : Set 𝔼)] u) ↔
      MemLp u p (volume.restrict (Ω : Set 𝔼)) ∧ ∃ g : Fin N → 𝔼 → ℝ,
        (∀ i, MemLp (g i) p (volume.restrict (Ω : Set 𝔼))) ∧ ∀ (φ : 𝓓(Ω, ℝ)) (i : Fin N),
          ∫ x in (Ω : Set 𝔼), u x * fderiv ℝ φ x (EuclideanSpace.single i 1)
            = -∫ x in (Ω : Set 𝔼), g i x * φ x := by
  have hp : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hs := Ω.isOpen.measurableSet
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨(SobolevMultiIndex.memLp v).ae_eq hv, fun i ↦ partialDeriv v i, fun i ↦ Lp.memLp _,
      fun φ i ↦ ?_⟩
    rw [← partialDeriv_spec v i φ]
    exact setIntegral_congr_ae hs ((ae_restrict_iff' hs).1 (hv.mono fun x hx ↦ by rw [hx]))
  · rintro ⟨hu, g, hgp, hg⟩
    obtain ⟨v, hv, -⟩ := exists_sobolevSpace_of_hasWeakIteratedLineDerivOn hu (g := g)
      (fun i ↦ hasWeakIteratedLineDerivOn_single_of_forall (hu.locallyIntegrableOn hp)
        ((hgp i).locallyIntegrableOn hp) fun φ ↦ hg φ i) hgp
    exact ⟨v, hv⟩


/-! ### Remark 1: test functions of class $C_c^1$ -/

omit [Fact (1 ≤ p)] in
/-- **Remark 1** in Chapter 9 of [brezis2011functional]. In the definition of $W^{1,p}(\Omega)$ the
test functions may be taken in $C_c^1(\Omega)$ instead of $C_c^\infty(\Omega)$. Let
$u \in W^{1,p}(\Omega)$ and $i = 1, \dots, N$, and let $\varphi : \mathbb{R}^N \to \mathbb{R}$
be of class $C^1$ with compact support contained in $\Omega$. Then
$$\int_\Omega u \frac{\partial \varphi}{\partial x_i} = -\int_\Omega \frac{\partial u}{\partial
  x_i} \varphi.$$

This holds for every exponent $p$. The proof specializes
`HasWeakIteratedLineDerivOn.integral_smul_eq_of_contDiff_one`, which uses a sequence of
mollifiers as the source suggests. The resulting equivalence of the two definitions is
`Brezis.Chapter09.remark_9_1_iff`.

**Typo.** Remark 1 presents $C_c^\infty$ as the alternative to $C_c^1$, though the preceding
 definition already uses $C_c^\infty$. This direction enlarges the test class to $C_c^1$. -/
theorem remark_9_1 (u : sobolevSpace N p Ω) (i : Fin N) {φ : 𝔼 → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hφc : HasCompactSupport φ) (hφΩ : tsupport φ ⊆ Ω) :
    ∫ x in (Ω : Set 𝔼), SobolevMultiIndex.fn u x * fderiv ℝ φ x (EuclideanSpace.single i 1)
      = -∫ x in (Ω : Set 𝔼), partialDeriv u i x * φ x := by
  have hs := Ω.isOpen.measurableSet
  have h := (hasWeakIteratedLineDerivOn_partialDeriv u i).integral_smul_eq_of_contDiff_one hφ
    hφc hφΩ
  refine (setIntegral_congr_fun hs fun x _ ↦ ?_).trans (h.trans ?_)
  · rw [smul_eq_mul, mul_comm]
  · congr 1
    exact setIntegral_congr_fun hs fun x _ ↦ by rw [smul_eq_mul, mul_comm]

/-- **Remark 1** in Chapter 9 of [brezis2011functional], the equivalence of the two definitions. Let
$1 \le p \le \infty$. A function $u : \mathbb{R}^N \to \mathbb{R}$ is, almost everywhere on
$\Omega$, the function of an element of $W^{1,p}(\Omega)$ if and only if $u \in L^p(\Omega)$ and
there are $g_1, \dots, g_N \in L^p(\Omega)$ with
$$\int_\Omega u \frac{\partial \varphi}{\partial x_i} = -\int_\Omega g_i \varphi$$
for every $\varphi$ of class $C^1$ with compact support contained in $\Omega$ and every $i$.

This is the definition of $W^{1,p}(\Omega)$ (`Brezis.Chapter09.sobolevSpace_iff`) with
$C_c^1(\Omega)$ in place of $C_c^\infty(\Omega)$. Every function of $C_c^\infty(\Omega)$ is in
$C_c^1(\Omega)$, and `Brezis.Chapter09.remark_9_1` gives the identities for $C_c^1(\Omega)$ from
those for $C_c^\infty(\Omega)$.

**Typo.** Remark 1 exchanges the roles of the original and alternative tests in the prose.
 The equivalence holds with the order used here. -/
theorem remark_9_1_iff (u : 𝔼 → ℝ) :
    (∃ v : sobolevSpace N p Ω, SobolevMultiIndex.fn v =ᵐ[volume.restrict (Ω : Set 𝔼)] u) ↔
      MemLp u p (volume.restrict (Ω : Set 𝔼)) ∧ ∃ g : Fin N → 𝔼 → ℝ,
        (∀ i, MemLp (g i) p (volume.restrict (Ω : Set 𝔼))) ∧
        ∀ φ : 𝔼 → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ Ω → ∀ i : Fin N,
          ∫ x in (Ω : Set 𝔼), u x * fderiv ℝ φ x (EuclideanSpace.single i 1)
            = -∫ x in (Ω : Set 𝔼), g i x * φ x := by
  have hs := Ω.isOpen.measurableSet
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨(SobolevMultiIndex.memLp v).ae_eq hv, fun i ↦ partialDeriv v i, fun i ↦ Lp.memLp _,
      fun φ hφ hφc hφΩ i ↦ ?_⟩
    rw [← remark_9_1 v i hφ hφc hφΩ]
    exact setIntegral_congr_ae hs ((ae_restrict_iff' hs).1 (hv.mono fun x hx ↦ by rw [hx]))
  · rintro ⟨hu, g, hgp, hg⟩
    exact (sobolevSpace_iff u).2 ⟨hu, g, hgp, fun φ i ↦
      hg φ (φ.contDiff.of_le (by simp)) φ.hasCompactSupport φ.tsupport_subset i⟩

/-! ### The space $H^1(\Omega)$ -/

/-- **Section 9.1** of [brezis2011functional], definition of $H^1(\Omega)$. The space
$H^1(\Omega) = W^{1,2}(\Omega)$, a Hilbert space for the scalar product
$$(u, v)_{H^1} = \int_\Omega uv + \sum_{i=1}^N \int_\Omega \frac{\partial u}{\partial x_i}
  \frac{\partial v}{\partial x_i}$$
and the norm $\|u\|_{H^1} = (\|u\|_2^2 + \sum_i \|\partial u / \partial x_i\|_2^2)^{1/2}$.

The scalar product and the norm are those of the type, by `Brezis.Chapter09.hInner` and
`Brezis.Chapter09.hNorm`. -/
noncomputable abbrev hSpace (N : ℕ) (Ω : Opens (EuclideanSpace ℝ (Fin N))) : Type :=
  sobolevSpace N 2 Ω

/-- **Section 9.1** of [brezis2011functional], the scalar product of $H^1(\Omega)$. For
$u, v \in H^1(\Omega)$ the inner product of the type is
$$(u, v)_{H^1} = \int_\Omega uv + \sum_{i=1}^N \int_\Omega \frac{\partial u}{\partial x_i}
  \frac{\partial v}{\partial x_i}.$$
-/
theorem hInner (u v : hSpace N Ω) :
    inner ℝ u v = (∫ x in (Ω : Set 𝔼), SobolevMultiIndex.fn u x * SobolevMultiIndex.fn v x)
      + ∑ i, ∫ x in (Ω : Set 𝔼), partialDeriv u i x * partialDeriv v i x := by
  rw [SobolevMultiIndex.inner_eq, integral_finsetSum _ fun α _ ↦ L2.integrable_inner (𝕜 := ℝ)
    (SobolevMultiIndex.weakDeriv u α) (SobolevMultiIndex.weakDeriv v α), MultiIndexLE.sum_univ_one]
  simp only [Real.inner_apply, partialDeriv]
  rfl

/-- **Section 9.1** of [brezis2011functional], the norm of $H^1(\Omega)$. For $u \in H^1(\Omega)$
the norm of the type is
$$\|u\|_{H^1} = \Big(\|u\|_2^2 + \sum_{i=1}^N \Big\|\frac{\partial u}{\partial
  x_i}\Big\|_2^2\Big)^{1/2}.$$

Here $\|u\|_2$ is the norm of the component `SobolevMultiIndex.weakDeriv u 0` of $u$ at the
multi-index $0$, which is $u$ as an element of $L^2(\Omega)$. -/
theorem hNorm (u : hSpace N Ω) :
    ‖u‖ = √(‖SobolevMultiIndex.weakDeriv u 0‖ ^ 2 + ∑ i, ‖partialDeriv u i‖ ^ 2) := by
  rw [SobolevMultiIndex.norm_eq_sum (by simp), MultiIndexLE.sum_univ_one, Real.sqrt_eq_rpow]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, partialDeriv]

/-! ### The norm $\|u\|_p + \sum_i \|\partial u / \partial x_i\|_p$ -/

/-- **Section 9.1** of [brezis2011functional], the norm of $W^{1,p}(\Omega)$. For
$u \in W^{1,p}(\Omega)$,
$$\|u\|_{W^{1,p}} = \|u\|_p + \sum_{i=1}^N \Big\|\frac{\partial u}{\partial x_i}\Big\|_p.$$

This is a norm on the type (`Brezis.Chapter09.bookNorm_add_le`,
`Brezis.Chapter09.bookNorm_smul`, `Brezis.Chapter09.bookNorm_eq_zero_iff`). It is equivalent to
the norm of the type (`Brezis.Chapter09.bookNorm_equiv`), which for $p < \infty$ is the norm
$(\|u\|_p^p + \sum_i \|\partial u / \partial x_i\|_p^p)^{1/p}$ that the source also mentions. -/
noncomputable def bookNorm (u : sobolevSpace N p Ω) : ℝ :=
  ‖SobolevMultiIndex.weakDeriv u 0‖ + ∑ i, ‖partialDeriv u i‖

omit [Fact (1 ≤ p)] in
/-- The norm $\|u\|_{W^{1,p}}$ of the source is the sum of the $L^p(\Omega)$ norms of all the weak
derivatives $D^\alpha u$ of order $|\alpha| \le 1$. -/
theorem bookNorm_eq_sum (u : sobolevSpace N p Ω) :
    bookNorm u = ∑ α, ‖SobolevMultiIndex.weakDeriv u α‖ :=
  (MultiIndexLE.sum_univ_one fun α ↦ ‖SobolevMultiIndex.weakDeriv u α‖).symm

/-- The norm $\|u\|_{W^{1,p}}$ of the source is nonnegative. -/
theorem bookNorm_nonneg (u : sobolevSpace N p Ω) : 0 ≤ bookNorm u :=
  add_nonneg (norm_nonneg _) (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)

/-- **Section 9.1** of [brezis2011functional], the triangle inequality for the norm of
$W^{1,p}(\Omega)$: $\|u + v\|_{W^{1,p}} \le \|u\|_{W^{1,p}} + \|v\|_{W^{1,p}}$ for
$u, v \in W^{1,p}(\Omega)$. -/
theorem bookNorm_add_le (u v : sobolevSpace N p Ω) :
    bookNorm (u + v) ≤ bookNorm u + bookNorm v := by
  simp only [bookNorm_eq_sum, SobolevMultiIndex.weakDeriv_add, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun α _ ↦ norm_add_le _ _

/-- **Section 9.1** of [brezis2011functional], the homogeneity of the norm of $W^{1,p}(\Omega)$:
$\|cu\|_{W^{1,p}} = |c| \, \|u\|_{W^{1,p}}$ for $c \in \mathbb{R}$ and $u \in W^{1,p}(\Omega)$. -/
theorem bookNorm_smul (c : ℝ) (u : sobolevSpace N p Ω) : bookNorm (c • u) = |c| * bookNorm u := by
  simp only [bookNorm_eq_sum, SobolevMultiIndex.weakDeriv_smul, norm_smul, Real.norm_eq_abs,
    Finset.mul_sum]

/-- **Section 9.1** of [brezis2011functional], the equivalence of the two norms of
$W^{1,p}(\Omega)$. Let $1 \le p \le \infty$ and $u \in W^{1,p}(\Omega)$. Then
$$\|u\| \le \|u\|_{W^{1,p}} \le (N + 1) \|u\|,$$
where $\|u\|$ is the norm of the type.

The norm of the type is the $\ell^p$ norm, and $\|u\|_{W^{1,p}}$ is the $\ell^1$ norm, of the
$N + 1$ numbers $\|u\|_p, \|\partial u / \partial x_1\|_p, \dots, \|\partial u / \partial
x_N\|_p$.

**Generalization.** The estimate gives explicit comparison constants and includes the
 maximum product norm at $p = \infty$. -/
theorem bookNorm_equiv (u : sobolevSpace N p Ω) :
    ‖u‖ ≤ bookNorm u ∧ bookNorm u ≤ (N + 1) * ‖u‖ := by
  refine ⟨bookNorm_eq_sum u ▸ SobolevMultiIndex.norm_le_sum_norm_weakDeriv u, ?_⟩
  calc bookNorm u = ∑ α, ‖SobolevMultiIndex.weakDeriv u α‖ := bookNorm_eq_sum u
    _ ≤ ∑ _α : MultiIndexLE (Fin N) 1, ‖u‖ :=
        Finset.sum_le_sum fun α _ ↦ SobolevMultiIndex.norm_weakDeriv_le u α
    _ = (N + 1) * ‖u‖ := by
        rw [MultiIndexLE.sum_univ_one (fun _ ↦ ‖u‖)]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- **Section 9.1** of [brezis2011functional], the definiteness of the norm of $W^{1,p}(\Omega)$:
$\|u\|_{W^{1,p}} = 0$ if and only if $u = 0$. -/
theorem bookNorm_eq_zero_iff (u : sobolevSpace N p Ω) : bookNorm u = 0 ↔ u = 0 := by
  constructor
  · intro h
    exact norm_le_zero_iff.1 ((bookNorm_equiv u).1.trans h.le)
  · rintro rfl
    refine le_antisymm ?_ (bookNorm_nonneg 0)
    simpa using (bookNorm_equiv (0 : sobolevSpace N p Ω)).2

/-! ### Proposition 9.1 -/

/-- **Proposition 9.1** of [brezis2011functional], first clause. For $1 \le p \le \infty$ the space
$W^{1,p}(\Omega)$ is a Banach space. -/
theorem proposition_9_1_banach : CompleteSpace (sobolevSpace N p Ω) :=
  inferInstance

/-- **Proposition 9.1** of [brezis2011functional], second clause. For $1 < p < \infty$ the space
$W^{1,p}(\Omega)$ is reflexive.

Reflexivity is the definition of Section 3.5 of the source, `Brezis.Chapter03.IsReflexive`. The
proof uses the reflexivity of $L^p(\Omega)$ (Theorem 4.10 of the source). -/
theorem proposition_9_1_reflexive (hp : 1 < p) (hp' : p ≠ ⊤) :
    Chapter03.IsReflexive (sobolevSpace N p Ω) := by
  have := Chapter04.theorem_4_10 (μ := volume.restrict (Ω : Set 𝔼)) hp hp'
  exact Chapter03.isReflexive_iff.2 inferInstance

/-- **Proposition 9.1** of [brezis2011functional], third clause. For $1 \le p < \infty$ the space
$W^{1,p}(\Omega)$ is separable.

Separability is the definition of Section 3.6 of the source, `Brezis.Chapter03.IsSeparable`. -/
theorem proposition_9_1_separable (hp' : p ≠ ⊤) : Chapter03.IsSeparable (sobolevSpace N p Ω) := by
  have := Fact.mk hp'
  exact (Chapter03.separable_iff _).2 inferInstance

/-- **Proposition 9.1** of [brezis2011functional], last clause. The space $H^1(\Omega)$ is a
separable Hilbert space: it is complete and separable, and its inner product is the instance of
the type, which is the scalar product of the source by `Brezis.Chapter09.hInner`. -/
theorem proposition_9_1_hilbert :
    CompleteSpace (hSpace N Ω) ∧ Chapter03.IsSeparable (hSpace N Ω) :=
  ⟨proposition_9_1_banach, proposition_9_1_separable (by simp)⟩

/-- **Proposition 9.1** of [brezis2011functional]. Let $1 \le p \le \infty$. The space
$W^{1,p}(\Omega)$ is a Banach space. It is reflexive for $1 < p < \infty$ and separable for
$1 \le p < \infty$. The space $H^1(\Omega)$ is a separable Hilbert space.

Reflexivity and separability are `Brezis.Chapter03.IsReflexive` and
`Brezis.Chapter03.IsSeparable`. The proof is that of the backbone: $W^{1,p}(\Omega)$ is a closed
subspace of the $\ell^p$ product of $N + 1$ copies of $L^p(\Omega)$, and the operator
$Tu = [u, \nabla u]$ of the proof of Proposition 8.1 in the source is the inclusion. -/
theorem proposition_9_1 :
    CompleteSpace (sobolevSpace N p Ω) ∧
    (1 < p → p ≠ ⊤ → Chapter03.IsReflexive (sobolevSpace N p Ω)) ∧
    (p ≠ ⊤ → Chapter03.IsSeparable (sobolevSpace N p Ω)) ∧
    (CompleteSpace (hSpace N Ω) ∧ Chapter03.IsSeparable (hSpace N Ω)) :=
  ⟨proposition_9_1_banach, proposition_9_1_reflexive, proposition_9_1_separable,
    proposition_9_1_hilbert⟩

/-! ### The tensor gradient -/

omit [Fact (1 ≤ p)] in
/-- The gradient of $u \in W^{1,p}(\Omega)$ is almost everywhere strongly measurable on $\Omega$. -/
theorem aestronglyMeasurable_gradient (u : sobolevSpace N p Ω) :
    AEStronglyMeasurable (gradient u) (volume.restrict (Ω : Set 𝔼)) :=
  (PiLp.continuous_toLp 2 _).comp_aestronglyMeasurable
    (aemeasurable_pi_iff.2 fun i ↦
      (Lp.aestronglyMeasurable (partialDeriv u i)).aemeasurable).aestronglyMeasurable

/-- A continuous linear functional $L$ on $\mathbb{R}^N$ has the norm
$\|L\| = |(L e_1, \dots, L e_N)|$, the Euclidean norm of the vector of its values on the
standard basis. -/
theorem norm_eq_norm_toLp_apply_single (L : 𝔼 →L[ℝ] ℝ) :
    ‖L‖ = ‖(WithLp.toLp 2 fun i ↦ L (EuclideanSpace.single i 1) : 𝔼)‖ := by
  have h : L = innerSL ℝ (E := 𝔼) (WithLp.toLp 2 fun i ↦ L (EuclideanSpace.single i 1)) := by
    refine ContinuousLinearMap.coe_injective ((𝔟).ext fun i ↦ ?_)
    simp [EuclideanSpace.inner_single_right]
  conv_lhs => rw [h]
  exact innerSL_apply_norm (𝕜 := ℝ) (E := 𝔼) _

/-- Let $u \in W^{1,p}(\Omega)$. There is a first-order weak derivative $w : \mathbb{R}^N \to
\mathcal{L}(\mathbb{R}^N, \mathbb{R})$ of $u$ on $\Omega$ such that $w \in L^p(\Omega)$,
$w(x) e_i = \partial u / \partial x_i (x)$ almost everywhere on $\Omega$ for each $i$,
$\|w(x)\| = |\nabla u(x)|$ almost everywhere on $\Omega$, and
$$\|w\|_{L^p(\Omega)} = \|\nabla u\|_{L^p(\Omega)}.$$

The weak derivative is in the sense of `HasWeakFDerivOn`, with the operator norm on
$\mathcal{L}(\mathbb{R}^N, \mathbb{R})$. This connects the partial derivatives of the source to
the backbone theorems, which are stated for this derivative.

**Reading.** The library packages the coordinate derivatives as a field of real linear
 functionals and identifies its norm with the Euclidean gradient norm. -/
theorem exists_hasWeakFDerivOn_fn_gradient (u : sobolevSpace N p Ω) :
    ∃ w : 𝔼 → 𝔼 →L[ℝ] ℝ, HasWeakFDerivOn (SobolevMultiIndex.fn u) w Ω volume ∧
      MemLp w p (volume.restrict (Ω : Set 𝔼)) ∧
      (∀ i, (fun x ↦ w x (EuclideanSpace.single i 1)) =ᵐ[volume.restrict (Ω : Set 𝔼)]
        partialDeriv u i) ∧
      (∀ᵐ x ∂volume.restrict (Ω : Set 𝔼), ‖w x‖ = ‖gradient u x‖) ∧
      eLpNorm w p (volume.restrict (Ω : Set 𝔼)) = eLpNorm (gradient u) p (volume.restrict Ω) := by
  obtain ⟨w, hw, hwp, hwi, -⟩ := SobolevMultiIndex.exists_hasWeakFDerivOn_fn (b := 𝔟) u
  have hwi' : ∀ i, (fun x ↦ w x (EuclideanSpace.single i 1)) =ᵐ[volume.restrict (Ω : Set 𝔼)]
      partialDeriv u i := fun i ↦ by
    have := hwi i
    rwa [basisFun_toBasis_apply] at this
  have hnorm : ∀ᵐ x ∂volume.restrict (Ω : Set 𝔼), ‖w x‖ = ‖gradient u x‖ := by
    filter_upwards [ae_all_iff.2 hwi'] with x hx
    rw [norm_eq_norm_toLp_apply_single (w x)]
    congr 2
    funext i
    exact hx i
  refine ⟨w, hw, hwp, hwi', hnorm, ?_⟩
  exact eLpNorm_congr_norm_ae hwp.aestronglyMeasurable (aestronglyMeasurable_gradient u) hnorm

/-- The gradient of $u \in W^{1,p}(\Omega)$ lies in $L^p(\Omega)$. -/
theorem memLp_gradient (u : sobolevSpace N p Ω) :
    MemLp (gradient u) p (volume.restrict (Ω : Set 𝔼)) := by
  obtain ⟨w, -, hwp, -, -, heq⟩ := exists_hasWeakFDerivOn_fn_gradient u
  rw [memLp_iff, ← heq]
  exact hwp

/-! ### Remark 2: functions of class $C^1$ -/

/-- **Remark 2** in Chapter 9 of [brezis2011functional], first part. Let $1 \le p \le \infty$ and
let $u \in C^1(\Omega) \cap L^p(\Omega)$ be such that its classical partial derivatives
$\partial u / \partial x_i$ lie in $L^p(\Omega)$ for $i = 1, \dots, N$. Then $u$ is, almost
everywhere on $\Omega$, the function of an element $v$ of $W^{1,p}(\Omega)$, and the weak
partial derivatives of $v$ are the classical partial derivatives of $u$ almost everywhere on
$\Omega$. So the notation is consistent.

The space $C^1(\Omega)$ is `ContDiffOn ℝ 1 u Ω`, and the classical partial derivative is
`fderiv ℝ u x (EuclideanSpace.single i 1)`. -/
theorem remark_9_2 {u : 𝔼 → ℝ} (hu : ContDiffOn ℝ 1 u Ω) (hup : MemLp u p (volume.restrict Ω))
    (hd : ∀ i, MemLp (fun x ↦ fderiv ℝ u x (EuclideanSpace.single i 1)) p (volume.restrict Ω)) :
    ∃ v : sobolevSpace N p Ω, SobolevMultiIndex.fn v =ᵐ[volume.restrict (Ω : Set 𝔼)] u ∧
      ∀ i, partialDeriv v i =ᵐ[volume.restrict (Ω : Set 𝔼)]
        fun x ↦ fderiv ℝ u x (EuclideanSpace.single i 1) := by
  refine exists_sobolevSpace_of_hasWeakIteratedLineDerivOn hup (fun i ↦ ?_) hd
  have h := (hu.hasWeakIteratedFDerivOn (μ := volume) (m := 1) le_rfl).lineDeriv
    ![EuclideanSpace.single i 1]
  simpa [iteratedFDeriv_one_apply] using h

/-- **Remark 2** in Chapter 9 of [brezis2011functional], "in particular". Let $\Omega$ be bounded
and $1 \le p \le \infty$. Every $u \in C^1(\bar\Omega)$ is, almost everywhere on $\Omega$, the
function of an element of $W^{1,p}(\Omega)$.

**Reading.** The space $C^1(\bar\Omega)$ is read as the functions
$u : \mathbb{R}^N \to \mathbb{R}$ that are of class $C^1$ on $\bar\Omega$ in the sense of
`ContDiffOn ℝ 1 u (closure Ω)`.

The function $u$ and its derivative are bounded on $\Omega$, and $\Omega$ has finite measure, so
$u$ and its partial derivatives lie in $L^p(\Omega)$. -/
theorem remark_9_2_closure (hΩ : Bornology.IsBounded (Ω : Set 𝔼)) {u : 𝔼 → ℝ}
    (hu : ContDiffOn ℝ 1 u (closure Ω)) :
    ∃ v : sobolevSpace N p Ω, SobolevMultiIndex.fn v =ᵐ[volume.restrict (Ω : Set 𝔼)] u := by
  have hs := Ω.isOpen.measurableSet
  have : IsFiniteMeasure (volume.restrict (Ω : Set 𝔼)) :=
    ⟨by simpa [Measure.restrict_apply_univ] using hΩ.measure_lt_top⟩
  have hΩc : IsCompact (closure (Ω : Set 𝔼)) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure hΩ.closure
  have hu' : ContDiffOn ℝ 1 u Ω := hu.mono subset_closure
  obtain ⟨C, hC⟩ := hΩc.exists_bound_of_continuousOn hu.continuousOn
  obtain ⟨M, hM⟩ := hu.exists_norm_fderiv_le_of_isCompact hΩc
  have hΩi : (Ω : Set 𝔼) ⊆ interior (closure (Ω : Set 𝔼)) :=
    Ω.isOpen.subset_interior_iff.2 subset_closure
  have hup : MemLp u p (volume.restrict Ω) :=
    MemLp.of_bound (hu'.continuousOn.aestronglyMeasurable hs) C
      ((ae_restrict_iff' hs).2 (Eventually.of_forall fun x hx ↦ hC x (subset_closure hx)))
  have hd : ∀ i, MemLp (fun x ↦ fderiv ℝ u x (EuclideanSpace.single i 1)) p
      (volume.restrict Ω) := fun i ↦
    MemLp.of_bound (((hu'.continuousOn_fderiv_of_isOpen Ω.isOpen le_rfl).clm_apply
      continuousOn_const).aestronglyMeasurable hs) M
      ((ae_restrict_iff' hs).2 (Eventually.of_forall fun x hx ↦ by
        calc ‖fderiv ℝ u x (EuclideanSpace.single i 1)‖
            ≤ ‖fderiv ℝ u x‖ * ‖(EuclideanSpace.single i (1 : ℝ) : 𝔼)‖ :=
              ContinuousLinearMap.le_opNorm _ _
          _ ≤ M := by simpa using hM x (hΩi hx)))
  obtain ⟨v, hv, -⟩ := remark_9_2 hu' hup hd
  exact ⟨v, hv⟩

/-- **Remark 2** in Chapter 9 of [brezis2011functional], converse. Let $1 \le p \le \infty$ and
$u \in W^{1,p}(\Omega)$, and let $g_1, \dots, g_N$ be continuous on $\Omega$ with
$\partial u / \partial x_i = g_i$ almost everywhere on $\Omega$ for each $i$. Then
$u \in C^1(\Omega)$: there is a function $\tilde u$ of class $C^1$ on $\Omega$ with
$u = \tilde u$ almost everywhere on $\Omega$ and $\partial \tilde u / \partial x_i (x) = g_i(x)$
for every $x \in \Omega$ and every $i$. -/
theorem remark_9_2_converse (u : sobolevSpace N p Ω) {g : Fin N → 𝔼 → ℝ}
    (hg : ∀ i, ContinuousOn (g i) Ω)
    (hgu : ∀ i, partialDeriv u i =ᵐ[volume.restrict (Ω : Set 𝔼)] g i) :
    ∃ ũ : 𝔼 → ℝ, ContDiffOn ℝ 1 ũ Ω ∧ SobolevMultiIndex.fn u =ᵐ[volume.restrict (Ω : Set 𝔼)] ũ ∧
      ∀ x ∈ (Ω : Set 𝔼), ∀ i, fderiv ℝ ũ x (EuclideanSpace.single i 1) = g i x := by
  have hs := Ω.isOpen.measurableSet
  obtain ⟨w, hw, -, hwi, -, -⟩ := exists_hasWeakFDerivOn_fn_gradient u
  -- the continuous tensor gradient assembled from the `g_i`
  set W : 𝔼 → 𝔼 →L[ℝ] ℝ := fun x ↦ innerSL ℝ (E := 𝔼) (WithLp.toLp 2 fun i ↦ g i x)
    with hWdef
  have hWi : ∀ x i, W x (EuclideanSpace.single i 1) = g i x := fun x i ↦ by
    simp [hWdef, EuclideanSpace.inner_single_right]
  have hWc : ContinuousOn W Ω := by
    refine (innerSL ℝ).continuous.comp_continuousOn
      ((PiLp.continuous_toLp 2 _).comp_continuousOn (continuousOn_pi.2 fun i ↦ hg i))
  have hwW : w =ᵐ[volume.restrict (Ω : Set 𝔼)] W := by
    filter_upwards [ae_all_iff.2 fun i ↦ (hwi i).trans (hgu i)] with x hx
    refine ContinuousLinearMap.coe_injective ((𝔟).ext fun i ↦ ?_)
    rw [basisFun_toBasis_apply]
    simpa [hWi] using hx i
  have hW : HasWeakFDerivOn (SobolevMultiIndex.fn u) W Ω volume :=
    HasWeakIteratedFDerivOn.congr_ae hw (Filter.EventuallyEq.refl _ _)
      (hwW.mono fun x hx ↦ by simp only [hx])
  obtain ⟨ũ, hũ, hu, hd⟩ := hW.exists_contDiffOn_ae_eq_of_continuousOn hWc
  exact ⟨ũ, hũ, hu, fun x hx i ↦ by rw [(hd x hx).fderiv, hWi]⟩


/-! ### Convergence in $W^{1,p}(\Omega)$ -/

/-- For $u \in W^{1,p}(\Omega)$ and $f \in L^p(\Omega)$, the $L^p(\Omega)$ norm of the difference of
the function of $u$ and $f$ is the distance in $L^p(\Omega)$ of $u$, as an element of
$L^p(\Omega)$, and $f$.

The element of $L^p(\Omega)$ is the image of $u$ under the inclusion `SobolevMultiIndex.fnL`,
and the norm is `eLpNorm`, an extended real. -/
theorem eLpNorm_fn_sub_eq (u : sobolevSpace N p Ω) (f : Lp ℝ p (volume.restrict (Ω : Set 𝔼))) :
    eLpNorm (SobolevMultiIndex.fn u - ⇑f) p (volume.restrict (Ω : Set 𝔼))
      = ENNReal.ofReal ‖SobolevMultiIndex.fnL ℝ 𝔟 1 p Ω volume u - f‖ := by
  rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _),
    eLpNorm_congr_ae (Lp.coeFn_sub _ _), SobolevMultiIndex.fnL_apply]

/-- Let $u_n \in W^{1,p}(\Omega)$ and $f \in L^p(\Omega)$. If $u_n \to f$ in $L^p(\Omega)$, then
$\|u_n - f\|_{L^p(\Omega)} \to 0$ for the functions of the $u_n$, with the norm `eLpNorm`. -/
theorem tendsto_eLpNorm_fn_sub_of_tendsto {u : ℕ → sobolevSpace N p Ω}
    {f : Lp ℝ p (volume.restrict (Ω : Set 𝔼))}
    (hf : Tendsto (fun n ↦ SobolevMultiIndex.fnL ℝ 𝔟 1 p Ω volume (u n)) atTop (𝓝 f)) :
    Tendsto (fun n ↦ eLpNorm (SobolevMultiIndex.fn (u n) - ⇑f) p (volume.restrict (Ω : Set 𝔼)))
      atTop (𝓝 0) := by
  simp only [eLpNorm_fn_sub_eq]
  rw [← ENNReal.ofReal_zero]
  exact ENNReal.tendsto_ofReal (tendsto_iff_norm_sub_tendsto_zero.1 hf)

/-- Let $1 \le p < \infty$, let $w_n, u \in W^{1,p}(\Omega)$, and let
$v_n : \mathbb{R}^N \to \mathbb{R}$ be such that the function of $w_n$ equals $v_n$ almost
everywhere on $\Omega$. If the Sobolev norm of $v_n - u$ in the backbone formulation
`sobolevNorm` tends to $0$, then $w_n \to u$ in $W^{1,p}(\Omega)$.

The backbone norm $\operatorname{sobolevNorm} f = (\|f\|_p^p + \|Df\|_p^p)^{1/p}$ measures the
weak derivative $Df$ as a field of linear maps. The proof compares the two norms by
`SobolevMultiIndex.ofReal_norm_le_sobolevNorm`.

**Reading.** This direction translates convergence in the source's sum norm on raw
 representatives into convergence in the bundled norm for finite $p$. -/
theorem tendsto_of_tendsto_sobolevNorm (hp' : p ≠ ⊤) {w : ℕ → sobolevSpace N p Ω}
    {u : sobolevSpace N p Ω} {v : ℕ → 𝔼 → ℝ}
    (hw : ∀ n, SobolevMultiIndex.fn (w n) =ᵐ[volume.restrict (Ω : Set 𝔼)] v n)
    (h : Tendsto (fun n ↦ sobolevNorm (v n - SobolevMultiIndex.fn u) 1 p Ω volume) atTop
      (𝓝 0)) :
    Tendsto w atTop (𝓝 u) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsub : ∀ n, sobolevNorm (SobolevMultiIndex.fn (w n - u)) 1 p Ω volume
      = sobolevNorm (v n - SobolevMultiIndex.fn u) 1 p Ω volume := fun n ↦
    sobolevNorm_congr_ae ((SobolevMultiIndex.fn_sub _ _).trans
      ((hw n).sub (Filter.EventuallyEq.refl _ _)))
  obtain ⟨C, hC, hCle⟩ : ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ n, ENNReal.ofReal ‖w n - u‖
      ≤ C * sobolevNorm (v n - SobolevMultiIndex.fn u) 1 p Ω volume := by
    refine ⟨_, ?_, fun n ↦ by
      rw [← hsub n]
      exact SobolevMultiIndex.ofReal_norm_le_sobolevNorm hp' (w n - u)⟩
    exact ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.sum_ne_top.2 fun _ _ ↦ enorm_ne_top⟩
  have hfin : ∀ᶠ n in atTop, sobolevNorm (v n - SobolevMultiIndex.fn u) 1 p Ω volume ≠ ⊤ := by
    filter_upwards [ENNReal.tendsto_nhds_zero.1 h 1 one_pos] with n hn
    exact (hn.trans_lt ENNReal.one_lt_top).ne
  have hbound : ∀ n, sobolevNorm (v n - SobolevMultiIndex.fn u) 1 p Ω volume ≠ ⊤ →
      ‖w n - u‖ ≤ (C * sobolevNorm (v n - SobolevMultiIndex.fn u) 1 p Ω volume).toReal :=
    fun n hn ↦ (ENNReal.toReal_ofReal (norm_nonneg _)).symm.le.trans
      (ENNReal.toReal_mono (ENNReal.mul_ne_top hC hn) (hCle n))
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) (hfin.mono hbound) ?_
  have h1 : Tendsto (fun n ↦ C * sobolevNorm (v n - SobolevMultiIndex.fn u) 1 p Ω volume) atTop
      (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul h (Or.inr hC)
  have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
  simpa [Function.comp_def] using this

/-! ### Remark 4 -/

/-- **Remark 4(i)** in Chapter 9 of [brezis2011functional], first sentence. Let
$1 \le p \le \infty$, let $u_n \in W^{1,p}(\Omega)$, and let
$f, g_1, \dots, g_N \in L^p(\Omega)$. If $u_n \to f$ in $L^p(\Omega)$ and
$\partial u_n / \partial x_i \to g_i$ in $L^p(\Omega)$ for each $i$, then there is
$v \in W^{1,p}(\Omega)$ with $v = f$ in $L^p(\Omega)$ and $\partial v / \partial x_i = g_i$ for
each $i$, and $u_n \to v$ in $W^{1,p}(\Omega)$.

This is the closedness of $W^{1,p}(\Omega)$ in the product of $N + 1$ copies of $L^p(\Omega)$,
the argument of the proof of Proposition 9.1. -/
theorem remark_9_4_i {u : ℕ → sobolevSpace N p Ω} {f : Lp ℝ p (volume.restrict (Ω : Set 𝔼))}
    {g : Fin N → Lp ℝ p (volume.restrict (Ω : Set 𝔼))}
    (hf : Tendsto (fun n ↦ SobolevMultiIndex.fnL ℝ 𝔟 1 p Ω volume (u n)) atTop (𝓝 f))
    (hg : ∀ i, Tendsto (fun n ↦ partialDeriv (u n) i) atTop (𝓝 (g i))) :
    ∃ v : sobolevSpace N p Ω, SobolevMultiIndex.fnL ℝ 𝔟 1 p Ω volume v = f ∧
      (∀ i, partialDeriv v i = g i) ∧ Tendsto u atTop (𝓝 v) := by
  classical
  -- the limit family in the ambient `ℓ^p` product of `L^p(Ω)` spaces
  let F : MultiIndexLE (Fin N) 1 → Lp ℝ p (volume.restrict (Ω : Set 𝔼)) := fun α ↦
    if h : ∃ i, α = MultiIndexLE.single i then g h.choose else f
  have hF0 : F 0 = f := by
    have h : ¬ ∃ i, (0 : MultiIndexLE (Fin N) 1) = MultiIndexLE.single i :=
      fun ⟨i, hi⟩ ↦ MultiIndexLE.single_ne_zero i hi.symm
    simp only [F, h, ↓reduceDIte]
  have hFi : ∀ i, F (MultiIndexLE.single i) = g i := fun i ↦ by
    have h : ∃ j, MultiIndexLE.single i = MultiIndexLE.single j := ⟨i, rfl⟩
    simp only [F, h, ↓reduceDIte]
    exact congrArg g (MultiIndexLE.single_injective h.choose_spec).symm
  have htend : Tendsto (fun n ↦ (u n : SobolevMultiIndexTuple ℝ (Fin N) 1 p Ω volume)) atTop
      (𝓝 (WithLp.toLp p F)) := by
    have h1 : Tendsto (fun n ↦ WithLp.ofLp (u n : SobolevMultiIndexTuple ℝ (Fin N) 1 p Ω volume))
        atTop (𝓝 F) := by
      refine tendsto_pi_nhds.2 fun α ↦ ?_
      rcases MultiIndexLE.eq_zero_or_exists_eq_single α with rfl | ⟨i, rfl⟩
      · rw [hF0]
        have h := hf
        simp only [SobolevMultiIndex.fnL_eq_weakDeriv_zero] at h
        exact h
      · rw [hFi]
        exact hg i
    have h2 := ((PiLp.continuous_toLp p _).tendsto F).comp h1
    simpa [Function.comp_def] using h2
  have hmem : WithLp.toLp p F ∈ SobolevMultiIndex ℝ 𝔟 1 p Ω volume :=
    SobolevMultiIndex.isClosed.mem_of_tendsto htend (Eventually.of_forall fun n ↦ (u n).2)
  refine ⟨⟨WithLp.toLp p F, hmem⟩, ?_, fun i ↦ ?_, tendsto_subtype_rng.2 htend⟩
  · rw [SobolevMultiIndex.fnL_eq_weakDeriv_zero]
    exact hF0
  · exact hFi i

/-- **Remark 4(i)** in Chapter 9 of [brezis2011functional], second sentence. Let $1 < p \le \infty$,
let $u_n \in W^{1,p}(\Omega)$ and $f \in L^p(\Omega)$. If $u_n \to f$ in $L^p(\Omega)$ and
$(\nabla u_n)$ is bounded in $L^p(\Omega)^N$, that is, there is $M$ with
$\|\partial u_n / \partial x_i\|_p \le M$ for all $n$ and $i$, then $f \in W^{1,p}(\Omega)$:
there is $v \in W^{1,p}(\Omega)$ with $v = f$ in $L^p(\Omega)$.

The proof answers the question "why?" of the source: the bound (ii) of Proposition 9.3 for the
$u_n$ passes to the limit, and (ii) ⇒ (i) applies. The conjugate exponent $p'$ is `q`, and
$p > 1$ makes $p' < \infty$. -/
theorem remark_9_4_i_bounded {q : ℝ≥0∞} [p.HolderConjugate q] (hp : 1 < p)
    {u : ℕ → sobolevSpace N p Ω} {f : Lp ℝ p (volume.restrict (Ω : Set 𝔼))}
    (hf : Tendsto (fun n ↦ SobolevMultiIndex.fnL ℝ 𝔟 1 p Ω volume (u n)) atTop (𝓝 f))
    {M : ℝ} (hM : ∀ n i, ‖partialDeriv (u n) i‖ ≤ M) :
    ∃ v : sobolevSpace N p Ω, SobolevMultiIndex.fnL ℝ 𝔟 1 p Ω volume v = f := by
  have hq : q ≠ ⊤ :=
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt (p := q) (q := p)).2 hp).ne
  choose w hw hwp hwi hwb using fun n ↦ SobolevMultiIndex.exists_hasWeakFDerivOn_fn (b := 𝔟) (u n)
  obtain ⟨Cb, hCb⟩ : ∃ Cb : ℝ, Cb = Fintype.card (Fin N) •
    ‖(𝔟).equivFunL.toContinuousLinearMap‖ := ⟨_, rfl⟩
  have hwM : ∀ n, eLpNorm (w n) p (volume.restrict (Ω : Set 𝔼))
      ≤ ENNReal.ofReal Cb * (N * ENNReal.ofReal M) := fun n ↦ by
    refine (hwb n).trans ?_
    rw [hCb]
    gcongr
    calc ∑ i, eLpNorm (SobolevMultiIndex.weakDeriv (u n) (MultiIndexLE.single i)) p
          (volume.restrict (Ω : Set 𝔼))
        = ∑ i, ENNReal.ofReal ‖partialDeriv (u n) i‖ := Finset.sum_congr rfl fun i _ ↦ by
          rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]
          rfl
      _ ≤ ∑ _i : Fin N, ENNReal.ofReal M :=
          Finset.sum_le_sum fun i _ ↦ ENNReal.ofReal_le_ofReal (hM n i)
      _ = N * ENNReal.ofReal M := by simp
  have hmem : MemSobolev (f : 𝔼 → ℝ) 1 p Ω volume :=
    MemSobolev.of_tendsto_eLpNorm_of_eLpNorm_le hq (fun n ↦ SobolevMultiIndex.memLp (u n)) hw
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top))
      hwM (Lp.memLp f) (tendsto_eLpNorm_fn_sub_of_tendsto hf)
  obtain ⟨v, hv⟩ := hmem.memSobolevMultiIndex.exists_sobolevMultiIndex (b := 𝔟)
  refine ⟨v, Lp.ext ?_⟩
  rw [SobolevMultiIndex.fnL_apply]
  exact hv

/-- **Remark 4(ii)** in Chapter 9 of [brezis2011functional], last sentence. Let $1 \le p \le \infty$
and $u \in W^{1,p}(\Omega)$, and let $\alpha : \mathbb{R}^N \to \mathbb{R}$ be of class
$C^\infty$, bounded with bounded derivative, with $\operatorname{supp} \alpha \subseteq
\mathbb{R}^N \setminus \partial\Omega$. Then the extension by zero $\overline{\alpha u}$ of
$\alpha u$ outside $\Omega$ lies in $W^{1,p}(\mathbb{R}^N)$, with
$$\frac{\partial}{\partial x_i} \overline{\alpha u} = \overline{\alpha \frac{\partial
  u}{\partial x_i} + \frac{\partial \alpha}{\partial x_i} u}$$
almost everywhere, for each $i$.

The hypothesis on $\alpha$ is the backbone's `IsSobolevCutoff Ω α`. The source asks for $\alpha
\in C^1(\mathbb{R}^N) \cap L^\infty(\mathbb{R}^N)$ with $\nabla\alpha \in L^\infty$; the case of
an $\alpha$ of class $C^1$ that is not of class $C^\infty$ is not formalized.

**Reading.** The cutoff is required to be smooth in the library. The source requires $C^1$. -/
theorem remark_9_4_ii_cutoff (u : sobolevSpace N p Ω) {α : 𝔼 → ℝ} (hα : IsSobolevCutoff Ω α) :
    ∃ v : sobolevSpace N p ⊤,
      SobolevMultiIndex.fn v =ᵐ[volume]
        (Ω : Set 𝔼).indicator (fun x ↦ α x * SobolevMultiIndex.fn u x) ∧
      ∀ i, partialDeriv v i =ᵐ[volume] (Ω : Set 𝔼).indicator fun x ↦
        α x * partialDeriv u i x
          + fderiv ℝ α x (EuclideanSpace.single i 1) * SobolevMultiIndex.fn u x := by
  have hp : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hmem := (SobolevMultiIndex.memSobolevMultiIndex u).indicator_mul hp hα
  have hg : ∀ i, HasWeakIteratedLineDerivOn ![EuclideanSpace.single i 1]
      ((Ω : Set 𝔼).indicator fun x ↦ α x * SobolevMultiIndex.fn u x)
      ((Ω : Set 𝔼).indicator fun x ↦ α x * partialDeriv u i x
        + fderiv ℝ α x (EuclideanSpace.single i 1) * SobolevMultiIndex.fn u x) ⊤ volume :=
    fun i ↦ (hasWeakIteratedLineDerivOn_partialDeriv u i).indicator_mul hα
  obtain ⟨v, hv, hvi⟩ := exists_sobolevSpace_of_hasWeakIteratedLineDerivOn hmem.memLp hg
    fun i ↦ memLp_of_memSobolevMultiIndex_of_hasWeakIteratedLineDerivOn hmem (hg i)
  exact ⟨v, eventuallyEq_restrict_coe_top_iff.1 hv,
    fun i ↦ eventuallyEq_restrict_coe_top_iff.1 (hvi i)⟩

/-- **Remark 4(ii)** in Chapter 9 of [brezis2011functional]. Let $1 \le p \le \infty$ and
$u \in W^{1,p}(\Omega)$, and let $\alpha : \mathbb{R}^N \to \mathbb{R}$ be of class $C^\infty$
with compact support contained in $\Omega$. Then the extension by zero $\overline{\alpha u}$ of
$\alpha u$ outside $\Omega$ lies in $W^{1,p}(\mathbb{R}^N)$, with
$$\frac{\partial}{\partial x_i} \overline{\alpha u} = \overline{\alpha \frac{\partial
  u}{\partial x_i} + \frac{\partial \alpha}{\partial x_i} u}$$
almost everywhere, for each $i$.

The source asks for $\alpha \in C_c^1(\Omega)$; the case of an $\alpha$ of class $C^1$ that is
not of class $C^\infty$ is not formalized. The proof specializes
`Brezis.Chapter09.remark_9_4_ii_cutoff`.

**Reading.** The cutoff is required to be smooth in the library. The source requires $C^1$. -/
theorem remark_9_4_ii (u : sobolevSpace N p Ω) {α : 𝔼 → ℝ} (hα : ContDiff ℝ ∞ α)
    (hαc : HasCompactSupport α) (hαΩ : tsupport α ⊆ Ω) :
    ∃ v : sobolevSpace N p ⊤,
      SobolevMultiIndex.fn v =ᵐ[volume]
        (Ω : Set 𝔼).indicator (fun x ↦ α x * SobolevMultiIndex.fn u x) ∧
      ∀ i, partialDeriv v i =ᵐ[volume] (Ω : Set 𝔼).indicator fun x ↦
        α x * partialDeriv u i x
          + fderiv ℝ α x (EuclideanSpace.single i 1) * SobolevMultiIndex.fn u x :=
  remark_9_4_ii_cutoff u (IsSobolevCutoff.of_hasCompactSupport hα hαc hαΩ)

/-! ### Strong inclusion, and Friedrichs' theorem -/

/-- **Section 9.1** of [brezis2011functional], definition of strong inclusion. An open set $\omega$
is **strongly included** in $\Omega$, written $\omega \subset\subset \Omega$, if
$\bar\omega \subseteq \Omega$ and $\bar\omega$ is compact.

As in footnote 4 of the source, the closure is taken in $\mathbb{R}^N$. The definition includes
the condition that $\omega$ is open. -/
def IsStronglyIncluded (V Ω : Set 𝔼) : Prop :=
  IsOpen V ∧ closure V ⊆ Ω ∧ IsCompact (closure V)

@[inherit_doc] scoped[Brezis] infixl:50 " ⊂⊂ " => Brezis.Chapter09.IsStronglyIncluded

/-- If $\omega \subset\subset \Omega$, then $\omega \subseteq \Omega$. -/
theorem IsStronglyIncluded.subset {V Ω : Set 𝔼} (h : IsStronglyIncluded V Ω) : V ⊆ Ω :=
  subset_closure.trans h.2.1

/-- **Theorem 9.2** of [brezis2011functional] (Friedrichs). Let $1 \le p < \infty$ and
$u \in W^{1,p}(\Omega)$. Then there is a sequence $(u_n)$ of functions of
$C_c^\infty(\mathbb{R}^N)$ such that $u_n|_\Omega \to u$ in $L^p(\Omega)$ and
$\nabla u_n|_\omega \to \nabla u|_\omega$ in $L^p(\omega)^N$ for every
$\omega \subset\subset \Omega$, that is,
$$\Big\|\frac{\partial u_n}{\partial x_i} - \frac{\partial u}{\partial x_i}\Big\|_{L^p(\omega)}
  \to 0 \qquad \text{for every } \omega \subset\subset \Omega \text{ and every } i.$$

The proof specializes `MemSobolev.exists_seq_contDiff_hasCompactSupport_tendsto`, which is
stated for the derivative as a field of linear maps; its values on the basis vectors are the
partial derivatives (`Brezis.Chapter09.exists_hasWeakFDerivOn_fn_gradient`). -/
theorem theorem_9_2 (hp' : p ≠ ⊤) (u : sobolevSpace N p Ω) :
    ∃ v : ℕ → 𝔼 → ℝ, (∀ n, ContDiff ℝ ∞ (v n)) ∧ (∀ n, HasCompactSupport (v n)) ∧
      Tendsto (fun n ↦ eLpNorm (v n - SobolevMultiIndex.fn u) p (volume.restrict (Ω : Set 𝔼)))
        atTop (𝓝 0) ∧
      ∀ V : Set 𝔼, IsStronglyIncluded V Ω → ∀ i,
        Tendsto (fun n ↦ eLpNorm (fun x ↦ fderiv ℝ (v n) x (EuclideanSpace.single i 1)
          - partialDeriv u i x) p (volume.restrict V)) atTop (𝓝 0) := by
  have hf : MemSobolev (SobolevMultiIndex.fn u) 1 p Ω volume :=
    (SobolevMultiIndex.memSobolevMultiIndex u).memSobolev
  obtain ⟨v, hvs, hvc, hv0, hv1⟩ := hf.exists_seq_contDiff_hasCompactSupport_tendsto Fact.out hp'
  obtain ⟨w, hw, hwp, hwi, -, -⟩ := exists_hasWeakFDerivOn_fn_gradient u
  refine ⟨v, hvs, hvc, hv0, fun V hV i ↦ ?_⟩
  have hVΩ : V ⊆ (Ω : Set 𝔼) := hV.subset
  have hVt := hv1 w hw V hV.2.2 hV.2.1
  have hwi' : (fun x ↦ w x (EuclideanSpace.single i 1)) =ᵐ[volume.restrict V] partialDeriv u i :=
    (hwi i).filter_mono (ae_mono (Measure.restrict_mono hVΩ le_rfl))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hVt (fun _ ↦ zero_le)
    fun n ↦ ?_
  calc eLpNorm (fun x ↦ fderiv ℝ (v n) x (EuclideanSpace.single i 1) - partialDeriv u i x) p
        (volume.restrict V)
      = eLpNorm (fun x ↦ ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i (1 : ℝ) : 𝔼)
          (fderiv ℝ (v n) x - w x)) p (volume.restrict V) := by
        refine eLpNorm_congr_ae (hwi'.mono fun x hx ↦ ?_)
        simp only [ContinuousLinearMap.apply_apply, sub_apply]
        rw [← hx]
    _ ≤ ‖ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i (1 : ℝ) : 𝔼)‖ₑ
          * eLpNorm (fun x ↦ fderiv ℝ (v n) x - w x) p (volume.restrict V) :=
        eLpNorm_comp_continuousLinearMap_le _ _ p
    _ ≤ 1 * eLpNorm (fun x ↦ fderiv ℝ (v n) x - w x) p (volume.restrict V) := by
        gcongr
        rw [← ofReal_norm, ← ENNReal.ofReal_one]
        refine ENNReal.ofReal_le_ofReal ((ContinuousLinearMap.opNorm_le_bound _ zero_le_one
          fun L ↦ ?_))
        rw [one_mul, ContinuousLinearMap.apply_apply]
        simpa using L.le_opNorm (EuclideanSpace.single i (1 : ℝ) : 𝔼)
    _ = eLpNorm (fun x ↦ fderiv ℝ (v n) x - w x) p (volume.restrict V) := one_mul _

/-- **Theorem 9.2** of [brezis2011functional], the case $\Omega = \mathbb{R}^N$. Let
$1 \le p < \infty$ and $u \in W^{1,p}(\mathbb{R}^N)$. Then there is a sequence $(u_n)$ of
functions of $C_c^\infty(\mathbb{R}^N)$ with $u_n \to u$ in $W^{1,p}(\mathbb{R}^N)$: there are
elements $w_n \in W^{1,p}(\mathbb{R}^N)$ whose functions equal $u_n$ almost everywhere, and
$w_n \to u$. -/
theorem theorem_9_2_univ (hp' : p ≠ ⊤) (u : sobolevSpace N p ⊤) :
    ∃ v : ℕ → 𝔼 → ℝ, (∀ n, ContDiff ℝ ∞ (v n)) ∧ (∀ n, HasCompactSupport (v n)) ∧
      ∃ w : ℕ → sobolevSpace N p ⊤, (∀ n, SobolevMultiIndex.fn (w n) =ᵐ[volume] v n) ∧
        Tendsto w atTop (𝓝 u) := by
  have hf : MemSobolev (SobolevMultiIndex.fn u) 1 p ⊤ volume :=
    (SobolevMultiIndex.memSobolevMultiIndex u).memSobolev
  obtain ⟨v, hvs, hvc, hvt⟩ := hf.exists_seq_hasCompactSupport_tendsto_sobolevNorm Fact.out hp'
  choose w hw using fun n ↦ (hvs n).exists_sobolevMultiIndex_of_hasCompactSupport (b := 𝔟)
    (k := 1) (p := p) (Ω := (⊤ : Opens 𝔼)) (μ := volume) (hvc n)
  exact ⟨v, hvs, hvc, w, fun n ↦ eventuallyEq_restrict_coe_top_iff.1 (hw n),
    tendsto_of_tendsto_sobolevNorm hp' hw hvt⟩

/-- **Lemma 9.1** of [brezis2011functional]. Let $\rho \in L^1(\mathbb{R}^N)$, $1 \le p \le \infty$
and $v \in W^{1,p}(\mathbb{R}^N)$. Then $\rho \star v \in W^{1,p}(\mathbb{R}^N)$ and
$$\frac{\partial}{\partial x_i}(\rho \star v) = \rho \star \frac{\partial v}{\partial x_i}
  \qquad \text{for } i = 1, \dots, N,$$
almost everywhere.

The convolution is $(\rho \star v)(x) = \int \rho(x - y) v(y) \, dy$ of Section 4.4 of the
source, written with `ContinuousLinearMap.mul ℝ ℝ`. -/
theorem lemma_9_1 {ρ : 𝔼 → ℝ} (hρ : Integrable ρ volume) (v : sobolevSpace N p ⊤) :
    ∃ w : sobolevSpace N p ⊤,
      SobolevMultiIndex.fn w =ᵐ[volume]
        ρ ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] SobolevMultiIndex.fn v ∧
      ∀ i, partialDeriv w i =ᵐ[volume]
        ρ ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] partialDeriv v i := by
  have hp : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hv : MemSobolev (SobolevMultiIndex.fn v) 1 p ⊤ volume :=
    (SobolevMultiIndex.memSobolevMultiIndex v).memSobolev
  have hvp : MemLp (SobolevMultiIndex.fn v) p volume := by
    simpa [Measure.restrict_coe_top] using SobolevMultiIndex.memLp v
  have hρ1 : MemLp ρ 1 volume := memLp_one_iff_integrable.2 hρ
  rw [← Chapter04.lsmul_eq_mul_real]
  have hmem := hv.convolution_of_integrable hρ hp
  have hg : ∀ i, HasWeakIteratedLineDerivOn ![EuclideanSpace.single i 1]
      (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] SobolevMultiIndex.fn v)
      (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] partialDeriv v i) ⊤ volume := fun i ↦
    (hasWeakIteratedLineDerivOn_partialDeriv v i).convolution_of_integrable hρ hp hvp
      (by simpa [Measure.restrict_coe_top] using Lp.memLp (partialDeriv v i))
  have hgp : ∀ i, MemLp (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] partialDeriv v i) p
      (volume.restrict ((⊤ : Opens 𝔼) : Set 𝔼)) := fun i ↦ by
    rw [Chapter04.lsmul_eq_mul_real]
    have := MemLp.convolution (L := ContinuousLinearMap.mul ℝ ℝ) hp hρ1
      (g := ⇑(partialDeriv v i))
      (by simpa [Measure.restrict_coe_top] using Lp.memLp (partialDeriv v i))
    simpa [Measure.restrict_coe_top] using this
  obtain ⟨w, hw, hwi⟩ := exists_sobolevSpace_of_hasWeakIteratedLineDerivOn hmem.memLp hg hgp
  exact ⟨w, eventuallyEq_restrict_coe_top_iff.1 hw,
    fun i ↦ eventuallyEq_restrict_coe_top_iff.1 (hwi i)⟩

/-- **Remark 5** in Chapter 9 of [brezis2011functional] (Meyers–Serrin). Let $1 \le p < \infty$ and
$u \in W^{1,p}(\Omega)$. Then there is a sequence $(u_n)$ of functions of
$C^\infty(\Omega) \cap W^{1,p}(\Omega)$ with $u_n \to u$ in $W^{1,p}(\Omega)$: there are
elements $w_n \in W^{1,p}(\Omega)$ whose functions equal $u_n$ almost everywhere on $\Omega$,
and $w_n \to u$.

The second claim of the remark, that for a general $\Omega$ no sequence of functions of
$C_c^1(\mathbb{R}^N)$ need converge to $u$ in $W^{1,p}(\Omega)$, is a counterexample and is not
formalized.

**Reading.** This is the density claim of the remark. The restriction on whole-space
 approximants is a separate counterexample in the source. -/
theorem remark_9_5 (hp' : p ≠ ⊤) (u : sobolevSpace N p Ω) :
    ∃ v : ℕ → 𝔼 → ℝ, (∀ n, ContDiffOn ℝ ∞ (v n) Ω) ∧
      ∃ w : ℕ → sobolevSpace N p Ω,
        (∀ n, SobolevMultiIndex.fn (w n) =ᵐ[volume.restrict (Ω : Set 𝔼)] v n) ∧
        Tendsto w atTop (𝓝 u) := by
  have hf : MemSobolev (SobolevMultiIndex.fn u) 1 p Ω volume :=
    (SobolevMultiIndex.memSobolevMultiIndex u).memSobolev
  obtain ⟨v, hvs, hvm, hvt⟩ := hf.exists_seq_contDiffOn_tendsto_sobolevNorm Fact.out hp'
  choose w hw using fun n ↦
    ((hvm n).memSobolevMultiIndex (b := 𝔟)).exists_sobolevMultiIndex
  exact ⟨v, hvs, w, hw, tendsto_of_tendsto_sobolevNorm hp' hw hvt⟩


/-! ### Proposition 9.3 -/

omit [Fact (1 ≤ p)] in
/-- A function $f \in L^\infty(\mu)$ satisfies $\|f(x)\| \le \|f\|_\infty$ for $\mu$-almost every
$x$. -/
theorem ae_norm_le_toReal_eLpNorm_top {G : Type*} [NormedAddCommGroup G] {μ : Measure 𝔼}
    {f : 𝔼 → G} (hf : MemLp f ⊤ μ) : ∀ᵐ x ∂μ, ‖f x‖ ≤ (eLpNorm f ⊤ μ).toReal := by
  have hne : eLpNorm f ⊤ μ ≠ ⊤ := hf.eLpNorm_ne_top
  rw [eLpNorm_exponent_top hf.aestronglyMeasurable] at hne ⊢
  filter_upwards [ae_le_eLpNormEssSup (f := f) (μ := μ)] with x hx
  rw [← ofReal_norm] at hx
  exact (ENNReal.ofReal_le_iff_le_toReal hne).1 hx

/-- **Proposition 9.3** of [brezis2011functional], (i) ⇒ (ii), with the constant
$C = \|\nabla u\|_{L^p(\Omega)}$. Let $1 \le p \le \infty$ with conjugate exponent $p'$, and let
$u \in W^{1,p}(\Omega)$. Then
$$\Big|\int_\Omega u \frac{\partial \varphi}{\partial x_i}\Big| \le \|\nabla u\|_{L^p(\Omega)}
  \|\varphi\|_{L^{p'}(\Omega)}$$
for every $\varphi \in C_c^\infty(\Omega)$ and every $i$.

The source calls this direction obvious: it is Hölder's inequality applied to the defining
identity. -/
theorem proposition_9_3_i_ii {q : ℝ≥0∞} [p.HolderConjugate q] (u : sobolevSpace N p Ω)
    (φ : 𝓓(Ω, ℝ)) (i : Fin N) :
    ‖∫ x in (Ω : Set 𝔼), SobolevMultiIndex.fn u x * fderiv ℝ φ x (EuclideanSpace.single i 1)‖ₑ
      ≤ eLpNorm (gradient u) p (volume.restrict Ω) * eLpNorm φ q (volume.restrict Ω) := by
  obtain ⟨w, hw, -, -, -, heq⟩ := exists_hasWeakFDerivOn_fn_gradient u
  have h := hw.abs_integral_smul_fderiv_le (p := p) (q := q) φ (EuclideanSpace.single i 1)
  rw [heq] at h
  have h1 : ‖(EuclideanSpace.single i (1 : ℝ) : 𝔼)‖ₑ = 1 := by
    rw [← ofReal_norm]
    simp
  rw [h1, one_mul] at h
  refine le_of_eq_of_le ?_ h
  congr 1
  exact setIntegral_congr_fun Ω.isOpen.measurableSet fun x _ ↦ by rw [smul_eq_mul, mul_comm]

omit [Fact (1 ≤ p)] in
/-- **Proposition 9.3** of [brezis2011functional], (ii) ⇒ (i). Let $1 < p \le \infty$ with conjugate
exponent $p'$, and let $u \in L^p(\Omega)$. If there is a constant $C$ with
$$\Big|\int_\Omega u \frac{\partial \varphi}{\partial x_i}\Big| \le C
  \|\varphi\|_{L^{p'}(\Omega)}$$
for every $\varphi \in C_c^\infty(\Omega)$ and every $i$, then $u \in W^{1,p}(\Omega)$: $u$ is,
almost everywhere on $\Omega$, the function of an element of $W^{1,p}(\Omega)$.

The condition $p > 1$ is $p' < \infty$. The proof is that of Proposition 8.3 of the source: the
Riesz representation theorem in $L^{p'}(\Omega)$ (Theorem 4.11) gives the weak derivatives. -/
theorem proposition_9_3_ii_i {q : ℝ≥0∞} [p.HolderConjugate q] (hp : 1 < p) {u : 𝔼 → ℝ}
    (hu : MemLp u p (volume.restrict Ω)) {C : ℝ}
    (h : ∀ (φ : 𝓓(Ω, ℝ)) (i : Fin N),
      ‖∫ x in (Ω : Set 𝔼), u x * fderiv ℝ φ x (EuclideanSpace.single i 1)‖ₑ
        ≤ ENNReal.ofReal C * eLpNorm φ q (volume.restrict Ω)) :
    ∃ v : sobolevSpace N p Ω, SobolevMultiIndex.fn v =ᵐ[volume.restrict (Ω : Set 𝔼)] u := by
  have hq : q ≠ ⊤ :=
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt (p := q) (q := p)).2 hp).ne
  refine (MemSobolev.of_forall_enorm_integral_smul_fderiv_basis_le hq hu 𝔟
    (C := fun _ ↦ ENNReal.ofReal C) (fun _ ↦ ENNReal.ofReal_ne_top) fun φ i ↦ ?_)
    |>.memSobolevMultiIndex.exists_sobolevMultiIndex
  rw [basisFun_toBasis_apply]
  refine le_of_eq_of_le ?_ (h φ i)
  congr 1
  exact setIntegral_congr_fun Ω.isOpen.measurableSet fun x _ ↦ by rw [smul_eq_mul, mul_comm]

/-- **Proposition 9.3** of [brezis2011functional], the distance from a set $\omega$ to the boundary
of $\Omega$:
$$\operatorname{dist}(\omega, \partial\Omega) = \inf_{x \in \omega} \operatorname{dist}(x,
  \partial\Omega),$$
as an extended real number.

The value is $\infty$ when $\partial\Omega = \emptyset$, which is the case
$\Omega = \mathbb{R}^N$, where every translation makes sense, and also when
$\omega = \emptyset$.

**Reading.** The distance is extended-valued so the empty boundary and the empty inner set
 have value $\infty$. -/
noncomputable def edistFrontier (V Ω : Set 𝔼) : ℝ≥0∞ :=
  ⨅ x ∈ V, Metric.infEDist x (frontier Ω)

/-- Let $\omega \subseteq \Omega$ and $h \in \mathbb{R}^N$ with $|h| < \operatorname{dist}(\omega,
\partial\Omega)$. Then $x + th \in \Omega$ for every $x \in \omega$ and every $t \in [0, 1]$.

This is the statement of the source that $\tau_h u(x) = u(x + h)$ makes sense for $x \in \omega$
and $|h| < \operatorname{dist}(\omega, \partial\Omega)$, in Proposition 9.3. A segment that
leaves the open set $\Omega$ meets its boundary at distance at most $|h|$ from $x$.

**Generalization.** The geometric assertion applies to any subset $\omega \subseteq \Omega$.
 It states containment along the entire translating segment. -/
theorem segment_subset_of_enorm_lt_edistFrontier {V : Set 𝔼} (hVΩ : V ⊆ Ω) {h : 𝔼}
    (hh : ‖h‖ₑ < edistFrontier V Ω) :
    ∀ x ∈ V, ∀ t ∈ Set.Icc (0 : ℝ) 1, x + t • h ∈ (Ω : Set 𝔼) := by
  intro x hx t ht
  have hseg : segment ℝ x (x + h) ⊆ (Ω : Set 𝔼) := by
    refine (convex_segment x (x + h)).isPreconnected.subset_of_closure_inter_subset Ω.isOpen
      ⟨x, left_mem_segment ℝ x (x + h), hVΩ hx⟩ fun z ⟨hzc, hzs⟩ ↦ ?_
    by_contra hzΩ
    have hzf : z ∈ frontier (Ω : Set 𝔼) :=
      ⟨hzc, fun hzi ↦ hzΩ (Ω.isOpen.interior_eq ▸ hzi)⟩
    have h1 : edistFrontier V Ω ≤ edist x z :=
      (iInf₂_le x hx).trans (Metric.infEDist_le_edist_of_mem hzf)
    have h2 : edist x z ≤ ‖h‖ₑ := by
      rw [edist_dist, ← ofReal_norm]
      refine ENNReal.ofReal_le_ofReal ?_
      have := dist_add_dist_of_mem_segment hzs
      have h3 : dist x (x + h) = ‖h‖ := by
        rw [dist_eq_norm, sub_add_cancel_left, norm_neg]
      linarith [dist_nonneg (x := z) (y := x + h)]
    exact (hh.trans_le (h1.trans h2)).false
  refine hseg ?_
  rw [segment_eq_image']
  exact ⟨t, ht, by rw [add_sub_cancel_left]⟩

/-- **Proposition 9.3** of [brezis2011functional], (i) ⇒ (iii), with the constant
$C = \|\nabla u\|_{L^p(\Omega)}$. Let $1 \le p \le \infty$, let $v \in W^{1,p}(\Omega)$, and let
$u$ equal the function of $v$ almost everywhere on $\Omega$. Then for every
$\omega \subset\subset \Omega$ and every $h \in \mathbb{R}^N$ with $|h| <
\operatorname{dist}(\omega, \partial\Omega)$,
$$\|\tau_h u - u\|_{L^p(\omega)} \le \|\nabla v\|_{L^p(\Omega)} |h|,$$
where $\tau_h u(x) = u(x + h)$. -/
theorem proposition_9_3_i_iii (v : sobolevSpace N p Ω) {u : 𝔼 → ℝ}
    (hu : SobolevMultiIndex.fn v =ᵐ[volume.restrict (Ω : Set 𝔼)] u) {V : Set 𝔼}
    (hV : IsStronglyIncluded V Ω) {h : 𝔼} (hh : ‖h‖ₑ < edistFrontier V Ω) :
    eLpNorm (fun x ↦ u (x + h) - u x) p (volume.restrict V)
      ≤ eLpNorm (gradient v) p (volume.restrict Ω) * ‖h‖ₑ := by
  have hs := Ω.isOpen.measurableSet
  have hseg := segment_subset_of_enorm_lt_edistFrontier hV.subset hh
  obtain ⟨w, hw, hwp, -, -, heq⟩ := exists_hasWeakFDerivOn_fn_gradient v
  -- replace `u` by the function of `v` on `ω` and on `ω + h`
  have hu' : ∀ᵐ x ∂volume, x ∈ (Ω : Set 𝔼) → SobolevMultiIndex.fn v x = u x :=
    (ae_restrict_iff' hs).1 hu
  have hu'' : ∀ᵐ x ∂volume, x + h ∈ (Ω : Set 𝔼) → SobolevMultiIndex.fn v (x + h) = u (x + h) :=
    (measurePreserving_add_right volume h).quasiMeasurePreserving.ae hu'
  have hae : (fun x ↦ u (x + h) - u x) =ᵐ[volume.restrict V]
      fun x ↦ SobolevMultiIndex.fn v (x + h) - SobolevMultiIndex.fn v x := by
    filter_upwards [ae_restrict_mem hV.1.measurableSet, ae_restrict_of_ae hu',
      ae_restrict_of_ae hu''] with x hxV h1 h2
    have hx1 : x + h ∈ (Ω : Set 𝔼) := by simpa using hseg x hxV 1 ⟨zero_le_one, le_rfl⟩
    rw [h1 (hV.subset hxV), h2 hx1]
  rw [eLpNorm_congr_ae hae, ← heq, mul_comm]
  rcases eq_or_ne p ⊤ with rfl | hp'
  · exact hw.eLpNorm_sub_translate_le_top hV.1 h hseg
  · exact hw.eLpNorm_sub_translate_le (SobolevMultiIndex.memLp v) hwp Fact.out hp' hV.1 h hseg

/-- **Proposition 9.3** of [brezis2011functional], the case $\Omega = \mathbb{R}^N$. Let
$1 \le p \le \infty$ and $u \in W^{1,p}(\mathbb{R}^N)$. Then for every $h \in \mathbb{R}^N$
$$\|\tau_h u - u\|_{L^p(\mathbb{R}^N)} \le |h| \, \|\nabla u\|_{L^p(\mathbb{R}^N)},$$
where $\tau_h u(x) = u(x + h)$.

**Generalization.** The estimate includes $p=1$. -/
theorem proposition_9_3_univ (u : sobolevSpace N p ⊤) (h : 𝔼) :
    eLpNorm (fun x ↦ SobolevMultiIndex.fn u (x + h) - SobolevMultiIndex.fn u x) p volume
      ≤ ‖h‖ₑ * eLpNorm (gradient u) p volume := by
  obtain ⟨w, hw, hwp, -, -, heq⟩ := exists_hasWeakFDerivOn_fn_gradient u
  rw [eLpNorm_restrict_coe_top, eLpNorm_restrict_coe_top] at heq
  rw [← heq]
  rcases eq_or_ne p ⊤ with rfl | hp'
  · have := hw.eLpNorm_sub_translate_le_top isOpen_univ h fun _ _ _ _ ↦ Set.mem_univ _
    simpa [Measure.restrict_coe_top] using this
  · exact hw.eLpNorm_sub_translate_le_univ
      (by simpa [Measure.restrict_coe_top] using SobolevMultiIndex.memLp u)
      (by simpa [Measure.restrict_coe_top] using hwp) Fact.out hp' h

/-- If $\omega \subset\subset \Omega$, then $\operatorname{dist}(\omega, \partial\Omega) > 0$: there
is $\delta > 0$ with $\delta \le \operatorname{dist}(\omega, \partial\Omega)$.

The compact set $\bar\omega \subseteq \Omega$ has a $\delta$-neighbourhood inside the open set
$\Omega$, and the boundary of $\Omega$ does not meet it. This supports Proposition 9.3 of
[brezis2011functional]. -/
theorem exists_pos_ofReal_le_edistFrontier {V : Set 𝔼} (hV : IsStronglyIncluded V Ω) :
    ∃ δ : ℝ, 0 < δ ∧ ENNReal.ofReal δ ≤ edistFrontier V Ω := by
  obtain ⟨δ, hδ, hδΩ⟩ := hV.2.2.exists_thickening_subset_open Ω.isOpen hV.2.1
  refine ⟨δ, hδ, le_iInf₂ fun x hx ↦ Metric.le_infEDist.2 fun z hz ↦ ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  have hz' : z ∈ thickening δ (closure V) :=
    mem_thickening_iff.2 ⟨x, subset_closure hx, by rwa [dist_comm, ← edist_lt_ofReal]⟩
  refine hz.2 ?_
  rw [Ω.isOpen.interior_eq]
  exact hδΩ hz'

omit [Fact (1 ≤ p)] in
/-- **Proposition 9.3** of [brezis2011functional], (iii) ⇒ (ii). Let $1 \le p \le \infty$ with
conjugate exponent $p'$, and let $u \in L^p(\Omega)$. Suppose that there is a constant $C$ such
that
$$\|\tau_h u - u\|_{L^p(\omega)} \le C |h|$$
for every $\omega \subset\subset \Omega$ and every $h \in \mathbb{R}^N$ with $|h| <
\operatorname{dist}(\omega, \partial\Omega)$. Then
$$\Big|\int_\Omega u \frac{\partial \varphi}{\partial x_i}\Big| \le C
  \|\varphi\|_{L^{p'}(\Omega)}$$
for every $\varphi \in C_c^\infty(\Omega)$ and every $i$.

The proof is that of the source. Choose $\omega \subset\subset \Omega$ with
$\operatorname{supp} \varphi \subseteq \omega$ and $h = t e_i$ with $t$ small. The change of
variables $\int_\Omega (\tau_h u - u) \varphi = \int_\Omega u (\varphi(\cdot - h) - \varphi)$
and Hölder's inequality bound the difference quotients of $\varphi$ against $u$ by
$C \|\varphi\|_{p'}$, and $t \to 0$ gives (ii). The proof specializes
`abs_integral_smul_fderiv_le_of_eLpNorm_sub_translate_le_of_norm_lt`, with the positivity of
$\operatorname{dist}(\omega, \partial\Omega)$ from
`Brezis.Chapter09.exists_pos_ofReal_le_edistFrontier`. -/
theorem proposition_9_3_iii_ii {q : ℝ≥0∞} [p.HolderConjugate q] {u : 𝔼 → ℝ}
    (hu : MemLp u p (volume.restrict Ω)) {C : ℝ}
    (h : ∀ V : Set 𝔼, IsStronglyIncluded V Ω → ∀ h : 𝔼, ‖h‖ₑ < edistFrontier V Ω →
      eLpNorm (fun x ↦ u (x + h) - u x) p (volume.restrict V) ≤ ENNReal.ofReal C * ‖h‖ₑ)
    (φ : 𝓓(Ω, ℝ)) (i : Fin N) :
    ‖∫ x in (Ω : Set 𝔼), u x * fderiv ℝ φ x (EuclideanSpace.single i 1)‖ₑ
      ≤ ENNReal.ofReal C * eLpNorm φ q (volume.restrict Ω) := by
  have key := abs_integral_smul_fderiv_le_of_eLpNorm_sub_translate_le_of_norm_lt (q := q) hu
    (C := ENNReal.ofReal C) (fun V hVo hVc hVΩ ↦ ?_) φ (EuclideanSpace.single i 1)
  · have h1 : ‖(EuclideanSpace.single i (1 : ℝ) : 𝔼)‖ₑ = 1 := by
      rw [← ofReal_norm]
      simp
    rw [h1, mul_one] at key
    refine le_of_eq_of_le ?_ key
    congr 1
    exact setIntegral_congr_fun Ω.isOpen.measurableSet fun x _ ↦ by rw [smul_eq_mul, mul_comm]
  · obtain ⟨δ, hδ, hδV⟩ := exists_pos_ofReal_le_edistFrontier ⟨hVo, hVΩ, hVc⟩
    refine ⟨δ, hδ, fun a ha ↦ h V ⟨hVo, hVΩ, hVc⟩ a ?_⟩
    calc ‖a‖ₑ < ENNReal.ofReal δ := by rwa [← ofReal_norm, ENNReal.ofReal_lt_ofReal_iff hδ]
      _ ≤ edistFrontier V Ω := hδV

/-- **Proposition 9.3** of [brezis2011functional]. Let $1 < p \le \infty$ with conjugate exponent
$p'$, and let $u \in L^p(\Omega)$. The following properties are equivalent:

(i) $u \in W^{1,p}(\Omega)$, that is, $u$ is, almost everywhere on $\Omega$, the function of an
element of $W^{1,p}(\Omega)$;

(ii) there is a constant $C$ such that $\big|\int_\Omega u \, \partial \varphi / \partial
x_i\big| \le C \|\varphi\|_{L^{p'}(\Omega)}$ for all $\varphi \in C_c^\infty(\Omega)$ and all
$i = 1, \dots, N$;

(iii) there is a constant $C$ such that $\|\tau_h u - u\|_{L^p(\omega)} \le C |h|$ for all
$\omega \subset\subset \Omega$ and all $h \in \mathbb{R}^N$ with $|h| <
\operatorname{dist}(\omega, \partial\Omega)$.

The statement of the source that one can take $C = \|\nabla u\|_{L^p(\Omega)}$ in (ii) and (iii)
is `Brezis.Chapter09.proposition_9_3_i_ii` and `Brezis.Chapter09.proposition_9_3_i_iii`. The
case $\Omega = \mathbb{R}^N$ is `Brezis.Chapter09.proposition_9_3_univ`. -/
theorem proposition_9_3 {q : ℝ≥0∞} [p.HolderConjugate q] (hp : 1 < p) {u : 𝔼 → ℝ}
    (hu : MemLp u p (volume.restrict Ω)) :
    [∃ v : sobolevSpace N p Ω, SobolevMultiIndex.fn v =ᵐ[volume.restrict (Ω : Set 𝔼)] u,
      ∃ C : ℝ, ∀ (φ : 𝓓(Ω, ℝ)) (i : Fin N),
        ‖∫ x in (Ω : Set 𝔼), u x * fderiv ℝ φ x (EuclideanSpace.single i 1)‖ₑ
          ≤ ENNReal.ofReal C * eLpNorm φ q (volume.restrict Ω),
      ∃ C : ℝ, ∀ V : Set 𝔼, IsStronglyIncluded V Ω → ∀ h : 𝔼, ‖h‖ₑ < edistFrontier V Ω →
        eLpNorm (fun x ↦ u (x + h) - u x) p (volume.restrict V)
          ≤ ENNReal.ofReal C * ‖h‖ₑ].TFAE := by
  tfae_have 1 → 2 := by
    rintro ⟨v, hv⟩
    refine ⟨(eLpNorm (gradient v) p (volume.restrict Ω)).toReal, fun φ i ↦ ?_⟩
    rw [ENNReal.ofReal_toReal (memLp_gradient v).eLpNorm_ne_top]
    refine le_of_eq_of_le ?_ (proposition_9_3_i_ii v φ i)
    congr 1
    exact integral_congr_ae (hv.symm.mono fun x hx ↦ by simp only [hx])
  tfae_have 2 → 1 := fun ⟨C, hC⟩ ↦ proposition_9_3_ii_i hp hu hC
  tfae_have 1 → 3 := by
    rintro ⟨v, hv⟩
    refine ⟨(eLpNorm (gradient v) p (volume.restrict Ω)).toReal, fun V hV h hh ↦ ?_⟩
    rw [ENNReal.ofReal_toReal (memLp_gradient v).eLpNorm_ne_top]
    exact proposition_9_3_i_iii v hv hV hh
  tfae_have 3 → 2 := fun ⟨C, hC⟩ ↦ ⟨C, proposition_9_3_iii_ii hu hC⟩
  tfae_finish

omit [Fact (1 ≤ p)] in
/-- **Remark 6** in Chapter 9 of [brezis2011functional]. When $p = 1$ the implications (i) ⇒ (ii) ⇔
(iii) of Proposition 9.3 remain true, in part. Let $u \in L^1(\Omega)$, so that $p' = \infty$.
Then (i) ⇒ (ii), (i) ⇒ (iii) and (iii) ⇒ (ii), with the properties (i), (ii) and (iii) of
Proposition 9.3 at $p = 1$.

The three implications of the backbone hold for every $1 \le p \le \infty$. The implication (ii)
⇒ (iii) at $p = 1$, that a function of bounded variation satisfies the estimate on translations,
belongs to the theory of $BV$ functions and is not formalized. The discussion of $BV$ in the
remark is not formalized either.

**Reading.** The statement gives the first and last implications of the source's chain,
 together with (i) ⇒ (iii). The implication (ii) ⇒ (iii) is omitted. -/
theorem remark_9_6 {u : 𝔼 → ℝ} (hu : MemLp u 1 (volume.restrict Ω)) :
    ((∃ v : sobolevSpace N 1 Ω, SobolevMultiIndex.fn v =ᵐ[volume.restrict (Ω : Set 𝔼)] u) →
      ∃ C : ℝ, ∀ (φ : 𝓓(Ω, ℝ)) (i : Fin N),
        ‖∫ x in (Ω : Set 𝔼), u x * fderiv ℝ φ x (EuclideanSpace.single i 1)‖ₑ
          ≤ ENNReal.ofReal C * eLpNorm φ ⊤ (volume.restrict Ω)) ∧
    ((∃ v : sobolevSpace N 1 Ω, SobolevMultiIndex.fn v =ᵐ[volume.restrict (Ω : Set 𝔼)] u) →
      ∃ C : ℝ, ∀ V : Set 𝔼, IsStronglyIncluded V Ω → ∀ h : 𝔼, ‖h‖ₑ < edistFrontier V Ω →
        eLpNorm (fun x ↦ u (x + h) - u x) 1 (volume.restrict V) ≤ ENNReal.ofReal C * ‖h‖ₑ) ∧
    ((∃ C : ℝ, ∀ V : Set 𝔼, IsStronglyIncluded V Ω → ∀ h : 𝔼, ‖h‖ₑ < edistFrontier V Ω →
        eLpNorm (fun x ↦ u (x + h) - u x) 1 (volume.restrict V) ≤ ENNReal.ofReal C * ‖h‖ₑ) →
      ∃ C : ℝ, ∀ (φ : 𝓓(Ω, ℝ)) (i : Fin N),
        ‖∫ x in (Ω : Set 𝔼), u x * fderiv ℝ φ x (EuclideanSpace.single i 1)‖ₑ
          ≤ ENNReal.ofReal C * eLpNorm φ ⊤ (volume.restrict Ω)) := by
  refine ⟨fun ⟨v, hv⟩ ↦ ⟨(eLpNorm (gradient v) 1 (volume.restrict Ω)).toReal, fun φ i ↦ ?_⟩,
    fun ⟨v, hv⟩ ↦ ⟨(eLpNorm (gradient v) 1 (volume.restrict Ω)).toReal, fun V hV h hh ↦ ?_⟩,
    fun ⟨C, hC⟩ ↦ ⟨C, proposition_9_3_iii_ii hu hC⟩⟩
  · rw [ENNReal.ofReal_toReal (memLp_gradient v).eLpNorm_ne_top]
    refine le_of_eq_of_le ?_ (proposition_9_3_i_ii v φ i)
    congr 1
    exact integral_congr_ae (hv.symm.mono fun x hx ↦ by simp only [hx])
  · rw [ENNReal.ofReal_toReal (memLp_gradient v).eLpNorm_ne_top]
    exact proposition_9_3_i_iii v hv hV hh

/-! ### Remark 7 -/

/-- **Remark 7** in Chapter 9 of [brezis2011functional], first sentence. Every
$u \in W^{1,\infty}(\Omega)$ has a representative that is continuous on $\Omega$: there is
$\tilde u$, continuous on $\Omega$, with $u = \tilde u$ almost everywhere on $\Omega$. -/
theorem remark_9_7 (u : sobolevSpace N ⊤ Ω) :
    ∃ ũ : 𝔼 → ℝ, ContinuousOn ũ Ω ∧ SobolevMultiIndex.fn u =ᵐ[volume.restrict (Ω : Set 𝔼)] ũ := by
  obtain ⟨w, hw, hwp, -, -, heq⟩ := exists_hasWeakFDerivOn_fn_gradient u
  obtain ⟨ũ, hũ, hu, -⟩ := hw.exists_continuousOn_ae_eq_of_ae_norm_le ENNReal.toReal_nonneg
    (ae_norm_le_toReal_eLpNorm_top hwp)
  exact ⟨ũ, hũ, hu⟩

/-- **Remark 7** in Chapter 9 of [brezis2011functional], the convex case. Let $\Omega$ be convex and
$u \in W^{1,\infty}(\Omega)$. Then $u$ has a representative $\tilde u$, equal to $u$ almost
everywhere on $\Omega$, with
$$|\tilde u(x) - \tilde u(y)| \le \|\nabla u\|_{L^\infty(\Omega)} |x - y| \qquad \text{for all }
  x, y \in \Omega.$$

The source states the estimate with the geodesic distance in $\Omega$, which is $|x - y|$ for a
convex $\Omega$. The form with the geodesic distance on a nonconvex $\Omega$ is not formalized.

**Reading.** Only the convex case of the geodesic estimate is stated. -/
theorem remark_9_7_convex (hΩ : Convex ℝ (Ω : Set 𝔼)) (u : sobolevSpace N ⊤ Ω) :
    ∃ ũ : 𝔼 → ℝ, SobolevMultiIndex.fn u =ᵐ[volume.restrict (Ω : Set 𝔼)] ũ ∧
      ∀ x ∈ (Ω : Set 𝔼), ∀ y ∈ (Ω : Set 𝔼),
        |ũ x - ũ y| ≤ (eLpNorm (gradient u) ⊤ (volume.restrict Ω)).toReal * ‖x - y‖ := by
  obtain ⟨w, hw, hwp, -, -, heq⟩ := exists_hasWeakFDerivOn_fn_gradient u
  obtain ⟨ũ, hu, hlip⟩ := hw.exists_lipschitzOnWith_ae_eq_of_convex hΩ ENNReal.toReal_nonneg
    (ae_norm_le_toReal_eLpNorm_top hwp)
  refine ⟨ũ, hu, fun x hx y hy ↦ ?_⟩
  have := hlip.dist_le_mul x hx y hy
  rwa [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ ENNReal.toReal_nonneg, heq] at this

/-- **Remark 7** in Chapter 9 of [brezis2011functional], last sentence. Let $1 \le p \le \infty$ and
$u \in W^{1,p}(\Omega)$ with $\nabla u = 0$ almost everywhere on $\Omega$. Then $u$ is constant
almost everywhere on each connected component of $\Omega$: for every $x_0$ there is
$c \in \mathbb{R}$ with $u = c$ almost everywhere on the connected component of $x_0$ in
$\Omega$.

For $x_0 \notin \Omega$ the connected component is empty, and the statement is trivial. -/
theorem remark_9_7_const (u : sobolevSpace N p Ω)
    (h : ∀ i, partialDeriv u i =ᵐ[volume.restrict (Ω : Set 𝔼)] 0) (x₀ : 𝔼) :
    ∃ c : ℝ, SobolevMultiIndex.fn u
      =ᵐ[volume.restrict (connectedComponentIn (Ω : Set 𝔼) x₀)] fun _ ↦ c := by
  obtain ⟨w, hw, -, hwi, -, -⟩ := exists_hasWeakFDerivOn_fn_gradient u
  set Ω' : Opens 𝔼 := ⟨connectedComponentIn (Ω : Set 𝔼) x₀, Ω.isOpen.connectedComponentIn⟩
    with hΩ'
  have hle : Ω' ≤ Ω := connectedComponentIn_subset _ _
  have hw0 : w =ᵐ[volume.restrict (Ω : Set 𝔼)] 0 := by
    filter_upwards [ae_all_iff.2 fun i ↦ (hwi i).trans (h i)] with x hx
    refine ContinuousLinearMap.coe_injective ((𝔟).ext fun i ↦ ?_)
    rw [basisFun_toBasis_apply]
    simpa using hx i
  obtain ⟨c, hc⟩ := (hw.mono hle).ae_eq_const_of_isPreconnected
    (hw0.filter_mono (ae_mono (Measure.restrict_mono hle le_rfl)))
    isPreconnected_connectedComponentIn
  exact ⟨c, hc⟩

/-! ### Propositions 9.4–9.6 -/

/-- **Proposition 9.4** of [brezis2011functional] (differentiation of a product). Let
$1 \le p \le \infty$ and $u, v \in W^{1,p}(\Omega) \cap L^\infty(\Omega)$. Then
$uv \in W^{1,p}(\Omega) \cap L^\infty(\Omega)$ and
$$\frac{\partial}{\partial x_i}(uv) = \frac{\partial u}{\partial x_i} v + u \frac{\partial
  v}{\partial x_i} \qquad \text{for } i = 1, \dots, N,$$
almost everywhere on $\Omega$. -/
theorem proposition_9_4 (u v : sobolevSpace N p Ω)
    (hu : MemLp (SobolevMultiIndex.fn u) ⊤ (volume.restrict Ω))
    (hv : MemLp (SobolevMultiIndex.fn v) ⊤ (volume.restrict Ω)) :
    ∃ w : sobolevSpace N p Ω,
      SobolevMultiIndex.fn w =ᵐ[volume.restrict (Ω : Set 𝔼)]
        (fun x ↦ SobolevMultiIndex.fn u x * SobolevMultiIndex.fn v x) ∧
      MemLp (SobolevMultiIndex.fn w) ⊤ (volume.restrict Ω) ∧
      ∀ i, partialDeriv w i =ᵐ[volume.restrict (Ω : Set 𝔼)] fun x ↦
        partialDeriv u i x * SobolevMultiIndex.fn v x
          + SobolevMultiIndex.fn u x * partialDeriv v i x := by
  have hp : (1 : ℝ≥0∞) ≤ p := Fact.out
  set M : ℝ := max (eLpNorm (SobolevMultiIndex.fn u) ⊤ (volume.restrict Ω)).toReal
    (eLpNorm (SobolevMultiIndex.fn v) ⊤ (volume.restrict Ω)).toReal with hM
  have hMu : ∀ᵐ x ∂volume.restrict (Ω : Set 𝔼), ‖SobolevMultiIndex.fn u x‖ ≤ M :=
    (ae_norm_le_toReal_eLpNorm_top hu).mono fun x hx ↦ hx.trans (le_max_left _ _)
  have hMv : ∀ᵐ x ∂volume.restrict (Ω : Set 𝔼), ‖SobolevMultiIndex.fn v x‖ ≤ M :=
    (ae_norm_le_toReal_eLpNorm_top hv).mono fun x hx ↦ hx.trans (le_max_right _ _)
  obtain ⟨hmem, hbound⟩ := (SobolevMultiIndex.memSobolevMultiIndex u).mul_of_ae_norm_le hp
    (SobolevMultiIndex.memSobolevMultiIndex v) hMu hMv
  have hg : ∀ i, HasWeakIteratedLineDerivOn ![EuclideanSpace.single i 1]
      (fun x ↦ SobolevMultiIndex.fn u x * SobolevMultiIndex.fn v x)
      (fun x ↦ partialDeriv u i x * SobolevMultiIndex.fn v x
        + SobolevMultiIndex.fn u x * partialDeriv v i x) Ω volume := fun i ↦
    (hasWeakIteratedLineDerivOn_partialDeriv u i).mul_of_ae_norm_le
      (hasWeakIteratedLineDerivOn_partialDeriv v i) hMu hMv
  obtain ⟨w, hw, hwi⟩ := exists_sobolevSpace_of_hasWeakIteratedLineDerivOn hmem.memLp hg
    fun i ↦ memLp_of_memSobolevMultiIndex_of_hasWeakIteratedLineDerivOn hmem (hg i)
  refine ⟨w, hw, ?_, hwi⟩
  exact (memLp_top_of_bound hmem.memLp.aestronglyMeasurable (M * M) hbound).ae_eq hw.symm

/-- **Proposition 9.5** of [brezis2011functional] (differentiation of a composition). Let
$G \in C^1(\mathbb{R})$ with $G(0) = 0$ and $|G'(s)| \le M$ for all $s \in \mathbb{R}$, and let
$1 \le p \le \infty$ and $u \in W^{1,p}(\Omega)$. Then $G \circ u \in W^{1,p}(\Omega)$ and
$$\frac{\partial}{\partial x_i}(G \circ u) = (G' \circ u) \frac{\partial u}{\partial x_i} \qquad
  \text{for } i = 1, \dots, N,$$
almost everywhere on $\Omega$. -/
theorem proposition_9_5 {G : ℝ → ℝ} (hG : ContDiff ℝ 1 G) (hG0 : G 0 = 0) {M : ℝ}
    (hM : ∀ s, |deriv G s| ≤ M) (u : sobolevSpace N p Ω) :
    ∃ w : sobolevSpace N p Ω,
      SobolevMultiIndex.fn w =ᵐ[volume.restrict (Ω : Set 𝔼)]
        (fun x ↦ G (SobolevMultiIndex.fn u x)) ∧
      ∀ i, partialDeriv w i =ᵐ[volume.restrict (Ω : Set 𝔼)] fun x ↦
        deriv G (SobolevMultiIndex.fn u x) * partialDeriv u i x := by
  have hp : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hmem := (SobolevMultiIndex.memSobolevMultiIndex u).contDiff_comp hp hG hG0 hM
  have hg : ∀ i, HasWeakIteratedLineDerivOn ![EuclideanSpace.single i 1]
      (fun x ↦ G (SobolevMultiIndex.fn u x))
      (fun x ↦ deriv G (SobolevMultiIndex.fn u x) * partialDeriv u i x) Ω volume := fun i ↦
    (hasWeakIteratedLineDerivOn_partialDeriv u i).contDiff_comp' hG hM
  exact exists_sobolevSpace_of_hasWeakIteratedLineDerivOn hmem.memLp hg
    fun i ↦ memLp_of_memSobolevMultiIndex_of_hasWeakIteratedLineDerivOn hmem (hg i)

/-- **Proposition 9.6** of [brezis2011functional] (change of variables formula). Let
$\Omega, \Omega' \subseteq \mathbb{R}^N$ be open, and let $H : \Omega' \to \Omega$ be a
bijection, $x = H(y)$, with $H \in C^1(\Omega')$, $H^{-1} \in C^1(\Omega)$,
$\operatorname{Jac} H \in L^\infty(\Omega')$ and
$\operatorname{Jac} H^{-1} \in L^\infty(\Omega)$. Let $1 \le p \le \infty$ and
$u \in W^{1,p}(\Omega)$. Then $u \circ H \in W^{1,p}(\Omega')$ and
$$\frac{\partial}{\partial y_j}(u \circ H)(y) = \sum_{i=1}^N \frac{\partial u}{\partial
  x_i}(H(y)) \frac{\partial H_i}{\partial y_j}(y) \qquad \text{for } j = 1, \dots, N,$$
almost everywhere on $\Omega'$.

The hypotheses on $H$ are the backbone's `IsDiffeoOnWithBoundedJacobian H Hinv Ω' Ω M`: the
Jacobian matrices of footnote 6 of the source are the derivatives `fderiv ℝ H y`, bounded in
norm by $M$, and likewise for $H^{-1}$. The entry $\partial H_i / \partial y_j (y)$ is
`fderiv ℝ H y (EuclideanSpace.single j 1) i`. -/
theorem proposition_9_6 {H Hinv : 𝔼 → 𝔼} {Ω' : Opens 𝔼} {M : ℝ}
    (hH : IsDiffeoOnWithBoundedJacobian H Hinv Ω' Ω M) (u : sobolevSpace N p Ω) :
    ∃ w : sobolevSpace N p Ω',
      SobolevMultiIndex.fn w =ᵐ[volume.restrict (Ω' : Set 𝔼)]
        (fun y ↦ SobolevMultiIndex.fn u (H y)) ∧
      ∀ j, partialDeriv w j =ᵐ[volume.restrict (Ω' : Set 𝔼)] fun y ↦
        ∑ i, partialDeriv u i (H y) * fderiv ℝ H y (EuclideanSpace.single j 1) i := by
  obtain ⟨w, hw, -, hwi, -, -⟩ := exists_hasWeakFDerivOn_fn_gradient u
  refine ⟨SobolevEuclidean.compDiffeoL hH u, SobolevMultiIndex.fn_compDiffeoL hH u, fun j ↦ ?_⟩
  -- the tensor gradient evaluated at any vector is the sum over the components
  have hall : ∀ᵐ z ∂volume.restrict (Ω : Set 𝔼), ∀ ξ : 𝔼,
      w z ξ = ∑ i, partialDeriv u i z * ξ i := by
    filter_upwards [ae_all_iff.2 hwi] with z hz ξ
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin N) ℝ).sum_repr ξ]
    simp only [map_sum, map_smul, EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr,
      smul_eq_mul]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [hz i, mul_comm]
  have h1 := SobolevMultiIndex.weakDeriv_compDiffeo_single hH u hw j
  rw [basisFun_toBasis_apply] at h1
  filter_upwards [h1, hH.ae_comp_restrict hall] with y hy hy'
  rw [SobolevMultiIndex.compDiffeoL_apply] at *
  exact hy.trans (hy' _)

/-! ### The spaces $W^{m,p}(\Omega)$ -/

/-- **Section 9.1** of [brezis2011functional], definition of the spaces $W^{m,p}(\Omega)$. Let
$m \ge 1$ be an integer and $1 \le p \le \infty$. The space $W^{m,p}(\Omega)$ consists of the
functions $u \in L^p(\Omega)$ all of whose weak derivatives $D^\alpha u$ of order
$|\alpha| \le m$ lie in $L^p(\Omega)$. Equivalently, defined by induction, $W^{m,p}(\Omega) =
\{u \in W^{m-1,p}(\Omega) : \partial u / \partial x_i \in W^{m-1,p}(\Omega) \text{ for } i = 1,
\dots, N\}$.

The type is the backbone type `SobolevEuclidean N m p Ω`, and is defined for every $m \ge 0$.
The multi-index definition is `Brezis.Chapter09.sobolevSpaceHigher_iff`, and the inductive one
is `Brezis.Chapter09.sobolevSpaceHigher_iff_inductive`.

**Generalization.** The type includes $m=0$ and $m=1$, and is available for all exponents.
 The source introduces these higher-order spaces for $m \ge 2$ and $1 \le p \le \infty$. -/
noncomputable abbrev sobolevSpaceHigher (N m : ℕ) (p : ℝ≥0∞)
    (Ω : Opens (EuclideanSpace ℝ (Fin N))) : Type :=
  SobolevEuclidean N m p Ω

omit [Fact (1 ≤ p)] in
/-- The space $W^{1,p}(\Omega)$ is the case $m = 1$ of $W^{m,p}(\Omega)$: the two types are equal.

**Generalization.** Order one is included in the higher-order family in Lean. -/
theorem sobolevSpaceHigher_one : sobolevSpaceHigher N 1 p Ω = sobolevSpace N p Ω :=
  rfl

omit [Fact (1 ≤ p)] in
/-- A function is, almost everywhere on $\Omega$, the function of an element of $W^{m,p}(\Omega)$ if
and only if it satisfies the backbone predicate `MemSobolevMultiIndex` for the standard basis,
the order $m$ and the exponent $p$. -/
theorem exists_fn_ae_eq_iff {m : ℕ} (u : 𝔼 → ℝ) :
    (∃ v : sobolevSpaceHigher N m p Ω, SobolevMultiIndex.fn v =ᵐ[volume.restrict (Ω : Set 𝔼)] u)
      ↔ MemSobolevMultiIndex 𝔟 u m p Ω volume :=
  ⟨fun ⟨v, hv⟩ ↦ (SobolevMultiIndex.memSobolevMultiIndex v).congr_ae hv,
    fun h ↦ h.exists_sobolevMultiIndex⟩

/-- **Section 9.1** of [brezis2011functional], the multi-index definition of $W^{m,p}(\Omega)$. Let
$1 \le p \le \infty$ and $m \ge 0$. A function $u : \mathbb{R}^N \to \mathbb{R}$ is, almost
everywhere on $\Omega$, the function of an element of $W^{m,p}(\Omega)$ if and only if
$u \in L^p(\Omega)$ and, for every multi-index $\alpha$ with $|\alpha| \le m$, there is
$g_\alpha \in L^p(\Omega)$ with
$$\int_\Omega u \, D^\alpha \varphi = (-1)^{|\alpha|} \int_\Omega g_\alpha \varphi \qquad
  \text{for every } \varphi \in C_c^\infty(\Omega).$$

Here $D^\alpha \varphi$ is the iterated derivative of $\varphi$ along the $|\alpha|$ directions
in which each $e_i$ is repeated $\alpha_i$ times (`multiIndexTuple`).

**Generalization.** The formula includes $m=0$ and $m=1$. -/
theorem sobolevSpaceHigher_iff {m : ℕ} (u : 𝔼 → ℝ) :
    (∃ v : sobolevSpaceHigher N m p Ω, SobolevMultiIndex.fn v =ᵐ[volume.restrict (Ω : Set 𝔼)] u)
      ↔ MemLp u p (volume.restrict Ω) ∧ ∀ α : MultiIndexLE (Fin N) m,
        ∃ g : 𝔼 → ℝ, MemLp g p (volume.restrict Ω) ∧ ∀ φ : 𝓓(Ω, ℝ),
          ∫ x in (Ω : Set 𝔼), u x * iteratedFDeriv ℝ (∑ i, α.1 i) φ x (multiIndexTuple 𝔟 α.1)
            = (-1) ^ (∑ i, α.1 i) * ∫ x in (Ω : Set 𝔼), g x * φ x := by
  have hp : (1 : ℝ≥0∞) ≤ p := Fact.out
  rw [exists_fn_ae_eq_iff]
  constructor
  · rintro ⟨hu, h⟩
    refine ⟨hu, fun α ↦ ?_⟩
    obtain ⟨g, hg, hgp⟩ := h α.1 α.2
    exact ⟨g, hgp, integral_mul_iteratedFDeriv_eq_of_hasWeakIteratedLineDerivOn hg⟩
  · rintro ⟨hu, h⟩
    refine ⟨hu, fun α hα ↦ ?_⟩
    obtain ⟨g, hgp, hg⟩ := h ⟨α, hα⟩
    exact ⟨g, hasWeakIteratedLineDerivOn_of_forall (hu.locallyIntegrableOn hp)
      (hgp.locallyIntegrableOn hp) hg, hgp⟩

omit [Fact (1 ≤ p)] in
/-- **Section 9.1** of [brezis2011functional], the inductive definition of $W^{m,p}(\Omega)$. Let
$m \ge 0$. A function $u$ is in $W^{m+1,p}(\Omega)$ if and only if $u \in W^{m,p}(\Omega)$ and,
for every $i$, $u$ has a weak partial derivative $\partial u / \partial x_i$ on $\Omega$ that
lies in $W^{m,p}(\Omega)$.

This is the description $W^{m,p} = \{u \in W^{m-1,p} : \partial u / \partial x_i \in W^{m-1,p}
\text{ for all } i\}$ of the source, with $m + 1$ in place of $m$. Membership of a function in
$W^{m,p}(\Omega)$ means that it equals the function of an element almost everywhere on $\Omega$.
The statement holds for every exponent $p$.

**Generalization.** The characterization includes the step from $m=0$ and all exponents. -/
theorem sobolevSpaceHigher_iff_inductive {m : ℕ} (u : 𝔼 → ℝ) :
    (∃ v : sobolevSpaceHigher N (m + 1) p Ω,
        SobolevMultiIndex.fn v =ᵐ[volume.restrict (Ω : Set 𝔼)] u) ↔
      (∃ v : sobolevSpaceHigher N m p Ω,
        SobolevMultiIndex.fn v =ᵐ[volume.restrict (Ω : Set 𝔼)] u) ∧
      ∀ i, ∃ g : 𝔼 → ℝ, HasWeakIteratedLineDerivOn ![EuclideanSpace.single i 1] u g Ω volume ∧
        ∃ v' : sobolevSpaceHigher N m p Ω,
          SobolevMultiIndex.fn v' =ᵐ[volume.restrict (Ω : Set 𝔼)] g := by
  simp only [exists_fn_ae_eq_iff]
  rw [memSobolevMultiIndex_succ_iff]
  simp only [basisFun_toBasis_apply]

/-- **Section 9.1** of [brezis2011functional], the norm of $W^{m,p}(\Omega)$. For
$u \in W^{m,p}(\Omega)$,
$$\|u\|_{W^{m,p}} = \sum_{|\alpha| \le m} \|D^\alpha u\|_p.$$

It is equivalent to the norm of the type, by `Brezis.Chapter09.bookNormHigher_equiv`. -/
noncomputable def bookNormHigher {m : ℕ} (u : sobolevSpaceHigher N m p Ω) : ℝ :=
  ∑ α, ‖SobolevMultiIndex.weakDeriv u α‖

/-- The two norms of $W^{m,p}(\Omega)$ are equivalent: for $u \in W^{m,p}(\Omega)$,
$$\|u\| \le \|u\|_{W^{m,p}} \le K \|u\|,$$
where $\|u\|$ is the norm of the type and $K$ is the number of multi-indices $\alpha$ with
$|\alpha| \le m$.

**Reading.** The source equips the space with the sum norm. The inequality compares it to
 the library's product norm. -/
theorem bookNormHigher_equiv {m : ℕ} (u : sobolevSpaceHigher N m p Ω) :
    ‖u‖ ≤ bookNormHigher u ∧
      bookNormHigher u ≤ Fintype.card (MultiIndexLE (Fin N) m) * ‖u‖ := by
  refine ⟨SobolevMultiIndex.norm_le_sum_norm_weakDeriv u, ?_⟩
  calc bookNormHigher u ≤ ∑ _α : MultiIndexLE (Fin N) m, ‖u‖ :=
        Finset.sum_le_sum fun α _ ↦ SobolevMultiIndex.norm_weakDeriv_le u α
    _ = Fintype.card (MultiIndexLE (Fin N) m) * ‖u‖ := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **Section 9.1** of [brezis2011functional]: "the space $W^{m,p}(\Omega)$ equipped with the norm
$\sum_{|\alpha| \le m} \|D^\alpha u\|_p$ is a Banach space". Let $1 \le p \le \infty$ and
$m \ge 0$. The space $W^{m,p}(\Omega)$ is complete, and for every $u \in W^{m,p}(\Omega)$
$$\|u\| \le \|u\|_{W^{m,p}} \le K \|u\|,$$
where $\|u\|$ is the norm of the type and $K$ is the number of multi-indices $\alpha$ with
$|\alpha| \le m$.

**Reading.** Completeness is stated using the equivalent ambient product norm, with an
 explicit comparison to the source norm. The result also includes orders zero and one. -/
theorem sobolevSpaceHigher_banach {m : ℕ} :
    CompleteSpace (sobolevSpaceHigher N m p Ω) ∧
      ∀ u : sobolevSpaceHigher N m p Ω, ‖u‖ ≤ bookNormHigher u ∧
        bookNormHigher u ≤ Fintype.card (MultiIndexLE (Fin N) m) * ‖u‖ :=
  ⟨inferInstance, bookNormHigher_equiv⟩

/-- **Section 9.1** of [brezis2011functional]: "the space $H^m(\Omega) = W^{m,2}(\Omega)$ equipped
with the scalar product $(u, v)_{H^m} = \sum_{|\alpha| \le m} (D^\alpha u, D^\alpha v)_{L^2}$ is
a Hilbert space". Let $m \ge 0$. The inner product of $W^{m,2}(\Omega)$ is
$$(u, v)_{H^m} = \sum_{|\alpha| \le m} \int_\Omega D^\alpha u \, D^\alpha v,$$
and $W^{m,2}(\Omega)$ is complete.

**Generalization.** The same formula includes orders zero and one. -/
theorem hSpaceHigher {m : ℕ} :
    (∀ u v : sobolevSpaceHigher N m 2 Ω, inner ℝ u v = ∑ α, ∫ x in (Ω : Set 𝔼),
      SobolevMultiIndex.weakDeriv u α x * SobolevMultiIndex.weakDeriv v α x) ∧
    CompleteSpace (sobolevSpaceHigher N m 2 Ω) := by
  refine ⟨fun u v ↦ ?_, inferInstance⟩
  rw [SobolevMultiIndex.inner_eq, integral_finsetSum _ fun α _ ↦ L2.integrable_inner (𝕜 := ℝ)
    (SobolevMultiIndex.weakDeriv u α) (SobolevMultiIndex.weakDeriv v α)]
  simp only [Real.inner_apply]

end Brezis.Chapter09
