/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.Deriv.Abs
import Numlib.Analysis.Sobolev.Mollification
import Numlib.Analysis.Sobolev.MultiIndex
import Numlib.Analysis.Sobolev.Triangulation

/-!
# Atkinson and Han, Section 7.1: Weak derivatives

This module formalizes Section 7.1 of [han2009theoretical]. The section extends the classical
derivative to the weak derivative on an open set $\Omega \subseteq \mathbb{R}^d$, by turning the
integration by parts formula (7.1.1) into a definition. A locally integrable function $w$ is the
weak $\alpha$-th derivative of a locally integrable function $v$ if
$$\int_\Omega v \, \partial^\alpha \varphi \, dx = (-1)^{|\alpha|} \int_\Omega w \, \varphi \, dx
  \qquad \text{for all } \varphi \in C_0^\infty(\Omega)$$
(Definition 7.1.3). The weak derivative is unique up to a null set (Lemma 7.1.4), it extends the
classical derivative (Lemma 7.1.5), and it is linear (Proposition 7.1.10). It satisfies the product
rule (Proposition 7.1.11) and the chain rule (Proposition 7.1.12). The examples compute weak
derivatives in dimension one: $|x|$ has the weak derivative $\operatorname{sgn} x$ (Example 7.1.6),
a jump has no weak derivative (Example 7.1.7), and a continuous piecewise $C^1$ function has its
piecewise derivative as weak derivative (Example 7.1.8). Example 7.1.9 treats piecewise smooth
functions on a triangulated plane domain.

The proofs specialize `Numlib.Analysis.Sobolev.MultiIndex`, `Numlib.Analysis.Sobolev.Mollification`
and `Numlib.Analysis.Sobolev.Triangulation`.

## Main definitions

* Definition 7.1.1, `AtkinsonHan.Chapter07.definition_7_1_1`: the space $L^p_{\mathrm{loc}}(\Omega)$
  of locally $p$-integrable functions.
* Definition 7.1.3, `AtkinsonHan.Chapter07.definition_7_1_3`: the weak derivatives of order $n$, for
  all multi-indices of length $n$ at once.
* Definition 7.1.3, `AtkinsonHan.Chapter07.definition_7_1_3_multiIndex`: the weak $\alpha$-th
  derivative, for one multi-index $\alpha$.

## Main results

* Lemma 7.1.2, `AtkinsonHan.Chapter07.lemma_7_1_2`: if $v \in L^1_{\mathrm{loc}}(\Omega)$ and
  $\int_\Omega v \varphi = 0$ for every test function $\varphi$, then $v = 0$ almost everywhere on
  $\Omega$.
* Definition 7.1.3, `AtkinsonHan.Chapter07.definition_7_1_3_multiIndex_of_definition_7_1_3`: the
  weak derivatives of order $n$ give the weak $\alpha$-th derivative for each $\alpha$ with
  $|\alpha| = n$.
* Lemma 7.1.4, `AtkinsonHan.Chapter07.lemma_7_1_4`: a weak derivative is unique up to a null set.
* Lemma 7.1.5, `AtkinsonHan.Chapter07.lemma_7_1_5`: for $v \in C^m(\Omega)$ and $n \le m$, the
  classical derivative of order $n$ is the weak one.
* Example 7.1.6, `AtkinsonHan.Chapter07.example_7_1_6`: on an interval that contains $0$, $|x|$ has
  the weak derivative $\operatorname{sgn} x$.
* Example 7.1.7, `AtkinsonHan.Chapter07.example_7_1_7`: the step function $\operatorname{sgn} x$ has
  no weak derivative on $(-1, 1)$.
* Example 7.1.8, `AtkinsonHan.Chapter07.example_7_1_8`: a continuous piecewise $C^1$ function has
  its piecewise classical derivative as weak derivative.
* Example 7.1.8, `AtkinsonHan.Chapter07.example_7_1_8_second_order`: if a continuous piecewise $C^2$
  function has a second-order weak derivative, its one-sided derivatives agree at the interior
  nodes.
* Example 7.1.9, `AtkinsonHan.Chapter07.example_7_1_9`: a $C^k$ function that is $C^{k+1}$ on each
  triangle of a triangulation has the piecewise derivatives of order $k + 1$ as weak derivatives.
* Proposition 7.1.10, `AtkinsonHan.Chapter07.proposition_7_1_10`: weak differentiation is linear.
* Proposition 7.1.11, `AtkinsonHan.Chapter07.proposition_7_1_11_contDiff`: the product rule
  $\partial^\alpha(ug) = (\partial^\alpha u) g + u \, \partial^\alpha g$ for $|\alpha| = 1$ and a
  smooth factor $g$.
* Proposition 7.1.11, `AtkinsonHan.Chapter07.proposition_7_1_11`: the product rule for
  $|\alpha| = 1$, $u, \partial^\alpha u \in L^p_{\mathrm{loc}}(\Omega)$ and $v, \partial^\alpha v
  \in L^q_{\mathrm{loc}}(\Omega)$ with conjugate exponents.
* Proposition 7.1.12, `AtkinsonHan.Chapter07.proposition_7_1_12`: the chain rule $\partial^\alpha (f
  \circ v) = (f' \circ v) \, \partial^\alpha v$ for $|\alpha| = 1$.

## Proof outline

The one-dimensional examples are stated on $\mathbb{R}^1$ and proved on $\mathbb{R}$, through the
volume-preserving linear isometry `AtkinsonHan.Chapter07.toE1`. By
`AtkinsonHan.Chapter07.transport`, Definition 7.1.3 in dimension one becomes one identity between
integrals on the line, which is an integration by parts with finitely many exceptional points. The
second half of Example 7.1.8 reads a second-order weak derivative as a first-order weak derivative
of the first-order one (`AtkinsonHan.Chapter07.secondOrder_bridge`) and uses the jump obstruction of
Example 7.1.7 in a general form. The general product rule and the chain rule mollify, apply the
smooth case on a relatively compact neighbourhood of the support of the test function, and pass to
the limit. Example 7.1.9 uses the fundamental theorem of calculus on almost every line, not Green's
formula.

## Implementation notes

* The open set $\Omega$ is `Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))`, the measure is
  `volume`, and test functions are Mathlib's bundled `𝓓(Ω, ℝ)`. The backbone predicates
  `HasWeakIteratedFDerivOn` and `HasWeakIteratedLineDerivOn` work over any finite-dimensional real
  normed space, and they include the local integrability of the function and of its weak derivative.
* A multi-index $\alpha$ with $|\alpha| = n$ is represented by a tuple $y$ of $n$ directions, so
  that $\partial^\alpha \varphi(x)$ is `iteratedFDeriv ℝ n φ x y`. Definition 7.1.3 is formalized
  twice. `AtkinsonHan.Chapter07.definition_7_1_3` takes one object for all $\alpha$ of length $n$,
  with values in the continuous $n$-linear maps. `AtkinsonHan.Chapter07.definition_7_1_3_multiIndex`
  takes one $\alpha$ at a time, read as the tuple in which $e_i$ is repeated $\alpha_i$ times.
  Section 7.2 uses the second form, because the norm of Definition 7.2.2 sums over the $\alpha$
  separately.
* The one-dimensional examples live on `AtkinsonHan.Chapter07.E1`, the space $\mathbb{R}^1$.

## Deviations from the source

* **Definition 7.1.1** (scope). The locally integrable predicate allows all extended
  nonnegative exponents. The source specifies $1 \le p < \infty$.
* **Definition 7.1.3, Lemmas 7.1.4–7.1.5 and Proposition 7.1.10** (scope). The first
  formulation uses a multilinear weak derivative of a given order. The multi-index
  predicate gives the scalar derivative in the source. The predicates allow an empty
  open set.
* **Proposition 7.1.11** (scope). There is a separate multiplication rule for a smooth
  factor, stated without the conjugate-exponent hypotheses.
* **Proposition 7.1.12** (generalization). The source assumes $v \in W^{1,p}(\Omega)$ and concludes
  for every first-order derivative. The library assumes $v, \partial^\alpha v \in L^p(\Omega)$ for
  one $\alpha$ with $|\alpha| = 1$ and concludes for that $\alpha$. See
  `AtkinsonHan.Chapter07.proposition_7_1_12`.
* **Example 7.1.9** (generalization). The source assumes $v \in C^k(\overline\Omega)$; the library
  assumes $v \in C^k(\Omega)$. See `AtkinsonHan.Chapter07.example_7_1_9`.
* **Example 7.1.9** (reading). The subdomains $\Omega_n$ are the triangles of a triangulation, and
  $v|_{\Omega_n} \in C^{k+1}(\overline\Omega_n)$ means that $v$ agrees on the open triangle with a
  $C^{k+1}$ function on the plane. See `AtkinsonHan.Chapter07.example_7_1_9`.
-/

open MeasureTheory Module TopologicalSpace Set intervalIntegral

open scoped ContDiff Distributions ENNReal Interval

namespace AtkinsonHan.Chapter07

variable {d n m : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin d))}
  {u v : EuclideanSpace ℝ (Fin d) → ℝ}

/-- **Definition 7.1.1** of [han2009theoretical]. Let $\Omega \subseteq \mathbb{R}^d$ be open and
$p \in [1, \infty)$. A function $v : \Omega \to \mathbb{R}$ is **locally $p$-integrable**,
$v \in L^p_{\mathrm{loc}}(\Omega)$, if every point of $\Omega$ has a neighbourhood in $\Omega$
on which $v$ is $p$-integrable.

The source asks that $v \in L^p(\Omega')$ for an open $\Omega'$ with
$\overline{\Omega'} \subseteq \Omega$. On an open $\Omega$ this is the same condition, because
every point of $\Omega$ has a ball whose closure lies in $\Omega$. The definition is
`MeasureTheory.LocallyMemLpOn v p Ω volume`, and it accepts every `p : ℝ≥0∞`.

**Generalization.** Same local integrability for the stated exponent range and extends to all
extended nonnegative exponents.
-/
def definition_7_1_1 (p : ℝ≥0∞) (Ω : Opens (EuclideanSpace ℝ (Fin d)))
    (v : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  LocallyMemLpOn v p Ω volume

/-- **Lemma 7.1.2** of [han2009theoretical] (generalized variational lemma). Let
$\Omega \subseteq \mathbb{R}^d$ be open and let $v \in L^1_{\mathrm{loc}}(\Omega)$. If
$\int_\Omega v \varphi \, dx = 0$ for every $\varphi \in C_0^\infty(\Omega)$, then $v = 0$
almost everywhere on $\Omega$.

The source quotes this result from the literature without proof. The proof is Mathlib's
`IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`. -/
theorem lemma_7_1_2 (hv : LocallyIntegrableOn v Ω volume)
    (h : ∀ φ : 𝓓(Ω, ℝ), ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin d))), v x * φ x = 0) :
    ∀ᵐ x, x ∈ (Ω : Set (EuclideanSpace ℝ (Fin d))) → v x = 0 := by
  refine Ω.isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero hv fun g hg h'g hgs ↦ ?_
  have e : ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin d))), v x * g x = ∫ x, g x • v x :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
      rw [show g x = 0 from image_eq_zero_of_notMem_tsupport fun hh ↦ hx (hgs hh),
        mul_zero]).trans (by simp [smul_eq_mul, mul_comm])
  exact e ▸ h ⟨g, hg, h'g, hgs⟩

/-- **Definition 7.1.3** of [han2009theoretical], with (7.1.2), for all multi-indices of a given
length. Let $\Omega \subseteq \mathbb{R}^d$ be open and $n \in \mathbb{N}$. A function $w$ on
$\Omega$ with values in the continuous $n$-linear maps on $\mathbb{R}^d$ is the **weak
derivative of order $n$** of $v$ if $v$ and $w$ are locally integrable on $\Omega$ and
$$\int_\Omega \partial^n \varphi(x)(y) \, v(x) \, dx = (-1)^n \int_\Omega \varphi(x) \, w(x)(y)
  \, dx$$
for every $\varphi \in C_0^\infty(\Omega)$ and every tuple $y$ of $n$ directions in
$\mathbb{R}^d$.

A tuple $y$ of directions names a multi-index $\alpha$ with $|\alpha| = n$, and $w(x)(y)$ is
then the weak $\partial^\alpha v(x)$. The definition is
`HasWeakIteratedFDerivOn n v w Ω volume`.

**Reading.** Bundles all weak derivatives of fixed order as a multilinear map rather than one
coordinate derivative.
-/
def definition_7_1_3 (n : ℕ) (v : EuclideanSpace ℝ (Fin d) → ℝ)
    (w : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) [×n]→L[ℝ] ℝ)
    (Ω : Opens (EuclideanSpace ℝ (Fin d))) : Prop :=
  HasWeakIteratedFDerivOn n v w Ω volume

/-- The standard basis $e_1, \dots, e_d$ of $\mathbb{R}^d$. The multi-index derivatives
$\partial^\alpha = \partial_1^{\alpha_1} \cdots \partial_d^{\alpha_d}$ of this chapter are taken
in this basis. -/
noncomputable abbrev stdBasis (d : ℕ) : Basis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)) :=
  (EuclideanSpace.basisFun (Fin d) ℝ).toBasis

/-- **Definition 7.1.3** of [han2009theoretical], with (7.1.2), for one multi-index. Let
$\Omega \subseteq \mathbb{R}^d$ be open and let $\alpha \in \mathbb{N}^d$. A function $w$ is the
**weak $\alpha$-th derivative** of $v$ if $v$ and $w$ are locally integrable on $\Omega$ and
$$\int_\Omega v \, \partial^\alpha \varphi \, dx = (-1)^{|\alpha|} \int_\Omega w \, \varphi \,
  dx \qquad \text{for every } \varphi \in C_0^\infty(\Omega).$$

The multi-index $\alpha$ is read as the tuple of $|\alpha| = \alpha_1 + \dots + \alpha_d$
directions in which $e_i$ is repeated $\alpha_i$ times, with the indices in increasing order, so
that $\partial^\alpha \varphi = \partial_1^{\alpha_1} \cdots \partial_d^{\alpha_d} \varphi$. The
definition is `HasWeakIteratedLineDerivOn` along `multiIndexTuple
(AtkinsonHan.Chapter07.stdBasis d) α`. `AtkinsonHan.Chapter07.definition_7_1_3` is the same
definition for all multi-indices of a given length at once. -/
def definition_7_1_3_multiIndex (α : Fin d → ℕ) (v w : EuclideanSpace ℝ (Fin d) → ℝ)
    (Ω : Opens (EuclideanSpace ℝ (Fin d))) : Prop :=
  HasWeakIteratedLineDerivOn (multiIndexTuple (stdBasis d) α) v w Ω volume

/-- Let $\alpha \in \mathbb{N}^d$. If $w$ is the weak derivative of order $|\alpha|$ of $v$ on
$\Omega$ in the sense of `AtkinsonHan.Chapter07.definition_7_1_3`, then
$x \mapsto w(x)(y_\alpha)$ is the weak $\alpha$-th derivative of $v$ on $\Omega$, where
$y_\alpha$ is the tuple of directions that names $\alpha$. So the reading of Definition 7.1.3
for all multi-indices at once implies the reading for one multi-index. -/
theorem definition_7_1_3_multiIndex_of_definition_7_1_3 (α : Fin d → ℕ)
    {w : EuclideanSpace ℝ (Fin d) →
      EuclideanSpace ℝ (Fin d) [×(∑ i, α i)]→L[ℝ] ℝ}
    (h : definition_7_1_3 (∑ i, α i) v w Ω) :
    definition_7_1_3_multiIndex α v (fun x ↦ w x (multiIndexTuple (stdBasis d) α)) Ω :=
  h.lineDeriv _

/-- **Lemma 7.1.4** of [han2009theoretical]. If $w_1$ and $w_2$ are both weak derivatives of order
$n$ of $v$ on $\Omega$, then $w_1 = w_2$ almost everywhere on $\Omega$. So a weak derivative, if
it exists, is unique up to a set of measure zero.

**Reading.** Almost-everywhere uniqueness is formulated for the full multilinear derivative.
-/
theorem lemma_7_1_4 {w₁ w₂ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) [×n]→L[ℝ] ℝ}
    (h₁ : definition_7_1_3 n v w₁ Ω) (h₂ : definition_7_1_3 n v w₂ Ω) :
    ∀ᵐ x, x ∈ (Ω : Set (EuclideanSpace ℝ (Fin d))) → w₁ x = w₂ x :=
  h₁.ae_eq h₂

/-- **Lemma 7.1.5** of [han2009theoretical]. Let $\Omega \subseteq \mathbb{R}^d$ be open,
$v \in C^m(\Omega)$ and $n \le m$. Then the classical derivative $\partial^n v$ of order $n$ is
the weak derivative of order $n$ of $v$ on $\Omega$. So for each $\alpha$ with $|\alpha| \le m$,
the classical $\partial^\alpha v$ is the weak $\alpha$-th derivative, and the weak derivative
extends the classical one.

The classical derivative is `iteratedFDeriv ℝ n v`, and $v \in C^m(\Omega)$ is
`ContDiffOn ℝ m v Ω`.

**Reading.** Uses the entire iterated Fréchet derivative in the weak identity.
-/
theorem lemma_7_1_5 (hv : ContDiffOn ℝ m v Ω) (hnm : n ≤ m) :
    definition_7_1_3 n v (iteratedFDeriv ℝ n v) Ω :=
  hv.hasWeakIteratedFDerivOn (by exact_mod_cast hnm)

/-- **Proposition 7.1.10** of [han2009theoretical]. Let $w_1$ and $w_2$ be weak derivatives of order
$n$ of $u$ and $v$ on $\Omega$, and let $c_1, c_2 \in \mathbb{R}$. Then $c_1 w_1 + c_2 w_2$ is
the weak derivative of order $n$ of $c_1 u + c_2 v$. So weak differentiation is linear:
$\partial^\alpha(c_1 u + c_2 v) = c_1 \partial^\alpha u + c_2 \partial^\alpha v$.

**Reading.** Linearity is formulated for the full multilinear weak derivative.
-/
theorem proposition_7_1_10 {w₁ w₂ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) [×n]→L[ℝ] ℝ}
    (h₁ : definition_7_1_3 n u w₁ Ω) (h₂ : definition_7_1_3 n v w₂ Ω) (c₁ c₂ : ℝ) :
    definition_7_1_3 n (c₁ • u + c₂ • v) (c₁ • w₁ + c₂ • w₂) Ω :=
  h₁.const_smul_add_const_smul h₂ c₁ c₂

/-- **Proposition 7.1.11** of [han2009theoretical] (product rule), for a smooth factor. Let
$\alpha \in \mathbb{N}^d$ with $|\alpha| = 1$, so that $\partial^\alpha$ is a first-order
partial derivative $\partial_i$. If $w$ is the weak $\alpha$-th derivative of $u$ on $\Omega$
and $g \in C^\infty(\mathbb{R}^d)$, then the weak $\alpha$-th derivative of $ug$ on $\Omega$ is
$$\partial^\alpha(ug) = w \, g + u \, \partial^\alpha g,$$
where $\partial^\alpha g$ is the classical derivative of $g$.

This is a special case of `AtkinsonHan.Chapter07.proposition_7_1_11`, which allows two locally
integrable factors. The smooth case is elementary, because $g \varphi$ is again a test function
when $\varphi$ is. The identity is then the integration by parts $\int (\partial^\alpha \varphi)
g u = \int \partial^\alpha(g \varphi) u - \int \varphi (\partial^\alpha g) u$.

**Reading.** Separate smooth multiplier rule without conjugate-exponent hypotheses.
-/
theorem proposition_7_1_11_contDiff {α : Fin d → ℕ} (hα : ∑ i, α i = 1)
    {w : EuclideanSpace ℝ (Fin d) → ℝ} (h : definition_7_1_3_multiIndex α u w Ω)
    {g : EuclideanSpace ℝ (Fin d) → ℝ} (hg : ContDiff ℝ ∞ g) :
    definition_7_1_3_multiIndex α (fun x ↦ u x * g x)
      (fun x ↦ w x * g x
        + u x * iteratedFDeriv ℝ (∑ i, α i) g x (multiIndexTuple (stdBasis d) α)) Ω :=
  HasWeakIteratedLineDerivOn.mul_contDiff h hα hg

/-- **Proposition 7.1.11** of [han2009theoretical] (product rule). Let $p, q \in (1, \infty)$ with
$1/p + 1/q = 1$, and let $\alpha \in \mathbb{N}^d$ with $|\alpha| = 1$, so that
$\partial^\alpha$ is a first-order partial derivative $\partial_i$. Let $u$ and $v$ have the
weak $\alpha$-th derivatives $\partial^\alpha u$ and $\partial^\alpha v$ on $\Omega$, with $u,
\partial^\alpha u \in L^p_{\mathrm{loc}}(\Omega)$ and $v, \partial^\alpha v \in
L^q_{\mathrm{loc}}(\Omega)$. Then the weak $\alpha$-th derivative of $uv$ on $\Omega$ is
$$\partial^\alpha(uv) = (\partial^\alpha u) \, v + u \, \partial^\alpha v.$$

The source states this result without proof. The proof mollifies $u$, applies the smooth case
`AtkinsonHan.Chapter07.proposition_7_1_11_contDiff` on a relatively compact open neighbourhood
of the support of the test function, and passes to the limit with Hölder's inequality. It
specializes `HasWeakIteratedLineDerivOn.mul`. The hypothesis $q > 1$ is the source's and is
kept, but it follows from $p < \infty$ and $1/p + 1/q = 1$. -/
theorem proposition_7_1_11 {α : Fin d → ℕ} (hα : ∑ i, α i = 1) {p q : ℝ≥0∞}
    (hp : 1 < p) (hp' : p < ⊤) (_hq : 1 < q) (hq' : q < ⊤) (hpq : 1 / p + 1 / q = 1)
    {wu wv : EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : definition_7_1_1 p Ω u) (hwu : definition_7_1_1 p Ω wu)
    (hv : definition_7_1_1 q Ω v) (hwv : definition_7_1_1 q Ω wv)
    (hdu : definition_7_1_3_multiIndex α u wu Ω) (hdv : definition_7_1_3_multiIndex α v wv Ω) :
    definition_7_1_3_multiIndex α (fun x ↦ u x * v x) (fun x ↦ wu x * v x + u x * wv x) Ω :=
  have : ENNReal.HolderConjugate p q :=
    ENNReal.holderConjugate_iff.2 (by simpa only [one_div] using hpq)
  hdu.mul hα hdv hp.le hp'.ne hq'.ne hu hwu hv hwv

/-- **Proposition 7.1.12** of [han2009theoretical] (chain rule). Let $f \in C^1(\mathbb{R})$ with
$|f'| \le M$ on $\mathbb{R}$, let $\Omega \subseteq \mathbb{R}^d$ be open and bounded, let
$p \in (1, \infty)$, and let $\alpha \in \mathbb{N}^d$ with $|\alpha| = 1$, so that
$\partial^\alpha$ is a first-order partial derivative $\partial_i$. If $v \in L^p(\Omega)$ has
the weak $\alpha$-th derivative $\partial^\alpha v \in L^p(\Omega)$, then $(f' \circ v) \,
\partial^\alpha v \in L^p(\Omega)$ and it is the weak $\alpha$-th derivative of $f \circ v$:
$$\partial^\alpha(f \circ v) = (f' \circ v) \, \partial^\alpha v.$$

**Generalization.** The source assumes $v \in W^{1,p}(\Omega)$, that is, every first-order weak
derivative of $v$ lies in $L^p(\Omega)$, and concludes for every $i$. Here one $\alpha$ is
enough, and the statement for all $\alpha$ with $|\alpha| = 1$ gives the reading of the source.

The source states this result without proof. The boundedness of $\Omega$ is the source's
hypothesis and is kept, but the proof does not use it. The proof mollifies $v$ on a relatively
compact open neighbourhood of the support of the test function, applies the classical chain
rule, and passes to the limit along an almost everywhere convergent subsequence by dominated
convergence. It specializes `HasWeakIteratedLineDerivOn.contDiff_comp`. -/
theorem proposition_7_1_12 {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) {M : ℝ}
    (hM : ∀ t, |deriv f t| ≤ M)
    (_hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin d))))
    {p : ℝ≥0∞} (hp : 1 < p) (hp' : p < ⊤) {α : Fin d → ℕ} (hα : ∑ i, α i = 1)
    {w : EuclideanSpace ℝ (Fin d) → ℝ}
    (hv : MemLp v p (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin d)))))
    (hw : MemLp w p (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin d)))))
    (hd : definition_7_1_3_multiIndex α v w Ω) :
    MemLp (fun x ↦ deriv f (v x) * w x) p
        (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin d)))) ∧
      definition_7_1_3_multiIndex α (fun x ↦ f (v x)) (fun x ↦ deriv f (v x) * w x) Ω := by
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  have hdom : MemLp (fun x ↦ M * |w x|) p
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin d)))) := hw.abs.const_mul M
  refine ⟨MemLp.of_le hdom
    ((hf.continuous_deriv le_rfl).comp_aestronglyMeasurable hv.aestronglyMeasurable |>.mul
      hw.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun z ↦ ?_), ?_⟩
  · rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (mul_nonneg hM0 (abs_nonneg (w z)))]
    exact mul_le_mul_of_nonneg_right (hM _) (abs_nonneg _)
  · exact hd.contDiff_comp hα hf hM hp.le hp'.ne
      (fun x _ ↦ ⟨(Ω : Set (EuclideanSpace ℝ (Fin d))), self_mem_nhdsWithin, hv⟩)
      (fun x _ ↦ ⟨(Ω : Set (EuclideanSpace ℝ (Fin d))), self_mem_nhdsWithin, hw⟩)

/-!
### The line $\mathbb{R}^1$

Examples 7.1.6, 7.1.7 and 7.1.8 are computations in dimension $d = 1$. They are stated on
`AtkinsonHan.Chapter07.E1`, the space $\mathbb{R}^1$, and proved on $\mathbb{R}$ through the linear
isometry `AtkinsonHan.Chapter07.toE1`.
-/

section OneDimensional

/-- The Euclidean space $\mathbb{R}^1$, the case $d = 1$ of the ambient space of Section 7.1 of
[han2009theoretical]. The one-dimensional Examples 7.1.6, 7.1.7 and 7.1.8 are stated on it. -/
abbrev E1 : Type := EuclideanSpace ℝ (Fin 1)

variable {Ω₁ : Opens E1}

/-- The linear isometry $\mathbb{R} \to \mathbb{R}^1$ that sends $t$ to the point with coordinate
$t$. It identifies the line with $\mathbb{R}^1$ in the one-dimensional examples of Section 7.1
of [han2009theoretical].

An isometry of finite-dimensional real inner product spaces preserves the volume, so an integral
over a subset of $\mathbb{R}^1$ is an integral over its preimage in $\mathbb{R}$
(`AtkinsonHan.Chapter07.setIntegral_toE1`). -/
noncomputable def toE1 : ℝ ≃ₗᵢ[ℝ] E1 where
  toLinearEquiv :=
    (LinearEquiv.funUnique (Fin 1) ℝ ℝ).symm.trans (WithLp.linearEquiv 2 ℝ (Fin 1 → ℝ)).symm
  norm_map' t := by
    simp [EuclideanSpace.norm_eq, LinearEquiv.funUnique, Real.sqrt_sq_eq_abs]

/-- The coordinate of the point `AtkinsonHan.Chapter07.toE1 t` of $\mathbb{R}^1$ is $t$. -/
@[simp] theorem toE1_apply (t : ℝ) : (toE1 t) 0 = t := rfl

/-- The inverse of `AtkinsonHan.Chapter07.toE1` sends a point of $\mathbb{R}^1$ to its coordinate.
-/
@[simp] theorem toE1_symm_apply (x : E1) : toE1.symm x = x 0 := rfl

/-- The image of $1$ in $\mathbb{R}^1$ is the single vector $e_1$ of the standard basis. -/
theorem toE1_one : toE1 1 = stdBasis 1 0 := by
  ext i; fin_cases i; simp [stdBasis]

/-- In dimension one, the tuple of directions that names the multi-index $\alpha = (k)$ is the
constant tuple of length $k$ with value $e_1$. So $\partial^\alpha$ is the $k$-th derivative in
the single coordinate direction. -/
theorem multiIndexTuple_dimOne (k : ℕ) :
    multiIndexTuple (stdBasis 1) ![k] = fun _ ↦ toE1 1 := by
  have hl : multiIndexDirections (⇑(stdBasis 1)) ![k] = List.replicate k (stdBasis 1 0) := by
    simp [multiIndexDirections]
  funext j
  simp only [multiIndexTuple]
  rw [List.get_of_eq hl]
  simp [toE1_one]

/-- For $g : \mathbb{R}^1 \to \mathbb{R}$ and $s \subseteq \mathbb{R}^1$, the integral of $g$ over
$s$ equals the integral of $t \mapsto g(t)$ over the preimage of $s$ in $\mathbb{R}$. -/
theorem setIntegral_toE1 (g : E1 → ℝ) (s : Set E1) :
    ∫ t in toE1 ⁻¹' s, g (toE1 t) = ∫ x in s, g x :=
  toE1.measurePreserving.setIntegral_preimage_emb toE1.toHomeomorph.measurableEmbedding g s

/-- A point of $\mathbb{R}^1$ with coordinate $0$ is the origin. -/
theorem eq_zero_of_apply_zero {x : E1} (h : x 0 = 0) : x = 0 := by
  ext i; fin_cases i; simpa using h

/-- Almost every point of $\mathbb{R}^1$ has a nonzero coordinate, because the origin is a null set.
-/
theorem ae_apply_ne_zero : ∀ᵐ x : E1, x 0 ≠ 0 := by
  have h : {x : E1 | ¬ (x 0 ≠ 0)} = {0} := by
    ext x
    simp only [ne_eq, not_not, mem_ofPred_eq, mem_singleton_iff]
    exact ⟨eq_zero_of_apply_zero, fun hx ↦ by rw [hx]; rfl⟩
  rw [ae_iff, h]
  simp

/-- For $c \in \mathbb{R}$, almost every $t \in \mathbb{R}$ satisfies $t \neq c$. -/
theorem ae_ne_real (c : ℝ) : ∀ᵐ t : ℝ, t ≠ c := by
  rw [ae_iff]; simp

/-- A bounded, almost everywhere strongly measurable function is locally integrable for a locally
finite measure. -/
private theorem locallyIntegrable_of_bound {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    {μ : Measure X} [IsLocallyFiniteMeasure μ] {w : X → ℝ} {C : ℝ}
    (hm : AEStronglyMeasurable w μ) (hb : ∀ᵐ x ∂μ, ‖w x‖ ≤ C) :
    LocallyIntegrable w μ :=
  (locallyIntegrable_const C).mono hm (by
    filter_upwards [hb] with x hx using hx.trans (le_abs_self C))

/-- A bounded, almost everywhere strongly measurable function on $\mathbb{R}$ is integrable on every
interval. -/
private theorem intervalIntegrable_of_bound {f : ℝ → ℝ} {C : ℝ}
    (hm : AEStronglyMeasurable f volume) (hb : ∀ᵐ t : ℝ, ‖f t‖ ≤ C) (a b : ℝ) :
    IntervalIntegrable f volume a b :=
  (intervalIntegrable_const (c := C)).mono_fun' hm.restrict (ae_restrict_of_ae hb)

/-! ### Pulling a test function on $\Omega \subseteq \mathbb{R}^1$ back to $\mathbb{R}$ -/

/-- A test function on $\Omega \subseteq \mathbb{R}^1$, read as a function on $\mathbb{R}$, is
smooth. -/
theorem contDiff_comp_toE1 (φ : 𝓓(Ω₁, ℝ)) : ContDiff ℝ ∞ ((φ : E1 → ℝ) ∘ toE1) :=
  φ.contDiff.comp toE1.toContinuousLinearEquiv.contDiff

/-- A test function on $\Omega \subseteq \mathbb{R}^1$, read as a function on $\mathbb{R}$, has
compact support. -/
theorem hasCompactSupport_comp_toE1 (φ : 𝓓(Ω₁, ℝ)) :
    HasCompactSupport ((φ : E1 → ℝ) ∘ toE1) :=
  φ.hasCompactSupport.comp_homeomorph toE1.toHomeomorph

/-- A test function on $\Omega \subseteq \mathbb{R}^1$, read as a function on $\mathbb{R}$, has its
support in the preimage of $\Omega$. -/
theorem tsupport_comp_toE1 (φ : 𝓓(Ω₁, ℝ)) :
    tsupport ((φ : E1 → ℝ) ∘ toE1) ⊆ toE1 ⁻¹' (Ω₁ : Set E1) := by
  rw [show ((φ : E1 → ℝ) ∘ toE1) = (φ : E1 → ℝ) ∘ toE1.toHomeomorph from rfl,
    tsupport_comp_eq_preimage]
  exact preimage_mono φ.tsupport_subset

/-- For a test function $\varphi$ on $\Omega \subseteq \mathbb{R}^1$, the derivative on $\mathbb{R}$
of $t \mapsto \varphi(t)$ is the partial derivative of $\varphi$ in the single coordinate
direction. -/
theorem deriv_comp_toE1 (φ : 𝓓(Ω₁, ℝ)) (t : ℝ) :
    deriv ((φ : E1 → ℝ) ∘ toE1) t = fderiv ℝ (φ : E1 → ℝ) (toE1 t) (toE1 1) :=
  (((φ.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt.comp t
    toE1.toContinuousLinearEquiv.hasFDerivAt).hasDerivAt).deriv

/-- For a test function $\varphi$ on $\Omega \subseteq \mathbb{R}^1$ and
$g : \mathbb{R}^1 \to \mathbb{R}$, the integral $\int_\Omega \varphi \, g$ equals the integral
of $t \mapsto \varphi(t) g(t)$ over the preimage of $\Omega$ in $\mathbb{R}$. -/
theorem integral_testFunction_mul (φ : 𝓓(Ω₁, ℝ)) (g : E1 → ℝ) :
    ∫ x in (Ω₁ : Set E1), φ x • g x ∂volume
      = ∫ t in toE1 ⁻¹' (Ω₁ : Set E1), ((φ : E1 → ℝ) ∘ toE1) t * g (toE1 t) :=
  (setIntegral_toE1 (fun x ↦ φ x • g x) _).symm

/-- For a test function $\varphi$ on $\Omega \subseteq \mathbb{R}^1$ and
$g : \mathbb{R}^1 \to \mathbb{R}$, the integral $\int_\Omega \varphi' \, g$ equals the integral
of $t \mapsto \varphi'(t) g(t)$ over the preimage of $\Omega$ in $\mathbb{R}$. -/
theorem integral_iteratedFDeriv_mul (φ : 𝓓(Ω₁, ℝ)) (g : E1 → ℝ) :
    ∫ x in (Ω₁ : Set E1), iteratedFDeriv ℝ 1 (φ : E1 → ℝ) x (fun _ ↦ toE1 1) • g x ∂volume
      = ∫ t in toE1 ⁻¹' (Ω₁ : Set E1), deriv ((φ : E1 → ℝ) ∘ toE1) t * g (toE1 t) := by
  simp only [iteratedFDeriv_one_apply, deriv_comp_toE1]
  exact (setIntegral_toE1 (fun x ↦ fderiv ℝ (φ : E1 → ℝ) x (toE1 1) • g x) _).symm

/-- Definition 7.1.3 in dimension one, read on the line. Let $\Omega \subseteq \mathbb{R}^1$ be open
and let $v, w$ be locally integrable on $\Omega$. Write
$\Omega_{\mathbb{R}} \subseteq \mathbb{R}$ for the preimage of $\Omega$. If
$$\int_{\Omega_{\mathbb{R}}} \psi'(t) \, v(t) \, dt = -\int_{\Omega_{\mathbb{R}}} \psi(t) \,
  w(t) \, dt$$
for every smooth compactly supported $\psi : \mathbb{R} \to \mathbb{R}$ with support in
$\Omega_{\mathbb{R}}$, then $w$ is the first-order weak derivative of $v$ on $\Omega$.

The examples of Section 7.1 of [han2009theoretical] in dimension one use this result to reduce
Definition 7.1.3 to an identity between integrals on $\mathbb{R}$. -/
theorem transport {v w : E1 → ℝ}
    (hv : LocallyIntegrableOn v Ω₁ volume) (hw : LocallyIntegrableOn w Ω₁ volume)
    (key : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ toE1 ⁻¹' (Ω₁ : Set E1) →
        (∫ t in toE1 ⁻¹' (Ω₁ : Set E1), deriv ψ t * v (toE1 t))
          = -∫ t in toE1 ⁻¹' (Ω₁ : Set E1), ψ t * w (toE1 t)) :
    definition_7_1_3_multiIndex ![1] v w Ω₁ := by
  rw [definition_7_1_3_multiIndex, multiIndexTuple_dimOne]
  refine ⟨hv, hw, fun φ ↦ ?_⟩
  change ∫ x in (Ω₁ : Set E1), iteratedFDeriv ℝ 1 (φ : E1 → ℝ) x (fun _ ↦ toE1 1) • v x ∂volume
      = (-1 : ℝ) ^ 1 • ∫ x in (Ω₁ : Set E1), φ x • w x ∂volume
  rw [integral_iteratedFDeriv_mul, integral_testFunction_mul,
    key _ (contDiff_comp_toE1 φ) (hasCompactSupport_comp_toE1 φ) (tsupport_comp_toE1 φ)]
  simp

/-- The converse of `AtkinsonHan.Chapter07.transport`. Let $\Omega \subseteq \mathbb{R}^1$ be open
and let $w$ be the first-order weak derivative of $v$ on $\Omega$. Write
$\Omega_{\mathbb{R}} \subseteq \mathbb{R}$ for the preimage of $\Omega$. Then for every smooth
compactly supported $\psi : \mathbb{R} \to \mathbb{R}$ with support in $\Omega_{\mathbb{R}}$,
$$\int_{\Omega_{\mathbb{R}}} \psi'(t) \, v(t) \, dt = -\int_{\Omega_{\mathbb{R}}} \psi(t) \,
  w(t) \, dt.$$
-/
theorem transport_symm {v w : E1 → ℝ} (h : definition_7_1_3_multiIndex ![1] v w Ω₁)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcs : HasCompactSupport ψ)
    (hsupp : tsupport ψ ⊆ toE1 ⁻¹' (Ω₁ : Set E1)) :
    (∫ t in toE1 ⁻¹' (Ω₁ : Set E1), deriv ψ t * v (toE1 t))
      = -∫ t in toE1 ⁻¹' (Ω₁ : Set E1), ψ t * w (toE1 t) := by
  rw [definition_7_1_3_multiIndex, multiIndexTuple_dimOne] at h
  have hφ : ContDiff ℝ ∞ (ψ ∘ toE1.symm) :=
    hψ.comp toE1.symm.toContinuousLinearEquiv.contDiff
  have hφcs : HasCompactSupport (ψ ∘ toE1.symm) := hcs.comp_homeomorph toE1.symm.toHomeomorph
  have hφts : tsupport (ψ ∘ toE1.symm) ⊆ (Ω₁ : Set E1) := by
    rw [show (ψ ∘ toE1.symm) = ψ ∘ toE1.symm.toHomeomorph from rfl, tsupport_comp_eq_preimage]
    intro y hy
    have h2 : toE1.symm y ∈ tsupport ψ := hy
    have h3 := hsupp h2
    rwa [mem_preimage, LinearIsometryEquiv.apply_symm_apply] at h3
  set φ : 𝓓(Ω₁, ℝ) := ⟨ψ ∘ toE1.symm, hφ, hφcs, hφts⟩ with hφdef
  have hcoe : ((φ : E1 → ℝ) ∘ toE1) = ψ := by funext t; simp [hφdef]
  have key : ∫ x in (Ω₁ : Set E1),
        iteratedFDeriv ℝ 1 (φ : E1 → ℝ) x (fun _ ↦ toE1 1) • v x ∂volume
      = (-1 : ℝ) ^ 1 • ∫ x in (Ω₁ : Set E1), φ x • w x ∂volume := h.integral_smul_eq φ
  rw [integral_iteratedFDeriv_mul, integral_testFunction_mul, hcoe] at key
  simpa using key

/-- A second-order weak derivative of $v$ is a first-order weak derivative of its first-order weak
derivative. Let $\Omega \subseteq \mathbb{R}^1$ be open. If $w$ is the first-order weak
derivative of $v$ on $\Omega$ and $z$ is the weak derivative of $v$ for the multi-index $(2)$,
then $z$ is the first-order weak derivative of $w$ on $\Omega$. This result supports the second
half of Example 7.1.8 of [han2009theoretical].

For a test function $\varphi$, the derivative $\partial^2 \varphi$ is
$\partial(\partial \varphi)$, and $\partial \varphi$ is again a test function. So the
second-order identity for $\varphi$ is the first-order identity for $\partial \varphi$. -/
theorem secondOrder_bridge {v w z : E1 → ℝ}
    (hw : definition_7_1_3_multiIndex ![1] v w Ω₁)
    (hz : definition_7_1_3_multiIndex ![2] v z Ω₁) :
    definition_7_1_3_multiIndex ![1] w z Ω₁ := by
  rw [definition_7_1_3_multiIndex, multiIndexTuple_dimOne] at hw ⊢
  rw [definition_7_1_3_multiIndex, multiIndexTuple_dimOne] at hz
  refine ⟨hw.locallyIntegrableOn_weakDeriv, hz.locallyIntegrableOn_weakDeriv, fun φ ↦ ?_⟩
  have e1 : ∀ x : E1, iteratedFDeriv ℝ 1 ((φ.fderivApply (toE1 1) : E1 → ℝ)) x
      (fun _ ↦ toE1 1) = iteratedFDeriv ℝ 2 (φ : E1 → ℝ) x (fun _ ↦ toE1 1) := by
    intro x
    rw [φ.contDiff.iteratedFDeriv_succ_apply_left' 1 (fun _ ↦ toE1 1) x]
    simp [Fin.tail]
  have h1 : ∫ x in (Ω₁ : Set E1), iteratedFDeriv ℝ 1 ((φ.fderivApply (toE1 1) : E1 → ℝ)) x
        (fun _ ↦ toE1 1) • v x ∂volume
      = (-1 : ℝ) ^ 1 • ∫ x in (Ω₁ : Set E1), (φ.fderivApply (toE1 1)) x • w x ∂volume :=
    hw.integral_smul_eq _
  have h2 : ∫ x in (Ω₁ : Set E1), iteratedFDeriv ℝ 2 (φ : E1 → ℝ) x (fun _ ↦ toE1 1) • v x ∂volume
      = (-1 : ℝ) ^ 2 • ∫ x in (Ω₁ : Set E1), φ x • z x ∂volume := hz.integral_smul_eq φ
  simp only [e1] at h1
  change ∫ x in (Ω₁ : Set E1), iteratedFDeriv ℝ 1 (φ : E1 → ℝ) x (fun _ ↦ toE1 1) • w x ∂volume
      = (-1 : ℝ) ^ 1 • ∫ x in (Ω₁ : Set E1), φ x • z x ∂volume
  have h3 := h1.symm.trans h2
  simp only [TestFunction.fderivApply_coe, iteratedFDeriv_one_apply, pow_one, pow_two,
    neg_mul, neg_neg, one_mul, smul_eq_mul] at h3 ⊢
  linarith [h3]

/-- For every point $x$ of an open set $\Omega \subseteq \mathbb{R}^1$ there is a test function
$\varphi$ on $\Omega$ with $\varphi(x) = 1$. -/
theorem exists_testFunction_eq_one {x : E1} (hx : x ∈ (Ω₁ : Set E1)) :
    ∃ φ : 𝓓(Ω₁, ℝ), φ x = 1 := by
  obtain ⟨f, h1, h2, h3, -, h5⟩ :=
    exists_contDiff_tsupport_subset (n := ⊤) (Ω₁.isOpen.mem_nhds hx)
  exact ⟨⟨f, h3, h2, h1⟩, h5⟩

/-! ### One-dimensional integration by parts -/

/-- The fundamental theorem of calculus with finitely many exceptional points: if $a \le b$, $g$ is
continuous on $[a, b]$, $g$ has derivative $g'$ at every point of $(a, b)$ outside a finite set,
and $g'$ is integrable on $[a, b]$, then $\int_a^b g' = g(b) - g(a)$. -/
private theorem ftcFinite (T : Finset ℝ) : ∀ {a b : ℝ}, a ≤ b → ∀ {g g' : ℝ → ℝ},
    ContinuousOn g (Icc a b) → (∀ t ∈ Ioo a b, t ∉ T → HasDerivAt g (g' t) t) →
    IntervalIntegrable g' volume a b → ∫ t in a..b, g' t = g b - g a := by
  induction T using Finset.strongInduction with
  | _ T ih =>
    intro a b hab g g' hcont hderiv hint
    by_cases hT : ∃ c ∈ T, c ∈ Ioo a b
    · obtain ⟨c, hcT, hc⟩ := hT
      have hac : a ≤ c := hc.1.le
      have hcb : c ≤ b := hc.2.le
      have hsub : T.erase c ⊂ T := Finset.erase_ssubset hcT
      have hint1 : IntervalIntegrable g' volume a c :=
        hint.mono_set (by rw [uIcc_of_le hab, uIcc_of_le hac]; exact Icc_subset_Icc le_rfl hcb)
      have hint2 : IntervalIntegrable g' volume c b :=
        hint.mono_set (by rw [uIcc_of_le hab, uIcc_of_le hcb]; exact Icc_subset_Icc hac le_rfl)
      have h1 : ∫ t in a..c, g' t = g c - g a := by
        refine ih _ hsub hac (hcont.mono (Icc_subset_Icc le_rfl hcb)) ?_ hint1
        intro t ht htT
        exact hderiv t ⟨ht.1, ht.2.trans hc.2⟩ fun h ↦ htT (Finset.mem_erase.2 ⟨ht.2.ne, h⟩)
      have h2 : ∫ t in c..b, g' t = g b - g c := by
        refine ih _ hsub hcb (hcont.mono (Icc_subset_Icc hac le_rfl)) ?_ hint2
        intro t ht htT
        exact hderiv t ⟨hc.1.trans ht.1, ht.2⟩ fun h ↦ htT (Finset.mem_erase.2 ⟨ht.1.ne', h⟩)
      rw [← integral_add_adjacent_intervals hint1 hint2, h1, h2]
      ring
    · exact integral_eq_sub_of_hasDerivAt_of_le hab hcont
        (fun t ht ↦ hderiv t ht fun h ↦ hT ⟨t, h, ht⟩) hint

/-- Integration by parts on $[c, d]$ with finitely many exceptional points: if $\psi \in C^1$, $v$
is continuous on $[c, d]$ with derivative $w$ on $(c, d)$ outside a finite set, and $w$ is
integrable on $[c, d]$, then $\int_c^d \psi' v + \int_c^d \psi w = \psi(d) v(d) - \psi(c) v(c)$. -/
private theorem integralByParts {c d : ℝ} (hcd : c ≤ d) (T : Finset ℝ) {v w ψ : ℝ → ℝ}
    (hv : ContinuousOn v (Icc c d)) (hψ : ContDiff ℝ 1 ψ)
    (hd : ∀ t ∈ Ioo c d, t ∉ T → HasDerivAt v (w t) t)
    (hw : IntervalIntegrable w volume c d) :
    (∫ t in c..d, deriv ψ t * v t) + ∫ t in c..d, ψ t * w t = ψ d * v d - ψ c * v c := by
  have hderivψ : ∀ t, HasDerivAt ψ (deriv ψ t) t := fun t ↦
    (hψ.differentiable (by norm_num) t).hasDerivAt
  have hcψ : Continuous (deriv ψ) := hψ.continuous_deriv le_rfl
  have h1 : IntervalIntegrable (fun t ↦ deriv ψ t * v t) volume c d :=
    ((hcψ.continuousOn.mul hv).intervalIntegrable_of_Icc hcd)
  have h2 : IntervalIntegrable (fun t ↦ ψ t * w t) volume c d :=
    hw.continuousOn_mul (hψ.continuous.continuousOn)
  rw [← integral_add h1 h2]
  exact ftcFinite T hcd ((hψ.continuous.continuousOn).mul hv)
    (fun t ht htT ↦ (hderivψ t).mul (hd t ht htT)) (h1.add h2)

/-- If $p \le q$, $(p, q) \subseteq (a, b)$ and $f$ vanishes outside $(p, q)$, then
$\int_{(a, b)} f = \int_p^q f$. -/
private theorem setIntegral_Ioo_eq_intervalIntegral {a b p q : ℝ} (hpq : p ≤ q)
    (hsub : Ioo p q ⊆ Ioo a b) {f : ℝ → ℝ} (hf : ∀ t ∉ Ioo p q, f t = 0) :
    ∫ t in Ioo a b, f t = ∫ t in p..q, f t := by
  rw [intervalIntegral.integral_of_le hpq,
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun t ht ↦ hf t fun h ↦ ht (hsub h)),
    setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun t ht ↦ hf t fun h ↦ ht (Ioo_subset_Ioc_self h))]

section Piece

variable {p c : ℝ} {W W₁ Y₁ ψ : ℝ → ℝ}

/-- If $W = W_1$ on $(p, c)$ with $p < c$, then $\int_p^c g \, W = \int_p^c g \, W_1$ for every $g$.
-/
private theorem intervalIntegral_congr_piece (hpc : p < c) (heq : ∀ t ∈ Ioo p c, W t = W₁ t)
    {g : ℝ → ℝ} : ∫ t in p..c, g t * W t = ∫ t in p..c, g t * W₁ t := by
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [ae_ne_real c] with t ht htI
  rw [uIoc_of_le hpc.le] at htI
  rw [heq t ⟨htI.1, lt_of_le_of_ne htI.2 ht⟩]

/-- Integration by parts on one piece $[p, c]$ of a partition, for a function $W$ that agrees on
$(p, c)$ with a $C^1$ function $W_1$ whose derivative is $Y_1$. -/
private theorem integralByParts_piece (hpc : p < c) (hW₁ : ContinuousOn W₁ (Icc p c))
    (hY₁ : ContinuousOn Y₁ (Icc p c)) (hd : ∀ t ∈ Ioo p c, HasDerivAt W₁ (Y₁ t) t)
    (heq : ∀ t ∈ Ioo p c, W t = W₁ t) (hψ : ContDiff ℝ 1 ψ) :
    (∫ t in p..c, deriv ψ t * W t) + ∫ t in p..c, ψ t * Y₁ t = ψ c * W₁ c - ψ p * W₁ p := by
  rw [intervalIntegral_congr_piece hpc heq]
  exact integralByParts hpc.le ∅ hW₁ hψ (fun t ht _ ↦ hd t ht)
    (hY₁.intervalIntegrable_of_Icc hpc.le)

/-- On one piece $[p, c]$ of a partition, the integrand $\psi' W$ is integrable. -/
private theorem intervalIntegrable_piece (hpc : p < c) (hW₁ : ContinuousOn W₁ (Icc p c))
    (heq : ∀ t ∈ Ioo p c, W t = W₁ t) (hψ : ContDiff ℝ 1 ψ) :
    IntervalIntegrable (fun t ↦ deriv ψ t * W t) volume p c := by
  refine IntervalIntegrable.congr_uIoo (f := fun t ↦ deriv ψ t * W₁ t) ?_ fun t ht ↦ ?_
  · exact (((hψ.continuous_deriv le_rfl).continuousOn).mul hW₁).intervalIntegrable_of_Icc hpc.le
  · rw [uIoo_of_le hpc.le] at ht
    rw [heq t ht]

end Piece

/-- An open interval $(p, q)$ of $\mathbb{R}$, as an open subset of $\mathbb{R}^1$. -/
private def opensOfIoo (p q : ℝ) : Opens E1 :=
  ⟨{y : E1 | y 0 ∈ Ioo p q}, isOpen_Ioo.preimage toE1.symm.continuous⟩

@[simp]
private theorem preimage_opensOfIoo (p q : ℝ) :
    toE1 ⁻¹' (opensOfIoo p q : Set E1) = Ioo p q := by
  ext t; simp [opensOfIoo]

/-- A function on $\mathbb{R}$ that is integrable on the preimage of $\Omega \subseteq \mathbb{R}^1$
is locally integrable on $\Omega$, read on $\mathbb{R}^1$. -/
private theorem locallyIntegrableOn_comp {s : Set ℝ} (hpre : toE1 ⁻¹' (Ω₁ : Set E1) = s)
    {U : ℝ → ℝ} (hU : IntegrableOn U s volume) :
    LocallyIntegrableOn (fun y : E1 ↦ U (y 0)) Ω₁ volume := by
  refine IntegrableOn.locallyIntegrableOn ?_
  rw [← toE1.measurePreserving.integrableOn_comp_preimage
    toE1.toHomeomorph.measurableEmbedding, hpre]
  exact hU

/-- An almost everywhere statement on $\mathbb{R}^1$ holds almost everywhere on $\mathbb{R}$, read
through `AtkinsonHan.Chapter07.toE1`. -/
private theorem ae_comp_toE1 {P : E1 → Prop} (h : ∀ᵐ x : E1, P x) : ∀ᵐ t : ℝ, P (toE1 t) := by
  refine ae_of_ae_map toE1.continuous.measurable.aemeasurable ?_
  rwa [toE1.measurePreserving.map_eq]

/-! ### The jump function of Examples 7.1.6 and 7.1.7 -/

/-- The jump function $\operatorname{sgn}$ on $\mathbb{R}^1$: it is $1$ where the coordinate is
positive and $-1$ elsewhere. It is the weak derivative of $|x|$ in Example 7.1.6 and the
function of Example 7.1.7 of [han2009theoretical].

At the origin its value is $-1$. -/
noncomputable def sgnE1 (x : E1) : ℝ := if 0 < x 0 then 1 else -1

/-- The jump function $\operatorname{sgn}$ on $\mathbb{R}^1$ is measurable. -/
theorem measurable_sgnE1 : Measurable sgnE1 :=
  Measurable.ite (measurableSet_lt measurable_const toE1.symm.continuous.measurable)
    measurable_const measurable_const

/-- The jump function $\operatorname{sgn}$ on $\mathbb{R}^1$ has absolute value at most $1$. -/
theorem norm_sgnE1_le (x : E1) : ‖sgnE1 x‖ ≤ 1 := by
  rw [sgnE1]; split_ifs <;> simp

/-- A function on $\mathbb{R}^1$ that agrees with $\operatorname{sgn}$ at every point with nonzero
coordinate is locally integrable. Its value at the origin is arbitrary. -/
theorem locallyIntegrable_of_eq_sgnE1 {V : E1 → ℝ}
    (hV : ∀ x : E1, x 0 ≠ 0 → V x = sgnE1 x) : LocallyIntegrable V volume := by
  have hae : V =ᵐ[volume] sgnE1 := by
    filter_upwards [ae_apply_ne_zero] with x hx using hV x hx
  refine locallyIntegrable_of_bound (C := 1)
    (measurable_sgnE1.aestronglyMeasurable.congr hae.symm) ?_
  filter_upwards [hae] with x hx using hx ▸ norm_sgnE1_le x

/-- A function on $\mathbb{R}$ that agrees with $\operatorname{sgn}$ at every $t \neq 0$ is
integrable on every interval. -/
theorem intervalIntegrable_of_eq_sgnE1 {V : ℝ → ℝ}
    (hV : ∀ t : ℝ, t ≠ 0 → V t = sgnE1 (toE1 t)) (a b : ℝ) :
    IntervalIntegrable V volume a b := by
  have hae : V =ᵐ[volume] sgnE1 ∘ toE1 := by
    filter_upwards [ae_ne_real 0] with t ht using hV t ht
  refine intervalIntegrable_of_bound (C := 1)
    ((measurable_sgnE1.comp toE1.continuous.measurable).aestronglyMeasurable.congr hae.symm) ?_ a b
  filter_upwards [hae] with t ht using ht ▸ norm_sgnE1_le (toE1 t)

/-- Let $\psi \in C^1(\mathbb{R})$ with $\psi(-1) = \psi(1) = 0$, and let $V$ agree with
$\operatorname{sgn}$ at every $t \neq 0$. Then
$$\int_{(-1, 1)} \psi'(t) \, V(t) \, dt = -2 \psi(0).$$
This is the computation behind Example 7.1.7 of [han2009theoretical]. -/
theorem integral_deriv_mul_jump {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hm : ψ (-1) = 0) (hp : ψ 1 = 0) {V : ℝ → ℝ}
    (hV : ∀ t : ℝ, t ≠ 0 → V t = sgnE1 (toE1 t)) :
    ∫ t in Ioo (-1 : ℝ) 1, deriv ψ t * V t = -2 * ψ 0 := by
  have hcψ : Continuous (deriv ψ) := hψ.continuous_deriv le_rfl
  have hψd : ∀ x, DifferentiableAt ℝ ψ x := hψ.differentiable (by norm_num)
  have hprod : ∀ a b : ℝ, IntervalIntegrable (fun t ↦ deriv ψ t * V t) volume a b :=
    fun a b ↦ (intervalIntegrable_of_eq_sgnE1 hV a b).continuousOn_mul hcψ.continuousOn
  have hsub : ∀ a b : ℝ, ∫ t in a..b, deriv ψ t = ψ b - ψ a := fun a b ↦
    integral_deriv_eq_sub (fun x _ ↦ hψd x) (hcψ.intervalIntegrable _ _)
  have e1 : ∫ t in (-1 : ℝ)..0, deriv ψ t * V t = -(ψ 0 - ψ (-1)) := by
    rw [intervalIntegral.integral_congr_ae (g := fun t ↦ -deriv ψ t) ?_,
      intervalIntegral.integral_neg, hsub]
    filter_upwards [ae_ne_real 0] with t ht htI
    rw [uIoc_of_le (by norm_num)] at htI
    have h : sgnE1 (toE1 t) = -1 := by rw [sgnE1, toE1_apply]; simp [not_lt.2 htI.2]
    rw [hV t ht, h]
    ring
  have e2 : ∫ t in (0 : ℝ)..1, deriv ψ t * V t = ψ 1 - ψ 0 := by
    rw [intervalIntegral.integral_congr_ae (g := fun t ↦ deriv ψ t) ?_, hsub]
    filter_upwards with t htI
    rw [uIoc_of_le (by norm_num)] at htI
    have h : sgnE1 (toE1 t) = 1 := by rw [sgnE1, toE1_apply]; simp [htI.1]
    rw [hV t htI.1.ne', h]
    ring
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num),
    ← integral_add_adjacent_intervals (hprod (-1) 0) (hprod 0 1), e1, e2, hm, hp]
  ring

/-! ### Examples 7.1.6, 7.1.7 and 7.1.8 -/

/-- **Example 7.1.6** of [han2009theoretical]. Let $a < 0 < b$ and
$\Omega = (a, b) \subseteq \mathbb{R}^1$. The function $v(x) = |x|$, which has no classical
derivative at $0$, has the first-order weak derivative
$$w(x) = \begin{cases} 1, & x > 0, \\ -1, & x < 0. \end{cases}$$

The value of $w$ at $0$ is arbitrary: the hypothesis constrains $w$ only at points with nonzero
coordinate. -/
theorem example_7_1_6 {a b : ℝ} (ha : a < 0) (hb : 0 < b)
    (hΩ : (Ω₁ : Set E1) = {x : E1 | x 0 ∈ Ioo a b})
    {w : E1 → ℝ} (hw : ∀ x : E1, x 0 ≠ 0 → w x = if 0 < x 0 then 1 else -1) :
    definition_7_1_3_multiIndex ![1] (fun x ↦ |x 0|) w Ω₁ := by
  have hab : a ≤ b := (ha.trans hb).le
  have hpre : toE1 ⁻¹' (Ω₁ : Set E1) = Ioo a b := by rw [hΩ]; ext t; simp
  refine transport ((toE1.symm.continuous.abs).locallyIntegrable.locallyIntegrableOn _)
    ((locallyIntegrable_of_eq_sgnE1 hw).locallyIntegrableOn _) ?_
  intro ψ hψ _ hsupp
  rw [hpre] at hsupp ⊢
  have hψa : ψ a = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ (hsupp h).1.false
  have hψb : ψ b = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ (hsupp h).2.false
  have hd : ∀ t ∈ Ioo a b, t ∉ ({0} : Finset ℝ) → HasDerivAt (|·| : ℝ → ℝ) (w (toE1 t)) t := by
    intro t _ ht
    simp only [Finset.mem_singleton] at ht
    rw [hw (toE1 t) (by simpa using ht), toE1_apply]
    rcases lt_or_gt_of_ne ht with h | h
    · simpa [not_lt.2 h.le] using hasDerivAt_abs_neg h
    · simpa [h] using hasDerivAt_abs_pos h
  have hwint : IntervalIntegrable (fun t ↦ w (toE1 t)) volume a b :=
    intervalIntegrable_of_eq_sgnE1 (fun t ht ↦ hw (toE1 t) (by simpa using ht)) a b
  have key := integralByParts hab {0} (v := (|·| : ℝ → ℝ)) (w := fun t ↦ w (toE1 t)) (ψ := ψ)
    continuous_abs.continuousOn (hψ.of_le (by norm_num)) hd hwint
  rw [hψa, hψb] at key
  simp only [zero_mul, sub_self] at key
  rw [← integral_Ioc_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hab, ← intervalIntegral.integral_of_le hab]
  simp only [toE1_apply]
  linarith [key]

/-- **Example 7.1.7** of [han2009theoretical]. Let $\Omega = (-1, 1) \subseteq \mathbb{R}^1$, and
let $v = -1$ on $(-1, 0)$ and $v = 1$ on $(0, 1)$, with any value at $0$. Then $v$ has no
first-order weak derivative on $\Omega$. So a jump discontinuity destroys weak
differentiability.

Integration by parts on each half gives $\int_\Omega v \, \varphi' = -2 \varphi(0)$. So a weak
derivative $w$ would satisfy $\int_\Omega w \varphi = 2 \varphi(0)$ for every test function.
Lemma 7.1.2 on $\Omega \setminus \{0\}$ then forces $w = 0$ almost everywhere on $\Omega$, hence
$\varphi(0) = 0$ for every test function, which is false. -/
theorem example_7_1_7 (hΩ : (Ω₁ : Set E1) = {x : E1 | x 0 ∈ Ioo (-1) 1})
    {v : E1 → ℝ} (hv : ∀ x : E1, x 0 ≠ 0 → v x = if 0 < x 0 then 1 else -1) :
    ¬ ∃ w : E1 → ℝ, definition_7_1_3_multiIndex ![1] v w Ω₁ := by
  rintro ⟨w, hwd⟩
  rw [definition_7_1_3_multiIndex, multiIndexTuple_dimOne] at hwd
  have hpre : toE1 ⁻¹' (Ω₁ : Set E1) = Ioo (-1 : ℝ) 1 := by rw [hΩ]; ext t; simp
  have hzero : (0 : E1) ∈ (Ω₁ : Set E1) := by rw [hΩ]; norm_num
  -- the defining identity forces `∫_Ω φ w = 2 φ(0)`
  have step1 : ∀ φ : 𝓓(Ω₁, ℝ), ∫ x in (Ω₁ : Set E1), φ x • w x ∂volume = 2 * φ 0 := by
    intro φ
    have h : ∫ x in (Ω₁ : Set E1),
          iteratedFDeriv ℝ 1 (φ : E1 → ℝ) x (fun _ ↦ toE1 1) • v x ∂volume
        = (-1 : ℝ) ^ 1 • ∫ x in (Ω₁ : Set E1), φ x • w x ∂volume := hwd.integral_smul_eq φ
    rw [integral_iteratedFDeriv_mul, hpre] at h
    have hjump : ∫ t in Ioo (-1 : ℝ) 1, deriv ((φ : E1 → ℝ) ∘ toE1) t * v (toE1 t)
        = -2 * φ 0 := by
      refine integral_deriv_mul_jump ((contDiff_comp_toE1 φ).of_le (by norm_num)) ?_ ?_
        (fun t ht ↦ hv (toE1 t) (by simpa using ht))
      · exact image_eq_zero_of_notMem_tsupport fun hm ↦ by
          have := hpre ▸ tsupport_comp_toE1 φ hm; simp at this
      · exact image_eq_zero_of_notMem_tsupport fun hm ↦ by
          have := hpre ▸ tsupport_comp_toE1 φ hm; simp at this
    rw [hjump] at h
    simp only [pow_one, neg_one_smul] at h
    linarith [h]
  -- Lemma 7.1.2 on `Ω \ {0}` makes `w` vanish a.e. there, hence a.e. on `Ω`
  set Ω' : Opens E1 :=
    ⟨(Ω₁ : Set E1) \ ({0} : Set E1), Ω₁.isOpen.sdiff isClosed_singleton⟩ with hΩ'def
  have hsub : (Ω' : Set E1) ⊆ (Ω₁ : Set E1) := Set.sdiff_subset
  have hnull : (Ω' : Set E1) =ᵐ[volume] (Ω₁ : Set E1) :=
    sdiff_ae_eq_self.2 (measure_mono_null inter_subset_right (measure_singleton 0))
  have hzeroΩ' : ∀ᵐ x : E1, x ∈ (Ω' : Set E1) → w x = 0 := by
    refine lemma_7_1_2 (hwd.locallyIntegrableOn_weakDeriv.mono_set hsub) fun φ' ↦ ?_
    have hts : tsupport (φ' : E1 → ℝ) ⊆ (Ω₁ : Set E1) := φ'.tsupport_subset.trans hsub
    have h0 : (φ' : E1 → ℝ) 0 = 0 :=
      image_eq_zero_of_notMem_tsupport fun hm ↦ (φ'.tsupport_subset hm).2 rfl
    have hstep := step1 ⟨φ', φ'.contDiff, φ'.hasCompactSupport, hts⟩
    have hcoe : ((⟨φ', φ'.contDiff, φ'.hasCompactSupport, hts⟩ : 𝓓(Ω₁, ℝ)) : E1 → ℝ) = φ' := rfl
    rw [hcoe, h0, mul_zero] at hstep
    rw [setIntegral_congr_set hnull]
    simpa [mul_comm] using hstep
  have hzeroΩ : ∀ᵐ x : E1, x ∈ (Ω₁ : Set E1) → w x = 0 := by
    filter_upwards [hzeroΩ', ae_apply_ne_zero] with x h1 h2 hxΩ
    exact h1 ⟨hxΩ, fun h ↦ h2 (by rw [h]; rfl)⟩
  -- but then `2 φ(0) = 0` for every test function, and some test function has `φ(0) = 1`
  obtain ⟨φ, hφ⟩ := exists_testFunction_eq_one hzero
  have hint : ∫ x in (Ω₁ : Set E1), φ x • w x ∂volume = 0 := by
    refine integral_eq_zero_of_ae ?_
    rw [Filter.EventuallyEq, ae_restrict_iff' Ω₁.isOpen.measurableSet]
    filter_upwards [hzeroΩ] with x hx hxΩ
    simp [hx hxΩ]
  rw [step1 φ, hφ] at hint
  norm_num at hint

section Partition

variable {N : ℕ} {x : Fin (N + 1) → ℝ} {V W : ℝ → ℝ}

/-- Let $x_0 < x_1 < \dots < x_N$. A point of $(x_0, x_N)$ that is not a node $x_i$ lies in one of
the open subintervals $(x_i, x_{i+1})$. -/
theorem exists_mem_Ioo_of_strictMono (hx : StrictMono x) {t : ℝ}
    (ht : t ∈ Ioo (x 0) (x (Fin.last N))) (ht' : ∀ i, t ≠ x i) :
    ∃ i : Fin N, t ∈ Ioo (x i.castSucc) (x i.succ) := by
  classical
  have hne : (Finset.univ.filter (fun i : Fin (N + 1) ↦ x i < t)).Nonempty :=
    ⟨0, by simp [ht.1]⟩
  set j := (Finset.univ.filter (fun i : Fin (N + 1) ↦ x i < t)).max' hne with hjdef
  have hjlt : x j < t := by
    have := Finset.max'_mem _ hne
    simpa [← hjdef] using this
  have hjn : (j : ℕ) < N := by
    rcases Nat.lt_or_ge (j : ℕ) N with h | h
    · exact h
    · exact absurd hjlt (not_lt.2 (le_trans ht.2.le
        (hx.monotone (by simpa [Fin.le_def, Fin.last] using h))))
  refine ⟨⟨j, hjn⟩, ?_, ?_⟩
  · simpa [Fin.castSucc, Fin.castAdd, Fin.castLE] using hjlt
  · have hsucc : ((⟨j, hjn⟩ : Fin N).succ) ∉
        Finset.univ.filter (fun i : Fin (N + 1) ↦ x i < t) := by
      intro hmem
      have := Finset.le_max' _ _ hmem
      simp [Fin.le_def, Fin.succ, ← hjdef] at this
    have : ¬ (x ((⟨j, hjn⟩ : Fin N).succ) < t) := by simpa using hsucc
    exact lt_of_le_of_ne (not_lt.1 this) (ht' _)

/-- If $V$ is $C^1$ on $[c, d]$ and $t \in (c, d)$, then $V$ has the classical derivative $V'(t)$ at
$t$. -/
theorem hasDerivAt_of_contDiffOn_Icc {c d : ℝ} (h : ContDiffOn ℝ 1 V (Icc c d))
    {t : ℝ} (ht : t ∈ Ioo c d) : HasDerivAt V (deriv V t) t :=
  ((h.differentiableOn one_ne_zero t (mem_Icc_of_Ioo ht)).differentiableAt
    (Icc_mem_nhds ht.1 ht.2)).hasDerivAt

/-- Let $c < d$ and let $V$ be $C^1$ on $[c, d]$. A function $W$ with $W = V'$ on $(c, d)$ is
integrable on $[c, d]$. -/
theorem intervalIntegrable_of_eq_deriv {c d : ℝ} (hcd : c < d)
    (h : ContDiffOn ℝ 1 V (Icc c d)) (hW : ∀ t ∈ Ioo c d, W t = deriv V t) :
    IntervalIntegrable W volume c d := by
  refine IntervalIntegrable.congr_uIoo (f := derivWithin V (Icc c d)) ?_ fun t ht ↦ ?_
  · exact (h.continuousOn_derivWithin (uniqueDiffOn_Icc hcd) le_rfl).intervalIntegrable_of_Icc
      hcd.le
  · rw [uIoo_of_le hcd.le] at ht
    rw [derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2), hW t ht]

/-- **Example 7.1.8** of [han2009theoretical], first order. Let $a = x_0 < x_1 < \dots < x_N = b$ be
a partition, let $V \in C[a, b]$ be $C^1$ on each closed subinterval $[x_{i-1}, x_i]$, and let
$W = V'$ on each open subinterval, with arbitrary values at the nodes. Then, on
$\Omega = (a, b) \subseteq \mathbb{R}^1$, $W$ is the first-order weak derivative of $V$.

The nodes are a strictly increasing `x : Fin (N + 1) → ℝ`. The functions on $\mathbb{R}^1$ are
$y \mapsto V(y_0)$ and $y \mapsto W(y_0)$. -/
theorem example_7_1_8 (hx : StrictMono x)
    (hΩ : (Ω₁ : Set E1) = {y : E1 | y 0 ∈ Ioo (x 0) (x (Fin.last N))})
    (hV : ContinuousOn V (Icc (x 0) (x (Fin.last N))))
    (hpw : ∀ i : Fin N, ContDiffOn ℝ 1 V (Icc (x i.castSucc) (x i.succ)))
    (hW : ∀ i : Fin N, ∀ t ∈ Ioo (x i.castSucc) (x i.succ), W t = deriv V t) :
    definition_7_1_3_multiIndex ![1] (fun y ↦ V (y 0)) (fun y ↦ W (y 0)) Ω₁ := by
  classical
  have hab : x 0 ≤ x (Fin.last N) := hx.monotone (Fin.zero_le _)
  have hpre : toE1 ⁻¹' (Ω₁ : Set E1) = Ioo (x 0) (x (Fin.last N)) := by rw [hΩ]; ext t; simp
  -- interval integrability of `W`, piece by piece and then over the whole interval
  have hWi : ∀ i : Fin N, IntervalIntegrable W volume (x i.castSucc) (x i.succ) := fun i ↦
    intervalIntegrable_of_eq_deriv (hx (by simp [Fin.lt_def])) (hpw i) (hW i)
  have hWint : IntervalIntegrable W volume (x 0) (x (Fin.last N)) := by
    have step : ∀ k : ℕ, ∀ hk : k < N + 1, IntervalIntegrable W volume (x 0) (x ⟨k, hk⟩) := by
      intro k
      induction k with
      | zero => intro hk; simp [IntervalIntegrable, show (⟨0, hk⟩ : Fin (N + 1)) = 0 from rfl]
      | succ m ih =>
        intro hk
        refine (ih (by omega)).trans ?_
        have h := hWi ⟨m, by omega⟩
        convert h using 2 <;> simp [Fin.castSucc, Fin.castAdd, Fin.castLE, Fin.succ]
    have h := step N (by omega)
    convert h using 2
    simp [Fin.last]
  -- the classical derivative away from the nodes
  have hd : ∀ t ∈ Ioo (x 0) (x (Fin.last N)), t ∉ Finset.image x Finset.univ →
      HasDerivAt V (W t) t := by
    intro t ht htT
    obtain ⟨i, hi⟩ := exists_mem_Ioo_of_strictMono hx ht
      (fun i hi ↦ htT (Finset.mem_image.2 ⟨i, Finset.mem_univ i, hi.symm⟩))
    rw [hW i t hi]
    exact hasDerivAt_of_contDiffOn_Icc (hpw i) hi
  -- local integrability of `V` and `W` on `Ω`
  have hcomp : ∀ U : ℝ → ℝ, IntegrableOn U (Ioo (x 0) (x (Fin.last N))) volume →
      LocallyIntegrableOn (fun y : E1 ↦ U (y 0)) Ω₁ volume := by
    intro U hU
    refine IntegrableOn.locallyIntegrableOn ?_
    rw [← toE1.measurePreserving.integrableOn_comp_preimage
      toE1.toHomeomorph.measurableEmbedding, hpre]
    exact hU
  refine transport (hcomp V (hV.integrableOn_Icc.mono_set Ioo_subset_Icc_self))
    (hcomp W ((intervalIntegrable_iff_integrableOn_Ioo_of_le hab).1 hWint)) ?_
  intro ψ hψ _ hsupp
  rw [hpre] at hsupp ⊢
  have hψa : ψ (x 0) = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ (hsupp h).1.false
  have hψb : ψ (x (Fin.last N)) = 0 :=
    image_eq_zero_of_notMem_tsupport fun h ↦ (hsupp h).2.false
  have key := integralByParts hab (Finset.image x Finset.univ) (v := V) (w := W) (ψ := ψ)
    hV (hψ.of_le (by norm_num)) hd hWint
  rw [hψa, hψb] at key
  simp only [zero_mul, sub_self] at key
  rw [← integral_Ioc_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hab, ← intervalIntegral.integral_of_le hab]
  simp only [toE1_apply]
  linarith [key]

end Partition

/-!
### A jump destroys weak differentiability

The obstruction of Example 7.1.7, in the form that the second half of Example 7.1.8 needs. Let a
function be continuously differentiable on $(p, c)$ and on $(c, q)$, and let it have a weak
derivative on an interval that contains $(p, q)$. Then its one-sided limits at $c$ agree.
-/

section Jump

variable {a b p c q : ℝ} {W W₁ W₂ Y₁ Y₂ : ℝ → ℝ} {z : E1 → ℝ}

/-- An almost everywhere statement on $(p, c)$ transfers to the interval $(p, c]$, because the two
sets differ by the single point $c$. -/
private theorem ae_uIoc_of_ae_Ioo (hpc : p < c) {f g : ℝ → ℝ}
    (h : ∀ᵐ t : ℝ, t ∈ Ioo p c → f t = g t) : ∀ᵐ t : ℝ, t ∈ Ι p c → f t = g t := by
  filter_upwards [h, ae_ne_real c] with t ht htne htI
  rw [uIoc_of_le hpc.le] at htI
  exact ht ⟨htI.1, lt_of_le_of_ne htI.2 htne⟩

/-- An almost everywhere statement on $(p, c)$ gives an almost everywhere equality for the measure
restricted to $(p, c]$. -/
private theorem ae_restrict_of_ae_Ioo (hpc : p < c) {f g : ℝ → ℝ}
    (h : ∀ᵐ t : ℝ, t ∈ Ioo p c → f t = g t) : f =ᵐ[volume.restrict (Ι p c)] g :=
  (ae_restrict_iff' measurableSet_uIoc).2 (ae_uIoc_of_ae_Ioo hpc h)

/-- On an open piece $(p, c)$ on which $W$ agrees with a continuously differentiable function $W_1$
with derivative $Y_1$, every weak derivative of $W$ agrees almost everywhere with $Y_1$. -/
private theorem ae_eq_of_hasDerivAt_piece (hpc : p < c) (hsub : Ioo p c ⊆ Ioo a b)
    (hΩ : (Ω₁ : Set E1) = {y : E1 | y 0 ∈ Ioo a b})
    (hW₁ : ContinuousOn W₁ (Icc p c)) (hY₁ : ContinuousOn Y₁ (Icc p c))
    (hd : ∀ t ∈ Ioo p c, HasDerivAt W₁ (Y₁ t) t) (heq : ∀ t ∈ Ioo p c, W t = W₁ t)
    (hz : definition_7_1_3_multiIndex ![1] (fun y ↦ W (y 0)) z Ω₁) :
    ∀ᵐ t : ℝ, t ∈ Ioo p c → z (toE1 t) = Y₁ t := by
  have hle : opensOfIoo p c ≤ Ω₁ := fun y hy ↦ show y ∈ (Ω₁ : Set E1) by
    rw [hΩ]; exact hsub hy
  have hz' : definition_7_1_3_multiIndex ![1] (fun y ↦ W (y 0)) z (opensOfIoo p c) :=
    HasWeakIteratedLineDerivOn.mono hz hle
  have hY : definition_7_1_3_multiIndex ![1] (fun y ↦ W (y 0))
      (fun y ↦ Y₁ (y 0)) (opensOfIoo p c) := by
    refine transport hz'.locallyIntegrableOn
      (locallyIntegrableOn_comp (preimage_opensOfIoo p c)
        ((hY₁.integrableOn_Icc).mono_set Ioo_subset_Icc_self)) ?_
    intro ψ hψ _ hsupp
    rw [preimage_opensOfIoo] at hsupp ⊢
    simp only [toE1_apply]
    have hψp : ψ p = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ (hsupp h).1.false
    have hψc : ψ c = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ (hsupp h).2.false
    have hz1 : ∀ t ∉ Ioo p c, deriv ψ t * W t = 0 := fun t ht ↦ by
      rw [Function.notMem_support.1 fun h ↦ ht (hsupp (support_deriv_subset h)), zero_mul]
    have hz2 : ∀ t ∉ Ioo p c, ψ t * Y₁ t = 0 := fun t ht ↦ by
      rw [image_eq_zero_of_notMem_tsupport fun h ↦ ht (hsupp h), zero_mul]
    rw [setIntegral_Ioo_eq_intervalIntegral hpc.le subset_rfl hz1,
      setIntegral_Ioo_eq_intervalIntegral hpc.le subset_rfl hz2]
    have key := integralByParts_piece hpc hW₁ hY₁ hd heq (hψ.of_le (by norm_num))
    rw [hψp, hψc] at key
    simp only [zero_mul, sub_self] at key
    linarith [key]
  have hae := HasWeakIteratedLineDerivOn.ae_eq hz' hY
  filter_upwards [ae_comp_toE1 hae] with t ht htI
  exact ht htI

/-- A jump destroys weak differentiability: if $W$ agrees with a continuously differentiable $W_1$
on $(p, c)$ and with a continuously differentiable $W_2$ on $(c, q)$, and $W$ has a weak
derivative on $\Omega = (a, b) \supseteq (p, q)$, then $W_1(c) = W_2(c)$. -/
private theorem eq_of_hasWeakDeriv_of_jump (hpc : p < c) (hcq : c < q)
    (hsub : Ioo p q ⊆ Ioo a b) (hΩ : (Ω₁ : Set E1) = {y : E1 | y 0 ∈ Ioo a b})
    (hW₁ : ContinuousOn W₁ (Icc p c)) (hY₁ : ContinuousOn Y₁ (Icc p c))
    (hd₁ : ∀ t ∈ Ioo p c, HasDerivAt W₁ (Y₁ t) t) (heq₁ : ∀ t ∈ Ioo p c, W t = W₁ t)
    (hW₂ : ContinuousOn W₂ (Icc c q)) (hY₂ : ContinuousOn Y₂ (Icc c q))
    (hd₂ : ∀ t ∈ Ioo c q, HasDerivAt W₂ (Y₂ t) t) (heq₂ : ∀ t ∈ Ioo c q, W t = W₂ t)
    (hz : definition_7_1_3_multiIndex ![1] (fun y ↦ W (y 0)) z Ω₁) :
    W₁ c = W₂ c := by
  have hpq : p ≤ q := (hpc.trans hcq).le
  have hsubl : Ioo p c ⊆ Ioo a b := (Ioo_subset_Ioo le_rfl hcq.le).trans hsub
  have hsubr : Ioo c q ⊆ Ioo a b := (Ioo_subset_Ioo hpc.le le_rfl).trans hsub
  have hA := ae_eq_of_hasDerivAt_piece hpc hsubl hΩ hW₁ hY₁ hd₁ heq₁ hz
  have hB := ae_eq_of_hasDerivAt_piece hcq hsubr hΩ hW₂ hY₂ hd₂ heq₂ hz
  -- a bump function equal to `1` at `c` and supported in `(p, q)`
  obtain ⟨ψ, hts, hcs, hψ, -, hψc⟩ := exists_contDiff_tsupport_subset (n := ⊤)
    (isOpen_Ioo.mem_nhds (show c ∈ Ioo p q from ⟨hpc, hcq⟩))
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by norm_num)
  have hψp : ψ p = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ (hts h).1.false
  have hψq : ψ q = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ (hts h).2.false
  have hpre : toE1 ⁻¹' (Ω₁ : Set E1) = Ioo a b := by rw [hΩ]; ext t; simp
  -- the defining identity, localized to `[p, q]` and split at `c`
  have hM := transport_symm hz hψ hcs (by rw [hpre]; exact hts.trans hsub)
  rw [hpre] at hM
  simp only [toE1_apply] at hM
  have hz1 : ∀ t ∉ Ioo p q, deriv ψ t * W t = 0 := fun t ht ↦ by
    rw [Function.notMem_support.1 fun h ↦ ht (hts (support_deriv_subset h)), zero_mul]
  have hz2 : ∀ t ∉ Ioo p q, ψ t * z (toE1 t) = 0 := fun t ht ↦ by
    rw [image_eq_zero_of_notMem_tsupport fun h ↦ ht (hts h), zero_mul]
  rw [setIntegral_Ioo_eq_intervalIntegral hpq hsub hz1,
    setIntegral_Ioo_eq_intervalIntegral hpq hsub hz2] at hM
  -- integrability of `ψ z` on each piece, through `hA` and `hB`
  have hA' : ∀ᵐ t : ℝ, t ∈ Ioo p c → ψ t * Y₁ t = ψ t * z (toE1 t) := by
    filter_upwards [hA] with t ht htI; rw [ht htI]
  have hB' : ∀ᵐ t : ℝ, t ∈ Ioo c q → ψ t * Y₂ t = ψ t * z (toE1 t) := by
    filter_upwards [hB] with t ht htI; rw [ht htI]
  have hiz₁ : IntervalIntegrable (fun t ↦ ψ t * z (toE1 t)) volume p c :=
    IntervalIntegrable.congr_ae
      ((hY₁.intervalIntegrable_of_Icc hpc.le).continuousOn_mul hψ.continuous.continuousOn)
      (ae_restrict_of_ae_Ioo hpc hA')
  have hiz₂ : IntervalIntegrable (fun t ↦ ψ t * z (toE1 t)) volume c q :=
    IntervalIntegrable.congr_ae
      ((hY₂.intervalIntegrable_of_Icc hcq.le).continuousOn_mul hψ.continuous.continuousOn)
      (ae_restrict_of_ae_Ioo hcq hB')
  rw [← integral_add_adjacent_intervals
      (intervalIntegrable_piece hpc hW₁ heq₁ hψ1) (intervalIntegrable_piece hcq hW₂ heq₂ hψ1),
    ← integral_add_adjacent_intervals hiz₁ hiz₂] at hM
  -- replace `z` by the classical derivative on each piece
  have e₁ : ∫ t in p..c, ψ t * z (toE1 t) = ∫ t in p..c, ψ t * Y₁ t :=
    (intervalIntegral.integral_congr_ae (ae_uIoc_of_ae_Ioo hpc hA')).symm
  have e₂ : ∫ t in c..q, ψ t * z (toE1 t) = ∫ t in c..q, ψ t * Y₂ t :=
    (intervalIntegral.integral_congr_ae (ae_uIoc_of_ae_Ioo hcq hB')).symm
  rw [e₁, e₂] at hM
  -- integration by parts on each piece
  have k₁ := integralByParts_piece hpc hW₁ hY₁ hd₁ heq₁ hψ1
  have k₂ := integralByParts_piece hcq hW₂ hY₂ hd₂ heq₂ hψ1
  rw [hψp, hψc] at k₁
  rw [hψq, hψc] at k₂
  simp only [zero_mul, sub_zero, one_mul, zero_sub] at k₁ k₂
  linarith [hM, k₁, k₂]

end Jump

section SecondOrder

variable {N : ℕ} {x : Fin (N + 1) → ℝ} {V W : ℝ → ℝ}

/-- **Example 7.1.8** of [han2009theoretical], second order. Let $a = x_0 < x_1 < \dots < x_N = b$
be a partition, let $V \in C[a, b]$ be $C^2$ on each closed subinterval, and let $W = V'$ on
each open subinterval. If $V$ has a second-order weak derivative on
$\Omega = (a, b) \subseteq \mathbb{R}^1$, then the one-sided derivatives of $V$ agree at every
interior node:
$$V'(x_i^-) = V'(x_i^+).$$

The one-sided derivatives are `derivWithin` of $V$ on the two closed subintervals that meet at
the node. An interior node is the common endpoint of two consecutive subintervals `i` and `j`,
with `i.succ = j.castSucc`. -/
theorem example_7_1_8_second_order (hx : StrictMono x)
    (hΩ : (Ω₁ : Set E1) = {y : E1 | y 0 ∈ Ioo (x 0) (x (Fin.last N))})
    (hV : ContinuousOn V (Icc (x 0) (x (Fin.last N))))
    (hpw : ∀ i : Fin N, ContDiffOn ℝ 2 V (Icc (x i.castSucc) (x i.succ)))
    (hW : ∀ i : Fin N, ∀ t ∈ Ioo (x i.castSucc) (x i.succ), W t = deriv V t)
    {z : E1 → ℝ} (hz : definition_7_1_3_multiIndex ![2] (fun y ↦ V (y 0)) z Ω₁)
    (i j : Fin N) (hij : i.succ = j.castSucc) :
    derivWithin V (Icc (x i.castSucc) (x i.succ)) (x i.succ)
      = derivWithin V (Icc (x j.castSucc) (x j.succ)) (x j.castSucc) := by
  -- the first-order weak derivative, and the bridge from the second-order one to it
  have hw : definition_7_1_3_multiIndex ![1] (fun y ↦ V (y 0)) (fun y ↦ W (y 0)) Ω₁ :=
    example_7_1_8 hx hΩ hV (fun k ↦ (hpw k).of_le (by norm_num)) hW
  have hzw : definition_7_1_3_multiIndex ![1] (fun y ↦ W (y 0)) z Ω₁ := secondOrder_bridge hw hz
  have hpc : x i.castSucc < x i.succ := hx (by simp [Fin.lt_def])
  have hcq : x j.castSucc < x j.succ := hx (by simp [Fin.lt_def])
  have hsub : Ioo (x i.castSucc) (x j.succ) ⊆ Ioo (x 0) (x (Fin.last N)) :=
    Ioo_subset_Ioo (hx.monotone (Fin.zero_le _)) (hx.monotone (Fin.le_last _))
  -- on each closed piece `W` is the `C^1` function `derivWithin V`
  have piece : ∀ k : Fin N,
      ContinuousOn (derivWithin V (Icc (x k.castSucc) (x k.succ)))
        (Icc (x k.castSucc) (x k.succ)) ∧
      ContinuousOn (derivWithin (derivWithin V (Icc (x k.castSucc) (x k.succ)))
        (Icc (x k.castSucc) (x k.succ))) (Icc (x k.castSucc) (x k.succ)) ∧
      (∀ t ∈ Ioo (x k.castSucc) (x k.succ),
        HasDerivAt (derivWithin V (Icc (x k.castSucc) (x k.succ)))
          (derivWithin (derivWithin V (Icc (x k.castSucc) (x k.succ)))
            (Icc (x k.castSucc) (x k.succ)) t) t) ∧
      (∀ t ∈ Ioo (x k.castSucc) (x k.succ),
        W t = derivWithin V (Icc (x k.castSucc) (x k.succ)) t) := by
    intro k
    have hlt : x k.castSucc < x k.succ := hx (by simp [Fin.lt_def])
    have hu : UniqueDiffOn ℝ (Icc (x k.castSucc) (x k.succ)) := uniqueDiffOn_Icc hlt
    have h1 : ContDiffOn ℝ 1 (derivWithin V (Icc (x k.castSucc) (x k.succ)))
        (Icc (x k.castSucc) (x k.succ)) := (hpw k).derivWithin hu (by norm_num)
    refine ⟨h1.continuousOn, h1.continuousOn_derivWithin hu le_rfl, fun t ht ↦ ?_, fun t ht ↦ ?_⟩
    · have hd := hasDerivAt_of_contDiffOn_Icc h1 ht
      rwa [derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]
    · rw [hW k t ht, derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]
  obtain ⟨hW₁, hY₁, hd₁, heq₁⟩ := piece i
  obtain ⟨hW₂, hY₂, hd₂, heq₂⟩ := piece j
  rw [← hij] at hW₂ hY₂ hd₂ heq₂ hcq ⊢
  exact eq_of_hasWeakDeriv_of_jump hpc hcq hsub hΩ hW₁ hY₁ hd₁ heq₁ hW₂ hY₂ hd₂ heq₂ hzw

end SecondOrder

end OneDimensional

/-! ### Example 7.1.9: piecewise smooth functions on a triangulated polygon -/

section Triangulated

local notation "𝔼₂" => EuclideanSpace ℝ (Fin 2)

/-- **Example 7.1.9** of [han2009theoretical], on a triangulated polygon. Let
$\Omega \subseteq \mathbb{R}^2$ be open with a triangulation $\mathcal{T}$, and let $k \ge 0$.
Let $v \in C^k(\Omega)$, and for each triangle $K$ of $\mathcal{T}$ let $v$ agree on the open
triangle $K$ with a function $g_K \in C^{k+1}(\mathbb{R}^2)$. Let $w$ agree with the classical
derivative $\partial^{k+1} v$ on every open triangle. Then $w$ is the weak derivative of order
$k + 1$ of $v$ on $\Omega$, for all multi-indices of length $k + 1$ at once.

**Generalization.** The source assumes $v \in C^k(\overline\Omega)$. Only $v \in C^k(\Omega)$ is
used, because the weak derivatives on $\Omega$ do not see the boundary. At $k = 0$ this is the
continuity of $v$ on $\Omega$.

**Reading.** The source partitions $\overline\Omega$ into subdomains,
$\overline\Omega = \bigcup_n \overline\Omega_n$, with
$v|_{\Omega_n} \in C^{k+1}(\overline\Omega_n)$. Here the subdomains are the triangles of a
triangulation, since a partition into quadrilaterals refines to one, and the condition on
$\Omega_n$ means agreement on the open triangle with a $C^{k+1}$ function on the plane.

The values of $w$ off the open triangles are arbitrary, since the edges form a null set. The
proof does not use Green's formula, and no boundary measure enters. For $k = 0$ it is
`Triangulation.hasWeakFDerivOn_of_piecewise`: Fubini's theorem and the fundamental theorem of
calculus on almost every line, because the edges of the triangulation form a finite union of
segments. For general $k$ the same theorem is applied to the classical derivatives of order $k$
of $v$, which are continuous on $\Omega$ and piecewise $C^1$, and composed with them through
`HasWeakIteratedLineDerivOn.cons`. The version with elementwise $W^{k+1,p}$ regularity in place
of $C^{k+1}$ is `AtkinsonHan.Chapter07.example_7_2_7`. -/
theorem example_7_1_9 {Ω : Opens 𝔼₂} (𝒯 : Triangulation Ω) {k : ℕ} {v : 𝔼₂ → ℝ}
    (hv : ContDiffOn ℝ k v Ω) {g : 𝒯.elems → 𝔼₂ → ℝ} (hg : ∀ T, ContDiff ℝ (k + 1) (g T))
    (hvg : ∀ T, ∀ x ∈ 𝒯.K T, v x = g T x) {w : 𝔼₂ → 𝔼₂ [×(k + 1)]→L[ℝ] ℝ}
    (hw : ∀ T, ∀ x ∈ 𝒯.K T, w x = iteratedFDeriv ℝ (k + 1) v x) :
    definition_7_1_3 (k + 1) v w Ω := by
  have h₀ : HasWeakIteratedFDerivOn (k + 1) v (𝒯.pieceIteratedFDeriv (k + 1) g) Ω volume :=
    ⟨hv.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet,
      𝒯.locallyIntegrableOn_pieceIteratedFDeriv hg,
      fun φ y ↦ (𝒯.hasWeakIteratedLineDerivOn_of_piecewise hv hg hvg y).integral_smul_eq φ⟩
  -- `w` agrees with it almost everywhere on `Ω`: off the skeleton, a null set
  refine h₀.congr_ae (Filter.EventuallyEq.refl _ _) ?_
  have hae : ∀ᵐ x ∂(volume.restrict (Ω : Set 𝔼₂)), x ∈ ⋃ T, 𝒯.K T := by
    rw [ae_restrict_iff' Ω.isOpen.measurableSet]
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 𝒯.volume_diff_iUnion_K] with x hx hxΩ
    by_contra h
    exact hx ⟨hxΩ, h⟩
  filter_upwards [hae] with x hx
  obtain ⟨T, hT⟩ := mem_iUnion.1 hx
  rw [hw T x hT, 𝒯.pieceIteratedFDeriv_of_mem g T hT,
    𝒯.iteratedFDeriv_eq_of_mem_K hvg (k + 1) T hT]

end Triangulated

end AtkinsonHan.Chapter07
