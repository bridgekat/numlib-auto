/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Sobolev.Interval.DifferenceQuotient
import NumlibSurface.Brezis.Chapter04.Section03

/-!
# Brezis, Section 8.2: The Sobolev space $W^{1,p}(I)$

This module formalizes Section 8.2 of [brezis2011functional], including its closing paragraph on the
spaces $W^{m,p}(I)$. Let $I \subseteq \mathbb{R}$ be an open interval, bounded or unbounded, and let
$1 \le p \le \infty$. The Sobolev space $W^{1,p}(I)$ is the set of $u \in L^p(I)$ for which there is
$g \in L^p(I)$ with
$$\int_I u \varphi' = -\int_I g \varphi \quad \text{for all } \varphi \in C_c^1(I).$$
The function $g$ is the weak derivative $u'$. The space has the norm
$\|u\|_{W^{1,p}} = \|u\|_{L^p} + \|u'\|_{L^p}$, and $H^1(I) = W^{1,2}(I)$ is a Hilbert space. The
section proves that $W^{1,p}(I)$ is a Banach space (Proposition 8.1) and that every
$u \in W^{1,p}(I)$ has a representative $\tilde u$, continuous on $\bar I$, with
$\tilde u(x) - \tilde u(y) = \int_y^x u'$ (Theorem 8.2). It gives three characterizations of
$W^{1,p}$ (Propositions 8.3–8.5), an extension operator $W^{1,p}(I) \to W^{1,p}(\mathbb{R})$
(Theorem 8.6), the density of $C_c^\infty(\mathbb{R})$ (Theorem 8.7), the embedding
$W^{1,p}(I) \subseteq L^\infty(I)$ and two compact embeddings (Theorem 8.8), and the rules for
products and compositions (Corollaries 8.9–8.11). For $m \ge 2$, the space $W^{m,p}(I)$ is the set
of $u \in W^{m-1,p}(I)$ with $u' \in W^{m-1,p}(I)$.

The proofs specialize the backbone modules `Numlib.Analysis.Sobolev.Interval.Basic`,
`Numlib.Analysis.Sobolev.Interval.Extension`, `Numlib.Analysis.Sobolev.Interval.Density`,
`Numlib.Analysis.Sobolev.Interval.Embedding`, `Numlib.Analysis.Sobolev.Interval.Higher`,
`Numlib.Analysis.Sobolev.Interval.Zero` and `Numlib.Analysis.Sobolev.Interval.DifferenceQuotient`.

## Main definitions

* Section 8.2, definition of $W^{1,p}(I)$, `Brezis.Chapter08.sobolevSpace` and
  `Brezis.Chapter08.MemSobolevSpace`: the space of pairs $(u, u')$ in $L^p(I) \times L^p(I)$, and
  the condition $u \in W^{1,p}(I)$ on a function $u$.
* Section 8.2, notation, `Brezis.Chapter08.H1`: the space $H^1(I) = W^{1,2}(I)$.
* Section 8.2, notation, `Brezis.Chapter08.sobolevNorm`: the norm $\|u\|_{L^p} + \|u'\|_{L^p}$.
* Section 8.2, the Sobolev spaces $W^{m,p}$, `Brezis.Chapter08.MemSobolevSpaceHigher`,
  `Brezis.Chapter08.sobolevSpaceHigher` and `Brezis.Chapter08.Hm`: the space $W^{m,p}(I)$, its
  inductive definition, and $H^m(I) = W^{m,2}(I)$.
* Section 8.2, the Sobolev spaces $W^{m,p}$, `Brezis.Chapter08.sobolevNormHigher`: the norm
  $\|u\|_{L^p} + \sum_{\alpha=1}^m \|D^\alpha u\|_{L^p}$.

## Main results

* Section 8.2, footnote 2, `Brezis.Chapter08.memSobolevSpace_deriv_unique`: the weak derivative is
  unique almost everywhere.
* Remark 1, `Brezis.Chapter08.remark_8_1`: the test functions $C_c^1(I)$ and $C_c^\infty(I)$ give
  the same space $W^{1,p}(I)$.
* Remark 2, `Brezis.Chapter08.remark_8_2`, `Brezis.Chapter08.remark_8_2_deriv` and
  `Brezis.Chapter08.remark_8_2_Icc`: a $C^1$ function $u$ with $u, u' \in L^p(I)$ lies in
  $W^{1,p}(I)$, and its weak derivative is the classical one.
* Section 8.2, Examples (i), `Brezis.Chapter08.example_abs`, `Brezis.Chapter08.example_abs_deriv`
  and `Brezis.Chapter08.example_piecewise_contDiff`: the function $|x|$ and the continuous piecewise
  $C^1$ functions lie in $W^{1,p}$.
* Section 8.2, Examples (ii), `Brezis.Chapter08.example_sign_not_mem`: the sign function does not
  lie in $W^{1,p}((-1, 1))$.
* Section 8.2, notation, `Brezis.Chapter08.sobolevNorm_equiv`, `Brezis.Chapter08.inner_H1` and
  `Brezis.Chapter08.norm_H1_sq`: the equivalent norm, and the scalar product and the norm of $H^1$.
* Proposition 8.1, `Brezis.Chapter08.proposition_8_1`: $W^{1,p}(I)$ is a Banach space, reflexive for
  $1 < p < \infty$ and separable for $1 \le p < \infty$, and $H^1(I)$ is a separable Hilbert space.
* Remark 4, `Brezis.Chapter08.remark_8_4`: limits in $L^p$ of sequences in $W^{1,p}$ whose
  derivatives converge, or for $p > 1$ stay bounded, lie in $W^{1,p}$.
* Theorem 8.2, `Brezis.Chapter08.theorem_8_2`: every $u \in W^{1,p}(I)$ has a representative
  $\tilde u$, continuous on $\bar I$, with $\tilde u(x) - \tilde u(y) = \int_y^x u'$.
* Remark 5, `Brezis.Chapter08.remark_8_5`: membership in $W^{1,p}$ depends only on the class of $u$
  almost everywhere, and the continuous representative is unique.
* Remark 6, `Brezis.Chapter08.remark_8_6`: if $u'$ has a continuous representative on $\bar I$, then
  $\tilde u \in C^1(\bar I)$.
* Lemma 8.1, `Brezis.Chapter08.lemma_8_1` (du Bois-Reymond): if $\int_I f \varphi' = 0$ for all test
  functions, then $f$ is constant almost everywhere.
* Lemma 8.2, `Brezis.Chapter08.lemma_8_2`: the primitive of $g \in L^1_{\mathrm{loc}}(I)$ is
  continuous, with weak derivative $g$.
* Remark 7, `Brezis.Chapter08.remark_8_7` and `Brezis.Chapter08.remark_8_7_of_bounded`: the
  primitive of $g \in L^p(I)$ lies in $W^{1,p}(I)$ if it lies in $L^p(I)$, and always when $I$ is
  bounded.
* Proposition 8.3, `Brezis.Chapter08.proposition_8_3`: for $1 < p \le \infty$, $u \in W^{1,p}(I)$ if
  and only if $|\int_I u \varphi'| \le C \|\varphi\|_{L^{p'}}$ for all test functions.
* Remark 8, `Brezis.Chapter08.remark_8_8`: the implication (i) $\Rightarrow$ (ii) of Proposition 8.3
  for $p = 1$, and $W^{1,1}((a, b))$ as the space of absolutely continuous functions.
* Proposition 8.4, `Brezis.Chapter08.proposition_8_4`: $u \in W^{1,\infty}(I)$ if and only if $u$ is
  Lipschitz almost everywhere.
* Proposition 8.5, `Brezis.Chapter08.proposition_8_5`: for $1 < p < \infty$,
  $u \in W^{1,p}(\mathbb{R})$ if and only if $\|\tau_h u - u\|_{L^p} \le C|h|$ for all $h$.
* Theorem 8.6, `Brezis.Chapter08.theorem_8_6` and `Brezis.Chapter08.theorem_8_6_const`: the
  extension operator $W^{1,p}(I) \to W^{1,p}(\mathbb{R})$, with the constants of footnote 6.
* Lemma 8.3, `Brezis.Chapter08.lemma_8_3`: the product of a smooth cut-off function and the
  extension by $0$ of $u \in W^{1,p}((0, 1))$ lies in $W^{1,p}((0, \infty))$.
* Theorem 8.7, `Brezis.Chapter08.theorem_8_7`: the restrictions to $I$ of the functions in
  $C_c^\infty(\mathbb{R})$ are dense in $W^{1,p}(I)$ for $1 \le p < \infty$.
* Remark 9, `Brezis.Chapter08.remark_8_9`: $C_c^\infty(I)$ is not dense in $W^{1,p}(I)$ for a
  bounded interval $I$.
* Lemma 8.4, `Brezis.Chapter08.lemma_8_4`: $\rho \star v \in W^{1,p}(\mathbb{R})$ with
  $(\rho \star v)' = \rho \star v'$.
* Theorem 8.8, `Brezis.Chapter08.theorem_8_8`: $W^{1,p}(I) \subseteq L^\infty(I)$ with continuous
  injection, and for bounded $I$ the compact injections $W^{1,p}(I) \subseteq C(\bar I)$ for
  $1 < p \le \infty$ and $W^{1,1}(I) \subseteq L^q(I)$ for $1 \le q < \infty$.
* Remark 10, `Brezis.Chapter08.remark_8_10_a`, `Brezis.Chapter08.remark_8_10_b`,
  `Brezis.Chapter08.remark_8_10_c` and `Brezis.Chapter08.remark_8_10_d`:
  $W^{1,1}((0, 1)) \subseteq C([0, 1])$ is not compact, Helly's selection theorem,
  $W^{1,p}(I) \subseteq L^\infty(I)$ is not compact for unbounded $I$, and local uniform convergence
  of a subsequence of a bounded sequence for $p > 1$.
* Remark 11, `Brezis.Chapter08.remark_8_11`: on a bounded interval, $\|u'\|_{L^p} + \|u\|_{L^q}$ is
  an equivalent norm on $W^{1,p}$.
* Remark 12, `Brezis.Chapter08.remark_8_12`: $W^{1,p}(I) \subseteq L^q(I)$ for $p \le q \le \infty$.
* Corollary 8.9, `Brezis.Chapter08.corollary_8_9`: for unbounded $I$ and $p < \infty$, $u(x) \to 0$
  as $|x| \to \infty$.
* Corollary 8.10, `Brezis.Chapter08.corollary_8_10`, `Brezis.Chapter08.corollary_8_10_deriv` and
  `Brezis.Chapter08.corollary_8_10_parts`: $uv \in W^{1,p}(I)$, $(uv)' = u'v + uv'$, and the formula
  of integration by parts.
* Corollary 8.11, `Brezis.Chapter08.corollary_8_11`, `Brezis.Chapter08.corollary_8_11_deriv` and
  `Brezis.Chapter08.corollary_8_11_of_bounded`: $G \circ u \in W^{1,p}(I)$ with
  $(G \circ u)' = (G' \circ u) u'$.
* Section 8.2, the Sobolev spaces $W^{m,p}$,
  `Brezis.Chapter08.memSobolevSpaceHigher_iff_forall_integral`,
  `Brezis.Chapter08.memSobolevSpaceHigher_deriv`, `Brezis.Chapter08.sobolevNormHigher_equiv` and
  `Brezis.Chapter08.inner_Hm`: the characterization of $W^{m,p}(I)$ by $m$ weak derivatives, its
  norm and the scalar product of $H^m(I)$.
* Section 8.2, the Sobolev spaces $W^{m,p}$, `Brezis.Chapter08.interpolationInequality` and
  `Brezis.Chapter08.interpolationInequality_norm_equiv`: the interpolation inequality $\|D^j
  u\|_{L^p} \le \varepsilon \|D^m u\|_{L^p} + C \|u\|_{L^p}$ and the equivalent norm
  $\|u\|_{L^p} + \|D^m u\|_{L^p}$.
* Section 8.2, the Sobolev spaces $W^{m,p}$, `Brezis.Chapter08.sobolevSpaceHigher_subset_contDiff`
  and `Brezis.Chapter08.sobolevSpaceHigher_subset_contDiff_compact`: for bounded $I$,
  $W^{m,p}(I) \subseteq C^{m-1}(\bar I)$ with continuous injection, compact for $1 < p \le \infty$.

## Conventions

* An open set $I \subseteq \mathbb{R}$ is `I : TopologicalSpace.Opens ℝ`. A result that needs $I$ to
  be an interval has the hypothesis `(I : Set ℝ).OrdConnected`; the other results hold for every
  open set $I$. The bounded interval $(a, b)$ is `TopologicalSpace.Opens.Ioo a b`, and $\mathbb{R}$
  is `⊤`.
* The exponent $1 \le p \le \infty$ is `p : ℝ≥0∞` with `[Fact (1 ≤ p)]`. The conjugate exponent $p'$
  is `q` with `[p.HolderConjugate q]`.
* An element $u \in W^{1,p}(I)$ is `u : SobolevIntervalLp 1 p I`. Its function is
  `SobolevIntervalLp.fn u` (equal to `SobolevIntervalLp.deriv u 0`), its weak derivative $u'$ is
  `SobolevIntervalLp.deriv u 1`, and its continuous representative $\tilde u$ of Theorem 8.2 is
  `SobolevIntervalLp.rep u`. The value "$u(x)$ for $x \in \bar I$" of the source is
  `SobolevIntervalLp.rep u x`.
* The test functions $C_c^\infty(I)$ are Mathlib's `𝓓(I, ℝ)`. Where the source tests against
  $C_c^1(I)$, the statements here test against $C_c^\infty(I)$. Remark 1 shows that both classes
  define the same space $W^{1,p}(I)$.
* The length $|I|$ of $I$ is `(volume (I : Set ℝ)).toReal`, which is $0$ for an unbounded interval.

## Implementation notes

* The type `SobolevIntervalLp 1 p I` carries the norm $(\|u\|_{L^p}^p + \|u'\|_{L^p}^p)^{1/p}$,
  which the source calls an equivalent norm. The norm $\|u\|_{L^p} + \|u'\|_{L^p}$ of the source is
  `Brezis.Chapter08.sobolevNorm`, and statements that quote this norm use it. For $p = 2$ the norm
  of the type is the norm of $H^1(I)$.
* The definition of the source, as a condition on functions, is `Brezis.Chapter08.MemSobolevSpace`.
  It agrees with the backbone's `MemSobolevIntervalLp u 1 p I` by
  `Brezis.Chapter08.memSobolevSpace_iff_memSobolevIntervalLp`. In the same way, $W^{m,p}(I)$ is the
  type `SobolevIntervalLp m p I`, and its inductive definition is
  `Brezis.Chapter08.MemSobolevSpaceHigher` (`Brezis.Chapter08.memSobolevSpaceHigher_iff`).
* The source proves Theorem 8.8(5) and Corollaries 8.9–8.11 through the density theorem. The
  backbone proves them from the absolutely continuous representative $\tilde u$.

## Deviations from the source

* **Lemma 8.3** (generalization). The source assumes $\eta = 1$ on $x < 1/4$ and $\eta = 0$ on
  $x > 3/4$. Only the second condition is assumed. See `Brezis.Chapter08.lemma_8_3`.
* **Remark 10(c)** (generalization). The source states the claim for $1 < p \le \infty$. It holds
  for every $1 \le p \le \infty$. See `Brezis.Chapter08.remark_8_10_c`.
* **Corollary 8.11, the derivative** (generalization). The source assumes $G(0) = 0$. The formula
  $(G \circ u)' = (G' \circ u) u'$ holds without this assumption. See
  `Brezis.Chapter08.corollary_8_11_deriv`.

## Not formalized

* **Remark 3**, on distributions.
* **Remark 8, functions of bounded variation.** The failure of the converse of (i) $\Rightarrow$
  (ii) of Proposition 8.3 for $p = 1$, and the characterizations (a)–(c) of the functions of bounded
  variation.
* **Remark 10(a) on other intervals.** Only the interval $(0, 1)$ is formalized.
* **Remark 10(b) on an unbounded interval.**
* **Remark 12, the second claim.** In general $u \notin L^q(I)$ for $q \in [1, p)$ (Exercise 8.1).
-/

open Filter MeasureTheory Set TopologicalSpace
open scoped Convolution Distributions ENNReal InnerProductSpace Topology

noncomputable section

namespace Brezis.Chapter08

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {I : Opens ℝ}

/-! ### The definition -/

/-- **Section 8.2** of [brezis2011functional], definition of $W^{1,p}(I)$. Let
$I \subseteq \mathbb{R}$ be open and $1 \le p \le \infty$. The **Sobolev space** $W^{1,p}(I)$ is
the space of pairs $(u, u')$ in $L^p(I) \times L^p(I)$ such that $u'$ is the weak derivative of
$u$ on $I$. It is a Banach space.

The type is the backbone's `SobolevIntervalLp 1 p I`. The definition of the source as a
condition on functions is `Brezis.Chapter08.MemSobolevSpace`. -/
abbrev sobolevSpace (p : ℝ≥0∞) (I : Opens ℝ) : Type := SobolevIntervalLp 1 p I

/-- **Section 8.2** of [brezis2011functional], notation. The space $H^1(I)$ is $W^{1,2}(I)$. -/
abbrev H1 (I : Opens ℝ) : Type := sobolevSpace 2 I

/-- **Section 8.2** of [brezis2011functional], definition of $W^{1,p}(I)$ as a condition on
functions. Let $I \subseteq \mathbb{R}$ be open, $1 \le p \le \infty$ and
$u : \mathbb{R} \to \mathbb{R}$. Then $u \in W^{1,p}(I)$ means that $u \in L^p(I)$ and that
there is $g \in L^p(I)$ with
$$\int_I u \varphi' = -\int_I g \varphi \quad \text{for all } \varphi \in C_c^\infty(I).$$
The function $g$ is the **weak derivative** $u'$. It is unique almost everywhere on $I$
(`Brezis.Chapter08.memSobolevSpace_deriv_unique`).

The source tests against $\varphi \in C_c^1(I)$. On an interval both classes of test functions
give the same condition, by Remark 1 (`Brezis.Chapter08.remark_8_1`). -/
def MemSobolevSpace (p : ℝ≥0∞) (I : Opens ℝ) (u : ℝ → ℝ) : Prop :=
  MemLp u p (volume.restrict I) ∧ ∃ g : ℝ → ℝ, MemLp g p (volume.restrict I) ∧
    ∀ φ : 𝓓(I, ℝ), ∫ x in (I : Set ℝ), u x * deriv φ x = -∫ x in (I : Set ℝ), g x * φ x

/-- Let $I \subseteq \mathbb{R}$ be open, $1 \le p \le \infty$ and $u : \mathbb{R} \to \mathbb{R}$.
Then $u \in W^{1,p}(I)$ in the sense of the definition of Section 8.2 of [brezis2011functional]
if and only if `MemSobolevIntervalLp u 1 p I` holds: $u \in L^p(I)$, and $u$ has a weak
derivative on $I$ that lies in $L^p(I)$.

A function in $L^p(I)$ is locally integrable on $I$, so the identity against test functions says
that $g$ is the weak derivative `HasWeakDerivOn u g I`. -/
theorem memSobolevSpace_iff_memSobolevIntervalLp {u : ℝ → ℝ} :
    MemSobolevSpace p I u ↔ MemSobolevIntervalLp u 1 p I := by
  rw [MemSobolevSpace, memSobolevIntervalLp_one_iff]
  refine and_congr_right fun hu ↦ ⟨fun ⟨g, hg, h⟩ ↦ ⟨g, hasWeakDerivOn_iff.2
    ⟨hu.locallyIntegrableOn Fact.out, hg.locallyIntegrableOn Fact.out, fun φ ↦ ?_⟩, hg⟩,
    fun ⟨g, hg, hgp⟩ ↦ ⟨g, hgp, fun φ ↦ ?_⟩⟩
  · have := h φ
    simp only [mul_comm] at this ⊢
    exact this
  · have := hg.integral_deriv_mul φ
    simp only [mul_comm] at this ⊢
    exact this

/-- **Footnote 2** of Section 8.2 of [brezis2011functional]. Let $I \subseteq \mathbb{R}$ be open,
$1 \le p \le \infty$, and $u, g_1, g_2 \in L^p(I)$. Suppose that, for $i = 1, 2$,
$$\int_I u \varphi' = -\int_I g_i \varphi \quad \text{for all } \varphi \in C_c^\infty(I).$$
Then $g_1 = g_2$ almost everywhere on $I$.

The source refers to its Corollary 4.24. The proof uses the uniqueness of weak derivatives,
`HasWeakIteratedLineDerivOn.ae_eq`. -/
theorem memSobolevSpace_deriv_unique {u g₁ g₂ : ℝ → ℝ} (hu : MemLp u p (volume.restrict I))
    (hg₁ : MemLp g₁ p (volume.restrict I)) (hg₂ : MemLp g₂ p (volume.restrict I))
    (h₁ : ∀ φ : 𝓓(I, ℝ), ∫ x in (I : Set ℝ), u x * deriv φ x = -∫ x in (I : Set ℝ), g₁ x * φ x)
    (h₂ : ∀ φ : 𝓓(I, ℝ), ∫ x in (I : Set ℝ), u x * deriv φ x = -∫ x in (I : Set ℝ), g₂ x * φ x) :
    g₁ =ᵐ[volume.restrict I] g₂ := by
  have hw : ∀ {g : ℝ → ℝ}, MemLp g p (volume.restrict I) →
      (∀ φ : 𝓓(I, ℝ), ∫ x in (I : Set ℝ), u x * deriv φ x = -∫ x in (I : Set ℝ), g x * φ x) →
      HasWeakDerivOn u g I := fun hg h ↦
    hasWeakDerivOn_iff.2 ⟨hu.locallyIntegrableOn Fact.out, hg.locallyIntegrableOn Fact.out,
      fun φ ↦ by
        have := h φ
        simp only [mul_comm] at this ⊢
        exact this⟩
  exact (ae_restrict_iff' I.isOpen.measurableSet).2 ((hw hg₁ h₁).ae_eq (hw hg₂ h₂))

/-- **Remark 2** in Chapter 8 of [brezis2011functional]. Let $I \subseteq \mathbb{R}$ be open and
$1 \le p \le \infty$. If $u \in C^1(I)$, $u \in L^p(I)$ and the classical derivative $u'$ lies
in $L^p(I)$, then $u \in W^{1,p}(I)$.

The weak derivative is the classical one, by `Brezis.Chapter08.remark_8_2_deriv`. The proof
specializes `memSobolevIntervalLp_of_contDiffOn`. -/
theorem remark_8_2 {u : ℝ → ℝ} (hu : ContDiffOn ℝ 1 u I) (hup : MemLp u p (volume.restrict I))
    (hup' : MemLp (deriv u) p (volume.restrict I)) : MemSobolevSpace p I u :=
  memSobolevSpace_iff_memSobolevIntervalLp.2 (memSobolevIntervalLp_of_contDiffOn hu hup hup').1

/-- **Remark 2** in Chapter 8 of [brezis2011functional], consistency of the notation. Let
$I \subseteq \mathbb{R}$ be open and $u \in C^1(I)$, with classical derivative $u'$. Then
$$\int_I u \varphi' = -\int_I u' \varphi \quad \text{for all } \varphi \in C_c^\infty(I).$$
So the classical derivative satisfies the defining identity of the weak derivative. -/
theorem remark_8_2_deriv {u : ℝ → ℝ} (hu : ContDiffOn ℝ 1 u I) (φ : 𝓓(I, ℝ)) :
    ∫ x in (I : Set ℝ), u x * deriv φ x = -∫ x in (I : Set ℝ), deriv u x * φ x := by
  have := (hasWeakDerivOn_of_contDiffOn hu).integral_deriv_mul φ
  simp only [mul_comm] at this ⊢
  exact this

/-- **Remark 2** in Chapter 8 of [brezis2011functional], the last sentence. Let $a < b$ and
$1 \le p \le \infty$. If $u$ is $C^1$ on $[a, b]$, then $u \in W^{1,p}((a, b))$. So
$C^1(\bar I) \subseteq W^{1,p}(I)$ for a bounded interval $I$.

The condition that $u$ is $C^1$ on $[a, b]$ is `ContDiffOn ℝ 1 u (Icc a b)`. The proof
specializes `memSobolevIntervalLp_of_contDiffOn_Icc`. -/
theorem remark_8_2_Icc {a b : ℝ} (hab : a < b) {u : ℝ → ℝ} (hu : ContDiffOn ℝ 1 u (Icc a b)) :
    MemSobolevSpace p (Opens.Ioo a b) u :=
  memSobolevSpace_iff_memSobolevIntervalLp.2 (memSobolevIntervalLp_of_contDiffOn_Icc hab hu).1

/-! ### Remark 1: the test class -/

/-- Let $f : \mathbb{R} \to \mathbb{R}$ have compact support contained in the open set $I$, and let
$y_0 \in I$; then there are points $l \le h$ of $I$ such that the support of $f$ lies in
$(l, h)$. -/
private theorem exists_mem_tsupport_subset_Ioo_of_hasCompactSupport {f : ℝ → ℝ}
    (hf : HasCompactSupport f) (hfI : tsupport f ⊆ I) {y₀ : ℝ} (hy₀ : y₀ ∈ I) :
    ∃ lo hi : ℝ, lo ∈ I ∧ hi ∈ I ∧ lo ≤ hi ∧ tsupport f ⊆ Ioo lo hi := by
  obtain ⟨lo, hi, hlo, hhi, hlohi, hsupp⟩ : ∃ lo hi : ℝ, lo ∈ I ∧ hi ∈ I ∧ lo ≤ hi ∧
      tsupport f ⊆ Icc lo hi := by
    by_cases hne : (tsupport f).Nonempty
    · obtain ⟨lo, hlo⟩ := hf.exists_isLeast hne
      obtain ⟨hi, hhi⟩ := hf.exists_isGreatest hne
      exact ⟨lo, hi, hfI hlo.1, hfI hhi.1, hlo.2 hhi.1, fun t ht ↦ ⟨hlo.2 ht, hhi.2 ht⟩⟩
    · rw [Set.not_nonempty_iff_eq_empty] at hne
      exact ⟨y₀, y₀, hy₀, hy₀, le_rfl, hne ▸ empty_subset _⟩
  obtain ⟨εl, hεl, hl⟩ := Metric.isOpen_iff.1 I.isOpen lo hlo
  obtain ⟨εh, hεh, hh⟩ := Metric.isOpen_iff.1 I.isOpen hi hhi
  refine ⟨lo - εl / 2, hi + εh / 2, hl ?_, hh ?_, by linarith, hsupp.trans ?_⟩
  · rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith
  · rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith
  · exact Icc_subset_Ioo (by linarith) (by linarith)

/-- **Remark 1** in Chapter 8 of [brezis2011functional]. Let $I$ be an open interval,
$1 \le p \le \infty$ and $u, g \in L^p(I)$. Then
$$\int_I u \varphi' = -\int_I g \varphi$$
holds for all $\varphi \in C_c^\infty(I)$ if and only if it holds for all
$\varphi \in C_c^1(I)$. So the definition of $W^{1,p}(I)$ can use either class of test
functions.

The space $C_c^1(I)$ is Mathlib's `TestFunction I ℝ 1`. The source mollifies $\varphi \in C_c^1(I)$.
The proof here is different: the identity for smooth test functions makes $u$ the function of an
element of $W^{1,p}(I)$ with derivative $g$, and then the integration by parts against a $C^1$
factor (`SobolevIntervalLp.integral_deriv_mul_contDiffOn`, Corollary 8.10), on a compact
subinterval that contains the support of $\varphi$, gives the identity for $\varphi$. -/
theorem remark_8_1 (hI : (I : Set ℝ).OrdConnected) {u g : ℝ → ℝ}
    (hu : MemLp u p (volume.restrict I)) (hg : MemLp g p (volume.restrict I)) :
    (∀ φ : 𝓓(I, ℝ), ∫ x in (I : Set ℝ), u x * deriv φ x = -∫ x in (I : Set ℝ), g x * φ x) ↔
      ∀ φ : 𝓓^{1}(I, ℝ), ∫ x in (I : Set ℝ), u x * deriv φ x = -∫ x in (I : Set ℝ), g x * φ x := by
  refine ⟨fun h φ ↦ ?_, fun h φ ↦
    h ⟨φ, φ.contDiff.of_le (mod_cast le_top), φ.hasCompactSupport, φ.tsupport_subset⟩⟩
  -- the element of `W^{1,p}(I)` carried by `u`, with derivative `g`
  have hweak : HasWeakDerivOn u g I :=
    hasWeakDerivOn_iff.2 ⟨hu.locallyIntegrableOn Fact.out, hg.locallyIntegrableOn Fact.out,
      fun ψ ↦ by
        have := h ψ
        simp only [mul_comm] at this ⊢
        exact this⟩
  obtain ⟨v, hv⟩ := (memSobolevIntervalLp_one_iff.2 ⟨hu, g, hweak, hg⟩).exists_sobolevIntervalLp
  have hv1 : ⇑(v.deriv 1) =ᵐ[volume.restrict I] g :=
    (ae_restrict_iff' I.isOpen.measurableSet).2
      ((v.hasWeakDerivOn_fn.congr_ae hv (EventuallyEq.refl _ _)).ae_eq hweak)
  have hurep : u =ᵐ[volume.restrict I] v.rep :=
    hv.symm.trans (SobolevIntervalLp.fn_ae_eq_rep hI v)
  -- a compact subinterval of `I` containing the support of `φ`
  by_cases hne : (tsupport φ).Nonempty
  · obtain ⟨y₀, hy₀⟩ : (I : Set ℝ).Nonempty := ⟨_, φ.tsupport_subset hne.some_mem⟩
    obtain ⟨lo, hi, hlo, hhi, -, hsupp⟩ :=
      exists_mem_tsupport_subset_Ioo_of_hasCompactSupport φ.hasCompactSupport
        φ.tsupport_subset hy₀
    have hIcc : Icc lo hi ⊆ I := hI.out hlo hhi
    have hφlo : φ lo = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ (hsupp h).1.ne rfl
    have hφhi : φ hi = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ (hsupp h).2.ne rfl
    have hφ' : ∀ x, x ∉ Ioc lo hi → deriv φ x = 0 := fun x hx ↦ by
      by_contra hd
      exact hx (Ioo_subset_Ioc_self (hsupp (support_deriv_subset hd)))
    have hφ0 : ∀ x, x ∉ Ioc lo hi → φ x = 0 := fun x hx ↦
      image_eq_zero_of_notMem_tsupport fun h ↦ hx (Ioo_subset_Ioc_self (hsupp h))
    have hlohi : lo ≤ hi := (hsupp hne.some_mem).1.le.trans (hsupp hne.some_mem).2.le
    -- both integrals live on `[lo, hi]`
    have e1' : (fun x ↦ u x * deriv φ x) =ᵐ[volume.restrict I] fun x ↦ v.rep x * deriv φ x :=
      hurep.mono fun x hx ↦ by simp only [hx]
    have e2' : (fun x ↦ g x * φ x) =ᵐ[volume.restrict I] fun x ↦ v.deriv 1 x * φ x :=
      hv1.mono fun x hx ↦ by simp only [hx]
    have e1 : ∫ x in (I : Set ℝ), u x * deriv φ x = ∫ x in lo..hi, v.rep x * deriv φ x := by
      rw [integral_congr_ae e1',
        setIntegral_eq_of_subset_of_forall_sdiff_eq_zero I.isOpen.measurableSet
          (Ioc_subset_Icc_self.trans hIcc) (fun x hx ↦ by rw [hφ' x hx.2, mul_zero]),
        intervalIntegral.integral_of_le hlohi]
    have e2 : ∫ x in (I : Set ℝ), g x * φ x = ∫ x in lo..hi, v.deriv 1 x * φ x := by
      rw [integral_congr_ae e2',
        setIntegral_eq_of_subset_of_forall_sdiff_eq_zero I.isOpen.measurableSet
          (Ioc_subset_Icc_self.trans hIcc) (fun x hx ↦ by rw [hφ0 x hx.2, mul_zero]),
        intervalIntegral.integral_of_le hlohi]
    rw [e1, e2, SobolevIntervalLp.integral_deriv_mul_contDiffOn hI v
      (subset_closure (hIcc (right_mem_Icc.2 hlohi)))
      (subset_closure (hIcc (left_mem_Icc.2 hlohi)))
      ((φ.contDiff.of_le (mod_cast le_rfl)).contDiffOn), hφlo, hφhi]
    ring
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    have hφ0 : ∀ x, φ x = 0 := fun x ↦
      image_eq_zero_of_notMem_tsupport (by rw [hne]; exact notMem_empty x)
    have hφ' : ∀ x, deriv φ x = 0 := fun x ↦ by
      by_contra hd
      exact absurd (support_deriv_subset hd) (by rw [hne]; exact notMem_empty x)
    simp only [hφ0, hφ', mul_zero, integral_zero, neg_zero]

/-! ### The Examples -/

/-- **Section 8.2** of [brezis2011functional], Examples (i). Let $1 \le p \le \infty$. The function
$u(x) = |x|$ belongs to $W^{1,p}((-1, 1))$.

The proof specializes `memSobolevIntervalLp_abs`. -/
theorem example_abs : MemSobolevSpace p (Opens.Ioo (-1) 1) fun x ↦ |x| :=
  memSobolevSpace_iff_memSobolevIntervalLp.2 memSobolevIntervalLp_abs.1

/-- **Section 8.2** of [brezis2011functional], Examples (i), the derivative. Let $g(x) = 1$ for
$x > 0$ and $g(x) = -1$ for $x \le 0$. Then
$$\int_{-1}^1 |x| \varphi'(x) \, dx = -\int_{-1}^1 g(x) \varphi(x) \, dx \quad \text{for all }
  \varphi \in C_c^\infty((-1, 1)).$$
So the weak derivative of $|x|$ on $(-1, 1)$ is the sign function $g$.

The source defines $g$ on $(0, 1)$ and on $(-1, 0)$. The value $g(0) = -1$ does not matter,
since a point has measure $0$. -/
theorem example_abs_deriv (φ : 𝓓(Opens.Ioo (-1) 1, ℝ)) :
    ∫ x in Ioo (-1 : ℝ) 1, |x| * deriv φ x
      = -∫ x in Ioo (-1 : ℝ) 1, (if 0 < x then 1 else -1) * φ x := by
  have := (memSobolevIntervalLp_abs (p := 1)).2.integral_deriv_mul φ
  simp only [mul_comm, Opens.coe_Ioo] at this ⊢
  exact this

/-- **Section 8.2** of [brezis2011functional], Examples (i), the general case. Let
$1 \le p \le \infty$, let $a = x_0 < x_1 < \dots < x_{N+1} = b$, and let $g$ be continuous on
$[a, b]$ and $C^1$ on each open interval $(x_j, x_{j+1})$, $j = 0, \dots, N$. Suppose that there
is one constant $C$ with $|g'| \le C$ on all these intervals. Then $g \in W^{1,p}((a, b))$.

The source says that $g$ is piecewise $C^1$ on $[a, b]$; here this means that $g$ is $C^1$ on
the open intervals of the partition with a common bound on $g'$. The partition is a strictly
increasing `x : Fin (N + 2) → ℝ`. The proof specializes
`memSobolevIntervalLp_of_piecewise_contDiffOn`. -/
theorem example_piecewise_contDiff {a b : ℝ} {N : ℕ} {x : Fin (N + 2) → ℝ} (hx : StrictMono x)
    (hxa : x 0 = a) (hxb : x (Fin.last (N + 1)) = b) {g : ℝ → ℝ} (hg : ContinuousOn g (Icc a b))
    (hg' : ∀ j : Fin (N + 1), ContDiffOn ℝ 1 g (Ioo (x j.castSucc) (x j.succ)))
    (hbdd : ∃ C, ∀ j : Fin (N + 1), ∀ t ∈ Ioo (x j.castSucc) (x j.succ), |deriv g t| ≤ C) :
    MemSobolevSpace p (Opens.Ioo a b) g :=
  memSobolevSpace_iff_memSobolevIntervalLp.2
    (memSobolevIntervalLp_of_piecewise_contDiffOn hx hxa hxb hg hg' hbdd).1

/-- **Section 8.2** of [brezis2011functional], Examples (ii). Let $1 \le p \le \infty$. The sign
function, $g(x) = 1$ for $x > 0$ and $g(x) = -1$ for $x \le 0$, does not belong to
$W^{1,p}((-1, 1))$.

The proof specializes `not_memSobolevIntervalLp_sign`. -/
theorem example_sign_not_mem :
    ¬ MemSobolevSpace p (Opens.Ioo (-1) 1) fun x ↦ if 0 < x then (1 : ℝ) else -1 := fun h ↦
  not_memSobolevIntervalLp_sign (memSobolevSpace_iff_memSobolevIntervalLp.1 h)

/-! ### The norm -/

/-- **Section 8.2** of [brezis2011functional], notation. The norm of $u \in W^{1,p}(I)$ in the
source is
$$\|u\|_{W^{1,p}} = \|u\|_{L^p} + \|u'\|_{L^p}.$$

The norm of the type `SobolevIntervalLp 1 p I` is a different, equivalent norm
(`Brezis.Chapter08.sobolevNorm_equiv`). -/
def sobolevNorm (u : SobolevIntervalLp 1 p I) : ℝ := ‖u.deriv 0‖ + ‖u.deriv 1‖

/-- Let $I \subseteq \mathbb{R}$ be open and $1 \le p \le \infty$. The norm $\|u\|_{W^{1,p}}$ of
Section 8.2 of [brezis2011functional] is nonnegative for every $u \in W^{1,p}(I)$. -/
theorem sobolevNorm_nonneg (u : SobolevIntervalLp 1 p I) : 0 ≤ sobolevNorm u :=
  add_nonneg (norm_nonneg _) (norm_nonneg _)

/-- **Section 8.2** of [brezis2011functional], notation, the equivalent norm. Let
$I \subseteq \mathbb{R}$ be open and $1 \le p \le \infty$. The norm of the type,
$\|u\| = (\|u\|_{L^p}^p + \|u'\|_{L^p}^p)^{1/p}$ for $p < \infty$ and $\|u\| =
\max(\|u\|_{L^\infty}, \|u'\|_{L^\infty})$ for $p = \infty$, is equivalent to the norm of the
source:
$$\|u\| \le \|u\|_{W^{1,p}} \le 2 \|u\| \quad \text{for all } u \in W^{1,p}(I).$$

The formula for the norm of the type is `SobolevIntervalLp.norm_eq_sum`. -/
theorem sobolevNorm_equiv (u : SobolevIntervalLp 1 p I) :
    ‖u‖ ≤ sobolevNorm u ∧ sobolevNorm u ≤ 2 * ‖u‖ := by
  refine ⟨(SobolevIntervalLp.norm_le_sum_norm_deriv u).trans_eq ?_, ?_⟩
  · rw [Fin.sum_univ_two]; rfl
  · have h0 := SobolevIntervalLp.norm_deriv_le u 0
    have h1 := SobolevIntervalLp.norm_deriv_le u 1
    unfold sobolevNorm
    linarith

/-- Let $I \subseteq \mathbb{R}$ be open. For $p = 1$ the norm of the type and the norm of Section
8.2 of [brezis2011functional] agree: $\|u\| = \|u\|_{L^1} + \|u'\|_{L^1}$ for every
$u \in W^{1,1}(I)$. -/
theorem sobolevNorm_eq_norm_of_one (u : SobolevIntervalLp 1 1 I) : sobolevNorm u = ‖u‖ := by
  rw [SobolevIntervalLp.norm_eq_sum ENNReal.one_ne_top, Fin.sum_univ_two]
  simp only [ENNReal.toReal_one, Real.rpow_one, div_one]
  rfl

/-- **Section 8.2** of [brezis2011functional], notation, the scalar product of $H^1$. Let
$I \subseteq \mathbb{R}$ be open. For $u, v \in H^1(I)$, the scalar product of the type is
$$(u, v)_{H^1} = (u, v)_{L^2} + (u', v')_{L^2} = \int_I (u v + u' v').$$

The proof specializes `SobolevIntervalLp.inner_eq_integral`. -/
theorem inner_H1 (u v : SobolevIntervalLp 1 2 I) :
    ⟪u, v⟫_ℝ = ∫ x in (I : Set ℝ), (u.fn x * v.fn x + u.deriv 1 x * v.deriv 1 x) :=
  SobolevIntervalLp.inner_eq_integral u v

/-- **Section 8.2** of [brezis2011functional], notation, the norm of $H^1$. Let
$I \subseteq \mathbb{R}$ be open. For $u \in H^1(I)$,
$$\|u\|_{H^1}^2 = \|u\|_{L^2}^2 + \|u'\|_{L^2}^2.$$
So for $p = 2$ the norm of the type is the norm of $H^1(I)$ in the source, the norm of the
scalar product. -/
theorem norm_H1_sq (u : SobolevIntervalLp 1 2 I) :
    ‖u‖ ^ 2 = ‖u.deriv 0‖ ^ 2 + ‖u.deriv 1‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, SobolevIntervalLp.inner_eq, Fin.sum_univ_two,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]

/-! ### Proposition 8.1 -/

/-- **Proposition 8.1** of [brezis2011functional], the Banach space. Let $I \subseteq \mathbb{R}$ be
open and $1 \le p \le \infty$. Then $W^{1,p}(I)$ is complete, so it is a Banach space.

Completeness is the instance `SobolevMultiIndex.instCompleteSpace`. The source proves it from
the closedness of the weak derivative under limits in $L^p$, which is Remark 4. -/
theorem proposition_8_1_banach : CompleteSpace (SobolevIntervalLp 1 p I) := inferInstance

/-- **Proposition 8.1** of [brezis2011functional], reflexivity. Let $I \subseteq \mathbb{R}$ be open
and $1 < p < \infty$. Then $W^{1,p}(I)$ is reflexive.

The map $u \mapsto (u, u')$ embeds $W^{1,p}(I)$ isometrically as a closed subspace of the
reflexive space $L^p(I) \times L^p(I)$. The factors are reflexive by Theorem 4.10
(`Brezis.Chapter04.theorem_4_10`), and the closed subspace is reflexive by
`SobolevMultiIndex.instIsReflexive`. -/
theorem proposition_8_1_reflexive (hp1 : 1 < p) (hp : p ≠ ∞) :
    NormedSpace.IsReflexive ℝ (SobolevIntervalLp 1 p I) :=
  have : NormedSpace.IsReflexive ℝ (Lp ℝ p (volume.restrict (I : Set ℝ))) :=
    Brezis.Chapter04.theorem_4_10 hp1 hp
  inferInstance

/-- **Proposition 8.1** of [brezis2011functional], separability. Let $I \subseteq \mathbb{R}$ be
open and $1 \le p < \infty$. Then $W^{1,p}(I)$ is separable.

The factors $L^p(I)$ are separable by Theorem 4.13 (`Brezis.Chapter04.theorem_4_13`). The proof
uses `SobolevMultiIndex.instSecondCountableTopology`. -/
theorem proposition_8_1_separable (hp : p ≠ ∞) :
    TopologicalSpace.SeparableSpace (SobolevIntervalLp 1 p I) :=
  have : Fact (p ≠ ∞) := ⟨hp⟩
  have : SecondCountableTopology (SobolevIntervalLp 1 p I) :=
    SobolevMultiIndex.instSecondCountableTopology
  TopologicalSpace.SecondCountableTopology.to_separableSpace

/-- **Proposition 8.1** of [brezis2011functional], the Hilbert space $H^1$. Let
$I \subseteq \mathbb{R}$ be open. The norm of $H^1(I)$ is the norm of its scalar product,
$\|u\| = (u, u)_{H^1}^{1/2}$ for all $u \in H^1(I)$, and $H^1(I)$ is complete and separable. So
$H^1(I)$ is a separable Hilbert space.

Mathlib has no bundled class of Hilbert spaces. As in Chapter 5, a Hilbert space is a type with
the instances `InnerProductSpace ℝ H` and `CompleteSpace H`. -/
theorem proposition_8_1_hilbert :
    (∀ u : SobolevIntervalLp 1 2 I, ‖u‖ = √⟪u, u⟫_ℝ) ∧ CompleteSpace (SobolevIntervalLp 1 2 I) ∧
      TopologicalSpace.SeparableSpace (SobolevIntervalLp 1 2 I) :=
  ⟨fun u ↦ norm_eq_sqrt_real_inner u, inferInstance, proposition_8_1_separable ENNReal.ofNat_ne_top⟩

/-- **Proposition 8.1** of [brezis2011functional]. Let $I \subseteq \mathbb{R}$ be open and
$1 \le p \le \infty$. The space $W^{1,p}(I)$ is a Banach space. It is reflexive for
$1 < p < \infty$ and separable for $1 \le p < \infty$. The space $H^1(I)$ is a separable Hilbert
space: its norm is $\|u\| = (u, u)_{H^1}^{1/2}$, and it is complete and separable. -/
theorem proposition_8_1 :
    CompleteSpace (SobolevIntervalLp 1 p I) ∧
      (1 < p → p ≠ ∞ → NormedSpace.IsReflexive ℝ (SobolevIntervalLp 1 p I)) ∧
      (p ≠ ∞ → TopologicalSpace.SeparableSpace (SobolevIntervalLp 1 p I)) ∧
      ((∀ u : SobolevIntervalLp 1 2 I, ‖u‖ = √⟪u, u⟫_ℝ) ∧
        CompleteSpace (SobolevIntervalLp 1 2 I) ∧
        TopologicalSpace.SeparableSpace (SobolevIntervalLp 1 2 I)) :=
  ⟨proposition_8_1_banach, proposition_8_1_reflexive, proposition_8_1_separable,
    proposition_8_1_hilbert⟩

/-! ### Remark 4 -/

/-- **Remark 4** in Chapter 8 of [brezis2011functional], first part. Let $I \subseteq \mathbb{R}$ be
open and $1 \le p \le \infty$. Let $(u_n)$ be a sequence in $W^{1,p}(I)$, and let
$v, w \in L^p(I)$ with $u_n \to v$ and $u_n' \to w$ in $L^p(I)$. Then $v \in W^{1,p}(I)$.
Moreover there is $\bar v \in W^{1,p}(I)$ whose function is $v$ and whose derivative is $w$,
almost everywhere on $I$, and $u_n \to \bar v$ in $W^{1,p}(I)$.

The proof specializes `hasWeakDerivOn_of_tendsto_eLpNorm` and
`SobolevIntervalLp.tendsto_of_tendsto_deriv`. -/
theorem remark_8_4_a {u : ℕ → SobolevIntervalLp 1 p I} {v w : ℝ → ℝ}
    (hv : MemLp v p (volume.restrict I)) (hw : MemLp w p (volume.restrict I))
    (hlv : Tendsto (fun n ↦ eLpNorm ((u n).fn - v) p (volume.restrict I)) atTop (𝓝 0))
    (hlw : Tendsto (fun n ↦ eLpNorm (⇑((u n).deriv 1) - w) p (volume.restrict I)) atTop (𝓝 0)) :
    MemSobolevSpace p I v ∧ ∃ v' : SobolevIntervalLp 1 p I,
      v'.fn =ᵐ[volume.restrict I] v ∧ ⇑(v'.deriv 1) =ᵐ[volume.restrict I] w ∧
        Tendsto u atTop (𝓝 v') := by
  have hweak : HasWeakDerivOn v w I :=
    hasWeakDerivOn_of_tendsto_eLpNorm (fun n ↦ (u n).hasWeakDerivOn_fn) hv hw hlv hlw
  refine ⟨memSobolevSpace_iff_memSobolevIntervalLp.2
    (memSobolevIntervalLp_one_iff.2 ⟨hv, w, hweak, hw⟩), ?_⟩
  let v' : SobolevIntervalLp 1 p I := SobolevIntervalLp.mk ![hv.toLp v, hw.toLp w] fun j ↦ by
    fin_cases j
    · exact HasWeakIteratedLineDerivOn.of_length_eq_zero rfl _
        ((Lp.memLp _).locallyIntegrableOn (Ω := I) Fact.out)
    · exact hweak.congr_ae hv.coeFn_toLp.symm hw.coeFn_toLp.symm
  refine ⟨v', hv.coeFn_toLp, hw.coeFn_toLp, SobolevIntervalLp.tendsto_of_tendsto_deriv fun j ↦ ?_⟩
  fin_cases j
  · exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm (fun n ↦ (u n).deriv 0) v hv).2 hlv
  · exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm (fun n ↦ (u n).deriv 1) w hw).2 hlw

/-- **Remark 4** in Chapter 8 of [brezis2011functional], second part. Let $I \subseteq \mathbb{R}$
be open and $1 < p \le \infty$. Let $(u_n)$ be a sequence in $W^{1,p}(I)$ with
$\|u_n'\|_{L^p} \le M$ for all $n$, and let $v \in L^p(I)$ with $u_n \to v$ in $L^p(I)$. Then
$v \in W^{1,p}(I)$.

The source refers to Exercise 8.2. The proof specializes
`SobolevIntervalLp.memSobolevIntervalLp_of_tendsto_of_bounded_deriv`: the bound of Proposition
8.3(ii) passes to the limit. -/
theorem remark_8_4_b (hp : 1 < p) {u : ℕ → SobolevIntervalLp 1 p I} {M : ℝ}
    (hM : ∀ n, ‖(u n).deriv 1‖ ≤ M) {v : ℝ → ℝ} (hv : MemLp v p (volume.restrict I))
    (hlv : Tendsto (fun n ↦ eLpNorm ((u n).fn - v) p (volume.restrict I)) atTop (𝓝 0)) :
    MemSobolevSpace p I v :=
  have := ENNReal.holderConjugate_sub_inv_inv (p := p)
  memSobolevSpace_iff_memSobolevIntervalLp.2
    (SobolevIntervalLp.memSobolevIntervalLp_of_tendsto_of_bounded_deriv
      ((ENNReal.HolderConjugate.lt_top_iff_one_lt (1 - p⁻¹)⁻¹ p).2 hp).ne hM hv hlv)

/-- **Remark 4** in Chapter 8 of [brezis2011functional]. Let $I \subseteq \mathbb{R}$ be open and
$1 \le p \le \infty$, let $(u_n)$ be a sequence in $W^{1,p}(I)$, and let $v \in L^p(I)$ with
$u_n \to v$ in $L^p(I)$. First, if $u_n' \to w$ in $L^p(I)$ for some $w \in L^p(I)$, then
$v \in W^{1,p}(I)$, and $u_n \to \bar v$ in $W^{1,p}(I)$ for some $\bar v \in W^{1,p}(I)$ whose
function is $v$ almost everywhere on $I$. Second, if $1 < p$ and $\|u_n'\|_{L^p} \le M$ for all
$n$, then $v \in W^{1,p}(I)$. -/
theorem remark_8_4 {u : ℕ → SobolevIntervalLp 1 p I} {v : ℝ → ℝ}
    (hv : MemLp v p (volume.restrict I))
    (hlv : Tendsto (fun n ↦ eLpNorm ((u n).fn - v) p (volume.restrict I)) atTop (𝓝 0)) :
    (∀ w : ℝ → ℝ, MemLp w p (volume.restrict I) →
      Tendsto (fun n ↦ eLpNorm (⇑((u n).deriv 1) - w) p (volume.restrict I)) atTop (𝓝 0) →
      MemSobolevSpace p I v ∧ ∃ v' : SobolevIntervalLp 1 p I,
        v'.fn =ᵐ[volume.restrict I] v ∧ Tendsto u atTop (𝓝 v')) ∧
    (1 < p → ∀ M : ℝ, (∀ n, ‖(u n).deriv 1‖ ≤ M) → MemSobolevSpace p I v) :=
  ⟨fun _ hw hlw ↦
    let ⟨h₁, v', hv', _, hlim⟩ := remark_8_4_a hv hw hlv hlw
    ⟨h₁, v', hv', hlim⟩,
    fun hp _ hM ↦ remark_8_4_b hp hM hv hlv⟩

/-! ### Theorem 8.2 and its lemmas -/

/-- **Theorem 8.2** of [brezis2011functional]. Let $I$ be an open interval, bounded or unbounded,
let $1 \le p \le \infty$, and let $u \in W^{1,p}(I)$. Then there is a function $\tilde u$,
continuous on $\bar I$, with $u = \tilde u$ almost everywhere on $I$ and
$$\tilde u(x) - \tilde u(y) = \int_y^x u'(t) \, dt \quad \text{for all } x, y \in \bar I.$$

The proof specializes `SobolevIntervalLp.exists_continuousOn_closure_ae_eq`. The canonical
choice of $\tilde u$, which the source writes $u(x)$ from here on, is `SobolevIntervalLp.rep u`. -/
theorem theorem_8_2 (hI : (I : Set ℝ).OrdConnected) (u : SobolevIntervalLp 1 p I) :
    ∃ ũ : ℝ → ℝ, ContinuousOn ũ (closure (I : Set ℝ)) ∧ u.fn =ᵐ[volume.restrict I] ũ ∧
      ∀ x ∈ closure (I : Set ℝ), ∀ y ∈ closure (I : Set ℝ),
        ũ x - ũ y = ∫ t in y..x, u.deriv 1 t :=
  let ⟨g, hg, hu, h⟩ := SobolevIntervalLp.exists_continuousOn_closure_ae_eq hI u
  ⟨g, hg, hu, fun x hx y hy ↦ h y hy x hx⟩

/-- **Remark 5** in Chapter 8 of [brezis2011functional], first sentence. Let
$I \subseteq \mathbb{R}$ be open and $1 \le p \le \infty$. If $u \in W^{1,p}(I)$ and $v = u$
almost everywhere on $I$, then $v \in W^{1,p}(I)$. -/
theorem remark_8_5_congr {u v : ℝ → ℝ} (hu : MemSobolevSpace p I u)
    (hvu : v =ᵐ[volume.restrict I] u) : MemSobolevSpace p I v :=
  memSobolevSpace_iff_memSobolevIntervalLp.2
    ((memSobolevSpace_iff_memSobolevIntervalLp.1 hu).congr_ae hvu.symm)

/-- **Remark 5** in Chapter 8 of [brezis2011functional], second sentence. Let $I$ be an open
interval, $1 \le p \le \infty$ and $u \in W^{1,p}(I)$. If $g_1$ and $g_2$ are continuous on
$\bar I$ and both equal $u$ almost everywhere on $I$, then $g_1 = g_2$ on $\bar I$. With Theorem
8.2, $u$ has exactly one continuous representative on $\bar I$.

The proof specializes `SobolevIntervalLp.rep_eq_of_continuousOn`. -/
theorem remark_8_5_unique (hI : (I : Set ℝ).OrdConnected) (u : SobolevIntervalLp 1 p I)
    {g₁ g₂ : ℝ → ℝ} (hg₁ : ContinuousOn g₁ (closure (I : Set ℝ)))
    (hg₂ : ContinuousOn g₂ (closure (I : Set ℝ))) (hu₁ : u.fn =ᵐ[volume.restrict I] g₁)
    (hu₂ : u.fn =ᵐ[volume.restrict I] g₂) : EqOn g₁ g₂ (closure (I : Set ℝ)) := fun _ hx ↦
  (SobolevIntervalLp.rep_eq_of_continuousOn hI u hg₁ hu₁ hx).symm.trans
    (SobolevIntervalLp.rep_eq_of_continuousOn hI u hg₂ hu₂ hx)

/-- **Remark 5** in Chapter 8 of [brezis2011functional]. Let $I$ be an open interval and
$1 \le p \le \infty$. If $u \in W^{1,p}(I)$ and $v = u$ almost everywhere on $I$, then
$v \in W^{1,p}(I)$. Every $u \in W^{1,p}(I)$ has at most one continuous representative on
$\bar I$: two functions continuous on $\bar I$ that equal $u$ almost everywhere on $I$ agree on
$\bar I$. -/
theorem remark_8_5 (hI : (I : Set ℝ).OrdConnected) :
    (∀ u v : ℝ → ℝ, MemSobolevSpace p I u → v =ᵐ[volume.restrict I] u → MemSobolevSpace p I v) ∧
    ∀ (u : SobolevIntervalLp 1 p I) (g₁ g₂ : ℝ → ℝ), ContinuousOn g₁ (closure (I : Set ℝ)) →
      ContinuousOn g₂ (closure (I : Set ℝ)) → u.fn =ᵐ[volume.restrict I] g₁ →
      u.fn =ᵐ[volume.restrict I] g₂ → EqOn g₁ g₂ (closure (I : Set ℝ)) :=
  ⟨fun _ _ hu hvu ↦ remark_8_5_congr hu hvu,
    fun u _ _ hg₁ hg₂ hu₁ hu₂ ↦ remark_8_5_unique hI u hg₁ hg₂ hu₁ hu₂⟩

omit [Fact (1 ≤ p)] in
/-- **Remark 6** in Chapter 8 of [brezis2011functional]. Let $I$ be an open interval and
$u \in W^{1,p}(I)$. Suppose that $u' = g$ almost everywhere on $I$ for a function $g$ continuous
on $\bar I$. Then $\tilde u \in C^1(\bar I)$, and at every $x \in \bar I$ the function
$\tilde u$ has the derivative $g(x)$ within $\bar I$.

Here $\tilde u$ is `SobolevIntervalLp.rep u`. The statement does not need $p \ge 1$. The proof
specializes `SobolevIntervalLp.contDiffOn_rep_of_continuousOn_deriv`. -/
theorem remark_8_6 (hI : (I : Set ℝ).OrdConnected) (u : SobolevIntervalLp 1 p I) {g : ℝ → ℝ}
    (hg : ContinuousOn g (closure (I : Set ℝ))) (hu : ⇑(u.deriv 1) =ᵐ[volume.restrict I] g) :
    ContDiffOn ℝ 1 u.rep (closure (I : Set ℝ)) ∧
      ∀ x ∈ closure (I : Set ℝ), HasDerivWithinAt u.rep (g x) (closure (I : Set ℝ)) x :=
  SobolevIntervalLp.contDiffOn_rep_of_continuousOn_deriv hI u hg hu

/-- **Lemma 8.1** of [brezis2011functional] (du Bois-Reymond). Let $I$ be an open interval and let
$f \in L^1_{\mathrm{loc}}(I)$ with
$$\int_I f \varphi' = 0 \quad \text{for all } \varphi \in C_c^\infty(I).$$
Then there is a constant $C$ with $f = C$ almost everywhere on $I$.

The proof specializes `HasWeakDerivOn.exists_ae_eq_const`. -/
theorem lemma_8_1 (hI : (I : Set ℝ).OrdConnected) {f : ℝ → ℝ} (hf : LocallyIntegrableOn f I)
    (h : ∀ φ : 𝓓(I, ℝ), ∫ x in (I : Set ℝ), f x * deriv φ x = 0) :
    ∃ C : ℝ, f =ᵐ[volume.restrict I] fun _ ↦ C := by
  refine HasWeakDerivOn.exists_ae_eq_const hI (hasWeakDerivOn_iff.2
    ⟨hf, (locallyIntegrable_const 0).locallyIntegrableOn _, fun φ ↦ ?_⟩)
  simp only [Pi.zero_apply, mul_zero, integral_zero, neg_zero]
  have := h φ
  simp only [mul_comm] at this ⊢
  exact this

/-- **Lemma 8.2** of [brezis2011functional]. Let $I$ be an open interval,
$g \in L^1_{\mathrm{loc}}(I)$ and $y_0 \in I$, and set $v(x) = \int_{y_0}^x g(t) \, dt$. Then
$v$ is continuous on $I$ and
$$\int_I v \varphi' = -\int_I g \varphi \quad \text{for all } \varphi \in C_c^\infty(I).$$

The proof specializes `MeasureTheory.LocallyIntegrableOn.hasWeakDerivOn_integral`, which uses
integration by parts for absolutely continuous functions instead of the Fubini argument of the
source, and `MeasureTheory.LocallyIntegrableOn.continuousOn_integral`. -/
theorem lemma_8_2 (hI : (I : Set ℝ).OrdConnected) {g : ℝ → ℝ} (hg : LocallyIntegrableOn g I)
    {y₀ : ℝ} (hy₀ : y₀ ∈ I) :
    ContinuousOn (fun x ↦ ∫ t in y₀..x, g t) I ∧ ∀ φ : 𝓓(I, ℝ),
      ∫ x in (I : Set ℝ), (∫ t in y₀..x, g t) * deriv φ x
        = -∫ x in (I : Set ℝ), g x * φ x := by
  have h1 := hg.continuousOn_integral hI hy₀ 0
  have h2 := hg.hasWeakDerivOn_integral hI hy₀ 0
  simp only [zero_add] at h1 h2
  refine ⟨h1, fun φ ↦ ?_⟩
  have := h2.integral_deriv_mul φ
  simp only [mul_comm] at this ⊢
  exact this

/-- **Remark 7** in Chapter 8 of [brezis2011functional]. Let $I$ be an open interval,
$1 \le p \le \infty$, $g \in L^p(I)$ and $y_0 \in I$, and set $v(x) = \int_{y_0}^x g(t) \, dt$.
If $v \in L^p(I)$, then $v \in W^{1,p}(I)$.

The proof specializes `memSobolevIntervalLp_integral`. -/
theorem remark_8_7 (hI : (I : Set ℝ).OrdConnected) {g : ℝ → ℝ} (hg : MemLp g p (volume.restrict I))
    {y₀ : ℝ} (hy₀ : y₀ ∈ I) (hv : MemLp (fun x ↦ ∫ t in y₀..x, g t) p (volume.restrict I)) :
    MemSobolevSpace p I fun x ↦ ∫ t in y₀..x, g t := by
  have := (memSobolevIntervalLp_integral hI hg hy₀ (c := 0) (by simpa only [zero_add] using hv)).1
  simp only [zero_add] at this
  exact memSobolevSpace_iff_memSobolevIntervalLp.2 this

/-- **Remark 7** in Chapter 8 of [brezis2011functional], the bounded case. Let $a < b$,
$1 \le p \le \infty$, $g \in L^p((a, b))$ and $y_0 \in (a, b)$. Then
$v(x) = \int_{y_0}^x g(t) \, dt$ belongs to $W^{1,p}((a, b))$.

The function $v$ is continuous on $[a, b]$, so it lies in $L^p((a, b))$, and Remark 7 applies. -/
theorem remark_8_7_of_bounded {a b : ℝ} (hab : a < b) {g : ℝ → ℝ}
    (hg : MemLp g p (volume.restrict (Ioo a b))) {y₀ : ℝ} (hy₀ : y₀ ∈ Ioo a b) :
    MemSobolevSpace p (Opens.Ioo a b) fun x ↦ ∫ t in y₀..x, g t := by
  have hI := SobolevIntervalLp.ordConnected_coe_Ioo a b
  have hcl := SobolevIntervalLp.closure_coe_Ioo hab
  refine remark_8_7 hI hg hy₀ ?_
  have hcont : ContinuousOn (fun x ↦ 0 + ∫ t in y₀..x, g t) (Icc a b) :=
    continuousOn_integral_of_intervalIntegrable (s := Icc a b) (Ioo_subset_Icc_self hy₀)
      (fun x hx y hy ↦ hg.intervalIntegrable_of_mem_closure hI (I := Opens.Ioo a b)
        (hcl ▸ hx) (hcl ▸ hy)) 0
  simp only [zero_add] at hcont
  exact hcont.memLp_top_restrict_Ioo.mono_exponent le_top

/-! ### Propositions 8.3–8.5 -/

/-- **Proposition 8.3** of [brezis2011functional], the implication (i) $\Rightarrow$ (ii) with an
explicit constant. Let $I \subseteq \mathbb{R}$ be open, $1 \le p \le \infty$ with conjugate
exponent $p'$, and $u \in W^{1,p}(I)$. Then
$$\left| \int_I u \varphi' \right| \le \|u'\|_{L^p(I)} \|\varphi\|_{L^{p'}(I)} \quad \text{for
  all } \varphi \in C_c^\infty(I).$$

The statement includes $p = 1$, as Remark 8 says. The proof specializes
`SobolevIntervalLp.abs_integral_mul_deriv_le`. -/
theorem proposition_8_3_const {q : ℝ≥0∞} [p.HolderConjugate q] (u : SobolevIntervalLp 1 p I)
    (φ : 𝓓(I, ℝ)) :
    |∫ x in (I : Set ℝ), u.fn x * deriv φ x|
      ≤ ‖u.deriv 1‖ * (eLpNorm φ q (volume.restrict I)).toReal :=
  SobolevIntervalLp.abs_integral_mul_deriv_le u φ

/-- **Proposition 8.3** of [brezis2011functional]. Let $I \subseteq \mathbb{R}$ be open,
$1 < p \le \infty$ with conjugate exponent $p'$, and $u \in L^p(I)$. Then $u \in W^{1,p}(I)$ if
and only if there is a constant $C$ with
$$\left| \int_I u \varphi' \right| \le C \|\varphi\|_{L^{p'}(I)} \quad \text{for all } \varphi
  \in C_c^\infty(I).$$

The proof specializes `memSobolevIntervalLp_iff_forall_abs_integral_mul_deriv_le`. The converse
uses the Riesz representation theorem, as in the source. -/
theorem proposition_8_3 {q : ℝ≥0∞} [p.HolderConjugate q] (hp : 1 < p) {u : ℝ → ℝ}
    (hu : MemLp u p (volume.restrict I)) :
    MemSobolevSpace p I u ↔ ∃ C : ℝ, ∀ φ : 𝓓(I, ℝ),
      |∫ x in (I : Set ℝ), u x * deriv φ x| ≤ C * (eLpNorm φ q (volume.restrict I)).toReal :=
  memSobolevSpace_iff_memSobolevIntervalLp.trans
    (memSobolevIntervalLp_iff_forall_abs_integral_mul_deriv_le
      ((ENNReal.HolderConjugate.lt_top_iff_one_lt q p).2 hp).ne hu)

/-- **Remark 8** in Chapter 8 of [brezis2011functional], the case $p = 1$. Let
$I \subseteq \mathbb{R}$ be open and $u \in W^{1,1}(I)$. Then
$$\left| \int_I u \varphi' \right| \le \|u'\|_{L^1(I)} \|\varphi\|_{L^\infty(I)} \quad \text{for
  all } \varphi \in C_c^\infty(I).$$
So the implication (i) $\Rightarrow$ (ii) of Proposition 8.3 holds for $p = 1$, with
$p' = \infty$. -/
theorem remark_8_8_one (u : SobolevIntervalLp 1 1 I) (φ : 𝓓(I, ℝ)) :
    |∫ x in (I : Set ℝ), u.fn x * deriv φ x|
      ≤ ‖u.deriv 1‖ * (eLpNorm φ ∞ (volume.restrict I)).toReal :=
  SobolevIntervalLp.abs_integral_mul_deriv_le u φ

/-- **Remark 8** in Chapter 8 of [brezis2011functional], absolutely continuous functions. Let
$a < b$ and $u : \mathbb{R} \to \mathbb{R}$. Then $u \in W^{1,1}((a, b))$ if and only if $u$
equals, almost everywhere on $(a, b)$, a function that is absolutely continuous on $[a, b]$.

The source calls absolute continuity property (AC). It is Mathlib's
`AbsolutelyContinuousOnInterval`. The proof specializes
`memSobolevIntervalLp_one_one_iff_absolutelyContinuousOnInterval`. -/
theorem remark_8_8_absolutelyContinuous {a b : ℝ} (hab : a < b) {u : ℝ → ℝ} :
    MemSobolevSpace 1 (Opens.Ioo a b) u ↔
      ∃ g : ℝ → ℝ, AbsolutelyContinuousOnInterval g a b ∧ u =ᵐ[volume.restrict (Ioo a b)] g :=
  memSobolevSpace_iff_memSobolevIntervalLp.trans
    (memSobolevIntervalLp_one_one_iff_absolutelyContinuousOnInterval hab)

/-- **Remark 8** in Chapter 8 of [brezis2011functional], the formalized parts. Let
$I \subseteq \mathbb{R}$ be open. First, for every $u \in W^{1,1}(I)$ and
$\varphi \in C_c^\infty(I)$,
$$\left| \int_I u \varphi' \right| \le \|u'\|_{L^1(I)} \|\varphi\|_{L^\infty(I)}.$$
Second, for all $a < b$, a function $u$ lies in $W^{1,1}((a, b))$ if and only if it equals,
almost everywhere on $(a, b)$, a function that is absolutely continuous on $[a, b]$.

The failure of the converse of (i) $\Rightarrow$ (ii) of Proposition 8.3 for $p = 1$, and the
characterizations (a)–(c) of the functions of bounded variation, are not formalized. -/
theorem remark_8_8 :
    (∀ (u : SobolevIntervalLp 1 1 I) (φ : 𝓓(I, ℝ)), |∫ x in (I : Set ℝ), u.fn x * deriv φ x|
      ≤ ‖u.deriv 1‖ * (eLpNorm φ ∞ (volume.restrict I)).toReal) ∧
    ∀ a b : ℝ, a < b → ∀ u : ℝ → ℝ, MemSobolevSpace 1 (Opens.Ioo a b) u ↔
      ∃ g : ℝ → ℝ, AbsolutelyContinuousOnInterval g a b ∧ u =ᵐ[volume.restrict (Ioo a b)] g :=
  ⟨remark_8_8_one, fun _ _ hab _ ↦ remark_8_8_absolutelyContinuous hab⟩

/-- **Proposition 8.4** of [brezis2011functional]. Let $I$ be an open interval and
$u \in L^\infty(I)$. Then $u \in W^{1,\infty}(I)$ if and only if there is a constant $C$ with
$$|u(x) - u(y)| \le C |x - y| \quad \text{for almost every } x, y \in I.$$

In the Lean statement, "for almost every $x$, for almost every $y$" is written with two nested
quantifiers `∀ᵐ`. The proof specializes `memSobolevIntervalLp_top_iff_lipschitz`, through the
calculus of absolutely continuous functions instead of Proposition 8.3 as in the source. -/
theorem proposition_8_4 (hI : (I : Set ℝ).OrdConnected) {u : ℝ → ℝ}
    (hu : MemLp u ∞ (volume.restrict I)) :
    MemSobolevSpace ∞ I u ↔
      ∃ C : ℝ, ∀ᵐ x ∂(volume.restrict I), ∀ᵐ y ∂(volume.restrict I), |u x - u y| ≤ C * |x - y| :=
  memSobolevSpace_iff_memSobolevIntervalLp.trans (memSobolevIntervalLp_top_iff_lipschitz hI hu)

/-- **Proposition 8.5** of [brezis2011functional], the implication (i) $\Rightarrow$ (ii) with an
explicit constant. Let $1 \le p \le \infty$ and $u \in W^{1,p}(\mathbb{R})$, and let
$(\tau_h u)(x) = u(x + h)$. Then
$$\|\tau_h u - u\|_{L^p(\mathbb{R})} \le |h| \, \|u'\|_{L^p(\mathbb{R})} \quad \text{for all } h
  \in \mathbb{R}.$$

Here $u$ is its continuous representative `SobolevIntervalLp.rep u`. The statement includes
$p = 1$. The proof specializes `SobolevIntervalLp.eLpNorm_translate_sub_le`. -/
theorem proposition_8_5_const (u : SobolevIntervalLp 1 p ⊤) (h : ℝ) :
    eLpNorm (fun x ↦ u.rep (x + h) - u.rep x) p volume
      ≤ ENNReal.ofReal |h| * eLpNorm (u.deriv 1) p volume :=
  SobolevIntervalLp.eLpNorm_translate_sub_le u h

/-- **Proposition 8.5** of [brezis2011functional]. Let $1 < p < \infty$ and $u \in L^p(\mathbb{R})$,
and let $(\tau_h u)(x) = u(x + h)$. Then $u \in W^{1,p}(\mathbb{R})$ if and only if there is a
constant $C$ with
$$\|\tau_h u - u\|_{L^p(\mathbb{R})} \le C |h| \quad \text{for all } h \in \mathbb{R}.$$

The hypothesis $p < \infty$ is the one of the source; the proof does not use it. The converse
goes through Proposition 8.3, which holds for $p = \infty$ too. The proof specializes
`memSobolevIntervalLp_of_eLpNorm_translate_sub_le` and
`SobolevIntervalLp.eLpNorm_translate_sub_le`. -/
theorem proposition_8_5 (hp1 : 1 < p) (_hp : p ≠ ∞) {u : ℝ → ℝ} (hu : MemLp u p volume) :
    MemSobolevSpace p ⊤ u ↔
      ∃ C : ℝ, ∀ h : ℝ, eLpNorm (fun x ↦ u (x + h) - u x) p volume ≤ ENNReal.ofReal (C * |h|) := by
  have := ENNReal.holderConjugate_sub_inv_inv (p := p)
  have hq : (1 - p⁻¹)⁻¹ ≠ ⊤ := ((ENNReal.HolderConjugate.lt_top_iff_one_lt (1 - p⁻¹)⁻¹ p).2 hp1).ne
  have hu' : MemLp u p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) := by
    rwa [Opens.coe_top, Measure.restrict_univ]
  rw [memSobolevSpace_iff_memSobolevIntervalLp]
  constructor
  · intro h
    obtain ⟨v, hv⟩ := h.exists_sobolevIntervalLp
    have hne : eLpNorm (⇑(v.deriv 1)) p volume ≠ ⊤ :=
      (SobolevIntervalLp.memLp_restrict_top_iff.1 (Lp.memLp (v.deriv 1))).eLpNorm_ne_top
    refine ⟨(eLpNorm (⇑(v.deriv 1)) p volume).toReal, fun t ↦ ?_⟩
    have hv' : u =ᵐ[volume] v.rep :=
      (SobolevIntervalLp.eventuallyEq_restrict_top_iff.1 hv).symm.trans
        (SobolevIntervalLp.eventuallyEq_restrict_top_iff.1
          (SobolevIntervalLp.fn_ae_eq_rep Opens.ordConnected_top v))
    have h1 : (fun x ↦ u (x + t)) =ᵐ[volume] fun x ↦ v.rep (x + t) :=
      (measurePreserving_add_right volume t).quasiMeasurePreserving.ae_eq_comp hv'
    have h2 : (fun x ↦ u (x + t) - u x) =ᵐ[volume] fun x ↦ v.rep (x + t) - v.rep x :=
      h1.sub hv'
    rw [eLpNorm_congr_ae h2, ENNReal.ofReal_mul ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal hne, mul_comm]
    exact proposition_8_5_const v t
  · rintro ⟨C, hC⟩
    exact (memSobolevIntervalLp_of_eLpNorm_translate_sub_le hq hu hC).1

/-! ### Theorem 8.6, the extension operator -/

/-- **Theorem 8.6** of [brezis2011functional] (extension operator), with the constants of
footnote 6. Let $I$ be a nonempty open interval and $1 \le p \le \infty$. There is a bounded
linear operator $P : W^{1,p}(I) \to W^{1,p}(\mathbb{R})$ such that for all $u \in W^{1,p}(I)$:
(i) $Pu = u$ almost everywhere on $I$; (ii) $\|Pu\|_{L^p(\mathbb{R})} \le 4 \|u\|_{L^p(I)}$;
(iii) $\|Pu\|_{W^{1,p}(\mathbb{R})} \le 4 (1 + 1/|I|) \|u\|_{W^{1,p}(I)}$, in the norm of the
source, where $1/|I| = 0$ when $|I| = \infty$.

The length $|I|$ is `(volume (I : Set ℝ)).toReal`, which is $0$ for an unbounded interval, and
then its inverse is $0$ by the convention $0^{-1} = 0$. The operator is
`SobolevIntervalLp.extensionCLM`. -/
theorem theorem_8_6_const (hI : (I : Set ℝ).OrdConnected) (hne : (I : Set ℝ).Nonempty) :
    ∃ P : SobolevIntervalLp 1 p I →L[ℝ] SobolevIntervalLp 1 p ⊤,
      (∀ u, (P u).fn =ᵐ[volume.restrict I] u.fn) ∧
      (∀ u, ‖(P u).deriv 0‖ ≤ 4 * ‖u.deriv 0‖) ∧
      ∀ u, sobolevNorm (P u) ≤ 4 * (1 + (volume (I : Set ℝ)).toReal⁻¹) * sobolevNorm u := by
  refine ⟨SobolevIntervalLp.extensionCLM hI hne, SobolevIntervalLp.fn_extensionCLM hI hne,
    SobolevIntervalLp.norm_deriv_extensionCLM_zero_le hI hne, fun u ↦ ?_⟩
  have h0 := SobolevIntervalLp.norm_deriv_extensionCLM_zero_le hI hne u
  have h1 := SobolevIntervalLp.norm_deriv_extensionCLM_one_le hI hne u
  have hk : 0 ≤ (volume (I : Set ℝ)).toReal⁻¹ := by positivity
  have hn0 := norm_nonneg (u.deriv 0)
  have hn1 := norm_nonneg (u.deriv 1)
  unfold sobolevNorm
  nlinarith

/-- **Theorem 8.6** of [brezis2011functional] (extension operator). Let $I$ be a nonempty open
interval and $1 \le p \le \infty$. There are a bounded linear operator
$P : W^{1,p}(I) \to W^{1,p}(\mathbb{R})$, called an extension operator, and a constant $C$ such
that for all $u \in W^{1,p}(I)$: (i) $Pu|_I = u$; (ii)
$\|Pu\|_{L^p(\mathbb{R})} \le C \|u\|_{L^p(I)}$; (iii) $\|Pu\|_{W^{1,p}(\mathbb{R})} \le C
\|u\|_{W^{1,p}(I)}$.

The source says that $C$ depends only on $|I| \le \infty$. The value $C = 4 (1 + 1/|I|)$ is in
`Brezis.Chapter08.theorem_8_6_const`. The equality $Pu|_I = u$ holds almost everywhere on $I$,
and the norm in (iii) is the norm of the source. -/
theorem theorem_8_6 (hI : (I : Set ℝ).OrdConnected) (hne : (I : Set ℝ).Nonempty) :
    ∃ (P : SobolevIntervalLp 1 p I →L[ℝ] SobolevIntervalLp 1 p ⊤) (C : ℝ),
      (∀ u, (P u).fn =ᵐ[volume.restrict I] u.fn) ∧
      (∀ u, ‖(P u).deriv 0‖ ≤ C * ‖u.deriv 0‖) ∧
      ∀ u, sobolevNorm (P u) ≤ C * sobolevNorm u := by
  obtain ⟨P, h1, h2, h3⟩ := theorem_8_6_const (p := p) hI hne
  have hk : 0 ≤ (volume (I : Set ℝ)).toReal⁻¹ := by positivity
  refine ⟨P, 4 * (1 + (volume (I : Set ℝ)).toReal⁻¹), h1, fun u ↦ (h2 u).trans ?_, h3⟩
  have := norm_nonneg (u.deriv 0)
  nlinarith

/-- **Lemma 8.3** of [brezis2011functional]. Let $1 \le p \le \infty$ and $u \in W^{1,p}((0, 1))$,
and let $\eta \in C^\infty(\mathbb{R})$ with $\eta(x) = 0$ for $x > 3/4$. Let $\tilde u$ and
$\widetilde{u'}$ be the extensions of $u$ and $u'$ by $0$ to $(0, \infty)$. Then
$\eta \tilde u \in W^{1,p}((0, \infty))$ and $(\eta \tilde u)' = \eta' \tilde u + \eta
\widetilde{u'}$, that is,
$$\int_0^\infty \eta \tilde u \varphi' = -\int_0^\infty (\eta' \tilde u + \eta \widetilde{u'})
  \varphi \quad \text{for all } \varphi \in C_c^\infty((0, \infty)).$$

**Generalization.** The source also assumes $\eta(x) = 1$ for $x < 1/4$. The statement does not
need this condition.

Here $u$ is its continuous representative `SobolevIntervalLp.rep u`, and the extension by $0$ is
`Set.indicator` of $(0, 1)$. The proof specializes
`HasWeakDerivOn.indicator_mul_of_tsupport_inter_subset`. As in the source, it integrates by
parts against $\eta \varphi \in C_c^1((0, 1))$. -/
theorem lemma_8_3 (u : SobolevIntervalLp 1 p (Opens.Ioo 0 1)) {η : ℝ → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη0 : ∀ x, 3 / 4 < x → η x = 0) :
    MemSobolevSpace p (Opens.Ioi 0) ((Ioo 0 1).indicator fun x ↦ η x * u.rep x) ∧
      ∀ φ : 𝓓(Opens.Ioi 0, ℝ),
        ∫ x in Ioi (0 : ℝ), (Ioo 0 1).indicator (fun x ↦ η x * u.rep x) x * deriv φ x
          = -∫ x in Ioi (0 : ℝ),
              (Ioo 0 1).indicator (fun x ↦ deriv η x * u.rep x + η x * u.deriv 1 x) x * φ x := by
  have hI := SobolevIntervalLp.ordConnected_coe_Ioo 0 1
  have hIJ : Opens.Ioo 0 1 ≤ Opens.Ioi 0 := fun x hx ↦ hx.1
  have hsupp : tsupport η ∩ ((Opens.Ioi 0 : Opens ℝ) : Set ℝ) ⊆ (Opens.Ioo 0 1 : Opens ℝ) := by
    rintro x ⟨hx, hx0⟩
    have hle : x ≤ 3 / 4 := by
      by_contra hlt
      push Not at hlt
      have : x ∈ (Function.support η)ᶜ := fun h ↦ h (hη0 x hlt)
      have hcl : tsupport η ⊆ Iic (3 / 4) := by
        refine closure_minimal (fun y hy ↦ ?_) isClosed_Iic
        by_contra hy'
        exact hy (hη0 y (not_le.1 hy'))
      exact absurd (hcl hx) (not_le.2 hlt)
    exact ⟨hx0, by linarith⟩
  have hweak := (SobolevIntervalLp.hasWeakDerivOn_rep hI u).indicator_mul_of_tsupport_inter_subset
    hIJ hη hsupp
  have hηb : MemLp η ⊤ (volume.restrict (Ioo (0 : ℝ) 1)) :=
    hη.continuous.continuousOn.memLp_top_restrict_Ioo
  have hηb' : MemLp (deriv η) ⊤ (volume.restrict (Ioo (0 : ℝ) 1)) :=
    (hη.continuous_deriv (by simp)).continuousOn.memLp_top_restrict_Ioo
  have hrest : (volume.restrict (Ioi (0 : ℝ))).restrict (Ioo 0 1) = volume.restrict (Ioo 0 1) := by
    rw [Measure.restrict_restrict measurableSet_Ioo, inter_eq_left.2 Ioo_subset_Ioi_self]
  have hmem : ∀ {f : ℝ → ℝ}, MemLp f p (volume.restrict (Ioo (0 : ℝ) 1)) →
      MemLp ((Ioo (0 : ℝ) 1).indicator f) p (volume.restrict (Ioi 0)) := fun hf ↦ by
    rw [memLp_iff, eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Ioo.nullMeasurableSet, hrest]
    exact hf.eLpNorm_lt_top
  refine ⟨memSobolevSpace_iff_memSobolevIntervalLp.2 (memSobolevIntervalLp_one_iff.2
    ⟨hmem (hηb.fun_mul (SobolevIntervalLp.memLp_rep hI u)), _, hweak,
      hmem ((hηb'.fun_mul (SobolevIntervalLp.memLp_rep hI u)).add
        (hηb.fun_mul (SobolevIntervalLp.memLp_deriv u 1)))⟩), fun φ ↦ ?_⟩
  have := hweak.integral_deriv_mul φ
  simp only [mul_comm, Opens.coe_Ioi] at this ⊢
  exact this

/-! ### Theorem 8.7, density -/

/-- **Theorem 8.7** of [brezis2011functional] (density). Let $I$ be a nonempty open interval,
$1 \le p < \infty$ and $u \in W^{1,p}(I)$. Then there is a sequence $(u_n)$ in
$C_c^\infty(\mathbb{R})$ such that $u_n|_I \to u$ in $W^{1,p}(I)$.

The restrictions $u_n|_I$ are elements $v_n \in W^{1,p}(I)$ whose functions equal $u_n$ almost
everywhere on $I$. The proof specializes
`SobolevIntervalLp.exists_seq_contDiff_hasCompactSupport_tendsto`, through the extension
operator and the density theorem on $\mathbb{R}$. -/
theorem theorem_8_7 (hI : (I : Set ℝ).OrdConnected) (hne : (I : Set ℝ).Nonempty) (hp : p ≠ ∞)
    (u : SobolevIntervalLp 1 p I) :
    ∃ g : ℕ → ℝ → ℝ, (∀ n, ContDiff ℝ (⊤ : ℕ∞) (g n)) ∧ (∀ n, HasCompactSupport (g n)) ∧
      ∃ v : ℕ → SobolevIntervalLp 1 p I,
        (∀ n, (v n).fn =ᵐ[volume.restrict I] g n) ∧ Tendsto v atTop (𝓝 u) :=
  SobolevIntervalLp.exists_seq_contDiff_hasCompactSupport_tendsto hI hne hp u

/-- **Remark 9** in Chapter 8 of [brezis2011functional]. Let $a < b$ and $1 \le p \le \infty$. In
general $C_c^\infty(I)$ is not dense in $W^{1,p}(I)$: on $I = (a, b)$, the element
$u \in W^{1,p}(I)$ with $u = 1$ almost everywhere is not the limit in $W^{1,p}(I)$ of any
sequence of elements whose functions are in $C_c^\infty(I)$.

The element $u$ lies outside the space $W_0^{1,p}((a, b))$ of Section 8.3. The proof specializes
`SobolevIntervalLp.exists_not_mem_closure_testFunctions`. -/
theorem remark_8_9 {a b : ℝ} (hab : a < b) :
    ∃ u : SobolevIntervalLp 1 p (Opens.Ioo a b), (u.fn =ᵐ[volume.restrict (Ioo a b)] fun _ ↦ 1) ∧
      ¬ ∃ v : ℕ → SobolevIntervalLp 1 p (Opens.Ioo a b),
        (∀ n, ∃ φ : 𝓓(Opens.Ioo a b, ℝ), (v n).fn =ᵐ[volume.restrict (Ioo a b)] φ) ∧
          Tendsto v atTop (𝓝 u) := by
  obtain ⟨u, hu, hu0⟩ := SobolevIntervalLp.exists_not_mem_closure_testFunctions (p := p) hab
  refine ⟨u, hu, fun ⟨v, hv, hlim⟩ ↦ hu0 ?_⟩
  refine SobolevMultiIndexZero.isClosed.mem_of_tendsto hlim (Eventually.of_forall fun n ↦ ?_)
  obtain ⟨φ, hφ⟩ := hv n
  exact SobolevIntervalLpZero.mem_of_fn_ae_eq φ hφ

/-- **Lemma 8.4** of [brezis2011functional]. Let $\rho \in L^1(\mathbb{R})$, $1 \le p \le \infty$
and $v \in W^{1,p}(\mathbb{R})$. Then $\rho \star v \in W^{1,p}(\mathbb{R})$ and
$(\rho \star v)' = \rho \star v'$, that is,
$$\int_{\mathbb{R}} (\rho \star v) \varphi' = -\int_{\mathbb{R}} (\rho \star v') \varphi \quad
  \text{for all } \varphi \in C_c^\infty(\mathbb{R}).$$

The proof specializes `SobolevIntervalLp.hasWeakDerivOn_convolution` and
`SobolevIntervalLp.memSobolevIntervalLp_convolution`. -/
theorem lemma_8_4 (v : SobolevIntervalLp 1 p ⊤) {ρ : ℝ → ℝ} (hρ : Integrable ρ) :
    MemSobolevSpace p ⊤ (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ] v.fn) ∧
      ∀ φ : 𝓓((⊤ : Opens ℝ), ℝ),
        ∫ x in ((⊤ : Opens ℝ) : Set ℝ), (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ] v.fn) x * deriv φ x
          = -∫ x in ((⊤ : Opens ℝ) : Set ℝ),
              (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ] ⇑(v.deriv 1)) x * φ x := by
  refine ⟨memSobolevSpace_iff_memSobolevIntervalLp.2
    (SobolevIntervalLp.memSobolevIntervalLp_convolution v hρ), fun φ ↦ ?_⟩
  have := (SobolevIntervalLp.hasWeakDerivOn_convolution v hρ).integral_deriv_mul φ
  simp only [mul_comm] at this ⊢
  exact this

/-! ### Theorem 8.8, the Sobolev embedding -/

/-- The constant `SobolevIntervalLp.embeddingConst p I` $= \max(2, |I|^{-1/p} + |I|^{1 - 1/p})$ is
at most $\max(2, \max(1, |I|^{-1}) + \max(1, |I|))$, a function of $|I|$ alone, so the constant
of Theorem 8.8(5) can be chosen independently of $p$ (footnote 7). -/
private theorem embeddingConst_le (p : ℝ≥0∞) [Fact (1 ≤ p)] (I : Opens ℝ) :
    SobolevIntervalLp.embeddingConst p I
      ≤ max 2 (max 1 (volume (I : Set ℝ)).toReal⁻¹ + max 1 (volume (I : Set ℝ)).toReal) := by
  have hp1 : (1 : ℝ≥0∞) ≤ p := Fact.out
  have he0 : 0 ≤ p.toReal⁻¹ := by positivity
  have he1 : p.toReal⁻¹ ≤ 1 := by
    have := one_sub_toReal_inv_nonneg hp1
    linarith
  refine max_le_max_left 2 (add_le_add ?_ ?_)
  · rcases (ENNReal.toReal_nonneg (a := volume (I : Set ℝ))).eq_or_lt with h0 | hpos
    · rw [← h0]; exact (Real.zero_rpow_le_one _).trans (le_max_left _ _)
    rcases le_or_gt 1 (volume (I : Set ℝ)).toReal with h1 | h1
    · exact (Real.rpow_le_one_of_one_le_of_nonpos h1 (by linarith)).trans (le_max_left _ _)
    · refine le_trans ?_ (le_max_right _ _)
      have h := Real.rpow_le_rpow_of_exponent_ge hpos h1.le
        (show (-1 : ℝ) ≤ -p.toReal⁻¹ by linarith)
      rwa [Real.rpow_neg_one] at h
  · rcases (ENNReal.toReal_nonneg (a := volume (I : Set ℝ))).eq_or_lt with h0 | hpos
    · rw [← h0]; exact (Real.zero_rpow_le_one _).trans (le_max_left _ _)
    rcases le_or_gt 1 (volume (I : Set ℝ)).toReal with h1 | h1
    · refine le_trans ?_ (le_max_right _ _)
      conv_rhs => rw [← Real.rpow_one (volume (I : Set ℝ)).toReal]
      exact Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
    · exact (Real.rpow_le_one hpos.le h1.le (by linarith)).trans (le_max_left _ _)

/-- **Theorem 8.8** of [brezis2011functional], inequality (5). Let $I$ be an open interval. There is
a constant $C$ such that
$$\|u\|_{L^\infty(I)} \le C \|u\|_{W^{1,p}(I)} \quad \text{for all } 1 \le p \le \infty \text{
  and all } u \in W^{1,p}(I).$$
In other words, $W^{1,p}(I) \subseteq L^\infty(I)$ with continuous injection for all
$1 \le p \le \infty$.

The source says that $C$ depends only on $|I| \le \infty$. The norm on the right is the norm of
the source, `Brezis.Chapter08.sobolevNorm`. The proof specializes
`SobolevIntervalLp.eLpNorm_top_le`, whose constant `SobolevIntervalLp.embeddingConst p I` is
bounded uniformly in $p$ (footnote 7) by a function of $|I|$. -/
theorem theorem_8_8_a (hI : (I : Set ℝ).OrdConnected) :
    ∃ C : ℝ, ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (u : SobolevIntervalLp 1 p I),
      eLpNorm u.fn ∞ (volume.restrict I) ≤ ENNReal.ofReal (C * sobolevNorm u) := by
  refine ⟨max 2 (max 1 (volume (I : Set ℝ)).toReal⁻¹ + max 1 (volume (I : Set ℝ)).toReal),
    fun p _ u ↦ (SobolevIntervalLp.eLpNorm_top_le hI u).trans (ENNReal.ofReal_le_ofReal ?_)⟩
  exact mul_le_mul (embeddingConst_le p I) (sobolevNorm_equiv u).1 (norm_nonneg _)
    (le_trans zero_le_two (le_max_left _ _))

/-- **Theorem 8.8** of [brezis2011functional], statement (6). Let $a < b$ and $1 < p \le \infty$.
The injection $W^{1,p}((a, b)) \to C([a, b])$, $u \mapsto \tilde u$, is a compact operator.

The injection is `SobolevIntervalLp.toContinuousMap`, which maps $u$ to its continuous
representative on $[a, b]$. The proof specializes
`SobolevIntervalLp.isCompactOperator_toContinuousMap`. It uses the Ascoli–Arzelà theorem, since
the unit ball of $W^{1,p}((a, b))$ is uniformly Hölder continuous. -/
theorem theorem_8_8_b {a b : ℝ} (hab : a < b) (hp : 1 < p) :
    IsCompactOperator (SobolevIntervalLp.toContinuousMap (p := p) hab) :=
  SobolevIntervalLp.isCompactOperator_toContinuousMap hab hp

/-- **Theorem 8.8** of [brezis2011functional], statement (7). Let $a < b$ and $1 \le q < \infty$.
The injection $W^{1,1}((a, b)) \to L^q((a, b))$ is a compact operator.

The injection is `SobolevIntervalLp.toLpOfBounded 1 hab q`. The proof specializes
`SobolevIntervalLp.isCompactOperator_toLp_one`, through the extension operator and the
Kolmogorov–M. Riesz–Fréchet theorem. -/
theorem theorem_8_8_c {a b : ℝ} (hab : a < b) {q : ℝ≥0∞} [Fact (1 ≤ q)] (hq : q ≠ ∞) :
    IsCompactOperator (SobolevIntervalLp.toLpOfBounded 1 hab q) :=
  SobolevIntervalLp.isCompactOperator_toLp_one hab hq

/-- **Theorem 8.8** of [brezis2011functional]. Let $I$ be an open interval. Then: (5) there is a
constant $C$ with $\|u\|_{L^\infty(I)} \le C \|u\|_{W^{1,p}(I)}$ for all $1 \le p \le \infty$
and all $u \in W^{1,p}(I)$; (6) for $a < b$ and $1 < p \le \infty$, the injection
$W^{1,p}((a, b)) \to C([a, b])$ is compact; (7) for $a < b$ and $1 \le q < \infty$, the
injection $W^{1,1}((a, b)) \to L^q((a, b))$ is compact. -/
theorem theorem_8_8 (hI : (I : Set ℝ).OrdConnected) :
    (∃ C : ℝ, ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (u : SobolevIntervalLp 1 p I),
      eLpNorm u.fn ∞ (volume.restrict I) ≤ ENNReal.ofReal (C * sobolevNorm u)) ∧
    (∀ (a b : ℝ) (hab : a < b) (p : ℝ≥0∞) [Fact (1 ≤ p)], 1 < p →
      IsCompactOperator (SobolevIntervalLp.toContinuousMap (p := p) hab)) ∧
    ∀ (a b : ℝ) (hab : a < b) (q : ℝ≥0∞) [Fact (1 ≤ q)], q ≠ ∞ →
      IsCompactOperator (SobolevIntervalLp.toLpOfBounded 1 hab q) :=
  ⟨theorem_8_8_a hI, fun _ _ hab _ _ hp ↦ theorem_8_8_b hab hp,
    fun _ _ hab _ _ hq ↦ theorem_8_8_c hab hq⟩

/-! ### Remark 10: the two non-compactness claims -/

/-- For every $n$, there is an element of $W^{1,1}((0, 1))$ of norm at most $2$ whose continuous
representative is $x \mapsto x^n$ on $[0, 1]$. -/
private theorem exists_pow_sobolevIntervalLp (n : ℕ) :
    ∃ u : SobolevIntervalLp 1 1 (Opens.Ioo 0 1), ‖u‖ ≤ 2 ∧
      ∀ x ∈ Icc (0 : ℝ) 1, u.rep x = x ^ n := by
  have hI := SobolevIntervalLp.ordConnected_coe_Ioo (0 : ℝ) 1
  have hmem : MemSobolevIntervalLp (fun y : ℝ ↦ y ^ n) 1 1 (Opens.Ioo 0 1) ∧
      HasWeakDerivOn (fun y : ℝ ↦ y ^ n) (deriv fun y : ℝ ↦ y ^ n) (Opens.Ioo 0 1) :=
    memSobolevIntervalLp_of_contDiffOn_Icc (p := 1) (zero_lt_one' ℝ) (contDiff_id.pow n).contDiffOn
  obtain ⟨u, hu⟩ := hmem.1.exists_sobolevIntervalLp
  have hderiv : ∀ x : ℝ, deriv (fun y : ℝ ↦ y ^ n) x = n * x ^ (n - 1) := fun x ↦
    (hasDerivAt_pow n x).deriv
  have hu1 : ⇑(u.deriv 1) =ᵐ[volume.restrict ((Opens.Ioo (0 : ℝ) 1 : Opens ℝ) : Set ℝ)]
      fun x ↦ (n : ℝ) * x ^ (n - 1) := by
    filter_upwards [(ae_restrict_iff' measurableSet_Ioo).2
      ((u.hasWeakDerivOn_fn.congr_ae hu (EventuallyEq.refl _ _)).ae_eq hmem.2)] with x hx
    rw [hx, hderiv]
  have hrep : ∀ x ∈ Icc (0 : ℝ) 1, u.rep x = x ^ n := fun x hx ↦
    SobolevIntervalLp.rep_eq_of_continuousOn hI u (continuous_pow n).continuousOn hu
      (by rw [SobolevIntervalLp.closure_coe_Ioo (zero_lt_one' ℝ)]; exact hx)
  refine ⟨u, ?_, hrep⟩
  rw [← sobolevNorm_eq_norm_of_one, sobolevNorm]
  have hfin : IsFiniteMeasure (volume.restrict ((Opens.Ioo (0 : ℝ) 1 : Opens ℝ) : Set ℝ)) := ⟨by
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter, Opens.coe_Ioo, Real.volume_Ioo]
    exact ENNReal.ofReal_lt_top⟩
  have hvol : measureUnivNNReal (volume.restrict ((Opens.Ioo (0 : ℝ) 1 : Opens ℝ) : Set ℝ))
      = 1 := by
    simp [measureUnivNNReal, Real.volume_Ioo]
  -- `‖x^n‖_{L¹(0, 1)} ≤ 1`
  have h0 : ‖u.deriv 0‖ ≤ 1 := by
    have := Lp.norm_le_of_ae_bound (f := u.deriv 0) (C := 1) zero_le_one ?_
    · rwa [hvol, NNReal.coe_one, Real.one_rpow, one_mul] at this
    · filter_upwards [hu, ae_restrict_mem measurableSet_Ioo] with x hx hxI
      rw [SobolevIntervalLp.deriv_zero, hx, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hxI.1.le _)]
      exact pow_le_one₀ hxI.1.le hxI.2.le
  -- `‖n x^{n-1}‖_{L¹(0, 1)} = 1 - 0^n ≤ 1`
  have h1 : ‖u.deriv 1‖ ≤ 1 := by
    have e0 : (fun x ↦ ‖u.deriv 1 x‖) =ᵐ[volume.restrict ((Opens.Ioo (0 : ℝ) 1 : Opens ℝ) : Set ℝ)]
        fun x ↦ ‖(n : ℝ) * x ^ (n - 1)‖ := hu1.mono fun x hx ↦ by simp only [hx]
    rw [L1.norm_eq_integral_norm, integral_congr_ae e0]
    have e : ∫ x in ((Opens.Ioo (0 : ℝ) 1 : Opens ℝ) : Set ℝ), ‖(n : ℝ) * x ^ (n - 1)‖
        = ∫ x in (0 : ℝ)..1, (n : ℝ) * x ^ (n - 1) := by
      rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo, Opens.coe_Ioo]
      refine setIntegral_congr_fun measurableSet_Ioo fun x hx ↦ ?_
      exact Real.norm_of_nonneg (by have := hx.1.le; positivity)
    rw [e, intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ ↦ hasDerivAt_pow n x)
      ((continuous_const.mul (continuous_pow _)).intervalIntegrable _ _), one_pow]
    linarith [pow_nonneg (le_refl (0 : ℝ)) n]
  linarith

/-- **Remark 10(a)** in Chapter 8 of [brezis2011functional]. The injection
$W^{1,1}((0, 1)) \to C([0, 1])$ is not a compact operator.

The source says that the injection $W^{1,1}(I) \subseteq C(\bar I)$ is continuous but never
compact, even if $I$ is a bounded interval; the statement here is the case $I = (0, 1)$. The
functions $u_n(x) = x^n$ are bounded in $W^{1,1}((0, 1))$ and converge pointwise on $[0, 1]$ to
the discontinuous indicator function of $\{1\}$, so no subsequence converges in $C([0, 1])$. The
source leaves this argument to the reader or to Exercise 8.2. -/
theorem remark_8_10_a :
    ¬ IsCompactOperator (SobolevIntervalLp.toContinuousMap (p := 1) (zero_lt_one' ℝ)) := by
  intro hT
  choose u hu hrep using exists_pow_sobolevIntervalLp
  obtain ⟨T, hT'⟩ : ∃ T : SobolevIntervalLp 1 1 (Opens.Ioo 0 1) →L[ℝ] C(Icc (0 : ℝ) 1, ℝ),
      T = SobolevIntervalLp.toContinuousMap (p := 1) (zero_lt_one' ℝ) := ⟨_, rfl⟩
  rw [← hT'] at hT
  have hT2 : IsCompactOperator
      (T : SobolevIntervalLp 1 1 (Opens.Ioo 0 1) →ₗ[ℝ] C(Icc (0 : ℝ) 1, ℝ)) := by
    rwa [ContinuousLinearMap.coe_coe]
  have hK := hT2.isCompact_closure_image_closedBall 2
  obtain ⟨g, -, ρ, hρ, hlim⟩ := hK.tendsto_subseq (x := fun n ↦ T (u n)) fun n ↦
    subset_closure ⟨u n, mem_closedBall_zero_iff.2 (hu n), rfl⟩
  -- the pointwise values of the limit
  have hval : ∀ (x : Icc (0 : ℝ) 1) (k : ℕ), (T (u (ρ k))) x = (x : ℝ) ^ ρ k := fun x k ↦ by
    rw [hT', SobolevIntervalLp.toContinuousMap_apply, hrep _ _ x.2]
  have hev : ∀ x : Icc (0 : ℝ) 1, Tendsto (fun k ↦ (x : ℝ) ^ ρ k) atTop (𝓝 (g x)) := fun x ↦
    (((continuous_eval_const x : Continuous fun f : C(Icc (0 : ℝ) 1, ℝ) ↦ f x).tendsto g).comp
      hlim).congr fun k ↦ hval x k
  have hg1 : g ⟨1, right_mem_Icc.2 zero_le_one⟩ = 1 := by
    refine tendsto_nhds_unique (hev ⟨1, right_mem_Icc.2 zero_le_one⟩) ?_
    simp only [one_pow]
    exact tendsto_const_nhds
  have hg0 : ∀ x : Icc (0 : ℝ) 1, (x : ℝ) < 1 → g x = 0 := fun x hx ↦
    tendsto_nhds_unique (hev x)
      ((tendsto_pow_atTop_nhds_zero_of_lt_one x.2.1 hx).comp hρ.tendsto_atTop)
  -- the limit is continuous at `1`, but its values left of `1` vanish
  have hxk : ∀ k : ℕ, 1 - 1 / ((k : ℝ) + 1) ∈ Icc (0 : ℝ) 1 := fun k ↦ by
    have h1 : (1 : ℝ) / ((k : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    have h2 : (0 : ℝ) ≤ 1 / ((k : ℝ) + 1) := by positivity
    constructor <;> linarith
  have hlt : ∀ k : ℕ, 1 - 1 / ((k : ℝ) + 1) < 1 := fun k ↦ by
    have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    linarith
  have hseq : Tendsto (fun k : ℕ ↦ (⟨1 - 1 / ((k : ℝ) + 1), hxk k⟩ : Icc (0 : ℝ) 1)) atTop
      (𝓝 ⟨1, right_mem_Icc.2 zero_le_one⟩) := by
    rw [tendsto_subtype_rng]
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_one_div_add_atTop_nhds_zero_nat
  have hcont := (g.continuous.tendsto _).comp hseq
  have hzero : Tendsto (fun k : ℕ ↦ g ⟨1 - 1 / ((k : ℝ) + 1), hxk k⟩) atTop (𝓝 0) :=
    tendsto_const_nhds.congr fun k ↦ (hg0 _ (hlt k)).symm
  have := tendsto_nhds_unique hcont hzero
  rw [hg1] at this
  exact one_ne_zero this

/-- Two distinct natural numbers $m \ne n$ satisfy $|m - n| \ge 1$ in $\mathbb{R}$. -/
private theorem one_le_abs_sub_of_ne {m n : ℕ} (h : m ≠ n) : 1 ≤ |(m : ℝ) - n| := by
  have e : (m : ℝ) - n = ((m : ℤ) - n : ℤ) := by push_cast; ring
  rw [e, ← Int.cast_abs, ← Int.cast_one, Int.cast_le]
  exact Int.one_le_abs (sub_ne_zero.2 (by exact_mod_cast h))

/-- Let $s \subseteq \mathbb{R}$ be open, $x \in s$, and $f$ continuous at $x$; then $|f(x)|$ is at
most the essential supremum of $|f|$ on $s$. -/
private theorem enorm_le_eLpNormEssSup_restrict {f : ℝ → ℝ} {s : Set ℝ} (hs : IsOpen s) {x : ℝ}
    (hx : x ∈ s) (hf : ContinuousAt f x) : ‖f x‖ₑ ≤ eLpNormEssSup f (volume.restrict s) := by
  by_contra hlt
  push Not at hlt
  have hev : ∀ᶠ y in 𝓝 x, eLpNormEssSup f (volume.restrict s) < ‖f y‖ₑ :=
    continuousAt_const.eventually_lt (continuous_enorm.continuousAt.comp hf) hlt
  obtain ⟨U, hUsub, hU, hxU⟩ := mem_nhds_iff.1 hev
  have h0 : volume.restrict s {y | eLpNormEssSup f (volume.restrict s) < ‖f y‖ₑ} = 0 :=
    meas_eLpNormEssSup_lt
  have hpos : 0 < volume.restrict s U := by
    rw [Measure.restrict_apply hU.measurableSet]
    exact (hU.inter hs).measure_pos volume ⟨x, hxU, hx⟩
  exact hpos.ne' (measure_mono_null hUsub h0)

/-- **Remark 10(c)** in Chapter 8 of [brezis2011functional]. Let $I$ be an unbounded open interval
and $1 \le p \le \infty$. The injection $W^{1,p}(I) \to L^\infty(I)$ is not a compact operator.

**Generalization.** The source states this in the context $1 < p \le \infty$. The statement here
holds for every $1 \le p \le \infty$.

The injection is `SobolevIntervalLp.toLp`, which is continuous by Theorem 8.8(5). Take a fixed
bump function $\varphi \in C_c^\infty(\mathbb{R})$ and its translates
$u_n = \varphi(\cdot - c_n)$ along a half-line in $I$, with the points $c_n$ at mutual distance
at least $1$. These are bounded in $W^{1,p}(I)$ and at mutual distance at least
$\|\varphi\|_\infty = 1$ in $L^\infty(I)$, so no subsequence is a Cauchy sequence in
$L^\infty(I)$. The source leaves this argument to the reader or to Exercise 8.4. -/
theorem remark_8_10_c (hI : (I : Set ℝ).OrdConnected) (hunb : ¬ Bornology.IsBounded (I : Set ℝ)) :
    ¬ IsCompactOperator (SobolevIntervalLp.toLp p hI (le_top : p ≤ ⊤)) := by
  intro hT
  -- centres of the translates, at mutual distance at least one, with `[c n - 1, c n + 1] ⊆ I`
  obtain ⟨c, hcI, hsep⟩ : ∃ c : ℕ → ℝ, (∀ n, Icc (c n - 1) (c n + 1) ⊆ I) ∧
      ∀ m n, m ≠ n → 1 ≤ |c m - c n| := by
    obtain ⟨x₀, hx₀⟩ : (I : Set ℝ).Nonempty := by
      by_contra h
      rw [not_nonempty_iff_eq_empty] at h
      exact hunb (h ▸ Bornology.isBounded_empty)
    rw [isBounded_iff_bddBelow_bddAbove, not_and_or] at hunb
    rcases hunb with h | h
    · refine ⟨fun n ↦ x₀ - ((n : ℝ) + 2), fun n ↦ ?_, fun m n hmn ↦ ?_⟩
      · obtain ⟨y, hy, hyx⟩ : ∃ y ∈ (I : Set ℝ), y < x₀ - ((n : ℝ) + 2) - 1 := by
          by_contra hcon
          push Not at hcon
          exact h ⟨_, fun y hy ↦ hcon y hy⟩
        exact (Icc_subset_Icc hyx.le (by linarith)).trans (hI.out hy hx₀)
      · rw [show x₀ - ((m : ℝ) + 2) - (x₀ - ((n : ℝ) + 2)) = -((m : ℝ) - n) by ring, abs_neg]
        exact one_le_abs_sub_of_ne hmn
    · refine ⟨fun n ↦ x₀ + ((n : ℝ) + 2), fun n ↦ ?_, fun m n hmn ↦ ?_⟩
      · obtain ⟨y, hy, hyx⟩ : ∃ y ∈ (I : Set ℝ), x₀ + ((n : ℝ) + 2) + 1 < y := by
          by_contra hcon
          push Not at hcon
          exact h ⟨_, fun y hy ↦ hcon y hy⟩
        exact (Icc_subset_Icc (by linarith) hyx.le).trans (hI.out hx₀ hy)
      · rw [show x₀ + ((m : ℝ) + 2) - (x₀ + ((n : ℝ) + 2)) = (m : ℝ) - n by ring]
        exact one_le_abs_sub_of_ne hmn
  -- the bump and its translates, as test functions on `I`
  obtain ⟨φ, hφin, hφout⟩ : ∃ φ : ContDiffBump (0 : ℝ), φ.rIn = 1 / 4 ∧ φ.rOut = 1 / 2 :=
    ⟨⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩, rfl, rfl⟩
  have hφc : ∀ n, tsupport (fun x ↦ φ (x - c n)) ⊆ I := fun n ↦ by
    refine (closure_minimal ?_ isClosed_Icc).trans (hcI n)
    intro x hx
    have hx' : x - c n ∈ Function.support φ := Function.mem_support.2 (Function.mem_support.1 hx)
    rw [φ.support_eq, Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_lt, hφout] at hx'
    constructor <;> linarith [hx'.1, hx'.2]
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ℕ → 𝓓(I, ℝ), ∀ n, ⇑(ψ n) = fun x ↦ φ (x - c n) :=
    ⟨fun n ↦ ⟨fun x ↦ φ (x - c n), (φ.contDiff (n := ⊤)).comp (contDiff_id.sub contDiff_const),
      φ.hasCompactSupport.comp_homeomorph (Homeomorph.subRight (c n)), hφc n⟩, fun n ↦ rfl⟩
  obtain ⟨u, hu⟩ : ∃ u : ℕ → SobolevIntervalLp 1 p I,
      ∀ n, u n = TestFunction.toSobolevIntervalLp p (ψ n) := ⟨_, fun n ↦ rfl⟩
  -- the translates are bounded in `W^{1,p}(I)`
  have hφp : MemLp (⇑φ) p volume := φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport
  have hφ'p : MemLp (deriv φ) p volume :=
    ((φ.contDiff (n := 1)).continuous_deriv le_rfl).memLp_of_hasCompactSupport
      φ.hasCompactSupport.deriv
  have hM : ∀ n, ‖u n‖ ≤ (eLpNorm φ p volume).toReal + (eLpNorm (deriv φ) p volume).toReal :=
    fun n ↦ by
    refine (sobolevNorm_equiv (u n)).1.trans (add_le_add ?_ ?_)
    · rw [Lp.norm_def]
      refine ENNReal.toReal_mono hφp.eLpNorm_ne_top ?_
      calc eLpNorm (⇑((u n).deriv 0)) p (volume.restrict I)
          = eLpNorm (ψ n) p (volume.restrict I) := by
            rw [hu]
            exact eLpNorm_congr_ae (TestFunction.fn_toSobolevIntervalLp_ae_eq (ψ n))
        _ ≤ eLpNorm (ψ n) p volume := eLpNorm_mono_measure _ Measure.restrict_le_self
        _ = eLpNorm φ p volume := by
            rw [hψ]
            exact eLpNorm_comp_measurePreserving φ.continuous.aestronglyMeasurable
              (measurePreserving_sub_right volume (c n))
    · rw [Lp.norm_def]
      refine ENNReal.toReal_mono hφ'p.eLpNorm_ne_top ?_
      have hd : deriv (ψ n) = fun x ↦ deriv φ (x - c n) := by
        rw [hψ]
        exact funext fun x ↦ deriv_comp_sub_const _ _ _
      calc eLpNorm (⇑((u n).deriv 1)) p (volume.restrict I)
          = eLpNorm (deriv (ψ n)) p (volume.restrict I) := by
            rw [hu]
            exact eLpNorm_congr_ae (TestFunction.coeFn_deriv_toSobolevIntervalLp_one (ψ n))
        _ ≤ eLpNorm (deriv (ψ n)) p volume := eLpNorm_mono_measure _ Measure.restrict_le_self
        _ = eLpNorm (deriv φ) p volume := by
            rw [hd]
            exact eLpNorm_comp_measurePreserving
              ((φ.contDiff (n := 1)).continuous_deriv le_rfl).aestronglyMeasurable
              (measurePreserving_sub_right volume (c n))
  -- two translates are at `L^∞` distance at least one
  obtain ⟨T, hT'⟩ : ∃ T : SobolevIntervalLp 1 p I →L[ℝ] Lp ℝ ⊤ (volume.restrict (I : Set ℝ)),
      T = SobolevIntervalLp.toLp p hI (le_top : p ≤ ⊤) := ⟨_, rfl⟩
  rw [← hT'] at hT
  have hge : ∀ a b, a ≠ b → 1 ≤ dist (T (u a)) (T (u b)) := fun a b hab ↦ by
    rw [dist_eq_norm, ← map_sub, hT', Lp.norm_def]
    have hae : ⇑(SobolevIntervalLp.toLp p hI (le_top : p ≤ ⊤) (u a - u b))
        =ᵐ[volume.restrict I] fun x ↦ φ (x - c a) - φ (x - c b) := by
      refine (SobolevIntervalLp.coeFn_toLp (p := p) (q := ⊤) hI le_top (u a - u b)).trans
        ((SobolevMultiIndex.fn_sub (u a) (u b)).trans ?_)
      rw [hu, hu]
      filter_upwards [TestFunction.fn_toSobolevIntervalLp_ae_eq (p := p) (ψ a),
        TestFunction.fn_toSobolevIntervalLp_ae_eq (p := p) (ψ b)] with x hxa hxb
      have hxa' : SobolevMultiIndex.fn (TestFunction.toSobolevIntervalLp p (ψ a)) x
          = φ (x - c a) := by
        have := congrFun (hψ a) x
        exact hxa.trans this
      have hxb' : SobolevMultiIndex.fn (TestFunction.toSobolevIntervalLp p (ψ b)) x
          = φ (x - c b) := by
        have := congrFun (hψ b) x
        exact hxb.trans this
      rw [Pi.sub_apply, hxa', hxb']
    have hcont : Continuous fun x ↦ φ (x - c a) - φ (x - c b) :=
      (φ.continuous.comp (continuous_sub_right (c a))).sub
        (φ.continuous.comp (continuous_sub_right (c b)))
    have hne : eLpNormEssSup (fun x ↦ φ (x - c a) - φ (x - c b)) (volume.restrict I) ≠ ⊤ := by
      rw [← eLpNorm_exponent_top hcont.aestronglyMeasurable, ← eLpNorm_congr_ae hae]
      exact Lp.eLpNorm_ne_top _
    rw [eLpNorm_congr_ae hae, eLpNorm_exponent_top hcont.aestronglyMeasurable]
    have hlow : ‖φ (c a - c a) - φ (c a - c b)‖ₑ
        ≤ eLpNormEssSup (fun x ↦ φ (x - c a) - φ (x - c b)) (volume.restrict I) :=
      enorm_le_eLpNormEssSup_restrict (f := fun x ↦ φ (x - c a) - φ (x - c b)) I.isOpen
        (hcI a ⟨by linarith, by linarith⟩) hcont.continuousAt
    rw [sub_self, φ.one_of_mem_closedBall (Metric.mem_closedBall_self (by rw [hφin]; norm_num)),
      φ.zero_of_le_dist (by rw [hφout, Real.dist_eq, sub_zero]; linarith [hsep a b hab]),
      sub_zero, enorm_one] at hlow
    have := ENNReal.toReal_mono hne hlow
    rwa [ENNReal.toReal_one] at this
  -- no subsequence of the translates is Cauchy in `L^∞(I)`
  have hT2 : IsCompactOperator
      (T : SobolevIntervalLp 1 p I →ₗ[ℝ] Lp ℝ ⊤ (volume.restrict (I : Set ℝ))) := by
    rwa [ContinuousLinearMap.coe_coe]
  have hK := hT2.isCompact_closure_image_closedBall
    ((eLpNorm φ p volume).toReal + (eLpNorm (deriv φ) p volume).toReal)
  obtain ⟨g, -, ρ, hρ, hlim⟩ := hK.tendsto_subseq (x := fun n ↦ T (u n)) fun n ↦
    subset_closure ⟨u n, mem_closedBall_zero_iff.2 (hM n), rfl⟩
  have hcauchy := hlim.cauchySeq
  rw [Metric.cauchySeq_iff'] at hcauchy
  obtain ⟨N, hN⟩ := hcauchy 1 one_pos
  have hlt := hN (N + 1) (Nat.le_succ N)
  simp only [Function.comp_apply] at hlt
  exact absurd hlt (not_lt.2 (hge _ _ (hρ.injective.ne (Nat.succ_ne_self N))))

/-- **Remark 10(b)** in Chapter 8 of [brezis2011functional] (Helly's selection theorem). Let
$a < b$, and let $(u_n)$ be a sequence in $W^{1,1}((a, b))$ with $\|u_n\| \le M$ for all $n$.
Then there is a subsequence $(u_{n_k})$ such that $\tilde u_{n_k}(x)$ converges for every
$x \in [a, b]$.

The source allows an unbounded interval $I$. That case follows by a diagonal argument on
$I \cap [-R, R]$ and is not formalized. Here $\tilde u_n$ is `SobolevIntervalLp.rep (u n)`, and
$\|u_n\|$ is the norm of the type. The proof specializes
`SobolevIntervalLp.exists_subseq_tendsto_of_bounded_one`. -/
theorem remark_8_10_b {a b : ℝ} (hab : a < b) {u : ℕ → SobolevIntervalLp 1 1 (Opens.Ioo a b)}
    {M : ℝ} (hM : ∀ n, ‖u n‖ ≤ M) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ x ∈ Icc a b, ∃ l : ℝ, Tendsto (fun n ↦ (u (φ n)).rep x) atTop (𝓝 l) :=
  SobolevIntervalLp.exists_subseq_tendsto_of_bounded_one hab hM

/-- **Remark 10(d)** in Chapter 8 of [brezis2011functional]. Let $I$ be an open interval,
$1 < p \le \infty$, and let $(u_n)$ be a sequence in $W^{1,p}(I)$ with $\|u_n\| \le M$ for all
$n$. Then there are a subsequence $(u_{n_k})$ and some $u \in W^{1,p}(I)$ such that
$u_{n_k} \to u$ in $L^\infty(J)$ for every bounded subset $J$ of $I$: for every $R$,
$\tilde u_{n_k} \to \tilde u$ uniformly on $\bar I \cap [-R, R]$.

The proof specializes `SobolevIntervalLp.exists_subseq_tendsto_rep_of_bounded`. -/
theorem remark_8_10_d (hI : (I : Set ℝ).OrdConnected) (hp : 1 < p)
    {u : ℕ → SobolevIntervalLp 1 p I} {M : ℝ} (hM : ∀ n, ‖u n‖ ≤ M) :
    ∃ (v : SobolevIntervalLp 1 p I) (φ : ℕ → ℕ), StrictMono φ ∧
      ∀ R : ℝ, TendstoUniformlyOn (fun n ↦ (u (φ n)).rep) v.rep atTop
        (closure (I : Set ℝ) ∩ Icc (-R) R) :=
  have := ENNReal.holderConjugate_sub_inv_inv (p := p)
  let ⟨v, φ, hφ, hlim, _⟩ := SobolevIntervalLp.exists_subseq_tendsto_rep_of_bounded hI
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt (1 - p⁻¹)⁻¹ p).2 hp).ne hM
  ⟨v, φ, hφ, hlim⟩

/-- **Remark 11** in Chapter 8 of [brezis2011functional]. Let $a < b$, $1 \le p \le \infty$ and
$1 \le q \le \infty$. On $W^{1,p}((a, b))$, the norm $\|u'\|_{L^p} + \|u\|_{L^q}$ is equivalent
to the norm of $W^{1,p}$: there are $C_1, C_2 > 0$ with
$$\|u\| \le C_1 (\|u'\|_{L^p} + \|u\|_{L^q}), \qquad \|u'\|_{L^p} + \|u\|_{L^q} \le C_2 \|u\|$$
for all $u \in W^{1,p}((a, b))$.

Here $\|u\|$ is the norm of the type, and $\|u\|_{L^q}$ is the norm of the image of $u$ under
`SobolevIntervalLp.toLpOfBounded p hab q`. The proof specializes
`SobolevIntervalLp.norm_equiv_of_bounded`. -/
theorem remark_8_11 {a b : ℝ} (hab : a < b) (q : ℝ≥0∞) [Fact (1 ≤ q)] :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ u : SobolevIntervalLp 1 p (Opens.Ioo a b),
      ‖u‖ ≤ C₁ * (‖u.deriv 1‖ + ‖SobolevIntervalLp.toLpOfBounded p hab q u‖) ∧
      ‖u.deriv 1‖ + ‖SobolevIntervalLp.toLpOfBounded p hab q u‖ ≤ C₂ * ‖u‖ :=
  SobolevIntervalLp.norm_equiv_of_bounded hab q

/-- **Remark 12** in Chapter 8 of [brezis2011functional]. Let $I$ be an unbounded open interval,
$1 \le p \le \infty$ and $u \in W^{1,p}(I)$. Then $u \in L^q(I)$ for all $q \in [p, \infty]$.

The proof does not use that $I$ is unbounded. It specializes `SobolevIntervalLp.memLp_of_le`,
which uses the interpolation $\int_I |u|^q \le \|u\|_\infty^{q - p} \|u\|_p^p$. The claim of the
source that in general $u \notin L^q(I)$ for $q \in [1, p)$ (Exercise 8.1) is not formalized. -/
theorem remark_8_12 (hI : (I : Set ℝ).OrdConnected) (_hunb : ¬ Bornology.IsBounded (I : Set ℝ))
    (u : SobolevIntervalLp 1 p I) {q : ℝ≥0∞} (hpq : p ≤ q) : MemLp u.fn q (volume.restrict I) :=
  SobolevIntervalLp.memLp_of_le hI hpq u

/-! ### Corollaries 8.9–8.11 -/

/-- **Corollary 8.9** of [brezis2011functional]. Let $I$ be an unbounded open interval,
$1 \le p < \infty$ and $u \in W^{1,p}(I)$. Then
$$\lim_{x \in I, \ |x| \to \infty} u(x) = 0.$$

Here $u(x)$ is the continuous representative `SobolevIntervalLp.rep u`, and the limit is along
the filter `cocompact ℝ ⊓ 𝓟 (I : Set ℝ)`. The proof specializes
`SobolevIntervalLp.tendsto_rep_cocompact`, which does not need $I$ unbounded: for a bounded $I$
the filter is trivial. -/
theorem corollary_8_9 (hI : (I : Set ℝ).OrdConnected) (_hunb : ¬ Bornology.IsBounded (I : Set ℝ))
    (hp : p ≠ ∞) (u : SobolevIntervalLp 1 p I) :
    Tendsto u.rep (cocompact ℝ ⊓ 𝓟 (I : Set ℝ)) (𝓝 0) :=
  SobolevIntervalLp.tendsto_rep_cocompact hI hp u

/-- **Corollary 8.10** of [brezis2011functional] (differentiation of a product). Let $I$ be an open
interval, $1 \le p \le \infty$ and $u, v \in W^{1,p}(I)$. Then $u v \in W^{1,p}(I)$.

The product is the product $\tilde u \tilde v$ of the continuous representatives. The proof
specializes `SobolevIntervalLp.memSobolevIntervalLp_mul`, from the calculus of absolutely
continuous functions instead of the density argument of the source. -/
theorem corollary_8_10 (hI : (I : Set ℝ).OrdConnected) (u v : SobolevIntervalLp 1 p I) :
    MemSobolevSpace p I fun t ↦ u.rep t * v.rep t :=
  memSobolevSpace_iff_memSobolevIntervalLp.2 (SobolevIntervalLp.memSobolevIntervalLp_mul hI u v)

/-- **Corollary 8.10** of [brezis2011functional], formula (10). Let $I$ be an open interval,
$1 \le p \le \infty$ and $u, v \in W^{1,p}(I)$. Then $(u v)' = u' v + u v'$, that is,
$$\int_I \tilde u \tilde v \varphi' = -\int_I (u' \tilde v + \tilde u v') \varphi \quad
  \text{for all } \varphi \in C_c^\infty(I).$$

The proof specializes `SobolevIntervalLp.hasWeakDerivOn_rep_mul`. -/
theorem corollary_8_10_deriv (hI : (I : Set ℝ).OrdConnected) (u v : SobolevIntervalLp 1 p I)
    (φ : 𝓓(I, ℝ)) :
    ∫ x in (I : Set ℝ), (u.rep x * v.rep x) * deriv φ x
      = -∫ x in (I : Set ℝ), (u.deriv 1 x * v.rep x + u.rep x * v.deriv 1 x) * φ x := by
  have := (SobolevIntervalLp.hasWeakDerivOn_rep_mul hI u v).integral_deriv_mul φ
  simp only [mul_comm] at this ⊢
  exact this

/-- **Corollary 8.10** of [brezis2011functional], formula (11) (integration by parts). Let $I$ be an
open interval, $1 \le p \le \infty$ and $u, v \in W^{1,p}(I)$. Then
$$\int_y^x u' v = u(x) v(x) - u(y) v(y) - \int_y^x u v' \quad \text{for all } x, y \in \bar I.$$

Here $u$ and $v$ are their continuous representatives. The proof specializes
`SobolevIntervalLp.integral_deriv_mul_eq_sub_integral_mul_deriv`. -/
theorem corollary_8_10_parts (hI : (I : Set ℝ).OrdConnected) (u v : SobolevIntervalLp 1 p I)
    {x y : ℝ} (hx : x ∈ closure (I : Set ℝ)) (hy : y ∈ closure (I : Set ℝ)) :
    ∫ t in y..x, u.deriv 1 t * v.rep t
      = u.rep x * v.rep x - u.rep y * v.rep y - ∫ t in y..x, u.rep t * v.deriv 1 t :=
  SobolevIntervalLp.integral_deriv_mul_eq_sub_integral_mul_deriv hI u v hx hy

/-- **Corollary 8.11** of [brezis2011functional] (differentiation of a composition). Let $I$ be an
open interval, $1 \le p \le \infty$, $G \in C^1(\mathbb{R})$ with $G(0) = 0$, and
$u \in W^{1,p}(I)$. Then $G \circ u \in W^{1,p}(I)$.

Here $G \circ u$ is $G \circ \tilde u$. The proof specializes
`SobolevIntervalLp.memSobolevIntervalLp_comp`. -/
theorem corollary_8_11 (hI : (I : Set ℝ).OrdConnected) (u : SobolevIntervalLp 1 p I) {G : ℝ → ℝ}
    (hG : ContDiff ℝ 1 G) (hG0 : G 0 = 0) : MemSobolevSpace p I fun t ↦ G (u.rep t) :=
  memSobolevSpace_iff_memSobolevIntervalLp.2
    (SobolevIntervalLp.memSobolevIntervalLp_comp hI u hG hG0).1

/-- **Corollary 8.11** of [brezis2011functional], the derivative. Let $I$ be an open interval,
$1 \le p \le \infty$, $G \in C^1(\mathbb{R})$ and $u \in W^{1,p}(I)$. Then
$(G \circ u)' = (G' \circ u) u'$, that is,
$$\int_I G(\tilde u) \varphi' = -\int_I G'(\tilde u) \, u' \varphi \quad \text{for all } \varphi
  \in C_c^\infty(I).$$

**Generalization.** The source assumes $G(0) = 0$ for the whole corollary. The formula for the
derivative holds without this assumption. -/
theorem corollary_8_11_deriv (hI : (I : Set ℝ).OrdConnected) (u : SobolevIntervalLp 1 p I)
    {G : ℝ → ℝ} (hG : ContDiff ℝ 1 G) (φ : 𝓓(I, ℝ)) :
    ∫ x in (I : Set ℝ), G (u.rep x) * deriv φ x
      = -∫ x in (I : Set ℝ), (deriv G (u.rep x) * u.deriv 1 x) * φ x := by
  have := (SobolevIntervalLp.hasWeakDerivOn_comp hI u hG).integral_deriv_mul φ
  simp only [mul_comm] at this ⊢
  exact this

/-- **Corollary 8.11** of [brezis2011functional], footnote 9. Let $a < b$, $1 \le p \le \infty$,
$G \in C^1(\mathbb{R})$ and $u \in W^{1,p}((a, b))$. Then $G \circ u \in W^{1,p}((a, b))$. So on
a bounded interval the condition $G(0) = 0$ is not needed.

The proof specializes `SobolevIntervalLp.memSobolevIntervalLp_comp_of_bounded`. -/
theorem corollary_8_11_of_bounded {a b : ℝ} (hab : a < b)
    (u : SobolevIntervalLp 1 p (Opens.Ioo a b)) {G : ℝ → ℝ} (hG : ContDiff ℝ 1 G) :
    MemSobolevSpace p (Opens.Ioo a b) fun t ↦ G (u.rep t) :=
  memSobolevSpace_iff_memSobolevIntervalLp.2
    (SobolevIntervalLp.memSobolevIntervalLp_comp_of_bounded hab u hG).1

/-! ### The Sobolev spaces $W^{m,p}$ -/

/-- **Section 8.2** of [brezis2011functional], the Sobolev spaces $W^{m,p}$, the inductive
definition as a condition on functions. Let $I \subseteq \mathbb{R}$ be open,
$1 \le p \le \infty$ and $u : \mathbb{R} \to \mathbb{R}$. The condition $u \in W^{0,p}(I)$ means
$u \in L^p(I)$. The condition $u \in W^{m+1,p}(I)$ means that $u \in W^{m,p}(I)$ and that $u$
has a weak derivative $g \in W^{m,p}(I)$:
$$\int_I u \varphi' = -\int_I g \varphi \quad \text{for all } \varphi \in C_c^\infty(I).$$

For $m = 1$ this is the condition `Brezis.Chapter08.MemSobolevSpace`
(`Brezis.Chapter08.memSobolevSpaceHigher_one`). For $m \ge 2$ it is the definition of the
source, $W^{m,p}(I) = \{u \in W^{m-1,p}(I) : u' \in W^{m-1,p}(I)\}$. -/
def MemSobolevSpaceHigher (p : ℝ≥0∞) (I : Opens ℝ) : ℕ → (ℝ → ℝ) → Prop
  | 0, u => MemLp u p (volume.restrict I)
  | m + 1, u => MemSobolevSpaceHigher p I m u ∧ ∃ g : ℝ → ℝ, MemSobolevSpaceHigher p I m g ∧
      ∀ φ : 𝓓(I, ℝ), ∫ x in (I : Set ℝ), u x * deriv φ x = -∫ x in (I : Set ℝ), g x * φ x

omit [Fact (1 ≤ p)] in
/-- For every $p$ and every open $I \subseteq \mathbb{R}$, a function $u$ satisfies the inductive
definition of $W^{1,p}(I)$, `Brezis.Chapter08.MemSobolevSpaceHigher p I 1 u`, if and only if
$u \in W^{1,p}(I)$ in the sense of `Brezis.Chapter08.MemSobolevSpace`. -/
theorem memSobolevSpaceHigher_one {u : ℝ → ℝ} :
    MemSobolevSpaceHigher p I 1 u ↔ MemSobolevSpace p I u := Iff.rfl

/-- Let $I \subseteq \mathbb{R}$ be open, $1 \le p \le \infty$, $m \in \mathbb{N}$ and
$u : \mathbb{R} \to \mathbb{R}$. Then $u \in W^{m,p}(I)$ in the inductive sense of Section 8.2
of [brezis2011functional] if and only if `MemSobolevIntervalLp u m p I` holds: $u$ and its weak
derivatives of orders $1, \dots, m$ on $I$ lie in $L^p(I)$.

The proof is an induction on $m$ through `memSobolevIntervalLp_succ_iff`. -/
theorem memSobolevSpaceHigher_iff {m : ℕ} {u : ℝ → ℝ} :
    MemSobolevSpaceHigher p I m u ↔ MemSobolevIntervalLp u m p I := by
  induction m generalizing u with
  | zero => exact memSobolevIntervalLp_zero_iff.symm
  | succ m ih =>
    rw [MemSobolevSpaceHigher, ih, memSobolevIntervalLp_succ_iff]
    constructor
    · rintro ⟨hu, g, hg, h⟩
      have hu' := (memSobolevIntervalLp_iff.1 hu).1
      have hg' := (memSobolevIntervalLp_iff.1 (ih.1 hg)).1
      refine ⟨hu', g, hasWeakDerivOn_iff.2 ⟨hu'.locallyIntegrableOn Fact.out,
        hg'.locallyIntegrableOn Fact.out, fun φ ↦ ?_⟩, ih.1 hg⟩
      have := h φ
      simp only [mul_comm] at this ⊢
      exact this
    · rintro ⟨hu, w, hw, hwm⟩
      refine ⟨?_, w, ih.2 hwm, fun φ ↦ ?_⟩
      · rw [memSobolevIntervalLp_iff] at hwm ⊢
        refine ⟨hu, fun j hj ↦ ?_⟩
        cases j with
        | zero => exact ⟨u, HasWeakIteratedLineDerivOn.of_length_eq_zero rfl _
            hw.locallyIntegrableOn, hu⟩
        | succ j =>
          obtain ⟨w', hw', hwp'⟩ := hwm.2 j (by omega)
          exact ⟨w', hw.hasWeakIteratedDerivOn_succ hw', hwp'⟩
      · have := hw.integral_deriv_mul φ
        simp only [mul_comm] at this ⊢
        exact this

/-- **Section 8.2** of [brezis2011functional], the Sobolev spaces $W^{m,p}$, definition. Let
$I \subseteq \mathbb{R}$ be open, $m \in \mathbb{N}$ and $1 \le p \le \infty$. The space
$W^{m,p}(I)$ is the space of tuples $(u, Du, \dots, D^m u)$ in $L^p(I)$ in which $D^j u$ is the
$j$-th weak derivative of $u$ on $I$.

The type is the backbone's `SobolevIntervalLp m p I`. -/
abbrev sobolevSpaceHigher (m : ℕ) (p : ℝ≥0∞) (I : Opens ℝ) : Type := SobolevIntervalLp m p I

/-- **Section 8.2** of [brezis2011functional], the Sobolev spaces $W^{m,p}$, notation. The space
$H^m(I)$ is $W^{m,2}(I)$. -/
abbrev Hm (m : ℕ) (I : Opens ℝ) : Type := sobolevSpaceHigher m 2 I

/-- **Section 8.2** of [brezis2011functional], the Sobolev spaces $W^{m,p}$, the characterization by
$m$ functions. Let $I \subseteq \mathbb{R}$ be open, $1 \le p \le \infty$, $m \in \mathbb{N}$
and $u : \mathbb{R} \to \mathbb{R}$. Then $u \in W^{m,p}(I)$ if and only if $u \in L^p(I)$ and
for each $j = 1, \dots, m$ there is $g_j \in L^p(I)$ with
$$\int_I u \, D^j \varphi = (-1)^j \int_I g_j \varphi \quad \text{for all } \varphi \in
  C_c^\infty(I).$$

The source says that this characterization is easily shown. The proof specializes
`SobolevIntervalLp.memSobolevIntervalLp_iff_forall_integral`. -/
theorem memSobolevSpaceHigher_iff_forall_integral {m : ℕ} {u : ℝ → ℝ} :
    MemSobolevSpaceHigher p I m u ↔ MemLp u p (volume.restrict I) ∧ ∀ j ∈ Icc 1 m,
      ∃ g : ℝ → ℝ, MemLp g p (volume.restrict I) ∧ ∀ φ : 𝓓(I, ℝ),
        ∫ x in (I : Set ℝ), u x * iteratedDeriv j φ x
          = (-1) ^ j * ∫ x in (I : Set ℝ), g x * φ x :=
  memSobolevSpaceHigher_iff.trans SobolevIntervalLp.memSobolevIntervalLp_iff_forall_integral

omit [Fact (1 ≤ p)] in
/-- **Section 8.2** of [brezis2011functional], the Sobolev spaces $W^{m,p}$, the successive
derivatives $Du, D^2 u, \dots, D^m u$. Let $I \subseteq \mathbb{R}$ be open, $m \in \mathbb{N}$
and $u \in W^{m,p}(I)$. For $j = 0, \dots, m$,
$$\int_I u \, D^j \varphi = (-1)^j \int_I (D^j u) \varphi \quad \text{for all } \varphi \in
  C_c^\infty(I),$$
where $D^j u$ is the component `SobolevIntervalLp.deriv u j` of $u$. So $D^j u$ is the function
$g_j$ of the characterization: $u' = g_1$, $(u')' = g_2$, and so on.

The statement does not need $p \ge 1$. The proof uses
`SobolevIntervalLp.hasWeakDerivOn_deriv_succ`. -/
theorem memSobolevSpaceHigher_deriv {m : ℕ} (u : SobolevIntervalLp m p I) (j : Fin (m + 1))
    (φ : 𝓓(I, ℝ)) :
    ∫ x in (I : Set ℝ), u.fn x * iteratedDeriv j φ x
      = (-1) ^ (j : ℕ) * ∫ x in (I : Set ℝ), u.deriv j x * φ x := by
  have := (SobolevIntervalLp.hasWeakIteratedDerivOn_deriv u j).integral_iteratedDeriv_mul φ
  simp only [mul_comm] at this ⊢
  exact this

/-- **Section 8.2** of [brezis2011functional], the Sobolev spaces $W^{m,p}$, the norm. The norm of
$u \in W^{m,p}(I)$ in the source is
$$\|u\|_{W^{m,p}} = \|u\|_{L^p} + \sum_{\alpha = 1}^m \|D^\alpha u\|_{L^p}.$$
-/
def sobolevNormHigher {m : ℕ} (u : SobolevIntervalLp m p I) : ℝ :=
  ‖u.deriv 0‖ + ∑ j : Fin m, ‖u.deriv j.succ‖

/-- Let $I \subseteq \mathbb{R}$ be open, $1 \le p \le \infty$, $m \in \mathbb{N}$ and
$u \in W^{m,p}(I)$. The norm $\|u\|_{W^{m,p}}$ of Section 8.2 of [brezis2011functional] is
equivalent to the norm of the type, which is the $\ell^p$ sum of the norms
$\|D^\alpha u\|_{L^p}$:
$$\|u\| \le \|u\|_{W^{m,p}} \le (m + 1) \|u\|.$$

The proof specializes `SobolevIntervalLp.norm_le_sum_norm_deriv` and
`SobolevIntervalLp.sum_norm_deriv_le_mul_norm`. -/
theorem sobolevNormHigher_equiv {m : ℕ} (u : SobolevIntervalLp m p I) :
    ‖u‖ ≤ sobolevNormHigher u ∧ sobolevNormHigher u ≤ (m + 1) * ‖u‖ := by
  have e : sobolevNormHigher u = ∑ j : Fin (m + 1), ‖u.deriv j‖ := by
    rw [sobolevNormHigher, Fin.sum_univ_succ]
  rw [e]
  exact ⟨SobolevIntervalLp.norm_le_sum_norm_deriv u, SobolevIntervalLp.sum_norm_deriv_le_mul_norm u⟩

/-- **Section 8.2** of [brezis2011functional], the Sobolev spaces $W^{m,p}$, the scalar product of
$H^m$. Let $I \subseteq \mathbb{R}$ be open and $m \in \mathbb{N}$. For $u, v \in H^m(I)$,
$$(u, v)_{H^m} = (u, v)_{L^2} + \sum_{\alpha = 1}^m (D^\alpha u, D^\alpha v)_{L^2}.$$

The proof specializes `SobolevIntervalLp.inner_eq`. -/
theorem inner_Hm {m : ℕ} (u v : SobolevIntervalLp m 2 I) :
    ⟪u, v⟫_ℝ = ⟪u.deriv 0, v.deriv 0⟫_ℝ + ∑ j : Fin m, ⟪u.deriv j.succ, v.deriv j.succ⟫_ℝ := by
  rw [SobolevIntervalLp.inner_eq, Fin.sum_univ_succ]

/-- **Section 8.2** of [brezis2011functional], the Sobolev spaces $W^{m,p}$, the interpolation
inequality. Let $I$ be an open interval, $1 \le p \le \infty$, let $j$ and $m$ be integers with
$1 \le j \le m - 1$, and let $\varepsilon > 0$. There is a constant $C$ such that
$$\|D^j u\|_{L^p} \le \varepsilon \|D^m u\|_{L^p} + C \|u\|_{L^p} \quad \text{for all } u \in
  W^{m,p}(I).$$

The source says that $C$ depends on $\varepsilon$ and $|I| \le \infty$, and refers to Adams and
to Exercise 8.6 for the proof. The proof specializes
`SobolevIntervalLp.eLpNorm_deriv_le_mul_add`, by a direct estimate on windows. -/
theorem interpolationInequality (hI : (I : Set ℝ).OrdConnected) {m : ℕ} (j : ℕ) (hj1 : 1 ≤ j)
    (hjm : j < m) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ u : SobolevIntervalLp m p I,
      ‖u.deriv ⟨j, by omega⟩‖ ≤ ε * ‖u.deriv (Fin.last m)‖ + C * ‖u.deriv 0‖ := by
  obtain ⟨C, -, hC⟩ := SobolevIntervalLp.eLpNorm_deriv_le_mul_add (p := p) hI
    (⟨j, by omega⟩ : Fin (m + 1)) (by rw [Ne, Fin.ext_iff]; simp; omega)
    (by rw [Ne, Fin.ext_iff]; simp; omega) hε
  exact ⟨C, hC⟩

/-- **Section 8.2** of [brezis2011functional], the Sobolev spaces $W^{m,p}$, the equivalent norm
$\|u\|_{L^p} + \|D^m u\|_{L^p}$. Let $I$ be an open interval, $1 \le p \le \infty$ and
$m \ge 1$. There is a constant $C$ such that
$$\|u\|_{L^p} + \|D^m u\|_{L^p} \le \|u\|_{W^{m,p}} \le C (\|u\|_{L^p} + \|D^m u\|_{L^p}) \quad
  \text{for all } u \in W^{m,p}(I).$$

The source states this consequence of the interpolation inequality before the inequality. The
order $m \ge 1$ is written `m + 1` with `m : ℕ`. The proof specializes
`SobolevIntervalLp.exists_norm_le_mul_norm_deriv_add`. -/
theorem interpolationInequality_norm_equiv (hI : (I : Set ℝ).OrdConnected) (m : ℕ) :
    ∃ C : ℝ, ∀ u : SobolevIntervalLp (m + 1) p I,
      ‖u.deriv 0‖ + ‖u.deriv (Fin.last (m + 1))‖ ≤ sobolevNormHigher u ∧
      sobolevNormHigher u ≤ C * (‖u.deriv 0‖ + ‖u.deriv (Fin.last (m + 1))‖) := by
  obtain ⟨C, hC0, hC⟩ := SobolevIntervalLp.exists_norm_le_mul_norm_deriv_add (p := p) hI (m + 1)
  refine ⟨(m + 1 + 1) * C, fun u ↦ ⟨?_, ?_⟩⟩
  · unfold sobolevNormHigher
    have : ‖u.deriv (Fin.last (m + 1))‖ ≤ ∑ j : Fin (m + 1), ‖u.deriv j.succ‖ := by
      rw [← Fin.succ_last]
      exact Finset.single_le_sum (f := fun j : Fin (m + 1) ↦ ‖u.deriv j.succ‖)
        (fun j _ ↦ norm_nonneg _) (Finset.mem_univ (Fin.last m))
    linarith
  · calc sobolevNormHigher u ≤ (m + 1 + 1) * ‖u‖ := by
          have := (sobolevNormHigher_equiv u).2
          push_cast at this
          exact this
      _ ≤ (m + 1 + 1) * (C * (‖u.deriv 0‖ + ‖u.deriv (Fin.last (m + 1))‖)) := by
          gcongr
          exact hC u
      _ = (m + 1 + 1) * C * (‖u.deriv 0‖ + ‖u.deriv (Fin.last (m + 1))‖) := by ring

/-- **Section 8.2** of [brezis2011functional], the Sobolev spaces $W^{m,p}$, the closing sentence:
$W^{m,p}(I) \subseteq C^{m-1}(\bar I)$ with continuous injection for a bounded interval $I$. Let
$a < b$, $1 \le p \le \infty$ and $m \in \mathbb{N}$. The bounded linear map
$W^{m+1,p}((a, b)) \to C^m([a, b])$, `SobolevIntervalLp.toContDiffMapIcc`, is injective, and it
maps every $u$ to a $C^m$ function on $[a, b]$ that equals $u$ almost everywhere on $(a, b)$.

The map sends $u$ to the continuous representatives of $u, u', \dots, u^{(m)}$. The space
$C^m([a, b])$ is `ContDiffMapIcc hab.le m`, and a function on $[a, b]$ is read on $\mathbb{R}$
through `ContDiffMapIcc.extend`. -/
theorem sobolevSpaceHigher_subset_contDiff {a b : ℝ} (hab : a < b) {m : ℕ} :
    Function.Injective (SobolevIntervalLp.toContDiffMapIcc (p := p) (m := m) hab) ∧
      ∀ u : SobolevIntervalLp (m + 1) p (Opens.Ioo a b),
        u.fn =ᵐ[volume.restrict (Ioo a b)] (SobolevIntervalLp.toContDiffMapIcc hab u).extend := by
  refine ⟨SobolevIntervalLp.toContDiffMapIcc_injective hab, fun u ↦ ?_⟩
  have h1 := SobolevIntervalLp.fn_ae_eq_rep (SobolevIntervalLp.ordConnected_coe_Ioo a b)
    (SobolevIntervalLp.derivOne u 0)
  rw [SobolevIntervalLp.fn_derivOne_zero] at h1
  refine h1.trans ((ae_restrict_mem measurableSet_Ioo).mono fun x hx ↦ ?_)
  rw [ContDiffMapIcc.extend_of_mem _ (Ioo_subset_Icc_self hx),
    SobolevIntervalLp.toContDiffMapIcc_apply]

/-- **Section 8.2** of [brezis2011functional], the Sobolev spaces $W^{m,p}$, the closing sentence,
compactness. Let $a < b$, $1 < p \le \infty$ and $m \in \mathbb{N}$. The injection
$W^{m+1,p}((a, b)) \to C^m([a, b])$ is a compact operator. So
$W^{m,p}(I) \subseteq C^{m-1}(\bar I)$ is compact for a bounded interval $I$.

The proof specializes `SobolevIntervalLp.isCompactOperator_toContDiffMapIcc`. -/
theorem sobolevSpaceHigher_subset_contDiff_compact {a b : ℝ} (hab : a < b) {m : ℕ} (hp : 1 < p) :
    IsCompactOperator (SobolevIntervalLp.toContDiffMapIcc (p := p) (m := m) hab) :=
  SobolevIntervalLp.isCompactOperator_toContDiffMapIcc hab hp

end Brezis.Chapter08
