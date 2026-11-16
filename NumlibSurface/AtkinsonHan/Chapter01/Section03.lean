/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.OfNorm
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Numlib.Analysis.Fourier.CosineBasis
import Numlib.Analysis.Fourier.TrigonometricBasis
import Numlib.Analysis.Sobolev.Interval
import Numlib.Approximation.OrthogonalPolynomial
import NumlibSurface.AtkinsonHan.Chapter01.Section01
import NumlibSurface.AtkinsonHan.Chapter01.Section02

/-!
# Atkinson and Han, Section 1.3: Inner product spaces

This module formalizes §1.3 of [han2009theoretical]: inner products and inner product spaces, the
Cauchy–Schwarz inequality, the parallelogram law as the characterization of norms that come from an
inner product, Hilbert spaces and their standard examples, orthogonality and orthogonal complements,
orthonormal systems and bases with Bessel's inequality and Parseval's equality, the trigonometric
and half-range cosine bases, and the Gram–Schmidt process. Applied to the monomials $1, x, x^2, x^3$
in $L^2(-1, 1)$, the Gram–Schmidt process gives the first four normalized Legendre polynomials
$\sqrt{(2n + 1)/2} \, P_n$.

Definitions 1.3.1, 1.3.5, 1.3.8, 1.3.9 and 1.3.10 are Mathlib's `InnerProductSpace`,
`CompleteSpace`, the condition `inner 𝕜 v u = 0`, `Submodule.orthogonal` and `Orthonormal`, and each
is restated here under the number of the book. The trigonometric and cosine bases, the Sobolev space
$H^m(a, b)$ and the Legendre polynomials come from the backbone modules
`Numlib.Analysis.Fourier.TrigonometricBasis`, `Numlib.Analysis.Fourier.CosineBasis`,
`Numlib.Analysis.Sobolev.Interval` and `Numlib.Approximation.OrthogonalPolynomial`.

## Main definitions

* Definition 1.3.8, `AtkinsonHan.Chapter01.definition_1_3_8`: $u$ and $v$ are orthogonal.
* Definition 1.3.9, `AtkinsonHan.Chapter01.definition_1_3_9`: the orthogonal complement of a subset.
* Definition 1.3.10, `AtkinsonHan.Chapter01.definition_1_3_10` and
  `AtkinsonHan.Chapter01.definition_1_3_10_basis`: an orthonormal system, and an orthonormal basis,
  that is, an orthonormal system that is a basis in the sense of Definition 1.2.20.
* Example 1.3.17, `AtkinsonHan.Chapter01.monomialLp`: the monomials $1, x, x^2, \dots$ as elements
  of $L^2(-1, 1)$.

## Main results

* Definition 1.3.1, `AtkinsonHan.Chapter01.definition_1_3_1`: a Mathlib inner product satisfies the
  three axioms of an inner product.
* Theorem 1.3.2, `AtkinsonHan.Chapter01.theorem_1_3_2`: the Cauchy–Schwarz inequality, with its case
  of equality.
* Proposition 1.3.3, `AtkinsonHan.Chapter01.proposition_1_3_3`: the inner product is continuous in
  both arguments.
* Theorem 1.3.4, `AtkinsonHan.Chapter01.theorem_1_3_4`: a norm comes from an inner product if and
  only if it satisfies the parallelogram law (1.3.3).
* Definition 1.3.5, `AtkinsonHan.Chapter01.definition_1_3_5`: a Hilbert space is an inner product
  space that is complete for the norm $\|v\| = \sqrt{(v, v)}$.
* Example 1.3.6, `AtkinsonHan.Chapter01.example_1_3_6`: $\mathbb{C}^d$, $\ell^2$ and $L^2(\mu)$ are
  Hilbert spaces, with the inner products of the book.
* Example 1.3.7, `AtkinsonHan.Chapter01.example_1_3_7`: $H^m(a, b)$ is a Hilbert space with the
  inner product $\sum_{j \le m} (f^{(j)}, g^{(j)})_{L^2(a, b)}$.
* Definition 1.3.8, `AtkinsonHan.Chapter01.definition_1_3_8_pythagoras`: orthogonal vectors satisfy
  $\|u + v\|^2 = \|u\|^2 + \|v\|^2$.
* Definition 1.3.9, `AtkinsonHan.Chapter01.definition_1_3_9_iff`,
  `AtkinsonHan.Chapter01.definition_1_3_9_isClosed` and
  `AtkinsonHan.Chapter01.definition_1_3_9_isSubspace`: the orthogonal complement is
  `Submodule.orthogonal`, and it is a closed subspace.
* Definition 1.3.10, `AtkinsonHan.Chapter01.definition_1_3_10_iff`: Definition 1.3.10 is
  `Orthonormal`.
* Theorem 1.3.11, `AtkinsonHan.Chapter01.theorem_1_3_11`: Bessel's inequality, the convergence of
  the expansion $\sum_j (u, v_j) v_j$, and the uniqueness of its coefficients.
* Theorem 1.3.12, `AtkinsonHan.Chapter01.theorem_1_3_12`: for an orthonormal system, density of the
  span, the generalized Parseval identity and Parseval's equality are equivalent.
* Theorem 1.3.13, `AtkinsonHan.Chapter01.theorem_1_3_13`: the real trigonometric system is an
  orthonormal basis of $L^2(-\pi, \pi)$.
* Example 1.3.14, `AtkinsonHan.Chapter01.example_1_3_14`: the half-range cosine system is an
  orthonormal basis of $L^2(0, \pi)$.
* Theorem 1.3.16, `AtkinsonHan.Chapter01.theorem_1_3_16`: the Gram–Schmidt process, with the
  equality (1.3.11) of the spans.
* Example 1.3.17, `AtkinsonHan.Chapter01.example_1_3_17`: the Gram–Schmidt process applied to
  $1, x, x^2, x^3$ in $L^2(-1, 1)$ gives the four orthonormal polynomials that the book displays,
  which are normalized Legendre polynomials.

## Conventions

* The book's inner product $(u, v)$ is linear in its first argument, and Mathlib's `inner 𝕜 u v` is
  linear in its second argument. The book's $(u, v)$ is therefore `inner 𝕜 v u`. The doc comments
  use the notation of the book, and the Lean statements contain the swap.
* The space $L^2(-1, 1)$ is `Lp ℝ 2 (volume.restrict (Set.Ioo (-1) 1))`. Its elements are classes of
  functions, so the displayed formulas of Example 1.3.17 are equalities almost everywhere.
* The Sobolev space $H^m(a, b)$ is the backbone's `SobolevInterval m a b`.

## Implementation notes

* A Hilbert space is an inner product space with `CompleteSpace`; Mathlib has no bundled Hilbert
  space.
* Theorem 1.3.13 is stated on $L^2$ of the circle `AddCircle (2 * π)` with its probability Haar
  measure. For $2\pi$-periodic functions this is $L^2(-\pi, \pi)$ with Lebesgue measure divided by
  $2\pi$. The scaling turns the book's system $1/\sqrt{2\pi}$, $\cos(jx)/\sqrt\pi$,
  $\sin(jx)/\sqrt\pi$ into the system $1$, $\sqrt 2 \cos(jx)$, $\sqrt 2 \sin(jx)$ of the backbone's
  `trigFun`.
* Example 1.3.17 is computed. The recursion `gramSchmidtNormed` is unfolded four steps on the
  monomials, and each inner product and norm is the integral of a polynomial over $(-1, 1)$. The
  result is matched against `Polynomial.legendre`, the Legendre family $P_n$ that §3.5 also uses:
  the book's orthonormal polynomials are $\sqrt{(2n + 1)/2} \, P_n$.
* The space $H^m(a, b)$ is defined by weak derivatives, the description that the book gives in
  Chapter 7, rather than as the completion of $C^m[a, b]$, which Example 1.2.28(b) takes as the
  definition. The two agree because $C^m[a, b]$ is dense in $H^m(a, b)$. For this type the density
  is proved only for $m = 1$ on $(0, 1)$, as `AtkinsonHan.Chapter02.example_2_4_2_dense`.

## Not formalized

* **Example 1.3.15**, the convergence in $L^2$ of the real Fourier series. It is not restated here;
  the backbone states it as `hasSum_trigSeries`.
* **The identity after Definition 1.3.8** for $n$ mutually orthogonal elements, $\|u_1 + \dots +
  u_n\|^2 = \|u_1\|^2 + \dots + \|u_n\|^2$. Only the case $n = 2$ is stated.
-/

open Filter InnerProductSpace MeasureTheory Submodule Topology

open scoped Real

namespace AtkinsonHan.Chapter01

section InnerProduct

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- **Definition 1.3.1** of [han2009theoretical]. An **inner product** on a linear space $V$ over
$\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$ is a map $(\cdot, \cdot) : V \times V \to \mathbb{K}$
with three properties: $(v, v) \ge 0$, and $(v, v) = 0$ only for $v = 0$;
$(u, v) = \overline{(v, u)}$; and $(\alpha u + \beta v, w) = \alpha (u, w) + \beta (v, w)$. The
space with the inner product is an **inner product space**. The theorem states that every
Mathlib inner product has these three properties, with $(v, v) \ge 0$ in the form
$\operatorname{Re}(v, v) \ge 0$.

The inner product space is `InnerProductSpace 𝕜 E`. The book's $(u, v)$ is `inner 𝕜 v u`, so the
book's linearity in the first argument is Mathlib's linearity in the second argument. By the
second property $(v, v)$ is real, so $\operatorname{Re}(v, v) \ge 0$ is the book's
$(v, v) \ge 0$. -/
theorem definition_1_3_1 (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] :
    (∀ v : E, 0 ≤ RCLike.re (inner 𝕜 v v) ∧ (inner 𝕜 v v = (0 : 𝕜) ↔ v = 0)) ∧
      (∀ u v : E, inner 𝕜 v u = starRingEnd 𝕜 (inner 𝕜 u v)) ∧
      (∀ (u v w : E) (α β : 𝕜),
        inner 𝕜 w (α • u + β • v) = α * inner 𝕜 w u + β * inner 𝕜 w v) := by
  refine ⟨fun v => ⟨?_, inner_self_eq_zero⟩, fun u v => (inner_conj_symm v u).symm,
    fun u v w α β => ?_⟩
  · rw [inner_self_eq_norm_sq]
    positivity
  · rw [inner_add_right, inner_smul_right, inner_smul_right]

/-- **Theorem 1.3.2** of [han2009theoretical] (Cauchy–Schwarz inequality). Let $V$ be an inner
product space and $u, v \in V$. Then $$|(u, v)| \le \|u\| \, \|v\|,$$ with equality if and only
if $u$ and $v$ are linearly dependent. -/
theorem theorem_1_3_2 (u v : E) :
    ‖inner 𝕜 u v‖ ≤ ‖u‖ * ‖v‖ ∧
      (‖inner 𝕜 u v‖ = ‖u‖ * ‖v‖ ↔ ¬ LinearIndependent 𝕜 ![u, v]) := by
  refine ⟨norm_inner_le_norm (𝕜 := 𝕜) (E := E) u v, ?_⟩
  have hdep : ¬ LinearIndependent 𝕜 ![u, v] ↔ (v = 0 ∨ ∃ a : 𝕜, a • v = u) := by
    rw [linearIndependent_fin2]
    constructor
    · intro h
      by_cases hv : v = 0
      · exact Or.inl hv
      · push Not at h
        exact Or.inr (h hv)
    · rintro (rfl | ⟨a, rfl⟩) h
      · exact h.1 rfl
      · exact h.2 a rfl
  rw [hdep]
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  rcases eq_or_ne u 0 with rfl | hu
  · simp
  rw [norm_inner_eq_norm_iff hu hv]
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact Or.inr ⟨r⁻¹, by rw [smul_smul, inv_mul_cancel₀ hr, one_smul]⟩
  · rintro (h | ⟨a, ha⟩)
    · exact absurd h hv
    · have ha0 : a ≠ 0 := by
        rintro rfl
        exact hu (by simpa using ha.symm)
      exact ⟨a⁻¹, inv_ne_zero ha0, by rw [← ha, smul_smul, inv_mul_cancel₀ ha0, one_smul]⟩

/-- **Proposition 1.3.3** of [han2009theoretical]. The inner product is continuous in both
arguments: if $u_n \to u$ and $v_n \to v$ in an inner product space, then
$(u_n, v_n) \to (u, v)$.

The limits are `x` and `y` in the Lean statement. -/
theorem proposition_1_3_3 {u v : ℕ → E} {x y : E} (hu : Tendsto u atTop (𝓝 x))
    (hv : Tendsto v atTop (𝓝 y)) :
    Tendsto (fun n => inner 𝕜 (u n) (v n)) atTop (𝓝 (inner 𝕜 x y)) :=
  hu.inner hv

end InnerProduct

/-- **Theorem 1.3.4** of [han2009theoretical] (Fréchet–von Neumann–Jordan). The norm of a normed
space $V$ over $\mathbb{K}$ is induced by an inner product if and only if it satisfies the
parallelogram law (1.3.3), $$\|u + v\|^2 + \|u - v\|^2 = 2 \big(\|u\|^2 + \|v\|^2\big) \qquad
\text{for all } u, v \in V.$$

An inner product that induces the given norm is a structure `InnerProductSpace 𝕜 E` on the
normed space, so the left side is `Nonempty (InnerProductSpace 𝕜 E)`. -/
theorem theorem_1_3_4 (𝕜 : Type*) [RCLike 𝕜] (E : Type*) [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] :
    Nonempty (InnerProductSpace 𝕜 E) ↔
      ∀ u v : E, ‖u + v‖ ^ 2 + ‖u - v‖ ^ 2 = 2 * (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
  constructor
  · rintro ⟨_⟩ u v
    exact parallelogram_law_with_norm (𝕜 := 𝕜) (E := E) u v
  · intro h
    have : InnerProductSpaceable E := ⟨fun u v => by
      simpa only [← pow_two] using h u v⟩
    exact nonempty_innerProductSpace 𝕜 E

section Hilbert0

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- **Definition 1.3.5** of [han2009theoretical]. A **Hilbert space** is an inner product space that
is a Banach space for the induced norm $\|v\| = \sqrt{(v, v)}$. The theorem states that the norm
of an inner product space is $\|v\| = \sqrt{\operatorname{Re}(v, v)}$, and that the space is
complete (`CompleteSpace`) if and only if every Cauchy sequence converges, as in Definition
1.2.24.

Mathlib has no bundled Hilbert space. This library assumes `CompleteSpace E` together with
`InnerProductSpace 𝕜 E` instead. -/
theorem definition_1_3_5 (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] :
    (∀ v : E, ‖v‖ = √(RCLike.re (inner 𝕜 v v))) ∧
      (CompleteSpace E ↔ ∀ u : ℕ → E, definition_1_2_21 u → ∃ v : E, definition_1_2_8 u v) :=
  ⟨fun v => by rw [inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg v)], definition_1_2_24 E⟩

/-- **Example 1.3.6** of [han2009theoretical]. Let $d \in \mathbb{N}$ and let $\mu$ be a measure.
The following are Hilbert spaces: $\mathbb{C}^d$ with
$(x, y) = \sum_{i=1}^d x_i \overline{y_i}$; the sequence space $\ell^2$ with
$(x, y) = \sum_i x_i \overline{y_i}$; and $L^2(\mu)$ with
$(u, v) = \int u \, \overline{v} \, d\mu$.

The spaces $L^2(0, 1)$, $L^2(\Omega)$ and the weighted space $L^2_w(\Omega)$ of the book are
instances of $L^2(\mu)$; the weighted space is the case `μ = ν.withDensity w`. The space
$\mathbb{C}^d$ is `EuclideanSpace ℂ (Fin d)`. The sequence space is `lp (fun _ : ℕ => ℂ) 2`,
indexed from $0$. -/
theorem example_1_3_6 (d : ℕ) {α : Type*} [MeasurableSpace α] (μ : Measure α) :
    ((∀ x y : EuclideanSpace ℂ (Fin d), inner ℂ y x = ∑ i, x i * starRingEnd ℂ (y i)) ∧
        CompleteSpace (EuclideanSpace ℂ (Fin d))) ∧
      ((∀ x y : lp (fun _ : ℕ => ℂ) 2, inner ℂ y x = ∑' i, x i * starRingEnd ℂ (y i)) ∧
        CompleteSpace (lp (fun _ : ℕ => ℂ) 2)) ∧
      ((∀ u v : Lp ℂ 2 μ, inner ℂ v u = ∫ a, u a * starRingEnd ℂ (v a) ∂μ) ∧
        CompleteSpace (Lp ℂ 2 μ)) := by
  refine ⟨⟨fun x y => ?_, inferInstance⟩, ⟨fun x y => ?_, inferInstance⟩,
    ⟨fun u v => ?_, inferInstance⟩⟩
  · rw [PiLp.inner_apply]
    exact Finset.sum_congr rfl fun i _ => by rw [RCLike.inner_apply, mul_comm]
  · rw [lp.inner_eq_tsum]
    exact tsum_congr fun i => by rw [RCLike.inner_apply, mul_comm]
  · rw [L2.inner_def]
    refine integral_congr_ae (Eventually.of_forall fun a => ?_)
    simp [RCLike.inner_apply]

/-- **Example 1.3.7** of [han2009theoretical]. Let $m \in \mathbb{N}$ and $a, b \in \mathbb{R}$. The
Sobolev space $H^m(a, b) = W^{m,2}(a, b)$ is a Hilbert space, with the inner product $$(f,
g)_{H^m} = \sum_{j=0}^m \big(f^{(j)}, g^{(j)}\big)_{L^2(a, b)}.$$

The space is the backbone's `SobolevInterval m a b`, and $f^{(j)}$ is the weak derivative
`SobolevInterval.deriv f j`. The embedding $H^1(a, b) \subseteq C[a, b]$ that the book recalls
from Exercise 1.2.20 is the backbone's `SobolevInterval.toContinuousMap`. -/
theorem example_1_3_7 (m : ℕ) (a b : ℝ) :
    (∀ f g : SobolevInterval m a b, inner ℝ g f =
        ∑ j : Fin (m + 1), inner ℝ (SobolevInterval.deriv g j) (SobolevInterval.deriv f j)) ∧
      CompleteSpace (SobolevInterval m a b) :=
  ⟨fun f g => SobolevInterval.inner_eq g f, inferInstance⟩

/-- **Definition 1.3.8** of [han2009theoretical]. Two vectors $u$ and $v$ of an inner product space
are **orthogonal** if $(u, v) = 0$. A vector $v$ is orthogonal to a subset $U$ if it is
orthogonal to every $u \in U$, that is, if $v \in U^\perp$ in the sense of Definition 1.3.9.

The condition is `inner 𝕜 v u = 0`, with the arguments swapped as everywhere in this module. The
identity that the book records after the definition, $\|u_1 + \dots + u_n\|^2 = \|u_1\|^2 +
\dots + \|u_n\|^2$ for mutually orthogonal elements, is
`AtkinsonHan.Chapter01.definition_1_3_8_pythagoras` for $n = 2$. -/
def definition_1_3_8 (𝕜 : Type*) {E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (u v : E) : Prop :=
  inner 𝕜 v u = (0 : 𝕜)

/-- Pythagoras' theorem: if $u$ and $v$ are orthogonal in the sense of Definition 1.3.8 of
[han2009theoretical], then $\|u + v\|^2 = \|u\|^2 + \|v\|^2$. This is the case of two terms of
the identity that the book records after Definition 1.3.8. -/
theorem definition_1_3_8_pythagoras {u v : E} (h : definition_1_3_8 𝕜 u v) :
    ‖u + v‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 := by
  have h' : inner 𝕜 u v = (0 : 𝕜) := by rw [← inner_conj_symm u v, h, map_zero]
  simpa [pow_two] using norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := 𝕜) u v h'

/-- **Definition 1.3.9** of [han2009theoretical]. The **orthogonal complement** of a subset $U$ of
an inner product space $V$ is $$U^\perp = \{v \in V : (v, u) = 0 \text{ for all } u \in U\}.$$
It is always a closed subspace.

For a submodule $U$ this is `Submodule.orthogonal` by
`AtkinsonHan.Chapter01.definition_1_3_9_iff`. It is closed by
`AtkinsonHan.Chapter01.definition_1_3_9_isClosed` and a subspace by
`AtkinsonHan.Chapter01.definition_1_3_9_isSubspace`. -/
def definition_1_3_9 (𝕜 : Type*) {E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (U : Set E) : Set E :=
  {v | ∀ u ∈ U, definition_1_3_8 𝕜 v u}

/-- For a submodule $U$ of an inner product space, the orthogonal complement $U^\perp$ in the sense
of Definition 1.3.9 of [han2009theoretical] is the carrier of `Submodule.orthogonal U`. -/
theorem definition_1_3_9_iff (U : Submodule 𝕜 E) :
    definition_1_3_9 𝕜 (U : Set E) = (Uᗮ : Set E) := by
  ext v
  simp [definition_1_3_9, definition_1_3_8, Submodule.mem_orthogonal]

/-- For every subset $U$ of an inner product space, the orthogonal complement $U^\perp$ of
Definition 1.3.9 of [han2009theoretical] is closed. -/
theorem definition_1_3_9_isClosed (U : Set E) : IsClosed (definition_1_3_9 𝕜 U) := by
  have h : definition_1_3_9 𝕜 U = ⋂ u ∈ U, (fun v => inner 𝕜 u v) ⁻¹' {(0 : 𝕜)} := by
    ext v
    simp [definition_1_3_9, definition_1_3_8]
  rw [h]
  exact isClosed_biInter fun u _ => isClosed_singleton.preimage (innerSL 𝕜 u).continuous

/-- For every subset $U$ of an inner product space, the orthogonal complement $U^\perp$ of
Definition 1.3.9 of [han2009theoretical] is a subspace in the sense of Definition 1.1.3. -/
theorem definition_1_3_9_isSubspace (U : Set E) :
    definition_1_1_3 𝕜 (definition_1_3_9 𝕜 U) := by
  refine ⟨fun v hv w hw u hu => ?_, fun α v hv u hu => ?_⟩
  · have h1 : inner 𝕜 u v = (0 : 𝕜) := hv u hu
    have h2 : inner 𝕜 u w = (0 : 𝕜) := hw u hu
    change inner 𝕜 u (v + w) = (0 : 𝕜)
    rw [inner_add_right, h1, h2, add_zero]
  · have h1 : inner 𝕜 u v = (0 : 𝕜) := hv u hu
    change inner 𝕜 u (α • v) = (0 : 𝕜)
    rw [inner_smul_right, h1, mul_zero]

/-- **Definition 1.3.10** of [han2009theoretical]. A sequence $\{v_i\}_{i \ge 0}$ in an inner
product space is an **orthonormal system** if $(v_i, v_j) = \delta_{ij}$ for all $i, j$. It is
an **orthonormal basis** if, in addition, it is a basis in the sense of Definition 1.2.20.

The predicate is `Orthonormal` by `AtkinsonHan.Chapter01.definition_1_3_10_iff`. The orthonormal
basis is `AtkinsonHan.Chapter01.definition_1_3_10_basis`; Mathlib's counterpart is
`HilbertBasis`. -/
def definition_1_3_10 (𝕜 : Type*) {E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (v : ℕ → E) : Prop :=
  ∀ i j, inner 𝕜 (v i) (v j) = if i = j then (1 : 𝕜) else 0

/-- A sequence in an inner product space is an orthonormal system in the sense of Definition 1.3.10
of [han2009theoretical] if and only if it is `Orthonormal`. -/
theorem definition_1_3_10_iff (v : ℕ → E) : definition_1_3_10 𝕜 v ↔ Orthonormal 𝕜 v :=
  orthonormal_iff_ite.symm

/-- **Definition 1.3.10** of [han2009theoretical], orthonormal basis. A sequence $\{v_i\}_{i \ge 0}$
in an inner product space is an **orthonormal basis** if it is an orthonormal system and a
countably-infinite basis in the sense of Definition 1.2.20(a). -/
def definition_1_3_10_basis (𝕜 : Type*) {E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (v : ℕ → E) : Prop :=
  definition_1_3_10 𝕜 v ∧ definition_1_2_20 𝕜 v

end Hilbert0

section Hilbert

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable {ι : Type*} {v : ι → E}

/-- **Theorem 1.3.11** of [han2009theoretical]. Let $V$ be a Hilbert space, let
$\{v_j\}_{j \in \iota}$ be an orthonormal system in $V$, and let $u \in V$. Then:

(a) Bessel's inequality holds: $\sum_j |(u, v_j)|^2 \le \|u\|^2$;

(b) the series $\sum_j (u, v_j) v_j$ converges;

(c) if $u = \sum_j a_j v_j$ for scalars $a_j$, then $a_j = (u, v_j)$ for every $j$.

The index set $\iota$ is arbitrary, and the series are unordered sums (`tsum`, `Summable` and
`HasSum`). -/
theorem theorem_1_3_11 (hv : Orthonormal 𝕜 v) (u : E) :
    ∑' i, ‖inner 𝕜 (v i) u‖ ^ 2 ≤ ‖u‖ ^ 2 ∧
      Summable (fun i => inner 𝕜 (v i) u • v i) ∧
      ∀ a : ι → 𝕜, HasSum (fun i => a i • v i) u → ∀ j, a j = inner 𝕜 (v j) u := by
  classical
  refine ⟨hv.tsum_inner_products_le u, ?_, ?_⟩
  · have h := (hv.orthogonalFamily.summable_iff_norm_sq_summable
      (fun i => (inner 𝕜 (v i) u : 𝕜))).2 (by simpa using hv.inner_products_summable u)
    simpa [LinearIsometry.toSpanSingleton_apply] using h
  · intro a hsum j
    have h : HasSum (fun i => inner 𝕜 (v j) (a i • v i)) (inner 𝕜 (v j) u) :=
      hsum.mapL (innerSL 𝕜 (v j))
    have hterm : ∀ i, inner 𝕜 (v j) (a i • v i) = if i = j then a j else 0 := by
      intro i
      rw [inner_smul_right, orthonormal_iff_ite.mp hv j i]
      rcases eq_or_ne i j with rfl | hij
      · simp
      · rw [ite_eq_right (Ne.symm hij), ite_eq_right hij, mul_zero]
    simp only [hterm] at h
    exact (hasSum_ite_eq j (a j)).unique h

/-- **Theorem 1.3.12** of [han2009theoretical]. Let $\{v_j\}_{j \in \iota}$ be an orthonormal system
in a Hilbert space $V$. The following are equivalent:

(a) $\{v_j\}$ is an orthonormal basis, that is, the span of $\{v_j\}$ is dense in $V$;

(b) the generalized Parseval identity $(u, w) = \sum_j (u, v_j) (v_j, w)$ holds for all
$u, w \in V$;

(c) Parseval's equality $\|w\|^2 = \sum_j |(w, v_j)|^2$ holds for all $w \in V$.

Clause (a) is stated as the density of the span,
`(span 𝕜 (Set.range v)).topologicalClosure = ⊤`, and not through Definition 1.3.10. The index
set $\iota$ is arbitrary, and the series are unordered sums (`HasSum`). -/
theorem theorem_1_3_12 (hv : Orthonormal 𝕜 v) :
    List.TFAE
      [(span 𝕜 (Set.range v)).topologicalClosure = ⊤,
        ∀ u w : E, HasSum (fun i => inner 𝕜 u (v i) * inner 𝕜 (v i) w) (inner 𝕜 u w),
        ∀ w : E, HasSum (fun i => ‖inner 𝕜 (v i) w‖ ^ 2) (‖w‖ ^ 2)] := by
  tfae_have 1 → 2 := by
    intro h u w
    have hbot : (span 𝕜 (Set.range v))ᗮ = ⊥ := Submodule.topologicalClosure_eq_top_iff.mp h
    have h2 := (HilbertBasis.mkOfOrthogonalEqBot hv hbot).hasSum_inner_mul_inner u w
    rwa [HilbertBasis.coe_mkOfOrthogonalEqBot] at h2
  tfae_have 2 → 3 := by
    intro h w
    have h2 := (h w w).map (RCLike.re (K := 𝕜)) RCLike.continuous_re
    have key : ∀ i, RCLike.re (inner 𝕜 w (v i) * inner 𝕜 (v i) w)
        = ‖inner 𝕜 (v i) w‖ ^ 2 := by
      intro i
      rw [← inner_conj_symm w (v i), RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_re]
    simp only [Function.comp_def, key, inner_self_eq_norm_sq] at h2
    exact h2
  tfae_have 3 → 1 := by
    intro h
    rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
    intro w hw
    have hzero : ∀ i, inner 𝕜 (v i) w = 0 := by
      intro i
      have hmem : v i ∈ span 𝕜 (Set.range v) := subset_span ⟨i, rfl⟩
      exact (Submodule.mem_orthogonal _ _).mp hw _ hmem
    have h0 : HasSum (fun i : ι => ‖inner 𝕜 (v i) w‖ ^ 2) 0 := by
      simp [hzero]
    have hnorm : ‖w‖ ^ 2 = 0 := (h w).unique h0
    exact norm_eq_zero.mp ((pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hnorm)
  tfae_finish

end Hilbert

section Trigonometric

/-- **Theorem 1.3.13** of [han2009theoretical]. The real trigonometric system is an orthonormal
basis of $L^2(-\pi, \pi)$: it is orthonormal and its span is dense. For the probability measure
on the circle $\mathbb{R}/2\pi\mathbb{Z}$, the system consists of the constant $1$ and the
functions $\sqrt 2 \cos(jx)$ and $\sqrt 2 \sin(jx)$ for $j \ge 1$.

The basis is the backbone's `trigBasis (2 * π)`, a Hilbert basis indexed by $\mathbb{Z}$ of
$L^2$ on `AddCircle (2 * π)` with its probability Haar measure. Its members are the classes of
the continuous functions `trigFun (2 * π) n`: the constant for $n = 0$, the cosine for
$n = j > 0$ and the sine for $n = -j < 0$. The probability measure is Lebesgue measure on
$(-\pi, \pi)$ divided by $2\pi$, so these are the book's functions $1/\sqrt{2\pi}$,
$\cos(jx)/\sqrt\pi$ and $\sin(jx)/\sqrt\pi$, multiplied by $\sqrt{2\pi}$. -/
theorem theorem_1_3_13 :
    Orthonormal ℝ (trigBasis (2 * π)) ∧
      (span ℝ (Set.range ⇑(trigBasis (2 * π)))).topologicalClosure = ⊤ ∧
      (∀ x : AddCircle (2 * π), trigFun (2 * π) 0 x = 1) ∧
      (∀ j : ℤ, 0 < j → ∀ x : ℝ,
        trigFun (2 * π) j (x : AddCircle (2 * π)) = √2 * Real.cos (j * x)) ∧
      (∀ j : ℤ, 0 < j → ∀ x : ℝ,
        trigFun (2 * π) (-j) (x : AddCircle (2 * π)) = √2 * Real.sin (j * x)) := by
  refine ⟨(trigBasis (2 * π)).orthonormal, (trigBasis (2 * π)).dense_span, fun x => by simp,
    fun j hj x => trigFun_coe_of_pos hj x, fun j hj x => ?_⟩
  rw [trigFun_coe_of_neg (by omega : (-j : ℤ) < 0) x]
  push_cast
  ring_nf

/-- **Example 1.3.14** of [han2009theoretical]. The half-range cosine system $$e_0 =
\frac{1}{\sqrt\pi}, \qquad e_k(x) = \sqrt{\frac{2}{\pi}} \cos(kx) \quad (k \ge 1)$$ is an
orthonormal basis of $L^2(0, \pi)$: it is orthonormal, and its span is dense.

The space $L^2(0, \pi)$ is `Lp ℝ 2 halfRangeMeasure`, where `halfRangeMeasure` is Lebesgue
measure on $[0, \pi]$, read on the subtype. The member $e_k$ is `cosLp k`, the class of the
continuous function `cosFun k`. The proof in `Numlib.Analysis.Fourier.CosineBasis` uses the
Stone–Weierstrass theorem rather than the even extension that the book suggests: the span of the
functions $\cos(kx)$ is a subalgebra of $C[0, \pi]$ by the product-to-sum formula, and it
separates points because $\cos$ is injective on $[0, \pi]$. -/
theorem example_1_3_14 :
    Orthonormal ℝ cosLp ∧
      (span ℝ (Set.range cosLp)).topologicalClosure = ⊤ ∧
      (∀ k : ℕ, cosLp k = ContinuousMap.toLp 2 halfRangeMeasure ℝ (cosFun k)) ∧
      (∀ x : Set.Icc (0 : ℝ) π, cosFun 0 x = 1 / √π) ∧
      (∀ k : ℕ, k ≠ 0 → ∀ x : Set.Icc (0 : ℝ) π,
        cosFun k x = √(2 / π) * Real.cos (k * (x : ℝ))) :=
  ⟨orthonormal_cosLp, dense_span_cosLp, fun _ => rfl, cosFun_zero_apply,
    fun _ hk => cosFun_apply_of_ne_zero hk⟩

end Trigonometric

section GramSchmidt

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- **Theorem 1.3.16** of [han2009theoretical] (Gram–Schmidt process). Let $\{f_n\}_{n \ge 0}$ be a
linearly independent sequence in an inner product space $V$. Then there is an orthonormal
sequence $\{w_n\}_{n \ge 0}$ in $V$ with $$\operatorname{span}\{w_0, \dots, w_n\} =
\operatorname{span}\{f_0, \dots, f_n\} \qquad \text{for all } n \ge 0,$$ which is (1.3.11). -/
theorem theorem_1_3_16 {f : ℕ → E} (hf : LinearIndependent 𝕜 f) :
    ∃ w : ℕ → E, Orthonormal 𝕜 w ∧
      ∀ n : ℕ, span 𝕜 (w '' Set.Iic n) = span 𝕜 (f '' Set.Iic n) :=
  ⟨gramSchmidtNormed 𝕜 f, gramSchmidtNormed_orthonormal hf, fun n => by
    rw [span_gramSchmidtNormed f (Set.Iic n), span_gramSchmidt_Iic 𝕜 f n]⟩

end GramSchmidt

section Legendre

open Polynomial OrthogonalPolynomial

/-- Lebesgue measure on $(-1, 1)$ is a weight in the sense of the backbone: all its moments are
finite and it is not carried by a finite set, so every polynomial lies in $L^2(-1, 1)$. -/
private theorem isWeightIoo : IsWeight (volume.restrict (Set.Ioo (-1 : ℝ) 1)) :=
  isWeight_legendreMeasure

/-- A real polynomial as an element of $L^2(-1, 1)$, as a linear map. -/
private noncomputable def polyL2 : ℝ[X] →ₗ[ℝ] Lp ℝ 2 (volume.restrict (Set.Ioo (-1 : ℝ) 1)) :=
  isWeightIoo.toLpₗ

/-- The class `polyL2 p` is almost everywhere equal to the function $x \mapsto p(x)$. -/
private theorem coeFn_polyL2 (p : ℝ[X]) :
    ⇑(polyL2 p) =ᵐ[volume.restrict (Set.Ioo (-1 : ℝ) 1)] fun x => eval x p :=
  isWeightIoo.coeFn_toLpₗ p

/-- Multiplying a polynomial by a constant $c$ multiplies its class in $L^2(-1, 1)$ by $c$. -/
private theorem polyL2_C_mul (c : ℝ) (p : ℝ[X]) : polyL2 (C c * p) = c • polyL2 p := by
  rw [← Polynomial.smul_eq_C_mul, map_smul]

/-- The map from polynomials to $L^2(-1, 1)$ is injective, because a nonzero polynomial has positive
norm. -/
private theorem injective_polyL2 : Function.Injective polyL2 := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro p hp
  by_contra hne
  have hpos := isWeightIoo.integral_eval_sq_pos hne
  have hzero : inner ℝ (polyL2 p) (polyL2 p) = (0 : ℝ) := by rw [hp]; simp
  rw [polyL2, isWeightIoo.inner_toLpₗ] at hzero
  simp only [← pow_two] at hzero
  rw [hzero] at hpos
  exact lt_irrefl _ hpos

/-- An integral for Lebesgue measure on $(-1, 1)$ is the interval integral from $-1$ to $1$. -/
private theorem integral_Ioo (f : ℝ → ℝ) :
    ∫ x, f x ∂(volume.restrict (Set.Ioo (-1 : ℝ) 1)) = ∫ x in (-1 : ℝ)..1, f x :=
  integral_legendreMeasure f

/-- The integral over $(-1, 1)$ of the polynomial $\sum_{i=0}^6 a_i x^i$ is $2 a_0 + \frac{2}{3}
a_2 + \frac{2}{5} a_4 + \frac{2}{7} a_6$. -/
private theorem integral_poly (a : Fin 7 → ℝ) :
    (∫ x in (-1 : ℝ)..1, ∑ i : Fin 7, a i * x ^ (i : ℕ))
      = 2 * a 0 + 2 / 3 * a 2 + 2 / 5 * a 4 + 2 / 7 * a 6 := by
  rw [intervalIntegral.integral_finsetSum fun (i : Fin 7) _ =>
    (intervalIntegral.intervalIntegrable_pow (n := (i : ℕ))).const_mul (a i)]
  simp [Fin.sum_univ_seven, intervalIntegral.integral_const_mul, integral_pow]
  ring

/-- If $p(x) q(x) = \sum_{i=0}^6 a_i x^i$, then the inner product of $p$ and $q$ in $L^2(-1, 1)$ is
$2 a_0 + \frac{2}{3} a_2 + \frac{2}{5} a_4 + \frac{2}{7} a_6$. -/
private theorem inner_polyL2 (p q : ℝ[X]) (a₀ a₁ a₂ a₃ a₄ a₅ a₆ : ℝ)
    (h : ∀ x : ℝ, eval x p * eval x q
      = a₀ + a₁ * x + a₂ * x ^ 2 + a₃ * x ^ 3 + a₄ * x ^ 4 + a₅ * x ^ 5 + a₆ * x ^ 6) :
    inner ℝ (polyL2 p) (polyL2 q) = 2 * a₀ + 2 / 3 * a₂ + 2 / 5 * a₄ + 2 / 7 * a₆ := by
  rw [polyL2, isWeightIoo.inner_toLpₗ p q, integral_Ioo]
  simp only [h]
  have := integral_poly ![a₀, a₁, a₂, a₃, a₄, a₅, a₆]
  simpa [Fin.sum_univ_seven] using this

/-- If $p(x)^2 = \sum_{i=0}^6 a_i x^i$, then the squared norm of $p$ in $L^2(-1, 1)$ is $2 a_0 +
\frac{2}{3} a_2 + \frac{2}{5} a_4 + \frac{2}{7} a_6$. -/
private theorem normSq_polyL2 (p : ℝ[X]) (a₀ a₁ a₂ a₃ a₄ a₅ a₆ : ℝ)
    (h : ∀ x : ℝ, eval x p * eval x p
      = a₀ + a₁ * x + a₂ * x ^ 2 + a₃ * x ^ 3 + a₄ * x ^ 4 + a₅ * x ^ 5 + a₆ * x ^ 6) :
    ‖polyL2 p‖ ^ 2 = 2 * a₀ + 2 / 3 * a₂ + 2 / 5 * a₄ + 2 / 7 * a₆ := by
  rw [← real_inner_self_eq_norm_sq]
  exact inner_polyL2 p p a₀ a₁ a₂ a₃ a₄ a₅ a₆ h

/-- The monomial $x \mapsto x^n$ is square integrable on $(-1, 1)$. -/
private theorem memLp_pow (n : ℕ) :
    MemLp (fun x : ℝ => x ^ n) 2 (volume.restrict (Set.Ioo (-1 : ℝ) 1)) :=
  MemLp.ae_eq (by simp) (isWeightIoo.memLp (X ^ n))

/-- The monomials $x^n$, $n \ge 0$, as elements of $L^2(-1, 1)$. This is the sequence to which
Example 1.3.17 of [han2009theoretical] applies the Gram–Schmidt process of Theorem 1.3.16. -/
noncomputable def monomialLp (n : ℕ) : Lp ℝ 2 (volume.restrict (Set.Ioo (-1 : ℝ) 1)) :=
  MemLp.toLp _ (memLp_pow n)

/-- The class `AtkinsonHan.Chapter01.monomialLp n` is almost everywhere on $(-1, 1)$ equal to the
function $x \mapsto x^n$. -/
theorem coeFn_monomialLp (n : ℕ) :
    ⇑(monomialLp n) =ᵐ[volume.restrict (Set.Ioo (-1 : ℝ) 1)] fun x : ℝ => x ^ n :=
  MemLp.coeFn_toLp _

/-- The class `AtkinsonHan.Chapter01.monomialLp n` is the image of the polynomial $X^n$ in
$L^2(-1, 1)$. -/
private theorem monomialLp_eq (n : ℕ) : monomialLp n = polyL2 (X ^ n) := by
  refine Lp.ext_iff.2 ?_
  filter_upwards [coeFn_monomialLp n, coeFn_polyL2 (X ^ n)] with x h1 h2
  rw [h1, h2, eval_pow, eval_X]

/-- The Gram–Schmidt recursion: the vector number $n$ is $f_n - \sum_{i < n} \frac{(f_n,
w_i)}{\|w_i\|^2} w_i$, where $w_0, \dots, w_{n-1}$ are the earlier Gram–Schmidt vectors. -/
private theorem gramSchmidt_recurrence {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (f : ℕ → E) (n : ℕ) :
    gramSchmidt ℝ f n = f n - ∑ i ∈ Finset.range n,
      (inner ℝ (gramSchmidt ℝ f i) (f n) / ‖gramSchmidt ℝ f i‖ ^ 2) • gramSchmidt ℝ f i := by
  rw [eq_sub_iff_add_eq]
  simpa [Nat.Iio_eq_range] using (gramSchmidt_def'' ℝ f n).symm

/-- The first Gram–Schmidt vector of the monomials is the constant $1$. -/
private theorem gramSchmidt_monomialLp_zero : gramSchmidt ℝ monomialLp 0 = polyL2 1 := by
  rw [gramSchmidt_recurrence]
  simp [monomialLp_eq]

/-- The squared norm of the constant $1$ in $L^2(-1, 1)$ is $\int_{-1}^1 1 \, dx = 2$. -/
private theorem normSq_polyL2_one : ‖polyL2 1‖ ^ 2 = 2 := by
  rw [normSq_polyL2 _ 1 0 0 0 0 0 0 fun x => by simp]; norm_num

/-- The squared norm of $x$ in $L^2(-1, 1)$ is $\int_{-1}^1 x^2 \, dx = 2/3$. -/
private theorem normSq_polyL2_X : ‖polyL2 X‖ ^ 2 = 2 / 3 := by
  rw [normSq_polyL2 _ 0 0 1 0 0 0 0 fun x => by simp; ring]; norm_num

/-- The second Gram–Schmidt vector of the monomials is $x$, because $1$ and $x$ are orthogonal. -/
private theorem gramSchmidt_monomialLp_one : gramSchmidt ℝ monomialLp 1 = polyL2 X := by
  rw [gramSchmidt_recurrence, Finset.sum_range_one, gramSchmidt_monomialLp_zero]
  simp only [monomialLp_eq]
  rw [inner_polyL2 1 (X ^ 1) 0 1 0 0 0 0 0 fun x => by simp]
  simp

/-- The third Gram–Schmidt vector of the monomials is $x^2 - 1/3$, because the projection of $x^2$
onto $1$ is $(x^2, 1)/\|1\|^2 = 1/3$ and its projection onto $x$ is zero. -/
private theorem gramSchmidt_monomialLp_two :
    gramSchmidt ℝ monomialLp 2 = polyL2 (X ^ 2 - C (1 / 3)) := by
  rw [gramSchmidt_recurrence, Finset.sum_range_succ, Finset.sum_range_one,
    gramSchmidt_monomialLp_zero, gramSchmidt_monomialLp_one]
  simp only [monomialLp_eq]
  rw [inner_polyL2 1 (X ^ 2) 0 0 1 0 0 0 0 (fun x => by simp),
    inner_polyL2 X (X ^ 2) 0 0 0 1 0 0 0 (fun x => by simp; ring),
    normSq_polyL2_one, normSq_polyL2_X, map_sub, ← polyL2_C_mul, mul_one]
  norm_num

/-- The squared norm of $x^2 - 1/3$ in $L^2(-1, 1)$ is $8/45$. -/
private theorem normSq_polyL2_two : ‖polyL2 (X ^ 2 - C (1 / 3))‖ ^ 2 = 8 / 45 := by
  rw [normSq_polyL2 _ (1 / 9) 0 (-2 / 3) 0 1 0 0 fun x => by simp; ring]; norm_num

/-- The fourth Gram–Schmidt vector of the monomials is $x^3 - \frac{3}{5} x$, because only the
projection of $x^3$ onto $x$ is nonzero. -/
private theorem gramSchmidt_monomialLp_three :
    gramSchmidt ℝ monomialLp 3 = polyL2 (X ^ 3 - C (3 / 5) * X) := by
  rw [gramSchmidt_recurrence, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
    gramSchmidt_monomialLp_zero, gramSchmidt_monomialLp_one, gramSchmidt_monomialLp_two]
  simp only [monomialLp_eq]
  rw [inner_polyL2 1 (X ^ 3) 0 0 0 1 0 0 0 (fun x => by simp),
    inner_polyL2 X (X ^ 3) 0 0 0 0 1 0 0 (fun x => by simp; ring),
    inner_polyL2 (X ^ 2 - C (1 / 3)) (X ^ 3) 0 0 0 (-1 / 3) 0 1 0 (fun x => by simp; ring),
    normSq_polyL2_one, normSq_polyL2_X, normSq_polyL2_two]
  have hrhs : polyL2 (X ^ 3 - C (3 / 5) * X) = polyL2 (X ^ 3) - (3 / 5 : ℝ) • polyL2 X := by
    rw [map_sub, polyL2_C_mul]
  rw [hrhs]
  norm_num

/-- The squared norm of $x^3 - \frac{3}{5} x$ in $L^2(-1, 1)$ is $8/175$. -/
private theorem normSq_polyL2_three : ‖polyL2 (X ^ 3 - C (3 / 5) * X)‖ ^ 2 = 8 / 175 := by
  rw [normSq_polyL2 _ 0 0 (9 / 25) 0 (-6 / 5) 0 1 fun x => by simp; ring]; norm_num

/-- If the squared norm of a polynomial in $L^2(-1, 1)$ is $c$, then its norm is $\sqrt c$. -/
private theorem norm_polyL2_of_sq (p : ℝ[X]) (c : ℝ) (h : ‖polyL2 p‖ ^ 2 = c) :
    ‖polyL2 p‖ = √c := by
  rw [← h, Real.sqrt_sq (norm_nonneg _)]

/-- The first normalized Gram–Schmidt vector of the monomials is $(\sqrt 2)^{-1} \cdot 1$. -/
private theorem gramSchmidtNormed_monomialLp_zero :
    gramSchmidtNormed ℝ monomialLp 0 = (√2)⁻¹ • polyL2 1 := by
  rw [gramSchmidtNormed, gramSchmidt_monomialLp_zero,
    norm_polyL2_of_sq _ 2 normSq_polyL2_one, RCLike.ofReal_real_eq_id, id_eq]

/-- The second normalized Gram–Schmidt vector of the monomials is $(\sqrt{2/3})^{-1} x$. -/
private theorem gramSchmidtNormed_monomialLp_one :
    gramSchmidtNormed ℝ monomialLp 1 = (√(2 / 3))⁻¹ • polyL2 X := by
  rw [gramSchmidtNormed, gramSchmidt_monomialLp_one,
    norm_polyL2_of_sq _ _ normSq_polyL2_X, RCLike.ofReal_real_eq_id, id_eq]

/-- The third normalized Gram–Schmidt vector of the monomials is $(\sqrt{8/45})^{-1} (x^2 - 1/3)$.
-/
private theorem gramSchmidtNormed_monomialLp_two :
    gramSchmidtNormed ℝ monomialLp 2 = (√(8 / 45))⁻¹ • polyL2 (X ^ 2 - C (1 / 3)) := by
  rw [gramSchmidtNormed, gramSchmidt_monomialLp_two,
    norm_polyL2_of_sq _ _ normSq_polyL2_two, RCLike.ofReal_real_eq_id, id_eq]

/-- The fourth normalized Gram–Schmidt vector of the monomials is
$(\sqrt{8/175})^{-1} (x^3 - \frac{3}{5} x)$. -/
private theorem gramSchmidtNormed_monomialLp_three :
    gramSchmidtNormed ℝ monomialLp 3 = (√(8 / 175))⁻¹ • polyL2 (X ^ 3 - C (3 / 5) * X) := by
  rw [gramSchmidtNormed, gramSchmidt_monomialLp_three,
    norm_polyL2_of_sq _ _ normSq_polyL2_three, RCLike.ofReal_real_eq_id, id_eq]

/-- The class of $c \, p$ in $L^2(-1, 1)$ is almost everywhere equal to the function
$x \mapsto c \, p(x)$. -/
private theorem coeFn_smul_polyL2 (c : ℝ) (p : ℝ[X]) :
    ⇑(c • polyL2 p) =ᵐ[volume.restrict (Set.Ioo (-1 : ℝ) 1)] fun x => c * eval x p := by
  filter_upwards [Lp.coeFn_smul c (polyL2 p), coeFn_polyL2 p] with x h1 h2
  rw [h1, Pi.smul_apply, h2, smul_eq_mul]

/-- The identity $(\sqrt 2)^{-1} = 1/\sqrt 2$. -/
private theorem inv_sqrt_two : (√(2 : ℝ))⁻¹ = 1 / √2 := (one_div _).symm

/-- The identity $(\sqrt{2/3})^{-1} = \sqrt{3/2}$. -/
private theorem inv_sqrt_two_div_three : (√(2 / 3 : ℝ))⁻¹ = √(3 / 2) := by
  rw [← Real.sqrt_inv]; norm_num

/-- The identity $(\sqrt{8/45})^{-1} = \frac{3}{2} \sqrt{5/2}$. -/
private theorem inv_sqrt_eight_div_fortyFive : (√(8 / 45 : ℝ))⁻¹ = 3 / 2 * √(5 / 2) := by
  rw [← Real.sqrt_inv, show ((8 : ℝ) / 45)⁻¹ = (3 / 2) ^ 2 * (5 / 2) by norm_num,
    Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]

/-- The identity $(\sqrt{8/175})^{-1} = \frac{5}{2} \sqrt{7/2}$. -/
private theorem inv_sqrt_eight_div_oneSeventyFive : (√(8 / 175 : ℝ))⁻¹ = 5 / 2 * √(7 / 2) := by
  rw [← Real.sqrt_inv, show ((8 : ℝ) / 175)⁻¹ = (5 / 2) ^ 2 * (7 / 2) by norm_num,
    Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]

/-- The identity $\sqrt{1/2} = 1/\sqrt 2$. -/
private theorem sqrt_half : √(1 / 2 : ℝ) = 1 / √2 := by
  rw [one_div, Real.sqrt_inv, one_div]

/-- The Legendre polynomial $P_2$ satisfies $2 P_2 = 3 X^2 - 1$, by the Legendre recursion. -/
private theorem two_mul_legendre_two : 2 * legendre 2 = 3 * X ^ 2 - 1 := by
  have h := legendre_recurrence 0
  rw [legendre_zero, legendre_one] at h
  push_cast at h
  linear_combination h

/-- The Legendre polynomial $P_3$ satisfies $6 P_3 = 15 X^3 - 9 X$, by the Legendre recursion. -/
private theorem six_mul_legendre_three : 6 * legendre 3 = 15 * X ^ 3 - 9 * X := by
  have h := legendre_recurrence 1
  rw [legendre_one] at h
  push_cast at h
  linear_combination 2 * h + 5 * X * two_mul_legendre_two

/-- The Legendre polynomial $P_2$ has the values $P_2(x) = (3x^2 - 1)/2$. -/
private theorem eval_legendre_two (x : ℝ) : eval x (legendre 2) = (3 * x ^ 2 - 1) / 2 := by
  have h := congrArg (eval x) two_mul_legendre_two
  simp only [eval_mul, eval_ofNat, eval_sub, eval_pow, eval_X, eval_one] at h
  linarith

/-- The Legendre polynomial $P_3$ has the values $P_3(x) = (5x^3 - 3x)/2$. -/
private theorem eval_legendre_three (x : ℝ) : eval x (legendre 3) = (5 * x ^ 3 - 3 * x) / 2 := by
  have h := congrArg (eval x) six_mul_legendre_three
  simp only [eval_mul, eval_ofNat, eval_sub, eval_pow, eval_X] at h
  linarith

/-- The monomials are linearly independent in $L^2(-1, 1)$, so Theorem 1.3.16 applies to them. -/
private theorem linearIndependent_monomialLp : LinearIndependent ℝ monomialLp := by
  have h : LinearIndependent ℝ fun n : ℕ => (X : ℝ[X]) ^ n := by
    have hb := (Polynomial.basisMonomials ℝ).linearIndependent
    rw [Polynomial.coe_basisMonomials] at hb
    simpa [Polynomial.X_pow_eq_monomial] using hb
  rw [show monomialLp = fun n : ℕ => polyL2 (X ^ n) from funext monomialLp_eq]
  exact h.map' polyL2 (LinearMap.ker_eq_bot.2 injective_polyL2)

/-- The first orthonormal Gram–Schmidt vector of the monomials is almost everywhere the constant
$1/\sqrt 2$. -/
private theorem coeFn_gramSchmidtNormed_zero :
    ⇑(gramSchmidtNormed ℝ monomialLp 0)
      =ᵐ[volume.restrict (Set.Ioo (-1 : ℝ) 1)] fun _ : ℝ => 1 / √2 := by
  rw [gramSchmidtNormed_monomialLp_zero, inv_sqrt_two]
  filter_upwards [coeFn_smul_polyL2 (1 / √2) 1] with x hx
  rw [hx, eval_one, mul_one]

/-- The second orthonormal Gram–Schmidt vector of the monomials is almost everywhere the function
$\sqrt{3/2} \, x$. -/
private theorem coeFn_gramSchmidtNormed_one :
    ⇑(gramSchmidtNormed ℝ monomialLp 1)
      =ᵐ[volume.restrict (Set.Ioo (-1 : ℝ) 1)] fun x : ℝ => √(3 / 2) * x := by
  rw [gramSchmidtNormed_monomialLp_one, inv_sqrt_two_div_three]
  filter_upwards [coeFn_smul_polyL2 (√(3 / 2)) X] with x hx
  rw [hx, eval_X]

/-- The third orthonormal Gram–Schmidt vector of the monomials is almost everywhere the function
$\frac{3}{2} \sqrt{5/2} \, (x^2 - 1/3)$. -/
private theorem coeFn_gramSchmidtNormed_two :
    ⇑(gramSchmidtNormed ℝ monomialLp 2)
      =ᵐ[volume.restrict (Set.Ioo (-1 : ℝ) 1)]
        fun x : ℝ => 3 / 2 * √(5 / 2) * (x ^ 2 - 1 / 3) := by
  rw [gramSchmidtNormed_monomialLp_two, inv_sqrt_eight_div_fortyFive]
  filter_upwards [coeFn_smul_polyL2 (3 / 2 * √(5 / 2)) (X ^ 2 - C (1 / 3))] with x hx
  rw [hx]
  simp

/-- The fourth orthonormal Gram–Schmidt vector of the monomials is almost everywhere the function
$\frac{1}{2} \sqrt{7/2} \, (5x^3 - 3x)$. -/
private theorem coeFn_gramSchmidtNormed_three :
    ⇑(gramSchmidtNormed ℝ monomialLp 3)
      =ᵐ[volume.restrict (Set.Ioo (-1 : ℝ) 1)]
        fun x : ℝ => 1 / 2 * √(7 / 2) * (5 * x ^ 3 - 3 * x) := by
  rw [gramSchmidtNormed_monomialLp_three, inv_sqrt_eight_div_oneSeventyFive]
  filter_upwards [coeFn_smul_polyL2 (5 / 2 * √(7 / 2)) (X ^ 3 - C (3 / 5) * X)] with x hx
  rw [hx]
  simp only [eval_sub, eval_mul, eval_pow, eval_X, eval_C]
  ring

/-- For $n \le 3$, the orthonormal Gram–Schmidt vector number $n$ of the monomials is almost
everywhere $\sqrt{(2n + 1)/2} \, P_n$, the normalized Legendre polynomial. -/
private theorem coeFn_gramSchmidtNormed_legendre (n : ℕ) (hn : n ≤ 3) :
    ⇑(gramSchmidtNormed ℝ monomialLp n)
      =ᵐ[volume.restrict (Set.Ioo (-1 : ℝ) 1)]
        fun x : ℝ => √((2 * n + 1) / 2) * eval x (legendre n) := by
  interval_cases n
  · filter_upwards [coeFn_gramSchmidtNormed_zero] with x hx
    rw [hx, legendre_zero, eval_one, mul_one]
    norm_num [sqrt_half]
  · filter_upwards [coeFn_gramSchmidtNormed_one] with x hx
    rw [hx, legendre_one, eval_X]
    norm_num
  · filter_upwards [coeFn_gramSchmidtNormed_two] with x hx
    rw [hx, eval_legendre_two]
    norm_num
    ring
  · filter_upwards [coeFn_gramSchmidtNormed_three] with x hx
    rw [hx, eval_legendre_three]
    norm_num
    ring

/-- **Example 1.3.17** of [han2009theoretical]. The monomials $1, x, x^2, \dots$ are linearly
independent in $L^2(-1, 1)$, and the Gram–Schmidt process of Theorem 1.3.16 turns
$1, x, x^2, x^3$ into the orthonormal polynomials $$w_0 = \frac{1}{\sqrt 2}, \quad w_1 =
\sqrt{\frac{3}{2}} \, x, \quad w_2 = \frac{3}{2} \sqrt{\frac{5}{2}} \Big(x^2 - \frac{1}{3}\Big),
\quad w_3 = \frac{1}{2} \sqrt{\frac{7}{2}} \big(5x^3 - 3x\big).$$ For $n \le 3$,
$w_n = \sqrt{(2n + 1)/2} \, P_n$, where $P_n$ is the Legendre polynomial of degree $n$.

The vector $w_n$ is `gramSchmidtNormed ℝ AtkinsonHan.Chapter01.monomialLp n`, and $P_n$ is
`Polynomial.legendre n`. The normalization agrees with the orthogonality relation $\int_{-1}^1
P_m P_n \, dx = 2 \delta_{mn}/(2n + 1)$. The equalities hold almost everywhere, because an
element of $L^2(-1, 1)$ is a class of functions. -/
theorem example_1_3_17 :
    LinearIndependent ℝ monomialLp ∧
      (⇑(gramSchmidtNormed ℝ monomialLp 0)
        =ᵐ[volume.restrict (Set.Ioo (-1 : ℝ) 1)] fun _ : ℝ => 1 / √2) ∧
      (⇑(gramSchmidtNormed ℝ monomialLp 1)
        =ᵐ[volume.restrict (Set.Ioo (-1 : ℝ) 1)] fun x : ℝ => √(3 / 2) * x) ∧
      (⇑(gramSchmidtNormed ℝ monomialLp 2)
        =ᵐ[volume.restrict (Set.Ioo (-1 : ℝ) 1)]
          fun x : ℝ => 3 / 2 * √(5 / 2) * (x ^ 2 - 1 / 3)) ∧
      (⇑(gramSchmidtNormed ℝ monomialLp 3)
        =ᵐ[volume.restrict (Set.Ioo (-1 : ℝ) 1)]
          fun x : ℝ => 1 / 2 * √(7 / 2) * (5 * x ^ 3 - 3 * x)) ∧
      (∀ n ≤ 3, ⇑(gramSchmidtNormed ℝ monomialLp n)
        =ᵐ[volume.restrict (Set.Ioo (-1 : ℝ) 1)]
          fun x : ℝ => √((2 * n + 1) / 2) * eval x (legendre n)) :=
  ⟨linearIndependent_monomialLp, coeFn_gramSchmidtNormed_zero, coeFn_gramSchmidtNormed_one,
    coeFn_gramSchmidtNormed_two, coeFn_gramSchmidtNormed_three, coeFn_gramSchmidtNormed_legendre⟩

end Legendre

end AtkinsonHan.Chapter01
