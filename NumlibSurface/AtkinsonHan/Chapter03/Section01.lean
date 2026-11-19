/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Topology.ContinuousMap.Polynomial
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.ContinuousMap.Weierstrass
import Numlib.Analysis.Fourier.TrigonometricBasis
import Numlib.Approximation.Muntz

/-!
# Atkinson and Han, Section 3.1: The Weierstrass approximation theorems

This module formalizes Section 3.1 of [han2009theoretical], on the density of polynomials and
trigonometric polynomials in spaces of continuous functions. The polynomials are dense in $C[a, b]$
with the uniform norm (Weierstrass). More generally, a subalgebra of $C(D)$, for a compact $D$, that
separates the points of $D$ is dense (Stone–Weierstrass). Two corollaries follow: the polynomials in
$d$ variables are dense in $C(D)$ for a compact $D \subseteq \mathbb{R}^d$, and the trigonometric
polynomials are dense in $C_p(2\pi)$. Finally, for exponents
$0 < \lambda_1 < \lambda_2 < \cdots \to \infty$, the span of the powers $t^{\lambda_j}$ is dense in
$L^2(0, 1)$ if and only if $\sum_j 1/\lambda_j = \infty$ (Müntz).

The first two theorems are in Mathlib. Corollary 3.1.3 is Theorem 3.1.2 applied to the image of
`MvPolynomial (Fin d) ℝ` in $C(D)$, which contains the constants and separates points because the
coordinate functions do. Corollary 3.1.4 is the backbone's `exists_mem_span_trigFun_norm_sub_lt` of
`Numlib.Analysis.Fourier.TrigonometricBasis`, and Theorem 3.1.5 is the backbone's
`Muntz.dense_span_powerL2_iff` of `Numlib.Approximation.Muntz`.

## Main results

* Theorem 3.1.1, `AtkinsonHan.Chapter03.theorem_3_1_1`: the polynomials are dense in $C[a, b]$.
* Theorem 3.1.2, `AtkinsonHan.Chapter03.theorem_3_1_2`: a subalgebra of $C(D)$ for a compact $D$
  that separates points is dense.
* Corollary 3.1.3, `AtkinsonHan.Chapter03.corollary_3_1_3`: the polynomials in $d$ variables are
  dense in $C(D)$ for a compact $D \subseteq \mathbb{R}^d$.
* Corollary 3.1.4, `AtkinsonHan.Chapter03.corollary_3_1_4`: the trigonometric polynomials are dense
  in $C_p(2\pi)$.
* Theorem 3.1.5, `AtkinsonHan.Chapter03.theorem_3_1_5`: the span of $t \mapsto t^{\lambda_j}$ is
  dense in $L^2(0, 1)$ if and only if $\sum_j 1/\lambda_j = \infty$.

## Proof outline

The backbone proves Theorem 3.1.5 with Gram determinants. The Gram matrix of finitely many powers in
$L^2(0, 1)$ is a Cauchy matrix. Gram's formula then gives the squared distance from $t^a$ to the
span of $t^{\lambda_1}, \dots, t^{\lambda_n}$ as the product
$$\frac{1}{2a + 1} \prod_{i=1}^n \left(\frac{a - \lambda_i}{a + \lambda_i + 1}\right)^2,$$
and this product tends to $0$ exactly when $\sum_i 1/\lambda_i$ diverges.

Corollary 3.1.4 comes from the density of the complex exponentials in
$C(\mathbb{R}/2\pi\mathbb{Z}, \mathbb{C})$, Mathlib's `span_fourier_closure_eq_top`, carried to the
real system `trigFun` by taking real parts. It is what makes the trigonometric system complete in
Theorem 1.3.13, and Theorem 4.1.2 uses it.

## Conventions

* $C_p(2\pi)$, the continuous $2\pi$-periodic functions with the uniform norm, is
  `C(AddCircle (2 * π), ℝ)`, as in the rest of the library.
* $\mathbb{R}^d$ is `Fin d → ℝ`. By Theorem 1.2.14 the choice of the norm on it does not matter;
  only the topology enters.
* $L^2(0, 1)$ is `Lp ℝ 2 μ₁`, where `μ₁` is the Lebesgue measure restricted to the open interval
  $(0, 1)$, and `Muntz.powerL2 l` is the power $t \mapsto t^l$ as an element of it.

## Deviations from the source

* **Theorem 3.1.1** (reading). The formal approximation bound is strict, which is equivalent
  because the tolerance is arbitrary. The theorem also permits an empty interval.
* **Theorem 3.1.2** (generalization). The approximation theorem applies to any compact
  topological space, while the book assumes a compact subset of Euclidean space.
* **Corollary 3.1.4** (generalization). The statement is for the continuous functions of any period
  $T > 0$; the source takes $T = 2\pi$. See `AtkinsonHan.Chapter03.corollary_3_1_4`.
-/

open Complex Filter MeasureTheory Set Submodule

open scoped Polynomial Real Topology

namespace AtkinsonHan.Chapter03

/-- **Theorem 3.1.1** of [han2009theoretical] (Weierstrass approximation theorem). Let
$a, b \in \mathbb{R}$ and $f \in C[a, b]$. For every $\varepsilon > 0$ there is a real
polynomial $p$ with
$$\max_{a \le x \le b} |f(x) - p(x)| < \varepsilon.$$

The polynomial acts on $[a, b]$ through `Polynomial.toContinuousMapOn`, and the maximum is the
norm of `C(Set.Icc a b, ℝ)`. If $a > b$ the interval is empty and the statement holds trivially.

**Reading.** The printed estimate is $\le \varepsilon$. Using a smaller positive tolerance shows
that the conclusion with $< \varepsilon$ is equivalent. The formal statement also permits an
empty interval. -/
theorem theorem_3_1_1 (a b : ℝ) (f : C(Set.Icc a b, ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℝ[X], ‖p.toContinuousMapOn (Set.Icc a b) - f‖ < ε :=
  exists_polynomial_near_continuousMap a b f ε hε

/-- **Theorem 3.1.2** of [han2009theoretical] (Stone–Weierstrass theorem). Let $D$ be a compact
topological space and let $A$ be a subalgebra of $C(D)$ that separates the points of $D$. Then
$A$ is dense in $C(D)$.

The source states the theorem for a linear subspace that is closed under products and contains
the constant functions, which is exactly a subalgebra. The proof is Mathlib's Stone–Weierstrass
theorem.

**Generalization.** The book takes a compact subset of $\mathbb{R}^{d}$. The declaration
allows an arbitrary compact topological space. -/
theorem theorem_3_1_2 {D : Type*} [TopologicalSpace D] [CompactSpace D] (A : Subalgebra ℝ C(D, ℝ))
    (hA : A.SeparatesPoints) : A.topologicalClosure = ⊤ :=
  ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints A hA

/-- **Corollary 3.1.3** of [han2009theoretical]. Let $D \subseteq \mathbb{R}^d$ be compact and
$f \in C(D)$. For every $\varepsilon > 0$ there is a real polynomial $p$ in $d$ variables with
$|p(x) - f(x)| < \varepsilon$ for all $x \in D$.

The polynomial is an element of `MvPolynomial (Fin d) ℝ`, evaluated by `MvPolynomial.eval`. -/
theorem corollary_3_1_3 {d : ℕ} {D : Set (Fin d → ℝ)} (hD : IsCompact D) (f : C(D, ℝ)) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ p : MvPolynomial (Fin d) ℝ, ∀ x : D, |MvPolynomial.eval (x : Fin d → ℝ) p - f x| < ε := by
  have : CompactSpace D := isCompact_iff_compactSpace.mp hD
  -- the `d` coordinate functions, as elements of `C(D, ℝ)`
  set φ : Fin d → C(D, ℝ) :=
    fun i => ⟨fun x => (x : Fin d → ℝ) i, (continuous_apply i).comp continuous_subtype_val⟩
  set A : Subalgebra ℝ C(D, ℝ) := (MvPolynomial.aeval φ).range
  have hmem : ∀ i, φ i ∈ A := fun i => ⟨MvPolynomial.X i, by simp⟩
  have hsep : A.SeparatesPoints := by
    intro x y hxy
    obtain ⟨i, hi⟩ : ∃ i, (x : Fin d → ℝ) i ≠ (y : Fin d → ℝ) i := by
      by_contra h
      exact hxy (Subtype.ext (funext fun i => not_not.mp (not_exists.mp h i)))
    exact ⟨⇑(φ i), ⟨φ i, hmem i, rfl⟩, hi⟩
  obtain ⟨g, hg⟩ :=
    ContinuousMap.exists_mem_subalgebra_near_continuousMap_of_separatesPoints A hsep f ε hε
  obtain ⟨p, hp⟩ := g.2
  refine ⟨p, fun x => ?_⟩
  have hx := (ContinuousMap.norm_lt_iff _ hε).mp hg x
  have hval : MvPolynomial.eval (x : Fin d → ℝ) p = (MvPolynomial.aeval φ) p x :=
    (MvPolynomial.comp_aeval_apply φ (ContinuousMap.evalAlgHom ℝ ℝ x) p).symm
  have hgp : (MvPolynomial.aeval φ) p = (g : C(D, ℝ)) := hp
  rw [hval, hgp]
  simpa [Real.norm_eq_abs] using hx

section Trigonometric

variable {T : ℝ}

/-- **Corollary 3.1.4** of [han2009theoretical]. Let $T > 0$ and let $f$ be a continuous
$T$-periodic real function. For every $\varepsilon > 0$ there is a real trigonometric polynomial
$p$ with $\|p - f\|_\infty < \varepsilon$. For $T = 2\pi$, $p$ is a real linear combination of
$1$, $\cos(jx)$ and $\sin(jx)$, $j \ge 1$.

**Generalization.** The source takes $C_p(2\pi)$, which is the case $T = 2\pi$.

The space of periodic functions is `C(AddCircle T, ℝ)`. The trigonometric polynomials are the
real span of `trigFun T`, the system of Theorem 1.3.13. The density is the backbone's
`exists_mem_span_trigFun_norm_sub_lt`. -/
theorem corollary_3_1_4 [Fact (0 < T)] (f : C(AddCircle T, ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ p ∈ span ℝ (Set.range (trigFun T)), ‖p - f‖ < ε :=
  exists_mem_span_trigFun_norm_sub_lt f hε

end Trigonometric

section Muntz

/-!
### Theorem 3.1.5: the Müntz–Szász theorem

$L^2(0, 1)$ is `Lp ℝ 2 μ₁` for the Lebesgue measure `μ₁` restricted to the open interval $(0, 1)$,
and `Muntz.powerL2 l` is the power $t \mapsto t^l$ as an element of it.
-/

/-- The measure of $L^2(0, 1)$: the Lebesgue measure restricted to the open interval $(0, 1)$. -/
local notation "μ₁" => MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) 1)

/-- **Theorem 3.1.5** of [han2009theoretical] (Müntz–Szász theorem). Let
$0 < \lambda_1 < \lambda_2 < \cdots$ with $\lambda_j \to \infty$. Then the span of the powers
$t \mapsto t^{\lambda_j}$ is dense in $L^2(0, 1)$ if and only if
$$\sum_{j=1}^\infty \frac{1}{\lambda_j} = \infty.$$

The sequence is indexed from $0$, so $\lambda_1$ of the source is `lam 0`. The divergence of
$\sum_j 1/\lambda_j$ is stated as the failure of `Summable`; the terms are positive. The proof
is the backbone's `Muntz.dense_span_powerL2_iff`. -/
theorem theorem_3_1_5 (lam : ℕ → ℝ) (hpos : 0 < lam 0) (hmono : StrictMono lam)
    (htop : Tendsto lam atTop atTop) :
    Dense ((Submodule.span ℝ (Set.range fun j ↦ Muntz.powerL2 (lam j)) :
        Submodule ℝ (Lp ℝ 2 μ₁)) : Set (Lp ℝ 2 μ₁))
      ↔ ¬ Summable fun j ↦ (lam j)⁻¹ :=
  Muntz.dense_span_powerL2_iff lam hpos hmono htop

end Muntz

end AtkinsonHan.Chapter03
