/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Real.Cardinality
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Numlib.Analysis.Normed.Module.Reflexive.Kakutani
import Numlib.Analysis.Normed.Module.WeakDual
import Numlib.MeasureTheory.Function.LpSpace.Clarkson
import Numlib.MeasureTheory.Function.LpSpace.Duality
import NumlibSurface.Brezis.Chapter04.Section02

/-!
# Brezis, Section 4.3: Reflexivity. Separability. Dual of $L^p$

This module formalizes Section 4.3 of [brezis2011functional] for real-valued functions on a σ-finite
measure space $\Omega$, which is the standing assumption of the chapter. The section treats three
cases. (A) For $1 < p < \infty$, $L^p$ is reflexive and uniformly convex (Theorem 4.10, Remark 3),
its dual is $L^{p'}$ (Theorem 4.11, Remark 4), $C_c(\mathbb{R}^N)$ is dense in $L^p(\mathbb{R}^N)$
(Theorem 4.12), and $L^p$ is separable (Theorem 4.13). (B) For $p = 1$, the dual of $L^1$ is
$L^\infty$ (Theorem 4.14, Remark 5), and $L^1$ is not reflexive (Remark 6). (C) For $p = \infty$,
the closed unit ball of $L^\infty$ is weak-∗ compact, bounded sequences have weakly-∗ convergent
subsequences, $L^\infty$ is not reflexive, its dual is strictly larger than $L^1$, and $L^\infty$ is
not separable (Lemma 4.2, Remark 8).

The proofs specialize the backbone modules `Numlib.MeasureTheory.Function.LpSpace.Clarkson` and
`Numlib.MeasureTheory.Function.LpSpace.Duality`: the uniform convexity
`MeasureTheory.Lp.instUniformConvexSpace`, the isometry `MeasureTheory.Lp.toDual`, its surjectivity
`MeasureTheory.Lp.toDual_surjective` (which gives Theorems 4.11 and 4.14 together, by the
Radon–Nikodym theorem), the isometric isomorphism `MeasureTheory.Lp.dualEquiv`, the reflexivity
instance `MeasureTheory.Lp.instIsReflexive` (proved from the duality, not from the Milman–Pettis
theorem), and `MeasureTheory.Lp.not_surjective_toDual_top`. Theorem 4.13 is Mathlib's
`MeasureTheory.Lp.SecondCountableTopology`.

## Main definitions

* Section 4.3, definition of a separable measure space,
  `Brezis.Chapter04.separableMeasureSpace_of_secondCountable`: a separable measure space is a
  countably generated σ-algebra, and $\mathbb{R}^N$ and every separable metric space with its Borel
  σ-algebra are examples.

## Main results

* Theorem 4.10, `Brezis.Chapter04.theorem_4_10`: $L^p$ is reflexive for $1 < p < \infty$.
* Theorem 4.10, Step 1, `Brezis.Chapter04.theorem_4_10_clarkson`: Clarkson's first inequality for
  $2 \le p < \infty$.
* Theorem 4.10, Step 2, `Brezis.Chapter04.theorem_4_10_uniformConvex`: $L^p$ is uniformly convex for
  $2 \le p < \infty$, with an explicit modulus.
* Theorem 4.10, Step 3, `Brezis.Chapter04.theorem_4_10_isometry`: the map
  $T : L^p \to (L^{p'})^\star$, $\langle Tu, f \rangle = \int uf$, is an isometry with closed range.
* Remark 3, `Brezis.Chapter04.remark_4_3`: Clarkson's second inequality, and the uniform convexity
  of $L^p$ for $1 < p \le 2$.
* Theorem 4.11 (Riesz representation theorem), `Brezis.Chapter04.theorem_4_11`: every
  $\varphi \in (L^p)^\star$ is $f \mapsto \int uf$ for a unique $u \in L^{p'}$, with
  $\|u\|_{p'} = \|\varphi\|$.
* Remark 4, `Brezis.Chapter04.remark_4_4`: $u \mapsto (f \mapsto \int uf)$ is an isometric
  isomorphism from $L^{p'}$ onto $(L^p)^\star$.
* Theorem 4.12, `Brezis.Chapter04.theorem_4_12`: $C_c(\mathbb{R}^N)$ is dense in $L^p(\mathbb{R}^N)$
  for $1 \le p < \infty$.
* Theorem 4.13, `Brezis.Chapter04.theorem_4_13`: $L^p(\Omega)$ is separable for a separable measure
  space $\Omega$ and $1 \le p < \infty$.
* Section 4.3, `Brezis.Chapter04.theorem_4_13_subset`: $L^p(\Omega)$ is separable for every
  $\Omega \subseteq \mathbb{R}^N$ and $1 \le p < \infty$.
* Theorem 4.14 (Riesz representation theorem), `Brezis.Chapter04.theorem_4_14`: every
  $\varphi \in (L^1)^\star$ is $f \mapsto \int uf$ for a unique $u \in L^\infty$, with
  $\|u\|_\infty = \|\varphi\|$.
* Remark 5, `Brezis.Chapter04.remark_4_5`: $u \mapsto (f \mapsto \int uf)$ is an isometric
  isomorphism from $L^\infty$ onto $(L^1)^\star$.
* Remark 6, `Brezis.Chapter04.remark_4_6`: $L^1(\Omega)$ is not reflexive for a nonempty open
  $\Omega \subseteq \mathbb{R}^N$.
* Section 4.3, case C, `Brezis.Chapter04.lInfty_weakStar_isCompact_closedBall`: the closed unit ball
  of $L^\infty$ is compact in $\sigma(L^\infty, L^1)$.
* Section 4.3, case C, `Brezis.Chapter04.lInfty_exists_subseq_weakStar_tendsto`: a bounded sequence
  in $L^\infty(\Omega)$, $\Omega \subseteq \mathbb{R}^N$, has a weakly-∗ convergent subsequence.
* Section 4.3, case C, `Brezis.Chapter04.lInfty_not_isReflexive`: $L^\infty(\Omega)$ is not
  reflexive for a nonempty open $\Omega \subseteq \mathbb{R}^N$.
* Section 4.3, case C, `Brezis.Chapter04.exists_strongDual_lInfty_not_integral`: some continuous
  linear functional on $L^\infty(\mathbb{R}^N)$ is not given by a function of $L^1$.
* Lemma 4.2, `Brezis.Chapter04.lemma_4_2`: a space with an uncountable family of pairwise disjoint
  nonempty open sets is not separable.
* Remark 8, `Brezis.Chapter04.remark_4_8`: $L^\infty(\Omega)$ is not separable for a nonempty open
  $\Omega \subseteq \mathbb{R}^N$.

## Conventions

* The conjugate exponent $p'$ is `q`, with `p.HolderConjugate q`. The space $L^p$ is
  `MeasureTheory.Lp ℝ p μ`, as in Section 4.2.
* For $\Omega \subseteq \mathbb{R}^N$, the space $L^p(\Omega)$ is `Lp ℝ p (volume.restrict Ω)` on
  `EuclideanSpace ℝ (Fin N)`.
* The negative results (Remarks 6 and 8, and the non-reflexivity and the functional of case C) are
  stated for a nonempty open set $\Omega \subseteq \mathbb{R}^N$ with $N \ge 1$, with Lebesgue
  measure. For $N = 0$ the spaces are finite-dimensional and these statements are false.

## Implementation notes

* Theorem 4.10 is proved from the Riesz representation theorem, through the backbone instance
  `MeasureTheory.Lp.instIsReflexive`. The three steps of the proof of the source are stated
  separately as `Brezis.Chapter04.theorem_4_10_clarkson`,
  `Brezis.Chapter04.theorem_4_10_uniformConvex` and `Brezis.Chapter04.theorem_4_10_isometry`.
* Remark 6 is proved from `MeasureTheory.Lp.not_surjective_toDual_top`, not by the weak compactness
  argument of the source.

## Deviations from the source

* **Theorem 4.10, Steps 1–3, and Remarks 3 and 4** (generalization). The Clarkson inequalities
  and uniform convexity apply to arbitrary measures. The dual isometry in Step 3 includes
  $p=1,\infty$, and the identification in Remark 4 includes $p=1$.
* **Separable measure space example** (reading). The argument for Euclidean space uses its Borel
  σ-algebra, whereas the opening of Chapter 4 uses the completed Lebesgue σ-algebra. The example
  for separable metric spaces extends to second countable spaces with their Borel σ-algebra.
  See `Brezis.Chapter04.separableMeasureSpace_of_secondCountable`.
* **Theorem 4.11** (generalization). The source states the theorem for $1 < p < \infty$. The formal
  statement holds for $1 \le p < \infty$, and Theorem 4.14 is its case $p = 1$. See
  `Brezis.Chapter04.theorem_4_11`.
* **Remark after Theorem 4.13** (generalization). The source assumes that
  $\Omega \subseteq \mathbb{R}^N$ is measurable. The formal statement holds for every subset. See
  `Brezis.Chapter04.theorem_4_13_subset`.
* **Study of $L^\infty$, part (ii)** (generalization). Weak-star sequential compactness is stated
  for the restriction of volume to any subset. See
  `Brezis.Chapter04.lInfty_exists_subseq_weakStar_tendsto`.
* **Remarks 6 and 8 and nonreflexivity of $L^\infty$** (reading). The formal conclusions are
  restricted to nonempty open subsets of positive-dimensional Euclidean space. See
  `Brezis.Chapter04.remark_4_6`, `Brezis.Chapter04.remark_4_8` and
  `Brezis.Chapter04.lInfty_not_isReflexive`.
* **Point evaluation in the dual of $L^\infty$** (reading). The example assumes $N\ge 1$.
  See `Brezis.Chapter04.exists_strongDual_lInfty_not_integral`.
* **Lemma 4.2** (generalization). The source states the lemma for a Banach space. The formal
  statement holds for every topological space. See `Brezis.Chapter04.lemma_4_2`.

## Not formalized

* **Remarks 6 and 8, the general measure space.** The claims that $L^1(\Omega)$ is not reflexive and
  $L^\infty(\Omega)$ is not separable unless $\Omega$ consists of finitely many atoms are stated
  only for nonempty open subsets of $\mathbb{R}^N$.
-/

open Filter MeasureTheory Metric Topology
open scoped ENNReal

namespace Brezis.Chapter04

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {p q : ℝ≥0∞}

/-! ### A. The case $1 < p < \infty$: reflexivity and uniform convexity -/

/-- **Theorem 4.10** of [brezis2011functional]. Let $\Omega$ be σ-finite and $1 < p < \infty$. Then
$L^p(\Omega)$ is reflexive.

The proof is the backbone instance `MeasureTheory.Lp.instIsReflexive`, which follows from the
Riesz representation theorem. The source argues differently: Clarkson's inequality gives uniform
convexity for $p \ge 2$, the Milman–Pettis theorem gives reflexivity, and for $1 < p \le 2$ the
isometry into $(L^{p'})^\star$ and Corollary 3.21 conclude. These steps are
`Brezis.Chapter04.theorem_4_10_clarkson`, `Brezis.Chapter04.theorem_4_10_uniformConvex` and
`Brezis.Chapter04.theorem_4_10_isometry`. -/
theorem theorem_4_10 [SigmaFinite μ] [Fact (1 ≤ p)] (hp : 1 < p) (hp' : p ≠ ∞) :
    NormedSpace.IsReflexive ℝ (Lp ℝ p μ) := by
  have := Fact.mk hp
  have := Fact.mk hp'
  infer_instance

/-- **Theorem 4.10** of [brezis2011functional], Step 1 (Clarkson's first inequality). Let
$2 \le p < \infty$. For all $f, g \in L^p(\Omega)$,
$$\Bigl\|\frac{f + g}{2}\Bigr\|_p^p + \Bigl\|\frac{f - g}{2}\Bigr\|_p^p \le \frac12
  \bigl(\|f\|_p^p + \|g\|_p^p\bigr). \qquad (8)$$
It follows from the pointwise inequality, for all $a, b \in \mathbb{R}$,
$$\Bigl|\frac{a + b}{2}\Bigr|^p + \Bigl|\frac{a - b}{2}\Bigr|^p \le \frac12 \bigl(|a|^p +
  |b|^p\bigr), \qquad (9)$$
which is also stated.

**Generalization.** The inequalities hold for any measure. -/
theorem theorem_4_10_clarkson (hp : 2 ≤ p) (hp' : p ≠ ∞) :
    (∀ f g : Lp ℝ p μ, ‖(2 : ℝ)⁻¹ • (f + g)‖ ^ p.toReal + ‖(2 : ℝ)⁻¹ • (f - g)‖ ^ p.toReal ≤
      (‖f‖ ^ p.toReal + ‖g‖ ^ p.toReal) / 2) ∧
    ∀ a b : ℝ, |(a + b) / 2| ^ p.toReal + |(a - b) / 2| ^ p.toReal ≤
      (|a| ^ p.toReal + |b| ^ p.toReal) / 2 :=
  ⟨Lp.clarkson_of_two_le hp hp',
    Real.clarkson_pointwise_of_two_le (by simpa using ENNReal.toReal_mono hp' hp)⟩

/-- **Theorem 4.10** of [brezis2011functional], Step 2. Let $2 \le p < \infty$. Then $L^p(\Omega)$
is uniformly convex. Precisely, for every $\varepsilon > 0$ and all $f, g \in L^p(\Omega)$ with
$\|f\|_p \le 1$, $\|g\|_p \le 1$ and $\|f - g\|_p > \varepsilon$,
$$\Bigl\|\frac{f + g}{2}\Bigr\|_p < 1 - \delta, \qquad \delta = 1 - \Bigl[1 -
  \Bigl(\frac{\varepsilon}{2}\Bigr)^p\Bigr]^{1/p}.$$

The bound follows from Clarkson's first inequality. The reflexivity conclusion is stated in
`Brezis.Chapter04.theorem_4_10` under σ-finiteness.

**Generalization.** The bound and uniform convexity hold for any measure. -/
theorem theorem_4_10_uniformConvex [Fact (1 ≤ p)] (hp : 2 ≤ p) (hp' : p ≠ ∞) :
    UniformConvexSpace (Lp ℝ p μ) ∧
    ∀ ε > 0, ∀ f g : Lp ℝ p μ, ‖f‖ ≤ 1 → ‖g‖ ≤ 1 → ε < ‖f - g‖ →
      ‖(2 : ℝ)⁻¹ • (f + g)‖ < (1 - (ε / 2) ^ p.toReal) ^ (1 / p.toReal) := by
  have h1 : Fact (1 < p) := ⟨ENNReal.one_lt_two.trans_le hp⟩
  have h2 : Fact (p ≠ ∞) := ⟨hp'⟩
  refine ⟨inferInstance, fun ε hε f g hf hg hfg => ?_⟩
  have hP : 0 < p.toReal := ENNReal.toReal_pos (zero_lt_one.trans_le Fact.out).ne' hp'
  have hc := Lp.clarkson_of_two_le hp hp' f g
  have hA : 0 ≤ ‖(2 : ℝ)⁻¹ • (f + g)‖ := norm_nonneg _
  have hB : ‖(2 : ℝ)⁻¹ • (f - g)‖ = ‖f - g‖ / 2 := by
    rw [norm_smul, norm_inv, Real.norm_ofNat, inv_mul_eq_div]
  have hε2 : ε / 2 < ‖(2 : ℝ)⁻¹ • (f - g)‖ := by rw [hB]; linarith
  have h1' : (ε / 2) ^ p.toReal < ‖(2 : ℝ)⁻¹ • (f - g)‖ ^ p.toReal :=
    Real.rpow_lt_rpow (by positivity) hε2 hP
  have hfp : ‖f‖ ^ p.toReal ≤ 1 := Real.rpow_le_one (norm_nonneg _) hf hP.le
  have hgp : ‖g‖ ^ p.toReal ≤ 1 := Real.rpow_le_one (norm_nonneg _) hg hP.le
  have key : ‖(2 : ℝ)⁻¹ • (f + g)‖ ^ p.toReal < 1 - (ε / 2) ^ p.toReal := by linarith
  calc ‖(2 : ℝ)⁻¹ • (f + g)‖ = (‖(2 : ℝ)⁻¹ • (f + g)‖ ^ p.toReal) ^ (1 / p.toReal) := by
        rw [one_div, Real.rpow_rpow_inv hA hP.ne']
    _ < (1 - (ε / 2) ^ p.toReal) ^ (1 / p.toReal) :=
        Real.rpow_lt_rpow (by positivity) key (by positivity)

/-- **Theorem 4.10** of [brezis2011functional], Step 3. Let $\Omega$ be σ-finite and let
$1 \le p \le \infty$ with conjugate exponent $p'$. The operator
$T : L^p(\Omega) \to (L^{p'}(\Omega))^\star$ defined by
$$\langle Tu, f \rangle = \int_\Omega u f \, d\mu \qquad (u \in L^p,\ f \in L^{p'})$$
satisfies $\|Tu\|_{(L^{p'})^\star} = \|u\|_p$ for every $u$ (equation (11)), and its range is
closed in $(L^{p'})^\star$.

The operator is the backbone's `MeasureTheory.Lp.toDual ℝ q p μ`. The last sentence of the step
in the source, that $L^p$ is reflexive for $1 < p \le 2$ by Corollary 3.21 and Proposition 3.20,
is stated in `Brezis.Chapter04.theorem_4_10`.

**Generalization.** The closed isometric embedding includes both conjugate endpoints, $p=1$
and $p=\infty$. -/
theorem theorem_4_10_isometry [SigmaFinite μ] [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [p.HolderConjugate q] :
    (∀ u : Lp ℝ p μ, ‖Lp.toDual ℝ q p μ u‖ = ‖u‖) ∧
    (∀ (u : Lp ℝ p μ) (f : Lp ℝ q μ), Lp.toDual ℝ q p μ u f = ∫ x, u x * f x ∂μ) ∧
    IsClosed (Set.range (Lp.toDual ℝ q p μ)) :=
  ⟨fun u => (Lp.toDual ℝ q p μ).norm_map u, fun u f => Lp.toDual_apply u f,
    (Lp.toDual ℝ q p μ).isometry.isUniformInducing.isComplete_range.isClosed⟩

/-- **Remark 3** in Chapter 4 of [brezis2011functional] (Clarkson's second inequality). Let
$1 < p \le 2$ with conjugate exponent $p'$. For all $f, g \in L^p(\Omega)$,
$$\Bigl\|\frac{f + g}{2}\Bigr\|_p^{p'} + \Bigl\|\frac{f - g}{2}\Bigr\|_p^{p'} \le \Bigl[\frac12
  \bigl(\|f\|_p^p + \|g\|_p^p\bigr)\Bigr]^{1/(p - 1)}.$$
Consequently $L^p(\Omega)$ is uniformly convex for $1 < p \le 2$ as well.

The inequality is inequality (6) of Problem 20 of the source, divided by $2^{p'}$.

**Generalization.** The conclusions hold for any measure. -/
theorem remark_4_3 [Fact (1 ≤ p)] [p.HolderConjugate q] (hp : 1 < p) (hp2 : p ≤ 2) :
    (∀ f g : Lp ℝ p μ, ‖(2 : ℝ)⁻¹ • (f + g)‖ ^ q.toReal + ‖(2 : ℝ)⁻¹ • (f - g)‖ ^ q.toReal ≤
      ((‖f‖ ^ p.toReal + ‖g‖ ^ p.toReal) / 2) ^ (1 / (p.toReal - 1))) ∧
    UniformConvexSpace (Lp ℝ p μ) := by
  have hp' : p ≠ ∞ := ne_top_of_le_ne_top (by simp) hp2
  have hq' : q ≠ ∞ := (ENNReal.HolderConjugate.ne_top_iff_ne_one q p).2 hp.ne'
  have hPQ : p.toReal.HolderConjugate q.toReal := ENNReal.HolderConjugate.toReal_of_ne_top hp' hq'
  refine ⟨fun f g => ?_, ?_⟩
  · have hc := Lp.clarkson_of_le_two (q := q) hp hp2 f g
    have hdiv : q.toReal / p.toReal = q.toReal - 1 := hPQ.symm.div_conj_eq_sub_one
    have hP1 : 1 < p.toReal := hPQ.lt
    have h1 : 1 / (p.toReal - 1) = q.toReal / p.toReal := by
      rw [hdiv, hPQ.conjugate_eq]
      have hP0 : p.toReal - 1 ≠ 0 := by linarith
      field_simp
      ring
    have hn2 : ∀ x : Lp ℝ p μ, ‖(2 : ℝ)⁻¹ • x‖ = ‖x‖ / 2 := fun x => by
      rw [norm_smul, norm_inv, Real.norm_ofNat, inv_mul_eq_div]
    rw [h1, hn2, hn2, Real.div_rpow (norm_nonneg _) (by norm_num),
      Real.div_rpow (norm_nonneg _) (by norm_num), ← add_div,
      Real.div_rpow (by positivity) (by norm_num)]
    have h2Q : (2 : ℝ) ^ q.toReal = 2 ^ (q.toReal / p.toReal) * 2 := by
      rw [← Real.rpow_add_one two_ne_zero]
      congr 1
      linarith
    rw [h2Q, div_le_div_iff₀ (by positivity) (by positivity)]
    calc (‖f + g‖ ^ q.toReal + ‖f - g‖ ^ q.toReal) * 2 ^ (q.toReal / p.toReal)
        ≤ 2 * (‖f‖ ^ p.toReal + ‖g‖ ^ p.toReal) ^ (q.toReal / p.toReal) *
          2 ^ (q.toReal / p.toReal) := by gcongr
      _ = (‖f‖ ^ p.toReal + ‖g‖ ^ p.toReal) ^ (q.toReal / p.toReal) *
          (2 ^ (q.toReal / p.toReal) * 2) := by ring
  · have := Fact.mk hp
    have := Fact.mk hp'
    infer_instance

/-! ### A. The case $1 < p < \infty$: the dual, density, separability -/

/-- **Theorem 4.11** of [brezis2011functional] (Riesz representation theorem). Let $\Omega$ be
σ-finite, let $1 \le p < \infty$, and let $p'$ be the conjugate exponent. For every
$\varphi \in (L^p(\Omega))^\star$ there is a unique $u \in L^{p'}(\Omega)$ such that
$$\langle \varphi, f \rangle = \int_\Omega u f \, d\mu \quad \text{for all } f \in L^p(\Omega),
  \qquad \text{and} \qquad \|u\|_{p'} = \|\varphi\|.$$

**Generalization.** The source states the theorem for $1 < p < \infty$ and proves it from the
reflexivity of $L^p$. The backbone proves it for $1 \le p < \infty$ by the Radon–Nikodym theorem
(`MeasureTheory.Lp.toDual_surjective`), so Theorem 4.14 is the case $p = 1$.

Uniqueness is stated for the pair of conditions: $u$ is the only element of $L^{p'}$ that
represents $\varphi$ and has norm $\|\varphi\|$. -/
theorem theorem_4_11 [SigmaFinite μ] [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]
    (hp' : p ≠ ∞) (φ : StrongDual ℝ (Lp ℝ p μ)) :
    ∃! u : Lp ℝ q μ, (∀ f : Lp ℝ p μ, φ f = ∫ x, u x * f x ∂μ) ∧ ‖u‖ = ‖φ‖ := by
  obtain ⟨u, hu⟩ := Lp.toDual_surjective (𝕜 := ℝ) (μ := μ) (p := p) (q := q) hp' φ
  refine ⟨u, ⟨fun f => by rw [← hu, Lp.toDual_apply], by rw [← hu, LinearIsometry.norm_map]⟩,
    fun v ⟨hv, _⟩ => (Lp.toDual ℝ p q μ).injective ?_⟩
  rw [hu]
  ext f
  rw [Lp.toDual_apply, hv f]

/-- **Remark 4** in Chapter 4 of [brezis2011functional]. Let $\Omega$ be σ-finite and
$1 \le p < \infty$ with conjugate exponent $p'$. The map $u \mapsto (f \mapsto \int u f)$ is a
linear surjective isometry from $L^{p'}(\Omega)$ onto $(L^p(\Omega))^\star$. This identifies
$(L^p)^\star$ with $L^{p'}$.

The isometry is the backbone's `MeasureTheory.Lp.dualEquiv`.

**Generalization.** The identification includes $p=1$, given separately in Remark 5. -/
theorem remark_4_4 [SigmaFinite μ] [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]
    (hp' : p ≠ ∞) :
    ∃ e : Lp ℝ q μ ≃ₗᵢ[ℝ] StrongDual ℝ (Lp ℝ p μ),
      ∀ (u : Lp ℝ q μ) (f : Lp ℝ p μ), e u f = ∫ x, u x * f x ∂μ :=
  ⟨Lp.dualEquiv ℝ p q μ hp', fun u f => Lp.dualEquiv_apply hp' u f⟩

/-- **Theorem 4.12** of [brezis2011functional]. Let $1 \le p < \infty$. Then $C_c(\mathbb{R}^N)$ is
dense in $L^p(\mathbb{R}^N)$: the classes of continuous functions with compact support form a
dense subset of $L^p(\mathbb{R}^N)$.

The proof is Mathlib's `MeasureTheory.MemLp.exists_hasCompactSupport_eLpNorm_sub_le`, which does
not follow the truncation argument of the source. -/
theorem theorem_4_12 {N : ℕ} [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    Dense {g : Lp ℝ p (volume : Measure (EuclideanSpace ℝ (Fin N))) |
      ∃ φ : EuclideanSpace ℝ (Fin N) → ℝ, Continuous φ ∧ HasCompactSupport φ ∧
        ⇑g =ᵐ[volume] φ} := by
  refine Metric.dense_iff.2 fun f ε hε => ?_
  obtain ⟨φ, hφs, hφε, hφc, hφp⟩ := (Lp.memLp f).exists_hasCompactSupport_eLpNorm_sub_le hp
    (ε := ENNReal.ofReal (ε / 2)) (ENNReal.ofReal_pos.2 (by positivity)).ne'
  refine ⟨hφp.toLp φ, ?_, φ, hφc, hφs, hφp.coeFn_toLp⟩
  rw [Metric.mem_ball, dist_comm, Lp.dist_def]
  calc (eLpNorm (⇑f - ⇑(hφp.toLp φ)) p volume).toReal
      = (eLpNorm (⇑f - φ) p volume).toReal := by
        congr 1
        exact eLpNorm_congr_ae ((EventuallyEq.refl _ _).sub hφp.coeFn_toLp)
    _ ≤ (ENNReal.ofReal (ε / 2)).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hφε
    _ = ε / 2 := ENNReal.toReal_ofReal (by positivity)
    _ < ε := half_lt_self hε

/-- **Section 4.3** of [brezis2011functional], definition of a separable measure space and the
example after it. The source calls a measure space **separable** if its σ-algebra is generated
by a countable family of sets; this is Mathlib's `MeasurableSpace.CountablyGenerated`. The
example states that $\mathbb{R}^N$ is a separable measure space, and more generally that every
separable metric space $X$ with its Borel σ-algebra is one.

**Reading.** The argument for $\mathbb{R}^N$ uses the Borel σ-algebra. The introduction to the
chapter uses the completed Lebesgue σ-algebra. The result for $X$ applies to any second countable
topological space with its Borel σ-algebra. -/
theorem separableMeasureSpace_of_secondCountable (N : ℕ) (X : Type*) [TopologicalSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] :
    MeasurableSpace.CountablyGenerated (EuclideanSpace ℝ (Fin N)) ∧
      MeasurableSpace.CountablyGenerated X :=
  ⟨inferInstance, inferInstance⟩

/-- **Theorem 4.13** of [brezis2011functional]. Let $\Omega$ be a σ-finite, separable measure space
and $1 \le p < \infty$. Then $L^p(\Omega)$ is separable.

The source proves only the case $\Omega = \mathbb{R}^N$. Mathlib's
`MeasureTheory.Lp.SecondCountableTopology` gives the general case. -/
theorem theorem_4_13 [MeasurableSpace.CountablyGenerated α] [SigmaFinite μ] [Fact (1 ≤ p)]
    (hp : p ≠ ∞) : TopologicalSpace.SeparableSpace (Lp ℝ p μ) := by
  have : Fact (p ≠ ∞) := ⟨hp⟩
  have : SecondCountableTopology (Lp ℝ p μ) := Lp.SecondCountableTopology
  infer_instance

/-- **Section 4.3** of [brezis2011functional], the remark after Theorem 4.13. Let
$\Omega \subseteq \mathbb{R}^N$ and $1 \le p < \infty$. Then $L^p(\Omega)$ is separable.

**Generalization.** The source assumes that $\Omega$ is measurable, and argues by extension by
zero. Here $L^p(\Omega)$ is $L^p$ of the restriction of Lebesgue measure to $\Omega$, and
Theorem 4.13 applies to it directly, for every subset $\Omega$. -/
theorem theorem_4_13_subset {N : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin N))) [Fact (1 ≤ p)]
    (hp : p ≠ ∞) : TopologicalSpace.SeparableSpace (Lp ℝ p (volume.restrict Ω)) :=
  theorem_4_13 hp

/-! ### B. The case $p = 1$ -/

/-- **Theorem 4.14** of [brezis2011functional] (Riesz representation theorem, $p = 1$). Let $\Omega$
be σ-finite. For every $\varphi \in (L^1(\Omega))^\star$ there is a unique
$u \in L^\infty(\Omega)$ such that
$$\langle \varphi, f \rangle = \int_\Omega u f \, d\mu \quad \text{for all } f \in L^1(\Omega),
  \qquad \text{and} \qquad \|u\|_\infty = \|\varphi\|.$$

This is the case $p = 1$ of `Brezis.Chapter04.theorem_4_11`. -/
theorem theorem_4_14 [SigmaFinite μ] (φ : StrongDual ℝ (Lp ℝ 1 μ)) :
    ∃! u : Lp ℝ ∞ μ, (∀ f : Lp ℝ 1 μ, φ f = ∫ x, u x * f x ∂μ) ∧ ‖u‖ = ‖φ‖ :=
  theorem_4_11 ENNReal.one_ne_top φ

/-- **Remark 5** in Chapter 4 of [brezis2011functional]. Let $\Omega$ be σ-finite. The map
$u \mapsto (f \mapsto \int u f)$ is a linear surjective isometry from $L^\infty(\Omega)$ onto
$(L^1(\Omega))^\star$. This identifies $(L^1)^\star$ with $L^\infty$. -/
theorem remark_4_5 [SigmaFinite μ] :
    ∃ e : Lp ℝ ∞ μ ≃ₗᵢ[ℝ] StrongDual ℝ (Lp ℝ 1 μ),
      ∀ (u : Lp ℝ ∞ μ) (f : Lp ℝ 1 μ), e u f = ∫ x, u x * f x ∂μ :=
  ⟨Lp.dualEquiv ℝ 1 ∞ μ ENNReal.one_ne_top, fun u f => Lp.dualEquiv_apply _ u f⟩

/-- **Remark 6** in Chapter 4 of [brezis2011functional]. Let $N \ge 1$ and let
$\Omega \subseteq \mathbb{R}^N$ be open and nonempty. Then $L^1(\Omega)$ is not reflexive.

**Reading.** The source treats σ-finite measure spaces beyond the finite-atom case. The library
specializes to nonempty open subsets of positive-dimensional Euclidean space. If $L^1$ were
reflexive, then through
$(L^1)^\star = L^\infty$ every continuous linear functional on $L^\infty$ would have the form
$f \mapsto \int uf$ with $u \in L^1$. But $(L^\infty)^\star$ is strictly larger than $L^1$, by
`MeasureTheory.Lp.not_surjective_toDual_top` (see also
`Brezis.Chapter04.exists_strongDual_lInfty_not_integral`). -/
theorem remark_4_6 {N : ℕ} [NeZero N] {Ω : Set (EuclideanSpace ℝ (Fin N))} (hΩ : IsOpen Ω)
    (hne : Ω.Nonempty) : ¬ NormedSpace.IsReflexive ℝ (Lp ℝ 1 (volume.restrict Ω)) := by
  intro h
  refine Lp.not_surjective_toDual_top volume hΩ hne fun ψ => ?_
  set e := Lp.dualEquiv ℝ 1 ∞ (volume.restrict Ω) ENNReal.one_ne_top with he
  obtain ⟨u, hu⟩ := NormedSpace.surjective_inclusionInDoubleDual (𝕜 := ℝ)
    (V := Lp ℝ 1 (volume.restrict Ω)) (ψ.comp (e.symm.toContinuousLinearEquiv :
      StrongDual ℝ (Lp ℝ 1 (volume.restrict Ω)) →L[ℝ] Lp ℝ ∞ (volume.restrict Ω)))
  refine ⟨u, ?_⟩
  ext f
  have := DFunLike.congr_fun hu (e f)
  rw [NormedSpace.dual_def, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, LinearIsometryEquiv.symm_apply_apply] at this
  rw [Lp.toDual_apply, ← this, he, Lp.dualEquiv_apply]
  exact integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)

/-! ### C. The case $p = \infty$ -/

/-- **Section 4.3** of [brezis2011functional], case C, weak-∗ compactness. Let $\Omega$ be σ-finite.
The closed unit ball of $L^\infty(\Omega)$ is compact in the weak-∗ topology
$\sigma(L^\infty, L^1)$.

The ball is carried into the dual $(L^1)^\star$ by the identification $L^\infty = (L^1)^\star$
of Remark 5 (`MeasureTheory.Lp.dualEquiv`), and its image is the closed unit ball of
`WeakDual ℝ (Lp ℝ 1 μ)`. This ball is compact by Theorem 3.16 (Banach–Alaoglu–Bourbaki,
`WeakDual.isCompact_closedBall`). -/
theorem lInfty_weakStar_isCompact_closedBall [SigmaFinite μ] :
    IsCompact ((fun u : Lp ℝ ∞ μ =>
      StrongDual.toWeakDual (Lp.dualEquiv ℝ 1 ∞ μ ENNReal.one_ne_top u)) '' closedBall 0 1) := by
  have h : (fun u : Lp ℝ ∞ μ =>
      StrongDual.toWeakDual (Lp.dualEquiv ℝ 1 ∞ μ ENNReal.one_ne_top u)) '' closedBall 0 1 =
        WeakDual.toStrongDual ⁻¹' closedBall 0 1 := by
    rw [show (fun u : Lp ℝ ∞ μ =>
        StrongDual.toWeakDual (Lp.dualEquiv ℝ 1 ∞ μ ENNReal.one_ne_top u)) '' closedBall 0 1 =
        StrongDual.toWeakDual '' (Lp.dualEquiv ℝ 1 ∞ μ ENNReal.one_ne_top '' closedBall 0 1) from
        (Set.image_image _ _ _).symm, LinearIsometryEquiv.image_closedBall, map_zero]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa only [Set.mem_preimage, StrongDual.toStrongDual_toWeakDual] using hy
    · intro hx
      exact ⟨WeakDual.toStrongDual x, hx, WeakDual.toWeakDual_toStrongDual x⟩
  rw [h]
  exact WeakDual.isCompact_closedBall 0 1

/-- **Section 4.3** of [brezis2011functional], case C, weak-∗ sequential compactness. Let
$\Omega \subseteq \mathbb{R}^N$, and let $(f_n)$ be a bounded sequence in $L^\infty(\Omega)$,
with $\|f_n\|_\infty \le C$ for all $n$. Then there are a subsequence $(f_{n_k})$ and
$f \in L^\infty(\Omega)$ with $f_{n_k} \overset{\star}{\rightharpoonup} f$ in
$\sigma(L^\infty, L^1)$, that is,
$$\int_\Omega f_{n_k} g \to \int_\Omega f g \quad \text{for every } g \in L^1(\Omega).$$

The proof is Corollary 3.30, the sequential Banach–Alaoglu theorem for the dual of the separable
space $L^1(\Omega)$, in the transported form `LinearIsometryEquiv.exists_subseq_tendsto_apply`,
applied through the identification $L^\infty = (L^1)^\star$ of Remark 5. In the Lean statement
the limit is `g` and the test function is `h`.

**Generalization.** The statement uses the restriction of volume to any subset $\Omega$. -/
theorem lInfty_exists_subseq_weakStar_tendsto {N : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin N))}
    (f : ℕ → Lp ℝ ∞ (volume.restrict Ω)) {C : ℝ} (hf : ∀ n, ‖f n‖ ≤ C) :
    ∃ (φ : ℕ → ℕ) (g : Lp ℝ ∞ (volume.restrict Ω)), StrictMono φ ∧
      ∀ h : Lp ℝ 1 (volume.restrict Ω),
        Tendsto (fun k => ∫ x, f (φ k) x * h x ∂(volume.restrict Ω)) atTop
          (𝓝 (∫ x, g x * h x ∂(volume.restrict Ω))) := by
  have : TopologicalSpace.SeparableSpace (Lp ℝ 1 (volume.restrict Ω)) :=
    theorem_4_13_subset Ω ENNReal.one_ne_top
  obtain ⟨φ, g, hφ, hlim⟩ :=
    (Lp.dualEquiv ℝ 1 ∞ (volume.restrict Ω) ENNReal.one_ne_top).exists_subseq_tendsto_apply hf
  refine ⟨φ, g, hφ, fun h => ?_⟩
  simpa only [Lp.dualEquiv_apply] using hlim h

/-- **Section 4.3** of [brezis2011functional], case C, non-reflexivity. Let $N \ge 1$ and let
$\Omega \subseteq \mathbb{R}^N$ be open and nonempty. Then $L^\infty(\Omega)$ is not reflexive.

Since $L^\infty = (L^1)^\star$ by Remark 5, reflexivity of $L^\infty$ would make $L^1$ reflexive
by Corollary 3.21 (`NormedSpace.isReflexive_of_isReflexive_strongDual`), which contradicts
Remark 6.

**Reading.** The source treats σ-finite measure spaces beyond the finite-atom case. The library
specializes to nonempty open subsets of positive-dimensional Euclidean space. -/
theorem lInfty_not_isReflexive {N : ℕ} [NeZero N] {Ω : Set (EuclideanSpace ℝ (Fin N))}
    (hΩ : IsOpen Ω) (hne : Ω.Nonempty) :
    ¬ NormedSpace.IsReflexive ℝ (Lp ℝ ∞ (volume.restrict Ω)) := by
  intro h
  have h1 : NormedSpace.IsReflexive ℝ (StrongDual ℝ (Lp ℝ 1 (volume.restrict Ω))) :=
    (NormedSpace.isReflexive_congr
      (Lp.dualEquiv ℝ 1 ∞ (volume.restrict Ω) ENNReal.one_ne_top).toContinuousLinearEquiv).1 h
  exact remark_4_6 hΩ hne NormedSpace.isReflexive_of_isReflexive_strongDual

/-- **Section 4.3** of [brezis2011functional], case C, the functional of (17) and (18). Let
$N \ge 1$. There is a continuous linear functional $\varphi$ on $L^\infty(\mathbb{R}^N)$ such
that $\langle \varphi, f \rangle = f(0)$ for every $f \in C_c(\mathbb{R}^N)$, and there is no
$u \in L^1(\mathbb{R}^N)$ with
$$\langle \varphi, f \rangle = \int_{\mathbb{R}^N} u f \quad \text{for all } f \in
  L^\infty(\mathbb{R}^N).$$
So $(L^\infty)^\star$ is strictly larger than $L^1$.

The functional is a Hahn–Banach extension of $f \mapsto f(0)$. It is the backbone's
`MeasureTheory.Lp.exists_strongDual_top_apply_eq` at the point $0$.

**Reading.** The example assumes $N\ge 1$, so the singleton $\{0\}$ has measure zero. -/
theorem exists_strongDual_lInfty_not_integral {N : ℕ} [NeZero N] :
    ∃ φ : StrongDual ℝ (Lp ℝ ∞ (volume : Measure (EuclideanSpace ℝ (Fin N)))),
      (∀ (f : EuclideanSpace ℝ (Fin N) → ℝ) (hf : MemLp f ∞ volume), Continuous f →
        HasCompactSupport f → φ (hf.toLp f) = f 0) ∧
      ¬ ∃ u : Lp ℝ 1 (volume : Measure (EuclideanSpace ℝ (Fin N))),
        ∀ g : Lp ℝ ∞ (volume : Measure (EuclideanSpace ℝ (Fin N))), φ g = ∫ x, u x * g x := by
  obtain ⟨φ, h1, h2⟩ := Lp.exists_strongDual_top_apply_eq
    (volume : Measure (EuclideanSpace ℝ (Fin N))) (x₀ := 0) fun _ hU =>
      Measure.measure_pos_of_mem_nhds volume hU
  refine ⟨φ, h1, fun ⟨u, hu⟩ => h2 u ?_⟩
  ext g
  rw [Lp.toDual_apply, hu g]

/-- **Lemma 4.2** of [brezis2011functional]. Let $E$ be a topological space, and suppose that there
is an uncountable family $(O_i)_{i \in I}$ of nonempty open subsets of $E$ that are pairwise
disjoint. Then $E$ is not separable.

**Generalization.** The source states the lemma for a Banach space $E$. The proof uses only the
topology.

The proof is Mathlib's `Pairwise.countable_of_isOpen_disjoint`. -/
theorem lemma_4_2 {E : Type*} [TopologicalSpace E] {ι : Type*} [Uncountable ι] (O : ι → Set E)
    (hO : ∀ i, IsOpen (O i)) (hne : ∀ i, (O i).Nonempty)
    (hdisj : Pairwise (Function.onFun Disjoint O)) :
    ¬ TopologicalSpace.SeparableSpace E := fun _ =>
  not_countable (hdisj.countable_of_isOpen_disjoint hO hne)

/-- **Remark 8** in Chapter 4 of [brezis2011functional]. Let $N \ge 1$ and let
$\Omega \subseteq \mathbb{R}^N$ be open and nonempty. Then $L^\infty(\Omega)$ is not separable.

**Reading.** The source states a result for σ-finite measure spaces beyond the finite-atom case.
The library gives the case of nonempty open subsets of positive-dimensional Euclidean space.
For a ball $B(x_0, r_0) \subseteq \Omega$, the classes of the indicator functions of the balls
$B(x_0, r)$ with $0 < r < r_0$ are at mutual distance $1$ in $L^\infty$. The balls of radius $1/2$
around them form an uncountable family of pairwise disjoint nonempty open sets, so Lemma 4.2
applies. -/
theorem remark_4_8 {N : ℕ} [NeZero N] {Ω : Set (EuclideanSpace ℝ (Fin N))} (hΩ : IsOpen Ω)
    (hne : Ω.Nonempty) : ¬ TopologicalSpace.SeparableSpace (Lp ℝ ∞ (volume.restrict Ω)) := by
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨r₀, hr₀, hball⟩ := Metric.isOpen_iff.1 hΩ x₀ hx₀
  have hfin : ∀ r : ℝ, (volume.restrict Ω) (ball x₀ r) ≠ ∞ := fun r =>
    ((Measure.le_iff'.1 Measure.restrict_le_self _).trans_lt measure_ball_lt_top).ne
  -- the indicator classes
  set χ : Set.Ioo (0 : ℝ) r₀ → Lp ℝ ∞ (volume.restrict Ω) := fun r =>
    indicatorConstLp ∞ measurableSet_ball (hfin r) (1 : ℝ) with hχ
  -- two of them are at distance at least `1`
  have hdist : ∀ r s : Set.Ioo (0 : ℝ) r₀, r ≠ s → 1 ≤ dist (χ r) (χ s) := by
    -- by symmetry it suffices to treat `r < s`
    have key : ∀ r s : Set.Ioo (0 : ℝ) r₀, (r : ℝ) < s → 1 ≤ dist (χ r) (χ s) := by
      intro r s hrs
      rw [dist_comm, Lp.dist_def, hχ]
      have hsub : ball x₀ r ⊆ ball x₀ s := ball_subset_ball hrs.le
      have heq : ⇑(indicatorConstLp ∞ measurableSet_ball (hfin s) (1 : ℝ)) -
          ⇑(indicatorConstLp ∞ measurableSet_ball (hfin r) (1 : ℝ)) =ᵐ[volume.restrict Ω]
          (ball x₀ s \ ball x₀ r).indicator fun _ => (1 : ℝ) := by
        filter_upwards [indicatorConstLp_coeFn (p := ∞)
          (hs := measurableSet_ball (x := x₀) (ε := s)) (hμs := hfin s) (c := (1 : ℝ)),
          indicatorConstLp_coeFn (p := ∞) (hs := measurableSet_ball (x := x₀) (ε := r))
          (hμs := hfin r) (c := (1 : ℝ))] with x hx hx'
        rw [Pi.sub_apply, hx, hx', Set.indicator_sdiff hsub]
        rfl
      rw [eLpNorm_congr_ae heq, eLpNorm_exponent_top (aestronglyMeasurable_const.indicator
        (measurableSet_ball.diff measurableSet_ball)), eLpNormEssSup_indicator_const_eq]
      · simp
      -- the annulus has positive measure
      rw [Measure.restrict_apply (measurableSet_ball.diff measurableSet_ball),
        Set.inter_eq_left.2 (Set.sdiff_subset.trans ((ball_subset_ball s.2.2.le).trans hball))]
      have hlt : volume (ball x₀ (r : ℝ)) < volume (ball x₀ (s : ℝ)) := by
        rw [Measure.addHaar_ball volume x₀ r.2.1.le, Measure.addHaar_ball volume x₀ s.2.1.le,
          mul_comm, mul_comm (ENNReal.ofReal _)]
        refine ENNReal.mul_lt_mul_right (measure_ball_pos (volume : Measure (EuclideanSpace ℝ
          (Fin N))) (0 : EuclideanSpace ℝ (Fin N)) one_pos).ne' measure_ball_lt_top.ne ?_
        refine ENNReal.ofReal_lt_ofReal_iff'.2 ⟨pow_lt_pow_left₀ hrs r.2.1.le ?_, pow_pos s.2.1 _⟩
        rw [finrank_euclideanSpace_fin]
        exact NeZero.ne N
      rw [measure_sdiff hsub measurableSet_ball.nullMeasurableSet measure_ball_lt_top.ne]
      exact (tsub_pos_iff_lt.2 hlt).ne'
    intro r s hrs
    rcases lt_or_gt_of_ne (Subtype.coe_ne_coe.2 hrs) with h | h
    · exact key r s h
    · rw [dist_comm]
      exact key s r h
  have : Uncountable (Set.Ioo (0 : ℝ) r₀) := not_countable_iff.1 fun h => by
    rw [Set.countable_coe_iff, Cardinal.Real.Ioo_countable_iff] at h
    linarith
  refine lemma_4_2 (fun r : Set.Ioo (0 : ℝ) r₀ => ball (χ r) (1 / 2)) (fun _ => isOpen_ball)
    (fun _ => nonempty_ball.2 (by norm_num)) fun r s hrs => ?_
  exact ball_disjoint_ball (le_of_eq_of_le (add_halves _) (hdist r s hrs))

end Brezis.Chapter04
