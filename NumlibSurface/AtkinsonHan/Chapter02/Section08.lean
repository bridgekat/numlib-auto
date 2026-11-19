/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Numlib.Analysis.InnerProductSpace.Ascent
import Numlib.Analysis.InnerProductSpace.CompactSpectral
import Numlib.Analysis.Normed.Operator.Compact
import Numlib.Analysis.Normed.Operator.Riesz
import Numlib.IntegralEquations.Basic
import Numlib.IntegralEquations.WeaklySingular
import NumlibSurface.AtkinsonHan.Chapter01.Section01
import NumlibSurface.AtkinsonHan.Chapter02.Section04

/-!
# Atkinson and Han, Section 2.8: Compact linear operators

This module formalizes Section 2.8 of [han2009theoretical]. Let $V$ and $W$ be normed spaces over
$\mathbb{K} \in \{\mathbb{R}, \mathbb{C}\}$. A bounded linear operator $K : V \to W$ is compact when
the image of the closed unit ball has compact closure, or equivalently when every bounded sequence
$(u_n)$ has a subsequence along which $K u_n$ converges. The module proves the closure properties of
the compact operators (finite rank, composition, limits in the operator norm), the compactness of
integral operators on $C(D)$ with a continuous kernel and with a weakly singular kernel (§2.8.1),
the Fredholm alternative for the equation of the second kind $(\lambda - K) u = f$, the Riesz theory
of the spectrum of a compact operator, and, in a Hilbert space, Schauder's theorem, the solvability
criterion $\mathcal{R}(\lambda - K) = \mathcal{N}(\bar\lambda - K^*)^\perp$ and the spectral theorem
for a compact self-adjoint operator.

Mathlib supplies `IsCompactOperator`, the Fredholm alternative
`IsCompactOperator.hasEigenvalue_or_mem_resolventSet` and the spectral theorem
`ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot`. The closure properties,
Schauder's theorem, the discreteness of the spectrum, the closed range and the Riesz index come from
the backbone modules `Numlib.Analysis.Normed.Operator.Compact` and
`Numlib.Analysis.Normed.Operator.Riesz`, the enumeration of the eigenvalues from
`Numlib.Analysis.InnerProductSpace.CompactSpectral` and `Numlib.Analysis.InnerProductSpace.Ascent`,
and the integral operators from `Numlib.IntegralEquations.Basic` and
`Numlib.IntegralEquations.WeaklySingular`.

## Main definitions

* Definition 2.8.1, `AtkinsonHan.Chapter02.definition_2_8_1`: a bounded operator is compact if and
  only if it maps bounded sequences to sequences with a convergent subsequence.
* Definition 2.8.3, `AtkinsonHan.Chapter02.definition_2_8_3`: an operator of finite rank, one whose
  range is finite dimensional.
* Definition 2.8.11, `AtkinsonHan.Chapter02.definition_2_8_11` and
  `AtkinsonHan.Chapter02.definition_2_8_11_eigenvector`: an eigenvalue $\lambda$ of an operator $K$,
  and an eigenvector $u \neq 0$ with $K u = \lambda u$.

## Main results

* Equation (2.8.2), `AtkinsonHan.Chapter02.equation_2_8_2`: a kernel on a compact
  $D \subseteq \mathbb{R}^d$ that satisfies (A₁)–(A₂) defines the integral operator
  $K v(x) = \int_D k(x, y) v(y) \, dy$ on $C(D)$.
* Equation (2.8.5), `AtkinsonHan.Chapter02.equation_2_8_5`: $|K v(x) - K v(z)| \le \omega(\|x - z\|)
  \|v\|_\infty$.
* Equation (2.8.6), `AtkinsonHan.Chapter02.equation_2_8_6_le` and
  `AtkinsonHan.Chapter02.equation_2_8_6`: $\|K\| = \sup_x \int_D |k(x, y)| \, dy$.
* Section 2.8.1, `AtkinsonHan.Chapter02.isCompactOperator_of_isAdmissibleKernel`: an integral
  operator whose kernel satisfies (A₁)–(A₂) is compact on $C(D)$.
* Example 2.8.2, `AtkinsonHan.Chapter02.example_2_8_2`: the kernel $\log|\cos x - \cos y|$ gives a
  compact operator on $C[0, \pi]$.
* Definition 2.8.3, `AtkinsonHan.Chapter02.definition_2_8_3_iff`: an operator has finite rank if and
  only if its range is `FiniteDimensional`.
* Proposition 2.8.4, `AtkinsonHan.Chapter02.proposition_2_8_4`: a bounded operator of finite rank is
  compact.
* Example 2.8.5, `AtkinsonHan.Chapter02.example_2_8_5`,
  `AtkinsonHan.Chapter02.example_2_8_5_isCompactOperator` and
  `AtkinsonHan.Chapter02.example_2_8_5_norm`: a degenerate kernel $\sum_i \beta_i(x) \gamma_i(y)$
  gives a compact operator with range in the span of the $\beta_i$ and norm at most
  $\sum_i \|\beta_i\|_\infty \int |\gamma_i|$.
* Proposition 2.8.6, `AtkinsonHan.Chapter02.proposition_2_8_6`: a composition with a compact factor
  is compact.
* Proposition 2.8.7, `AtkinsonHan.Chapter02.proposition_2_8_7`: a limit in the operator norm of
  compact operators into a Banach space is compact.
* Example 2.8.8, `AtkinsonHan.Chapter02.example_2_8_8` and
  `AtkinsonHan.Chapter02.example_2_8_8_interval`: an integral operator with a continuous kernel is
  compact on $C(D)$ for a compact $D \subseteq \mathbb{R}^d$, and on $C[a, b]$.
* Example 2.8.9, `AtkinsonHan.Chapter02.example_2_8_9`: the kernel $|x - y|^{-\gamma}$ with
  $0 < \gamma < 1$ gives a compact operator on $C[a, b]$.
* Theorem 2.8.10, `AtkinsonHan.Chapter02.theorem_2_8_10` and
  `AtkinsonHan.Chapter02.theorem_2_8_10_inverse`: the Fredholm alternative; if $\lambda - K$ is
  injective, it has a bounded inverse.
* Definition 2.8.11, `AtkinsonHan.Chapter02.definition_2_8_11_iff` and
  `AtkinsonHan.Chapter02.definition_2_8_11_eigenvector_iff`: the two notions are Mathlib's
  `Module.End.HasEigenvalue` and `Module.End.HasEigenvector`.
* Theorem 2.8.12(1), `AtkinsonHan.Chapter02.theorem_2_8_12_1`: for every $\varepsilon > 0$, a
  compact operator has only finitely many eigenvalues of modulus at least $\varepsilon$.
* Theorem 2.8.12(2), `AtkinsonHan.Chapter02.theorem_2_8_12_2`: the eigenspace of a nonzero
  eigenvalue is finite dimensional.
* Theorem 2.8.12(3), `AtkinsonHan.Chapter02.theorem_2_8_12_3`: a nonzero eigenvalue has a finite
  index $\nu(\lambda) \ge 1$, and $\mathcal{N}((\lambda - K)^{\nu(\lambda)})$ is finite dimensional.
* Theorem 2.8.12(4), `AtkinsonHan.Chapter02.theorem_2_8_12_4`: the range of $\lambda - K$ is closed
  for $\lambda \neq 0$.
* Theorem 2.8.12(5), `AtkinsonHan.Chapter02.theorem_2_8_12_5`: $V = \mathcal{N}((\lambda - K)^{\nu})
  \oplus \mathcal{R}((\lambda - K)^{\nu})$, with both summands invariant under $K$.
* Theorem 2.8.12(6), `AtkinsonHan.Chapter02.theorem_2_8_12_6`: the Fredholm alternative holds when
  only a power $K^m$ is compact.
* Lemma 2.8.13, `AtkinsonHan.Chapter02.lemma_2_8_13`: the adjoint of a compact operator between
  Hilbert spaces is compact.
* Theorem 2.8.14(1), `AtkinsonHan.Chapter02.theorem_2_8_14_hasEigenvalue_adjoint` and
  `AtkinsonHan.Chapter02.theorem_2_8_14_dim`: if $\lambda \neq 0$ is an eigenvalue of $K$, then
  $\bar\lambda$ is an eigenvalue of $K^*$, and $\dim \mathcal{N}(\lambda - K) = \dim
  \mathcal{N}(\bar\lambda - K^*)$.
* Theorem 2.8.14(2), `AtkinsonHan.Chapter02.theorem_2_8_14` and
  `AtkinsonHan.Chapter02.theorem_2_8_14_isCompl`: $(\lambda - K) u = f$ is solvable if and only if
  $f \perp \mathcal{N}(\bar\lambda - K^*)$, and $V = \mathcal{N}(\bar\lambda - K^*) \oplus
  \mathcal{R}(\lambda - K)$.
* Theorem 2.8.15, `AtkinsonHan.Chapter02.theorem_2_8_15`: the eigenvectors of a compact self-adjoint
  operator span a dense subspace.
* Theorem 2.8.15, `AtkinsonHan.Chapter02.theorem_2_8_15_eigenvalue_real`,
  `AtkinsonHan.Chapter02.theorem_2_8_15_index` and
  `AtkinsonHan.Chapter02.theorem_2_8_15_closure_range`: the eigenvalues of a self-adjoint operator
  are real, have index one, and $\mathcal{N}(K)^\perp = \overline{\mathcal{R}(K)}$.
* Theorem 2.8.15, (2.8.31)–(2.8.32), `AtkinsonHan.Chapter02.theorem_2_8_15_enumeration`: the nonzero
  eigenvalues can be listed with $|\lambda_1| \ge |\lambda_2| \ge \cdots > 0$ and $\lambda_j \to 0$,
  with an orthonormal family of eigenvectors.

## Conventions

* The source writes $\lambda$ for the scalar of the equation of the second kind. `λ` is a keyword in
  Lean, so the scalar is `l`.
* The source states the section over a general scalar field and then specializes to real or complex
  scalars. The statements here are over `RCLike 𝕜`, as in the rest of the library. Definitions 2.8.3
  and 2.8.11 need only linear spaces, so they are stated over a bare `Module`, as Chapter 1 states
  the definitions that they use.
* $\mathcal{N}(A)$ and $\mathcal{R}(A)$ are the null space and the range of $A$, that is,
  `LinearMap.ker` and `LinearMap.range`.
* The operator $\lambda - K$ is `l • 1 - K`.

## Implementation notes

* Mathlib's `IsCompactOperator K` says that some compact set has a preimage under $K$ that is a
  neighbourhood of $0$. By `isCompactOperator_iff_isCompact_closure_image_closedBall` it is
  equivalent to the condition of the source that the image of the closed unit ball has compact
  closure, and `AtkinsonHan.Chapter02.definition_2_8_1` adds the sequential form that the source
  uses in practice.
* An integral operator integrates against `IntegralOperator.regionMeasure D`, the Lebesgue measure
  on $D$, or against `IntegralOperator.iccMeasure a b` on an interval. The continuous-kernel case,
  which Chapters 12 and 13 use, is `AtkinsonHan.Chapter02.example_2_8_8`.

## Deviations from the source

* **Equations (2.8.5) and (2.8.6)** (reading). The modulus estimate uses continuous inputs.
  The norm formula uses a supremum and covers empty $D$. For nonempty compact $D$, (A₁) makes
  the row integral continuous, so the supremum agrees with the source's maximum.
* **Example 2.8.5** (reading). The kernel results use continuous factors on a compact measure
  space. The book allows integrable second factors on a closed interval. See
  `AtkinsonHan.Chapter02.example_2_8_5`.
* **Examples 2.8.2, 2.8.8, and 2.8.9** (reading). The singular kernels take value zero on the
  diagonal. The continuous-kernel result uses restricted ambient Lebesgue measure, including
  for lower-dimensional sets. The source also discusses surface and curve domains.
* **Definitions 2.8.3 and 2.8.11** (generalization). Finite rank is available over any division
  ring, and the eigenvalue and eigenvector predicates over any field.
* **Theorems 2.8.12–2.8.14** (generalization and reading). Some compact-operator results allow
  incomplete spaces or scalars that are not eigenvalues. The adjoint results cover both real
  and complex scalars. The case of a compact power gives the Fredholm alternative.
* **Theorem 2.8.15, the basis** (correction). The nonzero eigenspaces span densely in the closure
  of the range of $K$. The source prints the range of $\lambda I-K$. In finite dimension with
  $K=I$, the printed range for $\lambda=1$ is zero, although the nonzero eigenvectors span $V$.
* **Theorem 2.8.15, the reality of the eigenvalues, the index one and the closure of the range**
  (generalization). These three clauses are stated for every bounded self-adjoint operator, without
  compactness. See `AtkinsonHan.Chapter02.theorem_2_8_15_index`.

## Not formalized

* **Example 2.8.5 with integrable $\gamma_i$.** The source allows the functions $\gamma_i$ of a
  degenerate kernel to be only absolutely integrable. The continuous-kernel operator
  `IntegralOperator.kernelCLM` does not admit such kernels, so the example is stated for continuous
  $\gamma_i$.
* **The general enumeration in Theorem 2.8.15.** Lean states the case of an injective $K$ on an
  infinite-dimensional space. A general list of nonzero eigenvalues can be finite or infinite.
* **Example 2.8.9, the truncation formula.** The printed rate is an upper bound in general.
  For $b-a<2/n$, no integration row contains the full interval of distances $1/n$ on both
  sides of the singularity. Lean states the compactness result.
* **Theorem 2.8.12(6), extension of (1)–(5) to compact powers.** The corresponding surface
  declaration states the Fredholm alternative for compact powers.
* **Example 2.8.16.** On the unit sphere $D$ of $\mathbb{R}^3$ and $V = L^2(D)$, the single-layer
  operator $K v(x) = \int_D v(y) / \|x - y\| \, dS_y$ (2.8.33) is compact. Its eigenfunctions are
  the spherical harmonics: there are $2k + 1$ independent ones of each degree $k \ge 0$, with
  $K \varphi_k = \frac{4\pi}{2k + 1} \varphi_k$ (2.8.34), so that $\mathcal{N}(\mu_k - K)$ has
  dimension $2k + 1$ for $\mu_k = 4\pi/(2k + 1)$, and they form a basis of $L^2(D)$, as Theorem
  2.8.15 predicts. The source states this without proof and cites Mikhlin for the compactness. Three
  things are missing from Mathlib: an integration theory for the surface measure of the sphere, and
  with it $L^2(D)$; the spherical harmonics as a Hilbert basis of $L^2(D)$ with $2k + 1$ elements of
  each degree; and the Funk–Hecke computation of the eigenvalues $4\pi/(2k + 1)$. The compactness
  alone would follow from the (A₁)–(A₂) theory of `Numlib.IntegralEquations.WeaklySingular` once the
  surface measure is available.
-/

open Filter Topology Metric Module.End

open scoped InnerProductSpace

namespace AtkinsonHan.Chapter02

section Banach

variable {𝕜 V W : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [NormedAddCommGroup W] [NormedSpace 𝕜 W]

/-! ### Definition 2.8.1 and its sequential form -/

/-- **Definition 2.8.1** of [han2009theoretical], sequential form. Let $V$ and $W$ be normed spaces
over $\mathbb{K}$ and let $K : V \to W$ be a bounded linear operator. Then $K$ is compact if and
only if every bounded sequence $(u_n)$ in $V$ has a subsequence $(u_{\varphi(n)})$ such that
$(K u_{\varphi(n)})$ converges in $W$.

Compactness is Mathlib's `IsCompactOperator`. It is equivalent to the definition of the source,
that the image of the closed unit ball has compact closure, by
`isCompactOperator_iff_isCompact_closure_image_closedBall`. The subsequence is given by a
strictly increasing map $\varphi : \mathbb{N} \to \mathbb{N}$. -/
theorem definition_2_8_1 (K : V →L[𝕜] W) :
    IsCompactOperator K ↔
      ∀ u : ℕ → V, (∃ C, ∀ n, ‖u n‖ ≤ C) →
        ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ w, Tendsto (fun n => K (u (φ n))) atTop (𝓝 w) := by
  constructor
  · rintro hK u ⟨C, hC⟩
    obtain ⟨S, hS, hSsub⟩ := hK.image_closedBall_subset_compact (max C 1)
    obtain ⟨w, -, φ, hφ, hlim⟩ := hS.tendsto_subseq (x := fun n => K (u n)) fun n =>
      hSsub ⟨u n, mem_closedBall_zero_iff.2 ((hC n).trans (le_max_left _ _)), rfl⟩
    exact ⟨φ, hφ, w, hlim⟩
  · intro hseq
    refine (isCompactOperator_iff_isCompact_closure_image_closedBall
      (K : V →ₗ[𝕜] W) one_pos).2 (IsSeqCompact.isCompact fun x hx => ?_)
    have hchoice : ∀ n : ℕ, ∃ v : V, ‖v‖ ≤ 1 ∧ dist (x n) (K v) < 1 / ((n : ℝ) + 1) := by
      intro n
      obtain ⟨y, ⟨v, hv, rfl⟩, hd⟩ :=
        Metric.mem_closure_iff.1 (hx n) (1 / ((n : ℝ) + 1)) (by positivity)
      exact ⟨v, mem_closedBall_zero_iff.1 hv, hd⟩
    choose v hv hd using hchoice
    obtain ⟨φ, hφ, w, hw⟩ := hseq v ⟨1, hv⟩
    have hmem : ∀ n, K (v (φ n)) ∈ closure ((K : V →ₗ[𝕜] W) '' closedBall 0 1) := fun n =>
      subset_closure ⟨v (φ n), mem_closedBall_zero_iff.2 (hv _), rfl⟩
    refine ⟨w, isClosed_closure.mem_of_tendsto hw (.of_forall hmem), φ, hφ, ?_⟩
    have hone : Tendsto (fun n : ℕ => 1 / ((φ n : ℝ) + 1)) atTop (𝓝 0) := by
      have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      exact h0.comp hφ.tendsto_atTop
    have h1 : Tendsto (fun n => dist (x (φ n)) (K (v (φ n)))) atTop (𝓝 0) :=
      squeeze_zero (fun n => dist_nonneg) (fun n => (hd (φ n)).le) hone
    have h2 : Tendsto (fun n => dist (K (v (φ n))) w) atTop (𝓝 0) :=
      tendsto_iff_dist_tendsto_zero.1 hw
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun n => dist_nonneg)
      (fun n => dist_triangle (x (φ n)) (K (v (φ n))) w) ?_
    simpa using h1.add h2

end Banach

/-! ### Definition 2.8.3: operators of finite rank -/

section FiniteRank

variable {𝕜 V W : Type*} [DivisionRing 𝕜] [AddCommGroup V] [Module 𝕜 V] [AddCommGroup W]
  [Module 𝕜 W]

/-- **Definition 2.8.3** of [han2009theoretical]. A linear operator $K : V \to W$ between linear
spaces over a field $\mathbb{K}$ is **of finite rank** if its range $\mathcal{R}(K)$ is finite
dimensional, that is, if $\mathcal{R}(K)$ has a finite maximal linearly independent family in
the sense of Definition 1.1.9.

The definition uses `AtkinsonHan.Chapter01.definition_1_1_9`. By
`AtkinsonHan.Chapter02.definition_2_8_3_iff` it is `FiniteDimensional 𝕜 (LinearMap.range K)`,
which is the hypothesis of `AtkinsonHan.Chapter02.proposition_2_8_4`.

**Generalization.** The range criterion applies over any division ring. -/
def definition_2_8_3 (𝕜 : Type*) {V W : Type*} [DivisionRing 𝕜] [AddCommGroup V] [Module 𝕜 V]
    [AddCommGroup W] [Module 𝕜 W] (K : V →ₗ[𝕜] W) : Prop :=
  ∃ (n : ℕ) (v : Fin n → LinearMap.range K), Chapter01.definition_1_1_9 𝕜 v

/-- **Definition 2.8.3** of [han2009theoretical], identification. A linear operator $K$ is of finite
rank if and only if its range is finite dimensional in the sense of Mathlib's
`FiniteDimensional`.

The proof reads Definition 1.1.9 as finite dimensionality, by
`AtkinsonHan.Chapter01.definition_1_1_9_finiteDimensional_iff`. -/
theorem definition_2_8_3_iff (K : V →ₗ[𝕜] W) :
    definition_2_8_3 𝕜 K ↔ FiniteDimensional 𝕜 (LinearMap.range K) :=
  Chapter01.definition_1_1_9_finiteDimensional_iff 𝕜 _

end FiniteRank

section Banach

variable {𝕜 V W : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [NormedAddCommGroup W] [NormedSpace 𝕜 W]

/-! ### Propositions 2.8.4, 2.8.6 and 2.8.7: closure properties -/

/-- **Proposition 2.8.4** of [han2009theoretical]. Let $V$ and $W$ be normed spaces and let
$K : V \to W$ be a bounded linear operator whose range is finite dimensional. Then $K$ is
compact.

Finite rank is the instance `FiniteDimensional 𝕜 (LinearMap.range K)`, which is Definition 2.8.3
by `AtkinsonHan.Chapter02.definition_2_8_3_iff`. -/
theorem proposition_2_8_4 (K : V →L[𝕜] W)
    [FiniteDimensional 𝕜 (LinearMap.range (K : V →ₗ[𝕜] W))] : IsCompactOperator K :=
  IsCompactOperator.of_finiteDimensional_range K

/-- **Proposition 2.8.6** of [han2009theoretical]. Let $U$, $V$ and $W$ be normed spaces, let
$K : V \to W$ be compact, and let $A : U \to V$ and $B : W \to U$ be bounded linear operators.
Then $K A$ and $B K$ are compact. -/
theorem proposition_2_8_6 {U : Type*} [NormedAddCommGroup U] [NormedSpace 𝕜 U]
    (A : U →L[𝕜] V) (B : W →L[𝕜] U) {K : V →L[𝕜] W} (hK : IsCompactOperator K) :
    IsCompactOperator (K.comp A) ∧ IsCompactOperator (B.comp K) :=
  ⟨hK.comp_clm A, hK.clm_comp B⟩

/-- **Proposition 2.8.7** of [han2009theoretical]. Let $V$ be a normed space and $W$ a Banach space.
If $A_n : V \to W$ are compact operators and $\|A_n - K\| \to 0$ for a bounded operator $K$,
then $K$ is compact.

This is what makes an integral operator compact when its kernel is a uniform limit of degenerate
kernels, as in Example 2.8.8. -/
theorem proposition_2_8_7 [CompleteSpace W] {A : ℕ → V →L[𝕜] W} {K : V →L[𝕜] W}
    (hA : ∀ n, IsCompactOperator (A n)) (h : Tendsto (fun n => ‖A n - K‖) atTop (𝓝 0)) :
    IsCompactOperator K :=
  IsCompactOperator.of_tendsto hA h

end Banach

/-! ### Examples 2.8.5 and 2.8.8: integral operators -/

section IntegralOperators

open MeasureTheory IntegralOperator

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsFiniteMeasure μ] {n : ℕ}

/-- **Example 2.8.5** of [han2009theoretical], the range. Let $X$ be a compact space with a finite
Borel measure $\mu$, and let $\beta_1, \dots, \beta_n$ and $\gamma_1, \dots, \gamma_n$ be
continuous real functions on $X$. The integral operator $K$ on $C(X)$ with the **degenerate
kernel**
$$k(x, y) = \sum_{i=1}^n \beta_i(x) \gamma_i(y)$$
has its range in the span of $\beta_1, \dots, \beta_n$.

**Reading.** The source works on a closed real interval with Lebesgue measure and allows
absolutely integrable $\gamma_i$. The declaration admits general compact spaces with finite
Borel measure and assumes each $\gamma_i$ is continuous, since the backbone operator takes a
continuous kernel.

The kernel is `IntegralOperator.degenerateKernel β γ` and the operator is
`IntegralOperator.kernelCLM μ`. -/
theorem example_2_8_5 (β γ : Fin n → C(X, ℝ)) :
    LinearMap.range (kernelCLM μ (degenerateKernel β γ) : C(X, ℝ) →ₗ[ℝ] C(X, ℝ)) ≤
      Submodule.span ℝ (Set.range β) :=
  range_kernelCLM_degenerateKernel_le μ β γ

/-- **Example 2.8.5** of [han2009theoretical], compactness. With the notation of
`AtkinsonHan.Chapter02.example_2_8_5`, the integral operator with a degenerate kernel is compact
on $C(X)$.

**Reading.** The ambient space and the continuity assumptions are those of
`AtkinsonHan.Chapter02.example_2_8_5`.

Its range is finite dimensional, so this follows from Proposition 2.8.4. -/
theorem example_2_8_5_isCompactOperator (β γ : Fin n → C(X, ℝ)) :
    IsCompactOperator (kernelCLM μ (degenerateKernel β γ)) :=
  have := finiteDimensional_range_kernelCLM_degenerateKernel μ β γ
  proposition_2_8_4 (𝕜 := ℝ) _

/-- **Example 2.8.5** of [han2009theoretical], the norm bound. With the notation of
`AtkinsonHan.Chapter02.example_2_8_5`, the integral operator $K$ with a degenerate kernel
satisfies
$$\|K\| \le \sum_{i=1}^n \|\beta_i\|_\infty \int_X |\gamma_i(y)| \, d\mu(y).$$

**Reading.** The ambient space and the continuity assumptions are those of
`AtkinsonHan.Chapter02.example_2_8_5`. -/
theorem example_2_8_5_norm (β γ : Fin n → C(X, ℝ)) :
    ‖kernelCLM μ (degenerateKernel β γ)‖ ≤ ∑ i, ‖β i‖ * ∫ y, |γ i y| ∂μ :=
  norm_kernelCLM_degenerateKernel_le μ β γ

/-- **Example 2.8.8** of [han2009theoretical]. Let $D \subseteq \mathbb{R}^d$ be closed and bounded,
and let $k$ be a continuous real function on $D \times D$. Then the integral operator
$$K v(x) = \int_D k(x, y) v(y) \, dy$$
is compact on $C(D)$.

"Closed and bounded" is `IsCompact D` by the Heine–Borel theorem (Theorem 1.6.2), written here
as the instance `CompactSpace ↥D`. The measure is `IntegralOperator.regionMeasure D`, the
Lebesgue measure on $D$, and the operator is `IntegralOperator.kernelCLM`. The proof applies the
Arzelà–Ascoli theorem (Theorem 1.6.3) to the image of the unit ball, in the backbone, for any
compact space with a finite Borel measure. The source instead approximates $k$ uniformly by
degenerate kernels and uses Example 2.8.5 and Propositions 2.8.4 and 2.8.7.

**Reading.** Lean restricts the ambient Lebesgue measure, which is zero on a Lebesgue-null
surface or curve. The source also discusses lower-dimensional domains. -/
theorem example_2_8_8 {d : ℕ} {D : Set (EuclideanSpace ℝ (Fin d))} [CompactSpace D]
    (k : C(D × D, ℝ)) : IsCompactOperator (kernelCLM (regionMeasure D) k) :=
  isCompactOperator_kernelCLM _ k

/-- **Example 2.8.8** of [han2009theoretical], on an interval. Let $a \le b$ and let $k$ be a
continuous real function on $[a, b] \times [a, b]$. Then the Fredholm integral operator
$$K u(x) = \int_a^b k(x, y) u(y) \, dy$$
is compact on $C[a, b]$.

The operator is `IntegralOperator.fredholm`. This is the instance that discharges the
`IsCompactOperator` hypothesis of the projection methods and the Nyström method of Chapter 12
for a concrete operator. -/
theorem example_2_8_8_interval {a b : ℝ} (hab : a ≤ b)
    (k : C(Set.Icc a b × Set.Icc a b, ℝ)) : IsCompactOperator (fredholm hab k) :=
  isCompactOperator_fredholm hab k

end IntegralOperators

/-! ### §2.8.1: integral operators with a weakly singular kernel -/

section WeaklySingular

open MeasureTheory IntegralOperator

variable {d : ℕ} {D : Set (EuclideanSpace ℝ (Fin d))} [CompactSpace D] {k : D × D → ℝ}
  (hk : IsAdmissibleKernel (regionMeasure D) k)

include hk

/-- **Equation (2.8.2)** of [han2009theoretical]. Let $D \subseteq \mathbb{R}^d$ be compact and let
$k$ be a real function on $D \times D$ such that every function $y \mapsto k(x, y)$ is
integrable and such that the conditions (A₁) and (A₂) of §2.8.1 hold:
$$\text{(A}_1\text{)} \quad \omega(h) \to 0 \text{ as } h \to 0, \qquad \text{(A}_2\text{)}
  \quad \sup_{x \in D} \int_D |k(x, y)| \, dy < \infty,$$
with $\omega$ the modulus of continuity in the mean (2.8.3). Then the integral operator $K$ on
$C(D)$ that the kernel defines is given at $v \in C(D)$ and $x \in D$ by
$$K v(x) = \int_D k(x, y) v(y) \, dy.$$

The hypotheses are `IntegralOperator.IsAdmissibleKernel (IntegralOperator.regionMeasure D) k`,
which states (A₁) in the $\varepsilon$–$\delta$ form. The limit $\omega(h) \to 0$ is
`IntegralOperator.IsAdmissibleKernel.tendsto_kernelModulus`, and (A₂), the bound (2.8.4), is the
field `IntegralOperator.IsAdmissibleKernel.bddAbove_integral_abs`. The operator is
`IntegralOperator.admissibleKernelCLM`. -/
theorem equation_2_8_2 (u : C(D, ℝ)) (x : D) :
    admissibleKernelCLM hk u x = ∫ y, k (x, y) * u y ∂(regionMeasure D) :=
  rfl

/-- **Equation (2.8.5)** of [han2009theoretical]. Let $k$ be a kernel on a compact
$D \subseteq \mathbb{R}^d$ that satisfies the hypotheses of (2.8.2), with integral operator $K$.
Then for $v \in C(D)$ and $x, z \in D$,
$$|K v(x) - K v(z)| \le \omega(\|x - z\|) \, \|v\|_\infty,$$
where $\omega(h) = \sup_{\|x - z\| \le h} \int_D |k(x, y) - k(z, y)| \, dy$ is the modulus of
continuity in the mean (2.8.3).

The function $\omega$ is `IntegralOperator.kernelModulus`. This estimate makes the image of the
unit ball equicontinuous.

**Reading.** The bound is stated for $v \in C(D)$. The source also allows bounded
integrable inputs. -/
theorem equation_2_8_5 (u : C(D, ℝ)) (x z : D) :
    |admissibleKernelCLM hk u x - admissibleKernelCLM hk u z|
      ≤ kernelModulus (regionMeasure D) k (dist x z) * ‖u‖ :=
  hk.abs_admissibleKernelCLM_sub_le u x z

/-- **Equation (2.8.6)** of [han2009theoretical], upper bound. Let $k$ be a kernel on a compact
$D \subseteq \mathbb{R}^d$ that satisfies the hypotheses of (2.8.2), with integral operator $K$.
Then
$$\|K\| \le \sup_{x \in D} \int_D |k(x, y)| \, dy.$$

The equality is `AtkinsonHan.Chapter02.equation_2_8_6`. -/
theorem equation_2_8_6_le :
    ‖admissibleKernelCLM hk‖ ≤ ⨆ x, ∫ y, |k (x, y)| ∂(regionMeasure D) :=
  norm_admissibleKernelCLM_le hk

/-- **Equation (2.8.6)** of [han2009theoretical]. Let $k$ be a kernel on a compact
$D \subseteq \mathbb{R}^d$ that satisfies the hypotheses of (2.8.2), with integral operator $K$.
Then
$$\|K\| = \sup_{x \in D} \int_D |k(x, y)| \, dy.$$

**Reading.** The source writes a maximum over $x$. Condition (A₁) makes the row integral
continuous by bounding its change by $\omega(\|x-z\|)$. Thus the maximum exists for nonempty
compact $D$. The supremum also covers the empty case.

The supremum is the real `⨆`, which is a genuine supremum by (A₂). The proof of the lower bound
tests $K$ against a continuous approximation to the sign of one row of the kernel, which exists
because $C(D)$ is dense in $L^1(D)$. -/
theorem equation_2_8_6 :
    ‖admissibleKernelCLM hk‖ = ⨆ x, ∫ y, |k (x, y)| ∂(regionMeasure D) :=
  norm_admissibleKernelCLM hk

/-- **Section 2.8.1** of [han2009theoretical], compactness. Let $k$ be a kernel on a compact
$D \subseteq \mathbb{R}^d$ that satisfies the hypotheses of (2.8.2), that is, the conditions
(A₁) and (A₂). Then the integral operator $K v(x) = \int_D k(x, y) v(y) \, dy$ is compact on
$C(D)$.

The proof applies the Arzelà–Ascoli theorem (Theorem 1.6.3) to the image of the unit ball, which
is uniformly bounded by (2.8.6) and equicontinuous by (2.8.5).
`AtkinsonHan.Chapter02.example_2_8_2` and `AtkinsonHan.Chapter02.example_2_8_9` are the two
instances that the source gives. -/
theorem isCompactOperator_of_isAdmissibleKernel :
    IsCompactOperator (admissibleKernelCLM hk) :=
  isCompactOperator_admissibleKernelCLM hk

end WeaklySingular

/-! ### Examples 2.8.2 and 2.8.9: the two weakly singular kernels of an interval -/

section SingularExamples

open MeasureTheory IntegralOperator

open scoped Real

/-- **Example 2.8.9** of [han2009theoretical]. Let $a \le b$ and $0 < \gamma < 1$. The kernel
$$k(x, y) = |x - y|^{-\gamma}$$
of (2.8.14) gives a compact integral operator on $C[a, b]$.

The kernel takes the value $0$ on the diagonal $x = y$, because `Real.rpow` gives
$0^{-\gamma} = 0$; this is a set of measure zero. The source truncates $k$ at height $n^\gamma$
as in (2.8.15). The stated value $2\gamma / ((1 - \gamma) n^{1 - \gamma})$ for $\|K - K_n\|$
is an upper bound for general intervals, with equality when a row contains the full interval
of distances $1/n$ on both sides of the singularity. The backbone uses the truncation in the
(A₁)–(A₂) framework of
§2.8.1, so that the operator is the one of (2.8.2), and needs only that $\|K - K_n\| \to 0$. The
admissibility is `IntegralOperator.isAdmissibleKernel_abs_sub_rpow`.

**Reading.** Assigns zero on the measure-zero diagonal; proves the compactness conclusion without
stating the printed truncation equality.
-/
theorem example_2_8_9 {a b γ : ℝ} (hab : a ≤ b) (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    IsCompactOperator
      (admissibleKernelCLM (isAdmissibleKernel_abs_sub_rpow hab hγ0 hγ1)) :=
  isCompactOperator_admissibleKernelCLM _

/-- **Example 2.8.2** of [han2009theoretical]. The kernel
$$k(x, y) = \log|\cos x - \cos y|$$
gives a compact integral operator on $C[0, \pi]$.

The kernel takes the value $0$ on the diagonal, because `Real.log 0 = 0`; this is a set of
measure zero. The source writes $k(x, y) = |x - y|^{-1/2} \cdot \left(|x - y|^{1/2} \log|\cos
x - \cos y|\right)$ as in (2.8.10), with a continuous second factor, and applies the splitting
rule (2.8.9). The backbone reads that factorization as the bound
$|\log|\cos x - \cos y|| \le C |x - y|^{-1/2}$ instead, which
`IntegralOperator.isAdmissibleKernel_log_cos_sub_cos` proves.

**Reading.** Assigns zero on the measure-zero singular diagonal and proves the same compactness
using a kernel bound.
-/
theorem example_2_8_2 :
    IsCompactOperator (admissibleKernelCLM isAdmissibleKernel_log_cos_sub_cos) :=
  isCompactOperator_admissibleKernelCLM _

end SingularExamples

section Banach

variable {𝕜 V W : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [NormedAddCommGroup W] [NormedSpace 𝕜 W]

/-! ### Theorem 2.8.10: the Fredholm alternative -/

section Fredholm

variable [CompleteSpace V] {K : V →L[𝕜] V} {l : 𝕜}

/-- If $K$ is compact on a Banach space, $\lambda \neq 0$ and $\lambda - K$ is injective, then
$\lambda - K$ is a unit of the algebra of bounded operators. -/
private theorem isUnit_smul_one_sub (hK : IsCompactOperator K) (hl : l ≠ 0)
    (hinj : ∀ u : V, (l • (1 : V →L[𝕜] V) - K) u = 0 → u = 0) :
    IsUnit (l • (1 : V →L[𝕜] V) - K) := by
  have hne : ¬ HasEigenvalue (K : Module.End 𝕜 V) l := by
    intro hev
    refine hev (Submodule.eq_bot_iff _ |>.2 fun u hu => hinj u ?_)
    rw [mem_eigenspace_iff] at hu
    have hu' : K u = l • u := hu
    simp [hu']
  have hres := (hK.hasEigenvalue_or_mem_resolventSet hl).resolve_left hne
  rw [spectrum.mem_resolventSet_iff, Algebra.algebraMap_eq_smul_one] at hres
  exact hres

/-- **Theorem 2.8.10** of [han2009theoretical] (Fredholm alternative). Let $V$ be a Banach space,
let $K : V \to V$ be compact and let $\lambda \neq 0$. Then the equation $(\lambda - K) u = f$
has a unique solution $u \in V$ for every $f \in V$ if and only if the homogeneous equation
$(\lambda - K) u = 0$ has only the solution $u = 0$.

The bounded inverse is `AtkinsonHan.Chapter02.theorem_2_8_10_inverse`. The proof uses Mathlib's
`IsCompactOperator.hasEigenvalue_or_mem_resolventSet`. -/
theorem theorem_2_8_10 (hK : IsCompactOperator K) (hl : l ≠ 0) :
    (∀ f : V, ∃! u : V, (l • (1 : V →L[𝕜] V) - K) u = f) ↔
      ∀ u : V, (l • (1 : V →L[𝕜] V) - K) u = 0 → u = 0 := by
  constructor
  · intro h u hu
    obtain ⟨z, -, huniq⟩ := h 0
    rw [huniq u hu, ← huniq 0 (by simp)]
  · intro hinj
    have hbij := ContinuousLinearMap.isUnit_iff_bijective.1 (isUnit_smul_one_sub hK hl hinj)
    exact fun f => (hbij.existsUnique f)

/-- **Theorem 2.8.10** of [han2009theoretical], the bounded inverse. Let $V$ be a Banach space, let
$K : V \to V$ be compact and let $\lambda \neq 0$. If $(\lambda - K) u = 0$ implies $u = 0$,
then $\lambda - K$ is a bijection of $V$ onto $V$ with a bounded inverse.

The bounded inverse is a continuous linear equivalence `e : V ≃L[𝕜] V` whose underlying map is
$\lambda - K$. The source obtains it from the bounded inverse theorem, Theorem 2.4.3, and so
does the proof. -/
theorem theorem_2_8_10_inverse (hK : IsCompactOperator K) (hl : l ≠ 0)
    (hinj : ∀ u : V, (l • (1 : V →L[𝕜] V) - K) u = 0 → u = 0) :
    ∃ e : V ≃L[𝕜] V, (e : V →L[𝕜] V) = l • (1 : V →L[𝕜] V) - K :=
  theorem_2_4_3 _ (ContinuousLinearMap.isUnit_iff_bijective.1 (isUnit_smul_one_sub hK hl hinj))

end Fredholm

end Banach

/-! ### Definition 2.8.11: eigenvalues and eigenvectors -/

section Eigen

variable {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]

/-- **Definition 2.8.11** of [han2009theoretical]. Let $V$ be a linear space over a field
$\mathbb{K}$ and let $K : V \to V$. A scalar $\lambda$ is an **eigenvalue** of $K$ if
$K u = \lambda u$ for some $u \neq 0$.

The map $K$ need not be linear here. By `AtkinsonHan.Chapter02.definition_2_8_11_iff` the
definition is Mathlib's `Module.End.HasEigenvalue` for a linear $K$, in which the theorems of
this module are stated.

**Generalization.** The eigenvalue condition is stated over any field. -/
def definition_2_8_11 (𝕜 : Type*) {V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]
    (K : V → V) (l : 𝕜) : Prop :=
  ∃ u : V, u ≠ 0 ∧ K u = l • u

/-- **Definition 2.8.11** of [han2009theoretical], eigenvectors. Let $V$ be a linear space over a
field $\mathbb{K}$ and let $K : V \to V$. A vector $u$ is an **eigenvector** of $K$ for the
eigenvalue $\lambda$ if $u \neq 0$ and $K u = \lambda u$.

By `AtkinsonHan.Chapter02.definition_2_8_11_eigenvector_iff` this is Mathlib's
`Module.End.HasEigenvector` for a linear $K$.

**Generalization.** The eigenvector condition is stated over any field. -/
def definition_2_8_11_eigenvector (𝕜 : Type*) {V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]
    (K : V → V) (l : 𝕜) (u : V) : Prop :=
  u ≠ 0 ∧ K u = l • u

/-- **Definition 2.8.11** of [han2009theoretical], identification of eigenvectors. For a linear
operator $K$ on $V$, a vector $u$ is an eigenvector of $K$ for $\lambda$ in the sense of
Definition 2.8.11 if and only if `Module.End.HasEigenvector K l u` holds. -/
theorem definition_2_8_11_eigenvector_iff (K : Module.End 𝕜 V) (l : 𝕜) (u : V) :
    definition_2_8_11_eigenvector 𝕜 K l u ↔ HasEigenvector K l u := by
  rw [definition_2_8_11_eigenvector, hasEigenvector_iff, mem_eigenspace_iff, and_comm]

/-- **Definition 2.8.11** of [han2009theoretical], identification of eigenvalues. For a linear
operator $K$ on $V$, a scalar $\lambda$ is an eigenvalue of $K$ in the sense of Definition
2.8.11 if and only if `Module.End.HasEigenvalue K l` holds. -/
theorem definition_2_8_11_iff (K : Module.End 𝕜 V) (l : 𝕜) :
    definition_2_8_11 𝕜 K l ↔ HasEigenvalue K l := by
  constructor
  · rintro ⟨u, hu0, hu⟩
    exact hasEigenvalue_of_hasEigenvector
      ((definition_2_8_11_eigenvector_iff K l u).mp ⟨hu0, hu⟩)
  · intro h
    obtain ⟨u, hu⟩ := h.exists_hasEigenvector
    exact ⟨u, ((definition_2_8_11_eigenvector_iff K l u).mpr hu).1,
      ((definition_2_8_11_eigenvector_iff K l u).mpr hu).2⟩

end Eigen

section Banach

variable {𝕜 V W : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [NormedAddCommGroup W] [NormedSpace 𝕜 W]

/-! ### Theorem 2.8.12: the spectrum of a compact operator -/

/-- **Theorem 2.8.12(1)** of [han2009theoretical]. Let $V$ be a normed space and let $K : V \to V$
be compact. For every $\varepsilon > 0$, the set of eigenvalues $\mu$ of $K$ with
$|\mu| \ge \varepsilon$ is finite. Hence the eigenvalues of $K$ can accumulate only at $0$.

**Generalization.** Lean uses finiteness away from zero over either real or complex scalars
without requiring completeness. -/
theorem theorem_2_8_12_1 {K : V →L[𝕜] V} (hK : IsCompactOperator K) {ε : ℝ} (hε : 0 < ε) :
    {μ : 𝕜 | HasEigenvalue (K : Module.End 𝕜 V) μ ∧ ε ≤ ‖μ‖}.Finite :=
  hK.finite_setOf_hasEigenvalue_norm_le hε

/-- **Theorem 2.8.12(2)** of [han2009theoretical]. Let $V$ be a Banach space, let $K : V \to V$ be
compact and let $\mu \neq 0$. Then the eigenspace $\mathcal{N}(\mu - K)$ is finite dimensional.

The statement holds for every $\mu \neq 0$; if $\mu$ is not an eigenvalue, the eigenspace is
$\{0\}$. -/
theorem theorem_2_8_12_2 [CompleteSpace V] {K : V →L[𝕜] V} (hK : IsCompactOperator K) (μ : 𝕜)
    (hμ : μ ≠ 0) : FiniteDimensional 𝕜 (eigenspace K.toLinearMap μ) := by
  have hinv : ∀ v ∈ eigenspace K.toLinearMap μ, K.toLinearMap v ∈ eigenspace K.toLinearMap μ :=
    (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem _).mp
      (Module.End.eigenspace_mem_invtSubmodule K.toLinearMap μ)
  have hclosed : IsClosed ((eigenspace K.toLinearMap μ : Submodule 𝕜 V) : Set V) := by
    have hset : ((eigenspace K.toLinearMap μ : Submodule 𝕜 V) : Set V)
        = {v : V | K v - μ • v = 0} := by
      ext v
      simp [SetLike.mem_coe, sub_eq_zero]
    rw [hset]
    exact isClosed_eq (by fun_prop) continuous_const
  have : CompleteSpace (eigenspace K.toLinearMap μ) :=
    completeSpace_coe_iff_isComplete.2 hclosed.isComplete
  replace hK := hK.restrict' hinv
  rw [Module.End.restrict_eigenspace, LinearMap.coe_smul, IsCompactOperator.smul_iff₀ hμ] at hK
  rwa [← isCompactOperator_id_iff_finiteDimensional]

/-- **Theorem 2.8.12(4)** of [han2009theoretical]. Let $V$ be a normed space, let $K : V \to V$ be
compact and let $\lambda \neq 0$. Then the range $\mathcal{R}(\lambda - K)$ is closed in $V$.

**Generalization.** The closed-range conclusion does not require completeness. -/
theorem theorem_2_8_12_4 {K : V →L[𝕜] V} (hK : IsCompactOperator K) {l : 𝕜} (hl : l ≠ 0) :
    IsClosed ((LinearMap.range ((l • (1 : V →L[𝕜] V) - K) : V →ₗ[𝕜] V)) : Set V) :=
  hK.isClosed_range_smul_sub hl

/-- If $\lambda$ is an eigenvalue of $K$, then $\mathcal{N}((\lambda - K)^1) \neq \{0\}$. -/
private theorem ker_smul_one_sub_ne_bot {K : V →L[𝕜] V} {l : 𝕜}
    (hev : HasEigenvalue (K : Module.End 𝕜 V) l) :
    ((l • (1 : V →L[𝕜] V) - K) ^ 1).ker ≠ ⊥ := by
  rw [pow_one]
  intro h
  refine hev (Submodule.eq_bot_iff _ |>.2 fun u hu => ?_)
  rw [mem_eigenspace_iff] at hu
  have hu' : K u = l • u := hu
  exact (Submodule.eq_bot_iff _).1 h u (by simp [hu'])

/-- **Theorem 2.8.12(3)** of [han2009theoretical]. Let $V$ be a normed space, let $K : V \to V$ be
compact, and let $\lambda \neq 0$ be an eigenvalue of $K$. Then there is an integer
$\nu = \nu(\lambda) \ge 1$, the **index** of $\lambda$, such that the null spaces
$\mathcal{N}((\lambda - K)^j)$ increase strictly for $j \le \nu$ and are constant from $\nu$ on
(2.8.27):
$$\mathcal{N}((\lambda - K)^0) \subsetneq \mathcal{N}((\lambda - K)^1) \subsetneq \cdots
  \subsetneq \mathcal{N}((\lambda - K)^{\nu}) = \mathcal{N}((\lambda - K)^{\nu + 1}) = \cdots.$$
Moreover $\mathcal{N}((\lambda - K)^{\nu})$ is finite dimensional.

The proof specializes the Riesz theory of `Numlib.Analysis.Normed.Operator.Riesz`.

**Generalization.** The index and its finite-dimensional generalized eigenspace are stated
without completeness. -/
theorem theorem_2_8_12_3 {K : V →L[𝕜] V} (hK : IsCompactOperator K) {l : 𝕜} (hl : l ≠ 0)
    (hev : HasEigenvalue (K : Module.End 𝕜 V) l) :
    ∃ ν : ℕ, 1 ≤ ν ∧
      (∀ j < ν, ((l • (1 : V →L[𝕜] V) - K) ^ j).ker
        < ((l • (1 : V →L[𝕜] V) - K) ^ (j + 1)).ker) ∧
      (∀ j, ν ≤ j → ((l • (1 : V →L[𝕜] V) - K) ^ j).ker
        = ((l • (1 : V →L[𝕜] V) - K) ^ ν).ker) ∧
      FiniteDimensional 𝕜 (((l • (1 : V →L[𝕜] V) - K) ^ ν).ker) := by
  obtain ⟨ν, hstrict, hstab, -, -⟩ := hK.exists_riesz_index hl
  refine ⟨ν, ?_, hstrict, hstab, hK.finiteDimensional_ker_pow hl ν⟩
  by_contra hν
  refine ker_smul_one_sub_ne_bot hev ?_
  rw [hstab 1 (by omega), ← hstab 0 (by omega), pow_zero]
  exact Submodule.eq_bot_iff _ |>.2 fun u hu => by simpa using hu

/-- **Theorem 2.8.12(5)** of [han2009theoretical]. Let $V$ be a normed space, let $K : V \to V$ be
compact and let $\lambda \neq 0$. Then there is an integer $\nu \ge 0$ such that the null spaces
$\mathcal{N}((\lambda - K)^j)$ increase strictly for $j \le \nu$ and are constant from $\nu$ on,
and such that the decomposition (2.8.28)
$$V = \mathcal{N}((\lambda - K)^{\nu}) \oplus \mathcal{R}((\lambda - K)^{\nu})$$
holds, with both summands invariant under $K$.

The two chain conditions determine $\nu$, and they are those of
`AtkinsonHan.Chapter02.theorem_2_8_12_3`, so for an eigenvalue $\lambda$ this $\nu$ is the index
$\nu(\lambda)$. If $\lambda$ is not an eigenvalue, then $\nu = 0$. The direct sum is the
algebraic one, `IsCompl`.

**Generalization.** Completeness is unnecessary. The formula also holds for a nonzero scalar
that is not an eigenvalue, with index zero. -/
theorem theorem_2_8_12_5 {K : V →L[𝕜] V} (hK : IsCompactOperator K) {l : 𝕜} (hl : l ≠ 0) :
    ∃ ν : ℕ,
      (∀ j < ν, ((l • (1 : V →L[𝕜] V) - K) ^ j).ker
        < ((l • (1 : V →L[𝕜] V) - K) ^ (j + 1)).ker) ∧
      (∀ j, ν ≤ j → ((l • (1 : V →L[𝕜] V) - K) ^ j).ker
        = ((l • (1 : V →L[𝕜] V) - K) ^ ν).ker) ∧
      IsCompl (((l • (1 : V →L[𝕜] V) - K) ^ ν).ker)
        (((l • (1 : V →L[𝕜] V) - K) ^ ν).range) ∧
      (∀ u ∈ ((l • (1 : V →L[𝕜] V) - K) ^ ν).ker,
        K u ∈ ((l • (1 : V →L[𝕜] V) - K) ^ ν).ker) ∧
      (∀ u ∈ ((l • (1 : V →L[𝕜] V) - K) ^ ν).range,
        K u ∈ ((l • (1 : V →L[𝕜] V) - K) ^ ν).range) := by
  obtain ⟨ν, hstrict, hstab, -, hcompl⟩ := hK.exists_riesz_index hl
  exact ⟨ν, hstrict, hstab, hcompl, fun u hu => IsCompactOperator.mapsTo_ker_pow K l ν hu,
    fun u hu => IsCompactOperator.mapsTo_range_pow K l ν hu⟩

/-- **Theorem 2.8.12(6)** of [han2009theoretical]. Let $V$ be a Banach space, let $K : V \to V$ be a
bounded operator such that $K^m$ is compact for some $m$, and let $\lambda \neq 0$. Then the
equation $(\lambda - K) u = f$ has a unique solution $u \in V$ for every $f \in V$ if and only
if $(\lambda - K) u = 0$ has only the solution $u = 0$.

**Reading.** The source takes $m>1$ and extends parts (1)–(5) as well. Lean gives the Fredholm
alternative for any natural exponent with compact $K^m$. -/
theorem theorem_2_8_12_6 [CompleteSpace V] {K : V →L[𝕜] V} {m : ℕ}
    (hK : IsCompactOperator (K ^ m)) {l : 𝕜}
    (hl : l ≠ 0) :
    (∀ f : V, ∃! u : V, (l • (1 : V →L[𝕜] V) - K) u = f) ↔
      ∀ u : V, (l • (1 : V →L[𝕜] V) - K) u = 0 → u = 0 := by
  constructor
  · intro h u hu
    obtain ⟨z, -, huniq⟩ := h 0
    rw [huniq u hu, ← huniq 0 (by simp)]
  · intro hinj
    have hbij := ContinuousLinearMap.isUnit_iff_bijective.1
      (hK.isUnit_smul_one_sub_of_isCompactOperator_pow hl hinj)
    exact fun f => hbij.existsUnique f

end Banach

/-! ### Lemma 2.8.13, Theorem 2.8.14 and Theorem 2.8.15: the Hilbert space case -/

section Hilbert

variable {𝕜 V W : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] [CompleteSpace V] [CompleteSpace W]

/-- **Lemma 2.8.13** of [han2009theoretical] (Schauder's theorem). Let $V$ and $W$ be Hilbert spaces
and let $K : V \to W$ be compact. Then the adjoint $K^* : W \to V$ is compact.

**Generalization.** The real and complex cases and maps between two Hilbert spaces are included. -/
theorem lemma_2_8_13 {K : V →L[𝕜] W} (hK : IsCompactOperator K) :
    IsCompactOperator (ContinuousLinearMap.adjoint K) :=
  hK.adjoint

/-- **Theorem 2.8.14(2)** of [han2009theoretical], (2.8.29). Let $V$ be a Hilbert space, let
$K : V \to V$ be compact and let $\lambda \neq 0$. Then
$$\mathcal{R}(\lambda - K) = \mathcal{N}(\bar\lambda - K^*)^\perp,$$
that is, the equation $(\lambda - K) u = f$ has a solution if and only if $f$ is orthogonal to
every solution $v$ of the homogeneous adjoint equation $(\bar\lambda - K^*) v = 0$.

The adjoint $K^*$ is `ContinuousLinearMap.adjoint K`. The conjugate $\bar\lambda$ is
`starRingEnd 𝕜 l`.

**Generalization.** The formula holds for all nonzero scalars in real and complex Hilbert
spaces. The source begins with a nonzero complex eigenvalue. -/
theorem theorem_2_8_14 {K : V →L[𝕜] V} (hK : IsCompactOperator K) {l : 𝕜} (hl : l ≠ 0) :
    LinearMap.range ((l • (1 : V →L[𝕜] V) - K) : V →ₗ[𝕜] V) =
      (LinearMap.ker (((starRingEnd 𝕜) l • (1 : V →L[𝕜] V) -
        ContinuousLinearMap.adjoint K : V →L[𝕜] V) : V →ₗ[𝕜] V))ᗮ :=
  hK.range_smul_sub_eq_orthogonal_ker_adjoint hl

/-- **Theorem 2.8.14(2)** of [han2009theoretical], the decomposition (2.8.30). Let $V$ be a Hilbert
space, let $K : V \to V$ be compact and let $\lambda \neq 0$. Then $V$ is the direct sum
$$V = \mathcal{N}(\bar\lambda - K^*) \oplus \mathcal{R}(\lambda - K).$$

The direct sum is stated as `IsCompl`. By `AtkinsonHan.Chapter02.theorem_2_8_14` the two
summands are orthogonal complements of each other.

**Generalization.** The direct-sum formula also holds for real scalars and for a nonzero
scalar that is not an eigenvalue. -/
theorem theorem_2_8_14_isCompl {K : V →L[𝕜] V} (hK : IsCompactOperator K) {l : 𝕜} (hl : l ≠ 0) :
    IsCompl (LinearMap.ker (((starRingEnd 𝕜) l • (1 : V →L[𝕜] V) -
        ContinuousLinearMap.adjoint K : V →L[𝕜] V) : V →ₗ[𝕜] V))
      (LinearMap.range ((l • (1 : V →L[𝕜] V) - K) : V →ₗ[𝕜] V)) := by
  rw [theorem_2_8_14 hK hl]
  have hclosed := hK.isClosed_range_smul_sub hl
  have : CompleteSpace (LinearMap.ker (((starRingEnd 𝕜) l • (1 : V →L[𝕜] V) -
      ContinuousLinearMap.adjoint K : V →L[𝕜] V) : V →ₗ[𝕜] V)) := by
    refine completeSpace_coe_iff_isComplete.2 (IsClosed.isComplete ?_)
    exact (ContinuousLinearMap.isClosed_ker _)
  exact Submodule.isCompl_orthogonal _

/-- **Theorem 2.8.14(1)** of [han2009theoretical], the eigenvalue of the adjoint. Let $V$ be a
Hilbert space, let $K : V \to V$ be compact, and let $\lambda \neq 0$ be an eigenvalue of $K$.
Then $\bar\lambda$ is an eigenvalue of $K^*$.

If $\bar\lambda$ were not an eigenvalue, the Fredholm alternative for the compact operator $K^*$
would make $\bar\lambda - K^*$ bijective. But `AtkinsonHan.Chapter02.theorem_2_8_14` for $K^*$
gives $\mathcal{R}(\bar\lambda - K^*) = \mathcal{N}(\lambda - K)^\perp$, a proper subspace
because $\lambda$ is an eigenvalue of $K$. The equality of the dimensions is
`AtkinsonHan.Chapter02.theorem_2_8_14_dim`.

**Generalization.** The result also holds for real Hilbert spaces. -/
theorem theorem_2_8_14_hasEigenvalue_adjoint {K : V →L[𝕜] V} (hK : IsCompactOperator K) {l : 𝕜}
    (hl : l ≠ 0) (hev : HasEigenvalue (K : Module.End 𝕜 V) l) :
    HasEigenvalue ((ContinuousLinearMap.adjoint K : V →L[𝕜] V) : Module.End 𝕜 V)
      ((starRingEnd 𝕜) l) := by
  have hl' : (starRingEnd 𝕜) l ≠ 0 := by simpa using hl
  by_contra hno
  have hres := (hK.adjoint.hasEigenvalue_or_mem_resolventSet hl').resolve_left hno
  rw [spectrum.mem_resolventSet_iff, Algebra.algebraMap_eq_smul_one] at hres
  have hsurj : Function.Surjective
      ((starRingEnd 𝕜) l • (1 : V →L[𝕜] V) - ContinuousLinearMap.adjoint K) :=
    (ContinuousLinearMap.isUnit_iff_bijective.1 hres).2
  have hrange : LinearMap.range
      (((starRingEnd 𝕜) l • (1 : V →L[𝕜] V) - ContinuousLinearMap.adjoint K : V →L[𝕜] V) :
        V →ₗ[𝕜] V) = ⊤ := LinearMap.range_eq_top.2 hsurj
  have h14 : LinearMap.range
      (((starRingEnd 𝕜) l • (1 : V →L[𝕜] V) - ContinuousLinearMap.adjoint K : V →L[𝕜] V) :
        V →ₗ[𝕜] V) = (LinearMap.ker ((l • (1 : V →L[𝕜] V) - K : V →L[𝕜] V) : V →ₗ[𝕜] V))ᗮ := by
    simpa using theorem_2_8_14 hK.adjoint hl'
  rw [h14] at hrange
  have hbot : LinearMap.ker ((l • (1 : V →L[𝕜] V) - K : V →L[𝕜] V) : V →ₗ[𝕜] V) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    have hmem : x ∈ (LinearMap.ker ((l • (1 : V →L[𝕜] V) - K : V →L[𝕜] V) : V →ₗ[𝕜] V))ᗮ := by
      rw [hrange]; trivial
    exact inner_self_eq_zero.1 (hmem x hx)
  refine hev (Submodule.eq_bot_iff _ |>.2 fun u hu => ?_)
  rw [mem_eigenspace_iff] at hu
  have hu' : K u = l • u := hu
  have hker : u ∈ LinearMap.ker ((l • (1 : V →L[𝕜] V) - K : V →L[𝕜] V) : V →ₗ[𝕜] V) := by
    simp [hu']
  rw [hbot, Submodule.mem_bot] at hker
  exact hker

/-- **Theorem 2.8.14(1)** of [han2009theoretical], the dimensions. Let $V$ be a Hilbert space, let
$K : V \to V$ be compact and let $\lambda \neq 0$. Then
$$\dim \mathcal{N}(\lambda - K) = \dim \mathcal{N}(\bar\lambda - K^*).$$

Both null spaces are finite dimensional by Theorem 2.8.12(2), so `Module.finrank` is their
dimension. Equivalently, $\lambda - K$ has Fredholm index zero: the equation
$(\lambda - K) u = f$ has as many independent homogeneous solutions as the adjoint equation,
which is the number of conditions in the solvability criterion (2.8.29) of
`AtkinsonHan.Chapter02.theorem_2_8_14`.

**Generalization.** The dimensions also agree for real scalars and for every nonzero scalar. -/
theorem theorem_2_8_14_dim {K : V →L[𝕜] V} (hK : IsCompactOperator K) {l : 𝕜} (hl : l ≠ 0) :
    Module.finrank 𝕜 ((l • (1 : V →L[𝕜] V) - K).ker)
      = Module.finrank 𝕜 (((starRingEnd 𝕜) l • (1 : V →L[𝕜] V)
          - ContinuousLinearMap.adjoint K).ker) :=
  hK.finrank_ker_eq_finrank_ker_adjoint hl

/-- **Theorem 2.8.15** of [han2009theoretical] (spectral theorem for compact self-adjoint
operators). Let $V$ be a Hilbert space and let $K : V \to V$ be compact and self-adjoint. Then
the orthogonal complement of the closed span of all eigenspaces of $K$ is $\{0\}$:
$$\Bigl(\bigvee_{\mu} \mathcal{N}(\mu - K)\Bigr)^\perp = \{0\}.$$
So the eigenvectors of $K$ span a dense subspace of $V$, and $V$ has an orthonormal basis of
eigenvectors of $K$.

The proof is Mathlib's `ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot`.

**Reading.** This clause gives density using all eigenspaces, including the kernel.
The nonzero eigenvectors are dense in the closure of the range of $K$, the range used in the
formal enumeration. -/
theorem theorem_2_8_15 {K : V →L[𝕜] V} (hKc : IsCompactOperator K) (hK : IsSelfAdjoint K) :
    (⨆ μ, eigenspace (K : Module.End 𝕜 V) μ)ᗮ = ⊥ :=
  ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hKc
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 hK)

/-- **Theorem 2.8.15** of [han2009theoretical], the eigenvalues are real. Let $V$ be a Hilbert space
and let $K : V \to V$ be self-adjoint. Then every eigenvalue $\mu$ of $K$ is real:
$\bar\mu = \mu$.

**Generalization.** No compactness is assumed. -/
theorem theorem_2_8_15_eigenvalue_real {K : V →L[𝕜] V} (hK : IsSelfAdjoint K) {μ : 𝕜}
    (hμ : HasEigenvalue (K : Module.End 𝕜 V) μ) : (starRingEnd 𝕜) μ = μ :=
  (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 hK).conj_eigenvalue_eq_self hμ

/-- **Theorem 2.8.15** of [han2009theoretical], index one. Let $V$ be a Hilbert space, let
$K : V \to V$ be self-adjoint and let $\lambda$ be real. Then
$$\mathcal{N}((\lambda - K)^2) = \mathcal{N}(\lambda - K).$$
In particular every eigenvalue of $K$ has index one in the sense of Theorem 2.8.12(3).

**Generalization.** No compactness is assumed. The general Riesz theory of Theorem 2.8.12(3) is
not needed: for real $\lambda$ the operator $\lambda - K$ is self-adjoint, so
$(\lambda - K)^2 v = 0$ gives $\|(\lambda - K) v\|^2 = ((\lambda - K)^2 v, v) = 0$.

The eigenvalues of $K$ are real by `AtkinsonHan.Chapter02.theorem_2_8_15_eigenvalue_real`, so
the hypothesis $\bar\lambda = \lambda$ holds for them. The proof is the backbone's
`IsSelfAdjoint.ker_sq_smul_sub_eq_ker`. -/
theorem theorem_2_8_15_index {K : V →L[𝕜] V} (hK : IsSelfAdjoint K) {l : 𝕜}
    (hl : (starRingEnd 𝕜) l = l) :
    LinearMap.ker (((l • (1 : V →L[𝕜] V) - K) ^ 2 : V →L[𝕜] V) : V →ₗ[𝕜] V) =
      LinearMap.ker ((l • (1 : V →L[𝕜] V) - K : V →L[𝕜] V) : V →ₗ[𝕜] V) :=
  hK.ker_sq_smul_sub_eq_ker hl

/-- **Theorem 2.8.15** of [han2009theoretical], the closure of the range. Let $V$ be a Hilbert space
and let $K : V \to V$ be self-adjoint. Then
$$\mathcal{N}(K)^\perp = \overline{\mathcal{R}(K)}.$$
This closed subspace contains the eigenvectors for the nonzero eigenvalues.

**Generalization.** No compactness is assumed. -/
theorem theorem_2_8_15_closure_range {K : V →L[𝕜] V} (hK : IsSelfAdjoint K) :
    (LinearMap.ker (K : V →ₗ[𝕜] V))ᗮ =
      (LinearMap.range (K : V →ₗ[𝕜] V)).topologicalClosure := by
  have hadj : ContinuousLinearMap.adjoint K = K := by
    rw [← ContinuousLinearMap.star_eq_adjoint]
    exact hK
  rw [← Submodule.orthogonal_orthogonal_eq_closure]
  congr 1
  rw [ContinuousLinearMap.orthogonal_range K, hadj]

/-- **Theorem 2.8.15** of [han2009theoretical], the enumeration (2.8.31)–(2.8.32). Let $V$ be an
infinite-dimensional Hilbert space and let $K : V \to V$ be compact, self-adjoint and injective.
Then there are real numbers $\lambda_j \neq 0$ and vectors $u_j \in V$, $j \ge 0$, such that
$$|\lambda_0| \ge |\lambda_1| \ge \cdots > 0, \qquad \lambda_j \to 0,$$
the family $(u_j)$ is orthonormal, $K u_j = \lambda_j u_j$ for every $j$, and the closed span of
the $u_j$ is $\overline{\mathcal{R}(K)}$.

**Reading.** The sequence is indexed from $0$. The proof uses the backbone's enumeration of
the full eigenbasis in the injective infinite-dimensional case. For a general operator,
enumerating just the nonzero eigenvectors can give a finite or infinite list even when the
kernel is nontrivial. Under the formal hypotheses,
$\overline{\mathcal{R}(K)} = V$ by `AtkinsonHan.Chapter02.theorem_2_8_15_closure_range`.

**Correction.** The source prints the closure of the range of $\lambda I-K$. For $K=I$ on a
nonzero finite-dimensional space, that range at $\lambda=1$ is zero. The nonzero eigenvectors
span the entire space, which is the closure of the range of $K$. -/
theorem theorem_2_8_15_enumeration {K : V →L[𝕜] V} (hKc : IsCompactOperator K)
    (hK : IsSelfAdjoint K) (hinj : LinearMap.ker (K : V →ₗ[𝕜] V) = ⊥)
    (hfin : ¬ FiniteDimensional 𝕜 V) :
    ∃ (l : ℕ → ℝ) (u : ℕ → V),
      Antitone (fun j => |l j|) ∧ (∀ j, l j ≠ 0) ∧ Tendsto l atTop (𝓝 0) ∧
        Orthonormal 𝕜 u ∧ (∀ j, K (u j) = ((l j : ℝ) : 𝕜) • u j) ∧
        (Submodule.span 𝕜 (Set.range u)).topologicalClosure =
          (LinearMap.range (K : V →ₗ[𝕜] V)).topologicalClosure := by
  have hsym : (K : V →ₗ[𝕜] V).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 hK
  have horth := ContinuousLinearMap.IsSymmetric.orthonormal_eigenvector hsym hKc hfin
  have happ := ContinuousLinearMap.IsSymmetric.apply_eigenvector hsym hKc hfin
  refine ⟨ContinuousLinearMap.IsSymmetric.eigenvalueSeq hsym hKc,
    ContinuousLinearMap.IsSymmetric.eigenvector hsym hKc,
    ContinuousLinearMap.IsSymmetric.eigenvalueSeq_antitone hsym hKc, fun j h0 => ?_,
    ContinuousLinearMap.IsSymmetric.tendsto_eigenvalueSeq_zero hsym hKc, horth, happ, ?_⟩
  · have hz : K (ContinuousLinearMap.IsSymmetric.eigenvector hsym hKc j) = 0 := by
      rw [happ j, h0]; simp
    have hmem : ContinuousLinearMap.IsSymmetric.eigenvector hsym hKc j ∈
        LinearMap.ker (K : V →ₗ[𝕜] V) := hz
    rw [hinj, Submodule.mem_bot] at hmem
    have hone := horth.1 j
    rw [hmem, norm_zero] at hone
    exact one_ne_zero hone.symm
  · have hbot : (Submodule.span 𝕜
        (Set.range (ContinuousLinearMap.IsSymmetric.eigenvector hsym hKc)))ᗮ = ⊥ :=
      le_bot_iff.1 (hinj ▸
        ContinuousLinearMap.IsSymmetric.orthogonal_span_range_eigenvector_le_ker hsym hKc hfin)
    have hL : (Submodule.span 𝕜
        (Set.range (ContinuousLinearMap.IsSymmetric.eigenvector hsym hKc))).topologicalClosure
          = ⊤ := by
      rw [← Submodule.orthogonal_orthogonal_eq_closure, hbot, Submodule.bot_orthogonal_eq_top]
    have hR : (LinearMap.range (K : V →ₗ[𝕜] V)).topologicalClosure = ⊤ := by
      rw [← theorem_2_8_15_closure_range hK, hinj, Submodule.bot_orthogonal_eq_top]
    rw [hL, hR]

end Hilbert

end AtkinsonHan.Chapter02
