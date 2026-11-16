/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.l2Space
import Numlib.Analysis.Fourier.TrigonometricBasis
import Numlib.Analysis.InnerProductSpace.ConvexProjection
import Numlib.Analysis.Normed.Module.BestApprox
import Numlib.Approximation.OrthogonalPolynomial
import NumlibSurface.AtkinsonHan.Chapter03.Section03

/-!
# Atkinson and Han, Section 3.4: Best approximation in inner product spaces

This module formalizes §3.4 of [han2009theoretical]. Let $K$ be a convex subset of a real inner
product space $H$ and let $u \in H$. An element $\hat u \in K$ is a best approximation of $u$ from
$K$ if and only if $(u - \hat u, v - \hat u) \le 0$ for all $v \in K$ (3.4.1), so a best
approximation is unique. In a Hilbert space a nonempty closed convex $K$ has a best approximation
$P_K u$ to every $u$, and the map $P_K$ is monotone and non-expansive. When $K$ is a complete
subspace, (3.4.1) becomes the orthogonality condition $(u - \hat u, v) = 0$ for all $v \in K$
(3.4.2), and $P_K$ is the orthogonal projection onto $K$. For an orthonormal family $\{\varphi_i\}$
the best approximation from its span is $\sum_i (u, \varphi_i) \varphi_i$ (3.4.6).

The two examples of the section are least squares approximation by Legendre polynomials in
$L^2(-1, 1)$ and by trigonometric polynomials in $L^2(0, 2\pi)$. In both cases the orthonormal
family is complete, so the truncated expansion converges to $u$. The proofs specialize the metric
projection of `Numlib.Analysis.Normed.Module.BestApprox`, its Hilbert space theory in
`Numlib.Analysis.InnerProductSpace.ConvexProjection`, the Hilbert basis of orthogonal polynomials in
`Numlib.Approximation.OrthogonalPolynomial` and the real trigonometric system of
`Numlib.Analysis.Fourier.TrigonometricBasis`.

## Main definitions

* After Theorem 3.4.3, `AtkinsonHan.Chapter03.projConvex`: the projection $P_K$ onto a nonempty
  closed convex set.
* Example 3.4.8, `AtkinsonHan.Chapter03.legendreNormalized`: the normalized Legendre polynomials
  $L_n = \sqrt{(2n + 1)/2}\, P_n$.
* Example 3.4.8, `AtkinsonHan.Chapter03.legendreHilbertBasis`: the $L_n$ as a Hilbert basis of
  $L^2(-1, 1)$.
* Example 3.4.9, `AtkinsonHan.Chapter03.trigPolyLpLE`: the space $\mathcal{T}_n$ of trigonometric
  polynomials of degree at most $n$, inside $L^2(0, 2\pi)$.

## Main results

* Lemma 3.4.1, `AtkinsonHan.Chapter03.lemma_3_4_1`: for a convex $K$, $\hat u \in K$ is a best
  approximation of $u$ if and only if (3.4.1) holds.
* Corollary 3.4.2, `AtkinsonHan.Chapter03.corollary_3_4_2`: a best approximation from a convex set
  is unique.
* Theorem 3.4.3, `AtkinsonHan.Chapter03.theorem_3_4_3`: in a real Hilbert space, a nonempty closed
  convex set has a unique best approximation to every point.
* Proposition 3.4.4, `AtkinsonHan.Chapter03.proposition_3_4_4` and
  `AtkinsonHan.Chapter03.proposition_3_4_4'`: $P_K$ is monotone and non-expansive.
* Theorem 3.4.5, `AtkinsonHan.Chapter03.theorem_3_4_5`: a nonempty closed convex subset of a
  finite-dimensional subspace has a unique best approximation to every point.
* Theorem 3.4.6, `AtkinsonHan.Chapter03.theorem_3_4_6`: a complete subspace has a unique best
  approximation to every point, characterized by (3.4.2).
* Theorem 3.4.7, `AtkinsonHan.Chapter03.theorem_3_4_7`: the orthogonal projection $P_K$ is
  self-adjoint, satisfies $\|v\|^2 = \|P_K v\|^2 + \|v - P_K v\|^2$, and has norm $\|P_K\| \le 1$,
  with equality if $K \neq \{0\}$.
* Equation (3.4.6), `AtkinsonHan.Chapter03.equation_3_4_6`: the best approximation from the span of
  a finite orthonormal family is $\sum_i (u, \varphi_i) \varphi_i$.
* `AtkinsonHan.Chapter03.hilbertBasis_expansion`: the expansion
  $u = \sum_i (u, \varphi_i) \varphi_i$ in a Hilbert basis.
* Example 3.4.8, `AtkinsonHan.Chapter03.example_3_4_8`: the truncated Legendre expansion is the best
  approximation from the polynomials of degree at most $N$, it converges to $u$ in $L^2(-1, 1)$, and
  Parseval's equality holds.
* Example 3.4.9, `AtkinsonHan.Chapter03.example_3_4_9`: the best $L^2$ approximation from
  $\mathcal{T}_n$ is the $n$-th partial sum of the Fourier series, and the Fourier series converges
  in $L^2$.
* Exercise 3.4.8, `AtkinsonHan.Chapter03.exercise_3_4_8`: for a subspace, (3.4.1) and (3.4.2) are
  equivalent.

## Conventions

* The book works over a real inner product space throughout §3.4. All statements here are over `ℝ`,
  except Theorem 3.4.6, Theorem 3.4.7, (3.4.6) and the Hilbert basis expansion, which are over
  `RCLike 𝕜`.
* The book's inner product $(u, v)$ is linear in its first argument, and Mathlib's `inner 𝕜 u v` is
  linear in its second argument. So the book's $(u - \hat u, v)$ is `inner 𝕜 v (u - uhat)`, and the
  book's $(u, \varphi_i)$ is `inner 𝕜 (φ i) u`. In the real case the two agree.
* "$\hat u$ is a best approximation of $u$ from $K$" is `IsBestApprox K u uhat`: $\hat u \in K$ and
  $\|u - \hat u\| \le \|u - w\|$ for all $w \in K$.
* In Example 3.4.9 the space $L^2(0, 2\pi)$ is $L^2$ of the circle `AddCircle (2 * π)` with its
  probability Haar measure `AddCircle.haarAddCircle`. Its norm is $(2\pi)^{-1/2}$ times the book's
  norm.
* The book's $L^2_w(-1, 1)$ of §3.5 is `Lp ℝ 2 (AtkinsonHan.Chapter03.weightMeasure w)` there, and
  (3.5.2) is the instance of (3.4.6) for an orthonormal polynomial family.

## Deviations from the source

* **Theorem 3.4.7, display (3.4.5)** (correction). The book states $\|P_K\| = 1$. This fails for
  $K = \{0\}$, where $P_K = 0$. The library states $\|P_K\| \le 1$, with equality when
  $K \neq \{0\}$. See `AtkinsonHan.Chapter03.theorem_3_4_7`.
* **Theorems 3.4.6 and 3.4.7, (3.4.6)** (generalization). The book works over $\mathbb{R}$. These
  results are stated over $\mathbb{R}$ or $\mathbb{C}$.
* **Proposition 3.4.4** (generalization). `AtkinsonHan.Chapter03.proposition_3_4_4` states the two
  inequalities for any two best approximations from a convex set, with no completeness of the space.
-/

open Filter Topology

namespace AtkinsonHan.Chapter03

/-! ### The real theory of §3.4 -/

section Real

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- **Lemma 3.4.1** of [han2009theoretical]. Let $H$ be a real inner product space, let
$K \subseteq H$ be convex, and let $u \in H$ and $\hat u \in K$. Then $\hat u$ is a best
approximation of $u$ from $K$ if and only if
$$(u - \hat u, v - \hat u) \le 0 \quad \text{for all } v \in K. \qquad (3.4.1)$$
-/
theorem lemma_3_4_1 {K : Set H} (hK : Convex ℝ K) {u uhat : H} (hu : uhat ∈ K) :
    IsBestApprox K u uhat ↔ ∀ v ∈ K, inner ℝ (u - uhat) (v - uhat) ≤ 0 :=
  isBestApprox_iff_inner_le_zero hK hu

/-- **Corollary 3.4.2** of [han2009theoretical]. Let $H$ be a real inner product space and let
$K \subseteq H$ be convex. If $v_1$ and $v_2$ are both best approximations of $u \in H$ from
$K$, then $v_1 = v_2$. -/
theorem corollary_3_4_2 {K : Set H} (hK : Convex ℝ K) {u v₁ v₂ : H} (h₁ : IsBestApprox K u v₁)
    (h₂ : IsBestApprox K u v₂) : v₁ = v₂ :=
  h₁.unique hK h₂

/-- **Theorem 3.4.3** of [han2009theoretical] (projection onto a closed convex set). Let $H$ be a
real Hilbert space and let $K \subseteq H$ be nonempty, closed and convex. Then every $u \in H$
has exactly one best approximation $\hat u$ from $K$.

By Lemma 3.4.1 (`AtkinsonHan.Chapter03.lemma_3_4_1`), $\hat u$ is characterized by the
variational inequality (3.4.1). -/
theorem theorem_3_4_3 [CompleteSpace H] {K : Set H} (hne : K.Nonempty) (hcl : IsClosed K)
    (hK : Convex ℝ K) (u : H) : ∃! uhat, IsBestApprox K u uhat :=
  existsUnique_isBestApprox hne hcl hK u

/-- The **projection operator** $P_K : H \to H$ onto a set $K$, written after Theorem 3.4.3 of
[han2009theoretical]. $P_K u$ is a best approximation of $u$ from $K$ when one exists, and
$P_K u = u$ otherwise.

The definition is the backbone's metric projection `bestApprox K`, which is defined for every
set $K$. On a nonempty closed convex subset of a real Hilbert space, $P_K u$ is the best
approximation (`AtkinsonHan.Chapter03.isBestApprox_projConvex`). $P_K$ is not linear unless $K$
is a subspace, where it is the orthogonal projection
(`AtkinsonHan.Chapter03.projConvex_eq_starProjection`). -/
noncomputable abbrev projConvex (K : Set H) : H → H :=
  bestApprox K

/-- Let $H$ be a real Hilbert space and let $K \subseteq H$ be nonempty, closed and convex. Then
$P_K u$ is the best approximation of $u$ from $K$, for every $u \in H$. This is the backbone's
`isBestApprox_bestApprox_of_isClosed`. -/
theorem isBestApprox_projConvex [CompleteSpace H] (K : Set H) (hne : K.Nonempty)
    (hcl : IsClosed K) (hK : Convex ℝ K) (u : H) : IsBestApprox K u (projConvex K u) :=
  isBestApprox_bestApprox_of_isClosed hne hcl hK u

/-- Let $K$ be a complete subspace of a real inner product space $H$. Then $P_K u$ is the orthogonal
projection `K.starProjection u` of $u$ onto $K$, for every $u \in H$. This is the backbone's
`bestApprox_eq_starProjection`. -/
theorem projConvex_eq_starProjection (K : Submodule ℝ H) [CompleteSpace K] (u : H) :
    projConvex (K : Set H) u = K.starProjection u :=
  bestApprox_eq_starProjection K u

/-- **Proposition 3.4.4** of [han2009theoretical], for two best approximations. Let $H$ be a real
inner product space and let $K \subseteq H$ be convex. If $\hat u$ and $\hat v$ are best
approximations from $K$ of $u$ and $v$, then
$$(\hat u - \hat v, u - v) \ge 0 \quad \text{and} \quad \|\hat u - \hat v\| \le \|u - v\|.$$

**Generalization.** The book states the result for the projection $P_K$ onto a nonempty closed
convex subset of a Hilbert space, which is `AtkinsonHan.Chapter03.proposition_3_4_4'`. This form
needs no completeness and no existence of best approximations. -/
theorem proposition_3_4_4 {K : Set H} (hK : Convex ℝ K) {u v uhat vhat : H}
    (hu : IsBestApprox K u uhat) (hv : IsBestApprox K v vhat) :
    0 ≤ inner ℝ (uhat - vhat) (u - v) ∧ ‖uhat - vhat‖ ≤ ‖u - v‖ :=
  hu.dist_le_dist hK hv

/-- **Proposition 3.4.4** of [han2009theoretical]. Let $H$ be a real Hilbert space and let
$K \subseteq H$ be nonempty, closed and convex. Then for all $u, v \in H$,
$$(P_K u - P_K v, u - v) \ge 0 \quad \text{and} \quad \|P_K u - P_K v\| \le \|u - v\|.$$
So $P_K$ is monotone and non-expansive.

The proof specializes the backbone's `inner_bestApprox_sub_nonneg` and
`norm_bestApprox_sub_bestApprox_le`. -/
theorem proposition_3_4_4' [CompleteSpace H] {K : Set H} (hne : K.Nonempty) (hcl : IsClosed K)
    (hK : Convex ℝ K) (u v : H) :
    0 ≤ inner ℝ (projConvex K u - projConvex K v) (u - v) ∧
      ‖projConvex K u - projConvex K v‖ ≤ ‖u - v‖ :=
  ⟨inner_bestApprox_sub_nonneg hne hcl hK u v, norm_bestApprox_sub_bestApprox_le hne hcl hK u v⟩

/-- **Theorem 3.4.5** of [han2009theoretical]. Let $H$ be a real inner product space, let
$S \subseteq H$ be a finite-dimensional subspace, and let $K \subseteq S$ be nonempty, closed
and convex. Then every $u \in H$ has exactly one best approximation from $K$.

The space $H$ need not be complete. -/
theorem theorem_3_4_5 {K : Set H} (S : Submodule ℝ H) [FiniteDimensional ℝ S] (hKS : K ⊆ S)
    (hcl : IsClosed K) (hK : Convex ℝ K) (hne : K.Nonempty) (u : H) :
    ∃! uhat, IsBestApprox K u uhat := by
  obtain ⟨v, hv⟩ := exists_isBestApprox_of_isClosed_of_finiteDimensional hcl hne S hKS u
  exact ⟨v, hv, fun w hw => corollary_3_4_2 hK hw hv⟩

/-- **Exercise 3.4.8** of [han2009theoretical]. Let $K$ be a subspace of a real inner product space
$H$, and let $u \in H$ and $\hat u \in K$. Then the variational inequality (3.4.1) holds if and
only if the orthogonality condition (3.4.2) holds:
$$\bigl(\forall v \in K,\ (u - \hat u, v - \hat u) \le 0\bigr) \iff \bigl(\forall v \in K,\ (u -
  \hat u, v) = 0\bigr).$$

With Lemma 3.4.1, both conditions are equivalent to $\hat u$ being the best approximation of $u$
from $K$. -/
theorem exercise_3_4_8 (K : Submodule ℝ H) {u uhat : H} (hu : uhat ∈ K) :
    (∀ v ∈ K, inner ℝ (u - uhat) (v - uhat) ≤ 0) ↔ ∀ v ∈ K, inner ℝ v (u - uhat) = 0 := by
  constructor
  · intro h
    exact (Submodule.mem_orthogonal K _).1
      ((isBestApprox_iff_mem_orthogonal K hu).1 ((lemma_3_4_1 K.convex hu).2 h))
  · intro h
    exact (lemma_3_4_1 K.convex hu).1
      ((isBestApprox_iff_mem_orthogonal K hu).2 ((Submodule.mem_orthogonal K _).2 h))

end Real

/-! ### Subspaces and the orthogonal projection operator -/

section Hilbert

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- **Theorem 3.4.6** of [han2009theoretical]. Let $H$ be an inner product space over
$\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, let $K \subseteq H$ be a complete subspace, and let
$u \in H$. Then $u$ has exactly one best approximation from $K$. Moreover, an element
$\hat u \in K$ is the best approximation if and only if
$$(u - \hat u, v) = 0 \quad \text{for all } v \in K. \qquad (3.4.2)$$

**Generalization.** The book states the theorem for real spaces.

The book's $(u - \hat u, v)$ is `inner 𝕜 v (u - uhat)`. -/
theorem theorem_3_4_6 (K : Submodule 𝕜 H) [CompleteSpace K] (u : H) :
    (∃! uhat, IsBestApprox (K : Set H) u uhat) ∧
      ∀ uhat ∈ K, (IsBestApprox (K : Set H) u uhat ↔ ∀ v ∈ K, inner 𝕜 v (u - uhat) = 0) := by
  refine ⟨⟨K.starProjection u, isBestApprox_starProjection K u, fun w hw => ?_⟩,
    fun uhat huhat => ?_⟩
  · exact hw.eq_starProjection K
  · rw [isBestApprox_iff_mem_orthogonal K huhat, Submodule.mem_orthogonal]

/-- **Theorem 3.4.7** of [han2009theoretical]. Let $H$ be an inner product space over
$\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, let $K \subseteq H$ be a complete subspace, and let
$P_K$ be the orthogonal projection onto $K$. Then

* $(P_K u, v) = (u, P_K v)$ for all $u, v \in H$ (3.4.3);
* $\|v\|^2 = \|P_K v\|^2 + \|v - P_K v\|^2$ for all $v \in H$ (3.4.4);
* $\|P_K\| \le 1$, and $\|P_K\| = 1$ if $K \neq \{0\}$ (3.4.5).

**Correction.** The book states (3.4.5) as $\|P_K\| = 1$. This fails for $K = \{0\}$, where
$P_K = 0$.

**Generalization.** The book states the theorem for real spaces.

$P_K$ is `K.starProjection`. Its linearity and boundedness, which the book also proves, are part
of its type `H →L[𝕜] H`. -/
theorem theorem_3_4_7 (K : Submodule 𝕜 H) [CompleteSpace K] :
    (∀ u v : H, inner 𝕜 (K.starProjection u) v = inner 𝕜 u (K.starProjection v)) ∧
      (∀ v : H, ‖v‖ ^ 2 = ‖K.starProjection v‖ ^ 2 + ‖v - K.starProjection v‖ ^ 2) ∧
      ‖K.starProjection‖ ≤ 1 ∧ (K ≠ ⊥ → ‖K.starProjection‖ = 1) := by
  refine ⟨fun u v => K.starProjection_isSymmetric u v, fun v => ?_, K.starProjection_norm_le,
    fun hK => K.norm_starProjection hK⟩
  have hzero : inner 𝕜 (K.starProjection v) (v - K.starProjection v) = 0 :=
    (K.mem_orthogonal _).1 (K.sub_starProjection_mem_orthogonal v) _ (K.starProjection_apply_mem v)
  have hpy := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (K.starProjection v) (v - K.starProjection v) hzero
  have hsum : K.starProjection v + (v - K.starProjection v) = v := by abel
  rw [hsum] at hpy
  simp only [← pow_two] at hpy
  exact hpy

/-- **Equation (3.4.6)** of [han2009theoretical]. Let $H$ be an inner product space over
$\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, let $\{\varphi_i\}_{i \in \iota}$ be an orthonormal
family in $H$, and let $s \subseteq \iota$ be finite. Then the orthogonal projection of
$u \in H$ onto $\operatorname{span}\{\varphi_i : i \in s\}$, which is the best approximation of
$u$ from that span, is
$$\sum_{i \in s} (u, \varphi_i)\, \varphi_i.$$

**Generalization.** The book states the formula for real spaces.

The book's $(u, \varphi_i)$ is `inner 𝕜 (φ i) u`. -/
theorem equation_3_4_6 [DecidableEq H] {ι : Type*} {φ : ι → H} (hφ : Orthonormal 𝕜 φ) (s : Finset ι)
    (u : H) :
    (Submodule.span 𝕜 (s.image φ : Set H)).starProjection u = ∑ i ∈ s, inner 𝕜 (φ i) u • φ i := by
  rw [(OrthonormalBasis.span hφ s).starProjection_eq_sum_rankOne]
  simp only [FunLike.coe_sum, Finset.sum_apply, InnerProductSpace.rankOne_apply,
    OrthonormalBasis.span_apply]
  exact Finset.sum_coe_sort s fun i => inner 𝕜 (φ i) u • φ i

/-- The infinite-dimensional form of (3.4.6) in [han2009theoretical]. Let
$\{\varphi_i\}_{i \in \iota}$ be a Hilbert basis of a Hilbert space $H$ over
$\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$. Then for every $u \in H$ the family
$\{(u, \varphi_i)\, \varphi_i\}$ is summable with sum $u$:
$$u = \sum_{i \in \iota} (u, \varphi_i)\, \varphi_i.$$

The sum is an unordered sum (`HasSum`). -/
theorem hilbertBasis_expansion {ι : Type*} (b : HilbertBasis ι 𝕜 H) (u : H) :
    HasSum (fun i => inner 𝕜 (b i) u • b i) u := by
  simpa [b.repr_apply_apply] using b.hasSum_repr u

end Hilbert

/-! ### Example 3.4.8: least squares by Legendre polynomials in $L^2(-1, 1)$ -/

section Legendre

open MeasureTheory OrthogonalPolynomial Polynomial Real

/-- **Example 3.4.8** of [han2009theoretical], the normalized Legendre polynomials
$$L_n = \sqrt{\frac{2n + 1}{2}}\, P_n,$$
where $P_n$ is the Legendre polynomial of (3.5.4). By the orthogonality relation (3.5.5),
$(P_m, P_n) = 2 \delta_{mn} / (2n + 1)$, the $L_n$ have norm $1$ in $L^2(-1, 1)$. -/
noncomputable def legendreNormalized (n : ℕ) : ℝ[X] :=
  C (√((2 * (n : ℝ) + 1) / 2)) * legendre n

private theorem sqrt_coeff_pos (n : ℕ) : 0 < √((2 * (n : ℝ) + 1) / 2) :=
  Real.sqrt_pos.2 (by positivity)

/-- The normalized Legendre polynomial $L_n$ has degree $n$. -/
theorem degree_legendreNormalized (n : ℕ) : (legendreNormalized n).degree = n := by
  rw [legendreNormalized, degree_C_mul (sqrt_coeff_pos n).ne', degree_legendre]

/-- The normalized Legendre polynomials $L_n$ as elements of $L^2(-1, 1)$, for the Lebesgue measure
on $(-1, 1)$. -/
noncomputable def legendreLp (n : ℕ) : Lp ℝ 2 legendreMeasure :=
  isWeight_legendreMeasure.toLpₗ (legendreNormalized n)

/-- The normalized Legendre polynomials $L_n$ are orthonormal in $L^2(-1, 1)$. This is (3.5.5) of
[han2009theoretical] with the factor $\sqrt{(2n + 1)/2}$ put in. -/
theorem orthonormal_legendreLp : Orthonormal ℝ legendreLp := by
  have hbase : ∀ m n : ℕ, inner ℝ (legendreLp m) (legendreLp n)
      = (√((2 * (m : ℝ) + 1) / 2) * √((2 * (n : ℝ) + 1) / 2)) *
        (if m = n then 2 / (2 * (n : ℝ) + 1) else 0) := by
    intro m n
    have hval : ∀ x : ℝ, (legendreNormalized m).eval x * (legendreNormalized n).eval x
        = (√((2 * (m : ℝ) + 1) / 2) * √((2 * (n : ℝ) + 1) / 2)) *
          ((legendre m).eval x * (legendre n).eval x) := by
      intro x
      simp only [legendreNormalized, eval_mul, eval_C]
      ring
    rw [legendreLp, legendreLp, IsWeight.inner_toLpₗ]
    simp only [hval]
    rw [integral_const_mul, integral_legendreMeasure, integral_legendre_mul_legendre]
  have hinner : ∀ m n : ℕ, inner ℝ (legendreLp m) (legendreLp n)
      = if m = n then (1 : ℝ) else 0 := by
    intro m n
    rw [hbase m n]
    split_ifs with h
    · subst h
      rw [Real.mul_self_sqrt (by positivity : (0 : ℝ) ≤ (2 * (m : ℝ) + 1) / 2)]
      have h2 : (2 * (m : ℝ) + 1) ≠ 0 := by positivity
      field_simp
    · rw [mul_zero]
  constructor
  · intro n
    have h : ‖legendreLp n‖ ^ 2 = 1 := by
      rw [← real_inner_self_eq_norm_sq, hinner n n]
      simp
    nlinarith [norm_nonneg (legendreLp n)]
  · intro m n hmn
    rw [hinner m n]
    simp [hmn]

/-- **Example 3.4.8** of [han2009theoretical], completeness. The normalized Legendre polynomials
$L_0, L_1, \ldots$ form a Hilbert basis of $L^2(-1, 1)$.

Orthonormality is (3.5.5). Completeness is the density of the polynomials in $L^2(-1, 1)$, which
follows from the Weierstrass theorem and the density of the continuous functions in $L^2$. The
definition is the backbone's `OrthogonalPolynomial.hilbertBasisOfDegreeEq`. -/
noncomputable def legendreHilbertBasis : HilbertBasis ℕ ℝ (Lp ℝ 2 legendreMeasure) :=
  hilbertBasisOfDegreeEq isWeight_legendreMeasure legendreMeasure_compl_Icc
    degree_legendreNormalized orthonormal_legendreLp

/-- The members of the Legendre Hilbert basis `AtkinsonHan.Chapter03.legendreHilbertBasis` are the
normalized Legendre polynomials $L_n$. -/
@[simp]
theorem coe_legendreHilbertBasis : ⇑legendreHilbertBasis = legendreLp :=
  coe_hilbertBasisOfDegreeEq _ _ _ _

/-- **Example 3.4.8** of [han2009theoretical]. Let $L_n$ be the normalized Legendre polynomials, let
$u \in L^2(-1, 1)$, and let
$$P_N u = \sum_{k=0}^{N} (u, L_k)\, L_k.$$
Then

* the $L_n$ are orthonormal in $L^2(-1, 1)$;
* $P_N u$ is a best approximation of $u$ from the polynomials of degree at most $N$, by (3.4.6);
* $u = \sum_{n \ge 0} (u, L_n) L_n$ in $L^2(-1, 1)$, as an unordered sum;
* $\|u - P_N u\| \to 0$ as $N \to \infty$;
* Parseval's equality $\|u\|^2 = \sum_{n \ge 0} (u, L_n)^2$ holds.

The last three parts say that the $L_n$ are complete, and this is where the Weierstrass theorem
enters. The space of polynomials of degree at most $N$ is the image of `Polynomial.degreeLE ℝ N`
in $L^2(-1, 1)$. -/
theorem example_3_4_8 (N : ℕ) (u : Lp ℝ 2 legendreMeasure) :
    Orthonormal ℝ legendreLp ∧
      IsBestApprox
        ((Polynomial.degreeLE ℝ N).map isWeight_legendreMeasure.toLpₗ :
          Set (Lp ℝ 2 legendreMeasure))
        u (∑ k ∈ Finset.range (N + 1), inner ℝ (legendreLp k) u • legendreLp k) ∧
      HasSum (fun n => inner ℝ (legendreLp n) u • legendreLp n) u ∧
      Tendsto
        (fun N => ‖u - ∑ k ∈ Finset.range (N + 1), inner ℝ (legendreLp k) u • legendreLp k‖)
        atTop (𝓝 0) ∧
      HasSum (fun n => inner ℝ (legendreLp n) u ^ 2) (‖u‖ ^ 2) := by
  have hsum : HasSum (fun n => inner ℝ (legendreLp n) u • legendreLp n) u := by
    simpa only [coe_legendreHilbertBasis, HilbertBasis.repr_apply_apply] using
      legendreHilbertBasis.hasSum_repr u
  have htend : Tendsto
      (fun N => ∑ k ∈ Finset.range (N + 1), inner ℝ (legendreLp k) u • legendreLp k) atTop (𝓝 u) :=
    hsum.tendsto_sum_nat.comp (Filter.tendsto_add_atTop_nat 1)
  refine ⟨orthonormal_legendreLp, ?_, hsum, ?_, ?_⟩
  · have h := isBestApprox_truncation_of_degree_eq isWeight_legendreMeasure
      degree_legendreNormalized orthonormal_legendreLp N u
    rw [Fin.sum_univ_eq_sum_range fun k =>
      inner ℝ (isWeight_legendreMeasure.toLpₗ (legendreNormalized k)) u •
        isWeight_legendreMeasure.toLpₗ (legendreNormalized k)] at h
    exact h
  · simpa only [norm_sub_rev] using tendsto_iff_norm_sub_tendsto_zero.1 htend
  · have h := legendreHilbertBasis.hasSum_inner_mul_inner u u
    rw [real_inner_self_eq_norm_sq] at h
    refine h.congr_fun fun n => ?_
    rw [coe_legendreHilbertBasis, real_inner_comm, sq]

end Legendre

/-! ### Example 3.4.9: least squares by trigonometric polynomials in $L^2(0, 2\pi)$ -/

section Fourier

open MeasureTheory Real

/-- The space $\mathcal{T}_n$ of [han2009theoretical], inside $L^2(0, 2\pi)$: the image of the
trigonometric polynomials of degree at most $n$ under the inclusion of
$C(\mathbb{R}/2\pi\mathbb{Z})$ into $L^2$.

The trigonometric polynomials are `trigPolyLE (2 * π) n`, and $L^2$ is taken for the probability
Haar measure of the circle. -/
noncomputable def trigPolyLpLE (n : ℕ) :
    Submodule ℝ (Lp ℝ 2 (AddCircle.haarAddCircle : Measure (AddCircle (2 * π)))) :=
  (trigPolyLE (2 * π) n).map
    (ContinuousMap.toLp (E := ℝ) 2 AddCircle.haarAddCircle ℝ).toLinearMap

/-- The space $\mathcal{T}_n$ inside $L^2(0, 2\pi)$ is spanned by the members $\varphi_m$,
$|m| \le n$, of the real trigonometric system. -/
theorem trigPolyLpLE_eq_span (n : ℕ) :
    trigPolyLpLE n = Submodule.span ℝ (trigLp (2 * π) '' Set.Icc (-(n : ℤ)) n) := by
  rw [trigPolyLpLE, trigPolyLE, Submodule.map_span, ← Set.image_comp]
  rfl

/-- **Example 3.4.9** of [han2009theoretical]. Let $f \in L^2(0, 2\pi)$, let
$\{\varphi_m\}_{m \in \mathbb{Z}}$ be the real trigonometric system, let $c_m(f)$ be the
integral of $\varphi_m f$ over the circle, and let $S_n f = \sum_{|m| \le n} c_m(f)\, \varphi_m$
be the $n$-th partial sum of the Fourier series of $f$. Then

* $S_n f$ is a best approximation of $f$ from $\mathcal{T}_n$ in $L^2$;
* $S_n f = \sum_{|m| \le n} (f, \varphi_m)\, \varphi_m$, with the inner product of $L^2$;
* the Fourier series converges to $f$ in $L^2$:
  $f = \sum_{m \in \mathbb{Z}} c_m(f)\, \varphi_m$, as an unordered sum. This is the expansion
  (3.4.10).

The measure is `AddCircle.haarAddCircle`, the probability Haar measure of the circle. So the
inner product is $(2\pi)^{-1} \int_{-\pi}^{\pi}$, and $\varphi_m$ is `trigFun (2 * π) m`, which
is $\sqrt{2\pi}$ times the book's orthonormal system $1/\sqrt{2\pi}$, $\cos(jx)/\sqrt{\pi}$,
$\sin(jx)/\sqrt{\pi}$ of Theorem 1.3.13. The two factors cancel in $(f, \varphi_m)\, \varphi_m$,
so the three parts are the book's statements. Only the value of the norm differs, by the factor
$\sqrt{2\pi}$. In contrast, `AtkinsonHan.Chapter03.equation_3_7_5` uses the unnormalized measure
of the circle, because there the constant $\sqrt{2\pi}$ is the statement.

$S_n f$ is `trigPartialSum n f`, and $c_m(f)$ is `realFourierCoeff f m`. The book writes the
partial sum with the classical coefficients as $a_0/2 + \sum_{j=1}^{n} (a_j \cos(jx) + b_j
\sin(jx))$, where $a_j$ and $b_j$ are the integrals (3.4.9), which are (4.1.2) in Chapter 4. The
relation between these coefficients and $(f, \varphi_m)$ is
`AtkinsonHan.Chapter04.equation_4_1_3_const`, `AtkinsonHan.Chapter04.equation_4_1_3_cos` and
`AtkinsonHan.Chapter04.equation_4_1_3_sin`, which give the factors $2$ and $\sqrt 2$. -/
theorem example_3_4_9 (n : ℕ)
    (f : Lp ℝ 2 (AddCircle.haarAddCircle : Measure (AddCircle (2 * π)))) :
    IsBestApprox (trigPolyLpLE n : Set (Lp ℝ 2 AddCircle.haarAddCircle)) f
        (trigPartialSum n f) ∧
      trigPartialSum n f
        = ∑ m ∈ Finset.Icc (-(n : ℤ)) n, inner ℝ (trigLp (2 * π) m) f • trigLp (2 * π) m ∧
      HasSum
        (fun m : ℤ => realFourierCoeff (f : AddCircle (2 * π) → ℝ) m • trigLp (2 * π) m) f := by
  classical
  have hcoeff : trigPartialSum n f
      = ∑ m ∈ Finset.Icc (-(n : ℤ)) n, inner ℝ (trigLp (2 * π) m) f • trigLp (2 * π) m :=
    Finset.sum_congr rfl fun m _ => by rw [inner_trigLp]
  refine ⟨?_, hcoeff, hasSum_trigSeries f⟩
  have hspan : (((Finset.Icc (-(n : ℤ)) n).image (trigLp (2 * π)) : Finset _) :
      Set (Lp ℝ 2 (AddCircle.haarAddCircle : Measure (AddCircle (2 * π)))))
      = trigLp (2 * π) '' Set.Icc (-(n : ℤ)) n := by
    rw [Finset.coe_image, Finset.coe_Icc]
  have hproj := isBestApprox_starProjection
    (Submodule.span ℝ (((Finset.Icc (-(n : ℤ)) n).image (trigLp (2 * π)) : Finset _) :
      Set (Lp ℝ 2 (AddCircle.haarAddCircle : Measure (AddCircle (2 * π)))))) f
  rw [equation_3_4_6 orthonormal_trigFun _ f, hspan] at hproj
  rw [trigPolyLpLE_eq_span, hcoeff]
  exact hproj

end Fourier

end AtkinsonHan.Chapter03
