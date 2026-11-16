/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Distribution.Sobolev`, beside the material of
`Numlib/Analysis/Sobolev/Compactness.lean`; the polynomial lemmas belong in
`Mathlib.Algebra.MvPolynomial.PDeriv` and `Mathlib.Analysis.Calculus.FDeriv`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.RingTheory.MvPolynomial.Basic
import Numlib.Analysis.Sobolev.Compactness
import Numlib.Analysis.Sobolev.Friedrichs
import Numlib.Approximation.MvPolynomial

/-!
# The Deny–Lions norm equivalences

Let $\Omega$ be an open set in a real normed space $E$ with a basis $b = (b_i)_{i \in \iota}$, and
let $W^{k,p}(\Omega)$ be the Sobolev space with the norm $\|u\|_{k,p,\Omega} = \bigl(\sum_{|\alpha|
\le k} \|\partial^\alpha u\|_{L^p(\Omega)}^p\bigr)^{1/p}$. The **top-order seminorm** is
$|u|_{k,p,\Omega} = \bigl(\sum_{|\alpha| = k} \|\partial^\alpha u\|_{L^p(\Omega)}^p\bigr)^{1/p}$.
This file proves the norm equivalences of §7.3.5 of [han2009theoretical] (Theorems 7.3.12, 7.3.13
and 7.3.14): on a suitable domain $\Omega \subseteq \mathbb{R}^N$, with $k \ge 1$ and
$1 \le p < \infty$, let $f_1, \dots, f_J$ be seminorms on $W^{k,p}(\Omega)$ with (H1)
$f_j(v) \le c \|v\|_{k,p,\Omega}$, and (H2) if $v$ is a polynomial of degree $< k$ and $f_j(v) = 0$
for all $j$, then $v = 0$. Then the two quantities
$$|v|_{k,p,\Omega} + \sum_j f_j(v) \quad (7.3.3) \qquad \text{and} \qquad
  \Bigl(|v|_{k,p,\Omega}^p + \sum_j f_j(v)^p\Bigr)^{1/p} \quad (7.3.4)$$
are norms on $W^{k,p}(\Omega)$ equivalent to $\|v\|_{k,p,\Omega}$. The consequences are the
Poincaré–Friedrichs inequalities and the Bramble–Hilbert lemma.

The polynomial step is the classical fact that a function on a connected open set whose weak
derivatives of order $k$ all vanish is a polynomial of degree $< k$. The file also proves Theorem
7.3.17 of [han2009theoretical]: on a connected bounded domain, the quotient norm of
$W^{k+1,p}(\Omega)/\mathbb{P}_k(\Omega)$ is equivalent to $|v|_{k+1,p,\Omega}$, where
$\mathbb{P}_k(\Omega)$ is the space of polynomials of degree at most $k$. For a polynomial $q$ in
the coordinates of $b$, $q \circ b^{-1}$ denotes the polynomial function
$x \mapsto q(x_1, \dots, x_n)$ on $E$, where $b^{-1} : E \to \mathbb{R}^\iota$ is the coordinate map
of $b$.

## Main definitions

* `SobolevMultiIndex.topDeriv`: the tuple $(\partial^\alpha u)_{|\alpha| = k}$ of the weak
  derivatives of top order of $u \in W^{k,p}(\Omega)$.
* `SobolevMultiIndex.topSeminorm`: the top-order seminorm $|u|_{k,p,\Omega}$, the $\ell^p$ norm of
  this tuple.
* `MvPolynomial.gradientAntideriv`: a polynomial $Q$ with $\partial_i Q = q_i$ for a compatible
  family $(q_i)$.
* `MvPolynomial.evalBasis`: the polynomial function $x \mapsto q(x_1, \dots, x_n)$ on $E$, in the
  coordinates of the basis $b$.
* `absIntegralSeminorm`: the seminorm $v \mapsto \int_s |Lv| \, d\sigma$ of a bounded linear map $L$
  into the $L^q$ space of a finite measure, such as the boundary seminorm
  $\int_\Gamma |\gamma v| \, ds$.
* `SobolevEuclidean.polynomialSubmodule`: the finite-dimensional subspace $\mathbb{P}_k(\Omega)$ of
  $W^{k+1,p}(\Omega)$ for a bounded $\Omega \subseteq \mathbb{R}^N$.

## Main results

* `SobolevMultiIndex.norm_rpow_eq_norm_toLowerOrder_rpow_add`: for $p < \infty$,
  $\|u\|_{k+1,p,\Omega}^p = \|u\|_{k,p,\Omega}^p + |u|_{k+1,p,\Omega}^p$.
* `MvPolynomial.pderiv_gradientAntideriv`: the **Poincaré lemma for polynomials**: a family of
  polynomials $(q_i)$ with $\partial_j q_i = \partial_i q_j$ is the gradient of a polynomial.
* `SobolevMultiIndex.exists_mvPolynomial_ae_eq_of_forall_weakDeriv_eq_zero`: on a connected open
  set, $|u|_{k,p,\Omega} = 0$ implies that $u$ is almost everywhere a polynomial of degree $< k$.
* `SobolevMultiIndex.exists_norm_le_topSeminorm_add_sum_of_isCompactEmbedding`: the **abstract
  Deny–Lions theorem**: if $W^{k+1,p}(\Omega)$ embeds compactly in $W^{k,p}(\Omega)$ and
  $|v|_{k+1,p,\Omega} = 0$ and $f_j(v) = 0$ for all $j$ force $v = 0$, then $\|v\|_{k+1,p,\Omega}
  \le C (|v|_{k+1,p,\Omega} + \sum_j f_j(v))$.
* `SobolevEuclidean.exists_norm_le_topSeminorm_add_sum_of_forall_eq_zero`: Theorem 7.3.13 of
  [han2009theoretical] for the norm (7.3.3).
* `SobolevEuclidean.exists_norm_le_topSeminorm_add_sum_of_isPreconnected`: Theorem 7.3.12 of
  [han2009theoretical] for the norm (7.3.3).
* `SobolevEuclidean.exists_norm_le_topSeminorm_add_sum_of_iSup`: Theorem 7.3.14 of
  [han2009theoretical] for the norm (7.3.3).
* `SobolevEuclidean.exists_norm_le_lp_topSeminorm_sum_of_forall_eq_zero`: Theorem 7.3.13 of
  [han2009theoretical] for the norm (7.3.4).
* `SobolevEuclidean.exists_norm_le_topSeminorm_add_sum_abs_of_isPreconnected` and
  `SobolevEuclidean.exists_norm_le_topSeminorm_add_abs_of_isPreconnected`: Theorem 7.3.12 with the
  seminorms $|\ell_j(v)|$ of bounded linear functionals.
* `SobolevMultiIndex.topSeminorm_add_sum_le_norm`: the reverse inequality $|v|_{k,p,\Omega} + \sum_j
  f_j(v) \le (1 + Jc) \|v\|_{k,p,\Omega}$.
* `SobolevMultiIndex.norm_equiv_of_exists_norm_le_topSeminorm_add_sum`: the inequality of the
  theorems makes both (7.3.3) and (7.3.4) norms equivalent to $\|\cdot\|_{k,p,\Omega}$.
* `Seminorm.le_ciInf_norm_add_smul` and `Seminorm.ciInf_norm_add_smul_le_mul`: the quotient norm
  $\inf_\alpha \|v + \alpha w\|$ is equivalent to a seminorm $N$ with $N(w) = 0$, as in Lemma 8.4.1
  of [han2009theoretical].
* `SobolevEuclidean.topSeminorm_eq_zero_iff_mem_polynomialSubmodule`: on a connected bounded open
  set, $|v|_{k+1,p,\Omega} = 0$ if and only if $v \in \mathbb{P}_k(\Omega)$.
* `SobolevEuclidean.exists_ciInf_norm_add_le_mul_topSeminorm`: Theorem 7.3.17 of
  [han2009theoretical], $\inf_{q \in \mathbb{P}_k(\Omega)} \|v + q\|_{k+1,p,\Omega} \le C
  |v|_{k+1,p,\Omega}$.
* `SobolevMultiIndex.topSeminorm_one_eq_gradNorm`: at order one the top-order seminorm is the
  gradient norm $\|\nabla u\|_{L^p(\Omega)}$.

## Proof outline

The abstract theorem is the compactness argument of [han2009theoretical]. If the inequality fails,
there is a sequence with $\|v_n\| = 1$ and $|v_n| + \sum_j f_j(v_n) \le 1/n$. A subsequence
converges in $W^{k,p}(\Omega)$ by the compact embedding. Since the top-order seminorms tend to zero,
the subsequence is a Cauchy sequence in $W^{k+1,p}(\Omega)$, and its limit $v$ has $\|v\| = 1$,
$|v| = 0$ and $f_j(v) = 0$, which contradicts (H2)′.

The polynomial step is an induction on $k$. The partial derivatives $\partial_i u$ are polynomials
$q_i$ by the induction hypothesis. They satisfy $\partial_j q_i = \partial_i q_j$, so they are the
gradient of a polynomial $Q$. Then $u - Q$ has weak gradient zero, and it is constant on the
connected set $\Omega$.

## Implementation notes

* The Euclidean theorems write the order as $k + 1$ with $k \ge 0$. The order $k \ge 1$ of
  [han2009theoretical] is $k + 1$ here, and the book's $\mathbb{P}_{k-1}$ is
  `MvPolynomial.restrictTotalDegree (Fin N) ℝ k`.
* The book states the theorems on a bounded Lipschitz domain. Here the domain is a
  $W^{1,p}$-extension domain (`IsSobolevExtensionDomain`) of finite measure, which is the hypothesis
  that the compact embedding needs.
* The exponent of the Euclidean theorems is `p : ℝ≥0` with `1 ≤ (p : ℝ≥0∞)`, so $1 \le p < \infty$
  holds by the type.
* At $p = \infty$ the top-order seminorm is $\max_{|\alpha| = k} \|\partial^\alpha
  u\|_{L^\infty(\Omega)}$.
* `SobolevMultiIndex.topSeminorm_one_eq_gradNorm` connects the Poincaré inequality of
  `Numlib.Analysis.Sobolev.Poincare` with the top-order seminorm.
-/

open Filter MeasureTheory Metric Module Set TopologicalSpace
open scoped ContDiff Distributions ENNReal NNReal Topology

noncomputable section

/-! ### The top-order seminorm $|u|_{k,p,\Omega}$ -/

section TopSeminorm

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ι : Type*} [Fintype ι] [LinearOrder ι] {b : Basis ι ℝ E} {k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {Ω : Opens E} {μ : Measure E}

namespace SobolevMultiIndex

/-- The **top-order derivatives** of $u \in W^{k,p}(\Omega)$: the tuple
$(\partial^\alpha u)_{|\alpha| = k}$ of the weak derivatives of order exactly $k$, as an element
of the $\ell^p$ product of copies of $L^p(\Omega)$ indexed by the multi-indices of order $k$.

The index type is `MultiIndexEq ι k`, and the product is `PiLp p`. -/
def topDeriv (u : SobolevMultiIndex F b k p Ω μ) :
    PiLp p fun _ : MultiIndexEq ι k ↦ Lp F p (μ.restrict (Ω : Set E)) :=
  WithLp.toLp p fun α ↦ weakDeriv u α.1

omit [Fact (1 ≤ p)] in
/-- The entry at $\alpha$ of the top-order tuple of $u$ is $\partial^\alpha u$. -/
@[simp]
theorem topDeriv_apply (u : SobolevMultiIndex F b k p Ω μ) (α : MultiIndexEq ι k) :
    topDeriv u α = weakDeriv u α.1 :=
  rfl

omit [Fact (1 ≤ p)] in
/-- The top-order tuple is additive: the tuple of $u + v$ is the sum of the tuples of $u$ and $v$.
-/
theorem topDeriv_add (u v : SobolevMultiIndex F b k p Ω μ) :
    topDeriv (u + v) = topDeriv u + topDeriv v :=
  rfl

omit [Fact (1 ≤ p)] in
/-- The top-order tuple commutes with scalar multiplication: the tuple of $cu$ is $c$ times the
tuple of $u$. -/
theorem topDeriv_smul (c : ℝ) (u : SobolevMultiIndex F b k p Ω μ) :
    topDeriv (c • u) = c • topDeriv u :=
  rfl

variable (F b k p Ω μ) in
/-- The top-order tuple $u \mapsto (\partial^\alpha u)_{|\alpha| = k}$ as a linear map from
$W^{k,p}(\Omega)$ to the $\ell^p$ product of copies of $L^p(\Omega)$. -/
def topDerivₗ : SobolevMultiIndex F b k p Ω μ →ₗ[ℝ]
    PiLp p fun _ : MultiIndexEq ι k ↦ Lp F p (μ.restrict (Ω : Set E)) where
  toFun := topDeriv
  map_add' := topDeriv_add
  map_smul' := topDeriv_smul

variable (F b k p Ω μ) in
/-- The **top-order seminorm** on $W^{k,p}(\Omega)$ of §7.3.5 of [han2009theoretical]: for
$p < \infty$,
$$|u|_{k,p,\Omega}
  = \Bigl(\sum_{|\alpha| = k} \|\partial^\alpha u\|_{L^p(\Omega)}^p\Bigr)^{1/p},$$
and at $p = \infty$, $|u|_{k,\infty,\Omega} = \max_{|\alpha| = k} \|\partial^\alpha
u\|_{L^\infty(\Omega)}$.

The seminorm is the norm of the tuple `SobolevMultiIndex.topDeriv u` in the $\ell^p$ product,
bundled as a `Seminorm`. The formula for finite $p$ is `SobolevMultiIndex.topSeminorm_eq_sum`.
The seminorm is bounded by the norm (`SobolevMultiIndex.topSeminorm_le_norm`), and at $k = 1$ it
is the gradient norm `SobolevMultiIndex.gradNorm`
(`SobolevMultiIndex.topSeminorm_one_eq_gradNorm`). -/
def topSeminorm : Seminorm ℝ (SobolevMultiIndex F b k p Ω μ) :=
  (normSeminorm ℝ (PiLp p fun _ : MultiIndexEq ι k ↦ Lp F p (μ.restrict (Ω : Set E)))).comp
    (topDerivₗ F b k p Ω μ)

/-- The top-order seminorm of $u$ is the norm of the top-order tuple of $u$. -/
theorem topSeminorm_apply (u : SobolevMultiIndex F b k p Ω μ) :
    topSeminorm F b k p Ω μ u = ‖topDeriv u‖ :=
  rfl

/-- For $p < \infty$ and $u \in W^{k,p}(\Omega)$, the top-order seminorm is
$$|u|_{k,p,\Omega}
  = \Bigl(\sum_{|\alpha| = k} \|\partial^\alpha u\|_{L^p(\Omega)}^p\Bigr)^{1/p}.$$ -/
theorem topSeminorm_eq_sum (hp : p ≠ ⊤) (u : SobolevMultiIndex F b k p Ω μ) :
    topSeminorm F b k p Ω μ u
      = (∑ α : MultiIndexEq ι k, ‖weakDeriv u α.1‖ ^ p.toReal) ^ (1 / p.toReal) := by
  rw [topSeminorm_apply, topDeriv, PiLp.norm_eq_sum
    (ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne' hp)]

/-- For $u \in W^{k,p}(\Omega)$, $|u|_{k,p,\Omega} = 0$ if and only if $\partial^\alpha u = 0$ for
every multi-index $\alpha$ with $|\alpha| = k$. -/
theorem topSeminorm_eq_zero_iff (u : SobolevMultiIndex F b k p Ω μ) :
    topSeminorm F b k p Ω μ u = 0 ↔ ∀ α : MultiIndexEq ι k, weakDeriv u α.1 = 0 := by
  rw [topSeminorm_apply, norm_eq_zero, topDeriv, WithLp.ext_iff, WithLp.ofLp_toLp,
    WithLp.ofLp_zero, funext_iff]
  rfl

/-- For $u \in W^{k,p}(\Omega)$, the top-order seminorm is bounded by the norm:
$$|u|_{k,p,\Omega} \le \|u\|_{k,p,\Omega}.$$

The reason is that the multi-indices of order exactly $k$ are among those of order at most $k$. -/
theorem topSeminorm_le_norm (u : SobolevMultiIndex F b k p Ω μ) :
    topSeminorm F b k p Ω μ u ≤ ‖u‖ := by
  classical
  rw [topSeminorm_apply, topDeriv, ← Submodule.norm_coe]
  rcases eq_or_ne p ⊤ with rfl | hp
  · rw [PiLp.norm_eq_ciSup, PiLp.norm_eq_ciSup]
    refine Real.iSup_le (fun α ↦ ?_) (Real.iSup_nonneg fun _ ↦ norm_nonneg _)
    exact le_ciSup (Finite.bddAbove_range fun β : MultiIndexLE ι k ↦
      ‖(u : SobolevMultiIndexTuple F ι k ⊤ Ω μ) β‖) α.1
  · have hP : 0 < p.toReal :=
      ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne' hp
    rw [PiLp.norm_eq_sum hP, PiLp.norm_eq_sum hP]
    refine Real.rpow_le_rpow (Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _)
      ?_ (by positivity)
    calc ∑ α : MultiIndexEq ι k, ‖(u : SobolevMultiIndexTuple F ι k p Ω μ) α.1‖ ^ p.toReal
        = ∑ β ∈ Finset.univ.image (fun α : MultiIndexEq ι k ↦ α.1),
            ‖(u : SobolevMultiIndexTuple F ι k p Ω μ) β‖ ^ p.toReal := by
          rw [Finset.sum_image Subtype.val_injective.injOn]
      _ ≤ ∑ β : MultiIndexLE ι k, ‖(u : SobolevMultiIndexTuple F ι k p Ω μ) β‖ ^ p.toReal :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            fun _ _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _

/-- The top-order seminorm is $1$-Lipschitz: $\bigl| |u|_{k,p,\Omega} - |v|_{k,p,\Omega} \bigr| \le
\|u - v\|_{k,p,\Omega}$. -/
theorem abs_topSeminorm_sub_le (u v : SobolevMultiIndex F b k p Ω μ) :
    |topSeminorm F b k p Ω μ u - topSeminorm F b k p Ω μ v| ≤ ‖u - v‖ :=
  (abs_sub_map_le_sub _ u v).trans (topSeminorm_le_norm _)

/-- The top-order seminorm $u \mapsto |u|_{k,p,\Omega}$ is continuous on $W^{k,p}(\Omega)$. -/
theorem continuous_topSeminorm : Continuous (topSeminorm F b k p Ω μ) :=
  Seminorm.continuous_of_le (q := normSeminorm ℝ (SobolevMultiIndex F b k p Ω μ)) continuous_norm
    (Seminorm.le_def.2 fun u ↦ by simpa using topSeminorm_le_norm u)

omit [LinearOrder ι] in
/-- Let $M$ be an additive commutative monoid and let $f$ be a function on the multi-indices of
order at most $k + 1$ with values in $M$. Then the sum of $f$ splits into the sum over the
multi-indices of order at most $k$ and the sum over those of order exactly $k + 1$:
$$\sum_{|\alpha| \le k + 1} f(\alpha)
  = \sum_{|\alpha| \le k} f(\alpha) + \sum_{|\alpha| = k + 1} f(\alpha).$$ -/
theorem _root_.MultiIndexLE.sum_univ_succ {M : Type*} [AddCommMonoid M]
    (f : MultiIndexLE ι (k + 1) → M) :
    ∑ α, f α = ∑ α : MultiIndexLE ι k, f ⟨α.1, α.2.trans (Nat.le_succ k)⟩
      + ∑ α : MultiIndexEq ι (k + 1), f α.1 := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun α : MultiIndexLE ι (k + 1) ↦ ∑ i, α.1 i = k + 1) f, add_comm]
  congr 1
  · have himage : Finset.univ.image
        (fun α : MultiIndexLE ι k ↦ (⟨α.1, α.2.trans (Nat.le_succ k)⟩ : MultiIndexLE ι (k + 1)))
        = Finset.univ.filter fun α : MultiIndexLE ι (k + 1) ↦ ¬ ∑ i, α.1 i = k + 1 := by
      ext α
      simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
      constructor
      · rintro ⟨β, rfl⟩
        intro h
        change ∑ i, β.1 i = k + 1 at h
        omega
      · intro h
        exact ⟨⟨α.1, by omega⟩, rfl⟩
    rw [← himage, Finset.sum_image (MultiIndexLE.castLE_injective (Nat.le_succ k)).injOn]
  · exact Finset.sum_subtype (p := fun α : MultiIndexLE ι (k + 1) ↦ ∑ i, α.1 i = k + 1) _
      (fun _ ↦ by simp) f

/-- Let $p < \infty$ and $u \in W^{k+1,p}(\Omega)$. Then the norm splits into a lower-order part and
the top-order seminorm:
$$\|u\|_{k+1,p,\Omega}^p = \|u\|_{k,p,\Omega}^p + |u|_{k+1,p,\Omega}^p.$$

The lower-order part is the norm of `SobolevMultiIndex.toLowerOrder F b p Ω μ (Nat.le_succ k)
u`, which is $u$ read as an element of $W^{k,p}(\Omega)$. -/
theorem norm_rpow_eq_norm_toLowerOrder_rpow_add (hp : p ≠ ⊤)
    (u : SobolevMultiIndex F b (k + 1) p Ω μ) :
    ‖u‖ ^ p.toReal = ‖toLowerOrder F b p Ω μ (Nat.le_succ k) u‖ ^ p.toReal
      + topSeminorm F b (k + 1) p Ω μ u ^ p.toReal := by
  have hP : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne' hp
  have key : ∀ {n : ℕ} (v : SobolevMultiIndex F b n p Ω μ),
      ‖v‖ ^ p.toReal = ∑ α : MultiIndexLE ι n, ‖weakDeriv v α‖ ^ p.toReal := fun v ↦ by
    rw [norm_eq_sum hp, ← Real.rpow_mul
      (Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _), one_div_mul_cancel hP.ne',
      Real.rpow_one]
  rw [key, key, topSeminorm_eq_sum hp, ← Real.rpow_mul
    (Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _), one_div_mul_cancel hP.ne',
    Real.rpow_one, MultiIndexLE.sum_univ_succ]
  rfl

end SobolevMultiIndex

end TopSeminorm

/-! ### Polynomial functions: derivatives, and the Poincaré lemma for polynomials -/

section Polynomial

namespace MvPolynomial

variable {ι : Type*} [Fintype ι]

/-- Let $c, v \in \mathbb{R}^\iota$. The continuous linear map $\sum_i c_i \pi_i$, where $\pi_i$ is
the projection on the coordinate $i$, takes the value $\sum_i c_i v_i$ at $v$. -/
theorem _root_.ContinuousLinearMap.sum_smul_proj_apply (c : ι → ℝ) (v : ι → ℝ) :
    (∑ i, c i • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i) v = ∑ i, c i * v i := by
  simp

/-- For a polynomial $q$ in the variables $(x_i)_{i \in \iota}$, the polynomial function
$x \mapsto q(x)$ on $\mathbb{R}^\iota$ is smooth. -/
theorem contDiff_eval (q : MvPolynomial ι ℝ) : ContDiff ℝ ∞ (fun x : ι → ℝ ↦ eval x q) := by
  induction q using MvPolynomial.induction_on with
  | C a => simpa using contDiff_const (c := a)
  | add p q hp hq => simpa [map_add] using hp.add hq
  | mul_X p i hp => simpa [map_mul, eval_X] using hp.mul (contDiff_apply ℝ (fun _ => ℝ) i)

/-- Let $q$ be a polynomial in the variables $(x_i)_{i \in \iota}$ and $x \in \mathbb{R}^\iota$. The
function $y \mapsto q(y)$ has at $x$ the derivative
$$Dq(x) = \sum_i (\partial_i q)(x) \, \pi_i,$$
where $\pi_i$ is the projection on the coordinate $i$. So the derivative in the direction $e_i$
is $(\partial_i q)(x)$. -/
theorem hasFDerivAt_eval (q : MvPolynomial ι ℝ) (x : ι → ℝ) :
    HasFDerivAt (fun y : ι → ℝ ↦ eval y q)
      (∑ i, eval x (pderiv i q) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i) x := by
  classical
  induction q using MvPolynomial.induction_on with
  | C a => simpa [pderiv_C] using hasFDerivAt_const (eval x (C a)) x
  | add p q hp hq =>
    have h := hp.add hq
    simp only [map_add, add_smul, Finset.sum_add_distrib]
    exact h
  | mul_X p i hp =>
    have hX : HasFDerivAt (fun y : ι → ℝ ↦ y i)
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i) x := hasFDerivAt_apply i x
    have h := hp.mul hX
    have hsum : ∀ j, eval x (pderiv j (p * X i))
        = eval x (pderiv j p) * x i + if j = i then eval x p else 0 := by
      intro j
      rw [pderiv_mul, map_add, map_mul, map_mul, eval_X]
      split_ifs with hji
      · subst hji
        rw [pderiv_X_self, map_one, mul_one]
      · rw [pderiv_X_of_ne (Ne.symm hji), map_zero, mul_zero]
    convert h using 1
    · funext y
      simp [map_mul, eval_X]
    · ext v
      rw [ContinuousLinearMap.sum_smul_proj_apply, add_apply, smul_apply, smul_apply,
        ContinuousLinearMap.sum_smul_proj_apply, ContinuousLinearMap.proj_apply]
      simp only [hsum, smul_eq_mul, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.mul_sum]
      rw [add_comm]
      congr 1
      exact Finset.sum_congr rfl fun j _ ↦ by ring

omit [Fintype ι] in
/-- Let $q$ be a polynomial in the variables $(x_i)_{i \in \iota}$, with $\iota$ finite. The
derivative of $y \mapsto q(y)$ at $x$ in the direction of the unit vector $e_i$ is
$(\partial_i q)(x)$. -/
theorem fderiv_eval_single [Finite ι] [DecidableEq ι] (q : MvPolynomial ι ℝ) (x : ι → ℝ)
    (i : ι) :
    fderiv ℝ (fun y : ι → ℝ ↦ eval y q) x (Pi.single i 1) = eval x (pderiv i q) := by
  have := Fintype.ofFinite ι
  rw [(hasFDerivAt_eval q x).fderiv, ContinuousLinearMap.sum_smul_proj_apply]
  simp [Pi.single_apply]

end MvPolynomial

end Polynomial

section Poincare

namespace MvPolynomial

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The coefficient at the monomial $x^n$ of the polynomial antiderivative of a family
$(q_j)_{j \in \iota}$ of polynomials:
$$\frac{\sum_j \operatorname{coeff}_{n - e_j}(q_j) \, n_j}{\sum_j n_j^2}.$$

If the family is compatible, every $j$ with $n_j \ge 1$ gives the same quotient
$\operatorname{coeff}_{n - e_j}(q_j) / n_j$, and this symmetric average avoids the choice of one
$j$. At $n = 0$ the denominator is zero and the value is $0$. The subtraction $n - e_j$ is
truncated, but a term with $n_j = 0$ has the factor $n_j = 0$. -/
def gradientCoeff (q : ι → MvPolynomial ι ℝ) (n : ι →₀ ℕ) : ℝ :=
  (∑ j, (q j).coeff (n - Finsupp.single j 1) * (n j : ℝ)) / ∑ j, (n j : ℝ) ^ 2

/-- The candidate support of the polynomial antiderivative of a family $(q_j)$: the set of the
monomials $m + e_j$ for $j \in \iota$ and $m$ in the support of $q_j$. -/
def gradientSupport (q : ι → MvPolynomial ι ℝ) : Finset (ι →₀ ℕ) :=
  Finset.univ.biUnion fun j ↦ (q j).support.image (· + Finsupp.single j 1)

/-- If the coefficient `MvPolynomial.gradientCoeff q n` is nonzero, then $n$ is in the candidate
support `MvPolynomial.gradientSupport q`. -/
theorem gradientCoeff_ne_zero {q : ι → MvPolynomial ι ℝ} {n : ι →₀ ℕ}
    (h : gradientCoeff q n ≠ 0) : n ∈ gradientSupport q := by
  classical
  rw [gradientCoeff, div_ne_zero_iff] at h
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero h.1
  rw [mul_ne_zero_iff] at hj
  have hnj : 1 ≤ n j := Nat.one_le_iff_ne_zero.2 (by exact_mod_cast hj.2)
  refine Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _, Finset.mem_image.2
    ⟨n - Finsupp.single j 1, mem_support_iff.2 hj.1, ?_⟩⟩
  exact tsub_add_cancel_of_le (Finsupp.single_le_iff.2 hnj)

/-- The **polynomial antiderivative** of a family $(q_i)_{i \in \iota}$ of polynomials in the
variables $(x_i)_{i \in \iota}$: the polynomial whose coefficient at $x^n$ is
`MvPolynomial.gradientCoeff q n`. For a compatible family it is a polynomial $Q$ with
$\partial_i Q = q_i$ (`MvPolynomial.pderiv_gradientAntideriv`). -/
def gradientAntideriv (q : ι → MvPolynomial ι ℝ) : MvPolynomial ι ℝ :=
  AddMonoidAlgebra.ofCoeff
    (Finsupp.onFinset (gradientSupport q) (gradientCoeff q) fun _ ↦ gradientCoeff_ne_zero)

/-- The coefficient at $x^n$ of the polynomial antiderivative is `MvPolynomial.gradientCoeff q n`.
-/
theorem coeff_gradientAntideriv (q : ι → MvPolynomial ι ℝ) (n : ι →₀ ℕ) :
    (gradientAntideriv q).coeff n = gradientCoeff q n :=
  rfl

/-- The support of the polynomial antiderivative is contained in the candidate support
`MvPolynomial.gradientSupport q`. -/
theorem support_gradientAntideriv_subset (q : ι → MvPolynomial ι ℝ) :
    (gradientAntideriv q).support ⊆ gradientSupport q :=
  Finsupp.support_onFinset_subset (hf := fun _ ↦ gradientCoeff_ne_zero)

/-- If every monomial of every $q_j$ has degree at most $D$, then every monomial of the polynomial
antiderivative has degree at most $D + 1$. -/
theorem degree_le_of_mem_support_gradientAntideriv {q : ι → MvPolynomial ι ℝ} {D : ℕ}
    (hq : ∀ j, ∀ m ∈ (q j).support, m.degree ≤ D) {n : ι →₀ ℕ}
    (hn : n ∈ (gradientAntideriv q).support) : n.degree ≤ D + 1 := by
  classical
  obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.1 (support_gradientAntideriv_subset q hn)
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hj
  rw [map_add, Finsupp.degree_single]
  have := hq j m hm
  omega

omit [Fintype ι] [DecidableEq ι] in
/-- Let $(q_i)$ be a family of polynomials with $\partial_j q_i = \partial_i q_j$ for all $i, j$,
and let $n$ be a multi-index with $n_i \ge 1$ and $n_j \ge 1$. Then the compatibility holds on
the coefficients:
$$\operatorname{coeff}_{n - e_j}(q_j) \, n_i = \operatorname{coeff}_{n - e_i}(q_i) \, n_j.$$
-/
theorem coeff_sub_single_mul_eq_of_pderiv_eq {q : ι → MvPolynomial ι ℝ}
    (hq : ∀ i j, pderiv j (q i) = pderiv i (q j)) {n : ι →₀ ℕ} {i j : ι} (hi : 1 ≤ n i)
    (hj : 1 ≤ n j) :
    (q j).coeff (n - Finsupp.single j 1) * (n i : ℝ)
      = (q i).coeff (n - Finsupp.single i 1) * (n j : ℝ) := by
  classical
  rcases eq_or_ne i j with rfl | hij
  · rfl
  have key : (pderiv j (q i)).coeff (n - Finsupp.single i 1 - Finsupp.single j 1)
      = (pderiv i (q j)).coeff (n - Finsupp.single i 1 - Finsupp.single j 1) := by
    rw [hq i j]
  rw [coeff_pderiv, coeff_pderiv] at key
  have e1 : n - Finsupp.single i 1 - Finsupp.single j 1 + Finsupp.single j 1
      = n - Finsupp.single i 1 := by
    refine tsub_add_cancel_of_le (Finsupp.single_le_iff.2 ?_)
    simp [Ne.symm hij, hj]
  have e2 : n - Finsupp.single i 1 - Finsupp.single j 1 + Finsupp.single i 1
      = n - Finsupp.single j 1 := by
    rw [tsub_tsub, add_comm (Finsupp.single i 1), ← tsub_tsub]
    refine tsub_add_cancel_of_le (Finsupp.single_le_iff.2 ?_)
    simp [hij, hi]
  have e3 : (((n - Finsupp.single i 1 - Finsupp.single j 1 : ι →₀ ℕ) j : ℕ) : ℝ) + 1
      = (n j : ℝ) := by
    rw [← Nat.cast_succ]
    congr 1
    simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_apply, hij, ite_false, ite_true]
    omega
  have e4 : (((n - Finsupp.single i 1 - Finsupp.single j 1 : ι →₀ ℕ) i : ℕ) : ℝ) + 1
      = (n i : ℝ) := by
    rw [← Nat.cast_succ]
    congr 1
    simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_apply, Ne.symm hij, ite_false,
      ite_true]
    omega
  rw [e1, e2, e3, e4] at key
  exact key.symm

/-- The **Poincaré lemma for polynomials**. Let $(q_i)_{i \in \iota}$ be a family of real
polynomials in the variables $(x_i)_{i \in \iota}$, with $\iota$ finite, such that
$\partial_j q_i = \partial_i q_j$ for all $i, j$. Then the polynomial antiderivative $Q$
(`MvPolynomial.gradientAntideriv`) satisfies
$$\partial_i Q = q_i \qquad \text{for all } i.$$

The monomials of $Q$ are among the $m + e_j$ for $m$ a monomial of $q_j$, so
$\deg Q \le \max_j \deg q_j + 1$; this bound is
`MvPolynomial.degree_le_of_mem_support_gradientAntideriv`. -/
theorem pderiv_gradientAntideriv {q : ι → MvPolynomial ι ℝ}
    (hq : ∀ i j, pderiv j (q i) = pderiv i (q j)) (i : ι) :
    pderiv i (gradientAntideriv q) = q i := by
  classical
  refine MvPolynomial.ext _ _ fun m ↦ ?_
  rw [coeff_pderiv, coeff_gradientAntideriv]
  obtain ⟨n, hn⟩ : ∃ n : ι →₀ ℕ, n = m + Finsupp.single i 1 := ⟨_, rfl⟩
  have hni : n i = m i + 1 := by simp [hn]
  have hmi : n - Finsupp.single i 1 = m := by rw [hn, add_tsub_cancel_right]
  have hpos : (0 : ℝ) < ∑ j, (n j : ℝ) ^ 2 :=
    lt_of_lt_of_le (by rw [hni]; positivity)
      (Finset.single_le_sum (f := fun j ↦ (n j : ℝ) ^ 2) (fun _ _ ↦ by positivity)
        (Finset.mem_univ i))
  have hterm : ∀ j, (q j).coeff (n - Finsupp.single j 1) * (n j : ℝ) * (n i : ℝ)
      = (q i).coeff m * ((n j : ℝ) ^ 2) := by
    intro j
    rcases Nat.eq_zero_or_pos (n j) with hj | hj
    · simp [hj]
    · rw [mul_right_comm, coeff_sub_single_mul_eq_of_pderiv_eq hq (by omega) hj, hmi, sq,
        mul_assoc]
  have hcast : ((m i : ℝ) + 1) = (n i : ℝ) := by rw [hni]; push_cast; ring
  rw [← hn, gradientCoeff, div_mul_eq_mul_div, div_eq_iff hpos.ne', Finset.sum_mul, hcast]
  simp_rw [hterm]
  rw [← Finset.mul_sum]

omit [Fintype ι] [DecidableEq ι] in
/-- A polynomial whose monomials all have degree $< 0$ is zero. -/
theorem eq_zero_of_forall_degree_lt_zero {q : MvPolynomial ι ℝ}
    (h : ∀ m ∈ q.support, m.degree < 0) : q = 0 := by
  rw [← MvPolynomial.support_eq_empty, Finset.eq_empty_iff_forall_notMem]
  exact fun m hm ↦ absurd (h m hm) (Nat.not_lt_zero _)

/-- If every monomial of every $q_j$ has degree $< k$, then every monomial of the polynomial
antiderivative has degree $< k + 1$. -/
theorem degree_lt_of_mem_support_gradientAntideriv
    {q : ι → MvPolynomial ι ℝ} {k : ℕ} (hq : ∀ j, ∀ m ∈ (q j).support, m.degree < k)
    {n : ι →₀ ℕ} (hn : n ∈ (gradientAntideriv q).support) : n.degree < k + 1 := by
  obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.1 (support_gradientAntideriv_subset q hn)
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hj
  rw [map_add, Finsupp.degree_single]
  have := hq j m hm
  omega

end MvPolynomial

end Poincare

/-! ### Polynomial functions on a finite-dimensional space, in the coordinates of a basis -/

section EvalBasis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*} [Fintype ι]

namespace MvPolynomial

/-- The **polynomial function** on $E$ of a polynomial $q$ in the coordinates of a basis
$b = (b_i)_{i \in \iota}$: the function $x \mapsto q(x_1, \dots, x_n)$, where $(x_i)$ are the
coordinates of $x$ in the basis $b$.

On $\mathbb{R}^N$ with its standard basis this is $x \mapsto q(x)$
(`MvPolynomial.evalBasis_basisFun`). The polynomials of degree at most $k$ on an open set
$\Omega$ (the space $\mathbb{P}_k(\Omega)$ of [han2009theoretical]) are the restrictions to
$\Omega$ of the functions `MvPolynomial.evalBasis b q` with $q$ of total degree at most $k$. -/
def evalBasis (b : Basis ι ℝ E) (q : MvPolynomial ι ℝ) (x : E) : ℝ :=
  eval (b.equivFun x) q

variable (b : Basis ι ℝ E)

/-- The polynomial function of $q + r$ is the sum of the polynomial functions of $q$ and $r$. -/
@[simp]
theorem evalBasis_add (q r : MvPolynomial ι ℝ) :
    evalBasis b (q + r) = evalBasis b q + evalBasis b r := by
  funext x
  simp [evalBasis]

/-- The polynomial function of $q - r$ is the difference of the polynomial functions of $q$ and $r$.
-/
@[simp]
theorem evalBasis_sub (q r : MvPolynomial ι ℝ) :
    evalBasis b (q - r) = evalBasis b q - evalBasis b r := by
  funext x
  simp [evalBasis]

/-- The polynomial function of the zero polynomial is zero. -/
@[simp]
theorem evalBasis_zero : evalBasis b (0 : MvPolynomial ι ℝ) = 0 := by
  funext x
  simp [evalBasis]

/-- The polynomial function of the constant polynomial $c$ is the constant function $c$. -/
@[simp]
theorem evalBasis_C (c : ℝ) (x : E) : evalBasis b (C c) x = c := by
  simp [evalBasis]

omit [Fintype ι] in
/-- The coordinates of the basis vector $b_i$ in the basis $b$ are the unit vector $e_i$. -/
theorem _root_.Module.Basis.equivFunL_self [Finite ι] [DecidableEq ι] (i : ι) :
    b.equivFunL (b i) = Pi.single i 1 := by
  funext j
  rw [Basis.equivFunL_apply, Basis.repr_self, Finsupp.single_apply, Pi.single_apply]
  by_cases h : i = j
  · subst h
    simp
  · simp [h, Ne.symm h]

/-- The polynomial function $x \mapsto q(x_1, \dots, x_n)$ in the coordinates of a basis is smooth.
-/
theorem contDiff_evalBasis (q : MvPolynomial ι ℝ) : ContDiff ℝ ∞ (evalBasis b q) :=
  (contDiff_eval q).comp b.equivFunL.contDiff

/-- The polynomial function $x \mapsto q(x_1, \dots, x_n)$ in the coordinates of a basis $b$ has at
$x$ the derivative $\sum_i (\partial_i q)(x_1, \dots, x_n) \, b_i^*$, where $b_i^*$ is the
coordinate functional of $b_i$. -/
theorem hasFDerivAt_evalBasis (q : MvPolynomial ι ℝ) (x : E) :
    HasFDerivAt (evalBasis b q)
      ((∑ i, eval (b.equivFun x) (pderiv i q) •
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i).comp
          (b.equivFunL : E →L[ℝ] (ι → ℝ))) x :=
  (hasFDerivAt_eval q (b.equivFun x)).comp x b.equivFunL.hasFDerivAt

/-- The derivative of a polynomial function in the direction of a basis vector is the polynomial
function of the partial derivative: for every $x \in E$ and $i \in \iota$,
$$D(q \circ b^{-1})(x)(b_i) = (\partial_i q \circ b^{-1})(x),$$
where $q \circ b^{-1}$ denotes `MvPolynomial.evalBasis b q`. -/
theorem fderiv_evalBasis_apply_basis (q : MvPolynomial ι ℝ) (x : E) (i : ι) :
    fderiv ℝ (evalBasis b q) x (b i) = evalBasis b (pderiv i q) x := by
  classical
  rw [(hasFDerivAt_evalBasis b q x).fderiv, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, Basis.equivFunL_self, ContinuousLinearMap.sum_smul_proj_apply]
  simp [evalBasis, Pi.single_apply]

/-- Let $\mu$ be a measure on $E$ that is positive on nonempty open sets, and let
$\Omega \subseteq E$ be a nonempty open set. If the polynomial functions of two polynomials $q$
and $r$ agree $\mu$-almost everywhere on $\Omega$, then $q = r$.

The functions are continuous, so they agree on $\Omega$. The image of $\Omega$ under the
coordinate map has nonempty interior, and a polynomial that vanishes on a set with nonempty
interior is zero. -/
theorem eq_of_evalBasis_ae_eq [MeasurableSpace E] {μ : Measure E}
    [μ.IsOpenPosMeasure] {Ω : Opens E} (hΩ : (Ω : Set E).Nonempty) {q r : MvPolynomial ι ℝ}
    (h : evalBasis b q =ᵐ[μ.restrict (Ω : Set E)] evalBasis b r) : q = r := by
  have heq : EqOn (evalBasis b q) (evalBasis b r) Ω :=
    Measure.eqOn_open_of_ae_eq h Ω.isOpen (contDiff_evalBasis b q).continuous.continuousOn
      (contDiff_evalBasis b r).continuous.continuousOn
  have hopen : IsOpen (b.equivFunL '' (Ω : Set E)) := b.equivFunL.isOpenMap _ Ω.isOpen
  refine sub_eq_zero.1 (eq_zero_of_eval_eq_zero_of_mem_interior (D := b.equivFunL '' Ω)
    (by rw [hopen.interior_eq]; exact hΩ.image _) fun y hy ↦ ?_)
  rw [hopen.interior_eq] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  have := heq hx
  simp only [evalBasis] at this
  change eval (b.equivFun x) (q - r) = 0
  rw [map_sub, this, sub_self]

end MvPolynomial

end EvalBasis

/-! ### Vanishing top-order derivatives on a connected open set force a polynomial -/

section VanishingTop

open MvPolynomial

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι : Type*} [Fintype ι] [LinearOrder ι] {b : Basis ι ℝ E}
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens E} {μ : Measure E} [μ.IsAddHaarMeasure]

namespace SobolevMultiIndex

omit [μ.IsAddHaarMeasure] in
/-- Let $E$ be finite-dimensional and let $u \in W^{k+1,p}(\Omega)$ be real-valued. Then $u$ has a
first-order weak derivative $w$ on $\Omega$ whose components in the basis $b$ are the partial
derivatives of $u$: $w(x)(b_i) = \partial_i u(x)$ for almost every $x \in \Omega$ and every $i$.

This is `SobolevMultiIndex.exists_hasWeakFDerivOn_fn` read on
$W^{k+1,p}(\Omega) \subseteq W^{1,p}(\Omega)$. -/
theorem exists_hasWeakFDerivOn_fn_of_succ {k : ℕ} (u : SobolevMultiIndex ℝ b (k + 1) p Ω μ) :
    ∃ w : E → E →L[ℝ] ℝ, HasWeakFDerivOn (fn u) w Ω μ ∧
      ∀ i, (fun x ↦ w x (b i)) =ᵐ[μ.restrict (Ω : Set E)]
        weakDeriv u (MultiIndexLE.singleLE i) := by
  obtain ⟨w, hw, -, hwi, -⟩ :=
    exists_hasWeakFDerivOn_fn (toLowerOrder ℝ b p Ω μ (Nat.succ_le_succ (Nat.zero_le k)) u)
  exact ⟨w, hw, hwi⟩

/-- Let $E$ be finite-dimensional with a Haar measure $\mu$, let $\Omega$ be a connected open set,
and let $u \in W^{k+1,p}(\Omega)$ be real-valued. Let $g : E \to \mathbb{R}$ be smooth with
$Dg(x)(b_i) = \partial_i u(x)$ for almost every $x \in \Omega$ and every $i$. Then there is a
constant $c$ with $u = g + c$ almost everywhere on $\Omega$. -/
theorem exists_ae_eq_add_const_of_forall_fderiv_apply_ae_eq {k : ℕ}
    (hΩ : IsPreconnected (Ω : Set E)) (u : SobolevMultiIndex ℝ b (k + 1) p Ω μ) {g : E → ℝ}
    (hg : ContDiff ℝ ∞ g)
    (hgi : ∀ i, (fun x ↦ fderiv ℝ g x (b i)) =ᵐ[μ.restrict (Ω : Set E)]
      weakDeriv u (MultiIndexLE.singleLE i)) :
    ∃ c : ℝ, fn u =ᵐ[μ.restrict (Ω : Set E)] fun x ↦ g x + c := by
  obtain ⟨w, hw, hwi⟩ := exists_hasWeakFDerivOn_fn_of_succ u
  have hsub : HasWeakFDerivOn (fn u - g) (w - fderiv ℝ g) Ω μ := by
    have h := hw.sub (hg.of_le (by simp)).hasWeakFDerivOn
    exact h.congr_ae (Filter.EventuallyEq.refl _ _) (Eventually.of_forall fun x ↦ by
      simp [map_sub])
  have hzero : (w - fderiv ℝ g) =ᵐ[μ.restrict (Ω : Set E)] 0 := by
    have hall : ∀ᵐ x ∂μ.restrict (Ω : Set E), ∀ i, w x (b i) = fderiv ℝ g x (b i) :=
      ae_all_iff.2 fun i ↦ (hwi i).trans (hgi i).symm
    filter_upwards [hall] with x hx
    rw [Pi.sub_apply, Pi.zero_apply, sub_eq_zero]
    exact ContinuousLinearMap.coe_injective (b.ext fun i ↦ hx i)
  obtain ⟨c, hc⟩ := hsub.ae_eq_const_of_isPreconnected hzero hΩ
  refine ⟨c, ?_⟩
  filter_upwards [hc] with x hx
  rw [Pi.sub_apply] at hx
  linarith

/-- The order of the multi-index $\alpha + e_i$ is $|\alpha| + 1$. -/
theorem _root_.MultiIndexLE.sum_addSingle {k : ℕ} (i : ι) (α : MultiIndexLE ι k) :
    ∑ j, ((MultiIndexLE.addSingle i α : MultiIndexLE ι (k + 1)) : ι → ℕ) j = ∑ j, α.1 j + 1 := by
  simp [MultiIndexLE.coe_addSingle, Finset.sum_add_distrib]

/-- As multi-indices of order at most $k + 2$, $e_i + e_j = e_j + e_i$. -/
theorem _root_.MultiIndexLE.addSingle_singleLE_comm {k : ℕ} (i j : ι) :
    (MultiIndexLE.addSingle j (MultiIndexLE.singleLE i : MultiIndexLE ι (k + 1)) :
        MultiIndexLE ι (k + 1 + 1))
      = MultiIndexLE.addSingle i (MultiIndexLE.singleLE j) :=
  Subtype.ext (add_comm _ _)

/-- Let $E$ be finite-dimensional with a Haar measure $\mu$ and a basis $b$, and let
$\Omega \subseteq E$ be a connected open set. Let $k \ge 0$ and let $u \in W^{k,p}(\Omega)$ be
real-valued with $\partial^\alpha u = 0$ for every multi-index $\alpha$ with $|\alpha| = k$.
Then there is a polynomial $q$, all of whose monomials have degree $< k$, such that
$$u(x) = q(x_1, \dots, x_n) \qquad \text{for almost every } x \in \Omega,$$
where $(x_i)$ are the coordinates of $x$ in the basis $b$. This is the sentence before Theorem
7.3.12 of [han2009theoretical].

At $k = 0$ the polynomial is $0$. The proof is an induction on $k$. The partial derivatives
$\partial_i u \in W^{k-1,p}(\Omega)$ are polynomials $q_i$ by the induction hypothesis. They
satisfy $\partial_j q_i = \partial_i q_j$, since both are the weak derivative
$\partial_i \partial_j u$, so they are the gradient of a polynomial $Q$
(`MvPolynomial.pderiv_gradientAntideriv`). Then $u - Q$ has weak gradient zero, and it is
constant on the connected set $\Omega$ (`HasWeakFDerivOn.ae_eq_const_of_isPreconnected`). -/
theorem exists_mvPolynomial_ae_eq_of_forall_weakDeriv_eq_zero (hΩ : IsPreconnected (Ω : Set E)) :
    ∀ (k : ℕ) (u : SobolevMultiIndex ℝ b k p Ω μ),
      (∀ α : MultiIndexEq ι k, weakDeriv u α.1 = 0) →
      ∃ q : MvPolynomial ι ℝ, (∀ m ∈ q.support, m.degree < k) ∧
        fn u =ᵐ[μ.restrict (Ω : Set E)] evalBasis b q := by
  classical
  intro k
  induction k with
  | zero =>
    intro u hu
    refine ⟨0, by simp, ?_⟩
    have h0 := hu ⟨0, Fintype.sum_eq_zero _ fun _ ↦ rfl⟩
    rw [evalBasis_zero, ← weakDeriv_zero u, h0]
    exact Lp.coeFn_zero _ _ _
  | succ k ih =>
    intro u hu
    rcases (Ω : Set E).eq_empty_or_nonempty with hemp | hne
    · refine ⟨0, by simp, ?_⟩
      unfold Filter.EventuallyEq
      rw [hemp, Measure.restrict_empty, ae_zero]
      exact Filter.eventually_bot
    -- the partial derivatives are polynomials
    have hv : ∀ (i : ι) (α : MultiIndexEq ι k),
        weakDeriv (partialDeriv ℝ b p Ω μ i u) α.1 = 0 := fun i α ↦
      hu ⟨MultiIndexLE.addSingle i α.1, by rw [MultiIndexLE.sum_addSingle, α.2]⟩
    choose q hqdeg hqae using fun i ↦ ih (partialDeriv ℝ b p Ω μ i u) (hv i)
    have hqae' : ∀ i, (weakDeriv u (MultiIndexLE.singleLE i) : E → ℝ)
        =ᵐ[μ.restrict (Ω : Set E)] evalBasis b (q i) := fun i ↦ by
      rw [← fn_partialDeriv]
      exact hqae i
    -- compatibility of the family
    have hcomp : ∀ i j, pderiv j (q i) = pderiv i (q j) := by
      rcases k with _ | k
      · intro i j
        have h0 : ∀ i, q i = 0 := fun i ↦ MvPolynomial.eq_zero_of_forall_degree_lt_zero (hqdeg i)
        simp [h0]
      · intro i j
        have key : ∀ i j, evalBasis b (pderiv j (q i)) =ᵐ[μ.restrict (Ω : Set E)]
            (weakDeriv u (MultiIndexLE.addSingle i (MultiIndexLE.singleLE j)) : E → ℝ) := by
          intro i j
          have h1 : HasWeakIteratedLineDerivOn ![b j] (weakDeriv u (MultiIndexLE.singleLE i))
              (weakDeriv u (MultiIndexLE.addSingle i (MultiIndexLE.singleLE j))) Ω μ :=
            (hasWeakIteratedLineDerivOn_addSingle u i (MultiIndexLE.singleLE j)).of_perm
              (multiIndexTuple_single_perm (b : ι → E) j)
          have h2 : HasWeakIteratedLineDerivOn ![b j] (weakDeriv u (MultiIndexLE.singleLE i))
              (evalBasis b (pderiv j (q i))) Ω μ := by
            have h := ((contDiff_evalBasis b (q i)).contDiffOn.hasWeakIteratedFDerivOn
              (Ω := Ω) (μ := μ) (m := 1) (by simp)).lineDeriv ![b j]
            refine h.congr_ae (hqae' i).symm (Eventually.of_forall fun x ↦ ?_)
            simp only [iteratedFDeriv_one_apply, Matrix.cons_val_zero]
            exact fderiv_evalBasis_apply_basis b (q i) x j
          exact (ae_restrict_iff' Ω.isOpen.measurableSet).2 (h2.ae_eq h1)
        refine eq_of_evalBasis_ae_eq b hne ((key i j).trans ?_)
        rw [MultiIndexLE.addSingle_singleLE_comm]
        exact (key j i).symm
    -- the antiderivative
    obtain ⟨Q, hQ⟩ : ∃ Q, Q = gradientAntideriv q := ⟨_, rfl⟩
    have hQi : ∀ i, pderiv i Q = q i := fun i ↦ hQ ▸ pderiv_gradientAntideriv hcomp i
    have hQdeg : ∀ n ∈ Q.support, n.degree < k + 1 := fun n hn ↦
      degree_lt_of_mem_support_gradientAntideriv hqdeg (hQ ▸ hn)
    obtain ⟨c, hc⟩ := exists_ae_eq_add_const_of_forall_fderiv_apply_ae_eq hΩ u
      (contDiff_evalBasis b Q) fun i ↦ by
        refine Filter.EventuallyEq.trans (Eventually.of_forall fun x ↦ ?_) (hqae' i).symm
        change fderiv ℝ (evalBasis b Q) x (b i) = evalBasis b (q i) x
        rw [fderiv_evalBasis_apply_basis, hQi]
    refine ⟨Q + C c, fun m hm ↦ ?_, ?_⟩
    · rcases Finset.mem_union.1 (support_add hm) with h | h
      · exact hQdeg m h
      · rw [support_C] at h
        split_ifs at h with hc0
        · exact absurd h (Finset.notMem_empty _)
        · rw [Finset.mem_singleton.1 h, map_zero]
          exact Nat.succ_pos _
    · filter_upwards [hc] with x hx
      rw [hx, evalBasis_add, Pi.add_apply, evalBasis_C]

end SobolevMultiIndex

end VanishingTop

/-! ### The abstract Deny–Lions theorem -/

section Abstract

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {ι : Type*} [Fintype ι] [LinearOrder ι] {b : Basis ι ℝ E} {k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {Ω : Opens E} {μ : Measure E} [IsFiniteMeasureOnCompacts μ] [IsLocallyFiniteMeasure μ]

/-- Let $V$ be a real normed space. A seminorm $f$ on $V$ with $f(v) \le c \|v\|$ for all $v$ is
continuous. -/
theorem Seminorm.continuous_of_forall_le_mul_norm {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (f : Seminorm ℝ V) {c : ℝ} (hf : ∀ v, f v ≤ c * ‖v‖) : Continuous f := by
  refine Seminorm.continuous_of_le (q := c.toNNReal • normSeminorm ℝ V) ?_ (Seminorm.le_def.2
    fun v ↦ ?_)
  · have : ⇑(c.toNNReal • normSeminorm ℝ V) = fun v ↦ (c.toNNReal : ℝ) * ‖v‖ := by
      funext v
      simp [NNReal.smul_def]
    rw [this]
    exact continuous_const.mul continuous_norm
  · simp only [smul_apply, NNReal.smul_def, smul_eq_mul, coe_normSeminorm]
    exact (hf v).trans (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal c) (norm_nonneg _))

namespace SobolevMultiIndex

omit [CompleteSpace F] [IsFiniteMeasureOnCompacts μ] [IsLocallyFiniteMeasure μ] in
/-- Let $p < \infty$ and $u \in W^{k+1,p}(\Omega)$. Then
$$\|u\|_{k+1,p,\Omega} \le \|u\|_{k,p,\Omega} + |u|_{k+1,p,\Omega},$$
because the $\ell^p$ norm of two numbers is at most their sum. -/
theorem norm_le_norm_toLowerOrder_add_topSeminorm (hp : p ≠ ⊤)
    (u : SobolevMultiIndex F b (k + 1) p Ω μ) :
    ‖u‖ ≤ ‖toLowerOrder F b p Ω μ (Nat.le_succ k) u‖ + topSeminorm F b (k + 1) p Ω μ u := by
  have hP : 1 ≤ p.toReal := by
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_mono hp Fact.out
  have h := norm_rpow_eq_norm_toLowerOrder_rpow_add hp u
  rw [← Real.rpow_le_rpow_iff (norm_nonneg _) (add_nonneg (norm_nonneg _) (apply_nonneg _ _))
    (zero_lt_one.trans_le hP), h]
  exact Real.add_rpow_le_rpow_add (norm_nonneg _) (apply_nonneg _ _) hP

/-- The **abstract Deny–Lions theorem**. Let $F$ be a Banach space, let $\mu$ be locally finite and
finite on compact sets, and let $1 \le p < \infty$. Assume that the inclusion of
$W^{k+1,p}(\Omega)$ in $W^{k,p}(\Omega)$ is a compact embedding. Let $f_j$, for $j$ in a finite
set $J$, be continuous seminorms on $W^{k+1,p}(\Omega)$ such that

(H2)′ if $|v|_{k+1,p,\Omega} = 0$ and $f_j(v) = 0$ for all $j$, then $v = 0$.

Then there is $C > 0$ such that for all $v \in W^{k+1,p}(\Omega)$,
$$\|v\|_{k+1,p,\Omega} \le C \Bigl(|v|_{k+1,p,\Omega} + \sum_j f_j(v)\Bigr).$$
This is Theorem 7.3.13 of [han2009theoretical] in abstract form, and the argument of the proof
of Theorem 7.3.12.

The compact embedding is `IsCompactEmbedding` of `SobolevMultiIndex.toLowerOrderL`. The proof is
the book's argument by contradiction: a sequence with $\|v_n\| = 1$ and
$|v_n| + \sum_j f_j(v_n) \le 1/n$ has a subsequence that converges in $W^{k,p}(\Omega)$. The
top-order seminorms tend to zero, so the subsequence is a Cauchy sequence in $W^{k+1,p}(\Omega)$
(`SobolevMultiIndex.norm_le_norm_toLowerOrder_add_topSeminorm`). Its limit $v$ has $\|v\| = 1$,
$|v| = 0$ and $f_j(v) = 0$ for all $j$, which contradicts (H2)′. -/
theorem exists_norm_le_topSeminorm_add_sum_of_isCompactEmbedding (hp : p ≠ ⊤)
    (hc : IsCompactEmbedding (toLowerOrderL F b p Ω μ (Nat.le_succ k)).toLinearMap)
    {J : Type*} [Fintype J] (f : J → Seminorm ℝ (SobolevMultiIndex F b (k + 1) p Ω μ))
    (hf : ∀ j, Continuous (f j))
    (h2 : ∀ v, topSeminorm F b (k + 1) p Ω μ v = 0 → (∀ j, f j v = 0) → v = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : SobolevMultiIndex F b (k + 1) p Ω μ,
      ‖v‖ ≤ C * (topSeminorm F b (k + 1) p Ω μ v + ∑ j, f j v) := by
  obtain ⟨N, hN⟩ : ∃ N : Seminorm ℝ (SobolevMultiIndex F b (k + 1) p Ω μ),
      N = topSeminorm F b (k + 1) p Ω μ + ∑ j, f j := ⟨_, rfl⟩
  have hNapply : ∀ v, N v = topSeminorm F b (k + 1) p Ω μ v + ∑ j, f j v := fun v ↦ by
    rw [hN, add_apply]
    congr 1
    change (FunLike.coeAddMonoidHom _ _ _ (∑ j, f j)) v = _
    rw [map_sum, Finset.sum_apply]
    rfl
  have htopN : ∀ v, topSeminorm F b (k + 1) p Ω μ v ≤ N v := fun v ↦ by
    rw [hNapply]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun j _ ↦ apply_nonneg _ _)
  have hfN : ∀ j v, f j v ≤ N v := fun j v ↦ by
    rw [hNapply]
    exact le_add_of_nonneg_left (apply_nonneg _ _) |>.trans' (Finset.single_le_sum
      (f := fun j ↦ f j v) (fun j _ ↦ apply_nonneg _ _) (Finset.mem_univ j))
  by_contra hcon
  push Not at hcon
  simp_rw [← hNapply] at hcon
  -- the normalized sequence
  have hseq : ∀ n : ℕ, ∃ v : SobolevMultiIndex F b (k + 1) p Ω μ,
      ‖v‖ = 1 ∧ N v ≤ 1 / (n + 1) := by
    intro n
    obtain ⟨v, hv⟩ := hcon (n + 1) (by positivity)
    have hv0 : ‖v‖ ≠ 0 := fun h ↦ by
      rw [norm_eq_zero] at h
      subst h
      simp at hv
    refine ⟨‖v‖⁻¹ • v, by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hv0], ?_⟩
    have hn0 : (0 : ℝ) < ‖v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hv0)
    rw [map_smul_eq_mul, norm_inv, norm_norm, inv_mul_le_iff₀ hn0, mul_one_div,
      le_div_iff₀ (by positivity), mul_comm]
    exact hv.le
  choose v hv1 hvN using hseq
  -- a subsequence converging in `W^{k,p}(Ω)`
  obtain ⟨φ, w, hφ, hw⟩ := hc.exists_subseq_tendsto v ⟨1, fun n ↦ (hv1 n).le⟩
  have hNlim : Tendsto (fun n ↦ N (v (φ n))) atTop (𝓝 0) := by
    refine squeeze_zero (fun n ↦ apply_nonneg _ _) (fun n ↦ hvN (φ n)) ?_
    have h1 : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    refine squeeze_zero (fun n ↦ by positivity) (fun n ↦ ?_) h1
    exact one_div_le_one_div_of_le (by positivity)
      (by exact_mod_cast Nat.succ_le_succ (hφ.id_le n))
  have htop : Tendsto (fun n ↦ topSeminorm F b (k + 1) p Ω μ (v (φ n))) atTop (𝓝 0) :=
    squeeze_zero (fun n ↦ apply_nonneg _ _) (fun n ↦ htopN _) hNlim
  have hfj : ∀ j, Tendsto (fun n ↦ f j (v (φ n))) atTop (𝓝 0) := fun j ↦
    squeeze_zero (fun n ↦ apply_nonneg _ _) (fun n ↦ hfN j _) hNlim
  -- the subsequence is Cauchy in `W^{k+1,p}(Ω)`
  have hcauchy : CauchySeq (fun n ↦ v (φ n)) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N₁, hN₁⟩ := Metric.cauchySeq_iff.1 hw.cauchySeq (ε / 3) (by positivity)
    obtain ⟨N₂, hN₂⟩ := (Metric.tendsto_atTop.1 htop) (ε / 3) (by positivity)
    refine ⟨max N₁ N₂, fun m hm n hn ↦ ?_⟩
    have h1 := hN₁ m (le_of_max_le_left hm) n (le_of_max_le_left hn)
    have h2 := hN₂ m (le_of_max_le_right hm)
    have h3 := hN₂ n (le_of_max_le_right hn)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (apply_nonneg _ _)] at h2 h3
    rw [dist_eq_norm] at h1 ⊢
    calc ‖v (φ m) - v (φ n)‖
        ≤ ‖toLowerOrder F b p Ω μ (Nat.le_succ k) (v (φ m) - v (φ n))‖
          + topSeminorm F b (k + 1) p Ω μ (v (φ m) - v (φ n)) :=
          norm_le_norm_toLowerOrder_add_topSeminorm hp _
      _ ≤ ‖toLowerOrder F b p Ω μ (Nat.le_succ k) (v (φ m) - v (φ n))‖
          + (topSeminorm F b (k + 1) p Ω μ (v (φ m))
            + topSeminorm F b (k + 1) p Ω μ (v (φ n))) :=
          add_le_add le_rfl (map_sub_le_add _ _ _)
      _ < ε / 3 + (ε / 3 + ε / 3) := by
          refine add_lt_add ?_ (add_lt_add h2 h3)
          rw [← map_sub] at h1
          exact h1
      _ = ε := by ring
  obtain ⟨vlim, hvlim⟩ := cauchySeq_tendsto_of_complete hcauchy
  -- the limit has norm one, vanishing top seminorm and vanishing `f_j`
  have hnorm : ‖vlim‖ = 1 := by
    have h := (continuous_norm.tendsto vlim).comp hvlim
    simp only [Function.comp_def, hv1] at h
    exact tendsto_nhds_unique h tendsto_const_nhds
  have htoplim : topSeminorm F b (k + 1) p Ω μ vlim = 0 :=
    tendsto_nhds_unique ((continuous_topSeminorm.tendsto vlim).comp hvlim) htop
  have hflim : ∀ j, f j vlim = 0 := fun j ↦
    tendsto_nhds_unique (((hf j).tendsto vlim).comp hvlim) (hfj j)
  have := h2 vlim htoplim hflim
  rw [this, norm_zero] at hnorm
  exact zero_ne_one hnorm

end SobolevMultiIndex

end Abstract

/-!
### The seminorm $v \mapsto \int_s |Lv| \, d\sigma$ of a bounded map into $L^q$ of a finite measure
-/

section AbsIntegralSeminorm

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {X : Type*} [MeasurableSpace X]
  {σ : Measure X} [IsFiniteMeasure σ] {q : ℝ≥0∞} [Fact (1 ≤ q)]

/-- The **seminorm** $v \mapsto \int_s |(Lv)(x)| \, d\sigma(x)$ on a real normed space $W$, for a
bounded linear map $L : W \to L^q(\sigma)$ into the $L^q$ space of a finite measure $\sigma$,
with $1 \le q$, and a set $s$. The finite measure gives $L^q(\sigma) \subseteq L^1(\sigma)$.

With $L$ a trace operator, this is the boundary seminorm $f(v) = \int_\Gamma |\gamma v| \, ds$
to which the Deny–Lions norm equivalences are applied in Examples 7.3.15 and 7.3.16 of
[han2009theoretical]. -/
def absIntegralSeminorm (L : W →L[ℝ] Lp ℝ q σ) (s : Set X) : Seminorm ℝ W where
  toFun v := ∫ x in s, |(L v : X → ℝ) x| ∂σ
  map_zero' := by
    rw [map_zero]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [ae_restrict_of_ae (Lp.coeFn_zero ℝ q σ)] with x hx
    rw [hx, Pi.zero_apply, abs_zero]
  add_le' v w := by
    have hi : ∀ u : W, Integrable (fun x ↦ |(L u : X → ℝ) x|) (σ.restrict s) := fun u ↦
      ((Lp.memLp (L u)).integrable Fact.out).abs.integrableOn
    rw [← integral_add (hi v) (hi w)]
    refine integral_mono_ae (hi (v + w)) ((hi v).add (hi w)) ?_
    rw [map_add]
    filter_upwards [ae_restrict_of_ae (Lp.coeFn_add (L v) (L w))] with x hx
    rw [hx, Pi.add_apply]
    exact abs_add_le _ _
  neg' v := by
    rw [map_neg]
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae (Lp.coeFn_neg (L v))] with x hx
    rw [hx, Pi.neg_apply, abs_neg]
  smul' c v := by
    rw [map_smul, Real.norm_eq_abs, ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae (Lp.coeFn_smul c (L v))] with x hx
    rw [hx, Pi.smul_apply, smul_eq_mul, abs_mul]

/-- The value of `absIntegralSeminorm L s` at $v$ is $\int_s |(Lv)(x)| \, d\sigma(x)$. -/
theorem absIntegralSeminorm_apply (L : W →L[ℝ] Lp ℝ q σ) (s : Set X) (v : W) :
    absIntegralSeminorm L s v = ∫ x in s, |(L v : X → ℝ) x| ∂σ :=
  rfl

/-- The seminorm $v \mapsto \int_s |Lv| \, d\sigma$ satisfies the hypothesis (H1): there is $c$ with
$\int_s |Lv| \, d\sigma \le c \|v\|$ for all $v \in W$.

The bound comes from the inclusion $L^q(\sigma) \subseteq L^1(\sigma)$ for the finite measure
$\sigma$ (`MeasureTheory.Lp.monoExponentL`). With `Seminorm.continuous_of_forall_le_mul_norm`
the seminorm is therefore continuous. -/
theorem exists_absIntegralSeminorm_le (L : W →L[ℝ] Lp ℝ q σ) (s : Set X) :
    ∃ c : ℝ, ∀ v, absIntegralSeminorm L s v ≤ c * ‖v‖ := by
  refine ⟨‖(Lp.monoExponentL ℝ σ q 1 Fact.out).comp L‖, fun v ↦ ?_⟩
  rw [absIntegralSeminorm_apply]
  have hi : Integrable (fun x ↦ |(L v : X → ℝ) x|) σ :=
    ((Lp.memLp (L v)).integrable Fact.out).abs
  calc ∫ x in s, |(L v : X → ℝ) x| ∂σ
      ≤ ∫ x, |(L v : X → ℝ) x| ∂σ :=
        setIntegral_le_integral hi (Eventually.of_forall fun x ↦ abs_nonneg _)
    _ = ‖((Lp.monoExponentL ℝ σ q 1 Fact.out).comp L) v‖ := by
        rw [ContinuousLinearMap.comp_apply, L1.norm_eq_integral_norm]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_monoExponentL (G := ℝ) (μ := σ) (p := q) (q := 1) Fact.out
          (L v)] with x hx
        rw [hx, Real.norm_eq_abs]
    _ ≤ _ := ContinuousLinearMap.le_opNorm _ v

end AbsIntegralSeminorm
/-! ### The two norms (7.3.3) and (7.3.4) -/

section TwoNorms

/-- Let $z \in \mathbb{R}^\iota$ have nonnegative entries, with $\iota$ finite, and let
$1 \le p < \infty$. Then
$$\Bigl(\sum_i z_i^p\Bigr)^{1/p} \le \sum_i z_i.$$
-/
theorem Real.rpow_sum_rpow_le_sum {ι : Type*} [Fintype ι] {z : ι → ℝ} (hz : ∀ i, 0 ≤ z i)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) :
    (∑ i, z i ^ p.toReal) ^ (1 / p.toReal) ≤ ∑ i, z i := by
  have hP : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne' hp
  have h := PiLp.norm_le_sum_norm (p := p) (WithLp.toLp p z)
  rw [PiLp.norm_eq_sum hP] at h
  refine le_of_le_of_eq (le_of_eq_of_le ?_ h) ?_
  · congr 1
    exact Finset.sum_congr rfl fun i _ ↦ by simp [Real.norm_eq_abs, abs_of_nonneg (hz i)]
  · exact Finset.sum_congr rfl fun i _ ↦ by simp [Real.norm_eq_abs, abs_of_nonneg (hz i)]

/-- Let $z \in \mathbb{R}^\iota$ have nonnegative entries, with $\iota$ finite of cardinality $n$,
and let $1 \le p < \infty$. Then
$$\sum_i z_i \le n \Bigl(\sum_i z_i^p\Bigr)^{1/p}.$$
-/
theorem Real.sum_le_card_mul_rpow_sum_rpow {ι : Type*} [Fintype ι] {z : ι → ℝ}
    (hz : ∀ i, 0 ≤ z i) {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) :
    ∑ i, z i ≤ Fintype.card ι * (∑ i, z i ^ p.toReal) ^ (1 / p.toReal) := by
  have hP : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne' hp
  have hle : ∀ i, z i ≤ (∑ i, z i ^ p.toReal) ^ (1 / p.toReal) := fun i ↦ by
    have h := PiLp.norm_apply_le (p := p) (WithLp.toLp p z) i
    rw [PiLp.norm_eq_sum hP] at h
    simp only [Real.norm_eq_abs, abs_of_nonneg (hz _)] at h
    exact h
  calc ∑ i, z i ≤ ∑ _i : ι, (∑ i, z i ^ p.toReal) ^ (1 / p.toReal) :=
        Finset.sum_le_sum fun i _ ↦ hle i
    _ = Fintype.card ι * (∑ i, z i ^ p.toReal) ^ (1 / p.toReal) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end TwoNorms

/-! ### The reverse inequality, and the norm (7.3.4) -/

section Reverse

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ι : Type*} [Fintype ι] [LinearOrder ι] {b : Basis ι ℝ E} {k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {Ω : Opens E} {μ : Measure E}

namespace SobolevMultiIndex

/-- The easy half of the Deny–Lions equivalences. Let $f_j$, for $j$ in a finite set $J$ of
cardinality $|J|$, be seminorms on $W^{k,p}(\Omega)$ with $f_j(v) \le c \|v\|_{k,p,\Omega}$ for
all $j$ and $v$ (the hypothesis (H1)). Then for all $v \in W^{k,p}(\Omega)$,
$$|v|_{k,p,\Omega} + \sum_j f_j(v) \le (1 + |J| c) \|v\|_{k,p,\Omega}.$$
-/
theorem topSeminorm_add_sum_le_norm {J : Type*} [Fintype J]
    (f : J → Seminorm ℝ (SobolevMultiIndex F b k p Ω μ)) {c : ℝ} (hf : ∀ j v, f j v ≤ c * ‖v‖)
    (v : SobolevMultiIndex F b k p Ω μ) :
    topSeminorm F b k p Ω μ v + ∑ j, f j v ≤ (1 + Fintype.card J * c) * ‖v‖ := by
  calc topSeminorm F b k p Ω μ v + ∑ j, f j v ≤ ‖v‖ + ∑ _j : J, c * ‖v‖ :=
        add_le_add (topSeminorm_le_norm v) (Finset.sum_le_sum fun j _ ↦ hf j v)
    _ = (1 + Fintype.card J * c) * ‖v‖ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

/-- The quantity (7.3.4) is the $\ell^p$ norm of the vector
$(|v|_{k,p,\Omega}, f_1(v), \dots, f_J(v))$, indexed by `Option J`:
$$\Bigl(|v|_{k,p,\Omega}^p + \sum_j f_j(v)^p\Bigr)^{1/p} = \Bigl(\sum_{o} z_o^p\Bigr)^{1/p},$$
where $z_{\mathrm{none}} = |v|_{k,p,\Omega}$ and $z_j = f_j(v)$. -/
theorem lp_topSeminorm_sum_eq {J : Type*} [Fintype J]
    (f : J → Seminorm ℝ (SobolevMultiIndex F b k p Ω μ)) (v : SobolevMultiIndex F b k p Ω μ) :
    (topSeminorm F b k p Ω μ v ^ p.toReal + ∑ j, f j v ^ p.toReal) ^ (1 / p.toReal)
      = (∑ o : Option J, (o.elim (topSeminorm F b k p Ω μ v) fun j ↦ f j v) ^ p.toReal)
          ^ (1 / p.toReal) := by
  rw [Fintype.sum_option]
  rfl

/-- For $1 \le p < \infty$, seminorms $f_j$ on $W^{k,p}(\Omega)$ indexed by a finite set $J$, and
$v \in W^{k,p}(\Omega)$, the quantity (7.3.4) is at most the quantity (7.3.3):
$$\Bigl(|v|_{k,p,\Omega}^p + \sum_j f_j(v)^p\Bigr)^{1/p} \le |v|_{k,p,\Omega} + \sum_j f_j(v).$$
-/
theorem lp_topSeminorm_sum_le_add (hp : p ≠ ⊤) {J : Type*} [Fintype J]
    (f : J → Seminorm ℝ (SobolevMultiIndex F b k p Ω μ)) (v : SobolevMultiIndex F b k p Ω μ) :
    (topSeminorm F b k p Ω μ v ^ p.toReal + ∑ j, f j v ^ p.toReal) ^ (1 / p.toReal)
      ≤ topSeminorm F b k p Ω μ v + ∑ j, f j v := by
  rw [lp_topSeminorm_sum_eq]
  refine (Real.rpow_sum_rpow_le_sum (fun o ↦ ?_) hp).trans (le_of_eq ?_)
  · cases o <;> exact apply_nonneg _ _
  · rw [Fintype.sum_option]
    rfl

/-- For $1 \le p < \infty$, seminorms $f_j$ on $W^{k,p}(\Omega)$ indexed by a finite set $J$ of
cardinality $|J|$, and $v \in W^{k,p}(\Omega)$, the quantity (7.3.3) is at most $|J| + 1$ times
the quantity (7.3.4):
$$|v|_{k,p,\Omega} + \sum_j f_j(v)
  \le (|J| + 1) \Bigl(|v|_{k,p,\Omega}^p + \sum_j f_j(v)^p\Bigr)^{1/p}.$$
-/
theorem add_le_card_mul_lp_topSeminorm_sum (hp : p ≠ ⊤) {J : Type*} [Fintype J]
    (f : J → Seminorm ℝ (SobolevMultiIndex F b k p Ω μ)) (v : SobolevMultiIndex F b k p Ω μ) :
    topSeminorm F b k p Ω μ v + ∑ j, f j v
      ≤ (Fintype.card J + 1)
        * (topSeminorm F b k p Ω μ v ^ p.toReal + ∑ j, f j v ^ p.toReal) ^ (1 / p.toReal) := by
  rw [lp_topSeminorm_sum_eq]
  have h := Real.sum_le_card_mul_rpow_sum_rpow
    (z := fun o : Option J ↦ o.elim (topSeminorm F b k p Ω μ v) fun j ↦ f j v)
    (fun o ↦ by cases o <;> exact apply_nonneg _ _) hp
  rw [Fintype.sum_option, Fintype.card_option] at h
  push_cast at h
  exact h

end SobolevMultiIndex

end Reverse

/-! ### The Deny–Lions theorems on an extension domain of $\mathbb{R}^N$ -/

section Euclidean

open MvPolynomial SobolevMultiIndex

variable {N : ℕ} {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] {Ω : Opens (EuclideanSpace ℝ (Fin N))} {k : ℕ}

/-- For the standard basis of $\mathbb{R}^N$, the polynomial function `MvPolynomial.evalBasis` of
$q$ is $x \mapsto q(x_1, \dots, x_N)$. -/
theorem MvPolynomial.evalBasis_basisFun (q : MvPolynomial (Fin N) ℝ)
    (x : EuclideanSpace ℝ (Fin N)) :
    evalBasis (EuclideanSpace.basisFun (Fin N) ℝ).toBasis q x = eval (fun i ↦ x i) q := by
  unfold evalBasis
  congr 1

/-- A polynomial all of whose monomials have degree $< k + 1$ has total degree at most $k$. -/
theorem MvPolynomial.mem_restrictTotalDegree_of_forall_degree_lt {ι : Type*}
    {q : MvPolynomial ι ℝ} (h : ∀ m ∈ q.support, m.degree < k + 1) :
    q ∈ restrictTotalDegree ι ℝ k := by
  rw [mem_restrictTotalDegree, totalDegree]
  exact Finset.sup_le fun m hm ↦ Nat.lt_succ_iff.1 (h m hm)

/-- Let $\Omega \subseteq \mathbb{R}^N$ be a connected open set and let $v \in W^{k+1,p}(\Omega)$
with $|v|_{k+1,p,\Omega} = 0$. Then $v \in \mathbb{P}_k(\Omega)$: there is a polynomial $q$ of
total degree at most $k$ with $v(x) = q(x)$ for almost every $x \in \Omega$. This is the
sentence before Theorem 7.3.12 of [han2009theoretical], on $\mathbb{R}^N$. -/
theorem SobolevEuclidean.exists_mem_restrictTotalDegree_ae_eq_of_topSeminorm_eq_zero
    (hΩ : IsPreconnected (Ω : Set (EuclideanSpace ℝ (Fin N))))
    {v : SobolevEuclidean N (k + 1) p Ω}
    (hv : topSeminorm ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis (k + 1) p Ω volume v = 0) :
    ∃ q ∈ restrictTotalDegree (Fin N) ℝ k,
      fn v =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
        fun x ↦ eval (fun i ↦ x i) q := by
  obtain ⟨q, hq, hvq⟩ := exists_mvPolynomial_ae_eq_of_forall_weakDeriv_eq_zero hΩ (k + 1) v
    ((topSeminorm_eq_zero_iff v).1 hv)
  refine ⟨q, mem_restrictTotalDegree_of_forall_degree_lt hq, hvq.trans ?_⟩
  exact Eventually.of_forall fun x ↦ evalBasis_basisFun q x

/-- Let $\Omega \subseteq \mathbb{R}^N$ be a $W^{1,p}$-extension domain of finite measure, let
$k \ge 0$ and $1 \le p < \infty$. Let $f_j$, for $j$ in a finite set $J$, be seminorms on
$W^{k+1,p}(\Omega)$ such that

(H1) $f_j(v) \le c \|v\|_{k+1,p,\Omega}$ for all $j$ and $v$, and

(H2)′ if $|v|_{k+1,p,\Omega} = 0$ and $f_j(v) = 0$ for all $j$, then $v = 0$.

Then there is $C > 0$ such that for all $v \in W^{k+1,p}(\Omega)$,
$$\|v\|_{k+1,p,\Omega} \le C \Bigl(|v|_{k+1,p,\Omega} + \sum_j f_j(v)\Bigr).$$
This is Theorem 7.3.13 of [han2009theoretical] for the norm (7.3.3). With
`SobolevMultiIndex.topSeminorm_add_sum_le_norm` it gives the equivalence of the norm (7.3.3)
with $\|\cdot\|_{k+1,p,\Omega}$.

The book takes a bounded Lipschitz domain and the order $k \ge 1$; here the order is written
$k + 1$. The extension domain is `IsSobolevExtensionDomain N p Ω`. The proof specializes
`SobolevMultiIndex.exists_norm_le_topSeminorm_add_sum_of_isCompactEmbedding`. -/
theorem SobolevEuclidean.exists_norm_le_topSeminorm_add_sum_of_forall_eq_zero
    (hΩ : IsSobolevExtensionDomain N p Ω)
    (hμ : volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ≠ ⊤) {J : Type*} [Fintype J]
    (f : J → Seminorm ℝ (SobolevEuclidean N (k + 1) p Ω)) {c : ℝ} (hf : ∀ j v, f j v ≤ c * ‖v‖)
    (h2 : ∀ v : SobolevEuclidean N (k + 1) p Ω,
      topSeminorm ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis (k + 1) p Ω volume v = 0 →
        (∀ j, f j v = 0) → v = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : SobolevEuclidean N (k + 1) p Ω,
      ‖v‖ ≤ C * (topSeminorm ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis (k + 1) p Ω volume v
        + ∑ j, f j v) :=
  exists_norm_le_topSeminorm_add_sum_of_isCompactEmbedding (by simp)
    (SobolevEuclidean.isCompactEmbedding_toLowerOrderL_of_isSobolevExtensionDomain hΩ hμ k) f
    (fun j ↦ (f j).continuous_of_forall_le_mul_norm (hf j)) h2

/-- Let $\Omega \subseteq \mathbb{R}^N$ be a connected $W^{1,p}$-extension domain of finite measure,
let $k \ge 0$ and $1 \le p < \infty$. Let $f_j$, for $j$ in a finite set $J$, be seminorms on
$W^{k+1,p}(\Omega)$ such that

(H1) $f_j(v) \le c \|v\|_{k+1,p,\Omega}$ for all $j$ and $v$, and

(H2) if $v \in \mathbb{P}_k(\Omega)$ and $f_j(v) = 0$ for all $j$, then $v = 0$.

Then there is $C > 0$ such that for all $v \in W^{k+1,p}(\Omega)$,
$$\|v\|_{k+1,p,\Omega} \le C \Bigl(|v|_{k+1,p,\Omega} + \sum_j f_j(v)\Bigr).$$
This is Theorem 7.3.12 of [han2009theoretical] for the norm (7.3.3).

The book takes a Lipschitz domain, the order $k \ge 1$ and the polynomials $\mathbb{P}_{k-1}$;
here the order is written $k + 1$, and $\mathbb{P}_k$ is
`MvPolynomial.restrictTotalDegree (Fin N) ℝ k`. The statement $v \in \mathbb{P}_k(\Omega)$ means
that $v$ agrees almost everywhere on $\Omega$ with a polynomial of total degree at most $k$.
(H2) gives (H2)′ of Theorem 7.3.13, because $|v|_{k+1,p,\Omega} = 0$ implies
$v \in \mathbb{P}_k(\Omega)$ on a connected $\Omega$
(`SobolevEuclidean.exists_mem_restrictTotalDegree_ae_eq_of_topSeminorm_eq_zero`). -/
theorem SobolevEuclidean.exists_norm_le_topSeminorm_add_sum_of_isPreconnected
    (hΩ : IsSobolevExtensionDomain N p Ω)
    (hμ : volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ≠ ⊤)
    (hΩc : IsPreconnected (Ω : Set (EuclideanSpace ℝ (Fin N)))) {J : Type*} [Fintype J]
    (f : J → Seminorm ℝ (SobolevEuclidean N (k + 1) p Ω)) {c : ℝ} (hf : ∀ j v, f j v ≤ c * ‖v‖)
    (h2 : ∀ v : SobolevEuclidean N (k + 1) p Ω,
      (∃ q ∈ restrictTotalDegree (Fin N) ℝ k, fn v
        =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] fun x ↦ eval (fun i ↦ x i) q) →
        (∀ j, f j v = 0) → v = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : SobolevEuclidean N (k + 1) p Ω,
      ‖v‖ ≤ C * (topSeminorm ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis (k + 1) p Ω volume v
        + ∑ j, f j v) :=
  SobolevEuclidean.exists_norm_le_topSeminorm_add_sum_of_forall_eq_zero hΩ hμ f hf fun v hv hfv ↦
    h2 v (SobolevEuclidean.exists_mem_restrictTotalDegree_ae_eq_of_topSeminorm_eq_zero hΩc hv) hfv

/-- Let $\Omega \subseteq \mathbb{R}^N$ be a connected $W^{1,p}$-extension domain of finite measure,
let $k \ge 0$ and $1 \le p < \infty$. Let $\ell_j$, for $j$ in a finite set $J$, be bounded
linear functionals on $W^{k+1,p}(\Omega)$ such that if $v \in \mathbb{P}_k(\Omega)$ and
$\ell_j(v) = 0$ for all $j$, then $v = 0$. Then there is $C > 0$ such that for all
$v \in W^{k+1,p}(\Omega)$,
$$\|v\|_{k+1,p,\Omega} \le C \Bigl(|v|_{k+1,p,\Omega} + \sum_j |\ell_j(v)|\Bigr).$$
This is Theorem 7.3.12 of [han2009theoretical] with the seminorms $f_j(v) = |\ell_j(v)|$, the
form in which the theorem enters the Bramble–Hilbert lemma and Lemma 8.4.1 of the book.

The order is written $k + 1$, as in
`SobolevEuclidean.exists_norm_le_topSeminorm_add_sum_of_isPreconnected`, which this specializes. -/
theorem SobolevEuclidean.exists_norm_le_topSeminorm_add_sum_abs_of_isPreconnected
    (hΩ : IsSobolevExtensionDomain N p Ω)
    (hμ : volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ≠ ⊤)
    (hΩc : IsPreconnected (Ω : Set (EuclideanSpace ℝ (Fin N)))) {J : Type*} [Fintype J]
    (ℓ : J → SobolevEuclidean N (k + 1) p Ω →L[ℝ] ℝ)
    (h2 : ∀ v : SobolevEuclidean N (k + 1) p Ω,
      (∃ q ∈ restrictTotalDegree (Fin N) ℝ k, fn v
        =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] fun x ↦ eval (fun i ↦ x i) q) →
        (∀ j, ℓ j v = 0) → v = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : SobolevEuclidean N (k + 1) p Ω,
      ‖v‖ ≤ C * (topSeminorm ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis (k + 1) p Ω volume v
        + ∑ j, |ℓ j v|) := by
  have hf : ∀ j v, ((normSeminorm ℝ ℝ).comp (ℓ j).toLinearMap) v ≤ (∑ i, ‖ℓ i‖) * ‖v‖ :=
    fun j v ↦ ((ℓ j).le_opNorm v).trans (mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun i _ ↦ norm_nonneg (ℓ i)) (Finset.mem_univ j)) (norm_nonneg v))
  obtain ⟨C, hC, hle⟩ := SobolevEuclidean.exists_norm_le_topSeminorm_add_sum_of_isPreconnected
    hΩ hμ hΩc (fun j ↦ (normSeminorm ℝ ℝ).comp (ℓ j).toLinearMap) hf fun v hv hℓ ↦
      h2 v hv fun j ↦ by
        simpa only [Seminorm.comp_apply, coe_normSeminorm, ContinuousLinearMap.coe_coe,
          norm_eq_zero] using hℓ j
  refine ⟨C, hC, fun v ↦ ?_⟩
  simpa only [Seminorm.comp_apply, coe_normSeminorm, ContinuousLinearMap.coe_coe,
    Real.norm_eq_abs] using hle v

/-- Let $\Omega \subseteq \mathbb{R}^N$ be a connected $W^{1,p}$-extension domain of finite measure,
let $k \ge 0$ and $1 \le p < \infty$. Let $\ell$ be a bounded linear functional on
$W^{k+1,p}(\Omega)$ such that if $v \in \mathbb{P}_k(\Omega)$ and $\ell(v) = 0$, then $v = 0$.
Then there is $C > 0$ such that for all $v \in W^{k+1,p}(\Omega)$,
$$\|v\|_{k+1,p,\Omega} \le C \bigl(|v|_{k+1,p,\Omega} + |\ell(v)|\bigr).$$
This is Theorem 7.3.12 of [han2009theoretical] with one seminorm $f(v) = |\ell(v)|$, as in the
proof of Lemma 8.4.1 of the book. -/
theorem SobolevEuclidean.exists_norm_le_topSeminorm_add_abs_of_isPreconnected
    (hΩ : IsSobolevExtensionDomain N p Ω)
    (hμ : volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ≠ ⊤)
    (hΩc : IsPreconnected (Ω : Set (EuclideanSpace ℝ (Fin N))))
    (ℓ : SobolevEuclidean N (k + 1) p Ω →L[ℝ] ℝ)
    (h2 : ∀ v : SobolevEuclidean N (k + 1) p Ω,
      (∃ q ∈ restrictTotalDegree (Fin N) ℝ k, fn v
        =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] fun x ↦ eval (fun i ↦ x i) q) →
        ℓ v = 0 → v = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : SobolevEuclidean N (k + 1) p Ω,
      ‖v‖ ≤ C * (topSeminorm ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis (k + 1) p Ω volume v
        + |ℓ v|) := by
  obtain ⟨C, hC, hle⟩ := SobolevEuclidean.exists_norm_le_topSeminorm_add_sum_abs_of_isPreconnected
    hΩ hμ hΩc (fun _ : Unit ↦ ℓ) fun v hv hℓ ↦ h2 v hv (hℓ ())
  exact ⟨C, hC, fun v ↦ by simpa only [Fintype.sum_unique] using hle v⟩

/-- Let $\Omega' \subseteq \Omega$ be open sets and let $v \in W^{k,p}(\Omega)$ with
$|v|_{k,p,\Omega} = 0$. Then the restriction of $v$ to $\Omega'$, as an element of
$W^{k,p}(\Omega')$, also has top-order seminorm zero. -/
theorem SobolevMultiIndex.topSeminorm_restrictL_eq_zero {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [OpensMeasurableSpace E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {ι : Type*} [Fintype ι] [LinearOrder ι] {b : Basis ι ℝ E} {k : ℕ}
    {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω Ω' : Opens E} {μ : Measure E} (h : Ω' ≤ Ω)
    {v : SobolevMultiIndex F b k p Ω μ} (hv : topSeminorm F b k p Ω μ v = 0) :
    topSeminorm F b k p Ω' μ (restrictL F b k p μ h v) = 0 := by
  rw [topSeminorm_eq_zero_iff] at hv ⊢
  intro α
  refine Lp.ext ((weakDeriv_restrictL h v α).trans ?_)
  rw [hv α]
  refine Filter.EventuallyEq.trans (ae_mono (Measure.restrict_mono h le_rfl)
    (Lp.coeFn_zero F p (μ.restrict (Ω : Set E)))) ?_
  exact (Lp.coeFn_zero F p _).symm

/-- Let $\Omega \subseteq \mathbb{R}^N$ be a $W^{1,p}$-extension domain of finite measure, and let
$\Omega = \bigcup_{\lambda \in \Lambda} \Omega_\lambda$ be a union of connected open sets. Let
$k \ge 0$ and $1 \le p < \infty$. Let $f_j$, for $j$ in a finite set $J$, be seminorms on
$W^{k+1,p}(\Omega)$ such that

(H1) $f_j(v) \le c \|v\|_{k+1,p,\Omega}$ for all $j$ and $v$, and

(H2) if $v|_{\Omega_\lambda} \in \mathbb{P}_k(\Omega_\lambda)$ for every $\lambda$ and
$f_j(v) = 0$ for all $j$, then $v = 0$.

Then there is $C > 0$ such that for all $v \in W^{k+1,p}(\Omega)$,
$$\|v\|_{k+1,p,\Omega} \le C \Bigl(|v|_{k+1,p,\Omega} + \sum_j f_j(v)\Bigr).$$
This is Theorem 7.3.14 of [han2009theoretical] for the norm (7.3.3).

The book takes a disjoint union of Lipschitz domains and the order $k \ge 1$. Disjointness is
not needed here, and the index set $\Lambda$ is arbitrary. The order is written $k + 1$. The
condition $v|_{\Omega_\lambda} \in \mathbb{P}_k(\Omega_\lambda)$ means that $v$ agrees almost
everywhere on $\Omega_\lambda$ with a polynomial of total degree at most $k$. -/
theorem SobolevEuclidean.exists_norm_le_topSeminorm_add_sum_of_iSup
    (hΩ : IsSobolevExtensionDomain N p Ω)
    (hμ : volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ≠ ⊤) {Λ : Type*}
    {Ω' : Λ → Opens (EuclideanSpace ℝ (Fin N))} (hΩ' : Ω = ⨆ l, Ω' l)
    (hc : ∀ l, IsPreconnected (Ω' l : Set (EuclideanSpace ℝ (Fin N)))) {J : Type*} [Fintype J]
    (f : J → Seminorm ℝ (SobolevEuclidean N (k + 1) p Ω)) {c : ℝ} (hf : ∀ j v, f j v ≤ c * ‖v‖)
    (h2 : ∀ v : SobolevEuclidean N (k + 1) p Ω,
      (∀ l, ∃ q ∈ restrictTotalDegree (Fin N) ℝ k, fn v
        =ᵐ[volume.restrict (Ω' l : Set (EuclideanSpace ℝ (Fin N)))]
          fun x ↦ eval (fun i ↦ x i) q) →
        (∀ j, f j v = 0) → v = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : SobolevEuclidean N (k + 1) p Ω,
      ‖v‖ ≤ C * (topSeminorm ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis (k + 1) p Ω volume v
        + ∑ j, f j v) := by
  refine SobolevEuclidean.exists_norm_le_topSeminorm_add_sum_of_forall_eq_zero hΩ hμ f hf
    fun v hv hfv ↦ h2 v (fun l ↦ ?_) hfv
  have hle : Ω' l ≤ Ω := hΩ' ▸ le_iSup Ω' l
  obtain ⟨q, hq, hvq⟩ :=
    SobolevEuclidean.exists_mem_restrictTotalDegree_ae_eq_of_topSeminorm_eq_zero (hc l)
      (SobolevMultiIndex.topSeminorm_restrictL_eq_zero hle hv)
  exact ⟨q, hq, (fn_restrictL hle v).symm.trans hvq⟩

/-- Let $\Omega \subseteq \mathbb{R}^N$ be a $W^{1,p}$-extension domain of finite measure, let
$k \ge 0$ and $1 \le p < \infty$. Let $f_j$, for $j$ in a finite set $J$, be seminorms on
$W^{k+1,p}(\Omega)$ with (H1) $f_j(v) \le c \|v\|_{k+1,p,\Omega}$ and (H2)′: if
$|v|_{k+1,p,\Omega} = 0$ and $f_j(v) = 0$ for all $j$, then $v = 0$. Then there is $C > 0$ such
that for all $v \in W^{k+1,p}(\Omega)$,
$$\|v\|_{k+1,p,\Omega} \le C \Bigl(|v|_{k+1,p,\Omega}^p + \sum_j f_j(v)^p\Bigr)^{1/p}.$$
This is Theorem 7.3.13 of [han2009theoretical] for the norm (7.3.4).

The hypotheses are those of
`SobolevEuclidean.exists_norm_le_topSeminorm_add_sum_of_forall_eq_zero`, and the order is
written $k + 1$. -/
theorem SobolevEuclidean.exists_norm_le_lp_topSeminorm_sum_of_forall_eq_zero
    (hΩ : IsSobolevExtensionDomain N p Ω)
    (hμ : volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ≠ ⊤) {J : Type*} [Fintype J]
    (f : J → Seminorm ℝ (SobolevEuclidean N (k + 1) p Ω)) {c : ℝ} (hf : ∀ j v, f j v ≤ c * ‖v‖)
    (h2 : ∀ v : SobolevEuclidean N (k + 1) p Ω,
      topSeminorm ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis (k + 1) p Ω volume v = 0 →
        (∀ j, f j v = 0) → v = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : SobolevEuclidean N (k + 1) p Ω,
      ‖v‖ ≤ C * (topSeminorm ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis (k + 1) p Ω volume v
          ^ (p : ℝ≥0∞).toReal + ∑ j, f j v ^ (p : ℝ≥0∞).toReal) ^ (1 / (p : ℝ≥0∞).toReal) := by
  obtain ⟨C, hC, h⟩ :=
    SobolevEuclidean.exists_norm_le_topSeminorm_add_sum_of_forall_eq_zero hΩ hμ f hf h2
  refine ⟨C * (Fintype.card J + 1), by positivity, fun v ↦ (h v).trans ?_⟩
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (add_le_card_mul_lp_topSeminorm_sum (by simp) f v) hC.le

end Euclidean

/-! ### The top-order seminorm at order one is the gradient norm -/

section OrderOneSeminorm

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ι : Type*} [Fintype ι] [LinearOrder ι] {b : Basis ι ℝ E} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {Ω : Opens E} {μ : Measure E}

/-- The map $i \mapsto e_i$ from $\iota$ to the multi-indices of order exactly one is a bijection.
-/
theorem MultiIndexLE.single_bijective :
    Function.Bijective fun i : ι ↦ (⟨MultiIndexLE.single i, by simp⟩ : MultiIndexEq ι 1) := by
  refine ⟨fun i j h ↦ MultiIndexLE.single_injective (Subtype.mk.inj h), fun α ↦ ?_⟩
  rcases MultiIndexLE.eq_zero_or_exists_eq_single α.1 with h0 | ⟨i, hi⟩
  · have := α.2
    rw [h0] at this
    simp at this
  · exact ⟨i, Subtype.ext hi.symm⟩

namespace SobolevMultiIndex

/-- The top-order seminorm of $W^{1,p}(\Omega)$ is the gradient norm: for $u \in W^{1,p}(\Omega)$,
$$|u|_{1,p,\Omega} = \|\nabla u\|_{L^p(\Omega)}.$$

The gradient norm is `SobolevMultiIndex.gradNorm`, the $\ell^p$ norm of the tuple
$(\partial_i u)_i$. -/
theorem topSeminorm_one_eq_gradNorm (u : SobolevMultiIndex F b 1 p Ω μ) :
    topSeminorm F b 1 p Ω μ u = gradNorm u := by
  rw [topSeminorm_apply, gradNorm]
  rcases eq_or_ne p ⊤ with rfl | hp
  · rw [PiLp.norm_eq_ciSup, PiLp.norm_eq_ciSup]
    exact ((Equiv.ofBijective _ MultiIndexLE.single_bijective).iSup_comp
      (g := fun α : MultiIndexEq ι 1 ↦ ‖topDeriv u α‖)).symm
  · have hP : 0 < p.toReal :=
      ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne' hp
    rw [PiLp.norm_eq_sum hP, PiLp.norm_eq_sum hP]
    congr 1
    exact (Fintype.sum_bijective _ MultiIndexLE.single_bijective _ _ fun i ↦ rfl).symm

end SobolevMultiIndex

end OrderOneSeminorm

section Conclusion

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ι : Type*} [Fintype ι] [LinearOrder ι] {b : Basis ι ℝ E} {k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {Ω : Opens E} {μ : Measure E}

namespace SobolevMultiIndex

/-- Let $1 \le p < \infty$, and let $f_j$, for $j$ in a finite set $J$, be seminorms on
$W^{k,p}(\Omega)$ with $f_j(v) \le c \|v\|_{k,p,\Omega}$ for all $j$ and $v$. Assume that there
is $C > 0$ with $\|v\|_{k,p,\Omega} \le C (|v|_{k,p,\Omega} + \sum_j f_j(v))$ for all $v$. Then
each of the two quantities
$$|v|_{k,p,\Omega} + \sum_j f_j(v) \quad (7.3.3) \qquad \text{and} \qquad
  \Bigl(|v|_{k,p,\Omega}^p + \sum_j f_j(v)^p\Bigr)^{1/p} \quad (7.3.4)$$
of [han2009theoretical] vanishes only at $v = 0$, and there are $c_1, c_2 > 0$ with $c_1
\|v\|_{k,p,\Omega} \le (\text{quantity}) \le c_2 \|v\|_{k,p,\Omega}$ for all $v$. So both are
norms on $W^{k,p}(\Omega)$ that are equivalent to its norm. -/
theorem norm_equiv_of_exists_norm_le_topSeminorm_add_sum (hp' : p ≠ ⊤) {J : Type*} [Fintype J]
    {f : J → Seminorm ℝ (SobolevMultiIndex F b k p Ω μ)} {c : ℝ} (hf : ∀ j v, f j v ≤ c * ‖v‖)
    (h : ∃ C : ℝ, 0 < C ∧ ∀ v : SobolevMultiIndex F b k p Ω μ,
      ‖v‖ ≤ C * (topSeminorm F b k p Ω μ v + ∑ j, f j v)) :
    ((∀ v, topSeminorm F b k p Ω μ v + ∑ j, f j v = 0 → v = 0) ∧
      ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ v : SobolevMultiIndex F b k p Ω μ,
        c₁ * ‖v‖ ≤ topSeminorm F b k p Ω μ v + ∑ j, f j v ∧
        topSeminorm F b k p Ω μ v + ∑ j, f j v ≤ c₂ * ‖v‖) ∧
    ((∀ v, (topSeminorm F b k p Ω μ v ^ p.toReal + ∑ j, f j v ^ p.toReal) ^ (1 / p.toReal) = 0 →
        v = 0) ∧
      ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ v : SobolevMultiIndex F b k p Ω μ,
        c₁ * ‖v‖ ≤ (topSeminorm F b k p Ω μ v ^ p.toReal + ∑ j, f j v ^ p.toReal) ^ (1 / p.toReal) ∧
        (topSeminorm F b k p Ω μ v ^ p.toReal + ∑ j, f j v ^ p.toReal) ^ (1 / p.toReal)
          ≤ c₂ * ‖v‖) := by
  obtain ⟨C, hC, hle⟩ := h
  have hf' : ∀ j v, f j v ≤ max c 0 * ‖v‖ := fun j v ↦
    (hf j v).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  have hupper := fun v ↦ topSeminorm_add_sum_le_norm f hf' v
  have hc₂ : (0 : ℝ) < 1 + Fintype.card J * max c 0 := by positivity
  have hlow : ∀ v, C⁻¹ * ‖v‖ ≤ topSeminorm F b k p Ω μ v + ∑ j, f j v := fun v ↦ by
    rw [inv_mul_le_iff₀ hC]
    exact hle v
  have hJ : (0 : ℝ) < Fintype.card J + 1 := by positivity
  refine ⟨⟨fun v hv ↦ ?_, C⁻¹, 1 + Fintype.card J * max c 0, inv_pos.2 hC, hc₂, fun v ↦
    ⟨hlow v, hupper v⟩⟩, ⟨fun v hv ↦ ?_, C⁻¹ * ((Fintype.card J : ℝ) + 1)⁻¹,
      1 + Fintype.card J * max c 0, mul_pos (inv_pos.2 hC) (inv_pos.2 hJ), hc₂,
      fun v ↦ ⟨?_, ?_⟩⟩⟩
  · have := hlow v
    rw [hv] at this
    exact norm_eq_zero.1 (le_antisymm (by nlinarith [norm_nonneg v, inv_pos.2 hC])
      (norm_nonneg _))
  · have h1 := add_le_card_mul_lp_topSeminorm_sum hp' f v
    rw [hv, mul_zero] at h1
    have h2 := (hle v).trans (mul_le_mul_of_nonneg_left h1 hC.le)
    rw [mul_zero] at h2
    exact norm_eq_zero.1 (le_antisymm h2 (norm_nonneg _))
  · have h1 := add_le_card_mul_lp_topSeminorm_sum hp' f v
    rw [mul_assoc, inv_mul_le_iff₀ hC, inv_mul_le_iff₀ hJ, mul_left_comm]
    exact (hle v).trans (mul_le_mul_of_nonneg_left h1 hC.le)
  · exact (lp_topSeminorm_sum_le_add hp' f v).trans (hupper v)

end SobolevMultiIndex

end Conclusion

/-!
### The quotient norm

The norm of $V/\mathbb{R}w$ at a class $[v]$ is $\inf_\alpha \|v + \alpha w\|$. A seminorm
$N \le \|\cdot\|$ with $N(w) = 0$ is bounded by it. The quotient norm is bounded by $C N(v)$ when
$\|v\| \le C (N(v) + |\ell(v)|)$ for a linear functional $\ell$ with $\ell(w) \ne 0$. This is Lemma
8.4.1 of [han2009theoretical], with $V = H^1(\Omega)$, $w = 1$, $N = |\cdot|_{1,\Omega}$ and
$\ell(v) = \int_\Omega v$.
-/

section Quotient

namespace Seminorm

/-- Let $N$ be a seminorm on a real vector space $V$ and let $w \in V$ with $N(w) = 0$. Then
$N(v + \alpha w) = N(v)$ for all $v \in V$ and $\alpha \in \mathbb{R}$. -/
theorem apply_add_smul_of_eq_zero {V : Type*} [AddCommGroup V] [Module ℝ V]
    (N : Seminorm ℝ V) {w : V} (hw : N w = 0) (v : V) (α : ℝ) : N (v + α • w) = N v := by
  refine le_antisymm ?_ ?_
  · calc N (v + α • w) ≤ N v + N (α • w) := map_add_le_add _ _ _
      _ = N v := by rw [map_smul_eq_mul, hw, mul_zero, add_zero]
  · calc N v = N ((v + α • w) + (-α) • w) := by
          rw [add_assoc, ← add_smul, add_neg_cancel, zero_smul, add_zero]
      _ ≤ N (v + α • w) + N ((-α) • w) := map_add_le_add _ _ _
      _ = N (v + α • w) := by rw [map_smul_eq_mul, hw, mul_zero, add_zero]

variable {V : Type*} [SeminormedAddCommGroup V] [NormedSpace ℝ V]

/-- Let $V$ be a real seminormed space, let $N$ be a seminorm on $V$ with $N(v) \le \|v\|$ for all
$v$, and let $w \in V$ with $N(w) = 0$. Then for all $v \in V$,
$$N(v) \le \inf_{\alpha \in \mathbb{R}} \|v + \alpha w\|.$$
This is the lower bound of Lemma 8.4.1 of [han2009theoretical]. -/
theorem le_ciInf_norm_add_smul (N : Seminorm ℝ V) (hN : ∀ v, N v ≤ ‖v‖) {w : V} (hw : N w = 0)
    (v : V) : N v ≤ ⨅ α : ℝ, ‖v + α • w‖ :=
  le_ciInf fun α ↦ (N.apply_add_smul_of_eq_zero hw v α).symm.trans_le (hN _)

/-- Let $V$ be a real seminormed space, let $N$ be a seminorm on $V$, let $w \in V$ with $N(w) = 0$,
and let $\ell$ be a bounded linear functional on $V$ with $\ell(w) \ne 0$. Assume that
$\|v\| \le C (N(v) + |\ell(v)|)$ for all $v$. Then for all $v \in V$,
$$\inf_{\alpha \in \mathbb{R}} \|v + \alpha w\| \le C N(v).$$
This is the upper bound of Lemma 8.4.1 of [han2009theoretical].

The representative $v + \alpha w$ with $\alpha = -\ell(v)/\ell(w)$ has $\ell(v + \alpha w) = 0$. -/
theorem ciInf_norm_add_smul_le_mul (N : Seminorm ℝ V) (ℓ : V →L[ℝ] ℝ) {w : V} (hw : N w = 0)
    (hℓw : ℓ w ≠ 0) {C : ℝ} (hle : ∀ v, ‖v‖ ≤ C * (N v + |ℓ v|)) (v : V) :
    ⨅ α : ℝ, ‖v + α • w‖ ≤ C * N v := by
  have hbdd : BddBelow (Set.range fun α : ℝ ↦ ‖v + α • w‖) :=
    ⟨0, by rintro _ ⟨α, rfl⟩; exact norm_nonneg _⟩
  have hℓ0 : ℓ (v + (-(ℓ v) / ℓ w) • w) = 0 := by
    rw [map_add, map_smul, smul_eq_mul, div_mul_cancel₀ _ hℓw, add_neg_cancel]
  calc ⨅ α : ℝ, ‖v + α • w‖ ≤ ‖v + (-(ℓ v) / ℓ w) • w‖ := ciInf_le hbdd _
    _ ≤ C * (N (v + (-(ℓ v) / ℓ w) • w) + |ℓ (v + (-(ℓ v) / ℓ w) • w)|) := hle _
    _ = C * N v := by rw [hℓ0, abs_zero, add_zero, N.apply_add_smul_of_eq_zero hw]

end Seminorm

end Quotient

/-! ### The quotient by a finite-dimensional subspace -/

section QuotientSubspace

namespace Seminorm

variable {V : Type*} [SeminormedAddCommGroup V] [NormedSpace ℝ V]

/-- Let $N$ be a seminorm on a real seminormed space $V$ and let $q \in V$ with $N(q) = 0$. Then
$N(v + q) = N(v)$ for all $v \in V$. -/
theorem apply_add_of_eq_zero (N : Seminorm ℝ V) {q : V} (hq : N q = 0) (v : V) :
    N (v + q) = N v := by
  simpa using N.apply_add_smul_of_eq_zero hq v 1

/-- Let $V$ be a real seminormed space, let $N$ be a seminorm on $V$ with $N(v) \le \|v\|$ for all
$v$, and let $P$ be a subspace of $V$ on which $N$ vanishes. Then for all $v \in V$, $N$ is
bounded by the quotient norm of $V/P$:
$$N(v) \le \inf_{q \in P} \|v + q\|.$$
This is the first inequality of the proof of Theorem 7.3.17 of [han2009theoretical]. -/
theorem le_ciInf_norm_add (N : Seminorm ℝ V) (hN : ∀ v, N v ≤ ‖v‖) (P : Submodule ℝ V)
    (hP : ∀ q ∈ P, N q = 0) (v : V) : N v ≤ ⨅ q : P, ‖v + q‖ :=
  le_ciInf fun q ↦ (N.apply_add_of_eq_zero (hP q q.2) v).symm.trans_le (hN _)

/-- Let $V$ be a real seminormed space, let $P$ be a subspace of $V$ with a finite basis
$(b_j)_{j \in J}$, and let $N$ be a seminorm on $V$ that vanishes on $P$. Let $\ell_j$, for
$j \in J$, be bounded linear functionals on $V$ that extend the coordinate functionals of the
basis $(b_j)$. Assume that $\|v\| \le C (N(v) + \sum_j |\ell_j(v)|)$ for all $v$. Then for all
$v \in V$, the quotient norm of $V/P$ is bounded by $N$:
$$\inf_{q \in P} \|v + q\| \le C N(v).$$
This is the last step of the first proof of Theorem 7.3.17 of [han2009theoretical], after the
coordinate functionals have been extended by the Hahn–Banach theorem.

The representative $v + q$ with $q = -\sum_j \ell_j(v) b_j$ has $\ell_j(v + q) = 0$ for all $j$. -/
theorem ciInf_norm_add_le_mul (N : Seminorm ℝ V) (P : Submodule ℝ V) (hP : ∀ q ∈ P, N q = 0)
    {J : Type*} [Fintype J] (b : Basis J ℝ P) {ℓ : J → V →L[ℝ] ℝ}
    (hℓ : ∀ j (x : P), ℓ j x = b.coord j x) {C : ℝ}
    (hle : ∀ v, ‖v‖ ≤ C * (N v + ∑ j, |ℓ j v|)) (v : V) : ⨅ q : P, ‖v + q‖ ≤ C * N v := by
  have hbdd : BddBelow (Set.range fun q : P ↦ ‖v + q‖) :=
    ⟨0, by rintro _ ⟨q, rfl⟩; exact norm_nonneg _⟩
  obtain ⟨q, hq⟩ : ∃ q : P, q = -∑ j, ℓ j v • b j := ⟨_, rfl⟩
  have hℓ0 : ∀ i, ℓ i (v + q) = 0 := fun i ↦ by
    rw [map_add, hℓ i q, Basis.coord_apply, hq, map_neg, Finsupp.neg_apply, Basis.repr_sum_self,
      add_neg_cancel]
  calc ⨅ q : P, ‖v + q‖ ≤ ‖v + q‖ := ciInf_le hbdd q
    _ ≤ C * (N (v + q) + ∑ j, |ℓ j (v + q)|) := hle _
    _ = C * N v := by
      simp only [hℓ0, abs_zero, Finset.sum_const_zero, add_zero,
        N.apply_add_of_eq_zero (hP q q.2)]

end Seminorm

namespace Submodule

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Let $V$ be a real normed space and let $P$ be a finite-dimensional subspace with a basis
$(b_j)_{j \in J}$. Then the coordinate functionals of the basis extend to bounded linear
functionals $\ell_j$ on $V$: $\ell_j(x) = b_j^*(x)$ for all $x \in P$. This follows from the
Hahn–Banach theorem, and it gives the extended functionals of the first proof of Theorem 7.3.17
of [han2009theoretical]. -/
theorem exists_continuousLinearMap_forall_apply_eq_coord (P : Submodule ℝ V)
    [FiniteDimensional ℝ P] {J : Type*} (b : Basis J ℝ P) :
    ∃ ℓ : J → V →L[ℝ] ℝ, ∀ j (x : P), ℓ j x = b.coord j x := by
  have h : ∀ j, ∃ g : V →L[ℝ] ℝ, ∀ x : P, g x = b.coord j x := fun j ↦
    (exists_extension_norm_eq P (LinearMap.toContinuousLinearMap (b.coord j))).imp
      fun g hg x ↦ hg.1 x
  choose ℓ hℓ using h
  exact ⟨ℓ, hℓ⟩

/-- Let $P$ be a subspace of a real normed space $V$ with a basis $(b_j)_{j \in J}$, and let
$\ell_j$ be linear functionals on $V$ that extend the coordinate functionals of this basis. If
$q \in P$ and $\ell_j(q) = 0$ for all $j$, then $q = 0$. -/
theorem eq_zero_of_forall_apply_eq_zero {P : Submodule ℝ V} {J : Type*} (b : Basis J ℝ P)
    {ℓ : J → V →L[ℝ] ℝ} (hℓ : ∀ j (x : P), ℓ j x = b.coord j x) {q : V} (hq : q ∈ P)
    (h : ∀ j, ℓ j q = 0) : q = 0 := by
  have : (⟨q, hq⟩ : P) = 0 :=
    b.forall_coord_eq_zero_iff.1 fun j ↦ (hℓ j ⟨q, hq⟩).symm.trans (h j)
  exact congrArg Subtype.val this

end Submodule

end QuotientSubspace

/-! ### Higher derivatives of polynomial functions -/

section PolynomialDeriv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*} [Fintype ι]

namespace MvPolynomial

omit [Fintype ι] in
/-- The monomials of $\partial_i q$ come from those of $q$: if $m$ is in the support of
$\partial_i q$, then $m + e_i$ is in the support of $q$. -/
theorem add_single_mem_support_of_mem_support_pderiv {q : MvPolynomial ι ℝ} {i : ι}
    {m : ι →₀ ℕ} (hm : m ∈ (pderiv i q).support) : m + Finsupp.single i 1 ∈ q.support := by
  rw [mem_support_iff] at hm ⊢
  rw [coeff_pderiv] at hm
  exact left_ne_zero_of_mul hm

omit [Fintype ι] in
/-- If every monomial of $q$ has degree at most $k + 1$, then every monomial of $\partial_i q$ has
degree at most $k$. -/
theorem degree_le_of_mem_support_pderiv {q : MvPolynomial ι ℝ} {k : ℕ}
    (hq : ∀ m ∈ q.support, m.degree ≤ k + 1) {i : ι} {m : ι →₀ ℕ}
    (hm : m ∈ (pderiv i q).support) : m.degree ≤ k := by
  have := hq _ (add_single_mem_support_of_mem_support_pderiv hm)
  rw [map_add, Finsupp.degree_single] at this
  omega

variable (b : Basis ι ℝ E)

/-- The derivative of the polynomial function $q \circ b^{-1}$ (`MvPolynomial.evalBasis b q`), as a
function of the point:
$$D(q \circ b^{-1})(x) = \sum_i (\partial_i q \circ b^{-1})(x) \, b_i^*,$$
where $b_i^*$ is the coordinate functional of the basis vector $b_i$. -/
theorem fderiv_evalBasis (q : MvPolynomial ι ℝ) :
    fderiv ℝ (evalBasis b q) = fun x ↦ ∑ i, evalBasis b (pderiv i q) x •
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i).comp
        (b.equivFunL : E →L[ℝ] (ι → ℝ)) := by
  funext x
  rw [(hasFDerivAt_evalBasis b q x).fderiv, ContinuousLinearMap.finsetSum_comp]
  simp only [ContinuousLinearMap.smul_comp, evalBasis]

omit [Fintype ι] in
/-- Let $g : E \to \mathbb{R}$ be smooth with $D^n g = 0$, and let $c$ be a vector of a real normed
space. Then the function $y \mapsto g(y) c$ also has $n$-th derivative zero. -/
theorem _root_.iteratedFDeriv_smul_const_eq_zero {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {g : E → ℝ} {n : ℕ} (hg : ContDiff ℝ ∞ g)
    (h : iteratedFDeriv ℝ n g = 0) (c : F) : iteratedFDeriv ℝ n (fun y ↦ g y • c) = 0 := by
  have hgc : (fun y ↦ g y • c) = (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) c) ∘ g := by
    funext y
    simp
  rw [hgc]
  funext x
  rw [ContinuousLinearMap.iteratedFDeriv_comp_left _ hg.contDiffAt (by simp), h]
  ext m
  simp

/-- Let $q$ be a polynomial all of whose monomials have degree at most $k$. Then the $(k+1)$-st
derivative of the polynomial function $q \circ b^{-1}$ (`MvPolynomial.evalBasis b q`) vanishes
identically. -/
theorem iteratedFDeriv_evalBasis_eq_zero {k : ℕ} :
    ∀ q : MvPolynomial ι ℝ, (∀ m ∈ q.support, m.degree ≤ k) →
      iteratedFDeriv ℝ (k + 1) (evalBasis b q) = 0 := by
  induction k with
  | zero =>
    intro q hq
    have hdeg : q.totalDegree ≤ 0 := (mem_restrictTotalDegree _ _ _).1
      (mem_restrictTotalDegree_of_forall_degree_lt fun m hm ↦ Nat.lt_succ_of_le (hq m hm))
    have hqC : q = C (q.coeff 0) := totalDegree_eq_zero_iff_eq_C.1 (Nat.le_zero.1 hdeg)
    have hconst : evalBasis b q = fun _ ↦ q.coeff 0 := by
      funext x
      conv_lhs => rw [hqC]
      exact evalBasis_C b _ x
    rw [hconst]
    exact iteratedFDeriv_succ_const 0 _
  | succ k ih =>
    intro q hq
    have hd : ∀ i, ∀ m ∈ (pderiv i q).support, m.degree ≤ k := fun i m hm ↦
      degree_le_of_mem_support_pderiv hq hm
    have hf0 : iteratedFDeriv ℝ (k + 1) (fun y ↦ fderiv ℝ (evalBasis b q) y) = 0 := by
      simp only [fderiv_evalBasis]
      rw [iteratedFDeriv_sum (f := fun i y ↦ evalBasis b (pderiv i q) y •
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i).comp
          (b.equivFunL : E →L[ℝ] (ι → ℝ)))
        fun i _ ↦ ((contDiff_evalBasis b _).smul contDiff_const).of_le (by simp)]
      exact Finset.sum_eq_zero fun i _ ↦
        iteratedFDeriv_smul_const_eq_zero (contDiff_evalBasis b _) (ih _ (hd i)) _
    funext x
    rw [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply, hf0, Pi.zero_apply, map_zero,
      Pi.zero_apply]

/-- Let $q$ be a polynomial all of whose monomials have degree at most $k$, and let $n \ge k + 1$.
Then the $n$-th derivative of the polynomial function $q \circ b^{-1}$
(`MvPolynomial.evalBasis b q`) vanishes identically. -/
theorem iteratedFDeriv_evalBasis_eq_zero_of_le {k : ℕ} {q : MvPolynomial ι ℝ}
    (hq : ∀ m ∈ q.support, m.degree ≤ k) {n : ℕ} (hn : k + 1 ≤ n) :
    iteratedFDeriv ℝ n (evalBasis b q) = 0 := by
  induction n, hn using Nat.le_induction with
  | base => exact iteratedFDeriv_evalBasis_eq_zero b q hq
  | succ n _ ih =>
    rw [iteratedFDeriv_succ_eq_comp_left, ih, fderiv_zero]
    funext x
    simp

end MvPolynomial

end PolynomialDeriv

/-! ### The top seminorm vanishes on polynomials -/

section TopPolynomial

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] {ι : Type*} [Fintype ι] [LinearOrder ι] {b : Basis ι ℝ E} {k : ℕ}
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens E} {μ : Measure E}

namespace SobolevMultiIndex

open MvPolynomial

/-- Let $E$ be finite-dimensional with a Haar measure $\mu$, let $u \in W^{k+1,p}(\Omega)$ be
real-valued, and let $q$ be a polynomial all of whose monomials have degree at most $k$. If
$u = q \circ b^{-1}$ almost everywhere on $\Omega$, then $|u|_{k+1,p,\Omega} = 0$: the weak
derivatives of $u$ of order $k + 1$ vanish. -/
theorem topSeminorm_eq_zero_of_fn_ae_eq_evalBasis [FiniteDimensional ℝ E] [BorelSpace E]
    [μ.IsAddHaarMeasure] (u : SobolevMultiIndex ℝ b (k + 1) p Ω μ) {q : MvPolynomial ι ℝ}
    (hq : ∀ m ∈ q.support, m.degree ≤ k)
    (hu : fn u =ᵐ[μ.restrict (Ω : Set E)] evalBasis b q) :
    topSeminorm ℝ b (k + 1) p Ω μ u = 0 := by
  rw [topSeminorm_eq_zero_iff]
  intro α
  have h := weakDeriv_ae_eq_iteratedFDeriv_of_fn_ae_eq u (contDiff_evalBasis b q) hu α.1
  rw [iteratedFDeriv_evalBasis_eq_zero_of_le b hq α.2.ge] at h
  simp only [Pi.zero_apply, zero_apply] at h
  exact Lp.ext (h.trans (Lp.coeFn_zero ℝ p _).symm)

end SobolevMultiIndex

end TopPolynomial

/-!
### The polynomials of degree at most $k$ inside $W^{k+1,p}(\Omega)$, and the Sobolev quotient
-/

section SobolevQuotient

open MvPolynomial SobolevMultiIndex

variable {N : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens (EuclideanSpace ℝ (Fin N))} {k : ℕ}

namespace SobolevEuclidean

omit [Fact (1 ≤ p)] in
/-- Let $\Omega \subseteq \mathbb{R}^N$ be a bounded open set and let $q$ be a polynomial in $N$
variables. Then there is $u \in W^{k,p}(\Omega)$ with $u(x) = q(x)$ for almost every
$x \in \Omega$. -/
theorem exists_fn_ae_eq_eval (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin N))))
    (q : MvPolynomial (Fin N) ℝ) :
    ∃ u : SobolevEuclidean N k p Ω,
      fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
        fun x ↦ eval (fun i ↦ x i) q := by
  have h : (fun x : EuclideanSpace ℝ (Fin N) ↦ eval (fun i ↦ x i) q)
      = evalBasis (EuclideanSpace.basisFun (Fin N) ℝ).toBasis q :=
    funext fun x ↦ (evalBasis_basisFun q x).symm
  rw [h]
  exact exists_fn_ae_eq_of_contDiff hb (contDiff_evalBasis _ q)

/-- The polynomial $q$ as an element of $W^{k,p}(\Omega)$, for a bounded open set
$\Omega \subseteq \mathbb{R}^N$: an element whose function is $x \mapsto q(x)$ almost everywhere
on $\Omega$.

The element is chosen by `SobolevEuclidean.exists_fn_ae_eq_eval`. Its function is
`SobolevEuclidean.fn_ofPolynomial`. -/
def ofPolynomial (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin N))))
    (q : MvPolynomial (Fin N) ℝ) : SobolevEuclidean N k p Ω :=
  (exists_fn_ae_eq_eval (k := k) (p := p) hb q).choose

omit [Fact (1 ≤ p)] in
/-- The function of `SobolevEuclidean.ofPolynomial hb q` is $x \mapsto q(x)$ almost everywhere on
$\Omega$. -/
theorem fn_ofPolynomial (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin N))))
    (q : MvPolynomial (Fin N) ℝ) :
    fn (ofPolynomial (k := k) (p := p) hb q)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] fun x ↦ eval (fun i ↦ x i) q :=
  (exists_fn_ae_eq_eval (k := k) (p := p) hb q).choose_spec

omit [Fact (1 ≤ p)] in
/-- The map `SobolevEuclidean.ofPolynomial` is additive: the element of $q + r$ is the sum of the
elements of $q$ and $r$. The reason is that an element of $W^{k,p}(\Omega)$ is determined by its
function. -/
theorem ofPolynomial_add (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin N))))
    (q r : MvPolynomial (Fin N) ℝ) :
    ofPolynomial (k := k) (p := p) hb (q + r)
      = ofPolynomial (k := k) (p := p) hb q + ofPolynomial (k := k) (p := p) hb r :=
  ext_of_fn_ae_eq <| by
    filter_upwards [fn_ofPolynomial (k := k) (p := p) hb (q + r),
      fn_ofPolynomial (k := k) (p := p) hb q, fn_ofPolynomial (k := k) (p := p) hb r,
      fn_add (ofPolynomial (k := k) (p := p) hb q) (ofPolynomial (k := k) (p := p) hb r)]
      with x h1 h2 h3 h4
    rw [h1, h4, Pi.add_apply, h2, h3, map_add]

omit [Fact (1 ≤ p)] in
/-- The map `SobolevEuclidean.ofPolynomial` is homogeneous: the element of $cq$ is $c$ times the
element of $q$. -/
theorem ofPolynomial_smul (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin N))))
    (c : ℝ) (q : MvPolynomial (Fin N) ℝ) :
    ofPolynomial (k := k) (p := p) hb (c • q) = c • ofPolynomial (k := k) (p := p) hb q :=
  ext_of_fn_ae_eq <| by
    filter_upwards [fn_ofPolynomial (k := k) (p := p) hb (c • q),
      fn_ofPolynomial (k := k) (p := p) hb q,
      fn_smul c (ofPolynomial (k := k) (p := p) hb q)] with x h1 h2 h3
    rw [h1, h3, Pi.smul_apply, h2, smul_eval, smul_eq_mul]

/-- The linear map from $\mathbb{P}_k$ to $W^{k+1,p}(\Omega)$, for a bounded open set
$\Omega \subseteq \mathbb{R}^N$, that sends a polynomial of total degree at most $k$ to its
polynomial function on $\Omega$.

The domain $\mathbb{P}_k$ is `MvPolynomial.restrictTotalDegree (Fin N) ℝ k`. -/
def polynomialToSobolevₗ (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin N)))) :
    restrictTotalDegree (Fin N) ℝ k →ₗ[ℝ] SobolevEuclidean N (k + 1) p Ω where
  toFun q := ofPolynomial (k := k + 1) (p := p) hb q.1
  map_add' q r := ofPolynomial_add (k := k + 1) (p := p) hb q.1 r.1
  map_smul' c q := ofPolynomial_smul (k := k + 1) (p := p) hb c q.1

/-- The subspace $\mathbb{P}_k(\Omega)$ of $W^{k+1,p}(\Omega)$, for a bounded open set
$\Omega \subseteq \mathbb{R}^N$: the elements whose function agrees almost everywhere on
$\Omega$ with a polynomial of total degree at most $k$. The quotient
$W^{k+1,p}(\Omega)/\mathbb{P}_k(\Omega)$ of §7.3.6 of [han2009theoretical] is the quotient by
this subspace.

The subspace is the range of `SobolevEuclidean.polynomialToSobolevₗ`. Membership is
`SobolevEuclidean.mem_polynomialSubmodule_iff`. -/
def polynomialSubmodule (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin N)))) :
    Submodule ℝ (SobolevEuclidean N (k + 1) p Ω) :=
  LinearMap.range (polynomialToSobolevₗ (k := k) (p := p) hb)

/-- The subspace $\mathbb{P}_k(\Omega)$ of $W^{k+1,p}(\Omega)$ is finite-dimensional, as the image
of the finite-dimensional space $\mathbb{P}_k$. -/
instance instFiniteDimensionalPolynomialSubmodule
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin N)))) :
    FiniteDimensional ℝ (polynomialSubmodule (k := k) (p := p) hb) :=
  Module.Finite.range _

omit [Fact (1 ≤ p)] in
/-- Let $\Omega \subseteq \mathbb{R}^N$ be a bounded open set. An element $u$ of $W^{k+1,p}(\Omega)$
lies in $\mathbb{P}_k(\Omega)$ if and only if there is a polynomial $q$ of total degree at most
$k$ with $u(x) = q(x)$ for almost every $x \in \Omega$. -/
theorem mem_polynomialSubmodule_iff
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin N))))
    {u : SobolevEuclidean N (k + 1) p Ω} :
    u ∈ polynomialSubmodule hb ↔ ∃ q ∈ restrictTotalDegree (Fin N) ℝ k,
      fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
        fun x ↦ eval (fun i ↦ x i) q := by
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨q.1, q.2, fn_ofPolynomial (k := k + 1) (p := p) hb q.1⟩
  · rintro ⟨q, hq, hu⟩
    exact ⟨⟨q, hq⟩,
      ext_of_fn_ae_eq ((fn_ofPolynomial (k := k + 1) (p := p) hb q).trans hu.symm)⟩

/-- Let $\Omega \subseteq \mathbb{R}^N$ be a bounded open set. If $u \in \mathbb{P}_k(\Omega)$, then
$|u|_{k+1,p,\Omega} = 0$. -/
theorem topSeminorm_eq_zero_of_mem_polynomialSubmodule
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin N))))
    {u : SobolevEuclidean N (k + 1) p Ω} (hu : u ∈ polynomialSubmodule hb) :
    topSeminorm ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis (k + 1) p Ω volume u = 0 := by
  obtain ⟨q, hq, hu⟩ := (mem_polynomialSubmodule_iff hb).1 hu
  refine topSeminorm_eq_zero_of_fn_ae_eq_evalBasis u (q := q) (fun m hm ↦ ?_)
    (hu.trans (Eventually.of_forall fun x ↦ (evalBasis_basisFun q x).symm))
  exact (le_totalDegree hm).trans ((mem_restrictTotalDegree _ _ _).1 hq)

/-- Let $\Omega \subseteq \mathbb{R}^N$ be a bounded open set. The top-order seminorm is constant on
the classes of $W^{k+1,p}(\Omega)/\mathbb{P}_k(\Omega)$: if $q \in \mathbb{P}_k(\Omega)$, then
$|v + q|_{k+1,p,\Omega} = |v|_{k+1,p,\Omega}$. -/
theorem topSeminorm_add_of_mem_polynomialSubmodule
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin N))))
    (v : SobolevEuclidean N (k + 1) p Ω) {q : SobolevEuclidean N (k + 1) p Ω}
    (hq : q ∈ polynomialSubmodule hb) :
    topSeminorm ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis (k + 1) p Ω volume (v + q)
      = topSeminorm ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis (k + 1) p Ω volume v :=
  Seminorm.apply_add_of_eq_zero
    (topSeminorm ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis (k + 1) p Ω volume)
    (topSeminorm_eq_zero_of_mem_polynomialSubmodule hb hq) v

/-- Let $\Omega \subseteq \mathbb{R}^N$ be a bounded open set. The top-order seminorm is bounded by
the quotient norm of $W^{k+1,p}(\Omega)/\mathbb{P}_k(\Omega)$: for all
$v \in W^{k+1,p}(\Omega)$,
$$|v|_{k+1,p,\Omega} \le \inf_{q \in \mathbb{P}_k(\Omega)} \|v + q\|_{k+1,p,\Omega}.$$
This is the first inequality of the proof of Theorem 7.3.17 of [han2009theoretical]. -/
theorem topSeminorm_le_ciInf_norm_add
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin N))))
    (v : SobolevEuclidean N (k + 1) p Ω) :
    topSeminorm ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis (k + 1) p Ω volume v
      ≤ ⨅ q : polynomialSubmodule (k := k) (p := p) hb, ‖v + q‖ :=
  Seminorm.le_ciInf_norm_add (topSeminorm ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis (k + 1) p Ω
    volume) topSeminorm_le_norm (polynomialSubmodule (k := k) (p := p) hb)
    (fun _ hq ↦ topSeminorm_eq_zero_of_mem_polynomialSubmodule hb hq) v

end SobolevEuclidean

end SobolevQuotient

section SobolevQuotientMain

open MvPolynomial SobolevMultiIndex

variable {N : ℕ} {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] {Ω : Opens (EuclideanSpace ℝ (Fin N))} {k : ℕ}

/-- Let $\Omega \subseteq \mathbb{R}^N$ be a connected bounded open set and $1 \le p < \infty$. For
$u \in W^{k+1,p}(\Omega)$, $|u|_{k+1,p,\Omega} = 0$ if and only if $u \in \mathbb{P}_k(\Omega)$.
So the top-order seminorm is a norm on the quotient $W^{k+1,p}(\Omega)/\mathbb{P}_k(\Omega)$, as
Theorem 7.3.17 of [han2009theoretical] states. -/
theorem SobolevEuclidean.topSeminorm_eq_zero_iff_mem_polynomialSubmodule
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin N))))
    (hΩc : IsPreconnected (Ω : Set (EuclideanSpace ℝ (Fin N))))
    {u : SobolevEuclidean N (k + 1) p Ω} :
    topSeminorm ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis (k + 1) p Ω volume u = 0 ↔
      u ∈ SobolevEuclidean.polynomialSubmodule hb :=
  ⟨fun h ↦ (SobolevEuclidean.mem_polynomialSubmodule_iff hb).2
    (SobolevEuclidean.exists_mem_restrictTotalDegree_ae_eq_of_topSeminorm_eq_zero hΩc h),
    SobolevEuclidean.topSeminorm_eq_zero_of_mem_polynomialSubmodule hb⟩

/-- Let $\Omega \subseteq \mathbb{R}^N$ be a connected bounded $W^{1,p}$-extension domain and let
$1 \le p < \infty$. Then there is $C > 0$ such that for all $v \in W^{k+1,p}(\Omega)$,
$$\inf_{q \in \mathbb{P}_k(\Omega)} \|v + q\|_{k+1,p,\Omega} \le C |v|_{k+1,p,\Omega}.$$
This is the inequality (7.3.13) of Theorem 7.3.17 of [han2009theoretical]. With
`SobolevEuclidean.topSeminorm_le_ciInf_norm_add` it gives the equivalence of the quotient norm
of $W^{k+1,p}(\Omega)/\mathbb{P}_k(\Omega)$ with the top-order seminorm.

The book takes a Lipschitz domain. The proof is the book's first proof: the coordinate
functionals of a basis of $\mathbb{P}_k(\Omega)$ extend by the Hahn–Banach theorem to bounded
linear functionals $\ell_j$ on $W^{k+1,p}(\Omega)$, the seminorms $|\ell_j|$ satisfy (H2) of
Theorem 7.3.12, and the representative $v + q$ with $\ell_j(v + q) = 0$ for all $j$ gives the
bound. -/
theorem SobolevEuclidean.exists_ciInf_norm_add_le_mul_topSeminorm
    (hΩ : IsSobolevExtensionDomain N p Ω)
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin N))))
    (hΩc : IsPreconnected (Ω : Set (EuclideanSpace ℝ (Fin N)))) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : SobolevEuclidean N (k + 1) p Ω,
      ⨅ q : SobolevEuclidean.polynomialSubmodule (k := k) (p := p) hb, ‖v + q‖
        ≤ C * topSeminorm ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis (k + 1) p Ω volume v := by
  have hμ : volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ≠ ⊤ :=
    (hb.measure_lt_top (μ := volume)).ne
  obtain ⟨ℓ, hℓ⟩ := (SobolevEuclidean.polynomialSubmodule (k := k) (p := p)
    hb).exists_continuousLinearMap_forall_apply_eq_coord
      (Module.finBasis ℝ (SobolevEuclidean.polynomialSubmodule (k := k) (p := p) hb))
  obtain ⟨C, hC, hle⟩ := SobolevEuclidean.exists_norm_le_topSeminorm_add_sum_abs_of_isPreconnected
    hΩ hμ hΩc ℓ fun v hv h ↦ Submodule.eq_zero_of_forall_apply_eq_zero _ hℓ
      ((SobolevEuclidean.mem_polynomialSubmodule_iff hb).2 hv) h
  refine ⟨C, hC, fun v ↦ ?_⟩
  exact Seminorm.ciInf_norm_add_le_mul
    (topSeminorm ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis (k + 1) p Ω volume)
    (SobolevEuclidean.polynomialSubmodule (k := k) (p := p) hb)
    (fun _ hq ↦ SobolevEuclidean.topSeminorm_eq_zero_of_mem_polynomialSubmodule hb hq)
    (Module.finBasis ℝ (SobolevEuclidean.polynomialSubmodule (k := k) (p := p) hb)) hℓ hle v

end SobolevQuotientMain
