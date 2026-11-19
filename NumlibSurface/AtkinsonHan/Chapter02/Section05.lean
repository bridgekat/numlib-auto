/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.HahnBanach
import Numlib.Analysis.Sobolev.Interval
import Numlib.MeasureTheory.Function.LpSpace.Duality
import Numlib.MeasureTheory.Integral.IntervalIntegral

/-!
# Atkinson and Han, Section 2.5: Linear functionals

This module formalizes Section 2.5 of [han2009theoretical]. The dual space $V'$ of a normed space
$V$ is the space of bounded linear functionals on $V$. The Hahn–Banach theorem extends a bounded
linear functional from a subspace to the whole space with the same norm, and its generalized form
extends a linear functional dominated by a sublinear functional. Consequences are the norming
functionals and the formula
$$\|v\| = \sup_{\ell \in V', \ \|\ell\| = 1} |\ell(v)|.$$
On a Hilbert space the Riesz representation theorem writes every $\ell \in V'$ as $\ell(v) = (v, u)$
with a unique $u$ and $\|\ell\| = \|u\|$. The examples identify $(L^p(\Omega))'$ with
$L^{p'}(\Omega)$ for $1 \le p < \infty$, show that $(L^\infty(\Omega))'$ is larger than
$L^1(\Omega)$ by a Hahn–Banach extension of a point evaluation, and compute the Riesz representer of
a point evaluation on $H^1(a, b)$.

The proofs specialize Mathlib's Hahn–Banach and Riesz theorems, the $L^p$ duality of
`Numlib.MeasureTheory.Function.LpSpace.Duality`, and the space $H^1(a, b)$ of
`Numlib.Analysis.Sobolev.Interval`.

## Main definitions

* Example 2.5.3, `AtkinsonHan.Chapter02.cosetLinfty`: the coset $[v] \in L^\infty(0, 1)$ of a
  function $v \in C[0, 1]$.
* Example 2.5.3, `AtkinsonHan.Chapter02.contCosets`: the subspace $V_0 \subseteq L^\infty(0, 1)$ of
  the cosets of continuous functions.
* Example 2.5.3, `AtkinsonHan.Chapter02.evalCoset`: the point evaluation $\ell_c([v]) = v(c)$ on
  $V_0$, (2.5.3).
* Definition 2.5.4, `AtkinsonHan.Chapter02.IsSublinear`: a sublinear functional.

## Main results

* Example 2.5.1, `AtkinsonHan.Chapter02.example_2_5_1`: for $1 \le p < \infty$, the pairing (2.5.1)
  identifies $L^{p'}(\Omega)$ isometrically with $(L^p(\Omega))'$.
* Example 2.5.1, `AtkinsonHan.Chapter02.example_2_5_1_top`: some bounded linear functional on
  $L^\infty(\Omega)$ is not given by (2.5.1) for any $u \in L^1(\Omega)$.
* Theorem 2.5.2, `AtkinsonHan.Chapter02.theorem_2_5_2`: the Hahn–Banach theorem.
* Example 2.5.3, `AtkinsonHan.Chapter02.example_2_5_3`: $\|\ell_c\| = 1$, $\ell_c$ has a Hahn–Banach
  extension to $L^\infty(0, 1)$ of norm $1$, and no extension is given by an $L^1$ function.
* Definition 2.5.4, `AtkinsonHan.Chapter02.isSublinear_iff`: Definition 2.5.4 is equivalent to the
  hypotheses of Mathlib's Hahn–Banach theorem.
* Theorem 2.5.5, `AtkinsonHan.Chapter02.theorem_2_5_5`: the generalized Hahn–Banach theorem, for a
  sublinear functional.
* Corollary 2.5.6, `AtkinsonHan.Chapter02.corollary_2_5_6`: every $v \neq 0$ has a functional $\ell$
  with $\|\ell\| = 1$ and $\ell(v) = \|v\|$.
* Corollary 2.5.7, `AtkinsonHan.Chapter02.corollary_2_5_7`: the formula (2.5.4) for $\|v\|$.
* Theorem 2.5.8, `AtkinsonHan.Chapter02.theorem_2_5_8`: the Riesz representation theorem, with
  (2.5.5) and (2.5.6).
* Example 2.5.9, `AtkinsonHan.Chapter02.example_2_5_9_l2`: $(L^2(\Omega))' = L^2(\Omega)$ by the
  Riesz representation.
* Example 2.5.9, `AtkinsonHan.Chapter02.example_2_5_9`: the point evaluation $\ell(v) = v(c)$ on
  $H^1(a, b)$ has a unique Riesz representer, characterized by (2.5.8).

## Conventions

* The book's inner product $(u, v)$ is linear in its first argument, and Mathlib's `inner 𝕜 u v` is
  linear in its second argument. Therefore the book's $\ell(v) = (v, u)$ is written
  `ℓ v = inner 𝕜 u v`.

## Implementation notes

* The dual space $V'$ is Mathlib's `StrongDual 𝕜 V`.
* The space $H^1(a, b)$ is the backbone's `SobolevInterval 1 a b`. It is a Hilbert space with the
  inner product $(u, v)_{H^1} = \int_a^b (u'v' + uv) \, dx$
  (`SobolevInterval.inner_eq_intervalIntegral`). Point evaluation at $c \in [a, b]$ is bounded on
  it, because $H^1(a, b)$ embeds in $C[a, b]$ (`SobolevInterval.toContinuousMap`); this is the hint
  of Exercise 2.5.5.
* The duality of $L^p$ and $L^{p'}$ is the backbone's Riesz representation theorem
  `MeasureTheory.Lp.dualEquiv`, stated for any σ-finite measure. The case $p = \infty$ of Example
  2.5.1 is the backbone's `MeasureTheory.Lp.not_surjective_toDual_top`.
* Example 2.5.3 constructs the book's $V_0$, $\ell_c$ and $\hat\ell_c$. That $\hat\ell_c$ is not
  given by an $L^1$ function is proved for every extension of $\ell_c$, by the argument of
  `MeasureTheory.Lp.exists_strongDual_top_apply_eq`, through
  `MeasureTheory.Lp.toDual_ne_of_forall_contDiff_apply_eq`.

## Deviations from the source

* **Example 2.5.1** (generalization). The book takes $\Omega \subseteq \mathbb{R}^d$ bounded and
  open. The identification $(L^p(\Omega))' = L^{p'}(\Omega)$ for $1 \le p < \infty$ holds for every
  set $\Omega$. See `AtkinsonHan.Chapter02.example_2_5_1`.
* **Example 2.5.1, $p=\infty$** (generalization and reading). The real nonrepresentation result
  allows unbounded open sets and explicitly assumes nonemptiness and positive spatial dimension.
* **Example 2.5.3** (reading). The value identity is proved for globally continuous
  representatives. The book asserts it when the representative is continuous at the evaluation
  point. Lean also proves that none of the point-evaluation extensions has an $L^1$ density.
* **Corollary 2.5.7** (reading). Lean gives the empty supremum value zero in the zero space.
* **Example 2.5.9, $L^2$ case** (generalization). The representation theorem is stated for
  the restricted measure on any Euclidean subset.

## Not formalized

* **Example 2.5.3, further properties of $\hat\ell_c$.** The book states them without proof: the
  locality of $\hat\ell_c$, the bounds $m \le \hat\ell_c([v]) \le M$ in terms of the values of $v$
  in a neighbourhood of $c$, and convergence of nearby extended evaluations to $v(c)$ when
  $v$ is continuous at $c$. The value identity is stated for globally continuous functions.
* **Example 2.5.9, the boundary value problem.** The book calls the representer $u$ the generalized
  solution of $-u'' + u = \delta(x - c)$ with $u'(a) = u'(b) = 0$.
-/

open Filter Topology

namespace AtkinsonHan.Chapter02

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]

/-! ### Theorem 2.5.2: the Hahn–Banach theorem -/

/-- **Theorem 2.5.2** of [han2009theoretical] (Hahn–Banach theorem). Let $V$ be a normed space over
$\mathbb{K}$, let $V_0$ be a subspace of $V$, and let $\ell \in V_0'$. Then there is an
$\hat\ell \in V'$ with $\hat\ell(v) = \ell(v)$ for all $v \in V_0$ and
$\|\hat\ell\| = \|\ell\|$. -/
theorem theorem_2_5_2 (V₀ : Submodule 𝕜 V) (ℓ : StrongDual 𝕜 V₀) :
    ∃ ℓhat : StrongDual 𝕜 V, (∀ v : V₀, ℓhat v = ℓ v) ∧ ‖ℓhat‖ = ‖ℓ‖ :=
  exists_extension_norm_eq V₀ ℓ

/-! ### Definition 2.5.4 and Theorem 2.5.5: the generalized Hahn–Banach theorem -/

/-- **Definition 2.5.4** of [han2009theoretical]. Let $E$ be a real linear space. A functional
$p : E \to \mathbb{R}$ is **sublinear** if
$$p(u + v) \le p(u) + p(v) \quad \text{and} \quad p(\alpha v) = \alpha \, p(v)$$
for all $u, v \in E$ and all $\alpha \ge 0$.

The book states positive homogeneity for all $\alpha \ge 0$.
`AtkinsonHan.Chapter02.isSublinear_iff` shows that this is equivalent to the form for
$\alpha > 0$ that Mathlib uses. -/
def IsSublinear {E : Type*} [AddCommGroup E] [Module ℝ E] (p : E → ℝ) : Prop :=
  (∀ u v, p (u + v) ≤ p u + p v) ∧ ∀ (α : ℝ) (v : E), 0 ≤ α → p (α • v) = α * p v

/-- Let $E$ be a real linear space and $p : E \to \mathbb{R}$. Then $p$ is sublinear in the sense of
Definition 2.5.4 of [han2009theoretical] if and only if $p(u + v) \le p(u) + p(v)$ for all
$u, v$ and $p(cv) = c \, p(v)$ for all $c > 0$ and all $v$.

The right side is the pair of hypotheses `N_add` and `N_hom` of Mathlib's
`exists_extension_of_le_sublinear`. Homogeneity for $c > 0$ gives the case $c = 0$, because
$p(0) = p(2 \cdot 0) = 2 p(0)$. -/
theorem isSublinear_iff {E : Type*} [AddCommGroup E] [Module ℝ E] (p : E → ℝ) :
    IsSublinear p ↔
      (∀ u v, p (u + v) ≤ p u + p v) ∧ ∀ c : ℝ, 0 < c → ∀ v : E, p (c • v) = c * p v := by
  refine ⟨fun h => ⟨h.1, fun c hc v => h.2 c v hc.le⟩, fun h => ⟨h.1, fun α v hα => ?_⟩⟩
  rcases hα.lt_or_eq with hα' | hα'
  · exact h.2 α hα' v
  · have hzero : p 0 = 0 := by
      have := h.2 2 (by norm_num) (0 : E)
      rw [smul_zero] at this
      linarith
    rw [← hα', zero_smul, hzero, zero_mul]

/-- **Theorem 2.5.5** of [han2009theoretical] (generalized Hahn–Banach theorem). Let $E$ be a real
linear space, let $V_0$ be a subspace of $E$, let $p$ be a sublinear functional on $E$, and let
$\ell$ be a linear functional on $V_0$ with $\ell(v) \le p(v)$ for all $v \in V_0$. Then there
is a linear functional $\hat\ell$ on $E$ with $\hat\ell(v) = \ell(v)$ for all $v \in V_0$ and
$\hat\ell(v) \le p(v)$ for all $v \in E$. -/
theorem theorem_2_5_5 {E : Type*} [AddCommGroup E] [Module ℝ E] (V₀ : Submodule ℝ E) (p : E → ℝ)
    (hp : IsSublinear p) (ℓ : V₀ →ₗ[ℝ] ℝ) (hℓ : ∀ v : V₀, ℓ v ≤ p v) :
    ∃ ℓhat : E →ₗ[ℝ] ℝ, (∀ v : V₀, ℓhat v = ℓ v) ∧ ∀ v, ℓhat v ≤ p v := by
  obtain ⟨hadd, hhom⟩ := (isSublinear_iff p).1 hp
  exact exists_extension_of_le_sublinear ⟨V₀, ℓ⟩ p (fun c hc x => hhom c hc x) hadd hℓ

/-! ### Corollaries 2.5.6 and 2.5.7 -/

/-- **Corollary 2.5.6** of [han2009theoretical]. Let $V$ be a normed space over $\mathbb{K}$ and let
$v \in V$, $v \neq 0$. Then there is an $\ell \in V'$ with $\|\ell\| = 1$ and $\ell(v) = \|v\|$. -/
theorem corollary_2_5_6 (v : V) (hv : v ≠ 0) : ∃ ℓ : StrongDual 𝕜 V, ‖ℓ‖ = 1 ∧ ℓ v = ‖v‖ :=
  exists_dual_vector 𝕜 v (norm_ne_zero_iff.mpr hv)

/-- **Corollary 2.5.7** of [han2009theoretical], formula (2.5.4). Let $V$ be a normed space over
$\mathbb{K}$ and let $v \in V$. Then
$$\|v\| = \sup \{ |\ell(v)| : \ell \in V', \ \|\ell\| = 1 \}.$$
On the zero space no functional has norm $1$, the set is empty, and both sides are $0$, because
`sSup ∅ = 0`.

**Reading.** Defines the supremum of the empty norm-one dual sphere as zero on the zero space.
-/
theorem corollary_2_5_7 (v : V) :
    ‖v‖ = sSup {r : ℝ | ∃ ℓ : StrongDual 𝕜 V, ‖ℓ‖ = 1 ∧ r = ‖ℓ v‖} := by
  have hbdd : ∀ r ∈ {r : ℝ | ∃ ℓ : StrongDual 𝕜 V, ‖ℓ‖ = 1 ∧ r = ‖ℓ v‖}, r ≤ ‖v‖ := by
    rintro r ⟨ℓ, hℓ, rfl⟩
    simpa [hℓ] using ℓ.le_opNorm v
  refine le_antisymm ?_ (Real.sSup_le hbdd (norm_nonneg v))
  rcases eq_or_ne v 0 with rfl | hv
  · rw [norm_zero]
    exact Real.sSup_nonneg (by rintro r ⟨ℓ, -, rfl⟩; exact norm_nonneg _)
  · obtain ⟨ℓ, hℓ, hval⟩ := corollary_2_5_6 (𝕜 := 𝕜) v hv
    refine le_csSup ⟨‖v‖, fun r hr => hbdd r hr⟩ ⟨ℓ, hℓ, ?_⟩
    rw [hval, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg v)]

/-! ### Theorem 2.5.8: the Riesz representation theorem -/

/-- **Theorem 2.5.8** of [han2009theoretical] (Riesz representation theorem). Let $H$ be a Hilbert
space over $\mathbb{K}$ and let $\ell \in H'$. Then there is a unique $u \in H$ with
$$\ell(v) = (v, u) \quad \text{for all } v \in H, \qquad (2.5.5)$$
and $\|\ell\| = \|u\|$ (2.5.6).

The book's $(v, u)$ is `inner 𝕜 u v`. The norm identity is stated for the representer
`(InnerProductSpace.toDual 𝕜 H).symm ℓ`. -/
theorem theorem_2_5_8 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (ℓ : StrongDual 𝕜 H) :
    (∃! u : H, ∀ v, ℓ v = inner 𝕜 u v) ∧ ‖ℓ‖ = ‖(InnerProductSpace.toDual 𝕜 H).symm ℓ‖ := by
  constructor
  · refine ⟨(InnerProductSpace.toDual 𝕜 H).symm ℓ, fun v => ?_, ?_⟩
    · exact (InnerProductSpace.toDual_symm_apply).symm
    · change ∀ u : H, (∀ v, ℓ v = inner 𝕜 u v) → u = (InnerProductSpace.toDual 𝕜 H).symm ℓ
      intro u hu
      have : InnerProductSpace.toDual 𝕜 H u = ℓ := by
        ext v
        exact (hu v).symm
      rw [← this, LinearIsometryEquiv.symm_apply_apply]
  · exact ((InnerProductSpace.toDual 𝕜 H).symm.norm_map ℓ).symm

/-! ### Example 2.5.9: the Riesz representer of point evaluation on $H^1(a, b)$ -/

section Example259

open MeasureTheory Set

variable {a b : ℝ}

/-- **Example 2.5.9** of [han2009theoretical], the space $L^2(\Omega)$. Let
$\Omega \subseteq \mathbb{R}^d$ and let $\ell$ be a bounded linear functional on the real space
$L^2(\Omega)$. Then there is a unique $u \in L^2(\Omega)$ with $\ell(v) = (v, u)$ for all
$v \in L^2(\Omega)$. Thus $(L^2(\Omega))' = L^2(\Omega)$ through (2.5.5).

This is `AtkinsonHan.Chapter02.theorem_2_5_8` for $H = L^2(\Omega)$. The set $\Omega$ is
arbitrary, and the measure is Lebesgue measure restricted to $\Omega$.

**Generalization.** The restricted measure may come from any Euclidean subset. -/
theorem example_2_5_9_l2 {d : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (ℓ : StrongDual ℝ (Lp ℝ 2 (volume.restrict Ω))) :
    ∃! u : Lp ℝ 2 (volume.restrict Ω), ∀ v, ℓ v = inner ℝ u v :=
  (theorem_2_5_8 ℓ).1

/-- **Example 2.5.9** of [han2009theoretical], the space $H^1(a, b)$. Let $a < b$ and
$c \in [a, b]$. Then there is a unique $u \in H^1(a, b)$ such that
$$\int_a^b \big( u'(x) v'(x) + u(x) v(x) \big) \, dx = v(c) \quad \text{for every } v \in H^1(a,
  b). \qquad (2.5.8)$$
Thus $u$ is the Riesz representer of the functional $\ell(v) = v(c)$ of (2.5.7).

Here $v(c)$ is the value at $c$ of the continuous representative of $v$, given by the embedding
`SobolevInterval.toContinuousMap` of $H^1(a, b)$ in $C[a, b]$. The book calls $u$ the
generalized solution of $-u'' + u = \delta(x - c)$ with $u'(a) = u'(b) = 0$. This boundary value
problem is not formalized. -/
theorem example_2_5_9 (hab : a < b) (c : Icc a b) :
    ∃! u : SobolevInterval 1 a b, ∀ v : SobolevInterval 1 a b,
      (∫ x in a..b, (SobolevInterval.deriv u 1 x * SobolevInterval.deriv v 1 x
          + SobolevInterval.fn u x * SobolevInterval.fn v x)) =
        SobolevInterval.toContinuousMap hab v c := by
  obtain ⟨u, hu, huniq⟩ := (theorem_2_5_8 (SobolevInterval.evalCLM hab c)).1
  refine ⟨u, fun v => ?_, fun u' hu' => huniq u' fun v => ?_⟩
  · rw [← SobolevInterval.inner_eq_intervalIntegral hab.le u v]
    exact (hu v).symm
  · rw [SobolevInterval.inner_eq_intervalIntegral hab.le u' v]
    exact (hu' v).symm

end Example259

section Example251

open MeasureTheory Set
open scoped ENNReal

/-! ### Example 2.5.1: the dual of $L^p(\Omega)$ -/

/-- **Example 2.5.1** of [han2009theoretical], the case $1 \le p < \infty$. Let
$\Omega \subseteq \mathbb{R}^d$, let $1 \le p < \infty$, and let $p'$ be the conjugate exponent,
$1/p + 1/p' = 1$, with $p' = \infty$ for $p = 1$. For $u \in L^{p'}(\Omega)$ consider the
functional
$$\ell(v) = \int_\Omega u(x) v(x) \, dx, \qquad v \in L^p(\Omega). \qquad (2.5.1)$$
Then:

* every $\ell \in (L^p(\Omega))'$ has the form (2.5.1) for a unique $u \in L^{p'}(\Omega)$;
* every $u \in L^{p'}(\Omega)$ defines by (2.5.1) a functional $\ell \in (L^p(\Omega))'$ with
  $\|\ell\| = \|u\|_{L^{p'}}$;
* the map $u \mapsto \ell$ is a linear isometric isomorphism of $L^{p'}(\Omega)$ onto
  $(L^p(\Omega))'$.

**Generalization.** The book takes $\Omega$ bounded and open. The backbone's Riesz
representation theorem `MeasureTheory.Lp.dualEquiv` needs only a σ-finite measure, so $\Omega$
is any set here.

The scalars are $\mathbb{R}$ or $\mathbb{C}$, and the pairing is bilinear, $\int_\Omega u v$
without complex conjugation, as in (2.5.1). -/
theorem example_2_5_1 {d : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin d))) (p p' : ℝ≥0∞) [Fact (1 ≤ p)]
    [Fact (1 ≤ p')] [p.HolderConjugate p'] (hp : p ≠ ∞) :
    (∀ ℓ : StrongDual 𝕜 (Lp 𝕜 p (volume.restrict Ω)),
      ∃! u : Lp 𝕜 p' (volume.restrict Ω), ∀ v, ℓ v = ∫ x in Ω, u x * v x) ∧
    (∀ u : Lp 𝕜 p' (volume.restrict Ω), ∃ ℓ : StrongDual 𝕜 (Lp 𝕜 p (volume.restrict Ω)),
      ‖ℓ‖ = ‖u‖ ∧ ∀ v, ℓ v = ∫ x in Ω, u x * v x) ∧
    ∃ e : Lp 𝕜 p' (volume.restrict Ω) ≃ₗᵢ[𝕜] StrongDual 𝕜 (Lp 𝕜 p (volume.restrict Ω)),
      ∀ u v, e u v = ∫ x in Ω, u x * v x := by
  set e := Lp.dualEquiv 𝕜 p p' (volume.restrict Ω) hp with he
  refine ⟨fun ℓ ↦ ⟨e.symm ℓ, fun v ↦ ?_, fun u hu ↦ ?_⟩, fun u ↦ ⟨e u, e.norm_map u,
    fun v ↦ Lp.dualEquiv_apply hp u v⟩, e, fun u v ↦ Lp.dualEquiv_apply hp u v⟩
  · rw [← Lp.dualEquiv_apply hp (e.symm ℓ) v, he, LinearIsometryEquiv.apply_symm_apply]
  · refine e.injective ?_
    rw [he, LinearIsometryEquiv.apply_symm_apply]
    ext v
    rw [Lp.dualEquiv_apply hp u v, hu v]

/-- **Example 2.5.1** of [han2009theoretical], the case $p = \infty$. Let
$\Omega \subseteq \mathbb{R}^d$ with $d \ge 1$ be open and nonempty. Then there is a bounded
linear functional $\ell$ on the real space $L^\infty(\Omega)$ that is not of the form (2.5.1)
for any $u \in L^1(\Omega)$: for every $u \in L^1(\Omega)$ there is a $v \in L^\infty(\Omega)$
with $\ell(v) \neq \int_\Omega u v \, dx$. Thus $(L^\infty(\Omega))'$ is larger than
$L^1(\Omega)$.

The proof is the backbone's `MeasureTheory.Lp.not_surjective_toDual_top`, a Hahn–Banach
extension of a point evaluation as in Example 2.5.3. The dimension is written $d + 1$ in Lean,
and the scalars are real.

**Reading.** Lean assumes a nonempty open subset in positive spatial dimension and works with
real scalars. Boundedness of the set is unnecessary. -/
theorem example_2_5_1_top {d : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) (hΩ : IsOpen Ω)
    (hne : Ω.Nonempty) :
    ∃ ℓ : StrongDual ℝ (Lp ℝ ∞ (volume.restrict Ω)), ∀ u : Lp ℝ 1 (volume.restrict Ω),
      ∃ v, ℓ v ≠ ∫ x in Ω, u x * v x := by
  have h := Lp.not_surjective_toDual_top (volume : Measure (EuclideanSpace ℝ (Fin (d + 1)))) hΩ hne
  rw [Function.Surjective, not_forall] at h
  obtain ⟨ℓ, hℓ⟩ := h
  refine ⟨ℓ, fun u ↦ ?_⟩
  by_contra hcon
  push Not at hcon
  exact hℓ ⟨u, ContinuousLinearMap.ext fun v ↦ by rw [Lp.toDual_apply, hcon v]⟩

end Example251

/-! ### Example 2.5.3: point evaluation on $L^\infty(0, 1)$ -/

section Example253

open MeasureTheory Set
open scoped ENNReal

/-- **Example 2.5.3** of [han2009theoretical], the coset of a continuous function. For
$v \in C[0, 1]$, $[v] \in L^\infty(0, 1)$ is the class of the extension of $v$ to $\mathbb{R}$
by its values at the endpoints. The map $v \mapsto [v]$ is linear. -/
noncomputable def cosetLinfty : C(Icc (0 : ℝ) 1, ℝ) →ₗ[ℝ] Lp ℝ ∞ (volume.restrict (Ioo (0 : ℝ) 1))
    where
  toFun v := (ContinuousMap.IccExtend zero_le_one v).continuous.continuousOn.memLp_top_restrict_Ioo
    |>.toLp _
  map_add' v w := by
    rw [← MemLp.toLp_add]
    exact (MemLp.toLp_eq_toLp_iff _ _).2 (Eventually.of_forall fun x ↦ by
      simp [ContinuousMap.coe_IccExtend, IccExtend, Pi.add_apply])
  map_smul' c v := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    exact (MemLp.toLp_eq_toLp_iff _ _).2 (Eventually.of_forall fun x ↦ by
      simp [ContinuousMap.coe_IccExtend, IccExtend, Pi.smul_apply])

/-- For $v \in C[0, 1]$, the coset $[v]$ agrees almost everywhere on $(0, 1)$ with the extension of
$v$ by its endpoint values. -/
theorem coeFn_cosetLinfty (v : C(Icc (0 : ℝ) 1, ℝ)) :
    cosetLinfty v =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] IccExtend zero_le_one v :=
  MemLp.coeFn_toLp
    (ContinuousMap.IccExtend zero_le_one v).continuous.continuousOn.memLp_top_restrict_Ioo

/-- For $v \in C[0, 1]$ and $x \in [0, 1]$,
$$|v(x)| \le \|[v]\|_{L^\infty(0, 1)},$$
as used in Example 2.5.3 of [han2009theoretical]. The essential supremum over $(0, 1)$ bounds
$|v|$ on a dense subset of $[0, 1]$, and hence everywhere by continuity. -/
theorem norm_apply_le_norm_cosetLinfty (v : C(Icc (0 : ℝ) 1, ℝ)) (x : Icc (0 : ℝ) 1) :
    ‖v x‖ ≤ ‖cosetLinfty v‖ := by
  have hae : ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) 1)),
      ‖IccExtend zero_le_one v t‖ ≤ ‖cosetLinfty v‖ := by
    filter_upwards [coeFn_cosetLinfty v, Lp.ae_norm_le_norm_top (cosetLinfty v)] with t ht ht'
    rw [← ht]
    exact ht'
  have hIoo : ∀ t ∈ Ioo (0 : ℝ) 1, ‖IccExtend zero_le_one v t‖ ≤ ‖cosetLinfty v‖ :=
    forall_of_ae_restrict_of_isOpen isOpen_Ioo (by
      simp only [not_le]
      exact isOpen_lt continuous_const
        (ContinuousMap.IccExtend zero_le_one v).continuous.norm) hae
  have hcl : closure (Ioo (0 : ℝ) 1) ⊆ {t | ‖IccExtend zero_le_one v t‖ ≤ ‖cosetLinfty v‖} :=
    (isClosed_le (ContinuousMap.IccExtend zero_le_one v).continuous.norm
      continuous_const).closure_subset_iff.2 hIoo
  rw [closure_Ioo zero_ne_one] at hcl
  have := hcl x.2
  rwa [mem_ofPred_eq, IccExtend_val] at this

/-- For $v \in C[0, 1]$, the norm of the coset is the maximum norm:
$\|[v]\|_{L^\infty(0, 1)} = \|v\|_\infty$. Thus the norm (2.5.2) on $V_0$ is not only equivalent
to the norm of $C[0, 1]$, as Example 2.5.3 of [han2009theoretical] says, but equal to it. -/
theorem norm_cosetLinfty (v : C(Icc (0 : ℝ) 1, ℝ)) : ‖cosetLinfty v‖ = ‖v‖ := by
  refine le_antisymm ?_ ((ContinuousMap.norm_le _ (norm_nonneg _)).2
    (norm_apply_le_norm_cosetLinfty v))
  rw [Lp.norm_def, eLpNorm_exponent_top (Lp.aestronglyMeasurable _)]
  refine ENNReal.toReal_le_of_le_ofReal (norm_nonneg _) (eLpNormEssSup_le_of_ae_bound ?_)
  filter_upwards [coeFn_cosetLinfty v, ae_restrict_mem measurableSet_Ioo] with t ht htI
  rw [ht, IccExtend_of_mem _ _ (Ioo_subset_Icc_self htI)]
  exact v.norm_coe_le_norm _

/-- The map $v \mapsto [v]$ from $C[0, 1]$ to $L^\infty(0, 1)$ is injective, so $V_0$ is a copy of
$C[0, 1]$ inside $L^\infty(0, 1)$. -/
theorem cosetLinfty_injective : Function.Injective cosetLinfty :=
  (injective_iff_map_eq_zero _).2 fun v hv ↦ by
    have h := norm_cosetLinfty v
    rw [hv, norm_zero] at h
    exact norm_eq_zero.1 h.symm

/-- **Example 2.5.3** of [han2009theoretical], the subspace $V_0$. The subspace
$V_0 \subseteq L^\infty(0, 1)$ is the set of the cosets $[v]$ of continuous functions
$v \in C[0, 1]$. -/
noncomputable abbrev contCosets : Submodule ℝ (Lp ℝ ∞ (volume.restrict (Ioo (0 : ℝ) 1))) :=
  LinearMap.range cosetLinfty

/-- **Example 2.5.3** of [han2009theoretical], the functional (2.5.3). For $c \in [0, 1]$, the point
evaluation on $V_0$ is
$$\ell_c([v]) = v(c).$$
It is well defined because the map $v \mapsto [v]$ is injective, and it is bounded with
$\|\ell_c\| \le 1$ because $|v(c)| \le \|[v]\|_\infty$. -/
noncomputable def evalCoset (c : Icc (0 : ℝ) 1) : StrongDual ℝ contCosets :=
  LinearMap.mkContinuous
    ((ContinuousMap.evalCLM ℝ c : C(Icc (0 : ℝ) 1, ℝ) →L[ℝ] ℝ).toLinearMap ∘ₗ
      (LinearEquiv.ofInjective cosetLinfty cosetLinfty_injective).symm.toLinearMap) 1
    fun g ↦ by
      obtain ⟨v, rfl⟩ := (LinearEquiv.ofInjective cosetLinfty cosetLinfty_injective).surjective g
      rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, one_mul]
      exact norm_apply_le_norm_cosetLinfty v c

/-- For $v \in C[0, 1]$, the coset $[v]$ lies in $V_0$. -/
theorem cosetLinfty_mem_contCosets (v : C(Icc (0 : ℝ) 1, ℝ)) : cosetLinfty v ∈ contCosets :=
  LinearMap.mem_range_self _ v

/-- For $c \in [0, 1]$ and $v \in C[0, 1]$, $\ell_c([v]) = v(c)$. -/
@[simp]
theorem evalCoset_apply (c : Icc (0 : ℝ) 1) (v : C(Icc (0 : ℝ) 1, ℝ)) :
    evalCoset c ⟨cosetLinfty v, cosetLinfty_mem_contCosets v⟩ = v c := by
  change (ContinuousMap.evalCLM ℝ c)
    ((LinearEquiv.ofInjective cosetLinfty cosetLinfty_injective).symm
      ⟨cosetLinfty v, cosetLinfty_mem_contCosets v⟩) = v c
  have : (LinearEquiv.ofInjective cosetLinfty cosetLinfty_injective).symm
      ⟨cosetLinfty v, cosetLinfty_mem_contCosets v⟩ = v := by
    rw [LinearEquiv.symm_apply_eq]
    rfl
  rw [this]
  rfl

/-- For $c \in [0, 1]$, $\|\ell_c\| = 1$. The bound $|v(c)| \le \|[v]\|_\infty$ gives
$\|\ell_c\| \le 1$, and the constant function $1$ gives equality. -/
theorem norm_evalCoset (c : Icc (0 : ℝ) 1) : ‖evalCoset c‖ = 1 := by
  refine le_antisymm (LinearMap.mkContinuous_norm_le _ zero_le_one _) ?_
  have h1 := (evalCoset c).le_opNorm ⟨cosetLinfty 1, cosetLinfty_mem_contCosets 1⟩
  rw [evalCoset_apply, ContinuousMap.one_apply] at h1
  change ‖(1 : ℝ)‖ ≤ ‖evalCoset c‖ * ‖cosetLinfty 1‖ at h1
  simp only [norm_cosetLinfty, norm_one, mul_one] at h1
  exact h1

/-- Let $c \in [0, 1]$ and let $\ell$ be a bounded linear functional on $L^\infty(0, 1)$ with
$\ell([v]) = v(c)$ for every $v \in C[0, 1]$. Let $f : \mathbb{R} \to \mathbb{R}$ be continuous
and essentially bounded on $(0, 1)$. Then $\ell$ maps the class of $f$ to $f(c)$.

**Reading.** The source assumes continuity at the evaluation point. This statement uses a
globally continuous representative. -/
theorem apply_toLp_eq_of_forall_cosetLinfty (c : Icc (0 : ℝ) 1)
    (ℓ : StrongDual ℝ (Lp ℝ ∞ (volume.restrict (Ioo (0 : ℝ) 1))))
    (hℓ : ∀ v : C(Icc (0 : ℝ) 1, ℝ), ℓ (cosetLinfty v) = v c) (f : ℝ → ℝ)
    (hf : MemLp f ∞ (volume.restrict (Ioo (0 : ℝ) 1))) (hfc : Continuous f) :
    ℓ (hf.toLp f) = f c := by
  set v : C(Icc (0 : ℝ) 1, ℝ) := ⟨fun t ↦ f t, hfc.comp continuous_subtype_val⟩ with hv
  have : hf.toLp f = cosetLinfty v := by
    refine (MemLp.toLp_eq_toLp_iff hf (ContinuousMap.IccExtend zero_le_one
      v).continuous.continuousOn.memLp_top_restrict_Ioo).2 ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    rw [ContinuousMap.coe_IccExtend, IccExtend_of_mem _ _ (Ioo_subset_Icc_self ht)]
    rfl
  rw [this, hℓ]
  rfl

/-- **Example 2.5.3** of [han2009theoretical]. Let $c \in [0, 1]$, and let $\ell_c([v]) = v(c)$ be
the point evaluation (2.5.3) on the subspace $V_0 \subseteq L^\infty(0, 1)$ of the cosets of
continuous functions. Then:

* $\|\ell_c\| = 1$;
* there is an $\hat\ell_c \in (L^\infty(0, 1))'$ with $\hat\ell_c([v]) = v(c)$ for all
  $v \in C[0, 1]$ and $\|\hat\ell_c\| = 1$;
* no such extension is of the form (2.5.1): for every $\hat\ell_c \in (L^\infty(0, 1))'$ with
  $\hat\ell_c([v]) = v(c)$ for all $v \in C[0, 1]$, and every $u \in L^1(0, 1)$, there is a
  $w \in L^\infty(0, 1)$ with $\hat\ell_c(w) \neq \int_0^1 u w \, dx$.

The extension comes from the Hahn–Banach theorem, `AtkinsonHan.Chapter02.theorem_2_5_2`. It is a
point evaluation on functions that are only measurable, and it shows that the dual of
$L^\infty(0, 1)$ is larger than $L^1(0, 1)$, as in Example 2.5.1. The subspace $V_0$ is
`AtkinsonHan.Chapter02.contCosets`, and the point evaluation is
`AtkinsonHan.Chapter02.evalCoset`. The further properties of $\hat\ell_c$ that the book states
without proof (the bounds $m \le \hat\ell_c([v]) \le M$ in terms of the values of $v$ in a
neighbourhood of $c$, and the value $v(c)$ when $v$ is continuous at $c$) are not formalized.

**Reading.** For this construction Lean also rules out an $L^1$ density for every extension
agreeing with point evaluation on continuous functions. -/
theorem example_2_5_3 (c : Icc (0 : ℝ) 1) :
    ‖evalCoset c‖ = 1 ∧
    (∃ ℓhat : StrongDual ℝ (Lp ℝ ∞ (volume.restrict (Ioo (0 : ℝ) 1))),
      (∀ v : C(Icc (0 : ℝ) 1, ℝ), ℓhat (cosetLinfty v) = v c) ∧ ‖ℓhat‖ = 1) ∧
    ∀ ℓhat : StrongDual ℝ (Lp ℝ ∞ (volume.restrict (Ioo (0 : ℝ) 1))),
      (∀ v : C(Icc (0 : ℝ) 1, ℝ), ℓhat (cosetLinfty v) = v c) →
      ∀ u : Lp ℝ 1 (volume.restrict (Ioo (0 : ℝ) 1)),
        ∃ w, ℓhat w ≠ ∫ x in Ioo (0 : ℝ) 1, u x * w x := by
  refine ⟨norm_evalCoset c, ?_, fun ℓhat hℓ u ↦ ?_⟩
  · obtain ⟨ℓhat, hext, hnorm⟩ := theorem_2_5_2 contCosets (evalCoset c)
    refine ⟨ℓhat, fun v ↦ ?_, hnorm.trans (norm_evalCoset c)⟩
    rw [← evalCoset_apply c v]
    exact hext ⟨cosetLinfty v, cosetLinfty_mem_contCosets v⟩
  · have h := Lp.toDual_ne_of_forall_contDiff_apply_eq (x₀ := (c : ℝ)) ℓhat
      (fun f hf hfc _ ↦ apply_toLp_eq_of_forall_cosetLinfty c ℓhat hℓ f hf hfc.continuous) u
    by_contra hcon
    push Not at hcon
    exact h (ContinuousLinearMap.ext fun w ↦ by rw [Lp.toDual_apply, hcon w])

end Example253

end AtkinsonHan.Chapter02
