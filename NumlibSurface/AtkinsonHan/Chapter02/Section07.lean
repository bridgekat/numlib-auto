/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.DoubleDual
import Numlib.Analysis.Convex.Uniform
import Numlib.Analysis.Fourier.TrigonometricBasis
import Numlib.Analysis.Normed.Module.Reflexive
import Numlib.Analysis.Normed.Module.Reflexive.EberleinSmulian
import Numlib.Analysis.Normed.Module.WeakDual
import Numlib.Variational.WeakMinimization

/-!
# Atkinson and Han, Section 2.7: Weak convergence

This module formalizes Section 2.7 of [han2009theoretical]. A sequence $v_n$ in a normed space $V$
converges weakly to $u$, written $v_n \rightharpoonup u$, if $\ell(v_n) \to \ell(u)$ for every
$\ell \in V'$. A weakly convergent sequence is bounded, and $\|u\| \le \liminf \|v_n\|$. Weak
convergence is weaker than convergence in norm: $\sin(nx) \rightharpoonup 0$ in $L^2(0, 2\pi)$, but
not in norm. In a Hilbert space, and more generally in a uniformly convex space, weak convergence
together with $\|v_n\| \to \|u\|$ gives convergence in norm. The space $V$ is reflexive if the
canonical map $J : V \to V''$ is onto. Theorem 2.7.5 says that $V$ is reflexive if and only if every
bounded sequence in $V$ has a weakly convergent subsequence. For a sequence of operators
$L_n \in \mathcal{L}(V, W)$ the section defines strong convergence, $\|L - L_n\| \to 0$, and
weak-$*$ convergence, $L_n v \to Lv$ for every $v$. In the dual of a reflexive space, weak-$*$
convergence and weak convergence agree.

The proofs specialize the backbone modules `Numlib.Analysis.Normed.Module.WeakDual`,
`Numlib.Analysis.Convex.Uniform`, `Numlib.Analysis.Normed.Module.Reflexive` and
`Numlib.Analysis.Normed.Module.Reflexive.EberleinSmulian`, and the trigonometric system of
`Numlib.Analysis.Fourier.TrigonometricBasis`.

## Main definitions

* Definition 2.7.1, `AtkinsonHan.Chapter02.WeakSeqTendsto`: weak convergence $v_n \rightharpoonup u$
  of a sequence.
* Definition 2.7.4, `AtkinsonHan.Chapter02.definition_2_7_4`: $V$ is reflexive if the canonical map
  $J : V \to V''$ is onto.
* Definition 2.7.6, `AtkinsonHan.Chapter02.definition_2_7_6` and
  `AtkinsonHan.Chapter02.definition_2_7_6_weakStar`: strong convergence, $\|L - L_n\| \to 0$, and
  weak-$*$ convergence, $L_n v \to Lv$ for every $v$, of a sequence of operators.

## Main results

* Definition 2.7.1, `AtkinsonHan.Chapter02.tendsto_toWeakSpace_iff_weakSeqTendsto` and
  `AtkinsonHan.Chapter02.weakSeqTendsto_iff_root`: weak convergence is convergence in Mathlib's
  `WeakSpace` topology, and over the reals it is the backbone's `WeakSeqTendsto` of
  `Numlib.Variational.WeakMinimization`.
* Proposition 2.7.2, `AtkinsonHan.Chapter02.proposition_2_7_2`: a weakly convergent sequence is
  bounded.
* Example 2.7.3, `AtkinsonHan.Chapter02.example_2_7_3`: $\sin(nx) \rightharpoonup 0$ in
  $L^2(0, 2\pi)$, but not in norm.
* Definition 2.7.4, `AtkinsonHan.Chapter02.definition_2_7_4_iff_isReflexive`: Definition 2.7.4 is
  the backbone's `NormedSpace.IsReflexive`.
* Theorem 2.7.5, `AtkinsonHan.Chapter02.theorem_2_7_5_mp`, `AtkinsonHan.Chapter02.theorem_2_7_5_mpr`
  and `AtkinsonHan.Chapter02.theorem_2_7_5`: a normed space is reflexive if and only if every
  bounded sequence has a weakly convergent subsequence.
* Definition 2.7.6, `AtkinsonHan.Chapter02.definition_2_7_6_iff` and
  `AtkinsonHan.Chapter02.definition_2_7_6_weakStar_iff`: strong convergence is convergence in the
  operator norm, and weak-$*$ convergence is convergence in the topology of pointwise convergence.
* Definition 2.7.6, `AtkinsonHan.Chapter02.definition_2_7_6_weakStar_of_strong`: strong convergence
  implies weak-$*$ convergence.
* The remark closing the section, `AtkinsonHan.Chapter02.definition_2_7_6_weakStar_iff_weak`: in the
  dual of a reflexive space, weak-$*$ convergence and weak convergence agree.
* Exercise 2.7.2, `AtkinsonHan.Chapter02.exercise_2_7_2`: $v_n \rightharpoonup u$ implies
  $\|u\| \le \liminf \|v_n\|$.
* Exercise 2.7.3, `AtkinsonHan.Chapter02.exercise_2_7_3`: in a Hilbert space, $v_n \to u$ if and
  only if $v_n \rightharpoonup u$ and $\|v_n\| \to \|u\|$.
* Exercise 2.7.4 (a) and (c), `AtkinsonHan.Chapter02.exercise_2_7_4`: the same implication in a
  uniformly convex space.

## Proof outline

The forward half of Theorem 2.7.5 passes to the closed span of the bounded sequence, which is
separable and reflexive, and applies the sequential Banach–Alaoglu theorem there. The converse
combines Kakutani's characterization of reflexivity by the weak compactness of the closed unit ball,
proved through Goldstine's theorem, with the Eberlein–Šmulian theorem, which turns the sequential
hypothesis into that compactness.

## Conventions

* Exercise 2.7.4 and Definition 2.7.4 have the same number. `AtkinsonHan.Chapter02.exercise_2_7_4`
  is Exercise 2.7.4, the Radon–Riesz property in a uniformly convex space. It is a different result
  from Definition 2.7.4, reflexivity, which comes before Theorem 2.7.5.

## Implementation notes

* Only the sequential notion of weak convergence is defined, over any
  $\mathbb{K} \in \{\mathbb{R}, \mathbb{C}\}$. Section 3.3 uses this relation throughout, and
  Definition 3.3.3 is stated with it. The direct method of `Numlib.Variational.WeakMinimization` is
  stated with the backbone's real `WeakSeqTendsto`, and
  `AtkinsonHan.Chapter02.weakSeqTendsto_iff_root` connects the two.
* Proposition 2.7.2 and Exercise 2.7.2 are the backbone's `exists_norm_le_of_tendsto_toWeakSpace`
  and `norm_le_liminf_norm_of_weak_tendsto`, stated for Mathlib's `WeakSpace` topology and
  transferred by `tendsto_toWeakSpace_iff`. Exercises 2.7.3 and 2.7.4 are the backbone's
  `tendsto_of_forall_inner_tendsto_of_tendsto_norm` and
  `tendsto_of_forall_dual_tendsto_of_tendsto_norm`.
* Example 2.7.3 is read on the circle. The space $L^2(0, 2\pi)$ is $L^2$ of `AddCircle (2 * π)` with
  the normalized Haar measure, and $\sin(nx)$ is replaced by $\sqrt{2} \sin(nx)$, which is
  `trigFun (2 * π) (-n)`. This sequence is orthonormal, which makes it weakly null and of constant
  norm.
* Reflexivity is the backbone's `NormedSpace.IsReflexive` of
  `Numlib.Analysis.Normed.Module.Reflexive`, by
  `AtkinsonHan.Chapter02.definition_2_7_4_iff_isReflexive`. Where the book applies Theorem 2.7.5
  (Theorems 3.3.8, 3.3.10, 3.3.12 and 3.3.14), the surface assumes `NormedSpace.IsReflexive ℝ V`.
  Those proofs use the backbone class `WeaklySeqCompactSpace` of
  `Numlib.Variational.WeakMinimization`, and instance search supplies it through the instance
  `WeaklySeqCompactSpace.of_isReflexive`, which is again the forward half of Theorem 2.7.5. What the
  book leaves unproved beyond this is recorded in `Numlib.Variational.Minimization`.

## Deviations from the source

* **Example 2.7.3** (reading and generalization). Lean uses normalized Haar measure and scaled
  sine vectors of norm one. A separate theorem shows weak convergence to zero for sequences of
  distinct vectors from any orthonormal family in a real Hilbert space.
* **Theorem 2.7.5** (generalization). The book assumes that $V$ is a Banach space. The statement
  holds for every normed space, because a reflexive normed space is complete. See
  `AtkinsonHan.Chapter02.theorem_2_7_5`.
* **Exercises 2.7.3 and 2.7.4(c)** (reading and generalization). Lean states the Hilbert result
  over the reals and with completeness. For uniformly convex real spaces it states the implication
  from weak convergence and convergence of norms, allowing incomplete spaces.

## Not formalized

* **The uniform integrability criteria after Theorem 2.7.5**, including Dunford–Pettis.
* **Exercise 2.7.4 (b)**, the uniform convexity of $L^p$ by the Clarkson inequalities.
-/

open Filter MeasureTheory Topology

open scoped Real

namespace AtkinsonHan.Chapter02

section General

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- **Definition 2.7.1** of [han2009theoretical]. Let $V$ be a normed space over $\mathbb{K}$. A
sequence $v_n \in V$ **converges weakly** to $u \in V$, written $v_n \rightharpoonup u$, if
$$\ell(v_n) \to \ell(u) \quad \text{for every } \ell \in V'.$$

Only the sequential notion is defined, which is all that the surface uses. Mathlib's `WeakSpace`
carries the weak topology. -/
def WeakSeqTendsto (𝕜 : Type*) {V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    (v : ℕ → V) (u : V) : Prop :=
  ∀ ℓ : StrongDual 𝕜 V, Tendsto (fun n => ℓ (v n)) atTop (𝓝 (ℓ u))

/-- Let $V$ be a normed space over $\mathbb{K}$. A sequence $v_n$ converges weakly to $u$ in the
sense of Definition 2.7.1 of [han2009theoretical] if and only if it converges to $u$ in
Mathlib's `WeakSpace` topology on $V$.

The backbone states its two lemmas on weak convergence in this topology. -/
theorem tendsto_toWeakSpace_iff_weakSeqTendsto {v : ℕ → V} {u : V} :
    Tendsto (fun n => toWeakSpace 𝕜 V (v n)) atTop (𝓝 (toWeakSpace 𝕜 V u)) ↔
      WeakSeqTendsto 𝕜 v u :=
  tendsto_toWeakSpace_iff

/-- **Definition 2.7.1** of [han2009theoretical], over the reals. Let $V$ be a real normed space.
Then $v_n \rightharpoonup u$ in the sense of Definition 2.7.1 if and only if
$v_n \rightharpoonup u$ in the sense of the backbone's `WeakSeqTendsto`, in which
`Numlib.Variational.WeakMinimization` states the direct method. -/
theorem weakSeqTendsto_iff_root {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {v : ℕ → V}
    {u : V} : WeakSeqTendsto ℝ v u ↔ _root_.WeakSeqTendsto v u :=
  Iff.rfl

/-- **Proposition 2.7.2** of [han2009theoretical]. Let $V$ be a normed space over $\mathbb{K}$ and
let $v_n \rightharpoonup u$ in $V$. Then there is a $C$ with $\|v_n\| \le C$ for all $n$.

The proof applies the principle of uniform boundedness to the images of the $v_n$ in the double
dual. It is the backbone's `exists_norm_le_of_tendsto_toWeakSpace`. -/
theorem proposition_2_7_2 {v : ℕ → V} {u : V} (h : WeakSeqTendsto 𝕜 v u) :
    ∃ C : ℝ, ∀ n, ‖v n‖ ≤ C :=
  exists_norm_le_of_tendsto_toWeakSpace (tendsto_toWeakSpace_iff.2 h)

/-- **Exercise 2.7.2** of [han2009theoretical]. Let $V$ be a normed space over $\mathbb{K}$ and let
$v_n \rightharpoonup u$ in $V$. Then
$$\|u\| \le \liminf_{n \to \infty} \|v_n\|.$$
Thus the norm is weakly sequentially lower semicontinuous.

The book proves this statement twice, and `AtkinsonHan.Chapter03.example_3_3_5` restates it. In
`AtkinsonHan.Chapter02.example_2_7_3` the inequality is strict. -/
theorem exercise_2_7_2 {v : ℕ → V} {u : V} (h : WeakSeqTendsto 𝕜 v u) :
    ‖u‖ ≤ liminf (fun n => ‖v n‖) atTop :=
  norm_le_liminf_norm_of_weak_tendsto (tendsto_toWeakSpace_iff.2 h)

end General

/-! ### Example 2.7.3 -/

section Example

/-- Let $H$ be a real Hilbert space. Then $v_n \rightharpoonup u$ in $H$ if and only if
$(v_n, w) \to (u, w)$ for every $w \in H$.

The proof uses the Riesz representation of the dual. -/
theorem weakSeqTendsto_iff_inner {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {v : ℕ → H} {u : H} :
    WeakSeqTendsto ℝ v u ↔
      ∀ w : H, Tendsto (fun n => inner ℝ (v n) w) atTop (𝓝 (inner ℝ u w)) := by
  constructor
  · intro h w
    have h' := h (InnerProductSpace.toDual ℝ H w)
    simp only [InnerProductSpace.toDual_apply_apply] at h'
    simpa only [real_inner_comm] using h'
  · intro h ℓ
    obtain ⟨w, rfl⟩ := (InnerProductSpace.toDual ℝ H).surjective ℓ
    simp only [InnerProductSpace.toDual_apply_apply]
    simpa only [real_inner_comm] using h w

/-- Let $H$ be a real Hilbert space, let $(\varphi_i)_{i \in I}$ be an orthonormal family in $H$,
and let $g : \mathbb{N} \to I$ be injective. Then $\varphi_{g(n)} \rightharpoonup 0$.

By Bessel's inequality the inner products of the $\varphi_{g(n)}$ with a fixed vector are square
summable, so they tend to $0$.

**Generalization.** The source uses the sine sequence. The orthonormal-family argument
applies to any sequence of distinct members of such a family in a real Hilbert space. -/
theorem weakSeqTendsto_zero_of_orthonormal {ι H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {φ : ι → H} (hφ : Orthonormal ℝ φ) {g : ℕ → ι}
    (hg : Function.Injective g) : WeakSeqTendsto ℝ (fun n => φ (g n)) 0 := by
  refine weakSeqTendsto_iff_inner.2 fun w => ?_
  have hgt : Tendsto g atTop cofinite := Nat.cofinite_eq_atTop ▸ hg.tendsto_cofinite
  have h1 : Tendsto (fun n => ‖inner ℝ (φ (g n)) w‖ ^ 2) atTop (𝓝 0) :=
    (hφ.inner_products_summable w).tendsto_cofinite_zero.comp hgt
  have h2 : Tendsto (fun n => ‖inner ℝ (φ (g n)) w‖) atTop (𝓝 0) := by
    have h3 := (Real.continuous_sqrt.tendsto 0).comp h1
    simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using h3
  simpa using tendsto_zero_iff_norm_tendsto_zero.2 h2

/-- **Example 2.7.3** of [han2009theoretical]. Let $\varphi_n(x) = \sqrt{2} \sin(nx)$ for $n \ge 1$,
as elements of $L^2(0, 2\pi)$ with the normalized measure $dx / (2\pi)$. Then
$\varphi_n \rightharpoonup 0$, $\|\varphi_n\| = 1$ for every $n$, and $\varphi_n$ does not
converge to $0$ in norm.

The sequence is orthonormal, so its inner products with a fixed vector tend to $0$ by Bessel's
inequality. Since the weak limit is $0$ and every term has norm $1$, the inequality of
`AtkinsonHan.Chapter02.exercise_2_7_2` is strict here. The space $L^2(0, 2\pi)$ is $L^2$ of
`AddCircle (2 * π)` with the probability Haar measure, and $\varphi_{n+1}$ is
`trigLp (2 * π) (-(n + 1))`, the function `trigFun (2 * π) (-(n + 1))` of Theorem 1.3.13. The
factor $\sqrt{2}$ and the normalized measure make the sequence orthonormal; they do not change
the conclusion of the book about $\sin(nx)$.

**Reading.** The source uses unnormalized Lebesgue measure and the functions $\sin(nx)$.
Lean uses Haar probability measure and multiplies the functions by $\sqrt{2}$. -/
theorem example_2_7_3 :
    WeakSeqTendsto ℝ (fun n : ℕ => trigLp (2 * π) (-(n + 1) : ℤ)) 0 ∧
      (∀ n : ℕ, ‖trigLp (2 * π) (-(n + 1) : ℤ)‖ = 1) ∧
      ¬ Tendsto (fun n : ℕ => trigLp (2 * π) (-(n + 1) : ℤ)) atTop (𝓝 0) := by
  have hinj : Function.Injective fun n : ℕ => (-(n + 1) : ℤ) := by
    intro a b hab
    simpa using hab
  have hnorm : ∀ n : ℕ, ‖trigLp (2 * π) (-(n + 1) : ℤ)‖ = 1 := fun n =>
    orthonormal_trigFun.1 (-(n + 1) : ℤ)
  refine ⟨weakSeqTendsto_zero_of_orthonormal orthonormal_trigFun hinj, hnorm, fun h => ?_⟩
  have h1 : Tendsto (fun n : ℕ => ‖trigLp (2 * π) (-(n + 1) : ℤ)‖) atTop (𝓝 0) := by
    simpa using h.norm
  rw [tendsto_congr hnorm] at h1
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds h1)

end Example

/-! ### The Radon–Riesz property -/

/-- **Exercise 2.7.3** of [han2009theoretical]. Let $H$ be a real Hilbert space, and let
$v_n, u \in H$. Then $v_n \to u$ if and only if $v_n \rightharpoonup u$ and $\|v_n\| \to \|u\|$.

**Reading.** Lean assumes a real Hilbert space. The source names inner-product spaces. -/
theorem exercise_2_7_3 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {v : ℕ → H} {u : H} :
    Tendsto v atTop (𝓝 u) ↔
      WeakSeqTendsto ℝ v u ∧ Tendsto (fun n => ‖v n‖) atTop (𝓝 ‖u‖) := by
  rw [tendsto_of_forall_inner_tendsto_of_tendsto_norm (𝕜 := ℝ), weakSeqTendsto_iff_inner]

/-- **Exercise 2.7.4 (a), (c)** of [han2009theoretical] (Radon–Riesz property). Let $E$ be a real
uniformly convex normed space, and let $v_n \rightharpoonup u$ in $E$ with $\|v_n\| \to \|u\|$.
Then $v_n \to u$.

A Hilbert space is uniformly convex by Mathlib's `InnerProductSpace.toUniformConvexSpace`.
Completeness of $E$ is not assumed. The proof is the backbone's
`tendsto_of_forall_dual_tendsto_of_tendsto_norm`.

**Generalization.** The implication holds without completeness. The source states an
 equivalence in Banach spaces. This declaration gives the implication from the weak and norm
convergences. -/
theorem exercise_2_7_4 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [UniformConvexSpace E]
    {v : ℕ → E} {u : E} (hweak : WeakSeqTendsto ℝ v u)
    (hnorm : Tendsto (fun n => ‖v n‖) atTop (𝓝 ‖u‖)) : Tendsto v atTop (𝓝 u) :=
  tendsto_of_forall_dual_tendsto_of_tendsto_norm hweak hnorm

/-! ### Definition 2.7.4 and Theorem 2.7.5: reflexivity -/

section Reflexive

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- **Definition 2.7.4** of [han2009theoretical]. Let $V$ be a normed space over $\mathbb{K}$. Then
$V$ is **reflexive** if $V'' = V$, that is, if the canonical map $J : V \to V''$, $\langle Jv,
\ell \rangle = \langle \ell, v \rangle$, is onto.

The book defines $J$ just before the definition, shows that it is an isometry of $V$ onto
$J(V)$, and then identifies $J(V)$ with $V$. So the definition asks that this canonical $J$ is
onto, and not only that $V$ and $V''$ are isometrically isomorphic in some way, which is a
strictly weaker condition. The map $J$ is Mathlib's `NormedSpace.inclusionInDoubleDual`. The
book's two remarks on the definition are the backbone's
`NormedSpace.completeSpace_of_isReflexive` (a reflexive space is a Banach space) and
`NormedSpace.instIsReflexiveOfInnerProductSpace` (a Hilbert space is reflexive). -/
def definition_2_7_4 (𝕜 : Type*) (V : Type*) [RCLike 𝕜] [NormedAddCommGroup V]
    [NormedSpace 𝕜 V] : Prop :=
  Function.Surjective (NormedSpace.inclusionInDoubleDual 𝕜 V)

/-- **Definition 2.7.4** of [han2009theoretical], the identification with the backbone. A normed
space $V$ over $\mathbb{K}$ is reflexive in the sense of Definition 2.7.4 if and only if it is
reflexive in the sense of the backbone's `NormedSpace.IsReflexive`, in which
`Numlib.Analysis.Normed.Module.Reflexive` states the properties of reflexive spaces. -/
theorem definition_2_7_4_iff_isReflexive :
    definition_2_7_4 𝕜 V ↔ NormedSpace.IsReflexive 𝕜 V :=
  ⟨fun h => ⟨h⟩, fun _ => NormedSpace.surjective_inclusionInDoubleDual⟩

/-- **Theorem 2.7.5** of [han2009theoretical], the direct half. Let $V$ be a reflexive normed space
over $\mathbb{K}$, and let $v_n \in V$ satisfy $\|v_n\| \le C$ for all $n$. Then there are a
$u \in V$ and a subsequence $v_{n_k}$ with $v_{n_k} \rightharpoonup u$.

**Generalization.** The book states the theorem for a Banach space. Completeness need not be
assumed, because a reflexive normed space is complete
(`NormedSpace.completeSpace_of_isReflexive`).

This is the half that the book uses later. The proof is the backbone's
`NormedSpace.exists_subseq_forall_dual_tendsto`, which passes to the closed span of the
sequence, which is separable and reflexive as a closed subspace, and applies the sequential
Banach–Alaoglu theorem there. The converse is `AtkinsonHan.Chapter02.theorem_2_7_5_mpr`. -/
theorem theorem_2_7_5_mp (hV : definition_2_7_4 𝕜 V) {v : ℕ → V} {C : ℝ}
    (hv : ∀ n, ‖v n‖ ≤ C) :
    ∃ (u : V) (φ : ℕ → ℕ), StrictMono φ ∧ WeakSeqTendsto 𝕜 (fun k => v (φ k)) u := by
  have : NormedSpace.IsReflexive 𝕜 V := definition_2_7_4_iff_isReflexive.1 hV
  exact NormedSpace.exists_subseq_forall_dual_tendsto hv

/-- **Theorem 2.7.5** of [han2009theoretical], the converse half. Let $V$ be a normed space over
$\mathbb{K}$ in which every bounded sequence has a subsequence that converges weakly to an
element of $V$. Then $V$ is reflexive.

**Generalization.** The book states the theorem for a Banach space. Completeness need not be
assumed, because the conclusion implies it.

The proof combines Kakutani's characterization of reflexivity by the weak compactness of the
closed unit ball with the Eberlein–Šmulian theorem, which turns the sequential hypothesis into
that compactness. It is the backbone's
`NormedSpace.isReflexive_of_forall_exists_subseq_forall_dual_tendsto` of
`Numlib.Analysis.Normed.Module.Reflexive.EberleinSmulian`. -/
theorem theorem_2_7_5_mpr
    (h : ∀ (v : ℕ → V) (C : ℝ), (∀ n, ‖v n‖ ≤ C) →
      ∃ (u : V) (φ : ℕ → ℕ), StrictMono φ ∧ WeakSeqTendsto 𝕜 (fun k => v (φ k)) u) :
    definition_2_7_4 𝕜 V :=
  definition_2_7_4_iff_isReflexive.2
    (NormedSpace.isReflexive_of_forall_exists_subseq_forall_dual_tendsto h)

/-- **Theorem 2.7.5** of [han2009theoretical]. Let $V$ be a normed space over $\mathbb{K}$. Then $V$
is reflexive if and only if every bounded sequence in $V$ has a subsequence that converges
weakly to an element of $V$.

**Generalization.** The book assumes that $V$ is a Banach space. Completeness need not be
assumed, because either side implies it.

The two directions are `AtkinsonHan.Chapter02.theorem_2_7_5_mp` and
`AtkinsonHan.Chapter02.theorem_2_7_5_mpr`. -/
theorem theorem_2_7_5 :
    definition_2_7_4 𝕜 V ↔ ∀ (v : ℕ → V) (C : ℝ), (∀ n, ‖v n‖ ≤ C) →
      ∃ (u : V) (φ : ℕ → ℕ), StrictMono φ ∧ WeakSeqTendsto 𝕜 (fun k => v (φ k)) u :=
  ⟨fun hV _ _ hv => theorem_2_7_5_mp hV hv, theorem_2_7_5_mpr⟩

end Reflexive

/-! ### Definition 2.7.6: convergence of a sequence of operators -/

section Operators

variable {𝕜 V W : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [NormedAddCommGroup W] [NormedSpace 𝕜 W]

/-- **Definition 2.7.6** of [han2009theoretical], strong convergence. Let $V$ and $W$ be normed
spaces over $\mathbb{K}$, and let $L_n, L \in \mathcal{L}(V, W)$. The sequence $L_n$ **converges
strongly** to $L$ if $\|L - L_n\| \to 0$.

In Lean the sequence is `L` and the limit is `T`. The condition is convergence in the operator
norm of `V →L[𝕜] W` by `AtkinsonHan.Chapter02.definition_2_7_6_iff`, and the Banach–Steinhaus
material of Section 2.4 uses it in that form. -/
def definition_2_7_6 {𝕜 V W : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    [NormedAddCommGroup W] [NormedSpace 𝕜 W] (L : ℕ → V →L[𝕜] W) (T : V →L[𝕜] W) : Prop :=
  Tendsto (fun n => ‖T - L n‖) atTop (𝓝 0)

/-- **Definition 2.7.6** of [han2009theoretical], weak-$*$ convergence. Let $V$ and $W$ be normed
spaces over $\mathbb{K}$, and let $L_n, L \in \mathcal{L}(V, W)$. The sequence $L_n$ **converges
weak-$*$** to $L$, or pointwise on $V$, if $L_n v \to Lv$ for every $v \in V$.

In Lean the sequence is `L` and the limit is `T`. The condition is convergence in the topology
of pointwise convergence by `AtkinsonHan.Chapter02.definition_2_7_6_weakStar_iff`. The name
follows the book: for $W = \mathbb{K}$ this is weak-$*$ convergence in the dual $V'$, and by
`AtkinsonHan.Chapter02.definition_2_7_6_weakStar_iff_weak` it agrees with weak convergence in
$V'$ when $V$ is reflexive. -/
def definition_2_7_6_weakStar {𝕜 V W : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    [NormedAddCommGroup W] [NormedSpace 𝕜 W] (L : ℕ → V →L[𝕜] W) (T : V →L[𝕜] W) : Prop :=
  ∀ v : V, Tendsto (fun n => L n v) atTop (𝓝 (T v))

/-- Let $V$ and $W$ be normed spaces over $\mathbb{K}$, and let $L_n, L \in \mathcal{L}(V, W)$. Then
$L_n$ converges strongly to $L$ in the sense of Definition 2.7.6 of [han2009theoretical] if and
only if $L_n \to L$ in the normed space $\mathcal{L}(V, W)$. -/
theorem definition_2_7_6_iff (L : ℕ → V →L[𝕜] W) (T : V →L[𝕜] W) :
    definition_2_7_6 L T ↔ Tendsto L atTop (𝓝 T) := by
  constructor
  · intro h
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact h.congr fun n => norm_sub_rev T (L n)
  · intro h
    rw [tendsto_iff_norm_sub_tendsto_zero] at h
    exact h.congr fun n => norm_sub_rev (L n) T

/-- Let $V$ and $W$ be normed spaces over $\mathbb{K}$, and let $L_n, L \in \mathcal{L}(V, W)$. Then
$L_n$ converges weak-$*$ to $L$ in the sense of Definition 2.7.6 of [han2009theoretical] if and
only if the functions $L_n$ converge to $L$ in the topology of pointwise convergence on the
functions from $V$ to $W$. -/
theorem definition_2_7_6_weakStar_iff (L : ℕ → V →L[𝕜] W) (T : V →L[𝕜] W) :
    definition_2_7_6_weakStar L T ↔ Tendsto (fun n => ⇑(L n)) atTop (𝓝 (⇑T)) :=
  tendsto_pi_nhds.symm

/-- **Definition 2.7.6** of [han2009theoretical], the remark after it. Let $V$ and $W$ be normed
spaces over $\mathbb{K}$, and let $L_n, L \in \mathcal{L}(V, W)$. If $L_n$ converges strongly to
$L$, then $L_n$ converges weak-$*$ to $L$.

The proof uses $\|L_n v - Lv\| \le \|L - L_n\| \, \|v\|$. The converse fails, which is why the
two notions have different names. -/
theorem definition_2_7_6_weakStar_of_strong {L : ℕ → V →L[𝕜] W} {T : V →L[𝕜] W}
    (h : definition_2_7_6 L T) : definition_2_7_6_weakStar L T := by
  intro v
  rw [← tendsto_sub_nhds_zero_iff]
  have hb : Tendsto (fun n => ‖L n - T‖ * ‖v‖) atTop (𝓝 0) := by
    have h' := h.mul_const ‖v‖
    rw [zero_mul] at h'
    exact h'.congr fun n => by rw [norm_sub_rev T (L n)]
  refine squeeze_zero_norm (fun n => ?_) hb
  simpa using (L n - T).le_opNorm v

/-- The remark closing **Section 2.7** of [han2009theoretical]. Let $V$ be a reflexive normed space
over $\mathbb{K}$, and let $\ell_n, \ell \in V'$. Then $\ell_n$ converges weak-$*$ to $\ell$ if
and only if $\ell_n \rightharpoonup \ell$ in $V'$.

A sequence of functionals converges weak-$*$ if it converges at every $v \in V$, and weakly if
it converges at every element of $V''$. Reflexivity says that the second family of tests is the
first. Only the implication from weak-$*$ to weak convergence uses reflexivity. -/
theorem definition_2_7_6_weakStar_iff_weak (hV : definition_2_7_4 𝕜 V)
    (L : ℕ → V →L[𝕜] 𝕜) (T : V →L[𝕜] 𝕜) :
    definition_2_7_6_weakStar L T ↔ WeakSeqTendsto 𝕜 L T := by
  constructor
  · intro h ψ
    obtain ⟨v, rfl⟩ := hV ψ
    exact h v
  · intro h v
    exact h (NormedSpace.inclusionInDoubleDual 𝕜 V v)

end Operators

end AtkinsonHan.Chapter02
