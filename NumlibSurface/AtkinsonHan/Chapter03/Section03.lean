/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.InnerProductSpace.Convex
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Polynomial
import Numlib.Analysis.Convex.StrictConvexSpace
import Numlib.Analysis.Normed.Module.Reflexive
import Numlib.Analysis.Normed.Module.WeakDual
import Numlib.Analysis.Normed.Module.BestApprox
import Numlib.Approximation.Chebyshev
import Numlib.Variational.Minimization
import Numlib.Variational.WeakMinimization
import NumlibSurface.AtkinsonHan.Chapter01.Section02
import NumlibSurface.AtkinsonHan.Chapter02.Section07

/-!
# Atkinson and Han, Section 3.3: Best approximation

This module formalizes Section 3.3 of [han2009theoretical]. Let $K$ be a subset of a normed space
$V$ and let $u \in V$. An element $\hat u \in K$ is a best approximation of $u$ from $K$ if
$$\|u - \hat u\| = \inf_{v \in K} \|u - v\|. \qquad (3.3.3)$$
The section first defines convex sets and convex functionals, closed and weakly closed sets, lower
semicontinuous and weakly sequentially lower semicontinuous functionals, separated sets and coercive
functionals. It then proves that a minimizer of a functional exists on a weakly closed set in a
reflexive Banach space (Theorems 3.3.8, 3.3.10 and 3.3.12, with Mazur's lemma 3.3.11) and on a
closed subset of a finite-dimensional subspace (Theorem 3.3.13). As a consequence, best
approximations exist from closed convex sets in a reflexive space and from finite-dimensional
subspaces. They are unique when $\|\cdot\|^p$ is strictly convex or the space is strictly normed. In
$C[a, b]$ the best uniform approximation from $\mathcal{P}_n$ is unique and is characterized by the
alternation of the error at $n + 2$ points (Chebyshev), and the same existence and uniqueness holds
for trigonometric polynomials in $C_p(2\pi)$.

Best approximation is the backbone's `IsBestApprox` of `Numlib.Analysis.Normed.Module.BestApprox`.
The existence theorems specialize `Numlib.Variational.Minimization` and
`Numlib.Variational.WeakMinimization`, Theorems 3.3.19 and 3.3.20 come from
`Numlib.Approximation.Chebyshev`, and strict normedness from
`Numlib.Analysis.Convex.StrictConvexSpace`.

## Main definitions

* Definition 3.3.1, `AtkinsonHan.Chapter03.definition_3_3_1`: a convex set, identified with
  Mathlib's `Convex ℝ K` by `AtkinsonHan.Chapter03.definition_3_3_1_iff`.
* Definition 3.3.2, `AtkinsonHan.Chapter03.definition_3_3_2` and
  `AtkinsonHan.Chapter03.definition_3_3_2_strict`: a convex and a strictly convex functional,
  identified with `ConvexOn` and `StrictConvexOn` by `AtkinsonHan.Chapter03.definition_3_3_2_iff`
  and `AtkinsonHan.Chapter03.definition_3_3_2_strict_iff`.
* Definition 3.3.3, `AtkinsonHan.Chapter03.definition_3_3_3` and
  `AtkinsonHan.Chapter03.definition_3_3_3_weak`: a closed and a weakly closed set, identified with
  `IsClosed` and `IsWeakSeqClosed` by `AtkinsonHan.Chapter03.definition_3_3_3_iff` and
  `AtkinsonHan.Chapter03.definition_3_3_3_weak_iff`.
* Definition 3.3.4, `AtkinsonHan.Chapter03.definition_3_3_4` and
  `AtkinsonHan.Chapter03.definition_3_3_4_weak`: a lower semicontinuous and a weakly sequentially
  lower semicontinuous functional, identified with `LowerSemicontinuousOn` and
  `WeakSeqLowerSemicontinuousOn` by `AtkinsonHan.Chapter03.definition_3_3_4_iff` and
  `AtkinsonHan.Chapter03.definition_3_3_4_weak_iff`.
* Definition 3.3.6, `AtkinsonHan.Chapter03.AreSeparated` and
  `AtkinsonHan.Chapter03.AreStrictlySeparated`: two sets separated, or strictly separated, by a
  nonzero bounded linear functional.
* Definition 3.3.9, `AtkinsonHan.Chapter03.definition_3_3_9`: a functional coercive over $K$,
  identified with the backbone's `IsCoerciveFunctionalOn` by
  `AtkinsonHan.Chapter03.definition_3_3_9_iff`.
* Section 3.3.4, `AtkinsonHan.Chapter03.IsStrictlyNormed`: a strictly normed space, equivalent to
  Mathlib's `StrictConvexSpace ℝ V` by
  `AtkinsonHan.Chapter03.isStrictlyNormed_iff_strictConvexSpace`.
* `AtkinsonHan.Chapter03.polyLE` and `AtkinsonHan.Chapter03.rho`: the space $\mathcal{P}_n$ of
  polynomials of degree at most $n$ on $[a, b]$, and the error $\rho_n(f)$ of best uniform
  approximation from it.

## Main results

* Equation (3.3.1), `AtkinsonHan.Chapter03.definition_3_3_1_sum`: a convex set contains every convex
  combination of its elements.
* Equation (3.3.3), `AtkinsonHan.Chapter03.isBestApprox_iff_norm_eq_iInf`: `IsBestApprox` is the
  condition (3.3.3).
* Definition 3.3.3, `AtkinsonHan.Chapter03.definition_3_3_3_of_weak`: a weakly closed set is closed.
* Example 3.3.5, `AtkinsonHan.Chapter03.example_3_3_5`: the norm is weakly sequentially lower
  semicontinuous.
* Theorem 3.3.7, `AtkinsonHan.Chapter03.theorem_3_3_7` and `AtkinsonHan.Chapter03.theorem_3_3_7'`: a
  compact convex set and a disjoint closed convex set are strictly separated.
* Theorem 3.3.8, `AtkinsonHan.Chapter03.theorem_3_3_8`: a weakly sequentially lower semicontinuous
  functional has a minimizer on a nonempty bounded weakly closed subset of a reflexive Banach space.
* Theorem 3.3.10, `AtkinsonHan.Chapter03.theorem_3_3_10`: the same on an unbounded set, for a
  coercive functional.
* Theorem 3.3.11, `AtkinsonHan.Chapter03.theorem_3_3_11` (Mazur's lemma),
  `AtkinsonHan.Chapter03.theorem_3_3_11_isWeakSeqClosed` and
  `AtkinsonHan.Chapter03.theorem_3_3_11_weakSeqLsc`: a weak limit is a strong limit of convex
  combinations; so closed convex sets are weakly closed, and convex lower semicontinuous functionals
  are weakly sequentially lower semicontinuous.
* Theorem 3.3.12, `AtkinsonHan.Chapter03.theorem_3_3_12`: a convex lower semicontinuous functional
  has a minimizer on a nonempty closed convex subset of a reflexive Banach space, if the set is
  bounded or the functional is coercive.
* Theorem 3.3.13, `AtkinsonHan.Chapter03.theorem_3_3_13` and
  `AtkinsonHan.Chapter03.theorem_3_3_13_unique`: a lower semicontinuous functional has a minimizer
  on a nonempty closed subset of a finite-dimensional subspace, if the set is bounded or the
  functional is coercive; a strictly convex functional has at most one minimizer.
* Theorem 3.3.14, `AtkinsonHan.Chapter03.theorem_3_3_14`: in a reflexive Banach space every point
  has a best approximation from a nonempty closed convex set.
* Theorem 3.3.15, `AtkinsonHan.Chapter03.theorem_3_3_15`: every point has a best approximation from
  a nonempty closed convex subset of a finite-dimensional subspace.
* Theorem 3.3.16, `AtkinsonHan.Chapter03.theorem_3_3_16`: every point has a best approximation from
  a finite-dimensional subspace.
* Example 3.3.17, `AtkinsonHan.Chapter03.example_3_3_17`: best uniform polynomial approximations on
  $[a, b]$ exist.
* Theorem 3.3.18, `AtkinsonHan.Chapter03.theorem_3_3_18`: if $\|\cdot\|^p$ is strictly convex for
  some $p \ge 1$, best approximations from a convex set are unique.
* Theorem 3.3.19, `AtkinsonHan.Chapter03.theorem_3_3_19`,
  `AtkinsonHan.Chapter03.theorem_3_3_19_equioscillates` and
  `AtkinsonHan.Chapter03.theorem_3_3_19_alternation` (Chebyshev equioscillation theorem): the best
  uniform approximation from $\mathcal{P}_n$ on $[a, b]$ is unique, and it is characterized by an
  alternation of the error at $n + 2$ points.
* Theorem 3.3.20, `AtkinsonHan.Chapter03.theorem_3_3_20`: the best uniform approximation of
  $g \in C_p(2\pi)$ from $\mathcal{T}_n$ exists and is unique.
* Theorem 3.3.21, `AtkinsonHan.Chapter03.theorem_3_3_21`: in a strictly normed space, best
  approximations from a nonempty convex set are unique.
* Exercise 3.3.8, `AtkinsonHan.Chapter03.exercise_3_3_8` and
  `AtkinsonHan.Chapter03.exercise_3_3_8_rpow`: in an inner product space $\|\cdot\|^2$ is strictly
  convex.
* Exercise 3.3.9, `AtkinsonHan.Chapter03.exercise_3_3_9`: an inner product space is strictly normed.

## Conventions

* The convergence $v_n \to v$ is `AtkinsonHan.Chapter01.definition_1_2_8`, and the weak convergence
  $v_n \rightharpoonup v$ is `AtkinsonHan.Chapter02.WeakSeqTendsto`, Definition 2.7.1 of §2.7. This
  module uses these restatements instead of their Mathlib counterparts.
* $C_p(2\pi)$ is `C(AddCircle (2 * π), ℝ)`, and $\mathcal{T}_n$ is the backbone's
  `trigPolyLE (2 * π) n`.

## Implementation notes

* Theorems 3.3.8, 3.3.10, 3.3.12 and 3.3.14 assume a reflexive Banach space. The hypothesis is
  `[NormedSpace.IsReflexive ℝ V]`, the reflexivity class of
  `Numlib.Analysis.Normed.Module.Reflexive`, which is Definition 2.7.4 by
  `AtkinsonHan.Chapter02.definition_2_7_4_iff_isReflexive`. Mathlib's `Module.IsReflexive` is the
  algebraic double dual, a different condition. Completeness is not a separate hypothesis: a
  reflexive space is complete by `NormedSpace.completeSpace_of_isReflexive`, and none of the four
  proofs uses completeness.
* The proofs use reflexivity only through Theorem 2.7.5: every bounded sequence has a weakly
  convergent subsequence. This property is the class `WeaklySeqCompactSpace` of
  `Numlib.Variational.WeakMinimization`, in which the backbone states the existence theorems, and
  instance search derives it from reflexivity by `WeaklySeqCompactSpace.of_isReflexive`. The source
  says the same before its Theorem 3.3.13: "the reflexivity of $V$ is used only to extract a weakly
  convergent subsequence from a bounded sequence in $K$". Every Hilbert space is reflexive, by
  `NormedSpace.instIsReflexiveOfInnerProductSpace`.
* The predicates `LowerSemicontinuousOn` and `WeakSeqLowerSemicontinuousOn` are phrased as "for
  every $y < f(u)$, eventually $y < f(v_n)$" instead of $f(u) \le \liminf_n f(v_n)$. The two agree
  when $(f(v_n))$ is bounded below. The private lemma `le_liminf_ereal_iff` converts between the two
  forms.
* Coercivity in the sense of Definition 3.3.9 is the backbone's `IsCoerciveFunctionalOn`, not the
  backbone's `IsCoercive`. The latter is the condition $\operatorname{re} (A v, v) \ge c \|v\|^2$ on
  an operator or a sesquilinear form, which the source calls strongly monotone.
* Some hypotheses of the source are kept although the proofs do not use them: the convexity of $K$
  and $f$ in Theorem 3.3.13, the convexity of $K$ in Theorem 3.3.15, and the nonemptiness of $K$ in
  Theorem 3.3.21.

## Deviations from the source

* **Definition 3.3.4** (reading). The limit inferior $\liminf_n f(v_n)$ is taken in the extended
  reals `EReal`. Lean's real `liminf` is $0$ for a sequence that is not bounded below, and with it
  Theorem 3.3.8 would be false. See `AtkinsonHan.Chapter03.definition_3_3_4`.

## Not formalized

* **Example 3.3.17 in $L^p(a, b)$.** Only the case of $C[a, b]$ is stated.
-/

open Filter Topology Bornology

namespace AtkinsonHan.Chapter03

/-! ### Best approximation in the form (3.3.3) -/

section Iinf

variable {V : Type*} [SeminormedAddCommGroup V]

/-- **Equation (3.3.3)** of [han2009theoretical]. Let $K$ be a subset of a seminormed group $V$ and
let $u, v \in V$. Then $v$ is a best approximation of $u$ from $K$ in the sense of the
backbone's `IsBestApprox` if and only if
$$v \in K \quad \text{and} \quad \|u - v\| = \inf_{w \in K} \|u - w\|.$$
-/
theorem isBestApprox_iff_norm_eq_iInf (K : Set V) (u v : V) :
    IsBestApprox K u v ↔ v ∈ K ∧ ‖u - v‖ = ⨅ w : K, ‖u - (w : V)‖ := by
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    rw [h.norm_sub_eq_infDist, Metric.infDist_eq_iInf]
    simp [dist_eq_norm]
  · rintro ⟨hv, hnorm⟩
    refine (isBestApprox_iff_norm_sub_eq_infDist hv).2 ?_
    rw [hnorm, Metric.infDist_eq_iInf]
    simp [dist_eq_norm]

end Iinf

/-! ### Definitions 3.3.1 and 3.3.2: convex sets and convex functionals -/

section Convexity

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **Definition 3.3.1** of [han2009theoretical]. A subset $K$ of a real normed space $V$ is
**convex** if
$$\lambda u + (1 - \lambda) v \in K \quad \text{for all } u, v \in K \text{ and } \lambda \in
  (0, 1).$$

Mathlib's `Convex ℝ K` uses the closed interval $[0, 1]$; the two conditions agree by
`AtkinsonHan.Chapter03.definition_3_3_1_iff`. The convex-combination statement (3.3.1) is
`AtkinsonHan.Chapter03.definition_3_3_1_sum`. -/
def definition_3_3_1 {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (K : Set V) : Prop :=
  ∀ u ∈ K, ∀ v ∈ K, ∀ lam : ℝ, 0 < lam → lam < 1 → lam • u + (1 - lam) • v ∈ K

/-- **Definition 3.3.1** of [han2009theoretical], identification. A subset $K$ of a real normed
space is convex in the sense of Definition 3.3.1 if and only if it is convex in Mathlib's sense
`Convex ℝ K`: the open interval $(0, 1)$ of the source and the closed interval $[0, 1]$ of
Mathlib describe the same sets. -/
theorem definition_3_3_1_iff (K : Set V) : definition_3_3_1 K ↔ Convex ℝ K := by
  rw [convex_iff_openSegment_subset]
  constructor
  · rintro h u hu v hv z ⟨a, b, ha, hb, hab, rfl⟩
    have hb' : b = 1 - a := by linarith
    subst hb'
    exact h u hu v hv a ha (by linarith)
  · intro h u hu v hv lam h0 h1
    exact h hu hv ⟨lam, 1 - lam, h0, by linarith, by ring, rfl⟩

/-- **Equation (3.3.1)** of [han2009theoretical]. Let $K$ be a convex subset of a real normed space,
let $v_1, \dots, v_n \in K$ and let $\lambda_1, \dots, \lambda_n \ge 0$ with
$\sum_i \lambda_i = 1$. Then
$$\sum_{i=1}^n \lambda_i v_i \in K.$$
-/
theorem definition_3_3_1_sum {K : Set V} (hK : definition_3_3_1 K) {n : ℕ} {lam : Fin n → ℝ}
    {v : Fin n → V} (hlam : ∀ i, 0 ≤ lam i) (hsum : ∑ i, lam i = 1) (hv : ∀ i, v i ∈ K) :
    ∑ i, lam i • v i ∈ K :=
  ((definition_3_3_1_iff K).mp hK).sum_mem (fun i _ => hlam i) hsum fun i _ => hv i

/-- **Definition 3.3.2** of [han2009theoretical]. Let $K$ be a subset of a real normed space $V$. A
functional $f : V \to \mathbb{R}$ is **convex** on $K$ if
$$f(\lambda u + (1 - \lambda) v) \le \lambda f(u) + (1 - \lambda) f(v) \quad \text{for all } u,
  v \in K \text{ and } \lambda \in [0, 1].$$

The source defines $f$ on a convex set $K$ only; here $f$ is defined on all of $V$ and its
values outside $K$ play no part. Mathlib's `ConvexOn ℝ K f` also contains the convexity of $K$;
`AtkinsonHan.Chapter03.definition_3_3_2_iff` is the identification for a convex $K$. -/
def definition_3_3_2 {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (K : Set V)
    (f : V → ℝ) : Prop :=
  ∀ u ∈ K, ∀ v ∈ K, ∀ lam : ℝ, 0 ≤ lam → lam ≤ 1 →
    f (lam • u + (1 - lam) • v) ≤ lam * f u + (1 - lam) * f v

/-- **Definition 3.3.2** of [han2009theoretical], strict convexity. Let $K$ be a subset of a real
normed space $V$. A functional $f : V \to \mathbb{R}$ is **strictly convex** on $K$ if
$$f(\lambda u + (1 - \lambda) v) < \lambda f(u) + (1 - \lambda) f(v) \quad \text{for all } u, v
  \in K \text{ with } u \neq v \text{ and } \lambda \in (0, 1).$$

By `AtkinsonHan.Chapter03.definition_3_3_2_strict_iff` this is Mathlib's `StrictConvexOn ℝ K f`
for a convex $K$. -/
def definition_3_3_2_strict {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (K : Set V)
    (f : V → ℝ) : Prop :=
  ∀ u ∈ K, ∀ v ∈ K, u ≠ v → ∀ lam : ℝ, 0 < lam → lam < 1 →
    f (lam • u + (1 - lam) • v) < lam * f u + (1 - lam) * f v

/-- **Definition 3.3.2** of [han2009theoretical], identification. Let $K$ be a convex subset of a
real normed space and let $f : V \to \mathbb{R}$. Then $f$ is convex on $K$ in the sense of
Definition 3.3.2 if and only if `ConvexOn ℝ K f`, the form in which
`AtkinsonHan.Chapter03.theorem_3_3_12` and `AtkinsonHan.Chapter03.theorem_3_3_11_weakSeqLsc` are
stated. -/
theorem definition_3_3_2_iff {K : Set V} (hK : definition_3_3_1 K) (f : V → ℝ) :
    definition_3_3_2 K f ↔ ConvexOn ℝ K f := by
  refine ⟨fun h => ⟨(definition_3_3_1_iff K).mp hK, ?_⟩, fun h u hu v hv lam h0 h1 => ?_⟩
  · rintro u hu v hv a b ha hb hab
    have hb' : b = 1 - a := by linarith
    subst hb'
    exact h u hu v hv a ha (by linarith)
  · simpa using h.2 hu hv h0 (by linarith : (0 : ℝ) ≤ 1 - lam) (by ring)

/-- **Definition 3.3.2** of [han2009theoretical], identification of strict convexity. Let $K$ be a
convex subset of a real normed space and let $f : V \to \mathbb{R}$. Then $f$ is strictly convex
on $K$ in the sense of Definition 3.3.2 if and only if `StrictConvexOn ℝ K f`, the form in which
`AtkinsonHan.Chapter03.theorem_3_3_13_unique` is stated. -/
theorem definition_3_3_2_strict_iff {K : Set V} (hK : definition_3_3_1 K) (f : V → ℝ) :
    definition_3_3_2_strict K f ↔ StrictConvexOn ℝ K f := by
  refine ⟨fun h => ⟨(definition_3_3_1_iff K).mp hK, ?_⟩,
    fun h u hu v hv hne lam h0 h1 => ?_⟩
  · rintro u hu v hv hne a b ha hb hab
    have hb' : b = 1 - a := by linarith
    subst hb'
    exact h u hu v hv hne a ha (by linarith)
  · simpa using h.2 hu hv hne h0 (by linarith : (0 : ℝ) < 1 - lam) (by ring)

end Convexity

/-! ### Definition 3.3.6 and strictly normed spaces -/

section RealDefs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Definition 3.3.6** of [han2009theoretical], separated sets. Two subsets $A$ and $B$ of a real
normed space $E$ are **separated** if there are a nonzero bounded linear functional $\ell$ on
$E$ and a number $\alpha \in \mathbb{R}$ with
$$\ell(u) \le \alpha \quad \text{for all } u \in A, \qquad \ell(v) \ge \alpha \quad \text{for
  all } v \in B.$$
-/
def AreSeparated (A B : Set E) : Prop :=
  ∃ (ℓ : StrongDual ℝ E) (α : ℝ), ℓ ≠ 0 ∧ (∀ u ∈ A, ℓ u ≤ α) ∧ ∀ v ∈ B, α ≤ ℓ v

/-- **Definition 3.3.6** of [han2009theoretical], strictly separated sets. Two subsets $A$ and $B$
of a real normed space $E$ are **strictly separated** if there are a nonzero bounded linear
functional $\ell$ on $E$ and a number $\alpha \in \mathbb{R}$ with
$$\ell(u) < \alpha \quad \text{for all } u \in A, \qquad \ell(v) > \alpha \quad \text{for all }
  v \in B.$$
-/
def AreStrictlySeparated (A B : Set E) : Prop :=
  ∃ (ℓ : StrongDual ℝ E) (α : ℝ), ℓ ≠ 0 ∧ (∀ u ∈ A, ℓ u < α) ∧ ∀ v ∈ B, α < ℓ v

/-- Let $A$ and $B$ be nonempty subsets of a real normed space. If there are a bounded linear
functional $f$ and numbers $u < v$ with $f < u$ on $A$ and $f > v$ on $B$, then $A$ and $B$ are
strictly separated in the sense of Definition 3.3.6, with $\alpha = (u + v)/2$.

This is the form of the conclusion of Mathlib's geometric Hahn–Banach theorems. The converse
fails: in $\mathbb{R}$, the sets $A = (-\infty, 0)$ and $B = (0, \infty)$ are strictly separated
by $\ell = \mathrm{id}$ and $\alpha = 0$, but there are no $u < v$ with $\ell < u$ on $A$ and
$\ell > v$ on $B$. -/
theorem areStrictlySeparated_of_exists {A B : Set E} (hA : A.Nonempty) (hB : B.Nonempty)
    (h : ∃ (f : StrongDual ℝ E) (u v : ℝ), (∀ a ∈ A, f a < u) ∧ u < v ∧ ∀ b ∈ B, v < f b) :
    AreStrictlySeparated A B := by
  obtain ⟨f, u, v, hu, huv, hv⟩ := h
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  refine ⟨f, (u + v) / 2, ?_, fun x hx => (hu x hx).trans (by linarith), fun y hy => ?_⟩
  · rintro rfl
    have h₁ : (0 : ℝ) < u := by simpa using hu a ha
    have h₂ : v < (0 : ℝ) := by simpa using hv b hb
    linarith
  · exact lt_of_lt_of_le (by linarith) (hv y hy).le

/-- Two strictly separated sets in a real normed space are separated, in the sense of Definition
3.3.6. -/
theorem AreStrictlySeparated.areSeparated {A B : Set E} (h : AreStrictlySeparated A B) :
    AreSeparated A B := by
  obtain ⟨ℓ, α, h0, hA, hB⟩ := h
  exact ⟨ℓ, α, h0, fun u hu => (hA u hu).le, fun v hv => (hB v hv).le⟩

/-- **Section 3.3.4** of [han2009theoretical], definition of a strictly normed space. A real normed
space $E$ is **strictly normed** if, for all $u, v \in E$ with $u \neq 0$, the equality
$\|u + v\| = \|u\| + \|v\|$ implies $v = \lambda u$ for some $\lambda \ge 0$. -/
def IsStrictlyNormed (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] : Prop :=
  ∀ u v : E, ‖u + v‖ = ‖u‖ + ‖v‖ → u ≠ 0 → ∃ lam : ℝ, 0 ≤ lam ∧ v = lam • u

/-- A real normed space is strictly normed in the sense of §3.3.4 if and only if it is strictly
convex in Mathlib's sense `StrictConvexSpace ℝ E`. So the backbone's `IsBestApprox.unique`
applies to strictly normed spaces. -/
theorem isStrictlyNormed_iff_strictConvexSpace :
    IsStrictlyNormed E ↔ StrictConvexSpace ℝ E := by
  constructor
  · intro h
    refine StrictConvexSpace.of_norm_add fun x y hx hy hxy => ?_
    have hx0 : x ≠ 0 := by
      intro hx0
      rw [hx0, norm_zero] at hx
      exact zero_ne_one hx
    obtain ⟨lam, hlam, rfl⟩ := h x y (by rw [hxy, hx, hy]; norm_num) hx0
    exact SameRay.sameRay_nonneg_smul_right x hlam
  · intro h u v hnorm hu
    obtain ⟨r, hr, hrv⟩ := (sameRay_iff_norm_add.2 hnorm).exists_nonneg_left hu
    exact ⟨r, hr, hrv.symm⟩

end RealDefs

/-! ### Definitions 3.3.3 and 3.3.4: closed sets and lower semicontinuous functionals -/

section Closedness

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **Definition 3.3.3** of [han2009theoretical]. A subset $K$ of a real normed space $V$ is
**closed** if $v_n \in K$ for all $n$ and $v_n \to v$ imply $v \in K$.

The convergence $v_n \to v$ is Definition 1.2.8, `AtkinsonHan.Chapter01.definition_1_2_8`. By
`AtkinsonHan.Chapter03.definition_3_3_3_iff` this is Mathlib's `IsClosed`, because the
sequential and the topological notions agree in a metric space. -/
def definition_3_3_3 {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (K : Set V) : Prop :=
  ∀ (v : ℕ → V) (u : V), (∀ n, v n ∈ K) → Chapter01.definition_1_2_8 v u → u ∈ K

/-- **Definition 3.3.3** of [han2009theoretical], weak closedness. A subset $K$ of a real normed
space $V$ is **weakly closed** if $v_n \in K$ for all $n$ and $v_n \rightharpoonup v$ imply
$v \in K$.

The weak convergence $v_n \rightharpoonup v$ is Definition 2.7.1,
`AtkinsonHan.Chapter02.WeakSeqTendsto`. By `AtkinsonHan.Chapter03.definition_3_3_3_weak_iff`
this is the backbone's `IsWeakSeqClosed`, which `AtkinsonHan.Chapter03.theorem_3_3_8`,
`AtkinsonHan.Chapter03.theorem_3_3_10` and
`AtkinsonHan.Chapter03.theorem_3_3_11_isWeakSeqClosed` use. -/
def definition_3_3_3_weak {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (K : Set V) :
    Prop :=
  ∀ (v : ℕ → V) (u : V), (∀ n, v n ∈ K) → Chapter02.WeakSeqTendsto ℝ v u → u ∈ K

/-- **Definition 3.3.3** of [han2009theoretical], identification. A subset $K$ of a real normed
space is closed in the sense of Definition 3.3.3 if and only if `IsClosed K`. -/
theorem definition_3_3_3_iff (K : Set V) : definition_3_3_3 K ↔ IsClosed K := by
  rw [← isSeqClosed_iff_isClosed]
  simp only [definition_3_3_3, Chapter01.definition_1_2_8_iff]
  exact ⟨fun h _ _ hv hu => h _ _ hv hu, fun h v u hv hu => h hv hu⟩

/-- **Definition 3.3.3** of [han2009theoretical], identification of weak closedness. A subset $K$ of
a real normed space is weakly closed in the sense of Definition 3.3.3 if and only if the
backbone's `IsWeakSeqClosed K` holds. -/
theorem definition_3_3_3_weak_iff (K : Set V) :
    definition_3_3_3_weak K ↔ IsWeakSeqClosed K :=
  Iff.rfl

/-- **Definition 3.3.3** of [han2009theoretical], the remark after the definition. A weakly closed
subset of a real normed space is closed, because a sequence that converges in norm converges
weakly to the same limit.

The converse fails in infinite dimensions. -/
theorem definition_3_3_3_of_weak {K : Set V} (h : definition_3_3_3_weak K) :
    definition_3_3_3 K :=
  fun v u hv hu =>
    h v u hv (WeakSeqTendsto.of_tendsto ((Chapter01.definition_1_2_8_iff v u).mp hu))

/-- **Definition 3.3.4** of [han2009theoretical]. Let $K$ be a subset of a real normed space $V$. A
functional $f : V \to \mathbb{R}$ is **(sequentially) lower semicontinuous** on $K$ if
$$v_n \in K, \quad v \in K, \quad v_n \to v \implies f(v) \le \liminf_{n \to \infty} f(v_n).$$

**Reading.** The limit inferior is taken in the extended reals `EReal`, which is what the source
means. Lean's real `liminf` is $0$ for a sequence that is not bounded below, and with it Theorem
3.3.8 would be false: on $K = [0, 1]$ the function with $f(0) = 0$ and $f(x) = -1/x$ for $x > 0$
satisfies the literal real condition and has no minimum.

The convergence $v_n \to v$ is Definition 1.2.8. By `AtkinsonHan.Chapter03.definition_3_3_4_iff`
this is Mathlib's `LowerSemicontinuousOn`. -/
def definition_3_3_4 {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (K : Set V)
    (f : V → ℝ) : Prop :=
  ∀ (v : ℕ → V) (u : V), (∀ n, v n ∈ K) → u ∈ K → Chapter01.definition_1_2_8 v u →
    (f u : EReal) ≤ liminf (fun n => (f (v n) : EReal)) atTop

/-- **Definition 3.3.4** of [han2009theoretical], weak lower semicontinuity. Let $K$ be a subset of
a real normed space $V$. A functional $f : V \to \mathbb{R}$ is **weakly sequentially lower
semicontinuous** on $K$ if
$$v_n \in K, \quad v \in K, \quad v_n \rightharpoonup v \implies f(v) \le \liminf_{n \to \infty}
  f(v_n).$$

**Reading.** As in `AtkinsonHan.Chapter03.definition_3_3_4`, the limit inferior is taken in
`EReal`.

The weak convergence is Definition 2.7.1. By `AtkinsonHan.Chapter03.definition_3_3_4_weak_iff`
this is the backbone's `WeakSeqLowerSemicontinuousOn`, which
`AtkinsonHan.Chapter03.theorem_3_3_8`, `AtkinsonHan.Chapter03.theorem_3_3_10` and
`AtkinsonHan.Chapter03.theorem_3_3_11_weakSeqLsc` use. -/
def definition_3_3_4_weak {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (K : Set V)
    (f : V → ℝ) : Prop :=
  ∀ (v : ℕ → V) (u : V), (∀ n, v n ∈ K) → u ∈ K → Chapter02.WeakSeqTendsto ℝ v u →
    (f u : EReal) ≤ liminf (fun n => (f (v n) : EReal)) atTop

/-- For a real sequence $(g_n)$ and $c \in \mathbb{R}$: $c \le \liminf_n g_n$ in `EReal` if and only
if for every $y < c$, eventually $y < g_n$. -/
private theorem le_liminf_ereal_iff {g : ℕ → ℝ} {c : ℝ} :
    ((c : EReal) ≤ liminf (fun n => (g n : EReal)) atTop) ↔ ∀ y < c, ∀ᶠ n in atTop, y < g n := by
  constructor
  · intro h y hy
    have hy' : (y : EReal) < liminf (fun n => (g n : EReal)) atTop :=
      lt_of_lt_of_le (by exact_mod_cast hy) h
    filter_upwards [eventually_lt_of_lt_liminf hy'] with n hn
    exact_mod_cast hn
  · intro h
    by_contra hc
    rw [not_le] at hc
    obtain ⟨y, hy1, hy2⟩ := EReal.exists_between_coe_real hc
    have hylt : y < c := by exact_mod_cast hy2
    have := h y hylt
    have hle : (y : EReal) ≤ liminf (fun n => (g n : EReal)) atTop := by
      refine le_liminf_of_le ?_ ?_
      · exact isCoboundedUnder_ge_of_le _ (fun _ => le_top)
      · filter_upwards [this] with n hn
        exact_mod_cast hn.le
    exact absurd hle (not_le.mpr hy1)

/-- **Definition 3.3.4** of [han2009theoretical], identification. A functional $f$ is lower
semicontinuous on $K$ in the sense of Definition 3.3.4 if and only if
`LowerSemicontinuousOn f K`: in a metric space the sequential and the topological notions agree. -/
theorem definition_3_3_4_iff (K : Set V) (f : V → ℝ) :
    definition_3_3_4 K f ↔ LowerSemicontinuousOn f K := by
  constructor
  · intro h u hu y hy
    by_contra hcon
    have hne : (𝓝[K] u).NeBot := mem_closure_iff_nhdsWithin_neBot.mp (subset_closure hu)
    have h1 : ∃ᶠ z in 𝓝[K] u, ¬ y < f z := by rwa [Filter.not_eventually] at hcon
    have hfreq : ∃ᶠ z in 𝓝[K] u, z ∈ K ∧ f z ≤ y :=
      (h1.and_eventually self_mem_nhdsWithin).mono fun z hz => ⟨hz.2, not_lt.mp hz.1⟩
    obtain ⟨v, hvt, hv⟩ := exists_seq_forall_of_frequently hfreq
    have hK : ∀ n, v n ∈ K := fun n => (hv n).1
    have hlim : Chapter01.definition_1_2_8 v u :=
      (Chapter01.definition_1_2_8_iff v u).mpr (hvt.mono_right nhdsWithin_le_nhds)
    obtain ⟨n, hn⟩ := ((le_liminf_ereal_iff.mp (h v u hK hu hlim)) y hy).exists
    exact absurd hn (not_lt.mpr (hv n).2)
  · intro h v u hv hu hlim
    refine le_liminf_ereal_iff.mpr fun y hy => ?_
    have hwithin : Tendsto v atTop (𝓝[K] u) :=
      tendsto_nhdsWithin_iff.mpr ⟨(Chapter01.definition_1_2_8_iff v u).mp hlim,
        Eventually.of_forall hv⟩
    exact hwithin.eventually (h u hu y hy)

/-- **Definition 3.3.4** of [han2009theoretical], identification of weak lower semicontinuity. A
functional $f$ is weakly sequentially lower semicontinuous on $K$ in the sense of Definition
3.3.4 if and only if the backbone's `WeakSeqLowerSemicontinuousOn f K` holds. -/
theorem definition_3_3_4_weak_iff (K : Set V) (f : V → ℝ) :
    definition_3_3_4_weak K f ↔ WeakSeqLowerSemicontinuousOn f K := by
  constructor
  · intro h v u hv hu hweak
    exact le_liminf_ereal_iff.mp (h v u hv hu hweak)
  · intro h v u hv hu hweak
    exact le_liminf_ereal_iff.mpr fun y hy => h v u hv hu hweak y hy

end Closedness

/-! ### Example 3.3.5: weak lower semicontinuity of the norm -/

section WeakLsc

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- **Example 3.3.5** of [han2009theoretical]. Let $V$ be a normed space over $\mathbb{K}$. If
$v_n \rightharpoonup u$ in $V$, then
$$\|u\| \le \liminf_{n \to \infty} \|v_n\|.$$
So the norm is weakly sequentially lower semicontinuous.

The source proves the same statement as Exercise 2.7.2, which is
`AtkinsonHan.Chapter02.exercise_2_7_2`; this declaration restates it. The limit inferior is the
real `Filter.liminf`; a weakly convergent sequence is bounded, so it is a genuine limit
inferior. -/
theorem example_3_3_5 (v : ℕ → V) (u : V) (hweak : Chapter02.WeakSeqTendsto 𝕜 v u) :
    ‖u‖ ≤ liminf (fun n => ‖v n‖) atTop :=
  Chapter02.exercise_2_7_2 hweak

end WeakLsc

/-! ### Theorem 3.3.7: strict separation -/

section Separation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Theorem 3.3.7** of [han2009theoretical]. Let $A$ and $B$ be nonempty disjoint convex subsets
of a real normed space $E$, with $A$ compact and $B$ closed. Then $A$ and $B$ are strictly
separated in the sense of Definition 3.3.6. -/
theorem theorem_3_3_7 {A B : Set E} (hA : Convex ℝ A) (hB : Convex ℝ B) (hAne : A.Nonempty)
    (hBne : B.Nonempty) (hdisj : Disjoint A B) (hAc : IsCompact A) (hBc : IsClosed B) :
    AreStrictlySeparated A B :=
  areStrictlySeparated_of_exists hAne hBne
    (geometric_hahn_banach_compact_closed hA hAc hB hBc hdisj)

/-- **Theorem 3.3.7** of [han2009theoretical], with the roles exchanged. Let $A$ and $B$ be nonempty
disjoint convex subsets of a real normed space $E$, with $A$ closed and $B$ compact. Then $A$
and $B$ are strictly separated in the sense of Definition 3.3.6. -/
theorem theorem_3_3_7' {A B : Set E} (hA : Convex ℝ A) (hB : Convex ℝ B) (hAne : A.Nonempty)
    (hBne : B.Nonempty) (hdisj : Disjoint A B) (hAc : IsClosed A) (hBc : IsCompact B) :
    AreStrictlySeparated A B :=
  areStrictlySeparated_of_exists hAne hBne
    (geometric_hahn_banach_closed_compact hA hAc hB hBc hdisj)

end Separation

/-! ### Theorems 3.3.8–3.3.14: minimizers in a reflexive Banach space -/

section Reflexive

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **Theorem 3.3.8** of [han2009theoretical]. Let $V$ be a real reflexive Banach space, let
$K \subseteq V$ be nonempty, bounded and weakly closed, and let $f : V \to \mathbb{R}$ be weakly
sequentially lower semicontinuous on $K$. Then there is $u \in K$ with
$$f(u) = \inf_{v \in K} f(v).$$

Reflexivity is `[NormedSpace.IsReflexive ℝ V]`, which is Definition 2.7.4 by
`AtkinsonHan.Chapter02.definition_2_7_4_iff_isReflexive`. The completeness of $V$ needs no
hypothesis of its own, since a reflexive space is complete by
`NormedSpace.completeSpace_of_isReflexive`; the proof does not use completeness in any case.
Weakly closed is `IsWeakSeqClosed`, the sequential Definition 3.3.3, and the minimizer is
`IsMinOn f K u`. The proof uses reflexivity only through Theorem 2.7.5, by way of the class
`WeaklySeqCompactSpace` and the instance `WeaklySeqCompactSpace.of_isReflexive`. -/
theorem theorem_3_3_8 [NormedSpace.IsReflexive ℝ V] {K : Set V} {f : V → ℝ}
    (hne : K.Nonempty) (hbd : IsBounded K) (hKc : IsWeakSeqClosed K)
    (hf : WeakSeqLowerSemicontinuousOn f K) : ∃ u ∈ K, IsMinOn f K u :=
  exists_isMinOn_of_isWeakSeqClosed hne hbd hKc hf

/-- **Definition 3.3.9** of [han2009theoretical]. Let $K$ be a subset of a real normed space $V$. A
functional $f : V \to \mathbb{R}$ is **coercive over** $K$ if
$$f(v) \to \infty \quad \text{as } \|v\| \to \infty, \ v \in K.$$

The limit is `Filter.Tendsto f (Filter.comap norm Filter.atTop ⊓ Filter.principal K)
Filter.atTop`. If $K$ is bounded, every functional is coercive over $K$. By
`AtkinsonHan.Chapter03.definition_3_3_9_iff` this is the backbone's `IsCoerciveFunctionalOn`,
which `AtkinsonHan.Chapter03.theorem_3_3_10` and `AtkinsonHan.Chapter03.theorem_3_3_12` use. It
is not the backbone's `IsCoercive`, the condition $\operatorname{re} (A v, v) \ge c \|v\|^2$ on
an operator or a sesquilinear form, which the source calls strongly monotone. -/
def definition_3_3_9 {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (K : Set V)
    (f : V → ℝ) : Prop :=
  Tendsto f (comap norm atTop ⊓ 𝓟 K) atTop

/-- **Definition 3.3.9** of [han2009theoretical], identification. A functional $f$ is coercive over
$K$ if and only if for every $M \in \mathbb{R}$ there is $R \in \mathbb{R}$ with $f(v) \ge M$
for all $v \in K$ with $\|v\| \ge R$. The right-hand side is the backbone's
`IsCoerciveFunctionalOn f K`. -/
theorem definition_3_3_9_iff (K : Set V) (f : V → ℝ) :
    definition_3_3_9 K f ↔ IsCoerciveFunctionalOn f K := by
  simp only [definition_3_3_9, IsCoerciveFunctionalOn, tendsto_atTop, eventually_inf_principal,
    eventually_comap, eventually_atTop]
  refine ⟨fun h M => ?_, fun h M => ?_⟩
  · obtain ⟨R, hR⟩ := h M
    exact ⟨R, fun x hx hxR => hR ‖x‖ hxR x rfl hx⟩
  · obtain ⟨R, hR⟩ := h M
    exact ⟨R, fun r hr x hx hxK => hR x hxK (hx ▸ hr)⟩

/-- **Theorem 3.3.10** of [han2009theoretical]. Let $V$ be a real reflexive Banach space, let
$K \subseteq V$ be nonempty and weakly closed, and let $f : V \to \mathbb{R}$ be weakly
sequentially lower semicontinuous on $K$ and coercive over $K$. Then there is $u \in K$ with
$$f(u) = \inf_{v \in K} f(v).$$

The hypotheses on $V$ and $K$ are read as in `AtkinsonHan.Chapter03.theorem_3_3_8`. The proof
restricts the problem to the sublevel set $\{v \in K : f(v) \le f(v_0)\}$, which is bounded
because $f$ is coercive. -/
theorem theorem_3_3_10 [NormedSpace.IsReflexive ℝ V] {K : Set V} {f : V → ℝ}
    (hne : K.Nonempty) (hKc : IsWeakSeqClosed K) (hf : WeakSeqLowerSemicontinuousOn f K)
    (hcoer : IsCoerciveFunctionalOn f K) : ∃ u ∈ K, IsMinOn f K u :=
  exists_isMinOn_of_isCoerciveFunctionalOn hne hKc hf hcoer

/-- **Theorem 3.3.11** of [han2009theoretical] (Mazur's lemma). Let $V$ be a real normed space and
let $v_n \rightharpoonup u$ in $V$. Then there are integers $N(n) \ge n$ and numbers
$\lambda_i^{(n)} \ge 0$ with $\sum_{i=n}^{N(n)} \lambda_i^{(n)} = 1$ such that the convex
combinations
$$u_n = \sum_{i=n}^{N(n)} \lambda_i^{(n)} v_i$$
satisfy $\|u_n - u\| \to 0$.

No reflexivity is needed. -/
theorem theorem_3_3_11 {v : ℕ → V} {u : V} (h : Chapter02.WeakSeqTendsto ℝ v u) :
    ∃ (N : ℕ → ℕ) (lam : ℕ → ℕ → ℝ), (∀ n, n ≤ N n) ∧ (∀ n i, 0 ≤ lam n i) ∧
      (∀ n, ∑ i ∈ Finset.Icc n (N n), lam n i = 1) ∧
      Tendsto (fun n => ∑ i ∈ Finset.Icc n (N n), lam n i • v i) atTop (𝓝 u) :=
  exists_seq_convexCombination_tendsto h

/-- **Theorem 3.3.11** of [han2009theoretical], first corollary. A closed convex subset $K$ of a
real normed space is weakly closed.

So the weak hypothesis on $K$ in Theorems 3.3.8 and 3.3.10 follows from the ordinary one. Weakly
closed is `IsWeakSeqClosed`, the sequential Definition 3.3.3. -/
theorem theorem_3_3_11_isWeakSeqClosed {K : Set V} (hconv : Convex ℝ K) (hcl : IsClosed K) :
    IsWeakSeqClosed K :=
  hconv.isWeakSeqClosed hcl

/-- **Theorem 3.3.11** of [han2009theoretical], second corollary. Let $K$ be a subset of a real
normed space and let $f$ be convex and lower semicontinuous on $K$. Then $f$ is weakly
sequentially lower semicontinuous on $K$.

The proof uses that the sublevel sets of $f$ are convex. Convexity of $f$ on $K$ is
`ConvexOn ℝ K f`, which includes the convexity of $K$. -/
theorem theorem_3_3_11_weakSeqLsc {K : Set V} {f : V → ℝ} (hf : ConvexOn ℝ K f)
    (hlsc : LowerSemicontinuousOn f K) : WeakSeqLowerSemicontinuousOn f K :=
  hf.weakSeqLowerSemicontinuousOn hlsc

/-- **Theorem 3.3.12** of [han2009theoretical]. Let $V$ be a real reflexive Banach space, let
$K \subseteq V$ be nonempty, closed and convex, and let $f : V \to \mathbb{R}$ be convex and
lower semicontinuous on $K$. If $K$ is bounded or $f$ is coercive over $K$, then there is
$u \in K$ with
$$f(u) = \inf_{v \in K} f(v).$$

All hypotheses are for the norm topology. The two corollaries of Mazur's lemma convert them to
the weak hypotheses of Theorems 3.3.8 and 3.3.10. `AtkinsonHan.Chapter03.theorem_3_3_13` is the
finite-dimensional counterpart, and `AtkinsonHan.Chapter03.theorem_3_3_13_unique` is the
uniqueness clause of both. -/
theorem theorem_3_3_12 [NormedSpace.IsReflexive ℝ V] {K : Set V} {f : V → ℝ}
    (hne : K.Nonempty) (hcl : IsClosed K) (hconv : Convex ℝ K) (hf : ConvexOn ℝ K f)
    (hlsc : LowerSemicontinuousOn f K)
    (h : IsBounded K ∨ IsCoerciveFunctionalOn f K) : ∃ u ∈ K, IsMinOn f K u :=
  exists_isMinOn_of_convexOn hne hcl hconv hf hlsc h

/-- **Theorem 3.3.14** of [han2009theoretical]. Let $V$ be a real reflexive Banach space and let
$K \subseteq V$ be nonempty, closed and convex. Then every $u \in V$ has a best approximation
$\hat u$ from $K$.

The function $v \mapsto \|u - v\|$ is convex, continuous and coercive, so this is the coercive
case of Theorem 3.3.12. The finite-dimensional counterpart is
`AtkinsonHan.Chapter03.theorem_3_3_15`, and in a Hilbert space the result is
`AtkinsonHan.Chapter03.theorem_3_4_3`. -/
theorem theorem_3_3_14 [NormedSpace.IsReflexive ℝ V] {K : Set V} (hne : K.Nonempty)
    (hcl : IsClosed K) (hconv : Convex ℝ K) (u : V) : ∃ uhat, IsBestApprox K u uhat :=
  exists_isBestApprox_of_convex hne hcl hconv u

end Reflexive

/-! ### Theorem 3.3.13: minimizers on finite-dimensional closed sets -/

section Minimization

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]

set_option linter.unusedVariables false in
/-- **Theorem 3.3.13** of [han2009theoretical]. Let $V$ be a normed space over $\mathbb{K}$, let $S$
be a finite-dimensional subspace of $V$, and let $K \subseteq S$ be nonempty, closed and convex.
Let $f : V \to \mathbb{R}$ be convex and lower semicontinuous on $K$. If $K$ is bounded or $f$
is coercive over $K$, then there is $u \in K$ with
$$f(u) = \inf_{v \in K} f(v).$$

The convexity hypotheses on $K$ and $f$ are kept as in the source; neither the proof of the
source nor this proof uses them. Convexity is over $\mathbb{R}$, so $V$ is also a real normed
space, through `[NormedSpace ℝ V]` and `[IsScalarTower ℝ 𝕜 V]`. -/
theorem theorem_3_3_13 [NormedSpace ℝ V] [IsScalarTower ℝ 𝕜 V] {K : Set V} (S : Submodule 𝕜 V)
    [FiniteDimensional 𝕜 S] (hKS : K ⊆ S) (hcl : IsClosed K) (hconv : Convex ℝ K)
    (hne : K.Nonempty) (f : V → ℝ) (hf : ConvexOn ℝ K f) (hlsc : LowerSemicontinuousOn f K)
    (h : IsBounded K ∨ IsCoerciveFunctionalOn f K) : ∃ u ∈ K, IsMinOn f K u :=
  exists_isMinOn_of_isClosed_of_finiteDimensional S hKS hcl hne hlsc
    (h.elim IsCoerciveFunctionalOn.of_isBounded id)

/-- **Theorem 3.3.13** of [han2009theoretical], uniqueness. Let $K$ be a subset of a real normed
space and let $f$ be strictly convex on $K$. If $u_1, u_2 \in K$ both minimize $f$ over $K$,
then $u_1 = u_2$. -/
theorem theorem_3_3_13_unique [NormedSpace ℝ V] {K : Set V} {f : V → ℝ} (hf : StrictConvexOn ℝ K f)
    {u₁ u₂ : V} (hu₁ : IsMinOn f K u₁) (hu₂ : IsMinOn f K u₂) (h₁ : u₁ ∈ K) (h₂ : u₂ ∈ K) :
    u₁ = u₂ :=
  IsMinOn.eq_of_strictConvexOn hf hu₁ hu₂ h₁ h₂

end Minimization

/-! ### Theorems 3.3.15–3.3.16 and Example 3.3.17: existence of best approximations -/

section Existence

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]

set_option linter.unusedVariables false in
/-- **Theorem 3.3.15** of [han2009theoretical]. Let $V$ be a normed space over $\mathbb{K}$, let $S$
be a finite-dimensional subspace of $V$, and let $K \subseteq S$ be nonempty, closed and convex.
Then every $u \in V$ has a best approximation $\hat u$ from $K$.

The convexity of $K$ is kept as in the source and is not used. Convexity is over $\mathbb{R}$,
as in `AtkinsonHan.Chapter03.theorem_3_3_13`. -/
theorem theorem_3_3_15 [NormedSpace ℝ V] [IsScalarTower ℝ 𝕜 V] {K : Set V} (S : Submodule 𝕜 V)
    [FiniteDimensional 𝕜 S] (hKS : K ⊆ S) (hK : IsClosed K) (hconv : Convex ℝ K)
    (hne : K.Nonempty) (u : V) : ∃ uhat, IsBestApprox K u uhat :=
  exists_isBestApprox_of_isClosed_of_finiteDimensional hK hne S hKS u

/-- **Theorem 3.3.16** of [han2009theoretical]. Let $K$ be a finite-dimensional subspace of a normed
space $V$ over $\mathbb{K}$. Then every $u \in V$ has a best approximation $\hat u$ from $K$. -/
theorem theorem_3_3_16 (K : Submodule 𝕜 V) [FiniteDimensional 𝕜 K] (u : V) :
    ∃ uhat, IsBestApprox (K : Set V) u uhat :=
  exists_isBestApprox_of_finiteDimensional K u

end Existence

section Polynomials

/-- The space $\mathcal{P}_n$ of the restrictions to $[a, b]$ of the real polynomials of degree at
most $n$, as a subspace of $C[a, b]$. -/
noncomputable def polyLE (a b : ℝ) (n : ℕ) : Submodule ℝ C(Set.Icc a b, ℝ) :=
  (Polynomial.degreeLT ℝ (n + 1)).map
    (Polynomial.toContinuousMapOnAlgHom (Set.Icc a b)).toLinearMap

/-- The space $\mathcal{P}_n$ is finite dimensional: it is the image under a linear map of the
finite-dimensional space of polynomials of degree less than $n + 1$. -/
instance (a b : ℝ) (n : ℕ) : FiniteDimensional ℝ (polyLE a b n) := by
  unfold polyLE
  infer_instance

/-- The error of best uniform approximation of $f \in C[a, b]$ from $\mathcal{P}_n$:
$$\rho_n(f) = \inf_{p \in \mathcal{P}_n} \|f - p\|_\infty.$$
-/
noncomputable def rho (a b : ℝ) (n : ℕ) (f : C(Set.Icc a b, ℝ)) : ℝ :=
  ⨅ p : polyLE a b n, ‖f - (p : C(Set.Icc a b, ℝ))‖

/-- If $p$ is a best approximation of $f \in C[a, b]$ from $\mathcal{P}_n$, then
$\|f - p\|_\infty = \rho_n(f)$. -/
theorem rho_eq_norm_sub_of_isBestApprox {a b : ℝ} {n : ℕ} {f p : C(Set.Icc a b, ℝ)}
    (h : IsBestApprox (polyLE a b n : Set C(Set.Icc a b, ℝ)) f p) : ‖f - p‖ = rho a b n f :=
  ((isBestApprox_iff_norm_eq_iInf _ _ _).1 h).2

/-- **Example 3.3.17** of [han2009theoretical]. Let $a, b \in \mathbb{R}$, $n \ge 0$ and
$f \in C[a, b]$. Then $f$ has a best uniform approximation from $\mathcal{P}_n$.

$\mathcal{P}_n$ is a finite-dimensional subspace of $C[a, b]$, so Theorem 3.3.16 applies. The
case of $L^p(a, b)$ in the source is not formalized. -/
theorem example_3_3_17 (a b : ℝ) (n : ℕ) (f : C(Set.Icc a b, ℝ)) :
    ∃ p, IsBestApprox (polyLE a b n : Set C(Set.Icc a b, ℝ)) f p :=
  exists_isBestApprox_of_finiteDimensional (polyLE a b n) f

/-- The space $\mathcal{P}_n$ on $[a, b]$ of this module is the backbone's `polyLE (Set.Icc a b) n`:
the polynomials of degree less than $n + 1$ and those of degree at most $n$ form the same
subspace of $\mathbb{R}[X]$. -/
theorem polyLE_eq (a b : ℝ) (n : ℕ) : polyLE a b n = _root_.polyLE (Set.Icc a b) n := by
  rw [polyLE, _root_.polyLE, Polynomial.degreeLT_succ_eq_degreeLE]

/-- **Theorem 3.3.19** of [han2009theoretical] (Chebyshev equioscillation theorem), existence and
uniqueness. Let $a < b$, $n \ge 0$ and $f \in C[a, b]$. Then $f$ has exactly one best uniform
approximation $\hat p_n$ from $\mathcal{P}_n$:
$$\|f - \hat p_n\|_\infty = \min_{p \in \mathcal{P}_n} \|f - p\|_\infty = \rho_n(f).$$

The proof is in the backbone module `Numlib.Approximation.Chebyshev`. -/
theorem theorem_3_3_19 {a b : ℝ} (hab : a < b) (n : ℕ) (f : C(Set.Icc a b, ℝ)) :
    ∃! p : C(Set.Icc a b, ℝ), IsBestApprox (polyLE a b n : Set C(Set.Icc a b, ℝ)) f p := by
  have : Infinite (Set.Icc a b) := Set.Icc.infinite hab
  rw [polyLE_eq]
  exact existsUnique_isBestApprox_polyLE n f

/-- **Theorem 3.3.19** of [han2009theoretical], the characterization. Let $a < b$, $f \in C[a, b]$
and $p \in \mathcal{P}_n$. Then $p$ is a best uniform approximation of $f$ from $\mathcal{P}_n$
if and only if there are points $a \le x_0 < x_1 < \cdots < x_{n+1} \le b$ and a sign
$\sigma \in \{1, -1\}$ with
$$f(x_j) - p(x_j) = \sigma (-1)^j \|f - p\|_\infty, \qquad j = 0, \dots, n + 1.$$

The condition on the right is the backbone's `Equioscillates (f - p) (n + 2)`. -/
theorem theorem_3_3_19_equioscillates {a b : ℝ} (hab : a < b) {n : ℕ} {f p : C(Set.Icc a b, ℝ)}
    (hp : p ∈ polyLE a b n) :
    IsBestApprox (polyLE a b n : Set C(Set.Icc a b, ℝ)) f p ↔ Equioscillates (f - p) (n + 2) := by
  have : Infinite (Set.Icc a b) := Set.Icc.infinite hab
  rw [polyLE_eq] at hp ⊢
  exact isBestApprox_iff_equioscillates hp

/-- **Theorem 3.3.19** of [han2009theoretical], the alternation in the form of the source. Let
$a < b$, $f \in C[a, b]$, and let $\hat p_n$ be a best uniform approximation of $f$ from
$\mathcal{P}_n$. Then there are points $a \le x_0 < x_1 < \cdots < x_{n+1} \le b$ and a sign
$\sigma \in \{1, -1\}$ with
$$f(x_j) - \hat p_n(x_j) = \sigma (-1)^j \rho_n(f), \qquad j = 0, \dots, n + 1.$$
-/
theorem theorem_3_3_19_alternation {a b : ℝ} (hab : a < b) {n : ℕ} {f p : C(Set.Icc a b, ℝ)}
    (h : IsBestApprox (polyLE a b n : Set C(Set.Icc a b, ℝ)) f p) :
    ∃ (σ : ℝ) (x : Fin (n + 2) → Set.Icc a b), (σ = 1 ∨ σ = -1) ∧
      StrictMono (fun i => (x i : ℝ)) ∧
      ∀ i : Fin (n + 2), f (x i) - p (x i) = σ * (-1) ^ (i : ℕ) * rho a b n f := by
  obtain ⟨σ, x, hσ, hmono, hval⟩ := (theorem_3_3_19_equioscillates hab h.1).1 h
  exact ⟨σ, x, hσ, hmono, fun i => by
    simpa [rho_eq_norm_sub_of_isBestApprox h] using hval i⟩

end Polynomials

/-! ### Theorem 3.3.20: best uniform approximation by trigonometric polynomials -/

section TrigonometricPolynomials

open scoped Real

/-- **Theorem 3.3.20** of [han2009theoretical]. Let $g \in C_p(2\pi)$ and $n \ge 0$. Then there is
exactly one trigonometric polynomial $\hat q_n \in \mathcal{T}_n$ of degree at most $n$ with
$$\|g - \hat q_n\|_\infty = \min_{q \in \mathcal{T}_n} \|g - q\|_\infty.$$

$C_p(2\pi)$ is `C(AddCircle (2 * π), ℝ)`.
$\mathcal{T}_n$ is `trigPolyLE (2 * π) n`.
Existence is Theorem 3.3.16, since $\mathcal{T}_n$ has dimension $2n + 1$. Uniqueness comes from
the Haar condition for the trigonometric polynomials: a nonzero one of degree at most $n$ has at
most $2n$ zeros in a period. -/
theorem theorem_3_3_20 (n : ℕ) (g : C(AddCircle (2 * π), ℝ)) :
    ∃! q : C(AddCircle (2 * π), ℝ),
      IsBestApprox (trigPolyLE (2 * π) n : Set C(AddCircle (2 * π), ℝ)) g q :=
  existsUnique_isBestApprox_trigPolyLE n g

end TrigonometricPolynomials

/-! ### Theorems 3.3.18 and 3.3.21: uniqueness of best approximations -/

section Uniqueness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option linter.unusedVariables false in
/-- **Theorem 3.3.18** of [han2009theoretical]. Let $E$ be a real normed space such that
$v \mapsto \|v\|^p$ is strictly convex on $E$ for some $p \ge 1$, and let $K \subseteq E$ be
convex. Then every $u \in E$ has at most one best approximation from $K$.

The power is the real power `‖v‖ ^ p`. The proof shows that $E$ is strictly convex, by
`StrictConvexSpace.of_strictConvexOn_norm_rpow`, and applies `IsBestApprox.unique`. -/
theorem theorem_3_3_18 {p : ℝ} (hp : 1 ≤ p)
    (hconv : StrictConvexOn ℝ (Set.univ : Set E) fun v : E => ‖v‖ ^ p) {K : Set E}
    (hK : Convex ℝ K) {u v₁ v₂ : E} (h₁ : IsBestApprox K u v₁) (h₂ : IsBestApprox K u v₂) :
    v₁ = v₂ :=
  have : StrictConvexSpace ℝ E := StrictConvexSpace.of_strictConvexOn_norm_rpow hp hconv
  h₁.unique hK h₂

set_option linter.unusedVariables false in
/-- **Theorem 3.3.21** of [han2009theoretical]. Let $E$ be a strictly normed real space and let
$K \subseteq E$ be nonempty and convex. Then every $u \in E$ has at most one best approximation
from $K$.

The nonemptiness of $K$ is kept as in the source and is not used. -/
theorem theorem_3_3_21 (hV : IsStrictlyNormed E) {K : Set E} (hne : K.Nonempty) (hK : Convex ℝ K)
    {u v₁ v₂ : E} (h₁ : IsBestApprox K u v₁) (h₂ : IsBestApprox K u v₂) : v₁ = v₂ :=
  have : StrictConvexSpace ℝ E := isStrictlyNormed_iff_strictConvexSpace.1 hV
  h₁.unique hK h₂

end Uniqueness

/-! ### Exercises 3.3.8 and 3.3.9 -/

section InnerProduct

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- **Exercise 3.3.8** of [han2009theoretical]. In a real inner product space $H$, the function
$v \mapsto \|v\|^2$ is strictly convex. Indeed, for $a + b = 1$,
$$a \|x\|^2 + b \|y\|^2 - \|a x + b y\|^2 = a b \|x - y\|^2.$$
With Theorem 3.3.18 this gives the uniqueness of best approximations from convex sets (Corollary
3.4.2). -/
theorem exercise_3_3_8 : StrictConvexOn ℝ (Set.univ : Set H) fun v : H => ‖v‖ ^ 2 :=
  strictConvexOn_norm_sq

/-- **Exercise 3.3.8** of [han2009theoretical], with a real exponent. In a real inner product space
$H$, the function $v \mapsto \|v\|^2$, with the real power `‖v‖ ^ (2 : ℝ)`, is strictly convex.
This is the form that Theorem 3.3.18 uses, with $p = 2$. -/
theorem exercise_3_3_8_rpow :
    StrictConvexOn ℝ (Set.univ : Set H) fun v : H => ‖v‖ ^ (2 : ℝ) :=
  strictConvexOn_norm_rpow_two

/-- **Exercise 3.3.9** of [han2009theoretical]. A real inner product space is strictly normed. -/
theorem exercise_3_3_9 : IsStrictlyNormed H :=
  isStrictlyNormed_iff_strictConvexSpace.2 inferInstance

end InnerProduct

end AtkinsonHan.Chapter03
