/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Normed.Module.DualSeparable
import Numlib.Analysis.Normed.Module.WeakStarMetrizable
import NumlibSurface.Brezis.Chapter03.Section05

/-!
# Brezis, Section 3.6: Separable spaces

This module formalizes Section 3.6 of [brezis2011functional] for a real Banach space $E$. A metric
space is separable if it has a countable dense subset. Every subset of a separable metric space is
separable (Proposition 3.25). If $E^\star$ is separable, then $E$ is separable (Theorem 3.26), and
$E$ is reflexive and separable if and only if $E^\star$ is (Corollary 3.27). The closed unit ball
$B_{E^\star}$ is metrizable for the weak-∗ topology if and only if $E$ is separable (Theorem 3.28),
and $B_E$ is metrizable for the weak topology if and only if $E^\star$ is separable (Theorem 3.29).
In infinite dimension, neither topology is metrizable on the whole space (Remark 20). As a
consequence, every bounded sequence in the dual of a separable space has a weakly-∗ convergent
subsequence (Corollary 3.30). The module also contains Remark 4 of Section 3.2, whose proof needs
Theorems 3.18 and 3.29.

The proofs use Mathlib's separability instances and `WeakDual.isSeqCompact_closedBall`, and the
backbone modules `Numlib.Analysis.Normed.Module.DualSeparable`,
`Numlib.Analysis.Normed.Module.Reflexive` and `Numlib.Analysis.Normed.Module.WeakStarMetrizable`.
The last module also proves Exercise 3.24, used for the converse of Theorem 3.29, and Exercise 3.8,
used for Remark 20.

## Main definitions

* Section 3.6, definition of a separable space, `Brezis.Chapter03.IsSeparable`: the space has a
  countable dense subset.

## Main results

* Section 3.6, `Brezis.Chapter03.separable_iff`: the definition agrees with Mathlib's
  `TopologicalSpace.SeparableSpace`.
* Proposition 3.25, `Brezis.Chapter03.proposition_3_25`: every subset of a separable metric space is
  separable.
* Theorem 3.26, `Brezis.Chapter03.theorem_3_26`: if $E^\star$ is separable, then $E$ is separable.
* Corollary 3.27, `Brezis.Chapter03.corollary_3_27`: $E$ is reflexive and separable if and only if
  $E^\star$ is reflexive and separable.
* Theorem 3.28, `Brezis.Chapter03.theorem_3_28_mp`, `Brezis.Chapter03.theorem_3_28_mpr` and
  `Brezis.Chapter03.theorem_3_28`: $E$ is separable if and only if $B_{E^\star}$ is metrizable in
  $\sigma(E^\star, E)$.
* Theorem 3.29, `Brezis.Chapter03.theorem_3_29_mp`, `Brezis.Chapter03.theorem_3_29_mpr` and
  `Brezis.Chapter03.theorem_3_29`: $E^\star$ is separable if and only if $B_E$ is metrizable in
  $\sigma(E, E^\star)$.
* Remark 20, `Brezis.Chapter03.remark_3_20`: in infinite dimension, $\sigma(E, E^\star)$ on $E$ and
  $\sigma(E^\star, E)$ on $E^\star$ are not metrizable.
* Corollary 3.30, `Brezis.Chapter03.corollary_3_30`: if $E$ is separable, every bounded sequence in
  $E^\star$ has a weakly-∗ convergent subsequence.
* Remark 4 of Section 3.2, `Brezis.Chapter03.remark_3_4`: in infinite dimension, if $E^\star$ is
  separable or $E$ is reflexive, some sequence of unit vectors converges weakly to $0$.

## Conventions

* Separability of a space $X$ is Mathlib's class `TopologicalSpace.SeparableSpace X`. A subset $F$
  is separable when the subtype `F` is.
* "Metrizable" is `TopologicalSpace.MetrizableSpace` of the subtype. The ball $B_{E^\star}$ with
  $\sigma(E^\star, E)$ is the preimage of `closedBall 0 1` in `WeakDual ℝ E`, and $B_E$ with
  $\sigma(E, E^\star)$ is its image in `WeakSpace ℝ E`.

## Deviations from the source

* **Definition of separability** (generalization). The predicate applies to arbitrary topological
  spaces. See `Brezis.Chapter03.IsSeparable`.

## Not formalized

* **Remark 19, the spaces $L^1$ and $L^\infty$.** These claims are stated in Chapter 4.
-/

open Filter Metric Set Topology

namespace Brezis.Chapter03

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### Separability -/

/-- **Section 3.6** of [brezis2011functional], definition of a separable space. A topological space
$E$ is **separable** if it has a countable dense subset $D$.

**Generalization.** The source makes the definition for a metric space. The predicate applies to
any topological space. -/
def IsSeparable (E : Type*) [TopologicalSpace E] : Prop :=
  ∃ D : Set E, D.Countable ∧ Dense D

/-- **Section 3.6** of [brezis2011functional]. A topological space is separable in the sense of
`Brezis.Chapter03.IsSeparable` if and only if it is a `TopologicalSpace.SeparableSpace`. -/
theorem separable_iff (E : Type*) [TopologicalSpace E] :
    IsSeparable E ↔ TopologicalSpace.SeparableSpace E :=
  (TopologicalSpace.separableSpace_iff E).symm

/-- **Proposition 3.25** of [brezis2011functional]. Let $X$ be a separable metric space. Then every
subset $F \subseteq X$, with the induced metric, is separable.

The proof is Mathlib's instance chain: a separable metric space is second countable, and so is
each of its subspaces. -/
theorem proposition_3_25 {X : Type*} [MetricSpace X] [TopologicalSpace.SeparableSpace X]
    (F : Set X) : TopologicalSpace.SeparableSpace F :=
  inferInstance

/-- **Theorem 3.26** of [brezis2011functional]. Let $E$ be a real Banach space. If $E^\star$ is
separable, then $E$ is separable. -/
theorem theorem_3_26 [CompleteSpace E] [TopologicalSpace.SeparableSpace (StrongDual ℝ E)] :
    TopologicalSpace.SeparableSpace E :=
  separableSpace_of_separableSpace_strongDual (𝕜 := ℝ)

/-- **Corollary 3.27** of [brezis2011functional]. Let $E$ be a real Banach space. Then $E$ is
reflexive and separable if and only if $E^\star$ is reflexive and separable. -/
theorem corollary_3_27 [CompleteSpace E] :
    (IsReflexive E ∧ TopologicalSpace.SeparableSpace E) ↔
      (IsReflexive (StrongDual ℝ E) ∧ TopologicalSpace.SeparableSpace (StrongDual ℝ E)) := by
  constructor
  · rintro ⟨hE, hsep⟩
    have := isReflexive_iff.1 hE
    exact ⟨corollary_3_21.1 hE, NormedSpace.separableSpace_strongDual_of_isReflexive⟩
  · rintro ⟨hE, hsep⟩
    exact ⟨corollary_3_21.2 hE, theorem_3_26⟩

/-! ### Metrizability of the weak topologies on bounded sets -/

/-- **Theorem 3.28** of [brezis2011functional], "only if". Let $E$ be a separable real Banach space.
Then the closed unit ball $B_{E^\star}$ is metrizable in the weak-∗ topology
$\sigma(E^\star, E)$. -/
theorem theorem_3_28_mp [CompleteSpace E] [TopologicalSpace.SeparableSpace E] :
    TopologicalSpace.MetrizableSpace
      (WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual ℝ E) 1) :=
  WeakDual.metrizableSpace_closedBall 1

/-- **Theorem 3.28** of [brezis2011functional], "if". Let $E$ be a real Banach space. If the closed
unit ball $B_{E^\star}$ is metrizable in the weak-∗ topology $\sigma(E^\star, E)$, then $E$ is
separable. -/
theorem theorem_3_28_mpr [CompleteSpace E]
    (h : TopologicalSpace.MetrizableSpace
      (WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual ℝ E) 1)) :
    TopologicalSpace.SeparableSpace E :=
  separableSpace_of_metrizableSpace_weakDual_closedBall h

/-- **Theorem 3.28** of [brezis2011functional]. Let $E$ be a real Banach space. Then $E$ is
separable if and only if the closed unit ball $B_{E^\star} = \{f \in E^\star : \|f\| \le 1\}$ is
metrizable in the weak-∗ topology $\sigma(E^\star, E)$. -/
theorem theorem_3_28 [CompleteSpace E] :
    TopologicalSpace.SeparableSpace E ↔
      TopologicalSpace.MetrizableSpace
        (WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual ℝ E) 1) :=
  ⟨fun _ => theorem_3_28_mp, theorem_3_28_mpr⟩

/-- **Theorem 3.29** of [brezis2011functional], "only if". Let $E$ be a real Banach space such that
$E^\star$ is separable. Then the closed unit ball $B_E$ is metrizable in the weak topology
$\sigma(E, E^\star)$.

The source also states this in Remark 3 of Section 3.2. -/
theorem theorem_3_29_mp [CompleteSpace E] [TopologicalSpace.SeparableSpace (StrongDual ℝ E)] :
    TopologicalSpace.MetrizableSpace (toWeakSpace ℝ E '' closedBall (0 : E) 1) :=
  WeakSpace.metrizableSpace_image_closedBall 1

/-- **Theorem 3.29** of [brezis2011functional], "if". Let $E$ be a real Banach space. If the closed
unit ball $B_E$ is metrizable in the weak topology $\sigma(E, E^\star)$, then $E^\star$ is
separable.

The source leaves this direction to Exercise 3.24. -/
theorem theorem_3_29_mpr [CompleteSpace E]
    (h : TopologicalSpace.MetrizableSpace (toWeakSpace ℝ E '' closedBall (0 : E) 1)) :
    TopologicalSpace.SeparableSpace (StrongDual ℝ E) :=
  separableSpace_strongDual_of_metrizableSpace_weakSpace_closedBall h

/-- **Theorem 3.29** of [brezis2011functional]. Let $E$ be a real Banach space. Then $E^\star$ is
separable if and only if the closed unit ball $B_E = \{x \in E : \|x\| \le 1\}$ is metrizable in
the weak topology $\sigma(E, E^\star)$. -/
theorem theorem_3_29 [CompleteSpace E] :
    TopologicalSpace.SeparableSpace (StrongDual ℝ E) ↔
      TopologicalSpace.MetrizableSpace (toWeakSpace ℝ E '' closedBall (0 : E) 1) :=
  ⟨fun _ => theorem_3_29_mp, theorem_3_29_mpr⟩

/-- **Remark 20** in Chapter 3 of [brezis2011functional]. Let $E$ be an infinite-dimensional real
Banach space. Then the weak topology $\sigma(E, E^\star)$ on $E$ is not metrizable, and the weak-∗
topology $\sigma(E^\star, E)$ on $E^\star$ is not metrizable.

The source refers to Exercise 3.8. In particular, the metric built in the proof of Theorem 3.28
does not induce the weak-∗ topology on all of $E^\star$. -/
theorem remark_3_20 [CompleteSpace E] (h : ¬ FiniteDimensional ℝ E) :
    ¬ TopologicalSpace.MetrizableSpace (WeakSpace ℝ E) ∧
      ¬ TopologicalSpace.MetrizableSpace (WeakDual ℝ E) :=
  ⟨remark_3_3 h, not_metrizableSpace_weakDual h⟩

/-- **Corollary 3.30** of [brezis2011functional]. Let $E$ be a separable real Banach space and let
$(f_n)$ be a bounded sequence in $E^\star$, with $\|f_n\| \le C$ for all $n$. Then there are
$f \in E^\star$ and a subsequence $(f_{n_k})$ with $f_{n_k} \overset{\star}{\rightharpoonup} f$
in the weak-∗ topology $\sigma(E^\star, E)$.

The subsequence is $f \circ \varphi$ for a strictly increasing
$\varphi : \mathbb{N} \to \mathbb{N}$. The proof is Mathlib's
`WeakDual.isSeqCompact_closedBall`. -/
theorem corollary_3_30 [CompleteSpace E] [TopologicalSpace.SeparableSpace E]
    {f : ℕ → StrongDual ℝ E} {C : ℝ} (hf : ∀ n, ‖f n‖ ≤ C) :
    ∃ (g : StrongDual ℝ E) (φ : ℕ → ℕ), StrictMono φ ∧ (f ∘ φ) ⇀* g := by
  obtain ⟨a, -, φ, hφ, hlim⟩ := WeakDual.isSeqCompact_closedBall ℝ E 0 C
    (x := fun n => StrongDual.toWeakDual (f n)) fun n => by
      simpa [mem_closedBall_zero_iff] using hf n
  exact ⟨WeakDual.toStrongDual a, φ, hφ,
    by simpa [WeakStarTendsto, Function.comp_def] using hlim⟩

/-! ### Remark 4 of Section 3.2 -/

/-- **Remark 4** in Chapter 3 of [brezis2011functional], Section 3.2. Let $E$ be an
infinite-dimensional real Banach space such that $E^\star$ is separable or $E$ is reflexive. Then
there is a sequence $(x_n)$ in $E$ with $\|x_n\| = 1$ for all $n$ and $x_n \rightharpoonup 0$
weakly.

The source refers to Exercise 3.22. By Example 1 of Section 3.2, $0$ lies in the weak closure of
the unit sphere. When $E^\star$ is separable, $B_E$ is weakly metrizable by Theorem 3.29, so $0$
is a weak limit of a sequence on the sphere. When $E$ is reflexive, the sequential form of the
Eberlein–Šmulian theorem, with Theorem 3.18, gives the same conclusion. -/
theorem remark_3_4 [CompleteSpace E] (hinf : ¬ FiniteDimensional ℝ E)
    (h : TopologicalSpace.SeparableSpace (StrongDual ℝ E) ∨ IsReflexive E) :
    ∃ x : ℕ → E, (∀ n, ‖x n‖ = 1) ∧ x ⇀ 0 := by
  have h0 : toWeakSpace ℝ E 0 ∈ closure (toWeakSpace ℝ E '' sphere (0 : E) 1) := by
    rw [(example_3_1 hinf).1]
    exact ⟨0, by simp, rfl⟩
  rcases h with hsep | hrefl
  · -- `B_E` is weakly metrizable, so the weak closure of the sphere in it is sequential
    set B : Set (WeakSpace ℝ E) := toWeakSpace ℝ E '' closedBall (0 : E) 1 with hB
    have hmetr : TopologicalSpace.MetrizableSpace B := theorem_3_29_mp
    set S : Set B := Subtype.val ⁻¹' (toWeakSpace ℝ E '' sphere (0 : E) 1) with hS
    have h0B : toWeakSpace ℝ E 0 ∈ B := ⟨0, by simp, rfl⟩
    have h0S : (⟨toWeakSpace ℝ E 0, h0B⟩ : B) ∈ closure S := by
      rw [closure_subtype]
      have : Subtype.val '' S = toWeakSpace ℝ E '' sphere (0 : E) 1 := by
        rw [hS, Subtype.image_preimage_val]
        exact inter_eq_right.2 (image_mono sphere_subset_closedBall)
      rw [this]
      exact h0
    obtain ⟨y, hyS, hy⟩ := mem_closure_iff_seq_limit.1 h0S
    refine ⟨fun n => (toWeakSpace ℝ E).symm (y n : WeakSpace ℝ E), fun n => ?_, ?_⟩
    · obtain ⟨z, hz, hzy⟩ := hyS n
      change ‖(toWeakSpace ℝ E).symm (y n : WeakSpace ℝ E)‖ = 1
      rw [← hzy, LinearEquiv.symm_apply_apply]
      exact mem_sphere_zero_iff_norm.1 hz
    · have := (continuous_subtype_val.tendsto _).comp hy
      simpa [WeakTendsto, Function.comp_def] using this
  · -- Eberlein–Šmulian: the weak closure of a set whose sequences have weakly convergent
    -- subsequences is sequential
    obtain ⟨y, hy, hlim⟩ :=
      NormedSpace.exists_seq_tendsto_toWeakSpace_of_mem_closure_image_toWeakSpace
        (A := sphere (0 : E) 1) (fun x hx => theorem_3_18 hrefl (C := 1)
          fun n => (mem_sphere_zero_iff_norm.1 (hx n)).le) h0
    exact ⟨y, fun n => mem_sphere_zero_iff_norm.1 (hy n), hlim⟩

end Brezis.Chapter03
