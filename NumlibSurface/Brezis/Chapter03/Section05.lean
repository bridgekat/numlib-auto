/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Topology.Sequences
import Numlib.Analysis.Normed.Module.Reflexive.EberleinSmulian
import Numlib.Analysis.Normed.Module.Reflexive.Kakutani
import Numlib.Analysis.Normed.Operator.Unbounded.Reflexive
import NumlibSurface.Brezis.Chapter01.Section03
import NumlibSurface.Brezis.Chapter03.Section04

/-!
# Brezis, Section 3.5: Reflexive spaces

This module formalizes Section 3.5 of [brezis2011functional] for a real Banach space $E$. The space
$E$ is reflexive if the canonical injection $J : E \to E^{\star\star}$ of Section 1.3 is onto.
Kakutani's theorem characterizes reflexivity by the weak compactness of the closed unit ball $B_E$
(Theorem 3.17), with the lemmas of Helly and Goldstine (Lemmas 3.3 and 3.4) as tools. In a reflexive
space every bounded sequence has a weakly convergent subsequence, and this property characterizes
reflexivity (Theorems 3.18 and 3.19). Closed subspaces and the dual of a reflexive space are
reflexive (Proposition 3.20, Corollary 3.21), bounded closed convex sets are weakly compact
(Corollary 3.22), a convex, lower semicontinuous, coercive function attains its minimum on a closed
convex set (Corollary 3.23), and a closed densely defined operator between reflexive spaces is its
own double adjoint (Theorem 3.24).

The proofs specialize the backbone modules `Numlib.Analysis.Normed.Module.Reflexive.Kakutani`
(Theorem 3.17, Lemmas 3.3 and 3.4, Remark 15, Corollaries 3.21 and 3.22),
`Numlib.Analysis.Normed.Module.Reflexive` (Theorem 3.18, Proposition 3.20),
`Numlib.Analysis.Normed.Module.Reflexive.EberleinSmulian` (Theorem 3.19) and
`Numlib.Analysis.Normed.Operator.Unbounded.Reflexive` (Theorem 3.24). Corollary 3.23 is proved in
this module from Corollaries 3.22 and 3.9, by the argument of the source.

## Main definitions

* Section 3.5, definition of a reflexive space, `Brezis.Chapter03.IsReflexive`: the canonical
  injection $J : E \to E^{\star\star}$ is surjective.

## Main results

* Section 3.5, `Brezis.Chapter03.isReflexive_iff`: the definition agrees with the backbone class
  `NormedSpace.IsReflexive ℝ E`.
* Remark 13, `Brezis.Chapter03.remark_3_13_finiteDimensional` and
  `Brezis.Chapter03.remark_3_13_hilbert`: finite-dimensional spaces and Hilbert spaces are
  reflexive.
* Theorem 3.17 (Kakutani), `Brezis.Chapter03.theorem_3_17_mp`, `Brezis.Chapter03.theorem_3_17_mpr`
  and `Brezis.Chapter03.theorem_3_17`: $E$ is reflexive if and only if $B_E$ is compact in
  $\sigma(E, E^\star)$.
* Lemma 3.3 (Helly), `Brezis.Chapter03.lemma_3_3`: a criterion for the approximate solvability of
  $\langle f_i, x \rangle = \gamma_i$ with $\|x\| \le 1$.
* Lemma 3.4 (Goldstine), `Brezis.Chapter03.lemma_3_4` and `Brezis.Chapter03.lemma_3_4_dense`:
  $J(B_E)$ is dense in $B_{E^{\star\star}}$, and $J(E)$ is dense in $E^{\star\star}$, for
  $\sigma(E^{\star\star}, E^\star)$.
* Remark 15, `Brezis.Chapter03.remark_3_15`: $J(B_E)$ is strongly closed, so it is strongly dense in
  $B_{E^{\star\star}}$ only when $E$ is reflexive.
* Theorem 3.18, `Brezis.Chapter03.theorem_3_18`: in a reflexive space every bounded sequence has a
  weakly convergent subsequence.
* Theorem 3.19 (Eberlein–Šmulian), `Brezis.Chapter03.theorem_3_19`: conversely, if every bounded
  sequence has a weakly convergent subsequence, then $E$ is reflexive.
* Remark 17(i), `Brezis.Chapter03.remark_3_17`: in a metric space, compactness is sequential
  compactness.
* Proposition 3.20, `Brezis.Chapter03.proposition_3_20`: a closed subspace of a reflexive space is
  reflexive.
* Corollary 3.21, `Brezis.Chapter03.corollary_3_21`: $E$ is reflexive if and only if $E^\star$ is
  reflexive.
* Corollary 3.22, `Brezis.Chapter03.corollary_3_22`: in a reflexive space, a bounded, closed, convex
  set is weakly compact.
* Corollary 3.23, `Brezis.Chapter03.corollary_3_23`: in a reflexive space, a convex, lower
  semicontinuous, coercive function attains its minimum on a nonempty closed convex set.
* Theorem 3.24, `Brezis.Chapter03.theorem_3_24_a` and `Brezis.Chapter03.theorem_3_24_b`: for a
  closed densely defined operator $A$ between reflexive spaces, $D(A^\star)$ is dense and
  $A^{\star\star} = A$.

## Conventions

* The canonical injection $J : E \to E^{\star\star}$ is `NormedSpace.inclusionInDoubleDual ℝ E`.
* "Compact in $\sigma(E, E^\star)$" for a set $s \subseteq E$ is `IsCompact (toWeakSpace ℝ E '' s)`.
  Weak convergence $x_n \rightharpoonup x$ is `Brezis.Chapter03.WeakTendsto`, as in Section 3.2.
* The unbounded adjoint $A^\star$ is the backbone's `LinearPMap.strongDualAdjoint`, as in Chapter 2.

## Implementation notes

* The source defines reflexivity for a Banach space. The predicate `Brezis.Chapter03.IsReflexive`
  does not ask for completeness; a reflexive normed space is complete by
  `NormedSpace.completeSpace_of_isReflexive`. So Proposition 3.20 can be stated for a closed
  subspace $M$ without a proof that $M$ is complete. The theorems assume that $E$ is complete, as
  the source does.
* In Corollary 3.23, the function is `φ : E → EReal`, and its convexity and lower semicontinuity are
  hypotheses on the restriction `ConvexAnalysis.convexRestrict A φ`, as in Chapter 1.

## Deviations from the source

* **Corollary 3.23** (generalization). The source assumes that $\varphi$ never takes the value
  $-\infty$. The formal statement does not assume this. See `Brezis.Chapter03.corollary_3_23`.

## Not formalized

* **Remarks 14, 16 and 18.** They are discussion.
* **Remark 13, the spaces $L^p$, $\ell^p$, $L^1$, $L^\infty$ and $C(K)$.** These claims are stated
  in Chapters 4 and 11.
* **Remark 17(ii) and (iii).** These parts are not stated.
-/

open Bornology Filter Metric Set Topology NormedSpace

namespace Brezis.Chapter03

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-! ### The definition -/

/-- **Section 3.5** of [brezis2011functional], definition of a reflexive space. A real normed space
$E$ is **reflexive** if the canonical injection $J : E \to E^{\star\star}$ of Section 1.3 is
surjective, that is, $J(E) = E^{\star\star}$.

The source makes the definition for a Banach space. Completeness is not part of the predicate,
because a reflexive normed space is complete (`NormedSpace.completeSpace_of_isReflexive`). -/
def IsReflexive (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] : Prop :=
  Function.Surjective (inclusionInDoubleDual ℝ E)

/-- **Section 3.5** of [brezis2011functional]. A real normed space $E$ is reflexive in the sense of
`Brezis.Chapter03.IsReflexive` if and only if it is reflexive in the sense of the backbone class
`NormedSpace.IsReflexive ℝ E`. -/
theorem isReflexive_iff : IsReflexive E ↔ NormedSpace.IsReflexive ℝ E :=
  ⟨fun h => ⟨h⟩, fun _ => NormedSpace.surjective_inclusionInDoubleDual⟩

/-- **Remark 13** in Chapter 3 of [brezis2011functional], finite-dimensional spaces. Every
finite-dimensional real Banach space $E$ is reflexive.

The source argues from $\dim E = \dim E^\star = \dim E^{\star\star}$. -/
theorem remark_3_13_finiteDimensional [CompleteSpace E] [FiniteDimensional ℝ E] :
    IsReflexive E :=
  isReflexive_iff.2 inferInstance

/-- **Remark 13** in Chapter 3 of [brezis2011functional], Hilbert spaces. Every real Hilbert space
$H$ is reflexive.

The source announces this result for Chapter 5. -/
theorem remark_3_13_hilbert {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] : IsReflexive H :=
  isReflexive_iff.2 inferInstance

/-! ### Kakutani's theorem -/

/-- **Theorem 3.17** of [brezis2011functional] (Kakutani), "only if". Let $E$ be a real Banach
space. If $E$ is reflexive, then the closed unit ball $B_E = \{x \in E : \|x\| \le 1\}$ is
compact in the weak topology $\sigma(E, E^\star)$. -/
theorem theorem_3_17_mp [CompleteSpace E] (h : IsReflexive E) :
    IsCompact (toWeakSpace ℝ E '' closedBall (0 : E) 1) := by
  have := isReflexive_iff.1 h
  exact NormedSpace.isCompact_image_toWeakSpace_closedBall 1

/-- **Theorem 3.17** of [brezis2011functional] (Kakutani), "if". Let $E$ be a real Banach space. If
the closed unit ball $B_E$ is compact in the weak topology $\sigma(E, E^\star)$, then $E$ is
reflexive. -/
theorem theorem_3_17_mpr [CompleteSpace E]
    (h : IsCompact (toWeakSpace ℝ E '' closedBall (0 : E) 1)) : IsReflexive E :=
  isReflexive_iff.2 (NormedSpace.isReflexive_of_isCompact_image_toWeakSpace_closedBall h)

/-- **Theorem 3.17** of [brezis2011functional] (Kakutani). Let $E$ be a real Banach space. Then $E$
is reflexive if and only if the closed unit ball
$$B_E = \{x \in E : \|x\| \le 1\}$$
is compact in the weak topology $\sigma(E, E^\star)$. -/
theorem theorem_3_17 [CompleteSpace E] :
    IsReflexive E ↔ IsCompact (toWeakSpace ℝ E '' closedBall (0 : E) 1) :=
  ⟨theorem_3_17_mp, theorem_3_17_mpr⟩

/-- **Lemma 3.3** of [brezis2011functional] (Helly). Let $E$ be a real Banach space, let
$f_1, \dots, f_k \in E^\star$ and let $\gamma_1, \dots, \gamma_k \in \mathbb{R}$. The following
are equivalent:

1. for every $\varepsilon > 0$ there is $x_\varepsilon \in E$ with $\|x_\varepsilon\| \le 1$ and
   $|\langle f_i, x_\varepsilon \rangle - \gamma_i| < \varepsilon$ for all $i = 1, \dots, k$;
2. for all $\beta_1, \dots, \beta_k \in \mathbb{R}$,
$$\Bigl|\sum_{i=1}^k \beta_i \gamma_i\Bigr| \le \Bigl\|\sum_{i=1}^k \beta_i f_i\Bigr\|.$$

The indices run over `Fin k`. -/
theorem lemma_3_3 [CompleteSpace E] {k : ℕ} (f : Fin k → StrongDual ℝ E) (γ : Fin k → ℝ) :
    (∀ ε > 0, ∃ x : E, ‖x‖ ≤ 1 ∧ ∀ i, |f i x - γ i| < ε) ↔
      ∀ β : Fin k → ℝ, |∑ i, β i * γ i| ≤ ‖∑ i, β i • f i‖ :=
  NormedSpace.helly_iff f γ

/-- **Lemma 3.4** of [brezis2011functional] (Goldstine). Let $E$ be a real Banach space. The closure
of $J(B_E)$ in $E^{\star\star}$ for the weak-∗ topology $\sigma(E^{\star\star}, E^\star)$ is the
closed unit ball $B_{E^{\star\star}}$. That is, $J(B_E)$ is dense in $B_{E^{\star\star}}$ for
$\sigma(E^{\star\star}, E^\star)$.

The weak-∗ topology on $E^{\star\star}$ is that of `WeakDual ℝ (StrongDual ℝ E)`. -/
theorem lemma_3_4 [CompleteSpace E] :
    closure ((StrongDual.toWeakDual ∘ inclusionInDoubleDual ℝ E) '' closedBall (0 : E) 1) =
      WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual ℝ (StrongDual ℝ E)) 1 :=
  NormedSpace.goldstine

/-- **Lemma 3.4** of [brezis2011functional] (Goldstine), consequence. Let $E$ be a real Banach
space. Then $J(E)$ is dense in $E^{\star\star}$ for the weak-∗ topology
$\sigma(E^{\star\star}, E^\star)$. -/
theorem lemma_3_4_dense [CompleteSpace E] :
    DenseRange (StrongDual.toWeakDual ∘ inclusionInDoubleDual ℝ E) :=
  NormedSpace.denseRange_toWeakDual_inclusionInDoubleDual

/-- **Remark 15** in Chapter 3 of [brezis2011functional]. Let $E$ be a real Banach space. Then
$J(B_E)$ is closed in $E^{\star\star}$ for the strong topology. Consequently, if $J(B_E)$ is
strongly dense in $B_{E^{\star\star}}$, then $J(B_E) = B_{E^{\star\star}}$ and $E$ is reflexive. -/
theorem remark_3_15 [CompleteSpace E] :
    IsClosed (inclusionInDoubleDual ℝ E '' closedBall (0 : E) 1) ∧
      (closure (inclusionInDoubleDual ℝ E '' closedBall (0 : E) 1) =
        closedBall (0 : StrongDual ℝ (StrongDual ℝ E)) 1 → IsReflexive E) := by
  refine ⟨NormedSpace.isClosed_image_inclusionInDoubleDual_closedBall 1, fun hdense ξ => ?_⟩
  rw [(NormedSpace.isClosed_image_inclusionInDoubleDual_closedBall 1).closure_eq] at hdense
  rcases eq_or_ne ξ 0 with rfl | hξ
  · exact ⟨0, map_zero _⟩
  have hξ0 : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  have hmem : ‖ξ‖⁻¹ • ξ ∈ closedBall (0 : StrongDual ℝ (StrongDual ℝ E)) 1 := by
    rw [mem_closedBall_zero_iff, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hξ0.ne']
  rw [← hdense] at hmem
  obtain ⟨x, -, hx⟩ := hmem
  refine ⟨‖ξ‖ • x, ?_⟩
  rw [map_smul, hx, smul_smul, mul_inv_cancel₀ hξ0.ne', one_smul]

/-! ### Weak sequential compactness -/

/-- **Theorem 3.18** of [brezis2011functional]. Let $E$ be a reflexive real Banach space and let
$(x_n)$ be a bounded sequence in $E$, with $\|x_n\| \le C$ for all $n$. Then there are $u \in E$
and a subsequence $(x_{n_k})$ with $x_{n_k} \rightharpoonup u$ in the weak topology
$\sigma(E, E^\star)$.

The subsequence is $x \circ \varphi$ for a strictly increasing
$\varphi : \mathbb{N} \to \mathbb{N}$. -/
theorem theorem_3_18 [CompleteSpace E] (hE : IsReflexive E) {x : ℕ → E} {C : ℝ}
    (hx : ∀ n, ‖x n‖ ≤ C) : ∃ (u : E) (φ : ℕ → ℕ), StrictMono φ ∧ (x ∘ φ) ⇀ u := by
  have := isReflexive_iff.1 hE
  obtain ⟨u, φ, hφ, hlim⟩ := NormedSpace.exists_subseq_forall_dual_tendsto (𝕜 := ℝ) hx
  exact ⟨u, φ, hφ, (proposition_3_5 _ _).2 hlim⟩

/-- **Theorem 3.19** of [brezis2011functional] (Eberlein–Šmulian). Let $E$ be a real Banach space.
Suppose that every bounded sequence in $E$ has a subsequence that converges in the weak topology
$\sigma(E, E^\star)$. Then $E$ is reflexive.

The source refers to Problem 10 for the proof. -/
theorem theorem_3_19 [CompleteSpace E]
    (h : ∀ (x : ℕ → E) (C : ℝ), (∀ n, ‖x n‖ ≤ C) →
      ∃ (u : E) (φ : ℕ → ℕ), StrictMono φ ∧ (x ∘ φ) ⇀ u) : IsReflexive E :=
  isReflexive_iff.2 <| NormedSpace.isReflexive_of_forall_exists_subseq_forall_dual_tendsto
    fun x C hx => by
      obtain ⟨u, φ, hφ, hlim⟩ := h x C hx
      exact ⟨u, φ, hφ, (proposition_3_5 _ _).1 hlim⟩

/-- **Remark 17(i)** in Chapter 3 of [brezis2011functional]. In a metric space $X$, a set is compact
if and only if every sequence in it has a subsequence that converges to a point of the set. -/
theorem remark_3_17 {X : Type*} [MetricSpace X] (s : Set X) : IsCompact s ↔ IsSeqCompact s :=
  isCompact_iff_isSeqCompact

/-! ### Further properties of reflexive spaces -/

/-- **Proposition 3.20** of [brezis2011functional]. Let $E$ be a reflexive real Banach space and let
$M \subseteq E$ be a closed linear subspace. Then $M$, with the norm of $E$, is reflexive. -/
theorem proposition_3_20 [CompleteSpace E] (hE : IsReflexive E) (M : Submodule ℝ E)
    (hM : IsClosed (M : Set E)) : IsReflexive M := by
  have := isReflexive_iff.1 hE
  exact isReflexive_iff.2 (NormedSpace.isReflexive_of_isClosed M hM)

/-- **Corollary 3.21** of [brezis2011functional]. A real Banach space $E$ is reflexive if and only
if its dual $E^\star$ is reflexive. -/
theorem corollary_3_21 [CompleteSpace E] : IsReflexive E ↔ IsReflexive (StrongDual ℝ E) := by
  rw [isReflexive_iff, isReflexive_iff]
  exact NormedSpace.isReflexive_strongDual_iff.symm

/-- **Corollary 3.22** of [brezis2011functional]. Let $E$ be a reflexive real Banach space and let
$K \subseteq E$ be bounded, closed and convex. Then $K$ is compact in the weak topology
$\sigma(E, E^\star)$. -/
theorem corollary_3_22 [CompleteSpace E] (hE : IsReflexive E) {K : Set E} (hb : IsBounded K)
    (hc : IsClosed K) (hK : Convex ℝ K) : IsCompact (toWeakSpace ℝ E '' K) := by
  have := isReflexive_iff.1 hE
  exact hK.isCompact_image_toWeakSpace_of_isBounded_of_isClosed hb hc

/-- **Corollary 3.23** of [brezis2011functional]. Let $E$ be a reflexive real Banach space and let
$A \subseteq E$ be closed and convex. Let $\varphi : E \to [-\infty, +\infty]$, and suppose that
the function $\psi$ equal to $\varphi$ on $A$ and to $+\infty$ outside $A$ is convex and lower
semicontinuous. Suppose that $\varphi(a) < +\infty$ for some $a \in A$, and that either $A$ is
bounded or $\varphi$ is coercive on $A$:
$$\lim_{x \in A,\ \|x\| \to \infty} \varphi(x) = +\infty.$$
Then $\varphi$ attains its minimum on $A$: there is $x_0 \in A$ with
$\varphi(x_0) \le \varphi(x)$ for all $x \in A$.

**Generalization.** The source takes $\varphi : A \to (-\infty, +\infty]$, so $\varphi$ never
takes the value $-\infty$. The formal statement does not assume this.

The function $\psi$ is `ConvexAnalysis.convexRestrict A φ`. Coercivity is stated as: for every
$M \in \mathbb{R}$ there is $R$ with $\varphi(x) > M$ for all $x \in A$ with $\|x\| > R$. The
hypotheses that $A$ is closed and convex are present but the proof does not use them, because
the sublevel sets of $\psi$ are closed and convex. The proof applies Corollary 3.22 and
Corollary 3.9, as in the source. -/
theorem corollary_3_23 [CompleteSpace E] (hE : IsReflexive E) {A : Set E} (_hAc : IsClosed A)
    (_hAconv : Convex ℝ A) {φ : E → EReal}
    (hconv : ConvexAnalysis.ConvexFn (ConvexAnalysis.convexRestrict A φ))
    (hlsc : LowerSemicontinuous (ConvexAnalysis.convexRestrict A φ)) (hne : ∃ a ∈ A, φ a < ⊤)
    (hcoer : IsBounded A ∨ ∀ M : ℝ, ∃ R : ℝ, ∀ x ∈ A, R < ‖x‖ → (M : EReal) < φ x) :
    ∃ x₀ ∈ A, ∀ x ∈ A, φ x₀ ≤ φ x := by
  obtain ⟨a, haA, ha⟩ := hne
  set ψ := ConvexAnalysis.convexRestrict A φ with hψ
  -- the sublevel set `Ã = {x ∈ A | φ x ≤ φ a}`, which is `{x | ψ x ≤ φ a}`
  set S : Set E := {x | ψ x ≤ φ a} with hS
  have hSA : S ⊆ A := fun x hx => by
    by_contra hxA
    have : ψ x = ⊤ := ConvexAnalysis.convexRestrict_of_notMem hxA
    rw [hS, mem_ofPred_eq, this, top_le_iff] at hx
    exact ha.ne hx
  have hSmem : ∀ x ∈ A, x ∈ S ↔ φ x ≤ φ a := fun x hx => by
    rw [hS, mem_ofPred_eq, hψ, ConvexAnalysis.convexRestrict_of_mem hx]
  have haS : a ∈ S := (hSmem a haA).2 le_rfl
  have hSc : IsClosed S := hlsc.isClosed_preimage (φ a)
  have hSconv : Convex ℝ S := hconv.convex_le (φ a)
  have hSb : IsBounded S := by
    rcases hcoer with hb | hcoer
    · exact hb.subset hSA
    · obtain ⟨M, hM⟩ : ∃ M : ℝ, φ a < M := by
        rcases eq_or_ne (φ a) ⊥ with h | h
        · exact ⟨0, h ▸ EReal.bot_lt_coe 0⟩
        · obtain ⟨M, hM, -⟩ := EReal.lt_iff_exists_real_btwn.1 ha
          exact ⟨M, hM⟩
      obtain ⟨R, hR⟩ := hcoer M
      refine (isBounded_closedBall (x := (0 : E)) (r := R)).subset fun x hx => ?_
      rw [mem_closedBall_zero_iff]
      by_contra hRx
      have h1 := hR x (hSA hx) (lt_of_not_ge hRx)
      have h2 := (hSmem x (hSA hx)).1 hx
      exact (h1.trans_le h2).not_gt hM
  -- `Ã` is weakly compact and `ψ` is weakly l.s.c., so `ψ` attains its minimum on `Ã`
  have hcpt := corollary_3_22 hE hSb hSc hSconv
  have hwlsc := corollary_3_9 hconv hlsc
  have hSne : (toWeakSpace ℝ E '' S).Nonempty := ⟨toWeakSpace ℝ E a, a, haS, rfl⟩
  obtain ⟨y₀, hy₀, hmin⟩ := (hwlsc.lowerSemicontinuousOn _).exists_isMinOn hSne hcpt
  obtain ⟨x₀, hx₀S, rfl⟩ := hy₀
  refine ⟨x₀, hSA hx₀S, fun x hx => ?_⟩
  have hx₀a : φ x₀ ≤ φ a := (hSmem x₀ (hSA hx₀S)).1 hx₀S
  by_cases hxS : x ∈ S
  · have := hmin ⟨x, hxS, rfl⟩
    simpa [hψ, ConvexAnalysis.convexRestrict_of_mem hx,
        ConvexAnalysis.convexRestrict_of_mem (hSA hx₀S)]
      using this
  · have : φ a < φ x := lt_of_not_ge fun h => hxS ((hSmem x hx).2 h)
    exact hx₀a.trans this.le

/-! ### Theorem 3.24: the double adjoint -/

/-- **Theorem 3.24** of [brezis2011functional], density of $D(A^\star)$. Let $E$ and $F$ be
reflexive real Banach spaces, and let $A : D(A) \subseteq E \to F$ be a densely defined, closed
unbounded linear operator. Then the domain $D(A^\star)$ of the adjoint is dense in $F^\star$, so
that $A^{\star\star}$ is defined.

The hypothesis that $E$ is reflexive is present but not used for this part. The adjoint is
`LinearPMap.strongDualAdjoint`. -/
theorem theorem_3_24_a [CompleteSpace E] [CompleteSpace F] (_hE : IsReflexive E)
    (hF : IsReflexive F) {A : E →ₗ.[ℝ] F} (hd : Dense (A.domain : Set E)) (hc : A.IsClosed) :
    Dense (A.strongDualAdjoint.domain : Set (StrongDual ℝ F)) := by
  have := isReflexive_iff.1 hF
  exact LinearPMap.dense_domain_strongDualAdjoint hc hd

/-- **Theorem 3.24** of [brezis2011functional], $A^{\star\star} = A$. Let $E$ and $F$ be reflexive
real Banach spaces, and let $A : D(A) \subseteq E \to F$ be a densely defined, closed unbounded
linear operator. Then the double adjoint $A^{\star\star} : D(A^{\star\star}) \subseteq
E^{\star\star} \to F^{\star\star}$, seen as an operator from $E$ into $F$ through $J_E$ and
$J_F$, is $A$. That is, the graph of $A^{\star\star}$ is the image of the graph $G(A)$ under
$J_E \times J_F$. -/
theorem theorem_3_24_b [CompleteSpace E] [CompleteSpace F] (hE : IsReflexive E)
    (hF : IsReflexive F) {A : E →ₗ.[ℝ] F} (hd : Dense (A.domain : Set E)) (hc : A.IsClosed) :
    A.strongDualAdjoint.strongDualAdjoint.graph =
      A.graph.map ((inclusionInDoubleDual ℝ E : E →ₗ[ℝ] StrongDual ℝ (StrongDual ℝ E)).prodMap
        (inclusionInDoubleDual ℝ F : F →ₗ[ℝ] StrongDual ℝ (StrongDual ℝ F))) := by
  have := isReflexive_iff.1 hE
  have := isReflexive_iff.1 hF
  exact LinearPMap.graph_strongDualAdjoint_strongDualAdjoint hc hd

end Brezis.Chapter03
