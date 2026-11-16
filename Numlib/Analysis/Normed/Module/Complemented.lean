/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Normed.Module.Complemented`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Normed.Module.Complemented
import Mathlib.Analysis.Normed.Module.ContinuousInverse
import Numlib.Analysis.Normed.Operator.Unbounded.Basic

/-!
# Closed sums of closed subspaces, and one-sided inverses

This module proves consequences of the open mapping theorem for closed subspaces of a Banach space
and for one-sided inverses of bounded operators ([brezis2011functional], §2.4 and Exercise 2.16).
Let $G$ and $L$ be closed subspaces of a Banach space $E$. If $G + L$ is closed, then every
$z \in G + L$ can be written $z = x + y$ with $x \in G$, $y \in L$ and $\|x\|, \|y\| \le C \|z\|$,
and
$$\operatorname{dist}(x, G \cap L) \le C \bigl(\operatorname{dist}(x, G) + \operatorname{dist}(x,
  L)\bigr) \quad \text{for every } x \in E.$$
Conversely, this distance inequality implies that $G + L$ is closed. For bounded operators between
Banach spaces, a surjective operator has a bounded right inverse if and only if its kernel is
complemented, and an injective operator has a bounded left inverse if and only if its range is
closed and complemented.

## Main results

* `Submodule.exists_add_eq_norm_le_of_isClosed_sup`: if $G$, $L$ and $G + L$ are closed, then every
  $z \in G + L$ is $x + y$ with $x \in G$, $y \in L$ and $\|x\|, \|y\| \le C \|z\|$.
* `Submodule.exists_infDist_inf_le_of_isClosed_sup`: under the same hypotheses,
  $\operatorname{dist}(x, G \cap L) \le C (\operatorname{dist}(x, G) + \operatorname{dist}(x, L))$
  for every $x$.
* `Submodule.isClosed_sup_of_forall_infDist_inf_le`: if $\operatorname{dist}(x, G \cap L) \le C
  \operatorname{dist}(x, L)$ for every $x \in G$, then $G + L$ is closed.
* `Submodule.isClosed_sup_iff_exists_infDist_inf_le`: the last two results combined as an
  equivalence.
* `ContinuousLinearMap.HasRightInverse.of_surjective_of_closedComplemented_ker`,
  `ContinuousLinearMap.hasRightInverse_iff_closedComplemented_ker`: a surjective bounded operator
  between Banach spaces has a bounded right inverse if and only if its kernel is complemented.
* `ContinuousLinearMap.hasLeftInverse_iff_isClosed_range_and_closedComplemented_range`: an injective
  bounded operator between Banach spaces has a bounded left inverse if and only if its range is
  closed and complemented.

## Implementation notes

* Mathlib already provides the vocabulary: `Submodule.IsTopCompl` and
  `Submodule.ClosedComplemented`, and `ContinuousLinearMap.HasRightInverse` and
  `ContinuousLinearMap.HasLeftInverse`. In a Banach space, a topological complement of a closed
  subspace is the same as a closed algebraic complement
  (`Submodule.closedComplemented_iff_isClosed_exists_isClosed_isCompl`). Mathlib also characterizes
  left inverses
  (`ContinuousLinearMap.HasLeftInverse.of_injective_of_isClosed_range_of_closedComplement_range`)
  and proves one direction for right inverses
  (`ContinuousLinearMap.closedComplemented_ker_of_rightInverse`).
* Mathlib's product $G \times L$ carries the maximum norm. So the constant of the decomposition
  bounds $\max(\|x\|, \|y\|)$, not $\|x\| + \|y\|$ as in [brezis2011functional]. The two forms
  differ by a factor of at most $2$.
* The proof of `Submodule.isClosed_sup_of_forall_infDist_inf_le` uses the closed range criterion
  `ContinuousLinearMap.isClosed_range_iff_exists_infDist_ker_le` for the addition map
  $G \times L \to E$, whose kernel is $\{(w, -w) : w \in G \cap L\}$.
-/

open Metric

namespace Submodule

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [CompleteSpace E]

/-- **Bounded decomposition of a closed sum**. Let $G$ and $L$ be closed subspaces of a Banach space
$E$ such that $G + L$ is closed. Then there is a constant $C \ge 0$ such that every
$z \in G + L$ can be written $z = x + y$ with $x \in G$, $y \in L$,
$$\|x\| \le C \|z\| \quad \text{and} \quad \|y\| \le C \|z\|.$$
This is Theorem 2.10 of [brezis2011functional].

The source bounds $\|x\| + \|y\|$ instead. The proof is the open mapping theorem
(`ContinuousLinearMap.exists_preimage_norm_le`) for the bounded surjection
$G \times L \to G + L$, $(x, y) \mapsto x + y$, between Banach spaces. -/
theorem exists_add_eq_norm_le_of_isClosed_sup (G L : Submodule 𝕜 E) (hG : IsClosed (G : Set E))
    (hL : IsClosed (L : Set E)) (hGL : IsClosed ((G ⊔ L : Submodule 𝕜 E) : Set E)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ z ∈ G ⊔ L, ∃ x ∈ G, ∃ y ∈ L, z = x + y ∧ ‖x‖ ≤ C * ‖z‖ ∧ ‖y‖ ≤ C * ‖z‖ := by
  have := hG.completeSpace_coe
  have := hL.completeSpace_coe
  have := hGL.completeSpace_coe
  -- the addition map, with codomain restricted to the closed subspace `G ⊔ L`
  let T : G × L →L[𝕜] ↥(G ⊔ L) := (G.subtypeL.coprod L.subtypeL).codRestrict (G ⊔ L) fun p =>
    add_mem_sup p.1.2 p.2.2
  have hT : ∀ p : G × L, (T p : E) = p.1 + p.2 := fun p => rfl
  have hsurj : Function.Surjective T := by
    rintro ⟨z, hz⟩
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_sup.1 hz
    exact ⟨(⟨x, hx⟩, ⟨y, hy⟩), Subtype.ext (hT _)⟩
  obtain ⟨C, hC0, hC⟩ := T.exists_preimage_norm_le hsurj
  refine ⟨C, hC0.le, fun z hz => ?_⟩
  obtain ⟨⟨x, y⟩, hxy, hnorm⟩ := hC ⟨z, hz⟩
  have hz' : z = x + y := by
    have := congrArg Subtype.val hxy
    rw [hT] at this
    exact this.symm
  have hn : ‖(⟨z, hz⟩ : ↥(G ⊔ L))‖ = ‖z‖ := rfl
  rw [hn, Prod.norm_def, max_le_iff] at hnorm
  exact ⟨x, x.2, y, y.2, hz', hnorm.1, hnorm.2⟩

/-- **Distance to the intersection of a closed sum**. Let $G$ and $L$ be closed subspaces of a
Banach space $E$ such that $G + L$ is closed. Then there is a constant $C$ such that
$$\operatorname{dist}(x, G \cap L) \le C \bigl(\operatorname{dist}(x, G) +
  \operatorname{dist}(x, L)\bigr) \quad \text{for every } x \in E.$$
This is Corollary 2.11 of [brezis2011functional].

Given $a \in G$ and $b \in L$ that nearly attain the two distances, decompose $a - b = a' + b'$
with $a' \in G$, $b' \in L$ and $\|a'\| \le C \|a - b\|$ by
`Submodule.exists_add_eq_norm_le_of_isClosed_sup`. Then $a - a' \in G \cap L$ and $\|x - (a -
a')\| \le \|x - a\| + C (\|x - a\| + \|x - b\|)$. -/
theorem exists_infDist_inf_le_of_isClosed_sup (G L : Submodule 𝕜 E) (hG : IsClosed (G : Set E))
    (hL : IsClosed (L : Set E)) (hGL : IsClosed ((G ⊔ L : Submodule 𝕜 E) : Set E)) :
    ∃ C : ℝ, ∀ x : E,
      infDist x (G ⊓ L : Submodule 𝕜 E) ≤ C * (infDist x (G : Set E) + infDist x (L : Set E)) := by
  obtain ⟨C, hC0, hC⟩ := exists_add_eq_norm_le_of_isClosed_sup G L hG hL hGL
  refine ⟨1 + C, fun x => le_of_forall_pos_le_add fun ε hε => ?_⟩
  set ε₀ : ℝ := ε / (1 + 2 * C) with hε₀
  have hε₀pos : 0 < ε₀ := by positivity
  have hε₀eq : (1 + 2 * C) * ε₀ = ε := by rw [hε₀]; field_simp
  obtain ⟨a, ha, hxa⟩ := (infDist_lt_iff ⟨0, G.zero_mem⟩).1
    (lt_add_of_pos_right (infDist x (G : Set E)) hε₀pos)
  obtain ⟨b, hb, hxb⟩ := (infDist_lt_iff ⟨0, L.zero_mem⟩).1
    (lt_add_of_pos_right (infDist x (L : Set E)) hε₀pos)
  obtain ⟨a', ha', b', hb', hab, ha'n, -⟩ :=
    hC (a - b) (mem_sup.2 ⟨a, ha, -b, L.neg_mem hb, by rw [sub_eq_add_neg]⟩)
  have hmem : a - a' ∈ G ⊓ L := by
    refine ⟨G.sub_mem ha ha', ?_⟩
    have : a - a' = b + b' := by rw [← sub_eq_iff_eq_add'.2 hab]; abel
    rw [this]
    exact L.add_mem hb hb'
  have hab' : ‖a - b‖ ≤ dist x a + dist x b := by
    rw [dist_eq_norm, dist_eq_norm, ← norm_neg (x - a), neg_sub]
    calc ‖a - b‖ = ‖(a - x) + (x - b)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖a - x‖ + ‖x - b‖ := norm_add_le _ _
  have h1 : ‖a'‖ ≤ C * (dist x a + dist x b) := ha'n.trans (mul_le_mul_of_nonneg_left hab' hC0)
  have h3 : C * dist x a ≤ C * (infDist x (G : Set E) + ε₀) := mul_le_mul_of_nonneg_left hxa.le hC0
  have h4 : C * dist x b ≤ C * (infDist x (L : Set E) + ε₀) := mul_le_mul_of_nonneg_left hxb.le hC0
  calc infDist x (G ⊓ L : Submodule 𝕜 E) ≤ dist x (a - a') :=
        infDist_le_dist_of_mem (by exact_mod_cast hmem)
    _ ≤ dist x a + ‖a'‖ := by
        rw [dist_eq_norm, dist_eq_norm, sub_sub_eq_add_sub, add_sub_right_comm]
        exact norm_add_le _ _
    _ ≤ (1 + C) * (infDist x (G : Set E) + infDist x (L : Set E)) + ε := by
        have := infDist_nonneg (x := x) (s := (L : Set E))
        linarith

/-- Let $G$ and $L$ be closed subspaces of a Banach space $E$, and let $C$ be a real number such
that
$$\operatorname{dist}(x, G \cap L) \le C \operatorname{dist}(x, L) \quad \text{for every } x \in
  G.$$
Then $G + L$ is closed. This is Exercise 2.16 of [brezis2011functional], the converse of
Corollary 2.11 that its Remark 7 announces.

The source argues through the quotient $E / L$. Here the closed range criterion
`ContinuousLinearMap.isClosed_range_iff_exists_infDist_ker_le` is applied to the addition map
$T \colon G \times L \to E$. Its range is $G + L$ and its kernel is
$\{(w, -w) : w \in G \cap L\}$. For $(x, y) \in G \times L$, $\operatorname{dist}((x, y), \ker
T) \le \operatorname{dist}(x, G \cap L) + \|x + y\| \le (C + 1) \|x + y\|$. -/
theorem isClosed_sup_of_forall_infDist_inf_le (G L : Submodule 𝕜 E) (hG : IsClosed (G : Set E))
    (hL : IsClosed (L : Set E)) {C : ℝ}
    (h : ∀ x ∈ G, infDist x (G ⊓ L : Submodule 𝕜 E) ≤ C * infDist x (L : Set E)) :
    IsClosed ((G ⊔ L : Submodule 𝕜 E) : Set E) := by
  have := hG.completeSpace_coe
  have := hL.completeSpace_coe
  let T : G × L →L[𝕜] E := G.subtypeL.coprod L.subtypeL
  have hT : ∀ p : G × L, T p = p.1 + p.2 := fun p => rfl
  have hrange : Set.range T = ((G ⊔ L : Submodule 𝕜 E) : Set E) := by
    ext z
    constructor
    · rintro ⟨⟨x, y⟩, rfl⟩
      exact add_mem_sup x.2 y.2
    · intro hz
      obtain ⟨x, hx, y, hy, rfl⟩ := mem_sup.1 hz
      exact ⟨(⟨x, hx⟩, ⟨y, hy⟩), rfl⟩
  rw [← hrange, T.isClosed_range_iff_exists_infDist_ker_le]
  refine ⟨max C 0 + 1, fun p => ?_⟩
  obtain ⟨x, y⟩ := p
  rw [hT]
  have hne : ((G ⊓ L : Submodule 𝕜 E) : Set E).Nonempty := ⟨0, (G ⊓ L).zero_mem⟩
  -- `dist ((x, y), N(T)) ≤ dist (x, G ∩ L) + ‖x + y‖`
  have hker : infDist (x, y) (T.ker : Set (G × L)) ≤
      infDist (x : E) (G ⊓ L : Submodule 𝕜 E) + ‖(x : E) + y‖ := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨w, hw, hxw⟩ := (infDist_lt_iff hne).1
      (lt_add_of_pos_right (infDist (x : E) (G ⊓ L : Submodule 𝕜 E)) hε)
    have hw' : w ∈ G ⊓ L := hw
    let q : G × L := (⟨w, hw'.1⟩, ⟨-w, L.neg_mem hw'.2⟩)
    have hq : q ∈ T.ker := by
      rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, hT]
      exact add_neg_cancel w
    calc infDist (x, y) (T.ker : Set (G × L)) ≤ dist (x, y) q := infDist_le_dist_of_mem hq
      _ = max (dist (x : E) w) ‖(y : E) + w‖ := by
          rw [Prod.dist_eq, Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm (y : E), sub_neg_eq_add]
      _ ≤ dist (x : E) w + ‖(x : E) + y‖ := by
          refine max_le (le_add_of_nonneg_right (norm_nonneg _)) ?_
          rw [dist_eq_norm, add_comm (‖(x : E) - w‖)]
          calc ‖(y : E) + w‖ = ‖((x : E) + y) - ((x : E) - w)‖ := by
                congr 1; abel
            _ ≤ ‖(x : E) + y‖ + ‖(x : E) - w‖ := norm_sub_le _ _
      _ ≤ infDist (x : E) (G ⊓ L : Submodule 𝕜 E) + ‖(x : E) + y‖ + ε := by linarith
  -- `dist (x, G ∩ L) ≤ C dist (x, L) ≤ C ‖x + y‖`, since `-y ∈ L`
  have hL' : infDist (x : E) (L : Set E) ≤ ‖(x : E) + y‖ := by
    have := infDist_le_dist_of_mem (x := (x : E)) (L.neg_mem y.2)
    rwa [dist_eq_norm, sub_neg_eq_add] at this
  calc infDist (x, y) (T.ker : Set (G × L))
      ≤ infDist (x : E) (G ⊓ L : Submodule 𝕜 E) + ‖(x : E) + y‖ := hker
    _ ≤ max C 0 * infDist (x : E) (L : Set E) + ‖(x : E) + y‖ := by
        have := h x x.2
        have hle : C * infDist (x : E) (L : Set E) ≤ max C 0 * infDist (x : E) (L : Set E) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) infDist_nonneg
        linarith
    _ ≤ max C 0 * ‖(x : E) + y‖ + ‖(x : E) + y‖ := by
        have := mul_le_mul_of_nonneg_left hL' (le_max_right C 0)
        linarith
    _ = (max C 0 + 1) * ‖(x : E) + y‖ := by ring

/-- Let $G$ and $L$ be closed subspaces of a Banach space $E$. Then $G + L$ is closed if and only if
there is a constant $C$ such that
$$\operatorname{dist}(x, G \cap L) \le C \bigl(\operatorname{dist}(x, G) +
  \operatorname{dist}(x, L)\bigr) \quad \text{for every } x \in E.$$
This combines Corollary 2.11 of [brezis2011functional] with its Remark 7 and Exercise 2.16. -/
theorem isClosed_sup_iff_exists_infDist_inf_le (G L : Submodule 𝕜 E) (hG : IsClosed (G : Set E))
    (hL : IsClosed (L : Set E)) :
    IsClosed ((G ⊔ L : Submodule 𝕜 E) : Set E) ↔ ∃ C : ℝ, ∀ x : E,
      infDist x (G ⊓ L : Submodule 𝕜 E) ≤ C * (infDist x (G : Set E) + infDist x (L : Set E)) := by
  refine ⟨exists_infDist_inf_le_of_isClosed_sup G L hG hL, fun ⟨C, hC⟩ => ?_⟩
  refine isClosed_sup_of_forall_infDist_inf_le G L hG hL (C := C) fun x hx => ?_
  have := hC x
  rwa [infDist_zero_of_mem (s := (G : Set E)) hx, zero_add] at this

end Submodule

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace E] [CompleteSpace F]

/-- Let $T \colon E \to F$ be a surjective bounded linear operator between Banach spaces whose
kernel is complemented, that is, there is a bounded linear projection of $E$ onto $\ker T$. Then
$T$ has a bounded right inverse: a bounded linear operator $S \colon F \to E$ with $TS = I$.
This is the implication (ii) ⇒ (i) of Theorem 2.12 of [brezis2011functional].

Let $L$ be a topological complement of $\ker T$. Then $T$ restricted to $L$ is a bijection
$L \to F$, its inverse is bounded by the open mapping theorem, and its composition with the
inclusion of $L$ in $E$ is a right inverse of $T$. -/
theorem HasRightInverse.of_surjective_of_closedComplemented_ker {T : E →L[𝕜] F}
    (hT : Function.Surjective T) (hker : T.ker.ClosedComplemented) : T.HasRightInverse := by
  obtain ⟨L, hL⟩ := hker.exists_isTopCompl
  have := hL.isClosed'.completeSpace_coe
  let S : L →L[𝕜] F := T.comp L.subtypeL
  have hS : ∀ x : L, S x = T x := fun x => rfl
  have hinj : S.ker = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    rw [ContinuousLinearMap.coe_coe, hS] at hx
    have hx' : (x : E) ∈ T.ker ⊓ L := ⟨hx, x.2⟩
    rw [hL.isCompl.inf_eq_bot] at hx'
    exact Subtype.ext ((Submodule.mem_bot 𝕜).1 hx')
  have hsurj : S.range = ⊤ := by
    rw [eq_top_iff]
    rintro f -
    obtain ⟨x, rfl⟩ := hT f
    have hx : x ∈ T.ker ⊔ L := by rw [hL.isCompl.sup_eq_top]; trivial
    obtain ⟨k, hk, l, hl, rfl⟩ := Submodule.mem_sup.1 hx
    refine ⟨⟨l, hl⟩, ?_⟩
    have hk' : T k = 0 := (LinearMap.mem_ker).1 hk
    rw [ContinuousLinearMap.coe_coe, hS, map_add, hk', zero_add]
  let e := ContinuousLinearEquiv.ofBijective S hinj hsurj
  refine ⟨L.subtypeL.comp (e.symm : F →L[𝕜] L), fun f => ?_⟩
  change T (L.subtypeL (e.symm f)) = f
  exact ContinuousLinearEquiv.ofBijective_apply_symm_apply S hinj hsurj f

/-- Let $T \colon E \to F$ be a surjective bounded linear operator between Banach spaces. Then $T$
has a bounded right inverse if and only if $\ker T$ is complemented, that is, there is a bounded
linear projection of $E$ onto $\ker T$. This is Theorem 2.12 of [brezis2011functional]. -/
theorem hasRightInverse_iff_closedComplemented_ker {T : E →L[𝕜] F} (hT : Function.Surjective T) :
    T.HasRightInverse ↔ T.ker.ClosedComplemented :=
  ⟨fun ⟨S, hS⟩ => T.closedComplemented_ker_of_rightInverse S hS,
    HasRightInverse.of_surjective_of_closedComplemented_ker hT⟩

/-- Let $T \colon E \to F$ be an injective bounded linear operator between Banach spaces. Then $T$
has a bounded left inverse, that is, a bounded linear operator $S \colon F \to E$ with $ST = I$,
if and only if the range of $T$ is closed and complemented. This is Theorem 2.13 of
[brezis2011functional].

Both directions are in Mathlib: `ContinuousLinearMap.HasLeftInverse.isClosed_range`,
`ContinuousLinearMap.HasLeftInverse.closedComplemented_range` and
`ContinuousLinearMap.HasLeftInverse.of_injective_of_isClosed_range_of_closedComplement_range`.
The statement is recorded so that Theorems 2.12 and 2.13 have the same form. -/
theorem hasLeftInverse_iff_isClosed_range_and_closedComplemented_range {T : E →L[𝕜] F}
    (hT : Function.Injective T) :
    T.HasLeftInverse ↔ IsClosed (Set.range T) ∧ T.range.ClosedComplemented :=
  ⟨fun h => ⟨h.isClosed_range, h.closedComplemented_range⟩,
    fun h => HasLeftInverse.of_injective_of_isClosed_range_of_closedComplement_range hT h.1 h.2⟩

end ContinuousLinearMap
