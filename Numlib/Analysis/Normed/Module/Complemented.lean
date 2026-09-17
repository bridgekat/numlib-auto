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

What the open mapping theorem says about the geometry of closed subspaces of a Banach space, and
about one-sided inverses of bounded operators ([brezis2011functional], §2.4 and Exercise 2.16).

Mathlib already has the vocabulary: `Submodule.IsTopCompl` and `Submodule.ClosedComplemented`
(in a Banach space, a topological complement of a closed subspace is exactly a closed algebraic
complement, `Submodule.closedComplemented_iff_isClosed_exists_isClosed_isCompl`), and
`ContinuousLinearMap.HasRightInverse` / `HasLeftInverse` with the characterization of left
inverses `HasLeftInverse.of_injective_of_isClosed_range_of_closedComplement_range`. This file adds
what is missing.

## Main statements

* `Submodule.exists_add_eq_norm_le_of_isClosed_sup` — if `G`, `L` and `G + L` are closed, every
  `z ∈ G + L` decomposes as `z = x + y` with `x ∈ G`, `y ∈ L` and `‖x‖, ‖y‖ ≤ C ‖z‖`: the open
  mapping theorem for the surjection `G × L → G + L`, `(x, y) ↦ x + y`.
* `Submodule.exists_infDist_inf_le_of_isClosed_sup` — under the same hypotheses,
  `dist (x, G ∩ L) ≤ C (dist (x, G) + dist (x, L))` for every `x`.
* `Submodule.isClosed_sup_of_forall_infDist_inf_le` — the converse: if
  `dist (x, G ∩ L) ≤ C dist (x, L)` for all `x ∈ G`, then `G + L` is closed. This is proved
  through the closed range criterion `ContinuousLinearMap.isClosed_range_iff_exists_infDist_ker_le`
  for the map `G × L → E`, whose kernel is `{(w, -w) | w ∈ G ∩ L}`.
* `Submodule.isClosed_sup_iff_exists_infDist_inf_le` — the two combined as an equivalence.
* `ContinuousLinearMap.HasRightInverse.of_surjective_of_closedComplemented_ker`,
  `ContinuousLinearMap.hasRightInverse_iff_closedComplemented_ker` — a surjective bounded operator
  between Banach spaces has a bounded right inverse iff its kernel is complemented (the converse
  direction is Mathlib's `closedComplemented_ker_of_rightInverse`).
* `ContinuousLinearMap.hasLeftInverse_iff_isClosed_range_and_closedComplemented_range` — an
  injective bounded operator has a bounded left inverse iff its range is closed and complemented
  (both directions are Mathlib's, recorded here in the same shape as the right-inverse statement).

Mathlib's product `G × L` carries the sup norm, so the constant of the decomposition bounds
`max ‖x‖ ‖y‖` rather than the book's `‖x‖ + ‖y‖`; the two differ by a factor `2`.
-/

open Metric

namespace Submodule

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [CompleteSpace E]

/-- **Bounded decomposition of a closed sum** ([brezis2011functional], Theorem 2.10). If `G`, `L`
are closed subspaces of a Banach space with `G + L` closed, there is `C ≥ 0` such that every
`z ∈ G + L` can be written `z = x + y` with `x ∈ G`, `y ∈ L`, `‖x‖ ≤ C ‖z‖` and `‖y‖ ≤ C ‖z‖`.

This is the open mapping theorem (`ContinuousLinearMap.exists_preimage_norm_le`) for the
bounded surjection `G × L → G + L`, `(x, y) ↦ x + y`, between Banach spaces. -/
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

/-- **Distance to the intersection of a closed sum** ([brezis2011functional], Corollary 2.11). If
`G`, `L` and `G + L` are closed, there is `C` with
`dist (x, G ∩ L) ≤ C (dist (x, G) + dist (x, L))` for every `x`.

Given `a ∈ G`, `b ∈ L` nearly realizing the two distances, decompose `a - b = a' + b'` with
`‖a'‖ ≤ C ‖a - b‖` by `exists_add_eq_norm_le_of_isClosed_sup`; then `a - a' ∈ G ∩ L` and
`‖x - (a - a')‖ ≤ ‖x - a‖ + C (‖x - a‖ + ‖x - b‖)`. -/
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

/-- **A distance inequality forces a closed sum** ([brezis2011functional], Exercise 2.16, the
converse of Corollary 2.11 announced in its Remark 7). If `G`, `L` are closed subspaces of a
Banach space and `dist (x, G ∩ L) ≤ C dist (x, L)` for every `x ∈ G`, then `G + L` is closed.

The book argues through the quotient `E ⧸ L`; here the closed range criterion
`ContinuousLinearMap.isClosed_range_iff_exists_infDist_ker_le` is applied to the addition map
`T : G × L → E`, whose range is `G + L` and whose kernel is `{(w, -w) | w ∈ G ∩ L}`: for
`(x, y) ∈ G × L` one has `dist ((x, y), N(T)) ≤ dist (x, G ∩ L) + ‖x + y‖ ≤ (C + 1) ‖x + y‖`. -/
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

/-- **Closed sums through a distance inequality** ([brezis2011functional], Corollary 2.11 and
Remark 7 / Exercise 2.16): for closed subspaces `G`, `L` of a Banach space, `G + L` is closed iff
`dist (x, G ∩ L) ≤ C (dist (x, G) + dist (x, L))` for some `C` and all `x`. -/
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

/-- **A surjection with complemented kernel has a bounded right inverse**
([brezis2011functional], Theorem 2.12, (ii) ⇒ (i)). If `T : E → F` is a surjective bounded
operator between Banach spaces whose kernel has a topological complement `L`, then `T` restricted
to `L` is a bijection `L → F`, its inverse is bounded by the open mapping theorem, and composing
with the inclusion of `L` gives a right inverse of `T`. -/
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

/-- **Right inverses of a surjection** ([brezis2011functional], Theorem 2.12): a surjective
bounded operator between Banach spaces has a bounded right inverse iff its kernel is
complemented. -/
theorem hasRightInverse_iff_closedComplemented_ker {T : E →L[𝕜] F} (hT : Function.Surjective T) :
    T.HasRightInverse ↔ T.ker.ClosedComplemented :=
  ⟨fun ⟨S, hS⟩ => T.closedComplemented_ker_of_rightInverse S hS,
    HasRightInverse.of_surjective_of_closedComplemented_ker hT⟩

/-- **Left inverses of an injection** ([brezis2011functional], Theorem 2.13): an injective bounded
operator between Banach spaces has a bounded left inverse iff its range is closed and
complemented. Both directions are Mathlib's (`HasLeftInverse.isClosed_range`,
`HasLeftInverse.closedComplemented_range` and
`HasLeftInverse.of_injective_of_isClosed_range_of_closedComplement_range`); the statement is
recorded so that Theorems 2.12 and 2.13 have the same shape. -/
theorem hasLeftInverse_iff_isClosed_range_and_closedComplemented_range {T : E →L[𝕜] F}
    (hT : Function.Injective T) :
    T.HasLeftInverse ↔ IsClosed (Set.range T) ∧ T.range.ClosedComplemented :=
  ⟨fun h => ⟨h.isClosed_range, h.closedComplemented_range⟩,
    fun h => HasLeftInverse.of_injective_of_isClosed_range_of_closedComplement_range hT h.1 h.2⟩

end ContinuousLinearMap
