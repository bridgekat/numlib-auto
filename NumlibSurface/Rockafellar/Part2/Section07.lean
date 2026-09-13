import Mathlib.Tactic.TFAE
import Numlib.Analysis.Convex.Operations.Basic
import Numlib.Analysis.Convex.RelativeInterior
import NumlibSurface.Common.Euclidean
import NumlibSurface.Rockafellar.Part1.Section01

/-!
# Rockafellar, §7: Closures of Convex Functions

Lower semicontinuity, the lower semicontinuous hull, the closure `cl f` of a convex function, and
closed convex functions. All 17 numbered results of §7 are formalized.

Lower semicontinuity is Mathlib's `LowerSemicontinuous`; the lower semicontinuous hull is
`lscHull`, characterised as the greatest lsc minorant by `lscHull_isGreatest`; the closure of a
convex function is `clFn`; and a closed convex function is one with `ClosedFn f`. Two unnumbered
claims of the text are recorded as `closedFn_iff_lowerSemicontinuous_of_proper` and
`closed_improper_eq_const` — the only closed improper convex functions are the constants `+∞`
and `−∞`.

## The `cl f` case split, and the book's slip about `epi (cl f)`

Rockafellar defines `cl f` by cases: the lower semicontinuous hull when `f` is nowhere `−∞`, and
the constant `−∞` otherwise. The backbone's `clFn` branches on the *hull* taking `−∞` rather than
on `f` doing so, which is the standard Γ-regularisation and the only branch that keeps
`f** = cl f` true; `ConvexFn.clFn_eq_lscHull` is the proof that the two descriptions agree.

The book then asserts `epi (cl f) = cl (epi f)` "by definition". **That is false for improper
`f`**: when `f` takes the value `−∞`, `cl f ≡ −∞` and `epi (cl f)` is all of `ℝⁿ⁺¹`, while
`cl (epi f)` is `cl (dom f) × ℝ`. The identity holds for the *hull* with no hypothesis at all
(`epi_lscHull`), and for `cl f` exactly when `f` is proper. No statement below inherits the slip:
every use of it goes through `epi_lscHull` or through properness.

## References

* [rockafellar1970convex] §7.
-/

open Set Filter Topology

namespace Rockafellar

open ConvexAnalysis NumlibSurface

variable {n : ℕ} {f g : Rn n → EReal}

/-! ### The definitions of §7 -/

/-- **Rockafellar §7**, the sentence defining the lower semicontinuous hull: "there exists a
greatest lower semi-continuous function (not necessarily finite) majorized by `f`". -/
theorem lscHull_isGreatest (f : Rn n → EReal) :
    IsGreatest {g : Rn n → EReal | LowerSemicontinuous g ∧ g ≤ f} (lscHull f) :=
  isGreatest_lscHull f

/-- **Rockafellar §7**: "For a proper convex function, closedness is thus the same as lower
semi-continuity." Only the `≠ -∞` half of properness is used, and convexity is not used at all. -/
theorem closedFn_iff_lowerSemicontinuous_of_proper (hp : Proper f) :
    ClosedFn f ↔ LowerSemicontinuous f :=
  closedFn_iff_lowerSemicontinuous hp.ne_bot

/-- **Rockafellar §7**: "the only closed improper convex functions are the constant functions `+∞`
and `−∞`". Convexity is not needed. -/
theorem closed_improper_eq_const (hc : ClosedFn f) (himp : ¬ Proper f) :
    f = (fun _ => (⊥ : EReal)) ∨ f = fun _ => (⊤ : EReal) :=
  eq_const_of_closedFn_of_not_proper hc himp

/-! ### Dimension bookkeeping

Corollary 6.3.1 in the form Corollary 7.4.1 and Theorem 7.6 need; `dim` itself is §1's. -/

/-- Non-empty sets with the same affine hull have the same dimension. -/
theorem dim_eq_of_affineSpan_eq {S T : Set (Rn n)} (hS : S.Nonempty) (hT : T.Nonempty)
    (h : affineSpan ℝ S = affineSpan ℝ T) : dim S = dim T := by
  rw [dim_eq_finrank_direction hS, dim_eq_finrank_direction hT, h]

/-- **Corollary 6.3.1**, dimension half: sets with the same closure have the same
dimension, because they have the same affine hull. -/
theorem dim_eq_of_closure_eq {S T : Set (Rn n)} (h : closure S = closure T) : dim S = dim T := by
  have hspan : affineSpan ℝ S = affineSpan ℝ T := by
    rw [← affineSpan_closure S, h, affineSpan_closure]
  rcases Set.eq_empty_or_nonempty S with hS | hS
  · have hT : T = ∅ := (closure_empty_iff T).1 (by rw [← h, hS, closure_empty])
    rw [hS, hT]
  · have hT : T.Nonempty := by
      rcases Set.eq_empty_or_nonempty T with hTe | hTe
      · exact absurd ((closure_empty_iff S).1 (by rw [h, hTe, closure_empty])) hS.ne_empty
      · exact hTe
    exact dim_eq_of_affineSpan_eq hS hT hspan

/-! ### Theorem 7.1 -/

/-- **Theorem 7.1.** Let `f` be an arbitrary function from `ℝⁿ` to `[-∞, +∞]`. Then
the following conditions are equivalent:

(a) `f` is lower semi-continuous throughout `ℝⁿ`;

(b) `{x | f x ≤ α}` is closed for every `α ∈ R`;

(c) the epigraph of `f` is a closed set in `ℝⁿ⁺¹`.

Neither convexity nor finite dimension enters; the book's `ℝⁿ⁺¹` is `Rn n × ℝ`. -/
theorem theorem_7_1 (f : Rn n → EReal) :
    List.TFAE [LowerSemicontinuous f, ∀ α : ℝ, IsClosed {x | f x ≤ (α : EReal)},
      IsClosed (epi f)] := by
  tfae_have 1 ↔ 2 := lowerSemicontinuous_iff_isClosed_le
  tfae_have 1 ↔ 3 := lowerSemicontinuous_iff_isClosed_epi
  tfae_finish

/-! ### Theorem 7.2 and its corollaries -/

/-- **Theorem 7.2.** If `f` is an improper convex function, then `f x = -∞` for every
`x ∈ ri (dom f)`. Thus an improper convex function is necessarily infinite except perhaps at
relative boundary points of its effective domain. No properness hypothesis is added: the theorem is
*about* improper functions. -/
theorem theorem_7_2 (hf : ConvexFn f) (himp : ¬ Proper f) {x : Rn n} (hx : x ∈ ri (dom f)) :
    f x = ⊥ :=
  hf.eq_bot_of_mem_relint_dom himp hx

/-- **Corollary 7.2.1.** A lower semicontinuous improper convex function has no finite
values. -/
theorem corollary_7_2_1 (hf : ConvexFn f) (hl : LowerSemicontinuous f) (himp : ¬ Proper f)
    (x : Rn n) : f x = ⊥ ∨ f x = ⊤ := by
  by_cases hx : x ∈ closure (dom f)
  · exact Or.inl (hf.eq_bot_of_mem_closure_dom hl himp hx)
  · refine Or.inr ?_
    by_contra h
    exact hx (subset_closure (mem_dom.2 (lt_of_le_of_ne le_top h)))

/-- **Corollary 7.2.2.** Let `f` be an improper convex function. Then `cl f` is a
closed improper convex function which agrees with `f` on `ri (dom f)`.

Note that the agreement is *not* obtained from `epi (cl f) = cl (epi f)`, which fails exactly in
this improper case. -/
theorem corollary_7_2_2 (hf : ConvexFn f) (himp : ¬ Proper f) :
    ConvexFn (clFn f) ∧ ClosedFn (clFn f) ∧ ¬ Proper (clFn f) ∧
      ∀ x ∈ ri (dom f), clFn f x = f x :=
  ⟨convexFn_clFn hf, closedFn_clFn f, not_proper_clFn himp,
    fun _ hx => hf.clFn_eq_of_mem_relint_dom hx⟩

/-- **Corollary 7.2.3.** If `f` is a convex function whose effective domain is
relatively open (for instance if `dom f = ℝⁿ`), then either `f x > -∞` for every `x`, or `f x` is
infinite for every `x`. -/
theorem corollary_7_2_3 (hf : ConvexFn f) (hopen : ri (dom f) = dom f) :
    (∀ x, f x ≠ ⊥) ∨ ∀ x, f x = ⊥ ∨ f x = ⊤ :=
  hf.forall_ne_bot_or_forall_infinite hopen

/-! ### Lemma 7.3 and its corollaries -/

/-- **Lemma 7.3.** For any convex function `f`, `ri (epi f)` consists of the pairs
`(x, μ)` such that `x ∈ ri (dom f)` and `f x < μ < ∞`.

The book's `μ < ∞` is carried by the type: the second component of a point of `ℝⁿ⁺¹ = Rn n × ℝ` is a
real number. -/
theorem lemma_7_3 (hf : ConvexFn f) :
    ri (epi f) = {p : Rn n × ℝ | p.1 ∈ ri (dom f) ∧ f p.1 < (p.2 : EReal)} :=
  hf.relint_epi

/-- **Corollary 7.3.1.** Let `α` be a real number, and let `f` be a convex function
such that, for some `x`, `f x < α`. Then actually `f x < α` for some `x ∈ ri (dom f)`. -/
theorem corollary_7_3_1 (hf : ConvexFn f) {α : ℝ} (h : ∃ x, f x < (α : EReal)) :
    ∃ x ∈ ri (dom f), f x < (α : EReal) :=
  hf.exists_mem_relint_dom_lt h

/-- **Corollary 7.3.2.** For convex `f` and convex `C` with `ri C ⊆ dom f`: if `f x < α` for some
`x ∈ cl C`, then `f x < α` for some `x ∈ ri C`. -/
theorem corollary_7_3_2 (hf : ConvexFn f) {C : Set (Rn n)} (hC : Convex ℝ C)
    (hsub : ri C ⊆ dom f) {α : ℝ} (h : ∃ x ∈ closure C, f x < (α : EReal)) :
    ∃ x ∈ ri C, f x < (α : EReal) := by
  have hgc : ConvexFn (ConvexAnalysis.restrictFn (closure C) f) := hf.restrictFn hC.closure
  have hle : dom (ConvexAnalysis.restrictFn (closure C) f) ⊆ closure C := by
    intro z hz
    by_contra hzc
    rw [mem_dom, restrictFn_of_notMem hzc] at hz
    exact absurd hz (lt_irrefl ⊤)
  have hge : ri C ⊆ dom (ConvexAnalysis.restrictFn (closure C) f) := by
    intro z hz
    rw [mem_dom, restrictFn_of_mem (subset_closure (intrinsicInterior_subset hz))]
    exact hsub hz
  have hri : ri (dom (ConvexAnalysis.restrictFn (closure C) f)) = ri C :=
    (Convex.closure_eq_iff_relint_eq hgc.convex_dom hC).1
      (Convex.closure_eq_of_relint_subset_of_subset_closure hC hge hle)
  have hex : ∃ y, ConvexAnalysis.restrictFn (closure C) f y < (α : EReal) := by
    obtain ⟨x, hx, hxα⟩ := h
    exact ⟨x, by rw [restrictFn_of_mem hx]; exact hxα⟩
  obtain ⟨z, hz, hzα⟩ := hgc.exists_mem_relint_dom_lt hex
  rw [hri] at hz
  rw [restrictFn_of_mem (subset_closure (intrinsicInterior_subset hz))] at hzα
  exact ⟨z, hz, hzα⟩

/-- **Corollary 7.3.3.** For convex `f` finite on a convex set `C`: if `f x ≥ α` throughout `C`,
then `f x ≥ α` throughout `cl C`. Stated in the book's form, which needs `f ≠ -∞` only on `C`,
where the backbone's `ConvexFn.le_of_mem_closure` assumes it globally. -/
theorem corollary_7_3_3 (hf : ConvexFn f) {C : Set (Rn n)} (hC : Convex ℝ C)
    (hfin : ∀ x ∈ C, f x ≠ ⊥ ∧ f x ≠ ⊤) {α : ℝ} (hge : ∀ x ∈ C, (α : EReal) ≤ f x) {x : Rn n}
    (hx : x ∈ closure C) : (α : EReal) ≤ f x := by
  by_contra hlt
  obtain ⟨z, hz, hzα⟩ := corollary_7_3_2 hf hC
    (fun y hy => mem_dom.2 (lt_of_le_of_ne le_top (hfin y (intrinsicInterior_subset hy)).2))
    ⟨x, hx, not_le.1 hlt⟩
  exact absurd (hge z (intrinsicInterior_subset hz)) (not_le.2 hzα)

/-- **Corollary 7.3.4.** If convex `f` and `g` have `ri (dom f) = ri (dom g)` and agree there,
then `cl f = cl g`. No improper case split is needed, unlike in the book, because `clFn` is a
function of `lscHull` alone. -/
theorem corollary_7_3_4 (hf : ConvexFn f) (hg : ConvexFn g) (hdom : ri (dom f) = ri (dom g))
    (hagree : ∀ x ∈ ri (dom f), f x = g x) : clFn f = clFn g := by
  have hri : ri (epi f) = ri (epi g) := by
    rw [hf.relint_epi, hg.relint_epi]
    ext p
    simp only [Set.mem_ofPred_eq, ← hdom]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by rwa [← hagree p.1 h1]⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by rwa [hagree p.1 h1]⟩
  have hcl : closure (epi f) = closure (epi g) :=
    (Convex.closure_eq_iff_relint_eq hf.convex_epi hg.convex_epi).2 hri
  have hhull : lscHull f = lscHull g := epi_injective (by rw [epi_lscHull, epi_lscHull, hcl])
  by_cases hb : ∃ x, lscHull f x = ⊥
  · obtain ⟨x, hx⟩ := hb
    rw [clFn_of_exists_eq_bot ⟨x, hx⟩,
      clFn_of_exists_eq_bot ⟨x, by rw [← hhull]; exact hx⟩]
  · rw [clFn_of_forall_ne_bot (fun x hx => hb ⟨x, hx⟩),
      clFn_of_forall_ne_bot (fun x hx => hb ⟨x, by rw [hhull]; exact hx⟩), hhull]

/-! ### Theorem 7.4 and its corollaries -/

/-- **Theorem 7.4.** Let `f` be a proper convex function on `ℝⁿ`. Then `cl f` is a
closed proper convex function. Moreover, `cl f` agrees with `f` except perhaps at relative
boundary points of `dom f` — that is, off `cl (dom f) \ ri (dom f)`. -/
theorem theorem_7_4 (hf : ConvexFn f) (hp : Proper f) :
    ClosedProperConvexFn (clFn f) ∧ ∀ x ∉ closure (dom f) \ ri (dom f), clFn f x = f x := by
  refine ⟨⟨convexFn_clFn hf, closedFn_clFn f, hf.proper_clFn hp⟩, fun x hx => ?_⟩
  by_cases hc : x ∈ closure (dom f)
  · exact hf.clFn_eq_of_mem_relint_dom (by
      by_contra hr
      exact hx ⟨hc, hr⟩)
  · exact hf.clFn_eq_of_notMem_closure_dom hp hc

/-- **Corollary 7.4.1.** If `f` is a proper convex function, then `dom (cl f)` differs from `dom f`
at most by including some additional relative boundary points of `dom f`. In particular,
`dom (cl f)` and `dom f` have the same closure and relative interior, as well as the same dimension.
The dimension clause is `dim_eq_of_closure_eq`, which belongs to §6. -/
theorem corollary_7_4_1 (hf : ConvexFn f) (hp : Proper f) :
    dom f ⊆ dom (clFn f) ∧ dom (clFn f) ⊆ closure (dom f) ∧
      closure (dom (clFn f)) = closure (dom f) ∧ ri (dom (clFn f)) = ri (dom f) ∧
        dim (dom (clFn f)) = dim (dom f) := by
  have hsub : dom f ⊆ dom (clFn f) := by
    rw [hf.clFn_eq_lscHull hp]; exact dom_subset_dom_lscHull f
  have hsup : dom (clFn f) ⊆ closure (dom f) := by
    rw [hf.clFn_eq_lscHull hp]; exact dom_lscHull_subset_closure_dom f
  have hcl : closure (dom (clFn f)) = closure (dom f) :=
    Convex.closure_eq_of_relint_subset_of_subset_closure hf.convex_dom
      (intrinsicInterior_subset.trans hsub) hsup
  exact ⟨hsub, hsup, hcl, hf.relint_dom_clFn hp, dim_eq_of_closure_eq hcl⟩

/-- **Corollary 7.4.2.** If `f` is a proper convex function such that `dom f` is an
affine set (which is true in particular if `f` is finite throughout `ℝⁿ`), then `f` is closed.

`IsAffineSet` and its bridge to `AffineSubspace` are §1's (`Section01.lean`). -/
theorem corollary_7_4_2 (hf : ConvexFn f) (hp : Proper f) (hdom : IsAffineSet (dom f)) :
    ClosedFn f :=
  hf.closedFn_of_dom_eq_coe hp hdom.coe_toAffineSubspace.symm

/-! ### Theorem 7.5 and its corollary -/

/-- **Theorem 7.5.** Let `f` be a proper convex function, and let `x ∈ ri (dom f)`. Then
`(cl f) y = lim_{λ ↑ 1} f ((1 - λ) x + λ y)` for every `y`. The book's `λ ↑ 1` is the filter
`𝓝[<] (1 : ℝ)`. -/
theorem theorem_7_5 (hf : ConvexFn f) (hp : Proper f) {x : Rn n} (hx : x ∈ ri (dom f))
    (y : Rn n) :
    Tendsto (fun a : ℝ => f ((1 - a) • x + a • y)) (𝓝[<] (1 : ℝ)) (𝓝 (clFn f y)) :=
  hf.tendsto_clFn_along_segment_relint hp hx y

/-- **Theorem 7.5**, parenthetical clause: the formula is also valid for improper `f` and
`y ∈ cl (dom f)`. The restriction to `cl (dom f)` is not decorative — off it the function along
the segment is eventually `+∞`. -/
theorem theorem_7_5_improper (hf : ConvexFn f) (himp : ¬ Proper f) {x : Rn n}
    (hx : x ∈ ri (dom f)) {y : Rn n} (hy : y ∈ closure (dom f)) :
    Tendsto (fun a : ℝ => f ((1 - a) • x + a • y)) (𝓝[<] (1 : ℝ)) (𝓝 (clFn f y)) := by
  have hxbot : f x = ⊥ := hf.eq_bot_of_mem_relint_dom himp hx
  have hhull : lscHull f x = ⊥ := le_bot_iff.1 (by rw [← hxbot]; exact lscHull_le f x)
  rw [clFn_of_exists_eq_bot ⟨x, hhull⟩]
  refine Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [eventually_mem_Ico_nhdsLT_one] with a ha
  exact (hf.eq_bot_of_mem_relint_dom himp
    (Convex.segment_mem_relint hf.convex_dom hx hy ha.1 ha.2)).symm

/-- **Corollary 7.5.1.** For a closed proper convex function `f`, one has
`f y = lim_{λ ↑ 1} f ((1 - λ) x + λ y)` for every `x ∈ dom f` and every `y`.

The backbone proves this directly rather than through Theorem 7.5 and a restriction to a line, so no
relative interiors appear. -/
theorem corollary_7_5_1 (hf : ClosedProperConvexFn f) {x : Rn n} (hx : x ∈ dom f) (y : Rn n) :
    Tendsto (fun a : ℝ => f ((1 - a) • x + a • y)) (𝓝[<] (1 : ℝ)) (𝓝 (f y)) :=
  tendsto_along_segment_of_closed_proper hf hx y

/-! ### Theorem 7.6 and its corollary -/

/-- For `α` above the infimum of a convex `f`, the set `{x ∈ ri (dom f) | f x < α}` has the same
affine hull as `dom f`, hence the same dimension. The step Theorem 7.6's dimension clause needs;
the book takes it by a slice dimension count, this by the line segment principle. -/
theorem affineSpan_relint_dom_lt (hf : ConvexFn f) {α : ℝ} (hα : ⨅ x, f x < (α : EReal)) :
    affineSpan ℝ {x ∈ ri (dom f) | f x < (α : EReal)} = affineSpan ℝ (dom f) := by
  obtain ⟨y, hy, hyα⟩ := hf.exists_mem_relint_dom_lt (iInf_lt_iff.1 hα)
  set R : Set (Rn n) := {x ∈ ri (dom f) | f x < (α : EReal)} with hR
  refine le_antisymm (affineSpan_mono ℝ fun z hz => intrinsicInterior_subset hz.1) ?_
  rw [← hf.convex_dom.affineSpan_relint, affineSpan_le]
  intro x hx
  by_cases hxα : f x < (α : EReal)
  · exact subset_affineSpan ℝ R ⟨hx, hxα⟩
  obtain ⟨β, hyβ, hβα⟩ := EReal.lt_iff_exists_real_btwn.1 hyα
  obtain ⟨γ, hxγ, -⟩ :=
    EReal.lt_iff_exists_real_btwn.1 (mem_dom.1 (intrinsicInterior_subset hx))
  have hβα' : β < α := by exact_mod_cast hβα
  have hpos : (0 : ℝ) < α - β := by linarith
  set t : ℝ := min (1 / 2) ((α - β) / (2 * (|γ - β| + 1))) with ht
  have ht0 : 0 < t := lt_min (by norm_num) (div_pos hpos (by positivity))
  have ht1 : t < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have htb : t * (2 * (|γ - β| + 1)) ≤ α - β :=
    (le_div_iff₀ (by positivity)).1 (min_le_right _ _)
  have habs : t * (γ - β) ≤ t * |γ - β| := mul_le_mul_of_nonneg_left (le_abs_self _) ht0.le
  have hkey : (1 - t) * β + t * γ < α := by nlinarith [htb, habs, ht0, hβα']
  have hzri : (1 - t) • y + t • x ∈ ri (dom f) :=
    Convex.segment_mem_relint hf.convex_dom hy
      (subset_closure (intrinsicInterior_subset hx)) ht0.le ht1
  have hzα : f ((1 - t) • y + t • x) < (α : EReal) :=
    lt_of_le_of_lt (hf.epi_combo hyβ.le hxγ.le (by linarith) ht0.le (by ring))
      (by exact_mod_cast hkey)
  have hmem := AffineSubspace.combo_mem (M := affineSpan ℝ R)
    (subset_affineSpan ℝ R ⟨hy, hyα⟩) (subset_affineSpan ℝ R ⟨hzri, hzα⟩) t⁻¹
  rwa [combo_prolong y x ht0.ne'] at hmem


/-- **Theorem 7.6.** For proper convex `f` and real `α > inf f`, the level sets `{x | f x ≤ α}`
and `{x | f x < α}` have the same closure `{x | (cl f) x ≤ α}`, the same relative interior
`{x ∈ ri (dom f) | f x < α}`, and the same dimension as `dom f`. -/
theorem theorem_7_6 (hf : ConvexFn f) (hp : Proper f) {α : ℝ} (hα : ⨅ x, f x < (α : EReal)) :
    closure {x | f x ≤ (α : EReal)} = {x | clFn f x ≤ (α : EReal)} ∧
      closure {x | f x < (α : EReal)} = {x | clFn f x ≤ (α : EReal)} ∧
        ri {x | f x ≤ (α : EReal)} = {x ∈ ri (dom f) | f x < (α : EReal)} ∧
          ri {x | f x < (α : EReal)} = {x ∈ ri (dom f) | f x < (α : EReal)} ∧
            dim {x | f x ≤ (α : EReal)} = dim (dom f) ∧
              dim {x | f x < (α : EReal)} = dim (dom f) := by
  obtain ⟨y, hy, hyα⟩ := hf.exists_mem_relint_dom_lt (iInf_lt_iff.1 hα)
  have hdim : ∀ S : Set (Rn n), Convex ℝ S → S.Nonempty →
      ri S = {x ∈ ri (dom f) | f x < (α : EReal)} → dim S = dim (dom f) := by
    intro S hS hne hri
    refine dim_eq_of_affineSpan_eq hne ⟨y, intrinsicInterior_subset hy⟩ ?_
    rw [← hS.affineSpan_relint, hri, affineSpan_relint_dom_lt hf hα]
  exact ⟨hf.closure_setOf_le_clFn hp hα,
    by rw [hf.closure_setOf_lt hα, hf.clFn_eq_lscHull hp],
    hf.relint_setOf_le hα, hf.relint_setOf_lt hα,
    hdim _ (hf.convex_le _) ⟨y, hyα.le⟩ (hf.relint_setOf_le hα),
    hdim _ (hf.convex_lt _) ⟨y, hyα⟩ (hf.relint_setOf_lt hα)⟩

/-- **Corollary 7.6.1.** If `f` is a closed proper convex function whose effective
domain is relatively open (in particular if `dom f` is an affine set), then for
`inf f < α < +∞` one has `ri {x | f x ≤ α} = {x | f x < α}` and
`cl {x | f x < α} = {x | f x ≤ α}`.

The book's `α < +∞` is carried by `α : ℝ`. The two hypotheses split: the first formula needs only
relative openness of `dom f`, and the second only closedness. -/
theorem corollary_7_6_1 (hf : ConvexFn f) (hp : Proper f) (hc : ClosedFn f)
    (hopen : ri (dom f) = dom f) {α : ℝ} (hα : ⨅ x, f x < (α : EReal)) :
    ri {x | f x ≤ (α : EReal)} = {x | f x < (α : EReal)} ∧
      closure {x | f x < (α : EReal)} = {x | f x ≤ (α : EReal)} :=
  ⟨hf.relint_setOf_le_of_relint_dom_eq hopen hα, hf.closure_setOf_lt_of_closedFn hp hc hα⟩

end Rockafellar
