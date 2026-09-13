import Numlib.Analysis.Convex.RelativeInterior
import Numlib.Analysis.Convex.Saddle.Equiv

/-!
# Kernels of saddle-functions

The **kernel** of a concave-convex function `K` is its restriction to the relative interior
`ri (dom₁ K) × ri (dom₂ K)` of its effective domain, and it is a complete invariant: two closed
proper concave-convex functions are equivalent exactly when their kernels agree. Every *simple*
proper such function determines a single equivalence class of closed proper functions with that
kernel, the order interval between its lower and upper closures; and closedness of a proper `K` is
visible in the two effective domains `C = dom₁ K` and `D = dom₂ K` alone, with no closure
operation involved.

## Main definitions

* `kernelSet K` — the rectangle `ri (dom₁ K) ×ˢ ri (dom₂ K)`, which is `ri (dom K)`; `kernel K` is
  `K` on that rectangle and `⊤` off it.
* `domSaddle K` — `dom K = dom₁ K × dom₂ K`; `ProperSaddleFn K` — both halves nonempty.
* `SaddleStructure K` — the six structural clauses of a closed proper saddle-function, as
  `ConvexSliceStructure` for `K` and for `saddleSwap K`.
* `SimpleSaddleFn K` — Rockafellar's *simple*: over `ri (dom₁ K)` the convex slices stay inside
  `cl (dom₂ K)`, and symmetrically.
* `lowerSimpleExt C D K`, `upperSimpleExt C D K` — the two simple extensions of a finite
  saddle-function on `C × D`.

## Main results

* `saddleEquiv_iff_kernel_eq` — equivalence is detected by the kernel (Theorem 34.4 in [^1]);
  `closedSaddleFn_iff_saddleStructure` — closedness is detected by the six structural clauses.
* `exists_unique_saddleEquiv_class_of_kernel` — a simple proper saddle-function has exactly one
  class of closed proper functions with its kernel (Theorem 34.5 in [^1]);
  `exists_unique_saddleEquiv_class_of_finite` — the same starting from a finite saddle-function.
* `kernel_partialCl₂`, `kernel_partialCl₁`, `SimpleSaddleFn.partialCl₂`,
  `SimpleSaddleFn.partialCl₁` — `cl₁` and `cl₂` preserve simplicity, properness and the kernel,
  which is the engine of that uniqueness.
* `lowerCl_idem`, `upperCl_idem` — the lower and upper closures are idempotent, with no duality.
* `mem_saddleClass_simpleExt_iff_saddleEquiv` — the extensions of a finite saddle-function with the
  prescribed infinite values off `C × D` are one full equivalence class;
  `SaddleEquiv.eq_of_mem_relint_dom₁` — equivalent closed functions agree over `ri (dom₁ K)`.
* `clFn_eq_of_eqOn_relint_dom`, `clConcave_eq_of_eqOn_relint_domConcave` — a closed convex function
  is determined by its values on `ri (dom f)`.
* `domConcave_bracket` — the concave effective domain of `u ↦ ⟨Fu, y⟩` is `dom F`;
  `bracket_eq_concaveBracket_adjointBifun_of_polyhedral` — for a proper polyhedral bifunction the
  relative interior may be dropped and the two brackets agree except at the pairs with `u ∉ dom F`
  *and* `y ∉ dom F*`; `exists_unique_bifun_of_simpleExt` — a finite continuous saddle-function on a
  closed `C × D` comes from a unique closed convex bifunction.

## Implementation notes

`kernel K` is a total function rather than a `Set.restrict`: equations between restrictions to
rectangles that move with the function are unusable, whereas `kernel K = kernel L` is one honest
equation, which `kernel_eq_iff` unpacks into "same rectangle, same values there". Taking the kernel
to be its *rectangle* alone would break the invariance, since `K` and `K + 1` share a rectangle.

Finite dimension is used only where `ri` appears. No pairing appears in any statement here:
concave-convexity of the partial closures is the only input from the duality layer, and over a
normed space the continuous dual supplies the compatible pairing internally.

## References

[^1]: R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §33 and §34.
-/

namespace ConvexAnalysis

open Filter Topology

/-! ### Closures agree when the functions agree on a common relative interior -/

section ClosureAgreement

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {f g : E → EReal}

/-- **Two convex functions that agree on the relative interior of a common effective domain have the
same lower semicontinuous hull** — the sharp form of "a closed convex function is determined by its
values on the relative interior of its effective domain". From a relative interior point the
half-open segment towards `y` stays in the relative interior, where the two agree; off
`cl (dom f)` both hulls are `⊤`. -/
theorem lscHull_eq_of_eqOn_relint_dom (hf : ConvexFn f) (hg : ConvexFn g)
    (hdom : ri (dom f) = ri (dom g)) (heq : Set.EqOn f g (ri (dom f))) :
    lscHull f = lscHull g := by
  rcases Set.eq_empty_or_nonempty (ri (dom f)) with hem | ⟨x, hx⟩
  · have hempty : ∀ {h : E → EReal}, ConvexFn h → ri (dom h) = ∅ → h = fun _ => ⊤ := by
      intro h hh hri
      have hd : dom h = ∅ := by
        rw [← Set.not_nonempty_iff_eq_empty]
        intro hne
        exact (Set.nonempty_iff_ne_empty.1 (Convex.relint_nonempty hh.convex_dom hne)) hri
      funext y
      have hy : y ∉ dom h := by rw [hd]; exact Set.notMem_empty y
      exact top_le_iff.1 (not_lt.1 hy)
    rw [hempty hf hem, hempty hg (hdom ▸ hem)]
  · have hx' : x ∈ ri (dom g) := hdom ▸ hx
    have hcl : closure (dom f) = closure (dom g) :=
      (Convex.closure_eq_iff_relint_eq hf.convex_dom hg.convex_dom).2 hdom
    funext y
    by_cases hy : y ∈ closure (dom f)
    · have hyg : y ∈ closure (dom g) := hcl ▸ hy
      have t1 := hf.tendsto_lscHull_along_segment_relint hx y
      have t2 := hg.tendsto_lscHull_along_segment_relint hx' y
      refine tendsto_nhds_unique t1 (t2.congr' ?_)
      filter_upwards [eventually_mem_Ico_nhdsLT_one] with a ha
      exact (heq (Convex.segment_mem_relint hf.convex_dom hx hy ha.1 ha.2)).symm
    · have hyg : y ∉ closure (dom g) := fun h => hy (hcl ▸ h)
      have h1 : lscHull f y = ⊤ :=
        top_le_iff.1 (not_lt.1 fun hmem => hy (dom_lscHull_subset_closure_dom f hmem))
      have h2 : lscHull g y = ⊤ :=
        top_le_iff.1 (not_lt.1 fun hmem => hyg (dom_lscHull_subset_closure_dom g hmem))
      rw [h1, h2]

/-- The `clFn` form of `lscHull_eq_of_eqOn_relint_dom`. -/
theorem clFn_eq_of_eqOn_relint_dom (hf : ConvexFn f) (hg : ConvexFn g)
    (hdom : ri (dom f) = ri (dom g)) (heq : Set.EqOn f g (ri (dom f))) :
    clFn f = clFn g := by
  unfold clFn
  rw [lscHull_eq_of_eqOn_relint_dom hf hg hdom heq]

/-- The concave counterpart of `clFn_eq_of_eqOn_relint_dom`: two concave functions that agree on
the relative interior of a common effective domain have the same concave closure. -/
theorem clConcave_eq_of_eqOn_relint_domConcave (hf : ConcaveFn f) (hg : ConcaveFn g)
    (hdom : ri (domConcave f) = ri (domConcave g)) (heq : Set.EqOn f g (ri (domConcave f))) :
    clConcave f = clConcave g := by
  have hdn : dom (fun z => -(f z)) = domConcave f := (domConcave_eq_dom_neg f).symm
  have hgn : dom (fun z => -(g z)) = domConcave g := (domConcave_eq_dom_neg g).symm
  have h : clFn (fun z => -(f z)) = clFn fun z => -(g z) := by
    refine clFn_eq_of_eqOn_relint_dom hf.convexFn_neg hg.convexFn_neg ?_ ?_
    · rw [hdn, hgn]; exact hdom
    · rw [hdn]; exact fun z hz => congrArg Neg.neg (heq hz)
  funext z
  rw [clConcave_apply, clConcave_apply, congrFun h z]

end ClosureAgreement

/-! ### Two `EReal` rearrangements -/

section ERealAux

variable {E : Type*}

/-- The concave effective domain of `-h` is the convex effective domain of `h`. -/
theorem domConcave_neg (h : E → EReal) : domConcave (fun z => -(h z)) = dom h := by
  ext z
  change ⊥ < -(h z) ↔ h z < ⊤
  rw [← _root_.EReal.neg_top, _root_.EReal.neg_lt_neg_iff]

end ERealAux

/-! ### Auxiliary facts about closures and relative interiors -/

section AuxTopological

variable {E : Type*} [TopologicalSpace E] {f g : E → EReal}

/-- A convex closure that reaches `-∞` anywhere is the constant `-∞`. -/
theorem clFn_eq_bot_of_eq_bot {x₀ : E} (h : f x₀ = ⊥) : clFn f = fun _ => (⊥ : EReal) := by
  refine clFn_of_exists_eq_bot ⟨x₀, le_bot_iff.1 ?_⟩
  calc lscHull f x₀ ≤ f x₀ := lscHull_le f x₀
    _ = ⊥ := h

/-- A concave closure that reaches `+∞` anywhere is the constant `+∞`. -/
theorem clConcave_eq_top_of_eq_top {x₀ : E} (h : g x₀ = ⊤) :
    clConcave g = fun _ => (⊤ : EReal) := by
  have h1 : clFn (fun z => -(g z)) = fun _ => (⊥ : EReal) :=
    clFn_eq_bot_of_eq_bot (x₀ := x₀) (by simp [h])
  funext x
  rw [clConcave_apply, congrFun h1 x, _root_.EReal.neg_bot]

end AuxTopological

section AuxRelint

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {g : E → EReal}

/-- A convex set squeezed between `C` and `cl C` has the same relative interior as `C`. -/
theorem Convex.relint_eq_of_subset_of_subset_closure {C S : Set E} (hC : Convex ℝ C)
    (hS : Convex ℝ S) (h₁ : C ⊆ S) (h₂ : S ⊆ closure C) : ri S = ri C :=
  (Convex.closure_eq_iff_relint_eq hS hC).1
    (Convex.closure_eq_of_relint_subset_of_subset_closure hC
      (intrinsicInterior_subset.trans h₁) h₂)

/-- The concave counterpart of `ConvexFn.clFn_eq_of_mem_relint_dom`: `cl g` agrees with `g` at
every relative interior point of `domConcave g`. -/
theorem ConcaveFn.clConcave_eq_of_mem_relint_domConcave (hg : ConcaveFn g) {x : E}
    (hx : x ∈ ri (domConcave g)) : clConcave g x = g x := by
  rw [domConcave_eq_dom_neg] at hx
  rw [clConcave_apply, hg.convexFn_neg.clFn_eq_of_mem_relint_dom hx]
  exact neg_neg _

/-- The concave counterpart of `ConvexFn.clFn_eq_of_notMem_closure_dom`: `cl g` agrees with `g`
off the closure of `domConcave g`, where both are `-∞`. -/
theorem ConcaveFn.clConcave_eq_of_notMem_closure_domConcave (hg : ConcaveFn g)
    (hp : ProperConcave g) {x : E} (hx : x ∉ closure (domConcave g)) : clConcave g x = g x := by
  rw [domConcave_eq_dom_neg] at hx
  rw [clConcave_apply,
    hg.convexFn_neg.clFn_eq_of_notMem_closure_dom (properConcave_iff_proper_neg.1 hp) hx]
  exact neg_neg _

end AuxRelint

/-! ### Swapping the two variables -/

section Swap

variable {U X : Type*}

@[simp] theorem dom₁_saddleSwap (K : U × X → EReal) : dom₁ (saddleSwap K) = dom₂ K := by
  ext x
  refine forall_congr' fun u => ?_
  change ⊥ < -(K (u, x)) ↔ K (u, x) < ⊤
  rw [← _root_.EReal.neg_top, _root_.EReal.neg_lt_neg_iff]

@[simp] theorem dom₂_saddleSwap (K : U × X → EReal) : dom₂ (saddleSwap K) = dom₁ K := by
  ext u
  refine forall_congr' fun x => ?_
  change -(K (u, x)) < ⊤ ↔ ⊥ < K (u, x)
  rw [← _root_.EReal.neg_bot, _root_.EReal.neg_lt_neg_iff]

end Swap

section SwapClosed

variable {U X : Type*} [TopologicalSpace U] [TopologicalSpace X] {K : U × X → EReal}

/-- Rockafellar's closedness for saddle-functions is invariant under the swap involution: its two
equations exchange places. -/
theorem closedSaddleFn_saddleSwap_iff : ClosedSaddleFn (saddleSwap K) ↔ ClosedSaddleFn K := by
  have e1 : partialCl₁ (partialCl₂ (saddleSwap K)) = saddleSwap (partialCl₂ (partialCl₁ K)) := by
    rw [partialCl₂_saddleSwap, partialCl₁_saddleSwap]
  have e2 : partialCl₂ (partialCl₁ (saddleSwap K)) = saddleSwap (partialCl₁ (partialCl₂ K)) := by
    rw [partialCl₁_saddleSwap, partialCl₂_saddleSwap]
  constructor
  · rintro ⟨ha, hb⟩
    rw [e1, partialCl₁_saddleSwap] at ha
    rw [e2, partialCl₂_saddleSwap] at hb
    exact ⟨saddleSwap_injective hb, saddleSwap_injective ha⟩
  · rintro ⟨ha, hb⟩
    exact ⟨by rw [e1, partialCl₁_saddleSwap, hb], by rw [e2, partialCl₂_saddleSwap, ha]⟩

end SwapClosed

/-! ### The effective domains of the partial closures -/

section DomainsAlgebraic

variable {U X : Type*} {K : U × X → EReal} {u : U}

/-- Every slice `K (u, ·)` has `dom₂ K` inside its effective domain. -/
theorem dom₂_subset_dom_slice (K : U × X → EReal) (u : U) : dom₂ K ⊆ dom fun x => K (u, x) :=
  fun _ hx => hx u

/-- Every slice `K (·, x)` has `dom₁ K` inside its concave effective domain. -/
theorem dom₁_subset_domConcave_slice (K : U × X → EReal) (x : X) :
    dom₁ K ⊆ domConcave fun u => K (u, x) :=
  fun _ hu => hu x

/-- On `dom₁ K` the slice `K (u, ·)` is a proper convex function, as soon as `dom₂ K` is
nonempty. -/
theorem proper_slice_of_mem_dom₁ (hne : (dom₂ K).Nonempty) (hu : u ∈ dom₁ K) :
    Proper fun x => K (u, x) := by
  obtain ⟨x₀, hx₀⟩ := hne
  exact ⟨⟨x₀, hx₀ u⟩, fun x => (hu x).ne'⟩

/-- On `dom₂ K` the slice `K (·, x)` is a proper concave function, as soon as `dom₁ K` is
nonempty. -/
theorem properConcave_slice_of_mem_dom₂ {x : X} (hne : (dom₁ K).Nonempty) (hx : x ∈ dom₂ K) :
    ProperConcave fun u => K (u, x) := by
  obtain ⟨u₀, hu₀⟩ := hne
  exact ⟨⟨u₀, hu₀ x⟩, fun u => (hx u).ne⟩

end DomainsAlgebraic

section DomainsCl₂

variable {U X : Type*} [NormedAddCommGroup X] {K : U × X → EReal} {u : U}

/-- Off `dom₁ K` the slice `K (u, ·)` takes the value `-∞` somewhere, so its convex closure is the
constant `-∞`. -/
theorem partialCl₂_slice_eq_bot_of_notMem_dom₁ (hu : u ∉ dom₁ K) :
    (fun x => partialCl₂ K (u, x)) = fun _ => (⊥ : EReal) := by
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : X, K (u, x₀) = ⊥ := by
    rw [mem_dom₁] at hu
    push Not at hu
    obtain ⟨x₀, hx₀⟩ := hu
    exact ⟨x₀, le_bot_iff.1 hx₀⟩
  have h1 : lscHull (fun x => K (u, x)) x₀ = ⊥ := by
    refine le_bot_iff.1 ?_
    calc lscHull (fun x => K (u, x)) x₀ ≤ K (u, x₀) := lscHull_le _ x₀
      _ = ⊥ := hx₀
  rw [partialCl₂_slice]
  exact clFn_of_exists_eq_bot ⟨x₀, h1⟩

/-- `cl₂` can only enlarge the second effective domain, since it lowers `K`. -/
theorem dom₂_subset_dom₂_partialCl₂ (K : U × X → EReal) : dom₂ K ⊆ dom₂ (partialCl₂ K) :=
  fun _ hx u => lt_of_le_of_lt (partialCl₂_le K (u, _)) (hx u)

end DomainsCl₂

section DomainsCl₂FD

variable {U X : Type*} [AddCommGroup U] [Module ℝ U] [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] {K : U × X → EReal} {u : U}

/-- On `dom₁ K` the slice `(cl₂ K) (u, ·)` is again proper: closing a proper convex function
leaves it proper, slice by slice. -/
theorem proper_partialCl₂_slice (hK : ConcaveConvexFn K) (hne : (dom₂ K).Nonempty)
    (hu : u ∈ dom₁ K) : Proper fun x => partialCl₂ K (u, x) := by
  rw [partialCl₂_slice]
  exact (hK.convex_snd u).proper_clFn (proper_slice_of_mem_dom₁ hne hu)

/-- `dom₁ K` is the effective domain of *every* concave slice `(cl₂ K) (·, x)`, not merely their
intersection. -/
theorem domConcave_partialCl₂_slice (hK : ConcaveConvexFn K) (hne : (dom₂ K).Nonempty) (x : X) :
    domConcave (fun u => partialCl₂ K (u, x)) = dom₁ K := by
  ext u
  refine ⟨fun h => ?_, fun h => ?_⟩
  · by_contra hu
    have h' : (⊥ : EReal) < partialCl₂ K (u, x) := h
    rw [congrFun (partialCl₂_slice_eq_bot_of_notMem_dom₁ hu) x] at h'
    exact absurd h' (lt_irrefl ⊥)
  · exact bot_lt_iff_ne_bot.2 ((proper_partialCl₂_slice hK hne h).ne_bot x)

/-- `cl₂` does not change the first effective domain. -/
theorem dom₁_partialCl₂ (hK : ConcaveConvexFn K) (hne : (dom₂ K).Nonempty) :
    dom₁ (partialCl₂ K) = dom₁ K := by
  ext u
  constructor
  · intro hu
    have h : u ∈ domConcave fun u => partialCl₂ K (u, 0) := hu 0
    rwa [domConcave_partialCl₂_slice hK hne (0 : X)] at h
  · intro hu x
    have h : u ∈ domConcave fun u => partialCl₂ K (u, x) := by
      rw [domConcave_partialCl₂_slice hK hne x]; exact hu
    exact h

/-- Closing a convex function cannot push its effective domain past the closure: that of
`(cl₂ K) (u, ·)` lies inside the closure of that of `K (u, ·)`. -/
theorem dom_partialCl₂_slice_subset_closure (hK : ConcaveConvexFn K) (hne : (dom₂ K).Nonempty)
    (hu : u ∈ dom₁ K) :
    dom (fun x => partialCl₂ K (u, x)) ⊆ closure (dom fun x => K (u, x)) := by
  rw [partialCl₂_slice, (hK.convex_snd u).clFn_eq_lscHull (proper_slice_of_mem_dom₁ hne hu)]
  exact dom_lscHull_subset_closure_dom _

end DomainsCl₂FD

section DomainsCl₁

variable {U X : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [AddCommGroup X] [Module ℝ X]
  {K : U × X → EReal} {x : X}

omit [NormedSpace ℝ U] [AddCommGroup X] [Module ℝ X] in
/-- Off `dom₂ K` the slice `K (·, x)` takes the value `+∞` somewhere, so its concave closure is
the constant `+∞`. The mirror of `partialCl₂_slice_eq_bot_of_notMem_dom₁`. -/
theorem partialCl₁_slice_eq_top_of_notMem_dom₂ (hx : x ∉ dom₂ K) :
    (fun u => partialCl₁ K (u, x)) = fun _ => (⊤ : EReal) := by
  have h := partialCl₂_slice_eq_bot_of_notMem_dom₁ (K := saddleSwap K) (u := x)
    (by rwa [dom₁_saddleSwap])
  funext u
  have h' : partialCl₂ (saddleSwap K) (x, u) = ⊥ := congrFun h u
  rw [congrFun (partialCl₂_saddleSwap K) (x, u)] at h'
  change -(partialCl₁ K (u, x)) = ⊥ at h'
  simpa using congrArg (fun z : EReal => -z) h'

omit [NormedSpace ℝ U] [AddCommGroup X] [Module ℝ X] in
/-- `cl₁` can only enlarge the first effective domain, since it raises `K`. -/
theorem dom₁_subset_dom₁_partialCl₁ (K : U × X → EReal) : dom₁ K ⊆ dom₁ (partialCl₁ K) :=
  fun _ hu x => lt_of_lt_of_le (hu x) (le_partialCl₁ K (_, x))

omit [NormedSpace ℝ U] [AddCommGroup X] [Module ℝ X] in
/-- The slice of `cl₂` of the swap, written back in terms of `cl₁`. This is the workhorse of the
transport: every `cl₁` statement below is a `cl₂` statement at `saddleSwap K`. -/
theorem partialCl₂_saddleSwap_slice (K : U × X → EReal) (x : X) :
    (fun u => partialCl₂ (saddleSwap K) (x, u)) = fun u => -(partialCl₁ K (u, x)) :=
  funext fun u => congrFun (partialCl₂_saddleSwap K) (x, u)

variable [FiniteDimensional ℝ U]

/-- The mirror of `proper_partialCl₂_slice`: on `dom₂ K` the slice `(cl₁ K) (·, x)` is again a
proper concave function. -/
theorem properConcave_partialCl₁_slice (hK : ConcaveConvexFn K) (hne : (dom₁ K).Nonempty)
    (hx : x ∈ dom₂ K) : ProperConcave fun u => partialCl₁ K (u, x) := by
  have h := proper_partialCl₂_slice (concaveConvexFn_saddleSwap hK)
    (by rwa [dom₂_saddleSwap]) (u := x) (by rwa [dom₁_saddleSwap])
  rw [partialCl₂_saddleSwap_slice] at h
  exact properConcave_iff_proper_neg.2 h

/-- The mirror of `domConcave_partialCl₂_slice`: `dom₂ K` is the effective domain of *every*
convex slice `(cl₁ K) (u, ·)`. -/
theorem dom_partialCl₁_slice (hK : ConcaveConvexFn K) (hne : (dom₁ K).Nonempty) (u : U) :
    dom (fun x => partialCl₁ K (u, x)) = dom₂ K := by
  have h := domConcave_partialCl₂_slice (concaveConvexFn_saddleSwap hK)
    (by rwa [dom₂_saddleSwap]) u
  rw [dom₁_saddleSwap] at h
  rw [← h]
  ext x
  change partialCl₁ K (u, x) < ⊤ ↔ ⊥ < partialCl₂ (saddleSwap K) (x, u)
  rw [congrFun (partialCl₂_saddleSwap K) (x, u)]
  change partialCl₁ K (u, x) < ⊤ ↔ ⊥ < -(partialCl₁ K (u, x))
  rw [← _root_.EReal.neg_top, _root_.EReal.neg_lt_neg_iff]

/-- `cl₁` does not change the second effective domain. -/
theorem dom₂_partialCl₁ (hK : ConcaveConvexFn K) (hne : (dom₁ K).Nonempty) :
    dom₂ (partialCl₁ K) = dom₂ K := by
  have h := dom₁_partialCl₂ (concaveConvexFn_saddleSwap hK) (by rwa [dom₂_saddleSwap])
  rw [partialCl₂_saddleSwap, dom₁_saddleSwap, dom₁_saddleSwap] at h
  exact h

/-- The mirror of `dom_partialCl₂_slice_subset_closure`. -/
theorem domConcave_partialCl₁_slice_subset_closure (hK : ConcaveConvexFn K)
    (hne : (dom₁ K).Nonempty) (hx : x ∈ dom₂ K) :
    domConcave (fun u => partialCl₁ K (u, x)) ⊆ closure (domConcave fun u => K (u, x)) := by
  have h := dom_partialCl₂_slice_subset_closure (concaveConvexFn_saddleSwap hK)
    (by rwa [dom₂_saddleSwap]) (u := x) (by rwa [dom₁_saddleSwap])
  have e1 : dom (fun u => partialCl₂ (saddleSwap K) (x, u))
      = domConcave fun u => partialCl₁ K (u, x) := by
    ext u
    change partialCl₂ (saddleSwap K) (x, u) < ⊤ ↔ ⊥ < partialCl₁ K (u, x)
    rw [congrFun (partialCl₂_saddleSwap K) (x, u)]
    change -(partialCl₁ K (u, x)) < ⊤ ↔ ⊥ < partialCl₁ K (u, x)
    rw [← _root_.EReal.neg_bot, _root_.EReal.neg_lt_neg_iff]
  have e2 : dom (fun u => saddleSwap K (x, u)) = domConcave fun u => K (u, x) :=
    (domConcave_eq_dom_neg _).symm
  rw [e1, e2] at h
  exact h

end DomainsCl₁

/-! ### Proper saddle-functions and their effective domain -/

section Proper

variable {U X : Type*} {K : U × X → EReal}

/-- The **effective domain** of a saddle-function: the product `dom₁ K × dom₂ K`, on which `K` is
finite. -/
def domSaddle (K : U × X → EReal) : Set (U × X) := dom₁ K ×ˢ dom₂ K

@[simp] theorem mem_domSaddle {p : U × X} : p ∈ domSaddle K ↔ p.1 ∈ dom₁ K ∧ p.2 ∈ dom₂ K :=
  Iff.rfl

/-- A saddle-function is **proper** when its effective domain is nonempty. -/
structure ProperSaddleFn (K : U × X → EReal) : Prop where
  /-- `K` is somewhere finite in the first variable. -/
  dom₁_nonempty : (dom₁ K).Nonempty
  /-- `K` is somewhere finite in the second variable. -/
  dom₂_nonempty : (dom₂ K).Nonempty

theorem ProperSaddleFn.domSaddle_nonempty (hp : ProperSaddleFn K) : (domSaddle K).Nonempty := by
  obtain ⟨u, hu⟩ := hp.dom₁_nonempty
  obtain ⟨x, hx⟩ := hp.dom₂_nonempty
  exact ⟨(u, x), hu, hx⟩

theorem properSaddleFn_iff_domSaddle_nonempty :
    ProperSaddleFn K ↔ (domSaddle K).Nonempty :=
  ⟨ProperSaddleFn.domSaddle_nonempty, fun ⟨p, hp⟩ => ⟨⟨p.1, hp.1⟩, ⟨p.2, hp.2⟩⟩⟩

theorem ProperSaddleFn.saddleSwap (hp : ProperSaddleFn K) :
    ProperSaddleFn (ConvexAnalysis.saddleSwap K) :=
  ⟨by rw [dom₁_saddleSwap]; exact hp.dom₂_nonempty,
    by rw [dom₂_saddleSwap]; exact hp.dom₁_nonempty⟩

/-- On its effective domain a saddle-function is finite. -/
theorem lt_top_of_mem_domSaddle {p : U × X} (hp : p ∈ domSaddle K) : K p < ⊤ := hp.2 p.1

theorem bot_lt_of_mem_domSaddle {p : U × X} (hp : p ∈ domSaddle K) : ⊥ < K p := hp.1 p.2

end Proper

section ProperRelint

variable {U X : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] {K : U × X → EReal}

omit [FiniteDimensional ℝ U] [FiniteDimensional ℝ X] in
/-- The relative interior of the effective domain of a saddle-function is the product of the two
relative interiors: `ri (dom K) = ri (dom₁ K) × ri (dom₂ K)`. -/
theorem relint_domSaddle (K : U × X → EReal) :
    ri (domSaddle K) = ri (dom₁ K) ×ˢ ri (dom₂ K) :=
  intrinsicInterior_prod_eq _ _

omit [FiniteDimensional ℝ X] in
/-- The first effective domain of a proper concave-convex `K` has nonempty relative interior. -/
theorem ProperSaddleFn.relint_dom₁_nonempty (hK : ConcaveConvexFn K) (hp : ProperSaddleFn K) :
    (ri (dom₁ K)).Nonempty :=
  Convex.relint_nonempty hK.convex_dom₁ hp.dom₁_nonempty

omit [FiniteDimensional ℝ U] in
theorem ProperSaddleFn.relint_dom₂_nonempty (hK : ConcaveConvexFn K) (hp : ProperSaddleFn K) :
    (ri (dom₂ K)).Nonempty :=
  Convex.relint_nonempty hK.convex_dom₂ hp.dom₂_nonempty

end ProperRelint

/-! ### The partial closures are again concave-convex, with no pairing to choose -/

section CorFiniteDim

variable {U X : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup X] [NormedSpace ℝ X] {K : U × X → EReal}

/-- The partial closure `cl₂ K` of a concave-convex function is again concave-convex: over a
normed space the continuous dual is a compatible partner, so no pairing has to be chosen. -/
theorem ConcaveConvexFn.partialCl₂ (hK : ConcaveConvexFn K) :
    ConcaveConvexFn (ConvexAnalysis.partialCl₂ K) :=
  concaveConvexFn_partialCl₂ (X := StrongDual ℝ X) (topDualPairing ℝ X) hK

/-- The mirror clause: `cl₁ K` of a concave-convex function is again concave-convex. -/
theorem ConcaveConvexFn.partialCl₁ (hK : ConcaveConvexFn K) :
    ConcaveConvexFn (ConvexAnalysis.partialCl₁ K) :=
  concaveConvexFn_partialCl₁ (V := StrongDual ℝ U) (topDualPairing ℝ U).flip hK

end CorFiniteDim

/-! ### Effective domains and the relative-interior clauses -/

section DomainsRelint

variable {U X : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] {K L : U × X → EReal}

/-- `cl₂` leaves the *second* effective domain of a closed proper saddle-function unchanged. (That
it leaves the first unchanged is `dom₁_partialCl₂` and needs no closedness.) -/
theorem ClosedSaddleFn.dom₂_partialCl₂ (hcl : ClosedSaddleFn K) (hK : ConcaveConvexFn K)
    (hp : ProperSaddleFn K) : dom₂ (partialCl₂ K) = dom₂ K := by
  have hne₁ : (dom₁ (partialCl₂ K)).Nonempty := by
    rw [dom₁_partialCl₂ hK hp.dom₂_nonempty]; exact hp.dom₁_nonempty
  have h1 : dom₂ (partialCl₁ (partialCl₂ K)) = dom₂ (partialCl₂ K) :=
    dom₂_partialCl₁ hK.partialCl₂ hne₁
  rw [hcl.1, dom₂_partialCl₁ hK hp.dom₁_nonempty] at h1
  exact h1.symm

/-- `cl₁` leaves the *first* effective domain of a closed proper saddle-function unchanged. -/
theorem ClosedSaddleFn.dom₁_partialCl₁ (hcl : ClosedSaddleFn K) (hK : ConcaveConvexFn K)
    (hp : ProperSaddleFn K) : dom₁ (partialCl₁ K) = dom₁ K := by
  have hne₂ : (dom₂ (partialCl₁ K)).Nonempty := by
    rw [dom₂_partialCl₁ hK hp.dom₁_nonempty]; exact hp.dom₂_nonempty
  have h1 : dom₁ (partialCl₂ (partialCl₁ K)) = dom₁ (partialCl₁ K) :=
    dom₁_partialCl₂ hK.partialCl₁ hne₂
  rw [hcl.2, dom₁_partialCl₂ hK hp.dom₂_nonempty] at h1
  exact h1.symm

omit [NormedSpace ℝ U] [FiniteDimensional ℝ U] [NormedSpace ℝ X] [FiniteDimensional ℝ X] in
/-- Where the two closures agree, `K` agrees with them: they sandwich it. -/
theorem eq_partialCl₂_of_partialCl₁_eq {p : U × X} (h : partialCl₁ K p = partialCl₂ K p) :
    K p = partialCl₂ K p := by
  refine le_antisymm ?_ (partialCl₂_le K p)
  rw [← h]
  exact le_partialCl₁ K p

/-- At a relative interior point of `dom₁ K` the two partial closures of a closed saddle-function
already agree.

Closedness gives `cl₁ K = cl₁ (cl₂ K)`, which closes the *concave* function `(cl₂ K) (·, x)`,
whose effective domain is exactly `dom₁ K`, and a concave function agrees with its closure on the
relative interior of that domain. -/
theorem ClosedSaddleFn.partialCl₁_eq_partialCl₂_of_mem_relint_dom₁ (hcl : ClosedSaddleFn K)
    (hK : ConcaveConvexFn K) (hp : ProperSaddleFn K) {u : U} (hu : u ∈ ri (dom₁ K)) (x : X) :
    partialCl₁ K (u, x) = partialCl₂ K (u, x) := by
  have hslice : ConcaveFn fun u => partialCl₂ K (u, x) := hK.partialCl₂.concave_fst x
  have hdom : domConcave (fun u => partialCl₂ K (u, x)) = dom₁ K :=
    domConcave_partialCl₂_slice hK hp.dom₂_nonempty x
  have h := hslice.clConcave_eq_of_mem_relint_domConcave (x := u) (by rw [hdom]; exact hu)
  calc partialCl₁ K (u, x) = partialCl₁ (partialCl₂ K) (u, x) := by rw [hcl.1]
    _ = clConcave (fun u => partialCl₂ K (u, x)) u := congrFun (partialCl₁_slice _ x) u
    _ = partialCl₂ K (u, x) := h

/-- The mirror clause on `U × ri (dom₂ K)`, obtained from the swap involution. -/
theorem ClosedSaddleFn.partialCl₁_eq_partialCl₂_of_mem_relint_dom₂ (hcl : ClosedSaddleFn K)
    (hK : ConcaveConvexFn K) (hp : ProperSaddleFn K) {x : X} (hx : x ∈ ri (dom₂ K)) (u : U) :
    partialCl₁ K (u, x) = partialCl₂ K (u, x) := by
  have h := (closedSaddleFn_saddleSwap_iff.2 hcl).partialCl₁_eq_partialCl₂_of_mem_relint_dom₁
    (concaveConvexFn_saddleSwap hK) hp.saddleSwap (by rwa [dom₁_saddleSwap]) u
  rw [congrFun (partialCl₁_saddleSwap K) (x, u), congrFun (partialCl₂_saddleSwap K) (x, u)] at h
  change -(partialCl₂ K (u, x)) = -(partialCl₁ K (u, x)) at h
  simpa using (congrArg (fun z : EReal => -z) h).symm

/-- A closed saddle-function coincides with `cl₂ K` — hence with every member of its equivalence
class — on `ri (dom₁ K) × X`. -/
theorem ClosedSaddleFn.eq_partialCl₂_of_mem_relint_dom₁ (hcl : ClosedSaddleFn K)
    (hK : ConcaveConvexFn K) (hp : ProperSaddleFn K) {u : U} (hu : u ∈ ri (dom₁ K)) (x : X) :
    K (u, x) = partialCl₂ K (u, x) :=
  eq_partialCl₂_of_partialCl₁_eq (hcl.partialCl₁_eq_partialCl₂_of_mem_relint_dom₁ hK hp hu x)

/-- The same on `U × ri (dom₂ K)`: there too a closed saddle-function coincides with `cl₂ K`. -/
theorem ClosedSaddleFn.eq_partialCl₂_of_mem_relint_dom₂ (hcl : ClosedSaddleFn K)
    (hK : ConcaveConvexFn K) (hp : ProperSaddleFn K) {x : X} (hx : x ∈ ri (dom₂ K)) (u : U) :
    K (u, x) = partialCl₂ K (u, x) :=
  eq_partialCl₂_of_partialCl₁_eq (hcl.partialCl₁_eq_partialCl₂_of_mem_relint_dom₂ hK hp hx u)

/-! #### Equivalent saddle-functions: shared domains, agreement on relative interiors -/

omit [FiniteDimensional ℝ U] in
/-- Equivalent saddle-functions have the same first effective domain. No closedness is needed:
`dom₁ K` is already `dom₁ (cl₂ K)`. -/
theorem SaddleEquiv.dom₁_eq (h : SaddleEquiv K L) (hK : ConcaveConvexFn K)
    (hpK : ProperSaddleFn K) (hL : ConcaveConvexFn L) (hpL : ProperSaddleFn L) :
    dom₁ K = dom₁ L := by
  rw [← dom₁_partialCl₂ hK hpK.dom₂_nonempty, ← dom₁_partialCl₂ hL hpL.dom₂_nonempty, h.2]

omit [FiniteDimensional ℝ X] in
/-- Equivalent saddle-functions have the same second effective domain. -/
theorem SaddleEquiv.dom₂_eq (h : SaddleEquiv K L) (hK : ConcaveConvexFn K)
    (hpK : ProperSaddleFn K) (hL : ConcaveConvexFn L) (hpL : ProperSaddleFn L) :
    dom₂ K = dom₂ L := by
  rw [← dom₂_partialCl₁ hK hpK.dom₁_nonempty, ← dom₂_partialCl₁ hL hpL.dom₁_nonempty, h.1]

/-- Equivalent saddle-functions have the same effective domain. -/
theorem SaddleEquiv.domSaddle_eq (h : SaddleEquiv K L) (hK : ConcaveConvexFn K)
    (hpK : ProperSaddleFn K) (hL : ConcaveConvexFn L) (hpL : ProperSaddleFn L) :
    domSaddle K = domSaddle L := by
  rw [domSaddle, domSaddle, h.dom₁_eq hK hpK hL hpL, h.dom₂_eq hK hpK hL hpL]

/-- Equivalent *closed* saddle-functions agree wherever the first coordinate is a relative interior
point of `dom₁ K`. -/
theorem SaddleEquiv.eq_of_mem_relint_dom₁ (h : SaddleEquiv K L) (hclK : ClosedSaddleFn K)
    (hK : ConcaveConvexFn K) (hpK : ProperSaddleFn K) (hclL : ClosedSaddleFn L)
    (hL : ConcaveConvexFn L) (hpL : ProperSaddleFn L) {u : U} (hu : u ∈ ri (dom₁ K)) (x : X) :
    K (u, x) = L (u, x) := by
  have hu' : u ∈ ri (dom₁ L) := by rwa [← h.dom₁_eq hK hpK hL hpL]
  rw [hclK.eq_partialCl₂_of_mem_relint_dom₁ hK hpK hu x,
    hclL.eq_partialCl₂_of_mem_relint_dom₁ hL hpL hu' x, h.2]

/-- The mirror half: equivalent *closed* saddle-functions agree over `ri (dom₂ K)`. -/
theorem SaddleEquiv.eq_of_mem_relint_dom₂ (h : SaddleEquiv K L) (hclK : ClosedSaddleFn K)
    (hK : ConcaveConvexFn K) (hpK : ProperSaddleFn K) (hclL : ClosedSaddleFn L)
    (hL : ConcaveConvexFn L) (hpL : ProperSaddleFn L) {x : X} (hx : x ∈ ri (dom₂ K)) (u : U) :
    K (u, x) = L (u, x) := by
  have hx' : x ∈ ri (dom₂ L) := by rwa [← h.dom₂_eq hK hpK hL hpL]
  rw [hclK.eq_partialCl₂_of_mem_relint_dom₂ hK hpK hx u,
    hclL.eq_partialCl₂_of_mem_relint_dom₂ hL hpL hx' u, h.2]

end DomainsRelint

/-! ### Lower and upper closed representatives -/

section ClosedRepresentatives

variable {U X : Type*} [TopologicalSpace U] [AddCommGroup U] [IsTopologicalAddGroup U]
  [TopologicalSpace X] [AddCommGroup X] [IsTopologicalAddGroup X] {K L : U × X → EReal}

omit [AddCommGroup U] [IsTopologicalAddGroup U] in
/-- A lower closed saddle-function is closed. -/
theorem LowerClosedFn.closedSaddleFn (h : LowerClosedFn K) : ClosedSaddleFn K := by
  have h' : partialCl₂ (partialCl₁ K) = K := h
  have hc : partialCl₂ K = K := h.convexClosedFn
  exact ⟨by rw [hc], by rw [h', hc]⟩

omit [AddCommGroup X] [IsTopologicalAddGroup X] in
/-- An upper closed saddle-function is closed. -/
theorem UpperClosedFn.closedSaddleFn (h : UpperClosedFn K) : ClosedSaddleFn K := by
  have h' : partialCl₁ (partialCl₂ K) = K := h
  have hc : partialCl₁ K = K := h.concaveClosedFn
  exact ⟨by rw [h', hc], by rw [hc]⟩

omit [AddCommGroup U] [IsTopologicalAddGroup U] [AddCommGroup X] [IsTopologicalAddGroup X] in
/-- The least member `cl₂ K` of the class of a closed saddle-function is lower closed. -/
theorem ClosedSaddleFn.lowerClosedFn_partialCl₂ (hcl : ClosedSaddleFn K) :
    LowerClosedFn (partialCl₂ K) := by
  change partialCl₂ (partialCl₁ (partialCl₂ K)) = partialCl₂ K
  rw [hcl.1, hcl.2]

omit [AddCommGroup U] [IsTopologicalAddGroup U] [AddCommGroup X] [IsTopologicalAddGroup X] in
/-- The greatest member `cl₁ K` of the class of a closed saddle-function is upper closed. -/
theorem ClosedSaddleFn.upperClosedFn_partialCl₁ (hcl : ClosedSaddleFn K) :
    UpperClosedFn (partialCl₁ K) := by
  change partialCl₁ (partialCl₂ (partialCl₁ K)) = partialCl₁ K
  rw [hcl.2, hcl.1]

omit [AddCommGroup U] [IsTopologicalAddGroup U] in
/-- The lower closed member of an equivalence class is unique. -/
theorem SaddleEquiv.eq_partialCl₂_of_lowerClosedFn (h : SaddleEquiv K L)
    (hL : LowerClosedFn L) : L = partialCl₂ K := by
  have hc : partialCl₂ L = L := hL.convexClosedFn
  rw [← hc, ← h.2]

omit [AddCommGroup X] [IsTopologicalAddGroup X] in
/-- The upper closed member of an equivalence class is unique. -/
theorem SaddleEquiv.eq_partialCl₁_of_upperClosedFn (h : SaddleEquiv K L)
    (hL : UpperClosedFn L) : L = partialCl₁ K := by
  have hc : partialCl₁ L = L := hL.concaveClosedFn
  rw [← hc, ← h.1]

end ClosedRepresentatives

/-! ### The improper closed saddle-functions -/

section Constants

variable {E : Type*} [NormedAddCommGroup E]

/-- The constant `+∞` is its own closure. -/
@[simp] theorem clFn_const_top : clFn (fun _ : E => (⊤ : EReal)) = fun _ => ⊤ := by
  have hl : lscHull (fun _ : E => (⊤ : EReal)) = fun _ => ⊤ :=
    lscHull_eq_self_iff.2 lowerSemicontinuous_const
  rw [clFn_of_forall_ne_bot (by simp [hl]), hl]

/-- The constant `-∞` is its own concave closure. -/
@[simp] theorem clConcave_const_bot : clConcave (fun _ : E => (⊥ : EReal)) = fun _ => ⊥ := by
  have hb : (fun _ : E => -((⊥ : EReal))) = fun _ : E => (⊤ : EReal) := by
    funext _; exact _root_.EReal.neg_bot
  have h : clFn (fun _ : E => -((⊥ : EReal))) = fun _ => (⊤ : EReal) := by
    rw [hb, clFn_const_top]
  funext x
  rw [clConcave_apply, congrFun h x, _root_.EReal.neg_top]

end Constants

section Improper

variable {U X : Type*} [NormedAddCommGroup U] [NormedAddCommGroup X] {K : U × X → EReal}

/-- A closed saddle-function with empty first effective domain is the constant `-∞`. -/
theorem ClosedSaddleFn.eq_const_bot_of_dom₁_eq_empty (hcl : ClosedSaddleFn K)
    (h : dom₁ K = ∅) : K = fun _ => (⊥ : EReal) := by
  have h2 : partialCl₂ K = fun _ => (⊥ : EReal) := by
    funext p
    have hu : p.1 ∉ dom₁ K := by rw [h]; exact Set.notMem_empty _
    exact congrFun (partialCl₂_slice_eq_bot_of_notMem_dom₁ hu) p.2
  have h1 : partialCl₁ K = fun _ => (⊥ : EReal) := by
    rw [← hcl.1, h2]
    funext p
    exact (congrFun (partialCl₁_slice (fun _ : U × X => (⊥ : EReal)) p.2) p.1).trans
      (congrFun clConcave_const_bot p.1)
  funext p
  refine le_antisymm ?_ bot_le
  rw [← congrFun h1 p]
  exact le_partialCl₁ K p

/-- A closed saddle-function with empty second effective domain is the constant `+∞`. -/
theorem ClosedSaddleFn.eq_const_top_of_dom₂_eq_empty (hcl : ClosedSaddleFn K)
    (h : dom₂ K = ∅) : K = fun _ => (⊤ : EReal) := by
  have hs := (closedSaddleFn_saddleSwap_iff.2 hcl).eq_const_bot_of_dom₁_eq_empty
    (by rwa [dom₁_saddleSwap])
  funext p
  have hp : saddleSwap K (p.2, p.1) = ⊥ := congrFun hs (p.2, p.1)
  change -(K (p.1, p.2)) = ⊥ at hp
  simpa using congrArg (fun z : EReal => -z) hp

/-- The only improper closed saddle-functions are the two constants. -/
theorem ClosedSaddleFn.eq_const_of_not_properSaddleFn (hcl : ClosedSaddleFn K)
    (hp : ¬ ProperSaddleFn K) : K = (fun _ => (⊥ : EReal)) ∨ K = fun _ => (⊤ : EReal) := by
  by_cases h1 : (dom₁ K).Nonempty
  · by_cases h2 : (dom₂ K).Nonempty
    · exact absurd ⟨h1, h2⟩ hp
    · exact Or.inr (hcl.eq_const_top_of_dom₂_eq_empty (Set.not_nonempty_iff_eq_empty.1 h2))
  · exact Or.inl (hcl.eq_const_bot_of_dom₁_eq_empty (Set.not_nonempty_iff_eq_empty.1 h1))

/-- The two improper closed saddle-functions are not equivalent. -/
theorem not_saddleEquiv_const_bot_const_top [Nonempty U] [Nonempty X] :
    ¬ SaddleEquiv (fun _ : U × X => (⊥ : EReal)) (fun _ : U × X => (⊤ : EReal)) := by
  intro h
  obtain ⟨u⟩ := ‹Nonempty U›
  obtain ⟨x⟩ := ‹Nonempty X›
  have hbot : partialCl₂ (fun _ : U × X => (⊥ : EReal)) (u, x) = ⊥ :=
    congrFun (clFn_eq_bot_of_eq_bot (f := fun _ : X => (⊥ : EReal)) (x₀ := x) rfl) x
  have htop : partialCl₂ (fun _ : U × X => (⊤ : EReal)) (u, x) = ⊤ :=
    congrFun (clFn_const_top (E := X)) x
  rw [h.2, htop] at hbot
  exact absurd hbot.symm (by simp)

end Improper

/-! ### The structure of a closed proper saddle-function -/

section Structure

variable {U X : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] {K : U × X → EReal}

/-- The **convex slice structure**: the description of the convex slices `K (u, ·)` of a closed
proper concave-convex function, according to whether `u` lies in `ri C`, in `C ∖ ri C`, or
outside `C = dom₁ K`.

Over `C` the lower bound `dom₂ K ⊆ dom (K (u, ·))` is unconditional (`dom₂_subset_dom_slice`) and
is therefore not a field, and improperness off `C` is recorded through the two `-∞` clauses rather
than as a separate assertion. -/
structure ConvexSliceStructure (K : U × X → EReal) : Prop where
  /-- Every slice over `dom₁ K` is a proper convex function. -/
  proper_slice : ∀ u ∈ dom₁ K, Proper fun x => K (u, x)
  /-- Over `ri (dom₁ K)` the slice is moreover closed … -/
  closedFn_slice : ∀ u ∈ ri (dom₁ K), ClosedFn fun x => K (u, x)
  /-- … with effective domain exactly `dom₂ K`. -/
  dom_slice : ∀ u ∈ ri (dom₁ K), dom (fun x => K (u, x)) = dom₂ K
  /-- Over `dom₁ K` the effective domain of the slice stays inside `cl (dom₂ K)`. -/
  dom_slice_subset_closure : ∀ u ∈ dom₁ K, dom (fun x => K (u, x)) ⊆ closure (dom₂ K)
  /-- Off `dom₁ K` the slice is `-∞` throughout `ri (dom₂ K)`. -/
  eq_bot_of_notMem_dom₁ : ∀ u ∉ dom₁ K, ∀ x ∈ ri (dom₂ K), K (u, x) = ⊥
  /-- Off `cl (dom₁ K)` the slice is `-∞` throughout `dom₂ K`. -/
  eq_bot_of_notMem_closure_dom₁ : ∀ u ∉ closure (dom₁ K), ∀ x ∈ dom₂ K, K (u, x) = ⊥

/-- The full structural description of a closed proper saddle-function: the convex slice structure
for `K`, together with the same for the swapped saddle-function. -/
def SaddleStructure (K : U × X → EReal) : Prop :=
  ConvexSliceStructure K ∧ ConvexSliceStructure (saddleSwap K)

omit [FiniteDimensional ℝ U] [FiniteDimensional ℝ X] in
theorem SaddleStructure.saddleSwap (hs : SaddleStructure K) :
    SaddleStructure (ConvexAnalysis.saddleSwap K) :=
  ⟨hs.2, by rw [saddleSwap_saddleSwap]; exact hs.1⟩

/-! #### The swapped clauses, read in concave language -/

omit [FiniteDimensional ℝ U] [FiniteDimensional ℝ X] in
/-- Every slice `K (·, x)` over `dom₂ K` is a proper concave function. -/
theorem SaddleStructure.properConcave_slice (hs : SaddleStructure K) {x : X} (hx : x ∈ dom₂ K) :
    ProperConcave fun u => K (u, x) :=
  properConcave_iff_proper_neg.2 (hs.2.proper_slice x (by rwa [dom₁_saddleSwap]))

omit [FiniteDimensional ℝ U] [FiniteDimensional ℝ X] in
/-- Over `ri (dom₂ K)` the slice `K (·, x)` is a closed concave function. -/
theorem SaddleStructure.closedConcaveFn_slice (hs : SaddleStructure K) {x : X}
    (hx : x ∈ ri (dom₂ K)) : ClosedConcaveFn fun u => K (u, x) :=
  closedConcaveFn_iff.2 (hs.2.closedFn_slice x (by rwa [dom₁_saddleSwap]))

omit [FiniteDimensional ℝ U] [FiniteDimensional ℝ X] in
/-- Over `ri (dom₂ K)` the slice `K (·, x)` has `dom₁ K` as its effective domain. -/
theorem SaddleStructure.domConcave_slice (hs : SaddleStructure K) {x : X}
    (hx : x ∈ ri (dom₂ K)) : domConcave (fun u => K (u, x)) = dom₁ K := by
  have h := hs.2.dom_slice x (by rwa [dom₁_saddleSwap])
  rw [dom₂_saddleSwap] at h
  rw [domConcave_eq_dom_neg]
  exact h

omit [FiniteDimensional ℝ U] [FiniteDimensional ℝ X] in
/-- Over `dom₂ K` the effective domain of `K (·, x)` stays inside `cl (dom₁ K)`. -/
theorem SaddleStructure.domConcave_slice_subset_closure (hs : SaddleStructure K) {x : X}
    (hx : x ∈ dom₂ K) : domConcave (fun u => K (u, x)) ⊆ closure (dom₁ K) := by
  have h := hs.2.dom_slice_subset_closure x (by rwa [dom₁_saddleSwap])
  rw [dom₂_saddleSwap] at h
  rw [domConcave_eq_dom_neg]
  exact h

omit [FiniteDimensional ℝ U] [FiniteDimensional ℝ X] in
/-- Off `dom₂ K` the slice `K (·, x)` is `+∞` throughout `ri (dom₁ K)`. -/
theorem SaddleStructure.eq_top_of_notMem_dom₂ (hs : SaddleStructure K) {x : X}
    (hx : x ∉ dom₂ K) {u : U} (hu : u ∈ ri (dom₁ K)) : K (u, x) = ⊤ := by
  have h := hs.2.eq_bot_of_notMem_dom₁ x (by rwa [dom₁_saddleSwap]) u
    (by rwa [dom₂_saddleSwap])
  change -(K (u, x)) = ⊥ at h
  simpa using congrArg (fun z : EReal => -z) h

omit [FiniteDimensional ℝ U] [FiniteDimensional ℝ X] in
/-- Off `cl (dom₂ K)` the slice `K (·, x)` is `+∞` throughout `dom₁ K`. -/
theorem SaddleStructure.eq_top_of_notMem_closure_dom₂ (hs : SaddleStructure K) {x : X}
    (hx : x ∉ closure (dom₂ K)) {u : U} (hu : u ∈ dom₁ K) : K (u, x) = ⊤ := by
  have h := hs.2.eq_bot_of_notMem_closure_dom₁ x (by rwa [dom₁_saddleSwap]) u
    (by rwa [dom₂_saddleSwap])
  change -(K (u, x)) = ⊥ at h
  simpa using congrArg (fun z : EReal => -z) h

/-! #### Necessity: a closed proper saddle-function is structured -/

/-- A closed proper concave-convex function has the convex slice structure. -/
theorem ClosedSaddleFn.convexSliceStructure (hcl : ClosedSaddleFn K) (hK : ConcaveConvexFn K)
    (hp : ProperSaddleFn K) : ConvexSliceStructure K := by
  refine ⟨fun u hu => proper_slice_of_mem_dom₁ hp.dom₂_nonempty hu, fun u hu => ?_,
    fun u hu => ?_, fun u hu => ?_, fun u hu x hx => ?_, fun u hu x hx => ?_⟩
  · funext x
    exact (hcl.eq_partialCl₂_of_mem_relint_dom₁ hK hp hu x).symm
  · have hfun : (fun x => K (u, x)) = fun x => partialCl₁ K (u, x) := by
      funext x
      exact (hcl.eq_partialCl₂_of_mem_relint_dom₁ hK hp hu x).trans
        (hcl.partialCl₁_eq_partialCl₂_of_mem_relint_dom₁ hK hp hu x).symm
    rw [hfun, dom_partialCl₁_slice hK hp.dom₁_nonempty u]
  · have hMne : (dom₂ (partialCl₁ K)).Nonempty := by
      rw [dom₂_partialCl₁ hK hp.dom₁_nonempty]; exact hp.dom₂_nonempty
    have h := dom_partialCl₂_slice_subset_closure hK.partialCl₁ hMne
      (dom₁_subset_dom₁_partialCl₁ K hu)
    rw [dom_partialCl₁_slice hK hp.dom₁_nonempty u, hcl.2] at h
    have hsub : dom (fun x => K (u, x)) ⊆ dom fun x => partialCl₂ K (u, x) :=
      fun x hx => lt_of_le_of_lt (partialCl₂_le K (u, x)) hx
    exact fun x hx => h (hsub hx)
  · rw [hcl.eq_partialCl₂_of_mem_relint_dom₂ hK hp hx u]
    exact congrFun (partialCl₂_slice_eq_bot_of_notMem_dom₁ hu) x
  · have hunotin : u ∉ dom₁ K := fun h => hu (subset_closure h)
    have hMconc : ConcaveFn fun u => partialCl₂ K (u, x) := hK.partialCl₂.concave_fst x
    have hMdom : domConcave (fun u => partialCl₂ K (u, x)) = dom₁ K :=
      domConcave_partialCl₂_slice hK hp.dom₂_nonempty x
    have hMbot : partialCl₂ K (u, x) = ⊥ :=
      congrFun (partialCl₂_slice_eq_bot_of_notMem_dom₁ hunotin) x
    have hMproper : ProperConcave fun u => partialCl₂ K (u, x) := by
      refine ⟨?_, fun u' => ?_⟩
      · rw [hMdom]; exact hp.dom₁_nonempty
      · exact (lt_of_le_of_lt (partialCl₂_le K (u', x)) (hx u')).ne
    have h := hMconc.clConcave_eq_of_notMem_closure_domConcave hMproper
      (x := u) (by rw [hMdom]; exact hu)
    have h2 : partialCl₁ K (u, x) = ⊥ := by
      rw [← hcl.1, congrFun (partialCl₁_slice (partialCl₂ K) x) u, h, hMbot]
    refine le_antisymm ?_ bot_le
    rw [← h2]
    exact le_partialCl₁ K (u, x)

/-- A closed proper concave-convex function has all six structural properties. -/
theorem ClosedSaddleFn.saddleStructure (hcl : ClosedSaddleFn K) (hK : ConcaveConvexFn K)
    (hp : ProperSaddleFn K) : SaddleStructure K :=
  ⟨hcl.convexSliceStructure hK hp,
    (closedSaddleFn_saddleSwap_iff.2 hcl).convexSliceStructure (concaveConvexFn_saddleSwap hK)
      hp.saddleSwap⟩

/-! #### Sufficiency: a structured saddle-function is closed -/

/-- The key step of the sufficiency half: for a structured `K`, the concave slices of `cl₂ K` and
of `K` have the same concave closure. -/
theorem SaddleStructure.clConcave_partialCl₂_slice (hs : SaddleStructure K)
    (hK : ConcaveConvexFn K) (hp : ProperSaddleFn K) (x : X) :
    clConcave (fun u => partialCl₂ K (u, x)) = clConcave fun u => K (u, x) := by
  have hagree : ∀ u ∈ ri (dom₁ K), partialCl₂ K (u, x) = K (u, x) := by
    intro u hu
    exact congrFun (hs.1.closedFn_slice u hu) x
  by_cases hx : x ∈ dom₂ K
  · have hf : ConcaveFn fun u => partialCl₂ K (u, x) := hK.partialCl₂.concave_fst x
    have hg : ConcaveFn fun u => K (u, x) := hK.concave_fst x
    have hfdom : domConcave (fun u => partialCl₂ K (u, x)) = dom₁ K :=
      domConcave_partialCl₂_slice hK hp.dom₂_nonempty x
    have hgdom : ri (domConcave fun u => K (u, x)) = ri (dom₁ K) :=
      Convex.relint_eq_of_subset_of_subset_closure hK.convex_dom₁ hg.convex_domConcave
        (dom₁_subset_domConcave_slice K x) (hs.domConcave_slice_subset_closure hx)
    refine clConcave_eq_of_eqOn_relint_domConcave hf hg (by rw [hfdom, hgdom]) ?_
    intro u hu
    rw [hfdom] at hu
    exact hagree u hu
  · obtain ⟨u₀, hu₀⟩ := hp.relint_dom₁_nonempty hK
    have htop : K (u₀, x) = ⊤ := hs.eq_top_of_notMem_dom₂ hx hu₀
    rw [clConcave_eq_top_of_eq_top (x₀ := u₀) (g := fun u => partialCl₂ K (u, x))
        ((hagree u₀ hu₀).trans htop),
      clConcave_eq_top_of_eq_top (x₀ := u₀) (g := fun u => K (u, x)) htop]

/-- A structured saddle-function satisfies the first closedness equation, `cl₁ (cl₂ K) = cl₁ K`. -/
theorem SaddleStructure.partialCl₁_partialCl₂ (hs : SaddleStructure K) (hK : ConcaveConvexFn K)
    (hp : ProperSaddleFn K) : partialCl₁ (partialCl₂ K) = partialCl₁ K := by
  funext p
  calc partialCl₁ (partialCl₂ K) p
      = clConcave (fun u => partialCl₂ K (u, p.2)) p.1 := rfl
    _ = clConcave (fun u => K (u, p.2)) p.1 := by
        rw [hs.clConcave_partialCl₂_slice hK hp p.2]
    _ = partialCl₁ K p := rfl

/-- The six structural properties make `K` closed. -/
theorem SaddleStructure.closedSaddleFn (hs : SaddleStructure K) (hK : ConcaveConvexFn K)
    (hp : ProperSaddleFn K) : ClosedSaddleFn K := by
  refine ⟨hs.partialCl₁_partialCl₂ hK hp, ?_⟩
  have h := hs.saddleSwap.partialCl₁_partialCl₂ (concaveConvexFn_saddleSwap hK) hp.saddleSwap
  rw [partialCl₂_saddleSwap, partialCl₁_saddleSwap, partialCl₁_saddleSwap] at h
  exact saddleSwap_injective h

/-- A proper concave-convex function is closed if and only if it has the six structural
properties. -/
theorem closedSaddleFn_iff_saddleStructure (hK : ConcaveConvexFn K) (hp : ProperSaddleFn K) :
    ClosedSaddleFn K ↔ SaddleStructure K :=
  ⟨fun hcl => hcl.saddleStructure hK hp, fun hs => hs.closedSaddleFn hK hp⟩

end Structure

/-! ### The kernel -/

section Kernel

variable {U X : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] {K L : U × X → EReal}

/-- The rectangle `ri (dom K) = ri (dom₁ K) × ri (dom₂ K)` on which the kernel lives. -/
def kernelSet (K : U × X → EReal) : Set (U × X) := ri (dom₁ K) ×ˢ ri (dom₂ K)

omit [FiniteDimensional ℝ U] [FiniteDimensional ℝ X] in
theorem kernelSet_eq_relint_domSaddle (K : U × X → EReal) :
    kernelSet K = ri (domSaddle K) := (relint_domSaddle K).symm

omit [FiniteDimensional ℝ U] [FiniteDimensional ℝ X] in
@[simp] theorem mem_kernelSet {p : U × X} :
    p ∈ kernelSet K ↔ p.1 ∈ ri (dom₁ K) ∧ p.2 ∈ ri (dom₂ K) := Iff.rfl

omit [FiniteDimensional ℝ U] [FiniteDimensional ℝ X] in
theorem kernelSet_subset_domSaddle (K : U × X → EReal) : kernelSet K ⊆ domSaddle K :=
  fun _ hp => ⟨intrinsicInterior_subset hp.1, intrinsicInterior_subset hp.2⟩

/-- The **kernel** of a saddle-function: the restriction of `K` to `ri (dom K)`, extended by `⊤`
off that rectangle.

Rockafellar's kernel is literally a partial function, which makes equations between the kernels of
two saddle-functions awkward to state. The extension loses nothing — `K` is finite on `ri (dom K)`,
so `kernel K` is `⊤` exactly off the rectangle — and `kernel K = kernel L` recovers both "the same
rectangle" and "the same values there" (`kernel_eq_iff`). -/
noncomputable def kernel (K : U × X → EReal) : U × X → EReal :=
  ConvexAnalysis.restrict (kernelSet K) K

omit [FiniteDimensional ℝ U] [FiniteDimensional ℝ X] in
@[simp] theorem kernel_of_mem {p : U × X} (hp : p ∈ kernelSet K) : kernel K p = K p :=
  restrict_of_mem hp

omit [FiniteDimensional ℝ U] [FiniteDimensional ℝ X] in
@[simp] theorem kernel_of_notMem {p : U × X} (hp : p ∉ kernelSet K) : kernel K p = ⊤ :=
  restrict_of_notMem hp

omit [FiniteDimensional ℝ U] [FiniteDimensional ℝ X] in
/-- A saddle-function is finite on its kernel rectangle, which is what makes `kernel K` detect
that rectangle. -/
theorem lt_top_of_mem_kernelSet {p : U × X} (hp : p ∈ kernelSet K) : K p < ⊤ :=
  lt_top_of_mem_domSaddle (kernelSet_subset_domSaddle K hp)

omit [FiniteDimensional ℝ U] [FiniteDimensional ℝ X] in
/-- Equality of kernels unpacks into equality of the two rectangles and agreement on them. -/
theorem kernel_eq_iff :
    kernel K = kernel L ↔ kernelSet K = kernelSet L ∧ Set.EqOn K L (kernelSet K) := by
  constructor
  · intro h
    have hset : kernelSet K = kernelSet L := by
      ext p
      constructor
      · intro hp
        by_contra hq
        have h1 : K p = ⊤ := by rw [← kernel_of_mem hp, h, kernel_of_notMem hq]
        exact absurd h1 (lt_top_of_mem_kernelSet hp).ne
      · intro hp
        by_contra hq
        have h1 : L p = ⊤ := by rw [← kernel_of_mem hp, ← h, kernel_of_notMem hq]
        exact absurd h1 (lt_top_of_mem_kernelSet hp).ne
    refine ⟨hset, fun p hp => ?_⟩
    rw [← kernel_of_mem hp, h, kernel_of_mem (hset ▸ hp)]
  · rintro ⟨hset, heq⟩
    funext p
    by_cases hp : p ∈ kernelSet K
    · rw [kernel_of_mem hp, kernel_of_mem (hset ▸ hp), heq hp]
    · rw [kernel_of_notMem hp, kernel_of_notMem (fun h => hp (hset ▸ h))]

/-- The two factors of the kernel rectangle are determined by it, since both are nonempty for a
proper concave-convex function. -/
theorem relint_dom₁_eq_of_kernelSet_eq (hK : ConcaveConvexFn K) (hpK : ProperSaddleFn K)
    (h : kernelSet K = kernelSet L) : ri (dom₁ K) = ri (dom₁ L) := by
  obtain ⟨u₀, hu₀⟩ := hpK.relint_dom₁_nonempty hK
  obtain ⟨x₀, hx₀⟩ := hpK.relint_dom₂_nonempty hK
  have hmem₀ : (u₀, x₀) ∈ kernelSet K := ⟨hu₀, hx₀⟩
  rw [h] at hmem₀
  ext u
  constructor
  · intro hu
    have hmem : (u, x₀) ∈ kernelSet K := ⟨hu, hx₀⟩
    rw [h] at hmem
    exact hmem.1
  · intro hu
    have hmem : (u, x₀) ∈ kernelSet L := ⟨hu, hmem₀.2⟩
    rw [← h] at hmem
    exact hmem.1

theorem relint_dom₂_eq_of_kernelSet_eq (hK : ConcaveConvexFn K) (hpK : ProperSaddleFn K)
    (h : kernelSet K = kernelSet L) : ri (dom₂ K) = ri (dom₂ L) := by
  obtain ⟨u₀, hu₀⟩ := hpK.relint_dom₁_nonempty hK
  obtain ⟨x₀, hx₀⟩ := hpK.relint_dom₂_nonempty hK
  have hmem₀ : (u₀, x₀) ∈ kernelSet K := ⟨hu₀, hx₀⟩
  rw [h] at hmem₀
  ext x
  constructor
  · intro hx
    have hmem : (u₀, x) ∈ kernelSet K := ⟨hu₀, hx⟩
    rw [h] at hmem
    exact hmem.2
  · intro hx
    have hmem : (u₀, x) ∈ kernelSet L := ⟨hmem₀.1, hx⟩
    rw [← h] at hmem
    exact hmem.2

omit [FiniteDimensional ℝ U] [FiniteDimensional ℝ X] in
/-- The kernel rectangle of the swapped saddle-function. -/
theorem kernelSet_saddleSwap (K : U × X → EReal) :
    kernelSet (saddleSwap K) = ri (dom₂ K) ×ˢ ri (dom₁ K) := by
  rw [kernelSet, dom₁_saddleSwap, dom₂_saddleSwap]

/-- Having the same kernel is invariant under the swap involution. -/
theorem kernel_saddleSwap_eq_of_kernel_eq (hK : ConcaveConvexFn K) (hpK : ProperSaddleFn K)
    (h : kernel K = kernel L) : kernel (saddleSwap K) = kernel (saddleSwap L) := by
  obtain ⟨hset, heq⟩ := kernel_eq_iff.1 h
  have h1 := relint_dom₁_eq_of_kernelSet_eq hK hpK hset
  have h2 := relint_dom₂_eq_of_kernelSet_eq hK hpK hset
  refine kernel_eq_iff.2 ⟨?_, fun q hq => ?_⟩
  · rw [kernelSet_saddleSwap, kernelSet_saddleSwap, h1, h2]
  · rw [kernelSet_saddleSwap] at hq
    have hmem : (q.2, q.1) ∈ kernelSet K := ⟨hq.2, hq.1⟩
    change -(K (q.2, q.1)) = -(L (q.2, q.1))
    rw [heq hmem]

end Kernel

/-! ### Equivalence is equality of kernels -/

section KernelEquiv

variable {U X : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] {K L : U × X → EReal}

/-- Equivalent closed proper saddle-functions have the same kernel: they share both effective
domains and agree over the relative interiors. -/
theorem SaddleEquiv.kernel_eq (h : SaddleEquiv K L) (hclK : ClosedSaddleFn K)
    (hK : ConcaveConvexFn K) (hpK : ProperSaddleFn K) (hclL : ClosedSaddleFn L)
    (hL : ConcaveConvexFn L) (hpL : ProperSaddleFn L) : kernel K = kernel L := by
  refine kernel_eq_iff.2 ⟨?_, fun p hp => ?_⟩
  · rw [kernelSet, kernelSet, h.dom₁_eq hK hpK hL hpL, h.dom₂_eq hK hpK hL hpL]
  · exact h.eq_of_mem_relint_dom₁ hclK hK hpK hclL hL hpL hp.1 p.2

/-- Over `ri (dom₁ K)` two closed proper saddle-functions with the same kernel have literally the
same convex slice. A closed convex function is determined by its values on the relative interior
of its effective domain. -/
theorem slice_eq_of_kernel_eq (hclK : ClosedSaddleFn K) (hK : ConcaveConvexFn K)
    (hpK : ProperSaddleFn K) (hclL : ClosedSaddleFn L) (hL : ConcaveConvexFn L)
    (hpL : ProperSaddleFn L) (h : kernel K = kernel L) {u : U} (hu : u ∈ ri (dom₁ K)) :
    (fun x => K (u, x)) = fun x => L (u, x) := by
  obtain ⟨hset, heq⟩ := kernel_eq_iff.1 h
  have h1 := relint_dom₁_eq_of_kernelSet_eq hK hpK hset
  have h2 := relint_dom₂_eq_of_kernelSet_eq hK hpK hset
  have hu' : u ∈ ri (dom₁ L) := h1 ▸ hu
  have hsK := hclK.saddleStructure hK hpK
  have hsL := hclL.saddleStructure hL hpL
  have hdK : dom (fun x => K (u, x)) = dom₂ K := hsK.1.dom_slice u hu
  have hdL : dom (fun x => L (u, x)) = dom₂ L := hsL.1.dom_slice u hu'
  have hcl : clFn (fun x => K (u, x)) = clFn fun x => L (u, x) := by
    refine clFn_eq_of_eqOn_relint_dom (hK.convex_snd u) (hL.convex_snd u) ?_ ?_
    · rw [hdK, hdL, h2]
    · intro x hx
      rw [hdK] at hx
      exact heq (⟨hu, hx⟩ : (u, x) ∈ kernelSet K)
  calc (fun x => K (u, x)) = clFn fun x => K (u, x) := (hsK.1.closedFn_slice u hu).symm
    _ = clFn fun x => L (u, x) := hcl
    _ = fun x => L (u, x) := hsL.1.closedFn_slice u hu'

/-- Two closed proper saddle-functions with the same kernel have the same second effective
domain. -/
theorem dom₂_eq_of_kernel_eq (hclK : ClosedSaddleFn K) (hK : ConcaveConvexFn K)
    (hpK : ProperSaddleFn K) (hclL : ClosedSaddleFn L) (hL : ConcaveConvexFn L)
    (hpL : ProperSaddleFn L) (h : kernel K = kernel L) : dom₂ K = dom₂ L := by
  obtain ⟨hset, -⟩ := kernel_eq_iff.1 h
  have h1 := relint_dom₁_eq_of_kernelSet_eq hK hpK hset
  obtain ⟨u₀, hu₀⟩ := hpK.relint_dom₁_nonempty hK
  have hsK := hclK.saddleStructure hK hpK
  have hsL := hclL.saddleStructure hL hpL
  rw [← hsK.1.dom_slice u₀ hu₀, ← hsL.1.dom_slice u₀ (h1 ▸ hu₀),
    slice_eq_of_kernel_eq hclK hK hpK hclL hL hpL h hu₀]

/-- Two closed proper saddle-functions with the same kernel have the same concave closure `cl₁`. -/
theorem partialCl₁_eq_of_kernel_eq (hclK : ClosedSaddleFn K) (hK : ConcaveConvexFn K)
    (hpK : ProperSaddleFn K) (hclL : ClosedSaddleFn L) (hL : ConcaveConvexFn L)
    (hpL : ProperSaddleFn L) (h : kernel K = kernel L) : partialCl₁ K = partialCl₁ L := by
  obtain ⟨hset, -⟩ := kernel_eq_iff.1 h
  have h1 := relint_dom₁_eq_of_kernelSet_eq hK hpK hset
  have hd₂ := dom₂_eq_of_kernel_eq hclK hK hpK hclL hL hpL h
  have hsK := hclK.saddleStructure hK hpK
  have hsL := hclL.saddleStructure hL hpL
  obtain ⟨u₀, hu₀⟩ := hpK.relint_dom₁_nonempty hK
  have hagree : ∀ ⦃u⦄, u ∈ ri (dom₁ K) → ∀ x, K (u, x) = L (u, x) := by
    intro u hu x
    exact congrFun (slice_eq_of_kernel_eq hclK hK hpK hclL hL hpL h hu) x
  funext p
  have key : clConcave (fun u => K (u, p.2)) = clConcave fun u => L (u, p.2) := by
    by_cases hx : p.2 ∈ dom₂ K
    · have hgK : ConcaveFn fun u => K (u, p.2) := hK.concave_fst p.2
      have hgL : ConcaveFn fun u => L (u, p.2) := hL.concave_fst p.2
      have hrK : ri (domConcave fun u => K (u, p.2)) = ri (dom₁ K) :=
        Convex.relint_eq_of_subset_of_subset_closure hK.convex_dom₁ hgK.convex_domConcave
          (dom₁_subset_domConcave_slice K p.2) (hsK.domConcave_slice_subset_closure hx)
      have hrL : ri (domConcave fun u => L (u, p.2)) = ri (dom₁ L) :=
        Convex.relint_eq_of_subset_of_subset_closure hL.convex_dom₁ hgL.convex_domConcave
          (dom₁_subset_domConcave_slice L p.2) (hsL.domConcave_slice_subset_closure (hd₂ ▸ hx))
      refine clConcave_eq_of_eqOn_relint_domConcave hgK hgL (by rw [hrK, hrL, h1]) ?_
      intro u hu
      rw [hrK] at hu
      exact hagree hu p.2
    · have htopK : K (u₀, p.2) = ⊤ := hsK.eq_top_of_notMem_dom₂ hx hu₀
      have htopL : L (u₀, p.2) = ⊤ := (hagree hu₀ p.2) ▸ htopK
      rw [clConcave_eq_top_of_eq_top (x₀ := u₀) (g := fun u => K (u, p.2)) htopK,
        clConcave_eq_top_of_eq_top (x₀ := u₀) (g := fun u => L (u, p.2)) htopL]
  exact congrFun key p.1

/-- Two closed proper concave-convex functions are equivalent if and only if they have the same
kernel. -/
theorem saddleEquiv_iff_kernel_eq (hclK : ClosedSaddleFn K) (hK : ConcaveConvexFn K)
    (hpK : ProperSaddleFn K) (hclL : ClosedSaddleFn L) (hL : ConcaveConvexFn L)
    (hpL : ProperSaddleFn L) : SaddleEquiv K L ↔ kernel K = kernel L := by
  refine ⟨fun h => h.kernel_eq hclK hK hpK hclL hL hpL, fun h => ⟨?_, ?_⟩⟩
  · exact partialCl₁_eq_of_kernel_eq hclK hK hpK hclL hL hpL h
  · have hswap := partialCl₁_eq_of_kernel_eq (closedSaddleFn_saddleSwap_iff.2 hclK)
      (concaveConvexFn_saddleSwap hK) hpK.saddleSwap (closedSaddleFn_saddleSwap_iff.2 hclL)
      (concaveConvexFn_saddleSwap hL) hpL.saddleSwap
      (kernel_saddleSwap_eq_of_kernel_eq hK hpK h)
    rw [partialCl₁_saddleSwap, partialCl₁_saddleSwap] at hswap
    exact saddleSwap_injective hswap

end KernelEquiv

/-! ### Idempotence of the lower and upper closures, without any duality -/

section Idempotence

variable {U X : Type*} [TopologicalSpace U] [AddCommGroup U] [IsTopologicalAddGroup U]
  [TopologicalSpace X] [AddCommGroup X] [IsTopologicalAddGroup X]

/-- The lower closure is lower closed: `lowerCl` is idempotent.

No duality is needed: `cl₁` and `cl₂` are a closure and a *co*-closure operator — monotone,
idempotent, one raising and one lowering — and with `M = cl₁ K`, `N = cl₂ M` the chain
`cl₂ (cl₁ N) ≤ cl₂ (cl₁ M) = cl₂ M = N = cl₂ N ≤ cl₂ (cl₁ N)` closes. -/
theorem lowerCl_idem (K : U × X → EReal) : lowerCl (lowerCl K) = lowerCl K := by
  have hAM : partialCl₁ (partialCl₁ K) = partialCl₁ K := concaveClosedFn_partialCl₁ K
  have hBN : partialCl₂ (partialCl₂ (partialCl₁ K)) = partialCl₂ (partialCl₁ K) :=
    convexClosedFn_partialCl₂ (partialCl₁ K)
  have hNM : partialCl₂ (partialCl₁ K) ≤ partialCl₁ K := partialCl₂_le _
  simp only [lowerCl_def]
  refine le_antisymm ?_ ?_
  · calc partialCl₂ (partialCl₁ (partialCl₂ (partialCl₁ K)))
        ≤ partialCl₂ (partialCl₁ (partialCl₁ K)) := partialCl₂_mono (partialCl₁_mono hNM)
      _ = partialCl₂ (partialCl₁ K) := by rw [hAM]
  · calc partialCl₂ (partialCl₁ K) = partialCl₂ (partialCl₂ (partialCl₁ K)) := hBN.symm
      _ ≤ partialCl₂ (partialCl₁ (partialCl₂ (partialCl₁ K))) :=
          partialCl₂_mono (le_partialCl₁ _)

/-- The upper closure is upper closed, by the swap involution. -/
theorem upperCl_idem (K : U × X → EReal) : upperCl (upperCl K) = upperCl K := by
  have h := lowerCl_idem (saddleSwap K)
  rw [lowerCl_saddleSwap, lowerCl_saddleSwap] at h
  exact saddleSwap_injective h

omit [AddCommGroup U] [IsTopologicalAddGroup U] in
/-- The lower closure is convex-closed: it *is* a `cl₂`. -/
theorem convexClosedFn_lowerCl (K : U × X → EReal) : ConvexClosedFn (lowerCl K) :=
  convexClosedFn_partialCl₂ (partialCl₁ K)

omit [AddCommGroup X] [IsTopologicalAddGroup X] in
/-- The upper closure is concave-closed: it *is* a `cl₁`. -/
theorem concaveClosedFn_upperCl (K : U × X → EReal) : ConcaveClosedFn (upperCl K) :=
  concaveClosedFn_partialCl₁ (partialCl₂ K)

/-- The lower closure of any saddle-function is a closed saddle-function. -/
theorem closedSaddleFn_lowerCl (K : U × X → EReal) : ClosedSaddleFn (lowerCl K) :=
  LowerClosedFn.closedSaddleFn (lowerCl_idem K)

/-- The upper closure of any saddle-function is a closed saddle-function. -/
theorem closedSaddleFn_upperCl (K : U × X → EReal) : ClosedSaddleFn (upperCl K) :=
  UpperClosedFn.closedSaddleFn (upperCl_idem K)

end Idempotence

/-! ### Simple saddle-functions -/

section Simple

variable {U X : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] {K : U × X → EReal}

/-- A concave-convex function is **simple** — Rockafellar's word — when over `ri (dom₁ K)` the
convex slices have their effective domains inside `cl (dom₂ K)`, and symmetrically. Every closed
proper saddle-function is simple, and so is every simple extension of a finite saddle-function on
a product of convex sets. -/
structure SimpleSaddleFn (K : U × X → EReal) : Prop where
  /-- Over `ri (dom₁ K)` the convex slice does not reach beyond `cl (dom₂ K)`. -/
  dom_slice_subset_closure : ∀ u ∈ ri (dom₁ K), dom (fun x => K (u, x)) ⊆ closure (dom₂ K)
  /-- Over `ri (dom₂ K)` the concave slice does not reach beyond `cl (dom₁ K)`. -/
  domConcave_slice_subset_closure :
    ∀ x ∈ ri (dom₂ K), domConcave (fun u => K (u, x)) ⊆ closure (dom₁ K)

omit [FiniteDimensional ℝ U] [FiniteDimensional ℝ X] in
/-- Simplicity is invariant under the swap involution: the two clauses trade places. -/
theorem simpleSaddleFn_saddleSwap_iff :
    SimpleSaddleFn (saddleSwap K) ↔ SimpleSaddleFn K := by
  constructor
  · intro h
    refine ⟨fun u hu => ?_, fun x hx => ?_⟩
    · have h2 := h.domConcave_slice_subset_closure u (by rwa [dom₂_saddleSwap])
      rw [dom₁_saddleSwap] at h2
      rw [← domConcave_neg fun x => K (u, x)]
      exact h2
    · have h1 := h.dom_slice_subset_closure x (by rwa [dom₁_saddleSwap])
      rw [dom₂_saddleSwap] at h1
      rw [domConcave_eq_dom_neg]
      exact h1
  · intro h
    refine ⟨fun x hx => ?_, fun u hu => ?_⟩
    · rw [dom₁_saddleSwap] at hx
      rw [dom₂_saddleSwap]
      have h1 := h.domConcave_slice_subset_closure x hx
      rw [domConcave_eq_dom_neg] at h1
      exact h1
    · rw [dom₂_saddleSwap] at hu
      rw [dom₁_saddleSwap]
      have h2 := h.dom_slice_subset_closure u hu
      rw [← domConcave_neg fun x => K (u, x)] at h2
      exact h2

omit [FiniteDimensional ℝ U] [FiniteDimensional ℝ X] in
/-- The two slice-domain clauses say precisely that a structured saddle-function is simple. -/
theorem SaddleStructure.simpleSaddleFn (hs : SaddleStructure K) : SimpleSaddleFn K :=
  ⟨fun u hu => hs.1.dom_slice_subset_closure u (intrinsicInterior_subset hu),
    fun _x hx => hs.domConcave_slice_subset_closure (intrinsicInterior_subset hx)⟩

/-- Every closed proper concave-convex function is simple. -/
theorem ClosedSaddleFn.simpleSaddleFn (hcl : ClosedSaddleFn K) (hK : ConcaveConvexFn K)
    (hp : ProperSaddleFn K) : SimpleSaddleFn K :=
  (hcl.saddleStructure hK hp).simpleSaddleFn

end Simple

/-! ### The partial closures preserve simplicity, properness and the kernel -/

section Preserve

variable {U X : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] {K : U × X → EReal}

omit [FiniteDimensional ℝ U] in
/-- For a simple `K`, a convex slice taken over `ri (dom₁ K)` has effective domain with the same
relative interior as `dom₂ K`. -/
theorem relint_dom_slice (hK : ConcaveConvexFn K) (hs : SimpleSaddleFn K) {u : U}
    (hu : u ∈ ri (dom₁ K)) : ri (dom fun x => K (u, x)) = ri (dom₂ K) :=
  Convex.relint_eq_of_subset_of_subset_closure hK.convex_dom₂ (hK.convex_snd u).convex_dom
    (dom₂_subset_dom_slice K u) (hs.dom_slice_subset_closure u hu)

omit [FiniteDimensional ℝ U] in
/-- `cl₂` does not move a simple `K` on the kernel rectangle. -/
theorem partialCl₂_eq_of_mem_kernelSet (hK : ConcaveConvexFn K) (hs : SimpleSaddleFn K)
    {p : U × X} (hmem : p ∈ kernelSet K) : partialCl₂ K p = K p :=
  (hK.convex_snd p.1).clFn_eq_of_mem_relint_dom (x := p.2)
    (by rw [relint_dom_slice hK hs hmem.1]; exact hmem.2)

/-- `cl₂` cannot enlarge `dom₂ K` beyond its closure. -/
theorem dom₂_partialCl₂_subset_closure (hK : ConcaveConvexFn K) (hp : ProperSaddleFn K)
    (hs : SimpleSaddleFn K) : dom₂ (partialCl₂ K) ⊆ closure (dom₂ K) := by
  obtain ⟨u₀, hu₀⟩ := hp.relint_dom₁_nonempty hK
  intro x hx
  have h2 := dom_partialCl₂_slice_subset_closure hK hp.dom₂_nonempty
    (intrinsicInterior_subset hu₀) (hx u₀)
  have h3 : closure (dom fun x => K (u₀, x)) ⊆ closure (dom₂ K) := by
    rw [← closure_closure (s := dom₂ K)]
    exact closure_mono (hs.dom_slice_subset_closure u₀ hu₀)
  exact h3 h2

/-- `cl₂` leaves the relative interior of `dom₂` alone when `K` is simple. -/
theorem relint_dom₂_partialCl₂ (hK : ConcaveConvexFn K) (hp : ProperSaddleFn K)
    (hs : SimpleSaddleFn K) : ri (dom₂ (partialCl₂ K)) = ri (dom₂ K) :=
  Convex.relint_eq_of_subset_of_subset_closure hK.convex_dom₂ hK.partialCl₂.convex_dom₂
    (dom₂_subset_dom₂_partialCl₂ K) (dom₂_partialCl₂_subset_closure hK hp hs)

/-- `cl₂` leaves the closure of `dom₂` alone when `K` is simple. -/
theorem closure_dom₂_partialCl₂ (hK : ConcaveConvexFn K) (hp : ProperSaddleFn K)
    (hs : SimpleSaddleFn K) : closure (dom₂ (partialCl₂ K)) = closure (dom₂ K) :=
  (Convex.closure_eq_iff_relint_eq hK.partialCl₂.convex_dom₂ hK.convex_dom₂).2
    (relint_dom₂_partialCl₂ hK hp hs)

omit [FiniteDimensional ℝ U] in
/-- `cl₂` preserves properness. -/
theorem ProperSaddleFn.partialCl₂ (hK : ConcaveConvexFn K) (hp : ProperSaddleFn K) :
    ProperSaddleFn (ConvexAnalysis.partialCl₂ K) :=
  ⟨by rw [dom₁_partialCl₂ hK hp.dom₂_nonempty]; exact hp.dom₁_nonempty,
    hp.dom₂_nonempty.mono (dom₂_subset_dom₂_partialCl₂ K)⟩

/-- `cl₂` preserves simplicity. -/
theorem SimpleSaddleFn.partialCl₂ (hK : ConcaveConvexFn K) (hp : ProperSaddleFn K)
    (hs : SimpleSaddleFn K) : SimpleSaddleFn (ConvexAnalysis.partialCl₂ K) := by
  constructor
  · intro u hu
    rw [dom₁_partialCl₂ hK hp.dom₂_nonempty] at hu
    rw [closure_dom₂_partialCl₂ hK hp hs]
    intro x hx
    have h2 := dom_partialCl₂_slice_subset_closure hK hp.dom₂_nonempty
      (intrinsicInterior_subset hu) hx
    have h3 : closure (dom fun x => K (u, x)) ⊆ closure (dom₂ K) := by
      rw [← closure_closure (s := dom₂ K)]
      exact closure_mono (hs.dom_slice_subset_closure u hu)
    exact h3 h2
  · intro x _
    rw [domConcave_partialCl₂_slice hK hp.dom₂_nonempty x, dom₁_partialCl₂ hK hp.dom₂_nonempty]
    exact subset_closure

/-- `cl₂` preserves the kernel. -/
theorem kernel_partialCl₂ (hK : ConcaveConvexFn K) (hp : ProperSaddleFn K)
    (hs : SimpleSaddleFn K) : kernel (ConvexAnalysis.partialCl₂ K) = kernel K := by
  have hset : kernelSet (ConvexAnalysis.partialCl₂ K) = kernelSet K := by
    rw [kernelSet, kernelSet, dom₁_partialCl₂ hK hp.dom₂_nonempty,
      relint_dom₂_partialCl₂ hK hp hs]
  refine kernel_eq_iff.2 ⟨hset, fun p hp' => ?_⟩
  rw [hset] at hp'
  exact partialCl₂_eq_of_mem_kernelSet hK hs hp'

omit [FiniteDimensional ℝ X] in
/-- `cl₁` preserves properness. -/
theorem ProperSaddleFn.partialCl₁ (hK : ConcaveConvexFn K) (hp : ProperSaddleFn K) :
    ProperSaddleFn (ConvexAnalysis.partialCl₁ K) := by
  have h := ProperSaddleFn.partialCl₂ (concaveConvexFn_saddleSwap hK) hp.saddleSwap
  rw [partialCl₂_saddleSwap] at h
  exact ⟨by simpa using h.dom₂_nonempty, by simpa using h.dom₁_nonempty⟩

/-- The mirror: `cl₁` preserves simplicity. -/
theorem SimpleSaddleFn.partialCl₁ (hK : ConcaveConvexFn K) (hp : ProperSaddleFn K)
    (hs : SimpleSaddleFn K) : SimpleSaddleFn (ConvexAnalysis.partialCl₁ K) := by
  have h := SimpleSaddleFn.partialCl₂ (concaveConvexFn_saddleSwap hK) hp.saddleSwap
    (simpleSaddleFn_saddleSwap_iff.2 hs)
  rw [partialCl₂_saddleSwap] at h
  exact simpleSaddleFn_saddleSwap_iff.1 h

/-- The mirror: `cl₁` preserves the kernel. -/
theorem kernel_partialCl₁ (hK : ConcaveConvexFn K) (hp : ProperSaddleFn K)
    (hs : SimpleSaddleFn K) : kernel (ConvexAnalysis.partialCl₁ K) = kernel K := by
  have h := kernel_partialCl₂ (concaveConvexFn_saddleSwap hK) hp.saddleSwap
    (simpleSaddleFn_saddleSwap_iff.2 hs)
  rw [partialCl₂_saddleSwap] at h
  have h2 := kernel_saddleSwap_eq_of_kernel_eq
    (concaveConvexFn_saddleSwap (ConcaveConvexFn.partialCl₁ hK))
    (ProperSaddleFn.partialCl₁ hK hp).saddleSwap h
  rwa [saddleSwap_saddleSwap, saddleSwap_saddleSwap] at h2

end Preserve

/-! ### The equivalence class attached to a simple saddle-function -/

section DomainMono

variable {U X : Type*} {K L : U × X → EReal}

/-- The first effective domain is monotone in the saddle-function. -/
theorem dom₁_mono (h : K ≤ L) : dom₁ K ⊆ dom₁ L := fun _ hu x => lt_of_lt_of_le (hu x) (h (_, x))

/-- The second effective domain is antitone in the saddle-function. -/
theorem dom₂_anti (h : K ≤ L) : dom₂ L ⊆ dom₂ K := fun _ hx u => lt_of_le_of_lt (h (u, _)) (hx u)

end DomainMono

section SaddleClass

variable {U X : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] {K L : U × X → EReal}

omit [FiniteDimensional ℝ U] [FiniteDimensional ℝ X] in
/-- The lower closure of a simple proper concave-convex function is concave-convex. -/
theorem ConcaveConvexFn.lowerCl (hK : ConcaveConvexFn K) :
    ConcaveConvexFn (ConvexAnalysis.lowerCl K) :=
  ConcaveConvexFn.partialCl₂ (ConcaveConvexFn.partialCl₁ hK)

omit [FiniteDimensional ℝ U] [FiniteDimensional ℝ X] in
/-- The upper closure of a concave-convex function is concave-convex. -/
theorem ConcaveConvexFn.upperCl (hK : ConcaveConvexFn K) :
    ConcaveConvexFn (ConvexAnalysis.upperCl K) :=
  ConcaveConvexFn.partialCl₁ (ConcaveConvexFn.partialCl₂ hK)

/-- The lower closure of a simple proper saddle-function is proper. -/
theorem ProperSaddleFn.lowerCl (hK : ConcaveConvexFn K) (hp : ProperSaddleFn K) :
    ProperSaddleFn (ConvexAnalysis.lowerCl K) :=
  ProperSaddleFn.partialCl₂ (ConcaveConvexFn.partialCl₁ hK) (ProperSaddleFn.partialCl₁ hK hp)

/-- The upper closure of a simple proper saddle-function is proper. -/
theorem ProperSaddleFn.upperCl (hK : ConcaveConvexFn K) (hp : ProperSaddleFn K) :
    ProperSaddleFn (ConvexAnalysis.upperCl K) :=
  ProperSaddleFn.partialCl₁ (ConcaveConvexFn.partialCl₂ hK) (ProperSaddleFn.partialCl₂ hK hp)

/-- The lower closure of a simple saddle-function is simple. -/
theorem SimpleSaddleFn.lowerCl (hK : ConcaveConvexFn K) (hp : ProperSaddleFn K)
    (hs : SimpleSaddleFn K) : SimpleSaddleFn (ConvexAnalysis.lowerCl K) :=
  SimpleSaddleFn.partialCl₂ (ConcaveConvexFn.partialCl₁ hK) (ProperSaddleFn.partialCl₁ hK hp)
    (SimpleSaddleFn.partialCl₁ hK hp hs)

/-- The upper closure of a simple saddle-function is simple. -/
theorem SimpleSaddleFn.upperCl (hK : ConcaveConvexFn K) (hp : ProperSaddleFn K)
    (hs : SimpleSaddleFn K) : SimpleSaddleFn (ConvexAnalysis.upperCl K) :=
  SimpleSaddleFn.partialCl₁ (ConcaveConvexFn.partialCl₂ hK) (ProperSaddleFn.partialCl₂ hK hp)
    (SimpleSaddleFn.partialCl₂ hK hp hs)

/-- The lower closure of a simple saddle-function has the same kernel. -/
theorem kernel_lowerCl (hK : ConcaveConvexFn K) (hp : ProperSaddleFn K) (hs : SimpleSaddleFn K) :
    kernel (ConvexAnalysis.lowerCl K) = kernel K :=
  (kernel_partialCl₂ (ConcaveConvexFn.partialCl₁ hK) (ProperSaddleFn.partialCl₁ hK hp)
    (SimpleSaddleFn.partialCl₁ hK hp hs)).trans (kernel_partialCl₁ hK hp hs)

/-- The upper closure of a simple saddle-function has the same kernel. -/
theorem kernel_upperCl (hK : ConcaveConvexFn K) (hp : ProperSaddleFn K) (hs : SimpleSaddleFn K) :
    kernel (ConvexAnalysis.upperCl K) = kernel K :=
  (kernel_partialCl₁ (ConcaveConvexFn.partialCl₂ hK) (ProperSaddleFn.partialCl₂ hK hp)
    (SimpleSaddleFn.partialCl₂ hK hp hs)).trans (kernel_partialCl₂ hK hp hs)

/-- For a simple proper concave-convex `K`, the lower closure `cl₂ cl₁ K` and the upper closure
`cl₁ cl₂ K` are equivalent. Both are closed, and both have the same kernel as `K`, which for
closed proper saddle-functions already forces equivalence. -/
theorem saddleEquiv_lowerCl_upperCl (hK : ConcaveConvexFn K) (hp : ProperSaddleFn K)
    (hs : SimpleSaddleFn K) : SaddleEquiv (lowerCl K) (upperCl K) :=
  (saddleEquiv_iff_kernel_eq (closedSaddleFn_lowerCl K) hK.lowerCl (ProperSaddleFn.lowerCl hK hp)
    (closedSaddleFn_upperCl K) hK.upperCl (ProperSaddleFn.upperCl hK hp)).2
    ((kernel_lowerCl hK hp hs).trans (kernel_upperCl hK hp hs).symm)

/-- `cl₁` carries the lower closure to the upper one: the two are a closure pair. -/
theorem partialCl₁_lowerCl (hK : ConcaveConvexFn K) (hp : ProperSaddleFn K)
    (hs : SimpleSaddleFn K) : partialCl₁ (lowerCl K) = upperCl K :=
  ((saddleEquiv_lowerCl_upperCl hK hp hs).1).trans (concaveClosedFn_upperCl K)

/-- `cl₂` carries the upper closure back to the lower one. -/
theorem partialCl₂_upperCl (hK : ConcaveConvexFn K) (hp : ProperSaddleFn K)
    (hs : SimpleSaddleFn K) : partialCl₂ (upperCl K) = lowerCl K :=
  ((saddleEquiv_lowerCl_upperCl hK hp hs).2).symm.trans (convexClosedFn_lowerCl K)

/-- The lower closure lies below the upper one: `cl₂ cl₁ K ≤ cl₁ cl₂ K`. -/
theorem lowerCl_le_upperCl (hK : ConcaveConvexFn K) (hp : ProperSaddleFn K)
    (hs : SimpleSaddleFn K) : lowerCl K ≤ upperCl K :=
  le_of_partialCl₂_eq (partialCl₂_upperCl hK hp hs)

/-- Every saddle-function between the two closures is closed. -/
theorem closedSaddleFn_of_mem_saddleClass_lowerCl (hK : ConcaveConvexFn K) (hp : ProperSaddleFn K)
    (hs : SimpleSaddleFn K) (hL : L ∈ saddleClass (lowerCl K) (upperCl K)) : ClosedSaddleFn L :=
  closedSaddleFn_of_mem_saddleClass (partialCl₁_lowerCl hK hp hs) (partialCl₂_upperCl hK hp hs) hL

/-- Every saddle-function between the two closures is proper. -/
theorem properSaddleFn_of_mem_saddleClass_lowerCl (hK : ConcaveConvexFn K) (hp : ProperSaddleFn K)
    (hL : L ∈ saddleClass (lowerCl K) (upperCl K)) : ProperSaddleFn L :=
  ⟨(ProperSaddleFn.lowerCl hK hp).dom₁_nonempty.mono (dom₁_mono hL.1),
    (ProperSaddleFn.upperCl hK hp).dom₂_nonempty.mono (dom₂_anti hL.2)⟩

/-- Every saddle-function between the two closures is equivalent to them. -/
theorem saddleEquiv_of_mem_saddleClass_lowerCl (hK : ConcaveConvexFn K) (hp : ProperSaddleFn K)
    (hs : SimpleSaddleFn K) (hL : L ∈ saddleClass (lowerCl K) (upperCl K)) :
    SaddleEquiv (lowerCl K) L :=
  saddleEquiv_of_mem_saddleClass (partialCl₁_lowerCl hK hp hs) (partialCl₂_upperCl hK hp hs)
    (mem_saddleClass_left (partialCl₂_upperCl hK hp hs)) hL

/-- Every concave-convex saddle-function between the two closures has the same kernel as `K`. -/
theorem kernel_of_mem_saddleClass_lowerCl (hK : ConcaveConvexFn K) (hp : ProperSaddleFn K)
    (hs : SimpleSaddleFn K) (hCC : ConcaveConvexFn L)
    (hL : L ∈ saddleClass (lowerCl K) (upperCl K)) : kernel L = kernel K := by
  have hequiv := saddleEquiv_of_mem_saddleClass_lowerCl hK hp hs hL
  have h := hequiv.kernel_eq (closedSaddleFn_lowerCl K) hK.lowerCl (ProperSaddleFn.lowerCl hK hp)
    (closedSaddleFn_of_mem_saddleClass_lowerCl hK hp hs hL) hCC
    (properSaddleFn_of_mem_saddleClass_lowerCl hK hp hL)
  rw [← h, kernel_lowerCl hK hp hs]

/-- Conversely, a closed proper concave-convex function with the same kernel as `K` lies between
the two closures. -/
theorem mem_saddleClass_lowerCl_of_kernel_eq (hK : ConcaveConvexFn K) (hp : ProperSaddleFn K)
    (hs : SimpleSaddleFn K) (hclL : ClosedSaddleFn L) (hCC : ConcaveConvexFn L)
    (hpL : ProperSaddleFn L) (hker : kernel L = kernel K) :
    L ∈ saddleClass (lowerCl K) (upperCl K) := by
  have hequiv : SaddleEquiv (lowerCl K) L :=
    (saddleEquiv_iff_kernel_eq (closedSaddleFn_lowerCl K) hK.lowerCl (ProperSaddleFn.lowerCl hK hp)
      hclL hCC hpL).2 ((kernel_lowerCl hK hp hs).trans hker.symm)
  have h2 : partialCl₂ L = lowerCl K := by
    rw [← hequiv.2, convexClosedFn_lowerCl K]
  have h1 : partialCl₁ L = upperCl K := by
    rw [← hequiv.1, partialCl₁_lowerCl hK hp hs]
  have hmem := mem_saddleClass_self L
  rw [h1, h2] at hmem
  exact hmem

/-- The kernel of a simple proper concave-convex function is the kernel of exactly one equivalence
class of closed proper concave-convex functions, represented by the lower closure `cl₂ cl₁ K`. -/
theorem exists_unique_saddleEquiv_class_of_kernel (hK : ConcaveConvexFn K)
    (hp : ProperSaddleFn K) (hs : SimpleSaddleFn K) :
    ∃ M : U × X → EReal, (ClosedSaddleFn M ∧ ConcaveConvexFn M ∧ ProperSaddleFn M ∧
      kernel M = kernel K) ∧ ∀ L : U × X → EReal, ClosedSaddleFn L → ConcaveConvexFn L →
      ProperSaddleFn L → (kernel L = kernel K ↔ SaddleEquiv M L) := by
  refine ⟨lowerCl K, ⟨closedSaddleFn_lowerCl K, hK.lowerCl, ProperSaddleFn.lowerCl hK hp,
    kernel_lowerCl hK hp hs⟩, fun L hclL hCC hpL => ?_⟩
  rw [saddleEquiv_iff_kernel_eq (closedSaddleFn_lowerCl K) hK.lowerCl
    (ProperSaddleFn.lowerCl hK hp) hclL hCC hpL, kernel_lowerCl hK hp hs]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

end SaddleClass

/-! ### The simple extensions of a finite saddle-function on `C × D` -/

section SimpleExt

variable {E : Type*}

/-- The effective domain of a finite function extended by `⊤` is the set it was given on. -/
theorem dom_restrict_coe (s : Set E) (g : E → ℝ) : dom (restrict s fun x => (g x : EReal)) = s := by
  ext x
  by_cases hx : x ∈ s <;> simp [hx]

/-- The concave effective domain of a finite function extended by `⊥` is the set it was given
on. -/
theorem domConcave_restrictConcave_coe (s : Set E) (g : E → ℝ) :
    domConcave (restrictConcave s fun x => (g x : EReal)) = s := by
  ext x
  by_cases hx : x ∈ s <;> simp [hx]

end SimpleExt

section SimpleExtConvex

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Constant functions are concave; the mirror of `convexFn_const`. -/
theorem concaveFn_const (c : EReal) : ConcaveFn (fun _ : E => c) :=
  concaveFn_iff_convexFn_neg.2 (convexFn_const (-c))

/-- Restricting a concave function to a convex set — extending by `⊥` off it — gives a concave
function; the mirror of `ConvexFn.restrict`. -/
theorem ConcaveFn.restrictConcave {g : E → EReal} {s : Set E} (hg : ConcaveFn g)
    (hs : Convex ℝ s) : ConcaveFn (ConvexAnalysis.restrictConcave s g) := by
  refine concaveFn_iff_convexFn_neg.2 ?_
  rw [neg_restrictConcave]
  exact hg.convexFn_neg.restrict hs

end SimpleExtConvex

section LowerSimpleExt

variable {U X : Type*} {C : Set U} {D : Set X} {K : U × X → ℝ}

/-- Rockafellar's **lower simple extension** `K₁` of a finite saddle-function `K` on `C × D`:
`K` on `C × D`, `+∞` on `C × Dᶜ`, and `-∞` off `C`. -/
noncomputable def lowerSimpleExt (C : Set U) (D : Set X) (K : U × X → ℝ) : U × X → EReal :=
  fun p => restrictConcave C (fun u => restrict D (fun x => (K (u, x) : EReal)) p.2) p.1

@[simp] theorem lowerSimpleExt_of_mem {p : U × X} (hu : p.1 ∈ C) (hx : p.2 ∈ D) :
    lowerSimpleExt C D K p = (K p : EReal) := by
  simp [lowerSimpleExt, hu, hx]

@[simp] theorem lowerSimpleExt_of_notMem_left {p : U × X} (hu : p.1 ∉ C) :
    lowerSimpleExt C D K p = ⊥ := by
  simp [lowerSimpleExt, hu]

@[simp] theorem lowerSimpleExt_of_notMem_right {p : U × X} (hu : p.1 ∈ C) (hx : p.2 ∉ D) :
    lowerSimpleExt C D K p = ⊤ := by
  simp [lowerSimpleExt, hu, hx]

/-- Over `C` the convex slice of `K₁` is `K (u, ·)` extended by `⊤` off `D`. -/
theorem lowerSimpleExt_slice₂_of_mem {u : U} (hu : u ∈ C) :
    (fun x => lowerSimpleExt C D K (u, x)) = restrict D fun x => (K (u, x) : EReal) := by
  funext x
  by_cases hx : x ∈ D <;> simp [lowerSimpleExt, hu, hx]

/-- Off `C` the convex slice of `K₁` is the constant `-∞`. -/
theorem lowerSimpleExt_slice₂_of_notMem {u : U} (hu : u ∉ C) :
    (fun x => lowerSimpleExt C D K (u, x)) = fun _ => (⊥ : EReal) := by
  funext x
  simp [lowerSimpleExt, hu]

/-- Over `D` the concave slice of `K₁` is `K (·, x)` extended by `-∞` off `C`. -/
theorem lowerSimpleExt_slice₁_of_mem {x : X} (hx : x ∈ D) :
    (fun u => lowerSimpleExt C D K (u, x)) = restrictConcave C fun u => (K (u, x) : EReal) := by
  funext u
  by_cases hu : u ∈ C <;> simp [lowerSimpleExt, hu, hx]

/-- Off `D` the concave slice of `K₁` is the indicator-like function that is `+∞` on `C` and `-∞`
off it. -/
theorem lowerSimpleExt_slice₁_of_notMem {x : X} (hx : x ∉ D) :
    (fun u => lowerSimpleExt C D K (u, x)) = restrictConcave C fun _ => (⊤ : EReal) := by
  funext u
  by_cases hu : u ∈ C <;> simp [lowerSimpleExt, hu, hx]

/-- The lower simple extension has `dom₁ K₁ = C`. -/
theorem dom₁_lowerSimpleExt (hD : D.Nonempty) : dom₁ (lowerSimpleExt C D K) = C := by
  obtain ⟨x₀, hx₀⟩ := hD
  ext u
  refine ⟨fun hu => ?_, fun hu x => ?_⟩
  · by_contra h
    have := hu x₀
    rw [lowerSimpleExt_of_notMem_left (p := (u, x₀)) h] at this
    exact absurd this (lt_irrefl ⊥)
  · by_cases hx : x ∈ D
    · rw [lowerSimpleExt_of_mem (p := (u, x)) hu hx]
      exact EReal.bot_lt_coe _
    · rw [lowerSimpleExt_of_notMem_right (p := (u, x)) hu hx]
      exact bot_lt_top

/-- The lower simple extension has `dom₂ K₁ = D`. -/
theorem dom₂_lowerSimpleExt (hC : C.Nonempty) : dom₂ (lowerSimpleExt C D K) = D := by
  obtain ⟨u₀, hu₀⟩ := hC
  ext x
  refine ⟨fun hx => ?_, fun hx u => ?_⟩
  · by_contra h
    have := hx u₀
    rw [lowerSimpleExt_of_notMem_right (p := (u₀, x)) hu₀ h] at this
    exact absurd this (lt_irrefl ⊤)
  · by_cases hu : u ∈ C
    · rw [lowerSimpleExt_of_mem (p := (u, x)) hu hx]
      exact EReal.coe_lt_top _
    · rw [lowerSimpleExt_of_notMem_left (p := (u, x)) hu]
      exact bot_lt_top

end LowerSimpleExt

section LowerSimpleExtConvex

variable {U X : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]
  {C : Set U} {D : Set X} {K : U × X → ℝ}

/-- The lower simple extension of a finite concave-convex function on `C × D` is concave-convex on
all of `U × X`. -/
theorem concaveConvexFn_lowerSimpleExt (hC : Convex ℝ C)
    (hconv : ∀ u ∈ C, ConvexOn ℝ D fun x => K (u, x))
    (hconc : ∀ x ∈ D, ConcaveOn ℝ C fun u => K (u, x)) :
    ConcaveConvexFn (lowerSimpleExt C D K) := by
  constructor
  · intro x
    by_cases hx : x ∈ D
    · rw [lowerSimpleExt_slice₁_of_mem hx]
      exact (concaveOn_iff_concaveFn C fun u => K (u, x)).1 (hconc x hx)
    · rw [lowerSimpleExt_slice₁_of_notMem hx]
      exact (concaveFn_const ⊤).restrictConcave hC
  · intro u
    by_cases hu : u ∈ C
    · rw [lowerSimpleExt_slice₂_of_mem hu]
      exact (convexOn_iff_convexFn D fun x => K (u, x)).1 (hconv u hu)
    · rw [lowerSimpleExt_slice₂_of_notMem hu]
      exact convexFn_const ⊥

omit [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X] in
/-- The lower simple extension of a finite saddle-function on a nonempty `C × D` is proper. -/
theorem properSaddleFn_lowerSimpleExt (hCne : C.Nonempty) (hDne : D.Nonempty) :
    ProperSaddleFn (lowerSimpleExt C D K) :=
  ⟨by rw [dom₁_lowerSimpleExt hDne]; exact hCne, by rw [dom₂_lowerSimpleExt hCne]; exact hDne⟩

end LowerSimpleExtConvex

section LowerSimpleExtFD

variable {U X : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  {C : Set U} {D : Set X} {K : U × X → ℝ}

omit [FiniteDimensional ℝ U] [FiniteDimensional ℝ X] in
/-- The lower simple extension of a finite saddle-function is simple. Its slices have effective
domains exactly `D` and `C`, so they do not even reach the boundary. -/
theorem simpleSaddleFn_lowerSimpleExt (hCne : C.Nonempty) (hDne : D.Nonempty) :
    SimpleSaddleFn (lowerSimpleExt C D K) := by
  constructor
  · intro u hu
    rw [dom₁_lowerSimpleExt (K := K) hDne] at hu
    rw [dom₂_lowerSimpleExt (K := K) hCne,
      lowerSimpleExt_slice₂_of_mem (intrinsicInterior_subset hu), dom_restrict_coe]
    exact subset_closure
  · intro x hx
    rw [dom₂_lowerSimpleExt (K := K) hCne] at hx
    rw [dom₁_lowerSimpleExt (K := K) hDne,
      lowerSimpleExt_slice₁_of_mem (intrinsicInterior_subset hx), domConcave_restrictConcave_coe]
    exact subset_closure

omit [FiniteDimensional ℝ U] [FiniteDimensional ℝ X] in
/-- The kernel of the lower simple extension is the restriction of `K` to `ri (C × D)`. -/
theorem kernel_lowerSimpleExt (hCne : C.Nonempty) (hDne : D.Nonempty) :
    kernel (lowerSimpleExt C D K) = restrict (ri (C ×ˢ D)) fun p => (K p : EReal) := by
  have hset : kernelSet (lowerSimpleExt C D K) = ri (C ×ˢ D) := by
    rw [kernelSet, dom₁_lowerSimpleExt (K := K) hDne, dom₂_lowerSimpleExt (K := K) hCne,
      intrinsicInterior_prod_eq]
  funext p
  by_cases hp : p ∈ ri (C ×ˢ D)
  · have hp' : p ∈ kernelSet (lowerSimpleExt C D K) := by rw [hset]; exact hp
    rw [kernel_of_mem hp', restrict_of_mem hp,
      lowerSimpleExt_of_mem (intrinsicInterior_subset (hset ▸ hp')).1
        (intrinsicInterior_subset (hset ▸ hp')).2]
  · have hp' : p ∉ kernelSet (lowerSimpleExt C D K) := by rw [hset]; exact hp
    rw [kernel_of_notMem hp', restrict_of_notMem hp]

/-- A finite concave-convex function `K` on a nonempty product `C × D` of convex sets is the
kernel of exactly one equivalence class of closed proper concave-convex functions on `U × X`. The
class is the one attached to the lower simple extension of `K`. -/
theorem exists_unique_saddleEquiv_class_of_finite (hC : Convex ℝ C)
    (hCne : C.Nonempty) (hDne : D.Nonempty)
    (hconv : ∀ u ∈ C, ConvexOn ℝ D fun x => K (u, x))
    (hconc : ∀ x ∈ D, ConcaveOn ℝ C fun u => K (u, x)) :
    ∃ M : U × X → EReal, (ClosedSaddleFn M ∧ ConcaveConvexFn M ∧ ProperSaddleFn M ∧
      kernel M = restrict (ri (C ×ˢ D)) fun p => (K p : EReal)) ∧
      ∀ L : U × X → EReal, ClosedSaddleFn L → ConcaveConvexFn L → ProperSaddleFn L →
        (kernel L = restrict (ri (C ×ˢ D)) (fun p => (K p : EReal)) ↔ SaddleEquiv M L) := by
  obtain ⟨M, ⟨hclM, hCCM, hpM, hkerM⟩, huniq⟩ :=
    exists_unique_saddleEquiv_class_of_kernel (concaveConvexFn_lowerSimpleExt hC hconv hconc)
      (properSaddleFn_lowerSimpleExt hCne hDne) (simpleSaddleFn_lowerSimpleExt hCne hDne)
  rw [kernel_lowerSimpleExt hCne hDne] at hkerM
  refine ⟨M, ⟨hclM, hCCM, hpM, hkerM⟩, fun L hclL hCCL hpL => ?_⟩
  rw [← huniq L hclL hCCL hpL, kernel_lowerSimpleExt hCne hDne]

end LowerSimpleExtFD

/-! ### Closedness of a finite continuous function on a closed set -/

section ClosedRestrict

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [IsTopologicalAddGroup E]
  {s : Set E} {g : E → ℝ}

omit [AddCommGroup E] [IsTopologicalAddGroup E] in
/-- The epigraph of a finite continuous function on a closed set, extended by `⊤`, is closed. -/
theorem isClosed_epi_restrict_coe (hs : IsClosed s) (hg : ContinuousOn g s) :
    IsClosed (epi (restrict s fun x => (g x : EReal))) := by
  rw [epi_restrict_coe]
  have hcont : ContinuousOn (fun p : E × ℝ => g p.1 - p.2) (s ×ˢ (Set.univ : Set ℝ)) :=
    (hg.comp continuousOn_fst fun p hp => hp.1).sub continuousOn_snd
  have h := hcont.preimage_isClosed_of_isClosed (hs.prod isClosed_univ)
    (isClosed_Iic (a := (0 : ℝ)))
  convert h using 1
  ext p
  simp [Set.mem_prod]

/-- A finite continuous function on a closed set, extended by `⊤`, is a closed function. -/
theorem closedFn_restrict_coe (hs : IsClosed s) (hg : ContinuousOn g s) :
    ClosedFn (restrict s fun x => (g x : EReal)) := by
  have hne : ∀ x, (restrict s fun x => (g x : EReal)) x ≠ ⊥ := by
    intro x
    by_cases hx : x ∈ s <;> simp [hx]
  exact (closedFn_iff_lowerSemicontinuous hne).2
    (lowerSemicontinuous_iff_isClosed_epi.2 (isClosed_epi_restrict_coe hs hg))

/-- The concave mirror: a finite continuous function on a closed set, extended by `-∞`, is a closed
concave function. -/
theorem closedConcaveFn_restrictConcave_coe (hs : IsClosed s) (hg : ContinuousOn g s) :
    ClosedConcaveFn (restrictConcave s fun x => (g x : EReal)) := by
  rw [closedConcaveFn_iff, neg_restrictConcave]
  simp only [← EReal.coe_neg]
  exact closedFn_restrict_coe hs hg.neg

end ClosedRestrict

/-! ### The upper simple extension -/

section UpperSimpleExt

variable {U X : Type*} {C : Set U} {D : Set X} {K : U × X → ℝ}

/-- Rockafellar's **upper simple extension** `K₂` of a finite saddle-function `K` on `C × D`:
`K` on `C × D`, `-∞` on `Cᶜ × D`, and `+∞` off `D`. -/
noncomputable def upperSimpleExt (C : Set U) (D : Set X) (K : U × X → ℝ) : U × X → EReal :=
  fun p => restrict D (fun x => restrictConcave C (fun u => (K (u, x) : EReal)) p.1) p.2

/-- The real-valued companion of `saddleSwap`: negate and exchange the two arguments. Note that
`swapReal (swapReal K) = K` is **not** `rfl`, because the negation is on `ℝ` values. -/
def swapReal (K : U × X → ℝ) : X × U → ℝ := fun q => -K (q.2, q.1)

@[simp] theorem swapReal_swapReal (K : U × X → ℝ) : swapReal (swapReal K) = K := by
  funext q
  simp [swapReal]

/-- **The upper simple extension is the lower one, swapped.**

This identity is the whole of the upper theory: exchanging the two arguments turns `C` into `D`,
the concave restriction into the convex one and `-∞` into `+∞`, which is what `saddleSwap` does on
the value side and `swapReal` on the real side. Every upper lemma below is a rewrite along it. -/
theorem upperSimpleExt_eq_saddleSwap (C : Set U) (D : Set X) (K : U × X → ℝ) :
    upperSimpleExt C D K = saddleSwap (lowerSimpleExt D C (swapReal K)) := by
  funext p
  obtain ⟨u, x⟩ := p
  by_cases hx : x ∈ D <;> by_cases hu : u ∈ C <;>
    simp [upperSimpleExt, lowerSimpleExt, saddleSwap, swapReal, hu, hx]

@[simp] theorem upperSimpleExt_of_mem {p : U × X} (hu : p.1 ∈ C) (hx : p.2 ∈ D) :
    upperSimpleExt C D K p = (K p : EReal) := by
  rw [upperSimpleExt_eq_saddleSwap, saddleSwap_apply,
    lowerSimpleExt_of_mem (p := (p.2, p.1)) hx hu]
  simp [swapReal]

@[simp] theorem upperSimpleExt_of_notMem_right {p : U × X} (hx : p.2 ∉ D) :
    upperSimpleExt C D K p = ⊤ := by
  rw [upperSimpleExt_eq_saddleSwap, saddleSwap_apply,
    lowerSimpleExt_of_notMem_left (p := (p.2, p.1)) hx]
  simp

@[simp] theorem upperSimpleExt_of_notMem_left {p : U × X} (hu : p.1 ∉ C) (hx : p.2 ∈ D) :
    upperSimpleExt C D K p = ⊥ := by
  rw [upperSimpleExt_eq_saddleSwap, saddleSwap_apply,
    lowerSimpleExt_of_notMem_right (p := (p.2, p.1)) hx hu]
  simp

/-- Over `C` the convex slice of `K₂` agrees with that of `K₁`. -/
theorem upperSimpleExt_slice₂_of_mem {u : U} (hu : u ∈ C) :
    (fun x => upperSimpleExt C D K (u, x)) = restrict D fun x => (K (u, x) : EReal) := by
  funext x
  by_cases hx : x ∈ D <;> simp [upperSimpleExt, hu, hx]

/-- Off `C` the convex slice of `K₂` is `-∞` on `D` and `+∞` elsewhere. -/
theorem upperSimpleExt_slice₂_of_notMem {u : U} (hu : u ∉ C) :
    (fun x => upperSimpleExt C D K (u, x)) = restrict D fun _ => (⊥ : EReal) := by
  funext x
  by_cases hx : x ∈ D <;> simp [upperSimpleExt, hu, hx]

/-- Over `D` the concave slice of `K₂` agrees with that of `K₁`. -/
theorem upperSimpleExt_slice₁_of_mem {x : X} (hx : x ∈ D) :
    (fun u => upperSimpleExt C D K (u, x)) = restrictConcave C fun u => (K (u, x) : EReal) := by
  funext u
  by_cases hu : u ∈ C <;> simp [upperSimpleExt, hu, hx]

/-- Off `D` the concave slice of `K₂` is the constant `+∞`. -/
theorem upperSimpleExt_slice₁_of_notMem {x : X} (hx : x ∉ D) :
    (fun u => upperSimpleExt C D K (u, x)) = fun _ => (⊤ : EReal) := by
  funext u
  simp [upperSimpleExt, hx]

/-- The upper simple extension has `dom₁ K₂ = C`. -/
theorem dom₁_upperSimpleExt (hD : D.Nonempty) : dom₁ (upperSimpleExt C D K) = C := by
  rw [upperSimpleExt_eq_saddleSwap, dom₁_saddleSwap]
  exact dom₂_lowerSimpleExt hD

/-- The upper simple extension has `dom₂ K₂ = D`. -/
theorem dom₂_upperSimpleExt (hC : C.Nonempty) : dom₂ (upperSimpleExt C D K) = D := by
  rw [upperSimpleExt_eq_saddleSwap, dom₂_saddleSwap]
  exact dom₁_lowerSimpleExt hC

/-- The interval between the two simple extensions is exactly the set of extensions of `K` with
Rockafellar's prescribed infinite values off `C × D` — the class `Ω`. The values on `Cᶜ × Dᶜ` are
unconstrained. -/
theorem mem_saddleClass_simpleExt_iff {L : U × X → EReal} :
    L ∈ saddleClass (lowerSimpleExt C D K) (upperSimpleExt C D K) ↔
      (∀ u ∈ C, ∀ x ∈ D, L (u, x) = (K (u, x) : EReal)) ∧
        (∀ u ∈ C, ∀ x ∉ D, L (u, x) = ⊤) ∧ ∀ u ∉ C, ∀ x ∈ D, L (u, x) = ⊥ := by
  rw [mem_saddleClass]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun u hu x hx => le_antisymm ?_ ?_, fun u hu x hx => ?_, fun u hu x hx => ?_⟩
    · have := h2 (u, x)
      rwa [upperSimpleExt_of_mem (p := (u, x)) hu hx] at this
    · have := h1 (u, x)
      rwa [lowerSimpleExt_of_mem (p := (u, x)) hu hx] at this
    · have := h1 (u, x)
      rw [lowerSimpleExt_of_notMem_right (p := (u, x)) hu hx] at this
      exact top_le_iff.1 this
    · have := h2 (u, x)
      rw [upperSimpleExt_of_notMem_left (p := (u, x)) hu hx] at this
      exact le_bot_iff.1 this
  · rintro ⟨h1, h2, h3⟩
    constructor
    · rintro ⟨u, x⟩
      by_cases hu : u ∈ C
      · by_cases hx : x ∈ D
        · rw [lowerSimpleExt_of_mem (p := (u, x)) hu hx, h1 u hu x hx]
        · rw [lowerSimpleExt_of_notMem_right (p := (u, x)) hu hx, h2 u hu x hx]
      · rw [lowerSimpleExt_of_notMem_left (p := (u, x)) hu]
        exact bot_le
    · rintro ⟨u, x⟩
      by_cases hx : x ∈ D
      · by_cases hu : u ∈ C
        · rw [upperSimpleExt_of_mem (p := (u, x)) hu hx, h1 u hu x hx]
        · rw [upperSimpleExt_of_notMem_left (p := (u, x)) hu hx, h3 u hu x hx]
      · rw [upperSimpleExt_of_notMem_right (p := (u, x)) hx]
        exact le_top

end UpperSimpleExt

section UpperSimpleExtConvex

variable {U X : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]
  {C : Set U} {D : Set X} {K : U × X → ℝ}

/-- The upper simple extension of a finite concave-convex function on `C × D` is concave-convex on
all of `U × X`.

Transported from `concaveConvexFn_lowerSimpleExt`: the swap exchanges the convexity and concavity
hypotheses and negates each, which is exactly `ConvexOn.neg` and `ConcaveOn.neg`. -/
theorem concaveConvexFn_upperSimpleExt (hD : Convex ℝ D)
    (hconv : ∀ u ∈ C, ConvexOn ℝ D fun x => K (u, x))
    (hconc : ∀ x ∈ D, ConcaveOn ℝ C fun u => K (u, x)) :
    ConcaveConvexFn (upperSimpleExt C D K) := by
  rw [upperSimpleExt_eq_saddleSwap]
  exact concaveConvexFn_saddleSwap
    (concaveConvexFn_lowerSimpleExt hD (fun x hx => (hconc x hx).neg)
      (fun u hu => (hconv u hu).neg))

end UpperSimpleExtConvex

/-! ### The class `Ω` is a full equivalence class -/

section FullClass

variable {U X : Type*} [TopologicalSpace U] [AddCommGroup U] [IsTopologicalAddGroup U]
  [TopologicalSpace X] [AddCommGroup X] [IsTopologicalAddGroup X] {C : Set U} {D : Set X}
  {K : U × X → ℝ} {L : U × X → EReal}

omit [TopologicalSpace U] [AddCommGroup U] [IsTopologicalAddGroup U] in
/-- The convex slices of the two simple extensions of a finite continuous saddle-function on a
closed `C × D` are closed, so `cl₂` fixes the lower simple extension. -/
theorem partialCl₂_lowerSimpleExt (hDcl : IsClosed D)
    (hcont : ∀ u ∈ C, ContinuousOn (fun x => K (u, x)) D) :
    partialCl₂ (lowerSimpleExt C D K) = lowerSimpleExt C D K := by
  funext p
  obtain ⟨u, x⟩ := p
  by_cases hu : u ∈ C
  · have h : (fun x => partialCl₂ (lowerSimpleExt C D K) (u, x))
        = restrict D fun x => (K (u, x) : EReal) := by
      rw [partialCl₂_slice (lowerSimpleExt C D K) u, lowerSimpleExt_slice₂_of_mem hu]
      exact closedFn_restrict_coe hDcl (hcont u hu)
    rw [congrFun h x, ← congrFun (lowerSimpleExt_slice₂_of_mem (K := K) hu) x]
  · have h : (fun x => partialCl₂ (lowerSimpleExt C D K) (u, x)) = fun _ => (⊥ : EReal) := by
      rw [partialCl₂_slice (lowerSimpleExt C D K) u, lowerSimpleExt_slice₂_of_notMem hu]
      exact clFn_const_bot
    rw [congrFun h x, lowerSimpleExt_of_notMem_left (p := (u, x)) hu]

omit [TopologicalSpace X] [AddCommGroup X] [IsTopologicalAddGroup X] in
/-- `cl₁` carries the lower simple extension to the upper one. -/
theorem partialCl₁_lowerSimpleExt (hCcl : IsClosed C) (hCne : C.Nonempty)
    (hcont : ∀ x ∈ D, ContinuousOn (fun u => K (u, x)) C) :
    partialCl₁ (lowerSimpleExt C D K) = upperSimpleExt C D K := by
  funext p
  obtain ⟨u, x⟩ := p
  by_cases hx : x ∈ D
  · have h : (fun u => partialCl₁ (lowerSimpleExt C D K) (u, x))
        = restrictConcave C fun u => (K (u, x) : EReal) := by
      rw [partialCl₁_slice (lowerSimpleExt C D K) x, lowerSimpleExt_slice₁_of_mem hx]
      exact closedConcaveFn_restrictConcave_coe hCcl (hcont x hx)
    rw [congrFun h u, ← congrFun (upperSimpleExt_slice₁_of_mem (K := K) hx) u]
  · obtain ⟨u₀, hu₀⟩ := hCne
    have h : (fun u => partialCl₁ (lowerSimpleExt C D K) (u, x)) = fun _ => (⊤ : EReal) := by
      rw [partialCl₁_slice (lowerSimpleExt C D K) x, lowerSimpleExt_slice₁_of_notMem hx]
      exact clConcave_eq_top_of_eq_top (x₀ := u₀) (by simp [hu₀])
    rw [congrFun h u, upperSimpleExt_of_notMem_right (p := (u, x)) hx]

omit [TopologicalSpace U] [AddCommGroup U] [IsTopologicalAddGroup U] in
/-- `cl₂` carries the upper simple extension back to the lower one.

The mirror of `partialCl₁_lowerSimpleExt`, transported rather than re-proved:
`partialCl₂_saddleSwap` exchanges the two closures, `upperSimpleExt_eq_saddleSwap` exchanges the
two extensions, and the continuity hypothesis passes through as `ContinuousOn.neg`. -/
theorem partialCl₂_upperSimpleExt (hDcl : IsClosed D) (hDne : D.Nonempty)
    (hcont : ∀ u ∈ C, ContinuousOn (fun x => K (u, x)) D) :
    partialCl₂ (upperSimpleExt C D K) = lowerSimpleExt C D K := by
  rw [upperSimpleExt_eq_saddleSwap, partialCl₂_saddleSwap,
    partialCl₁_lowerSimpleExt hDcl hDne (fun u hu => (hcont u hu).neg),
    upperSimpleExt_eq_saddleSwap, swapReal_swapReal, saddleSwap_saddleSwap]

/-- Every member of `Ω` is a closed saddle-function. -/
theorem closedSaddleFn_of_mem_saddleClass_simpleExt (hCcl : IsClosed C) (hDcl : IsClosed D)
    (hCne : C.Nonempty) (hDne : D.Nonempty)
    (hcontD : ∀ u ∈ C, ContinuousOn (fun x => K (u, x)) D)
    (hcontC : ∀ x ∈ D, ContinuousOn (fun u => K (u, x)) C)
    (hL : L ∈ saddleClass (lowerSimpleExt C D K) (upperSimpleExt C D K)) : ClosedSaddleFn L :=
  closedSaddleFn_of_mem_saddleClass (partialCl₁_lowerSimpleExt hCcl hCne hcontC)
    (partialCl₂_upperSimpleExt hDcl hDne hcontD) hL

/-- `Ω` is contained in a single equivalence class. -/
theorem saddleEquiv_of_mem_saddleClass_simpleExt (hCcl : IsClosed C) (hDcl : IsClosed D)
    (hCne : C.Nonempty) (hDne : D.Nonempty)
    (hcontD : ∀ u ∈ C, ContinuousOn (fun x => K (u, x)) D)
    (hcontC : ∀ x ∈ D, ContinuousOn (fun u => K (u, x)) C)
    (hL : L ∈ saddleClass (lowerSimpleExt C D K) (upperSimpleExt C D K)) :
    SaddleEquiv (lowerSimpleExt C D K) L :=
  saddleEquiv_of_mem_saddleClass (partialCl₁_lowerSimpleExt hCcl hCne hcontC)
    (partialCl₂_upperSimpleExt hDcl hDne hcontD)
    (mem_saddleClass_left (partialCl₂_upperSimpleExt hDcl hDne hcontD)) hL

/-- `Ω` is *exactly* the equivalence class of the lower simple extension, so the extensions of `K`
with the prescribed infinite values form one full equivalence class of closed saddle-functions.
Proved from closedness of the slices of the two simple extensions rather than from the bifunction
representation, so the hypotheses are separate continuity in each variable rather than joint
continuity. -/
theorem mem_saddleClass_simpleExt_iff_saddleEquiv (hCcl : IsClosed C) (hDcl : IsClosed D)
    (hCne : C.Nonempty) (hDne : D.Nonempty)
    (hcontD : ∀ u ∈ C, ContinuousOn (fun x => K (u, x)) D)
    (hcontC : ∀ x ∈ D, ContinuousOn (fun u => K (u, x)) C) :
    L ∈ saddleClass (lowerSimpleExt C D K) (upperSimpleExt C D K) ↔
      SaddleEquiv (lowerSimpleExt C D K) L := by
  refine ⟨saddleEquiv_of_mem_saddleClass_simpleExt hCcl hDcl hCne hDne hcontD hcontC, fun h => ?_⟩
  have h2 : partialCl₂ L = lowerSimpleExt C D K := by
    rw [← h.2, partialCl₂_lowerSimpleExt hDcl hcontD]
  have h1 : partialCl₁ L = upperSimpleExt C D K := by
    rw [← h.1, partialCl₁_lowerSimpleExt hCcl hCne hcontC]
  have hmem := mem_saddleClass_self L
  rw [h1, h2] at hmem
  exact hmem

omit [TopologicalSpace U] [AddCommGroup U] [IsTopologicalAddGroup U] [TopologicalSpace X]
  [AddCommGroup X] [IsTopologicalAddGroup X] in
/-- Every member of `Ω` is proper. -/
theorem properSaddleFn_of_mem_saddleClass_simpleExt (hCne : C.Nonempty) (hDne : D.Nonempty)
    (hL : L ∈ saddleClass (lowerSimpleExt C D K) (upperSimpleExt C D K)) : ProperSaddleFn L :=
  ⟨by
    refine Set.Nonempty.mono (dom₁_mono hL.1) ?_
    rw [dom₁_lowerSimpleExt (K := K) hDne]
    exact hCne, by
    refine Set.Nonempty.mono (dom₂_anti hL.2) ?_
    rw [dom₂_upperSimpleExt (K := K) hCne]
    exact hDne⟩

end FullClass

/-! ### The two brackets of a bifunction on a relative interior

The two brackets of a convex bifunction differ by a concave closure in the first variable. A
concave function agrees with its closure on the relative interior of its effective domain, and the
effective domain of `u ↦ ⟨Fu, y⟩` is `dom F` on the nose — so on `ri (dom F)` the two brackets are
simply equal. -/

section DomBracket

variable {U X Y : Type*} [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  {F : Bifun U X}

/-- **The concave effective domain of `u ↦ ⟨Fu, y⟩` is `dom F`**, for every `y`. The bracket is
`-∞` exactly where the slice `F u` is identically `+∞`. -/
theorem domConcave_bracket (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (F : Bifun U X) (y : Y) :
    domConcave (fun u => bracket Bx F u y) = domBifun F := by
  ext u
  change ⊥ < conj Bx (F u) y ↔ ∃ x, F u x ≠ ⊤
  rw [bot_lt_iff_ne_bot, ne_eq, conj_eq_bot_iff, not_forall]

end DomBracket

section BracketRelint

variable {U V X Y : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [AddCommGroup V] [Module ℝ V] [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  {F : Bifun U X}

/-- At a relative interior point of `dom F` the two brackets already agree —
`⟨Fu, y⟩ = ⟨u, F* y⟩`, with no closure in sight. -/
theorem bracket_eq_concaveBracket_adjointBifun_of_mem_relint (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (hF : ConvexBifun F) {u : U}
    (hu : u ∈ ri (domBifun F)) (y : Y) :
    bracket Bx F u y = concaveBracket Bu (adjointBifun Bu Bx F) u y := by
  rw [congrFun (concaveBracket_adjointBifun_eq_partialCl₁ (Bu := Bu) hF y) u,
    congrFun (partialCl₁_slice (fun p : U × Y => bracket Bx F p.1 p.2) y) u]
  exact ((concaveFn_bracket hF Bx y).clConcave_eq_of_mem_relint_domConcave
    (by rw [domConcave_bracket]; exact hu)).symm

end BracketRelint

/-! ### The two brackets of a polyhedral bifunction

The previous section puts the two brackets together on the *relative interior* of an effective
domain, because that is where a convex or concave function must agree with its closure. A
polyhedral function agrees with its closure on all of its effective domain, so for a polyhedral
bifunction the equality extends to the domain itself, leaving uncovered only the pairs with
`u ∉ dom F` *and* `y ∉ dom F*`, where the two brackets are `-∞` and `+∞`. The `u`-side half needs
no properness; the `y`-side half does, because it runs through `F** = cl F = F`. -/

section PolyhedralBrackets

variable {U V X Y : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
  {F : Bifun U X}

omit [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y] in
/-- Off `dom F` the bracket is `-∞`: there `F u` is identically `+∞`, and the conjugate of `+∞` is
`-∞`. -/
theorem bracket_eq_bot_of_notMem_domBifun (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) {u : U}
    (hu : u ∉ domBifun F) (y : Y) : bracket Bx F u y = ⊥ := by
  by_contra hne
  refine hu ?_
  rw [← domConcave_bracket Bx F y]
  exact bot_lt_iff_ne_bot.2 hne

omit [FiniteDimensional ℝ U] [FiniteDimensional ℝ V] [NormedAddCommGroup Y]
  [NormedSpace ℝ Y] [FiniteDimensional ℝ Y] in
/-- Off `dom G` the concave bracket is `+∞`, the mirror of `bracket_eq_bot_of_notMem_domBifun`. -/
theorem concaveBracket_eq_top_of_notMem_domConcaveBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (G : Bifun Y V) (u : U) {y : Y} (hy : y ∉ domConcaveBifun G) :
    concaveBracket Bu G u y = ⊤ := by
  by_contra hne
  refine hy ?_
  rw [← dom_concaveBracket Bu G u]
  exact lt_top_iff_ne_top.2 hne

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Y] in
/-- **The `u`-side half**: for a polyhedral convex bifunction the two brackets agree at every `u`
of `dom F`, not merely at the relative-interior points that
`bracket_eq_concaveBracket_adjointBifun_of_mem_relint` asks for.

The two differ by the concave closure in `u`; `⟨F·, y⟩` is polyhedral concave with effective
domain `dom F`, and a polyhedral function agrees with its closure on all of its effective domain.
Properness of `F` plays no part here. -/
theorem bracket_eq_concaveBracket_adjointBifun_of_mem_domBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (hF : PolyhedralBifun F) {u : U}
    (hu : u ∈ domBifun F) (y : Y) :
    bracket Bx F u y = concaveBracket Bu (adjointBifun Bu Bx F) u y := by
  rw [congrFun (concaveBracket_adjointBifun_eq_partialCl₁ (Bu := Bu)
      (PolyhedralBifun.convexBifun hF) y) u,
    congrFun (partialCl₁_slice (fun p : U × Y => bracket Bx F p.1 p.2) y) u]
  exact (clConcave_eq_of_mem_domConcave (polyhedralFn_neg_bracket hF Bx y)
    (by rw [domConcave_bracket]; exact hu)).symm

/-- **The `y`-side half**: for a *proper* polyhedral convex bifunction the two brackets agree at
every `y` of `dom F*`, for every `u`.

This is the first half read on the dual side: the brackets differ by the convex closure in `y`
once `cl F = F`, which properness plus polyhedrality supply; `⟨u, F*·⟩` is polyhedral convex with
effective domain `dom F*`, so the closure changes nothing there. -/
theorem bracket_eq_concaveBracket_adjointBifun_of_mem_domConcaveBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx]
    [IsCompatiblePairing Bx.flip] (hF : PolyhedralBifun F) (hp : Proper (graphFn F)) (u : U)
    {y : Y} (hy : y ∈ domConcaveBifun (adjointBifun Bu Bx F)) :
    bracket Bx F u y = concaveBracket Bu (adjointBifun Bu Bx F) u y := by
  have hcl : clFn (fun w => concaveBracket Bu (adjointBifun Bu Bx F) u w) y
      = bracket Bx F u y :=
    congrFun (partialCl₂_concaveBracket_adjoint Bu Bx (PolyhedralBifun.convexBifun hF)
      (closedBifun_of_polyhedralBifun hF hp)) (u, y)
  rw [← hcl]
  refine PolyhedralFn.clFn_eq_of_mem_dom
    (polyhedralFn_concaveBracket (polyhedralFn_neg_graphFn_adjointBifun Bu Bx hF) Bu u) ?_
  rw [dom_concaveBracket]
  exact hy

/-- For a proper polyhedral convex bifunction the two brackets agree, `⟨Fu, y⟩ = ⟨u, F* y⟩`, at
every pair `(u, y)` except those with `u ∉ dom F` and `y ∉ dom F*`. -/
theorem bracket_eq_concaveBracket_adjointBifun_of_polyhedral (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx]
    [IsCompatiblePairing Bx.flip] (hF : PolyhedralBifun F) (hp : Proper (graphFn F)) (u : U)
    (y : Y) (h : u ∈ domBifun F ∨ y ∈ domConcaveBifun (adjointBifun Bu Bx F)) :
    bracket Bx F u y = concaveBracket Bu (adjointBifun Bu Bx F) u y :=
  h.elim (fun hu => bracket_eq_concaveBracket_adjointBifun_of_mem_domBifun Bu Bx hF hu y)
    fun hy => bracket_eq_concaveBracket_adjointBifun_of_mem_domConcaveBifun Bu Bx hF hp u hy

omit [FiniteDimensional ℝ U] [FiniteDimensional ℝ V] [FiniteDimensional ℝ X]
  [FiniteDimensional ℝ Y] in
/-- The exceptional pairs: when `u ∉ dom F` and `y ∉ dom F*` one bracket is `-∞` and the other
`+∞`. Neither polyhedrality nor properness is used. -/
theorem bracket_eq_bot_and_concaveBracket_eq_top (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) {u : U} (hu : u ∉ domBifun F) {y : Y}
    (hy : y ∉ domConcaveBifun (adjointBifun Bu Bx F)) :
    bracket Bx F u y = ⊥ ∧ concaveBracket Bu (adjointBifun Bu Bx F) u y = ⊤ :=
  ⟨bracket_eq_bot_of_notMem_domBifun Bx hu y,
    concaveBracket_eq_top_of_notMem_domConcaveBifun Bu (adjointBifun Bu Bx F) u hy⟩

end PolyhedralBrackets

/-! ### The bifunction behind a finite continuous saddle-function

The two simple extensions of a finite continuous saddle-function on a closed `C × D` are a closure
pair, which is exactly what the representation by a closed convex bifunction asks for. Both
closure computations are already done — they are what the class `Ω` runs on — so the result is
their composition. -/

section SimpleExtClosed

variable {U Y : Type*} [TopologicalSpace U] [AddCommGroup U] [IsTopologicalAddGroup U]
  [TopologicalSpace Y] [AddCommGroup Y] [IsTopologicalAddGroup Y] {C : Set U} {D : Set Y}
  {K : U × Y → ℝ}

/-- The lower simple extension is lower closed. -/
theorem lowerClosedFn_lowerSimpleExt (hCcl : IsClosed C) (hDcl : IsClosed D) (hCne : C.Nonempty)
    (hDne : D.Nonempty) (hcontD : ∀ u ∈ C, ContinuousOn (fun x => K (u, x)) D)
    (hcontC : ∀ x ∈ D, ContinuousOn (fun u => K (u, x)) C) :
    LowerClosedFn (lowerSimpleExt C D K) := by
  rw [lowerClosedFn_iff, lowerCl_def, partialCl₁_lowerSimpleExt hCcl hCne hcontC,
    partialCl₂_upperSimpleExt hDcl hDne hcontD]

/-- The upper simple extension is upper closed. -/
theorem upperClosedFn_upperSimpleExt (hCcl : IsClosed C) (hDcl : IsClosed D) (hCne : C.Nonempty)
    (hDne : D.Nonempty) (hcontD : ∀ u ∈ C, ContinuousOn (fun x => K (u, x)) D)
    (hcontC : ∀ x ∈ D, ContinuousOn (fun u => K (u, x)) C) :
    UpperClosedFn (upperSimpleExt C D K) := by
  rw [upperClosedFn_iff, upperCl_def, partialCl₂_upperSimpleExt hDcl hDne hcontD,
    partialCl₁_lowerSimpleExt hCcl hCne hcontC]

end SimpleExtClosed

section SimpleExtBifun

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X]
  [TopologicalSpace Y] [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y] [LocallyConvexSpace ℝ Y]
  {C : Set U} {D : Set Y} {K : U × Y → ℝ}

/-- A finite continuous concave-convex function on a nonempty closed `C × D` has a unique closed
convex bifunction `F` whose two brackets are its lower and upper simple extensions. The explicit
formulas for `F` and `F*` are the definitions of the conjugate and the concave conjugate of the
slices. -/
theorem exists_unique_bifun_of_simpleExt (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu]
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip]
    (hC : Convex ℝ C) (hCcl : IsClosed C) (hDcl : IsClosed D) (hCne : C.Nonempty)
    (hconv : ∀ u ∈ C, ConvexOn ℝ D fun x => K (u, x))
    (hconc : ∀ x ∈ D, ConcaveOn ℝ C fun u => K (u, x))
    (hDne : D.Nonempty) (hcontD : ∀ u ∈ C, ContinuousOn (fun x => K (u, x)) D)
    (hcontC : ∀ x ∈ D, ContinuousOn (fun u => K (u, x)) C) :
    ∃! F : Bifun U X, ConvexBifun F ∧ ClosedBifun F ∧
      (fun p : U × Y => bracket Bx F p.1 p.2) = lowerSimpleExt C D K ∧
      (fun p : U × Y => concaveBracket Bu (adjointBifun Bu Bx F) p.1 p.2)
        = upperSimpleExt C D K :=
  exists_unique_bifun_of_closure_pair Bu Bx (concaveConvexFn_lowerSimpleExt hC hconv hconc)
    (partialCl₁_lowerSimpleExt hCcl hCne hcontC) (partialCl₂_upperSimpleExt hDcl hDne hcontD)

end SimpleExtBifun

end ConvexAnalysis
