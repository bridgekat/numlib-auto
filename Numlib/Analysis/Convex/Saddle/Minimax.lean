import Numlib.Analysis.Convex.Optimization.Lagrangian
import Numlib.Analysis.Convex.Optimization.Minimum
import Numlib.Analysis.Convex.Optimization.Normal
import Numlib.Analysis.Convex.Saddle.Kernel

/-!
# Minimax problems and conjugate saddle-functions

A function `K` of two variables has two iterated extrema, `maximin K = ⨆ u, ⨅ x, K (u, x)` and
`minimax K = ⨅ x, ⨆ u, K (u, x)`, the first never above the second; when they agree their common
value is the **saddle-value** of `K`. A **saddle-point** is a point `p` at which `K (·, p.2)` is
maximised and `K (p.1, ·)` minimised, which is exactly a pair of optimal strategies together with
the existence of the saddle-value. For a closed proper concave-convex `K` the whole space may be
replaced by `dom K` without changing either extremum, and both depend only on the equivalence
class of `K`.

The Lagrangian of a convex program is a saddle-function whose saddle-points are the pairs "optimal
solution, Kuhn–Tucker vector", whence the general Kuhn–Tucker theorem; and the Lagrangians of
closed convex programs are exactly the upper closed concave-convex functions.

The last part turns the iterated extrema into a conjugacy: `-K̲*(0, 0)` and `-K̄*(0, 0)` are
`minimax K` and `maximin K`, and both conjugates of every member of a class `Ω (F)` are read off
from `F` alone — the upper one is the Lagrangian of `F`, the lower one the bracket of `F_*^*`. So
the saddle-value exists exactly when the two conjugates agree at the origin.

## Main definitions

* `IsSaddlePoint K p`, `IsSaddlePointOn K C D p` — the saddle-point condition, over the whole space
  and relative to `C × D`.
* `maximin K`, `minimax K`, `HasSaddleValue K` — the two iterated extrema and their equality.
* `saddleLagrangian Bu F` — the Lagrangian of `(P)` read as a saddle-function on `V × X`;
  `flipBifun F` and `inverseBifun F` — arguments exchanged, and Rockafellar's `F_*`.
* `lowerConjSaddle Bu Bx K`, `upperConjSaddle Bu Bx K` — the conjugates `K̲*`, `K̄*`;
  `bifunSaddleClass Bu Bx F` — the class `Ω (F)`, squeezed between the two brackets of `F`.

## Main results

* `maximin_le_minimax` — `sup inf ≤ inf sup`; `isSaddlePoint_iff_attained` — a saddle-point is a
  pair of attained outer extrema that agree. Neither needs any structure at all, not even
  nonemptiness of the two spaces.
* `isSaddlePoint_iff_iSup_eq_iInf` — the one-equation form of the saddle-point condition, on which
  everything downstream is a computation of `⨆ u, K (u, x)` and `⨅ x, K (u, x)`.
* `maximin_eq_biSup_biInf`, `isSaddlePoint_iff_isSaddlePointOn_dom` — for a closed proper `K` both
  extrema and all saddle-points already live on `dom K`; `IsSaddlePoint.mem_domSaddle` — a
  saddle-point of a proper `K` lies in `dom K`; `SaddleEquiv.maximin_eq` — the two extrema see
  only the equivalence class.
* `isSaddlePoint_lagrangian_iff` — the saddle-points of the Lagrangian are the pairs "Kuhn–Tucker
  vector, optimal solution"; `isSaddlePoint_lagrangian_iff_normal_and_optimal` — the same read
  through normality; `mem_argmin_iff_exists_isSaddlePoint_lagrangian` — the general Kuhn–Tucker
  theorem (Theorem 36.6 in [^1]); `exists_unique_closedBifun_saddleLagrangian_eq` — Lagrangians
  are exactly the upper closed concave-convex functions (Theorem 36.5 in [^1]).
* `hasSaddleValue_iff_conjSaddle_zero_eq` — the saddle-value read off at the origin.
* `upperConjSaddle_eq_saddleLagrangian`, `lowerConjSaddle_eq_bracket_inverseBifun` — the two
  conjugates of a member of `Ω (F)`, in terms of `F` alone (Theorem 37.1 in [^1]);
  `concaveConvexFn_upperConjSaddle` and companions — they are again concave-convex, and closed.

## Implementation notes

`HasSaddleValue K` is the bare equation `maximin K = minimax K`; as in the book, finiteness of the
common value is a separate conclusion. The extrema are taken over the whole space, the `±∞`
extension making a problem on `C × D` into one on the product; `IsSaddlePointOn` records that.

Rockafellar writes the Lagrangian as `L (v, x) = ⟨v, F_* x⟩` and the bifunction behind the lower
conjugate as `F_*^*`, both through the *concave* inverse. There is no concave adjoint of a concave
bifunction here, so `inverseBifun (adjointBifun Bu Bx F)` is the definition of `F_*^*`; and the
characterisation of Lagrangians goes through `saddleSwap`, which turns the Lagrangian into a
bracket of `flipBifun F` for the negated pairing, where the convex theory applies verbatim.

## References

[^1]: R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §36, §37.
-/

namespace ConvexAnalysis

/-! ### Saddle-points and the two iterated extrema -/

section Basic

variable {U X : Type*} {K : U × X → EReal} {p : U × X}

/-- `p` is a **saddle-point** of `K`: the concave variable is maximised and the convex variable is
minimised there. -/
def IsSaddlePoint (K : U × X → EReal) (p : U × X) : Prop :=
  (∀ u, K (u, p.2) ≤ K p) ∧ ∀ x, K p ≤ K (p.1, x)

/-- `p` is a **saddle-point of `K` relative to `C × D`**: Rockafellar's saddle-point with respect
to maximising over `C` and minimising over `D`. -/
def IsSaddlePointOn (K : U × X → EReal) (C : Set U) (D : Set X) (p : U × X) : Prop :=
  p.1 ∈ C ∧ p.2 ∈ D ∧ (∀ u ∈ C, K (u, p.2) ≤ K p) ∧ ∀ x ∈ D, K p ≤ K (p.1, x)

/-- Rockafellar's `sup inf`. -/
noncomputable def maximin (K : U × X → EReal) : EReal := ⨆ u, ⨅ x, K (u, x)

/-- Rockafellar's `inf sup`. -/
noncomputable def minimax (K : U × X → EReal) : EReal := ⨅ x, ⨆ u, K (u, x)

theorem maximin_apply (K : U × X → EReal) : maximin K = ⨆ u, ⨅ x, K (u, x) := rfl

theorem minimax_apply (K : U × X → EReal) : minimax K = ⨅ x, ⨆ u, K (u, x) := rfl

/-- The **saddle-value of `K` exists** when the two iterated extrema agree. Following Rockafellar,
this says nothing about the common value being finite. -/
def HasSaddleValue (K : U × X → EReal) : Prop := maximin K = minimax K

theorem hasSaddleValue_iff : HasSaddleValue K ↔ maximin K = minimax K := Iff.rfl

/-- **`sup inf ≤ inf sup`**. No hypothesis at all is needed — in particular neither `U` nor `X`
need be nonempty. -/
theorem maximin_le_minimax (K : U × X → EReal) : maximin K ≤ minimax K :=
  iSup_le fun u => le_iInf fun x => (iInf_le (fun x => K (u, x)) x).trans
    (le_iSup (fun u => K (u, x)) u)

theorem iInf_slice_le_maximin (K : U × X → EReal) (u : U) : (⨅ x, K (u, x)) ≤ maximin K :=
  le_iSup (fun u => ⨅ x, K (u, x)) u

theorem minimax_le_iSup_slice (K : U × X → EReal) (x : X) : minimax K ≤ ⨆ u, K (u, x) :=
  iInf_le (fun x => ⨆ u, K (u, x)) x

theorem iInf_slice_le_self (K : U × X → EReal) (p : U × X) : (⨅ x, K (p.1, x)) ≤ K p :=
  iInf_le (fun x => K (p.1, x)) p.2

theorem le_iSup_slice (K : U × X → EReal) (p : U × X) : K p ≤ ⨆ u, K (u, p.2) :=
  le_iSup (fun u => K (u, p.2)) p.1

/-- **The saddle-point condition in one equation**: `p` is a saddle-point exactly when the maximum
of `K (·, p.2)` and the minimum of `K (p.1, ·)` agree, the common value being `K p`. -/
theorem isSaddlePoint_iff_iSup_eq_iInf :
    IsSaddlePoint K p ↔ (⨆ u, K (u, p.2)) = ⨅ x, K (p.1, x) := by
  constructor
  · rintro ⟨h1, h2⟩
    exact le_antisymm (le_iInf fun x => (iSup_le h1).trans (h2 x))
      ((iInf_slice_le_self K p).trans (le_iSup_slice K p))
  · intro h
    refine ⟨fun u => ?_, fun x => ?_⟩
    · exact ((le_iSup (fun u => K (u, p.2)) u).trans h.le).trans (iInf_slice_le_self K p)
    · exact ((le_iSup_slice K p).trans h.le).trans (iInf_le (fun x => K (p.1, x)) x)

theorem IsSaddlePoint.iSup_eq (h : IsSaddlePoint K p) : (⨆ u, K (u, p.2)) = K p :=
  le_antisymm (iSup_le h.1) (le_iSup_slice K p)

theorem IsSaddlePoint.iInf_eq (h : IsSaddlePoint K p) : (⨅ x, K (p.1, x)) = K p :=
  le_antisymm (iInf_slice_le_self K p) (le_iInf h.2)

/-- `p` is a saddle-point exactly when the outer supremum in `sup inf` is attained at `p.1`, the
outer infimum in `inf sup` is attained at `p.2`, and the two extrema are equal. -/
theorem isSaddlePoint_iff_attained :
    IsSaddlePoint K p ↔
      (⨅ x, K (p.1, x)) = maximin K ∧ (⨆ u, K (u, p.2)) = minimax K ∧ HasSaddleValue K := by
  constructor
  · intro h
    have h₁ : K p ≤ maximin K := h.iInf_eq ▸ iInf_slice_le_maximin K p.1
    have h₂ : minimax K ≤ K p := h.iSup_eq ▸ minimax_le_iSup_slice K p.2
    have hmm : maximin K = K p := le_antisymm ((maximin_le_minimax K).trans h₂) h₁
    have hMM : minimax K = K p := le_antisymm h₂ (h₁.trans (maximin_le_minimax K))
    exact ⟨by rw [h.iInf_eq, hmm], by rw [h.iSup_eq, hMM], by rw [hasSaddleValue_iff, hmm, hMM]⟩
  · rintro ⟨h1, h2, h3⟩
    exact isSaddlePoint_iff_iSup_eq_iInf.2 (by rw [h1, h2, hasSaddleValue_iff.1 h3])

/-- At a saddle-point the saddle-value is `K p`. -/
theorem IsSaddlePoint.maximin_eq (h : IsSaddlePoint K p) : maximin K = K p :=
  (isSaddlePoint_iff_attained.1 h).1.symm.trans h.iInf_eq

theorem IsSaddlePoint.minimax_eq (h : IsSaddlePoint K p) : minimax K = K p :=
  (isSaddlePoint_iff_attained.1 h).2.1.symm.trans h.iSup_eq

theorem IsSaddlePoint.hasSaddleValue (h : IsSaddlePoint K p) : HasSaddleValue K :=
  (isSaddlePoint_iff_attained.1 h).2.2

/-- A saddle-point relative to `C × D` is characterised by the same one equation, now with the
two extrema restricted. -/
theorem isSaddlePointOn_iff_biSup_eq_biInf {C : Set U} {D : Set X} (h₁ : p.1 ∈ C)
    (h₂ : p.2 ∈ D) :
    IsSaddlePointOn K C D p ↔ (⨆ u ∈ C, K (u, p.2)) = ⨅ x ∈ D, K (p.1, x) := by
  have hle : K p ≤ ⨆ u ∈ C, K (u, p.2) := le_iSup₂ (f := fun u (_ : u ∈ C) => K (u, p.2)) p.1 h₁
  have hge : (⨅ x ∈ D, K (p.1, x)) ≤ K p := iInf₂_le (f := fun x (_ : x ∈ D) => K (p.1, x)) p.2 h₂
  constructor
  · rintro ⟨-, -, hu, hx⟩
    exact le_antisymm (le_iInf₂ fun x hx' => (iSup₂_le hu).trans (hx x hx')) (hge.trans hle)
  · intro h
    refine ⟨h₁, h₂, fun u hu => ?_, fun x hx => ?_⟩
    · exact ((le_iSup₂ (f := fun u (_ : u ∈ C) => K (u, p.2)) u hu).trans h.le).trans hge
    · exact (hle.trans h.le).trans (iInf₂_le (f := fun x (_ : x ∈ D) => K (p.1, x)) x hx)

@[simp] theorem isSaddlePointOn_univ_univ :
    IsSaddlePointOn K Set.univ Set.univ p ↔ IsSaddlePoint K p := by
  simp only [IsSaddlePointOn, IsSaddlePoint, Set.mem_univ, true_and, forall_const]

/-! ### Restricting the outer extrema to the effective domains -/

theorem iInf_slice_eq_bot_of_notMem_dom₁ {u : U} (hu : u ∉ dom₁ K) : (⨅ x, K (u, x)) = ⊥ := by
  rw [mem_dom₁] at hu
  push Not at hu
  obtain ⟨x, hx⟩ := hu
  exact le_bot_iff.1 ((iInf_le (fun x => K (u, x)) x).trans hx)

theorem iSup_slice_eq_top_of_notMem_dom₂ {x : X} (hx : x ∉ dom₂ K) : (⨆ u, K (u, x)) = ⊤ := by
  rw [mem_dom₂] at hx
  push Not at hx
  obtain ⟨u, hu⟩ := hx
  exact top_le_iff.1 (hu.trans (le_iSup (fun u => K (u, x)) u))

/-- The outer supremum in `sup inf` may always be restricted to `dom₁ K`: off it the inner
infimum is `−∞`. -/
theorem maximin_eq_biSup_dom₁ (K : U × X → EReal) :
    maximin K = ⨆ u ∈ dom₁ K, ⨅ x, K (u, x) := by
  refine le_antisymm (iSup_le fun u => ?_)
    (iSup₂_le fun u _ => le_iSup (fun u => ⨅ x, K (u, x)) u)
  by_cases hu : u ∈ dom₁ K
  · exact le_iSup₂ (f := fun u (_ : u ∈ dom₁ K) => ⨅ x, K (u, x)) u hu
  · rw [iInf_slice_eq_bot_of_notMem_dom₁ hu]
    exact bot_le

/-- The outer infimum in `inf sup` may always be restricted to `dom₂ K`: off it the inner
supremum is `+∞`. -/
theorem minimax_eq_biInf_dom₂ (K : U × X → EReal) :
    minimax K = ⨅ x ∈ dom₂ K, ⨆ u, K (u, x) := by
  refine le_antisymm (le_iInf₂ fun x _ => iInf_le (fun x => ⨆ u, K (u, x)) x)
    (le_iInf fun x => ?_)
  by_cases hx : x ∈ dom₂ K
  · exact iInf₂_le (f := fun x (_ : x ∈ dom₂ K) => ⨆ u, K (u, x)) x hx
  · rw [iSup_slice_eq_top_of_notMem_dom₂ hx]
    exact le_top

end Basic

/-! ### The two extrema see only the equivalence class -/

section ClosureExtrema

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] {g : E → EReal}

/-- The concave mirror of `iInf_clFn_eq_iInf`: a concave function and its concave closure have the
same supremum. Like its convex original it needs no convexity. -/
theorem iSup_clConcave_eq_iSup (g : E → EReal) : (⨆ x, clConcave g x) = ⨆ x, g x := by
  have h : (⨆ x, clConcave g x) = -⨅ x, clFn (fun z => -(g z)) x := by
    rw [EReal.neg_iInf]
    exact iSup_congr fun x => rfl
  rw [h, iInf_clFn_eq_iInf, EReal.neg_iInf]
  exact iSup_congr fun x => neg_neg _

end ClosureExtrema

section EquivExtrema

variable {U X : Type*} [TopologicalSpace U] [AddCommGroup U] [TopologicalSpace X]
  [AddCommGroup X] {K L : U × X → EReal} {p : U × X}

omit [TopologicalSpace U] [AddCommGroup U] in
theorem iInf_partialCl₂_slice (K : U × X → EReal) (u : U) :
    (⨅ x, partialCl₂ K (u, x)) = ⨅ x, K (u, x) :=
  iInf_clFn_eq_iInf fun x => K (u, x)

omit [TopologicalSpace X] [AddCommGroup X] in
theorem iSup_partialCl₁_slice (K : U × X → EReal) (x : X) :
    (⨆ u, partialCl₁ K (u, x)) = ⨆ u, K (u, x) :=
  iSup_clConcave_eq_iSup fun u => K (u, x)

omit [AddCommGroup U] in
/-- Equivalent saddle-functions have the same inner infima — "two convex functions with the same
closure have the same infimum". -/
theorem SaddleEquiv.iInf_slice_eq (h : SaddleEquiv K L) (u : U) :
    (⨅ x, K (u, x)) = ⨅ x, L (u, x) := by
  rw [← iInf_partialCl₂_slice K u, ← iInf_partialCl₂_slice L u, h.2]

omit [AddCommGroup X] in
/-- Equivalent saddle-functions have the same inner suprema. -/
theorem SaddleEquiv.iSup_slice_eq (h : SaddleEquiv K L) (x : X) :
    (⨆ u, K (u, x)) = ⨆ u, L (u, x) := by
  rw [← iSup_partialCl₁_slice K x, ← iSup_partialCl₁_slice L x, h.1]

omit [AddCommGroup U] in
/-- Equivalent saddle-functions have the same `sup inf`. -/
theorem SaddleEquiv.maximin_eq (h : SaddleEquiv K L) : maximin K = maximin L :=
  iSup_congr fun u => h.iInf_slice_eq u

omit [AddCommGroup X] in
/-- Equivalent saddle-functions have the same `inf sup`. -/
theorem SaddleEquiv.minimax_eq (h : SaddleEquiv K L) : minimax K = minimax L :=
  iInf_congr fun x => h.iSup_slice_eq x

/-- Equivalent saddle-functions have the same saddle-value. -/
theorem SaddleEquiv.hasSaddleValue_iff (h : SaddleEquiv K L) :
    HasSaddleValue K ↔ HasSaddleValue L := by
  change maximin K = minimax K ↔ maximin L = minimax L
  rw [h.maximin_eq, h.minimax_eq]

/-- Equivalent saddle-functions have the same saddle-points. The saddle-point condition is an
equation between an inner supremum and an inner infimum (`isSaddlePoint_iff_iSup_eq_iInf`), and
equivalence preserves both. -/
theorem SaddleEquiv.isSaddlePoint_iff (h : SaddleEquiv K L) :
    IsSaddlePoint K p ↔ IsSaddlePoint L p := by
  rw [isSaddlePoint_iff_iSup_eq_iInf, isSaddlePoint_iff_iSup_eq_iInf, h.iSup_slice_eq,
    h.iInf_slice_eq]

end EquivExtrema

/-! ### Saddle-points of a proper saddle-function -/

section ProperSaddlePoints

variable {U X : Type*} {K : U × X → EReal} {p : U × X}

/-- A saddle-point of a proper saddle-function lies in its effective domain. Only properness is
used. -/
theorem IsSaddlePoint.mem_domSaddle (hp : ProperSaddleFn K) (h : IsSaddlePoint K p) :
    p ∈ domSaddle K := by
  obtain ⟨u₀, hu₀⟩ := hp.dom₁_nonempty
  obtain ⟨x₀, hx₀⟩ := hp.dom₂_nonempty
  have hbot : ⊥ < K p := by
    by_contra hc
    have hKp : K p = ⊥ := le_bot_iff.1 (not_lt.1 hc)
    exact absurd (le_bot_iff.1 (hKp ▸ h.1 u₀)) (ne_of_gt (hu₀ p.2))
  have htop : K p < ⊤ := by
    by_contra hc
    have hKp : K p = ⊤ := top_le_iff.1 (not_lt.1 hc)
    exact absurd (top_le_iff.1 (hKp ▸ h.2 x₀)) (ne_of_lt (hx₀ p.1))
  exact ⟨fun x => lt_of_lt_of_le hbot (h.2 x), fun u => lt_of_le_of_lt (h.1 u) htop⟩

/-- The saddle-value at a saddle-point of a proper saddle-function is finite. -/
theorem IsSaddlePoint.exists_maximin_eq_coe (hp : ProperSaddleFn K) (h : IsSaddlePoint K p) :
    ∃ r : ℝ, maximin K = (r : EReal) := by
  obtain ⟨r, hr⟩ := EReal.exists_coe_of_ne_bot_of_lt_top
    (ne_of_gt (bot_lt_of_mem_domSaddle (h.mem_domSaddle hp)))
    (lt_top_of_mem_domSaddle (h.mem_domSaddle hp))
  exact ⟨r, by rw [h.maximin_eq, hr]⟩

end ProperSaddlePoints

/-! ### Minimising a convex function over a set containing the relative interior -/

section RelintMin

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal}

/-- Minimising a convex function over any set that contains `ri (dom f)` already gives the global
infimum. -/
theorem ConvexFn.biInf_eq_iInf_of_relint_dom_subset (hf : ConvexFn f) {S : Set E}
    (hS : ri (dom f) ⊆ S) : (⨅ x ∈ S, f x) = ⨅ x, f x := by
  refine le_antisymm ?_ (le_iInf₂ fun x _ => iInf_le f x)
  refine EReal.le_of_forall_coe_le fun s hs => ?_
  refine EReal.le_coe_of_forall_lt fun q hq => ?_
  have hqc : ((s : ℝ) : EReal) < (q : EReal) := by exact_mod_cast hq
  obtain ⟨x, hx⟩ := iInf_lt_iff.1 (lt_of_le_of_lt hs hqc)
  obtain ⟨z, hz, hzq⟩ := hf.exists_mem_relint_dom_lt ⟨x, hx⟩
  exact lt_of_le_of_lt (iInf₂_le (f := fun x (_ : x ∈ S) => f x) z (hS hz)) hzq

end RelintMin

/-! ### The extrema and the saddle-points live on the effective domain -/

section DomainExtrema

variable {U X : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] {K : U × X → EReal}
  {p : U × X}

omit [FiniteDimensional ℝ U] in
/-- The inner infimum: for a closed proper concave-convex `K` the infimum of a slice over all of
`X` is already reached over `D = dom₂ K`. -/
theorem biInf_dom₂_eq_iInf_slice (hK : ConcaveConvexFn K) (hs : SaddleStructure K)
    (hp : ProperSaddleFn K) (u : U) : (⨅ x ∈ dom₂ K, K (u, x)) = ⨅ x, K (u, x) := by
  by_cases hu : u ∈ dom₁ K
  · refine ConvexFn.biInf_eq_iInf_of_relint_dom_subset (hK.convex_snd u) ?_
    have hrw : ri (dom fun x => K (u, x)) = ri (dom₂ K) :=
      Convex.relint_eq_of_subset_of_subset_closure hK.convex_dom₂ (hK.convex_snd u).convex_dom
        (dom₂_subset_dom_slice K u) (hs.1.dom_slice_subset_closure u hu)
    rw [hrw]
    exact intrinsicInterior_subset
  · obtain ⟨x₀, hx₀⟩ := ProperSaddleFn.relint_dom₂_nonempty hK hp
    have hbot : K (u, x₀) = ⊥ := hs.1.eq_bot_of_notMem_dom₁ u hu x₀ hx₀
    rw [iInf_slice_eq_bot_of_notMem_dom₁ hu]
    exact le_bot_iff.1 ((iInf₂_le (f := fun x (_ : x ∈ dom₂ K) => K (u, x)) x₀
      (intrinsicInterior_subset hx₀)).trans hbot.le)

omit [FiniteDimensional ℝ X] in
/-- The inner supremum: the mirror of `biInf_dom₂_eq_iInf_slice`, obtained from it at the swapped
saddle-function. -/
theorem biSup_dom₁_eq_iSup_slice (hK : ConcaveConvexFn K) (hs : SaddleStructure K)
    (hp : ProperSaddleFn K) (x : X) : (⨆ u ∈ dom₁ K, K (u, x)) = ⨆ u, K (u, x) := by
  have h := biInf_dom₂_eq_iInf_slice (concaveConvexFn_saddleSwap hK) hs.saddleSwap hp.saddleSwap x
  rw [dom₂_saddleSwap] at h
  have hneg := congrArg (fun z : EReal => -z) h
  simpa only [EReal.neg_iInf, saddleSwap_apply, neg_neg] using hneg

omit [FiniteDimensional ℝ U] in
/-- `sup inf` over the whole space is `sup inf` over `C × D`. -/
theorem maximin_eq_biSup_biInf (hK : ConcaveConvexFn K) (hs : SaddleStructure K)
    (hp : ProperSaddleFn K) : maximin K = ⨆ u ∈ dom₁ K, ⨅ x ∈ dom₂ K, K (u, x) := by
  rw [maximin_eq_biSup_dom₁]
  exact iSup_congr fun u => iSup_congr fun _ => (biInf_dom₂_eq_iInf_slice hK hs hp u).symm

omit [FiniteDimensional ℝ X] in
/-- `inf sup` over the whole space is `inf sup` over `C × D`. -/
theorem minimax_eq_biInf_biSup (hK : ConcaveConvexFn K) (hs : SaddleStructure K)
    (hp : ProperSaddleFn K) : minimax K = ⨅ x ∈ dom₂ K, ⨆ u ∈ dom₁ K, K (u, x) := by
  rw [minimax_eq_biInf_dom₂]
  exact iInf_congr fun x => iInf_congr fun _ => (biSup_dom₁_eq_iSup_slice hK hs hp x).symm

/-- The saddle-points of `K` with respect to the whole space are exactly its saddle-points with
respect to `C × D = dom K`. -/
theorem isSaddlePoint_iff_isSaddlePointOn_dom (hK : ConcaveConvexFn K) (hs : SaddleStructure K)
    (hp : ProperSaddleFn K) :
    IsSaddlePoint K p ↔ IsSaddlePointOn K (dom₁ K) (dom₂ K) p := by
  constructor
  · intro h
    obtain ⟨h₁, h₂⟩ := h.mem_domSaddle hp
    refine (isSaddlePointOn_iff_biSup_eq_biInf h₁ h₂).2 ?_
    rw [biSup_dom₁_eq_iSup_slice hK hs hp, biInf_dom₂_eq_iInf_slice hK hs hp]
    exact isSaddlePoint_iff_iSup_eq_iInf.1 h
  · intro h
    refine isSaddlePoint_iff_iSup_eq_iInf.2 ?_
    rw [← biSup_dom₁_eq_iSup_slice hK hs hp, ← biInf_dom₂_eq_iInf_slice hK hs hp]
    exact (isSaddlePointOn_iff_biSup_eq_biInf h.1 h.2.1).1 h

end DomainExtrema

/-! ### Slices of a bifunction in its *first* variable -/

section SliceFlip

variable {U X : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]
  {F : Bifun U X}

/-- Each *first*-variable slice `F (·) x` of a convex bifunction is convex. Not an instance of
`convexFn_compLin`, because `u ↦ (u, x)` is affine and not linear. -/
theorem ConvexBifun.convexFn_flip (hF : ConvexBifun F) (x : X) : ConvexFn fun u => F u x := by
  refine convexFn_of_epi_combo fun u w mu nu hu hw a b ha hb hab => ?_
  have h := hF.epi_combo (x := (u, x)) (y := (w, x)) hu hw ha hb hab
  have hx : a • ((u, x) : U × X) + b • (w, x) = (a • u + b • w, x) := by
    rw [Prod.smul_mk, Prod.smul_mk, Prod.mk_add_mk, ← add_smul, hab, one_smul]
  rwa [hx] at h

end SliceFlip

section ClosedSliceFlip

variable {U X : Type*} [TopologicalSpace U] [AddCommGroup U] [IsTopologicalAddGroup U]
  [TopologicalSpace X] [AddCommGroup X] [IsTopologicalAddGroup X] {F : Bifun U X}

/-- Each *first*-variable slice of a closed bifunction is closed — the mirror of
`ClosedBifun.imageClosedBifun`. -/
theorem ClosedBifun.closedFn_flip (hF : ClosedBifun F) (x : X) : ClosedFn fun u => F u x := by
  rcases closedFn_iff.1 (closedBifun_iff.1 hF) with h | ⟨hlsc, hne⟩
  · exact closedFn_iff.2 (Or.inl (funext fun u => congrFun h (u, x)))
  · exact closedFn_iff.2 (Or.inr ⟨lowerSemicontinuous_comp hlsc
      (continuous_id.prodMk continuous_const), fun u => hne (u, x)⟩)

end ClosedSliceFlip

/-! ### The Lagrangian as a saddle-function -/

section SaddleLagrangian

variable {U V X : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]

/-- The Lagrangian of `(P)` read as a function on the product `V × X`, i.e. as a saddle-function.
The minimax problem studied below is the one for exactly this function. -/
noncomputable def saddleLagrangian (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (F : Bifun U X) : V × X → EReal :=
  fun q => lagrangian Bu F q.1 q.2

theorem saddleLagrangian_apply (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (F : Bifun U X) (q : V × X) :
    saddleLagrangian Bu F q = lagrangian Bu F q.1 q.2 := rfl

end SaddleLagrangian

/-! ### Saddle-points of the Lagrangian -/

section LagrangianSaddlePoints

variable {U V X : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [TopologicalSpace U] [IsTopologicalAddGroup U]
  [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U] [TopologicalSpace X] [IsTopologicalAddGroup X]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsCompatiblePairing Bu] {F : Bifun U X} {v : V} {x : X}

omit [AddCommGroup X] [Module ℝ X] [TopologicalSpace X] [IsTopologicalAddGroup X] in
/-- The companion of `iInf_lagrangian`: *maximising* the Lagrangian over the price variable gives
the closure of the objective slice at the origin. This is the computation behind the criterion. -/
theorem iSup_lagrangian (hf : ConvexFn fun u => F u x) :
    (⨆ w, lagrangian Bu F w x) = clFn (fun u => F u x) 0 :=
  (clFn_zero_eq_iSup_iInf (B := Bu) hf).symm

/-- For a closed convex bifunction the supremum of the Lagrangian over the price variable is the
objective `(F 0)(x)` itself. -/
theorem iSup_lagrangian_eq (hF : ConvexBifun F) (hcl : ClosedBifun F) :
    (⨆ w, lagrangian Bu F w x) = F 0 x := by
  rw [iSup_lagrangian (hF.convexFn_flip x), congrFun (hcl.closedFn_flip x) 0]

omit [AddCommGroup X] [Module ℝ X] [TopologicalSpace U] [IsTopologicalAddGroup U]
  [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U] [IsCompatiblePairing Bu] [TopologicalSpace X]
  [IsTopologicalAddGroup X] in
/-- Properness bounds the Lagrangian's infimum away from `+∞`. -/
theorem iInf_lagrangian_ne_top (hpr : Proper (graphFn F)) :
    (⨅ y, lagrangian Bu F v y) ≠ ⊤ := by
  obtain ⟨q, hq⟩ := hpr.dom_nonempty
  refine ne_of_lt (lt_of_le_of_lt (iInf_le (fun y => lagrangian Bu F v y) q.2) ?_)
  refine lt_of_le_of_lt (iInf_le (fun u => ((Bu u v : ℝ) : EReal) + F u q.2) q.1) ?_
  exact _root_.EReal.add_lt_top (_root_.EReal.coe_ne_top _) (ne_of_lt hq)

/-- `(v, x)` is a saddle-point of the Lagrangian of `(P)` exactly when `v` is a Kuhn–Tucker vector
for `(P)` and `x` is an optimal solution to `(P)`.

The proof is the book's: `⨅ y, L (v, y) ≤ inf F 0 ≤ (F 0) x = ⨆ w, L (w, x)`, whose outer terms are
respectively `≠ ⊤` and `≠ ⊥` by properness, so the saddle-point condition collapses the chain. -/
theorem isSaddlePoint_lagrangian_iff (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (hpr : Proper (graphFn F)) :
    IsSaddlePoint (saddleLagrangian Bu F) (v, x)
      ↔ v ∈ KuhnTucker Bu F ∧ x ∈ argmin (F 0) := by
  have hA : (⨅ y, lagrangian Bu F v y) ≤ infBifun F 0 := iInf_lagrangian_le Bu F v
  have hB : infBifun F 0 ≤ F 0 x := iInf_le (fun z => F 0 z) x
  have hsup : (⨆ w, lagrangian Bu F w x) = F 0 x := iSup_lagrangian_eq hF hcl
  have hAtop : (⨅ y, lagrangian Bu F v y) ≠ ⊤ := iInf_lagrangian_ne_top hpr
  have hBbot : F 0 x ≠ ⊥ := hpr.ne_bot (0, x)
  rw [isSaddlePoint_iff_iSup_eq_iInf, mem_kuhnTucker_iff_iInf_lagrangian,
    mem_argmin_iff_le_iInf]
  change (⨆ w, lagrangian Bu F w x) = (⨅ y, lagrangian Bu F v y) ↔ _
  rw [hsup]
  constructor
  · intro h
    have h1 : (⨅ y, lagrangian Bu F v y) = infBifun F 0 :=
      le_antisymm hA (by rw [← h]; exact hB)
    have h2 : F 0 x = infBifun F 0 := by rw [h, h1]
    exact ⟨⟨by rw [← h1]; exact hAtop, by rw [← h2]; exact hBbot, h1⟩, le_of_eq h2⟩
  · rintro ⟨⟨-, -, h1⟩, h2⟩
    rw [h1]
    exact le_antisymm (le_trans h2 (le_of_eq rfl)) hB

end LagrangianSaddlePoints

/-! ### The general Kuhn–Tucker theorem -/

section KuhnTucker

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  [TopologicalSpace X] [IsTopologicalAddGroup X]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsCompatiblePairing Bu] {F : Bifun U X} {v : V} {x : X}

omit [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  [IsCompatiblePairing Bu] [TopologicalSpace X] [IsTopologicalAddGroup X] in
/-- Minimising the Lagrangian over the convex variable *is* evaluating the dual objective `F* 0`:
both are `⨅ u (⟨u, v⟩ + inf F u)`. -/
theorem iInf_lagrangian_eq_adjointBifun_zero (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) :
    (⨅ y, lagrangian Bu F v y) = adjointBifun Bu Bx F 0 v := by
  rw [iInf_lagrangian, adjointBifun_zero_apply]

/-- `(v, x)` is a saddle-point of the Lagrangian exactly when the primal objective at `x` is no
larger than the dual objective at `v` — in which case weak duality forces equality. -/
theorem isSaddlePoint_lagrangian_iff_le_adjointBifun (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (hF : ConvexBifun F) (hcl : ClosedBifun F) :
    IsSaddlePoint (saddleLagrangian Bu F) (v, x) ↔ F 0 x ≤ adjointBifun Bu Bx F 0 v := by
  have hge : adjointBifun Bu Bx F 0 v ≤ F 0 x :=
    (adjointBifun_zero_le Bu Bx F v).trans (iInf_le (fun z => F 0 z) x)
  rw [isSaddlePoint_iff_iSup_eq_iInf]
  change (⨆ w, lagrangian Bu F w x) = (⨅ y, lagrangian Bu F v y) ↔ _
  rw [iSup_lagrangian_eq hF hcl, iInf_lagrangian_eq_adjointBifun_zero (Bu := Bu) Bx]
  exact ⟨le_of_eq, fun h => le_antisymm h hge⟩

/-- `(v, x)` is a saddle-point of the Lagrangian exactly when normality holds and `x`, `v` are
optimal for `(P)` and `(P*)`. -/
theorem isSaddlePoint_lagrangian_iff_normal_and_optimal (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (hF : ConvexBifun F) (hcl : ClosedBifun F) (hpr : Proper (graphFn F)) :
    IsSaddlePoint (saddleLagrangian Bu F) (v, x) ↔ Normal F ∧ x ∈ argmin (F 0) ∧
      adjointBifun Bu Bx F 0 v = ⨆ w, adjointBifun Bu Bx F 0 w := by
  constructor
  · intro h
    obtain ⟨hv, hx⟩ := (isSaddlePoint_lagrangian_iff hF hcl hpr).1 h
    have hn : Normal F := normal_of_kuhnTucker_nonempty Bx hF ⟨v, hv⟩
    obtain ⟨ht, hb, -⟩ := (mem_kuhnTucker_iff_adjointBifun_zero_eq (Bx := Bx)).1 hv
    exact ⟨hn, hx,
      (mem_kuhnTucker_iff_adjointBifun_zero_eq_iSup (Bu := Bu) Bx hF hn ht hb).1 hv⟩
  · rintro ⟨hn, hx, hv⟩
    refine (isSaddlePoint_lagrangian_iff_le_adjointBifun Bx hF hcl).2 ?_
    rw [hv, (normal_iff_iSup_adjointBifun_eq (Bu := Bu) Bx hF).1 hn]
    exact mem_argmin_iff_le_iInf.1 hx

omit [AddCommGroup Y] [Module ℝ Y] in
/-- **The general Kuhn–Tucker theorem**: once one Kuhn–Tucker vector is known to exist, `x` solves
`(P)` exactly when some `v` makes `(v, x)` a saddle-point of the Lagrangian, and the `v` that do
are precisely the Kuhn–Tucker vectors. -/
theorem mem_argmin_iff_exists_isSaddlePoint_lagrangian (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (hpr : Proper (graphFn F)) (hkt : (KuhnTucker Bu F).Nonempty) :
    x ∈ argmin (F 0) ↔ ∃ v : V, IsSaddlePoint (saddleLagrangian Bu F) (v, x) := by
  constructor
  · intro hx
    obtain ⟨w, hw⟩ := hkt
    exact ⟨w, (isSaddlePoint_lagrangian_iff hF hcl hpr).2 ⟨hw, hx⟩⟩
  · rintro ⟨w, hw⟩
    exact ((isSaddlePoint_lagrangian_iff hF hcl hpr).1 hw).2

omit [AddCommGroup Y] [Module ℝ Y] in
/-- The "which `v`" clause: for an optimal `x`, the prices `v` completing it to a saddle-point of
the Lagrangian are exactly the Kuhn–Tucker vectors. -/
theorem isSaddlePoint_lagrangian_iff_mem_kuhnTucker (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (hpr : Proper (graphFn F)) (hx : x ∈ argmin (F 0)) :
    IsSaddlePoint (saddleLagrangian Bu F) (v, x) ↔ v ∈ KuhnTucker Bu F :=
  (isSaddlePoint_lagrangian_iff hF hcl hpr).trans ⟨fun h => h.1, fun h => ⟨h, hx⟩⟩

end KuhnTucker

section KuhnTuckerSlater

variable {U V X : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup X] [NormedSpace ℝ X]
  {F : Bifun U X}
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsCompatiblePairing Bu] {x : X}

/-- The Kuhn–Tucker theorem under the strong-consistency qualification: for a strongly consistent
closed proper convex program, `x` is an optimal solution exactly when it is the convex half of a
saddle-point of the Lagrangian. -/
theorem mem_argmin_iff_exists_isSaddlePoint_lagrangian_of_stronglyConsistent
    (hF : ConvexBifun F) (hcl : ClosedBifun F) (hpr : Proper (graphFn F))
    (hip : Proper (infBifun F)) (hs : StronglyConsistent F) (ht : infBifun F 0 ≠ ⊤) :
    x ∈ argmin (F 0) ↔ ∃ v : V, IsSaddlePoint (saddleLagrangian Bu F) (v, x) :=
  mem_argmin_iff_exists_isSaddlePoint_lagrangian hF hcl hpr
    (kuhnTucker_nonempty_of_stronglyConsistent hF hip hs ht)

end KuhnTuckerSlater

/-! ### Lagrangians are exactly the upper closed concave-convex functions -/

section FlipBifun

variable {U X : Type*}

/-- The bifunction with its two arguments exchanged. Unlike Rockafellar's inverse operation `F_*`
this does not negate, so it stays convex; it is what lets the convex bracket theory be applied to
the swapped saddle-function. -/
def flipBifun (F : Bifun U X) : Bifun X U := fun x u => F u x

@[simp] theorem flipBifun_apply (F : Bifun U X) (x : X) (u : U) : flipBifun F x u = F u x := rfl

@[simp] theorem flipBifun_flipBifun (F : Bifun U X) : flipBifun (flipBifun F) = F := rfl

theorem graphFn_flipBifun (F : Bifun U X) (q : X × U) :
    graphFn (flipBifun F) q = graphFn F (q.2, q.1) := rfl

end FlipBifun

section FlipBifunConvex

variable {U X : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]
  {F : Bifun U X}

/-- Exchanging the two arguments preserves convexity. -/
theorem convexBifun_flipBifun (hF : ConvexBifun F) : ConvexBifun (flipBifun F) := by
  refine convexFn_of_epi_combo fun q r mu nu hq hr a b ha hb hab => ?_
  have h := hF.epi_combo (x := (q.2, q.1)) (y := (r.2, r.1)) hq hr ha hb hab
  have hsw : a • ((q.2, q.1) : U × X) + b • (r.2, r.1)
      = ((a • q + b • r).2, (a • q + b • r).1) := rfl
  rwa [hsw] at h

end FlipBifunConvex

section FlipBifunClosed

variable {U X : Type*} [TopologicalSpace U] [AddCommGroup U] [IsTopologicalAddGroup U]
  [TopologicalSpace X] [AddCommGroup X] [IsTopologicalAddGroup X] {F : Bifun U X}

/-- Exchanging the two arguments preserves closedness. -/
theorem closedBifun_flipBifun (hF : ClosedBifun F) : ClosedBifun (flipBifun F) := by
  rcases closedFn_iff.1 (closedBifun_iff.1 hF) with h | ⟨hlsc, hne⟩
  · exact closedFn_iff.2 (Or.inl (funext fun q => congrFun h (q.2, q.1)))
  · exact closedFn_iff.2 (Or.inr ⟨lowerSemicontinuous_comp hlsc
      (continuous_snd.prodMk continuous_fst), fun q => hne (q.2, q.1)⟩)

end FlipBifunClosed

section LagrangianUpperClosed

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [LocallyConvexSpace ℝ V]
  [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X]
  [TopologicalSpace Y] [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y] [LocallyConvexSpace ℝ Y]
  {F : Bifun U X} {L : V × X → EReal}

omit [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U]
  [LocallyConvexSpace ℝ U] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
  [LocallyConvexSpace ℝ V] [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X] [TopologicalSpace Y]
  [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y] [LocallyConvexSpace ℝ Y] in
/-- **The Lagrangian is a bracket, after swapping.** Rockafellar writes it `L (v, x) = ⟨v, F_* x⟩`,
through the *inverse* bifunction; the same identity, negated and with the variables exchanged, is
the bracket of `flipBifun F` for the **negated** pairing, where the convex theory applies
verbatim. -/
theorem saddleSwap_saddleLagrangian (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (F : Bifun U X) :
    saddleSwap (saddleLagrangian Bu F)
      = fun q : X × V => bracket (-Bu) (flipBifun F) q.1 q.2 := by
  funext q
  rw [saddleSwap_apply, saddleLagrangian_apply, lagrangian_apply, bracket_apply,
    EReal.neg_iInf]
  refine iSup_congr fun u => ?_
  have hb : (((-Bu) u q.2 : ℝ) : EReal) = ((-(Bu u q.2) : ℝ) : EReal) := rfl
  rw [hb, _root_.EReal.coe_neg,
    _root_.EReal.neg_add (.inl (_root_.EReal.coe_ne_bot _)) (.inl (_root_.EReal.coe_ne_top _))]
  rfl

omit [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U]
  [LocallyConvexSpace ℝ U] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
  [LocallyConvexSpace ℝ V] [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  [LocallyConvexSpace ℝ X] in
/-- The Lagrangian of a convex program is a concave-convex function: the brackets of a convex
bifunction are, and the Lagrangian is one of them after swapping. -/
theorem concaveConvexFn_saddleLagrangian (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hF : ConvexBifun F) :
    ConcaveConvexFn (saddleLagrangian Bu F) := by
  have h : ConcaveConvexFn (saddleSwap (saddleLagrangian Bu F)) := by
    rw [saddleSwap_saddleLagrangian]
    exact concaveConvexFn_bracket (convexBifun_flipBifun hF) (-Bu)
  have h2 := concaveConvexFn_saddleSwap h
  rwa [saddleSwap_saddleSwap] at h2

omit [TopologicalSpace Y] [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y]
  [LocallyConvexSpace ℝ Y] in
/-- The Lagrangian of a closed convex bifunction is an upper closed concave-convex function. -/
theorem upperClosedFn_saddleLagrangian (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu]
    [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx]
    (hF : ConvexBifun F) (hcl : ClosedBifun F) : UpperClosedFn (saddleLagrangian Bu F) := by
  have h : LowerClosedFn (saddleSwap (saddleLagrangian Bu F)) := by
    rw [saddleSwap_saddleLagrangian]
    exact lowerClosedFn_bracket Bx (-Bu) (convexBifun_flipBifun hF) (closedBifun_flipBifun hcl)
  have h3 := lowerClosedFn_iff_upperClosedFn_saddleSwap.1 h
  rwa [saddleSwap_saddleSwap] at h3

omit [TopologicalSpace Y] [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y]
  [LocallyConvexSpace ℝ Y] in
/-- Every upper closed concave-convex function on `V × X` is the Lagrangian of one and only one
closed convex bifunction from `U` to `X`. -/
theorem exists_unique_closedBifun_saddleLagrangian_eq (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bx] (hL : ConcaveConvexFn L) (huc : UpperClosedFn L) :
    ∃! G : Bifun U X, ConvexBifun G ∧ ClosedBifun G ∧ saddleLagrangian Bu G = L := by
  have hsw : ConcaveConvexFn (saddleSwap L) := concaveConvexFn_saddleSwap hL
  have hlc : LowerClosedFn (saddleSwap L) := by
    refine lowerClosedFn_iff_upperClosedFn_saddleSwap.2 ?_
    rwa [saddleSwap_saddleSwap]
  obtain ⟨H, ⟨hHconv, hHcl, hHbr⟩, huniq⟩ :=
    exists_unique_convexBifun_bracket_eq Bx (-Bu) hsw hlc
  refine ⟨flipBifun H, ⟨convexBifun_flipBifun hHconv, closedBifun_flipBifun hHcl, ?_⟩, ?_⟩
  · refine saddleSwap_injective ?_
    rw [saddleSwap_saddleLagrangian, flipBifun_flipBifun]
    exact hHbr
  · rintro G ⟨hGconv, hGcl, hGL⟩
    have hbr : (fun q : X × V => bracket (-Bu) (flipBifun G) q.1 q.2) = saddleSwap L := by
      rw [← saddleSwap_saddleLagrangian, hGL]
    have hHG := huniq (flipBifun G)
      ⟨convexBifun_flipBifun hGconv, closedBifun_flipBifun hGcl, hbr⟩
    rw [← hHG, flipBifun_flipBifun]

end LagrangianUpperClosed

/-! ## Conjugate saddle-functions -/

/-! ### The inverse of a bifunction -/

section InverseBifun

variable {U X : Type*}

/-- The inverse is `flipBifun` composed with a change of sign. -/
theorem inverseBifun_eq_flipBifun_neg (F : Bifun U X) :
    inverseBifun F = flipBifun fun u x => -(F u x) := rfl

end InverseBifun

section InverseBifunConvex

variable {U X : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]
  {G : Bifun U X}

/-- **The inverse of a concave bifunction is convex.** -/
theorem convexBifun_inverseBifun (hG : ConcaveBifun G) : ConvexBifun (inverseBifun G) := by
  have h : ConvexBifun fun u x => -(G u x) := hG.convexFn_neg
  exact convexBifun_flipBifun h

end InverseBifunConvex

section InverseBifunClosed

variable {U X : Type*} [TopologicalSpace U] [AddCommGroup U] [IsTopologicalAddGroup U]
  [TopologicalSpace X] [AddCommGroup X] [IsTopologicalAddGroup X] {G : Bifun U X}

/-- **The inverse of a concave-closed bifunction is closed.** -/
theorem closedBifun_inverseBifun (hG : ClosedConcaveFn (graphFn G)) :
    ClosedBifun (inverseBifun G) := by
  have h : ClosedBifun fun u x => -(G u x) := closedConcaveFn_iff.1 hG
  exact closedBifun_flipBifun h

end InverseBifunClosed

/-! ### The concave conjugate sees only the concave closure -/

section ConcaveConjClosure

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace E] [IsTopologicalAddGroup E] {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} [IsContinuousPairing B]

/-- **The concave conjugate sees only the concave closure**: `(cl g)* = g*`. This is `conj_clFn`
read through the sign dictionary, and it is what makes the lower conjugate independent of the
representative of the equivalence class. -/
theorem concaveConj_clConcave (g : E → EReal) :
    concaveConj B (clConcave g) = concaveConj B g := by
  funext y
  rw [concaveConj_eq_neg_conj_neg, concaveConj_eq_neg_conj_neg]
  congr 1
  have h : (fun x => -(clConcave g x)) = clFn fun z => -(g z) := funext fun x => neg_clConcave g x
  rw [h, conj_clFn]

end ConcaveConjClosure

/-! ### The lower and upper conjugates of a saddle-function -/

section ConjugateSaddle

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]

/-- **The lower conjugate `K̲*`** of a saddle-function:
`K̲* (u*, x) = ⨆ y, ⨅ u, {⟨u, u*⟩ + ⟨x, y⟩ - K (u, y)}`. -/
noncomputable def lowerConjSaddle (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (K : U × Y → EReal) : V × X → EReal :=
  fun q => ⨆ y, ⨅ u, (((Bu u q.1 + Bx q.2 y : ℝ) : EReal) - K (u, y))

/-- **The upper conjugate `K̄*`** of a saddle-function:
`K̄* (u*, x) = ⨅ u, ⨆ y, {⟨u, u*⟩ + ⟨x, y⟩ - K (u, y)}`. -/
noncomputable def upperConjSaddle (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (K : U × Y → EReal) : V × X → EReal :=
  fun q => ⨅ u, ⨆ y, (((Bu u q.1 + Bx q.2 y : ℝ) : EReal) - K (u, y))

theorem lowerConjSaddle_apply (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (K : U × Y → EReal) (q : V × X) :
    lowerConjSaddle Bu Bx K q = ⨆ y, ⨅ u, (((Bu u q.1 + Bx q.2 y : ℝ) : EReal) - K (u, y)) := rfl

theorem upperConjSaddle_apply (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (K : U × Y → EReal) (q : V × X) :
    upperConjSaddle Bu Bx K q = ⨅ u, ⨆ y, (((Bu u q.1 + Bx q.2 y : ℝ) : EReal) - K (u, y)) := rfl

/-- The lower conjugate never exceeds the upper one, `K̲* ≤ K̄*`, by `sup inf ≤ inf sup`. -/
theorem lowerConjSaddle_le_upperConjSaddle (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (K : U × Y → EReal) :
    lowerConjSaddle Bu Bx K ≤ upperConjSaddle Bu Bx K := fun q =>
  maximin_le_minimax fun p : Y × U => (((Bu p.2 q.1 + Bx q.2 p.1 : ℝ) : EReal) - K (p.2, p.1))

/-- The equivalence class `Ω (F)` of saddle-functions attached to a convex bifunction: the
concave-convex functions squeezed between the two brackets of `F`. -/
noncomputable def bifunSaddleClass (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (F : Bifun U X) : Set (U × Y → EReal) :=
  saddleClass (fun p : U × Y => bracket Bx F p.1 p.2)
    (fun p : U × Y => concaveBracket Bu (adjointBifun Bu Bx F) p.1 p.2)

theorem mem_bifunSaddleClass {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ} {F : Bifun U X}
    {K : U × Y → EReal} : K ∈ bifunSaddleClass Bu Bx F ↔
      ((fun p : U × Y => bracket Bx F p.1 p.2) ≤ K ∧
        K ≤ fun p : U × Y => concaveBracket Bu (adjointBifun Bu Bx F) p.1 p.2) := Iff.rfl

end ConjugateSaddle

/-! ### The saddle-value is a value of the conjugate at the origin -/

section ConjugateSaddleZero

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]

/-- `inf sup K = -K̲* (0, 0)`: the `inf sup` is a value of the lower conjugate at the origin. -/
theorem minimax_eq_neg_lowerConjSaddle_zero (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (K : U × Y → EReal) :
    minimax K = -(lowerConjSaddle Bu Bx K 0) := by
  have h : lowerConjSaddle Bu Bx K 0 = -(minimax K) := by
    rw [lowerConjSaddle_apply, minimax_apply, EReal.neg_iInf]
    refine iSup_congr fun y => ?_
    rw [EReal.neg_iSup]
    refine iInf_congr fun u => ?_
    have h0 : (Bu u (0 : V × X).1 + Bx (0 : V × X).2 y : ℝ) = 0 := by simp
    rw [h0, _root_.EReal.coe_zero]
    change (0 : EReal) + -(K (u, y)) = -(K (u, y))
    rw [zero_add]
  rw [h, neg_neg]

/-- `sup inf K = -K̄* (0, 0)`: the `sup inf` is a value of the upper conjugate at the origin. -/
theorem maximin_eq_neg_upperConjSaddle_zero (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (K : U × Y → EReal) :
    maximin K = -(upperConjSaddle Bu Bx K 0) := by
  have h : upperConjSaddle Bu Bx K 0 = -(maximin K) := by
    rw [upperConjSaddle_apply, maximin_apply, EReal.neg_iSup]
    refine iInf_congr fun u => ?_
    rw [EReal.neg_iInf]
    refine iSup_congr fun y => ?_
    have h0 : (Bu u (0 : V × X).1 + Bx (0 : V × X).2 y : ℝ) = 0 := by simp
    rw [h0, _root_.EReal.coe_zero]
    change (0 : EReal) + -(K (u, y)) = -(K (u, y))
    rw [zero_add]
  rw [h, neg_neg]

/-- The saddle-value of `K` exists exactly when the two conjugates agree at the origin. This is the
reduction of minimax theory to the position of the origin relative to the effective domain of the
conjugate class. -/
theorem hasSaddleValue_iff_conjSaddle_zero_eq (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (K : U × Y → EReal) :
    HasSaddleValue K ↔ upperConjSaddle Bu Bx K 0 = lowerConjSaddle Bu Bx K 0 := by
  rw [hasSaddleValue_iff, maximin_eq_neg_upperConjSaddle_zero Bu Bx K,
    minimax_eq_neg_lowerConjSaddle_zero Bu Bx K, _root_.neg_inj]

end ConjugateSaddleZero

/-! ### The structure of the inverse adjoint -/

section AdjointStructure

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]

theorem concaveFn_adjointBifun_apply (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (F : Bifun U X) (y : Y) : ConcaveFn (adjointBifun Bu Bx F y) :=
  concaveFn_iff_convexFn_neg.2 ((convexBifun_neg_adjointBifun Bu Bx F).convexFn_apply y)

/-- **The inverse of the adjoint is a convex bifunction.** Rockafellar writes it `F_*^*`, using the
commutation `(F_*)^* = (F^*)_*`; taking `(F^*)_*` as the definition makes that commutation a
triviality, and this is the bifunction the lower conjugate turns out to be the bracket of. -/
theorem convexBifun_inverseBifun_adjointBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (F : Bifun U X) :
    ConvexBifun (inverseBifun (adjointBifun Bu Bx F)) :=
  convexBifun_flipBifun (convexBifun_neg_adjointBifun Bu Bx F)

end AdjointStructure

section AdjointClosed

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace V] [IsTopologicalAddGroup V] [TopologicalSpace Y] [IsTopologicalAddGroup Y]

/-- Each slice of the negated adjoint is a closed convex function: the adjoint of a bifunction is
closed, read slice by slice. -/
theorem closedFn_neg_adjointBifun_apply (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsContinuousPairing Bu.flip]
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsContinuousPairing Bx.flip] (F : Bifun U X) (y : Y) :
    ClosedFn fun v => -(adjointBifun Bu Bx F y v) := by
  have := isContinuousPairing_prodPairing_flip Bu Bx
  have h : ClosedBifun fun y v => -(adjointBifun Bu Bx F y v) := closedBifun_neg_adjointBifun
  exact h.imageClosedBifun y

/-- **The inverse of the adjoint is a closed bifunction.** -/
theorem closedBifun_inverseBifun_adjointBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsContinuousPairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsContinuousPairing Bx.flip]
    (F : Bifun U X) : ClosedBifun (inverseBifun (adjointBifun Bu Bx F)) := by
  have := isContinuousPairing_prodPairing_flip Bu Bx
  exact closedBifun_flipBifun closedBifun_neg_adjointBifun

end AdjointClosed

/-! ### The two conjugates of a member of `Ω (F)` -/

section ClassConjugates

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [LocallyConvexSpace ℝ V]
  [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X]
  [TopologicalSpace Y] [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y] [LocallyConvexSpace ℝ Y]
  {F : Bifun U X} {K : U × Y → EReal}

omit [AddCommGroup U] [Module ℝ U] [TopologicalSpace U] [IsTopologicalAddGroup U]
  [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U] [TopologicalSpace X] [IsTopologicalAddGroup X]
  [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X] [TopologicalSpace Y] [IsTopologicalAddGroup Y]
  [ContinuousSMul ℝ Y] [LocallyConvexSpace ℝ Y] in
/-- `bifunOfSaddle` is antitone: it is a conjugate in disguise. -/
theorem bifunOfSaddle_antitone (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) {K L : U × Y → EReal} (h : K ≤ L) :
    bifunOfSaddle Bx L ≤ bifunOfSaddle Bx K :=
  fun u x => conj_antitone Bx.flip (fun y => h (u, y)) x

omit [AddCommGroup U] [Module ℝ U] [TopologicalSpace U] [IsTopologicalAddGroup U]
  [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U] [TopologicalSpace X] [IsTopologicalAddGroup X]
  [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X] [ContinuousSMul ℝ Y]
  [LocallyConvexSpace ℝ Y] in
/-- **The convex bifunction attached to a saddle-function sees only its `cl₂` closure.** This is
`conj_clFn` on each slice. -/
theorem bifunOfSaddle_partialCl₂ (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx.flip]
    (K : U × Y → EReal) : bifunOfSaddle Bx (partialCl₂ K) = bifunOfSaddle Bx K :=
  funext fun u => conj_clFn (B := Bx.flip) fun y => K (u, y)

omit [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
  [LocallyConvexSpace ℝ V] in
/-- **Every member of the class `Ω (F)` has the same associated bifunction, namely `F`.** The two
brackets have equal `bifunOfSaddle` — one is the `cl₂` of the other, and `bifunOfSaddle` sees only
`cl₂` — so the sandwich collapses. This is the step that gives the upper conjugate. -/
theorem bifunOfSaddle_eq_of_mem_bifunSaddleClass (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx]
    [IsCompatiblePairing Bx.flip] (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (hK : K ∈ bifunSaddleClass Bu Bx F) : bifunOfSaddle Bx K = F := by
  obtain ⟨hlow, hup⟩ := hK
  have hbase : bifunOfSaddle Bx (fun p : U × Y => bracket Bx F p.1 p.2) = F := by
    funext u
    have h : bifunOfSaddle Bx (fun p : U × Y => bracket Bx F p.1 p.2) u
        = conj Bx.flip (bracket Bx F u) := rfl
    rw [h, ← clFn_eq_conj_bracket hF u]
    exact hcl.imageClosedBifun u
  have h2 : partialCl₂ (fun p : U × Y => concaveBracket Bu (adjointBifun Bu Bx F) p.1 p.2)
      = fun p : U × Y => bracket Bx F p.1 p.2 :=
    partialCl₂_concaveBracket_adjoint Bu Bx hF hcl
  have hupper : bifunOfSaddle Bx
      (fun p : U × Y => concaveBracket Bu (adjointBifun Bu Bx F) p.1 p.2) = F :=
    calc bifunOfSaddle Bx (fun p : U × Y => concaveBracket Bu (adjointBifun Bu Bx F) p.1 p.2)
        = bifunOfSaddle Bx
            (partialCl₂ fun p : U × Y => concaveBracket Bu (adjointBifun Bu Bx F) p.1 p.2) :=
          (bifunOfSaddle_partialCl₂ Bx _).symm
      _ = bifunOfSaddle Bx (fun p : U × Y => bracket Bx F p.1 p.2) := by rw [h2]
      _ = F := hbase
  refine le_antisymm ?_ ?_
  · rw [← hbase]
    exact bifunOfSaddle_antitone Bx hlow
  · rw [← hupper]
    exact bifunOfSaddle_antitone Bx hup

omit [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  [LocallyConvexSpace ℝ X] [ContinuousSMul ℝ Y] [LocallyConvexSpace ℝ Y] in
/-- **The concave conjugate of a slice of `K` is a slice of the adjoint `F*`**, for every `K` in the
class `Ω (F)`: the concave conjugate sees only `cl₁`, and `cl₁` of the lower bracket is the upper
bracket. This is the step that gives the lower conjugate. -/
theorem concaveConj_slice_eq_adjointBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu]
    [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx.flip]
    (hF : ConvexBifun F) (hK : K ∈ bifunSaddleClass Bu Bx F) (y : Y) :
    concaveConj Bu (fun u => K (u, y)) = adjointBifun Bu Bx F y := by
  obtain ⟨hlow, hup⟩ := hK
  have hcl1 : (fun u => concaveBracket Bu (adjointBifun Bu Bx F) u y)
      = clConcave fun u => bracket Bx F u y := by
    funext u
    have h1 : partialCl₁ (fun p : U × Y => bracket Bx F p.1 p.2) (u, y)
        = concaveBracket Bu (adjointBifun Bu Bx F) u y :=
      congrFun (partialCl₁_bracket Bu Bx hF) (u, y)
    rw [← h1]
    exact congrFun (partialCl₁_slice (fun p : U × Y => bracket Bx F p.1 p.2) y) u
  have hends : concaveConj Bu (fun u => concaveBracket Bu (adjointBifun Bu Bx F) u y)
      = concaveConj Bu fun u => bracket Bx F u y := by
    rw [hcl1, concaveConj_clConcave]
  have hA : concaveConj Bu (fun u => concaveBracket Bu (adjointBifun Bu Bx F) u y)
      ≤ concaveConj Bu fun u => K (u, y) :=
    concaveConj_antitone Bu fun u => hup (u, y)
  have hB : concaveConj Bu (fun u => K (u, y))
      ≤ concaveConj Bu fun u => bracket Bx F u y :=
    concaveConj_antitone Bu fun u => hlow (u, y)
  have hKeq : concaveConj Bu (fun u => K (u, y))
      = concaveConj Bu fun u => concaveBracket Bu (adjointBifun Bu Bx F) u y :=
    le_antisymm (by rw [hends]; exact hB) hA
  rw [hKeq, concaveBracket_eq_concaveConj Bu (adjointBifun Bu Bx F) y]
  exact biconcaveConj_eq_self (B := Bu.flip) (concaveFn_adjointBifun_apply Bu Bx F y)
    (closedFn_neg_adjointBifun_apply Bu Bx F y)

omit [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
  [LocallyConvexSpace ℝ V] in
/-- The *upper* conjugate of any `K` in the class `Ω (F)` of a closed convex bifunction `F` is the
Lagrangian of `F`, `K̄* (u*, x) = ⟨u*, F_* x⟩ = ⨅ u, {⟨u, u*⟩ + (Fu)(x)}`. In particular it does
not depend on the representative. -/
theorem upperConjSaddle_eq_saddleLagrangian (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu]
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip]
    (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ bifunSaddleClass Bu Bx F) :
    upperConjSaddle Bu Bx K = saddleLagrangian Bu F := by
  have hB := bifunOfSaddle_eq_of_mem_bifunSaddleClass Bu Bx hF hcl hK
  funext q
  rw [upperConjSaddle_apply, saddleLagrangian_apply, lagrangian_apply]
  refine iInf_congr fun u => ?_
  have h1 : ∀ y, (((Bu u q.1 + Bx q.2 y : ℝ) : EReal) - K (u, y))
      = (((Bx q.2 y : ℝ) : EReal) - K (u, y)) + ((Bu u q.1 : ℝ) : EReal) := by
    intro y
    rw [_root_.EReal.coe_add]
    simp only [sub_eq_add_neg]
    rw [add_assoc, add_comm]
  simp only [h1]
  rw [← EReal.iSup_add_coe]
  have h2 : (⨆ y, (((Bx q.2 y : ℝ) : EReal) - K (u, y))) = F u q.2 := by
    rw [← congrFun (congrFun hB u) q.2, bifunOfSaddle_apply]
  rw [h2, add_comm]

omit [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  [LocallyConvexSpace ℝ X] [ContinuousSMul ℝ Y] [LocallyConvexSpace ℝ Y] in
/-- The *lower* conjugate of any `K` in the class `Ω (F)` is the bracket of the inverse adjoint,
`K̲* (u*, x) = ⟨F_*^* u*, x⟩`; like the upper conjugate it depends only on the class. -/
theorem lowerConjSaddle_eq_bracket_inverseBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bx.flip] (hF : ConvexBifun F) (hK : K ∈ bifunSaddleClass Bu Bx F) :
    lowerConjSaddle Bu Bx K
      = fun q : V × X => bracket Bx.flip (inverseBifun (adjointBifun Bu Bx F)) q.1 q.2 := by
  funext q
  rw [lowerConjSaddle_apply, bracket_apply]
  refine iSup_congr fun y => ?_
  have h1 : ∀ u, (((Bu u q.1 + Bx q.2 y : ℝ) : EReal) - K (u, y))
      = (((Bu u q.1 : ℝ) : EReal) - K (u, y)) + ((Bx q.2 y : ℝ) : EReal) := by
    intro u
    rw [_root_.EReal.coe_add]
    simp only [sub_eq_add_neg]
    rw [add_right_comm]
  simp only [h1]
  rw [← EReal.iInf_add_coe]
  have h2 : (⨅ u, (((Bu u q.1 : ℝ) : EReal) - K (u, y))) = adjointBifun Bu Bx F y q.1 :=
    congrFun (concaveConj_slice_eq_adjointBifun Bu Bx hF hK y) q.1
  rw [h2]
  have h3 : ((Bx.flip y q.2 : ℝ) : EReal) - inverseBifun (adjointBifun Bu Bx F) q.1 y
      = ((Bx q.2 y : ℝ) : EReal) + adjointBifun Bu Bx F y q.1 := by
    rw [inverseBifun_apply]
    simp only [sub_eq_add_neg, neg_neg]
    rfl
  rw [h3, add_comm]

/-! ### The conjugates are again concave-convex, and closed -/

omit [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
  [LocallyConvexSpace ℝ V] in
/-- The upper conjugate of a member of `Ω (F)` is a concave-convex function. -/
theorem concaveConvexFn_upperConjSaddle (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu]
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip]
    (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ bifunSaddleClass Bu Bx F) :
    ConcaveConvexFn (upperConjSaddle Bu Bx K) := by
  rw [upperConjSaddle_eq_saddleLagrangian Bu Bx hF hcl hK]
  exact concaveConvexFn_saddleLagrangian Bu hF

/-- The upper conjugate of a member of `Ω (F)` is *upper closed*: it is a Lagrangian, and the
Lagrangians are exactly the upper closed concave-convex functions. -/
theorem upperClosedFn_upperConjSaddle (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu]
    [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx]
    [IsCompatiblePairing Bx.flip] (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (hK : K ∈ bifunSaddleClass Bu Bx F) : UpperClosedFn (upperConjSaddle Bu Bx K) := by
  rw [upperConjSaddle_eq_saddleLagrangian Bu Bx hF hcl hK]
  exact upperClosedFn_saddleLagrangian Bu Bx hF hcl

omit [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  [LocallyConvexSpace ℝ X] [ContinuousSMul ℝ Y] [LocallyConvexSpace ℝ Y] in
/-- The lower conjugate of a member of `Ω (F)` is a concave-convex function. -/
theorem concaveConvexFn_lowerConjSaddle (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu]
    [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx.flip]
    (hF : ConvexBifun F) (hK : K ∈ bifunSaddleClass Bu Bx F) :
    ConcaveConvexFn (lowerConjSaddle Bu Bx K) := by
  rw [lowerConjSaddle_eq_bracket_inverseBifun Bu Bx hF hK]
  exact concaveConvexFn_bracket (convexBifun_inverseBifun_adjointBifun Bu Bx F) Bx.flip

/-- The lower conjugate of a member of `Ω (F)` is *lower closed*: it is the bracket of the closed
convex bifunction `F_*^*`. -/
theorem lowerClosedFn_lowerConjSaddle (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu]
    [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx]
    [IsCompatiblePairing Bx.flip] (hF : ConvexBifun F) (hK : K ∈ bifunSaddleClass Bu Bx F) :
    LowerClosedFn (lowerConjSaddle Bu Bx K) := by
  rw [lowerConjSaddle_eq_bracket_inverseBifun Bu Bx hF hK]
  exact lowerClosedFn_bracket Bu.flip Bx.flip (convexBifun_inverseBifun_adjointBifun Bu Bx F)
    (closedBifun_inverseBifun_adjointBifun Bu Bx F)

end ClassConjugates

end ConvexAnalysis
