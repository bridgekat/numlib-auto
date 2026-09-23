import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Semicontinuity.Basic
import Numlib.Analysis.Convex.Homogeneous
import Numlib.Analysis.Convex.Indicator
import Numlib.Analysis.Convex.Operations.Epi
import Numlib.Analysis.Convex.Separation

/-!
# Closures of convex functions

Two operations on functions `f : E → EReal` over a real topological vector space: the lower
semicontinuous hull `lscHull f`, whose epigraph is `closure (epi f)`, and the *closure* `convexCl f`
of a convex function, which is that hull except that it is flattened to the constant `⊥` when the
hull takes the value `⊥` anywhere.

## Main definitions

* `lscHull f` — the lower semicontinuous hull, `ofEpi (closure (epi f))`; `uscHull g`, the upper
  semicontinuous hull `-(lscHull (-g))`.
* `convexCl f` — the closure of a convex function.
* `ClosedConvex f` — `f` is closed, i.e. `convexCl f = f`.
* `concaveCl g`, `ClosedConcave g` — the **concave closure** `-(cl (-g))`, which Rockafellar also
  writes `cl g`, and the functions fixed by it; it is `uscHull g` outside the exceptional branch.
* `ClosedProperConvexFn f` — closed, proper *and* convex, bundled; the standing hypothesis of the
  duality theory, and the class `convexConjEquiv` and `supportEquiv` are bijections between.
  `ClosedProperConcaveFn g` is its concave twin.
* `lscHullClosure`, `convexClClosure` — both operations as `ClosureOperator`s on `(E → EReal)ᵒᵈ`.

## Main results

* `lowerSemicontinuous_iff_isClosed_epi`, `lowerSemicontinuous_iff_isClosed_le` —
  lower semicontinuity, closed sublevel sets and a closed epigraph coincide.
* `epi_lscHull` — `epi (lscHull f) = closure (epi f)`, unconditionally; the workhorse of the file.
* `isGreatest_lscHull` — `lscHull f` is the greatest lower semicontinuous minorant of `f`.
* `closedConvex_iff` — `f` is closed exactly when it is the constant `⊥`, or lower semicontinuous
  and never `⊥`.
* `iInf_convexCl_eq_iInf` — `f` and `cl f` have the same infimum.
* `ConvexFn.eq_bot_or_eq_top` — a lower semicontinuous improper convex function has no finite
  values. This replaces the relative-interior dichotomy outside finite dimensions.
* `exists_affine_le_of_closed_proper` — a closed proper convex function on a locally convex space
  has a continuous affine minorant; the keystone of Fenchel–Moreau.
* `tendsto_lscHull_along_segment`, `tendsto_along_segment_of_closed_proper` — the closure as a
  limit along a segment, with `interior (epi f)` in place of `ri (epi f)`.
* `lscHull_le_setOf` — `{x | (cl f) x ≤ α} = ⋂_{μ > α} cl {f ≤ μ}`, the level sets of the closure,
  in the part that does not need relative interiors.
* `lscHull_eq_liminf`, `convexCl_eq_liminf_or` — the hull and the closure as `liminf f (𝓝 x)`.
* `posHomogeneous_lscHull`, `posHomogeneous_convexCl` — both hulls preserve positive homogeneity.
* `closedProperConvexFn_coe_affineMap` — a *continuous* affine function is closed proper convex.

## Implementation notes

`convexCl` branches on `lscHull f`, not on `f` as Rockafellar does. The two agree for convex `f` on
`ℝⁿ` but not in general, and branching on `f` would make Fenchel–Moreau
false: a discontinuous linear functional `g` on an infinite-dimensional space is convex, finite and
proper, yet its kernel is dense, so `lscHull g ≡ ⊥` and `g` has no continuous affine minorant at
all. Branching on the hull is the standard Γ-regularization and makes `f** = convexCl f`
unconditional; the price is that `ProperConvex f → ProperConvex (convexCl f)` is finite-dimensional
and appears as `ConvexFn.properConvex_convexCl` in `Numlib/Analysis/Convex/RelativeInterior.lean`,
together with the relative-interior dichotomy itself.

## References

* [rockafellar1970convex] §7.
-/

open Set Filter Topology

namespace ConvexAnalysis

/-! ### Lower semicontinuity -/

section Semicontinuity

variable {E : Type*} [TopologicalSpace E] {f g : E → EReal}

/-- **A function is lower semicontinuous exactly when its epigraph is closed.** -/
theorem lowerSemicontinuous_iff_isClosed_epi : LowerSemicontinuous f ↔ IsClosed (epi f) := by
  constructor
  · intro hf
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    rintro ⟨x, μ⟩ hp
    obtain ⟨r, hμr, hrf⟩ := EReal.lt_iff_exists_real_btwn.1 (not_le.1 hp)
    refine mem_of_superset
      (prod_mem_nhds (hf x (r : EReal) hrf) (Iio_mem_nhds (by exact_mod_cast hμr))) ?_
    rintro ⟨z, ν⟩ ⟨hz, hν⟩
    have hz' : (r : EReal) < f z := hz
    have hν' : ν < r := hν
    exact not_le.2 (lt_trans (by exact_mod_cast hν') hz')
  · intro hF x y hy
    obtain ⟨r, hyr, hrf⟩ := EReal.lt_iff_exists_real_btwn.1 hy
    have hclosed : IsClosed {z : E | f z ≤ (r : EReal)} := by
      have hpre : {z : E | f z ≤ (r : EReal)} = (fun z : E => (z, r)) ⁻¹' epi f := rfl
      rw [hpre]
      exact hF.preimage (continuous_id.prodMk continuous_const)
    filter_upwards [hclosed.isOpen_compl.mem_nhds (not_le.2 hrf)] with z hz
    exact hyr.trans (not_le.1 hz)

/-- **A function is lower semicontinuous exactly when every sublevel set `{x | f x ≤ α}` with `α`
real is closed.** -/
theorem lowerSemicontinuous_iff_isClosed_le :
    LowerSemicontinuous f ↔ ∀ α : ℝ, IsClosed {x | f x ≤ (α : EReal)} := by
  constructor
  · intro hf α
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro x hx
    filter_upwards [hf x (α : EReal) (not_le.1 hx)] with z hz using not_le.2 hz
  · intro h x y hy
    obtain ⟨r, hyr, hrf⟩ := EReal.lt_iff_exists_real_btwn.1 hy
    filter_upwards [(h r).isOpen_compl.mem_nhds (not_le.2 hrf)] with z hz
    exact hyr.trans (not_le.1 hz)

end Semicontinuity

/-! ### The lower semicontinuous hull and the closure of a convex function -/

section Defs

variable {E : Type*} [TopologicalSpace E] {f g : E → EReal}

/-- The **lower semicontinuous hull** of `f`, the function whose epigraph is the closure of the
epigraph of `f`: the greatest lower semicontinuous minorant of `f`. -/
noncomputable def lscHull (f : E → EReal) : E → EReal := ofEpi (closure (epi f))

/-- The **upper semicontinuous hull** of `g`, the least upper semicontinuous majorant of `g`: the
counterpart of `lscHull` obtained by conjugating it with negation (`uscHull_apply`). -/
noncomputable def uscHull (g : E → EReal) : E → EReal := fun x => -(lscHull (fun z => -(g z)) x)

open Classical in
/-- The **closure** of a convex function: its lower semicontinuous hull, except that if the hull
takes the value `⊥` anywhere then the closure is the constant function `⊥`. Rockafellar branches
on whether `f` itself takes `⊥`, which is equivalent for convex `f` on `ℝⁿ` but not in general; see
the module docstring. -/
noncomputable def convexCl (f : E → EReal) : E → EReal :=
  if ∃ x, lscHull f x = ⊥ then (fun _ => ⊥) else lscHull f

/-- A function is **closed** when it equals its own closure. -/
def ClosedConvex (f : E → EReal) : Prop := convexCl f = f

/-- The **concave closure**: the counterpart of `convexCl` obtained by conjugating it with negation.
Rockafellar writes `cl g` for it too; here it needs a name of its own. -/
noncomputable def concaveCl (g : E → EReal) : E → EReal := fun x => -(convexCl (fun z => -(g z)) x)

/-- `g` is **concave-closed** when it equals its concave closure. -/
def ClosedConcave (g : E → EReal) : Prop := concaveCl g = g

/-! #### The sign dictionary -/

theorem uscHull_apply (g : E → EReal) (x : E) :
    uscHull g x = -(lscHull (fun z => -(g z)) x) := rfl

@[simp] theorem neg_uscHull (g : E → EReal) (x : E) :
    -(uscHull g x) = lscHull (fun z => -(g z)) x := neg_neg _

theorem concaveCl_apply (g : E → EReal) (x : E) :
    concaveCl g x = -(convexCl (fun z => -(g z)) x) := rfl

@[simp] theorem neg_concaveCl (g : E → EReal) (x : E) :
    -(concaveCl g x) = convexCl (fun z => -(g z)) x := neg_neg _

theorem concaveCl_neg (f : E → EReal)
    (x : E) : concaveCl (fun z => -(f z)) x = -(convexCl f x) := by
  rw [concaveCl_apply]
  simp only [neg_neg]

/-- `g` is concave-closed exactly when `-g` is closed. -/
theorem closedConcave_iff_closedConvex_neg : ClosedConcave g ↔ ClosedConvex (fun z => -(g z)) := by
  constructor
  · intro h
    funext x
    rw [← neg_concaveCl g x, h]
  · intro h
    funext x
    rw [concaveCl_apply, congrFun h x, neg_neg]

/-! #### Basic properties of the hulls -/

/-- The defining equation of `convexCl` in the regular branch. -/
theorem convexCl_of_forall_ne_bot (h : ∀ x, lscHull f x ≠ ⊥) : convexCl f = lscHull f := by
  have hc : ¬ ∃ x, lscHull f x = ⊥ := by push Not; exact h
  simp [convexCl, hc]

/-- The defining equation of `convexCl` in the exceptional branch. -/
theorem convexCl_of_exists_eq_bot (h : ∃ x, lscHull f x = ⊥) : convexCl f = fun _ => ⊥ := by
  simp [convexCl, h]

/-- The defining equation of `concaveCl` in the regular branch. -/
theorem concaveCl_of_forall_ne_top (h : ∀ x, uscHull g x ≠ ⊤) : concaveCl g = uscHull g := by
  have h' : ∀ x, lscHull (fun z => -(g z)) x ≠ ⊥ := fun x hx =>
    h x (by rw [uscHull_apply, hx, EReal.neg_bot])
  funext x
  rw [concaveCl_apply, convexCl_of_forall_ne_bot h', uscHull_apply]

/-- The defining equation of `concaveCl` in the exceptional branch. -/
theorem concaveCl_of_exists_eq_top (h : ∃ x, uscHull g x = ⊤) : concaveCl g = fun _ => ⊤ := by
  obtain ⟨x₀, hx₀⟩ := h
  have h' : ∃ x, lscHull (fun z => -(g z)) x = ⊥ := ⟨x₀, by rw [← neg_uscHull, hx₀, EReal.neg_top]⟩
  funext x
  rw [concaveCl_apply, convexCl_of_exists_eq_bot h', EReal.neg_bot]

theorem lscHull_le (f : E → EReal) : lscHull f ≤ f := by
  have h := ofEpi_mono (subset_closure (s := epi f))
  rwa [ofEpi_epi] at h

theorem lscHull_mono (h : f ≤ g) : lscHull f ≤ lscHull g :=
  ofEpi_mono (closure_mono (epi_anti h))

/-- **The universal property, easy half.** A lower semicontinuous minorant of `f` is a minorant of
`lscHull f`, because its epigraph is a closed set containing `epi f`. -/
theorem le_lscHull_of_le (hg : LowerSemicontinuous g) (hgf : g ≤ f) : g ≤ lscHull f :=
  subset_epi_iff_le_ofEpi.1
    (closure_minimal (epi_anti hgf) (lowerSemicontinuous_iff_isClosed_epi.1 hg))

/-- For a lower semicontinuous `g`, being a minorant of `lscHull f` is the same as being a minorant
of `f`. -/
theorem le_lscHull_iff (hg : LowerSemicontinuous g) : g ≤ lscHull f ↔ g ≤ f :=
  ⟨fun h => h.trans (lscHull_le f), le_lscHull_of_le hg⟩

/-- The closure of `f` is a minorant of its lower semicontinuous hull; the two differ only in the
exceptional branch. -/
theorem convexCl_le_lscHull (f : E → EReal) : convexCl f ≤ lscHull f := by
  by_cases h : ∃ x, lscHull f x = ⊥
  · rw [convexCl_of_exists_eq_bot h]
    exact fun _ => bot_le
  · rw [convexCl_of_forall_ne_bot (by push Not at h; exact h)]

theorem convexCl_le (f : E → EReal) : convexCl f ≤ f := (convexCl_le_lscHull f).trans (lscHull_le f)

theorem le_concaveCl (g : E → EReal) : g ≤ concaveCl g := by
  intro x
  rw [← EReal.neg_le_neg_iff, neg_concaveCl]
  exact convexCl_le _ x

/-- A convex closure that reaches `-∞` anywhere is the constant `-∞`. -/
theorem convexCl_eq_bot_of_eq_bot {x₀ : E} (h : f x₀ = ⊥) : convexCl f = fun _ => (⊥ : EReal) := by
  refine convexCl_of_exists_eq_bot ⟨x₀, le_bot_iff.1 ?_⟩
  calc lscHull f x₀ ≤ f x₀ := lscHull_le f x₀
    _ = ⊥ := h

/-- A concave closure that reaches `+∞` anywhere is the constant `+∞`. -/
theorem concaveCl_eq_top_of_eq_top {x₀ : E} (h : g x₀ = ⊤) :
    concaveCl g = fun _ => (⊤ : EReal) := by
  funext x
  rw [concaveCl_apply, convexCl_eq_bot_of_eq_bot (x₀ := x₀) (by simp [h]), EReal.neg_bot]

theorem convexCl_mono (h : f ≤ g) : convexCl f ≤ convexCl g := by
  by_cases hg : ∃ x, lscHull g x = ⊥
  · obtain ⟨x, hx⟩ := hg
    have hf : ∃ z, lscHull f z = ⊥ := ⟨x, le_bot_iff.1 (by rw [← hx]; exact lscHull_mono h x)⟩
    rw [convexCl_of_exists_eq_bot hf, convexCl_of_exists_eq_bot ⟨x, hx⟩]
  · have hg' : ∀ x, lscHull g x ≠ ⊥ := by push Not at hg; exact hg
    rw [convexCl_of_forall_ne_bot (f := g) hg']
    exact (convexCl_le_lscHull f).trans (lscHull_mono h)

theorem concaveCl_mono (h : f ≤ g) : concaveCl f ≤ concaveCl g := by
  intro x
  rw [concaveCl_apply, concaveCl_apply, EReal.neg_le_neg_iff]
  exact convexCl_mono (fun z => EReal.neg_le_neg_iff.2 (h z)) x

end Defs

/-! ### The hull is a hull -/

section Hull

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [IsTopologicalAddGroup E]
  {f g : E → EReal}

/-- **The workhorse of this file.** The epigraph of the lower semicontinuous hull is the closure of
the epigraph, with no hypothesis on `f`: the closure of an epigraph is again an epigraph. -/
@[simp] theorem epi_lscHull (f : E → EReal) : epi (lscHull f) = closure (epi f) :=
  epi_ofEpi (IsEpiLike.closure (isEpiLike_epi f))

theorem lowerSemicontinuous_lscHull (f : E → EReal) : LowerSemicontinuous (lscHull f) :=
  lowerSemicontinuous_iff_isClosed_epi.2 (by rw [epi_lscHull]; exact isClosed_closure)

/-- **The universal property.** `lscHull f` is the greatest lower semicontinuous minorant of
`f`. -/
theorem isGreatest_lscHull (f : E → EReal) :
    IsGreatest {g : E → EReal | LowerSemicontinuous g ∧ g ≤ f} (lscHull f) :=
  ⟨⟨lowerSemicontinuous_lscHull f, lscHull_le f⟩, fun _ hg => le_lscHull_of_le hg.1 hg.2⟩

theorem lscHull_idem (f : E → EReal) : lscHull (lscHull f) = lscHull f :=
  epi_injective (by rw [epi_lscHull, epi_lscHull, closure_closure])

/-- A function equals its lower semicontinuous hull exactly when it is lower semicontinuous. -/
theorem lscHull_eq_self_iff : lscHull f = f ↔ LowerSemicontinuous f :=
  ⟨fun h => h ▸ lowerSemicontinuous_lscHull f,
    fun h => le_antisymm (lscHull_le f) (le_lscHull_of_le h le_rfl)⟩

omit [TopologicalSpace E] [AddCommGroup E] [IsTopologicalAddGroup E] in
@[simp] theorem epi_const_bot : epi (fun _ : E => (⊥ : EReal)) = univ := by
  ext p; simp [epi]

omit [AddCommGroup E] [IsTopologicalAddGroup E] in
@[simp] theorem lscHull_const_bot : lscHull (fun _ : E => (⊥ : EReal)) = fun _ => ⊥ := by
  simp only [lscHull, epi_const_bot, closure_univ, ofEpi_univ]
  rfl

omit [IsTopologicalAddGroup E] in
@[simp] theorem convexCl_const_bot : convexCl (fun _ : E => (⊥ : EReal)) = fun _ => ⊥ :=
  convexCl_of_exists_eq_bot ⟨0, by rw [lscHull_const_bot]⟩

theorem convexCl_idem (f : E → EReal) : convexCl (convexCl f) = convexCl f := by
  by_cases h : ∃ x, lscHull f x = ⊥
  · rw [convexCl_of_exists_eq_bot h, convexCl_const_bot]
  · have h' : ∀ x, lscHull f x ≠ ⊥ := by push Not at h; exact h
    have h'' : ∀ x, lscHull (lscHull f) x ≠ ⊥ := by rw [lscHull_idem]; exact h'
    rw [convexCl_of_forall_ne_bot h', convexCl_of_forall_ne_bot h'', lscHull_idem]

theorem closedConvex_convexCl (f : E → EReal) : ClosedConvex (convexCl f) := convexCl_idem f

theorem closedConcave_concaveCl (g : E → EReal) : ClosedConcave (concaveCl g) := by
  rw [closedConcave_iff_closedConvex_neg]
  simpa only [neg_concaveCl] using closedConvex_convexCl (fun z => -(g z))

theorem concaveCl_idem (g : E → EReal) : concaveCl (concaveCl g) = concaveCl g :=
  closedConcave_concaveCl g

/-- **What closedness means.** A function is closed exactly when it is the constant `⊥`, or is
lower semicontinuous and never takes the value `⊥`. -/
theorem closedConvex_iff :
    ClosedConvex f ↔ f = (fun _ => ⊥) ∨ (LowerSemicontinuous f ∧ ∀ x, f x ≠ ⊥) := by
  constructor
  · intro hc
    by_cases h : ∃ x, lscHull f x = ⊥
    · exact Or.inl (by rw [← hc, convexCl_of_exists_eq_bot h])
    · have h' : ∀ x, lscHull f x ≠ ⊥ := by push Not at h; exact h
      have hs : lscHull f = f := by rw [← convexCl_of_forall_ne_bot h']; exact hc
      exact Or.inr ⟨lscHull_eq_self_iff.1 hs, fun x => by rw [← hs]; exact h' x⟩
  · rintro (rfl | ⟨hlsc, hne⟩)
    · exact convexCl_const_bot
    · have hs : lscHull f = f := lscHull_eq_self_iff.2 hlsc
      have h' : ∀ x, lscHull f x ≠ ⊥ := fun x => by rw [hs]; exact hne x
      exact (convexCl_of_forall_ne_bot h').trans hs

/-- For a function that never takes the value `⊥` — in particular for a proper convex function —
**closedness is exactly lower semicontinuity**. -/
theorem closedConvex_iff_lowerSemicontinuous (h : ∀ x, f x ≠ ⊥) :
    ClosedConvex f ↔ LowerSemicontinuous f := by
  rw [closedConvex_iff]
  refine ⟨?_, fun hl => Or.inr ⟨hl, h⟩⟩
  rintro (rfl | ⟨hl, -⟩)
  · exact absurd rfl (h 0)
  · exact hl

theorem ClosedConvex.lowerSemicontinuous (hc : ClosedConvex f) : LowerSemicontinuous f := by
  rcases closedConvex_iff.1 hc with rfl | ⟨hl, -⟩
  · exact lowerSemicontinuous_const
  · exact hl

/-- **The only closed improper convex functions are the constant functions `+∞` and `−∞`.**
Convexity is not needed for this direction. -/
theorem eq_const_of_closedConvex_of_not_properConvex (hc : ClosedConvex f) (hp : ¬ ProperConvex f) :
    f = (fun _ => ⊥) ∨ f = fun _ => ⊤ := by
  rcases closedConvex_iff.1 hc with h | ⟨-, hne⟩
  · exact Or.inl h
  · exact Or.inr (funext fun x => top_le_iff.1 (not_lt.1 fun hx => hp ⟨⟨x, hx⟩, hne⟩))

theorem closedConvex_const_top : ClosedConvex (fun _ : E => (⊤ : EReal)) :=
  closedConvex_iff.2 (Or.inr ⟨lowerSemicontinuous_const, fun _ => by simp⟩)

omit [IsTopologicalAddGroup E] in
theorem closedConvex_const_bot : ClosedConvex (fun _ : E => (⊥ : EReal)) := convexCl_const_bot

/-- The constant `+∞` is its own closure. -/
@[simp] theorem convexCl_const_top : convexCl (fun _ : E => (⊤ : EReal)) = fun _ => ⊤ :=
  closedConvex_const_top

/-- The constant `-∞` is its own concave closure. -/
@[simp] theorem concaveCl_const_bot : concaveCl (fun _ : E => (⊥ : EReal)) = fun _ => ⊥ := by
  funext x
  simp [concaveCl_apply]

/-! ### Infima, effective domains and level sets -/

omit [AddCommGroup E] [IsTopologicalAddGroup E] in
/-- **`f` and its lower semicontinuous hull have the same infimum.** A constant function is
lower semicontinuous, so `⨅ x, f x` is already a minorant of `lscHull f`. -/
theorem iInf_lscHull_eq_iInf (f : E → EReal) : ⨅ x, lscHull f x = ⨅ x, f x :=
  le_antisymm (iInf_mono fun x => lscHull_le f x)
    (le_iInf fun x =>
      le_lscHull_of_le (g := fun _ => ⨅ y, f y) lowerSemicontinuous_const (fun y => iInf_le f y) x)

omit [IsTopologicalAddGroup E] in
/-- **`f` and `cl f` have the same infimum.** -/
theorem iInf_convexCl_eq_iInf (f : E → EReal) : ⨅ x, convexCl f x = ⨅ x, f x := by
  have : Nonempty E := ⟨0⟩
  by_cases h : ∃ x, lscHull f x = ⊥
  · obtain ⟨x₀, hx₀⟩ := h
    have hb : ⨅ x, f x = ⊥ := by
      rw [← iInf_lscHull_eq_iInf]
      exact le_bot_iff.1 (by rw [← hx₀]; exact iInf_le (fun x => lscHull f x) x₀)
    rw [hb, convexCl_of_exists_eq_bot ⟨x₀, hx₀⟩]
    simp
  · rw [convexCl_of_forall_ne_bot (by push Not at h; exact h)]
    exact iInf_lscHull_eq_iInf f

omit [IsTopologicalAddGroup E] in
/-- The concave mirror of `iInf_convexCl_eq_iInf`: `g` and its concave closure have the same
supremum. Like its convex original it needs no concavity. -/
theorem iSup_concaveCl_eq_iSup (g : E → EReal) : (⨆ x, concaveCl g x) = ⨆ x, g x := by
  have h : (⨆ x, concaveCl g x) = -⨅ x, convexCl (fun z => -(g z)) x := by
    rw [EReal.neg_iInf]
    exact iSup_congr fun x => rfl
  rw [h, iInf_convexCl_eq_iInf, EReal.neg_iInf]
  exact iSup_congr fun x => neg_neg _

omit [AddCommGroup E] [IsTopologicalAddGroup E] in
theorem convexDom_subset_convexDom_lscHull (f : E → EReal) : convexDom f ⊆ convexDom (lscHull f) :=
  fun _ hx => lt_of_le_of_lt (lscHull_le f _) hx

omit [AddCommGroup E] [IsTopologicalAddGroup E] in
/-- `dom f ⊆ dom (cl f) ⊆ cl (dom f)`; this is the second inclusion, which
holds for the hull with no hypothesis on `f`. It is `convexDom_eq_fst_image_epi` pushed through the
continuous projection `Prod.fst`. -/
theorem convexDom_lscHull_subset_closure_convexDom
    (f : E → EReal) : convexDom (lscHull f) ⊆ closure (convexDom f) := by
  intro x hx
  obtain ⟨μ, hμ, -⟩ := ofEpi_lt_iff.1 (hx : lscHull f x < ⊤)
  have h2 := image_closure_subset_closure_image (f := (Prod.fst : E × ℝ → E)) continuous_fst
    (mem_image_of_mem _ hμ)
  rwa [← convexDom_eq_fst_image_epi] at h2

omit [AddCommGroup E] [IsTopologicalAddGroup E] in
/-- **The closure of an improper function is improper.** Neither convexity nor finite dimension is
used. The converse — properness is preserved — needs both, and is `ConvexFn.properConvex_convexCl`
in `Numlib/Analysis/Convex/RelativeInterior.lean`. -/
theorem not_properConvex_convexCl (himp : ¬ ProperConvex f) : ¬ ProperConvex (convexCl f) := by
  intro hpr
  refine himp ⟨?_, fun z hz => hpr.ne_bot z (le_bot_iff.1 (by rw [← hz]; exact convexCl_le f z))⟩
  obtain ⟨y, hy⟩ := hpr.convexDom_nonempty
  have hb : ∀ x, lscHull f x ≠ ⊥ := fun x hx =>
    hpr.ne_bot x (le_bot_iff.1 (by rw [← hx]; exact convexCl_le_lscHull f x))
  rw [convexCl_of_forall_ne_bot hb] at hy
  have hyd : y ∈ closure (convexDom f) := convexDom_lscHull_subset_closure_convexDom f hy
  rcases Set.eq_empty_or_nonempty (convexDom f) with h | h
  · rw [h, closure_empty] at hyd
    exact absurd hyd (Set.notMem_empty y)
  · exact h

omit [AddCommGroup E] [IsTopologicalAddGroup E] in
/-- A point of `closure (epi f)` at height `μ` is a limit of points where `f` is below any `ν > μ`.
This is the pointwise content of Rockafellar's description of `cl f` as the infimum of the `μ` with
`x ∈ cl {z | f z ≤ μ}`. -/
theorem mem_closure_le_of_mem_closure_epi {x : E} {μ ν : ℝ}
    (h : ((x, μ) : E × ℝ) ∈ closure (epi f)) (hμν : μ < ν) :
    x ∈ closure {z | f z ≤ (ν : EReal)} := by
  rw [mem_closure_iff] at h ⊢
  intro U hU hxU
  obtain ⟨p, hp1, hp2⟩ := h (U ×ˢ Iio ν) (hU.prod isOpen_Iio) ⟨hxU, hμν⟩
  have hp2' : f p.1 ≤ (p.2 : EReal) := hp2
  have hp1' : p.2 < ν := hp1.2
  exact ⟨p.1, hp1.1, hp2'.trans (by exact_mod_cast hp1'.le)⟩

/-- The closure of a sublevel set of `f` is contained in the corresponding sublevel set of the
hull. -/
theorem closure_le_subset_lscHull_le (f : E → EReal) (α : ℝ) :
    closure {x | f x ≤ (α : EReal)} ⊆ {x | lscHull f x ≤ (α : EReal)} := by
  intro x hx
  have hsub : (fun z : E => (z, α)) '' {z | f z ≤ (α : EReal)} ⊆ epi f := by
    rintro _ ⟨z, hz, rfl⟩; exact hz
  have h1 := image_closure_subset_closure_image
    (f := fun z : E => (z, α)) (continuous_id.prodMk continuous_const) (mem_image_of_mem _ hx)
  have h2 := closure_mono hsub h1
  rw [← epi_lscHull] at h2
  exact h2

/-- **The level sets of the closure**: `{x | (cl f) x ≤ α} = ⋂_{μ > α} cl {x | f x ≤ μ}`. Stated
for the hull, which is where the content is; the `ri`-flavoured half is finite-dimensional and is
not proved here. -/
theorem lscHull_le_setOf (f : E → EReal) (α : ℝ) :
    {x | lscHull f x ≤ (α : EReal)} = ⋂ μ ∈ Ioi α, closure {x | f x ≤ (μ : EReal)} := by
  refine subset_antisymm (fun x hx => mem_iInter₂.2 fun μ hμ => ?_) fun x hx => ?_
  · have hlt : lscHull f x < (μ : EReal) :=
      lt_of_le_of_lt hx (by exact_mod_cast (hμ : α < μ))
    obtain ⟨ν, hν, hνμ⟩ := ofEpi_lt_iff.1 hlt
    exact mem_closure_le_of_mem_closure_epi hν (by exact_mod_cast hνμ)
  · refine EReal.le_of_forall_lt_iff_le.1 fun q hq => le_of_lt ?_
    replace hq := EReal.coe_lt_coe_iff.1 hq
    obtain ⟨μ, hαμ, hμq⟩ := exists_between hq
    exact lt_of_le_of_lt
      (closure_le_subset_lscHull_le f μ (mem_iInter₂.1 hx μ hαμ)) (by exact_mod_cast hμq)


/-! ### `lscHull` and `convexCl` as closure operators

Both operations are monotone, idempotent and **de**creasing, so each is a closure operator on the
*order dual* of `E → EReal`. Recording that makes Mathlib's `ClosureOperator` API available and
identifies `LowerSemicontinuous` and `ClosedConvex` as the two closedness predicates; the
constructor's hypotheses are literally the universal property. -/

open OrderDual in
/-- `lscHull`, as a closure operator on `(E → EReal)ᵒᵈ`. Its closed elements are the lower
semicontinuous functions. -/
noncomputable def lscHullClosure : ClosureOperator (E → EReal)ᵒᵈ :=
  ClosureOperator.ofPred (fun g => toDual (lscHull (ofDual g)))
    (fun g => LowerSemicontinuous (ofDual g))
    (fun g => lscHull_le (ofDual g))
    (fun g => lowerSemicontinuous_lscHull (ofDual g))
    (fun _ _ hgh hh => le_lscHull_of_le hh hgh)

@[simp] theorem lscHullClosure_apply (f : E → EReal) :
    lscHullClosure (OrderDual.toDual f) = OrderDual.toDual (lscHull f) := rfl

theorem lowerSemicontinuous_iff_lscHullClosure_isClosed :
    LowerSemicontinuous f ↔ lscHullClosure.IsClosed (OrderDual.toDual f) := Iff.rfl

open OrderDual in
/-- `convexCl`, as a closure operator on `(E → EReal)ᵒᵈ`. Its closed elements are exactly the closed
functions, so `ClosedConvex` is the closedness predicate of a genuine closure operator. -/
noncomputable def convexClClosure : ClosureOperator (E → EReal)ᵒᵈ :=
  ClosureOperator.ofPred (fun g => toDual (convexCl (ofDual g)))
    (fun g => ClosedConvex (ofDual g))
    (fun g => convexCl_le (ofDual g))
    (fun g => convexCl_idem (ofDual g))
    (fun _ _ hgh hh => hh.symm.trans_le (convexCl_mono hgh))

@[simp] theorem convexClClosure_apply (f : E → EReal) :
    convexClClosure (OrderDual.toDual f) = OrderDual.toDual (convexCl f) := rfl

theorem closedConvex_iff_convexClClosure_isClosed :
    ClosedConvex f ↔ convexClClosure.IsClosed (OrderDual.toDual f) := Iff.rfl

omit [AddCommGroup E] [IsTopologicalAddGroup E] in
/-- **The universal property of the closure.** `convexCl f` is the greatest closed minorant of `f`;
this is the `hmin` field of `convexClClosure`, restated without the `OrderDual` wrapping. -/
theorem le_convexCl_of_le (hg : ClosedConvex g) (hgf : g ≤ f) : g ≤ convexCl f :=
  hg.symm.trans_le (convexCl_mono hgf)


/-! ### Indicator functions -/

omit [AddCommGroup E] [IsTopologicalAddGroup E] in
/-- The lower semicontinuous hull of an indicator function is the indicator of the closure. -/
@[simp] theorem lscHull_indicatorFn (s : Set E) :
    lscHull (indicatorFn s) = indicatorFn (closure s) := by
  have h : closure (epi (indicatorFn s)) = epi (indicatorFn (closure s)) := by
    rw [epi_indicatorFn, epi_indicatorFn, closure_prod_eq, isClosed_Ici.closure_eq]
  rw [lscHull, h, ofEpi_epi]

omit [AddCommGroup E] [IsTopologicalAddGroup E] in
/-- **`cl δ(· | s) = δ(· | cl s)`**: closing an indicator function closes its set. -/
@[simp] theorem convexCl_indicatorFn (s : Set E) :
    convexCl (indicatorFn s) = indicatorFn (closure s) := by
  rw [convexCl_of_forall_ne_bot fun x => by
    rw [lscHull_indicatorFn]; exact indicatorFn_ne_bot _ _, lscHull_indicatorFn]

omit [AddCommGroup E] [IsTopologicalAddGroup E] in
theorem closedConvex_indicatorFn {s : Set E} (hs : IsClosed s) : ClosedConvex (indicatorFn s) := by
  change convexCl (indicatorFn s) = indicatorFn s
  rw [convexCl_indicatorFn, hs.closure_eq]

/-! ### Finite continuous functions on closed sets -/

omit [AddCommGroup E] [IsTopologicalAddGroup E] in
/-- The epigraph of a finite continuous function on a closed set, extended by `⊤`, is closed. -/
theorem isClosed_epi_convexRestrict_coe {s : Set E} {g : E → ℝ} (hs : IsClosed s)
    (hg : ContinuousOn g s) : IsClosed (epi (convexRestrict s fun x => (g x : EReal))) := by
  rw [epi_convexRestrict_coe]
  have hcont : ContinuousOn (fun p : E × ℝ => g p.1 - p.2) (s ×ˢ (Set.univ : Set ℝ)) :=
    (hg.comp continuousOn_fst fun p hp => hp.1).sub continuousOn_snd
  have h := hcont.preimage_isClosed_of_isClosed (hs.prod isClosed_univ)
    (isClosed_Iic (a := (0 : ℝ)))
  convert h using 1
  ext p
  simp [Set.mem_prod]

/-- A finite continuous function on a closed set, extended by `⊤`, is a closed function. -/
theorem closedConvex_convexRestrict_coe {s : Set E} {g : E → ℝ} (hs : IsClosed s)
    (hg : ContinuousOn g s) : ClosedConvex (convexRestrict s fun x => (g x : EReal)) := by
  have hne : ∀ x, (convexRestrict s fun x => (g x : EReal)) x ≠ ⊥ := by
    intro x
    by_cases hx : x ∈ s <;> simp [hx]
  exact (closedConvex_iff_lowerSemicontinuous hne).2
    (lowerSemicontinuous_iff_isClosed_epi.2 (isClosed_epi_convexRestrict_coe hs hg))

/-- The concave mirror: a finite continuous function on a closed set, extended by `-∞`, is a closed
concave function. -/
theorem closedConcave_concaveRestrict_coe {s : Set E} {g : E → ℝ} (hs : IsClosed s)
    (hg : ContinuousOn g s) : ClosedConcave (concaveRestrict s fun x => (g x : EReal)) := by
  rw [closedConcave_iff_closedConvex_neg, neg_concaveRestrict]
  simp only [← EReal.coe_neg]
  exact closedConvex_convexRestrict_coe hs hg.neg

end Hull

/-! ### Approaching the endpoint of a segment

The three lemmas below package the filter `𝓝[<] (1 : ℝ)` bookkeeping shared by the dichotomy
for improper functions and by the limit formulas for the closure. -/

section Segment

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

theorem tendsto_segment (x y : E) :
    Tendsto (fun a : ℝ => (1 - a) • x + a • y) (𝓝[<] (1 : ℝ)) (𝓝 y) := by
  have hcont : Continuous fun a : ℝ => (1 - a) • x + a • y :=
    ((continuous_const.sub continuous_id).smul continuous_const).add
      (continuous_id.smul continuous_const)
  have h : Tendsto (fun a : ℝ => (1 - a) • x + a • y) (𝓝[<] (1 : ℝ))
      (𝓝 ((1 - (1 : ℝ)) • x + (1 : ℝ) • y)) := (hcont.tendsto 1).mono_left nhdsWithin_le_nhds
  simpa using h

theorem eventually_mem_Ico_nhdsLT_one : ∀ᶠ a : ℝ in 𝓝[<] (1 : ℝ), 0 ≤ a ∧ a < 1 := by
  filter_upwards [(eventually_ge_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with a ha ha1 using ⟨ha, ha1⟩

theorem tendsto_affine_nhdsLT_one (α β : ℝ) :
    Tendsto (fun a : ℝ => (1 - a) * α + a * β) (𝓝[<] (1 : ℝ)) (𝓝 β) := by
  have hcont : Continuous fun a : ℝ => (1 - a) * α + a * β :=
    ((continuous_const.sub continuous_id).mul continuous_const).add
      (continuous_id.mul continuous_const)
  have h : Tendsto (fun a : ℝ => (1 - a) * α + a * β) (𝓝[<] (1 : ℝ))
      (𝓝 ((1 - (1 : ℝ)) * α + (1 : ℝ) * β)) := (hcont.tendsto 1).mono_left nhdsWithin_le_nhds
  simpa using h

end Segment

/-! ### Convexity of the hull and of the closure -/

section Convex

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] {f g : E → EReal}

/-- The lower semicontinuous hull of a convex function is convex: the closure of a convex set is
convex (`Convex.closure`), and `convexFn_ofEpi` turns that back into a convex function. -/
theorem convexFn_lscHull (hf : ConvexFn f) : ConvexFn (lscHull f) :=
  convexFn_ofEpi hf.convex_epi.closure

/-- **The closure of a convex function is again convex**, in either branch. -/
theorem convexFn_convexCl (hf : ConvexFn f) : ConvexFn (convexCl f) := by
  by_cases h : ∃ x, lscHull f x = ⊥
  · rw [convexCl_of_exists_eq_bot h]
    exact ⟨by rw [epi_const_bot]; exact convex_univ⟩
  · rw [convexCl_of_forall_ne_bot (by push Not at h; exact h)]
    exact convexFn_lscHull hf

theorem concaveFn_concaveCl (hg : ConcaveFn g) : ConcaveFn (concaveCl g) := by
  rw [concaveFn_iff_convexFn_neg]
  simpa only [neg_concaveCl] using convexFn_convexCl hg.convexFn_neg

/-! ### The dichotomy for improper convex functions

"An improper convex function is `−∞` on `ri (dom f)`" is finite-dimensional. Its
lower-semicontinuous consequence below is not, and holds in any topological vector space. It is
also the sharp form: the stronger-sounding "a lower semicontinuous convex function taking `⊥`
anywhere is identically `⊥`" is **false**; see `eq_bot_of_lsc_of_eq_bot`. -/

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- The algebraic engine of the dichotomy, valid in any real vector space: if `f` is convex,
`f x₀ = ⊥` and `y` is in the effective domain, then `f` is `⊥` on the half-open segment `[x₀, y)`.
The hypothesis `y ∈ dom f` is needed: for `f = convexRestrict {x₀} (fun _ => ⊥)` the segment meets
`dom f` only at `x₀`. -/
theorem ConvexFn.eq_bot_of_lt_one (hf : ConvexFn f) {x₀ y : E} (h₀ : f x₀ = ⊥)
    (hy : y ∈ convexDom f)
    {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) : f ((1 - a) • x₀ + a • y) = ⊥ := by
  rcases eq_or_lt_of_le ha with rfl | ha'
  · simpa using h₀
  · obtain ⟨β, hβ, -⟩ := EReal.lt_iff_exists_real_btwn.1 (hy : f y < ⊤)
    have hb : (0 : ℝ) < 1 - a := by linarith
    refine le_bot_iff.1 (EReal.le_of_forall_lt_iff_le.1 fun r _ => ?_)
    have hb' : (1 : ℝ) - a ≠ 0 := ne_of_gt hb
    have harith : (1 - a) * ((r - a * β) / (1 - a)) + a * β = r := by
      field_simp
      ring
    have hx₀ : f x₀ < (((r - a * β) / (1 - a) : ℝ) : EReal) := by rw [h₀]; simp
    have hkey := (convexFn_iff_forall_lt f).1 hf x₀ y (1 - a) a hb ha' (by ring) _ β hx₀ hβ
    rw [harith] at hkey
    exact hkey.le

/-- **A lower semicontinuous convex function that takes the value `⊥` somewhere takes it at every
point of its effective domain.** Only lower
semicontinuity at `y` is used, through the limit `λ ↑ 1` along the segment from `x₀` to `y`. -/
theorem ConvexFn.eq_bot_of_mem_convexDom (hf : ConvexFn f) (hl : LowerSemicontinuous f) {x₀ : E}
    (h₀ : f x₀ = ⊥) {y : E} (hy : y ∈ convexDom f) : f y = ⊥ := by
  by_contra hne
  have h1 : ∀ᶠ a in 𝓝[<] (1 : ℝ), (⊥ : EReal) < f ((1 - a) • x₀ + a • y) :=
    (tendsto_segment x₀ y).eventually (hl y ⊥ (bot_lt_iff_ne_bot.2 hne))
  have hbot : ∀ᶠ a : ℝ in 𝓝[<] (1 : ℝ), f ((1 - a) • x₀ + a • y) = ⊥ := by
    filter_upwards [eventually_mem_Ico_nhdsLT_one] with a ha
    exact hf.eq_bot_of_lt_one h₀ hy ha.1 ha.2
  obtain ⟨a, hlt, heq⟩ := (h1.and hbot).exists
  rw [heq] at hlt
  exact absurd hlt (lt_irrefl ⊥)

/-- **A lower semicontinuous improper convex function has no finite values**: it is `⊥` on its
effective domain and `⊤` off it. -/
theorem ConvexFn.eq_bot_or_eq_top (hf : ConvexFn f) (hl : LowerSemicontinuous f)
    (h : ∃ x₀, f x₀ = ⊥) (x : E) : f x = ⊥ ∨ f x = ⊤ := by
  obtain ⟨x₀, h₀⟩ := h
  rcases eq_top_or_lt_top (f x) with hx | hx
  · exact Or.inr hx
  · exact Or.inl (hf.eq_bot_of_mem_convexDom hl h₀ hx)

/-- A lower semicontinuous convex function taking the value `⊥` is `⊥` exactly on its effective
domain, which is therefore closed. -/
theorem ConvexFn.convexDom_eq_setOf_eq_bot (hf : ConvexFn f) (hl : LowerSemicontinuous f)
    (h : ∃ x₀, f x₀ = ⊥) : convexDom f = {x | f x = ⊥} := by
  ext x
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · obtain ⟨x₀, h₀⟩ := h
    exact hf.eq_bot_of_mem_convexDom hl h₀ hx
  · have hx' : f x = ⊥ := hx
    exact mem_convexDom.2 (lt_of_le_of_lt (le_of_eq hx') bot_lt_top)

/-- **The dichotomy, in the form that is actually true.** A lower semicontinuous convex function
that takes the value `⊥` somewhere and is nowhere `⊤` is identically `⊥`. The hypothesis `hdom` is
not removable — see the `example` at the end of this file — and the sharp unconditional form is
`ConvexFn.eq_bot_or_eq_top`. -/
theorem eq_bot_of_lsc_of_eq_bot (hf : ConvexFn f) (hl : LowerSemicontinuous f)
    (hdom : ∀ x, f x < ⊤) (h : ∃ x₀, f x₀ = ⊥) : f = fun _ => ⊥ := by
  obtain ⟨x₀, h₀⟩ := h
  exact funext fun x => hf.eq_bot_of_mem_convexDom hl h₀ (hdom x)

end Convex

/-! ### Positively homogeneous functions -/

section PosHomogeneous

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] {f : E → EReal}

/-- **The lower semicontinuous hull of a positively homogeneous function is positively
homogeneous.** Positive homogeneity is the epigraph being a cone, `epi (lscHull f)` is the closure
of `epi f`, and the closure of a cone is a cone. Convexity is not used anywhere in that chain. -/
theorem posHomogeneous_lscHull (hf : PosHomogeneous f) : PosHomogeneous (lscHull f) := by
  rw [posHomogeneous_iff_isCone_epi] at hf ⊢
  intro a ha
  rw [epi_lscHull]
  exact smul_closure_eq_of_isCone hf a ha

/-- **The closure of a positively homogeneous function is positively homogeneous.** The improper
branch is a case rather than an exclusion: there `cl f` is the constant `⊥`, and `a * ⊥ = ⊥` for
`a > 0`. The same conclusion for *convex* `f` follows from writing `cl f` as a support function;
neither the pairing that needs, nor convexity, is required here. -/
theorem posHomogeneous_convexCl (hf : PosHomogeneous f) : PosHomogeneous (convexCl f) := by
  by_cases h : ∃ x, lscHull f x = ⊥
  · rw [convexCl_of_exists_eq_bot h]
    exact fun a ha _ => (EReal.coe_mul_bot_of_pos ha).symm
  · rw [convexCl_of_forall_ne_bot (by push Not at h; exact h)]
    exact posHomogeneous_lscHull hf

end PosHomogeneous

/-! ### Non-negative scalar multiples -/

section ScalarMultiple

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] {f : E → EReal}

omit [IsTopologicalAddGroup E] in
/-- **`scaleSnd c` is continuous.** It scales only the real coordinate, so `E` contributes nothing
beyond its own topology — no `ContinuousSMul ℝ E` is needed. -/
theorem continuous_scaleSnd (c : ℝ) : Continuous (scaleSnd (E := E) c) := by
  have h : (scaleSnd (E := E) c : E × ℝ → E × ℝ) = fun p => (p.1, c * p.2) := rfl
  rw [h]
  exact continuous_fst.prodMk (continuous_const.mul continuous_snd)

/-- **A non-negative multiple of a closed function is closed**, provided the function never takes
`⊥`. The `⊥`-freedom is what makes closedness of `cf` equivalent to lower semicontinuity of `cf`;
given it, `epi (cf)` is `epi f` pulled back along the continuous `scaleSnd c⁻¹`, and at `c = 0` the
product is the constant `0`. -/
theorem closedConvex_coe_mul {c : ℝ} (hc : 0 ≤ c) (hf : ClosedConvex f) (hb : ∀ x, f x ≠ ⊥) :
    ClosedConvex (fun x => (c : EReal) * f x) := by
  have hb' : ∀ x, (c : EReal) * f x ≠ ⊥ := fun x => EReal.coe_mul_ne_bot hc (hb x)
  rw [closedConvex_iff_lowerSemicontinuous hb', lowerSemicontinuous_iff_isClosed_epi]
  rcases eq_or_lt_of_le hc with h | h
  · have hz : (fun x => (c : EReal) * f x) = fun _ : E => (0 : EReal) := by
      funext x; rw [← h]; simp
    rw [hz, ← lowerSemicontinuous_iff_isClosed_epi]
    exact lowerSemicontinuous_const
  · rw [epi_coe_mul h f]
    refine IsClosed.preimage (continuous_scaleSnd _) ?_
    rw [← lowerSemicontinuous_iff_isClosed_epi]
    exact (closedConvex_iff_lowerSemicontinuous hb).1 hf

end ScalarMultiple

/-! ### Closed proper convex functions -/

section ClosedProperConvex

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] {f : E → EReal}

/-- A **closed proper convex function**: the standing hypothesis of the duality theory, and the
class `convexConjEquiv` and `supportEquiv` are bijections between. The three conditions travel
together throughout the duality theory, so they are bundled rather than repeated. -/
structure ClosedProperConvexFn (f : E → EReal) : Prop where
  /-- The epigraph is convex. -/
  convex : ConvexFn f
  /-- `f` equals its own closure. -/
  closed : ClosedConvex f
  /-- `f` is finite somewhere and never `-∞`. -/
  proper : ProperConvex f

/-- A **closed proper concave function**, the concave twin of `ClosedProperConvexFn` and the
standing hypothesis on the concave side of Fenchel's duality theorem. -/
structure ClosedProperConcaveFn (g : E → EReal) : Prop where
  /-- The hypograph is convex. -/
  concave : ConcaveFn g
  /-- `g` equals its own concave closure. -/
  closed : ClosedConcave g
  /-- `g` is finite somewhere and never `+∞`. -/
  proper : ProperConcave g

omit [IsTopologicalAddGroup E] in
/-- **The sign dictionary**: `g` is closed proper concave exactly when `-g` is closed proper
convex, clause by clause. -/
theorem closedProperConcaveFn_iff_closedProperConvexFn_neg {g : E → EReal} :
    ClosedProperConcaveFn g ↔ ClosedProperConvexFn fun x => -(g x) :=
  ⟨fun h => ⟨h.concave.convexFn_neg, closedConcave_iff_closedConvex_neg.1 h.closed,
      h.proper.properConvex_neg⟩,
    fun h => ⟨concaveFn_iff_convexFn_neg.2 h.convex, closedConcave_iff_closedConvex_neg.2 h.closed,
      properConcave_iff_properConvex_neg.2 h.proper⟩⟩

omit [IsTopologicalAddGroup E] in
/-- The forward direction of `closedProperConcaveFn_iff_closedProperConvexFn_neg`. -/
theorem ClosedProperConcaveFn.closedProperConvexFn_neg {g : E → EReal}
    (hg : ClosedProperConcaveFn g) : ClosedProperConvexFn fun x => -(g x) :=
  closedProperConcaveFn_iff_closedProperConvexFn_neg.1 hg

theorem ClosedProperConvexFn.lowerSemicontinuous (hf : ClosedProperConvexFn f) :
    LowerSemicontinuous f :=
  hf.closed.lowerSemicontinuous

theorem ClosedProperConvexFn.isClosed_epi (hf : ClosedProperConvexFn f) : IsClosed (epi f) :=
  lowerSemicontinuous_iff_isClosed_epi.1 hf.lowerSemicontinuous

/-- For a proper function, closedness of the epigraph is closedness of the function, so this is the
form of the constructor the recession theory uses. -/
theorem ClosedProperConvexFn.of_isClosed_epi (hconv : ConvexFn f) (hc : IsClosed (epi f))
    (hp : ProperConvex f) : ClosedProperConvexFn f :=
  ⟨hconv, (closedConvex_iff_lowerSemicontinuous hp.ne_bot).2
    (lowerSemicontinuous_iff_isClosed_epi.2 hc), hp⟩

theorem closedProperConvexFn_iff_isClosed_epi (hp : ProperConvex f) :
    ClosedProperConvexFn f ↔ ConvexFn f ∧ IsClosed (epi f) :=
  ⟨fun hf => ⟨hf.convex, hf.isClosed_epi⟩,
    fun ⟨hconv, hc⟩ => ClosedProperConvexFn.of_isClosed_epi hconv hc hp⟩

/-- **A continuous affine function, read into `EReal`, is closed proper convex.** This is what a
section with affine constraints asks for: an equality constraint `a x = 0` enters the theory as the
pair of convex functions `a` and `-a`. Continuity is a hypothesis rather than a consequence: on an
infinite-dimensional space a *discontinuous* linear functional is convex, finite everywhere and
proper, and is not closed. In finite dimensions `AffineMap.continuous_of_finiteDimensional`
discharges it. -/
theorem closedProperConvexFn_coe_affineMap {g : E →ᵃ[ℝ] ℝ} (hg : Continuous g) :
    ClosedProperConvexFn (fun x => ((g x : ℝ) : EReal)) := by
  have hcont : Continuous fun x : E => ((g x : ℝ) : EReal) := EReal.continuous_coe_iff.2 hg
  refine ⟨?_, ?_, ⟨⟨0, mem_convexDom.2 (EReal.coe_lt_top _)⟩,
    fun _ => EReal.coe_ne_bot _⟩⟩
  · refine convexFn_of_epi_combo fun x y p q hx hy s t hs ht hst => ?_
    rw [EReal.coe_le_coe_iff] at hx hy ⊢
    rw [Convex.combo_affine_apply hst]
    simp only [smul_eq_mul]
    nlinarith
  · exact (closedConvex_iff_lowerSemicontinuous fun _ => EReal.coe_ne_bot _).2
      hcont.lowerSemicontinuous

end ClosedProperConvex

/-! ### Why the dichotomy needs a hypothesis

The `example` below is the reason `eq_bot_of_lsc_of_eq_bot` carries `∀ x, f x < ⊤`: the function
that is `⊥` at the origin of `ℝ` and `⊤` elsewhere has the vertical line `{0} × ℝ` as its epigraph,
so it is convex and lower semicontinuous, takes the value `⊥`, and is not the constant `⊥`. -/

example : ∃ f : ℝ → EReal,
    ConvexFn f ∧ LowerSemicontinuous f ∧ (∃ x, f x = ⊥) ∧ f ≠ fun _ => ⊥ := by
  have hepi : epi (ConvexAnalysis.convexRestrict ({0} : Set ℝ) fun _ => (⊥ : EReal))
      = (Prod.fst : ℝ × ℝ → ℝ) ⁻¹' {0} := by
    ext p
    by_cases h : p.1 ∈ ({0} : Set ℝ) <;> simp [epi, h]
  refine ⟨ConvexAnalysis.convexRestrict ({0} : Set ℝ) fun _ => ⊥, ⟨?_⟩, ?_, ⟨0, by simp⟩, ?_⟩
  · rw [hepi]
    exact (convex_singleton (0 : ℝ)).linear_preimage (LinearMap.fst ℝ ℝ ℝ)
  · refine lowerSemicontinuous_iff_isClosed_epi.2 ?_
    rw [hepi]
    exact isClosed_singleton.preimage continuous_fst
  · intro hcontra
    have h1 := congrFun hcontra 1
    rw [ConvexAnalysis.convexRestrict_of_notMem (by norm_num : (1 : ℝ) ∉ ({0} : Set ℝ))] at h1
    exact absurd h1 (by simp)


/-! ### Affine minorants of closed proper convex functions -/

section LocallyConvex

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] {f : E → EReal}

/-- **A closed proper convex function has a continuous affine minorant**, the keystone of
Fenchel–Moreau. Closedness is essential: for a merely proper convex `f` the statement is false in
infinite dimensions — a discontinuous linear functional `g` has dense kernel, so `lscHull g ≡ ⊥`,
while `g` is convex, finite everywhere and proper. The proof separates the closed convex set
`epi f` from the point `(x₀, f x₀ - 1)`; the separating functional cannot be vertical, since a
functional `(y, 0)` agrees at `(x₀, f x₀ - 1)` and at `(x₀, f x₀) ∈ epi f`. -/
theorem exists_affine_le_of_closed_proper (hf : ClosedProperConvexFn f) :
    ∃ (y : E →L[ℝ] ℝ) (c : ℝ), ∀ x, ((y x : ℝ) : EReal) - c ≤ f x := by
  obtain ⟨x₀, hx₀⟩ := hf.proper.convexDom_nonempty
  obtain ⟨t, ht⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hf.proper.ne_bot x₀) hx₀
  obtain ⟨y, b, hy, _⟩ :=
    exists_affine_le_of_isClosed_epi hf.convex hf.isClosed_epi (ν := t) (μ := t - 1) (le_of_eq ht)
      (by rw [ht]; exact_mod_cast (by linarith : t - 1 < t))
  exact ⟨y, b, hy⟩

end LocallyConvex

/-! ### Limits along a segment -/

section SegmentLimit

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] {f : E → EReal}

/-- **The lower semicontinuous hull of `f` at `y` is the limit of `f` along the segment running
from `x` to `y`**, provided the segment starts at an *interior* point of `epi f`. The classical
hypothesis is `x ∈ ri (dom f)`, which says that the vertical line over `x` meets `ri (epi f)`;
relative interiors are finite-dimensional, so the general statement uses `interior (epi f)`
instead. In finite dimensions `interior (epi f)` may be
empty when `ri (epi f)` is not, so this is a restriction as well as a generalisation. -/
theorem tendsto_lscHull_along_segment (hf : ConvexFn f) {x : E} {α : ℝ}
    (hx : (x, α) ∈ interior (epi f)) (y : E) :
    Tendsto (fun a : ℝ => f ((1 - a) • x + a • y)) (𝓝[<] (1 : ℝ)) (𝓝 (lscHull f y)) := by
  rw [tendsto_order]
  constructor
  · intro b hb
    filter_upwards [(tendsto_segment x y).eventually (lowerSemicontinuous_lscHull f y b hb)]
      with a ha
    exact lt_of_lt_of_le ha (lscHull_le f _)
  · intro b hb
    obtain ⟨β, hβ1, hβ2⟩ := EReal.lt_iff_exists_real_btwn.1 hb
    obtain ⟨γ, hγ1, hγ2⟩ := EReal.lt_iff_exists_real_btwn.1 hβ2
    have hβγ : β < γ := by exact_mod_cast hγ1
    have hyβ : ((y, β) : E × ℝ) ∈ closure (epi f) := by
      rw [← epi_lscHull]; exact hβ1.le
    filter_upwards [(tendsto_affine_nhdsLT_one α β).eventually_lt_const hβγ,
      eventually_mem_Ico_nhdsLT_one] with a hlt ha
    have hcombo := hf.convex_epi.combo_interior_closure_mem_interior hx hyβ
      (by linarith [ha.2] : (0 : ℝ) < 1 - a) ha.1 (by ring)
    have hpair : (1 - a) • ((x, α) : E × ℝ) + a • (y, β)
        = ((1 - a) • x + a • y, (1 - a) * α + a * β) := by
      simp [smul_eq_mul]
    rw [hpair] at hcombo
    have hle : f ((1 - a) • x + a • y) ≤ (((1 - a) * α + a * β : ℝ) : EReal) :=
      mk_mem_epi.1 (interior_subset hcombo)
    exact lt_of_le_of_lt hle (lt_trans (by exact_mod_cast hlt) hγ2)

/-- The same limit formula for `convexCl`. The exceptional branch has to be ruled out by hand, and
it genuinely can occur: for the function that is `⊥` on a closed ball and `⊤` outside it,
`convexCl f ≡ ⊥` while the limit along a segment ending outside the ball is `⊤`. The classical
statement carries the matching restriction `y ∈ cl (dom f)` in the improper case. -/
theorem convexCl_eq_limit_along_segment (hf : ConvexFn f) (hne : ∀ z, lscHull f z ≠ ⊥)
    {x : E} {α : ℝ}
    (hx : (x, α) ∈ interior (epi f)) (y : E) :
    Tendsto (fun a : ℝ => f ((1 - a) • x + a • y)) (𝓝[<] (1 : ℝ)) (𝓝 (convexCl f y)) := by
  rw [convexCl_of_forall_ne_bot hne]
  exact tendsto_lscHull_along_segment hf hx y

/-- **For a closed proper convex `f`, every `x ∈ dom f` and every `y`,
`f y = lim_{a ↑ 1} f ((1 - a) • x + a • y)`.** No relative interiors are involved: lower
semicontinuity gives the `liminf` half for every `y`, including `f y = ⊤`, and convexity applied to
the finite values `f x` and `f y` gives the `limsup` half. -/
theorem tendsto_along_segment_of_closed_proper (hf : ClosedProperConvexFn f)
    {x : E} (hx : x ∈ convexDom f) (y : E) :
    Tendsto (fun a : ℝ => f ((1 - a) • x + a • y)) (𝓝[<] (1 : ℝ)) (𝓝 (f y)) := by
  have hlsc : LowerSemicontinuous f := hf.lowerSemicontinuous
  rw [tendsto_order]
  refine ⟨fun b hb => (tendsto_segment x y).eventually (hlsc y b hb), fun b hb => ?_⟩
  obtain ⟨s, hs⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hf.proper.ne_bot x) hx
  obtain ⟨r, hr⟩ :=
    EReal.exists_coe_of_ne_bot_of_lt_top (hf.proper.ne_bot y) (lt_of_lt_of_le hb le_top)
  obtain ⟨γ, hγ1, hγ2⟩ := EReal.lt_iff_exists_real_btwn.1 hb
  have hrγ : r < γ := by rw [hr] at hγ1; exact_mod_cast hγ1
  filter_upwards [(tendsto_affine_nhdsLT_one s r).eventually_lt_const hrγ,
    eventually_mem_Ico_nhdsLT_one] with a hlt ha
  have hle := hf.convex.epi_combo hs.le hr.le (by linarith [ha.2] : (0 : ℝ) ≤ 1 - a) ha.1 (by ring)
  exact lt_of_le_of_lt hle (lt_trans (by exact_mod_cast hlt) hγ2)

end SegmentLimit

/-! ### The lower semicontinuous hull as a `liminf`

Rockafellar writes `(cl f)(x) = liminf_{y → x} f(y)`. In a complete lattice
`liminf f (𝓝 x) = ⨆ s ∈ 𝓝 x, ⨅ y ∈ s, f y`, which is exactly the value of `lscHull` at `x`, so the
identity needs no convexity and no hypothesis on `f`. -/

section Liminf

variable {E : Type*} [TopologicalSpace E] {f : E → EReal}

/-- The pointwise `liminf` of `f` along the neighbourhood filter is a minorant of `f`: the
neighbourhood filter contains the point itself. -/
theorem liminf_nhds_le (f : E → EReal) (x : E) : liminf f (𝓝 x) ≤ f x := by
  rw [liminf_eq_iSup_iInf]
  exact iSup₂_le fun s hs => iInf₂_le x (mem_of_mem_nhds hs)

/-- The mirror of `liminf_nhds_le`: a function is at most its own `limsup` along the neighbourhood
filter. -/
theorem le_limsup_nhds (g : E → EReal) (x : E) : g x ≤ limsup g (𝓝 x) := by
  have h := liminf_nhds_le (-g) x
  rw [EReal.liminf_neg, Pi.neg_apply] at h
  exact EReal.neg_le_neg_iff.1 h

/-- `x ↦ liminf_{y → x} f(y)` is lower semicontinuous: a neighbourhood witnessing the bound at `x`
witnesses it, through its interior, at every nearby point. -/
theorem lowerSemicontinuous_liminf_nhds (f : E → EReal) :
    LowerSemicontinuous fun x => liminf f (𝓝 x) := by
  intro x c hc
  have hc' : c < liminf f (𝓝 x) := hc
  rw [liminf_eq_iSup_iInf] at hc'
  obtain ⟨s, hs⟩ := lt_iSup_iff.1 hc'
  obtain ⟨hsmem, hlt⟩ := lt_iSup_iff.1 hs
  filter_upwards [isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.2 hsmem)] with z hz
  change c < liminf f (𝓝 z)
  refine lt_of_lt_of_le hlt ?_
  rw [liminf_eq_iSup_iInf]
  refine le_trans ?_
    (le_iSup₂ (f := fun t (_ : t ∈ 𝓝 z) => ⨅ a ∈ t, f a) (interior s)
      (isOpen_interior.mem_nhds hz))
  exact le_iInf₂ fun a ha => iInf₂_le a (interior_subset ha)

end Liminf

section LiminfHull

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [IsTopologicalAddGroup E]
  {f : E → EReal}

/-- **The lower semicontinuous hull is a `liminf`**: `(lsc f)(x) = liminf_{y → x} f(y)`, since the
`liminf` function is a lower semicontinuous minorant of `f` and a lower semicontinuous function is
at most its own `liminf`. -/
theorem lscHull_eq_liminf (f : E → EReal) (x : E) : lscHull f x = liminf f (𝓝 x) := by
  refine le_antisymm ?_ (le_lscHull_of_le (lowerSemicontinuous_liminf_nhds f) (liminf_nhds_le f) x)
  refine le_trans (LowerSemicontinuous.le_liminf (lowerSemicontinuous_lscHull f) x) ?_
  rw [liminf_eq_iSup_iInf, liminf_eq_iSup_iInf]
  exact iSup₂_mono fun s _ => iInf₂_mono fun a _ => lscHull_le f a

/-- **Rockafellar's `cl f = liminf f`**, in the regular branch: as soon as the lower semicontinuous
hull is nowhere `-∞`, the closure of `f` at `x` is the `liminf` of `f` at `x`. -/
theorem convexCl_eq_liminf (h : ∀ z, lscHull f z ≠ ⊥) (x : E) : convexCl f x = liminf f (𝓝 x) := by
  rw [convexCl_of_forall_ne_bot h, lscHull_eq_liminf]

end LiminfHull

section LiminfConvex

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] {f : E → EReal}

/-- **Rockafellar's `cl f = liminf f`, in full.** For a *convex* `f` the closure at `x` is the
`liminf` of `f` at `x`, except in the single degenerate case where the left side is `-∞` and the
right side is `+∞`; that case can only arise in the exceptional branch of `convexCl`, where the
dichotomy leaves `lscHull f` with only the values `-∞` and `+∞`. -/
theorem convexCl_eq_liminf_or (hf : ConvexFn f) (x : E) :
    convexCl f x = liminf f (𝓝 x) ∨ (convexCl f x = ⊥ ∧ liminf f (𝓝 x) = ⊤) := by
  by_cases h : ∃ z, lscHull f z = ⊥
  · have hcl : convexCl f x = ⊥ := by rw [convexCl_of_exists_eq_bot h]
    rcases ConvexFn.eq_bot_or_eq_top (convexFn_lscHull hf) (lowerSemicontinuous_lscHull f) h x with
      hb | ht
    · exact Or.inl (by rw [hcl, ← lscHull_eq_liminf, hb])
    · exact Or.inr ⟨hcl, by rw [← lscHull_eq_liminf]; exact ht⟩
  · push Not at h
    exact Or.inl (by rw [convexCl_of_forall_ne_bot h, lscHull_eq_liminf])

/-- The concave mirror of `convexCl_eq_liminf_or`: for concave `g` the concave closure at `x` is the
`limsup` of `g` at `x`, except when the left side is `+∞` and the right `-∞`. -/
theorem concaveCl_eq_limsup_or {g : E → EReal} (hg : ConcaveFn g) (x : E) :
    concaveCl g x = limsup g (𝓝 x) ∨ (concaveCl g x = ⊤ ∧ limsup g (𝓝 x) = ⊥) := by
  have hkey : liminf (fun z => -(g z)) (𝓝 x) = -(limsup g (𝓝 x)) := EReal.liminf_neg
  rcases convexCl_eq_liminf_or hg.convexFn_neg x with heq | ⟨hbot, htop⟩
  · exact Or.inl (by rw [concaveCl_apply, heq, hkey, neg_neg])
  · refine Or.inr ⟨by rw [concaveCl_apply, hbot, EReal.neg_bot], ?_⟩
    rw [hkey] at htop
    exact EReal.neg_eq_top_iff.1 htop

end LiminfConvex

end ConvexAnalysis
