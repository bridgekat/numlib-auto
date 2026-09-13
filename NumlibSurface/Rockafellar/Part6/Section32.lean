import Numlib.Analysis.Convex.Duality.Support
import Numlib.Analysis.Convex.Optimization.Maximum
import Numlib.Analysis.Convex.Subdifferential.Existence
import Numlib.Analysis.Convex.Subdifferential.Rademacher
import NumlibSurface.Common.Euclidean
import NumlibSurface.Rockafellar.Part2.Section08
import NumlibSurface.Rockafellar.Part4.Section19

/-!
# Rockafellar, §32: The Maximum of a Convex Function

Maximising a convex function, which behaves nothing like minimising one. The maximum principle
(Theorem 32.1) says that a relative interior maximiser forces constancy, so the maximum lives on
the relative boundary — on a face, and ultimately at an extreme point (Theorem 32.3 and its four
corollaries). Theorem 32.4 reads the same fact through subgradients: at a maximiser every
subgradient is a non-zero normal vector.

All 11 numbered results of §32 are formalized: Theorems 32.1, 32.2, 32.3 and 32.4 and Corollaries
32.1.1, 32.2.1, 32.3.1, 32.3.2, 32.3.3, 32.3.4 and 32.4.1, together with the section's two examples
and the unnumbered remarks that carry mathematical content.

## Main definitions

* `maximumSet f C` — Rockafellar's `W`, the set of points where the supremum of `f` relative to `C`
  is attained. Corollary 32.1.1 is then the set equation `W = ⋃₀ {C' | IsFace C C' ∧ C' ⊆ W}`.
* `NoUnboundedHalfLine f C` — the standing hypothesis of Theorem 32.3, quantified over genuine
  half-lines (`v ≠ 0`). `bddAboveOnRays_iff` is the bridge to the backbone's `BddAboveOnRays`,
  which folds the book's *other* standing hypothesis `C ⊆ dom f` into the same predicate by
  allowing `v = 0`; the two agree exactly when `C ⊆ dom f`, so every statement below carries
  Rockafellar's two hypotheses separately, as he writes them.
* `linearSystem a α` — the solution set of a finite system `⟨x, aᵢ⟩ ≤ αᵢ`, so that
  `corollary_32_3_4_linearSystem` can be the book's own sentence on the basis of the simplex method.
* `parabolicSet`, `parabolicFn`, `parabolicCap`, `quarticCap` — the section's two examples.

**Corollary 32.3.2's finiteness clause is false as printed.** "Then the supremum of `f` relative to
`C` is finite" fails for the improper `f ≡ −∞`, whose domain is `ℝⁿ`, so that `ri (dom f)` contains
every compact convex `C` while the supremum is `−∞`. `corollary_32_3_2` and
`corollary_32_3_2_finite` therefore carry `Proper f`; the attainment clause needs no repair.

The two examples both use `parabolicFn`, `f(ξ₁, ξ₂) = ξ₁²/ξ₂ − ξ₂` for `ξ₂ > 0`, `0` at the origin
and `+∞` elsewhere, which is convex, closed and proper because it is the support function of
`parabolicSet`. They show that `C ⊆ ri (dom f)` in Corollary 32.3.2 cannot be weakened to
`C ⊆ dom f` even for closed `f`: on `parabolicCap` the supremum is `1` and unattained, and on
`quarticCap` it is `+∞`. Both weakenings are stated and refuted in Lean, as
`corollary_32_3_2_not_attained_of_subset_dom` and `corollary_32_3_2_not_bddAbove_of_subset_dom`.

Two statements are stronger than the book's: `theorem_32_1` drops the convexity of `C`, which its
proof does not use, and `corollary_32_4_1` applies Theorem 32.4 to `S` directly instead of passing
to `conv S`.

## References

* [rockafellar1970convex] §32 (pp. 342–348).
-/

open scoped Pointwise

namespace Rockafellar

open ConvexAnalysis NumlibSurface

variable {n : ℕ} {f : Rn n → EReal} {C : Set (Rn n)}

/-! ### Theorem 32.1: the maximum principle -/

/-- **Theorem 32.1**, the maximum principle: if a convex function attains its supremum relative to
a set `C ⊆ dom f` at a point of `ri C`, it takes the same value everywhere on `C`.

Rockafellar assumes `C` convex; the proof does not use it. All that is needed is that a relative
interior point can be prolonged past itself inside `C` (Theorem 6.4), which exhibits `z` as a
proper convex combination of `x` and a further point of `C`. -/
theorem theorem_32_1 (hf : ConvexFn f) (hCdom : C ⊆ dom f) {z : Rn n} (hz : z ∈ ri C)
    (hmax : ∀ w ∈ C, f w ≤ f z) {x : Rn n} (hx : x ∈ C) : f x = f z :=
  hf.eq_of_isMaxOn_mem_relint hCdom hz hmax hx

/-- **Theorem 32.1**: "`f` is actually constant throughout `C`", stated as constancy rather than as
"every value equals the maximum". -/
theorem theorem_32_1_const (hf : ConvexFn f) (hCdom : C ⊆ dom f) {z : Rn n} (hz : z ∈ ri C)
    (hmax : ∀ w ∈ C, f w ≤ f z) {x y : Rn n} (hx : x ∈ C) (hy : y ∈ C) : f x = f y := by
  rw [theorem_32_1 hf hCdom hz hmax hx, theorem_32_1 hf hCdom hz hmax hy]

/-- **§32**, first sentence of the remark after Theorem 32.1: a convex function attaining its
supremum relative to an affine set `M ⊆ dom f` is constant on `M`. Theorem 32.1 at `C = M`, where
`ri M = M` so the relative interior hypothesis is free. -/
theorem theorem_32_1_affineSubspace (hf : ConvexFn f) {M : AffineSubspace ℝ (Rn n)}
    (hMdom : (M : Set (Rn n)) ⊆ dom f) {z : Rn n} (hz : z ∈ M)
    (hmax : ∀ w ∈ (M : Set (Rn n)), f w ≤ f z) {x : Rn n} (hx : x ∈ M) : f x = f z :=
  theorem_32_1 hf hMdom (by rw [AffineSubspace.intrinsicInterior_coe]; exact hz) hmax hx

/-- **§32**, second sentence, which is **Corollary 8.6.2**: the conclusion holds as soon as the
supremum over `M` is finite, attained or not. -/
theorem theorem_32_1_affineSubspace_of_le (hf : ConvexFn f) {M : AffineSubspace ℝ (Rn n)}
    {α : ℝ} (hM : ∀ w ∈ M, f w ≤ (α : EReal)) {x z : Rn n} (hx : x ∈ M) (hz : z ∈ M) :
    f z = f x :=
  corollary_8_6_2 hf hM hx hz

/-- **Corollary 32.1.1**: Rockafellar's `W`, the set of points at which the supremum of `f` relative
to `C` is attained. -/
def maximumSet (f : Rn n → EReal) (C : Set (Rn n)) : Set (Rn n) :=
  {x | x ∈ C ∧ ∀ w ∈ C, f w ≤ f x}

theorem mem_maximumSet {x : Rn n} :
    x ∈ maximumSet f C ↔ x ∈ C ∧ ∀ w ∈ C, f w ≤ f x := Iff.rfl

/-- **Corollary 32.1.1**: `W` is a union of faces of `C`, stated as the set equation it is.

The inclusion `⊇` is free. For `⊆`, Theorem 18.2 produces the unique face `C'` having a given
maximiser in its relative interior, and Theorem 32.1 applied to `C'` makes `f` constant on it, so
`C'` consists of maximisers too. -/
theorem corollary_32_1_1 (hf : ConvexFn f) (hC : Convex ℝ C) (hCdom : C ⊆ dom f) :
    maximumSet f C = ⋃₀ {C' | IsFace C C' ∧ C' ⊆ maximumSet f C} := by
  refine Set.Subset.antisymm (fun x hx => ?_) (Set.sUnion_subset fun C' hC' => hC'.2)
  obtain ⟨C', hface, hxC', hconst⟩ :=
    exists_isFace_forall_eq_of_isMaxOn hf hC hCdom hx.1 hx.2
  refine ⟨C', ⟨hface, fun y hy => ⟨hface.toIsExtreme.1 hy, fun w hw => ?_⟩⟩, hxC'⟩
  rw [hconst y hy]
  exact hx.2 w hw

/-! ### Theorem 32.2: passing to the convex hull -/

/-- **Theorem 32.2**: the convex hull does not raise the supremum of a
convex function, `sup_{conv S} f = sup_S f`.

The sublevel set `{x | f x ≤ sup_S f}` is convex and contains `S`, so it contains `conv S`. This
is `convexHull_min`, not a Carathéodory decomposition, and it needs neither a topology nor a
dimension bound. -/
theorem theorem_32_2 (hf : ConvexFn f) (S : Set (Rn n)) :
    (⨆ x ∈ convexHull ℝ S, f x) = ⨆ x ∈ S, f x :=
  hf.iSup_convexHull S

/-- **Theorem 32.2**: "the first supremum is attained only when the second (more restrictive)
supremum is attained". The *strict* sublevel set does the same job: a convex function staying
strictly below its maximum throughout `S` stays below it throughout `conv S`. -/
theorem theorem_32_2_attained (hf : ConvexFn f) {S : Set (Rn n)} {x : Rn n}
    (hx : x ∈ convexHull ℝ S) (hmax : ∀ z ∈ convexHull ℝ S, f z ≤ f x) :
    ∃ z ∈ S, f z = f x :=
  exists_eq_of_isMaxOn_convexHull hf hx hmax

/-- **Corollary 32.2.1**: for a closed convex `C` that is not an affine set
or half of one, the supremum over `C` is already the supremum over the relative boundary.

Rockafellar's two exceptional cases are one predicate in the backbone, `IsAffineHalf` — the
degenerate functional `φ = 0` gives the affine sets — and the exclusion cannot be dropped: over
`[0, ∞)` the relative boundary is `{0}` while `f x = x` has supremum `⊤`. The proof is
Theorem 18.4 in hull form (`convexHull ℝ (C \ ri C) = C`) fed to Theorem 32.2. -/
theorem corollary_32_2_1 (hf : ConvexFn f) (hC : Convex ℝ C) (hCcl : IsClosed C)
    (hhalf : ¬ IsAffineHalf C) : (⨆ x ∈ C, f x) = ⨆ x ∈ C \ ri C, f x :=
  hf.iSup_sdiff_relint hC hCcl hhalf

/-- **Corollary 32.2.1**: "the former is attained only when the latter is attained" — Theorem 32.2's
attainment clause read through Theorem 18.4. -/
theorem corollary_32_2_1_attained (hf : ConvexFn f) (hC : Convex ℝ C) (hCcl : IsClosed C)
    (hhalf : ¬ IsAffineHalf C) {x : Rn n} (hx : x ∈ C) (hmax : ∀ z ∈ C, f z ≤ f x) :
    ∃ z ∈ C \ ri C, f z = f x :=
  exists_notMem_relint_eq_of_isMaxOn hf hC hCcl hhalf hx hmax

/-! ### Theorem 32.3: the extreme point principle -/

/-- **Theorem 32.3**, the standing hypothesis "there are no half-lines in `C` on which `f` is
unbounded above", read over genuine half-lines (`v ≠ 0`). -/
def NoUnboundedHalfLine (f : Rn n → EReal) (C : Set (Rn n)) : Prop :=
  ∀ u v : Rn n, v ≠ 0 → (∀ t : ℝ, 0 ≤ t → u + t • v ∈ C) →
    ∃ β : ℝ, ∀ t : ℝ, 0 ≤ t → f (u + t • v) ≤ (β : EReal)

/-- **The bridge to the backbone's `BddAboveOnRays`.** The backbone folds Rockafellar's two standing
hypotheses of Theorem 32.3 into one predicate by letting the direction `v` be `0`, so that the
degenerate "half-line" `{u}` carries the condition `f u < ⊤`; under `C ⊆ dom f` the degenerate case
is automatic and the two predicates agree. -/
theorem bddAboveOnRays_iff (hCdom : C ⊆ dom f) :
    BddAboveOnRays f C ↔ NoUnboundedHalfLine f C := by
  constructor
  · exact fun h u v _ hray => h u v hray
  · intro h u v hray
    rcases eq_or_ne v 0 with rfl | hv
    · have hu : u ∈ C := by simpa using hray 0 le_rfl
      obtain ⟨β, hβ, -⟩ := EReal.lt_iff_exists_real_btwn.1 (mem_dom.1 (hCdom hu))
      exact ⟨β, fun t _ => by simpa using hβ.le⟩
    · exact h u v hv hray

/-- **Theorem 32.3**, in the book's own form: `sup_C f = sup_E f`, where `E` is the set of extreme
points of `C ∩ L⊥` and `L` is the lineality space of `C`.

The backbone states this for an *arbitrary* complement `N` of `L`, since fixing `L⊥` would need an
inner product it does not assume. Here the inner product is available, so this is that theorem at
`N = L⊥` — the book's form. -/
theorem theorem_32_3 (hf : ConvexFn f) (hC : Convex ℝ C) (hCcl : IsClosed C)
    (hCdom : C ⊆ dom f) (hray : NoUnboundedHalfLine f C) :
    (⨆ x ∈ C, f x)
      = ⨆ x ∈ (C ∩ ((linealitySubmodule C)ᗮ : Set (Rn n))).extremePoints ℝ, f x :=
  hf.iSup_extremePoints_inter_of_isCompl hC hCcl ((bddAboveOnRays_iff hCdom).2 hray)
    (Submodule.isCompl_orthogonal _)

/-- **Theorem 32.3**: "the supremum relative to `C` is attained only when the supremum relative to
`E` is attained". The maximiser is transported to `C ∩ L⊥` along the lineality space, where
Corollary 32.3.1 applies. Rockafellar's `C ⊆ dom f` is what supplies `f x ≠ ⊤` there. -/
theorem theorem_32_3_attained (hf : ConvexFn f) (hC : Convex ℝ C) (hCcl : IsClosed C)
    (hCdom : C ⊆ dom f) (hray : NoUnboundedHalfLine f C) {x : Rn n} (hx : x ∈ C)
    (hmax : ∀ w ∈ C, f w ≤ f x) :
    ∃ z ∈ (C ∩ ((linealitySubmodule C)ᗮ : Set (Rn n))).extremePoints ℝ, f z = f x :=
  exists_mem_extremePoints_inter_eq_of_isMaxOn_of_isCompl hf hC hCcl
    ((bddAboveOnRays_iff hCdom).2 hray) (Submodule.isCompl_orthogonal _) hx hmax

/-- **Corollary 32.3.1**: if the supremum of a convex function over a closed convex set containing
no lines is attained at all, it is attained at an extreme point. No boundedness is needed — a finite
maximum is itself a bound — but `f x ≠ ⊤` is, and that is what `C ⊆ dom f` supplies. -/
theorem corollary_32_3_1 (hf : ConvexFn f) (hC : Convex ℝ C) (hCcl : IsClosed C)
    (hCdom : C ⊆ dom f) (hnl : ContainsNoLine C) {x : Rn n} (hx : x ∈ C)
    (hmax : ∀ z ∈ C, f z ≤ f x) : ∃ z ∈ C.extremePoints ℝ, f z = f x :=
  exists_mem_extremePoints_eq_of_isMaxOn_of_containsNoLine hf hC hCcl hnl hx
    (mem_dom.1 (hCdom hx)).ne hmax

/-- **Corollary 32.3.2**: a convex function attains its supremum relative to a non-empty closed
bounded convex `C ⊆ ri (dom f)` at an extreme point of `C`. `C ⊆ ri (dom f)` makes `f` continuous
relative to `C` (Theorem 10.1), closed and bounded makes `C` compact, and Corollary 32.3.1 moves the
maximiser to an extreme point. `Proper f` is not in the book's statement; see
`corollary_32_3_2_finite`. -/
theorem corollary_32_3_2 (hf : ConvexFn f) (hp : Proper f) (hne : C.Nonempty)
    (hCcl : IsClosed C) (hCbdd : Bornology.IsBounded C) (hCconv : Convex ℝ C)
    (hCri : C ⊆ ri (dom f)) : ∃ z ∈ C.extremePoints ℝ, ∀ w ∈ C, f w ≤ f z :=
  exists_mem_extremePoints_isMaxOn_of_isCompact hf hp
    (Metric.isCompact_of_isClosed_isBounded hCcl hCbdd) hCconv hne hCri

/-- **Corollary 32.3.2**: "the supremum of `f` relative to `C` is finite". **This is the clause that
needs `Proper f`, which the book omits**: for `f ≡ −∞` the printed hypotheses hold and the supremum
is `⊥`. Given properness the supremum is the value at the maximiser, a real number because the
maximiser lies in `dom f` and `f` never takes `−∞`. -/
theorem corollary_32_3_2_finite (hf : ConvexFn f) (hp : Proper f) (hne : C.Nonempty)
    (hCcl : IsClosed C) (hCbdd : Bornology.IsBounded C) (hCconv : Convex ℝ C)
    (hCri : C ⊆ ri (dom f)) : ∃ r : ℝ, (⨆ x ∈ C, f x) = (r : EReal) := by
  obtain ⟨z, hz, hzmax⟩ := corollary_32_3_2 hf hp hne hCcl hCbdd hCconv hCri
  have hzC : z ∈ C := extremePoints_subset hz
  obtain ⟨r, hr⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hp.ne_bot z)
    (mem_dom.1 (intrinsicInterior_subset (hCri hzC)))
  refine ⟨r, le_antisymm (iSup₂_le fun w hw => hr ▸ hzmax w hw) ?_⟩
  rw [← hr]
  exact le_iSup₂ (f := fun w (_ : w ∈ C) => f w) z hzC

/-- **Corollary 32.3.3**: on a non-empty polyhedral `C ⊆ dom f` with no half-line on which `f` is
unbounded above, the supremum of `f` relative to `C` is attained. Nothing is claimed about extreme
points, and nothing is assumed about lines in `C` — a set containing a line has none. -/
theorem corollary_32_3_3 (hf : ConvexFn f) (hC : Polyhedral C) (hne : C.Nonempty)
    (hCdom : C ⊆ dom f) (hray : NoUnboundedHalfLine f C) : ∃ z ∈ C, ∀ w ∈ C, f w ≤ f z :=
  exists_isMaxOn_of_polyhedral_of_bddAboveOnRays hf hC hne ((bddAboveOnRays_iff hCdom).2 hray)

/-- **Corollary 32.3.4**: a convex function bounded above on a non-empty polyhedral convex set
containing no lines attains its supremum at one of the (finitely many) extreme points.

This combines Corollaries 32.3.1 and 32.3.3, and is **the theoretical basis of the simplex
method**: it "applies in particular to the problem of maximizing an affine function over the set of
solutions to a finite system of weak linear inequalities", which is
`corollary_32_3_4_linearSystem`. The uniform real bound carries Rockafellar's standing
`C ⊆ dom f` with it. -/
theorem corollary_32_3_4 (hf : ConvexFn f) (hC : Polyhedral C) (hne : C.Nonempty)
    (hnl : ContainsNoLine C) {β : ℝ} (hbdd : ∀ x ∈ C, f x ≤ (β : EReal)) :
    ∃ z ∈ C.extremePoints ℝ, ∀ w ∈ C, f w ≤ f z :=
  exists_mem_extremePoints_isMaxOn_of_finitelyGenerated hf hC.finitelyGenerated hnl hne hbdd

/-- **Corollary 32.3.4**: the parenthetical "(finitely many)". A polyhedral set is finitely
generated (Theorem 19.1) and the extreme points of `conv P + cone D` lie in `P` (Corollary
18.3.1). -/
theorem corollary_32_3_4_finite (hC : Polyhedral C) : (C.extremePoints ℝ).Finite :=
  corollary_19_1_1_extremePoints hC

/-- **§32**: "Theorem 32.2 can be applied to a given closed convex set `C` by representing `C` as
the convex hull of its extreme points and extreme directions as in §18." Unlike Theorem 32.3 this
needs no boundedness: keeping the extreme *directions* in the index set is what makes the identity
unconditional. -/
theorem theorem_32_2_extremePoints_add_coneHull (hf : ConvexFn f) (hC : Convex ℝ C)
    (hCcl : IsClosed C) (hnl : ContainsNoLine C) :
    (⨆ x ∈ C, f x)
      = ⨆ x ∈ C.extremePoints ℝ + (PointedCone.hull ℝ (extremeDirections C) : Set (Rn n)), f x :=
  hf.iSup_extremePoints_add_coneHull hC hCcl hnl

/-- **§32**: the step of Theorem 32.3's proof that cites Corollary 8.6.2 — `f` is constant along
every line in `C`. -/
theorem theorem_32_3_const_on_lineality (hf : ConvexFn f) (hCdom : C ⊆ dom f)
    (hray : NoUnboundedHalfLine f C) {u v : Rn n} (hu : u ∈ C) (hv : v ∈ linealitySpace C) :
    f (u + v) = f u :=
  hf.add_eq_of_mem_linealitySpace ((bddAboveOnRays_iff hCdom).2 hray) hu hv

/-- **Theorem 32.3** when `C` contains no lines: then `L = 0` and `C ∩ L⊥ = C`, so the supremum over
`C` is the supremum over the extreme points of `C` itself. This is the form Corollary 32.3.1 is read
off. -/
theorem theorem_32_3_containsNoLine (hf : ConvexFn f) (hC : Convex ℝ C) (hCcl : IsClosed C)
    (hCdom : C ⊆ dom f) (hray : NoUnboundedHalfLine f C) (hnl : ContainsNoLine C) :
    (⨆ x ∈ C, f x) = ⨆ x ∈ C.extremePoints ℝ, f x :=
  hf.iSup_extremePoints_of_containsNoLine hC hCcl hnl ((bddAboveOnRays_iff hCdom).2 hray)

/-- **Corollary 32.3.2**, supremum form: over a compact convex set the supremum of a convex function
is already the supremum over the extreme points. This is Minkowski's theorem (Corollary 18.5.1) fed
to Theorem 32.2, and it needs neither `C ⊆ ri (dom f)` nor properness — only the *attainment* clause
does. -/
theorem corollary_32_3_2_iSup (hf : ConvexFn f) (hCcl : IsClosed C)
    (hCbdd : Bornology.IsBounded C) (hCconv : Convex ℝ C) :
    (⨆ x ∈ C, f x) = ⨆ x ∈ C.extremePoints ℝ, f x :=
  hf.iSup_extremePoints (Metric.isCompact_of_isClosed_isBounded hCcl hCbdd) hCconv

/-- **§32.** The solution set of a finite system of weak linear inequalities `⟨x, aᵢ⟩ ≤ αᵢ`, `i < m`
— the feasible region of a linear program. -/
def linearSystem {m : ℕ} (a : Fin m → Rn n) (α : Fin m → ℝ) : Set (Rn n) :=
  {x : Rn n | ∀ i, pairing n x (a i) ≤ α i}

/-- A finite system of weak linear inequalities has a polyhedral solution set — this is the
definition of `Polyhedral`, transcribed at the book's index type. -/
theorem polyhedral_linearSystem {m : ℕ} (a : Fin m → Rn n) (α : Fin m → ℝ) :
    Polyhedral (linearSystem a α) := by
  classical
  refine ⟨Finset.image (fun i => (((pairing n).flip (a i) : Rn n →ₗ[ℝ] ℝ), α i)) Finset.univ, ?_⟩
  ext x
  constructor
  · intro hx q hq
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hq
    exact hx i
  · intro hx i
    exact hx _ (Finset.mem_image.2 ⟨i, Finset.mem_univ i, rfl⟩)

/-- **§32**: Corollary 32.3.4 for an affine objective `⟨x, b⟩ − γ`. An affine function is convex
(`convexFn_affineFn`) and real-valued, so both of Rockafellar's standing hypotheses reduce to the
boundedness assumption. -/
theorem corollary_32_3_4_affine (b : Rn n) (γ : ℝ) (hC : Polyhedral C) (hne : C.Nonempty)
    (hnl : ContainsNoLine C) {β : ℝ} (hbdd : ∀ x ∈ C, pairing n x b - γ ≤ β) :
    ∃ z ∈ C.extremePoints ℝ, ∀ w ∈ C, pairing n w b - γ ≤ pairing n z b - γ := by
  obtain ⟨z, hz, hzmax⟩ := corollary_32_3_4 (convexFn_affineFn b γ) hC hne hnl (β := β)
    fun x hx => by rw [affineFn_eq_coe]; exact_mod_cast hbdd x hx
  refine ⟨z, hz, fun w hw => ?_⟩
  have hle := hzmax w hw
  rw [affineFn_eq_coe, affineFn_eq_coe, EReal.coe_le_coe_iff] at hle
  exact hle

/-- **§32**: maximising an affine function over the solutions of a finite system of weak linear
inequalities — the theoretical basis of the simplex method. -/
theorem corollary_32_3_4_linearSystem {m : ℕ} (a : Fin m → Rn n) (α : Fin m → ℝ) (b : Rn n)
    (γ : ℝ) (hne : (linearSystem a α).Nonempty) (hnl : ContainsNoLine (linearSystem a α))
    {β : ℝ} (hbdd : ∀ x ∈ linearSystem a α, pairing n x b - γ ≤ β) :
    ∃ z ∈ (linearSystem a α).extremePoints ℝ,
      ∀ w ∈ linearSystem a α, pairing n w b - γ ≤ pairing n z b - γ :=
  corollary_32_3_4_affine b γ (polyhedral_linearSystem a α) hne hnl hbdd

/-! ### Theorem 32.4: subgradients at a maximiser -/

/-- **Theorem 32.4**: "here `f` must be proper by Theorem 7.2, since `f` is assumed to be finite at
a point of `ri (dom f)`." Properness is a *consequence* of the theorem's hypotheses, not one of
them, and this is the step that produces it. -/
theorem theorem_32_4_proper (hf : ConvexFn f) {x : Rn n} (hxri : x ∈ ri (dom f))
    (hxb : f x ≠ ⊥) : Proper f := by
  by_contra himp
  exact hxb (hf.eq_bot_of_mem_relint_dom himp hxri)

/-- **Theorem 32.4**: "the set `∂f(x)` is non-empty, because `x ∈ ri (dom f)` (Theorem 23.4)" —
which is what makes the theorem's conclusion about *every* subgradient a statement with content. -/
theorem theorem_32_4_nonempty (hf : ConvexFn f) {x : Rn n} (hxri : x ∈ ri (dom f))
    (hxb : f x ≠ ⊥) : (subdifferential (pairing n) f x).Nonempty :=
  subdifferential_nonempty_of_mem_relint_dom hf (theorem_32_4_proper hf hxri hxb) hxri

/-- **Theorem 32.4**: at a point where `f` attains its supremum relative to `C`, every
`x* ∈ ∂f(x)` is normal to `C` at `x`.

Rockafellar routes this through the sublevel set `D = {z | f z ≤ α}` and Theorem 23.7. Read
directly it is one line: the subgradient inequality at `z` and maximality at `z` sandwich
`⟨z − x, x*⟩` between `0` and `0`. Only finiteness of `f x` is used, so neither convexity of `C`
nor `x ∈ ri (dom f)` appears. -/
theorem theorem_32_4_normal (hfin : ∀ z ∈ C, f z ≠ ⊥ ∧ f z ≠ ⊤) {x : Rn n} (hx : x ∈ C)
    (hmax : ∀ z ∈ C, f z ≤ f x) {y : Rn n} (hy : y ∈ subdifferential (pairing n) f x) :
    y ∈ normalCone (pairing n) C x :=
  mem_normalCone_of_mem_subdifferential_of_isMaxOn (hfin x hx).1 (hfin x hx).2 hmax hy

/-- **Theorem 32.4**: the vector is **non-zero**. Rockafellar's argument is that `inf f < f x`
because `f` is not constant on `C`, hence `0 ∉ ∂f(x)`; here the witness of non-constancy is passed
directly, since a set on which `f` is not constant supplies one at every one of its points. -/
theorem theorem_32_4_ne_zero {x : Rn n} (hmax : ∀ z ∈ C, f z ≤ f x) {z₀ : Rn n} (hz₀ : z₀ ∈ C)
    (hne : f z₀ ≠ f x) {y : Rn n} (hy : y ∈ subdifferential (pairing n) f x) : y ≠ 0 :=
  ne_zero_of_mem_subdifferential_of_isMaxOn hmax hz₀ hne hy

/-- **Corollary 32.4.1**: for a proper convex `f` and a non-empty `S` on which `f` is not constant,
if the supremum of `f` relative to `S` is attained at `x ∈ ri (dom f)`, then every `x* ∈ ∂f(x)` is
non-zero and the *linear* function `⟨·, x*⟩` attains its supremum relative to `S` at `x`.

Rockafellar passes to `C = conv S` so that Theorem 32.4 applies to a convex set. That detour is
unnecessary: `theorem_32_4_normal` asks nothing of `C`, so it applies to `S` itself. -/
theorem corollary_32_4_1 (hp : Proper f) {S : Set (Rn n)} {x : Rn n} (hxri : x ∈ ri (dom f))
    (hmax : ∀ z ∈ S, f z ≤ f x) {z₀ : Rn n} (hz₀ : z₀ ∈ S) (hne : f z₀ ≠ f x)
    {y : Rn n} (hy : y ∈ subdifferential (pairing n) f x) :
    y ≠ 0 ∧ ∀ z ∈ S, pairing n z y ≤ pairing n x y := by
  refine ⟨ne_zero_of_mem_subdifferential_of_isMaxOn hmax hz₀ hne hy, fun z hz => ?_⟩
  exact le_of_mem_normalCone (mem_normalCone_of_mem_subdifferential_of_isMaxOn (hp.ne_bot x)
    (mem_dom.1 (intrinsicInterior_subset hxri)).ne hmax hy) hz

/-- **§32**: the vectors normal to the Euclidean unit ball at a boundary
point `x` are exactly the `λx` with `λ ≥ 0`.

`pairing n` is an `abbrev` for `innerₗ (Rn n)`, so this is the backbone's
`normalCone_innerₗ_closedBall`, which holds in any real inner-product space. -/
theorem normalCone_closedBall {x : Rn n} (hx : ‖x‖ = 1) :
    normalCone (pairing n) (Metric.closedBall (0 : Rn n) 1) x
      = {y : Rn n | ∃ lam : ℝ, 0 ≤ lam ∧ y = lam • x} :=
  normalCone_innerₗ_closedBall hx

/-- **§32**: at a maximiser of `f` over the unit Euclidean ball, maximisation leads to the
"eigenvalue" condition `λx ∈ ∂f(x)`, `|x| = 1`. -/
theorem theorem_32_4_ball {x : Rn n} (hx : ‖x‖ = 1)
    (hfin : ∀ z ∈ Metric.closedBall (0 : Rn n) 1, f z ≠ ⊥ ∧ f z ≠ ⊤)
    (hmax : ∀ z ∈ Metric.closedBall (0 : Rn n) 1, f z ≤ f x) {z₀ : Rn n}
    (hz₀ : z₀ ∈ Metric.closedBall (0 : Rn n) 1) (hne : f z₀ ≠ f x) {y : Rn n}
    (hy : y ∈ subdifferential (pairing n) f x) : ∃ lam : ℝ, 0 < lam ∧ y = lam • x := by
  have hxmem : x ∈ Metric.closedBall (0 : Rn n) 1 := by
    rw [Metric.mem_closedBall, dist_zero_right, hx]
  have hyne : y ≠ 0 := theorem_32_4_ne_zero hmax hz₀ hne hy
  have hnormal := theorem_32_4_normal hfin hxmem hmax hy
  rw [normalCone_closedBall hx] at hnormal
  obtain ⟨lam, hlam, rfl⟩ := hnormal
  refine ⟨lam, lt_of_le_of_ne hlam ?_, rfl⟩
  rintro rfl
  exact hyne (by simp)

/-- **§32.** The parabolic convex set `K = {(ξ₁, ξ₂) | ξ₁² + 4ξ₂ + 4 ≤ 0}`, whose support function
is `parabolicFn`. -/
def parabolicSet : Set (Rn 2) := {y : Rn 2 | y 0 ^ 2 + 4 * y 1 + 4 ≤ 0}

theorem mem_parabolicSet {y : Rn 2} :
    y ∈ parabolicSet ↔ y 0 ^ 2 + 4 * y 1 + 4 ≤ 0 := Iff.rfl

/-- The boundary point of `parabolicSet` with abscissa `t`. -/
private noncomputable def parabolicPoint (t : ℝ) : Rn 2 :=
  WithLp.toLp 2 ![t, -(t ^ 2 + 4) / 4]

private theorem parabolicPoint_zero (t : ℝ) : parabolicPoint t 0 = t := rfl

private theorem parabolicPoint_one (t : ℝ) : parabolicPoint t 1 = -(t ^ 2 + 4) / 4 := rfl

private theorem parabolicPoint_mem (t : ℝ) : parabolicPoint t ∈ parabolicSet := by
  rw [mem_parabolicSet, parabolicPoint_zero, parabolicPoint_one]
  exact le_of_eq (by ring)

/-- The point `(0, s)` of `ℝ²`. -/
private noncomputable def verticalPoint (s : ℝ) : Rn 2 := WithLp.toLp 2 ![0, s]

private theorem verticalPoint_zero (s : ℝ) : verticalPoint s 0 = 0 := rfl

private theorem verticalPoint_one (s : ℝ) : verticalPoint s 1 = s := rfl

private theorem verticalPoint_mem {s : ℝ} (hs : s ≤ -1) : verticalPoint s ∈ parabolicSet := by
  rw [mem_parabolicSet, verticalPoint_zero, verticalPoint_one]
  nlinarith

/-- **§32.** The closed proper convex function `f(ξ₁, ξ₂) = ξ₁²/ξ₂ − ξ₂` for `ξ₂ > 0`, `0` at the
origin, `+∞` elsewhere. Lean's `x / 0 = 0` makes the first branch compute the second, so one
`⨅ _ : p, …` suffices. -/
noncomputable def parabolicFn (x : Rn 2) : EReal :=
  ⨅ _ : 0 ≤ x 1 ∧ (x 1 = 0 → x 0 = 0), ((x 0 ^ 2 / x 1 - x 1 : ℝ) : EReal)

theorem parabolicFn_of_mem {x : Rn 2} (hx : 0 ≤ x 1 ∧ (x 1 = 0 → x 0 = 0)) :
    parabolicFn x = ((x 0 ^ 2 / x 1 - x 1 : ℝ) : EReal) := iInf_pos hx

theorem parabolicFn_of_notMem {x : Rn 2} (hx : ¬ (0 ≤ x 1 ∧ (x 1 = 0 → x 0 = 0))) :
    parabolicFn x = ⊤ := iInf_neg hx

/-- **§32**: `f` is the support function of the parabolic set, which is the verification of
convexity and closedness the book suggests in its own parenthesis. -/
theorem supportFn_parabolicSet : supportFn (pairing 2) parabolicSet = parabolicFn := by
  funext y
  by_cases hy : 0 ≤ y 1 ∧ (y 1 = 0 → y 0 = 0)
  · rw [parabolicFn_of_mem hy]
    rcases lt_or_eq_of_le hy.1 with hy1 | hy1
    · have hy1ne : y 1 ≠ 0 := ne_of_gt hy1
      refine le_antisymm (supportFn_le_coe_iff.2 fun x hx => ?_) ?_
      · have hx' : x 0 ^ 2 + 4 * x 1 + 4 ≤ 0 := hx
        rw [pairing_two, le_sub_iff_add_le, le_div_iff₀ hy1]
        nlinarith [sq_nonneg (2 * y 0 - x 0 * y 1),
          mul_nonneg (sq_nonneg (y 1)) (by linarith : (0 : ℝ) ≤ -(x 0 ^ 2 + 4 * x 1 + 4))]
      · have hval : pairing 2 (parabolicPoint (2 * y 0 / y 1)) y = y 0 ^ 2 / y 1 - y 1 := by
          rw [pairing_two, parabolicPoint_zero, parabolicPoint_one]
          field_simp
          ring
        rw [← hval]
        exact le_supportFn (parabolicPoint_mem _) y
    · have hy1' : y 1 = 0 := hy1.symm
      have hy0 : y 0 = 0 := hy.2 hy1'
      have hzero : ∀ x : Rn 2, pairing 2 x y = 0 := by
        intro x; rw [pairing_two, hy0, hy1']; ring
      have hsup : supportFn (pairing 2) parabolicSet y = ((0 : ℝ) : EReal) := by
        refine le_antisymm (supportFn_le_coe_iff.2 fun x _ => le_of_eq (hzero x)) ?_
        rw [← hzero (parabolicPoint 0)]
        exact le_supportFn (parabolicPoint_mem 0) y
      rw [hsup, hy0, hy1']
      norm_num
  · rw [parabolicFn_of_notMem hy, EReal.eq_top_iff_forall_lt]
    intro c
    by_cases hy1 : 0 ≤ y 1
    · have hy1' : y 1 = 0 := by
        by_contra h
        exact hy ⟨hy1, fun hc => absurd hc h⟩
      have hy0 : y 0 ≠ 0 := fun h => hy ⟨hy1, fun _ => h⟩
      have hval : pairing 2 (parabolicPoint ((c + 1) / y 0)) y = c + 1 := by
        rw [pairing_two, parabolicPoint_zero, hy1', mul_zero, add_zero]
        field_simp
      have hle := le_supportFn (B := pairing 2) (parabolicPoint_mem ((c + 1) / y 0)) y
      rw [hval] at hle
      exact lt_of_lt_of_le (by exact_mod_cast (by linarith : c < c + 1)) hle
    · have hyneg : y 1 < 0 := not_le.1 hy1
      have hy1ne : y 1 ≠ 0 := ne_of_lt hyneg
      have hnn : 0 ≤ (|c| + 1) / (-y 1) := div_nonneg (by positivity) (by linarith)
      have hs : -1 - (|c| + 1) / (-y 1) ≤ -1 := by linarith
      have hval : pairing 2 (verticalPoint (-1 - (|c| + 1) / (-y 1))) y = -y 1 + (|c| + 1) := by
        rw [pairing_two, verticalPoint_zero, verticalPoint_one]
        field_simp
        ring
      have hle := le_supportFn (B := pairing 2) (verticalPoint_mem hs) y
      rw [hval] at hle
      refine lt_of_lt_of_le ?_ hle
      exact_mod_cast (by cases abs_cases c <;> linarith : c < -y 1 + (|c| + 1))

theorem convexFn_parabolicFn : ConvexFn parabolicFn := by
  rw [← supportFn_parabolicSet]; exact convexFn_supportFn _ _

theorem closedFn_parabolicFn : ClosedFn parabolicFn := by
  rw [← supportFn_parabolicSet]; exact closedFn_supportFn

theorem proper_parabolicFn : Proper parabolicFn := by
  rw [← supportFn_parabolicSet]
  exact proper_supportFn ⟨parabolicPoint 0, parabolicPoint_mem 0⟩

/-! #### The two caps -/

private def cap (g : ℝ → ℝ) : Set (Rn 2) := {x : Rn 2 | g (x 0) ≤ x 1 ∧ x 1 ≤ 1}

private theorem zero_mem_cap {g : ℝ → ℝ} (hg0 : g 0 ≤ 0) : (0 : Rn 2) ∈ cap g := by
  have h0 : (0 : Rn 2) 0 = 0 := by simp
  have h1 : (0 : Rn 2) 1 = 0 := by simp
  exact ⟨by rw [h0, h1]; exact hg0, by rw [h1]; norm_num⟩

private theorem isClosed_cap {g : ℝ → ℝ} (hgc : Continuous g) : IsClosed (cap g) := by
  have hc0 : Continuous fun x : Rn 2 => x 0 := by fun_prop
  have hc1 : Continuous fun x : Rn 2 => x 1 := by fun_prop
  have hcg : Continuous fun x : Rn 2 => g (x 0) := hgc.comp hc0
  exact (isClosed_le hcg hc1).inter (isClosed_le hc1 continuous_const)

private theorem isBounded_cap {g : ℝ → ℝ} (hgnn : ∀ t : ℝ, 0 ≤ g t)
    (hgsq : ∀ t : ℝ, g t ≤ 1 → t ^ 2 ≤ 1) : Bornology.IsBounded (cap g) := by
  rw [isBounded_iff_forall_norm_le]
  refine ⟨2, fun x hx => ?_⟩
  have hx1nn : 0 ≤ x 1 := le_trans (hgnn _) hx.1
  have hsq : x 0 ^ 2 ≤ 1 := hgsq _ (le_trans hx.1 hx.2)
  have hnorm : ‖x‖ = Real.sqrt (x 0 ^ 2 + x 1 ^ 2) := by
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
    congr 1
    rw [Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
  rw [hnorm]
  have hle : x 0 ^ 2 + x 1 ^ 2 ≤ 4 := by nlinarith [hx.2]
  calc Real.sqrt (x 0 ^ 2 + x 1 ^ 2) ≤ Real.sqrt 4 := Real.sqrt_le_sqrt hle
    _ = 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]

/-- The convexity inequality for `t ↦ t²` in the form `convex_cap` consumes. -/
private theorem sq_combo_le {p q a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (a * p + b * q) ^ 2 ≤ a * p ^ 2 + b * q ^ 2 := by
  have key : a * p ^ 2 + b * q ^ 2 - (a * p + b * q) ^ 2 = a * b * (p - q) ^ 2 := by
    linear_combination (-(a * p ^ 2 + b * q ^ 2)) * hab
  nlinarith [mul_nonneg (mul_nonneg ha hb) (sq_nonneg (p - q))]

/-- The convexity inequality for `t ↦ t⁴`: square the one for `t ↦ t²` twice. -/
private theorem quartic_combo_le {p q a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (a * p + b * q) ^ 4 ≤ a * p ^ 4 + b * q ^ 4 :=
  calc (a * p + b * q) ^ 4 = ((a * p + b * q) ^ 2) ^ 2 := by ring
    _ ≤ (a * p ^ 2 + b * q ^ 2) ^ 2 :=
        pow_le_pow_left₀ (sq_nonneg _) (sq_combo_le ha hb hab) 2
    _ ≤ a * (p ^ 2) ^ 2 + b * (q ^ 2) ^ 2 := sq_combo_le ha hb hab
    _ = a * p ^ 4 + b * q ^ 4 := by ring

private theorem convex_cap {g : ℝ → ℝ}
    (hg : ∀ p q a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      g (a * p + b * q) ≤ a * g p + b * g q) :
    Convex ℝ (cap g) := by
  intro x hx y hy a b ha hb hab
  have h0 : (a • x + b • y) 0 = a * x 0 + b * y 0 := rfl
  have h1 : (a • x + b • y) 1 = a * x 1 + b * y 1 := rfl
  have hcv := hg (x 0) (y 0) a b ha hb hab
  refine ⟨?_, ?_⟩
  · rw [h0, h1]
    have h₁ := mul_le_mul_of_nonneg_left hx.1 ha
    have h₂ := mul_le_mul_of_nonneg_left hy.1 hb
    linarith
  · rw [h1]
    have h₁ := mul_le_mul_of_nonneg_left hx.2 ha
    have h₂ := mul_le_mul_of_nonneg_left hy.2 hb
    linarith

private theorem parabolicFn_cap {g : ℝ → ℝ} (hgnn : ∀ t : ℝ, 0 ≤ g t)
    (hgz : ∀ t : ℝ, g t ≤ 0 → t = 0) {x : Rn 2} (hx : x ∈ cap g) :
    parabolicFn x = ((x 0 ^ 2 / x 1 - x 1 : ℝ) : EReal) :=
  parabolicFn_of_mem ⟨le_trans (hgnn _) hx.1, fun h => hgz _ (h ▸ hx.1)⟩

private theorem cap_subset_dom {g : ℝ → ℝ} (hgnn : ∀ t : ℝ, 0 ≤ g t)
    (hgz : ∀ t : ℝ, g t ≤ 0 → t = 0) : cap g ⊆ dom parabolicFn := fun x hx => by
  rw [mem_dom, parabolicFn_cap hgnn hgz hx]
  exact EReal.coe_lt_top _

private noncomputable def capPoint (k : ℕ) (t : ℝ) : Rn 2 := WithLp.toLp 2 ![t, t ^ k]

private theorem capPoint_zero (k : ℕ) (t : ℝ) : capPoint k t 0 = t := rfl

private theorem capPoint_one (k : ℕ) (t : ℝ) : capPoint k t 1 = t ^ k := rfl

private theorem capPoint_mem {k : ℕ} {t : ℝ} (ht : t ^ k ≤ 1) :
    capPoint k t ∈ cap (fun s : ℝ => s ^ k) :=
  ⟨le_of_eq (by rw [capPoint_zero, capPoint_one]), by rw [capPoint_one]; exact ht⟩

private theorem sq_nonneg' : ∀ t : ℝ, 0 ≤ t ^ 2 := fun t => sq_nonneg t

private theorem sq_eq_zero' : ∀ t : ℝ, t ^ 2 ≤ 0 → t = 0 := fun t h =>
  pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm h (sq_nonneg t))

private theorem quartic_nonneg : ∀ t : ℝ, 0 ≤ t ^ 4 := fun t => by positivity

private theorem quartic_eq_zero : ∀ t : ℝ, t ^ 4 ≤ 0 → t = 0 := fun t h =>
  pow_eq_zero_iff (by norm_num) |>.1 (le_antisymm h (by positivity))

/-- **§32.** `C = {(ξ₁, ξ₂) | ξ₁² ≤ ξ₂ ≤ 1}`. -/
def parabolicCap : Set (Rn 2) := {x : Rn 2 | x 0 ^ 2 ≤ x 1 ∧ x 1 ≤ 1}

/-- **§32.** `D = {(ξ₁, ξ₂) | ξ₁⁴ ≤ ξ₂ ≤ 1}`. -/
def quarticCap : Set (Rn 2) := {x : Rn 2 | x 0 ^ 4 ≤ x 1 ∧ x 1 ≤ 1}

private theorem parabolicCap_eq : parabolicCap = cap (fun t : ℝ => t ^ 2) := rfl

private theorem quarticCap_eq : quarticCap = cap (fun t : ℝ => t ^ 4) := rfl

theorem zero_mem_parabolicCap : (0 : Rn 2) ∈ parabolicCap := by
  rw [parabolicCap_eq]; exact zero_mem_cap (by norm_num)

theorem isClosed_parabolicCap : IsClosed parabolicCap := by
  rw [parabolicCap_eq]; exact isClosed_cap (by fun_prop)

theorem isBounded_parabolicCap : Bornology.IsBounded parabolicCap := by
  rw [parabolicCap_eq]; exact isBounded_cap sq_nonneg' fun _ h => h

theorem convex_parabolicCap : Convex ℝ parabolicCap := by
  rw [parabolicCap_eq]; exact convex_cap fun _ _ _ _ ha hb hab => sq_combo_le ha hb hab

theorem parabolicCap_subset_dom : parabolicCap ⊆ dom parabolicFn := by
  rw [parabolicCap_eq]; exact cap_subset_dom sq_nonneg' sq_eq_zero'

theorem zero_mem_quarticCap : (0 : Rn 2) ∈ quarticCap := by
  rw [quarticCap_eq]; exact zero_mem_cap (by norm_num)

theorem isClosed_quarticCap : IsClosed quarticCap := by
  rw [quarticCap_eq]; exact isClosed_cap (by fun_prop)

theorem isBounded_quarticCap : Bornology.IsBounded quarticCap := by
  rw [quarticCap_eq]
  exact isBounded_cap quartic_nonneg fun t h => by nlinarith [sq_nonneg t, sq_nonneg (t ^ 2 - 1)]

theorem convex_quarticCap : Convex ℝ quarticCap := by
  rw [quarticCap_eq]; exact convex_cap fun _ _ _ _ ha hb hab => quartic_combo_le ha hb hab

theorem quarticCap_subset_dom : quarticCap ⊆ dom parabolicFn := by
  rw [quarticCap_eq]; exact cap_subset_dom quartic_nonneg quartic_eq_zero

/-! #### The first example: a supremum that is not attained -/

/-- **§32**: "clearly `f(ξ₁, ξ₂) < 1` throughout `C`". On `C` one has `ξ₁² ≤ ξ₂`, so `ξ₁²/ξ₂ ≤ 1`
and `f ≤ 1 − ξ₂ < 1` when `ξ₂ > 0`; and `ξ₂ = 0` forces the origin, where `f = 0`. -/
theorem parabolicFn_lt_one_of_mem_parabolicCap {x : Rn 2} (hx : x ∈ parabolicCap) :
    parabolicFn x < ((1 : ℝ) : EReal) := by
  rw [parabolicFn_cap (g := fun t : ℝ => t ^ 2) sq_nonneg' sq_eq_zero' hx,
    EReal.coe_lt_coe_iff]
  rcases eq_or_lt_of_le (le_trans (sq_nonneg (x 0)) hx.1) with h | h
  · have hx0 : x 0 = 0 := sq_eq_zero' _ (h ▸ hx.1)
    rw [hx0, ← h]
    norm_num
  · have hdiv : x 0 ^ 2 / x 1 ≤ 1 := (div_le_one h).2 hx.1
    linarith

/-- **§32**: "the value of `f(ξ₁, ξ₂)` approaches `1` as `(ξ₁, ξ₂)` moves toward `(0, 0)` along the
boundary of `C`." On the boundary parabola `ξ₂ = ξ₁²` the value is exactly `1 − t²`. -/
theorem parabolicFn_capPoint {t : ℝ} (ht : t ≠ 0) (ht1 : t ^ 2 ≤ 1) :
    parabolicFn (capPoint 2 t) = ((1 - t ^ 2 : ℝ) : EReal) := by
  rw [parabolicFn_cap sq_nonneg' sq_eq_zero' (capPoint_mem ht1), capPoint_zero, capPoint_one,
    div_self (pow_ne_zero 2 ht)]

/-- **§32**: "thus `1` is the supremum of `f` relative to `C`, and this supremum is not attained."
Given a candidate maximiser with value `r < 1`, the boundary point `(t, t²)` with
`t = min 1 ((1 − r)/2)` lies in `C` and carries the strictly larger value `1 − t²`. -/
theorem parabolicCap_not_attained :
    ¬ ∃ z ∈ parabolicCap, ∀ w ∈ parabolicCap, parabolicFn w ≤ parabolicFn z := by
  rintro ⟨z, hz, hzmax⟩
  have hfz : parabolicFn z = ((z 0 ^ 2 / z 1 - z 1 : ℝ) : EReal) :=
    parabolicFn_cap (g := fun t : ℝ => t ^ 2) sq_nonneg' sq_eq_zero' hz
  have hr1 : z 0 ^ 2 / z 1 - z 1 < 1 := by
    have hlt := parabolicFn_lt_one_of_mem_parabolicCap hz
    rw [hfz, EReal.coe_lt_coe_iff] at hlt
    exact hlt
  have ht0 : 0 < min 1 ((1 - (z 0 ^ 2 / z 1 - z 1)) / 2) := lt_min one_pos (by linarith)
  have ht1 : min 1 ((1 - (z 0 ^ 2 / z 1 - z 1)) / 2) ≤ 1 := min_le_left _ _
  have ht2 : min 1 ((1 - (z 0 ^ 2 / z 1 - z 1)) / 2) ≤ (1 - (z 0 ^ 2 / z 1 - z 1)) / 2 :=
    min_le_right _ _
  have hsq : min 1 ((1 - (z 0 ^ 2 / z 1 - z 1)) / 2) ^ 2 ≤ 1 := pow_le_one₀ ht0.le ht1
  have hmem : capPoint 2 (min 1 ((1 - (z 0 ^ 2 / z 1 - z 1)) / 2)) ∈ parabolicCap := by
    rw [parabolicCap_eq]; exact capPoint_mem hsq
  have hle := hzmax _ hmem
  rw [parabolicFn_capPoint (ne_of_gt ht0) hsq, hfz, EReal.coe_le_coe_iff] at hle
  nlinarith

/-! #### The second example: a supremum that is not finite -/

/-- **§32**: "along the boundary curve `ξ₁⁴ = ξ₂` of `D`, the value of `f(ξ₁, ξ₂)` is `ξ₁⁻² − ξ₂`,
and this rises to `+∞` as `(ξ₁, ξ₂)` moves toward the origin. Thus `f` is not even bounded above on
`D`." Given a candidate bound `r`, the boundary point `(t, t⁴)` with `t = min 1 (1/(|r| + 2))` lies
in `D` and carries a value at least `(|r| + 2)² − 1 > r`. -/
theorem quarticCap_not_bddAbove :
    ¬ ∃ r : ℝ, ∀ w ∈ quarticCap, parabolicFn w ≤ (r : EReal) := by
  rintro ⟨r, hr⟩
  have hM1 : (1 : ℝ) ≤ |r| + 2 := by cases abs_cases r <;> linarith
  have hM0 : (0 : ℝ) < |r| + 2 := by linarith
  have hrM : r ≤ |r| + 2 - 2 := by cases abs_cases r <;> linarith
  have ht0 : 0 < min 1 (1 / (|r| + 2)) := lt_min one_pos (by positivity)
  have ht1 : min 1 (1 / (|r| + 2)) ≤ 1 := min_le_left _ _
  have htM : min 1 (1 / (|r| + 2)) ≤ 1 / (|r| + 2) := min_le_right _ _
  have hmt : min 1 (1 / (|r| + 2)) * (|r| + 2) ≤ 1 := (le_div_iff₀ hM0).1 htM
  have hq1 : min 1 (1 / (|r| + 2)) ^ 4 ≤ 1 := pow_le_one₀ ht0.le ht1
  have hmem : capPoint 4 (min 1 (1 / (|r| + 2))) ∈ quarticCap := by
    rw [quarticCap_eq]; exact capPoint_mem hq1
  have hval : parabolicFn (capPoint 4 (min 1 (1 / (|r| + 2))))
      = ((min 1 (1 / (|r| + 2)) ^ 2 / min 1 (1 / (|r| + 2)) ^ 4
          - min 1 (1 / (|r| + 2)) ^ 4 : ℝ) : EReal) := by
    rw [parabolicFn_cap quartic_nonneg quartic_eq_zero (capPoint_mem hq1), capPoint_zero,
      capPoint_one]
  have hsq : min 1 (1 / (|r| + 2)) ^ 2 * (|r| + 2) ^ 2 ≤ 1 := by
    nlinarith [mul_pos ht0 hM0]
  have hbig : (|r| + 2) ^ 2 ≤ min 1 (1 / (|r| + 2)) ^ 2 / min 1 (1 / (|r| + 2)) ^ 4 := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (min 1 (1 / (|r| + 2))), pow_pos ht0 2]
  have hle := hr _ hmem
  rw [hval, EReal.coe_le_coe_iff] at hle
  nlinarith

/-! #### The weakening of Corollary 32.3.2 that the two examples refute -/

/-- **§32**, first half of the remark the two examples exist for, *stated and refuted*: Corollary
32.3.2 with `C ⊆ ri (dom f)` weakened to `C ⊆ dom f` would say that the supremum is still attained.
It is not, and adding `ClosedFn` and `Proper` — the book's "even when `f` is closed" — does not save
it. The witness is `parabolicCap`. -/
theorem corollary_32_3_2_not_attained_of_subset_dom :
    ¬ ∀ (g : Rn 2 → EReal) (D : Set (Rn 2)), ConvexFn g → ClosedFn g → Proper g →
        D.Nonempty → IsClosed D → Bornology.IsBounded D → Convex ℝ D → D ⊆ dom g →
        ∃ z ∈ D, ∀ w ∈ D, g w ≤ g z := fun h =>
  parabolicCap_not_attained (h parabolicFn parabolicCap convexFn_parabolicFn
    closedFn_parabolicFn proper_parabolicFn ⟨0, zero_mem_parabolicCap⟩ isClosed_parabolicCap
    isBounded_parabolicCap convex_parabolicCap parabolicCap_subset_dom)

/-- **§32**, second half, *stated and refuted*: the same weakening would say that the supremum is
still finite. The witness is `quarticCap`, on which `f` is not even bounded above. -/
theorem corollary_32_3_2_not_bddAbove_of_subset_dom :
    ¬ ∀ (g : Rn 2 → EReal) (D : Set (Rn 2)), ConvexFn g → ClosedFn g → Proper g →
        D.Nonempty → IsClosed D → Bornology.IsBounded D → Convex ℝ D → D ⊆ dom g →
        ∃ r : ℝ, ∀ w ∈ D, g w ≤ (r : EReal) := fun h =>
  quarticCap_not_bddAbove (h parabolicFn quarticCap convexFn_parabolicFn
    closedFn_parabolicFn proper_parabolicFn ⟨0, zero_mem_quarticCap⟩ isClosed_quarticCap
    isBounded_quarticCap convex_quarticCap quarticCap_subset_dom)

end Rockafellar
