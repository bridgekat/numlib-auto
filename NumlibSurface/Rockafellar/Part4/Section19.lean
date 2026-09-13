import Numlib.Analysis.Convex.HellyRefined
import Numlib.Analysis.Convex.Optimization.Perturbation
import Numlib.Analysis.Convex.Polyhedral.Closedness
import Numlib.Analysis.Convex.Polyhedral.Conjugate
import Numlib.Analysis.Convex.Polyhedral.Faces
import Numlib.Analysis.Convex.Polyhedral.NormalForm
import Numlib.Analysis.Convex.Polyhedral.Recession
import Numlib.Analysis.Convex.Polyhedral.Simplicial
import Numlib.Analysis.Convex.Representation
import NumlibSurface.Rockafellar.Part2.Section09

/-!
# Rockafellar, §19: Polyhedral Convex Sets and Functions

The Minkowski–Weyl theorem and the polyhedral calculus, over `Rn n = ℝⁿ`.

All seventeen numbered results of §19 are formalized: Theorems 19.1–19.7 and Corollaries 19.1.1,
19.1.2, 19.2.1, 19.2.2, 19.3.1–19.3.4, 19.5.1, 19.7.1, together with the unnumbered normal form
`f = h + δ(· | C)`.

The section's five notions are the backbone's. A **polyhedral convex set** is `Polyhedral`, the
solution set of finitely many weak linear inequalities; a **polyhedral convex cone** is
`PolyhedralCone`; a **finitely generated convex set** is `FinitelyGenerated`, that is `convexHullPD`
of a finite set of points and directions; a **polytope** is `IsPolytope`, a bounded set of either
kind; and a **polyhedral convex function** is `PolyhedralFn f := Polyhedral (epi f)`, with
`FinitelyGeneratedFn` its generated twin.

Theorems 19.6 and 19.7 and Corollary 19.5.1 use Rockafellar's extended coefficient `λ ≥ 0⁺`,
modelled by §9's `ExtCoeff`: `ExtCoeff.smulSet` sends `0⁺` to the recession cone and
`ExtCoeff.smulFn` to the recession function.

Every statement of §19 is correct as printed; two of its proofs are not. Theorem 19.1's
(b) ⇒ (a) reduces without justification to the `n`-dimensional case, and is proved here through
clause (c) instead; Theorem 19.6 is printed with no proof paragraph at all.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §19.
-/

namespace Rockafellar

open ConvexAnalysis NumlibSurface

open scoped Pointwise

variable {n m : ℕ}

/-! ### The book's spellings of the two definitions -/

/-- **§19**: a **polytope** is a bounded finitely generated convex set — equivalently
(`isPolytope_iff`) a bounded polyhedral convex set. -/
def IsPolytope (C : Set (Rn n)) : Prop := ∃ P : Finset (Rn n), C = convexHull ℝ (P : Set (Rn n))

/-- **§19**: a convex function is **finitely generated** when its epigraph is a finitely generated
convex set in `ℝⁿ⁺¹`. The book defines it by an infimum formula and then observes, before Corollary
19.1.2, that this says `f x = inf {μ | (x, μ) ∈ F}` for `F` the hull of the points `(aᵢ, αᵢ)`,
their directions and the direction `(0, 1)`; the generator `(0, 1)` is absorbed here into the
requirement that the generated set be an epigraph. -/
def FinitelyGeneratedFn (f : Rn n → EReal) : Prop := FinitelyGenerated (epi f)

/-- A polytope is exactly a bounded polyhedral convex set. -/
theorem isPolytope_iff {C : Set (Rn n)} :
    IsPolytope C ↔ Polyhedral C ∧ Bornology.IsBounded C := by
  constructor
  · rintro ⟨P, rfl⟩
    exact ⟨polyhedral_convexHull_finset P,
      (P.finite_toSet.isCompact.convexHull).isBounded⟩
  · rintro ⟨hC, hb⟩
    exact hC.exists_finset_convexHull hb

/-! ### Theorem 19.1 -/

/-- **Theorem 19.1** (Minkowski–Weyl), clauses (a) and (c): a convex set is *polyhedral* — an
intersection of finitely many closed half-spaces — iff it is *finitely generated*, the convex hull
of a finite set of points and directions. -/
theorem theorem_19_1 {C : Set (Rn n)} : Polyhedral C ↔ FinitelyGenerated C :=
  polyhedral_iff_finitelyGenerated

/-- **Theorem 19.1**, clause (a) in the book's notation: `C` is polyhedral exactly when it solves a
finite system `⟨x, bᵢ⟩ ≤ βᵢ` in *vectors* `bᵢ`. The backbone quantifies over linear functionals,
which the pairing represents on `ℝⁿ`. -/
theorem theorem_19_1_pairing {C : Set (Rn n)} :
    Polyhedral C ↔ ∃ s : Finset (Rn n × ℝ), C = {x : Rn n | ∀ q ∈ s, pairing n x q.1 ≤ q.2} := by
  classical
  refine ⟨fun hC => hC.exists_finset_pairing, ?_⟩
  rintro ⟨s, rfl⟩
  refine ⟨s.image fun q => ((pairing n).flip q.1, q.2), ?_⟩
  ext x
  simp only [Set.mem_ofPred_eq, Finset.mem_image]
  constructor
  · rintro h q ⟨p, hp, rfl⟩
    exact h p hp
  · intro h q hq
    exact h ((pairing n).flip q.1, q.2) ⟨q, hq, rfl⟩

/-- **Theorem 19.1**, clause (c) in the book's notation: `C` is finitely generated exactly when
`C = conv S` for a finite set `S` of points and directions. -/
theorem theorem_19_1_convexHullPD {C : Set (Rn n)} :
    FinitelyGenerated C ↔ ∃ P D : Finset (Rn n),
      C = convexHullPD (P : Set (Rn n)) (D : Set (Rn n)) := Iff.rfl

/-- **Theorem 19.1**, first half of clause (b): a polyhedral convex set is closed. -/
theorem theorem_19_1_isClosed {C : Set (Rn n)} (hC : Polyhedral C) : IsClosed C :=
  hC.isClosed

/-- **Theorem 19.1**, second half of clause (b): a polyhedral convex set has finitely many
faces. -/
theorem theorem_19_1_finite_faces {C : Set (Rn n)} (hC : Polyhedral C) :
    {C' : Set (Rn n) | IsFace C C'}.Finite :=
  hC.finite_setOf_isFace

/-- **Theorem 19.1**, (b) ⇒ (c): a closed convex set with finitely many faces is finitely
generated. -/
theorem theorem_19_1_finitelyGenerated_of_finite_faces {C : Set (Rn n)} (hC : Convex ℝ C)
    (hCcl : IsClosed C) (hfin : {C' : Set (Rn n) | IsFace C C'}.Finite) :
    FinitelyGenerated C :=
  finitelyGenerated_of_finite_setOf_isFace hC hCcl hfin

/-- **Theorem 19.1**, (b) ⇒ (a): a closed convex set with finitely many faces is polyhedral.

**The book's proof of this implication has a hole**: it writes "it suffices to treat the case where
`C` is `n`-dimensional in `Rⁿ`" with no justification, then runs the tangent half-spaces of Theorem
18.8 over that case. The route taken here avoids the reduction — (b) ⇒ (c) ⇒ (a) — and never uses
Theorem 18.8 or counts a dimension. -/
theorem theorem_19_1_of_finite_faces {C : Set (Rn n)} (hC : Convex ℝ C) (hCcl : IsClosed C)
    (hfin : {C' : Set (Rn n) | IsFace C C'}.Finite) : Polyhedral C :=
  polyhedral_of_finite_setOf_isFace hC hCcl hfin

/-- **Theorem 19.1**, clauses (a) and (b): a convex set is polyhedral iff it is closed and has
finitely many faces. With `theorem_19_1` this completes the three-way statement. -/
theorem theorem_19_1_iff_finite_faces {C : Set (Rn n)} (hC : Convex ℝ C) :
    Polyhedral C ↔ IsClosed C ∧ {C' : Set (Rn n) | IsFace C C'}.Finite :=
  polyhedral_iff_isClosed_finite_setOf_isFace hC

/-- **§19**, the remark after Theorem 19.1: a face of a polyhedral convex set is polyhedral. -/
theorem theorem_19_1_face {C C' : Set (Rn n)} (hC : Polyhedral C) (hface : IsFace C C') :
    Polyhedral C' :=
  hC.of_isFace hface

/-! ### Corollary 19.1.1 -/

/-- **Corollary 19.1.1**, the points half: a polyhedral convex set has finitely many extreme
points. -/
theorem corollary_19_1_1_extremePoints {C : Set (Rn n)} (hC : Polyhedral C) :
    (C.extremePoints ℝ).Finite :=
  hC.finitelyGenerated.finite_extremePoints

/-- **Corollary 19.1.1**, the directions half: a polyhedral convex set has finitely many extreme
directions. This cannot read `(extremeDirections C).Finite`: a direction is recorded by a
generating vector, so `extremeDirections C` is closed under positive rescaling and is infinite as
soon as it is non-empty. The finiteness is stated up to positive scaling, which is what the book
means. -/
theorem corollary_19_1_1_extremeDirections {C : Set (Rn n)} (hC : Polyhedral C) :
    ∃ D : Finset (Rn n), ∀ y ∈ extremeDirections C,
      ∃ z ∈ (D : Set (Rn n)), ∃ a : ℝ, 0 < a ∧ y = a • z := by
  obtain ⟨P, D, hPD⟩ := hC.finitelyGenerated
  have hPD' : C = convexHullPD (P : Set (Rn n)) (D : Set (Rn n)) := hPD
  refine ⟨D, fun y hy => ?_⟩
  rw [hPD'] at hy
  exact exists_mem_eq_smul_of_mem_extremeDirections_of_isBounded _ _ P.finite_toSet.isBounded hy

/-! ### Corollary 19.1.2 -/

/-- **Corollary 19.1.2**, first sentence: a convex function is polyhedral iff it is finitely
generated. Both sides are Theorem 19.1 applied to the epigraph. -/
theorem corollary_19_1_2 {f : Rn n → EReal} : PolyhedralFn f ↔ FinitelyGeneratedFn f :=
  polyhedral_iff_finitelyGenerated

/-- **Corollary 19.1.2**, second sentence: a proper polyhedral convex function is closed.
Properness cannot be dropped: `f ≡ ⊥` has epigraph `ℝⁿ⁺¹`, polyhedral by the empty system, and is
not closed in the `ClosedFn` sense. -/
theorem corollary_19_1_2_closed {f : Rn n → EReal} (hf : PolyhedralFn f) (hp : Proper f) :
    ClosedFn f :=
  hf.closedFn hp.ne_bot

/-- **Corollary 19.1.2**, third sentence: the infimum defining a finitely generated convex function
is attained wherever it is finite. -/
theorem corollary_19_1_2_attained {f : Rn n → EReal} {P D : Finset (Rn n × ℝ)}
    (hPD : epi f = convexHullPD (P : Set (Rn n × ℝ)) (D : Set (Rn n × ℝ)))
    {x : Rn n} {μ : ℝ} (hx : f x = (μ : EReal)) :
    ((x, μ) : Rn n × ℝ) ∈ convexHullPD (P : Set (Rn n × ℝ)) (D : Set (Rn n × ℝ)) := by
  rw [← hPD]
  exact mk_mem_epi.2 (le_of_eq hx)

/-! ### Theorem 19.2 and its corollaries -/

/-- **Theorem 19.2**. The conjugate of a polyhedral convex function is polyhedral. No properness
is assumed, and none is needed. -/
theorem theorem_19_2 {f : Rn n → EReal} (hf : PolyhedralFn f) :
    PolyhedralFn (conj (pairing n) f) :=
  hf.conj

/-- **Corollary 19.2.1**. A closed convex set is polyhedral iff its support function is
polyhedral. -/
theorem corollary_19_2_1 {C : Set (Rn n)} (hconv : Convex ℝ C) (hcl : IsClosed C) :
    Polyhedral C ↔ PolyhedralFn (supportFn (pairing n) C) := by
  constructor
  · intro hC
    rw [supportFn_eq_conj_indicatorFn]
    exact (polyhedralFn_indicatorFn hC).conj
  · intro hs
    have h := hs.conj (B := (pairing n).flip)
    rw [conj_supportFn hconv hcl] at h
    have hd := h.polyhedral_dom
    rwa [dom_indicatorFn] at hd

/-- **Corollary 19.2.2**. The polar of a polyhedral convex set is polyhedral. -/
theorem corollary_19_2_2 {C : Set (Rn n)} (hC : Polyhedral C) :
    Polyhedral (polarSet (pairing n) C) := by
  have hs : PolyhedralFn (supportFn (pairing n) C) := by
    rw [supportFn_eq_conj_indicatorFn]
    exact (polyhedralFn_indicatorFn hC).conj
  have heq : polarSet (pairing n) C
      = {y : Rn n | supportFn (pairing n) C y ≤ ((1 : ℝ) : EReal)} := by
    ext y
    rw [Set.mem_ofPred_eq, supportFn_le_coe_iff, mem_polarSet]
  rw [heq]
  exact hs.polyhedral_sublevel 1

/-! ### Theorem 19.3 and its corollaries -/

/-- **Theorem 19.3**, first half: the image `AC` of a polyhedral convex set under a linear
transformation `A : ℝⁿ → ℝᵐ` is polyhedral. -/
theorem theorem_19_3_image {C : Set (Rn n)} (hC : Polyhedral C) (A : Rn n →ₗ[ℝ] Rn m) :
    Polyhedral (A '' C) :=
  hC.image A

/-- **Theorem 19.3**, second half: the preimage `A⁻¹D` of a polyhedral convex set is
polyhedral. -/
theorem theorem_19_3_preimage {D : Set (Rn m)} (hD : Polyhedral D) (A : Rn n →ₗ[ℝ] Rn m) :
    Polyhedral (A ⁻¹' D) :=
  hD.comap A

/-- **Corollary 19.3.1**, first half: the image `Af` of a polyhedral convex function is
polyhedral. -/
theorem corollary_19_3_1_image {f : Rn n → EReal} (hf : PolyhedralFn f) (A : Rn n →ₗ[ℝ] Rn m) :
    PolyhedralFn (mapLin A f) :=
  polyhedralFn_mapLin hf A

/-- **Corollary 19.3.1**, the attainment clause: the infimum defining `(Af)(y)` is attained
wherever it is finite. -/
theorem corollary_19_3_1_attained {f : Rn n → EReal} (hf : PolyhedralFn f) (A : Rn n →ₗ[ℝ] Rn m)
    {y : Rn m} {μ : ℝ} (hy : mapLin A f y = (μ : EReal)) :
    ∃ x : Rn n, A x = y ∧ f x = mapLin A f y :=
  exists_mapLin_eq_of_polyhedralFn hf A hy

/-- **Corollary 19.3.1**, second half: `gA` is polyhedral for `g` polyhedral. -/
theorem corollary_19_3_1_preimage {g : Rn m → EReal} (hg : PolyhedralFn g)
    (A : Rn n →ₗ[ℝ] Rn m) : PolyhedralFn (compLin g A) :=
  polyhedralFn_compLin hg A

/-- **Corollary 19.3.2**. A sum of two polyhedral convex sets is polyhedral. -/
theorem corollary_19_3_2 {C₁ C₂ : Set (Rn n)} (h₁ : Polyhedral C₁) (h₂ : Polyhedral C₂) :
    Polyhedral (C₁ + C₂) :=
  h₁.add h₂

/-- **Corollary 19.3.3**. Two disjoint polyhedral convex sets can be separated strongly. The
book's non-emptiness hypotheses are kept because the book has them, but are not used: `C₁ - C₂` is
polyhedral hence closed, and Theorem 11.4 applies. -/
theorem corollary_19_3_3 {C₁ C₂ : Set (Rn n)} (h₁ : Polyhedral C₁) (h₂ : Polyhedral C₂)
    (_hne₁ : C₁.Nonempty) (_hne₂ : C₂.Nonempty) (hdisj : Disjoint C₁ C₂) :
    ∃ (φ : Rn n →L[ℝ] ℝ) (c : ℝ), SeparatesStrongly φ c C₁ C₂ :=
  separatesStrongly_of_polyhedral h₁ h₂ hdisj

/-- **Corollary 19.3.4**. The infimal convolute `f₁ □ f₂` of two polyhedral convex functions is
polyhedral. Properness, which the book assumes, is not needed. -/
theorem corollary_19_3_4 {f₁ f₂ : Rn n → EReal} (h₁ : PolyhedralFn f₁) (h₂ : PolyhedralFn f₂) :
    PolyhedralFn (infConv f₁ f₂) :=
  h₁.infConv h₂

/-- **Corollary 19.3.4**, the attainment clause: the infimum defining `(f₁ □ f₂)(x)` is attained
wherever it is finite. -/
theorem corollary_19_3_4_attained {f₁ f₂ : Rn n → EReal} (h₁ : PolyhedralFn f₁)
    (h₂ : PolyhedralFn f₂) {x : Rn n} {μ : ℝ} (hx : infConv f₁ f₂ x = (μ : EReal)) :
    ∃ x₁ x₂ : Rn n, x₁ + x₂ = x ∧ f₁ x₁ + f₂ x₂ ≤ (μ : EReal) := by
  have hmem : ((x, μ) : Rn n × ℝ) ∈ epi (infConv f₁ f₂) := mk_mem_epi.2 (le_of_eq hx)
  rw [epi_infConv_of_polyhedralFn h₁ h₂] at hmem
  obtain ⟨⟨x₁, μ₁⟩, hp₁, ⟨x₂, μ₂⟩, hp₂, hsum⟩ := hmem
  refine ⟨x₁, x₂, congrArg Prod.fst hsum, ?_⟩
  have hμ : μ₁ + μ₂ = μ := congrArg Prod.snd hsum
  calc f₁ x₁ + f₂ x₂ ≤ (μ₁ : EReal) + (μ₂ : EReal) :=
        add_le_add (mk_mem_epi.1 hp₁) (mk_mem_epi.1 hp₂)
    _ = (μ : EReal) := by rw [← EReal.coe_add, hμ]

/-! ### Theorem 19.4 -/

/-- **Theorem 19.4**. A sum of two proper polyhedral convex functions is polyhedral. Properness
enters only as `∀ x, fᵢ x ≠ ⊥`, which is what makes the `EReal` splitting
`f₁ x + f₂ x ≤ μ ↔ ∃ α β, f₁ x ≤ α ∧ f₂ x ≤ β ∧ α + β = μ` valid; `⊤ + ⊥` would break it. -/
theorem theorem_19_4 {f₁ f₂ : Rn n → EReal} (h₁ : PolyhedralFn f₁) (h₂ : PolyhedralFn f₂)
    (hp₁ : Proper f₁) (hp₂ : Proper f₂) : PolyhedralFn (f₁ + f₂) :=
  h₁.add h₂ hp₁.ne_bot hp₂.ne_bot

/-! ### The normal form `f = h + δ(· | C)` -/

/-- **§19**, the unnumbered normal form: `f` is polyhedral convex iff

`f x = h x + δ(x | C)`, with `h x = max {⟨x, b₁⟩ - β₁, …, ⟨x, bₖ⟩ - βₖ}` and
`C = {x | ⟨x, bₖ₊₁⟩ ≤ βₖ₊₁, …, ⟨x, bₘ⟩ ≤ βₘ}`.

The two families are the two kinds of closed half-space that can bound `epi f` in `ℝⁿ⁺¹`: epigraphs
of affine functions, and "vertical" ones. `∀ x, f x ≠ ⊥` cannot be dropped: since `⊥ + ⊤ = ⊥` in
`EReal`, a right-hand side of this shape takes the value `⊥` only inside `C`, whereas the function
that is `⊥` on a non-empty polyhedral `C` and `⊤` outside is convex with polyhedral epigraph. -/
theorem polyhedralFn_iff_normalForm {f : Rn n → EReal} (hb : ∀ x, f x ≠ ⊥) :
    PolyhedralFn f ↔ ∃ (s : Finset (Rn n × ℝ)) (C : Set (Rn n)), Polyhedral C ∧
      ∀ x, f x = (⨆ q ∈ s, ((pairing n x q.1 - q.2 : ℝ) : EReal)) + indicatorFn C x := by
  classical
  have hrep : ∀ φ : Rn n →ₗ[ℝ] ℝ, ∃ a : Rn n, ∀ x, φ x = pairing n x a := by
    intro φ
    obtain ⟨a, ha⟩ := exists_pairing_eq (pairing n) (LinearMap.toContinuousLinearMap φ)
    exact ⟨a, fun x => ha x⟩
  choose rep hrep using hrep
  constructor
  · intro hf
    obtain ⟨s, C, hC, hfC⟩ := (polyhedralFn_iff_maxAffineFn_add_indicatorFn hb).1 hf
    refine ⟨s.image fun q => (rep q.1, q.2), C, hC, fun x => ?_⟩
    have hval : f x = maxAffineFn s x + indicatorFn C x := congrFun hfC x
    have hunfold : maxAffineFn s x = ⨆ q ∈ s, ((q.1 x - q.2 : ℝ) : EReal) := rfl
    have hmax : maxAffineFn s x
        = ⨆ q ∈ s.image fun q => (rep q.1, q.2), ((pairing n x q.1 - q.2 : ℝ) : EReal) := by
      rw [hunfold]
      refine le_antisymm (iSup₂_le fun ψ hψ => ?_) (iSup₂_le fun ψ hψ => ?_)
      · refine le_iSup₂_of_le (rep ψ.1, ψ.2) (Finset.mem_image_of_mem _ hψ) (le_of_eq ?_)
        rw [hrep ψ.1 x]
      · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hψ
        refine le_iSup₂_of_le q hq (le_of_eq ?_)
        rw [hrep q.1 x]
    rw [hval, hmax]
  · rintro ⟨s, C, hC, hfC⟩
    refine (polyhedralFn_iff_maxAffineFn_add_indicatorFn hb).2
      ⟨s.image fun q => ((pairing n).flip q.1, q.2), C, hC, funext fun x => ?_⟩
    have hunfold : maxAffineFn (s.image fun q => ((pairing n).flip q.1, q.2)) x
        = ⨆ ψ ∈ s.image fun q => ((pairing n).flip q.1, q.2),
            ((ψ.1 x - ψ.2 : ℝ) : EReal) := rfl
    have hmax : maxAffineFn (s.image fun q => ((pairing n).flip q.1, q.2)) x
        = ⨆ q ∈ s, ((pairing n x q.1 - q.2 : ℝ) : EReal) := by
      rw [hunfold]
      refine le_antisymm (iSup₂_le fun ψ hψ => ?_) (iSup₂_le fun q hq => ?_)
      · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hψ
        exact le_iSup₂_of_le q hq (le_of_eq rfl)
      · exact le_iSup₂_of_le ((pairing n).flip q.1, q.2)
          (Finset.mem_image_of_mem _ hq) (le_of_eq rfl)
    change f x = maxAffineFn (s.image fun q => ((pairing n).flip q.1, q.2)) x + indicatorFn C x
    rw [hmax]
    exact hfC x

/-! ### Theorem 19.5 and its corollary -/

/-- **Theorem 19.5**, first assertion: `λC` is polyhedral for every scalar `λ`. One statement
covers `λ > 0`, `λ = 0` and `λ < 0`, so the book's three-way case split is not reproduced. -/
theorem theorem_19_5_smul {C : Set (Rn n)} (hC : Polyhedral C) (l : ℝ) : Polyhedral (l • C) :=
  hC.smul l

/-- **Theorem 19.5**, second assertion: the recession cone of a non-empty polyhedral convex set is
a polyhedral convex cone. -/
theorem theorem_19_5_recession {C : Set (Rn n)} (hC : Polyhedral C) (hne : C.Nonempty) :
    PolyhedralCone (recessionCone C) :=
  hC.polyhedralCone_recessionCone hne

/-- **Theorem 19.5**, third assertion: if `C = conv S` for a finite set `S` of points and
directions, then `0⁺C = conv S₀` for `S₀` the origin together with the directions of `S`, which is
the cone `PointedCone.hull ℝ ↑D` they generate. -/
theorem theorem_19_5_generators {C : Set (Rn n)} {P D : Finset (Rn n)}
    (hPD : C = convexHullPD (P : Set (Rn n)) (D : Set (Rn n))) (hne : C.Nonempty) :
    recessionCone C = (PointedCone.hull ℝ (D : Set (Rn n)) : Set (Rn n)) :=
  recessionCone_of_finitelyGenerated hPD hne

/-- **Corollary 19.5.1**. For `f` a proper polyhedral convex function, `fλ` is polyhedral for
`λ ≥ 0` and for `λ = 0⁺`, the `λ ≥ 0⁺` convention being §9's `ExtCoeff.smulFn`. -/
theorem corollary_19_5_1 {f : Rn n → EReal} (hf : PolyhedralFn f) (hp : Proper f)
    {l : ExtCoeff} (hl : l.Nonneg) : PolyhedralFn (l.smulFn f) := by
  cases l with
  | ofReal t =>
    rw [ExtCoeff.smulFn_ofReal]
    rcases eq_or_lt_of_le (hl : (0 : ℝ) ≤ t) with ht | ht
    · rw [← ht, smulRight_zero hp.dom_nonempty]
      exact polyhedralFn_indicatorFn polyhedral_zero
    · change Polyhedral (epi (smulRight f t))
      rw [epi_smulRight ht]
      exact hf.smul t
  | zeroPlus =>
    change Polyhedral (epi (recessionFn f))
    rw [epi_recessionFn]
    exact (hf.polyhedralCone_recessionCone
      ((epi_nonempty_iff f).2 hp.dom_nonempty)).polyhedral

/-! ### Theorems 19.6 and 19.7 -/

/-- **Theorem 19.6** for `m = 2`: `cl (conv (C₁ ∪ C₂))` is polyhedral for `C₁`, `C₂` non-empty
polyhedral. The book prints Theorem 19.6 with **no proof paragraph**; the argument formalized here
is the one in its running text. -/
theorem theorem_19_6 {C₁ C₂ : Set (Rn n)} (h₁ : Polyhedral C₁) (hne₁ : C₁.Nonempty)
    (h₂ : Polyhedral C₂) (hne₂ : C₂.Nonempty) :
    Polyhedral (closure (convexHull ℝ (C₁ ∪ C₂))) :=
  polyhedral_closure_convexHull_union h₁ hne₁ h₂ hne₂

/-- **Theorem 19.6** for `m = 2`, the formula

`cl (conv (C₁ ∪ C₂)) = ⋃ {λ₁C₁ + λ₂C₂ | λᵢ ≥ 0, λ₁ + λ₂ = 1}`,

with `0⁺Cᵢ` substituted for `0Cᵢ` when `λᵢ = 0`. The union is indexed by `ExtCoeff`, exactly as in
Theorem 9.8. -/
theorem theorem_19_6_iUnion {C₁ C₂ : Set (Rn n)} (h₁ : Polyhedral C₁) (hne₁ : C₁.Nonempty)
    (h₂ : Polyhedral C₂) (hne₂ : C₂.Nonempty) :
    closure (convexHull ℝ (C₁ ∪ C₂))
      = ⋃ p : ExtCoeff × ExtCoeff,
          ⋃ _ : p.1.Nonneg ∧ p.2.Nonneg ∧ p.1.toReal + p.2.toReal = 1,
            p.1.smulSet C₁ + p.2.smulSet C₂ := by
  rw [iUnion_extCoeff_pair h₁.convex hne₁ h₂.convex hne₂]
  exact (finitelyGenerated_closure_convexHull_union h₁ hne₁ h₂ hne₂).2

/-- **Theorem 19.6** for general `m`: `cl (conv (C₁ ∪ ⋯ ∪ Cₘ))` is polyhedral. Indexed by a
`Finset`, which also allows the empty family, where both sides are `∅`. -/
theorem theorem_19_6_biUnion {ι : Type*} {s : Finset ι} {C : ι → Set (Rn n)}
    (hC : ∀ i ∈ s, Polyhedral (C i)) (hne : ∀ i ∈ s, (C i).Nonempty) :
    Polyhedral (closure (convexHull ℝ (⋃ i ∈ s, C i))) :=
  polyhedral_closure_convexHull_biUnion hC hne

/-- **Theorem 19.6** for general `m`, in convention-free form:

`cl (conv (C₁ ∪ ⋯ ∪ Cₘ)) = conv (C₁ ∪ ⋯ ∪ Cₘ) + (0⁺C₁ + ⋯ + 0⁺Cₘ)`.

Adding the recession cones says what the book's union over weights says, with no convention. -/
theorem theorem_19_6_biUnion_add {ι : Type*} {s : Finset ι} {C : ι → Set (Rn n)}
    (hC : ∀ i ∈ s, Polyhedral (C i)) (hne : ∀ i ∈ s, (C i).Nonempty) :
    closure (convexHull ℝ (⋃ i ∈ s, C i))
      = convexHull ℝ (⋃ i ∈ s, C i) + ∑ i ∈ s, recessionCone (C i) :=
  (finitelyGenerated_closure_convexHull_biUnion hC hne).2

/-- **The `λ ≥ 0⁺` convention for a single set.** For convex `C`, Rockafellar's
`⋃ {λC | λ > 0 or λ = 0⁺}` is exactly `cone C + 0⁺C`. Theorem 19.7 asks `C` non-empty; the identity
does not, both sides collapsing to `0⁺∅` when `C = ∅`. -/
theorem iUnion_extCoeff_pos {C : Set (Rn n)} (hC : Convex ℝ C) :
    (⋃ l : ExtCoeff, ⋃ _ : l.Pos, l.smulSet C)
      = (PointedCone.hull ℝ C : Set (Rn n)) + recessionCone C := by
  have hzeroK : (0 : Rn n) ∈ (PointedCone.hull ℝ C : Set (Rn n)) :=
    (PointedCone.hull ℝ C).zero_mem
  refine Set.Subset.antisymm (fun x hx => ?_) (fun x hx => ?_)
  · obtain ⟨l, hl, hmem⟩ := Set.mem_iUnion₂.1 hx
    cases l with
    | ofReal t =>
      obtain ⟨y, hy, hyx⟩ := hmem
      have hyx' : t • y = x := hyx
      have hKt : x ∈ (PointedCone.hull ℝ C : Set (Rn n)) := by
        rw [← hyx']
        exact Submodule.smul_mem _ (⟨t, (hl : (0 : ℝ) < t).le⟩ : {c : ℝ // 0 ≤ c})
          (PointedCone.subset_hull hy)
      simpa using Set.add_mem_add hKt (zero_mem_recessionCone C)
    | zeroPlus => simpa using Set.add_mem_add hzeroK hmem
  · obtain ⟨u, hu, v, hv, huv⟩ := hx
    have huv' : u + v = x := huv
    rcases (mem_coe_hull_iff_of_convex hC).1 hu with rfl | ⟨t, ht, y, hy, hty⟩
    · refine Set.mem_iUnion₂.2 ⟨ExtCoeff.zeroPlus, trivial, ?_⟩
      rw [ExtCoeff.smulSet_zeroPlus, ← huv', zero_add]
      exact hv
    · have hty' : t • y = u := hty
      refine Set.mem_iUnion₂.2 ⟨ExtCoeff.ofReal t, ht, ?_⟩
      rw [ExtCoeff.smulSet_ofReal]
      have hyC : y + t⁻¹ • v ∈ C :=
        add_mem_of_mem_recessionCone (smul_mem_recessionCone (by positivity) hv) hy
      have hmem := Set.smul_mem_smul_set (a := t) hyC
      have hval : t • (y + t⁻¹ • v) = x := by
        rw [smul_add, smul_smul, mul_inv_cancel₀ (ne_of_gt ht), one_smul, hty', huv']
      rwa [hval] at hmem

/-- **Theorem 19.7**. For `C` a non-empty polyhedral convex set, the closure of the convex cone
generated by `C` is a polyhedral convex cone. The closure is needed: for `C` the horizontal line at
height `1` in `ℝ²` the cone generated is the open upper half-plane with the origin, and the missing
horizontal directions are exactly `0⁺C`. -/
theorem theorem_19_7 {C : Set (Rn n)} (hC : Polyhedral C) (hne : C.Nonempty) :
    PolyhedralCone (closure (PointedCone.hull ℝ C : Set (Rn n))) :=
  polyhedralCone_closure_coe_hull hC hne

/-- **Theorem 19.7**, the formula `K = ⋃ {λC | λ > 0 or λ = 0⁺}`, converted by
`iUnion_extCoeff_pos` into the backbone's `cone C + 0⁺C`. -/
theorem theorem_19_7_iUnion {C : Set (Rn n)} (hC : Polyhedral C) (hne : C.Nonempty) :
    closure (PointedCone.hull ℝ C : Set (Rn n)) = ⋃ l : ExtCoeff, ⋃ _ : l.Pos, l.smulSet C := by
  rw [iUnion_extCoeff_pos hC.convex]
  exact (finitelyGeneratedCone_closure_coe_hull hC hne).2

/-- **Corollary 19.7.1**. If a polyhedral convex set `C` contains the origin, the convex cone
generated by `C` is polyhedral, with no closure needed. -/
theorem corollary_19_7_1 {C : Set (Rn n)} (hC : Polyhedral C) (h0 : (0 : Rn n) ∈ C) :
    PolyhedralCone (PointedCone.hull ℝ C : Set (Rn n)) :=
  (finitelyGeneratedCone_hull_of_zero_mem hC h0).polyhedralCone

end Rockafellar
