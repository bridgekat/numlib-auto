import Numlib.Analysis.Convex.Polyhedral.Closedness
import Numlib.Analysis.Convex.Polyhedral.Simplicial
import NumlibSurface.Rockafellar.Chapter03.Section11
import NumlibSurface.Rockafellar.Chapter03.Section12
import NumlibSurface.Rockafellar.Chapter03.Section16

/-!
# Rockafellar §20: some applications of polyhedral convexity

Surface file for R. Tyrrell Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §20:
the separation theorems, closure conditions and conjugacy formulas of Parts II and III, refined by
assuming *some* of the convexity polyhedral.

All eight numbered results of §20 are formalized over `Rn n = ℝⁿ`: Theorems 20.1–20.5 and
Corollaries 20.1.1, 20.2.1, 20.3.1, together with the unnumbered all-polyhedral computation of the
opening paragraph (`theorem_20_1_pair_exact`).

`IsExactSum` and `IsExactFinsetSum` are the backbone's names for the conclusion Theorems 16.4 and
20.1 share; the `m`-ary statements are proved for the family, not by induction on the binary ones,
and the index set is split membership-wise so that no `DecidableEq` instance enters a statement.

`IsPolyhedral` is Rockafellar's §19 definition quantified over *vectors* `bᵢ`, bridged to the
backbone's functional-indexed `Polyhedral` by `isPolyhedral_iff_polyhedral`; a polyhedral convex
*function* is the backbone's `PolyhedralFn` directly.

## Main definitions

* `IsPolyhedral` — the book's polyhedral convex set, an intersection of finitely many closed
  half-spaces `{x | ⟨x, bᵢ⟩ ≤ βᵢ}`.
* `SeparableProperlyNotContaining` — the sharpened separation of §20: properly, and with the
  hyperplane containing neither set.

## Main results

* `theorem_20_1_exact`, `theorem_20_1_attained`, `theorem_20_1_exact_finset`,
  `theorem_20_1_attained_finset`, `theorem_20_1_pair_exact`, `theorem_20_1_pair_attained` — a
  polyhedral summand needs only `dom fᵢ`, not `ri (dom fᵢ)`, in the qualification of Theorem 16.4.
* `corollary_20_1_1`, `corollary_20_1_1_attained`, `corollary_20_1_1_finset`,
  `corollary_20_1_1_attained_finset` — the dual form, for the infimal convolute.
* `theorem_20_2`, `corollary_20_2_1` — with `C₁` polyhedral, proper separation not containing `C₂`
  is possible exactly when `C₁ ∩ ri C₂ = ∅`.
* `theorem_20_3`, `corollary_20_3_1` — with `C₁` polyhedral and `C₂` closed, strong separation
  needs only disjointness plus a recession condition.
* `theorem_20_4` — a closed bounded `C` inside `int D` can be sandwiched by a polyhedral convex
  `P`: `C ⊆ int P` and `P ⊆ int D`.
* `theorem_20_5`, `theorem_20_5_polytope` — every polyhedral convex set, and every polytope, is
  locally simplicial; this is what §10's continuity theorems are applied to.

## The asymmetry of Theorem 20.1

Theorem 16.4 makes `(f₁ + ⋯ + fₘ)* = f₁* □ ⋯ □ fₘ*` exact when the sets `ri (dom fᵢ)` have a common
point. Theorem 20.1 says that for a *polyhedral* summand the relative interior may be dropped: only
`dom fᵢ` need take part in the intersection, and when every summand is polyhedral no relative
interior appears at all. The asymmetry comes from two segment lemmas: a proper polyhedral function
is already closed, so Corollary 7.5.1 asks only for a point of `dom f`, whereas Theorem 7.5 asks
for a point of `ri (dom g)`.
-/

open Set Pointwise

namespace Rockafellar

open ConvexAnalysis

variable {n : ℕ}

/-! ### Polyhedral convex sets, in the book's own words -/

/-- **§19 (p. 170).** A **polyhedral convex set** in `ℝⁿ` is an intersection of finitely many
closed half-spaces `{x | ⟨x, bᵢ⟩ ≤ βᵢ}`. Nothing below unfolds the definition. -/
def IsPolyhedral (C : Set (Rn n)) : Prop :=
  ∃ s : Finset (Rn n × ℝ), C = {x | ∀ q ∈ s, pairing n x q.1 ≤ q.2}

/-- Rockafellar's vector-indexed system of half-spaces and the backbone's functional-indexed one
describe the same sets, `linFn` and `exists_linFn` being the round trip. -/
theorem isPolyhedral_iff_polyhedral {C : Set (Rn n)} : IsPolyhedral C ↔ Polyhedral C := by
  classical
  constructor
  · rintro ⟨s, rfl⟩
    refine ⟨s.image fun q => ((linFn q.1 : Rn n →ₗ[ℝ] ℝ), q.2), Set.ext fun x => ?_⟩
    constructor
    · refine fun hx => Finset.forall_mem_image.2 fun q hq => ?_
      change (linFn q.1) x ≤ q.2
      rw [linFn_apply]
      exact hx q hq
    · intro hx q hq
      have hq' : (linFn q.1) x ≤ q.2 := Finset.forall_mem_image.1 hx hq
      rwa [linFn_apply] at hq'
  · rintro ⟨s, rfl⟩
    have hrep : ∀ φ : Rn n →ₗ[ℝ] ℝ, ∃ b : Rn n, ∀ x, pairing n x b = φ x := by
      intro φ
      obtain ⟨b, hb⟩ := exists_linFn (LinearMap.toContinuousLinearMap φ)
      exact ⟨b, fun x => by rw [← linFn_apply, hb]; simp⟩
    choose rep hrep using hrep
    refine ⟨s.image fun q => (rep q.1, q.2), Set.ext fun x => ?_⟩
    constructor
    · refine fun hx => Finset.forall_mem_image.2 fun q hq => ?_
      change pairing n x (rep q.1) ≤ q.2
      rw [hrep]
      exact hx q hq
    · intro hx q hq
      have hq' : pairing n x (rep q.1) ≤ q.2 := Finset.forall_mem_image.1 hx hq
      rwa [hrep] at hq'

/-! ### Separation that does not swallow the second set -/

/-- **§20 (p. 181).** There exists a hyperplane separating `C₁` and `C₂` properly and *not
containing* `C₂`. The side convention is §11's: `C₁` lies in the closed half-space
`{x | ⟨x, b⟩ ≥ β}` and `C₂` in the opposite one. -/
def SeparableProperlyNotContaining (C₁ C₂ : Set (Rn n)) : Prop :=
  ∃ (b : Rn n) (β : ℝ), SeparatesProperlyRn b β C₁ C₂ ∧ ¬ C₂ ⊆ {x | pairing n x b = β}

/-- The bridge from `SeparableProperlyNotContaining` to the backbone's functional form. -/
theorem separableProperlyNotContaining_iff_exists {C₁ C₂ : Set (Rn n)}
    (hne₁ : C₁.Nonempty) (hne₂ : C₂.Nonempty) :
    SeparableProperlyNotContaining C₁ C₂ ↔
      ∃ (g : Rn n →L[ℝ] ℝ) (c : ℝ), Separates g c C₁ C₂ ∧ ¬ C₂ ⊆ {x | g x = c} := by
  constructor
  · rintro ⟨b, β, ⟨-, hsep⟩, hns⟩
    refine ⟨-linFn b, -β, hsep.toSeparates.symm, fun hcon => hns fun x hx => ?_⟩
    simpa using hcon hx
  · rintro ⟨g, c, hsep, hns⟩
    have hprop : SeparatesProperly g c C₁ C₂ :=
      ⟨hsep, fun hcon => hns fun x hx => hcon (Set.mem_union_right _ hx)⟩
    obtain ⟨b, hb⟩ := exists_linFn (-g)
    have hb0 : b ≠ 0 := by
      intro hzero
      have hz : linFn b = 0 := linFn_eq_zero_iff.2 hzero
      rw [hb, neg_eq_zero] at hz
      exact hprop.ne_zero hne₁ hne₂ hz
    refine ⟨b, -c, ⟨hb0, by rw [hb]; exact hprop.symm⟩, fun hcon => hns fun x hx => ?_⟩
    have h : pairing n x b = -c := hcon hx
    rw [← linFn_apply, hb] at h
    simpa using h

/-! ### Theorem 20.1 and its corollary -/

/-- **§20 (p. 179)**, the all-polyhedral case: if `f` and `g` are proper polyhedral convex
functions whose effective domains meet at all, then `(f + g)* = f* □ g*`. No relative interior
appears in the hypothesis. Rockafellar gives this unnumbered, as the computation motivating
Theorem 20.1. -/
theorem theorem_20_1_pair_exact {f g : Rn n → EReal} (hf : PolyhedralFn f) (hpf : ProperConvex f)
    (hg : PolyhedralFn g) (hpg : ProperConvex g) {x₀ : Rn n} (hxf : x₀ ∈ convexDom f)
        (hxg : x₀ ∈ convexDom g) :
    convexConj (pairing n) (f + g)
        = infConv (convexConj (pairing n) f) (convexConj (pairing n) g) :=
  (IsExactSum.of_polyhedral_pair (B := pairing n) hf hpf hg hpg hxf hxg).convexConj_add

/-- **§20 (p. 179)**, the all-polyhedral case, attainment: the infimum defining `(f* □ g*)(x*)` is
attained for every `x*`. -/
theorem theorem_20_1_pair_attained {f g : Rn n → EReal} (hf : PolyhedralFn f) (hpf : ProperConvex f)
    (hg : PolyhedralFn g) (hpg : ProperConvex g) {x₀ : Rn n} (hxf : x₀ ∈ convexDom f)
        (hxg : x₀ ∈ convexDom g)
    (y : Rn n) :
    ∃ y₁ y₂ : Rn n, y₁ + y₂ = y ∧
      convexConj (pairing n) f y₁ + convexConj (pairing n) g y₂
          = convexConj (pairing n) (f + g) y :=
  (IsExactSum.of_polyhedral_pair (B := pairing n) hf hpf hg hpg hxf hxg).exists_convexConj_add_eq y

/-- **Theorem 20.1**. For `f` and `g` proper convex with `f` polyhedral and
`dom f ∩ ri (dom g) ≠ ∅`,

`(f + g)*(x*) = (f* □ g*)(x*) = inf {f*(x₁*) + g*(x₂*) | x₁* + x₂* = x*}`.

**The asymmetry is the point**: the polyhedral summand contributes only a point of `dom f`, the
other a point of `ri (dom g)`. Compare `theorem_16_4_exact`, which asks for a point of
`ri (dom f) ∩ ri (dom g)`, and `theorem_20_1_pair_exact`, which asks for neither. -/
theorem theorem_20_1_exact {f g : Rn n → EReal} (hf : PolyhedralFn f) (hpf : ProperConvex f)
    (hg : ConvexFn g) (hpg : ProperConvex g) {x₀ : Rn n} (hxf : x₀ ∈ convexDom f)
    (hxg : x₀ ∈ ri (convexDom g)) :
    convexConj (pairing n) (f + g)
        = infConv (convexConj (pairing n) f) (convexConj (pairing n) g) :=
  (IsExactSum.of_polyhedral (B := pairing n) hf hpf hg hpg hxf hxg).convexConj_add

/-- **Theorem 20.1**, the attainment clause: under the same qualification the infimum
`inf {f*(x₁*) + g*(x₂*) | x₁* + x₂* = x*}` is attained for each `x*`. -/
theorem theorem_20_1_attained {f g : Rn n → EReal} (hf : PolyhedralFn f) (hpf : ProperConvex f)
    (hg : ConvexFn g) (hpg : ProperConvex g) {x₀ : Rn n} (hxf : x₀ ∈ convexDom f)
    (hxg : x₀ ∈ ri (convexDom g)) (y : Rn n) :
    ∃ y₁ y₂ : Rn n, y₁ + y₂ = y ∧
      convexConj (pairing n) f y₁ + convexConj (pairing n) g y₂
          = convexConj (pairing n) (f + g) y :=
  (IsExactSum.of_polyhedral (B := pairing n) hf hpf hg hpg hxf hxg).exists_convexConj_add_eq y

section Corollary_20_1_1

variable {f g : Rn n → EReal}

private theorem isExactSum_convexConj_of_polyhedral (hf : PolyhedralFn f)
    (hcf : ClosedProperConvexFn f) (hg : ClosedProperConvexFn g) {x₀ : Rn n}
    (hxf : x₀ ∈ convexDom (convexConj (pairing n) f))
        (hxg : x₀ ∈ ri (convexDom (convexConj (pairing n) g))) :
    IsExactSum (pairing n) (convexConj (pairing n) f) (convexConj (pairing n) g) :=
  IsExactSum.of_polyhedral (B := pairing n) (PolyhedralFn.convexConj hf)
      (properConvex_convexConj hcf)
    (convexFn_convexConj _ _) (properConvex_convexConj hg) hxf hxg

private theorem infConv_eq_convexConj_add_convexConj (hf : PolyhedralFn f)
    (hcf : ClosedProperConvexFn f)
    (hg : ClosedProperConvexFn g) {x₀ : Rn n} (hxf : x₀ ∈ convexDom (convexConj (pairing n) f))
    (hxg : x₀ ∈ ri (convexDom (convexConj (pairing n) g))) :
    infConv f g = convexConj (pairing n) (convexConj (pairing n) f + convexConj (pairing n) g) := by
  have hff : convexConj (pairing n) (convexConj (pairing n) f) = f := by
    rw [theorem_12_2_biconj hcf.convex]; exact hcf.closed
  have hgg : convexConj (pairing n) (convexConj (pairing n) g) = g := by
    rw [theorem_12_2_biconj hg.convex]; exact hg.closed
  rw [(isExactSum_convexConj_of_polyhedral hf hcf hg hxf hxg).convexConj_add, hff, hgg]

/-- **Corollary 20.1.1**. For `f` and `g` closed proper convex with `f` polyhedral and
`dom f* ∩ ri (dom g*) ≠ ∅`, the infimal convolute `f □ g` is a closed proper convex function.
Rockafellar's proof verbatim: apply Theorem 20.1 to the conjugates, `f*` being polyhedral by
Theorem 19.2, and read back through Theorem 12.2. -/
theorem corollary_20_1_1 (hf : PolyhedralFn f) (hcf : ClosedProperConvexFn f)
    (hg : ClosedProperConvexFn g) {x₀ : Rn n} (hxf : x₀ ∈ convexDom (convexConj (pairing n) f))
    (hxg : x₀ ∈ ri (convexDom (convexConj (pairing n) g))) :
    ClosedProperConvexFn (infConv f g) := by
  have hexact := isExactSum_convexConj_of_polyhedral hf hcf hg hxf hxg
  rw [infConv_eq_convexConj_add_convexConj hf hcf hg hxf hxg]
  exact ⟨convexFn_convexConj _ _, closedConvex_convexConj, properConvex_convexConj_of_properConvex
    (ConvexFn.add (convexFn_convexConj _ _) (convexFn_convexConj _ _)
      (properConvex_convexConj hcf).ne_bot (properConvex_convexConj hg).ne_bot)
          hexact.properConvex_add⟩

/-- **Corollary 20.1.1**, the attainment clause: the infimum defining `(f □ g)(x)` is attained for
every `x`. -/
theorem corollary_20_1_1_attained (hf : PolyhedralFn f) (hcf : ClosedProperConvexFn f)
    (hg : ClosedProperConvexFn g) {x₀ : Rn n} (hxf : x₀ ∈ convexDom (convexConj (pairing n) f))
    (hxg : x₀ ∈ ri (convexDom (convexConj (pairing n) g))) (x : Rn n) :
    ∃ x₁ x₂ : Rn n, x₁ + x₂ = x ∧ f x₁ + g x₂ = infConv f g x := by
  have hff : convexConj (pairing n) (convexConj (pairing n) f) = f := by
    rw [theorem_12_2_biconj hcf.convex]; exact hcf.closed
  have hgg : convexConj (pairing n) (convexConj (pairing n) g) = g := by
    rw [theorem_12_2_biconj hg.convex]; exact hg.closed
  obtain ⟨x₁, x₂, hsum, hval⟩ :=
    (isExactSum_convexConj_of_polyhedral hf hcf hg hxf hxg).exists_convexConj_add_eq x
  refine ⟨x₁, x₂, hsum, ?_⟩
  rw [infConv_eq_convexConj_add_convexConj hf hcf hg hxf hxg, ← hval, hff, hgg]

end Corollary_20_1_1

/-- **Theorem 20.1** in the book's `m`-ary form. Let `f₁, …, fₘ` be proper convex with
`f₁, …, f_k` polyhedral, and suppose

`dom f₁ ∩ ⋯ ∩ dom f_k ∩ ri (dom f_{k+1}) ∩ ⋯ ∩ ri (dom fₘ)`

is non-empty. Then `(f₁ + ⋯ + fₘ)* = f₁* □ ⋯ □ fₘ*`. Here `t` is the book's `{1, …, k}` and `u` its
complement. Compare `theorem_16_4_exact_finset`, which asks for a relative interior point on every
index. -/
theorem theorem_20_1_exact_finset {ι : Type*} {s t u : Finset ι} {f : ι → Rn n → EReal}
    (hs : s.Nonempty) (hdisj : Disjoint t u) (hmem : ∀ i, i ∈ s ↔ i ∈ t ∨ i ∈ u)
    (hpoly : ∀ i ∈ t, PolyhedralFn (f i)) (hconv : ∀ i ∈ u, ConvexFn (f i))
    (hpf : ∀ i ∈ s, ProperConvex (f i)) {x₀ : Rn n} (hxt : ∀ i ∈ t, x₀ ∈ convexDom (f i))
    (hxu : ∀ i ∈ u, x₀ ∈ ri (convexDom (f i))) :
    convexConj (pairing n) (∑ i ∈ s, f i)
      = ofInfConvFn (∑ i ∈ s, toInfConvFn (convexConj (pairing n) (f i))) :=
  (IsExactFinsetSum.of_polyhedral (B := pairing n) hs hdisj hmem hpoly hconv hpf hxt
    hxu).convexConj_finsetSum

/-- **Theorem 20.1**, the attainment clause for `m` summands:
`inf {f₁*(x₁*) + ⋯ + fₘ*(xₘ*) | x₁* + ⋯ + xₘ* = x*}` is attained for each `x*`. -/
theorem theorem_20_1_attained_finset {ι : Type*} {s t u : Finset ι} {f : ι → Rn n → EReal}
    (hs : s.Nonempty) (hdisj : Disjoint t u) (hmem : ∀ i, i ∈ s ↔ i ∈ t ∨ i ∈ u)
    (hpoly : ∀ i ∈ t, PolyhedralFn (f i)) (hconv : ∀ i ∈ u, ConvexFn (f i))
    (hpf : ∀ i ∈ s, ProperConvex (f i)) {x₀ : Rn n} (hxt : ∀ i ∈ t, x₀ ∈ convexDom (f i))
    (hxu : ∀ i ∈ u, x₀ ∈ ri (convexDom (f i))) (y : Rn n) :
    ∃ y' : ι → Rn n, ∑ i ∈ s, y' i = y ∧
      ∑ i ∈ s, convexConj (pairing n) (f i) (y' i) = convexConj (pairing n) (∑ i ∈ s, f i) y :=
  (IsExactFinsetSum.of_polyhedral (B := pairing n) hs hdisj hmem hpoly hconv hpf hxt
    hxu).exists_convexConj_finsetSum_eq y

section Corollary_20_1_1_finset

variable {ι : Type*} {s t u : Finset ι} {f : ι → Rn n → EReal}
variable (hs : s.Nonempty) (hdisj : Disjoint t u) (hmem : ∀ i, i ∈ s ↔ i ∈ t ∨ i ∈ u)
variable (hpoly : ∀ i ∈ t, PolyhedralFn (f i)) (hcf : ∀ i ∈ s, ClosedProperConvexFn (f i))
variable {x₀ : Rn n} (hxt : ∀ i ∈ t, x₀ ∈ convexDom (convexConj (pairing n) (f i)))
variable (hxu : ∀ i ∈ u, x₀ ∈ ri (convexDom (convexConj (pairing n) (f i))))

include hs hdisj hmem hpoly hcf hxt hxu

private theorem isExactFinsetSum_convexConj_of_polyhedral :
    IsExactFinsetSum (pairing n) s fun i => convexConj (pairing n) (f i) :=
  IsExactFinsetSum.of_polyhedral (B := pairing n) hs hdisj hmem
    (fun i hi => PolyhedralFn.convexConj (B := pairing n) (hpoly i hi))
    (fun i _ => convexFn_convexConj (pairing n) (f i))
        (fun i hi => properConvex_convexConj (hcf i hi)) hxt hxu

private theorem sum_toInfConvFn_eq_convexConj_finsetSum_convexConj :
    ofInfConvFn (∑ i ∈ s, toInfConvFn (f i))
      = convexConj (pairing n) (∑ i ∈ s, convexConj (pairing n) (f i)) := by
  have hbi : ∀ i ∈ s, convexConj (pairing n) (convexConj (pairing n) (f i)) = f i := fun i hi => by
    rw [theorem_12_2_biconj (hcf i hi).convex]; exact (hcf i hi).closed
  rw [(isExactFinsetSum_convexConj_of_polyhedral hs hdisj hmem hpoly hcf hxt
      hxu).convexConj_finsetSum]
  exact congrArg ofInfConvFn
    (Finset.sum_congr rfl fun i hi => congrArg toInfConvFn (hbi i hi).symm)

/-- **Corollary 20.1.1** in the book's `m`-ary form. Let `f₁, …, fₘ` be closed proper convex with
`f₁, …, f_k` polyhedral, and suppose

`dom f₁* ∩ ⋯ ∩ dom f_k* ∩ ri (dom f_{k+1}*) ∩ ⋯ ∩ ri (dom fₘ*)`

is non-empty. Then `f₁ □ ⋯ □ fₘ` is a closed proper convex function. -/
theorem corollary_20_1_1_finset :
    ClosedProperConvexFn (ofInfConvFn (∑ i ∈ s, toInfConvFn (f i))) := by
  have hx₀ : ∀ i ∈ s, x₀ ∈ convexDom (convexConj (pairing n) (f i)) := fun i hi =>
    (hmem i).1 hi |>.elim (fun h => hxt i h) fun h => intrinsicInterior_subset (hxu i h)
  obtain ⟨hconvsum, -, -⟩ :=
    properConvexFn_finsetSum (f := fun i => convexConj (pairing n) (f i))
      (fun i _ => convexFn_convexConj (pairing n) (f i))
          (fun i hi => properConvex_convexConj (hcf i hi)) hx₀
  rw [sum_toInfConvFn_eq_convexConj_finsetSum_convexConj hs hdisj hmem hpoly hcf hxt hxu]
  exact ⟨convexFn_convexConj _ _, closedConvex_convexConj,
      properConvex_convexConj_of_properConvex hconvsum
    (isExactFinsetSum_convexConj_of_polyhedral hs hdisj hmem hpoly hcf hxt
        hxu).properConvex_finsetSum⟩

/-- **Corollary 20.1.1**, the attainment clause: the infimum defining `(f₁ □ ⋯ □ fₘ)(x)` is
attained for every `x`. -/
theorem corollary_20_1_1_attained_finset (x : Rn n) :
    ∃ x' : ι → Rn n, ∑ i ∈ s, x' i = x ∧
      ∑ i ∈ s, f i (x' i) = ofInfConvFn (∑ i ∈ s, toInfConvFn (f i)) x := by
  have hbi : ∀ i ∈ s, convexConj (pairing n) (convexConj (pairing n) (f i)) = f i := fun i hi => by
    rw [theorem_12_2_biconj (hcf i hi).convex]; exact (hcf i hi).closed
  obtain ⟨x', hx', hval⟩ :=
    (isExactFinsetSum_convexConj_of_polyhedral hs hdisj hmem hpoly hcf hxt
        hxu).exists_convexConj_finsetSum_eq
      x
  refine ⟨x', hx', ?_⟩
  rw [sum_toInfConvFn_eq_convexConj_finsetSum_convexConj hs hdisj hmem hpoly hcf hxt hxu, ← hval]
  exact Finset.sum_congr rfl fun i hi => congrArg (fun k => k (x' i)) (hbi i hi).symm

end Corollary_20_1_1_finset

/-! ### Theorem 20.2 and its corollary -/

/-- **Theorem 20.2**. For non-empty convex `C₁`, `C₂` with `C₁` polyhedral, a hyperplane separating
`C₁` and `C₂` properly and not containing `C₂` exists iff `C₁ ∩ ri C₂ = ∅`. Compare Theorem 11.3,
which asks `ri C₁ ∩ ri C₂ = ∅` and promises nothing about containment: polyhedrality of `C₁` buys
both improvements at once. Convexity of `C₁` follows from polyhedrality and is not assumed. -/
theorem theorem_20_2 {C₁ C₂ : Set (Rn n)} (h₁ : IsPolyhedral C₁) (hne₁ : C₁.Nonempty)
    (h₂ : Convex ℝ C₂) (hne₂ : C₂.Nonempty) :
    SeparableProperlyNotContaining C₁ C₂ ↔ C₁ ∩ ri C₂ = ∅ := by
  rw [separableProperlyNotContaining_iff_exists hne₁ hne₂,
    exists_separates_not_subset_iff_disjoint_relint (isPolyhedral_iff_polyhedral.1 h₁) h₂ hne₂,
    Set.disjoint_iff_inter_eq_empty]

/-- **Corollary 20.2.1**. For non-empty convex `C₁`, `C₂` with `C₁` polyhedral, `C₁ ∩ ri C₂` is
non-empty iff every `x*` with `δ*(x* | C₁) ≤ -δ*(-x* | C₂)` satisfies
`δ*(x* | C₁) = δ*(x* | C₂)`. The hypothesis on `x*` says some hyperplane orthogonal to `x*`
separates the two sets; the conclusion says every such hyperplane contains `C₂`. -/
theorem corollary_20_2_1 {C₁ C₂ : Set (Rn n)} (h₁ : IsPolyhedral C₁) (hne₁ : C₁.Nonempty)
    (h₂ : Convex ℝ C₂) (hne₂ : C₂.Nonempty) :
    (C₁ ∩ ri C₂).Nonempty ↔
      ∀ y : Rn n, supportFn (pairing n) C₁ y ≤ -supportFn (pairing n) C₂ (-y) →
        supportFn (pairing n) C₁ y = supportFn (pairing n) C₂ y :=
  nonempty_inter_relint_iff_forall_supportFn (B := pairing n)
    (isPolyhedral_iff_polyhedral.1 h₁) hne₁ h₂ hne₂

/-! ### Theorem 20.3 and its corollary -/

/-- **Theorem 20.3**. Let `C₁` be polyhedral and `C₂` closed, both non-empty convex, and suppose
every direction of recession of `C₁` whose opposite recedes in `C₂` is a direction in which `C₂` is
linear. Then `C₁ + C₂` is closed. "Linear in the direction `v`" is `v ∈ 0⁺C₂` *given* `-v ∈ 0⁺C₂`.
Compare Corollary 9.1.1, which asks in addition that such a `v` lie in the lineality space of
`C₁`. -/
theorem theorem_20_3 {C₁ C₂ : Set (Rn n)} (h₁ : IsPolyhedral C₁) (hne₁ : C₁.Nonempty)
    (h₂ : Convex ℝ C₂) (hcl₂ : IsClosed C₂) (hne₂ : C₂.Nonempty)
    (hrec : ∀ v ∈ recessionCone C₁, -v ∈ recessionCone C₂ → v ∈ recessionCone C₂) :
    IsClosed (C₁ + C₂) :=
  isClosed_add_of_polyhedral (B := pairing n) (isPolyhedral_iff_polyhedral.1 h₁) hne₁ h₂ hcl₂
    hne₂ hrec

/-- **Corollary 20.3.1**. Disjoint non-empty convex `C₁` polyhedral and `C₂` closed can be
separated strongly, provided their only common directions of recession are ones in which `C₂` is
linear. Compare Corollary 11.4.1, which forbids common recession directions outright, and
Corollary 19.3.3, where both sets are polyhedral and no recession hypothesis is needed. -/
theorem corollary_20_3_1 {C₁ C₂ : Set (Rn n)} (h₁ : IsPolyhedral C₁) (hne₁ : C₁.Nonempty)
    (h₂ : Convex ℝ C₂) (hcl₂ : IsClosed C₂) (hne₂ : C₂.Nonempty) (hdisj : C₁ ∩ C₂ = ∅)
    (hrec : ∀ v ∈ recessionCone C₁, v ∈ recessionCone C₂ → -v ∈ recessionCone C₂) :
    SeparableStrongly C₁ C₂ := by
  rw [separableStrongly_iff_exists hne₁ hne₂]
  exact separatesStrongly_of_polyhedral_of_recession (B := pairing n)
    (isPolyhedral_iff_polyhedral.1 h₁) hne₁ h₂ hcl₂ hne₂
    (Set.disjoint_iff_inter_eq_empty.2 hdisj) hrec

/-! ### Theorems 20.4 and 20.5 -/

/-- **Theorem 20.4**. For `C` closed and bounded and `D` convex with `C ⊆ int D`, there is a
polyhedral convex `P` with `P ⊆ int D` and `C ⊆ int P`.

**Rockafellar also assumes `C` non-empty and convex; neither hypothesis is used.** The argument is
a finite subcover of `C` by polyhedral neighbourhoods and never combines two points of `C`
convexly. -/
theorem theorem_20_4 {C D : Set (Rn n)} (hCcl : IsClosed C) (hCbdd : Bornology.IsBounded C)
    (hD : Convex ℝ D) (hCD : C ⊆ interior D) :
    ∃ P : Set (Rn n), IsPolyhedral P ∧ P ⊆ interior D ∧ C ⊆ interior P := by
  obtain ⟨P, hPpoly, hPD, hCP⟩ := exists_polyhedral_between hCcl hCbdd hD hCD
  exact ⟨P, isPolyhedral_iff_polyhedral.2 hPpoly, hPD, hCP⟩

/-- **Theorem 20.5**. Every polyhedral convex set is locally simplicial. The book's proof is a
two-line sketch which *asserts* the triangulation of a bounded polyhedron; the proof here produces
the simplices explicitly, as the convex hulls of the affinely independent subsets of a generating
`Finset`. -/
theorem theorem_20_5 {C : Set (Rn n)} (hC : IsPolyhedral C) : LocallySimplicial C :=
  Polyhedral.locallySimplicial (isPolyhedral_iff_polyhedral.1 hC)

/-- **Theorem 20.5**, second clause: every polytope is locally simplicial. -/
theorem theorem_20_5_polytope (P : Finset (Rn n)) :
    LocallySimplicial (convexHull ℝ (P : Set (Rn n))) :=
  Polyhedral.locallySimplicial (polyhedral_convexHull_finset P)

end Rockafellar
