import Numlib.Analysis.Convex.Duality.HomConePolar
import Numlib.Analysis.Convex.Duality.PolarBounded
import NumlibSurface.Rockafellar.Chapter03.Section12
import NumlibSurface.Rockafellar.Chapter03.Section13

/-!
# Rockafellar, §14: Polars of Convex Sets

The polar `K°` of a convex cone and the polar `C°` of a convex set, the bipolar theorems, and the
duality between gauges and support functions that polarity carries. All 11 numbered results of §14
are formalized.

## The section's definitions

* **The polar of a convex cone** `K° = {x* | ⟨x, x*⟩ ≤ 0 for every x ∈ K}` is the backbone's
  `polarCone (pairing n)`, unfolded here as `mem_polarCone_rn`.
* **The polar of a convex set** `C° = {x* | ⟨x, x*⟩ ≤ 1 for every x ∈ C}` is
  `polarSet (pairing n)`, unfolded as `mem_polarSet_rn`. The two agree on cones
  (`polarCone_eq_polarSet_rn`, the remark following Corollary 14.5.1).
* **Rank** of a convex set is `rankSet C = dim C - lineality C`, defined here because
  Corollary 14.6.1 is its first consumer among sets; §13's `rankFn` is the companion for functions.
* **The triples of `ℝⁿ⁺²`** that Theorem 14.4 is stated in are `triple λ x μ`, the concatenation
  `(λ, x, μ)`, and `endsReflection` is the book's `(λ*, x*, μ*) ↦ (-μ*, x*, -λ*)` read through it.

Theorems 14.1 and 14.5 carry no `Proof.` paragraph in the book, each summarising the running text
before it; both arguments are recovered here. `polarCone_polarCone` is proved by the separation
route the book mentions as an alternative (Corollary 11.7.1), and `C°° = C` by the same argument
with the constant normalised to `1`.

The unnumbered running text is recorded too: `(cl K)° = K°` and `K°° = cl K` for an arbitrary
bundled cone; the polar of a subspace as its orthogonal complement, of the non-negative orthant as
the non-positive orthant, and of a generated cone as the solution set of `⟨aᵢ, x*⟩ ≤ 0`; that
polarity is order-inverting; and that `C° = D°` for `D = cl (conv (C ∪ {0}))`, whence
`C°° = cl (conv (C ∪ {0}))` — which is what makes Theorem 14.5's hypotheses exactly the right ones.

## References

* [rockafellar1970convex] §14.
-/

open Set Pointwise

namespace Rockafellar

open ConvexAnalysis

variable {n : ℕ}

/-! ### The two polars of §14 -/

/-- **Rockafellar's polar of a convex cone** (§14, p. 121):
`K° = {x* | ⟨x, x*⟩ ≤ 0 for every x ∈ K}`. This is the backbone's `polarCone (pairing n)`, and the
equation is the definition unfolded. -/
theorem mem_polarCone_rn (K : Set (Rn n)) (y : Rn n) :
    y ∈ polarCone (pairing n) K ↔ ∀ x ∈ K, (inner ℝ x y : ℝ) ≤ 0 := Iff.rfl

/-- **Rockafellar's polar of a convex set** (§14, p. 125):
`C° = {x* | ⟨x, x*⟩ ≤ 1 for every x ∈ C}`. -/
theorem mem_polarSet_rn (C : Set (Rn n)) (y : Rn n) :
    y ∈ polarSet (pairing n) C ↔ ∀ x ∈ C, (inner ℝ x y : ℝ) ≤ 1 := Iff.rfl

/-- **Polarity is order-inverting** (§14): `C₁ ⊆ C₂` implies `C₂° ⊆ C₁°`. -/
theorem polarSet_anti_rn {C D : Set (Rn n)} (h : C ⊆ D) :
    polarSet (pairing n) D ⊆ polarSet (pairing n) C :=
  polarSet_anti h

/-- Order-inversion for cones. Specialises `polarCone_anti`. -/
theorem polarCone_anti_rn {K L : Set (Rn n)} (h : K ⊆ L) :
    polarCone (pairing n) L ⊆ polarCone (pairing n) K :=
  polarCone_anti h

/-- **The polar of a convex cone as a cone and as a set coincide** (§14): the half-space
`{x | ⟨x, x*⟩ ≤ 1}` contains `K` if and only if `{x | ⟨x, x*⟩ ≤ 0}` does. The hypothesis is
Rockafellar's "cone", closure under *positive* scalar multiplication. -/
theorem polarCone_eq_polarSet_rn {K : Set (Rn n)} (hK : ∀ a : ℝ, 0 < a → a • K = K) :
    polarCone (pairing n) K = polarSet (pairing n) K :=
  polarCone_eq_polarSet_of_isCone hK

/-- The bipolar of a set, with the `.flip` the backbone statement carries rewritten away;
`flip_pairing` says that `⟨·, ·⟩` on `ℝⁿ` is its own flip. -/
theorem polarSet_polarSet_rn {C : Set (Rn n)} (hconv : Convex ℝ C) (hcl : IsClosed C)
    (h0 : (0 : Rn n) ∈ C) :
    polarSet (pairing n) (polarSet (pairing n) C) = C := by
  simpa using polarSet_polarSet (B := pairing n) hconv hcl h0

/-! ### Theorem 14.1

The polarity correspondence for convex cones. The book prints no proof; see the module docstring. -/

/-- **Theorem 14.1**, first assertion: the polar of a convex cone is **non-empty** — it always
contains the origin. No hypothesis on `K` is needed. -/
theorem theorem_14_1_nonempty (K : Set (Rn n)) : (polarCone (pairing n) K).Nonempty :=
  polarCone_nonempty (pairing n) K

/-- **Theorem 14.1**, first assertion: the polar of a convex cone is **convex**. No hypothesis on
`K` is needed. -/
theorem theorem_14_1_convex (K : Set (Rn n)) : Convex ℝ (polarCone (pairing n) K) :=
  convex_polarCone (pairing n) K

/-- **Theorem 14.1**, first assertion: the polar of a convex cone is a **cone** in Rockafellar's
sense, `a K° = K°` for every `a > 0`. No hypothesis on `K` is needed. -/
theorem theorem_14_1_isCone (K : Set (Rn n)) {a : ℝ} (ha : 0 < a) :
    a • polarCone (pairing n) K = polarCone (pairing n) K :=
  smul_polarCone (pairing n) K a ha

/-- **Theorem 14.1**, first assertion: the polar of a convex cone is **closed**, being an
intersection of homogeneous closed half-spaces — which is Rockafellar's own remark that the first
assertion could also be derived from Corollary 11.7.1. No hypothesis on `K` is needed. -/
theorem theorem_14_1_isClosed (K : Set (Rn n)) : IsClosed (polarCone (pairing n) K) :=
  isClosed_polarCone

/-- **Theorem 14.1**, second assertion: `K°° = K` for a non-empty closed convex cone.

A non-empty closed cone in Rockafellar's sense contains the origin, so it is a `PointedCone`, and
the bundled `polarCone_polarCone_pointedCone` supplies convexity, positive homogeneity and
non-emptiness at once. -/
theorem theorem_14_1_bipolar (K : PointedCone ℝ (Rn n)) (hcl : IsClosed (K : Set (Rn n))) :
    polarCone (pairing n) (polarCone (pairing n) (K : Set (Rn n))) = (K : Set (Rn n)) := by
  simpa using polarCone_polarCone_pointedCone (B := pairing n) K hcl

/-- **Theorem 14.1**, third assertion: the indicator functions of `K` and `K°` are
conjugate to each other. This direction is the computation §14 opens with, and needs no closedness.

Specialises `conj_indicatorFn_eq_indicatorFn_polarCone`, with the hypothesis triple supplied by the
bundling. -/
theorem theorem_14_1_conj (K : PointedCone ℝ (Rn n)) :
    conj (pairing n) (indicatorFn (K : Set (Rn n)))
      = indicatorFn (polarCone (pairing n) (K : Set (Rn n))) :=
  conj_indicatorFn_eq_indicatorFn_polarCone (smul_coe_pointedCone K) ⟨0, K.zero_mem⟩

/-- **Theorem 14.1**, third assertion, in the remaining direction: `δ(· | K°)*` is
`δ(· | K)` for a non-empty closed convex cone. -/
theorem theorem_14_1_conj_dual (K : PointedCone ℝ (Rn n)) (hcl : IsClosed (K : Set (Rn n))) :
    conj (pairing n) (indicatorFn (polarCone (pairing n) (K : Set (Rn n))))
      = indicatorFn (K : Set (Rn n)) := by
  simpa using conj_indicatorFn_polarCone_pointedCone (B := pairing n) K hcl

/-- **`(cl K)° = K°`** (§14), the invariance that lets Theorem 14.1 be stated for closed
cones without loss. Specialises `polarCone_closure`. -/
theorem polarCone_closure_rn (K : Set (Rn n)) :
    polarCone (pairing n) (closure K) = polarCone (pairing n) K :=
  polarCone_closure K

/-- **`K°° = cl K`** (§14) for a convex cone that need not be closed. -/
theorem polarCone_polarCone_rn (K : PointedCone ℝ (Rn n)) :
    polarCone (pairing n) (polarCone (pairing n) (K : Set (Rn n)))
      = closure (K : Set (Rn n)) := by
  simpa using polarCone_polarCone_pointedCone_eq_closure (B := pairing n) K

/-! ### The examples of §14 (pp. 122–123) -/

/-- **The polar of a subspace is the orthogonally complementary subspace** (§14). For the Euclidean
pairing the annihilator of `L` is Mathlib's `Submodule.orthogonal`. -/
theorem polarCone_submodule_rn (L : Submodule ℝ (Rn n)) :
    polarCone (pairing n) (L : Set (Rn n)) = (Lᗮ : Set (Rn n)) := by
  rw [polarCone_coe_submodule' (pairing n) L]
  ext y
  simp only [Set.mem_ofPred_eq, pairing_apply, SetLike.mem_coe, Submodule.mem_orthogonal]

/-- **The polar of the non-negative orthant is the non-positive orthant** (§14).

`nonnegOrthant` is §12's. -/
theorem polarCone_nonnegOrthant_rn (n : ℕ) :
    polarCone (pairing n) (nonnegOrthant n) = {y : Rn n | ∀ j, y j ≤ 0} :=
  polarCone_nonnegOrthant

/-- **The polar of the convex cone generated by a family `{aᵢ}`** is the solution set of the
homogeneous inequalities `⟨aᵢ, x*⟩ ≤ 0` (§14). -/
theorem polarCone_hull_range_rn {ι : Sort*} (a : ι → Rn n) :
    polarCone (pairing n) (PointedCone.hull ℝ (Set.range a) : Set (Rn n))
      = {y : Rn n | ∀ i, (inner ℝ (a i) y : ℝ) ≤ 0} :=
  polarCone_hull_range (pairing n) a

/-- **Dually** (§14): the polar of `{y | ⟨aᵢ, y⟩ ≤ 0 for every i}` is the closure of the
convex cone generated by the `aᵢ`. -/
theorem polarCone_setOf_forall_le_zero_rn {ι : Sort*} (a : ι → Rn n) :
    polarCone (pairing n) {y : Rn n | ∀ i, (inner ℝ (a i) y : ℝ) ≤ 0}
      = closure (PointedCone.hull ℝ (Set.range a) : Set (Rn n)) := by
  simpa using polarCone_setOf_forall_le_zero (B := pairing n) a

/-! ### Theorem 14.2 -/

/-- **Theorem 14.2**, first assertion. Let `f` be a proper convex function. The polar
of the convex cone generated by `dom f` is the recession cone of `f*`.

The backbone's second properness hypothesis is discharged by Theorem 12.2 (`theorem_12_2_proper`),
which is available on `ℝⁿ`. -/
theorem theorem_14_2 {f : Rn n → EReal} (hf : ConvexFn f) (hp : Proper f) :
    polarCone (pairing n) (PointedCone.hull ℝ (dom f) : Set (Rn n))
      = recessionConeFn (conj (pairing n) f) :=
  recessionConeFn_conj_hull hp ((theorem_12_2_proper hf).2 hp)

/-- **Theorem 14.2**, second assertion. If `f` is closed, the polar of the recession
cone of `f` is the closure of the convex cone generated by `dom f*`. -/
theorem theorem_14_2_dual {f : Rn n → EReal} (hf : ClosedProperConvexFn f) :
    polarCone (pairing n) (recessionConeFn f)
      = closure (PointedCone.hull ℝ (dom (conj (pairing n) f)) : Set (Rn n)) :=
  polarCone_recessionConeFn hf.convex hf.closed hf.proper

/-- **Corollary 14.2.1.** The polar of the barrier cone of a non-empty closed convex
set `C` is the recession cone of `C`.

`barrierCone` is §13's. -/
theorem corollary_14_2_1 {C : Set (Rn n)} (hC : Convex ℝ C) (hcl : IsClosed C)
    (hne : C.Nonempty) :
    polarCone (pairing n) (barrierCone C) = recessionCone C := by
  rw [barrierCone_eq_dom_supportFn]
  simpa using polarCone_dom_supportFn (B := pairing n) hC hcl hne

/-- **Corollary 14.2.2.** Let `f` be a closed proper convex function. In order that
`{x | f x ≤ α}` be bounded for every `α ∈ ℝ`, it is necessary and sufficient that
`0 ∈ int (dom f*)`. -/
theorem corollary_14_2_2 {f : Rn n → EReal} (hf : ClosedProperConvexFn f) :
    (∀ α : ℝ, Bornology.IsBounded {x : Rn n | f x ≤ (α : EReal)})
      ↔ (0 : Rn n) ∈ interior (dom (conj (pairing n) f)) :=
  isBounded_setOf_le_iff_zero_mem_interior_dom_conj hf.convex hf.closed hf.proper

/-! ### Theorem 14.3

Rockafellar's hypothesis `f(0) > 0 > inf f` is self-dual: `f*(0) = -inf f` and `inf f* = -f(0)`
(`conj_apply_zero`, `iInf_conj_eq_neg_apply_zero`), so `f*(0) > 0 > inf f*` as well. -/

/-- **Theorem 14.3.** Let `f` be a closed proper convex function with
`f(0) > 0 > inf f`. The closed convex cones generated by `{x | f x ≤ 0}` and by
`{x* | f*(x*) ≤ 0}` are polar to each other; this is one of the two directions. -/
theorem theorem_14_3 {f : Rn n → EReal} (hf : ClosedProperConvexFn f) (h0 : 0 < f 0)
    (hinf : ⨅ x, f x < 0) :
    polarCone (pairing n) (closure (PointedCone.hull ℝ {x : Rn n | f x ≤ 0} : Set (Rn n)))
      = closure (PointedCone.hull ℝ {y : Rn n | conj (pairing n) f y ≤ 0} : Set (Rn n)) := by
  have hg : ClosedProperConvexFn (conj (pairing n) f) :=
    ⟨convexFn_conj _ _, closedFn_conj, proper_conj hf⟩
  have hg0 : 0 < conj (pairing n) f 0 := by
    rw [conj_apply_zero]
    exact EReal.neg_pos.2 hinf
  have hginf : ⨅ y, conj (pairing n) f y < 0 := by
    rw [iInf_conj_eq_neg_apply_zero hf.convex hf.closed]
    exact EReal.neg_lt_zero.2 h0
  rw [polarCone_closure, polarCone_hull, polarCone_eq_setOf_supportFn_le_zero,
    supportFn_setOf_le_zero hf.convex hf.closed, setOf_clFn_posHomGen_le_zero hg hg0 hginf]

/-- **Theorem 14.3**, in the remaining direction: the polar of the closed convex cone
generated by `{x* | f*(x*) ≤ 0}` is the closed convex cone generated by `{x | f x ≤ 0}`.

Theorem 14.3 rewrites the inner cone as a polar, and the bipolar theorem
(`polarCone_polarCone_rn`) closes it. -/
theorem theorem_14_3_dual {f : Rn n → EReal} (hf : ClosedProperConvexFn f) (h0 : 0 < f 0)
    (hinf : ⨅ x, f x < 0) :
    polarCone (pairing n)
        (closure (PointedCone.hull ℝ {y : Rn n | conj (pairing n) f y ≤ 0} : Set (Rn n)))
      = closure (PointedCone.hull ℝ {x : Rn n | f x ≤ 0} : Set (Rn n)) := by
  have h := theorem_14_3 hf h0 hinf
  rw [polarCone_closure, polarCone_hull] at h
  rw [← h, ← polarCone_hull (pairing n) {x : Rn n | f x ≤ 0}, polarCone_polarCone_rn]

/-! ### Theorem 14.4

`K` is the convex cone in `ℝⁿ⁺²` generated by the `(1, x, μ)` with `μ ≥ f(x)`, and `K*` the same
cone built from `f*`. The theorem reads the conjugate of `f` off the polar of `K` — conjugacy from
polarity, the direction opposite to the rest of §14. The mathematics lives in `ℝ × ℝⁿ × ℝ`, where
the cone is `homCone f`; `triple` concatenates that space into `ℝⁿ⁺²`. -/

/-- The vector `(λ, x, μ) ∈ ℝⁿ⁺²`: a scalar, a vector of `ℝⁿ` and a scalar, concatenated. -/
noncomputable abbrev triple (l : ℝ) (x : Rn n) (m : ℝ) : Rn (n + 2) :=
  euclideanTripleEquiv n ((l, x), m)

/-- **Rockafellar's mapping** `(λ*, x*, μ*) ↦ (-μ*, x*, -λ*)` of `ℝⁿ⁺²` (§14, the display in the
proof of Theorem 14.4). -/
noncomputable def endsReflection (n : ℕ) : Rn (n + 2) → Rn (n + 2) := fun z =>
  euclideanTripleEquiv n (negSwapEnds (Rn n) ((euclideanTripleEquiv n).symm z))

@[simp] theorem endsReflection_triple (l : ℝ) (x : Rn n) (m : ℝ) :
    endsReflection n (triple l x m) = triple (-m) x (-l) := by
  simp [endsReflection]

/-- The inner product of `ℝⁿ⁺²` read through the concatenation is the pairing the backbone's cone
theory is stated against. -/
theorem pairing_euclideanTripleEquiv (p q : (ℝ × Rn n) × ℝ) :
    pairing (n + 2) (euclideanTripleEquiv n p) (euclideanTripleEquiv n q)
      = homConePairing (pairing n) p q :=
  inner_euclideanTripleEquiv p q

/-- The generating vectors `(1, x, μ)` with `μ ≥ g(x)`, read through the concatenation: they are
the epigraph of the level-one lift of `g`. -/
theorem setOf_triple_one_eq_image (g : Rn n → EReal) :
    {z : Rn (n + 2) | ∃ x : Rn n, ∃ μ : ℝ, g x ≤ (μ : EReal) ∧ z = triple 1 x μ}
      = euclideanTripleEquiv n '' epi (levelOneLift g) := by
  ext z
  constructor
  · rintro ⟨x, μ, hμ, rfl⟩
    exact ⟨((1, x), μ), mk_one_mem_epi_levelOneLift.2 hμ, rfl⟩
  · rintro ⟨⟨⟨a, x⟩, μ⟩, hp, rfl⟩
    rw [mem_epi_levelOneLift] at hp
    obtain ⟨rfl, hμ⟩ := hp
    exact ⟨x, μ, hμ, rfl⟩

/-- The book's reflection and the backbone's are the same map, read through the concatenation. -/
theorem preimage_endsReflection_image (P : Set ((ℝ × Rn n) × ℝ)) :
    endsReflection n ⁻¹' (euclideanTripleEquiv n '' P)
      = euclideanTripleEquiv n '' (negSwapEnds (Rn n) ⁻¹' P) := by
  ext z
  simp only [Set.mem_preimage, Set.mem_image, endsReflection]
  constructor
  · rintro ⟨v, hv, heq⟩
    refine ⟨(euclideanTripleEquiv n).symm z, ?_, by simp⟩
    have hveq : v = negSwapEnds (Rn n) ((euclideanTripleEquiv n).symm z) :=
      (euclideanTripleEquiv n).injective heq
    rwa [← hveq]
  · rintro ⟨w, hw, rfl⟩
    exact ⟨negSwapEnds (Rn n) w, hw, by rw [ContinuousLinearEquiv.symm_apply_apply]⟩

/-- **Theorem 14.4.** Let `f` be a closed proper convex function on `ℝⁿ`, let `K` be
the convex cone generated by the vectors `(1, x, μ) ∈ ℝⁿ⁺²` with `μ ≥ f(x)`, and let `K*` be the
convex cone generated by the `(1, x*, μ*)` with `μ* ≥ f*(x*)`. Then

`cl K* = {(λ*, x*, μ*) | (-μ*, x*, -λ*) ∈ K°}`.

Closedness of `f` is used in one place only, to give `dom f* ≠ ∅`. -/
theorem theorem_14_4 {f : Rn n → EReal} (hf : ClosedProperConvexFn f) :
    closure (PointedCone.hull ℝ {z : Rn (n + 2) | ∃ y : Rn n, ∃ ν : ℝ,
        conj (pairing n) f y ≤ (ν : EReal) ∧ z = triple 1 y ν} : Set (Rn (n + 2)))
      = endsReflection n ⁻¹' polarCone (pairing (n + 2))
          (PointedCone.hull ℝ {z : Rn (n + 2) | ∃ x : Rn n, ∃ μ : ℝ,
            f x ≤ (μ : EReal) ∧ z = triple 1 x μ} : Set (Rn (n + 2))) := by
  have hg : ClosedProperConvexFn (conj (pairing n) f) :=
    ⟨convexFn_conj _ _, closedFn_conj, proper_conj hf⟩
  have hhull : ∀ S : Set ((ℝ × Rn n) × ℝ),
      (PointedCone.hull ℝ (euclideanTripleEquiv n '' S) : Set (Rn (n + 2)))
        = euclideanTripleEquiv n '' (PointedCone.hull ℝ S : Set ((ℝ × Rn n) × ℝ)) := fun S =>
    coe_hull_image ((euclideanTripleEquiv n) : ((ℝ × Rn n) × ℝ) →ₗ[ℝ] Rn (n + 2)) S
  have hpolar : polarCone (pairing (n + 2)) (euclideanTripleEquiv n '' epi (levelOneLift f))
      = euclideanTripleEquiv n ''
          polarCone (homConePairing (pairing n)) (epi (levelOneLift f)) :=
    polarCone_image_of_pairing_eq (euclideanTripleEquiv n).toLinearEquiv
      (euclideanTripleEquiv n).toLinearEquiv pairing_euclideanTripleEquiv _
  rw [setOf_triple_one_eq_image, hhull, ← homCone_eq_coe_hull hg.convex, polarCone_hull,
    setOf_triple_one_eq_image, hpolar, ← polarCone_homCone hf.convex,
    closure_image_euclideanTripleEquiv, preimage_endsReflection_image,
    closure_homCone_conj hf.convex hf.proper.dom_nonempty (proper_conj hf).dom_nonempty]

/-! ### Theorem 14.5

The polarity correspondence for closed convex sets containing the origin. The book prints no proof;
see the module docstring. -/

/-- **Theorem 14.5**, first assertion: `C°` is **closed**.
Specialises `isClosed_polarSet`; no hypothesis on `C` is needed. -/
theorem theorem_14_5_isClosed (C : Set (Rn n)) : IsClosed (polarSet (pairing n) C) :=
  isClosed_polarSet

/-- **Theorem 14.5**, first assertion: `C°` is **convex**.
Specialises `convex_polarSet`; no hypothesis on `C` is needed. -/
theorem theorem_14_5_convex (C : Set (Rn n)) : Convex ℝ (polarSet (pairing n) C) :=
  convex_polarSet (pairing n) C

/-- **Theorem 14.5**, first assertion: `C°` **contains the origin**.
Specialises `zero_mem_polarSet`; no hypothesis on `C` is needed. -/
theorem theorem_14_5_zero_mem (C : Set (Rn n)) : (0 : Rn n) ∈ polarSet (pairing n) C :=
  zero_mem_polarSet (pairing n) C

/-- **Theorem 14.5**, first assertion: `C°° = C` for a closed convex set containing
the origin. Specialises `polarSet_polarSet`. -/
theorem theorem_14_5_bipolar {C : Set (Rn n)} (hconv : Convex ℝ C) (hcl : IsClosed C)
    (h0 : (0 : Rn n) ∈ C) :
    polarSet (pairing n) (polarSet (pairing n) C) = C :=
  polarSet_polarSet_rn hconv hcl h0

/-- **Theorem 14.5**, second assertion: the gauge function of `C` is the support
function of `C°`.

Obtained from `gaugeFn_polarSet` at `C°` together with `C°° = C`; the backbone records that only
`0 ∈ C°` — which is automatic — is needed for that step. -/
theorem theorem_14_5_gauge {C : Set (Rn n)} (hconv : Convex ℝ C) (hcl : IsClosed C)
    (h0 : (0 : Rn n) ∈ C) :
    gaugeFn C = supportFn (pairing n) (polarSet (pairing n) C) := by
  conv_lhs => rw [← polarSet_polarSet_rn hconv hcl h0]
  exact gaugeFn_polarSet (zero_mem_polarSet (pairing n) C)

/-- **Theorem 14.5**, third assertion: dually, the gauge function of `C°` is the support function of
`C`. It needs only `0 ∈ C`. -/
theorem theorem_14_5_gauge_dual {C : Set (Rn n)} (h0 : (0 : Rn n) ∈ C) :
    gaugeFn (polarSet (pairing n) C) = supportFn (pairing n) C :=
  gaugeFn_polarSet h0

/-- **`C° = D°` where `D = cl(conv(C ∪ {0}))`** (§14): a half-space `{x | ⟨x, x*⟩ ≤ 1}`
contains `C` if and only if it contains `D`, because such a half-space is closed and convex and
contains the origin. -/
theorem polarSet_convexHullZero_rn (C : Set (Rn n)) :
    polarSet (pairing n) (closure (convexHull ℝ (C ∪ {0}))) = polarSet (pairing n) C := by
  refine subset_antisymm (polarSet_anti ?_) ?_
  · exact (Set.subset_union_left.trans (subset_convexHull ℝ _)).trans subset_closure
  · have hD : closure (convexHull ℝ (C ∪ {0}))
        ⊆ polarSet (pairing n) (polarSet (pairing n) C) := by
      refine closure_minimal (convexHull_min ?_ (convex_polarSet _ _)) isClosed_polarSet
      refine Set.union_subset ?_ ?_
      · simpa using subset_polarSet_polarSet (pairing n) C
      · simp
    have h := polarSet_anti (B := pairing n) hD
    rwa [polarSet_polarSet_rn (convex_polarSet _ _) isClosed_polarSet
      (zero_mem_polarSet (pairing n) C)] at h

/-- **`C°° = cl(conv(C ∪ {0}))`** (§14), the identity that makes Theorem 14.5's
hypotheses exactly the right ones: the bipolar of an arbitrary set is the smallest closed convex
set containing it and the origin. -/
theorem polarSet_polarSet_convexHullZero_rn (C : Set (Rn n)) :
    polarSet (pairing n) (polarSet (pairing n) C) = closure (convexHull ℝ (C ∪ {0})) := by
  rw [← polarSet_convexHullZero_rn C]
  refine polarSet_polarSet_rn (convex_convexHull ℝ _).closure isClosed_closure ?_
  exact subset_closure (subset_convexHull ℝ _ (Set.mem_union_right _ rfl))

/-- **Corollary 14.5.1.** Let `C` be a closed convex set containing the origin. Then
`C°` is bounded if and only if `0 ∈ int C`. -/
theorem corollary_14_5_1 {C : Set (Rn n)} (hconv : Convex ℝ C) (hcl : IsClosed C)
    (h0 : (0 : Rn n) ∈ C) :
    Bornology.IsBounded (polarSet (pairing n) C) ↔ (0 : Rn n) ∈ interior C :=
  isBounded_polarSet_iff_zero_mem_interior hconv hcl h0

/-- **Corollary 14.5.1**, dual form: `C` is bounded if and only if `0 ∈ int C°`. This is Corollary
14.5.1 applied to `C°` together with `C°° = C`. -/
theorem corollary_14_5_1_dual {C : Set (Rn n)} (hconv : Convex ℝ C) (hcl : IsClosed C)
    (h0 : (0 : Rn n) ∈ C) :
    Bornology.IsBounded C ↔ (0 : Rn n) ∈ interior (polarSet (pairing n) C) :=
  isBounded_iff_zero_mem_interior_polarSet hconv hcl h0

/-! ### Theorem 14.6 -/

/-- **Theorem 14.6**, first assertion: the polar of the recession cone of `C` is the
closure of the convex cone generated by `C°`. -/
theorem theorem_14_6_recession {C : Set (Rn n)} (hconv : Convex ℝ C) (hcl : IsClosed C)
    (h0 : (0 : Rn n) ∈ C) :
    polarCone (pairing n) (recessionCone C)
      = closure (PointedCone.hull ℝ (polarSet (pairing n) C) : Set (Rn n)) :=
  polarCone_recessionCone hconv hcl h0

/-- **Theorem 14.6**, first assertion, in the other direction: the polar of the closed
convex cone generated by `C°` is the recession cone of `C`. With `theorem_14_6_recession` this is
the book's "polar to each other". -/
theorem theorem_14_6_recession_dual {C : Set (Rn n)} (hconv : Convex ℝ C) (hcl : IsClosed C)
    (h0 : (0 : Rn n) ∈ C) :
    polarCone (pairing n) (closure (PointedCone.hull ℝ (polarSet (pairing n) C) : Set (Rn n)))
      = recessionCone C := by
  rw [polarCone_closure, polarCone_hull]
  have h := recessionCone_eq_polarCone_polarSet (B := pairing n) hconv hcl h0
  rw [flip_pairing] at h
  exact h.symm

/-- **Theorem 14.6**, second assertion: the lineality space of `C` and the subspace
generated by `C°` are orthogonally complementary — here in the form "the lineality space of `C` is
the annihilator of `C°`". -/
theorem theorem_14_6_lineality {C : Set (Rn n)} (hconv : Convex ℝ C) (hcl : IsClosed C)
    (h0 : (0 : Rn n) ∈ C) :
    linealitySpace C
      = {x : Rn n | ∀ y ∈ polarSet (pairing n) C, (inner ℝ x y : ℝ) = 0} :=
  linealitySpace_eq_setOf_pairing_eq_zero hconv hcl h0

/-- **Theorem 14.6**, second assertion, dual form: the polar of the lineality space of
`C` is the closed subspace generated by `C°`. -/
theorem theorem_14_6_lineality_dual {C : Set (Rn n)} (hconv : Convex ℝ C) (hcl : IsClosed C)
    (h0 : (0 : Rn n) ∈ C) :
    polarCone (pairing n) (linealitySpace C)
      = closure (Submodule.span ℝ (polarSet (pairing n) C) : Set (Rn n)) :=
  polarCone_linealitySpace hconv hcl h0

/-! ### Corollary 14.6.1 -/

/-- Rockafellar's **rank** of a convex set (§8, p. 70): `rank C = dim C - lineality C`. §13's
`rankFn` is the companion for convex functions. -/
noncomputable def rankSet (C : Set (Rn n)) : ℤ := dim C - (lineality C : ℤ)

/-- **Corollary 14.6.1**, first relation: `dim C° = n - lineality C` for a closed
convex set `C` containing the origin.

`dim` is §1's, and the affine hull of `C°` is a subspace because `0 ∈ C°`. -/
theorem corollary_14_6_1_dim {C : Set (Rn n)} (hconv : Convex ℝ C) (hcl : IsClosed C)
    (h0 : (0 : Rn n) ∈ C) :
    dim (polarSet (pairing n) C) = (n : ℤ) - (lineality C : ℤ) := by
  have h := finrank_vectorSpan_polarSet_add_lineality (B := pairing n) hconv hcl h0
  rw [finrank_euclideanSpace_fin] at h
  rw [dim_of_nonempty ⟨0, zero_mem_polarSet (pairing n) C⟩]
  omega

/-- **Corollary 14.6.1**, second relation: `lineality C° = n - dim C`. -/
theorem corollary_14_6_1_lineality {C : Set (Rn n)} (hconv : Convex ℝ C) (hcl : IsClosed C)
    (h0 : (0 : Rn n) ∈ C) :
    (lineality (polarSet (pairing n) C) : ℤ) = (n : ℤ) - dim C := by
  have h := finrank_vectorSpan_add_lineality_polarSet (B := pairing n) hconv hcl h0
  rw [finrank_euclideanSpace_fin] at h
  rw [dim_of_nonempty ⟨0, h0⟩]
  omega

/-- **Corollary 14.6.1**, third relation: `rank C° = rank C`. It is the difference of the other two,
both of which read `n`. -/
theorem corollary_14_6_1_rank {C : Set (Rn n)} (hconv : Convex ℝ C) (hcl : IsClosed C)
    (h0 : (0 : Rn n) ∈ C) :
    rankSet (polarSet (pairing n) C) = rankSet C := by
  rw [rankSet, rankSet, corollary_14_6_1_dim hconv hcl h0,
    corollary_14_6_1_lineality hconv hcl h0]
  ring

/-! ### Theorem 14.7 -/

/-- **Theorem 14.7**, first assertion: if `f` is non-negative and vanishes at the origin, then
`f*` is likewise non-negative. -/
theorem theorem_14_7_conj_nonneg {f : Rn n → EReal} (h0 : f 0 = 0) (y : Rn n) :
    0 ≤ conj (pairing n) f y :=
  zero_le_conj (le_of_eq h0) y

/-- **Theorem 14.7**, first assertion: `f*` vanishes at the origin. -/
theorem theorem_14_7_conj_zero {f : Rn n → EReal} (hnn : ∀ x, 0 ≤ f x) (h0 : f 0 = 0) :
    conj (pairing n) f 0 = 0 :=
  conj_zero_eq_zero hnn (le_of_eq h0)

/-- **Theorem 14.7**, first inclusion: `{x | f x ≤ α}° ⊆ α⁻¹ {x* | f* x* ≤ α}` for
`0 < α < ∞`.

Stated without the closedness the book assumes: one inclusion is a rescaling into the level set,
the other is Fenchel's inequality, and neither uses it. -/
theorem theorem_14_7_left {f : Rn n → EReal} (hf : ConvexFn f) (hnn : ∀ x, 0 ≤ f x)
    (h0 : f 0 = 0) {α : ℝ} (hα : 0 < α) :
    polarSet (pairing n) {x : Rn n | f x ≤ (α : EReal)}
      ⊆ α⁻¹ • {y : Rn n | conj (pairing n) f y ≤ (α : EReal)} :=
  (polarSet_setOf_le_subset_and_subset hf hnn (le_of_eq h0) hα).1

/-- **Theorem 14.7**, second inclusion:
`α⁻¹ {x* | f* x* ≤ α} ⊆ 2 {x | f x ≤ α}°`. -/
theorem theorem_14_7_right {f : Rn n → EReal} (hf : ConvexFn f) (hnn : ∀ x, 0 ≤ f x)
    (h0 : f 0 = 0) {α : ℝ} (hα : 0 < α) :
    α⁻¹ • {y : Rn n | conj (pairing n) f y ≤ (α : EReal)}
      ⊆ (2 : ℝ) • polarSet (pairing n) {x : Rn n | f x ≤ (α : EReal)} :=
  (polarSet_setOf_le_subset_and_subset hf hnn (le_of_eq h0) hα).2

end Rockafellar
