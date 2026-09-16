import Numlib.Analysis.Convex.Duality.Barrier
import Numlib.Analysis.Convex.Duality.Level
import Numlib.Analysis.Convex.Duality.SupportRelint
import Numlib.Analysis.Convex.Recession.Conjugate
import Numlib.Analysis.Convex.Subdifferential.Convergence
import NumlibSurface.Rockafellar.Chapter01.Section01

/-!
# Rockafellar, §13: Support Functions

The support function `δ*(· | C)` of a convex set, the bijection between closed convex sets and
closed proper positively homogeneous convex functions, and the derivation of the support functions
of `dom f`, `dom f*` and of a level set `{x | f x ≤ 0}` from the conjugate `f*`. All 15 numbered
results of §13 are formalized. Theorem 13.2's bijection is `theorem_13_2_correspondence`.

## The section's definitions

* **The support function** `δ*(x* | C) = sup {⟨x, x*⟩ | x ∈ C}` is the backbone's `supportFn`;
  `supportFn_apply_rn` records that it is the book's formula verbatim.
* **The barrier cone** of `C` is `dom δ*(· | C)`, recorded as `barrierCone`, with the bridge
  `barrierCone_eq_dom_supportFn` and the unfolded form `mem_barrierCone_iff`.
* **Co-finite** is the backbone's `Cofinite`: closed, proper, convex, and `f0⁺ = +∞` in every
  non-zero direction — the epigraph contains no non-vertical half-line.
* **Rank** is `rankFn f = dim (dom f) - lineality f`, defined here rather than in §8 because it
  needs §1's affine-hull dimension `dim`; Corollary 13.4.1 is its first consumer.

The unnumbered running text of the section is recorded too: the infimum formula
`inf {⟨x, x*⟩ | x ∈ C} = -δ*(-x* | C)` (`infimum_eq_neg_supportFn_neg`); the half-space description
`C ⊆ {x | ⟨x, x*⟩ ≤ β} ↔ β ≥ δ*(x* | C)` (`subset_halfspace_iff`); the invariance
`δ*(·|C) = δ*(·|cl C) = δ*(·|ri C)`; the additivity `δ*(·|C₁+C₂) = δ*(·|C₁) + δ*(·|C₂)`; the
recovery of a closed convex set from its support function (`eq_setOf_le_supportFn`); the
subadditivity noted after Theorem 13.2; and the Euclidean-norm example `|x| = δ*(x | B)` with its
translate-and-scale form.

## References

* [rockafellar1970convex] §13.
-/

open Set Pointwise

namespace Rockafellar

open ConvexAnalysis

variable {n : ℕ}

/-! ### The definitions of §13 -/

/-- **Rockafellar's support function** (§13, p. 112): `δ*(x* | C) = sup {⟨x, x*⟩ | x ∈ C}`. This is
the backbone's `supportFn (pairing n) C`, and the equation is the definition unfolded. -/
theorem supportFn_apply_rn (C : Set (Rn n)) (y : Rn n) :
    supportFn (pairing n) C y = ⨆ x ∈ C, ((inner ℝ x y : ℝ) : EReal) :=
  supportFn_apply (pairing n) C y

/-- **Rockafellar's barrier cone** (§13, p. 112): the effective domain of `δ*(· | C)`, the set of
directions in which a linear function is bounded above on `C`. -/
def barrierCone (C : Set (Rn n)) : Set (Rn n) := dom (supportFn (pairing n) C)

/-- The bridge: the barrier cone *is* `dom δ*(· | C)`. -/
theorem barrierCone_eq_dom_supportFn (C : Set (Rn n)) :
    barrierCone C = dom (supportFn (pairing n) C) := rfl

/-- The barrier cone unfolded: `x*` is a barrier direction exactly when `⟨·, x*⟩` is bounded above
on `C`. -/
theorem mem_barrierCone_iff (C : Set (Rn n)) (y : Rn n) :
    y ∈ barrierCone C ↔ ∃ c : ℝ, ∀ x ∈ C, inner ℝ x y ≤ c := by
  rw [barrierCone_eq_dom_supportFn, dom_supportFn]
  exact Iff.rfl

/-- **Rockafellar's co-finite convex functions** (§13, p. 116): closed proper convex functions whose
epigraph contains no non-vertical half-line, i.e. with `(f0⁺)(y) = +∞` for every `y ≠ 0`. This is
the backbone's `Cofinite`, transcribed without change. -/
theorem cofinite_iff_rn (f : Rn n → EReal) :
    Cofinite f ↔ ClosedProperConvexFn f ∧ ∀ y : Rn n, y ≠ 0 → recessionFn f y = ⊤ :=
  ⟨fun h => ⟨h.toClosedProperConvexFn, h.recessionFn_eq_top⟩,
    fun h => { h.1 with recessionFn_eq_top := h.2 }⟩

/-- **Rockafellar's rank of a convex function** (§8, p. 70): `rank f = dim f - lineality f`, where
`dim f` is the dimension of `dom f` and the lineality of `f` is the dimension of its lineality
space. Defined here rather than in §8 because it needs §1's `dim`; Corollary 13.4.1 is the first
result that uses it. -/
noncomputable def rankFn (f : Rn n → EReal) : ℤ := dim (dom f) - (linealityFn f : ℤ)

/-! ### Properness of the conjugate

Rockafellar states Theorems 13.3 and 13.4 for a *proper convex* `f`; the backbone asks in addition
that `f*` be proper, which in `ℝⁿ` is automatic — Theorem 12.2, through Theorem 7.4. -/

/-! ### The unnumbered running text of pp. 112–114 -/

/-- **Rockafellar, §13, p. 112**: minimisation of linear functions over `C` is covered too, since
`inf {⟨x, x*⟩ | x ∈ C} = -δ*(-x* | C)`. -/
theorem infimum_eq_neg_supportFn_neg (C : Set (Rn n)) (y : Rn n) :
    ⨅ x ∈ C, ((inner ℝ x y : ℝ) : EReal) = -supportFn (pairing n) C (-y) := by
  rw [supportFn_apply_rn, EReal.neg_iSup]
  refine iInf_congr fun x => ?_
  rw [EReal.neg_iSup]
  refine iInf_congr fun _ => ?_
  rw [inner_neg_right, EReal.coe_neg, neg_neg]

/-- **Rockafellar, §13, p. 112**: the support function describes all the closed half-spaces
containing `C` — `C ⊆ {x | ⟨x, x*⟩ ≤ β}` if and only if `β ≥ δ*(x* | C)`. -/
theorem subset_halfspace_iff (C : Set (Rn n)) (y : Rn n) (β : ℝ) :
    C ⊆ {x : Rn n | inner ℝ x y ≤ β} ↔ supportFn (pairing n) C y ≤ (β : EReal) :=
  ⟨fun h => supportFn_le_coe_iff.2 fun _ hx => h hx, fun h _ hx => supportFn_le_coe_iff.1 h _ hx⟩

/-- **Rockafellar, §13, p. 112**: the support function does not see the closure. -/
theorem supportFn_closure_rn (C : Set (Rn n)) :
    supportFn (pairing n) (closure C) = supportFn (pairing n) C :=
  supportFn_closure C

/-- **Rockafellar, §13, p. 112**: nor does it see the relative interior, for convex `C`. -/
theorem supportFn_relint_rn {C : Set (Rn n)} (hC : Convex ℝ C) :
    supportFn (pairing n) (ri C) = supportFn (pairing n) C := by
  rw [← supportFn_closure (B := pairing n) (ri C), hC.closure_relint, supportFn_closure]

/-- **Rockafellar, §13, p. 113**: addition of sets is converted into addition of functions. -/
theorem supportFn_add_rn (C₁ C₂ : Set (Rn n)) :
    supportFn (pairing n) (C₁ + C₂) = supportFn (pairing n) C₁ + supportFn (pairing n) C₂ :=
  supportFn_add (pairing n) C₁ C₂

/-- **Rockafellar, §13, p. 113**: a closed convex set is the solution set of the system of
inequalities given by its support function, so it is completely determined by it. -/
theorem eq_setOf_le_supportFn {C : Set (Rn n)} (hC : Convex ℝ C) (hCcl : IsClosed C) :
    C = {x : Rn n | ∀ y : Rn n, ((inner ℝ x y : ℝ) : EReal) ≤ supportFn (pairing n) C y} := by
  ext x
  have h := mem_closure_convexHull_iff_le_supportFn (B := pairing n) C x
  rw [hC.convexHull_eq, hCcl.closure_eq] at h
  exact h

/-- **Rockafellar, §13, p. 114**: the Euclidean norm is the support function of the unit ball. -/
theorem supportFn_unitBall (x : Rn n) :
    supportFn (pairing n) (Metric.closedBall (0 : Rn n) 1) x = ((‖x‖ : ℝ) : EReal) := by
  rw [supportFn_closedBall zero_le_one, one_mul]

/-- **Rockafellar, §13, p. 114**: the support function of the ball `a + λB`, `λ ≥ 0`, is
`⟨x, a⟩ + λ|x|`. -/
theorem supportFn_ball (a : Rn n) {lam : ℝ} (hlam : 0 ≤ lam) (x : Rn n) :
    supportFn (pairing n) ({a} + Metric.closedBall (0 : Rn n) lam) x =
      ((inner ℝ a x : ℝ) : EReal) + ((lam * ‖x‖ : ℝ) : EReal) := by
  rw [supportFn_add, Pi.add_apply, supportFn_singleton, supportFn_closedBall hlam]
  rfl

/-! ### Theorem 13.1 -/

/-- **Theorem 13.1**, first clause. Let `C` be a convex set. Then `x ∈ cl C` if and
only if `⟨x, x*⟩ ≤ δ*(x* | C)` for every vector `x*`.

Specialises `mem_closure_convexHull_iff_le_supportFn` — Corollary 11.5.1 read through the
pairing. -/
theorem theorem_13_1_cl {C : Set (Rn n)} (hC : Convex ℝ C) (x : Rn n) :
    x ∈ closure C ↔ ∀ y : Rn n, ((inner ℝ x y : ℝ) : EReal) ≤ supportFn (pairing n) C y := by
  have h := mem_closure_convexHull_iff_le_supportFn (B := pairing n) C x
  rw [hC.convexHull_eq] at h
  exact h

/-- **Theorem 13.1**, second clause. `x ∈ ri C` if and only if the same condition holds, with strict
inequality for each `x*` such that `-δ*(-x* | C) ≠ δ*(x* | C)`. Specialises
`mem_relint_iff_lt_supportFn` — Corollary 11.6.2 read through the pairing. -/
theorem theorem_13_1_ri {C : Set (Rn n)} (hC : Convex ℝ C) (x : Rn n) :
    x ∈ ri C ↔ (∀ y : Rn n, ((inner ℝ x y : ℝ) : EReal) ≤ supportFn (pairing n) C y) ∧
      ∀ y : Rn n, -supportFn (pairing n) C (-y) ≠ supportFn (pairing n) C y →
        ((inner ℝ x y : ℝ) : EReal) < supportFn (pairing n) C y :=
  mem_relint_iff_lt_supportFn (B := pairing n) hC x

/-- **Theorem 13.1**, third clause. `x ∈ int C` if and only if `⟨x, x*⟩ < δ*(x* | C)`
for every `x* ≠ 0`.

**The book omits `C ≠ ∅`**, and the clause is false without it — over the zero space the condition
is vacuous while `int ∅ = ∅`. -/
theorem theorem_13_1_int {C : Set (Rn n)} (hC : Convex ℝ C) (hne : C.Nonempty) (x : Rn n) :
    x ∈ interior C ↔
      ∀ y : Rn n, y ≠ 0 → ((inner ℝ x y : ℝ) : EReal) < supportFn (pairing n) C y := by
  exact mem_interior_iff_lt_supportFn (B := pairing n) hC hne (separatingRight_pairing n) x

/-- **Theorem 13.1**, fourth clause. Assuming `C ≠ ∅`, `x ∈ aff C` if and only if
`⟨x, x*⟩ = δ*(x* | C)` for every `x*` with `-δ*(-x* | C) = δ*(x* | C)`.

It needs no convexity: the reversible directions describe the hyperplanes containing `C`, and
Corollary 1.4.1 intersects them. -/
theorem theorem_13_1_aff {C : Set (Rn n)} (hne : C.Nonempty) (x : Rn n) :
    x ∈ affineSpan ℝ C ↔ ∀ y : Rn n, -supportFn (pairing n) C (-y) = supportFn (pairing n) C y →
      ((inner ℝ x y : ℝ) : EReal) = supportFn (pairing n) C y :=
  mem_affineSpan_iff_eq_supportFn (B := pairing n) hne x

/-- **Corollary 13.1.1.** For convex sets `C₁` and `C₂` in `ℝⁿ`, one has
`cl C₁ ⊆ cl C₂` if and only if `δ*(· | C₁) ≤ δ*(· | C₂)`. -/
theorem corollary_13_1_1 {C₁ C₂ : Set (Rn n)} (h₁ : Convex ℝ C₁) (h₂ : Convex ℝ C₂) :
    closure C₁ ⊆ closure C₂ ↔ supportFn (pairing n) C₁ ≤ supportFn (pairing n) C₂ := by
  have h := closure_convexHull_subset_iff_supportFn_le (B := pairing n) C₁ C₂
  rw [h₁.convexHull_eq, h₂.convexHull_eq] at h
  exact h

/-! ### Theorem 13.2 -/

/-- **Theorem 13.2**, first assertion, one direction: the support function of a set is
the conjugate of its indicator function. -/
theorem theorem_13_2_conj_indicator (C : Set (Rn n)) :
    conj (pairing n) (indicatorFn C) = supportFn (pairing n) C :=
  (supportFn_eq_conj_indicatorFn (pairing n) C).symm

/-- **Theorem 13.2**, first assertion: the indicator function and the support function
of a closed convex set are conjugate to each other. -/
theorem theorem_13_2_conj {C : Set (Rn n)} (hC : Convex ℝ C) (hCcl : IsClosed C) :
    conj (pairing n) (supportFn (pairing n) C) = indicatorFn C := by
  have h := conj_supportFn (B := pairing n) hC hCcl
  rwa [flip_pairing] at h

/-- **Theorem 13.2**, second assertion: the functions which are the support functions
of non-empty convex sets are exactly the closed proper convex functions which are positively
homogeneous.

Since `δ*` sees neither the closure nor the convex hull, the class of sets may be narrowed to the
non-empty *closed convex* ones, and that is what makes the correspondence one-to-one. -/
theorem theorem_13_2 (g : Rn n → EReal) :
    (∃ C : Set (Rn n), C.Nonempty ∧ Convex ℝ C ∧ IsClosed C ∧ g = supportFn (pairing n) C) ↔
      ClosedProperConvexFn g ∧ PosHomogeneous g :=
  exists_supportFn_iff

/-- **Theorem 13.2** as the "important one-to-one correspondence between the closed
convex sets in `ℝⁿ` and objects of quite a different sort, certain functions on `ℝⁿ`". -/
noncomputable def theorem_13_2_correspondence (n : ℕ) :
    {C : Set (Rn n) // C.Nonempty ∧ Convex ℝ C ∧ IsClosed C} ≃
      {g : Rn n → EReal // ClosedProperConvexFn g ∧ PosHomogeneous g} :=
  supportEquiv (pairing n)

/-- **Rockafellar, §13, p. 115**, the consequence drawn immediately after Theorem 13.2:
`δ*(· | C)` is subadditive. -/
theorem theorem_13_2_subadditive {C : Set (Rn n)} (hne : C.Nonempty) (y₁ y₂ : Rn n) :
    supportFn (pairing n) C (y₁ + y₂) ≤
      supportFn (pairing n) C y₁ + supportFn (pairing n) C y₂ :=
  supportFn_add_le hne y₁ y₂

/-- **Corollary 13.2.1.** Let `f` be a positively homogeneous convex function which is
not identically `+∞`. Then `cl f` is the support function of the closed convex set
`C = {x* | ∀ x, ⟨x, x*⟩ ≤ f x}`.

The improper case is included: if `f` takes `-∞` then `cl f ≡ -∞`, `C` is empty, and both sides are
`δ*(· | ∅)`. -/
theorem corollary_13_2_1 {f : Rn n → EReal} (hf : PosHomogeneous f) (hconv : ConvexFn f)
    (hne : ∃ x, f x ≠ ⊤) :
    clFn f =
      supportFn (pairing n) {y : Rn n | ∀ x : Rn n, ((inner ℝ x y : ℝ) : EReal) ≤ f x} := by
  have h := clFn_eq_supportFn_of_posHomogeneous (B := pairing n) hf hconv hne
  rwa [flip_pairing] at h

/-- **Corollary 13.2.2.** The support functions of the non-empty bounded convex sets
are the finite positively homogeneous convex functions.

Closedness is not part of the statement, being free in `ℝⁿ` by Corollary 7.4.2; in general it is
not redundant, a discontinuous linear functional being finite, convex and positively homogeneous
without being a support function. -/
theorem corollary_13_2_2 (g : Rn n → EReal) :
    (∃ C : Set (Rn n), C.Nonempty ∧ Bornology.IsBounded C ∧ g = supportFn (pairing n) C) ↔
      ((∀ y, g y ≠ ⊥) ∧ (∀ y, g y ≠ ⊤) ∧ ConvexFn g ∧ ClosedFn g ∧ PosHomogeneous g) := by
  rw [← exists_supportFn_finite_iff (B := pairing n) (g := g)]
  exact exists_congr fun C => and_congr_right fun _ =>
    and_congr_left fun _ => isBounded_iff_forall_bddAbove

/-! ### Theorem 13.3 -/

/-- **Theorem 13.3**, first assertion. Let `f` be a proper convex function. The support function of
`dom f` is the recession function `f*0⁺` of `f*`. The extra properness hypothesis the backbone
carries is discharged here by `proper_conj_of_proper`. -/
theorem theorem_13_3 {f : Rn n → EReal} (hf : ConvexFn f) (hp : Proper f) :
    supportFn (pairing n) (dom f) = recessionFn (conj (pairing n) f) :=
  (recessionFn_conj hp (proper_conj_of_proper hf hp)).symm

/-- **Theorem 13.3**, second assertion. If `f` is closed, the support function of
`dom f*` is the recession function `f0⁺` of `f`. -/
theorem theorem_13_3_dual {f : Rn n → EReal} (hf : ClosedProperConvexFn f) :
    supportFn (pairing n) (dom (conj (pairing n) f)) = recessionFn f := by
  have h := recessionFn_eq_supportFn_dom_conj (B := pairing n) hf
  rw [flip_pairing] at h
  exact h.symm

/-- **Corollary 13.3.1.** Let `f` be a closed convex function on `ℝⁿ`. In order that
`f*` be finite everywhere, so that `dom f* = ℝⁿ`, it is necessary and sufficient that `f` be
co-finite. -/
theorem corollary_13_3_1 {f : Rn n → EReal} (hf : ClosedProperConvexFn f) :
    dom (conj (pairing n) f) = univ ↔ Cofinite f :=
  (cofinite_iff_dom_conj_eq_univ hf).symm

/-! ### Corollary 13.3.2

The book leaves its key step as an exercise: a convex set is affine iff every linear function
bounded above on it is constant on it. That is `affine_iff_forall_reversible` below. -/

/-- **The step Rockafellar leaves as an exercise**: a non-empty convex set `C` is
affine if and only if every linear function bounded above on `C` is constant on it — that is, if
and only if `-δ*(-x* | C) = δ*(x* | C)` whenever `δ*(x* | C) < +∞`. -/
theorem affine_iff_forall_reversible {C : Set (Rn n)} (hC : Convex ℝ C) (hne : C.Nonempty) :
    (affineSpan ℝ C : Set (Rn n)) = C ↔
      ∀ y : Rn n, supportFn (pairing n) C y ≠ ⊤ →
        -supportFn (pairing n) C (-y) = supportFn (pairing n) C y := by
  constructor
  · intro haff y hy
    refine (neg_supportFn_neg_eq_iff (B := pairing n) hne y).2 ?_
    obtain ⟨x₀, hx₀⟩ := hne
    have hmemdom : y ∈ dom (supportFn (pairing n) C) := mem_dom.2 (lt_top_iff_ne_top.2 hy)
    rw [dom_supportFn] at hmemdom
    obtain ⟨c, hc⟩ := hmemdom
    refine ⟨inner ℝ x₀ y, fun x hx => ?_⟩
    by_contra hne'
    set d : ℝ := (inner ℝ x y : ℝ) - (inner ℝ x₀ y : ℝ) with hd
    have hd0 : d ≠ 0 := sub_ne_zero.2 hne'
    have hmem : ∀ t : ℝ, t • (x - x₀) + x₀ ∈ C := by
      intro t
      have hstep := (affineSpan ℝ C).smul_vsub_vadd_mem t (subset_affineSpan ℝ C hx)
        (subset_affineSpan ℝ C hx₀) (subset_affineSpan ℝ C hx₀)
      rw [← haff]
      exact hstep
    set t : ℝ := (|c - (inner ℝ x₀ y : ℝ)| + 1) / d with ht
    have hval : (inner ℝ (t • (x - x₀) + x₀) y : ℝ) = t * d + (inner ℝ x₀ y : ℝ) := by
      rw [inner_add_left, real_inner_smul_left, inner_sub_left, hd]
    have hle := hc _ (hmem t)
    rw [show (pairing n) (t • (x - x₀) + x₀) y = (inner ℝ (t • (x - x₀) + x₀) y : ℝ) from rfl,
      hval, ht, div_mul_cancel₀ _ hd0] at hle
    have hab : c - (inner ℝ x₀ y : ℝ) ≤ |c - (inner ℝ x₀ y : ℝ)| := le_abs_self _
    linarith
  · intro hrev
    refine subset_antisymm (fun x hx => ?_) (subset_affineSpan ℝ C)
    have hclosure : ∀ z : Rn n, z ∈ affineSpan ℝ C → z ∈ closure C := by
      intro z hz
      rw [theorem_13_1_cl hC]
      intro y
      by_cases hy : supportFn (pairing n) C y = ⊤
      · rw [hy]
        exact le_top
      · exact le_of_eq ((theorem_13_1_aff hne z).1 hz y (hrev y hy))
    obtain ⟨x₀, hx₀⟩ := hC.relint_nonempty hne
    have hxa : x₀ ∈ affineSpan ℝ C := subset_affineSpan ℝ C (intrinsicInterior_subset hx₀)
    have hz : (2 : ℝ) • (x - x₀) + x₀ ∈ affineSpan ℝ C :=
      (affineSpan ℝ C).smul_vsub_vadd_mem 2 hx hxa hxa
    have hmid : (1 - (2 : ℝ)⁻¹) • x₀ + (2 : ℝ)⁻¹ • ((2 : ℝ) • (x - x₀) + x₀) = x := by
      module
    have hseg := hC.segment_mem_relint hx₀ (hclosure _ hz) (by norm_num : (0 : ℝ) ≤ 2⁻¹)
      (by norm_num : (2 : ℝ)⁻¹ < 1)
    rw [hmid] at hseg
    exact intrinsicInterior_subset hseg

/-- **Corollary 13.3.2.** Let `f` be a closed proper convex function. In order that `dom f*` be an
affine set, it is necessary and sufficient that `(f0⁺)(y) = +∞` for every `y` which is not actually
in the lineality space of `f`. The step the book leaves as an exercise is
`affine_iff_forall_reversible` above. -/
theorem corollary_13_3_2 {f : Rn n → EReal} (hf : ClosedProperConvexFn f) :
    (affineSpan ℝ (dom (conj (pairing n) f)) : Set (Rn n)) = dom (conj (pairing n) f) ↔
      ∀ y : Rn n, y ∉ linealitySpaceFn f → recessionFn f y = ⊤ := by
  have hconv : Convex ℝ (dom (conj (pairing n) f)) := (convexFn_conj (pairing n) f).convex_dom
  have hne : (dom (conj (pairing n) f)).Nonempty := (proper_conj hf).dom_nonempty
  rw [affine_iff_forall_reversible hconv hne, theorem_13_3_dual hf]
  constructor
  · intro h y hy
    by_contra hy'
    exact hy (mem_linealitySpaceFn.2 (neg_eq_iff_eq_neg.1 (h y hy')))
  · intro h y hy
    refine neg_eq_iff_eq_neg.2 (mem_linealitySpaceFn.1 ?_)
    by_contra hmem
    exact hy (h y hmem)

/-! ### Corollary 13.3.3 -/

/-- **Corollary 13.3.3**, the quantitative half: for `α ≥ 0`, the Lipschitz condition
`f(z) ≤ f(x) + α|z - x|` holds for all `x` and `z` exactly when `dom f*` is contained in the ball
of radius `α`. This is what "the smallest such `α` is `sup {|x*| : x* ∈ dom f*}`" means. -/
theorem corollary_13_3_3_least {f : Rn n → EReal} (hf : ClosedProperConvexFn f) {α : ℝ}
    (hα : 0 ≤ α) :
    (∀ x z : Rn n, f z ≤ f x + ((α * ‖z - x‖ : ℝ) : EReal)) ↔
      dom (conj (pairing n) f) ⊆ Metric.closedBall (0 : Rn n) α := by
  have hball : supportFn (pairing n) (Metric.closedBall (0 : Rn n) α) =
      fun y => ((α * ‖y‖ : ℝ) : EReal) := funext fun y => supportFn_closedBall hα y
  constructor
  · intro hlip
    have hle : recessionFn f ≤ fun y => ((α * ‖y‖ : ℝ) : EReal) :=
      (recessionFn_isLeast hf.convex hf.proper).2 fun x z => hlip x z
    have hsub : closure (dom (conj (pairing n) f)) ⊆
        closure (Metric.closedBall (0 : Rn n) α) := by
      refine (corollary_13_1_1 (convexFn_conj (pairing n) f).convex_dom
        (convex_closedBall 0 α)).2 ?_
      rw [theorem_13_3_dual hf, hball]
      exact hle
    intro y hy
    have hmem := hsub (subset_closure hy)
    rwa [Metric.isClosed_closedBall.closure_eq] at hmem
  · intro hsub x z
    have hle : recessionFn f ≤ fun y => ((α * ‖y‖ : ℝ) : EReal) := by
      rw [← hball, ← theorem_13_3_dual hf]
      exact (corollary_13_1_1 (convexFn_conj (pairing n) f).convex_dom
        (convex_closedBall 0 α)).1 (closure_mono hsub)
    exact ((recessionFn_isLeast hf.convex hf.proper).1 x z).trans
      (add_le_add le_rfl (hle (z - x)))

/-- **Corollary 13.3.3**, first assertion: `dom f*` is bounded if and only if `f`
satisfies a global Lipschitz condition. -/
theorem corollary_13_3_3 {f : Rn n → EReal} (hf : ClosedProperConvexFn f) :
    Bornology.IsBounded (dom (conj (pairing n) f)) ↔
      ∃ α : ℝ, 0 ≤ α ∧ ∀ x z : Rn n, f z ≤ f x + ((α * ‖z - x‖ : ℝ) : EReal) := by
  constructor
  · intro hb
    obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Rn n)).1 hb
    obtain ⟨y₀, hy₀⟩ := (proper_conj (B := pairing n) hf).dom_nonempty
    have hr0 : 0 ≤ r := by
      have hmem := hr hy₀
      rw [Metric.mem_closedBall, dist_zero_right] at hmem
      exact le_trans (norm_nonneg _) hmem
    exact ⟨r, hr0, (corollary_13_3_3_least hf hr0).2 hr⟩
  · rintro ⟨α, hα, hlip⟩
    exact (Metric.isBounded_iff_subset_closedBall (0 : Rn n)).2
      ⟨α, (corollary_13_3_3_least hf hα).1 hlip⟩

/-- **Corollary 13.3.3**, the "`f` is finite everywhere" clause: the Lipschitz
condition forces a proper `f` to be real-valued. -/
theorem corollary_13_3_3_finite {f : Rn n → EReal} (hf : ClosedProperConvexFn f) {α : ℝ}
    (hlip : ∀ x z : Rn n, f z ≤ f x + ((α * ‖z - x‖ : ℝ) : EReal)) (z : Rn n) :
    f z ≠ ⊤ ∧ f z ≠ ⊥ := by
  obtain ⟨x₀, hx₀⟩ := hf.proper.dom_nonempty
  refine ⟨?_, hf.proper.ne_bot z⟩
  obtain ⟨c, hc⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hf.proper.ne_bot x₀) hx₀
  have hstep := hlip x₀ z
  rw [hc, ← EReal.coe_add] at hstep
  exact (lt_of_le_of_lt hstep (EReal.coe_lt_top _)).ne

/-! ### Corollary 13.3.4

The book sets `g (x) = f (x) - ⟨x, x*⟩`, so that `(g0⁺)(y) = (f0⁺)(y) - ⟨y, x*⟩`; the four clauses
below are stated through `f0⁺` and `⟨y, x*⟩` directly, which makes the translation by `-x*`
disappear. Rockafellar's exception set in (b) is `y`-independent for this reason. -/

/-- **Corollary 13.3.4(a).** `x* ∈ cl (dom f*)` if and only if `(g0⁺)(y) ≥ 0` for
every `y`. Specialises `mem_closure_dom_conj_iff`. -/
theorem corollary_13_3_4_a {f : Rn n → EReal} (hf : ClosedProperConvexFn f) (y₀ : Rn n) :
    y₀ ∈ closure (dom (conj (pairing n) f)) ↔
      ∀ y : Rn n, ((inner ℝ y y₀ : ℝ) : EReal) ≤ recessionFn f y :=
  mem_closure_dom_conj_iff hf y₀

/-- **Corollary 13.3.4(b).** `x* ∈ ri (dom f*)` if and only if `(g0⁺)(y) > 0` for all
`y` except those with `-(g0⁺)(-y) = (g0⁺)(y) = 0`. Specialises `mem_relint_dom_conj_iff`. -/
theorem corollary_13_3_4_b {f : Rn n → EReal} (hf : ClosedProperConvexFn f) (y₀ : Rn n) :
    y₀ ∈ ri (dom (conj (pairing n) f)) ↔
      (∀ y : Rn n, ((inner ℝ y y₀ : ℝ) : EReal) ≤ recessionFn f y) ∧
      ∀ y : Rn n, -recessionFn f (-y) ≠ recessionFn f y →
        ((inner ℝ y y₀ : ℝ) : EReal) < recessionFn f y :=
  mem_relint_dom_conj_iff hf y₀

/-- **Corollary 13.3.4(c).** `x* ∈ int (dom f*)` if and only if `(g0⁺)(y) > 0` for
every `y ≠ 0`. Specialises `mem_interior_dom_conj_iff`. -/
theorem corollary_13_3_4_c {f : Rn n → EReal} (hf : ClosedProperConvexFn f) (y₀ : Rn n) :
    y₀ ∈ interior (dom (conj (pairing n) f)) ↔
      ∀ y : Rn n, y ≠ 0 → ((inner ℝ y y₀ : ℝ) : EReal) < recessionFn f y :=
  mem_interior_dom_conj_iff hf y₀

/-- **Corollary 13.3.4(d).** `x* ∈ aff (dom f*)` if and only if `(g0⁺)(y) = 0` for
every `y` with `-(g0⁺)(-y) = (g0⁺)(y)`. Specialises `mem_affineSpan_dom_conj_iff`. -/
theorem corollary_13_3_4_d {f : Rn n → EReal} (hf : ClosedProperConvexFn f) (y₀ : Rn n) :
    y₀ ∈ affineSpan ℝ (dom (conj (pairing n) f)) ↔
      ∀ y : Rn n, -recessionFn f (-y) = recessionFn f y →
        ((inner ℝ y y₀ : ℝ) : EReal) = recessionFn f y :=
  mem_affineSpan_dom_conj_iff hf y₀

/-! ### Theorem 13.4 -/

/-- **Theorem 13.4**, first assertion. Let `f` be a proper convex function on `ℝⁿ`.
The lineality space of `f*` is the orthogonal complement of the subspace parallel to
`aff (dom f)`.

In an inner-product space the annihilator of a subspace is its orthogonal complement, which is the
book's phrasing, and `vectorSpan ℝ (dom f)` is the subspace parallel to `aff (dom f)`. -/
theorem theorem_13_4 {f : Rn n → EReal} (hf : ConvexFn f) (hp : Proper f) :
    linealitySpaceFn (conj (pairing n) f) = ((vectorSpan ℝ (dom f))ᗮ : Set (Rn n)) := by
  rw [linealitySpaceFn_conj_eq_annihilator hp (proper_conj_of_proper hf hp)]
  ext y
  simp only [Set.mem_ofPred_eq, SetLike.mem_coe, Submodule.mem_orthogonal]
  exact forall₂_congr fun v _ => by rw [pairing_apply, real_inner_comm]

/-- **Theorem 13.4**, second assertion. If `f` is closed, the subspace parallel to
`aff (dom f*)` is the orthogonal complement of the lineality space of `f`.

Stated in the equivalent form `lineality f = (vectorSpan (dom f*))ᗮ`; a subspace of `ℝⁿ` is its
own double complement, so this is the book's phrasing. -/
theorem theorem_13_4_dual {f : Rn n → EReal} (hf : ClosedProperConvexFn f) :
    linealitySpaceFn f = ((vectorSpan ℝ (dom (conj (pairing n) f)))ᗮ : Set (Rn n)) := by
  rw [linealitySpaceFn_eq_annihilator_dom_conj (B := pairing n) hf]
  ext x
  simp only [Set.mem_ofPred_eq, SetLike.mem_coe, Submodule.mem_orthogonal]
  exact forall₂_congr fun v _ => by rw [pairing_apply, real_inner_comm]

/-- **Theorem 13.4**, first dimensionality formula:
`lineality f* = n - dimension f`. -/
theorem theorem_13_4_lineality {f : Rn n → EReal} (hf : ConvexFn f) (hp : Proper f) :
    (linealityFn (conj (pairing n) f) : ℤ) = (n : ℤ) - dim (dom f) := by
  have hsub : linealitySubmoduleFn (conj (pairing n) f) = (vectorSpan ℝ (dom f))ᗮ :=
    SetLike.ext' (by
      rw [coe_linealitySubmoduleFn (proper_conj_of_proper hf hp), theorem_13_4 hf hp])
  have hcount := Submodule.finrank_add_finrank_orthogonal (K := vectorSpan ℝ (dom f))
  rw [finrank_euclideanSpace_fin] at hcount
  rw [linealityFn, hsub, dim_of_nonempty hp.dom_nonempty]
  omega

/-- **Theorem 13.4**, second dimensionality formula:
`dimension f* = n - lineality f`. -/
theorem theorem_13_4_dimension {f : Rn n → EReal} (hf : ClosedProperConvexFn f) :
    dim (dom (conj (pairing n) f)) = (n : ℤ) - (linealityFn f : ℤ) := by
  have hsub : linealitySubmoduleFn f = (vectorSpan ℝ (dom (conj (pairing n) f)))ᗮ :=
    SetLike.ext' (by rw [coe_linealitySubmoduleFn hf.proper, theorem_13_4_dual hf])
  have hcount := Submodule.finrank_add_finrank_orthogonal
    (K := vectorSpan ℝ (dom (conj (pairing n) f)))
  rw [finrank_euclideanSpace_fin] at hcount
  rw [linealityFn, hsub, dim_of_nonempty (proper_conj (B := pairing n) hf).dom_nonempty]
  omega

/-- **Corollary 13.4.1.** Closed proper convex functions conjugate to each other have
the same rank.

Immediate from the two dimensionality formulas of Theorem 13.4 and the definition of rank:
`rank f* = (n - lineality f) - (n - dim f) = dim f - lineality f = rank f`. -/
theorem corollary_13_4_1 {f : Rn n → EReal} (hf : ClosedProperConvexFn f) :
    rankFn (conj (pairing n) f) = rankFn f := by
  rw [rankFn, rankFn, theorem_13_4_dimension hf, theorem_13_4_lineality hf.convex hf.proper]
  omega

/-- **Corollary 13.4.2.** Let `f` be a closed proper convex function. Then `dom f*` has
a non-empty interior if and only if there are no lines along which `f` is (finite and) affine. -/
theorem corollary_13_4_2 {f : Rn n → EReal} (hf : ClosedProperConvexFn f) :
    (interior (dom (conj (pairing n) f))).Nonempty ↔ linealitySpaceFn f = {0} :=
  interior_dom_conj_nonempty_iff hf

/-! ### Theorem 13.5 -/

/-- **Theorem 13.5**, first assertion. Let `f` be a closed proper convex function. The
support function of `{x | f x ≤ 0}` is `cl g`, where `g` is the positively homogeneous convex
function generated by `f*`.

Properness is not needed: Fenchel–Moreau in the form `biconj_eq_self` already covers the improper
cases. -/
theorem theorem_13_5 {f : Rn n → EReal} (hf : ConvexFn f) (hc : ClosedFn f) :
    supportFn (pairing n) {x : Rn n | f x ≤ 0} = clFn (posHomGen (conj (pairing n) f)) :=
  supportFn_setOf_le_zero hf hc

/-- **Theorem 13.5**, second assertion. The closure of the positively homogeneous convex function
`k` generated by `f` is the support function of `{x* | f*(x*) ≤ 0}`. It needs no hypothesis at
all. -/
theorem theorem_13_5_dual (f : Rn n → EReal) :
    clFn (posHomGen f) = supportFn (pairing n) {y : Rn n | conj (pairing n) f y ≤ 0} := by
  have h := clFn_posHomGen (B := pairing n) f
  rwa [flip_pairing] at h

/-- **Corollary 13.5.1.** Let `f` be a closed proper convex function on `ℝⁿ`. The
function `k` on `ℝⁿ⁺¹` given by `k (λ, x) = (fλ)(x)` for `λ > 0`, `(f0⁺)(x)` for `λ = 0` and `+∞`
for `λ < 0` is the support function of `C = {(λ*, x*) | λ* ≤ -f*(x*)}`.

Identifying the book's three-case `k` with `cl (hom f)` is Corollary 8.5.2, a §8 statement, and is
not repeated here. -/
theorem corollary_13_5_1 {f : Rn n → EReal} (hf : ConvexFn f) (hdom : (dom f).Nonempty) :
    clFn (hom f) = supportFn (prodPairing (innerₗ ℝ) (pairing n)).flip
      {q : ℝ × Rn n | conj (pairing n) f q.2 ≤ ((-q.1 : ℝ) : EReal)} :=
  clFn_hom hf hdom

end Rockafellar
