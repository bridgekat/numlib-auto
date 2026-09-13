import Numlib.Analysis.Convex.Subgradient.BoundaryDirDeriv
import Numlib.Analysis.Convex.Subgradient.Cofinite
import Numlib.Analysis.Convex.Subgradient.Preservation
import NumlibSurface.Common.Euclidean

/-!
# Rockafellar, §26: The Legendre Transformation

The classical Legendre transformation, and the exact sense in which it is the conjugacy
correspondence restricted to the functions whose subdifferential is a genuine one-to-one mapping.

All eleven numbered results of §26 are formalized over `Rn n = ℝⁿ`: Theorems 26.1, 26.3, 26.4,
26.5, 26.6, Lemmas 26.2 and 26.7, and Corollaries 26.3.1, 26.3.2, 26.3.3, 26.4.1, together with all
three of the section's counterexamples, transcribed as Lean definitions.

`SingleValued`, `inverseMap` and `OneToOne` are the book's vocabulary for multivalued mappings
(p. 251), and `legendreDomain f` is Rockafellar's `D`, the image of `C = int (dom f)` under the
gradient mapping. `LegendreType` is the backbone's, and says exactly what the book's "the pair
`(C, f)` is a convex function of Legendre type" says for `C = int (dom f)`. Essential smoothness is
carried in two equivalent forms — `EssentiallySmoothBook`, with the book's condition (c), and
`EssentiallySmoothDir`, with its directional form (c′), the equivalence being Lemma 26.2 — because
a limit-of-gradients argument produces (c) while a user with a concrete `f` can check (c′). The
backbone's `EssentiallySmooth` quantifies (c) over points *outside* `C` rather than over boundary
points of `C`; the two agree, and `essentiallySmooth_iff_book` proves it.

Three of the book's hypotheses are stronger than its own proofs need. **Theorem 26.5 says "closed
convex function" where its proof needs "closed *proper* convex"**, so `theorem_26_5` carries
`Proper f`; nothing is lost, since an improper closed convex function is `+∞` everywhere or `−∞` on
`cl (dom f)` and so is differentiable on no non-empty interior. **Theorem 26.4's single-valuedness
and its formula `g = f*` follow from convexity alone**, so `theorem_26_4_wellDefined` and
`theorem_26_4_eq` carry only `ConvexFn f`. **Corollary 26.3.3's "`A` maps `ℝⁿ` onto `ℝᵐ`" is used
only through injectivity of `A*`** — the book's own proof says so parenthetically.

There is deliberately **no involution lemma** for the Legendre transformation. The book is explicit
(p. 258) that the Legendre conjugate of the Legendre conjugate need not be the original function;
Theorem 26.5 says exactly when it is, and `not_convex_legendreDomain_halfPlaneFn` is why its
hypothesis cannot be dropped.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §26.
-/

open Filter Set Topology

namespace Rockafellar

open ConvexAnalysis NumlibSurface

variable {n : ℕ} {f : Rn n → EReal}

/-! ### Multivalued mappings -/

/-- **§26 (p. 251).** A multivalued mapping `ρ` is **single-valued** when `ρ x` has at most one
element for each `x`. Its effective domain need not be all of `ℝⁿ`. -/
def SingleValued (ρ : Rn n → Set (Rn n)) : Prop := ∀ x, (ρ x).Subsingleton

/-- **Rockafellar, §26 (p. 251).** The **inverse** of a multivalued mapping,
`ρ⁻¹ x* = {x | x* ∈ ρ x}`. -/
def inverseMap (ρ : Rn n → Set (Rn n)) : Rn n → Set (Rn n) := fun y => {x | y ∈ ρ x}

@[simp] theorem mem_inverseMap {ρ : Rn n → Set (Rn n)} {x y : Rn n} :
    x ∈ inverseMap ρ y ↔ y ∈ ρ x := Iff.rfl

/-- **Rockafellar, §26 (p. 251).** A multivalued mapping is **one-to-one** when both it and its
inverse are single-valued — equivalently, when `graph ρ` contains neither two different pairs with
the same first component nor two with the same second component. -/
def OneToOne (ρ : Rn n → Set (Rn n)) : Prop := SingleValued ρ ∧ SingleValued (inverseMap ρ)

/-- Single-valuedness of `ρ⁻¹` is the statement that `ρ` takes distinct points to disjoint sets,
which is the form the backbone's injectivity theorems are stated in. -/
theorem singleValued_inverseMap_iff {ρ : Rn n → Set (Rn n)} :
    SingleValued (inverseMap ρ) ↔ ∀ x₁ x₂ : Rn n, x₁ ≠ x₂ → Disjoint (ρ x₁) (ρ x₂) := by
  constructor
  · intro h x₁ x₂ hne
    rw [Set.disjoint_left]
    intro y hy₁ hy₂
    exact hne (h y hy₁ hy₂)
  · intro h y x₁ hx₁ x₂ hx₂
    by_contra hne
    exact Set.disjoint_left.1 (h x₁ x₂ hne) hx₁ hx₂

/-- The bridge between the book's "one-to-one" and the backbone's injectivity. -/
theorem oneToOne_iff {ρ : Rn n → Set (Rn n)} :
    OneToOne ρ ↔ (∀ x, (ρ x).Subsingleton) ∧ ∀ x₁ x₂ : Rn n, x₁ ≠ x₂ → Disjoint (ρ x₁) (ρ x₂) :=
  and_congr_right' singleValued_inverseMap_iff

/-! ### Essential smoothness

A proper convex function `f` is **essentially smooth** (p. 251) when, for `C = int (dom f)`:

* (a) `C` is not empty;
* (b) `f` is differentiable throughout `C`;
* (c) `|∇f xᵢ| → +∞` whenever `x₁, x₂, …` is a sequence in `C` converging to a boundary point of
  `C`. -/

/-- **Rockafellar, §26 (p. 251)**, verbatim: conditions (a), (b) and (c) with (c) quantified over
*boundary points* of `C = int (dom f)`, as the book quantifies it. -/
def EssentiallySmoothBook (f : Rn n → EReal) : Prop :=
  (interior (dom f)).Nonempty ∧
    (∀ ⦃z : Rn n⦄, z ∈ interior (dom f) → DifferentiableAtFn f z) ∧
    ∀ ⦃z : Rn n⦄, z ∈ frontier (interior (dom f)) → ∀ zs : ℕ → Rn n,
      (∀ i, zs i ∈ interior (dom f)) → Tendsto zs atTop (𝓝 z) →
        Tendsto (fun i => ‖fderiv ℝ (fun w => (f w).toReal) (zs i)‖) atTop atTop

/-- **The book's condition (c) and the backbone's are the same condition.** `C = int (dom f)` is
open, so its frontier is `cl C \ C`: a boundary point of `C` is not in `C`, and conversely a point
outside `C` that a sequence in `C` converges to lies on the boundary. -/
theorem essentiallySmooth_iff_book : EssentiallySmooth f ↔ EssentiallySmoothBook f := by
  have hfr : frontier (interior (dom f)) = closure (interior (dom f)) \ interior (dom f) :=
    isOpen_interior.frontier_eq
  constructor
  · rintro ⟨hne, hdiff, hc⟩
    refine ⟨hne, hdiff, fun z hz => ?_⟩
    rw [hfr] at hz
    exact hc hz.2
  · rintro ⟨hne, hdiff, hc⟩
    refine ⟨hne, hdiff, fun z hz zs hzs hlim => ?_⟩
    refine hc ?_ zs hzs hlim
    rw [hfr]
    exact ⟨mem_closure_of_tendsto hlim (Eventually.of_forall hzs), hz⟩

/-! ### Theorem 26.1 -/

/-- **Rockafellar, Theorem 26.1.** Let `f` be a closed proper convex function. Then `∂f` is a
single-valued mapping if and only if `f` is essentially smooth. -/
theorem theorem_26_1 (hf : ConvexFn f) (hp : Proper f) (hcl : ClosedFn f) :
    SingleValued (subgradient (pairing n) f) ↔ EssentiallySmooth f :=
  subsingleton_subgradient_iff_essentiallySmooth hf hp hcl

/-- **Rockafellar, Theorem 26.1**, the "in this case" clause, first half: `∂f x` consists of the
vector `∇f x` alone when `x ∈ int (dom f)`. -/
theorem theorem_26_1_gradient (hf : ConvexFn f) (hes : EssentiallySmooth f) {x : Rn n}
    (hx : x ∈ interior (dom f)) :
    subgradient (pairing n) f x = {gradient (fun w => (f w).toReal) x} := by
  have h := subgradient_eq_singleton_of_essentiallySmooth hf hes hx
  rwa [show (InnerProductSpace.toDual ℝ (Rn n)).symm (fderiv ℝ (fun w => (f w).toReal) x)
      = gradient (fun w => (f w).toReal) x from rfl] at h

/-- **Rockafellar, Theorem 26.1**, the "in this case" clause, second half: `∂f x = ∅` when
`x ∉ int (dom f)`. This is the substantive half — it is what makes `∂f` an ordinary function on
`int (dom f)` and nothing anywhere else. -/
theorem theorem_26_1_empty (hf : ConvexFn f) (hp : Proper f) (hcl : ClosedFn f)
    (hes : EssentiallySmooth f) {x : Rn n} (hx : x ∉ interior (dom f)) :
    subgradient (pairing n) f x = ∅ :=
  subgradient_eq_empty_of_essentiallySmooth hf hp hcl hes hx

/-- **Rockafellar, Theorem 26.1**, both halves of the "in this case" clause as one equation:
`dom ∂f = int (dom f)` for an essentially smooth closed proper convex function. -/
theorem theorem_26_1_domSubgradient (hf : ConvexFn f) (hp : Proper f) (hcl : ClosedFn f)
    (hes : EssentiallySmooth f) :
    domSubgradient (pairing n) f = interior (dom f) :=
  domSubgradient_eq_interior_dom_of_essentiallySmooth hf hp hcl hes

/-! ### Lemma 26.2 -/

/-- **Rockafellar, Lemma 26.2**, conditions (a), (b), (c′): the definition of essential smoothness
with condition (c) replaced by

```
(c')  f'(x + λ(a − x); a − x) ↓ −∞ as λ ↓ 0, for any a ∈ C and any boundary point x of C.
```

The `↓` of the book records that the map is nondecreasing in `λ`, which holds for every convex `f`;
the *content* of (c′) is the value of the limit, so only the limit appears here. -/
def EssentiallySmoothDir (f : Rn n → EReal) : Prop :=
  (interior (dom f)).Nonempty ∧
    (∀ ⦃z : Rn n⦄, z ∈ interior (dom f) → DifferentiableAtFn f z) ∧
    ∀ x ∉ interior (dom f), ∀ a ∈ interior (dom f),
      Tendsto (fun t : ℝ => dirDeriv f (x + t • (a - x)) (a - x)) (𝓝[>] 0) (𝓝 ⊥)

/-- **Rockafellar, Lemma 26.2**, at a single point: assuming (a) and (b), condition (c) at `x` and
condition (c′) at `x` along the segment from any `a ∈ C` say the same thing — namely that `f` has
no subgradient at `x`. -/
theorem lemma_26_2_at (hf : ConvexFn f) (hp : Proper f) (hcl : ClosedFn f)
    (hne : (interior (dom f)).Nonempty)
    (hdiff : ∀ ⦃z : Rn n⦄, z ∈ interior (dom f) → DifferentiableAtFn f z)
    {a : Rn n} (ha : a ∈ interior (dom f)) (x : Rn n) :
    (∀ zs : ℕ → Rn n, (∀ i, zs i ∈ interior (dom f)) → Tendsto zs atTop (𝓝 x) →
        Tendsto (fun i => ‖fderiv ℝ (fun w => (f w).toReal) (zs i)‖) atTop atTop)
      ↔ Tendsto (fun t : ℝ => dirDeriv f (x + t • (a - x)) (a - x)) (𝓝[>] 0) (𝓝 ⊥) :=
  tendsto_norm_fderiv_iff_tendsto_dirDeriv hf hp hcl hne hdiff ha x

/-- **Rockafellar, Lemma 26.2.** For a closed proper convex function, condition (c) may be replaced
by condition (c′): the two definitions of essential smoothness agree. -/
theorem lemma_26_2 (hf : ConvexFn f) (hp : Proper f) (hcl : ClosedFn f) :
    EssentiallySmooth f ↔ EssentiallySmoothDir f := by
  constructor
  · intro hes
    refine ⟨hes.interior_dom_nonempty, hes.differentiableAtFn, ?_⟩
    exact (essentiallySmooth_iff_tendsto_dirDeriv hf hp hcl hes.interior_dom_nonempty
      hes.differentiableAtFn).1 hes
  · rintro ⟨hne, hdiff, hc⟩
    exact (essentiallySmooth_iff_tendsto_dirDeriv hf hp hcl hne hdiff).2 hc

/-! ### Essential strict convexity

A real-valued function is **strictly convex on `C`** (p. 253) when the convexity inequality between
two different points of `C` is strict, and a proper convex function on `ℝⁿ` is **essentially
strictly convex** when it is strictly convex on every convex subset of `dom ∂f`. Both are the
backbone's `StrictConvexOnFn` and `EssentiallyStrictlyConvex`, whose definitions are literally the
book's. Rockafellar's two warnings about the definition are the counterexamples below. -/

/-! ### Coordinates on `ℝ²`

The section's three counterexamples all live on `ℝ²`; these are the coordinate facts they need. -/

private theorem sub_apply_two (u v : Rn 2) (i : Fin 2) : (u - v) i = u i - v i := rfl

/-- Two vectors of `ℝ²` agreeing in both coordinates are equal. -/
private theorem ext_two {u v : Rn 2} (h0 : u 0 = v 0) (h1 : u 1 = v 1) : u = v := by
  ext i
  fin_cases i
  · exact h0
  · exact h1

/-- **A function vanishing along the non-negative `ξ₁`-axis is not strictly convex on any set
containing two points of that axis.** Both counterexamples below are of this shape: `(3/2, 0)` is
the midpoint of `(1, 0)` and `(2, 0)`, and all three values are `0`. -/
private theorem not_strictConvexOnFn_of_axis {g : Rn 2 → EReal} {C : Set (Rn 2)}
    (h1 : (WithLp.toLp 2 ![(1 : ℝ), 0] : Rn 2) ∈ C)
    (h2 : (WithLp.toLp 2 ![(2 : ℝ), 0] : Rn 2) ∈ C)
    (hg : ∀ t : ℝ, 0 ≤ t → g (WithLp.toLp 2 ![t, 0]) = 0) : ¬ StrictConvexOnFn g C := by
  intro h
  have hne : (WithLp.toLp 2 ![(1 : ℝ), 0] : Rn 2) ≠ WithLp.toLp 2 ![(2 : ℝ), 0] := by
    intro hc
    have hco : (WithLp.toLp 2 ![(1 : ℝ), 0] : Rn 2) 0 = (WithLp.toLp 2 ![(2 : ℝ), 0] : Rn 2) 0 :=
      congrArg (fun w : Rn 2 => w 0) hc
    have hnum : (1 : ℝ) = 2 := hco
    norm_num at hnum
  have hlt := h h1 h2 hne (by norm_num : (0:ℝ) < 1/2) (by norm_num : (0:ℝ) < 1/2) (by norm_num)
  have hmid : ((1/2 : ℝ) • (WithLp.toLp 2 ![(1 : ℝ), 0] : Rn 2)
      + (1/2 : ℝ) • (WithLp.toLp 2 ![(2 : ℝ), 0] : Rn 2)) = WithLp.toLp 2 ![(3/2 : ℝ), 0] :=
    ext_two (by change (1/2 : ℝ) * 1 + (1/2 : ℝ) * 2 = 3/2; norm_num)
      (by change (1/2 : ℝ) * 0 + (1/2 : ℝ) * 0 = 0; norm_num)
  rw [hmid, hg 1 zero_le_one, hg 2 (by norm_num), hg (3/2) (by norm_num)] at hlt
  simp at hlt

/-! ### The counterexample of p. 253

Rockafellar's first warning: a closed proper convex function which is essentially strictly convex
need **not** be strictly convex on the whole of `dom f`. -/

/-- **§26 (p. 253)**, the first counterexample:

```
f(ξ₁, ξ₂) = ξ₂²/2ξ₁ − 2ξ₂^(1/2)   if ξ₁ > 0, ξ₂ ≥ 0
          = 0                      if ξ₁ = 0 = ξ₂
          = +∞                     otherwise.
```

The two branches are one formula: at the origin the real expression reads `0/0 − 2√0`, which is `0`
in Lean, matching the book's second clause. Rockafellar's claim is that this `f` is essentially
strictly convex — indeed essentially smooth — while **not** being strictly convex on `dom f`,
because it vanishes along the whole non-negative `ξ₁`-axis. Only the second half is formalized, as
`essStrictlyConvexFn_not_strictConvexOn_dom`. -/
noncomputable def essStrictlyConvexFn (x : Rn 2) : EReal :=
  ⨅ _ : (0 < x 0 ∧ 0 ≤ x 1) ∨ (x 0 = 0 ∧ x 1 = 0),
    ((x 1 ^ 2 / (2 * x 0) - 2 * Real.sqrt (x 1) : ℝ) : EReal)

/-- The value of the p. 253 example on its effective domain. -/
theorem essStrictlyConvexFn_of_mem {x : Rn 2}
    (h : (0 < x 0 ∧ 0 ≤ x 1) ∨ (x 0 = 0 ∧ x 1 = 0)) :
    essStrictlyConvexFn x = ((x 1 ^ 2 / (2 * x 0) - 2 * Real.sqrt (x 1) : ℝ) : EReal) :=
  iInf_pos h

/-- **The p. 253 example vanishes along the whole non-negative `ξ₁`-axis**, which is the book's
observation. -/
theorem essStrictlyConvexFn_axis {t : ℝ} (ht : 0 ≤ t) :
    essStrictlyConvexFn (WithLp.toLp 2 ![t, 0]) = 0 := by
  have e0 : (WithLp.toLp 2 ![t, 0] : Rn 2) 0 = t := rfl
  have e1 : (WithLp.toLp 2 ![t, 0] : Rn 2) 1 = 0 := rfl
  have hc : (0 < (WithLp.toLp 2 ![t, 0] : Rn 2) 0 ∧ 0 ≤ (WithLp.toLp 2 ![t, 0] : Rn 2) 1)
      ∨ ((WithLp.toLp 2 ![t, 0] : Rn 2) 0 = 0 ∧ (WithLp.toLp 2 ![t, 0] : Rn 2) 1 = 0) := by
    rw [e0, e1]
    rcases eq_or_lt_of_le ht with he | hlt
    · exact Or.inr ⟨he.symm, rfl⟩
    · exact Or.inl ⟨hlt, le_rfl⟩
  rw [essStrictlyConvexFn_of_mem hc, e0, e1]
  norm_num

/-- The non-negative `ξ₁`-axis lies in the effective domain of the p. 253 example. -/
theorem essStrictlyConvexFn_mem_dom {t : ℝ} (ht : 0 ≤ t) :
    (WithLp.toLp 2 ![t, 0] : Rn 2) ∈ dom essStrictlyConvexFn := by
  rw [mem_dom, essStrictlyConvexFn_axis ht]
  exact lt_top_iff_ne_top.2 (by simp)

/-- **Rockafellar, §26 (p. 253).** The example is not strictly convex on `dom f`: it is identically
zero along the non-negative `ξ₁`-axis, which is a convex subset of `dom f`. This is what separates
*essential* strict convexity from strict convexity on the effective domain. -/
theorem essStrictlyConvexFn_not_strictConvexOn_dom :
    ¬ StrictConvexOnFn essStrictlyConvexFn (dom essStrictlyConvexFn) :=
  not_strictConvexOnFn_of_axis (essStrictlyConvexFn_mem_dom zero_le_one)
    (essStrictlyConvexFn_mem_dom (by norm_num)) fun _ ht => essStrictlyConvexFn_axis ht

/-! ### The counterexample of p. 254

Rockafellar's second warning: a closed proper convex function may be strictly convex on
`ri (dom f)` and still fail to be essentially strictly convex, because `dom ∂f` can be strictly
larger than `ri (dom f)` and can contain a convex set on which `f` is constant. -/

/-- **§26 (p. 254)**, the second counterexample:

```
f(ξ₁, ξ₂) = ξ₂²/2ξ₁ + ξ₂²   if ξ₁ > 0, ξ₂ ≥ 0
          = 0                if ξ₁ = 0 = ξ₂
          = +∞               otherwise.
```

Encoded exactly as `essStrictlyConvexFn` is. Rockafellar's claim is that `ri (dom f)` is the open
positive quadrant, on which `f` *is* strictly convex, while `dom ∂f` also contains the whole
non-negative `ξ₁`-axis, on which `f` is constant — so `f` is **not** essentially strictly convex.
Both halves are proved below. -/
noncomputable def strictOnRelintFn (x : Rn 2) : EReal :=
  ⨅ _ : (0 < x 0 ∧ 0 ≤ x 1) ∨ (x 0 = 0 ∧ x 1 = 0),
    ((x 1 ^ 2 / (2 * x 0) + x 1 ^ 2 : ℝ) : EReal)

/-- The value of the p. 254 example on its effective domain. -/
theorem strictOnRelintFn_of_mem {x : Rn 2}
    (h : (0 < x 0 ∧ 0 ≤ x 1) ∨ (x 0 = 0 ∧ x 1 = 0)) :
    strictOnRelintFn x = ((x 1 ^ 2 / (2 * x 0) + x 1 ^ 2 : ℝ) : EReal) :=
  iInf_pos h

/-- Off its effective domain the p. 254 example is `+∞`. -/
theorem strictOnRelintFn_of_not_mem {x : Rn 2}
    (h : ¬ ((0 < x 0 ∧ 0 ≤ x 1) ∨ (x 0 = 0 ∧ x 1 = 0))) : strictOnRelintFn x = ⊤ :=
  iInf_neg h

/-- The p. 254 example is non-negative everywhere, which is what makes `0` a subgradient at every
point where it vanishes. -/
theorem strictOnRelintFn_nonneg (x : Rn 2) : 0 ≤ strictOnRelintFn x := by
  by_cases h : (0 < x 0 ∧ 0 ≤ x 1) ∨ (x 0 = 0 ∧ x 1 = 0)
  · rw [strictOnRelintFn_of_mem h]
    have hr : (0 : ℝ) ≤ x 1 ^ 2 / (2 * x 0) + x 1 ^ 2 := by
      rcases h with ⟨h0, -⟩ | ⟨-, h1⟩
      · have hq : (0 : ℝ) ≤ x 1 ^ 2 / (2 * x 0) := div_nonneg (sq_nonneg _) (by linarith)
        nlinarith [sq_nonneg (x 1)]
      · rw [h1]
        norm_num
    exact_mod_cast hr
  · rw [strictOnRelintFn_of_not_mem h]
    exact le_top

/-- The non-negative `ξ₁`-axis of `ℝ²`. -/
def nonnegAxis : Set (Rn 2) := {x : Rn 2 | 0 ≤ x 0 ∧ x 1 = 0}

/-- The non-negative `ξ₁`-axis is convex — which is what makes it admissible in Rockafellar's
definition of essential strict convexity. -/
theorem convex_nonnegAxis : Convex ℝ nonnegAxis := by
  intro x hx y hy a b ha hb hab
  obtain ⟨hx0, hx1⟩ := hx
  obtain ⟨hy0, hy1⟩ := hy
  constructor
  · change 0 ≤ a * x 0 + b * y 0
    nlinarith
  · change a * x 1 + b * y 1 = 0
    rw [hx1, hy1]
    ring

/-- The p. 254 example vanishes on the non-negative `ξ₁`-axis. -/
theorem strictOnRelintFn_eq_zero_of_mem {x : Rn 2} (hx : x ∈ nonnegAxis) :
    strictOnRelintFn x = 0 := by
  obtain ⟨h0, h1⟩ := hx
  have hc : (0 < x 0 ∧ 0 ≤ x 1) ∨ (x 0 = 0 ∧ x 1 = 0) := by
    rcases eq_or_lt_of_le h0 with he | hlt
    · exact Or.inr ⟨he.symm, h1⟩
    · exact Or.inl ⟨hlt, le_of_eq h1.symm⟩
  rw [strictOnRelintFn_of_mem hc, h1]
  norm_num

/-- **The whole non-negative `ξ₁`-axis lies in `dom ∂f`** for the p. 254 example: the function is
non-negative and vanishes there, so `0` is a subgradient at each of its points. This is exactly
Rockafellar's observation that `dom ∂f` is bigger than `ri (dom f)` here. -/
theorem zero_mem_subgradient_strictOnRelintFn {x : Rn 2} (hx : x ∈ nonnegAxis) :
    (0 : Rn 2) ∈ subgradient (pairing 2) strictOnRelintFn x := by
  intro z
  have h0 : ((pairing 2 (z - x)) (0 : Rn 2) : ℝ) = 0 := map_zero _
  rw [strictOnRelintFn_eq_zero_of_mem hx, h0]
  simpa using strictOnRelintFn_nonneg z

/-- The p. 254 example vanishes at `(t, 0)` for `t ≥ 0`. -/
theorem strictOnRelintFn_axis {t : ℝ} (ht : 0 ≤ t) :
    strictOnRelintFn (WithLp.toLp 2 ![t, 0]) = 0 :=
  strictOnRelintFn_eq_zero_of_mem ⟨ht, rfl⟩

/-- **Rockafellar, §26 (p. 254).** The example is not essentially strictly convex: the non-negative
`ξ₁`-axis is a convex subset of `dom ∂f` on which the function is constant. -/
theorem strictOnRelintFn_not_essentiallyStrictlyConvex :
    ¬ EssentiallyStrictlyConvex (B := pairing 2) strictOnRelintFn := by
  intro h
  have hsub : nonnegAxis ⊆ domSubgradient (pairing 2) strictOnRelintFn :=
    fun _ hx => ⟨0, zero_mem_subgradient_strictOnRelintFn hx⟩
  refine not_strictConvexOnFn_of_axis (C := nonnegAxis) ⟨zero_le_one, rfl⟩
    ⟨by norm_num, rfl⟩ (fun _ ht => strictOnRelintFn_axis ht) ?_
  exact h convex_nonnegAxis hsub

/-! ### The p. 254 example is strictly convex on `ri (dom f)`

The other half of Rockafellar's claim, and what makes the example separate the two conditions.
`ri (dom f)` is the open positive quadrant, and strict convexity there is the weighted
Cauchy–Schwarz inequality `(au + bv)²/(as + bt) ≤ au²/s + bv²/t` together with
`(au + bv)² ≤ au² + bv²`, one of which is strict at any two distinct points of the quadrant. -/

/-- The open positive quadrant of `ℝ²`, which is `ri (dom f)` for the p. 254 example. -/
def openQuadrant : Set (Rn 2) := {x : Rn 2 | 0 < x 0 ∧ 0 < x 1}

theorem isOpen_openQuadrant : IsOpen openQuadrant :=
  (isOpen_lt continuous_const (continuous_coord 0)).inter
    (isOpen_lt continuous_const (continuous_coord 1))

/-- The effective domain of the p. 254 example, spelled as a set. -/
theorem dom_strictOnRelintFn :
    dom strictOnRelintFn = {x : Rn 2 | (0 < x 0 ∧ 0 ≤ x 1) ∨ (x 0 = 0 ∧ x 1 = 0)} := by
  ext x
  by_cases h : (0 < x 0 ∧ 0 ≤ x 1) ∨ (x 0 = 0 ∧ x 1 = 0)
  · simp only [mem_dom, strictOnRelintFn_of_mem h, Set.mem_ofPred_eq]
    exact ⟨fun _ => h, fun _ => EReal.coe_lt_top _⟩
  · simp only [mem_dom, strictOnRelintFn_of_not_mem h, Set.mem_ofPred_eq, lt_self_iff_false]
    exact ⟨fun hc => absurd hc not_false, fun hc => absurd hc h⟩

private theorem openQuadrant_subset_dom : openQuadrant ⊆ dom strictOnRelintFn := by
  rintro x ⟨h0, h1⟩
  rw [dom_strictOnRelintFn]
  exact Or.inl ⟨h0, h1.le⟩

/-- **`ri (dom f)` is the open positive quadrant** for the p. 254 example. The domain has
non-empty interior, so `ri` collapses to `interior`, and the interior is the quadrant because a
domain point with `ξ₂ = 0` has points with `ξ₂ < 0` arbitrarily close to it. -/
theorem relint_dom_strictOnRelintFn : ri (dom strictOnRelintFn) = openQuadrant := by
  have hpt : (WithLp.toLp 2 ![(1 : ℝ), 1] : Rn 2) ∈ openQuadrant := ⟨one_pos, one_pos⟩
  have htop : affineSpan ℝ (dom strictOnRelintFn) = ⊤ :=
    top_unique <| (isOpen_openQuadrant.affineSpan_eq_top ⟨_, hpt⟩).ge.trans
      (affineSpan_mono ℝ openQuadrant_subset_dom)
  rw [intrinsicInterior_eq_interior htop]
  refine Set.Subset.antisymm (fun x hx => ?_)
    (interior_maximal openQuadrant_subset_dom isOpen_openQuadrant)
  have hnn : ∀ y : Rn 2, y ∈ dom strictOnRelintFn → 0 ≤ y 1 := by
    intro y hy
    rw [dom_strictOnRelintFn] at hy
    rcases hy with ⟨-, h⟩ | ⟨-, h⟩
    · exact h
    · exact h.ge
  have hnorm : ‖(WithLp.toLp 2 ![(0 : ℝ), 1] : Rn 2)‖ = 1 := by
    rw [EuclideanSpace.norm_eq]
    simp [Fin.sum_univ_two]
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior x hx
  have hd : dist (x + (-(ε / 2)) • (WithLp.toLp 2 ![(0 : ℝ), 1] : Rn 2)) x = ε / 2 := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, hnorm, mul_one, Real.norm_eq_abs,
      abs_of_nonpos (by linarith), neg_neg]
  have hmem := hball (by rw [Metric.mem_ball, hd]; linarith)
  have hcoord : (x + (-(ε / 2)) • (WithLp.toLp 2 ![(0 : ℝ), 1] : Rn 2)) 1 = x 1 - ε / 2 := by
    change x 1 + -(ε / 2) * (1 : ℝ) = x 1 - ε / 2
    ring
  have hle := hnn _ (interior_subset hmem)
  rw [hcoord] at hle
  have hx1 : 0 < x 1 := by linarith
  have hxD := interior_subset hx
  rw [dom_strictOnRelintFn] at hxD
  rcases hxD with ⟨h0, -⟩ | ⟨-, h1⟩
  · exact ⟨h0, hx1⟩
  · exact absurd h1 hx1.ne'

/-- The weighted Cauchy–Schwarz identity: the gap in `(au + bv)²/(as + bt) ≤ au²/s + bv²/t` is
`ab(ut − vs)²/(st(as + bt))`. No relation between `a` and `b` is used. -/
private theorem engel_key {s t u v a b : ℝ} (hs : 0 < s) (ht : 0 < t) (ha : 0 < a) (hb : 0 < b) :
    a * (u ^ 2 / s) + b * (v ^ 2 / t) - (a * u + b * v) ^ 2 / (a * s + b * t)
      = a * b * (u * t - v * s) ^ 2 / (s * t * (a * s + b * t)) := by
  have hw : 0 < a * s + b * t := by positivity
  field_simp
  ring

private theorem engel_le {s t u v a b : ℝ} (hs : 0 < s) (ht : 0 < t) (ha : 0 < a) (hb : 0 < b) :
    (a * u + b * v) ^ 2 / (a * s + b * t) ≤ a * (u ^ 2 / s) + b * (v ^ 2 / t) := by
  have hkey := engel_key (u := u) (v := v) hs ht ha hb
  have hnn : 0 ≤ a * b * (u * t - v * s) ^ 2 / (s * t * (a * s + b * t)) := by positivity
  linarith

private theorem engel_lt {s t u v a b : ℝ} (hs : 0 < s) (ht : 0 < t) (ha : 0 < a) (hb : 0 < b)
    (hne : u * t ≠ v * s) :
    (a * u + b * v) ^ 2 / (a * s + b * t) < a * (u ^ 2 / s) + b * (v ^ 2 / t) := by
  have hkey := engel_key (u := u) (v := v) hs ht ha hb
  have hsq : 0 < (u * t - v * s) ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (sub_ne_zero.2 hne)))
  have hw : 0 < s * t * (a * s + b * t) := by positivity
  have hpos : 0 < a * b * (u * t - v * s) ^ 2 / (s * t * (a * s + b * t)) :=
    div_pos (by positivity) hw
  linarith

/-- The gap in `(au + bv)² ≤ au² + bv²` is `ab(u − v)²`, and here `a + b = 1` is used. -/
private theorem sq_combo_key {u v a b : ℝ} (hab : a + b = 1) :
    a * u ^ 2 + b * v ^ 2 - (a * u + b * v) ^ 2 = a * b * (u - v) ^ 2 := by
  linear_combination (-(a * u ^ 2 + b * v ^ 2)) * hab

/-- **§26 (p. 254)**, the positive half: the example *is* strictly convex on `ri (dom f)`, the open
positive quadrant. With `strictOnRelintFn_not_essentiallyStrictlyConvex` this is the whole point of
the example. Neither summand of `ξ₂²/2ξ₁ + ξ₂²` is strictly convex on the quadrant — the first is
positively homogeneous, hence affine along every ray from the origin, and the second is constant in
`ξ₁` — so no sum rule applies; what makes the sum strict is that their directions of affineness are
disjoint. -/
theorem strictConvexOnFn_strictOnRelintFn :
    StrictConvexOnFn strictOnRelintFn (ri (dom strictOnRelintFn)) := by
  rw [relint_dom_strictOnRelintFn]
  rintro x ⟨hx0, hx1⟩ y ⟨hy0, hy1⟩ hxy a b ha hb hab
  have hzc0 : (a • x + b • y : Rn 2) 0 = a * x 0 + b * y 0 := rfl
  have hzc1 : (a • x + b • y : Rn 2) 1 = a * x 1 + b * y 1 := rfl
  have hz0 : 0 < a * x 0 + b * y 0 := by positivity
  have hz1 : 0 < a * x 1 + b * y 1 := by positivity
  have hxm : (0 < x 0 ∧ 0 ≤ x 1) ∨ (x 0 = 0 ∧ x 1 = 0) := Or.inl ⟨hx0, hx1.le⟩
  have hym : (0 < y 0 ∧ 0 ≤ y 1) ∨ (y 0 = 0 ∧ y 1 = 0) := Or.inl ⟨hy0, hy1.le⟩
  have hzm : (0 < (a • x + b • y : Rn 2) 0 ∧ 0 ≤ (a • x + b • y : Rn 2) 1)
      ∨ ((a • x + b • y : Rn 2) 0 = 0 ∧ (a • x + b • y : Rn 2) 1 = 0) :=
    Or.inl ⟨by rw [hzc0]; exact hz0, by rw [hzc1]; exact hz1.le⟩
  rw [strictOnRelintFn_of_mem hxm, strictOnRelintFn_of_mem hym, strictOnRelintFn_of_mem hzm,
    hzc0, hzc1, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add,
    EReal.coe_lt_coe_iff]
  have hden : a * (2 * x 0) + b * (2 * y 0) = 2 * (a * x 0 + b * y 0) := by ring
  have hexp : a * (x 1 ^ 2 / (2 * x 0) + x 1 ^ 2) + b * (y 1 ^ 2 / (2 * y 0) + y 1 ^ 2)
      = (a * (x 1 ^ 2 / (2 * x 0)) + b * (y 1 ^ 2 / (2 * y 0)))
        + (a * x 1 ^ 2 + b * y 1 ^ 2) := by ring
  have hx0' : (0 : ℝ) < 2 * x 0 := by linarith
  have hy0' : (0 : ℝ) < 2 * y 0 := by linarith
  have hsq := sq_combo_key (u := x 1) (v := y 1) hab
  rw [hexp]
  rcases eq_or_ne (x 1) (y 1) with h1 | h1
  · have hx0y0 : x 0 ≠ y 0 := fun h => hxy (ext_two h h1)
    have hne : x 1 * (2 * y 0) ≠ y 1 * (2 * x 0) := by
      rw [h1]
      intro hcon
      exact hx0y0 (by linarith [mul_left_cancel₀ hy1.ne' hcon, h1])
    have hA := engel_lt (u := x 1) (v := y 1) hx0' hy0' ha hb hne
    rw [hden] at hA
    have hB : (a * x 1 + b * y 1) ^ 2 ≤ a * x 1 ^ 2 + b * y 1 ^ 2 := by
      nlinarith [sq_nonneg (x 1 - y 1), mul_pos ha hb]
    linarith
  · have hA := engel_le (u := x 1) (v := y 1) hx0' hy0' ha hb
    rw [hden] at hA
    have hB : (a * x 1 + b * y 1) ^ 2 < a * x 1 ^ 2 + b * y 1 ^ 2 := by
      have hsq0 : 0 < (x 1 - y 1) ^ 2 :=
        lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (sub_ne_zero.2 h1)))
      nlinarith [mul_pos ha hb]
    linarith

/-! ### Theorem 26.3 -/

/-- **Rockafellar, Theorem 26.3.** A closed proper convex function is essentially strictly convex
if and only if its conjugate is essentially smooth. -/
theorem theorem_26_3 (hf : ConvexFn f) (hp : Proper f) (hcl : ClosedFn f) :
    EssentiallyStrictlyConvex (B := pairing n) f ↔ EssentiallySmooth (conj (pairing n) f) :=
  (essentiallySmooth_conj_iff_essentiallyStrictlyConvex hf hp hcl).symm

/-- **Rockafellar, Theorem 26.3**, read at `f*`: the conjugate of a closed proper convex function is
essentially strictly convex exactly when the function itself is essentially smooth. This is the
direction Corollaries 26.3.2 and 26.3.3 use. -/
theorem theorem_26_3' (hf : ConvexFn f) (hp : Proper f) (hcl : ClosedFn f) :
    EssentiallyStrictlyConvex (B := pairing n) (conj (pairing n) f) ↔ EssentiallySmooth f :=
  essentiallyStrictlyConvex_conj_iff_essentiallySmooth hf hp hcl

/-! ### Corollary 26.3.1 -/

/-- **Rockafellar, Corollary 26.3.1.** Let `f` be a closed proper convex function. Then `∂f` is a
one-to-one mapping if and only if `f` is strictly convex on `int (dom f)` and essentially smooth. -/
theorem corollary_26_3_1 (hf : ConvexFn f) (hp : Proper f) (hcl : ClosedFn f) :
    OneToOne (subgradient (pairing n) f) ↔
      (StrictConvexOnFn f (interior (dom f)) ∧ EssentiallySmooth f) :=
  oneToOne_iff.trans ((subgradient_injective_iff hf hp hcl).trans and_comm)

/-! ### Corollaries 26.3.2 and 26.3.3: preservation of essential smoothness -/

/-- **Rockafellar, Corollary 26.3.2.** Let `f₁` and `f₂` be closed proper convex functions on `ℝⁿ`
such that `f₁` is essentially smooth and `ri (dom f₁*) ∩ ri (dom f₂*) ≠ ∅`. Then `f₁ □ f₂` is
essentially smooth. -/
theorem corollary_26_3_2 {f₁ f₂ : Rn n → EReal} (h₁ : ClosedProperConvexFn f₁)
    (h₂ : ClosedProperConvexFn f₂) (hes : EssentiallySmooth f₁)
    (hri : (ri (dom (conj (pairing n) f₁)) ∩ ri (dom (conj (pairing n) f₂))).Nonempty) :
    EssentiallySmooth (infConv f₁ f₂) := by
  obtain ⟨y₀, hy₁, hy₂⟩ := hri
  exact essentiallySmooth_infConv_of_relint h₁ h₂ hes hy₁ hy₂

/-- **Rockafellar, Corollary 26.3.3.** Let `f` be a closed proper convex function on `ℝⁿ` which is
essentially smooth, and let `A` be a linear transformation from `ℝⁿ` onto `ℝᵐ`. If there exists a
`y* ∈ ℝᵐ` such that `A* y* ∈ ri (dom f*)`, then the convex function `Af` on `ℝᵐ` is essentially
smooth.

`A*` is `LinearMap.adjoint A`; the surjectivity of `A` is used only to make `A*` injective, which is
what the argument consumes. -/
theorem corollary_26_3_3 {m : ℕ} {g : Rn n → EReal} (hg : ClosedProperConvexFn g)
    (hes : EssentiallySmooth g) (A : Rn n →ₗ[ℝ] Rn m) (hsurj : Function.Surjective A) {y : Rn m}
    (hy : LinearMap.adjoint A y ∈ ri (dom (conj (pairing n) g))) :
    EssentiallySmooth (mapLin A g) := by
  have hA : IsAdjointPair (innerₗ (Rn m)) (innerₗ (Rn n)) (LinearMap.adjoint A) A := by
    have h := isAdjointPair_adjoint (LinearMap.adjoint A)
    rwa [LinearMap.adjoint_adjoint] at h
  exact essentiallySmooth_mapLin_of_relint hA hg hes hsurj hy

/-! ### The Legendre conjugate

Rockafellar, p. 256. For a differentiable real-valued `f` on an open set `C ⊆ ℝⁿ`, the **Legendre
conjugate** of `(C, f)` is the pair `(D, g)` where `D = ∇f(C)` and

```
g(x*) = ⟨(∇f)⁻¹(x*), x*⟩ − f((∇f)⁻¹(x*)).
```

`∇f` need not be one-to-one for `g` to be well defined; it suffices that `⟨x, x*⟩ − f(x)` be the
same for every `x` with `∇f x = x*`, which is Theorem 26.4's first clause. -/

/-- **Rockafellar, §26 (p. 256).** Rockafellar's `D`: the image of `C = int (dom f)` under the
gradient mapping. -/
def legendreDomain (f : Rn n → EReal) : Set (Rn n) :=
  gradient (fun w => (f w).toReal) '' interior (dom f)

/-- **The bridge to the backbone's `gradientRange`**, valid as soon as condition (b) holds:
`{v | ∃ x, ∇f x = v}` and "the image of `C` under `∇f`" are the same set, because every gradient is
attained at an interior point of `dom f` (Corollary 25.1.1) and, on `C`, Mathlib's `gradient` of the
real trace *is* Rockafellar's `∇f`. -/
theorem legendreDomain_eq_gradientRange
    (hdiff : ∀ ⦃z : Rn n⦄, z ∈ interior (dom f) → DifferentiableAtFn f z) :
    legendreDomain f = gradientRange f := by
  ext v
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (hdiff hz).hasGradientAtFn_gradient.mem_gradientRange
  · rintro ⟨z, hz⟩
    exact ⟨z, hz.mem_interior_dom, by
      rw [hz.gradient_toReal_eq, LinearIsometryEquiv.symm_apply_apply]⟩

/-! ### Theorem 26.4 -/

/-- **Rockafellar, Theorem 26.4**, first clause: the Legendre conjugate `(D, g)` of `(C, f)` is
well-defined. Whatever `x` is chosen in `(∇f)⁻¹(x*)`, the value `⟨x, x*⟩ − f(x)` is the same.

**Only convexity is needed.** The book states the theorem for a closed proper convex `f` with
non-empty `C = int (dom f)` on which `f` is differentiable; the well-definedness is a consequence of
Theorem 23.5 at the two points separately and holds wherever two gradients happen to agree. -/
theorem theorem_26_4_wellDefined (hf : ConvexFn f) {v x₁ x₂ : Rn n}
    (h₁ : HasGradientAtFn f (InnerProductSpace.toDual ℝ (Rn n) v) x₁)
    (h₂ : HasGradientAtFn f (InnerProductSpace.toDual ℝ (Rn n) v) x₂) :
    pairing n x₁ v - (f x₁).toReal = pairing n x₂ v - (f x₂).toReal := by
  obtain ⟨r₁, hr₁⟩ := h₁.exists_coe
  obtain ⟨r₂, hr₂⟩ := h₂.exists_coe
  have h := sub_eq_sub_of_hasGradientAtFn hf h₁ h₂ hr₁ hr₂
  rw [toDual_apply_eq_pairing, toDual_apply_eq_pairing] at h
  rw [hr₁, hr₂]
  simpa using h

/-- **Rockafellar, Theorem 26.4**, second and third clauses: `D ⊆ dom f*`, and `g` is the
restriction of `f*` to `D` — at a point `x*` of `D` the defining formula returns `f*(x*)`. -/
theorem theorem_26_4_eq (hf : ConvexFn f) {v x : Rn n}
    (h : HasGradientAtFn f (InnerProductSpace.toDual ℝ (Rn n) v) x) :
    conj (pairing n) f v = ((pairing n x v - (f x).toReal : ℝ) : EReal) := by
  obtain ⟨r, hr⟩ := h.exists_coe
  have hval := conj_eq_of_hasGradientAtFn hf h hr
  rw [conj_innerL_eq_conj_topDualPairing, hval, toDual_apply_eq_pairing, hr]
  simp

/-- **Rockafellar, Theorem 26.4**: `D` is a subset of `dom f*`. -/
theorem theorem_26_4_subset_dom_conj (hf : ConvexFn f)
    (hdiff : ∀ ⦃z : Rn n⦄, z ∈ interior (dom f) → DifferentiableAtFn f z) :
    legendreDomain f ⊆ dom (conj (pairing n) f) := by
  rw [legendreDomain_eq_gradientRange hdiff]
  rintro v ⟨x, hx⟩
  rw [mem_dom, theorem_26_4_eq hf hx]
  exact EReal.coe_lt_top _

/-! ### Corollary 26.4.1 -/

/-- **Rockafellar, Corollary 26.4.1**, first clause: for an essentially smooth closed proper convex
`f`, the domain `D` of the Legendre conjugate is `{x* | ∂f*(x*) ≠ ∅}`. -/
theorem corollary_26_4_1_dom (hf : ConvexFn f) (hp : Proper f) (hcl : ClosedFn f)
    (hes : EssentiallySmooth f) :
    legendreDomain f = domSubgradient (pairing n) (conj (pairing n) f) := by
  rw [legendreDomain_eq_gradientRange hes.differentiableAtFn]
  exact gradientRange_eq_domSubgradient_conj hf hp hcl hes

/-- **Rockafellar, Corollary 26.4.1**: `ri (dom f*) ⊆ D`, so `D` is "almost convex". -/
theorem corollary_26_4_1_relint_subset (hf : ConvexFn f) (hp : Proper f) (hcl : ClosedFn f)
    (hes : EssentiallySmooth f) : ri (dom (conj (pairing n) f)) ⊆ legendreDomain f := by
  rw [legendreDomain_eq_gradientRange hes.differentiableAtFn]
  exact relint_dom_conj_subset_gradientRange hf hp hcl hes

/-- **Rockafellar, Corollary 26.4.1**: `D ⊆ dom f*`, the other half of the squeeze. -/
theorem corollary_26_4_1_subset_dom (hf : ConvexFn f) (hp : Proper f) (hcl : ClosedFn f)
    (hes : EssentiallySmooth f) : legendreDomain f ⊆ dom (conj (pairing n) f) := by
  rw [legendreDomain_eq_gradientRange hes.differentiableAtFn]
  exact gradientRange_subset_dom_conj hf hp hcl hes

/-- **Rockafellar, Corollary 26.4.1**: `g` is the restriction of `f*` to `D`. -/
theorem corollary_26_4_1_eq (hf : ConvexFn f) (hes : EssentiallySmooth f) {x : Rn n}
    (hx : x ∈ interior (dom f)) :
    conj (pairing n) f (gradient (fun w => (f w).toReal) x)
      = ((pairing n x (gradient (fun w => (f w).toReal) x) - (f x).toReal : ℝ) : EReal) :=
  theorem_26_4_eq hf (hes.differentiableAtFn hx).hasGradientAtFn_gradient

/-- **Rockafellar, Corollary 26.4.1**, last clause: `g` is strictly convex on every convex subset
of `D`. Since `g = f*` on `D` (Theorem 26.4), this is the essential strict convexity of `f*`, which
Theorem 26.3 supplies from the essential smoothness of `f`. -/
theorem corollary_26_4_1_strictConvexOn (hf : ConvexFn f) (hp : Proper f) (hcl : ClosedFn f)
    (hes : EssentiallySmooth f) {C : Set (Rn n)} (hC : Convex ℝ C) (hCsub : C ⊆ legendreDomain f) :
    StrictConvexOnFn (conj (pairing n) f) C := by
  rw [legendreDomain_eq_gradientRange hes.differentiableAtFn] at hCsub
  exact strictConvexOnFn_conj_of_subset_gradientRange hf hp hcl hes hC hCsub

/-! ### The counterexample of p. 257: the parabola

Rockafellar, p. 257: if `f` is a differentiable convex function on a non-empty open convex set `C`
failing condition (c), the domain `D` of the Legendre conjugate need not be *almost convex*. The
witness is `ξ₁²/4ξ₂` on the open upper half-plane, whose `D` is the parabola `ξ₂* = −(ξ₁*)²`.
Without condition (c) the squeeze `ri (dom f*) ⊆ D ⊆ dom f*` of Corollary 26.4.1 fails, and `D`
need not even be convex. -/

/-- The vector `(a, −a²)` of `ℝ²`. -/
noncomputable def parabolaPoint (a : ℝ) : Rn 2 := WithLp.toLp 2 ![a, -a ^ 2]

@[simp] theorem parabolaPoint_zero (a : ℝ) : parabolaPoint a 0 = a := rfl

@[simp] theorem parabolaPoint_one (a : ℝ) : parabolaPoint a 1 = -a ^ 2 := rfl

theorem parabolaPoint_zero_eq : parabolaPoint 0 = 0 :=
  ext_two (by norm_num) (by norm_num)

/-- **Rockafellar, §26 (p. 257).** The parabola `P = {(ξ₁*, ξ₂*) | ξ₂* = −(ξ₁*)²}`. -/
def parabola : Set (Rn 2) := {w : Rn 2 | w 1 = -(w 0) ^ 2}

theorem mem_parabola {w : Rn 2} : w ∈ parabola ↔ w 1 = -(w 0) ^ 2 := Iff.rfl

/-- **Rockafellar, §26 (p. 257).** `f(ξ₁, ξ₂) = ξ₁²/4ξ₂` on the open upper half-plane, extended by
`+∞`, so that `C = int (dom f)` is exactly the open upper half-plane. -/
noncomputable def halfPlaneFn (x : Rn 2) : EReal :=
  ⨅ _ : 0 < x 1, ((x 0 ^ 2 / (4 * x 1) : ℝ) : EReal)

theorem halfPlaneFn_of_pos {x : Rn 2} (hx : 0 < x 1) :
    halfPlaneFn x = ((x 0 ^ 2 / (4 * x 1) : ℝ) : EReal) := iInf_pos hx

theorem halfPlaneFn_of_nonpos {x : Rn 2} (hx : ¬ 0 < x 1) : halfPlaneFn x = ⊤ := iInf_neg hx

theorem halfPlaneFn_ne_bot (x : Rn 2) : halfPlaneFn x ≠ ⊥ := by
  by_cases hx : 0 < x 1
  · rw [halfPlaneFn_of_pos hx]; exact EReal.coe_ne_bot _
  · rw [halfPlaneFn_of_nonpos hx]; exact top_ne_bot

theorem dom_halfPlaneFn : dom halfPlaneFn = {x : Rn 2 | 0 < x 1} := by
  ext x
  rw [mem_dom]
  by_cases hx : 0 < x 1
  · simp [halfPlaneFn_of_pos hx, hx]
  · simp [halfPlaneFn_of_nonpos hx, hx]

/-- `C = int (dom f)` is the open upper half-plane, as the book takes it to be. -/
theorem interior_dom_halfPlaneFn : interior (dom halfPlaneFn) = {x : Rn 2 | 0 < x 1} := by
  rw [dom_halfPlaneFn]
  exact IsOpen.interior_eq (isOpen_lt continuous_const (by fun_prop))

/-- The p. 257 example is convex: "quadratic over linear" is jointly convex, and the identity
that says so is `A − B = ab(ξ₁ η₂ − η₁ ξ₂)² / 4ξ₂η₂(aξ₂ + bη₂)`. -/
theorem convexFn_halfPlaneFn : ConvexFn halfPlaneFn := by
  refine (convexFn_iff_le halfPlaneFn_ne_bot).2 fun x y a b ha hb hab => ?_
  by_cases hx : 0 < x 1
  · by_cases hy : 0 < y 1
    · have h0 : (a • x + b • y) 0 = a * x 0 + b * y 0 := rfl
      have h1 : (a • x + b • y) 1 = a * x 1 + b * y 1 := rfl
      have hz : 0 < (a • x + b • y) 1 := by rw [h1]; positivity
      rw [halfPlaneFn_of_pos hx, halfPlaneFn_of_pos hy, halfPlaneFn_of_pos hz, h0, h1,
        ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add,
        EReal.coe_le_coe_iff]
      have hx0 : x 1 ≠ 0 := ne_of_gt hx
      have hy0 : y 1 ≠ 0 := ne_of_gt hy
      have hs : 0 < a * x 1 + b * y 1 := by positivity
      have hs0 : a * x 1 + b * y 1 ≠ 0 := ne_of_gt hs
      have hid : a * (x 0 ^ 2 / (4 * x 1)) + b * (y 0 ^ 2 / (4 * y 1))
            - (a * x 0 + b * y 0) ^ 2 / (4 * (a * x 1 + b * y 1))
          = a * b * (x 0 * y 1 - y 0 * x 1) ^ 2
              / (4 * (x 1 * y 1 * (a * x 1 + b * y 1))) := by
        field_simp
        ring
      have hnn : 0 ≤ a * b * (x 0 * y 1 - y 0 * x 1) ^ 2
          / (4 * (x 1 * y 1 * (a * x 1 + b * y 1))) := by positivity
      linarith
    · rw [halfPlaneFn_of_nonpos hy, EReal.coe_mul_top_of_pos hb,
        EReal.add_top_of_ne_bot (EReal.coe_mul_ne_bot ha.le (halfPlaneFn_ne_bot x))]
      exact le_top
  · rw [halfPlaneFn_of_nonpos hx, EReal.coe_mul_top_of_pos ha,
      EReal.top_add_of_ne_bot (EReal.coe_mul_ne_bot hb.le (halfPlaneFn_ne_bot y))]
    exact le_top

theorem proper_halfPlaneFn : Proper halfPlaneFn := by
  refine ⟨⟨WithLp.toLp 2 ![0, 1], ?_⟩, halfPlaneFn_ne_bot⟩
  rw [mem_dom, halfPlaneFn_of_pos (x := WithLp.toLp 2 ![0, 1]) (by norm_num)]
  exact EReal.coe_lt_top _

/-- **The subdifferential of `ξ₁²/4ξ₂` in coordinates.** Both directions come from the same
completed square: `ξ₁²/4ξ₂ − u₀ξ₁ − u₁ξ₂ = (ξ₁ − 2u₀ξ₂)²/4ξ₂ − ξ₂(u₀² + u₁)`, whose infimum over
the ray `ξ = (2su₀, s)` is `−s(u₀² + u₁)`. Testing at `s = ξ₂`, `s = ξ₂ + 1` and `s = ξ₂/2` forces
both `u₀² + u₁ = 0` and the completed square to vanish, with no case analysis. -/
theorem mem_subgradient_halfPlaneFn_iff {x u : Rn 2} (hx : 0 < x 1) :
    u ∈ subgradient (pairing 2) halfPlaneFn x ↔ u 1 = -(u 0) ^ 2 ∧ x 0 = 2 * u 0 * x 1 := by
  constructor
  · intro h
    have key : ∀ s : ℝ, 0 < s →
        x 0 ^ 2 / (4 * x 1) - u 0 * x 0 - u 1 * x 1 ≤ -(s * (u 0 ^ 2 + u 1)) := by
      intro s hs
      have hzs : (0 : ℝ) < (WithLp.toLp 2 ![2 * s * u 0, s] : Rn 2) 1 := hs
      have hle := h (WithLp.toLp 2 ![2 * s * u 0, s] : Rn 2)
      rw [halfPlaneFn_of_pos hx, halfPlaneFn_of_pos hzs, pairing_two] at hle
      rw [sub_apply_two, sub_apply_two, ← EReal.coe_add,
        EReal.coe_le_coe_iff] at hle
      have e0 : (WithLp.toLp 2 ![2 * s * u 0, s] : Rn 2) 0 = 2 * s * u 0 := rfl
      have e1 : (WithLp.toLp 2 ![2 * s * u 0, s] : Rn 2) 1 = s := rfl
      rw [e0, e1] at hle
      have hrs : (2 * s * u 0) ^ 2 / (4 * s) = s * u 0 ^ 2 := by
        field_simp
        ring
      rw [hrs] at hle
      nlinarith [hle]
    have hK : 0 ≤ (x 0 - 2 * u 0 * x 1) ^ 2 / (4 * x 1) := by positivity
    have hid : x 0 ^ 2 / (4 * x 1) - u 0 * x 0 - u 1 * x 1
        = (x 0 - 2 * u 0 * x 1) ^ 2 / (4 * x 1) - x 1 * (u 0 ^ 2 + u 1) := by
      have hx0 : x 1 ≠ 0 := ne_of_gt hx
      field_simp
      ring
    have h1 := key (x 1) hx
    have h2 := key (x 1 + 1) (by linarith)
    have h3 := key (x 1 / 2) (by linarith)
    rw [hid] at h1 h2 h3
    have hd : u 0 ^ 2 + u 1 = 0 := by nlinarith [hK, hx]
    have hKz : (x 0 - 2 * u 0 * x 1) ^ 2 / (4 * x 1) = 0 := by nlinarith [hK, hd]
    refine ⟨by linarith, ?_⟩
    have hx0 : x 1 ≠ 0 := ne_of_gt hx
    have hsq : (x 0 - 2 * u 0 * x 1) ^ 2 = 0 := by
      field_simp at hKz
      simpa using hKz
    have hz := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hsq
    linarith
  · rintro ⟨hu1, hu0⟩ z
    by_cases hz : 0 < z 1
    · rw [halfPlaneFn_of_pos hx, halfPlaneFn_of_pos hz, pairing_two, sub_apply_two,
        sub_apply_two, ← EReal.coe_add, EReal.coe_le_coe_iff]
      have hz4 : (0 : ℝ) < 4 * z 1 := by linarith
      have hxval : x 0 ^ 2 / (4 * x 1) = u 0 ^ 2 * x 1 := by
        have hx0 : x 1 ≠ 0 := ne_of_gt hx
        rw [hu0]
        field_simp
        ring
      rw [hxval, hu0, hu1, le_div_iff₀ hz4]
      nlinarith [sq_nonneg (z 0 - 2 * u 0 * z 1)]
    · rw [halfPlaneFn_of_nonpos hz]
      exact le_top

/-- On the open upper half-plane the subdifferential of the p. 257 example is the single vector
`(ξ₁/2ξ₂, −ξ₁²/4ξ₂²)`, which lies on the parabola. -/
theorem subgradient_halfPlaneFn {x : Rn 2} (hx : 0 < x 1) :
    subgradient (pairing 2) halfPlaneFn x = {parabolaPoint (x 0 / (2 * x 1))} := by
  have hx0 : x 1 ≠ 0 := ne_of_gt hx
  ext u
  rw [mem_subgradient_halfPlaneFn_iff hx, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hu1, hu0⟩
    have hu : u 0 = x 0 / (2 * x 1) := by field_simp; linarith
    exact ext_two (by rw [parabolaPoint_zero, hu]) (by rw [parabolaPoint_one, hu1, hu])
  · rintro rfl
    refine ⟨by rw [parabolaPoint_zero, parabolaPoint_one], ?_⟩
    rw [parabolaPoint_zero]
    field_simp

/-- The p. 257 example is differentiable throughout `C`, its gradient at `x` being the single
subgradient there (Theorem 25.1 backwards). -/
theorem hasGradientAtFn_halfPlaneFn {x : Rn 2} (hx : 0 < x 1) :
    HasGradientAtFn halfPlaneFn
      (InnerProductSpace.toDual ℝ (Rn 2) (parabolaPoint (x 0 / (2 * x 1)))) x :=
  hasGradientAtFn_toDual_of_subgradient_eq_singleton convexFn_halfPlaneFn proper_halfPlaneFn
    (subgradient_halfPlaneFn hx)

theorem differentiableAtFn_halfPlaneFn ⦃z : Rn 2⦄ (hz : z ∈ interior (dom halfPlaneFn)) :
    DifferentiableAtFn halfPlaneFn z := by
  rw [interior_dom_halfPlaneFn] at hz
  exact ⟨_, hasGradientAtFn_halfPlaneFn hz⟩

/-- **Rockafellar, §26 (p. 257).** The image `D` of `C` under `∇f` is exactly the parabola: as
`x` runs over the open upper half-plane, `ξ₁/2ξ₂` runs over all of `ℝ`, and the second coordinate
of the gradient is forced to be minus its square. -/
theorem gradientRange_halfPlaneFn : gradientRange halfPlaneFn = parabola := by
  ext v
  constructor
  · rintro ⟨x, hx⟩
    have hxi : x ∈ interior (dom halfPlaneFn) := hx.mem_interior_dom
    rw [interior_dom_halfPlaneFn] at hxi
    have hsing := subgradient_innerL_eq_singleton convexFn_halfPlaneFn hx
    rw [LinearIsometryEquiv.symm_apply_apply] at hsing
    have hv : v ∈ subgradient (pairing 2) halfPlaneFn x := by
      rw [hsing]
      exact Set.mem_singleton v
    exact ((mem_subgradient_halfPlaneFn_iff hxi).1 hv).1
  · intro hv
    refine ⟨WithLp.toLp 2 ![v 0, 1 / 2], ?_⟩
    have hx1 : (0 : ℝ) < (WithLp.toLp 2 ![v 0, 1 / 2] : Rn 2) 1 := by norm_num
    have h := hasGradientAtFn_halfPlaneFn hx1
    have e0 : (WithLp.toLp 2 ![v 0, 1 / 2] : Rn 2) 0 = v 0 := rfl
    have e1 : (WithLp.toLp 2 ![v 0, 1 / 2] : Rn 2) 1 = 1 / 2 := rfl
    have hpt : parabolaPoint ((WithLp.toLp 2 ![v 0, 1 / 2] : Rn 2) 0
        / (2 * (WithLp.toLp 2 ![v 0, 1 / 2] : Rn 2) 1)) = v := by
      refine ext_two ?_ ?_
      · rw [parabolaPoint_zero, e0, e1]
        norm_num
      · rw [parabolaPoint_one, mem_parabola.1 hv, e0, e1]
        norm_num
    rwa [hpt] at h

/-- **Rockafellar, §26 (p. 257).** `D` is the parabola, in the book's own `legendreDomain`. -/
theorem legendreDomain_halfPlaneFn : legendreDomain halfPlaneFn = parabola := by
  rw [legendreDomain_eq_gradientRange differentiableAtFn_halfPlaneFn]
  exact gradientRange_halfPlaneFn

/-- The parabola is not convex: `(0, 0)` and `(1, −1)` lie on it and their midpoint
`(1/2, −1/2)` does not, since `−1/2 ≠ −1/4`. -/
theorem not_convex_parabola : ¬ Convex ℝ parabola := by
  intro h
  have h0 : parabolaPoint 0 ∈ parabola := by
    rw [mem_parabola, parabolaPoint_zero, parabolaPoint_one]
  have h1 : parabolaPoint 1 ∈ parabola := by
    rw [mem_parabola, parabolaPoint_zero, parabolaPoint_one]
  have hm := h h0 h1 (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
  rw [mem_parabola] at hm
  have e0 : ((1/2 : ℝ) • parabolaPoint 0 + (1/2 : ℝ) • parabolaPoint 1) 0 = 1/2 := by
    change (1/2 : ℝ) * parabolaPoint 0 0 + (1/2 : ℝ) * parabolaPoint 1 0 = 1/2
    rw [parabolaPoint_zero, parabolaPoint_zero]
    norm_num
  have e1 : ((1/2 : ℝ) • parabolaPoint 0 + (1/2 : ℝ) • parabolaPoint 1) 1 = -(1/2) := by
    change (1/2 : ℝ) * parabolaPoint 0 1 + (1/2 : ℝ) * parabolaPoint 1 1 = -(1/2)
    rw [parabolaPoint_one, parabolaPoint_one]
    norm_num
  rw [e0, e1] at hm
  norm_num at hm

/-- **Rockafellar, §26 (p. 257), the point of the example.** For a differentiable convex function on
a non-empty open convex set that fails condition (c), the domain `D` of the Legendre conjugate need
not be convex — let alone "almost convex" in the sense of Corollary 26.4.1. -/
theorem not_convex_legendreDomain_halfPlaneFn : ¬ Convex ℝ (legendreDomain halfPlaneFn) := by
  rw [legendreDomain_halfPlaneFn]
  exact not_convex_parabola

/-- **Rockafellar, §26 (p. 257), last sentence**: "Condition (c) fails for `f` at the origin."
Along the sequence `(0, 1/(i+1))`, which lies in `C` and converges to the origin, the gradient is
identically `0`; so its norm does not tend to `+∞` and the p. 257 example is not essentially
smooth. This is why Corollary 26.4.1 does not apply to it, and hence why
`not_convex_legendreDomain_halfPlaneFn` is not a contradiction. -/
theorem not_essentiallySmooth_halfPlaneFn : ¬ EssentiallySmooth halfPlaneFn := by
  intro hes
  set e : Rn 2 := WithLp.toLp 2 ![0, 1] with he
  set zs : ℕ → Rn 2 := fun i => (1 / (i + 1 : ℝ)) • e with hzsdef
  have hcoord : ∀ i : ℕ, zs i 1 = 1 / (i + 1 : ℝ) := by
    intro i
    change (1 / (i + 1 : ℝ)) * (1 : ℝ) = 1 / (i + 1 : ℝ)
    ring
  have hcoord0 : ∀ i : ℕ, zs i 0 = 0 := by
    intro i
    change (1 / (i + 1 : ℝ)) * (0 : ℝ) = 0
    ring
  have hpos : ∀ i : ℕ, (0 : ℝ) < zs i 1 := by
    intro i
    rw [hcoord i]
    positivity
  have hmem : ∀ i, zs i ∈ interior (dom halfPlaneFn) := by
    intro i
    rw [interior_dom_halfPlaneFn]
    exact hpos i
  have hout : (0 : Rn 2) ∉ interior (dom halfPlaneFn) := by
    rw [interior_dom_halfPlaneFn]
    intro hc
    have hlt : (0 : ℝ) < (0 : Rn 2) 1 := hc
    simp at hlt
  have hlim : Tendsto zs atTop (𝓝 (0 : Rn 2)) := by
    have hc : Tendsto (fun i : ℕ => (1 / (i + 1 : ℝ))) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hcs := hc.smul_const e
    rwa [zero_smul] at hcs
  have htop := hes.tendsto_norm_fderiv hout zs hmem hlim
  have hzero : ∀ i, ‖fderiv ℝ (fun w => (halfPlaneFn w).toReal) (zs i)‖ = 0 := by
    intro i
    have hg := hasGradientAtFn_halfPlaneFn (hpos i)
    rw [hg.fderiv_toReal_eq]
    have hpt : parabolaPoint (zs i 0 / (2 * zs i 1)) = 0 := by
      rw [hcoord0 i, zero_div]
      exact parabolaPoint_zero_eq
    rw [hpt, map_zero, norm_zero]
  rw [tendsto_congr hzero] at htop
  exact not_tendsto_atTop_of_tendsto_nhds tendsto_const_nhds htop

/-! ### Functions of Legendre type

A pair `(C, f)` with `C` open convex and `f` strictly convex on `C` satisfying (a), (b) and (c) is
a **convex function of Legendre type** (p. 258). Since `C = int (dom f)` is determined by `f`, this
is the backbone's `LegendreType f`, which by Corollary 26.3.1 holds exactly when `∂f` is
one-to-one. -/

/-- **Rockafellar, p. 258**, the characterisation the book states immediately after the definition:
a closed proper convex function `f` has `∂f` one-to-one if and only if the restriction of `f` to
`C = int (dom f)` is a convex function of Legendre type. -/
theorem legendreType_iff (hf : ConvexFn f) (hp : Proper f) (hcl : ClosedFn f) :
    LegendreType f ↔ OneToOne (subgradient (pairing n) f) :=
  (legendreType_iff_subgradient_injective hf hp hcl).trans oneToOne_iff.symm

/-! ### Theorem 26.5 -/

/-- **Rockafellar, Theorem 26.5**, first assertion. Let `f` be a closed convex function, and let
`C = int (dom f)`, `C* = int (dom f*)`. Then `(C, f)` is a convex function of Legendre type if and
only if `(C*, f*)` is. -/
theorem theorem_26_5 (hf : ConvexFn f) (hp : Proper f) (hcl : ClosedFn f) :
    LegendreType f ↔ LegendreType (conj (pairing n) f) :=
  (legendreType_conj_iff hf hp hcl).symm

/-- **Rockafellar, Theorem 26.5**: when `f` is of Legendre type, `(C*, f*)` **is** the Legendre
conjugate of `(C, f)` — the domain half, `D = C*`. -/
theorem theorem_26_5_legendreDomain (hf : ConvexFn f) (hp : Proper f) (hcl : ClosedFn f)
    (hleg : LegendreType f) :
    legendreDomain f = interior (dom (conj (pairing n) f)) := by
  rw [legendreDomain_eq_gradientRange hleg.1.differentiableAtFn]
  exact gradientRange_eq_interior_dom_conj hf hp hcl hleg

/-- **Rockafellar, Theorem 26.5**: the value half of "`(C*, f*)` is the Legendre conjugate of
`(C, f)`" — on `C` the defining formula of the Legendre conjugate returns `f*`. -/
theorem theorem_26_5_conj_apply (hf : ConvexFn f) (hleg : LegendreType f) {x : Rn n}
    (hx : x ∈ interior (dom f)) :
    conj (pairing n) f (gradient (fun w => (f w).toReal) x)
      = ((pairing n x (gradient (fun w => (f w).toReal) x) - (f x).toReal : ℝ) : EReal) :=
  corollary_26_4_1_eq hf hleg.1 hx

/-- **Rockafellar, Theorem 26.5**: `(C, f)` is *in turn* the Legendre conjugate of `(C*, f*)` — the
domain half. Note the hypothesis: this is the involutivity of the Legendre transformation, and it
holds **only** within the Legendre-type class. See the module docstring. -/
theorem theorem_26_5_legendreDomain_conj (hf : ConvexFn f) (hp : Proper f) (hcl : ClosedFn f)
    (hleg : LegendreType f) :
    legendreDomain (conj (pairing n) f) = interior (dom f) := by
  have hgleg := hleg.conj hf hp hcl
  have h := theorem_26_5_legendreDomain (convexFn_conj _ f) (proper_conj ⟨hf, hcl, hp⟩)
    closedFn_conj hgleg
  rwa [conj_conj_innerL hf hcl] at h

/-- **Rockafellar, Theorem 26.5**: `(C, f)` is in turn the Legendre conjugate of `(C*, f*)` — the
value half. Again only within the Legendre-type class. -/
theorem theorem_26_5_apply (hf : ConvexFn f) (hp : Proper f) (hcl : ClosedFn f)
    (hleg : LegendreType f) {v : Rn n} (hv : v ∈ interior (dom (conj (pairing n) f))) :
    f (gradient (fun w => (conj (pairing n) f w).toReal) v)
      = ((pairing n v (gradient (fun w => (conj (pairing n) f w).toReal) v)
          - (conj (pairing n) f v).toReal : ℝ) : EReal) := by
  have hgleg := hleg.conj hf hp hcl
  have h := corollary_26_4_1_eq (convexFn_conj (pairing n) f) hgleg.1 hv
  rwa [conj_conj_innerL hf hcl] at h

/-- **Rockafellar, Theorem 26.5**: the gradient mapping `∇f` is one-to-one from the open convex set
`C` onto the open convex set `C*`. -/
theorem theorem_26_5_bijOn (hf : ConvexFn f) (hp : Proper f) (hcl : ClosedFn f)
    (hleg : LegendreType f) :
    Set.BijOn (gradient fun w => (f w).toReal) (interior (dom f))
      (interior (dom (conj (pairing n) f))) :=
  bijOn_gradient_of_legendreType hf hp hcl hleg

/-- **Rockafellar, Theorem 26.5**: `∇f` is continuous on `C`. -/
theorem theorem_26_5_continuousOn (hf : ConvexFn f) (hp : Proper f) (hleg : LegendreType f) :
    ContinuousOn (gradient fun w => (f w).toReal) (interior (dom f)) :=
  continuousOn_gradient_interior_dom hf hp hleg.1

/-- **Rockafellar, Theorem 26.5**: `∇f` is continuous *in both directions*, the second half being
the continuity of `∇f*` on `C*`. -/
theorem theorem_26_5_continuousOn_conj (hf : ConvexFn f) (hp : Proper f) (hcl : ClosedFn f)
    (hleg : LegendreType f) :
    ContinuousOn (gradient fun w => (conj (pairing n) f w).toReal)
      (interior (dom (conj (pairing n) f))) :=
  continuousOn_gradient_interior_dom (convexFn_conj _ f) (proper_conj ⟨hf, hcl, hp⟩)
    (hleg.conj hf hp hcl).1

/-- **Rockafellar, Theorem 26.5**: `∇f* = (∇f)⁻¹`, one composite. -/
theorem theorem_26_5_gradient_conj (hf : ConvexFn f) (hp : Proper f) (hcl : ClosedFn f)
    (hleg : LegendreType f) {x : Rn n} (hx : x ∈ interior (dom f)) :
    gradient (fun w => (conj (pairing n) f w).toReal) (gradient (fun w => (f w).toReal) x) = x :=
  gradient_conj_gradient hf hp hcl hleg hx

/-- **Rockafellar, Theorem 26.5**: `∇f* = (∇f)⁻¹`, the other composite. -/
theorem theorem_26_5_gradient_gradient_conj (hf : ConvexFn f) (hp : Proper f) (hcl : ClosedFn f)
    (hleg : LegendreType f) {v : Rn n} (hv : v ∈ interior (dom (conj (pairing n) f))) :
    gradient (fun w => (f w).toReal) (gradient (fun w => (conj (pairing n) f w).toReal) v) = v :=
  gradient_gradient_conj hf hp hcl hleg hv

/-! ### Theorem 26.6 -/

/-- **Rockafellar, Theorem 26.6.** Let `f` be a (finite) differentiable convex function on `ℝⁿ`. In
order that `∇f` be a one-to-one mapping from `ℝⁿ` onto itself, it is necessary and sufficient that
`f` be strictly convex and co-finite. -/
theorem theorem_26_6 (hf : ConvexFn f) (hp : Proper f) (hdom : dom f = Set.univ)
    (hdiff : ∀ z : Rn n, DifferentiableAtFn f z) :
    Set.BijOn (gradient fun w => (f w).toReal) Set.univ Set.univ ↔
      (StrictConvexOnFn f Set.univ ∧ Cofinite f) := by
  have hcl : ClosedFn f := closedFn_of_dom_eq_univ hf hp hdom
  rw [bijOn_gradient_univ_iff hf hp hdom hdiff,
    ← cofinite_iff_dom_conj_eq_univ (B := pairing n) ⟨hf, hcl, hp⟩]

/-- **Rockafellar, Theorem 26.6**, the concluding clauses: when `∇f` is one-to-one from `ℝⁿ` onto
itself, `f*` is likewise a (finite) differentiable convex function on `ℝⁿ` which is strictly convex
and co-finite. -/
theorem theorem_26_6_conj (hf : ConvexFn f) (hp : Proper f) (hdom : dom f = Set.univ)
    (hdiff : ∀ z : Rn n, DifferentiableAtFn f z)
    (hbij : Set.BijOn (gradient fun w => (f w).toReal) Set.univ Set.univ) :
    dom (conj (pairing n) f) = Set.univ ∧
      (∀ z : Rn n, DifferentiableAtFn (conj (pairing n) f) z) ∧
      StrictConvexOnFn (conj (pairing n) f) Set.univ ∧ Cofinite (conj (pairing n) f) := by
  have hcl : ClosedFn f := closedFn_of_dom_eq_univ hf hp hdom
  obtain ⟨hdc, hdiffc, hscc⟩ := conj_finite_of_bijOn_gradient_univ hf hp hdom hdiff hbij
  refine ⟨hdc, hdiffc, hscc, ?_⟩
  have hcpc : ClosedProperConvexFn (conj (pairing n) f) :=
    ⟨convexFn_conj _ f, closedFn_conj, proper_conj ⟨hf, hcl, hp⟩⟩
  rw [cofinite_iff_dom_conj_eq_univ (B := pairing n) hcpc, conj_conj_innerL hf hcl]
  exact hdom

/-- **Rockafellar, Theorem 26.6**: `f*` is the same as the Legendre conjugate of `f`, i.e.
`f*(x*) = ⟨(∇f)⁻¹(x*), x*⟩ − f((∇f)⁻¹(x*))` for every `x*`. -/
theorem theorem_26_6_apply (hf : ConvexFn f) (hdiff : ∀ z : Rn n, DifferentiableAtFn f z)
    (x : Rn n) :
    conj (pairing n) f (gradient (fun w => (f w).toReal) x)
      = ((pairing n x (gradient (fun w => (f w).toReal) x) - (f x).toReal : ℝ) : EReal) :=
  theorem_26_4_eq hf (hdiff x).hasGradientAtFn_gradient

/-! ### Lemma 26.7 -/

/-- **Rockafellar, Lemma 26.7.** Let `f` be a differentiable convex function on `ℝⁿ`. In order that
`f` be co-finite, it is necessary and sufficient that `|∇f(xᵢ)| → +∞` for every sequence with
`|xᵢ| → +∞`. -/
theorem lemma_26_7 (hf : ConvexFn f) (hp : Proper f) (hdom : dom f = Set.univ)
    (hdiff : ∀ z : Rn n, DifferentiableAtFn f z) :
    Cofinite f ↔ ∀ xs : ℕ → Rn n, Tendsto (fun i => ‖xs i‖) atTop atTop →
      Tendsto (fun i => ‖gradient (fun w => (f w).toReal) (xs i)‖) atTop atTop :=
  cofinite_iff_forall_tendsto_norm_gradient_atTop hf hp hdom hdiff

end Rockafellar
