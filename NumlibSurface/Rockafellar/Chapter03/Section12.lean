import Numlib.Analysis.Convex.Duality.GaugeLike
import Numlib.Analysis.Convex.Duality.Ops
import NumlibSurface.Rockafellar.Chapter02.Section07

/-!
# Rockafellar §12: conjugates of convex functions

Surface file for R. Tyrrell Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §12:
the conjugacy correspondence `f ↦ f*`, its involutivity on closed proper convex functions, and the
elementary table of operations under which the conjugate transforms by a change of variable.

All 9 numbered results of §12 are formalized.

Rockafellar prints **Theorem 12.4** with no proof at all. The argument here avoids the
symmetrisation `f x = g (abs x)` that the surrounding prose suggests, and with it the question of
whether `x ↦ g (abs x)` is convex. Writing `K` for the non-negative orthant, the one fact that
makes the truncation `g⁺ = convexRestrict K f*` harmless is `convexConj_posPart`: `f* (y⁺) = f* y`,
where `y⁺` is the componentwise positive part. The supremum defining `f**` may then be taken over
`K` alone, and Fenchel–Moreau finishes.

## The section's definitions

* **The conjugate `f*`** is `convexConj (pairing n) f`, the backbone's `convexConj` against the
  Euclidean self-pairing, defined by the book's own supremum for an *arbitrary* `f : ℝⁿ → [-∞, +∞]`.
* **Fenchel's inequality** is `fenchel_inequality`, stated for a proper `f` exactly as the book
  states it; the hypothesis is not removable.
* **Symmetry with respect to a set `G` of orthogonal transformations** is transcribed literally as
  `SymmetricWrt`, with `IsOrthogonalEquiv` for "orthogonal linear transformation of `ℝⁿ` onto
  itself" — a linear bijection preserving the inner product.
* **The monotone conjugate `g⁺`** is `monotoneConjOrthant`, acting on `MonotoneOrthantFn`: `+∞`
  off the non-negative orthant, non-decreasing for the componentwise order, convex, closed, and
  finite at the origin. `monotoneConjOrthant_apply` is the book's formula
  `g⁺(z*) = sup {⟨z, z*⟩ - g z | z ≥ 0}`.
* **`corollary_12_2_1`** is a `def`: the involution of the closed proper convex functions that
  Corollary 12.2.1 asserts, packaged as an `Equiv`.

## Main results

* `theorem_12_1`, `corollary_12_1_1`, `corollary_12_1_2` — a closed convex function is the
  pointwise supremum of the affine functions below it.
* `theorem_12_2_convex`, `theorem_12_2_closed`, `theorem_12_2_proper`, `theorem_12_2_conj_clFn`,
  `theorem_12_2_biconj` — the conjugate of a convex function is closed and convex, is proper
  exactly when `f` is, is unchanged by closure, and `f** = cl f` (Fenchel–Moreau).
* `corollary_12_2_1`, `corollary_12_2_2` — conjugacy is a symmetric one-to-one correspondence on
  the closed proper convex functions, and the supremum defining `f*` may be restricted to
  `ri (dom f)`.
* `fenchel_inequality` — `⟨x, x*⟩ ≤ f x + f* x*` for proper convex `f`.
* `theorem_12_3`, `corollary_12_3_1` — the change-of-variable table, and the invariance of
  conjugacy under a group of orthogonal transformations.
* `theorem_12_4_mem`, `theorem_12_4_involutive` — the monotone conjugate is again a non-decreasing
  closed convex function on the orthant, and the operation is involutive.
-/

namespace Rockafellar

open ConvexAnalysis

variable {n : ℕ} {f : Rn n → EReal}

/-! ### Theorem 12.1 -/

/-- **Theorem 12.1.** A closed convex function `f` on `ℝⁿ` is the pointwise supremum
of the collection of all affine functions `h` such that `h ≤ f`.

An affine function on `ℝⁿ` is `x ↦ ⟨x, b⟩ - β`, indexed here by the pair `(b, β)`; that every affine
function has this form is the identification of `ℝⁿ` with its own dual that `pairing n` makes. -/
theorem theorem_12_1 (hf : ConvexFn f) (hc : ClosedConvex f) :
    f = fun x => ⨆ p ∈ {p : Rn n × ℝ | affineFn (pairing n) p.1 p.2 ≤ f},
      affineFn (pairing n) p.1 p.2 x :=
  eq_biSup_affineFn hf hc

/-- **Corollary 12.1.1.** If `f` is any function from `ℝⁿ` to `[-∞, ∞]`, then `cl (conv f)` is the
pointwise supremum of the collection of all affine functions on `ℝⁿ` majorized by `f`. The affine
minorants of `cl (conv f)` are exactly those of `f`. -/
theorem corollary_12_1_1 (f : Rn n → EReal) :
    convexCl (convHullFn f) = fun x => ⨆ p ∈ {p : Rn n × ℝ | affineFn (pairing n) p.1 p.2 ≤ f},
      affineFn (pairing n) p.1 p.2 x := by
  have hset : {p : Rn n × ℝ | affineFn (pairing n) p.1 p.2 ≤ convexCl (convHullFn f)}
      = {p : Rn n × ℝ | affineFn (pairing n) p.1 p.2 ≤ f} := by
    ext p
    simp only [Set.mem_ofPred_eq, ← convexConj_le_coe_iff, convexConj_convexCl,
        convexConj_convHullFn]
  rw [eq_biSup_affineFn (B := pairing n) (convexFn_convexCl (convexFn_convHullFn f))
    (closedConvex_convexCl _), hset]

/-- **Corollary 12.1.2.** Given any proper convex function `f` on `ℝⁿ`, there exists some `b ∈ ℝⁿ`
and `β ∈ ℝ` such that `f x ≥ ⟨x, b⟩ - β` for every `x`. The book states this corollary with no proof
of its own. -/
theorem corollary_12_1_2 (hf : ConvexFn f) (hp : ProperConvex f) :
    ∃ (b : Rn n) (β : ℝ), ∀ x, ((inner ℝ x b : ℝ) : EReal) - (β : EReal) ≤ f x := by
  have hcl : ClosedProperConvexFn (convexCl f) :=
    ⟨convexFn_convexCl hf, closedConvex_convexCl f, hf.properConvex_convexCl hp⟩
  obtain ⟨⟨b, hb⟩, -⟩ := properConvex_convexConj (B := pairing n) hcl
  rw [mem_convexDom, convexConj_convexCl] at hb
  obtain ⟨β, hβ, -⟩ := EReal.lt_iff_exists_real_btwn.1 hb
  exact ⟨b, β, convexConj_le_coe_iff.1 hβ.le⟩

/-! ### Theorem 12.2: Fenchel–Moreau -/

/-- **Theorem 12.2**, first clause: the conjugate of a convex function is convex.

Convexity of `f` is not needed — `f*` is a pointwise supremum of affine functions whatever `f` is —
so the hypothesis of the book's statement is dropped. -/
theorem theorem_12_2_convex (f : Rn n → EReal) : ConvexFn (convexConj (pairing n) f) :=
  convexFn_convexConj _ f

/-- **Theorem 12.2**, second clause: the conjugate of a convex function is closed. Again no
hypothesis on `f` is needed. -/
theorem theorem_12_2_closed (f : Rn n → EReal) : ClosedConvex (convexConj (pairing n) f) :=
  closedConvex_convexConj

/-- **Theorem 12.2**, third clause: `f*` is proper if and only if `f` is.

Strengthens `properConvex_convexConj_iff`, which asks for `f` closed as well as convex: on `ℝⁿ` the
closure of a proper convex function is again proper (Theorem 7.4), so the hypothesis can be
discharged, and `convexConj_convexCl` transports the conclusion back. -/
theorem theorem_12_2_proper
    (hf : ConvexFn f) : ProperConvex (convexConj (pairing n) f) ↔ ProperConvex f := by
  refine ⟨properConvex_of_properConvex_convexConj, fun hp => ?_⟩
  have h := properConvex_convexConj (B := pairing n)
    ⟨convexFn_convexCl hf, closedConvex_convexCl f, hf.properConvex_convexCl hp⟩
  rwa [convexConj_convexCl] at h

/-- **Theorem 12.2**, fourth clause: `(cl f)* = f*`. Convexity is not needed. -/
theorem theorem_12_2_conj_clFn (f : Rn n → EReal) :
    convexConj (pairing n) (convexCl f) = convexConj (pairing n) f :=
  convexConj_convexCl f

/-- **Theorem 12.2**, the Fenchel–Moreau theorem: `f** = cl f` for convex `f`.

On `ℝⁿ` the two sides of the pairing coincide, so `f**` is literally `convexConj (pairing n)`
applied twice; `flip_pairing` is what removes the backbone's `B.flip`. -/
theorem theorem_12_2_biconj (hf : ConvexFn f) :
    convexConj (pairing n) (convexConj (pairing n) f) = convexCl f := by
  have h := convexBiconj_eq_convexCl (B := pairing n) hf
  rwa [convexBiconj, flip_pairing] at h

/-- **Corollary 12.2.1.** The conjugacy operation `f ↦ f*` induces a symmetric
one-to-one correspondence in the class of all closed proper convex functions on `ℝⁿ`.

"Symmetric" is `corollary_12_2_1_symm_apply` below: the inverse of the correspondence is the
correspondence itself. -/
noncomputable def corollary_12_2_1 (n : ℕ) :
    {f : Rn n → EReal // ClosedProperConvexFn f} ≃ {g : Rn n → EReal // ClosedProperConvexFn g} :=
  convexConjEquiv (pairing n)

/-- The correspondence of Corollary 12.2.1 sends `f` to its conjugate `f*`. -/
@[simp] theorem corollary_12_2_1_apply (f : {f : Rn n → EReal // ClosedProperConvexFn f}) :
    ((corollary_12_2_1 n f : {g : Rn n → EReal // ClosedProperConvexFn g}) : Rn n → EReal)
      = convexConj (pairing n) f := rfl

/-- The correspondence of Corollary 12.2.1 is **symmetric**: its inverse is itself. -/
@[simp] theorem corollary_12_2_1_symm_apply
    (g : {g : Rn n → EReal // ClosedProperConvexFn g}) :
    (((corollary_12_2_1 n).symm g : {f : Rn n → EReal // ClosedProperConvexFn f}) : Rn n → EReal)
      = convexConj (pairing n) g := by
  simp [corollary_12_2_1, convexConjEquiv]

/-- **Corollary 12.2.2.** For any convex function `f` on `ℝⁿ`,
`f* x* = sup {⟨x, x*⟩ - f x ∣ x ∈ ri (dom f)}`. -/
theorem corollary_12_2_2 (hf : ConvexFn f) (y : Rn n) :
    convexConj (pairing n) f y = ⨆ x ∈ ri (convexDom f), ((inner ℝ x y : ℝ) : EReal) - f x := by
  have hdomconv : Convex ℝ (convexDom f) := hf.convex_convexDom
  have hsub : ri (convexDom f) ⊆ convexDom f := intrinsicInterior_subset
  have hg : ConvexFn (convexRestrict (ri (convexDom f)) f) := hf.convexRestrict hdomconv.relint
  have hdomg : convexDom (convexRestrict (ri (convexDom f)) f) = ri (convexDom f) := by
    ext x
    by_cases hx : x ∈ ri (convexDom f)
    · simp only [mem_convexDom, convexRestrict_of_mem hx]
      exact ⟨fun _ => hx, fun _ => hsub hx⟩
    · simp [hx]
  have hri : ri (convexDom (convexRestrict (ri (convexDom f)) f)) = ri (convexDom f) := by
    rw [hdomg, hdomconv.relint_relint]
  have hcl : convexCl (convexRestrict (ri (convexDom f)) f) = convexCl f :=
    corollary_7_3_4 hg hf hri fun x hx => convexRestrict_of_mem (hri ▸ hx)
  have hconj : convexConj (pairing n) (convexRestrict (ri (convexDom f)) f)
      = convexConj (pairing n) f := by
    rw [← convexConj_convexCl (B := pairing n) (convexRestrict (ri (convexDom f)) f), hcl,
        convexConj_convexCl]
  rw [← hconj, convexConj_apply]
  refine le_antisymm (iSup_le fun x => ?_) (iSup₂_le fun x hx => ?_)
  · by_cases hx : x ∈ ri (convexDom f)
    · rw [convexRestrict_of_mem hx]
      exact le_iSup₂ (f := fun x (_ : x ∈ ri (convexDom f)) =>
        ((inner ℝ x y : ℝ) : EReal) - f x) x hx
    · rw [convexRestrict_of_notMem hx]
      simp
  · rw [← convexRestrict_of_mem (f := f) hx]
    exact le_iSup (fun x : Rn n => ((pairing n x y : ℝ) : EReal)
      - convexRestrict (ri (convexDom f)) f x) x

/-! ### Fenchel's inequality -/

/-- **Fenchel's inequality** (Rockafellar, §12, p. 105): `⟨x, x*⟩ ≤ f x + f* x*` for any proper
convex function `f` and its conjugate.

Properness is the book's hypothesis and it is not removable: for `f ≡ +∞` the right-hand side is
`⊤ + ⊥ = ⊥`. -/
theorem fenchel_inequality (hp : ProperConvex f) (x y : Rn n) :
    ((inner ℝ x y : ℝ) : EReal) ≤ f x + convexConj (pairing n) f y :=
  hp.le_add_convexConj (B := pairing n) x y

/-! ### Theorem 12.3 -/

/-- **Theorem 12.3.** Let `h` be a convex function on `ℝⁿ` and
`f x = h (A (x - a)) + ⟨x, a*⟩ + α` with `A` a one-to-one linear transformation from `ℝⁿ` onto
`ℝⁿ`. Then `f* x* = h* (A*⁻¹ (x* - a*)) + ⟨x*, a⟩ + α*`, where `α* = -α - ⟨a, a*⟩`.

The book writes `A*⁻¹`; the adjoint is taken as data, so `A'` and `⟨A x, z⟩ = ⟨x, A' z⟩` are
hypotheses — over `ℝⁿ` the adjoint exists and is unique, but it must still be supplied. No
convexity of `h` is needed. -/
theorem theorem_12_3 (A A' : Rn n ≃ₗ[ℝ] Rn n)
    (hA : ∀ x z : Rn n, (inner ℝ (A x) z : ℝ) = inner ℝ x (A' z))
    (h : Rn n → EReal) (a b : Rn n) (α : ℝ) (y : Rn n) :
    convexConj (pairing n) (fun x => h (A (x - a)) + ((inner ℝ x b : ℝ) : EReal) + (α : EReal)) y
      = convexConj (pairing n) h (A'.symm (y - b)) + ((inner ℝ a y : ℝ) : EReal)
        + ((-α - inner ℝ a b : ℝ) : EReal) :=
  convexConj_comp_affine (B := pairing n) (B' := pairing n) A A' (fun x z => hA x z) h a b α y

/-! ### Corollary 12.3.1 -/

/-- **An orthogonal linear transformation of `ℝⁿ` onto itself** (Rockafellar, §12, p. 109): a
linear bijection preserving the inner product. The bridge to the backbone's `IsAdjointPair` is
`orthogonalEquiv_adjoint` below, which is Rockafellar's `A*⁻¹ = A`. -/
def IsOrthogonalEquiv (A : Rn n ≃ₗ[ℝ] Rn n) : Prop :=
  ∀ x y : Rn n, (inner ℝ (A x) (A y) : ℝ) = inner ℝ x y

/-- The bridge for `IsOrthogonalEquiv`: for an orthogonal `A` the adjoint `A*` is `A⁻¹`. -/
theorem orthogonalEquiv_adjoint {A : Rn n ≃ₗ[ℝ] Rn n} (hA : IsOrthogonalEquiv A) (x z : Rn n) :
    (inner ℝ (A x) z : ℝ) = inner ℝ x (A.symm z) := by
  rw [← hA x (A.symm z), LinearEquiv.apply_symm_apply]

/-- **Symmetry with respect to a set `G` of transformations** (Rockafellar, §12, p. 109):
`f (A x) = f x` for every `x` and every `A ∈ G`. -/
def SymmetricWrt (f : Rn n → EReal) (G : Set (Rn n ≃ₗ[ℝ] Rn n)) : Prop :=
  ∀ A ∈ G, ∀ x, f (A x) = f x

/-- The half of Corollary 12.3.1 that needs no closedness: if `f` is symmetric under the
orthogonal transformation `A`, so is `f*`. This is Theorem 12.3 with `h = f`, `a = 0 = a*`,
`α = 0`, together with `A*⁻¹ = A`. -/
theorem convexConj_comp_orthogonal {A : Rn n ≃ₗ[ℝ] Rn n} (hA : IsOrthogonalEquiv A)
    (hfA : ∀ x, f (A x) = f x) (y : Rn n) :
    convexConj (pairing n) f (A y) = convexConj (pairing n) f y := by
  have h := convexConj_comp_linearEquiv (B := pairing n) (B' := pairing n) A A.symm
    (orthogonalEquiv_adjoint hA) f y
  rw [LinearEquiv.symm_symm] at h
  rw [← h]
  exact congrArg (fun g => convexConj (pairing n) g y) (funext hfA)

/-- **Corollary 12.3.1.** A closed convex function `f` is symmetric with respect to a
given set `G` of orthogonal linear transformations if and only if `f*` is symmetric with respect
to `G`. -/
theorem corollary_12_3_1 (hf : ConvexFn f) (hc : ClosedConvex f) {G : Set (Rn n ≃ₗ[ℝ] Rn n)}
    (hG : ∀ A ∈ G, IsOrthogonalEquiv A) :
    SymmetricWrt f G ↔ SymmetricWrt (convexConj (pairing n) f) G := by
  refine ⟨fun h A hA => convexConj_comp_orthogonal (hG A hA) (h A hA), fun h A hA => ?_⟩
  have hb : convexConj (pairing n) (convexConj (pairing n) f) = f := by
    rw [theorem_12_2_biconj hf, hc]
  have hsym := convexConj_comp_orthogonal (f := convexConj (pairing n) f) (hG A hA) (h A hA)
  rw [hb] at hsym
  exact hsym

/-! ### Theorem 12.4: monotone conjugacy on the non-negative orthant -/

section MonotoneConjugacy

/-- The **non-negative orthant** of `ℝⁿ` (Rockafellar, §12, p. 111): the set `{z | z ≥ 0}` for the
componentwise order. -/
def nonnegOrthant (n : ℕ) : Set (Rn n) := {z : Rn n | ∀ j, 0 ≤ z j}

theorem mem_nonnegOrthant {z : Rn n} : z ∈ nonnegOrthant n ↔ ∀ j, 0 ≤ z j := Iff.rfl

/-- The inner product of `ℝⁿ` in coordinates, which is what the componentwise order interacts
with. -/
theorem inner_rn (x y : Rn n) : (inner ℝ x y : ℝ) = ∑ j, x j * y j := by
  simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]

theorem convex_nonnegOrthant (n : ℕ) : Convex ℝ (nonnegOrthant n) := by
  intro x hx y hy a b ha hb _ j
  exact add_nonneg (mul_nonneg ha (hx j)) (mul_nonneg hb (hy j))

theorem isClosed_nonnegOrthant (n : ℕ) : IsClosed (nonnegOrthant n) := by
  have hset : nonnegOrthant n = ⋂ j, (fun z : Rn n => z j) ⁻¹' Set.Ici (0 : ℝ) := by
    ext z; simp [nonnegOrthant]
  rw [hset]
  exact isClosed_iInter fun j =>
    isClosed_Ici.preimage (PiLp.continuous_apply (p := 2) (fun _ : Fin n => ℝ) j)

theorem zero_mem_nonnegOrthant (n : ℕ) : (0 : Rn n) ∈ nonnegOrthant n := fun _ => le_rfl

/-- The componentwise **positive part** of `y`, which is `y` itself on the orthant. -/
noncomputable def posPart (y : Rn n) : Rn n := WithLp.toLp 2 fun j => max (y j) 0

@[simp] theorem posPart_apply (y : Rn n) (j : Fin n) : posPart y j = max (y j) 0 := rfl

theorem posPart_mem (y : Rn n) : posPart y ∈ nonnegOrthant n := fun _ => le_max_right _ _

theorem le_posPart (y : Rn n) (j : Fin n) : y j ≤ posPart y j := le_max_left _ _

theorem posPart_of_mem {y : Rn n} (hy : y ∈ nonnegOrthant n) : posPart y = y := by
  ext j; exact max_eq_left (hy j)

/-- `z` with the coordinates on which `y` is negative set to zero. It is the competitor that makes
the truncation in `monotoneConjOrthant` harmless. -/
noncomputable def maskNonneg (y z : Rn n) : Rn n :=
  WithLp.toLp 2 fun j => if 0 ≤ y j then z j else 0

@[simp] theorem maskNonneg_apply (y z : Rn n) (j : Fin n) :
    maskNonneg y z j = if 0 ≤ y j then z j else 0 := rfl

theorem maskNonneg_mem {z : Rn n} (y : Rn n) (hz : z ∈ nonnegOrthant n) :
    maskNonneg y z ∈ nonnegOrthant n := by
  intro j
  rw [maskNonneg_apply]
  split
  · exact hz j
  · exact le_rfl

theorem maskNonneg_le {z : Rn n} (y : Rn n) (hz : z ∈ nonnegOrthant n) (j : Fin n) :
    maskNonneg y z j ≤ z j := by
  rw [maskNonneg_apply]
  split
  · exact le_rfl
  · exact hz j

theorem inner_maskNonneg (y z : Rn n) :
    (inner ℝ (maskNonneg y z) y : ℝ) = inner ℝ z (posPart y) := by
  rw [inner_rn, inner_rn]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [maskNonneg_apply, posPart_apply]
  split_ifs with hj
  · rw [max_eq_left hj]
  · rw [max_eq_right (le_of_not_ge hj), zero_mul, mul_zero]

theorem inner_le_inner_posPart {z : Rn n} (hz : z ∈ nonnegOrthant n) (y : Rn n) :
    (inner ℝ y z : ℝ) ≤ inner ℝ (posPart y) z := by
  rw [inner_rn, inner_rn]
  exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (le_posPart y j) (hz j)

/-- **A non-decreasing closed convex function on the non-negative orthant**, in the encoding the
book's §4 convention prescribes: a function on all of `ℝⁿ` that is `+∞` off the orthant.
Rockafellar's hypotheses on `g` (p. 111) are exactly these. -/
structure MonotoneOrthantFn (f : Rn n → EReal) : Prop where
  /-- `f` is `+∞` off the non-negative orthant; the book's "function on the orthant". -/
  top_of_notMem : ∀ ⦃z : Rn n⦄, z ∉ nonnegOrthant n → f z = ⊤
  /-- `f z ≤ f z'` whenever `0 ≤ z ≤ z'`: the book's *non-decreasing*. -/
  mono : ∀ ⦃z z' : Rn n⦄, z ∈ nonnegOrthant n → (∀ j, z j ≤ z' j) → f z ≤ f z'
  /-- `f` is convex. -/
  convex : ConvexFn f
  /-- `f` is lower semicontinuous, i.e. closed. -/
  closed : ClosedConvex f
  /-- `f 0` is finite: not `+∞` … -/
  zero_ne_top : f 0 ≠ ⊤
  /-- … and not `-∞`. -/
  zero_ne_bot : f 0 ≠ ⊥

theorem MonotoneOrthantFn.zero_le {f : Rn n → EReal} (hf : MonotoneOrthantFn f)
    {z : Rn n} (hz : z ∈ nonnegOrthant n) : f 0 ≤ f z :=
  hf.mono (zero_mem_nonnegOrthant n) fun j => hz j

theorem MonotoneOrthantFn.proper {f : Rn n → EReal}
    (hf : MonotoneOrthantFn f) : ProperConvex f := by
  refine ⟨⟨0, lt_of_le_of_ne le_top hf.zero_ne_top⟩, fun z hz => ?_⟩
  by_cases hzm : z ∈ nonnegOrthant n
  · exact hf.zero_ne_bot (le_bot_iff.1 (hz ▸ hf.zero_le hzm))
  · exact absurd (hf.top_of_notMem hzm) (hz ▸ bot_ne_top)

/-- The **monotone conjugate** `g⁺` of Rockafellar's p. 111: the conjugate, truncated back to the
non-negative orthant so that the correspondence is one between functions on the orthant. -/
noncomputable def monotoneConjOrthant (f : Rn n → EReal) : Rn n → EReal :=
  convexRestrict (nonnegOrthant n) (convexConj (pairing n) f)

/-- Rockafellar's formula `g⁺(z*) = sup {⟨z, z*⟩ - g z ∣ z ≥ 0}` (p. 111), on the orthant. -/
theorem monotoneConjOrthant_apply {f : Rn n → EReal}
    (htop : ∀ ⦃z : Rn n⦄, z ∉ nonnegOrthant n → f z = ⊤) {y : Rn n} (hy : y ∈ nonnegOrthant n) :
    monotoneConjOrthant f y = ⨆ z ∈ nonnegOrthant n, ((inner ℝ z y : ℝ) : EReal) - f z := by
  rw [monotoneConjOrthant, convexRestrict_of_mem hy, convexConj_apply]
  refine le_antisymm (iSup_le fun z => ?_) (iSup₂_le fun z hz => ?_)
  · by_cases hz : z ∈ nonnegOrthant n
    · exact le_iSup₂ (f := fun z (_ : z ∈ nonnegOrthant n) =>
        ((inner ℝ z y : ℝ) : EReal) - f z) z hz
    · rw [htop hz]; simp
  · exact le_iSup (fun z : Rn n => ((pairing n z y : ℝ) : EReal) - f z) z

theorem monotoneConjOrthant_of_notMem (f : Rn n → EReal) {y : Rn n}
    (hy : y ∉ nonnegOrthant n) : monotoneConjOrthant f y = ⊤ :=
  convexRestrict_of_notMem hy

theorem convexConj_le_monotoneConjOrthant (f : Rn n → EReal) (y : Rn n) :
    convexConj (pairing n) f y ≤ monotoneConjOrthant f y := by
  by_cases hy : y ∈ nonnegOrthant n
  · rw [monotoneConjOrthant, convexRestrict_of_mem hy]
  · rw [monotoneConjOrthant_of_notMem f hy]; exact le_top

/-- The conjugate of an orthant function is monotone in the dual variable. -/
theorem convexConj_mono_of_top_of_notMem {f : Rn n → EReal}
    (htop : ∀ ⦃z : Rn n⦄, z ∉ nonnegOrthant n → f z = ⊤) {y y' : Rn n} (h : ∀ j, y j ≤ y' j) :
    convexConj (pairing n) f y ≤ convexConj (pairing n) f y' := by
  rw [convexConj_apply, convexConj_apply]
  refine iSup_le fun z => ?_
  by_cases hz : z ∈ nonnegOrthant n
  · refine le_trans ?_ (le_iSup (fun z : Rn n => ((pairing n z y' : ℝ) : EReal) - f z) z)
    refine EReal.sub_le_sub ?_ le_rfl
    rw [EReal.coe_le_coe_iff]
    change (inner ℝ z y : ℝ) ≤ inner ℝ z y'
    rw [inner_rn, inner_rn]
    exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (h j) (hz j)
  · rw [htop hz]; simp

/-- **The one fact that makes the truncation harmless**: `f*` does not distinguish `y` from its
positive part. See the module docstring. -/
theorem convexConj_posPart {f : Rn n → EReal} (hf : MonotoneOrthantFn f) (y : Rn n) :
    convexConj (pairing n) f (posPart y) = convexConj (pairing n) f y := by
  refine le_antisymm ?_ (convexConj_mono_of_top_of_notMem hf.top_of_notMem (le_posPart y))
  rw [convexConj_apply, convexConj_apply]
  refine iSup_le fun z => ?_
  by_cases hz : z ∈ nonnegOrthant n
  · refine le_trans ?_
      (le_iSup (fun w : Rn n => ((pairing n w y : ℝ) : EReal) - f w) (maskNonneg y z))
    refine EReal.sub_le_sub (le_of_eq ?_)
      (hf.mono (maskNonneg_mem y hz) (maskNonneg_le y hz))
    rw [EReal.coe_eq_coe_iff]
    exact (inner_maskNonneg y z).symm
  · rw [hf.top_of_notMem hz]; simp

/-- **Theorem 12.4**, first half: the monotone conjugate `g⁺` of a non-decreasing
lower semicontinuous convex function on the non-negative orthant, finite at the origin, is another
such function.

The book states Theorem 12.4 with **no proof at all**. Note `g⁺(0) = -g(0)`, because `g` attains
its infimum over the orthant at the origin. -/
theorem theorem_12_4_mem {f : Rn n → EReal} (hf : MonotoneOrthantFn f) :
    MonotoneOrthantFn (monotoneConjOrthant f) := by
  have hzero : monotoneConjOrthant f 0 = -f 0 := by
    rw [monotoneConjOrthant, convexRestrict_of_mem (zero_mem_nonnegOrthant n), convexConj_apply]
    refine le_antisymm (iSup_le fun z => ?_) ?_
    · by_cases hz : z ∈ nonnegOrthant n
      · have h0 : ((pairing n z 0 : ℝ) : EReal) = 0 := by
          rw [map_zero, EReal.coe_zero]
        rw [h0, zero_sub, EReal.neg_le_neg_iff]
        exact hf.zero_le hz
      · rw [hf.top_of_notMem hz]; simp
    · refine le_trans (le_of_eq ?_)
        (le_iSup (fun z : Rn n => ((pairing n z 0 : ℝ) : EReal) - f z) 0)
      rw [map_zero, EReal.coe_zero, zero_sub]
  refine ⟨fun y hy => monotoneConjOrthant_of_notMem f hy, ?_,
    (convexFn_convexConj (pairing n) f).convexRestrict (convex_nonnegOrthant n),
    (closedConvex_convexConj (B := pairing n) (f := f)).convexRestrict
        ?_ (isClosed_nonnegOrthant n),
    ?_, ?_⟩
  · intro y y' hy hyy'
    have hy' : y' ∈ nonnegOrthant n := fun j => le_trans (hy j) (hyy' j)
    rw [monotoneConjOrthant, convexRestrict_of_mem hy, convexRestrict_of_mem hy']
    exact convexConj_mono_of_top_of_notMem hf.top_of_notMem hyy'
  · exact fun y => convexConj_ne_bot hf.proper.convexDom_nonempty y
  · rw [hzero]
    exact fun h => hf.zero_ne_bot (EReal.neg_eq_top_iff.1 h)
  · rw [hzero]
    exact fun h => hf.zero_ne_top (EReal.neg_eq_bot_iff.1 h)

/-- **Theorem 12.4**, second half: the monotone conjugate of `g⁺` is in turn `g`. The book states
Theorem 12.4 with **no proof at all**; see the module docstring. -/
theorem theorem_12_4_involutive {f : Rn n → EReal} (hf : MonotoneOrthantFn f) :
    monotoneConjOrthant (monotoneConjOrthant f) = f := by
  have hbi : convexConj (pairing n) (convexConj (pairing n) f) = f := by
    rw [theorem_12_2_biconj hf.convex, hf.closed]
  funext z
  by_cases hz : z ∈ nonnegOrthant n
  · have hLHS : convexConj (pairing n) (convexConj (pairing n) f) z
        = ⨆ y : Rn n, ((pairing n y z : ℝ) : EReal) - convexConj (pairing n) f y :=
            convexConj_apply _ _ _
    have hRHS : convexConj (pairing n) (monotoneConjOrthant f) z
        = ⨆ w : Rn n, ((pairing n w z : ℝ) : EReal) - monotoneConjOrthant f w :=
            convexConj_apply _ _ _
    have hge : convexConj (pairing n) (convexConj (pairing n) f) z
        ≤ convexConj (pairing n) (monotoneConjOrthant f) z := by
      rw [hLHS, hRHS]
      refine iSup_le fun y => ?_
      refine le_trans ?_
        (le_iSup (fun w : Rn n => ((pairing n w z : ℝ) : EReal) - monotoneConjOrthant f w)
          (posPart y))
      refine EReal.sub_le_sub ?_ (le_of_eq ?_)
      · rw [EReal.coe_le_coe_iff]
        exact inner_le_inner_posPart hz y
      · rw [monotoneConjOrthant, convexRestrict_of_mem (posPart_mem y), convexConj_posPart hf]
    have hle := convexConj_antitone (pairing n) (convexConj_le_monotoneConjOrthant f) z
    rw [hbi] at hge hle
    rw [monotoneConjOrthant, convexRestrict_of_mem hz]
    exact le_antisymm hle hge
  · rw [monotoneConjOrthant_of_notMem _ hz, (hf.top_of_notMem hz).symm]

end MonotoneConjugacy

end Rockafellar
