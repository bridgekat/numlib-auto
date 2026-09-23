import Numlib.Analysis.Convex.Duality.Exact
import Numlib.Analysis.Convex.Subdifferential.Defs

/-!
# Subdifferential calculus

How `∂` interacts with sums and with linear maps. Both rules have the same shape: one inclusion is
unconditional — a subgradient of each piece assembles into a subgradient of the whole — and the
reverse inclusion, the useful one, needs exactly the constraint qualification that makes the
corresponding conjugacy rule exact. Both are therefore stated against the `IsExactSum` and
`IsExactImage` interfaces; the classical `ri` versions of the two rules are these composed with the
`of_relint` constructors.

## Main results

* `IsExactSum.subdifferential_add`, `IsExactFinsetSum.subdifferential_finsetSum` —
  `∂(∑ fᵢ) = ∑ ∂fᵢ`, for two summands and for `m` of them ([rockafellar1970convex] Theorem 23.8).
* `IsExactImage.subdifferential_compLin` — `∂(g A) x = A' (∂g (A x))`
  ([rockafellar1970convex] Theorem 23.9).
* `subdifferential_coe_mul`, `subdifferential_coe_affineMap` — `∂(cf) = c ∂f` for `c > 0`, and for
  *arbitrary* `c` when `f` is affine.
* `IsExactSum.normalCone_inter` — the normal cone to an intersection, as a sum of normal cones.
* `subdifferential_add_normalCone_convexDom_subset`,
  `normalCone_convexDom_eq_zero_of_subdifferential_eq_singleton` — the normal cone to `dom f`, and
  what a *unique* subgradient does to it.

## Implementation notes

Everything reduces to the conjugate characterisation `y ∈ ∂f x ↔ f x + f* y ≤ ⟨x, y⟩`,
written so that no `∞ - ∞` can arise; no epigraph, directional derivative or separating hyperplane
appears in any proof here. The sum rule additionally needs the `EReal` fact that two slack
inequalities whose sum is tight must each be tight, and that is where the properness carried by
`IsExactSum` is spent. Its `m`-ary form is proved for the whole family in one pass, because the
binary rule does not iterate: `EReal` has no subtraction to peel a summand off with.

## References

* [rockafellar1970convex] §23.
-/

open Pointwise

namespace ConvexAnalysis

/-! ### Sums -/

section Add

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
variable {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f g : E → EReal}

/-- **The unconditional inclusion**: a subgradient of `f` plus a subgradient of `g` is a
subgradient of `f + g`. The two subgradient inequalities simply add. -/
theorem subdifferential_add_subset (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f g : E → EReal) (x : E) :
    subdifferential B f x + subdifferential B g x ⊆ subdifferential B (f + g) x := by
  rintro _ ⟨y₁, hy₁, y₂, hy₂, rfl⟩ z
  have h₁ := hy₁ z
  have h₂ := hy₂ z
  rw [Pi.add_apply, Pi.add_apply, map_add, EReal.coe_add, add_add_add_comm]
  exact add_le_add h₁ h₂

/-- `∂(f + g) x = ∂f x + ∂g x` whenever the sum is exact. Exactness splits
`y = y₁ + y₂` with `f* y₁ + g* y₂ ≤ (f+g)* y`, and tightness of Fenchel's inequality for `f + g`
then leaves the two inequalities for `f` at `y₁` and `g` at `y₂` no room to be strict. -/
theorem IsExactSum.subdifferential_add (h : IsExactSum B f g) (x : E) :
    subdifferential B (f + g) x = subdifferential B f x + subdifferential B g x := by
  refine Set.Subset.antisymm (fun y hy => ?_) (subdifferential_add_subset B f g x)
  obtain ⟨y₁, y₂, rfl, hle⟩ := h.exact_le y
  have hy' := mem_subdifferential_iff_add_convexConj_le.1 hy
  rw [Pi.add_apply] at hy'
  have hkey : (f x + convexConj B f y₁) + (g x + convexConj B g y₂)
      ≤ ((B x y₁ + B x y₂ : ℝ) : EReal) := by
    calc (f x + convexConj B f y₁) + (g x + convexConj B g y₂)
        = (f x + g x) + (convexConj B f y₁ + convexConj B g y₂) := (add_add_add_comm _ _ _ _).symm
      _ ≤ (f x + g x) + convexConj B (f + g) (y₁ + y₂) := add_le_add le_rfl hle
      _ ≤ ((B x (y₁ + y₂) : ℝ) : EReal) := hy'
      _ = ((B x y₁ + B x y₂ : ℝ) : EReal) := by rw [map_add]
  have hkey' : (g x + convexConj B g y₂) + (f x + convexConj B f y₁)
      ≤ ((B x y₂ + B x y₁ : ℝ) : EReal) := by
    rw [add_comm (g x + convexConj B g y₂), add_comm (B x y₂)]
    exact hkey
  have hf := h.properConvex_left.le_add_convexConj (B := B) x y₁
  have hg := h.properConvex_right.le_add_convexConj (B := B) x y₂
  exact ⟨y₁, mem_subdifferential_iff_add_convexConj_le.2
      (EReal.le_coe_of_add_le_coe_add hf hg hkey),
    y₂, mem_subdifferential_iff_add_convexConj_le.2
      (EReal.le_coe_of_add_le_coe_add hg hf hkey'), rfl⟩

end Add

/-! ### Sums of `m` functions -/

section FinsetAdd

variable {ι E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
variable {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {s : Finset ι} {f : ι → E → EReal}

/-- **The unconditional inclusion** for `m` summands:
`∂f₁ x + ⋯ + ∂fₘ x ⊆ ∂(f₁ + ⋯ + fₘ) x`. Over the empty `Finset` the left side is `{0}` and the
right side is `∂(0) x`, which contains `0`. -/
theorem subdifferential_finsetSum_subset (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (s : Finset ι)
    (f : ι → E → EReal) (x : E) :
    ∑ i ∈ s, subdifferential B (f i) x ⊆ subdifferential B (∑ i ∈ s, f i) x := by
  induction s using Finset.cons_induction with
  | empty =>
    intro y hy
    simp only [Finset.sum_empty, Set.mem_zero] at hy
    subst hy
    simp [mem_subdifferential]
  | cons i t hi ih =>
    rw [Finset.sum_cons, Finset.sum_cons]
    exact (Set.add_subset_add_left ih).trans (subdifferential_add_subset B (f i) _ x)

/-- `∂(f₁ + ⋯ + fₘ) x = ∂f₁ x + ⋯ + ∂fₘ x` whenever the family adds exactly.
Exactness hands back a splitting `y = y₁ + ⋯ + yₘ` whose conjugate values already sum to
`(∑ fᵢ)* y`, and `y ∈ ∂(∑ fᵢ) x` makes the sum of the `m` Fenchel inequalities tight, hence each
of them. This is not the binary rule iterated. -/
theorem IsExactFinsetSum.subdifferential_finsetSum (h : IsExactFinsetSum B s f) (x : E) :
    subdifferential B (∑ i ∈ s, f i) x = ∑ i ∈ s, subdifferential B (f i) x := by
  refine Set.Subset.antisymm (fun y hy => ?_) (subdifferential_finsetSum_subset B s f x)
  obtain ⟨y', hy', hle⟩ := h.exact_le y
  have hfen : ∀ i ∈ s, ((B x (y' i) : ℝ) : EReal) ≤ f i x + convexConj B (f i) (y' i) :=
    fun i hi => (h.proper i hi).le_add_convexConj x (y' i)
  have hsum : ∑ i ∈ s, (f i x + convexConj B (f i) (y' i))
      ≤ ((∑ i ∈ s, B x (y' i) : ℝ) : EReal) := by
    calc ∑ i ∈ s, (f i x + convexConj B (f i) (y' i))
        = (∑ i ∈ s, f i) x + ∑ i ∈ s, convexConj B (f i) (y' i) := by
          rw [Finset.sum_add_distrib, Finset.sum_apply]
      _ ≤ (∑ i ∈ s, f i) x + convexConj B (∑ i ∈ s, f i) y := add_le_add le_rfl hle
      _ ≤ ((B x y : ℝ) : EReal) := mem_subdifferential_iff_add_convexConj_le.1 hy
      _ = ((∑ i ∈ s, B x (y' i) : ℝ) : EReal) := by rw [← hy', map_sum]
  have hmem : ∀ i ∈ s, y' i ∈ subdifferential B (f i) x := fun i hi =>
    mem_subdifferential_iff_add_convexConj_le.2
      (EReal.le_coe_of_sum_le_coe_sum (c := fun i => B x (y' i))
        (u := fun i => f i x + convexConj B (f i) (y' i)) hfen hsum hi)
  have hgoal := Set.finsetSum_mem_finsetSum s (fun i => subdifferential B (f i) x) y' hmem
  rwa [hy'] at hgoal

end FinsetAdd

/-! ### Linear maps -/

section Image

variable {E F G H : Type*}
  [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [AddCommGroup G] [Module ℝ G] [AddCommGroup H] [Module ℝ H]
variable {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {B' : G →ₗ[ℝ] H →ₗ[ℝ] ℝ}
  {A : E →ₗ[ℝ] G} {A' : H →ₗ[ℝ] F} {g : G → EReal}

/-- **The unconditional inclusion**: the transpose carries subgradients of `g` at
`A x` to subgradients of `g A` at `x`. Only the adjointness datum is used; `g` is arbitrary. -/
theorem image_subdifferential_subset (hA : IsAdjointPair B B' A A') (g : G → EReal) (x : E) :
    A' '' subdifferential B' g (A x) ⊆ subdifferential B (compLin g A) x := by
  rintro _ ⟨z, hz, rfl⟩ w
  have hw := hz (A w)
  rwa [compLin_apply, compLin_apply, ← hA (w - x) z, map_sub]

/-- `∂(g A) x = A' (∂g (A x))` whenever the pullback is exact. Unlike the sum
rule this needs no splitting: exactness hands back a single `z` in the fibre with
`g* z ≤ (g A)* (A' z)`, which slots straight into Fenchel's inequality once a subgradient at `x` is
seen to force `(g A)* y` finite. -/
theorem IsExactImage.subdifferential_compLin {hA : IsAdjointPair B B' A A'}
    (h : IsExactImage B B' A A' hA g) (x : E) :
    subdifferential B (compLin g A) x = A' '' subdifferential B' g (A x) := by
  refine Set.Subset.antisymm (fun y hy => ?_) (image_subdifferential_subset hA g x)
  have hne : compLin g A x ≠ ⊥ := by rw [compLin_apply]; exact h.proper.ne_bot (A x)
  have hfin : convexConj B (compLin g A) y < ⊤ := by
    by_contra htop
    rw [not_lt, top_le_iff] at htop
    have hsub := mem_subdifferential_iff_add_convexConj_le.1 hy
    rw [htop, EReal.add_top_of_ne_bot hne, top_le_iff] at hsub
    exact absurd hsub (EReal.coe_ne_top _)
  obtain ⟨z, rfl, hle⟩ := h.exact_le y hfin
  refine ⟨z, mem_subdifferential_iff_add_convexConj_le.2 ?_, rfl⟩
  calc g (A x) + convexConj B' g z
      ≤ g (A x) + convexConj B (compLin g A) (A' z) := add_le_add le_rfl hle
    _ = compLin g A x + convexConj B (compLin g A) (A' z) := by rw [compLin_apply]
    _ ≤ ((B x (A' z) : ℝ) : EReal) := mem_subdifferential_iff_add_convexConj_le.1 hy
    _ = ((B' (A x) z : ℝ) : EReal) := by rw [hA x z]

end Image

/-! ### Scalar multiples -/

section Smul

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
variable {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ}

/-- `∂(cf) x = c ∂f x` for `c > 0`, with no hypothesis on `f`: multiplying the subgradient
inequality through by `c > 0` is reversible even on `EReal`.

Positivity is essential in both directions. At `c = 0` the left side is `{y | ∀ w, B w y = 0}`,
which has nothing to do with `∂f x`; for `c < 0` the scaled inequality reverses and `cf` is
*concave* where `f` is convex. The negative case survives only when `f` is affine. -/
theorem subdifferential_coe_mul {c : ℝ} (hc : 0 < c) (f : E → EReal) (x : E) :
    subdifferential B (fun y => (c : EReal) * f y) x = c • subdifferential B f x := by
  ext v
  constructor
  · intro hv
    refine ⟨c⁻¹ • v, fun z => ?_, ?_⟩
    swap
    · change c • (c⁻¹ • v) = v
      rw [smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
    have h1 := hv z
    have hp : B (z - x) (c⁻¹ • v) = c⁻¹ * B (z - x) v := by rw [map_smul, smul_eq_mul]
    rw [hp]
    refine (EReal.coe_mul_add_coe_le_coe_mul_iff hc (f x) (f z) _).1 ?_
    rw [show c * (c⁻¹ * B (z - x) v) = B (z - x) v from by field_simp]
    exact h1
  · rintro ⟨w, hw, rfl⟩
    intro z
    have hp : B (z - x) (c • w) = c * B (z - x) w := by rw [map_smul, smul_eq_mul]
    rw [hp]
    exact (EReal.coe_mul_add_coe_le_coe_mul_iff hc (f x) (f z) _).2 (hw z)

/-- `∂(0 · f) x = {0}`: the zero function has the origin as its only subgradient.

This is what the parenthesis "(Omit terms with `λᵢ = 0`.)" in the Kuhn–Tucker conditions means, and
why it is not cosmetic: `∂fᵢ x` may be *empty* at a boundary point of `dom fᵢ`, so the term
`0 · ∂fᵢ x` that the parenthesis drops would be `∅` rather than `{0}`, emptying the whole sum. -/
theorem subdifferential_zero_mul (hB : Function.Injective B.flip) (f : E → EReal) (x : E) :
    subdifferential B (fun y => ((0 : ℝ) : EReal) * f y) x = {(0 : F)} := by
  have hz : (fun y => ((0 : ℝ) : EReal) * f y) = fun _ : E => (0 : EReal) := by
    funext y; rw [EReal.coe_zero, zero_mul]
  rw [hz]
  ext v
  rw [Set.mem_singleton_iff]
  constructor
  · intro hv
    have hle : ∀ w : E, B w v ≤ 0 := by
      intro w
      have h := hv (x + w)
      rw [add_sub_cancel_left, zero_add] at h
      have h' : ((B w v : ℝ) : EReal) ≤ (0 : EReal) := h
      exact_mod_cast h'
    refine hB (LinearMap.ext fun w => ?_)
    change B w v = B w 0
    rw [map_zero]
    refine le_antisymm (hle w) ?_
    have hneg := hle (-w)
    rw [map_neg B w, LinearMap.neg_apply] at hneg
    linarith
  · rintro rfl
    intro z
    rw [zero_add, map_zero]
    exact le_of_eq (by norm_num)

/-- The subdifferential of an affine function is one point, namely the vector `b` representing its
linear part through the pairing. No differentiation is needed: `b` is handed in, together with the
identity `⟨w, b⟩ = a.linear w` naming it, and nothing in the statement mentions a topology. -/
theorem subdifferential_coe_affineMap (hB : Function.Injective B.flip) (a : E →ᵃ[ℝ] ℝ) {b : F}
    (hb : ∀ w : E, B w b = a.linear w) (x : E) :
    subdifferential B (fun y => ((a y : ℝ) : EReal)) x = {b} := by
  have hdec : ∀ z : E, a z - a x = a.linear (z - x) := by
    intro z
    have h1 : ∀ y : E, a y = a.linear y + a 0 := fun y => congrFun (AffineMap.decomp a) y
    rw [h1 z, h1 x, map_sub]
    ring
  ext v
  rw [Set.mem_singleton_iff]
  constructor
  · intro hv
    have hle : ∀ w : E, B w v ≤ a.linear w := by
      intro w
      have h := hv (w + x)
      rw [add_sub_cancel_right, ← EReal.coe_add, EReal.coe_le_coe_iff] at h
      have hd := hdec (w + x)
      rw [add_sub_cancel_right] at hd
      linarith
    refine hB (LinearMap.ext fun w => ?_)
    change B w v = B w b
    rw [hb w]
    refine le_antisymm (hle w) ?_
    have hneg := hle (-w)
    rw [map_neg B w, LinearMap.neg_apply, map_neg a.linear w] at hneg
    linarith
  · rintro rfl
    intro z
    rw [← EReal.coe_add, EReal.coe_le_coe_iff, hb (z - x)]
    linarith [hdec z]

/-- `∂(ca) x = c ∂a x` for an *arbitrary* real `c`, when `a` is affine. An affine function satisfies
the subgradient inequality with *equality*, so scaling by a negative `c` reverses nothing; this is
what covers equality-constraint multipliers, which may be negative. -/
theorem subdifferential_coe_mul_affineMap (hB : Function.Injective B.flip) (c : ℝ) (a : E →ᵃ[ℝ] ℝ)
    {b : F} (hb : ∀ w : E, B w b = a.linear w) (x : E) :
    subdifferential B (fun y => (c : EReal) * ((a y : ℝ) : EReal)) x
      = c • subdifferential B (fun y => ((a y : ℝ) : EReal)) x := by
  have hfun : (fun y => (c : EReal) * ((a y : ℝ) : EReal))
      = fun y => (((c • a) y : ℝ) : EReal) := by
    funext y
    rw [← EReal.coe_mul]
    rfl
  have hb' : ∀ w : E, B w (c • b) = (c • a).linear w := by
    intro w
    rw [map_smul, smul_eq_mul, hb w]
    rfl
  rw [hfun, subdifferential_coe_affineMap hB (c • a) hb' x, subdifferential_coe_affineMap hB a hb x,
    Set.smul_set_singleton]

end Smul

/-! ### Normal cones to an intersection -/

section NormalCone

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
variable {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {C D : Set E} {x : E}

/-- **The unconditional inclusion**. Proved directly rather than through indicators, so that it
needs neither `x ∈ C` nor `x ∈ D`. -/
theorem normalCone_add_subset (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (C D : Set E) (x : E) :
    normalCone B C x + normalCone B D x ⊆ normalCone B (C ∩ D) x := by
  rintro _ ⟨y₁, hy₁, y₂, hy₂, rfl⟩ z hz
  rw [map_add]
  exact add_nonpos (hy₁ z hz.1) (hy₂ z hz.2)

/-- The normal cone to an intersection is the sum of the normal cones, under the exact-sum
hypothesis for the two indicators. -/
theorem IsExactSum.normalCone_inter (h : IsExactSum B (indicatorFn C) (indicatorFn D))
    (hC : x ∈ C) (hD : x ∈ D) :
    normalCone B (C ∩ D) x = normalCone B C x + normalCone B D x := by
  have hsum := h.subdifferential_add x
  rwa [indicatorFn_add, subdifferential_indicatorFn (Set.mem_inter hC hD),
    subdifferential_indicatorFn hC,
    subdifferential_indicatorFn hD] at hsum

end NormalCone

/-! ### The normal cone to the effective domain -/

section NormalConeDom

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
variable {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f : E → EReal} {x : E}

/-- A normal to the effective domain may be added to a subgradient — the elementary inclusion
behind `∂f x + N_{dom f}(x) = ∂f x`. Neither convexity nor a topology is needed. -/
theorem subdifferential_add_normalCone_convexDom_subset (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal)
    (x : E) :
    subdifferential B f x + normalCone B (convexDom f) x ⊆ subdifferential B f x := by
  rintro _ ⟨y, hy, n, hn, rfl⟩ z
  by_cases hz : z ∈ convexDom f
  · have hle : ((B (z - x) (y + n) : ℝ) : EReal) ≤ ((B (z - x) y : ℝ) : EReal) := by
      rw [map_add, EReal.coe_le_coe_iff]
      linarith [hn z hz]
    exact (add_le_add (le_refl (f x)) hle).trans (hy z)
  · rw [top_le_iff.1 (not_lt.1 fun h => hz (mem_convexDom.2 h))]
    exact le_top

/-- A lone subgradient leaves no room for a normal direction: if `∂f x = {y₀}` then `y₀ + n` is
again a subgradient for every `n` normal to `dom f` at `x`, so `n = 0`. With
`mem_interior_of_normalCone_eq_zero` this turns uniqueness into an interiority statement. -/
theorem normalCone_convexDom_eq_zero_of_subdifferential_eq_singleton {y₀ : F}
    (h : subdifferential B f x = {y₀}) : normalCone B (convexDom f) x = {0} := by
  refine Set.eq_singleton_iff_unique_mem.2 ⟨fun z _ => by simp, fun n hn => ?_⟩
  have hy₀ : y₀ ∈ subdifferential B f x := by rw [h]; rfl
  have hmem := subdifferential_add_normalCone_convexDom_subset B f x (Set.add_mem_add hy₀ hn)
  rw [h, Set.mem_singleton_iff] at hmem
  simpa using hmem

end NormalConeDom

/-! ### Transport along a linear isomorphism

`convexConj_comp_linearEquiv` of `Duality/Conjugate` is the substitution rule for the conjugate. The
subdifferential obeys the same rule, in the generality of an arbitrary adjoint pair of
isomorphisms. -/

section LinearEquivTransport

variable {E F G H : Type*}
variable [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
variable [AddCommGroup G] [Module ℝ G] [AddCommGroup H] [Module ℝ H]

/-- **Precomposing with a linear isomorphism moves the subdifferential along the transpose.**
The companion of `convexConj_comp_linearEquiv` for `∂f`: if `A` and `A'` are adjoint isomorphisms,
then `∂(g ∘ A)(x) = A' (∂g (A x))`. -/
theorem subdifferential_comp_linearEquiv {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {B' : G →ₗ[ℝ] H →ₗ[ℝ] ℝ}
    (A : E ≃ₗ[ℝ] G) (A' : H ≃ₗ[ℝ] F)
    (hA : IsAdjointPair B B' (A : E →ₗ[ℝ] G) (A' : H →ₗ[ℝ] F)) (g : G → EReal) (x : E) :
    subdifferential B (fun u => g (A u)) x = A' '' subdifferential B' g (A x) := by
  ext y
  constructor
  · intro hy
    refine ⟨A'.symm y, fun w => ?_, A'.apply_symm_apply y⟩
    have hw : g (A x) + ((B (A.symm w - x) y : ℝ) : EReal) ≤ g (A (A.symm w)) := hy (A.symm w)
    rw [LinearEquiv.apply_symm_apply] at hw
    have h2 := hA (A.symm w - x) (A'.symm y)
    simp only [LinearEquiv.coe_coe] at h2
    have h1 : A (A.symm w - x) = w - A x := by simp
    have h3 : A' (A'.symm y) = y := A'.apply_symm_apply y
    rw [h1, h3] at h2
    rw [h2]
    exact hw
  · rintro ⟨v, hv, rfl⟩
    intro w
    have hw : g (A x) + ((B' (A w - A x) v : ℝ) : EReal) ≤ g (A w) := hv (A w)
    have h2 := hA (w - x) v
    simp only [LinearEquiv.coe_coe] at h2
    have h1 : A (w - x) = A w - A x := map_sub A w x
    rw [h1] at h2
    rw [← h2]
    exact hw

end LinearEquivTransport

end ConvexAnalysis
