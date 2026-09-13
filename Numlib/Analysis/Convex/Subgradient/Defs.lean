import Mathlib.Data.EReal.Inv
import Mathlib.Data.Rel
import Numlib.Analysis.Convex.Duality.Support

/-!
# Subgradients, normal cones and directional derivatives

Over a dual pair `B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ`, a *subgradient* of `f` at `x` is a `y : F` for which the
affine function `z ↦ f x + ⟨z - x, y⟩` minorizes `f`; equivalently, one whose graph is a
non-vertical supporting hyperplane to `epi f` at `(x, f x)`. The set of them is the
*subdifferential* `∂f x`. The definition is deliberately algebraic — a system of weak linear
inequalities, one for each `z` — and no topology enters until the closure of `f` does. This file
also introduces the normal cone `N_C(x)` and the one-sided directional derivative `f'(x; y)`, and
develops the elementary theory of all three.

## Main definitions

* `subgradient B f x` — the subdifferential `∂f x`, a subset of `F`; `subgradientRel B f` is its
  graph as a `SetRel E F`, and `domSubgradient B f` the set of points where it is non-empty.
* `normalCone B C x` — the normal cone `N_C(x)`, bundled by `normalPointedCone`.
* `dirDeriv f x y` — the directional derivative `f'(x; y)`, as the infimum of the difference
  quotient. Meaningful only where `f x` is finite; see the implementation notes.

## Main results

* `Proper.mem_subgradient_tfae` — `y ∈ ∂f x`, attainment of the supremum of `⟨·, y⟩ - f` at `x`,
  and equality in Fenchel's inequality at `(x, y)` say the same thing (Theorem 23.5 in [^1]). All
  the individual implications but the last are unconditional.
* `subgradientRel_conj_eq_inv` — for closed proper convex `f`, the graph of `∂f*` is the flip of
  the graph of `∂f`; `subgradient_clFn` — `∂(cl f) x = ∂f x` wherever `f` is subdifferentiable.
* `subgradient_indicatorFn` — `∂δ(· | C) x = N_C(x)` for `x ∈ C`; `subgradient_supportFn` — the
  subgradients of `δ*(· | C)` at `y` are the maximizers of `⟨·, y⟩` over `C`.
* `monotoneOn_sub_div`, `posHomogeneous_dirDeriv`, `convexFn_dirDeriv` — the difference quotient is
  nondecreasing in the step; `f'(x; ·)` is positively homogeneous and convex.
* `mem_subgradient_iff_le_dirDeriv`, `conj_dirDeriv`, `clFn_dirDeriv` — `∂f x` is where
  `⟨·, y⟩ ≤ f'(x; ·)`, and `cl f'(x; ·)` is the support function of `∂f x` (Theorem 23.2 in [^1]).
* `proper_of_mem_subgradient` — subdifferentiability at a point of finiteness forces properness.

## Implementation notes

`∂f` is available both pointwise and as a relation. The monotonicity and Legendre theory is about
the graph, and with `subgradientRel` the inversion reads literally as `∂(f*) = (∂f)⁻¹`. `∂f x` is
not bundled as a convex set: convexity is unconditional but closedness needs a continuous pairing,
and a bundled object would carry that hypothesis as data. `N_C(x)` *is* bundled, being a cone for
every `C` and `x`.

The finiteness hypothesis on `dirDeriv` is not removable: `EReal` has `⊤ - ⊤ = ⊥`, so off `dom f`
the difference quotient is `⊥` in every direction and `f'(x; 0) = 0` fails. Statements that
mention a *value* of `f'(x; ·)` therefore carry `f x ≠ ⊤` and `f x ≠ ⊥`; positive homogeneity is
the exception, being a reindexing of the infimum.

## References

[^1]: R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §23.
-/

open Set

namespace ConvexAnalysis

/-! ### Definitions -/

section Defs

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

/-- The **subdifferential** of `f` at `x` with respect to the pairing `B`: the set of `y : F`
satisfying the *subgradient inequality* `f z ≥ f x + ⟨z - x, y⟩` for every `z`.

Geometrically, when `f x` is finite, `y` is a subgradient exactly when the graph of the affine
function `z ↦ f x + ⟨z - x, y⟩` is a non-vertical supporting hyperplane to `epi f` at
`(x, f x)`. -/
def subgradient (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) (x : E) : Set F :=
  {y | ∀ z, f x + ((B (z - x) y : ℝ) : EReal) ≤ f z}

/-- The **graph of the subdifferential**: the multivalued mapping `∂f : x ↦ ∂f x`, as a
`SetRel E F`. This is the object the monotonicity and duality theory is about, and what
conjugation inverts. -/
def subgradientRel (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) : SetRel E F :=
  {p | p.2 ∈ subgradient B f p.1}

/-- The **normal cone** to `C` at `x`: the `y : F` making a non-acute angle with every direction
`z - x` pointing from `x` into `C`. Introducing `N_C(x)` as `∂δ(x | C)` would leave it empty for
`x ∉ C`; here it is defined for every `x`, which is what makes it a pointed cone with no
hypothesis. The price is the `x ∈ C` in `subgradient_indicatorFn`. -/
def normalCone (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (C : Set E) (x : E) : Set F :=
  {y | ∀ z ∈ C, B (z - x) y ≤ 0}

variable {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f : E → EReal} {C : Set E} {x : E} {y : F}

@[simp] theorem mem_subgradient :
    y ∈ subgradient B f x ↔ ∀ z, f x + ((B (z - x) y : ℝ) : EReal) ≤ f z := Iff.rfl

@[simp] theorem mem_subgradientRel : (x, y) ∈ subgradientRel B f ↔ y ∈ subgradient B f x := Iff.rfl

@[simp] theorem mem_normalCone : y ∈ normalCone B C x ↔ ∀ z ∈ C, B (z - x) y ≤ 0 := Iff.rfl

/-- The normal cone as a pointed convex cone, with no hypothesis on `C` or on `x`. -/
def normalPointedCone (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (C : Set E) (x : E) : PointedCone ℝ F where
  carrier := normalCone B C x
  zero_mem' z _ := by simp
  add_mem' {y₁ y₂} h₁ h₂ z hz := by
    rw [map_add]
    exact add_nonpos (h₁ z hz) (h₂ z hz)
  smul_mem' c y h z hz := by
    rw [LinearMap.map_smul_of_tower]
    exact smul_nonpos_of_nonneg_of_nonpos c.2 (h z hz)

@[simp] theorem coe_normalPointedCone (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (C : Set E) (x : E) :
    (normalPointedCone B C x : Set F) = normalCone B C x := rfl

/-- The subdifferential is a convex set, with no hypothesis on `f`: it is an intersection of
half-spaces of `F`, one for each `z`. -/
theorem convex_subgradient (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) (x : E) :
    Convex ℝ (subgradient B f x) := by
  intro y₁ h₁ y₂ h₂ a b ha hb hab z
  have key : ∀ p q : ℝ, f x + (p : EReal) ≤ f z → q ≤ p → f x + (q : EReal) ≤ f z :=
    fun _ _ hp hqp => le_trans (add_le_add le_rfl (mod_cast hqp)) hp
  simp only [mem_subgradient, map_add, map_smul, smul_eq_mul] at h₁ h₂ ⊢
  rcases le_total (B (z - x) y₁) (B (z - x) y₂) with h | h
  · refine key _ _ (h₂ z) ?_
    have h1 : a * B (z - x) y₁ ≤ a * B (z - x) y₂ := mul_le_mul_of_nonneg_left h ha
    have h2 : a * B (z - x) y₂ + b * B (z - x) y₂ = B (z - x) y₂ := by rw [← add_mul, hab, one_mul]
    linarith
  · refine key _ _ (h₁ z) ?_
    have h1 : b * B (z - x) y₂ ≤ b * B (z - x) y₁ := mul_le_mul_of_nonneg_left h hb
    have h2 : a * B (z - x) y₁ + b * B (z - x) y₁ = B (z - x) y₁ := by rw [← add_mul, hab, one_mul]
    linarith

/-- A point with a subgradient lies in the effective domain: were `f x = ⊤`, the subgradient
inequality would read `⊤ ≤ f z` for every `z` and force `f ≡ ⊤`, which properness forbids. -/
theorem mem_dom_of_mem_subgradient (hp : Proper f) (hy : y ∈ subgradient B f x) : x ∈ dom f := by
  obtain ⟨z₀, hz₀⟩ := hp.dom_nonempty
  refine mem_dom.2 (lt_top_iff_ne_top.2 fun htop => ?_)
  have hle := hy z₀
  rw [htop, EReal.top_add_coe] at hle
  exact absurd (top_le_iff.1 hle) (mem_dom.1 hz₀).ne

/-- `dom ∂f`: the set of points at which `f` has at least one subgradient. -/
def domSubgradient (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) : Set E :=
  {x | (subgradient B f x).Nonempty}

@[simp] theorem mem_domSubgradient : x ∈ domSubgradient B f ↔ (subgradient B f x).Nonempty :=
  Iff.rfl

/-- `dom ∂f ⊆ dom f`: a subgradient at `x` forces `f x < ⊤`. -/
theorem domSubgradient_subset_dom (hp : Proper f) : domSubgradient B f ⊆ dom f := by
  rintro z ⟨y, hy⟩
  exact mem_dom_of_mem_subgradient hp hy

end Defs

/-! ### Subgradients, conjugates and Fenchel's inequality -/

section Conj

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
variable {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f : E → EReal} {x : E} {y : F}

/-- `y ∈ ∂f x` says exactly that `⟨·, y⟩ - f` attains its supremum at `x`. -/
theorem mem_subgradient_iff_forall_sub_le :
    y ∈ subgradient B f x ↔ ∀ z, ((B z y : ℝ) : EReal) - f z ≤ ((B x y : ℝ) : EReal) - f x := by
  refine forall_congr' fun z => ?_
  rw [EReal.coe_sub_le_comm, EReal.coe_sub_coe_sub, map_sub, LinearMap.sub_apply, add_comm]

/-- That supremum *is* `f* y`, so `y ∈ ∂f x` is the inequality `f* y ≤ ⟨x, y⟩ - f x`. -/
theorem mem_subgradient_iff_conj_le :
    y ∈ subgradient B f x ↔ conj B f y ≤ ((B x y : ℝ) : EReal) - f x := by
  rw [mem_subgradient_iff_forall_sub_le, conj_apply, iSup_le_iff]

/-- Attainment written as an equation: `y ∈ ∂f x` exactly when `f* y = ⟨x, y⟩ - f x`. This is the
`∞ - ∞`-free reading of equality in Fenchel's inequality. -/
theorem mem_subgradient_iff_conj_eq :
    y ∈ subgradient B f x ↔ conj B f y = ((B x y : ℝ) : EReal) - f x :=
  ⟨fun h => le_antisymm (mem_subgradient_iff_conj_le.1 h) (sub_le_conj B f x y),
    fun h => mem_subgradient_iff_conj_le.2 h.le⟩

/-- The same in the additive form `f x + f* y ≤ ⟨x, y⟩`. Unconditional: adding a *real* number is
an order isomorphism of `EReal`, so no `∞ - ∞` arises. -/
theorem mem_subgradient_iff_add_conj_le :
    y ∈ subgradient B f x ↔ f x + conj B f y ≤ ((B x y : ℝ) : EReal) := by
  rw [mem_subgradient_iff_conj_le, EReal.le_sub_iff_add_le
    (.inr (EReal.coe_ne_bot _)) (.inr (EReal.coe_ne_top _)), add_comm]

/-- `y ∈ ∂f x` exactly when **Fenchel's inequality** holds with equality at `(x, y)`. Properness is
not decorative: for `f ≡ ⊤` every `y` is a subgradient at every `x`, while `f* ≡ ⊥` and so
`f x + f* y = ⊤ + ⊥ = ⊥ ≠ ⟨x, y⟩`. -/
theorem Proper.mem_subgradient_iff_add_conj_eq (hp : Proper f) :
    y ∈ subgradient B f x ↔ f x + conj B f y = ((B x y : ℝ) : EReal) := by
  rw [mem_subgradient_iff_add_conj_le]
  exact ⟨fun h => le_antisymm h (hp.le_add_conj x y), fun h => h.le⟩

/-- **The four equivalent forms of subgradient membership**: for a proper `f` the conditions

* (a) `y ∈ ∂f x`;
* (b) `⟨·, y⟩ - f` attains its supremum at `x`;
* (c) `f x + f* y ≤ ⟨x, y⟩`;
* (d) `f x + f* y = ⟨x, y⟩`

are equivalent. Convexity of `f` is nowhere used; properness is needed only to close the loop back
from (d). -/
theorem Proper.mem_subgradient_tfae (hp : Proper f) (x : E) (y : F) :
    List.TFAE [y ∈ subgradient B f x,
      ∀ z, ((B z y : ℝ) : EReal) - f z ≤ ((B x y : ℝ) : EReal) - f x,
      f x + conj B f y ≤ ((B x y : ℝ) : EReal),
      f x + conj B f y = ((B x y : ℝ) : EReal)] := by
  tfae_have 1 ↔ 2 := mem_subgradient_iff_forall_sub_le
  tfae_have 1 ↔ 3 := mem_subgradient_iff_add_conj_le
  tfae_have 1 ↔ 4 := hp.mem_subgradient_iff_add_conj_eq
  tfae_finish

/-- `x ∈ ∂f* y` and `y ∈ ∂f x` agree at every `x` where `f` coincides with its biconjugate — for a
closed proper convex `f`, everywhere. -/
theorem mem_subgradient_conj_iff (h : biconj B f x = f x) :
    x ∈ subgradient B.flip (conj B f) y ↔ y ∈ subgradient B f x := by
  have h' : conj B.flip (conj B f) x = f x := h
  rw [mem_subgradient_iff_add_conj_le, mem_subgradient_iff_add_conj_le, LinearMap.flip_apply, h',
    add_comm]

/-- At a point where `f` is subdifferentiable it agrees with its biconjugate. No topology and no
convexity are needed. -/
theorem biconj_eq_of_mem_subgradient (hy : y ∈ subgradient B f x) : biconj B f x = f x := by
  refine le_antisymm (biconj_le B f x) ?_
  have h := sub_le_conj B.flip (conj B f) y x
  rwa [LinearMap.flip_apply, mem_subgradient_iff_conj_eq.1 hy, EReal.coe_sub_coe_sub, sub_self,
    EReal.coe_zero, zero_add] at h

/-- A function subdifferentiable at a point where it is finite is proper. The subgradient
inequality exhibits a finite affine minorant, ruling out the value `⊥`. -/
theorem proper_of_mem_subgradient (ht : f x ≠ ⊤) (hb : f x ≠ ⊥) (hy : y ∈ subgradient B f x) :
    Proper f := by
  obtain ⟨r, hr⟩ := EReal.exists_coe_of_ne_bot_of_lt_top hb (lt_top_iff_ne_top.2 ht)
  refine ⟨⟨x, lt_top_iff_ne_top.2 ht⟩, fun z hz => ?_⟩
  have h := hy z
  rw [hr, hz, ← EReal.coe_add] at h
  exact EReal.coe_ne_bot _ (le_bot_iff.1 h)

/-- The same in the "subdifferentiable" phrasing. -/
theorem proper_of_subgradient_nonempty (ht : f x ≠ ⊤) (hb : f x ≠ ⊥)
    (h : (subgradient B f x).Nonempty) : Proper f :=
  h.elim fun _ hy => proper_of_mem_subgradient ht hb hy

/-- A proper function has no subgradients off its effective domain. Unlike the finer statements
about where `∂f` is non-empty, this involves no relative interiors. -/
theorem subgradient_eq_empty_of_notMem_dom (hp : Proper f) (hx : x ∉ dom f) :
    subgradient B f x = ∅ := by
  obtain ⟨z, hz⟩ := hp.dom_nonempty
  have hfx : f x = ⊤ := by
    by_contra hc
    exact hx (lt_top_iff_ne_top.2 hc)
  refine eq_empty_of_forall_notMem fun y hy => absurd (hy z) (not_le.2 ?_)
  rw [hfx, EReal.top_add_coe]
  exact hz

end Conj

/-! ### Indicator functions, normal cones and polar cones -/

section Indicator

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
variable {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {C : Set E} {x : E} {y : F}

/-- The subdifferential of an indicator function is the normal cone, at any point of `C`. -/
theorem subgradient_indicatorFn (hx : x ∈ C) :
    subgradient B (indicatorFn C) x = normalCone B C x := by
  ext y
  simp only [mem_subgradient, indicatorFn_of_mem hx, zero_add, mem_normalCone]
  refine ⟨fun h z hz => ?_, fun h z => ?_⟩
  · have hz' := h z
    rw [indicatorFn_of_mem hz] at hz'
    exact_mod_cast hz'
  · by_cases hz : z ∈ C
    · rw [indicatorFn_of_mem hz]
      exact_mod_cast h z hz
    · rw [indicatorFn_of_notMem hz]
      exact le_top

/-- Off `C` there are no subgradients of `δ(· | C)`, provided `C` is nonempty. -/
theorem subgradient_indicatorFn_of_notMem (hC : C.Nonempty) (hx : x ∉ C) :
    subgradient B (indicatorFn C) x = ∅ :=
  subgradient_eq_empty_of_notMem_dom ⟨by rwa [dom_indicatorFn], indicatorFn_ne_bot C⟩
    (by rwa [dom_indicatorFn])

/-- Membership in `∂δ(· | C)` in full, for nonempty `C`. -/
theorem mem_subgradient_indicatorFn_iff (hC : C.Nonempty) :
    y ∈ subgradient B (indicatorFn C) x ↔ x ∈ C ∧ y ∈ normalCone B C x := by
  by_cases hx : x ∈ C
  · rw [subgradient_indicatorFn hx]
    exact ⟨fun h => ⟨hx, h⟩, fun h => h.2⟩
  · rw [subgradient_indicatorFn_of_notMem hC hx]
    exact ⟨fun h => absurd h (notMem_empty y), fun h => absurd h.1 hx⟩

/-- For a pointed convex cone `K`, `y` is a subgradient of `δ(· | K)` at `x` exactly when `x ∈ K`,
`y` lies in the polar cone `K° = N_K(0)`, and `⟨x, y⟩ = 0`. The classical route assumes `K` closed
and goes through `δ(· | K)* = δ(· | K°)`; the direct argument — put `z = 0` and `z = x + x` into
the subgradient inequality — needs no topology, so `K` is arbitrary here. -/
theorem mem_subgradient_indicatorFn_pointedCone (K : PointedCone ℝ E) :
    y ∈ subgradient B (indicatorFn (K : Set E)) x ↔
      x ∈ K ∧ y ∈ normalCone B (K : Set E) 0 ∧ B x y = 0 := by
  rw [mem_subgradient_indicatorFn_iff ⟨0, K.zero_mem⟩]
  simp only [mem_normalCone, sub_zero, SetLike.mem_coe]
  constructor
  · rintro ⟨hx, h⟩
    have h0 : B (0 - x) y ≤ 0 := h 0 K.zero_mem
    have h2 : B (x + x - x) y ≤ 0 := h (x + x) (K.add_mem hx hx)
    rw [zero_sub, map_neg, LinearMap.neg_apply] at h0
    rw [add_sub_cancel_right] at h2
    have hzero : B x y = 0 := le_antisymm h2 (by linarith)
    refine ⟨hx, fun z hz => ?_, hzero⟩
    have hz' := h z hz
    rwa [map_sub, LinearMap.sub_apply, hzero, sub_zero] at hz'
  · rintro ⟨hx, hpol, hzero⟩
    refine ⟨hx, fun z hz => ?_⟩
    rw [map_sub, LinearMap.sub_apply, hzero, sub_zero]
    exact hpol z hz

end Indicator

/-! ### Closedness of the subdifferential -/

section Closed

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace F] {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ}

omit [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] in
/-- Adding a fixed `EReal` to a real is continuous. Note that `u + ·` on all of `EReal` is *not*
continuous when `u = ⊤`, because `⊤ + ⊥ = ⊥`; restricting the argument to the reals saves it. -/
theorem continuous_add_coe (u : EReal) : Continuous fun t : ℝ => u + (t : EReal) := by
  induction u with
  | bot => simpa only [EReal.bot_add] using continuous_const
  | coe r =>
    have h : Continuous fun t : ℝ => (r + t : ℝ) := by fun_prop
    simpa only [← EReal.coe_add] using continuous_coe_real_ereal.comp' h
  | top => simpa only [EReal.top_add_coe] using continuous_const

/-- The subdifferential is closed once every `⟨z, ·⟩ : F → ℝ` is continuous — automatic in `ℝⁿ`,
and here the instance `closedFn_conj` also asks for. -/
theorem isClosed_subgradient [IsContinuousPairing B.flip] (f : E → EReal) (x : E) :
    IsClosed (subgradient B f x) := by
  rw [show subgradient B f x = ⋂ z : E, {y | f x + ((B (z - x) y : ℝ) : EReal) ≤ f z} from
    Set.ext fun y => by simp]
  exact isClosed_iInter fun z =>
    isClosed_Iic.preimage ((continuous_add_coe (f x)).comp (continuous_pairing B.flip (z - x)))

end Closed

/-! ### The directional derivative -/

section DirDeriv

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {f : E → EReal} {x y : E}

/-- The **one-sided directional derivative** `f'(x; y)`, as the infimum over `a > 0` of the
difference quotient. The quotient is nondecreasing in `a` for convex `f` finite at `x`, so the
infimum is the limit as `a ↓ 0`, the classical definition. Off `dom f` the expression degenerates
to `⊥` in every direction. -/
noncomputable def dirDeriv (f : E → EReal) (x y : E) : EReal :=
  ⨅ a ∈ Set.Ioi (0 : ℝ), (f (x + a • y) - f x) / (a : EReal)

theorem dirDeriv_apply (f : E → EReal) (x y : E) :
    dirDeriv f x y = ⨅ a ∈ Set.Ioi (0 : ℝ), (f (x + a • y) - f x) / (a : EReal) := rfl

/-- The directional derivative is a lower bound for every difference quotient. -/
theorem dirDeriv_le (f : E → EReal) (x y : E) {a : ℝ} (ha : 0 < a) :
    dirDeriv f x y ≤ (f (x + a • y) - f x) / (a : EReal) :=
  iInf₂_le (f := fun (b : ℝ) (_ : b ∈ Set.Ioi (0 : ℝ)) => (f (x + b • y) - f x) / (b : EReal)) a ha

/-- A lower bound for all difference quotients bounds the directional derivative. -/
theorem le_dirDeriv {c : EReal} (h : ∀ a : ℝ, 0 < a → c ≤ (f (x + a • y) - f x) / (a : EReal)) :
    c ≤ dirDeriv f x y :=
  le_iInf₂ (f := fun (b : ℝ) (_ : b ∈ Set.Ioi (0 : ℝ)) => (f (x + b • y) - f x) / (b : EReal)) h

/-- Witness extraction from the defining infimum. -/
theorem dirDeriv_lt_iff {c : EReal} :
    dirDeriv f x y < c ↔ ∃ a : ℝ, 0 < a ∧ (f (x + a • y) - f x) / (a : EReal) < c := by
  simp only [dirDeriv, iInf_lt_iff, Set.mem_Ioi, exists_prop]

/-- `f'(x; 0) = 0` whenever `f x` is finite. -/
theorem dirDeriv_zero (ht : f x ≠ ⊤) (hb : f x ≠ ⊥) : dirDeriv f x 0 = 0 := by
  have h : ∀ a : ℝ, 0 < a → (f (x + a • (0 : E)) - f x) / (a : EReal) = 0 := fun a _ => by
    rw [smul_zero, add_zero, EReal.sub_self ht hb, EReal.zero_div]
  exact le_antisymm ((dirDeriv_le f x 0 one_pos).trans (h 1 one_pos).le)
    (le_dirDeriv fun a ha => (h a ha).ge)

/-- `f'(x; ·)` is positively homogeneous. Unlike its other basic properties this needs no
hypothesis: it is the reindexing `a ↦ a * c` of the defining infimum. -/
theorem posHomogeneous_dirDeriv (f : E → EReal) (x : E) : PosHomogeneous (dirDeriv f x) := by
  intro c hc y
  have hterm : ∀ a : ℝ, 0 < a →
      (f (x + a • (c • y)) - f x) / (a : EReal)
        = (c : EReal) * ((f (x + (a * c) • y) - f x) / ((a * c : ℝ) : EReal)) := by
    intro a _
    rw [smul_smul, div_eq_mul_inv, div_eq_mul_inv, ← EReal.coe_inv, ← EReal.coe_inv,
      ← mul_assoc, mul_comm (c : EReal) _, mul_assoc, ← EReal.coe_mul,
      show c * (a * c)⁻¹ = a⁻¹ from by field_simp]
  rw [dirDeriv_apply, dirDeriv_apply, iInf_subtype', iInf_subtype', EReal.coe_mul_iInf hc]
  refine le_antisymm (le_iInf fun b => ?_) (le_iInf fun a => ?_)
  · have hb : (0 : ℝ) < (b : ℝ) / c := div_pos b.2 hc
    refine le_trans (iInf_le _ (⟨(b : ℝ) / c, hb⟩ : Set.Ioi (0 : ℝ))) ?_
    rw [hterm _ hb, div_mul_cancel₀ (b : ℝ) hc.ne']
  · rw [hterm _ a.2]
    exact iInf_le _ (⟨(a : ℝ) * c, mul_pos a.2 hc⟩ : Set.Ioi (0 : ℝ))

/-- For convex `f` finite at `x`, the difference quotient is nondecreasing in the step `a`. This
is what makes the infimum defining `dirDeriv` the limit as `a ↓ 0`. -/
theorem monotoneOn_sub_div (hf : ConvexFn f) {r : ℝ} (hr : f x = (r : EReal)) (y : E) :
    MonotoneOn (fun a : ℝ => (f (x + a • y) - f x) / (a : EReal)) (Set.Ioi 0) := by
  intro a ha b hb hab
  simp only [Set.mem_Ioi] at ha hb
  have hbne : b ≠ 0 := hb.ne'
  simp only [hr]
  refine EReal.le_of_forall_coe_le fun s hs => ?_
  rw [EReal.sub_div_le_coe_iff hb] at hs
  rw [EReal.sub_div_le_coe_iff ha]
  have ht0 : (0 : ℝ) ≤ a / b := (div_pos ha hb).le
  have ht1 : (0 : ℝ) ≤ 1 - a / b := by
    have : a / b ≤ 1 := (div_le_one hb).2 hab
    linarith
  have hvec : (1 - a / b) • x + (a / b) • (x + b • y) = x + a • y := by
    rw [smul_add, smul_smul, div_mul_cancel₀ a hbne, sub_smul, one_smul]
    abel
  have hcomb := hf.epi_combo (le_of_eq hr) hs ht1 ht0 (by ring)
  have hscal : (1 - a / b) * r + a / b * (r + s * b) = r + s * a := by field_simp; ring
  rw [hvec, hscal] at hcomb
  exact hcomb

/-- The form in which that monotonicity is consumed: if `f'(x; y) < m` then
`f (x + a • y) ≤ f x + m * a` for every sufficiently small `a > 0`. -/
theorem exists_le_of_dirDeriv_lt (hf : ConvexFn f) {r : ℝ} (hr : f x = (r : EReal)) {y : E}
    {m : ℝ} (h : dirDeriv f x y < (m : EReal)) :
    ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ a : ℝ, 0 < a → a ≤ a₀ → f (x + a • y) ≤ ((r + m * a : ℝ) : EReal) := by
  obtain ⟨a₀, ha₀, hlt⟩ := dirDeriv_lt_iff.1 h
  refine ⟨a₀, ha₀, fun a ha hle => ?_⟩
  rw [← EReal.sub_div_le_coe_iff ha, ← hr]
  exact le_trans (monotoneOn_sub_div hf hr y ha ha₀ hle) hlt.le

/-- `f'(x; ·)` is a convex function, for convex `f` finite at `x`. -/
theorem convexFn_dirDeriv (hf : ConvexFn f) (ht : f x ≠ ⊤) (hb : f x ≠ ⊥) :
    ConvexFn (dirDeriv f x) := by
  obtain ⟨r, hr⟩ := EReal.exists_coe_of_ne_bot_of_lt_top hb (lt_top_iff_ne_top.2 ht)
  refine convexFn_of_epi_combo fun y₁ y₂ μ ν h₁ h₂ s t hs ht' hst => ?_
  rcases hs.eq_or_lt with hs0 | hs0
  · subst hs0
    have : t = 1 := by linarith
    subst this
    simpa using h₂
  rcases ht'.eq_or_lt with ht0 | ht0
  · subst ht0
    have : s = 1 := by linarith
    subst this
    simpa using h₁
  refine EReal.le_of_forall_lt_iff_le.1 fun p hp => le_of_lt ?_
  replace hp := EReal.coe_lt_coe_iff.1 hp
  obtain ⟨e, he, hesum⟩ : ∃ e : ℝ, 0 < e ∧ s * μ + t * ν + e = p - e :=
    ⟨(p - (s * μ + t * ν)) / 2, by linarith, by ring⟩
  have h1 : dirDeriv f x y₁ < ((μ + e : ℝ) : EReal) :=
    lt_of_le_of_lt h₁ (mod_cast lt_add_of_pos_right μ he)
  have h2 : dirDeriv f x y₂ < ((ν + e : ℝ) : EReal) :=
    lt_of_le_of_lt h₂ (mod_cast lt_add_of_pos_right ν he)
  obtain ⟨a₁, ha₁, H₁⟩ := exists_le_of_dirDeriv_lt hf hr h1
  obtain ⟨a₂, ha₂, H₂⟩ := exists_le_of_dirDeriv_lt hf hr h2
  have ha : 0 < min a₁ a₂ := lt_min ha₁ ha₂
  have hA := H₁ _ ha (min_le_left a₁ a₂)
  have hB := H₂ _ ha (min_le_right a₁ a₂)
  have hvec : s • (x + min a₁ a₂ • y₁) + t • (x + min a₁ a₂ • y₂)
      = x + min a₁ a₂ • (s • y₁ + t • y₂) := by
    match_scalars
    · linear_combination hst
    · ring
    · ring
  have hcomb := hf.epi_combo hA hB hs ht' hst
  rw [hvec, show s * (r + (μ + e) * min a₁ a₂) + t * (r + (ν + e) * min a₁ a₂)
      = r + (p - e) * min a₁ a₂ from by
    linear_combination (r + min a₁ a₂ * e) * hst + min a₁ a₂ * hesum] at hcomb
  calc dirDeriv f x (s • y₁ + t • y₂)
      ≤ (f (x + min a₁ a₂ • (s • y₁ + t • y₂)) - f x) / ((min a₁ a₂ : ℝ) : EReal) :=
        dirDeriv_le _ _ _ ha
    _ ≤ ((p - e : ℝ) : EReal) := by
        rw [hr]
        exact (EReal.sub_div_le_coe_iff ha _).2 hcomb
    _ < (p : EReal) := mod_cast sub_lt_self p he

/-- `-f'(x; -y) ≤ f'(x; y)`. No `≠ ⊥` hypothesis on `f'(x; ·)` appears, although
`PosHomogeneous.neg_le` carries one: `f'(x; ·)` really can take the value `⊥`. -/
theorem neg_dirDeriv_neg_le (hf : ConvexFn f) (ht : f x ≠ ⊤) (hb : f x ≠ ⊥) (y : E) :
    -dirDeriv f x (-y) ≤ dirDeriv f x y := by
  have hconv := convexFn_dirDeriv hf ht hb
  have hzero := dirDeriv_zero ht hb
  have main : ∀ m n : ℝ, dirDeriv f x (-y) ≤ (m : EReal) → dirDeriv f x y ≤ (n : EReal) →
      (0 : ℝ) ≤ m + n := by
    intro m n hm hn
    have hc := hconv.epi_combo hm hn (a := 1 / 2) (b := 1 / 2) (by norm_num) (by norm_num)
      (by norm_num)
    rw [show ((1 : ℝ) / 2) • (-y) + ((1 : ℝ) / 2) • y = (0 : E) from by
      rw [smul_neg, neg_add_cancel], hzero, ← EReal.coe_zero,
      EReal.coe_le_coe_iff] at hc
    linarith
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨n, hn1, hn2⟩ := EReal.lt_iff_exists_real_btwn.1 hcon
  have h3 : dirDeriv f x (-y) < ((-n : ℝ) : EReal) := by
    rw [EReal.coe_neg]
    exact EReal.lt_neg_comm.1 hn2
  obtain ⟨m, hm1, hm2⟩ := EReal.exists_between_coe_real h3
  replace hm2 := EReal.coe_lt_coe_iff.1 hm2
  have := main m n hm1.le hn1.le
  linarith

end DirDeriv

/-! ### The subdifferential and the directional derivative -/

section DirDerivSubgradient

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
variable {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f : E → EReal} {x : E} {y : F}

/-- `y` is a subgradient of `f` at `x` exactly when the linear function `⟨·, y⟩` is majorized by
the directional derivative `f'(x; ·)`. Neither convexity of `f` nor monotonicity of the difference
quotient is used. -/
theorem mem_subgradient_iff_le_dirDeriv (ht : f x ≠ ⊤) (hb : f x ≠ ⊥) :
    y ∈ subgradient B f x ↔ ∀ v : E, ((B v y : ℝ) : EReal) ≤ dirDeriv f x v := by
  obtain ⟨r, hr⟩ := EReal.exists_coe_of_ne_bot_of_lt_top hb (lt_top_iff_ne_top.2 ht)
  constructor
  · intro h v
    refine le_dirDeriv fun a ha => ?_
    rw [hr, EReal.coe_le_sub_div_iff ha]
    have hv := h (x + a • v)
    rw [add_sub_cancel_left, hr, ← EReal.coe_add, map_smul, LinearMap.smul_apply,
      smul_eq_mul] at hv
    rwa [mul_comm (B v y) a]
  · intro h z
    have h1 := dirDeriv_le f x (z - x) one_pos
    rw [one_smul, show x + (z - x) = z from by abel] at h1
    have h2 := (h (z - x)).trans h1
    rw [hr, EReal.coe_le_sub_div_iff one_pos, mul_one, EReal.coe_add] at h2
    rw [hr]
    exact h2

/-- The support set of `f'(x; ·)` is the subdifferential. -/
theorem supportSet_dirDeriv (ht : f x ≠ ⊤) (hb : f x ≠ ⊥) :
    supportSet B (dirDeriv f x) = subgradient B f x :=
  Set.ext fun _ => (mem_subgradient_iff_le_dirDeriv ht hb).symm

/-- Dually, the conjugate of `f'(x; ·)` is the *indicator* of `∂f x`. Neither convexity of `f` nor
any topology is needed. -/
theorem conj_dirDeriv (ht : f x ≠ ⊤) (hb : f x ≠ ⊥) :
    conj B (dirDeriv f x) = indicatorFn (subgradient B f x) := by
  rw [conj_eq_indicatorFn_of_posHomogeneous (posHomogeneous_dirDeriv f x)
      ⟨0, by rw [dirDeriv_zero ht hb]; simp⟩,
    supportSet_dirDeriv ht hb]

end DirDerivSubgradient

/-! ### Conjugate subdifferentials, and the closure of the directional derivative

Everything here consumes Fenchel–Moreau, so it carries the pairing hypotheses of
`biconj_eq_clFn`. -/

section FenchelMoreau

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace E] [IsTopologicalAddGroup E] {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f : E → EReal}
  {x : E} {y : F}

/-- `∂(cl f) x = ∂f x` wherever `(cl f) x = f x`. Only continuity of the pairing is needed,
through `conj_clFn`. -/
theorem mem_subgradient_clFn_iff [IsContinuousPairing B] (hx : clFn f x = f x) :
    y ∈ subgradient B (clFn f) x ↔ y ∈ subgradient B f x := by
  rw [mem_subgradient_iff_conj_le, mem_subgradient_iff_conj_le, conj_clFn, hx]

variable [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]

/-- Pointwise inversion: for a closed proper convex `f`, `x ∈ ∂f* y` and `y ∈ ∂f x` say the same
thing. -/
theorem mem_subgradient_conj_iff_of_closedFn [IsCompatiblePairing B] (hf : ConvexFn f)
    (hc : ClosedFn f) :
    x ∈ subgradient B.flip (conj B f) y ↔ y ∈ subgradient B f x :=
  mem_subgradient_conj_iff (congrFun (biconj_eq_self hf hc) x)

/-- For a closed proper convex `f`, `∂f*` is the inverse of `∂f` as a multivalued mapping — the
graph of `∂f*` is the flip of the graph of `∂f`. -/
theorem subgradientRel_conj_eq_inv [IsCompatiblePairing B] (hf : ConvexFn f) (hc : ClosedFn f) :
    subgradientRel B.flip (conj B f) = (subgradientRel B f).inv := by
  ext ⟨y, x⟩
  simp only [SetRel.mem_inv, mem_subgradientRel]
  exact mem_subgradient_conj_iff_of_closedFn hf hc

/-- At a point where a convex `f` is subdifferentiable, `(cl f) x = f x`. -/
theorem clFn_eq_of_mem_subgradient [IsCompatiblePairing B] (hf : ConvexFn f)
    (hy : y ∈ subgradient B f x) : clFn f x = f x := by
  rw [← congrFun (biconj_eq_clFn (B := B) hf) x]
  exact biconj_eq_of_mem_subgradient hy

/-- And then `∂(cl f) x = ∂f x`. -/
theorem subgradient_clFn [IsCompatiblePairing B] (hf : ConvexFn f)
    (hy : y ∈ subgradient B f x) : subgradient B (clFn f) x = subgradient B f x :=
  Set.ext fun _ => mem_subgradient_clFn_iff (clFn_eq_of_mem_subgradient hf hy)

/-- For a nonempty closed convex set `C`, the subgradients at `y` of the support function
`δ*(· | C) = δ(· | C)*` are exactly the points of `C` at which `⟨·, y⟩` attains its maximum over
`C`. -/
theorem subgradient_conj_indicatorFn [IsCompatiblePairing B] {C : Set E} (hC : IsClosed C)
    (hCc : Convex ℝ C) (hCne : C.Nonempty) (y : F) :
    subgradient B.flip (conj B (indicatorFn C)) y = {x ∈ C | ∀ z ∈ C, B z y ≤ B x y} := by
  ext x
  have hbi := congrFun (biconj_eq_self (B := B) (convexFn_indicatorFn.2 hCc)
    (closedFn_indicatorFn hC)) x
  rw [mem_subgradient_conj_iff hbi, mem_subgradient_indicatorFn_iff hCne, Set.mem_sep_iff]
  refine and_congr_right fun _ => ?_
  simp only [mem_normalCone]
  exact forall₂_congr fun z _ => by rw [map_sub, LinearMap.sub_apply, sub_nonpos]

/-- The same in terms of `supportFn`: `∂δ*(· | C) y` is the face of `C` on which `⟨·, y⟩` is
maximized. -/
theorem subgradient_supportFn [IsCompatiblePairing B] {C : Set E} (hC : IsClosed C)
    (hCc : Convex ℝ C) (hCne : C.Nonempty) (y : F) :
    subgradient B.flip (supportFn B C) y = {x ∈ C | ∀ z ∈ C, B z y ≤ B x y} := by
  rw [supportFn_eq_conj_indicatorFn]
  exact subgradient_conj_indicatorFn hC hCc hCne y

/-- The closure of `f'(x; ·)` is the support function of `∂f x`, the conjugate of `f'(x; ·)`
being the indicator of that set. -/
theorem clFn_dirDeriv [IsCompatiblePairing B] (hf : ConvexFn f) (ht : f x ≠ ⊤) (hb : f x ≠ ⊥) :
    clFn (dirDeriv f x) = supportFn B.flip (subgradient B f x) := by
  rw [supportFn_eq_conj_indicatorFn, ← conj_dirDeriv ht hb]
  exact (biconj_eq_clFn (convexFn_dirDeriv hf ht hb)).symm

end FenchelMoreau

end ConvexAnalysis
