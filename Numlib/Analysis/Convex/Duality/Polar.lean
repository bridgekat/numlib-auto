import Mathlib.Geometry.Convex.Cone.Dual
import Numlib.Analysis.Convex.Duality.Support
import Numlib.Order.GaloisConnection

/-!
# Polars of convex sets and convex cones

The **polar** of a convex cone `K` is `K° = {y ∣ ∀ x ∈ K, ⟨x, y⟩ ≤ 0}`, and the polar of a convex
set `C` containing the origin is `C° = {y ∣ ∀ x ∈ C, ⟨x, y⟩ ≤ 1}`. Polarity is what conjugacy
becomes on indicator functions: the indicator of a cone is positively homogeneous, so its conjugate
is again an indicator, and the set it indicates is the polar. The bipolar theorem `K°° = cl K`
follows from that together with separation. The further polarity theorems need the recession
function or the gauge and are proved in `Recession/Conjugate.lean`, `Duality/HomConePolar.lean`,
`Duality/Level.lean`, `Duality/Gauge.lean` and `Duality/PolarBounded.lean`.

## Main definitions

* `polarCone B K`, `polarSet B C` — the two polars above; `polarPointedCone B K` bundles the first
  as a `PointedCone ℝ F` and `polarSubmodule B M` bundles the polar of a subspace.
* `gc_polarCone_polarCone`, `polarConeClosure` — polarity as an antitone Galois connection between
  `Set E` and `Set F`, and the closure operator `K ↦ K°°` it induces; likewise
  `gc_polarSet_polarSet` and `polarSetClosure`.

## Main results

* `isClosed_polarCone`, `polarPointedCone`, `polarCone_polarCone`,
  `conj_indicatorFn_eq_indicatorFn_polarCone` — the three assertions of the **bipolar theorem**
  (Theorem 14.1 in [^1]): `K°` is a nonempty closed convex cone for *any* `K`; `K°° = cl K` for a
  nonempty convex cone; and the indicator functions of `K` and `K°` are conjugate.
  `neg_polarCone_neg_polarCone` is `K** = K` for the *dual* cone `K* = -K°`.
* `polarSet_polarSet` — `C°° = C` for a closed convex `C` containing the origin
  (Theorem 14.5 in [^1]).
* `polarCone_eq_setOf_supportFn_le_zero` — the polar is the zero sublevel set of the support
  function, for an arbitrary set: this is what turns a theorem computing a support function into a
  theorem computing a polar.
* `polarSet_closure`, `polarSet_union`, `polarSet_convexHull`, `polarSet_smul`, `polarCone_add` —
  the lattice and scaling identities. A polar is an intersection of closed half-spaces, so polarity
  does not see the convex hull.
* `polarCone_coe_submodule`, `polarCone_hull_range`, `polarCone_setOf_forall_le_zero`,
  `polarCone_nonnegOrthant` — the standard examples: the polar of a subspace is its annihilator,
  the polar of a generated cone is the solution set of the corresponding homogeneous inequalities
  and conversely, and the polar of the nonnegative orthant is the nonpositive orthant.
* `conj_partialAffineFn` — the conjugate of a partial affine function,
  `(δ(· ∣ L + a) + ⟨·, a*⟩ + α)* = δ(· ∣ L^⊥ + a*) + ⟨a, ·⟩ + α*`.

## Implementation notes

Every bipolar statement takes `Convex ℝ K`, `∀ a > 0, a • K = K` and `K.Nonempty` separately,
because that is the generality in which the separation argument runs; a `PointedCone ℝ E` supplies
all three, and each statement has a `_pointedCone` companion. `K°° = cl K`, not `K°° = K`, is the
theorem, and nonemptiness of `K` is genuinely needed: `∅° = F`, and `F°` is the kernel of the
pairing rather than `cl ∅ = ∅`. The adjunction `L ⊆ K° ↔ K ⊆ L°` makes `K ↦ K°°` a
`ClosureOperator (Set E)`, with the `OrderDual` on the *codomain* rather than the domain because
the indicator embedding `s ↦ δ(· ∣ s)` is antitone.

Two Mathlib objects are close but different. `PointedCone.dual` is the *inner* dual, so
`K° = -(Kᵛ)` (`polarPointedCone_eq_dual_neg`); the bipolar theorem proved here asks for
`IsCompatiblePairing` rather than a perfect pairing, and closedness of the polar needs only
`IsContinuousPairing`. `LinearMap.polar` is the **absolute** polar, which agrees with `polarSet`
exactly on balanced sets (`polarSet_eq_polar_of_balanced`).

## References

[^1]: R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §14.
-/

open Set Pointwise

namespace ConvexAnalysis

/-! ### Definitions -/

section Defs

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

/-- **The polar of a convex cone**: `K° = {y | ∀ x ∈ K, ⟨x, y⟩ ≤ 0}`. This is a *one-sided* polar,
neither Mathlib's absolute polar `LinearMap.polar` nor its inner dual cone, of which it is the
negative (`polarPointedCone_eq_dual_neg`). -/
def polarCone (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (K : Set E) : Set F := {y | ∀ x ∈ K, B x y ≤ 0}

/-- **Rockafellar's polar of a convex set containing the origin**:
`C° = {y | ∀ x ∈ C, ⟨x, y⟩ ≤ 1}`. -/
def polarSet (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (C : Set E) : Set F := {y | ∀ x ∈ C, B x y ≤ 1}

variable {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {K L : Set E} {C D : Set E} {y : F}

@[simp] theorem mem_polarCone : y ∈ polarCone B K ↔ ∀ x ∈ K, B x y ≤ 0 := Iff.rfl

@[simp] theorem mem_polarSet : y ∈ polarSet B C ↔ ∀ x ∈ C, B x y ≤ 1 := Iff.rfl

theorem polarCone_anti (h : K ⊆ L) : polarCone B L ⊆ polarCone B K := fun _ hy x hx => hy x (h hx)

theorem polarSet_anti (h : C ⊆ D) : polarSet B D ⊆ polarSet B C := fun _ hy x hx => hy x (h hx)

@[simp] theorem polarCone_empty (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) :
    polarCone B (∅ : Set E) = univ := by ext y; simp

@[simp] theorem polarSet_empty (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) :
    polarSet B (∅ : Set E) = univ := by ext y; simp

@[simp] theorem zero_mem_polarCone (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (K : Set E) :
    (0 : F) ∈ polarCone B K := fun x _ => by simp

@[simp] theorem zero_mem_polarSet (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (C : Set E) :
    (0 : F) ∈ polarSet B C := fun x _ => by simp

theorem polarCone_nonempty (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (K : Set E) : (polarCone B K).Nonempty :=
  ⟨0, zero_mem_polarCone B K⟩

/-- The polar cone is contained in the polar set, since `0 ≤ 1`. -/
theorem polarCone_subset_polarSet : polarCone B K ⊆ polarSet B K :=
  fun _ hy x hx => (hy x hx).trans zero_le_one

theorem polarCone_union (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (K L : Set E) :
    polarCone B (K ∪ L) = polarCone B K ∩ polarCone B L := by
  ext y; exact ⟨fun h => ⟨fun x hx => h x (Or.inl hx), fun x hx => h x (Or.inr hx)⟩,
    fun h x hx => hx.elim (h.1 x) (h.2 x)⟩

theorem polarCone_iUnion {ι : Sort*} (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (u : ι → Set E) :
    polarCone B (⋃ i, u i) = ⋂ i, polarCone B (u i) := by
  ext y
  simp only [mem_polarCone, Set.mem_iInter, Set.mem_iUnion]
  exact ⟨fun h i x hx => h x ⟨i, hx⟩, fun h x hx => hx.elim fun i hi => h i x hi⟩

theorem polarSet_union (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (C D : Set E) :
    polarSet B (C ∪ D) = polarSet B C ∩ polarSet B D := by
  ext y
  simp only [polarSet, Set.mem_ofPred, Set.mem_inter_iff, Set.mem_union]
  exact ⟨fun h => ⟨fun x hx => h x (Or.inl hx), fun x hx => h x (Or.inr hx)⟩,
    fun h x hx => hx.elim (h.1 x) (h.2 x)⟩

theorem polarSet_iUnion {ι : Sort*} (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (u : ι → Set E) :
    polarSet B (⋃ i, u i) = ⋂ i, polarSet B (u i) := by
  ext y
  simp only [polarSet, Set.mem_ofPred, Set.mem_iInter, Set.mem_iUnion]
  exact ⟨fun h i x hx => h x ⟨i, hx⟩, fun h x hx => hx.elim fun i hi => h i x hi⟩


/-- **For a cone the two polars coincide**, because the half-space `{x | ⟨x, y⟩ ≤ 1}` contains a
cone exactly when `{x | ⟨x, y⟩ ≤ 0}` does. -/
theorem polarCone_eq_polarSet_of_isCone (hK : ∀ a : ℝ, 0 < a → a • K = K) :
    polarCone B K = polarSet B K := by
  refine subset_antisymm polarCone_subset_polarSet fun y hy x hx => ?_
  by_contra hcon
  rw [not_le] at hcon
  have hmem : (2 / B x y) • x ∈ K :=
    (smul_mem_iff_of_isCone hK (by positivity)).2 hx
  have h := hy _ hmem
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul, div_mul_cancel₀ _ hcon.ne'] at h
  linarith

/-- **The polarity adjunction**: `L ⊆ K°` and `K ⊆ L°` both say that `⟨x, y⟩ ≤ 0` for every
`x ∈ K` and `y ∈ L`. -/
theorem subset_polarCone_comm {L : Set F} : L ⊆ polarCone B K ↔ K ⊆ polarCone B.flip L :=
  ⟨fun h _ hx _ hy => h hy _ hx, fun h _ hy _ hx => h hx _ hy⟩

theorem subset_polarSet_comm {L : Set F} : L ⊆ polarSet B C ↔ C ⊆ polarSet B.flip L :=
  ⟨fun h _ hx _ hy => h hy _ hx, fun h _ hy _ hx => h hx _ hy⟩

/-- **The unit of the polarity adjunction**: every set is contained in its bipolar. -/
theorem subset_polarCone_polarCone (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (K : Set E) :
    K ⊆ polarCone B.flip (polarCone B K) := subset_polarCone_comm.1 (subset_refl _)

theorem subset_polarSet_polarSet (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (C : Set E) :
    C ⊆ polarSet B.flip (polarSet B C) := subset_polarSet_comm.1 (subset_refl _)

/-! ### Polarity as a Galois connection -/

/-- **Polarity of cones is an antitone Galois connection** between `Set E` and `Set F`. -/
theorem gc_polarCone_polarCone (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) :
    GaloisConnection (fun K : Set E => OrderDual.toDual (polarCone B K))
      (fun L : (Set F)ᵒᵈ => polarCone B.flip (OrderDual.ofDual L)) :=
  fun _ _ => subset_polarCone_comm

/-- **Polarity of sets is an antitone Galois connection** between `Set E` and `Set F`. -/
theorem gc_polarSet_polarSet (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) :
    GaloisConnection (fun C : Set E => OrderDual.toDual (polarSet B C))
      (fun L : (Set F)ᵒᵈ => polarSet B.flip (OrderDual.ofDual L)) :=
  fun _ _ => subset_polarSet_comm

/-- The bipolar operator `K ↦ K°°` as a `ClosureOperator` on `Set E`. Its closed elements are, by
`polarCone_polarCone_of_isClosed`, the nonempty closed convex cones. -/
def polarConeClosure (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) : ClosureOperator (Set E) :=
  (gc_polarCone_polarCone B).closureOperator

@[simp] theorem polarConeClosure_apply (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (K : Set E) :
    polarConeClosure B K = polarCone B.flip (polarCone B K) := rfl

theorem isClosed_polarConeClosure_iff :
    (polarConeClosure B).IsClosed K ↔ polarCone B.flip (polarCone B K) = K := Iff.rfl

/-- The bipolar operator `C ↦ C°°` as a `ClosureOperator` on `Set E`. Its closed elements are, by
`polarSet_polarSet`, the closed convex sets containing the origin. -/
def polarSetClosure (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) : ClosureOperator (Set E) :=
  (gc_polarSet_polarSet B).closureOperator

@[simp] theorem polarSetClosure_apply (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (C : Set E) :
    polarSetClosure B C = polarSet B.flip (polarSet B C) := rfl

theorem isClosed_polarSetClosure_iff :
    (polarSetClosure B).IsClosed C ↔ polarSet B.flip (polarSet B C) = C := Iff.rfl

/-- **Polarity is unchanged by taking the bipolar first** — the triangle identity of the
adjunction, and Rockafellar's `(cl K)° = K°` in its purely algebraic form. -/
theorem polarCone_polarCone_polarCone (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (K : Set E) :
    polarCone B (polarCone B.flip (polarCone B K)) = polarCone B K :=
  subset_antisymm (polarCone_anti (subset_polarCone_polarCone B K))
    (subset_polarCone_comm.2 (subset_refl _))

/-- **Polarity is an order anti-isomorphism between the bipolar-closed sets.** The bipolar theorem
with its order structure and with no topology; once `E` and `F` carry compatible topologies the
bipolar-closed sets are exactly the closed convex cones containing the origin. -/
def polarConeOrderIso (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) :
    {K : Set E // polarCone B.flip (polarCone B K) = K} ≃o
      {L : (Set F)ᵒᵈ //
        OrderDual.toDual (polarCone B (polarCone B.flip (OrderDual.ofDual L))) = L} :=
  (gc_polarCone_polarCone B).closedsOrderIso

/-- The same for polars of sets, in order form. -/
def polarSetOrderIso (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) :
    {C : Set E // polarSet B.flip (polarSet B C) = C} ≃o
      {L : (Set F)ᵒᵈ //
        OrderDual.toDual (polarSet B (polarSet B.flip (OrderDual.ofDual L))) = L} :=
  (gc_polarSet_polarSet B).closedsOrderIso

/-! ### The polar cone as a `PointedCone` -/

/-- **The polar of an arbitrary set is a pointed convex cone** — the first assertion of the
bipolar theorem, before any topology enters. Bundling it makes the `PointedCone` API available. -/
def polarPointedCone (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (K : Set E) : PointedCone ℝ F where
  carrier := polarCone B K
  zero_mem' := zero_mem_polarCone B K
  add_mem' {u v} hu hv x hx := by
    rw [map_add]
    exact add_nonpos (hu x hx) (hv x hx)
  smul_mem' c u hu x hx := by
    rw [← Nonneg.coe_smul, map_smul, smul_eq_mul]
    calc (c : ℝ) * B x u ≤ (c : ℝ) * 0 := mul_le_mul_of_nonneg_left (hu x hx) c.2
      _ = 0 := mul_zero _

@[simp] theorem coe_polarPointedCone (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (K : Set E) :
    (polarPointedCone B K : Set F) = polarCone B K := rfl

@[simp] theorem mem_polarPointedCone : y ∈ polarPointedCone B K ↔ ∀ x ∈ K, B x y ≤ 0 := Iff.rfl

theorem convex_polarCone (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (K : Set E) : Convex ℝ (polarCone B K) :=
  ((polarPointedCone B K : ConvexCone ℝ F)).convex

theorem convex_polarSet (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (C : Set E) : Convex ℝ (polarSet B C) := by
  intro y hy z hz a b ha hb hab x hx
  have h1 := hy x hx
  have h2 := hz x hx
  simp only [map_add, map_smul, smul_eq_mul]
  nlinarith

/-- **A closed half-space of the pairing is convex**, in the real-valued form that cuts out a polar
set; `convex_setOf_pairing_le` is the `EReal` form. -/
theorem convex_setOf_pairing_le_coe (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (y : F) (c : ℝ) :
    Convex ℝ {x : E | B x y ≤ c} := by
  intro u hu v hv a b ha hb hab
  have hu' : B u y ≤ c := hu
  have hv' : B v y ≤ c := hv
  have : B (a • u + b • v) y = a * B u y + b * B v y := by
    simp [map_add, map_smul, smul_eq_mul]
  change B (a • u + b • v) y ≤ c
  rw [this]
  calc a * B u y + b * B v y ≤ a * c + b * c := by
        exact add_le_add (mul_le_mul_of_nonneg_left hu' ha) (mul_le_mul_of_nonneg_left hv' hb)
    _ = c := by rw [← add_mul, hab, one_mul]

/-- **Polarity does not see the convex hull**: the polar is cut out by the convex half-spaces
`{x | ⟨x, y⟩ ≤ 1}`. The `polarCone` counterpart is `polarCone_hull`. -/
@[simp] theorem polarSet_convexHull (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (C : Set E) :
    polarSet B (convexHull ℝ C) = polarSet B C := by
  refine Set.Subset.antisymm (polarSet_anti (subset_convexHull ℝ C)) fun y hy => ?_
  exact fun x hx => convexHull_min (fun z hz => (hy z hz : B z y ≤ 1))
    (convex_setOf_pairing_le_coe B y 1) hx

/-- **Dilating a set inverts the dilation of its polar**: `(aC)° = a⁻¹ C°` for `a > 0`. -/
theorem polarSet_smul (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) {a : ℝ} (ha : 0 < a) (C : Set E) :
    polarSet B (a • C) = a⁻¹ • polarSet B C := by
  have key : ∀ (c : ℝ) (x : E) (z : F), B (c • x) z = B x (c • z) := fun c x z => by
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  ext y
  constructor
  · intro hy
    refine ⟨a • y, fun x hx => ?_, inv_smul_smul₀ ha.ne' y⟩
    have h := hy (a • x) ⟨x, hx, rfl⟩
    rwa [key] at h
  · rintro ⟨z, hz, rfl⟩ _ ⟨x, hx, rfl⟩
    have h := hz x hx
    have hval : B (a • x) (a⁻¹ • z) = B x z := by
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
      rw [← mul_assoc, inv_mul_cancel₀ ha.ne', one_mul]
    rw [hval]
    exact h

/-- **The polar of a sum is the intersection of the polars**, for sets containing the origin —
the additive counterpart of `polarCone_union`. -/
theorem polarCone_add (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) {K L : Set E} (hK : (0 : E) ∈ K)
    (hL : (0 : E) ∈ L) : polarCone B (K + L) = polarCone B K ∩ polarCone B L := by
  refine Set.Subset.antisymm (fun y hy => ⟨fun x hx => ?_, fun x hx => ?_⟩) ?_
  · simpa using hy (x + 0) ⟨x, hx, 0, hL, rfl⟩
  · simpa using hy (0 + x) ⟨0, hK, x, hx, rfl⟩
  · rintro y ⟨h₁, h₂⟩ _ ⟨x₁, hx₁, x₂, hx₂, rfl⟩
    have hsum : B (x₁ + x₂) y = B x₁ y + B x₂ y := by simp
    change B (x₁ + x₂) y ≤ 0
    rw [hsum]
    simpa using add_le_add (h₁ x₁ hx₁) (h₂ x₂ hx₂)

theorem smul_coe_pointedCone (K : PointedCone ℝ E) (a : ℝ) (ha : 0 < a) :
    a • (K : Set E) = (K : Set E) := by
  ext x
  refine ⟨?_, fun hx => ⟨a⁻¹ • x, K.smul_mem (inv_pos.2 ha).le hx, smul_inv_smul₀ ha.ne' x⟩⟩
  rintro ⟨z, hz, rfl⟩
  exact K.smul_mem ha.le hz

theorem smul_coe_submodule (M : Submodule ℝ E) {a : ℝ} (ha : 0 < a) :
    a • (M : Set E) = (M : Set E) := by
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact M.smul_mem a hu
  · intro hz
    refine ⟨a⁻¹ • z, M.smul_mem _ hz, ?_⟩
    change a • a⁻¹ • z = z
    rw [smul_smul, mul_inv_cancel₀ ha.ne', one_smul]

theorem smul_polarCone (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (K : Set E) (a : ℝ) (ha : 0 < a) :
    a • polarCone B K = polarCone B K := smul_coe_pointedCone (polarPointedCone B K) a ha

/-- **Negating the cone negates its polar**: `(-K)° = -(K°)`. With the bipolar theorem this makes
the dual cone `K* = -K°` an involution (`neg_polarCone_neg_polarCone`). -/
theorem polarCone_neg (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (K : Set E) :
    polarCone B (-K) = -(polarCone B K) := by
  ext y
  rw [Set.mem_neg, mem_polarCone, mem_polarCone]
  refine ⟨fun hy u hu => ?_, fun hy x hx => ?_⟩
  · have h := hy (-u) (Set.mem_neg.2 (by rwa [neg_neg]))
    rw [map_neg B u, LinearMap.neg_apply] at h
    rwa [map_neg (B u) y]
  · have h := hy (-x) (Set.mem_neg.1 hx)
    rwa [map_neg B x, LinearMap.neg_apply, map_neg (B x) y, neg_neg] at h

theorem smul_neg_polarCone (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (K : Set E) (a : ℝ) (ha : 0 < a) :
    a • (-(polarCone B K)) = -(polarCone B K) := by
  rw [← polarCone_neg]
  exact smul_polarCone B (-K) a ha

theorem zero_mem_neg_polarCone (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (K : Set E) :
    (0 : F) ∈ -(polarCone B K) := by
  rw [Set.mem_neg, neg_zero, mem_polarCone]
  exact fun x _ => le_of_eq (map_zero (B x))

theorem neg_polarCone_nonempty (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (K : Set E) :
    (-(polarCone B K)).Nonempty := ⟨0, zero_mem_neg_polarCone B K⟩

theorem convex_neg_polarCone (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (K : Set E) :
    Convex ℝ (-(polarCone B K)) := (convex_polarCone B K).neg

/-! ### Bridges to Mathlib -/

/-- **Mathlib's dual cone is the inner one.** `PointedCone.dual B s = {y | ∀ x ∈ s, 0 ≤ ⟨x, y⟩}`, so
Rockafellar's polar is its negative — equivalently, the dual of `-K`. -/
theorem polarPointedCone_eq_dual_neg (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (K : Set E) :
    polarPointedCone B K = PointedCone.dual B (-K) := by
  ext y
  simp only [mem_polarPointedCone, PointedCone.mem_dual, Set.mem_neg]
  constructor
  · intro h x hx
    have hx' := h (-x) hx
    rw [map_neg, LinearMap.neg_apply] at hx'
    linarith
  · intro h x hx
    have hx' := h (x := -x) (by simpa using hx)
    rw [map_neg, LinearMap.neg_apply] at hx'
    linarith

theorem polarCone_eq_neg_dual (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (K : Set E) :
    polarCone B K = -(PointedCone.dual B K : Set F) := by
  rw [← coe_polarPointedCone, polarPointedCone_eq_dual_neg]
  exact congrArg _ (PointedCone.dual_neg (p := B) (s := K))

/-- **Mathlib's `LinearMap.polar` is the absolute polar** `{y | ∀ x ∈ C, ‖⟨x, y⟩‖ ≤ 1}`. It agrees
with Rockafellar's one-sided polar exactly on balanced sets, where `x ∈ C` implies `-x ∈ C`. -/
theorem polarSet_eq_polar_of_balanced (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) {C : Set E} (hC : Balanced ℝ C) :
    polarSet B C = B.polar C := by
  ext y
  simp only [mem_polarSet, LinearMap.polar_mem_iff, Real.norm_eq_abs]
  refine ⟨fun h x hx => abs_le.2 ⟨?_, h x hx⟩, fun h x hx => (le_abs_self _).trans (h x hx)⟩
  have hneg : -x ∈ C := by
    have := hC (-1 : ℝ) (by norm_num)
    exact this ⟨x, hx, by simp⟩
  have := h (-x) hneg
  rw [map_neg, LinearMap.neg_apply] at this
  linarith

end Defs

/-! ### The polar cone and the conjugate of an indicator

This computation needs no topology: the indicator of a
cone is positively homogeneous, so its conjugate is again an indicator
(`conj_eq_indicatorFn_of_posHomogeneous`), and the set it indicates is the polar. -/

section Indicator

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {K : Set E}

/-- The set that the conjugate of an indicator function indicates is the polar cone. -/
@[simp] theorem supportSet_indicatorFn (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (K : Set E) :
    supportSet B (indicatorFn K) = polarCone B K := by
  ext y
  simp only [mem_supportSet, mem_polarCone]
  refine ⟨fun h x hx => ?_, fun h x => ?_⟩
  · have hx' := h x
    rw [indicatorFn_of_mem hx] at hx'
    exact_mod_cast hx'
  · by_cases hx : x ∈ K
    · rw [indicatorFn_of_mem hx]
      exact_mod_cast h x hx
    · rw [indicatorFn_of_notMem hx]
      exact le_top

/-- **The indicator functions of a nonempty convex cone and of its polar are conjugate** to each
other. -/
theorem conj_indicatorFn_eq_indicatorFn_polarCone (hK : ∀ a : ℝ, 0 < a → a • K = K)
    (hne : K.Nonempty) : conj B (indicatorFn K) = indicatorFn (polarCone B K) := by
  obtain ⟨x₀, hx₀⟩ := hne
  rw [← supportSet_indicatorFn]
  exact conj_eq_indicatorFn_of_posHomogeneous (posHomogeneous_indicatorFn.2 hK)
    ⟨x₀, by rw [indicatorFn_of_mem hx₀]; simp⟩

/-- **The support function of a nonempty convex cone is the indicator of its polar.** -/
theorem supportFn_eq_indicatorFn_polarCone (hK : ∀ a : ℝ, 0 < a → a • K = K) (hne : K.Nonempty) :
    supportFn B K = indicatorFn (polarCone B K) := by
  rw [supportFn_eq_conj_indicatorFn]
  exact conj_indicatorFn_eq_indicatorFn_polarCone hK hne

/-- **The polar is the zero sublevel set of the support function**: `⟨x, y⟩ ≤ 0` for every `x ∈ K`
says exactly that `δ*(y | K) ≤ 0`. Holds for an arbitrary set `K`, and is what turns a theorem
computing a support function into a theorem computing a polar. -/
theorem polarCone_eq_setOf_supportFn_le_zero (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (K : Set E) :
    polarCone B K = {y : F | supportFn B K y ≤ 0} := by
  ext y
  exact supportFn_le_zero_iff.symm

end Indicator

/-! ### Closedness of the polar -/

section Closed

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace F] {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} [IsContinuousPairing B.flip] {K C : Set E}

/-- **The polar of any set is closed**, being an intersection of homogeneous closed
half-spaces. -/
theorem isClosed_polarCone : IsClosed (polarCone B K) := by
  have h : polarCone B K = ⋂ x ∈ K, {y : F | B x y ≤ 0} := by ext y; simp [polarCone]
  rw [h]
  exact isClosed_biInter fun x _ => isClosed_le (continuous_pairing B.flip x) continuous_const

theorem isClosed_polarSet : IsClosed (polarSet B C) := by
  have h : polarSet B C = ⋂ x ∈ C, {y : F | B x y ≤ 1} := by ext y; simp [polarSet]
  rw [h]
  exact isClosed_biInter fun x _ => isClosed_le (continuous_pairing B.flip x) continuous_const

end Closed

section ClosureDomain

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace E] {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} [IsContinuousPairing B]

/-- **The polar does not see the closure**: `(cl K)° = K°`. -/
theorem polarCone_closure (K : Set E) : polarCone (B := B) (closure K) = polarCone B K := by
  refine subset_antisymm (polarCone_anti subset_closure) fun y hy x hx => ?_
  exact closure_minimal (fun z hz => hy z hz)
    (isClosed_le (continuous_pairing B y) continuous_const) hx

/-- **The polar does not see the closure**, in the `polarSet` sense — the companion of
`polarCone_closure`. -/
theorem polarSet_closure (C : Set E) : polarSet (B := B) (closure C) = polarSet B C := by
  refine subset_antisymm (polarSet_anti subset_closure) fun y hy x hx => ?_
  exact closure_minimal (fun z hz => hy z hz)
    (isClosed_le (continuous_pairing B y) continuous_const) hx

end ClosureDomain

/-! ### The bipolar theorem

Separation supplies the only nontrivial half. -/

section BipolarCone

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} [IsCompatiblePairing B] {K : Set E}

/-- **The bipolar of a nonempty convex cone is its *closure*.**

A point outside `cl K` is strongly separated from it by a continuous linear functional; because
`cl K` is a nonempty cone, that functional is `≤ 0` on it and the separating constant is
nonnegative, so the `y` representing it lies in `K°` and detects the point. -/
theorem polarCone_polarCone (hconv : Convex ℝ K) (hcone : ∀ a : ℝ, 0 < a → a • K = K)
    (hne : K.Nonempty) :
    polarCone B.flip (polarCone B K) = closure K := by
  have hmem : ∀ ⦃a : ℝ⦄, 0 < a → ∀ ⦃x⦄, x ∈ K → a • x ∈ K :=
    fun _ ha _ hx => (smul_mem_iff_of_isCone hcone ha).2 hx
  refine subset_antisymm (fun x hx => ?_) ?_
  · by_contra hcon
    obtain ⟨f, u, hfK, hfx⟩ :=
      geometric_hahn_banach_closed_point hconv.closure isClosed_closure hcon
    have hbdd : ∀ z ∈ closure K, f z ≤ u := fun z hz => (hfK z hz).le
    have hle : ∀ z ∈ K, f z ≤ 0 := fun z hz =>
      le_zero_of_isCone_of_forall_le (smul_mem_closure_of_isCone hmem) hbdd (subset_closure hz)
    have hu : 0 ≤ u := nonneg_of_isCone_of_forall_le (smul_mem_closure_of_isCone hmem) hbdd
      (hne.mono subset_closure)
    obtain ⟨y, hy⟩ := exists_pairing_eq B f
    have hyK : y ∈ polarCone B K := fun z hz => hy z ▸ hle z hz
    have := hx y hyK
    rw [LinearMap.flip_apply, ← hy x] at this
    linarith
  · exact closure_minimal (subset_polarCone_polarCone B K) (isClosed_polarCone (B := B.flip))

/-- For a nonempty *closed* convex cone the polarity correspondence is an involution:
`K°° = K`. -/
theorem polarCone_polarCone_of_isClosed (hconv : Convex ℝ K)
    (hcone : ∀ a : ℝ, 0 < a → a • K = K) (hne : K.Nonempty) (hcl : IsClosed K) :
    polarCone B.flip (polarCone B K) = K :=
  (polarCone_polarCone hconv hcone hne).trans hcl.closure_eq

/-- The same for a bundled cone: for a closed `PointedCone`, `K°° = K`. All three hypotheses of
the previous statement are supplied by the bundling. -/
theorem polarCone_polarCone_pointedCone (K : PointedCone ℝ E) (hcl : IsClosed (K : Set E)) :
    polarCone B.flip (polarCone B (K : Set E)) = (K : Set E) :=
  polarCone_polarCone_of_isClosed (K : ConvexCone ℝ E).convex
    (smul_coe_pointedCone K) ⟨0, K.zero_mem⟩ hcl

theorem polarCone_polarCone_pointedCone_eq_closure (K : PointedCone ℝ E) :
    polarCone B.flip (polarCone B (K : Set E)) = closure (K : Set E) :=
  polarCone_polarCone (K : ConvexCone ℝ E).convex (smul_coe_pointedCone K) ⟨0, K.zero_mem⟩

/-- The bipolar theorem in its dual-cone form: `K** = K` for a nonempty closed convex cone, where
`K* = -K°` is the dual cone. -/
theorem neg_polarCone_neg_polarCone (hconv : Convex ℝ K)
    (hcone : ∀ a : ℝ, 0 < a → a • K = K) (hne : K.Nonempty) (hcl : IsClosed K) :
    -(polarCone B.flip (-(polarCone B K))) = K := by
  rw [polarCone_neg, neg_neg, polarCone_polarCone_of_isClosed hconv hcone hne hcl]

theorem neg_polarCone_neg_polarCone_pointedCone (K : PointedCone ℝ E)
    (hcl : IsClosed (K : Set E)) :
    -(polarCone B.flip (-(polarCone B (K : Set E)))) = (K : Set E) :=
  neg_polarCone_neg_polarCone (K : ConvexCone ℝ E).convex (smul_coe_pointedCone K)
    ⟨0, K.zero_mem⟩ hcl

/-- The conjugacy of indicators in the remaining direction: for a nonempty closed convex cone the
indicator of `K°` conjugates back to the indicator of `K`. -/
theorem conj_indicatorFn_polarCone (hconv : Convex ℝ K)
    (hcone : ∀ a : ℝ, 0 < a → a • K = K) (hne : K.Nonempty) (hcl : IsClosed K) :
    conj B.flip (indicatorFn (polarCone B K)) = indicatorFn K := by
  rw [conj_indicatorFn_eq_indicatorFn_polarCone (B := B.flip) (smul_polarCone B K)
      (polarCone_nonempty B K),
    polarCone_polarCone_of_isClosed hconv hcone hne hcl]

theorem conj_indicatorFn_polarCone_pointedCone (K : PointedCone ℝ E)
    (hcl : IsClosed (K : Set E)) :
    conj B.flip (indicatorFn (polarCone B (K : Set E))) = indicatorFn (K : Set E) :=
  conj_indicatorFn_polarCone (K : ConvexCone ℝ E).convex (smul_coe_pointedCone K)
    ⟨0, K.zero_mem⟩ hcl

end BipolarCone

/-! ### The bipolar of a set containing the origin

`C°° = C` for a closed convex set containing the origin. The separation argument is the same as for
cones, with the constant normalised to `1` instead of `0`. -/

section BipolarSet

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} [IsCompatiblePairing B] {C : Set E}

/-- **The polar of a closed convex set containing the origin** is another such set, and `C°° = C`.
Containment of the origin is what makes the separating constant positive, so that the separating
functional can be rescaled to have value exactly `1`. -/
theorem polarSet_polarSet (hconv : Convex ℝ C) (hcl : IsClosed C) (h0 : (0 : E) ∈ C) :
    polarSet B.flip (polarSet B C) = C := by
  refine subset_antisymm (fun x hx => ?_) (subset_polarSet_polarSet B C)
  by_contra hcon
  obtain ⟨f, u, hfC, hfx⟩ := geometric_hahn_banach_closed_point hconv hcl hcon
  have hu : 0 < u := by simpa using hfC 0 h0
  obtain ⟨y, hy⟩ := exists_pairing_eq B f
  have hyC : u⁻¹ • y ∈ polarSet B C := by
    intro z hz
    rw [map_smul, smul_eq_mul, ← hy z]
    rw [inv_mul_le_iff₀ hu, mul_one]
    exact (hfC z hz).le
  have hxle := hx _ hyC
  rw [LinearMap.flip_apply, map_smul, smul_eq_mul, ← hy x, inv_mul_le_iff₀ hu, mul_one] at hxle
  linarith

theorem isClosed_polarSetClosure_of_isClosed (hconv : Convex ℝ C) (hcl : IsClosed C)
    (h0 : (0 : E) ∈ C) : (polarSetClosure B).IsClosed C :=
  isClosed_polarSetClosure_iff.2 (polarSet_polarSet hconv hcl h0)

end BipolarSet

/-! ### Examples -/

section Examples

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ}

/-- **The polar of a subspace is its annihilator** — the book's "orthogonally complementary
subspace". Under the pairing this is `Submodule.dualAnnihilator` pulled back along `B.flip`. -/
theorem polarCone_coe_submodule (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (M : Submodule ℝ E) :
    polarCone B (M : Set E) = (M.dualAnnihilator.comap B.flip : Set F) := by
  ext y
  simp only [mem_polarCone, SetLike.mem_coe, Submodule.mem_comap, Submodule.mem_dualAnnihilator,
    LinearMap.flip_apply]
  refine ⟨fun h x hx => le_antisymm (h x hx) ?_, fun h x hx => (h x hx).le⟩
  have := h (-x) (M.neg_mem hx)
  rw [map_neg, LinearMap.neg_apply] at this
  linarith

theorem polarCone_coe_submodule' (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (M : Submodule ℝ E) :
    polarCone B (M : Set E) = {y : F | ∀ x ∈ M, B x y = 0} := by
  rw [polarCone_coe_submodule]
  ext y
  simp

/-- The polar of a **subspace**, bundled as a submodule of `F`: the annihilator of `M` pulled back
along `B.flip`. Its carrier is `polarCone B M` (`polarCone_coe_submodule`). -/
noncomputable def polarSubmodule (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (M : Submodule ℝ E) : Submodule ℝ F :=
  M.dualAnnihilator.comap B.flip

@[simp] theorem coe_polarSubmodule (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (M : Submodule ℝ E) :
    (polarSubmodule B M : Set F) = polarCone B (M : Set E) :=
  (polarCone_coe_submodule B M).symm

/-- **The polar does not see the cone generated**: a polar cone cannot tell a set from the cone it
generates. -/
@[simp] theorem polarCone_hull (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (S : Set E) :
    polarCone B (PointedCone.hull ℝ S : Set E) = polarCone B S := by
  rw [polarCone_eq_neg_dual, polarCone_eq_neg_dual, PointedCone.dual_hull]

/-- **The polar of the convex cone generated by a family `aᵢ`** is the solution set of the
homogeneous inequalities `⟨aᵢ, y⟩ ≤ 0`. -/
theorem polarCone_hull_range {ι : Sort*} (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (a : ι → E) :
    polarCone B (PointedCone.hull ℝ (Set.range a) : Set E) = {y : F | ∀ i, B (a i) y ≤ 0} := by
  rw [polarCone_hull]
  ext y
  simp only [mem_polarCone, Set.mem_range, Set.mem_ofPred]
  exact ⟨fun h i => h (a i) ⟨i, rfl⟩, fun h _ ⟨i, hi⟩ => hi ▸ h i⟩

end Examples

/-! ### Partial affine functions

A *partial affine function* is a proper convex function whose effective domain is an affine set and
which is affine on it; every such function is `δ(· | L + a) + ⟨·, a*⟩ + α` for a subspace `L`.
Conjugacy exchanges `L` with its polar, `a` with `a*`, and `α` with `-α - ⟨a, a*⟩`, so partial
affine functions, like subspaces, come in dual pairs. The formula is the conjugacy rule for
`h(Ax) + ⟨x, b⟩ + α` at `h = δ(· | L)`, fed by `conj_indicatorFn_eq_indicatorFn_polarCone`. -/

section PartialAffine

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

/-- **A partial affine function** in Rockafellar's normal form: `δ(· | L + a) + ⟨·, b⟩ + α`, for a
subspace `L`, vectors `a` and `b`, and a real `α`. -/
noncomputable def partialAffineFn (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (L : Submodule ℝ E) (a : E) (b : F)
    (α : ℝ) : E → EReal :=
  fun x => indicatorFn (a +ᵥ (L : Set E)) x + ((B x b : ℝ) : EReal) + (α : EReal)

theorem partialAffineFn_apply (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (L : Submodule ℝ E) (a : E) (b : F)
    (α : ℝ) (x : E) : partialAffineFn B L a b α x
      = indicatorFn (a +ᵥ (L : Set E)) x + ((B x b : ℝ) : EReal) + (α : EReal) := rfl

/-- **The conjugate of a partial affine function**:
`(δ(· | L + a) + ⟨·, a*⟩ + α)* = δ(· | L^⊥ + a*) + ⟨a, ·⟩ + α*`, where `α*` is `-α - ⟨a, a*⟩`. -/
theorem conj_partialAffineFn (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (L : Submodule ℝ E) (a : E) (b : F) (α : ℝ) :
    conj B (partialAffineFn B L a b α)
      = partialAffineFn B.flip (polarSubmodule B L) b a (-α - B a b) := by
  have hcone : conj B (indicatorFn (L : Set E)) = indicatorFn (polarCone B (L : Set E)) :=
    conj_indicatorFn_eq_indicatorFn_polarCone (fun _ hc => smul_coe_submodule L hc)
      ⟨0, L.zero_mem⟩
  have hfun : partialAffineFn B L a b α
      = fun x : E => indicatorFn (L : Set E) (x - a) + ((B x b : ℝ) : EReal) + (α : EReal) := by
    funext x
    rw [partialAffineFn_apply, indicatorFn_vadd]
  funext y
  have e : conj B (fun x : E => indicatorFn (L : Set E) (x - a) + ((B x b : ℝ) : EReal)
        + (α : EReal)) y
      = conj B (indicatorFn (L : Set E)) (y - b) + ((B a y : ℝ) : EReal)
        + ((-α - B a b : ℝ) : EReal) :=
    conj_comp_affine (B := B) (B' := B) (LinearEquiv.refl ℝ E) (LinearEquiv.refl ℝ F)
      (fun _ _ => rfl) (indicatorFn (L : Set E)) a b α y
  rw [hfun, e, hcone, partialAffineFn_apply, indicatorFn_vadd, coe_polarSubmodule,
    LinearMap.flip_apply]

end PartialAffine

section ExamplesTopology

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} [IsCompatiblePairing B]

/-- Dually: the polar of the solution set of the homogeneous inequalities `⟨aᵢ, y⟩ ≤ 0` is the
closure of the convex cone generated by the `aᵢ`. -/
theorem polarCone_setOf_forall_le_zero {ι : Sort*} (a : ι → E) :
    polarCone B.flip {y : F | ∀ i, B (a i) y ≤ 0} =
      closure (PointedCone.hull ℝ (Set.range a) : Set E) := by
  rw [← polarCone_hull_range B a]
  exact polarCone_polarCone
    ((PointedCone.hull ℝ (Set.range a) : ConvexCone ℝ E)).convex
    (smul_coe_pointedCone _) ⟨0, (PointedCone.hull ℝ (Set.range a)).zero_mem⟩

end ExamplesTopology

/-! ### The nonnegative orthant

The book's second example, for a real inner-product space paired with itself. -/

section Orthant

variable {ι : Type*} [Fintype ι]

/-- **The polar of the nonnegative orthant is the nonpositive orthant.** -/
theorem polarCone_nonnegOrthant :
    polarCone (innerₗ (EuclideanSpace ℝ ι)) {x : EuclideanSpace ℝ ι | ∀ i, 0 ≤ x i} =
      {y : EuclideanSpace ℝ ι | ∀ i, y i ≤ 0} := by
  classical
  ext y
  simp only [mem_polarCone, Set.mem_ofPred, innerₗ_apply_apply, PiLp.inner_apply,
    RCLike.inner_apply, starRingEnd_apply, star_trivial]
  constructor
  · intro h i
    have hmem : ∀ j, (0 : ℝ) ≤ (EuclideanSpace.single i (1 : ℝ) : EuclideanSpace ℝ ι) j := by
      intro j
      simp only [PiLp.single_apply]
      split <;> norm_num
    have h' := h _ hmem
    simpa using h'
  · intro h x hx
    refine Finset.sum_nonpos fun i _ => ?_
    have hi := mul_le_mul_of_nonneg_right (h i) (hx i)
    simpa using hi

end Orthant

end ConvexAnalysis
