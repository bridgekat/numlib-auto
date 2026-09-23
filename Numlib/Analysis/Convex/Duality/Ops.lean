import Numlib.Analysis.Convex.Duality.Conjugate
import Numlib.Analysis.Convex.Duality.Support
import Numlib.Analysis.Convex.Homogenize
import Numlib.Analysis.Convex.Operations.Hull
import Numlib.Analysis.Convex.Operations.Image
import Numlib.Analysis.Convex.Operations.InfConv

/-!
# The dual operations table

Every operation on convex functions has a dual operation, and conjugacy exchanges the two.

| primal | dual | form |
|---|---|---|
| `a • f` | `smulRight (convexConj B f) a` | unconditional |
| `smulRight f a` | `a • convexConj B f` | unconditional |
| `mapLin A f` | `compLin (convexConj B f) A'` | unconditional |
| `compLin g A` | `mapLin A' (convexConj B' g)` | up to closure |
| `infConv f g` | `convexConj B f + convexConj B g` | unconditional |
| `f + g` | `infConv (convexConj B f) (convexConj B g)` | up to closure |
| `convFn f` | `⨆ i, convexConj B (f i)` | unconditional |
| `⨆ i, f i` | `convFn fun i => convexConj B (f i)` | up to closure |

Each row appears in up to three forms. The **unconditional** half is an identity valid for
arbitrary functions; the rows marked "up to closure" hold for closed convex functions with a
`convexCl` on the dual side; and the *exact* forms, in which the closure is dropped and the infimum
attained, are the consequences of `IsExactSum` and `IsExactImage` in `Duality/Exact.lean`. Nothing
in this file needs a constraint qualification.

## Main results

* `convexConj_ofEpi` — the conjugate read off an epigraph-defining set.
* `convexConj_smul`, `convexConj_smulRight` — scalar multiplication is dual to right scalar
  multiplication.
* `convexConj_mapLin` — the image row, unconditional half; `convexConj_compLin_eq_convexCl_mapLin`
  is the closure form.
* `convexConj_infConv` — the convolution row, unconditional half;
  `convexConj_add_eq_convexCl_infConv` the closure form. `convexConj_sum_toInfConvFn` is the `m`-ary
  version, `(f₁ □ ⋯ □ fₘ)* = ∑ fᵢ*`, which says that `convexConj B` is a monoid homomorphism out of
  `InfConvFn E`.
* `convexConj_convFn`, `convexConj_convHullFn`, `convexConj_convFn₂` — the convex-hull row,
  unconditional half; `convexConj_iSup_eq_convexCl_convFn` the closure form.

## Implementation notes

Most of the unconditional identities are proved by showing that both sides are `≤ (c : EReal)`
under the same condition on `c` — that is, by comparing the two collections of affine minorants
rather than by manipulating suprema. The exception is `convexConj_infConv`, whose right-hand side is
a *sum*, which has no such characterisation.

Each closure form is the unconditional identity for the *dual* operation, conjugated once more and
read through Fenchel–Moreau; that is why each needs compatible topologies on both spaces and closed
convex inputs.

## References

* [rockafellar1970convex] §16.
-/

open Pointwise Set

namespace ConvexAnalysis

/-! ### Conjugates through the epigraph -/

section OfEpi

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
variable {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ}

/-- **The conjugate reads off an epigraph-defining set.** `(ofEpi S)*(y)` is the supremum of
`⟨x, y⟩ - μ` over the points `(x, μ)` of `S`. The infimum defining `ofEpi S` need not be attained,
so this is not a rearrangement of the supremum defining `convexConj`. -/
theorem convexConj_ofEpi (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (S : Set (E × ℝ)) (y : F) :
    convexConj B (ofEpi S) y = ⨆ p ∈ S, ((B p.1 y - p.2 : ℝ) : EReal) := by
  refine EReal.eq_of_forall_le_coe_iff fun c => ?_
  rw [convexConj_le_coe_iff, ← subset_epi_iff_le_ofEpi, iSup₂_le_iff]
  constructor
  · intro h p hp
    have hp' : affineFn B y c p.1 ≤ (p.2 : EReal) := h hp
    rw [affineFn_eq_coe, EReal.coe_le_coe_iff] at hp'
    rw [EReal.coe_le_coe_iff]
    linarith
  · intro h p hp
    have hp' := h p hp
    rw [EReal.coe_le_coe_iff] at hp'
    rw [mem_epi, affineFn_eq_coe, EReal.coe_le_coe_iff]
    linarith

/-- `convexConj_ofEpi` for the epigraph itself: the conjugate is a supremum over the epigraph. -/
theorem convexConj_eq_biSup_epi (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) (y : F) :
    convexConj B f y = ⨆ p ∈ epi f, ((B p.1 y - p.2 : ℝ) : EReal) := by
  have h := convexConj_ofEpi B (epi f) y
  rwa [ofEpi_epi] at h

end OfEpi

/-! ### Scalar multiplication -/

section Smul

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
variable {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f : E → EReal} {a : ℝ}

/-- `(af)* = f*a` for `a > 0`: ordinary scalar multiplication is dual to right scalar
multiplication. -/
theorem convexConj_smul (ha : 0 < a) (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) :
    convexConj B (fun x => (a : EReal) * f x) = smulRight (convexConj B f) a := by
  have ha0 : a ≠ 0 := ha.ne'
  funext y
  refine EReal.eq_of_forall_le_coe_iff fun c => ?_
  rw [convexConj_le_coe_iff, smulRight_apply_pos ha, EReal.coe_mul_le_coe_iff ha,
      convexConj_le_coe_iff,
    Pi.le_def, Pi.le_def]
  refine forall_congr' fun x => ?_
  have hcoe : ((B x y - c) / a : ℝ) = B x (a⁻¹ • y) - c / a := by
    rw [map_smul, smul_eq_mul]
    ring
  rw [affineFn_eq_coe, affineFn_eq_coe, EReal.coe_le_coe_mul_iff ha, hcoe]

/-- `(fa)* = a(f*)` for `a > 0`, the other half. -/
theorem convexConj_smulRight (ha : 0 < a) (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) :
    convexConj B (smulRight f a) = fun y => (a : EReal) * convexConj B f y := by
  have ha0 : a ≠ 0 := ha.ne'
  funext y
  refine EReal.eq_of_forall_le_coe_iff fun c => ?_
  rw [convexConj_le_coe_iff, EReal.coe_mul_le_coe_iff ha, convexConj_le_coe_iff, Pi.le_def,
      Pi.le_def]
  have hcoe : ∀ x : E, ((B (a • x) y - c) / a : ℝ) = B x y - c / a := fun x => by
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
    field_simp
  have key : ∀ x : E, (affineFn B y c (a • x) ≤ smulRight f a (a • x))
      ↔ (affineFn B y (c / a) x ≤ f x) := fun x => by
    rw [affineFn_eq_coe, affineFn_eq_coe, smulRight_apply_pos ha, inv_smul_smul₀ ha0,
      EReal.coe_le_coe_mul_iff ha, hcoe x]
  refine ⟨fun h x => (key x).1 (h (a • x)), fun h x => ?_⟩
  have hx := (key (a⁻¹ • x)).2 (h (a⁻¹ • x))
  rwa [smul_inv_smul₀ ha0] at hx

end Smul

/-! ### Linear images -/

section Image

variable {E F G H : Type*}
  [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [AddCommGroup G] [Module ℝ G] [AddCommGroup H] [Module ℝ H]
variable {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {B' : G →ₗ[ℝ] H →ₗ[ℝ] ℝ}
  {A : E →ₗ[ℝ] G} {A' : H →ₗ[ℝ] F}

/-- **The image row**, unconditional half: `(Af)* = f*A'`. The conjugate of an image is the
*inverse* image of the conjugate under the transpose, with no hypothesis on `f` and no closure.
Contrast `IsExactImage.convexConj_compLin`, the other row, which needs a constraint
qualification. -/
theorem convexConj_mapLin (hA : IsAdjointPair B B' A A') (f : E → EReal) :
    convexConj B' (mapLin A f) = compLin (convexConj B f) A' := by
  funext z
  refine le_antisymm ?_ ?_
  · rw [convexConj_apply]
    refine iSup_le fun u => ?_
    rw [EReal.coe_sub_le_comm]
    refine le_mapLin fun x hx => ?_
    subst hx
    rw [hA x z, ← EReal.coe_sub_le_comm]
    exact sub_le_convexConj B f x (A' z)
  · rw [compLin_apply, convexConj_apply]
    refine iSup_le fun x => ?_
    rw [← hA x z]
    exact (EReal.sub_le_sub le_rfl (mapLin_le rfl)).trans
      (sub_le_convexConj B' (mapLin A f) (A x) z)

end Image

/-! ### Infimal convolution -/

section InfConv

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
variable {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ}

/-- **The convolution row**, unconditional half: `(f □ g)* = f* + g*`, with no hypothesis on `f`
and `g`. The reverse row, `(f + g)* = f* □ g*`, is `IsExactSum.convexConj_add` and needs a
constraint qualification. -/
theorem convexConj_infConv (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f g : E → EReal) :
    convexConj B (infConv f g) = convexConj B f + convexConj B g := by
  funext y
  have hadd : ∀ p q : E × ℝ, ((B (p + q).1 y - (p + q).2 : ℝ) : EReal)
      = ((B p.1 y - p.2 : ℝ) : EReal) + ((B q.1 y - q.2 : ℝ) : EReal) := fun p q => by
    rw [← EReal.coe_add]
    congr 1
    simp only [Prod.fst_add, Prod.snd_add, map_add, LinearMap.add_apply]
    ring
  rw [Pi.add_apply, infConv_def, convexConj_ofEpi, convexConj_eq_biSup_epi B f y,
      convexConj_eq_biSup_epi B g y,
    EReal.biSup_add_biSup (fun _ _ => EReal.coe_ne_bot _)
      (fun _ _ => EReal.coe_ne_bot _)]
  refine le_antisymm (iSup₂_le fun r hr => ?_) (iSup₂_le fun p hp => iSup₂_le fun q hq => ?_)
  · obtain ⟨p, hp, q, hq, rfl⟩ := hr
    rw [hadd p q]
    exact le_iSup₂_of_le p hp (le_iSup₂_of_le q hq le_rfl)
  · rw [← hadd p q]
    exact le_iSup₂_of_le (p + q) (Set.add_mem_add hp hq) le_rfl

/-- **The concave convolution row**, the twin of `convexConj_infConv` and like it unconditional:
`(g □ h)* = g* + h*` for the supremal convolution, where the sum on the right is taken in the
*concave* `∞ - ∞` convention, `-(-u + -v)`, under which `⊤ + ⊥ = ⊤`. -/
theorem concaveConj_supConv (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (g h : E → EReal) :
    concaveConj B (supConv g h) = fun y => -(-(concaveConj B g y) + -(concaveConj B h y)) := by
  funext y
  have hneg : (fun x => -(supConv g h x)) = infConv (fun w => -(g w)) (fun w => -(h w)) :=
    funext fun x => neg_supConv g h x
  rw [neg_concaveConj, neg_concaveConj, ← Pi.add_apply, ← convexConj_infConv,
    concaveConj_eq_neg_convexConj_neg, hneg]

/-- The conjugate of `δ(· | 0)` is the zero function — the identity of `□` goes to the identity
of `+`, which is what makes conjugacy a monoid homomorphism here. -/
@[simp] theorem convexConj_indicatorFn_zero (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) :
    convexConj B (indicatorFn ({0} : Set E)) = 0 := by
  rw [← supportFn_eq_convexConj_indicatorFn, supportFn_singleton]
  funext y
  simp

/-- **The convolution row** in its `m`-ary form: `(f₁ □ ⋯ □ fₘ)* = f₁* + ⋯ + fₘ*`,
unconditionally. The `□`-product being the `AddCommMonoid` sum of `InfConvFn E`, this says that
`convexConj B` is a monoid homomorphism from `(E → EReal, □, δ(· | 0))` to `(F → EReal, +, 0)`. No
properness is needed, and none may be assumed: `□` does not preserve it. -/
theorem convexConj_sum_toInfConvFn {ι : Type*} (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (s : Finset ι)
    (f : ι → E → EReal) :
    convexConj B (ofInfConvFn (∑ i ∈ s, toInfConvFn (f i))) = ∑ i ∈ s, convexConj B (f i) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i t hi ih =>
    rw [Finset.sum_cons, Finset.sum_cons, ofInfConvFn_add, ofInfConvFn_toInfConvFn,
      convexConj_infConv, ih]

end InfConv

/-! ### Convex hulls of families -/

section Hull

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
variable {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {ι : Sort*}

/-- **The convex-hull row**, unconditional half: `(conv {fᵢ})* = sup {fᵢ*}`, with no hypothesis on
the family. The empty family is not an exception: both sides are then `⊥`. -/
theorem convexConj_convFn (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : ι → E → EReal) :
    convexConj B (convFn f) = ⨆ i, convexConj B (f i) := by
  funext y
  refine EReal.eq_of_forall_le_coe_iff fun c => ?_
  rw [convexConj_le_coe_iff, iSup_apply, iSup_le_iff]
  refine ⟨fun h i => convexConj_le_coe_iff.2 (h.trans (convFn_le f i)), fun h => ?_⟩
  exact le_convFn (convexFn_affineFn y c) fun i => convexConj_le_coe_iff.1 (h i)

/-- A function and its convex hull have the same conjugate, since they have the same affine
minorants. -/
theorem convexConj_convHullFn (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (g : E → EReal) :
    convexConj B (convHullFn g) = convexConj B g := by
  funext y
  refine EReal.eq_of_forall_le_coe_iff fun c => ?_
  rw [convexConj_le_coe_iff, convexConj_le_coe_iff]
  exact ⟨fun h => h.trans (convHullFn_le g), fun h => le_convHullFn (convexFn_affineFn y c) h⟩

theorem convexConj_convFn₂ (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f g : E → EReal) :
    convexConj B (convFn₂ f g) = convexConj B f ⊔ convexConj B g := by
  funext y
  refine EReal.eq_of_forall_le_coe_iff fun c => ?_
  rw [convexConj_le_coe_iff, Pi.sup_apply, sup_le_iff, convexConj_le_coe_iff, convexConj_le_coe_iff]
  exact ⟨fun h => ⟨h.trans (convFn₂_le_left f g), h.trans (convFn₂_le_right f g)⟩,
    fun h => le_convFn₂ (convexFn_affineFn y c) h.1 h.2⟩

end Hull

/-! ### The closure forms

The second row of each pair carries a closure on the dual side: `(fA)* = cl(A'f*)`,
`(f + g)* = cl(f* □ g*)`, `(sup fᵢ)* = cl conv{fᵢ*}`. -/

section Closure

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} [IsCompatiblePairing B] [IsCompatiblePairing B.flip]
  {f g : E → EReal} {ι : Sort*}

/-- **The convolution row**, closure form: `(f + g)* = cl(f* □ g*)` for closed convex `f` and `g`.
`IsExactSum.convexConj_add` is the same statement with the closure dropped. -/
theorem convexConj_add_eq_convexCl_infConv (hf : ConvexFn f) (hfc : ClosedConvex f)
    (hg : ConvexFn g)
    (hgc : ClosedConvex g) :
    convexConj B (f + g) = convexCl (infConv (convexConj B f) (convexConj B g)) := by
  have hstep : convexConj B.flip (infConv (convexConj B f) (convexConj B g)) = f + g := by
    rw [convexConj_infConv,
        show convexConj B.flip (convexConj B f) = f from convexBiconj_eq_self hf hfc,
      show convexConj B.flip (convexConj B g) = g from convexBiconj_eq_self hg hgc]
  rw [← hstep]
  exact convexBiconj_eq_convexCl
      (B := B.flip) (convexFn_infConv (convexFn_convexConj B f) (convexFn_convexConj B g))

/-- **The convex-hull row**, closure form: `(sup fᵢ)* = cl conv {fᵢ*}` for a family of closed
convex functions. -/
theorem convexConj_iSup_eq_convexCl_convFn {f : ι → E → EReal} (hf : ∀ i, ConvexFn (f i))
    (hfc : ∀ i, ClosedConvex (f i)) :
    convexConj B (⨆ i, f i) = convexCl (convFn fun i => convexConj B (f i)) := by
  have hstep : convexConj B.flip (convFn fun i => convexConj B (f i)) = ⨆ i, f i := by
    rw [convexConj_convFn]
    exact iSup_congr fun i => convexBiconj_eq_self (hf i) (hfc i)
  rw [← hstep]
  exact convexBiconj_eq_convexCl (B := B.flip) (convexFn_convFn _)

end Closure

section ClosureImage

variable {E F G H : Type*}
  [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [AddCommGroup G] [Module ℝ G] [AddCommGroup H] [Module ℝ H]
  [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F]
  [TopologicalSpace G] [IsTopologicalAddGroup G] [ContinuousSMul ℝ G] [LocallyConvexSpace ℝ G]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {B' : G →ₗ[ℝ] H →ₗ[ℝ] ℝ}
  {A : E →ₗ[ℝ] G} {A' : H →ₗ[ℝ] F} {g : G → EReal}

/-- **The image row**, closure form: `(gA)* = cl(A'g*)` for closed convex `g`.
`IsExactImage.convexConj_compLin` is the same statement with the closure dropped. -/
theorem convexConj_compLin_eq_convexCl_mapLin [IsCompatiblePairing B'] [IsCompatiblePairing B.flip]
    (hA : IsAdjointPair B B' A A') (hg : ConvexFn g) (hgc : ClosedConvex g) :
    convexConj B (compLin g A) = convexCl (mapLin A' (convexConj B' g)) := by
  have hstep : convexConj B.flip (mapLin A' (convexConj B' g)) = compLin g A := by
    rw [convexConj_mapLin hA.flip,
        show convexConj B'.flip (convexConj B' g) = g from convexBiconj_eq_self hg hgc]
  rw [← hstep]
  exact convexBiconj_eq_convexCl (B := B.flip) (convexFn_mapLin A' (convexFn_convexConj B' g))

end ClosureImage

end ConvexAnalysis
