/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Duality.Conjugate
import Numlib.Analysis.Convex.Duality.Support
import Numlib.Analysis.Convex.Homogenize
import Numlib.Analysis.Convex.Operations.Hull
import Numlib.Analysis.Convex.Operations.Image
import Numlib.Analysis.Convex.Operations.InfConv

/-!
# The dual operations table

Let $E$ and $F$ be real vector spaces paired by $B$, and write $f^*$ for the conjugate of
$f : E \to [-\infty, +\infty]$. Every operation on convex functions has a dual operation, and
conjugacy exchanges the two. This module proves the rows of the following table, which is §16 of
[rockafellar1970convex]. Here $a > 0$, $(A, A')$ is an adjoint pair of linear maps, $f a$ is right
scalar multiplication, $A f$ is the image and $g A$ the inverse image under a linear map, $\square$
is infimal convolution, and $\operatorname{conv}$ is the convex hull of a family of functions.

| Primal | Conjugate | Form |
|---|---|---|
| $a f$ | $f^* a$ | unconditional |
| $f a$ | $a f^*$ | unconditional |
| $A f$ | $f^* A'$ | unconditional |
| $g A$ | $\operatorname{cl}(A' g^*)$ | up to closure |
| $f \mathbin{\square} g$ | $f^* + g^*$ | unconditional |
| $f + g$ | $\operatorname{cl}(f^* \mathbin{\square} g^*)$ | up to closure |
| $\operatorname{conv} \{f_i\}$ | $\sup_i f_i^*$ | unconditional |
| $\sup_i f_i$ | $\operatorname{cl} \operatorname{conv} \{f_i^*\}$ | up to closure |

Each row has up to three forms. The **unconditional** form is an identity for arbitrary functions.
The rows marked "up to closure" hold for closed convex functions, with a closure on the dual side.
The **exact** forms, in which the closure is dropped and the infimum is attained, are consequences
of `ConvexAnalysis.IsExactSum` and `ConvexAnalysis.IsExactImage` in
`Numlib.Analysis.Convex.Duality.Exact`. Nothing in this module needs a constraint qualification.

## Main results

* `ConvexAnalysis.convexConj_ofEpi`: the conjugate of the function determined by a set
  $S \subseteq E \times \mathbb{R}$ is the supremum of $\langle x, y \rangle - \mu$ over
  $(x, \mu) \in S$.
* `ConvexAnalysis.convexConj_smul`, `ConvexAnalysis.convexConj_smulRight`: for $a > 0$,
  $(a f)^* = f^* a$ and $(f a)^* = a f^*$.
* `ConvexAnalysis.convexConj_mapLin`: the image row, $(A f)^* = f^* A'$.
  `ConvexAnalysis.convexConj_compLin_eq_convexCl_mapLin` is its closure form
  $(g A)^* = \operatorname{cl}(A' g^*)$.
* `ConvexAnalysis.convexConj_infConv`: the convolution row, $(f \mathbin{\square} g)^* = f^* + g^*$.
  `ConvexAnalysis.convexConj_add_eq_convexCl_infConv` is its closure form $(f + g)^* =
  \operatorname{cl}(f^* \mathbin{\square} g^*)$.
* `ConvexAnalysis.concaveConj_supConv`: the concave counterpart of the convolution row, for supremal
  convolution.
* `ConvexAnalysis.convexConj_sum_toInfConvFn`: the $m$-ary convolution row, $(f_1 \mathbin{\square}
  \cdots \mathbin{\square} f_m)^* = f_1^* + \cdots + f_m^*$. It says that conjugation is a monoid
  homomorphism out of the infimal convolution monoid `ConvexAnalysis.InfConvFn E`.
* `ConvexAnalysis.convexConj_convFn`, `ConvexAnalysis.convexConj_convHullFn`,
  `ConvexAnalysis.convexConj_convFn₂`: the convex hull row,
  $(\operatorname{conv} \{f_i\})^* = \sup_i f_i^*$.
  `ConvexAnalysis.convexConj_iSup_eq_convexCl_convFn` is its closure form $(\sup_i f_i)^* =
  \operatorname{cl} \operatorname{conv} \{f_i^*\}$.

## Proof outline

Most unconditional identities are proved by showing that both sides are at most $c$ under the same
condition on $c \in \mathbb{R}$, that is, by a comparison of the two sets of affine minorants
instead of a manipulation of suprema. The exception is `ConvexAnalysis.convexConj_infConv`, whose
right-hand side is a sum, which has no such characterization.

Each closure form is the unconditional identity for the dual operation, conjugated once more and
read through the Fenchel–Moreau theorem. This is why each closure form needs compatible topologies
on both spaces and closed convex inputs.

## Notation

* $f a$: the right scalar multiple `ConvexAnalysis.smulRight f a`, with $(f a)(x) = a f(a^{-1} x)$
  for $a > 0$.
* $A f$: the image `ConvexAnalysis.mapLin A f`, with $(A f)(y) = \inf \{f(x) \mid A x = y\}$.
* $g A$: the inverse image `ConvexAnalysis.compLin g A`, with $(g A)(x) = g(A x)$.
* $f \mathbin{\square} g$: the infimal convolution `ConvexAnalysis.infConv f g`.
* $\operatorname{conv} \{f_i\}$: the convex hull `ConvexAnalysis.convFn f` of a family.
* $\operatorname{cl} f$: the closure `ConvexAnalysis.convexCl f`.
-/

open Pointwise Set

namespace ConvexAnalysis

/-! ### Conjugates through the epigraph -/

section OfEpi

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
variable {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ}

/-- **The conjugate read off a set that defines an epigraph.** Let $S \subseteq E \times \mathbb{R}$
and let $h$ be the function whose graph is the lower boundary of $S$,
$h(x) = \inf \{\mu \mid (x, \mu) \in S\}$. Then for every $y \in F$, $$h^*(y) = \sup_{(x, \mu)
\in S} \bigl(B(x, y) - \mu\bigr).$$

The function $h$ is `ConvexAnalysis.ofEpi S`. The infimum that defines $h$ need not be attained,
so this is not a rearrangement of the supremum that defines `ConvexAnalysis.convexConj`. -/
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

/-- The conjugate is a supremum over the epigraph: for $f : E \to [-\infty, +\infty]$ and $y \in F$,
$$f^*(y) = \sup_{(x, \mu) \in \operatorname{epi} f} \bigl(B(x, y) - \mu\bigr).$$ This is
`ConvexAnalysis.convexConj_ofEpi` for $S = \operatorname{epi} f$. -/
theorem convexConj_eq_biSup_epi (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) (y : F) :
    convexConj B f y = ⨆ p ∈ epi f, ((B p.1 y - p.2 : ℝ) : EReal) := by
  have h := convexConj_ofEpi B (epi f) y
  rwa [ofEpi_epi] at h

end OfEpi

/-! ### Scalar multiplication -/

section Smul

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
variable {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f : E → EReal} {a : ℝ}

/-- Let $f : E \to [-\infty, +\infty]$ and $a > 0$. The conjugate of $a f$ is the right scalar
multiple of the conjugate: $$(a f)^* = f^* a, \qquad \text{that is,} \qquad (a f)^*(y) = a
f^*(a^{-1} y).$$ So ordinary scalar multiplication is dual to right scalar multiplication.

The right scalar multiple is `ConvexAnalysis.smulRight`. -/
theorem convexConj_smul (ha : 0 < a) (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) :
    convexConj B (fun x => (a : EReal) * f x) = smulRight (convexConj B f) a := by
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

/-- Let $f : E \to [-\infty, +\infty]$ and $a > 0$. The conjugate of the right scalar multiple $f a$
is $a$ times the conjugate: $$(f a)^* = a f^*.$$

The right scalar multiple is `ConvexAnalysis.smulRight`. This is the other half of
`ConvexAnalysis.convexConj_smul`. -/
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

/-- **The image row**, unconditional form. Let $B$ pair $E$ with $F$ and $B'$ pair $G$ with $H$, and
let $A : E \to G$ and $A' : H \to F$ form an adjoint pair. For every
$f : E \to [-\infty, +\infty]$, $$(A f)^* = f^* A',$$ where
$(A f)(z) = \inf \{f(x) \mid A x = z\}$ is the image of $f$ and $(f^* A')(w) = f^*(A' w)$.

There is no hypothesis on $f$ and no closure: the conjugate of an image is the inverse image of
the conjugate under the adjoint. Contrast `ConvexAnalysis.IsExactImage.convexConj_compLin`, the
other row, which needs a constraint qualification. -/
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

/-- **The convolution row**, unconditional form. For all $f, g : E \to [-\infty, +\infty]$, $$(f
\mathbin{\square} g)^* = f^* + g^*.$$

There is no hypothesis on $f$ and $g$. The sum on the right is the sum of extended reals, in
which $-\infty + \infty = -\infty$. The reverse row, $(f + g)^* = f^* \mathbin{\square} g^*$, is
`ConvexAnalysis.IsExactSum.convexConj_add` and needs a constraint qualification. -/
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

/-- **The concave convolution row**, the counterpart of `ConvexAnalysis.convexConj_infConv`, and
like it unconditional. For all $g, h : E \to [-\infty, +\infty]$, the concave conjugate of the
supremal convolution satisfies $$(g \mathbin{\square} h)^*(y) = g^*(y) + h^*(y),$$ where the sum
is taken in the concave convention $u + v := -((-u) + (-v))$, under which
$\infty + (-\infty) = \infty$.

The supremal convolution is `ConvexAnalysis.supConv` and the concave conjugate is
`ConvexAnalysis.concaveConj`. -/
theorem concaveConj_supConv (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (g h : E → EReal) :
    concaveConj B (supConv g h) = fun y => -(-(concaveConj B g y) + -(concaveConj B h y)) := by
  funext y
  have hneg : (fun x => -(supConv g h x)) = infConv (fun w => -(g w)) (fun w => -(h w)) :=
    funext fun x => neg_supConv g h x
  rw [neg_concaveConj, neg_concaveConj, ← Pi.add_apply, ← convexConj_infConv,
    concaveConj_eq_neg_convexConj_neg, hneg]

/-- The conjugate of the indicator function $\delta(\cdot \mid 0)$ of the origin is the zero
function.

The identity of $\square$ goes to the identity of $+$, which makes conjugation a monoid
homomorphism. -/
@[simp] theorem convexConj_indicatorFn_zero (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) :
    convexConj B (indicatorFn ({0} : Set E)) = 0 := by
  rw [← supportFn_eq_convexConj_indicatorFn, supportFn_singleton]
  funext y
  simp

/-- **The convolution row** in its $m$-ary form. For a finite family
$f_1, \dots, f_m : E \to [-\infty, +\infty]$, $$(f_1 \mathbin{\square} \cdots \mathbin{\square}
f_m)^* = f_1^* + \cdots + f_m^*,$$ with no hypothesis on the functions. For the empty family,
both sides are $0$.

No properness is needed, and none can be assumed, because $\square$ does not preserve
properness. The convolution of the family is the sum `∑ i ∈ s, toInfConvFn (f i)` in the
commutative monoid `ConvexAnalysis.InfConvFn E`, whose addition is $\square$ and whose zero is
$\delta(\cdot \mid 0)$. So the result says that conjugation is a monoid homomorphism from $(E
\to [-\infty, +\infty], \square, \delta(\cdot \mid 0))$ to $(F \to [-\infty, +\infty], +, 0)$. -/
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

/-- **The convex hull row**, unconditional form. For every family $(f_i)_{i \in \iota}$ of functions
$E \to [-\infty, +\infty]$, $$(\operatorname{conv} \{f_i\})^* = \sup_i f_i^*.$$

There is no hypothesis on the family. The empty family is not an exception: both sides are then
the constant $-\infty$. The convex hull of the family is `ConvexAnalysis.convFn f`. -/
theorem convexConj_convFn (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : ι → E → EReal) :
    convexConj B (convFn f) = ⨆ i, convexConj B (f i) := by
  funext y
  refine EReal.eq_of_forall_le_coe_iff fun c => ?_
  rw [convexConj_le_coe_iff, iSup_apply, iSup_le_iff]
  refine ⟨fun h i => convexConj_le_coe_iff.2 (h.trans (convFn_le f i)), fun h => ?_⟩
  exact le_convFn (convexFn_affineFn y c) fun i => convexConj_le_coe_iff.1 (h i)

/-- A function and its convex hull have the same conjugate: for every
$g : E \to [-\infty, +\infty]$, $(\operatorname{conv} g)^* = g^*$. The reason is that they have
the same affine minorants. -/
theorem convexConj_convHullFn (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (g : E → EReal) :
    convexConj B (convHullFn g) = convexConj B g := by
  funext y
  refine EReal.eq_of_forall_le_coe_iff fun c => ?_
  rw [convexConj_le_coe_iff, convexConj_le_coe_iff]
  exact ⟨fun h => h.trans (convHullFn_le g), fun h => le_convHullFn (convexFn_affineFn y c) h⟩

/-- For all $f, g : E \to [-\infty, +\infty]$, the conjugate of the convex hull of $f$ and $g$ is
the pointwise maximum of the conjugates: $$(\operatorname{conv} \{f, g\})^* = \max \{f^*,
g^*\}.$$

The convex hull of two functions is `ConvexAnalysis.convFn₂ f g`. -/
theorem convexConj_convFn₂ (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f g : E → EReal) :
    convexConj B (convFn₂ f g) = convexConj B f ⊔ convexConj B g := by
  funext y
  refine EReal.eq_of_forall_le_coe_iff fun c => ?_
  rw [convexConj_le_coe_iff, Pi.sup_apply, sup_le_iff, convexConj_le_coe_iff, convexConj_le_coe_iff]
  exact ⟨fun h => ⟨h.trans (convFn₂_le_left f g), h.trans (convFn₂_le_right f g)⟩,
    fun h => le_convFn₂ (convexFn_affineFn y c) h.1 h.2⟩

end Hull

/-!
### The closure forms

The second row of each pair carries a closure on the dual side:
$(g A)^* = \operatorname{cl}(A' g^*)$, $(f + g)^* = \operatorname{cl}(f^* \mathbin{\square} g^*)$
and $(\sup_i f_i)^* = \operatorname{cl} \operatorname{conv} \{f_i^*\}$.
-/

section Closure

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} [IsCompatiblePairing B] [IsCompatiblePairing B.flip]
  {f g : E → EReal} {ι : Sort*}

/-- **The convolution row**, closure form. Let $E$ and $F$ be locally convex spaces, and let the
pairing $B$ be compatible with the topologies of both $E$ and $F$. If
$f, g : E \to [-\infty, +\infty]$ are convex and closed, then $$(f + g)^* =
\operatorname{cl}(f^* \mathbin{\square} g^*).$$

The compatibility hypotheses are `ConvexAnalysis.IsCompatiblePairing B` and
`ConvexAnalysis.IsCompatiblePairing B.flip`. `ConvexAnalysis.IsExactSum.convexConj_add` is the
same statement without the closure. -/
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

/-- **The convex hull row**, closure form. Let $E$ and $F$ be locally convex spaces, and let the
pairing $B$ be compatible with the topologies of both $E$ and $F$. If every member of the family
$(f_i)_{i \in \iota}$ of functions $E \to [-\infty, +\infty]$ is convex and closed, then
$$\Bigl(\sup_i f_i\Bigr)^* = \operatorname{cl} \operatorname{conv} \{f_i^*\}.$$
-/
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

/-- **The image row**, closure form. Let $B$ pair $E$ with $F$ and $B'$ pair $G$ with $H$, where $F$
and $G$ are locally convex spaces, $B'$ is compatible with the topology of $G$ and $B$ is
compatible with the topology of $F$. Let $A : E \to G$ and $A' : H \to F$ form an adjoint pair.
If $g : G \to [-\infty, +\infty]$ is convex and closed, then $$(g A)^* = \operatorname{cl}(A'
g^*),$$ where $(g A)(x) = g(A x)$ and $A' g^*$ is the image of $g^*$ under $A'$.

The compatibility hypotheses are `ConvexAnalysis.IsCompatiblePairing B'` and
`ConvexAnalysis.IsCompatiblePairing B.flip`. `ConvexAnalysis.IsExactImage.convexConj_compLin` is
the same statement without the closure. -/
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
