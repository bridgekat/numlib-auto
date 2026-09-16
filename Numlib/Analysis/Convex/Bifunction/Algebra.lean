import Numlib.Analysis.Convex.Duality.ConcaveOps
import Numlib.Analysis.Convex.Duality.Exact
import Numlib.Analysis.Convex.Duality.Ops
import Numlib.Analysis.Convex.Extremum.Fenchel
import Numlib.Analysis.Convex.Saddle.Defs

/-!
# The algebra of bifunctions

The adjoint of a convex bifunction generalizes the adjoint of a linear transformation. This file
generalizes the rest of the linear algebra — addition, scalar multiplication, application to a
vector, composition, the inner product — and describes how each behaves under taking adjoints.

| operation | here | linear-algebra analogue |
|---|---|---|
| `F₁ □ F₂` | `infConvBifun` | `A₁ + A₂` |
| `H₁ ⊡ H₂` | `infConvFstBifun` | the same, in the *first* variable |
| `Fλ` | `smulRightBifun` | `λ A` |
| `Ff` | `imageBifun` | `A x` |
| `GF` | `compBifun` | `B ∘ A` |
| `F⁎`, `F⁎*` | `inverseBifun`, `lowerAdjointBifun` | `A⁻¹`, `(A⁻¹)*` |
| `⟨f, g⟩` | `fenchelSup` / `fenchelInf` / `HasFenchelPairing` | `⟨x, y⟩` |

## Main results

* **Sums and scalar multiples** — `adjointBifun_infConvBifun`: `(F₁ □ F₂)* = F₁* □ F₂*`, the right
  side a supremal convolution (`supConvBifun`) of concave bifunctions, with `bracket_infConvBifun`
  the bracket identity behind it; and `adjointBifun_smulRightBifun`, `(Fλ)* = F*λ` for `λ > 0`.
* **The conjugate of an image** — `conj_imageBifun`, `exists_conj_imageBifun_eq`: `(Ff)* = F⁎* f*`,
  infimum attained ([rockafellar1970convex] Theorem 38.4); `conj_imageBifun_of_bracket_eq_top` is
  the degenerate branch `y ∉ dom F*`, and `closedBifun_lowerAdjointBifun` says `F⁎*` is closed for
  *any* `F`.
* **The adjoint of a product** — `inverseBifun_compBifun`, `adjointBifun_compBifun`,
  `lowerAdjointBifun_compBifun`: `(GF)⁎ = F⁎ G⁎`, `(GF)* = F* G*` with the supremum attained, and
  `(GF)⁎* = (G⁎*)(F⁎*)` ([rockafellar1970convex] Theorem 38.5); `lowerAdjointBifun_infConvFstBifun`
  is `(H₁ ⊡ H₂)⁎* = H₁⁎* □ H₂⁎*`.
* **The closed case** — for closed proper convex arguments each operation is closed, its defining
  extremum is attained, and the adjoint of the result is the *closure* of the corresponding
  product or convolution (`closedBifun_compBifun` and the `_eq_clBifun` results).
* **The inner product** — `fenchelSup_le_fenchelInf` is weak duality, with no hypothesis;
  `fenchelPairing_conj` says conjugation reverses `⟨f, g⟩`; `conj_imageBifun_eq_fenchelPairing`
  (`⟨Ff, y⟩ = ⟨f, F* y⟩`) and `bracket_compBifun_eq_fenchelPairing` move an adjoint across it; and
  `fenchelSup_imageBifun_lowerAdjointBifun` gives `⟨Ff, g*⟩ = ⟨f, F* g*⟩`
  ([rockafellar1970convex] Theorem 38.7).

## Implementation notes

Rockafellar's hypotheses throughout are "`ri (dom …)` and `ri (dom …)` have a point in common",
whose conclusion is that `(f + g)*` is an *exact* infimal convolution of `f*` and `g*`. That
conclusion is taken here as the hypothesis, in the form `IsExactSum` — one instance per dual vector
where the book has a single relative-interior condition. It also demands that both summands be
proper, so it is *stronger* than the book's hypothesis, and needs no topology, no finite dimension.

`lowerAdjointBifun Bu Bx F v y` is *defined* as `-(adjointBifun Bu Bx F y v)`; working through `F⁎*`
rather than a second, concave adjoint keeps the closed-case corollaries between *convex*
bifunctions and avoids needing a concave `clBifun`.

Rockafellar leaves `⟨f, g⟩` *undefined* when the two extrema differ, so they are kept apart here as
`fenchelSup`, `fenchelInf` and the predicate `HasFenchelPairing` that they agree. He also restricts
them to `dom f ∩ dom g*` to avoid `∞ - ∞`; for proper `f` and proper concave `g` the excluded terms
are `⊥` on the sup side and `⊤` on the inf side, so the plain `⨆`/`⨅` used here agree with his.

## References

* [rockafellar1970convex] §38.
-/

open Pointwise

namespace ConvexAnalysis

/-! ### Infimal convolution of bifunctions -/

section InfConvBifunDefs

variable {U X : Type*} [AddCommGroup X]

/-- Rockafellar's `F₁ □ F₂`: infimal convolution in the second variable, pointwise in the first.

This is the bifunction analogue of the *sum* of two linear transformations: if `Fᵢ` is the convex
indicator bifunction of `Aᵢ`, then `F₁ □ F₂` is the convex indicator bifunction of `A₁ + A₂`. -/
noncomputable def infConvBifun (F₁ F₂ : Bifun U X) : Bifun U X := fun u => infConv (F₁ u) (F₂ u)

theorem infConvBifun_apply (F₁ F₂ : Bifun U X) (u : U) :
    infConvBifun F₁ F₂ u = infConv (F₁ u) (F₂ u) := rfl

theorem infConvBifun_comm (F₁ F₂ : Bifun U X) : infConvBifun F₁ F₂ = infConvBifun F₂ F₁ :=
  funext fun u => infConv_comm (F₁ u) (F₂ u)

theorem infConvBifun_assoc (F₁ F₂ F₃ : Bifun U X) :
    infConvBifun (infConvBifun F₁ F₂) F₃ = infConvBifun F₁ (infConvBifun F₂ F₃) :=
  funext fun u => infConv_assoc (F₁ u) (F₂ u) (F₃ u)

omit [AddCommGroup X] in
theorem mem_domBifun_iff_dom_nonempty {F : Bifun U X} {u : U} :
    u ∈ domBifun F ↔ (dom (F u)).Nonempty := by
  constructor
  · rintro ⟨x, hx⟩; exact ⟨x, lt_top_iff_ne_top.2 hx⟩
  · rintro ⟨x, hx⟩; exact ⟨x, hx.ne⟩

/-- **The effective domain of `F₁ □ F₂` is `dom F₁ ∩ dom F₂`.**

No hypothesis at all is needed: `dom (f □ g) = dom f + dom g` is unconditional, and a sum of sets
is nonempty exactly when both summands are. -/
theorem domBifun_infConvBifun (F₁ F₂ : Bifun U X) :
    domBifun (infConvBifun F₁ F₂) = domBifun F₁ ∩ domBifun F₂ := by
  ext u
  rw [Set.mem_inter_iff, mem_domBifun_iff_dom_nonempty, mem_domBifun_iff_dom_nonempty,
    mem_domBifun_iff_dom_nonempty, infConvBifun_apply, dom_infConv]
  exact Set.add_nonempty

end InfConvBifunDefs

section InfConvBifunConvex

variable {U X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]
variable [AddCommGroup Y] [Module ℝ Y] {F₁ F₂ : Bifun U X}

/-- The linear map `((u, x), y) ↦ (u, x - y)`, the left half of the change of variables that turns
a partial infimal convolution into a partial minimisation. -/
def infConvSubLeft (U X : Type*) [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X] :
    (U × X) × X →ₗ[ℝ] U × X :=
  LinearMap.prod (LinearMap.fst ℝ U X ∘ₗ LinearMap.fst ℝ (U × X) X)
    (LinearMap.snd ℝ U X ∘ₗ LinearMap.fst ℝ (U × X) X - LinearMap.snd ℝ (U × X) X)

@[simp] theorem infConvSubLeft_apply (q : (U × X) × X) :
    infConvSubLeft U X q = (q.1.1, q.1.2 - q.2) := rfl

/-- The linear map `((u, x), y) ↦ (u, y)`, the right half of the same change of variables. -/
def infConvSubRight (U X : Type*) [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X] :
    (U × X) × X →ₗ[ℝ] U × X :=
  LinearMap.prod (LinearMap.fst ℝ U X ∘ₗ LinearMap.fst ℝ (U × X) X) (LinearMap.snd ℝ (U × X) X)

@[simp] theorem infConvSubRight_apply (q : (U × X) × X) :
    infConvSubRight U X q = (q.1.1, q.2) := rfl

/-- The graph function of `F₁ □ F₂` is a *partial minimisation* of a convex function on
`(U × X) × X`: the infimum formula for `□`, read jointly in `(u, x)`. -/
theorem graphFn_infConvBifun (hb₁ : ∀ u x, F₁ u x ≠ ⊥) (hb₂ : ∀ u x, F₂ u x ≠ ⊥) (p : U × X) :
    graphFn (infConvBifun F₁ F₂) p
      = ⨅ y : X, (compLin (graphFn F₁) (infConvSubLeft U X)
          + compLin (graphFn F₂) (infConvSubRight U X)) (p, y) := by
  change infConv (F₁ p.1) (F₂ p.1) p.2 = _
  rw [infConv_apply (fun x => hb₁ p.1 x) (fun x => hb₂ p.1 x)]
  rfl

/-- **An infimal convolute of convex bifunctions is convex.**

`F₁ □ F₂` is a *partial* infimal convolution of the graph functions, so this is
`convexFn_iInf_right` applied to the sum of the two graph functions after the linear change of
variables `((u, x), y) ↦ ((u, x - y), (u, y))`. -/
theorem convexBifun_infConvBifun (hb₁ : ∀ u x, F₁ u x ≠ ⊥) (hb₂ : ∀ u x, F₂ u x ≠ ⊥)
    (hF₁ : ConvexBifun F₁) (hF₂ : ConvexBifun F₂) : ConvexBifun (infConvBifun F₁ F₂) := by
  have hh : ConvexFn (compLin (graphFn F₁) (infConvSubLeft U X)
      + compLin (graphFn F₂) (infConvSubRight U X)) :=
    ConvexFn.add (convexFn_compLin _ hF₁) (convexFn_compLin _ hF₂)
      (fun q => hb₁ _ _) (fun q => hb₂ _ _)
  have hmin := convexFn_iInf_right hh
  have hgr : graphFn (infConvBifun F₁ F₂)
      = fun p : U × X => ⨅ y : X, (compLin (graphFn F₁) (infConvSubLeft U X)
          + compLin (graphFn F₂) (infConvSubRight U X)) (p, y) :=
    funext (graphFn_infConvBifun hb₁ hb₂)
  rw [ConvexBifun, hgr]
  exact hmin

omit [AddCommGroup U] [Module ℝ U] in
/-- **The bracket of an infimal convolute is the sum of the brackets**,
`⟨(F₁ □ F₂) u, x*⟩ = ⟨F₁ u, x*⟩ + ⟨F₂ u, x*⟩`.

This is `conj_infConv`, the unconditional identity `(f □ g)* = f* + g*`, read slice by slice; no
hypothesis is needed, and Rockafellar's convention `∞ - ∞ = -∞` is `EReal`'s own `⊤ + ⊥ = ⊥`. -/
theorem bracket_infConvBifun (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (F₁ F₂ : Bifun U X) (u : U) :
    bracket Bx (infConvBifun F₁ F₂) u = bracket Bx F₁ u + bracket Bx F₂ u :=
  conj_infConv Bx (F₁ u) (F₂ u)

end InfConvBifunConvex

/-! ### The adjoint of an infimal convolute -/

section SupConvBifun

variable {V Y : Type*} [AddCommGroup V]

/-- The concave analogue of `infConvBifun`: `(G₁ □ G₂) y = G₁ y □ G₂ y`, with the *supremal*
convolution in the second variable. Rockafellar writes `□` for both, the orientation of the
bifunction deciding which is meant. -/
noncomputable def supConvBifun (G₁ G₂ : Bifun Y V) : Bifun Y V := fun y => supConv (G₁ y) (G₂ y)

theorem supConvBifun_apply (G₁ G₂ : Bifun Y V) (y : Y) :
    supConvBifun G₁ G₂ y = supConv (G₁ y) (G₂ y) := rfl

end SupConvBifun

section AdjointInfConvBifun

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]

/-- **The adjoint of an infimal convolute is the supremal convolute of the adjoints**,
`(F₁ □ F₂)* = F₁* □ F₂*`, one dual vector at a time.

The proof is the concave conjugate of a sum, applied to the two concave functions `u ↦ ⟨Fᵢ u, y⟩`:
the adjoint at `y` *is* their concave conjugate, and the bracket of `F₁ □ F₂` is their sum. The
two properness fields of `IsExactSum` say that neither `u ↦ ⟨Fᵢ u, y⟩` takes the value `+∞`, which
is Rockafellar's branch condition `y ∈ dom F₁* ∩ dom F₂*`; the exactness field is what his
relative-interior condition supplies. -/
theorem adjointBifun_infConvBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (F₁ F₂ : Bifun U X) {y : Y}
    (hex : IsExactSum Bu (fun u => -(bracket Bx F₁ u y)) (fun u => -(bracket Bx F₂ u y))) :
    adjointBifun Bu Bx (infConvBifun F₁ F₂) y
      = supConv (adjointBifun Bu Bx F₁ y) (adjointBifun Bu Bx F₂ y) := by
  have hadj : ∀ F : Bifun U X,
      adjointBifun Bu Bx F y = concaveConj Bu (fun u => bracket Bx F u y) :=
    fun F => funext fun v => adjointBifun_eq_concaveConj_bracket Bu Bx F y v
  have hbr : (fun u => bracket Bx (infConvBifun F₁ F₂) u y)
      = fun u => bracket Bx F₁ u y + bracket Bx F₂ u y :=
    funext fun u => congrFun (bracket_infConvBifun Bx F₁ F₂ u) y
  calc adjointBifun Bu Bx (infConvBifun F₁ F₂) y
      = concaveConj Bu (fun u => bracket Bx (infConvBifun F₁ F₂) u y) := hadj _
    _ = concaveConj Bu (fun u => bracket Bx F₁ u y + bracket Bx F₂ u y) := by rw [hbr]
    _ = supConv (concaveConj Bu fun u => bracket Bx F₁ u y)
          (concaveConj Bu fun u => bracket Bx F₂ u y) := concaveConj_add_of_isExactSum hex
    _ = supConv (adjointBifun Bu Bx F₁ y) (adjointBifun Bu Bx F₂ y) := by
          rw [hadj F₁, hadj F₂]

/-- The adjoint of an infimal convolute, as an identity of bifunctions rather than pointwise. -/
theorem adjointBifun_infConvBifun_eq_supConvBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (F₁ F₂ : Bifun U X)
    (hex : ∀ y : Y, IsExactSum Bu (fun u => -(bracket Bx F₁ u y))
      (fun u => -(bracket Bx F₂ u y))) :
    adjointBifun Bu Bx (infConvBifun F₁ F₂)
      = supConvBifun (adjointBifun Bu Bx F₁) (adjointBifun Bu Bx F₂) :=
  funext fun y => adjointBifun_infConvBifun Bu Bx F₁ F₂ (hex y)

end AdjointInfConvBifun

/-! ### `EReal` bookkeeping -/

section ERealAux

private theorem coe_sub_add (r : ℝ) {a b : EReal} (ha : a ≠ ⊥) (hb : b ≠ ⊥) :
    (r : EReal) - (a + b) = ((r : EReal) - b) - a := by
  have h : -(a + b) = -b + -a := by
    rw [add_comm a b]
    exact EReal.neg_add (.inl hb) (.inr ha)
  change (r : EReal) + -(a + b) = ((r : EReal) + -b) + -a
  rw [h, ← add_assoc]

private theorem add_coe_ne_top {a : EReal} (ha : a ≠ ⊤) (c : ℝ) : a + (c : EReal) ≠ ⊤ := by
  induction a with
  | bot => simp
  | coe p => rw [← EReal.coe_add]; exact EReal.coe_ne_top _
  | top => exact absurd rfl ha

private theorem sub_sub_eq_add_sub {a b c : EReal} (ha : a ≠ ⊥) (hc : c ≠ ⊤) :
    b - (a - c) = (b + c) - a := by
  have h : -(a - c) = c - a := EReal.neg_sub_comm (.inl ha) (.inr hc)
  change b + -(a - c) = b + c + -a
  rw [h]
  change b + (c + -a) = b + c + -a
  rw [← add_assoc]

end ERealAux

/-! ### The image of a convex function under a bifunction -/

section ImageBifunDefs

variable {U X : Type*}

/-- `Prod.swap` as a linear map. -/
def swapLin (E G : Type*) [AddCommGroup E] [Module ℝ E] [AddCommGroup G] [Module ℝ G] :
    E × G →ₗ[ℝ] G × E := LinearMap.prod (LinearMap.snd ℝ E G) (LinearMap.fst ℝ E G)

@[simp] theorem swapLin_apply {E G : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup G]
    [Module ℝ G] (q : E × G) : swapLin E G q = (q.2, q.1) := rfl

/-- Rockafellar's `Ff`, the **image of a convex function under a convex bifunction**:
`(Ff)(x) = ⨅ u, f u + (Fu)(x)`.

When `F` is the convex indicator bifunction of a linear map `A`, this is the image `mapLin A f`. -/
noncomputable def imageBifun (F : Bifun U X) (f : U → EReal) : X → EReal :=
  fun x => ⨅ u, f u + F u x

theorem imageBifun_apply (F : Bifun U X) (f : U → EReal) (x : X) :
    imageBifun F f x = ⨅ u, f u + F u x := rfl

/-- The image of a concave function under a *concave* bifunction: the mirror of `imageBifun`, with
the infimum replaced by a supremum. Rockafellar's `Gg` for concave `G` and `g`. -/
noncomputable def concaveImageBifun (G : Bifun U X) (g : U → EReal) : X → EReal :=
  fun x => ⨆ u, g u + G u x

theorem concaveImageBifun_apply (G : Bifun U X) (g : U → EReal) (x : X) :
    concaveImageBifun G g x = ⨆ u, g u + G u x := rfl

end ImageBifunDefs

section ImageBifunConvex

variable {U X : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]
variable {F : Bifun U X} {f : U → EReal}

/-- **The image of a convex function under a convex bifunction is convex** on `X`.

`(u, x) ↦ f u + (Fu)(x)` is convex on `U × X`, and `Ff` is its image under the projection
`(u, x) ↦ x`. -/
theorem convexFn_imageBifun (hbF : ∀ u x, F u x ≠ ⊥) (hbf : ∀ u, f u ≠ ⊥)
    (hF : ConvexBifun F) (hf : ConvexFn f) : ConvexFn (imageBifun F f) := by
  have hh : ConvexFn (compLin f (LinearMap.snd ℝ X U) + compLin (graphFn F) (swapLin X U)) :=
    ConvexFn.add (convexFn_compLin _ hf) (convexFn_compLin _ hF)
      (fun q => hbf _) (fun q => hbF _ _)
  exact convexFn_iInf_right hh

end ImageBifunConvex

section LowerAdjoint

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
variable [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]

/-- Rockafellar's `F⁎*`: the adjoint of the inverse of `F`, a *convex* bifunction from `V` to `Y`.

It is the reflected negative of the adjoint, `(F⁎* v)(y) = -(F* y)(v)`; that identity is
`lowerAdjointBifun_eq_concaveAdjointBifun`, and it is the reason `F⁎*` needs no separate
construction. -/
noncomputable def lowerAdjointBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (F : Bifun U X) : Bifun V Y := fun v y => -(adjointBifun Bu Bx F y v)

@[simp] theorem lowerAdjointBifun_apply (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (F : Bifun U X) (v : V) (y : Y) :
    lowerAdjointBifun Bu Bx F v y = -(adjointBifun Bu Bx F y v) := rfl

/-- `F⁎*` really is the adjoint of the inverse bifunction `F⁎`: the concave adjoint of `F⁎`,
taken for the flipped pairings, is the reflected negative of `F*`.

Both sides are the same extremum over `U × X`, read once through `Prod.swap`; the only arithmetic
is `-(z + c) = -z + (-c)` for a real constant `c`, which needs no side condition. -/
theorem lowerAdjointBifun_eq_concaveAdjointBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (F : Bifun U X) :
    lowerAdjointBifun Bu Bx F = concaveAdjointBifun Bu.flip Bx.flip (inverseBifun F) := by
  funext v y
  rw [lowerAdjointBifun_apply, adjointBifun_apply, EReal.neg_iInf, concaveAdjointBifun_apply]
  rw [← Function.Surjective.iSup_comp (f := (Prod.swap : X × U → U × X)) Prod.swap_surjective]
  refine iSup_congr fun q => ?_
  simp only [Prod.fst_swap, Prod.snd_swap, inverseBifun_apply, LinearMap.flip_apply]
  have h1 : -(F q.2 q.1 + ((Bu q.2 v - Bx q.1 y : ℝ) : EReal))
      = -(F q.2 q.1) + -(((Bu q.2 v - Bx q.1 y : ℝ) : EReal)) :=
    EReal.neg_add (.inr (EReal.coe_ne_top _)) (.inr (EReal.coe_ne_bot _))
  have hr : (-(Bu q.2 v - Bx q.1 y) : ℝ) = Bx q.1 y - Bu q.2 v := by ring
  rw [h1, ← EReal.coe_neg, hr]

/-- `F⁎*` is a convex bifunction, with no hypothesis on `F`: it is the negative of the concave
`F*`, read through the swap of the two factors. -/
theorem convexBifun_lowerAdjointBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (F : Bifun U X) : ConvexBifun (lowerAdjointBifun Bu Bx F) := by
  have hc : ConvexFn (fun p : Y × V => -(graphFn (adjointBifun Bu Bx F) p)) :=
    concaveFn_iff_convexFn_neg.1 (concaveFn_graphFn_adjointBifun Bu Bx F)
  exact convexFn_compLin (swapLin V Y) hc

end LowerAdjoint

/-! ### The lower adjoint is closed -/

section LowerAdjointClosed

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace V] [IsTopologicalAddGroup V] [TopologicalSpace Y] [IsTopologicalAddGroup Y]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ}
  [IsContinuousPairing (prodPairing Bu Bx).flip] {F : Bifun U X}

/-- **`F⁎*` is a closed convex bifunction, with no hypothesis on `F` at all.**

The adjoint `F*` is concave-closed for any `F`; `F⁎*` is its reflected negative, and closedness
carries across the reflection. This is what makes a bifunction exhibited as some `H⁎*` closed. -/
theorem closedBifun_lowerAdjointBifun : ClosedBifun (lowerAdjointBifun Bu Bx F) := by
  have hc : ClosedFn (fun p : Y × V => -(graphFn (adjointBifun Bu Bx F) p)) :=
    closedConcaveFn_iff.1 closedConcaveFn_graphFn_adjointBifun
  have hcont : Continuous (swapLin V Y) := by
    change Continuous fun p : V × Y => ((p.2, p.1) : Y × V)
    exact continuous_snd.prodMk continuous_fst
  have heq : graphFn (lowerAdjointBifun Bu Bx F)
      = compLin (fun p : Y × V => -(graphFn (adjointBifun Bu Bx F) p)) (swapLin V Y) :=
    funext fun _ => rfl
  change ClosedFn (graphFn (lowerAdjointBifun Bu Bx F))
  rw [heq]
  exact closedFn_compLin hc hcont

end LowerAdjointClosed

/-! ### The conjugate of an image -/

section ImageBifunConj

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
variable [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
variable {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ} {F : Bifun U X} {f : U → EReal}

omit [AddCommGroup U] [Module ℝ U] in
/-- The conjugate of the image `Ff` is the supremum over `u` of the bracket `⟨Fu, y⟩` offset by
`f u`. This is the whole computational content of the formula for `(Ff)*`; what remains is
Fenchel's duality theorem applied to the concave function `u ↦ ⟨Fu, y⟩`. -/
theorem conj_imageBifun_eq_iSup (hbF : ∀ u x, F u x ≠ ⊥) (hbf : ∀ u, f u ≠ ⊥) (y : Y) :
    conj Bx (imageBifun F f) y = ⨆ u, (bracket Bx F u y - f u) := by
  have hstep : ∀ u : U, (⨆ x : X, (((Bx x y : ℝ) : EReal) - (f u + F u x)))
      = bracket Bx F u y - f u := by
    intro u
    have hbody : ∀ x : X, ((Bx x y : ℝ) : EReal) - (f u + F u x)
        = (((Bx x y : ℝ) : EReal) - F u x) + -(f u) := fun x => by
      rw [coe_sub_add _ (hbf u) (hbF u x), sub_eq_add_neg]
    rw [iSup_congr hbody, ← EReal.iSup_add, ← sub_eq_add_neg]
    rfl
  rw [conj_apply]
  calc (⨆ x : X, (((Bx x y : ℝ) : EReal) - imageBifun F f x))
      = ⨆ x : X, ⨆ u : U, (((Bx x y : ℝ) : EReal) - (f u + F u x)) :=
        iSup_congr fun x => EReal.coe_sub_iInf _ _
    _ = ⨆ u : U, ⨆ x : X, (((Bx x y : ℝ) : EReal) - (f u + F u x)) := iSup_comm
    _ = ⨆ u : U, (bracket Bx F u y - f u) := iSup_congr hstep

omit [AddCommGroup U] [Module ℝ U] in
/-- The same supremum as `conj_imageBifun_eq_iSup`, turned around: when no bracket value is `⊤`,
`(Ff)*(y)` is minus the infimum of `f - ⟨F·, y⟩`, which is the primal side of Fenchel's duality
theorem. -/
theorem conj_imageBifun_eq_neg_iInf (hbF : ∀ u x, F u x ≠ ⊥) (hbf : ∀ u, f u ≠ ⊥) {y : Y}
    (hgt : ∀ u, bracket Bx F u y ≠ ⊤) :
    conj Bx (imageBifun F f) y = -(⨅ u, (f u - bracket Bx F u y)) := by
  rw [conj_imageBifun_eq_iSup hbF hbf y, EReal.neg_iInf]
  exact iSup_congr fun u => (EReal.neg_sub_comm (.inl (hbf u)) (.inr (hgt u))).symm

/-- **The conjugate of an image is the image under the lower adjoint**, `(Ff)* = F⁎* f*`, in the
pointwise form `(Ff)*(y) = ⨅ v, f*(v) - (F* y)(v)`.

The hypothesis is that Fenchel's duality theorem applies to `f` and to the concave function
`u ↦ ⟨Fu, y⟩` — Rockafellar's "`ri (dom f)` and `ri (dom F)` have a point in common", as an
`IsExactSum`. It also carries `Proper (-⟨F·, y⟩)`, i.e. his side condition `y ∈ dom F*`; the
degenerate branch is `conj_imageBifun_of_bracket_eq_top`. -/
theorem conj_imageBifun (hbF : ∀ u x, F u x ≠ ⊥) (hf : Proper f) {y : Y}
    (hex : IsExactSum Bu f (fun u => -(bracket Bx F u y))) :
    conj Bx (imageBifun F f) y = ⨅ v, (conj Bu f v - adjointBifun Bu Bx F y v) := by
  set g : U → EReal := fun u => bracket Bx F u y with hg
  have hex' : IsExactSum Bu f (-g) := hex
  have hgt : ∀ u, g u ≠ ⊤ := by
    intro u hu
    exact hex'.proper_right.ne_bot u (by simp [Pi.neg_apply, hu])
  have hgd : (domConcave g).Nonempty := by
    rw [domConcave_eq_dom_neg]
    exact hex'.proper_right.dom_nonempty
  have h1 : conj Bx (imageBifun F f) y = -(⨅ u, (f u - g u)) :=
    conj_imageBifun_eq_neg_iInf hbF hf.ne_bot hgt
  have h2 : (⨅ u, f u - g u) = ⨆ v, (concaveConj Bu g v - conj Bu f v) := fenchel_duality hex'
  have h4 : -(⨆ v, (concaveConj Bu g v - conj Bu f v))
      = ⨅ v, (conj Bu f v - concaveConj Bu g v) := by
    rw [EReal.neg_iSup]
    exact iInf_congr fun v =>
      EReal.neg_sub_comm (.inr (conj_ne_bot hf.dom_nonempty v)) (.inl (concaveConj_ne_top hgd v))
  rw [h1, h2, h4]
  exact iInf_congr fun v => by rw [adjointBifun_eq_concaveConj_bracket]

/-- **The infimum defining `(F⁎* f*)(y)` is attained**, under the hypothesis of
`conj_imageBifun`. -/
theorem exists_conj_imageBifun_eq (hbF : ∀ u x, F u x ≠ ⊥) (hf : Proper f) {y : Y}
    (hex : IsExactSum Bu f (fun u => -(bracket Bx F u y))) :
    ∃ v : V, conj Bu f v - adjointBifun Bu Bx F y v = conj Bx (imageBifun F f) y := by
  set g : U → EReal := fun u => bracket Bx F u y with hg
  have hex' : IsExactSum Bu f (-g) := hex
  have hgt : ∀ u, g u ≠ ⊤ := by
    intro u hu
    exact hex'.proper_right.ne_bot u (by simp [Pi.neg_apply, hu])
  have hgd : (domConcave g).Nonempty := by
    rw [domConcave_eq_dom_neg]
    exact hex'.proper_right.dom_nonempty
  obtain ⟨v, hv⟩ := exists_concaveConj_sub_conj_eq hex'
  refine ⟨v, ?_⟩
  rw [conj_imageBifun_eq_neg_iInf hbF hf.ne_bot hgt, ← hv,
    EReal.neg_sub_comm (.inr (conj_ne_bot hf.dom_nonempty v)) (.inl (concaveConj_ne_top hgd v)),
    adjointBifun_eq_concaveConj_bracket]

/-- **The degenerate branch of `(Ff)* = F⁎* f*`**, `y ∉ dom F*`: if the bracket `⟨Fu, y⟩` is `+∞`
at some `u` where `f` is finite, both sides are `+∞`.

With the finiteness of `f u₀` as an explicit hypothesis this is unconditional, where Rockafellar
reaches the case from a relative-interior hypothesis instead. -/
theorem conj_imageBifun_of_bracket_eq_top (hbF : ∀ u x, F u x ≠ ⊥) (hf : Proper f) {u₀ : U}
    {y : Y} (htop : bracket Bx F u₀ y = ⊤) (hfin : f u₀ ≠ ⊤) :
    conj Bx (imageBifun F f) y = ⊤ ∧
      imageBifun (lowerAdjointBifun Bu Bx F) (conj Bu f) y = ⊤ := by
  obtain ⟨r, hr⟩ :=
    EReal.exists_coe_of_ne_bot_of_lt_top (hf.ne_bot u₀) (lt_top_iff_ne_top.2 hfin)
  constructor
  · rw [conj_imageBifun_eq_iSup hbF hf.ne_bot y]
    refine eq_top_iff.2 (le_trans (le_of_eq ?_) (le_iSup _ u₀))
    rw [htop, hr]
    simp
  · have hbot : ∀ v : V, adjointBifun Bu Bx F y v = ⊥ := by
      intro v
      rw [adjointBifun_eq_concaveConj_bracket,
        concaveConj_of_eq_top (B := Bu) (g := fun u => bracket Bx F u y) htop]
    rw [imageBifun_apply]
    refine le_antisymm le_top (le_iInf fun v => ?_)
    have hv : conj Bu f v + lowerAdjointBifun Bu Bx F v y = ⊤ := by
      rw [lowerAdjointBifun_apply, hbot v, EReal.neg_bot,
        EReal.add_top_of_ne_bot (conj_ne_bot hf.dom_nonempty v)]
    exact le_of_eq hv.symm

end ImageBifunConj

/-! ### The image of a closed proper convex function -/

section ImageBifunProper

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
variable [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
variable {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ} {F : Bifun U X} {f : U → EReal}

/-- The adjoint of a bifunction that is finite somewhere is nowhere `⊤`: the infimum defining it
is bounded above by the single term at `(u₀, x₀)`. -/
theorem adjointBifun_ne_top {u₀ : U} {x₀ : X} (hF : F u₀ x₀ ≠ ⊤) (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (y : Y) (v : V) : adjointBifun Bu Bx F y v ≠ ⊤ :=
  ne_top_of_le_ne_top (add_coe_ne_top hF _) (iInf_le _ (u₀, x₀))

/-- `F⁎*` never takes the value `-∞` when `F` is finite somewhere. This is the hypothesis `hbF` of
`conj_imageBifun`, for the bifunction `F⁎*`. -/
theorem lowerAdjointBifun_ne_bot {u₀ : U} {x₀ : X} (hF : F u₀ x₀ ≠ ⊤)
    (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (v : V) (y : Y) :
    lowerAdjointBifun Bu Bx F v y ≠ ⊥ := by
  rw [lowerAdjointBifun_apply]
  simpa using adjointBifun_ne_top hF Bu Bx y v

/-- **`(Ff)* = F⁎* f*`** packaged as an identity of functions rather than as a formula for the
values. The two sides differ only by `a - b = a + (-b)`. -/
theorem conj_imageBifun_eq_imageBifun (hbF : ∀ u x, F u x ≠ ⊥) (hf : Proper f) {y : Y}
    (hex : IsExactSum Bu f (fun u => -(bracket Bx F u y))) :
    conj Bx (imageBifun F f) y = imageBifun (lowerAdjointBifun Bu Bx F) (conj Bu f) y := by
  rw [conj_imageBifun hbF hf hex]
  rfl

end ImageBifunProper

section ImageBifunClosed

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsCompatiblePairing Bu] {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ}
  [IsCompatiblePairing Bx] {F : Bifun U X} {f : U → EReal}

/-- **`F⁎*⁎* = cl F`**, the biadjoint identity in the `F⁎*` packaging.

Rockafellar states the biadjoint as `F** = cl F` for the *concave* adjoint of `F*`; taking `F⁎*`
twice is the same computation with the two negations moved outside, so nothing concave is built. -/
theorem lowerAdjointBifun_lowerAdjointBifun_eq_clBifun (hF : ConvexBifun F) :
    lowerAdjointBifun Bu.flip Bx.flip (lowerAdjointBifun Bu Bx F) = clBifun F := by
  rw [← concaveAdjointBifun_adjointBifun_eq_clBifun (Bu := Bu) (Bx := Bx) hF]
  funext u x
  rw [lowerAdjointBifun_apply, adjointBifun_apply, EReal.neg_iInf, concaveAdjointBifun_apply,
    ← Function.Surjective.iSup_comp (f := (Prod.swap : V × Y → Y × V)) Prod.swap_surjective]
  refine iSup_congr fun q => ?_
  simp only [Prod.fst_swap, Prod.snd_swap, lowerAdjointBifun_apply, LinearMap.flip_apply]
  have h1 : -(-(adjointBifun Bu Bx F q.2 q.1) + ((Bu u q.1 - Bx x q.2 : ℝ) : EReal))
      = -(-(adjointBifun Bu Bx F q.2 q.1)) + -(((Bu u q.1 - Bx x q.2 : ℝ) : EReal)) :=
    EReal.neg_add (.inr (EReal.coe_ne_top _)) (.inr (EReal.coe_ne_bot _))
  have hr : (-(Bu u q.1 - Bx x q.2) : ℝ) = Bx x q.2 - Bu u q.1 := by ring
  rw [h1, neg_neg, ← EReal.coe_neg, hr]

/-- **`(F⁎* f*)* = Ff`** for a closed proper convex `F` and a closed proper convex `f` — the
identity the rest of the closed case follows from.

This is `conj_imageBifun` applied to `F⁎*` and `f*`, whose own adjoint and conjugate are `F` and
`f` again. Rockafellar's `ri (dom f*) ∩ ri (dom F⁎*) ≠ ∅` is the `IsExactSum` hypothesis. -/
theorem conj_imageBifun_lowerAdjointBifun (hF : ConvexBifun F) (hFcl : ClosedBifun F)
    {u₀ : U} {x₀ : X} (hFp : F u₀ x₀ ≠ ⊤) (hf : ClosedProperConvexFn f) {x : X}
    (hex : IsExactSum Bu.flip (conj Bu f)
      (fun v => -(bracket Bx.flip (lowerAdjointBifun Bu Bx F) v x))) :
    conj Bx.flip (imageBifun (lowerAdjointBifun Bu Bx F) (conj Bu f)) x = imageBifun F f x := by
  have hbid : conj Bu.flip (conj Bu f) = f :=
    (biconj_eq_clFn (B := Bu) hf.convex).trans hf.closed
  have h := conj_imageBifun_eq_imageBifun (Bu := Bu.flip) (Bx := Bx.flip)
    (lowerAdjointBifun_ne_bot hFp Bu Bx) (proper_conj hf) hex
  rw [h, lowerAdjointBifun_lowerAdjointBifun_eq_clBifun hF, hFcl.clBifun_eq, hbid]

/-- **The image `Ff` of a closed proper convex function is closed.** It is a conjugate. -/
theorem closedFn_imageBifun (hF : ConvexBifun F) (hFcl : ClosedBifun F)
    {u₀ : U} {x₀ : X} (hFp : F u₀ x₀ ≠ ⊤) (hf : ClosedProperConvexFn f)
    (hex : ∀ x : X, IsExactSum Bu.flip (conj Bu f)
      (fun v => -(bracket Bx.flip (lowerAdjointBifun Bu Bx F) v x))) :
    ClosedFn (imageBifun F f) := by
  have hfun : imageBifun F f
      = conj Bx.flip (imageBifun (lowerAdjointBifun Bu Bx F) (conj Bu f)) :=
    funext fun x => (conj_imageBifun_lowerAdjointBifun hF hFcl hFp hf (hex x)).symm
  rw [hfun]
  exact closedFn_conj

/-- **The infimum defining `(Ff)(x)` is attained**, for a closed proper convex `F` and `f`. This is
`exists_conj_imageBifun_eq` read at `F⁎*` and `f*`. -/
theorem exists_imageBifun_eq (hF : ConvexBifun F) (hFcl : ClosedBifun F)
    {u₀ : U} {x₀ : X} (hFp : F u₀ x₀ ≠ ⊤) (hf : ClosedProperConvexFn f) {x : X}
    (hex : IsExactSum Bu.flip (conj Bu f)
      (fun v => -(bracket Bx.flip (lowerAdjointBifun Bu Bx F) v x))) :
    ∃ u : U, f u + F u x = imageBifun F f x := by
  have hbid : conj Bu.flip (conj Bu f) = f :=
    (biconj_eq_clFn (B := Bu) hf.convex).trans hf.closed
  have hlow : lowerAdjointBifun Bu.flip Bx.flip (lowerAdjointBifun Bu Bx F) = F :=
    (lowerAdjointBifun_lowerAdjointBifun_eq_clBifun hF).trans hFcl.clBifun_eq
  obtain ⟨u, hu⟩ := exists_conj_imageBifun_eq (Bu := Bu.flip) (Bx := Bx.flip)
    (lowerAdjointBifun_ne_bot hFp Bu Bx) (proper_conj hf) hex
  refine ⟨u, ?_⟩
  have hadj : adjointBifun Bu.flip Bx.flip (lowerAdjointBifun Bu Bx F) x u = -(F u x) := by
    rw [← neg_neg (adjointBifun Bu.flip Bx.flip (lowerAdjointBifun Bu Bx F) x u)]
    exact congrArg Neg.neg (congrFun (congrFun hlow u) x)
  rw [hbid, hadj] at hu
  have hval : f u - -(F u x) = f u + F u x := by
    change f u + -(-(F u x)) = f u + F u x
    rw [neg_neg]
  rw [← conj_imageBifun_lowerAdjointBifun hF hFcl hFp hf hex, ← hu, hval]

variable [TopologicalSpace Y] [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y]
  [LocallyConvexSpace ℝ Y] [IsCompatiblePairing Bx.flip]

/-- **`(Ff)* = cl (F⁎* f*)`** for a closed proper convex `F` and `f`.

`Ff` is the conjugate of `F⁎* f*`, so `(Ff)*` is its biconjugate, which is its closure. -/
theorem conj_imageBifun_eq_clFn (hF : ConvexBifun F) (hFcl : ClosedBifun F)
    {u₀ : U} {x₀ : X} (hFp : F u₀ x₀ ≠ ⊤) (hf : ClosedProperConvexFn f)
    (hex : ∀ x : X, IsExactSum Bu.flip (conj Bu f)
      (fun v => -(bracket Bx.flip (lowerAdjointBifun Bu Bx F) v x))) :
    conj Bx (imageBifun F f)
      = clFn (imageBifun (lowerAdjointBifun Bu Bx F) (conj Bu f)) := by
  have hconv : ConvexFn (imageBifun (lowerAdjointBifun Bu Bx F) (conj Bu f)) :=
    convexFn_imageBifun (lowerAdjointBifun_ne_bot hFp Bu Bx)
      (proper_conj hf).ne_bot (convexBifun_lowerAdjointBifun Bu Bx F) (convexFn_conj Bu f)
  have hfun : imageBifun F f
      = conj Bx.flip (imageBifun (lowerAdjointBifun Bu Bx F) (conj Bu f)) :=
    funext fun x => (conj_imageBifun_lowerAdjointBifun hF hFcl hFp hf (hex x)).symm
  rw [hfun]
  exact biconj_eq_clFn (B := Bx.flip) hconv

end ImageBifunClosed



/-! ### The inner product of a convex and a concave function -/

section FenchelPairing

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
variable {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f : E → EReal} {g : F → EReal}

/-- The **sup side** of Rockafellar's inner product `⟨f, g⟩` of a convex `f` on `E` and a concave
`g` on the paired space `F`: `sup_x {g*(x) - f(x)}`. -/
noncomputable def fenchelSup (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) (g : F → EReal) : EReal :=
  ⨆ x : E, (concaveConj B.flip g x - f x)

/-- The **inf side** of `⟨f, g⟩`: `inf_y {f*(y) - g(y)}`. -/
noncomputable def fenchelInf (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) (g : F → EReal) : EReal :=
  ⨅ y : F, (conj B f y - g y)

theorem fenchelSup_apply (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) (g : F → EReal) :
    fenchelSup B f g = ⨆ x : E, (concaveConj B.flip g x - f x) := rfl

theorem fenchelInf_apply (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) (g : F → EReal) :
    fenchelInf B f g = ⨅ y : F, (conj B f y - g y) := rfl

/-- Rockafellar's inner product `⟨f, g⟩` **exists** exactly when the two extrema agree; when they
do not, `⟨f, g⟩` is undefined. -/
def HasFenchelPairing (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) (g : F → EReal) : Prop :=
  fenchelSup B f g = fenchelInf B f g

/-- The value of Rockafellar's `⟨f, g⟩`, represented by the inf side.

Only under `HasFenchelPairing` is this Rockafellar's inner product;
`HasFenchelPairing.fenchelSup_eq` is the statement that the sup side then agrees. -/
noncomputable def fenchelPairing (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) (g : F → EReal) : EReal :=
  fenchelInf B f g

theorem HasFenchelPairing.fenchelSup_eq (h : HasFenchelPairing B f g) :
    fenchelSup B f g = fenchelPairing B f g := h

theorem fenchelPairing_eq_fenchelInf (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) (g : F → EReal) :
    fenchelPairing B f g = fenchelInf B f g := rfl

/-- **Weak duality for the inner product**: the sup side never exceeds the inf side.

No hypothesis at all; both `∞ - ∞` collisions are absorbed on the correct side, exactly as in
`concaveConj_sub_conj_le_sub`. -/
theorem fenchelSup_le_fenchelInf (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) (g : F → EReal) :
    fenchelSup B f g ≤ fenchelInf B f g := by
  refine iSup_le fun x => le_iInf fun y => ?_
  have hsub : ∀ {p q r : EReal}, p ≤ q → p - r ≤ q - r := fun h => add_le_add h le_rfl
  have h1 : concaveConj B.flip g x ≤ ((B x y : ℝ) : EReal) - g y := concaveConj_le_sub B.flip g y x
  have h2 : ((B x y : ℝ) : EReal) - f x ≤ conj B f y := sub_le_conj B f x y
  calc concaveConj B.flip g x - f x
      ≤ (((B x y : ℝ) : EReal) - g y) - f x := hsub h1
    _ = (((B x y : ℝ) : EReal) - f x) - g y := by
        change ((B x y : ℝ) : EReal) + -(g y) + -(f x)
          = ((B x y : ℝ) : EReal) + -(f x) + -(g y)
        exact add_right_comm _ _ _
    _ ≤ conj B f y - g y := hsub h2

theorem hasFenchelPairing_of_le (h : fenchelInf B f g ≤ fenchelSup B f g) :
    HasFenchelPairing B f g :=
  le_antisymm (fenchelSup_le_fenchelInf B f g) h

end FenchelPairing

/-! ### Conjugation reverses the inner product -/

section FenchelPairingConj

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
variable {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f : E → EReal} {g : F → EReal}

/-- One of the two outer steps of the four-term chain below: the inf side of `⟨f*, g*⟩` is at most
`-⟨f, g⟩` read on the sup side. It rests only on `f** ≤ f`. -/
theorem fenchelInf_conj_le_neg_fenchelSup (hf : Proper f) (hg : ProperConcave g) :
    fenchelInf B.flip (conj B f) (concaveConj B.flip g) ≤ -(fenchelSup B f g) := by
  have hneg : -(fenchelSup B f g) = ⨅ x : E, (f x - concaveConj B.flip g x) := by
    rw [fenchelSup_apply, EReal.neg_iSup]
    exact iInf_congr fun x =>
      EReal.neg_sub_comm (.inr (hf.ne_bot x)) (.inl (concaveConj_ne_top hg.domConcave_nonempty x))
  rw [hneg, fenchelInf_apply]
  exact iInf_mono fun x => add_le_add (biconj_le B f x) le_rfl

/-- The other outer step: `-⟨f, g⟩` read on the inf side is at most the sup side of `⟨f*, g*⟩`.
It rests only on `g ≤ g**`. -/
theorem neg_fenchelInf_le_fenchelSup_conj (hf : Proper f) (hg : ProperConcave g) :
    -(fenchelInf B f g) ≤ fenchelSup B.flip (conj B f) (concaveConj B.flip g) := by
  have hneg : -(fenchelInf B f g) = ⨆ y : F, (g y - conj B f y) := by
    rw [fenchelInf_apply, EReal.neg_iInf]
    exact iSup_congr fun y =>
      EReal.neg_sub_comm (.inl (conj_ne_bot hf.dom_nonempty y)) (.inr (hg.ne_top y))
  rw [hneg, fenchelSup_apply]
  exact iSup_mono fun y => add_le_add (le_biconcaveConj B.flip g y) le_rfl

/-- **If `⟨f, g⟩` exists then so does `⟨f*, g*⟩`.**

The proof is the chain `-⟨f, g⟩ ≤ ⟨f*, g*⟩_sup ≤ ⟨f*, g*⟩_inf ≤ -⟨f, g⟩`, the middle link being
weak duality; when the two ends coincide all four terms do. -/
theorem hasFenchelPairing_conj (hf : Proper f) (hg : ProperConcave g)
    (h : HasFenchelPairing B f g) :
    HasFenchelPairing B.flip (conj B f) (concaveConj B.flip g) := by
  refine hasFenchelPairing_of_le (le_trans (fenchelInf_conj_le_neg_fenchelSup hf hg) ?_)
  rw [h]
  exact neg_fenchelInf_le_fenchelSup_conj hf hg

/-- **Conjugation reverses the inner product**: `⟨f*, g*⟩ = -⟨f, g⟩`. -/
theorem fenchelPairing_conj (hf : Proper f) (hg : ProperConcave g)
    (h : HasFenchelPairing B f g) :
    fenchelPairing B.flip (conj B f) (concaveConj B.flip g) = -(fenchelPairing B f g) := by
  refine le_antisymm ?_ ?_
  · refine le_trans (fenchelInf_conj_le_neg_fenchelSup hf hg) (le_of_eq ?_)
    rw [fenchelPairing_eq_fenchelInf, ← h]
  · simp only [fenchelPairing_eq_fenchelInf]
    rw [← hasFenchelPairing_conj hf hg h]
    exact neg_fenchelInf_le_fenchelSup_conj hf hg

end FenchelPairingConj

/-! ### An adjoint moves across the inner product -/

section AdjointAcrossAux

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

/-- `⟨f*, g⟩` read on the sup side is minus `⟨f, g*⟩` read on the inf side.

This is pure sign bookkeeping, and it is the step that lets an adjoint move across the inner
product. -/
theorem fenchelSup_conj_eq_neg_fenchelInf (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) {f h : E → EReal}
    (hd : (dom f).Nonempty) (hh : (domConcave h).Nonempty) :
    fenchelSup B.flip (conj B f) h = -(fenchelInf B f (concaveConj B h)) := by
  rw [fenchelSup_apply, fenchelInf_apply, EReal.neg_iInf]
  refine iSup_congr fun y => ?_
  rw [LinearMap.flip_flip]
  exact (EReal.neg_sub_comm (.inl (conj_ne_bot hd y)) (.inr (concaveConj_ne_top hh y))).symm

end AdjointAcrossAux

section AdjointAcrossBracket

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
variable [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
variable {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ} {F : Bifun U X}
variable {f : U → EReal} {g : X → EReal}

/-- The bracket `⟨Fu, y⟩` is below the concave biconjugate that `⟨f, F* y⟩` sees. This is
`le_biconcaveConj` after `adjointBifun_eq_concaveConj_bracket`, and it is what makes the existence
of `⟨f, F* y⟩` free. -/
theorem bracket_le_concaveConj_adjointBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (F : Bifun U X) (y : Y) (u : U) :
    bracket Bx F u y ≤ concaveConj Bu.flip (adjointBifun Bu Bx F y) u := by
  have hrw : adjointBifun Bu Bx F y = concaveConj Bu (fun u => bracket Bx F u y) :=
    funext fun v => adjointBifun_eq_concaveConj_bracket Bu Bx F y v
  rw [hrw]
  exact le_biconcaveConj Bu (fun u => bracket Bx F u y) u

/-- **The inner product `⟨f, F* y⟩` exists**, its two extrema agreeing.

Weak duality gives one inequality for free; the other is `conj_imageBifun` together with
`bracket_le_concaveConj_adjointBifun`. -/
theorem hasFenchelPairing_adjointBifun (hbF : ∀ u x, F u x ≠ ⊥) (hf : Proper f) {y : Y}
    (hex : IsExactSum Bu f (fun u => -(bracket Bx F u y))) :
    HasFenchelPairing Bu f (adjointBifun Bu Bx F y) := by
  refine hasFenchelPairing_of_le ?_
  have h1 : fenchelInf Bu f (adjointBifun Bu Bx F y) = ⨆ u, (bracket Bx F u y - f u) := by
    rw [fenchelInf_apply, ← conj_imageBifun hbF hf hex, conj_imageBifun_eq_iSup hbF hf.ne_bot y]
  rw [h1, fenchelSup_apply]
  exact iSup_mono fun u =>
    add_le_add (bracket_le_concaveConj_adjointBifun Bu Bx F y u) le_rfl

/-- **An adjoint moves across the inner product**: `⟨Ff, y⟩ = ⟨f, F* y⟩`.

The left-hand side is the bracket `⟨Ff, x*⟩`, i.e. `(Ff)*(x*)`; the right-hand side is the inner
product of the convex `f` with the concave function `F* x*`. -/
theorem conj_imageBifun_eq_fenchelPairing (hbF : ∀ u x, F u x ≠ ⊥) (hf : Proper f) {y : Y}
    (hex : IsExactSum Bu f (fun u => -(bracket Bx F u y))) :
    conj Bx (imageBifun F f) y = fenchelPairing Bu f (adjointBifun Bu Bx F y) :=
  conj_imageBifun hbF hf hex

end AdjointAcrossBracket

section AdjointAcross

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
variable [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
variable {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ} {F : Bifun U X}
variable {f : U → EReal} {g : X → EReal}

/-- The image `F* g*` of a concave conjugate under the adjoint is nowhere `⊤`, provided `F` is
finite at some `(u₀, x₀)` at which `g` is finite.

The bound is uniform in `y` because the two occurrences of `⟨x₀, y⟩` cancel: every term of the
supremum is bounded by `F u₀ x₀ + ⟨u₀, v⟩ - g x₀`. -/
theorem concaveImageBifun_adjointBifun_ne_top (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) {u₀ : U} {x₀ : X} (hF : F u₀ x₀ ≠ ⊤) (hgb : g x₀ ≠ ⊥)
    (hgt : g x₀ ≠ ⊤) (v : V) :
    concaveImageBifun (adjointBifun Bu Bx F) (concaveConj Bx g) v ≠ ⊤ := by
  obtain ⟨r, hr⟩ := EReal.exists_coe_of_ne_bot_of_lt_top hgb (lt_top_iff_ne_top.2 hgt)
  have hbound : ∀ y : Y, concaveConj Bx g y + adjointBifun Bu Bx F y v
      ≤ F u₀ x₀ + ((Bu u₀ v - r : ℝ) : EReal) := by
    intro y
    have h1 : concaveConj Bx g y ≤ ((Bx x₀ y : ℝ) : EReal) - g x₀ := concaveConj_le_sub Bx g x₀ y
    have h2 : adjointBifun Bu Bx F y v ≤ F u₀ x₀ + ((Bu u₀ v - Bx x₀ y : ℝ) : EReal) :=
      iInf_le _ (u₀, x₀)
    refine le_trans (add_le_add h1 h2) (le_of_eq ?_)
    rw [hr, ← EReal.coe_sub, add_left_comm, ← EReal.coe_add]
    congr 2
    ring
  exact ne_top_of_le_ne_top (add_coe_ne_top hF _) (iSup_le hbound)

/-- **The "by definition" identity behind `⟨Ff, g*⟩ = ⟨f, F* g*⟩`**: `⟨F⁎* f*, g⟩` on the sup side
is minus `⟨f, F* g*⟩` on the inf side.

Both unwind to the same double extremum over `V × Y`, term by term
`⟨F* y, g*⟩ - f*(v) = (g*(y) + (F* y)(v)) - f*(v)`. -/
theorem fenchelSup_imageBifun_lowerAdjointBifun (hf : Proper f) {u₀ : U} {x₀ : X}
    (hF : F u₀ x₀ ≠ ⊤) (hgb : g x₀ ≠ ⊥) (hgt : g x₀ ≠ ⊤) :
    fenchelSup Bx.flip (imageBifun (lowerAdjointBifun Bu Bx F) (conj Bu f)) g
      = -(fenchelInf Bu f (concaveImageBifun (adjointBifun Bu Bx F) (concaveConj Bx g))) := by
  have hane : ∀ v : V, conj Bu f v ≠ ⊥ := fun v => conj_ne_bot hf.dom_nonempty v
  have hcne : ∀ (y : Y) (v : V), adjointBifun Bu Bx F y v ≠ ⊤ :=
    fun y v => adjointBifun_ne_top hF Bu Bx y v
  have hL : fenchelSup Bx.flip (imageBifun (lowerAdjointBifun Bu Bx F) (conj Bu f)) g
      = ⨆ y : Y, ⨆ v : V,
        (concaveConj Bx g y - (conj Bu f v - adjointBifun Bu Bx F y v)) := by
    rw [fenchelSup_apply]
    refine iSup_congr fun y => ?_
    rw [LinearMap.flip_flip]
    have hH : imageBifun (lowerAdjointBifun Bu Bx F) (conj Bu f) y
        = ⨅ v : V, (conj Bu f v - adjointBifun Bu Bx F y v) := rfl
    rw [hH, EReal.sub_iInf]
  have hR : -(fenchelInf Bu f (concaveImageBifun (adjointBifun Bu Bx F) (concaveConj Bx g)))
      = ⨆ v : V, ⨆ y : Y,
        ((concaveConj Bx g y + adjointBifun Bu Bx F y v) - conj Bu f v) := by
    rw [fenchelInf_apply, EReal.neg_iInf]
    refine iSup_congr fun v => ?_
    rw [EReal.neg_sub_comm (.inl (hane v))
        (.inr (concaveImageBifun_adjointBifun_ne_top Bu Bx hF hgb hgt v)),
      concaveImageBifun_apply, EReal.iSup_sub_of_ne_bot _ (hane v)]
  rw [hL, hR, iSup_comm]
  exact iSup_congr fun v => iSup_congr fun y => sub_sub_eq_add_sub (hane v) (hcne y v)

omit [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X] in
/-- If `f` and `F` are both finite at some common `u₀`, the image `Ff` is not identically `⊤`. -/
theorem dom_imageBifun_nonempty (hbF : ∀ u x, F u x ≠ ⊥) (hf : Proper f) {u₀ : U} {x₀ : X}
    (hF : F u₀ x₀ ≠ ⊤) (hfu : f u₀ ≠ ⊤) : (dom (imageBifun F f)).Nonempty := by
  refine ⟨x₀, ?_⟩
  have hle : imageBifun F f x₀ ≤ f u₀ + F u₀ x₀ := iInf_le _ u₀
  have hne : imageBifun F f x₀ ≠ ⊤ := ne_top_of_le_ne_top
    ((EReal.add_ne_top_iff_ne_top₂ (hf.ne_bot u₀) (hbF u₀ x₀)).2 ⟨hfu, hF⟩) hle
  exact lt_top_iff_ne_top.2 hne

/-- **`⟨F⁎* f*, g⟩ = -⟨Ff, g*⟩`**, the third equality of the chain below.

This is `fenchelSup_conj_eq_neg_fenchelInf` composed with `conj_imageBifun`. -/
theorem fenchelSup_imageBifun_lowerAdjointBifun_eq_neg (hbF : ∀ u x, F u x ≠ ⊥) (hf : Proper f)
    (hgd : (domConcave g).Nonempty) {u₀ : U} {x₀ : X} (hF : F u₀ x₀ ≠ ⊤) (hfu : f u₀ ≠ ⊤)
    (hex : ∀ y : Y, IsExactSum Bu f (fun u => -(bracket Bx F u y))) :
    fenchelSup Bx.flip (imageBifun (lowerAdjointBifun Bu Bx F) (conj Bu f)) g
      = -(fenchelInf Bx (imageBifun F f) (concaveConj Bx g)) := by
  have h38 : conj Bx (imageBifun F f) = imageBifun (lowerAdjointBifun Bu Bx F) (conj Bu f) :=
    funext fun y => conj_imageBifun hbF hf (hex y)
  rw [← h38]
  exact fenchelSup_conj_eq_neg_fenchelInf Bx (dom_imageBifun_nonempty hbF hf hF hfu) hgd

/-- **Adjoints move across the inner product**, `⟨Ff, g*⟩ = ⟨f, F* g*⟩`.

Rockafellar's route is `⟨Ff, g*⟩ = ⟨f, F* g*⟩ = -⟨f*, F⁎ g⟩ = -⟨F⁎* f*, g⟩`, the last step being
`fenchelSup_imageBifun_lowerAdjointBifun` and the other bridge `conj_imageBifun`. The book's
relative-interior hypothesis is carried by `hex` together with a common point `(u₀, x₀)` at which
`f`, `F` and `g` are all finite. The equation is stated between the two *inf* sides; each is
Rockafellar's inner product as soon as the corresponding pairing exists. -/
theorem fenchelInf_imageBifun_eq_fenchelInf_concaveImageBifun (hbF : ∀ u x, F u x ≠ ⊥)
    (hf : Proper f) (hgd : (domConcave g).Nonempty) {u₀ : U} {x₀ : X} (hF : F u₀ x₀ ≠ ⊤)
    (hfu : f u₀ ≠ ⊤) (hgb : g x₀ ≠ ⊥) (hgt : g x₀ ≠ ⊤)
    (hex : ∀ y : Y, IsExactSum Bu f (fun u => -(bracket Bx F u y))) :
    fenchelInf Bx (imageBifun F f) (concaveConj Bx g)
      = fenchelInf Bu f (concaveImageBifun (adjointBifun Bu Bx F) (concaveConj Bx g)) := by
  have h1 := fenchelSup_imageBifun_lowerAdjointBifun_eq_neg hbF hf hgd hF hfu hex
  rw [fenchelSup_imageBifun_lowerAdjointBifun hf hF hgb hgt] at h1
  have h2 := congrArg (fun z : EReal => -z) h1
  simpa using h2.symm

end AdjointAcross

/-! ### Right scalar multiplication -/

section SmulRightBifun

variable {U X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]
variable [AddCommGroup Y] [Module ℝ Y] {F : Bifun U X} {l : ℝ}

/-- Rockafellar's `Fλ`: right scalar multiplication of a bifunction,
`((Fλ) u)(x) = λ (Fu)(λ⁻¹ x)`, applied slice by slice. -/
noncomputable def smulRightBifun (F : Bifun U X) (l : ℝ) : Bifun U X := fun u => smulRight (F u) l

omit [AddCommGroup U] [Module ℝ U] in
theorem smulRightBifun_apply (F : Bifun U X) (l : ℝ) (u : U) :
    smulRightBifun F l u = smulRight (F u) l := rfl

/-- The linear map `(u, x) ↦ (l • u, x)`. -/
def scaleFst (X : Type*) [AddCommGroup X] [Module ℝ X] (l : ℝ) : U × X →ₗ[ℝ] U × X :=
  LinearMap.prod (l • LinearMap.fst ℝ U X) (LinearMap.snd ℝ U X)

@[simp] theorem scaleFst_apply (l : ℝ) (p : U × X) : scaleFst X l p = (l • p.1, p.2) := rfl

/-- The graph function of `Fλ` is a right scalar multiple of the graph function of `F`, read after
the shear `(u, x) ↦ (λu, x)`. This is the linear change of variables `(u, x, μ) ↦ (u, λx, λμ)` of
Rockafellar's proof. -/
theorem graphFn_smulRightBifun (hl : 0 < l) (F : Bifun U X) :
    graphFn (smulRightBifun F l) = smulRight (compLin (graphFn F) (scaleFst X l)) l := by
  funext p
  rw [smulRight_apply_pos hl]
  change smulRight (F p.1) l p.2 = _
  rw [smulRight_apply_pos hl, compLin_apply, scaleFst_apply]
  congr 2
  exact (smul_inv_smul₀ hl.ne' p.1).symm

/-- **`Fλ` is a convex bifunction when `F` is**, for every `λ > 0`. -/
theorem convexBifun_smulRightBifun (hl : 0 < l) (hF : ConvexBifun F) :
    ConvexBifun (smulRightBifun F l) := by
  rw [ConvexBifun, graphFn_smulRightBifun hl F]
  exact convexFn_smulRight l (convexFn_compLin _ hF)

omit [AddCommGroup U] [Module ℝ U] in
/-- **The bracket scales with the bifunction**:
`⟨(Fλ) u, x*⟩ = λ ⟨Fu, x*⟩`. It is the conjugation rule `conj_smulRight`, slice by slice. -/
theorem bracket_smulRightBifun (hl : 0 < l) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (F : Bifun U X) (u : U) :
    bracket Bx (smulRightBifun F l) u = fun y => (l : EReal) * bracket Bx F u y :=
  conj_smulRight hl Bx (F u)

end SmulRightBifun

section SmulRightBifunAdjoint

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y] {l : ℝ}

/-- **The adjoint of a right scalar multiple**: `(Fλ)* = F*λ` for `λ > 0`.

Right scalar multiplication commutes with taking adjoints, with no hypothesis beyond `0 < l`: the
infimum defining `((Fλ)* y)(v)` becomes the one defining `((F* y)λ)(v)` under `x ↦ l • x`. -/
theorem adjointBifun_smulRightBifun (hl : 0 < l) (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (F : Bifun U X) (y : Y) (v : V) :
    adjointBifun Bu Bx (smulRightBifun F l) y v = smulRight (adjointBifun Bu Bx F y) l v := by
  have hl0 : l ≠ 0 := ne_of_gt hl
  have hsurj : Function.Surjective (fun p : U × X => (p.1, l • p.2)) := fun q =>
    ⟨(q.1, l⁻¹ • q.2), by rw [Prod.mk.injEq]; exact ⟨rfl, smul_inv_smul₀ hl0 q.2⟩⟩
  rw [smulRight_apply_pos hl, adjointBifun_apply, adjointBifun_apply,
    EReal.coe_mul_iInf hl, ← hsurj.iInf_comp]
  refine iInf_congr fun p => ?_
  rw [smulRightBifun_apply, smulRight_apply_pos hl, inv_smul_smul₀ hl0,
    EReal.left_distrib_of_nonneg_of_ne_top (by exact_mod_cast hl.le) (EReal.coe_ne_top l),
    ← EReal.coe_mul]
  have hr : l * (Bu p.1 (l⁻¹ • v) - Bx p.2 y) = Bu p.1 v - Bx (l • p.2) y := by
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    field_simp
  rw [hr]

end SmulRightBifunAdjoint

/-! ### Composition of bifunctions -/

section CompBifun

section Defs

variable {U X Y : Type*}

/-- Rockafellar's product `GF` of bifunctions: `((GF) u)(y) = ⨅ x, (Fu)(x) + (Gx)(y)`.

When `F` and `G` are the convex indicator bifunctions of linear maps `A` and `B`, `GF` is the
indicator bifunction of `B ∘ A`. -/
noncomputable def compBifun (G : Bifun X Y) (F : Bifun U X) : Bifun U Y :=
  fun u y => ⨅ x, F u x + G x y

theorem compBifun_apply (G : Bifun X Y) (F : Bifun U X) (u : U) (y : Y) :
    compBifun G F u y = ⨅ x, F u x + G x y := rfl

/-- The composition of *concave* bifunctions: the same formula with a supremum. -/
noncomputable def concaveCompBifun (G : Bifun Y X) (F : Bifun X U) : Bifun Y U :=
  fun y u => ⨆ x, G y x + F x u

theorem concaveCompBifun_apply (G : Bifun Y X) (F : Bifun X U) (y : Y) (u : U) :
    concaveCompBifun G F y u = ⨆ x, G y x + F x u := rfl

/-- **The inverse of a product is the product of the inverses** in the opposite order, with the
concave orientation: `(GF)⁎ = F⁎ G⁎`. -/
theorem inverseBifun_compBifun (G : Bifun X Y) (F : Bifun U X) (hbF : ∀ u x, F u x ≠ ⊥)
    (hbG : ∀ x y, G x y ≠ ⊥) :
    inverseBifun (compBifun G F) = concaveCompBifun (inverseBifun G) (inverseBifun F) := by
  funext y u
  rw [inverseBifun_apply, compBifun_apply, EReal.neg_iInf, concaveCompBifun_apply]
  refine iSup_congr fun x => ?_
  have h : -(F u x + G x y) = -(F u x) + -(G x y) :=
    EReal.neg_add (.inl (hbF u x)) (.inr (hbG x y))
  rw [h, inverseBifun_apply, inverseBifun_apply, add_comm]

end Defs

variable {U X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]
variable [AddCommGroup Y] [Module ℝ Y] {F : Bifun U X} {G : Bifun X Y}

/-- The linear map `((u, y), x) ↦ (u, x)`. -/
def compLeft (U X Y : Type*) [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]
    [AddCommGroup Y] [Module ℝ Y] : (U × Y) × X →ₗ[ℝ] U × X :=
  LinearMap.prod (LinearMap.fst ℝ U Y ∘ₗ LinearMap.fst ℝ (U × Y) X) (LinearMap.snd ℝ (U × Y) X)

@[simp] theorem compLeft_apply (q : (U × Y) × X) : compLeft U X Y q = (q.1.1, q.2) := rfl

/-- The linear map `((u, y), x) ↦ (x, y)`. -/
def compRight (U X Y : Type*) [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]
    [AddCommGroup Y] [Module ℝ Y] : (U × Y) × X →ₗ[ℝ] X × Y :=
  LinearMap.prod (LinearMap.snd ℝ (U × Y) X) (LinearMap.snd ℝ U Y ∘ₗ LinearMap.fst ℝ (U × Y) X)

@[simp] theorem compRight_apply (q : (U × Y) × X) : compRight U X Y q = (q.2, q.1.2) := rfl

/-- **A product of convex bifunctions is convex.**

`(u, x, y) ↦ (Fu)(x) + (Gx)(y)` is convex on `U × X × Y`, and the graph function of `GF` is its
image under the projection `(u, x, y) ↦ (u, y)`. -/
theorem convexBifun_compBifun (hbF : ∀ u x, F u x ≠ ⊥) (hbG : ∀ x y, G x y ≠ ⊥)
    (hF : ConvexBifun F) (hG : ConvexBifun G) : ConvexBifun (compBifun G F) := by
  have hh : ConvexFn (compLin (graphFn F) (compLeft U X Y)
      + compLin (graphFn G) (compRight U X Y)) :=
    ConvexFn.add (convexFn_compLin _ hF) (convexFn_compLin _ hG)
      (fun q => hbF _ _) (fun q => hbG _ _)
  exact convexFn_iInf_right hh

end CompBifun

/-! ### The adjoint of a product -/

section AdjointCompBifun

variable {U V X W Y Z : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup W] [Module ℝ W]
  [AddCommGroup Y] [Module ℝ Y] [AddCommGroup Z] [Module ℝ Z]
  {F : Bifun U X} {G : Bifun X Y}

omit [AddCommGroup X] [Module ℝ X] in
/-- Rockafellar's `f(x) = ⟨u*, F⁎x⟩` is the image `Fℓ` of the *linear* function `ℓ u = ⟨u, u*⟩`
under `F`. Both sides are `⨅ u, ⟨u, u*⟩ + (Fu)(x)`; the only step is `-(-(Fu)(x)) = (Fu)(x)`. -/
theorem concaveBracket_inverseBifun_eq_imageBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (F : Bifun U X) (v : V) :
    concaveBracket Bu.flip (inverseBifun F) v = imageBifun F fun u => ((Bu u v : ℝ) : EReal) := by
  funext x
  rw [concaveBracket_apply, imageBifun_apply]
  refine iInf_congr fun u => ?_
  rw [inverseBifun_apply, LinearMap.flip_apply]
  change ((Bu u v : ℝ) : EReal) + -(-(F u x)) = _
  rw [neg_neg]

/-- The conjugate of `⟨u*, F⁎·⟩` is `-(F* ·)(u*)`. This is the entry that turns Fenchel's dual
value into the adjoint of `F`; it is `conj_imageBifun_eq_iSup` read at a linear `f`. -/
theorem conj_concaveBracket_inverseBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] W →ₗ[ℝ] ℝ)
    (hbF : ∀ u x, F u x ≠ ⊥) (v : V) (w : W) :
    conj Bx (concaveBracket Bu.flip (inverseBifun F) v) w = -(adjointBifun Bu Bx F w v) := by
  rw [concaveBracket_inverseBifun_eq_imageBifun,
    conj_imageBifun_eq_iSup hbF (fun _ => EReal.coe_ne_bot _),
    adjointBifun_eq_concaveConj_bracket, concaveConj_apply, EReal.neg_iInf]
  exact iSup_congr fun u => (EReal.neg_coe_sub _ _).symm

omit [AddCommGroup X] [Module ℝ X] in
/-- **The primal problem behind the adjoint of a product.** `((GF)* z)(v)` is the infimum over `x`
of the difference between the convex `⟨v, F⁎x⟩` and the concave `⟨Gx, z⟩`.

This is the whole `EReal` content of Rockafellar's proof: the triple infimum defining
`((GF)* z)(v)` is reindexed as `⨅ x ⨅ u ⨅ y`, and the inner double infimum splits because neither
half is `-∞` — exactly the properness Fenchel's duality theorem will demand. -/
theorem adjointBifun_compBifun_eq_iInf (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (By : Y →ₗ[ℝ] Z →ₗ[ℝ] ℝ)
    (F : Bifun U X) (G : Bifun X Y) {z : Z} {v : V}
    (hfb : ∀ x, concaveBracket Bu.flip (inverseBifun F) v x ≠ ⊥)
    (hgt : ∀ x, bracket By G x z ≠ ⊤) :
    adjointBifun Bu By (compBifun G F) z v
      = ⨅ x, (concaveBracket Bu.flip (inverseBifun F) v x - bracket By G x z) := by
  have hgb : ∀ x : X, (⨅ y, (G x y - ((By y z : ℝ) : EReal))) = -(bracket By G x z) := by
    intro x
    rw [bracket_apply, EReal.neg_iSup]
    exact iInf_congr fun y => (EReal.neg_coe_sub _ _).symm
  have hfa : ∀ x : X, (⨅ u, (((Bu u v : ℝ) : EReal) + F u x))
      = concaveBracket Bu.flip (inverseBifun F) v x := by
    intro x
    rw [concaveBracket_inverseBifun_eq_imageBifun, imageBifun_apply]
  have hstep : ∀ (u : U) (y : Y),
      compBifun G F u y + ((Bu u v - By y z : ℝ) : EReal)
        = ⨅ x, ((((Bu u v : ℝ) : EReal) + F u x) + (G x y - ((By y z : ℝ) : EReal))) := by
    intro u y
    rw [compBifun_apply, EReal.iInf_add_coe]
    refine iInf_congr fun x => ?_
    rw [EReal.coe_sub]
    change (F u x + G x y) + (((Bu u v : ℝ) : EReal) + -((By y z : ℝ) : EReal))
      = (((Bu u v : ℝ) : EReal) + F u x) + (G x y + -((By y z : ℝ) : EReal))
    ac_rfl
  rw [adjointBifun_apply, iInf_prod]
  calc (⨅ u, ⨅ y, (compBifun G F u y + ((Bu u v - By y z : ℝ) : EReal)))
      = ⨅ u, ⨅ y, ⨅ x, ((((Bu u v : ℝ) : EReal) + F u x)
          + (G x y - ((By y z : ℝ) : EReal))) := by
        exact iInf_congr fun u => iInf_congr fun y => hstep u y
    _ = ⨅ x, ⨅ u, ⨅ y, ((((Bu u v : ℝ) : EReal) + F u x)
          + (G x y - ((By y z : ℝ) : EReal))) := by
        have hswap : ∀ u : U, (⨅ y : Y, ⨅ x : X, ((((Bu u v : ℝ) : EReal) + F u x)
              + (G x y - ((By y z : ℝ) : EReal))))
            = ⨅ x : X, ⨅ y : Y, ((((Bu u v : ℝ) : EReal) + F u x)
              + (G x y - ((By y z : ℝ) : EReal))) := fun u => iInf_comm
        rw [iInf_congr hswap, iInf_comm]
    _ = ⨅ x, (concaveBracket Bu.flip (inverseBifun F) v x - bracket By G x z) := by
        refine iInf_congr fun x => ?_
        rw [← EReal.iInf_add_iInf_of_ne_bot _ _ (by rw [hfa x]; exact hfb x)
          (by rw [hgb x]; simpa using hgt x), hfa x, hgb x]
        rfl

/-- **The adjoint of a product is the product of the adjoints**, `(GF)* = F* G*`, the right-hand
side being the *concave* product, `((F* G*) z)(v) = ⨆ w, ((G* z)(w) + (F* w)(v))`.

The proof is Rockafellar's: Fenchel's duality theorem applied to `f(x) = ⟨v, F⁎x⟩` and
`g(x) = ⟨Gx, z⟩`, with `adjointBifun_compBifun_eq_iInf` for the primal side. His
`ri (dom F⁎) ∩ ri (dom G) ≠ ∅` is again an `IsExactSum` — one instance per `(z, v)`, since `f` and
`g` depend on them, where his single condition does not. Like `conj_imageBifun` it carries the
properness selecting the main branch; his degenerate branches `z ∉ dom G*` and `v ∉ dom F⁎*` are
where `f` or `g` fails to be proper. -/
theorem adjointBifun_compBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] W →ₗ[ℝ] ℝ)
    (By : Y →ₗ[ℝ] Z →ₗ[ℝ] ℝ) (hbF : ∀ u x, F u x ≠ ⊥) {z : Z} {v : V}
    (hex : IsExactSum Bx (concaveBracket Bu.flip (inverseBifun F) v)
      (fun x => -(bracket By G x z))) :
    adjointBifun Bu By (compBifun G F) z v
      = concaveCompBifun (adjointBifun Bx By G) (adjointBifun Bu Bx F) z v := by
  have hex' : IsExactSum Bx (concaveBracket Bu.flip (inverseBifun F) v)
      (-fun x => bracket By G x z) := hex
  have hgt : ∀ x, bracket By G x z ≠ ⊤ := fun x hx =>
    hex'.proper_right.ne_bot x (by simp [Pi.neg_apply, hx])
  rw [adjointBifun_compBifun_eq_iInf Bu By F G hex'.proper_left.ne_bot hgt,
    fenchel_duality hex', concaveCompBifun_apply]
  refine iSup_congr fun w => ?_
  rw [conj_concaveBracket_inverseBifun Bu Bx hbF v w, ← adjointBifun_eq_concaveConj_bracket]
  change _ + - -(adjointBifun Bu Bx F w v) = _
  rw [neg_neg]

/-- **The adjoint of a product in the `F⁎*` packaging**: `(GF)⁎* = (G⁎*)(F⁎*)`.

Inversion reverses the order twice, so the composite on the right is taken in the *same* order as
`GF`, and both sides are convex bifunctions — no concave product is needed. The two `≠ ⊤`
hypotheses are what let the negation split across the sum. -/
theorem lowerAdjointBifun_compBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] W →ₗ[ℝ] ℝ)
    (By : Y →ₗ[ℝ] Z →ₗ[ℝ] ℝ) (hbF : ∀ u x, F u x ≠ ⊥) {u₀ : U} {x₀ : X} (hFp : F u₀ x₀ ≠ ⊤)
    {x₁ : X} {y₁ : Y} (hGp : G x₁ y₁ ≠ ⊤) {z : Z} {v : V}
    (hex : IsExactSum Bx (concaveBracket Bu.flip (inverseBifun F) v)
      (fun x => -(bracket By G x z))) :
    lowerAdjointBifun Bu By (compBifun G F) v z
      = compBifun (lowerAdjointBifun Bx By G) (lowerAdjointBifun Bu Bx F) v z := by
  rw [lowerAdjointBifun_apply, adjointBifun_compBifun Bu Bx By hbF hex, concaveCompBifun_apply,
    EReal.neg_iSup, compBifun_apply]
  refine iInf_congr fun w => ?_
  have h : -(adjointBifun Bx By G z w + adjointBifun Bu Bx F w v)
      = -(adjointBifun Bx By G z w) + -(adjointBifun Bu Bx F w v) :=
    EReal.neg_add (.inr (adjointBifun_ne_top hFp Bu Bx w v))
      (.inl (adjointBifun_ne_top hGp Bx By z w))
  rw [h, lowerAdjointBifun_apply, lowerAdjointBifun_apply, add_comm]

/-- **The supremum defining `((F* G*) z)(v)` is attained**, under the hypothesis of
`adjointBifun_compBifun`. -/
theorem exists_adjointBifun_compBifun_eq (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] W →ₗ[ℝ] ℝ)
    (By : Y →ₗ[ℝ] Z →ₗ[ℝ] ℝ) (hbF : ∀ u x, F u x ≠ ⊥) {z : Z} {v : V}
    (hex : IsExactSum Bx (concaveBracket Bu.flip (inverseBifun F) v)
      (fun x => -(bracket By G x z))) :
    ∃ w : W, adjointBifun Bx By G z w + adjointBifun Bu Bx F w v
      = adjointBifun Bu By (compBifun G F) z v := by
  have hex' : IsExactSum Bx (concaveBracket Bu.flip (inverseBifun F) v)
      (-fun x => bracket By G x z) := hex
  have hgt : ∀ x, bracket By G x z ≠ ⊤ := fun x hx =>
    hex'.proper_right.ne_bot x (by simp [Pi.neg_apply, hx])
  obtain ⟨w, hw⟩ := exists_concaveConj_sub_conj_eq hex'
  refine ⟨w, ?_⟩
  rw [adjointBifun_compBifun_eq_iInf Bu By F G hex'.proper_left.ne_bot hgt, ← hw,
    conj_concaveBracket_inverseBifun Bu Bx hbF v w, ← adjointBifun_eq_concaveConj_bracket]
  change _ = _ + - -(adjointBifun Bu Bx F w v)
  rw [neg_neg]

end AdjointCompBifun


/-! ### Products of closed proper convex bifunctions -/

section CompBifunClosed

variable {U V X W Y Z : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup W] [Module ℝ W]
  [AddCommGroup Y] [Module ℝ Y] [AddCommGroup Z] [Module ℝ Z]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X]
  [TopologicalSpace Y] [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y] [LocallyConvexSpace ℝ Y]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsCompatiblePairing Bu] {Bx : X →ₗ[ℝ] W →ₗ[ℝ] ℝ}
  [IsCompatiblePairing Bx] {By : Y →ₗ[ℝ] Z →ₗ[ℝ] ℝ} [IsCompatiblePairing By]
  {F : Bifun U X} {G : Bifun X Y}

/-- `F⁎*` is somewhere `< ⊤`, for a closed proper convex `F`: that is properness of `F*`
(`exists_adjointBifun_ne_bot`) read through the reflection. -/
theorem exists_lowerAdjointBifun_ne_top (hF : ClosedProperConvexFn (graphFn F))
    (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu] (Bx : X →ₗ[ℝ] W →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bx] : ∃ (v : V) (w : W), lowerAdjointBifun Bu Bx F v w ≠ ⊤ := by
  obtain ⟨w, v, hwv⟩ := exists_adjointBifun_ne_bot (Bu := Bu) (Bx := Bx) (F := F) hF
  exact ⟨v, w, by rw [lowerAdjointBifun_apply]; simpa using hwv⟩

/-- **`(G⁎* F⁎*)⁎* = GF`** for closed proper convex `F` and `G` — the identity the rest of the
closed case follows from.

This is `lowerAdjointBifun_compBifun` applied to the pair `(F⁎*, G⁎*)`, whose own lower adjoints
are `F` and `G` again. Rockafellar's condition that `ri (dom F*)` and `ri (dom G⁎*)` have a point
in common is the `IsExactSum` hypothesis, one instance per `(u, y)`. -/
theorem lowerAdjointBifun_compBifun_lowerAdjointBifun
    (hF : ClosedProperConvexFn (graphFn F)) (hG : ClosedProperConvexFn (graphFn G))
    {u : U} {y : Y}
    (hex : IsExactSum Bx.flip (concaveBracket Bu (inverseBifun (lowerAdjointBifun Bu Bx F)) u)
      (fun w => -(bracket By.flip (lowerAdjointBifun Bx By G) w y))) :
    lowerAdjointBifun Bu.flip By.flip
        (compBifun (lowerAdjointBifun Bx By G) (lowerAdjointBifun Bu Bx F)) u y
      = compBifun G F u y := by
  obtain ⟨p₀, hp₀⟩ := hF.proper.dom_nonempty
  obtain ⟨v₁, w₁, hFt⟩ := exists_lowerAdjointBifun_ne_top hF Bu Bx
  obtain ⟨w₂, z₂, hGt⟩ := exists_lowerAdjointBifun_ne_top hG Bx By
  rw [lowerAdjointBifun_compBifun Bu.flip Bx.flip By.flip
      (lowerAdjointBifun_ne_bot (F := F) hp₀.ne Bu Bx) hFt hGt hex,
    lowerAdjointBifun_lowerAdjointBifun_eq_clBifun (Bu := Bx) (Bx := By) hG.convex,
    lowerAdjointBifun_lowerAdjointBifun_eq_clBifun (Bu := Bu) (Bx := Bx) hF.convex,
    ClosedBifun.clBifun_eq hG.closed, ClosedBifun.clBifun_eq hF.closed]

/-- **A product of closed proper convex bifunctions is closed.** It is a lower adjoint. -/
theorem closedBifun_compBifun (hF : ClosedProperConvexFn (graphFn F))
    (hG : ClosedProperConvexFn (graphFn G))
    (hex : ∀ (u : U) (y : Y), IsExactSum Bx.flip
      (concaveBracket Bu (inverseBifun (lowerAdjointBifun Bu Bx F)) u)
      (fun w => -(bracket By.flip (lowerAdjointBifun Bx By G) w y))) :
    ClosedBifun (compBifun G F) := by
  have := isContinuousPairing_prodPairing_flip Bu.flip By.flip
  have hfun : compBifun G F = lowerAdjointBifun Bu.flip By.flip
      (compBifun (lowerAdjointBifun Bx By G) (lowerAdjointBifun Bu Bx F)) :=
    funext fun u => funext fun y =>
      (lowerAdjointBifun_compBifun_lowerAdjointBifun hF hG (hex u y)).symm
  rw [hfun]
  exact closedBifun_lowerAdjointBifun

/-- **The infimum defining `((GF)u)(y)` is attained**, for closed proper convex `F` and `G`. This
is `exists_adjointBifun_compBifun_eq` read at `F⁎*` and `G⁎*`. -/
theorem exists_compBifun_eq (hF : ClosedProperConvexFn (graphFn F))
    (hG : ClosedProperConvexFn (graphFn G)) {u : U} {y : Y}
    (hex : IsExactSum Bx.flip (concaveBracket Bu (inverseBifun (lowerAdjointBifun Bu Bx F)) u)
      (fun w => -(bracket By.flip (lowerAdjointBifun Bx By G) w y))) :
    ∃ x : X, F u x + G x y = compBifun G F u y := by
  obtain ⟨p₀, hp₀⟩ := hF.proper.dom_nonempty
  have hlowF : lowerAdjointBifun Bu.flip Bx.flip (lowerAdjointBifun Bu Bx F) = F :=
    (lowerAdjointBifun_lowerAdjointBifun_eq_clBifun hF.convex).trans
      (ClosedBifun.clBifun_eq hF.closed)
  have hlowG : lowerAdjointBifun Bx.flip By.flip (lowerAdjointBifun Bx By G) = G :=
    (lowerAdjointBifun_lowerAdjointBifun_eq_clBifun hG.convex).trans
      (ClosedBifun.clBifun_eq hG.closed)
  obtain ⟨x, hx⟩ := exists_adjointBifun_compBifun_eq Bu.flip Bx.flip By.flip
    (lowerAdjointBifun_ne_bot (F := F) hp₀.ne Bu Bx) hex
  refine ⟨x, ?_⟩
  have hFadj : adjointBifun Bu.flip Bx.flip (lowerAdjointBifun Bu Bx F) x u = -(F u x) := by
    rw [← neg_neg (adjointBifun Bu.flip Bx.flip (lowerAdjointBifun Bu Bx F) x u)]
    exact congrArg Neg.neg (congrFun (congrFun hlowF u) x)
  have hGadj : adjointBifun Bx.flip By.flip (lowerAdjointBifun Bx By G) y x = -(G x y) := by
    rw [← neg_neg (adjointBifun Bx.flip By.flip (lowerAdjointBifun Bx By G) y x)]
    exact congrArg Neg.neg (congrFun (congrFun hlowG x) y)
  have hcomp : adjointBifun Bu.flip By.flip
      (compBifun (lowerAdjointBifun Bx By G) (lowerAdjointBifun Bu Bx F)) y u
        = -(compBifun G F u y) := by
    rw [← lowerAdjointBifun_compBifun_lowerAdjointBifun hF hG hex]
    exact (neg_neg _).symm
  rw [hFadj, hGadj, hcomp] at hx
  have hGb : G x y ≠ ⊥ := hG.proper.ne_bot (x, y)
  have hFb : F u x ≠ ⊥ := hF.proper.ne_bot (u, x)
  have hsplit : (-(G x y) + -(F u x) : EReal) = -(G x y + F u x) := by
    rw [EReal.neg_add (.inl hGb) (.inr hFb)]
    rfl
  rw [hsplit] at hx
  rw [add_comm]
  exact neg_injective hx

end CompBifunClosed

section CompBifunClosedAdjoint

variable {U V X W Y Z : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup W] [Module ℝ W]
  [AddCommGroup Y] [Module ℝ Y] [AddCommGroup Z] [Module ℝ Z]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X]
  [TopologicalSpace Y] [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y] [LocallyConvexSpace ℝ Y]
  [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [LocallyConvexSpace ℝ V]
  [TopologicalSpace Z] [IsTopologicalAddGroup Z] [ContinuousSMul ℝ Z] [LocallyConvexSpace ℝ Z]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsCompatiblePairing Bu] [IsCompatiblePairing Bu.flip]
  {Bx : X →ₗ[ℝ] W →ₗ[ℝ] ℝ} [IsCompatiblePairing Bx]
  {By : Y →ₗ[ℝ] Z →ₗ[ℝ] ℝ} [IsCompatiblePairing By] [IsCompatiblePairing By.flip]
  {F : Bifun U X} {G : Bifun X Y}

/-- **`(GF)* = cl (F* G*)`** for closed proper convex `F` and `G`, in the `F⁎*` packaging
`(GF)⁎* = cl (G⁎* F⁎*)`.

`GF` is the lower adjoint of `G⁎* F⁎*`, so `(GF)⁎*` is that bifunction's double lower adjoint,
which is its closure. Rockafellar's `cl (F* G*)` is this with the two negations moved outside. -/
theorem lowerAdjointBifun_compBifun_eq_clBifun (hF : ClosedProperConvexFn (graphFn F))
    (hG : ClosedProperConvexFn (graphFn G))
    (hex : ∀ (u : U) (y : Y), IsExactSum Bx.flip
      (concaveBracket Bu (inverseBifun (lowerAdjointBifun Bu Bx F)) u)
      (fun w => -(bracket By.flip (lowerAdjointBifun Bx By G) w y))) :
    lowerAdjointBifun Bu By (compBifun G F)
      = clBifun (compBifun (lowerAdjointBifun Bx By G) (lowerAdjointBifun Bu Bx F)) := by
  obtain ⟨p₀, hp₀⟩ := hF.proper.dom_nonempty
  obtain ⟨q₀, hq₀⟩ := hG.proper.dom_nonempty
  have hconv : ConvexBifun (compBifun (lowerAdjointBifun Bx By G) (lowerAdjointBifun Bu Bx F)) :=
    convexBifun_compBifun (lowerAdjointBifun_ne_bot (F := F) hp₀.ne Bu Bx)
      (lowerAdjointBifun_ne_bot (F := G) hq₀.ne Bx By)
      (convexBifun_lowerAdjointBifun Bu Bx F) (convexBifun_lowerAdjointBifun Bx By G)
  have hfun : compBifun G F = lowerAdjointBifun Bu.flip By.flip
      (compBifun (lowerAdjointBifun Bx By G) (lowerAdjointBifun Bu Bx F)) :=
    funext fun u => funext fun y =>
      (lowerAdjointBifun_compBifun_lowerAdjointBifun hF hG (hex u y)).symm
  have hbi := lowerAdjointBifun_lowerAdjointBifun_eq_clBifun (Bu := Bu.flip) (Bx := By.flip)
    (F := compBifun (lowerAdjointBifun Bx By G) (lowerAdjointBifun Bu Bx F)) hconv
  simp only [LinearMap.flip_flip] at hbi
  rw [hfun, hbi]

end CompBifunClosedAdjoint

/-! ### Infimal convolution in the first variable -/

section InfConvFstBifunDefs

variable {V Y : Type*} [AddCommGroup V]

/-- Infimal convolution of bifunctions in the **first** variable, pointwise in the second:
`(H₁ ⊡ H₂) v y = ⨅ {v₁ + v₂ = v}, H₁ v₁ y + H₂ v₂ y`.

`infConvBifun` convolves in the *second* variable; this is its mirror, and it is the operation the
lower adjoints have to be combined by (`lowerAdjointBifun_infConvFstBifun`). -/
noncomputable def infConvFstBifun (H₁ H₂ : Bifun V Y) : Bifun V Y :=
  fun v y => infConv (fun w => H₁ w y) (fun w => H₂ w y) v

theorem infConvFstBifun_slice (H₁ H₂ : Bifun V Y) (y : Y) :
    (fun v => infConvFstBifun H₁ H₂ v y) = infConv (fun w => H₁ w y) (fun w => H₂ w y) := rfl

theorem infConvFstBifun_comm (H₁ H₂ : Bifun V Y) :
    infConvFstBifun H₁ H₂ = infConvFstBifun H₂ H₁ :=
  funext fun v => funext fun _y => congrFun (infConv_comm _ _) v

theorem infConvFstBifun_assoc (H₁ H₂ H₃ : Bifun V Y) :
    infConvFstBifun (infConvFstBifun H₁ H₂) H₃ = infConvFstBifun H₁ (infConvFstBifun H₂ H₃) :=
  funext fun v => funext fun _y => congrFun (infConv_assoc _ _ _) v

end InfConvFstBifunDefs

section InfConvFstBifunConvex

variable {V Y : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup Y] [Module ℝ Y]
variable {H₁ H₂ : Bifun V Y}

/-- The linear map `((v, y), w) ↦ (v - w, y)`, the left half of the change of variables that turns
a first-variable infimal convolution into a partial minimisation. -/
def infConvFstLeft (V Y : Type*) [AddCommGroup V] [Module ℝ V] [AddCommGroup Y] [Module ℝ Y] :
    (V × Y) × V →ₗ[ℝ] V × Y :=
  LinearMap.prod (LinearMap.fst ℝ V Y ∘ₗ LinearMap.fst ℝ (V × Y) V - LinearMap.snd ℝ (V × Y) V)
    (LinearMap.snd ℝ V Y ∘ₗ LinearMap.fst ℝ (V × Y) V)

@[simp] theorem infConvFstLeft_apply (q : (V × Y) × V) :
    infConvFstLeft V Y q = (q.1.1 - q.2, q.1.2) := rfl

/-- The linear map `((v, y), w) ↦ (w, y)`, the right half of the same change of variables. -/
def infConvFstRight (V Y : Type*) [AddCommGroup V] [Module ℝ V] [AddCommGroup Y] [Module ℝ Y] :
    (V × Y) × V →ₗ[ℝ] V × Y :=
  LinearMap.prod (LinearMap.snd ℝ (V × Y) V) (LinearMap.snd ℝ V Y ∘ₗ LinearMap.fst ℝ (V × Y) V)

@[simp] theorem infConvFstRight_apply (q : (V × Y) × V) :
    infConvFstRight V Y q = (q.2, q.1.2) := rfl

/-- The graph function of `H₁ ⊡ H₂` is a *partial minimisation* of a convex function on
`(V × Y) × V`: the infimum formula for `⊡`, read jointly in `(v, y)`. -/
theorem graphFn_infConvFstBifun (hb₁ : ∀ v y, H₁ v y ≠ ⊥) (hb₂ : ∀ v y, H₂ v y ≠ ⊥) (p : V × Y) :
    graphFn (infConvFstBifun H₁ H₂) p
      = ⨅ w : V, (compLin (graphFn H₁) (infConvFstLeft V Y)
          + compLin (graphFn H₂) (infConvFstRight V Y)) (p, w) := by
  change infConv (fun w => H₁ w p.2) (fun w => H₂ w p.2) p.1 = _
  rw [infConv_apply (fun w => hb₁ w p.2) (fun w => hb₂ w p.2)]
  rfl

/-- `H₁ ⊡ H₂` is a convex bifunction, by the same partial-minimisation argument that makes
`H₁ □ H₂` one. -/
theorem convexBifun_infConvFstBifun (hb₁ : ∀ v y, H₁ v y ≠ ⊥) (hb₂ : ∀ v y, H₂ v y ≠ ⊥)
    (hH₁ : ConvexBifun H₁) (hH₂ : ConvexBifun H₂) : ConvexBifun (infConvFstBifun H₁ H₂) := by
  have hh : ConvexFn (compLin (graphFn H₁) (infConvFstLeft V Y)
      + compLin (graphFn H₂) (infConvFstRight V Y)) :=
    ConvexFn.add (convexFn_compLin _ hH₁) (convexFn_compLin _ hH₂)
      (fun q => hb₁ _ _) (fun q => hb₂ _ _)
  have hgr : graphFn (infConvFstBifun H₁ H₂)
      = fun p : V × Y => ⨅ w : V, (compLin (graphFn H₁) (infConvFstLeft V Y)
          + compLin (graphFn H₂) (infConvFstRight V Y)) (p, w) :=
    funext (graphFn_infConvFstBifun hb₁ hb₂)
  rw [ConvexBifun, hgr]
  exact convexFn_iInf_right hh

end InfConvFstBifunConvex

/-! ### The lower adjoint of a first-variable convolute -/

section ERealAuxFst

private theorem neg_add_coe' (a : EReal) (r : ℝ) :
    -(a + (r : EReal)) = ((-r : ℝ) : EReal) - a := by
  induction a with
  | bot =>
    rw [EReal.bot_add, EReal.neg_bot,
      EReal.sub_bot (EReal.coe_ne_bot _)]
  | coe c =>
    rw [← EReal.coe_add, ← EReal.coe_neg, ← EReal.coe_sub,
      EReal.coe_eq_coe_iff]
    ring
  | top => rw [EReal.top_add_coe, EReal.neg_top, EReal.sub_top]

private theorem neg_add_coe_sub' (a : EReal) (r s : ℝ) :
    -(a + ((r - s : ℝ) : EReal)) = (s : EReal) - (a + (r : EReal)) := by
  induction a with
  | bot =>
    rw [EReal.bot_add, EReal.neg_bot, EReal.bot_add,
      EReal.sub_bot (EReal.coe_ne_bot _)]
  | coe c =>
    rw [← EReal.coe_add, ← EReal.coe_add, ← EReal.coe_neg,
      ← EReal.coe_sub, EReal.coe_eq_coe_iff]
    ring
  | top =>
    rw [EReal.top_add_coe, EReal.neg_top, EReal.top_add_coe,
      EReal.sub_top]

/-- Negation distributes over a sum of two negatives, provided neither original summand is `⊥`.
This is not `EReal.neg_add`, whose second side condition fails when both summands are `⊤` — and
that case is genuinely fine here, since `-(⊥ + ⊥) = ⊤ = ⊤ + ⊤`. -/
private theorem neg_add_neg' {a b : EReal} (ha : a ≠ ⊥) (hb : b ≠ ⊥) :
    -(-a + -b) = a + b := by
  rcases eq_or_ne a ⊤ with rfl | hat
  · rw [EReal.neg_top, EReal.bot_add, EReal.neg_bot,
      EReal.top_add_of_ne_bot hb]
  · rcases eq_or_ne b ⊤ with rfl | hbt
    · rw [EReal.neg_top, EReal.add_bot, EReal.neg_bot,
        EReal.add_top_of_ne_bot ha]
    · rw [EReal.neg_add (.inl (by rw [Ne, EReal.neg_eq_bot_iff]; exact hat))
        (.inl (by rw [Ne, EReal.neg_eq_top_iff]; exact ha)), neg_neg]
      change a + -(-b) = a + b
      rw [neg_neg]

end ERealAuxFst

section LowerAdjointInfConvFst

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
variable [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]

omit [AddCommGroup Y] [Module ℝ Y] in
/-- The bracket that the lower adjoint conjugates: `⟨u, H⁎ y⟩ = ⨅ v, ((H v)(y) + ⟨u, v⟩)`. -/
theorem concaveBracket_inverseBifun_apply (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (H : Bifun V Y) (u : U) (y : Y) :
    concaveBracket Bu (inverseBifun H) u y = ⨅ v : V, (H v y + ((Bu u v : ℝ) : EReal)) := by
  rw [concaveBracket_apply]
  refine iInf_congr fun v => ?_
  change ((Bu u v : ℝ) : EReal) + -(-(H v y)) = _
  rw [neg_neg, add_comm]

omit [AddCommGroup Y] [Module ℝ Y] in
/-- Minus the bracket is a conjugate in the *first* variable, taken at `-u`. -/
theorem neg_concaveBracket_inverseBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (H : Bifun V Y) (u : U) (y : Y) :
    -(concaveBracket Bu (inverseBifun H) u y) = conj Bu.flip (fun v => H v y) (-u) := by
  rw [concaveBracket_inverseBifun_apply, EReal.neg_iInf, conj_apply]
  refine iSup_congr fun v => ?_
  have hr : (Bu.flip v (-u) : ℝ) = -(Bu u v) := by
    rw [LinearMap.flip_apply, map_neg, LinearMap.neg_apply]
  rw [hr]
  exact neg_add_coe' (H v y) (Bu u v)

/-- **The lower adjoint at a fixed `u` is an ordinary conjugate** — of the bracket
`y ↦ ⟨u, H⁎ y⟩`. This is the identity the whole closed case for `□` runs through. -/
theorem lowerAdjointBifun_eq_conj_concaveBracket_inverseBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (H : Bifun V Y) (u : U) :
    lowerAdjointBifun Bu.flip Bx.flip H u
      = conj Bx.flip (concaveBracket Bu (inverseBifun H) u) := by
  funext x
  rw [lowerAdjointBifun_apply, adjointBifun_apply, EReal.neg_iInf, conj_apply, iSup_prod,
    iSup_comm]
  refine iSup_congr fun y => ?_
  rw [concaveBracket_inverseBifun_apply, EReal.coe_sub_iInf]
  refine iSup_congr fun v => ?_
  have hu : (Bu.flip v u : ℝ) = Bu u v := rfl
  have hx : (Bx.flip y x : ℝ) = Bx x y := rfl
  rw [hu, hx]
  exact neg_add_coe_sub' (H v y) (Bu u v) (Bx x y)

omit [AddCommGroup Y] [Module ℝ Y] in
/-- The bracket of a first-variable convolute is the **sum** of the brackets: the unconditional
identity `(f □ g)* = f* + g*`, read in the first variable of a bifunction. -/
theorem concaveBracket_inverseBifun_infConvFstBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (H₁ H₂ : Bifun V Y)
    (u : U) (h₁ : ∀ y, concaveBracket Bu (inverseBifun H₁) u y ≠ ⊥)
    (h₂ : ∀ y, concaveBracket Bu (inverseBifun H₂) u y ≠ ⊥) :
    concaveBracket Bu (inverseBifun (infConvFstBifun H₁ H₂)) u
      = concaveBracket Bu (inverseBifun H₁) u + concaveBracket Bu (inverseBifun H₂) u := by
  funext y
  have hsum : -(concaveBracket Bu (inverseBifun (infConvFstBifun H₁ H₂)) u y)
      = -(concaveBracket Bu (inverseBifun H₁) u y)
        + -(concaveBracket Bu (inverseBifun H₂) u y) := by
    rw [neg_concaveBracket_inverseBifun, neg_concaveBracket_inverseBifun,
      neg_concaveBracket_inverseBifun, infConvFstBifun_slice, conj_infConv]
    rfl
  rw [Pi.add_apply, ← neg_add_neg' (h₁ y) (h₂ y), ← hsum, neg_neg]

/-- **The lower adjoint turns a first-variable convolution into a second-variable one**:
`(H₁ ⊡ H₂)⁎* = H₁⁎* □ H₂⁎*`.

This is the one new theorem the closed case for `□` needs. Written `φᵢ y = ⨅ v, (Hᵢ v y + ⟨u, v⟩)`,
the lower adjoint of `Hᵢ` at `u` *is* `φᵢ*`; `φ = φ₁ + φ₂` for a first-variable convolute with no
hypothesis at all, and an exact conjugate of a sum turns `(φ₁ + φ₂)*` into the infimal convolution.
The hypothesis is Rockafellar's relative-interior condition in `IsExactSum` form, one per `u`. -/
theorem lowerAdjointBifun_infConvFstBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (H₁ H₂ : Bifun V Y) {u : U}
    (hex : IsExactSum Bx.flip (concaveBracket Bu (inverseBifun H₁) u)
      (concaveBracket Bu (inverseBifun H₂) u)) :
    lowerAdjointBifun Bu.flip Bx.flip (infConvFstBifun H₁ H₂) u
      = infConvBifun (lowerAdjointBifun Bu.flip Bx.flip H₁)
          (lowerAdjointBifun Bu.flip Bx.flip H₂) u := by
  rw [lowerAdjointBifun_eq_conj_concaveBracket_inverseBifun,
    concaveBracket_inverseBifun_infConvFstBifun Bu H₁ H₂ u hex.proper_left.ne_bot
      hex.proper_right.ne_bot, hex.conj_add, infConvBifun_apply,
    lowerAdjointBifun_eq_conj_concaveBracket_inverseBifun,
    lowerAdjointBifun_eq_conj_concaveBracket_inverseBifun]

end LowerAdjointInfConvFst

/-! ### Infimal convolutes of closed proper convex bifunctions -/

section InfConvBifunClosed

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsCompatiblePairing Bu]
  {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ} [IsCompatiblePairing Bx]
  {F₁ F₂ : Bifun U X}

/-- **`(F₁⁎* ⊡ F₂⁎*)⁎* = F₁ □ F₂`** for closed proper convex `F₁` and `F₂` — the identity the rest
of the closed case follows from.

This is `lowerAdjointBifun_infConvFstBifun` applied to the pair `(F₁⁎*, F₂⁎*)`, whose own lower
adjoints are `F₁` and `F₂` again. Rockafellar's condition that `ri (dom F₁*)` and `ri (dom F₂*)`
have a point in common is the `IsExactSum` hypothesis, one instance per `u`. -/
theorem lowerAdjointBifun_infConvFstBifun_lowerAdjointBifun (hF₁ : ConvexBifun F₁)
    (hF₁cl : ClosedBifun F₁) (hF₂ : ConvexBifun F₂) (hF₂cl : ClosedBifun F₂) {u : U}
    (hex : IsExactSum Bx.flip
      (concaveBracket Bu (inverseBifun (lowerAdjointBifun Bu Bx F₁)) u)
      (concaveBracket Bu (inverseBifun (lowerAdjointBifun Bu Bx F₂)) u)) :
    lowerAdjointBifun Bu.flip Bx.flip
        (infConvFstBifun (lowerAdjointBifun Bu Bx F₁) (lowerAdjointBifun Bu Bx F₂)) u
      = infConvBifun F₁ F₂ u := by
  rw [lowerAdjointBifun_infConvFstBifun Bu Bx _ _ hex,
    lowerAdjointBifun_lowerAdjointBifun_eq_clBifun hF₁,
    lowerAdjointBifun_lowerAdjointBifun_eq_clBifun hF₂, hF₁cl.clBifun_eq, hF₂cl.clBifun_eq]

theorem infConvBifun_eq_lowerAdjointBifun_infConvFstBifun (hF₁ : ConvexBifun F₁)
    (hF₁cl : ClosedBifun F₁) (hF₂ : ConvexBifun F₂) (hF₂cl : ClosedBifun F₂)
    (hex : ∀ u : U, IsExactSum Bx.flip
      (concaveBracket Bu (inverseBifun (lowerAdjointBifun Bu Bx F₁)) u)
      (concaveBracket Bu (inverseBifun (lowerAdjointBifun Bu Bx F₂)) u)) :
    infConvBifun F₁ F₂ = lowerAdjointBifun Bu.flip Bx.flip
      (infConvFstBifun (lowerAdjointBifun Bu Bx F₁) (lowerAdjointBifun Bu Bx F₂)) :=
  funext fun u =>
    (lowerAdjointBifun_infConvFstBifun_lowerAdjointBifun hF₁ hF₁cl hF₂ hF₂cl (hex u)).symm

/-- **An infimal convolute of closed proper convex bifunctions is closed.** It is a lower adjoint,
and a lower adjoint is closed with no hypothesis at all. -/
theorem closedBifun_infConvBifun (hF₁ : ConvexBifun F₁) (hF₁cl : ClosedBifun F₁)
    (hF₂ : ConvexBifun F₂) (hF₂cl : ClosedBifun F₂)
    (hex : ∀ u : U, IsExactSum Bx.flip
      (concaveBracket Bu (inverseBifun (lowerAdjointBifun Bu Bx F₁)) u)
      (concaveBracket Bu (inverseBifun (lowerAdjointBifun Bu Bx F₂)) u)) :
    ClosedBifun (infConvBifun F₁ F₂) := by
  have := isContinuousPairing_prodPairing_flip Bu.flip Bx.flip
  rw [infConvBifun_eq_lowerAdjointBifun_infConvFstBifun hF₁ hF₁cl hF₂ hF₂cl hex]
  exact closedBifun_lowerAdjointBifun

end InfConvBifunClosed

section InfConvBifunClosedAdjoint

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X]
  [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [LocallyConvexSpace ℝ V]
  [TopologicalSpace Y] [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y] [LocallyConvexSpace ℝ Y]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsCompatiblePairing Bu] [IsCompatiblePairing Bu.flip]
  {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ} [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip]
  {F₁ F₂ : Bifun U X}

/-- **`(F₁ □ F₂)* = cl (F₁* □ F₂*)`** for closed proper convex `F₁` and `F₂`, in the `F⁎*`
packaging `(F₁ □ F₂)⁎* = cl (F₁⁎* ⊡ F₂⁎*)`.

`F₁ □ F₂` is the lower adjoint of `F₁⁎* ⊡ F₂⁎*`, so `(F₁ □ F₂)⁎*` is that bifunction's double
lower adjoint, its closure. The right-hand convolution is in the *first* variable, which is what
Rockafellar's `F₁* □ F₂*` becomes once the two negations are moved outside. -/
theorem lowerAdjointBifun_infConvBifun_eq_clBifun (hF₁ : ClosedProperConvexFn (graphFn F₁))
    (hF₂ : ClosedProperConvexFn (graphFn F₂))
    (hex : ∀ u : U, IsExactSum Bx.flip
      (concaveBracket Bu (inverseBifun (lowerAdjointBifun Bu Bx F₁)) u)
      (concaveBracket Bu (inverseBifun (lowerAdjointBifun Bu Bx F₂)) u)) :
    lowerAdjointBifun Bu Bx (infConvBifun F₁ F₂)
      = clBifun (infConvFstBifun (lowerAdjointBifun Bu Bx F₁) (lowerAdjointBifun Bu Bx F₂)) := by
  obtain ⟨p₁, hp₁⟩ := hF₁.proper.dom_nonempty
  obtain ⟨p₂, hp₂⟩ := hF₂.proper.dom_nonempty
  have hconv : ConvexBifun
      (infConvFstBifun (lowerAdjointBifun Bu Bx F₁) (lowerAdjointBifun Bu Bx F₂)) :=
    convexBifun_infConvFstBifun (lowerAdjointBifun_ne_bot (F := F₁) hp₁.ne Bu Bx)
      (lowerAdjointBifun_ne_bot (F := F₂) hp₂.ne Bu Bx)
      (convexBifun_lowerAdjointBifun Bu Bx F₁) (convexBifun_lowerAdjointBifun Bu Bx F₂)
  have hbi := lowerAdjointBifun_lowerAdjointBifun_eq_clBifun (Bu := Bu.flip) (Bx := Bx.flip)
    (F := infConvFstBifun (lowerAdjointBifun Bu Bx F₁) (lowerAdjointBifun Bu Bx F₂)) hconv
  simp only [LinearMap.flip_flip] at hbi
  rw [infConvBifun_eq_lowerAdjointBifun_infConvFstBifun hF₁.convex hF₁.closed hF₂.convex
    hF₂.closed hex, hbi]

end InfConvBifunClosedAdjoint

/-! ### The inner products of a product of bifunctions -/

section CompBifunPairing

variable {U X W Y Z : Type*} [AddCommGroup X] [Module ℝ X] [AddCommGroup W] [Module ℝ W]
  [AddCommGroup Y] [Module ℝ Y] [AddCommGroup Z] [Module ℝ Z] {F : Bifun U X} {G : Bifun X Y}

omit [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y] in
/-- **A slice of a product is the image of a slice**: `(GF)u = G(Fu)`. Both sides are
`⨅ x, (Fu)(x) + (Gx)(y)`, so this is `rfl`; it is what makes every statement about `⟨GFu, ·⟩` a
statement about an image, and hence a case of `conj_imageBifun` and its inner-product form. -/
theorem compBifun_slice (G : Bifun X Y) (F : Bifun U X) (u : U) :
    compBifun G F u = imageBifun G (F u) := rfl

/-- **The inner product `⟨Fu, G* z⟩` exists**, its two extrema agreeing.

Rockafellar derives the hypothesis, `ri (dom (Fu))` meets `ri (dom G)`, from his condition on
`ri (dom F⁎) ∩ ri (dom G)` by a calculus of relative interiors that he leaves to the reader; here
it is the `IsExactSum` the proof actually consumes, one instance per `(u, z)`. -/
theorem hasFenchelPairing_adjointBifun_slice (Bx : X →ₗ[ℝ] W →ₗ[ℝ] ℝ) (By : Y →ₗ[ℝ] Z →ₗ[ℝ] ℝ)
    (hbG : ∀ x y, G x y ≠ ⊥) {u : U} (hFu : Proper (F u)) {z : Z}
    (hex : IsExactSum Bx (F u) (fun x => -(bracket By G x z))) :
    HasFenchelPairing Bx (F u) (adjointBifun Bx By G z) :=
  hasFenchelPairing_adjointBifun hbG hFu hex

/-- **`⟨GFu, z⟩ = ⟨Fu, G* z⟩`**, an adjoint moving across the inner product at a slice.

This is `conj_imageBifun_eq_fenchelPairing` at the slice `Fu`, since `(GF)u = G(Fu)`. The other
equality `⟨GFu, z⟩ = ⟨u, F* G* z⟩` needs a relative interior; it is
`bracket_compBifun_eq_concaveBracket_concaveCompBifun` in `Bifunction/Cofinite.lean`. -/
theorem bracket_compBifun_eq_fenchelPairing (Bx : X →ₗ[ℝ] W →ₗ[ℝ] ℝ) (By : Y →ₗ[ℝ] Z →ₗ[ℝ] ℝ)
    (hbG : ∀ x y, G x y ≠ ⊥) {u : U} (hFu : Proper (F u)) {z : Z}
    (hex : IsExactSum Bx (F u) (fun x => -(bracket By G x z))) :
    bracket By (compBifun G F) u z = fenchelPairing Bx (F u) (adjointBifun Bx By G z) :=
  conj_imageBifun_eq_fenchelPairing hbG hFu hex

end CompBifunPairing

end ConvexAnalysis
