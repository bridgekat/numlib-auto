import Numlib.Analysis.Convex.Extremum.Normal
import Numlib.Analysis.Convex.Saddle.Closure

/-!
# The correspondence between saddle-functions and bifunctions

The two brackets `⟨Fu, y⟩ = cl₂ K` and `⟨u, F* y⟩ = cl₁ K` set up a one-to-one correspondence
between the *lower closed* concave-convex functions on `U × Y` and the *closed convex* bifunctions
from `U` to `X`; the rest of the saddle-function theory is built on it.

Three refinements follow. Weakening closedness to *image*-closedness on the bifunction side and to
convex-closedness on the function side keeps the bijection; the closure pairs `(K̲, K̄)` are exactly
the pairs of brackets of a closed convex bifunction; and `cl₁` and `cl₂` are inverse bijections
between the lower closed and the upper closed functions. The first has a polyhedral form, with
properness in place of closedness.

## Main definitions

* `saddleOfBifun Bx F` — `⟨Fu, x*⟩` uncurried, so that the correspondence is about a map.
* `bifunSaddleEquiv` — the image-closed form of the correspondence, as an `Equiv`.
* `lowerUpperClosedEquiv` — `cl₁` and `cl₂` as inverse bijections, as an `Equiv`.

## Main results

* `eq_of_bracket_eq` — the bracket determines an image-closed convex bifunction. This is why
  image-closedness has to be named: `bracket Bx F u = conj Bx (F u)` sees only `cl (F u)`.
* `lowerClosedFn_bracket`, `exists_unique_convexBifun_bracket_eq` — the bracket of a closed convex
  bifunction is lower closed, and every lower closed concave-convex function is the bracket of
  exactly one closed convex bifunction ([rockafellar1970convex] Theorem 33.3).
* `exists_unique_bifun_of_closure_pair` — a pair with `cl₁ K̲ = K̄` and `cl₂ K̄ = K̲` is exactly a
  bracket pair; `le_of_partialCl₂_eq` adds `K̲ ≤ K̄`.
* `polyhedralFn_bracket`, `polyhedralFn_neg_bracket`, `imageClosedBifun_of_polyhedralBifun`,
  `eq_convexConj_bracket_of_polyhedralBifun` — the polyhedral case: both variables of the bracket
  are polyhedral, and a proper polyhedral bifunction is recovered from its bracket.

## Implementation notes

Given a lower closed `K`, the bifunction `bifunOfSaddle Bx K` has the right bracket at once, but
its closedness still has to be argued: `cl F` and `F` are both image-closed and convex and have the
same bracket, so they are equal.

## References

* [rockafellar1970convex] §33.
-/

namespace ConvexAnalysis

/-! ### The bracket is injective on image-closed convex bifunctions -/

section Injective

variable {U X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]
  [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace X] [IsTopologicalAddGroup X]
  [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X] {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ}
  [IsCompatiblePairing Bx] {F G : Bifun U X}

/-- **Two image-closed convex bifunctions with the same bracket are equal.** The bracket sees only
`cl (F u)`, and image-closedness says that is all of `F u`. -/
theorem eq_of_bracket_eq (hF : ConvexBifun F) (hG : ConvexBifun G) (hFi : ImageClosedBifun F)
    (hGi : ImageClosedBifun G) (h : bracket Bx F = bracket Bx G) : F = G := by
  funext u
  calc F u = convexCl (F u) := (hFi u).symm
    _ = convexConj Bx.flip (bracket Bx F u) := convexCl_eq_convexConj_bracket hF u
    _ = convexConj Bx.flip (bracket Bx G u) := by rw [h]
    _ = convexCl (G u) := (convexCl_eq_convexConj_bracket hG u).symm
    _ = G u := hGi u

end Injective

/-! ### The correspondence -/

section Correspondence

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X]
  [TopologicalSpace Y] [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y] [LocallyConvexSpace ℝ Y]
  {F : Bifun U X} {K : U × Y → EReal}

omit [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  [LocallyConvexSpace ℝ X] [TopologicalSpace Y] [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y]
  [LocallyConvexSpace ℝ Y] in
/-- The two brackets of a bifunction are related by `cl₁ ⟨Fu, y⟩ = ⟨u, F* y⟩`. -/
theorem partialCl₁_bracket (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu]
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (hF : ConvexBifun F) :
    partialCl₁ (fun p : U × Y => bracket Bx F p.1 p.2)
      = fun p : U × Y => concaveBracket Bu (convexAdjointBifun Bu Bx F) p.1 p.2 := by
  funext p
  exact (congrFun (concaveBracket_convexAdjointBifun_eq_partialCl₁ (Bu := Bu) hF p.2) p.1).symm

/-- For a *closed* bifunction, `cl₂ ⟨u, F* y⟩ = ⟨Fu, y⟩`: the two brackets of a closed convex
bifunction are a closure pair. -/
theorem partialCl₂_concaveBracket_adjoint (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu]
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip]
    (hF : ConvexBifun F) (hcl : ClosedConvexBifun F) :
    partialCl₂ (fun p : U × Y => concaveBracket Bu (convexAdjointBifun Bu Bx F) p.1 p.2)
      = fun p : U × Y => bracket Bx F p.1 p.2 := by
  funext p
  have h2 := bracket_concaveAdjointBifun_eq_partialCl₂ (Bu := Bu) (Bx := Bx)
    (concaveBifun_convexAdjointBifun Bu Bx F) p.1
  rw [concaveAdjointBifun_convexAdjointBifun_eq_convexClBifun hF, hcl.convexClBifun_eq] at h2
  exact (congrFun h2 p.2).symm

/-- One direction of the correspondence: the bracket of a closed convex bifunction is a lower
closed concave-convex function. Each closure step exchanges the two brackets, and the loop closes
because `F** = cl F = F`. -/
theorem lowerClosedFn_bracket (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu]
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip]
    (hF : ConvexBifun F) (hcl : ClosedConvexBifun F) :
    LowerClosedFn (fun p : U × Y => bracket Bx F p.1 p.2) := by
  rw [lowerClosedFn_iff, lowerCl_def, partialCl₁_bracket Bu Bx hF,
    partialCl₂_concaveBracket_adjoint Bu Bx hF hcl]

/-- The other direction: a lower closed concave-convex function is the bracket of one and only
one closed convex bifunction, namely `F u = K(u, ·)*`. -/
theorem exists_unique_convexBifun_bracket_eq (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu]
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip]
    (hK : ConcaveConvexFn K) (hlc : LowerClosedFn K) :
    ∃! F : Bifun U X, ConvexBifun F ∧ ClosedConvexBifun F ∧
      (fun p : U × Y => bracket Bx F p.1 p.2) = K := by
  have hF : ConvexBifun (bifunOfSaddle Bx K) := convexBifun_bifunOfSaddle hK Bx
  have hbr : (fun p : U × Y => bracket Bx (bifunOfSaddle Bx K) p.1 p.2) = K :=
    funext fun p => (bracket_bifunOfSaddle hK p).trans (congrFun hlc.partialClosed₂ p)
  have himg : ImageClosedBifun (bifunOfSaddle Bx K) :=
    fun u => closedConvex_convexConj (B := Bx.flip) (f := fun y => K (u, y))
  have hcl1 : partialCl₁ K
      = fun p : U × Y =>
        concaveBracket Bu (convexAdjointBifun Bu Bx (bifunOfSaddle Bx K)) p.1 p.2 := by
    calc partialCl₁ K
        = partialCl₁ (fun p : U × Y => bracket Bx (bifunOfSaddle Bx K) p.1 p.2) := by rw [hbr]
      _ = _ := by
          funext p
          exact (congrFun (concaveBracket_convexAdjointBifun_eq_partialCl₁ (Bu := Bu) hF p.2)
              p.1).symm
  have hMK : partialCl₂ (fun p : U × Y =>
      concaveBracket Bu (convexAdjointBifun Bu Bx (bifunOfSaddle Bx K)) p.1 p.2) = K := by
    rw [← hcl1]
    exact hlc
  have hclbr : bracket Bx (convexClBifun (bifunOfSaddle Bx K))
      = bracket Bx (bifunOfSaddle Bx K) := by
    funext u y
    have h2 := congrFun
      (partialCl₂_concaveBracket_convexAdjointBifun (Bu := Bu) (Bx := Bx) hF u) y
    rw [← h2, congrFun hMK (u, y)]
    exact (congrFun hbr (u, y)).symm
  have hclF : convexClBifun (bifunOfSaddle Bx K) = bifunOfSaddle Bx K :=
    eq_of_bracket_eq hF.convexClBifun hF
      ((closedConvexBifun_convexClBifun (bifunOfSaddle Bx K)).imageClosedBifun) himg hclbr
  refine ⟨bifunOfSaddle Bx K, ⟨hF, closedConvexBifun_iff_convexClBifun_eq.2 hclF, hbr⟩, ?_⟩
  rintro F' ⟨hF'conv, hF'cl, hF'br⟩
  exact eq_of_bracket_eq hF'conv hF hF'cl.imageClosedBifun himg
    (funext fun u => funext fun y => (congrFun hF'br (u, y)).trans (congrFun hbr (u, y)).symm)

end Correspondence

/-! ### Closure pairs are bracket pairs -/

section ClosurePairOrder

variable {U Y : Type*} [TopologicalSpace Y] {Klow Kup : U × Y → EReal}

/-- A closure pair is ordered, `K̲ ≤ K̄`. Only the `cl₂` relation is needed, because `cl₂`
lowers. -/
theorem le_of_partialCl₂_eq (h2 : partialCl₂ Kup = Klow) : Klow ≤ Kup := by
  rw [← h2]
  exact partialCl₂_le Kup

end ClosurePairOrder

section ClosurePair

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X]
  [TopologicalSpace Y] [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y] [LocallyConvexSpace ℝ Y]
  {Klow Kup : U × Y → EReal}

/-- The pairs `(K̲, K̄)` of concave-convex functions with
`cl₁ K̲ = K̄` and `cl₂ K̄ = K̲` are exactly the pairs of brackets `(⟨Fu, y⟩, ⟨u, F* y⟩)` of a
closed convex bifunction, and `F` is unique. -/
theorem exists_unique_bifun_of_closure_pair (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu]
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip]
    (hK : ConcaveConvexFn Klow) (h1 : partialCl₁ Klow = Kup) (h2 : partialCl₂ Kup = Klow) :
    ∃! F : Bifun U X, ConvexBifun F ∧ ClosedConvexBifun F ∧
      (fun p : U × Y => bracket Bx F p.1 p.2) = Klow ∧
      (fun p : U × Y => concaveBracket Bu (convexAdjointBifun Bu Bx F) p.1 p.2) = Kup := by
  have hlc : LowerClosedFn Klow := by
    rw [lowerClosedFn_iff, lowerCl_def, h1, h2]
  obtain ⟨F, ⟨hFconv, hFcl, hFbr⟩, huniq⟩ :=
    exists_unique_convexBifun_bracket_eq Bu Bx hK hlc
  have hup : (fun p : U × Y => concaveBracket Bu (convexAdjointBifun Bu Bx F) p.1 p.2) = Kup := by
    refine Eq.trans ?_ h1
    rw [← hFbr]
    funext p
    exact congrFun (concaveBracket_convexAdjointBifun_eq_partialCl₁ (Bu := Bu) hFconv p.2) p.1
  refine ⟨F, ⟨hFconv, hFcl, hFbr, hup⟩, ?_⟩
  rintro F' ⟨hF'conv, hF'cl, hF'br, -⟩
  exact huniq F' ⟨hF'conv, hF'cl, hF'br⟩

end ClosurePair

/-! ### The correspondence under image-closedness

The two round trips are the two halves of the bracket construction, and each needs the closedness
hypothesis on its own side: image-closedness of `F`, convex-closedness of `K`. -/

section SaddleOfBifun

variable {U X Y : Type*} [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]

/-- The saddle-function attached to a convex bifunction, `⟨Fu, x*⟩` read as a function of the pair:
`bracket` uncurried, named because the correspondence is a statement about it as a map. -/
noncomputable def saddleOfBifun (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (F : Bifun U X) : U × Y → EReal :=
  fun p => bracket Bx F p.1 p.2

theorem saddleOfBifun_apply (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (F : Bifun U X) (p : U × Y) :
    saddleOfBifun Bx F p = bracket Bx F p.1 p.2 := rfl

end SaddleOfBifun

section SaddleOfBifunClosed

variable {U X Y : Type*} [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace Y] [IsTopologicalAddGroup Y] {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ}
  [IsContinuousPairing Bx.flip] {F : Bifun U X}

/-- The saddle-function of a bifunction is convex-closed: every slice is a conjugate. -/
theorem partialClosed₂_saddleOfBifun : PartialClosed₂ (saddleOfBifun Bx F) :=
  partialClosed₂_iff.2 fun u => closedConvex_bracket u

end SaddleOfBifunClosed

section SaddleOfBifunConvex

variable {U X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]
  [AddCommGroup Y] [Module ℝ Y] {F : Bifun U X}

/-- The saddle-function of a *convex* bifunction is concave-convex. -/
theorem concaveConvexFn_saddleOfBifun (hF : ConvexBifun F) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) :
    ConcaveConvexFn (saddleOfBifun Bx F) := concaveConvexFn_bracket hF Bx

end SaddleOfBifunConvex

section BifunOfSaddleImage

variable {U X Y : Type*} [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace X] [IsTopologicalAddGroup X] {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ}
  [IsContinuousPairing Bx] {K : U × Y → EReal}

/-- The bifunction of a saddle-function is image-closed: every slice is a conjugate. -/
theorem imageClosedBifun_bifunOfSaddle : ImageClosedBifun (bifunOfSaddle Bx K) :=
  fun u => closedConvex_convexConj (B := Bx.flip) (f := fun y => K (u, y))

end BifunOfSaddleImage

section RoundTripRight

variable {U X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]
  [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y]
  [ContinuousSMul ℝ Y] [LocallyConvexSpace ℝ Y] {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ}
  [IsCompatiblePairing Bx.flip] {K : U × Y → EReal}

/-- One round trip: a convex-closed concave-convex `K` is the saddle-function of the bifunction
it defines. -/
theorem saddleOfBifun_bifunOfSaddle (hK : ConcaveConvexFn K) (hcc : PartialClosed₂ K) :
    saddleOfBifun Bx (bifunOfSaddle Bx K) = K :=
  funext fun p => (bracket_bifunOfSaddle hK p).trans (congrFun hcc p)

end RoundTripRight

section RoundTripLeft

variable {U X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]
  [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace X] [IsTopologicalAddGroup X]
  [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X] {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ}
  [IsCompatiblePairing Bx] {F : Bifun U X}

/-- The other round trip: an image-closed convex bifunction is the bifunction of the
saddle-function it defines. -/
theorem bifunOfSaddle_saddleOfBifun (hF : ConvexBifun F) (hFi : ImageClosedBifun F) :
    bifunOfSaddle Bx (saddleOfBifun Bx F) = F :=
  funext fun u => (convexCl_eq_convexConj_bracket hF u).symm.trans (hFi u)

end RoundTripLeft

section RoundTripEquiv

variable {U X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]
  [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X]
  [TopologicalSpace Y] [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y] [LocallyConvexSpace ℝ Y]
  {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ} [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip]

/-- `K (u, x*) = ⟨Fu, x*⟩` and `Fu = K(u, ·)*` are inverse bijections between the image-closed
convex bifunctions from `U` to `X` and the convex-closed concave-convex functions on `U × Y`. -/
noncomputable def bifunSaddleEquiv :
    {F : Bifun U X // ConvexBifun F ∧ ImageClosedBifun F} ≃
      {K : U × Y → EReal // ConcaveConvexFn K ∧ PartialClosed₂ K} where
  toFun F := ⟨saddleOfBifun Bx F.1,
    concaveConvexFn_saddleOfBifun F.2.1 Bx, partialClosed₂_saddleOfBifun⟩
  invFun K := ⟨bifunOfSaddle Bx K.1,
    convexBifun_bifunOfSaddle K.2.1 Bx, imageClosedBifun_bifunOfSaddle⟩
  left_inv F := Subtype.ext (bifunOfSaddle_saddleOfBifun F.2.1 F.2.2)
  right_inv K := Subtype.ext (saddleOfBifun_bifunOfSaddle K.2.1 K.2.2)

end RoundTripEquiv

/-! ### The bracket of a polyhedral bifunction

For a polyhedral convex bifunction both variables of the bracket sharpen from convex to polyhedral,
and properness does the work that closedness does in the general correspondence: `F` is recovered
from its bracket with no closedness hypothesis at all. "Polyhedral concave" is spelled
`PolyhedralFn (fun u => -(⟨Fu, y⟩))`, there being no predicate for a polyhedral hypograph. -/

section PolyhedralLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → EReal}

/-- **Adding a linear functional preserves polyhedrality.** The epigraph of `f + φ` is the preimage
of `epi f` under the shear `(x, μ) ↦ (x, μ - φ x)`, which needs nothing beyond a real vector space —
no finite dimension, no topology. -/
theorem PolyhedralFn.add_linear (hf : PolyhedralFn f) (φ : E →ₗ[ℝ] ℝ) :
    PolyhedralFn (fun x => f x + ((φ x : ℝ) : EReal)) := by
  have hepi : epi (fun x => f x + ((φ x : ℝ) : EReal))
      = (LinearMap.prod (LinearMap.fst ℝ E ℝ)
          (LinearMap.snd ℝ E ℝ - φ.comp (LinearMap.fst ℝ E ℝ))) ⁻¹' epi f := by
    ext q
    exact EReal.add_coe_le_coe_iff
  change Polyhedral (epi _)
  rw [hepi]
  exact Polyhedral.comap hf _

end PolyhedralLinear

section PolyhedralBracket

variable {U X Y : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] {F : Bifun U X}

omit [FiniteDimensional ℝ U] in
/-- `⟨Fu, ·⟩` is polyhedral convex for each `u`: it is the conjugate of the slice `F u`, which is
itself polyhedral. -/
theorem polyhedralFn_bracket (hF : PolyhedralBifun F) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (u : U) :
    PolyhedralFn (bracket Bx F u) := by
  rw [bracket_eq_convexConj]
  exact PolyhedralFn.convexConj (B := Bx) (PolyhedralBifun.polyhedralFn_apply hF u)

private theorem polyhedralFn_neg_bracket_aux (hF : PolyhedralBifun F)
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (y : Y) (φ : (U × X) →ₗ[ℝ] ℝ)
    (hφ : ∀ p : U × X, φ p = -(Bx p.2 y : ℝ)) :
    PolyhedralFn (fun u => -(bracket Bx F u y)) := by
  have hval : ∀ u : U, (⨅ x : X, (graphFn F (u, x) + ((φ (u, x) : ℝ) : EReal)))
      = -(bracket Bx F u y) := by
    intro u
    rw [bracket_apply, EReal.neg_iSup]
    refine iInf_congr fun x => ?_
    rw [EReal.neg_sub (.inl (EReal.coe_ne_bot _))
        (.inl (EReal.coe_ne_top _)), hφ (u, x), EReal.coe_neg,
      add_comm (graphFn F (u, x))]
    rfl
  have hfun : (fun u => -(bracket Bx F u y))
      = mapLin (LinearMap.fst ℝ U X) (fun p : U × X => graphFn F p + ((φ p : ℝ) : EReal)) := by
    funext u
    rw [mapLin_fst_apply]
    exact (hval u).symm
  rw [hfun]
  exact PolyhedralFn.mapLin (PolyhedralFn.add_linear hF φ) _

/-- `⟨F·, y⟩` is polyhedral *concave* for each `y`. `-⟨Fu, y⟩ = ⨅ x ((Fu)(x) - ⟨x, y⟩)` is the
image of a polyhedral convex function on `U × X` under `(u, x) ↦ u`, and such an image is
polyhedral. -/
theorem polyhedralFn_neg_bracket (hF : PolyhedralBifun F) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (y : Y) :
    PolyhedralFn (fun u => -(bracket Bx F u y)) :=
  polyhedralFn_neg_bracket_aux hF Bx y ((-(Bx.flip y)).comp (LinearMap.snd ℝ U X)) fun _ => rfl

omit [FiniteDimensional ℝ U] in
/-- A *proper* polyhedral convex bifunction is image-closed — each slice has a closed epigraph
and properness keeps it from taking `-∞`. This is the polyhedral substitute for the closedness
hypothesis of the correspondence. -/
theorem imageClosedBifun_of_polyhedralBifun (hF : PolyhedralBifun F)
    (hp : ProperConvex (graphFn F)) :
    ImageClosedBifun F := fun u =>
  PolyhedralFn.closedConvex (PolyhedralBifun.polyhedralFn_apply hF u) fun x => hp.ne_bot (u, x)

omit [FiniteDimensional ℝ U] in
/-- A proper polyhedral convex bifunction is recovered from its bracket, `Fu = ⟨Fu, ·⟩*`. -/
theorem eq_convexConj_bracket_of_polyhedralBifun (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx]
    (hF : PolyhedralBifun F) (hp : ProperConvex (graphFn F)) (u : U) :
    F u = convexConj Bx.flip (bracket Bx F u) :=
  (imageClosedBifun_of_polyhedralBifun hF hp u).symm.trans
    (convexCl_eq_convexConj_bracket (PolyhedralBifun.convexBifun hF) u)

omit [FiniteDimensional ℝ U] in
/-- The same recovery written out: `(Fu)(x) = sup_y {⟨x, y⟩ - ⟨Fu, y⟩}`. -/
theorem eq_iSup_sub_bracket_of_polyhedralBifun (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bx] (hF : PolyhedralBifun F) (hp : ProperConvex (graphFn F)) (u : U)
        (x : X) :
    F u x = ⨆ y : Y, ((Bx x y : ℝ) : EReal) - bracket Bx F u y :=
  congrFun (eq_convexConj_bracket_of_polyhedralBifun Bx hF hp u) x

end PolyhedralBracket

/-! ### The bracket of the adjoint of a polyhedral bifunction

The adjoint of a polyhedral convex bifunction is polyhedral concave and its concave bracket is
polyhedral convex in `y`. With the fact that a polyhedral function agrees with its closure
throughout its effective domain, that pushes the equality of the two brackets out from the relative
interior of an effective domain to all of it. -/

section PolyhedralConcaveClosure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {g : E → EReal}

/-- **A polyhedral concave function agrees with its closure throughout its effective domain**, not
merely on the relative interior. The mirror of `PolyhedralFn.convexCl_eq_of_mem_convexDom`, by
negating twice. -/
theorem concaveCl_eq_of_mem_concaveDom (hg : PolyhedralFn fun z => -(g z)) {x : E}
    (hx : x ∈ concaveDom g) : concaveCl g x = g x := by
  have hmem : x ∈ convexDom fun z => -(g z) := by
    rw [← concaveDom_eq_convexDom_neg]
    exact hx
  rw [concaveCl_apply, PolyhedralFn.convexCl_eq_of_mem_convexDom hg hmem, neg_neg]

end PolyhedralConcaveClosure

section PolyhedralAdjoint

variable {U V X Y : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] {F : Bifun U X}

/-- **A proper polyhedral convex bifunction is closed.** Its graph function has a polyhedral, hence
closed, epigraph, and properness rules out the `-∞` branch of `convexCl`. -/
theorem closedConvexBifun_of_polyhedralBifun (hF : PolyhedralBifun F)
    (hp : ProperConvex (graphFn F)) :
    ClosedConvexBifun F := PolyhedralFn.closedConvex hF hp.ne_bot

/-- **The adjoint of a polyhedral convex bifunction is polyhedral concave.** `-F*` is the conjugate
of the graph function composed with the reflection `(y, v) ↦ (-v, y)`. Neither properness nor
closedness is needed, exactly as in the concavity half of the adjoint construction. -/
theorem polyhedralFn_neg_graphFn_convexAdjointBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (hF : PolyhedralBifun F) :
    PolyhedralFn fun q : Y × V => -(graphFn (convexAdjointBifun Bu Bx F) q) := by
  have h : (fun q : Y × V => -(graphFn (convexAdjointBifun Bu Bx F) q))
      = compLin (convexConj (prodPairing Bu Bx) (graphFn F)) (adjointSwap V Y) := by
    funext q
    rw [graphFn_convexAdjointBifun, neg_neg]
  rw [h]
  exact PolyhedralFn.compLin (PolyhedralFn.convexConj (B := prodPairing Bu Bx) hF) _

end PolyhedralAdjoint

section ConcaveBracketDom

variable {U V Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]

/-- **The effective domain of `y ↦ ⟨u, G y⟩` is `dom G`**, for every `u`: the concave bracket is
`+∞` exactly where the slice `G y` is identically `-∞`. Mirror of `concaveDom_bracket`. -/
theorem convexDom_concaveBracket (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (G : Bifun Y V) (u : U) :
    convexDom (fun y => concaveBracket Bu G u y) = concaveDomBifun G := by
  ext y
  change concaveConj Bu.flip (G y) u < ⊤ ↔ ∃ v, G y v ≠ ⊥
  rw [lt_top_iff_ne_top, ne_eq, concaveConj_eq_top_iff, not_forall]

end ConcaveBracketDom

section PolyhedralConcaveBracket

variable {U V Y : Type*} [AddCommGroup U] [Module ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y] {G : Bifun Y V}

private theorem polyhedralFn_concaveBracket_aux
    (hG : PolyhedralFn fun q : Y × V => -(graphFn G q)) (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (u : U)
    (ψ : (Y × V) →ₗ[ℝ] ℝ) (hψ : ∀ q : Y × V, ψ q = (Bu u q.2 : ℝ)) :
    PolyhedralFn (fun y => concaveBracket Bu G u y) := by
  have hval : ∀ y : Y, (⨅ v : V, (-(graphFn G (y, v)) + ((ψ (y, v) : ℝ) : EReal)))
      = concaveBracket Bu G u y := by
    intro y
    rw [concaveBracket_apply]
    refine iInf_congr fun v => ?_
    rw [hψ (y, v), sub_eq_add_neg, add_comm ((Bu u v : ℝ) : EReal) (-(G y v))]
    rfl
  have hfun : (fun y => concaveBracket Bu G u y)
      = mapLin (LinearMap.fst ℝ Y V)
        (fun q : Y × V => -(graphFn G q) + ((ψ q : ℝ) : EReal)) := by
    funext y
    rw [mapLin_fst_apply]
    exact (hval y).symm
  rw [hfun]
  exact PolyhedralFn.mapLin (PolyhedralFn.add_linear hG ψ) _

/-- **The concave bracket of a polyhedral concave bifunction is polyhedral convex** in its second
variable: `⟨u, G y⟩ = ⨅ v (⟨u, v⟩ - (G y)(v))` is the image of a polyhedral convex function on
`Y × V` under `(y, v) ↦ y`, and such an image is polyhedral. -/
theorem polyhedralFn_concaveBracket (hG : PolyhedralFn fun q : Y × V => -(graphFn G q))
    (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (u : U) : PolyhedralFn (fun y => concaveBracket Bu G u y) :=
  polyhedralFn_concaveBracket_aux hG Bu u ((Bu u).comp (LinearMap.snd ℝ Y V)) fun _ => rfl

end PolyhedralConcaveBracket

/-! ### The two closures as inverse bijections -/

section ClosureBijection

variable {U Y : Type*} [TopologicalSpace U] [TopologicalSpace Y] {K : U × Y → EReal}

theorem upperClosedFn_partialCl₁ (h : LowerClosedFn K) : UpperClosedFn (partialCl₁ K) := by
  change partialCl₁ (partialCl₂ (partialCl₁ K)) = partialCl₁ K
  rw [← lowerCl_def, lowerClosedFn_iff.1 h]

theorem lowerClosedFn_partialCl₂ (h : UpperClosedFn K) : LowerClosedFn (partialCl₂ K) := by
  change partialCl₂ (partialCl₁ (partialCl₂ K)) = partialCl₂ K
  rw [← upperCl_def, upperClosedFn_iff.1 h]

theorem partialCl₂_partialCl₁_of_lowerClosedFn (h : LowerClosedFn K) :
    partialCl₂ (partialCl₁ K) = K := h

theorem partialCl₁_partialCl₂_of_upperClosedFn (h : UpperClosedFn K) :
    partialCl₁ (partialCl₂ K) = K := h

end ClosureBijection

section ClosureEquiv

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  [TopologicalSpace Y] [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y] [LocallyConvexSpace ℝ Y]

/-- `K̄ = cl₁ K̲` and `K̲ = cl₂ K̄` are inverse bijections between the lower closed and the upper
closed concave-convex functions on `U × Y`. The round trips
are the definitions of `LowerClosedFn` and `UpperClosedFn`; the content is that each operator lands
in the other class. -/
noncomputable def lowerUpperClosedEquiv (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu]
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx.flip] :
    {K : U × Y → EReal // ConcaveConvexFn K ∧ LowerClosedFn K} ≃
      {K : U × Y → EReal // ConcaveConvexFn K ∧ UpperClosedFn K} where
  toFun K := ⟨partialCl₁ K.1, concaveConvexFn_partialCl₁ Bu K.2.1,
    upperClosedFn_partialCl₁ K.2.2⟩
  invFun K := ⟨partialCl₂ K.1, concaveConvexFn_partialCl₂ Bx K.2.1,
    lowerClosedFn_partialCl₂ K.2.2⟩
  left_inv K := Subtype.ext (partialCl₂_partialCl₁_of_lowerClosedFn K.2.2)
  right_inv K := Subtype.ext (partialCl₁_partialCl₂_of_upperClosedFn K.2.2)

end ClosureEquiv

end ConvexAnalysis

