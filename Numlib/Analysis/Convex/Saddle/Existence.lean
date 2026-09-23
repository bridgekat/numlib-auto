import Numlib.Analysis.Convex.Saddle.Subdifferential
import Numlib.Analysis.Convex.Subdifferential.Monotone

/-!
# Existence of saddle-values and saddle-points

This module turns the effective domains of the conjugates (`Saddle/Conjugate.lean`) into criteria
for a saddle-value and a saddle-point in terms of `K` alone, each in a second-variable and a
first-variable form, and then specialises everything to a finite continuous concave-convex
function on a product of closed convex sets — where the result is the classical **minimax
theorem**.

The device is the involution `saddleSwap K (y, u) = -K (u, y)`. Under it the class `Ω (F)` becomes
the class `Ω (F♯)` for the **negated flipped pairings** `-Bx.flip`, `-Bu.flip`, where `F♯` is the
bifunction `(F♯ y) v = -(F* y)(v)`, and the two conjugates are exchanged. So every first-variable
(`C*`) statement is its second-variable (`D*`) companion read at the swapped data, and no new
duality is needed. The pairings must be
negated and not merely flipped: `saddleSwap` negates values, and only the negated pairings restore
the sign of the linear terms in the two conjugates.

The file closes with the identification of `∂K` with the subdifferential of the graph function of
`F`, partially inverted along a linear homeomorphism.

## Main results

* `swapAdjointBifun`, `convexAdjointBifun_swapAdjointBifun`, `saddleSwap_mem_bifunSaddleClass` — the
  swap dictionary: `saddleSwap` carries `Ω (F)` onto `Ω (F♯)`, and the adjoint of `F♯` is `-F`; the
  two conjugates are exchanged by `upperConjSaddle_saddleSwap`, `lowerConjSaddle_saddleSwap`
  (`Saddle/Minimax.lean`).
* `properConvex_graphFn_of_properSaddleFn` — a proper member of `Ω (F)` forces
  `ProperConvex (graphFn F)`.
* `zero_mem_interior_dom₂_upperConjSaddle_iff`, `zero_mem_interior_dom₁_upperConjSaddle_iff` —
  `0 ∈ int D*` and `0 ∈ int C*` in terms of directions of recession
  ([rockafellar1970convex] Corollary 37.2.1);
  `hasSaddleValue_of_no_common_direction_of_recession_snd`, `…_fst` — no common direction of
  recession in one variable gives a saddle-value ([rockafellar1970convex] Theorem 37.3);
  `hasSaddleValue_of_isBounded_dom₂`, `hasSaddleValue_of_isBounded_dom₁` — likewise when `D` or
  `C` is bounded.
* `exists_isSaddlePoint_of_no_common_direction_of_recession` — a saddle-point exists when neither
  variable has a common direction of recession ([rockafellar1970convex] Theorem 37.6);
  `exists_isSaddlePoint_of_isBounded_domSaddle` — likewise for a bounded effective domain.
* `saddleStructure_lowerSimpleExt`, `maximin_lowerSimpleExt`,
  `exists_bifunSaddleClass_lowerSimpleExt` — the transfer to a finite continuous concave-convex
  function on a closed `C × D`, through its lower simple extension.
* `biSup_biInf_eq_biInf_biSup_of_isBounded_right`, `…_left` — `sup inf = inf sup` with one factor
  bounded;
  `exists_saddlePoint_of_isBounded` — the **minimax theorem**
  ([rockafellar1970convex] Corollary 37.6.2).
* `isBifunSubgradientPair_iff_mem_subdifferential_graphFn`,
  `setOf_mem_saddleSubdifferential_eq_preimage` — `∂K` is `∂f` partially inverted, pointwise and as
  an equality of graphs; `isClosed_setOf_mem_saddleSubdifferential` — the graph of `∂K` is closed.

## Implementation notes

The `sup inf = inf sup` statements carry `EReal`-valued extrema. The customary display is
`inf_D sup_C K = sup_C inf_D K` for a finite `K`, but with only one of `C`, `D` bounded the two
iterated extrema can be `±∞`. The minimax theorem, where both are bounded, is stated with real
inequalities.

## References

* [rockafellar1970convex] §24, §34, §36, §37.
-/

namespace ConvexAnalysis

/-! ### `saddleSwap` and the conjugate saddle-functions -/

section SwapNeg

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]

/-- **The adjoint commutes with `flipBifun` once both pairings are negated and exchanged.** This is
the identity behind the whole swap dictionary: `convexAdjointBifun` is an infimum over `U × X` of
`F u x + ⟨u, v⟩ - ⟨x, y⟩`, and negating and exchanging the pairings restores that summand with the
two bound variables exchanged. -/
theorem convexAdjointBifun_neg_flipBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (F : Bifun U X) :
    convexAdjointBifun (-Bx) (-Bu) (flipBifun F) = flipBifun (convexAdjointBifun Bu Bx F) := by
  funext v y
  rw [flipBifun_apply, convexAdjointBifun_apply, convexAdjointBifun_apply, iInf_prod, iInf_prod,
      iInf_comm]
  refine iInf_congr fun u => iInf_congr fun x => ?_
  rw [flipBifun_apply]
  congr 2
  simp only [LinearMap.neg_apply]
  ring

omit [AddCommGroup Y] [Module ℝ Y] in
/-- The bracket of `y ↦ -(G y ·)` at the negated flipped pairing is minus the concave bracket
of `G`. This is one of the two halves of the swap dictionary for equivalence classes. -/
theorem bracket_neg_flip_flipBifun_inverseBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (G : Bifun Y V)
    (y : Y) (u : U) :
    bracket (-Bu.flip) (flipBifun (inverseBifun G)) y u = -(concaveBracket Bu G u y) := by
  rw [bracket_apply, concaveBracket_apply, EReal.neg_iInf]
  refine iSup_congr fun v => ?_
  rw [flipBifun_apply, inverseBifun_apply, EReal.neg_coe_sub]
  have hr : ((-Bu.flip) v u : ℝ) = -(Bu u v) := by
    simp only [LinearMap.neg_apply, LinearMap.flip_apply]
  rw [hr, coe_neg_sub_neg]

omit [AddCommGroup U] [Module ℝ U] in
/-- The mirror half: the concave bracket of `u ↦ -(H u ·)` at the negated flipped pairing is
minus the bracket of `H`. -/
theorem concaveBracket_neg_flip_flipBifun_inverseBifun (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (H : Bifun U X)
    (y : Y) (u : U) :
    concaveBracket (-Bx.flip) (flipBifun (inverseBifun H)) y u = -(bracket Bx H u y) := by
  rw [concaveBracket_apply, bracket_apply, EReal.neg_iSup]
  refine iInf_congr fun x => ?_
  rw [flipBifun_apply, inverseBifun_apply, EReal.neg_coe_sub]
  have hr : ((-Bx.flip) y x : ℝ) = -(Bx x y) := by
    simp only [LinearMap.neg_apply, LinearMap.flip_apply]
  rw [hr, coe_neg_sub_neg]

end SwapNeg

/-! ### The class conjugate to `Ω (F)` seen through `saddleSwap` -/

section SwapClass

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]

/-- The convex bifunction attached to the **swapped** saddle-function: `(F♯ y) v = -(F* y)(v)`.

It is not `F_*^*`, which goes from `V` to `Y` and belongs to the *conjugate* class on `V × X`;
`F♯` goes from `Y` to `V`, and the two differ by `flipBifun`. Its two brackets at the negated
flipped pairings are the negatives of the two brackets of `F`, exchanged — which is what
`saddleSwap` does to the class `Ω (F)`. -/
noncomputable def swapAdjointBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (F : Bifun U X) : Bifun Y V :=
  flipBifun (lowerAdjointBifun Bu Bx F)

@[simp] theorem swapAdjointBifun_apply (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (F : Bifun U X) (y : Y) (v : V) :
    swapAdjointBifun Bu Bx F y v = -(convexAdjointBifun Bu Bx F y v) := rfl

/-- `F♯` is a convex bifunction: it is `F_*^*` with its two arguments exchanged. -/
theorem convexBifun_swapAdjointBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (F : Bifun U X) : ConvexBifun (swapAdjointBifun Bu Bx F) :=
  convexBifun_flipBifun (convexBifun_lowerAdjointBifun Bu Bx F)

end SwapClass

section SwapClassClosed

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace V] [IsTopologicalAddGroup V] [TopologicalSpace Y] [IsTopologicalAddGroup Y]

/-- `F♯` is a closed bifunction, because an adjoint bifunction is closed. -/
theorem closedConvexBifun_swapAdjointBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsContinuousPairing Bu.flip]
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsContinuousPairing Bx.flip] (F : Bifun U X) :
    ClosedConvexBifun (swapAdjointBifun Bu Bx F) :=
  haveI := isContinuousPairing_prodPairing_flip Bu Bx
  closedConvexBifun_flipBifun closedConvexBifun_lowerAdjointBifun

end SwapClassClosed

section SwapClassMem

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X]
  {F : Bifun U X} {K : U × Y → EReal}

/-- **The adjoint of `F♯` is `-F`**, which is the biadjoint identity `(F_*^*)^* = F_*` read
through `convexAdjointBifun_neg_flipBifun`. -/
theorem convexAdjointBifun_swapAdjointBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu]
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx] (hF : ConvexBifun F)
    (hcl : ClosedConvexBifun F) :
    convexAdjointBifun (-Bx.flip) (-Bu.flip) (swapAdjointBifun Bu Bx F)
        = flipBifun (inverseBifun F) := by
  rw [swapAdjointBifun, convexAdjointBifun_neg_flipBifun Bu.flip Bx.flip,
    convexAdjointBifun_flip_lowerAdjointBifun (Bu := Bu) (Bx := Bx) hF hcl]

/-- **The swap dictionary for equivalence classes**: `saddleSwap` carries `Ω (F)` onto `Ω (F♯)`
at the negated flipped pairings. Every statement about the first variable is therefore the
corresponding statement about the second variable, read here. -/
theorem saddleSwap_mem_bifunSaddleClass (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu]
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx] (hF : ConvexBifun F)
        (hcl : ClosedConvexBifun F)
    (hK : K ∈ bifunSaddleClass Bu Bx F) :
    saddleSwap K ∈ bifunSaddleClass (-Bx.flip) (-Bu.flip) (swapAdjointBifun Bu Bx F) := by
  have h1 : (fun p : Y × U => bracket (-Bu.flip) (swapAdjointBifun Bu Bx F) p.1 p.2)
      = saddleSwap fun p : U × Y => concaveBracket Bu (convexAdjointBifun Bu Bx F) p.1 p.2 := by
    funext p
    rw [swapAdjointBifun, lowerAdjointBifun_eq_inverseBifun_convexAdjointBifun,
      bracket_neg_flip_flipBifun_inverseBifun, saddleSwap_apply]
  have h2 : (fun p : Y × U => concaveBracket (-Bx.flip)
        (convexAdjointBifun (-Bx.flip) (-Bu.flip) (swapAdjointBifun Bu Bx F)) p.1 p.2)
      = saddleSwap fun p : U × Y => bracket Bx F p.1 p.2 := by
    funext p
    rw [convexAdjointBifun_swapAdjointBifun Bu Bx hF hcl,
      concaveBracket_neg_flip_flipBifun_inverseBifun, saddleSwap_apply]
  rw [mem_bifunSaddleClass] at hK
  rw [mem_bifunSaddleClass, h1, h2]
  exact ⟨saddleSwap_le_saddleSwap hK.2, saddleSwap_le_saddleSwap hK.1⟩

end SwapClassMem

/-! ### Properness of the bifunction behind a proper class -/

section ProperGraph

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  {F : Bifun U X} {K : U × Y → EReal}

/-- **A proper member forces a proper bifunction.** The two propernesses are usually not
separated, but the results here ask for `ProperConvex (graphFn F)` while the structural theorems
deliver `ProperSaddleFn K`, so the bridge is crossed explicitly.

`F u x = ⊥` would make the bracket `⟨Fu, y⟩` identically `+∞`, contradicting `dom₂ K ≠ ∅`; and
`F ≡ +∞` would make the upper bracket `-∞`, contradicting `dom₁ K ≠ ∅`. -/
theorem properConvex_graphFn_of_properSaddleFn (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (hK : K ∈ bifunSaddleClass Bu Bx F) (hp : ProperSaddleFn K) : ProperConvex (graphFn F) := by
  obtain ⟨u₀, hu₀⟩ := hp.dom₁_nonempty
  obtain ⟨y₀, hy₀⟩ := hp.dom₂_nonempty
  rw [mem_bifunSaddleClass] at hK
  have hbot : ∀ q : U × X, graphFn F q ≠ ⊥ := by
    rintro ⟨u, x⟩ hq
    have hle : ((Bx x y₀ : ℝ) : EReal) - F u x ≤ bracket Bx F u y₀ :=
      le_iSup (fun x => ((Bx x y₀ : ℝ) : EReal) - F u x) x
    have htop : ((Bx x y₀ : ℝ) : EReal) - F u x = ⊤ := by
      rw [show F u x = (⊥ : EReal) from hq]
      simp
    rw [htop] at hle
    exact absurd (top_le_iff.1 (hle.trans (hK.1 (u, y₀)))) (ne_of_lt (hy₀ u))
  refine ⟨?_, hbot⟩
  have hlt : ⊥ < concaveBracket Bu (convexAdjointBifun Bu Bx F) u₀ y₀ := lt_of_lt_of_le (hu₀ y₀)
    (hK.2 (u₀, y₀))
  have hterm : (⊥ : EReal) < ((Bu u₀ 0 : ℝ) : EReal) - convexAdjointBifun Bu Bx F y₀ 0 := by
    refine lt_of_lt_of_le hlt ?_
    rw [concaveBracket_apply]
    exact iInf_le (fun v => ((Bu u₀ v : ℝ) : EReal) - convexAdjointBifun Bu Bx F y₀ v) 0
  have hne : convexAdjointBifun Bu Bx F y₀ 0 ≠ ⊤ := by
    intro hcon
    rw [hcon] at hterm
    simp at hterm
  obtain ⟨q, hq⟩ := iInf_lt_iff.1 (lt_of_le_of_ne le_top hne)
  refine ⟨q, ?_⟩
  by_contra hcon
  rw [mem_convexDom, not_lt, top_le_iff] at hcon
  rw [show F q.1 q.2 = (⊤ : EReal) from hcon] at hq
  simp at hq

end ProperGraph

/-! ### Negated flipped pairings -/

section SeparatingNeg

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

/-- Negating and flipping a pairing exchanges its two separation properties. -/
theorem separatingRight_neg_flip {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} (hB : B.SeparatingLeft) :
    (-B.flip).SeparatingRight := by
  intro x hx
  refine hB x fun y => ?_
  have h := hx y
  simpa using h

end SeparatingNeg

/-! ### The saddle-value criteria

Each criterion comes in a second-variable form, about `D*` and the slices `K (u, ·)`, and a
first-variable form, about `C*` and the slices `-K (·, y)`. The `D*` form is proved from the
support function of `D*` (`Saddle/Conjugate.lean`); the `C*` form is the `D*` form read at
`saddleSwap K`, whose class is `Ω (F♯)` for the negated flipped pairings. -/

section SaddleValue

variable {U V X Y : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
  {F : Bifun U X} {K : U × Y → EReal}

omit [FiniteDimensional ℝ V] in
/-- **The origin is an interior point of `D*`** if and only if the convex functions `K (u, ·)`, for
`u ∈ ri C`, have no common direction of recession.

`0 ∈ int D*` iff `δ*(w | D*) > 0` for every `w ≠ 0`, and `δ*(w | D*)` is the supremum of the
`(K (u, ·))∞ (w)`. `Bx.SeparatingRight` is what makes `w ≠ 0` and `⟨·, w⟩ ≠ 0` the same
condition; where a space is paired with itself it is automatic. -/
theorem zero_mem_interior_dom₂_upperConjSaddle_iff (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip] (hB : Bx.SeparatingRight)
    (hF : ConvexBifun F) (hcl : ClosedConvexBifun F) (hK : K ∈ bifunSaddleClass Bu Bx F)
    (hKcc : ConcaveConvexFn K) (hp : ProperSaddleFn K) (hs : SaddleStructure K) :
    (0 : X) ∈ interior (dom₂ (upperConjSaddle Bu Bx K)) ↔
      ∀ w : Y, w ≠ 0 → ∃ u ∈ ri (dom₁ K), 0 < recessionFn (fun y => K (u, y)) w := by
  have hconv : Convex ℝ (dom₂ (upperConjSaddle Bu Bx K)) :=
    (concaveConvexFn_upperConjSaddle Bu Bx hF hcl hK).convex_dom₂
  have hnex : (dom₂ (upperConjSaddle Bu Bx K)).Nonempty :=
    (properSaddleFn_upperConjSaddle Bu Bx hF
        hcl (properConvex_graphFn_of_properSaddleFn Bu Bx hK hp)
      hK).dom₂_nonempty
  rw [mem_interior_iff_lt_supportFn (B := Bx) hconv hnex hB 0]
  refine forall_congr' fun w => imp_congr_right fun _ => ?_
  rw [map_zero, LinearMap.zero_apply, EReal.coe_zero,
    supportFn_dom₂_upperConjSaddle_eq_iSup_recessionFn Bu Bx hF hcl hK hKcc hp.dom₂_nonempty hs.1
      w]
  simp only [lt_iSup_iff, exists_prop]

/-- **The origin is an interior point of `C*`** if and only if the convex functions `-K (·, y)`,
for `y ∈ ri D`, have no common direction of recession. This is the `D*` criterion read at
`saddleSwap K`. -/
theorem zero_mem_interior_dom₁_upperConjSaddle_iff (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip] (hB : Bu.SeparatingLeft)
    (hF : ConvexBifun F) (hcl : ClosedConvexBifun F) (hK : K ∈ bifunSaddleClass Bu Bx F)
    (hKcc : ConcaveConvexFn K) (hp : ProperSaddleFn K) (hs : SaddleStructure K) :
    (0 : V) ∈ interior (dom₁ (upperConjSaddle Bu Bx K)) ↔
      ∀ z : U, z ≠ 0 → ∃ y ∈ ri (dom₂ K), 0 < recessionFn (fun u => -(K (u, y))) z := by
  have hmain := zero_mem_interior_dom₂_upperConjSaddle_iff (-Bx.flip) (-Bu.flip)
    (separatingRight_neg_flip hB) (convexBifun_swapAdjointBifun Bu Bx F)
    (closedConvexBifun_swapAdjointBifun Bu Bx F) (saddleSwap_mem_bifunSaddleClass Bu Bx hF hcl hK)
    hKcc.saddleSwap hp.saddleSwap hs.saddleSwap
  rw [upperConjSaddle_saddleSwap, dom₂_saddleSwap, dom₁_saddleSwap,
    dom₁_conjSaddle_eq Bu Bx hF hcl (properConvex_graphFn_of_properSaddleFn Bu Bx hK hp) hK]
        at hmain
  exact hmain

/-- If the convex functions `K (u, ·)` for `u ∈ ri C` have no common direction of recession, then
the saddle-value of `K` exists: the hypothesis is `0 ∈ int D*`, and the origin in `ri D*` gives
the saddle-value. -/
theorem hasSaddleValue_of_no_common_direction_of_recession_snd (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip] (hB : Bx.SeparatingRight)
    (hF : ConvexBifun F) (hcl : ClosedConvexBifun F) (hK : K ∈ bifunSaddleClass Bu Bx F)
    (hKcc : ConcaveConvexFn K) (hp : ProperSaddleFn K) (hs : SaddleStructure K)
    (hrec : ∀ w : Y, w ≠ 0 → ∃ u ∈ ri (dom₁ K), 0 < recessionFn (fun y => K (u, y)) w) :
    HasSaddleValue K := by
  have hpr := properConvex_graphFn_of_properSaddleFn Bu Bx hK hp
  refine hasSaddleValue_of_mem_relint_dom₂_lowerConjSaddle Bu Bx hF hcl hpr hK ?_
  rw [dom₂_conjSaddle_eq Bu Bx hF hcl hpr hK]
  exact interior_subset_intrinsicInterior
    ((zero_mem_interior_dom₂_upperConjSaddle_iff Bu Bx hB hF hcl hK hKcc hp hs).2 hrec)

/-- If the convex functions `-K (·, y)` for `y ∈ ri D` have no common direction of recession, then
the saddle-value of `K` exists: the hypothesis is `0 ∈ int C*`. -/
theorem hasSaddleValue_of_no_common_direction_of_recession_fst (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip] (hB : Bu.SeparatingLeft)
    (hF : ConvexBifun F) (hcl : ClosedConvexBifun F) (hK : K ∈ bifunSaddleClass Bu Bx F)
    (hKcc : ConcaveConvexFn K) (hp : ProperSaddleFn K) (hs : SaddleStructure K)
    (hrec : ∀ z : U, z ≠ 0 → ∃ y ∈ ri (dom₂ K), 0 < recessionFn (fun u => -(K (u, y))) z) :
    HasSaddleValue K := by
  have hpr := properConvex_graphFn_of_properSaddleFn Bu Bx hK hp
  refine hasSaddleValue_of_mem_relint_dom₁_lowerConjSaddle Bu Bx hF hcl hpr hK ?_
  rw [dom₁_conjSaddle_eq Bu Bx hF hcl hpr hK]
  exact interior_subset_intrinsicInterior
    ((zero_mem_interior_dom₁_upperConjSaddle_iff Bu Bx hB hF hcl hK hKcc hp hs).2 hrec)

omit [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [NormedAddCommGroup X]
  [NormedSpace ℝ X] [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y] in
/-- **A bounded `D` leaves the slices `K (u, ·)` no common direction of recession**: for
`u ∈ ri C` the effective domain of `K (u, ·)` is exactly `D`. -/
theorem exists_mem_relint_lt_recessionFn_of_isBounded_dom₂ (hKcc : ConcaveConvexFn K)
    (hp : ProperSaddleFn K) (hs : SaddleStructure K) (hbd : Bornology.IsBounded (dom₂ K))
    {w : Y} (hw : w ≠ 0) : ∃ u ∈ ri (dom₁ K), 0 < recessionFn (fun y => K (u, y)) w := by
  obtain ⟨u, hu⟩ := Convex.relint_nonempty hKcc.convex_dom₁ hp.dom₁_nonempty
  have hdom : convexDom (fun y => K (u, y)) = dom₂ K := hs.1.convexDom_slice u hu
  exact ⟨u, hu, lt_recessionFn_of_isBounded_convexDom (by rw [hdom]; exact hp.dom₂_nonempty)
    (by rw [hdom]; exact hbd) hw⟩

omit [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [NormedAddCommGroup X]
  [NormedSpace ℝ X] [FiniteDimensional ℝ X] [FiniteDimensional ℝ U] in
/-- **A bounded `C` leaves the slices `-K (·, y)` no common direction of recession**: the
second-variable statement read at `saddleSwap K`. -/
theorem exists_mem_relint_lt_recessionFn_of_isBounded_dom₁ (hKcc : ConcaveConvexFn K)
    (hp : ProperSaddleFn K) (hs : SaddleStructure K) (hbd : Bornology.IsBounded (dom₁ K))
    {z : U} (hz : z ≠ 0) : ∃ y ∈ ri (dom₂ K), 0 < recessionFn (fun u => -(K (u, y))) z := by
  have h := exists_mem_relint_lt_recessionFn_of_isBounded_dom₂ hKcc.saddleSwap hp.saddleSwap
    hs.saddleSwap (by rwa [dom₂_saddleSwap]) hz
  rw [dom₁_saddleSwap] at h
  exact h

/-- **If the second effective domain of `K` is bounded, the saddle-value of `K` exists.** Over a
compact `D` this is the classical minimax theorem. -/
theorem hasSaddleValue_of_isBounded_dom₂ (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu]
    [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx]
    [IsCompatiblePairing Bx.flip] (hB : Bx.SeparatingRight) (hF : ConvexBifun F)
    (hcl : ClosedConvexBifun F) (hK : K ∈ bifunSaddleClass Bu Bx F) (hKcc : ConcaveConvexFn K)
    (hp : ProperSaddleFn K) (hs : SaddleStructure K)
    (hbd : Bornology.IsBounded (dom₂ K)) : HasSaddleValue K :=
  hasSaddleValue_of_no_common_direction_of_recession_snd Bu Bx hB hF hcl hK hKcc hp hs
    fun _ hw => exists_mem_relint_lt_recessionFn_of_isBounded_dom₂ hKcc hp hs hbd hw

/-- If the first effective domain of `K` is bounded, the saddle-value of `K` exists. -/
theorem hasSaddleValue_of_isBounded_dom₁ (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu]
    [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx]
    [IsCompatiblePairing Bx.flip] (hB : Bu.SeparatingLeft) (hF : ConvexBifun F)
    (hcl : ClosedConvexBifun F) (hK : K ∈ bifunSaddleClass Bu Bx F) (hKcc : ConcaveConvexFn K)
    (hp : ProperSaddleFn K) (hs : SaddleStructure K)
    (hbd : Bornology.IsBounded (dom₁ K)) : HasSaddleValue K :=
  hasSaddleValue_of_no_common_direction_of_recession_fst Bu Bx hB hF hcl hK hKcc hp hs
    fun _ hz => exists_mem_relint_lt_recessionFn_of_isBounded_dom₁ hKcc hp hs hbd hz

end SaddleValue

/-! ### Existence of a saddle-point -/

section SaddlePoint

variable {U V X Y : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
  {F : Bifun U X} {K : U × Y → EReal}

/-- If neither variable has a common direction of recession, `K` has a saddle-point. The two
recession conditions translate into `0 ∈ int C*` and `0 ∈ int D*`, and `∂K* (0, 0)` is then a
nonempty set of saddle-points. -/
theorem exists_isSaddlePoint_of_no_common_direction_of_recession (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip] (hBu : Bu.SeparatingLeft)
    (hBx : Bx.SeparatingRight) (hF : ConvexBifun F) (hcl : ClosedConvexBifun F)
    (hK : K ∈ bifunSaddleClass Bu Bx F) (hKcc : ConcaveConvexFn K) (hp : ProperSaddleFn K)
    (hs : SaddleStructure K)
    (hrec₂ : ∀ w : Y, w ≠ 0 → ∃ u ∈ ri (dom₁ K), 0 < recessionFn (fun y => K (u, y)) w)
    (hrec₁ : ∀ z : U, z ≠ 0 → ∃ y ∈ ri (dom₂ K), 0 < recessionFn (fun u => -(K (u, y))) z) :
    ∃ q, IsSaddlePoint K q := by
  exact exists_isSaddlePoint_of_zero_mem_interior_dom_upperConjSaddle Bu Bx hF hcl
    (properConvex_graphFn_of_properSaddleFn Bu Bx hK hp) hK
    ((zero_mem_interior_dom₁_upperConjSaddle_iff Bu Bx hBu hF hcl hK hKcc hp hs).2 hrec₁)
    ((zero_mem_interior_dom₂_upperConjSaddle_iff Bu Bx hBx hF hcl hK hKcc hp hs).2 hrec₂)

/-- If both halves of the effective domain of `K` are bounded, `K` has a saddle-point. -/
theorem exists_isSaddlePoint_of_isBounded_domSaddle (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip] (hBu : Bu.SeparatingLeft)
    (hBx : Bx.SeparatingRight) (hF : ConvexBifun F) (hcl : ClosedConvexBifun F)
    (hK : K ∈ bifunSaddleClass Bu Bx F) (hKcc : ConcaveConvexFn K) (hp : ProperSaddleFn K)
    (hs : SaddleStructure K) (hbd₁ : Bornology.IsBounded (dom₁ K))
    (hbd₂ : Bornology.IsBounded (dom₂ K)) : ∃ q, IsSaddlePoint K q := by
  exact exists_isSaddlePoint_of_no_common_direction_of_recession Bu Bx hBu hBx hF hcl hK hKcc
    hp hs (fun _ hw => exists_mem_relint_lt_recessionFn_of_isBounded_dom₂ hKcc hp hs hbd₂ hw)
    fun _ hz => exists_mem_relint_lt_recessionFn_of_isBounded_dom₁ hKcc hp hs hbd₁ hz

/-- The saddle-value is then finite — it is a value of `K` at a saddle-point, and a proper
saddle-function is finite on its effective domain. -/
theorem exists_maximin_eq_coe_of_isBounded_domSaddle (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip] (hBu : Bu.SeparatingLeft)
    (hBx : Bx.SeparatingRight) (hF : ConvexBifun F) (hcl : ClosedConvexBifun F)
    (hK : K ∈ bifunSaddleClass Bu Bx F) (hKcc : ConcaveConvexFn K) (hp : ProperSaddleFn K)
    (hs : SaddleStructure K) (hbd₁ : Bornology.IsBounded (dom₁ K))
    (hbd₂ : Bornology.IsBounded (dom₂ K)) : ∃ r : ℝ, maximin K = (r : EReal) := by
  obtain ⟨q, hq⟩ := exists_isSaddlePoint_of_isBounded_domSaddle Bu Bx hBu hBx hF hcl hK hKcc hp
    hs hbd₁ hbd₂
  exact hq.exists_maximin_eq_coe hp

end SaddlePoint

/-! ### A finite continuous saddle-function on `C × D` -/

section SimpleExt

variable {U V X Y : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
  {C : Set U} {D : Set Y} {K : U × Y → ℝ}

omit [FiniteDimensional ℝ V] [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] in
/-- The lower simple extension is a closed proper concave-convex function, so it has the full
structural description. -/
theorem saddleStructure_lowerSimpleExt (hC : Convex ℝ C) (hCcl : IsClosed C) (hDcl : IsClosed D)
    (hCne : C.Nonempty) (hDne : D.Nonempty)
    (hconv : ∀ u ∈ C, ConvexOn ℝ D fun x => K (u, x))
    (hconc : ∀ x ∈ D, ConcaveOn ℝ C fun u => K (u, x))
    (hcontD : ∀ u ∈ C, ContinuousOn (fun x => K (u, x)) D)
    (hcontC : ∀ x ∈ D, ContinuousOn (fun u => K (u, x)) C) :
    SaddleStructure (lowerSimpleExt C D K) :=
  (closedSaddleFn_iff_saddleStructure (concaveConvexFn_lowerSimpleExt hC hconv hconc)
      (properSaddleFn_lowerSimpleExt hCne hDne)).1
    (closedSaddleFn_of_mem_saddleClass_simpleExt hCcl hDcl hCne hDne hcontD hcontC
      (mem_saddleClass_left (partialCl₂_upperSimpleExt hDcl hDne hcontD)))

omit [FiniteDimensional ℝ V] [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] in
/-- The `sup inf` of the lower simple extension over the whole space is the `sup inf` of `K` over
`C × D`. -/
theorem maximin_lowerSimpleExt (hC : Convex ℝ C) (hCcl : IsClosed C) (hDcl : IsClosed D)
    (hCne : C.Nonempty) (hDne : D.Nonempty)
    (hconv : ∀ u ∈ C, ConvexOn ℝ D fun x => K (u, x))
    (hconc : ∀ x ∈ D, ConcaveOn ℝ C fun u => K (u, x))
    (hcontD : ∀ u ∈ C, ContinuousOn (fun x => K (u, x)) D)
    (hcontC : ∀ x ∈ D, ContinuousOn (fun u => K (u, x)) C) :
    maximin (lowerSimpleExt C D K) = ⨆ u ∈ C, ⨅ x ∈ D, ((K (u, x) : ℝ) : EReal) := by
  rw [maximin_eq_biSup_biInf (concaveConvexFn_lowerSimpleExt hC hconv hconc)
      (saddleStructure_lowerSimpleExt hC hCcl hDcl hCne hDne hconv hconc hcontD hcontC)
      (properSaddleFn_lowerSimpleExt hCne hDne),
    dom₁_lowerSimpleExt (K := K) hDne, dom₂_lowerSimpleExt (K := K) hCne]
  exact iSup_congr fun u => iSup_congr fun hu => iInf_congr fun x => iInf_congr fun hx =>
    lowerSimpleExt_of_mem (p := (u, x)) hu hx

omit [FiniteDimensional ℝ V] [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] in
/-- The `inf sup` of the lower simple extension over the whole space is the `inf sup` of `K` over
`C × D`. -/
theorem minimax_lowerSimpleExt (hC : Convex ℝ C) (hCcl : IsClosed C) (hDcl : IsClosed D)
    (hCne : C.Nonempty) (hDne : D.Nonempty)
    (hconv : ∀ u ∈ C, ConvexOn ℝ D fun x => K (u, x))
    (hconc : ∀ x ∈ D, ConcaveOn ℝ C fun u => K (u, x))
    (hcontD : ∀ u ∈ C, ContinuousOn (fun x => K (u, x)) D)
    (hcontC : ∀ x ∈ D, ContinuousOn (fun u => K (u, x)) C) :
    minimax (lowerSimpleExt C D K) = ⨅ x ∈ D, ⨆ u ∈ C, ((K (u, x) : ℝ) : EReal) := by
  rw [minimax_eq_biInf_biSup (concaveConvexFn_lowerSimpleExt hC hconv hconc)
      (saddleStructure_lowerSimpleExt hC hCcl hDcl hCne hDne hconv hconc hcontD hcontC)
      (properSaddleFn_lowerSimpleExt hCne hDne),
    dom₁_lowerSimpleExt (K := K) hDne, dom₂_lowerSimpleExt (K := K) hCne]
  exact iInf_congr fun x => iInf_congr fun hx => iSup_congr fun u => iSup_congr fun hu =>
    lowerSimpleExt_of_mem (p := (u, x)) hu hx

omit [FiniteDimensional ℝ U] [FiniteDimensional ℝ V] [FiniteDimensional ℝ X]
  [FiniteDimensional ℝ Y] in
/-- The unique closed convex bifunction whose lower bracket is the lower simple extension, packaged
with the membership `K₁ ∈ Ω (F)` that the results above consume. -/
theorem exists_bifunSaddleClass_lowerSimpleExt (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu]
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip]
    (hC : Convex ℝ C) (hCcl : IsClosed C) (hDcl : IsClosed D) (hCne : C.Nonempty)
    (hDne : D.Nonempty) (hconv : ∀ u ∈ C, ConvexOn ℝ D fun x => K (u, x))
    (hconc : ∀ x ∈ D, ConcaveOn ℝ C fun u => K (u, x))
    (hcontD : ∀ u ∈ C, ContinuousOn (fun x => K (u, x)) D)
    (hcontC : ∀ x ∈ D, ContinuousOn (fun u => K (u, x)) C) :
    ∃ F : Bifun U X, ConvexBifun F ∧ ClosedConvexBifun F ∧
      lowerSimpleExt C D K ∈ bifunSaddleClass Bu Bx F := by
  obtain ⟨F, ⟨hFconv, hFcl, hbr1, hbr2⟩, -⟩ := exists_unique_bifun_of_simpleExt Bu Bx hC hCcl
    hDcl hCne hconv hconc hDne hcontD hcontC
  refine ⟨F, hFconv, hFcl, ?_⟩
  rw [bifunSaddleClass, hbr1, hbr2]
  exact mem_saddleClass_left (partialCl₂_upperSimpleExt hDcl hDne hcontD)

end SimpleExt

section Minimax

variable {U V X Y : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
  {C : Set U} {D : Set Y} {K : U × Y → ℝ}

omit [FiniteDimensional ℝ V] [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] in
/-- The common last step of the two bounded halves: once the lower simple extension has a
saddle-value, `sup inf = inf sup` over `C × D`, because its extrema over the whole space are the
restricted ones. -/
theorem biSup_biInf_eq_biInf_biSup_of_hasSaddleValue_lowerSimpleExt (hC : Convex ℝ C)
    (hCcl : IsClosed C) (hDcl : IsClosed D) (hCne : C.Nonempty) (hDne : D.Nonempty)
    (hconv : ∀ u ∈ C, ConvexOn ℝ D fun x => K (u, x))
    (hconc : ∀ x ∈ D, ConcaveOn ℝ C fun u => K (u, x))
    (hcontD : ∀ u ∈ C, ContinuousOn (fun x => K (u, x)) D)
    (hcontC : ∀ x ∈ D, ContinuousOn (fun u => K (u, x)) C)
    (hsv : HasSaddleValue (lowerSimpleExt C D K)) :
    (⨆ u ∈ C, ⨅ x ∈ D, ((K (u, x) : ℝ) : EReal))
      = ⨅ x ∈ D, ⨆ u ∈ C, ((K (u, x) : ℝ) : EReal) := by
  rwa [hasSaddleValue_iff, maximin_lowerSimpleExt hC hCcl hDcl hCne hDne hconv hconc hcontD hcontC,
    minimax_lowerSimpleExt hC hCcl hDcl hCne hDne hconv hconc hcontD hcontC] at hsv

/-- The half where `D` is bounded: a finite continuous concave-convex function on a product of
nonempty closed convex sets, one of them bounded, has `sup inf = inf sup` over `C × D`. The lower
simple extension is a closed proper concave-convex function with effective domain `C × D`, so it
has a saddle-value, and its extrema over the whole space are the restricted ones. -/
theorem biSup_biInf_eq_biInf_biSup_of_isBounded_right (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip] (hB : Bx.SeparatingRight)
    (hC : Convex ℝ C) (hCcl : IsClosed C) (hDcl : IsClosed D) (hCne : C.Nonempty)
    (hDne : D.Nonempty) (hconv : ∀ u ∈ C, ConvexOn ℝ D fun x => K (u, x))
    (hconc : ∀ x ∈ D, ConcaveOn ℝ C fun u => K (u, x))
    (hcontD : ∀ u ∈ C, ContinuousOn (fun x => K (u, x)) D)
    (hcontC : ∀ x ∈ D, ContinuousOn (fun u => K (u, x)) C)
    (hbd : Bornology.IsBounded D) :
    (⨆ u ∈ C, ⨅ x ∈ D, ((K (u, x) : ℝ) : EReal))
      = ⨅ x ∈ D, ⨆ u ∈ C, ((K (u, x) : ℝ) : EReal) := by
  obtain ⟨F, hFconv, hFcl, hmem⟩ := exists_bifunSaddleClass_lowerSimpleExt Bu Bx hC hCcl hDcl
    hCne hDne hconv hconc hcontD hcontC
  refine biSup_biInf_eq_biInf_biSup_of_hasSaddleValue_lowerSimpleExt hC hCcl hDcl hCne hDne hconv
    hconc hcontD hcontC ?_
  exact hasSaddleValue_of_isBounded_dom₂ Bu Bx hB hFconv hFcl hmem
    (concaveConvexFn_lowerSimpleExt hC hconv hconc) (properSaddleFn_lowerSimpleExt hCne hDne)
    (saddleStructure_lowerSimpleExt hC hCcl hDcl hCne hDne hconv hconc hcontD hcontC)
    (by rw [dom₂_lowerSimpleExt (K := K) hCne]; exact hbd)

/-- The half where `C` is bounded. -/
theorem biSup_biInf_eq_biInf_biSup_of_isBounded_left (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip] (hB : Bu.SeparatingLeft)
    (hC : Convex ℝ C) (hCcl : IsClosed C) (hDcl : IsClosed D) (hCne : C.Nonempty)
    (hDne : D.Nonempty) (hconv : ∀ u ∈ C, ConvexOn ℝ D fun x => K (u, x))
    (hconc : ∀ x ∈ D, ConcaveOn ℝ C fun u => K (u, x))
    (hcontD : ∀ u ∈ C, ContinuousOn (fun x => K (u, x)) D)
    (hcontC : ∀ x ∈ D, ContinuousOn (fun u => K (u, x)) C)
    (hbd : Bornology.IsBounded C) :
    (⨆ u ∈ C, ⨅ x ∈ D, ((K (u, x) : ℝ) : EReal))
      = ⨅ x ∈ D, ⨆ u ∈ C, ((K (u, x) : ℝ) : EReal) := by
  obtain ⟨F, hFconv, hFcl, hmem⟩ := exists_bifunSaddleClass_lowerSimpleExt Bu Bx hC hCcl hDcl
    hCne hDne hconv hconc hcontD hcontC
  refine biSup_biInf_eq_biInf_biSup_of_hasSaddleValue_lowerSimpleExt hC hCcl hDcl hCne hDne hconv
    hconc hcontD hcontC ?_
  exact hasSaddleValue_of_isBounded_dom₁ Bu Bx hB hFconv hFcl hmem
    (concaveConvexFn_lowerSimpleExt hC hconv hconc) (properSaddleFn_lowerSimpleExt hCne hDne)
    (saddleStructure_lowerSimpleExt hC hCcl hDcl hCne hDne hconv hconc hcontD hcontC)
    (by rw [dom₁_lowerSimpleExt (K := K) hDne]; exact hbd)

/-- **The minimax theorem**: a finite continuous concave-convex function on a product of nonempty
compact convex sets has a saddle-point relative to that product. The bounded-domain criterion gives
the lower simple extension a saddle-point, that saddle-point lies in `C × D`, and there the
extension agrees with `K`. -/
theorem exists_saddlePoint_of_isBounded (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu]
    [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx]
    [IsCompatiblePairing Bx.flip] (hBu : Bu.SeparatingLeft) (hBx : Bx.SeparatingRight)
    (hC : Convex ℝ C) (hCcl : IsClosed C) (hDcl : IsClosed D) (hCne : C.Nonempty)
    (hDne : D.Nonempty) (hconv : ∀ u ∈ C, ConvexOn ℝ D fun x => K (u, x))
    (hconc : ∀ x ∈ D, ConcaveOn ℝ C fun u => K (u, x))
    (hcontD : ∀ u ∈ C, ContinuousOn (fun x => K (u, x)) D)
    (hcontC : ∀ x ∈ D, ContinuousOn (fun u => K (u, x)) C)
    (hbdC : Bornology.IsBounded C) (hbdD : Bornology.IsBounded D) :
    ∃ q : U × Y, q.1 ∈ C ∧ q.2 ∈ D ∧
      (∀ u ∈ C, K (u, q.2) ≤ K q) ∧ ∀ x ∈ D, K q ≤ K (q.1, x) := by
  obtain ⟨F, hFconv, hFcl, hmem⟩ := exists_bifunSaddleClass_lowerSimpleExt Bu Bx hC hCcl hDcl
    hCne hDne hconv hconc hcontD hcontC
  have hp : ProperSaddleFn (lowerSimpleExt C D K) := properSaddleFn_lowerSimpleExt hCne hDne
  obtain ⟨q, hq⟩ := exists_isSaddlePoint_of_isBounded_domSaddle Bu Bx hBu hBx hFconv hFcl hmem
    (concaveConvexFn_lowerSimpleExt hC hconv hconc) hp
    (saddleStructure_lowerSimpleExt hC hCcl hDcl hCne hDne hconv hconc hcontD hcontC)
    (by rw [dom₁_lowerSimpleExt (K := K) hDne]; exact hbdC)
    (by rw [dom₂_lowerSimpleExt (K := K) hCne]; exact hbdD)
  obtain ⟨hq₁, hq₂⟩ := hq.mem_domSaddle hp
  rw [dom₁_lowerSimpleExt (K := K) hDne] at hq₁
  rw [dom₂_lowerSimpleExt (K := K) hCne] at hq₂
  have hval : lowerSimpleExt C D K q = ((K q : ℝ) : EReal) :=
    lowerSimpleExt_of_mem (p := q) hq₁ hq₂
  refine ⟨q, hq₁, hq₂, fun u hu => ?_, fun x hx => ?_⟩
  · have h := hq.1 u
    rw [lowerSimpleExt_of_mem (p := (u, q.2)) hu hq₂, hval, EReal.coe_le_coe_iff] at h
    exact h
  · have h := hq.2 x
    rw [lowerSimpleExt_of_mem (p := (q.1, x)) hq₁ hx, hval, EReal.coe_le_coe_iff] at h
    exact h

end Minimax

/-! ### `∂K` as the subdifferential of the graph function, partially inverted -/

section GraphSubdifferential

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]

private theorem add_coe_right_inj {a b : EReal} {r : ℝ} :
    a + (r : EReal) = b + (r : EReal) ↔ a = b :=
  ⟨fun h => le_antisymm ((EReal.addLECancellable_coe r).add_le_add_iff_right.1 h.le)
      ((EReal.addLECancellable_coe r).add_le_add_iff_right.1 h.ge), fun h => by rw [h]⟩

/-- The arithmetic behind that identification: with `e = c - d`, the equations `-b = e - a` and
`a - c = b - d` say the same thing, both reducing to `a + d = b + c`. -/
private theorem neg_eq_coe_sub_iff_sub_coe_eq_sub_coe (a b : EReal) (c d e : ℝ)
    (he : -d + c = e) :
    -b = ((e : ℝ) : EReal) - a ↔ a - ((c : ℝ) : EReal) = b - ((d : ℝ) : EReal) := by
  have hb : -b = -(b - ((0 : ℝ) : EReal)) := by
    rw [EReal.coe_zero, sub_zero]
  have hkey : b + ((e : ℝ) : EReal) + ((d : ℝ) : EReal) = b + ((c : ℝ) : EReal) := by
    rw [add_assoc, ← EReal.coe_add]
    congr 2
    linarith
  rw [hb, ← neg_sub_coe a e, _root_.neg_inj, sub_coe_eq_sub_coe_iff, EReal.coe_zero,
    add_zero, sub_coe_eq_sub_coe_iff]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← h]
    exact hkey
  · exact add_coe_right_inj.1 (hkey.trans h.symm)

/-- Membership in the subdifferential of the class `Ω (F)` is membership in the subdifferential
of the graph function `f` of `F`, with the pair `(u*, v)` **partially inverted** to `(-u*, v)`. No
hypothesis on `F` is needed: it is the conjugate criterion for a subgradient together with the
unconditional identity `(F* v)(u*) = -f*(-u*, v)`. -/
theorem isBifunSubgradientPair_iff_mem_subdifferential_graphFn (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (F : Bifun U X) (p : U × Y) (q : V × X) :
    IsBifunSubgradientPair Bu Bx F p q ↔
      (-q.1, p.2) ∈ subdifferential (prodPairing Bu Bx) (graphFn F) (p.1, q.2) := by
  have hconj : convexConj (prodPairing Bu Bx) (graphFn F) (-q.1, p.2)
      = -(convexAdjointBifun Bu Bx F p.2 q.1) := by
    rw [convexAdjointBifun_eq_neg_convexConj_graphFn, neg_neg]
  have hpair : (prodPairing Bu Bx (p.1, q.2) (-q.1, p.2) : ℝ)
      = -(Bu p.1 q.1) + Bx q.2 p.2 := by
    simp
  rw [mem_subdifferential_iff_convexConj_eq, hconj, hpair, graphFn_apply,
      isBifunSubgradientPair_def]
  exact (neg_eq_coe_sub_iff_sub_coe_eq_sub_coe _ _ _ _ _ rfl).symm

end GraphSubdifferential

section GraphInversion

variable {U V X Y : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] {F : Bifun U X} {K : U × Y → EReal}

/-- **The graph of `∂K` is the graph of `∂f` partially inverted**, `f` the graph function of `F`,
as an equality of sets. The inversion `(u, y, v, x) ↦ ((u, x), (-v, y))` is a linear homeomorphism,
which is what makes closedness and maximal monotonicity transfer from `∂f`. -/
theorem setOf_mem_saddleSubdifferential_eq_preimage (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip] (hF : ConvexBifun F)
    (hcl : ClosedConvexBifun F) (hK : K ∈ bifunSaddleClass Bu Bx F) :
    {r : (U × Y) × (V × X) | r.2 ∈ saddleSubdifferential Bu Bx.flip K r.1}
      = (fun r : (U × Y) × (V × X) => ((r.1.1, r.2.2), (-r.2.1, r.1.2)))
        ⁻¹' subgradientRel (prodPairing Bu Bx) (graphFn F) := by
  ext r
  rw [Set.mem_preimage, Set.mem_ofPred_eq,
    mem_saddleSubdifferential_iff_isBifunSubgradientPair Bu Bx hF hcl hK,
    isBifunSubgradientPair_iff_mem_subdifferential_graphFn]
  exact Iff.rfl

/-- The graph of `∂K` is closed: it is the preimage of the graph of `∂f` under a linear
homeomorphism, and the graph of the subdifferential of a closed proper convex function is closed.
The homeomorphism clause is `saddleSubdifferentialHomeomorph`. -/
theorem isClosed_setOf_mem_saddleSubdifferential (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu]
    [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx]
    [IsCompatiblePairing Bx.flip] (hcu : Continuous fun r : U × V => Bu r.1 r.2)
    (hcx : Continuous fun r : X × Y => Bx r.1 r.2) (hF : ConvexBifun F) (hcl : ClosedConvexBifun F)
    (hpr : ProperConvex (graphFn F)) (hK : K ∈ bifunSaddleClass Bu Bx F) :
    IsClosed {r : (U × Y) × (V × X) | r.2 ∈ saddleSubdifferential Bu Bx.flip K r.1} := by
  have hcont : Continuous fun r : (U × Y) × (V × X) => ((r.1.1, r.2.2), (-r.2.1, r.1.2)) := by
    fun_prop
  have hpairing : Continuous fun r : (U × X) × (V × Y) => (prodPairing Bu Bx) r.1 r.2 := by
    have hgu : Continuous fun r : (U × X) × (V × Y) => (r.1.1, r.2.1) := by fun_prop
    have hgx : Continuous fun r : (U × X) × (V × Y) => (r.1.2, r.2.2) := by fun_prop
    have h1 : Continuous fun r : (U × X) × (V × Y) => Bu r.1.1 r.2.1 := hcu.comp hgu
    have h2 : Continuous fun r : (U × X) × (V × Y) => Bx r.1.2 r.2.2 := hcx.comp hgx
    have h3 : Continuous fun r : (U × X) × (V × Y) => Bu r.1.1 r.2.1 + Bx r.1.2 r.2.2 :=
      h1.add h2
    simpa only [prodPairing_apply] using h3
  rw [setOf_mem_saddleSubdifferential_eq_preimage Bu Bx hF hcl hK]
  exact IsClosed.preimage hcont
    (isClosed_subgradientRel hpairing hpr (ClosedConvex.lowerSemicontinuous hcl))

end GraphInversion

end ConvexAnalysis
