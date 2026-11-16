/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Saddle.Subdifferential
import Numlib.Analysis.Convex.Subdifferential.Monotone

/-!
# Existence of saddle-values and saddle-points

Let $F$ be a closed convex bifunction from $U$ to $X$, and let $K$ be a concave-convex function in
its class $\Omega(F)$, with effective domains $C = \operatorname{dom}_1 K$ and
$D = \operatorname{dom}_2 K$. The saddle-value of $K$ exists if
$\sup_u \inf_y K(u, y) = \inf_y \sup_u K(u, y)$. This module turns the effective domains $C^*$ and
$D^*$ of the upper conjugate $$\overline{K}^*(u^*, x) = \inf_u \sup_y \{\langle u, u^* \rangle +
\langle x, y \rangle - K(u, y)\}$$ (`Numlib.Analysis.Convex.Saddle.Conjugate`) into criteria for a
saddle-value and a saddle-point in terms of $K$ alone. Each criterion has a form in the second
variable and a form in the first. The criteria are then specialized to a finite continuous
concave-convex function on a product of closed convex sets, which gives the classical **minimax
theorem**. The presentation follows [rockafellar1970convex], §24, §34, §36 and §37.

The module closes with the identification of the subdifferential $\partial K$ with the
subdifferential of the graph function $f(u, x) = (Fu)(x)$ of $F$, partially inverted along a linear
homeomorphism.

## Main definitions

* `ConvexAnalysis.swapAdjointBifun`: the convex bifunction $F^\sharp$ from $Y$ to $V$ with
  $(F^\sharp y)(v) = -(F^* y)(v)$.

## Main results

* `ConvexAnalysis.convexAdjointBifun_swapAdjointBifun`,
  `ConvexAnalysis.saddleSwap_mem_bifunSaddleClass`: the swap $(y, u) \mapsto -K(u, y)$ carries
  $\Omega(F)$ into $\Omega(F^\sharp)$, and the adjoint of $F^\sharp$ is $-F$. The two conjugates are
  exchanged by `ConvexAnalysis.upperConjSaddle_saddleSwap` and
  `ConvexAnalysis.lowerConjSaddle_saddleSwap`.
* `ConvexAnalysis.properConvex_graphFn_of_properSaddleFn`: a proper member of $\Omega(F)$ forces the
  graph function of $F$ to be proper.
* `ConvexAnalysis.zero_mem_interior_dom₂_upperConjSaddle_iff`,
  `ConvexAnalysis.zero_mem_interior_dom₁_upperConjSaddle_iff`: $0 \in \operatorname{int} D^*$ and
  $0 \in \operatorname{int} C^*$ in terms of directions of recession, as in Corollary 37.2.1 of
  [rockafellar1970convex].
* `ConvexAnalysis.hasSaddleValue_of_no_common_direction_of_recession_snd`,
  `ConvexAnalysis.hasSaddleValue_of_no_common_direction_of_recession_fst`: the saddle-value exists
  if the slices in one variable have no common direction of recession, as in Theorem 37.3 of
  [rockafellar1970convex].
* `ConvexAnalysis.hasSaddleValue_of_isBounded_dom₂`,
  `ConvexAnalysis.hasSaddleValue_of_isBounded_dom₁`: the saddle-value exists if $D$ or $C$ is
  bounded.
* `ConvexAnalysis.exists_isSaddlePoint_of_no_common_direction_of_recession`,
  `ConvexAnalysis.exists_isSaddlePoint_of_isBounded_domSaddle`: a saddle-point exists if neither
  variable has a common direction of recession, as in Theorem 37.6 of [rockafellar1970convex], or if
  $C$ and $D$ are bounded.
* `ConvexAnalysis.saddleStructure_lowerSimpleExt`, `ConvexAnalysis.maximin_lowerSimpleExt`,
  `ConvexAnalysis.minimax_lowerSimpleExt`, `ConvexAnalysis.exists_bifunSaddleClass_lowerSimpleExt`:
  the transfer to a finite continuous concave-convex function on a closed product $C \times D$,
  through its lower simple extension.
* `ConvexAnalysis.biSup_biInf_eq_biInf_biSup_of_isBounded_right`,
  `ConvexAnalysis.biSup_biInf_eq_biInf_biSup_of_isBounded_left`: $\sup_{u \in C} \inf_{x \in D} K =
  \inf_{x \in D} \sup_{u \in C} K$ if one of $C$ and $D$ is bounded.
* `ConvexAnalysis.exists_saddlePoint_of_isBounded`: the **minimax theorem**, as in Corollary 37.6.2
  of [rockafellar1970convex].
* `ConvexAnalysis.isBifunSubgradientPair_iff_mem_subdifferential_graphFn`,
  `ConvexAnalysis.setOf_mem_saddleSubdifferential_eq_preimage`,
  `ConvexAnalysis.isClosed_setOf_mem_saddleSubdifferential`: $\partial K$ is $\partial f$ partially
  inverted, pointwise and as an equality of graphs, and the graph of $\partial K$ is closed.

## Proof outline

The device is the swap $(y, u) \mapsto -K(u, y)$. It carries the class $\Omega(F)$ into the class
$\Omega(F^\sharp)$ for the negated flipped pairings $(y, x) \mapsto -\langle x, y \rangle$ and
$(v, u) \mapsto -\langle u, v \rangle$, and it exchanges the two conjugates. So every statement
about the first variable and $C^*$ is the corresponding statement about the second variable and
$D^*$, read at the swapped data, and no new duality theory is needed. The pairings must be negated
and not only flipped: the swap negates the values, and only the negated pairings restore the sign of
the linear terms in the two conjugates.

## Implementation notes

* The statements $\sup \inf = \inf \sup$ are equalities of extended-real extrema. The customary
  display is $\inf_D \sup_C K = \sup_C \inf_D K$ for a finite $K$, but when only one of $C$ and $D$
  is bounded the two iterated extrema can be $\pm\infty$. The minimax theorem, where both sets are
  bounded, is stated with real inequalities.
* The results about a finite $K$ on $C \times D$ still take pairings of $U$ with $V$ and of $X$ with
  $Y$ as hypotheses, because the proofs pass through a class $\Omega(F)$. These hypotheses concern
  only the auxiliary pairings, not $K$.
* The hypothesis `ConvexAnalysis.SaddleStructure K` is the structural description of a closed proper
  saddle-function from `Numlib.Analysis.Convex.Saddle.Kernel`.
-/

namespace ConvexAnalysis

/-! ### The swap and the conjugate saddle-functions -/

section SwapNeg

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]

/-- **The adjoint commutes with flipping once both pairings are negated and exchanged.** For every
bifunction $F$ from $U$ to $X$, the adjoint of the flipped bifunction $(x, u) \mapsto (Fu)(x)$,
taken with respect to the pairings $-\langle x, y \rangle$ and $-\langle u, v \rangle$, is the
flip of $F^*$: its value at $(v, y)$ is $(F^* y)(v)$.

This identity is behind the whole swap dictionary. The adjoint is an infimum over $U \times X$
of $(Fu)(x) + \langle u, v \rangle - \langle x, y \rangle$, and negating and exchanging the
pairings gives the same summand with the two bound variables exchanged. -/
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
/-- For every bifunction $G$ from $Y$ to $V$, let $H$ be the bifunction from $Y$ to $V$ with
$(Hy)(v) = -(Gy)(v)$. With respect to the pairing $(v, u) \mapsto -\langle u, v \rangle$, the
bracket of $H$ is the negative of the bracket of $G$:
$\langle Hy, u \rangle = -\langle u, Gy \rangle$.

This is one of the two halves of the swap dictionary for equivalence classes. -/
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
/-- For every bifunction $H$ from $U$ to $X$, let $G$ be the bifunction from $U$ to $X$ with
$(Gu)(x) = -(Hu)(x)$. With respect to the pairing $(y, x) \mapsto -\langle x, y \rangle$, the
concave bracket of $G$ is the negative of the bracket of $H$:
$\langle y, Gu \rangle = -\langle Hu, y \rangle$.

This is the mirror half of `ConvexAnalysis.bracket_neg_flip_flipBifun_inverseBifun`. -/
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

/-! ### The class $\Omega(F)$ seen through the swap -/

section SwapClass

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]

/-- The bifunction $F^\sharp$ from $Y$ to $V$ attached to the swapped saddle-function: $$(F^\sharp
y)(v) = -(F^* y)(v).$$

It is not $F_*^*$, which goes from $V$ to $Y$ and belongs to the conjugate class on
$V \times X$. The bifunction $F^\sharp$ goes from $Y$ to $V$, and the two differ by an exchange
of the arguments. Its two brackets with respect to the negated flipped pairings are the
negatives of the two brackets of $F$, exchanged, and this is what the swap does to the class
$\Omega(F)$. -/
noncomputable def swapAdjointBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (F : Bifun U X) : Bifun Y V :=
  flipBifun (lowerAdjointBifun Bu Bx F)

/-- $(F^\sharp y)(v) = -(F^* y)(v)$. -/
@[simp] theorem swapAdjointBifun_apply (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (F : Bifun U X) (y : Y) (v : V) :
    swapAdjointBifun Bu Bx F y v = -(convexAdjointBifun Bu Bx F y v) := rfl

/-- For every bifunction $F$, the bifunction $F^\sharp$ is convex: it is $F_*^*$ with its two
arguments exchanged. -/
theorem convexBifun_swapAdjointBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (F : Bifun U X) : ConvexBifun (swapAdjointBifun Bu Bx F) :=
  convexBifun_flipBifun (convexBifun_lowerAdjointBifun Bu Bx F)

end SwapClass

section SwapClassClosed

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace V] [IsTopologicalAddGroup V] [TopologicalSpace Y] [IsTopologicalAddGroup Y]

/-- Let $V$ and $Y$ be commutative topological groups, and let the pairings be such that every
$\langle u, \cdot \rangle$ is continuous on $V$ and every $\langle x, \cdot \rangle$ is
continuous on $Y$. For every bifunction $F$, the bifunction $F^\sharp$ is closed, because an
adjoint bifunction is closed. -/
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

/-- **The adjoint of $F^\sharp$ is $-F$.** Let $U$ and $X$ be locally convex topological vector
spaces with compatible pairings with $V$ and $Y$, and let $F$ be a closed convex bifunction from
$U$ to $X$. With respect to the pairings $(y, x) \mapsto -\langle x, y \rangle$ and
$(v, u) \mapsto -\langle u, v \rangle$, the adjoint of $F^\sharp$ is the bifunction
$(u, x) \mapsto -(Fu)(x)$.

This is the biadjoint identity $(F_*^*)^* = F_*$, read through
`ConvexAnalysis.convexAdjointBifun_neg_flipBifun`. -/
theorem convexAdjointBifun_swapAdjointBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu]
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx] (hF : ConvexBifun F)
    (hcl : ClosedConvexBifun F) :
    convexAdjointBifun (-Bx.flip) (-Bu.flip) (swapAdjointBifun Bu Bx F)
        = flipBifun (inverseBifun F) := by
  rw [swapAdjointBifun, convexAdjointBifun_neg_flipBifun Bu.flip Bx.flip,
    convexAdjointBifun_flip_lowerAdjointBifun (Bu := Bu) (Bx := Bx) hF hcl]

/-- **The swap dictionary for equivalence classes.** Let $U$ and $X$ be locally convex topological
vector spaces with compatible pairings with $V$ and $Y$, and let $F$ be a closed convex
bifunction from $U$ to $X$. If $K \in \Omega(F)$, then the swap $(y, u) \mapsto -K(u, y)$ lies
in $\Omega(F^\sharp)$, the class taken with respect to the pairings
$(y, x) \mapsto -\langle x, y \rangle$ and $(v, u) \mapsto -\langle u, v \rangle$.

So every statement about the first variable is the corresponding statement about the second
variable, read at the swapped data. -/
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

/-- **A proper member forces a proper bifunction.** If $K \in \Omega(F)$ and $K$ is proper, that is,
$\operatorname{dom}_1 K$ and $\operatorname{dom}_2 K$ are nonempty, then the graph function
$(u, x) \mapsto (Fu)(x)$ of $F$ is proper: it is less than $+\infty$ somewhere and never equals
$-\infty$.

If $(Fu)(x) = -\infty$ for some $(u, x)$, then $\langle Fu, \cdot \rangle$ is identically
$+\infty$, which contradicts $\operatorname{dom}_2 K \neq \emptyset$. If $F$ is identically
$+\infty$, then the upper bracket is $-\infty$, which contradicts
$\operatorname{dom}_1 K \neq \emptyset$. The two kinds of properness are usually not separated,
but the results here need properness of the graph function while the structural theorems give
properness of $K$. -/
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

/-- If a pairing $\langle x, y \rangle$ of $E$ with $F$ separates the points of $E$, then the
pairing $(y, x) \mapsto -\langle x, y \rangle$ of $F$ with $E$ separates the points of its
second space $E$. -/
theorem separatingRight_neg_flip {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} (hB : B.SeparatingLeft) :
    (-B.flip).SeparatingRight := by
  intro x hx
  refine hB x fun y => ?_
  have h := hx y
  simpa using h

end SeparatingNeg

/-!
### The saddle-value criteria

Each criterion has a form in the second variable, about $D^*$ and the slices $K(u, \cdot)$, and a
form in the first variable, about $C^*$ and the slices $-K(\cdot, y)$. The form about $D^*$ is
proved from the support function of $D^*$ (`Numlib.Analysis.Convex.Saddle.Conjugate`). The form
about $C^*$ is the form about $D^*$ read at the swap of $K$, whose class is $\Omega(F^\sharp)$ for
the negated flipped pairings.
-/

section SaddleValue

variable {U V X Y : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
  {F : Bifun U X} {K : U × Y → EReal}

omit [FiniteDimensional ℝ V] in
/-- **The origin is an interior point of $D^*$** if and only if the convex functions $K(u, \cdot)$,
$u \in \operatorname{ri} C$, have no common direction of recession. Let $U$, $X$ and $Y$ be
finite-dimensional normed spaces and $V$ a normed space. Let the pairing of $U$ with $V$ be
compatible on $U$, let the pairing of $X$ with $Y$ be compatible on $X$ and on $Y$, and let it
separate the points of $Y$. Let $F$ be a closed convex bifunction from $U$ to $X$, and let
$K \in \Omega(F)$ be concave-convex, proper, and with the structure
`ConvexAnalysis.SaddleStructure` of a closed proper saddle-function. Then
$0 \in \operatorname{int} D^*$ if and only if for every $w \in Y$ with $w \neq 0$ there is
$u \in \operatorname{ri} C$ with $$(K(u, \cdot) 0^+)(w) > 0,$$ where $0^+$ denotes the recession
function. This is Corollary 37.2.1 of [rockafellar1970convex], first half.

The proof uses that $0 \in \operatorname{int} D^*$ if and only if $\delta^*(w \mid D^*) > 0$ for
every $w \neq 0$, and that $\delta^*(w \mid D^*)$ is the supremum of the $(K(u, \cdot) 0^+)(w)$.
The separation hypothesis makes $w \neq 0$ and $\langle \cdot, w \rangle \neq 0$ the same
condition. It holds automatically when a space is paired with itself by an inner product. -/
theorem zero_mem_interior_dom₂_upperConjSaddle_iff (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
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

/-- **The origin is an interior point of $C^*$** if and only if the convex functions $-K(\cdot, y)$,
$y \in \operatorname{ri} D$, have no common direction of recession. Let $U$, $V$, $X$ and $Y$ be
finite-dimensional normed spaces, let both pairings be compatible on both sides, and let the
pairing of $U$ with $V$ separate the points of $U$. Let $F$ be a closed convex bifunction from
$U$ to $X$, and let $K \in \Omega(F)$ be concave-convex, proper, and with the structure
`ConvexAnalysis.SaddleStructure`. Then $0 \in \operatorname{int} C^*$ if and only if for every
$z \in U$ with $z \neq 0$ there is $y \in \operatorname{ri} D$ with $$((-K(\cdot, y)) 0^+)(z) >
0.$$ This is Corollary 37.2.1 of [rockafellar1970convex], second half.

The proof reads the criterion for $D^*$ at the swap of $K$. -/
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

/-- Let $U$, $V$, $X$ and $Y$ be finite-dimensional normed spaces, let both pairings be compatible
on both sides, and let the pairing of $X$ with $Y$ separate the points of $Y$. Let $F$ be a
closed convex bifunction from $U$ to $X$, and let $K \in \Omega(F)$ be concave-convex, proper,
and with the structure `ConvexAnalysis.SaddleStructure`. If the convex functions $K(u, \cdot)$,
$u \in \operatorname{ri} C$, have no common direction of recession, that is, for every
$w \neq 0$ there is $u \in \operatorname{ri} C$ with $(K(u, \cdot) 0^+)(w) > 0$, then the
saddle-value of $K$ exists. This is Theorem 37.3 (a) of [rockafellar1970convex].

The hypothesis is $0 \in \operatorname{int} D^*$, and the origin in $\operatorname{ri} D^*$
gives the saddle-value. -/
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

/-- Let $U$, $V$, $X$ and $Y$ be finite-dimensional normed spaces, let both pairings be compatible
on both sides, and let the pairing of $U$ with $V$ separate the points of $U$. Let $F$ be a
closed convex bifunction from $U$ to $X$, and let $K \in \Omega(F)$ be concave-convex, proper,
and with the structure `ConvexAnalysis.SaddleStructure`. If the convex functions $-K(\cdot, y)$,
$y \in \operatorname{ri} D$, have no common direction of recession, that is, for every
$z \neq 0$ there is $y \in \operatorname{ri} D$ with $((-K(\cdot, y)) 0^+)(z) > 0$, then the
saddle-value of $K$ exists. This is Theorem 37.3 (b) of [rockafellar1970convex].

The hypothesis is $0 \in \operatorname{int} C^*$. -/
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
/-- **A bounded $D$ leaves the slices $K(u, \cdot)$ no common direction of recession.** Let $U$ be a
finite-dimensional normed space and $Y$ a normed space, and let $K$ be concave-convex, proper,
and with the structure `ConvexAnalysis.SaddleStructure`. If $D = \operatorname{dom}_2 K$ is
bounded and $w \neq 0$, then there is $u \in \operatorname{ri} C$ with
$(K(u, \cdot) 0^+)(w) > 0$.

For $u \in \operatorname{ri} C$ the effective domain of $K(u, \cdot)$ is exactly $D$. -/
theorem exists_mem_relint_lt_recessionFn_of_isBounded_dom₂ (hKcc : ConcaveConvexFn K)
    (hp : ProperSaddleFn K) (hs : SaddleStructure K) (hbd : Bornology.IsBounded (dom₂ K))
    {w : Y} (hw : w ≠ 0) : ∃ u ∈ ri (dom₁ K), 0 < recessionFn (fun y => K (u, y)) w := by
  obtain ⟨u, hu⟩ := Convex.relint_nonempty hKcc.convex_dom₁ hp.dom₁_nonempty
  have hdom : convexDom (fun y => K (u, y)) = dom₂ K := hs.1.convexDom_slice u hu
  exact ⟨u, hu, lt_recessionFn_of_isBounded_convexDom (by rw [hdom]; exact hp.dom₂_nonempty)
    (by rw [hdom]; exact hbd) hw⟩

omit [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [NormedAddCommGroup X]
  [NormedSpace ℝ X] [FiniteDimensional ℝ X] [FiniteDimensional ℝ U] in
/-- **A bounded $C$ leaves the slices $-K(\cdot, y)$ no common direction of recession.** Let $U$ be
a normed space and $Y$ a finite-dimensional normed space, and let $K$ be concave-convex, proper,
and with the structure `ConvexAnalysis.SaddleStructure`. If $C = \operatorname{dom}_1 K$ is
bounded and $z \neq 0$, then there is $y \in \operatorname{ri} D$ with
$((-K(\cdot, y)) 0^+)(z) > 0$.

This is the statement for the second variable, read at the swap of $K$. -/
theorem exists_mem_relint_lt_recessionFn_of_isBounded_dom₁ (hKcc : ConcaveConvexFn K)
    (hp : ProperSaddleFn K) (hs : SaddleStructure K) (hbd : Bornology.IsBounded (dom₁ K))
    {z : U} (hz : z ≠ 0) : ∃ y ∈ ri (dom₂ K), 0 < recessionFn (fun u => -(K (u, y))) z := by
  have h := exists_mem_relint_lt_recessionFn_of_isBounded_dom₂ hKcc.saddleSwap hp.saddleSwap
    hs.saddleSwap (by rwa [dom₂_saddleSwap]) hz
  rw [dom₁_saddleSwap] at h
  exact h

/-- **If the second effective domain of $K$ is bounded, the saddle-value of $K$ exists.** Let $U$,
$V$, $X$ and $Y$ be finite-dimensional normed spaces, let both pairings be compatible on both
sides, and let the pairing of $X$ with $Y$ separate the points of $Y$. Let $F$ be a closed
convex bifunction from $U$ to $X$, and let $K \in \Omega(F)$ be concave-convex, proper, and with
the structure `ConvexAnalysis.SaddleStructure`. If $D = \operatorname{dom}_2 K$ is bounded, then
the saddle-value of $K$ exists. This is Corollary 37.3.1 of [rockafellar1970convex], the case
where $D$ is bounded.

Over a compact $D$ this is the classical minimax theorem. -/
theorem hasSaddleValue_of_isBounded_dom₂ (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu]
    [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx]
    [IsCompatiblePairing Bx.flip] (hB : Bx.SeparatingRight) (hF : ConvexBifun F)
    (hcl : ClosedConvexBifun F) (hK : K ∈ bifunSaddleClass Bu Bx F) (hKcc : ConcaveConvexFn K)
    (hp : ProperSaddleFn K) (hs : SaddleStructure K)
    (hbd : Bornology.IsBounded (dom₂ K)) : HasSaddleValue K :=
  hasSaddleValue_of_no_common_direction_of_recession_snd Bu Bx hB hF hcl hK hKcc hp hs
    fun _ hw => exists_mem_relint_lt_recessionFn_of_isBounded_dom₂ hKcc hp hs hbd hw

/-- **If the first effective domain of $K$ is bounded, the saddle-value of $K$ exists.** Let $U$,
$V$, $X$ and $Y$ be finite-dimensional normed spaces, let both pairings be compatible on both
sides, and let the pairing of $U$ with $V$ separate the points of $U$. Let $F$ be a closed
convex bifunction from $U$ to $X$, and let $K \in \Omega(F)$ be concave-convex, proper, and with
the structure `ConvexAnalysis.SaddleStructure`. If $C = \operatorname{dom}_1 K$ is bounded, then
the saddle-value of $K$ exists. This is Corollary 37.3.1 of [rockafellar1970convex], the case
where $C$ is bounded. -/
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

/-- Let $U$, $V$, $X$ and $Y$ be finite-dimensional normed spaces, let both pairings be compatible
on both sides, let the pairing of $U$ with $V$ separate the points of $U$, and let the pairing
of $X$ with $Y$ separate the points of $Y$. Let $F$ be a closed convex bifunction from $U$ to
$X$, and let $K \in \Omega(F)$ be concave-convex, proper, and with the structure
`ConvexAnalysis.SaddleStructure`. Suppose that neither variable has a common direction of
recession: for every $w \in Y$ with $w \neq 0$ there is $u \in \operatorname{ri} C$ with
$(K(u, \cdot) 0^+)(w) > 0$, and for every $z \in U$ with $z \neq 0$ there is
$y \in \operatorname{ri} D$ with $((-K(\cdot, y)) 0^+)(z) > 0$. Then $K$ has a saddle-point.
This is Theorem 37.6 of [rockafellar1970convex].

The two recession conditions give $0 \in \operatorname{int} C^*$ and
$0 \in \operatorname{int} D^*$, and the subdifferential $\partial \overline{K}^*(0, 0)$ is then
a nonempty set of saddle-points. -/
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

/-- Let $U$, $V$, $X$ and $Y$ be finite-dimensional normed spaces, let both pairings be compatible
on both sides, let the pairing of $U$ with $V$ separate the points of $U$, and let the pairing
of $X$ with $Y$ separate the points of $Y$. Let $F$ be a closed convex bifunction from $U$ to
$X$, and let $K \in \Omega(F)$ be concave-convex, proper, and with the structure
`ConvexAnalysis.SaddleStructure`. If $C = \operatorname{dom}_1 K$ and
$D = \operatorname{dom}_2 K$ are both bounded, then $K$ has a saddle-point. This is Corollary
37.6.1 of [rockafellar1970convex]. -/
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

/-- Under the hypotheses of `ConvexAnalysis.exists_isSaddlePoint_of_isBounded_domSaddle`, the
saddle-value $\sup_u \inf_y K(u, y)$ is a real number.

It is a value of $K$ at a saddle-point, and a proper saddle-function is finite on its effective
domain. -/
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

/-! ### A finite continuous saddle-function on $C \times D$ -/

section SimpleExt

variable {U V X Y : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
  {C : Set U} {D : Set Y} {K : U × Y → ℝ}

omit [FiniteDimensional ℝ V] [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] in
/-- Let $U$ and $Y$ be finite-dimensional normed spaces, let $C \subseteq U$ be nonempty, closed and
convex, and let $D \subseteq Y$ be nonempty and closed. Let $K : U \times Y \to \mathbb{R}$ be
concave-convex on $C \times D$, with $K(u, \cdot)$ continuous on $D$ for every $u \in C$ and
$K(\cdot, x)$ continuous on $C$ for every $x \in D$. Then the lower simple extension $K_1$ of
$K$ ($K$ on $C \times D$, $+\infty$ on $C \times (Y \setminus D)$, and $-\infty$ off $C$) has
the structure `ConvexAnalysis.SaddleStructure` of a closed proper saddle-function.

The convexity of $D$ follows from the hypothesis that $K$ is concave-convex on $C \times D$. -/
theorem saddleStructure_lowerSimpleExt (hC : Convex ℝ C) (hCcl : IsClosed C) (hDcl : IsClosed D)
    (hCne : C.Nonempty) (hDne : D.Nonempty)
    (hK : ConcaveConvexOn C D K)
    (hcontD : ∀ u ∈ C, ContinuousOn (fun x => K (u, x)) D)
    (hcontC : ∀ x ∈ D, ContinuousOn (fun u => K (u, x)) C) :
    SaddleStructure (lowerSimpleExt C D K) :=
  (closedSaddleFn_iff_saddleStructure (concaveConvexFn_lowerSimpleExt hC hK)
      (properSaddleFn_lowerSimpleExt hCne hDne)).1
    (closedSaddleFn_of_mem_saddleClass_simpleExt hCcl hDcl hCne hDne hcontD hcontC
      (mem_saddleClass_left (partialCl₂_upperSimpleExt hDcl hDne hcontD)))

omit [FiniteDimensional ℝ V] [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] in
/-- Under the hypotheses of `ConvexAnalysis.saddleStructure_lowerSimpleExt`, the iterated extremum
$\sup_u \inf_x K_1(u, x)$ of the lower simple extension over the whole space equals $$\sup_{u
\in C} \inf_{x \in D} K(u, x),$$ as extended real numbers. -/
theorem maximin_lowerSimpleExt (hC : Convex ℝ C) (hCcl : IsClosed C) (hDcl : IsClosed D)
    (hCne : C.Nonempty) (hDne : D.Nonempty)
    (hK : ConcaveConvexOn C D K)
    (hcontD : ∀ u ∈ C, ContinuousOn (fun x => K (u, x)) D)
    (hcontC : ∀ x ∈ D, ContinuousOn (fun u => K (u, x)) C) :
    maximin (lowerSimpleExt C D K) = ⨆ u ∈ C, ⨅ x ∈ D, ((K (u, x) : ℝ) : EReal) := by
  rw [maximin_eq_biSup_biInf (concaveConvexFn_lowerSimpleExt hC hK)
      (saddleStructure_lowerSimpleExt hC hCcl hDcl hCne hDne hK hcontD hcontC)
      (properSaddleFn_lowerSimpleExt hCne hDne),
    dom₁_lowerSimpleExt (K := K) hDne, dom₂_lowerSimpleExt (K := K) hCne]
  exact iSup_congr fun u => iSup_congr fun hu => iInf_congr fun x => iInf_congr fun hx =>
    lowerSimpleExt_of_mem (p := (u, x)) hu hx

omit [FiniteDimensional ℝ V] [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] in
/-- Under the hypotheses of `ConvexAnalysis.saddleStructure_lowerSimpleExt`, the iterated extremum
$\inf_x \sup_u K_1(u, x)$ of the lower simple extension over the whole space equals $$\inf_{x
\in D} \sup_{u \in C} K(u, x),$$ as extended real numbers. -/
theorem minimax_lowerSimpleExt (hC : Convex ℝ C) (hCcl : IsClosed C) (hDcl : IsClosed D)
    (hCne : C.Nonempty) (hDne : D.Nonempty)
    (hK : ConcaveConvexOn C D K)
    (hcontD : ∀ u ∈ C, ContinuousOn (fun x => K (u, x)) D)
    (hcontC : ∀ x ∈ D, ContinuousOn (fun u => K (u, x)) C) :
    minimax (lowerSimpleExt C D K) = ⨅ x ∈ D, ⨆ u ∈ C, ((K (u, x) : ℝ) : EReal) := by
  rw [minimax_eq_biInf_biSup (concaveConvexFn_lowerSimpleExt hC hK)
      (saddleStructure_lowerSimpleExt hC hCcl hDcl hCne hDne hK hcontD hcontC)
      (properSaddleFn_lowerSimpleExt hCne hDne),
    dom₁_lowerSimpleExt (K := K) hDne, dom₂_lowerSimpleExt (K := K) hCne]
  exact iInf_congr fun x => iInf_congr fun hx => iSup_congr fun u => iSup_congr fun hu =>
    lowerSimpleExt_of_mem (p := (u, x)) hu hx

omit [FiniteDimensional ℝ U] [FiniteDimensional ℝ V] [FiniteDimensional ℝ X]
  [FiniteDimensional ℝ Y] in
/-- Let $U$, $V$, $X$ and $Y$ be normed spaces, let the pairing of $U$ with $V$ be compatible on
$U$, and let the pairing of $X$ with $Y$ be compatible on $X$ and on $Y$. Let $C \subseteq U$ be
nonempty, closed and convex, let $D \subseteq Y$ be nonempty and closed, and let
$K : U \times Y \to \mathbb{R}$ be concave-convex on $C \times D$ and continuous in each
variable separately on $C$ and on $D$. Then there is a closed convex bifunction $F$ from $U$ to
$X$ such that the lower simple extension of $K$ lies in $\Omega(F)$.

This packages the membership $K_1 \in \Omega(F)$ that the criteria above need. -/
theorem exists_bifunSaddleClass_lowerSimpleExt (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu]
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip]
    (hC : Convex ℝ C) (hCcl : IsClosed C) (hDcl : IsClosed D) (hCne : C.Nonempty)
    (hDne : D.Nonempty) (hK : ConcaveConvexOn C D K)
    (hcontD : ∀ u ∈ C, ContinuousOn (fun x => K (u, x)) D)
    (hcontC : ∀ x ∈ D, ContinuousOn (fun u => K (u, x)) C) :
    ∃ F : Bifun U X, ConvexBifun F ∧ ClosedConvexBifun F ∧
      lowerSimpleExt C D K ∈ bifunSaddleClass Bu Bx F := by
  obtain ⟨F, ⟨hFconv, hFcl, hbr1, hbr2⟩, -⟩ := exists_unique_bifun_of_simpleExt Bu Bx hC hCcl
    hDcl hCne hK hDne hcontD hcontC
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
/-- Let $U$ and $Y$ be finite-dimensional normed spaces, let $C \subseteq U$ be nonempty, closed and
convex, let $D \subseteq Y$ be nonempty and closed, and let $K : U \times Y \to \mathbb{R}$ be
concave-convex on $C \times D$ and continuous in each variable separately on $C$ and on $D$. If
the lower simple extension of $K$ has a saddle-value, then $$\sup_{u \in C} \inf_{x \in D} K(u,
x) = \inf_{x \in D} \sup_{u \in C} K(u, x)$$ as extended real numbers.

This is the common last step of the two bounded cases: the extrema of the extension over the
whole space are the restricted extrema of $K$. -/
theorem biSup_biInf_eq_biInf_biSup_of_hasSaddleValue_lowerSimpleExt (hC : Convex ℝ C)
    (hCcl : IsClosed C) (hDcl : IsClosed D) (hCne : C.Nonempty) (hDne : D.Nonempty)
    (hK : ConcaveConvexOn C D K)
    (hcontD : ∀ u ∈ C, ContinuousOn (fun x => K (u, x)) D)
    (hcontC : ∀ x ∈ D, ContinuousOn (fun u => K (u, x)) C)
    (hsv : HasSaddleValue (lowerSimpleExt C D K)) :
    (⨆ u ∈ C, ⨅ x ∈ D, ((K (u, x) : ℝ) : EReal))
      = ⨅ x ∈ D, ⨆ u ∈ C, ((K (u, x) : ℝ) : EReal) := by
  rwa [hasSaddleValue_iff, maximin_lowerSimpleExt hC hCcl hDcl hCne hDne hK hcontD hcontC,
    minimax_lowerSimpleExt hC hCcl hDcl hCne hDne hK hcontD hcontC] at hsv

/-- Let $U$, $V$, $X$ and $Y$ be finite-dimensional normed spaces, let both pairings be compatible
on both sides, and let the pairing of $X$ with $Y$ separate the points of $Y$. Let
$C \subseteq U$ be nonempty, closed and convex, let $D \subseteq Y$ be nonempty, closed and
bounded, and let $K : U \times Y \to \mathbb{R}$ be concave-convex on $C \times D$ and
continuous in each variable separately on $C$ and on $D$. Then $$\sup_{u \in C} \inf_{x \in D}
K(u, x) = \inf_{x \in D} \sup_{u \in C} K(u, x)$$ as extended real numbers. This is Corollary
37.3.2 of [rockafellar1970convex], the case where $D$ is bounded.

The lower simple extension is a closed proper concave-convex function with effective domain
$C \times D$, so it has a saddle-value, and its extrema over the whole space are the restricted
extrema of $K$. -/
theorem biSup_biInf_eq_biInf_biSup_of_isBounded_right (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip] (hB : Bx.SeparatingRight)
    (hC : Convex ℝ C) (hCcl : IsClosed C) (hDcl : IsClosed D) (hCne : C.Nonempty)
    (hDne : D.Nonempty) (hK : ConcaveConvexOn C D K)
    (hcontD : ∀ u ∈ C, ContinuousOn (fun x => K (u, x)) D)
    (hcontC : ∀ x ∈ D, ContinuousOn (fun u => K (u, x)) C)
    (hbd : Bornology.IsBounded D) :
    (⨆ u ∈ C, ⨅ x ∈ D, ((K (u, x) : ℝ) : EReal))
      = ⨅ x ∈ D, ⨆ u ∈ C, ((K (u, x) : ℝ) : EReal) := by
  obtain ⟨F, hFconv, hFcl, hmem⟩ := exists_bifunSaddleClass_lowerSimpleExt Bu Bx hC hCcl hDcl
    hCne hDne hK hcontD hcontC
  refine biSup_biInf_eq_biInf_biSup_of_hasSaddleValue_lowerSimpleExt hC hCcl hDcl hCne hDne hK
    hcontD hcontC ?_
  exact hasSaddleValue_of_isBounded_dom₂ Bu Bx hB hFconv hFcl hmem
    (concaveConvexFn_lowerSimpleExt hC hK) (properSaddleFn_lowerSimpleExt hCne hDne)
    (saddleStructure_lowerSimpleExt hC hCcl hDcl hCne hDne hK hcontD hcontC)
    (by rw [dom₂_lowerSimpleExt (K := K) hCne]; exact hbd)

/-- Let $U$, $V$, $X$ and $Y$ be finite-dimensional normed spaces, let both pairings be compatible
on both sides, and let the pairing of $U$ with $V$ separate the points of $U$. Let
$C \subseteq U$ be nonempty, closed, convex and bounded, let $D \subseteq Y$ be nonempty and
closed, and let $K : U \times Y \to \mathbb{R}$ be concave-convex on $C \times D$ and continuous
in each variable separately on $C$ and on $D$. Then $$\sup_{u \in C} \inf_{x \in D} K(u, x) =
\inf_{x \in D} \sup_{u \in C} K(u, x)$$ as extended real numbers. This is Corollary 37.3.2 of
[rockafellar1970convex], the case where $C$ is bounded. -/
theorem biSup_biInf_eq_biInf_biSup_of_isBounded_left (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip] (hB : Bu.SeparatingLeft)
    (hC : Convex ℝ C) (hCcl : IsClosed C) (hDcl : IsClosed D) (hCne : C.Nonempty)
    (hDne : D.Nonempty) (hK : ConcaveConvexOn C D K)
    (hcontD : ∀ u ∈ C, ContinuousOn (fun x => K (u, x)) D)
    (hcontC : ∀ x ∈ D, ContinuousOn (fun u => K (u, x)) C)
    (hbd : Bornology.IsBounded C) :
    (⨆ u ∈ C, ⨅ x ∈ D, ((K (u, x) : ℝ) : EReal))
      = ⨅ x ∈ D, ⨆ u ∈ C, ((K (u, x) : ℝ) : EReal) := by
  obtain ⟨F, hFconv, hFcl, hmem⟩ := exists_bifunSaddleClass_lowerSimpleExt Bu Bx hC hCcl hDcl
    hCne hDne hK hcontD hcontC
  refine biSup_biInf_eq_biInf_biSup_of_hasSaddleValue_lowerSimpleExt hC hCcl hDcl hCne hDne hK
    hcontD hcontC ?_
  exact hasSaddleValue_of_isBounded_dom₁ Bu Bx hB hFconv hFcl hmem
    (concaveConvexFn_lowerSimpleExt hC hK) (properSaddleFn_lowerSimpleExt hCne hDne)
    (saddleStructure_lowerSimpleExt hC hCcl hDcl hCne hDne hK hcontD hcontC)
    (by rw [dom₁_lowerSimpleExt (K := K) hDne]; exact hbd)

/-- The **minimax theorem**. Let $U$, $V$, $X$ and $Y$ be finite-dimensional normed spaces, let both
pairings be compatible on both sides, let the pairing of $U$ with $V$ separate the points of
$U$, and let the pairing of $X$ with $Y$ separate the points of $Y$. Let $C \subseteq U$ be
nonempty, closed, convex and bounded, let $D \subseteq Y$ be nonempty, closed and bounded, and
let $K : U \times Y \to \mathbb{R}$ be concave-convex on $C \times D$ and continuous in each
variable separately on $C$ and on $D$. Then $K$ has a saddle-point relative to $C \times D$:
there are $\bar u \in C$ and $\bar x \in D$ with $$K(u, \bar x) \le K(\bar u, \bar x) \le K(\bar
u, x) \quad \text{for all } u \in C,\ x \in D.$$ This is Corollary 37.6.2 of
[rockafellar1970convex].

In finite dimensions $C$ and $D$ are compact. The criterion for bounded effective domains gives
the lower simple extension a saddle-point, this saddle-point lies in $C \times D$, and there the
extension agrees with $K$. -/
theorem exists_saddlePoint_of_isBounded (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu]
    [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx]
    [IsCompatiblePairing Bx.flip] (hBu : Bu.SeparatingLeft) (hBx : Bx.SeparatingRight)
    (hC : Convex ℝ C) (hCcl : IsClosed C) (hDcl : IsClosed D) (hCne : C.Nonempty)
    (hDne : D.Nonempty) (hK : ConcaveConvexOn C D K)
    (hcontD : ∀ u ∈ C, ContinuousOn (fun x => K (u, x)) D)
    (hcontC : ∀ x ∈ D, ContinuousOn (fun u => K (u, x)) C)
    (hbdC : Bornology.IsBounded C) (hbdD : Bornology.IsBounded D) :
    ∃ q : U × Y, q.1 ∈ C ∧ q.2 ∈ D ∧
      (∀ u ∈ C, K (u, q.2) ≤ K q) ∧ ∀ x ∈ D, K q ≤ K (q.1, x) := by
  obtain ⟨F, hFconv, hFcl, hmem⟩ := exists_bifunSaddleClass_lowerSimpleExt Bu Bx hC hCcl hDcl
    hCne hDne hK hcontD hcontC
  have hp : ProperSaddleFn (lowerSimpleExt C D K) := properSaddleFn_lowerSimpleExt hCne hDne
  obtain ⟨q, hq⟩ := exists_isSaddlePoint_of_isBounded_domSaddle Bu Bx hBu hBx hFconv hFcl hmem
    (concaveConvexFn_lowerSimpleExt hC hK) hp
    (saddleStructure_lowerSimpleExt hC hCcl hDcl hCne hDne hK hcontD hcontC)
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

/-! ### The subdifferential of a saddle-function as a partially inverted subdifferential -/

section GraphSubdifferential

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]

/-- For $a, b \in [-\infty, +\infty]$ and real $c, d, e$ with $e = c - d$, the equation $-b = e - a$
holds if and only if $a - c = b - d$. -/
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
  · exact EReal.add_coe_right_cancel (hkey.trans h.symm)

/-- Let $F$ be a bifunction from $U$ to $X$, with pairings $\langle u, v \rangle$ of $U$ with $V$
and $\langle x, y \rangle$ of $X$ with $Y$, and let $f(u, x) = (Fu)(x)$ be its graph function.
For $(u, y) \in U \times Y$ and $(v, x) \in V \times X$, $$(Fu)(x) - \langle x, y \rangle = (F^*
y)(v) - \langle u, v \rangle$$ if and only if $(-v, y) \in \partial f(u, x)$, the
subdifferential taken with respect to the product pairing of $U \times X$ with $V \times Y$.

No hypothesis on $F$ is needed. The proof combines the conjugate criterion for a subgradient
with the identity $(F^* y)(v) = -f^*(-v, y)$, which holds for every $F$. The equation on the
left is the condition that `ConvexAnalysis.IsBifunSubgradientPair` names, and it describes
membership of $(v, x)$ in $\partial K(u, y)$ for every $K \in \Omega(F)$. -/
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

/-- **The graph of $\partial K$ is the graph of $\partial f$ partially inverted.** Let $U$, $V$, $X$
and $Y$ be normed spaces, let both pairings be compatible on both sides, let $F$ be a closed
convex bifunction from $U$ to $X$ with graph function $f$, and let $K \in \Omega(F)$. Then
$(v, x) \in \partial K(u, y)$ if and only if $(-v, y) \in \partial f(u, x)$. Equivalently, the
graph of $\partial K$ is the preimage of the graph of $\partial f$ under the map
$((u, y), (v, x)) \mapsto ((u, x), (-v, y))$.

Here $\partial K(u, y)$ is the product of the supergradients of $K(\cdot, y)$ at $u$ and the
subgradients of $K(u, \cdot)$ at $y$. The partial inversion is a linear homeomorphism, so
closedness and maximal monotonicity transfer from $\partial f$ to $\partial K$. -/
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

/-- Let $U$, $V$, $X$ and $Y$ be normed spaces, let both pairings be compatible on both sides and
jointly continuous, and let $F$ be a closed convex bifunction from $U$ to $X$ whose graph
function is proper. If $K \in \Omega(F)$, then the graph $\{((u, y), (v, x)) \mid (v, x) \in
\partial K(u, y)\}$ of $\partial K$ is closed. This is part of Corollary 37.5.1 of
[rockafellar1970convex].

The graph is the preimage of the graph of $\partial f$ under a linear homeomorphism, and the
graph of the subdifferential of a closed proper convex function is closed. The homeomorphism
part of the corollary is `ConvexAnalysis.saddleSubdifferentialHomeomorph`. -/
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
