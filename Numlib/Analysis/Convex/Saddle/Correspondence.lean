/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Extremum.Normal
import Numlib.Analysis.Convex.Saddle.Closure

/-!
# The correspondence between saddle-functions and bifunctions

Let $U$ be paired with $V$ and $X$ with $Y$. A convex bifunction $F$ from $U$ to $X$ has two
brackets, the lower bracket $\langle Fu, y \rangle = (Fu)^*(y)$ and the upper bracket
$\langle u, F^* y \rangle$, the concave bracket of the adjoint $F^*$. For a closed convex $F$ they
satisfy $\operatorname{cl}_1 \langle Fu, y \rangle = \langle u, F^* y \rangle$ and
$\operatorname{cl}_2 \langle u, F^* y \rangle = \langle Fu, y \rangle$. The lower bracket sets up a
one-to-one correspondence between the closed convex bifunctions from $U$ to $X$ and the lower closed
concave-convex functions on $U \times Y$, with inverse $K \mapsto (u \mapsto K(u, \cdot)^*)$. This
is Theorem 33.3 of [rockafellar1970convex], and the rest of the theory of saddle-functions is built
on it. The presentation follows [rockafellar1970convex], §33.

Three refinements follow. First, the correspondence remains a bijection if closedness is weakened to
image-closedness (each $Fu$ closed) on the side of bifunctions and to closedness in the second
variable on the side of functions. Second, the closure pairs $(\underline{K}, \overline{K})$, with
$\operatorname{cl}_1 \underline{K} = \overline{K}$ and $\operatorname{cl}_2 \overline{K} =
\underline{K}$, are exactly the pairs of brackets of a closed convex bifunction. Third,
$\operatorname{cl}_1$ and $\operatorname{cl}_2$ are inverse bijections between the lower closed and
the upper closed concave-convex functions. The first refinement has a polyhedral form, in which
properness takes the place of closedness.

## Main definitions

* `ConvexAnalysis.saddleOfBifun`: the lower bracket $(u, y) \mapsto \langle Fu, y \rangle$ as a
  function on $U \times Y$.
* `ConvexAnalysis.bifunSaddleEquiv`: the bijection between the image-closed convex bifunctions and
  the concave-convex functions closed in the second variable.
* `ConvexAnalysis.lowerUpperClosedEquiv`: $\operatorname{cl}_1$ and $\operatorname{cl}_2$ as inverse
  bijections between the lower closed and the upper closed concave-convex functions.

## Main results

* `ConvexAnalysis.eq_of_bracket_eq`: two image-closed convex bifunctions with the same lower bracket
  are equal. This is why image-closedness needs a name: the bracket
  $\langle Fu, \cdot \rangle = (Fu)^*$ sees only $\operatorname{cl} (Fu)$.
* `ConvexAnalysis.lowerClosedFn_bracket`, `ConvexAnalysis.exists_unique_convexBifun_bracket_eq`: the
  lower bracket of a closed convex bifunction is lower closed, and every lower closed concave-convex
  function is the lower bracket of exactly one closed convex bifunction. This is Theorem 33.3 of
  [rockafellar1970convex].
* `ConvexAnalysis.exists_unique_bifun_of_closure_pair`: a closure pair is the pair of brackets of
  exactly one closed convex bifunction; `ConvexAnalysis.le_of_partialCl₂_eq` adds
  $\underline{K} \le \overline{K}$.
* `ConvexAnalysis.polyhedralFn_bracket`, `ConvexAnalysis.polyhedralFn_neg_bracket`,
  `ConvexAnalysis.imageClosedBifun_of_polyhedralBifun`,
  `ConvexAnalysis.eq_convexConj_bracket_of_polyhedralBifun`: for a polyhedral convex bifunction the
  lower bracket is polyhedral in each variable, and a proper polyhedral convex bifunction is
  recovered from its lower bracket.

## Implementation notes

* For a lower closed $K$, the bifunction $F u = K(u, \cdot)^*$ (`ConvexAnalysis.bifunOfSaddle`) has
  the right bracket at once, but its closedness needs an argument: $\operatorname{cl} F$ and $F$ are
  both image-closed and convex and have the same bracket, so they are equal.
-/

namespace ConvexAnalysis

/-! ### The bracket is injective on image-closed convex bifunctions -/

section Injective

variable {U X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]
  [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace X] [IsTopologicalAddGroup X]
  [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X] {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ}
  [IsCompatiblePairing Bx] {F G : Bifun U X}

/-- Let $X$ be a locally convex space paired with $Y$ by a compatible pairing. If $F$ and $G$ are
convex bifunctions from $U$ to $X$, both image-closed (each $Fu$ and each $Gu$ is a closed
function), and $\langle Fu, y \rangle = \langle Gu, y \rangle$ for all $u$ and $y$, then
$F = G$.

The bracket $\langle Fu, \cdot \rangle = (Fu)^*$ sees only $\operatorname{cl} (Fu)$, and
image-closedness says that $\operatorname{cl} (Fu) = Fu$. -/
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
/-- Let $U$ be a locally convex space paired with $V$ by a compatible pairing, let $X$ be paired
with $Y$, and let $F$ be a convex bifunction from $U$ to $X$. Then the concave closure in the
first variable of the lower bracket is the upper bracket:
$$\operatorname{cl}_1 \langle Fu, y \rangle = \langle u, F^* y \rangle.$$
-/
theorem partialCl₁_bracket (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu]
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (hF : ConvexBifun F) :
    partialCl₁ (fun p : U × Y => bracket Bx F p.1 p.2)
      = fun p : U × Y => concaveBracket Bu (convexAdjointBifun Bu Bx F) p.1 p.2 := by
  funext p
  exact (congrFun (concaveBracket_convexAdjointBifun_eq_partialCl₁ (Bu := Bu) hF p.2) p.1).symm

/-- Let $U$, $X$ and $Y$ be locally convex spaces, with $U$ paired with $V$ and $X$ with $Y$, where
the pairings are compatible with the topologies of $U$, $X$ and $Y$. If $F$ is a closed convex
bifunction from $U$ to $X$, then the convex closure in the second variable of the upper bracket
is the lower bracket:
$$\operatorname{cl}_2 \langle u, F^* y \rangle = \langle Fu, y \rangle.$$
Together with `ConvexAnalysis.partialCl₁_bracket` this says that the two brackets of a closed
convex bifunction form a closure pair. -/
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

/-- Let $U$, $X$ and $Y$ be locally convex spaces, with $U$ paired with $V$ and $X$ with $Y$, where
the pairings are compatible with the topologies of $U$, $X$ and $Y$. If $F$ is a closed convex
bifunction from $U$ to $X$, then its lower bracket $(u, y) \mapsto \langle Fu, y \rangle$ is
lower closed:
$$\operatorname{cl}_2 \operatorname{cl}_1 \langle Fu, y \rangle = \langle Fu, y \rangle.$$
This is one direction of Theorem 33.3 of [rockafellar1970convex].

Each closure step exchanges the two brackets, and the loop closes because
$F^{**} = \operatorname{cl} F = F$. -/
theorem lowerClosedFn_bracket (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu]
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip]
    (hF : ConvexBifun F) (hcl : ClosedConvexBifun F) :
    LowerClosedFn (fun p : U × Y => bracket Bx F p.1 p.2) := by
  rw [lowerClosedFn_iff, lowerCl_def, partialCl₁_bracket Bu Bx hF,
    partialCl₂_concaveBracket_adjoint Bu Bx hF hcl]

/-- Let $U$, $X$ and $Y$ be locally convex spaces, with $U$ paired with $V$ and $X$ with $Y$, where
the pairings are compatible with the topologies of $U$, $X$ and $Y$. If
$K : U \times Y \to [-\infty, +\infty]$ is concave-convex and lower closed, then there is
exactly one closed convex bifunction $F$ from $U$ to $X$ with
$$\langle Fu, y \rangle = K(u, y) \quad \text{for all } (u, y) \in U \times Y.$$
This is the other direction of Theorem 33.3 of [rockafellar1970convex].

The bifunction is $F u = K(u, \cdot)^*$, which is `ConvexAnalysis.bifunOfSaddle`. -/
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

/-- Let $Y$ be a topological space and let $\underline{K}, \overline{K} : U \times Y \to [-\infty,
+\infty]$. If $\operatorname{cl}_2 \overline{K} = \underline{K}$, then
$\underline{K} \le \overline{K}$. In particular a closure pair is ordered. Only this relation is
needed, because $\operatorname{cl}_2$ lowers a function. -/
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

/-- Let $U$, $X$ and $Y$ be locally convex spaces, with $U$ paired with $V$ and $X$ with $Y$, where
the pairings are compatible with the topologies of $U$, $X$ and $Y$. Let $\underline{K},
\overline{K} : U \times Y \to [-\infty, +\infty]$, with $\underline{K}$ concave-convex, form a
closure pair: $\operatorname{cl}_1 \underline{K} = \overline{K}$ and $\operatorname{cl}_2
\overline{K} = \underline{K}$. Then there is exactly one closed convex bifunction $F$ from $U$
to $X$ whose two brackets are the pair:
$$\langle Fu, y \rangle = \underline{K}(u, y), \qquad \langle u, F^* y \rangle
  = \overline{K}(u, y).$$

Conversely, the two brackets of a closed convex bifunction form a closure pair, by
`ConvexAnalysis.partialCl₁_bracket` and `ConvexAnalysis.partialCl₂_concaveBracket_adjoint`. So
the closure pairs are exactly the pairs of brackets of closed convex bifunctions. -/
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

/-!
### The correspondence under image-closedness

The two round trips are the two halves of the bracket construction. Each needs the closedness
hypothesis on its own side: image-closedness of $F$, and closedness of $K$ in the second variable.
-/

section SaddleOfBifun

variable {U X Y : Type*} [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]

/-- The **saddle-function of a bifunction**: for a bifunction $F$ from $U$ to $X$ and a pairing of
$X$ with $Y$, the function $(u, y) \mapsto \langle Fu, y \rangle = (Fu)^*(y)$ on $U \times Y$.

This is `ConvexAnalysis.bracket` in uncurried form. It has a name because the correspondence is
a statement about it as a map. -/
noncomputable def saddleOfBifun (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (F : Bifun U X) : U × Y → EReal :=
  fun p => bracket Bx F p.1 p.2

/-- The saddle-function of $F$ takes the value $\langle Fu, y \rangle$ at $(u, y)$. -/
theorem saddleOfBifun_apply (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (F : Bifun U X) (p : U × Y) :
    saddleOfBifun Bx F p = bracket Bx F p.1 p.2 := rfl

end SaddleOfBifun

section SaddleOfBifunClosed

variable {U X Y : Type*} [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace Y] [IsTopologicalAddGroup Y] {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ}
  [IsContinuousPairing Bx.flip] {F : Bifun U X}

/-- If the pairing of $X$ with $Y$ is continuous in $y$, the saddle-function of any bifunction is
closed in the second variable, because every slice $\langle Fu, \cdot \rangle$ is a conjugate. -/
theorem partialClosed₂_saddleOfBifun : PartialClosed₂ (saddleOfBifun Bx F) :=
  partialClosed₂_iff.2 fun u => closedConvex_bracket u

end SaddleOfBifunClosed

section SaddleOfBifunConvex

variable {U X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]
  [AddCommGroup Y] [Module ℝ Y] {F : Bifun U X}

/-- The saddle-function $(u, y) \mapsto \langle Fu, y \rangle$ of a convex bifunction is
concave-convex. -/
theorem concaveConvexFn_saddleOfBifun (hF : ConvexBifun F) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) :
    ConcaveConvexFn (saddleOfBifun Bx F) := concaveConvexFn_bracket hF Bx

end SaddleOfBifunConvex

section BifunOfSaddleImage

variable {U X Y : Type*} [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace X] [IsTopologicalAddGroup X] {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ}
  [IsContinuousPairing Bx] {K : U × Y → EReal}

/-- If the pairing of $X$ with $Y$ is continuous in $x$, the bifunction $F u = K(u, \cdot)^*$ of any
function $K$ on $U \times Y$ is image-closed, because every $F u$ is a conjugate. -/
theorem imageClosedBifun_bifunOfSaddle : ImageClosedBifun (bifunOfSaddle Bx K) :=
  fun u => closedConvex_convexConj (B := Bx.flip) (f := fun y => K (u, y))

end BifunOfSaddleImage

section RoundTripRight

variable {U X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]
  [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y]
  [ContinuousSMul ℝ Y] [LocallyConvexSpace ℝ Y] {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ}
  [IsCompatiblePairing Bx.flip] {K : U × Y → EReal}

/-- Let $Y$ be a locally convex space paired with $X$ by a compatible pairing. If $K$ is
concave-convex on $U \times Y$ and closed in the second variable, then $K$ is the
saddle-function of its bifunction: $\langle Fu, y \rangle = K(u, y)$ for $F u = K(u, \cdot)^*$. -/
theorem saddleOfBifun_bifunOfSaddle (hK : ConcaveConvexFn K) (hcc : PartialClosed₂ K) :
    saddleOfBifun Bx (bifunOfSaddle Bx K) = K :=
  funext fun p => (bracket_bifunOfSaddle hK p).trans (congrFun hcc p)

end RoundTripRight

section RoundTripLeft

variable {U X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]
  [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace X] [IsTopologicalAddGroup X]
  [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X] {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ}
  [IsCompatiblePairing Bx] {F : Bifun U X}

/-- Let $X$ be a locally convex space paired with $Y$ by a compatible pairing. If $F$ is an
image-closed convex bifunction from $U$ to $X$, then $F$ is the bifunction of its
saddle-function: $F u = \langle Fu, \cdot \rangle^*$ for every $u$. -/
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

/-- Let $X$ and $Y$ be locally convex spaces paired by a pairing compatible with both topologies.
The maps $F \mapsto \bigl((u, y) \mapsto \langle Fu, y \rangle\bigr)$ and
$K \mapsto \bigl(u \mapsto K(u, \cdot)^*\bigr)$ are inverse bijections between the image-closed
convex bifunctions from $U$ to $X$ and the concave-convex functions on $U \times Y$ that are
closed in the second variable.

This is the correspondence of `ConvexAnalysis.exists_unique_convexBifun_bracket_eq` with
closedness weakened on both sides. -/
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

/-!
### The bracket of a polyhedral bifunction

For a polyhedral convex bifunction, both variables of the lower bracket become polyhedral instead of
merely convex or concave. Properness does the work that closedness does in the general
correspondence: $F$ is recovered from its bracket with no closedness hypothesis. A polyhedral
concave function $g$ is expressed as `ConvexAnalysis.PolyhedralFn` of $-g$, since there is no
predicate for a polyhedral hypograph.
-/

section PolyhedralLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → EReal}

/-- Adding a linear functional preserves polyhedrality: if $f$ is a polyhedral convex function on
$E$ and $\varphi$ is a linear functional on $E$, then $f + \varphi$ is polyhedral convex.

The epigraph of $f + \varphi$ is the preimage of the epigraph of $f$ under the shear
$(x, \mu) \mapsto (x, \mu - \varphi(x))$. This needs only the structure of a real vector space,
with no finite dimension and no topology. -/
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
/-- Let $X$ be a finite-dimensional real normed space paired with $Y$, and let $F$ be a polyhedral
convex bifunction from $U$ to $X$. For every $u$, the function $y \mapsto \langle Fu, y \rangle$
is polyhedral convex. It is the conjugate of the slice $Fu$, which is itself polyhedral. -/
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

/-- Let $U$ and $X$ be finite-dimensional real normed spaces, with $X$ paired with $Y$, and let $F$
be a polyhedral convex bifunction from $U$ to $X$. For every $y$, the function
$u \mapsto \langle Fu, y \rangle$ is polyhedral concave: $u \mapsto -\langle Fu, y \rangle$ is
polyhedral convex.

The function $-\langle Fu, y \rangle = \inf_x \{(Fu)(x) - \langle x, y \rangle\}$ is the image
of a polyhedral convex function on $U \times X$ under the projection $(u, x) \mapsto u$, and
such an image is polyhedral. -/
theorem polyhedralFn_neg_bracket (hF : PolyhedralBifun F) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (y : Y) :
    PolyhedralFn (fun u => -(bracket Bx F u y)) :=
  polyhedralFn_neg_bracket_aux hF Bx y ((-(Bx.flip y)).comp (LinearMap.snd ℝ U X)) fun _ => rfl

omit [FiniteDimensional ℝ U] in
/-- Let $X$ be a finite-dimensional real normed space and let $F$ be a polyhedral convex bifunction
from $U$ to $X$ whose graph function is proper. Then $F$ is image-closed: each $Fu$ is a closed
function.

Each slice has a closed epigraph, and properness keeps it from taking the value $-\infty$. This
is the polyhedral substitute for the closedness hypothesis of the correspondence. -/
theorem imageClosedBifun_of_polyhedralBifun (hF : PolyhedralBifun F)
    (hp : ProperConvex (graphFn F)) :
    ImageClosedBifun F := fun u =>
  PolyhedralFn.closedConvex (PolyhedralBifun.polyhedralFn_apply hF u) fun x => hp.ne_bot (u, x)

omit [FiniteDimensional ℝ U] in
/-- Let $X$ be a finite-dimensional real normed space paired with $Y$ by a compatible pairing, and
let $F$ be a polyhedral convex bifunction from $U$ to $X$ whose graph function is proper. Then
$F$ is recovered from its lower bracket: for every $u$,
$$Fu = \langle Fu, \cdot \rangle^*.$$
-/
theorem eq_convexConj_bracket_of_polyhedralBifun (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx]
    (hF : PolyhedralBifun F) (hp : ProperConvex (graphFn F)) (u : U) :
    F u = convexConj Bx.flip (bracket Bx F u) :=
  (imageClosedBifun_of_polyhedralBifun hF hp u).symm.trans
    (convexCl_eq_convexConj_bracket (PolyhedralBifun.convexBifun hF) u)

omit [FiniteDimensional ℝ U] in
/-- Let $X$ be a finite-dimensional real normed space paired with $Y$ by a compatible pairing, and
let $F$ be a polyhedral convex bifunction from $U$ to $X$ whose graph function is proper. Then
for all $u$ and $x$
$$(Fu)(x) = \sup_y \{\langle x, y \rangle - \langle Fu, y \rangle\}.$$
This is `ConvexAnalysis.eq_convexConj_bracket_of_polyhedralBifun` with the conjugate written
out. -/
theorem eq_iSup_sub_bracket_of_polyhedralBifun (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bx] (hF : PolyhedralBifun F) (hp : ProperConvex (graphFn F)) (u : U)
        (x : X) :
    F u x = ⨆ y : Y, ((Bx x y : ℝ) : EReal) - bracket Bx F u y :=
  congrFun (eq_convexConj_bracket_of_polyhedralBifun Bx hF hp u) x

end PolyhedralBracket

/-!
### The bracket of the adjoint of a polyhedral bifunction

The adjoint of a polyhedral convex bifunction is polyhedral concave, and its concave bracket is
polyhedral convex in $y$. A polyhedral function agrees with its closure throughout its effective
domain. Together these facts extend the equality of the two brackets from the relative interior of
an effective domain to all of it.
-/

section PolyhedralConcaveClosure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {g : E → EReal}

/-- Let $E$ be a finite-dimensional real normed space and let $g$ be a polyhedral concave function
on $E$, that is $-g$ is polyhedral convex. Then $g$ agrees with its concave closure throughout
its effective domain, not only on the relative interior: $(\operatorname{cl} g)(x) = g(x)$
whenever $g(x) > -\infty$.

This is the mirror of `ConvexAnalysis.PolyhedralFn.convexCl_eq_of_mem_convexDom`, obtained by
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

/-- Let $U$ and $X$ be finite-dimensional real normed spaces. A polyhedral convex bifunction from
$U$ to $X$ whose graph function is proper is closed. Its graph function has a polyhedral, hence
closed, epigraph, and properness rules out the value $-\infty$ of the closure. -/
theorem closedConvexBifun_of_polyhedralBifun (hF : PolyhedralBifun F)
    (hp : ProperConvex (graphFn F)) :
    ClosedConvexBifun F := PolyhedralFn.closedConvex hF hp.ne_bot

/-- Let $U$ and $X$ be finite-dimensional real normed spaces, with $U$ paired with $V$ and $X$ with
$Y$. The adjoint $F^*$ of a polyhedral convex bifunction $F$ from $U$ to $X$ is polyhedral
concave: the function $(y, v) \mapsto -(F^* y)(v)$ on $Y \times V$ is polyhedral convex.

The function $-F^*$ is the conjugate of the graph function of $F$ composed with the map
$(y, v) \mapsto (-v, y)$. Neither properness nor closedness is needed, as in the proof that the
adjoint is concave. -/
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

/-- For every bifunction $G$ from $Y$ to $V$, every pairing of $U$ with $V$ and every $u$, the
effective domain of $y \mapsto \langle u, G y \rangle$ is $\operatorname{dom} G = \{y \mid (G
y)(v) > -\infty \text{ for some } v\}$. The concave bracket is $+\infty$ exactly where the slice
$G y$ is identically $-\infty$. This is the mirror of `ConvexAnalysis.concaveDom_bracket`. -/
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

/-- Let $V$ and $Y$ be finite-dimensional real normed spaces, with $U$ paired with $V$, and let $G$
be a polyhedral concave bifunction from $Y$ to $V$, that is $(y, v) \mapsto -(G y)(v)$ is
polyhedral convex. Then for every $u$, the concave bracket $y \mapsto \langle u, G y \rangle$ is
polyhedral convex.

The bracket $\langle u, G y \rangle = \inf_v \{\langle u, v \rangle - (G y)(v)\}$ is the image
of a polyhedral convex function on $Y \times V$ under the projection $(y, v) \mapsto y$, and
such an image is polyhedral. -/
theorem polyhedralFn_concaveBracket (hG : PolyhedralFn fun q : Y × V => -(graphFn G q))
    (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (u : U) : PolyhedralFn (fun y => concaveBracket Bu G u y) :=
  polyhedralFn_concaveBracket_aux hG Bu u ((Bu u).comp (LinearMap.snd ℝ Y V)) fun _ => rfl

end PolyhedralConcaveBracket

/-! ### The two closures as inverse bijections -/

section ClosureBijection

variable {U Y : Type*} [TopologicalSpace U] [TopologicalSpace Y] {K : U × Y → EReal}

/-- If $K$ is lower closed, then $\operatorname{cl}_1 K$ is upper closed. -/
theorem upperClosedFn_partialCl₁ (h : LowerClosedFn K) : UpperClosedFn (partialCl₁ K) := by
  change partialCl₁ (partialCl₂ (partialCl₁ K)) = partialCl₁ K
  rw [← lowerCl_def, lowerClosedFn_iff.1 h]

/-- If $K$ is upper closed, then $\operatorname{cl}_2 K$ is lower closed. -/
theorem lowerClosedFn_partialCl₂ (h : UpperClosedFn K) : LowerClosedFn (partialCl₂ K) := by
  change partialCl₂ (partialCl₁ (partialCl₂ K)) = partialCl₂ K
  rw [← upperCl_def, upperClosedFn_iff.1 h]

/-- If $K$ is lower closed, then $\operatorname{cl}_2 \operatorname{cl}_1 K = K$. -/
theorem partialCl₂_partialCl₁_of_lowerClosedFn (h : LowerClosedFn K) :
    partialCl₂ (partialCl₁ K) = K := h

/-- If $K$ is upper closed, then $\operatorname{cl}_1 \operatorname{cl}_2 K = K$. -/
theorem partialCl₁_partialCl₂_of_upperClosedFn (h : UpperClosedFn K) :
    partialCl₁ (partialCl₂ K) = K := h

end ClosureBijection

section ClosureEquiv

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  [TopologicalSpace Y] [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y] [LocallyConvexSpace ℝ Y]

/-- Let $U$ and $Y$ be locally convex spaces, with $U$ paired with $V$ and $X$ with $Y$, where the
pairings are compatible with the topologies of $U$ and $Y$. The maps $\overline{K} =
\operatorname{cl}_1 \underline{K}$ and $\underline{K} = \operatorname{cl}_2 \overline{K}$ are
inverse bijections between the lower closed and the upper closed concave-convex functions on
$U \times Y$.

The two round trips are the definitions of lower closed and upper closed functions. The content
is that each operator maps one class into the other and preserves concave-convexity. -/
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

