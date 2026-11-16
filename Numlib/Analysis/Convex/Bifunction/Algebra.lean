/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Duality.Exact
import Numlib.Analysis.Convex.Duality.Ops
import Numlib.Analysis.Convex.Extremum.Fenchel
import Numlib.Analysis.Convex.Saddle.Defs

/-!
# The algebra of bifunctions

A bifunction $F$ from $U$ to $X$ assigns to each $u \in U$ a function
$Fu : X \to [-\infty, +\infty]$. The adjoint $F^*$ of a convex bifunction generalizes the adjoint of
a linear transformation. This module generalizes the rest of linear algebra to bifunctions:
addition, scalar multiplication, application to a vector, composition and the inner product. For
each operation it describes how the operation behaves under taking adjoints. The presentation
follows [rockafellar1970convex], §38.

The main identities are $(F_1 \mathbin{\square} F_2)^* = F_1^* \mathbin{\square} F_2^*$ for the
analogue of a sum, $(F \lambda)^* = F^* \lambda$ for a scalar multiple, $(Ff)^* = F_*^* f^*$ for the
image of a convex function, and $(GF)^* = F^* G^*$ for a product. Each identity holds under a
qualification condition that makes a convex conjugate of a sum exact. For closed proper convex
arguments, each operation gives a closed bifunction, its defining extremum is attained, and the
adjoint of the result is the closure of the corresponding product or convolution.

## Main definitions

* `ConvexAnalysis.infConvBifun` and `ConvexAnalysis.supConvBifun`: the infimal convolute
  $F_1 \mathbin{\square} F_2$ of convex bifunctions and the supremal convolute of concave
  bifunctions, in the second variable.
* `ConvexAnalysis.infConvFstBifun`: the infimal convolute $H_1 \boxdot H_2$ in the first variable.
* `ConvexAnalysis.smulRightBifun`: the right scalar multiple $F \lambda$.
* `ConvexAnalysis.imageBifun` and `ConvexAnalysis.concaveImageBifun`: the image $Ff$ of a function
  under a bifunction.
* `ConvexAnalysis.compBifun` and `ConvexAnalysis.concaveCompBifun`: the product $GF$ of convex
  bifunctions and of concave bifunctions.
* `ConvexAnalysis.fenchelSup`, `ConvexAnalysis.fenchelInf`, `ConvexAnalysis.HasFenchelPairing` and
  `ConvexAnalysis.fenchelPairing`: the two sides of Rockafellar's inner product
  $\langle f, g \rangle$ of a convex and a concave function, the condition that they agree, and the
  common value.

## Main results

* `ConvexAnalysis.convexAdjointBifun_infConvBifun`: $(F_1 \mathbin{\square} F_2)^* = F_1^*
  \mathbin{\square} F_2^*$, the right side a supremal convolute.
  `ConvexAnalysis.bracket_infConvBifun` is the identity of inner products behind it, and
  `ConvexAnalysis.concaveAdjointBifun_supConvBifun` and `ConvexAnalysis.concaveBracket_supConvBifun`
  are the concave halves. These are Theorems 38.1–38.2 of [rockafellar1970convex].
* `ConvexAnalysis.convexAdjointBifun_smulRightBifun`: $(F \lambda)^* = F^* \lambda$ for
  $\lambda > 0$.
* `ConvexAnalysis.convexConj_imageBifun` and `ConvexAnalysis.exists_convexConj_imageBifun_eq`:
  $(Ff)^* = F_*^* f^*$, and the infimum is attained. This is Theorem 38.4 of
  [rockafellar1970convex]. `ConvexAnalysis.convexConj_imageBifun_of_bracket_eq_top` is the
  degenerate case $y \notin \operatorname{dom} F^*$.
* `ConvexAnalysis.inverseBifun_compBifun`, `ConvexAnalysis.convexAdjointBifun_compBifun` and
  `ConvexAnalysis.lowerAdjointBifun_compBifun`: $(GF)_* = F_* G_*$, $(GF)^* = F^* G^*$ with the
  supremum attained, and $(GF)_*^* = G_*^* F_*^*$. This is Theorem 38.5 of [rockafellar1970convex].
  `ConvexAnalysis.lowerAdjointBifun_infConvFstBifun` is $(H_1 \boxdot H_2)_*^* = H_{1*}^*
  \mathbin{\square} H_{2*}^*$.
* `ConvexAnalysis.closedConvexBifun_compBifun` and `ConvexAnalysis.closedConvexBifun_infConvBifun`:
  for closed proper convex arguments the product and the infimal convolute are closed.
  `ConvexAnalysis.lowerAdjointBifun_compBifun_eq_convexClBifun`,
  `ConvexAnalysis.lowerAdjointBifun_infConvBifun_eq_convexClBifun` and
  `ConvexAnalysis.convexConj_imageBifun_eq_convexCl` give the adjoint of the result as a closure.
* `ConvexAnalysis.fenchelSup_le_fenchelInf`: weak duality for the inner product, with no hypothesis.
* `ConvexAnalysis.fenchelPairing_convexConj`: conjugation reverses the inner product, $\langle f^*,
  g^* \rangle = -\langle f, g \rangle$.
* `ConvexAnalysis.convexConj_imageBifun_eq_fenchelPairing` and
  `ConvexAnalysis.bracket_compBifun_eq_fenchelPairing`: an adjoint moves across the inner product,
  $\langle Ff, y \rangle = \langle f, F^* y \rangle$ and $\langle (GF) u, z \rangle = \langle Fu,
  G^* z \rangle$. These are Corollary 38.7.1 and the first equality of Corollary 38.7.2 of
  [rockafellar1970convex].
* `ConvexAnalysis.fenchelInf_imageBifun_eq_fenchelInf_concaveImageBifun`: $\langle Ff, g^* \rangle =
  \langle f, F^* g^* \rangle$, with `ConvexAnalysis.fenchelSup_imageBifun_lowerAdjointBifun` as the
  main step. This is Theorem 38.7 of [rockafellar1970convex].

## Notation

* $\langle u, v \rangle$ is the pairing `Bu` of $U$ and $V$, and $\langle x, y \rangle$ is the
  pairing `Bx` of $X$ and $Y$. Further pairings `By` of $Y$ and $Z$, and `Bx` of $X$ and $W$, appear
  for products.
* $f^*$ is the convex conjugate $f^*(y) = \sup_x \{ \langle x, y \rangle - f(x) \}$
  (`ConvexAnalysis.convexConj`), and for a concave $g$, $g^*$ is the concave conjugate $g^*(y) =
  \inf_x \{ \langle x, y \rangle - g(x) \}$ (`ConvexAnalysis.concaveConj`).
* $\langle Fu, y \rangle = (Fu)^*(y)$ is the inner product of a convex bifunction
  (`ConvexAnalysis.bracket`), and $\langle u, Gy \rangle = \inf_v \{ \langle u, v \rangle - (Gy)(v)
  \}$ that of a concave bifunction (`ConvexAnalysis.concaveBracket`).
* $F^*$ is the adjoint of $F$, the concave bifunction from $Y$ to $V$ with $(F^* y)(v) = \inf_{u, x}
  \{ (Fu)(x) - \langle x, y \rangle + \langle u, v \rangle \}$
  (`ConvexAnalysis.convexAdjointBifun`). The adjoint of a concave bifunction, with a supremum, is
  `ConvexAnalysis.concaveAdjointBifun`.
* $F_*$ is the inverse $(F_* x)(u) = -(Fu)(x)$ (`ConvexAnalysis.inverseBifun`), and $F_*^*$ is the
  convex bifunction from $V$ to $Y$ with $(F_*^* v)(y) = -(F^* y)(v)$
  (`ConvexAnalysis.lowerAdjointBifun`).
* The operations and their linear-algebra analogues are: $F_1 \mathbin{\square} F_2$ for
  $A_1 + A_2$; $H_1 \boxdot H_2$ for the same in the first variable; $F \lambda$ for $\lambda A$;
  $Ff$ for $Ax$; $GF$ for $B A$; $F_*$ and $F_*^*$ for $A^{-1}$ and $(A^{-1})^*$; and
  $\langle f, g \rangle$ for $\langle x, y \rangle$.

## Implementation notes

* Rockafellar's hypotheses are of the form "the relative interiors of two effective domains have a
  point in common". Their consequence is that the conjugate of a sum is an exact infimal convolution
  of the conjugates. Here that consequence is the hypothesis, in the form
  `ConvexAnalysis.IsExactSum`, with one instance for each dual vector where the book has a single
  relative-interior condition. `ConvexAnalysis.IsExactSum` also demands that both summands be
  proper. So it is stronger than the book's hypothesis, and it needs no topology and no finite
  dimension.
* $F_*^*$ is `ConvexAnalysis.lowerAdjointBifun` of `Numlib.Analysis.Convex.Extremum.Adjoint`, the
  inverse of the adjoint. Working with it, and not with a second, concave adjoint, keeps the results
  of the closed case between convex bifunctions and avoids a concave closure of bifunctions. Each
  convex statement about $\square$ is followed by its concave twin about the supremal convolute
  `ConvexAnalysis.supConvBifun`.
* Rockafellar leaves $\langle f, g \rangle$ undefined when the two extrema differ. So they are kept
  apart here as `ConvexAnalysis.fenchelSup` and `ConvexAnalysis.fenchelInf`, with the predicate
  `ConvexAnalysis.HasFenchelPairing` that they agree. He also restricts the extrema to
  $\operatorname{dom} f \cap \operatorname{dom} g^*$ to avoid $\infty - \infty$. For proper $f$ and
  proper concave $g$ the excluded terms are $-\infty$ on the supremum side and $+\infty$ on the
  infimum side, so the plain supremum and infimum used here agree with his.
* Values are extended reals (`EReal`), where $a - b = a + (-b)$ and
  $(+\infty) + (-\infty) = -\infty$.
-/

open Pointwise

namespace ConvexAnalysis

/-! ### Infimal and supremal convolution of bifunctions -/

section InfConvBifunDefs

variable {U X : Type*} [AddCommGroup X]

/-- Let $U$ be a type and $X$ an additive group. The **infimal convolute**
$F_1 \mathbin{\square} F_2$ of two bifunctions $F_1, F_2$ from $U$ to $X$ is the bifunction from
$U$ to $X$ with
$$(F_1 \mathbin{\square} F_2) u = F_1 u \mathbin{\square} F_2 u,$$
the infimal convolution in the second variable, for each $u$ separately. When neither function
takes the value $-\infty$, $((F_1 \mathbin{\square} F_2) u)(x) = \inf \{ (F_1 u)(x_1) + (F_2
u)(x_2) \mid x_1 + x_2 = x \}$.

This is the bifunction analogue of the sum of two linear transformations: if $F_i$ is the convex
indicator bifunction of $A_i$, then $F_1 \mathbin{\square} F_2$ is the convex indicator
bifunction of $A_1 + A_2$. The infimal convolution of functions is `ConvexAnalysis.infConv`. -/
noncomputable def infConvBifun (F₁ F₂ : Bifun U X) : Bifun U X := fun u => infConv (F₁ u) (F₂ u)

/-- The slice of $F_1 \mathbin{\square} F_2$ at $u$ is the infimal convolution
$F_1 u \mathbin{\square} F_2 u$. -/
theorem infConvBifun_apply (F₁ F₂ : Bifun U X) (u : U) :
    infConvBifun F₁ F₂ u = infConv (F₁ u) (F₂ u) := rfl

/-- Let $U$ be a type and $X$ an additive group. The **supremal convolute**
$G_1 \mathbin{\square} G_2$ of two bifunctions $G_1, G_2$ from $U$ to $X$, the concave analogue
of `ConvexAnalysis.infConvBifun`, is the bifunction from $U$ to $X$ with
$$(G_1 \mathbin{\square} G_2) u = G_1 u \mathbin{\square} G_2 u,$$
the supremal convolution in the second variable. When neither function takes the value
$+\infty$, $((G_1 \mathbin{\square} G_2) u)(x) = \sup \{ (G_1 u)(x_1) + (G_2 u)(x_2) \mid x_1 +
x_2 = x \}$.

Rockafellar writes $\square$ for both convolutions; the orientation of the bifunction decides
which one is meant. The supremal convolution of functions is `ConvexAnalysis.supConv`. -/
noncomputable def supConvBifun (G₁ G₂ : Bifun U X) : Bifun U X := fun u => supConv (G₁ u) (G₂ u)

/-- The slice of the supremal convolute $G_1 \mathbin{\square} G_2$ at $u$ is the supremal
convolution $G_1 u \mathbin{\square} G_2 u$. -/
theorem supConvBifun_apply (G₁ G₂ : Bifun U X) (u : U) :
    supConvBifun G₁ G₂ u = supConv (G₁ u) (G₂ u) := rfl

/-- The negative of a supremal convolute is the infimal convolute of the negatives: $-(G_1
\mathbin{\square} G_2) = (-G_1) \mathbin{\square} (-G_2)$. -/
theorem neg_supConvBifun (G₁ G₂ : Bifun U X) :
    (fun u x => -(supConvBifun G₁ G₂ u x))
      = infConvBifun (fun u x => -(G₁ u x)) (fun u x => -(G₂ u x)) :=
  funext fun u => funext fun x => neg_supConv (G₁ u) (G₂ u) x

/-- The infimal convolute of bifunctions is commutative: $F_1 \mathbin{\square} F_2 = F_2
\mathbin{\square} F_1$. -/
theorem infConvBifun_comm (F₁ F₂ : Bifun U X) : infConvBifun F₁ F₂ = infConvBifun F₂ F₁ :=
  funext fun u => infConv_comm (F₁ u) (F₂ u)

/-- The supremal convolute of bifunctions is commutative: $G_1 \mathbin{\square} G_2 = G_2
\mathbin{\square} G_1$. -/
theorem supConvBifun_comm (G₁ G₂ : Bifun U X) : supConvBifun G₁ G₂ = supConvBifun G₂ G₁ :=
  funext fun u => supConv_comm (G₁ u) (G₂ u)

/-- The infimal convolute of bifunctions is associative: $(F_1 \mathbin{\square} F_2)
\mathbin{\square} F_3 = F_1 \mathbin{\square} (F_2 \mathbin{\square} F_3)$. -/
theorem infConvBifun_assoc (F₁ F₂ F₃ : Bifun U X) :
    infConvBifun (infConvBifun F₁ F₂) F₃ = infConvBifun F₁ (infConvBifun F₂ F₃) :=
  funext fun u => infConv_assoc (F₁ u) (F₂ u) (F₃ u)

/-- The supremal convolute of bifunctions is associative: $(G_1 \mathbin{\square} G_2)
\mathbin{\square} G_3 = G_1 \mathbin{\square} (G_2 \mathbin{\square} G_3)$. -/
theorem supConvBifun_assoc (G₁ G₂ G₃ : Bifun U X) :
    supConvBifun (supConvBifun G₁ G₂) G₃ = supConvBifun G₁ (supConvBifun G₂ G₃) :=
  funext fun u => supConv_assoc (G₁ u) (G₂ u) (G₃ u)

omit [AddCommGroup X] in
/-- A point $u$ is in the effective domain $\operatorname{dom} F$ of a bifunction if and only if the
effective domain of the slice $Fu$ is nonempty. -/
theorem mem_convexDomBifun_iff_convexDom_nonempty {F : Bifun U X} {u : U} :
    u ∈ convexDomBifun F ↔ (convexDom (F u)).Nonempty := by
  constructor
  · rintro ⟨x, hx⟩; exact ⟨x, lt_top_iff_ne_top.2 hx⟩
  · rintro ⟨x, hx⟩; exact ⟨x, hx.ne⟩

/-- **The effective domain of an infimal convolute.** For any bifunctions $F_1$ and $F_2$ from $U$
to $X$,
$$\operatorname{dom} (F_1 \mathbin{\square} F_2)
  = \operatorname{dom} F_1 \cap \operatorname{dom} F_2.$$

No hypothesis is needed: $\operatorname{dom} (f \mathbin{\square} g) = \operatorname{dom} f +
\operatorname{dom} g$ holds for all $f$ and $g$, and a sum of sets is nonempty exactly when both
summands are. -/
theorem convexDomBifun_infConvBifun (F₁ F₂ : Bifun U X) :
    convexDomBifun (infConvBifun F₁ F₂) = convexDomBifun F₁ ∩ convexDomBifun F₂ := by
  ext u
  rw [Set.mem_inter_iff, mem_convexDomBifun_iff_convexDom_nonempty,
      mem_convexDomBifun_iff_convexDom_nonempty,
    mem_convexDomBifun_iff_convexDom_nonempty, infConvBifun_apply, convexDom_infConv]
  exact Set.add_nonempty

/-- **The effective domain of a supremal convolute.** For any bifunctions $G_1$ and $G_2$ from $U$
to $X$, the concave effective domains satisfy $\operatorname{dom} (G_1 \mathbin{\square} G_2) =
\operatorname{dom} G_1 \cap \operatorname{dom} G_2$. This is the mirror of
`ConvexAnalysis.convexDomBifun_infConvBifun`. -/
theorem concaveDomBifun_supConvBifun (G₁ G₂ : Bifun U X) :
    concaveDomBifun (supConvBifun G₁ G₂) = concaveDomBifun G₁ ∩ concaveDomBifun G₂ := by
  rw [← convexDomBifun_neg, ← convexDomBifun_neg, ← convexDomBifun_neg, neg_supConvBifun,
      convexDomBifun_infConvBifun]

end InfConvBifunDefs

section InfConvBifunConvex

variable {U X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]
variable [AddCommGroup Y] [Module ℝ Y] {F₁ F₂ : Bifun U X}

/-- The linear map $((u, x), y) \mapsto (u, x - y)$ from $(U \times X) \times X$ to $U \times X$.
With `ConvexAnalysis.infConvSubRight` it is the change of variables that turns a partial infimal
convolution into a partial minimization. -/
def infConvSubLeft (U X : Type*) [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X] :
    (U × X) × X →ₗ[ℝ] U × X :=
  LinearMap.prod (LinearMap.fst ℝ U X ∘ₗ LinearMap.fst ℝ (U × X) X)
    (LinearMap.snd ℝ U X ∘ₗ LinearMap.fst ℝ (U × X) X - LinearMap.snd ℝ (U × X) X)

/-- The map `ConvexAnalysis.infConvSubLeft` sends $((u, x), y)$ to $(u, x - y)$. -/
@[simp] theorem infConvSubLeft_apply (q : (U × X) × X) :
    infConvSubLeft U X q = (q.1.1, q.1.2 - q.2) := rfl

/-- The linear map $((u, x), y) \mapsto (u, y)$ from $(U \times X) \times X$ to $U \times X$, the
second half of the change of variables of `ConvexAnalysis.infConvSubLeft`. -/
def infConvSubRight (U X : Type*) [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X] :
    (U × X) × X →ₗ[ℝ] U × X :=
  LinearMap.prod (LinearMap.fst ℝ U X ∘ₗ LinearMap.fst ℝ (U × X) X) (LinearMap.snd ℝ (U × X) X)

/-- The map `ConvexAnalysis.infConvSubRight` sends $((u, x), y)$ to $(u, y)$. -/
@[simp] theorem infConvSubRight_apply (q : (U × X) × X) :
    infConvSubRight U X q = (q.1.1, q.2) := rfl

/-- The graph function of $F_1 \mathbin{\square} F_2$ is a partial minimization. If $F_1$ and $F_2$
never take the value $-\infty$, then for all $(u, x) \in U \times X$
$$(F_1 \mathbin{\square} F_2)(u, x) = \inf_{y \in X} \{ F_1(u, x - y) + F_2(u, y) \}.$$
The function minimized is convex on $(U \times X) \times X$ when $F_1$ and $F_2$ are convex. -/
theorem graphFn_infConvBifun (hb₁ : ∀ u x, F₁ u x ≠ ⊥) (hb₂ : ∀ u x, F₂ u x ≠ ⊥) (p : U × X) :
    graphFn (infConvBifun F₁ F₂) p
      = ⨅ y : X, (compLin (graphFn F₁) (infConvSubLeft U X)
          + compLin (graphFn F₂) (infConvSubRight U X)) (p, y) := by
  change infConv (F₁ p.1) (F₂ p.1) p.2 = _
  rw [infConv_apply (fun x => hb₁ p.1 x) (fun x => hb₂ p.1 x)]
  rfl

/-- **An infimal convolute of convex bifunctions is convex.** Let $F_1$ and $F_2$ be convex
bifunctions from $U$ to $X$ that never take the value $-\infty$. Then
$F_1 \mathbin{\square} F_2$ is convex.

$F_1 \mathbin{\square} F_2$ is a partial infimal convolution of the graph functions. So the
result is `ConvexAnalysis.convexFn_iInf_right`, applied to the sum of the two graph functions
after the linear change of variables $((u, x), y) \mapsto ((u, x - y), (u, y))$. -/
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

/-- **A supremal convolute of concave bifunctions is concave.** Let $G_1$ and $G_2$ be concave
bifunctions from $U$ to $X$ that never take the value $+\infty$. Then
$G_1 \mathbin{\square} G_2$ is concave. This is the mirror of
`ConvexAnalysis.convexBifun_infConvBifun`, through $-(G_1 \mathbin{\square} G_2) = (-G_1)
\mathbin{\square} (-G_2)$. -/
theorem concaveBifun_supConvBifun {G₁ G₂ : Bifun U X} (ht₁ : ∀ u x, G₁ u x ≠ ⊤)
    (ht₂ : ∀ u x, G₂ u x ≠ ⊤) (hG₁ : ConcaveBifun G₁) (hG₂ : ConcaveBifun G₂) :
    ConcaveBifun (supConvBifun G₁ G₂) := by
  have h : (fun p => -(graphFn (supConvBifun G₁ G₂) p))
      = graphFn (infConvBifun (fun u x => -(G₁ u x)) (fun u x => -(G₂ u x))) :=
    funext fun p => congrFun (congrFun (neg_supConvBifun G₁ G₂) p.1) p.2
  rw [ConcaveBifun, concaveFn_iff_convexFn_neg, h]
  exact convexBifun_infConvBifun (fun u x => by rw [Ne, EReal.neg_eq_bot_iff]; exact ht₁ u x)
    (fun u x => by rw [Ne, EReal.neg_eq_bot_iff]; exact ht₂ u x) hG₁.convexFn_neg
    hG₂.convexFn_neg

omit [AddCommGroup U] [Module ℝ U] in
/-- **The inner product with an infimal convolute is the sum of the inner products.** Let $X$ and
$Y$ be real vector spaces paired by $\langle x, y \rangle$, and let $F_1$ and $F_2$ be
bifunctions from $U$ to $X$. Then for every $u \in U$ and $y \in Y$
$$\langle (F_1 \mathbin{\square} F_2) u, y \rangle
  = \langle F_1 u, y \rangle + \langle F_2 u, y \rangle.$$

No hypothesis is needed. The sum follows Rockafellar's convention $\infty - \infty = -\infty$,
which is the extended-real convention $(+\infty) + (-\infty) = -\infty$. The result is
`ConvexAnalysis.convexConj_infConv`, the identity $(f \mathbin{\square} g)^* = f^* + g^*$,
applied to each slice. -/
theorem bracket_infConvBifun (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (F₁ F₂ : Bifun U X) (u : U) :
    bracket Bx (infConvBifun F₁ F₂) u = bracket Bx F₁ u + bracket Bx F₂ u :=
  convexConj_infConv Bx (F₁ u) (F₂ u)

omit [AddCommGroup U] [Module ℝ U] in
/-- **The concave inner product with a supremal convolute is the concave sum of the concave inner
products.** Let $Y$ and $X$ be real vector spaces paired by $\langle y, x \rangle$, and let
$G_1$ and $G_2$ be bifunctions from $U$ to $X$. Then for every $y \in Y$ and $u \in U$
$$\langle y, (G_1 \mathbin{\square} G_2) u \rangle
  = \langle y, G_1 u \rangle + \langle y, G_2 u \rangle,$$
where $\langle y, Gu \rangle = \inf_x \{ \langle y, x \rangle - (Gu)(x) \}$, and the sum follows
the concave convention $\infty - \infty = +\infty$.

No hypothesis is needed. The concave sum $a + b$ is written $-(-a + -b)$. The result is
`ConvexAnalysis.concaveConj_supConv` applied to each slice, and it is the concave twin of
`ConvexAnalysis.bracket_infConvBifun`. -/
theorem concaveBracket_supConvBifun (By : Y →ₗ[ℝ] X →ₗ[ℝ] ℝ) (G₁ G₂ : Bifun U X) (y : Y) (u : U) :
    concaveBracket By (supConvBifun G₁ G₂) y u
      = -(-(concaveBracket By G₁ y u) + -(concaveBracket By G₂ y u)) :=
  congrFun (concaveConj_supConv By.flip (G₁ u) (G₂ u)) y

end InfConvBifunConvex

/-! ### The adjoint of an infimal or supremal convolute -/

section AdjointInfConvBifun

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]

/-- **The adjoint of an infimal convolute is the supremal convolute of the adjoints.** Let $U, V$
and $X, Y$ be pairs of real vector spaces, each pair with a bilinear pairing, let $F_1$ and
$F_2$ be bifunctions from $U$ to $X$, and let $y \in Y$. Let the functions
$u \mapsto -\langle F_1 u, y \rangle$ and $u \mapsto -\langle F_2 u, y \rangle$ on $U$ add
exactly. Then
$$(F_1 \mathbin{\square} F_2)^* y = F_1^* y \mathbin{\square} F_2^* y,$$
the supremal convolution of the concave functions $F_1^* y$ and $F_2^* y$ on $V$.

The adjoint at $y$ is the concave conjugate of the concave function
$u \mapsto \langle F u, y \rangle$, and by `ConvexAnalysis.bracket_infConvBifun` the inner
product with $F_1 \mathbin{\square} F_2$ is the sum of the two. The proof is the concave
conjugate of a sum. Exact addition is `ConvexAnalysis.IsExactSum`. Its two properness conditions
say that neither $u \mapsto \langle F_i u, y \rangle$ takes the value $+\infty$, which is
Rockafellar's condition $y \in \operatorname{dom} F_1^* \cap \operatorname{dom} F_2^*$. Its
exactness condition is what his relative-interior condition supplies. -/
theorem convexAdjointBifun_infConvBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (F₁ F₂ : Bifun U X) {y : Y}
    (hex : IsExactSum Bu (fun u => -(bracket Bx F₁ u y)) (fun u => -(bracket Bx F₂ u y))) :
    convexAdjointBifun Bu Bx (infConvBifun F₁ F₂) y
      = supConv (convexAdjointBifun Bu Bx F₁ y) (convexAdjointBifun Bu Bx F₂ y) := by
  have hadj : ∀ F : Bifun U X,
      convexAdjointBifun Bu Bx F y = concaveConj Bu (fun u => bracket Bx F u y) :=
    fun F => funext fun v => convexAdjointBifun_eq_concaveConj_bracket Bu Bx F y v
  have hbr : (fun u => bracket Bx (infConvBifun F₁ F₂) u y)
      = fun u => bracket Bx F₁ u y + bracket Bx F₂ u y :=
    funext fun u => congrFun (bracket_infConvBifun Bx F₁ F₂ u) y
  calc convexAdjointBifun Bu Bx (infConvBifun F₁ F₂) y
      = concaveConj Bu (fun u => bracket Bx (infConvBifun F₁ F₂) u y) := hadj _
    _ = concaveConj Bu (fun u => bracket Bx F₁ u y + bracket Bx F₂ u y) := by rw [hbr]
    _ = supConv (concaveConj Bu fun u => bracket Bx F₁ u y)
          (concaveConj Bu fun u => bracket Bx F₂ u y) := hex.concaveConj_add
    _ = supConv (convexAdjointBifun Bu Bx F₁ y) (convexAdjointBifun Bu Bx F₂ y) := by
          rw [hadj F₁, hadj F₂]

/-- **The adjoint of an infimal convolute**, as an identity of bifunctions. If for every $y \in Y$
the functions $u \mapsto -\langle F_1 u, y \rangle$ and $u \mapsto -\langle F_2 u, y \rangle$
add exactly, then $(F_1 \mathbin{\square} F_2)^* = F_1^* \mathbin{\square} F_2^*$, the right
side a supremal convolute. -/
theorem convexAdjointBifun_infConvBifun_eq_supConvBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (F₁ F₂ : Bifun U X)
    (hex : ∀ y : Y, IsExactSum Bu (fun u => -(bracket Bx F₁ u y))
      (fun u => -(bracket Bx F₂ u y))) :
    convexAdjointBifun Bu Bx (infConvBifun F₁ F₂)
      = supConvBifun (convexAdjointBifun Bu Bx F₁) (convexAdjointBifun Bu Bx F₂) :=
  funext fun y => convexAdjointBifun_infConvBifun Bu Bx F₁ F₂ (hex y)

/-- **The adjoint of a supremal convolute is the infimal convolute of the adjoints.** Let $U, V$ and
$X, Y$ be pairs of real vector spaces, each pair with a bilinear pairing, let $G_1$ and $G_2$ be
bifunctions from $Y$ to $V$, and let $u \in U$. Let the concave inner products
$y \mapsto \langle u, G_1 y \rangle$ and $y \mapsto \langle u, G_2 y \rangle$ on $Y$ add
exactly, with respect to the pairing of $Y$ with $X$. Then the concave adjoints satisfy
$$(G_1 \mathbin{\square} G_2)^* u = G_1^* u \mathbin{\square} G_2^* u,$$
the infimal convolution of the functions $G_1^* u$ and $G_2^* u$ on $X$. This is the mirror of
`ConvexAnalysis.convexAdjointBifun_infConvBifun`.

The concave adjoint at $u$ is the conjugate of the concave inner product
$y \mapsto \langle u, G y \rangle$. By `ConvexAnalysis.concaveBracket_supConvBifun` the concave
inner product with $G_1 \mathbin{\square} G_2$ is the sum of the two, and the concave sum agrees
with the convex sum because neither term is $-\infty$. An exact conjugate of a sum is the
infimal convolution of the conjugates. -/
theorem concaveAdjointBifun_supConvBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (G₁ G₂ : Bifun Y V) {u : U}
    (hex : IsExactSum Bx.flip (concaveBracket Bu G₁ u) (concaveBracket Bu G₂ u)) :
    concaveAdjointBifun Bu Bx (supConvBifun G₁ G₂) u
      = infConv (concaveAdjointBifun Bu Bx G₁ u) (concaveAdjointBifun Bu Bx G₂ u) := by
  have hsum : (fun y => concaveBracket Bu (supConvBifun G₁ G₂) u y)
      = concaveBracket Bu G₁ u + concaveBracket Bu G₂ u := by
    funext y
    rw [concaveBracket_supConvBifun, Pi.add_apply,
      EReal.neg_neg_add_neg (hex.properConvex_left.ne_bot y) (hex.properConvex_right.ne_bot y)]
  funext x
  rw [concaveAdjointBifun_eq_convexConj_concaveBracket, hsum, hex.convexConj_add,
    ← funext (concaveAdjointBifun_eq_convexConj_concaveBracket Bu Bx G₁ u),
    ← funext (concaveAdjointBifun_eq_convexConj_concaveBracket Bu Bx G₂ u)]

/-- **The adjoint of a supremal convolute**, as an identity of bifunctions. If for every $u \in U$
the concave inner products $y \mapsto \langle u, G_1 y \rangle$ and
$y \mapsto \langle u, G_2 y \rangle$ add exactly, then the concave adjoints satisfy $(G_1
\mathbin{\square} G_2)^* = G_1^* \mathbin{\square} G_2^*$, the right side an infimal convolute. -/
theorem concaveAdjointBifun_supConvBifun_eq_infConvBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (G₁ G₂ : Bifun Y V)
    (hex : ∀ u : U, IsExactSum Bx.flip (concaveBracket Bu G₁ u) (concaveBracket Bu G₂ u)) :
    concaveAdjointBifun Bu Bx (supConvBifun G₁ G₂)
      = infConvBifun (concaveAdjointBifun Bu Bx G₁) (concaveAdjointBifun Bu Bx G₂) :=
  funext fun u => concaveAdjointBifun_supConvBifun Bu Bx G₁ G₂ (hex u)

end AdjointInfConvBifun

/-! ### The image of a convex function under a bifunction -/

section ImageBifunDefs

variable {U X : Type*}

/-- Let $F$ be a bifunction from $U$ to $X$ and $f : U \to [-\infty, +\infty]$. The **image** of $f$
under $F$ is the function $Ff$ on $X$ with
$$(Ff)(x) = \inf_{u} \{ f(u) + (Fu)(x) \}.$$

When $F$ is the convex indicator bifunction of a linear map $A$, $Ff$ is the image
`ConvexAnalysis.mapLin A f`. -/
noncomputable def imageBifun (F : Bifun U X) (f : U → EReal) : X → EReal :=
  fun x => ⨅ u, f u + F u x

/-- The image $Ff$ has the value $(Ff)(x) = \inf_u \{ f(u) + (Fu)(x) \}$. -/
theorem imageBifun_apply (F : Bifun U X) (f : U → EReal) (x : X) :
    imageBifun F f x = ⨅ u, f u + F u x := rfl

/-- Let $G$ be a bifunction from $U$ to $X$ and $g : U \to [-\infty, +\infty]$. The **concave
image** of $g$ under $G$ is the function $Gg$ on $X$ with
$(Gg)(x) = \sup_u \{ g(u) + (Gu)(x) \}$. This is the mirror of `ConvexAnalysis.imageBifun`, for
concave $G$ and $g$. -/
noncomputable def concaveImageBifun (G : Bifun U X) (g : U → EReal) : X → EReal :=
  fun x => ⨆ u, g u + G u x

/-- The concave image $Gg$ has the value $(Gg)(x) = \sup_u \{ g(u) + (Gu)(x) \}$. -/
theorem concaveImageBifun_apply (G : Bifun U X) (g : U → EReal) (x : X) :
    concaveImageBifun G g x = ⨆ u, g u + G u x := rfl

end ImageBifunDefs

section ImageBifunConvex

variable {U X : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]
variable {F : Bifun U X} {f : U → EReal}

/-- **The image of a convex function under a convex bifunction is convex.** Let $F$ be a convex
bifunction from $U$ to $X$ and $f$ a convex function on $U$, neither of which takes the value
$-\infty$. Then $Ff$ is convex on $X$.

The function $(u, x) \mapsto f(u) + (Fu)(x)$ is convex on $U \times X$, and $Ff$ is its image
under the projection $(u, x) \mapsto x$. -/
theorem convexFn_imageBifun (hbF : ∀ u x, F u x ≠ ⊥) (hbf : ∀ u, f u ≠ ⊥)
    (hF : ConvexBifun F) (hf : ConvexFn f) : ConvexFn (imageBifun F f) := by
  have hh : ConvexFn (compLin f (LinearMap.snd ℝ X U) + compLin (graphFn F)
      (LinearEquiv.prodComm ℝ X U).toLinearMap) :=
    ConvexFn.add (convexFn_compLin _ hf) (convexFn_compLin _ hF)
      (fun q => hbf _) (fun q => hbF _ _)
  exact convexFn_iInf_right hh

end ImageBifunConvex

/-! ### The conjugate of an image -/

section ImageBifunConj

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
variable [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
variable {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ} {F : Bifun U X} {f : U → EReal}

omit [AddCommGroup U] [Module ℝ U] in
/-- **The conjugate of an image as a supremum.** Let $F$ be a bifunction from $U$ to $X$ and $f$ a
function on $U$, neither of which takes the value $-\infty$. Then for every $y \in Y$
$$(Ff)^*(y) = \sup_u \{ \langle Fu, y \rangle - f(u) \}.$$

This is the whole computational content of the formula for $(Ff)^*$. What remains is Fenchel's
duality theorem for $f$ and the concave function $u \mapsto \langle Fu, y \rangle$. -/
theorem convexConj_imageBifun_eq_iSup (hbF : ∀ u x, F u x ≠ ⊥) (hbf : ∀ u, f u ≠ ⊥) (y : Y) :
    convexConj Bx (imageBifun F f) y = ⨆ u, (bracket Bx F u y - f u) := by
  have hstep : ∀ u : U, (⨆ x : X, (((Bx x y : ℝ) : EReal) - (f u + F u x)))
      = bracket Bx F u y - f u := by
    intro u
    have hbody : ∀ x : X, ((Bx x y : ℝ) : EReal) - (f u + F u x)
        = (((Bx x y : ℝ) : EReal) - F u x) + -(f u) := fun x => by
      rw [EReal.sub_add_eq_sub_sub_swap _ (hbf u) (hbF u x), sub_eq_add_neg]
    rw [iSup_congr hbody, ← EReal.iSup_add, ← sub_eq_add_neg]
    rfl
  rw [convexConj_apply]
  calc (⨆ x : X, (((Bx x y : ℝ) : EReal) - imageBifun F f x))
      = ⨆ x : X, ⨆ u : U, (((Bx x y : ℝ) : EReal) - (f u + F u x)) :=
        iSup_congr fun x => EReal.coe_sub_iInf _ _
    _ = ⨆ u : U, ⨆ x : X, (((Bx x y : ℝ) : EReal) - (f u + F u x)) := iSup_comm
    _ = ⨆ u : U, (bracket Bx F u y - f u) := iSup_congr hstep

omit [AddCommGroup U] [Module ℝ U] in
/-- The conjugate of an image as a negated infimum. Let $F$ and $f$ never take the value $-\infty$,
and let $\langle Fu, y \rangle < +\infty$ for every $u$. Then $(Ff)^*(y) = -\inf_u \{ f(u) -
\langle Fu, y \rangle \}$, the primal side of Fenchel's duality theorem. -/
theorem convexConj_imageBifun_eq_neg_iInf (hbF : ∀ u x, F u x ≠ ⊥) (hbf : ∀ u, f u ≠ ⊥) {y : Y}
    (hgt : ∀ u, bracket Bx F u y ≠ ⊤) :
    convexConj Bx (imageBifun F f) y = -(⨅ u, (f u - bracket Bx F u y)) := by
  rw [convexConj_imageBifun_eq_iSup hbF hbf y, EReal.neg_iInf]
  exact iSup_congr fun u => (EReal.neg_sub_comm (.inl (hbf u)) (.inr (hgt u))).symm

/-- **The conjugate of an image is the image under the lower adjoint.** Let $U, V$ and $X, Y$ be
pairs of real vector spaces, each pair with a bilinear pairing, let $F$ be a bifunction from $U$
to $X$ that never takes the value $-\infty$, let $f$ be a proper function on $U$, and let
$y \in Y$. Let $f$ and the function $u \mapsto -\langle Fu, y \rangle$ add exactly. Then
$$(Ff)^*(y) = \inf_v \{ f^*(v) - (F^* y)(v) \} = (F_*^* f^*)(y).$$
This is Theorem 38.4 of [rockafellar1970convex].

The hypothesis says that Fenchel's duality theorem applies to $f$ and the concave function
$u \mapsto \langle Fu, y \rangle$. It replaces Rockafellar's condition that the relative
interiors of $\operatorname{dom} f$ and $\operatorname{dom} F$ have a point in common. It also
contains the properness of $u \mapsto -\langle Fu, y \rangle$, which is his side condition
$y \in \operatorname{dom} F^*$; the degenerate case is
`ConvexAnalysis.convexConj_imageBifun_of_bracket_eq_top`. Exact addition is
`ConvexAnalysis.IsExactSum`. -/
theorem convexConj_imageBifun (hbF : ∀ u x, F u x ≠ ⊥) (hf : ProperConvex f) {y : Y}
    (hex : IsExactSum Bu f (fun u => -(bracket Bx F u y))) :
    convexConj Bx (imageBifun F f) y = ⨅ v,
        (convexConj Bu f v - convexAdjointBifun Bu Bx F y v) := by
  set g : U → EReal := fun u => bracket Bx F u y with hg
  have hex' : IsExactSum Bu f (-g) := hex
  have hgt : ∀ u, g u ≠ ⊤ := by
    intro u hu
    exact hex'.properConvex_right.ne_bot u (by simp [Pi.neg_apply, hu])
  have hgd : (concaveDom g).Nonempty := by
    rw [concaveDom_eq_convexDom_neg]
    exact hex'.properConvex_right.convexDom_nonempty
  have h1 : convexConj Bx (imageBifun F f) y = -(⨅ u, (f u - g u)) :=
    convexConj_imageBifun_eq_neg_iInf hbF hf.ne_bot hgt
  have h2 : (⨅ u, f u - g u) = ⨆ v, (concaveConj Bu g v - convexConj Bu f v) := fenchel_duality hex'
  have h4 : -(⨆ v, (concaveConj Bu g v - convexConj Bu f v))
      = ⨅ v, (convexConj Bu f v - concaveConj Bu g v) := by
    rw [EReal.neg_iSup]
    exact iInf_congr fun v =>
      EReal.neg_sub_comm (.inr (convexConj_ne_bot hf.convexDom_nonempty v))
          (.inl (concaveConj_ne_top hgd v))
  rw [h1, h2, h4]
  exact iInf_congr fun v => by rw [convexAdjointBifun_eq_concaveConj_bracket]

/-- **The infimum in $(F_*^* f^*)(y)$ is attained.** Under the hypotheses of
`ConvexAnalysis.convexConj_imageBifun`, there is $v \in V$ with
$$f^*(v) - (F^* y)(v) = (Ff)^*(y).$$
This is the attainment part of Theorem 38.4 of [rockafellar1970convex]. -/
theorem exists_convexConj_imageBifun_eq (hbF : ∀ u x, F u x ≠ ⊥) (hf : ProperConvex f) {y : Y}
    (hex : IsExactSum Bu f (fun u => -(bracket Bx F u y))) :
    ∃ v : V,
        convexConj Bu f v - convexAdjointBifun Bu Bx F y v = convexConj Bx (imageBifun F f) y := by
  set g : U → EReal := fun u => bracket Bx F u y with hg
  have hex' : IsExactSum Bu f (-g) := hex
  have hgt : ∀ u, g u ≠ ⊤ := by
    intro u hu
    exact hex'.properConvex_right.ne_bot u (by simp [Pi.neg_apply, hu])
  have hgd : (concaveDom g).Nonempty := by
    rw [concaveDom_eq_convexDom_neg]
    exact hex'.properConvex_right.convexDom_nonempty
  obtain ⟨v, hv⟩ := exists_concaveConj_sub_convexConj_eq hex'
  refine ⟨v, ?_⟩
  rw [convexConj_imageBifun_eq_neg_iInf hbF hf.ne_bot hgt, ← hv,
    EReal.neg_sub_comm (.inr (convexConj_ne_bot hf.convexDom_nonempty v))
        (.inl (concaveConj_ne_top hgd v)),
    convexAdjointBifun_eq_concaveConj_bracket]

/-- **The degenerate case of $(Ff)^* = F_*^* f^*$.** Let $F$ be a bifunction from $U$ to $X$ that
never takes the value $-\infty$, let $f$ be a proper function on $U$, and let $y \in Y$. If
$\langle F u_0, y \rangle = +\infty$ at some $u_0$ with $f(u_0) < +\infty$, then
$$(Ff)^*(y) = +\infty \quad \text{and} \quad (F_*^* f^*)(y) = +\infty.$$

The condition at $u_0$ puts $y$ outside $\operatorname{dom} F^*$. With the finiteness of
$f(u_0)$ as an explicit hypothesis the result needs no qualification condition; Rockafellar
reaches this case from a relative-interior hypothesis instead. -/
theorem convexConj_imageBifun_of_bracket_eq_top (hbF : ∀ u x, F u x ≠ ⊥) (hf : ProperConvex f)
    {u₀ : U}
    {y : Y} (htop : bracket Bx F u₀ y = ⊤) (hfin : f u₀ ≠ ⊤) :
    convexConj Bx (imageBifun F f) y = ⊤ ∧
      imageBifun (lowerAdjointBifun Bu Bx F) (convexConj Bu f) y = ⊤ := by
  obtain ⟨r, hr⟩ :=
    EReal.exists_coe_of_ne_bot_of_lt_top (hf.ne_bot u₀) (lt_top_iff_ne_top.2 hfin)
  constructor
  · rw [convexConj_imageBifun_eq_iSup hbF hf.ne_bot y]
    refine eq_top_iff.2 (le_trans (le_of_eq ?_) (le_iSup _ u₀))
    rw [htop, hr]
    simp
  · have hbot : ∀ v : V, convexAdjointBifun Bu Bx F y v = ⊥ := by
      intro v
      rw [convexAdjointBifun_eq_concaveConj_bracket,
        concaveConj_of_eq_top (B := Bu) (g := fun u => bracket Bx F u y) htop]
    rw [imageBifun_apply]
    refine le_antisymm le_top (le_iInf fun v => ?_)
    have hv : convexConj Bu f v + lowerAdjointBifun Bu Bx F v y = ⊤ := by
      rw [lowerAdjointBifun_apply, hbot v, EReal.neg_bot,
        EReal.add_top_of_ne_bot (convexConj_ne_bot hf.convexDom_nonempty v)]
    exact le_of_eq hv.symm

end ImageBifunConj

/-! ### The image of a closed proper convex function -/

section ImageBifunProper

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
variable [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
variable {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ} {F : Bifun U X} {f : U → EReal}

/-- **$(Ff)^* = F_*^* f^*$ as an identity of values of images.** Under the hypotheses of
`ConvexAnalysis.convexConj_imageBifun`, $(Ff)^*(y) = (F_*^* f^*)(y)$, where the right side is
the image of $f^*$ under $F_*^*$. The two forms differ only by $a - b = a + (-b)$. -/
theorem convexConj_imageBifun_eq_imageBifun (hbF : ∀ u x, F u x ≠ ⊥) (hf : ProperConvex f) {y : Y}
    (hex : IsExactSum Bu f (fun u => -(bracket Bx F u y))) :
    convexConj Bx (imageBifun F f) y
        = imageBifun (lowerAdjointBifun Bu Bx F) (convexConj Bu f) y := by
  rw [convexConj_imageBifun hbF hf hex]
  rfl

end ImageBifunProper

section ImageBifunClosed

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsCompatiblePairing Bu] {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ}
  [IsCompatiblePairing Bx] {F : Bifun U X} {f : U → EReal}

/-- **$(F_*^* f^*)^* = Ff$ in the closed case.** Let $U$ and $X$ be locally convex real topological
vector spaces, paired with $V$ and $Y$ by pairings compatible with their topologies. Let $F$ be
a convex bifunction from $U$ to $X$ with a closed graph function and a finite value
$F(u_0, x_0) < +\infty$, let $f$ be a closed proper convex function on $U$, and let $x \in X$.
Let $f^*$ and the function $v \mapsto -\langle F_*^* v, x \rangle$ on $V$ add exactly. Then
$$(F_*^* f^*)^*(x) = (Ff)(x).$$
The rest of the closed case follows from this identity.

This is `ConvexAnalysis.convexConj_imageBifun` for $F_*^*$ and $f^*$, whose own lower adjoint
and conjugate are $F$ and $f$ again. The exactness hypothesis replaces Rockafellar's condition
that the relative interiors of $\operatorname{dom} f^*$ and $\operatorname{dom} F_*^*$ have a
point in common. -/
theorem convexConj_imageBifun_lowerAdjointBifun (hF : ConvexBifun F) (hFcl : ClosedConvexBifun F)
    {u₀ : U} {x₀ : X} (hFp : F u₀ x₀ ≠ ⊤) (hf : ClosedProperConvexFn f) {x : X}
    (hex : IsExactSum Bu.flip (convexConj Bu f)
      (fun v => -(bracket Bx.flip (lowerAdjointBifun Bu Bx F) v x))) :
    convexConj Bx.flip (imageBifun (lowerAdjointBifun Bu Bx F) (convexConj Bu f)) x
        = imageBifun F f x := by
  have hbid : convexConj Bu.flip (convexConj Bu f) = f :=
    (convexBiconj_eq_convexCl (B := Bu) hf.convex).trans hf.closed
  have h := convexConj_imageBifun_eq_imageBifun (Bu := Bu.flip) (Bx := Bx.flip)
    (lowerAdjointBifun_ne_bot hFp Bu Bx) (properConvex_convexConj hf) hex
  rw [h, lowerAdjointBifun_lowerAdjointBifun_eq_convexClBifun hF, hFcl.convexClBifun_eq, hbid]

/-- **The image of a closed proper convex function is closed.** Under the hypotheses of
`ConvexAnalysis.convexConj_imageBifun_lowerAdjointBifun` for every $x \in X$, the image $Ff$ is
closed. It is a conjugate. -/
theorem closedConvex_imageBifun (hF : ConvexBifun F) (hFcl : ClosedConvexBifun F)
    {u₀ : U} {x₀ : X} (hFp : F u₀ x₀ ≠ ⊤) (hf : ClosedProperConvexFn f)
    (hex : ∀ x : X, IsExactSum Bu.flip (convexConj Bu f)
      (fun v => -(bracket Bx.flip (lowerAdjointBifun Bu Bx F) v x))) :
    ClosedConvex (imageBifun F f) := by
  have hfun : imageBifun F f
      = convexConj Bx.flip (imageBifun (lowerAdjointBifun Bu Bx F) (convexConj Bu f)) :=
    funext fun x => (convexConj_imageBifun_lowerAdjointBifun hF hFcl hFp hf (hex x)).symm
  rw [hfun]
  exact closedConvex_convexConj

/-- **The infimum in $(Ff)(x)$ is attained.** Under the hypotheses of
`ConvexAnalysis.convexConj_imageBifun_lowerAdjointBifun` at $x$, there is $u \in U$ with
$f(u) + (Fu)(x) = (Ff)(x)$. This is `ConvexAnalysis.exists_convexConj_imageBifun_eq` for $F_*^*$
and $f^*$. -/
theorem exists_imageBifun_eq (hF : ConvexBifun F) (hFcl : ClosedConvexBifun F)
    {u₀ : U} {x₀ : X} (hFp : F u₀ x₀ ≠ ⊤) (hf : ClosedProperConvexFn f) {x : X}
    (hex : IsExactSum Bu.flip (convexConj Bu f)
      (fun v => -(bracket Bx.flip (lowerAdjointBifun Bu Bx F) v x))) :
    ∃ u : U, f u + F u x = imageBifun F f x := by
  have hbid : convexConj Bu.flip (convexConj Bu f) = f :=
    (convexBiconj_eq_convexCl (B := Bu) hf.convex).trans hf.closed
  obtain ⟨u, hu⟩ := exists_convexConj_imageBifun_eq (Bu := Bu.flip) (Bx := Bx.flip)
    (lowerAdjointBifun_ne_bot hFp Bu Bx) (properConvex_convexConj hf) hex
  refine ⟨u, ?_⟩
  rw [hbid, convexAdjointBifun_flip_lowerAdjointBifun hF hFcl, inverseBifun_apply] at hu
  have hval : f u - -(F u x) = f u + F u x := by
    change f u + -(-(F u x)) = f u + F u x
    rw [neg_neg]
  rw [← convexConj_imageBifun_lowerAdjointBifun hF hFcl hFp hf hex, ← hu, hval]

variable [TopologicalSpace Y] [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y]
  [LocallyConvexSpace ℝ Y] [IsCompatiblePairing Bx.flip]

/-- **$(Ff)^* = \operatorname{cl}(F_*^* f^*)$ in the closed case.** Let $U$, $X$ and $Y$ be locally
convex real topological vector spaces, with $U, V$ and $X, Y$ paired by pairings compatible with
the topologies of $U$, $X$ and $Y$. Let $F$ be a convex bifunction from $U$ to $X$ with a closed
graph function and a finite value $F(u_0, x_0) < +\infty$, and let $f$ be a closed proper convex
function on $U$. If for every $x \in X$ the functions $f^*$ and
$v \mapsto -\langle F_*^* v, x \rangle$ add exactly, then
$$(Ff)^* = \operatorname{cl}(F_*^* f^*).$$

$Ff$ is the conjugate of $F_*^* f^*$, so $(Ff)^*$ is the biconjugate of $F_*^* f^*$, which is
its closure. -/
theorem convexConj_imageBifun_eq_convexCl (hF : ConvexBifun F) (hFcl : ClosedConvexBifun F)
    {u₀ : U} {x₀ : X} (hFp : F u₀ x₀ ≠ ⊤) (hf : ClosedProperConvexFn f)
    (hex : ∀ x : X, IsExactSum Bu.flip (convexConj Bu f)
      (fun v => -(bracket Bx.flip (lowerAdjointBifun Bu Bx F) v x))) :
    convexConj Bx (imageBifun F f)
      = convexCl (imageBifun (lowerAdjointBifun Bu Bx F) (convexConj Bu f)) := by
  have hconv : ConvexFn (imageBifun (lowerAdjointBifun Bu Bx F) (convexConj Bu f)) :=
    convexFn_imageBifun (lowerAdjointBifun_ne_bot hFp Bu Bx)
      (properConvex_convexConj hf).ne_bot (convexBifun_lowerAdjointBifun Bu Bx F)
          (convexFn_convexConj Bu f)
  have hfun : imageBifun F f
      = convexConj Bx.flip (imageBifun (lowerAdjointBifun Bu Bx F) (convexConj Bu f)) :=
    funext fun x => (convexConj_imageBifun_lowerAdjointBifun hF hFcl hFp hf (hex x)).symm
  rw [hfun]
  exact convexBiconj_eq_convexCl (B := Bx.flip) hconv

end ImageBifunClosed



/-! ### The inner product of a convex and a concave function -/

section FenchelPairing

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
variable {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f : E → EReal} {g : F → EReal}

/-- Let $E$ and $F$ be real vector spaces paired by $\langle x, y \rangle$, let $f$ be a function on
$E$ and $g$ a function on $F$. The **supremum side** of Rockafellar's inner product
$\langle f, g \rangle$ of a convex $f$ and a concave $g$ is
$$\sup_{x \in E} \{ g^*(x) - f(x) \},$$
where $g^*$ is the concave conjugate of $g$. -/
noncomputable def fenchelSup (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) (g : F → EReal) : EReal :=
  ⨆ x : E, (concaveConj B.flip g x - f x)

/-- Let $E$ and $F$ be real vector spaces paired by $\langle x, y \rangle$, let $f$ be a function on
$E$ and $g$ a function on $F$. The **infimum side** of Rockafellar's inner product
$\langle f, g \rangle$ is
$$\inf_{y \in F} \{ f^*(y) - g(y) \}.$$
-/
noncomputable def fenchelInf (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) (g : F → EReal) : EReal :=
  ⨅ y : F, (convexConj B f y - g y)

/-- The supremum side of $\langle f, g \rangle$ has the value $\sup_x \{ g^*(x) - f(x) \}$. -/
theorem fenchelSup_apply (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) (g : F → EReal) :
    fenchelSup B f g = ⨆ x : E, (concaveConj B.flip g x - f x) := rfl

/-- The infimum side of $\langle f, g \rangle$ has the value $\inf_y \{ f^*(y) - g(y) \}$. -/
theorem fenchelInf_apply (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) (g : F → EReal) :
    fenchelInf B f g = ⨅ y : F, (convexConj B f y - g y) := rfl

/-- Rockafellar's inner product $\langle f, g \rangle$ **exists** if its supremum side
`ConvexAnalysis.fenchelSup` and its infimum side `ConvexAnalysis.fenchelInf` are equal. When
they differ, $\langle f, g \rangle$ is undefined. -/
def HasFenchelPairing (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) (g : F → EReal) : Prop :=
  fenchelSup B f g = fenchelInf B f g

/-- The value of Rockafellar's inner product $\langle f, g \rangle$, represented by its infimum side
`ConvexAnalysis.fenchelInf`.

This is Rockafellar's inner product only when `ConvexAnalysis.HasFenchelPairing` holds;
`ConvexAnalysis.HasFenchelPairing.fenchelSup_eq` states that the supremum side then agrees. -/
noncomputable def fenchelPairing (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) (g : F → EReal) : EReal :=
  fenchelInf B f g

/-- If the inner product $\langle f, g \rangle$ exists, then its supremum side equals its value
`ConvexAnalysis.fenchelPairing`. -/
theorem HasFenchelPairing.fenchelSup_eq (h : HasFenchelPairing B f g) :
    fenchelSup B f g = fenchelPairing B f g := h

/-- The value `ConvexAnalysis.fenchelPairing` of $\langle f, g \rangle$ is its infimum side. -/
theorem fenchelPairing_eq_fenchelInf (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) (g : F → EReal) :
    fenchelPairing B f g = fenchelInf B f g := rfl

/-- **Weak duality for the inner product.** Let $E$ and $F$ be real vector spaces paired by
$\langle x, y \rangle$, and let $f$ be a function on $E$ and $g$ a function on $F$. Then
$$\sup_{x \in E} \{ g^*(x) - f(x) \} \le \inf_{y \in F} \{ f^*(y) - g(y) \}.$$

No hypothesis is needed. Both collisions $\infty - \infty$ fall on the correct side, as in
`ConvexAnalysis.concaveConj_sub_convexConj_le_sub`. -/
theorem fenchelSup_le_fenchelInf (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) (g : F → EReal) :
    fenchelSup B f g ≤ fenchelInf B f g := by
  refine iSup_le fun x => le_iInf fun y => ?_
  have hsub : ∀ {p q r : EReal}, p ≤ q → p - r ≤ q - r := fun h => add_le_add h le_rfl
  have h1 : concaveConj B.flip g x ≤ ((B x y : ℝ) : EReal) - g y := concaveConj_le_sub B.flip g y x
  have h2 : ((B x y : ℝ) : EReal) - f x ≤ convexConj B f y := sub_le_convexConj B f x y
  calc concaveConj B.flip g x - f x
      ≤ (((B x y : ℝ) : EReal) - g y) - f x := hsub h1
    _ = (((B x y : ℝ) : EReal) - f x) - g y := by
        change ((B x y : ℝ) : EReal) + -(g y) + -(f x)
          = ((B x y : ℝ) : EReal) + -(f x) + -(g y)
        exact add_right_comm _ _ _
    _ ≤ convexConj B f y - g y := hsub h2

/-- If the infimum side of $\langle f, g \rangle$ is at most its supremum side, then the inner
product exists. By weak duality the two sides are then equal. -/
theorem hasFenchelPairing_of_le (h : fenchelInf B f g ≤ fenchelSup B f g) :
    HasFenchelPairing B f g :=
  le_antisymm (fenchelSup_le_fenchelInf B f g) h

end FenchelPairing

/-! ### Conjugation reverses the inner product -/

section FenchelPairingConj

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
variable {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f : E → EReal} {g : F → EReal}

/-- Let $f$ be a proper convex function on $E$ and $g$ a proper concave function on $F$. Then the
infimum side of $\langle f^*, g^* \rangle$ is at most minus the supremum side of
$\langle f, g \rangle$. This is one of the two outer steps in the proof of
`ConvexAnalysis.hasFenchelPairing_convexConj`, and it rests only on $f^{**} \le f$. -/
theorem fenchelInf_convexConj_le_neg_fenchelSup (hf : ProperConvex f) (hg : ProperConcave g) :
    fenchelInf B.flip (convexConj B f) (concaveConj B.flip g) ≤ -(fenchelSup B f g) := by
  have hneg : -(fenchelSup B f g) = ⨅ x : E, (f x - concaveConj B.flip g x) := by
    rw [fenchelSup_apply, EReal.neg_iSup]
    exact iInf_congr fun x =>
      EReal.neg_sub_comm (.inr (hf.ne_bot x)) (.inl (concaveConj_ne_top hg.concaveDom_nonempty x))
  rw [hneg, fenchelInf_apply]
  exact iInf_mono fun x => add_le_add (convexBiconj_le B f x) le_rfl

/-- Let $f$ be a proper convex function on $E$ and $g$ a proper concave function on $F$. Then minus
the infimum side of $\langle f, g \rangle$ is at most the supremum side of
$\langle f^*, g^* \rangle$. This is the other outer step in the proof of
`ConvexAnalysis.hasFenchelPairing_convexConj`, and it rests only on $g \le g^{**}$. -/
theorem neg_fenchelInf_le_fenchelSup_convexConj (hf : ProperConvex f) (hg : ProperConcave g) :
    -(fenchelInf B f g) ≤ fenchelSup B.flip (convexConj B f) (concaveConj B.flip g) := by
  have hneg : -(fenchelInf B f g) = ⨆ y : F, (g y - convexConj B f y) := by
    rw [fenchelInf_apply, EReal.neg_iInf]
    exact iSup_congr fun y =>
      EReal.neg_sub_comm (.inl (convexConj_ne_bot hf.convexDom_nonempty y)) (.inr (hg.ne_top y))
  rw [hneg, fenchelSup_apply]
  exact iSup_mono fun y => add_le_add (le_concaveBiconj B.flip g y) le_rfl

/-- **If $\langle f, g \rangle$ exists, then so does $\langle f^*, g^* \rangle$.** Let $f$ be a
proper convex function on $E$ and $g$ a proper concave function on $F$. If the two sides of
$\langle f, g \rangle$ agree, then the two sides of $\langle f^*, g^* \rangle$ agree.

The proof is the chain $-\langle f, g \rangle \le \langle f^*, g^* \rangle_{\sup} \le \langle
f^*, g^* \rangle_{\inf} \le -\langle f, g \rangle$, the middle link being weak duality. When the
two ends coincide, all four terms do. -/
theorem hasFenchelPairing_convexConj (hf : ProperConvex f) (hg : ProperConcave g)
    (h : HasFenchelPairing B f g) :
    HasFenchelPairing B.flip (convexConj B f) (concaveConj B.flip g) := by
  refine hasFenchelPairing_of_le (le_trans (fenchelInf_convexConj_le_neg_fenchelSup hf hg) ?_)
  rw [h]
  exact neg_fenchelInf_le_fenchelSup_convexConj hf hg

/-- **Conjugation reverses the inner product.** Let $E$ and $F$ be real vector spaces paired by
$\langle x, y \rangle$, let $f$ be a proper convex function on $E$, and let $g$ be a proper
concave function on $F$. If the inner product $\langle f, g \rangle$ exists, then
$\langle f^*, g^* \rangle$ exists and
$$\langle f^*, g^* \rangle = -\langle f, g \rangle.$$

Here $f^*$ is the convex conjugate on $F$ and $g^*$ the concave conjugate on $E$, and
$\langle f^*, g^* \rangle$ is taken with respect to the flipped pairing. The existence is
`ConvexAnalysis.hasFenchelPairing_convexConj`. -/
theorem fenchelPairing_convexConj (hf : ProperConvex f) (hg : ProperConcave g)
    (h : HasFenchelPairing B f g) :
    fenchelPairing B.flip (convexConj B f) (concaveConj B.flip g) = -(fenchelPairing B f g) := by
  refine le_antisymm ?_ ?_
  · refine le_trans (fenchelInf_convexConj_le_neg_fenchelSup hf hg) (le_of_eq ?_)
    rw [fenchelPairing_eq_fenchelInf, ← h]
  · simp only [fenchelPairing_eq_fenchelInf]
    rw [← hasFenchelPairing_convexConj hf hg h]
    exact neg_fenchelInf_le_fenchelSup_convexConj hf hg

end FenchelPairingConj

/-! ### An adjoint moves across the inner product -/

section AdjointAcrossAux

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

/-- Let $E$ and $F$ be real vector spaces paired by $\langle x, y \rangle$, let $f$ be a function on
$E$ with nonempty effective domain, and let $h$ be a function on $E$ with nonempty concave
effective domain. Then the supremum side of $\langle f^*, h \rangle$ is minus the infimum side
of $\langle f, h^* \rangle$:
$$\sup_y \{ h^*(y) - f^*(y) \} = -\inf_y \{ f^*(y) - h^*(y) \}.$$

This is sign bookkeeping, and it is the step that lets an adjoint move across the inner product. -/
theorem fenchelSup_convexConj_eq_neg_fenchelInf (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) {f h : E → EReal}
    (hd : (convexDom f).Nonempty) (hh : (concaveDom h).Nonempty) :
    fenchelSup B.flip (convexConj B f) h = -(fenchelInf B f (concaveConj B h)) := by
  rw [fenchelSup_apply, fenchelInf_apply, EReal.neg_iInf]
  refine iSup_congr fun y => ?_
  rw [LinearMap.flip_flip]
  exact (EReal.neg_sub_comm (.inl (convexConj_ne_bot hd y)) (.inr (concaveConj_ne_top hh y))).symm

end AdjointAcrossAux

section AdjointAcrossBracket

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
variable [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
variable {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ} {F : Bifun U X}
variable {f : U → EReal} {g : X → EReal}

/-- For every bifunction $F$ from $U$ to $X$, $u \in U$ and $y \in Y$, the inner product
$\langle Fu, y \rangle$ is at most the concave conjugate of $F^* y$ at $u$,
$\inf_v \{ \langle u, v \rangle - (F^* y)(v) \}$. This is `ConvexAnalysis.le_concaveBiconj`
after `ConvexAnalysis.convexAdjointBifun_eq_concaveConj_bracket`, and it makes the existence of
$\langle f, F^* y \rangle$ automatic. -/
theorem bracket_le_concaveConj_convexAdjointBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (F : Bifun U X) (y : Y) (u : U) :
    bracket Bx F u y ≤ concaveConj Bu.flip (convexAdjointBifun Bu Bx F y) u := by
  have hrw : convexAdjointBifun Bu Bx F y = concaveConj Bu (fun u => bracket Bx F u y) :=
    funext fun v => convexAdjointBifun_eq_concaveConj_bracket Bu Bx F y v
  rw [hrw]
  exact le_concaveBiconj Bu (fun u => bracket Bx F u y) u

/-- **The inner product $\langle f, F^* y \rangle$ exists.** Let $F$ be a bifunction from $U$ to $X$
that never takes the value $-\infty$, let $f$ be a proper function on $U$, and let $f$ and
$u \mapsto -\langle Fu, y \rangle$ add exactly. Then the two sides of $\langle f, F^* y \rangle$
agree.

Weak duality gives one inequality. The other is `ConvexAnalysis.convexConj_imageBifun` together
with `ConvexAnalysis.bracket_le_concaveConj_convexAdjointBifun`. -/
theorem hasFenchelPairing_convexAdjointBifun (hbF : ∀ u x, F u x ≠ ⊥) (hf : ProperConvex f) {y : Y}
    (hex : IsExactSum Bu f (fun u => -(bracket Bx F u y))) :
    HasFenchelPairing Bu f (convexAdjointBifun Bu Bx F y) := by
  refine hasFenchelPairing_of_le ?_
  have h1 : fenchelInf Bu f (convexAdjointBifun Bu Bx F y) = ⨆ u, (bracket Bx F u y - f u) := by
    rw [fenchelInf_apply, ← convexConj_imageBifun hbF hf hex,
        convexConj_imageBifun_eq_iSup hbF hf.ne_bot y]
  rw [h1, fenchelSup_apply]
  exact iSup_mono fun u =>
    add_le_add (bracket_le_concaveConj_convexAdjointBifun Bu Bx F y u) le_rfl

/-- **An adjoint moves across the inner product.** Let $U, V$ and $X, Y$ be pairs of real vector
spaces, each pair with a bilinear pairing, let $F$ be a bifunction from $U$ to $X$ that never
takes the value $-\infty$, let $f$ be a proper function on $U$, and let $y \in Y$. Let $f$ and
the function $u \mapsto -\langle Fu, y \rangle$ add exactly. Then
$$\langle Ff, y \rangle = \langle f, F^* y \rangle.$$

The left side is $(Ff)^*(y)$, the inner product of the image $Ff$ with $y$. The right side is
the inner product `ConvexAnalysis.fenchelPairing` of the convex function $f$ with the concave
function $F^* y$, which exists by `ConvexAnalysis.hasFenchelPairing_convexAdjointBifun`. Exact
addition is `ConvexAnalysis.IsExactSum`. -/
theorem convexConj_imageBifun_eq_fenchelPairing (hbF : ∀ u x, F u x ≠ ⊥)
    (hf : ProperConvex f) {y : Y}
    (hex : IsExactSum Bu f (fun u => -(bracket Bx F u y))) :
    convexConj Bx (imageBifun F f) y = fenchelPairing Bu f (convexAdjointBifun Bu Bx F y) :=
  convexConj_imageBifun hbF hf hex

end AdjointAcrossBracket

section AdjointAcross

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
variable [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
variable {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ} {F : Bifun U X}
variable {f : U → EReal} {g : X → EReal}

/-- Let $F$ be a bifunction from $U$ to $X$ and $g$ a function on $X$, and let
$F(u_0, x_0) < +\infty$ and $g(x_0)$ be finite for some $(u_0, x_0)$. Then the concave image
$F^* g^*$ of the concave conjugate $g^*$ under the adjoint is nowhere $+\infty$.

The bound is uniform in $y$ because the two occurrences of $\langle x_0, y \rangle$ cancel:
every term of the supremum is at most $F(u_0, x_0) + \langle u_0, v \rangle - g(x_0)$. -/
theorem concaveImageBifun_convexAdjointBifun_ne_top (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) {u₀ : U} {x₀ : X} (hF : F u₀ x₀ ≠ ⊤) (hgb : g x₀ ≠ ⊥)
    (hgt : g x₀ ≠ ⊤) (v : V) :
    concaveImageBifun (convexAdjointBifun Bu Bx F) (concaveConj Bx g) v ≠ ⊤ := by
  obtain ⟨r, hr⟩ := EReal.exists_coe_of_ne_bot_of_lt_top hgb (lt_top_iff_ne_top.2 hgt)
  have hbound : ∀ y : Y, concaveConj Bx g y + convexAdjointBifun Bu Bx F y v
      ≤ F u₀ x₀ + ((Bu u₀ v - r : ℝ) : EReal) := by
    intro y
    have h1 : concaveConj Bx g y ≤ ((Bx x₀ y : ℝ) : EReal) - g x₀ := concaveConj_le_sub Bx g x₀ y
    have h2 : convexAdjointBifun Bu Bx F y v ≤ F u₀ x₀ + ((Bu u₀ v - Bx x₀ y : ℝ) : EReal) :=
      iInf_le _ (u₀, x₀)
    refine le_trans (add_le_add h1 h2) (le_of_eq ?_)
    rw [hr, ← EReal.coe_sub, add_left_comm, ← EReal.coe_add]
    congr 2
    ring
  exact ne_top_of_le_ne_top (EReal.add_ne_top hF (EReal.coe_ne_top _)) (iSup_le hbound)

/-- **The main step of $\langle Ff, g^* \rangle = \langle f, F^* g^* \rangle$.** Let $U, V$ and
$X, Y$ be pairs of real vector spaces, each pair with a bilinear pairing, let $F$ be a
bifunction from $U$ to $X$, let $f$ be a proper function on $U$, and let $g$ be a function on
$X$. Let $F(u_0, x_0) < +\infty$ and let $g(x_0)$ be finite for some $(u_0, x_0)$. Then the
supremum side of $\langle F_*^* f^*, g \rangle$ is minus the infimum side of
$\langle f, F^* g^* \rangle$.

Both sides unwind to the same double extremum over $V \times Y$, term by term $\langle F^* y,
g^* \rangle - f^*(v) = (g^*(y) + (F^* y)(v)) - f^*(v)$. Here $F^* g^*$ is the concave image
`ConvexAnalysis.concaveImageBifun`, and $\langle F_*^* f^*, g \rangle$ is taken with respect to
the flipped pairing of $Y$ and $X$. -/
theorem fenchelSup_imageBifun_lowerAdjointBifun (hf : ProperConvex f) {u₀ : U} {x₀ : X}
    (hF : F u₀ x₀ ≠ ⊤) (hgb : g x₀ ≠ ⊥) (hgt : g x₀ ≠ ⊤) :
    fenchelSup Bx.flip (imageBifun (lowerAdjointBifun Bu Bx F) (convexConj Bu f)) g
      = -(fenchelInf Bu f (concaveImageBifun (convexAdjointBifun Bu Bx F) (concaveConj Bx g))) := by
  have hane : ∀ v : V, convexConj Bu f v ≠ ⊥ := fun v => convexConj_ne_bot hf.convexDom_nonempty v
  have hcne : ∀ (y : Y) (v : V), convexAdjointBifun Bu Bx F y v ≠ ⊤ :=
    fun y v => convexAdjointBifun_ne_top hF Bu Bx y v
  have hL : fenchelSup Bx.flip (imageBifun (lowerAdjointBifun Bu Bx F) (convexConj Bu f)) g
      = ⨆ y : Y, ⨆ v : V,
        (concaveConj Bx g y - (convexConj Bu f v - convexAdjointBifun Bu Bx F y v)) := by
    rw [fenchelSup_apply]
    refine iSup_congr fun y => ?_
    rw [LinearMap.flip_flip]
    have hH : imageBifun (lowerAdjointBifun Bu Bx F) (convexConj Bu f) y
        = ⨅ v : V, (convexConj Bu f v - convexAdjointBifun Bu Bx F y v) := rfl
    rw [hH, EReal.sub_iInf]
  have hR : -(fenchelInf Bu f (concaveImageBifun (convexAdjointBifun Bu Bx F) (concaveConj Bx g)))
      = ⨆ v : V, ⨆ y : Y,
        ((concaveConj Bx g y + convexAdjointBifun Bu Bx F y v) - convexConj Bu f v) := by
    rw [fenchelInf_apply, EReal.neg_iInf]
    refine iSup_congr fun v => ?_
    rw [EReal.neg_sub_comm (.inl (hane v))
        (.inr (concaveImageBifun_convexAdjointBifun_ne_top Bu Bx hF hgb hgt v)),
      concaveImageBifun_apply, EReal.iSup_sub_of_ne_bot _ (hane v)]
  rw [hL, hR, iSup_comm]
  exact iSup_congr fun v => iSup_congr fun y => EReal.sub_sub_eq_add_sub (hane v) (hcne y v)

omit [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X] in
/-- If $F$ and $f$ never take the value $-\infty$, $f$ is proper, and $F(u_0, x_0) < +\infty$ and
$f(u_0) < +\infty$ for some $(u_0, x_0)$, then the image $Ff$ is not identically $+\infty$. -/
theorem convexDom_imageBifun_nonempty (hbF : ∀ u x, F u x ≠ ⊥) (hf : ProperConvex f) {u₀ : U}
    {x₀ : X}
    (hF : F u₀ x₀ ≠ ⊤) (hfu : f u₀ ≠ ⊤) : (convexDom (imageBifun F f)).Nonempty := by
  refine ⟨x₀, ?_⟩
  have hle : imageBifun F f x₀ ≤ f u₀ + F u₀ x₀ := iInf_le _ u₀
  have hne : imageBifun F f x₀ ≠ ⊤ := ne_top_of_le_ne_top
    ((EReal.add_ne_top_iff_ne_top₂ (hf.ne_bot u₀) (hbF u₀ x₀)).2 ⟨hfu, hF⟩) hle
  exact lt_top_iff_ne_top.2 hne

/-- Let $F$ never take the value $-\infty$, let $f$ be proper, let $g$ have nonempty concave
effective domain, and let $F(u_0, x_0) < +\infty$ and $f(u_0) < +\infty$ for some $(u_0, x_0)$.
If for every $y$ the functions $f$ and $u \mapsto -\langle Fu, y \rangle$ add exactly, then the
supremum side of $\langle F_*^* f^*, g \rangle$ is minus the infimum side of
$\langle Ff, g^* \rangle$. This is `ConvexAnalysis.fenchelSup_convexConj_eq_neg_fenchelInf`
composed with `ConvexAnalysis.convexConj_imageBifun`. -/
theorem fenchelSup_imageBifun_lowerAdjointBifun_eq_neg (hbF : ∀ u x, F u x ≠ ⊥)
    (hf : ProperConvex f)
    (hgd : (concaveDom g).Nonempty) {u₀ : U} {x₀ : X} (hF : F u₀ x₀ ≠ ⊤) (hfu : f u₀ ≠ ⊤)
    (hex : ∀ y : Y, IsExactSum Bu f (fun u => -(bracket Bx F u y))) :
    fenchelSup Bx.flip (imageBifun (lowerAdjointBifun Bu Bx F) (convexConj Bu f)) g
      = -(fenchelInf Bx (imageBifun F f) (concaveConj Bx g)) := by
  have h38 : convexConj Bx (imageBifun F f)
      = imageBifun (lowerAdjointBifun Bu Bx F) (convexConj Bu f) :=
    funext fun y => convexConj_imageBifun hbF hf (hex y)
  rw [← h38]
  exact fenchelSup_convexConj_eq_neg_fenchelInf Bx (convexDom_imageBifun_nonempty hbF hf hF hfu) hgd

/-- **Adjoints move across the inner product**, $\langle Ff, g^* \rangle = \langle f, F^* g^*
\rangle$. Let $U, V$ and $X, Y$ be pairs of real vector spaces, each pair with a bilinear
pairing, let $F$ be a bifunction from $U$ to $X$ that never takes the value $-\infty$, let $f$
be a proper function on $U$, and let $g$ be a function on $X$ with nonempty concave effective
domain. Let $F(u_0, x_0) < +\infty$, $f(u_0) < +\infty$ and $g(x_0)$ finite for some
$(u_0, x_0)$, and for every $y \in Y$ let $f$ and $u \mapsto -\langle Fu, y \rangle$ add
exactly. Then the infimum sides agree:
$$\inf_y \{ (Ff)^*(y) - g^*(y) \} = \inf_v \{ f^*(v) - (F^* g^*)(v) \}.$$
Each side is Rockafellar's inner product as soon as the corresponding inner product exists.

Rockafellar's route is $\langle Ff, g^* \rangle = \langle f, F^* g^* \rangle = -\langle f^*, F_*
g \rangle = -\langle F_*^* f^*, g \rangle$. The last step is
`ConvexAnalysis.fenchelSup_imageBifun_lowerAdjointBifun`, and the other bridge is
`ConvexAnalysis.convexConj_imageBifun`. The book's relative-interior hypothesis is replaced by
the exactness hypothesis together with the common point $(u_0, x_0)$ at which $f$, $F$ and $g$
are finite. -/
theorem fenchelInf_imageBifun_eq_fenchelInf_concaveImageBifun (hbF : ∀ u x, F u x ≠ ⊥)
    (hf : ProperConvex f) (hgd : (concaveDom g).Nonempty) {u₀ : U} {x₀ : X} (hF : F u₀ x₀ ≠ ⊤)
    (hfu : f u₀ ≠ ⊤) (hgb : g x₀ ≠ ⊥) (hgt : g x₀ ≠ ⊤)
    (hex : ∀ y : Y, IsExactSum Bu f (fun u => -(bracket Bx F u y))) :
    fenchelInf Bx (imageBifun F f) (concaveConj Bx g)
      = fenchelInf Bu f (concaveImageBifun (convexAdjointBifun Bu Bx F) (concaveConj Bx g)) := by
  have h1 := fenchelSup_imageBifun_lowerAdjointBifun_eq_neg hbF hf hgd hF hfu hex
  rw [fenchelSup_imageBifun_lowerAdjointBifun hf hF hgb hgt] at h1
  have h2 := congrArg (fun z : EReal => -z) h1
  simpa using h2.symm

end AdjointAcross

/-! ### Right scalar multiplication -/

section SmulRightBifun

variable {U X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]
variable [AddCommGroup Y] [Module ℝ Y] {F : Bifun U X} {l : ℝ}

/-- Let $F$ be a bifunction from $U$ to $X$ and $\lambda \in \mathbb{R}$. The **right scalar
multiple** $F \lambda$ is the bifunction with $(F \lambda) u = (Fu) \lambda$ for each $u$, where
$(f \lambda)(x) = \lambda f(\lambda^{-1} x)$ for $\lambda > 0$.

The right scalar multiple of a function is `ConvexAnalysis.smulRight`, defined through the
scaled epigraph $\lambda \operatorname{epi} f$. -/
noncomputable def smulRightBifun (F : Bifun U X) (l : ℝ) : Bifun U X := fun u => smulRight (F u) l

omit [AddCommGroup U] [Module ℝ U] in
/-- The slice of $F \lambda$ at $u$ is the right scalar multiple $(Fu) \lambda$. -/
theorem smulRightBifun_apply (F : Bifun U X) (l : ℝ) (u : U) :
    smulRightBifun F l u = smulRight (F u) l := rfl

/-- The linear map $(u, x) \mapsto (\lambda u, x)$ on $U \times X$. -/
def scaleFst (X : Type*) [AddCommGroup X] [Module ℝ X] (l : ℝ) : U × X →ₗ[ℝ] U × X :=
  LinearMap.prod (l • LinearMap.fst ℝ U X) (LinearMap.snd ℝ U X)

/-- The map `ConvexAnalysis.scaleFst` sends $(u, x)$ to $(\lambda u, x)$. -/
@[simp] theorem scaleFst_apply (l : ℝ) (p : U × X) : scaleFst X l p = (l • p.1, p.2) := rfl

/-- For $\lambda > 0$ the graph function of $F \lambda$ is the right scalar multiple, by $\lambda$,
of the function $(u, x) \mapsto F(\lambda u, x)$. This is the linear change of variables $(u, x,
\mu) \mapsto (u, \lambda x, \lambda \mu)$ of Rockafellar's proof. -/
theorem graphFn_smulRightBifun (hl : 0 < l) (F : Bifun U X) :
    graphFn (smulRightBifun F l) = smulRight (compLin (graphFn F) (scaleFst X l)) l := by
  funext p
  rw [smulRight_apply_pos hl]
  change smulRight (F p.1) l p.2 = _
  rw [smulRight_apply_pos hl, compLin_apply, scaleFst_apply]
  congr 2
  exact (smul_inv_smul₀ hl.ne' p.1).symm

/-- **$F \lambda$ is convex when $F$ is**, for every $\lambda > 0$. -/
theorem convexBifun_smulRightBifun (hl : 0 < l) (hF : ConvexBifun F) :
    ConvexBifun (smulRightBifun F l) := by
  rw [ConvexBifun, graphFn_smulRightBifun hl F]
  exact convexFn_smulRight l (convexFn_compLin _ hF)

omit [AddCommGroup U] [Module ℝ U] in
/-- **The inner product scales with the bifunction.** For $\lambda > 0$, every bifunction $F$ from
$U$ to $X$, $u \in U$ and $y \in Y$, $\langle (F \lambda) u, y \rangle = \lambda \langle Fu, y
\rangle$. This is the conjugation rule `ConvexAnalysis.convexConj_smulRight`, applied to each
slice. -/
theorem bracket_smulRightBifun (hl : 0 < l) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (F : Bifun U X) (u : U) :
    bracket Bx (smulRightBifun F l) u = fun y => (l : EReal) * bracket Bx F u y :=
  convexConj_smulRight hl Bx (F u)

end SmulRightBifun

section SmulRightBifunAdjoint

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y] {l : ℝ}

/-- **The adjoint of a right scalar multiple.** Let $U, V$ and $X, Y$ be pairs of real vector
spaces, each pair with a bilinear pairing, let $F$ be a bifunction from $U$ to $X$, and let
$\lambda > 0$. Then for all $y \in Y$ and $v \in V$
$$((F \lambda)^* y)(v) = ((F^* y) \lambda)(v),$$
so $(F \lambda)^* = F^* \lambda$.

Right scalar multiplication commutes with taking adjoints, with no hypothesis beyond
$\lambda > 0$: the infimum that defines $((F \lambda)^* y)(v)$ becomes the one that defines
$((F^* y) \lambda)(v)$ under the substitution $x \mapsto \lambda x$. -/
theorem convexAdjointBifun_smulRightBifun (hl : 0 < l) (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (F : Bifun U X) (y : Y) (v : V) :
    convexAdjointBifun Bu Bx (smulRightBifun F l) y v
        = smulRight (convexAdjointBifun Bu Bx F y) l v := by
  have hl0 : l ≠ 0 := ne_of_gt hl
  have hsurj : Function.Surjective (fun p : U × X => (p.1, l • p.2)) := fun q =>
    ⟨(q.1, l⁻¹ • q.2), by rw [Prod.mk.injEq]; exact ⟨rfl, smul_inv_smul₀ hl0 q.2⟩⟩
  rw [smulRight_apply_pos hl, convexAdjointBifun_apply, convexAdjointBifun_apply,
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

/-- Let $F$ be a bifunction from $U$ to $X$ and $G$ a bifunction from $X$ to $Y$. Their **product**
$GF$ is the bifunction from $U$ to $Y$ with
$$((GF) u)(y) = \inf_x \{ (Fu)(x) + (Gx)(y) \}.$$

When $F$ and $G$ are the convex indicator bifunctions of linear maps $A$ and $B$, $GF$ is the
convex indicator bifunction of $B A$. -/
noncomputable def compBifun (G : Bifun X Y) (F : Bifun U X) : Bifun U Y :=
  fun u y => ⨅ x, F u x + G x y

/-- The product $GF$ has the value $((GF) u)(y) = \inf_x \{ (Fu)(x) + (Gx)(y) \}$. -/
theorem compBifun_apply (G : Bifun X Y) (F : Bifun U X) (u : U) (y : Y) :
    compBifun G F u y = ⨅ x, F u x + G x y := rfl

/-- Let $G$ be a bifunction from $Y$ to $X$ and $F$ a bifunction from $X$ to $U$. Their **concave
product** is the bifunction from $Y$ to $U$ with the same formula as `ConvexAnalysis.compBifun`,
a supremum in place of the infimum: $y \mapsto (u \mapsto \sup_x \{ (Gy)(x) + (Fx)(u) \})$. -/
noncomputable def concaveCompBifun (G : Bifun Y X) (F : Bifun X U) : Bifun Y U :=
  fun y u => ⨆ x, G y x + F x u

/-- The concave product of $G$ and $F$ has the value $\sup_x \{ (Gy)(x) + (Fx)(u) \}$ at $(y, u)$.
-/
theorem concaveCompBifun_apply (G : Bifun Y X) (F : Bifun X U) (y : Y) (u : U) :
    concaveCompBifun G F y u = ⨆ x, G y x + F x u := rfl

/-- **The inverse of a product is the product of the inverses** in the opposite order. Let $F$ be a
bifunction from $U$ to $X$ and $G$ a bifunction from $X$ to $Y$, neither of which takes the
value $-\infty$. Then
$$(GF)_* = F_* G_*,$$
where the right side is the concave product $((F_* G_*) y)(u) = \sup_x \{ (G_* y)(x) + (F_*
x)(u) \}$. This is part of Theorem 38.5 of [rockafellar1970convex]. -/
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

/-- The linear map $((u, y), x) \mapsto (u, x)$ from $(U \times Y) \times X$ to $U \times X$. -/
def compLeft (U X Y : Type*) [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]
    [AddCommGroup Y] [Module ℝ Y] : (U × Y) × X →ₗ[ℝ] U × X :=
  LinearMap.prod (LinearMap.fst ℝ U Y ∘ₗ LinearMap.fst ℝ (U × Y) X) (LinearMap.snd ℝ (U × Y) X)

/-- The map `ConvexAnalysis.compLeft` sends $((u, y), x)$ to $(u, x)$. -/
@[simp] theorem compLeft_apply (q : (U × Y) × X) : compLeft U X Y q = (q.1.1, q.2) := rfl

/-- The linear map $((u, y), x) \mapsto (x, y)$ from $(U \times Y) \times X$ to $X \times Y$. -/
def compRight (U X Y : Type*) [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]
    [AddCommGroup Y] [Module ℝ Y] : (U × Y) × X →ₗ[ℝ] X × Y :=
  LinearMap.prod (LinearMap.snd ℝ (U × Y) X) (LinearMap.snd ℝ U Y ∘ₗ LinearMap.fst ℝ (U × Y) X)

/-- The map `ConvexAnalysis.compRight` sends $((u, y), x)$ to $(x, y)$. -/
@[simp] theorem compRight_apply (q : (U × Y) × X) : compRight U X Y q = (q.2, q.1.2) := rfl

/-- **A product of convex bifunctions is convex.** Let $F$ be a convex bifunction from $U$ to $X$
and $G$ a convex bifunction from $X$ to $Y$, neither of which takes the value $-\infty$. Then
$GF$ is convex.

The function $(u, x, y) \mapsto (Fu)(x) + (Gx)(y)$ is convex on $U \times X \times Y$, and the
graph function of $GF$ is its image under the projection $(u, x, y) \mapsto (u, y)$. -/
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
/-- For a bifunction $F$ from $U$ to $X$ and $v \in V$, the concave inner product
$x \mapsto \langle v, F_* x \rangle$ is the image $F \ell$ of the linear function
$\ell(u) = \langle u, v \rangle$ under $F$. Both sides are
$\inf_u \{ \langle u, v \rangle + (Fu)(x) \}$; the only step is $-(-(Fu)(x)) = (Fu)(x)$. -/
theorem concaveBracket_inverseBifun_eq_imageBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (F : Bifun U X) (v : V) :
    concaveBracket Bu.flip (inverseBifun F) v = imageBifun F fun u => ((Bu u v : ℝ) : EReal) := by
  funext x
  rw [concaveBracket_apply, imageBifun_apply]
  refine iInf_congr fun u => ?_
  rw [inverseBifun_apply, LinearMap.flip_apply]
  change ((Bu u v : ℝ) : EReal) + -(-(F u x)) = _
  rw [neg_neg]

/-- Let $F$ be a bifunction from $U$ to $X$ that never takes the value $-\infty$. Then for $v \in V$
and $w \in W$ the conjugate of $x \mapsto \langle v, F_* x \rangle$ at $w$ is $-(F^* w)(v)$.
This turns the dual value in Fenchel's duality theorem into the adjoint of $F$; it is
`ConvexAnalysis.convexConj_imageBifun_eq_iSup` for a linear $f$. -/
theorem convexConj_concaveBracket_inverseBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] W →ₗ[ℝ] ℝ)
    (hbF : ∀ u x, F u x ≠ ⊥) (v : V) (w : W) :
    convexConj Bx (concaveBracket Bu.flip (inverseBifun F) v) w =
        -(convexAdjointBifun Bu Bx F w v) := by
  rw [concaveBracket_inverseBifun_eq_imageBifun,
    convexConj_imageBifun_eq_iSup hbF (fun _ => EReal.coe_ne_bot _),
    convexAdjointBifun_eq_concaveConj_bracket, concaveConj_apply, EReal.neg_iInf]
  exact iSup_congr fun u => (EReal.neg_coe_sub _ _).symm

omit [AddCommGroup X] [Module ℝ X] in
/-- **The primal problem behind the adjoint of a product.** Let $F$ be a bifunction from $U$ to $X$
and $G$ a bifunction from $X$ to $Y$, and let $z \in Z$ and $v \in V$. If
$\langle v, F_* x \rangle > -\infty$ and $\langle Gx, z \rangle < +\infty$ for every $x$, then
$$((GF)^* z)(v) = \inf_x \{ \langle v, F_* x \rangle - \langle Gx, z \rangle \}.$$

This is the whole extended-real content of Rockafellar's proof. The triple infimum that defines
$((GF)^* z)(v)$ is reindexed as an infimum over $x$, then $u$, then $y$, and the inner double
infimum splits because neither half is $-\infty$. This is the properness that Fenchel's duality
theorem demands. -/
theorem convexAdjointBifun_compBifun_eq_iInf (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (By : Y →ₗ[ℝ] Z →ₗ[ℝ] ℝ)
    (F : Bifun U X) (G : Bifun X Y) {z : Z} {v : V}
    (hfb : ∀ x, concaveBracket Bu.flip (inverseBifun F) v x ≠ ⊥)
    (hgt : ∀ x, bracket By G x z ≠ ⊤) :
    convexAdjointBifun Bu By (compBifun G F) z v
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
  rw [convexAdjointBifun_apply, iInf_prod]
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

/-- **The adjoint of a product is the product of the adjoints.** Let $U, V$, $X, W$ and $Y, Z$ be
pairs of real vector spaces, each pair with a bilinear pairing. Let $F$ be a bifunction from $U$
to $X$ that never takes the value $-\infty$, let $G$ be a bifunction from $X$ to $Y$, and let
$z \in Z$ and $v \in V$. Let the functions $x \mapsto \langle v, F_* x \rangle$ and
$x \mapsto -\langle Gx, z \rangle$ add exactly. Then
$$((GF)^* z)(v) = ((F^* G^*) z)(v) = \sup_w \{ (G^* z)(w) + (F^* w)(v) \},$$
where $F^* G^*$ is the concave product. This is Theorem 38.5 of [rockafellar1970convex].

The proof is Rockafellar's: Fenchel's duality theorem for $f(x) = \langle v, F_* x \rangle$ and
$g(x) = \langle Gx, z \rangle$, with `ConvexAnalysis.convexAdjointBifun_compBifun_eq_iInf` for
the primal side. His condition that the relative interiors of $\operatorname{dom} F_*$ and
$\operatorname{dom} G$ have a point in common is replaced by the exactness hypothesis
(`ConvexAnalysis.IsExactSum`). There is one instance for each $(z, v)$, since $f$ and $g$ depend
on them, where his single condition does not. Like `ConvexAnalysis.convexConj_imageBifun`, the
hypothesis contains the properness that selects the main case; his degenerate cases
$z \notin \operatorname{dom} G^*$ and $v \notin \operatorname{dom} F_*^*$ are those where $f$ or
$g$ fails to be proper. -/
theorem convexAdjointBifun_compBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] W →ₗ[ℝ] ℝ)
    (By : Y →ₗ[ℝ] Z →ₗ[ℝ] ℝ) (hbF : ∀ u x, F u x ≠ ⊥) {z : Z} {v : V}
    (hex : IsExactSum Bx (concaveBracket Bu.flip (inverseBifun F) v)
      (fun x => -(bracket By G x z))) :
    convexAdjointBifun Bu By (compBifun G F) z v
      = concaveCompBifun (convexAdjointBifun Bx By G) (convexAdjointBifun Bu Bx F) z v := by
  have hex' : IsExactSum Bx (concaveBracket Bu.flip (inverseBifun F) v)
      (-fun x => bracket By G x z) := hex
  have hgt : ∀ x, bracket By G x z ≠ ⊤ := fun x hx =>
    hex'.properConvex_right.ne_bot x (by simp [Pi.neg_apply, hx])
  rw [convexAdjointBifun_compBifun_eq_iInf Bu By F G hex'.properConvex_left.ne_bot hgt,
    fenchel_duality hex', concaveCompBifun_apply]
  refine iSup_congr fun w => ?_
  rw [convexConj_concaveBracket_inverseBifun Bu Bx hbF v w,
      ← convexAdjointBifun_eq_concaveConj_bracket]
  change _ + - -(convexAdjointBifun Bu Bx F w v) = _
  rw [neg_neg]

/-- **The adjoint of a product, for the lower adjoints.** Let $U, V$, $X, W$ and $Y, Z$ be pairs of
real vector spaces, each pair with a bilinear pairing. Let $F$ be a bifunction from $U$ to $X$
that never takes the value $-\infty$, with $F(u_0, x_0) < +\infty$ for some $(u_0, x_0)$, and
let $G$ be a bifunction from $X$ to $Y$ with $G(x_1, y_1) < +\infty$ for some $(x_1, y_1)$. Let
$z \in Z$ and $v \in V$, and let $x \mapsto \langle v, F_* x \rangle$ and
$x \mapsto -\langle Gx, z \rangle$ add exactly. Then
$$((GF)_*^* v)(z) = ((G_*^* F_*^*) v)(z) = \inf_w \{ (F_*^* v)(w) + (G_*^* w)(z) \}.$$
This is part of Theorem 38.5 of [rockafellar1970convex].

Inversion reverses the order twice, so the product on the right is taken in the same order as
$GF$, and both sides are convex bifunctions; no concave product is needed. The two finiteness
hypotheses let the negation split across the sum. -/
theorem lowerAdjointBifun_compBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] W →ₗ[ℝ] ℝ)
    (By : Y →ₗ[ℝ] Z →ₗ[ℝ] ℝ) (hbF : ∀ u x, F u x ≠ ⊥) {u₀ : U} {x₀ : X} (hFp : F u₀ x₀ ≠ ⊤)
    {x₁ : X} {y₁ : Y} (hGp : G x₁ y₁ ≠ ⊤) {z : Z} {v : V}
    (hex : IsExactSum Bx (concaveBracket Bu.flip (inverseBifun F) v)
      (fun x => -(bracket By G x z))) :
    lowerAdjointBifun Bu By (compBifun G F) v z
      = compBifun (lowerAdjointBifun Bx By G) (lowerAdjointBifun Bu Bx F) v z := by
  rw [lowerAdjointBifun_apply, convexAdjointBifun_compBifun Bu Bx By hbF hex,
      concaveCompBifun_apply,
    EReal.neg_iSup, compBifun_apply]
  refine iInf_congr fun w => ?_
  have h : -(convexAdjointBifun Bx By G z w + convexAdjointBifun Bu Bx F w v)
      = -(convexAdjointBifun Bx By G z w) + -(convexAdjointBifun Bu Bx F w v) :=
    EReal.neg_add (.inr (convexAdjointBifun_ne_top hFp Bu Bx w v))
      (.inl (convexAdjointBifun_ne_top hGp Bx By z w))
  rw [h, lowerAdjointBifun_apply, lowerAdjointBifun_apply, add_comm]

/-- **The supremum in $((F^* G^*) z)(v)$ is attained.** Under the hypotheses of
`ConvexAnalysis.convexAdjointBifun_compBifun`, there is $w \in W$ with
$(G^* z)(w) + (F^* w)(v) = ((GF)^* z)(v)$. -/
theorem exists_convexAdjointBifun_compBifun_eq (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] W →ₗ[ℝ] ℝ)
    (By : Y →ₗ[ℝ] Z →ₗ[ℝ] ℝ) (hbF : ∀ u x, F u x ≠ ⊥) {z : Z} {v : V}
    (hex : IsExactSum Bx (concaveBracket Bu.flip (inverseBifun F) v)
      (fun x => -(bracket By G x z))) :
    ∃ w : W, convexAdjointBifun Bx By G z w + convexAdjointBifun Bu Bx F w v
      = convexAdjointBifun Bu By (compBifun G F) z v := by
  have hex' : IsExactSum Bx (concaveBracket Bu.flip (inverseBifun F) v)
      (-fun x => bracket By G x z) := hex
  have hgt : ∀ x, bracket By G x z ≠ ⊤ := fun x hx =>
    hex'.properConvex_right.ne_bot x (by simp [Pi.neg_apply, hx])
  obtain ⟨w, hw⟩ := exists_concaveConj_sub_convexConj_eq hex'
  refine ⟨w, ?_⟩
  rw [convexAdjointBifun_compBifun_eq_iInf Bu By F G hex'.properConvex_left.ne_bot hgt, ← hw,
    convexConj_concaveBracket_inverseBifun Bu Bx hbF v w,
        ← convexAdjointBifun_eq_concaveConj_bracket]
  change _ = _ + - -(convexAdjointBifun Bu Bx F w v)
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

/-- **$(G_*^* F_*^*)_*^* = GF$ in the closed case.** Let $U$, $X$ and $Y$ be locally convex real
topological vector spaces, paired with $V$, $W$ and $Z$ by pairings compatible with their
topologies. Let $F$ from $U$ to $X$ and $G$ from $X$ to $Y$ be bifunctions whose graph functions
are closed proper convex, and let $u \in U$ and $y \in Y$. Let the functions $w \mapsto \inf_v
\{ \langle u, v \rangle + (F_*^* v)(w) \}$ and $w \mapsto -\langle G_*^* w, y \rangle$ on $W$
add exactly. Then
$$((G_*^* F_*^*)_*^* u)(y) = ((GF) u)(y),$$
the outer lower adjoint taken with respect to the flipped pairings. The rest of the closed case
follows from this identity.

This is `ConvexAnalysis.lowerAdjointBifun_compBifun` for $F_*^*$ and $G_*^*$, whose own lower
adjoints are $F$ and $G$ again. The exactness hypothesis, one instance for each $(u, y)$,
replaces Rockafellar's condition that the relative interiors of $\operatorname{dom} F^*$ and
$\operatorname{dom} G_*^*$ have a point in common. -/
theorem lowerAdjointBifun_compBifun_lowerAdjointBifun
    (hF : ClosedProperConvexFn (graphFn F)) (hG : ClosedProperConvexFn (graphFn G))
    {u : U} {y : Y}
    (hex : IsExactSum Bx.flip (concaveBracket Bu (inverseBifun (lowerAdjointBifun Bu Bx F)) u)
      (fun w => -(bracket By.flip (lowerAdjointBifun Bx By G) w y))) :
    lowerAdjointBifun Bu.flip By.flip
        (compBifun (lowerAdjointBifun Bx By G) (lowerAdjointBifun Bu Bx F)) u y
      = compBifun G F u y := by
  obtain ⟨p₀, hp₀⟩ := hF.proper.convexDom_nonempty
  obtain ⟨v₁, w₁, hFt⟩ := exists_lowerAdjointBifun_ne_top hF Bu Bx
  obtain ⟨w₂, z₂, hGt⟩ := exists_lowerAdjointBifun_ne_top hG Bx By
  rw [lowerAdjointBifun_compBifun Bu.flip Bx.flip By.flip
      (lowerAdjointBifun_ne_bot (F := F) hp₀.ne Bu Bx) hFt hGt hex,
    lowerAdjointBifun_lowerAdjointBifun_eq_convexClBifun (Bu := Bx) (Bx := By) hG.convex,
    lowerAdjointBifun_lowerAdjointBifun_eq_convexClBifun (Bu := Bu) (Bx := Bx) hF.convex,
    ClosedConvexBifun.convexClBifun_eq hG.closed, ClosedConvexBifun.convexClBifun_eq hF.closed]

/-- **A product of closed proper convex bifunctions is closed.** Under the hypotheses of
`ConvexAnalysis.lowerAdjointBifun_compBifun_lowerAdjointBifun` for every $u \in U$ and
$y \in Y$, the product $GF$ has a closed graph function. It is a lower adjoint, and a lower
adjoint is always closed. -/
theorem closedConvexBifun_compBifun (hF : ClosedProperConvexFn (graphFn F))
    (hG : ClosedProperConvexFn (graphFn G))
    (hex : ∀ (u : U) (y : Y), IsExactSum Bx.flip
      (concaveBracket Bu (inverseBifun (lowerAdjointBifun Bu Bx F)) u)
      (fun w => -(bracket By.flip (lowerAdjointBifun Bx By G) w y))) :
    ClosedConvexBifun (compBifun G F) := by
  have := isContinuousPairing_prodPairing_flip Bu.flip By.flip
  have hfun : compBifun G F = lowerAdjointBifun Bu.flip By.flip
      (compBifun (lowerAdjointBifun Bx By G) (lowerAdjointBifun Bu Bx F)) :=
    funext fun u => funext fun y =>
      (lowerAdjointBifun_compBifun_lowerAdjointBifun hF hG (hex u y)).symm
  rw [hfun]
  exact closedConvexBifun_lowerAdjointBifun

/-- **The infimum in $((GF) u)(y)$ is attained.** Under the hypotheses of
`ConvexAnalysis.lowerAdjointBifun_compBifun_lowerAdjointBifun` at $(u, y)$, there is $x \in X$
with $(Fu)(x) + (Gx)(y) = ((GF) u)(y)$. This is
`ConvexAnalysis.exists_convexAdjointBifun_compBifun_eq` for $F_*^*$ and $G_*^*$. -/
theorem exists_compBifun_eq (hF : ClosedProperConvexFn (graphFn F))
    (hG : ClosedProperConvexFn (graphFn G)) {u : U} {y : Y}
    (hex : IsExactSum Bx.flip (concaveBracket Bu (inverseBifun (lowerAdjointBifun Bu Bx F)) u)
      (fun w => -(bracket By.flip (lowerAdjointBifun Bx By G) w y))) :
    ∃ x : X, F u x + G x y = compBifun G F u y := by
  obtain ⟨p₀, hp₀⟩ := hF.proper.convexDom_nonempty
  obtain ⟨x, hx⟩ := exists_convexAdjointBifun_compBifun_eq Bu.flip Bx.flip By.flip
    (lowerAdjointBifun_ne_bot (F := F) hp₀.ne Bu Bx) hex
  refine ⟨x, ?_⟩
  have hFadj : convexAdjointBifun Bu.flip Bx.flip (lowerAdjointBifun Bu Bx F) x u = -(F u x) :=
    congrFun (congrFun (convexAdjointBifun_flip_lowerAdjointBifun hF.convex hF.closed) x) u
  have hGadj : convexAdjointBifun Bx.flip By.flip (lowerAdjointBifun Bx By G) y x = -(G x y) :=
    congrFun (congrFun (convexAdjointBifun_flip_lowerAdjointBifun hG.convex hG.closed) y) x
  have hcomp : convexAdjointBifun Bu.flip By.flip
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

/-- **$(GF)^* = \operatorname{cl}(F^* G^*)$ in the closed case**, stated for the lower adjoints as
$(GF)_*^* = \operatorname{cl}(G_*^* F_*^*)$. Let $U$, $V$, $X$, $Y$ and $Z$ be locally convex
real topological vector spaces with compatible pairings, and let $F$ from $U$ to $X$ and $G$
from $X$ to $Y$ be bifunctions whose graph functions are closed proper convex. If the exactness
hypothesis of `ConvexAnalysis.lowerAdjointBifun_compBifun_lowerAdjointBifun` holds for every
$(u, y)$, then
$$(GF)_*^* = \operatorname{cl}(G_*^* F_*^*).$$

$GF$ is the lower adjoint of $G_*^* F_*^*$, so $(GF)_*^*$ is the double lower adjoint of
$G_*^* F_*^*$, which is its closure. Rockafellar's $\operatorname{cl}(F^* G^*)$ is this identity
with the two negations moved outside. -/
theorem lowerAdjointBifun_compBifun_eq_convexClBifun (hF : ClosedProperConvexFn (graphFn F))
    (hG : ClosedProperConvexFn (graphFn G))
    (hex : ∀ (u : U) (y : Y), IsExactSum Bx.flip
      (concaveBracket Bu (inverseBifun (lowerAdjointBifun Bu Bx F)) u)
      (fun w => -(bracket By.flip (lowerAdjointBifun Bx By G) w y))) :
    lowerAdjointBifun Bu By (compBifun G F)
      = convexClBifun (compBifun (lowerAdjointBifun Bx By G) (lowerAdjointBifun Bu Bx F)) := by
  obtain ⟨p₀, hp₀⟩ := hF.proper.convexDom_nonempty
  obtain ⟨q₀, hq₀⟩ := hG.proper.convexDom_nonempty
  have hconv : ConvexBifun (compBifun (lowerAdjointBifun Bx By G) (lowerAdjointBifun Bu Bx F)) :=
    convexBifun_compBifun (lowerAdjointBifun_ne_bot (F := F) hp₀.ne Bu Bx)
      (lowerAdjointBifun_ne_bot (F := G) hq₀.ne Bx By)
      (convexBifun_lowerAdjointBifun Bu Bx F) (convexBifun_lowerAdjointBifun Bx By G)
  have hfun : compBifun G F = lowerAdjointBifun Bu.flip By.flip
      (compBifun (lowerAdjointBifun Bx By G) (lowerAdjointBifun Bu Bx F)) :=
    funext fun u => funext fun y =>
      (lowerAdjointBifun_compBifun_lowerAdjointBifun hF hG (hex u y)).symm
  have hbi := lowerAdjointBifun_lowerAdjointBifun_eq_convexClBifun (Bu := Bu.flip) (Bx := By.flip)
    (F := compBifun (lowerAdjointBifun Bx By G) (lowerAdjointBifun Bu Bx F)) hconv
  simp only [LinearMap.flip_flip] at hbi
  rw [hfun, hbi]

end CompBifunClosedAdjoint

/-! ### Infimal convolution in the first variable -/

section InfConvFstBifunDefs

variable {V Y : Type*} [AddCommGroup V]

/-- Let $V$ be an additive group and $Y$ a type. The **infimal convolute in the first variable**
$H_1 \boxdot H_2$ of two bifunctions $H_1, H_2$ from $V$ to $Y$ is the bifunction with
$$(H_1 \boxdot H_2)(v, y) = \bigl( H_1(\cdot, y) \mathbin{\square} H_2(\cdot, y) \bigr)(v),$$
the infimal convolution in the first variable, for each $y$ separately.

`ConvexAnalysis.infConvBifun` convolves in the second variable; this is its mirror under the
exchange of the variables (`ConvexAnalysis.infConvFstBifun_eq_flipBifun`). The lower adjoints
are combined by this operation (`ConvexAnalysis.lowerAdjointBifun_infConvFstBifun`). -/
noncomputable def infConvFstBifun (H₁ H₂ : Bifun V Y) : Bifun V Y :=
  fun v y => infConv (fun w => H₁ w y) (fun w => H₂ w y) v

/-- For each $y$, the function $v \mapsto (H_1 \boxdot H_2)(v, y)$ is the infimal convolution of
$H_1(\cdot, y)$ and $H_2(\cdot, y)$. -/
theorem infConvFstBifun_slice (H₁ H₂ : Bifun V Y) (y : Y) :
    (fun v => infConvFstBifun H₁ H₂ v y) = infConv (fun w => H₁ w y) (fun w => H₂ w y) := rfl

/-- **The first-variable convolute is the second-variable convolute with the variables exchanged.**
$H_1 \boxdot H_2$ is the flip of $\tilde H_1 \mathbin{\square} \tilde H_2$, where
$\tilde H(y, v) = H(v, y)$. Every property of $\boxdot$ follows from the corresponding property
of $\square$ through this identity. -/
theorem infConvFstBifun_eq_flipBifun (H₁ H₂ : Bifun V Y) :
    infConvFstBifun H₁ H₂ = flipBifun (infConvBifun (flipBifun H₁) (flipBifun H₂)) := rfl

/-- The infimal convolute in the first variable is commutative: $H_1 \boxdot H_2 = H_2 \boxdot H_1$.
-/
theorem infConvFstBifun_comm (H₁ H₂ : Bifun V Y) :
    infConvFstBifun H₁ H₂ = infConvFstBifun H₂ H₁ := by
  rw [infConvFstBifun_eq_flipBifun, infConvBifun_comm, ← infConvFstBifun_eq_flipBifun]

/-- The infimal convolute in the first variable is associative: $(H_1 \boxdot H_2) \boxdot H_3 = H_1
\boxdot (H_2 \boxdot H_3)$. -/
theorem infConvFstBifun_assoc (H₁ H₂ H₃ : Bifun V Y) :
    infConvFstBifun (infConvFstBifun H₁ H₂) H₃ = infConvFstBifun H₁ (infConvFstBifun H₂ H₃) := by
  simp only [infConvFstBifun_eq_flipBifun, flipBifun_flipBifun, infConvBifun_assoc]

/-- The inverse of a first-variable infimal convolute is the supremal convolute of the inverses:
$(H_1 \boxdot H_2)_* = H_{1*} \mathbin{\square} H_{2*}$. The change of sign exchanges the
infimum and the supremum. -/
theorem inverseBifun_infConvFstBifun (H₁ H₂ : Bifun V Y) :
    inverseBifun (infConvFstBifun H₁ H₂) = supConvBifun (inverseBifun H₁) (inverseBifun H₂) := by
  funext y v
  simp only [inverseBifun_apply, supConvBifun_apply, supConv, infConvFstBifun, neg_neg]

end InfConvFstBifunDefs

section InfConvFstBifunConvex

variable {V Y : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup Y] [Module ℝ Y]
variable {H₁ H₂ : Bifun V Y}

/-- Let $H_1$ and $H_2$ be convex bifunctions from $V$ to $Y$ that never take the value $-\infty$.
Then $H_1 \boxdot H_2$ is a convex bifunction: it is $H_1 \mathbin{\square} H_2$ with the two
variables exchanged. -/
theorem convexBifun_infConvFstBifun (hb₁ : ∀ v y, H₁ v y ≠ ⊥) (hb₂ : ∀ v y, H₂ v y ≠ ⊥)
    (hH₁ : ConvexBifun H₁) (hH₂ : ConvexBifun H₂) : ConvexBifun (infConvFstBifun H₁ H₂) :=
  convexBifun_flipBifun (convexBifun_infConvBifun (fun y v => hb₁ v y) (fun y v => hb₂ v y)
    (convexBifun_flipBifun hH₁) (convexBifun_flipBifun hH₂))

end InfConvFstBifunConvex

/-! ### The lower adjoint of a first-variable convolute -/

section LowerAdjointInfConvFst

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
variable [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]

/-- **The lower adjoint turns a first-variable convolute into a second-variable convolute.** Let
$U, V$ and $X, Y$ be pairs of real vector spaces, each pair with a bilinear pairing, let $H_1$
and $H_2$ be bifunctions from $V$ to $Y$, and let $u \in U$. Let the concave inner products
$y \mapsto \langle u, H_{1*} y \rangle$ and $y \mapsto \langle u, H_{2*} y \rangle$ on $Y$ add
exactly, with respect to the pairing of $Y$ with $X$. Then
$$(H_1 \boxdot H_2)_*^* u = H_{1*}^* u \mathbin{\square} H_{2*}^* u,$$
the lower adjoints taken with respect to the flipped pairings, from $U$ to $X$.

$H_*^*$ is the concave adjoint of $H_*$, and $(H_1 \boxdot H_2)_* = H_{1*} \mathbin{\square}
H_{2*}$ (`ConvexAnalysis.inverseBifun_infConvFstBifun`). So this is
`ConvexAnalysis.concaveAdjointBifun_supConvBifun`, the concave half of the adjoint of a
convolute. The exactness hypothesis, one instance for each $u$, replaces Rockafellar's
relative-interior condition. -/
theorem lowerAdjointBifun_infConvFstBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (H₁ H₂ : Bifun V Y) {u : U}
    (hex : IsExactSum Bx.flip (concaveBracket Bu (inverseBifun H₁) u)
      (concaveBracket Bu (inverseBifun H₂) u)) :
    lowerAdjointBifun Bu.flip Bx.flip (infConvFstBifun H₁ H₂) u
      = infConvBifun (lowerAdjointBifun Bu.flip Bx.flip H₁)
          (lowerAdjointBifun Bu.flip Bx.flip H₂) u := by
  simp only [lowerAdjointBifun_eq_concaveAdjointBifun, LinearMap.flip_flip,
    inverseBifun_infConvFstBifun]
  exact concaveAdjointBifun_supConvBifun Bu Bx _ _ hex

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

/-- **$(F_{1*}^* \boxdot F_{2*}^*)_*^* = F_1 \mathbin{\square} F_2$ in the closed case.** Let $U$
and $X$ be locally convex real topological vector spaces, paired with $V$ and $Y$ by pairings
compatible with their topologies. Let $F_1$ and $F_2$ be convex bifunctions from $U$ to $X$ with
closed graph functions, and let $u \in U$. Let the functions
$y \mapsto \langle u, (F_{1*}^*)_* y \rangle$ and $y \mapsto \langle u, (F_{2*}^*)_* y \rangle$
on $Y$ add exactly. Then
$$(F_{1*}^* \boxdot F_{2*}^*)_*^* u = (F_1 \mathbin{\square} F_2) u.$$
The rest of the closed case follows from this identity.

This is `ConvexAnalysis.lowerAdjointBifun_infConvFstBifun` for $F_{1*}^*$ and $F_{2*}^*$, whose
own lower adjoints are $F_1$ and $F_2$ again. The exactness hypothesis, one instance for each
$u$, replaces Rockafellar's condition that the relative interiors of $\operatorname{dom} F_1^*$
and $\operatorname{dom} F_2^*$ have a point in common. -/
theorem lowerAdjointBifun_infConvFstBifun_lowerAdjointBifun (hF₁ : ConvexBifun F₁)
    (hF₁cl : ClosedConvexBifun F₁) (hF₂ : ConvexBifun F₂) (hF₂cl : ClosedConvexBifun F₂) {u : U}
    (hex : IsExactSum Bx.flip
      (concaveBracket Bu (inverseBifun (lowerAdjointBifun Bu Bx F₁)) u)
      (concaveBracket Bu (inverseBifun (lowerAdjointBifun Bu Bx F₂)) u)) :
    lowerAdjointBifun Bu.flip Bx.flip
        (infConvFstBifun (lowerAdjointBifun Bu Bx F₁) (lowerAdjointBifun Bu Bx F₂)) u
      = infConvBifun F₁ F₂ u := by
  rw [lowerAdjointBifun_infConvFstBifun Bu Bx _ _ hex,
    lowerAdjointBifun_lowerAdjointBifun_eq_convexClBifun hF₁,
    lowerAdjointBifun_lowerAdjointBifun_eq_convexClBifun hF₂, hF₁cl.convexClBifun_eq,
        hF₂cl.convexClBifun_eq]

/-- **$F_1 \mathbin{\square} F_2$ is a lower adjoint.** Under the hypotheses of
`ConvexAnalysis.lowerAdjointBifun_infConvFstBifun_lowerAdjointBifun` for every $u \in U$, $F_1
\mathbin{\square} F_2 = (F_{1*}^* \boxdot F_{2*}^*)_*^*$. -/
theorem infConvBifun_eq_lowerAdjointBifun_infConvFstBifun (hF₁ : ConvexBifun F₁)
    (hF₁cl : ClosedConvexBifun F₁) (hF₂ : ConvexBifun F₂) (hF₂cl : ClosedConvexBifun F₂)
    (hex : ∀ u : U, IsExactSum Bx.flip
      (concaveBracket Bu (inverseBifun (lowerAdjointBifun Bu Bx F₁)) u)
      (concaveBracket Bu (inverseBifun (lowerAdjointBifun Bu Bx F₂)) u)) :
    infConvBifun F₁ F₂ = lowerAdjointBifun Bu.flip Bx.flip
      (infConvFstBifun (lowerAdjointBifun Bu Bx F₁) (lowerAdjointBifun Bu Bx F₂)) :=
  funext fun u =>
    (lowerAdjointBifun_infConvFstBifun_lowerAdjointBifun hF₁ hF₁cl hF₂ hF₂cl (hex u)).symm

/-- **An infimal convolute of closed convex bifunctions is closed.** Let $U$ and $X$ be locally
convex real topological vector spaces, paired with $V$ and $Y$ by pairings compatible with their
topologies. Let $F_1$ and $F_2$ be convex bifunctions from $U$ to $X$ with closed graph
functions. If for every $u \in U$ the functions $y \mapsto \langle u, (F_{1*}^*)_* y \rangle$
and $y \mapsto \langle u, (F_{2*}^*)_* y \rangle$ add exactly, then $F_1 \mathbin{\square} F_2$
has a closed graph function.

$F_1 \mathbin{\square} F_2$ is a lower adjoint
(`ConvexAnalysis.infConvBifun_eq_lowerAdjointBifun_infConvFstBifun`), and a lower adjoint is
always closed. -/
theorem closedConvexBifun_infConvBifun (hF₁ : ConvexBifun F₁) (hF₁cl : ClosedConvexBifun F₁)
    (hF₂ : ConvexBifun F₂) (hF₂cl : ClosedConvexBifun F₂)
    (hex : ∀ u : U, IsExactSum Bx.flip
      (concaveBracket Bu (inverseBifun (lowerAdjointBifun Bu Bx F₁)) u)
      (concaveBracket Bu (inverseBifun (lowerAdjointBifun Bu Bx F₂)) u)) :
    ClosedConvexBifun (infConvBifun F₁ F₂) := by
  have := isContinuousPairing_prodPairing_flip Bu.flip Bx.flip
  rw [infConvBifun_eq_lowerAdjointBifun_infConvFstBifun hF₁ hF₁cl hF₂ hF₂cl hex]
  exact closedConvexBifun_lowerAdjointBifun

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

/-- **$(F_1 \mathbin{\square} F_2)^* = \operatorname{cl}(F_1^* \mathbin{\square} F_2^*)$ in the
closed case**, stated for the lower adjoints as $(F_1 \mathbin{\square} F_2)_*^* =
\operatorname{cl}(F_{1*}^* \boxdot F_{2*}^*)$. Let $U$, $V$, $X$ and $Y$ be locally convex real
topological vector spaces with pairings compatible with the topologies on both sides, and let
$F_1$ and $F_2$ be bifunctions from $U$ to $X$ whose graph functions are closed proper convex.
If for every $u \in U$ the functions $y \mapsto \langle u, (F_{1*}^*)_* y \rangle$ and
$y \mapsto \langle u, (F_{2*}^*)_* y \rangle$ add exactly, then
$$(F_1 \mathbin{\square} F_2)_*^* = \operatorname{cl}(F_{1*}^* \boxdot F_{2*}^*).$$

$F_1 \mathbin{\square} F_2$ is the lower adjoint of $F_{1*}^* \boxdot F_{2*}^*$, so
$(F_1 \mathbin{\square} F_2)_*^*$ is the double lower adjoint of $F_{1*}^* \boxdot F_{2*}^*$,
which is its closure. The convolution on the right is in the first variable; it is what
Rockafellar's $F_1^* \mathbin{\square} F_2^*$ becomes when the two negations are moved outside. -/
theorem lowerAdjointBifun_infConvBifun_eq_convexClBifun (hF₁ : ClosedProperConvexFn (graphFn F₁))
    (hF₂ : ClosedProperConvexFn (graphFn F₂))
    (hex : ∀ u : U, IsExactSum Bx.flip
      (concaveBracket Bu (inverseBifun (lowerAdjointBifun Bu Bx F₁)) u)
      (concaveBracket Bu (inverseBifun (lowerAdjointBifun Bu Bx F₂)) u)) :
    lowerAdjointBifun Bu Bx (infConvBifun F₁ F₂)
      = convexClBifun
          (infConvFstBifun (lowerAdjointBifun Bu Bx F₁) (lowerAdjointBifun Bu Bx F₂)) := by
  obtain ⟨p₁, hp₁⟩ := hF₁.proper.convexDom_nonempty
  obtain ⟨p₂, hp₂⟩ := hF₂.proper.convexDom_nonempty
  have hconv : ConvexBifun
      (infConvFstBifun (lowerAdjointBifun Bu Bx F₁) (lowerAdjointBifun Bu Bx F₂)) :=
    convexBifun_infConvFstBifun (lowerAdjointBifun_ne_bot (F := F₁) hp₁.ne Bu Bx)
      (lowerAdjointBifun_ne_bot (F := F₂) hp₂.ne Bu Bx)
      (convexBifun_lowerAdjointBifun Bu Bx F₁) (convexBifun_lowerAdjointBifun Bu Bx F₂)
  have hbi := lowerAdjointBifun_lowerAdjointBifun_eq_convexClBifun (Bu := Bu.flip) (Bx := Bx.flip)
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
/-- **A slice of a product is the image of a slice**: $(GF) u = G(Fu)$. Both sides are
$y \mapsto \inf_x \{ (Fu)(x) + (Gx)(y) \}$, so the identity holds by definition. It makes every
statement about $\langle (GF) u, \cdot \rangle$ a statement about an image, and so a case of
`ConvexAnalysis.convexConj_imageBifun` and its form for the inner product. -/
theorem compBifun_slice (G : Bifun X Y) (F : Bifun U X) (u : U) :
    compBifun G F u = imageBifun G (F u) := rfl

/-- **The inner product $\langle Fu, G^* z \rangle$ exists.** Let $G$ be a bifunction from $X$ to
$Y$ that never takes the value $-\infty$, let the slice $Fu$ be proper, and let $Fu$ and
$x \mapsto -\langle Gx, z \rangle$ add exactly. Then the two sides of
$\langle Fu, G^* z \rangle$ agree.

Rockafellar derives the hypothesis, that the relative interiors of $\operatorname{dom}(Fu)$ and
$\operatorname{dom} G$ meet, from his condition on the relative interiors of
$\operatorname{dom} F_*$ and $\operatorname{dom} G$, by a calculus of relative interiors that he
leaves to the reader. Here it is the exactness hypothesis that the proof uses, one instance for
each $(u, z)$. -/
theorem hasFenchelPairing_convexAdjointBifun_slice (Bx : X →ₗ[ℝ] W →ₗ[ℝ] ℝ) (By : Y →ₗ[ℝ] Z →ₗ[ℝ] ℝ)
    (hbG : ∀ x y, G x y ≠ ⊥) {u : U} (hFu : ProperConvex (F u)) {z : Z}
    (hex : IsExactSum Bx (F u) (fun x => -(bracket By G x z))) :
    HasFenchelPairing Bx (F u) (convexAdjointBifun Bx By G z) :=
  hasFenchelPairing_convexAdjointBifun hbG hFu hex

/-- **An adjoint moves across the inner product at a slice.** Let $X, W$ and $Y, Z$ be pairs of real
vector spaces, each pair with a bilinear pairing. Let $F$ be a bifunction from $U$ to $X$ and
$G$ a bifunction from $X$ to $Y$ that never takes the value $-\infty$. Let $u \in U$ with $Fu$
proper, let $z \in Z$, and let $Fu$ and $x \mapsto -\langle Gx, z \rangle$ add exactly. Then
$$\langle (GF) u, z \rangle = \langle Fu, G^* z \rangle.$$

This is `ConvexAnalysis.convexConj_imageBifun_eq_fenchelPairing` at the slice $Fu$, since
$(GF) u = G(Fu)$. The other identity $\langle (GF) u, z \rangle = \langle u, F^* G^* z \rangle$
needs a relative interior; it is
`ConvexAnalysis.bracket_compBifun_eq_concaveBracket_concaveCompBifun` in
`Numlib.Analysis.Convex.Bifunction.Cofinite`. -/
theorem bracket_compBifun_eq_fenchelPairing (Bx : X →ₗ[ℝ] W →ₗ[ℝ] ℝ) (By : Y →ₗ[ℝ] Z →ₗ[ℝ] ℝ)
    (hbG : ∀ x y, G x y ≠ ⊥) {u : U} (hFu : ProperConvex (F u)) {z : Z}
    (hex : IsExactSum Bx (F u) (fun x => -(bracket By G x z))) :
    bracket By (compBifun G F) u z = fenchelPairing Bx (F u) (convexAdjointBifun Bx By G z) :=
  convexConj_imageBifun_eq_fenchelPairing hbG hFu hex

end CompBifunPairing

end ConvexAnalysis
