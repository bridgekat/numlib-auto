/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Saddle.Minimax

/-!
# The two conjugates of a saddle-function form a closure pair

Let $U$ be paired with $V$ and $X$ with $Y$, by bilinear pairings $\langle u, v \rangle$ and
$\langle x, y \rangle$. Let $F$ be a closed convex bifunction from $U$ to $X$, and let
$K : U \times Y \to [-\infty, +\infty]$ lie in the class $\Omega(F)$, so that $\langle Fu, y \rangle
\le K(u, y) \le \langle u, F^* y \rangle$ for all $(u, y)$. Here $\langle Fu, y \rangle = (Fu)^*(y)$
is the lower bracket and $\langle u, F^* y \rangle$ is the concave bracket of the adjoint $F^*$ of
$F$. The **lower conjugate** and the **upper conjugate** of $K$ are the functions on $V \times X$
$$\underline{K}^*(v, x) = \sup_y \inf_u \{\langle u, v \rangle + \langle x, y \rangle - K(u, y)\},
  \qquad \overline{K}^*(v, x) = \inf_u \sup_y
  \{\langle u, v \rangle + \langle x, y \rangle - K(u, y)\}.$$
This module shows that $\underline{K}^*$ and $\overline{K}^*$ are the two brackets of one convex
bifunction $F_*^*$ from $V$ to $Y$, the adjoint of the inverse bifunction $(F_* x)(u) = -F(u, x)$.
Therefore they form a **closure pair**: $\operatorname{cl}_1 \underline{K}^* = \overline{K}^*$ and
$\operatorname{cl}_2 \overline{K}^* = \underline{K}^*$. They are equivalent, they have a common
effective domain $C^* \times D^*$, and they agree wherever one coordinate lies in the relative
interior of its factor. That the two conjugates form a closure pair is Corollary 37.1.2 of
[rockafellar1970convex]. Because $\underline{K}^*(0, 0) = -\inf_y \sup_u K$ and
$\overline{K}^*(0, 0) = -\sup_u \inf_y K$, the condition $0 \in \operatorname{ri} C^*$ or
$0 \in \operatorname{ri} D^*$ implies that the saddle-value of $K$ exists.

The second half of the module computes the effective domains. The set $D^*$ is the projection of
$\operatorname{dom} F$ on $X$, and its support function is the supremum over $u \in
\operatorname{ri} (\operatorname{dom}_1 K)$ of the recession functions of the slices $K(u, \cdot)$.
This is Theorem 37.2 of [rockafellar1970convex]. The module
`Numlib.Analysis.Convex.Saddle.Existence` turns it into criteria for $0 \in \operatorname{int} D^*$,
for $0 \in \operatorname{int} C^*$, and for the existence of the saddle-value.

## Main results

* `ConvexAnalysis.saddleLagrangian_eq_concaveBracket`: the Lagrangian $L(v, x) = \inf_u \{\langle u,
  v \rangle + F(u, x)\}$ is the concave bracket $\langle v, F_* x \rangle$ of the inverse
  bifunction.
* `ConvexAnalysis.partialCl₁_lowerConjSaddle`, `ConvexAnalysis.partialCl₂_upperConjSaddle`,
  `ConvexAnalysis.saddleClass_conjSaddle`, `ConvexAnalysis.domSaddle_conjSaddle_eq`,
  `ConvexAnalysis.lowerConjSaddle_eq_upperConjSaddle_of_mem_relint_dom₁`: the two conjugates form a
  closure pair, their class is $\Omega(F_*^*)$, they have the same effective domain, and they agree
  over the relative interior.
* `ConvexAnalysis.properSaddleFn_saddleLagrangian`: the Lagrangian of a closed proper convex
  bifunction is a proper saddle-function.
* `ConvexAnalysis.hasSaddleValue_of_mem_relint_dom₁_lowerConjSaddle`,
  `ConvexAnalysis.exists_maximin_eq_coe_of_mem_relint_domSaddle`: if the origin lies in
  $\operatorname{ri} C^*$ or in $\operatorname{ri} D^*$, the saddle-value of $K$ exists, and if it
  lies in both, the saddle-value is finite.
* `ConvexAnalysis.dom₁_eq_convexDomBifun_of_mem_bifunSaddleClass`: every concave-convex
  $K \in \Omega(F)$ with $\operatorname{dom}_2 K \neq \emptyset$ has
  $\operatorname{dom}_1 K = \operatorname{dom} F$.
* `ConvexAnalysis.supportFn_dom₂_upperConjSaddle`: the support function of $D^*$ is $\delta^*(w \mid
  D^*) = \sup_{u \in \operatorname{ri} C} \sup_{y \in D} \{K(u, y + w) - K(u, y)\}$, with
  $C = \operatorname{dom}_1 K$ and $D = \operatorname{dom}_2 K$.

## Implementation notes

* The conjugates $\underline{K}^*$ and $\overline{K}^*$ live on $V \times X$, and the bifunction
  $F_*^*$ behind them goes from $V$ to $Y$. So every bracket lemma is used at the flipped pairings
  `Bu.flip` and `Bx.flip`, and the compatibility instances `ConvexAnalysis.IsCompatiblePairing` are
  required for the flipped pairings too.
* The one fact needed beyond the theory of brackets is the **biadjoint identity** $(F_*^*)^* = F_*$,
  which is `ConvexAnalysis.convexAdjointBifun_flip_lowerAdjointBifun` in
  `Numlib.Analysis.Convex.Extremum.Adjoint`. Since $F \mapsto F_*$ intertwines the convex and the
  concave adjoint, it is the involutivity of the adjoint read through that intertwining.
* The two halves of properness of the conjugate are of different depth. The condition
  $\operatorname{dom}_2 \overline{K}^* \neq \emptyset$ follows at once from the properness of the
  graph function of $F$. The condition $\operatorname{dom}_1 \overline{K}^* \neq \emptyset$ is the
  existence of an affine minorant of the graph function, and this is why the closedness of $F$ is a
  real hypothesis.
-/

namespace ConvexAnalysis

/-! ### The Lagrangian is the concave bracket of the inverse -/

section LagrangianBracket

variable {U V X : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]

/-- Let $U$ be paired with $V$ and let $F$ be a bifunction from $U$ to $X$. For all $v \in V$ and
$x \in X$, the concave bracket of the inverse bifunction $F_*$, taken with the flipped pairing,
is the Lagrangian of $F$:
$$\langle v, F_* x \rangle = L(v, x) = \inf_u \{\langle u, v \rangle + F(u, x)\}.$$
The identity is an unfolding of the definitions. -/
theorem concaveBracket_inverseBifun_eq_lagrangian (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (F : Bifun U X)
    (v : V) (x : X) :
    concaveBracket Bu.flip (inverseBifun F) v x = lagrangian Bu F v x := by
  rw [concaveBracket_apply, lagrangian_apply]
  refine iInf_congr fun u => ?_
  rw [inverseBifun_apply, sub_eq_add_neg, neg_neg, LinearMap.flip_apply]

/-- Let $U$ be paired with $V$ and let $F$ be a bifunction from $U$ to $X$. The Lagrangian of $F$,
read as a function on $V \times X$, is the concave bracket of the inverse bifunction $F_*$:
$$L(v, x) = \inf_u \{\langle u, v \rangle + F(u, x)\} = \langle v, F_* x \rangle
  \quad \text{for all } (v, x) \in V \times X.$$

This is `ConvexAnalysis.concaveBracket_inverseBifun_eq_lagrangian` in uncurried form. The
Lagrangian on $V \times X$ is `ConvexAnalysis.saddleLagrangian`, and the bracket is
`ConvexAnalysis.concaveBracket` for the flipped pairing `Bu.flip`. -/
theorem saddleLagrangian_eq_concaveBracket (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (F : Bifun U X) :
    saddleLagrangian Bu F
      = fun q : V × X => concaveBracket Bu.flip (inverseBifun F) q.1 q.2 :=
  funext fun q => (concaveBracket_inverseBifun_eq_lagrangian Bu F q.1 q.2).symm

end LagrangianBracket

/-! ### The two conjugates are the two brackets of $F_*^*$ -/

section ConjugateBrackets

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [LocallyConvexSpace ℝ V]
  [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X]
  [TopologicalSpace Y] [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y] [LocallyConvexSpace ℝ Y]
  {F : Bifun U X} {K : U × Y → EReal}

omit [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
  [LocallyConvexSpace ℝ V] in
/-- Let $U$, $X$ and $Y$ be locally convex spaces, with $U$ paired with $V$ and $X$ with $Y$, where
the pairings are compatible with the topologies of $U$, $X$ and $Y$. Let $F$ be a closed convex
bifunction from $U$ to $X$ and let $K \in \Omega(F)$. Then the upper conjugate of $K$ is the
concave bracket of the adjoint of $F_*^*$:
$$\overline{K}^*(v, x) = \langle v, (F_*^*)^* x \rangle \quad \text{for all } (v, x) \in V
  \times X,$$
where the adjoint $(F_*^*)^*$ is taken for the flipped pairings. This is the companion of
`ConvexAnalysis.lowerConjSaddle_eq_bracket_lowerAdjointBifun` for the lower conjugate. The upper
conjugate is the Lagrangian of $F$, that is the concave bracket of $F_*$, and the biadjoint
identity rewrites $F_*$ as the adjoint of $F_*^*$. -/
theorem upperConjSaddle_eq_concaveBracket_convexAdjointBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx]
    [IsCompatiblePairing Bx.flip] (hF : ConvexBifun F) (hcl : ClosedConvexBifun F)
    (hK : K ∈ bifunSaddleClass Bu Bx F) :
    upperConjSaddle Bu Bx K = fun q : V × X => concaveBracket Bu.flip
      (convexAdjointBifun Bu.flip Bx.flip (lowerAdjointBifun Bu Bx F)) q.1 q.2 := by
  rw [upperConjSaddle_eq_saddleLagrangian Bu Bx hF hcl hK,
    convexAdjointBifun_flip_lowerAdjointBifun (Bu := Bu) (Bx := Bx) hF hcl,
    saddleLagrangian_eq_concaveBracket]

/-- Let $U$, $V$, $X$ and $Y$ be locally convex spaces, with $U$ paired with $V$ and $X$ with $Y$,
where the pairings are compatible with the topologies of all four spaces. Let $F$ be a closed
convex bifunction from $U$ to $X$ and let $K \in \Omega(F)$. Then the concave closure in the
first variable of the lower conjugate is the upper conjugate:
$$\operatorname{cl}_1 \underline{K}^* = \overline{K}^*.$$

Both conjugates are brackets of the single closed convex bifunction $F_*^*$, so this is the
first bracket-closure equation of
`ConvexAnalysis.concaveBracket_convexAdjointBifun_eq_partialCl₁`, at the flipped pairings. -/
theorem partialCl₁_lowerConjSaddle (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu]
    [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx]
    [IsCompatiblePairing Bx.flip] (hF : ConvexBifun F) (hcl : ClosedConvexBifun F)
    (hK : K ∈ bifunSaddleClass Bu Bx F) :
    partialCl₁ (lowerConjSaddle Bu Bx K) = upperConjSaddle Bu Bx K := by
  have hG : ConvexBifun (lowerAdjointBifun Bu Bx F) := convexBifun_lowerAdjointBifun Bu Bx F
  rw [lowerConjSaddle_eq_bracket_lowerAdjointBifun Bu Bx hF hK,
    partialCl₁_bracket Bu.flip Bx.flip hG,
    upperConjSaddle_eq_concaveBracket_convexAdjointBifun Bu Bx hF hcl hK]

/-- Let $U$, $V$, $X$ and $Y$ be locally convex spaces, with $U$ paired with $V$ and $X$ with $Y$,
where the pairings are compatible with the topologies of all four spaces. Let $F$ be a closed
convex bifunction from $U$ to $X$ and let $K \in \Omega(F)$. Then the convex closure in the
second variable of the upper conjugate is the lower conjugate:
$$\operatorname{cl}_2 \overline{K}^* = \underline{K}^*.$$

This is the second bracket-closure equation of
`ConvexAnalysis.partialCl₂_concaveBracket_convexAdjointBifun`, at the flipped pairings. The
proof uses that $F_*^*$ is closed. -/
theorem partialCl₂_upperConjSaddle (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu]
    [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx]
    [IsCompatiblePairing Bx.flip] (hF : ConvexBifun F) (hcl : ClosedConvexBifun F)
    (hK : K ∈ bifunSaddleClass Bu Bx F) :
    partialCl₂ (upperConjSaddle Bu Bx K) = lowerConjSaddle Bu Bx K := by
  have hG : ConvexBifun (lowerAdjointBifun Bu Bx F) := convexBifun_lowerAdjointBifun Bu Bx F
  have := isContinuousPairing_prodPairing_flip Bu Bx
  have hGcl : ClosedConvexBifun (lowerAdjointBifun Bu Bx F) := closedConvexBifun_lowerAdjointBifun
  rw [upperConjSaddle_eq_concaveBracket_convexAdjointBifun Bu Bx hF hcl hK,
    partialCl₂_concaveBracket_adjoint Bu.flip Bx.flip hG hGcl,
    lowerConjSaddle_eq_bracket_lowerAdjointBifun Bu Bx hF hK]

/-- Let $U$, $V$, $X$ and $Y$ be locally convex spaces, with $U$ paired with $V$ and $X$ with $Y$,
where the pairings are compatible with the topologies of all four spaces. Let $F$ be a closed
convex bifunction from $U$ to $X$ and let $K \in \Omega(F)$. Then the class $\Omega(F_*^*)$,
taken for the flipped pairings, consists of the functions $L$ on $V \times X$ with
$$\underline{K}^* \le L \le \overline{K}^*.$$
So the class conjugate to $\Omega(F)$ is $\Omega(F_*^*)$, and its two ends are the lower and the
upper conjugate of any member of $\Omega(F)$. -/
theorem saddleClass_conjSaddle (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu]
    [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx]
    [IsCompatiblePairing Bx.flip] (hF : ConvexBifun F) (hcl : ClosedConvexBifun F)
    (hK : K ∈ bifunSaddleClass Bu Bx F) :
    bifunSaddleClass Bu.flip Bx.flip (lowerAdjointBifun Bu Bx F)
      = saddleClass (lowerConjSaddle Bu Bx K) (upperConjSaddle Bu Bx K) := by
  rw [bifunSaddleClass, lowerConjSaddle_eq_bracket_lowerAdjointBifun Bu Bx hF hK,
    upperConjSaddle_eq_concaveBracket_convexAdjointBifun Bu Bx hF hcl hK]

/-- Let $U$, $V$, $X$ and $Y$ be locally convex spaces, with $U$ paired with $V$ and $X$ with $Y$,
where the pairings are compatible with the topologies of all four spaces. Let $F$ be a closed
convex bifunction from $U$ to $X$ and let $K \in \Omega(F)$. Then the two conjugates are
equivalent: $\operatorname{cl}_1 \underline{K}^* = \operatorname{cl}_1 \overline{K}^*$ and
$\operatorname{cl}_2 \underline{K}^* = \operatorname{cl}_2 \overline{K}^*$. Hence they have the
same iterated extrema and the same saddle-points. -/
theorem saddleEquiv_lowerConjSaddle_upperConjSaddle (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip] (hF : ConvexBifun F)
    (hcl : ClosedConvexBifun F) (hK : K ∈ bifunSaddleClass Bu Bx F) :
    SaddleEquiv (lowerConjSaddle Bu Bx K) (upperConjSaddle Bu Bx K) := by
  have h1 := partialCl₁_lowerConjSaddle Bu Bx hF hcl hK
  have h2 := partialCl₂_upperConjSaddle Bu Bx hF hcl hK
  exact saddleEquiv_of_mem_saddleClass h1 h2 (mem_saddleClass_left h2) (mem_saddleClass_right h2)

end ConjugateBrackets

/-! ### Properness of the conjugate saddle-functions -/

section ProperConj

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X]
  {F : Bifun U X}

/-- Let $U$ and $X$ be locally convex spaces, with $U$ paired with $V$ and $X$ with $Y$, where the
pairings are compatible with the topologies of $U$ and $X$. Let $F$ be a closed convex
bifunction from $U$ to $X$ whose graph function is proper. Then the Lagrangian
$$L(v, x) = \inf_u \{\langle u, v \rangle + F(u, x)\}$$
is a proper saddle-function on $V \times X$: both $\operatorname{dom}_1 L$ and
$\operatorname{dom}_2 L$ are nonempty. Since the Lagrangian is the upper conjugate of every
member of $\Omega(F)$, a saddle-function conjugate to a closed proper one is again proper.

The two halves are of different depth. The condition $\operatorname{dom}_2 L \neq \emptyset$
needs only a point where the graph function is finite. The condition
$\operatorname{dom}_1 L \neq \emptyset$ is the existence of an affine minorant of the graph
function (`ConvexAnalysis.properConvex_convexConj`), and this is where closedness enters. -/
theorem properSaddleFn_saddleLagrangian (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu]
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx] (hF : ConvexBifun F)
    (hcl : ClosedConvexBifun F) (hpr : ProperConvex (graphFn F)) :
    ProperSaddleFn (saddleLagrangian Bu F) := by
  obtain ⟨p₀, hp₀⟩ := hpr.convexDom_nonempty
  obtain ⟨⟨v₁, y₁⟩, hw⟩ :=
    (properConvex_convexConj (B := prodPairing Bu Bx) ⟨hF, hcl, hpr⟩).convexDom_nonempty
  have hw' : convexConj (prodPairing Bu Bx) (graphFn F) (v₁, y₁) < ⊤ := hw
  have hadj : convexAdjointBifun Bu Bx F y₁ (-v₁) ≠ ⊥ := by
    rw [convexAdjointBifun_eq_neg_convexConj_graphFn, neg_neg]
    exact fun hcon => absurd (EReal.neg_eq_bot_iff.1 hcon) (ne_of_lt hw')
  refine ⟨⟨-v₁, ?_⟩, ⟨p₀.2, ?_⟩⟩
  · intro x
    have hterm : ∀ u : U, ((Bu u (-v₁) : ℝ) : EReal) + F u x
        = (F u x + ((Bu u (-v₁) - Bx x y₁ : ℝ) : EReal)) + ((Bx x y₁ : ℝ) : EReal) := by
      intro u
      have hreal : (Bu u (-v₁) - Bx x y₁ : ℝ) + Bx x y₁ = Bu u (-v₁) := by ring
      rw [add_assoc, ← EReal.coe_add, hreal, add_comm (F u x)]
    have hge : convexAdjointBifun Bu Bx F y₁ (-v₁) + ((Bx x y₁ : ℝ) : EReal)
        ≤ saddleLagrangian Bu F (-v₁, x) := by
      change _ ≤ lagrangian Bu F (-v₁) x
      rw [lagrangian_apply]
      refine le_iInf fun u => ?_
      rw [hterm u, convexAdjointBifun_apply]
      exact add_le_add (iInf_le (fun p : U × X =>
        F p.1 p.2 + ((Bu p.1 (-v₁) - Bx p.2 y₁ : ℝ) : EReal)) (u, x)) le_rfl
    refine lt_of_lt_of_le (bot_lt_iff_ne_bot.2 fun hcon => ?_) hge
    rcases EReal.add_eq_bot_iff.1 hcon with h | h
    · exact hadj h
    · exact EReal.coe_ne_bot _ h
  · intro v
    change lagrangian Bu F v p₀.2 < ⊤
    rw [lagrangian_apply]
    refine lt_of_le_of_lt (iInf_le (fun u => ((Bu u v : ℝ) : EReal) + F u p₀.2) p₀.1) ?_
    exact EReal.add_lt_top (EReal.coe_ne_top _) (ne_of_lt hp₀)

end ProperConj

/-! ### A closure pair agrees on the relative interiors -/

section ClosurePairRelint

variable {U X : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] {Klow Kup : U × X → EReal}

/-- Let $U$ and $X$ be finite-dimensional real normed spaces and let $\underline{K}, \overline{K} :
U \times X \to [-\infty, +\infty]$ form a closure pair: $\operatorname{cl}_1 \underline{K} =
\overline{K}$ and $\operatorname{cl}_2 \overline{K} = \underline{K}$. Suppose that
$\overline{K}$ is concave-convex and $\operatorname{dom}_2 \overline{K} \neq \emptyset$. Then
$\underline{K}(u, x) = \overline{K}(u, x)$ for every $u \in \operatorname{ri}
(\operatorname{dom}_1 \underline{K})$ and every $x \in X$.

The closure relations hold exactly, so the hypotheses are lighter than in the version for a
closed saddle-function. The slice $\underline{K}(\cdot, x)$ is
$\operatorname{cl}_2 \overline{K}(\cdot, x)$, its concave effective domain is
$\operatorname{dom}_1 \overline{K}$, and a concave function agrees with its closure on the
relative interior of its effective domain. Only $\operatorname{dom}_2 \overline{K} \neq
\emptyset$ is needed of properness. -/
theorem eq_of_mem_relint_dom₁_of_closure_pair (hup : ConcaveConvexFn Kup)
    (hne : (dom₂ Kup).Nonempty) (h1 : partialCl₁ Klow = Kup) (h2 : partialCl₂ Kup = Klow)
    {u : U} (hu : u ∈ ri (dom₁ Klow)) (x : X) : Klow (u, x) = Kup (u, x) := by
  have hd1 : dom₁ Klow = dom₁ Kup := by rw [← h2]; exact dom₁_partialCl₂ hup hne
  have hslice : ConcaveFn fun u => partialCl₂ Kup (u, x) := hup.partialCl₂.concave_fst x
  have hdom : concaveDom (fun u => partialCl₂ Kup (u, x)) = dom₁ Kup :=
    concaveDom_partialCl₂_slice hup hne x
  have hmem : u ∈ ri (concaveDom fun u => partialCl₂ Kup (u, x)) := by
    rw [hdom, ← hd1]; exact hu
  have hcl := hslice.concaveCl_eq_of_mem_relint_concaveDom hmem
  calc Klow (u, x) = partialCl₂ Kup (u, x) := by rw [h2]
    _ = concaveCl (fun u => partialCl₂ Kup (u, x)) u := hcl.symm
    _ = concaveCl (fun u => Klow (u, x)) u := by rw [h2]
    _ = partialCl₁ Klow (u, x) := (congrFun (partialCl₁_slice Klow x) u).symm
    _ = Kup (u, x) := by rw [h1]

/-- Let $U$ and $X$ be finite-dimensional real normed spaces and let $\underline{K}, \overline{K} :
U \times X \to [-\infty, +\infty]$ form a closure pair: $\operatorname{cl}_1 \underline{K} =
\overline{K}$ and $\operatorname{cl}_2 \overline{K} = \underline{K}$. Suppose that
$\underline{K}$ is concave-convex and $\operatorname{dom}_1 \underline{K} \neq \emptyset$. Then
$\underline{K}(u, x) = \overline{K}(u, x)$ for every $x \in \operatorname{ri}
(\operatorname{dom}_2 \overline{K})$ and every $u \in U$.

This is `ConvexAnalysis.eq_of_mem_relint_dom₁_of_closure_pair` applied to the swap
$(x, u) \mapsto -K(u, x)$, which exchanges $\operatorname{cl}_1$ with $\operatorname{cl}_2$ and
the two members of the pair. -/
theorem eq_of_mem_relint_dom₂_of_closure_pair (hlow : ConcaveConvexFn Klow)
    (hne : (dom₁ Klow).Nonempty) (h1 : partialCl₁ Klow = Kup) (h2 : partialCl₂ Kup = Klow)
    {x : X} (hx : x ∈ ri (dom₂ Kup)) (u : U) : Klow (u, x) = Kup (u, x) := by
  have h := eq_of_mem_relint_dom₁_of_closure_pair hlow.saddleSwap (by rwa [dom₂_saddleSwap])
    (by rw [partialCl₁_saddleSwap, h2]) (by rw [partialCl₂_saddleSwap, h1])
    (by rwa [dom₁_saddleSwap]) u
  rw [saddleSwap_apply, saddleSwap_apply] at h
  exact (neg_inj.1 h).symm

end ClosurePairRelint

/-! ### The common effective domain, and existence of the saddle-value -/

section CommonDom

variable {U V X Y : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] {F : Bifun U X} {K : U × Y → EReal}

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ X] in
/-- Let $U$, $V$, $X$ and $Y$ be real normed spaces, with $U$ paired with $V$ and $X$ with $Y$,
where the pairings are compatible with the topologies of $U$, $X$ and $Y$. Let $F$ be a closed
proper convex bifunction from $U$ to $X$ and let $K \in \Omega(F)$. Then the upper conjugate
$\overline{K}^*$ is a proper saddle-function. -/
theorem properSaddleFn_upperConjSaddle (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu]
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip]
    (hF : ConvexBifun F) (hcl : ClosedConvexBifun F) (hpr : ProperConvex (graphFn F))
    (hK : K ∈ bifunSaddleClass Bu Bx F) : ProperSaddleFn (upperConjSaddle Bu Bx K) := by
  rw [upperConjSaddle_eq_saddleLagrangian Bu Bx hF hcl hK]
  exact properSaddleFn_saddleLagrangian Bu Bx hF hcl hpr

omit [FiniteDimensional ℝ V] in
/-- Let $U$, $V$, $X$ and $Y$ be real normed spaces with $X$ finite-dimensional, with $U$ paired
with $V$ and $X$ with $Y$, where the pairings are compatible with the topologies of all four
spaces. Let $F$ be a closed proper convex bifunction from $U$ to $X$ and let $K \in \Omega(F)$.
Then the lower conjugate $\underline{K}^*$ is a proper saddle-function. It is
$\operatorname{cl}_2$ of the upper conjugate, and $\operatorname{cl}_2$ preserves properness. -/
theorem properSaddleFn_lowerConjSaddle (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu]
    [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx]
    [IsCompatiblePairing Bx.flip] (hF : ConvexBifun F) (hcl : ClosedConvexBifun F)
    (hpr : ProperConvex (graphFn F)) (hK : K ∈ bifunSaddleClass Bu Bx F) :
    ProperSaddleFn (lowerConjSaddle Bu Bx K) := by
  rw [← partialCl₂_upperConjSaddle Bu Bx hF hcl hK]
  exact ProperSaddleFn.partialCl₂ (concaveConvexFn_upperConjSaddle Bu Bx hF hcl hK)
    (properSaddleFn_upperConjSaddle Bu Bx hF hcl hpr hK)

omit [FiniteDimensional ℝ V] in
/-- Let $U$, $V$, $X$ and $Y$ be real normed spaces with $X$ finite-dimensional, with $U$ paired
with $V$ and $X$ with $Y$, where the pairings are compatible with the topologies of all four
spaces. Let $F$ be a closed proper convex bifunction from $U$ to $X$ and let $K \in \Omega(F)$.
Then $\operatorname{dom}_1 \underline{K}^* = \operatorname{dom}_1 \overline{K}^*$. This common
set is $C^*$, the first factor of the common effective domain. -/
theorem dom₁_conjSaddle_eq (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu]
    [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx]
    [IsCompatiblePairing Bx.flip] (hF : ConvexBifun F) (hcl : ClosedConvexBifun F)
    (hpr : ProperConvex (graphFn F)) (hK : K ∈ bifunSaddleClass Bu Bx F) :
    dom₁ (lowerConjSaddle Bu Bx K) = dom₁ (upperConjSaddle Bu Bx K) := by
  rw [← partialCl₂_upperConjSaddle Bu Bx hF hcl hK]
  exact dom₁_partialCl₂ (concaveConvexFn_upperConjSaddle Bu Bx hF hcl hK)
    (properSaddleFn_upperConjSaddle Bu Bx hF hcl hpr hK).dom₂_nonempty

/-- Let $U$, $V$, $X$ and $Y$ be real normed spaces with $V$ and $X$ finite-dimensional, with $U$
paired with $V$ and $X$ with $Y$, where the pairings are compatible with the topologies of all
four spaces. Let $F$ be a closed proper convex bifunction from $U$ to $X$ and let
$K \in \Omega(F)$. Then $\operatorname{dom}_2 \underline{K}^* = \operatorname{dom}_2
\overline{K}^*$. This common set is $D^*$, the second factor of the common effective domain. -/
theorem dom₂_conjSaddle_eq (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu]
    [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx]
    [IsCompatiblePairing Bx.flip] (hF : ConvexBifun F) (hcl : ClosedConvexBifun F)
    (hpr : ProperConvex (graphFn F)) (hK : K ∈ bifunSaddleClass Bu Bx F) :
    dom₂ (lowerConjSaddle Bu Bx K) = dom₂ (upperConjSaddle Bu Bx K) := by
  rw [← partialCl₁_lowerConjSaddle Bu Bx hF hcl hK]
  exact (dom₂_partialCl₁ (concaveConvexFn_lowerConjSaddle Bu Bx hF hK)
    (properSaddleFn_lowerConjSaddle Bu Bx hF hcl hpr hK).dom₁_nonempty).symm

/-- Let $U$, $V$, $X$ and $Y$ be real normed spaces with $V$ and $X$ finite-dimensional, with $U$
paired with $V$ and $X$ with $Y$, where the pairings are compatible with the topologies of all
four spaces. Let $F$ be a closed proper convex bifunction from $U$ to $X$ and let
$K \in \Omega(F)$. Then the two conjugates have the same effective domain:
$$\operatorname{dom}_1 \underline{K}^* \times \operatorname{dom}_2 \underline{K}^*
  = \operatorname{dom}_1 \overline{K}^* \times \operatorname{dom}_2 \overline{K}^* = C^*
  \times D^*.$$
-/
theorem domSaddle_conjSaddle_eq (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu]
    [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx]
    [IsCompatiblePairing Bx.flip] (hF : ConvexBifun F) (hcl : ClosedConvexBifun F)
    (hpr : ProperConvex (graphFn F)) (hK : K ∈ bifunSaddleClass Bu Bx F) :
    domSaddle (lowerConjSaddle Bu Bx K) = domSaddle (upperConjSaddle Bu Bx K) := by
  rw [domSaddle, domSaddle, dom₁_conjSaddle_eq Bu Bx hF hcl hpr hK,
    dom₂_conjSaddle_eq Bu Bx hF hcl hpr hK]

/-- Let $U$, $V$, $X$ and $Y$ be real normed spaces with $V$ and $X$ finite-dimensional, with $U$
paired with $V$ and $X$ with $Y$, where the pairings are compatible with the topologies of all
four spaces. Let $F$ be a closed proper convex bifunction from $U$ to $X$ and let
$K \in \Omega(F)$. Then
$$\underline{K}^*(v, x) = \overline{K}^*(v, x)
  \quad \text{for all } v \in \operatorname{ri} C^* \text{ and } x \in X,$$
where $C^* = \operatorname{dom}_1 \underline{K}^*$. -/
theorem lowerConjSaddle_eq_upperConjSaddle_of_mem_relint_dom₁ (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip] (hF : ConvexBifun F)
    (hcl : ClosedConvexBifun F) (hpr : ProperConvex (graphFn F)) (hK : K ∈ bifunSaddleClass Bu Bx F)
    {v : V} (hv : v ∈ ri (dom₁ (lowerConjSaddle Bu Bx K))) (x : X) :
    lowerConjSaddle Bu Bx K (v, x) = upperConjSaddle Bu Bx K (v, x) :=
  eq_of_mem_relint_dom₁_of_closure_pair (concaveConvexFn_upperConjSaddle Bu Bx hF hcl hK)
    (properSaddleFn_upperConjSaddle Bu Bx hF hcl hpr hK).dom₂_nonempty
    (partialCl₁_lowerConjSaddle Bu Bx hF hcl hK) (partialCl₂_upperConjSaddle Bu Bx hF hcl hK)
    hv x

/-- Let $U$, $V$, $X$ and $Y$ be real normed spaces with $V$ and $X$ finite-dimensional, with $U$
paired with $V$ and $X$ with $Y$, where the pairings are compatible with the topologies of all
four spaces. Let $F$ be a closed proper convex bifunction from $U$ to $X$ and let
$K \in \Omega(F)$. Then
$$\underline{K}^*(v, x) = \overline{K}^*(v, x)
  \quad \text{for all } x \in \operatorname{ri} D^* \text{ and } v \in V,$$
where $D^* = \operatorname{dom}_2 \underline{K}^*$. -/
theorem lowerConjSaddle_eq_upperConjSaddle_of_mem_relint_dom₂ (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip] (hF : ConvexBifun F)
    (hcl : ClosedConvexBifun F) (hpr : ProperConvex (graphFn F)) (hK : K ∈ bifunSaddleClass Bu Bx F)
    {x : X} (hx : x ∈ ri (dom₂ (lowerConjSaddle Bu Bx K))) (v : V) :
    lowerConjSaddle Bu Bx K (v, x) = upperConjSaddle Bu Bx K (v, x) := by
  refine eq_of_mem_relint_dom₂_of_closure_pair (concaveConvexFn_lowerConjSaddle Bu Bx hF hK)
    (properSaddleFn_lowerConjSaddle Bu Bx hF hcl hpr hK).dom₁_nonempty
    (partialCl₁_lowerConjSaddle Bu Bx hF hcl hK) (partialCl₂_upperConjSaddle Bu Bx hF hcl hK)
    ?_ v
  rwa [← dom₂_conjSaddle_eq Bu Bx hF hcl hpr hK]

/-- Let $U$, $V$, $X$ and $Y$ be real normed spaces with $V$ and $X$ finite-dimensional, with $U$
paired with $V$ and $X$ with $Y$, where the pairings are compatible with the topologies of all
four spaces. Let $F$ be a closed proper convex bifunction from $U$ to $X$ and let
$K \in \Omega(F)$. If $0 \in \operatorname{ri} C^*$, where
$C^* = \operatorname{dom}_1 \underline{K}^*$, then the saddle-value of $K$ exists:
$$\sup_u \inf_y K(u, y) = \inf_y \sup_u K(u, y).$$

The two iterated extrema of $K$ are the negatives of the two conjugates at the origin, and
`ConvexAnalysis.lowerConjSaddle_eq_upperConjSaddle_of_mem_relint_dom₁` makes the conjugates
agree there. -/
theorem hasSaddleValue_of_mem_relint_dom₁_lowerConjSaddle (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip] (hF : ConvexBifun F)
    (hcl : ClosedConvexBifun F) (hpr : ProperConvex (graphFn F)) (hK : K ∈ bifunSaddleClass Bu Bx F)
    (h0 : (0 : V) ∈ ri (dom₁ (lowerConjSaddle Bu Bx K))) : HasSaddleValue K :=
  (hasSaddleValue_iff_conjSaddle_zero_eq Bu Bx K).2
    (lowerConjSaddle_eq_upperConjSaddle_of_mem_relint_dom₁ Bu Bx hF hcl hpr hK h0 0).symm

/-- Let $U$, $V$, $X$ and $Y$ be real normed spaces with $V$ and $X$ finite-dimensional, with $U$
paired with $V$ and $X$ with $Y$, where the pairings are compatible with the topologies of all
four spaces. Let $F$ be a closed proper convex bifunction from $U$ to $X$ and let
$K \in \Omega(F)$. If $0 \in \operatorname{ri} D^*$, where
$D^* = \operatorname{dom}_2 \underline{K}^*$, then the saddle-value of $K$ exists:
$$\sup_u \inf_y K(u, y) = \inf_y \sup_u K(u, y).$$
-/
theorem hasSaddleValue_of_mem_relint_dom₂_lowerConjSaddle (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip] (hF : ConvexBifun F)
    (hcl : ClosedConvexBifun F) (hpr : ProperConvex (graphFn F)) (hK : K ∈ bifunSaddleClass Bu Bx F)
    (h0 : (0 : X) ∈ ri (dom₂ (lowerConjSaddle Bu Bx K))) : HasSaddleValue K :=
  (hasSaddleValue_iff_conjSaddle_zero_eq Bu Bx K).2
    (lowerConjSaddle_eq_upperConjSaddle_of_mem_relint_dom₂ Bu Bx hF hcl hpr hK h0 0).symm

/-- Let $U$, $V$, $X$ and $Y$ be real normed spaces with $V$ and $X$ finite-dimensional, with $U$
paired with $V$ and $X$ with $Y$, where the pairings are compatible with the topologies of all
four spaces. Let $F$ be a closed proper convex bifunction from $U$ to $X$ and let
$K \in \Omega(F)$. If $0 \in \operatorname{ri} C^*$ and $0 \in \operatorname{ri} D^*$, where
$C^* \times D^*$ is the effective domain of $\underline{K}^*$, then the saddle-value of $K$ is a
real number: $\sup_u \inf_y K(u, y) = r$ for some $r \in \mathbb{R}$.

The saddle-value is minus the value of the conjugate at the origin, which lies in its effective
domain, and a saddle-function is finite on its effective domain. -/
theorem exists_maximin_eq_coe_of_mem_relint_domSaddle (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip] (hF : ConvexBifun F)
    (hcl : ClosedConvexBifun F) (hpr : ProperConvex (graphFn F)) (hK : K ∈ bifunSaddleClass Bu Bx F)
    (h1 : (0 : V) ∈ ri (dom₁ (lowerConjSaddle Bu Bx K)))
    (h2 : (0 : X) ∈ ri (dom₂ (lowerConjSaddle Bu Bx K))) :
    ∃ r : ℝ, maximin K = (r : EReal) := by
  have hmem : ((0 : V), (0 : X)) ∈ domSaddle (lowerConjSaddle Bu Bx K) :=
    ⟨intrinsicInterior_subset h1, intrinsicInterior_subset h2⟩
  obtain ⟨r, hr⟩ := EReal.exists_coe_of_ne_bot_of_lt_top
    (ne_of_gt (bot_lt_of_mem_domSaddle hmem)) (lt_top_of_mem_domSaddle hmem)
  refine ⟨-r, ?_⟩
  have heq : upperConjSaddle Bu Bx K 0 = ((r : ℝ) : EReal) := by
    have h := lowerConjSaddle_eq_upperConjSaddle_of_mem_relint_dom₁ Bu Bx hF hcl hpr hK h1 0
    change lowerConjSaddle Bu Bx K 0 = upperConjSaddle Bu Bx K 0 at h
    rw [← h]
    exact hr
  rw [maximin_eq_neg_upperConjSaddle_zero Bu Bx K, heq, EReal.coe_neg]

end CommonDom

/-!
### The effective domains of the conjugate saddle-functions

For $K \in \Omega(F)$, the support functions of $C^* = \operatorname{dom}_1 K^*$ and
$D^* = \operatorname{dom}_2 K^*$ can be computed from $K$ itself. The half for $D^*$ is the one with
content. The set $D^*$ is the projection on $X$ of $\operatorname{dom} F$, and the support function
of this projection is assembled from the support functions of the slices $\operatorname{dom} (F u)$,
each of which is a recession function. The lemmas before it are auxiliary: support functions do not
see relative interiors, and the relative interior of a projection is the union of the relative
interiors of the slices.
-/

section DomLagrangian

variable {U V X : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]

/-- Let $U$ be paired with $V$ and let $F$ be any bifunction from $U$ to $X$. The second effective
domain of the Lagrangian $L(v, x) = \inf_u \{\langle u, v \rangle + F(u, x)\}$ is the projection
on $X$ of the effective domain of the graph function of $F$:
$$\operatorname{dom}_2 L = \{x \mid F(u, x) < +\infty \text{ for some } u\}.$$
No hypothesis on $F$ is needed. The inequality $L(v, x) \le \langle u, v \rangle + F(u, x)$
gives the inclusion $\supseteq$, and for $\subseteq$ it is enough to test $v = 0$. -/
theorem dom₂_saddleLagrangian (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (F : Bifun U X) :
    dom₂ (saddleLagrangian Bu F) = Prod.snd '' convexDom (graphFn F) := by
  ext x
  constructor
  · intro hx
    have h0 : lagrangian Bu F 0 x < ⊤ := hx 0
    rw [lagrangian_apply] at h0
    have h1 : ⨅ u, F u x < ⊤ := by
      refine lt_of_le_of_lt (le_of_eq (iInf_congr fun u => ?_)) h0
      rw [map_zero, EReal.coe_zero, zero_add]
    obtain ⟨u, hu⟩ := iInf_lt_iff.1 h1
    exact ⟨(u, x), hu, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    intro v
    change lagrangian Bu F v p.2 < ⊤
    rw [lagrangian_apply]
    refine lt_of_le_of_lt (iInf_le (fun u => ((Bu u v : ℝ) : EReal) + F u p.2) p.1) ?_
    exact EReal.add_lt_top (EReal.coe_ne_top _) (ne_of_lt hp)

end DomLagrangian

section DomProjection

variable {U X : Type*}

/-- The effective domain $\operatorname{dom} F = \{u \mid F(u, x) < +\infty \text{ for some } x\}$
of a bifunction $F$ from $U$ to $X$ is the projection on $U$ of the effective domain of its
graph function. -/
theorem convexDomBifun_eq_image_fst
    (F : Bifun U X) : convexDomBifun F = Prod.fst '' convexDom (graphFn F) := by
  ext u
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨(u, x), lt_top_iff_ne_top.2 hx, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p.2, ne_of_lt hp⟩

end DomProjection

section DomBracket

variable {U X Y : Type*} [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]

/-- Let $X$ be paired with $Y$ and let $F$ be a bifunction from $U$ to $X$. The first effective
domain of the lower bracket $(u, y) \mapsto \langle Fu, y \rangle = (Fu)^*(y)$ is
$\operatorname{dom} F$. The bracket is $-\infty$ exactly where $F u$ is identically $+\infty$,
for every $y$ (`ConvexAnalysis.concaveDom_bracket`). -/
theorem dom₁_bracket (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (F : Bifun U X) :
    dom₁ (fun p : U × Y => bracket Bx F p.1 p.2) = convexDomBifun F := by
  ext u
  constructor
  · intro hu
    have h : u ∈ concaveDom fun u => bracket Bx F u (0 : Y) := hu 0
    rwa [concaveDom_bracket] at h
  · intro hu y
    have h : u ∈ concaveDom fun u => bracket Bx F u y := by
      rw [concaveDom_bracket]; exact hu
    exact h

end DomBracket

section SupportRelint

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [AddCommGroup F] [Module ℝ F]

/-- Let $E$ be a finite-dimensional real normed space and let $B$ be a pairing of $E$ with $F$ that
is continuous in its first variable. For a convex set $C \subseteq E$, the support function does
not see the relative interior: $\delta^*(\cdot \mid \operatorname{ri} C) = \delta^*(\cdot \mid
C)$. This holds because the support function does not see closures and $\operatorname{cl}
(\operatorname{ri} C) = \operatorname{cl} C$. -/
theorem supportFn_relint (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [IsContinuousPairing B] {C : Set E}
    (hC : Convex ℝ C) : supportFn B (ri C) = supportFn B C := by
  rw [← supportFn_closure (B := B) (ri C), Convex.closure_relint hC, supportFn_closure]

end SupportRelint

section RelintProjection

variable {U X : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]

/-- Let $U$ and $X$ be finite-dimensional real normed spaces and let $S \subseteq U \times X$ be
convex. The relative interior of the projection of $S$ on $X$ is the union, over $u$ in the
relative interior of the projection of $S$ on $U$, of the relative interiors of the slices of
$S$:
$$\operatorname{ri} \{x \mid (u, x) \in S \text{ for some } u\}
  = \bigcup_{u \in \operatorname{ri} \{u \mid (u, x) \in S \text{ for some } x\}} \operatorname{ri}
  \{x \mid (u, x) \in S\}.$$
-/
theorem relint_image_snd_eq_iUnion {S : Set (U × X)} (hS : Convex ℝ S) :
    ri (Prod.snd '' S) = ⋃ u ∈ ri (Prod.fst '' S), ri {x | (u, x) ∈ S} := by
  have hsnd : ri (Prod.snd '' S) = Prod.snd '' ri S := by
    have h := Convex.relint_image hS (LinearMap.snd ℝ U X)
    rwa [show ⇑(LinearMap.snd ℝ U X) = Prod.snd from rfl] at h
  rw [hsnd]
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    have h := (Convex.mem_relint_prod_iff hS (y := p.1) (z := p.2)).1 hp
    exact Set.mem_iUnion₂.2 ⟨p.1, h.1, h.2⟩
  · intro hx
    obtain ⟨u, hu, hx'⟩ := Set.mem_iUnion₂.1 hx
    exact ⟨(u, x), (Convex.mem_relint_prod_iff hS).2 ⟨hu, hx'⟩, rfl⟩

end RelintProjection

section SupportUnion

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

/-- The support function of a union is the supremum of the support functions: for a family of sets
$t_i \subseteq E$ indexed by $i \in s$,
$$\delta^*\Bigl(y \Bigm| \bigcup_{i \in s} t_i\Bigr) = \sup_{i \in s} \delta^*(y \mid t_i).$$
-/
theorem supportFn_biUnion {ι : Type*} (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (s : Set ι) (t : ι → Set E)
    (y : F) : supportFn B (⋃ i ∈ s, t i) y = ⨆ i ∈ s, supportFn B (t i) y := by
  simp only [supportFn_iUnion]

end SupportUnion

section ConjRecession

variable {U V X Y : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
  {F : Bifun U X} {K : U × Y → EReal}

omit [FiniteDimensional ℝ U] [FiniteDimensional ℝ X] in
/-- Let $U$, $V$, $X$ and $Y$ be real normed spaces with $Y$ finite-dimensional, with $U$ paired
with $V$ and $X$ with $Y$, where the pairings are compatible with the topologies of $U$, $X$ and
$Y$. Let $F$ be a closed convex bifunction from $U$ to $X$, and let $K \in \Omega(F)$ be
concave-convex with $\operatorname{dom}_2 K \neq \emptyset$. Then the first effective domain of
$K$ is the effective domain of $F$:
$$\operatorname{dom}_1 K = \operatorname{dom} F.$$
Rockafellar uses this identification without comment.

The operator $\operatorname{cl}_2$ does not change $\operatorname{dom}_1$, and on $\Omega(F)$ it
is constant, equal to the lower bracket. The first effective domain of the lower bracket is
$\operatorname{dom} F$, because $\langle Fu, y \rangle = -\infty$ exactly where
$F u \equiv +\infty$. -/
theorem dom₁_eq_convexDomBifun_of_mem_bifunSaddleClass (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx]
    [IsCompatiblePairing Bx.flip] (hF : ConvexBifun F) (hcl : ClosedConvexBifun F)
    (hK : K ∈ bifunSaddleClass Bu Bx F) (hKcc : ConcaveConvexFn K) (hne : (dom₂ K).Nonempty) :
    dom₁ K = convexDomBifun F := by
  have hcl₂ : partialCl₂ K = fun p : U × Y => bracket Bx F p.1 p.2 :=
    partialCl₂_eq_of_mem_saddleClass (partialCl₂_concaveBracket_adjoint Bu Bx hF hcl) hK
  rw [← dom₁_partialCl₂ hKcc hne, hcl₂, dom₁_bracket]

omit [FiniteDimensional ℝ U] [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y] in
/-- Let $X$ be paired with $Y$ by a pairing compatible with the topology of $Y$. Let
$K : U \times Y \to [-\infty, +\infty]$ be concave-convex with the slice structure
`ConvexAnalysis.ConvexSliceStructure` of a closed proper saddle-function, and let $F$ be the
bifunction $F u = K(u, \cdot)^*$. For $u \in \operatorname{ri} (\operatorname{dom}_1 K)$, the
recession function of the slice $K(u, \cdot)$ is the support function of
$\operatorname{dom} (F u)$:
$$K(u, \cdot) 0^+ = \delta^*(\cdot \mid \operatorname{dom} (F u)).$$
Over $\operatorname{ri} (\operatorname{dom}_1 K)$ the slice is closed proper convex and $F u$ is
its conjugate, and the support function of the effective domain of a conjugate is the recession
function of the original function. -/
theorem recessionFn_slice_eq_supportFn_convexDom (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bx.flip] (hK : ConcaveConvexFn K) (hs : ConvexSliceStructure K) {u : U}
    (hu : u ∈ ri (dom₁ K)) :
    recessionFn (fun y => K (u, y)) = supportFn Bx (convexDom (bifunOfSaddle Bx K u)) := by
  have hcpc : ClosedProperConvexFn fun y => K (u, y) :=
    ⟨hK.convex_snd u, hs.closedConvex_slice u hu,
        hs.properConvex_slice u (intrinsicInterior_subset hu)⟩
  have h := recessionFn_eq_supportFn_convexDom_convexConj (B := Bx.flip) hcpc
  rwa [LinearMap.flip_flip] at h

omit [FiniteDimensional ℝ U] [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y] in
/-- Let $X$ be paired with $Y$ by a pairing compatible with the topology of $Y$. Let
$K : U \times Y \to [-\infty, +\infty]$ be concave-convex with the slice structure
`ConvexAnalysis.ConvexSliceStructure` of a closed proper saddle-function, and let $F$ be the
bifunction $F u = K(u, \cdot)^*$. For $u \in \operatorname{ri} (\operatorname{dom}_1 K)$ and
$w \in Y$,
$$\delta^*(w \mid \operatorname{dom} (F u))
  = \sup_{y \in \operatorname{dom}_2 K} \{K(u, y + w) - K(u, y)\}.$$
The support function of $\operatorname{dom} (K(u, \cdot)^*)$ is the recession function of
$K(u, \cdot)$, which is the supremum of the difference quotients over the effective domain. -/
theorem supportFn_convexDom_bifunOfSaddle_eq_iSup_sub (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bx.flip] (hK : ConcaveConvexFn K) (hs : ConvexSliceStructure K) {u : U}
    (hu : u ∈ ri (dom₁ K)) (w : Y) :
    supportFn Bx (convexDom (bifunOfSaddle Bx K u)) w = ⨆ y ∈ dom₂ K,
        (K (u, y + w) - K (u, y)) := by
  have hconv : ConvexFn fun y => K (u, y) := hK.convex_snd u
  have hp : ProperConvex fun y => K (u, y) := hs.properConvex_slice u (intrinsicInterior_subset hu)
  rw [← recessionFn_slice_eq_supportFn_convexDom Bx hK hs hu,
    recessionFn_apply_eq_iSup_sub hconv hp.ne_bot w, hs.convexDom_slice u hu]

omit [FiniteDimensional ℝ U] [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y] in
/-- Let $U$, $V$, $X$ and $Y$ be real normed spaces, with $U$ paired with $V$ and $X$ with $Y$,
where the pairings are compatible with the topologies of $U$, $X$ and $Y$. Let $F$ be a closed
convex bifunction from $U$ to $X$ and let $K \in \Omega(F)$. Then the second effective domain of
the upper conjugate is the projection of $\operatorname{dom} F$ on $X$:
$$D^* = \operatorname{dom}_2 \overline{K}^* = \{x \mid F(u, x) < +\infty \text{ for some } u\}.$$
The upper conjugate is the Lagrangian of $F$, and `ConvexAnalysis.dom₂_saddleLagrangian`
applies. -/
theorem dom₂_upperConjSaddle (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu]
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip]
    (hF : ConvexBifun F) (hcl : ClosedConvexBifun F) (hK : K ∈ bifunSaddleClass Bu Bx F) :
    dom₂ (upperConjSaddle Bu Bx K) = Prod.snd '' convexDom (graphFn F) := by
  rw [upperConjSaddle_eq_saddleLagrangian Bu Bx hF hcl hK, dom₂_saddleLagrangian]

/-- Let $U$, $V$, $X$ and $Y$ be real normed spaces with $U$, $X$ and $Y$ finite-dimensional, with
$U$ paired with $V$ and $X$ with $Y$, where the pairings are compatible with the topologies of
$U$, $X$ and $Y$. Let $F$ be a closed convex bifunction from $U$ to $X$, and let
$K \in \Omega(F)$ be concave-convex with $\operatorname{dom}_2 K \neq \emptyset$ and with the
slice structure `ConvexAnalysis.ConvexSliceStructure` of a closed proper saddle-function. Write
$C = \operatorname{dom}_1 K$, $D = \operatorname{dom}_2 K$ and
$D^* = \operatorname{dom}_2 \overline{K}^*$. Then for every $w \in Y$
$$\delta^*(w \mid D^*) = \sup_{u \in \operatorname{ri} C} \sup_{y \in D}
  \{K(u, y + w) - K(u, y)\}.$$
This is Theorem 37.2 of [rockafellar1970convex].

The set $D^*$ is the projection of $\operatorname{dom} F$ on $X$. A support function does not
see the relative interior, so $\delta^*(\cdot \mid D^*)$ is the supremum over
$u \in \operatorname{ri} C$ of the support functions of the slices $\operatorname{dom} (F u)$,
and `ConvexAnalysis.supportFn_convexDom_bifunOfSaddle_eq_iSup_sub` computes each of them. -/
theorem supportFn_dom₂_upperConjSaddle (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu]
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip]
    (hF : ConvexBifun F) (hcl : ClosedConvexBifun F) (hK : K ∈ bifunSaddleClass Bu Bx F)
    (hKcc : ConcaveConvexFn K) (hne : (dom₂ K).Nonempty) (hs : ConvexSliceStructure K) (w : Y) :
    supportFn Bx (dom₂ (upperConjSaddle Bu Bx K)) w
      = ⨆ u ∈ ri (dom₁ K), ⨆ y ∈ dom₂ K, (K (u, y + w) - K (u, y)) := by
  have hFK : bifunOfSaddle Bx K = F := bifunOfSaddle_eq_of_mem_bifunSaddleClass Bu Bx hF hcl hK
  have hG : Convex ℝ (convexDom (graphFn F)) := ConvexFn.convex_convexDom hF
  have hC : dom₁ K = Prod.fst '' convexDom (graphFn F) := by
    rw [dom₁_eq_convexDomBifun_of_mem_bifunSaddleClass Bu Bx hF hcl hK hKcc hne,
        convexDomBifun_eq_image_fst]
  have hsndconv : Convex ℝ (Prod.snd '' convexDom (graphFn F)) :=
    hG.linear_image (LinearMap.snd ℝ U X)
  calc supportFn Bx (dom₂ (upperConjSaddle Bu Bx K)) w
      = supportFn Bx (ri (Prod.snd '' convexDom (graphFn F))) w := by
        rw [dom₂_upperConjSaddle Bu Bx hF hcl hK, supportFn_relint Bx hsndconv]
    _ = supportFn Bx (⋃ u ∈ ri (dom₁ K), ri {x | (u, x) ∈ convexDom (graphFn F)}) w := by
        rw [relint_image_snd_eq_iUnion hG, hC]
    _ = ⨆ u ∈ ri (dom₁ K), supportFn Bx (ri {x | (u, x) ∈ convexDom (graphFn F)}) w :=
        supportFn_biUnion Bx (ri (dom₁ K)) (fun u => ri {x | (u, x) ∈ convexDom (graphFn F)}) w
    _ = ⨆ u ∈ ri (dom₁ K), ⨆ y ∈ dom₂ K, (K (u, y + w) - K (u, y)) := by
        refine iSup_congr fun u => iSup_congr fun hu => ?_
        have hslice : {x | (u, x) ∈ convexDom (graphFn F)} = convexDom (bifunOfSaddle Bx K u) := by
          rw [hFK]; rfl
        have hconvu : ConvexFn (bifunOfSaddle Bx K u) := by
          rw [hFK]; exact ConvexBifun.convexFn_apply hF u
        rw [hslice, supportFn_relint Bx (ConvexFn.convex_convexDom hconvu)]
        exact supportFn_convexDom_bifunOfSaddle_eq_iSup_sub Bx hKcc hs hu w

/-- In the setting of `ConvexAnalysis.supportFn_dom₂_upperConjSaddle`, the support function of $D^*$
is the pointwise supremum of the recession functions of the slices:
$$\delta^*(w \mid D^*) = \sup_{u \in \operatorname{ri} C} (K(u, \cdot) 0^+)(w)
  \quad \text{for every } w \in Y.$$
-/
theorem supportFn_dom₂_upperConjSaddle_eq_iSup_recessionFn (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx]
    [IsCompatiblePairing Bx.flip] (hF : ConvexBifun F) (hcl : ClosedConvexBifun F)
    (hK : K ∈ bifunSaddleClass Bu Bx F) (hKcc : ConcaveConvexFn K) (hne : (dom₂ K).Nonempty)
    (hs : ConvexSliceStructure K) (w : Y) :
    supportFn Bx (dom₂ (upperConjSaddle Bu Bx K)) w
      = ⨆ u ∈ ri (dom₁ K), recessionFn (fun y => K (u, y)) w := by
  rw [supportFn_dom₂_upperConjSaddle Bu Bx hF hcl hK hKcc hne hs w]
  refine iSup_congr fun u => iSup_congr fun hu => ?_
  exact (supportFn_convexDom_bifunOfSaddle_eq_iSup_sub Bx hKcc hs hu w).symm.trans
    (congrFun (recessionFn_slice_eq_supportFn_convexDom Bx hKcc hs hu) w).symm

end ConjRecession

end ConvexAnalysis
