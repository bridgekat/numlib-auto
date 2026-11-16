/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Duality.Pairing
import Numlib.Analysis.Convex.Operations.Closed
import Numlib.Analysis.Convex.Extremum.Lagrangian

/-!
# Adjoint bifunctions and dual programs

Let $U$ and $V$, and $X$ and $Y$, be real vector spaces in duality through pairings
$\langle u, v \rangle$ and $\langle x, y \rangle$. A bifunction $F$ from $U$ to $X$ assigns to each
$u \in U$ a function $F u : X \to [-\infty, +\infty]$, and the convex program $(P)$ is to minimize
$F 0$. The **adjoint** of $F$ is the bifunction $F^*$ from $Y$ to $V$ given by
$$(F^* y)(v) = \inf_{u, x} \bigl\{ F(u, x) - \langle x, y \rangle + \langle u, v \rangle \bigr\},$$
and the dual program $(P^*)$ is to maximize $F^* 0$ over $V$. This module develops the theory of the
adjoint in [rockafellar1970convex], §§29–30.

All results follow from one computation: $(F^* y)(v) = -h^*(-v, y)$, where $h(u, x) = F(u, x)$ is
the graph function of $F$ and $h^*$ is its conjugate for the product pairing. Thus $F^*$ is closed
and concave with no hypothesis on $F$, the second adjoint $F^{**}$ is the closure
$\operatorname{cl} F$, and the dual objective $F^* 0$ is the concave conjugate of $-\inf F$. The
same computation shows that $\operatorname{cl} F$ is computed slice by slice on the relative
interior of the effective domain of $F$. Hence the closure of a strongly consistent program has the
same optimal value and the same Kuhn–Tucker vectors as the program, and every optimal solution of
the program is an optimal solution of its closure.

## Main definitions

* `ConvexAnalysis.convexAdjointBifun`: the adjoint $F^*$ of a convex bifunction $F$.
* `ConvexAnalysis.concaveAdjointBifun`: the adjoint of a concave bifunction, the same formula with a
  supremum.
* `ConvexAnalysis.lowerAdjointBifun`: the bifunction $F_*^*$ of [rockafellar1970convex], the inverse
  of the adjoint, $(F_*^* v)(y) = -(F^* y)(v)$.
* `ConvexAnalysis.convexClBifun`: the closure $\operatorname{cl} F$, whose graph function is the
  closure of the graph function of $F$.
* `ConvexAnalysis.ClosedConvexBifun`: $F$ is closed if its graph function is closed.
* `ConvexAnalysis.ImageClosedBifun`: $F$ is image-closed if each function $F u$ is closed.

## Main results

* `ConvexAnalysis.convexAdjointBifun_eq_neg_convexConj_graphFn`: $(F^* y)(v) = -h^*(-v, y)$, where
  $h$ is the graph function of $F$.
* `ConvexAnalysis.concaveFn_graphFn_convexAdjointBifun`,
  `ConvexAnalysis.closedConcave_graphFn_convexAdjointBifun`,
  `ConvexAnalysis.concaveAdjointBifun_convexAdjointBifun_eq_convexClBifun`,
  `ConvexAnalysis.properConcave_graphFn_convexAdjointBifun_iff`: $F^*$ is concave and closed,
  $F^{**} = \operatorname{cl} F$ for convex $F$, and for closed convex $F$, $F^*$ is proper if and
  only if $F$ is proper. Together these are Theorem 30.1 of [rockafellar1970convex].
* `ConvexAnalysis.convexBifun_lowerAdjointBifun`,
  `ConvexAnalysis.closedConvexBifun_lowerAdjointBifun`,
  `ConvexAnalysis.lowerAdjointBifun_lowerAdjointBifun_eq_convexClBifun`,
  `ConvexAnalysis.convexAdjointBifun_flip_lowerAdjointBifun`: the same facts for $F_*^*$.
* `ConvexAnalysis.convexAdjointBifun_flip_inverseBifun`,
  `ConvexAnalysis.lowerAdjointBifun_eq_concaveAdjointBifun`: the inverse commutes with the adjoint,
  $(G_*)^* = (G^*)_*$.
* `ConvexAnalysis.convexAdjointBifun_zero_eq_concaveConj`: the dual objective $F^* 0$ is the concave
  conjugate of $-\inf F$.
* `ConvexAnalysis.convexAdjointBifun_zero_le`: weak duality, $(F^* 0)(v) \le \inf F 0$.
* `ConvexAnalysis.mem_kuhnTucker_iff_convexAdjointBifun_zero_eq`: the Kuhn–Tucker vectors of $(P)$
  are the points where the dual objective attains the finite optimal value of $(P)$.
* `ConvexAnalysis.convexClBifun_apply_eq_convexCl`, `ConvexAnalysis.infBifun_convexClBifun_eq`: on
  the relative interior of $\operatorname{dom} F$, $(\operatorname{cl} F) u = \operatorname{cl}(F
  u)$ and $\inf (\operatorname{cl} F) u = \inf F u$. With the two inclusions $\operatorname{dom} F
  \subseteq \operatorname{dom} \operatorname{cl} F \subseteq \operatorname{cl} \operatorname{dom}
  F$, this is Theorem 29.4 of [rockafellar1970convex].

## Notation

* $\operatorname{dom} F$: the effective domain `ConvexAnalysis.convexDomBifun F`, the set of $u$
  such that $F(u, x) < +\infty$ for some $x$.
* $\inf F$: the perturbation function `ConvexAnalysis.infBifun F`, $u \mapsto \inf_x F(u, x)$. Its
  value at $0$ is the optimal value of $(P)$.
* $F_*$: the inverse `ConvexAnalysis.inverseBifun F`, the bifunction from $X$ to $U$ with
  $(F_* x)(u) = -F(u, x)$.

## Implementation notes

* A bifunction is `ConvexAnalysis.Bifun U X`, which is `U → X → EReal`, and its graph function is
  `ConvexAnalysis.graphFn F`. The pairings are `Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ` and
  `Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ`, and the product pairing is `ConvexAnalysis.prodPairing Bu Bx`.
* The sign change is carried in the argument, not in a reflected pairing:
  $\langle u, -v \rangle + \langle x, y \rangle$ is the product pairing of $(u, x)$ with $(-v, y)$.
  Thus $F^*$ is `ConvexAnalysis.convexConj` at a reflected point, and the lemmas about
  `ConvexAnalysis.convexConj` apply without change.
* The two real terms $\langle u, v \rangle - \langle x, y \rangle$ are added in $\mathbb{R}$ and
  then cast to `EReal`, so the expression $\infty - \infty$ cannot occur.
* The dual objective uses the concave conjugate `ConvexAnalysis.concaveConj`, since the concave
  conjugate $g^*$ is not $-(-g)^*$ in general.
* The closedness of $F^*$ assumes `ConvexAnalysis.IsContinuousPairing (prodPairing Bu Bx).flip`, not
  the unflipped class. The closedness of a conjugate needs continuity on the side where the
  conjugate lives, and the unflipped form would need a topology on $U \times X$.
* "Closed" means equal to the closure `ConvexAnalysis.convexCl`, as in
  `ConvexAnalysis.ClosedConvex`. This predicate does not include convexity.
* Results are stated for $F_*^*$ as well as for $F^*$, so that the algebra of closed bifunctions
  stays among convex bifunctions and needs no concave closure of bifunctions.
-/

namespace ConvexAnalysis

section Defs

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ} {F : Bifun U X} {v : V} {y : Y}

/-- The **adjoint** of a bifunction $F$ from $U$ to $X$ is the bifunction $F^*$ from $Y$ to $V$
given by
$$(F^* y)(v) = \inf_{(u, x) \in U \times X} \bigl\{ F(u, x) + \langle u, v \rangle - \langle x,
  y \rangle \bigr\}.$$
It is a concave bifunction for every $F$.

The two real terms are added in $\mathbb{R}$ before they are cast to `EReal`. This follows §30
of [rockafellar1970convex]. -/
noncomputable def convexAdjointBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (F : Bifun U X) : Bifun Y V :=
  fun y v => ⨅ p : U × X, (F p.1 p.2 + ((Bu p.1 v - Bx p.2 y : ℝ) : EReal))

/-- The value $(F^* y)(v)$ of the adjoint is $\inf_{(u, x)} \{F(u, x) + \langle u, v \rangle -
\langle x, y \rangle\}$. -/
theorem convexAdjointBifun_apply (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (F : Bifun U X)
    (y : Y) (v : V) :
    convexAdjointBifun Bu Bx F y v = ⨅ p : U × X,
        (F p.1 p.2 + ((Bu p.1 v - Bx p.2 y : ℝ) : EReal)) :=
  rfl

/-- If $F(u_0, x_0) < +\infty$ for some $(u_0, x_0)$, then $(F^* y)(v) < +\infty$ for all $y$ and
$v$: the infimum that defines it is at most its term at $(u_0, x_0)$. -/
theorem convexAdjointBifun_ne_top {u₀ : U} {x₀ : X} (hF : F u₀ x₀ ≠ ⊤) (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (y : Y) (v : V) : convexAdjointBifun Bu Bx F y v ≠ ⊤ :=
  ne_top_of_le_ne_top (EReal.add_lt_top hF (EReal.coe_ne_top _)).ne (iInf_le _ (u₀, x₀))

/-- **The adjoint is a reflected conjugate.** Let $F$ be a bifunction from $U$ to $X$ with graph
function $h(u, x) = F(u, x)$. Then for all $y \in Y$ and $v \in V$,
$$(F^* y)(v) = -h^*(-v, y),$$
where $h^*$ is the conjugate of $h$ for the product pairing $\langle (u, x), (v, y) \rangle =
\langle u, v \rangle + \langle x, y \rangle$.

All results about the adjoint in this module follow from this identity. The conjugate is
`ConvexAnalysis.convexConj (ConvexAnalysis.prodPairing Bu Bx) (ConvexAnalysis.graphFn F)`. -/
theorem convexAdjointBifun_eq_neg_convexConj_graphFn (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (F : Bifun U X) (y : Y) (v : V) :
    convexAdjointBifun Bu Bx F y v = -(convexConj (prodPairing Bu Bx) (graphFn F) (-v, y)) := by
  rw [convexAdjointBifun_apply, convexConj_apply, EReal.neg_iSup]
  refine iInf_congr fun p => ?_
  have hpair : (prodPairing Bu Bx p (-v, y) : ℝ) = -(Bu p.1 v - Bx p.2 y) := by
    rw [prodPairing_apply, map_neg]
    ring
  rw [hpair, EReal.neg_coe_sub]
  change graphFn F p + ((Bu p.1 v - Bx p.2 y : ℝ) : EReal)
      = graphFn F p + -(-((Bu p.1 v - Bx p.2 y : ℝ) : EReal))
  rw [neg_neg]

end Defs

/-! ### The adjoint is a closed concave bifunction -/

section Closed

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ} {F : Bifun U X}

/-- The reflection $R : Y \times V \to V \times Y$, $R(y, v) = (-v, y)$, which turns the adjoint
into a conjugate. -/
def adjointSwap (V Y : Type*) [AddCommGroup V] [Module ℝ V] [AddCommGroup Y] [Module ℝ Y] :
    (Y × V) →ₗ[ℝ] (V × Y) :=
  LinearMap.prod (-LinearMap.snd ℝ Y V) (LinearMap.fst ℝ Y V)

/-- The reflection satisfies $R(y, v) = (-v, y)$. -/
@[simp] theorem adjointSwap_apply (V Y : Type*) [AddCommGroup V] [Module ℝ V] [AddCommGroup Y]
    [Module ℝ Y] (q : Y × V) : adjointSwap V Y q = (-q.2, q.1) := rfl

/-- The graph function of the adjoint is $(y, v) \mapsto -h^*(R(y, v))$, where $h^*$ is the
conjugate of the graph function $h$ of $F$ and $R(y, v) = (-v, y)$. -/
theorem graphFn_convexAdjointBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (F : Bifun U X) : graphFn (convexAdjointBifun Bu Bx F)
      = fun q => -(compLin (convexConj (prodPairing Bu Bx) (graphFn F)) (adjointSwap V Y) q) :=
  funext fun q => convexAdjointBifun_eq_neg_convexConj_graphFn Bu Bx F q.1 q.2

/-- The negative of the graph function of the adjoint is $h^* \circ R$, where $h^*$ is the conjugate
of the graph function $h$ of $F$ and $R(y, v) = (-v, y)$. The closedness, convexity and
properness results about $F^*$ use this form. -/
theorem neg_graphFn_convexAdjointBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (F : Bifun U X) : (fun q => -(graphFn (convexAdjointBifun Bu Bx F) q))
      = compLin (convexConj (prodPairing Bu Bx) (graphFn F)) (adjointSwap V Y) := by
  funext q
  rw [graphFn_convexAdjointBifun, neg_neg]

/-- **The adjoint of every bifunction is concave.** Let $F$ be any bifunction from $U$ to $X$. Then
the graph function $(y, v) \mapsto (F^* y)(v)$ of its adjoint is a concave function on
$Y \times V$.

No convexity, properness or closedness of $F$ is needed. This is part of Theorem 30.1 of
[rockafellar1970convex]. -/
theorem concaveFn_graphFn_convexAdjointBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (F : Bifun U X) : ConcaveFn (graphFn (convexAdjointBifun Bu Bx F)) := by
  rw [concaveFn_iff_convexFn_neg, neg_graphFn_convexAdjointBifun]
  exact convexFn_compLin _ (convexFn_convexConj _ _)

/-- The adjoint $F^*$ of every bifunction $F$ is a concave bifunction. -/
theorem concaveBifun_convexAdjointBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (F : Bifun U X) : ConcaveBifun (convexAdjointBifun Bu Bx F) :=
  concaveFn_graphFn_convexAdjointBifun Bu Bx F

/-- For every bifunction $F$, the bifunction $(y, v) \mapsto -(F^* y)(v)$ is convex. The concave
normality criteria use the adjoint in this form. -/
theorem convexBifun_neg_convexAdjointBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (F : Bifun U X) : ConvexBifun fun y v => -(convexAdjointBifun Bu Bx F y v) :=
  concaveFn_iff_convexFn_neg.1 (concaveFn_graphFn_convexAdjointBifun Bu Bx F)

/-- For every bifunction $F$ and every $y \in Y$, the function $F^* y$ on $V$ is concave. -/
theorem concaveFn_convexAdjointBifun_apply (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (F : Bifun U X) (y : Y) : ConcaveFn (convexAdjointBifun Bu Bx F y) :=
  concaveFn_iff_convexFn_neg.2 ((convexBifun_neg_convexAdjointBifun Bu Bx F).convexFn_apply y)

end Closed

section ClosedTopology

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [TopologicalSpace Y] [IsTopologicalAddGroup Y]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ}
  [IsContinuousPairing (prodPairing Bu Bx).flip] {F : Bifun U X}

omit [IsTopologicalAddGroup Y] [IsContinuousPairing (prodPairing Bu Bx).flip] in
/-- The reflection $R(y, v) = (-v, y)$ is continuous. -/
theorem continuous_adjointSwap : Continuous (adjointSwap V Y) := by
  change Continuous fun q : Y × V => ((-q.2, q.1) : V × Y)
  exact (continuous_neg.comp continuous_snd).prodMk continuous_fst

/-- **The adjoint of every bifunction is closed.** Let $V$ and $Y$ be topological additive groups,
and let the product pairing $\langle (u, x), (v, y) \rangle$ be continuous in
$(v, y) \in V \times Y$ for each fixed $(u, x)$. Then for every bifunction $F$, the graph
function of $F^*$ is a closed concave function, that is, it equals its concave closure.

The conjugate is closed, and closedness is preserved by the linear reflection
$R(y, v) = (-v, y)$. This is part of Theorem 30.1 of [rockafellar1970convex]. The continuity
hypothesis is `ConvexAnalysis.IsContinuousPairing (ConvexAnalysis.prodPairing Bu Bx).flip`. -/
theorem closedConcave_graphFn_convexAdjointBifun :
    ClosedConcave (graphFn (convexAdjointBifun Bu Bx F)) := by
  rw [closedConcave_iff_closedConvex_neg, neg_graphFn_convexAdjointBifun]
  exact closedConvex_compLin closedConvex_convexConj continuous_adjointSwap

end ClosedTopology

/-! ### The closure of a bifunction -/

section BifunClosure

variable {U X : Type*} [TopologicalSpace U] [TopologicalSpace X] {F : Bifun U X}

/-- The **closure** $\operatorname{cl} F$ of a bifunction $F$ from $U$ to $X$ is the bifunction
whose graph function is the closure of the graph function of $F$:
$$(\operatorname{cl} F)(u, x) = (\operatorname{cl} h)(u, x), \qquad h(u, x) = F(u, x).$$

The closure is `ConvexAnalysis.convexCl`. The second adjoint of a convex bifunction is its
closure, by `ConvexAnalysis.concaveAdjointBifun_convexAdjointBifun_eq_convexClBifun`. -/
noncomputable def convexClBifun (F : Bifun U X) : Bifun U X :=
    fun u x => convexCl (graphFn F) (u, x)

/-- The value $(\operatorname{cl} F)(u, x)$ is the value at $(u, x)$ of the closure of the graph
function of $F$. -/
theorem convexClBifun_apply (F : Bifun U X) (u : U) (x : X) :
    convexClBifun F u x = convexCl (graphFn F) (u, x) := rfl

/-- The graph function of $\operatorname{cl} F$ is the closure of the graph function of $F$. -/
@[simp] theorem graphFn_convexClBifun (F : Bifun U X) : graphFn (convexClBifun F)
    = convexCl (graphFn F) := rfl

/-- A bifunction $F$ is **closed** if its graph function $(u, x) \mapsto F(u, x)$ is closed, that
is, equal to its closure `ConvexAnalysis.convexCl`.

This predicate does not include convexity. -/
def ClosedConvexBifun (F : Bifun U X) : Prop := ClosedConvex (graphFn F)

/-- A bifunction is closed if and only if its graph function is closed. -/
theorem closedConvexBifun_iff : ClosedConvexBifun F ↔ ClosedConvex (graphFn F) := Iff.rfl

/-- The closure of a bifunction is at most the bifunction: $(\operatorname{cl} F)(u, x) \le F(u, x)$
for all $u$ and $x$. -/
theorem convexClBifun_le (F : Bifun U X) : convexClBifun F ≤ F :=
    fun u x => convexCl_le (graphFn F) (u, x)

/-- A closed bifunction is equal to its closure. -/
theorem ClosedConvexBifun.convexClBifun_eq (hF : ClosedConvexBifun F) : convexClBifun F = F :=
  funext fun u => funext fun x => congrFun hF (u, x)

/-- A bifunction is closed if and only if it is equal to its closure. -/
theorem closedConvexBifun_iff_convexClBifun_eq : ClosedConvexBifun F ↔ convexClBifun F = F := by
  refine ⟨fun hF => hF.convexClBifun_eq, fun hF => ?_⟩
  change convexCl (graphFn F) = graphFn F
  exact funext fun p => congrFun (congrFun hF p.1) p.2

end BifunClosure

section BifunClosureClosed

variable {U X : Type*} [TopologicalSpace U] [AddCommGroup U] [IsTopologicalAddGroup U]
  [TopologicalSpace X] [AddCommGroup X] [IsTopologicalAddGroup X]

/-- For topological additive groups $U$ and $X$, the closure $\operatorname{cl} F$ of every
bifunction $F$ is closed. -/
theorem closedConvexBifun_convexClBifun (F : Bifun U X) : ClosedConvexBifun (convexClBifun F) :=
  closedConvex_convexCl (graphFn F)

/-- If $F$ is a closed bifunction from $U$ to $X$, then the bifunction $(x, u) \mapsto F(u, x)$ from
$X$ to $U$ is closed. -/
theorem closedConvexBifun_flipBifun {F : Bifun U X} (hF : ClosedConvexBifun F) :
    ClosedConvexBifun (flipBifun F) := by
  rcases closedConvex_iff.1 (closedConvexBifun_iff.1 hF) with h | ⟨hlsc, hne⟩
  · exact closedConvex_iff.2 (Or.inl (funext fun q => congrFun h (q.2, q.1)))
  · exact closedConvex_iff.2 (Or.inr ⟨lowerSemicontinuous_comp hlsc
      (continuous_snd.prodMk continuous_fst), fun q => hne (q.2, q.1)⟩)

/-- **The inverse of a closed concave bifunction is closed.** Let $U$ and $X$ be topological
additive groups, and let $G$ be a bifunction from $U$ to $X$ whose graph function is equal to
its concave closure. Then the inverse $G_*$, $(G_* x)(u) = -G(u, x)$, is a closed bifunction
from $X$ to $U$.

The hypothesis is `ConvexAnalysis.ClosedConcave (ConvexAnalysis.graphFn G)`, and the inverse is
`ConvexAnalysis.inverseBifun G`. -/
theorem closedConvexBifun_inverseBifun {G : Bifun U X} (hG : ClosedConcave (graphFn G)) :
    ClosedConvexBifun (inverseBifun G) := by
  have h : ClosedConvexBifun fun u x => -(G u x) := closedConcave_iff_closedConvex_neg.1 hG
  exact closedConvexBifun_flipBifun h

end BifunClosureClosed

/-! ### The closure of a bifunction, slice by slice -/

section RelintClosure

open Filter Topology

variable {U X : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] {F : Bifun U X}

omit [FiniteDimensional ℝ U] [FiniteDimensional ℝ X] in
/-- The effective domain $\operatorname{dom} F$ of a bifunction is the image under the projection
$(u, x) \mapsto u$ of the effective domain of its graph function. Since the relative interior
and the closure commute with a linear image, the slice formula for $\operatorname{cl} F$ reduces
to a fact about the graph function. -/
theorem convexDomBifun_eq_image_convexDom_graphFn (F : Bifun U X) :
    convexDomBifun F = LinearMap.fst ℝ U X '' convexDom (graphFn F) := by
  ext u
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨(u, x), mem_convexDom.2 (lt_of_le_of_ne le_top hx), rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p.2, (mem_convexDom.1 hp).ne⟩

/-- **Relative interiors pass to slices.** Let $S \subseteq U \times X$ be convex, with $U$ and $X$
finite-dimensional real normed spaces. If $(u, x) \in \operatorname{ri} S$, then $x$ is in the
relative interior of the slice $\{y : (u, y) \in S\}$. -/
theorem mem_relint_slice {S : Set (U × X)} (hS : Convex ℝ S) {u : U} {x : X}
    (hux : (u, x) ∈ ri S) : x ∈ ri {y | (u, y) ∈ S} := by
  have hT : Convex ℝ {y | (u, y) ∈ S} := by
    intro a ha b hb s t hs ht hst
    have h := hS ha hb hs ht hst
    have hu : s • ((u, a) : U × X) + t • (u, b) = (u, s • a + t • b) := by
      rw [Prod.smul_mk, Prod.smul_mk, Prod.mk_add_mk, ← add_smul, hst, one_smul]
    rwa [hu] at h
  have hxT : ((u, x) : U × X) ∈ S := intrinsicInterior_subset hux
  refine (Convex.mem_relint_iff_prolong hT ⟨x, hxT⟩).2 fun y hy => ?_
  obtain ⟨μ, hμ, hmem⟩ := (Convex.mem_relint_iff_prolong hS ⟨(u, y), hy⟩).1 hux (u, y) hy
  refine ⟨μ, hμ, ?_⟩
  have hu : (1 - μ) • ((u, y) : U × X) + μ • (u, x) = (u, (1 - μ) • y + μ • x) := by
    rw [Prod.smul_mk, Prod.smul_mk, Prod.mk_add_mk, ← add_smul, sub_add_cancel, one_smul]
  rwa [hu] at hmem

/-- **The closure of a convex bifunction is computed slice by slice.** Let $U$ and $X$ be
finite-dimensional real normed spaces, let $F$ be a convex bifunction from $U$ to $X$, and let
$u \in \operatorname{ri}(\operatorname{dom} F)$. Then
$$(\operatorname{cl} F) u = \operatorname{cl}(F u).$$

This is part of Theorem 29.4 of [rockafellar1970convex]. A relative interior point of the
effective domain of the graph function lies over $u$, with $x$ in the relative interior of
$\operatorname{dom}(F u)$. Both closures are then the same limit along a segment in the slice. -/
theorem convexClBifun_apply_eq_convexCl (hF : ConvexBifun F) {u : U}
    (hu : u ∈ ri (convexDomBifun F)) :
    convexClBifun F u = convexCl (F u) := by
  have hconv : Convex ℝ (convexDom (graphFn F)) := ConvexFn.convex_convexDom hF
  have himg : u ∈ LinearMap.fst ℝ U X '' ri (convexDom (graphFn F)) := by
    rw [← Convex.relint_image hconv, ← convexDomBifun_eq_image_convexDom_graphFn]
    exact hu
  obtain ⟨⟨u', x⟩, hp, hpu⟩ := himg
  simp only [LinearMap.fst_apply] at hpu
  subst hpu
  have hslice : x ∈ ri (convexDom (F u')) := mem_relint_slice hconv hp
  have hxdom : x ∈ convexDom (F u') := intrinsicInterior_subset hslice
  by_cases hpr : ProperConvex (graphFn F)
  · have hFu : ProperConvex (F u') := ⟨⟨x, hxdom⟩, fun y => hpr.ne_bot (u', y)⟩
    funext y
    have h1 : Tendsto (fun a : ℝ => graphFn F ((1 - a) • ((u', x) : U × X) + a • (u', y)))
        (𝓝[<] (1 : ℝ)) (𝓝 (convexCl (graphFn F) (u', y))) :=
      ConvexFn.tendsto_convexCl_along_segment_relint hF hpr hp (u', y)
    have heq : (fun a : ℝ => graphFn F ((1 - a) • ((u', x) : U × X) + a • (u', y)))
        = fun a : ℝ => F u' ((1 - a) • x + a • y) := by
      funext a
      have hu : (1 - a) • ((u', x) : U × X) + a • (u', y) = (u', (1 - a) • x + a • y) := by
        rw [Prod.smul_mk, Prod.smul_mk, Prod.mk_add_mk, ← add_smul, sub_add_cancel, one_smul]
      rw [hu]
      rfl
    rw [heq] at h1
    exact tendsto_nhds_unique h1
      (ConvexFn.tendsto_convexCl_along_segment_relint (hF.convexFn_apply u') hFu hslice y)
  · have hbot : graphFn F (u', x) = ⊥ := ConvexFn.eq_bot_of_mem_relint_convexDom hF hpr hp
    have hb1 : lscHull (graphFn F) (u', x) = ⊥ :=
      le_bot_iff.1 (hbot ▸ lscHull_le (graphFn F) (u', x))
    have hb2 : lscHull (F u') x = ⊥ := le_bot_iff.1 (hbot ▸ lscHull_le (F u') x)
    rw [convexCl_of_exists_eq_bot ⟨x, hb2⟩]
    funext y
    rw [convexClBifun_apply, convexCl_of_exists_eq_bot ⟨(u', x), hb1⟩]

/-- **The closure does not change the optimal value on the relative interior.** Let $U$ and $X$ be
finite-dimensional real normed spaces, let $F$ be a convex bifunction from $U$ to $X$, and let
$u \in \operatorname{ri}(\operatorname{dom} F)$. Then
$$\inf_x (\operatorname{cl} F)(u, x) = \inf_x F(u, x).$$

A convex function and its closure have the same infimum, and by
`ConvexAnalysis.convexClBifun_apply_eq_convexCl` the function $(\operatorname{cl} F) u$ is the
closure of $F u$. This is part of Theorem 29.4 of [rockafellar1970convex]. -/
theorem infBifun_convexClBifun_eq (hF : ConvexBifun F) {u : U} (hu : u ∈ ri (convexDomBifun F)) :
    infBifun (convexClBifun F) u = infBifun F u := by
  rw [infBifun_apply, infBifun_apply, convexClBifun_apply_eq_convexCl hF hu]
  exact iInf_convexCl_eq_iInf (F u)

/-- Let $F$ be a convex bifunction from $U$ to $X$, with $U$ and $X$ finite-dimensional real normed
spaces, whose graph function is proper. Then $\operatorname{dom} F \subseteq
\operatorname{dom}(\operatorname{cl} F)$. -/
theorem convexDomBifun_subset_convexDomBifun_convexClBifun (hF : ConvexBifun F)
    (hp : ProperConvex (graphFn F)) :
    convexDomBifun F ⊆ convexDomBifun (convexClBifun F) := by
  rw [convexDomBifun_eq_image_convexDom_graphFn F,
      convexDomBifun_eq_image_convexDom_graphFn (convexClBifun F), graphFn_convexClBifun]
  refine Set.image_mono ?_
  rw [ConvexFn.convexCl_eq_lscHull hF hp]
  exact convexDom_subset_convexDom_lscHull _

/-- Let $F$ be a convex bifunction from $U$ to $X$, with $U$ and $X$ finite-dimensional real normed
spaces, whose graph function is proper. Then $\operatorname{dom}(\operatorname{cl} F) \subseteq
\operatorname{cl}(\operatorname{dom} F)$. -/
theorem convexDomBifun_convexClBifun_subset_closure (hF : ConvexBifun F)
    (hp : ProperConvex (graphFn F)) :
    convexDomBifun (convexClBifun F) ⊆ closure (convexDomBifun F) := by
  rw [convexDomBifun_eq_image_convexDom_graphFn F,
      convexDomBifun_eq_image_convexDom_graphFn (convexClBifun F), graphFn_convexClBifun]
  refine subset_trans (Set.image_mono ?_) (image_closure_subset_closure_image continuous_fst)
  rw [ConvexFn.convexCl_eq_lscHull hF hp]
  exact convexDom_lscHull_subset_closure_convexDom _

end RelintClosure

section ImageClosed

variable {U X : Type*} [TopologicalSpace X] {F : Bifun U X}

/-- A bifunction $F$ from $U$ to $X$ is **image-closed** if each function $F u$ on $X$ is closed,
that is, equal to its closure `ConvexAnalysis.convexCl`.

This is all that the correspondence between bifunctions and concave-convex functions depends on. -/
def ImageClosedBifun (F : Bifun U X) : Prop := ∀ u, ClosedConvex (F u)

/-- A bifunction is image-closed if and only if each function $F u$ is closed. -/
theorem imageClosedBifun_iff : ImageClosedBifun F ↔ ∀ u, ClosedConvex (F u) := Iff.rfl

end ImageClosed

section ImageClosedSlice

variable {U X : Type*} [TopologicalSpace U] [AddCommGroup U] [IsTopologicalAddGroup U]
  [TopologicalSpace X] [AddCommGroup X] [IsTopologicalAddGroup X] {F : Bifun U X}

/-- For topological additive groups $U$ and $X$, every closed bifunction from $U$ to $X$ is
image-closed: each slice of a closed function is closed. The converse is false, because
image-closedness says nothing about the joint behavior in $(u, x)$. -/
theorem ClosedConvexBifun.imageClosedBifun (hF : ClosedConvexBifun F) : ImageClosedBifun F := by
  intro u
  rcases closedConvex_iff.1 (closedConvexBifun_iff.1 hF) with h | ⟨hlsc, hne⟩
  · exact closedConvex_iff.2 (Or.inl (funext fun x => congrFun h (u, x)))
  · exact closedConvex_iff.2 (Or.inr ⟨lowerSemicontinuous_comp hlsc
      (continuous_const.prodMk continuous_id), fun x => hne (u, x)⟩)

end ImageClosedSlice

section BifunClosureConvex

variable {U X : Type*} [TopologicalSpace U] [AddCommGroup U] [Module ℝ U]
  [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [TopologicalSpace X] [AddCommGroup X]
  [Module ℝ X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] {F : Bifun U X}

/-- For topological vector spaces $U$ and $X$, the closure of a convex bifunction is convex. -/
theorem ConvexBifun.convexClBifun (hF : ConvexBifun F) :
    ConvexBifun (ConvexAnalysis.convexClBifun F) :=
  convexFn_convexCl hF

end BifunClosureConvex

section AdjointClosure

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [TopologicalSpace X] [IsTopologicalAddGroup X]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsContinuousPairing Bu] {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ}
  [IsContinuousPairing Bx] {F : Bifun U X}

/-- **The adjoint depends only on the closure.** Let $U$ and $X$ be topological additive groups, and
let the pairings $\langle u, v \rangle$ and $\langle x, y \rangle$ be continuous in $u$ and in
$x$. Then for every bifunction $F$ from $U$ to $X$, $(\operatorname{cl} F)^* = F^*$.

This is `ConvexAnalysis.convexConj_convexCl` for the graph function. -/
theorem convexAdjointBifun_convexClBifun : convexAdjointBifun Bu Bx (convexClBifun F)
    = convexAdjointBifun Bu Bx F := by
  funext y v
  rw [convexAdjointBifun_eq_neg_convexConj_graphFn, convexAdjointBifun_eq_neg_convexConj_graphFn,
      graphFn_convexClBifun,
    convexConj_convexCl]

end AdjointClosure

section NegAdjointClosed

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [TopologicalSpace Y] [IsTopologicalAddGroup Y]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ}
  [IsContinuousPairing (prodPairing Bu Bx).flip] {F : Bifun U X}

/-- Let $V$ and $Y$ be topological additive groups, and let the product pairing
$\langle (u, x), (v, y) \rangle$ be continuous in $(v, y) \in V \times Y$ for each fixed
$(u, x)$. Then for every bifunction $F$, the bifunction $(y, v) \mapsto -(F^* y)(v)$ is closed. -/
theorem closedConvexBifun_neg_convexAdjointBifun :
    ClosedConvexBifun fun y v => -(convexAdjointBifun Bu Bx F y v) :=
  closedConcave_iff_closedConvex_neg.1 closedConcave_graphFn_convexAdjointBifun

end NegAdjointClosed

section NegAdjointClosedSlice

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [TopologicalSpace Y] [IsTopologicalAddGroup Y]

/-- Let $V$ and $Y$ be topological additive groups, and let the pairings be continuous in $v$ and in
$y$. Then for every bifunction $F$ and every $y \in Y$, the function $v \mapsto -(F^* y)(v)$ is
closed. -/
theorem closedConvex_neg_convexAdjointBifun_apply (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsContinuousPairing Bu.flip]
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsContinuousPairing Bx.flip] (F : Bifun U X) (y : Y) :
    ClosedConvex fun v => -(convexAdjointBifun Bu Bx F y v) := by
  have := isContinuousPairing_prodPairing_flip Bu Bx
  have h : ClosedConvexBifun fun y v => -(convexAdjointBifun Bu Bx F y v) :=
      closedConvexBifun_neg_convexAdjointBifun
  exact h.imageClosedBifun y

end NegAdjointClosedSlice

/-! ### The second adjoint: $F^{**} = \operatorname{cl} F$ -/

section ConcaveAdjoint

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]

/-- The **adjoint of a concave bifunction** $G$ from $Y$ to $V$ is the bifunction $G^*$ from $U$ to
$X$ given by
$$(G^* u)(x) = \sup_{(y, v) \in Y \times V} \bigl\{ G(y, v) + \langle x, y \rangle - \langle u,
  v \rangle \bigr\}.$$

It is the formula of `ConvexAnalysis.convexAdjointBifun` with the infimum replaced by a
supremum. -/
noncomputable def concaveAdjointBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (G : Bifun Y V) : Bifun U X :=
  fun u x => ⨆ q : Y × V, (G q.1 q.2 + ((Bx x q.1 - Bu u q.2 : ℝ) : EReal))

/-- The value $(G^* u)(x)$ of the adjoint of a concave bifunction is $\sup_{(y, v)} \{G(y, v) +
\langle x, y \rangle - \langle u, v \rangle\}$. -/
theorem concaveAdjointBifun_apply (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (G : Bifun Y V) (u : U) (x : X) :
    concaveAdjointBifun Bu Bx G u x
      = ⨆ q : Y × V, (G q.1 q.2 + ((Bx x q.1 - Bu u q.2 : ℝ) : EReal)) := rfl

/-- The reflection $R(y, v) = (-v, y)$ is surjective: $(v, y) = R(y, -v)$. -/
theorem surjective_adjointSwap : Function.Surjective (adjointSwap V Y) :=
  fun w => ⟨(w.2, -w.1), by rw [adjointSwap_apply, neg_neg]⟩

/-- For every bifunction $F$ from $U$ to $X$, the concave adjoint of $F^*$ is the biconjugate of the
graph function $h$ of $F$:
$$(F^{**} u)(x) = h^{**}(u, x),$$
with both conjugates taken for the product pairing.

The two reflections cancel when the bound variables are renamed. -/
theorem concaveAdjointBifun_convexAdjointBifun_eq_convexBiconj (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (F : Bifun U X) (u : U) (x : X) :
    concaveAdjointBifun Bu Bx (convexAdjointBifun Bu Bx F) u x
      = convexBiconj (prodPairing Bu Bx) (graphFn F) (u, x) := by
  rw [concaveAdjointBifun_apply, convexBiconj_apply,
    ← (surjective_adjointSwap (V := V) (Y := Y)).iSup_comp
      (fun w : V × Y => ((prodPairing Bu Bx (u, x) w : ℝ) : EReal)
        - convexConj (prodPairing Bu Bx) (graphFn F) w)]
  refine iSup_congr fun q => ?_
  rw [convexAdjointBifun_eq_neg_convexConj_graphFn, adjointSwap_apply]
  have hpair : (prodPairing Bu Bx (u, x) (-q.2, q.1) : ℝ) = Bx x q.1 - Bu u q.2 := by
    rw [prodPairing_apply, map_neg]
    ring
  rw [hpair]
  exact add_comm _ _

end ConcaveAdjoint

/-! ### The adjoint of the inverse, $F_*^*$ -/

section LowerAdjoint

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y] {F : Bifun U X}

/-- The bifunction $F_*^*$ of [rockafellar1970convex]: for a bifunction $F$ from $U$ to $X$, the
convex bifunction from $V$ to $Y$ given by
$$(F_*^* v)(y) = -(F^* y)(v).$$

This definition makes $F_*^*$ the inverse $(F^*)_*$ of the adjoint. It is also the concave
adjoint $(F_*)^*$ of the inverse, by `ConvexAnalysis.lowerAdjointBifun_eq_concaveAdjointBifun`.
Working with $F_*^*$ keeps the algebra of closed bifunctions among convex bifunctions and needs
no concave closure of bifunctions. -/
noncomputable def lowerAdjointBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (F : Bifun U X) : Bifun V Y := fun v y => -(convexAdjointBifun Bu Bx F y v)

/-- The value $(F_*^* v)(y)$ is $-(F^* y)(v)$. -/
@[simp] theorem lowerAdjointBifun_apply (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (F : Bifun U X) (v : V) (y : Y) :
    lowerAdjointBifun Bu Bx F v y = -(convexAdjointBifun Bu Bx F y v) := rfl

/-- The bifunction $F_*^*$ is the inverse of the adjoint $F^*$, by definition. -/
theorem lowerAdjointBifun_eq_inverseBifun_convexAdjointBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (F : Bifun U X) :
    lowerAdjointBifun Bu Bx F = inverseBifun (convexAdjointBifun Bu Bx F) := rfl

/-- **The inverse commutes with the adjoint, concave orientation.** Let $G$ be a bifunction from $Y$
to $V$. Then the convex adjoint of the inverse $G_*$, for the flipped pairings, is the inverse
of the concave adjoint of $G$:
$$(G_*)^* = (G^*)_*.$$

No hypothesis on $G$ is needed: both sides are the same iterated extremum, and the proof
exchanges two bound variables. The flipped pairings are `Bu.flip` and `Bx.flip`. -/
theorem convexAdjointBifun_flip_inverseBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (G : Bifun Y V) :
    convexAdjointBifun Bu.flip Bx.flip (inverseBifun G)
      = inverseBifun (concaveAdjointBifun Bu Bx G) := by
  funext x u
  have hpt : ∀ (v : V) (y : Y),
      inverseBifun G v y + ((Bu u v - Bx x y : ℝ) : EReal)
        = -(G y v + ((Bx x y - Bu u v : ℝ) : EReal)) := by
    intro v y
    have hneg : -(G y v + ((Bx x y - Bu u v : ℝ) : EReal))
        = -(G y v) + -(((Bx x y - Bu u v : ℝ) : EReal)) :=
      EReal.neg_add (.inr (EReal.coe_ne_top _))
        (.inr (EReal.coe_ne_bot _))
    have hr : (Bu u v - Bx x y : ℝ) = -(Bx x y - Bu u v) := by ring
    rw [hneg, inverseBifun_apply, hr, EReal.coe_neg]
  rw [inverseBifun_apply, concaveAdjointBifun_apply, EReal.neg_iSup, iInf_prod,
    convexAdjointBifun_apply, iInf_prod, iInf_comm]
  exact iInf_congr fun y => iInf_congr fun v => hpt v y

/-- **The inverse commutes with the adjoint, convex orientation.** For every bifunction $F$ from $U$
to $X$, the bifunction $F_*^* = (F^*)_*$ is the concave adjoint of the inverse $F_*$, for the
flipped pairings:
$$(F^*)_* = (F_*)^*.$$

This is `ConvexAnalysis.convexAdjointBifun_flip_inverseBifun` for $G = F_*$. -/
theorem lowerAdjointBifun_eq_concaveAdjointBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (F : Bifun U X) :
    lowerAdjointBifun Bu Bx F = concaveAdjointBifun Bu.flip Bx.flip (inverseBifun F) := by
  have h := convexAdjointBifun_flip_inverseBifun Bu.flip Bx.flip (inverseBifun F)
  simp only [LinearMap.flip_flip, inverseBifun_inverseBifun] at h
  rw [lowerAdjointBifun_eq_inverseBifun_convexAdjointBifun, h, inverseBifun_inverseBifun]

/-- For every bifunction $F$, the bifunction $F_*^*$ is convex, since it is the inverse of the
concave bifunction $F^*$. -/
theorem convexBifun_lowerAdjointBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (F : Bifun U X) : ConvexBifun (lowerAdjointBifun Bu Bx F) :=
  convexBifun_inverseBifun (concaveBifun_convexAdjointBifun Bu Bx F)

/-- If $F(u_0, x_0) < +\infty$ for some $(u_0, x_0)$, then $(F_*^* v)(y) > -\infty$ for all $v$ and
$y$. -/
theorem lowerAdjointBifun_ne_bot {u₀ : U} {x₀ : X} (hF : F u₀ x₀ ≠ ⊤)
    (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (v : V) (y : Y) :
    lowerAdjointBifun Bu Bx F v y ≠ ⊥ := by
  rw [lowerAdjointBifun_apply]
  simpa using convexAdjointBifun_ne_top hF Bu Bx y v

end LowerAdjoint

section LowerAdjointClosed

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace V] [IsTopologicalAddGroup V] [TopologicalSpace Y] [IsTopologicalAddGroup Y]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ}
  [IsContinuousPairing (prodPairing Bu Bx).flip] {F : Bifun U X}

/-- **$F_*^*$ is a closed convex bifunction, for every $F$.** Let $V$ and $Y$ be topological
additive groups, and let the product pairing $\langle (u, x), (v, y) \rangle$ be continuous in
$(v, y) \in V \times Y$ for each fixed $(u, x)$. Then for every bifunction $F$ from $U$ to $X$,
the bifunction $F_*^*$ is closed.

The adjoint $F^*$ is closed and concave for every $F$, and $F_*^*$ is its inverse. Thus every
bifunction of the form $H_*^*$ is closed. -/
theorem closedConvexBifun_lowerAdjointBifun : ClosedConvexBifun (lowerAdjointBifun Bu Bx F) :=
  closedConvexBifun_inverseBifun closedConcave_graphFn_convexAdjointBifun

end LowerAdjointClosed

section SecondAdjoint

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsCompatiblePairing Bu] {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ}
  [IsCompatiblePairing Bx] {F : Bifun U X}

/-- **The second adjoint is the closure.** Let $U$ and $X$ be locally convex real topological vector
spaces, and let the pairings $\langle u, v \rangle$ and $\langle x, y \rangle$ be compatible
with their topologies. Then for every convex bifunction $F$ from $U$ to $X$,
$$F^{**} = \operatorname{cl} F.$$

This is part of Theorem 30.1 of [rockafellar1970convex]. The two adjoints compose to the
biconjugate of the graph function, and the Fenchel–Moreau theorem turns this into its closure.
The compatibility of the product pairing follows from the compatibility of the two pairings,
which is `ConvexAnalysis.IsCompatiblePairing`. -/
theorem concaveAdjointBifun_convexAdjointBifun_eq_convexClBifun (hF : ConvexBifun F) :
    concaveAdjointBifun Bu Bx (convexAdjointBifun Bu Bx F) = convexClBifun F := by
  funext u x
  rw [concaveAdjointBifun_convexAdjointBifun_eq_convexBiconj, convexClBifun_apply]
  exact congrFun (convexBiconj_eq_convexCl (B := prodPairing Bu Bx) hF) (u, x)

/-- Under the hypotheses of
`ConvexAnalysis.concaveAdjointBifun_convexAdjointBifun_eq_convexClBifun`, a closed convex
bifunction $F$ satisfies $F^{**} = F$. -/
theorem concaveAdjointBifun_convexAdjointBifun_eq_self (hF : ConvexBifun F)
    (hcl : ClosedConvexBifun F) :
    concaveAdjointBifun Bu Bx (convexAdjointBifun Bu Bx F) = F := by
  rw [concaveAdjointBifun_convexAdjointBifun_eq_convexClBifun hF, hcl.convexClBifun_eq]

/-- **The second adjoint in the form $F_*^*$.** Let $U$ and $X$ be locally convex real topological
vector spaces with compatible pairings. Then for every convex bifunction $F$, applying the
construction $F \mapsto F_*^*$ twice, the second time for the flipped pairings, gives
$\operatorname{cl} F$.

The inverse commutes with the adjoint and is an involution, so this is
$F^{**} = \operatorname{cl} F$. -/
theorem lowerAdjointBifun_lowerAdjointBifun_eq_convexClBifun (hF : ConvexBifun F) :
    lowerAdjointBifun Bu.flip Bx.flip (lowerAdjointBifun Bu Bx F) = convexClBifun F := by
  rw [lowerAdjointBifun_eq_inverseBifun_convexAdjointBifun,
    lowerAdjointBifun_eq_inverseBifun_convexAdjointBifun, convexAdjointBifun_flip_inverseBifun,
    inverseBifun_inverseBifun, concaveAdjointBifun_convexAdjointBifun_eq_convexClBifun hF]

/-- **The adjoint of $F_*^*$ is the inverse of $F$.** Let $U$ and $X$ be locally convex real
topological vector spaces with compatible pairings, and let $F$ be a closed convex bifunction
from $U$ to $X$. Then the adjoint of $F_*^*$, for the flipped pairings, is the inverse $F_*$:
$$(F_*^*)^* = F_*.$$

The proof is `ConvexAnalysis.convexAdjointBifun_flip_inverseBifun` followed by $F^{**} = F$ for
closed convex $F$. -/
theorem convexAdjointBifun_flip_lowerAdjointBifun (hF : ConvexBifun F) (hcl : ClosedConvexBifun F) :
    convexAdjointBifun Bu.flip Bx.flip (lowerAdjointBifun Bu Bx F) = inverseBifun F := by
  rw [lowerAdjointBifun_eq_inverseBifun_convexAdjointBifun, convexAdjointBifun_flip_inverseBifun,
    concaveAdjointBifun_convexAdjointBifun_eq_self hF hcl]

/-- Let $U$ and $X$ be locally convex real topological vector spaces with compatible pairings, and
let the graph function of $F$ be closed, proper and convex. Then $(F^* y)(v) > -\infty$ for some
$y$ and $v$.

This is the properness of a conjugate, read through
`ConvexAnalysis.convexAdjointBifun_eq_neg_convexConj_graphFn`. -/
theorem exists_convexAdjointBifun_ne_bot (hF : ClosedProperConvexFn (graphFn F)) :
    ∃ (y : Y) (v : V), convexAdjointBifun Bu Bx F y v ≠ ⊥ := by
  obtain ⟨q, hq⟩ := (properConvex_convexConj (B := prodPairing Bu Bx) hF).convexDom_nonempty
  refine ⟨q.2, -q.1, ?_⟩
  rw [convexAdjointBifun_eq_neg_convexConj_graphFn, neg_neg]
  simpa using hq.ne

/-- **The adjoint is proper exactly when the bifunction is.** Let $U$ and $X$ be locally convex real
topological vector spaces with compatible pairings, and let $F$ be a closed convex bifunction
from $U$ to $X$. Then the graph function of $F^*$ is a proper concave function if and only if
the graph function of $F$ is a proper convex function.

This is part of Theorem 30.1 of [rockafellar1970convex]. It is the properness of a conjugate,
read through the surjective reflection $(y, v) \mapsto (-v, y)$. Closedness is used only for the
implication from the properness of $F$ to the properness of $F^*$. -/
theorem properConcave_graphFn_convexAdjointBifun_iff (hF : ConvexBifun F)
    (hcl : ClosedConvexBifun F) :
    ProperConcave (graphFn (convexAdjointBifun Bu Bx F)) ↔ ProperConvex (graphFn F) := by
  rw [properConcave_iff_properConvex_neg, neg_graphFn_convexAdjointBifun,
    properConvex_compLin_of_surjective surjective_adjointSwap,
    properConvex_convexConj_iff (B := prodPairing Bu Bx) hF hcl]

end SecondAdjoint

section LowerAdjointProper

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X]
  {F : Bifun U X}

/-- Let $U$ and $X$ be locally convex real topological vector spaces with compatible pairings, and
let the graph function of $F$ be closed, proper and convex. Then $(F_*^* v)(y) < +\infty$ for
some $v$ and $y$. -/
theorem exists_lowerAdjointBifun_ne_top (hF : ClosedProperConvexFn (graphFn F))
    (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bx] : ∃ (v : V) (y : Y), lowerAdjointBifun Bu Bx F v y ≠ ⊤ := by
  obtain ⟨y, v, hyv⟩ := exists_convexAdjointBifun_ne_bot (Bu := Bu) (Bx := Bx) (F := F) hF
  exact ⟨v, y, by rw [lowerAdjointBifun_apply]; simpa using hyv⟩

end LowerAdjointProper

/-! ### The dual objective -/

section Dual

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ} {F : Bifun U X} {v : V}

/-- The dual objective is $(F^* 0)(v) = \inf_u \{\langle u, v \rangle + \inf_x F(u, x)\}$. -/
theorem convexAdjointBifun_zero_apply (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (F : Bifun U X) (v : V) :
    convexAdjointBifun Bu Bx F 0 v = ⨅ u, (((Bu u v : ℝ) : EReal) + infBifun F u) := by
  rw [convexAdjointBifun_apply, iInf_prod]
  refine iInf_congr fun u => ?_
  have hzero : ∀ x : X, (Bu u v - Bx x 0 : ℝ) = Bu u v := fun x => by
    rw [map_zero, sub_zero]
  simp only [hzero]
  rw [infBifun_apply, add_comm, EReal.iInf_add_coe]

/-- **The dual objective is a concave conjugate.** For every bifunction $F$ from $U$ to $X$, the
dual objective $F^* 0$ is the concave conjugate, for the pairing $\langle u, v \rangle$, of the
concave function $u \mapsto -\inf_x F(u, x)$:
$$(F^* 0)(v) = \inf_u \bigl\{ \langle u, v \rangle + \inf_x F(u, x) \bigr\}.$$

The concave conjugate is `ConvexAnalysis.concaveConj`. -/
theorem convexAdjointBifun_zero_eq_concaveConj (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (F : Bifun U X) :
    convexAdjointBifun Bu Bx F 0 = concaveConj Bu (fun u => -(infBifun F u)) := by
  funext v
  rw [convexAdjointBifun_zero_apply, concaveConj_apply]
  exact iInf_congr fun u => by rw [sub_eq_add_neg, neg_neg]

/-- **Weak duality.** For every bifunction $F$ from $U$ to $X$ and every $v \in V$, the value of the
dual objective at $v$ is at most the optimal value of $(P)$:
$$(F^* 0)(v) \le \inf_x F(0, x).$$

No hypothesis on $F$ is needed. -/
theorem convexAdjointBifun_zero_le (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (F : Bifun U X)
    (v : V) : convexAdjointBifun Bu Bx F 0 v ≤ infBifun F 0 := by
  rw [convexAdjointBifun_zero_apply]
  exact iInf_add_infBifun_le Bu F v

/-- **Kuhn–Tucker vectors are dual optimal points.** For every bifunction $F$ from $U$ to $X$, a
vector $v \in V$ is a Kuhn–Tucker vector of $(P)$ if and only if the optimal value $\inf F 0$ is
finite and
$$(F^* 0)(v) = \inf_x F(0, x).$$

This holds without normality. The Kuhn–Tucker vectors are `ConvexAnalysis.KuhnTucker`. -/
theorem mem_kuhnTucker_iff_convexAdjointBifun_zero_eq (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) :
    v ∈ KuhnTucker Bu F ↔ infBifun F 0 ≠ ⊤ ∧ infBifun F 0 ≠ ⊥ ∧
      convexAdjointBifun Bu Bx F 0 v = infBifun F 0 := by
  rw [KuhnTucker, Set.mem_ofPred_eq, convexAdjointBifun_zero_apply]

/-- **Weak duality, supremum form.** For every bifunction $F$, the supremum of the dual objective is
at most the optimal value of $(P)$: $\sup_v (F^* 0)(v) \le \inf_x F(0, x)$. -/
theorem iSup_convexAdjointBifun_zero_le (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (F : Bifun U X) : (⨆ v, convexAdjointBifun Bu Bx F 0 v) ≤ infBifun F 0 :=
  iSup_le (convexAdjointBifun_zero_le Bu Bx F)

end Dual

/-! ### Closing a strongly consistent program changes nothing -/

section ClosureInvariance

open Filter Topology

variable {U X : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] {F : Bifun U X}

/-- Let $U$ and $X$ be finite-dimensional real normed spaces, and let $F$ be a convex bifunction
from $U$ to $X$ whose graph function is proper. Then
$$\operatorname{ri}(\operatorname{dom} \operatorname{cl} F) =
  \operatorname{ri}(\operatorname{dom} F).$$

The set $\operatorname{dom} \operatorname{cl} F$ lies between $\operatorname{dom} F$ and
$\operatorname{cl}(\operatorname{dom} F)$, and every such set has the same relative interior. -/
theorem relint_convexDomBifun_convexClBifun (hF : ConvexBifun F) (hp : ProperConvex (graphFn F)) :
    ri (convexDomBifun (convexClBifun F)) = ri (convexDomBifun F) := by
  have hconv : Convex ℝ (convexDomBifun F) := convex_convexDomBifun hF
  have hconvcl : Convex ℝ (convexDomBifun (convexClBifun F)) :=
      convex_convexDomBifun (ConvexBifun.convexClBifun hF)
  refine (Convex.closure_eq_iff_relint_eq hconvcl hconv).1 ?_
  exact Convex.closure_eq_of_relint_subset_of_subset_closure hconv
    (intrinsicInterior_subset.trans (convexDomBifun_subset_convexDomBifun_convexClBifun hF hp))
    (convexDomBifun_convexClBifun_subset_closure hF hp)

/-- Let $U$ and $X$ be finite-dimensional real normed spaces, and let $F$ be a convex bifunction
from $U$ to $X$ whose graph function is proper. If $(P)$ is strongly consistent, that is,
$0 \in \operatorname{ri}(\operatorname{dom} F)$, then the program of $\operatorname{cl} F$ is
strongly consistent. -/
theorem stronglyConsistent_convexClBifun (hF : ConvexBifun F) (hp : ProperConvex (graphFn F))
    (hs : StronglyConsistent F) : StronglyConsistent (convexClBifun F) := by
  rw [StronglyConsistent, relint_convexDomBifun_convexClBifun hF hp]
  exact hs

/-- Let $U$ and $X$ be finite-dimensional real normed spaces, and let $F$ be a strongly consistent
convex bifunction from $U$ to $X$. Then the objective of the closed program is the closure of
the objective: $(\operatorname{cl} F) 0 = \operatorname{cl}(F 0)$. -/
theorem convexClBifun_zero_eq_convexCl (hF : ConvexBifun F) (hs : StronglyConsistent F) :
    convexClBifun F 0 = convexCl (F 0) :=
  convexClBifun_apply_eq_convexCl hF hs

/-- Let $U$ and $X$ be finite-dimensional real normed spaces, and let $F$ be a strongly consistent
convex bifunction from $U$ to $X$. Then the programs of $F$ and of $\operatorname{cl} F$ have
the same optimal value: $\inf_x (\operatorname{cl} F)(0, x) = \inf_x F(0, x)$. -/
theorem infBifun_convexClBifun_zero_eq (hF : ConvexBifun F) (hs : StronglyConsistent F) :
    infBifun (convexClBifun F) 0 = infBifun F 0 :=
  infBifun_convexClBifun_eq hF hs

/-- Let $U$ and $X$ be finite-dimensional real normed spaces, and let $F$ be a strongly consistent
convex bifunction from $U$ to $X$. Then every minimizer of $F 0$ is a minimizer of
$(\operatorname{cl} F) 0$.

The inclusion is strict in general, because the closure can create new minimizers. -/
theorem argmin_subset_argmin_convexClBifun (hF : ConvexBifun F) (hs : StronglyConsistent F) :
    argmin (F 0) ⊆ argmin (convexClBifun F 0) := by
  rw [convexClBifun_zero_eq_convexCl hF hs]
  intro x hx
  rw [mem_argmin_iff_le_iInf] at hx ⊢
  rw [iInf_convexCl_eq_iInf]
  exact le_trans (convexCl_le _ x) hx

/-- Let $U$ and $X$ be finite-dimensional real normed spaces, and let $F$ be a strongly consistent
convex bifunction from $U$ to $X$ whose graph function is proper. Then the perturbation
functions $\inf \operatorname{cl} F$ and $\inf F$ agree on a neighborhood of $0$.

The slice formula gives agreement only on $\operatorname{ri}(\operatorname{dom} F)$, a relative
neighborhood of $0$. Outside the affine hull of $\operatorname{dom} F$ both perturbation
functions are $+\infty$. Since $\operatorname{ri}(\operatorname{dom} F)$ is relatively open and
$\operatorname{dom} \operatorname{cl} F \subseteq \operatorname{cl}(\operatorname{dom} F)
\subseteq \operatorname{aff}(\operatorname{dom} F)$, a small ball around $0$ meets no other
points. -/
theorem eventually_infBifun_convexClBifun_eq (hF : ConvexBifun F) (hp : ProperConvex (graphFn F))
    (hs : StronglyConsistent F) :
    ∀ᶠ u in 𝓝 (0 : U), infBifun (convexClBifun F) u = infBifun F u := by
  have hconv : Convex ℝ (convexDomBifun F) := convex_convexDomBifun hF
  have h0 : (0 : U) ∈ ri (ri (convexDomBifun F)) := by
    rw [Convex.relint_relint hconv]
    exact hs
  obtain ⟨-, ε, hε, hball⟩ := mem_intrinsicInterior_iff.1 h0
  rw [Metric.eventually_nhds_iff]
  refine ⟨ε, hε, fun {u} hu => ?_⟩
  by_cases haff : u ∈ affineSpan ℝ (convexDomBifun F)
  · refine infBifun_convexClBifun_eq hF (hball u ?_ hu)
    rwa [Convex.affineSpan_relint hconv]
  · have hcl : u ∉ convexDomBifun (convexClBifun F) := fun hmem =>
      haff (closure_subset_affineSpan _ (convexDomBifun_convexClBifun_subset_closure hF hp hmem))
    have hF0 : u ∉ convexDomBifun F := fun hmem => haff (subset_affineSpan ℝ _ hmem)
    rw [infBifun_eq_top_of_notMem_convexDomBifun hcl, infBifun_eq_top_of_notMem_convexDomBifun hF0]

end ClosureInvariance

section ClosureKuhnTucker

variable {U V X : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [AddCommGroup V] [Module ℝ V] [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsContinuousPairing Bu] {F : Bifun U X}

/-- Let $U$ and $X$ be finite-dimensional real normed spaces, let the pairings
$\langle u, v \rangle$ and $\langle x, y \rangle$ be continuous in $u$ and in $x$, and let $F$
be a strongly consistent convex bifunction from $U$ to $X$. Then the programs of $F$ and of
$\operatorname{cl} F$ have the same Kuhn–Tucker vectors.

A Kuhn–Tucker vector is a point where the dual objective attains the optimal value. The adjoint
does not change under the closure, and strong consistency makes the two optimal values equal. -/
theorem kuhnTucker_convexClBifun_eq {Y : Type*} [AddCommGroup Y] [Module ℝ Y]
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsContinuousPairing Bx] (hF : ConvexBifun F)
    (hs : StronglyConsistent F) : KuhnTucker Bu (convexClBifun F) = KuhnTucker Bu F := by
  have hval : infBifun (convexClBifun F) 0 = infBifun F 0 := infBifun_convexClBifun_eq hF hs
  ext v
  rw [mem_kuhnTucker_iff_convexAdjointBifun_zero_eq (Bx := Bx),
    mem_kuhnTucker_iff_convexAdjointBifun_zero_eq (Bx := Bx),
        convexAdjointBifun_convexClBifun, hval]

end ClosureKuhnTucker

end ConvexAnalysis
