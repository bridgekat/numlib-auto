/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Extremum.Adjoint
import Numlib.Analysis.Convex.Extremum.Minimum

/-!
# Normality of a dual pair of convex programs

Let $F$ be a convex bifunction from $U$ to $X$, with the program $(P)$ and the perturbation function
$\inf F$ of `Numlib.Analysis.Convex.Extremum.Perturbation`. Let $V$ and $Y$ be paired with $U$ and
$X$, and let $F^*$ be the adjoint bifunction, $(F^* y)(v) = \inf_{u, x} \{(Fu)(x) - \langle x, y
\rangle + \langle u, v \rangle\}$. The dual program $(P^*)$ is the concave program associated with
$F^*$: maximize the dual objective $F^* 0$ over $V$. The program $(P)$ is **normal** when its
perturbation function is closed at the origin:
$$(\operatorname{cl} (\inf F))(0) = (\inf F)(0).$$
The presentation follows §30 of [rockafellar1970convex].

This one condition is equivalent to the absence of a duality gap, $\sup_v (F^* 0)(v) = (\inf F)(0)$,
and, for closed $F$, to the normality of $(P^*)$. Ten sufficient conditions for normality are
collected below. Under normality, the Kuhn–Tucker vectors of $(P)$ are exactly the optimal solutions
of $(P^*)$. All of this rests on the Fenchel–Moreau theorem at the origin, $(\operatorname{cl}
f)(0) = \sup_y \inf_x \{\langle x, y \rangle + f(x)\}$. For $f = \inf F$ the inner infimum is the
dual objective $(F^* 0)(y)$, so $(\operatorname{cl} (\inf F))(0) = \sup_v (F^* 0)(v)$.

## Main definitions

* `ConvexAnalysis.Normal`: normality of the program associated with a bifunction $F$.
* `ConvexAnalysis.ConcaveNormal`: normality of a concave program, the concave counterpart of
  `ConvexAnalysis.Normal`. It is normality of the convex program $-G$
  (`ConvexAnalysis.concaveNormal_iff_normal_neg`).

## Main results

* `ConvexAnalysis.convexCl_infBifun_zero_eq_iSup_convexAdjointBifun`,
  `ConvexAnalysis.concaveCl_supBifun_convexAdjointBifun_zero_eq`: the optimal value of each program
  is the perturbation function of the other program, closed at the origin.
* `ConvexAnalysis.not_concaveConsistent_convexAdjointBifun_iff`,
  `ConvexAnalysis.not_consistent_iff_exists_supBifun_eq_top`: one program is inconsistent exactly
  when some perturbation of the other program is unbounded.
* `ConvexAnalysis.liminf_infBifun_eq_iSup_convexAdjointBifun`,
  `ConvexAnalysis.limsup_supBifun_convexAdjointBifun_eq`: the optimal values as a limit inferior and
  a limit superior.
* `ConvexAnalysis.normal_iff_iSup_convexAdjointBifun_eq`,
  `ConvexAnalysis.concaveNormal_convexAdjointBifun_iff`,
  `ConvexAnalysis.normal_iff_concaveNormal_convexAdjointBifun`: normality of $(P)$, the absence of a
  duality gap, and normality of $(P^*)$ are one condition. This is Theorem 30.3 of
  [rockafellar1970convex].
* `ConvexAnalysis.StronglyConsistent.normal`,
  `ConvexAnalysis.normal_of_concaveStronglyConsistent_convexAdjointBifun`,
  `ConvexAnalysis.normal_of_kuhnTucker_nonempty`,
  `ConvexAnalysis.normal_of_concaveKuhnTucker_convexAdjointBifun_nonempty`,
  `ConvexAnalysis.normal_of_exists_setOf_le`,
  `ConvexAnalysis.normal_of_argmin_nonempty_and_isBounded`,
  `ConvexAnalysis.normal_of_exists_setOf_ge_convexAdjointBifun`,
  `ConvexAnalysis.normal_of_argmax_convexAdjointBifun_nonempty_and_isBounded`,
  `ConvexAnalysis.PolyhedralBifun.normal`,
  `ConvexAnalysis.normal_of_concavePolyhedral_convexAdjointBifun`: the ten sufficient conditions for
  normality of Theorem 30.4 of [rockafellar1970convex].
* `ConvexAnalysis.mem_kuhnTucker_iff_convexAdjointBifun_zero_eq_iSup`,
  `ConvexAnalysis.kuhnTucker_eq_setOf_isMax`: under normality, the Kuhn–Tucker vectors of $(P)$ are
  exactly the optimal solutions of $(P^*)$.
  `ConvexAnalysis.mem_concaveKuhnTucker_convexAdjointBifun_iff_mem_argmin` is the dual assertion.
  This is Theorem 30.5 of [rockafellar1970convex].
* `ConvexAnalysis.exists_infBifun_eq_of_concaveStronglyConsistent`: if $(P)$ is consistent and
  $(P^*)$ is strongly consistent, the infimum of $(P)$ is attained.

## Implementation notes

* The first formula for $(\operatorname{cl} (\inf F))(0)$ needs only convexity of $F$, not
  closedness. It is the Fenchel–Moreau theorem for $\inf F$, and the adjoint does not distinguish
  $F$ from $\operatorname{cl} F$. So normality and the absence of a duality gap agree for every
  convex bifunction, and only the normality of the dual needs `ConvexAnalysis.ClosedConvexBifun F`.
* A Kuhn–Tucker vector implies normality through weak duality, not through subgradients, so this
  criterion needs no finite dimension.
-/

open Filter Topology

namespace ConvexAnalysis

/-! ### Normality -/

section Normal

variable {U X : Type*} [AddCommGroup U] [TopologicalSpace U] {F : Bifun U X}

/-- Let $U$ be a topological vector space and let $F$ be a bifunction from $U$ to $X$. The program
associated with $F$ is **normal** when its perturbation function is closed at the origin:
$$(\operatorname{cl} (\inf F))(0) = (\inf F)(0).$$

When $0$ is in the closure of $\operatorname{dom} F$, this is lower semicontinuity of
$u \mapsto (\inf F)(u)$ at $u = 0$. The closure is `ConvexAnalysis.convexCl`. -/
def Normal (F : Bifun U X) : Prop := convexCl (infBifun F) 0 = infBifun F 0

/-- The program associated with $F$ is normal if and only if
$(\operatorname{cl} (\inf F))(0) = (\inf F)(0)$. -/
theorem normal_iff : Normal F ↔ convexCl (infBifun F) 0 = infBifun F 0 := Iff.rfl

end Normal

section ConcaveNormality

variable {V Y : Type*} [AddCommGroup Y] [TopologicalSpace Y] {G : Bifun Y V}

/-- The concave program associated with a bifunction $G$ is **normal** when
$$(\operatorname{cl} (\sup G))(0) = (\sup G)(0),$$
where the closure is the concave closure `ConvexAnalysis.concaveCl`. This is the concave
counterpart of `ConvexAnalysis.Normal`. -/
def ConcaveNormal (G : Bifun Y V) : Prop := concaveCl (supBifun G) 0 = supBifun G 0

/-- The concave program associated with $G$ is normal if and only if
$(\operatorname{cl} (\sup G))(0) = (\sup G)(0)$, with the concave closure. -/
theorem concaveNormal_iff : ConcaveNormal G ↔ concaveCl (supBifun G) 0 = supBifun G 0 := Iff.rfl

/-- The concave program $G$ is normal if and only if the convex program $(y, v) \mapsto -(Gy)(v)$ is
normal.

So each concave sufficient condition for normality is the matching convex condition for $-F^*$,
with the pairings flipped. -/
theorem concaveNormal_iff_normal_neg : ConcaveNormal G ↔ Normal fun y v => -(G y v) := by
  have hval : ∀ y, infBifun (fun y' v => -(G y' v)) y = -(supBifun G y) :=
    fun y => (congrFun (neg_supBifun G) y).symm
  have hcl : convexCl (infBifun fun y' v => -(G y' v)) 0 = -(concaveCl (supBifun G) 0) := by
    rw [concaveCl_apply, neg_neg, neg_supBifun]
  rw [concaveNormal_iff, normal_iff, hcl, hval 0, neg_inj]

end ConcaveNormality

/-! ### The two optimal values -/

section OptimalValues

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsCompatiblePairing Bu] {F : Bifun U X}

/-- **The optimal value of the dual program.** Let $U$ be a real locally convex space paired with
$V$ by $B_u$ such that every continuous linear functional on $U$ has the form
$\langle \cdot, v \rangle$, let $X$ be paired with $Y$ by $B_x$, and let $F$ be a convex
bifunction from $U$ to $X$. Then
$$(\operatorname{cl} (\inf F))(0) = \sup_v (F^* 0)(v).$$

Closedness of $F$ is not needed: the formula is the Fenchel–Moreau theorem for $\inf F$, and
$F^*$ does not distinguish $F$ from its closure. -/
theorem convexCl_infBifun_zero_eq_iSup_convexAdjointBifun (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (hF : ConvexBifun F) :
    convexCl (infBifun F) 0 = ⨆ v : V, convexAdjointBifun Bu Bx F 0 v := by
  rw [convexCl_zero_eq_iSup_iInf (B := Bu) (convexFn_infBifun hF)]
  exact iSup_congr fun v => (convexAdjointBifun_zero_apply Bu Bx F v).symm

/-- Under the hypotheses of `ConvexAnalysis.convexCl_infBifun_zero_eq_iSup_convexAdjointBifun`, the
program $(P)$ is normal if and only if there is no duality gap:
$$\sup_v (F^* 0)(v) = (\inf F)(0).$$
This is part of Theorem 30.3 of [rockafellar1970convex]. -/
theorem normal_iff_iSup_convexAdjointBifun_eq (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (hF : ConvexBifun F) :
    Normal F ↔ (⨆ v : V, convexAdjointBifun Bu Bx F 0 v) = infBifun F 0 := by
  rw [normal_iff, convexCl_infBifun_zero_eq_iSup_convexAdjointBifun (Bu := Bu) Bx hF]

end OptimalValues

section ConcaveOptimalValues

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace Y] [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y] [LocallyConvexSpace ℝ Y]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ} [IsCompatiblePairing Bx.flip]
  {G : Bifun Y V}

/-- Let $Y$ be a real locally convex space paired with $X$ such that every continuous linear
functional on $Y$ has the form $\langle x, \cdot \rangle$, and let $G$ be a concave bifunction
from $Y$ to $V$. Then the concave closure of $\sup G$ at the origin is the optimal value of the
program associated with the adjoint $G^*$ of $G$:
$$(\operatorname{cl} (\sup G))(0) = (\inf G^*)(0).$$
This is the dual of `ConvexAnalysis.convexCl_infBifun_zero_eq_iSup_convexAdjointBifun`. -/
theorem concaveCl_supBifun_zero_eq_infBifun_concaveAdjointBifun (hG : ConcaveBifun G) :
    concaveCl (supBifun G) 0 = infBifun (concaveAdjointBifun Bu Bx G) 0 := by
  have hsurj : Function.Surjective (fun x : X => -x) := fun x => ⟨-x, neg_neg x⟩
  have hneg : ConvexBifun fun y v => -(G y v) := concaveFn_iff_convexFn_neg.1 hG
  have hpt : ∀ x : X, -(convexAdjointBifun Bx.flip Bu.flip (fun y v => -(G y v)) 0 x)
      = concaveAdjointBifun Bu Bx G 0 (-x) := by
    intro x
    rw [convexAdjointBifun_apply, EReal.neg_iInf, concaveAdjointBifun_apply]
    refine iSup_congr fun q => ?_
    have h1 : (Bx.flip q.1 x - Bu.flip q.2 (0 : U) : ℝ) = Bx x q.1 := by
      rw [LinearMap.flip_apply, LinearMap.flip_apply, map_zero, LinearMap.zero_apply, sub_zero]
    have h2 : (Bx (-x) q.1 - Bu (0 : U) q.2 : ℝ) = -(Bx x q.1) := by
      rw [map_zero, LinearMap.zero_apply, sub_zero, map_neg, LinearMap.neg_apply]
    rw [h1, h2, EReal.neg_add (.inr (EReal.coe_ne_top _)) (.inr (EReal.coe_ne_bot _)), neg_neg,
      sub_eq_add_neg, ← EReal.coe_neg]
  rw [concaveCl_apply, neg_supBifun,
    convexCl_infBifun_zero_eq_iSup_convexAdjointBifun (Bu := Bx.flip) Bu.flip hneg, EReal.neg_iSup,
    iInf_congr hpt]
  exact hsurj.iInf_comp fun x : X => concaveAdjointBifun Bu Bx G 0 x

end ConcaveOptimalValues

/-! ### Normality of $(P)$, of $(P^*)$, and the absence of a duality gap -/

section DualityGap

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X]
  [TopologicalSpace Y] [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y] [LocallyConvexSpace ℝ Y]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsCompatiblePairing Bu] {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ}
  [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip] {F : Bifun U X}

/-- **The optimal value of the primal program.** Let $U$, $X$ and $Y$ be real locally convex spaces,
paired with $V$ and with each other such that $B_u$, $B_x$ and the flip of $B_x$ represent all
continuous linear functionals. Let $F$ be a closed convex bifunction from $U$ to $X$. Then
$$(\operatorname{cl} (\sup F^*))(0) = (\inf F)(0),$$
with the concave closure on the left.

Closedness is what turns $F^{**}$ back into $F$. -/
theorem concaveCl_supBifun_convexAdjointBifun_zero_eq (hF : ConvexBifun F)
    (hcl : ClosedConvexBifun F) :
    concaveCl (supBifun (convexAdjointBifun Bu Bx F)) 0 = infBifun F 0 := by
  rw [concaveCl_supBifun_zero_eq_infBifun_concaveAdjointBifun (Bu := Bu) (Bx := Bx)
      (concaveBifun_convexAdjointBifun Bu Bx F),
    concaveAdjointBifun_convexAdjointBifun_eq_convexClBifun hF, hcl.convexClBifun_eq]

/-- Under the hypotheses of `ConvexAnalysis.concaveCl_supBifun_convexAdjointBifun_zero_eq`, the dual
program $(P^*)$ is normal if and only if there is no duality gap:
$$\sup_v (F^* 0)(v) = (\inf F)(0).$$
This is part of Theorem 30.3 of [rockafellar1970convex]. -/
theorem concaveNormal_convexAdjointBifun_iff (hF : ConvexBifun F) (hcl : ClosedConvexBifun F) :
    ConcaveNormal (convexAdjointBifun Bu Bx F)
      ↔ (⨆ v : V, convexAdjointBifun Bu Bx F 0 v) = infBifun F 0 := by
  rw [concaveNormal_iff, concaveCl_supBifun_convexAdjointBifun_zero_eq hF hcl]
  exact eq_comm

/-- Under the hypotheses of `ConvexAnalysis.concaveCl_supBifun_convexAdjointBifun_zero_eq`, the
closed convex program $(P)$ is normal if and only if its dual program $(P^*)$ is normal. This is
part of Theorem 30.3 of [rockafellar1970convex]. -/
theorem normal_iff_concaveNormal_convexAdjointBifun (hF : ConvexBifun F)
    (hcl : ClosedConvexBifun F) :
    Normal F ↔ ConcaveNormal (convexAdjointBifun Bu Bx F) :=
  (normal_iff_iSup_convexAdjointBifun_eq (Bu := Bu) Bx hF).trans
    (concaveNormal_convexAdjointBifun_iff hF hcl).symm

end DualityGap

/-! ### Sufficient conditions for normality -/

section KuhnTucker

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsCompatiblePairing Bu] {F : Bifun U X} {v : V}

/-- Let $U$ be a real locally convex space paired with $V$ such that every continuous linear
functional on $U$ has the form $\langle \cdot, v \rangle$, and let $F$ be a convex bifunction
from $U$ to $X$. If $(P)$ has a Kuhn–Tucker vector, then $(P)$ is normal. This is one of the
sufficient conditions of Theorem 30.4 of [rockafellar1970convex].

At a Kuhn–Tucker vector the dual objective reaches $(\inf F)(0)$, and by weak duality it never
exceeds this value. The finiteness of the optimal value is part of the definition
`ConvexAnalysis.KuhnTucker`. -/
theorem normal_of_kuhnTucker_nonempty (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (hF : ConvexBifun F)
    (h : (KuhnTucker Bu F).Nonempty) : Normal F := by
  obtain ⟨w, hw⟩ := h
  rw [mem_kuhnTucker_iff_convexAdjointBifun_zero_eq (Bx := Bx)] at hw
  rw [normal_iff_iSup_convexAdjointBifun_eq (Bu := Bu) Bx hF]
  refine le_antisymm (iSup_convexAdjointBifun_zero_le Bu Bx F) ?_
  rw [← hw.2.2]
  exact le_iSup (fun z : V => convexAdjointBifun Bu Bx F 0 z) w

/-- Let $U$ be a real locally convex space paired with $V$ such that every continuous linear
functional on $U$ has the form $\langle \cdot, v \rangle$, and let $F$ be a convex bifunction
from $U$ to $X$. Let $(P)$ be normal with finite optimal value $(\inf F)(0)$. Then $v$ is a
Kuhn–Tucker vector of $(P)$ if and only if $v$ is an optimal solution of $(P^*)$:
$$(F^* 0)(v) = \sup_w (F^* 0)(w).$$
This is Theorem 30.5 of [rockafellar1970convex]. -/
theorem mem_kuhnTucker_iff_convexAdjointBifun_zero_eq_iSup (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (hF : ConvexBifun F)
    (hn : Normal F) (ht : infBifun F 0 ≠ ⊤) (hb : infBifun F 0 ≠ ⊥) :
    v ∈ KuhnTucker Bu F
      ↔ convexAdjointBifun Bu Bx F 0 v = ⨆ w : V, convexAdjointBifun Bu Bx F 0 w := by
  rw [mem_kuhnTucker_iff_convexAdjointBifun_zero_eq (Bx := Bx),
    (normal_iff_iSup_convexAdjointBifun_eq (Bu := Bu) Bx hF).1 hn]
  exact ⟨fun h => h.2.2, fun h => ⟨ht, hb, h⟩⟩

/-- Under the hypotheses of `ConvexAnalysis.mem_kuhnTucker_iff_convexAdjointBifun_zero_eq_iSup`, the
set of Kuhn–Tucker vectors of $(P)$ is the set of optimal solutions of $(P^*)$:
$$\{v \mid v \text{ a Kuhn–Tucker vector}\} = \{v \mid (F^* 0)(v) = \sup_w (F^* 0)(w)\}.$$
-/
theorem kuhnTucker_eq_setOf_isMax (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (hF : ConvexBifun F) (hn : Normal F)
    (ht : infBifun F 0 ≠ ⊤) (hb : infBifun F 0 ≠ ⊥) :
    KuhnTucker Bu F
      = {v : V | convexAdjointBifun Bu Bx F 0 v = ⨆ w : V, convexAdjointBifun Bu Bx F 0 w} :=
  Set.ext fun _ => mem_kuhnTucker_iff_convexAdjointBifun_zero_eq_iSup Bx hF hn ht hb

omit [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U]
  [LocallyConvexSpace ℝ U] [IsCompatiblePairing Bu] in
/-- If $v$ is a Kuhn–Tucker vector of $(P)$, then $v$ is an optimal solution of $(P^*)$ and the
common optimal value is $(\inf F)(0)$: this value is the greatest element of the range of
$F^* 0$.

This half needs no normality hypothesis, since the existence of $v$ implies normality. -/
theorem isGreatest_convexAdjointBifun_zero_of_mem_kuhnTucker (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (hv : v ∈ KuhnTucker Bu F) :
    IsGreatest (Set.range (convexAdjointBifun Bu Bx F 0)) (infBifun F 0) := by
  rw [mem_kuhnTucker_iff_convexAdjointBifun_zero_eq (Bx := Bx)] at hv
  exact ⟨⟨v, hv.2.2⟩, by rintro _ ⟨w, rfl⟩; exact convexAdjointBifun_zero_le Bu Bx F w⟩

end KuhnTucker

section StrongConsistency

variable {U X : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [AddCommGroup X] [Module ℝ X] {F : Bifun U X}

/-- Let $U$ be a finite-dimensional real normed space and let $F$ be a convex bifunction from $U$ to
$X$. If $(P)$ is strongly consistent, then $(P)$ is normal. This is one of the sufficient
conditions of Theorem 30.4 of [rockafellar1970convex].

A convex function agrees with its closure on the relative interior of its effective domain, and
here this relative interior contains the origin. -/
theorem StronglyConsistent.normal (hs : StronglyConsistent F) (hF : ConvexBifun F) : Normal F := by
  have hri : (0 : U) ∈ ri (convexDom (infBifun F)) := by rwa [convexDom_infBifun]
  exact (convexFn_infBifun hF).convexCl_eq_of_mem_relint_convexDom hri

/-- Let $U$ be a finite-dimensional real normed space and let $F$ be a convex bifunction from $U$ to
$X$. If $(P)$ is strictly consistent, then $(P)$ is normal. -/
theorem StrictlyConsistent.normal (hs : StrictlyConsistent F) (hF : ConvexBifun F) : Normal F :=
  hs.stronglyConsistent.normal hF

end StrongConsistency

/-! ### Strong consistency of the dual program -/

section

variable {V Y : Type*} [AddCommGroup V] [Module ℝ V] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [FiniteDimensional ℝ Y] {G : Bifun Y V}

/-- Let $Y$ be a finite-dimensional real normed space and let $G$ be a concave bifunction from $Y$
to $V$. If the concave program associated with $G$ is strongly consistent, then it is normal.
This is the concave counterpart of `ConvexAnalysis.StronglyConsistent.normal`. -/
theorem ConcaveStronglyConsistent.concaveNormal (hs : ConcaveStronglyConsistent G)
    (hG : ConcaveBifun G) : ConcaveNormal G := by
  have hri : (0 : Y) ∈ ri (convexDom fun z => -(supBifun G z)) := by
    rw [← concaveDom_eq_convexDom_neg, concaveDom_supBifun]
    exact hs
  rw [ConcaveNormal, concaveCl_apply,
    (concaveFn_supBifun hG).convexFn_neg.convexCl_eq_of_mem_relint_convexDom hri, neg_neg]

end

section DualStrongConsistency

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsCompatiblePairing Bu] {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ}
  [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip] {F : Bifun U X}

/-- Let $U$ and $X$ be real locally convex spaces and $Y$ a finite-dimensional real normed space,
with pairings that represent all continuous linear functionals, and let $F$ be a closed convex
bifunction from $U$ to $X$. If the dual program $(P^*)$ is strongly consistent, then $(P)$ is
normal. This is one of the sufficient conditions of Theorem 30.4 of [rockafellar1970convex]. -/
theorem normal_of_concaveStronglyConsistent_convexAdjointBifun (hF : ConvexBifun F)
    (hcl : ClosedConvexBifun F)
        (hs : ConcaveStronglyConsistent (convexAdjointBifun Bu Bx F)) : Normal F :=
  (normal_iff_concaveNormal_convexAdjointBifun hF hcl).2
    (hs.concaveNormal (concaveBifun_convexAdjointBifun Bu Bx F))

end DualStrongConsistency

/-! ### Bounded level sets and bounded sets of optimal solutions -/

section Shift

variable {U V X Y : Type*} [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ} {F : Bifun U X} {y : Y}

/-- The bifunction $F$ with a linear function of $x$ subtracted:
$(u, x) \mapsto (Fu)(x) - \langle x, y \rangle$.

Its optimal value at $u$ is $-(Fu)^*(y)$. So the formula for the dual optimal value, applied to
it, computes the whole slice $\sup_v (F^* y)(v)$ of the adjoint. -/
noncomputable def shiftBifun (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (F : Bifun U X) (y : Y) : Bifun U X :=
  fun u x => F u x - ((Bx x y : ℝ) : EReal)

/-- The shifted bifunction has the value $(Fu)(x) - \langle x, y \rangle$. -/
@[simp] theorem shiftBifun_apply (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (F : Bifun U X) (y : Y) (u : U)
    (x : X) : shiftBifun Bx F y u x = F u x - ((Bx x y : ℝ) : EReal) := rfl

/-- The optimal value of the shifted program at $u$ is minus the conjugate of $Fu$ at $y$:
$$\inf_x \{(Fu)(x) - \langle x, y \rangle\} = -(Fu)^*(y).$$
-/
theorem infBifun_shiftBifun (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (F : Bifun U X) (y : Y) (u : U) :
    infBifun (shiftBifun Bx F y) u = -(convexConj Bx (F u) y) := by
  rw [infBifun_apply, convexConj_apply, EReal.neg_iSup]
  refine iInf_congr fun x => ?_
  rw [shiftBifun_apply, EReal.neg_sub (Or.inl (EReal.coe_ne_bot ((Bx x) y)))
    (Or.inl (EReal.coe_ne_top ((Bx x) y))), sub_eq_add_neg]
  exact add_comm _ _

end Shift

section ShiftConvex

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ} {F : Bifun U X} {y : Y}

/-- If $F$ is a convex bifunction, then so is $(u, x) \mapsto (Fu)(x) - \langle x, y \rangle$. -/
theorem convexBifun_shiftBifun (hF : ConvexBifun F) (y : Y) :
    ConvexBifun (shiftBifun Bx F y) := by
  have hl : ∀ (p q : U × X) (a b : ℝ), a + b = 1 →
      (fun r : U × X => -(Bx r.2 y)) (a • p + b • q)
        = a * (fun r : U × X => -(Bx r.2 y)) p + b * (fun r : U × X => -(Bx r.2 y)) q := by
    intro p q a b _
    simp only [Prod.snd_add, Prod.smul_snd, map_add, map_smul, smul_eq_mul,
      LinearMap.add_apply, LinearMap.smul_apply]
    ring
  have h := convexFn_add_coe (f := graphFn F) (l := fun r : U × X => -(Bx r.2 y)) hF hl
  have heq : (fun p : U × X => graphFn F p + ((-(Bx p.2 y) : ℝ) : EReal))
      = graphFn (shiftBifun Bx F y) := by
    funext p
    simp only [graphFn, shiftBifun, EReal.coe_neg, sub_eq_add_neg]
  refine convexBifun_iff.2 ?_
  rw [← heq]
  exact h

/-- The adjoint of the shifted bifunction $(u, x) \mapsto (Fu)(x) - \langle x, y \rangle$ at the
origin is the adjoint of $F$ at $y$: its value at $v$ is $(F^* y)(v)$. -/
theorem convexAdjointBifun_shiftBifun_zero (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (F : Bifun U X) (y : Y) (v : V) :
    convexAdjointBifun Bu Bx (shiftBifun Bx F y) 0 v = convexAdjointBifun Bu Bx F y v := by
  have key : ∀ (z : EReal) (b c : ℝ),
      (z - (c : EReal)) + (b : EReal) = z + ((b - c : ℝ) : EReal) := by
    intro z b c
    rw [EReal.coe_sub, sub_eq_add_neg z, sub_eq_add_neg ((b : ℝ) : EReal), add_assoc,
      add_comm (-(((c : ℝ) : EReal))) (((b : ℝ) : EReal))]
  simp only [convexAdjointBifun_apply, shiftBifun_apply, map_zero, sub_zero, key]

end ShiftConvex

section BoundedLevelSets

variable {U V X Y : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [AddCommGroup V] [Module ℝ V]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsCompatiblePairing Bu] {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ}
  [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip] {F : Bifun U X} {y : Y}

omit [FiniteDimensional ℝ U] [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y]
  [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip] in
/-- **The dual objective at an arbitrary $y$.** Let $U$ be a real normed space paired with $V$ such
that every continuous linear functional on $U$ has the form $\langle \cdot, v \rangle$, and let
$F$ be a convex bifunction from $U$ to $X$. Then for every $y$, the supremum $\sup_v (F^* y)(v)$
is the closure at the origin of the optimal value of the shifted program
$(u, x) \mapsto (Fu)(x) - \langle x, y \rangle$. -/
theorem supBifun_convexAdjointBifun (hF : ConvexBifun F) (y : Y) :
    supBifun (convexAdjointBifun Bu Bx F) y = convexCl (infBifun (shiftBifun Bx F y)) 0 := by
  rw [supBifun_apply,
    convexCl_infBifun_zero_eq_iSup_convexAdjointBifun (Bu := Bu) Bx (convexBifun_shiftBifun hF y)]
  exact (iSup_congr fun v => convexAdjointBifun_shiftBifun_zero Bu Bx F y v).symm

omit [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y] [IsCompatiblePairing Bx]
  [IsCompatiblePairing Bx.flip] in
/-- Let $U$ be a finite-dimensional real normed space paired with $V$ such that every continuous
linear functional on $U$ has the form $\langle \cdot, v \rangle$. Let $F$ be a consistent convex
bifunction from $U$ to $X$, and let $y \in Y$ be such that $(Fu)^*(y) \neq +\infty$ for every
$u$, that is, $(Fu)(x) - \langle x, y \rangle$ is bounded below in $x$ for every perturbation
$u$. Then $y$ is in the effective domain of the concave bifunction $F^*$:
$(F^* y)(v) \neq -\infty$ for some $v$.

The condition $\sup_v (F^* y)(v) \neq -\infty$ is $(\operatorname{cl} (\inf (F - \langle \cdot,
y \rangle)))(0) \neq -\infty$. This is stronger than $(\inf (F - \langle \cdot, y \rangle))(0)
\neq -\infty$, which is what $y \in \operatorname{dom} (F0)^*$ says. The gap is bridged by the
fact that a proper convex function has a proper closure. This is the only result of this group
that needs $U$ finite-dimensional. -/
theorem mem_concaveDomBifun_convexAdjointBifun (hF : ConvexBifun F) (hc : Consistent F)
    (h : ∀ u : U, convexConj Bx (F u) y ≠ ⊤) :
    y ∈ concaveDomBifun (convexAdjointBifun Bu Bx F) := by
  obtain ⟨x₀, hx₀⟩ := hc
  have hprop : ProperConvex (infBifun (shiftBifun Bx F y)) := by
    refine ⟨⟨0, mem_convexDom.2 ?_⟩, fun u => ?_⟩
    · have hle : infBifun (shiftBifun Bx F y) 0 ≤ shiftBifun Bx F y 0 x₀ := iInf_le _ x₀
      refine lt_of_le_of_lt hle ?_
      rw [shiftBifun_apply, sub_eq_add_neg]
      exact EReal.add_lt_top hx₀
        (by rw [Ne, EReal.neg_eq_top_iff]; exact EReal.coe_ne_bot _)
    · rw [infBifun_shiftBifun, Ne, EReal.neg_eq_bot_iff]
      exact h u
  have hcl :=
      (convexFn_infBifun (convexBifun_shiftBifun (Bx := Bx) hF y)).properConvex_convexCl hprop
  have hne : supBifun (convexAdjointBifun Bu Bx F) y ≠ ⊥ := by
    rw [supBifun_convexAdjointBifun hF y]
    exact hcl.ne_bot 0
  rw [mem_concaveDomBifun]
  by_contra hcon
  push Not at hcon
  exact hne (by rw [supBifun_apply, iSup_eq_bot.2 hcon])

include Bu Bx in
/-- Let $U$, $X$ and $Y$ be finite-dimensional real normed spaces, with pairings that represent all
continuous linear functionals, and let $F$ be a closed convex bifunction from $U$ to $X$. If
some level set $\{x \mid (F0)(x) \le \alpha\}$ with $\alpha$ real is nonempty and bounded, then
$(P)$ is normal, and so is $(P^*)$ by
`ConvexAnalysis.normal_iff_concaveNormal_convexAdjointBifun`. This is one of the sufficient
conditions of Theorem 30.4 of [rockafellar1970convex].

A bounded level set gives $0 \in \operatorname{int}(\operatorname{dom} (F0)^*)$. But strict
consistency of $(P^*)$ is $0 \in \operatorname{int}$ of the effective domain of $F^*$, which is
an intersection over all perturbations $u$ of the sets $\operatorname{dom} (Fu)^*$, and an
intersection of open sets need not be open. It is open here because all slices of a closed
convex bifunction have the same recession function, so every
$\operatorname{int}(\operatorname{dom} (Fu)^*)$ is described by the same inequality and these
sets are all equal. No properness is assumed: an improper closed convex bifunction has
$(\inf F)(0) = -\infty$, and then normality is trivial. -/
theorem normal_of_exists_setOf_le (hF : ConvexBifun F) (hcl : ClosedConvexBifun F)
    (h : ∃ α : ℝ, {x : X | F 0 x ≤ (α : EReal)}.Nonempty ∧
      Bornology.IsBounded {x : X | F 0 x ≤ (α : EReal)}) :
    Normal F := by
  obtain ⟨α, ⟨x₀, hx₀⟩, hbd⟩ := h
  have hx₀top : F 0 x₀ ≠ ⊤ := (lt_of_le_of_lt hx₀ (EReal.coe_lt_top α)).ne
  have hcons : Consistent F := ⟨x₀, hx₀top⟩
  have hlsc : LowerSemicontinuous (graphFn F) := ClosedConvex.lowerSemicontinuous hcl
  have hcont : ∀ u : U, Continuous fun x : X => (u, x) := fun u =>
    continuous_const.prodMk continuous_id
  by_cases hbot : ∃ p : U × X, graphFn F p = ⊥
  · have hb : F 0 x₀ = ⊥ :=
      (ConvexFn.eq_bot_or_eq_top hF hlsc hbot (0, x₀)).resolve_right hx₀top
    have hval : infBifun F 0 = ⊥ := by
      refine le_bot_iff.1 ?_
      rw [infBifun_apply, ← hb]
      exact iInf_le _ x₀
    have hle : convexCl (infBifun F) 0 ≤ ⊥ := by rw [← hval]; exact convexCl_le _ 0
    rw [normal_iff, le_bot_iff.1 hle, hval]
  push Not at hbot
  have hslice : ∀ u : U, u ∈ convexDomBifun F → ClosedProperConvexFn (F u) := by
    intro u hu
    obtain ⟨x₁, hx₁⟩ := hu
    refine ⟨hF.convexFn_apply u, ?_, ⟨⟨x₁, mem_convexDom.2 (lt_top_iff_ne_top.2 hx₁)⟩,
      fun x => hbot (u, x)⟩⟩
    refine (closedConvex_iff_lowerSemicontinuous fun x => hbot (u, x)).2 fun x r hr => ?_
    exact ((hcont u).tendsto x).eventually (hlsc (u, x) r hr)
  have hepi : IsClosed (epi (graphFn F)) := lowerSemicontinuous_iff_isClosed_epi.1 hlsc
  have h0int : (0 : Y) ∈ interior (convexDom (convexConj Bx (F 0))) := by
    have h0 := hslice 0 hcons
    exact (exists_setOf_le_nonempty_and_isBounded_iff_zero_mem_interior_convexDom_convexConj
        (B := Bx)
      h0.convex h0.closed h0.proper).1 ⟨α, ⟨x₀, hx₀⟩, hbd⟩
  have hsub : interior (convexDom (convexConj Bx (F 0)))
      ⊆ concaveDomBifun (convexAdjointBifun Bu Bx F) := by
    intro z hz
    refine mem_concaveDomBifun_convexAdjointBifun hF hcons fun u => ?_
    by_cases hu : u ∈ convexDomBifun F
    · have hrec : recessionFn (F 0) = recessionFn (F u) :=
        recessionFn_slice_eq hF hepi hcons hu
      have hzu : z ∈ interior (convexDom (convexConj Bx (F u))) := by
        rw [mem_interior_convexDom_convexConj_iff (hslice u hu) z, ← hrec]
        exact (mem_interior_convexDom_convexConj_iff (hslice 0 hcons) z).1 hz
      exact (mem_convexDom.1 (interior_subset hzu)).ne
    · have htop : ∀ x : X, F u x = ⊤ := fun x => by
        by_contra hcon
        exact hu ⟨x, hcon⟩
      have hinf : infBifun (shiftBifun Bx F z) u = ⊤ := by
        rw [infBifun_apply]
        refine le_antisymm le_top (le_iInf fun x => ?_)
        rw [shiftBifun_apply, htop x, EReal.top_sub_coe]
      rw [infBifun_shiftBifun] at hinf
      rw [EReal.neg_eq_top_iff.1 hinf]
      exact bot_ne_top
  exact normal_of_concaveStronglyConsistent_convexAdjointBifun hF hcl
    (interior_subset_intrinsicInterior (interior_maximal hsub isOpen_interior h0int))

include Bu Bx in
/-- Under the hypotheses of `ConvexAnalysis.normal_of_exists_setOf_le`, but with $F0$ proper,
suppose that the set of optimal solutions of $(P)$ is nonempty and bounded, in particular if it
is a single point. Then $(P)$ is normal. This is one of the sufficient conditions of Theorem
30.4 of [rockafellar1970convex].

With $F0$ proper, this is the level-set criterion, since the set of optimal solutions is then
the level set at the minimum value. Properness cannot be removed: for $F0 \equiv +\infty$ on a
zero-dimensional $X$, the set of optimal solutions is nonempty and bounded, but no level set is
nonempty. -/
theorem normal_of_argmin_nonempty_and_isBounded (hF : ConvexBifun F) (hcl : ClosedConvexBifun F)
    (hp : ProperConvex (F 0)) (hne : (argmin (F 0)).Nonempty)
    (hbd : Bornology.IsBounded (argmin (F 0))) :
    Normal F := by
  have hc : ClosedConvex (F 0) := by
    refine (closedConvex_iff_lowerSemicontinuous hp.ne_bot).2 fun x r hr => ?_
    exact ((continuous_const.prodMk continuous_id).tendsto x).eventually
      (ClosedConvex.lowerSemicontinuous hcl (0, x) r hr)
  exact normal_of_exists_setOf_le (Bu := Bu) (Bx := Bx) hF hcl
    ((argmin_nonempty_and_isBounded_iff_exists_setOf_le (B := Bx) (hF.convexFn_apply 0) hc hp).1
      ⟨hne, hbd⟩)

end BoundedLevelSets

/-! ### Bounded level sets of the dual objective -/

section DualBoundedLevelSets

variable {U V X Y : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsCompatiblePairing Bu] [IsCompatiblePairing Bu.flip]
  {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ} [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip]
  {F : Bifun U X}

/-- Let $U$, $V$ and $Y$ be finite-dimensional real normed spaces and $X$ a real normed space, with
pairings that represent all continuous linear functionals in both directions, and let $F$ be a
closed convex bifunction from $U$ to $X$. If some superlevel set
$\{v \mid (F^* 0)(v) \ge \alpha\}$ of the dual objective with $\alpha$ real is nonempty and
bounded, then $(P)$ is normal, and so is $(P^*)$ by
`ConvexAnalysis.normal_iff_concaveNormal_convexAdjointBifun`. This is one of the sufficient
conditions of Theorem 30.4 of [rockafellar1970convex].

This is the level-set criterion for the convex program associated with $-F^*$, which is convex
and closed with no hypothesis on $F$. Its objective is $-(F^* 0)$, and its sublevel set at
$-\alpha$ is the superlevel set of $F^* 0$ at $\alpha$. Normality of that program is normality
of the concave program $F^*$, hence normality of $(P)$. This route needs no concave counterpart
of the level-set and recession results on $V$. -/
theorem normal_of_exists_setOf_ge_convexAdjointBifun (hF : ConvexBifun F)
    (hcl : ClosedConvexBifun F)
    (h : ∃ α : ℝ, {v : V | (α : EReal) ≤ convexAdjointBifun Bu Bx F 0 v}.Nonempty ∧
      Bornology.IsBounded {v : V | (α : EReal) ≤ convexAdjointBifun Bu Bx F 0 v}) :
    Normal F := by
  have hpair : IsContinuousPairing (prodPairing Bu Bx).flip :=
    isContinuousPairing_prodPairing_flip Bu Bx
  obtain ⟨α, hne, hbd⟩ := h
  have hset : {v : V | -(convexAdjointBifun Bu Bx F 0 v) ≤ ((-α : ℝ) : EReal)}
      = {v : V | (α : EReal) ≤ convexAdjointBifun Bu Bx F 0 v} := by
    ext v
    have hiff : (-(convexAdjointBifun Bu Bx F 0 v) ≤ ((-α : ℝ) : EReal))
        ↔ ((α : EReal) ≤ convexAdjointBifun Bu Bx F 0 v) := by
      rw [EReal.neg_le, EReal.coe_neg, neg_neg]
    exact hiff
  have hne' : {v : V | -(convexAdjointBifun Bu Bx F 0 v) ≤ ((-α : ℝ) : EReal)}.Nonempty := by
    rw [hset]; exact hne
  have hbd' : Bornology.IsBounded
      {v : V | -(convexAdjointBifun Bu Bx F 0 v) ≤ ((-α : ℝ) : EReal)} := by
    rw [hset]; exact hbd
  have hnormal : Normal fun y v => -(convexAdjointBifun Bu Bx F y v) :=
    normal_of_exists_setOf_le (Bu := Bx.flip) (Bx := Bu.flip)
      (convexBifun_neg_convexAdjointBifun Bu Bx F)
          closedConvexBifun_neg_convexAdjointBifun ⟨-α, hne', hbd'⟩
  exact (normal_iff_concaveNormal_convexAdjointBifun hF hcl).2
      (concaveNormal_iff_normal_neg.2 hnormal)

/-- Under the hypotheses of `ConvexAnalysis.normal_of_exists_setOf_ge_convexAdjointBifun`, but with
$-(F^* 0)$ proper, suppose that the set of optimal solutions of $(P^*)$ is nonempty and bounded,
in particular if it is a single point. Then $(P)$ is normal. This is one of the sufficient
conditions of Theorem 30.4 of [rockafellar1970convex].

This is `ConvexAnalysis.normal_of_argmin_nonempty_and_isBounded` for the convex program
associated with $-F^*$. Properness of the objective cannot be removed there either. -/
theorem normal_of_argmax_convexAdjointBifun_nonempty_and_isBounded (hF : ConvexBifun F)
    (hcl : ClosedConvexBifun F) (hp : ProperConvex fun v => -(convexAdjointBifun Bu Bx F 0 v))
    (hne : (argmax (convexAdjointBifun Bu Bx F 0)).Nonempty)
    (hbd : Bornology.IsBounded (argmax (convexAdjointBifun Bu Bx F 0))) :
    Normal F := by
  have hpair : IsContinuousPairing (prodPairing Bu Bx).flip :=
    isContinuousPairing_prodPairing_flip Bu Bx
  have harg : argmin (fun v : V => -(convexAdjointBifun Bu Bx F 0 v))
      = argmax (convexAdjointBifun Bu Bx F 0) := (argmax_eq_argmin_neg _).symm
  have hne' : (argmin fun v : V => -(convexAdjointBifun Bu Bx F 0 v)).Nonempty := by
    rw [harg]; exact hne
  have hbd' : Bornology.IsBounded (argmin fun v : V => -(convexAdjointBifun Bu Bx F 0 v)) := by
    rw [harg]; exact hbd
  have hnormal : Normal fun y v => -(convexAdjointBifun Bu Bx F y v) :=
    normal_of_argmin_nonempty_and_isBounded (Bu := Bx.flip) (Bx := Bu.flip)
      (convexBifun_neg_convexAdjointBifun Bu Bx F) closedConvexBifun_neg_convexAdjointBifun hp
          hne' hbd'
  exact (normal_iff_concaveNormal_convexAdjointBifun hF hcl).2
      (concaveNormal_iff_normal_neg.2 hnormal)

end DualBoundedLevelSets

/-! ### Consistency of the two programs -/

section ConjTop

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [AddCommGroup G] [Module ℝ G] {B : E →ₗ[ℝ] G →ₗ[ℝ] ℝ} [IsCompatiblePairing B]
  {f : E → EReal}

/-- **A dichotomy for conjugates.** Let $E$ be a finite-dimensional real normed space paired with
$G$ such that every continuous linear functional on $E$ has the form $\langle \cdot, y \rangle$,
and let $f$ be a convex function on $E$. Then $f^*$ is identically $+\infty$ if and only if
$f(x) = -\infty$ for some $x$.

One direction needs no hypothesis. For the other, a proper convex function has a proper closure,
whose conjugate is proper, and $(\operatorname{cl} f)^* = f^*$. -/
theorem forall_convexConj_eq_top_iff (hf : ConvexFn f) :
    (∀ y : G, convexConj B f y = ⊤) ↔ ∃ x : E, f x = ⊥ := by
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    by_cases hd : ∃ x : E, f x ≠ ⊤
    · obtain ⟨x₀, hx₀⟩ := hd
      have hp : ProperConvex f := ⟨⟨x₀, mem_convexDom.2 (lt_of_le_of_ne le_top hx₀)⟩, hcon⟩
      have hpc : ProperConvex (convexConj B (convexCl f)) :=
        properConvex_convexConj ⟨convexFn_convexCl hf, closedConvex_convexCl f,
            hf.properConvex_convexCl hp⟩
      rw [convexConj_convexCl] at hpc
      obtain ⟨y, hy⟩ := hpc.convexDom_nonempty
      exact absurd (h y) (mem_convexDom.1 hy).ne
    · push Not at hd
      have hbot : convexConj B f 0 = ⊥ := convexConj_eq_bot_iff.2 hd
      rw [h 0] at hbot
      exact absurd hbot (by simp)
  · rintro ⟨x, hx⟩ y
    refine top_le_iff.1 ?_
    rw [convexConj_apply]
    refine le_trans (le_of_eq ?_) (le_iSup (fun z : E => ((B z y : ℝ) : EReal) - f z) x)
    rw [hx]
    simp

end ConjTop

section DualConsistency

variable {U V X Y : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [AddCommGroup V] [Module ℝ V] [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsCompatiblePairing Bu] {F : Bifun U X}

omit [FiniteDimensional ℝ U] [IsCompatiblePairing Bu] in
/-- The dual objective, negated, is the conjugate of the perturbation function at the reflected
point:
$$-(F^* 0)(v) = (\inf F)^*(-v).$$
-/
theorem neg_convexAdjointBifun_zero_apply (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (v : V) :
    -(convexAdjointBifun Bu Bx F 0 v) = convexConj Bu (infBifun F) (-v) := by
  rw [convexAdjointBifun_zero_apply, EReal.neg_iInf, convexConj_apply]
  refine iSup_congr fun u => ?_
  rw [EReal.neg_add (.inl (EReal.coe_ne_bot _)) (.inl (EReal.coe_ne_top _)), ← EReal.coe_neg,
    map_neg]

omit [FiniteDimensional ℝ U] [IsCompatiblePairing Bu] in
/-- The dual objective is $-\infty$ at $v$ if and only if the conjugate of the perturbation function
is $+\infty$ at $-v$. -/
theorem convexAdjointBifun_zero_eq_bot_iff (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (v : V) :
    convexAdjointBifun Bu Bx F 0 v = ⊥ ↔ convexConj Bu (infBifun F) (-v) = ⊤ := by
  rw [← neg_convexAdjointBifun_zero_apply (Bu := Bu) Bx (F := F) v, EReal.neg_eq_top_iff]

/-- **Inconsistency of the dual.** Let $U$ be a finite-dimensional real normed space paired with $V$
such that every continuous linear functional on $U$ has the form $\langle \cdot, v \rangle$, and
let $F$ be a convex bifunction from $U$ to $X$. Then $(P^*)$ is inconsistent if and only if
$(\inf F)(u) = -\infty$ for some perturbation $u$.

Closedness of $F$ is not needed, because $F^*$ does not distinguish $F$ from
$\operatorname{cl} F$. -/
theorem not_concaveConsistent_convexAdjointBifun_iff (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (hF : ConvexBifun F) :
    ¬ ConcaveConsistent (convexAdjointBifun Bu Bx F) ↔ ∃ u, infBifun F u = ⊥ := by
  rw [← forall_convexConj_eq_top_iff (B := Bu) (convexFn_infBifun hF), concaveConsistent_iff]
  push Not
  constructor
  · intro h y
    have hy := (convexAdjointBifun_zero_eq_bot_iff (Bu := Bu) Bx (F := F) (-y)).1 (h (-y))
    rwa [neg_neg] at hy
  · intro h v
    exact (convexAdjointBifun_zero_eq_bot_iff (Bu := Bu) Bx (F := F) v).2 (h (-v))

/-- Under the hypotheses of `ConvexAnalysis.not_concaveConsistent_convexAdjointBifun_iff`, the dual
program $(P^*)$ is consistent if and only if $(\inf F)(u) \neq -\infty$ for every perturbation
$u$. -/
theorem concaveConsistent_convexAdjointBifun_iff (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (hF : ConvexBifun F) :
    ConcaveConsistent (convexAdjointBifun Bu Bx F) ↔ ∀ u, infBifun F u ≠ ⊥ := by
  rw [← not_iff_not, not_concaveConsistent_convexAdjointBifun_iff Bx hF]
  push Not
  rfl

end DualConsistency

/-!
### The objective of the doubly adjoint program

Three algebraic facts about $G^* 0$ for a concave bifunction $G$. They need no topology and no
hypothesis on the pairings.
-/

section ConcaveAdjointZero

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y] {G : Bifun Y V}

/-- Let $G$ be a bifunction from $Y$ to $V$. The objective of the program associated with the
concave adjoint $G^*$ is
$$(G^* 0)(x) = \sup_y \{\langle x, y \rangle + (\sup G)(y)\}.$$
This is the concave counterpart of `ConvexAnalysis.convexAdjointBifun_zero_apply`. -/
theorem concaveAdjointBifun_zero_apply (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (G : Bifun Y V) (x : X) :
    concaveAdjointBifun Bu Bx G 0 x = ⨆ y, (((Bx x y : ℝ) : EReal) + supBifun G y) := by
  rw [concaveAdjointBifun_apply, iSup_prod]
  refine iSup_congr fun y => ?_
  have hzero : ∀ v : V, (Bx x y - Bu (0 : U) v : ℝ) = Bx x y := fun v => by
    rw [map_zero, LinearMap.zero_apply, sub_zero]
  simp only [hzero]
  rw [supBifun_apply, add_comm, EReal.iSup_add_coe]

/-- Let $G$ be a bifunction from $Y$ to $V$. The objective of the doubly adjoint program is the
conjugate of $-\sup G$: $G^* 0 = (-\sup G)^*$, with the conjugate taken with respect to the flip
of the pairing of $X$ and $Y$. -/
theorem concaveAdjointBifun_zero_eq_convexConj (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (G : Bifun Y V) :
    concaveAdjointBifun Bu Bx G 0 = convexConj Bx.flip (fun y => -(supBifun G y)) := by
  funext x
  rw [concaveAdjointBifun_zero_apply, convexConj_apply]
  exact iSup_congr fun y => by rw [LinearMap.flip_apply, sub_eq_add_neg, neg_neg]

/-- If $G$ is a concave bifunction, then $y \mapsto -(\sup G)(y)$ is a convex function, since it is
$\inf (-G)$. -/
theorem convexFn_neg_supBifun (hG : ConcaveBifun G) : ConvexFn (fun y => -(supBifun G y)) := by
  rw [neg_supBifun]
  exact convexFn_infBifun (concaveFn_iff_convexFn_neg.1 hG)

end ConcaveAdjointZero

section PrimalConsistency

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsCompatiblePairing Bu] {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ}
  [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip] {F : Bifun U X}

/-- **Inconsistency of the primal.** Let $U$ and $X$ be real locally convex spaces and $Y$ a
finite-dimensional real normed space, with pairings that represent all continuous linear
functionals, and let $F$ be a closed convex bifunction from $U$ to $X$. Then $(P)$ is
inconsistent if and only if $(\sup F^*)(y) = +\infty$ for some perturbation $y$.

Unlike the dual result `ConvexAnalysis.not_concaveConsistent_convexAdjointBifun_iff`, this needs
$F$ closed: it is that result for the dual pair, and $F^{**} = F$ identifies the objective of
$(P)$. -/
theorem not_consistent_iff_exists_supBifun_eq_top (hF : ConvexBifun F) (hcl : ClosedConvexBifun F) :
    ¬ Consistent F ↔ ∃ y, supBifun (convexAdjointBifun Bu Bx F) y = ⊤ := by
  have hg : ConvexFn (fun y => -(supBifun (convexAdjointBifun Bu Bx F) y)) :=
    convexFn_neg_supBifun (concaveBifun_convexAdjointBifun Bu Bx F)
  have hF0 : ∀ x : X,
      F 0 x = convexConj Bx.flip (fun y => -(supBifun (convexAdjointBifun Bu Bx F) y)) x := by
    intro x
    rw [← concaveAdjointBifun_zero_eq_convexConj Bu Bx (convexAdjointBifun Bu Bx F),
      concaveAdjointBifun_convexAdjointBifun_eq_self hF hcl]
  rw [consistent_iff]
  push Not
  simp only [hF0]
  rw [forall_convexConj_eq_top_iff (B := Bx.flip) hg]
  exact exists_congr fun y => EReal.neg_eq_bot_iff

/-- Under the hypotheses of `ConvexAnalysis.not_consistent_iff_exists_supBifun_eq_top`, the program
$(P)$ is consistent if and only if $(\sup F^*)(y) \neq +\infty$ for every perturbation $y$. -/
theorem consistent_iff_forall_supBifun_ne_top (hF : ConvexBifun F) (hcl : ClosedConvexBifun F) :
    Consistent F ↔ ∀ y, supBifun (convexAdjointBifun Bu Bx F) y ≠ ⊤ := by
  rw [← not_iff_not, not_consistent_iff_exists_supBifun_eq_top (Bu := Bu) (Bx := Bx) hF hcl]
  push Not
  rfl

end PrimalConsistency

/-! ### Kuhn–Tucker vectors of the dual program -/

section ConcaveKuhnTuckerNormal

variable {V X Y : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup X] [Module ℝ X]
  [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y]
  [ContinuousSMul ℝ Y] [LocallyConvexSpace ℝ Y] {B : Y →ₗ[ℝ] X →ₗ[ℝ] ℝ}
  [IsCompatiblePairing B] {G : Bifun Y V}

/-- Let $Y$ be a real locally convex space paired with $X$ by $B$ such that every continuous linear
functional on $Y$ has the form $B(\cdot, x)$, and let $G$ be a concave bifunction from $Y$ to
$V$. If the concave program $G$ has a Kuhn–Tucker vector, then it is normal. This is the concave
counterpart of `ConvexAnalysis.normal_of_kuhnTucker_nonempty`.

Such a vector is a supergradient of $\sup G$ at the origin, and a convex function agrees with
its closure wherever it is subdifferentiable. -/
theorem concaveNormal_of_concaveKuhnTucker_nonempty (hG : ConcaveBifun G)
    (h : (ConcaveKuhnTucker B G).Nonempty) : ConcaveNormal G := by
  obtain ⟨x, hx⟩ := h
  rw [mem_concaveKuhnTucker_iff_neg_mem_kuhnTucker] at hx
  have ht := hx.1
  have hb := hx.2.1
  have hsub : -(-x) ∈ subdifferential B (infBifun fun y v => -(G y v)) 0 :=
    (mem_kuhnTucker_iff_neg_mem_subdifferential ht hb).1 hx
  rw [neg_neg] at hsub
  have hclosed : convexCl (infBifun fun y v => -(G y v)) 0 = infBifun (fun y v => -(G y v)) 0 :=
    convexCl_eq_of_mem_subdifferential (B := B)
        (convexFn_infBifun (concaveFn_iff_convexFn_neg.1 hG))
      hsub
  have hinf0 : infBifun (fun y v => -(G y v)) 0 = -(supBifun G 0) :=
    (congrFun (neg_supBifun G) 0).symm
  rw [concaveNormal_iff, concaveCl_apply, neg_supBifun, hclosed, hinf0, neg_neg]

end ConcaveKuhnTuckerNormal

section DualKuhnTucker

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X]
  [TopologicalSpace Y] [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y] [LocallyConvexSpace ℝ Y]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsCompatiblePairing Bu] {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ}
  [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip] {F : Bifun U X}

/-- Let $U$, $X$ and $Y$ be real locally convex spaces, with pairings that represent all continuous
linear functionals, and let $F$ be a closed convex bifunction from $U$ to $X$. If the dual
program $(P^*)$ has a Kuhn–Tucker vector, then $(P)$ is normal. This is one of the sufficient
conditions of Theorem 30.4 of [rockafellar1970convex].

The finiteness of the optimal value of $(P^*)$ is part of the definition
`ConvexAnalysis.ConcaveKuhnTucker`. -/
theorem normal_of_concaveKuhnTucker_convexAdjointBifun_nonempty (hF : ConvexBifun F)
    (hcl : ClosedConvexBifun F)
    (h : (ConcaveKuhnTucker Bx.flip (convexAdjointBifun Bu Bx F)).Nonempty) : Normal F :=
  (normal_iff_concaveNormal_convexAdjointBifun hF hcl).2
    (concaveNormal_of_concaveKuhnTucker_nonempty (concaveBifun_convexAdjointBifun Bu Bx F) h)

end DualKuhnTucker

/-! ### Polyhedral programs -/

section Polyhedral

variable {U X : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] {F : Bifun U X}

/-- Let $U$ and $X$ be finite-dimensional real normed spaces and let $F$ be a polyhedral bifunction
from $U$ to $X$. If $(P)$ is consistent, then $(P)$ is normal. This is one of the sufficient
conditions of Theorem 30.4 of [rockafellar1970convex].

The function $\inf F$ is polyhedral, and a polyhedral convex function agrees with its closure on
its effective domain, which contains the origin by consistency. -/
theorem PolyhedralBifun.normal (hF : PolyhedralBifun F) (hc : Consistent F) : Normal F := by
  have hdom : (0 : U) ∈ convexDom (infBifun F) := by
    rw [convexDom_infBifun]
    exact hc
  exact PolyhedralFn.convexCl_eq_of_mem_convexDom hF.polyhedralFn_infBifun hdom

end Polyhedral

section ConcavePolyhedral

variable {V Y : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y] {G : Bifun Y V}

/-- Let $V$ and $Y$ be finite-dimensional real normed spaces and let $G$ be a concave polyhedral
bifunction from $Y$ to $V$. If the concave program $G$ is consistent, then it is normal. This is
the concave counterpart of `ConvexAnalysis.PolyhedralBifun.normal`. -/
theorem ConcavePolyhedralBifun.concaveNormal (hG : ConcavePolyhedralBifun G)
    (hc : ConcaveConsistent G) : ConcaveNormal G := by
  have hne : supBifun G 0 ≠ ⊥ := by
    have h0 : (0 : Y) ∈ concaveDom (supBifun G) := by
      rw [concaveDom_supBifun]
      exact hc
    exact (mem_concaveDom.1 h0).ne'
  have hdom : (0 : Y) ∈ convexDom fun z => -(supBifun G z) := mem_convexDom.2 (by
    rw [lt_top_iff_ne_top, ne_eq, EReal.neg_eq_top_iff]
    exact hne)
  have hpoly : PolyhedralFn fun z : Y => -(supBifun G z) := by
    rw [neg_supBifun]
    exact PolyhedralBifun.polyhedralFn_infBifun hG
  rw [concaveNormal_iff, concaveCl_apply, PolyhedralFn.convexCl_eq_of_mem_convexDom hpoly hdom]
  exact neg_neg _

end ConcavePolyhedral

section DualPolyhedral

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsCompatiblePairing Bu] {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ}
  [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip] {F : Bifun U X}

/-- Let $U$ and $X$ be real locally convex spaces and $V$ and $Y$ finite-dimensional real normed
spaces, with pairings that represent all continuous linear functionals, and let $F$ be a closed
convex bifunction from $U$ to $X$. If the dual program $(P^*)$ is polyhedral and consistent,
then $(P)$ is normal. This is one of the sufficient conditions of Theorem 30.4 of
[rockafellar1970convex]. -/
theorem normal_of_concavePolyhedral_convexAdjointBifun (hF : ConvexBifun F)
    (hcl : ClosedConvexBifun F)
    (hG : ConcavePolyhedralBifun (convexAdjointBifun Bu Bx F))
    (hc : ConcaveConsistent (convexAdjointBifun Bu Bx F)) : Normal F :=
  (normal_iff_concaveNormal_convexAdjointBifun hF hcl).2
    (ConcavePolyhedralBifun.concaveNormal hG hc)

end DualPolyhedral

/-! ### The two optimal values as a limit inferior and a limit superior -/

section Liminf

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsCompatiblePairing Bu] {F : Bifun U X}

/-- Let $U$ be a real locally convex space paired with $V$ such that every continuous linear
functional on $U$ has the form $\langle \cdot, v \rangle$, and let $F$ be a convex bifunction
from $U$ to $X$. If $(P)$ or $(P^*)$ is consistent, then
$$\liminf_{u \to 0} (\inf F)(u) = \sup_v (F^* 0)(v).$$

The limit inferior is taken along the neighbourhood filter of $0$, which includes $u = 0$. The
exception, where both programs are inconsistent, cannot be avoided: $\operatorname{cl} (\inf F)$
and $\liminf (\inf F)$ at $0$ can differ only when the first is $-\infty$, that is, the dual is
inconsistent, and the second is $+\infty$, which forces $(\inf F)(0) = +\infty$. -/
theorem liminf_infBifun_eq_iSup_convexAdjointBifun (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (hF : ConvexBifun F)
    (h : Consistent F ∨ ConcaveConsistent (convexAdjointBifun Bu Bx F)) :
    Filter.liminf (infBifun F) (𝓝 (0 : U)) = ⨆ v : V, convexAdjointBifun Bu Bx F 0 v := by
  rcases convexCl_eq_liminf_or (convexFn_infBifun hF) (0 : U) with heq | ⟨hbot, htop⟩
  · rw [← heq, convexCl_infBifun_zero_eq_iSup_convexAdjointBifun (Bu := Bu) Bx hF]
  · exfalso
    have hsup : (⨆ v : V, convexAdjointBifun Bu Bx F 0 v) = ⊥ := by
      rw [← convexCl_infBifun_zero_eq_iSup_convexAdjointBifun (Bu := Bu) Bx hF]
      exact hbot
    have hinf : infBifun F 0 = ⊤ := by
      have hle := liminf_nhds_le (infBifun F) (0 : U)
      rw [htop] at hle
      exact top_le_iff.1 hle
    rw [infBifun_apply] at hinf
    rcases h with hc | hc
    · obtain ⟨x, hx⟩ := hc
      exact hx (iInf_eq_top.1 hinf x)
    · obtain ⟨v, hv⟩ := hc
      exact hv (iSup_eq_bot.1 hsup v)

end Liminf

section Limsup

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X]
  [TopologicalSpace Y] [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y] [LocallyConvexSpace ℝ Y]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsCompatiblePairing Bu] {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ}
  [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip] {F : Bifun U X}

/-- Let $U$, $X$ and $Y$ be real locally convex spaces, with pairings that represent all continuous
linear functionals, and let $F$ be a closed convex bifunction from $U$ to $X$. If $(P)$ or
$(P^*)$ is consistent, then
$$\limsup_{y \to 0} (\sup F^*)(y) = (\inf F)(0).$$

The limit superior is taken along the neighbourhood filter of $0$, which includes $y = 0$. -/
theorem limsup_supBifun_convexAdjointBifun_eq (hF : ConvexBifun F) (hcl : ClosedConvexBifun F)
    (h : Consistent F ∨ ConcaveConsistent (convexAdjointBifun Bu Bx F)) :
    Filter.limsup (supBifun (convexAdjointBifun Bu Bx F)) (𝓝 (0 : Y)) = infBifun F 0 := by
  rcases concaveCl_eq_limsup_or (concaveFn_supBifun (concaveBifun_convexAdjointBifun Bu Bx F))
    (0 : Y) with heq | ⟨htop, hbot⟩
  · rw [← heq, concaveCl_supBifun_convexAdjointBifun_zero_eq hF hcl]
  · exfalso
    have hinf : infBifun F 0 = ⊤ := by
      rw [← concaveCl_supBifun_convexAdjointBifun_zero_eq (Bu := Bu) (Bx := Bx) hF hcl]
      exact htop
    have hsup : supBifun (convexAdjointBifun Bu Bx F) 0 = ⊥ :=
      le_bot_iff.1 (hbot ▸ le_limsup_nhds (supBifun (convexAdjointBifun Bu Bx F)) (0 : Y))
    rw [infBifun_apply] at hinf
    rw [supBifun_apply] at hsup
    rcases h with hc | hc
    · obtain ⟨x, hx⟩ := hc
      exact hx (iInf_eq_top.1 hinf x)
    · obtain ⟨v, hv⟩ := hc
      exact hv (iSup_eq_bot.1 hsup v)

end Limsup

/-!
### The dual assertion, and attainment of the primal infimum

The dual counterpart of the statement that the Kuhn–Tucker vectors are the dual optimal solutions
needs both the concave Kuhn–Tucker vectors and the computation
`ConvexAnalysis.concaveAdjointBifun_zero_apply` of the doubly adjoint objective.
-/

section ConcaveKuhnTuckerAdjoint

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]

/-- Let $G$ be a bifunction from $Y$ to $V$. A vector $x \in X$ is a Kuhn–Tucker vector of the
concave program $G$ if and only if $(\sup G)(0)$ is finite and the objective of the doubly
adjoint program attains it at $x$:
$$(G^* 0)(x) = (\sup G)(0).$$
This is the concave counterpart of
`ConvexAnalysis.mem_kuhnTucker_iff_convexAdjointBifun_zero_eq`.

The Kuhn–Tucker vectors are taken with respect to the flip of the pairing $B_x$, while the
adjoint uses $B_x$ itself. -/
theorem mem_concaveKuhnTucker_iff_concaveAdjointBifun_zero_eq (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (G : Bifun Y V) (x : X) :
    x ∈ ConcaveKuhnTucker Bx.flip G
      ↔ supBifun G 0 ≠ ⊤ ∧ supBifun G 0 ≠ ⊥
        ∧ concaveAdjointBifun Bu Bx G 0 x = supBifun G 0 := by
  have h : concaveAdjointBifun Bu Bx G 0 x
      = ⨆ y, (((Bx.flip y x : ℝ) : EReal) + supBifun G y) := by
    rw [concaveAdjointBifun_zero_apply]
    exact iSup_congr fun y => by rw [LinearMap.flip_apply]
  rw [h]
  exact Iff.rfl

end ConcaveKuhnTuckerAdjoint

section DualAssertion

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsCompatiblePairing Bu] {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ}
  [IsCompatiblePairing Bx] {F : Bifun U X} {x : X}

/-- **The dual assertion.** Let $U$ and $X$ be real locally convex spaces paired with $V$ and $Y$
such that $B_u$ and $B_x$ represent all continuous linear functionals, and let $F$ be a closed
convex bifunction from $U$ to $X$. Let $(P)$ be normal with finite optimal value $(\inf F)(0)$.
Then $x$ is a Kuhn–Tucker vector of $(P^*)$ if and only if $x$ is an optimal solution of $(P)$,
that is, a minimizer of $F0$. This is part of Theorem 30.5 of [rockafellar1970convex].

The supremum in the definition of a concave Kuhn–Tucker vector is the objective of the doubly
adjoint program, and $F^{**} = F$ turns this into $(F0)(x)$. Normality identifies the two
optimal values. -/
theorem mem_concaveKuhnTucker_convexAdjointBifun_iff_mem_argmin (hF : ConvexBifun F)
    (hcl : ClosedConvexBifun F) (hn : Normal F) (ht : infBifun F 0 ≠ ⊤) (hb : infBifun F 0 ≠ ⊥) :
    x ∈ ConcaveKuhnTucker Bx.flip (convexAdjointBifun Bu Bx F) ↔ x ∈ argmin (F 0) := by
  have hval : supBifun (convexAdjointBifun Bu Bx F) 0 = infBifun F 0 := by
    rw [supBifun_apply]
    exact (normal_iff_iSup_convexAdjointBifun_eq (Bu := Bu) Bx hF).1 hn
  have hself : concaveAdjointBifun Bu Bx (convexAdjointBifun Bu Bx F) 0 = F 0 :=
    congrFun (concaveAdjointBifun_convexAdjointBifun_eq_self hF hcl) 0
  rw [mem_concaveKuhnTucker_iff_concaveAdjointBifun_zero_eq Bu Bx, hself, hval,
    mem_argmin_iff_eq_iInf, ← infBifun_apply]
  exact ⟨fun h => h.2.2, fun h => ⟨ht, hb, h⟩⟩

end DualAssertion

section Attainment

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsCompatiblePairing Bu] {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ}
  [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip] {F : Bifun U X}

/-- **Attainment of the primal infimum.** Let $U$ be a real locally convex space, $X$ a real normed
space and $Y$ a finite-dimensional real normed space, with pairings that represent all
continuous linear functionals, and let $F$ be a closed convex bifunction from $U$ to $X$. If
$(P)$ is consistent, $(\inf F)(0) \neq -\infty$, and $(P^*)$ is strongly consistent, then the
infimum of $(P)$ is attained: $(F0)(x) = (\inf F)(0)$ for some $x$.

The proof goes through the convex program associated with $-F^*$. This is a convex bifunction
with no hypothesis on $F$, strong consistency of $(P^*)$ is strong consistency of this program,
and its perturbation function $-\sup F^*$ is proper because the optimal values are finite.
Strong consistency then gives a Kuhn–Tucker vector for $-F^*$, and the dual assertion
`ConvexAnalysis.mem_concaveKuhnTucker_convexAdjointBifun_iff_mem_argmin` turns it into a
minimizer of $F0$. -/
theorem exists_infBifun_eq_of_concaveStronglyConsistent (hF : ConvexBifun F)
    (hcl : ClosedConvexBifun F) (hc : Consistent F) (hbot : infBifun F 0 ≠ ⊥)
    (hs : ConcaveStronglyConsistent (convexAdjointBifun Bu Bx F)) : ∃ x, F 0 x = infBifun F 0 := by
  have hnorm : Normal F := normal_of_concaveStronglyConsistent_convexAdjointBifun hF hcl hs
  have hgap : supBifun (convexAdjointBifun Bu Bx F) 0 = infBifun F 0 := by
    rw [supBifun_apply]
    exact (normal_iff_iSup_convexAdjointBifun_eq (Bu := Bu) Bx hF).1 hnorm
  have htop : ∀ y, supBifun (convexAdjointBifun Bu Bx F) y ≠ ⊤ :=
    (consistent_iff_forall_supBifun_ne_top (Bu := Bu) (Bx := Bx) hF hcl).1 hc
  have hinfneg : ∀ y, infBifun (fun y' v => -(convexAdjointBifun Bu Bx F y' v)) y
      = -(supBifun (convexAdjointBifun Bu Bx F) y) :=
    fun y => (congrFun (neg_supBifun (convexAdjointBifun Bu Bx F)) y).symm
  have ht : infBifun (fun y' v => -(convexAdjointBifun Bu Bx F y' v)) 0 ≠ ⊤ := by
    rw [hinfneg 0, hgap, ne_eq, EReal.neg_eq_top_iff]
    exact hbot
  have hp : ProperConvex (infBifun fun y' v => -(convexAdjointBifun Bu Bx F y' v)) := by
    refine ⟨⟨0, lt_top_iff_ne_top.2 ht⟩, fun y => ?_⟩
    rw [hinfneg y, ne_eq, EReal.neg_eq_bot_iff]
    exact htop y
  obtain ⟨w, hw⟩ := kuhnTucker_nonempty_of_stronglyConsistent (B := Bx.flip)
    (convexBifun_neg_convexAdjointBifun Bu Bx F) hp
    (concaveStronglyConsistent_iff_stronglyConsistent_neg.1 hs) ht
  have hkt : -w ∈ ConcaveKuhnTucker Bx.flip (convexAdjointBifun Bu Bx F) := by
    rw [mem_concaveKuhnTucker_iff_neg_mem_kuhnTucker, neg_neg]
    exact hw
  obtain ⟨-, -, heq⟩ :=
    (mem_concaveKuhnTucker_iff_concaveAdjointBifun_zero_eq Bu Bx _ (-w)).1 hkt
  have hself : concaveAdjointBifun Bu Bx (convexAdjointBifun Bu Bx F) 0 = F 0 :=
    congrFun (concaveAdjointBifun_convexAdjointBifun_eq_self hF hcl) 0
  exact ⟨-w, by rw [← hgap, ← heq, hself]⟩

end Attainment

end ConvexAnalysis
