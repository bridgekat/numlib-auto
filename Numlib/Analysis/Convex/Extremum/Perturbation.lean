/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Continuity
import Numlib.Analysis.Convex.Operations.Image
import Numlib.Analysis.Convex.Extremum.Minimum
import Numlib.Analysis.Convex.Polyhedral.Duality
import Numlib.Analysis.Convex.Subdifferential.Existence
import Numlib.Analysis.Convex.Subdifferential.Gradient

/-!
# Convex bifunctions and generalized convex programs

A **bifunction** $F$ from $U$ to $X$ assigns to each $u \in U$ a function
$Fu \colon X \to [-\infty, +\infty]$. It is a family of minimization problems indexed by a
perturbation parameter $u$. The **generalized convex program** $(P)$ associated with $F$ is to
minimize $F0$ over $X$, with the perturbations $Fu$ in view. Its **perturbation function** is
$\inf F \colon u \mapsto \inf_x (Fu)(x)$, and its optimal value is $(\inf F)(0)$. Let $V$ be paired
with $U$ by $\langle u, v \rangle$. A **Kuhn–Tucker vector** of $(P)$ is a $v \in V$ such that
$(\inf F)(0)$ is finite and
$$\inf_u \{\langle u, v \rangle + (\inf F)(u)\} = (\inf F)(0).$$
So $v$ is a price at which no perturbation is worth buying. The presentation follows §29 of
[rockafellar1970convex].

All results rest on one identification. The function $\inf F$ is a partial minimization of the
convex function $(u, x) \mapsto (Fu)(x)$, hence convex, and $v$ is a Kuhn–Tucker vector exactly when
$-v \in \partial (\inf F)(0)$. So the Kuhn–Tucker set is a reflected subdifferential, and the
subgradient theory applies to it: existence under strong consistency, compactness under strict
consistency, the directional-derivative formulas, and the polyhedral case.

## Main definitions

* `ConvexAnalysis.Bifun`: a bifunction. `ConvexAnalysis.graphFn` is the same data as a function on
  $U \times X$, and `ConvexAnalysis.ConvexBifun` and `ConvexAnalysis.PolyhedralBifun` are convexity
  and polyhedrality of that function.
* `ConvexAnalysis.flipBifun`: the bifunction with its two variables exchanged.
  `ConvexAnalysis.inverseBifun`: the inverse $F_*$ of [rockafellar1970convex],
  $(F_* x)(u) = -(Fu)(x)$.
* `ConvexAnalysis.infBifun`, `ConvexAnalysis.convexDomBifun`: the perturbation function $\inf F$ and
  the effective domain $\operatorname{dom} F = \{u \mid Fu \not\equiv +\infty\}$.
* `ConvexAnalysis.KuhnTucker`: the set of Kuhn–Tucker vectors.
* `ConvexAnalysis.Consistent`, `ConvexAnalysis.StronglyConsistent`,
  `ConvexAnalysis.StrictlyConsistent`: the conditions $0 \in \operatorname{dom} F$,
  $0 \in \operatorname{ri}(\operatorname{dom} F)$ and
  $0 \in \operatorname{int}(\operatorname{dom} F)$.
* The concave counterparts `ConvexAnalysis.ConcaveBifun`, `ConvexAnalysis.supBifun`,
  `ConvexAnalysis.concaveDomBifun`, `ConvexAnalysis.ConcaveConsistent`,
  `ConvexAnalysis.ConcaveStronglyConsistent`, `ConvexAnalysis.ConcaveKuhnTucker` and
  `ConvexAnalysis.ConcavePolyhedralBifun`. Each comes right after its convex counterpart, and each
  is the convex notion for $-G$ (`ConvexAnalysis.neg_supBifun`, `ConvexAnalysis.convexDomBifun_neg`,
  `ConvexAnalysis.mem_concaveKuhnTucker_iff_neg_mem_kuhnTucker`).

## Main results

* `ConvexAnalysis.convexFn_infBifun`, `ConvexAnalysis.convexDom_infBifun`,
  `ConvexAnalysis.mem_kuhnTucker_iff_neg_mem_subdifferential`: $\inf F$ is convex with effective
  domain $\operatorname{dom} F$, and the Kuhn–Tucker set is $-\partial (\inf F)(0)$. This is Theorem
  29.1 of [rockafellar1970convex].
* `ConvexAnalysis.kuhnTucker_eq_neg_subdifferential`, `ConvexAnalysis.convex_kuhnTucker`,
  `ConvexAnalysis.isClosed_kuhnTucker`, `ConvexAnalysis.supportFn_kuhnTucker`: the Kuhn–Tucker set
  is closed and convex, and its support function is the closure of $u \mapsto (\inf F)'(0; -u)$.
* `ConvexAnalysis.kuhnTucker_eq_empty_iff`: when the Kuhn–Tucker set is empty.
  `ConvexAnalysis.kuhnTucker_eq_singleton_of_hasGradientAtFn`: when it is a single vector.
* `ConvexAnalysis.kuhnTucker_nonempty_of_stronglyConsistent`, `ConvexAnalysis.dirDeriv_infBifun_eq`:
  under strong consistency a Kuhn–Tucker vector exists, and $(\inf F)'(0; u)$ is the support
  function of the Kuhn–Tucker set at $-u$.
* `ConvexAnalysis.isCompact_kuhnTucker_of_strictlyConsistent`,
  `ConvexAnalysis.continuousOn_infBifun_interior`: under strict consistency the Kuhn–Tucker set is
  compact, and $\inf F$ is continuous near the origin.
* `ConvexAnalysis.infBifun_eq_bot_of_mem_relint`: if $\inf F$ takes the value $-\infty$, then it is
  $-\infty$ on $\operatorname{ri}(\operatorname{dom} F)$.
* `ConvexAnalysis.PolyhedralBifun.polyhedralFn_infBifun`,
  `ConvexAnalysis.kuhnTucker_nonempty_of_polyhedralBifun`,
  `ConvexAnalysis.argmin_nonempty_of_polyhedralBifun`,
  `ConvexAnalysis.polyhedral_kuhnTucker_of_polyhedralBifun`,
  `ConvexAnalysis.polyhedral_argmin_of_polyhedralBifun`: the polyhedral case, Theorem 29.2 of
  [rockafellar1970convex].

## Implementation notes

* `ConvexAnalysis.KuhnTucker` is the definition of the source, an equation for an infimum. The
  subdifferential characterization and the inequality form $(\inf F)(0) \le \langle u, v \rangle +
  (\inf F)(u)$ for all $u$ are theorems
  (`ConvexAnalysis.mem_kuhnTucker_iff_neg_mem_subdifferential`,
  `ConvexAnalysis.mem_kuhnTucker_iff_forall_le`).
* The norm bound on the Kuhn–Tucker set under strict consistency needs $V$ finite-dimensional. For a
  general dual pair the result is only that each $\langle u, \cdot \rangle$ is bounded above on the
  set (`ConvexAnalysis.bddAbove_kuhnTucker_of_strictlyConsistent`). The norm bound comes from an
  estimate in coordinates with respect to a finite basis.
-/

open Pointwise

namespace ConvexAnalysis

/-! ### Bifunctions and the perturbation function -/

section Defs

variable {U X : Type*}

/-- A **bifunction** from $U$ to $X$ is a map $F$ that assigns to each $u \in U$ a function
$Fu \colon X \to [-\infty, +\infty]$. The parameter $u$ is a perturbation.

The program $(P)$ associated with $F$ is identified with $F$ itself. -/
abbrev Bifun (U X : Type*) := U → X → EReal

/-- The **graph function** of a bifunction $F$ is the function $(u, x) \mapsto (Fu)(x)$ on
$U \times X$.

Every convexity statement about $F$ is a statement about this function. -/
def graphFn (F : Bifun U X) : U × X → EReal := fun p => F p.1 p.2

/-- The graph function of $F$ has the value $(Fu)(x)$ at $(u, x)$. -/
@[simp] theorem graphFn_apply (F : Bifun U X) (u : U) (x : X) : graphFn F (u, x) = F u x := rfl

/-- The bifunction $F$ with its two variables exchanged: the bifunction from $X$ to $U$ that maps
$x$ to the function $u \mapsto (Fu)(x)$.

Unlike the inverse $F_*$ of [rockafellar1970convex] (`ConvexAnalysis.inverseBifun`), this
operation does not change the sign, so it keeps convex bifunctions convex. It lets the convex
theory be applied to the saddle-function with its variables exchanged. -/
def flipBifun (F : Bifun U X) : Bifun X U := fun x u => F u x

/-- The exchanged bifunction has the value $(Fu)(x)$ at $x$ and $u$. -/
@[simp] theorem flipBifun_apply (F : Bifun U X) (x : X) (u : U) : flipBifun F x u = F u x := rfl

/-- Exchanging the two variables twice gives back $F$. -/
@[simp] theorem flipBifun_flipBifun (F : Bifun U X) : flipBifun (flipBifun F) = F := rfl

/-- The graph function of the exchanged bifunction at $(x, u)$ is the graph function of $F$ at
$(u, x)$. -/
theorem graphFn_flipBifun (F : Bifun U X) (q : X × U) :
    graphFn (flipBifun F) q = graphFn F (q.2, q.1) := rfl

/-- **The inverse of a bifunction.** The inverse $F_*$ of a bifunction $F$ from $U$ to $X$ is the
bifunction from $X$ to $U$ with
$$(F_* x)(u) = -(Fu)(x).$$

Unlike `ConvexAnalysis.flipBifun`, it also changes the sign, so it maps convex bifunctions to
concave ones and back. It is an involution, and the composition of bifunctions is built on it.
The change of sign makes $(Ff)(x) = \inf (f - F_* x)$ agree with $\inf_u \{f(u) + (Fu)(x)\}$. -/
noncomputable def inverseBifun (F : Bifun U X) : Bifun X U := fun x u => -(F u x)

/-- The inverse has the value $(F_* x)(u) = -(Fu)(x)$. -/
@[simp] theorem inverseBifun_apply (F : Bifun U X) (x : X) (u : U) :
    inverseBifun F x u = -(F u x) := rfl

/-- **The inverse operation is an involution**: $(F_*)_* = F$. -/
@[simp] theorem inverseBifun_inverseBifun (F : Bifun U X) :
    inverseBifun (inverseBifun F) = F :=
  funext fun u => funext fun x => neg_neg (F u x)

/-- The graph function of $F_*$ at $(x, u)$ is minus the graph function of $F$ at $(u, x)$. -/
theorem graphFn_inverseBifun (F : Bifun U X) (q : X × U) :
    graphFn (inverseBifun F) q = -(graphFn F (q.2, q.1)) := rfl

/-- The inverse $F_*$ is the bifunction $(u, x) \mapsto -(Fu)(x)$ with its two variables exchanged.
-/
theorem inverseBifun_eq_flipBifun_neg (F : Bifun U X) :
    inverseBifun F = flipBifun fun u x => -(F u x) := rfl

/-- The **perturbation function** of a bifunction $F$ is
$$(\inf F)(u) = \inf_x (Fu)(x).$$
Its value at $u = 0$ is the optimal value of the program $(P)$. -/
noncomputable def infBifun (F : Bifun U X) : U → EReal := fun u => ⨅ x, F u x

/-- The perturbation function has the value $(\inf F)(u) = \inf_x (Fu)(x)$. -/
theorem infBifun_apply (F : Bifun U X) (u : U) : infBifun F u = ⨅ x, F u x := rfl

/-- The optimal value of the concave program $Gu$ as a function of the perturbation $u$:
$$(\sup G)(u) = \sup_x (Gu)(x).$$
This is the concave counterpart of `ConvexAnalysis.infBifun`, written $\sup G$ in
[rockafellar1970convex]. -/
noncomputable def supBifun (G : Bifun U X) : U → EReal := fun u => ⨆ x, G u x

/-- The function $\sup G$ has the value $(\sup G)(u) = \sup_x (Gu)(x)$. -/
theorem supBifun_apply (G : Bifun U X) (u : U) : supBifun G u = ⨆ x, G u x := rfl

/-- The **effective domain** of a bifunction $F$ is the set of perturbations $u$ for which $Fu$ is
not identically $+\infty$:
$$\operatorname{dom} F = \{u \mid (Fu)(x) \neq +\infty \text{ for some } x\}.$$
-/
def convexDomBifun (F : Bifun U X) : Set U := {u | ∃ x, F u x ≠ ⊤}

/-- A perturbation $u$ is in $\operatorname{dom} F$ if and only if $(Fu)(x) \neq +\infty$ for some
$x$. -/
@[simp] theorem mem_convexDomBifun {F : Bifun U X} {u : U} :
    u ∈ convexDomBifun F ↔ ∃ x, F u x ≠ ⊤ := Iff.rfl

/-- The effective domain of a concave bifunction $G$ is the set of perturbations $u$ for which $Gu$
is not identically $-\infty$:
$$\{u \mid (Gu)(x) \neq -\infty \text{ for some } x\}.$$
This is the concave counterpart of `ConvexAnalysis.convexDomBifun`. -/
def concaveDomBifun (G : Bifun U X) : Set U := {u | ∃ x, G u x ≠ ⊥}

/-- A perturbation $u$ is in the effective domain of the concave bifunction $G$ if and only if
$(Gu)(x) \neq -\infty$ for some $x$. -/
theorem mem_concaveDomBifun {G : Bifun U X} {u : U} :
    u ∈ concaveDomBifun G ↔ ∃ x, G u x ≠ ⊥ := Iff.rfl

/-- For every bifunction $F$, the effective domain of the perturbation function $\inf F$ is the
effective domain of $F$:
$$\operatorname{dom} (\inf F) = \operatorname{dom} F.$$
This is part of Theorem 29.1 of [rockafellar1970convex]. -/
theorem convexDom_infBifun (F : Bifun U X) : convexDom (infBifun F) = convexDomBifun F := by
  ext u
  constructor
  · intro h
    by_contra hcon
    have hall : ∀ x, F u x = ⊤ := fun x => by
      by_contra hx
      exact hcon ⟨x, hx⟩
    have htop : (⨅ x, F u x) = ⊤ := le_antisymm le_top (le_iInf fun x => (hall x).ge)
    rw [mem_convexDom, infBifun_apply, htop] at h
    exact absurd h (lt_irrefl ⊤)
  · rintro ⟨x, hx⟩
    exact mem_convexDom.2 (lt_of_le_of_lt (iInf_le _ x) (lt_top_iff_ne_top.2 hx))

/-- For every bifunction $G$, the effective domain $\{u \mid (\sup G)(u) > -\infty\}$ of the concave
function $\sup G$ is the effective domain of $G$ as a concave bifunction. This is the concave
counterpart of `ConvexAnalysis.convexDom_infBifun`. -/
theorem concaveDom_supBifun (G : Bifun U X) : concaveDom (supBifun G) = concaveDomBifun G := by
  ext u
  simp only [mem_concaveDom, supBifun_apply, mem_concaveDomBifun, bot_lt_iff_ne_bot, ne_eq,
    iSup_eq_bot, not_forall]

/-! ### The sign dictionary -/

/-- Negating a bifunction $G$ turns its supremum into the infimum of the negation:
$-(\sup G)(u) = (\inf (-G))(u)$ for all $u$. -/
theorem neg_supBifun (G : Bifun U X) :
    (fun u => -(supBifun G u)) = infBifun fun u x => -(G u x) := by
  funext u
  rw [supBifun_apply, EReal.neg_iSup, infBifun_apply]

/-- **The effective domain of $-G$ is the concave effective domain of $G$**, since
$-(Gu)(x) \neq +\infty$ and $(Gu)(x) \neq -\infty$ are the same condition.

This turns every consistency hypothesis about a concave program into the matching hypothesis
about the convex program $-G$. -/
theorem convexDomBifun_neg
    (G : Bifun U X) : convexDomBifun (fun u x => -(G u x)) = concaveDomBifun G := by
  ext u
  simp only [mem_convexDomBifun, mem_concaveDomBifun, ne_eq, EReal.neg_eq_top_iff]

end Defs

/-! ### Convexity -/

section Convex

variable {U X : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]
  {F : Bifun U X}

/-- A bifunction $F$ from $U$ to $X$ is **convex** when its graph function $(u, x) \mapsto (Fu)(x)$
is a convex function on $U \times X$. -/
def ConvexBifun (F : Bifun U X) : Prop := ConvexFn (graphFn F)

/-- A bifunction is convex if and only if its graph function is a convex function. -/
theorem convexBifun_iff : ConvexBifun F ↔ ConvexFn (graphFn F) := Iff.rfl

/-- A bifunction $G$ from $U$ to $X$ is **concave** when its graph function $(u, x) \mapsto (Gu)(x)$
is a concave function on $U \times X$. -/
def ConcaveBifun (G : Bifun U X) : Prop := ConcaveFn (graphFn G)

/-- A bifunction is concave if and only if its graph function is a concave function. -/
theorem concaveBifun_iff {G : Bifun U X} : ConcaveBifun G ↔ ConcaveFn (graphFn G) := Iff.rfl

/-- Let $F$ be a convex bifunction. Then the perturbation function $\inf F$ is a convex function.
This is part of Theorem 29.1 of [rockafellar1970convex].

The function $\inf F$ is the partial minimization of the convex graph function along the
projection $(u, x) \mapsto u$. -/
theorem convexFn_infBifun (hF : ConvexBifun F) : ConvexFn (infBifun F) :=
  convexFn_iInf_right hF

/-- Let $G$ be a concave bifunction. Then $\sup G$ is a concave function of the perturbation. This
is the concave counterpart of `ConvexAnalysis.convexFn_infBifun`. -/
theorem concaveFn_supBifun {G : Bifun U X} (hG : ConcaveBifun G) : ConcaveFn (supBifun G) :=
  concaveFn_iff_convexFn_neg.2 (by
    rw [neg_supBifun]
    exact convexFn_infBifun (concaveFn_iff_convexFn_neg.1 hG))

/-- If $F$ is a convex bifunction, then so is the bifunction with its two variables exchanged. -/
theorem convexBifun_flipBifun (hF : ConvexBifun F) : ConvexBifun (flipBifun F) := by
  refine convexFn_of_epi_combo fun q r mu nu hq hr a b ha hb hab => ?_
  have h := hF.epi_combo (x := (q.2, q.1)) (y := (r.2, r.1)) hq hr ha hb hab
  have hsw : a • ((q.2, q.1) : U × X) + b • (r.2, r.1)
      = ((a • q + b • r).2, (a • q + b • r).1) := rfl
  rwa [hsw] at h

/-- **The inverse of a concave bifunction is convex.** If $G$ is a concave bifunction from $U$ to
$X$, then its inverse $G_*$, with $(G_* x)(u) = -(Gu)(x)$, is a convex bifunction from $X$ to
$U$. -/
theorem convexBifun_inverseBifun {G : Bifun U X} (hG : ConcaveBifun G) :
    ConvexBifun (inverseBifun G) := by
  have h : ConvexBifun fun u x => -(G u x) := hG.convexFn_neg
  exact convexBifun_flipBifun h

/-- **The inverse of a convex bifunction is concave.** If $F$ is a convex bifunction from $U$ to
$X$, then its inverse $F_*$, with $(F_* x)(u) = -(Fu)(x)$, is a concave bifunction from $X$ to
$U$.

The negative of $F_*$ is the bifunction $F$ with its variables exchanged
(`ConvexAnalysis.flipBifun`), which is convex. -/
theorem concaveBifun_inverseBifun (hF : ConvexBifun F) : ConcaveBifun (inverseBifun F) := by
  have he : (fun q : X × U => -(graphFn (inverseBifun F) q)) = graphFn (flipBifun F) :=
    funext fun _ => neg_neg _
  rw [ConcaveBifun, concaveFn_iff_convexFn_neg, he]
  exact convexBifun_flipBifun hF

/-- If $F$ is a convex bifunction, then each function $Fu$ is convex. It is a slice of a jointly
convex function, since $a u + b u = u$ when $a + b = 1$. -/
theorem ConvexBifun.convexFn_apply (hF : ConvexBifun F) (u : U) : ConvexFn (F u) := by
  refine convexFn_of_epi_combo fun x y mu nu hx hy a b ha hb hab => ?_
  have h := hF.epi_combo (x := (u, x)) (y := (u, y)) hx hy ha hb hab
  have hu : a • (u, x) + b • (u, y) = (u, a • x + b • y) := by
    rw [Prod.smul_mk, Prod.smul_mk, Prod.mk_add_mk, ← add_smul, hab, one_smul]
  rwa [hu] at h

/-- If $F$ is a convex bifunction, then its effective domain $\operatorname{dom} F$ is convex,
because it is $\operatorname{dom} (\inf F)$. -/
theorem convex_convexDomBifun (hF : ConvexBifun F) : Convex ℝ (convexDomBifun F) := by
  rw [← convexDom_infBifun]
  exact ConvexFn.convex_convexDom (convexFn_infBifun hF)

end Convex

/-! ### Consistency -/

section Consistency

variable {U X : Type*} [AddCommGroup U] {F : Bifun U X}

/-- The program $(P)$ associated with $F$ is **consistent** when $0 \in \operatorname{dom} F$, that
is, when $(F0)(x) \neq +\infty$ for some $x$. Equivalently, $(P)$ has a feasible solution, and
its optimal value is less than $+\infty$. -/
def Consistent (F : Bifun U X) : Prop := (0 : U) ∈ convexDomBifun F

/-- The program $(P)$ is consistent if and only if $(F0)(x) \neq +\infty$ for some $x$. -/
theorem consistent_iff : Consistent F ↔ ∃ x, F 0 x ≠ ⊤ := Iff.rfl

/-- The concave program associated with $G$ is **consistent** when $0$ is in the effective domain of
$G$, that is, when $(G0)(x) \neq -\infty$ for some $x$. This is the concave counterpart of
`ConvexAnalysis.Consistent`. -/
def ConcaveConsistent (G : Bifun U X) : Prop := (0 : U) ∈ concaveDomBifun G

/-- The concave program associated with $G$ is consistent if and only if $(G0)(x) \neq -\infty$ for
some $x$. -/
theorem concaveConsistent_iff {G : Bifun U X} : ConcaveConsistent G ↔ ∃ x, G 0 x ≠ ⊥ := Iff.rfl

end Consistency

section ConsistencyTopology

variable {U X : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] {F : Bifun U X}

/-- Let $U$ be a real normed space. The program $(P)$ associated with $F$ is **strongly consistent**
when $0$ is in the relative interior of $\operatorname{dom} F$:
$$0 \in \operatorname{ri}(\operatorname{dom} F).$$

This is the qualification under which Kuhn–Tucker vectors exist
(`ConvexAnalysis.kuhnTucker_nonempty_of_stronglyConsistent`). -/
def StronglyConsistent (F : Bifun U X) : Prop := (0 : U) ∈ ri (convexDomBifun F)

/-- Let $U$ be a real normed space. The concave program associated with $G$ is **strongly
consistent** when $0$ is in the relative interior of the effective domain of $G$. This is the
concave counterpart of `ConvexAnalysis.StronglyConsistent`. -/
def ConcaveStronglyConsistent (G : Bifun U X) : Prop := (0 : U) ∈ ri (concaveDomBifun G)

/-- Let $U$ be a real normed space. The program $(P)$ associated with $F$ is **strictly consistent**
when $0$ is an interior point of $\operatorname{dom} F$:
$$0 \in \operatorname{int}(\operatorname{dom} F).$$
-/
def StrictlyConsistent (F : Bifun U X) : Prop := (0 : U) ∈ interior (convexDomBifun F)

/-- A strictly consistent program is strongly consistent. -/
theorem StrictlyConsistent.stronglyConsistent (h : StrictlyConsistent F) :
    StronglyConsistent F :=
  interior_subset_intrinsicInterior h

/-- A strongly consistent program is consistent. -/
theorem StronglyConsistent.consistent (h : StronglyConsistent F) : Consistent F :=
  intrinsicInterior_subset h

/-- A strongly consistent concave program is consistent. -/
theorem ConcaveStronglyConsistent.concaveConsistent {G : Bifun U X}
    (h : ConcaveStronglyConsistent G) : ConcaveConsistent G :=
  intrinsicInterior_subset h

/-- The concave program $G$ is strongly consistent if and only if the convex program $-G$ is
strongly consistent.

This lets the concave consistency statements be read off the convex ones. -/
theorem concaveStronglyConsistent_iff_stronglyConsistent_neg {G : Bifun U X} :
    ConcaveStronglyConsistent G ↔ StronglyConsistent fun u x => -(G u x) := by
  rw [ConcaveStronglyConsistent, StronglyConsistent, convexDomBifun_neg]

end ConsistencyTopology

/-! ### Kuhn–Tucker vectors -/

section KuhnTucker

variable {U V X : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  {B : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} {F : Bifun U X} {v : V}

/-- Let $U$ and $V$ be real vector spaces paired by the bilinear form
$\langle u, v \rangle = B(u, v)$, and let $F$ be a bifunction from $U$ to $X$. A vector
$v \in V$ is a **Kuhn–Tucker vector** of the program $(P)$ associated with $F$ when the optimal
value $(\inf F)(0)$ is finite and
$$\inf_u \{\langle u, v \rangle + (\inf F)(u)\} = (\inf F)(0).$$
This defines the set of all Kuhn–Tucker vectors.

The vector $v$ is a price at which no perturbation is worth buying. -/
def KuhnTucker (B : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (F : Bifun U X) : Set V :=
  {v | infBifun F 0 ≠ ⊤ ∧ infBifun F 0 ≠ ⊥ ∧
    (⨅ u, (((B u v : ℝ) : EReal) + infBifun F u)) = infBifun F 0}

/-- Let $U$ and $V$ be real vector spaces paired by $\langle u, v \rangle = B(u, v)$, and let $G$ be
a bifunction from $U$ to $X$. A vector $v \in V$ is a **Kuhn–Tucker vector of the concave
program** associated with $G$ when $(\sup G)(0)$ is finite and
$$\sup_u \{\langle u, v \rangle + (\sup G)(u)\} = (\sup G)(0).$$
This is the concave counterpart of `ConvexAnalysis.KuhnTucker`. -/
def ConcaveKuhnTucker (B : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (G : Bifun U X) : Set V :=
  {v | supBifun G 0 ≠ ⊤ ∧ supBifun G 0 ≠ ⊥ ∧
    (⨆ u, (((B u v : ℝ) : EReal) + supBifun G u)) = supBifun G 0}

/-- A vector $v$ is a Kuhn–Tucker vector of the concave program $G$ if and only if $-v$ is a
Kuhn–Tucker vector of the convex program $-G$. -/
theorem mem_concaveKuhnTucker_iff_neg_mem_kuhnTucker {G : Bifun U X} :
    v ∈ ConcaveKuhnTucker B G ↔ -v ∈ KuhnTucker B (fun u x => -(G u x)) := by
  have hinf : ∀ u : U, infBifun (fun u' x => -(G u' x)) u = -(supBifun G u) := fun u =>
    (congrFun (neg_supBifun G) u).symm
  have hkey : (⨅ u : U, (((B u (-v) : ℝ) : EReal) + infBifun (fun u' x => -(G u' x)) u))
      = -(⨆ u : U, (((B u v : ℝ) : EReal) + supBifun G u)) := by
    rw [EReal.neg_iSup]
    refine iInf_congr fun u => ?_
    have hb : ((B u (-v) : ℝ) : EReal) = -(((B u v : ℝ)) : EReal) := by
      rw [← EReal.coe_neg, map_neg]
    rw [hinf u, hb, EReal.neg_add (.inl (EReal.coe_ne_bot _))
      (.inl (EReal.coe_ne_top _))]
    rfl
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [hinf 0, ne_eq, EReal.neg_eq_top_iff]
      exact h2
    · rw [hinf 0, ne_eq, EReal.neg_eq_bot_iff]
      exact h1
    · rw [hkey, hinf 0, h3]
  · rintro ⟨h1, h2, h3⟩
    rw [hinf 0, ne_eq, EReal.neg_eq_top_iff] at h1
    rw [hinf 0, ne_eq, EReal.neg_eq_bot_iff] at h2
    rw [hkey, hinf 0] at h3
    exact ⟨h2, h1, neg_inj.1 h3⟩

/-- For every bifunction $F$ and every $v$,
$$\inf_u \{\langle u, v \rangle + (\inf F)(u)\} \le (\inf F)(0).$$
This is the value of the infimum at $u = 0$. -/
theorem iInf_add_infBifun_le (B : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (F : Bifun U X) (v : V) :
    (⨅ u, (((B u v : ℝ) : EReal) + infBifun F u)) ≤ infBifun F 0 := by
  refine le_trans (iInf_le _ 0) (le_of_eq ?_)
  rw [map_zero, LinearMap.zero_apply, EReal.coe_zero, zero_add]

/-- A vector $v$ is a Kuhn–Tucker vector if and only if $(\inf F)(0)$ is finite and
$$(\inf F)(0) \le \langle u, v \rangle + (\inf F)(u) \qquad \text{for all } u.$$
At the price $v$, every perturbation costs at least what it saves. -/
theorem mem_kuhnTucker_iff_forall_le :
    v ∈ KuhnTucker B F ↔ infBifun F 0 ≠ ⊤ ∧ infBifun F 0 ≠ ⊥ ∧
      ∀ u, infBifun F 0 ≤ ((B u v : ℝ) : EReal) + infBifun F u := by
  constructor
  · rintro ⟨ht, hb, heq⟩
    refine ⟨ht, hb, fun u => ?_⟩
    rw [← heq]
    exact iInf_le _ u
  · rintro ⟨ht, hb, hall⟩
    exact ⟨ht, hb, le_antisymm (iInf_add_infBifun_le B F v) (le_iInf hall)⟩

/-- Let $F$ be a bifunction from $U$ to $X$ whose optimal value $(\inf F)(0)$ is finite. Then $v$ is
a Kuhn–Tucker vector if and only if
$$-v \in \partial (\inf F)(0).$$
This is part of Theorem 29.1 of [rockafellar1970convex].

The subgradient inequality for $-v$ at the origin says that no perturbation is worth buying at
the price $v$. The subdifferential is taken with respect to the pairing $B$. -/
theorem mem_kuhnTucker_iff_neg_mem_subdifferential (ht : infBifun F 0 ≠ ⊤) (hb : infBifun F 0 ≠ ⊥) :
    v ∈ KuhnTucker B F ↔ -v ∈ subdifferential B (infBifun F) 0 := by
  obtain ⟨c, hc⟩ := EReal.exists_coe_of_ne_bot_of_lt_top hb (lt_top_iff_ne_top.2 ht)
  have hiff : ∀ u : U, (infBifun F 0 ≤ ((B u v : ℝ) : EReal) + infBifun F u)
      ↔ (infBifun F 0 + ((B (u - 0) (-v) : ℝ) : EReal) ≤ infBifun F u) := by
    intro u
    rw [sub_zero, map_neg, hc, EReal.coe_neg, ← sub_eq_add_neg,
      EReal.sub_le_iff_le_add (.inl (EReal.coe_ne_bot _)) (.inl (EReal.coe_ne_top _)), add_comm]
  rw [mem_kuhnTucker_iff_forall_le, mem_subdifferential]
  exact ⟨fun h u => (hiff u).1 (h.2.2 u), fun h => ⟨ht, hb, fun u => (hiff u).2 (h u)⟩⟩

/-- Let $F$ be a bifunction whose optimal value $(\inf F)(0)$ is finite. Then the Kuhn–Tucker set is
the reflected subdifferential of the perturbation function at the origin:
$$\{v \mid v \text{ is a Kuhn–Tucker vector}\} = -\partial (\inf F)(0).$$
-/
theorem kuhnTucker_eq_neg_subdifferential (ht : infBifun F 0 ≠ ⊤) (hb : infBifun F 0 ≠ ⊥) :
    KuhnTucker B F = -(subdifferential B (infBifun F) 0) := by
  ext v
  rw [Set.mem_neg]
  exact mem_kuhnTucker_iff_neg_mem_subdifferential ht hb

/-- Let $F$ be a bifunction whose optimal value $(\inf F)(0)$ is finite. Then the set of Kuhn–Tucker
vectors is convex. -/
theorem convex_kuhnTucker (ht : infBifun F 0 ≠ ⊤) (hb : infBifun F 0 ≠ ⊥) :
    Convex ℝ (KuhnTucker B F) := by
  rw [kuhnTucker_eq_neg_subdifferential ht hb]
  exact (convex_subdifferential B (infBifun F) 0).neg

end KuhnTucker

/-! ### Closedness and existence -/

section Topology

variable {U V X : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V] {B : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} {F : Bifun U X}

/-- Let $U$ and $V$ be real normed spaces paired by $B$ such that $v \mapsto B(u, v)$ is continuous
for each $u$, and let $F$ be a bifunction whose optimal value $(\inf F)(0)$ is finite. Then the
set of Kuhn–Tucker vectors is closed. -/
theorem isClosed_kuhnTucker [IsContinuousPairing B.flip] (ht : infBifun F 0 ≠ ⊤)
    (hb : infBifun F 0 ≠ ⊥) : IsClosed (KuhnTucker B F) := by
  rw [kuhnTucker_eq_neg_subdifferential ht hb]
  exact (isClosed_subdifferential (B := B) (infBifun F) 0).neg

end Topology

section Existence

variable {U V X : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [AddCommGroup X] [Module ℝ X]
  {B : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} {F : Bifun U X}

/-- Let $U$ be a finite-dimensional real normed space and $V$ a real normed space, paired by $B$
such that every continuous linear functional on $U$ has the form $\langle \cdot, v \rangle$. Let
$F$ be a convex bifunction from $U$ to $X$ such that $\inf F$ is proper, $(P)$ is strongly
consistent, and $(\inf F)(0) \neq +\infty$. Then $(P)$ has a Kuhn–Tucker vector.

The origin is in the relative interior of $\operatorname{dom}(\inf F)$, so the proper convex
function $\inf F$ is subdifferentiable there. -/
theorem kuhnTucker_nonempty_of_stronglyConsistent [IsCompatiblePairing B] (hF : ConvexBifun F)
    (hp : ProperConvex (infBifun F)) (hs : StronglyConsistent F) (ht : infBifun F 0 ≠ ⊤) :
    (KuhnTucker B F).Nonempty := by
  have hri : (0 : U) ∈ ri (convexDom (infBifun F)) := by rwa [convexDom_infBifun]
  obtain ⟨y, hy⟩ :=
    subdifferential_nonempty_of_mem_relint_convexDom (B := B) (convexFn_infBifun hF) hp hri
  refine ⟨-y, ?_⟩
  rw [mem_kuhnTucker_iff_neg_mem_subdifferential ht (hp.ne_bot 0), neg_neg]
  exact hy

end Existence

/-! ### The directional derivative of the perturbation function -/

section DirDeriv

variable {U V X : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] {B : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} {F : Bifun U X}

/-- The support function of a reflected set is the support function at the reflected point:
$\delta^*(v \mid -s) = \delta^*(-v \mid s)$. -/
theorem supportFn_neg_set (B : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (s : Set U) (v : V) :
    supportFn B (-s) v = supportFn B s (-v) := by
  rw [supportFn_apply, supportFn_apply]
  refine le_antisymm (iSup₂_le fun u hu => ?_) (iSup₂_le fun u hu => ?_)
  · have hmem : -u ∈ s := hu
    refine le_trans (le_of_eq ?_)
      (le_iSup₂ (f := fun w (_ : w ∈ s) => ((B w (-v) : ℝ) : EReal)) (-u) hmem)
    simp
  · have hmem : -u ∈ -s := by
      rw [Set.mem_neg, neg_neg]
      exact hu
    refine le_trans (le_of_eq ?_)
      (le_iSup₂ (f := fun w (_ : w ∈ -s) => ((B w v : ℝ) : EReal)) (-u) hmem)
    simp

omit [AddCommGroup X] [Module ℝ X] in
/-- For every bifunction $F$, the directional derivative $u \mapsto (\inf F)'(0; u)$ is positively
homogeneous. -/
theorem posHomogeneous_dirDeriv_infBifun (F : Bifun U X) :
    PosHomogeneous (dirDeriv (infBifun F) 0) :=
  posHomogeneous_dirDeriv _ _

/-- Let $F$ be a convex bifunction whose optimal value $(\inf F)(0)$ is finite. Then the directional
derivative $u \mapsto (\inf F)'(0; u)$ is a convex function. -/
theorem convexFn_dirDeriv_infBifun (hF : ConvexBifun F) (ht : infBifun F 0 ≠ ⊤)
    (hb : infBifun F 0 ≠ ⊥) : ConvexFn (dirDeriv (infBifun F) 0) :=
  convexFn_dirDeriv (convexFn_infBifun hF) ht hb

end DirDeriv

section DirDerivSupport

variable {U V X : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [TopologicalSpace U] [IsTopologicalAddGroup U]
  [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  {B : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsCompatiblePairing B] {F : Bifun U X}

/-- Let $U$ be a real locally convex space paired with $V$ by $B$ such that every continuous linear
functional on $U$ has the form $\langle \cdot, v \rangle$. Let $F$ be a convex bifunction from
$U$ to $X$ whose optimal value $(\inf F)(0)$ is finite. Then for every $u \in U$, the support
function of the Kuhn–Tucker set is
$$\sup \{\langle u, v \rangle \mid v \text{ a Kuhn–Tucker vector}\} = (\operatorname{cl} g)(-u),
  \qquad g = (\inf F)'(0; \cdot).$$

The support function of a subdifferential is the closure of the directional derivative, and the
reflection $v \mapsto -v$ moves to the argument $-u$. -/
theorem supportFn_kuhnTucker (hF : ConvexBifun F) (ht : infBifun F 0 ≠ ⊤)
    (hb : infBifun F 0 ≠ ⊥) (u : U) :
    supportFn B.flip (KuhnTucker B F) u = convexCl (dirDeriv (infBifun F) 0) (-u) := by
  rw [kuhnTucker_eq_neg_subdifferential ht hb, supportFn_neg_set,
    convexCl_dirDeriv (B := B) (convexFn_infBifun hF) ht hb]

end DirDerivSupport

/-! ### The improper and the empty case -/

section Improper

variable {U V X : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [AddCommGroup V] [Module ℝ V] [AddCommGroup X] [Module ℝ X]
  {B : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} {F : Bifun U X}

omit [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U] [AddCommGroup V]
  [Module ℝ V] [AddCommGroup X] [Module ℝ X] in
/-- If $u \notin \operatorname{dom} F$, then the optimal value $(\inf F)(u)$ is $+\infty$. -/
theorem infBifun_eq_top_of_notMem_convexDomBifun {u : U}
    (hu : u ∉ convexDomBifun F) : infBifun F u = ⊤ := by
  by_contra h
  exact hu (by rw [← convexDom_infBifun]; exact mem_convexDom.2 (lt_of_le_of_ne le_top h))

omit [FiniteDimensional ℝ U] [AddCommGroup V] [Module ℝ V] in
/-- Let $U$ be a real normed space and let $F$ be a convex bifunction from $U$ to $X$. If
$(\inf F)(u') = -\infty$ for some $u'$, then $(\inf F)(u) = -\infty$ for every
$u \in \operatorname{ri}(\operatorname{dom} F)$.

An improper convex function is $-\infty$ on the relative interior of its effective domain. -/
theorem infBifun_eq_bot_of_mem_relint (hF : ConvexBifun F) (h : ∃ u, infBifun F u = ⊥) {u : U}
    (hu : u ∈ ri (convexDomBifun F)) : infBifun F u = ⊥ := by
  obtain ⟨u₀, hu₀⟩ := h
  have hp : ¬ ProperConvex (infBifun F) := fun hp => hp.ne_bot u₀ hu₀
  refine ConvexFn.eq_bot_of_mem_relint_convexDom (convexFn_infBifun hF) hp ?_
  rwa [convexDom_infBifun]

end Improper

section KuhnTuckerEmpty

variable {U V X : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [AddCommGroup V] [Module ℝ V] [AddCommGroup X] [Module ℝ X]
  {B : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsCompatiblePairing B] {F : Bifun U X}

/-- Let $U$ be a finite-dimensional real normed space paired with $V$ by $B$ such that every
continuous linear functional on $U$ has the form $\langle \cdot, v \rangle$. Let $F$ be a convex
bifunction from $U$ to $X$ whose optimal value $(\inf F)(0)$ is finite. Then $(P)$ has no
Kuhn–Tucker vector if and only if there is a direction $u$ with
$$(\inf F)'(0; u) = -\infty \quad \text{and} \quad (\inf F)'(0; -u) = +\infty,$$
that is, the two-sided directional derivative $(\inf F)'(0; u) = -(\inf F)'(0; -u)$ is
$-\infty$.

For the forward direction: an empty subdifferential makes the closure of $(\inf F)'(0; \cdot)$
the constant $-\infty$, and the closure of a proper convex function is proper. -/
theorem kuhnTucker_eq_empty_iff (hF : ConvexBifun F) (ht : infBifun F 0 ≠ ⊤)
    (hb : infBifun F 0 ≠ ⊥) :
    KuhnTucker B F = ∅ ↔
      ∃ u : U, dirDeriv (infBifun F) 0 u = ⊥ ∧ dirDeriv (infBifun F) 0 (-u) = ⊤ := by
  have hconv := convexFn_infBifun hF
  constructor
  · intro hempty
    have h1 : -(subdifferential B (infBifun F) 0) = ∅ := by
      rw [← kuhnTucker_eq_neg_subdifferential ht hb]
      exact hempty
    have hsub : subdifferential B (infBifun F) 0 = ∅ := by
      rw [← neg_neg (subdifferential B (infBifun F) 0), h1]
      simp
    have hcl : convexCl (dirDeriv (infBifun F) 0) = fun _ => (⊥ : EReal) := by
      rw [convexCl_dirDeriv (B := B) hconv ht hb, hsub, supportFn_empty]
    have hnp : ¬ ProperConvex (dirDeriv (infBifun F) 0) := by
      intro hp
      have hpc := ConvexFn.properConvex_convexCl (convexFn_dirDeriv hconv ht hb) hp
      rw [hcl] at hpc
      exact hpc.ne_bot 0 rfl
    have hdom : (convexDom (dirDeriv (infBifun F) 0)).Nonempty :=
      ⟨0, mem_convexDom.2 (by rw [dirDeriv_zero ht hb]; exact EReal.zero_lt_top)⟩
    have hy : ∃ u, dirDeriv (infBifun F) 0 u = ⊥ := by
      by_contra hcon
      push Not at hcon
      exact hnp ⟨hdom, hcon⟩
    obtain ⟨u, hub⟩ := hy
    refine ⟨u, hub, ?_⟩
    have hle := neg_dirDeriv_neg_le hconv ht hb u
    rw [hub, le_bot_iff, EReal.neg_eq_bot_iff] at hle
    exact hle
  · rintro ⟨u, hu, -⟩
    rw [Set.eq_empty_iff_forall_notMem]
    intro v hv
    rw [mem_kuhnTucker_iff_neg_mem_subdifferential ht hb,
      mem_subdifferential_iff_le_dirDeriv ht hb] at hv
    have hcontra := hv u
    rw [hu, le_bot_iff] at hcontra
    exact absurd hcontra (EReal.coe_ne_bot _)

end KuhnTuckerEmpty

/-! ### What consistency and differentiability buy -/

section Consistency

variable {U X : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [AddCommGroup X] [Module ℝ X] {F : Bifun U X}

omit [FiniteDimensional ℝ U] in
/-- Let $U$ be a real normed space and let $F$ be a strongly consistent convex bifunction from $U$
to $X$ with $(\inf F)(0) \neq -\infty$. Then $\inf F$ is proper. If it were improper, it would
be $-\infty$ on $\operatorname{ri}(\operatorname{dom} F)$, which contains the origin. -/
theorem properConvex_infBifun_of_stronglyConsistent (hF : ConvexBifun F) (hs : StronglyConsistent F)
    (hb : infBifun F 0 ≠ ⊥) : ProperConvex (infBifun F) := by
  refine ⟨⟨0, ?_⟩, fun u => ?_⟩
  · rw [convexDom_infBifun]
    exact StronglyConsistent.consistent hs
  · exact fun hcon => hb (infBifun_eq_bot_of_mem_relint hF ⟨u, hcon⟩ hs)

/-- Let $U$ be a finite-dimensional real normed space and let $F$ be a convex bifunction from $U$ to
$X$ such that $\inf F$ is proper. Then $\inf F$ is continuous on
$\operatorname{int}(\operatorname{dom} F)$.

Under strict consistency, this interior is a neighbourhood of the origin. -/
theorem continuousOn_infBifun_interior (hF : ConvexBifun F) (hp : ProperConvex (infBifun F)) :
    ContinuousOn (infBifun F) (interior (convexDomBifun F)) := by
  have hsub : interior (convexDomBifun F) ⊆ ri (convexDom (infBifun F)) := by
    rw [convexDom_infBifun]
    exact interior_subset_intrinsicInterior
  exact ContinuousOn.mono ((convexFn_infBifun hF).continuousOn_relint_convexDom hp) hsub

omit [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U] [AddCommGroup X]
  [Module ℝ X] in
/-- If $u \in \operatorname{dom} F$, then the optimal value $(\inf F)(u)$ is not $+\infty$. -/
theorem infBifun_ne_top_of_mem_convexDomBifun {u : U}
    (hu : u ∈ convexDomBifun F) : infBifun F u ≠ ⊤ := by
  rw [← convexDom_infBifun] at hu
  exact (mem_convexDom.1 hu).ne

end Consistency

section DirDerivFormula

variable {U V X : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [AddCommGroup V] [Module ℝ V] [AddCommGroup X] [Module ℝ X]
  {B : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsCompatiblePairing B] {F : Bifun U X}

/-- **The derivative formula.** Let $U$ be a finite-dimensional real normed space paired with $V$ by
$B$ such that every continuous linear functional on $U$ has the form $\langle \cdot, v \rangle$.
Let $F$ be a strongly consistent convex bifunction from $U$ to $X$ such that $\inf F$ is proper.
Then for every $u \in U$,
$$(\inf F)'(0; u) = \sup \{\langle -u, v \rangle \mid v \text{ a Kuhn–Tucker vector}\},$$
the support function of the Kuhn–Tucker set at the reflected direction $-u$. -/
theorem dirDeriv_infBifun_eq (hF : ConvexBifun F) (hp : ProperConvex (infBifun F))
    (hs : StronglyConsistent F) (u : U) :
    dirDeriv (infBifun F) 0 u = supportFn B.flip (KuhnTucker B F) (-u) := by
  have hri : (0 : U) ∈ ri (convexDom (infBifun F)) := by rwa [convexDom_infBifun]
  have ht : infBifun F 0 ≠ ⊤ := (mem_convexDom.1 (intrinsicInterior_subset hri)).ne
  rw [kuhnTucker_eq_neg_subdifferential ht (hp.ne_bot 0), supportFn_neg_set, neg_neg,
    dirDeriv_eq_supportFn_of_mem_relint_convexDom (B := B) (convexFn_infBifun hF) hp hri]

/-- Under the hypotheses of `ConvexAnalysis.dirDeriv_infBifun_eq`, but with $(P)$ strictly
consistent, the Kuhn–Tucker set is bounded in the sense of the pairing: for every $u \in U$
there is a real $c$ with $\langle u, v \rangle \le c$ for all Kuhn–Tucker vectors $v$. -/
theorem bddAbove_kuhnTucker_of_strictlyConsistent (hF : ConvexBifun F)
    (hp : ProperConvex (infBifun F))
    (hs : StrictlyConsistent F) (u : U) :
    ∃ c : ℝ, ∀ v ∈ KuhnTucker B F, B u v ≤ c := by
  have hint : (0 : U) ∈ interior (convexDom (infBifun F)) := by rwa [convexDom_infBifun]
  have hri : (0 : U) ∈ ri (convexDom (infBifun F)) := interior_subset_intrinsicInterior hint
  have ht : infBifun F 0 ≠ ⊤ := (mem_convexDom.1 (intrinsicInterior_subset hri)).ne
  obtain ⟨c, hc⟩ :=
    (bddAbove_subdifferential_iff_mem_interior_convexDom (B := B) (convexFn_infBifun hF) hp
        hri).2 hint
      (-u)
  refine ⟨c, fun v hv => ?_⟩
  rw [kuhnTucker_eq_neg_subdifferential ht (hp.ne_bot 0), Set.mem_neg] at hv
  have hb := hc (-v) hv
  simpa using hb

end DirDerivFormula

section KuhnTuckerCompact

variable {U V X : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [AddCommGroup X] [Module ℝ X]
  {B : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsCompatiblePairing B] [IsCompatiblePairing B.flip] {F : Bifun U X}

/-- Let $U$ and $V$ be finite-dimensional real normed spaces, paired by $B$ such that the continuous
linear functionals on $U$ are the maps $\langle \cdot, v \rangle$ and those on $V$ are the maps
$\langle u, \cdot \rangle$. Let $F$ be a strictly consistent convex bifunction from $U$ to $X$
such that $\inf F$ is proper. Then the Kuhn–Tucker set is bounded in the norm of $V$.

The step from the bound in the sense of the pairing
(`ConvexAnalysis.bddAbove_kuhnTucker_of_strictlyConsistent`) to the norm bound uses finite
dimension. -/
theorem isBounded_kuhnTucker_of_strictlyConsistent (hF : ConvexBifun F)
    (hp : ProperConvex (infBifun F)) (hs : StrictlyConsistent F) :
    Bornology.IsBounded (KuhnTucker B F) := by
  rw [isBounded_iff_forall_bddAbove (B := B.flip)]
  intro u
  simpa using bddAbove_kuhnTucker_of_strictlyConsistent (B := B) hF hp hs u

/-- Let $U$ and $V$ be finite-dimensional real normed spaces, paired by $B$ such that the continuous
linear functionals on $U$ are the maps $\langle \cdot, v \rangle$ and those on $V$ are the maps
$\langle u, \cdot \rangle$. Let $F$ be a strictly consistent convex bifunction from $U$ to $X$
such that $\inf F$ is proper and $(\inf F)(0) \neq +\infty$. Then the set of Kuhn–Tucker vectors
is compact.

The set is closed and bounded. With `ConvexAnalysis.kuhnTucker_nonempty_of_strictlyConsistent`
and `ConvexAnalysis.convex_kuhnTucker`, it is the "non-empty closed bounded convex set" of
[rockafellar1970convex]. -/
theorem isCompact_kuhnTucker_of_strictlyConsistent (hF : ConvexBifun F)
    (hp : ProperConvex (infBifun F)) (hs : StrictlyConsistent F) (ht : infBifun F 0 ≠ ⊤) :
    IsCompact (KuhnTucker B F) :=
  Metric.isCompact_of_isClosed_isBounded (isClosed_kuhnTucker ht (hp.ne_bot 0))
    (isBounded_kuhnTucker_of_strictlyConsistent hF hp hs)

omit [FiniteDimensional ℝ V] [IsCompatiblePairing B.flip] in
/-- Let $U$ be a finite-dimensional real normed space paired with a real normed space $V$ by $B$
such that every continuous linear functional on $U$ has the form $\langle \cdot, v \rangle$. Let
$F$ be a strictly consistent convex bifunction from $U$ to $X$ such that $\inf F$ is proper and
$(\inf F)(0) \neq +\infty$. Then $(P)$ has a Kuhn–Tucker vector, because a strictly consistent
program is strongly consistent. -/
theorem kuhnTucker_nonempty_of_strictlyConsistent (hF : ConvexBifun F)
    (hp : ProperConvex (infBifun F)) (hs : StrictlyConsistent F) (ht : infBifun F 0 ≠ ⊤) :
    (KuhnTucker B F).Nonempty :=
  kuhnTucker_nonempty_of_stronglyConsistent (B := B) hF hp hs.stronglyConsistent ht

end KuhnTuckerCompact

section KuhnTuckerUnique

variable {U V X : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] {B : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} {F : Bifun U X}

omit [AddCommGroup X] [Module ℝ X] in
/-- **The unique Kuhn–Tucker vector, algebraic form.** Let $U$ and $V$ be paired by $B$ such that
$v \mapsto \langle \cdot, v \rangle$ is injective, and let $F$ be a bifunction whose optimal
value $(\inf F)(0)$ is finite. If $(\inf F)'(0; u) = \langle u, -v_0 \rangle$ for every $u$,
then $v_0$ is the only Kuhn–Tucker vector. -/
theorem kuhnTucker_eq_singleton_of_dirDeriv_eq (hsep : Function.Injective B.flip)
    (ht : infBifun F 0 ≠ ⊤) (hb : infBifun F 0 ≠ ⊥) {v₀ : V}
    (h : ∀ u : U, dirDeriv (infBifun F) 0 u = ((B u (-v₀) : ℝ) : EReal)) :
    KuhnTucker B F = {v₀} := by
  rw [kuhnTucker_eq_neg_subdifferential ht hb,
    subdifferential_eq_singleton_of_dirDeriv_eq hsep ht hb h]
  simp

end KuhnTuckerUnique

section KuhnTuckerGradient

variable {U X : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [AddCommGroup X] [Module ℝ X]
  {F : Bifun U X}

/-- **The unique Kuhn–Tucker vector, Fréchet form.** Let $U$ be a real normed space, paired with its
continuous dual. Let $F$ be a convex bifunction from $U$ to $X$ whose optimal value
$(\inf F)(0)$ is finite, and let $\inf F$ have the gradient $f'$ at the origin. Then $-f'$ is
the only Kuhn–Tucker vector.

The pairing of $U$ with its dual is `(topDualPairing ℝ U).flip`. The gradient is in the sense of
`ConvexAnalysis.HasGradientAtFn`. -/
theorem kuhnTucker_eq_singleton_of_hasGradientAtFn (hF : ConvexBifun F)
    {f' : StrongDual ℝ U} (h : HasGradientAtFn (infBifun F) f' 0) (ht : infBifun F 0 ≠ ⊤)
    (hb : infBifun F 0 ≠ ⊥) :
    KuhnTucker (topDualPairing ℝ U).flip F = {-f'} := by
  rw [kuhnTucker_eq_neg_subdifferential ht hb,
    HasGradientAtFn.subdifferential_eq (convexFn_infBifun hF) h]
  simp

end KuhnTuckerGradient

/-! ### Polyhedral convex programs -/

section PolyhedralImage

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] {f : E → EReal}

/-- Let $f$ be a polyhedral convex function on a finite-dimensional real normed space. Then the
closure of $f$ agrees with $f$ on the effective domain of $f$.

If $f$ is proper, it is closed. Otherwise both functions are $-\infty$ on the effective domain. -/
theorem PolyhedralFn.convexCl_eq_of_mem_convexDom (hf : PolyhedralFn f) {x : E}
    (hx : x ∈ convexDom f) :
    convexCl f x = f x := by
  by_cases hp : ProperConvex f
  · exact congrFun (hf.closedConvex hp.ne_bot) x
  · have hbot : f x = ⊥ :=
      ConvexFn.eq_bot_of_mem_closure_convexDom hf.convexFn hf.lowerSemicontinuous
          hp (subset_closure hx)
    have hl : lscHull f x = ⊥ := le_bot_iff.1 (hbot ▸ lscHull_le f x)
    rw [convexCl_of_exists_eq_bot ⟨x, hl⟩, hbot]

end PolyhedralImage

section PolyhedralBifun

variable {U V X : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  {B : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} {F : Bifun U X}

/-- Let $U$ and $X$ be finite-dimensional real normed spaces. A bifunction $F$ from $U$ to $X$ is
**polyhedral** when its graph function $(u, x) \mapsto (Fu)(x)$ is a polyhedral convex function.
The associated program is then a *polyhedral convex program*. -/
def PolyhedralBifun (F : Bifun U X) : Prop := PolyhedralFn (graphFn F)

/-- A bifunction $G$ is **concave polyhedral** when its negative $-G$ is a polyhedral bifunction.
This is the concave counterpart of `ConvexAnalysis.PolyhedralBifun`. -/
def ConcavePolyhedralBifun (G : Bifun U X) : Prop := PolyhedralBifun fun u x => -(G u x)

omit [FiniteDimensional ℝ U] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [FiniteDimensional ℝ X] in
/-- A bifunction is polyhedral if and only if its graph function is a polyhedral convex function. -/
theorem polyhedralBifun_iff : PolyhedralBifun F ↔ PolyhedralFn (graphFn F) := Iff.rfl

omit [FiniteDimensional ℝ U] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [FiniteDimensional ℝ X] in
/-- A polyhedral bifunction is convex. -/
theorem PolyhedralBifun.convexBifun (hF : PolyhedralBifun F) : ConvexBifun F :=
  PolyhedralFn.convexFn hF

omit [FiniteDimensional ℝ U] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [FiniteDimensional ℝ X] in
/-- Let $F$ be a polyhedral bifunction. Then every function $Fu$ is a polyhedral convex function. In
particular, the objective $F0$ is polyhedral. -/
theorem PolyhedralBifun.polyhedralFn_apply (hF : PolyhedralBifun F) (u : U) :
    PolyhedralFn (F u) := by
  have hpre : epi (F u)
      = (fun p : X × ℝ => ((LinearMap.inr ℝ U X).prodMap (LinearMap.id : ℝ →ₗ[ℝ] ℝ)) p
          + ((u, (0 : X)), (0 : ℝ))) ⁻¹' epi (graphFn F) := by
    ext p
    simp [graphFn]
  change Polyhedral (epi (F u))
  rw [hpre]
  exact Polyhedral.comap_affine hF _ _

omit [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- Let $U$ and $X$ be finite-dimensional real normed spaces and let $F$ be a polyhedral bifunction
from $U$ to $X$. Then the perturbation function $\inf F$ is a polyhedral convex function. This
is part of Theorem 29.2 of [rockafellar1970convex].

The function $\inf F$ is a partial minimization of a polyhedral convex function along the
projection $(u, x) \mapsto u$. -/
theorem PolyhedralBifun.polyhedralFn_infBifun (hF : PolyhedralBifun F) :
    PolyhedralFn (infBifun F) := by
  have h : infBifun F = mapLin (LinearMap.fst ℝ U X) (graphFn F) := by
    funext u
    rw [mapLin_fst_apply, infBifun_apply]
    rfl
  rw [h]
  exact PolyhedralFn.mapLin hF _

omit [FiniteDimensional ℝ V] in
/-- Let $U$ be a finite-dimensional real normed space paired with a real normed space $V$ by $B$
such that every continuous linear functional on $U$ has the form $\langle \cdot, v \rangle$. Let
$F$ be a polyhedral bifunction from $U$ to a finite-dimensional real normed space $X$ whose
optimal value $(\inf F)(0)$ is finite. Then $(P)$ has a Kuhn–Tucker vector. This is part of
Theorem 29.2 of [rockafellar1970convex].

A polyhedral convex function is subdifferentiable at every point of its effective domain. -/
theorem kuhnTucker_nonempty_of_polyhedralBifun [IsCompatiblePairing B] (hF : PolyhedralBifun F)
    (ht : infBifun F 0 ≠ ⊤) (hb : infBifun F 0 ≠ ⊥) : (KuhnTucker B F).Nonempty := by
  obtain ⟨y, hy⟩ :=
    subdifferential_nonempty_of_polyhedralFn (B := B) hF.polyhedralFn_infBifun ht hb
  exact ⟨-y, by rw [mem_kuhnTucker_iff_neg_mem_subdifferential ht hb, neg_neg]; exact hy⟩

/-- Let $U$ and $V$ be finite-dimensional real normed spaces paired by $B$, and let $F$ be a
polyhedral bifunction from $U$ to a finite-dimensional real normed space $X$ whose optimal value
$(\inf F)(0)$ is finite. Then the set of Kuhn–Tucker vectors is a polyhedral convex set. -/
theorem polyhedral_kuhnTucker_of_polyhedralBifun (hF : PolyhedralBifun F)
    (ht : infBifun F 0 ≠ ⊤) (hb : infBifun F 0 ≠ ⊥) : Polyhedral (KuhnTucker B F) := by
  rw [kuhnTucker_eq_neg_subdifferential ht hb]
  exact Polyhedral.neg
    (polyhedral_subdifferential_of_polyhedralFn (B := B) hF.polyhedralFn_infBifun ht hb)

omit [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [FiniteDimensional ℝ U] in
/-- Let $U$ be a real normed space and $X$ a finite-dimensional real normed space, and let $F$ be a
polyhedral bifunction from $U$ to $X$ with $(\inf F)(0) \neq -\infty$. Then $(P)$ has an
**optimal solution**: the infimum of $F0$ is attained. This is part of Theorem 29.2 of
[rockafellar1970convex].

The source assumes that the optimal value is finite. Only $(\inf F)(0) \neq -\infty$ is used
here: if the optimal value is $+\infty$, every point is optimal. Finiteness is needed for the
polyhedrality of the set of optimal solutions
(`ConvexAnalysis.polyhedral_argmin_of_polyhedralBifun`). The proof uses only the objective $F0$,
which is a polyhedral convex function on $X$, so $U$ need not be finite-dimensional. -/
theorem argmin_nonempty_of_polyhedralBifun (hF : PolyhedralBifun F) (hb : infBifun F 0 ≠ ⊥) :
    (argmin (F 0)).Nonempty := by
  refine argmin_nonempty_of_polyhedralFn (hF.polyhedralFn_apply 0) ?_
  have h : (⨅ x, F 0 x) = infBifun F 0 := (infBifun_apply F 0).symm
  rw [h]
  exact lt_of_le_of_ne bot_le (Ne.symm hb)

omit [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [FiniteDimensional ℝ U] in
/-- Let $U$ be a real normed space and $X$ a finite-dimensional real normed space, and let $F$ be a
polyhedral bifunction from $U$ to $X$ whose optimal value $(\inf F)(0)$ is finite. Then the set
of optimal solutions of $(P)$ is a polyhedral convex set. It is the sublevel set of $F0$ at the
optimal value. -/
theorem polyhedral_argmin_of_polyhedralBifun (hF : PolyhedralBifun F) (ht : infBifun F 0 ≠ ⊤)
    (hb : infBifun F 0 ≠ ⊥) : Polyhedral (argmin (F 0)) := by
  obtain ⟨x, hx⟩ := argmin_nonempty_of_polyhedralBifun hF hb
  have hval : F 0 x = infBifun F 0 := by
    rw [infBifun_apply]
    exact le_antisymm (le_iInf hx) (iInf_le _ x)
  have hb' : F 0 x ≠ ⊥ := by rw [hval]; exact hb
  have ht' : F 0 x < ⊤ := by rw [hval]; exact lt_top_iff_ne_top.2 ht
  obtain ⟨μ, hμ⟩ := EReal.exists_coe_of_ne_bot_of_lt_top hb' ht'
  rw [argmin_eq_setOf_le hx hμ]
  exact (hF.polyhedralFn_apply 0).polyhedral_sublevel μ

end PolyhedralBifun

end ConvexAnalysis
