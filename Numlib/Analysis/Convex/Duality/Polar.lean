/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Geometry.Convex.Cone.Dual
import Numlib.Analysis.Convex.Duality.Support
import Numlib.Order.GaloisConnection

/-!
# Polars of convex sets and convex cones

Let $B$ be a bilinear pairing of real vector spaces $E$ and $F$, written
$\langle x, y \rangle = B(x, y)$. The **polar** of a set $K \subseteq E$, viewed as a cone, is
$K^\circ = \{y \in F \mid \langle x, y \rangle \le 0 \text{ for all } x \in K\}$, and the polar of a
set $C \subseteq E$, viewed as a convex set containing the origin, is $C^\circ = \{y \in F \mid
\langle x, y \rangle \le 1 \text{ for all } x \in C\}$. Polars of subsets of $F$ are taken with
respect to the flipped pairing and are subsets of $E$. Polarity is what conjugacy becomes on
indicator functions: the indicator of a cone is positively homogeneous, so its conjugate is again an
indicator, and the set that it indicates is the polar. The **bipolar theorem**
$K^{\circ\circ} = \operatorname{cl} K$ for a nonempty convex cone $K$ follows from this together
with separation. The presentation follows §14 of [rockafellar1970convex].

The further polarity theorems need the recession function or the gauge. They are proved in
`Numlib.Analysis.Convex.Recession.Conjugate`, `Numlib.Analysis.Convex.Duality.HomConePolar`,
`Numlib.Analysis.Convex.Duality.Level`, `Numlib.Analysis.Convex.Duality.Gauge` and
`Numlib.Analysis.Convex.Duality.PolarBounded`.

## Main definitions

* `ConvexAnalysis.polarCone`, `ConvexAnalysis.polarSet`: the two polars $K^\circ$ and $C^\circ$
  above.
* `ConvexAnalysis.polarPointedCone`: the polar $K^\circ$ bundled as a pointed cone in $F$.
* `ConvexAnalysis.polarSubmodule`: the polar of a subspace, bundled as a subspace of $F$.
* `ConvexAnalysis.polarConeClosure`, `ConvexAnalysis.polarSetClosure`: the closure operators
  $K \mapsto K^{\circ\circ}$ and $C \mapsto C^{\circ\circ}$ on the subsets of $E$.
* `ConvexAnalysis.partialAffineFn`: the partial affine function $\delta(\cdot \mid a + L) + \langle
  \cdot, b \rangle + \alpha$.

## Main results

* `ConvexAnalysis.isClosed_polarCone`, `ConvexAnalysis.polarPointedCone`: the polar of any set is a
  nonempty closed convex cone; this is the first assertion of Theorem 14.1 of
  [rockafellar1970convex] (the bipolar theorem).
* `ConvexAnalysis.polarCone_polarCone`: $K^{\circ\circ} = \operatorname{cl} K$ for a nonempty convex
  cone $K$; this is the second assertion of Theorem 14.1.
* `ConvexAnalysis.convexConj_indicatorFn_eq_indicatorFn_polarCone`: the conjugate of the indicator
  of a nonempty cone $K$ is the indicator of $K^\circ$; this is the third assertion of Theorem 14.1.
* `ConvexAnalysis.neg_polarCone_neg_polarCone`: $K^{**} = K$ for a nonempty closed convex cone $K$
  and its dual cone $K^* = -K^\circ$.
* `ConvexAnalysis.polarSet_polarSet`: $C^{\circ\circ} = C$ for a closed convex set $C$ that contains
  the origin (Theorem 14.5 of [rockafellar1970convex]).
* `ConvexAnalysis.gc_polarCone_polarCone`, `ConvexAnalysis.gc_polarSet_polarSet`: each kind of
  polarity is an antitone Galois connection between the subsets of $E$ and the subsets of $F$.
* `ConvexAnalysis.polarCone_eq_setOf_supportFn_le_zero`: for an arbitrary set $K$, the polar
  $K^\circ$ is the set where the support function of $K$ is at most $0$.
* `ConvexAnalysis.polarSet_closure`, `ConvexAnalysis.polarSet_union`,
  `ConvexAnalysis.polarSet_convexHull`, `ConvexAnalysis.polarSet_smul`,
  `ConvexAnalysis.polarCone_add`: the polar does not change under closure and convex hull, turns
  unions and sums into intersections, and turns $aC$ into $a^{-1} C^\circ$.
* `ConvexAnalysis.polarCone_coe_submodule`, `ConvexAnalysis.polarCone_hull_range`,
  `ConvexAnalysis.polarCone_setOf_forall_le_zero`, `ConvexAnalysis.polarCone_nonnegOrthant`: the
  polar of a subspace is its annihilator, the polar of a finitely or infinitely generated cone is
  the solution set of the corresponding homogeneous inequalities and conversely, and the polar of
  the nonnegative orthant is the nonpositive orthant.
* `ConvexAnalysis.convexConj_partialAffineFn`: the conjugate of a partial affine function is
$$\bigl(\delta(\cdot \mid a + L) + \langle \cdot, b \rangle + \alpha\bigr)^* = \delta(\cdot \mid b +
  L^\perp) + \langle a, \cdot \rangle - \alpha - \langle a, b \rangle.$$

## Implementation notes

* Every bipolar statement takes `Convex ℝ K`, `ConvexAnalysis.IsCone K` and `K.Nonempty` separately,
  because the separation argument runs in this generality. A `PointedCone ℝ E` supplies all three
  hypotheses (`ConvexAnalysis.isCone_coe_pointedCone` gives the second), and each statement has a
  `_pointedCone` companion.
* The theorem is $K^{\circ\circ} = \operatorname{cl} K$, not $K^{\circ\circ} = K$. Nonemptiness of
  $K$ is necessary: $\emptyset^\circ = F$, and $F^\circ$ is the set of $x$ with
  $\langle x, y \rangle \le 0$ for all $y$, which is not $\operatorname{cl} \emptyset = \emptyset$.
* The adjunction $L \subseteq K^\circ \iff K \subseteq L^\circ$ makes $K \mapsto K^{\circ\circ}$ a
  `ClosureOperator (Set E)`. The `OrderDual` is on the codomain, not on the domain, because the
  embedding $s \mapsto \delta(\cdot \mid s)$ of sets into functions is antitone.
* Two Mathlib objects are close but different. `PointedCone.dual` is the inner dual cone $\{y \mid
  \langle x, y \rangle \ge 0 \text{ for all } x \in K\}$, so $K^\circ$ is the dual cone of $-K$
  (`ConvexAnalysis.polarPointedCone_eq_dual_neg`). `LinearMap.polar` is the absolute polar, which
  agrees with `ConvexAnalysis.polarSet` on balanced sets
  (`ConvexAnalysis.polarSet_eq_polar_of_balanced`).
* The bipolar theorem here assumes `ConvexAnalysis.IsCompatiblePairing` rather than a perfect
  pairing, and closedness of the polar needs only `ConvexAnalysis.IsContinuousPairing`.
-/

open Set Pointwise

namespace ConvexAnalysis

/-! ### Definitions -/

section Defs

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

/-- The **polar cone** of a set $K \subseteq E$ with respect to the pairing $B$ is
$$K^\circ = \{y \in F \mid \langle x, y \rangle \le 0 \text{ for all } x \in K\}.$$

This one-sided polar is neither Mathlib's absolute polar `LinearMap.polar` nor its inner dual
cone `PointedCone.dual`. It is the dual cone of $-K$
(`ConvexAnalysis.polarPointedCone_eq_dual_neg`). The set $K$ is arbitrary; the name refers to
the case where $K$ is a convex cone. -/
def polarCone (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (K : Set E) : Set F := {y | ∀ x ∈ K, B x y ≤ 0}

/-- The **polar** of a set $C \subseteq E$ with respect to the pairing $B$, in the sense of
[rockafellar1970convex] §14, is
$$C^\circ = \{y \in F \mid \langle x, y \rangle \le 1 \text{ for all } x \in C\}.$$

The set $C$ is arbitrary; the definition is mainly used for convex sets that contain the origin. -/
def polarSet (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (C : Set E) : Set F := {y | ∀ x ∈ C, B x y ≤ 1}

variable {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {K L : Set E} {C D : Set E} {y : F}

/-- A point $y$ lies in $K^\circ$ if and only if $\langle x, y \rangle \le 0$ for every $x \in K$.
-/
@[simp] theorem mem_polarCone : y ∈ polarCone B K ↔ ∀ x ∈ K, B x y ≤ 0 := Iff.rfl

/-- A point $y$ lies in $C^\circ$ if and only if $\langle x, y \rangle \le 1$ for every $x \in C$.
-/
@[simp] theorem mem_polarSet : y ∈ polarSet B C ↔ ∀ x ∈ C, B x y ≤ 1 := Iff.rfl

/-- The polar cone is antitone: if $K \subseteq L$, then $L^\circ \subseteq K^\circ$. -/
theorem polarCone_anti (h : K ⊆ L) : polarCone B L ⊆ polarCone B K := fun _ hy x hx => hy x (h hx)

/-- The polar set is antitone: if $C \subseteq D$, then $D^\circ \subseteq C^\circ$. -/
theorem polarSet_anti (h : C ⊆ D) : polarSet B D ⊆ polarSet B C := fun _ hy x hx => hy x (h hx)

/-- The polar cone of the empty set is all of $F$. -/
@[simp] theorem polarCone_empty (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) :
    polarCone B (∅ : Set E) = univ := by ext y; simp

/-- The polar set of the empty set is all of $F$. -/
@[simp] theorem polarSet_empty (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) :
    polarSet B (∅ : Set E) = univ := by ext y; simp

/-- The origin of $F$ lies in the polar cone of every set. -/
@[simp] theorem zero_mem_polarCone (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (K : Set E) :
    (0 : F) ∈ polarCone B K := fun x _ => by simp

/-- The origin of $F$ lies in the polar set of every set. -/
@[simp] theorem zero_mem_polarSet (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (C : Set E) :
    (0 : F) ∈ polarSet B C := fun x _ => by simp

/-- The polar cone of every set is nonempty. -/
theorem polarCone_nonempty (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (K : Set E) : (polarCone B K).Nonempty :=
  ⟨0, zero_mem_polarCone B K⟩

/-- The polar cone of a set is contained in its polar set: $\{y \mid \langle x, y \rangle \le 0 \
\forall x \in K\} \subseteq \{y \mid \langle x, y \rangle \le 1 \ \forall x \in K\}$, since
$0 \le 1$. -/
theorem polarCone_subset_polarSet : polarCone B K ⊆ polarSet B K :=
  fun _ hy x hx => (hy x hx).trans zero_le_one

/-- For all sets $K, L \subseteq E$, the polar cone of the union is the intersection of the polar
cones:
$$(K \cup L)^\circ = K^\circ \cap L^\circ.$$
-/
theorem polarCone_union (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (K L : Set E) :
    polarCone B (K ∪ L) = polarCone B K ∩ polarCone B L := by
  ext y; exact ⟨fun h => ⟨fun x hx => h x (Or.inl hx), fun x hx => h x (Or.inr hx)⟩,
    fun h x hx => hx.elim (h.1 x) (h.2 x)⟩

/-- For a family of sets $u_i \subseteq E$, the polar cone of the union is the intersection of the
polar cones: $\bigl(\bigcup_i u_i\bigr)^\circ = \bigcap_i u_i^\circ$. -/
theorem polarCone_iUnion {ι : Sort*} (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (u : ι → Set E) :
    polarCone B (⋃ i, u i) = ⋂ i, polarCone B (u i) := by
  ext y
  simp only [mem_polarCone, Set.mem_iInter, Set.mem_iUnion]
  exact ⟨fun h i x hx => h x ⟨i, hx⟩, fun h x hx => hx.elim fun i hi => h i x hi⟩

/-- For all sets $C, D \subseteq E$, the polar set of the union is the intersection of the polar
sets:
$$(C \cup D)^\circ = C^\circ \cap D^\circ.$$
-/
theorem polarSet_union (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (C D : Set E) :
    polarSet B (C ∪ D) = polarSet B C ∩ polarSet B D := by
  ext y
  simp only [polarSet, Set.mem_ofPred, Set.mem_inter_iff, Set.mem_union]
  exact ⟨fun h => ⟨fun x hx => h x (Or.inl hx), fun x hx => h x (Or.inr hx)⟩,
    fun h x hx => hx.elim (h.1 x) (h.2 x)⟩

/-- For a family of sets $u_i \subseteq E$, the polar set of the union is the intersection of the
polar sets: $\bigl(\bigcup_i u_i\bigr)^\circ = \bigcap_i u_i^\circ$. -/
theorem polarSet_iUnion {ι : Sort*} (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (u : ι → Set E) :
    polarSet B (⋃ i, u i) = ⋂ i, polarSet B (u i) := by
  ext y
  simp only [polarSet, Set.mem_ofPred, Set.mem_iInter, Set.mem_iUnion]
  exact ⟨fun h i x hx => h x ⟨i, hx⟩, fun h x hx => hx.elim fun i hi => h i x hi⟩


/-- **For a cone the two polars coincide.** If $K$ is closed under multiplication by positive
scalars, then $\{y \mid \langle x, y \rangle \le 0 \ \forall x \in K\} = \{y \mid \langle x, y
\rangle \le 1 \ \forall x \in K\}$, because the half-space
$\{x \mid \langle x, y \rangle \le 1\}$ contains a cone exactly when
$\{x \mid \langle x, y \rangle \le 0\}$ does. -/
theorem polarCone_eq_polarSet_of_isCone (hK : IsCone K) :
    polarCone B K = polarSet B K := by
  refine subset_antisymm polarCone_subset_polarSet fun y hy x hx => ?_
  by_contra hcon
  rw [not_le] at hcon
  have hmem : (2 / B x y) • x ∈ K :=
    (smul_mem_iff_of_isCone hK (by positivity)).2 hx
  have h := hy _ hmem
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul, div_mul_cancel₀ _ hcon.ne'] at h
  linarith

/-- **The polarity adjunction for cones.** For $K \subseteq E$ and $L \subseteq F$,
$L \subseteq K^\circ$ if and only if $K \subseteq L^\circ$, where $L^\circ$ is taken with
respect to the flipped pairing. Both conditions say that $\langle x, y \rangle \le 0$ for every
$x \in K$ and $y \in L$. -/
theorem subset_polarCone_comm {L : Set F} : L ⊆ polarCone B K ↔ K ⊆ polarCone B.flip L :=
  ⟨fun h _ hx _ hy => h hy _ hx, fun h _ hy _ hx => h hx _ hy⟩

/-- **The polarity adjunction for sets.** For $C \subseteq E$ and $L \subseteq F$,
$L \subseteq C^\circ$ if and only if $C \subseteq L^\circ$, where $L^\circ$ is the polar set
with respect to the flipped pairing. Both conditions say that $\langle x, y \rangle \le 1$ for
every $x \in C$ and $y \in L$. -/
theorem subset_polarSet_comm {L : Set F} : L ⊆ polarSet B C ↔ C ⊆ polarSet B.flip L :=
  ⟨fun h _ hx _ hy => h hy _ hx, fun h _ hy _ hx => h hx _ hy⟩

/-- Every set $K \subseteq E$ is contained in its bipolar cone: $K \subseteq K^{\circ\circ}$, where
the second polar is taken with respect to the flipped pairing. -/
theorem subset_polarCone_polarCone (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (K : Set E) :
    K ⊆ polarCone B.flip (polarCone B K) := subset_polarCone_comm.1 (subset_refl _)

/-- Every set $C \subseteq E$ is contained in its bipolar set: $C \subseteq C^{\circ\circ}$, where
the second polar is taken with respect to the flipped pairing. -/
theorem subset_polarSet_polarSet (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (C : Set E) :
    C ⊆ polarSet B.flip (polarSet B C) := subset_polarSet_comm.1 (subset_refl _)

/-! ### Polarity as a Galois connection -/

/-- **Polarity of cones is an antitone Galois connection.** The map $K \mapsto K^\circ$ from the
subsets of $E$ to the order dual of the subsets of $F$, and the map $L \mapsto L^\circ$ back
(polar with respect to the flipped pairing), form a Galois connection: $K^\circ \supseteq L$ if
and only if $K \subseteq L^\circ$. -/
theorem gc_polarCone_polarCone (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) :
    GaloisConnection (fun K : Set E => OrderDual.toDual (polarCone B K))
      (fun L : (Set F)ᵒᵈ => polarCone B.flip (OrderDual.ofDual L)) :=
  fun _ _ => subset_polarCone_comm

/-- **Polarity of sets is an antitone Galois connection.** The map $C \mapsto C^\circ$ from the
subsets of $E$ to the order dual of the subsets of $F$, and the map $L \mapsto L^\circ$ back
(polar set with respect to the flipped pairing), form a Galois connection: $C^\circ \supseteq L$
if and only if $C \subseteq L^\circ$. -/
theorem gc_polarSet_polarSet (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) :
    GaloisConnection (fun C : Set E => OrderDual.toDual (polarSet B C))
      (fun L : (Set F)ᵒᵈ => polarSet B.flip (OrderDual.ofDual L)) :=
  fun _ _ => subset_polarSet_comm

/-- The **bipolar cone operator** $K \mapsto K^{\circ\circ}$ as a closure operator on the subsets of
$E$. It is the closure operator of the Galois connection
`ConvexAnalysis.gc_polarCone_polarCone`.

When $E$ is a locally convex space and the pairing is compatible with its topology, the closed
elements of this operator are exactly the nonempty closed convex cones, by
`ConvexAnalysis.polarCone_polarCone_of_isClosed`. -/
def polarConeClosure (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) : ClosureOperator (Set E) :=
  (gc_polarCone_polarCone B).closureOperator

/-- The bipolar cone operator sends $K$ to $K^{\circ\circ}$, where the second polar is taken with
respect to the flipped pairing. -/
@[simp] theorem polarConeClosure_apply (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (K : Set E) :
    polarConeClosure B K = polarCone B.flip (polarCone B K) := rfl

/-- A set $K \subseteq E$ is closed for the bipolar cone operator if and only if
$K^{\circ\circ} = K$. -/
theorem isClosed_polarConeClosure_iff :
    (polarConeClosure B).IsClosed K ↔ polarCone B.flip (polarCone B K) = K := Iff.rfl

/-- The **bipolar set operator** $C \mapsto C^{\circ\circ}$ as a closure operator on the subsets of
$E$. It is the closure operator of the Galois connection `ConvexAnalysis.gc_polarSet_polarSet`.

When $E$ is a locally convex space and the pairing is compatible with its topology, the closed
elements of this operator are exactly the closed convex sets that contain the origin, by
`ConvexAnalysis.polarSet_polarSet`. -/
def polarSetClosure (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) : ClosureOperator (Set E) :=
  (gc_polarSet_polarSet B).closureOperator

/-- The bipolar set operator sends $C$ to $C^{\circ\circ}$, where the second polar is taken with
respect to the flipped pairing. -/
@[simp] theorem polarSetClosure_apply (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (C : Set E) :
    polarSetClosure B C = polarSet B.flip (polarSet B C) := rfl

/-- A set $C \subseteq E$ is closed for the bipolar set operator if and only if
$C^{\circ\circ} = C$. -/
theorem isClosed_polarSetClosure_iff :
    (polarSetClosure B).IsClosed C ↔ polarSet B.flip (polarSet B C) = C := Iff.rfl

/-- **The polar cone does not change when the bipolar is taken first.** For every set
$K \subseteq E$, $(K^{\circ\circ})^\circ = K^\circ$. This is the triangle identity of the
polarity adjunction, and an algebraic form of the identity
$(\operatorname{cl} K)^\circ = K^\circ$ of [rockafellar1970convex] §14. -/
theorem polarCone_polarCone_polarCone (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (K : Set E) :
    polarCone B (polarCone B.flip (polarCone B K)) = polarCone B K :=
  subset_antisymm (polarCone_anti (subset_polarCone_polarCone B K))
    (subset_polarCone_comm.2 (subset_refl _))

/-- **Polarity of cones is an order anti-isomorphism between the bipolar-closed sets.** The map
$K \mapsto K^\circ$ is an order isomorphism from the sets $K \subseteq E$ with
$K^{\circ\circ} = K$ to the order dual of the sets $L \subseteq F$ with $L^{\circ\circ} = L$.

No topology is used. When $E$ is a locally convex space and the pairing is compatible with its
topology, `ConvexAnalysis.polarCone_polarCone` shows that the bipolar-closed sets in $E$ are
exactly the nonempty closed convex cones. -/
def polarConeOrderIso (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) :
    {K : Set E // polarCone B.flip (polarCone B K) = K} ≃o
      {L : (Set F)ᵒᵈ //
        OrderDual.toDual (polarCone B (polarCone B.flip (OrderDual.ofDual L))) = L} :=
  (gc_polarCone_polarCone B).closedsOrderIso

/-- **Polarity of sets is an order anti-isomorphism between the bipolar-closed sets.** The map
$C \mapsto C^\circ$ is an order isomorphism from the sets $C \subseteq E$ with
$C^{\circ\circ} = C$ to the order dual of the sets $L \subseteq F$ with $L^{\circ\circ} = L$. -/
def polarSetOrderIso (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) :
    {C : Set E // polarSet B.flip (polarSet B C) = C} ≃o
      {L : (Set F)ᵒᵈ //
        OrderDual.toDual (polarSet B (polarSet B.flip (OrderDual.ofDual L))) = L} :=
  (gc_polarSet_polarSet B).closedsOrderIso

/-! ### The polar cone as a `PointedCone` -/

/-- The polar cone $K^\circ$ of an arbitrary set $K \subseteq E$, bundled as a pointed convex cone
in $F$: it contains $0$ and is closed under addition and under multiplication by nonnegative
scalars.

This is the algebraic part of the first assertion of Theorem 14.1 of [rockafellar1970convex],
before any topology enters. The bundling makes the `PointedCone` API available. -/
def polarPointedCone (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (K : Set E) : PointedCone ℝ F where
  carrier := polarCone B K
  zero_mem' := zero_mem_polarCone B K
  add_mem' {u v} hu hv x hx := by
    rw [map_add]
    exact add_nonpos (hu x hx) (hv x hx)
  smul_mem' c u hu x hx := by
    rw [← Nonneg.coe_smul, map_smul, smul_eq_mul]
    calc (c : ℝ) * B x u ≤ (c : ℝ) * 0 := mul_le_mul_of_nonneg_left (hu x hx) c.2
      _ = 0 := mul_zero _

/-- The underlying set of `ConvexAnalysis.polarPointedCone B K` is the polar cone $K^\circ$. -/
@[simp] theorem coe_polarPointedCone (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (K : Set E) :
    (polarPointedCone B K : Set F) = polarCone B K := rfl

/-- A point $y$ lies in the bundled polar cone of $K$ if and only if $\langle x, y \rangle \le 0$
for every $x \in K$. -/
@[simp] theorem mem_polarPointedCone : y ∈ polarPointedCone B K ↔ ∀ x ∈ K, B x y ≤ 0 := Iff.rfl

/-- The polar cone of every set is convex. -/
theorem convex_polarCone (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (K : Set E) : Convex ℝ (polarCone B K) :=
  ((polarPointedCone B K : ConvexCone ℝ F)).convex

/-- The polar set of every set is convex. -/
theorem convex_polarSet (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (C : Set E) : Convex ℝ (polarSet B C) := by
  intro y hy z hz a b ha hb hab x hx
  have h1 := hy x hx
  have h2 := hz x hx
  simp only [map_add, map_smul, smul_eq_mul]
  nlinarith

/-- **A closed half-space of the pairing is convex.** For $y \in F$ and $c \in \mathbb{R}$, the set
$\{x \in E \mid \langle x, y \rangle \le c\}$ is convex.

This is the real-valued form, which cuts out a polar set;
`ConvexAnalysis.convex_setOf_pairing_le` is the form with an extended-real bound. -/
theorem convex_setOf_pairing_le_coe (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (y : F) (c : ℝ) :
    Convex ℝ {x : E | B x y ≤ c} := by
  intro u hu v hv a b ha hb hab
  have hu' : B u y ≤ c := hu
  have hv' : B v y ≤ c := hv
  have : B (a • u + b • v) y = a * B u y + b * B v y := by
    simp [map_add, map_smul, smul_eq_mul]
  change B (a • u + b • v) y ≤ c
  rw [this]
  calc a * B u y + b * B v y ≤ a * c + b * c := by
        exact add_le_add (mul_le_mul_of_nonneg_left hu' ha) (mul_le_mul_of_nonneg_left hv' hb)
    _ = c := by rw [← add_mul, hab, one_mul]

/-- **The polar set does not change under the convex hull.** For every set $C \subseteq E$,
$$(\operatorname{conv} C)^\circ = C^\circ.$$

The reason is that $C^\circ$ is cut out by the convex half-spaces
$\{x \mid \langle x, y \rangle \le 1\}$. The counterpart for the polar cone is
`ConvexAnalysis.polarCone_hull`. -/
@[simp] theorem polarSet_convexHull (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (C : Set E) :
    polarSet B (convexHull ℝ C) = polarSet B C := by
  refine Set.Subset.antisymm (polarSet_anti (subset_convexHull ℝ C)) fun y hy => ?_
  exact fun x hx => convexHull_min (fun z hz => (hy z hz : B z y ≤ 1))
    (convex_setOf_pairing_le_coe B y 1) hx

/-- **Dilating a set inverts the dilation of its polar.** Let $a > 0$ and $C \subseteq E$. Then
$$(aC)^\circ = a^{-1} C^\circ.$$
-/
theorem polarSet_smul (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) {a : ℝ} (ha : 0 < a) (C : Set E) :
    polarSet B (a • C) = a⁻¹ • polarSet B C := by
  have key : ∀ (c : ℝ) (x : E) (z : F), B (c • x) z = B x (c • z) := fun c x z => by
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  ext y
  constructor
  · intro hy
    refine ⟨a • y, fun x hx => ?_, inv_smul_smul₀ ha.ne' y⟩
    have h := hy (a • x) ⟨x, hx, rfl⟩
    rwa [key] at h
  · rintro ⟨z, hz, rfl⟩ _ ⟨x, hx, rfl⟩
    have h := hz x hx
    have hval : B (a • x) (a⁻¹ • z) = B x z := by
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
      rw [← mul_assoc, inv_mul_cancel₀ ha.ne', one_mul]
    rw [hval]
    exact h

/-- **The polar cone of a sum is the intersection of the polar cones.** Let $K, L \subseteq E$ both
contain the origin. Then
$$(K + L)^\circ = K^\circ \cap L^\circ.$$

This is the additive counterpart of `ConvexAnalysis.polarCone_union`. -/
theorem polarCone_add (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) {K L : Set E} (hK : (0 : E) ∈ K)
    (hL : (0 : E) ∈ L) : polarCone B (K + L) = polarCone B K ∩ polarCone B L := by
  refine Set.Subset.antisymm (fun y hy => ⟨fun x hx => ?_, fun x hx => ?_⟩) ?_
  · simpa using hy (x + 0) ⟨x, hx, 0, hL, rfl⟩
  · simpa using hy (0 + x) ⟨0, hK, x, hx, rfl⟩
  · rintro y ⟨h₁, h₂⟩ _ ⟨x₁, hx₁, x₂, hx₂, rfl⟩
    have hsum : B (x₁ + x₂) y = B x₁ y + B x₂ y := by simp
    change B (x₁ + x₂) y ≤ 0
    rw [hsum]
    simpa using add_le_add (h₁ x₁ hx₁) (h₂ x₂ hx₂)

/-- A pointed cone $K$ in $E$ is invariant under positive dilation: $aK = K$ for every $a > 0$. -/
theorem smul_coe_pointedCone (K : PointedCone ℝ E) (a : ℝ) (ha : 0 < a) :
    a • (K : Set E) = (K : Set E) := by
  ext x
  refine ⟨?_, fun hx => ⟨a⁻¹ • x, K.smul_mem (inv_pos.2 ha).le hx, smul_inv_smul₀ ha.ne' x⟩⟩
  rintro ⟨z, hz, rfl⟩
  exact K.smul_mem ha.le hz

/-- A subspace $M$ of $E$ is invariant under positive dilation: $aM = M$ for every $a > 0$. -/
theorem smul_coe_submodule (M : Submodule ℝ E) {a : ℝ} (ha : 0 < a) :
    a • (M : Set E) = (M : Set E) := by
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact M.smul_mem a hu
  · intro hz
    refine ⟨a⁻¹ • z, M.smul_mem _ hz, ?_⟩
    change a • a⁻¹ • z = z
    rw [smul_smul, mul_inv_cancel₀ ha.ne', one_smul]

/-- The polar cone of every set is invariant under positive dilation: $a K^\circ = K^\circ$ for
every $a > 0$. -/
theorem smul_polarCone (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (K : Set E) (a : ℝ) (ha : 0 < a) :
    a • polarCone B K = polarCone B K := smul_coe_pointedCone (polarPointedCone B K) a ha

/-- The underlying set of a pointed cone $K \subseteq E$ is a cone: it is closed under
multiplication by positive scalars. -/
theorem isCone_coe_pointedCone (K : PointedCone ℝ E) : IsCone (K : Set E) :=
  fun _ ha _ hx => K.smul_mem ha.le hx

/-- The underlying set of a subspace $M$ of $E$ is a cone: it is closed under multiplication by
positive scalars. -/
theorem isCone_coe_submodule (M : Submodule ℝ E) : IsCone (M : Set E) :=
  fun a _ _ hx => M.smul_mem a hx

/-- The polar cone $K^\circ$ of every set $K \subseteq E$ is a cone: it is closed under
multiplication by positive scalars. -/
theorem isCone_polarCone (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (K : Set E) : IsCone (polarCone B K) :=
  isCone_coe_pointedCone (polarPointedCone B K)

/-- **Negating a set negates its polar cone.** For every set $K \subseteq E$,
$(-K)^\circ = -(K^\circ)$.

With the bipolar theorem, this makes the passage to the dual cone $K^* = -K^\circ$ an involution
on the nonempty closed convex cones (`ConvexAnalysis.neg_polarCone_neg_polarCone`). -/
theorem polarCone_neg (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (K : Set E) :
    polarCone B (-K) = -(polarCone B K) := by
  ext y
  rw [Set.mem_neg, mem_polarCone, mem_polarCone]
  refine ⟨fun hy u hu => ?_, fun hy x hx => ?_⟩
  · have h := hy (-u) (Set.mem_neg.2 (by rwa [neg_neg]))
    rw [map_neg B u, LinearMap.neg_apply] at h
    rwa [map_neg (B u) y]
  · have h := hy (-x) (Set.mem_neg.1 hx)
    rwa [map_neg B x, LinearMap.neg_apply, map_neg (B x) y, neg_neg] at h

/-- The dual cone $-K^\circ$ of every set $K$ is invariant under positive dilation:
$a(-K^\circ) = -K^\circ$ for every $a > 0$. -/
theorem smul_neg_polarCone (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (K : Set E) (a : ℝ) (ha : 0 < a) :
    a • (-(polarCone B K)) = -(polarCone B K) := by
  rw [← polarCone_neg]
  exact smul_polarCone B (-K) a ha

/-- The origin of $F$ lies in the dual cone $-K^\circ$ of every set $K$. -/
theorem zero_mem_neg_polarCone (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (K : Set E) :
    (0 : F) ∈ -(polarCone B K) := by
  rw [Set.mem_neg, neg_zero, mem_polarCone]
  exact fun x _ => le_of_eq (map_zero (B x))

/-- The dual cone $-K^\circ$ of every set $K$ is nonempty. -/
theorem neg_polarCone_nonempty (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (K : Set E) :
    (-(polarCone B K)).Nonempty := ⟨0, zero_mem_neg_polarCone B K⟩

/-- The dual cone $-K^\circ$ of every set $K$ is convex. -/
theorem convex_neg_polarCone (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (K : Set E) :
    Convex ℝ (-(polarCone B K)) := (convex_polarCone B K).neg

/-! ### Bridges to Mathlib -/

/-- **Mathlib's dual cone is the inner one.** `PointedCone.dual B s` is $\{y \mid \langle x, y
\rangle \ge 0 \text{ for all } x \in s\}$. Therefore the polar cone $K^\circ$, bundled as a
pointed cone, is `PointedCone.dual B (-K)`, the Mathlib dual cone of $-K$. -/
theorem polarPointedCone_eq_dual_neg (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (K : Set E) :
    polarPointedCone B K = PointedCone.dual B (-K) := by
  ext y
  simp only [mem_polarPointedCone, PointedCone.mem_dual, Set.mem_neg]
  constructor
  · intro h x hx
    have hx' := h (-x) hx
    rw [map_neg, LinearMap.neg_apply] at hx'
    linarith
  · intro h x hx
    have hx' := h (x := -x) (by simpa using hx)
    rw [map_neg, LinearMap.neg_apply] at hx'
    linarith

/-- The polar cone of $K$ is the negative of the Mathlib dual cone of $K$: $K^\circ = -K^{\vee}$,
where $K^{\vee} = \{y \mid \langle x, y \rangle \ge 0 \text{ for all } x \in K\}$ is
`PointedCone.dual B K`. -/
theorem polarCone_eq_neg_dual (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (K : Set E) :
    polarCone B K = -(PointedCone.dual B K : Set F) := by
  rw [← coe_polarPointedCone, polarPointedCone_eq_dual_neg]
  exact congrArg _ (PointedCone.dual_neg (p := B) (s := K))

/-- **On balanced sets the polar set is Mathlib's absolute polar.** Let $C \subseteq E$ be balanced,
that is, $tC \subseteq C$ for every scalar $t$ with $|t| \le 1$. Then $C^\circ = \{y \mid
|\langle x, y \rangle| \le 1 \text{ for all } x \in C\}$, which is `LinearMap.polar B C`.
-/
theorem polarSet_eq_polar_of_balanced (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) {C : Set E} (hC : Balanced ℝ C) :
    polarSet B C = B.polar C := by
  ext y
  simp only [mem_polarSet, LinearMap.polar_mem_iff, Real.norm_eq_abs]
  refine ⟨fun h x hx => abs_le.2 ⟨?_, h x hx⟩, fun h x hx => (le_abs_self _).trans (h x hx)⟩
  have hneg : -x ∈ C := by
    have := hC (-1 : ℝ) (by norm_num)
    exact this ⟨x, hx, by simp⟩
  have := h (-x) hneg
  rw [map_neg, LinearMap.neg_apply] at this
  linarith

end Defs

/-!
### The polar cone and the conjugate of an indicator

This computation needs no topology. The indicator of a cone is positively homogeneous, so its
conjugate is again an indicator (`ConvexAnalysis.convexConj_eq_indicatorFn_of_posHomogeneous`), and
the set that it indicates is the polar.
-/

section Indicator

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {K : Set E}

/-- For every set $K \subseteq E$, the set $\{y \in F \mid \langle x, y \rangle \le \delta(x \mid K)
\text{ for all } x \in E\}$ is the polar cone $K^\circ$. This is the set that the conjugate of
the indicator $\delta(\cdot \mid K)$ indicates when $K$ is a cone. -/
@[simp] theorem supportSet_indicatorFn (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (K : Set E) :
    supportSet B (indicatorFn K) = polarCone B K := by
  ext y
  simp only [mem_supportSet, mem_polarCone]
  refine ⟨fun h x hx => ?_, fun h x => ?_⟩
  · have hx' := h x
    rw [indicatorFn_of_mem hx] at hx'
    exact_mod_cast hx'
  · by_cases hx : x ∈ K
    · rw [indicatorFn_of_mem hx]
      exact_mod_cast h x hx
    · rw [indicatorFn_of_notMem hx]
      exact le_top

/-- **The indicator functions of a nonempty cone and of its polar are conjugate.** Let
$K \subseteq E$ be nonempty and closed under multiplication by positive scalars. Then the
conjugate of the indicator function of $K$ is the indicator function of $K^\circ$:
$$\delta^*(\cdot \mid K) = \delta(\cdot \mid K^\circ).$$
This is the third assertion of Theorem 14.1 of [rockafellar1970convex].

Convexity of $K$ is not needed. The proof combines
`ConvexAnalysis.convexConj_eq_indicatorFn_of_posHomogeneous` with
`ConvexAnalysis.supportSet_indicatorFn`. The conjugacy in the other direction is
`ConvexAnalysis.convexConj_indicatorFn_polarCone`. -/
theorem convexConj_indicatorFn_eq_indicatorFn_polarCone (hK : IsCone K)
    (hne : K.Nonempty) : convexConj B (indicatorFn K) = indicatorFn (polarCone B K) := by
  obtain ⟨x₀, hx₀⟩ := hne
  rw [← supportSet_indicatorFn]
  exact convexConj_eq_indicatorFn_of_posHomogeneous
    (posHomogeneous_indicatorFn.2 (isCone_iff_smul_eq.1 hK))
    ⟨x₀, by rw [indicatorFn_of_mem hx₀]; simp⟩

/-- **The support function of a nonempty cone is the indicator of its polar.** Let $K \subseteq E$
be nonempty and closed under multiplication by positive scalars. Then $\delta^*(y \mid K) =
\sup_{x \in K} \langle x, y \rangle$ is $0$ for $y \in K^\circ$ and $+\infty$ otherwise. -/
theorem supportFn_eq_indicatorFn_polarCone (hK : IsCone K) (hne : K.Nonempty) :
    supportFn B K = indicatorFn (polarCone B K) := by
  rw [supportFn_eq_convexConj_indicatorFn]
  exact convexConj_indicatorFn_eq_indicatorFn_polarCone hK hne

/-- **The polar cone is the zero sublevel set of the support function.** For every set
$K \subseteq E$,
$$K^\circ = \{y \in F \mid \delta^*(y \mid K) \le 0\}.$$

The set $K$ is arbitrary. This identity turns a theorem that computes a support function into a
theorem that computes a polar. -/
theorem polarCone_eq_setOf_supportFn_le_zero (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (K : Set E) :
    polarCone B K = {y : F | supportFn B K y ≤ 0} := by
  ext y
  exact supportFn_le_zero_iff.symm

end Indicator

/-! ### Closedness of the polar -/

section Closed

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace F] {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} [IsContinuousPairing B.flip] {K C : Set E}

/-- **The polar cone of any set is closed.** Let $F$ carry a topology for which every functional
$\langle x, \cdot \rangle$ is continuous. Then $K^\circ$ is closed for every set
$K \subseteq E$.

With `ConvexAnalysis.polarPointedCone` this is the first assertion of Theorem 14.1 of
[rockafellar1970convex]: $K^\circ$ is a closed convex cone that contains the origin. The proof
writes $K^\circ$ as an intersection of closed half-spaces. -/
theorem isClosed_polarCone : IsClosed (polarCone B K) := by
  have h : polarCone B K = ⋂ x ∈ K, {y : F | B x y ≤ 0} := by ext y; simp [polarCone]
  rw [h]
  exact isClosed_biInter fun x _ => isClosed_le (continuous_pairing B.flip x) continuous_const

/-- **The polar set of any set is closed.** Let $F$ carry a topology for which every functional
$\langle x, \cdot \rangle$ is continuous. Then $C^\circ$ is closed for every set
$C \subseteq E$.

The proof writes $C^\circ$ as an intersection of closed half-spaces. -/
theorem isClosed_polarSet : IsClosed (polarSet B C) := by
  have h : polarSet B C = ⋂ x ∈ C, {y : F | B x y ≤ 1} := by ext y; simp [polarSet]
  rw [h]
  exact isClosed_biInter fun x _ => isClosed_le (continuous_pairing B.flip x) continuous_const

end Closed

section ClosureDomain

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace E] {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} [IsContinuousPairing B]

/-- **The polar cone does not change under closure.** Let $E$ carry a topology for which every
functional $\langle \cdot, y \rangle$ is continuous. Then for every set $K \subseteq E$,
$$(\operatorname{cl} K)^\circ = K^\circ.$$
-/
theorem polarCone_closure (K : Set E) : polarCone (B := B) (closure K) = polarCone B K := by
  refine subset_antisymm (polarCone_anti subset_closure) fun y hy x hx => ?_
  exact closure_minimal (fun z hz => hy z hz)
    (isClosed_le (continuous_pairing B y) continuous_const) hx

/-- **The polar set does not change under closure.** Let $E$ carry a topology for which every
functional $\langle \cdot, y \rangle$ is continuous. Then for every set $C \subseteq E$,
$$(\operatorname{cl} C)^\circ = C^\circ.$$

This is the companion of `ConvexAnalysis.polarCone_closure`. -/
theorem polarSet_closure (C : Set E) : polarSet (B := B) (closure C) = polarSet B C := by
  refine subset_antisymm (polarSet_anti subset_closure) fun y hy x hx => ?_
  exact closure_minimal (fun z hz => hy z hz)
    (isClosed_le (continuous_pairing B y) continuous_const) hx

end ClosureDomain

/-!
### The bipolar theorem

Separation supplies the only nontrivial inclusion.
-/

section BipolarCone

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} [IsCompatiblePairing B] {K : Set E}

/-- The **bipolar theorem**. Let $E$ be a locally convex real topological vector space, and let the
pairing be compatible with the topology of $E$: every functional $\langle \cdot, y \rangle$ is
continuous, and every continuous linear functional on $E$ has this form. Let $K \subseteq E$ be
a nonempty convex set that is closed under multiplication by positive scalars. Then
$$K^{\circ\circ} = \operatorname{cl} K,$$
where the second polar is taken with respect to the flipped pairing. This is the second
assertion of Theorem 14.1 of [rockafellar1970convex].

The proof separates a point outside $\operatorname{cl} K$ strongly from $\operatorname{cl} K$ by
a continuous linear functional. Because $\operatorname{cl} K$ is a nonempty cone, this
functional is at most $0$ on it, so the point $y$ that represents it lies in $K^\circ$ and
detects the point. -/
theorem polarCone_polarCone (hconv : Convex ℝ K) (hcone : IsCone K)
    (hne : K.Nonempty) :
    polarCone B.flip (polarCone B K) = closure K := by
  have hmem : ∀ ⦃a : ℝ⦄, 0 < a → ∀ ⦃x⦄, x ∈ K → a • x ∈ K :=
    fun _ ha _ hx => (smul_mem_iff_of_isCone hcone ha).2 hx
  refine subset_antisymm (fun x hx => ?_) ?_
  · by_contra hcon
    obtain ⟨f, u, hfK, hfx⟩ :=
      geometric_hahn_banach_closed_point hconv.closure isClosed_closure hcon
    have hbdd : ∀ z ∈ closure K, f z ≤ u := fun z hz => (hfK z hz).le
    have hle : ∀ z ∈ K, f z ≤ 0 := fun z hz =>
      le_zero_of_isCone_of_forall_le (smul_mem_closure_of_isCone hmem) hbdd (subset_closure hz)
    have hu : 0 ≤ u := nonneg_of_isCone_of_forall_le (smul_mem_closure_of_isCone hmem) hbdd
      (hne.mono subset_closure)
    obtain ⟨y, hy⟩ := exists_pairing_eq B f
    have hyK : y ∈ polarCone B K := fun z hz => hy z ▸ hle z hz
    have := hx y hyK
    rw [LinearMap.flip_apply, ← hy x] at this
    linarith
  · exact closure_minimal (subset_polarCone_polarCone B K) (isClosed_polarCone (B := B.flip))

/-- **For a nonempty closed convex cone the bipolar is the cone itself.** Let $E$ be a locally
convex real topological vector space with a compatible pairing, and let $K \subseteq E$ be a
nonempty closed convex set that is closed under multiplication by positive scalars. Then
$K^{\circ\circ} = K$. -/
theorem polarCone_polarCone_of_isClosed (hconv : Convex ℝ K)
    (hcone : IsCone K) (hne : K.Nonempty) (hcl : IsClosed K) :
    polarCone B.flip (polarCone B K) = K :=
  (polarCone_polarCone hconv hcone hne).trans hcl.closure_eq

/-- For a closed pointed cone $K$ in a locally convex real topological vector space $E$ with a
compatible pairing, $K^{\circ\circ} = K$. The bundling supplies the three hypotheses of
`ConvexAnalysis.polarCone_polarCone_of_isClosed` other than closedness. -/
theorem polarCone_polarCone_pointedCone (K : PointedCone ℝ E) (hcl : IsClosed (K : Set E)) :
    polarCone B.flip (polarCone B (K : Set E)) = (K : Set E) :=
  polarCone_polarCone_of_isClosed (K : ConvexCone ℝ E).convex
    (isCone_coe_pointedCone K) ⟨0, K.zero_mem⟩ hcl

/-- For a pointed cone $K$ in a locally convex real topological vector space $E$ with a compatible
pairing, $K^{\circ\circ} = \operatorname{cl} K$. -/
theorem polarCone_polarCone_pointedCone_eq_closure (K : PointedCone ℝ E) :
    polarCone B.flip (polarCone B (K : Set E)) = closure (K : Set E) :=
  polarCone_polarCone (K : ConvexCone ℝ E).convex (isCone_coe_pointedCone K) ⟨0, K.zero_mem⟩

/-- **The bipolar theorem for dual cones.** Let $E$ be a locally convex real topological vector
space with a compatible pairing, and let $K \subseteq E$ be a nonempty closed convex set that is
closed under multiplication by positive scalars. Let $K^* = -K^\circ$ be the dual cone of $K$,
and take the dual cone of a subset of $F$ with respect to the flipped pairing. Then
$$K^{**} = K.$$
-/
theorem neg_polarCone_neg_polarCone (hconv : Convex ℝ K)
    (hcone : IsCone K) (hne : K.Nonempty) (hcl : IsClosed K) :
    -(polarCone B.flip (-(polarCone B K))) = K := by
  rw [polarCone_neg, neg_neg, polarCone_polarCone_of_isClosed hconv hcone hne hcl]

/-- For a closed pointed cone $K$ in a locally convex real topological vector space $E$ with a
compatible pairing, the dual cone of the dual cone $K^* = -K^\circ$ is $K$: $K^{**} = K$. -/
theorem neg_polarCone_neg_polarCone_pointedCone (K : PointedCone ℝ E)
    (hcl : IsClosed (K : Set E)) :
    -(polarCone B.flip (-(polarCone B (K : Set E)))) = (K : Set E) :=
  neg_polarCone_neg_polarCone (K : ConvexCone ℝ E).convex (isCone_coe_pointedCone K)
    ⟨0, K.zero_mem⟩ hcl

/-- **The indicator of the polar cone conjugates back to the indicator of the cone.** Let $E$ be a
locally convex real topological vector space with a compatible pairing, and let $K \subseteq E$
be a nonempty closed convex set that is closed under multiplication by positive scalars. Then
the conjugate of $\delta(\cdot \mid K^\circ)$ with respect to the flipped pairing is
$\delta(\cdot \mid K)$. -/
theorem convexConj_indicatorFn_polarCone (hconv : Convex ℝ K)
    (hcone : IsCone K) (hne : K.Nonempty) (hcl : IsClosed K) :
    convexConj B.flip (indicatorFn (polarCone B K)) = indicatorFn K := by
  rw [convexConj_indicatorFn_eq_indicatorFn_polarCone (B := B.flip) (isCone_polarCone B K)
      (polarCone_nonempty B K),
    polarCone_polarCone_of_isClosed hconv hcone hne hcl]

/-- For a closed pointed cone $K$ in a locally convex real topological vector space $E$ with a
compatible pairing, the conjugate of $\delta(\cdot \mid K^\circ)$ with respect to the flipped
pairing is $\delta(\cdot \mid K)$. -/
theorem convexConj_indicatorFn_polarCone_pointedCone (K : PointedCone ℝ E)
    (hcl : IsClosed (K : Set E)) :
    convexConj B.flip (indicatorFn (polarCone B (K : Set E))) = indicatorFn (K : Set E) :=
  convexConj_indicatorFn_polarCone (K : ConvexCone ℝ E).convex (isCone_coe_pointedCone K)
    ⟨0, K.zero_mem⟩ hcl

end BipolarCone

/-!
### The bipolar of a set containing the origin

For a closed convex set $C$ that contains the origin, $C^{\circ\circ} = C$. The separation argument
is the same as for cones, with the constant normalized to $1$ instead of $0$.
-/

section BipolarSet

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} [IsCompatiblePairing B] {C : Set E}

/-- **The bipolar of a closed convex set that contains the origin.** Let $E$ be a locally convex
real topological vector space, and let the pairing be compatible with the topology of $E$. Let
$C \subseteq E$ be a closed convex set that contains the origin. Then
$$C^{\circ\circ} = C,$$
where the second polar is the polar set with respect to the flipped pairing. This is part of
Theorem 14.5 of [rockafellar1970convex].

That $C^\circ$ is again a closed convex set that contains the origin is
`ConvexAnalysis.isClosed_polarSet`, `ConvexAnalysis.convex_polarSet` and
`ConvexAnalysis.zero_mem_polarSet`. In the proof, containment of the origin makes the separating
constant positive, so that the separating functional can be rescaled to have the value $1$. -/
theorem polarSet_polarSet (hconv : Convex ℝ C) (hcl : IsClosed C) (h0 : (0 : E) ∈ C) :
    polarSet B.flip (polarSet B C) = C := by
  refine subset_antisymm (fun x hx => ?_) (subset_polarSet_polarSet B C)
  by_contra hcon
  obtain ⟨f, u, hfC, hfx⟩ := geometric_hahn_banach_closed_point hconv hcl hcon
  have hu : 0 < u := by simpa using hfC 0 h0
  obtain ⟨y, hy⟩ := exists_pairing_eq B f
  have hyC : u⁻¹ • y ∈ polarSet B C := by
    intro z hz
    rw [map_smul, smul_eq_mul, ← hy z]
    rw [inv_mul_le_iff₀ hu, mul_one]
    exact (hfC z hz).le
  have hxle := hx _ hyC
  rw [LinearMap.flip_apply, map_smul, smul_eq_mul, ← hy x, inv_mul_le_iff₀ hu, mul_one] at hxle
  linarith

/-- In a locally convex real topological vector space with a compatible pairing, a closed convex set
that contains the origin is a closed element of the bipolar set operator
`ConvexAnalysis.polarSetClosure`. -/
theorem isClosed_polarSetClosure_of_isClosed (hconv : Convex ℝ C) (hcl : IsClosed C)
    (h0 : (0 : E) ∈ C) : (polarSetClosure B).IsClosed C :=
  isClosed_polarSetClosure_iff.2 (polarSet_polarSet hconv hcl h0)

end BipolarSet

/-! ### Examples -/

section Examples

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ}

/-- **The polar cone of a subspace is its annihilator.** For a subspace $M$ of $E$, $M^\circ$ is the
set of $y \in F$ for which the functional $\langle \cdot, y \rangle$ vanishes on $M$. This is
the orthogonally complementary subspace of [rockafellar1970convex] §14.

In Lean the annihilator is `M.dualAnnihilator` pulled back along `B.flip`, which sends $y$ to
the functional $\langle \cdot, y \rangle$. -/
theorem polarCone_coe_submodule (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (M : Submodule ℝ E) :
    polarCone B (M : Set E) = (M.dualAnnihilator.comap B.flip : Set F) := by
  ext y
  simp only [mem_polarCone, SetLike.mem_coe, Submodule.mem_comap, Submodule.mem_dualAnnihilator,
    LinearMap.flip_apply]
  refine ⟨fun h x hx => le_antisymm (h x hx) ?_, fun h x hx => (h x hx).le⟩
  have := h (-x) (M.neg_mem hx)
  rw [map_neg, LinearMap.neg_apply] at this
  linarith

/-- For a subspace $M$ of $E$, $M^\circ = \{y \in F \mid \langle x, y \rangle = 0 \text{ for all } x
\in M\}$. -/
theorem polarCone_coe_submodule' (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (M : Submodule ℝ E) :
    polarCone B (M : Set E) = {y : F | ∀ x ∈ M, B x y = 0} := by
  rw [polarCone_coe_submodule]
  ext y
  simp

/-- The **polar subspace** $M^\perp$ of a subspace $M$ of $E$: the subspace of $F$ consisting of the
$y$ for which the functional $\langle \cdot, y \rangle$ vanishes on $M$.

It is `M.dualAnnihilator` pulled back along `B.flip`. Its underlying set is the polar cone
$M^\circ$ (`ConvexAnalysis.polarCone_coe_submodule`). -/
noncomputable def polarSubmodule (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (M : Submodule ℝ E) : Submodule ℝ F :=
  M.dualAnnihilator.comap B.flip

/-- The underlying set of the polar subspace of $M$ is the polar cone $M^\circ$. -/
@[simp] theorem coe_polarSubmodule (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (M : Submodule ℝ E) :
    (polarSubmodule B M : Set F) = polarCone B (M : Set E) :=
  (polarCone_coe_submodule B M).symm

/-- **The polar cone does not change under the generated cone.** For every set $S \subseteq E$, the
polar cone of the pointed convex cone generated by $S$ (the set of nonnegative linear
combinations of points of $S$) is $S^\circ$. -/
@[simp] theorem polarCone_hull (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (S : Set E) :
    polarCone B (PointedCone.hull ℝ S : Set E) = polarCone B S := by
  rw [polarCone_eq_neg_dual, polarCone_eq_neg_dual, PointedCone.dual_hull]

/-- **The polar of a generated cone.** For a family $(a_i)_{i \in I}$ of points of $E$, the polar
cone of the pointed convex cone generated by the $a_i$ is the solution set of the homogeneous
inequalities
$$\langle a_i, y \rangle \le 0 \quad \text{for all } i \in I.$$
-/
theorem polarCone_hull_range {ι : Sort*} (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (a : ι → E) :
    polarCone B (PointedCone.hull ℝ (Set.range a) : Set E) = {y : F | ∀ i, B (a i) y ≤ 0} := by
  rw [polarCone_hull]
  ext y
  simp only [mem_polarCone, Set.mem_range, Set.mem_ofPred]
  exact ⟨fun h i => h (a i) ⟨i, rfl⟩, fun h _ ⟨i, hi⟩ => hi ▸ h i⟩

end Examples

/-!
### Partial affine functions

A **partial affine function** is a proper convex function whose effective domain is an affine set
and which is affine on it. Every such function has the form $\delta(\cdot \mid a + L) + \langle
\cdot, b \rangle + \alpha$ for a subspace $L$. Conjugacy exchanges $L$ with its polar subspace, $a$
with $b$, and $\alpha$ with $-\alpha - \langle a, b \rangle$, so partial affine functions, like
subspaces, come in dual pairs. The formula is the conjugacy rule for
$h(Ax) + \langle x, b \rangle + \alpha$ at $h = \delta(\cdot \mid L)$, together with
`ConvexAnalysis.convexConj_indicatorFn_eq_indicatorFn_polarCone`.
-/

section PartialAffine

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

/-- A **partial affine function** in the normal form of [rockafellar1970convex]: for a subspace $L$
of $E$, vectors $a \in E$ and $b \in F$, and a real number $\alpha$, it is the function
$$x \mapsto \delta(x \mid a + L) + \langle x, b \rangle + \alpha,$$
which equals $\langle x, b \rangle + \alpha$ on the affine set $a + L$ and $+\infty$ elsewhere. -/
noncomputable def partialAffineFn (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (L : Submodule ℝ E) (a : E) (b : F)
    (α : ℝ) : E → EReal :=
  fun x => indicatorFn (a +ᵥ (L : Set E)) x + ((B x b : ℝ) : EReal) + (α : EReal)

/-- The partial affine function with data $L, a, b, \alpha$ takes at $x$ the value $\delta(x \mid
a + L) + \langle x, b \rangle + \alpha$. -/
theorem partialAffineFn_apply (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (L : Submodule ℝ E) (a : E) (b : F)
    (α : ℝ) (x : E) : partialAffineFn B L a b α x
      = indicatorFn (a +ᵥ (L : Set E)) x + ((B x b : ℝ) : EReal) + (α : EReal) := rfl

/-- **The conjugate of a partial affine function.** Let $L$ be a subspace of $E$, let $a \in E$,
$b \in F$ and $\alpha \in \mathbb{R}$. Then
$$\bigl(\delta(\cdot \mid a + L) + \langle \cdot, b \rangle + \alpha\bigr)^* = \delta(\cdot \mid
  b + L^\perp) + \langle a, \cdot \rangle - \alpha - \langle a, b \rangle,$$
where $L^\perp \subseteq F$ is the polar subspace of $L$.

The right side is `ConvexAnalysis.partialAffineFn` for the flipped pairing, with the subspace
`ConvexAnalysis.polarSubmodule B L`, the base point $b$, the linear term $a$ and the constant
$-\alpha - \langle a, b \rangle$. -/
theorem convexConj_partialAffineFn (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (L : Submodule ℝ E) (a : E) (b : F)
    (α : ℝ) :
    convexConj B (partialAffineFn B L a b α)
      = partialAffineFn B.flip (polarSubmodule B L) b a (-α - B a b) := by
  have hcone : convexConj B (indicatorFn (L : Set E)) = indicatorFn (polarCone B (L : Set E)) :=
    convexConj_indicatorFn_eq_indicatorFn_polarCone (isCone_coe_submodule L)
      ⟨0, L.zero_mem⟩
  have hfun : partialAffineFn B L a b α
      = fun x : E => indicatorFn (L : Set E) (x - a) + ((B x b : ℝ) : EReal) + (α : EReal) := by
    funext x
    rw [partialAffineFn_apply, indicatorFn_vadd]
  funext y
  have e : convexConj B (fun x : E => indicatorFn (L : Set E) (x - a) + ((B x b : ℝ) : EReal)
        + (α : EReal)) y
      = convexConj B (indicatorFn (L : Set E)) (y - b) + ((B a y : ℝ) : EReal)
        + ((-α - B a b : ℝ) : EReal) :=
    convexConj_comp_affine (B := B) (B' := B) (LinearEquiv.refl ℝ E) (LinearEquiv.refl ℝ F)
      (fun _ _ => rfl) (indicatorFn (L : Set E)) a b α y
  rw [hfun, e, hcone, partialAffineFn_apply, indicatorFn_vadd, coe_polarSubmodule,
    LinearMap.flip_apply]

end PartialAffine

section ExamplesTopology

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} [IsCompatiblePairing B]

/-- **The polar of a system of homogeneous inequalities.** Let $E$ be a locally convex real
topological vector space, and let the pairing be compatible with the topology of $E$. For a
family $(a_i)_{i \in I}$ of points of $E$, the polar (with respect to the flipped pairing) of
the solution set $\{y \in F \mid \langle a_i, y \rangle \le 0 \text{ for all } i\}$ is the
closure of the pointed convex cone generated by the $a_i$. -/
theorem polarCone_setOf_forall_le_zero {ι : Sort*} (a : ι → E) :
    polarCone B.flip {y : F | ∀ i, B (a i) y ≤ 0} =
      closure (PointedCone.hull ℝ (Set.range a) : Set E) := by
  rw [← polarCone_hull_range B a]
  exact polarCone_polarCone
    ((PointedCone.hull ℝ (Set.range a) : ConvexCone ℝ E)).convex
    (isCone_coe_pointedCone _) ⟨0, (PointedCone.hull ℝ (Set.range a)).zero_mem⟩

end ExamplesTopology

/-!
### The nonnegative orthant

An example of [rockafellar1970convex] §14, for the Euclidean space $\mathbb{R}^I$ paired with itself
by the inner product.
-/

section Orthant

variable {ι : Type*} [Fintype ι]

/-- **The polar of the nonnegative orthant is the nonpositive orthant.** Let $I$ be a finite index
set, and pair the Euclidean space $\mathbb{R}^I$ with itself by the inner product. Then
$$\{x \in \mathbb{R}^I \mid x_i \ge 0 \text{ for all } i\}^\circ = \{y \in \mathbb{R}^I \mid y_i
  \le 0 \text{ for all } i\}.$$
-/
theorem polarCone_nonnegOrthant :
    polarCone (innerₗ (EuclideanSpace ℝ ι)) {x : EuclideanSpace ℝ ι | ∀ i, 0 ≤ x i} =
      {y : EuclideanSpace ℝ ι | ∀ i, y i ≤ 0} := by
  classical
  ext y
  simp only [mem_polarCone, Set.mem_ofPred, innerₗ_apply_apply, PiLp.inner_apply,
    RCLike.inner_apply, starRingEnd_apply, star_trivial]
  constructor
  · intro h i
    have hmem : ∀ j, (0 : ℝ) ≤ (EuclideanSpace.single i (1 : ℝ) : EuclideanSpace ℝ ι) j := by
      intro j
      simp only [PiLp.single_apply]
      split <;> norm_num
    have h' := h _ hmem
    simpa using h'
  · intro h x hx
    refine Finset.sum_nonpos fun i _ => ?_
    have hi := mul_le_mul_of_nonneg_right (h i) (hx i)
    simpa using hi

end Orthant

/-!
### Transport along a linear map

Both rules are needed wherever a cone in a product space is read in $\mathbb{R}^k$. The polar needs
a pair of maps that is adjoint for the two pairings; the generated cone needs only linearity.
-/

section LinearTransport

variable {E F G H : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [AddCommGroup G] [Module ℝ G] [AddCommGroup H] [Module ℝ H]

/-- **Polarity transports along an adjoint pair of isomorphisms.** Let $B$ pair $E$ with $F$ and
$B'$ pair $G$ with $H$. Let $A : E \to G$ and $A' : F \to H$ be linear isomorphisms with
$B'(Ap, A'q) = B(p, q)$ for all $p \in E$ and $q \in F$. Then for every set $S \subseteq E$, the
polar cone of $A(S)$ with respect to $B'$ is the image under $A'$ of the polar cone of $S$ with
respect to $B$:
$$(A S)^\circ = A' (S^\circ).$$
-/
theorem polarCone_image_of_pairing_eq {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {B' : G →ₗ[ℝ] H →ₗ[ℝ] ℝ}
    (A : E ≃ₗ[ℝ] G) (A' : F ≃ₗ[ℝ] H) (hA : ∀ p q, B' (A p) (A' q) = B p q) (S : Set E) :
    polarCone B' (A '' S) = A' '' polarCone B S := by
  ext w
  constructor
  · intro hw
    refine ⟨A'.symm w, fun p hp => ?_, A'.apply_symm_apply w⟩
    have hkey := hA p (A'.symm w)
    rw [A'.apply_symm_apply] at hkey
    rw [← hkey]
    exact hw (A p) ⟨p, hp, rfl⟩
  · rintro ⟨v, hv, rfl⟩ z ⟨p, hp, rfl⟩
    rw [hA p v]
    exact hv p hp

/-- **The generated cone transports along a linear map.** Let $A : E \to G$ be a linear map and
$S \subseteq E$. Then the pointed convex cone generated by $A(S)$ is the image under $A$ of the
pointed convex cone generated by $S$.

This is `Submodule.map_span` over the semiring of nonnegative reals, restated for the underlying
sets. -/
theorem coe_hull_image (A : E →ₗ[ℝ] G) (S : Set E) :
    (PointedCone.hull ℝ (A '' S) : Set G) = A '' (PointedCone.hull ℝ S : Set E) := by
  have h : PointedCone.hull ℝ (A '' S) = (PointedCone.hull ℝ S).map A :=
    (Submodule.map_span (A : E →ₗ[{c : ℝ // 0 ≤ c}] G) S).symm
  rw [h, PointedCone.coe_map]

end LinearTransport

end ConvexAnalysis
