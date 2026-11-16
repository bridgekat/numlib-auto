/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Convex.Cone.Closure
import Mathlib.Analysis.Normed.Affine.AsymptoticCone
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Geometry.Convex.Cone.Pointed

/-!
# Recession cones and lineality spaces

Let $E$ be a real vector space and $C \subseteq E$. The **recession cone** $0^+C$ is the set of
$y \in E$ such that $x + ay \in C$ for every $x \in C$ and every $a \ge 0$: the directions in which
$C$ recedes. The **lineality space** $\operatorname{lin} C = 0^+C \cap (-0^+C)$ is the largest
subspace inside $0^+C$, the set of directions in which $C$ is linear. The presentation follows §8 of
[rockafellar1970convex]. The last result is the recession hypothesis of Helly's theorem, from §21 of
[rockafellar1970convex].

Most of the theory is algebraic. The closedness of $0^+C$ and its description by limits of sequences
need only a real topological vector space. Finite dimension is used only in the criteria for
boundedness.

## Main definitions

* `ConvexAnalysis.recessionCone`: the recession cone $0^+C$.
* `ConvexAnalysis.recessionPointedCone`: $0^+C$ as a `PointedCone ℝ E`; for every set $C$ it is a
  convex cone that contains $0$.
* `ConvexAnalysis.linealitySpace`: the lineality space $\operatorname{lin} C = 0^+C \cap (-0^+C)$.
* `ConvexAnalysis.linealitySubmodule`: the lineality space as a submodule of $E$.
* `ConvexAnalysis.lineality`: the dimension of $\operatorname{lin} C$.

## Main results

* `ConvexAnalysis.recessionCone_eq_add_subset`: for convex $C$,
  $0^+C = \{y \mid C + y \subseteq C\}$.
* `ConvexAnalysis.eq_add_inter_of_isCompl`: if $L'$ is a complement of $L = \operatorname{lin} C$,
  then $C = L + (C \cap L')$.
* `ConvexAnalysis.recessionCone_coe_affineSubspace`: the recession cone of a nonempty affine set is
  the subspace parallel to it.
* `ConvexAnalysis.recessionCone_setOf_forall_le`: the recession cone of the nonempty solution set of
  a system of weak linear inequalities $b_i(x) \ge \beta_i$ is the solution set of the homogeneous
  system $b_i(y) \ge 0$.
* `ConvexAnalysis.recessionCone_prod`, `ConvexAnalysis.recessionCone_pi`: the recession cone of a
  product of nonempty sets is the product of the recession cones.
* `ConvexAnalysis.isClosed_recessionCone`: $0^+C$ is closed when $C$ is closed; no convexity and no
  nonemptiness are needed.
* `ConvexAnalysis.mem_recessionCone_iff_exists_tendsto`: for a nonempty closed convex $C$, $0^+C$ is
  the set of limits of sequences $\lambda_i x_i$ with $x_i \in C$, $\lambda_i > 0$ and
  $\lambda_i \to 0$ (Theorem 8.2 of [rockafellar1970convex]).
* `ConvexAnalysis.mem_recessionCone_of_exists_ray`: if a closed convex set $C$ contains one
  half-line in the direction $y$, then $y \in 0^+C$ (Theorem 8.3 of [rockafellar1970convex]).
* `ConvexAnalysis.recessionCone_iInter`, `ConvexAnalysis.recessionCone_preimage`: the recession cone
  of an intersection of closed convex sets with a common point is the intersection of the recession
  cones, and the recession cone of a nonempty preimage $A^{-1}D$ of a closed convex set $D$ is
  $A^{-1}(0^+D)$.
* `ConvexAnalysis.isBounded_iff_recessionCone_eq_zero`: in finite dimension, a nonempty closed
  convex set $C$ is bounded if and only if $0^+C = \{0\}$.
* `ConvexAnalysis.isBounded_inter_of_direction_eq`: if an affine set meets a closed convex set $C$
  in a nonempty bounded set, then every parallel affine set meets $C$ in a bounded set.
* `ConvexAnalysis.iInter_recessionCone_eq_zero_iff_exists_isBounded`: for closed convex sets of
  which every finite subfamily has a common point, the recession cones have only $0$ in common if
  and only if some finite subfamily has a bounded intersection.

## Implementation notes

* The recession cone of the empty set is the whole space. For this reason the results on products,
  intersections and preimages assume that the sets are nonempty.
* Mathlib's `asymptoticCone ℝ C` is not $0^+C$: it is always closed, and it is empty for
  $C = \emptyset$. For a nonempty convex $C$ it is $0^+(\operatorname{cl} C)$
  (`ConvexAnalysis.recessionCone_closure_eq_asymptoticCone`), so the two agree for nonempty closed
  convex sets. The recession cone $0^+C$ is defined algebraically, so it is available where $E$ has
  no topology.
-/

open Bornology Filter Pointwise Set Topology

namespace ConvexAnalysis

/-! ### The definitions and their algebraic structure -/

section Defs

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {C : Set E} {x y z : E} {a : ℝ}

/-- The **recession cone** $0^+C$ of a set $C \subseteq E$ is the set of $y \in E$ such that
$x + ay \in C$ for every $x \in C$ and every real $a \ge 0$.

A direction of recession in the classical sense is a nonzero element of $0^+C$. The set $0^+C$
also contains $y = 0$, and this makes it a cone. For $C = \emptyset$ the condition is vacuous,
so $0^+\emptyset = E$. -/
def recessionCone (C : Set E) : Set E := {y | ∀ x ∈ C, ∀ a : ℝ, 0 ≤ a → x + a • y ∈ C}

/-- Membership in the recession cone: $y \in 0^+C$ if and only if $x + ay \in C$ for every $x \in C$
and every $a \ge 0$. -/
theorem mem_recessionCone : y ∈ recessionCone C ↔ ∀ x ∈ C, ∀ a : ℝ, 0 ≤ a → x + a • y ∈ C :=
  Iff.rfl

/-- If $y \in 0^+C$, $x \in C$ and $a \ge 0$, then $x + ay \in C$. -/
theorem add_smul_mem_of_mem_recessionCone (hy : y ∈ recessionCone C) (hx : x ∈ C) (ha : 0 ≤ a) :
    x + a • y ∈ C := hy x hx a ha

/-- If $y \in 0^+C$ and $x \in C$, then $x + y \in C$. -/
theorem add_mem_of_mem_recessionCone (hy : y ∈ recessionCone C) (hx : x ∈ C) : x + y ∈ C := by
  simpa using hy x hx 1 zero_le_one

/-- The origin lies in the recession cone of every set. -/
@[simp]
theorem zero_mem_recessionCone (C : Set E) : (0 : E) ∈ recessionCone C := fun x hx _ _ => by
  simpa using hx

/-- The recession cone is closed under multiplication by scalars $a \ge 0$. -/
theorem smul_mem_recessionCone (ha : 0 ≤ a) (hy : y ∈ recessionCone C) :
    a • y ∈ recessionCone C := fun x hx b hb => by
  rw [smul_smul]
  exact hy x hx (b * a) (mul_nonneg hb ha)

/-- The recession cone is closed under addition: if $y, z \in 0^+C$, then $y + z \in 0^+C$. -/
theorem add_mem_recessionCone (hy : y ∈ recessionCone C) (hz : z ∈ recessionCone C) :
    y + z ∈ recessionCone C := fun x hx a ha => by
  rw [smul_add, ← add_assoc]
  exact hz _ (hy x hx a ha) a ha

/-- The recession cone $0^+C$ as a Mathlib `PointedCone ℝ E`: for every set $C$, $0^+C$ is a convex
cone that contains the origin.

No hypothesis on $C$ is needed. Convexity of $C$ is used only in
`ConvexAnalysis.recessionCone_eq_add_subset`, which tests the recession condition with a single
step. -/
def recessionPointedCone (C : Set E) : PointedCone ℝ E where
  carrier := recessionCone C
  zero_mem' := zero_mem_recessionCone C
  add_mem' := add_mem_recessionCone
  smul_mem' c _ hy := smul_mem_recessionCone c.2 hy

/-- The underlying set of `ConvexAnalysis.recessionPointedCone C` is $0^+C$. -/
@[simp]
theorem coe_recessionPointedCone (C : Set E) :
    (recessionPointedCone C : Set E) = recessionCone C := rfl

/-- Membership in `ConvexAnalysis.recessionPointedCone C` is membership in $0^+C$. -/
@[simp]
theorem mem_recessionPointedCone : y ∈ recessionPointedCone C ↔ y ∈ recessionCone C := Iff.rfl

/-- The recession cone of every set is convex. -/
theorem convex_recessionCone (C : Set E) : Convex ℝ (recessionCone C) :=
  ((recessionPointedCone C : ConvexCone ℝ E)).convex

/-- The recession cone of the empty set is the whole space, because the condition is vacuous. -/
@[simp]
theorem recessionCone_empty : recessionCone (∅ : Set E) = univ := by
  ext y; simp [recessionCone]

/-- The recession cone of the whole space is the whole space. -/
@[simp]
theorem recessionCone_univ : recessionCone (univ : Set E) = univ := by
  ext y; simp [recessionCone]

/-- The recession cone of a singleton $\{x\}$ is $\{0\}$. -/
@[simp]
theorem recessionCone_singleton (x : E) : recessionCone ({x} : Set E) = {0} := by
  ext y
  refine ⟨fun hy => ?_, ?_⟩
  · have h : x + (1 : ℝ) • y ∈ ({x} : Set E) := hy x rfl 1 zero_le_one
    rw [one_smul] at h
    simpa using h
  · rintro rfl
    exact zero_mem_recessionCone _

/-- The recession cone is an intersection of preimages of $C$:
$$0^+C = \bigcap_{x \in C} \bigcap_{a \ge 0} \{y \mid x + ay \in C\}.$$

This is why $0^+C$ is closed when $C$ is closed (`ConvexAnalysis.isClosed_recessionCone`). For
$a > 0$ the set $\{y \mid x + ay \in C\}$ is $a^{-1}(C - x)$, the form that the argument of
[rockafellar1970convex] uses. -/
theorem recessionCone_eq_iInter (C : Set E) :
    recessionCone C = ⋂ x ∈ C, ⋂ a ∈ Ici (0 : ℝ), (fun y => x + a • y) ⁻¹' C := by
  ext y; simp [recessionCone]

/-- For a family of sets $C_i$, $\bigcap_i 0^+C_i \subseteq 0^+\bigl(\bigcap_i C_i\bigr)$. The
reverse inclusion holds for closed convex sets with a common point; it is
`ConvexAnalysis.recessionCone_iInter`. -/
theorem iInter_recessionCone_subset {ι : Sort*} (C : ι → Set E) :
    ⋂ i, recessionCone (C i) ⊆ recessionCone (⋂ i, C i) := by
  intro y hy x hx a ha
  exact mem_iInter.2 fun i => (mem_iInter.1 hy i) x (mem_iInter.1 hx i) a ha

/-- For all sets $C$ and $D$, $0^+C \cap 0^+D \subseteq 0^+(C \cap D)$. -/
theorem inter_recessionCone_subset (C D : Set E) :
    recessionCone C ∩ recessionCone D ⊆ recessionCone (C ∩ D) := by
  rintro y ⟨hyC, hyD⟩ x ⟨hxC, hxD⟩ a ha
  exact ⟨hyC x hxC a ha, hyD x hxD a ha⟩

/-- If $C$ is convex, then $y \in 0^+C$ if and only if $x + y \in C$ for every $x \in C$: it is
enough to test the recession condition at $a = 1$. -/
theorem mem_recessionCone_iff_forall_add_mem (hC : Convex ℝ C) :
    y ∈ recessionCone C ↔ ∀ x ∈ C, x + y ∈ C := by
  refine ⟨fun hy x hx => add_mem_of_mem_recessionCone hy hx, fun hy x hx a ha => ?_⟩
  have key : ∀ n : ℕ, x + (n : ℝ) • y ∈ C := by
    intro n
    induction n with
    | zero => simpa using hx
    | succ n ih =>
      have h := hy _ ih
      have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
      rw [hcast, add_smul, one_smul, ← add_assoc]
      exact h
  obtain ⟨n, hn⟩ := exists_nat_ge a
  rcases ha.eq_or_lt with rfl | ha'
  · simpa using hx
  · have hn0 : (0 : ℝ) < n := ha'.trans_le hn
    have hle : a / (n : ℝ) ≤ 1 := (div_le_one hn0).2 hn
    have h := hC hx (key n) (by linarith : (0 : ℝ) ≤ 1 - a / (n : ℝ))
      (by positivity : (0 : ℝ) ≤ a / (n : ℝ)) (by ring)
    have hcancel : a / (n : ℝ) * (n : ℝ) = a := div_mul_cancel₀ a hn0.ne'
    rwa [smul_add, smul_smul, hcancel, ← add_assoc, ← add_smul,
      show 1 - a / (n : ℝ) + a / (n : ℝ) = 1 by ring, one_smul] at h

omit [Module ℝ E] in
/-- In an additive group, $C + \{y\} \subseteq C$ if and only if $x + y \in C$ for every $x \in C$.
-/
theorem add_singleton_subset_iff_forall (C : Set E) (y : E) :
    C + {y} ⊆ C ↔ ∀ x ∈ C, x + y ∈ C := by
  rw [Set.add_singleton, Set.image_subset_iff]
  exact ⟨fun h x hx => h hx, fun h _ hx => h _ hx⟩

/-- Let $C$ be a convex subset of a real vector space $E$. Then
$$0^+C = \{y \in E \mid C + y \subseteq C\}.$$

The set $C + y$ is written `C + {y}`. -/
theorem recessionCone_eq_add_subset (hC : Convex ℝ C) :
    recessionCone C = {y | C + {y} ⊆ C} := by
  ext y
  rw [mem_recessionCone_iff_forall_add_mem hC]
  exact (add_singleton_subset_iff_forall C y).symm

/-- For every set $C$, $0^+(-C) = -0^+C$. -/
theorem recessionCone_neg (C : Set E) : recessionCone (-C) = -recessionCone C := by
  ext v
  simp only [Set.mem_neg, mem_recessionCone]
  constructor
  · intro h x hx a ha
    have hmem : -(-x) ∈ C := by rw [neg_neg]; exact hx
    have hstep := h (-x) hmem a ha
    have heq : -(-x + a • v) = x + a • (-v) := by module
    rwa [heq] at hstep
  · intro h x hx a ha
    have hstep := h (-x) hx a ha
    have heq : -x + a • (-v) = -(x + a • v) := by module
    rwa [heq] at hstep

/-- The **lineality space** of a set $C$ is
$$\operatorname{lin} C = 0^+C \cap (-0^+C),$$
the set of $y$ such that both $y$ and $-y$ lie in the recession cone of $C$. It is the set of
directions in which $C$ is linear.

It is a subspace (`ConvexAnalysis.linealitySubmodule`), and it is the largest subspace inside
$0^+C$ (`ConvexAnalysis.linealitySubmodule_isGreatest`). -/
def linealitySpace (C : Set E) : Set E := recessionCone C ∩ (-recessionCone C)

/-- $y \in \operatorname{lin} C$ if and only if $y \in 0^+C$ and $-y \in 0^+C$. -/
theorem mem_linealitySpace :
    y ∈ linealitySpace C ↔ y ∈ recessionCone C ∧ -y ∈ recessionCone C := by
  simp [linealitySpace]

/-- The origin lies in the lineality space of every set. -/
@[simp] theorem zero_mem_linealitySpace (C : Set E) : (0 : E) ∈ linealitySpace C :=
  mem_linealitySpace.2 ⟨zero_mem_recessionCone C, by
    rw [neg_zero]; exact zero_mem_recessionCone C⟩

/-- The lineality space is contained in the recession cone. -/
theorem linealitySpace_subset_recessionCone (C : Set E) :
    linealitySpace C ⊆ recessionCone C := inter_subset_left

/-- The lineality space $\operatorname{lin} C$ as a `Submodule ℝ E`: for every set $C$,
$\operatorname{lin} C$ is a linear subspace of $E$.

It is defined as Mathlib's `PointedCone.lineal` of `ConvexAnalysis.recessionPointedCone C`, the
largest submodule inside that cone. -/
noncomputable def linealitySubmodule (C : Set E) : Submodule ℝ E :=
  (recessionPointedCone C).lineal

/-- The underlying set of `ConvexAnalysis.linealitySubmodule C` is $\operatorname{lin} C$. -/
@[simp]
theorem coe_linealitySubmodule (C : Set E) :
    (linealitySubmodule C : Set E) = linealitySpace C := by
  ext y; simp [linealitySubmodule, linealitySpace]

/-- Membership in `ConvexAnalysis.linealitySubmodule C` is membership in $\operatorname{lin} C$. -/
@[simp]
theorem mem_linealitySubmodule : y ∈ linealitySubmodule C ↔ y ∈ linealitySpace C := by
  rw [← SetLike.mem_coe, coe_linealitySubmodule]

/-- The lineality space of every set is convex. -/
theorem convex_linealitySpace (C : Set E) : Convex ℝ (linealitySpace C) := by
  simpa using (linealitySubmodule C).convex

/-- The lineality space is the largest subspace inside the recession cone: it is contained in
$0^+C$, and it contains every subspace $L$ with $L \subseteq 0^+C$. -/
theorem linealitySubmodule_isGreatest (C : Set E) :
    IsGreatest {L : Submodule ℝ E | (L : Set E) ⊆ recessionCone C} (linealitySubmodule C) := by
  constructor
  · have hsub : ((linealitySubmodule C : Submodule ℝ E) : Set E) ⊆ recessionCone C := by
      rw [coe_linealitySubmodule]
      exact linealitySpace_subset_recessionCone C
    exact hsub
  · intro L hL y hy
    exact mem_linealitySubmodule.2 (mem_linealitySpace.2 ⟨hL hy, hL (L.neg_mem hy)⟩)

/-- If $C$ is convex, then $\operatorname{lin} C = \{y \mid C + y = C\}$. For the recession cone the
condition is $C + y \subseteq C$ instead (`ConvexAnalysis.recessionCone_eq_add_subset`). -/
theorem linealitySpace_eq_add_eq (hC : Convex ℝ C) :
    linealitySpace C = {y | C + {y} = C} := by
  ext y
  rw [mem_linealitySpace, mem_recessionCone_iff_forall_add_mem hC,
    mem_recessionCone_iff_forall_add_mem hC]
  constructor
  · rintro ⟨h₁, h₂⟩
    refine Set.Subset.antisymm ((add_singleton_subset_iff_forall C y).2 h₁) fun x hx => ?_
    exact ⟨x + -y, h₂ x hx, y, rfl, by change x + -y + y = x; abel⟩
  · intro h
    have hsub : C + {y} ⊆ C := h.le
    refine ⟨(add_singleton_subset_iff_forall C y).1 hsub, fun x hx => ?_⟩
    obtain ⟨w, hw, v, hv, hwv⟩ := h.ge hx
    have hwv' : w + v = x := hwv
    rw [Set.mem_singleton_iff] at hv
    have hxw : x + -y = w := by rw [← hwv', hv]; abel
    exact hxw ▸ hw

/-- Let $N$ and $M$ be complementary subspaces of $E$ with $N \subseteq \operatorname{lin} C$. Then
$C = N + (C \cap M)$.

This generalizes `ConvexAnalysis.eq_add_inter_of_isCompl`, which takes
$N = \operatorname{lin} C$. The closedness theorem for linear images needs the general form,
with a subspace $N$ of $\operatorname{lin} C \cap \ker A$. No convexity of $C$ is needed. -/
theorem eq_add_inter_of_isCompl_of_le {N M : Submodule ℝ E}
    (hN : (N : Set E) ⊆ linealitySpace C) (h : IsCompl N M) :
    C = (N : Set E) + (C ∩ (M : Set E)) := by
  refine Set.Subset.antisymm (fun x hx => ?_) ?_
  · have hmem : x ∈ N ⊔ M := by rw [h.sup_eq_top]; trivial
    obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.1 hmem
    have hpneg : -p ∈ recessionCone C := (mem_linealitySpace.1 (hN hp)).2
    have hqC : q ∈ C := by
      have hstep := add_mem_of_mem_recessionCone hpneg hx
      simpa [add_comm, add_assoc] using hstep
    exact Set.add_mem_add hp ⟨hqC, hq⟩
  · rintro _ ⟨p, hp, q, ⟨hqC, -⟩, rfl⟩
    have hpC : p ∈ recessionCone C := (mem_linealitySpace.1 (hN hp)).1
    simpa [add_comm] using add_mem_of_mem_recessionCone hpC hqC

/-- Let $C$ be a subset of a real vector space $E$, let $L = \operatorname{lin} C$, and let $L'$ be
a subspace of $E$ complementary to $L$. Then
$$C = L + (C \cap L').$$

The classical statement takes $L' = L^\perp$ in an inner product space; that is a special case.
No convexity of $C$ is needed. The complement is given as `IsCompl (linealitySubmodule C) L`. -/
theorem eq_add_inter_of_isCompl {L : Submodule ℝ E} (h : IsCompl (linealitySubmodule C) L) :
    C = (linealitySubmodule C : Set E) + (C ∩ (L : Set E)) :=
  eq_add_inter_of_isCompl_of_le (coe_linealitySubmodule C).subset h

/-- If $C$ is convex, then $\{z \mid x + cz \in C\}$ is convex for every $x \in E$ and every real
$c$. -/
theorem convex_preimage_affine_smul (hC : Convex ℝ C) (x : E) (c : ℝ) :
    Convex ℝ {z | x + c • z ∈ C} := by
  intro z₁ h₁ z₂ h₂ a b ha hb hab
  have hxab : a • x + b • x = x := by rw [← add_smul, hab, one_smul]
  have heq : x + c • (a • z₁ + b • z₂) = a • (x + c • z₁) + b • (x + c • z₂) := by
    conv_lhs => rw [← hxab]
    simp only [smul_add, smul_smul]
    rw [mul_comm c a, mul_comm c b]
    abel
  change x + c • (a • z₁ + b • z₂) ∈ C
  rw [heq]
  exact hC h₁ h₂ ha hb hab

/-- Let $c > 0$ and $x \in E$. Then the set $\{z \mid x + cz \in C\}$ has the same recession cone as
$C$.

The recession cone does not change under translation, and multiplication by $c > 0$ maps each
ray from the origin onto itself. This change of variables turns the statement that $C$ recedes
in a direction $v$ into a statement about a decreasing family of sets. -/
theorem recessionCone_preimage_affine {c : ℝ} (hc : 0 < c) (x : E) (C : Set E) :
    recessionCone {z | x + c • z ∈ C} = recessionCone C := by
  ext w
  simp only [mem_recessionCone, Set.mem_ofPred_eq]
  constructor
  · intro hw u hu b hb
    have hz : x + c • (c⁻¹ • (u - x)) ∈ C := by
      rw [smul_inv_smul₀ hc.ne']
      simpa using hu
    have hstep := hw _ hz (b / c) (by positivity)
    have heq : x + c • (c⁻¹ • (u - x) + (b / c) • w) = u + b • w := by
      rw [smul_add, smul_inv_smul₀ hc.ne', smul_smul, mul_div_cancel₀ _ hc.ne']
      abel
    rwa [heq] at hstep
  · intro hw z hz a ha
    have hstep := hw _ hz (c * a) (by positivity)
    have heq : x + c • (z + a • w) = x + c • z + (c * a) • w := by
      rw [smul_add, smul_smul]
      abel
    rwa [heq]


/-- The **lineality** of a set $C$ is the dimension of its lineality space $\operatorname{lin} C$.

The dimension is `Module.finrank`, so the lineality is $0$ when $\operatorname{lin} C$ has
infinite dimension. -/
noncomputable def lineality (C : Set E) : ℕ := Module.finrank ℝ (linealitySubmodule C)

end Defs

/-! ### Affine sets and systems of weak linear inequalities -/

section Examples

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- A subspace $M$ is its own recession cone: $0^+M = M$. -/
@[simp] theorem recessionCone_coe_submodule (M : Submodule ℝ E) :
    recessionCone (M : Set E) = M := by
  refine Set.Subset.antisymm (fun y hy => ?_) (fun y hy z hz a ha => ?_)
  · simpa using hy 0 M.zero_mem 1 zero_le_one
  · exact M.add_mem hz (M.smul_mem a hy)

/-- A pointed convex cone $K$ is its own recession cone: $0^+K = K$.

For this reason the sum rule for cones is a special case of the sum rule for sets: for cones,
the recession hypothesis is a hypothesis about the cones themselves. -/
@[simp] theorem recessionCone_coe_pointedCone (K : PointedCone ℝ E) :
    recessionCone (K : Set E) = K := by
  refine Set.Subset.antisymm (fun y hy => ?_) (fun y hy z hz a ha => ?_)
  · simpa using hy 0 K.zero_mem 1 zero_le_one
  · exact K.add_mem hz (K.smul_mem ha hy)

/-- Let $M$ be a nonempty affine subset of a real vector space $E$. Then $0^+M$ is the subspace
parallel to $M$.

The parallel subspace is `AffineSubspace.direction`. -/
theorem recessionCone_coe_affineSubspace {s : AffineSubspace ℝ E} (hs : (s : Set E).Nonempty) :
    recessionCone (s : Set E) = s.direction := by
  obtain ⟨x, hx⟩ := hs
  refine Set.Subset.antisymm (fun y hy => ?_) (fun y hy z hz a ha => ?_)
  · have h : x + (1 : ℝ) • y ∈ s := hy x hx 1 zero_le_one
    rw [one_smul] at h
    simpa using AffineSubspace.vsub_mem_direction h hx
  · have h : a • y ∈ s.direction := s.direction.smul_mem a hy
    simpa [vadd_eq_add, add_comm] using AffineSubspace.vadd_mem_of_mem_direction h hz

/-- Let $M$ be a nonempty affine subset of a real vector space $E$. Then $\operatorname{lin} M$ is
the subspace parallel to $M$.

The parallel subspace is `AffineSubspace.direction`. -/
theorem linealitySpace_coe_affineSubspace {s : AffineSubspace ℝ E} (hs : (s : Set E).Nonempty) :
    linealitySpace (s : Set E) = s.direction := by
  ext y
  rw [mem_linealitySpace, recessionCone_coe_affineSubspace hs]
  exact ⟨fun h => h.1, fun h => ⟨h, s.direction.neg_mem h⟩⟩

/-- Let $E$ be a real vector space, let $(b_i)_{i \in I}$ be a family of linear functionals on $E$,
and let $(\beta_i)_{i \in I}$ be real numbers, where the index set $I$ is arbitrary. If the set
$C = \{x \in E \mid \beta_i \le b_i(x) \text{ for all } i\}$ is nonempty, then
$$0^+C = \{y \in E \mid 0 \le b_i(y) \text{ for all } i\}.$$
-/
theorem recessionCone_setOf_forall_le {ι : Type*} (b : ι → E →ₗ[ℝ] ℝ) (β : ι → ℝ)
    (h : {x : E | ∀ i, β i ≤ b i x}.Nonempty) :
    recessionCone {x : E | ∀ i, β i ≤ b i x} = {y : E | ∀ i, 0 ≤ b i y} := by
  refine Set.Subset.antisymm (fun y hy i => ?_) (fun y hy x hx a ha i => ?_)
  · by_contra hb
    obtain ⟨x, hx⟩ := h
    have hxi : ∀ j, β j ≤ b j x := hx
    have hd : 0 < -(b i y) := by linarith [not_le.1 hb]
    have hnum : (0 : ℝ) ≤ b i x - β i + 1 := by linarith [hxi i]
    have ha : (0 : ℝ) ≤ (b i x - β i + 1) / (-(b i y)) := div_nonneg hnum hd.le
    have hstep : ∀ j, β j ≤ b j (x + ((b i x - β i + 1) / (-(b i y))) • y) := hy x hx _ ha
    have hval := hstep i
    rw [map_add, map_smul, smul_eq_mul] at hval
    have hcancel : (b i x - β i + 1) / (-(b i y)) * (-(b i y)) = b i x - β i + 1 :=
      div_mul_cancel₀ _ hd.ne'
    linarith
  · have hxi : ∀ j, β j ≤ b j x := hx
    have hyi : ∀ j, (0 : ℝ) ≤ b j y := hy
    change β i ≤ b i (x + a • y)
    rw [map_add, map_smul, smul_eq_mul]
    have : (0 : ℝ) ≤ a * b i y := mul_nonneg ha (hyi i)
    linarith [hxi i]

/-- Let $E$ be a real vector space, let $(b_i)_{i \in I}$ be a family of linear functionals on $E$,
and let $(\beta_i)_{i \in I}$ be real numbers, where the index set $I$ is arbitrary. If the set
$C = \{x \in E \mid \beta_i \le b_i(x) \text{ for all } i\}$ is nonempty, then
$$\operatorname{lin} C = \{y \in E \mid b_i(y) = 0 \text{ for all } i\}.$$
-/
theorem linealitySpace_setOf_forall_le {ι : Type*} (b : ι → E →ₗ[ℝ] ℝ) (β : ι → ℝ)
    (h : {x : E | ∀ i, β i ≤ b i x}.Nonempty) :
    linealitySpace {x : E | ∀ i, β i ≤ b i x} = {y : E | ∀ i, b i y = 0} := by
  ext y
  rw [mem_linealitySpace, recessionCone_setOf_forall_le b β h]
  constructor
  · rintro ⟨h₁, h₂⟩ i
    have h₁' : ∀ j, (0 : ℝ) ≤ b j y := h₁
    have h₂' : ∀ j, (0 : ℝ) ≤ b j (-y) := h₂
    have := h₂' i
    rw [map_neg] at this
    linarith [h₁' i]
  · intro hy
    have hy' : ∀ j, b j y = 0 := hy
    exact ⟨fun i => (hy' i).ge, fun i => by rw [map_neg, hy' i]; simp⟩

end Examples

/-! ### Products, and preimages under a linear map -/

section Prod

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  {C : Set E} {D : Set F}

/-- For all sets $C \subseteq E$ and $D \subseteq F$, $0^+C \times 0^+D \subseteq 0^+(C \times D)$.
-/
theorem prod_recessionCone_subset (C : Set E) (D : Set F) :
    recessionCone C ×ˢ recessionCone D ⊆ recessionCone (C ×ˢ D) := by
  rintro ⟨y₁, y₂⟩ ⟨hy₁, hy₂⟩ ⟨x₁, x₂⟩ hx a ha
  exact ⟨hy₁ x₁ hx.1 a ha, hy₂ x₂ hx.2 a ha⟩

/-- Let $E$ and $F$ be real vector spaces, and let $C \subseteq E$ and $D \subseteq F$ be nonempty.
Then
$$0^+(C \times D) = 0^+C \times 0^+D.$$

Both factors must be nonempty: $0^+(C \times \emptyset) = 0^+\emptyset$ is all of $E \times F$,
which is not $0^+C \times F$ unless $0^+C = E$. -/
theorem recessionCone_prod (hC : C.Nonempty) (hD : D.Nonempty) :
    recessionCone (C ×ˢ D) = recessionCone C ×ˢ recessionCone D := by
  refine Set.Subset.antisymm (fun y hy => ⟨fun x hx a ha => ?_, fun x hx a ha => ?_⟩)
    (prod_recessionCone_subset C D)
  · obtain ⟨w, hw⟩ := hD
    exact (hy (x, w) ⟨hx, hw⟩ a ha).1
  · obtain ⟨w, hw⟩ := hC
    exact (hy (w, x) ⟨hw, hx⟩ a ha).2

/-- Let $E$ and $F$ be real vector spaces, and let $C \subseteq E$ and $D \subseteq F$ be nonempty.
Then
$$\operatorname{lin}(C \times D) = \operatorname{lin} C \times \operatorname{lin} D.$$
-/
theorem linealitySpace_prod (hC : C.Nonempty) (hD : D.Nonempty) :
    linealitySpace (C ×ˢ D) = linealitySpace C ×ˢ linealitySpace D := by
  ext ⟨y₁, y₂⟩
  simp only [mem_linealitySpace, recessionCone_prod hC hD, Set.mem_prod, Prod.neg_mk]
  tauto

end Prod

section Pi

variable {ι : Type*} {E : ι → Type*} [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)]
  {s : Set ι} {C : ∀ i, Set (E i)}

/-- Let $s$ be a set of indices and let $C_i \subseteq E_i$ for each index $i$. Then the product
over $s$ of the recession cones is contained in the recession cone of the product over $s$ of
the sets. A product over $s$ (`Set.pi s`) puts no condition on the coordinates outside $s$.

No hypothesis is needed. This is the `Set.pi` form of
`ConvexAnalysis.prod_recessionCone_subset`. -/
theorem pi_recessionCone_subset (s : Set ι) (C : ∀ i, Set (E i)) :
    s.pi (fun i => recessionCone (C i)) ⊆ recessionCone (s.pi C) := by
  intro y hy x hx a ha i hi
  exact hy i hi (x i) (hx i hi) a ha

/-- Let $(E_i)$ be a family of real vector spaces, let $s$ be a set of indices, let
$C_i \subseteq E_i$ for each $i$, and let
$$P = \{x \mid x_i \in C_i \text{ for all } i \in s\}.$$
If $P$ is nonempty, then
$$0^+P = \{y \mid y_i \in 0^+C_i \text{ for all } i \in s\}.$$

This is the `Set.pi` form of `ConvexAnalysis.recessionCone_prod`. The nonemptiness hypothesis is
needed for the same reason: to test one coordinate, the proof needs a point in all the other
coordinates. -/
theorem recessionCone_pi (hC : (s.pi C).Nonempty) :
    recessionCone (s.pi C) = s.pi (fun i => recessionCone (C i)) := by
  classical
  refine Set.Subset.antisymm (fun y hy => ?_) (pi_recessionCone_subset s C)
  intro i hi x hx a ha
  obtain ⟨w, hw⟩ := hC
  have hupd : Function.update w i x ∈ s.pi C := by
    intro j hj
    rcases eq_or_ne j i with rfl | hji
    · rwa [Function.update_self]
    · rw [Function.update_of_ne hji]
      exact hw j hj
  have hmem := hy (Function.update w i x) hupd a ha i hi
  rwa [Pi.add_apply, Pi.smul_apply, Function.update_self] at hmem

/-- Let $(E_i)$ be a family of real vector spaces, let $s$ be a set of indices, let
$C_i \subseteq E_i$ for each $i$, and let $P = \{x \mid x_i \in C_i \text{ for all } i \in s\}$.
If $P$ is nonempty, then
$$\operatorname{lin} P = \{y \mid y_i \in \operatorname{lin} C_i \text{ for all } i \in s\}.$$
-/
theorem linealitySpace_pi (hC : (s.pi C).Nonempty) :
    linealitySpace (s.pi C) = s.pi (fun i => linealitySpace (C i)) := by
  ext y
  simp only [mem_linealitySpace, recessionCone_pi hC, Set.mem_pi, Pi.neg_apply, forall_and]

end Pi

section PreimageDefs

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

/-- For a linear map $A : E \to F$ and a set $D \subseteq F$, $A^{-1}(0^+D) \subseteq 0^+(A^{-1}D)$.
No hypothesis is needed. -/
theorem preimage_recessionCone_subset (A : E →ₗ[ℝ] F) (D : Set F) :
    A ⁻¹' recessionCone D ⊆ recessionCone (A ⁻¹' D) := by
  intro y hy x hx a ha
  have h : A x + a • A y ∈ D := hy (A x) hx a ha
  simpa [map_add, map_smul] using h

end PreimageDefs

/-! ### Closedness, limits, and one-half-line criteria -/

section Topological

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] {C D : Set E} {y : E}

/-- The sequence $(n + 1)^{-1}$ tends to $0$ as $n \to \infty$. Mathlib states this with
`1 / (n + 1)` in place of `(n + 1)⁻¹`. -/
theorem tendsto_inv_nat_add_one_atTop_nhds_zero :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
  simpa only [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)

/-- The closure of a pointed convex cone $K$ is its own recession cone:
$0^+(\operatorname{cl} K) = \operatorname{cl} K$.

Mathlib's `PointedCone.closure` makes $\operatorname{cl} K$ a pointed convex cone, and then
`ConvexAnalysis.recessionCone_coe_pointedCone` applies. -/
theorem recessionCone_closure_coe_pointedCone (K : PointedCone ℝ E) :
    recessionCone (closure (K : Set E)) = closure (K : Set E) := by
  rw [← PointedCone.coe_closure]
  exact recessionCone_coe_pointedCone K.closure

/-- Let $E$ be a real topological vector space and $C \subseteq E$ a closed set. Then $0^+C$ is
closed.

No convexity, no nonemptiness and no local compactness are needed: by
`ConvexAnalysis.recessionCone_eq_iInter`, $0^+C$ is an intersection of preimages of $C$ under
the continuous maps $y \mapsto x + ay$. -/
theorem isClosed_recessionCone (hC : IsClosed C) : IsClosed (recessionCone C) := by
  rw [recessionCone_eq_iInter]
  exact isClosed_biInter fun x _ => isClosed_biInter fun a _ => hC.preimage (by fun_prop)

omit [ContinuousSMul ℝ E] in
/-- Let $E$ be a real vector space with a topology in which addition is continuous. Then
$0^+C \subseteq 0^+(\operatorname{cl} C)$ for every set $C$.

The reverse inclusion is false: for $C = \{(s, t) \mid s > 0,\ t > 0\} \cup \{0\}$ in
$\mathbb{R}^2$, $0^+(\operatorname{cl} C)$ is the closed quadrant, while $0^+C = C$. -/
theorem recessionCone_subset_recessionCone_closure (C : Set E) :
    recessionCone C ⊆ recessionCone (closure C) := by
  intro y hy x hx a ha
  have hcont : Continuous fun z : E => z + a • y := by fun_prop
  have himg : (fun z : E => z + a • y) '' closure C ⊆ closure ((fun z : E => z + a • y) '' C) :=
    image_closure_subset_closure_image hcont
  refine closure_mono (fun z hz => ?_) (himg ⟨x, hx, rfl⟩)
  obtain ⟨w, hw, rfl⟩ := hz
  exact hy w hw a ha

/-- For $x, y \in E$, the sequence $(n + 1)^{-1}(x + (n + 1)y)$ converges to $y$. It is the sequence
that `ConvexAnalysis.exists_tendsto_of_mem_recessionCone` uses. -/
theorem tendsto_inv_smul_ray (x y : E) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹ • (x + ((n : ℝ) + 1) • y)) atTop (𝓝 y) := by
  have hfun : (fun n : ℕ => ((n : ℝ) + 1)⁻¹ • (x + ((n : ℝ) + 1) • y))
      = fun n : ℕ => ((n : ℝ) + 1)⁻¹ • x + y := by
    funext n
    have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
    rw [smul_add, smul_smul, inv_mul_cancel₀ hne, one_smul]
  have hconst : Tendsto (fun _ : ℕ => y) atTop (𝓝 y) := tendsto_const_nhds
  have hsum := (tendsto_inv_nat_add_one_atTop_nhds_zero.smul_const x).add hconst
  rw [hfun]
  simpa using hsum

/-- Let $C$ be a closed convex subset of a real topological vector space, and let $x_i \in C$ and
$\lambda_i > 0$ be sequences with $\lambda_i \to 0$ and $\lambda_i x_i \to y$. Then
$y \in 0^+C$.

Finite dimension is not needed. For $x \in C$ and $a \ge 0$, the point
$(1 - a\lambda_i)x + a\lambda_i x_i$ lies in $C$ once $a\lambda_i \le 1$, and it converges to
$x + ay$. The sequence $(\lambda_i)$ need not be decreasing. -/
theorem mem_recessionCone_of_tendsto (hC : Convex ℝ C) (hC' : IsClosed C) {l : ℕ → ℝ} {u : ℕ → E}
    (hu : ∀ n, u n ∈ C) (hl : ∀ n, 0 < l n) (hl0 : Tendsto l atTop (𝓝 0))
    (hly : Tendsto (fun n => l n • u n) atTop (𝓝 y)) : y ∈ recessionCone C := by
  intro x hx a ha
  have hal : Tendsto (fun n => a * l n) atTop (𝓝 0) := by simpa using hl0.const_mul a
  have hev : ∀ᶠ n in atTop, a * l n ≤ 1 :=
    (hal.eventually_lt_const one_pos).mono fun n hn => hn.le
  have hmem : ∀ᶠ n in atTop, (1 - a * l n) • x + (a * l n) • u n ∈ C := by
    filter_upwards [hev] with n hn
    exact hC hx (hu n) (by linarith) (mul_nonneg ha (hl n).le) (by ring)
  have h1 : Tendsto (fun n => (1 - a * l n) • x) atTop (𝓝 x) := by
    have hone : Tendsto (fun n => 1 - a * l n) atTop (𝓝 1) := by simpa using hal.const_sub 1
    simpa using hone.smul_const x
  have h2 : Tendsto (fun n => (a * l n) • u n) atTop (𝓝 (a • y)) := by
    simpa [mul_smul] using hly.const_smul a
  exact hC'.mem_of_tendsto (h1.add h2) hmem

/-- Let $C$ be nonempty and $y \in 0^+C$. Then there are sequences $x_i \in C$ and $\lambda_i > 0$
with $\lambda_i \to 0$ and $\lambda_i x_i \to y$. -/
theorem exists_tendsto_of_mem_recessionCone (hne : C.Nonempty) (hy : y ∈ recessionCone C) :
    ∃ (l : ℕ → ℝ) (u : ℕ → E), (∀ n, u n ∈ C) ∧ (∀ n, 0 < l n) ∧
      Tendsto l atTop (𝓝 0) ∧ Tendsto (fun n => l n • u n) atTop (𝓝 y) := by
  obtain ⟨x, hx⟩ := hne
  refine ⟨fun n => ((n : ℝ) + 1)⁻¹, fun n => x + ((n : ℝ) + 1) • y,
    fun n => hy x hx _ (by positivity), fun n => by positivity,
    tendsto_inv_nat_add_one_atTop_nhds_zero, tendsto_inv_smul_ray x y⟩

/-- Let $E$ be a real topological vector space and $C \subseteq E$ a nonempty closed convex set.
Then $y \in 0^+C$ if and only if there are sequences $x_i \in C$ and $\lambda_i > 0$ with
$$\lambda_i \to 0, \qquad \lambda_i x_i \to y.$$
This is Theorem 8.2 of [rockafellar1970convex].

The sequences are indexed by $\mathbb{N}$, and $(\lambda_i)$ need not be decreasing. The two
directions are `ConvexAnalysis.exists_tendsto_of_mem_recessionCone` and
`ConvexAnalysis.mem_recessionCone_of_tendsto`. -/
theorem mem_recessionCone_iff_exists_tendsto (hC : Convex ℝ C) (hC' : IsClosed C)
    (hne : C.Nonempty) :
    y ∈ recessionCone C ↔ ∃ (l : ℕ → ℝ) (u : ℕ → E), (∀ n, u n ∈ C) ∧ (∀ n, 0 < l n) ∧
      Tendsto l atTop (𝓝 0) ∧ Tendsto (fun n => l n • u n) atTop (𝓝 y) :=
  ⟨exists_tendsto_of_mem_recessionCone hne, fun ⟨_, _, hu, hl, hl0, hly⟩ =>
    mem_recessionCone_of_tendsto hC hC' hu hl hl0 hly⟩

/-- Let $E$ be a real topological vector space, $C \subseteq E$ a closed convex set and $y \in E$.
If there is a point $x$ with $x + ay \in C$ for every $a \ge 0$, then $y \in 0^+C$. So if $C$
contains one half-line in the direction $y$, then it contains every half-line in the direction
$y$ that starts at a point of $C$. This is Theorem 8.3 of [rockafellar1970convex].

The hypothesis does not require $x \in C$ separately; it follows by taking $a = 0$. -/
theorem mem_recessionCone_of_exists_ray (hC : Convex ℝ C) (hC' : IsClosed C)
    (h : ∃ x, ∀ a : ℝ, 0 ≤ a → x + a • y ∈ C) : y ∈ recessionCone C := by
  obtain ⟨x, hx⟩ := h
  exact mem_recessionCone_of_tendsto hC hC' (l := fun n : ℕ => ((n : ℝ) + 1)⁻¹)
    (fun n => hx ((n : ℝ) + 1) (by positivity)) (fun n => by positivity)
    tendsto_inv_nat_add_one_atTop_nhds_zero (tendsto_inv_smul_ray x y)

/-- If $C$ is closed, convex and contains $0$, then
$0^+C = \bigcap_{\varepsilon > 0} \varepsilon C$. -/
theorem recessionCone_eq_iInter_smul (hC : Convex ℝ C) (hC' : IsClosed C) (h0 : (0 : E) ∈ C) :
    recessionCone C = ⋂ ε ∈ Ioi (0 : ℝ), ε • C := by
  refine Set.Subset.antisymm (fun y hy => mem_iInter₂.2 fun ε hε => ?_) (fun y hy => ?_)
  · have hε' : (0 : ℝ) < ε := hε
    have hmem : ε⁻¹ • y ∈ C := by simpa using hy 0 h0 ε⁻¹ (by positivity)
    simpa [smul_inv_smul₀ hε'.ne'] using Set.smul_mem_smul_set (a := ε) hmem
  · have hu : ∀ n : ℕ, ((n : ℝ) + 1) • y ∈ C := by
      intro n
      have hne : (((n : ℝ) + 1)⁻¹ : ℝ) ≠ 0 := by positivity
      have hpos : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := by positivity
      have hmem : y ∈ ((n : ℝ) + 1)⁻¹ • C := mem_iInter₂.1 hy ((n : ℝ) + 1)⁻¹ hpos
      simpa using (Set.mem_smul_set_iff_inv_smul_mem₀ hne C y).1 hmem
    refine mem_recessionCone_of_tendsto hC hC' (l := fun n : ℕ => ((n : ℝ) + 1)⁻¹) hu
      (fun n => by positivity) tendsto_inv_nat_add_one_atTop_nhds_zero ?_
    have hconst : (fun n : ℕ => ((n : ℝ) + 1)⁻¹ • (((n : ℝ) + 1) • y)) = fun _ : ℕ => y := by
      funext n
      rw [smul_smul, inv_mul_cancel₀ (by positivity), one_smul]
    rw [hconst]
    exact tendsto_const_nhds

/-- Let $(C_i)_{i \in I}$ be a family of closed convex subsets of a real topological vector space
whose intersection is nonempty. Then
$$0^+\Bigl(\bigcap_i C_i\Bigr) = \bigcap_i 0^+C_i.$$
-/
theorem recessionCone_iInter {ι : Sort*} {C : ι → Set E} (hconv : ∀ i, Convex ℝ (C i))
    (hclosed : ∀ i, IsClosed (C i)) (hne : (⋂ i, C i).Nonempty) :
    recessionCone (⋂ i, C i) = ⋂ i, recessionCone (C i) := by
  refine Set.Subset.antisymm (fun y hy => mem_iInter.2 fun i => ?_)
    (iInter_recessionCone_subset C)
  obtain ⟨x, hx⟩ := hne
  exact mem_recessionCone_of_exists_ray (hconv i) (hclosed i)
    ⟨x, fun a ha => mem_iInter.1 (hy x hx a ha) i⟩

/-- Let $p$ be a predicate on the indices, let $C_i$ be a closed convex set for each $i$ with
$p(i)$, and suppose that $\bigcap_{p(i)} C_i$ is nonempty. Then the recession cone of
$\bigcap_{p(i)} C_i$ is $\bigcap_{p(i)} 0^+C_i$.

The subfamily is given by a predicate and not by a `Set` or a `Finset`, so that the result
applies to both forms of a bounded intersection. -/
theorem recessionCone_iInter₂ {ι : Sort*} {p : ι → Prop} {C : ∀ i, p i → Set E}
    (hconv : ∀ i h, Convex ℝ (C i h)) (hclosed : ∀ i h, IsClosed (C i h))
    (hne : (⋂ i, ⋂ h, C i h).Nonempty) :
    recessionCone (⋂ i, ⋂ h, C i h) = ⋂ i, ⋂ h, recessionCone (C i h) := by
  obtain ⟨x, hx⟩ := hne
  rw [recessionCone_iInter (fun i => convex_iInter (hconv i))
    (fun i => isClosed_iInter (hclosed i)) ⟨x, hx⟩]
  exact iInter_congr fun i =>
    recessionCone_iInter (hconv i) (hclosed i) ⟨x, mem_iInter.1 hx i⟩

/-- If $C$ and $D$ are closed convex sets with a common point, then
$0^+(C \cap D) = 0^+C \cap 0^+D$. -/
theorem recessionCone_inter (hC : Convex ℝ C) (hC' : IsClosed C) (hD : Convex ℝ D)
    (hD' : IsClosed D) (hne : (C ∩ D).Nonempty) :
    recessionCone (C ∩ D) = recessionCone C ∩ recessionCone D := by
  obtain ⟨x, hxC, hxD⟩ := hne
  refine Set.Subset.antisymm (fun y hy => ⟨?_, ?_⟩) (inter_recessionCone_subset C D)
  · exact mem_recessionCone_of_exists_ray hC hC' ⟨x, fun a ha => (hy x ⟨hxC, hxD⟩ a ha).1⟩
  · exact mem_recessionCone_of_exists_ray hD hD' ⟨x, fun a ha => (hy x ⟨hxC, hxD⟩ a ha).2⟩

/-- If $C$ is convex and its interior is nonempty, then $0^+(\operatorname{int} C) =
0^+(\operatorname{cl} C)$. The classical statement uses the relative interior in place of the
interior. -/
theorem recessionCone_interior_eq_recessionCone_closure (hC : Convex ℝ C)
    (hne : (interior C).Nonempty) :
    recessionCone (interior C) = recessionCone (closure C) := by
  refine Set.Subset.antisymm ?_ (fun y hy x hx a ha => ?_)
  · rw [← hC.closure_interior_eq_closure_of_nonempty_interior hne]
    exact recessionCone_subset_recessionCone_closure _
  · have h2 : x + (2 * a) • y ∈ closure C :=
      hy x (subset_closure (interior_subset hx)) (2 * a) (by linarith)
    have hcombo := hC.combo_interior_closure_mem_interior hx h2 (a := (1 : ℝ) / 2)
      (b := (1 : ℝ) / 2) (by norm_num) (by norm_num) (by norm_num)
    have hcoef : (1 : ℝ) / 2 * (2 * a) = a := by ring
    have heq : ((1 : ℝ) / 2) • x + ((1 : ℝ) / 2) • (x + (2 * a) • y) = x + a • y := by
      rw [smul_add, smul_smul, hcoef, ← add_assoc, ← add_smul]
      norm_num
    rwa [heq] at hcombo

/-! ### The relation to Mathlib's `asymptoticCone` -/

/-- If $C$ is nonempty, then $0^+C$ is contained in Mathlib's asymptotic cone `asymptoticCone ℝ C`.
-/
theorem recessionCone_subset_asymptoticCone (hne : C.Nonempty) :
    recessionCone C ⊆ asymptoticCone ℝ C := by
  obtain ⟨x, hx⟩ := hne
  intro y hy
  rw [mem_asymptoticCone_iff]
  refine (((tendsto_id (x := atTop (α := ℝ))).atTop_smul_const_tendsto_asymptoticNhds
    y).asymptoticNhds_vadd_const x).frequently (Filter.Eventually.frequently ?_)
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with c hc
  simpa [vadd_eq_add, add_comm] using hy x hx c hc

/-- If $C$ is closed and convex, then `asymptoticCone ℝ C` is contained in $0^+C$. -/
theorem asymptoticCone_subset_recessionCone (hC : Convex ℝ C) (hC' : IsClosed C) :
    asymptoticCone ℝ C ⊆ recessionCone C := fun y hy x hx a ha => by
  simpa [vadd_eq_add, add_comm] using
    hC.smul_vadd_mem_of_isClosed_of_mem_asymptoticCone hC' ha hy hx

/-- If $C$ is nonempty, closed and convex, then $0^+C$ is `asymptoticCone ℝ C`. -/
theorem recessionCone_eq_asymptoticCone (hC : Convex ℝ C) (hC' : IsClosed C) (hne : C.Nonempty) :
    recessionCone C = asymptoticCone ℝ C :=
  Set.Subset.antisymm (recessionCone_subset_asymptoticCone hne)
    (asymptoticCone_subset_recessionCone hC hC')

/-- If $C$ is nonempty and convex, then `asymptoticCone ℝ C` is $0^+(\operatorname{cl} C)$. So
Mathlib's asymptotic cone is the recession cone of the closure, which the older literature calls
the asymptotic cone. -/
theorem recessionCone_closure_eq_asymptoticCone (hC : Convex ℝ C) (hne : C.Nonempty) :
    recessionCone (closure C) = asymptoticCone ℝ C := by
  rw [recessionCone_eq_asymptoticCone hC.closure isClosed_closure hne.closure,
    asymptoticCone_closure]

end Topological

/-! ### Preimages under a linear map -/

section Preimage

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] {D : Set F}

/-- Let $E$ be a real vector space, $F$ a real topological vector space, $A : E \to F$ a linear map,
and $D \subseteq F$ a closed convex set with $A^{-1}D$ nonempty. Then
$$0^+(A^{-1}D) = A^{-1}(0^+D).$$

Continuity of $A$ is not needed, and $E$ carries no topology: the proof uses
`ConvexAnalysis.mem_recessionCone_of_exists_ray` inside $D$, not inside $A^{-1}D$. -/
theorem recessionCone_preimage (A : E →ₗ[ℝ] F) (hD : Convex ℝ D) (hD' : IsClosed D)
    (hne : (A ⁻¹' D).Nonempty) :
    recessionCone (A ⁻¹' D) = A ⁻¹' recessionCone D := by
  obtain ⟨x, hx⟩ := hne
  refine Set.Subset.antisymm (fun y hy => ?_) (preimage_recessionCone_subset A D)
  refine mem_recessionCone_of_exists_ray hD hD' ⟨A x, fun a ha => ?_⟩
  simpa [map_add, map_smul] using hy x hx a ha

end Preimage

/-! ### Bounded sets and balls -/

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {C : Set E}

/-- In a real normed space, a nonempty bounded set $C$ has $0^+C = \{0\}$. Closedness, convexity and
finite dimension are not needed. -/
theorem recessionCone_eq_zero_of_isBounded (hne : C.Nonempty) (h : IsBounded C) :
    recessionCone C = {0} := by
  refine Set.Subset.antisymm (fun y hy => ?_) (by simp)
  obtain ⟨x, hx⟩ := hne
  obtain ⟨R, hR⟩ := h.exists_norm_le
  by_contra hy0
  have hyne : y ≠ 0 := by simpa using hy0
  have hy' : 0 < ‖y‖ := norm_pos_iff.2 hyne
  have hR0 : 0 ≤ R := (norm_nonneg x).trans (hR x hx)
  set a : ℝ := (R + ‖x‖ + 1) / ‖y‖ with hadef
  have ha : 0 ≤ a := by positivity
  have hmem : ‖x + a • y‖ ≤ R := hR _ (hy x hx a ha)
  have hsplit : ‖a • y‖ ≤ ‖x + a • y‖ + ‖x‖ := by
    have hrw : ‖a • y‖ = ‖x + a • y - x‖ := by congr 1; abel
    rw [hrw]
    exact norm_sub_le (x + a • y) x
  have hnorm : ‖a • y‖ = R + ‖x‖ + 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha, hadef, div_mul_cancel₀ _ hy'.ne']
  rw [hnorm] at hsplit
  linarith

/-- For $\varepsilon \ge 0$, the recession cone of the closed ball $\bar B(x, \varepsilon)$ is
$\{0\}$. -/
theorem recessionCone_closedBall (x : E) {ε : ℝ} (hε : 0 ≤ ε) :
    recessionCone (Metric.closedBall x ε) = {0} :=
  recessionCone_eq_zero_of_isBounded ⟨x, Metric.mem_closedBall_self hε⟩ Metric.isBounded_closedBall

variable {G : Type*} [AddCommGroup G] [Module ℝ G]

/-- Let $A : G \to E$ be a linear map from a real vector space $G$ to a real normed space $E$, let
$x \in E$ and $\varepsilon \ge 0$, and suppose that $A^{-1}\bar B(x, \varepsilon)$ is nonempty.
Then $0^+\bigl(A^{-1}\bar B(x, \varepsilon)\bigr) = \ker A$.

The closedness theorem for linear images uses this computation. It needs no topology on $G$. -/
theorem recessionCone_preimage_closedBall (A : G →ₗ[ℝ] E) (x : E) {ε : ℝ} (hε : 0 ≤ ε)
    (hne : (A ⁻¹' Metric.closedBall x ε).Nonempty) :
    recessionCone (A ⁻¹' Metric.closedBall x ε) = LinearMap.ker A := by
  rw [recessionCone_preimage A (convex_closedBall x ε) Metric.isClosed_closedBall hne,
    recessionCone_closedBall x hε]
  ext y
  simp [LinearMap.mem_ker]

end Normed

/-! ### Boundedness -/

section FiniteDimensional

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {C : Set E}

/-- Let $E$ be a finite-dimensional real normed space and $C \subseteq E$ a nonempty closed convex
set. Then $C$ is bounded if and only if $0^+C = \{0\}$.

Finite dimension enters here through Mathlib's `isBounded_iff_asymptoticCone_subset_singleton`.
The other boundedness results of this module use this criterion, and
`ConvexAnalysis.exists_finset_iInter₂_recessionCone_eq_zero` also uses the compactness of the
unit sphere. -/
theorem isBounded_iff_recessionCone_eq_zero (hC : Convex ℝ C) (hC' : IsClosed C)
    (hne : C.Nonempty) : IsBounded C ↔ recessionCone C = {0} := by
  rw [recessionCone_eq_asymptoticCone hC hC' hne, isBounded_iff_asymptoticCone_subset_singleton]
  refine ⟨fun h => Set.Subset.antisymm h ?_, fun h => h.subset⟩
  simpa using zero_mem_asymptoticCone.2 hne

/-- In a finite-dimensional real normed space, an unbounded nonempty closed convex set $C$ has a
nonzero $y \in 0^+C$. -/
theorem exists_ne_zero_mem_recessionCone_of_not_isBounded (hC : Convex ℝ C) (hC' : IsClosed C)
    (hne : C.Nonempty) (hub : ¬ IsBounded C) : ∃ y ∈ recessionCone C, y ≠ 0 := by
  by_contra hcon
  push Not at hcon
  refine hub ((isBounded_iff_recessionCone_eq_zero hC hC' hne).2 ?_)
  refine Set.Subset.antisymm (fun y hy => ?_) (by simp)
  simpa using hcon y hy

/-- In a finite-dimensional real normed space, a nonempty closed convex set $C$ is compact if and
only if $0^+C = \{0\}$. -/
theorem isCompact_iff_recessionCone_eq_zero (hC : Convex ℝ C) (hC' : IsClosed C)
    (hne : C.Nonempty) : IsCompact C ↔ recessionCone C = {0} := by
  rw [← isBounded_iff_recessionCone_eq_zero hC hC' hne]
  exact ⟨fun h => h.isBounded, fun h => Metric.isCompact_of_isClosed_isBounded hC' h⟩

/-- Let $E$ be a finite-dimensional real normed space, $C \subseteq E$ a closed convex set, and $M$,
$N$ affine subsets of $E$ that are parallel, that is, have the same direction. If $M \cap C$ is
nonempty and bounded, then $N \cap C$ is bounded. -/
theorem isBounded_inter_of_direction_eq (hC : Convex ℝ C) (hC' : IsClosed C)
    {M N : AffineSubspace ℝ E} (hMN : M.direction = N.direction)
    (hM : ((M : Set E) ∩ C).Nonempty) (hb : IsBounded ((M : Set E) ∩ C)) :
    IsBounded ((N : Set E) ∩ C) := by
  rcases Set.eq_empty_or_nonempty ((N : Set E) ∩ C) with h | hN
  · simp [h]
  have hMne : (M : Set E).Nonempty := hM.mono inter_subset_left
  have hNne : (N : Set E).Nonempty := hN.mono inter_subset_left
  have hMcl : IsClosed (M : Set E) := M.closed_of_finiteDimensional
  have hNcl : IsClosed (N : Set E) := N.closed_of_finiteDimensional
  have key : recessionCone ((N : Set E) ∩ C) = recessionCone ((M : Set E) ∩ C) := by
    rw [recessionCone_inter N.convex hNcl hC hC' hN, recessionCone_inter M.convex hMcl hC hC' hM,
      recessionCone_coe_affineSubspace hNne, recessionCone_coe_affineSubspace hMne, hMN]
  rw [isBounded_iff_recessionCone_eq_zero (N.convex.inter hC) (hNcl.inter hC') hN, key]
  exact (isBounded_iff_recessionCone_eq_zero (M.convex.inter hC) (hMcl.inter hC') hM).1 hb

/-- In a finite-dimensional real normed space, let $(C_i)_{i \in I}$ be closed sets with
$\bigcap_i 0^+C_i = \{0\}$. Then there is a finite set $S \subseteq I$ with
$\bigcap_{i \in S} 0^+C_i = \{0\}$.

Convexity is not used. Each $0^+C_i$ is a closed cone, so the unit sphere is covered by the
complements of finitely many of them. -/
theorem exists_finset_iInter₂_recessionCone_eq_zero {ι : Type*} {C : ι → Set E}
    (hcl : ∀ i, IsClosed (C i)) (h : ⋂ i, recessionCone (C i) = {0}) :
    ∃ S : Finset ι, ⋂ i ∈ S, recessionCone (C i) = {0} := by
  have hempty : Metric.sphere (0 : E) 1 ∩ ⋂ i, recessionCone (C i) = ∅ := by
    rw [h]
    ext y
    simp +contextual
  obtain ⟨S, hS⟩ := (isCompact_sphere (0 : E) 1).elim_finite_subfamily_closed
    (fun i => recessionCone (C i)) (fun i => isClosed_recessionCone (hcl i))
    (Set.disjoint_iff_inter_eq_empty.2 hempty)
  rw [Set.disjoint_iff_inter_eq_empty] at hS
  refine ⟨S, Set.Subset.antisymm (fun y hy => ?_) (by simp)⟩
  by_contra hy0
  have hyne : ‖y‖ ≠ 0 := norm_ne_zero_iff.2 (by simpa using hy0)
  have hmem : ‖y‖⁻¹ • y ∈ Metric.sphere (0 : E) 1 ∩ ⋂ i ∈ S, recessionCone (C i) := by
    refine ⟨?_, mem_iInter₂.2 fun i hi =>
      smul_mem_recessionCone (by positivity) (mem_iInter₂.1 hy i hi)⟩
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (by simpa using hyne)]
  rw [hS] at hmem
  exact hmem

/-- Let $E$ be a finite-dimensional real normed space, and let $(C_i)_{i \in I}$ be a family of
closed convex subsets of $E$ such that every finite subfamily has a common point. Then
$$\bigcap_i 0^+C_i = \{0\} \iff \bigcap_{i \in S} C_i \text{ is bounded for some finite } S
  \subseteq I.$$
This is the recession hypothesis of Helly's theorem.

Neither direction uses the recession cone of the whole intersection. The forward direction
applies `ConvexAnalysis.isBounded_iff_recessionCone_eq_zero` to a finite subfamily that
`ConvexAnalysis.exists_finset_iInter₂_recessionCone_eq_zero` gives by compactness of the unit
sphere. The reverse direction applies the same criterion to the finite intersection, whose
recession cone is the intersection of the recession cones. -/
theorem iInter_recessionCone_eq_zero_iff_exists_isBounded {ι : Type*} {C : ι → Set E}
    (hconv : ∀ i, Convex ℝ (C i)) (hcl : ∀ i, IsClosed (C i))
    (hne : ∀ S : Finset ι, (⋂ i ∈ S, C i).Nonempty) :
    ⋂ i, recessionCone (C i) = {0} ↔ ∃ S : Finset ι, IsBounded (⋂ i ∈ S, C i) := by
  have hrec : ∀ S : Finset ι,
      recessionCone (⋂ i ∈ S, C i) = ⋂ i ∈ S, recessionCone (C i) := fun S =>
    recessionCone_iInter₂ (C := fun i (_ : i ∈ S) => C i) (fun i _ => hconv i)
      (fun i _ => hcl i) (hne S)
  have hbdd : ∀ S : Finset ι,
      IsBounded (⋂ i ∈ S, C i) ↔ ⋂ i ∈ S, recessionCone (C i) = {0} := fun S => by
    rw [isBounded_iff_recessionCone_eq_zero (convex_iInter₂ fun i _ => hconv i)
      (isClosed_iInter fun i => isClosed_iInter fun _ => hcl i) (hne S), hrec S]
  constructor
  · intro h
    obtain ⟨S, hS⟩ := exists_finset_iInter₂_recessionCone_eq_zero hcl h
    exact ⟨S, (hbdd S).2 hS⟩
  · rintro ⟨S, hS⟩
    refine Set.Subset.antisymm (fun y hy => ?_) (by simp)
    rw [← (hbdd S).1 hS]
    exact mem_iInter₂.2 fun i _ => mem_iInter.1 hy i

end FiniteDimensional

end ConvexAnalysis
