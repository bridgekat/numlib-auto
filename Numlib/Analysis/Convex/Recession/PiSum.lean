/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Recession.Closedness

/-!
# Sums of finitely many convex sets

Let $C_i$, $i \in \iota$, be subsets of a real vector space $E$, indexed by a finite type $\iota$.
Their sum $\sum_i C_i = \{\sum_i x_i : x_i \in C_i\}$ is the image of the product set
$\prod_i C_i \subseteq E^\iota$ under the linear sum map $(x_i)_i \mapsto \sum_i x_i$. A question
about the closure or the recession cone of a finite sum thus becomes a question about a linear
image, and the results on linear images in `Numlib.Analysis.Convex.Recession.Closedness` answer it.
The presentation follows [rockafellar1970convex], §9.

Write $\operatorname{cl} C$ for the closure of $C$, $0^+C = \{y : x + a y \in C \text{ for all } x
\in C,\ a \ge 0\}$ for its recession cone, and $\operatorname{lin} C = 0^+C \cap (-0^+C)$ for its
lineality space. In a finite-dimensional real normed space, the module proves three facts about
nonempty convex sets $C_i$ under a cancellation condition: if $z_i \in 0^+(\operatorname{cl} C_i)$
for all $i$ and $\sum_i z_i = 0$, then $z_i \in \operatorname{lin}(\operatorname{cl} C_i)$ for all
$i$. Under this condition a sum of closed sets is closed, and closure and recession cone distribute
over the sum.

## Main definitions

* `ConvexAnalysis.piSum`: the linear sum map $E^\iota \to E$, $(x_i)_i \mapsto \sum_i x_i$.

## Main results

* `ConvexAnalysis.image_piSum_univ_pi`: the sum map sends $\prod_i C_i$ onto $\sum_i C_i$.
* `Convex.isClosed_sum`: a finite sum of nonempty closed convex sets that satisfies the cancellation
  condition is closed.
* `Convex.closure_sum_eq`: under the cancellation condition, $\operatorname{cl}(\sum_i C_i) = \sum_i
  \operatorname{cl} C_i$.
* `Convex.recessionCone_sum`: under the cancellation condition, $0^+(\sum_i \operatorname{cl} C_i) =
  \sum_i 0^+(\operatorname{cl} C_i)$.

## Implementation notes

* The cancellation condition is a condition on the whole family. A sum of $m$ directions of
  recession can vanish although no two of them cancel, so the condition cannot be reduced to pairs
  of sets. For this reason the two-set results of `Numlib.Analysis.Convex.Recession.Closedness`,
  such as `Convex.isClosed_add`, are kept separately and are not derived from the results here.
* The product set $\prod_i C_i$ is `Set.univ.pi C`, and the sum $\sum_i C_i$ is the pointwise sum of
  sets `∑ i, C i`.
-/

open Set

open scoped Pointwise

namespace ConvexAnalysis

section Defs

variable {ι E : Type*} [Fintype ι] [AddCommGroup E] [Module ℝ E]

/-- Let $\iota$ be a finite type and $E$ a real vector space. The **sum map** is the linear map
$E^\iota \to E$ given by $$(x_i)_{i \in \iota} \mapsto \sum_{i \in \iota} x_i.$$

It is the $m$-ary codiagonal, where $m$ is the number of elements of $\iota$. -/
def piSum : (ι → E) →ₗ[ℝ] E where
  toFun x := ∑ i, x i
  map_add' _ _ := by simp [Finset.sum_add_distrib]
  map_smul' _ _ := by simp [Finset.smul_sum]

/-- The sum map sends $x \in E^\iota$ to $\sum_{i \in \iota} x_i$. -/
@[simp] theorem piSum_apply (x : ι → E) : (piSum : (ι → E) →ₗ[ℝ] E) x = ∑ i, x i := rfl

/-- Let $C_i \subseteq E$ for $i \in \iota$. The sum map sends the product set $\prod_i C_i$ onto
the sum of the sets: $$\Big\{\sum_i x_i : x \in \prod_i C_i\Big\} = \sum_i C_i.$$

This turns a question about a finite sum into a question about a linear image. The product set
is `Set.univ.pi C`. -/
theorem image_piSum_univ_pi (C : ι → Set E) :
    (piSum : (ι → E) →ₗ[ℝ] E) '' univ.pi C = ∑ i, C i := by
  ext y
  rw [Set.mem_fintype_sum]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, fun i => hx i (mem_univ i), rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, fun i _ => hg i, rfl⟩

end Defs

section Sum

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {C : ι → Set E}

omit [FiniteDimensional ℝ E] in
/-- Let $E$ be a real normed space and let each $C_i \subseteq E$ be nonempty. Suppose that if
$z_i \in 0^+(\operatorname{cl} C_i)$ for all $i$ and $\sum_i z_i = 0$, then $z_i \in
\operatorname{lin}(\operatorname{cl} C_i)$ for all $i$. Then the same condition holds for the
product set $P = \prod_i C_i$ and the sum map $S$: every $p \in 0^+(\operatorname{cl} P)$ with
$S p = 0$ lies in $\operatorname{lin}(\operatorname{cl} P)$.

This transports the cancellation condition of the family to the product set, where the results
on linear images apply. Finite dimension is not needed. -/
theorem forall_mem_linealitySpace_pi (hne : ∀ i, (C i).Nonempty)
    (h : ∀ z : ι → E, (∀ i, z i ∈ recessionCone (closure (C i))) → ∑ i, z i = 0 →
      ∀ i, z i ∈ linealitySpace (closure (C i))) :
    ∀ p ∈ recessionCone (closure (univ.pi C)), (piSum : (ι → E) →ₗ[ℝ] E) p = 0 →
      p ∈ linealitySpace (closure (univ.pi C)) := by
  have hpine : (univ.pi fun i => closure (C i)).Nonempty :=
    Set.univ_pi_nonempty_iff.2 fun i => (hne i).closure
  intro p hp hzero
  rw [closure_pi_set, recessionCone_pi hpine] at hp
  rw [closure_pi_set, linealitySpace_pi hpine]
  exact fun i _ => h p (fun i => hp i (mem_univ i)) hzero i

/-- Let $E$ be a finite-dimensional real normed space, and let $C_i \subseteq E$, $i \in \iota$, be
nonempty closed convex sets indexed by a finite type. Suppose that if $z_i \in 0^+ C_i$ for all
$i$ and $\sum_i z_i = 0$, then $z_i \in \operatorname{lin} C_i$ for all $i$. Then the sum
$\sum_i C_i$ is closed.

The condition says that finitely many directions of recession can sum to zero only inside the
lineality spaces. The proof applies `Convex.isClosed_image_closure` to the sum map on
$\prod_i C_i$. -/
theorem _root_.Convex.isClosed_sum (hC : ∀ i, Convex ℝ (C i)) (hCc : ∀ i, IsClosed (C i))
    (hne : ∀ i, (C i).Nonempty)
    (h : ∀ z : ι → E, (∀ i, z i ∈ recessionCone (C i)) → ∑ i, z i = 0 →
      ∀ i, z i ∈ linealitySpace (C i)) :
    IsClosed (∑ i, C i) := by
  have hcl : ∀ i, closure (C i) = C i := fun i => (hCc i).closure_eq
  have hkey := forall_mem_linealitySpace_pi hne (by simp only [hcl]; exact h)
  have hmain := Convex.isClosed_image_closure (convex_pi fun i _ => hC i) piSum hkey
  rw [closure_pi_set] at hmain
  simp only [hcl] at hmain
  rwa [image_piSum_univ_pi] at hmain

/-- Let $E$ be a finite-dimensional real normed space, and let $C_i \subseteq E$, $i \in \iota$, be
nonempty convex sets indexed by a finite type. Suppose that if
$z_i \in 0^+(\operatorname{cl} C_i)$ for all $i$ and $\sum_i z_i = 0$, then $z_i \in
\operatorname{lin}(\operatorname{cl} C_i)$ for all $i$. Then closure distributes over the sum:
$$\operatorname{cl}\Big(\sum_i C_i\Big) = \sum_i \operatorname{cl} C_i.$$
-/
theorem _root_.Convex.closure_sum_eq (hC : ∀ i, Convex ℝ (C i)) (hne : ∀ i, (C i).Nonempty)
    (h : ∀ z : ι → E, (∀ i, z i ∈ recessionCone (closure (C i))) → ∑ i, z i = 0 →
      ∀ i, z i ∈ linealitySpace (closure (C i))) :
    closure (∑ i, C i) = ∑ i, closure (C i) := by
  have hmain := Convex.closure_image_eq (convex_pi fun i _ => hC i) piSum
    (forall_mem_linealitySpace_pi hne h)
  rwa [image_piSum_univ_pi, closure_pi_set, image_piSum_univ_pi] at hmain

/-- Let $E$ be a finite-dimensional real normed space, and let $C_i \subseteq E$, $i \in \iota$, be
nonempty convex sets indexed by a finite type. Suppose that if
$z_i \in 0^+(\operatorname{cl} C_i)$ for all $i$ and $\sum_i z_i = 0$, then $z_i \in
\operatorname{lin}(\operatorname{cl} C_i)$ for all $i$. Then the recession cone of the sum of
the closures is the sum of the recession cones: $$0^+\Big(\sum_i \operatorname{cl} C_i\Big) =
\sum_i 0^+(\operatorname{cl} C_i).$$
-/
theorem _root_.Convex.recessionCone_sum (hC : ∀ i, Convex ℝ (C i)) (hne : ∀ i, (C i).Nonempty)
    (h : ∀ z : ι → E, (∀ i, z i ∈ recessionCone (closure (C i))) → ∑ i, z i = 0 →
      ∀ i, z i ∈ linealitySpace (closure (C i))) :
    recessionCone (∑ i, closure (C i)) = ∑ i, recessionCone (closure (C i)) := by
  have hpine : (univ.pi fun i => closure (C i)).Nonempty :=
    Set.univ_pi_nonempty_iff.2 fun i => (hne i).closure
  have hmain := Convex.recessionCone_image_closure (convex_pi fun i _ => hC i)
    (Set.univ_pi_nonempty_iff.2 hne) piSum (forall_mem_linealitySpace_pi hne h)
  rwa [closure_pi_set, image_piSum_univ_pi, recessionCone_pi hpine,
    image_piSum_univ_pi] at hmain

end Sum

end ConvexAnalysis
