/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Duality.Barrier
import Numlib.Analysis.Convex.Polyhedral.Duality
import Numlib.Analysis.Convex.Polyhedral.Separation

/-!
# Closedness of a sum with a polyhedral set

Let $E$ and $F$ be finite-dimensional real normed spaces in duality through a pairing
$\langle x, y \rangle$, and let $C_1, C_2 \subseteq E$ be nonempty convex sets with $C_2$ closed.
The general criterion for the closedness of $C_1 + C_2$ asks that every direction of recession $v$
of $C_1$ with $-v$ a direction of recession of $C_2$ lies in the lineality spaces of both sets. If
$C_1$ is polyhedral, the condition on $C_1$ disappears: it is enough that $C_2$ is linear in each
such direction, that is, that $v$ is also a direction of recession of $C_2$. This is Theorem 20.3 of
[rockafellar1970convex]. A consequence is a strong separation theorem for a polyhedral set and a
closed convex set.

The proof uses the barrier cones $\operatorname{dom} \delta^*(\cdot \mid C_i)$, the effective
domains of the support functions. Polyhedral separation of the two barrier cones gives the
constraint qualification that the barrier cone of $C_1$ meets the relative interior of the barrier
cone of $C_2$.

## Main results

* `ConvexAnalysis.isClosed_add_of_polyhedral`: if $C_1$ is a nonempty polyhedral set, $C_2$ is a
  nonempty closed convex set, and $C_2$ is linear in every direction of recession $v$ of $C_1$ with
  $-v$ a direction of recession of $C_2$, then $C_1 + C_2$ is closed.
* `ConvexAnalysis.separatesStrongly_of_polyhedral_of_recession`: the same hypotheses, for disjoint
  sets and with $v$ in place of $-v$, give strong separation of $C_1$ and $C_2$.
* `ConvexAnalysis.nonempty_convexDom_supportFn_inter_relint`: under the hypotheses of the first
  result, the barrier cone of $C_1$ meets the relative interior of the barrier cone of $C_2$.

## Implementation notes

* Closedness is read off effective domains, not from a formula for an infimal convolute.
  `ConvexAnalysis.IsExactSum.of_polyhedral_closed` gives $\big(\delta^*(\cdot \mid C_1) +
  \delta^*(\cdot \mid C_2)\big)^* = \delta(\cdot \mid C_1) \mathbin{\square} \delta(\cdot \mid
  C_2)$. The left side is $\delta(\cdot \mid \operatorname{cl}(C_1 + C_2))$, and the effective
  domain of the right side is $C_1 + C_2$.
* The pairing is a bilinear map `B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ`. The hypotheses
  `ConvexAnalysis.IsCompatiblePairing B` and `ConvexAnalysis.IsCompatiblePairing B.flip` say that
  every continuous linear functional on $E$ is $\langle \cdot, y \rangle$ for some $y \in F$, and
  every continuous linear functional on $F$ is $\langle x, \cdot \rangle$ for some $x \in E$.
-/

open Set
open scoped Pointwise

namespace ConvexAnalysis

section Closedness

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {C₁ C₂ : Set E}

/-- If $C_1$ is polyhedral, then its barrier cone $\operatorname{dom} \delta^*(\cdot \mid C_1)$ is
polyhedral.

The support function $\delta^*(\cdot \mid C_1)$ is the conjugate of the indicator function of
$C_1$, which is polyhedral. So the support function is polyhedral, and the effective domain of a
polyhedral function is polyhedral. -/
theorem polyhedral_convexDom_supportFn (h₁ : Polyhedral C₁) :
    Polyhedral (convexDom (supportFn B C₁)) := by
  have hfn : PolyhedralFn (supportFn B C₁) := by
    rw [supportFn_eq_convexConj_indicatorFn]
    exact PolyhedralFn.convexConj (B := B) (polyhedralFn_indicatorFn h₁)
  exact hfn.polyhedral_convexDom

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- If $C_1$ is nonempty, then $0$ is in its barrier cone: $\delta^*(0 \mid C_1) < +\infty$. -/
theorem zero_mem_convexDom_supportFn (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (hne : C₁.Nonempty) :
    (0 : F) ∈ convexDom (supportFn B C₁) := by
  rw [mem_convexDom, supportFn_zero hne]
  exact EReal.zero_lt_top

/-- **The constraint qualification.** Let $E$ and $F$ be finite-dimensional real normed spaces with
a pairing under which each space represents all continuous linear functionals on the other. Let
$C_1$ be a nonempty polyhedral set and let $C_2$ be a nonempty closed convex set. Suppose that
every direction of recession $v$ of $C_1$ such that $-v$ is a direction of recession of $C_2$ is
also a direction of recession of $C_2$. Then the barrier cone of $C_1$ meets the relative
interior of the barrier cone of $C_2$: $$\operatorname{dom} \delta^*(\cdot \mid C_1) \cap
\operatorname{ri} \operatorname{dom} \delta^*(\cdot \mid C_2) \ne \emptyset.$$

The proof uses the polyhedrality of $C_1$ here. If the intersection were empty, polyhedral
separation would separate the two barrier cones by a hyperplane, and the normal of this
hyperplane would be a direction of recession that violates the hypothesis. -/
theorem nonempty_convexDom_supportFn_inter_relint [IsCompatiblePairing B]
    [IsCompatiblePairing B.flip]
    (h₁ : Polyhedral C₁) (hne₁ : C₁.Nonempty)
    (h₂ : Convex ℝ C₂) (hcl₂ : IsClosed C₂) (hne₂ : C₂.Nonempty)
    (hrec : ∀ v ∈ recessionCone C₁, -v ∈ recessionCone C₂ → v ∈ recessionCone C₂) :
    (convexDom (supportFn B C₁) ∩ ri (convexDom (supportFn B C₂))).Nonempty := by
  by_contra hcon
  rw [Set.not_nonempty_iff_eq_empty, ← Set.disjoint_iff_inter_eq_empty] at hcon
  obtain ⟨ψ, γ, hsep, hns⟩ :=
    (exists_separates_not_subset_iff_disjoint_relint (polyhedral_convexDom_supportFn h₁)
      (convexFn_supportFn B C₂).convex_convexDom
      ⟨0, zero_mem_convexDom_supportFn B hne₂⟩).2 hcon
  have hγ : γ = 0 := by
    have hl : ψ 0 ≤ γ := hsep.le_of_mem_left (zero_mem_convexDom_supportFn B hne₁)
    have hr : γ ≤ ψ 0 := hsep.le_of_mem_right (zero_mem_convexDom_supportFn B hne₂)
    rw [map_zero] at hl hr
    linarith
  subst hγ
  obtain ⟨v, hv⟩ := exists_pairing_eq B.flip ψ
  have hv₁ : v ∈ recessionCone C₁ := by
    rw [← polarCone_convexDom_supportFn (B := B) h₁.convex h₁.isClosed hne₁]
    intro y hy
    have h := hsep.le_of_mem_left hy
    rw [hv y] at h
    exact h
  have hv₂ : -v ∈ recessionCone C₂ := by
    rw [← polarCone_convexDom_supportFn (B := B) h₂ hcl₂ hne₂]
    intro y hy
    have h := hsep.le_of_mem_right hy
    rw [hv y] at h
    have hneg : B.flip y (-v) = -(B.flip y v) := map_neg _ _
    rw [hneg]
    linarith
  have hv₃ : v ∉ recessionCone C₂ := by
    rw [← polarCone_convexDom_supportFn (B := B) h₂ hcl₂ hne₂]
    intro hmem
    refine hns fun y hy => ?_
    have h1 : B.flip y v ≤ 0 := hmem y hy
    have h2 := hsep.le_of_mem_right hy
    rw [hv y] at h2
    have h3 : ψ y = 0 := by rw [hv y]; linarith
    exact h3
  exact hv₃ (hrec v hv₁ hv₂)

/-- Let $E$ and $F$ be finite-dimensional real normed spaces with a pairing under which each space
represents all continuous linear functionals on the other. Let $C_1 \subseteq E$ be a nonempty
polyhedral convex set and let $C_2 \subseteq E$ be a nonempty closed convex set. Suppose that
every direction of recession $v$ of $C_1$ such that $-v$ is a direction of recession of $C_2$ is
also a direction of recession of $C_2$, that is, a direction in which $C_2$ is linear. Then
$C_1 + C_2$ is closed.

This is Theorem 20.3 of [rockafellar1970convex]. The general criterion asks in addition that
such a direction lie in the lineality space of $C_1$. The polyhedrality of $C_1$ removes this
condition. -/
theorem isClosed_add_of_polyhedral [IsCompatiblePairing B] [IsCompatiblePairing B.flip]
    (h₁ : Polyhedral C₁) (hne₁ : C₁.Nonempty)
    (h₂ : Convex ℝ C₂) (hcl₂ : IsClosed C₂) (hne₂ : C₂.Nonempty)
    (hrec : ∀ v ∈ recessionCone C₁, -v ∈ recessionCone C₂ → v ∈ recessionCone C₂) :
    IsClosed (C₁ + C₂) := by
  obtain ⟨x₀, hx₀₁, hx₀₂⟩ :=
    nonempty_convexDom_supportFn_inter_relint (B := B) h₁ hne₁ h₂ hcl₂ hne₂ hrec
  have hfn₁ : PolyhedralFn (supportFn B C₁) := by
    rw [supportFn_eq_convexConj_indicatorFn]
    exact PolyhedralFn.convexConj (B := B) (polyhedralFn_indicatorFn h₁)
  have hexact : IsExactSum B.flip (supportFn B C₁) (supportFn B C₂) :=
    IsExactSum.of_polyhedral_closed hfn₁ (properConvex_supportFn hne₁)
      ⟨convexFn_supportFn B C₂, closedConvex_supportFn, properConvex_supportFn hne₂⟩ hx₀₁ hx₀₂
  have hL : convexConj B.flip (supportFn B C₁ + supportFn B C₂)
      = indicatorFn (closure (C₁ + C₂)) := by
    rw [← supportFn_add]
    exact convexConj_supportFn_of_convex (h₁.convex.add h₂)
  have hkey := hexact.convexConj_add
  rw [hL, convexConj_supportFn h₁.convex h₁.isClosed, convexConj_supportFn h₂ hcl₂] at hkey
  have hdom := congrArg convexDom hkey
  rw [convexDom_indicatorFn, convexDom_infConv, convexDom_indicatorFn,
      convexDom_indicatorFn] at hdom
  exact closure_eq_iff_isClosed.1 hdom

/-- Let $E$ and $F$ be finite-dimensional real normed spaces with a pairing under which each space
represents all continuous linear functionals on the other. Let $C_1 \subseteq E$ be a nonempty
polyhedral convex set and let $C_2 \subseteq E$ be a nonempty closed convex set, disjoint from
$C_1$. Suppose that for every direction of recession $v$ of $C_1$ that is also a direction of
recession of $C_2$, the direction $-v$ is a direction of recession of $C_2$. Then $C_1$ and
$C_2$ can be separated strongly: there are a continuous linear functional $f$ on $E$ and a real
number $c$ with $$\sup_{x \in C_1} f(x) < c < \inf_{x \in C_2} f(x).$$

The hypothesis says that the only common directions of recession of $C_1$ and $C_2$ are
directions in which $C_2$ is linear. The general criterion asks that the two sets have no common
direction of recession. When both sets are polyhedral, no condition on recession is needed
(`ConvexAnalysis.separatesStrongly_of_polyhedral`). -/
theorem separatesStrongly_of_polyhedral_of_recession [IsCompatiblePairing B]
    [IsCompatiblePairing B.flip]
    (h₁ : Polyhedral C₁) (hne₁ : C₁.Nonempty)
    (h₂ : Convex ℝ C₂) (hcl₂ : IsClosed C₂) (hne₂ : C₂.Nonempty) (hdisj : Disjoint C₁ C₂)
    (hrec : ∀ v ∈ recessionCone C₁, v ∈ recessionCone C₂ → -v ∈ recessionCone C₂) :
    ∃ (f : E →L[ℝ] ℝ) (c : ℝ), SeparatesStrongly f c C₁ C₂ := by
  refine (separatesStrongly_iff_zero_notMem_closure_sub h₁.convex h₂).2 ?_
  have hclosed : IsClosed (C₁ + (-C₂)) := by
    refine isClosed_add_of_polyhedral (B := B) h₁ hne₁ h₂.neg hcl₂.neg hne₂.neg ?_
    intro v hv₁ hv₂
    rw [recessionCone_neg, Set.mem_neg] at hv₂ ⊢
    rw [neg_neg] at hv₂
    exact hrec v hv₁ hv₂
  rw [sub_eq_add_neg, hclosed.closure_eq]
  rintro ⟨x, hx, y, hy, hxy⟩
  rw [Set.mem_neg] at hy
  have hxy' : x + y = 0 := hxy
  have hxe : x = -y := add_eq_zero_iff_eq_neg.1 hxy'
  exact Set.disjoint_left.1 hdisj hx (hxe ▸ hy)

end Closedness

end ConvexAnalysis
