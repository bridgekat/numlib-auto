/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Polyhedral.Conjugate
import Numlib.Analysis.Convex.Duality.Relint
import Numlib.Analysis.Convex.Indicator

/-!
# Polyhedral constraint qualifications

Let $E$ and $F$ be finite-dimensional real normed spaces in duality through a pairing
$\langle x, y \rangle$. Two proper convex functions $f, g$ on $E$ **add exactly** if the conjugate
of the sum is the infimal convolute of the conjugates, with the infimum attained: $$(f + g)^*(y) =
\min_{y_1 + y_2 = y} \big( f^*(y_1) + g^*(y_2) \big).$$ The relative-interior constraint
qualification of `Numlib.Analysis.Convex.Duality.Relint` asks that
$\operatorname{ri}(\operatorname{dom} f) \cap \operatorname{ri}(\operatorname{dom} g) \ne
\emptyset$. This module weakens it when $f$ is polyhedral: the polyhedral side contributes only a
point of its effective domain, not of its relative interior. This is Theorem 20.1 of
[rockafellar1970convex]. The same weakening holds for finitely many summands, and for the conjugate
of an inverse image $gA$.

## Main results

* `ConvexAnalysis.IsExactSum.of_polyhedral_pair`: two proper polyhedral convex functions add exactly
  if $\operatorname{dom} f \cap \operatorname{dom} g \ne \emptyset$.
* `ConvexAnalysis.IsExactSum.of_polyhedral`: a proper polyhedral convex function $f$ and a proper
  convex function $g$ add exactly if $\operatorname{dom} f$ meets
  $\operatorname{ri}(\operatorname{dom} g)$.
* `ConvexAnalysis.IsExactSum.of_polyhedral_closed`: the case of the previous result with $g$ closed,
  which carries the argument.
* `ConvexAnalysis.relint_inter_relint_nonempty_of_subset_affineSpan`: the step on relative interiors
  that the reduction uses.
* `ConvexAnalysis.IsExactFinsetSum.of_polyhedral`: proper convex functions $f_1, \dots, f_m$, of
  which $f_1, \dots, f_k$ are polyhedral, add exactly if $\operatorname{dom} f_1 \cap \dots \cap
  \operatorname{dom} f_k \cap \operatorname{ri}(\operatorname{dom} f_{k+1}) \cap \dots \cap
  \operatorname{ri}(\operatorname{dom} f_m) \ne \emptyset$.
* `ConvexAnalysis.IsExactImage.of_polyhedral`: a proper polyhedral convex function $g$ pulls back
  exactly along a linear map $A$ if the range of $A$ meets $\operatorname{dom} g$. This gives the
  polyhedral clauses of the general rules for images and subgradients.

## Proof outline

The case of two polyhedral functions is the proof of `ConvexAnalysis.IsExactSum.of_relint`, with its
closedness criterion replaced by polyhedrality. Both proofs need $\operatorname{epi} f^* +
\operatorname{epi} g^*$ to be closed. Here this is automatic, because a sum of polyhedral sets is
polyhedral and therefore closed. The general case is the classical reduction, applied to an
indicator function. Let $M = \operatorname{aff}(\operatorname{dom} g)$ and
$\delta = \delta(\cdot \mid M)$. The function $\delta + f$ is polyhedral, and
$M \cap \operatorname{dom} f$ meets $\operatorname{ri}(\operatorname{dom} g)$. So
`ConvexAnalysis.IsExactSum.of_relint` applies to $\delta + f$ and $g$. The remaining term $\delta^*$
is then absorbed, because $\delta + g = g$ and $\delta + (f + g) = f + g$.

## Implementation notes

* Closedness is not a hypothesis on either function, because a proper polyhedral convex function is
  closed (`ConvexAnalysis.PolyhedralFn.closedProperConvexFn`).
* The pairing is a bilinear map `B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ`. The hypotheses
  `ConvexAnalysis.IsCompatiblePairing B` and `ConvexAnalysis.IsCompatiblePairing B.flip` say that
  every continuous linear functional on $E$ is $\langle \cdot, y \rangle$ for some $y \in F$, and
  every continuous linear functional on $F$ is $\langle x, \cdot \rangle$ for some $x \in E$.
-/

open Set
open scoped Pointwise

namespace ConvexAnalysis

section Sum

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f g : E → EReal}

omit [FiniteDimensional ℝ F] in
/-- A proper polyhedral convex function on a finite-dimensional space is a closed proper convex
function. -/
theorem PolyhedralFn.closedProperConvexFn (hf : PolyhedralFn f) (hpf : ProperConvex f) :
    ClosedProperConvexFn f :=
  ⟨hf.convexFn, hf.closedConvex hpf.ne_bot, hpf⟩

/-- **The case of two polyhedral functions.** Let $E$ and $F$ be finite-dimensional real normed
spaces with a pairing under which each space represents all continuous linear functionals on the
other. Let $f, g \colon E \to [-\infty, +\infty]$ be proper polyhedral convex functions, and let
$x_0 \in \operatorname{dom} f \cap \operatorname{dom} g$. Then $f$ and $g$ add exactly: for
every $y \in F$ there are $y_1, y_2 \in F$ with $y_1 + y_2 = y$ and $$f^*(y_1) + g^*(y_2) \le
(f + g)^*(y).$$

No relative interior is needed on either side. This is the case $k = m$ of Theorem 20.1 of
[rockafellar1970convex], to which the general case is reduced. -/
theorem IsExactSum.of_polyhedral_pair [IsCompatiblePairing B] [IsCompatiblePairing B.flip]
    (hf : PolyhedralFn f) (hpf : ProperConvex f) (hg : PolyhedralFn g) (hpg : ProperConvex g)
    {x₀ : E} (hxf : x₀ ∈ convexDom f) (hxg : x₀ ∈ convexDom g) : IsExactSum B f g := by
  have hfc : ClosedProperConvexFn f := hf.closedProperConvexFn hpf
  have hgc : ClosedProperConvexFn g := hg.closedProperConvexFn hpg
  -- the sum of the two dual epigraphs is polyhedral, hence closed
  have hclosed : IsClosed (epi (convexConj B f) + epi (convexConj B g)) :=
    Polyhedral.isClosed (Polyhedral.add (PolyhedralFn.convexConj hf) (PolyhedralFn.convexConj hg))
  exact IsExactSum.of_isClosed_epi_add hfc hgc hxf hxg hclosed

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Let $C \subseteq E$ and let $k \colon E \to [-\infty, +\infty]$ have
$\operatorname{dom} k \subseteq C$. Then $\delta(\cdot \mid C) + k = k$.

No properness is needed: off $C$ the sum is $+\infty + (+\infty) = +\infty$. The reduction below
uses this with $C = \operatorname{aff}(\operatorname{dom} g)$, for $k = g$ and for $k = f + g$. -/
theorem indicatorFn_add_eq_self {C : Set E} {k : E → EReal}
    (hsub : convexDom k ⊆ C) : indicatorFn C + k = k := by
  funext x
  by_cases hx : x ∈ C
  · rw [Pi.add_apply, indicatorFn_of_mem hx, zero_add]
  · have hxk : k x = ⊤ := by
      by_contra hcon
      exact hx (hsub (mem_convexDom.2 (lt_top_iff_ne_top.2 hcon)))
    rw [Pi.add_apply, indicatorFn_of_notMem hx, hxk]
    simp

omit [FiniteDimensional ℝ F] in
/-- **The step on relative interiors.** Let $D_1, D_2 \subseteq E$ be convex, with $D_1$ contained
in the affine hull of $D_2$. If some $x_0 \in D_1$ is in $\operatorname{ri} D_2$, then
$\operatorname{ri} D_1 \cap \operatorname{ri} D_2 \ne \emptyset$.

The point $x_0$ need not be in $\operatorname{ri} D_1$. But $\operatorname{ri} D_2$ is a
relatively open neighbourhood of $x_0$ in $\operatorname{aff} D_2 \supseteq \operatorname{aff}
D_1$, so a small step from $x_0$ towards any point of $\operatorname{ri} D_1$ lands in both
sets. -/
theorem relint_inter_relint_nonempty_of_subset_affineSpan {D₁ D₂ : Set E}
    (h₁ : Convex ℝ D₁) (h₂ : Convex ℝ D₂) (hsub : D₁ ⊆ (affineSpan ℝ D₂ : Set E))
    {x₀ : E} (hx₁ : x₀ ∈ D₁) (hx₂ : x₀ ∈ ri D₂) : (ri D₁ ∩ ri D₂).Nonempty := by
  obtain ⟨z, hz⟩ := Convex.relint_nonempty h₁ ⟨x₀, hx₁⟩
  have hzD₁ : z ∈ D₁ := intrinsicInterior_subset hz
  have hzM : z ∈ affineSpan ℝ D₂ := hsub hzD₁
  have hx₀D₂ : x₀ ∈ D₂ := intrinsicInterior_subset hx₂
  have hx₀M : x₀ ∈ affineSpan ℝ D₂ := subset_affineSpan ℝ D₂ hx₀D₂
  -- the reflection of `z` in `x₀` still lies in the affine hull of `D₂`
  have hyM : (1 : ℝ) • (x₀ -ᵥ z) +ᵥ x₀ ∈ affineSpan ℝ D₂ :=
    AffineSubspace.smul_vsub_vadd_mem _ 1 hx₀M hzM hx₀M
  obtain ⟨μ, hμ, hmem⟩ := exists_one_lt_smul_mem_of_mem_relint hx₂ hyM
  set t : ℝ := μ - 1 with ht
  have ht0 : 0 < t := by rw [ht]; linarith
  have hxt : (1 - t) • x₀ + t • z ∈ D₂ := by
    have heq : (1 - μ) • ((1 : ℝ) • (x₀ -ᵥ z) +ᵥ x₀) + μ • x₀ = (1 - t) • x₀ + t • z := by
      simp only [vsub_eq_sub, vadd_eq_add, one_smul, ht]
      module
    rwa [heq] at hmem
  set s : ℝ := min (t / 2) 1 with hs
  have hs0 : 0 < s := lt_min (by linarith) one_pos
  have hs1 : s ≤ 1 := min_le_right _ _
  have hst : s < t := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  refine ⟨(1 - s) • x₀ + s • z, ?_, ?_⟩
  · have hseg := Convex.segment_mem_relint h₁ hz (subset_closure hx₁)
      (a := 1 - s) (by linarith) (by linarith)
    have heq : (1 - (1 - s)) • z + (1 - s) • x₀ = (1 - s) • x₀ + s • z := by module
    rwa [heq] at hseg
  · have hseg := Convex.segment_mem_relint h₂ hx₂ (subset_closure hxt)
      (a := s / t) (by positivity) ((div_lt_one ht0).2 hst)
    have heq : (1 - s / t) • x₀ + (s / t) • ((1 - t) • x₀ + t • z) = (1 - s) • x₀ + s • z := by
      match_scalars <;> (field_simp; try ring)
    rwa [heq] at hseg

/-- Let $E$ and $F$ be finite-dimensional real normed spaces with a pairing under which each space
represents all continuous linear functionals on the other. Let
$f \colon E \to [-\infty, +\infty]$ be a proper polyhedral convex function, let
$g \colon E \to [-\infty, +\infty]$ be a closed proper convex function, and let $x_0 \in
\operatorname{dom} f \cap \operatorname{ri}(\operatorname{dom} g)$. Then $f$ and $g$ add
exactly.

Let $M = \operatorname{aff}(\operatorname{dom} g)$, $\delta = \delta(\cdot \mid M)$ and
$h = \delta + f$. Then $\operatorname{ri}(\operatorname{dom} h)$ meets
$\operatorname{ri}(\operatorname{dom} g)$, so `ConvexAnalysis.IsExactSum.of_relint` splits
$(h + g)^* = (f + g)^*$ exactly. The case of two polyhedral functions splits $h^*$ as
$\delta^* \mathbin{\square} f^*$, and $\delta^* \mathbin{\square} g^* = (\delta + g)^* = g^*$
absorbs the remaining term $\delta^*$. -/
theorem IsExactSum.of_polyhedral_closed [IsCompatiblePairing B] [IsCompatiblePairing B.flip]
    (hf : PolyhedralFn f) (hpf : ProperConvex f) (hg : ClosedProperConvexFn g)
    {x₀ : E} (hxf : x₀ ∈ convexDom f) (hxg : x₀ ∈ ri (convexDom g)) : IsExactSum B f g := by
  classical
  have hx₀g : x₀ ∈ convexDom g := intrinsicInterior_subset hxg
  set MA : AffineSubspace ℝ E := affineSpan ℝ (convexDom g) with hMA
  have hx₀M : x₀ ∈ MA := subset_affineSpan ℝ (convexDom g) hx₀g
  have hdomgM : convexDom g ⊆ (MA : Set E) := subset_affineSpan ℝ (convexDom g)
  set δ : E → EReal := indicatorFn (MA : Set E) with hδdef
  have hδbot : ∀ x, δ x ≠ ⊥ := fun x => indicatorFn_ne_bot _ x
  have hδdom : convexDom δ = (MA : Set E) := convexDom_indicatorFn _
  have hδpoly : PolyhedralFn δ :=
    polyhedralFn_indicatorFn (polyhedral_coe_affineSubspace hx₀M)
  have hδproper : ProperConvex δ := ⟨⟨x₀, by rw [hδdom]; exact hx₀M⟩, hδbot⟩
  have hδcpc : ClosedProperConvexFn δ := hδpoly.closedProperConvexFn hδproper
  have hx₀δ : x₀ ∈ convexDom δ := by rw [hδdom]; exact hx₀M
  -- `h = δ + f` is polyhedral and proper, with `dom h = M ∩ dom f`
  have hhpoly : PolyhedralFn (δ + f) := PolyhedralFn.add hδpoly hf hδbot hpf.ne_bot
  have hhbot : ∀ x, (δ + f) x ≠ ⊥ := fun x =>
    EReal.add_ne_bot_iff.2 ⟨hδbot x, hpf.ne_bot x⟩
  have hhdom : convexDom (δ + f) = (MA : Set E) ∩ convexDom f := by
    rw [convexDom_add hδbot hpf.ne_bot, hδdom]
  have hx₀h : x₀ ∈ convexDom (δ + f) := by rw [hhdom]; exact ⟨hx₀M, hxf⟩
  have hhproper : ProperConvex (δ + f) := ⟨⟨x₀, hx₀h⟩, hhbot⟩
  have hhcpc : ClosedProperConvexFn (δ + f) := hhpoly.closedProperConvexFn hhproper
  -- the relative-interior step
  obtain ⟨x₁, hx₁h, hx₁g⟩ :=
    relint_inter_relint_nonempty_of_subset_affineSpan
      (PolyhedralFn.convexFn hhpoly).convex_convexDom hg.convex.convex_convexDom
      (by rw [hhdom]; exact fun x hx => hx.1) hx₀h hxg
  -- the three exact splittings
  have hAg : IsExactSum B (δ + f) g := IsExactSum.of_relint_closed hhcpc hg hx₁h hx₁g
  have hδf : IsExactSum B δ f := IsExactSum.of_polyhedral_pair hδpoly hδproper hf hpf hx₀δ hxf
  have hx₀riδ : x₀ ∈ ri (convexDom δ) := by
    rw [hδdom, AffineSubspace.intrinsicInterior_coe]; exact hx₀M
  have hδg : IsExactSum B δ g := IsExactSum.of_relint_closed hδcpc hg hx₀riδ hxg
  -- `δ` is absorbed on both sides
  have hsumδg : δ + g = g := indicatorFn_add_eq_self hdomgM
  have hsum : δ + f + g = f + g := by
    rw [add_assoc]
    exact indicatorFn_add_eq_self
      (by rw [convexDom_add hpf.ne_bot hg.proper.ne_bot]; exact fun x hx => hdomgM hx.2)
  have hδne : ∀ y : F, convexConj B δ y ≠ ⊥ :=
      fun y => convexConj_ne_bot hδproper.convexDom_nonempty y
  have hgne : ∀ y : F, convexConj B g y ≠ ⊥ :=
      fun y => convexConj_ne_bot hg.proper.convexDom_nonempty y
  have hgconj : convexConj B g = infConv (convexConj B δ) (convexConj B g) := by
    have h0 := hδg.convexConj_add
    rwa [hsumδg] at h0
  refine ⟨hpf, hg.proper, fun y => ?_⟩
  obtain ⟨z₁, z₂, hz, hzle⟩ := hAg.exact_le y
  obtain ⟨u, v, huv, huvle⟩ := hδf.exact_le z₁
  have habs : convexConj B g (u + z₂) ≤ convexConj B δ u + convexConj B g z₂ := by
    have hle := infConv_le_add (f := convexConj B δ) (g := convexConj B g) hδne hgne (u + z₂) z₂
    rw [add_sub_cancel_right] at hle
    calc convexConj B g (u + z₂) = infConv (convexConj B δ) (convexConj B g) (u + z₂) :=
        by rw [← hgconj]
      _ ≤ convexConj B δ u + convexConj B g z₂ := hle
  refine ⟨v, u + z₂, ?_, ?_⟩
  · rw [← hz, ← huv]; abel
  · calc convexConj B f v + convexConj B g (u + z₂)
        ≤ convexConj B f v + (convexConj B δ u + convexConj B g z₂) := add_le_add le_rfl habs
      _ = convexConj B δ u + convexConj B f v + convexConj B g z₂ := by
          rw [← add_assoc, add_comm (convexConj B f v)]
      _ ≤ convexConj B (δ + f) z₁ + convexConj B g z₂ := add_le_add huvle le_rfl
      _ ≤ convexConj B (δ + f + g) y := hzle
      _ = convexConj B (f + g) y := by rw [hsum]

/-- Let $E$ and $F$ be finite-dimensional real normed spaces with a pairing under which each space
represents all continuous linear functionals on the other. Let
$f \colon E \to [-\infty, +\infty]$ be a proper polyhedral convex function, let
$g \colon E \to [-\infty, +\infty]$ be a proper convex function, and let $x_0 \in
\operatorname{dom} f \cap \operatorname{ri}(\operatorname{dom} g)$. Then $f$ and $g$ add
exactly: for every $y \in F$, $$(f + g)^*(y) = \min_{y_1 + y_2 = y} \big( f^*(y_1) + g^*(y_2)
\big).$$

This is the case $m = 2$, $k = 1$ of Theorem 20.1 of [rockafellar1970convex]. Neither closedness
of $g$ nor a relative interior point of $\operatorname{dom} f$ is needed. The proof reduces to
`ConvexAnalysis.IsExactSum.of_polyhedral_closed` through
`ConvexAnalysis.convexConj_add_eq_convexConj_convexCl_add_convexCl`. The two hypotheses of that
lemma hold for different reasons: $f$ is closed and proper, so $x_0 \in \operatorname{dom} f$ is
enough, and $g$ is proper and convex, with $x_0 \in \operatorname{ri}(\operatorname{dom} g)$.
This asymmetry is the asymmetry of the theorem. -/
theorem IsExactSum.of_polyhedral [IsCompatiblePairing B] [IsCompatiblePairing B.flip]
    (hf : PolyhedralFn f) (hpf : ProperConvex f) (hg : ConvexFn g) (hpg : ProperConvex g)
    {x₀ : E} (hxf : x₀ ∈ convexDom f) (hxg : x₀ ∈ ri (convexDom g)) : IsExactSum B f g := by
  have hfc : ClosedProperConvexFn f := hf.closedProperConvexFn hpf
  have hcl : convexCl f = f := hfc.closed
  refine IsExactSum.of_convexCl hpf hpg ?_
    (convexConj_add_eq_convexConj_convexCl_add_convexCl hfc.convex hpf hg hpg
      (hfc.tendstoConvexClAlongSegment hxf) (hg.tendstoConvexClAlongSegment hpg hxg))
  rw [hcl]
  exact IsExactSum.of_polyhedral_closed hf hpf
    ⟨convexFn_convexCl hg, closedConvex_convexCl g, hg.properConvex_convexCl hpg⟩ hxf
    (by rw [hg.relint_convexDom_convexCl hpg]; exact hxg)

end Sum

/-! ### Exact addition of $m$ summands -/

section FinsetSum

variable {ι : Type*} {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {s t u : Finset ι} {f : ι → E → EReal}

/-- **The case of $m$ polyhedral functions.** Let $E$ and $F$ be finite-dimensional real normed
spaces with a pairing under which each space represents all continuous linear functionals on the
other. Let $s$ be a nonempty finite set and let $f_i$, $i \in s$, be proper polyhedral convex
functions on $E$ whose effective domains have a common point $x_0$. Then the family
$(f_i)_{i \in s}$ adds exactly: for every $y \in F$ there are $y_i \in F$ with
$\sum_{i \in s} y_i = y$ and $$\sum_{i \in s} f_i^*(y_i) \le \Big( \sum_{i \in s} f_i
\Big)^*(y).$$
-/
theorem IsExactFinsetSum.of_polyhedral_pair [IsCompatiblePairing B] [IsCompatiblePairing B.flip]
    (hs : s.Nonempty) (hpoly : ∀ i ∈ s, PolyhedralFn (f i)) (hpf : ∀ i ∈ s, ProperConvex (f i))
    {x₀ : E} (hx₀ : ∀ i ∈ s, x₀ ∈ convexDom (f i)) : IsExactFinsetSum B s f := by
  induction s using Finset.cons_induction with
  | empty => exact absurd hs (by simp)
  | cons i t hi ih =>
    have hmt : ∀ j ∈ t, j ∈ Finset.cons i t hi := fun j hj => Finset.mem_cons_of_mem hj
    rcases Finset.eq_empty_or_nonempty t with rfl | htne
    · rw [Finset.cons_empty]
      exact IsExactFinsetSum.singleton (hpf i (by simp))
    refine IsExactFinsetSum.cons hi ?_
      (ih htne (fun j hj => hpoly j (hmt j hj)) (fun j hj => hpf j (hmt j hj))
        (fun j hj => hx₀ j (hmt j hj)))
    obtain ⟨-, hprop, hdom⟩ :=
      properConvexFn_finsetSum (fun j hj => (hpoly j (hmt j hj)).convexFn)
        (fun j hj => hpf j (hmt j hj)) (fun j hj => hx₀ j (hmt j hj))
    refine IsExactSum.of_polyhedral_pair (hpoly i (by simp)) (hpf i (by simp))
      (PolyhedralFn.finsetSum htne (fun j hj => hpoly j (hmt j hj))
        (fun j hj x => (hpf j (hmt j hj)).ne_bot x)) hprop (hx₀ i (by simp)) ?_
    rw [hdom]
    exact Set.mem_iInter₂.2 fun j hj => hx₀ j (hmt j hj)

/-- Let $E$ and $F$ be finite-dimensional real normed spaces with a pairing under which each space
represents all continuous linear functionals on the other. Let $s$ be a nonempty finite set that
is the disjoint union of $t$ and $u$. Let $f_i$, $i \in s$, be proper convex functions on $E$,
with $f_i$ polyhedral for $i \in t$. Suppose that there is a point $x_0$ with
$x_0 \in \operatorname{dom} f_i$ for every $i \in t$ and $x_0 \in
\operatorname{ri}(\operatorname{dom} f_i)$ for every $i \in u$. Then the family
$(f_i)_{i \in s}$ adds exactly: for every $y \in F$, $$\Big( \sum_{i \in s} f_i \Big)^*(y) =
\min \Big\{ \sum_{i \in s} f_i^*(y_i) \Bigm| \sum_{i \in s} y_i = y \Big\}.$$

This is Theorem 20.1 of [rockafellar1970convex], with $t = \{1, \dots, k\}$ and
$u = \{k + 1, \dots, m\}$. The condition there reads $$\operatorname{dom} f_1 \cap \dots \cap
\operatorname{dom} f_k \cap \operatorname{ri}(\operatorname{dom} f_{k+1}) \cap \dots \cap
\operatorname{ri}(\operatorname{dom} f_m) \ne \emptyset.$$

The splitting of $s$ is stated by membership, $i \in s \iff i \in t \lor i \in u$, rather than
as $s = t \cup u$, so that no `DecidableEq` instance enters the statement. The sum
$\sum_{i \in t} f_i$ is polyhedral and adds exactly to $\sum_{i \in u} f_i$ by the binary case.
Each of the two blocks adds exactly on its own: the polyhedral block by the case of $m$
polyhedral functions, and the other by the relative-interior criterion. -/
theorem IsExactFinsetSum.of_polyhedral [IsCompatiblePairing B] [IsCompatiblePairing B.flip]
    (hs : s.Nonempty) (hdisj : Disjoint t u) (hmem : ∀ i, i ∈ s ↔ i ∈ t ∨ i ∈ u)
    (hpoly : ∀ i ∈ t, PolyhedralFn (f i)) (hconv : ∀ i ∈ u, ConvexFn (f i))
    (hpf : ∀ i ∈ s, ProperConvex (f i)) {x₀ : E} (hxt : ∀ i ∈ t, x₀ ∈ convexDom (f i))
    (hxu : ∀ i ∈ u, x₀ ∈ ri (convexDom (f i))) : IsExactFinsetSum B s f := by
  have hts : ∀ i ∈ t, i ∈ s := fun i hi => (hmem i).2 (Or.inl hi)
  have hus : ∀ i ∈ u, i ∈ s := fun i hi => (hmem i).2 (Or.inr hi)
  rcases Finset.eq_empty_or_nonempty t with rfl | htne
  · have hsu : s = u := Finset.ext fun i => by simpa using hmem i
    subst hsu
    exact IsExactFinsetSum.of_relint hs hconv hpf hxu
  rcases Finset.eq_empty_or_nonempty u with rfl | hune
  · have hst : s = t := Finset.ext fun i => by simpa using hmem i
    subst hst
    exact IsExactFinsetSum.of_polyhedral_pair hs hpoly hpf hxt
  obtain ⟨-, hpropt, hdomt⟩ :=
    properConvexFn_finsetSum (fun i hi => (hpoly i hi).convexFn) (fun i hi => hpf i (hts i hi)) hxt
  obtain ⟨hconvu, hpropu, -⟩ :=
    properConvexFn_finsetSum hconv (fun i hi => hpf i (hus i hi))
      (fun i hi => intrinsicInterior_subset (hxu i hi))
  refine IsExactFinsetSum.of_split hdisj hmem
    (IsExactFinsetSum.of_polyhedral_pair htne hpoly (fun i hi => hpf i (hts i hi)) hxt)
    (IsExactFinsetSum.of_relint hune hconv (fun i hi => hpf i (hus i hi)) hxu) ?_
  refine IsExactSum.of_polyhedral
    (PolyhedralFn.finsetSum htne hpoly (fun i hi x => (hpf i (hts i hi)).ne_bot x)) hpropt
    hconvu hpropu ?_
    (mem_relint_convexDom_finsetSum hconv (fun i hi => hpf i (hus i hi)) hxu)
  rw [hdomt]
  exact Set.mem_iInter₂.2 hxt

end FinsetSum

section Image

variable {E F G H : Type*}
  [AddCommGroup E] [Module ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {B' : G →ₗ[ℝ] H →ₗ[ℝ] ℝ}
  {A : E →ₗ[ℝ] G} {A' : H →ₗ[ℝ] F} {g : G → EReal}

/-- **The polyhedral case for an inverse image.** Let $E$ be a real vector space, and let $F$, $G$
and $H$ be finite-dimensional real normed spaces. Let $\langle \cdot, \cdot \rangle$ pair $E$
with $F$ and $\langle \cdot, \cdot \rangle'$ pair $G$ with $H$, such that every continuous
linear functional on $G$ is $\langle \cdot, z \rangle'$ for some $z \in H$ and every continuous
linear functional on $F$ is $\langle x, \cdot \rangle$ for some $x \in E$. Let
$A \colon E \to G$ and $A' \colon H \to F$ be linear maps with $\langle Ax, z \rangle' = \langle
x, A'z \rangle$. Let $g \colon G \to [-\infty, +\infty]$ be a proper polyhedral convex function,
and let $Ax_0 \in \operatorname{dom} g$ for some $x_0 \in E$. Then $g$ pulls back exactly along
$A$: wherever $(gA)^*(y) < +\infty$, there is a $z \in H$ with $A'z = y$ and
$g^*(z) \le (gA)^*(y)$, so that $(gA)^* = A'(g^*)$ with the infimum attained.

No relative interior is needed, as for sums. The proof uses none of the theory of sums. The
conjugate $g^*$ is polyhedral, so $A'(g^*)$ is polyhedral and therefore closed, and the closure
in the general formula for the image changes nothing. The same fact gives the attainment of the
infimum over the fibre. Properness of $g$ is used twice: it makes $g$ closed, and
$Ax_0 \in \operatorname{dom} g$ prevents $(gA)^*$ from taking the value $-\infty$. -/
theorem IsExactImage.of_polyhedral [IsCompatiblePairing B'] [IsCompatiblePairing B.flip]
    (hA : IsAdjointPair B B' A A') (hg : PolyhedralFn g) (hp : ProperConvex g)
    {x₀ : E} (hx₀ : A x₀ ∈ convexDom g) :
    IsExactImage B B' A A' hA g := by
  have hconjpoly : PolyhedralFn (convexConj B' g) := PolyhedralFn.convexConj hg
  have hmappoly : PolyhedralFn (mapLin A' (convexConj B' g)) := PolyhedralFn.mapLin hconjpoly A'
  have hne : (convexDom (compLin g A)).Nonempty := ⟨x₀, by rwa [mem_convexDom, compLin_apply]⟩
  have hbot : ∀ y, convexConj B (compLin g A) y ≠ ⊥ := fun y => convexConj_ne_bot hne y
  have hmapbot : ∀ y, mapLin A' (convexConj B' g) y ≠ ⊥ := fun y hy =>
    hbot y (le_bot_iff.1 (hy ▸ convexConj_compLin_le_mapLin hA g y))
  have heq : convexConj B (compLin g A) = mapLin A' (convexConj B' g) := by
    rw [convexConj_compLin_eq_convexCl_mapLin hA hg.convexFn (hg.closedConvex hp.ne_bot)]
    exact hmappoly.closedConvex hmapbot
  refine ⟨hp, fun y hy => ?_⟩
  rw [heq] at hy ⊢
  obtain ⟨μ, hμ⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hmapbot y) hy
  obtain ⟨z, hz, hzeq⟩ := exists_mapLin_eq_of_polyhedralFn hconjpoly A' hμ
  exact ⟨z, hz, le_of_eq hzeq⟩

end Image

end ConvexAnalysis
