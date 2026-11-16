/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Duality.Level
import Numlib.Analysis.Convex.Subdifferential.LegendreType

/-!
# Co-finiteness and the growth of the gradient

Let $E$ be a finite-dimensional real inner product space, and let $f : E \to \mathbb{R}$ be convex
and differentiable on all of $E$. A closed proper convex function is **co-finite**
(`ConvexAnalysis.Cofinite`) when its recession function is $+\infty$ in every nonzero direction, or
equivalently when its conjugate $f^*$ is finite everywhere. This module proves that $f$ is co-finite
if and only if $\|\nabla f(x_i)\| \to \infty$ for every sequence with $\|x_i\| \to \infty$. This is
Lemma 26.7 of [rockafellar1970convex]. The criterion turns a condition on the recession function, or
on $\operatorname{dom} f^*$, into a condition on the gradient map alone.

## Main results

* `ConvexAnalysis.forall_tendsto_norm_atTop_iff_isBounded`: for any map $g$, the condition
  "$\|g(x_i)\| \to \infty$ whenever $\|x_i\| \to \infty$" is equivalent to boundedness of every set
  $\{x \mid \|g(x)\| \le b\}$.
* `ConvexAnalysis.isBounded_setOf_norm_gradient_le_of_convexDom_convexConj_eq_univ`: if
  $\operatorname{dom} f^* = E$, the sets $\{x \mid \|\nabla f(x)\| \le b\}$ are bounded.
* `ConvexAnalysis.convexDom_convexConj_eq_univ_of_isBounded`: conversely, if these sets are bounded,
  then $\operatorname{dom} f^* = E$.
* `ConvexAnalysis.cofinite_iff_forall_tendsto_norm_gradient_atTop`: the criterion. This is Lemma
  26.7 of [rockafellar1970convex].

## Proof outline

If $\operatorname{dom} f^* = E$, the set $\{x \mid \|\nabla f(x)\| \le b\}$ lies in the image under
$\partial f^*$ of the closed ball of radius $b$, which is compact. For the converse, the proof shows
that the range $D = \nabla f(E)$ is open and closed in the connected space $E$; it does not use the
case analysis at a boundary point of $\operatorname{dom} f^*$ of [rockafellar1970convex]. For
openness, let $n \ne 0$ be normal to $\operatorname{dom} f^*$ at $v = \nabla f(x)$. Then the whole
half-line $x + t n$, $t \ge 0$, lies in $\partial f^*(v)$, so every point of it has gradient $v$,
and $\{y \mid \|\nabla f(y)\| \le \|v\|\}$ is unbounded.

## Implementation notes

* The function is $f : E \to [-\infty, +\infty]$ with the hypotheses that $f$ is proper and convex,
  $\operatorname{dom} f = E$, and $f$ is differentiable at every point
  (`ConvexAnalysis.DifferentiableAtFn`). The gradient is `gradient (fun w => (f w).toReal)`.
* The conjugate is taken for the inner product `innerₗ E`.
-/

namespace ConvexAnalysis

open Filter Metric Topology Set

/-! ### Sequences that tend to infinity and bounded level sets -/

section Metric

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

/-- Let $E$ and $F$ be normed additive groups, and let $g : E \to F$ be any map. Then the following
are equivalent:

* $\|g(x_i)\| \to \infty$ for every sequence $(x_i)$ in $E$ with $\|x_i\| \to \infty$;
* the set $\{x \in E \mid \|g(x)\| \le b\}$ is bounded for every $b \in \mathbb{R}$.

No convexity and no linearity are needed. -/
theorem forall_tendsto_norm_atTop_iff_isBounded (g : E → F) :
    (∀ xs : ℕ → E, Tendsto (fun i => ‖xs i‖) atTop atTop →
        Tendsto (fun i => ‖g (xs i)‖) atTop atTop)
      ↔ ∀ b : ℝ, Bornology.IsBounded {x : E | ‖g x‖ ≤ b} := by
  constructor
  · intro h b
    by_contra hcon
    rw [isBounded_iff_forall_norm_le] at hcon
    push Not at hcon
    choose xs hxs hxn using fun n : ℕ => hcon (n : ℝ)
    have hxtop : Tendsto (fun i => ‖xs i‖) atTop atTop :=
      tendsto_atTop_mono (fun i => (hxn i).le) tendsto_natCast_atTop_atTop
    obtain ⟨i, hi⟩ := ((h xs hxtop).eventually_ge_atTop (b + 1)).exists
    have hbi : ‖g (xs i)‖ ≤ b := hxs i
    linarith
  · intro h xs hxs
    rw [Filter.tendsto_atTop]
    intro b
    obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 (h b)
    filter_upwards [hxs.eventually_gt_atTop R] with i hi
    by_contra hcon
    exact absurd (hR (xs i) (not_le.1 hcon).le) (by linarith)

end Metric

/-! ### The gradient criterion for co-finiteness -/

section GradientCriterion

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal}

/-- Let $E$ be a finite-dimensional real inner product space, let $f : E \to [-\infty, +\infty]$ be
proper and convex with $\operatorname{dom} f = E$, and let $f$ be differentiable at every point.
If $\operatorname{dom} f^* = E$, then for every $b \in \mathbb{R}$ the set
$$\{x \in E \mid \|\nabla f(x)\| \le b\}$$
is bounded.

This is the easy half of `ConvexAnalysis.cofinite_iff_forall_tendsto_norm_gradient_atTop`. The
set lies in the image under $\partial f^*$ of the closed ball of radius $b$, which is compact. -/
theorem isBounded_setOf_norm_gradient_le_of_convexDom_convexConj_eq_univ (hf : ConvexFn f)
    (hp : ProperConvex f)
    (hdom : convexDom f = univ) (hdiff : ∀ z : E, DifferentiableAtFn f z)
    (hdc : convexDom (convexConj (innerₗ E) f) = univ) (b : ℝ) :
    Bornology.IsBounded {x : E | ‖gradient (fun w => (f w).toReal) x‖ ≤ b} := by
  have hcl : ClosedConvex f := closedConvex_of_convexDom_eq_univ hf hp hdom
  have hes : EssentiallySmooth f := essentiallySmooth_of_convexDom_eq_univ hdom hdiff
  have hgcpc : ClosedProperConvexFn (convexConj (innerₗ E) f) :=
    ⟨convexFn_convexConj _ f, closedConvex_convexConj, properConvex_convexConj ⟨hf, hcl, hp⟩⟩
  have hcomp := isCompact_image_subgradientRel hgcpc (isCompact_closedBall (0 : E) b)
    (by rw [hdc, interior_univ]; exact subset_univ _)
  refine hcomp.isBounded.subset fun x hx => ⟨gradient (fun w => (f w).toReal) x, ?_, ?_⟩
  · exact mem_closedBall_zero_iff.2 hx
  · rw [mem_subgradientRel, mem_subdifferential_convexConj_innerL_iff hf hcl,
      ← hasGradientAtFn_toDual_iff_mem_subdifferential hf hp hcl hes]
    exact (hdiff x).hasGradientAtFn_gradient

/-- Let $f$ be proper and convex with $\operatorname{dom} f = E$, differentiable at every point, and
let every set $\{x \mid \|\nabla f(x)\| \le b\}$ be bounded. Then the range of $\nabla f$ lies
in $\operatorname{int}(\operatorname{dom} f^*)$.

This is the first step of the hard half. A nonzero vector $n$ normal to $\operatorname{dom} f^*$
at $v = \nabla f(x)$ can be added to $x$ with any nonnegative coefficient without leaving
$\partial f^*(v)$. So the whole half-line $x + t n$ has gradient $v$, and
$\{y \mid \|\nabla f(y)\| \le \|v\|\}$ is unbounded. The range of $\nabla f$ is
`ConvexAnalysis.gradientRange f`. -/
theorem gradientRange_subset_interior_convexDom_convexConj_of_isBounded (hf : ConvexFn f)
    (hp : ProperConvex f)
    (hdom : convexDom f = univ) (hdiff : ∀ z : E, DifferentiableAtFn f z)
    (hbd : ∀ b : ℝ, Bornology.IsBounded {x : E | ‖gradient (fun w => (f w).toReal) x‖ ≤ b}) :
    gradientRange f ⊆ interior (convexDom (convexConj (innerₗ E) f)) := by
  have hcl : ClosedConvex f := closedConvex_of_convexDom_eq_univ hf hp hdom
  have hes : EssentiallySmooth f := essentiallySmooth_of_convexDom_eq_univ hdom hdiff
  intro v hv
  refine mem_interior_of_normalCone_eq_zero
      (B := innerₗ E) (convexFn_convexConj _ f).convex_convexDom
    (gradientRange_subset_convexDom_convexConj hf hp hcl hes hv) ?_
  refine eq_singleton_iff_unique_mem.2 ⟨fun z _ => by simp, fun n hn => ?_⟩
  by_contra hn0
  -- A point of `∂f*(v)`: `v` is a gradient of `f`, so `∂f*(v)` is non-empty.
  obtain ⟨x, hx⟩ : (subdifferential (innerₗ E) (convexConj (innerₗ E) f) v).Nonempty := by
    rw [← mem_domSubdifferential, ← gradientRange_eq_domSubdifferential_convexConj hf hp hcl hes]
    exact hv
  -- The half-line `x + t n` stays inside `∂f*(v)`, so its gradient is constantly `v`.
  have hline : ∀ t : ℝ, 0 ≤ t → ‖gradient (fun w => (f w).toReal) (x + t • n)‖ = ‖v‖ := by
    intro t ht
    have hsmul : t • n ∈ normalCone (innerₗ E) (convexDom (convexConj (innerₗ E) f)) v := by
      intro z hz
      rw [map_smul, smul_eq_mul]
      exact mul_nonpos_of_nonneg_of_nonpos ht (hn z hz)
    have hmem :=
        subdifferential_add_normalCone_convexDom_subset (innerₗ E) (convexConj (innerₗ E) f) v
      (Set.add_mem_add hx hsmul)
    rw [mem_subdifferential_convexConj_innerL_iff hf hcl,
      ← hasGradientAtFn_toDual_iff_mem_subdifferential hf hp hcl hes] at hmem
    rw [hmem.gradient_toReal_eq, LinearIsometryEquiv.symm_apply_apply]
  -- Which contradicts boundedness of the sublevel set at height `‖v‖`.
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 (hbd ‖v‖)
  have hx0 : ‖gradient (fun w => (f w).toReal) x‖ = ‖v‖ := by simpa using hline 0 le_rfl
  have hxR : ‖x‖ ≤ R := hR x hx0.le
  have hnpos : 0 < ‖n‖ := norm_pos_iff.2 hn0
  have hRnn : 0 ≤ R := le_trans (norm_nonneg x) hxR
  set t : ℝ := (R + ‖x‖ + 1) / ‖n‖ with ht
  have htpos : 0 ≤ t := div_nonneg (by linarith [norm_nonneg x]) hnpos.le
  have hle := hR (x + t • n) (le_of_eq (hline t htpos))
  have hnorm : ‖t • n‖ = R + ‖x‖ + 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg htpos, ht, div_mul_cancel₀ _ hnpos.ne']
  have hsub : ‖t • n‖ ≤ ‖x + t • n‖ + ‖x‖ := by
    simpa using norm_sub_le (x + t • n) x
  rw [hnorm] at hsub
  linarith

/-- Let $f$ be proper and convex with $\operatorname{dom} f = E$, differentiable at every point, and
let every set $\{x \mid \|\nabla f(x)\| \le b\}$ be bounded. Then the range of $\nabla f$ is
closed.

This is the second step of the hard half. A convergent sequence of gradients is bounded, so the
points where they are taken lie in one bounded set $\{x \mid \|\nabla f(x)\| \le b\}$, and the
limit of a convergent subsequence of these points has the limit gradient as its gradient. -/
theorem isClosed_gradientRange_of_isBounded (hf : ConvexFn f) (hp : ProperConvex f)
    (hdom : convexDom f = univ) (hdiff : ∀ z : E, DifferentiableAtFn f z)
    (hbd : ∀ b : ℝ, Bornology.IsBounded {x : E | ‖gradient (fun w => (f w).toReal) x‖ ≤ b}) :
    IsClosed (gradientRange f) := by
  have hes : EssentiallySmooth f := essentiallySmooth_of_convexDom_eq_univ hdom hdiff
  have hcont : Continuous (gradient fun w => (f w).toReal) := by
    rw [← continuousOn_univ, ← interior_univ, ← hdom]
    exact continuousOn_gradient_interior_convexDom hf hp hes
  refine IsSeqClosed.isClosed fun {vs v} hvs hlim => ?_
  choose xs hxs using hvs
  have hgrad : ∀ n, gradient (fun w => (f w).toReal) (xs n) = vs n := fun n => by
    rw [(hxs n).gradient_toReal_eq, LinearIsometryEquiv.symm_apply_apply]
  obtain ⟨b, hb⟩ := isBounded_iff_forall_norm_le.1 (Metric.isBounded_range_of_tendsto vs hlim)
  obtain ⟨R, hR⟩ := (isBounded_iff_subset_closedBall (0 : E)).1 (hbd b)
  have hmem : ∀ n, xs n ∈ closedBall (0 : E) R := fun n =>
    hR (show ‖gradient (fun w => (f w).toReal) (xs n)‖ ≤ b by
      rw [hgrad n]; exact hb _ ⟨n, rfl⟩)
  obtain ⟨a, -, φ, hφ, hφlim⟩ := (isCompact_closedBall (0 : E) R).tendsto_subseq hmem
  have hva : gradient (fun w => (f w).toReal) a = v := by
    refine tendsto_nhds_unique ((hcont.tendsto a).comp hφlim) ?_
    exact (hlim.comp hφ.tendsto_atTop).congr fun n => (hgrad (φ n)).symm
  exact ⟨a, hva ▸ (hdiff a).hasGradientAtFn_gradient⟩

/-- Let $E$ be a finite-dimensional real inner product space, let $f : E \to [-\infty, +\infty]$ be
proper and convex with $\operatorname{dom} f = E$, and let $f$ be differentiable at every point.
If the set $\{x \in E \mid \|\nabla f(x)\| \le b\}$ is bounded for every $b \in \mathbb{R}$,
then $\operatorname{dom} f^* = E$.

This is the hard half of `ConvexAnalysis.cofinite_iff_forall_tendsto_norm_gradient_atTop`. The
range $\nabla f(E)$ is nonempty, open and closed, and $E$ is connected, so $\nabla f(E) = E$.
With the first step, $E \subseteq \operatorname{int}(\operatorname{dom} f^*)$. -/
theorem convexDom_convexConj_eq_univ_of_isBounded (hf : ConvexFn f) (hp : ProperConvex f)
    (hdom : convexDom f = univ)
    (hdiff : ∀ z : E, DifferentiableAtFn f z)
    (hbd : ∀ b : ℝ, Bornology.IsBounded {x : E | ‖gradient (fun w => (f w).toReal) x‖ ≤ b}) :
    convexDom (convexConj (innerₗ E) f) = univ := by
  have hcl : ClosedConvex f := closedConvex_of_convexDom_eq_univ hf hp hdom
  have hes : EssentiallySmooth f := essentiallySmooth_of_convexDom_eq_univ hdom hdiff
  have hne : (gradientRange f).Nonempty := ⟨_, (hdiff 0).hasGradientAtFn_gradient.mem_gradientRange⟩
  have hsub := gradientRange_subset_interior_convexDom_convexConj_of_isBounded hf hp hdom hdiff hbd
  have heq : gradientRange f = interior (convexDom (convexConj (innerₗ E) f)) :=
    Subset.antisymm hsub
      ((Convex.interior_subset_relint).trans
        (relint_convexDom_convexConj_subset_gradientRange hf hp hcl hes))
  have hclopen : IsClopen (gradientRange f) :=
    ⟨isClosed_gradientRange_of_isBounded hf hp hdom hdiff hbd, heq ▸ isOpen_interior⟩
  have huniv : interior (convexDom (convexConj (innerₗ E) f)) = univ := heq ▸ hclopen.eq_univ hne
  exact eq_univ_of_univ_subset (huniv.ge.trans interior_subset)

/-- Let $E$ be a finite-dimensional real inner product space, let $f : E \to [-\infty, +\infty]$ be
proper and convex with $\operatorname{dom} f = E$, and let $f$ be differentiable at every point
of $E$. Then $f$ is co-finite if and only if
$$\|\nabla f(x_i)\| \to \infty \quad \text{for every sequence } (x_i) \text{ in } E \text{ with
  } \|x_i\| \to \infty.$$

This is Lemma 26.7 of [rockafellar1970convex]. Co-finiteness is `ConvexAnalysis.Cofinite`: $f$
is closed, proper and convex, and its recession function is $+\infty$ in every nonzero
direction. The gradient is `gradient (fun w => (f w).toReal)`. -/
theorem cofinite_iff_forall_tendsto_norm_gradient_atTop (hf : ConvexFn f) (hp : ProperConvex f)
    (hdom : convexDom f = univ) (hdiff : ∀ z : E, DifferentiableAtFn f z) :
    Cofinite f ↔ ∀ xs : ℕ → E, Tendsto (fun i => ‖xs i‖) atTop atTop →
      Tendsto (fun i => ‖gradient (fun w => (f w).toReal) (xs i)‖) atTop atTop := by
  have hcl : ClosedConvex f := closedConvex_of_convexDom_eq_univ hf hp hdom
  rw [cofinite_iff_convexDom_convexConj_eq_univ (B := innerₗ E) ⟨hf, hcl, hp⟩,
    forall_tendsto_norm_atTop_iff_isBounded]
  exact ⟨fun h => isBounded_setOf_norm_gradient_le_of_convexDom_convexConj_eq_univ hf hp hdom
      hdiff h,
    convexDom_convexConj_eq_univ_of_isBounded hf hp hdom hdiff⟩

end GradientCriterion

end ConvexAnalysis
