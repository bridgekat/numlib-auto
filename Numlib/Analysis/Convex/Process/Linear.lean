/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Process.Basic

/-!
# Linear transformations inside the convex algebra

A linear transformation $T : U \to X$ is a single-valued convex process, and
`ConvexAnalysis.ConvexProcess.ofLinearMap` is this embedding. Every operation on convex processes
restricts along it to the corresponding operation on linear maps. The image of a set is the linear
image $TC$, the product of processes is the composition of maps, the image of a function under the
indicator bifunction is the image $(Tf)(x) = \inf \{f(u) \mid Tu = x\}$, and the adjoint of the
process is a transpose $T'$ of the linear map, with $\langle Tu, y \rangle = \langle u, T' y
\rangle$. The presentation follows [rockafellar1970convex], §39.

## Main results

* `ConvexAnalysis.ConvexProcess.image_ofLinearMap`: the image of a set $C$ under the process of $T$
  is $TC$.
* `ConvexAnalysis.ConvexProcess.comp_ofLinearMap`: the product of the processes of $S$ and $T$ is
  the process of $S \circ T$.
* `ConvexAnalysis.ConvexProcess.imageBifun_indicatorBifun_ofLinearMap`: the image of $f$ under the
  indicator bifunction of $T$ is the linear image $Tf$, if $f$ never takes the value $-\infty$.
* `ConvexAnalysis.ConvexProcess.adjointProcess_ofLinearMap`,
  `ConvexAnalysis.ConvexProcess.coadjointProcess_ofLinearMap`: both adjoints of the process of $T$
  are the process of a transpose $T'$, if the pairing of $U$ with $V$ separates the points of $V$.

## Implementation notes

* The adjoints of a convex process, of a bifunction and of a function are defined directly from a
  pair of pairings, and none of them mentions a linear map. A transpose enters only in this module,
  as the hypothesis `ConvexAnalysis.IsAdjointPair Bu Bx T T'`. Between arbitrarily paired spaces a
  linear map need not have a transpose, and when it has one, the transpose is unique only if `Bu` is
  separating on the right (`LinearMap.SeparatingRight`): $\langle u, v \rangle = 0$ for all $u$
  implies $v = 0$.
* The two adjoints `ConvexAnalysis.ConvexProcess.adjointProcess` and
  `ConvexAnalysis.ConvexProcess.coadjointProcess` must be kept apart for a general process. For a
  linear process the graph is a subspace, so the defining inequality at $-u$ reverses the inequality
  at $u$, and both reduce to $\langle Tu, y \rangle = \langle u, v \rangle$. Separation by `Bu`, not
  by `Bx`, determines the answer: without it, the adjoint process is single-valued only up to the
  annihilator of $U$ in $V$.
-/

open Set

namespace ConvexAnalysis

namespace ConvexProcess

/-! ### The set-level dictionary -/

section Sets

variable {U X Z : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]
  [AddCommGroup Z] [Module ℝ Z]

/-- The image of a set $C \subseteq U$ under the process of a linear map $T : U \to X$ is the linear
image $TC = \{Tu \mid u \in C\}$. -/
theorem image_ofLinearMap (T : U →ₗ[ℝ] X) (C : Set U) : (ofLinearMap T).image C = T '' C := by
  ext x
  constructor
  · rintro ⟨u, hu, hx⟩
    exact ⟨u, hu, (mem_graph_ofLinearMap.1 hx).symm⟩
  · rintro ⟨u, hu, hx⟩
    exact ⟨u, hu, mem_graph_ofLinearMap.2 hx.symm⟩

/-- The range of the process of a linear map $T$ is the range of $T$. -/
theorem range_ofLinearMap (T : U →ₗ[ℝ] X) : (ofLinearMap T).range = Set.range T := by
  rw [← image_univ, image_ofLinearMap, Set.image_univ]

/-- For linear maps $T : U \to X$ and $S : X \to Z$, the product of the processes of $S$ and $T$ is
the process of the composition $S \circ T$. -/
theorem comp_ofLinearMap (S : X →ₗ[ℝ] Z) (T : U →ₗ[ℝ] X) :
    (ofLinearMap S).comp (ofLinearMap T) = ofLinearMap (S ∘ₗ T) := by
  ext p
  constructor
  · rintro ⟨x, hx, hz⟩
    exact (mem_graph_ofLinearMap.1 hz).trans (congrArg S (mem_graph_ofLinearMap.1 hx))
  · intro h
    exact ⟨T p.1, rfl, mem_graph_ofLinearMap.2 (mem_graph_ofLinearMap.1 h)⟩

/-- Two linear maps $T_1, T_2 : U \to X$ whose convex processes are equal are themselves equal. -/
theorem ofLinearMap_injective :
    Function.Injective (ofLinearMap : (U →ₗ[ℝ] X) → ConvexProcess U X) := fun T S h => by
  ext u
  have hu : (u, T u) ∈ (ofLinearMap S).graph := h ▸ mem_graph_ofLinearMap.2 rfl
  exact mem_graph_ofLinearMap.1 hu

end Sets

/-! ### The image of a function under a linear process -/

section Image

variable {U X : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]

/-- Let $T : U \to X$ be linear and let $f : U \to [-\infty, +\infty]$ never take the value
$-\infty$. Then the image of $f$ under the indicator bifunction of the process of $T$ is the
linear image of $f$:
$$\inf_u \bigl(f(u) + \delta(x \mid \{Tu\})\bigr) = \inf \{f(u) \mid Tu = x\} \quad \text{for
  all } x \in X.$$

The hypothesis $f(u) \neq -\infty$ is needed. Off the fibre of $T$ the summand is $+\infty$, and
in `EReal` the sum $-\infty + \infty$ is $-\infty$, which would make the infimum $-\infty$ at
every point of $X$. -/
theorem imageBifun_indicatorBifun_ofLinearMap (T : U →ₗ[ℝ] X) {f : U → EReal}
    (hbf : ∀ u, f u ≠ ⊥) :
    imageBifun (ofLinearMap T).indicatorBifun f = mapLin T f := by
  funext x
  rw [imageBifun_apply]
  refine le_antisymm (le_mapLin fun u hu => ?_) (le_iInf fun u => ?_)
  · refine (iInf_le _ u).trans (le_of_eq ?_)
    rw [indicatorBifun_apply, eval_ofLinearMap,
      indicatorFn_of_mem (Set.mem_singleton_iff.2 hu.symm), add_zero]
  · by_cases h : T u = x
    · rw [indicatorBifun_apply, eval_ofLinearMap,
        indicatorFn_of_mem (Set.mem_singleton_iff.2 h.symm), add_zero]
      exact mapLin_le h
    · rw [indicatorBifun_apply, eval_ofLinearMap,
        indicatorFn_of_notMem fun hc => h (Set.mem_singleton_iff.1 hc).symm,
        EReal.add_top_of_ne_bot (hbf u)]
      exact le_top

end Image

/-! ### The adjoint of a linear process -/

section Adjoint

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ} {T : U →ₗ[ℝ] X} {T' : Y →ₗ[ℝ] V}
  {y : Y} {v : V}

/-- For a linear process the adjoint condition is an equation, because the graph is a subspace. -/
private theorem pairing_eq_of_forall_le (h : ∀ u : U, Bx (T u) y ≤ Bu u v) (u : U) :
    Bx (T u) y = Bu u v := by
  refine le_antisymm (h u) ?_
  have hn := h (-u)
  simp only [map_neg, LinearMap.neg_apply] at hn
  linarith

private theorem eq_of_forall_pairing_eq (hB : Bu.SeparatingRight)
    (hA : IsAdjointPair Bu Bx T T') (h : ∀ u : U, Bx (T u) y = Bu u v) : v = T' y := by
  refine sub_eq_zero.1 (hB _ fun u => ?_)
  rw [map_sub (Bu u) v (T' y), sub_eq_zero, ← hA u y, h u]

/-- **The adjoint of a linear process is the process of a transpose.** Let $T : U \to X$ and
$T' : Y \to V$ be linear with $\langle Tu, y \rangle = \langle u, T' y \rangle$ for all
$u \in U$ and $y \in Y$, and suppose that $\langle u, v \rangle = 0$ for all $u \in U$ implies
$v = 0$. Then the adjoint of the process of $T$ is the process of $T'$.

The separation hypothesis on `Bu` makes the answer unique, as it does for the transpose itself. -/
theorem adjointProcess_ofLinearMap (hB : Bu.SeparatingRight) (hA : IsAdjointPair Bu Bx T T') :
    adjointProcess Bu Bx (ofLinearMap T) = ofLinearMap T' := by
  ext q
  constructor
  · intro h
    exact eq_of_forall_pairing_eq hB hA
      (pairing_eq_of_forall_le fun u => h (u, T u) (mem_graph_ofLinearMap.2 rfl))
  · intro h p hp
    have hp' : p.2 = T p.1 := mem_graph_ofLinearMap.1 hp
    have hq : q.2 = T' q.1 := mem_graph_ofLinearMap.1 h
    rw [hp', hq, hA p.1 q.1]

/-- **The infimum-oriented adjoint of a linear process is the process of the same transpose.** Under
the hypotheses of `ConvexAnalysis.ConvexProcess.adjointProcess_ofLinearMap`, the
infimum-oriented adjoint of the process of $T$ is the process of $T'$.

This is `ConvexAnalysis.ConvexProcess.adjointProcess_ofLinearMap` for the negated pairings, for
which $T'$ is still a transpose. -/
theorem coadjointProcess_ofLinearMap (hB : Bu.SeparatingRight) (hA : IsAdjointPair Bu Bx T T') :
    coadjointProcess Bu Bx (ofLinearMap T) = ofLinearMap T' := by
  rw [coadjointProcess_eq_adjointProcess_neg]
  refine adjointProcess_ofLinearMap (fun v hv => hB v fun u => ?_) fun u y => ?_
  · simpa using hv u
  · simp only [LinearMap.neg_apply, hA u y]

end Adjoint

end ConvexProcess

end ConvexAnalysis
