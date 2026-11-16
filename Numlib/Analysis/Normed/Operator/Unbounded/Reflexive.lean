/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Normed.Operator.Unbounded.Adjoint`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Numlib.Analysis.Normed.Operator.Unbounded.Adjoint

/-!
# The adjoint of a closed operator between reflexive spaces

Let $E$ and $F$ be normed spaces over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, and let
$A \colon D(A) \subseteq E \to F$ be a closed operator with $D(A)$ dense in $E$. Let
$A^* \colon D(A^*) \subseteq F^* \to E^*$ be its adjoint (`LinearPMap.strongDualAdjoint`), and let
$J_E \colon E \to E^{**}$ and $J_F \colon F \to F^{**}$ be the canonical embeddings
(`NormedSpace.inclusionInDoubleDual`). If $F$ is reflexive, then $D(A^*)$ is dense in $F^*$, so the
adjoint $A^{**} \colon D(A^{**}) \subseteq E^{**} \to F^{**}$ of $A^*$ is meaningful. If $E$ and $F$
are both reflexive, then $A^{**}$ is $A$ read through the canonical embeddings:
$D(A^{**}) = J_E(D(A))$ and $A^{**}(J_E u) = J_F(Au)$. This is Theorem 3.24 of
[brezis2011functional]; without reflexivity only the weak-$*$ density of $D(A^*)$ holds (Remark
2.15).

## Main results

* `LinearPMap.dense_domain_strongDualAdjoint`: $D(A^*)$ is dense in $F^*$ when $F$ is reflexive.
* `LinearPMap.graph_strongDualAdjoint_strongDualAdjoint`:
  $G(A^{**}) = \{(J_E u, J_F(Au)) : u \in D(A)\}$ when $E$ and $F$ are reflexive.

## Proof outline

Both proofs are direct separation arguments from the closed graph of $A$, packaged in
`LinearPMap.IsClosed.exists_apply_ne_strongDualAdjoint_apply_of_notMem_graph`. For the density, a
functional on $F^*$ that vanishes on $D(A^*)$ is, by reflexivity, the evaluation at some $y \in F$,
and $D(A^*)$ separates the points of $F$. For the graph, a pair $(J_E u, J_F y)$ lies in $G(A^{**})$
if and only if $v(y) = (A^* v)(u)$ for all $v \in D(A^*)$; then $(u, y) \in G(A)$, because otherwise
some $v \in D(A^*)$ would separate them. The route of [brezis2011functional], through the
orthogonality relations $I[G(A^*)] = G(A)^\perp$ and $I[G(A^{**})] = G(A^*)^\perp$
(`LinearPMap.map_graph_strongDualAdjoint_eq_annihilator_graph`) and the bipolar identity in the
reflexive space $E \times F$, is not needed.

## Implementation notes

* Reflexivity is `NormedSpace.IsReflexive` of `Numlib.Analysis.Normed.Module.Reflexive`. Only the
  reflexivity of $F$ is used for the density, and that of both spaces for the identification of
  $A^{**}$.
* No completeness hypothesis appears, since reflexive spaces are complete.
-/

open NormedSpace

namespace LinearPMap

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {A : E →ₗ.[𝕜] F}

/-- Let $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, let $F$ be reflexive, and let
$A \colon D(A) \subseteq E \to F$ be closed with $D(A)$ dense in $E$. Then $D(A^*)$ is dense in
$F^*$. This is the first clause of Theorem 3.24 of [brezis2011functional].

A functional $\varphi \in F^{**}$ that vanishes on $D(A^*)$ is the evaluation at some $y \in F$
by reflexivity. Since $D(A^*)$ separates the points of $F$
(`LinearPMap.IsClosed.exists_mem_domain_strongDualAdjoint_apply_ne_zero`), $y = 0$ and
$\varphi = 0$. So the annihilator of $D(A^*)$ is trivial, which is density. Only the reflexivity
of $F$ is used. -/
theorem dense_domain_strongDualAdjoint [IsReflexive 𝕜 F] (hc : A.IsClosed)
    (hd : Dense (A.domain : Set E)) :
    Dense (A.strongDualAdjoint.domain : Set (StrongDual 𝕜 F)) := by
  rw [← Submodule.strongDualAnnihilator_eq_bot_iff, eq_bot_iff]
  intro φ hφ
  rw [Submodule.mem_strongDualAnnihilator] at hφ
  obtain ⟨y, rfl⟩ := surjective_inclusionInDoubleDual (𝕜 := 𝕜) (V := F) φ
  rw [Submodule.mem_bot]
  by_contra hy0
  have hy : y ≠ 0 := fun h => hy0 (by rw [h, _root_.map_zero])
  obtain ⟨v, hv⟩ := hc.exists_mem_domain_strongDualAdjoint_apply_ne_zero hd hy
  have := hφ v v.2
  rw [dual_def] at this
  exact hv this

/-- $A^{**} = A$ **between reflexive spaces**. Let $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, let
$E$ and $F$ be reflexive, and let $A \colon D(A) \subseteq E \to F$ be closed with $D(A)$ dense
in $E$. Then the graph of the double adjoint $A^{**} \colon D(A^{**}) \subseteq E^{**} \to
F^{**}$ is the image of the graph of $A$ under the canonical embeddings:
$$G(A^{**}) = \{(J_E u, J_F(Au)) : u \in D(A)\}.$$
This is the second clause of Theorem 3.24 of [brezis2011functional].

The adjoint $A^{**}$ is meaningful because $D(A^*)$ is dense
(`LinearPMap.dense_domain_strongDualAdjoint`). A pair $(\xi, \eta)$ lies in $G(A^{**})$ if and
only if $\eta(v) = \xi(A^* v)$ for all $v \in D(A^*)$. With $\xi = J_E u$ and $\eta = J_F y$
this says $v(y) = (A^* v)(u)$, and separation from the closed graph forces $(u, y) \in G(A)$.
The embeddings act on the graph through `LinearMap.prodMap`. -/
theorem graph_strongDualAdjoint_strongDualAdjoint [IsReflexive 𝕜 E] [IsReflexive 𝕜 F]
    (hc : A.IsClosed) (hd : Dense (A.domain : Set E)) :
    A.strongDualAdjoint.strongDualAdjoint.graph =
      A.graph.map ((inclusionInDoubleDual 𝕜 E : E →ₗ[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E)).prodMap
        (inclusionInDoubleDual 𝕜 F : F →ₗ[𝕜] StrongDual 𝕜 (StrongDual 𝕜 F))) := by
  have hd' : Dense (A.strongDualAdjoint.domain : Set (StrongDual 𝕜 F)) :=
    dense_domain_strongDualAdjoint hc hd
  ext ⟨ξ, η⟩
  rw [Submodule.mem_map, mem_graph_strongDualAdjoint_iff hd']
  constructor
  · intro hmem
    obtain ⟨u, rfl⟩ := surjective_inclusionInDoubleDual (𝕜 := 𝕜) (V := E) ξ
    obtain ⟨y, rfl⟩ := surjective_inclusionInDoubleDual (𝕜 := 𝕜) (V := F) η
    refine ⟨(u, y), ?_, rfl⟩
    by_contra hnot
    obtain ⟨v, hv⟩ := hc.exists_apply_ne_strongDualAdjoint_apply_of_notMem_graph hd hnot
    have := hmem v
    rw [dual_def, dual_def] at this
    exact hv this
  · rintro ⟨⟨x, z⟩, hxz, hmap⟩
    simp only [LinearMap.prodMap_apply, ContinuousLinearMap.coe_coe, Prod.mk.injEq] at hmap
    obtain ⟨rfl, rfl⟩ := hmap
    obtain ⟨u, hu, hAu⟩ := (mem_graph_iff A).1 hxz
    simp only at hu hAu
    subst hu hAu
    intro v
    rw [dual_def, dual_def, strongDualAdjoint_apply hd v u]

end LinearPMap
