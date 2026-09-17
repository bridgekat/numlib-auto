/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Normed.Operator.Unbounded.Adjoint`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Numlib.Analysis.Normed.Operator.Unbounded.Adjoint

/-!
# The Banach adjoint between reflexive spaces: `D(A*)` is dense and `A** = A`

For a densely defined closed operator `A : D(A) ⊆ E → F` between reflexive Banach spaces over
`RCLike 𝕜`, the Banach adjoint `A* : D(A*) ⊆ F* → E*` (`LinearPMap.strongDualAdjoint`) is itself
densely defined, so that its adjoint `A** : D(A**) ⊆ E** → F**` is meaningful, and `A**` is `A`
read through the canonical embeddings `J_E : E → E**`, `J_F : F → F**`
(`NormedSpace.inclusionInDoubleDual`):

* `LinearPMap.dense_domain_strongDualAdjoint` — `D(A*)` is dense in `F*` when `F` is reflexive
  ([brezis2011functional], Theorem 3.24, first clause; without reflexivity only the weak-∗
  density `LinearPMap.IsClosed.dense_toWeakDual_domain_strongDualAdjoint` holds, Remark 2.15).
* `LinearPMap.graph_strongDualAdjoint_strongDualAdjoint` — `G(A**) = (J_E × J_F)(G(A))`, i.e.
  `D(A**) = J_E(D(A))` and `A** (J_E u) = J_F (A u)` (Theorem 3.24, second clause, "`A** = A`").

Both proofs are direct separation arguments from the closed graph of `A`, packaged in
`LinearPMap.IsClosed.exists_apply_ne_strongDualAdjoint_apply_of_notMem_graph`: a functional on
`F*` vanishing on `D(A*)` is, by reflexivity, evaluation at some `y ∈ F`, and `D(A*)` separates
the points of `F`; and a pair `(J_E u, J_F y)` in `G(A**)`, which means `v y = (A* v) u` for all
`v ∈ D(A*)`, has `(u, y) ∈ G(A)` because otherwise some `v ∈ D(A*)` would separate them. The
book's route through the orthogonality relations `I[G(A*)] = G(A)^⊥`, `I[G(A**)] = G(A*)^⊥`
(`LinearPMap.map_graph_strongDualAdjoint_eq_annihilator_graph`) and the reflexive bipolar
identity in `E × F` is not needed.

Reflexivity is `NormedSpace.IsReflexive` of `Numlib.Analysis.Normed.Module.Reflexive`; only the
reflexivity of `F` is used for the density, and that of both spaces for the identification.
No completeness hypothesis appears, since reflexive spaces are complete.

## References

[brezis2011functional], Theorem 3.24, and Remarks 2.15 and 2.17.
-/

open NormedSpace

namespace LinearPMap

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {A : E →ₗ.[𝕜] F}

/-- **`D(A*)` is dense when `F` is reflexive** ([brezis2011functional], Theorem 3.24, first
clause), for a closed densely defined `A : D(A) ⊆ E → F`. A functional `φ ∈ F**` vanishing on
`D(A*)` is evaluation at some `y ∈ F` by reflexivity, and `D(A*)` separates the points of `F`
(`LinearPMap.IsClosed.exists_mem_domain_strongDualAdjoint_apply_ne_zero`), so `y = 0` and
`φ = 0`; the annihilator of `D(A*)` is therefore trivial, which is density. Only the
reflexivity of `F` is used. -/
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

/-- **`A** = A` between reflexive spaces** ([brezis2011functional], Theorem 3.24, second clause):
for a closed densely defined `A : D(A) ⊆ E → F` between reflexive spaces, the graph of the double
adjoint `A** : D(A**) ⊆ E** → F**` is the image of the graph of `A` under the canonical
embeddings, `G(A**) = {(J_E u, J_F (A u)) | u ∈ D(A)}`. The adjoint `A**` is meaningful because
`D(A*)` is dense (`dense_domain_strongDualAdjoint`); `(ξ, η) ∈ G(A**)` means `η v = ξ (A* v)` for
all `v ∈ D(A*)`, and with `ξ = J_E u`, `η = J_F y` this says `v y = (A* v) u`, which by separation
from the closed graph forces `(u, y) ∈ G(A)`. -/
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
