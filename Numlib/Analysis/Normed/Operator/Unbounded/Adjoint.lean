/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Normed.Operator.Unbounded.Adjoint`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Extend
import Mathlib.Topology.Algebra.Module.LinearPMap
import Numlib.Analysis.Normed.Module.WeakClosed

/-!
# The Banach-space adjoint of a bounded and of an unbounded operator

For normed spaces `E`, `F` over a nontrivially normed field `𝕜`, the **adjoint** (transpose) of a
bounded operator `T : E →L[𝕜] F` is the bounded operator `T* : F* → E*`, `T* v = v ∘ T`, between
the strong duals; it satisfies `⟨T* v, u⟩ = ⟨v, T u⟩` and, over `RCLike 𝕜`, `‖T*‖ = ‖T‖`. For an
unbounded operator `A : D(A) ⊆ E → F` (a `LinearPMap`, `E →ₗ.[𝕜] F`) with dense domain, the
adjoint is the unbounded operator `A* : D(A*) ⊆ F* → E*` whose domain consists of those `v ∈ F*`
for which `u ↦ ⟨v, A u⟩` is bounded on `D(A)`, `A* v` being the extension by continuity of that
functional to `E`; the fundamental relation is `⟨A* v, u⟩ = ⟨v, A u⟩` for `u ∈ D(A)`,
`v ∈ D(A*)`. This is [brezis2011functional] §2.6.

Mathlib has the algebraic `LinearMap.dualMap` on `Module.Dual`, the TVS-general precomposition
map `ContinuousLinearMap.precomp`, and the Hilbert-space adjoints `ContinuousLinearMap.adjoint`
and `LinearPMap.adjoint` (`T†`, through the Riesz representation); it has no norm statement
about the Banach transpose and no Banach-space adjoint of an unbounded operator.

## Main definitions

* `ContinuousLinearMap.strongDualMap T : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E` — the bounded
  adjoint `T* v = v.comp T`. It is Mathlib's `ContinuousLinearMap.precomp 𝕜 T` specialised to
  scalar-valued maps (`strongDualMap_eq_precomp`, by `rfl`), so that Mathlib's lemmas about
  `precomp` apply; `strongDualMapₗᵢ` is the map `T ↦ T*` bundled as a linear isometry over
  `RCLike 𝕜`. The name `dualMap` is left free for a future Mathlib addition.
* `LinearPMap.strongDualAdjoint A : StrongDual 𝕜 F →ₗ.[𝕜] StrongDual 𝕜 E` — the unbounded
  adjoint, built exactly like Mathlib's Hilbert-space `LinearPMap.adjoint`: the domain is the
  subspace `{v | Continuous ((v : F →ₗ[𝕜] 𝕜).comp A.toFun)}`, the value on `v` is
  `ContinuousLinearMap.extend` of `u ↦ v (A u)` along the inclusion of `D(A)`, and the map
  `v ↦ A* v` is linear because the extension is unique when `D(A)` is dense; when `D(A)` is not
  dense the values are the junk `0`. Only the completeness of `𝕜` is used, no Hahn–Banach
  ([brezis2011functional], Remark 2.14).

## Main statements

* `LinearPMap.mem_strongDualAdjoint_domain_iff` — `v ∈ D(A*) ↔ ∃ c, ∀ u ∈ D(A), ‖v (A u)‖ ≤ c ‖u‖`
  (the book's definition of the domain).
* `LinearPMap.strongDualAdjoint_apply` — the fundamental relation `(A* v) u = v (A u)`, and
  `strongDualAdjoint_apply_eq`, `mem_strongDualAdjoint_domain_of_exists` — `A* v` is the unique
  `f ∈ E*` with `f u = v (A u)` on `D(A)`, and any such `f` puts `v` in `D(A*)`.
* `LinearPMap.strongDualAdjoint_isClosed` — **the adjoint is closed** (Proposition 2.17).
* `ContinuousLinearMap.toPMap_strongDualAdjoint` — for a bounded operator restricted to a dense
  subspace the two adjoints agree, `D(T*) = F*` and `T* v = v ∘ T` (Remark 2.16).
* `LinearPMap.map_graph_strongDualAdjoint_eq_annihilator_graph` — the graphs are related by
  `I[G(A*)] = G(A)^⊥` with `I (v, f) = (-f, v)`, after the identification
  `(E × F)* ≃ E* × F*`.
* `LinearPMap.IsClosed.exists_apply_ne_strongDualAdjoint_apply_of_notMem_graph` — separation
  of a point `(u, y)` from the closed graph of `A`, read through the adjoint: some `v ∈ D(A*)`
  has `v y ≠ (A* v) u`. Every consequence of closedness below goes through it.
* Corollary 2.18: `LinearPMap.ker_strongDualAdjoint_eq_annihilator_range` (`N(A*) = R(A)^⊥`),
  `LinearPMap.IsClosed.ker_eq_strongDualCoannihilator_range_strongDualAdjoint`
  (`N(A) = R(A*)^⊥`), `LinearPMap.closure_range_strongDualAdjoint_le_annihilator_ker`
  (`closure R(A*) ⊆ N(A)^⊥`),
  `LinearPMap.strongDualCoannihilator_ker_strongDualAdjoint_eq_closure_range`
  (`N(A*)^⊥ = closure R(A)`), and the bounded forms
  `ContinuousLinearMap.ker_strongDualMap_eq_annihilator_range`,
  `ContinuousLinearMap.ker_eq_strongDualCoannihilator_range_strongDualMap`.
* Remark 2.20: `A` onto implies `A*` injective, `A*` onto implies `A` injective.
* Remarks 2.15 and 2.17, the weak-∗ clauses: `D(A*)` is weak-∗ dense in `F*`
  (`LinearPMap.IsClosed.dense_toWeakDual_domain_strongDualAdjoint`), and `N(A)^⊥` is the weak-∗
  closure of `R(A*)`
  (`LinearPMap.IsClosed.annihilator_ker_eq_closure_toWeakDual_range_strongDualAdjoint`).

## Conventions

The annihilators are `Submodule.strongDualAnnihilator` (`M^⊥ ⊆ E*`) and
`Submodule.strongDualCoannihilator` (`N^⊥ ⊆ E`) of `Numlib.Analysis.Normed.Module.Annihilator`,
abbreviated to `annihilator` in lemma names. The range of `A` is `LinearMap.range A.toFun`, its
kernel `A.ker`. The reflexive-space theorems about `A*` (`D(A*)` dense, `A** = A`) are in
`Numlib.Analysis.Normed.Operator.Unbounded.Reflexive`, the closed range theorem in
`Numlib.Analysis.Normed.Operator.Unbounded.ClosedRange`.

## References

[brezis2011functional], §2.6 (the definition, Remarks 14–17, Proposition 2.17, relation (27),
Corollary 2.18, Exercise 2.18) and §2.7 (Remark 20).
-/

open Filter Topology

noncomputable section

namespace ContinuousLinearMap

section NontriviallyNormedField

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- **The Banach-space adjoint of a bounded operator**, `T* : F* → E*`, `T* v = v ∘ T`
([brezis2011functional], Remark 2.16). It is Mathlib's precomposition map
`ContinuousLinearMap.precomp 𝕜 T` with scalar-valued functionals as targets. -/
def strongDualMap (T : E →L[𝕜] F) : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E :=
  precomp 𝕜 T

/-- The fundamental relation `⟨T* v, u⟩ = ⟨v, T u⟩`. -/
@[simp]
theorem strongDualMap_apply (T : E →L[𝕜] F) (v : StrongDual 𝕜 F) (u : E) :
    T.strongDualMap v u = v (T u) :=
  rfl

/-- `T* v` is the composite functional `v ∘ T`. -/
theorem strongDualMap_apply' (T : E →L[𝕜] F) (v : StrongDual 𝕜 F) :
    T.strongDualMap v = v.comp T :=
  rfl

/-- The adjoint is Mathlib's `ContinuousLinearMap.precomp` at scalar-valued targets. -/
theorem strongDualMap_eq_precomp (T : E →L[𝕜] F) : T.strongDualMap = precomp 𝕜 T :=
  rfl

/-- The adjoint is the flip of the composition map `compL`, applied to `T`. -/
theorem strongDualMap_eq_compL_flip (T : E →L[𝕜] F) :
    T.strongDualMap = (compL 𝕜 E F 𝕜).flip T := by
  ext; rfl

/-- The adjoint of the identity is the identity. -/
@[simp]
theorem strongDualMap_id :
    (ContinuousLinearMap.id 𝕜 E).strongDualMap = ContinuousLinearMap.id 𝕜 (StrongDual 𝕜 E) := by
  ext; rfl

/-- `(S ∘ T)* = T* ∘ S*` ([brezis2011functional], Exercise 2.25). -/
theorem strongDualMap_comp (S : F →L[𝕜] G) (T : E →L[𝕜] F) :
    (S.comp T).strongDualMap = T.strongDualMap.comp S.strongDualMap := by
  ext; rfl

/-- The adjoint of a sum is the sum of the adjoints. -/
@[simp]
theorem strongDualMap_add (S T : E →L[𝕜] F) :
    (S + T).strongDualMap = S.strongDualMap + T.strongDualMap := by
  ext; simp

/-- The adjoint of a scalar multiple is the scalar multiple of the adjoint. -/
@[simp]
theorem strongDualMap_smul (c : 𝕜) (T : E →L[𝕜] F) :
    (c • T).strongDualMap = c • T.strongDualMap := by
  ext; simp

/-- The adjoint of the zero operator is zero. -/
@[simp]
theorem strongDualMap_zero : (0 : E →L[𝕜] F).strongDualMap = 0 := by
  ext; simp

/-- The adjoint of a difference is the difference of the adjoints. -/
@[simp]
theorem strongDualMap_sub (S T : E →L[𝕜] F) :
    (S - T).strongDualMap = S.strongDualMap - T.strongDualMap := by
  ext; simp

/-- Compatibility with Mathlib's algebraic dual map: as a linear map, `T* v` is
`LinearMap.dualMap T v`. -/
theorem toLinearMap_strongDualMap_apply (T : E →L[𝕜] F) (v : StrongDual 𝕜 F) :
    ((T.strongDualMap v : StrongDual 𝕜 E) : E →ₗ[𝕜] 𝕜) =
      (T : E →ₗ[𝕜] F).dualMap (v : F →ₗ[𝕜] 𝕜) :=
  rfl

/-- `‖T*‖ ≤ ‖T‖` ([brezis2011functional], Remark 2.16, first inequality). -/
theorem opNorm_strongDualMap_le (T : E →L[𝕜] F) : ‖T.strongDualMap‖ ≤ ‖T‖ := by
  refine opNorm_le_bound _ (norm_nonneg _) fun v => ?_
  rw [strongDualMap_apply', mul_comm]
  exact opNorm_comp_le v T

/-- **`N(T*) = R(T)^⊥`** ([brezis2011functional], Corollary 2.18 (ii) for a bounded operator):
`T* v = 0` iff `v` vanishes on the range of `T`. -/
theorem ker_strongDualMap_eq_annihilator_range (T : E →L[𝕜] F) :
    T.strongDualMap.ker = (LinearMap.range (T : E →ₗ[𝕜] F)).strongDualAnnihilator := by
  ext v
  simp only [LinearMap.mem_ker, coe_coe, Submodule.mem_strongDualAnnihilator, LinearMap.mem_range,
    forall_exists_index, forall_apply_eq_imp_iff, ContinuousLinearMap.ext_iff, zero_apply,
    strongDualMap_apply]

end NontriviallyNormedField

section RCLike

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **`‖T*‖ = ‖T‖`** ([brezis2011functional], Remark 2.16). The inequality `‖T‖ ≤ ‖T*‖` is
Corollary 1.4 of the book: a norming functional `v` of `T u` with `‖v‖ ≤ 1` gives
`‖T u‖ = ‖(T* v) u‖ ≤ ‖T*‖ ‖u‖`. -/
theorem opNorm_strongDualMap (T : E →L[𝕜] F) : ‖T.strongDualMap‖ = ‖T‖ := by
  refine le_antisymm (opNorm_strongDualMap_le T) ?_
  refine opNorm_le_bound _ (norm_nonneg _) fun u => ?_
  obtain ⟨v, hv, hvu⟩ := exists_dual_vector'' 𝕜 (T u)
  calc ‖T u‖ = ‖v (T u)‖ := by rw [hvu, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _)]
    _ = ‖T.strongDualMap v u‖ := rfl
    _ ≤ ‖T.strongDualMap v‖ * ‖u‖ := le_opNorm _ _
    _ ≤ ‖T.strongDualMap‖ * ‖v‖ * ‖u‖ := by gcongr; exact le_opNorm _ _
    _ ≤ ‖T.strongDualMap‖ * ‖u‖ := by
        have := mul_le_mul_of_nonneg_left hv (norm_nonneg T.strongDualMap)
        nlinarith [norm_nonneg u, norm_nonneg T.strongDualMap]

variable (𝕜 E F) in
/-- The map `T ↦ T*` as a linear isometry `(E →L[𝕜] F) →ₗᵢ[𝕜] (F* →L[𝕜] E*)`. Unlike the
Hilbert-space adjoint it is not onto: its image consists of the weak-∗ continuous operators. -/
def strongDualMapₗᵢ : (E →L[𝕜] F) →ₗᵢ[𝕜] (StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E) where
  toFun := strongDualMap
  map_add' := strongDualMap_add
  map_smul' := strongDualMap_smul
  norm_map' := opNorm_strongDualMap

@[simp]
theorem strongDualMapₗᵢ_apply (T : E →L[𝕜] F) : strongDualMapₗᵢ 𝕜 E F T = T.strongDualMap :=
  rfl

/-- **`N(T) = R(T*)^⊥`** ([brezis2011functional], Corollary 2.18 (i) for a bounded operator):
`T u = 0` iff `(T* v) u = v (T u) = 0` for every `v ∈ F*`, the functionals separating the points
of `F`. -/
theorem ker_eq_strongDualCoannihilator_range_strongDualMap (T : E →L[𝕜] F) :
    T.ker = Submodule.strongDualCoannihilator
      (LinearMap.range (T.strongDualMap : StrongDual 𝕜 F →ₗ[𝕜] StrongDual 𝕜 E)) := by
  ext u
  rw [LinearMap.mem_ker, coe_coe, Submodule.mem_strongDualCoannihilator]
  constructor
  · rintro h _ ⟨v, rfl⟩
    rw [coe_coe, strongDualMap_apply, h, map_zero]
  · intro h
    refine SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := 𝕜) fun v => ?_
    exact h _ ⟨v, rfl⟩

end RCLike

end ContinuousLinearMap

namespace LinearPMap

section Definition

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

variable (A : E →ₗ.[𝕜] F)

/-- The domain of the Banach adjoint: those `v ∈ F*` for which `u ↦ v (A u)` is continuous on
`D(A)`, i.e. `‖v (A u)‖ ≤ c ‖u‖` for some `c`. -/
def strongDualAdjointDomain : Submodule 𝕜 (StrongDual 𝕜 F) where
  carrier := {v | Continuous ((v : F →ₗ[𝕜] 𝕜).comp A.toFun)}
  zero_mem' := by
    simp only [Set.mem_ofPred_eq, ContinuousLinearMap.toLinearMap_zero, LinearMap.zero_comp]
    exact continuous_zero
  add_mem' hv hw := by
    simp only [Set.mem_ofPred_eq, ContinuousLinearMap.toLinearMap_add, LinearMap.add_comp] at *
    exact hv.add hw
  smul_mem' c v hv := by
    simp only [Set.mem_ofPred_eq, ContinuousLinearMap.toLinearMap_smul, LinearMap.smul_comp] at *
    exact hv.const_smul c

omit [CompleteSpace 𝕜] in
theorem mem_strongDualAdjointDomain_iff (v : StrongDual 𝕜 F) :
    v ∈ A.strongDualAdjointDomain ↔ Continuous ((v : F →ₗ[𝕜] 𝕜).comp A.toFun) :=
  Iff.rfl

omit [CompleteSpace 𝕜] in
/-- The book's form of the domain condition. -/
theorem mem_strongDualAdjointDomain_iff_exists (v : StrongDual 𝕜 F) :
    v ∈ A.strongDualAdjointDomain ↔ ∃ c : ℝ, ∀ u : A.domain, ‖v (A u)‖ ≤ c * ‖u‖ := by
  rw [mem_strongDualAdjointDomain_iff]
  constructor
  · intro h
    obtain ⟨c, _, hc⟩ := (⟨(v : F →ₗ[𝕜] 𝕜).comp A.toFun, h⟩ : A.domain →L[𝕜] 𝕜).bound
    exact ⟨c, fun u => hc u⟩
  · rintro ⟨c, hc⟩
    exact (LinearMap.mkContinuousOfExistsBound _ ⟨c, hc⟩).continuous

/-- `u ↦ v (A u)` as a bounded functional on `D(A)`. -/
def strongDualAdjointDomainMkCLM (v : A.strongDualAdjointDomain) : StrongDual 𝕜 A.domain :=
  ⟨((v : StrongDual 𝕜 F) : F →ₗ[𝕜] 𝕜).comp A.toFun, v.prop⟩

omit [CompleteSpace 𝕜] in
theorem strongDualAdjointDomainMkCLM_apply (v : A.strongDualAdjointDomain) (u : A.domain) :
    A.strongDualAdjointDomainMkCLM v u = (v : StrongDual 𝕜 F) (A u) :=
  rfl

/-- The extension by continuity of `u ↦ v (A u)` to all of `E` ([brezis2011functional],
Remark 2.14: no Hahn–Banach is needed). -/
def strongDualAdjointDomainMkCLMExtend (v : A.strongDualAdjointDomain) : StrongDual 𝕜 E :=
  (A.strongDualAdjointDomainMkCLM v).extend (Submodule.subtypeL A.domain)

variable {A}

@[simp]
theorem strongDualAdjointDomainMkCLMExtend_apply (hA : Dense (A.domain : Set E))
    (v : A.strongDualAdjointDomain) (u : A.domain) :
    A.strongDualAdjointDomainMkCLMExtend v (u : E) = (v : StrongDual 𝕜 F) (A u) :=
  ContinuousLinearMap.extend_eq _ hA.denseRange_val
    isUniformEmbedding_subtype_val.isUniformInducing _

variable (hA : Dense (A.domain : Set E))

/-- The adjoint as a linear map on its domain; linearity needs the density of `D(A)`. -/
def strongDualAdjointAux : A.strongDualAdjointDomain →ₗ[𝕜] StrongDual 𝕜 E where
  toFun v := A.strongDualAdjointDomainMkCLMExtend v
  map_add' v w := by
    refine ContinuousLinearMap.ext_on (R₁ := 𝕜) (s := (A.domain : Set E)) (by simpa) ?_
    rintro u hu
    simp [strongDualAdjointDomainMkCLMExtend_apply hA _ ⟨u, hu⟩]
  map_smul' c v := by
    refine ContinuousLinearMap.ext_on (R₁ := 𝕜) (s := (A.domain : Set E)) (by simpa) ?_
    rintro u hu
    simp [strongDualAdjointDomainMkCLMExtend_apply hA _ ⟨u, hu⟩]

theorem strongDualAdjointAux_apply (v : A.strongDualAdjointDomain) (u : A.domain) :
    strongDualAdjointAux hA v u = (v : StrongDual 𝕜 F) (A u) := by
  simp [strongDualAdjointAux, hA]

theorem strongDualAdjointAux_unique (v : A.strongDualAdjointDomain) {f : StrongDual 𝕜 E}
    (hf : ∀ u : A.domain, f u = (v : StrongDual 𝕜 F) (A u)) : strongDualAdjointAux hA v = f := by
  refine ContinuousLinearMap.ext_on (R₁ := 𝕜) (s := (A.domain : Set E)) (by simpa) ?_
  rintro u hu
  rw [strongDualAdjointAux_apply hA v ⟨u, hu⟩, hf ⟨u, hu⟩]

variable (A)

open scoped Classical in
/-- **The Banach-space adjoint** `A* : D(A*) ⊆ F* → E*` of an unbounded operator
`A : D(A) ⊆ E → F` ([brezis2011functional], §2.6): `D(A*)` consists of the `v ∈ F*` with
`‖v (A u)‖ ≤ c ‖u‖` on `D(A)`, and `A* v` is the extension by continuity of `u ↦ v (A u)` to
`E`. When `D(A)` is not dense the values are the junk `0` (the pattern of Mathlib's Hilbert-space
`LinearPMap.adjoint`). -/
def strongDualAdjoint : StrongDual 𝕜 F →ₗ.[𝕜] StrongDual 𝕜 E where
  domain := A.strongDualAdjointDomain
  toFun := if hA : Dense (A.domain : Set E) then strongDualAdjointAux hA else 0

/-- **The domain of the adjoint** ([brezis2011functional], §2.6, the definition (24)):
`v ∈ D(A*)` iff `‖v (A u)‖ ≤ c ‖u‖` on `D(A)` for some constant `c`. -/
theorem mem_strongDualAdjoint_domain_iff (v : StrongDual 𝕜 F) :
    v ∈ A.strongDualAdjoint.domain ↔ ∃ c : ℝ, ∀ u : A.domain, ‖v (A u)‖ ≤ c * ‖u‖ :=
  A.mem_strongDualAdjointDomain_iff_exists v

/-- `v ∈ D(A*)` iff `u ↦ v (A u)` is continuous on `D(A)`. -/
theorem mem_strongDualAdjoint_domain_iff_continuous (v : StrongDual 𝕜 F) :
    v ∈ A.strongDualAdjoint.domain ↔ Continuous ((v : F →ₗ[𝕜] 𝕜).comp A.toFun) :=
  Iff.rfl

variable {A}

theorem strongDualAdjoint_apply_of_dense (v : A.strongDualAdjoint.domain) :
    A.strongDualAdjoint v = strongDualAdjointAux hA v := by
  classical
  change (if hA : Dense (A.domain : Set E) then strongDualAdjointAux hA else 0) v = _
  simp only [hA, dite_true]

theorem strongDualAdjoint_apply_of_not_dense (hA : ¬ Dense (A.domain : Set E))
    (v : A.strongDualAdjoint.domain) : A.strongDualAdjoint v = 0 := by
  classical
  change (if hA : Dense (A.domain : Set E) then strongDualAdjointAux hA else 0) v = _
  simp only [hA, dite_false]
  rfl

include hA in
/-- **The fundamental relation** `⟨A* v, u⟩ = ⟨v, A u⟩` for `u ∈ D(A)`, `v ∈ D(A*)`
([brezis2011functional], §2.6, (25)). -/
theorem strongDualAdjoint_apply (v : A.strongDualAdjoint.domain) (u : A.domain) :
    A.strongDualAdjoint v u = (v : StrongDual 𝕜 F) (A u) := by
  rw [strongDualAdjoint_apply_of_dense hA]
  exact strongDualAdjointAux_apply hA v u

include hA in
/-- **Uniqueness of the extension**: a functional `f ∈ E*` with `f u = v (A u)` on the dense
`D(A)` is `A* v`. -/
theorem strongDualAdjoint_apply_eq (v : A.strongDualAdjoint.domain) {f : StrongDual 𝕜 E}
    (hf : ∀ u : A.domain, f u = (v : StrongDual 𝕜 F) (A u)) : A.strongDualAdjoint v = f := by
  rw [strongDualAdjoint_apply_of_dense hA]
  exact strongDualAdjointAux_unique hA v hf

/-- `v ∈ D(A*)` as soon as some `f ∈ E*` satisfies `f u = v (A u)` on `D(A)`. -/
theorem mem_strongDualAdjoint_domain_of_exists (v : StrongDual 𝕜 F)
    (h : ∃ f : StrongDual 𝕜 E, ∀ u : A.domain, f u = v (A u)) :
    v ∈ A.strongDualAdjoint.domain := by
  obtain ⟨f, hf⟩ := h
  refine (A.mem_strongDualAdjoint_domain_iff v).2 ⟨‖f‖, fun u => ?_⟩
  rw [← hf u]
  exact f.le_opNorm u

include hA in
/-- **The graph of the adjoint**: `(v, f) ∈ G(A*)` iff `f u = v (A u)` for every `u ∈ D(A)`
([brezis2011functional], the computation after Proposition 2.17, before any identification of
`(E × F)*`). -/
theorem mem_graph_strongDualAdjoint_iff (v : StrongDual 𝕜 F) (f : StrongDual 𝕜 E) :
    (v, f) ∈ A.strongDualAdjoint.graph ↔ ∀ u : A.domain, f u = v (A u) := by
  rw [mem_graph_iff]
  constructor
  · rintro ⟨w, hw, rfl⟩ u
    obtain ⟨w, hw'⟩ := w
    simp only at hw
    subst hw
    exact strongDualAdjoint_apply hA _ u
  · intro h
    have hv : v ∈ A.strongDualAdjoint.domain := mem_strongDualAdjoint_domain_of_exists v ⟨f, h⟩
    exact ⟨⟨v, hv⟩, rfl, strongDualAdjoint_apply_eq hA ⟨v, hv⟩ h⟩

include hA in
/-- **The adjoint is closed** ([brezis2011functional], Proposition 2.17): the graph of `A*` is
the intersection over `u ∈ D(A)` of the closed sets `{(v, f) | f u = v (A u)}`. Without density
of `D(A)` the graph is `D(A*) × {0}`, which need not be closed. -/
theorem strongDualAdjoint_isClosed : A.strongDualAdjoint.IsClosed := by
  have hgraph : (A.strongDualAdjoint.graph : Set (StrongDual 𝕜 F × StrongDual 𝕜 E)) =
      ⋂ u : A.domain, {p | p.2 (u : E) = p.1 (A u)} := by
    ext ⟨v, f⟩
    simp only [SetLike.mem_coe, Set.mem_iInter, Set.mem_ofPred_eq]
    exact mem_graph_strongDualAdjoint_iff hA v f
  rw [LinearPMap.IsClosed, hgraph]
  exact isClosed_iInter fun u =>
    isClosed_eq (continuous_snd.clm_apply continuous_const)
      (continuous_fst.clm_apply continuous_const)

/-- **The adjoint of a bounded operator restricted to a dense subspace is its bounded adjoint**
([brezis2011functional], Remark 2.16): `D(T*) = F*` and `T* v = v ∘ T`. With `p = ⊤` this is
the statement that the two adjoints agree on bounded operators. -/
theorem _root_.ContinuousLinearMap.toPMap_strongDualAdjoint (T : E →L[𝕜] F) {p : Submodule 𝕜 E}
    (hp : Dense (p : Set E)) :
    ((T : E →ₗ[𝕜] F).toPMap p).strongDualAdjoint =
      (T.strongDualMap : StrongDual 𝕜 F →ₗ[𝕜] StrongDual 𝕜 E).toPMap ⊤ := by
  have hp' : Dense ((((T : E →ₗ[𝕜] F).toPMap p).domain : Submodule 𝕜 E) : Set E) := hp
  refine LinearPMap.ext ?_ ?_
  · refine le_antisymm le_top fun v _ => ?_
    exact mem_strongDualAdjoint_domain_of_exists v ⟨T.strongDualMap v, fun u => rfl⟩
  · intro v hv hv'
    exact strongDualAdjoint_apply_eq hp' ⟨v, hv⟩ fun u => rfl

/-- **`N(A*) = R(A)^⊥`** ([brezis2011functional], Corollary 2.18 (ii); Exercise 2.18): `v ∈ D(A*)`
with `A* v = 0` iff `v` vanishes on `R(A)`. Closedness of `A` is not needed. -/
theorem ker_strongDualAdjoint_eq_annihilator_range (hA : Dense (A.domain : Set E)) :
    A.strongDualAdjoint.ker = (LinearMap.range A.toFun).strongDualAnnihilator := by
  ext v
  simp only [Submodule.mem_strongDualAnnihilator, LinearMap.mem_range, forall_exists_index,
    forall_apply_eq_imp_iff, mem_ker_iff, toFun_eq_coe]
  constructor
  · rintro ⟨w, rfl, hw⟩ u
    rw [← strongDualAdjoint_apply hA w u, hw, _root_.zero_apply]
  · intro h
    have hv : v ∈ A.strongDualAdjoint.domain := mem_strongDualAdjoint_domain_of_exists v
      ⟨0, fun u => by rw [h u, _root_.zero_apply]⟩
    exact ⟨⟨v, hv⟩, rfl, strongDualAdjoint_apply_eq hA _ fun u => by
      rw [h u, _root_.zero_apply]⟩

/-- **`closure R(A*) ⊆ N(A)^⊥`** ([brezis2011functional], Corollary 2.18 (iii)):
`(A* v) u = v (A u) = 0` for `u ∈ N(A)`, and the annihilator is closed. Equality can fail
(Remark 2.17, Exercise 2.23); the weak-∗ closure does give equality,
`IsClosed.annihilator_ker_eq_closure_toWeakDual_range_strongDualAdjoint`. -/
theorem closure_range_strongDualAdjoint_le_annihilator_ker (hA : Dense (A.domain : Set E)) :
    (LinearMap.range A.strongDualAdjoint.toFun).topologicalClosure ≤
      A.ker.strongDualAnnihilator := by
  refine Submodule.topologicalClosure_minimal _ ?_ (Submodule.isClosed_strongDualAnnihilator _)
  rintro f ⟨v, rfl⟩
  refine Submodule.mem_strongDualAnnihilator.2 fun u hu => ?_
  obtain ⟨w, rfl, hw⟩ := mem_ker_iff.1 hu
  rw [toFun_eq_coe, strongDualAdjoint_apply hA v w, hw, _root_.map_zero]

/-- **`A` onto implies `A*` injective** ([brezis2011functional], Remark 2.20):
`N(A*) = R(A)^⊥ = F^⊥ = 0`. -/
theorem ker_strongDualAdjoint_eq_bot_of_range_eq_top (hA : Dense (A.domain : Set E))
    (h : LinearMap.range A.toFun = ⊤) : A.strongDualAdjoint.ker = ⊥ := by
  rw [ker_strongDualAdjoint_eq_annihilator_range hA, h, Submodule.strongDualAnnihilator_top]

end Definition

section RCLike

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {A : E →ₗ.[𝕜] F}

/-- **`N(A*)^⊥ = closure R(A)`** ([brezis2011functional], Corollary 2.18 (iv)): `N(A*) = R(A)^⊥`
and the bipolar identity `(M^⊥)^⊥ = closure M`. This is the shape of the closed range theorem and
of the Fredholm alternative: when `R(A)` is closed, `A u = f` is solvable iff `v f = 0` for every
`v ∈ N(A*)`. -/
theorem strongDualCoannihilator_ker_strongDualAdjoint_eq_closure_range
    (hA : Dense (A.domain : Set E)) :
    A.strongDualAdjoint.ker.strongDualCoannihilator =
      (LinearMap.range A.toFun).topologicalClosure := by
  rw [ker_strongDualAdjoint_eq_annihilator_range hA,
    Submodule.strongDualCoannihilator_strongDualAnnihilator]

/-- **The graph relation** `I[G(A*)] = G(A)^⊥` ([brezis2011functional], §2.6, (27)), with
`I (v, f) = (-f, v)` (`LinearEquiv.skewSwap`) and the identification `(E × F)* ≃ E* × F*`
sending `(g, v)` to `(x, y) ↦ g x + v y` (`ContinuousLinearMap.coprodEquivL`): the functional
`(x, y) ↦ -f x + v y` vanishes on `G(A)` iff `f u = v (A u)` on `D(A)`. -/
theorem map_graph_strongDualAdjoint_eq_annihilator_graph (hA : Dense (A.domain : Set E)) :
    (A.strongDualAdjoint.graph.map
      (LinearEquiv.skewSwap 𝕜 (StrongDual 𝕜 F) (StrongDual 𝕜 E) : _ →ₗ[𝕜] _)).map
        (((ContinuousLinearMap.coprodEquivL 𝕜 : (StrongDual 𝕜 E × StrongDual 𝕜 F) ≃L[𝕜]
          StrongDual 𝕜 (E × F)) : (StrongDual 𝕜 E × StrongDual 𝕜 F) →L[𝕜] StrongDual 𝕜 (E × F)) :
            (StrongDual 𝕜 E × StrongDual 𝕜 F) →ₗ[𝕜] StrongDual 𝕜 (E × F)) =
      A.graph.strongDualAnnihilator := by
  ext φ
  rw [Submodule.mem_map, Submodule.mem_strongDualAnnihilator]
  constructor
  · rintro ⟨q, hq, rfl⟩ ⟨x, y⟩ hxy
    obtain ⟨⟨v, f⟩, hvf, rfl⟩ := Submodule.mem_map.1 hq
    rw [mem_graph_strongDualAdjoint_iff hA] at hvf
    obtain ⟨u, hu1, hu2⟩ := (mem_graph_iff A).1 hxy
    simp only at hu1 hu2
    subst hu1 hu2
    simp [hvf u]
  · intro h
    refine ⟨(φ.comp (ContinuousLinearMap.inl 𝕜 E F), φ.comp (ContinuousLinearMap.inr 𝕜 E F)),
      Submodule.mem_map.2 ⟨(φ.comp (ContinuousLinearMap.inr 𝕜 E F),
        -(φ.comp (ContinuousLinearMap.inl 𝕜 E F))),
        (mem_graph_strongDualAdjoint_iff hA _ _).2 fun u => ?_, by simp⟩, ?_⟩
    · have := h ((u : E), A u) (A.mem_graph u)
      have hsplit : ((u : E), A u) = ContinuousLinearMap.inl 𝕜 E F u +
          ContinuousLinearMap.inr 𝕜 E F (A u) := by simp
      rw [hsplit, _root_.map_add] at this
      simp only [_root_.neg_apply, ContinuousLinearMap.comp_apply]
      linear_combination -this
    · refine ContinuousLinearMap.ext fun p => ?_
      obtain ⟨x, y⟩ := p
      simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearMap.coe_coe,
        ContinuousLinearMap.coprodEquivL_apply_apply, ContinuousLinearMap.comp_apply,
        ← _root_.map_add φ, ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply,
        Prod.mk_add_mk, add_zero, zero_add]

/-- **Separation from the closed graph, through the adjoint.** If `A` is closed and densely
defined and `(u, y) ∉ G(A)`, then some `v ∈ D(A*)` has `v y ≠ (A* v) u`. A functional
`Φ ∈ (E × F)*` vanishing on the graph with `Φ (u, y) ≠ 0`
(`Submodule.exists_dual_eq_zero_of_notMem`) has components `f = Φ ∘ inl`, `v = Φ ∘ inr` with
`f x + v (A x) = 0` on `D(A)`, so `v ∈ D(A*)`
with `A* v = -f`, and `v y - (A* v) u = Φ (u, y)`. Every consequence of the closedness of `A` for
its adjoint (Corollary 2.18 (i), the weak-∗ density of `D(A*)`, Theorem 3.24) reduces to this. -/
theorem IsClosed.exists_apply_ne_strongDualAdjoint_apply_of_notMem_graph (hc : A.IsClosed)
    (hA : Dense (A.domain : Set E)) {u : E} {y : F} (h : (u, y) ∉ A.graph) :
    ∃ v : A.strongDualAdjoint.domain, (v : StrongDual 𝕜 F) y ≠ A.strongDualAdjoint v u := by
  have hc' : _root_.IsClosed (A.graph : Set (E × F)) := hc
  obtain ⟨Φ, -, hΦ0, hΦ⟩ := A.graph.exists_dual_eq_zero_of_notMem hc' h
  set f : StrongDual 𝕜 E := Φ.comp (ContinuousLinearMap.inl 𝕜 E F) with hf
  set v : StrongDual 𝕜 F := Φ.comp (ContinuousLinearMap.inr 𝕜 E F) with hv
  have hsplit : ∀ x y, Φ (x, y) = f x + v y := fun x y => by
    rw [hf, hv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      ← _root_.map_add Φ]
    simp
  have hrel : ∀ x : A.domain, (-f) x = v (A x) := fun x => by
    have := hΦ0 _ (A.mem_graph x)
    rw [hsplit] at this
    rw [_root_.neg_apply]
    linear_combination -this
  have hvD : v ∈ A.strongDualAdjoint.domain := mem_strongDualAdjoint_domain_of_exists v ⟨-f, hrel⟩
  refine ⟨⟨v, hvD⟩, fun heq => hΦ ?_⟩
  rw [strongDualAdjoint_apply_eq hA ⟨v, hvD⟩ hrel, _root_.neg_apply] at heq
  rw [hsplit]
  linear_combination heq

/-- **`N(A) = R(A*)^⊥`** for a closed operator ([brezis2011functional], Corollary 2.18 (i);
Exercise 2.18): `u ∈ D(A)` with `A u = 0` iff `(A* v) u = 0` for every `v ∈ D(A*)`. The
inclusion `⊆` is the fundamental relation; for `⊇`, a `u ∈ R(A*)^⊥` outside `N(A)` has
`(u, 0) ∉ G(A)`, and separation from the closed graph produces `v ∈ D(A*)` with
`(A* v) u ≠ v 0 = 0`. -/
theorem IsClosed.ker_eq_strongDualCoannihilator_range_strongDualAdjoint (hc : A.IsClosed)
    (hA : Dense (A.domain : Set E)) :
    A.ker = (LinearMap.range A.strongDualAdjoint.toFun).strongDualCoannihilator := by
  ext u
  simp only [Submodule.mem_strongDualCoannihilator, LinearMap.mem_range, forall_exists_index,
    forall_apply_eq_imp_iff, toFun_eq_coe]
  constructor
  · rintro hu v
    obtain ⟨w, rfl, hw⟩ := mem_ker_iff.1 hu
    rw [strongDualAdjoint_apply hA v w, hw, _root_.map_zero]
  · intro h
    by_contra hu
    have hnot : (u, (0 : F)) ∉ A.graph := fun hmem => by
      obtain ⟨w, hw, hw0⟩ := (mem_graph_iff A).1 hmem
      exact hu (mem_ker_iff.2 ⟨w, hw.symm, hw0⟩)
    obtain ⟨v, hv⟩ := hc.exists_apply_ne_strongDualAdjoint_apply_of_notMem_graph hA hnot
    exact hv (by rw [h v, _root_.map_zero])

/-- **`A*` onto implies `A` injective** ([brezis2011functional], Remark 2.20): for a closed
operator, `N(A) = R(A*)^⊥ = (E*)^⊥ = 0`. -/
theorem IsClosed.ker_eq_bot_of_range_strongDualAdjoint_eq_top (hc : A.IsClosed)
    (hA : Dense (A.domain : Set E)) (h : LinearMap.range A.strongDualAdjoint.toFun = ⊤) :
    A.ker = ⊥ := by
  rw [hc.ker_eq_strongDualCoannihilator_range_strongDualAdjoint hA, h,
    Submodule.strongDualCoannihilator_top]

/-- **`D(A*)` separates the points of `F`** when `A` is closed and densely defined: for `y ≠ 0`
some `v ∈ D(A*)` has `v y ≠ 0`. Indeed `(0, y) ∉ G(A)`, and separation from the closed graph
gives `v ∈ D(A*)` with `v y ≠ (A* v) 0 = 0`. This is the common core of the weak-∗ density of
`D(A*)` (Remark 2.15) and of its norm density for reflexive `F` (Theorem 3.24). -/
theorem IsClosed.exists_mem_domain_strongDualAdjoint_apply_ne_zero (hc : A.IsClosed)
    (hA : Dense (A.domain : Set E)) {y : F} (hy : y ≠ 0) :
    ∃ v : A.strongDualAdjoint.domain, (v : StrongDual 𝕜 F) y ≠ 0 := by
  have hnot : ((0 : E), y) ∉ A.graph := fun hmem => by
    obtain ⟨u, hu, hAu⟩ := (mem_graph_iff A).1 hmem
    have : u = 0 := Subtype.ext hu
    simp only at hAu
    exact hy (by rw [← hAu, this, A.map_zero])
  obtain ⟨v, hv⟩ := hc.exists_apply_ne_strongDualAdjoint_apply_of_notMem_graph hA hnot
  refine ⟨v, fun h => hv ?_⟩
  rw [h, _root_.map_zero]

/-- **`D(A*)` is weak-∗ dense in `F*`** for a closed densely defined operator
([brezis2011functional], Remark 2.15; Problem 9): if the weak-∗ closure `K` of `D(A*)` missed
some `w`, the separation `Submodule.exists_weakDual_eval_eq_zero_of_notMem` would give `y : F`
killed by every `v ∈ D(A*)` with `w y ≠ 0`; but `D(A*)` separates the points of `F`
(`exists_mem_domain_strongDualAdjoint_apply_ne_zero`). The norm-closure statement fails in
general (Exercise 2.22) and holds for reflexive `F` (Theorem 3.24,
`LinearPMap.dense_domain_strongDualAdjoint`). -/
theorem IsClosed.dense_toWeakDual_domain_strongDualAdjoint (hc : A.IsClosed)
    (hA : Dense (A.domain : Set E)) :
    Dense (StrongDual.toWeakDual '' (A.strongDualAdjoint.domain : Set (StrongDual 𝕜 F))) := by
  rw [dense_iff_closure_eq, Set.eq_univ_iff_forall]
  intro w
  by_contra hw
  -- the weak-∗ closure of `D(A*)`, as a closed submodule of `WeakDual 𝕜 F`
  set K : Submodule 𝕜 (WeakDual 𝕜 F) :=
    (A.strongDualAdjoint.domain.map ((StrongDual.toWeakDual (𝕜 := 𝕜) (E := F)) :
      StrongDual 𝕜 F →ₗ[𝕜] WeakDual 𝕜 F)).topologicalClosure with hK
  have hKc : (K : Set (WeakDual 𝕜 F)) = _root_.closure
      (StrongDual.toWeakDual '' (A.strongDualAdjoint.domain : Set (StrongDual 𝕜 F))) := by
    rw [hK, Submodule.topologicalClosure_coe, Submodule.map_coe]
    rfl
  have hwK : w ∉ K := by rwa [← SetLike.mem_coe, hKc]
  obtain ⟨y, hy, hwy⟩ := K.exists_weakDual_eval_eq_zero_of_notMem
    (by rw [hKc]; exact isClosed_closure) hwK
  have hy0 : y ≠ 0 := fun h => hwy (by rw [h, _root_.map_zero])
  obtain ⟨v, hv⟩ := hc.exists_mem_domain_strongDualAdjoint_apply_ne_zero hA hy0
  exact hv (hy (StrongDual.toWeakDual v) (Submodule.le_topologicalClosure _ ⟨v, v.2, rfl⟩))

/-- **`N(A)^⊥` is the weak-∗ closure of `R(A*)`** for a closed densely defined operator
([brezis2011functional], Remark 2.17; Problem 9): `N(A) = R(A*)^⊥` and the weak-∗ bipolar
theorem for subspaces,
`Submodule.strongDualAnnihilator_strongDualCoannihilator_eq_closure_toWeakDual`. In norm the
inclusion `closure R(A*) ⊆ N(A)^⊥` can be strict; equality holds when `E` is reflexive
(`Submodule.strongDualAnnihilator_strongDualCoannihilator`). -/
theorem IsClosed.annihilator_ker_eq_closure_toWeakDual_range_strongDualAdjoint (hc : A.IsClosed)
    (hA : Dense (A.domain : Set E)) :
    StrongDual.toWeakDual '' (A.ker.strongDualAnnihilator : Set (StrongDual 𝕜 E)) =
      _root_.closure (StrongDual.toWeakDual ''
        (LinearMap.range A.strongDualAdjoint.toFun : Set (StrongDual 𝕜 E))) := by
  rw [hc.ker_eq_strongDualCoannihilator_range_strongDualAdjoint hA]
  exact Submodule.strongDualAnnihilator_strongDualCoannihilator_eq_closure_toWeakDual _

end RCLike

end LinearPMap

end
