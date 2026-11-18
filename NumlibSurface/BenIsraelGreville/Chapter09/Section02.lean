/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.InnerProductSpace.MaximalMonotone
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import Numlib.Analysis.Normed.Lp.Sequence
import Numlib.Analysis.Normed.Operator.Compact

/-!
# Hilbert spaces and partial linear operators

Section 9.2 of [benIsrael2003generalized] collects the Hilbert space
and operator preliminaries used for generalized inverses. Partial
operators carry a linear subspace as their domain.

## Deviations from the source

* The first equality in **Equation (3)** uses a closed densely defined
  operator. For a closable operator the right kernel is that of the closure.
* **Equation (4)** assigns $+\infty$ when the carrier is trivial. This
  includes the zero operator in the positivity criterion.
-/

namespace BenIsraelGreville.Chapter09

open Filter Topology
open scoped InnerProductSpace

variable {𝕜 E F : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

section Subspaces

omit [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- **Part (A)** of [benIsrael2003generalized], Chapter 9, Section 2.
The orthogonal complement is closed and depends only on the closure. -/
theorem orthogonalComplement_closure (M : Submodule 𝕜 E) :
    IsClosed (Mᗮ : Set E) ∧ M.topologicalClosureᗮ = Mᗮ :=
  ⟨M.isClosed_orthogonal, M.orthogonal_closure⟩

/-- **Part (A)** of [benIsrael2003generalized], Chapter 9, Section 2.
A subspace decomposes with respect to a contained subspace if its vectors
split into one part in that subspace and one part orthogonal to it. -/
def IsDecomposable (L M : Submodule 𝕜 E) : Prop :=
  M ≤ L ∧ L = M ⊔ (L ⊓ Mᗮ)

variable [CompleteSpace E]

/-- **Equation (1)** of [benIsrael2003generalized], Chapter 9.
Decomposability means that the orthogonal projection onto the closure
of `M` carries vectors of `L` into `M`. -/
theorem isDecomposable_iff_starProjection (L M : Submodule 𝕜 E) :
    IsDecomposable L M ↔
      M ≤ L ∧ ∀ x ∈ L, M.topologicalClosure.starProjection x ∈ M := by
  let C := M.topologicalClosure
  constructor
  · rintro ⟨hML, hL⟩
    refine ⟨hML, fun x hx => ?_⟩
    have hm : x ∈ M ⊔ (L ⊓ Mᗮ) := hL ▸ hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hm
    have hpy : C.starProjection y = y :=
      C.starProjection_eq_self_iff.mpr (M.le_topologicalClosure hy)
    have hxorth : z ∈ Cᗮ := by
      change z ∈ M.topologicalClosureᗮ
      rw [M.orthogonal_closure]
      exact hz.2
    have hpz : C.starProjection z = 0 := C.starProjection_apply_eq_zero_iff.mpr hxorth
    change C.starProjection (y + z) ∈ M
    rw [map_add, hpy, hpz, add_zero]
    exact hy
  · rintro ⟨hML, hP⟩
    refine ⟨hML, le_antisymm ?_ (sup_le hML inf_le_left)⟩
    intro x hx
    let y := C.starProjection x
    have hy : y ∈ M := hP x hx
    have hz : x - y ∈ Mᗮ := by
      rw [← M.orthogonal_closure]
      exact C.sub_starProjection_mem_orthogonal x
    exact Submodule.mem_sup.mpr
      ⟨y, hy, x - y, ⟨L.sub_mem hx (hML hy), hz⟩, by abel⟩

/-- A closed subspace is a decomposing subspace of each larger subspace. -/
theorem isDecomposable_of_isClosed {L M : Submodule 𝕜 E} (hML : M ≤ L)
    (hM : IsClosed (M : Set E)) : IsDecomposable L M := by
  let : CompleteSpace M := hM.completeSpace_coe
  refine ⟨hML, le_antisymm ?_ (sup_le hML inf_le_left)⟩
  intro x hx
  let y := M.starProjection x
  have hy : y ∈ M := M.starProjection_apply_mem x
  have hz : x - y ∈ Mᗮ := M.sub_starProjection_mem_orthogonal x
  exact Submodule.mem_sup.mpr
    ⟨y, hy, x - y, ⟨L.sub_mem hx (hML hy), hz⟩, by abel⟩

/-- **Part (A)** of [benIsrael2003generalized], Chapter 9, Section 2.
The sum of two orthogonal closed subspaces is closed. -/
theorem orthogonal_sup_isClosed {L M : Submodule 𝕜 E}
    (hL : IsClosed (L : Set E)) (hM : IsClosed (M : Set E)) (hOrth : M ≤ Lᗮ) :
    IsClosed ((L ⊔ M : Submodule 𝕜 E) : Set E) := by
  let : CompleteSpace L := hL.completeSpace_coe
  have heq : ((L ⊔ M : Submodule 𝕜 E) : Set E) =
      (fun x => x - L.starProjection x) ⁻¹' (M : Set E) := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
      simp only [Set.mem_preimage, map_add, L.starProjection_eq_self_iff.mpr hy,
        L.starProjection_apply_eq_zero_iff.mpr (hOrth hz), add_zero, add_sub_cancel_left]
      exact hz
    · intro hx
      exact Submodule.mem_sup.mpr
        ⟨L.starProjection x, L.starProjection_apply_mem x, x - L.starProjection x, hx, by abel⟩
  rw [heq]
  exact hM.preimage (continuous_id.sub L.starProjection.continuous)

end Subspaces

section Product

/-- **Part (B)** of [benIsrael2003generalized], Chapter 9, Section 2.
The two coordinate inclusions in the Hilbert product. -/
def hilbertProductInclusions :
    (E →ₗᵢ[𝕜] WithLp 2 (E × F)) × (F →ₗᵢ[𝕜] WithLp 2 (E × F)) :=
  ⟨{ toFun := fun x => WithLp.toLp 2 (x, 0)
     map_add' := by
       intro x y
       apply (WithLp.equiv 2 _).injective
       change (x + y, (0 : F)) = (x, 0) + (y, 0)
       ext <;> simp
     map_smul' := by
       intro c x
       apply (WithLp.equiv 2 _).injective
       change (c • x, (0 : F)) = c • (x, 0)
       ext <;> simp
     norm_map' := by
       intro x
       rw [WithLp.prod_norm_eq_of_L2]
       simp },
   { toFun := fun y => WithLp.toLp 2 (0, y)
     map_add' := by
       intro x y
       apply (WithLp.equiv 2 _).injective
       change ((0 : E), x + y) = (0, x) + (0, y)
       ext <;> simp
     map_smul' := by
       intro c y
       apply (WithLp.equiv 2 _).injective
       change ((0 : E), c • y) = c • (0, y)
       ext <;> simp
     norm_map' := by
       intro y
       rw [WithLp.prod_norm_eq_of_L2]
       simp }⟩

end Product

section PartialOperators

/-- **Part (C)**, Equation (2) of [benIsrael2003generalized], Chapter 9.
The carrier is the part of the domain orthogonal to the kernel. -/
def carrier (T : E →ₗ.[𝕜] F) : Submodule 𝕜 E :=
  T.domain ⊓ T.kerᗮ

/-- **Part (C)** of [benIsrael2003generalized], Chapter 9, Section 2.
A subspace is the graph of a unique partial linear operator exactly when
its intersection with the vertical axis is trivial. -/
theorem graph_iff_disjoint_vertical (G : Submodule 𝕜 (E × F)) :
    (∃! T : E →ₗ.[𝕜] F, T.graph = G ∧ T.domain = G.map (LinearMap.fst 𝕜 E F)) ↔
      ∀ y : F, ((0 : E), y) ∈ G → y = 0 := by
  constructor
  · rintro ⟨T, ⟨hG, _⟩, _⟩ y hy
    rw [← hG] at hy
    exact T.graph_fst_eq_zero_snd hy rfl
  · intro h
    have hG : G.toLinearPMap.graph = G := G.toLinearPMap_graph_eq fun x hx hx0 => by
      rcases x with ⟨x, y⟩
      change x = 0 at hx0
      subst x
      exact h y hx
    refine ⟨G.toLinearPMap, ⟨hG, ?_⟩, fun T hT => ?_⟩
    · rfl
    · exact LinearPMap.eq_of_eq_graph (hT.1.trans hG.symm)

/-- The inverse-graph version of **Part (C)**, with the axes interchanged. -/
theorem inverseGraph_iff_disjoint_horizontal (G : Submodule 𝕜 (E × F)) :
    (∃! T : F →ₗ.[𝕜] E,
      T.graph = G.map (LinearEquiv.prodComm 𝕜 E F : (E × F) →ₗ[𝕜] (F × E)) ∧
      T.domain = G.map (LinearMap.snd 𝕜 E F)) ↔ ∀ x : E, (x, (0 : F)) ∈ G → x = 0 := by
  have hg : (G.map (LinearEquiv.prodComm 𝕜 E F : (E × F) →ₗ[𝕜] (F × E))).map
      (LinearMap.fst 𝕜 F E) = G.map (LinearMap.snd 𝕜 E F) := by
    rw [← Submodule.map_comp]
    rfl
  rw [← hg, graph_iff_disjoint_vertical]
  simp only [Submodule.map_equiv_eq_comap_symm, Submodule.mem_comap, LinearEquiv.coe_coe]
  rfl

/-- **Part (D)** of [benIsrael2003generalized], Chapter 9, Section 2.
The graph of a closed operator contains the limits of its convergent
sequences. This sequence condition also implies closedness. -/
theorem isClosed_iff_graphLimit (T : E →ₗ.[𝕜] F) :
    T.IsClosed ↔ ∀ (u : ℕ → E × F) (v : E × F),
      (∀ j, u j ∈ T.graph) → Tendsto u atTop (𝓝 v) → v ∈ T.graph := by
  constructor
  · intro h u v hu ht
    exact h.mem_of_tendsto ht (Eventually.of_forall hu)
  · intro h
    exact IsSeqClosed.isClosed (fun _ _ hu hv => h _ _ hu hv)

/-- The kernel of a closed partial operator is closed, as in **Part (D)**. -/
theorem isClosed_kernel_of_isClosed (T : E →ₗ.[𝕜] F) (hT : T.IsClosed) :
    IsClosed (T.ker : Set E) :=
  hT.isClosed_ker

/-- **Part (E)** of [benIsrael2003generalized], Chapter 9, Section 2.
A partial operator is bounded when its norm on the given domain admits a
uniform linear bound. -/
def IsBoundedOperator (T : E →ₗ.[𝕜] F) : Prop :=
  ∃ c : ℝ, ∀ x : T.domain, ‖T x‖ ≤ c * ‖x‖

open scoped ENNReal in
/-- **Part (E)** of [benIsrael2003generalized], Chapter 9, Section 2.
The operator norm is the supremum of the norm ratios on nonzero vectors
in the domain. Its value can be infinite on an unbounded operator. -/
noncomputable def partialOperatorNorm (T : E →ₗ.[𝕜] F) : ℝ≥0∞ :=
  ⨆ x : {x : T.domain // x ≠ 0}, ENNReal.ofReal (‖T x.val‖ / ‖x.val‖)

/-- A partial operator is bounded exactly when its operator norm is finite. -/
theorem isBoundedOperator_iff_partialOperatorNorm_lt_top (T : E →ₗ.[𝕜] F) :
    IsBoundedOperator T ↔ partialOperatorNorm T < ⊤ := by
  constructor
  · rintro ⟨c, hc⟩
    calc
      partialOperatorNorm T ≤ ENNReal.ofReal c := by
        apply iSup_le
        intro x
        exact ENNReal.ofReal_le_ofReal ((div_le_iff₀ (norm_pos_iff.mpr x.prop)).mpr (hc x.val))
      _ < ⊤ := ENNReal.ofReal_lt_top
  · intro h
    refine ⟨(partialOperatorNorm T).toReal, fun x => ?_⟩
    by_cases hx : x = 0
    · simp [hx]
    · apply (div_le_iff₀ (norm_pos_iff.mpr hx)).mp
      apply (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).mp
      rw [ENNReal.ofReal_toReal h.ne]
      exact le_iSup (fun u : {u : T.domain // u ≠ 0} => ENNReal.ofReal (‖T u.val‖ / ‖u.val‖))
        ⟨x, hx⟩

/-- Boundedness on the domain is equivalent to continuity on the domain. -/
theorem isBoundedOperator_iff_continuous (T : E →ₗ.[𝕜] F) :
    IsBoundedOperator T ↔ Continuous T.toFun := by
  constructor
  · rintro ⟨c, hc⟩
    exact (T.toFun.mkContinuous c hc).continuous
  · intro h
    obtain ⟨c, _, hc⟩ := SemilinearMapClass.bound_of_continuous T.toFun h
    exact ⟨c, hc⟩

/-- **Part (E)** of [benIsrael2003generalized], Chapter 9, Section 2.
A bounded partial operator with complete codomain is closed exactly when
its domain is closed. -/
theorem isClosed_iff_isClosed_domain_of_bounded [CompleteSpace F]
    (T : E →ₗ.[𝕜] F) (hT : IsBoundedOperator T) :
    T.IsClosed ↔ IsClosed (T.domain : Set E) := by
  have hcont := (isBoundedOperator_iff_continuous T).mp hT
  let f : T.domain →L[𝕜] F := ⟨T.toFun, hcont⟩
  constructor
  · intro hg
    refine IsSeqClosed.isClosed ?_
    intro u x hu hux
    let v (j : ℕ) : T.domain := ⟨u j, hu j⟩
    have hc : CauchySeq v := by
      apply Metric.cauchySeq_iff'.mpr
      intro ε hε
      obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.mp hux.cauchySeq ε hε
      exact ⟨N, fun j hj => hN j hj⟩
    have hfc : CauchySeq (fun j => f (v j)) :=
      f.uniformContinuous.comp_cauchySeq hc
    obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hfc
    exact ((LinearPMap.isClosed_iff_seq T).mp hg v x y hux hy).choose
  · intro hD
    apply (LinearPMap.isClosed_iff_seq T).mpr
    intro u x y hx hy
    have hxD : x ∈ T.domain := hD.mem_of_tendsto hx (Eventually.of_forall fun j => (u j).prop)
    have hu : Tendsto u atTop (𝓝 (⟨x, hxD⟩ : T.domain)) := tendsto_subtype_rng.mpr hx
    exact ⟨hxD, tendsto_nhds_unique ((f.continuous.tendsto _).comp hu) hy⟩

/-- The closed graph theorem on a closed partial domain. -/
theorem isBoundedOperator_of_isClosed_domain [CompleteSpace E] [CompleteSpace F]
    (T : E →ₗ.[𝕜] F) (hT : T.IsClosed) (hD : IsClosed (T.domain : Set E)) :
    IsBoundedOperator T := by
  let : CompleteSpace T.domain := hD.completeSpace_coe
  apply (isBoundedOperator_iff_continuous T).mpr
  apply T.toFun.continuous_of_isClosed_graph
  have heq : (T.toFun.graph : Set (T.domain × F)) =
      (fun p : T.domain × F => ((p.1 : E), p.2)) ⁻¹' (T.graph : Set (E × F)) := by
    ext p
    rcases p with ⟨x, y⟩
    rw [SetLike.mem_coe, LinearMap.mem_graph_iff]
    change y = T x ↔ (x.val, y) ∈ T.graph
    rw [T.mem_graph_iff]
    exact ⟨fun h => ⟨x, rfl, h.symm⟩, fun ⟨z, hz, h⟩ =>
      h.symm.trans (congrArg T (Subtype.ext hz))⟩
  rw [heq]
  exact hT.preimage ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)

/-- A bounded partial operator extends to a bounded operator on the whole
Hilbert space, as in **Part (E)**. -/
theorem exists_bounded_extension [CompleteSpace E] [CompleteSpace F]
    (T : E →ₗ.[𝕜] F) (hT : IsBoundedOperator T) :
    ∃ B : E →L[𝕜] F, ∀ x : T.domain, B x = T x := by
  let C := T.domain.topologicalClosure
  let e : T.domain →ₗ[𝕜] C := Submodule.inclusion T.domain.le_topologicalClosure
  have he : DenseRange e := by
    intro x
    rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]
    have heq : Subtype.val '' Set.range e = (T.domain : Set E) := by
      ext y
      constructor
      · rintro ⟨z, ⟨u, rfl⟩, rfl⟩
        exact u.prop
      · intro hy
        exact ⟨e ⟨y, hy⟩, ⟨⟨y, hy⟩, rfl⟩, rfl⟩
    rw [heq]
    exact x.prop
  have hT' : ∃ c : ℝ, ∀ x : T.domain, ‖T.toFun x‖ ≤ c * ‖e x‖ := hT
  refine ⟨(T.toFun.extendOfNorm e).comp C.orthogonalProjectionOnto, fun x => ?_⟩
  change T.toFun.extendOfNorm e (C.orthogonalProjectionOnto (e x)) = T x
  rw [C.orthogonalProjectionOnto_mem_subspace_eq_self]
  exact LinearMap.extendOfNorm_eq he hT' x

/-- The restriction to the carrier in **Part (F)** of [benIsrael2003generalized],
Chapter 9, Section 2. -/
abbrev restrictCarrier (T : E →ₗ.[𝕜] F) : E →ₗ.[𝕜] F :=
  T.domRestrict T.kerᗮ

/-- The carrier restriction has exactly the carrier as its domain. -/
theorem restrictCarrier_domain (T : E →ₗ.[𝕜] F) : (restrictCarrier T).domain = carrier T :=
  inf_comm _ _

/-- The original operator extends its carrier restriction. -/
theorem restrictCarrier_le (T : E →ₗ.[𝕜] F) : restrictCarrier T ≤ T :=
  LinearPMap.domRestrict_le

/-- The carrier restriction has zero kernel. -/
theorem restrictCarrier_ker (T : E →ₗ.[𝕜] F) : (restrictCarrier T).ker = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  have hxC := (restrictCarrier T).ker_le_domain hx
  rw [restrictCarrier_domain] at hxC
  have hxK : x ∈ T.ker := by
    obtain ⟨y, hy, hy0⟩ := (LinearPMap.mem_ker_iff.mp hx)
    refine LinearPMap.mem_ker_iff.mpr ⟨⟨x, hxC.1⟩, rfl, ?_⟩
    rw [← hy0]
    exact ((restrictCarrier_le T).2 (x := y) (y := ⟨x, hxC.1⟩) hy.symm).symm
  have he : x ∈ T.ker ⊓ T.kerᗮ := ⟨hxK, hxC.2⟩
  rwa [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] at he

/-- Restricting a closed operator to its carrier preserves closedness. -/
theorem restrictCarrier_isClosed (T : E →ₗ.[𝕜] F) (hT : T.IsClosed) :
    (restrictCarrier T).IsClosed := by
  have heq : ((restrictCarrier T).graph : Set (E × F)) =
      (T.graph : Set (E × F)) ∩ Prod.fst ⁻¹' (T.kerᗮ : Set E) := by
    ext p
    change p ∈ (restrictCarrier T).graph ↔ p ∈ T.graph ∧ p.1 ∈ T.kerᗮ
    constructor
    · intro hp
      have hr := LinearPMap.le_graph_of_le (restrictCarrier_le T) hp
      obtain ⟨x, hx, _⟩ := (restrictCarrier T).mem_graph_iff.mp hp
      have hxC : x.val ∈ carrier T :=
        Eq.mp (congrArg (fun D : Submodule 𝕜 E => x.val ∈ D) (restrictCarrier_domain T)) x.prop
      exact ⟨hr, hx ▸ hxC.2⟩
    · rintro ⟨hp, ho⟩
      obtain ⟨x, hx, hy⟩ := T.mem_graph_iff.mp hp
      have hxC : (x : E) ∈ (restrictCarrier T).domain := by
        rw [restrictCarrier_domain]
        exact ⟨x.prop, hx.symm ▸ ho⟩
      exact (restrictCarrier T).mem_graph_iff.mpr
        ⟨⟨x, hxC⟩, hx, (LinearPMap.domRestrict_apply rfl).trans hy⟩
  change IsClosed ((restrictCarrier T).graph : Set (E × F))
  rw [heq]
  exact hT.inter (T.ker.isClosed_orthogonal.preimage continuous_fst)

/-- The range of the carrier restriction lies in the original range. -/
theorem restrictCarrier_range_le (T : E →ₗ.[𝕜] F) :
    (restrictCarrier T).toFun.range ≤ T.toFun.range := by
  rintro y ⟨x, rfl⟩
  exact ⟨⟨x, (restrictCarrier_le T).1 x.prop⟩,
    (LinearPMap.domRestrict_apply rfl).symm⟩

/-- If the domain decomposes along the kernel, restricting to the carrier
preserves the range. -/
theorem restrictCarrier_range (T : E →ₗ.[𝕜] F)
    (h : IsDecomposable T.domain T.ker) :
    (restrictCarrier T).toFun.range = T.toFun.range := by
  refine le_antisymm (restrictCarrier_range_le T) ?_
  rintro y ⟨x, rfl⟩
  have hx : x.val ∈ T.ker ⊔ carrier T := h.2 ▸ x.prop
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hx
  let a : T.domain := ⟨u, T.ker_le_domain hu⟩
  let b : T.domain := ⟨v, hv.1⟩
  have hx' : a + b = x := Subtype.ext huv
  have ha : T a = 0 := LinearPMap.coe_mem_ker_iff.mp hu
  have hb : v ∈ (restrictCarrier T).domain := restrictCarrier_domain T ▸ hv
  refine ⟨⟨v, hb⟩, ?_⟩
  calc
    _ = T b := LinearPMap.domRestrict_apply rfl
    _ = T (a + b) := by
      change T.toFun b = T.toFun (a + b)
      rw [map_add, show T.toFun a = 0 from ha, zero_add]
    _ = T x := congrArg T hx'

/-- **Part (F)** of [benIsrael2003generalized], Chapter 9, Section 2.
The inverse of the carrier restriction has the swapped graph, and
closedness is equivalent on either side. -/
theorem restrictCarrier_inverse (T : E →ₗ.[𝕜] F) :
    (restrictCarrier T).inverse.graph = (restrictCarrier T).graph.map
      (LinearEquiv.prodComm 𝕜 E F : (E × F) →ₗ[𝕜] (F × E)) ∧
      ((restrictCarrier T).inverse.IsClosed ↔ (restrictCarrier T).IsClosed) :=
  ⟨LinearPMap.inverse_graph (restrictCarrier_ker T),
    LinearPMap.inverse_closed_iff (restrictCarrier_ker T)⟩

/-- The partial composition has the largest domain on which the first
operator is defined and its value belongs to the domain of the second. -/
def partialComp {G : Type*} [AddCommGroup G] [Module 𝕜 G]
    (S : F →ₗ.[𝕜] G) (T : E →ₗ.[𝕜] F) : E →ₗ.[𝕜] G := by
  let D := (S.domain.comap T.toFun).map T.domain.subtype
  have hD : D ≤ T.domain := fun _ ⟨u, _, hu⟩ => hu ▸ u.prop
  let f := T.toFun.comp (Submodule.inclusion hD)
  have hf (x : D) : f x ∈ S.domain := by
    obtain ⟨u, hu, he⟩ := x.prop
    have hxu : Submodule.inclusion hD x = u := Subtype.ext he.symm
    change T.toFun (Submodule.inclusion hD x) ∈ S.domain
    rw [hxu]
    exact hu
  exact ⟨D, S.toFun.comp (f.codRestrict S.domain hf)⟩

/-- Domain membership for partial composition. -/
theorem partialComp_mem_domain {G : Type*} [AddCommGroup G] [Module 𝕜 G]
    (S : F →ₗ.[𝕜] G) (T : E →ₗ.[𝕜] F) (x : E) :
    x ∈ (partialComp S T).domain ↔ ∃ hx : x ∈ T.domain, T ⟨x, hx⟩ ∈ S.domain := by
  change (∃ u : T.domain, T u ∈ S.domain ∧ u.val = x) ↔ _
  constructor
  · rintro ⟨u, h, hu⟩
    refine ⟨hu ▸ u.prop, ?_⟩
    rwa [show (⟨x, hu ▸ u.prop⟩ : T.domain) = u from Subtype.ext hu.symm]
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

/-- Evaluation of partial composition. -/
theorem partialComp_apply {G : Type*} [AddCommGroup G] [Module 𝕜 G]
    (S : F →ₗ.[𝕜] G) (T : E →ₗ.[𝕜] F) (x : E)
    (hx : x ∈ T.domain) (hTx : T ⟨x, hx⟩ ∈ S.domain) :
    partialComp S T ⟨x, (partialComp_mem_domain S T x).mpr ⟨hx, hTx⟩⟩ = S ⟨T ⟨x, hx⟩, hTx⟩ :=
  rfl

end PartialOperators

section Adjoints

/-- **Part (G)** of [benIsrael2003generalized], Chapter 9, Section 2.
The graph in the Hilbert product with the sum inner product. -/
def hilbertGraph (T : E →ₗ.[𝕜] F) : Submodule 𝕜 (WithLp 2 (E × F)) :=
  T.graph.map (WithLp.linearEquiv 2 𝕜 (E × F)).symm.toLinearMap

private theorem mem_hilbertGraph_iff (T : E →ₗ.[𝕜] F) (p : WithLp 2 (E × F)) :
    p ∈ hilbertGraph T ↔ WithLp.ofLp p ∈ T.graph := by
  rw [hilbertGraph, Submodule.mem_map]
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact hq
  · intro hp
    exact ⟨WithLp.ofLp p, hp, rfl⟩

private theorem mem_closure_hilbertGraph_iff (T : E →ₗ.[𝕜] F) (p : WithLp 2 (E × F)) :
    p ∈ (hilbertGraph T).topologicalClosure ↔ WithLp.ofLp p ∈ T.graph.topologicalClosure := by
  have he : (hilbertGraph T : Set (WithLp 2 (E × F))) =
      (WithLp.homeomorphProd 2 E F) ⁻¹' (T.graph : Set (E × F)) := by
    ext x
    exact mem_hilbertGraph_iff T x
  change p ∈ closure (hilbertGraph T : Set (WithLp 2 (E × F))) ↔ _
  rw [he, ← (WithLp.homeomorphProd 2 E F).preimage_closure]
  rfl

/-- The graph-orthogonality equation in **Part (G)**. -/
theorem mem_hilbertGraph_orthogonal_iff (T : E →ₗ.[𝕜] F) (p : E × F) :
    WithLp.toLp 2 p ∈ (hilbertGraph T)ᗮ ↔ ∀ x : T.domain,
      inner 𝕜 (x : E) p.1 + inner 𝕜 (T x) p.2 = 0 := by
  rw [Submodule.mem_orthogonal]
  constructor
  · intro h x
    exact h (WithLp.toLp 2 (x.val, T x)) ((mem_hilbertGraph_iff T _).mpr (T.mem_graph x))
  · intro h q hq
    obtain ⟨x, hx, hy⟩ := T.mem_graph_iff.mp ((mem_hilbertGraph_iff T q).mp hq)
    rw [WithLp.prod_inner_apply, ← hx, ← hy]
    exact h x

omit [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] in
private theorem dense_iff_orthogonal_eq_bot [CompleteSpace E] (D : Submodule 𝕜 E) :
    Dense (D : Set E) ↔ Dᗮ = ⊥ := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top,
    ← D.topologicalClosure.orthogonal_eq_bot_iff, D.orthogonal_closure]

/-- **Part (G)** of [benIsrael2003generalized], Chapter 9, Section 2.
Dense definition is equivalent to the orthogonal graph complement meeting
the horizontal axis only at zero. -/
theorem isDense_iff_graph_orthogonal_disjoint [CompleteSpace E] (T : E →ₗ.[𝕜] F) :
    Dense (T.domain : Set E) ↔
      ∀ y : E, WithLp.toLp 2 (y, (0 : F)) ∈ (hilbertGraph T)ᗮ → y = 0 := by
  rw [dense_iff_orthogonal_eq_bot, Submodule.eq_bot_iff]
  constructor
  · intro h y hy
    apply h
    rw [Submodule.mem_orthogonal]
    intro x hx
    simpa only [inner_zero_right, add_zero] using
      (mem_hilbertGraph_orthogonal_iff T (y, 0)).mp hy ⟨x, hx⟩
  · intro h y hy
    apply h y
    apply (mem_hilbertGraph_orthogonal_iff T (y, 0)).mpr
    intro x
    simpa only [inner_zero_right, add_zero] using
      (Submodule.mem_orthogonal _ _).mp hy x x.prop

/-- The orthogonal graph complement is the inverse graph of the negative
adjoint, as in **Part (G)**. -/
theorem mem_adjoint_graph_iff_graph_orthogonal [CompleteSpace E] (T : E →ₗ.[𝕜] F)
    (hD : Dense (T.domain : Set E)) (p : E × F) :
    (p.2, -p.1) ∈ T.adjoint.graph ↔ WithLp.toLp 2 p ∈ (hilbertGraph T)ᗮ := by
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint hD,
    Submodule.mem_adjoint_iff, mem_hilbertGraph_orthogonal_iff]
  constructor
  · intro h x
    have he := h x (T x) (T.mem_graph x)
    simpa only [inner_neg_right, sub_neg_eq_add, add_comm] using he
  · intro h a b hab
    obtain ⟨x, hx, hy⟩ := T.mem_graph_iff.mp hab
    change x.val = a at hx
    change T x = b at hy
    change inner 𝕜 b p.2 - inner 𝕜 a (-p.1) = 0
    rw [← hx, ← hy, inner_neg_right, sub_neg_eq_add, add_comm]
    exact h x

/-- **Part (J)** of [benIsrael2003generalized], Chapter 9, Section 2.
The graph closure defines an operator exactly when its vertical section is
trivial. For a closable operator it gives the least closed extension. -/
theorem isClosable_iff_graphClosure_disjoint_vertical (T : E →ₗ.[𝕜] F) :
    T.IsClosable ↔ ∀ y : F, ((0 : E), y) ∈ T.graph.topologicalClosure → y = 0 := by
  constructor
  · rintro ⟨S, hS⟩ y hy
    rw [hS] at hy
    exact S.graph_fst_eq_zero_snd hy rfl
  · intro h
    obtain ⟨S, hS, _⟩ := (graph_iff_disjoint_vertical T.graph.topologicalClosure).mpr h
    exact ⟨S, hS.1.symm⟩

/-- The closure is the least closed extension, as in **Part (J)**. -/
theorem closure_le_iff (T S : E →ₗ.[𝕜] F) (hS : S.IsClosed) : T.closure ≤ S ↔ T ≤ S := by
  refine ⟨fun h => T.le_closure.trans h, fun h => ?_⟩
  have hC := hS.isClosable.leIsClosable h
  apply LinearPMap.le_of_le_graph
  rw [← hC.graph_closure_eq_closure_graph]
  exact T.graph.topologicalClosure_minimal (LinearPMap.le_graph_of_le h) hS

/-- A densely defined closable partial operator has a densely defined adjoint. -/
theorem dense_adjoint_domain_of_isClosable [CompleteSpace E] [CompleteSpace F]
    (T : E →ₗ.[𝕜] F) (hD : Dense (T.domain : Set E)) (hC : T.IsClosable) :
    Dense (T.adjoint.domain : Set F) := by
  rw [dense_iff_orthogonal_eq_bot, Submodule.eq_bot_iff]
  intro y hy
  have hmem : WithLp.toLp 2 ((0 : E), y) ∈ (hilbertGraph T)ᗮᗮ := by
    rw [Submodule.mem_orthogonal]
    intro q hq
    have hqAdj := (mem_adjoint_graph_iff_graph_orthogonal T hD (WithLp.ofLp q)).mpr hq
    obtain ⟨u, hu, _⟩ := T.adjoint.mem_graph_iff.mp hqAdj
    change u.val = (WithLp.ofLp q).2 at hu
    have hqDom : (WithLp.ofLp q).2 ∈ T.adjoint.domain := hu ▸ u.prop
    rw [WithLp.prod_inner_apply]
    simp only [inner_zero_right, zero_add]
    exact (Submodule.mem_orthogonal _ _).mp hy _ hqDom
  rw [Submodule.orthogonal_orthogonal_eq_closure, mem_closure_hilbertGraph_iff] at hmem
  exact (isClosable_iff_graphClosure_disjoint_vertical T).mp hC y hmem

/-- A densely defined operator is closable exactly when its adjoint has
dense domain. -/
theorem isClosable_iff_dense_adjoint_domain [CompleteSpace E] [CompleteSpace F]
    (T : E →ₗ.[𝕜] F) (hD : Dense (T.domain : Set E)) :
    T.IsClosable ↔ Dense (T.adjoint.domain : Set F) := by
  refine ⟨dense_adjoint_domain_of_isClosable T hD, fun h => ?_⟩
  exact (LinearPMap.adjoint_isClosed h).isClosable.leIsClosable
    ((LinearPMap.adjoint_isFormalAdjoint hD).le_adjoint h)

/-- **Part (J)** of [benIsrael2003generalized], Chapter 9, Section 2.
The double adjoint of a densely defined closable operator is its closure. -/
theorem closure_eq_adjoint_adjoint [CompleteSpace E] [CompleteSpace F]
    (T : E →ₗ.[𝕜] F) (hD : Dense (T.domain : Set E)) (hC : T.IsClosable) :
    T.closure = T.adjoint.adjoint := by
  apply LinearPMap.eq_of_eq_graph
  rw [← hC.graph_closure_eq_closure_graph, LinearPMap.adjoint_graph_eq_graph_adjoint
    (dense_adjoint_domain_of_isClosable T hD hC)]
  ext p
  rw [← mem_closure_hilbertGraph_iff T (WithLp.toLp 2 p),
    ← Submodule.orthogonal_orthogonal_eq_closure, Submodule.mem_orthogonal,
    Submodule.mem_adjoint_iff]
  constructor
  · intro hp a b hab
    have hq := (mem_adjoint_graph_iff_graph_orthogonal T hD (-b, a)).mp (by simpa using hab)
    have h := hp (WithLp.toLp 2 (-b, a)) hq
    change inner 𝕜 (-b) p.1 + inner 𝕜 a p.2 = 0 at h
    rw [inner_neg_left] at h
    linear_combination -h
  · intro hp q hq
    have h := hp _ _ ((mem_adjoint_graph_iff_graph_orthogonal T hD (WithLp.ofLp q)).mpr hq)
    rw [inner_neg_left] at h
    rw [WithLp.prod_inner_apply]
    linear_combination -h

/-- A closed densely defined operator equals its double adjoint. -/
theorem adjoint_adjoint_eq_of_isClosed [CompleteSpace E] [CompleteSpace F]
    (T : E →ₗ.[𝕜] F) (hD : Dense (T.domain : Set E)) (hC : T.IsClosed) :
    T.adjoint.adjoint = T := by
  rw [← closure_eq_adjoint_adjoint T hD hC.isClosable]
  apply LinearPMap.eq_of_eq_graph
  rw [← hC.isClosable.graph_closure_eq_closure_graph]
  exact hC.submodule_topologicalClosure_eq

/-- For a densely defined operator, the adjoint kernel is the orthogonal
complement of the range, as in **Equation (3)**. -/
theorem ker_adjoint_eq_orthogonal_range [CompleteSpace E]
    (T : E →ₗ.[𝕜] F) (hD : Dense (T.domain : Set E)) : T.adjoint.ker = T.toFun.rangeᗮ := by
  ext y
  rw [LinearPMap.mem_ker_iff, Submodule.mem_orthogonal]
  constructor
  · rintro ⟨z, rfl, hz⟩ _ ⟨x, rfl⟩
    change inner 𝕜 (T x) (z : F) = 0
    rw [(LinearPMap.adjoint_isFormalAdjoint hD).symm x z, hz, inner_zero_right]
  · intro hy
    have he (x : T.domain) : inner 𝕜 (0 : E) (x : E) = inner 𝕜 y (T x) := by
      rw [inner_zero_left, ← inner_conj_symm, hy (T x) ⟨x, rfl⟩, map_zero]
    have hz : y ∈ T.adjoint.domain := LinearPMap.mem_adjoint_domain_of_exists y ⟨0, he⟩
    exact ⟨⟨y, hz⟩, rfl, LinearPMap.adjoint_apply_eq hD _ he⟩

/-- The dual equality in **Equation (3)** for a closed densely defined operator.
For a closable operator the corresponding kernel is that of the closure. -/
theorem orthogonal_range_adjoint_eq_ker [CompleteSpace E] [CompleteSpace F]
    (T : E →ₗ.[𝕜] F) (hD : Dense (T.domain : Set E)) (hC : T.IsClosed) :
    T.adjoint.toFun.rangeᗮ = T.ker := by
  rw [← ker_adjoint_eq_orthogonal_range T.adjoint
    (dense_adjoint_domain_of_isClosable T hD hC.isClosable),
    adjoint_adjoint_eq_of_isClosed T hD hC]

/-- An operator has dense range exactly when its adjoint is injective. -/
theorem dense_range_iff_injective_adjoint [CompleteSpace E] [CompleteSpace F]
    (T : E →ₗ.[𝕜] F) (hD : Dense (T.domain : Set E)) :
    Dense (T.toFun.range : Set F) ↔ Function.Injective T.adjoint := by
  rw [← LinearPMap.ker_eq_bot, ker_adjoint_eq_orthogonal_range T hD,
    dense_iff_orthogonal_eq_bot]

/-- The adjoint of a closed operator has dense range exactly when the
original densely defined operator is injective. -/
theorem dense_range_adjoint_iff_injective [CompleteSpace E] [CompleteSpace F]
    (T : E →ₗ.[𝕜] F) (hD : Dense (T.domain : Set E)) (hC : T.IsClosed) :
    Dense (T.adjoint.toFun.range : Set E) ↔ Function.Injective T := by
  rw [← LinearPMap.ker_eq_bot, dense_iff_orthogonal_eq_bot,
    orthogonal_range_adjoint_eq_ker T hD hC]

private theorem mem_swapped_inverse_graph (T : E →ₗ.[𝕜] F) (hT : T.ker = ⊥)
    (p : E × F) : p.swap ∈ T.inverse.graph ↔ p ∈ T.graph := by
  rw [LinearPMap.inverse_graph hT, Submodule.map_equiv_eq_comap_symm]
  rfl

/-- **Part (I)** of [benIsrael2003generalized], Chapter 9, Section 2.
If an injective operator has dense domain and dense range, the adjoint of
its partial inverse is the partial inverse of its adjoint. -/
theorem adjoint_inverse [CompleteSpace E] [CompleteSpace F] (T : E →ₗ.[𝕜] F)
    (hD : Dense (T.domain : Set E)) (hR : Dense (T.toFun.range : Set F))
    (hT : T.ker = ⊥) : T.inverse.adjoint = T.adjoint.inverse := by
  have hI : Dense (T.inverse.domain : Set F) := by rwa [LinearPMap.inverse_domain]
  have hA : T.adjoint.ker = ⊥ := (ker_adjoint_eq_orthogonal_range T hD).trans
    ((dense_iff_orthogonal_eq_bot T.toFun.range).mp hR)
  apply LinearPMap.eq_of_eq_graph
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint hI]
  ext p
  have hp := mem_swapped_inverse_graph T.adjoint hA p.swap
  rw [Prod.swap_swap, LinearPMap.adjoint_graph_eq_graph_adjoint hD] at hp
  rw [hp, Submodule.mem_adjoint_iff, Submodule.mem_adjoint_iff]
  constructor
  · intro h a b hab
    have hba := h b a ((mem_swapped_inverse_graph T hT (a, b)).mpr hab)
    exact sub_eq_zero.mpr (sub_eq_zero.mp hba).symm
  · intro h b a hab
    have hab' := h a b ((mem_swapped_inverse_graph T hT (a, b)).mp hab)
    exact sub_eq_zero.mpr (sub_eq_zero.mp hab').symm

end Adjoints

section GramOperators

/-- **Part (K)** of [benIsrael2003generalized], Chapter 9, Section 2.
A symmetric partial operator has dense domain and agrees with its adjoint
on that domain. -/
def IsSymmetricOperator [CompleteSpace E] (T : E →ₗ.[𝕜] E) : Prop :=
  Dense (T.domain : Set E) ∧ T ≤ T.adjoint

/-- **Part (K)** of [benIsrael2003generalized], Chapter 9, Section 2.
A nonnegative partial operator is self-adjoint and its quadratic form is
nonnegative on its domain. -/
def IsNonnegativeOperator [CompleteSpace E] (T : E →ₗ.[𝕜] E) : Prop :=
  IsSelfAdjoint T ∧ T.IsMonotone

private theorem gramOperator_properties [CompleteSpace E] [CompleteSpace F]
    (T : E →ₗ.[𝕜] F) (hT : T.IsClosed) (hD : Dense (T.domain : Set E)) :
    let A := partialComp T.adjoint T
    A.IsMaximalMonotone ∧ A.IsFormalAdjoint A := by
  intro A
  have hval (u : A.domain) : ∃ (v : T.domain) (hv : T v ∈ T.adjoint.domain),
      (v : E) = u.val ∧ A u = T.adjoint ⟨T v, hv⟩ := by
    obtain ⟨h, hv⟩ := (partialComp_mem_domain T.adjoint T u.val).mp u.prop
    exact ⟨⟨u.val, h⟩, hv, rfl, partialComp_apply T.adjoint T u.val h hv⟩
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro u
    obtain ⟨v, hv, hvu, he⟩ := hval u
    rw [he, ← hvu, LinearPMap.adjoint_isFormalAdjoint hD ⟨T v, hv⟩ v,
      inner_self_eq_norm_sq]
    exact sq_nonneg _
  · intro x
    let K := hilbertGraph T
    have hK : IsClosed (K : Set (WithLp 2 (E × F))) := by
      convert hT.preimage (WithLp.prod_continuous_ofLp 2 E F) using 1
      ext p
      exact mem_hilbertGraph_iff T p
    let : CompleteSpace K := hK.completeSpace_coe
    let p : WithLp 2 (E × F) := WithLp.toLp 2 (x, (0 : F))
    let q := K.starProjection p
    have hp : WithLp.ofLp q ∈ T.graph :=
      (mem_hilbertGraph_iff T q).mp (K.starProjection_apply_mem p)
    obtain ⟨v, hv, hTv⟩ := T.mem_graph_iff.mp hp
    have hq : q = WithLp.toLp 2 (v.val, T v) := by
      apply (WithLp.equiv 2 (E × F)).injective
      exact Prod.ext hv.symm hTv.symm
    have ho := K.sub_starProjection_mem_orthogonal p
    change p - q ∈ (hilbertGraph T)ᗮ at ho
    rw [hq, show p = WithLp.toLp 2 (x, (0 : F)) from rfl,
      ← WithLp.toLp_sub, Prod.mk_sub_mk, zero_sub] at ho
    have ha : (-T v, -(x - v.val)) ∈ T.adjoint.graph :=
      (mem_adjoint_graph_iff_graph_orthogonal T hD (x - v.val, -T v)).mpr ho
    have ha' : (T v, x - v.val) ∈ T.adjoint.graph := by
      simpa only [Prod.neg_mk, neg_neg] using T.adjoint.graph.neg_mem ha
    obtain ⟨w, hw, he⟩ := T.adjoint.mem_graph_iff.mp ha'
    change w.val = T v at hw
    have hV : T v ∈ T.adjoint.domain := hw ▸ w.prop
    have hA : v.val ∈ A.domain :=
      (partialComp_mem_domain T.adjoint T v.val).mpr ⟨v.prop, hV⟩
    refine ⟨⟨v.val, hA⟩, ?_⟩
    have hTw : T.adjoint ⟨T v, hV⟩ = x - v.val :=
      (congrArg T.adjoint (Subtype.ext hw.symm)).trans he
    rw [show A ⟨v.val, hA⟩ = T.adjoint ⟨T v, hV⟩ from
      partialComp_apply T.adjoint T v.val v.prop hV, hTw]
    change v.val + (x - v.val) = x
    abel
  · intro u w
    obtain ⟨v, hv, hvu, he⟩ := hval u
    obtain ⟨z, hz, hzw, hf⟩ := hval w
    rw [he, hf, ← hvu, ← hzw, LinearPMap.adjoint_isFormalAdjoint hD ⟨T v, hv⟩ z,
      (LinearPMap.adjoint_isFormalAdjoint hD).symm v ⟨T z, hz⟩]

/-- **Part (K)** of [benIsrael2003generalized], Chapter 9, Section 2.
Both partial Gram operators of a densely defined closed operator are
nonnegative. The shifts by the identity are surjective and have bounded
inverses given by their resolvents at one. -/
theorem gramOperators_nonnegative [CompleteSpace E] [CompleteSpace F]
    (T : E →ₗ.[𝕜] F) (hT : T.IsClosed) (hD : Dense (T.domain : Set E)) :
    let A := partialComp T.adjoint T
    let B := partialComp T T.adjoint
    IsNonnegativeOperator A ∧ A.IsMaximalMonotone ∧
      IsNonnegativeOperator B ∧ B.IsMaximalMonotone := by
  intro A B
  have hA := gramOperator_properties T hT hD
  have hDa := dense_adjoint_domain_of_isClosable T hD hT.isClosable
  have hB := gramOperator_properties T.adjoint (LinearPMap.adjoint_isClosed hD) hDa
  dsimp only at hB
  rw [adjoint_adjoint_eq_of_isClosed T hD hT] at hB
  exact ⟨⟨hA.1.isSelfAdjoint_of_isFormalAdjoint hA.2, hA.1.isMonotone⟩, hA.1,
    ⟨hB.1.isSelfAdjoint_of_isFormalAdjoint hB.2, hB.1.isMonotone⟩, hB.1⟩

/-- The bounded inverse of the shifted left Gram operator is defined on
the whole Hilbert space. -/
theorem gramOperator_resolvent_one [CompleteSpace E] [CompleteSpace F]
    (T : E →ₗ.[𝕜] F) (hT : T.IsClosed) (hD : Dense (T.domain : Set E)) :
    let A := partialComp T.adjoint T
    ∃ J : E →L[𝕜] E,
      (∀ y : E, ∃ hy : J y ∈ A.domain, J y + A ⟨J y, hy⟩ = y) ∧
      ∀ x : A.domain, J (x.val + A x) = x.val := by
  intro A
  have hA := (gramOperator_properties T hT hD).1
  refine ⟨A.resolvent 1, fun y => ⟨hA.resolvent_apply_mem_domain one_pos y, ?_⟩, fun x => ?_⟩
  · simpa only [RCLike.ofReal_one, one_smul] using hA.resolvent_add_smul_apply one_pos y
  · simpa only [RCLike.ofReal_one, one_smul] using hA.resolvent_apply_add_smul one_pos x

/-- The bounded inverse of the shifted right Gram operator is defined on
the whole Hilbert space. -/
theorem adjointGramOperator_resolvent_one [CompleteSpace E] [CompleteSpace F]
    (T : E →ₗ.[𝕜] F) (hT : T.IsClosed) (hD : Dense (T.domain : Set E)) :
    let A := partialComp T T.adjoint
    ∃ J : F →L[𝕜] F,
      (∀ y : F, ∃ hy : J y ∈ A.domain, J y + A ⟨J y, hy⟩ = y) ∧
      ∀ x : A.domain, J (x.val + A x) = x.val := by
  have h := gramOperator_resolvent_one T.adjoint (LinearPMap.adjoint_isClosed hD)
    (dense_adjoint_domain_of_isClosable T hD hT.isClosable)
  rw [adjoint_adjoint_eq_of_isClosed T hD hT] at h
  exact h

end GramOperators

section Projections

omit [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- **Part (L)** of [benIsrael2003generalized], Chapter 9, Section 2.
A bounded projection is orthogonal exactly when it is the orthogonal
projection onto a closed subspace. -/
theorem orthogonalProjector_iff [CompleteSpace E] (P : E →L[𝕜] E) :
    IsStarProjection P ↔ ∃ (L : Submodule 𝕜 E) (hL : IsClosed (L : Set E)),
      let _ : CompleteSpace L := hL.completeSpace_coe
      P = L.starProjection := by
  constructor
  · intro h
    obtain ⟨_, hP⟩ := isStarProjection_iff_eq_starProjection_range.mp h
    refine ⟨P.range, ContinuousLinearMap.IsIdempotentElem.isClosed_range h.isIdempotentElem, ?_⟩
    exact hP
  · rintro ⟨L, hL, rfl⟩
    let : CompleteSpace L := hL.completeSpace_coe
    exact isStarProjection_starProjection

/-- An orthogonal projection has a closed range orthogonal to its kernel. -/
theorem orthogonalProjector_range_ker [CompleteSpace E] (P : E →L[𝕜] E)
    (hP : IsStarProjection P) : IsClosed (P.range : Set E) ∧
      P.ker = P.rangeᗮ ∧ IsCompl P.range P.ker := by
  obtain ⟨L, hL, h⟩ := (orthogonalProjector_iff P).mp hP
  let : CompleteSpace L := hL.completeSpace_coe
  rw [h, L.range_starProjection, L.ker_starProjection]
  exact ⟨hL, rfl, L.isCompl_orthogonal⟩

/-- Each closed subspace is the range of a unique orthogonal projection. -/
theorem existsUnique_orthogonalProjector [CompleteSpace E] (L : Submodule 𝕜 E)
    (hL : IsClosed (L : Set E)) : ∃! P : E →L[𝕜] E, IsStarProjection P ∧ P.range = L := by
  let : CompleteSpace L := hL.completeSpace_coe
  refine ⟨L.starProjection, ⟨(orthogonalProjector_iff _).mpr ⟨L, hL, rfl⟩,
    L.range_starProjection⟩, ?_⟩
  rintro P ⟨hP, hr⟩
  obtain ⟨M, hM, he⟩ := (orthogonalProjector_iff P).mp hP
  let : CompleteSpace M := hM.completeSpace_coe
  have hML : M = L := by rwa [he, M.range_starProjection] at hr
  subst M
  exact he

end Projections

section NormalSolvability

/-- **Part (M)** of [benIsrael2003generalized], Chapter 9, Section 2.
Normal solvability means the range of the closed operator is closed. -/
def IsNormallySolvable (T : E →ₗ.[𝕜] F) : Prop :=
  T.IsClosed ∧ IsClosed (T.toFun.range : Set F)

open scoped ENNReal in
/-- **Equation (4)** of [benIsrael2003generalized], Chapter 9.
The reduced minimum modulus is the infimum of the norm ratios on nonzero
carrier vectors. It is infinite if the carrier is trivial. -/
noncomputable def reducedMinimumModulus (T : E →ₗ.[𝕜] F) : ℝ≥0∞ :=
  ⨅ x : {x : (restrictCarrier T).domain // x ≠ 0},
    ENNReal.ofReal (‖restrictCarrier T x.val‖ / ‖x.val‖)

/-- Positive reduced minimum modulus is equivalent to a uniform positive
lower bound for the carrier restriction. -/
theorem reducedMinimumModulus_pos_iff (T : E →ₗ.[𝕜] F) :
    0 < reducedMinimumModulus T ↔ ∃ c : ℝ, 0 < c ∧
      ∀ x : (restrictCarrier T).domain, c * ‖x‖ ≤ ‖restrictCarrier T x‖ := by
  constructor
  · intro h
    obtain ⟨c, hc, hcγ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp h
    refine ⟨c, by exact_mod_cast hc, fun x => ?_⟩
    by_cases hx : x = 0
    · rw [hx, LinearPMap.map_zero, norm_zero, norm_zero, mul_zero]
    · apply (le_div_iff₀ (norm_pos_iff.mpr hx)).mp
      apply (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp
      rw [ENNReal.ofReal_coe_nnreal]
      exact hcγ.le.trans (iInf_le _ (⟨x, hx⟩ : {x : (restrictCarrier T).domain // x ≠ 0}))
  · rintro ⟨c, hc, h⟩
    apply (ENNReal.ofReal_pos.mpr hc).trans_le
    unfold reducedMinimumModulus
    apply le_iInf
    intro x
    apply ENNReal.ofReal_le_ofReal
    exact (le_div_iff₀ (norm_pos_iff.mpr x.prop)).mpr (h x.val)

private theorem isBoundedOperator_inverse_iff_norm_le (S : E →ₗ.[𝕜] F) (hS : S.ker = ⊥) :
    IsBoundedOperator S.inverse ↔ ∃ c : ℝ, ∀ x : S.domain, ‖x‖ ≤ c * ‖S x‖ := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, fun x => ?_⟩
    have hmem : S x ∈ S.inverse.domain := by
      rw [LinearPMap.inverse_domain]
      exact ⟨x, rfl⟩
    have hi := LinearPMap.inverse_apply_eq hS (y := ⟨S x, hmem⟩) (x := x) rfl
    have h := hc ⟨S x, hmem⟩
    rw [hi] at h
    exact h
  · rintro ⟨c, hc⟩
    refine ⟨c, fun y => ?_⟩
    have hmem : y.val ∈ S.toFun.range :=
      Eq.mp (congrArg (fun D : Submodule 𝕜 F => y.val ∈ D) LinearPMap.inverse_domain) y.prop
    obtain ⟨x, hx⟩ := hmem
    have h := hc x
    change S x = y.val at hx
    rw [LinearPMap.inverse_apply_eq hS hx]
    rwa [hx] at h

/-- **Part (I)** of [benIsrael2003generalized], Chapter 9, Section 2.
An injective densely defined operator has a bounded partial inverse
exactly when its adjoint is surjective. -/
theorem isBoundedOperator_inverse_iff_adjoint_range_top [CompleteSpace E] [CompleteSpace F]
    (T : E →ₗ.[𝕜] F) (hD : Dense (T.domain : Set E)) (hT : T.ker = ⊥) :
    IsBoundedOperator T.inverse ↔ T.adjoint.toFun.range = ⊤ := by
  constructor
  · intro h
    obtain ⟨B, hB⟩ := exists_bounded_extension T.inverse h
    apply LinearMap.range_eq_top.mpr
    intro x
    have hBT (u : T.domain) : B (T u) = u := by
      have hu : T u ∈ T.inverse.domain := by
        rw [LinearPMap.inverse_domain]
        exact ⟨u, rfl⟩
      exact (hB ⟨T u, hu⟩).trans
        (LinearPMap.inverse_apply_eq hT (y := ⟨T u, hu⟩) rfl)
    have he (u : T.domain) : inner 𝕜 x (u : E) = inner 𝕜 (B.adjoint x) (T u) := by
      rw [B.adjoint_inner_left, hBT]
    have hz : B.adjoint x ∈ T.adjoint.domain :=
      LinearPMap.mem_adjoint_domain_of_exists _ ⟨x, he⟩
    exact ⟨⟨_, hz⟩, LinearPMap.adjoint_apply_eq hD _ he⟩
  · intro h
    let A := T.adjoint
    let : CompleteSpace A.graph := (LinearPMap.adjoint_isClosed hD).completeSpace_graph
    let B := (ContinuousLinearMap.snd 𝕜 F E).comp A.graph.subtypeL
    have hB : Function.Surjective B := by
      intro x
      obtain ⟨u, hu⟩ := LinearMap.range_eq_top.mp h x
      exact ⟨⟨(u.val, A u), A.mem_graph u⟩, hu⟩
    obtain ⟨C, hC, hp⟩ := B.exists_preimage_norm_le hB
    apply (isBoundedOperator_inverse_iff_norm_le T hT).mpr
    refine ⟨C, fun u => ?_⟩
    by_cases hu : u = 0
    · simp [hu]
    · obtain ⟨p, hpu, hn⟩ := hp u.val
      obtain ⟨v, hv, hAv⟩ := A.mem_graph_iff.mp p.prop
      change v.val = p.val.1 at hv
      have hf : A v = (u : E) := hAv.trans hpu
      have hvn : ‖v.val‖ ≤ C * ‖u.val‖ := by
        rw [hv]
        exact (norm_fst_le p.val).trans hn
      have he : inner 𝕜 (u : E) u = inner 𝕜 (v : F) (T u) := by
        calc
          _ = inner 𝕜 (A v) (u : E) := congrArg (fun z => inner 𝕜 z (u : E)) hf.symm
          _ = _ := LinearPMap.adjoint_isFormalAdjoint hD v u
      apply (mul_le_mul_iff_left₀ (norm_pos_iff.mpr hu)).mp
      calc
        ‖u‖ * ‖u‖ = RCLike.re (inner 𝕜 (u : E) u) := by
          rw [inner_self_eq_norm_sq, pow_two]; rfl
        _ = RCLike.re (inner 𝕜 (v : F) (T u)) := congrArg RCLike.re he
        _ ≤ ‖v.val‖ * ‖T u‖ := re_inner_le_norm _ _
        _ ≤ (C * ‖u.val‖) * ‖T u‖ := mul_le_mul_of_nonneg_right hvn (norm_nonneg _)
        _ = (C * ‖T u‖) * ‖u‖ := by rw [mul_right_comm]; rfl

private theorem reducedMinimumModulus_pos_iff_inverse_bounded (T : E →ₗ.[𝕜] F) :
    0 < reducedMinimumModulus T ↔ IsBoundedOperator (restrictCarrier T).inverse := by
  rw [reducedMinimumModulus_pos_iff,
    isBoundedOperator_inverse_iff_norm_le _ (restrictCarrier_ker T)]
  constructor
  · rintro ⟨c, hc, h⟩
    exact ⟨c⁻¹, fun x => by
      have h' := mul_le_mul_of_nonneg_left (h x) (inv_nonneg.mpr hc.le)
      simpa [← mul_assoc, hc.ne'] using h'⟩
  · rintro ⟨c, h⟩
    let d := max c 1
    have hd : 0 < d := zero_lt_one.trans_le (le_max_right _ _)
    refine ⟨d⁻¹, inv_pos.mpr hd, fun x => ?_⟩
    have h' := (h x).trans (mul_le_mul_of_nonneg_right (le_max_left c 1) (norm_nonneg _))
    have h'' := mul_le_mul_of_nonneg_left h' (inv_nonneg.mpr hd.le)
    change d⁻¹ * ‖x‖ ≤ d⁻¹ * (d * ‖restrictCarrier T x‖) at h''
    simpa [← mul_assoc, hd.ne'] using h''

/-- **Part (M)** of [benIsrael2003generalized], Chapter 9, Section 2.
For a closed operator, closed range is equivalent to boundedness of the
inverse on the carrier and to positivity of the reduced minimum modulus. -/
theorem isNormallySolvable_iff [CompleteSpace E] [CompleteSpace F]
    (T : E →ₗ.[𝕜] F) (hT : T.IsClosed) :
    (IsNormallySolvable T ↔ IsBoundedOperator (restrictCarrier T).inverse) ∧
      (IsNormallySolvable T ↔ 0 < reducedMinimumModulus T) := by
  have hi : (restrictCarrier T).inverse.IsClosed :=
    (restrictCarrier_inverse T).2.mpr (restrictCarrier_isClosed T hT)
  have hd : (restrictCarrier T).inverse.domain = T.toFun.range :=
    LinearPMap.inverse_domain.trans
      (restrictCarrier_range T (isDecomposable_of_isClosed T.ker_le_domain hT.isClosed_ker))
  have hb : IsNormallySolvable T ↔ IsBoundedOperator (restrictCarrier T).inverse := by
    refine ⟨fun h => isBoundedOperator_of_isClosed_domain _ hi (hd.symm ▸ h.2), fun h => ?_⟩
    exact ⟨hT, hd ▸ (isClosed_iff_isClosed_domain_of_bounded _ h).mp hi⟩
  exact ⟨hb, hb.trans (reducedMinimumModulus_pos_iff_inverse_bounded T).symm⟩

/-- For a densely defined closed operator, normal solvability means that
exactly the right-hand sides orthogonal to the adjoint kernel are consistent. -/
theorem isNormallySolvable_iff_orthogonal_ker_adjoint [CompleteSpace E] [CompleteSpace F]
    (T : E →ₗ.[𝕜] F) (hT : T.IsClosed) (hD : Dense (T.domain : Set E)) :
    IsNormallySolvable T ↔ T.toFun.range = T.adjoint.kerᗮ := by
  unfold IsNormallySolvable
  rw [ker_adjoint_eq_orthogonal_range T hD, Submodule.orthogonal_orthogonal_eq_closure]
  exact ⟨fun h => h.2.submodule_topologicalClosure_eq.symm,
    fun h => ⟨hT, h.symm ▸ T.toFun.range.isClosed_topologicalClosure⟩⟩

/-- Surjectivity is equivalent to bounded invertibility of the adjoint of
a closed densely defined operator with injective adjoint, as in **Part (I)**. -/
theorem isBoundedOperator_adjoint_inverse_iff_range_top [CompleteSpace E] [CompleteSpace F]
    (T : E →ₗ.[𝕜] F) (hD : Dense (T.domain : Set E)) (hT : T.IsClosed)
    (hA : T.adjoint.ker = ⊥) :
    IsBoundedOperator T.adjoint.inverse ↔ T.toFun.range = ⊤ := by
  rw [isBoundedOperator_inverse_iff_adjoint_range_top T.adjoint
    (dense_adjoint_domain_of_isClosable T hD hT.isClosable) hA,
    adjoint_adjoint_eq_of_isClosed T hD hT]

/-- **Part (I)** of [benIsrael2003generalized], Chapter 9, Section 2.
The adjoint of a surjective densely defined operator is injective and its
partial inverse is bounded. Closedness of the original graph is unnecessary
for this direction. -/
theorem inverse_adjoint_bounded_if_surjective [CompleteSpace E] [CompleteSpace F]
    (T : E →ₗ.[𝕜] F) (hD : Dense (T.domain : Set E)) (hR : T.toFun.range = ⊤) :
    T.adjoint.ker = ⊥ ∧ IsBoundedOperator T.adjoint.inverse := by
  have hk : T.adjoint.ker = ⊥ := by
    rw [ker_adjoint_eq_orthogonal_range T hD, hR, Submodule.top_orthogonal_eq_bot]
  refine ⟨hk, (isBoundedOperator_inverse_iff_norm_le T.adjoint hk).mpr ?_⟩
  let G := T.graph.topologicalClosure
  let : CompleteSpace G := T.graph.isClosed_topologicalClosure.completeSpace_coe
  let B := (ContinuousLinearMap.snd 𝕜 E F).comp G.subtypeL
  have hB : Function.Surjective B := by
    intro y
    obtain ⟨x, hx⟩ := LinearMap.range_eq_top.mp hR y
    exact ⟨⟨(x.val, T x), T.graph.le_topologicalClosure (T.mem_graph x)⟩, hx⟩
  obtain ⟨C, _, hp⟩ := B.exists_preimage_norm_le hB
  refine ⟨C, fun v => ?_⟩
  by_cases hv : v = 0
  · simp [hv]
  · obtain ⟨p, hpv, hn⟩ := hp v.val
    have hset : IsClosed {q : E × F | inner 𝕜 (T.adjoint v) q.1 = inner 𝕜 (v : F) q.2} :=
      isClosed_eq (continuous_const.inner continuous_fst) (continuous_const.inner continuous_snd)
    have hm : p.val ∈ {q : E × F | inner 𝕜 (T.adjoint v) q.1 = inner 𝕜 (v : F) q.2} := by
      refine closure_minimal (s := (T.graph : Set (E × F))) (fun q hq => ?_) hset p.prop
      obtain ⟨u, hu₁, hu₂⟩ := T.mem_graph_iff.mp hq
      change inner 𝕜 (T.adjoint v) q.1 = inner 𝕜 (v : F) q.2
      rw [← hu₁, ← hu₂]
      exact LinearPMap.adjoint_isFormalAdjoint hD v u
    change p.val.2 = v.val at hpv
    change inner 𝕜 (T.adjoint v) p.val.1 = inner 𝕜 (v : F) p.val.2 at hm
    rw [hpv] at hm
    have hpn : ‖p.val.1‖ ≤ C * ‖v.val‖ := (norm_fst_le p.val).trans hn
    apply (mul_le_mul_iff_left₀ (norm_pos_iff.mpr hv)).mp
    calc
      ‖v‖ * ‖v‖ = RCLike.re (inner 𝕜 (v : F) v) := by
        rw [inner_self_eq_norm_sq, pow_two]; rfl
      _ = RCLike.re (inner 𝕜 (T.adjoint v) p.val.1) := congrArg RCLike.re hm.symm
      _ ≤ ‖T.adjoint v‖ * ‖p.val.1‖ := re_inner_le_norm _ _
      _ ≤ ‖T.adjoint v‖ * (C * ‖v.val‖) := mul_le_mul_of_nonneg_left hpn (norm_nonneg _)
      _ = (C * ‖T.adjoint v‖) * ‖v‖ := by rw [mul_left_comm, ← mul_assoc]; rfl

/-- **Part (I)** of [benIsrael2003generalized], Chapter 9, Section 2.
Closedness makes bounded invertibility onto the whole codomain equivalent
on the two sides of the adjoint. -/
theorem adjoint_boundedInverse_and_surjective_iff [CompleteSpace E] [CompleteSpace F]
    (T : E →ₗ.[𝕜] F) (hD : Dense (T.domain : Set E)) (hT : T.IsClosed)
    (hk : T.ker = ⊥) (hka : T.adjoint.ker = ⊥) :
    (IsBoundedOperator T.adjoint.inverse ∧ T.adjoint.toFun.range = ⊤) ↔
      (IsBoundedOperator T.inverse ∧ T.toFun.range = ⊤) := by
  rw [isBoundedOperator_inverse_iff_adjoint_range_top T hD hk,
    isBoundedOperator_adjoint_inverse_iff_range_top T hD hT hka, and_comm]

/-- With closed range, the range of the adjoint is the orthogonal
complement of the kernel. -/
theorem range_adjoint_eq_orthogonal_ker_of_isNormallySolvable
    [CompleteSpace E] [CompleteSpace F] (T : E →ₗ.[𝕜] F)
    (hD : Dense (T.domain : Set E)) (hT : IsNormallySolvable T) :
    T.adjoint.toFun.range = T.kerᗮ := by
  have hI := (isNormallySolvable_iff T hT.1).1.mp hT
  obtain ⟨B, hB⟩ := exists_bounded_extension (restrictCarrier T).inverse hI
  let : CompleteSpace T.ker := hT.1.isClosed_ker.completeSpace_coe
  refine le_antisymm ?_ ?_
  · rintro _ ⟨y, rfl⟩
    change T.adjoint y ∈ T.kerᗮ
    rw [Submodule.mem_orthogonal]
    intro u hu
    let v : T.domain := ⟨u, T.ker_le_domain hu⟩
    have hv : T v = 0 := LinearPMap.coe_mem_ker_iff.mp hu
    change inner 𝕜 (v : E) (T.adjoint y) = 0
    rw [← (LinearPMap.adjoint_isFormalAdjoint hD).symm v y, hv, inner_zero_left]
  · intro x hx
    let y := B.adjoint x
    have he (u : T.domain) : inner 𝕜 x (u : E) = inner 𝕜 y (T u) := by
      let z := T.ker.starProjection (u : E)
      have hz : z ∈ T.ker := T.ker.starProjection_apply_mem _
      let u₀ : T.domain := u - ⟨z, T.ker_le_domain hz⟩
      have hz₀ : T (⟨z, T.ker_le_domain hz⟩ : T.domain) = 0 :=
        LinearPMap.coe_mem_ker_iff.mp hz
      have hTu : T u₀ = T u := by rw [show u₀ = u - _ from rfl, T.map_sub, hz₀, sub_zero]
      have hzC : u₀.val ∈ (restrictCarrier T).domain := by
        rw [restrictCarrier_domain]
        exact ⟨u₀.prop, T.ker.sub_starProjection_mem_orthogonal u.val⟩
      let w : (restrictCarrier T).domain := ⟨u₀.val, hzC⟩
      have hw : restrictCarrier T w = T u :=
        ((restrictCarrier_le T).2 (x := w) (y := u₀) rfl).trans hTu
      have hTuR : T u ∈ (restrictCarrier T).inverse.domain := by
        rw [LinearPMap.inverse_domain]
        exact ⟨w, hw⟩
      have hBT : B (T u) = u₀.val := (hB ⟨T u, hTuR⟩).trans
        (LinearPMap.inverse_apply_eq (restrictCarrier_ker T) (y := ⟨T u, hTuR⟩) hw)
      have hxz : inner 𝕜 x z = 0 := inner_eq_zero_symm.mp
        ((Submodule.mem_orthogonal _ _).mp hx z hz)
      rw [show y = B.adjoint x from rfl, B.adjoint_inner_left, hBT]
      change inner 𝕜 x u.val = inner 𝕜 x (u.val - z)
      rw [inner_sub_right, hxz, sub_zero]
    have hy : y ∈ T.adjoint.domain := LinearPMap.mem_adjoint_domain_of_exists y ⟨x, he⟩
    exact ⟨⟨y, hy⟩, LinearPMap.adjoint_apply_eq hD _ he⟩

/-- **Exercise 9** of [benIsrael2003generalized], Chapter 9.
A closed densely defined operator is normally solvable exactly when its
adjoint is normally solvable. -/
theorem exercise_9_9_adjoint [CompleteSpace E] [CompleteSpace F]
    (T : E →ₗ.[𝕜] F) (hD : Dense (T.domain : Set E)) (hT : T.IsClosed) :
    IsNormallySolvable T ↔ IsNormallySolvable T.adjoint := by
  constructor
  · intro h
    exact ⟨LinearPMap.adjoint_isClosed hD, by
      rw [range_adjoint_eq_orthogonal_ker_of_isNormallySolvable T hD h]
      exact T.ker.isClosed_orthogonal⟩
  · intro h
    have hr := range_adjoint_eq_orthogonal_ker_of_isNormallySolvable T.adjoint
      (dense_adjoint_domain_of_isClosable T hD hT.isClosable) h
    rw [adjoint_adjoint_eq_of_isClosed T hD hT] at hr
    exact ⟨hT, hr.symm ▸ T.adjoint.ker.isClosed_orthogonal⟩

private theorem gram_range_le_adjoint_range (T : E →ₗ.[𝕜] F) [CompleteSpace E] :
    (partialComp T.adjoint T).toFun.range ≤ T.adjoint.toFun.range := by
  rintro _ ⟨u, rfl⟩
  obtain ⟨hu, hTu⟩ := (partialComp_mem_domain T.adjoint T u.val).mp u.prop
  exact ⟨⟨T ⟨u.val, hu⟩, hTu⟩, (partialComp_apply T.adjoint T u.val hu hTu).symm⟩

private theorem gram_ker_eq_ker [CompleteSpace E] (T : E →ₗ.[𝕜] F)
    (hD : Dense (T.domain : Set E)) : (partialComp T.adjoint T).ker = T.ker := by
  ext x
  rw [LinearPMap.mem_ker_iff, LinearPMap.mem_ker_iff]
  constructor
  · rintro ⟨u, rfl, hu⟩
    obtain ⟨hx, hTx⟩ := (partialComp_mem_domain T.adjoint T u.val).mp u.prop
    let v : T.domain := ⟨u.val, hx⟩
    have he : T.adjoint ⟨T v, hTx⟩ = 0 :=
      (partialComp_apply T.adjoint T u.val hx hTx).symm.trans hu
    have h := LinearPMap.adjoint_isFormalAdjoint hD ⟨T v, hTx⟩ v
    rw [he, inner_zero_left] at h
    exact ⟨v, rfl, inner_self_eq_zero.mp h.symm⟩
  · rintro ⟨v, rfl, hv⟩
    have hTx : T v ∈ T.adjoint.domain := hv.symm ▸ T.adjoint.domain.zero_mem
    refine ⟨⟨v.val, (partialComp_mem_domain T.adjoint T v.val).mpr ⟨v.prop, hTx⟩⟩, rfl, ?_⟩
    rw [partialComp_apply T.adjoint T v.val v.prop hTx]
    have he : (⟨T v, hTx⟩ : T.adjoint.domain) = 0 := Subtype.ext hv
    rw [he, LinearPMap.map_zero]

private theorem gram_range_eq_adjoint_range_of_isNormallySolvable
    [CompleteSpace E] [CompleteSpace F] (T : E →ₗ.[𝕜] F)
    (hD : Dense (T.domain : Set E)) (hT : IsNormallySolvable T) :
    (partialComp T.adjoint T).toFun.range = T.adjoint.toFun.range := by
  let R := T.toFun.range
  let : CompleteSpace R := hT.2.completeSpace_coe
  refine le_antisymm (gram_range_le_adjoint_range T) ?_
  rintro _ ⟨y, rfl⟩
  let w := R.starProjection (y : F)
  have hw : w ∈ R := R.starProjection_apply_mem _
  have hz : y.val - w ∈ T.adjoint.ker := by
    rw [ker_adjoint_eq_orthogonal_range T hD]
    exact R.sub_starProjection_mem_orthogonal y.val
  let z : T.adjoint.domain := ⟨y.val - w, T.adjoint.ker_le_domain hz⟩
  let v := y - z
  have hv : (v : F) = w := by
    change y.val - (y.val - w) = w
    abel
  have hz₀ : T.adjoint z = 0 := LinearPMap.coe_mem_ker_iff.mp hz
  have hTv : T.adjoint v = T.adjoint y := by
    rw [show v = y - z from rfl, T.adjoint.map_sub, hz₀, sub_zero]
  obtain ⟨u, hu⟩ := hw
  change T u = w at hu
  have huD : T u ∈ T.adjoint.domain := (hv.trans hu.symm) ▸ v.prop
  have huV : (⟨T u, huD⟩ : T.adjoint.domain) = v := Subtype.ext (hu.trans hv.symm)
  refine ⟨⟨u.val, (partialComp_mem_domain T.adjoint T u.val).mpr ⟨u.prop, huD⟩⟩, ?_⟩
  change partialComp T.adjoint T _ = T.adjoint y
  rw [partialComp_apply T.adjoint T u.val u.prop huD, huV, hTv]

private theorem isNormallySolvable_iff_gram [CompleteSpace E] [CompleteSpace F]
    (T : E →ₗ.[𝕜] F) (hD : Dense (T.domain : Set E)) (hT : T.IsClosed) :
    IsNormallySolvable T ↔ IsNormallySolvable (partialComp T.adjoint T) := by
  let A := partialComp T.adjoint T
  have hg := gramOperators_nonnegative T hT hD
  have hA : IsSelfAdjoint A := hg.1.1
  have hAD : Dense (A.domain : Set E) := hg.2.1.dense_domain
  constructor
  · intro h
    refine ⟨hA.isClosed, ?_⟩
    change IsClosed (A.toFun.range : Set E)
    rw [gram_range_eq_adjoint_range_of_isNormallySolvable T hD h]
    exact ((exercise_9_9_adjoint T hD hT).mp h).2
  · intro h
    have he := (isNormallySolvable_iff_orthogonal_ker_adjoint A hA.isClosed hAD).mp h
    rw [LinearPMap.isSelfAdjoint_def.mp hA] at he
    have hRg : A.toFun.range = T.kerᗮ :=
      he.trans (congrArg Submodule.orthogonal (gram_ker_eq_ker T hD))
    have hRt : T.adjoint.toFun.range = T.kerᗮ := by
      apply le_antisymm
      · rw [← orthogonal_range_adjoint_eq_ker T hD hT]
        exact Submodule.le_orthogonal_orthogonal _
      · rw [← hRg]
        exact gram_range_le_adjoint_range T
    apply (exercise_9_9_adjoint T hD hT).mpr
    exact ⟨LinearPMap.adjoint_isClosed hD, hRt.symm ▸ T.ker.isClosed_orthogonal⟩

/-- **Exercise 9** of [benIsrael2003generalized], Chapter 9.
The two partial Gram operators are normally solvable exactly when the
original densely defined closed operator is normally solvable. -/
theorem exercise_9_9_gram [CompleteSpace E] [CompleteSpace F]
    (T : E →ₗ.[𝕜] F) (hD : Dense (T.domain : Set E)) (hT : T.IsClosed) :
    (IsNormallySolvable T ↔ IsNormallySolvable (partialComp T.adjoint T)) ∧
      (IsNormallySolvable T ↔ IsNormallySolvable (partialComp T T.adjoint)) := by
  refine ⟨isNormallySolvable_iff_gram T hD hT, (exercise_9_9_adjoint T hD hT).trans ?_⟩
  have h := isNormallySolvable_iff_gram T.adjoint
    (dense_adjoint_domain_of_isClosable T hD hT.isClosable) (LinearPMap.adjoint_isClosed hD)
  rw [adjoint_adjoint_eq_of_isClosed T hD hT] at h
  exact h

end NormalSolvability

section Exercises

/-- **Exercise 1** of [benIsrael2003generalized], Chapter 9.
Adding the horizontal domain to the graph produces the product of the
domain and range. When the operator is bounded with closed domain and
nonclosed range, this is a nonclosed sum of two closed subspaces. -/
theorem exercise_9_1 [CompleteSpace F] (T : E →ₗ.[𝕜] F)
    (hT : IsBoundedOperator T) (hD : IsClosed (T.domain : Set E))
    (hR : ¬IsClosed (T.toFun.range : Set F)) :
    let L := T.domain.prod (⊥ : Submodule 𝕜 F)
    IsClosed (T.graph : Set (E × F)) ∧ IsClosed (L : Set (E × F)) ∧
      T.graph ⊔ L = T.domain.prod T.toFun.range ∧
      ¬IsClosed ((T.graph ⊔ L : Submodule 𝕜 (E × F)) : Set (E × F)) := by
  intro L
  have hprod : T.graph ⊔ L = T.domain.prod T.toFun.range := by
    apply le_antisymm
    · apply sup_le
      · intro p hp
        obtain ⟨x, hx, hy⟩ := T.mem_graph_iff.mp hp
        exact ⟨hx ▸ x.prop, ⟨x, hy⟩⟩
      · intro p hp
        exact ⟨hp.1, (bot_le : (⊥ : Submodule 𝕜 F) ≤ T.toFun.range) hp.2⟩
    · intro p hp
      obtain ⟨x, hx⟩ := hp.2
      refine Submodule.mem_sup.mpr ⟨(x.val, T x), T.mem_graph x, (p.1 - x.val, 0), ?_, ?_⟩
      · exact ⟨T.domain.sub_mem hp.1 x.prop, Submodule.zero_mem _⟩
      · change T x = p.2 at hx
        exact Prod.ext (by change x.val + (p.1 - x.val) = p.1; abel) (by simpa using hx)
  refine ⟨(isClosed_iff_isClosed_domain_of_bounded T hT).mpr hD, ?_, hprod, ?_⟩
  · exact hD.prod isClosed_singleton
  · intro h
    rw [hprod] at h
    apply hR
    have hc : Continuous fun y : F => ((0 : E), y) := continuous_const.prodMk continuous_id
    convert h.preimage hc using 1
    ext y
    exact ⟨fun hy => ⟨T.domain.zero_mem, hy⟩, fun hy => hy.2⟩

omit [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] in
/-- **Exercise 2** of [benIsrael2003generalized], Chapter 9.
An everywhere-defined unbounded functional has dense kernel and trivial
carrier. The conclusion applies to the abstract functional on a Hilbert space. -/
theorem exercise_9_2 [CompleteSpace E] (f : E →ₗ[𝕜] 𝕜) (hf : ¬Continuous f) :
    Dense (f.ker : Set E) ∧ (f.toPMap ⊤).kerᗮ = ⊥ ∧ carrier (f.toPMap ⊤) = ⊥ := by
  have hn0 : ∃ u : E, f u ≠ 0 := by
    by_contra! h
    apply hf
    have he : f = 0 := LinearMap.ext h
    rw [he]
    exact continuous_zero
  obtain ⟨u₀, hu₀⟩ := hn0
  let u := (f u₀)⁻¹ • u₀
  have hu : f u = 1 := by
    dsimp only [u]
    rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hu₀]
  have hdiff (x : E) : x - f x • u ∈ f.ker := by
    rw [LinearMap.mem_ker, map_sub, map_smul, hu, smul_eq_mul, mul_one, sub_self]
  have hclosed : ¬IsClosed (f.ker : Set E) := by
    intro h
    apply hf
    apply f.continuous_of_isClosed_graph
    have he : (f.graph : Set (E × 𝕜)) =
        (fun p : E × 𝕜 => p.1 - p.2 • u) ⁻¹' (f.ker : Set E) := by
      ext p
      rw [SetLike.mem_coe, LinearMap.mem_graph_iff, Set.mem_preimage,
        SetLike.mem_coe, LinearMap.mem_ker, map_sub, map_smul, hu, smul_eq_mul, mul_one,
        sub_eq_zero, eq_comm]
    rw [he]
    exact h.preimage (continuous_fst.sub (continuous_snd.smul continuous_const))
  have hd : Dense (f.ker : Set E) := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top]
    have hle : f.ker < f.ker.topologicalClosure :=
      lt_of_le_of_ne f.ker.le_topologicalClosure fun he =>
        hclosed (he.symm ▸ f.ker.isClosed_topologicalClosure)
    obtain ⟨x, hx, hx₀⟩ := IsConcreteLE.exists_of_lt hle
    have hx₁ : f x ≠ 0 := hx₀
    have hfxu : f x • u ∈ f.ker.topologicalClosure := by
      have he := f.ker.topologicalClosure.sub_mem hx (f.ker.le_topologicalClosure (hdiff x))
      convert he using 1
      abel
    have hu' : u ∈ f.ker.topologicalClosure := by
      simpa only [smul_smul, inv_mul_cancel₀ hx₁, one_smul] using
        f.ker.topologicalClosure.smul_mem (f x)⁻¹ hfxu
    apply top_unique
    intro y _
    have he := f.ker.topologicalClosure.add_mem (f.ker.le_topologicalClosure (hdiff y))
      (f.ker.topologicalClosure.smul_mem (f y) hu')
    simpa only [sub_add_cancel] using he
  have ho : (f.toPMap ⊤).kerᗮ = ⊥ := by
    rw [LinearMap.toPMap_ker, top_inf_eq]
    exact (dense_iff_orthogonal_eq_bot f.ker).mp hd
  exact ⟨hd, ho, by rw [carrier, ho, inf_bot_eq]⟩

omit [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] in
/-- **Exercise 3** of [benIsrael2003generalized], Chapter 9.
The intersection of a dense subspace with a closed finite-codimensional
subspace is dense in the latter. -/
theorem exercise_9_3 [CompleteSpace E] (D L : Submodule 𝕜 E)
    (hD : Dense (D : Set E)) (hL : IsClosed (L : Set E))
    [FiniteDimensional 𝕜 Lᗮ] : (D ⊓ L).topologicalClosure = L := by
  let P := Lᗮ.orthogonalProjectionOnto
  let Q := P.comp D.subtypeL
  have hP : Function.Surjective P := fun y =>
    ⟨y.val, Lᗮ.orthogonalProjectionOnto_mem_subspace_eq_self y⟩
  have hQr : (Q.range : Set Lᗮ) = P '' (D : Set E) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.val, x.prop, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have hQ : Q.range = ⊤ := by
    have hQrDense : Dense (Q.range : Set Lᗮ) := by
      rw [hQr]
      exact hP.denseRange.dense_image P.continuous hD
    have hcl : IsClosed (Q.range : Set Lᗮ) := Q.range.closed_of_finiteDimensional
    exact hcl.submodule_topologicalClosure_eq ▸
      Submodule.dense_iff_topologicalClosure_eq_top.mp hQrDense
  obtain ⟨J, hJ⟩ := Q.exists_rightInverse_of_surjective hQ
  let g (x : E) := x - (J (P x) : E)
  have hg : Continuous g := continuous_id.sub (continuous_subtype_val.comp
    (J.continuous.comp P.continuous))
  have hker : P.ker = L := by
    rw [Submodule.ker_orthogonalProjectionOnto, Submodule.orthogonal_orthogonal_eq_closure,
      hL.submodule_topologicalClosure_eq]
  have hm : Set.MapsTo g (D : Set E) ((D ⊓ L : Submodule 𝕜 E) : Set E) := by
    intro x hx
    refine ⟨D.sub_mem hx (J (P x)).prop, ?_⟩
    rw [← hker]
    change P (x - (J (P x) : E)) = 0
    have he : P (J (P x) : E) = P x := congrFun (congrArg DFunLike.coe hJ) (P x)
    rw [map_sub, he, sub_self]
  refine le_antisymm (Submodule.topologicalClosure_minimal _ inf_le_right hL) fun x hx => ?_
  have hx' : x ∈ closure (D : Set E) := by rw [hD.closure_eq]; exact Set.mem_univ _
  have he := hm.closure hg hx'
  have hp0 : P x = 0 := show x ∈ P.ker from hker.symm ▸ hx
  change x ∈ closure ((D ⊓ L : Submodule 𝕜 E) : Set E)
  simpa [g, hp0] using he

omit [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] in
/-- **Exercise 4** of [benIsrael2003generalized], Chapter 9.
For a proper dense domain, the rank-one example has the indicated kernel,
fixes its range pointwise, and has a closed everywhere-defined extension. -/
theorem exercise_9_4_rankOne [CompleteSpace E] (D : Submodule 𝕜 E) (hD : Dense (D : Set E))
    (v : E) (hv : v ∉ D) :
    ∃ T : E →ₗ.[𝕜] E, T.domain = D ∧ IsBoundedOperator T ∧ T.IsClosable ∧
      T.toFun.range ≠ ⊥ ∧ carrier T = ⊥ ∧ T.ker = D ⊓ (𝕜 ∙ v)ᗮ ∧
      ∀ x : T.domain, (T x, T x) ∈ T.graph := by
  let f := innerSL 𝕜 v
  have hex : ∃ a ∈ D, f a ≠ 0 := by
    by_contra! h
    exact hv ((hD.eq_zero_of_inner_left 𝕜 h) ▸ D.zero_mem)
  obtain ⟨a, ha, hfa⟩ := hex
  let u := (f a)⁻¹ • a
  have hu : u ∈ D := D.smul_mem _ ha
  have hfu : f u = 1 := by
    dsimp only [u]
    rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hfa]
  have hu0 : u ≠ 0 := fun h => by simp [h] at hfu
  let B := f.smulRight u
  let T := B.toLinearMap.toPMap D
  have hTa (x : T.domain) : T x = f x • u := rfl
  have hB : IsBoundedOperator T :=
    ⟨‖B‖, fun x => B.le_opNorm (x : E)⟩
  have hclos : T.IsClosable := by
    apply LinearPMap.isClosable_iff_exists_closed_extension.mpr
    refine ⟨B.toLinearMap.toPMap ⊤, B.isClosed_toPMap (by simp), le_top, ?_⟩
    intro x y he
    change B x = B y
    exact congrArg B he
  refine ⟨T, rfl, hB, hclos, ?_, ?_⟩
  · intro he
    have hr : u ∈ T.toFun.range := by
      refine ⟨⟨u, hu⟩, ?_⟩
      change T (⟨u, hu⟩ : T.domain) = u
      rw [hTa, hfu, one_smul]
    have hz : u ∈ (⊥ : Submodule 𝕜 E) := he ▸ hr
    exact hu0 (by simpa using hz)
  · let L := 𝕜 ∙ v
    let K := Lᗮ
    have hK (x : E) : x ∈ K ↔ f x = 0 :=
      Submodule.mem_orthogonal_singleton_iff_inner_right
    have hk : T.ker = D ⊓ K := by
      ext x
      change x ∈ T.ker ↔ x ∈ D ∧ x ∈ K
      rw [LinearPMap.mem_ker_iff, hK]
      constructor
      · rintro ⟨y, rfl, hy⟩
        rw [hTa] at hy
        exact ⟨y.prop, (smul_eq_zero.mp hy).resolve_right hu0⟩
      · rintro ⟨hx, hx0⟩
        exact ⟨⟨x, hx⟩, rfl, by rw [hTa, hx0, zero_smul]⟩
    have hKcl : (D ⊓ K).topologicalClosure = K := by
      refine le_antisymm (Submodule.topologicalClosure_minimal _ inf_le_right
        L.isClosed_orthogonal) ?_
      let g (x : E) := x - f x • u
      have hg : Continuous g := continuous_id.sub (f.continuous.smul continuous_const)
      have hm : Set.MapsTo g (D : Set E) ((D ⊓ K : Submodule 𝕜 E) : Set E) := by
        intro x hx
        refine ⟨D.sub_mem hx (D.smul_mem _ hu), (hK _).mpr ?_⟩
        dsimp only [g]
        rw [map_sub, map_smul, hfu, smul_eq_mul, mul_one, sub_self]
      intro x hx
      have hx' : x ∈ closure (D : Set E) := by rw [hD.closure_eq]; exact Set.mem_univ _
      have he := hm.closure hg hx'
      change x ∈ closure ((D ⊓ K : Submodule 𝕜 E) : Set E)
      simpa only [g, (hK _).mp hx, zero_smul, sub_zero] using he
    have hL : IsClosed (L : Set E) := L.closed_of_finiteDimensional
    have hker : T.kerᗮ = L := by
      rw [← T.ker.orthogonal_closure, hk, hKcl]
      change Lᗮᗮ = L
      rw [Submodule.orthogonal_orthogonal_eq_closure, hL.submodule_topologicalClosure_eq]
    refine ⟨?_, hk, ?_⟩
    · rw [carrier, hker, Submodule.eq_bot_iff]
      rintro x ⟨hx, hxL⟩
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hxL
      by_cases hc : c = 0
      · rw [hc, zero_smul]
      · exfalso
        apply hv
        simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using D.smul_mem c⁻¹ hx
    · intro x
      let y : T.domain := ⟨f x • u, D.smul_mem _ hu⟩
      refine T.mem_graph_iff.mpr ⟨y, (hTa x).symm, ?_⟩
      rw [hTa y, hTa x]
      change f (f x • u) • u = f x • u
      rw [map_smul, hfu, smul_eq_mul, mul_one]

omit [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] in
/-- **Exercise 4** of [benIsrael2003generalized], Chapter 9.
Every proper dense subspace is the domain of a nonzero bounded partial
operator with trivial carrier and a closed everywhere-defined extension. -/
theorem exercise_9_4 [CompleteSpace E] (D : Submodule 𝕜 E) (hD : Dense (D : Set E))
    (v : E) (hv : v ∉ D) :
    ∃ T : E →ₗ.[𝕜] E, T.domain = D ∧ IsBoundedOperator T ∧ T.IsClosable ∧
      T.toFun.range ≠ ⊥ ∧ carrier T = ⊥ := by
  obtain ⟨T, hdom, hB, hclos, hR, hC, _, _⟩ := exercise_9_4_rankOne D hD v hv
  exact ⟨T, hdom, hB, hclos, hR, hC⟩

omit [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] in
/-- **Exercise 6** of [benIsrael2003generalized], Chapter 9.
The orthogonal summands are the intersections of their sum with the
orthogonal complements of the other summands. -/
theorem exercise_9_6 (L M N : Submodule 𝕜 E)
    (h : L = M ⊔ N) (ho : M ≤ Nᗮ) :
    M = L ⊓ Nᗮ ∧ N = L ⊓ Mᗮ := by
  have hs {A B : Submodule 𝕜 E} (hL : L = A ⊔ B) (hAB : A ≤ Bᗮ) : A = L ⊓ Bᗮ := by
    rw [hL]
    refine le_antisymm (le_inf le_sup_left hAB) ?_
    rintro x ⟨hx, hxB⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
    have hb' : b ∈ Bᗮ := by
      simpa only [add_sub_cancel_left] using Bᗮ.sub_mem hxB (hAB ha)
    have hb₀ : b = 0 := by
      have he : b ∈ B ⊓ Bᗮ := ⟨hb, hb'⟩
      rwa [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] at he
    simpa only [hb₀, add_zero] using ha
  have ho' : N ≤ Mᗮ := fun x hx => (Submodule.mem_orthogonal _ _).mpr fun y hy =>
    inner_eq_zero_symm.mp ((Submodule.mem_orthogonal _ _).mp (ho hy) x hx)
  exact ⟨hs h ho, hs (h.trans (sup_comm _ _)) ho'⟩

omit [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] in
/-- **Exercise 7** of [benIsrael2003generalized], Chapter 9.
Multiplying the $n$th coordinate of a square-summable sequence by $k^n$,
for $0<k<1$, gives a bounded injective operator with dense nonclosed range. -/
theorem exercise_9_7 (k : ℝ) (hk₀ : 0 < k) (hk₁ : k < 1) :
    ∃ T : lp (fun _ : ℕ => ℝ) 2 →L[ℝ] lp (fun _ : ℕ => ℝ) 2,
      (∀ x n, T x n = k ^ n * x n) ∧ Function.Injective T ∧
      Dense (Set.range T) ∧ ¬IsClosed (Set.range T) := by
  let H := lp (fun _ : ℕ => ℝ) 2
  have hk (i : ℕ) : ‖k ^ i‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hk₀.le _)]
    exact pow_le_one₀ hk₀.le hk₁.le
  let T : H →L[ℝ] H := lp.diagonalL (fun _ : ℕ => ℝ) 2 (fun i => k ^ i) hk
  have hT (x : H) (i : ℕ) : T x i = k ^ i * x i := rfl
  have hinj : Function.Injective T := by
    intro x y h
    ext i
    have he := congrArg (fun z : H => z i) h
    rw [hT, hT] at he
    exact mul_left_cancel₀ (pow_ne_zero _ hk₀.ne') he
  have hsingle (i : ℕ) (a : ℝ) : T (lp.single 2 i a) = k ^ i • lp.single 2 i a :=
    lp.diagonalL_single (E := fun _ : ℕ => ℝ) (p := 2) (fun i => k ^ i) hk i a
  refine ⟨T, hT, hinj, ?_, ?_⟩
  · intro x
    apply mem_closure_of_tendsto (lp.hasSum_single (by norm_num) x)
    filter_upwards with s
    refine ⟨∑ i ∈ s, lp.single 2 i (x i / k ^ i), ?_⟩
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hsingle, ← lp.single_smul, smul_eq_mul, mul_div_cancel₀ _ (pow_ne_zero _ hk₀.ne')]
  · intro hclosed
    obtain ⟨C, hC⟩ := T.antilipschitz_of_injective_of_isClosed_range hinj hclosed
    have he (n : ℕ) : 1 ≤ (C : ℝ) * k ^ n := by
      have h := hC.le_mul_norm T.map_zero (lp.single 2 n (1 : ℝ))
      rwa [hsingle, norm_smul, lp.norm_single (by norm_num), norm_one, mul_one,
        Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hk₀.le _)] at h
    have hlim : Tendsto (fun n : ℕ => (C : ℝ) * k ^ n) atTop (𝓝 ((C : ℝ) * 0)) :=
      tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_lt_one hk₀.le hk₁)
    have hz : (1 : ℝ) ≤ 0 :=
      ge_of_tendsto (by simpa only [mul_zero] using hlim) (Eventually.of_forall he)
    exact (not_le_of_gt zero_lt_one) hz

/-- **Exercise 8(a)** of [benIsrael2003generalized], Chapter 9.
An identity minus a compact operator has closed range. This gives the
closed-range result for integral operators of the second kind. -/
theorem exercise_9_8a (T : E →L[𝕜] E) (hT : IsCompactOperator T) :
    IsClosed (((1 : E →L[𝕜] E) - T).range : Set E) := by
  simpa only [one_smul] using hT.isClosed_range_smul_sub (μ := 1) one_ne_zero

/-- **Exercise 8(b)** of [benIsrael2003generalized], Chapter 9.
A compact operator between Hilbert spaces has closed range exactly when
its range is finite dimensional. -/
theorem exercise_9_8b [CompleteSpace E] [CompleteSpace F]
    (T : E →L[𝕜] F) (hT : IsCompactOperator T) :
    IsClosed (T.range : Set F) ↔ FiniteDimensional 𝕜 T.range := by
  constructor
  · intro hR
    let K := T.ker
    have hK : IsClosed (K : Set E) := T.isClosed_ker
    let : CompleteSpace K := hK.completeSpace_coe
    let A := T.comp Kᗮ.subtypeL
    have hAR : A.range = T.range := by
      apply le_antisymm
      · rintro _ ⟨x, rfl⟩
        exact ⟨x.val, rfl⟩
      · rintro _ ⟨x, rfl⟩
        refine ⟨⟨x - K.starProjection x, K.sub_starProjection_mem_orthogonal x⟩, ?_⟩
        change T (x - K.starProjection x) = T x
        have hz : T (K.starProjection x) = 0 := K.starProjection_apply_mem x
        rw [map_sub, hz, sub_zero]
    have hAr : IsClosed (A.range : Set F) := hAR.symm ▸ hR
    have hAi : Function.Injective A := by
      apply (LinearMap.ker_eq_bot.mp ?_ : Function.Injective A.toLinearMap)
      rw [Submodule.eq_bot_iff]
      intro x hx
      have hKx : x.val ∈ K := hx
      have he : x.val ∈ K ⊓ Kᗮ := ⟨hKx, x.prop⟩
      rw [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] at he
      exact Subtype.ext he
    let e := A.equivRange hAi hAr
    have hAc : IsCompactOperator A := hT.comp_clm Kᗮ.subtypeL
    have hEc : IsCompactOperator (e : Kᗮ →L[𝕜] A.range) :=
      hAc.codRestrict (V := A.range) (fun x => ⟨x, rfl⟩) hAr
    have hIc : IsCompactOperator (id : A.range → A.range) := by
      have h := hEc.comp_clm e.symm.toContinuousLinearMap
      have he : (e : Kᗮ →L[𝕜] A.range).comp e.symm.toContinuousLinearMap =
          ContinuousLinearMap.id 𝕜 A.range := ContinuousLinearMap.ext e.apply_symm_apply
      change IsCompactOperator ((e : Kᗮ →L[𝕜] A.range).comp e.symm.toContinuousLinearMap) at h
      rwa [he] at h
    exact hAR ▸ isCompactOperator_id_iff_finiteDimensional.mp hIc
  · intro h
    exact T.range.closed_of_finiteDimensional

end Exercises

end BenIsraelGreville.Chapter09
