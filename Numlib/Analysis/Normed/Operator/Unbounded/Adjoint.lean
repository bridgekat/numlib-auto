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
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Extend
import Mathlib.Topology.Algebra.Module.LinearPMap
import Numlib.Analysis.Normed.Module.WeakClosed

/-!
# The Banach-space adjoint of a bounded and of an unbounded operator

Let $E$ and $F$ be normed spaces over a nontrivially normed field $\mathbb{K}$, with strong duals
$E^*$ and $F^*$, and write $\langle f, u \rangle = f(u)$. The **adjoint** (transpose) of a bounded
operator $T \colon E \to F$ is the bounded operator $T^* \colon F^* \to E^*$, $T^* v = v \circ T$.
It satisfies $\langle T^* v, u \rangle = \langle v, Tu \rangle$ and, over $\mathbb{K} = \mathbb{R}$
or $\mathbb{C}$, $\|T^*\| = \|T\|$. For an unbounded operator $A \colon D(A) \subseteq E \to F$ with
dense domain, the adjoint is the unbounded operator $A^* \colon D(A^*) \subseteq F^* \to E^*$. Its
domain consists of the $v \in F^*$ for which $u \mapsto \langle v, Au \rangle$ is bounded on $D(A)$,
and $A^* v$ is the extension by continuity of that functional to $E$. The fundamental relation is
$\langle A^* v, u \rangle = \langle v, Au \rangle$ for $u \in D(A)$ and $v \in D(A^*)$. The
presentation follows [brezis2011functional], §2.6 (the definition, Remarks 2.14–2.17, Proposition
2.17, relation (27), Corollary 2.18 and Exercise 2.18) and §2.7 (Remark 2.20).

For a subspace $M \subseteq E$ the annihilator is $M^\perp = \{f \in E^* : f = 0 \text{ on } M\}$,
and for a subspace $N \subseteq E^*$ it is $N^\perp = \{u \in E : f(u) = 0 \text{ for all } f \in
N\}$. The main results relate kernels, ranges and graphs: $N(A^*) = R(A)^\perp$,
$N(A) = R(A^*)^\perp$ for closed $A$, $\overline{R(A^*)} \subseteq N(A)^\perp$,
$N(A^*)^\perp = \overline{R(A)}$, and $A^*$ is closed. When $A$ is closed, $D(A^*)$ is weak-$*$
dense in $F^*$, and $N(A)^\perp$ is the weak-$*$ closure of $R(A^*)$.

## Main definitions

* `ContinuousLinearMap.strongDualMap`: the adjoint $T^* v = v \circ T$ of a bounded operator.
* `ContinuousLinearMap.strongDualMapₗᵢ`: over $\mathbb{R}$ or $\mathbb{C}$, the map $T \mapsto T^*$
  as a linear isometry.
* `LinearPMap.strongDualAdjoint`: the adjoint $A^* \colon D(A^*) \subseteq F^* \to E^*$ of an
  unbounded operator.

## Main results

* `LinearPMap.mem_strongDualAdjoint_domain_iff`: $v \in D(A^*)$ if and only if $|v(Au)| \le c \|u\|$
  on $D(A)$ for some constant $c$.
* `LinearPMap.strongDualAdjoint_apply`: the fundamental relation $(A^* v)(u) = v(Au)$.
* `LinearPMap.strongDualAdjoint_apply_eq` and `LinearPMap.mem_strongDualAdjoint_domain_of_exists`:
  $A^* v$ is the unique $f \in E^*$ with $f(u) = v(Au)$ on $D(A)$, and any such $f$ puts $v$ in
  $D(A^*)$.
* `LinearPMap.strongDualAdjoint_isClosed`: the adjoint is closed.
* `ContinuousLinearMap.toPMap_strongDualAdjoint`: for a bounded operator restricted to a dense
  subspace, the two adjoints agree.
* `LinearPMap.map_graph_strongDualAdjoint_eq_annihilator_graph`: $I[G(A^*)] = G(A)^\perp$ with
  $I(v, f) = (-f, v)$.
* `LinearPMap.IsClosed.exists_apply_ne_strongDualAdjoint_apply_of_notMem_graph`: if $A$ is closed
  and $(u, y) \notin G(A)$, some $v \in D(A^*)$ has $v(y) \ne (A^* v)(u)$.
* `LinearPMap.ker_strongDualAdjoint_eq_annihilator_range`: $N(A^*) = R(A)^\perp$.
* `LinearPMap.IsClosed.ker_eq_strongDualCoannihilator_range_strongDualAdjoint`:
  $N(A) = R(A^*)^\perp$ for closed $A$.
* `LinearPMap.closure_range_strongDualAdjoint_le_annihilator_ker`:
  $\overline{R(A^*)} \subseteq N(A)^\perp$.
* `LinearPMap.strongDualCoannihilator_ker_strongDualAdjoint_eq_closure_range`:
  $N(A^*)^\perp = \overline{R(A)}$.
* `ContinuousLinearMap.ker_strongDualMap_eq_annihilator_range` and
  `ContinuousLinearMap.ker_eq_strongDualCoannihilator_range_strongDualMap`: $N(T^*) = R(T)^\perp$
  and $N(T) = R(T^*)^\perp$ for a bounded operator.
* `LinearPMap.ker_strongDualAdjoint_eq_bot_of_range_eq_top` and
  `LinearPMap.IsClosed.ker_eq_bot_of_range_strongDualAdjoint_eq_top`: if $A$ is onto then $A^*$ is
  injective, and if $A^*$ is onto then the closed operator $A$ is injective.
* `LinearPMap.IsClosed.dense_toWeakDual_domain_strongDualAdjoint`: $D(A^*)$ is weak-$*$ dense in
  $F^*$.
* `LinearPMap.IsClosed.annihilator_ker_eq_closure_toWeakDual_range_strongDualAdjoint`: $N(A)^\perp$
  is the weak-$*$ closure of $R(A^*)$.

## Implementation notes

* Mathlib has the algebraic `LinearMap.dualMap` on `Module.Dual`, the precomposition map
  `ContinuousLinearMap.precomp` for topological vector spaces, and the Hilbert-space adjoints
  `ContinuousLinearMap.adjoint` and `LinearPMap.adjoint`, which go through the Riesz representation.
  It has no norm statement about the Banach transpose and no Banach-space adjoint of an unbounded
  operator.
* `ContinuousLinearMap.strongDualMap T` is `ContinuousLinearMap.precomp 𝕜 T` with scalar-valued
  targets, by `rfl` (`ContinuousLinearMap.strongDualMap_eq_precomp`), so that Mathlib's lemmas about
  `precomp` apply. The name `dualMap` is left free for a future Mathlib addition.
* `LinearPMap.strongDualAdjoint` is built like Mathlib's `LinearPMap.adjoint`. The domain is the
  subspace `{v | Continuous ((v : F →ₗ[𝕜] 𝕜).comp A.toFun)}`, and the value at $v$ is
  `ContinuousLinearMap.extend` of $u \mapsto v(Au)$ along the inclusion of $D(A)$. The map
  $v \mapsto A^* v$ is linear because the extension is unique when $D(A)$ is dense. When $D(A)$ is
  not dense, all values are $0$. Only the completeness of $\mathbb{K}$ is used, and no Hahn–Banach
  theorem (Remark 2.14 of [brezis2011functional]).
* The annihilators are `Submodule.strongDualAnnihilator` ($M^\perp \subseteq E^*$) and
  `Submodule.strongDualCoannihilator` ($N^\perp \subseteq E$) of
  `Numlib.Analysis.Normed.Module.Annihilator`; lemma names abbreviate the first to `annihilator`.
  The range of $A$ is `LinearMap.range A.toFun` and its kernel is `A.ker`.
* The theorems about $A^*$ between reflexive spaces ($D(A^*)$ dense, $A^{**} = A$) are in
  `Numlib.Analysis.Normed.Operator.Unbounded.Reflexive`, and the closed range theorem is in
  `Numlib.Analysis.Normed.Operator.Unbounded.ClosedRange`.
-/

open Filter Topology

noncomputable section

namespace ContinuousLinearMap

section NontriviallyNormedField

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- The **adjoint of a bounded operator**. Let $T \colon E \to F$ be a bounded linear operator
between normed spaces over $\mathbb{K}$. Its adjoint is the bounded operator
$T^* \colon F^* \to E^*$ defined by
$$T^* v = v \circ T.$$
This is the adjoint of Remark 2.16 of [brezis2011functional].

The dual $F^*$ is `StrongDual 𝕜 F`. The definition is Mathlib's precomposition map
`ContinuousLinearMap.precomp 𝕜 T` with scalar-valued functionals as targets. -/
def strongDualMap (T : E →L[𝕜] F) : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E :=
  precomp 𝕜 T

/-- The **fundamental relation** for a bounded operator. Let $T \colon E \to F$ be bounded,
$v \in F^*$ and $u \in E$. Then $(T^* v)(u) = v(Tu)$, that is, $\langle T^* v, u \rangle =
\langle v, Tu \rangle$. -/
@[simp]
theorem strongDualMap_apply (T : E →L[𝕜] F) (v : StrongDual 𝕜 F) (u : E) :
    T.strongDualMap v u = v (T u) :=
  rfl

/-- For a bounded operator $T$ and $v \in F^*$, $T^* v$ is the composite functional $v \circ T$. -/
theorem strongDualMap_apply' (T : E →L[𝕜] F) (v : StrongDual 𝕜 F) :
    T.strongDualMap v = v.comp T :=
  rfl

/-- The adjoint $T^*$ of a bounded operator is Mathlib's `ContinuousLinearMap.precomp 𝕜 T` with
scalar-valued targets. -/
theorem strongDualMap_eq_precomp (T : E →L[𝕜] F) : T.strongDualMap = precomp 𝕜 T :=
  rfl

/-- The adjoint $T^*$ of a bounded operator is the flip of the composition map
`ContinuousLinearMap.compL 𝕜 E F 𝕜`, evaluated at $T$. -/
theorem strongDualMap_eq_compL_flip (T : E →L[𝕜] F) :
    T.strongDualMap = (compL 𝕜 E F 𝕜).flip T := by
  ext; rfl

/-- The adjoint of the identity of $E$ is the identity of $E^*$. -/
@[simp]
theorem strongDualMap_id :
    (ContinuousLinearMap.id 𝕜 E).strongDualMap = ContinuousLinearMap.id 𝕜 (StrongDual 𝕜 E) := by
  ext; rfl

/-- Let $T \colon E \to F$ and $S \colon F \to G$ be bounded operators. Then
$(S \circ T)^* = T^* \circ S^*$. This is Exercise 2.25 of [brezis2011functional]. -/
theorem strongDualMap_comp (S : F →L[𝕜] G) (T : E →L[𝕜] F) :
    (S.comp T).strongDualMap = T.strongDualMap.comp S.strongDualMap := by
  ext; rfl

/-- For bounded operators $S, T \colon E \to F$, $(S + T)^* = S^* + T^*$. -/
@[simp]
theorem strongDualMap_add (S T : E →L[𝕜] F) :
    (S + T).strongDualMap = S.strongDualMap + T.strongDualMap := by
  ext; simp

/-- For $c \in \mathbb{K}$ and a bounded operator $T$, $(cT)^* = c T^*$. -/
@[simp]
theorem strongDualMap_smul (c : 𝕜) (T : E →L[𝕜] F) :
    (c • T).strongDualMap = c • T.strongDualMap := by
  ext; simp

/-- The adjoint of the zero operator is zero. -/
@[simp]
theorem strongDualMap_zero : (0 : E →L[𝕜] F).strongDualMap = 0 := by
  ext; simp

/-- For bounded operators $S, T \colon E \to F$, $(S - T)^* = S^* - T^*$. -/
@[simp]
theorem strongDualMap_sub (S T : E →L[𝕜] F) :
    (S - T).strongDualMap = S.strongDualMap - T.strongDualMap := by
  ext; simp

/-- Let $T \colon E \to F$ be bounded and $v \in F^*$. As a linear map, $T^* v$ is Mathlib's
algebraic dual map `LinearMap.dualMap` of $T$ applied to $v$. -/
theorem toLinearMap_strongDualMap_apply (T : E →L[𝕜] F) (v : StrongDual 𝕜 F) :
    ((T.strongDualMap v : StrongDual 𝕜 E) : E →ₗ[𝕜] 𝕜) =
      (T : E →ₗ[𝕜] F).dualMap (v : F →ₗ[𝕜] 𝕜) :=
  rfl

/-- Let $T \colon E \to F$ be a bounded operator between normed spaces over a nontrivially normed
field. Then
$$\|T^*\| \le \|T\|.$$
This is the first inequality of Remark 2.16 of [brezis2011functional]. -/
theorem opNorm_strongDualMap_le (T : E →L[𝕜] F) : ‖T.strongDualMap‖ ≤ ‖T‖ := by
  refine opNorm_le_bound _ (norm_nonneg _) fun v => ?_
  rw [strongDualMap_apply', mul_comm]
  exact opNorm_comp_le v T

/-- Let $T \colon E \to F$ be bounded. Then $N(T^*) = R(T)^\perp$: for $v \in F^*$, $T^* v = 0$ if
and only if $v$ vanishes on the range of $T$. This is Corollary 2.18(ii) of
[brezis2011functional] for a bounded operator. -/
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

/-- Let $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, and let $T \colon E \to F$ be bounded. Then
$$\|T^*\| = \|T\|.$$
This is Remark 2.16 of [brezis2011functional].

The inequality $\|T\| \le \|T^*\|$ uses Corollary 1.4 of [brezis2011functional]: a functional
$v$ with $\|v\| \le 1$ and $v(Tu) = \|Tu\|$ gives $\|Tu\| = |(T^* v)(u)| \le \|T^*\| \|u\|$. -/
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
/-- Let $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$. The map $T \mapsto T^*$ is a linear isometry from
the bounded operators $E \to F$ to the bounded operators $F^* \to E^*$.

Unlike the Hilbert-space adjoint, this map is not onto in general: its image consists of the
weak-$*$ continuous operators. -/
def strongDualMapₗᵢ : (E →L[𝕜] F) →ₗᵢ[𝕜] (StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E) where
  toFun := strongDualMap
  map_add' := strongDualMap_add
  map_smul' := strongDualMap_smul
  norm_map' := opNorm_strongDualMap

/-- The linear isometry `ContinuousLinearMap.strongDualMapₗᵢ` sends $T$ to $T^*$. -/
@[simp]
theorem strongDualMapₗᵢ_apply (T : E →L[𝕜] F) : strongDualMapₗᵢ 𝕜 E F T = T.strongDualMap :=
  rfl

/-- Let $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, and let $T \colon E \to F$ be bounded. Then
$N(T) = R(T^*)^\perp$: $Tu = 0$ if and only if $(T^* v)(u) = 0$ for every $v \in F^*$. This is
Corollary 2.18(i) of [brezis2011functional] for a bounded operator.

The proof uses that $(T^* v)(u) = v(Tu)$ and that the functionals separate the points of $F$. -/
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

/-- The **domain of the adjoint**. For a linear operator $A \colon D(A) \subseteq E \to F$, this is
the subspace of those $v \in F^*$ for which $u \mapsto v(Au)$ is continuous on $D(A)$, that is,
$|v(Au)| \le c \|u\|$ on $D(A)$ for some constant $c$. -/
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
/-- A functional $v \in F^*$ lies in `LinearPMap.strongDualAdjointDomain` if and only if
$u \mapsto v(Au)$ is continuous on $D(A)$. -/
theorem mem_strongDualAdjointDomain_iff (v : StrongDual 𝕜 F) :
    v ∈ A.strongDualAdjointDomain ↔ Continuous ((v : F →ₗ[𝕜] 𝕜).comp A.toFun) :=
  Iff.rfl

omit [CompleteSpace 𝕜] in
/-- A functional $v \in F^*$ lies in `LinearPMap.strongDualAdjointDomain` if and only if there is
$c \in \mathbb{R}$ with $|v(Au)| \le c \|u\|$ for every $u \in D(A)$. This is the form of the
definition in [brezis2011functional]. -/
theorem mem_strongDualAdjointDomain_iff_exists (v : StrongDual 𝕜 F) :
    v ∈ A.strongDualAdjointDomain ↔ ∃ c : ℝ, ∀ u : A.domain, ‖v (A u)‖ ≤ c * ‖u‖ := by
  rw [mem_strongDualAdjointDomain_iff]
  constructor
  · intro h
    obtain ⟨c, _, hc⟩ := (⟨(v : F →ₗ[𝕜] 𝕜).comp A.toFun, h⟩ : A.domain →L[𝕜] 𝕜).bound
    exact ⟨c, fun u => hc u⟩
  · rintro ⟨c, hc⟩
    exact (LinearMap.mkContinuousOfExistsBound _ ⟨c, hc⟩).continuous

/-- For $v$ in the domain of the adjoint, the bounded functional $u \mapsto v(Au)$ on $D(A)$, with
the norm of $E$. -/
def strongDualAdjointDomainMkCLM (v : A.strongDualAdjointDomain) : StrongDual 𝕜 A.domain :=
  ⟨((v : StrongDual 𝕜 F) : F →ₗ[𝕜] 𝕜).comp A.toFun, v.prop⟩

omit [CompleteSpace 𝕜] in
/-- For $v$ in the domain of the adjoint and $u \in D(A)$, `LinearPMap.strongDualAdjointDomainMkCLM`
takes the value $v(Au)$ at $u$. -/
theorem strongDualAdjointDomainMkCLM_apply (v : A.strongDualAdjointDomain) (u : A.domain) :
    A.strongDualAdjointDomainMkCLM v u = (v : StrongDual 𝕜 F) (A u) :=
  rfl

/-- For $v$ in the domain of the adjoint, the extension by continuity of $u \mapsto v(Au)$ from
$D(A)$ to an element of $E^*$. As Remark 2.14 of [brezis2011functional] observes, no Hahn–Banach
theorem is needed. -/
def strongDualAdjointDomainMkCLMExtend (v : A.strongDualAdjointDomain) : StrongDual 𝕜 E :=
  (A.strongDualAdjointDomainMkCLM v).extend (Submodule.subtypeL A.domain)

variable {A}

/-- If $D(A)$ is dense in $E$, then for $v$ in the domain of the adjoint and $u \in D(A)$, the
extension `LinearPMap.strongDualAdjointDomainMkCLMExtend` takes the value $v(Au)$ at $u$. -/
@[simp]
theorem strongDualAdjointDomainMkCLMExtend_apply (hA : Dense (A.domain : Set E))
    (v : A.strongDualAdjointDomain) (u : A.domain) :
    A.strongDualAdjointDomainMkCLMExtend v (u : E) = (v : StrongDual 𝕜 F) (A u) :=
  ContinuousLinearMap.extend_eq _ hA.denseRange_val
    isUniformEmbedding_subtype_val.isUniformInducing _

variable (hA : Dense (A.domain : Set E))

/-- If $D(A)$ is dense in $E$, the map that sends $v$ in the domain of the adjoint to the extension
of $u \mapsto v(Au)$ is linear. Linearity uses the density of $D(A)$, through the uniqueness of
the extension. -/
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

/-- If $D(A)$ is dense, then for $v$ in the domain of the adjoint and $u \in D(A)$, the functional
that `LinearPMap.strongDualAdjointAux` assigns to $v$ takes the value $v(Au)$ at $u$. -/
theorem strongDualAdjointAux_apply (v : A.strongDualAdjointDomain) (u : A.domain) :
    strongDualAdjointAux hA v u = (v : StrongDual 𝕜 F) (A u) := by
  simp [strongDualAdjointAux, hA]

/-- If $D(A)$ is dense, $v$ lies in the domain of the adjoint, and $f \in E^*$ satisfies
$f(u) = v(Au)$ for every $u \in D(A)$, then `LinearPMap.strongDualAdjointAux` sends $v$ to $f$. -/
theorem strongDualAdjointAux_unique (v : A.strongDualAdjointDomain) {f : StrongDual 𝕜 E}
    (hf : ∀ u : A.domain, f u = (v : StrongDual 𝕜 F) (A u)) : strongDualAdjointAux hA v = f := by
  refine ContinuousLinearMap.ext_on (R₁ := 𝕜) (s := (A.domain : Set E)) (by simpa) ?_
  rintro u hu
  rw [strongDualAdjointAux_apply hA v ⟨u, hu⟩, hf ⟨u, hu⟩]

variable (A)

open scoped Classical in
/-- The **adjoint of an unbounded operator**. Let $\mathbb{K}$ be a complete nontrivially normed
field, let $E$ and $F$ be normed spaces over $\mathbb{K}$, and let
$A \colon D(A) \subseteq E \to F$ be a linear operator. The adjoint
$A^* \colon D(A^*) \subseteq F^* \to E^*$ has the domain
$$D(A^*) = \{v \in F^* : \exists c,\ |v(Au)| \le c \|u\| \text{ for all } u \in D(A)\}.$$
If $D(A)$ is dense in $E$, then $A^* v$ is the extension by continuity of $u \mapsto v(Au)$ to
$E$, which is the unique $f \in E^*$ with $f(u) = v(Au)$ on $D(A)$. If $D(A)$ is not dense, then
$A^* v = 0$ for every $v \in D(A^*)$. This is the adjoint of §2.6 of [brezis2011functional].

The value $0$ off the dense case follows the pattern of Mathlib's Hilbert-space
`LinearPMap.adjoint`. The domain is `LinearPMap.strongDualAdjointDomain`, and the value is
`LinearPMap.strongDualAdjointAux`. -/
def strongDualAdjoint : StrongDual 𝕜 F →ₗ.[𝕜] StrongDual 𝕜 E where
  domain := A.strongDualAdjointDomain
  toFun := if hA : Dense (A.domain : Set E) then strongDualAdjointAux hA else 0

/-- The **domain of the adjoint**. A functional $v \in F^*$ lies in $D(A^*)$ if and only if there is
$c \in \mathbb{R}$ with
$$|v(Au)| \le c \|u\| \quad \text{for every } u \in D(A).$$
This is the definition (24) in §2.6 of [brezis2011functional]. -/
theorem mem_strongDualAdjoint_domain_iff (v : StrongDual 𝕜 F) :
    v ∈ A.strongDualAdjoint.domain ↔ ∃ c : ℝ, ∀ u : A.domain, ‖v (A u)‖ ≤ c * ‖u‖ :=
  A.mem_strongDualAdjointDomain_iff_exists v

/-- A functional $v \in F^*$ lies in $D(A^*)$ if and only if $u \mapsto v(Au)$ is continuous on
$D(A)$. -/
theorem mem_strongDualAdjoint_domain_iff_continuous (v : StrongDual 𝕜 F) :
    v ∈ A.strongDualAdjoint.domain ↔ Continuous ((v : F →ₗ[𝕜] 𝕜).comp A.toFun) :=
  Iff.rfl

variable {A}

/-- If $D(A)$ is dense, then $A^* v$ is `LinearPMap.strongDualAdjointAux` at $v$, for every
$v \in D(A^*)$. -/
theorem strongDualAdjoint_apply_of_dense (v : A.strongDualAdjoint.domain) :
    A.strongDualAdjoint v = strongDualAdjointAux hA v := by
  classical
  change (if hA : Dense (A.domain : Set E) then strongDualAdjointAux hA else 0) v = _
  simp only [hA, dite_true]

/-- If $D(A)$ is not dense in $E$, then $A^* v = 0$ for every $v \in D(A^*)$. -/
theorem strongDualAdjoint_apply_of_not_dense (hA : ¬ Dense (A.domain : Set E))
    (v : A.strongDualAdjoint.domain) : A.strongDualAdjoint v = 0 := by
  classical
  change (if hA : Dense (A.domain : Set E) then strongDualAdjointAux hA else 0) v = _
  simp only [hA, dite_false]
  rfl

include hA in
/-- The **fundamental relation** for the adjoint. Let $D(A)$ be dense in $E$. Then for
$v \in D(A^*)$ and $u \in D(A)$,
$$(A^* v)(u) = v(Au), \quad \text{that is,} \quad \langle A^* v, u \rangle = \langle v, Au
  \rangle.$$
This is relation (25) in §2.6 of [brezis2011functional]. -/
theorem strongDualAdjoint_apply (v : A.strongDualAdjoint.domain) (u : A.domain) :
    A.strongDualAdjoint v u = (v : StrongDual 𝕜 F) (A u) := by
  rw [strongDualAdjoint_apply_of_dense hA]
  exact strongDualAdjointAux_apply hA v u

include hA in
/-- **Uniqueness of the extension**. Let $D(A)$ be dense in $E$, let $v \in D(A^*)$, and let
$f \in E^*$ satisfy $f(u) = v(Au)$ for every $u \in D(A)$. Then $A^* v = f$. -/
theorem strongDualAdjoint_apply_eq (v : A.strongDualAdjoint.domain) {f : StrongDual 𝕜 E}
    (hf : ∀ u : A.domain, f u = (v : StrongDual 𝕜 F) (A u)) : A.strongDualAdjoint v = f := by
  rw [strongDualAdjoint_apply_of_dense hA]
  exact strongDualAdjointAux_unique hA v hf

/-- Let $v \in F^*$. If some $f \in E^*$ satisfies $f(u) = v(Au)$ for every $u \in D(A)$, then
$v \in D(A^*)$.

No density of $D(A)$ is needed. -/
theorem mem_strongDualAdjoint_domain_of_exists (v : StrongDual 𝕜 F)
    (h : ∃ f : StrongDual 𝕜 E, ∀ u : A.domain, f u = v (A u)) :
    v ∈ A.strongDualAdjoint.domain := by
  obtain ⟨f, hf⟩ := h
  refine (A.mem_strongDualAdjoint_domain_iff v).2 ⟨‖f‖, fun u => ?_⟩
  rw [← hf u]
  exact f.le_opNorm u

include hA in
/-- The **graph of the adjoint**. Let $D(A)$ be dense in $E$. For $v \in F^*$ and $f \in E^*$,
$(v, f) \in G(A^*)$ if and only if $f(u) = v(Au)$ for every $u \in D(A)$. This is the
computation after Proposition 2.17 of [brezis2011functional], before any identification of
$(E \times F)^*$. -/
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
/-- The **adjoint is closed**. Let $D(A)$ be dense in $E$. Then
$A^* \colon D(A^*) \subseteq F^* \to E^*$ is a closed operator. This is Proposition 2.17 of
[brezis2011functional].

The graph of $A^*$ is the intersection over $u \in D(A)$ of the closed sets
$\{(v, f) : f(u) = v(Au)\}$. Without the density of $D(A)$ the graph is $D(A^*) \times \{0\}$,
which need not be closed. -/
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

/-- The **adjoint of a bounded operator restricted to a dense subspace is its bounded adjoint**. Let
$\mathbb{K}$ be complete, let $T \colon E \to F$ be bounded, and let $p$ be a dense subspace of
$E$. Then the adjoint of the restriction of $T$ to $p$ has domain $F^*$ and equals $T^*$, that
is, it sends $v$ to $v \circ T$. This is Remark 2.16 of [brezis2011functional].

With $p = E$ this says that the two adjoints agree on bounded operators. -/
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

/-- Let $D(A)$ be dense in $E$. Then
$$N(A^*) = R(A)^\perp:$$
an element $v \in F^*$ lies in $D(A^*)$ with $A^* v = 0$ if and only if $v$ vanishes on $R(A)$.
This is Corollary 2.18(ii) and Exercise 2.18 of [brezis2011functional].

Closedness of $A$ is not needed. -/
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

/-- Let $D(A)$ be dense in $E$. Then the norm closure of $R(A^*)$ is contained in $N(A)^\perp$. This
is Corollary 2.18(iii) of [brezis2011functional].

The relation $(A^* v)(u) = v(Au) = 0$ holds for $u \in N(A)$, and the annihilator is closed.
Equality can fail (Remark 2.17 and Exercise 2.23 of [brezis2011functional]). The weak-$*$
closure gives equality for closed $A$, by
`LinearPMap.IsClosed.annihilator_ker_eq_closure_toWeakDual_range_strongDualAdjoint`. -/
theorem closure_range_strongDualAdjoint_le_annihilator_ker (hA : Dense (A.domain : Set E)) :
    (LinearMap.range A.strongDualAdjoint.toFun).topologicalClosure ≤
      A.ker.strongDualAnnihilator := by
  refine Submodule.topologicalClosure_minimal _ ?_ (Submodule.isClosed_strongDualAnnihilator _)
  rintro f ⟨v, rfl⟩
  refine Submodule.mem_strongDualAnnihilator.2 fun u hu => ?_
  obtain ⟨w, rfl, hw⟩ := mem_ker_iff.1 hu
  rw [toFun_eq_coe, strongDualAdjoint_apply hA v w, hw, _root_.map_zero]

/-- Let $D(A)$ be dense in $E$. If $A$ is onto, that is, $R(A) = F$, then $A^*$ is injective:
$N(A^*) = \{0\}$. This is Remark 2.20 of [brezis2011functional].

The proof is $N(A^*) = R(A)^\perp = F^\perp = \{0\}$. -/
theorem ker_strongDualAdjoint_eq_bot_of_range_eq_top (hA : Dense (A.domain : Set E))
    (h : LinearMap.range A.toFun = ⊤) : A.strongDualAdjoint.ker = ⊥ := by
  rw [ker_strongDualAdjoint_eq_annihilator_range hA, h, Submodule.strongDualAnnihilator_top]

end Definition

section RCLike

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {A : E →ₗ.[𝕜] F}

/-- Let $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, and let $D(A)$ be dense in $E$. Then
$$N(A^*)^\perp = \overline{R(A)}.$$
This is Corollary 2.18(iv) of [brezis2011functional].

The proof combines $N(A^*) = R(A)^\perp$ with the bipolar identity
$(M^\perp)^\perp = \overline{M}$. This is the shape of the closed range theorem and of the
Fredholm alternative: when $R(A)$ is closed, $Au = f$ is solvable if and only if $v(f) = 0$ for
every $v \in N(A^*)$. -/
theorem strongDualCoannihilator_ker_strongDualAdjoint_eq_closure_range
    (hA : Dense (A.domain : Set E)) :
    A.strongDualAdjoint.ker.strongDualCoannihilator =
      (LinearMap.range A.toFun).topologicalClosure := by
  rw [ker_strongDualAdjoint_eq_annihilator_range hA,
    Submodule.strongDualCoannihilator_strongDualAnnihilator]

/-- The **graph relation**. Let $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, and let $D(A)$ be dense
in $E$. Let $I \colon F^* \times E^* \to E^* \times F^*$ be $I(v, f) = (-f, v)$, and identify
$E^* \times F^*$ with $(E \times F)^*$ by sending $(g, v)$ to $(x, y) \mapsto g(x) + v(y)$. Then
$$I[G(A^*)] = G(A)^\perp.$$
This is relation (27) in §2.6 of [brezis2011functional].

The map $I$ is `LinearEquiv.skewSwap`, and the identification is
`ContinuousLinearMap.coprodEquivL`. The functional $(x, y) \mapsto -f(x) + v(y)$ vanishes on
$G(A)$ if and only if $f(u) = v(Au)$ on $D(A)$. -/
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

/-- **Separation from the closed graph, through the adjoint**. Let $\mathbb{K} = \mathbb{R}$ or
$\mathbb{C}$, let $A \colon D(A) \subseteq E \to F$ be closed with $D(A)$ dense in $E$, and let
$(u, y) \in E \times F$ with $(u, y) \notin G(A)$. Then some $v \in D(A^*)$ has
$$v(y) \ne (A^* v)(u).$$

A functional $\Phi \in (E \times F)^*$ that vanishes on the graph with $\Phi(u, y) \ne 0$
(`Submodule.exists_dual_eq_zero_of_notMem`) has components $f = \Phi \circ \mathrm{inl}$ and
$v = \Phi \circ \mathrm{inr}$ with $f(x) + v(Ax) = 0$ on $D(A)$. So $v \in D(A^*)$ with
$A^* v = -f$, and $v(y) - (A^* v)(u) = \Phi(u, y)$. Every consequence of the closedness of $A$
for its adjoint reduces to this: Corollary 2.18(i), the weak-$*$ density of $D(A^*)$, and
Theorem 3.24 of [brezis2011functional]. -/
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

/-- Let $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, and let $A \colon D(A) \subseteq E \to F$ be
closed with $D(A)$ dense in $E$. Then
$$N(A) = R(A^*)^\perp:$$
an element $u \in E$ lies in $D(A)$ with $Au = 0$ if and only if $(A^* v)(u) = 0$ for every
$v \in D(A^*)$. This is Corollary 2.18(i) and Exercise 2.18 of [brezis2011functional].

The inclusion $\subseteq$ is the fundamental relation. For $\supseteq$, an element
$u \in R(A^*)^\perp$ outside $N(A)$ has $(u, 0) \notin G(A)$, and separation from the closed
graph produces $v \in D(A^*)$ with $(A^* v)(u) \ne v(0) = 0$. -/
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

/-- Let $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, and let $A$ be closed with $D(A)$ dense in $E$.
If $A^*$ is onto, that is, $R(A^*) = E^*$, then $A$ is injective: $N(A) = \{0\}$. This is Remark
2.20 of [brezis2011functional].

The proof is $N(A) = R(A^*)^\perp = (E^*)^\perp = \{0\}$. -/
theorem IsClosed.ker_eq_bot_of_range_strongDualAdjoint_eq_top (hc : A.IsClosed)
    (hA : Dense (A.domain : Set E)) (h : LinearMap.range A.strongDualAdjoint.toFun = ⊤) :
    A.ker = ⊥ := by
  rw [hc.ker_eq_strongDualCoannihilator_range_strongDualAdjoint hA, h,
    Submodule.strongDualCoannihilator_top]

/-- The **domain of the adjoint separates the points of $F$**. Let $\mathbb{K} = \mathbb{R}$ or
$\mathbb{C}$, and let $A$ be closed with $D(A)$ dense in $E$. For every $y \in F$ with
$y \ne 0$, some $v \in D(A^*)$ has $v(y) \ne 0$.

Indeed $(0, y) \notin G(A)$, and separation from the closed graph gives $v \in D(A^*)$ with
$v(y) \ne (A^* v)(0) = 0$. This is the common core of the weak-$*$ density of $D(A^*)$ (Remark
2.15 of [brezis2011functional]) and of its norm density for reflexive $F$ (Theorem 3.24). -/
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

/-- Let $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, and let $A$ be closed with $D(A)$ dense in $E$.
Then $D(A^*)$ is dense in $F^*$ for the weak-$*$ topology. This is Remark 2.15 and Problem 9 of
[brezis2011functional].

The statement is that the image of $D(A^*)$ under `StrongDual.toWeakDual` is dense. If the
weak-$*$ closure of $D(A^*)$ missed some $w$, then
`Submodule.exists_weakDual_eval_eq_zero_of_notMem` would give $y \in F$ with $v(y) = 0$ for
every $v \in D(A^*)$ and $w(y) \ne 0$; but $D(A^*)$ separates the points of $F$
(`LinearPMap.IsClosed.exists_mem_domain_strongDualAdjoint_apply_ne_zero`). Density in norm fails
in general (Exercise 2.22) and holds for reflexive $F$ (Theorem 3.24,
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

/-- Let $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, and let $A$ be closed with $D(A)$ dense in $E$.
Then $N(A)^\perp$ is the closure of $R(A^*)$ in the weak-$*$ topology of $E^*$. This is Remark
2.17 and Problem 9 of [brezis2011functional].

Both sides are stated as subsets of the weak dual, through `StrongDual.toWeakDual`. The proof
combines $N(A) = R(A^*)^\perp$ with the weak-$*$ bipolar theorem for subspaces,
`Submodule.strongDualAnnihilator_strongDualCoannihilator_eq_closure_toWeakDual`. In norm, the
inclusion $\overline{R(A^*)} \subseteq N(A)^\perp$ can be strict; equality holds when $E$ is
reflexive (`Submodule.strongDualAnnihilator_strongDualCoannihilator`). -/
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
