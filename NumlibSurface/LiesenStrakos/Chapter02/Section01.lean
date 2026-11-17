/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Projection.WellDefined

/-!
# §2.1. Projection processes

A search space $S$ supplies a correction to $x_0$ and a constraint space $C$ determines the
orthogonality of the residual. This section gives the projected matrix criterion for the
process in [liesen2013krylov] and the condition for exact termination.

## Main definitions

* `LiesenStrakos.IsProjectionIterate` specifies the affine search and residual constraints.
* `LiesenStrakos.ProjectionWellDefined` expresses the direct sum $AS \oplus C^\perp$.
* `LiesenStrakos.projectedMatrix` is the projected matrix $C^*AS$ in the two bases.
* `LiesenStrakos.projectedIterate` gives the iterate obtained by solving the projected system.
* `LiesenStrakos.IsOrthogonalProjectionProcess` and
  `LiesenStrakos.IsObliqueProjectionProcess` distinguish $AS=C$ from $AS\ne C$.

## Main results

* `LiesenStrakos.theorem_2_1_2` characterizes invertibility of the projected matrix.
* `LiesenStrakos.isProjectionIterate_projectedIterate` verifies the coordinate formula.
* `LiesenStrakos.theorem_2_1_6` gives the three sufficient conditions for well-definedness.
* `LiesenStrakos.lemma_2_1_7` gives exactness on an invariant search space.
-/

namespace LiesenStrakos

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The projection condition (2.1.1)–(2.1.4) of [liesen2013krylov] is $x_n \in x_0+S$
and $b-Ax_n \perp C$. -/
abbrev IsProjectionIterate (A : E →ₗ[𝕜] E) (b x₀ : E) (S C : Submodule 𝕜 E) (x : E) : Prop :=
  IsPetrovGalerkin A b x₀ S C x

/-- The well-definedness condition (2.1.6) is the direct sum $E = AS \oplus C^\perp$. -/
abbrev ProjectionWellDefined (A : E →ₗ[𝕜] E) (S C : Submodule 𝕜 E) : Prop :=
  IsCompl (S.map A) Cᗮ

/-- The projected matrix of (2.1.9) has entry $c_i^*As_j$ in row $i$ and column $j$. -/
noncomputable abbrev projectedMatrix {ι : Type*} {S C : Submodule 𝕜 E}
    (A : E →ₗ[𝕜] E) (s : Module.Basis ι 𝕜 S) (c : Module.Basis ι 𝕜 C) : Matrix ι ι 𝕜 :=
  LinearMap.crossGram 𝕜 (fun j => A (s j)) (fun i => (c i : E))

/-- **Theorem 2.1.2** of [liesen2013krylov].
If the search and constraint spaces have bases indexed by the same finite set, the projected
matrix is invertible if and only if $AS$ and $C^\perp$ are complementary. -/
theorem theorem_2_1_2 [FiniteDimensional 𝕜 E] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S C : Submodule 𝕜 E} (A : E →ₗ[𝕜] E) (s : Module.Basis ι 𝕜 S) (c : Module.Basis ι 𝕜 C) :
    IsUnit (projectedMatrix A s c) ↔ ProjectionWellDefined A S C :=
  isUnit_crossGram_map_iff_isCompl A s c

/-- The projected iterate in (2.1.10) is $x_0+S(C^*AS)^{-1}C^*(b-Ax_0)$,
where the columns of $S$ and $C$ are bases of the search and constraint spaces. -/
noncomputable def projectedIterate {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S C : Submodule 𝕜 E} (A : E →ₗ[𝕜] E) (s : Module.Basis ι 𝕜 S) (c : Module.Basis ι 𝕜 C)
    (b x₀ : E) : E :=
  let t := (projectedMatrix A s c)⁻¹.mulVec (fun i => inner 𝕜 (c i : E) (b - A x₀))
  x₀ + ∑ j, t j • (s j : E)

/-- If $C^*AS$ is invertible, the coordinate formula (2.1.10) gives an iterate with
correction in the search space and residual orthogonal to the constraint space. -/
theorem isProjectionIterate_projectedIterate {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S C : Submodule 𝕜 E} (A : E →ₗ[𝕜] E) (s : Module.Basis ι 𝕜 S) (c : Module.Basis ι 𝕜 C)
    (b x₀ : E) (h : IsUnit (projectedMatrix A s c)) :
    IsProjectionIterate A b x₀ S C (projectedIterate A s c b x₀) := by
  unfold projectedIterate
  apply (isPetrovGalerkin_iff_mulVec s c _).2
  exact Matrix.mulVec_nonsing_inv_mulVec h _

/-- **Definition 2.1.3** of [liesen2013krylov], orthogonal case.
A well-defined projection process is orthogonal when $AS = C$. -/
def IsOrthogonalProjectionProcess (A : E →ₗ[𝕜] E) (S C : Submodule 𝕜 E) : Prop :=
  ProjectionWellDefined A S C ∧ S.map A = C

/-- **Definition 2.1.3** of [liesen2013krylov], oblique case.
A well-defined projection process is oblique when $AS \ne C$. -/
def IsObliqueProjectionProcess (A : E →ₗ[𝕜] E) (S C : Submodule 𝕜 E) : Prop :=
  ProjectionWellDefined A S C ∧ S.map A ≠ C

/-- **Theorem 2.1.6** of [liesen2013krylov].
The process is well defined for positive definite Hermitian $A$ and $C=S$, for Hermitian
invertible $A$ and $C=A^{-1}S$, and for invertible $A$ and $C=AS$. -/
theorem theorem_2_1_6 [FiniteDimensional 𝕜 E] (A : E →ₗ[𝕜] E) (S : Submodule 𝕜 E) :
    (A.IsSymmetricCoercive → ProjectionWellDefined A S S) ∧
      (A.IsSymmetric → Function.Bijective A → ProjectionWellDefined A S (S.comap A)) ∧
      (Function.Bijective A → ProjectionWellDefined A S (S.map A)) :=
  ⟨fun h => isCompl_map_orthogonal_of_isCoercive h.isCoercive S,
    fun h h' => isCompl_map_orthogonal_comap_of_isSymmetric h h' S,
    fun _ => (S.map A).isCompl_orthogonal⟩

/-- **Lemma 2.1.7** of [liesen2013krylov].
At a well-defined projection step with $b-Ax_0 \in S$ and $AS=S$, the residual $b-Ax_n$ is zero. -/
theorem lemma_2_1_7 {A : E →ₗ[𝕜] E} {S C : Submodule 𝕜 E} {b x₀ x : E}
    (h : ProjectionWellDefined A S C) (hx : IsProjectionIterate A b x₀ S C x)
    (hr : b - A x₀ ∈ S) (hS : S.map A = S) : b - A x = 0 := by
  have hK : S ∈ Module.End.invtSubmodule A := by
    exact (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem A).2
      fun _ hz => hS ▸ Submodule.mem_map_of_mem hz
  have hC := h.disjoint
  rw [hS] at hC
  exact sub_eq_zero.2 (hx.eq_of_invt hK hr fun z hz hz' => by
    have hm : z ∈ S ⊓ Cᗮ := ⟨hz, hz'⟩
    rwa [hC.eq_bot, Submodule.mem_bot] at hm).symm

end LiesenStrakos
