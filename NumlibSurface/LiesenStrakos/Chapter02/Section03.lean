/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.LiesenStrakos.Chapter01.Section03
import NumlibSurface.LiesenStrakos.Chapter02.Section02
import Numlib.Krylov.Iterate
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# §2.3. Characterization of CG, SYMMLQ, and minimal-residual methods

The choices of trial and constraint spaces give distinct approximation properties.
The CG iterate minimizes the energy error, the SYMMLQ iterate minimizes the Euclidean
error, and the minimal-residual iterate minimizes the Euclidean residual.

## Main results

* `LiesenStrakos.theorem_2_3_1_cg` characterizes the CG projection.
* `LiesenStrakos.theorem_2_3_1_symmlq` characterizes the SYMMLQ projection.
* `LiesenStrakos.theorem_2_3_1_minres` characterizes the minimal-residual projection.
* `LiesenStrakos.theorem_2_3_2` gives the weighted best-approximation criterion.

## Deviations from the source

* **Theorem 2.3.2** (generalization). The weighted best approximation property holds in general
  inner product spaces.
* **Theorem 2.3.1** (generalization). The CG, SYMMLQ and minimal-residual characterizations
  include step zero, zero initial residual, and steps after the grade. See
  `LiesenStrakos.theorem_2_3_1_cg`,
  `LiesenStrakos.theorem_2_3_1_symmlq`,
  `LiesenStrakos.theorem_2_3_1_minres`.
-/

namespace LiesenStrakos

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- **Theorem 2.3.1(1)** of [liesen2013krylov].
For Hermitian positive definite $A$, the Galerkin iterate exists uniquely, is characterized
equivalently by energy-orthogonality or energy-error minimization, and is exact at and after the
grade.

**Generalization.** The source assumes positive grade $d$ and considers steps $1$ through $d$.
The characterization here also covers zero initial residual and all natural step indices.
After step $d$, the Krylov space has stabilized and the iterate remains exact. -/
theorem theorem_2_3_1_cg (A : E →ₗ[𝕜] E) (hA : A.IsSymmetricCoercive)
    (b x₀ xstar : E) (hstar : A xstar = b) (n : ℕ) :
    let K := krylovSubspace A (b - A x₀) n
    ProjectionWellDefined A K K ∧
    (∃! x, IsProjectionIterate A b x₀ K K x) ∧
    (∀ x, IsProjectionIterate A b x₀ K K x ↔
      x - x₀ ∈ K ∧ ∀ w ∈ K, EnergyOrthogonal A (xstar - x) w) ∧
    (∀ x, IsProjectionIterate A b x₀ K K x ↔
      x - x₀ ∈ K ∧ ∀ y, y - x₀ ∈ K →
        energyNorm A (xstar - x) ≤ energyNorm A (xstar - y)) ∧
    (grade A (b - A x₀) ≤ n → ∀ x, IsProjectionIterate A b x₀ K K x → A x = b) := by
  dsimp only
  refine ⟨(theorem_2_1_6 A _).1 hA,
    Krylov.existsUnique_isGalerkinIterate_of_isCoercive hA.isCoercive b x₀ n,
    ?_, fun _ => IsGalerkin.iff_energyNorm_min hA hstar, ?_⟩
  · intro x
    have hres : A (xstar - x) = b - A x := by rw [map_sub, hstar]
    constructor
    · exact fun h => ⟨h.mem, fun w hw => by simpa only [EnergyOrthogonal,
        energyInnerProduct, hres] using h.inner_residual_eq_zero hw⟩
    · rintro ⟨hmem, hort⟩
      refine ⟨hmem, ?_⟩
      intro w hw
      simpa only [EnergyOrthogonal, energyInnerProduct, hres] using hort w hw
  · exact fun hn _ hx => Krylov.IsGalerkinIterate.apply_eq_of_grade_le hx hn

omit [FiniteDimensional 𝕜 E] in
private theorem symmlq_projection_iff (A : E →ₗ[𝕜] E) (hA : A.IsSymmetric)
    (b x₀ xstar : E) (hstar : A xstar = b) (K : Submodule 𝕜 E) (x : E) :
    IsProjectionIterate A b x₀ (K.map A) K x ↔
      x - x₀ ∈ K.map A ∧ xstar - x ∈ (K.map A)ᗮ := by
  have horth : b - A x ∈ Kᗮ ↔ xstar - x ∈ (K.map A)ᗮ := by
    rw [Submodule.mem_orthogonal, Submodule.mem_orthogonal]
    constructor
    · intro h _ hy
      obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 hy
      simpa only [hA z, map_sub, hstar] using h z hz
    · intro h z hz
      have hz' := h (A z) (Submodule.mem_map_of_mem hz)
      rwa [hA z, map_sub, hstar] at hz'
  exact ⟨fun hx => ⟨hx.mem, horth.1 hx.orth⟩, fun hx => ⟨hx.1, horth.2 hx.2⟩⟩

/-- **Theorem 2.3.1(2)** of [liesen2013krylov].
For Hermitian nonsingular $A$, the projection with trial space $AK$ and constraint space $K$
exists uniquely, is characterized equivalently by error orthogonality or Euclidean-error
minimization on $x_0+AK$, and is exact at and after the grade.

**Generalization.** The source assumes positive grade and considers steps up to termination.
The characterization also covers step zero, zero initial residual, and steps after the grade. -/
theorem theorem_2_3_1_symmlq (A : E →ₗ[𝕜] E) (hA : A.IsSymmetric)
    (hAi : Function.Bijective A) (b x₀ xstar : E) (hstar : A xstar = b) (n : ℕ) :
    let K := krylovSubspace A (b - A x₀) n
    ProjectionWellDefined A (K.map A) K ∧
    (∃! x, IsProjectionIterate A b x₀ (K.map A) K x) ∧
    (∀ x, IsProjectionIterate A b x₀ (K.map A) K x ↔
      x - x₀ ∈ K.map A ∧ xstar - x ∈ (K.map A)ᗮ) ∧
    (∀ x, IsProjectionIterate A b x₀ (K.map A) K x ↔ IsMinError xstar x₀ (K.map A) x) ∧
    (grade A (b - A x₀) ≤ n → ∀ x, IsProjectionIterate A b x₀ (K.map A) K x → A x = b) := by
  let K := krylovSubspace A (b - A x₀) n
  change ProjectionWellDefined A (K.map A) K ∧ _
  have hcomap : (K.map A).comap A = K := by
    ext z
    constructor
    · rintro ⟨y, hy, hyz⟩
      exact hAi.injective hyz ▸ hy
    · exact Submodule.mem_map_of_mem
  have hwell : ProjectionWellDefined A (K.map A) K := by
    simpa only [hcomap] using (theorem_2_1_6 A (K.map A)).2.1 hA hAi
  refine ⟨hwell, existsUnique_isPetrovGalerkin_of_isCompl hwell hAi.injective.injOn _ _,
    symmlq_projection_iff A hA b x₀ xstar hstar K, ?_, ?_⟩
  · intro x
    rw [symmlq_projection_iff A hA b x₀ xstar hstar K x]
    refine ⟨fun ⟨hx, hort⟩ => ⟨hx, fun y hy => ?_⟩,
      fun h => ⟨h.mem, h.sub_mem_orthogonal⟩⟩
    have hnorm := Submodule.norm_sub_le_of_forall_inner_eq_zero hx
      (fun w hw => by
        rw [show xstar - x₀ - (x - x₀) = xstar - x by abel]
        exact (Submodule.mem_orthogonal' _ _).1 hort w hw) hy
    simpa only [show xstar - x₀ - (x - x₀) = xstar - x by abel,
      show xstar - x₀ - (y - x₀) = xstar - y by abel] using hnorm
  · intro hn x hx
    let r := b - A x₀
    have hinv : K.map A = K := by
      apply Submodule.eq_of_le_of_finrank_le
      · change (Krylov.subspace A r n).map A ≤ Krylov.subspace A r n
        rw [Krylov.subspace_eq_of_grade_le A r hn]
        exact (Module.End.mem_invtSubmodule_iff_map_le A).1
          (Krylov.subspace_grade_mem_invtSubmodule A r)
      · rw [LinearMap.finrank_map_of_injective A hAi.injective]
    rw [hinv] at hx hwell
    have hr : r ∈ K := by
      change r ∈ Krylov.subspace A r n
      rw [Krylov.subspace_eq_of_grade_le A r hn]
      rw [Krylov.subspace_grade_eq_fullSubspace]
      exact Krylov.subspace_le_fullSubspace A r 1 (Krylov.self_mem_subspace A r Nat.zero_lt_one)
    exact (sub_eq_zero.1 (lemma_2_1_7 hwell hx hr hinv)).symm

/-- **Theorem 2.3.1(3)** of [liesen2013krylov].
For nonsingular $A$, the projection with trial space $K$ and constraint space $AK$ exists
uniquely, minimizes the residual norm or, equivalently, the $A^*A$-norm of the error on
$x_0+K$, and is exact at and after the grade.

**Generalization.** The source assumes positive grade and considers steps up to termination.
The characterization also covers step zero, zero initial residual, and steps after the grade. -/
theorem theorem_2_3_1_minres (A : E →ₗ[𝕜] E) (hA : Function.Bijective A)
    (b x₀ xstar : E) (hstar : A xstar = b) (n : ℕ) :
    let K := krylovSubspace A (b - A x₀) n
    ProjectionWellDefined A K (K.map A) ∧
    (∃! x, IsProjectionIterate A b x₀ K (K.map A) x) ∧
    (∀ x, IsProjectionIterate A b x₀ K (K.map A) x ↔ Krylov.IsMinResidualIterate A b x₀ n x) ∧
    (∀ x, IsProjectionIterate A b x₀ K (K.map A) x ↔
      x - x₀ ∈ K ∧ ∀ w ∈ K, EnergyOrthogonal (A.adjoint.comp A) (xstar - x) w) ∧
    (∀ x, IsProjectionIterate A b x₀ K (K.map A) x ↔
      x - x₀ ∈ K ∧ ∀ y, y - x₀ ∈ K →
        energyNorm (A.adjoint.comp A) (xstar - x) ≤ energyNorm (A.adjoint.comp A) (xstar - y)) ∧
    (grade A (b - A x₀) ≤ n → ∀ x, IsProjectionIterate A b x₀ K (K.map A) x → A x = b) := by
  dsimp only
  have hw := (theorem_2_1_6 A (krylovSubspace A (b - A x₀) n)).2.2 hA
  refine ⟨hw, existsUnique_isPetrovGalerkin_of_isCompl hw hA.injective.injOn b x₀,
    fun _ => IsMinResidual.iff_isPetrovGalerkin.symm, ?_, ?_, ?_⟩
  · intro x
    have hinner (w : E) :
        energyInnerProduct (A.adjoint.comp A) (xstar - x) w = inner 𝕜 (A w) (b - A x) := by
      change inner 𝕜 w (A.adjoint (A (xstar - x))) = _
      rw [LinearMap.adjoint_inner_right, map_sub, hstar]
    refine ⟨fun hx => ⟨hx.mem, fun w hw' => ?_⟩, fun ⟨hmem, hort⟩ => ⟨hmem, ?_⟩⟩
    · simpa only [EnergyOrthogonal, hinner] using
        hx.inner_residual_eq_zero (Submodule.mem_map_of_mem hw')
    · intro y hy
      obtain ⟨w, hw', rfl⟩ := Submodule.mem_map.1 hy
      simpa only [EnergyOrthogonal, hinner] using hort w hw'
  · have hnorm (y : E) : energyNorm (A.adjoint.comp A) (xstar - y) = ‖b - A y‖ := by
      rw [energyNorm, LinearMap.comp_apply, LinearMap.adjoint_inner_left,
        inner_self_eq_norm_sq, map_sub, hstar,
        Real.sqrt_sq (norm_nonneg _)]
    intro x
    unfold IsProjectionIterate
    rw [← IsMinResidual.iff_isPetrovGalerkin]
    exact ⟨fun h => ⟨h.mem, fun y hy => by simpa only [hnorm] using h.min y hy⟩,
      fun ⟨hx, h⟩ => ⟨hx, fun y hy => by simpa only [hnorm] using h y hy⟩⟩
  · exact fun hn _ hx => Krylov.IsMinResidualIterate.apply_eq_of_grade_le
      (IsMinResidual.iff_isPetrovGalerkin.2 hx) hn hA.injective.injOn

/-- **Theorem 2.3.2** of [liesen2013krylov].
A vector $z_n \in U$ is a best approximation to $z$ in the $B$-norm if and only if its
error is $B$-orthogonal to every vector of $U$.

**Generalization.** The equivalence holds on arbitrary inner product spaces for symmetric
coercive $B$. -/
theorem theorem_2_3_2 (B : E →ₗ[𝕜] E) (hB : B.IsSymmetricCoercive)
    (U : Submodule 𝕜 E) (z zₙ : E) (hzₙ : zₙ ∈ U) :
    (∀ w ∈ U, EnergyOrthogonal B (z - zₙ) w) ↔
      ∀ w ∈ U, energyNorm B (z - zₙ) ≤ energyNorm B (z - w) := by
  have hiff := IsGalerkin.iff_energyNorm_min (x := zₙ) (x₀ := 0) (K := U) hB
    (show B z = B z from rfl)
  simp only [sub_zero] at hiff
  constructor
  · intro hort
    refine (hiff.1 ⟨by simpa using hzₙ, ?_⟩).2
    rw [← map_sub]
    exact hort
  · intro hmin w hw
    have hp := hiff.2 ⟨hzₙ, hmin⟩
    have h := hp.inner_residual_eq_zero hw
    rwa [← map_sub] at h

end LiesenStrakos
