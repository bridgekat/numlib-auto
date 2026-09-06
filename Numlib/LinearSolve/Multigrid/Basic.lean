import Mathlib.Analysis.InnerProductSpace.Adjoint
import Numlib.Analysis.InnerProductSpace.Energy
import Numlib.LinearSolve.Projection.Optimality
import Numlib.LinearSolve.Stationary.Splitting

/-!
# The Galerkin coarse problem and the coarse-grid correction

Given a symmetric coercive `A` on an inner product space `E` and a *prolongation*
`Pr : F →ₗ[𝕜] E` from a finite-dimensional coarse space `F`, the **Galerkin coarse operator** is
`A_H = Pr† A Pr` (`Multigrid.galerkinCoarse`) and the **coarse-grid correction** is
`T = 1 - Pr A_H⁻¹ Pr† A` (`Multigrid.coarseCorrection`).

The design decision of this module is to *define* the coarse-grid projector
`Q = Pr A_H⁻¹ Pr† A` as the `A`-orthogonal projector onto `range Pr` — that is, as
`Submodule.starProjection` in the energy space `WithEnergy A hA` of
`Numlib/Analysis/InnerProductSpace/Energy.lean`, transported back along `WithEnergy.equiv` — and to
prove the formula `Q x = Pr y` for `A_H y = Pr† (A x)` afterwards
(`Multigrid.coarseProjection_apply_eq`).  Stated that way, the classical facts about the
correction are the projection theory the library already has:

* it is the Galerkin step of `Numlib/LinearSolve/Projection/Basic` on the subspace `range Pr`
  (`Multigrid.isGalerkin_coarseSolve`), so `IsGalerkin.energyNorm_le` says that it minimizes the
  energy norm of the error over `x + range Pr`;
* the splitting of the space into the "smooth" and "oscillatory" subspaces is
  `starProjection`'s own range/kernel API: `range Q = ker (1 - Q) = range Pr` and
  `range (1 - Q) = ker Q = ker (Pr† A)`, and the two are complementary
  (`Multigrid.range_coarseProjection`, `Multigrid.ker_coarseCorrection`,
  `Multigrid.range_coarseCorrection`, `Multigrid.ker_coarseProjection`,
  `Multigrid.isCompl_range_ker`).

No mesh appears anywhere: a prolongation is any linear map into `E`, and a smoother is given by
its **error propagation operator** `S = 1 - B A` (`Multigrid.smootherOperator`), never by the
iteration itself, because every statement of the theory is about the error.  The classical
smoothers are the iteration operators of `Numlib/LinearSolve/Stationary/Splitting`
(`Multigrid.smootherOperator_eq_iterationOperator`).  The two-grid error propagation operator
`S^ν₂ (1 - Q) S^ν₁` is `Multigrid.twoGridOperator`.

The coarse space is finite-dimensional throughout — that is what makes the `A`-orthogonal
projection onto `range Pr` exist — and `E` is finite-dimensional wherever `Pr†` appears, which is
what `LinearMap.adjoint` needs.

## References

[^saad-iterative]: Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition,
  SIAM, 2003.  The coarse operator is his (13.39), the correction his (13.43), Lemma 13.1 is
  `Multigrid.coarseProjection_apply_eq`, and the subspace decomposition is his (13.59)–(13.61).
  His restriction `I_h^H` is `Pr†` up to the positive factor `2^d` of (13.37), which cancels out
  of every formula here.
-/

namespace Multigrid

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-! ### The Galerkin coarse operator -/

/-- The **Galerkin coarse operator** `A_H = Pr† A Pr` of a prolongation `Pr : F →ₗ[𝕜] E`
(Saad, *Iterative Methods for Sparse Linear Systems*, (13.39)). -/
noncomputable def galerkinCoarse [FiniteDimensional 𝕜 E] (A : E →ₗ[𝕜] E) (Pr : F →ₗ[𝕜] E) :
    F →ₗ[𝕜] F :=
  LinearMap.adjoint Pr ∘ₗ A ∘ₗ Pr

@[simp]
theorem galerkinCoarse_apply [FiniteDimensional 𝕜 E] (A : E →ₗ[𝕜] E) (Pr : F →ₗ[𝕜] E) (u : F) :
    galerkinCoarse A Pr u = LinearMap.adjoint Pr (A (Pr u)) := rfl

/-- The defining identity of the coarse operator: its quadratic form is the form of `A` restricted
to the range of the prolongation. -/
theorem inner_galerkinCoarse [FiniteDimensional 𝕜 E] (A : E →ₗ[𝕜] E) (Pr : F →ₗ[𝕜] E) (u v : F) :
    inner 𝕜 (galerkinCoarse A Pr u) v = inner 𝕜 (A (Pr u)) (Pr v) := by
  rw [galerkinCoarse_apply, LinearMap.adjoint_inner_left]

/-- **The coarse problem is well posed**: for symmetric coercive `A` and injective `Pr`, the
Galerkin coarse operator is symmetric coercive, hence invertible.  This is what makes the coarse
solve of the two-grid cycle meaningful. -/
theorem galerkinCoarse_isSymmetricCoercive [FiniteDimensional 𝕜 E] {A : E →ₗ[𝕜] E}
    (hA : A.IsSymmetricCoercive) {Pr : F →ₗ[𝕜] E} (hPr : Function.Injective Pr) :
    (galerkinCoarse A Pr).IsSymmetricCoercive := by
  refine ⟨fun u v => ?_, (LinearMap.isCoercive_iff_forall_pos _).2 fun u hu => ?_⟩
  · rw [inner_galerkinCoarse, hA.isSymmetric (Pr u) (Pr v), galerkinCoarse_apply,
      LinearMap.adjoint_inner_right]
  · have hPu : Pr u ≠ 0 := fun h => hu (hPr (by rw [h, map_zero]))
    rw [inner_galerkinCoarse]
    exact hA.isCoercive.inner_self_pos hPu

/-! ### The coarse-grid projector -/

section Projector

variable (A : E →ₗ[𝕜] E) (hA : A.IsSymmetricCoercive) (Pr : F →ₗ[𝕜] E)

/-- Saad's coarse-grid projector `Q_h = I_H^h A_H⁻¹ I_h^H A_h`, *defined* as the `A`-orthogonal
projector onto the range of the prolongation: the orthogonal projector of the energy space
`WithEnergy A hA` onto the image of `range Pr`, read back on `E`.  The formula
`Q x = Pr (A_H⁻¹ (Pr† (A x)))` is `Multigrid.coarseProjection_apply_eq`. -/
noncomputable def coarseProjection : E →ₗ[𝕜] E :=
  (WithEnergy.equiv A hA).symm.toLinearMap ∘ₗ
    (WithEnergy.submoduleMap A hA (LinearMap.range Pr)).starProjection.toLinearMap ∘ₗ
      (WithEnergy.equiv A hA).toLinearMap

/-- Saad's coarse-grid correction operator `T_h^H = I - Q_h` (Saad, *Iterative Methods for Sparse
Linear Systems*, (13.43)), the error propagation operator of one coarse-grid correction. -/
noncomputable def coarseCorrection : E →ₗ[𝕜] E := 1 - coarseProjection A hA Pr

@[simp]
theorem coarseCorrection_apply (x : E) :
    coarseCorrection A hA Pr x = x - coarseProjection A hA Pr x := rfl

@[simp]
theorem equiv_coarseProjection (x : E) :
    WithEnergy.equiv A hA (coarseProjection A hA Pr x)
      = (WithEnergy.submoduleMap A hA (LinearMap.range Pr)).starProjection
          (WithEnergy.equiv A hA x) :=
  rfl

/-- The value of the coarse-grid projector lies in the range of the prolongation. -/
theorem coarseProjection_apply_mem (x : E) : coarseProjection A hA Pr x ∈ LinearMap.range Pr := by
  have hmem : (WithEnergy.submoduleMap A hA (LinearMap.range Pr)).starProjection
      (WithEnergy.equiv A hA x) ∈ WithEnergy.submoduleMap A hA (LinearMap.range Pr) := by
    have h : (WithEnergy.submoduleMap A hA (LinearMap.range Pr)).starProjection
        (WithEnergy.equiv A hA x)
        ∈ (WithEnergy.submoduleMap A hA (LinearMap.range Pr)).starProjection.range :=
      ⟨WithEnergy.equiv A hA x, rfl⟩
    rwa [Submodule.range_starProjection] at h
  rw [← WithEnergy.equiv_mem_submoduleMap_iff A hA, equiv_coarseProjection]
  exact hmem

/-- The coarse-grid projector fixes the range of the prolongation. -/
theorem coarseProjection_apply_of_mem {x : E} (hx : x ∈ LinearMap.range Pr) :
    coarseProjection A hA Pr x = x :=
  (WithEnergy.equiv A hA).injective
    (Submodule.starProjection_eq_self_iff.2 ((WithEnergy.equiv_mem_submoduleMap_iff A hA).2 hx))

/-- Saad (13.59): the range of the coarse-grid projector is the range of the prolongation, the
"smooth" subspace `𝒮_h`. -/
@[simp]
theorem range_coarseProjection :
    LinearMap.range (coarseProjection A hA Pr) = LinearMap.range Pr := by
  refine le_antisymm ?_ fun z hz => ⟨z, coarseProjection_apply_of_mem A hA Pr hz⟩
  rintro _ ⟨x, rfl⟩
  exact coarseProjection_apply_mem A hA Pr x

/-- Saad (13.60): the coarse-grid correction annihilates exactly the range of the
prolongation. -/
@[simp]
theorem ker_coarseCorrection :
    LinearMap.ker (coarseCorrection A hA Pr) = LinearMap.range Pr := by
  ext x
  rw [LinearMap.mem_ker, coarseCorrection_apply, sub_eq_zero]
  exact ⟨fun h => h ▸ coarseProjection_apply_mem A hA Pr x,
    fun h => (coarseProjection_apply_of_mem A hA Pr h).symm⟩

section Adjoint

variable [FiniteDimensional 𝕜 E]

/-- Energy orthogonality to the range of the prolongation is exactly `Pr† A x = 0`, which is why
the "oscillatory" subspace of Saad (13.61) is the kernel of `Pr† A`. -/
theorem equiv_mem_orthogonal_iff (x : E) :
    WithEnergy.equiv A hA x ∈ (WithEnergy.submoduleMap A hA (LinearMap.range Pr))ᗮ
      ↔ LinearMap.adjoint Pr (A x) = 0 := by
  have key : ∀ v : F, inner 𝕜 (WithEnergy.equiv A hA (Pr v)) (WithEnergy.equiv A hA x)
      = inner 𝕜 v (LinearMap.adjoint Pr (A x)) := fun v => by
    rw [WithEnergy.inner_equiv, energyInner, hA.isSymmetric (Pr v) x,
      LinearMap.adjoint_inner_right]
  constructor
  · intro h
    have hv := h _ ((WithEnergy.equiv_mem_submoduleMap_iff A hA).2
      ⟨LinearMap.adjoint Pr (A x), rfl⟩)
    rw [key] at hv
    exact inner_self_eq_zero.1 hv
  · intro h
    refine (Submodule.mem_orthogonal _ _).2 fun w hw => ?_
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 hw
    obtain ⟨v, rfl⟩ := hz
    exact (key v).trans (by rw [h, inner_zero_right])

/-- **Saad's Lemma 13.1**: the Galerkin coarse-grid projector is the `A`-orthogonal projector onto
the range of the prolongation.  Concretely, if `y` solves the coarse problem
`A_H y = Pr† (A x)`, then `Q x = Pr y`, which is the formula `Q = Pr A_H⁻¹ Pr† A` of Saad (13.43)
written without an inverse. -/
theorem coarseProjection_apply_eq {x : E} {y : F}
    (hy : galerkinCoarse A Pr y = LinearMap.adjoint Pr (A x)) :
    coarseProjection A hA Pr x = Pr y := by
  refine (WithEnergy.equiv A hA).injective ?_
  rw [equiv_coarseProjection]
  refine Submodule.eq_starProjection_of_mem_orthogonal
    ((WithEnergy.equiv_mem_submoduleMap_iff A hA).2 ⟨y, rfl⟩) ?_
  rw [← map_sub]
  refine (equiv_mem_orthogonal_iff A hA Pr (x - Pr y)).2 ?_
  rw [map_sub, map_sub, ← galerkinCoarse_apply A Pr y, hy, sub_self]

/-- Saad (13.61): the kernel of the coarse-grid projector is the kernel of `Pr† A`, the
"oscillatory" subspace `𝒯_h`. -/
@[simp]
theorem ker_coarseProjection :
    LinearMap.ker (coarseProjection A hA Pr) = LinearMap.ker (LinearMap.adjoint Pr ∘ₗ A) := by
  ext x
  rw [LinearMap.mem_ker, LinearMap.mem_ker, LinearMap.comp_apply,
    ← equiv_mem_orthogonal_iff A hA Pr, ← Submodule.starProjection_apply_eq_zero_iff,
    ← equiv_coarseProjection]
  exact ⟨fun h => by rw [h, map_zero],
    fun h => (WithEnergy.equiv A hA).injective (by simpa using h)⟩

/-- Saad (13.61): the range of the coarse-grid correction is the kernel of `Pr† A`. -/
@[simp]
theorem range_coarseCorrection :
    LinearMap.range (coarseCorrection A hA Pr) = LinearMap.ker (LinearMap.adjoint Pr ∘ₗ A) := by
  rw [← ker_coarseProjection A hA Pr]
  refine le_antisymm ?_ fun x hx => ⟨x, ?_⟩
  · rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker, coarseCorrection_apply, map_sub,
      coarseProjection_apply_of_mem A hA Pr (coarseProjection_apply_mem A hA Pr x), sub_self]
  · rw [coarseCorrection_apply, LinearMap.mem_ker.1 hx, sub_zero]

include hA in
/-- Saad (13.59): `E` is the direct sum of the smooth subspace `range Pr` and the oscillatory
subspace `ker (Pr† A)`, the ranges of the coarse-grid projector and of the coarse-grid
correction. -/
theorem isCompl_range_ker :
    IsCompl (LinearMap.range Pr) (LinearMap.ker (LinearMap.adjoint Pr ∘ₗ A)) := by
  constructor
  · refine Submodule.disjoint_def.2 fun x hx hker => ?_
    have h1 : coarseProjection A hA Pr x = x := coarseProjection_apply_of_mem A hA Pr hx
    have h2 : coarseProjection A hA Pr x = 0 :=
      LinearMap.mem_ker.1 (by rw [ker_coarseProjection A hA Pr]; exact hker)
    rw [← h1, h2]
  · refine codisjoint_iff.2 (top_le_iff.1 fun x _ => ?_)
    refine Submodule.mem_sup.2 ⟨coarseProjection A hA Pr x, coarseProjection_apply_mem A hA Pr x,
      coarseCorrection A hA Pr x, ?_, by rw [coarseCorrection_apply]; abel⟩
    rw [← range_coarseCorrection A hA Pr]
    exact LinearMap.mem_range_self _ x

/-! ### The coarse solve as a Galerkin step -/

/-- The coarse-grid correction is the Galerkin projection method of
`Numlib/LinearSolve/Projection/Basic` on the subspace `range Pr`: solving the coarse residual
equation `A_H δ = Pr† (b - A x)` and adding `Pr δ` produces a Galerkin iterate.  Consequently
`IsGalerkin.energyNorm_le` bounds its error in the energy norm by that of every point of
`x + range Pr`. -/
theorem isGalerkin_coarseSolve {b x : E} {d : F}
    (hd : galerkinCoarse A Pr d = LinearMap.adjoint Pr (b - A x)) :
    IsGalerkin A b x (LinearMap.range Pr) (x + Pr d) := by
  have hzero : LinearMap.adjoint Pr (b - A (x + Pr d)) = 0 := by
    have hres : b - A (x + Pr d) = b - A x - A (Pr d) := by rw [map_add]; abel
    rw [hres, map_sub, ← galerkinCoarse_apply A Pr d, hd, sub_self]
  refine ⟨by simp, (Submodule.mem_orthogonal _ _).2 ?_⟩
  rintro w ⟨v, rfl⟩
  rw [← inner_conj_symm, ← LinearMap.adjoint_inner_left Pr, hzero, inner_zero_left, map_zero]

/-- The same statement in terms of the projector: the coarse-grid correction of `x` towards the
solution `x*` is `x + Q (x* - x)`, a Galerkin iterate on `range Pr`, and the error it leaves is
`T (x* - x)`. -/
theorem isGalerkin_coarseProjection {b x xstar : E} (hstar : A xstar = b) :
    IsGalerkin A b x (LinearMap.range Pr) (x + coarseProjection A hA Pr (xstar - x)) := by
  refine ⟨by simpa using coarseProjection_apply_mem A hA Pr (xstar - x),
    (Submodule.mem_orthogonal _ _).2 ?_⟩
  rintro w ⟨v, rfl⟩
  set e := xstar - x with he
  have hres : b - A (x + coarseProjection A hA Pr e) = A (coarseCorrection A hA Pr e) := by
    have h1 : A (coarseCorrection A hA Pr e) = A e - A (coarseProjection A hA Pr e) := by
      rw [coarseCorrection_apply, map_sub]
    have h2 : A e = b - A x := by rw [he, map_sub, hstar]
    rw [h1, h2, map_add]
    abel
  have horth : LinearMap.adjoint Pr (A (coarseCorrection A hA Pr e)) = 0 := by
    refine (equiv_mem_orthogonal_iff A hA Pr _).1 ?_
    rw [coarseCorrection_apply, map_sub, equiv_coarseProjection]
    exact Submodule.sub_starProjection_mem_orthogonal _
  rw [← inner_conj_symm, hres, ← LinearMap.adjoint_inner_left Pr, horth, inner_zero_left, map_zero]

end Adjoint

end Projector

/-! ### Smoothers and the two-grid operator -/

/-- The **error propagation operator** of a smoother with approximate inverse `B`: `S = 1 - B A`
(Saad, *Iterative Methods for Sparse Linear Systems*, (13.40)–(13.42)).  A smoother enters the
theory only through this operator, because every statement of the theory is about the error. -/
def smootherOperator (A B : E →ₗ[𝕜] E) : E →ₗ[𝕜] E := 1 - B ∘ₗ A

@[simp]
theorem smootherOperator_apply (A B : E →ₗ[𝕜] E) (x : E) :
    smootherOperator A B x = x - B (A x) := rfl

/-- The classical smoothers are instances: the error propagation operator of the stationary
iteration built from a splitting `A = M - N` is `Multigrid.smootherOperator A M⁻¹`, which is the
iteration operator of `Numlib/LinearSolve/Stationary/Splitting`. -/
theorem smootherOperator_eq_iterationOperator {A : Module.End 𝕜 E} (s : Stationary.Splitting A) :
    smootherOperator A (Ring.inverse s.m) = s.iterationOperator :=
  rfl

/-- The error propagation operator `M_H^h` of the two-grid cycle with `ν₁` pre-smoothing steps and
`ν₂` post-smoothing steps around one coarse-grid correction (Saad, *Iterative Methods for Sparse
Linear Systems*, Algorithm 13.2). -/
noncomputable def twoGridOperator (A : E →ₗ[𝕜] E) (hA : A.IsSymmetricCoercive) (Pr : F →ₗ[𝕜] E)
    (S : E →ₗ[𝕜] E) (nu1 nu2 : ℕ) : E →ₗ[𝕜] E :=
  (S ^ nu2) ∘ₗ coarseCorrection A hA Pr ∘ₗ (S ^ nu1)

@[simp]
theorem twoGridOperator_apply (A : E →ₗ[𝕜] E) (hA : A.IsSymmetricCoercive) (Pr : F →ₗ[𝕜] E)
    (S : E →ₗ[𝕜] E) (nu1 nu2 : ℕ) (x : E) :
    twoGridOperator A hA Pr S nu1 nu2 x
      = (S ^ nu2) (coarseCorrection A hA Pr ((S ^ nu1) x)) :=
  rfl

/-- With no smoothing the two-grid cycle is the coarse-grid correction itself. -/
@[simp]
theorem twoGridOperator_zero_zero (A : E →ₗ[𝕜] E) (hA : A.IsSymmetricCoercive) (Pr : F →ₗ[𝕜] E)
    (S : E →ₗ[𝕜] E) : twoGridOperator A hA Pr S 0 0 = coarseCorrection A hA Pr := by
  ext x
  simp

end Multigrid
