/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Numlib.Analysis.InnerProductSpace.Energy
import Numlib.Projection.Optimality
import Numlib.Stationary.Splitting

/-!
# The Galerkin coarse problem and the coarse-grid correction

Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$, let $E$ be an inner product space over
$\mathbb{K}$, let $F$ be a finite-dimensional inner product space (the coarse space), let
$A \colon E \to E$ be linear, and let $P \colon F \to E$ be a linear map, the **prolongation** (the
Lean variable `Pr`). The **Galerkin coarse operator** is $A_H = P^* A P$, and the **coarse-grid
correction** is $T = I - Q$ with the coarse-grid projector $Q = P A_H^{-1} P^* A$. This follows
[saad2003iterative], §13.4.1–13.4.2 and §13.5.1. Write $\|x\|_A = \sqrt{\operatorname{Re} \langle
Ax, x \rangle}$ for the energy norm.

For $A$ symmetric coercive, $Q$ is the $A$-orthogonal projector onto $\operatorname{range} P$. Then
$T$ is a Galerkin projection step on the subspace $\operatorname{range} P$, so it minimizes the
energy norm of the error over $x + \operatorname{range} P$. The space splits into the "smooth"
subspace $\operatorname{range} Q = \ker T = \operatorname{range} P$ and the "oscillatory" subspace
$\operatorname{range} T = \ker Q = \ker(P^* A)$, and the two are complementary. A smoother enters
only through its **error propagation operator** $S = I - BA$, and the two-grid error propagation
operator is $S^{\nu_2} (I - Q) S^{\nu_1}$.

## Main definitions

* `Multigrid.galerkinCoarse`: the Galerkin coarse operator $A_H = P^* A P$.
* `Multigrid.coarseProjection`: the coarse-grid projector $Q$, the $A$-orthogonal projector onto
  $\operatorname{range} P$.
* `Multigrid.coarseCorrection`: the coarse-grid correction $T = I - Q$.
* `Multigrid.smootherOperator`: the error propagation operator $S = I - BA$ of a smoother with
  approximate inverse $B$.
* `Multigrid.twoGridOperator`: the two-grid error propagation operator
  $S^{\nu_2} (I - Q) S^{\nu_1}$.

## Main results

* `Multigrid.galerkinCoarse_isSymmetricCoercive`: if $A$ is symmetric coercive and $P$ is injective,
  then $A_H$ is symmetric coercive.
* `Multigrid.coarseProjection_apply_eq`: if $A_H y = P^* A x$, then $Qx = Py$ (Lemma 13.1 of
  [saad2003iterative]).
* `Multigrid.range_coarseProjection`, `Multigrid.ker_coarseCorrection`: $\operatorname{range} Q =
  \ker T = \operatorname{range} P$.
* `Multigrid.ker_coarseProjection`, `Multigrid.range_coarseCorrection`:
  $\ker Q = \operatorname{range} T = \ker(P^* A)$.
* `Multigrid.isCompl_range_ker`: $E = \operatorname{range} P \oplus \ker(P^* A)$.
* `Multigrid.isGalerkin_coarseSolve`, `Multigrid.isGalerkin_coarseProjection`: the coarse-grid
  correction of an iterate is a Galerkin iterate on $\operatorname{range} P$.
* `Multigrid.smootherOperator_eq_iterationOperator`: the iteration operator of a splitting
  $A = M - N$ is the error propagation operator of the smoother with $B = M^{-1}$.

## Implementation notes

* The coarse-grid projector is defined as the orthogonal projector `Submodule.starProjection` onto
  the image of $\operatorname{range} P$ in the energy space `WithEnergy A hA` of
  `Numlib.Analysis.InnerProductSpace.Energy`, transported back to $E$ along `WithEnergy.equiv`. The
  formula $Q = P A_H^{-1} P^* A$ is then a theorem, `Multigrid.coarseProjection_apply_eq`, stated
  without an inverse. With this definition, the range and kernel facts and the Galerkin property
  come from the projection theory of `Numlib.Projection.Basic` and the range and kernel facts of
  `Submodule.starProjection`.
* No mesh appears. A prolongation is any linear map into $E$. A smoother is given by its error
  propagation operator, never by the iteration itself, because every statement of the theory is
  about the error. The classical smoothers are the iteration operators of
  `Numlib.Stationary.Splitting`.
* The coarse space $F$ is finite-dimensional throughout, so that the $A$-orthogonal projection onto
  $\operatorname{range} P$ exists. The space $E$ is finite-dimensional wherever $P^*$ appears,
  because `LinearMap.adjoint` needs this.
-/

namespace Multigrid

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-! ### The Galerkin coarse operator -/

/-- Let $E$ be finite-dimensional, let $A \colon E \to E$ be linear, and let $P \colon F \to E$ be a
prolongation. The **Galerkin coarse operator** is
$$A_H = P^* A P \colon F \to F.$$

This is (13.39) of [saad2003iterative]. The adjoint $P^*$ is `LinearMap.adjoint Pr`. -/
noncomputable def galerkinCoarse [FiniteDimensional 𝕜 E] (A : E →ₗ[𝕜] E) (Pr : F →ₗ[𝕜] E) :
    F →ₗ[𝕜] F :=
  LinearMap.adjoint Pr ∘ₗ A ∘ₗ Pr

/-- The Galerkin coarse operator acts as $A_H u = P^*(A(Pu))$. -/
@[simp]
theorem galerkinCoarse_apply [FiniteDimensional 𝕜 E] (A : E →ₗ[𝕜] E) (Pr : F →ₗ[𝕜] E) (u : F) :
    galerkinCoarse A Pr u = LinearMap.adjoint Pr (A (Pr u)) := rfl

/-- The quadratic form of the Galerkin coarse operator is the form of $A$ on the range of the
prolongation: $\langle A_H u, v \rangle = \langle A P u, P v \rangle$ for all $u, v \in F$. -/
theorem inner_galerkinCoarse [FiniteDimensional 𝕜 E] (A : E →ₗ[𝕜] E) (Pr : F →ₗ[𝕜] E) (u v : F) :
    inner 𝕜 (galerkinCoarse A Pr u) v = inner 𝕜 (A (Pr u)) (Pr v) := by
  rw [galerkinCoarse_apply, LinearMap.adjoint_inner_left]

/-- Let $E$ be finite-dimensional, let $A \colon E \to E$ be symmetric coercive, and let the
prolongation $P \colon F \to E$ be injective. Then the Galerkin coarse operator $A_H = P^* A P$
is symmetric coercive.

In particular, $A_H$ is invertible, so the coarse solve of the two-grid cycle is well posed. -/
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

/-- Let $A \colon E \to E$ be symmetric coercive and let $P \colon F \to E$ be a prolongation. The
**coarse-grid projector** $Q$ is the $A$-orthogonal projector onto $\operatorname{range} P$: for
$x \in E$, $Qx$ is the element of $\operatorname{range} P$ with
$\langle A(x - Qx), Pv \rangle = 0$ for all $v \in F$. This is the operator
$Q_h = I_H^h A_H^{-1} I_h^H A_h$ of [saad2003iterative].

The definition is the orthogonal projector of the energy space `WithEnergy A hA` onto the image
of $\operatorname{range} P$, read back on $E$. The formula $Qx = P A_H^{-1} P^* A x$ is
`Multigrid.coarseProjection_apply_eq`. -/
noncomputable def coarseProjection : E →ₗ[𝕜] E :=
  (WithEnergy.equiv A hA).symm.toLinearMap ∘ₗ
    (WithEnergy.submoduleMap A hA (LinearMap.range Pr)).starProjection.toLinearMap ∘ₗ
      (WithEnergy.equiv A hA).toLinearMap

/-- Let $A \colon E \to E$ be symmetric coercive and let $P \colon F \to E$ be a prolongation. The
**coarse-grid correction** is $T = I - Q$, where $Q$ is the coarse-grid projector
`Multigrid.coarseProjection`. It is the error propagation operator of one coarse-grid correction
step.

This is the operator $T_h^H = I - Q_h$ of (13.43) of [saad2003iterative]. -/
noncomputable def coarseCorrection : E →ₗ[𝕜] E := 1 - coarseProjection A hA Pr

/-- The coarse-grid correction acts as $Tx = x - Qx$. -/
@[simp]
theorem coarseCorrection_apply (x : E) :
    coarseCorrection A hA Pr x = x - coarseProjection A hA Pr x := rfl

/-- In the energy space `WithEnergy A hA`, the coarse-grid projector is the orthogonal projector
onto the image of $\operatorname{range} P$.

This is the definition of `Multigrid.coarseProjection`, and the proofs of this module go through
it. -/
@[simp]
theorem equiv_coarseProjection (x : E) :
    WithEnergy.equiv A hA (coarseProjection A hA Pr x)
      = (WithEnergy.submoduleMap A hA (LinearMap.range Pr)).starProjection
          (WithEnergy.equiv A hA x) :=
  rfl

/-- For every $x \in E$, the value $Qx$ of the coarse-grid projector lies in
$\operatorname{range} P$. -/
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

/-- The coarse-grid projector fixes the range of the prolongation: $Qx = x$ for
$x \in \operatorname{range} P$. -/
theorem coarseProjection_apply_of_mem {x : E} (hx : x ∈ LinearMap.range Pr) :
    coarseProjection A hA Pr x = x :=
  (WithEnergy.equiv A hA).injective
    (Submodule.starProjection_eq_self_iff.2 ((WithEnergy.equiv_mem_submoduleMap_iff A hA).2 hx))

/-- Let $A \colon E \to E$ be symmetric coercive and let $P \colon F \to E$ be a prolongation. The
range of the coarse-grid projector is the range of the prolongation:
$$\operatorname{range} Q = \operatorname{range} P.$$

This is the "smooth" subspace $\mathcal{S}_h$ of (13.59) of [saad2003iterative]. -/
@[simp]
theorem range_coarseProjection :
    LinearMap.range (coarseProjection A hA Pr) = LinearMap.range Pr := by
  refine le_antisymm ?_ fun z hz => ⟨z, coarseProjection_apply_of_mem A hA Pr hz⟩
  rintro _ ⟨x, rfl⟩
  exact coarseProjection_apply_mem A hA Pr x

/-- Let $A \colon E \to E$ be symmetric coercive and let $P \colon F \to E$ be a prolongation. The
kernel of the coarse-grid correction is the range of the prolongation:
$$\ker T = \operatorname{range} P.$$

This is (13.60) of [saad2003iterative]. -/
@[simp]
theorem ker_coarseCorrection :
    LinearMap.ker (coarseCorrection A hA Pr) = LinearMap.range Pr := by
  ext x
  rw [LinearMap.mem_ker, coarseCorrection_apply, sub_eq_zero]
  exact ⟨fun h => h ▸ coarseProjection_apply_mem A hA Pr x,
    fun h => (coarseProjection_apply_of_mem A hA Pr h).symm⟩

section Adjoint

variable [FiniteDimensional 𝕜 E]

/-- Let $E$ be finite-dimensional and let $A$ be symmetric coercive. A vector $x \in E$ is
$A$-orthogonal to $\operatorname{range} P$ if and only if $P^*(Ax) = 0$.

This is the reason why the "oscillatory" subspace of (13.61) of [saad2003iterative] is
$\ker(P^* A)$. The $A$-orthogonality is stated in the energy space `WithEnergy A hA`. -/
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

/-- **Lemma 13.1** of [saad2003iterative]. Let $E$ be finite-dimensional, let $A \colon E \to E$ be
symmetric coercive, and let $P \colon F \to E$ be a prolongation. Let $x \in E$, and let
$y \in F$ solve the coarse problem $A_H y = P^*(Ax)$. Then the $A$-orthogonal projector $Q$ onto
$\operatorname{range} P$ satisfies
$$Qx = Py.$$

This is the formula $Q = P A_H^{-1} P^* A$ of (13.43) of [saad2003iterative], written without an
inverse. The statement does not assume that $P$ is injective, so $A_H$ need not be invertible:
every solution $y$ gives the same $Py$. -/
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

/-- Let $E$ be finite-dimensional, let $A \colon E \to E$ be symmetric coercive, and let
$P \colon F \to E$ be a prolongation. The kernel of the coarse-grid projector is the kernel of
$P^* A$:
$$\ker Q = \ker(P^* A).$$

This is the "oscillatory" subspace $\mathcal{T}_h$ of (13.61) of [saad2003iterative]. -/
@[simp]
theorem ker_coarseProjection :
    LinearMap.ker (coarseProjection A hA Pr) = LinearMap.ker (LinearMap.adjoint Pr ∘ₗ A) := by
  ext x
  rw [LinearMap.mem_ker, LinearMap.mem_ker, LinearMap.comp_apply,
    ← equiv_mem_orthogonal_iff A hA Pr, ← Submodule.starProjection_apply_eq_zero_iff,
    ← equiv_coarseProjection]
  exact ⟨fun h => by rw [h, map_zero],
    fun h => (WithEnergy.equiv A hA).injective (by simpa using h)⟩

/-- Let $E$ be finite-dimensional, let $A \colon E \to E$ be symmetric coercive, and let
$P \colon F \to E$ be a prolongation. The range of the coarse-grid correction is the kernel of
$P^* A$:
$$\operatorname{range} T = \ker(P^* A).$$

This is (13.61) of [saad2003iterative]. -/
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
/-- Let $E$ be finite-dimensional, let $A \colon E \to E$ be symmetric coercive, and let
$P \colon F \to E$ be a prolongation. Then $E$ is the direct sum of the smooth subspace and the
oscillatory subspace:
$$E = \operatorname{range} P \oplus \ker(P^* A).$$

These are the ranges of the coarse-grid projector and of the coarse-grid correction. This is
(13.59) of [saad2003iterative]. The direct sum is `IsCompl`. -/
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

/-- Let $E$ be finite-dimensional, let $A \colon E \to E$ be linear, let $P \colon F \to E$ be a
prolongation, and let $b, x \in E$. If $d \in F$ solves the coarse residual equation
$A_H d = P^*(b - Ax)$, then $x + Pd$ is a Galerkin iterate for $Ax = b$ from $x$ on the subspace
$\operatorname{range} P$: the correction $Pd$ lies in $\operatorname{range} P$, and the residual
$b - A(x + Pd)$ is orthogonal to $\operatorname{range} P$.

The Galerkin property is `IsGalerkin` of `Numlib.Projection.Basic`. For symmetric coercive $A$,
`IsGalerkin.energyNorm_le` then says that the error of $x + Pd$ has energy norm at most that of
every point of $x + \operatorname{range} P$. -/
theorem isGalerkin_coarseSolve {b x : E} {d : F}
    (hd : galerkinCoarse A Pr d = LinearMap.adjoint Pr (b - A x)) :
    IsGalerkin A b x (LinearMap.range Pr) (x + Pr d) := by
  have hzero : LinearMap.adjoint Pr (b - A (x + Pr d)) = 0 := by
    have hres : b - A (x + Pr d) = b - A x - A (Pr d) := by rw [map_add]; abel
    rw [hres, map_sub, ← galerkinCoarse_apply A Pr d, hd, sub_self]
  refine ⟨by simp, (Submodule.mem_orthogonal _ _).2 ?_⟩
  rintro w ⟨v, rfl⟩
  rw [← inner_conj_symm, ← LinearMap.adjoint_inner_left Pr, hzero, inner_zero_left, map_zero]

/-- Let $E$ be finite-dimensional, let $A \colon E \to E$ be symmetric coercive, let
$P \colon F \to E$ be a prolongation, and let $x^* \in E$ solve $Ax^* = b$. Then for every
$x \in E$, the corrected iterate $x + Q(x^* - x)$ is a Galerkin iterate for $Ax = b$ from $x$ on
the subspace $\operatorname{range} P$.

The error of the corrected iterate is $x^* - x - Q(x^* - x) = T(x^* - x)$. The Galerkin property
is `IsGalerkin`. -/
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

/-- Let $A, B \colon E \to E$ be linear. The **error propagation operator** of the smoother with
approximate inverse $B$ is
$$S = I - BA.$$

This is (13.40)–(13.42) of [saad2003iterative]. A smoother enters the theory only through this
operator, because every statement of the theory is about the error. -/
def smootherOperator (A B : E →ₗ[𝕜] E) : E →ₗ[𝕜] E := 1 - B ∘ₗ A

/-- The error propagation operator of a smoother acts as $Sx = x - B(Ax)$. -/
@[simp]
theorem smootherOperator_apply (A B : E →ₗ[𝕜] E) (x : E) :
    smootherOperator A B x = x - B (A x) := rfl

/-- Let $A = M - N$ be a splitting of a linear operator $A$ on $E$, with $M$ invertible. Then the
error propagation operator $I - M^{-1} A$ of the smoother with approximate inverse $M^{-1}$ is
the iteration operator of the splitting.

The splitting is `Stationary.Splitting`, and its iteration operator is
`Stationary.Splitting.iterationOperator`. The term `Ring.inverse s.m` stands for $M^{-1}$.
So the classical smoothers of `Numlib.Stationary.Splitting` are instances of
`Multigrid.smootherOperator`. -/
theorem smootherOperator_eq_iterationOperator {A : Module.End 𝕜 E} (s : Stationary.Splitting A) :
    smootherOperator A (Ring.inverse s.m) = s.iterationOperator :=
  rfl

/-- Let $A \colon E \to E$ be symmetric coercive, let $P \colon F \to E$ be a prolongation, let
$S \colon E \to E$ be the error propagation operator of a smoother, and let
$\nu_1, \nu_2 \in \mathbb{N}$. The **two-grid error propagation operator** $M_H^h$ of the cycle
with $\nu_1$ pre-smoothing steps and $\nu_2$ post-smoothing steps around one coarse-grid
correction is
$$M_H^h = S^{\nu_2} (I - Q) S^{\nu_1}.$$

This is the operator of Algorithm 13.2 of [saad2003iterative]. The same smoother is used before
and after the correction. -/
noncomputable def twoGridOperator (A : E →ₗ[𝕜] E) (hA : A.IsSymmetricCoercive) (Pr : F →ₗ[𝕜] E)
    (S : E →ₗ[𝕜] E) (nu1 nu2 : ℕ) : E →ₗ[𝕜] E :=
  (S ^ nu2) ∘ₗ coarseCorrection A hA Pr ∘ₗ (S ^ nu1)

/-- The two-grid cycle acts as $M_H^h x = S^{\nu_2}(T(S^{\nu_1} x))$: pre-smoothing, then
coarse-grid correction, then post-smoothing. -/
@[simp]
theorem twoGridOperator_apply (A : E →ₗ[𝕜] E) (hA : A.IsSymmetricCoercive) (Pr : F →ₗ[𝕜] E)
    (S : E →ₗ[𝕜] E) (nu1 nu2 : ℕ) (x : E) :
    twoGridOperator A hA Pr S nu1 nu2 x
      = (S ^ nu2) (coarseCorrection A hA Pr ((S ^ nu1) x)) :=
  rfl

/-- With no smoothing steps, the two-grid operator is the coarse-grid correction: $M_H^h = T$ for
$\nu_1 = \nu_2 = 0$. -/
@[simp]
theorem twoGridOperator_zero_zero (A : E →ₗ[𝕜] E) (hA : A.IsSymmetricCoercive) (Pr : F →ₗ[𝕜] E)
    (S : E →ₗ[𝕜] E) : twoGridOperator A hA Pr S 0 0 = coarseCorrection A hA Pr := by
  ext x
  simp

end Multigrid
