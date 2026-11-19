/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.LiesenStrakos.Chapter02.Section02
import Numlib.Krylov.CG
import Numlib.Krylov.Hessenberg
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# §2.5. Derivation of Krylov methods

The conjugate gradient recurrence produces mutually orthogonal residuals and pairs of conjugate
search directions. For a conforming Galerkin method, the energy error splits into a discretization
error and a coefficient error. The Galerkin problem also has a quadratic minimization form.

## Main results

* `LiesenStrakos.theorem_2_5_1` gives the residual and direction bases in CG.
* `LiesenStrakos.theorem_2_5_2` gives the Galerkin energy error decomposition.
* `LiesenStrakos.theorem_2_5_3` identifies the unique Galerkin solution with the minimizer of
  the quadratic energy on the affine trial space.
* `LiesenStrakos.gmres_triangular_system` gives the triangular system and the residual norm
  used by a GMRES step.

## Deviations from the source

* **Algorithm 2.5.1** (reading). The fixed-step recurrence uses total divisions. The quadratic
  functional is defined in an arbitrary real inner product space.
* **Theorem 2.5.3** (generalization). The quadratic minimization result applies on any
  finite-dimensional affine Galerkin trial space with a symmetric coercive operator. See
  `LiesenStrakos.theorem_2_5_3`.
* **Theorem 2.5.2** (generalization). The identity is stated for a Galerkin synthesis map
  in an energy inner product, including the conforming finite-element space in the source.
-/

namespace LiesenStrakos

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Algorithm 2.5.1 of [liesen2013krylov], with the iterate, residual and direction as the
state after $n$ steps of the conjugate gradient recurrence.

**Reading.** This is a fixed number of recurrence steps using total divisions. The source
algorithm takes an HPD matrix and stops according to a supplied criterion. -/
noncomputable abbrev cgIterate (A : E →ₗ[𝕜] E) (b x₀ : E) (n : ℕ) : CG.State E :=
  CG.iterate A b x₀ n

/-- **Theorem 2.5.1** of [liesen2013krylov].
If CG for a Hermitian positive definite operator has a nonzero residual at step $n$, the residuals
through step $n$ are an orthogonal basis of $\mathcal K_{n+1}$. The directions through step $n$
are an $A$-orthogonal basis of the same space. -/
theorem theorem_2_5_1 [FiniteDimensional 𝕜 E] {A : E →ₗ[𝕜] E} (hA : A.IsSymmetricCoercive)
    (b x₀ : E) (n : ℕ) (hn : (cgIterate A b x₀ n).r ≠ 0) :
    let K := krylovSubspace A (b - A x₀) (n + 1)
    let rs := fun i : Fin (n + 1) => (cgIterate A b x₀ i).r
    let ps := fun i : Fin (n + 1) => (cgIterate A b x₀ i).p
    LinearIndependent 𝕜 rs ∧ Submodule.span 𝕜 (Set.range rs) = K ∧
      (∀ i j, i ≠ j → inner 𝕜 (rs i) (rs j) = 0) ∧
    LinearIndependent 𝕜 ps ∧ Submodule.span 𝕜 (Set.range ps) = K ∧
      (∀ i j, i ≠ j → inner 𝕜 (A (ps i)) (ps j) = 0) := by
  dsimp only
  have hd : n + 1 ≤ Krylov.grade A (b - A x₀) := by
    by_contra! h
    exact hn (CG.residual_eq_zero_of_grade_le b x₀ hA (by omega))
  have hr := CG.span_residual_eq b x₀ hA (n + 1)
  have hp := CG.span_direction_eq b x₀ hA (n + 1)
  have hdim := (Krylov.finrank_subspace A (b - A x₀) (n + 1)).trans (min_eq_left hd)
  have hbasis (f : Fin (n + 1) → E)
      (hf : Submodule.span 𝕜 (Set.range f) = krylovSubspace A (b - A x₀) (n + 1)) :
      LinearIndependent 𝕜 f := by
    rw [linearIndependent_iff_card_eq_finrank_span]
    change Fintype.card (Fin (n + 1)) = Module.finrank 𝕜 (Submodule.span 𝕜 (Set.range f))
    rw [hf, Fintype.card_fin]
    exact hdim.symm
  exact ⟨hbasis _ hr, hr, fun _ _ hij => CG.inner_residual_eq_zero b x₀ hA
      (fun h => hij (Fin.ext h)),
    hbasis _ hp, hp, fun _ _ hij => CG.inner_apply_direction_eq_zero b x₀ hA
      (fun h => hij (Fin.ext h))⟩

/-- **Theorem 2.5.2** of [liesen2013krylov].
Let $u$ solve the ambient problem and let $u_D+C x$ be its Galerkin approximation on the affine
space with direction $\operatorname{range} C$. For arbitrary approximate coefficients $y$, the
squared energy error of $u_D+C y$ is the sum of the squared discretization error and the squared
coefficient error in the stiffness operator $C^* B C$. The synthesis map $C$ sends coefficient
vectors to their corresponding trial functions.

**Generalization.** The source takes the Poisson energy and a conforming finite-element basis.
After subtracting the common Dirichlet lift, use the homogeneous trial space as the ambient
energy space, and let $C$ synthesize finite-element functions from their coefficients. -/
theorem theorem_2_5_2 {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (B : H →ₗ[ℝ] H) (hB : B.IsSymmetricCoercive) (C : V →L[ℝ] H)
    (b u uD : H) (x y : V) (hu : B u = b)
    (hx : IsGalerkin B b uD (LinearMap.range C.toLinearMap) (uD + C x)) :
    let A := C.adjoint.toLinearMap.comp (B.comp C.toLinearMap)
    energyNorm B (u - (uD + C y)) ^ 2 =
      energyNorm B (u - (uD + C x)) ^ 2 + energyNorm A (x - y) ^ 2 := by
  dsimp only
  rw [IsGalerkin.energyNorm_sq_add hB hx hu (by
    rw [add_sub_cancel_left]
    exact ⟨y, rfl⟩)]
  congr 2
  rw [show uD + C x - (uD + C y) = C (x - y) by rw [map_sub]; abel]
  unfold energyNorm
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  exact congrArg (fun q : ℝ => Real.sqrt (RCLike.re q))
    (C.adjoint_inner_left (x - y) (B (C (x - y)))).symm

/-- The quadratic functional in (2.5.31) is one half of the quadratic energy minus the load
applied to the trial vector. A real load functional is represented by its inner-product vector.

**Generalization.** The same quadratic formula is defined on an arbitrary real inner product
space. -/
noncomputable abbrev quadraticFunctional {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (A : H →ₗ[ℝ] H) (b : H) : H → ℝ := energyFunctional A b

/-- **Theorem 2.5.3** of [liesen2013krylov].
The affine Galerkin problem for a symmetric coercive operator and the minimization of its
quadratic functional on the same finite-dimensional trial space have the same unique solution.

**Generalization.** The source proves this equivalence for its conforming finite-element
problem. The equivalence holds for any finite-dimensional affine trial space of a real inner
product space with a symmetric coercive operator. -/
theorem theorem_2_5_3 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : H →ₗ[ℝ] H) (hA : A.IsSymmetricCoercive) (b x₀ : H) (K : Submodule ℝ H)
    [FiniteDimensional ℝ K] :
    (∃! x, IsGalerkin A b x₀ K x) ∧
      ∀ x, IsGalerkin A b x₀ K x ↔
        x - x₀ ∈ K ∧ ∀ y, y - x₀ ∈ K →
          quadraticFunctional A b x ≤ quadraticFunctional A b y := by
  refine ⟨existsUnique_isGalerkin_of_isCoercive b x₀ K hA.isCoercive, fun x => ?_⟩
  exact ⟨fun hx => ⟨hx.mem, (isGalerkin_iff_forall_quadratic_le hA hx.mem).1 hx⟩,
    fun ⟨hx, h⟩ => (isGalerkin_iff_forall_quadratic_le hA hx).2 h⟩

/-- A full orthogonalization method iterate lies in the affine Krylov space and has residual
orthogonal to the same Krylov space. -/
abbrev IsFOMIterate (A : E →ₗ[𝕜] E) (b x₀ : E) (n : ℕ) (x : E) : Prop :=
  Krylov.IsGalerkinIterate A b x₀ n x

/-- A GMRES iterate minimizes the Euclidean norm of the residual over the affine Krylov space. -/
abbrev IsGMRESIterate (A : E →ₗ[𝕜] E) (b x₀ : E) (n : ℕ) (x : E) : Prop :=
  Krylov.IsMinResidualIterate A b x₀ n x

/-- MINRES is the minimal-residual method for a Hermitian operator. -/
abbrev IsMINRESIterate (A : E →ₗ[𝕜] E) (_hA : A.IsSymmetric) (b x₀ : E) (n : ℕ) (x : E) : Prop :=
  IsGMRESIterate A b x₀ n x

/-- In a GMRES step before Arnoldi breakdown, the coefficients solve the triangular system
from (2.5.62) and the residual norm equals the modulus of the last rotated right-hand side
entry, as in (2.5.63) of [liesen2013krylov]. -/
theorem gmres_triangular_system [FiniteDimensional 𝕜 E] {A : E →ₗ[𝕜] E} {b x₀ x : E}
    {n : ℕ} (hn : n < grade A (b - A x₀)) (hx : IsGMRESIterate A b x₀ n x) :
    let r₀ := b - A x₀
    let h := Arnoldi.coeff A r₀
    let β : 𝕜 := ↑‖r₀‖
    ‖b - A x‖ = ‖Krylov.gamma h β n‖ ∧
      ∃ y : Fin n → 𝕜,
        (Krylov.hessenbergSqOf (Krylov.rotated h n) n).mulVec y =
          (fun i : Fin n => Krylov.gvec h β i) ∧
        x = x₀ + ∑ j, y j • Arnoldi.vec A r₀ j :=
  ⟨hx.norm_residual_eq_norm_gamma hn, hx.exists_mulVec_rotated_eq hn.le⟩

end LiesenStrakos
