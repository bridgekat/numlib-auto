/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Numlib.Krylov.Iterate

/-!
# Liesen and Strakoš, §5.10: Rounding errors in GMRES

A computed Arnoldi relation has a factorisation defect. Its basis also has a separate
orthogonality defect, given by the difference between the identity and the Gram matrix.

## Deviations from the source

* **Section 5.10.1** (generalization). The trial span and right-hand side identities use
  arbitrary spanning families or prefix orthogonality.

## Not formalized

* The condition number formula for the Simpler GMRES basis in (5.10.7).
* The backward-stability and loss-of-orthogonality estimates of §§5.10.2–5.10.3 require a
  model of rounding in the Arnoldi and least-squares stages.
-/

namespace LiesenStrakos.Chapter05

open scoped InnerProductSpace

/-- **Equation (5.10.2)** of [liesen2013krylov]. Adjoining the initial residual to a
spanning family of the image of the previous Krylov space gives the next trial space
used by Simpler GMRES.

**Generalization.** The span identity holds over any field and only requires the family to span
the image trial space. -/
theorem simplerGMRES_trial_span {𝕜 E : Type*} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E]
    (A : E →ₗ[𝕜] E) (v : E) (n : ℕ) (W : Fin n → E)
    (hW : Submodule.span 𝕜 (Set.range W) = (Krylov.subspace A v n).map A) :
    Submodule.span 𝕜 (insert v (Set.range W)) = Krylov.subspace A v (n + 1) := by
  rw [Submodule.span_insert, hW]
  refine le_antisymm (sup_le ?_ (Krylov.map_subspace_le A v n)) ?_
  · exact Submodule.span_le.2 (Set.singleton_subset_iff.2
      (Krylov.self_mem_subspace A v (Nat.succ_pos n)))
  rw [Krylov.subspace_eq_span_image_Iio, Submodule.span_le]
  rintro _ ⟨j, hj, rfl⟩
  cases j with
  | zero =>
    simpa using (Submodule.mem_sup_left (T := (Krylov.subspace A v n).map A)
      (Submodule.mem_span_singleton_self v))
  | succ j =>
    change (A ^ (j + 1)) v ∈ Submodule.span 𝕜 {v} ⊔ (Krylov.subspace A v n).map A
    rw [pow_succ', Module.End.mul_apply]
    exact Submodule.mem_sup_right ⟨_, Krylov.pow_apply_mem_subspace A v (Nat.lt_of_succ_lt_succ hj),
      rfl⟩

/-- **Equation (5.10.6)** of [liesen2013krylov]. In Simpler GMRES the new orthogonal
image-space vector has the same inner product with the initial residual and with the
previous residual. The difference of those residuals belongs to the previous image space.

**Generalization.** Affine membership and orthogonality to the preceding image space suffice. -/
theorem simplerGMRES_rhs_eq {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (A : E →ₗ[𝕜] E) (b x₀ : E) {n : ℕ} (W y : Fin n → E)
    (hy : ∀ i, y i - x₀ ∈ Krylov.subspace A (b - A x₀) i.val)
    (hW : ∀ i, W i ∈ ((Krylov.subspace A (b - A x₀) i.val).map A)ᗮ) :
    ∀ i, inner 𝕜 (W i) (b - A x₀) = inner 𝕜 (W i) (b - A (y i)) := by
  intro i
  have hmem : A (y i - x₀) ∈ (Krylov.subspace A (b - A x₀) i.val).map A :=
    ⟨_, hy i, rfl⟩
  rw [residual_eq_sub_apply_sub A b x₀ (y i)]
  conv_rhs => rw [inner_sub_right]
  rw [Submodule.inner_left_of_mem_orthogonal hmem (hW i), sub_zero]

/-- **Section 5.10.1** of [liesen2013krylov]. Given a coefficient matrix $A$, basis blocks
$V_n,V_{n+1}$, and Hessenberg block $\underline H_{n,n}$, the **Arnoldi defect** is the matrix
$AV_n-V_{n+1}\underline H_{n,n}$. It vanishes when the Arnoldi relation holds exactly. -/
def computedArnoldiDefect {N n : ℕ} {𝕜 : Type*} [Ring 𝕜]
    (A : Matrix (Fin N) (Fin N) 𝕜) (V : Matrix (Fin N) (Fin n) 𝕜)
    (Vnext : Matrix (Fin N) (Fin (n + 1)) 𝕜) (H : Matrix (Fin (n + 1)) (Fin n) 𝕜) :
    Matrix (Fin N) (Fin n) 𝕜 :=
  A * V - Vnext * H

/-- **Section 5.10.2** of [liesen2013krylov]. For a computed basis matrix $V$, the
**orthogonality defect** is $I-V^*V$. It vanishes when the columns of $V$ are orthonormal.

**Generalization.** The matrix difference is defined over any star ring. -/
def computedOrthogonalityDefect {N n : ℕ} {𝕜 : Type*} [Ring 𝕜] [StarRing 𝕜]
    (V : Matrix (Fin N) (Fin n) 𝕜) : Matrix (Fin n) (Fin n) 𝕜 :=
  1 - V.conjTranspose * V

end LiesenStrakos.Chapter05
