import Mathlib.Analysis.InnerProductSpace.Adjoint
import Numlib.Krylov.NormalEquations

/-!
# Linear least-squares problems

Section 5.3 of [conn2000trust].
-/

namespace ConnGouldToint.Chapter05

open Krylov

/-- Theorem 5.3.1. Applying conjugate gradients to the normal equations
`A A* y = A g` from a point in the range of `A` keeps every iterate in that range. -/
theorem theorem_5_3_1 {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (A : E →L[ℝ] F) (g : E) {y₀ : F} (hy₀ : y₀ ∈ LinearMap.range A.toLinearMap)
    (k : ℕ) :
    (CG.iterate (A.toLinearMap ∘ₗ A.adjoint.toLinearMap) (A g) y₀ k).x ∈
      LinearMap.range A.toLinearMap := by
  let H := A.toLinearMap ∘ₗ A.adjoint.toLinearMap
  have happly (y : F) : H y ∈ LinearMap.range A.toLinearMap := ⟨A.adjoint y, rfl⟩
  have hinv : LinearMap.range A.toLinearMap ∈ Module.End.invtSubmodule H :=
    (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem H).2 fun y _ => happly y
  have hr : A g - H y₀ ∈ LinearMap.range A.toLinearMap :=
    Submodule.sub_mem _ ⟨g, rfl⟩ (happly y₀)
  have hsub := ((subspace_le_fullSubspace H (A g - H y₀) k).trans
    (fullSubspace_le_of_mem_invtSubmodule H (A g - H y₀) hinv hr))
    (CG.iterate_sub_mem (A := H) (A g) y₀ k)
  exact (Submodule.sub_mem_iff_left _ hy₀).mp hsub


open scoped RealInnerProductSpace

/-- Algorithm 5.3.1 is CGNR on the transposed least-squares system. Its
residual is the negative of the CGNR residual, as in the printed recurrences.
The iterate and search direction are those of CG on the normal equations. -/
theorem algorithm_5_3_1 {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (A : E →L[ℝ] F) (g : E) (y₀ : F) (k : ℕ) :
    let s := CGNR.iterate A.adjoint.toLinearMap A.toLinearMap g y₀
    let r (j : ℕ) := -(s j).r
    let p (j : ℕ) := (s j).p
    let y (j : ℕ) := (s j).x
    let H := A.toLinearMap ∘ₗ A.adjoint.toLinearMap
    let q := A.adjoint (p k)
    let α := ‖A (r k)‖ ^ 2 / ‖q‖ ^ 2
    let β := ‖A (r (k + 1))‖ ^ 2 / ‖A (r k)‖ ^ 2
    y 0 = y₀ ∧ r 0 = A.adjoint y₀ - g ∧ p 0 = -A (r 0) ∧
      y (k + 1) = y k + α • p k ∧
      r (k + 1) = r k + α • q ∧
      p (k + 1) = -A (r (k + 1)) + β • p k ∧
      y k = (CG.iterate H (A g) y₀ k).x ∧
      -A (r k) = (CG.iterate H (A g) y₀ k).r ∧
      p k = (CG.iterate H (A g) y₀ k).p := by
  intro s r p y H q α β
  have ht : CGNR.step A.adjoint.toLinearMap A.toLinearMap (s k) = s (k + 1) :=
    (CGNR.iterate_succ A.adjoint.toLinearMap A.toLinearMap g y₀ k).symm
  have ha : CGNR.alpha A.adjoint.toLinearMap A.toLinearMap (s k) = α := by
    simp [CGNR.alpha, α, r, q, p]
  have hb : CGNR.beta A.adjoint.toLinearMap A.toLinearMap (s k) = β := by
    simp [CGNR.beta, β, r, ht]
  have hadj := A.adjoint.isAdjointPair_inner
  rw [ContinuousLinearMap.adjoint_adjoint] at hadj
  obtain ⟨hx, hr, hp, _⟩ :=
    CGNR.iterate_eq A.adjoint.toLinearMap A.toLinearMap g y₀ hadj k
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, hx, ?_, hp⟩
  · change -(g - A.adjoint y₀) = A.adjoint y₀ - g
    abel
  · change A (g - A.adjoint y₀) = -A (-(g - A.adjoint y₀))
    simp
  · change (s (k + 1)).x = (s k).x + α • (s k).p
    rw [← ht, CGNR.step_x, ha]
  · change -(s (k + 1)).r = -(s k).r + α • A.adjoint (s k).p
    rw [← ht, CGNR.step_r, ha, neg_sub]
    change α • A.adjoint (s k).p - (s k).r = _
    abel
  · change (s (k + 1)).p = -A (-(s (k + 1)).r) + β • (s k).p
    rw [← ht, CGNR.step_p, hb]
    simp
  · simpa [r] using hr

end ConnGouldToint.Chapter05
