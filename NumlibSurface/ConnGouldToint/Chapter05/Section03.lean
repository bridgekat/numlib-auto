import Mathlib.Analysis.InnerProductSpace.Adjoint
import Numlib.Krylov.CG

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

end ConnGouldToint.Chapter05
