/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Numlib.Krylov.NormalEquations

/-!
# Conn, Gould and Toint, Section 5.3: Linear least-squares problems

This module formalizes Section 5.3 of [conn2000trust]. Let $A : E \to F$ be a bounded linear
operator between real Hilbert spaces, and let $g \in E$. The linear least-squares problem
$\min_y \|A^* y - g\|$ has the normal equations $AA^* y = Ag$. Algorithm 5.3.1 applies the conjugate
gradient method to these equations without forming $AA^*$, and Theorem 5.3.1 shows that the iterates
stay in the range of $A$ when the starting point does.

The proofs specialize the CGNR method of the backbone module `Numlib.Krylov.NormalEquations`.

## Main results

* Theorem 5.3.1, `ConnGouldToint.Chapter05.theorem_5_3_1`: conjugate gradients on $AA^* y = Ag$ from
  a point of the range of $A$ keep every iterate in that range.
* Algorithm 5.3.1, `ConnGouldToint.Chapter05.algorithm_5_3_1`: the recurrences of the algorithm, and
  their agreement with conjugate gradients on the normal equations.

## Conventions

* The backbone states carry the residual $b - Ax$ of the system that they solve. The residual
  $r_k = A^* y_k - g$ of Algorithm 5.3.1 is the negative of the CGNR residual.
-/

namespace ConnGouldToint.Chapter05

open Krylov

/-- **Theorem 5.3.1** of [conn2000trust]. Let $E$ and $F$ be real Hilbert spaces, let $A : E \to F$
be a bounded linear operator, and let $g \in E$. Let $y_k$ be the iterates of the conjugate
gradient method for the normal equations
$$AA^* y = Ag$$
from a starting point $y_0$ in the range of $A$. Then every $y_k$ lies in the range of $A$.

The iterates are `Krylov.CG.iterate` for the operator $AA^*$ and the right-hand side $Ag$. -/
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

/-- **Algorithm 5.3.1** of [conn2000trust]. Let $E$ and $F$ be real Hilbert spaces, let
$A : E \to F$ be a bounded linear operator, and let $g \in E$ and $y_0 \in F$. Let $y_k$, $r_k$
and $p_k$ be the iterates, residuals and directions of CGNR for the system $A^* y = g$ from
$y_0$, with the residual negated, so that $r_k = A^* y_k - g$. Then, with
$$q_k = A^* p_k, \qquad \alpha_k = \frac{\|A r_k\|^2}{\|q_k\|^2}, \qquad \beta_k = \frac{\|A
  r_{k+1}\|^2}{\|A r_k\|^2},$$
the recurrences of the algorithm hold:
$$r_0 = A^* y_0 - g, \qquad p_0 = -A r_0,$$
$$y_{k+1} = y_k + \alpha_k p_k, \qquad r_{k+1} = r_k + \alpha_k q_k, \qquad p_{k+1} = -A
  r_{k+1} + \beta_k p_k.$$
Moreover, $y_k$, $-A r_k$ and $p_k$ are the iterate, the residual and the direction of the
conjugate gradient method for $AA^* y = Ag$ from $y_0$.

The CGNR states are `Krylov.CGNR.iterate` for the operator $A^*$ with adjoint $A$, and the
conjugate gradient states are `Krylov.CG.iterate`. The divisions use Lean's convention
$a / 0 = 0$. -/
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
