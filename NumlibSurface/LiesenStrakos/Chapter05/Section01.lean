/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.InnerProductSpace.Energy
import Numlib.Conditioning.LinearSystem
import Numlib.Conditioning.LinearSystem.Componentwise

/-!
# Liesen and Strakoš, §5.1: Seeing the context is essential

For an approximate solution in a Galerkin trial space, the energy error separates into
orthogonal discretisation and algebraic contributions. Backward errors measure the effects
of perturbations of the discrete linear system.
-/

namespace LiesenStrakos.Chapter05

/-- **Section 5.1** of [liesen2013krylov], Galerkin error decomposition. Let $A$ be a symmetric
coercive operator on a real inner product space, $u$ the exact solution, $u_h$ its exact Galerkin
approximation, and $\tilde u_h$ an algebraic approximation in the Galerkin space. If the
discretisation error $u-u_h$ is $A$-orthogonal to the algebraic error $u_h-\tilde u_h$, then
$$\|u-\tilde u_h\|_A^2=\|u-u_h\|_A^2+\|u_h-\tilde u_h\|_A^2.$$ -/
theorem poisson_error_sq_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {A : E →ₗ[ℝ] E} (hA : A.IsSymmetricCoercive) (u uh uhn : E)
    (horth : inner ℝ (A (u - uh)) (uh - uhn) = 0) :
    energyNorm A (u - uhn) ^ 2 = energyNorm A (u - uh) ^ 2 + energyNorm A (uh - uhn) ^ 2 := by
  have horth' : inner ℝ (A (uh - uhn)) (u - uh) = 0 := by
    rw [hA.isSymmetric, real_inner_comm, horth]
  rw [hA.energyNorm_sq, hA.energyNorm_sq, hA.energyNorm_sq]
  have hexp : u - uhn = (u - uh) + (uh - uhn) := by abel
  conv_lhs =>
    rw [hexp, map_add, inner_add_left, inner_add_right, inner_add_right, horth, horth']
  simp

/-- **Equation (5.1.3)** of [liesen2013krylov]. For a real linear system $Ax=b$ and an approximate
solution $x_n$, the **normwise backward error** is $\|b-Ax_n\|/(\|b\|+\|A\|\|x_n\|)$, with the
induced operator norm on $A$. When its denominator is zero, this expression has value $0$. -/
noncomputable abbrev poisson_normwise_backward_error {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (A : E →L[ℝ] E) (b xn : E) : ℝ :=
  backwardError A b xn 1 1

/-- **Equation (5.1.7)** of [liesen2013krylov]. For a square real matrix $A$ and vectors $b,x_n$,
the **componentwise backward error** is
$$\max_i\frac{|(b-Ax_n)_i|}{(|A|\,|x_n|+|b|)_i}.$$
Absolute value is applied entrywise. A term with zero denominator is represented by $0$ and
the empty supremum is also $0$. The perturbation interpretation requires any
zero-denominator row to have zero residual. -/
noncomputable abbrev poisson_componentwise_backward_error {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℝ) (b xn : Fin N → ℝ) : ℝ :=
  A.componentwiseBackwardError A b b xn

end LiesenStrakos.Chapter05
