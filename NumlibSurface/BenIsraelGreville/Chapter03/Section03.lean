/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.LinearAlgebra.Matrix.LeastSquares.Regularized

/-!
# Tikhonov regularization

Section 3.3 of [benIsrael2003generalized] penalizes the squared norm of a least-squares
solution. The unique regularized minimizer decreases in norm as the penalty increases
and converges to the minimum-norm least-squares solution as the penalty tends to zero.
-/

namespace BenIsraelGreville.Chapter03

open Matrix Filter
open scoped Topology

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- **Equation (37)** of [benIsrael2003generalized], Chapter 3. With penalty coefficient
$t=\alpha^2$, the Tikhonov objective is $\|Ax-b\|^2+t\|x\|^2$. -/
noncomputable def tikhonovObjective (A : Matrix m n ℂ) (b : EuclideanSpace ℂ m)
    (t : ℝ) (x : EuclideanSpace ℂ n) : ℝ :=
  ‖toEuclideanLin A x - b‖ ^ 2 + t * ‖x‖ ^ 2

variable [DecidableEq m]

/-- **Theorem 3** of [benIsrael2003generalized], Chapter 3. For each positive coefficient
$t$, the unique minimizer is $(A^H A+tI)^{-1}A^H b$. Its norm is antitone on $t>0$. -/
theorem theorem_3 (A : Matrix m n ℂ) (b : EuclideanSpace ℂ m) :
    (∀ t : ℝ, 0 < t → ∀ x : EuclideanSpace ℂ n,
      IsMinOn (tikhonovObjective A b t) Set.univ x ↔
        x = toEuclideanLin ((Aᴴ * A + (t : ℂ) • 1)⁻¹ * Aᴴ) b) ∧
    AntitoneOn (fun t : ℝ =>
      ‖toEuclideanLin ((Aᴴ * A + (t : ℂ) • 1)⁻¹ * Aᴴ) b‖) (Set.Ioi 0) := by
  have horder (t : ℝ) : A.tikhonov t = (Aᴴ * A + (t : ℂ) • 1)⁻¹ * Aᴴ := by
    exact congrArg (fun M : Matrix n n ℂ => M⁻¹ * Aᴴ)
      (add_comm ((t : ℂ) • (1 : Matrix n n ℂ)) (Aᴴ * A))
  constructor
  · intro t ht x
    rw [← horder]
    exact (Matrix.eq_toEuclideanLin_tikhonov_iff_isMinOn A ht b x).symm
  · simpa only [horder] using
      Matrix.antitoneOn_norm_toEuclideanLin_tikhonov A b

/-- **Exercise 25** of [benIsrael2003generalized], Chapter 3. As the positive coefficient
$t=\alpha^2$ tends to zero, the regularized solution converges to $A^\dagger b$. -/
theorem tendsto_tikhonov (A : Matrix m n ℂ) (b : EuclideanSpace ℂ m) :
    Tendsto (fun t : ℝ => toEuclideanLin (A.tikhonov t) b) (𝓝[>] 0)
      (𝓝 (toEuclideanLin A.pinv b)) := by
  let eval : Matrix n m ℂ →ₗ[ℂ] EuclideanSpace ℂ n :=
    ((LinearMap.applyₗ (R := ℂ) (M₂ := EuclideanSpace ℂ n)) b).comp toEuclideanLin.toLinearMap
  have hEval : Continuous eval := eval.continuous_of_finiteDimensional
  exact hEval.continuousAt.tendsto.comp A.tendsto_tikhonov_pinv

end BenIsraelGreville.Chapter03
