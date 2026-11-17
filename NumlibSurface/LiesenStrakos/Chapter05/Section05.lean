/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Krylov.Convergence.CG
import Numlib.Preconditioner.Chebyshev
import Numlib.Stationary.Richardson

/-!
# Liesen and Strakoš, §5.5: Convergence of stationary and semi-iterative methods

The error of a stationary iteration evolves by powers of the iteration operator. Richardson
iteration uses a fixed step length, whereas Chebyshev semi-iteration applies a normalized
Chebyshev residual polynomial suited to the spectral interval of a positive definite system.

## Main results

* Theorem 5.5.1, `LiesenStrakos.Chapter05.theorem_5_5_1`: the relative energy error is at most twice
  the $n$-th power of the square-root condition-number factor.

## Deviations from the source

* **Theorem 5.5.1** (generalization). The spectral endpoints may be any positive bounds on the
  quadratic form, and the operator need not be finite dimensional.
-/

open Polynomial Polynomial.Chebyshev

namespace LiesenStrakos.Chapter05

/-- **Equation (5.5.1)** of [liesen2013krylov]. Given the true solution $x$ and approximations
$x_0$ and $x_n$, the **average reduction factor** at step $n$ is
$(\|x-x_n\|/\|x-x_0\|)^{1/n}$. Lean evaluates this as $1$ for $n=0$. For a zero initial error and
$n>0$, Lean evaluates the ratio as $0$. -/
noncomputable def stationaryErrorReductionFactor {E : Type*} [SeminormedAddCommGroup E]
    (x x₀ xn : E) (n : ℕ) : ℝ :=
  (‖x - xn‖ / ‖x - x₀‖) ^ (1 / (n : ℝ))

/-- **Section 5.5.1** of [liesen2013krylov]. For a continuous linear iteration operator $M$ on
an inner product space over $\mathbb R$ or $\mathbb C$, the **average rate** after $n$ iterations
is $-n^{-1}\log\|M^n\|$. The Lean expression is $0$ if $n=0$ or $\|M^n\|=0$. -/
noncomputable abbrev stationaryAverageConvergenceRate {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (M : E →L[𝕜] E) (n : ℕ) : ℝ :=
  Stationary.averageConvergenceRate M n

/-- **Section 5.5.1** of [liesen2013krylov]. For a complex continuous linear iteration operator
$M$, the **asymptotic rate of convergence** is $-\log\rho(M)$, where $\rho$ is the spectral radius.
The Lean expression is $0$ at $\rho(M)=0$. -/
noncomputable abbrev stationaryAsymptoticConvergenceRate {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] (M : E →L[ℂ] E) : ℝ :=
  Stationary.asymptoticConvergenceRate M

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Section 5.5.2** of [liesen2013krylov]. **Stationary Richardson iteration** with initial
approximation $x_0$ uses the constant step size $1/((\alpha+\beta)/2)$ for spectral endpoints
$\alpha,\beta$. At a zero midpoint the step size is $0$. -/
noncomputable abbrev stationaryRichardson (A : E →ₗ[ℝ] E) (b x₀ : E)
    (α β : ℝ) (n : ℕ) : E :=
  Richardson.iterate A 1 (fun _ => ((α + β) / 2)⁻¹) b x₀ n

/-- **Section 5.5.2** of [liesen2013krylov]. The **Chebyshev semi-iterative approximation**
starts at $x_0$ and uses the Chebyshev recurrence for a spectral interval $[\alpha,\beta]$.
For a singleton interval, its positive-index approximation is
$x_0+\alpha^{-1}(b-Ax_0)$. This equals the solution for a positive scalar operator. -/
noncomputable def chebyshevSemiIterate (A : E →ₗ[ℝ] E) (b x₀ : E) (α β : ℝ) (n : ℕ) : E :=
  if n = 0 then x₀
  else if α = β then x₀ + α⁻¹ • (b - A x₀)
  else (Preconditioner.Chebyshev.iterate A b x₀ ((β + α) / 2) ((β - α) / 2) n).x

/-- **Theorem 5.5.1** of [liesen2013krylov]. Let $A$ be a symmetric operator on a real inner product
space with quadratic form between $\alpha\|v\|^2$ and $\beta\|v\|^2$, where
$0<\alpha\le\beta$. For an exact solution $x$ of $Ax=b$ and the $n$-th Chebyshev semi-iterate $x_n$
from $x_0$, the relative energy error satisfies
$$\frac{\|x-x_n\|_A}{\|x-x_0\|_A}
 \le 2\biggl(\frac{\sqrt{\beta/\alpha}-1}{\sqrt{\beta/\alpha}+1}\biggr)^n.$$

**Generalization.** The source uses the extremal eigenvalues of a positive definite matrix. The
statement works for any positive spectral bounds of a symmetric operator. A zero initial error
gives a ratio of $0$ in Lean. -/
theorem theorem_5_5_1 {A : E →ₗ[ℝ] E} {α β : ℝ} (hA : A.IsSymmetricBoundedBy α β)
    (hα : 0 < α) (hαβ : α ≤ β) {b x x₀ : E} (hx : A x = b) (n : ℕ) :
    energyNorm A (x - chebyshevSemiIterate A b x₀ α β n) / energyNorm A (x - x₀) ≤
      2 * ((Real.sqrt (β / α) - 1) / (Real.sqrt (β / α) + 1)) ^ n := by
  have hq : 0 ≤ (Real.sqrt (β / α) - 1) / (Real.sqrt (β / α) + 1) := by
    have hκ : 1 ≤ β / α := (one_le_div hα).2 hαβ
    have hs : 1 ≤ Real.sqrt (β / α) := by simpa using Real.sqrt_le_sqrt hκ
    exact div_nonneg (sub_nonneg.2 hs) (by positivity)
  rcases eq_or_ne (energyNorm A (x - x₀)) 0 with hz | hz
  · rw [hz, div_zero]
    positivity
  have he : 0 < energyNorm A (x - x₀) := lt_of_le_of_ne (energyNorm_nonneg _ _) hz.symm
  rw [div_le_iff₀ he]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [chebyshevSemiIterate, ↓reduceIte, pow_zero, mul_one]
    linarith
  rcases hαβ.lt_or_eq with hab | rfl
  · let y := (Preconditioner.Chebyshev.iterate A b x₀ ((β + α) / 2) ((β - α) / 2) n).x
    have hr :
        b - A y = aeval A ((shifted n α β 0).map (algebraMap ℝ ℝ)) (b - A x₀) := by
      dsimp only [y]
      rw [← Preconditioner.Chebyshev.residual_eq]
      exact Preconditioner.Chebyshev.residual_iterate_eq (A := A) (b := b) (x₀ := x₀) hα hab n
    rw [chebyshevSemiIterate, ite_eq_right hn.ne', ite_eq_right hab.ne]
    change energyNorm A (x - y) ≤ _
    rw [Krylov.error_eq_aeval_of_injective (hA.isSymmetricCoercive hα).isCoercive.injective hx hr]
    exact (hA.energyNorm_aeval_map_apply_le hα (shifted n α β 0) (x - x₀)).trans
      (mul_le_mul_of_nonneg_right (Krylov.sSup_abs_eval_shifted_le hα hab n)
        (energyNorm_nonneg _ _))
  · have hres : b - A x₀ = α • (x - x₀) := by
      rw [← hx, ← map_sub, hA.apply_eq_smul]
      rfl
    have hsolve : x = x₀ + α⁻¹ • (b - A x₀) := by
      rw [hres, smul_smul, inv_mul_cancel₀ hα.ne', one_smul]
      abel
    rw [chebyshevSemiIterate, ite_eq_right hn.ne', ite_eq_left rfl, ← hsolve, sub_self]
    have hzero : energyNorm A 0 = 0 := by simp [energyNorm]
    rw [hzero]
    positivity

end LiesenStrakos.Chapter05
