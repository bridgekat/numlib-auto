/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Conditioning.LinearSystem

/-!
# Liesen and Strakoš, §5.8: Rounding errors and backward stability

For a fixed approximate solution, the relative normwise backward error measures the least
simultaneous perturbation to the operator and right-hand side. If only the right-hand side is
perturbed, the relative residual norm is the corresponding perturbation size.
-/

namespace LiesenStrakos.Chapter05

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- **Section 5.8.3** of [liesen2013krylov]. The **relative normwise backward error** of $y$
for $Ax=b$ is the ratio $\|b-Ay\|/(\|A\|\|y\|+\|b\|)$, with the operator norm on $A$. A zero
denominator gives value zero. -/
noncomputable abbrev relativeNormwiseBackwardError (A : E →L[𝕜] E) (b y : E) : ℝ :=
  backwardError A b y 1 1

/-- **Equation (5.8.17)** of [liesen2013krylov], minimality. If $\|A\|\|y\|+\|b\|>0$, then
the relative normwise backward error is the least $\xi$ for which $(A+\Delta A)y=b+\Delta b$
for a bounded operator $\Delta A$ and a vector $\Delta b$ with
$\|\Delta A\|\le \xi\|A\|$ and $\|\Delta b\|\le \xi\|b\|$. -/
theorem relativeNormwiseBackwardError_isLeast (A : E →L[𝕜] E) (b y : E)
    (hpos : 0 < ‖A‖ * ‖y‖ + ‖b‖) :
    IsLeast {ξ : ℝ | ∃ (ΔA : E →L[𝕜] E) (Δb : E), (A + ΔA) y = b + Δb ∧
      ‖ΔA‖ ≤ ξ * ‖A‖ ∧ ‖Δb‖ ≤ ξ * ‖b‖} (relativeNormwiseBackwardError A b y) := by
  simpa only [one_mul, mul_one] using
    isLeast_backwardError A b y zero_le_one zero_le_one (by simpa only [one_mul] using hpos)

/-- **Equation (5.8.15)** of [liesen2013krylov]. If $A$ is an invertible bounded operator,
$Ax=b \ne 0$, and $y$ is an approximate solution, then
$$\frac{\|x-y\|}{\|x\|}\le\kappa(A)\frac{\|b-Ay\|}{\|b\|}.$$ -/
theorem relativeError_le_cond_mul_relativeResidual (A : E ≃L[𝕜] E) {b x y : E}
    (hx : A x = b) (hb : b ≠ 0) :
    ‖x - y‖ / ‖x‖ ≤ NormedRing.condNumber (A : E →L[𝕜] E) * (‖b - A y‖ / ‖b‖) :=
  relative_error_le_condNumber_mul_relative_residual A hx hb

/-- **Equation (5.8.16)** of [liesen2013krylov]. For real $A,b,x_p$, the **Hegedüs scaling** of a
preliminary approximation $x_p$ uses the coefficient $(b^TAx_p)/\|Ax_p\|^2$. Its value is $0$
when $Ax_p=0$. -/
noncomputable def hegedusScale {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (A : F →ₗ[ℝ] F) (b xp : F) : ℝ :=
  inner ℝ b (A xp) / ‖A xp‖ ^ 2

end LiesenStrakos.Chapter05
