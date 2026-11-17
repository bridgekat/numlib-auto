/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Krylov.Convergence.Polynomial
import Numlib.Krylov.Iterate
import Numlib.Projection.OneDimensional
import Numlib.RingTheory.Polynomial.ChebyshevMinimax

/-!
# Chebyshev convergence bounds for Galerkin (CG) and minimal-residual iterates

Let $A$ be a symmetric operator on an inner product space with $\lambda_{\min} \|x\|^2 \le
\operatorname{Re} \langle Ax, x \rangle \le \lambda_{\max} \|x\|^2$ for all $x$ and
$0 < \lambda_{\min}$ (`LinearMap.IsSymmetricBoundedBy`). Let
$\kappa = \lambda_{\max} / \lambda_{\min}$ be the spectral condition number, let $T_m$ be the
Chebyshev polynomial of the first kind of degree $m$, and let $\|x\|_A = \sqrt{\operatorname{Re}
\langle Ax, x \rangle}$ be the energy norm. For *any* sequence of Galerkin iterates $x_m$ for
$Ax = b$ (CG, D-Lanczos, …), with exact solution $x^*$,
$$\|x^* - x_m\|_A \le \frac{\|x^* - x_0\|_A}{T_m\!\left(\frac{\lambda_{\max} +
  \lambda_{\min}}{\lambda_{\max} - \lambda_{\min}}\right)} \le 2 \left( \frac{\sqrt{\kappa} -
  1}{\sqrt{\kappa} + 1} \right)^m \|x^* - x_0\|_A.$$
This is Theorem 6.29 and (6.123)–(6.128) of [saad2003iterative], Theorem 5.6.1 of
[han2009theoretical], and (3.9) of [meurant2006lanczos]. The module also proves the analogue for the
residual norm of minimal-residual iterates, Theorem 6.30 of [saad2003iterative] (restarted
minimal-residual iterations converge for a coercive $A$), and the one-step Kantorovich contraction
$\|x^* - x_{m+1}\|_A \le \frac{\lambda_{\max} - \lambda_{\min}}{\lambda_{\max} + \lambda_{\min}}
\|x^* - x_m\|_A$ of (5.6.4) in [han2009theoretical], which compares a Galerkin step with a
steepest-descent step.

No finite dimension is assumed: the proofs go through the compression of $A$ to $\mathcal{K}_{m+1}$.
Only the sharp Chebyshev form needs a strict spectral gap $\lambda_{\min} < \lambda_{\max}$, because
it divides by $\lambda_{\max} - \lambda_{\min}$. The geometric forms hold for
$\lambda_{\min} \le \lambda_{\max}$. In the degenerate case $\lambda_{\min} = \lambda_{\max}$ the
operator $A$ is a scalar and the iterates are exact from step $1$.

## Main results

* `Krylov.IsGalerkinIterate.energyNorm_error_le_div_eval_T`: the sharp Chebyshev bound, (6.123) of
  [saad2003iterative].
* `Krylov.IsGalerkinIterate.energyNorm_error_le`: its geometric form, Theorem 6.29 and (6.128) of
  [saad2003iterative] and Theorem 5.6.1 of [han2009theoretical].
* `Krylov.IsMinResidualIterate.norm_residual_le`: the same geometric bound for the residual norm of
  minimal-residual iterates.
* `Krylov.IsGalerkinIterate.energyNorm_error_succ_le`: the one-step Kantorovich contraction, (5.6.4)
  of [han2009theoretical].
* `Krylov.sqrt_ratio_le_ratio`: the comparison $(\sqrt{\kappa} - 1)/(\sqrt{\kappa} + 1) \le
  (\kappa - 1)/(\kappa + 1)$ of the two rates, (5.6.6) of [han2009theoretical].
* `Krylov.IsMinResidualIterate.norm_residual_le_of_isCoerciveWith` and
  `Krylov.restarted_minRes_tendsto`: convergence of restarted minimal-residual iterations for a
  bounded coercive $A$, Theorem 6.30 of [saad2003iterative].
-/

open Polynomial Polynomial.Chebyshev Krylov

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {A : E →ₗ[𝕜] E} {b x₀ : E}

namespace Krylov

section Chebyshev

/-!
### The residual polynomial

`Polynomial.Chebyshev.shifted m lmin lmax 0` is the Chebyshev polynomial of
$[\lambda_{\min}, \lambda_{\max}]$ of degree $m$, normalized to $1$ at $0$. Its image in
$\mathbb{R}[X]$ or $\mathbb{C}[X]$ is the competitor polynomial of the optimality statements for
Galerkin and minimal-residual iterates.
-/

variable {lmin lmax : ℝ} (hl : 0 < lmin) (hll : lmin < lmax)

/-- If $0 < \lambda_{\min}$, then $0 \notin [\lambda_{\min}, \lambda_{\max}]$, so the shifted
Chebyshev polynomial can be normalized at $0$. -/
private theorem zero_notMem_Icc (h : 0 < lmin) : (0 : ℝ) ∉ Set.Icc lmin lmax := fun hmem =>
  absurd hmem.1 (not_le.mpr h)

include hl hll

private theorem one_le_ratio : 1 ≤ (lmax + lmin) / (lmax - lmin) := by
  rw [le_div_iff₀ (by linarith)]
  linarith

/-- For $0 < \lambda_{\min} < \lambda_{\max}$, the Chebyshev value $T_m((\lambda_{\max} +
\lambda_{\min})/(\lambda_{\max} - \lambda_{\min}))$ of (6.123) in [saad2003iterative] is at
least $1$, and in particular positive. -/
private theorem one_le_eval_T_ratio (m : ℕ) : 1 ≤ (T ℝ m).eval ((lmax + lmin) / (lmax - lmin)) :=
  one_le_eval_T (one_le_ratio hl hll) m

/-- For $0 < \lambda_{\min} < \lambda_{\max}$, the supremum of the absolute value of the shifted
Chebyshev polynomial over $[\lambda_{\min}, \lambda_{\max}]$ is $1 / T_m((\lambda_{\max} +
\lambda_{\min})/(\lambda_{\max} - \lambda_{\min}))$. -/
private theorem sSup_abs_eval_shifted_zero (m : ℕ) :
    sSup ((fun t => |(shifted m lmin lmax 0).eval t|) '' Set.Icc lmin lmax) =
      1 / (T ℝ m).eval ((lmax + lmin) / (lmax - lmin)) := by
  rw [sSup_abs_eval_shifted m hll (zero_notMem_Icc hl)]
  rw [show (lmax + lmin - 2 * 0) / (lmax - lmin) = (lmax + lmin) / (lmax - lmin) by ring_nf]
  rw [abs_of_pos (lt_of_lt_of_le zero_lt_one (one_le_eval_T_ratio hl hll m))]

/-- For $0 < \lambda_{\min} < \lambda_{\max}$, the supremum of the absolute value of the shifted
Chebyshev polynomial over $[\lambda_{\min}, \lambda_{\max}]$ is at most
$2((\sqrt{\kappa} - 1)/(\sqrt{\kappa} + 1))^m$ with $\kappa = \lambda_{\max} / \lambda_{\min}$,
as in (6.128) of [saad2003iterative]. -/
theorem sSup_abs_eval_shifted_le (m : ℕ) :
    sSup ((fun t => |(shifted m lmin lmax 0).eval t|) '' Set.Icc lmin lmax) ≤
      2 * ((Real.sqrt (lmax / lmin) - 1) / (Real.sqrt (lmax / lmin) + 1)) ^ m := by
  rw [sSup_abs_eval_shifted_zero hl hll]
  have hκ : 1 < lmax / lmin := (one_lt_div hl).2 hll
  have harg : (lmax / lmin + 1) / (lmax / lmin - 1) = (lmax + lmin) / (lmax - lmin) := by
    have h2 : lmax - lmin ≠ 0 := sub_ne_zero.mpr hll.ne'
    field_simp
  rw [← harg]
  exact one_div_eval_T_le_two_mul_pow hκ m

omit hl hll

/-- The shifted Chebyshev polynomial `Polynomial.Chebyshev.shifted m lmin lmax 0`, with its
coefficients mapped into the scalar field. -/
private noncomputable def chebPoly (𝕜 : Type*) [RCLike 𝕜] (m : ℕ) (lmin lmax : ℝ) : 𝕜[X] :=
  (shifted m lmin lmax 0).map (algebraMap ℝ 𝕜)

private theorem chebPoly_degree_le (m : ℕ) : (chebPoly 𝕜 m lmin lmax).degree ≤ m :=
  degree_map_le.trans (shifted_degree_le m lmin lmax 0)

include hl hll in
private theorem chebPoly_eval_zero (m : ℕ) : (chebPoly 𝕜 m lmin lmax).eval 0 = 1 := by
  rw [chebPoly, eval_zero_map, shifted_eval_self m hll (zero_notMem_Icc hl)]
  simp

end Chebyshev

section OneStep

/-!
### The one-step contraction

A Galerkin step is at least as good as a steepest-descent step from the previous iterate, because
the steepest-descent point lies in the next Krylov space.
-/

variable {lmin lmax : ℝ} (hl : 0 < lmin) (hA : A.IsSymmetricBoundedBy lmin lmax)
include hl hA

/-- Let $A$ be symmetric with $\lambda_{\min} \|x\|^2 \le \operatorname{Re} \langle Ax, x \rangle
\le \lambda_{\max} \|x\|^2$ for all $x$, where $0 < \lambda_{\min}$, and let $A x^* = b$. If $x$
is the Galerkin iterate for $Ax = b$ from $x_0$ at step $m$ and $y$ is the Galerkin iterate at
step $m + 1$, then one step contracts the energy norm of the error by the Kantorovich factor:
$$\|x^* - y\|_A \le \frac{\lambda_{\max} - \lambda_{\min}}{\lambda_{\max} + \lambda_{\min}}
  \|x^* - x\|_A.$$
This is (5.6.4) of [han2009theoretical], and it holds for any Galerkin iteration (CG, FOM,
D-Lanczos).

The Galerkin iterate over $\mathcal{K}_{m+1}$ minimizes the energy norm of the error there
(`IsGalerkin.energyNorm_le`). The steepest-descent point from $x$ is a competitor in the same
affine space, so the steepest-descent rate (Theorem 5.9 of [saad2003iterative], proved from
Kantorovich's inequality) applies. Together with `Krylov.sqrt_ratio_le_ratio`, this is the
weaker one-step form of the Chebyshev bound `Krylov.IsGalerkinIterate.energyNorm_error_le`, as
(5.6.4) compares with (5.6.5) in [han2009theoretical]. -/
theorem IsGalerkinIterate.energyNorm_error_succ_le {m : ℕ} {x y xstar : E}
    (hx : IsGalerkinIterate A b x₀ m x) (hy : IsGalerkinIterate A b x₀ (m + 1) y)
    (hstar : A xstar = b) :
    energyNorm A (xstar - y) ≤ (lmax - lmin) / (lmax + lmin) * energyNorm A (xstar - x) := by
  have hmem : Projection.steepestDescentStep A b x - x₀ ∈ subspace A (b - A x₀) (m + 1) := by
    have hsplit : Projection.steepestDescentStep A b x - x₀ = (x - x₀) +
        (inner 𝕜 (b - A x) (b - A x) / inner 𝕜 (b - A x) (A (b - A x))) • (b - A x) := by
      rw [Projection.steepestDescentStep, Projection.step1]
      abel
    rw [hsplit]
    exact Submodule.add_mem _ (subspace_mono A (b - A x₀) (Nat.le_succ m) hx.mem)
      (Submodule.smul_mem _ _ (residual_mem_subspace_succ hx.mem))
  exact (IsGalerkin.energyNorm_le (hA.isSymmetricCoercive hl) hy hstar hmem).trans
    (Projection.energyNorm_steepestDescentStep_le hl hA hstar x)

end OneStep

section StrictGap

variable {lmin lmax : ℝ} (hl : 0 < lmin) (hll : lmin < lmax) (hA : A.IsSymmetricBoundedBy lmin lmax)
include hl hll hA

/-- The **sharp Chebyshev bound** for Galerkin iterates. Let $A$ be symmetric with $\lambda_{\min}
\|x\|^2 \le \operatorname{Re} \langle Ax, x \rangle \le \lambda_{\max} \|x\|^2$ for all $x$,
where $0 < \lambda_{\min} < \lambda_{\max}$, and let $A x^* = b$. If $x_m$ is the Galerkin
iterate for $Ax = b$ from $x_0$ at step $m$, then
$$\|x^* - x_m\|_A \le \frac{\|x^* - x_0\|_A}{T_m\!\left(\frac{\lambda_{\max} +
  \lambda_{\min}}{\lambda_{\max} - \lambda_{\min}}\right)}.$$
This is (6.123) of [saad2003iterative].

Unlike the geometric bound `Krylov.IsGalerkinIterate.energyNorm_error_le`, this bound needs the
strict spectral gap $\lambda_{\min} < \lambda_{\max}$, because its right-hand side divides by
$\lambda_{\max} - \lambda_{\min}$. The polynomial $T_m$ is `Polynomial.Chebyshev.T ℝ m`. -/
theorem IsGalerkinIterate.energyNorm_error_le_div_eval_T {m : ℕ} {x xstar : E}
    (hx : IsGalerkinIterate A b x₀ m x) (hstar : A xstar = b) :
    energyNorm A (xstar - x) ≤
      energyNorm A (xstar - x₀) / (T ℝ m).eval ((lmax + lmin) / (lmax - lmin)) := by
  have h1 := Krylov.IsGalerkinIterate.energyNorm_error_le_energyNorm_aeval
    (hA.isSymmetricCoercive hl) hx hstar (chebPoly 𝕜 m lmin lmax) (chebPoly_degree_le m)
    (chebPoly_eval_zero hl hll m)
  have h2 := hA.energyNorm_aeval_map_apply_le hl (shifted m lmin lmax 0) (xstar - x₀)
  rw [sSup_abs_eval_shifted_zero hl hll] at h2
  rw [div_eq_inv_mul, ← one_div]
  exact h1.trans h2

end StrictGap

section Degenerate

/-!
### The degenerate spectral interval $\lambda_{\min} = \lambda_{\max}$

The hypothesis `A.IsSymmetricBoundedBy l l` says that the quadratic form of $A$ is exactly
$l \|x\|^2$. For a symmetric operator this forces $A = l I$
(`LinearMap.IsSymmetricBoundedBy.apply_eq_smul`). The solution then lies in $x_0 + \mathcal{K}_1$
already, so every Krylov iterate from step $1$ on is exact, and the geometric bounds below hold with
a right-hand side of $0$. This is why they need no strict spectral gap.
-/

variable {l : ℝ} (hl : 0 < l) (hA : A.IsSymmetricBoundedBy l l)
include hl hA

/-- Let $A$ be symmetric with quadratic form exactly $l \|x\|^2$, where $l > 0$, and let
$A x^* = b$. Then $A = l I$, so $x^* - x_0 \in \mathcal{K}_m(A, b - A x_0)$ for every $m \ge 1$. -/
theorem sub_mem_subspace_of_isSymmetricBoundedBy_self {xstar : E} (hstar : A xstar = b) {m : ℕ}
    (hm : 1 ≤ m) : xstar - x₀ ∈ subspace A (b - A x₀) m := by
  have hl0 : (l : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.2 hl.ne'
  have hres : b - A x₀ = (l : 𝕜) • (xstar - x₀) := by
    rw [← hstar, ← map_sub, hA.apply_eq_smul]
  have hsol : xstar - x₀ = (l : 𝕜)⁻¹ • (b - A x₀) := by
    rw [hres, smul_smul, inv_mul_cancel₀ hl0, one_smul]
  rw [hsol]
  exact Submodule.smul_mem _ _ (self_mem_subspace A (b - A x₀) hm)

/-- Let $A$ be symmetric with quadratic form exactly $l \|x\|^2$, where $l > 0$. Then $A = l I$ is
invertible, so the equation $A x^* = b$ has a solution. -/
theorem exists_apply_eq_of_isSymmetricBoundedBy_self : ∃ xstar : E, A xstar = b := by
  have hl0 : (l : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.2 hl.ne'
  exact ⟨(l : 𝕜)⁻¹ • b, by rw [hA.apply_eq_smul, smul_smul, mul_inv_cancel₀ hl0, one_smul]⟩

end Degenerate

section Symmetric

variable {lmin lmax : ℝ} (hl : 0 < lmin) (hll : lmin ≤ lmax) (hA : A.IsSymmetricBoundedBy lmin lmax)
include hl hll hA

/-- The **geometric Chebyshev bound** for Galerkin iterates. Let $A$ be symmetric with
$\lambda_{\min} \|x\|^2 \le \operatorname{Re} \langle Ax, x \rangle \le \lambda_{\max} \|x\|^2$
for all $x$, where $0 < \lambda_{\min} \le \lambda_{\max}$, let
$\kappa = \lambda_{\max} / \lambda_{\min}$, and let $A x^* = b$. If $x_m$ is the Galerkin
iterate for $Ax = b$ from $x_0$ at step $m$, then
$$\|x^* - x_m\|_A \le 2 \left( \frac{\sqrt{\kappa} - 1}{\sqrt{\kappa} + 1} \right)^m \|x^* -
  x_0\|_A.$$
This is Theorem 6.29 of [saad2003iterative] and (5.6.5) of [han2009theoretical].

No strict spectral gap is needed. When $\lambda_{\min} = \lambda_{\max}$, the operator is a
scalar (`Krylov.sub_mem_subspace_of_isSymmetricBoundedBy_self`), $\kappa = 1$ makes the factor
$0$, and the iterate is exact for $m \ge 1$. For $m = 0$ the bound reads
$\|x^* - x_0\|_A \le 2 \|x^* - x_0\|_A$. -/
theorem IsGalerkinIterate.energyNorm_error_le {m : ℕ} {x xstar : E}
    (hx : IsGalerkinIterate A b x₀ m x) (hstar : A xstar = b) :
    energyNorm A (xstar - x) ≤
      2 * ((Real.sqrt (lmax / lmin) - 1) / (Real.sqrt (lmax / lmin) + 1)) ^ m *
        energyNorm A (xstar - x₀) := by
  rcases hll.lt_or_eq with hlt | rfl
  · have h1 := Krylov.IsGalerkinIterate.energyNorm_error_le_energyNorm_aeval
      (hA.isSymmetricCoercive hl) hx hstar (chebPoly 𝕜 m lmin lmax) (chebPoly_degree_le m)
      (chebPoly_eval_zero hl hlt m)
    have h2 := hA.energyNorm_aeval_map_apply_le hl (shifted m lmin lmax 0) (xstar - x₀)
    exact h1.trans (h2.trans
      (mul_le_mul_of_nonneg_right (sSup_abs_eval_shifted_le hl hlt m) (Real.sqrt_nonneg _)))
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have hx0 : x = x₀ := by
      have h := hx.mem
      rw [subspace_zero, Submodule.mem_bot] at h
      exact sub_eq_zero.1 h
    rw [hx0, pow_zero, mul_one]
    linarith [energyNorm_nonneg A (xstar - x₀)]
  · have hzero : (Real.sqrt (lmin / lmin) - 1) / (Real.sqrt (lmin / lmin) + 1) = 0 := by
      rw [div_self hl.ne', Real.sqrt_one]
      norm_num
    rw [hzero, zero_pow hm.ne', mul_zero, zero_mul]
    refine le_trans (IsGalerkin.energyNorm_le (hA.isSymmetricCoercive hl) hx hstar
      (sub_mem_subspace_of_isSymmetricBoundedBy_self hl hA hstar hm)) ?_
    simp [energyNorm]

/-- The geometric Chebyshev bound for minimal-residual iterates. Let $A$ be symmetric with
$\lambda_{\min} \|x\|^2 \le \operatorname{Re} \langle Ax, x \rangle \le \lambda_{\max} \|x\|^2$
for all $x$, where $0 < \lambda_{\min} \le \lambda_{\max}$, and let
$\kappa = \lambda_{\max} / \lambda_{\min}$. If $x_m$ is a minimal-residual iterate for $Ax = b$
from $x_0$ at step $m$, then
$$\|b - A x_m\| \le 2 \left( \frac{\sqrt{\kappa} - 1}{\sqrt{\kappa} + 1} \right)^m \|b - A
  x_0\|.$$

As for `Krylov.IsGalerkinIterate.energyNorm_error_le`, no strict spectral gap is needed. -/
theorem IsMinResidualIterate.norm_residual_le {m : ℕ} {x : E}
    (hx : IsMinResidualIterate A b x₀ m x) :
    ‖b - A x‖ ≤
      2 * ((Real.sqrt (lmax / lmin) - 1) / (Real.sqrt (lmax / lmin) + 1)) ^ m * ‖b - A x₀‖ := by
  rcases hll.lt_or_eq with hlt | rfl
  · have h1 := Krylov.IsMinResidualIterate.norm_residual_le_norm_aeval hx (chebPoly 𝕜 m lmin lmax)
      (chebPoly_degree_le m) (chebPoly_eval_zero hl hlt m)
    have h2 := hA.norm_aeval_map_apply_le (shifted m lmin lmax 0) (b - A x₀)
    exact h1.trans (h2.trans
      (mul_le_mul_of_nonneg_right (sSup_abs_eval_shifted_le hl hlt m) (norm_nonneg _)))
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have hx0 : x = x₀ := by
      have h := hx.mem
      rw [subspace_zero, Submodule.mem_bot] at h
      exact sub_eq_zero.1 h
    rw [hx0, pow_zero, mul_one]
    linarith [norm_nonneg (b - A x₀)]
  · obtain ⟨xstar, hstar⟩ := exists_apply_eq_of_isSymmetricBoundedBy_self (b := b) hl hA
    have hzero : (Real.sqrt (lmin / lmin) - 1) / (Real.sqrt (lmin / lmin) + 1) = 0 := by
      rw [div_self hl.ne', Real.sqrt_one]
      norm_num
    rw [hzero, zero_pow hm.ne', mul_zero, zero_mul]
    have h := hx.min xstar (sub_mem_subspace_of_isSymmetricBoundedBy_self hl hA hstar hm)
    rwa [hstar, sub_self, norm_zero] at h

end Symmetric

/-- For $\kappa \ge 1$,
$$\frac{\sqrt{\kappa} - 1}{\sqrt{\kappa} + 1} \le \frac{\kappa - 1}{\kappa + 1}.$$
This compares the rate of the Chebyshev bound with the rate of the one-step contraction, as in
(5.6.6) of [han2009theoretical]. -/
theorem sqrt_ratio_le_ratio {κ : ℝ} (hκ : 1 ≤ κ) :
    (Real.sqrt κ - 1) / (Real.sqrt κ + 1) ≤ (κ - 1) / (κ + 1) := by
  have hs : 1 ≤ Real.sqrt κ := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hκ
  have hsq : Real.sqrt κ ^ 2 = κ := Real.sq_sqrt (by linarith)
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith [mul_nonneg (sub_nonneg.2 hs) (by linarith : (0 : ℝ) ≤ 2 * Real.sqrt κ)]

/-- One cycle of a restarted minimal-residual iteration contracts the residual. Let $A$ be a bounded
operator on an inner product space with $c \|x\|^2 \le \operatorname{Re} \langle Ax, x \rangle$
for all $x$, where $c > 0$, and let $m \ge 1$. If $x$ is a minimal-residual iterate for $Ax = b$
from $x_0$ at step $m$, then
$$\|b - Ax\| \le \sqrt{1 - c^2 / \|A\|^2} \, \|b - A x_0\|.$$
This is the contraction in the proof of Theorem 6.30 of [saad2003iterative].

The operator $A$ need not be symmetric, and no finite dimension is assumed. The operator $A$ is
a continuous linear map, and $\|A\|$ is its operator norm. -/
theorem IsMinResidualIterate.norm_residual_le_of_isCoerciveWith {A : E →L[𝕜] E} {c : ℝ} (hc : 0 < c)
    (hA : (A : E →ₗ[𝕜] E).IsCoerciveWith c) {b x₀ x : E} {m : ℕ} (hm : 1 ≤ m)
    (hx : IsMinResidualIterate (A : E →ₗ[𝕜] E) b x₀ m x) :
    ‖b - A x‖ ≤ Real.sqrt (1 - c ^ 2 / ‖A‖ ^ 2) * ‖b - A x₀‖ := by
  have hmem : Projection.minResStep (A : E →ₗ[𝕜] E) b x₀ - x₀ ∈
      subspace (A : E →ₗ[𝕜] E) (b - A x₀) m := by
    have : Projection.minResStep (A : E →ₗ[𝕜] E) b x₀ - x₀ =
        (inner 𝕜 ((A : E →ₗ[𝕜] E) (b - A x₀)) (b - A x₀) /
          inner 𝕜 ((A : E →ₗ[𝕜] E) (b - A x₀)) ((A : E →ₗ[𝕜] E) (b - A x₀))) • (b - A x₀) := by
      simp [Projection.minResStep, Projection.step1]
    rw [this]
    exact Submodule.smul_mem _ _ (self_mem_subspace _ _ hm)
  exact (hx.min _ hmem).trans (Projection.norm_residual_minResStep_le hc hA b x₀)

/-- **Restarted minimal-residual iteration converges** for a bounded coercive operator. Let $A$ be a
bounded operator on an inner product space with $c \|x\|^2 \le \operatorname{Re} \langle Ax, x
\rangle$ for all $x$, where $c > 0$, and let $m \ge 1$. Let $(x_k)$ be a sequence such that each
$x_{k+1}$ is a minimal-residual iterate for $Ax = b$ from $x_k$ at step $m$. Then
$$\|b - A x_k\| \to 0 \quad (k \to \infty).$$
This is Theorem 6.30 of [saad2003iterative].

Each cycle restarts from the output of the previous cycle and contracts the residual by the
factor $\sqrt{1 - c^2/\|A\|^2} < 1$ of
`Krylov.IsMinResidualIterate.norm_residual_le_of_isCoerciveWith`, so the residual norms tend to
$0$ geometrically. Coercivity alone is enough: it keeps $r$ and $Ar$ from becoming orthogonal,
so a single step of a cycle already reduces the residual by a fixed fraction. No spectral
hypothesis, no symmetry and no finite dimension are needed. -/
theorem restarted_minRes_tendsto {A : E →L[𝕜] E} {c : ℝ} (hc : 0 < c)
    (hA : (A : E →ₗ[𝕜] E).IsCoerciveWith c) {b : E} {m : ℕ} (hm : 1 ≤ m) (x : ℕ → E)
    (hx : ∀ k, IsMinResidualIterate (A : E →ₗ[𝕜] E) b (x k) m (x (k + 1))) :
    Filter.Tendsto (fun k => ‖b - A (x k)‖) Filter.atTop (nhds 0) := by
  rcases (norm_nonneg A).eq_or_lt with hA0 | hA0
  · -- `A = 0` forces `E = 0` by coercivity, so every residual vanishes.
    have hAz : A = 0 := by rwa [eq_comm, norm_eq_zero] at hA0
    have hzero : ∀ y : E, y = 0 := by
      intro y
      have h1 := hA y
      rw [hAz] at h1
      simp only [ContinuousLinearMap.toLinearMap_zero, LinearMap.zero_apply, inner_zero_left,
        map_zero] at h1
      rw [← norm_eq_zero]
      by_contra hne
      have hpos : 0 < ‖y‖ := lt_of_le_of_ne (norm_nonneg y) (Ne.symm hne)
      linarith [mul_pos hc (pow_pos hpos 2)]
    have : (fun k => ‖b - A (x k)‖) = fun _ : ℕ => (0 : ℝ) := by
      funext k
      rw [hzero b, hzero (x k)]
      simp
    rw [this]
    exact tendsto_const_nhds
  · set q := Real.sqrt (1 - c ^ 2 / ‖A‖ ^ 2) with hq
    have hq0 : 0 ≤ q := Real.sqrt_nonneg _
    have hq1 : q < 1 := by
      rw [hq, Real.sqrt_lt' one_pos]
      have : 0 < c ^ 2 / ‖A‖ ^ 2 := div_pos (pow_pos hc 2) (pow_pos hA0 2)
      nlinarith
    have hbound : ∀ k, ‖b - A (x k)‖ ≤ q ^ k * ‖b - A (x 0)‖ := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
          calc ‖b - A (x (k + 1))‖ ≤ q * ‖b - A (x k)‖ :=
                IsMinResidualIterate.norm_residual_le_of_isCoerciveWith hc hA hm (hx k)
            _ ≤ q * (q ^ k * ‖b - A (x 0)‖) := by gcongr
            _ = q ^ (k + 1) * ‖b - A (x 0)‖ := by ring
    refine squeeze_zero (fun k => norm_nonneg _) hbound ?_
    simpa using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const ‖b - A (x 0)‖

end Krylov
