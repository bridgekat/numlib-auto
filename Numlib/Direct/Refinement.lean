/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.FloatingPoint.LU
import Numlib.FloatingPoint.Stationary
import Numlib.Stationary.Basic

/-!
# Iterative refinement and scaling

This module formalizes the devices of [quarteroni2000numerical], §3.12, that improve the accuracy of
a direct solve of $Ax = b$. **Iterative refinement** with an approximate inverse $C$ repeats the
step $x \mapsto x + C(b - Ax)$: compute the residual, solve for a correction, and update. In exact
arithmetic this is the stationary iteration with the iteration operator $I - CA$. So the error after
$k$ steps is $(I - CA)^k (x_0 - x^*)$, the error contracts by the factor $\|I - CA\|$ in each step,
and one step is exact when $CA = I$. On a finite-dimensional complex space with $C$ onto, refinement
converges for every right-hand side and every start if and only if $\rho(I - CA) < 1$. **Scaling**
replaces $Ax = b$ by $(D_1 A D_2) y = D_1 b$ with $y = D_2^{-1} x$ (§3.12.1).

The rounding-error analysis follows [higham2002accuracy], §12.1. A computed refinement step has
three errors: the residual error $\xi$, the backward error $\Delta A$ of the solve, and the error
$\eta$ of the update. They satisfy the exact identity $(A + \Delta A)(x - \hat y) = \Delta A (x -
\hat x) - \xi - (A + \Delta A) \eta$. In the $\infty$-norm this gives the recursion $\|x - \hat
y\|_\infty \le \rho \|x - \hat x\|_\infty + \varphi$ with explicit $\rho$ and $\varphi$, and
iterating it gives the contraction by $\rho$ down to the limiting accuracy $\varphi / (1 - \rho)$.
This is the rigorous form of Theorems 12.1–12.2 of [higham2002accuracy], which
[quarteroni2000numerical], §3.12.2, quotes as $\rho \simeq 2n \operatorname{cond}(A, x) u$ in fixed
precision and $\rho \simeq u$ in mixed precision.

## Main definitions

* `Refinement.step`: one step $x \mapsto x + C(b - Ax)$ of iterative refinement with an approximate
  inverse $C$.
* `Refinement.RoundsStepLU`: one computed refinement step with computed LU factors, in fixed
  precision.
* `Refinement.RoundsStepLUMixed`: the same step with the residual computed in a finer precision.

## Main results

* `Refinement.step_eq_stationary_step`: refinement is the stationary iteration with the iteration
  operator $I - CA$ and the constant $Cb$.
* `Refinement.step_eq_of_eq_inverse`: if $CA = I$, one step from any start gives the solution.
* `Refinement.iterate_sub_eq`, `Refinement.norm_iterate_sub_le`: the error after $k$ steps is
  $(I - CA)^k (x_0 - x^*)$, and its norm is at most $\|I - CA\|^k \|x_0 - x^*\|$.
* `Refinement.forall_tendsto_iff_spectralRadius_lt_one`: on a finite-dimensional complex space with
  $C$ onto, refinement converges for every $b$ and every start if and only if $\rho(I - CA) < 1$.
* `Refinement.step_error`: the error identity of one computed step.
* `Refinement.norm_step_error_le`: the $\infty$-norm form of the error identity.
* `Refinement.step_error_fp`: in the rounding model, the three errors are bounded by
  $\gamma_{3n} |L| |U|$, $\gamma_{n+1} (|A| |\hat x| + |b|)$ and $u |\hat x + \hat z|$.
* `Refinement.norm_step_error_le_of_abs_le`: the one-step recursion of [higham2002accuracy] (12.5)
  in the $\infty$-norm, for any solver with $|\Delta A| \le \gamma W$.
* `Refinement.norm_sub_le_of_roundsStepLU`, `Refinement.norm_sub_le_of_roundsStepLUMixed`: one step
  of [higham2002accuracy] Theorems 12.2 and 12.1.
* `Refinement.norm_sub_le_of_forall_roundsStepLU`,
  `Refinement.norm_sub_le_of_forall_roundsStepLUMixed`: [higham2002accuracy] Theorems 12.2 and 12.1,
  with the limiting accuracy $\varphi / (1 - \rho)$.
* `Matrix.scaled_mulVec_eq_iff`: $Ax = b$ if and only if $(D_1 A D_2)(D_2^{-1} x) = D_1 b$.

## Notation

* $u$: the unit roundoff of a rounding model `FloatingPoint.RoundingModel`, and
  $\gamma_k = ku / (1 - ku)$ (`FloatingPoint.gamma`). In mixed precision, $\bar u$ and
  $\bar\gamma_k$ are those of the finer model.
* $|A|$ and $|x|$: the matrix and the vector of the absolute values of the entries. Inequalities
  between matrices or vectors hold entry by entry.
* $\operatorname{cond}(A) = \| |A^{-1}| \, |A| \|_\infty$, the Skeel condition number, and
  $\operatorname{cond}(A, x) = \| |A^{-1}| \, |A| \, |x| \|_\infty / \|x\|_\infty$.

## Implementation notes

* The exact-arithmetic results are stated for continuous linear maps $C, A : E \to E$ of a normed
  space where possible. In practice $C$ is the LU solve as a linear map. The rounding-error analysis
  and scaling are stated for matrices; the rounding-error analysis is over $\mathbb{R}$, because the
  rounding models of `Numlib.FloatingPoint.Model` are.
* The iteration operator is `1 - C * A`, and the stationary iteration is `Stationary.step` of
  `Numlib.Stationary.Basic`. The quantity $\|I - CA\|$ is the $\|R\|$ of Property 3.1 of
  [quarteroni2000numerical] with the factors in the other order.
* The norms in the rounding-error analysis are the $\infty$-norm on `Fin n → ℝ` and the operator
  norm that it induces on matrices, from `Matrix.Norms.Operator`.
* The condition estimate of [quarteroni2000numerical], §3.11, is in
  `Numlib.Direct.ConditionEstimation`.
-/

open Filter Topology

/-! ### Iterative refinement -/

namespace Refinement

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- **One step of iterative refinement** with the approximate inverse $C$
([quarteroni2000numerical], §3.12.2, steps 1–3). For continuous linear maps $C, A : E \to E$ and
$b, x \in E$, compute the residual $b - Ax$, solve for the correction with $C$, and update:
$$x \mapsto x + C(b - Ax).$$
-/
def step (C A : E →L[𝕜] E) (b x : E) : E := x + C (b - A x)

variable (C A : E →L[𝕜] E) (b : E)

/-- Iterative refinement is the stationary iteration $x \mapsto (I - CA) x + Cb$, with the iteration
operator $I - CA$ and the constant $Cb$. -/
theorem step_eq_stationary_step : step C A b = Stationary.step (1 - C * A) (C b) := by
  funext x
  simp only [step, Stationary.step, sub_apply, one_apply_eq_self, mul_apply_eq_comp, map_sub]
  abel

variable {C A b}

/-- **Exact arithmetic stops after one step**. Let $C, A : E \to E$ be continuous linear maps with
$CA = I$, for example $C = A^{-1}$, and let $Ax^* = b$. Then one refinement step from any
$x \in E$ gives $x^*$.

This is the book's remark "in absence of rounding errors, the process would stop at the first
step". -/
theorem step_eq_of_eq_inverse (hCA : C * A = 1) {xs : E} (hxs : A xs = b) (x : E) :
    step C A b x = xs := by
  have h : C (A (xs - x)) = xs - x := by
    change (C * A) (xs - x) = xs - x
    rw [hCA, one_apply_eq_self]
  rw [step, ← hxs, ← map_sub, h]
  abel

/-- **Error propagation**. Let $C, A : E \to E$ be continuous linear maps, and let $Ax^* = b$. Then
for every start $x_0$ and every $k$, the $k$-th refinement iterate $x_k$ satisfies
$$x_k - x^* = (I - CA)^k (x_0 - x^*).$$
-/
theorem iterate_sub_eq {xs : E} (hxs : A xs = b) (x₀ : E) (k : ℕ) :
    (step C A b)^[k] x₀ - xs = ((1 - C * A) ^ k) (x₀ - xs) := by
  rw [step_eq_stationary_step]
  refine Stationary.step_iterate_sub (1 - C * A) (C b) ?_ x₀ k
  rw [sub_apply, one_apply_eq_self]
  change xs - C (A xs) + C b = xs
  rw [hxs]
  abel

/-- **Linear convergence of iterative refinement**. Let $C, A : E \to E$ be continuous linear maps,
and let $Ax^* = b$. Then for every start $x_0$ and every $k$, the $k$-th refinement iterate
$x_k$ satisfies
$$\|x_k - x^*\| \le \|I - CA\|^k \, \|x_0 - x^*\|.$$
So the iteration converges from every start when $\|I - CA\| < 1$.

Bounds of the type $\|I - CA\| \le \|C\| \, \|A - C^{-1}\|$ relate this to the backward a priori
analysis of [quarteroni2000numerical], Property 3.1. -/
theorem norm_iterate_sub_le {xs : E} (hxs : A xs = b) (x₀ : E) (k : ℕ) :
    ‖(step C A b)^[k] x₀ - xs‖ ≤ ‖1 - C * A‖ ^ k * ‖x₀ - xs‖ := by
  rw [iterate_sub_eq hxs x₀ k]
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right (ContinuousLinearMap.norm_pow_le_pow_norm _ k) (norm_nonneg _))

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- **Convergence of iterative refinement if and only if $\rho(I - CA) < 1$**
([quarteroni2000numerical], §3.12.2, through [saad2003iterative], Theorem 4.1). Let $F$ be a
finite-dimensional complex normed space, and let $C, A : F \to F$ be continuous linear maps with
$C$ onto. Then the refinement iterates converge for every right-hand side $b$ and every start
$x_0$ if and only if the spectral radius of $I - CA$ is less than $1$.

The LU solve is onto. The "only if" needs $C$ onto: for $C = 0$ the iteration is constant, so it
converges, but $\rho(I - 0) = 1$. -/
theorem forall_tendsto_iff_spectralRadius_lt_one [FiniteDimensional ℂ F] {C A : F →L[ℂ] F}
    (hC : Function.Surjective C) :
    (∀ b x₀, ∃ x, Tendsto (fun k => (step C A b)^[k] x₀) atTop (𝓝 x)) ↔
      spectralRadius ℂ (1 - C * A) < 1 := by
  rw [← Stationary.forall_tendsto_iff_spectralRadius_lt_one]
  constructor
  · intro h f x₀
    obtain ⟨b, rfl⟩ := hC f
    rw [← step_eq_stationary_step]
    exact h b x₀
  · intro h b x₀
    rw [step_eq_stationary_step]
    exact h (C b) x₀

end Refinement

/-!
### Iterative refinement on real matrices

This section gives the matrix form $x \mapsto x + C(b - Ax)$ of `Refinement.step` for real square
matrices: its error recursion, and the convergence criterion $\rho(I - CA) < 1$ with the complex
spectral radius of `Numlib.LinearAlgebra.Matrix.Complexify`. Unlike
`Refinement.forall_tendsto_iff_spectralRadius_lt_one`, the criterion needs no surjectivity of $C$,
because the convergence asked for is to one limit independent of the start.
-/

namespace Refinement

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Error propagation for the matrix refinement step** ([quarteroni2000numerical], §3.12.2). Let
$C, A \in \mathbb{R}^{n \times n}$, and let $Ax^* = b$. Then for every start $x^{(0)}$ and every
$k$, the iterates of $x \mapsto x + C(b - Ax)$ satisfy
$$x^{(k)} - x^* = (I - CA)^k (x^{(0)} - x^*).$$
-/
theorem iterate_sub_eq_mulVec (C A : Matrix ι ι ℝ) {b xs : ι → ℝ} (hxs : A *ᵥ xs = b)
    (x₀ : ι → ℝ) (k : ℕ) :
    (fun x => x + C *ᵥ (b - A *ᵥ x))^[k] x₀ - xs = ((1 - C * A) ^ k) *ᵥ (x₀ - xs) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', pow_succ', ← mulVec_mulVec, ← ih]
    generalize (fun x => x + C *ᵥ (b - A *ᵥ x))^[k] x₀ = y
    rw [← hxs]
    simp only [sub_mulVec, one_mulVec, ← mulVec_mulVec, mulVec_sub]
    abel

/-- **Convergence of iterative refinement if and only if $\rho(I - CA) < 1$**
([quarteroni2000numerical], §3.12.2, with Theorem 1.5). Let $C, A \in \mathbb{R}^{n \times n}$.
Then the following are equivalent:

* for every $b \in \mathbb{R}^n$ there is an $x$ such that the iterates of
  $x \mapsto x + C(b - Ax)$ converge to $x$ from every start;
* the spectral radius of $I - CA$, computed over $\mathbb{C}$, is less than $1$.

The spectral radius is `Matrix.complexSpectralRadius`. For the "only if", take $b = 0$ and
compare the iterates from $v$ and from $0$, whose difference is $(I - CA)^k v$. For the "if",
$CA$ and hence $A$ are nonsingular, and the limit is $A^{-1} b$. -/
theorem forall_exists_forall_tendsto_iff_complexSpectralRadius_lt_one (C A : Matrix ι ι ℝ) :
    (∀ b : ι → ℝ, ∃ x, ∀ x₀,
        Tendsto (fun k => (fun x => x + C *ᵥ (b - A *ᵥ x))^[k] x₀) atTop (𝓝 x)) ↔
      complexSpectralRadius (1 - C * A) < 1 := by
  constructor
  · intro h
    obtain ⟨x, hx⟩ := h 0
    rw [← tendsto_pow_iff_complexSpectralRadius_lt_one,
      tendsto_zero_iff_forall_mulVec_tendsto_zero]
    intro v
    have hv := (hx v).sub (hx 0)
    rw [sub_self] at hv
    have key : ∀ k, (fun x => x + C *ᵥ (0 - A *ᵥ x))^[k] v -
        (fun x => x + C *ᵥ (0 - A *ᵥ x))^[k] 0 = ((1 - C * A) ^ k) *ᵥ v := by
      intro k
      have h1 := iterate_sub_eq_mulVec C A (xs := 0) (mulVec_zero A) v k
      have h2 := iterate_sub_eq_mulVec C A (xs := 0) (mulVec_zero A) 0 k
      rw [sub_zero, sub_zero] at h1
      rw [sub_zero, sub_zero, mulVec_zero] at h2
      rw [h1, h2, sub_zero]
    simpa only [key] using hv
  · intro h b
    have hu : IsUnit (C * A) := by
      have := isUnit_one_sub_of_complexSpectralRadius_lt_one h
      rwa [sub_sub_cancel] at this
    have hA : IsUnit A := (isUnit_iff_isUnit_det A).2
      (isUnit_of_mul_isUnit_right (by rw [← det_mul]; exact (isUnit_iff_isUnit_det _).1 hu))
    refine ⟨A⁻¹ *ᵥ b, fun x₀ => ?_⟩
    rw [← tendsto_sub_nhds_zero_iff]
    have hpow := (tendsto_pow_iff_complexSpectralRadius_lt_one _).2 h
    rw [tendsto_zero_iff_forall_mulVec_tendsto_zero] at hpow
    simpa only [iterate_sub_eq_mulVec C A (mulVec_nonsing_inv_mulVec hA b) x₀] using
      hpow (x₀ - A⁻¹ *ᵥ b)

end Refinement

/-!
### The error of one computed refinement step

`Refinement.step` is the step in exact arithmetic. An implementation computes something else, and
the three results here are the error analysis of one computed step. They are stated for matrices
over $\mathbb{R}$, because the rounding models of `Numlib.FloatingPoint.Model` are.
-/

namespace Refinement

open Matrix

variable {n : ℕ}

/-- **The error of one computed refinement step, exactly** ([quarteroni2000numerical], §3.12.2;
[higham2002accuracy], §12.1). Let $A, \Delta A \in \mathbb{R}^{n \times n}$, and let $x$ solve
$Ax = b$. Let $\hat x$ be the current iterate, let the computed residual be
$\hat r = b - A\hat x + \xi$, let the computed correction $\hat z$ solve the perturbed system
$(A + \Delta A) \hat z = \hat r$, and let the computed update be
$\hat y = \hat x + \hat z + \eta$. Then
$$(A + \Delta A)(x - \hat y) = \Delta A (x - \hat x) - \xi - (A + \Delta A) \eta.$$

A solve with computed LU factors gives a correction of this form, by [quarteroni2000numerical]
(3.64). Every term on the right is small: $\Delta A$ is the backward error of the solve, $\xi$
the error of the residual and $\eta$ the error of the update. So the new error is the old error
multiplied by $(A + \Delta A)^{-1} \Delta A$, plus a floor of the size of the rounding errors.
This is the algebraic core of the convergence claim of [quarteroni2000numerical], §3.12.2, and
of [higham2002accuracy], Theorems 12.1–12.2. It is an identity: no hypothesis on the sizes of
$\Delta A$, $\xi$ and $\eta$ is used. -/
theorem step_error {A ΔA : Matrix (Fin n) (Fin n) ℝ}
    {b x xhat zhat yhat rhat ξ η : Fin n → ℝ} (hx : A *ᵥ x = b)
    (hr : rhat = b - A *ᵥ xhat + ξ) (hz : (A + ΔA) *ᵥ zhat = rhat)
    (hy : yhat = xhat + zhat + η) :
    (A + ΔA) *ᵥ (x - yhat) = ΔA *ᵥ (x - xhat) - ξ - (A + ΔA) *ᵥ η := by
  have hr' : rhat = (A + ΔA) *ᵥ (x - xhat) - ΔA *ᵥ (x - xhat) + ξ := by
    rw [hr, ← hx, add_mulVec, mulVec_sub]
    abel
  rw [hr'] at hz
  rw [hy, show x - (xhat + zhat + η) = x - xhat - zhat - η by abel, mulVec_sub, mulVec_sub, hz]
  abel

open scoped Matrix.Norms.Operator in
/-- **The error recursion of a computed refinement step, in the $\infty$-norm.** Let
$A, \Delta A \in \mathbb{R}^{n \times n}$ with $A + \Delta A$ nonsingular, and let $x$,
$\hat x$, $\hat r$, $\hat z$, $\hat y$, $\xi$ and $\eta$ be as in `Refinement.step_error`:
$Ax = b$, $\hat r = b - A\hat x + \xi$, $(A + \Delta A) \hat z = \hat r$ and
$\hat y = \hat x + \hat z + \eta$. Then
$$\|x - \hat y\|_\infty \le \|(A + \Delta A)^{-1} \Delta A\|_\infty \, \|x - \hat x\|_\infty +
  \|(A + \Delta A)^{-1}\|_\infty \, \|\xi\|_\infty + \|\eta\|_\infty.$$

The error is reduced by the factor $\|(A + \Delta A)^{-1} \Delta A\|_\infty$ down to a floor set
by the roundings of the residual and the update. With $|\Delta A| \le \gamma_{3n} |L| |U|$ from
the backward error of the LU solve, the factor is at most $\gamma_{3n} \| |(A + \Delta A)^{-1}|
\, |L| \, |U| \|_\infty$. This is the quantity that [quarteroni2000numerical], §3.12.2, asks to
be "sufficiently small", with $(A + \Delta A)^{-1}$ in place of $A^{-1}$. -/
theorem norm_step_error_le {A ΔA : Matrix (Fin n) (Fin n) ℝ}
    {b x xhat zhat yhat rhat ξ η : Fin n → ℝ} (hinv : IsUnit (A + ΔA).det) (hx : A *ᵥ x = b)
    (hr : rhat = b - A *ᵥ xhat + ξ) (hz : (A + ΔA) *ᵥ zhat = rhat) (hy : yhat = xhat + zhat + η) :
    ‖x - yhat‖ ≤ ‖(A + ΔA)⁻¹ * ΔA‖ * ‖x - xhat‖ + ‖(A + ΔA)⁻¹‖ * ‖ξ‖ + ‖η‖ := by
  have hid := step_error hx hr hz hy
  have hsol : x - yhat = ((A + ΔA)⁻¹ * ΔA) *ᵥ (x - xhat) - (A + ΔA)⁻¹ *ᵥ ξ - η := by
    have h1 : (A + ΔA) *ᵥ (x - yhat + η) = ΔA *ᵥ (x - xhat) - ξ := by
      rw [mulVec_add, hid]; abel
    have h2 := congrArg (fun v => (A + ΔA)⁻¹ *ᵥ v) h1
    simp only [mulVec_mulVec, nonsing_inv_mul _ hinv, one_mulVec, mulVec_sub] at h2
    rw [show x - yhat = x - yhat + η - η by abel, h2, mulVec_sub]
  calc ‖x - yhat‖ = ‖((A + ΔA)⁻¹ * ΔA) *ᵥ (x - xhat) - (A + ΔA)⁻¹ *ᵥ ξ - η‖ := by rw [hsol]
    _ ≤ ‖((A + ΔA)⁻¹ * ΔA) *ᵥ (x - xhat) - (A + ΔA)⁻¹ *ᵥ ξ‖ + ‖η‖ := norm_sub_le _ _
    _ ≤ ‖((A + ΔA)⁻¹ * ΔA) *ᵥ (x - xhat)‖ + ‖(A + ΔA)⁻¹ *ᵥ ξ‖ + ‖η‖ := by
        gcongr
        exact norm_sub_le _ _
    _ ≤ ‖(A + ΔA)⁻¹ * ΔA‖ * ‖x - xhat‖ + ‖(A + ΔA)⁻¹‖ * ‖ξ‖ + ‖η‖ := by
        gcongr <;> exact linfty_opNorm_mulVec _ _

open FloatingPoint in
/-- **One computed refinement step in the rounding model** ([quarteroni2000numerical], §3.12.2,
steps 1–3; [higham2002accuracy], §12.1). Let $n \ge 1$, and let the rounding model have unit
roundoff $u < 1$ with $3nu < 1$. Let $Ax = b$, and let $L$, $U$ be computed LU factors of $A$
with $u_{jj} \neq 0$ for every $j$. Suppose that the residual $\hat r$ is computed from $\hat x$
as the affine step $-A\hat x + b$, the correction $\hat z$ is computed by forward substitution
with $L$ and backward substitution with $U$, and the update $\hat y_i$ is a rounding of
$\hat x_i + \hat z_i$ for every $i$. Then there are $\Delta A$, $\xi$ and $\eta$ with
$$|\Delta A| \le \gamma_{3n} |L| \, |U|, \qquad |\xi| \le \gamma_{n+1} (|A| \, |\hat x| + |b|),
  \qquad |\eta_i| \le u \, |\hat x_i + \hat z_i|,$$
that satisfy the error identity of `Refinement.step_error`.

The computations are `FloatingPoint.RoundsAffineStep m (-A) b xhat rhat`,
`FloatingPoint.RoundsLU`, `FloatingPoint.RoundsForwardSubst` and
`FloatingPoint.RoundsBackSubst`. This is the rigorous content behind the asymptotic convergence
factors $\rho \simeq 2n \operatorname{cond}(A, x) u$ in fixed precision and $\rho \simeq u$ in
mixed precision that [quarteroni2000numerical], §3.12.2, quotes from [higham2002accuracy],
Theorems 12.1–12.2. The theorems themselves are `Refinement.norm_sub_le_of_forall_roundsStepLU`
and `Refinement.norm_sub_le_of_forall_roundsStepLUMixed`. -/
theorem step_error_fp [NeZero n] {m : RoundingModel ℝ} (hu : m.u < 1)
    (hcard : ((3 * n : ℕ) : ℝ) * m.u < 1) {A L U : Matrix (Fin n) (Fin n) ℝ}
    {b x xhat rhat y zhat yhat : Fin n → ℝ} (hx : A *ᵥ x = b)
    (hres : RoundsAffineStep m (-A) b xhat rhat) (hLU : RoundsLU m A L U) (hd : ∀ j, U j j ≠ 0)
    (hfwd : RoundsForwardSubst m L rhat y) (hbck : RoundsBackSubst m U y zhat)
    (hupd : ∀ i, m.Rounds (xhat i + zhat i) (yhat i)) :
    ∃ ΔA : Matrix (Fin n) (Fin n) ℝ, ∃ ξ η : Fin n → ℝ,
      ΔA.abs ≤ₑ gamma m.u (3 * n) • (L.abs * U.abs) ∧
        |ξ| ≤ gamma m.u (n + 1) • (A.abs *ᵥ |xhat| + |b|) ∧
        (∀ i, |η i| ≤ m.u * |xhat i + zhat i|) ∧
        (A + ΔA) *ᵥ (x - yhat) = ΔA *ᵥ (x - xhat) - ξ - (A + ΔA) *ᵥ η := by
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.2 (NeZero.ne n)
  have hcard' : ((Fintype.card (Fin n) + 1 : ℕ) : ℝ) * m.u < 1 := by
    have h1 : ((Fintype.card (Fin n) + 1 : ℕ) : ℝ) ≤ ((3 * n : ℕ) : ℝ) := by
      simp only [Fintype.card_fin]
      push_cast
      have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    nlinarith [m.u_nonneg]
  have hcard3 : ((3 * Fintype.card (Fin n) : ℕ) : ℝ) * m.u < 1 := by
    simpa [Fintype.card_fin] using hcard
  obtain ⟨ξ, hξeq, hξle⟩ := exists_roundsAffineStep_eq_add hu hcard' hres
  obtain ⟨ΔA, hΔA, hsolve⟩ := exists_roundsLU_solve_eq hu hcard3 hLU hd hfwd hbck
  refine ⟨ΔA, ξ, yhat - (xhat + zhat), by simpa [Fintype.card_fin] using hΔA, ?_,
    fun i => by simpa using m.abs_sub_le (hupd i), ?_⟩
  · have habs : (-A).abs = A.abs := by ext i j; simp
    simpa [Fintype.card_fin, habs] using hξle
  · refine step_error hx ?_ hsolve (by ext i; simp)
    rw [hξeq, neg_mulVec]
    abel

/-!
### The convergence of iterative refinement in finite precision

This section proves [higham2002accuracy], §12.1, Theorems 12.1–12.2, in rigorous form. The one-step
recursion $\|x - \hat y\|_\infty \le \rho \|x - \hat x\|_\infty + \varphi$ with explicit $\rho$ and
$\varphi$ is `Refinement.norm_step_error_le_of_abs_le`, the $\infty$-norm form of Higham's (12.5),
for any solver with $|\Delta A| \le \gamma W$ and any residual with $|\xi| \le \alpha |A| |x - \hat
x| + \beta |A| |x|$. Its two instances for the LU solve, with the residual computed in the working
precision (Theorem 12.2) and in a finer precision (Theorem 12.1), are
`Refinement.norm_sub_le_of_roundsStepLU` and `Refinement.norm_sub_le_of_roundsStepLUMixed`. The
iterated statements with the limiting accuracy $\varphi / (1 - \rho)$ are
`Refinement.norm_sub_le_of_forall_roundsStepLU` and
`Refinement.norm_sub_le_of_forall_roundsStepLUMixed`. The computed steps are the predicates
`Refinement.RoundsStepLU` and `Refinement.RoundsStepLUMixed`; the latter has two rounding models.
-/

section Convergence

open FloatingPoint
open scoped Matrix.Norms.Operator

/-- A **perturbed contraction**. Let $0 \le \rho < 1$ and $c \ge 0$, and let $(a_k)$ be a real
sequence with $a_{k+1} \le \rho a_k + c$ for every $k$. Then for every $k$,
$$a_k \le \rho^k a_0 + \frac{c}{1 - \rho}.$$
-/
theorem le_pow_mul_add_div_of_forall_le_mul_add {a : ℕ → ℝ} {ρ c : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ < 1) (hc : 0 ≤ c) (h : ∀ k, a (k + 1) ≤ ρ * a k + c) (k : ℕ) :
    a k ≤ ρ ^ k * a 0 + c / (1 - ρ) := by
  have hpos : 0 < 1 - ρ := by linarith
  induction k with
  | zero =>
    rw [pow_zero, one_mul]
    linarith [div_nonneg hc hpos.le]
  | succ k ih =>
    refine (h k).trans ?_
    have h1 : ρ * a k ≤ ρ * (ρ ^ k * a 0 + c / (1 - ρ)) := mul_le_mul_of_nonneg_left ih hρ0
    have h2 : ρ * (c / (1 - ρ)) + c = c / (1 - ρ) := by
      field_simp
      ring
    calc ρ * a k + c ≤ ρ * (ρ ^ k * a 0 + c / (1 - ρ)) + c := by linarith
      _ = ρ ^ (k + 1) * a 0 + (ρ * (c / (1 - ρ)) + c) := by ring
      _ = ρ ^ (k + 1) * a 0 + c / (1 - ρ) := by rw [h2]

/-- The **limiting value of a perturbed contraction**. Let $0 \le \rho < 1$ and $c \ge 0$, and let
$(a_k)$ be a nonnegative real sequence with $a_{k+1} \le \rho a_k + c$ for every $k$. Then
$$\limsup_{k \to \infty} a_k \le \frac{c}{1 - \rho}.$$
-/
theorem limsup_le_div_of_forall_le_mul_add {a : ℕ → ℝ} {ρ c : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hc : 0 ≤ c) (ha : ∀ k, 0 ≤ a k) (h : ∀ k, a (k + 1) ≤ ρ * a k + c) :
    limsup a atTop ≤ c / (1 - ρ) := by
  have hv : Tendsto (fun k : ℕ => ρ ^ k * a 0 + c / (1 - ρ)) atTop
      (𝓝 (0 * a 0 + c / (1 - ρ))) :=
    ((tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).mul_const _).add_const _
  have hle : limsup a atTop ≤ limsup (fun k : ℕ => ρ ^ k * a 0 + c / (1 - ρ)) atTop :=
    limsup_le_limsup
      (Eventually.of_forall fun k => le_pow_mul_add_div_of_forall_le_mul_add hρ0 hρ1 hc h k)
      (isCoboundedUnder_le_of_le _ ha) hv.isBoundedUnder_le
  rw [hv.limsup_eq] at hle
  simpa using hle

/-- The **residual error in the form of [higham2002accuracy] (12.2)**. Let
$A \in \mathbb{R}^{n \times n}$, $Ax = b$ and $c \ge 0$. If the error $\xi$ of a computed
residual at $\hat x$ satisfies $|\xi| \le c (|A| \, |\hat x| + |b|)$, then
$$|\xi| \le c \, |A| \, |x - \hat x| + 2c \, |A| \, |x|,$$
a bound in terms of the error $x - \hat x$ and the solution $x$. -/
theorem abs_le_of_abs_le_smul_mulVec_abs_add_abs {A : Matrix (Fin n) (Fin n) ℝ}
    {b x xhat ξ : Fin n → ℝ} (hx : A *ᵥ x = b) {c : ℝ} (hc : 0 ≤ c)
    (hξ : |ξ| ≤ c • (A.abs *ᵥ |xhat| + |b|)) :
    |ξ| ≤ c • (A.abs *ᵥ |x - xhat|) + (2 * c) • (A.abs *ᵥ |x|) := by
  have hxhat : |xhat| ≤ |x| + |x - xhat| := fun i => by
    have := abs_sub (x i) (x i - xhat i)
    rwa [sub_sub_cancel] at this
  have h1 : A.abs *ᵥ |xhat| ≤ A.abs *ᵥ |x| + A.abs *ᵥ |x - xhat| := by
    rw [← mulVec_add]
    exact (entrywiseNonneg_abs A).mulVec_mono hxhat
  have h2 : |b| ≤ A.abs *ᵥ |x| := by rw [← hx]; exact abs_mulVec_le A x
  refine hξ.trans (Pi.le_def.2 fun i => ?_)
  have := h1 i
  have := h2 i
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul] at *
  nlinarith

/-- **The forward error of one computed refinement step**, [higham2002accuracy] (12.5) in the
$\infty$-norm. Let $A \in \mathbb{R}^{n \times n}$ be nonsingular, and let
$\Delta A, W \in \mathbb{R}^{n \times n}$. Let $Ax = b$, let $\hat r = b - A\hat x + \xi$ be a
computed residual, let $(A + \Delta A) \hat z = \hat r$, and let
$\hat y = \hat x + \hat z + \eta$. Let $\gamma, \alpha, \beta, u \ge 0$, and suppose that
$$|\Delta A| \le \gamma W, \qquad |\xi| \le \alpha |A| \, |x - \hat x| + \beta |A| \, |x|,
  \qquad |\eta_i| \le u \, |\hat x_i + \hat z_i|.$$
The first bound is [higham2002accuracy] (12.1) and the second is (12.2). If
$\theta = \gamma \| |A^{-1}| W \|_\infty$ satisfies $\theta + 2u < 1$, then
$$(1 - 2u - \theta) \|x - \hat y\|_\infty \le (\theta + \alpha \| |A^{-1}| \, |A| \|_\infty)
  \|x - \hat x\|_\infty + \beta \| |A^{-1}| \, |A| \, |x| \|_\infty + u (1 + \theta)
  \|x\|_\infty.$$

So the error contracts by the factor $(\theta + \alpha \operatorname{cond}(A)) / (1 - 2u -
\theta)$ down to the floor $(\beta \operatorname{cond}(A, x) + u(1 + \theta)) \|x\|_\infty /
(1 - 2u - \theta)$. Higham writes the factor as "approximately
$\eta = u \| |A^{-1}| (|A| + W) \|_\infty$". The proof solves the identity of
`Refinement.step_error` for $x - \hat y$ with $A^{-1}$ instead of $(A + \Delta A)^{-1}$, $x -
\hat y = A^{-1} (\Delta A (x - \hat x) - \xi - \Delta A \eta - \Delta A (x - \hat y)) - \eta$,
bounds it entrywise, and moves the terms in $\Delta A (x - \hat y)$ and $\eta$ to the left side;
this gives the factor $1 - 2u - \theta$. -/
theorem norm_step_error_le_of_abs_le {A ΔA W : Matrix (Fin n) (Fin n) ℝ}
    {b x xhat zhat yhat rhat ξ η : Fin n → ℝ} (hA : IsUnit A) (hx : A *ᵥ x = b)
    (hr : rhat = b - A *ᵥ xhat + ξ) (hz : (A + ΔA) *ᵥ zhat = rhat) (hy : yhat = xhat + zhat + η)
    {γ α β u : ℝ} (hγ : 0 ≤ γ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hu : 0 ≤ u) (hΔA : ΔA.abs ≤ₑ γ • W)
    (hξ : |ξ| ≤ α • (A.abs *ᵥ |x - xhat|) + β • (A.abs *ᵥ |x|))
    (hη : ∀ i, |η i| ≤ u * |xhat i + zhat i|) (hsmall : γ * ‖A⁻¹.abs * W‖ + 2 * u < 1) :
    (1 - 2 * u - γ * ‖A⁻¹.abs * W‖) * ‖x - yhat‖ ≤
      (γ * ‖A⁻¹.abs * W‖ + α * ‖A⁻¹.abs * A.abs‖) * ‖x - xhat‖
        + β * ‖A⁻¹.abs *ᵥ (A.abs *ᵥ |x|)‖ + u * (1 + γ * ‖A⁻¹.abs * W‖) * ‖x‖ := by
  have hAd : IsUnit A.det := (isUnit_iff_isUnit_det A).1 hA
  set θ : ℝ := γ * ‖A⁻¹.abs * W‖ with hθ
  have hθ0 : 0 ≤ θ := mul_nonneg hγ (norm_nonneg _)
  -- the error identity, solved for `x - ŷ` with `A⁻¹`
  have hid := step_error hx hr hz hy
  set v : Fin n → ℝ := ΔA *ᵥ (x - xhat) - ξ - ΔA *ᵥ η - ΔA *ᵥ (x - yhat) with hv
  have hsol : x - yhat = A⁻¹ *ᵥ v - η := by
    have h1 : A *ᵥ (x - yhat + η) = v := by
      rw [add_mulVec, add_mulVec] at hid
      rw [hv, mulVec_add]
      linear_combination hid
    have h2 := congrArg (fun w => A⁻¹ *ᵥ w) h1
    simp only [mulVec_mulVec, nonsing_inv_mul _ hAd, one_mulVec] at h2
    rw [← h2]
    abel
  -- the entrywise bounds
  have hΔ : ∀ w : Fin n → ℝ, |ΔA *ᵥ w| ≤ γ • (W *ᵥ |w|) := fun w =>
    (abs_mulVec_le ΔA w).trans (by
      have := hΔA.mulVec_le_of_nonneg (abs_nonneg w)
      rwa [smul_mulVec] at this)
  have hAinv := entrywiseNonneg_abs A⁻¹
  have hvabs : |v| ≤ γ • (W *ᵥ |x - xhat|) + |ξ| + γ • (W *ᵥ |η|) + γ • (W *ᵥ |x - yhat|) := by
    refine Pi.le_def.2 fun i => ?_
    have h1 := hΔ (x - xhat) i
    have h2 := hΔ η i
    have h3 := hΔ (x - yhat) i
    simp only [hv, Pi.abs_apply, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at *
    calc |(ΔA *ᵥ (x - xhat)) i - ξ i - (ΔA *ᵥ η) i - (ΔA *ᵥ (x - yhat)) i|
        ≤ |(ΔA *ᵥ (x - xhat)) i| + |ξ i| + |(ΔA *ᵥ η) i| + |(ΔA *ᵥ (x - yhat)) i| := by
          refine (abs_sub _ _).trans (add_le_add ?_ le_rfl)
          refine (abs_sub _ _).trans (add_le_add ?_ le_rfl)
          exact abs_sub _ _
      _ ≤ _ := by linarith
  have hkey : |x - yhat| ≤ γ • ((A⁻¹.abs * W) *ᵥ |x - xhat|)
      + (α • ((A⁻¹.abs * A.abs) *ᵥ |x - xhat|) + β • (A⁻¹.abs *ᵥ (A.abs *ᵥ |x|)))
      + γ • ((A⁻¹.abs * W) *ᵥ |η|) + γ • ((A⁻¹.abs * W) *ᵥ |x - yhat|) + |η| := by
    calc |x - yhat| = |A⁻¹ *ᵥ v - η| := by rw [hsol]
      _ ≤ |A⁻¹ *ᵥ v| + |η| := Pi.le_def.2 fun i => by
          simp only [Pi.abs_apply, Pi.sub_apply, Pi.add_apply]
          exact abs_sub _ _
      _ ≤ A⁻¹.abs *ᵥ |v| + |η| := add_le_add (abs_mulVec_le _ _) le_rfl
      _ ≤ A⁻¹.abs *ᵥ (γ • (W *ᵥ |x - xhat|) + (α • (A.abs *ᵥ |x - xhat|) + β • (A.abs *ᵥ |x|))
            + γ • (W *ᵥ |η|) + γ • (W *ᵥ |x - yhat|)) + |η| := by
          refine add_le_add (hAinv.mulVec_mono ?_) le_rfl
          refine hvabs.trans ?_
          intro i
          have := hξ i
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at *
          linarith
      _ = _ := by
          simp only [mulVec_add, mulVec_smul, mulVec_mulVec]
  -- the sup norms
  have hηn : ‖η‖ ≤ u * (‖x‖ + ‖x - yhat‖ + ‖η‖) := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
    rw [Real.norm_eq_abs]
    have h1 : xhat i + zhat i = yhat i - η i := by rw [hy]; simp only [Pi.add_apply]; ring
    have h2 : |yhat i - η i| ≤ |x i| + |x i - yhat i| + |η i| := by
      have := abs_sub (yhat i) (η i)
      have := abs_sub (x i) (x i - yhat i)
      rw [sub_sub_cancel] at this
      linarith
    have h3 : |x i| ≤ ‖x‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm x i
    have h4 : |x i - yhat i| ≤ ‖x - yhat‖ := by
      rw [← Real.norm_eq_abs]; exact norm_le_pi_norm (x - yhat) i
    have h5 : |η i| ≤ ‖η‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm η i
    calc |η i| ≤ u * |xhat i + zhat i| := hη i
      _ ≤ u * (‖x‖ + ‖x - yhat‖ + ‖η‖) := by
          rw [h1]
          exact mul_le_mul_of_nonneg_left (h2.trans (by linarith)) hu
  have hmv : ∀ (M : Matrix (Fin n) (Fin n) ℝ) (w : Fin n → ℝ), ‖M *ᵥ |w|‖ ≤ ‖M‖ * ‖w‖ :=
    fun M w => by rw [← norm_abs_eq w]; exact linfty_opNorm_mulVec _ _
  have hen : ‖x - yhat‖ ≤ θ * ‖x - xhat‖
      + (α * ‖A⁻¹.abs * A.abs‖ * ‖x - xhat‖ + β * ‖A⁻¹.abs *ᵥ (A.abs *ᵥ |x|)‖)
      + θ * ‖η‖ + θ * ‖x - yhat‖ + ‖η‖ := by
    refine (norm_le_norm_of_abs_le hkey).trans ?_
    refine (norm_add_le _ _).trans (add_le_add ?_ (norm_abs_eq η).le)
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [norm_smul, Real.norm_of_nonneg hγ, hθ, mul_assoc]
          exact mul_le_mul_of_nonneg_left (hmv _ _) hγ
        · refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
          · rw [norm_smul, Real.norm_of_nonneg hα, mul_assoc]
            exact mul_le_mul_of_nonneg_left (hmv _ _) hα
          · rw [norm_smul, Real.norm_of_nonneg hβ]
      · rw [norm_smul, Real.norm_of_nonneg hγ, hθ, mul_assoc]
        exact mul_le_mul_of_nonneg_left (hmv _ _) hγ
    · rw [norm_smul, Real.norm_of_nonneg hγ, hθ, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hmv _ _) hγ
  -- collect
  have hen' := mul_le_mul_of_nonneg_left hen (by linarith : (0 : ℝ) ≤ 1 - u)
  have hηn2 : (1 - u) * ‖η‖ ≤ u * (‖x‖ + ‖x - yhat‖) := by linarith
  have hηn' := mul_le_mul_of_nonneg_left hηn2 (by linarith : (0 : ℝ) ≤ 1 + θ)
  have hrest : 0 ≤ u * (θ * ‖x - xhat‖ + (α * ‖A⁻¹.abs * A.abs‖ * ‖x - xhat‖
      + β * ‖A⁻¹.abs *ᵥ (A.abs *ᵥ |x|)‖)) := by positivity
  linarith

/-! ### The computed steps, and Higham's Theorems 12.1–12.2 -/

/-- **One computed step of iterative refinement with LU factors, in fixed precision**
([quarteroni2000numerical], §3.12.2, FPR; [higham2002accuracy], §12.1 with $\bar u = u$). For a
rounding model, matrices $A, L, U \in \mathbb{R}^{n \times n}$ and vectors $b$, $\hat x$,
$\hat y$, the predicate says that $\hat y$ is an admissible computed value of one refinement
step from $\hat x$. That is, there are $\hat r$, $y$ and $\hat z$ such that the residual
$\hat r = \operatorname{fl}(b - A\hat x)$ is computed as an affine step, the correction $\hat z$
is computed by forward substitution with $L$ ($Ly = \hat r$) and backward substitution with $U$
($U \hat z = y$), and $\hat y_i$ is a rounding of $\hat x_i + \hat z_i$ for every $i$.

The computations are `FloatingPoint.RoundsAffineStep`, `FloatingPoint.RoundsForwardSubst` and
`FloatingPoint.RoundsBackSubst`. -/
def RoundsStepLU (m : RoundingModel ℝ) (A L U : Matrix (Fin n) (Fin n) ℝ)
    (b xhat yhat : Fin n → ℝ) : Prop :=
  ∃ rhat y zhat : Fin n → ℝ, RoundsAffineStep m (-A) b xhat rhat ∧
    RoundsForwardSubst m L rhat y ∧ RoundsBackSubst m U y zhat ∧
    ∀ i, m.Rounds (xhat i + zhat i) (yhat i)

/-- **One computed step of iterative refinement with LU factors, in mixed precision**
([quarteroni2000numerical], §3.12.2, MPR; [higham2002accuracy], §12.1 with $\bar u = u^2$). For
two rounding models `m` and `m'`, the predicate is `Refinement.RoundsStepLU` with the residual
computed in the second, finer model `m'` (in the book, double precision) and then rounded once
to the working precision `m`: $s = \operatorname{fl}'(b - A\hat x)$ and
$\hat r = \operatorname{fl}(s)$. The solve and the update are in `m`. -/
def RoundsStepLUMixed (m m' : RoundingModel ℝ) (A L U : Matrix (Fin n) (Fin n) ℝ)
    (b xhat yhat : Fin n → ℝ) : Prop :=
  ∃ s rhat y zhat : Fin n → ℝ, RoundsAffineStep m' (-A) b xhat s ∧
    (∀ i, m.Rounds (s i) (rhat i)) ∧
    RoundsForwardSubst m L rhat y ∧ RoundsBackSubst m U y zhat ∧
    ∀ i, m.Rounds (xhat i + zhat i) (yhat i)

/-- The **residual computed as an affine step**, with its error in the form of [higham2002accuracy]
(12.2). Let the rounding model have unit roundoff $u < 1$ with $(n + 1) u < 1$, let $Ax = b$,
and let $\hat r$ be computed from $\hat x$ as the affine step $-A\hat x + b$. Then
$\hat r = b - A\hat x + \xi$ for some $\xi$ with
$$|\xi| \le \gamma_{n+1} |A| \, |x - \hat x| + 2 \gamma_{n+1} |A| \, |x|.$$
-/
theorem exists_roundsAffineStep_residual_eq_add {m : RoundingModel ℝ} (hu : m.u < 1)
    (hcard : ((n + 1 : ℕ) : ℝ) * m.u < 1) {A : Matrix (Fin n) (Fin n) ℝ} {b x xhat rhat : Fin n → ℝ}
    (hx : A *ᵥ x = b) (hres : RoundsAffineStep m (-A) b xhat rhat) :
    ∃ ξ : Fin n → ℝ, rhat = b - A *ᵥ xhat + ξ ∧
      |ξ| ≤ gamma m.u (n + 1) • (A.abs *ᵥ |x - xhat|)
        + (2 * gamma m.u (n + 1)) • (A.abs *ᵥ |x|) := by
  have hcard' : ((Fintype.card (Fin n) + 1 : ℕ) : ℝ) * m.u < 1 := by
    simpa [Fintype.card_fin] using hcard
  obtain ⟨ξ, hξeq, hξle⟩ := exists_roundsAffineStep_eq_add hu hcard' hres
  have habs : (-A).abs = A.abs := by ext i j; simp
  refine ⟨ξ, by rw [hξeq, neg_mulVec]; abel, ?_⟩
  refine abs_le_of_abs_le_smul_mulVec_abs_add_abs hx (gamma_nonneg m.u_nonneg hcard) ?_
  simpa [Fintype.card_fin, habs] using hξle

/-- The **mixed-precision residual**, with its error in the form of [higham2002accuracy] (12.2). Let
the finer model `m'` have unit roundoff $\bar u < 1$ with $(n + 1) \bar u < 1$, and let $u$ be
the unit roundoff of the model `m`. Let $Ax = b$, let $s$ be computed in `m'` from $\hat x$ as
the affine step $-A\hat x + b$, and let $\hat r_i$ be a rounding of $s_i$ in `m` for every $i$.
Then $\hat r = b - A\hat x + \xi$ for some $\xi$ with
$$|\xi| \le (u + (1 + u) \bar\gamma_{n+1}) |A| \, |x - \hat x| + 2 (1 + u) \bar\gamma_{n+1} |A|
  \, |x|,$$
where $\bar\gamma_{n+1}$ is the constant of `m'`. -/
theorem exists_mixed_residual_eq_add {m m' : RoundingModel ℝ} (hu' : m'.u < 1)
    (hcard' : ((n + 1 : ℕ) : ℝ) * m'.u < 1) {A : Matrix (Fin n) (Fin n) ℝ}
    {b x xhat s rhat : Fin n → ℝ} (hx : A *ᵥ x = b) (hres : RoundsAffineStep m' (-A) b xhat s)
    (hround : ∀ i, m.Rounds (s i) (rhat i)) :
    ∃ ξ : Fin n → ℝ, rhat = b - A *ᵥ xhat + ξ ∧
      |ξ| ≤ (m.u + (1 + m.u) * gamma m'.u (n + 1)) • (A.abs *ᵥ |x - xhat|)
        + (2 * (1 + m.u) * gamma m'.u (n + 1)) • (A.abs *ᵥ |x|) := by
  obtain ⟨ξ', hs, hξ'⟩ := exists_roundsAffineStep_residual_eq_add hu' hcard' hx hres
  have hu0 := m.u_nonneg
  refine ⟨rhat - (b - A *ᵥ xhat), by abel, Pi.le_def.2 fun i => ?_⟩
  have h1 : |rhat i - s i| ≤ m.u * |s i| := m.abs_sub_le (hround i)
  have h2 : |(b - A *ᵥ xhat) i| ≤ (A.abs *ᵥ |x - xhat|) i := by
    rw [← hx, ← mulVec_sub]
    exact abs_mulVec_le A (x - xhat) i
  have h3 := hξ' i
  have hsi : s i = (b - A *ᵥ xhat) i + ξ' i := by rw [hs]; rfl
  have h4 : |s i| ≤ (A.abs *ᵥ |x - xhat|) i + |ξ' i| := by
    rw [hsi]
    exact (abs_add_le _ _).trans (add_le_add h2 le_rfl)
  have h5 : |(rhat - (b - A *ᵥ xhat)) i| ≤ |rhat i - s i| + |ξ' i| := by
    have : (rhat - (b - A *ᵥ xhat)) i = (rhat i - s i) + ξ' i := by
      simp only [Pi.sub_apply, hsi]; ring
    rw [this]
    exact abs_add_le _ _
  simp only [Pi.abs_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at *
  nlinarith

/-- **Theorem 12.2 of [higham2002accuracy], one step** (fixed-precision iterative refinement with LU
factors, [quarteroni2000numerical], §3.12.2, FPR). Let $n \ge 1$, and let the rounding model
have unit roundoff $u$ with $3nu < 1$. Let $A \in \mathbb{R}^{n \times n}$ be nonsingular with
$Ax = b$, and let $L$, $U$ be computed LU factors of $A$ with $u_{jj} \neq 0$ for every $j$. Let
$\hat y$ be a computed refinement step from $\hat x$ (`Refinement.RoundsStepLU`), and let
$\theta = \gamma_{3n} \| |A^{-1}| \, |L| \, |U| \|_\infty$. If $\theta + 2u < 1$, then
$$(1 - 2u - \theta) \|x - \hat y\|_\infty \le (\theta + \gamma_{n+1} \operatorname{cond}(A))
  \|x - \hat x\|_\infty + 2 \gamma_{n+1} \| |A^{-1}| \, |A| \, |x| \|_\infty + u (1 + \theta)
  \|x\|_\infty,$$
where $\operatorname{cond}(A) = \| |A^{-1}| \, |A| \|_\infty$ is the Skeel condition number.

This is `Refinement.norm_step_error_le_of_abs_le` with the three errors of
`Refinement.step_error_fp`: $|\Delta A| \le \gamma_{3n} |L| |U|$
(`FloatingPoint.exists_roundsLU_solve_eq`), the residual error of
`Refinement.exists_roundsAffineStep_residual_eq_add`, and $|\eta_i| \le u |\hat x_i + \hat z_i|$
for the update. -/
theorem norm_sub_le_of_roundsStepLU [NeZero n] {m : RoundingModel ℝ}
    (hcard : ((3 * n : ℕ) : ℝ) * m.u < 1) {A L U : Matrix (Fin n) (Fin n) ℝ}
    {b x xhat yhat : Fin n → ℝ} (hA : IsUnit A) (hx : A *ᵥ x = b) (hLU : RoundsLU m A L U)
    (hd : ∀ j, U j j ≠ 0) (hstep : RoundsStepLU m A L U b xhat yhat)
    (hsmall : gamma m.u (3 * n) * ‖A⁻¹.abs * (L.abs * U.abs)‖ + 2 * m.u < 1) :
    (1 - 2 * m.u - gamma m.u (3 * n) * ‖A⁻¹.abs * (L.abs * U.abs)‖) * ‖x - yhat‖ ≤
      (gamma m.u (3 * n) * ‖A⁻¹.abs * (L.abs * U.abs)‖
          + gamma m.u (n + 1) * ‖A⁻¹.abs * A.abs‖) * ‖x - xhat‖
        + 2 * gamma m.u (n + 1) * ‖A⁻¹.abs *ᵥ (A.abs *ᵥ |x|)‖
        + m.u * (1 + gamma m.u (3 * n) * ‖A⁻¹.abs * (L.abs * U.abs)‖) * ‖x‖ := by
  obtain ⟨rhat, y, zhat, hres, hfwd, hbck, hupd⟩ := hstep
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.2 (NeZero.ne n)
  have hu : m.u < 1 := by
    have h1 : (1 : ℝ) * m.u ≤ ((3 * n : ℕ) : ℝ) * m.u := by
      refine mul_le_mul_of_nonneg_right ?_ m.u_nonneg
      exact_mod_cast (by omega : 1 ≤ 3 * n)
    linarith
  have hcard1 : ((n + 1 : ℕ) : ℝ) * m.u < 1 := by
    have h1 : ((n + 1 : ℕ) : ℝ) ≤ ((3 * n : ℕ) : ℝ) := by exact_mod_cast (by omega : n + 1 ≤ 3 * n)
    nlinarith [m.u_nonneg]
  have hcard3 : ((3 * Fintype.card (Fin n) : ℕ) : ℝ) * m.u < 1 := by
    simpa [Fintype.card_fin] using hcard
  obtain ⟨ξ, hξeq, hξle⟩ := exists_roundsAffineStep_residual_eq_add hu hcard1 hx hres
  obtain ⟨ΔA, hΔA, hsolve⟩ := exists_roundsLU_solve_eq hu hcard3 hLU hd hfwd hbck
  rw [Fintype.card_fin] at hΔA
  have hγ3 := gamma_nonneg m.u_nonneg hcard
  have hγ1 := gamma_nonneg m.u_nonneg hcard1
  have hη : ∀ i, |(yhat - (xhat + zhat)) i| ≤ m.u * |xhat i + zhat i| := fun i => by
    simpa using m.abs_sub_le (hupd i)
  have hy : yhat = xhat + zhat + (yhat - (xhat + zhat)) := by abel
  have h := norm_step_error_le_of_abs_le hA hx hξeq hsolve hy hγ3 hγ1
    (by positivity) m.u_nonneg hΔA hξle hη hsmall
  linarith

/-- **Theorem 12.1 of [higham2002accuracy], one step** (mixed-precision iterative refinement with LU
factors, [quarteroni2000numerical], §3.12.2, MPR). Let $n \ge 1$, let the working model `m` have
unit roundoff $u$ with $3nu < 1$, and let the finer model `m'` have unit roundoff $\bar u$ with
$(n + 1) \bar u < 1$. Let $A \in \mathbb{R}^{n \times n}$ be nonsingular with $Ax = b$, and let
$L$, $U$ be computed LU factors of $A$ in `m` with $u_{jj} \neq 0$ for every $j$. Let $\hat y$
be a computed refinement step from $\hat x$ whose residual is computed in `m'` and rounded to
`m` (`Refinement.RoundsStepLUMixed`), and let $\theta = \gamma_{3n} \| |A^{-1}| \, |L| \, |U|
\|_\infty$. If $\theta + 2u < 1$, then
$$(1 - 2u - \theta) \|x - \hat y\|_\infty \le (\theta + (u + (1 + u) \bar\gamma_{n+1})
  \operatorname{cond}(A)) \|x - \hat x\|_\infty + 2 (1 + u) \bar\gamma_{n+1} \| |A^{-1}| \, |A|
  \, |x| \|_\infty + u (1 + \theta) \|x\|_\infty,$$
where $\bar\gamma_{n+1}$ is the constant of `m'`.

With $\bar u = u^2$, the floor $2 (1 + u) \bar\gamma_{n+1} \operatorname{cond}(A, x) + u (1 +
\theta)$ is $u (1 + \theta) + O(n u^2 \operatorname{cond}(A, x))$. To first order it does not
depend on the condition number; this is the book's $\rho \simeq u$. -/
theorem norm_sub_le_of_roundsStepLUMixed [NeZero n] {m m' : RoundingModel ℝ}
    (hcard : ((3 * n : ℕ) : ℝ) * m.u < 1) (hcard' : ((n + 1 : ℕ) : ℝ) * m'.u < 1)
    {A L U : Matrix (Fin n) (Fin n) ℝ} {b x xhat yhat : Fin n → ℝ} (hA : IsUnit A)
    (hx : A *ᵥ x = b) (hLU : RoundsLU m A L U) (hd : ∀ j, U j j ≠ 0)
    (hstep : RoundsStepLUMixed m m' A L U b xhat yhat)
    (hsmall : gamma m.u (3 * n) * ‖A⁻¹.abs * (L.abs * U.abs)‖ + 2 * m.u < 1) :
    (1 - 2 * m.u - gamma m.u (3 * n) * ‖A⁻¹.abs * (L.abs * U.abs)‖) * ‖x - yhat‖ ≤
      (gamma m.u (3 * n) * ‖A⁻¹.abs * (L.abs * U.abs)‖
          + (m.u + (1 + m.u) * gamma m'.u (n + 1)) * ‖A⁻¹.abs * A.abs‖) * ‖x - xhat‖
        + 2 * (1 + m.u) * gamma m'.u (n + 1) * ‖A⁻¹.abs *ᵥ (A.abs *ᵥ |x|)‖
        + m.u * (1 + gamma m.u (3 * n) * ‖A⁻¹.abs * (L.abs * U.abs)‖) * ‖x‖ := by
  obtain ⟨s, rhat, y, zhat, hres, hround, hfwd, hbck, hupd⟩ := hstep
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.2 (NeZero.ne n)
  have hu : m.u < 1 := by
    have h1 : (1 : ℝ) * m.u ≤ ((3 * n : ℕ) : ℝ) * m.u := by
      refine mul_le_mul_of_nonneg_right ?_ m.u_nonneg
      exact_mod_cast (by omega : 1 ≤ 3 * n)
    linarith
  have hu' : m'.u < 1 := by
    have h1 : (1 : ℝ) * m'.u ≤ ((n + 1 : ℕ) : ℝ) * m'.u := by
      refine mul_le_mul_of_nonneg_right ?_ m'.u_nonneg
      exact_mod_cast (by omega : 1 ≤ n + 1)
    linarith
  have hcard3 : ((3 * Fintype.card (Fin n) : ℕ) : ℝ) * m.u < 1 := by
    simpa [Fintype.card_fin] using hcard
  obtain ⟨ξ, hξeq, hξle⟩ := exists_mixed_residual_eq_add hu' hcard' hx hres hround
  obtain ⟨ΔA, hΔA, hsolve⟩ := exists_roundsLU_solve_eq hu hcard3 hLU hd hfwd hbck
  rw [Fintype.card_fin] at hΔA
  have hγ3 := gamma_nonneg m.u_nonneg hcard
  have hγ1 := gamma_nonneg m'.u_nonneg hcard'
  have hη : ∀ i, |(yhat - (xhat + zhat)) i| ≤ m.u * |xhat i + zhat i| := fun i => by
    simpa using m.abs_sub_le (hupd i)
  have hy : yhat = xhat + zhat + (yhat - (xhat + zhat)) := by abel
  have hu0 := m.u_nonneg
  have h := norm_step_error_le_of_abs_le hA hx hξeq hsolve hy hγ3
    (by positivity) (by positivity) hu0 hΔA hξle hη hsmall
  linarith

/-- The one-step recursion of [higham2002accuracy] (12.5) in the form $N' \le \rho N + \varphi$,
from its product form. Let $u, \theta, \sigma, c, N, N', X$ be real numbers with
$1 - 2u - \theta > 0$ and
$$(1 - 2u - \theta) N' \le (\theta + \sigma) N + c + u (1 + \theta) X.$$
Then $N' \le \rho N + \varphi$ with $\rho = (\theta + \sigma) / (1 - 2u - \theta)$ and
$\varphi = (c + u (1 + \theta) X) / (1 - 2u - \theta)$. -/
theorem norm_sub_le_mul_add_of_mul_le {u θ σ c N N' X : ℝ} (hpos : 0 < 1 - 2 * u - θ)
    (h : (1 - 2 * u - θ) * N' ≤ (θ + σ) * N + c + u * (1 + θ) * X) :
    N' ≤ (θ + σ) / (1 - 2 * u - θ) * N + (c + u * (1 + θ) * X) / (1 - 2 * u - θ) := by
  rw [div_mul_eq_mul_div, ← add_div, le_div_iff₀ hpos]
  linarith

/-- **Theorem 12.2 of [higham2002accuracy]** (fixed-precision iterative refinement), in rigorous
form. Let $n \ge 1$, and let the rounding model have unit roundoff $u$ with $3nu < 1$. Let
$A \in \mathbb{R}^{n \times n}$ be nonsingular with $Ax = b$, let $L$, $U$ be computed LU
factors of $A$ with $u_{jj} \neq 0$ for every $j$, and let $x^{(0)}, x^{(1)}, \dots$ be computed
refinement iterates: $x^{(k+1)}$ is a computed step from $x^{(k)}$ (`Refinement.RoundsStepLU`)
for every $k$. Put
$$\theta = \gamma_{3n} \| |A^{-1}| \, |L| \, |U| \|_\infty, \qquad \rho = \frac{\theta +
  \gamma_{n+1} \operatorname{cond}(A)}{1 - 2u - \theta}, \qquad \varphi = \frac{2 \gamma_{n+1}
  \| |A^{-1}| \, |A| \, |x| \|_\infty + u (1 + \theta) \|x\|_\infty}{1 - 2u - \theta}.$$
If $2\theta + \gamma_{n+1} \operatorname{cond}(A) + 2u < 1$, then $\rho < 1$, and for every $k$
$$\|x - x^{(k+1)}\|_\infty \le \rho \|x - x^{(k)}\|_\infty + \varphi, \qquad \|x -
  x^{(k)}\|_\infty \le \rho^k \|x - x^{(0)}\|_\infty + \frac{\varphi}{1 - \rho},$$
and the limiting accuracy is $\limsup_k \|x - x^{(k)}\|_\infty \le \varphi / (1 - \rho)$.

The hypothesis is the theorem's "$\eta$ sufficiently less than $1$", with
$\eta \approx u \| |A^{-1}| (|A| + W) \|_\infty$ and $uW = \gamma_{3n} |L| |U|$. The relative
floor $\varphi / \|x\|_\infty = (2 \gamma_{n+1} \operatorname{cond}(A, x) + u (1 + \theta)) /
(1 - 2u - \theta) \approx 2n \operatorname{cond}(A, x) u$ is the theorem's "until $\|x - \hat
x_i\|_\infty / \|x\|_\infty \lesssim 2n \operatorname{cond}(A, x) u$". -/
theorem norm_sub_le_of_forall_roundsStepLU [NeZero n] {m : RoundingModel ℝ}
    (hcard : ((3 * n : ℕ) : ℝ) * m.u < 1) {A L U : Matrix (Fin n) (Fin n) ℝ}
    {b x : Fin n → ℝ} (hA : IsUnit A) (hx : A *ᵥ x = b) (hLU : RoundsLU m A L U)
    (hd : ∀ j, U j j ≠ 0) {xs : ℕ → Fin n → ℝ}
    (hstep : ∀ k, RoundsStepLU m A L U b (xs k) (xs (k + 1))) {θ ρ φ : ℝ}
    (hθ : θ = gamma m.u (3 * n) * ‖A⁻¹.abs * (L.abs * U.abs)‖)
    (hρ : ρ = (θ + gamma m.u (n + 1) * ‖A⁻¹.abs * A.abs‖) / (1 - 2 * m.u - θ))
    (hφ : φ = (2 * gamma m.u (n + 1) * ‖A⁻¹.abs *ᵥ (A.abs *ᵥ |x|)‖ + m.u * (1 + θ) * ‖x‖)
      / (1 - 2 * m.u - θ))
    (hsmall : 2 * θ + gamma m.u (n + 1) * ‖A⁻¹.abs * A.abs‖ + 2 * m.u < 1) :
    ρ < 1 ∧ (∀ k, ‖x - xs (k + 1)‖ ≤ ρ * ‖x - xs k‖ + φ) ∧
      (∀ k, ‖x - xs k‖ ≤ ρ ^ k * ‖x - xs 0‖ + φ / (1 - ρ)) ∧
      limsup (fun k => ‖x - xs k‖) atTop ≤ φ / (1 - ρ) := by
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.2 (NeZero.ne n)
  have hcard1 : ((n + 1 : ℕ) : ℝ) * m.u < 1 := by
    have h1 : ((n + 1 : ℕ) : ℝ) ≤ ((3 * n : ℕ) : ℝ) := by exact_mod_cast (by omega : n + 1 ≤ 3 * n)
    nlinarith [m.u_nonneg]
  have hθ0 : 0 ≤ θ := by
    rw [hθ]; exact mul_nonneg (gamma_nonneg m.u_nonneg hcard) (norm_nonneg _)
  have hσ0 : 0 ≤ gamma m.u (n + 1) * ‖A⁻¹.abs * A.abs‖ :=
    mul_nonneg (gamma_nonneg m.u_nonneg hcard1) (norm_nonneg _)
  have hpos : 0 < 1 - 2 * m.u - θ := by linarith
  have hsmall' : θ + 2 * m.u < 1 := by linarith
  have hρ1 : ρ < 1 := by
    rw [hρ, div_lt_one hpos]; linarith
  have hρ0 : 0 ≤ ρ := by rw [hρ]; positivity
  have hφ0 : 0 ≤ φ := by
    rw [hφ]
    have : 0 ≤ 2 * gamma m.u (n + 1) * ‖A⁻¹.abs *ᵥ (A.abs *ᵥ |x|)‖ + m.u * (1 + θ) * ‖x‖ := by
      have := gamma_nonneg m.u_nonneg hcard1
      have := m.u_nonneg
      positivity
    positivity
  have hrec : ∀ k, ‖x - xs (k + 1)‖ ≤ ρ * ‖x - xs k‖ + φ := fun k => by
    have h := norm_sub_le_of_roundsStepLU hcard hA hx hLU hd (hstep k) (by rw [← hθ]; exact hsmall')
    rw [← hθ] at h
    rw [hρ, hφ]
    exact norm_sub_le_mul_add_of_mul_le hpos h
  refine ⟨hρ1, hrec, fun k =>
    le_pow_mul_add_div_of_forall_le_mul_add (a := fun k => ‖x - xs k‖) hρ0 hρ1 hφ0 hrec k, ?_⟩
  exact limsup_le_div_of_forall_le_mul_add hρ0 hρ1 hφ0 (fun k => norm_nonneg _) hrec

/-- **Theorem 12.1 of [higham2002accuracy]** (mixed-precision iterative refinement), in rigorous
form. Let $n \ge 1$, let the working model `m` have unit roundoff $u$ with $3nu < 1$, and let
the finer model `m'` have unit roundoff $\bar u$ with $(n + 1) \bar u < 1$. Let
$A \in \mathbb{R}^{n \times n}$ be nonsingular with $Ax = b$, let $L$, $U$ be computed LU
factors of $A$ in `m` with $u_{jj} \neq 0$ for every $j$, and let $x^{(k+1)}$ be a computed step
from $x^{(k)}$ with the residual computed in `m'` (`Refinement.RoundsStepLUMixed`) for every
$k$. Put
$$\theta = \gamma_{3n} \| |A^{-1}| \, |L| \, |U| \|_\infty, \qquad \rho = \frac{\theta + (u +
  (1 + u) \bar\gamma_{n+1}) \operatorname{cond}(A)}{1 - 2u - \theta}, \qquad \varphi = \frac{2
  (1 + u) \bar\gamma_{n+1} \| |A^{-1}| \, |A| \, |x| \|_\infty + u (1 + \theta)
  \|x\|_\infty}{1 - 2u - \theta},$$
where $\bar\gamma_{n+1}$ is the constant of `m'`. If $2\theta + (u + (1 + u) \bar\gamma_{n+1})
\operatorname{cond}(A) + 2u < 1$, then $\rho < 1$, and for every $k$
$$\|x - x^{(k+1)}\|_\infty \le \rho \|x - x^{(k)}\|_\infty + \varphi, \qquad \|x -
  x^{(k)}\|_\infty \le \rho^k \|x - x^{(0)}\|_\infty + \frac{\varphi}{1 - \rho},$$
and $\limsup_k \|x - x^{(k)}\|_\infty \le \varphi / (1 - \rho)$. Moreover, in "double the
working precision", that is, if $\bar u \le u^2$ and $2 (n + 1) \bar u \le 1$, the floor is of
the order of the working precision:
$$\varphi \le \frac{u \bigl(4 (1 + u)(n + 1) u \, \| |A^{-1}| \, |A| \, |x| \|_\infty + (1 +
  \theta) \|x\|_\infty\bigr)}{1 - 2u - \theta}.$$

This is the theorem's "until $\|x - \hat x_i\|_\infty / \|x\|_\infty \approx u$", which does not
depend on the condition number to first order in $u$. -/
theorem norm_sub_le_of_forall_roundsStepLUMixed [NeZero n] {m m' : RoundingModel ℝ}
    (hcard : ((3 * n : ℕ) : ℝ) * m.u < 1) (hcard' : ((n + 1 : ℕ) : ℝ) * m'.u < 1)
    {A L U : Matrix (Fin n) (Fin n) ℝ} {b x : Fin n → ℝ} (hA : IsUnit A) (hx : A *ᵥ x = b)
    (hLU : RoundsLU m A L U) (hd : ∀ j, U j j ≠ 0) {xs : ℕ → Fin n → ℝ}
    (hstep : ∀ k, RoundsStepLUMixed m m' A L U b (xs k) (xs (k + 1))) {θ ρ φ : ℝ}
    (hθ : θ = gamma m.u (3 * n) * ‖A⁻¹.abs * (L.abs * U.abs)‖)
    (hρ : ρ = (θ + (m.u + (1 + m.u) * gamma m'.u (n + 1)) * ‖A⁻¹.abs * A.abs‖)
      / (1 - 2 * m.u - θ))
    (hφ : φ = (2 * (1 + m.u) * gamma m'.u (n + 1) * ‖A⁻¹.abs *ᵥ (A.abs *ᵥ |x|)‖
      + m.u * (1 + θ) * ‖x‖) / (1 - 2 * m.u - θ))
    (hsmall : 2 * θ + (m.u + (1 + m.u) * gamma m'.u (n + 1)) * ‖A⁻¹.abs * A.abs‖ + 2 * m.u < 1) :
    ρ < 1 ∧ (∀ k, ‖x - xs (k + 1)‖ ≤ ρ * ‖x - xs k‖ + φ) ∧
      (∀ k, ‖x - xs k‖ ≤ ρ ^ k * ‖x - xs 0‖ + φ / (1 - ρ)) ∧
      limsup (fun k => ‖x - xs k‖) atTop ≤ φ / (1 - ρ) ∧
      (m'.u ≤ m.u ^ 2 → 2 * ((n + 1 : ℕ) * m'.u) ≤ 1 →
        φ ≤ m.u * (4 * (1 + m.u) * (n + 1) * m.u * ‖A⁻¹.abs *ᵥ (A.abs *ᵥ |x|)‖ + (1 + θ) * ‖x‖)
          / (1 - 2 * m.u - θ)) := by
  have hθ0 : 0 ≤ θ := by
    rw [hθ]; exact mul_nonneg (gamma_nonneg m.u_nonneg hcard) (norm_nonneg _)
  have hγ0 := gamma_nonneg m'.u_nonneg hcard'
  have hu0 := m.u_nonneg
  have hσ0 : 0 ≤ (m.u + (1 + m.u) * gamma m'.u (n + 1)) * ‖A⁻¹.abs * A.abs‖ := by positivity
  have hpos : 0 < 1 - 2 * m.u - θ := by linarith
  have hsmall' : θ + 2 * m.u < 1 := by linarith
  have hρ1 : ρ < 1 := by
    rw [hρ, div_lt_one hpos]; linarith
  have hρ0 : 0 ≤ ρ := by rw [hρ]; positivity
  have hφ0 : 0 ≤ φ := by
    rw [hφ]
    positivity
  have hrec : ∀ k, ‖x - xs (k + 1)‖ ≤ ρ * ‖x - xs k‖ + φ := fun k => by
    have h := norm_sub_le_of_roundsStepLUMixed hcard hcard' hA hx hLU hd (hstep k)
      (by rw [← hθ]; exact hsmall')
    rw [← hθ] at h
    rw [hρ, hφ]
    exact norm_sub_le_mul_add_of_mul_le hpos h
  refine ⟨hρ1, hrec, fun k =>
    le_pow_mul_add_div_of_forall_le_mul_add (a := fun k => ‖x - xs k‖) hρ0 hρ1 hφ0 hrec k,
    limsup_le_div_of_forall_le_mul_add hρ0 hρ1 hφ0 (fun k => norm_nonneg _) hrec,
    fun hu2 hn2 => ?_⟩
  rw [hφ]
  refine div_le_div_of_nonneg_right ?_ hpos.le
  have hγ : gamma m'.u (n + 1) ≤ 2 * ((n + 1 : ℕ) * m'.u) := gamma_le_two_mul m'.u_nonneg hn2
  have hγ' : gamma m'.u (n + 1) ≤ 2 * (n + 1) * m.u ^ 2 := by
    refine hγ.trans ?_
    push_cast
    nlinarith [(by positivity : (0 : ℝ) ≤ n + 1)]
  have h1 : 2 * (1 + m.u) * gamma m'.u (n + 1) * ‖A⁻¹.abs *ᵥ (A.abs *ᵥ |x|)‖
      ≤ 2 * (1 + m.u) * (2 * (n + 1) * m.u ^ 2) * ‖A⁻¹.abs *ᵥ (A.abs *ᵥ |x|)‖ := by
    gcongr
  nlinarith

end Convergence

end Refinement

/-! ### Scaling -/

namespace Matrix

variable {n K : Type*} [Fintype n] [DecidableEq n] [Field K]

/-- **Scaling a linear system** ([quarteroni2000numerical], §3.12.1). Let $K$ be a field, let
$A \in K^{n \times n}$, and let $D_1, D_2 \in K^{n \times n}$ be nonsingular. Then for all
$x, b \in K^n$,
$$Ax = b \iff (D_1 A D_2)(D_2^{-1} x) = D_1 b.$$

In the book $D_1$ and $D_2$ are diagonal: $D_1$ scales the equations and $D_2$ scales the
unknowns. Here they are arbitrary nonsingular matrices. Row scaling alone is the case $D_2 = I$. -/
theorem scaled_mulVec_eq_iff {D₁ D₂ : Matrix n n K} (h₁ : IsUnit D₁) (h₂ : IsUnit D₂)
    (A : Matrix n n K) (x b : n → K) :
    A *ᵥ x = b ↔ (D₁ * A * D₂) *ᵥ (D₂⁻¹ *ᵥ x) = D₁ *ᵥ b := by
  rw [mulVec_mulVec, Matrix.mul_assoc, mul_nonsing_inv _ ((isUnit_iff_isUnit_det D₂).1 h₂),
    Matrix.mul_one, ← mulVec_mulVec]
  exact (mulVec_injective_iff_isUnit.2 h₁).eq_iff.symm

end Matrix
