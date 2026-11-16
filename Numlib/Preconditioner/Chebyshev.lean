/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Krylov.Convergence.Polynomial
import Numlib.Krylov.Iterate
import Numlib.RingTheory.Polynomial.ChebyshevMinimax

/-!
# Chebyshev acceleration

Let $A$ be an operator on an inner product space, let $b$ be a right-hand side and $x_0$ an initial
guess, and let $0 < \alpha < \beta$. Chebyshev acceleration is the three-term iteration whose
residuals are $r_k = P_k(A) r_0$, where $P_k$ is the shifted Chebyshev polynomial of degree $k$ of
the interval $[\alpha, \beta]$, normalized by $P_k(0) = 1$ ([saad2003iterative], §12.3.2 and
Algorithm 12.1; [kress1998numerical], §4.4). With $\theta = (\beta + \alpha)/2$ and
$\delta = (\beta - \alpha)/2$,
$$P_k(t) = \frac{C_k((\theta - t)/\delta)}{C_k(\theta/\delta)},$$
where $C_k$ is the Chebyshev polynomial of the first kind. The method needs no parameters other than
$\alpha$ and $\beta$. One step costs one application of $A$ and no inner product, and this is the
practical reason to use the method.

The residual polynomial is `Polynomial.Chebyshev.shifted k α β 0` of
`Numlib.RingTheory.Polynomial.ChebyshevMinimax`. This module defines the iteration, proves that its
residuals are this polynomial applied to $r_0$, and deduces the convergence rate $\|r_k\| \le
\|r_0\| / C_k((\beta + \alpha)/(\beta - \alpha))$ for a symmetric $A$ whose quadratic form lies in
$[\alpha, \beta]$. Chebyshev acceleration is not optimal in the Krylov sense. Its iterate lies in
the same affine space $x_0 + \mathcal{K}_k(A, r_0)$ as the iterates of GMRES and CG, but it
minimizes nothing there. So the rate is only an upper bound, and a minimal-residual method is never
worse. This comparison is the standard argument for CG when inner products are affordable.

## Main definitions

* `Preconditioner.Chebyshev.State`: the state $(x_k, r_k, d_k, \rho_k)$ of Algorithm 12.1.
* `Preconditioner.Chebyshev.step`: one step of Algorithm 12.1.
* `Preconditioner.Chebyshev.iterate`: the state after $k$ steps.

## Main results

* `Preconditioner.Chebyshev.residual_iterate_eq`: $r_k = P_k(A) r_0$ with $P_k$ the shifted
  Chebyshev polynomial of $[\alpha, \beta]$.
* `Preconditioner.Chebyshev.mem_krylov_subspace_iterate_x_sub`:
  $x_k - x_0 \in \mathcal{K}_k(A, r_0)$.
* `Preconditioner.Chebyshev.norm_residual_iterate_le`: $\|r_k\| \le \|r_0\| / C_k((\beta +
  \alpha)/(\beta - \alpha))$.
* `Preconditioner.Chebyshev.norm_residual_iterate_le_pow`: $\|r_k\| \le 2 \bigl((\sqrt{\kappa} -
  1)/(\sqrt{\kappa} + 1)\bigr)^k \|r_0\|$ with $\kappa = \beta/\alpha$.
* `Preconditioner.Chebyshev.norm_residual_minRes_le_norm_residual_iterate`: a minimal-residual
  Krylov iterate of step $k$ has a residual no larger than $\|r_k\|$.

## Implementation notes

* The scalar sequences of (12.6)–(12.7) of [saad2003iterative] are `Preconditioner.Chebyshev.sigma`,
  $\sigma_k = C_k(\theta/\delta)$, and `Preconditioner.Chebyshev.rho`,
  $\rho_k = \sigma_k / \sigma_{k+1}$.
* `Preconditioner.Chebyshev.resPoly` and `Preconditioner.Chebyshev.dirPoly` are the polynomials
  $P_k$ and $Q_k$ with $r_k = P_k(A) r_0$ and $d_k = Q_k(A) r_0$. The proof rests on the identity
  $P_{k+1} = P_k - X Q_k$, the three-term recurrence of the residual polynomials
  (`Preconditioner.Chebyshev.resPoly_add_two`, which is (12.8) of [saad2003iterative]), and the
  scalar identity $\rho_{k+1} (2 \sigma_1 - \rho_k) = 1$ (`Preconditioner.Chebyshev.rho_succ_mul`).
* `Preconditioner.Chebyshev.resPoly_add_two` is a statement about `Polynomial.Chebyshev.shifted`,
  although it is stated here.
-/

open Polynomial Krylov
open Polynomial.Chebyshev (T shifted shifted_degree_le shifted_eval_self sSup_abs_eval_shifted
  one_div_eval_T_le_two_mul_pow one_le_eval_T)

namespace Preconditioner.Chebyshev

variable {θ δ : ℝ}

/-! ### The scalar sequences -/

/-- The **Chebyshev values** $\sigma_k = C_k(\theta/\delta)$ of (12.7) of [saad2003iterative], where
$C_k$ is the Chebyshev polynomial of the first kind. -/
noncomputable def sigma (θ δ : ℝ) (k : ℕ) : ℝ := (T ℝ (k : ℤ)).eval (θ / δ)

/-- The scalar $\rho_k = \sigma_k / \sigma_{k+1}$ of (12.6) of [saad2003iterative], which the
iteration carries in its state. -/
noncomputable def rho (θ δ : ℝ) (k : ℕ) : ℝ := sigma θ δ k / sigma θ δ (k + 1)

/-- By definition, $\rho_k = \sigma_k / \sigma_{k+1}$. -/
theorem rho_eq_div_sigma (θ δ : ℝ) (k : ℕ) : rho θ δ k = sigma θ δ k / sigma θ δ (k + 1) := rfl

/-- The first Chebyshev value is $\sigma_0 = 1$. -/
@[simp] theorem sigma_zero (θ δ : ℝ) : sigma θ δ 0 = 1 := by
  simp [sigma, Polynomial.Chebyshev.T_zero]

/-- The second Chebyshev value is $\sigma_1 = \theta/\delta$. -/
@[simp] theorem sigma_one (θ δ : ℝ) : sigma θ δ 1 = θ / δ := by
  simp [sigma, Polynomial.Chebyshev.T_one]

/-- The Chebyshev values satisfy the three-term recurrence (12.7) of [saad2003iterative]:
$$\sigma_{k+2} = 2 \frac{\theta}{\delta} \sigma_{k+1} - \sigma_k.$$
It follows from the recurrence of the Chebyshev polynomials `Polynomial.Chebyshev.T`. -/
theorem sigma_add_two (θ δ : ℝ) (k : ℕ) :
    sigma θ δ (k + 2) = 2 * (θ / δ) * sigma θ δ (k + 1) - sigma θ δ k := by
  have h2 : ((k + 2 : ℕ) : ℤ) = (k : ℤ) + 2 := by push_cast; ring
  have h1 : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by push_cast; ring
  simp [sigma, h1, h2, Polynomial.Chebyshev.T_add_two]

section Positive

variable (hδ : 0 < δ) (hθδ : δ < θ)
include hδ hθδ

/-- If $0 < \delta < \theta$, then $\sigma_1 = \theta/\delta \ge 1$. The interval
$[\theta - \delta, \theta + \delta]$ then lies to the right of $0$, and this makes every
$\sigma_k$ grow. -/
theorem one_le_sigma_one : 1 ≤ θ / δ := (one_le_div hδ).mpr hθδ.le

/-- If $0 < \delta < \theta$, then $\sigma_k \ge 1$ for every $k$, because a Chebyshev polynomial is
at least $1$ at points greater than or equal to $1$. -/
theorem one_le_sigma (k : ℕ) : 1 ≤ sigma θ δ k := one_le_eval_T (one_le_sigma_one hδ hθδ) k

/-- If $0 < \delta < \theta$, then $\sigma_k > 0$ for every $k$. -/
theorem sigma_pos (k : ℕ) : 0 < sigma θ δ k := lt_of_lt_of_le zero_lt_one (one_le_sigma hδ hθδ k)

/-- If $0 < \delta < \theta$, then $\sigma_k \neq 0$ for every $k$, so the quotients that define
$\rho_k$ are true divisions. -/
theorem sigma_ne_zero (k : ℕ) : sigma θ δ k ≠ 0 := (sigma_pos hδ hθδ k).ne'

/-- If $0 < \delta < \theta$, then $\rho_k > 0$ for every $k$. -/
theorem rho_pos (k : ℕ) : 0 < rho θ δ k :=
  div_pos (sigma_pos hδ hθδ k) (sigma_pos hδ hθδ (k + 1))

/-- If $0 < \delta < \theta$, then $\rho_0 = \delta/\theta$. -/
@[simp] theorem rho_zero : rho θ δ 0 = δ / θ := by
  have hθ : θ ≠ 0 := (hδ.trans hθδ).ne'
  rw [rho, sigma_zero, sigma_one]
  field_simp

/-- If $0 < \delta < \theta$, then $2 \sigma_1 - \rho_k = \sigma_{k+2} / \sigma_{k+1}$. This is the
form of the denominator in (12.6) of [saad2003iterative]. -/
theorem two_mul_sigma_one_sub_rho (k : ℕ) :
    2 * (θ / δ) - rho θ δ k = sigma θ δ (k + 2) / sigma θ δ (k + 1) := by
  have h1 := sigma_ne_zero hδ hθδ (k + 1)
  rw [rho, sigma_add_two]
  field_simp

/-- If $0 < \delta < \theta$, then $\rho_{k+1} = (2 \sigma_1 - \rho_k)^{-1}$. This is the recurrence
(12.6) of [saad2003iterative] with which the algorithm updates its scalar. -/
theorem rho_succ (k : ℕ) : rho θ δ (k + 1) = (2 * (θ / δ) - rho θ δ k)⁻¹ := by
  rw [two_mul_sigma_one_sub_rho hδ hθδ, inv_div, rho]

/-- If $0 < \delta < \theta$, then $\rho_{k+1} (2 \sigma_1 - \rho_k) = 1$. This identity turns the
three-term recurrence of the polynomials into the vector recurrence for the search direction. -/
theorem rho_succ_mul (k : ℕ) : rho θ δ (k + 1) * (2 * (θ / δ) - rho θ δ k) = 1 := by
  have h1 := sigma_ne_zero hδ hθδ (k + 1)
  have h2 := sigma_ne_zero hδ hθδ (k + 2)
  rw [two_mul_sigma_one_sub_rho hδ hθδ, rho]
  field_simp

end Positive

/-! ### The residual and direction polynomials -/

/-- The affine polynomial $t \mapsto (\theta - t)/\delta$ of §12.3.2 of [saad2003iterative], written
as $\theta/\delta - \delta^{-1} X$. -/
noncomputable def shift (θ δ : ℝ) : ℝ[X] := C (θ / δ) - C δ⁻¹ * X

/-- The **residual polynomial** $P_k$ of step $k$: the shifted Chebyshev polynomial
`Polynomial.Chebyshev.shifted k α β 0` of the interval $[\alpha, \beta] = [\theta - \delta,
\theta + \delta]$, normalized to the value $1$ at $0$. -/
noncomputable def resPoly (θ δ : ℝ) (k : ℕ) : ℝ[X] := shifted k (θ - δ) (θ + δ) 0

/-- The **direction polynomial** $Q_k$ of step $k$, so that $d_k = Q_k(A) r_0$. It is defined by
$Q_0 = \theta^{-1}$ and
$$Q_{k+1} = \rho_k \rho_{k+1} Q_k + \frac{2 \rho_{k+1}}{\delta} P_{k+1}.$$
-/
noncomputable def dirPoly (θ δ : ℝ) : ℕ → ℝ[X]
  | 0 => C θ⁻¹
  | k + 1 => C (rho θ δ k * rho θ δ (k + 1)) * dirPoly θ δ k +
      C (2 * rho θ δ (k + 1) / δ) * resPoly θ δ (k + 1)

/-- The residual polynomial $P_k$ has degree at most $k$, so the residual $r_k$ lies in the Krylov
subspace $\mathcal{K}_{k+1}(A, r_0)$. -/
theorem degree_resPoly_le (θ δ : ℝ) (k : ℕ) : (resPoly θ δ k).degree ≤ (k : WithBot ℕ) :=
  shifted_degree_le k (θ - δ) (θ + δ) 0

/-- If $\delta \neq 0$, the residual polynomial has the closed form
$P_k(t) = C_k((\theta - t)/\delta) / \sigma_k$. -/
private theorem eval_resPoly (hδ : δ ≠ 0) (k : ℕ) (t : ℝ) :
    (resPoly θ δ k).eval t = (T ℝ (k : ℤ)).eval (θ / δ - δ⁻¹ * t) / sigma θ δ k := by
  have h1 : θ + δ - (θ - δ) = 2 * δ := by ring
  have e2 : (θ + δ + (θ - δ)) / (θ + δ - (θ - δ)) = θ / δ := by rw [h1]; field_simp; ring
  have e3 : (2 : ℝ) / (θ + δ - (θ - δ)) = δ⁻¹ := by rw [h1]; field_simp
  rw [resPoly, Polynomial.Chebyshev.shifted, sigma]
  simp only [eval_mul, eval_C, eval_comp, eval_sub, eval_X, mul_zero, sub_zero, e2, e3]
  ring

/-- The residual polynomial of step $0$ is $P_0 = 1$. -/
@[simp] theorem resPoly_zero (θ δ : ℝ) : resPoly θ δ 0 = 1 := by
  simp [resPoly, Polynomial.Chebyshev.shifted, Polynomial.Chebyshev.T_zero]

/-- If $\delta \neq 0$ and $\theta \neq 0$, the first residual polynomial is
$P_1 = 1 - \theta^{-1} X$. This matches the first step $d_0 = \theta^{-1} r_0$. -/
theorem resPoly_one (hδ : δ ≠ 0) (hθ : θ ≠ 0) : resPoly θ δ 1 = 1 - C θ⁻¹ * X := by
  refine Polynomial.funext fun t => ?_
  rw [eval_resPoly hδ, sigma_one]
  simp only [Nat.cast_one, Polynomial.Chebyshev.T_one, eval_X, eval_sub, eval_one, eval_mul,
    eval_C]
  field_simp

/-- If $0 < \delta < \theta$, the residual polynomials satisfy the three-term recurrence (12.8) of
[saad2003iterative]:
$$P_{k+2} = 2 \rho_{k+1} \, \frac{\theta - X}{\delta} \, P_{k+1} - \rho_k \rho_{k+1} P_k.$$
It is the Chebyshev recurrence $C_{k+2}(s) = 2 s C_{k+1}(s) - C_k(s)$ divided by $\sigma_{k+2}$.
This recurrence is the reason why the vector recurrence of Algorithm 12.1 produces Chebyshev
residuals. The factor $(\theta - X)/\delta$ is `Preconditioner.Chebyshev.shift`. -/
theorem resPoly_add_two (hδ : 0 < δ) (hθδ : δ < θ) (k : ℕ) :
    resPoly θ δ (k + 2) =
      C (2 * rho θ δ (k + 1)) * (shift θ δ * resPoly θ δ (k + 1)) -
        C (rho θ δ k * rho θ δ (k + 1)) * resPoly θ δ k := by
  have h0 := sigma_ne_zero hδ hθδ k
  have h1 := sigma_ne_zero hδ hθδ (k + 1)
  have h2 := sigma_ne_zero hδ hθδ (k + 2)
  refine Polynomial.funext fun t => ?_
  have hT : (T ℝ ((k + 2 : ℕ) : ℤ)).eval (θ / δ - δ⁻¹ * t) =
      2 * (θ / δ - δ⁻¹ * t) * (T ℝ ((k + 1 : ℕ) : ℤ)).eval (θ / δ - δ⁻¹ * t) -
        (T ℝ (k : ℤ)).eval (θ / δ - δ⁻¹ * t) := by
    have e2 : ((k + 2 : ℕ) : ℤ) = (k : ℤ) + 2 := by push_cast; ring
    have e1 : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by push_cast; ring
    simp [e1, e2, Polynomial.Chebyshev.T_add_two]
  simp only [eval_sub, eval_mul, eval_C, eval_resPoly hδ.ne', shift, eval_X, hT, rho]
  field_simp

/-! ### The iteration -/

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  {A : E →ₗ[𝕜] E} {b x₀ : E}

/-- The **state of Algorithm 12.1** of [saad2003iterative]. A state consists of the iterate $x_k$,
the residual $r_k$, the search direction $d_k$ and the scalar
$\rho_k = \sigma_k / \sigma_{k+1}$. -/
@[ext]
structure State (E : Type*) where
  /-- The iterate $x_k$. -/
  x : E
  /-- The residual $r_k = b - A x_k$ (see `Preconditioner.Chebyshev.residual_eq`). -/
  r : E
  /-- The search direction $d_k$, so that $x_{k+1} = x_k + d_k$. -/
  d : E
  /-- The scalar $\rho_k = \sigma_k / \sigma_{k+1}$ of (12.6) of [saad2003iterative]. -/
  ρ : ℝ

/-- **One step of Algorithm 12.1** of [saad2003iterative]. Let $A$ be an operator and
$\theta, \delta$ real numbers. The step maps a state $(x, r, d, \rho)$ to the state
$(x', r', d', \rho')$ with
$$x' = x + d, \qquad r' = r - A d, \qquad \rho' = (2 \sigma_1 - \rho)^{-1}, \qquad d' = \rho
  \rho' d + \frac{2 \rho'}{\delta} r',$$
where $\sigma_1 = \theta/\delta$.

The step computes no inner product. The real scalars act on the vectors through the coercion
from $\mathbb{R}$ to the scalar field $\mathbb{K}$. Division by $0$ gives $0$ in Lean, so the
step is defined for all $\theta$ and $\delta$, and the results below assume
$0 < \delta < \theta$. -/
noncomputable def step (A : E →ₗ[𝕜] E) (θ δ : ℝ) (s : State E) : State E :=
  let r' := s.r - A s.d
  let ρ' := (2 * (θ / δ) - s.ρ)⁻¹
  { x := s.x + s.d
    r := r'
    d := ((s.ρ * ρ' : ℝ) : 𝕜) • s.d + ((2 * ρ' / δ : ℝ) : 𝕜) • r'
    ρ := ρ' }

/-- The **initial state** of Chebyshev acceleration: $x_0$, $r_0 = b - A x_0$,
$d_0 = \theta^{-1} r_0$ and $\rho_0 = \delta/\theta$. -/
noncomputable def init (A : E →ₗ[𝕜] E) (b x₀ : E) (θ δ : ℝ) : State E where
  x := x₀
  r := b - A x₀
  d := ((θ⁻¹ : ℝ) : 𝕜) • (b - A x₀)
  ρ := δ / θ

/-- The **state after $k$ steps** of Chebyshev acceleration: the $k$-fold application of
`Preconditioner.Chebyshev.step` to the initial state `Preconditioner.Chebyshev.init A b x₀ θ δ`.

The results for an interval $[\alpha, \beta]$ take $\theta = (\beta + \alpha)/2$ and
$\delta = (\beta - \alpha)/2$. The iterate, the residual, the direction and the scalar of step
$k$ are the fields of the state. -/
noncomputable def iterate (A : E →ₗ[𝕜] E) (b x₀ : E) (θ δ : ℝ) (k : ℕ) : State E :=
  (step A θ δ)^[k] (init A b x₀ θ δ)

/-- The state after $0$ steps is the initial state. -/
@[simp] theorem iterate_zero : iterate A b x₀ θ δ 0 = init A b x₀ θ δ := rfl

/-- The state after $k + 1$ steps is one `Preconditioner.Chebyshev.step` applied to the state after
$k$ steps. -/
theorem iterate_succ (k : ℕ) :
    iterate A b x₀ θ δ (k + 1) = step A θ δ (iterate A b x₀ θ δ k) :=
  Function.iterate_succ_apply' _ _ _

/-- A step moves the iterate along the search direction: $x' = x + d$. -/
theorem step_x (s : State E) : (step A θ δ s).x = s.x + s.d := rfl

/-- A step updates the residual by $r' = r - A d$. -/
theorem step_r (s : State E) : (step A θ δ s).r = s.r - A s.d := rfl

/-- A step updates the scalar by the recurrence (12.6) of [saad2003iterative],
$\rho' = (2 \sigma_1 - \rho)^{-1}$. -/
theorem step_ρ (s : State E) : (step A θ δ s).ρ = (2 * (θ / δ) - s.ρ)⁻¹ := rfl

/-- A step updates the search direction by the three-term recurrence
$d' = \rho \rho' d + (2 \rho'/\delta) r'$. -/
theorem step_d (s : State E) :
    (step A θ δ s).d = ((s.ρ * (step A θ δ s).ρ : ℝ) : 𝕜) • s.d +
      ((2 * (step A θ δ s).ρ / δ : ℝ) : 𝕜) • (step A θ δ s).r := rfl

/-- The residual field of every state is the true residual: $r_k = b - A x_k$. -/
theorem residual_eq (k : ℕ) :
    (iterate A b x₀ θ δ k).r = b - A (iterate A b x₀ θ δ k).x := by
  induction k with
  | zero => rfl
  | succ k ih => rw [iterate_succ, step_r, step_x, ih, map_add, sub_sub]

/-! ### The residual is a Chebyshev polynomial of the initial residual -/

/-- For an operator $A$ and a real polynomial $q$, $A \, q(A) v = (Xq)(A) v$. -/
private theorem apply_aeval (A : E →ₗ[𝕜] E) (q : ℝ[X]) (v : E) :
    A (aeval A (q.map (algebraMap ℝ 𝕜)) v) = aeval A ((X * q).map (algebraMap ℝ 𝕜)) v := by
  rw [Polynomial.map_mul, Polynomial.map_X, map_mul, aeval_X, Module.End.mul_apply]

/-- For real polynomials $p$ and $q$, $(p - q)(A) v = p(A) v - q(A) v$. -/
private theorem aeval_sub_apply (A : E →ₗ[𝕜] E) (p q : ℝ[X]) (v : E) :
    aeval A ((p - q).map (algebraMap ℝ 𝕜)) v =
      aeval A (p.map (algebraMap ℝ 𝕜)) v - aeval A (q.map (algebraMap ℝ 𝕜)) v := by
  rw [Polynomial.map_sub, map_sub, LinearMap.sub_apply]

/-- For a real number $c$ and a real polynomial $q$, $c \, q(A) v = (cq)(A) v$. -/
private theorem smul_aeval (A : E →ₗ[𝕜] E) (c : ℝ) (q : ℝ[X]) (v : E) :
    ((c : 𝕜)) • aeval A (q.map (algebraMap ℝ 𝕜)) v =
      aeval A ((C c * q).map (algebraMap ℝ 𝕜)) v := by
  rw [Polynomial.map_mul, Polynomial.map_C, map_mul, aeval_C, Module.End.mul_apply,
    Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply,
    RCLike.algebraMap_eq_ofReal]

/-- The invariant of Algorithm 12.1: $r_k = P_k(A) r_0$, $d_k = Q_k(A) r_0$, the scalar of the state
is $\rho_k$, and $P_{k+1} = P_k - X Q_k$. -/
private theorem iterate_invariant (A : E →ₗ[𝕜] E) (b x₀ : E) (hδ : 0 < δ) (hθδ : δ < θ) (k : ℕ) :
    (iterate A b x₀ θ δ k).r = aeval A ((resPoly θ δ k).map (algebraMap ℝ 𝕜)) (b - A x₀) ∧
      (iterate A b x₀ θ δ k).d =
        aeval A ((dirPoly θ δ k).map (algebraMap ℝ 𝕜)) (b - A x₀) ∧
      (iterate A b x₀ θ δ k).ρ = rho θ δ k ∧
      resPoly θ δ (k + 1) = resPoly θ δ k - X * dirPoly θ δ k := by
  have hθ : θ ≠ 0 := (hδ.trans hθδ).ne'
  induction k with
  | zero =>
      refine ⟨by simp [init], ?_, by simp [init, rho_zero hδ hθδ], ?_⟩
      · have h1 : aeval A ((dirPoly θ δ 0).map (algebraMap ℝ 𝕜)) (b - A x₀) =
            ((θ⁻¹ : ℝ) : 𝕜) • (b - A x₀) := by
          rw [dirPoly, Polynomial.map_C, aeval_C, Algebra.algebraMap_eq_smul_one,
            LinearMap.smul_apply, Module.End.one_apply, RCLike.algebraMap_eq_ofReal]
        rw [iterate_zero]
        exact h1.symm
      · rw [resPoly_one hδ.ne' hθ, resPoly_zero, dirPoly]
        ring
  | succ k ih =>
      obtain ⟨hr, hd, hρ, hP⟩ := ih
      have hρ' : (iterate A b x₀ θ δ (k + 1)).ρ = rho θ δ (k + 1) := by
        rw [iterate_succ, step_ρ, hρ, rho_succ hδ hθδ]
      have hr' : (iterate A b x₀ θ δ (k + 1)).r =
          aeval A ((resPoly θ δ (k + 1)).map (algebraMap ℝ 𝕜)) (b - A x₀) := by
        rw [iterate_succ, step_r, hr, hd, apply_aeval, hP, aeval_sub_apply]
      refine ⟨hr', ?_, hρ', ?_⟩
      · rw [iterate_succ, step_d, ← iterate_succ, hρ, hρ', hr', hd, smul_aeval, smul_aeval,
          dirPoly, Polynomial.map_add, map_add]
        rfl
      · have hXQ : X * dirPoly θ δ k = resPoly θ δ k - resPoly θ δ (k + 1) := by rw [hP]; ring
        have hkey : C (2 * rho θ δ (k + 1)) * C (θ / δ) =
            1 + C (rho θ δ k * rho θ δ (k + 1)) := by
          rw [← C_mul, ← C_1, ← C_add]
          congr 1
          linear_combination rho_succ_mul hδ hθδ k
        have hdiv : (C (2 * rho θ δ (k + 1) / δ) : ℝ[X]) =
            C (2 * rho θ δ (k + 1)) * C δ⁻¹ := by
          rw [← C_mul, div_eq_mul_inv]
        rw [resPoly_add_two hδ hθδ k, dirPoly, shift]
        linear_combination (resPoly θ δ (k + 1)) * hkey +
          (X * resPoly θ δ (k + 1)) * hdiv +
          C (rho θ δ k * rho θ δ (k + 1)) * hXQ

/-- Let $A$ be an operator on an inner product space over $\mathbb{R}$ or $\mathbb{C}$, let $b$ and
$x_0$ be vectors, and let $0 < \alpha < \beta$. Let $r_k$ be the residual after $k$ steps of
Chebyshev acceleration with $\theta = (\beta + \alpha)/2$ and $\delta = (\beta - \alpha)/2$.
Then
$$r_k = P_k(A) \, r_0, \qquad P_k(t) = \frac{C_k\bigl((\beta + \alpha - 2t)/(\beta -
  \alpha)\bigr)}{C_k\bigl((\beta + \alpha)/(\beta - \alpha)\bigr)},$$
where $r_0 = b - A x_0$ and $C_k$ is the Chebyshev polynomial of the first kind. This is the
residual polynomial of §12.3.2 of [saad2003iterative].

The polynomial $P_k$ is `Polynomial.Chebyshev.shifted k α β 0`. This identification lets
Chebyshev acceleration use the min–max optimality of `Polynomial.Chebyshev.shifted`. No symmetry
of $A$ is needed. -/
theorem residual_iterate_eq {α β : ℝ} (hα : 0 < α) (hαβ : α < β) (k : ℕ) :
    (iterate A b x₀ ((β + α) / 2) ((β - α) / 2) k).r =
      aeval A ((shifted k α β 0).map (algebraMap ℝ 𝕜)) (b - A x₀) := by
  have hδ : (0 : ℝ) < (β - α) / 2 := by linarith
  have hθδ : (β - α) / 2 < (β + α) / 2 := by linarith
  have h := (iterate_invariant A b x₀ hδ hθδ k).1
  rwa [resPoly, show (β + α) / 2 - (β - α) / 2 = α by ring,
    show (β + α) / 2 + (β - α) / 2 = β by ring] at h

/-! ### The iterate lies in the Krylov subspace -/

/-- The polynomial $\sum_{j < k} Q_j$, for which $x_k - x_0 = \bigl(\sum_{j < k} Q_j\bigr)(A) r_0$.
-/
private noncomputable def iterPoly (θ δ : ℝ) (k : ℕ) : ℝ[X] :=
  ∑ j ∈ Finset.range k, dirPoly θ δ j

/-- The direction polynomial $Q_k$ has degree at most $k$. -/
private theorem degree_dirPoly_le (k : ℕ) : (dirPoly θ δ k).degree ≤ (k : WithBot ℕ) := by
  induction k with
  | zero => simpa [dirPoly] using degree_C_le
  | succ k ih =>
      rw [dirPoly]
      refine (degree_add_le _ _).trans (max_le ?_ ?_)
      · refine (degree_mul_le _ _).trans ((add_le_add degree_C_le ih).trans ?_)
        rw [zero_add]
        exact_mod_cast Nat.le_succ k
      · refine (degree_mul_le _ _).trans
          ((add_le_add degree_C_le (degree_resPoly_le θ δ (k + 1))).trans ?_)
        rw [zero_add]

/-- The polynomial $\sum_{j < k} Q_j$ has degree less than $k$. -/
private theorem degree_iterPoly_lt (k : ℕ) : (iterPoly θ δ k).degree < (k : WithBot ℕ) := by
  induction k with
  | zero => simp [iterPoly]
  | succ k ih =>
      have hsum : iterPoly θ δ (k + 1) = iterPoly θ δ k + dirPoly θ δ k := by
        rw [iterPoly, Finset.sum_range_succ, iterPoly]
      rw [hsum]
      refine lt_of_le_of_lt (degree_add_le _ _) (max_lt ?_ ?_)
      · exact lt_of_lt_of_le ih (by exact_mod_cast Nat.le_succ k)
      · exact lt_of_le_of_lt (degree_dirPoly_le k) (by exact_mod_cast Nat.lt_succ_self k)

/-- The iterate is $x_k = x_0 + \bigl(\sum_{j < k} Q_j\bigr)(A) r_0$. -/
private theorem iterate_x_eq (A : E →ₗ[𝕜] E) (b x₀ : E) (hδ : 0 < δ) (hθδ : δ < θ) (k : ℕ) :
    (iterate A b x₀ θ δ k).x =
      x₀ + aeval A ((iterPoly θ δ k).map (algebraMap ℝ 𝕜)) (b - A x₀) := by
  induction k with
  | zero => simp [iterPoly, init]
  | succ k ih =>
      have hsum : iterPoly θ δ (k + 1) = iterPoly θ δ k + dirPoly θ δ k := by
        rw [iterPoly, Finset.sum_range_succ, iterPoly]
      rw [iterate_succ, step_x, ih, (iterate_invariant A b x₀ hδ hθδ k).2.1, hsum,
        Polynomial.map_add, map_add]
      simp [add_assoc]

/-- Let $0 < \alpha < \beta$, and let $x_k$ be the iterate after $k$ steps of Chebyshev acceleration
with $\theta = (\beta + \alpha)/2$ and $\delta = (\beta - \alpha)/2$. Then
$$x_k - x_0 \in \mathcal{K}_k(A, r_0), \qquad r_0 = b - A x_0.$$
So the iterate lies in the same affine space $x_0 + \mathcal{K}_k(A, r_0)$ as the iterate of
step $k$ of GMRES or CG, but it does not minimize anything there. -/
theorem mem_krylov_subspace_iterate_x_sub {α β : ℝ} (hα : 0 < α) (hαβ : α < β) (k : ℕ) :
    (iterate A b x₀ ((β + α) / 2) ((β - α) / 2) k).x - x₀ ∈ Krylov.subspace A (b - A x₀) k := by
  have hδ : (0 : ℝ) < (β - α) / 2 := by linarith
  have hθδ : (β - α) / 2 < (β + α) / 2 := by linarith
  rw [iterate_x_eq A b x₀ hδ hθδ, add_sub_cancel_left]
  exact (Krylov.mem_subspace_iff_exists_aeval A (b - A x₀)).2
    ⟨_, lt_of_le_of_lt degree_map_le (degree_iterPoly_lt k), rfl⟩

/-! ### The convergence rate -/

/-- The **convergence rate of Chebyshev acceleration**. Let $A$ be a symmetric operator on an inner
product space over $\mathbb{R}$ or $\mathbb{C}$ with
$$\alpha \|v\|^2 \le \operatorname{Re} \langle Av, v \rangle \le \beta \|v\|^2 \quad \text{for
  all } v,$$
where $0 < \alpha < \beta$. Let $r_k$ be the residual after $k$ steps of Chebyshev acceleration
with $\theta = (\beta + \alpha)/2$ and $\delta = (\beta - \alpha)/2$. Then
$$\|r_k\| \le \frac{1}{C_k\bigl((\beta + \alpha)/(\beta - \alpha)\bigr)} \, \|b - A x_0\|,$$
where $C_k$ is the Chebyshev polynomial of the first kind.

The factor is the min–max value of the interval $[\alpha, \beta]$. The hypothesis on $A$ is
`LinearMap.IsSymmetricBoundedBy`. -/
theorem norm_residual_iterate_le {α β : ℝ} (hA : A.IsSymmetricBoundedBy α β) (hα : 0 < α)
    (hαβ : α < β) (k : ℕ) :
    ‖(iterate A b x₀ ((β + α) / 2) ((β - α) / 2) k).r‖ ≤
      1 / (T ℝ (k : ℤ)).eval ((β + α) / (β - α)) * ‖b - A x₀‖ := by
  have hγ : (0 : ℝ) ∉ Set.Icc α β := fun h => absurd (Set.mem_Icc.mp h).1 (by linarith)
  have hT : (0 : ℝ) < (T ℝ (k : ℤ)).eval ((β + α) / (β - α)) := by
    refine lt_of_lt_of_le zero_lt_one (one_le_eval_T ?_ k)
    rw [le_div_iff₀ (by linarith : (0:ℝ) < β - α)]
    linarith
  have h := hA.norm_aeval_map_apply_le (shifted k α β 0) (b - A x₀)
  rw [sSup_abs_eval_shifted k hαβ hγ,
    show (β + α - 2 * (0 : ℝ)) / (β - α) = (β + α) / (β - α) by ring, abs_of_pos hT] at h
  rwa [residual_iterate_eq hα hαβ]

/-- The classical form of the rate. Under the hypotheses of
`Preconditioner.Chebyshev.norm_residual_iterate_le`, with $\kappa = \beta/\alpha$,
$$\|r_k\| \le 2 \left(\frac{\sqrt{\kappa} - 1}{\sqrt{\kappa} + 1}\right)^k \|b - A x_0\|.$$
-/
theorem norm_residual_iterate_le_pow {α β : ℝ} (hA : A.IsSymmetricBoundedBy α β) (hα : 0 < α)
    (hαβ : α < β) (k : ℕ) :
    ‖(iterate A b x₀ ((β + α) / 2) ((β - α) / 2) k).r‖ ≤
      2 * ((Real.sqrt (β / α) - 1) / (Real.sqrt (β / α) + 1)) ^ k * ‖b - A x₀‖ := by
  refine (norm_residual_iterate_le hA hα hαβ k).trans
    (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  have hκ : 1 < β / α := (one_lt_div hα).mpr hαβ
  have hne1 : β / α - 1 ≠ 0 := sub_ne_zero.mpr hκ.ne'
  have hne2 : β - α ≠ 0 := sub_ne_zero.mpr (by linarith : β ≠ α)
  have hrw : (β / α + 1) / (β / α - 1) = (β + α) / (β - α) := by
    rw [div_eq_div_iff hne1 hne2]
    field_simp
  have h := one_div_eval_T_le_two_mul_pow hκ k
  rwa [hrw] at h

/-- Let $A$ be an operator on an inner product space over $\mathbb{R}$ or $\mathbb{C}$, and let
$0 < \alpha < \beta$. Let $y$ be a minimal-residual iterate of step $k$, that is, $y$ minimizes
$\|b - Ay\|$ over $x_0 + \mathcal{K}_k(A, r_0)$. Then
$$\|b - Ay\| \le \|r_k\|,$$
where $r_k$ is the residual after $k$ steps of Chebyshev acceleration with
$\theta = (\beta + \alpha)/2$ and $\delta = (\beta - \alpha)/2$.

The Chebyshev iterate is one of the candidates in the minimization, by
`Preconditioner.Chebyshev.mem_krylov_subspace_iterate_x_sub`. This is why Chebyshev acceleration
is used where inner products are expensive, and why its analysis gives only an upper bound. The
minimal-residual iterate is `Krylov.IsMinResidualIterate`. No symmetry of $A$ is needed. -/
theorem norm_residual_minRes_le_norm_residual_iterate {α β : ℝ} (hα : 0 < α) (hαβ : α < β)
    {y : E} {k : ℕ} (hy : Krylov.IsMinResidualIterate A b x₀ k y) :
    ‖b - A y‖ ≤ ‖(iterate A b x₀ ((β + α) / 2) ((β - α) / 2) k).r‖ := by
  have hγ : (0 : ℝ) ∉ Set.Icc α β := fun h => absurd (Set.mem_Icc.mp h).1 (by linarith)
  rw [residual_iterate_eq hα hαβ]
  refine hy.norm_residual_le_norm_aeval _ (degree_map_le.trans (shifted_degree_le k α β 0)) ?_
  have h0 : (0 : 𝕜) = algebraMap ℝ 𝕜 0 := by simp
  rw [h0, eval_map, eval₂_at_apply, shifted_eval_self k hαβ hγ, map_one]

end Preconditioner.Chebyshev
