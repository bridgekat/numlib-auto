import Numlib.Krylov.Convergence.Polynomial
import Numlib.Krylov.Iterate
import Numlib.RingTheory.Polynomial.ChebyshevMinimax

/-!
# Chebyshev acceleration

The parameter-free three-term iteration whose residuals are the shifted Chebyshev polynomials of an
interval `[α, β]` enclosing the spectrum of a symmetric operator ([saad2003iterative], §12.3.2 and
Algorithm 12.1; [kress1998numerical], §4.4). One step costs one operator application and no inner
product at all, which is the practical point of the method.

The residual polynomial is already in the library: it is `Polynomial.Chebyshev.shifted k α β 0` of
`Numlib/RingTheory/Polynomial/ChebyshevMinimax`, which evaluates to `C_k((θ - t)/δ) / C_k(θ/δ)` for
`θ = (β + α)/2` and `δ = (β - α)/2`. So this module names the iteration (`Chebyshev.State`,
`Chebyshev.step`, `Chebyshev.iterate`), proves that its residuals are that polynomial applied to
`r₀` (`Chebyshev.residual_iterate_eq`), and reads off the rate from what is already proved about
`shifted`.

Chebyshev acceleration is *not* a Krylov-optimal method: its iterate lies in the same affine space
as GMRES and CG (`Chebyshev.mem_krylov_subspace_iterate_x_sub`) but minimizes nothing, which is why
`Chebyshev.norm_residual_iterate_le` is a one-sided bound and why a minimal-residual method is never
worse (`Chebyshev.norm_residual_minRes_le_norm_residual_iterate`). That comparison is the standard
argument for preferring CG when inner products are affordable.

## Implementation notes

The scalar sequences of [saad2003iterative] (12.6)–(12.7) are `Chebyshev.sigma`, `σ_k = C_k(θ/δ)`,
and `Chebyshev.rho`, `ρ_k = σ_k/σ_{k+1}`. `Chebyshev.resPoly` and `Chebyshev.dirPoly` are the
polynomials with `r_k = P_k(A) r₀` and `d_k = Q_k(A) r₀`; the identity that drives everything is
`P_{k+1} = P_k - X Q_k` together with the three-term recurrence of the residual polynomials
(`Chebyshev.resPoly_add_two`, the recurrence [saad2003iterative] writes as (12.8)) and the scalar
identity `ρ_{k+1} (2 σ₁ - ρ_k) = 1` (`Chebyshev.rho_succ_mul`).

`Chebyshev.resPoly_add_two` is really a statement about `Polynomial.Chebyshev.shifted` and belongs
beside it in `Numlib/RingTheory/Polynomial/ChebyshevMinimax`; it is proved here only because that
file was owned elsewhere while this one was written.
-/

open Polynomial Krylov
open Polynomial.Chebyshev (T shifted shifted_degree_le shifted_eval_self sSup_abs_eval_shifted
  one_div_eval_T_le_two_mul_pow one_le_eval_T)

namespace Preconditioner.Chebyshev

variable {θ δ : ℝ}

/-! ### The scalar sequences -/

/-- `σ_k = C_k(θ/δ)`, the Chebyshev values of [saad2003iterative] (12.7). -/
noncomputable def sigma (θ δ : ℝ) (k : ℕ) : ℝ := (T ℝ (k : ℤ)).eval (θ / δ)

/-- `ρ_k = σ_k/σ_{k+1}`, the scalar of [saad2003iterative] (12.6) that the iteration carries. -/
noncomputable def rho (θ δ : ℝ) (k : ℕ) : ℝ := sigma θ δ k / sigma θ δ (k + 1)

/-- The defining quotient of `ρ_k`, in a form `rw` can use. -/
theorem rho_eq_div_sigma (θ δ : ℝ) (k : ℕ) : rho θ δ k = sigma θ δ k / sigma θ δ (k + 1) := rfl

@[simp] theorem sigma_zero (θ δ : ℝ) : sigma θ δ 0 = 1 := by
  simp [sigma, Polynomial.Chebyshev.T_zero]

@[simp] theorem sigma_one (θ δ : ℝ) : sigma θ δ 1 = θ / δ := by
  simp [sigma, Polynomial.Chebyshev.T_one]

/-- The three-term recurrence of [saad2003iterative] (12.7), inherited from
`Polynomial.Chebyshev.T`. -/
theorem sigma_add_two (θ δ : ℝ) (k : ℕ) :
    sigma θ δ (k + 2) = 2 * (θ / δ) * sigma θ δ (k + 1) - sigma θ δ k := by
  have h2 : ((k + 2 : ℕ) : ℤ) = (k : ℤ) + 2 := by push_cast; ring
  have h1 : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by push_cast; ring
  simp [sigma, h1, h2, Polynomial.Chebyshev.T_add_two]

section Positive

variable (hδ : 0 < δ) (hθδ : δ < θ)
include hδ hθδ

/-- The Chebyshev argument `σ₁ = θ/δ` is at least `1`: the interval `[θ - δ, θ + δ]` lies to the
right of the origin, which is what makes every `σ_k` grow. -/
theorem one_le_sigma_one : 1 ≤ θ / δ := (one_le_div hδ).mpr hθδ.le

/-- Chebyshev polynomials are at least `1` outside `[-1, 1]`, so `1 ≤ σ_k`. -/
theorem one_le_sigma (k : ℕ) : 1 ≤ sigma θ δ k := one_le_eval_T (one_le_sigma_one hδ hθδ) k

/-- Every `σ_k` is positive. -/
theorem sigma_pos (k : ℕ) : 0 < sigma θ δ k := lt_of_lt_of_le zero_lt_one (one_le_sigma hδ hθδ k)

/-- Every `σ_k` is nonzero, so the quotients defining `ρ_k` are honest divisions. -/
theorem sigma_ne_zero (k : ℕ) : sigma θ δ k ≠ 0 := (sigma_pos hδ hθδ k).ne'

/-- Every `ρ_k` is positive. -/
theorem rho_pos (k : ℕ) : 0 < rho θ δ k :=
  div_pos (sigma_pos hδ hθδ k) (sigma_pos hδ hθδ (k + 1))

@[simp] theorem rho_zero : rho θ δ 0 = δ / θ := by
  have hθ : θ ≠ 0 := (hδ.trans hθδ).ne'
  rw [rho, sigma_zero, sigma_one]
  field_simp

/-- `2 σ₁ - ρ_k = σ_{k+2}/σ_{k+1}`, the shape of the denominator in [saad2003iterative] (12.6). -/
theorem two_mul_sigma_one_sub_rho (k : ℕ) :
    2 * (θ / δ) - rho θ δ k = sigma θ δ (k + 2) / sigma θ δ (k + 1) := by
  have h1 := sigma_ne_zero hδ hθδ (k + 1)
  rw [rho, sigma_add_two]
  field_simp

/-- The recurrence the algorithm uses to update its scalar, [saad2003iterative] (12.6). -/
theorem rho_succ (k : ℕ) : rho θ δ (k + 1) = (2 * (θ / δ) - rho θ δ k)⁻¹ := by
  rw [two_mul_sigma_one_sub_rho hδ hθδ, inv_div, rho]

/-- The identity that turns the polynomial three-term recurrence into the vector recurrence for the
search direction: `ρ_{k+1} (2 σ₁ - ρ_k) = 1`. -/
theorem rho_succ_mul (k : ℕ) : rho θ δ (k + 1) * (2 * (θ / δ) - rho θ δ k) = 1 := by
  have h1 := sigma_ne_zero hδ hθδ (k + 1)
  have h2 := sigma_ne_zero hδ hθδ (k + 2)
  rw [two_mul_sigma_one_sub_rho hδ hθδ, rho]
  field_simp

end Positive

/-! ### The residual and direction polynomials -/

/-- The affine map `t ↦ (θ - t)/δ` of [saad2003iterative] §12.3.2, as a polynomial. -/
noncomputable def shift (θ δ : ℝ) : ℝ[X] := C (θ / δ) - C δ⁻¹ * X

/-- The residual polynomial of the `k`-th Chebyshev step: `shifted k α β 0` for the interval `[α, β]
= [θ - δ, θ + δ]`. -/
noncomputable def resPoly (θ δ : ℝ) (k : ℕ) : ℝ[X] := shifted k (θ - δ) (θ + δ) 0

/-- The direction polynomial of the `k`-th Chebyshev step, so that `d_k = Q_k(A) r₀`. -/
noncomputable def dirPoly (θ δ : ℝ) : ℕ → ℝ[X]
  | 0 => C θ⁻¹
  | k + 1 => C (rho θ δ k * rho θ δ (k + 1)) * dirPoly θ δ k +
      C (2 * rho θ δ (k + 1) / δ) * resPoly θ δ (k + 1)

/-- The `k`-th residual polynomial has degree at most `k`, so the `k`-th residual lies in the `k`-th
Krylov subspace. -/
theorem degree_resPoly_le (θ δ : ℝ) (k : ℕ) : (resPoly θ δ k).degree ≤ (k : WithBot ℕ) :=
  shifted_degree_le k (θ - δ) (θ + δ) 0

/-- The residual polynomial in closed form: `P_k(t) = C_k((θ - t)/δ) / σ_k`. -/
private theorem eval_resPoly (hδ : δ ≠ 0) (k : ℕ) (t : ℝ) :
    (resPoly θ δ k).eval t = (T ℝ (k : ℤ)).eval (θ / δ - δ⁻¹ * t) / sigma θ δ k := by
  have h1 : θ + δ - (θ - δ) = 2 * δ := by ring
  have e2 : (θ + δ + (θ - δ)) / (θ + δ - (θ - δ)) = θ / δ := by rw [h1]; field_simp; ring
  have e3 : (2 : ℝ) / (θ + δ - (θ - δ)) = δ⁻¹ := by rw [h1]; field_simp
  rw [resPoly, Polynomial.Chebyshev.shifted, sigma]
  simp only [eval_mul, eval_C, eval_comp, eval_sub, eval_X, mul_zero, sub_zero, e2, e3]
  ring

@[simp] theorem resPoly_zero (θ δ : ℝ) : resPoly θ δ 0 = 1 := by
  simp [resPoly, Polynomial.Chebyshev.shifted, Polynomial.Chebyshev.T_zero]

/-- The first residual polynomial is `1 - t/θ`, matching the first step `d₀ = θ⁻¹ r₀`. -/
theorem resPoly_one (hδ : δ ≠ 0) (hθ : θ ≠ 0) : resPoly θ δ 1 = 1 - C θ⁻¹ * X := by
  refine Polynomial.funext fun t => ?_
  rw [eval_resPoly hδ, sigma_one]
  simp only [Nat.cast_one, Polynomial.Chebyshev.T_one, eval_X, eval_sub, eval_one, eval_mul,
    eval_C]
  field_simp

/-- The three-term recurrence of the residual polynomials, [saad2003iterative] (12.8). It is the
Chebyshev recurrence `C_{k+2} = 2 t C_{k+1} - C_k` divided by `σ_{k+2}`, and it is what makes the
vector recurrence of Algorithm 12.1 produce Chebyshev residuals. -/
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

/-- The state of [saad2003iterative] Algorithm 12.1: iterate, residual, search direction and the
scalar `ρ_k = σ_k/σ_{k+1}`. -/
@[ext]
structure State (E : Type*) where
  /-- The iterate `x_k`. -/
  x : E
  /-- The residual `r_k = b - A x_k` (see `Chebyshev.residual_eq`). -/
  r : E
  /-- The search direction `d_k`, so that `x_{k+1} = x_k + d_k`. -/
  d : E
  /-- The scalar `ρ_k = σ_k/σ_{k+1}` of [saad2003iterative] (12.6). -/
  ρ : ℝ

/-- One step of [saad2003iterative] Algorithm 12.1: `x' = x + d`, `r' = r - A d`, `ρ' = (2 σ₁ -
ρ)⁻¹` and `d' = ρ ρ' • d + (2 ρ'/δ) • r'`, with `σ₁ = θ/δ`. No inner product is computed. -/
noncomputable def step (A : E →ₗ[𝕜] E) (θ δ : ℝ) (s : State E) : State E :=
  let r' := s.r - A s.d
  let ρ' := (2 * (θ / δ) - s.ρ)⁻¹
  { x := s.x + s.d
    r := r'
    d := ((s.ρ * ρ' : ℝ) : 𝕜) • s.d + ((2 * ρ' / δ : ℝ) : 𝕜) • r'
    ρ := ρ' }

/-- The initial state `x₀`, `r₀ = b - A x₀`, `d₀ = θ⁻¹ r₀`, `ρ₀ = δ/θ`. -/
noncomputable def init (A : E →ₗ[𝕜] E) (b x₀ : E) (θ δ : ℝ) : State E where
  x := x₀
  r := b - A x₀
  d := ((θ⁻¹ : ℝ) : 𝕜) • (b - A x₀)
  ρ := δ / θ

/-- The `k`-th state of Chebyshev acceleration. -/
noncomputable def iterate (A : E →ₗ[𝕜] E) (b x₀ : E) (θ δ : ℝ) (k : ℕ) : State E :=
  (step A θ δ)^[k] (init A b x₀ θ δ)

@[simp] theorem iterate_zero : iterate A b x₀ θ δ 0 = init A b x₀ θ δ := rfl

/-- The recurrence: state `k + 1` is one `Chebyshev.step` applied to state `k`. -/
theorem iterate_succ (k : ℕ) :
    iterate A b x₀ θ δ (k + 1) = step A θ δ (iterate A b x₀ θ δ k) :=
  Function.iterate_succ_apply' _ _ _

/-- The iterate advances along the search direction, `x' = x + d`. -/
theorem step_x (s : State E) : (step A θ δ s).x = s.x + s.d := rfl

/-- The residual follows the iterate, `r' = r - A d`. -/
theorem step_r (s : State E) : (step A θ δ s).r = s.r - A s.d := rfl

/-- The scalar recurrence of [saad2003iterative] (12.6), `ρ' = (2 σ₁ - ρ)⁻¹`. -/
theorem step_ρ (s : State E) : (step A θ δ s).ρ = (2 * (θ / δ) - s.ρ)⁻¹ := rfl

/-- The three-term recurrence for the search direction, `d' = ρ ρ' d + (2 ρ'/δ) r'`. -/
theorem step_d (s : State E) :
    (step A θ δ s).d = ((s.ρ * (step A θ δ s).ρ : ℝ) : 𝕜) • s.d +
      ((2 * (step A θ δ s).ρ / δ : ℝ) : 𝕜) • (step A θ δ s).r := rfl

/-- The state's residual field is the true residual. -/
theorem residual_eq (k : ℕ) :
    (iterate A b x₀ θ δ k).r = b - A (iterate A b x₀ θ δ k).x := by
  induction k with
  | zero => rfl
  | succ k ih => rw [iterate_succ, step_r, step_x, ih, map_add, sub_sub]

/-! ### The residual is a Chebyshev polynomial of the initial residual -/

/-- Applying `A` after a polynomial in `A` multiplies the polynomial by `X`. -/
private theorem apply_aeval (A : E →ₗ[𝕜] E) (q : ℝ[X]) (v : E) :
    A (aeval A (q.map (algebraMap ℝ 𝕜)) v) = aeval A ((X * q).map (algebraMap ℝ 𝕜)) v := by
  rw [Polynomial.map_mul, Polynomial.map_X, map_mul, aeval_X, Module.End.mul_apply]

/-- Evaluation at a vector of a polynomial in `A` respects subtraction of polynomials. -/
private theorem aeval_sub_apply (A : E →ₗ[𝕜] E) (p q : ℝ[X]) (v : E) :
    aeval A ((p - q).map (algebraMap ℝ 𝕜)) v =
      aeval A (p.map (algebraMap ℝ 𝕜)) v - aeval A (q.map (algebraMap ℝ 𝕜)) v := by
  rw [Polynomial.map_sub, map_sub, LinearMap.sub_apply]

/-- A real scalar multiple of `q(A) v` is `(C c * q)(A) v`. -/
private theorem smul_aeval (A : E →ₗ[𝕜] E) (c : ℝ) (q : ℝ[X]) (v : E) :
    ((c : 𝕜)) • aeval A (q.map (algebraMap ℝ 𝕜)) v =
      aeval A ((C c * q).map (algebraMap ℝ 𝕜)) v := by
  rw [Polynomial.map_mul, Polynomial.map_C, map_mul, aeval_C, Module.End.mul_apply,
    Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply,
    RCLike.algebraMap_eq_ofReal]

/-- The invariant of Algorithm 12.1: the residual, the direction and the scalar are the Chebyshev
data, and the residual polynomials satisfy `P_{k+1} = P_k - X Q_k`. -/
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

/-- The residual of the `k`-th Chebyshev step is the shifted Chebyshev polynomial of `[α, β]`
applied to the initial residual ([saad2003iterative] §12.3.2): with `θ = (β + α)/2` and `δ = (β -
α)/2`, `r_k = (shifted k α β 0)(A) r₀`. This is the identification that makes Chebyshev acceleration
inherit the min–max optimality already proved for `Polynomial.Chebyshev.shifted`. -/
theorem residual_iterate_eq {α β : ℝ} (hα : 0 < α) (hαβ : α < β) (k : ℕ) :
    (iterate A b x₀ ((β + α) / 2) ((β - α) / 2) k).r =
      aeval A ((shifted k α β 0).map (algebraMap ℝ 𝕜)) (b - A x₀) := by
  have hδ : (0 : ℝ) < (β - α) / 2 := by linarith
  have hθδ : (β - α) / 2 < (β + α) / 2 := by linarith
  have h := (iterate_invariant A b x₀ hδ hθδ k).1
  rwa [resPoly, show (β + α) / 2 - (β - α) / 2 = α by ring,
    show (β + α) / 2 + (β - α) / 2 = β by ring] at h

/-! ### The iterate lies in the Krylov subspace -/

/-- The polynomial with `x_k - x₀ = Q(A) r₀`. -/
private noncomputable def iterPoly (θ δ : ℝ) (k : ℕ) : ℝ[X] :=
  ∑ j ∈ Finset.range k, dirPoly θ δ j

/-- The `k`-th direction polynomial has degree at most `k`. -/
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

/-- The polynomial carrying `x_k - x₀` has degree below `k`, which is exactly membership in the
`k`-th Krylov subspace. -/
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

/-- The iterate is `x₀` plus the running sum of the direction polynomials applied to `r₀`. -/
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

/-- The Chebyshev iterate lies in the same affine space `x₀ + 𝒦_k(A, r₀)` as the `k`-th GMRES or CG
iterate; it simply does not minimize anything there. -/
theorem mem_krylov_subspace_iterate_x_sub {α β : ℝ} (hα : 0 < α) (hαβ : α < β) (k : ℕ) :
    (iterate A b x₀ ((β + α) / 2) ((β - α) / 2) k).x - x₀ ∈ Krylov.subspace A (b - A x₀) k := by
  have hδ : (0 : ℝ) < (β - α) / 2 := by linarith
  have hθδ : (β - α) / 2 < (β + α) / 2 := by linarith
  rw [iterate_x_eq A b x₀ hδ hθδ, add_sub_cancel_left]
  exact (Krylov.mem_subspace_iff_exists_aeval A (b - A x₀)).2
    ⟨_, lt_of_le_of_lt degree_map_le (degree_iterPoly_lt k), rfl⟩

/-! ### The convergence rate -/

/-- The convergence rate of Chebyshev acceleration: for a symmetric `A` whose quadratic form lies in
`[α, β]` with `0 < α < β`, the `k`-th residual satisfies `‖r_k‖ ≤ (1 / C_k((β + α)/(β - α))) ‖r₀‖`,
which is the min–max value of the interval. -/
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

/-- The classical `√κ` form of the rate: `‖r_k‖ ≤ 2 ((√κ - 1)/(√κ + 1))^k ‖r₀‖` for `κ = β/α`. -/
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

/-- A minimal-residual Krylov iterate of the same degree is never worse than the Chebyshev iterate,
because the Chebyshev residual polynomial is only one competitor in the minimization. This is why
Chebyshev acceleration is used where inner products are expensive, and why its analysis is a
one-sided bound. -/
theorem norm_residual_minRes_le_norm_residual_iterate {α β : ℝ} (hα : 0 < α) (hαβ : α < β)
    {y : E} {k : ℕ} (hy : Krylov.IsMinResidualIterate A b x₀ k y) :
    ‖b - A y‖ ≤ ‖(iterate A b x₀ ((β + α) / 2) ((β - α) / 2) k).r‖ := by
  have hγ : (0 : ℝ) ∉ Set.Icc α β := fun h => absurd (Set.mem_Icc.mp h).1 (by linarith)
  rw [residual_iterate_eq hα hαβ]
  refine hy.norm_residual_le_norm_aeval _ (degree_map_le.trans (shifted_degree_le k α β 0)) ?_
  have h0 : (0 : 𝕜) = algebraMap ℝ 𝕜 0 := by simp
  rw [h0, eval_map, eval₂_at_apply, shifted_eval_self k hαβ hγ, map_one]

end Preconditioner.Chebyshev
