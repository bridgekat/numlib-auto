import Mathlib.Analysis.InnerProductSpace.Adjoint
import Numlib.Analysis.Normed.Ring.CondNumber
import Numlib.FloatingPoint.LU
import Numlib.FloatingPoint.Stationary
import Numlib.Stationary.Basic

/-!
# Iterative refinement, scaling and condition estimation

The devices of [quarteroni2000numerical] §3.11–3.12 for improving and assessing the accuracy of
a direct solve.

* **Iterative refinement** (§3.12.2) with an approximate inverse `C` — in practice the LU solve
  of §3.12.2, `C = luSolve` as a linear map — is the step `x ↦ x + C (b - A x)`
  (`Refinement.step`), which is the stationary iteration `Stationary.step (1 - C A) (C b)` of
  `Numlib/Stationary/Basic` (`Refinement.step_eq_stationary_step`). Hence its error after `k`
  steps is `(1 - C A)^k (x₀ - x*)` (`Refinement.iterate_sub_eq`), it contracts by `‖1 - C A‖`
  per step (`Refinement.norm_iterate_sub_le`), it is exact after one step when `C A = 1`
  (`Refinement.step_eq_of_eq_inverse`, the book's "in absence of rounding errors, the process
  would stop at the first step"), and, on a finite-dimensional complex space with `C` onto, it
  converges for every right-hand side and start iff `ρ(1 - C A) < 1`
  (`Refinement.forall_tendsto_iff_spectralRadius_lt_one`). The quantity `‖1 - C A‖` is the
  `‖R‖` of the book's Property 3.1 with the factors in the other order.
* **One computed step** (§3.12.2 again), the rigorous content those asymptotics summarize: the
  error identity `(A + ΔA)(x - ŷ) = ΔA (x - x̂) - ξ - (A + ΔA) η` for a residual, a solve and an
  update each carrying a backward error (`Refinement.step_error`), its `∞`-norm form
  (`Refinement.norm_step_error_le`), and its instantiation in the relational rounding model of
  `Numlib/FloatingPoint`, where the three errors are bounded by `γ_{3n} |L| |U|`,
  `γ_{n+1}(|A| |x̂| + |b|)` and `u |x̂ + ẑ|` (`Refinement.step_error_fp`). These are stated on
  matrices over `ℝ`, since the rounding models are.
* **Convergence in finite precision** ([higham2002accuracy] §12.1, Theorems 12.1–12.2, the
  rigorous form of the book's `ρ ≃ 2 n cond(A, x) u` in fixed precision and `ρ ≃ u` in mixed
  precision): solving the error identity with `A⁻¹` in place of `(A + ΔA)⁻¹` gives the recursion
  `(1 - 2u - θ) ‖x - ŷ‖_∞ ≤ (θ + α cond(A)) ‖x - x̂‖_∞ + β cond(A, x) ‖x‖_∞ + u (1 + θ) ‖x‖_∞`
  with `θ = γ ‖|A⁻¹| W‖_∞` (`Refinement.norm_step_error_le_of_abs_le`), which for the LU solve
  reads with `θ = γ_{3n} ‖|A⁻¹| |L| |U|‖_∞` and `α = γ_{n+1}`, `β = 2 γ_{n+1}` in fixed
  precision (`Refinement.norm_sub_le_of_roundsStepLU`) or `α = u + (1 + u) γ̄_{n+1}`,
  `β = 2 (1 + u) γ̄_{n+1}` with the constant `γ̄` of the finer model in mixed precision
  (`Refinement.norm_sub_le_of_roundsStepLUMixed`); iterating gives the contraction by
  `ρ = (θ + α cond(A)) / (1 - 2u - θ)` down to the limiting accuracy `φ / (1 - ρ)`
  (`Refinement.norm_sub_le_of_forall_roundsStepLU`,
  `Refinement.norm_sub_le_of_forall_roundsStepLUMixed`), which is `≈ 2 n cond(A, x) u` in
  fixed precision and `≈ u` in mixed precision. The computed steps are the predicates
  `Refinement.RoundsStepLU` and `Refinement.RoundsStepLUMixed`.
* **Scaling** (§3.12.1): `A x = b ↔ (D₁ A D₂) y = D₁ b` with `y = D₂⁻¹ x` for nonsingular `D₁`,
  `D₂` (`Matrix.scaled_mulVec_eq_iff`), diagonal in the book and arbitrary here.
* **Condition estimation** (§3.11): the basic inequality `‖A⁻¹ d‖ / ‖d‖ ≤ ‖A⁻¹‖`
  (`norm_apply_div_le_norm_inverse`), the estimate `K̂(A) = ‖A‖ ‖y‖ / ‖x‖` from the probe `d`,
  `A† x = d`, `A y = x` ((3.70), `condEstimate`, on a Hilbert space where the adjoint lives), and
  its one property, `K̂(A) ≤ K(A)` (`condEstimate_le_condNumber`). The lookahead heuristic
  (3.71)–(3.72) that chooses `d` is an algorithm with no theorem attached and is not formalized.

Stated on a normed space (`E →L[𝕜] E`, `NormedRing.condNumber`) where possible, on matrices only
for scaling.
-/

open Filter Topology NormedRing

/-! ### Iterative refinement -/

namespace Refinement

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- **One step of iterative refinement** with the approximate inverse `C`
([quarteroni2000numerical] §3.12.2, steps 1–3): compute the residual `b - A x`, solve for the
correction with `C`, update. -/
def step (C A : E →L[𝕜] E) (b x : E) : E := x + C (b - A x)

variable (C A : E →L[𝕜] E) (b : E)

/-- Iterative refinement is the stationary iteration with iteration operator `1 - C A` and
constant `C b`. -/
theorem step_eq_stationary_step : step C A b = Stationary.step (1 - C * A) (C b) := by
  funext x
  simp only [step, Stationary.step, sub_apply, one_apply_eq_self, mul_apply_eq_comp, map_sub]
  abel

variable {C A b}

/-- **Exact arithmetic stops after one step**: if `C A = 1` (in particular `C = A⁻¹`) and
`A x* = b`, one refinement step from any `x` lands on `x*`. -/
theorem step_eq_of_eq_inverse (hCA : C * A = 1) {xs : E} (hxs : A xs = b) (x : E) :
    step C A b x = xs := by
  have h : C (A (xs - x)) = xs - x := by
    change (C * A) (xs - x) = xs - x
    rw [hCA, one_apply_eq_self]
  rw [step, ← hxs, ← map_sub, h]
  abel

/-- **Error propagation**: the error after `k` refinement steps is `(1 - C A)^k` applied to the
initial error, for any solution `x*` of `A x* = b`. -/
theorem iterate_sub_eq {xs : E} (hxs : A xs = b) (x₀ : E) (k : ℕ) :
    (step C A b)^[k] x₀ - xs = ((1 - C * A) ^ k) (x₀ - xs) := by
  rw [step_eq_stationary_step]
  refine Stationary.step_iterate_sub (1 - C * A) (C b) ?_ x₀ k
  rw [sub_apply, one_apply_eq_self]
  change xs - C (A xs) + C b = xs
  rw [hxs]
  abel

/-- `‖G ^ k‖ ≤ ‖G‖ ^ k` for operators, including `k = 0`, where `‖1‖ ≤ 1` holds even on a
trivial space. -/
theorem norm_pow_le_pow_norm (G : E →L[𝕜] E) (k : ℕ) : ‖G ^ k‖ ≤ ‖G‖ ^ k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [pow_zero, pow_zero]
    exact ContinuousLinearMap.norm_id_le
  · exact norm_pow_le' G hk

/-- **Linear convergence of iterative refinement**: the error after `k` steps is at most
`‖1 - C A‖ ^ k` times the initial error, so the iteration converges from every start when
`‖1 - C A‖ < 1`. Bounds of the type `‖1 - C A‖ ≤ ‖C‖ ‖A - C⁻¹‖` relate this to the backward a
priori analysis of [quarteroni2000numerical] Property 3.1. -/
theorem norm_iterate_sub_le {xs : E} (hxs : A xs = b) (x₀ : E) (k : ℕ) :
    ‖(step C A b)^[k] x₀ - xs‖ ≤ ‖1 - C * A‖ ^ k * ‖x₀ - xs‖ := by
  rw [iterate_sub_eq hxs x₀ k]
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right (norm_pow_le_pow_norm _ k) (norm_nonneg _))

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- **Convergence of iterative refinement iff `ρ(1 - C A) < 1`** ([quarteroni2000numerical]
§3.12.2 through [saad2003iterative] Theorem 4.1): on a finite-dimensional complex space, and
for an approximate inverse `C` that is onto (as the LU solve is), refinement converges for every
right-hand side and every start iff the spectral radius of `1 - C A` is less than one. The
surjectivity of `C` is needed for the "only if": with `C = 0` the iteration is constant, hence
convergent, while `ρ(1 - 0) = 1`. -/
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

/-! ### The error of one computed refinement step

`Refinement.step` is the step in exact arithmetic; what an implementation computes is something
else, and the three results here are the error analysis of one computed step. They are stated on
matrices over `ℝ`, because the rounding models of `Numlib/FloatingPoint` are. -/

namespace Refinement

open Matrix

variable {n : ℕ}

/-- **The error of one computed refinement step, exactly** ([quarteroni2000numerical] §3.12.2,
[higham2002accuracy] §12.1). Let `x` solve `A x = b`, let `xhat` be the current iterate, let the
computed residual be `rhat = b - A xhat + ξ`, let the computed correction `zhat` solve the
perturbed system `(A + ΔA) zhat = rhat` — which is what a solve with computed `LU` factors
delivers, [quarteroni2000numerical] (3.64) — and let the computed update be
`yhat = xhat + zhat + η`. Then

`(A + ΔA) (x - yhat) = ΔA (x - xhat) - ξ - (A + ΔA) η`.

Every term on the right is small: `ΔA` is the backward error of the solve, `ξ` that of the residual
and `η` that of the update, so the new error is the old error multiplied by `(A + ΔA)⁻¹ ΔA` plus a
floor of the size of the rounding errors. This is the algebraic core of the convergence claim of
[quarteroni2000numerical] §3.12.2 and of [higham2002accuracy] Theorems 12.1–12.2. It is an
identity: no hypothesis on the sizes of `ΔA`, `ξ`, `η` is used. -/
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
/-- **The error recursion of a computed refinement step, in the `∞`-norm.** With the data of
`step_error` and `A + ΔA` nonsingular,

`‖x - yhat‖_∞ ≤ ‖(A + ΔA)⁻¹ ΔA‖_∞ ‖x - xhat‖_∞ + ‖(A + ΔA)⁻¹‖_∞ ‖ξ‖_∞ + ‖η‖_∞`:

the error is reduced by the factor `‖(A + ΔA)⁻¹ ΔA‖_∞` down to a floor set by the residual and
update roundings. With `|ΔA| ≤ γ_{3n} |L| |U|` from the LU backward error the factor is at most
`γ_{3n} ‖ |(A + ΔA)⁻¹| |L| |U| ‖_∞`, which is the quantity [quarteroni2000numerical] §3.12.2 asks
to be "sufficiently small", with `(A + ΔA)⁻¹` in place of `A⁻¹`. -/
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
/-- **One computed refinement step in the relational rounding model**
([quarteroni2000numerical] §3.12.2, steps 1–3; [higham2002accuracy] §12.1), with the three backward
errors named. The residual is computed as an affine step
(`FloatingPoint.RoundsAffineStep m (-A) b xhat rhat`), the correction by a solve with the computed
factors `L`, `U` of `A` (`FloatingPoint.RoundsLU` and the two substitutions), and the update
entrywise. Then there are `ΔA`, `ξ`, `η` with

`|ΔA| ≤ γ_{3n} |L| |U|`, `|ξ| ≤ γ_{n+1} (|A| |xhat| + |b|)`, `|η_i| ≤ u |xhat_i + zhat_i|`

satisfying the error identity of `step_error`. This is the rigorous content behind the asymptotic
convergence factors `ρ ≃ 2n cond(A, x) u` (fixed precision) and `ρ ≃ u` (mixed precision) that
[quarteroni2000numerical] §3.12.2 quotes from [higham2002accuracy] Theorems 12.1–12.2; the
theorems themselves are `norm_sub_le_of_forall_roundsStepLU` and
`norm_sub_le_of_forall_roundsStepLUMixed` below. -/
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

/-! ### The convergence of iterative refinement in finite precision

[higham2002accuracy] §12.1, Theorems 12.1–12.2, in rigorous form: the one-step recursion
`‖x - ŷ‖_∞ ≤ ρ ‖x - x̂‖_∞ + φ` with explicit `ρ` and `φ` (`norm_step_error_le_of_abs_le`, the
`∞`-norm form of Higham's (12.5), for any solver with `|ΔA| ≤ γ W` and any residual with
`|ξ| ≤ α |A| |x - x̂| + β |A| |x|`), its two instances for the LU solve with residuals in the
working precision (`norm_sub_le_of_roundsStepLU`, Theorem 12.2) and in a finer precision
(`norm_sub_le_of_roundsStepLUMixed`, Theorem 12.1), and the iterated statements with the
limiting accuracy `φ / (1 - ρ)` (`norm_sub_le_of_forall_roundsStepLU`,
`norm_sub_le_of_forall_roundsStepLUMixed`). The computed steps are the predicates `RoundsStepLU`
and `RoundsStepLUMixed`, the latter carrying two rounding models. -/

section Convergence

open FloatingPoint
open scoped Matrix.Norms.Operator

/-- A perturbed contraction: a real sequence with `a (k + 1) ≤ ρ a k + c`, `0 ≤ ρ < 1`, `0 ≤ c`,
satisfies `a k ≤ ρ ^ k a 0 + c / (1 - ρ)`. -/
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

/-- The limiting value of a perturbed contraction: a nonnegative real sequence with
`a (k + 1) ≤ ρ a k + c`, `0 ≤ ρ < 1`, `0 ≤ c`, has `limsup a ≤ c / (1 - ρ)`. -/
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

/-- An entrywise bound on a matrix bounds its action on nonnegative vectors. -/
theorem _root_.Matrix.EntrywiseLE.mulVec_le_of_nonneg {M N : Matrix (Fin n) (Fin n) ℝ}
    (hMN : M ≤ₑ N) {w : Fin n → ℝ} (hw : 0 ≤ w) : M *ᵥ w ≤ N *ᵥ w := by
  refine Pi.le_def.2 fun i => ?_
  simp only [mulVec_apply_eq_sum]
  exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hMN i j) (hw j)

/-- The residual error in the form of [higham2002accuracy] (12.2): a bound
`|ξ| ≤ c (|A| |x̂| + |b|)` on the error of a computed residual of `A x = b` at `x̂` is the bound
`|ξ| ≤ c |A| |x - x̂| + 2 c |A| |x|` in terms of the error `x - x̂` and the solution `x`. -/
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
`∞`-norm. With the data of `step_error` — `A x = b`, a computed residual `r̂ = b - A x̂ + ξ`, a
computed correction with `(A + ΔA) ẑ = r̂`, an update `ŷ = x̂ + ẑ + η` — and the bounds

`|ΔA| ≤ γ W` ([higham2002accuracy] (12.1)),
`|ξ| ≤ α |A| |x - x̂| + β |A| |x|` ([higham2002accuracy] (12.2)),
`|η_i| ≤ u |x̂_i + ẑ_i|`,

if `θ := γ ‖|A⁻¹| W‖_∞` satisfies `θ + 2u < 1`, then

`(1 - 2u - θ) ‖x - ŷ‖_∞ ≤ (θ + α ‖|A⁻¹| |A|‖_∞) ‖x - x̂‖_∞ + β ‖|A⁻¹| |A| |x|‖_∞ + u (1 + θ) ‖x‖_∞`.

The error contracts by the factor `(θ + α cond(A)) / (1 - 2u - θ)` — [higham2002accuracy]'s
"approximately `η = u ‖|A⁻¹| (|A| + W)‖_∞`" — down to the floor
`(β cond(A, x) + u (1 + θ)) ‖x‖_∞ / (1 - 2u - θ)`. The proof solves the identity of `step_error`
for `x - ŷ` with `A⁻¹` rather than `(A + ΔA)⁻¹`, `x - ŷ = A⁻¹ (ΔA (x - x̂) - ξ - ΔA η
- ΔA (x - ŷ)) - η`, bounds entrywise, and absorbs the `ΔA (x - ŷ)` and `η` terms into the
left-hand side, which is where `2u + θ` comes from. -/
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
  have hu1 : u < 1 := by linarith
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
  have hN0 : 0 ≤ ‖x - xhat‖ := norm_nonneg _
  have hN'0 : 0 ≤ ‖x - yhat‖ := norm_nonneg _
  have hX0 : 0 ≤ ‖x‖ := norm_nonneg _
  have hη0 : 0 ≤ ‖η‖ := norm_nonneg _
  have hσ0 : 0 ≤ α * ‖A⁻¹.abs * A.abs‖ * ‖x - xhat‖ := by positivity
  have hφ0 : 0 ≤ β * ‖A⁻¹.abs *ᵥ (A.abs *ᵥ |x|)‖ := by positivity
  have hen' := mul_le_mul_of_nonneg_left hen (by linarith : (0 : ℝ) ≤ 1 - u)
  have hηn2 : (1 - u) * ‖η‖ ≤ u * (‖x‖ + ‖x - yhat‖) := by linarith
  have hηn' := mul_le_mul_of_nonneg_left hηn2 (by linarith : (0 : ℝ) ≤ 1 + θ)
  have hrest : 0 ≤ u * (θ * ‖x - xhat‖ + (α * ‖A⁻¹.abs * A.abs‖ * ‖x - xhat‖
      + β * ‖A⁻¹.abs *ᵥ (A.abs *ᵥ |x|)‖)) := by positivity
  linarith

/-! #### The computed steps, and Higham's Theorems 12.1–12.2 -/

/-- **One computed step of iterative refinement with LU factors, in fixed precision**
([quarteroni2000numerical] §3.12.2, FPR; [higham2002accuracy] §12.1 with `ū = u`).
`RoundsStepLU m A L U b x̂ ŷ` says that `ŷ` is an admissible computed value of one refinement
step from `x̂` in the rounding model `m`: the residual `r̂ = fl(b - A x̂)` is computed as an
affine step (`FloatingPoint.RoundsAffineStep`), the correction `ẑ` by forward and back
substitution with the computed factors `L`, `U` (`FloatingPoint.RoundsForwardSubst`,
`FloatingPoint.RoundsBackSubst`), and the update `ŷ = fl(x̂ + ẑ)` entrywise. -/
def RoundsStepLU (m : RoundingModel ℝ) (A L U : Matrix (Fin n) (Fin n) ℝ)
    (b xhat yhat : Fin n → ℝ) : Prop :=
  ∃ rhat y zhat : Fin n → ℝ, RoundsAffineStep m (-A) b xhat rhat ∧
    RoundsForwardSubst m L rhat y ∧ RoundsBackSubst m U y zhat ∧
    ∀ i, m.Rounds (xhat i + zhat i) (yhat i)

/-- **One computed step of iterative refinement with LU factors, in mixed precision**
([quarteroni2000numerical] §3.12.2, MPR; [higham2002accuracy] §12.1 with `ū = u²`).
`RoundsStepLUMixed m m' A L U b x̂ ŷ` is `RoundsStepLU` with the residual computed in a second,
finer rounding model `m'` (in the book, double precision) and then rounded once to the working
precision `m`: `s = fl'(b - A x̂)`, `r̂ = fl(s)`; the solve and the update are in `m`. -/
def RoundsStepLUMixed (m m' : RoundingModel ℝ) (A L U : Matrix (Fin n) (Fin n) ℝ)
    (b xhat yhat : Fin n → ℝ) : Prop :=
  ∃ s rhat y zhat : Fin n → ℝ, RoundsAffineStep m' (-A) b xhat s ∧
    (∀ i, m.Rounds (s i) (rhat i)) ∧
    RoundsForwardSubst m L rhat y ∧ RoundsBackSubst m U y zhat ∧
    ∀ i, m.Rounds (xhat i + zhat i) (yhat i)

/-- The residual computed as an affine step, with the error in the form of
[higham2002accuracy] (12.2): `r̂ = b - A x̂ + ξ` with
`|ξ| ≤ γ_{n+1} |A| |x - x̂| + 2 γ_{n+1} |A| |x|` when `A x = b`. -/
theorem exists_roundsAffineStep_residual_eq_add [NeZero n] {m : RoundingModel ℝ} (hu : m.u < 1)
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

/-- The mixed-precision residual, [higham2002accuracy] (12.2): computed in the model `m'` and
rounded once to the model `m`, `r̂ = b - A x̂ + ξ` with
`|ξ| ≤ (u + (1 + u) γ̄_{n+1}) |A| |x - x̂| + 2 (1 + u) γ̄_{n+1} |A| |x|`, where `u = m.u` and
`γ̄_{n+1}` is the constant of `m'`. -/
theorem exists_mixed_residual_eq_add [NeZero n] {m m' : RoundingModel ℝ} (hu' : m'.u < 1)
    (hcard' : ((n + 1 : ℕ) : ℝ) * m'.u < 1) {A : Matrix (Fin n) (Fin n) ℝ}
    {b x xhat s rhat : Fin n → ℝ} (hx : A *ᵥ x = b) (hres : RoundsAffineStep m' (-A) b xhat s)
    (hround : ∀ i, m.Rounds (s i) (rhat i)) :
    ∃ ξ : Fin n → ℝ, rhat = b - A *ᵥ xhat + ξ ∧
      |ξ| ≤ (m.u + (1 + m.u) * gamma m'.u (n + 1)) • (A.abs *ᵥ |x - xhat|)
        + (2 * (1 + m.u) * gamma m'.u (n + 1)) • (A.abs *ᵥ |x|) := by
  obtain ⟨ξ', hs, hξ'⟩ := exists_roundsAffineStep_residual_eq_add hu' hcard' hx hres
  have hu0 := m.u_nonneg
  have hγ0 := gamma_nonneg m'.u_nonneg hcard'
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
  have hAe : 0 ≤ (A.abs *ᵥ |x - xhat|) i :=
    (entrywiseNonneg_abs A).mulVec_nonneg (abs_nonneg _) i
  have hAx : 0 ≤ (A.abs *ᵥ |x|) i := (entrywiseNonneg_abs A).mulVec_nonneg (abs_nonneg _) i
  simp only [Pi.abs_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at *
  nlinarith

/-- **[higham2002accuracy] Theorem 12.2, one step** (fixed-precision iterative refinement with
LU factors, [quarteroni2000numerical] §3.12.2 FPR): for a computed step `RoundsStepLU` from `x̂`
to `ŷ`, with `A x = b`, `A` nonsingular, computed factors `L`, `U` of `A` with nonzero pivots and
`3 n u < 1`, let `θ = γ_{3n} ‖|A⁻¹| |L| |U|‖_∞`. If `θ + 2u < 1` then

`(1 - 2u - θ) ‖x - ŷ‖_∞ ≤ (θ + γ_{n+1} cond(A)) ‖x - x̂‖_∞ + 2 γ_{n+1} ‖|A⁻¹| |A| |x|‖_∞
  + u (1 + θ) ‖x‖_∞`,

with `cond(A) = ‖|A⁻¹| |A|‖_∞` the Skeel condition number. This is `norm_step_error_le_of_abs_le`
with the three backward errors of `step_error_fp`: `|ΔA| ≤ γ_{3n} |L| |U|`
(`FloatingPoint.exists_roundsLU_solve_eq`), the residual error of
`exists_roundsAffineStep_residual_eq_add`, and `|η_i| ≤ u |x̂_i + ẑ_i|` for the update. -/
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

/-- **[higham2002accuracy] Theorem 12.1, one step** (mixed-precision iterative refinement with
LU factors, [quarteroni2000numerical] §3.12.2 MPR): for a computed step `RoundsStepLUMixed`
from `x̂` to `ŷ` whose residual is computed in the finer model `m'` and rounded to `m`, with the
data of `norm_sub_le_of_roundsStepLU` and `(n + 1) ū < 1` for `ū = m'.u`, let
`θ = γ_{3n} ‖|A⁻¹| |L| |U|‖_∞` and `γ̄_{n+1}` the constant of `m'`. If `θ + 2u < 1` then

`(1 - 2u - θ) ‖x - ŷ‖_∞ ≤ (θ + (u + (1 + u) γ̄_{n+1}) cond(A)) ‖x - x̂‖_∞
  + 2 (1 + u) γ̄_{n+1} ‖|A⁻¹| |A| |x|‖_∞ + u (1 + θ) ‖x‖_∞`.

With `ū = u²` the floor `2 (1 + u) γ̄_{n+1} cond(A, x) + u (1 + θ)` is
`u (1 + θ) + O(n u² cond(A, x))`, independent of the condition number to first order, which is
the book's `ρ ≃ u`. -/
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

/-- The one-step recursion of [higham2002accuracy] (12.5) in the shape
`‖x - ŷ‖ ≤ ρ ‖x - x̂‖ + φ`, from its product form: for `0 < 1 - 2u - θ`,
`ρ = (θ + σ) / (1 - 2u - θ)` and `φ = (c + u (1 + θ) ‖x‖) / (1 - 2u - θ)`. -/
theorem norm_sub_le_mul_add_of_mul_le {u θ σ c N N' X : ℝ} (hpos : 0 < 1 - 2 * u - θ)
    (h : (1 - 2 * u - θ) * N' ≤ (θ + σ) * N + c + u * (1 + θ) * X) :
    N' ≤ (θ + σ) / (1 - 2 * u - θ) * N + (c + u * (1 + θ) * X) / (1 - 2 * u - θ) := by
  rw [div_mul_eq_mul_div, ← add_div, le_div_iff₀ hpos]
  linarith

/-- **[higham2002accuracy] Theorem 12.2 (fixed precision iterative refinement)**, in rigorous
form. Let `A x = b` with `A` nonsingular, let `L`, `U` be computed LU factors of `A` with nonzero
pivots in a rounding model with unit roundoff `u`, `3 n u < 1`, and let `x⁽⁰⁾, x⁽¹⁾, …` be a
sequence of computed refinement iterates (`RoundsStepLU` at every step). Put

`θ = γ_{3n} ‖|A⁻¹| |L| |U|‖_∞`, `ρ = (θ + γ_{n+1} cond(A)) / (1 - 2u - θ)`,
`φ = (2 γ_{n+1} ‖|A⁻¹| |A| |x|‖_∞ + u (1 + θ) ‖x‖_∞) / (1 - 2u - θ)`.

If `2θ + γ_{n+1} cond(A) + 2u < 1` — the theorem's "`η` sufficiently less than `1`", with
`η ≈ u ‖|A⁻¹| (|A| + W)‖_∞`, `uW = γ_{3n} |L| |U|` — then `ρ < 1`, the forward error is reduced by
the factor `ρ` at each step up to the floor `φ`,

`‖x - x⁽ᵏ⁺¹⁾‖_∞ ≤ ρ ‖x - x⁽ᵏ⁾‖_∞ + φ`, hence `‖x - x⁽ᵏ⁾‖_∞ ≤ ρᵏ ‖x - x⁽⁰⁾‖_∞ + φ / (1 - ρ)`,

and the limiting accuracy is `limsup_k ‖x - x⁽ᵏ⁾‖_∞ ≤ φ / (1 - ρ)`, where
`φ / ‖x‖_∞ = (2 γ_{n+1} cond(A, x) + u (1 + θ)) / (1 - 2u - θ) ≈ 2 n cond(A, x) u` is the
theorem's "until `‖x - x̂_i‖_∞ / ‖x‖_∞ ≲ 2n cond(A, x) u`". -/
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

/-- `γ_k ≤ 2 k u` when `2 k u ≤ 1`. -/
theorem _root_.FloatingPoint.gamma_le_two_mul {u : ℝ} (hu : 0 ≤ u) {k : ℕ}
    (h : 2 * ((k : ℝ) * u) ≤ 1) : gamma u k ≤ 2 * (k * u) := by
  have hk0 : 0 ≤ (k : ℝ) * u := by positivity
  rw [gamma_def, div_le_iff₀ (by linarith)]
  nlinarith

/-- **[higham2002accuracy] Theorem 12.1 (mixed precision iterative refinement)**, in rigorous
form: as `norm_sub_le_of_forall_roundsStepLU`, with the residuals computed in a finer model `m'`
(`RoundsStepLUMixed` at every step, `(n + 1) ū < 1` for `ū = m'.u`) and the constants

`θ = γ_{3n} ‖|A⁻¹| |L| |U|‖_∞`, `ρ = (θ + (u + (1 + u) γ̄_{n+1}) cond(A)) / (1 - 2u - θ)`,
`φ = (2 (1 + u) γ̄_{n+1} ‖|A⁻¹| |A| |x|‖_∞ + u (1 + θ) ‖x‖_∞) / (1 - 2u - θ)`,

`γ̄_{n+1}` being the constant of `m'`. If `2θ + (u + (1 + u) γ̄_{n+1}) cond(A) + 2u < 1` then
`ρ < 1`, `‖x - x⁽ᵏ⁺¹⁾‖_∞ ≤ ρ ‖x - x⁽ᵏ⁾‖_∞ + φ`, `‖x - x⁽ᵏ⁾‖_∞ ≤ ρᵏ ‖x - x⁽⁰⁾‖_∞ + φ / (1 - ρ)` and
`limsup_k ‖x - x⁽ᵏ⁾‖_∞ ≤ φ / (1 - ρ)`. Moreover, in "double the working precision", `ū ≤ u²`
with `2 (n + 1) ū ≤ 1`, the floor is of the order of the working precision,

`φ ≤ u (4 (1 + u) (n + 1) u ‖|A⁻¹| |A| |x|‖_∞ + (1 + θ) ‖x‖_∞) / (1 - 2u - θ)`,

which is the theorem's "until `‖x - x̂_i‖_∞ / ‖x‖_∞ ≈ u`", independent of the condition number
to first order in `u`. -/
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
    have : 0 ≤ 2 * (1 + m.u) * gamma m'.u (n + 1) * ‖A⁻¹.abs *ᵥ (A.abs *ᵥ |x|)‖
        + m.u * (1 + θ) * ‖x‖ := by positivity
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
  have hX : 0 ≤ ‖A⁻¹.abs *ᵥ (A.abs *ᵥ |x|)‖ := norm_nonneg _
  have h1 : 2 * (1 + m.u) * gamma m'.u (n + 1) * ‖A⁻¹.abs *ᵥ (A.abs *ᵥ |x|)‖
      ≤ 2 * (1 + m.u) * (2 * (n + 1) * m.u ^ 2) * ‖A⁻¹.abs *ᵥ (A.abs *ᵥ |x|)‖ := by
    gcongr
  nlinarith

end Convergence

end Refinement

/-! ### Scaling -/

namespace Matrix

variable {n K : Type*} [Fintype n] [DecidableEq n] [Field K]

/-- **Scaling a linear system** ([quarteroni2000numerical] §3.12.1): for nonsingular `D₁`, `D₂`
(diagonal in the book: `D₁` scales the equations, `D₂` the unknowns), `A x = b` iff
`(D₁ A D₂) y = D₁ b` with `y = D₂⁻¹ x`; row scaling alone is `D₂ = 1`. -/
theorem scaled_mulVec_eq_iff {D₁ D₂ : Matrix n n K} (h₁ : IsUnit D₁) (h₂ : IsUnit D₂)
    (A : Matrix n n K) (x b : n → K) :
    A *ᵥ x = b ↔ (D₁ * A * D₂) *ᵥ (D₂⁻¹ *ᵥ x) = D₁ *ᵥ b := by
  rw [mulVec_mulVec, Matrix.mul_assoc, mul_nonsing_inv _ ((isUnit_iff_isUnit_det D₂).1 h₂),
    Matrix.mul_one, ← mulVec_mulVec]
  exact (mulVec_injective_iff_isUnit.2 h₁).eq_iff.symm

end Matrix

/-! ### Condition estimation -/

section CondEstimate

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- **The basic inequality of condition estimation** ([quarteroni2000numerical] §3.11): for any
probe `d`, `γ(d) = ‖y‖ / ‖d‖ ≤ ‖A⁻¹‖` where `A y = d`; the estimators look for a `d` making
`γ(d)` as large as possible. -/
theorem norm_apply_div_le_norm_inverse (A : E ≃L[𝕜] E) (d : E) :
    ‖A.symm d‖ / ‖d‖ ≤ ‖(A.symm : E →L[𝕜] E)‖ := by
  rcases eq_or_ne d 0 with rfl | hd
  · simp
  rw [div_le_iff₀ (norm_pos_iff.2 hd)]
  exact (A.symm : E →L[𝕜] E).le_opNorm d

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- **The condition estimate** of [quarteroni2000numerical] §3.11, (3.70): from a probe vector
`d`, solve `A† x = d` (the book's `Rᵀ x = d`, or `(L U)ᵀ x = d` in (3.72)) and `A y = x`, and
estimate `K(A)` by `K̂(A) = ‖A‖ ‖y‖ / ‖x‖`. Here `x = (A⁻¹)† d`, the adjoint being that of the
Hilbert space `E`; the only provable property of the estimate is `K̂(A) ≤ K(A)`
(`condEstimate_le_condNumber`), its quality depending on the heuristic choice of `d`. -/
noncomputable def condEstimate (A : E ≃L[𝕜] E) (d : E) : ℝ :=
  ‖(A : E →L[𝕜] E)‖ * ‖A.symm (ContinuousLinearMap.adjoint (A.symm : E →L[𝕜] E) d)‖ /
    ‖ContinuousLinearMap.adjoint (A.symm : E →L[𝕜] E) d‖

/-- **The condition estimate never exceeds the condition number**: `K̂(A) ≤ K(A)`, since
`‖y‖ / ‖x‖ = ‖A⁻¹ x‖ / ‖x‖ ≤ ‖A⁻¹‖`. The book's `K̂₁(A) = ‖R‖₁ ‖y‖₁ / ‖x‖₁` is this in the
`1`-norm; the statement here is norm-agnostic. -/
theorem condEstimate_le_condNumber (A : E ≃L[𝕜] E) (d : E) :
    condEstimate A d ≤ condNumber (A : E →L[𝕜] E) := by
  rw [condEstimate, A.condNumber_eq, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (norm_apply_div_le_norm_inverse A _) (norm_nonneg _)

end CondEstimate
