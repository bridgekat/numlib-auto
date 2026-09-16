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
  `‖R‖` of the book's Property 3.1 with the factors in the other order. The finite-precision
  statements of §3.12.2 (`ρ ≃ 2 n cond(A, x) u` in fixed precision, `ρ ≃ u` in mixed precision;
  [higham2002accuracy] Theorems 12.1–12.2) are asymptotic and are not formalized.
* **One computed step** (§3.12.2 again), the rigorous content those asymptotics summarize: the
  error identity `(A + ΔA)(x - ŷ) = ΔA (x - x̂) - ξ - (A + ΔA) η` for a residual, a solve and an
  update each carrying a backward error (`Refinement.step_error`), its `∞`-norm form
  (`Refinement.norm_step_error_le`), and its instantiation in the relational rounding model of
  `Numlib/FloatingPoint`, where the three errors are bounded by `γ_{3n} |L| |U|`,
  `γ_{n+1}(|A| |x̂| + |b|)` and `u |x̂ + ẑ|` (`Refinement.step_error_fp`). These are stated on
  matrices over `ℝ`, since the rounding models are.
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
[quarteroni2000numerical] §3.12.2 quotes from [higham2002accuracy] Theorems 12.1–12.2; those two
are asymptotic statements and are not formalized. -/
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
