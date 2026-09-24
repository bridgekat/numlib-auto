import Mathlib.Analysis.InnerProductSpace.Adjoint
import Numlib.Analysis.Matrix.OperatorNorm

/-!
# Condition estimation

Condition estimation for `A x = b`: the one provable property of every estimator that solves a
system `A y = d` with a well-chosen right-hand side, namely that `‖y‖ / ‖d‖` is a **lower bound**
for `‖A⁻¹‖` and `‖A‖ ‖y‖ / ‖d‖` a lower bound for the condition number ([golub2013matrix] §3.5.4,
the implication `A y = d ⇒ ‖A⁻¹‖_∞ ≥ ‖y‖_∞ / ‖d‖_∞` of Cline, Moler, Stewart and Wilkinson;
[quarteroni2000numerical] §3.11; [higham2002accuracy] Chapter 15). How good the lower bound is
depends on the heuristic choice of `d` and has no theorem; the choice itself (the LINPACK
look-ahead of [golub2013matrix] Algorithm 3.5.1, the `± 1` greedy of (3.5.6), the lookahead of
[quarteroni2000numerical] (3.71)–(3.72)) is an algorithm, and algorithms live in the surface.

## Main results

* `norm_apply_div_le_norm_inverse`: the basic inequality `‖A⁻¹ d‖ / ‖d‖ ≤ ‖A⁻¹‖` for a
  continuous linear equivalence `A` of any normed space.
* `condEstimate`, `condEstimate_le_condNumber`: the estimate `K̂(A) = ‖A‖ ‖y‖ / ‖x‖` of
  [quarteroni2000numerical] (3.70) from a probe `d` (`A† x = d`, `A y = x`), on a Hilbert space
  where the adjoint lives, and `K̂(A) ≤ K(A)`.
* `Matrix.norm_le_lpOpNorm_inv_mul_lpSeminorm_mulVec`, `Matrix.lpCondEstimate`,
  `Matrix.lpCondEstimate_le_condNumberLp`: the same for square matrices over `RCLike 𝕜` in the
  induced `p`-norms of `Numlib/Analysis/Matrix/OperatorNorm`, as **instances** of the operator
  statements through `Matrix.lpEquiv p hA : PiLp p ≃L[𝕜] PiLp p`.
* `Matrix.linfty_opNorm_mul_norm_le_condNumberLp_top_of_mulVec_eq`: the sign-vector estimate
  `κ̂_∞ = ‖T‖_∞ ‖y‖_∞` of [golub2013matrix] (3.5.6) and Algorithm 3.5.1 is at most `κ_∞(T)`, and
  `Matrix.one_le_lpOpNorm_top_inv_mul_norm_mulVec_inv_norm_smul`, the normalized output
  `‖T y / ‖y‖‖_∞ ≥ 1 / ‖T⁻¹‖_∞`; `pi_norm_eq_one_of_forall_norm_eq_one` reads a sign vector's
  sup norm.

## References

* [golub2013matrix] §3.5.4.
* [quarteroni2000numerical] §3.11.
* [higham2002accuracy] Chapter 15.
-/

open NormedRing
open scoped ENNReal

/-! ### The operator statements -/

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

/-- A vector all of whose entries have norm one has sup norm one. The sign vectors
`d ∈ {±1}ⁿ` of [golub2013matrix] (3.5.6) and Algorithm 3.5.1 are the use; Mathlib has the
constant case `pi_norm_const'`. -/
theorem pi_norm_eq_one_of_forall_norm_eq_one {ι E : Type*} [Fintype ι] [Nonempty ι]
    [SeminormedAddCommGroup E] {f : ι → E} (hf : ∀ i, ‖f i‖ = 1) : ‖f‖ = 1 := by
  refine le_antisymm ((pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => (hf i).le) ?_
  obtain ⟨i⟩ := ‹Nonempty ι›
  exact (hf i).symm.le.trans (norm_le_pi_norm f i)

/-! ### The matrix `p`-norm statements -/

namespace Matrix

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- **The basic inequality of condition estimation** in the induced `p`-norm: if `A y = d` then
`‖y‖_p ≤ ‖A⁻¹‖_p ‖d‖_p`, the form `‖A⁻¹‖_∞ ≥ ‖y‖_∞ / ‖d‖_∞` of [golub2013matrix] §3.5.4 at
`p = ∞` (`Matrix.lpOpNorm_top`). The instance of `norm_apply_div_le_norm_inverse` at
`Matrix.lpEquiv p hA`. -/
theorem norm_le_lpOpNorm_inv_mul_lpSeminorm_mulVec {A : Matrix n n 𝕜} (hA : IsUnit A)
    (y : n → 𝕜) : lpSeminorm p y ≤ lpOpNorm p A⁻¹ * lpSeminorm p (A *ᵥ y) := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  have hAy : A *ᵥ y ≠ 0 := fun h =>
    hy (mulVec_injective_iff_isUnit.2 hA (h.trans (mulVec_zero A).symm))
  have h := norm_apply_div_le_norm_inverse (lpEquiv p hA) (WithLp.toLp p (A *ᵥ y))
  rw [lpEquiv_symm_apply, WithLp.ofLp_toLp, mulVec_mulVec,
    nonsing_inv_mul _ ((isUnit_iff_isUnit_det A).1 hA), one_mulVec, coe_lpEquiv_symm,
    div_le_iff₀ (norm_pos_iff.2 ((WithLp.toLp_eq_zero p).not.2 hAy))] at h
  simpa [lpOpNorm] using h

/-- The condition estimate from a probe `r`: `‖A‖_p ‖z‖_p / ‖r‖_p` with `A z = r`
([golub2013matrix] §3.5.4 Step 3 with `p = ∞`, [quarteroni2000numerical] (3.70) with the probe
already transformed). Junk `0` for `r = 0`. -/
noncomputable def lpCondEstimate (A : Matrix n n 𝕜) (r : n → 𝕜) : ℝ :=
  lpOpNorm p A * lpSeminorm p (A⁻¹ *ᵥ r) / lpSeminorm p r

/-- **The condition estimate never exceeds the condition number**, `‖A‖_p ‖z‖_p / ‖r‖_p ≤ κ_p(A)`
for `A z = r` and every probe `r`: the matrix form of `condEstimate_le_condNumber`, from
`Matrix.norm_le_lpOpNorm_inv_mul_lpSeminorm_mulVec` at `y = A⁻¹ r`. -/
theorem lpCondEstimate_le_condNumberLp {A : Matrix n n 𝕜} (hA : IsUnit A) (r : n → 𝕜) :
    lpCondEstimate p A r ≤ condNumberLp p A := by
  have hn : 0 ≤ lpOpNorm p A := norm_nonneg _
  rcases eq_or_ne r 0 with rfl | hr
  · rw [lpCondEstimate, map_zero, div_zero, condNumberLp]
    exact mul_nonneg hn (norm_nonneg _)
  have h := norm_le_lpOpNorm_inv_mul_lpSeminorm_mulVec p hA (A⁻¹ *ᵥ r)
  rw [mulVec_mulVec, mul_nonsing_inv _ ((isUnit_iff_isUnit_det A).1 hA), one_mulVec,
    ← div_le_iff₀ (by simpa using hr)] at h
  rw [lpCondEstimate, condNumberLp, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left h hn

/-- **The sign-vector estimate is a lower bound for `κ_∞`** ([golub2013matrix] §3.5.4, the
estimate `κ̂_∞ = ‖T‖_∞ ‖y‖_∞` of (3.5.6) and of Algorithm 3.5.1, where `d i = ± 1`): if
`T y = d` with `‖d i‖ = 1` for all `i`, then `‖T‖_∞ ‖y‖_∞ ≤ κ_∞(T)` (`‖y‖` the sup norm). -/
theorem linfty_opNorm_mul_norm_le_condNumberLp_top_of_mulVec_eq [Nonempty n]
    {T : Matrix n n 𝕜} (hT : IsUnit T) {y d : n → 𝕜} (hy : T *ᵥ y = d)
    (hd : ∀ i, ‖d i‖ = 1) : lpOpNorm ⊤ T * ‖y‖ ≤ condNumberLp ⊤ T := by
  have h := norm_le_lpOpNorm_inv_mul_lpSeminorm_mulVec ⊤ hT y
  rw [lpSeminorm_apply, lpSeminorm_apply, PiLp.norm_toLp, PiLp.norm_toLp, hy,
    pi_norm_eq_one_of_forall_norm_eq_one hd, mul_one] at h
  rw [condNumberLp]
  exact mul_le_mul_of_nonneg_left h (norm_nonneg _)

/-- The normalized output of [golub2013matrix] Algorithm 3.5.1: for every `y ≠ 0`,
`‖T (y / ‖y‖_∞)‖_∞ ≥ 1 / ‖T⁻¹‖_∞`, written `1 ≤ ‖T⁻¹‖_∞ ‖T (y / ‖y‖_∞)‖_∞`; the book's
"`‖T y‖_∞ ≈ 1 / ‖T⁻¹‖_∞`" in its rigorous half. -/
theorem one_le_lpOpNorm_top_inv_mul_norm_mulVec_inv_norm_smul {T : Matrix n n 𝕜}
    (hT : IsUnit T) {y : n → 𝕜} (hy : y ≠ 0) :
    1 ≤ lpOpNorm ⊤ T⁻¹ * ‖T *ᵥ ((‖y‖⁻¹ : 𝕜) • y)‖ := by
  have h := norm_le_lpOpNorm_inv_mul_lpSeminorm_mulVec ⊤ hT ((‖y‖⁻¹ : 𝕜) • y)
  rwa [lpSeminorm_apply, lpSeminorm_apply, PiLp.norm_toLp, PiLp.norm_toLp, norm_smul,
    norm_inv, RCLike.norm_ofReal, abs_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hy)] at h

end Matrix
