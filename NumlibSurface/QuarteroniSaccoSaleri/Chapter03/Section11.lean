import Numlib.Direct.Refinement
import NumlibSurface.QuarteroniSaccoSaleri.Chapter03.Section10

/-!
# Quarteroni–Sacco–Saleri §3.11: an approximate computation of `K(A)`

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*
[quarteroni2000numerical], §3.11, over the backbone `Numlib/Direct/Refinement` (the basic
inequality `‖A⁻¹ d‖ / ‖d‖ ≤ ‖A⁻¹‖` and the Hilbert-space condition estimate `condEstimate`) and
`Numlib/Analysis/Matrix/OperatorNorm` (`κ₂(Q R) = κ₂(R)`).

## Conventions

Norms are the induced `p`-norms of §3.1, `‖A‖_p = lpOpNorm p A`, `‖x‖_p = ‖toLp p x‖` and
`K_p(A) = condNumber p A`; the book's `K̂₁(A)` is the case `p = 1` and the `‖·‖₂` discussion the
case `p = 2`. The systems `Rᵀ x = d`, `R y = x` of (3.70) — or `(L U)ᵀ x = d`, `L U y = x` of
(3.72) with `A = L U` — are solved as `x = Aᵀ⁻¹ d`, `y = A⁻¹ x` for a nonsingular `A`, and the
estimate is `condEstimate p A d = ‖A‖_p ‖y‖_p / ‖x‖_p`. The backbone's `condEstimate` lives on a
Hilbert space, where the adjoint replaces the transpose; it is the case `p = 2`
(`condEstimate_two_eq`), while the book's `1`-norm estimate needs the matrix form stated here.

## Contents

* `equation_3_70` — `γ(d) = ‖A⁻¹ d‖ / ‖d‖ ≤ ‖A⁻¹‖`, and the ratio `‖y‖ / ‖x‖ ≤ ‖R⁻¹‖`.
* `condEstimate`, `condEstimate_two_eq`, `condEstimate_le` — the estimate `K̂_p(A)` and
  `K̂_p(A) ≤ K_p(A)`.
* `condNumber_two_eq_of_qr` — `K₂(A) = K₂(R)` for a QR factorization.

The lookahead heuristic (3.71) for the signs of `d`, Program 14 and Example 3.9 state no theorem
and are not nodes; Exercise 15, which the text cites, is in `Section15`.
-/

open Finset Matrix WithLp
open scoped ENNReal

namespace QuarteroniSaccoSaleri.Chapter03

variable {n : ℕ} (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- **§3.11, the basic inequality, and (3.70).** For a nonsingular `A` and any `d ≠ 0`,
`γ(d) = ‖y‖ / ‖d‖ ≤ ‖A⁻¹‖` where `A y = d`, by the definition of the induced norm; so for the
solutions `x`, `y` of `Rᵀ x = d`, `R y = x` (`R` nonsingular) the ratio `‖y‖ / ‖x‖` never exceeds
`‖R⁻¹‖` (backbone `norm_apply_div_le_norm_inverse`). -/
theorem equation_3_70 {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A) (d : Fin n → ℝ) :
    ‖toLp p (A⁻¹ *ᵥ d)‖ / ‖toLp p d‖ ≤ lpOpNorm p A⁻¹ ∧
      ‖toLp p (A⁻¹ *ᵥ (Aᵀ⁻¹ *ᵥ d))‖ / ‖toLp p (Aᵀ⁻¹ *ᵥ d)‖ ≤ lpOpNorm p A⁻¹ := by
  have key : ∀ v : Fin n → ℝ, ‖toLp p (A⁻¹ *ᵥ v)‖ / ‖toLp p v‖ ≤ lpOpNorm p A⁻¹ := fun v => by
    have h := norm_apply_div_le_norm_inverse (lpEquiv p hA) (toLp p v)
    rwa [lpEquiv_symm_apply, ofLp_toLp, coe_lpEquiv_symm] at h
  exact ⟨key d, key _⟩

/-- **§3.11, the condition estimate** `K̂_p(A) = ‖A‖_p ‖y‖_p / ‖x‖_p` from a probe vector `d`:
`x` solves `Aᵀ x = d` (the book's `Rᵀ x = d` in (3.70), `(L U)ᵀ x = d` in (3.72)) and `y` solves
`A y = x`; `p = 1` is the book's `K̂₁(A)`. Its quality depends on the heuristic choice of `d`,
and its one provable property is `K̂_p(A) ≤ K_p(A)` (`condEstimate_le`). -/
noncomputable def condEstimate (A : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ) : ℝ :=
  lpOpNorm p A * ‖toLp p (A⁻¹ *ᵥ (Aᵀ⁻¹ *ᵥ d))‖ / ‖toLp p (Aᵀ⁻¹ *ᵥ d)‖

/-- The adjoint of `x ↦ M x` on `EuclideanSpace ℝ (Fin n)` is `x ↦ Mᵀ x`. -/
private theorem adjoint_lpCLM_two (M : Matrix (Fin n) (Fin n) ℝ) :
    ContinuousLinearMap.adjoint (lpCLM 2 M) = lpCLM 2 Mᵀ := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  simp only [lpCLM_apply, EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  rw [dotProduct_mulVec, vecMul_transpose, dotProduct_comm]

/-- For `p = 2` the estimate is the backbone's Hilbert-space `condEstimate`, whose adjoint
`(A⁻¹)†` is `(A⁻¹)ᵀ = (Aᵀ)⁻¹`. -/
theorem condEstimate_two_eq {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A) (d : Fin n → ℝ) :
    condEstimate 2 A d = _root_.condEstimate (lpEquiv 2 hA) (toLp 2 d) := by
  rw [condEstimate, _root_.condEstimate, coe_lpEquiv, coe_lpEquiv_symm, adjoint_lpCLM_two,
    lpEquiv_symm_apply, lpCLM_apply, ofLp_toLp, ofLp_toLp, transpose_nonsing_inv]
  rfl

/-- **§3.11, `K̂_p(A) ≤ K_p(A)`**: the estimator never overestimates, for any probe `d`, since
`‖y‖ / ‖x‖ = ‖A⁻¹ x‖ / ‖x‖ ≤ ‖A⁻¹‖` (the matrix form of the backbone's
`condEstimate_le_condNumber`). -/
theorem condEstimate_le {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A) (d : Fin n → ℝ) :
    condEstimate p A d ≤ condNumber p A := by
  rw [condEstimate, condNumber, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (equation_3_70 p hA d).2 (lpOpNorm_nonneg _ _)

open scoped Matrix.Norms.L2Operator in
/-- **§3.11, `K₂(A) = K₂(R)`** "due to Property 1.8" (Exercise 14): if `A = Q R` with `Q`
orthogonal, the spectral condition numbers of `A` and `R` agree, since `‖Q R‖₂ = ‖R‖₂` and
`‖(Q R)⁻¹‖₂ = ‖R⁻¹ Qᵀ‖₂ = ‖R⁻¹‖₂` (backbone `Matrix.condNumber_l2_unitary_mul`). -/
theorem condNumber_two_eq_of_qr {A Q R : Matrix (Fin n) (Fin n) ℝ}
    (hQ : Q ∈ orthogonalGroup (Fin n) ℝ) (hA : A = Q * R) : condNumber 2 A = condNumber 2 R := by
  rw [condNumber_two_eq, condNumber_two_eq, hA]
  exact condNumber_l2_unitary_mul hQ R

end QuarteroniSaccoSaleri.Chapter03
