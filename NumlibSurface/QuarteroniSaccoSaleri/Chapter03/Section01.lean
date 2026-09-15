import Numlib.Conditioning.LinearSystem.Componentwise
import Numlib.FloatingPoint.Stationary
import NumlibSurface.QuarteroniSaccoSaleri.Chapter01.Section11

/-!
# Quarteroni–Sacco–Saleri §3.1: stability analysis of linear systems

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*
[quarteroni2000numerical], §3.1, over the backbone `Numlib/Analysis/Normed/Ring/CondNumber` (the
condition number `κ a = ‖a‖ ‖a⁻¹‖` of an element of a normed ring),
`Numlib/Analysis/Matrix/OperatorNorm` (the induced `p`-norms `‖A‖_p` and `κ_p(A)`, the spectral
condition number of unitary and positive definite matrices), `Numlib/LinearAlgebra/Matrix/SVD`
(`κ₂ = σ_max / σ_min`), `Numlib/Conditioning/LinearSystem` (the normwise perturbation theory:
Kahan's distance to singularity, Theorems 3.1–3.3, Property 3.1, the a posteriori bounds) and
`Numlib/Conditioning/LinearSystem/Componentwise` (the componentwise theory (3.15)–(3.16), the
Skeel condition number and the LAPACK residual bound).

## Conventions

The book's `K(A) = ‖A‖ ‖A⁻¹‖` "for an induced matrix norm" (3.4) is stated for the norm
`‖·‖_p` induced by the vector `p`-norm, `1 ≤ p ≤ ∞`: `condNumber p A = ‖A‖_p ‖A⁻¹‖_p` with
`Matrix.lpOpNorm p`, which is the backbone's `Matrix.condNumberLp p A`
(`condNumber_eq_condNumberLp`) and the `NormedRing.condNumber` of the operator `x ↦ A x` on
`PiLp p (Fin n → ℝ)` (`condNumber_eq`). Vector `p`-norms are `‖toLp p x‖` as in chapter 1. Where
the book fixes `p = ∞` (the componentwise estimates of §3.1.2 and the LAPACK bound of §3.1.4),
`‖x‖_∞` is the sup norm `‖x‖` of `Fin n → ℝ` (`‖toLp ⊤ x‖ = ‖x‖`, `PiLp.norm_toLp`) and `‖A‖_∞`
is Mathlib's scoped `Matrix.Norms.Operator` instance, the maximum absolute row sum, which
`Matrix.lpOpNorm_top` identifies with `‖·‖_⊤`. The entrywise absolute value `|A|` is
`Matrix.abs A` and the entrywise order `C ≤ D` of §3.1.2 is `C ≤ₑ D` (`Matrix.EntrywiseLE`), both
from `Numlib/LinearAlgebra/Matrix/Order`. A singular matrix has `A⁻¹ = 0` in Mathlib, so
`condNumber p A = 0` for it where the book says `∞`; every statement below assumes `A`
nonsingular, as the book does, and the book's matrices have positive order, which is the
`[NeZero n]` of the statements that need a nontrivial space.

The perturbed system (3.8) is the hypothesis `(A + δA) *ᵥ (x + δx) = b + δb`, with `δx` the
unknown perturbation of the solution `x` of `A x = b`.

## Contents

* `condNumber`, `condNumber_eq_condNumberLp`, `condNumber_eq`, `one_le_condNumber`,
  `condNumber_inv`, `condNumber_smul`, `condNumber_two_eq`, `condNumber_two_of_orthogonal`,
  `condNumber_two_eq_div_singularValues`, `equation_3_5` — §3.1.1, the condition number.
* `exists_lpCLM_eq`, `remark_3_1`, `equation_3_7` — the distance to singularity and its
  consequence.
* `theorem_3_1`, `theorem_3_2`, `theorem_3_2_lower`, `theorem_3_3`, `theorem_3_3_sum` — the
  normwise forward a priori analysis of §3.1.2.
* `equation_3_15`, `equation_3_16_a`, `equation_3_16_b`, `example_3_1_matrix`, `example_3_1` —
  the componentwise estimates of §3.1.2.
* `property_3_1_isUnit`, `property_3_1_inv`, `property_3_1_sub`, `equation_3_19` — the backward
  a priori analysis of §3.1.3.
* `equation_3_20`, `equation_3_21`, `computedResidualErrorBound` — the a posteriori analysis of
  §3.1.4.

## Readings and errata

(3.7) prints `‖δA‖_p ‖A‖_p < 1` and says that it follows from `A + δA` being nonsingular; both
are wrong (`δA = A` gives a nonsingular `A + δA` with `‖A‖_p ‖A‖_p ≥ 1` for, say, `A = I`), and
the proof of Theorem 3.1 uses (3.7) as "`‖A⁻¹ δA‖ < 1`". The reading adopted, which is what
Kahan's formula (3.6) gives, is `‖δA‖_p ‖A⁻¹‖_p < 1 ⟹ A + δA` nonsingular (`equation_3_7`), and
Theorem 3.1 assumes `‖δA‖ ‖A⁻¹‖ < 1`. The second line of (3.15) prints `‖A⁻¹||A|‖_∞`; it is read
as `‖|A⁻¹| |A|‖_∞`, the Skeel condition number `Matrix.skeelCond A`. (3.19) is stated, as the
book's own derivation requires, with the roles of `A` and `C` interchanged in the hypothesis:
`C` is the exact inverse of `A + δA`, so the residual that has to be small is `R = C A - I`.
-/

open Finset Matrix WithLp
open scoped ENNReal NNReal

namespace QuarteroniSaccoSaleri.Chapter03

variable {n : ℕ} (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-! ### §3.1.1: the condition number of a matrix -/

/-- **(3.4).** The *condition number* `K_p(A) = ‖A‖_p ‖A⁻¹‖_p` of `A ∈ ℝ^{n×n}` in the matrix
norm induced by the vector `p`-norm (`p = 1, 2, ∞` being the remarkable instances); it is the
backbone's `Matrix.condNumberLp p A`. Mathlib's `A⁻¹` is `0` for a singular `A`, so the value is
then `0` rather than the book's `∞`; every statement about it assumes `A` nonsingular. -/
noncomputable def condNumber (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  lpOpNorm p A * lpOpNorm p A⁻¹

/-- `K_p(A)` is the backbone's `Matrix.condNumberLp p A`. -/
theorem condNumber_eq_condNumberLp (A : Matrix (Fin n) (Fin n) ℝ) :
    condNumber p A = condNumberLp p A := rfl

/-- `K_p(A)` is the `NormedRing.condNumber` of the operator `x ↦ A x` on `PiLp p (Fin n → ℝ)`,
which is how the operator-level theorems of the backbone reach it. -/
theorem condNumber_eq (A : Matrix (Fin n) (Fin n) ℝ) :
    condNumber p A = NormedRing.condNumber (lpCLM p A) :=
  condNumberLp_eq_condNumber p A

variable {p}

/-- **§3.1.1, `K(A) ≥ 1`**: for a nonsingular `A`, `1 = ‖A A⁻¹‖ ≤ ‖A‖ ‖A⁻¹‖ = K(A)` (backbone
`Matrix.one_le_condNumberLp`, `NormedRing.one_le_condNumber`). -/
theorem one_le_condNumber [NeZero n] {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A) :
    1 ≤ condNumber p A :=
  one_le_condNumberLp p hA

/-- **§3.1.1, `K(A⁻¹) = K(A)`** (backbone `NormedRing.condNumber_inverse`; for a singular `A`
both sides are `0`). -/
theorem condNumber_inv (A : Matrix (Fin n) (Fin n) ℝ) : condNumber p A⁻¹ = condNumber p A := by
  rw [condNumber_eq, condNumber_eq, ← ringInverse_lpCLM, NormedRing.condNumber_inverse]

/-- **§3.1.1, `K(α A) = K(A)`** for every `α ≠ 0` (backbone `Matrix.condNumberLp_smul`). -/
theorem condNumber_smul {α : ℝ} (hα : α ≠ 0) (A : Matrix (Fin n) (Fin n) ℝ) :
    condNumber p (α • A) = condNumber p A :=
  condNumberLp_smul p hα A

open scoped Matrix.Norms.L2Operator in
/-- `K₂(A)` is the `NormedRing.condNumber` of `A` in Mathlib's scoped `L2Operator` norm, the form
in which the backbone states the spectral condition number. -/
theorem condNumber_two_eq (A : Matrix (Fin n) (Fin n) ℝ) :
    condNumber 2 A = NormedRing.condNumber A := by
  rw [condNumber, lpOpNorm_two, lpOpNorm_two, NormedRing.condNumber, nonsing_inv_eq_ringInverse]

open scoped Matrix.Norms.L2Operator in
/-- **§3.1.1, orthogonal matrices**: if `A` is orthogonal then `K₂(A) = 1`, since
`‖A‖₂ = √ρ(Aᵀ A) = √ρ(I) = 1` and `A⁻¹ = Aᵀ` (backbone `Matrix.condNumber_l2_of_mem_unitaryGroup`,
the orthogonal group being the real unitary group). -/
theorem condNumber_two_of_orthogonal [NeZero n] {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A ∈ orthogonalGroup (Fin n) ℝ) : condNumber 2 A = 1 := by
  rw [condNumber_two_eq]
  exact condNumber_l2_of_mem_unitaryGroup hA

open scoped Matrix.Norms.L2Operator in
/-- **§3.1.1, the spectral condition number**: for a nonsingular `A`,
`K₂(A) = ‖A‖₂ ‖A⁻¹‖₂ = σ₁(A) / σₙ(A)`, the ratio of the largest and the smallest singular values
(backbone `Matrix.condNumber_l2_eq_div_singularValues`; the singular values are indexed by the
columns of `A`, in no particular order). -/
theorem condNumber_two_eq_div_singularValues [NeZero n] {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : IsUnit A) :
    condNumber 2 A = (⨆ i, A.singularValues i) / ⨅ i, A.singularValues i := by
  rw [condNumber_two_eq]
  exact condNumber_l2_eq_div_singularValues A ((isUnit_iff_isUnit_det A).mp hA)

open scoped Matrix.Norms.L2Operator in
/-- **(3.5).** For a symmetric positive definite `A`, `K₂(A) = λ_max / λ_min = ρ(A) ρ(A⁻¹)`, the
ratio of the extreme eigenvalues (backbone `Matrix.PosDef.condNumber_l2_eq_div_eigenvalues`, the
eigenvalues being Mathlib's `hA.1.eigenvalues`, and `‖A‖₂ = ρ(A)` for a symmetric matrix,
`Matrix.l2_opNorm_eq_complexSpectralRadius_of_isHermitian`). -/
theorem equation_3_5 [NeZero n] {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) :
    condNumber 2 A = (⨆ i, hA.1.eigenvalues i) / ⨅ i, hA.1.eigenvalues i ∧
      condNumber 2 A = (complexSpectralRadius A).toReal * (complexSpectralRadius A⁻¹).toReal := by
  refine ⟨by rw [condNumber_two_eq]; exact hA.condNumber_l2_eq_div_eigenvalues, ?_⟩
  rw [condNumber, lpOpNorm_two, lpOpNorm_two,
    l2_opNorm_eq_complexSpectralRadius_of_isHermitian hA.1,
    l2_opNorm_eq_complexSpectralRadius_of_isHermitian hA.1.inv]

/-! ### Remark 3.1: the distance to singularity, and (3.7) -/

-- TODO(backbone): belongs in `Numlib/Analysis/Matrix/OperatorNorm` beside `Matrix.lpCLM`, with
-- the injectivity `lpCLM_injective` below.
/-- Every operator on `PiLp p (Fin n → ℝ)` is `x ↦ M x` for a matrix `M`: `Matrix.toLpLin` is a
linear equivalence. -/
theorem exists_lpCLM_eq (t : PiLp p (fun _ : Fin n => ℝ) →L[ℝ] PiLp p (fun _ : Fin n => ℝ)) :
    ∃ M : Matrix (Fin n) (Fin n) ℝ, lpCLM p M = t :=
  ⟨(toLpLin p p).symm (t : PiLp p (fun _ : Fin n => ℝ) →ₗ[ℝ] PiLp p (fun _ : Fin n => ℝ)), by
    ext x
    simp [lpCLM]⟩

/-- `Matrix.lpCLM p` respects subtraction. -/
private theorem lpCLM_sub (A B : Matrix (Fin n) (Fin n) ℝ) :
    lpCLM p (A - B) = lpCLM p A - lpCLM p B := by
  ext x i
  simp [sub_mulVec]

/-- `Matrix.lpCLM p` is injective. -/
private theorem lpCLM_injective :
    Function.Injective (lpCLM p : Matrix (Fin n) (Fin n) ℝ → _) := fun A B h =>
  (toLpLin p p).injective (by
    have := congrArg ContinuousLinearMap.toLinearMap h
    simpa only [lpCLM, LinearMap.coe_toContinuousLinearMap] using this)

-- TODO(backbone): the operator ring of a finite-dimensional space is Dedekind-finite; stated
-- here for `PiLp p (Fin n → ℝ)` through the matrix algebra, for `isUnit_of_norm_mul_sub_one_lt`.
instance : IsDedekindFiniteMonoid
    (PiLp p (fun _ : Fin n => ℝ) →L[ℝ] PiLp p (fun _ : Fin n => ℝ)) where
  mul_eq_one_symm {a b} h := by
    obtain ⟨A, rfl⟩ := exists_lpCLM_eq a
    obtain ⟨B, rfl⟩ := exists_lpCLM_eq b
    rw [← lpCLM_mul, ← lpCLM_one] at h ⊢
    rw [mul_eq_one_comm.mp (lpCLM_injective h)]

/-- **Remark 3.1, (3.6) (Kahan).** For a nonsingular `A`, the relative distance of `A` from the
set of singular matrices in the `p`-norm, `dist_p(A) = min {‖δA‖_p / ‖A‖_p : A + δA singular}`,
is attained and equals `1 / K_p(A)` (backbone `ContinuousLinearEquiv.isLeast_dist_singular` for
the operator `x ↦ A x` on `PiLp p (Fin n → ℝ)`). -/
theorem remark_3_1 [NeZero n] {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A) :
    IsLeast {r | ∃ δA : Matrix (Fin n) (Fin n) ℝ,
        ¬ IsUnit (A + δA) ∧ lpOpNorm p δA / lpOpNorm p A = r}
      (1 / condNumber p A) := by
  have h := (lpEquiv p hA).isLeast_dist_singular
  rw [← ContinuousLinearEquiv.condNumber_coe, coe_lpEquiv, ← condNumber_eq] at h
  convert h using 1
  ext r
  constructor
  · rintro ⟨δA, hδA, rfl⟩
    refine ⟨lpCLM p δA, ?_, rfl⟩
    rwa [← lpCLM_add, isUnit_lpCLM_iff]
  · rintro ⟨t, ht, rfl⟩
    obtain ⟨δA, rfl⟩ := exists_lpCLM_eq t
    refine ⟨δA, ?_, rfl⟩
    rwa [← lpCLM_add, isUnit_lpCLM_iff] at ht

/-- A nonsingular matrix of positive order and its inverse have positive `p`-norms, since
`1 ≤ K_p(A)`. -/
private theorem lpOpNorm_pos_of_isUnit [NeZero n] {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : IsUnit A) : 0 < lpOpNorm p A ∧ 0 < lpOpNorm p A⁻¹ := by
  have h1 := one_le_condNumberLp p hA
  rw [condNumberLp] at h1
  refine ⟨(lpOpNorm_nonneg p A).lt_of_ne fun h => ?_,
    (lpOpNorm_nonneg p A⁻¹).lt_of_ne fun h => ?_⟩
  · rw [← h, zero_mul] at h1; norm_num at h1
  · rw [← h, mul_zero] at h1; norm_num at h1

/-- A nonzero vector of `ℝⁿ` forces `n ≠ 0`. -/
private theorem neZero_of_ne_zero {b : Fin n → ℝ} (hb : b ≠ 0) : NeZero n :=
  ⟨fun h => hb (by subst h; exact Subsingleton.elim _ _)⟩

/-- **(3.7), corrected.** If `‖δA‖_p ‖A⁻¹‖_p < 1` then `A + δA` is nonsingular: the relative
perturbation is below the distance to singularity `1 / K_p(A)` of (3.6). The book prints
`‖δA‖_p ‖A‖_p < 1` and states the implication the other way, which is false (`δA = A`); the
proof of Theorem 3.1 uses (3.7) in this reading, "`A⁻¹ δA` has norm less than `1`" (backbone
`NormedRing.norm_le_of_not_isUnit_add`, the lower half of Kahan's formula). -/
theorem equation_3_7 {A δA : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A)
    (h : lpOpNorm p δA * lpOpNorm p A⁻¹ < 1) : IsUnit (A + δA) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact isUnit_of_subsingleton _
  have : NeZero n := ⟨hn.ne'⟩
  by_contra hne
  rw [← isUnit_lpCLM_iff p, lpCLM_add] at hne
  have hle := NormedRing.norm_le_of_not_isUnit_add ((isUnit_lpCLM_iff p A).mpr hA) hne
  rw [ringInverse_lpCLM] at hle
  have hpos := (lpOpNorm_pos_of_isUnit (p := p) hA).2
  have h1 : 1 ≤ lpOpNorm p δA * lpOpNorm p A⁻¹ := by
    rw [← div_le_iff₀ hpos, one_div]
    exact hle
  exact absurd h (not_lt.mpr h1)

/-! ### §3.1.2: forward a priori analysis, Theorems 3.1–3.3 -/

section Forward

variable {A δA : Matrix (Fin n) (Fin n) ℝ} {b δb x δx : Fin n → ℝ}

/-- **Theorem 3.1, (3.9).** Let `A` be nonsingular and `δA` satisfy (3.7), `‖δA‖ ‖A⁻¹‖ < 1`, in
the induced `p`-norm. If `x` solves `A x = b` with `b ≠ 0` and `δx` satisfies the perturbed
system (3.8), `(A + δA)(x + δx) = b + δb`, then
`‖δx‖ / ‖x‖ ≤ K(A) / (1 - K(A) ‖δA‖ / ‖A‖) (‖δb‖ / ‖b‖ + ‖δA‖ / ‖A‖)`
(backbone `relative_error_le_condNumber` for the operator on `PiLp p (Fin n → ℝ)`, whose
denominator `1 - ‖A⁻¹‖ ‖δA‖` is the book's `1 - K(A) ‖δA‖ / ‖A‖`). -/
theorem theorem_3_1 (hA : IsUnit A) (hδA : lpOpNorm p δA * lpOpNorm p A⁻¹ < 1)
    (hx : A *ᵥ x = b) (hb : b ≠ 0) (hδx : (A + δA) *ᵥ (x + δx) = b + δb) :
    ‖toLp p δx‖ / ‖toLp p x‖ ≤
      condNumber p A / (1 - condNumber p A * (lpOpNorm p δA / lpOpNorm p A)) *
        (‖toLp p δb‖ / ‖toLp p b‖ + lpOpNorm p δA / lpOpNorm p A) := by
  have := neZero_of_ne_zero hb
  have hApos := (lpOpNorm_pos_of_isUnit (p := p) hA).1
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hb (by rw [← hx, mulVec_zero])
  have h := relative_error_le_condNumber (lpEquiv p hA) (lpCLM p δA) (b := toLp p b)
    (Δb := toLp p δb) (x := toLp p x) (y := toLp p (x + δx))
    (by rw [lpEquiv_apply, ofLp_toLp, hx])
    (by rw [coe_lpEquiv, ← lpCLM_add, lpCLM_apply, ofLp_toLp, hδx, toLp_add])
    (by rw [coe_lpEquiv_symm, mul_comm]; exact hδA)
    (by rwa [Ne, toLp_eq_zero]) (by rwa [Ne, toLp_eq_zero])
  rw [coe_lpEquiv, coe_lpEquiv_symm, ← condNumber_eq, ← toLp_sub, add_sub_cancel_left] at h
  have e : condNumber p A * (lpOpNorm p δA / lpOpNorm p A) = lpOpNorm p A⁻¹ * lpOpNorm p δA := by
    rw [condNumber]
    field_simp
  rw [e, add_comm]
  exact h

/-- **Theorem 3.2, the upper inequality of (3.11).** Under the hypotheses of Theorem 3.1 with
`δA = 0`, `‖δx‖ / ‖x‖ ≤ K(A) ‖δb‖ / ‖b‖` (backbone
`ContinuousLinearEquiv.relative_error_le_condNumber_mul_relative_residual`). -/
theorem theorem_3_2 (hA : IsUnit A) (hx : A *ᵥ x = b) (hb : b ≠ 0)
    (hδx : A *ᵥ (x + δx) = b + δb) :
    ‖toLp p δx‖ / ‖toLp p x‖ ≤ condNumber p A * (‖toLp p δb‖ / ‖toLp p b‖) := by
  have h := (lpEquiv p hA).relative_error_le_condNumber_mul_relative_residual (v := toLp p x)
    (v' := toLp p (x + δx)) (w := toLp p b) (w' := toLp p (b + δb))
    (by rw [lpEquiv_apply, ofLp_toLp, hx]) (by rw [lpEquiv_apply, ofLp_toLp, hδx])
    (by rwa [Ne, toLp_eq_zero])
  rwa [← ContinuousLinearEquiv.condNumber_coe, coe_lpEquiv, ← condNumber_eq, ← toLp_sub,
    ← toLp_sub, sub_add_cancel_left, sub_add_cancel_left, toLp_neg, toLp_neg, norm_neg,
    norm_neg] at h

/-- **Theorem 3.2, the lower inequality of (3.11).** Under the hypotheses of Theorem 3.1 with
`δA = 0`, `(1 / K(A)) ‖δb‖ / ‖b‖ ≤ ‖δx‖ / ‖x‖` (backbone
`ContinuousLinearEquiv.relative_residual_le_condNumber_mul_relative_error`, divided by
`K(A) ≥ 1`). -/
theorem theorem_3_2_lower (hA : IsUnit A) (hx : A *ᵥ x = b) (hb : b ≠ 0)
    (hδx : A *ᵥ (x + δx) = b + δb) :
    1 / condNumber p A * (‖toLp p δb‖ / ‖toLp p b‖) ≤ ‖toLp p δx‖ / ‖toLp p x‖ := by
  have := neZero_of_ne_zero hb
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hb (by rw [← hx, mulVec_zero])
  have h := (lpEquiv p hA).relative_residual_le_condNumber_mul_relative_error (v := toLp p x)
    (v' := toLp p (x + δx)) (w := toLp p b) (w' := toLp p (b + δb))
    (by rw [lpEquiv_apply, ofLp_toLp, hx]) (by rw [lpEquiv_apply, ofLp_toLp, hδx])
    (by rwa [Ne, toLp_eq_zero])
  rw [← ContinuousLinearEquiv.condNumber_coe, coe_lpEquiv, ← condNumber_eq, ← toLp_sub,
    ← toLp_sub, sub_add_cancel_left, sub_add_cancel_left, toLp_neg, toLp_neg, norm_neg,
    norm_neg] at h
  rw [one_div, inv_mul_le_iff₀ (zero_lt_one.trans_le (one_le_condNumber hA))]
  exact h

/-- **Theorem 3.3, (3.13).** If `‖δA‖ ≤ γ ‖A‖` and `‖δb‖ ≤ γ ‖b‖` with `γ K(A) < 1` (and the
setting of Theorem 3.1: `A` nonsingular, `A x = b`, `b ≠ 0`, `(A + δA)(x + δx) = b + δb`), then
`‖δx‖ / ‖x‖ ≤ 2γ / (1 - γ K(A)) K(A)` (backbone `relative_error_le_of_norm_le_mul`). -/
theorem theorem_3_3 (hA : IsUnit A) (hx : A *ᵥ x = b) (hb : b ≠ 0)
    (hδx : (A + δA) *ᵥ (x + δx) = b + δb) {γ : ℝ} (hδA : lpOpNorm p δA ≤ γ * lpOpNorm p A)
    (hδb : ‖toLp p δb‖ ≤ γ * ‖toLp p b‖) (hγ : γ * condNumber p A < 1) :
    ‖toLp p δx‖ / ‖toLp p x‖ ≤ 2 * γ / (1 - γ * condNumber p A) * condNumber p A := by
  have h := relative_error_le_of_norm_le_mul (lpEquiv p hA) (lpCLM p δA) (b := toLp p b)
    (Δb := toLp p δb) (x := toLp p x) (y := toLp p (x + δx))
    (by rw [lpEquiv_apply, ofLp_toLp, hx])
    (by rw [coe_lpEquiv, ← lpCLM_add, lpCLM_apply, ofLp_toLp, hδx, toLp_add])
    (by rw [coe_lpEquiv]; exact hδA) hδb (by rw [coe_lpEquiv, ← condNumber_eq]; exact hγ)
    (by rwa [Ne, toLp_eq_zero])
  rwa [coe_lpEquiv, ← condNumber_eq, ← toLp_sub, add_sub_cancel_left] at h

/-- **Theorem 3.3, (3.12).** Under the hypotheses of (3.13),
`‖x + δx‖ / ‖x‖ ≤ (1 + γ K(A)) / (1 - γ K(A))` (backbone `norm_add_div_le_of_norm_le_mul`). -/
theorem theorem_3_3_sum (hA : IsUnit A) (hx : A *ᵥ x = b) (hb : b ≠ 0)
    (hδx : (A + δA) *ᵥ (x + δx) = b + δb) {γ : ℝ} (hδA : lpOpNorm p δA ≤ γ * lpOpNorm p A)
    (hδb : ‖toLp p δb‖ ≤ γ * ‖toLp p b‖) (hγ : γ * condNumber p A < 1) :
    ‖toLp p (x + δx)‖ / ‖toLp p x‖ ≤ (1 + γ * condNumber p A) / (1 - γ * condNumber p A) := by
  have h := norm_add_div_le_of_norm_le_mul (lpEquiv p hA) (lpCLM p δA) (b := toLp p b)
    (Δb := toLp p δb) (x := toLp p x) (y := toLp p (x + δx))
    (by rw [lpEquiv_apply, ofLp_toLp, hx])
    (by rw [coe_lpEquiv, ← lpCLM_add, lpCLM_apply, ofLp_toLp, hδx, toLp_add])
    (by rw [coe_lpEquiv]; exact hδA) hδb (by rw [coe_lpEquiv, ← condNumber_eq]; exact hγ)
    (by rwa [Ne, toLp_eq_zero])
  rwa [coe_lpEquiv, ← condNumber_eq] at h

end Forward

/-! ### §3.1.2: the componentwise estimates (3.15)–(3.16) and Example 3.1 -/

section Componentwise

open scoped Matrix.Norms.Operator

variable {A δA : Matrix (Fin n) (Fin n) ℝ} {b δb x δx : Fin n → ℝ}

/-- **(3.15).** For perturbations with `|δA| ≤ γ |A|` and `|δb| ≤ γ |b|` entrywise, `γ ≥ 0`, in
the setting of Theorem 3.1 (`A` nonsingular, `A x = b`, `b ≠ 0`, `(A + δA)(x + δx) = b + δb`) and
with `γ ‖|A⁻¹| |A|‖_∞ < 1`, the `∞`-norm relative error satisfies
`‖δx‖_∞ / ‖x‖_∞ ≤ γ ‖|A⁻¹| |A| |x| + |A⁻¹| |b|‖_∞ / ((1 - γ ‖|A⁻¹| |A|‖_∞) ‖x‖_∞)` and
`‖δx‖_∞ / ‖x‖_∞ ≤ 2γ / (1 - γ ‖|A⁻¹| |A|‖_∞) ‖|A⁻¹| |A|‖_∞` (the book's second line prints
`‖A⁻¹||A|‖_∞`). Backbone `Matrix.norm_sub_le_of_abs_le_abs`, [higham2002accuracy] Theorem 7.4
with `E = |A|`, `f = |b|`; `‖|A⁻¹| |A|‖_∞` is the Skeel condition number `Matrix.skeelCond A`. -/
theorem equation_3_15 (hA : IsUnit A) (hx : A *ᵥ x = b) (hb : b ≠ 0)
    (hδx : (A + δA) *ᵥ (x + δx) = b + δb) {γ : ℝ} (hγ : 0 ≤ γ) (hδA : δA.abs ≤ₑ γ • A.abs)
    (hδb : |δb| ≤ γ • |b|) (hsmall : γ * ‖A⁻¹.abs * A.abs‖ < 1) :
    ‖δx‖ / ‖x‖ ≤ γ * ‖A⁻¹.abs *ᵥ (A.abs *ᵥ |x|) + A⁻¹.abs *ᵥ |b|‖ /
        ((1 - γ * ‖A⁻¹.abs * A.abs‖) * ‖x‖) ∧
      ‖δx‖ / ‖x‖ ≤ 2 * γ / (1 - γ * ‖A⁻¹.abs * A.abs‖) * ‖A⁻¹.abs * A.abs‖ := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hb (by rw [← hx, mulVec_zero])
  have h := norm_sub_le_of_abs_le_abs hA hx hδx hγ hδA hδb hsmall hx0
  rwa [add_sub_cancel_left] at h

/-- **(3.16), the case `δb = 0`.** If `|δA| ≤ γ |A|` and `(A + δA)(x + δx) = b`, then for every
`i`, `|δx_i| ≤ γ |r_(i)ᵀ| |A| |x + δx|`, where `r_(i)ᵀ = e_iᵀ A⁻¹` is the `i`-th row of `A⁻¹`
(backbone `Matrix.abs_sub_apply_le_of_abs_le_abs`). -/
theorem equation_3_16_a (hA : IsUnit A) (hx : A *ᵥ x = b) (hδx : (A + δA) *ᵥ (x + δx) = b)
    {γ : ℝ} (hδA : δA.abs ≤ₑ γ • A.abs) (i : Fin n) :
    |δx i| ≤ γ * (|A⁻¹ i| ⬝ᵥ (A.abs *ᵥ |x + δx|)) := by
  have h := abs_sub_apply_le_of_abs_le_abs hA hx hδx hδA i
  rwa [Pi.add_apply, add_sub_cancel_left] at h

/-- **(3.16), the case `δA = 0`.** If `|δb| ≤ γ |b|` and `A (x + δx) = b + δb`, then for every
`i`, `|δx_i| / |x_i| ≤ γ |r_(i)ᵀ| |b| / |r_(i)ᵀ b|`, with `r_(i)ᵀ = e_iᵀ A⁻¹` the `i`-th row of
`A⁻¹` (backbone `Matrix.abs_sub_apply_div_le_of_abs_le_abs`). -/
theorem equation_3_16_b (hA : IsUnit A) (hx : A *ᵥ x = b) (hδx : A *ᵥ (x + δx) = b + δb)
    {γ : ℝ} (hδb : |δb| ≤ γ • |b|) (i : Fin n) :
    |δx i| / |x i| ≤ γ * (|A⁻¹ i| ⬝ᵥ |b|) / |A⁻¹ i ⬝ᵥ b| := by
  have h := abs_sub_apply_div_le_of_abs_le_abs hA hx hδx hδb i
  rwa [Pi.add_apply, add_sub_cancel_left] at h

/-- **Example 3.1, the matrix** `A = [α, 1/α; 0, 1/α]`. -/
noncomputable def example_3_1_matrix (α : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![α, α⁻¹; 0, α⁻¹]

/-- The inverse of the matrix of Example 3.1, `A⁻¹ = [1/α, -1/α; 0, α]`. -/
private theorem example_3_1_matrix_inv {α : ℝ} (hα : 0 < α) :
    (example_3_1_matrix α)⁻¹ = !![α⁻¹, -α⁻¹; 0, α] := by
  refine inv_eq_right_inv ?_
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [example_3_1_matrix, Matrix.mul_apply, Fin.sum_univ_two, hα.ne']

/-- **Example 3.1, (3.17).** For `0 < α`, the system with `A = [α, 1/α; 0, 1/α]` and
`b = (α² + 1/α, 1/α)` has the solution `x = (α, 1)`, and
`|A⁻¹| |A| |x| = |A⁻¹| |b| = (α + 2/α², 1)`, unbounded as `α → 0`; the amplification factor of
(3.16) for the component of maximum absolute value, `x₂`, is `|r_(2)ᵀ| |A| |x| / |x₂| = 1`.
(The book takes `0 < α < 1`; the identities hold for every `α > 0`.) -/
theorem example_3_1 {α : ℝ} (hα : 0 < α) :
    example_3_1_matrix α *ᵥ ![α, 1] = ![α ^ 2 + α⁻¹, α⁻¹] ∧
      (example_3_1_matrix α)⁻¹.abs *ᵥ ((example_3_1_matrix α).abs *ᵥ |![α, 1]|) =
        ![α + 2 / α ^ 2, 1] ∧
      (example_3_1_matrix α)⁻¹.abs *ᵥ |![α ^ 2 + α⁻¹, α⁻¹]| = ![α + 2 / α ^ 2, 1] ∧
      |(example_3_1_matrix α)⁻¹ 1| ⬝ᵥ ((example_3_1_matrix α).abs *ᵥ |![α, 1]|) / |![α, 1] 1|
        = 1 := by
  have hinv := example_3_1_matrix_inv hα
  have hα' : 0 < α⁻¹ := inv_pos.mpr hα
  have habs : |![α, (1 : ℝ)]| = ![α, 1] := by
    ext i; fin_cases i <;> simp [abs_of_pos hα]
  have habsb : |![α ^ 2 + α⁻¹, α⁻¹]| = ![α ^ 2 + α⁻¹, α⁻¹] := by
    ext i; fin_cases i <;> simp [abs_of_pos, hα', add_pos (pow_pos hα 2) hα']
  have hAabs : (example_3_1_matrix α).abs = example_3_1_matrix α := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [example_3_1_matrix, abs_of_pos hα, abs_of_pos hα']
  have hAinvabs : (example_3_1_matrix α)⁻¹.abs = !![α⁻¹, α⁻¹; 0, α] := by
    rw [hinv]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [abs_of_pos hα, abs_of_pos hα']
  have hAx : example_3_1_matrix α *ᵥ ![α, 1] = ![α ^ 2 + α⁻¹, α⁻¹] := by
    ext i
    fin_cases i <;> simp [example_3_1_matrix, mulVec, dotProduct, Fin.sum_univ_two, sq]
  have hAb : !![α⁻¹, α⁻¹; 0, α] *ᵥ ![α ^ 2 + α⁻¹, α⁻¹] = ![α + 2 / α ^ 2, 1] := by
    ext i
    fin_cases i
    · simp [mulVec, dotProduct, Fin.sum_univ_two]
      field_simp
      ring
    · simp [mulVec, dotProduct, Fin.sum_univ_two]
      field_simp
  refine ⟨hAx, ?_, ?_, ?_⟩
  · rw [habs, hAabs, hAx, hAinvabs, hAb]
  · rw [hAinvabs, habsb, hAb]
  · rw [habs, hAabs, hAx, hinv]
    simp [dotProduct, Fin.sum_univ_two, abs_of_pos hα]
    field_simp

end Componentwise

/-! ### §3.1.3: backward a priori analysis, Property 3.1 -/

section Backward

variable {A C : Matrix (Fin n) (Fin n) ℝ}

/-- **Property 3.1, the first clause.** Let `R = A C - I`; if `‖R‖ < 1` in an induced `p`-norm
then `A` and `C` are nonsingular (backbone `isUnit_of_norm_mul_sub_one_lt` in the operator ring
of `PiLp p (Fin n → ℝ)`, which is Dedekind-finite because the matrix ring is). -/
theorem property_3_1_isUnit (hR : lpOpNorm p (A * C - 1) < 1) : IsUnit A ∧ IsUnit C := by
  have h : ‖lpCLM p A * lpCLM p C - 1‖ < 1 := by
    rw [← lpCLM_mul, ← lpCLM_one, ← lpCLM_sub]
    exact hR
  obtain ⟨hA, hC⟩ := isUnit_of_norm_mul_sub_one_lt h
  exact ⟨(isUnit_lpCLM_iff p A).mp hA, (isUnit_lpCLM_iff p C).mp hC⟩

/-- **Property 3.1, (3.18), the first bound.** If `‖A C - I‖ < 1` then
`‖A⁻¹‖ ≤ ‖C‖ / (1 - ‖A C - I‖)` (backbone `NormedRing.norm_inverse_le_of_norm_mul_sub_one_lt`). -/
theorem property_3_1_inv [NeZero n] (hR : lpOpNorm p (A * C - 1) < 1) :
    lpOpNorm p A⁻¹ ≤ lpOpNorm p C / (1 - lpOpNorm p (A * C - 1)) := by
  have h : ‖lpCLM p A * lpCLM p C - 1‖ < 1 := by
    rw [← lpCLM_mul, ← lpCLM_one, ← lpCLM_sub]
    exact hR
  have hA := (isUnit_lpCLM_iff p A).mpr (property_3_1_isUnit hR).1
  have hle := NormedRing.norm_inverse_le_of_norm_mul_sub_one_lt hA h
  rwa [ringInverse_lpCLM, ← lpCLM_mul, ← lpCLM_one, ← lpCLM_sub] at hle

/-- **Property 3.1, (3.18), the second display.** If `‖A C - I‖ < 1` then
`‖A C - I‖ / ‖A‖ ≤ ‖C - A⁻¹‖ ≤ ‖C‖ ‖A C - I‖ / (1 - ‖A C - I‖)` (backbone
`NormedRing.norm_mul_sub_one_div_norm_le_norm_sub_inverse` and
`NormedRing.norm_sub_inverse_le_of_norm_mul_sub_one_lt`). -/
theorem property_3_1_sub [NeZero n] (hR : lpOpNorm p (A * C - 1) < 1) :
    lpOpNorm p (A * C - 1) / lpOpNorm p A ≤ lpOpNorm p (C - A⁻¹) ∧
      lpOpNorm p (C - A⁻¹) ≤
        lpOpNorm p C * lpOpNorm p (A * C - 1) / (1 - lpOpNorm p (A * C - 1)) := by
  have h : ‖lpCLM p A * lpCLM p C - 1‖ < 1 := by
    rw [← lpCLM_mul, ← lpCLM_one, ← lpCLM_sub]
    exact hR
  have hA := (isUnit_lpCLM_iff p A).mpr (property_3_1_isUnit hR).1
  have h1 := NormedRing.norm_mul_sub_one_div_norm_le_norm_sub_inverse (c := lpCLM p C) hA
  have h2 := NormedRing.norm_sub_inverse_le_of_norm_mul_sub_one_lt hA h
  rw [ringInverse_lpCLM, ← lpCLM_sub, ← lpCLM_mul, ← lpCLM_one, ← lpCLM_sub] at h1 h2
  exact ⟨h1, h2⟩

/-- **(3.19).** Interpreting `C` as the exact inverse of a perturbed matrix `A + δA`, that is
`C (A + δA) = I` and `δA = C⁻¹ - A`: if `‖R‖ < 1` for `R = C A - I` — the roles of `A` and `C`
in Property 3.1 interchanged, as the book's derivation requires — then
`‖δA‖ ≤ ‖R‖ ‖A‖ / (1 - ‖R‖)` (backbone `NormedRing.norm_sub_le_of_norm_mul_sub_one_lt`). -/
theorem equation_3_19 [NeZero n] (hR : lpOpNorm p (C * A - 1) < 1) :
    lpOpNorm p (C⁻¹ - A) ≤
      lpOpNorm p (C * A - 1) * lpOpNorm p A / (1 - lpOpNorm p (C * A - 1)) := by
  have h : ‖lpCLM p C * lpCLM p A - 1‖ < 1 := by
    rw [← lpCLM_mul, ← lpCLM_one, ← lpCLM_sub]
    exact hR
  have hC := (isUnit_lpCLM_iff p C).mpr (property_3_1_isUnit hR).1
  have hle := NormedRing.norm_sub_le_of_norm_mul_sub_one_lt hC h
  rwa [ringInverse_lpCLM, ← lpCLM_sub, ← lpCLM_mul, ← lpCLM_one, ← lpCLM_sub] at hle

end Backward

/-! ### §3.1.4: a posteriori analysis -/

section Posteriori

variable {A C : Matrix (Fin n) (Fin n) ℝ} {b x : Fin n → ℝ}

/-- **(3.20).** Let `x` solve `A x = b`, let `y` be any approximate solution with residual
`r = b - A y` and error `e = y - x`, and let `C` be an approximate inverse with
`‖R‖ = ‖A C - I‖ < 1`. Then `‖e‖ ≤ ‖r‖ ‖C‖ / (1 - ‖R‖)` (backbone
`norm_error_le_of_norm_mul_sub_one_lt`); `y` need not be the `C b` of the backward analysis. -/
theorem equation_3_20 (hR : lpOpNorm p (A * C - 1) < 1) (hx : A *ᵥ x = b) (y : Fin n → ℝ) :
    ‖toLp p (y - x)‖ ≤
      ‖toLp p (b - A *ᵥ y)‖ * lpOpNorm p C / (1 - lpOpNorm p (A * C - 1)) := by
  have hA := (property_3_1_isUnit hR).1
  have h : ‖(lpEquiv p hA : _ →L[ℝ] _) * lpCLM p C - 1‖ < 1 := by
    rw [coe_lpEquiv, ← lpCLM_mul, ← lpCLM_one, ← lpCLM_sub]
    exact hR
  have hle := norm_error_le_of_norm_mul_sub_one_lt (lpEquiv p hA) (lpCLM p C) h
    (x := toLp p x) (b := toLp p b) (by rw [lpEquiv_apply, ofLp_toLp, hx]) (toLp p y)
  rwa [coe_lpEquiv, ← lpCLM_mul, ← lpCLM_one, ← lpCLM_sub, lpEquiv_apply, ofLp_toLp,
    ← toLp_sub, ← toLp_sub] at hle

/-- **(3.21).** Interpreting `δb` in (3.11) as the residual `r = b - A y` of an approximate
solution `y = x + δx`: for `A` nonsingular, `A x = b` with `b ≠ 0`, and any `y`,
`‖e‖ / ‖x‖ ≤ K(A) ‖r‖ / ‖b‖` with `e = y - x` (backbone
`relative_error_le_condNumber_mul_relative_residual`). -/
theorem equation_3_21 (hA : IsUnit A) (hx : A *ᵥ x = b) (hb : b ≠ 0) (y : Fin n → ℝ) :
    ‖toLp p (y - x)‖ / ‖toLp p x‖ ≤ condNumber p A * (‖toLp p (b - A *ᵥ y)‖ / ‖toLp p b‖) := by
  have h := relative_error_le_condNumber_mul_relative_residual (lpEquiv p hA) (x := toLp p x)
    (b := toLp p b) (y := toLp p y) (by rw [lpEquiv_apply, ofLp_toLp, hx])
    (by rwa [Ne, toLp_eq_zero])
  rw [coe_lpEquiv, ← condNumber_eq, lpEquiv_apply, ofLp_toLp, ← toLp_sub, ← toLp_sub] at h
  rwa [← neg_sub x y, toLp_neg, norm_neg]

open scoped Matrix.Norms.Operator in
/-- **§3.1.4, the LAPACK estimate.** Let `A x = b` with `A` nonsingular, let `y` be an
approximate solution, and let `r̂ = fl(b - A y)` be its residual computed in floating point with
unit roundoff `u`, `(n + 1) u < 1`, so that `r̂ = r + δr` with
`|δr| ≤ γ_{n+1} (|A| |y| + |b|)`, `γ_{n+1} = (n + 1) u / (1 - (n + 1) u)`. Then
`‖e‖_∞ / ‖y‖_∞ ≤ ‖|A⁻¹| (|r̂| + γ_{n+1} (|A| |y| + |b|))‖_∞ / ‖y‖_∞` for the error `e = y - x`.
The computed residual is an admissible `FloatingPoint.RoundsAffineStep m (-A) b y r̂` of the
relational model (backbone `FloatingPoint.exists_roundsAffineStep_eq_add` for the perturbation
`δr`, `Matrix.norm_sub_le_of_computedResidual` for the bound). -/
theorem computedResidualErrorBound {m : FloatingPoint.RoundingModel ℝ}
    (hu : ((n + 1 : ℕ) : ℝ) * m.u < 1) (hA : IsUnit A) (hx : A *ᵥ x = b) {y rhat : Fin n → ℝ}
    (hr : FloatingPoint.RoundsAffineStep m (-A) b y rhat) :
    ‖y - x‖ / ‖y‖ ≤
      ‖A⁻¹.abs *ᵥ (|rhat| + FloatingPoint.gamma m.u (n + 1) • (A.abs *ᵥ |y| + |b|))‖ / ‖y‖ := by
  have hu1 : m.u < 1 := by
    have h0 := m.u_nonneg
    have : m.u ≤ ((n + 1 : ℕ) : ℝ) * m.u := by
      have : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
      nlinarith
    exact this.trans_lt hu
  obtain ⟨ξ, hξ, hξle⟩ := FloatingPoint.exists_roundsAffineStep_eq_add hu1
    (by rwa [Fintype.card_fin]) hr
  have hneg : (-A).abs = A.abs := by
    ext i j
    simp
  rw [Fintype.card_fin, hneg] at hξle
  have hle := norm_sub_le_of_computedResidual hA hx (rhat := rhat) (δr := ξ)
    (by rw [hξ, neg_mulVec, sub_eq_neg_add]) hξle
  exact div_le_div_of_nonneg_right hle (norm_nonneg y)

end Posteriori

end QuarteroniSaccoSaleri.Chapter03
