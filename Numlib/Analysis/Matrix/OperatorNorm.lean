import Numlib.Analysis.Matrix.ToEuclideanLin
import Numlib.Analysis.Normed.Ring.CondNumber
import Numlib.LinearAlgebra.Matrix.Complexify

/-!
# The matrix norms induced by the vector `p`-norms

The operator `Matrix.lpCLM p A : PiLp p (fun _ ↦ 𝕜) →L[𝕜] PiLp p (fun _ ↦ 𝕜)`, `x ↦ A x` read on
the `ℓ^p` spaces, and its operator norm `Matrix.lpOpNorm p A = ‖lpCLM p A‖`, which is the matrix
norm `‖A‖_p = sup_{x ≠ 0} ‖A x‖_p / ‖x‖_p` induced by the vector `p`-norm (Saad, *Iterative
Methods for Sparse Linear Systems*, 2nd edition, §1.5 (1.7); Quarteroni–Sacco–Saleri, *Numerical
Mathematics*, §1.11 (1.19)–(1.20)).  Mathlib carries the induced norm only for `p = ∞`
(`Matrix.Norms.Operator`) and `p = 2` (`Matrix.Norms.L2Operator`), one scoped
`NormedAddCommGroup` instance each; a second instance on the same type is not an option for the
other values of `p`, so the general induced norm is a function of `p` and `A` and not an
instance.

The matrices are rectangular, `A : Matrix m n 𝕜`, wherever the statement makes sense; the
operator algebra results (`‖1‖ = 1`, invertibility, the condition number) are for square ones.

## Main definitions

* `Matrix.lpCLM p A`: the operator `x ↦ A x` on `PiLp p`, with `lpCLM_one`, `lpCLM_mul` (and
  its rectangular form `lpCLM_mul_eq_comp`), `lpCLM_add`, `lpCLM_smul`, `lpCLM_zero`.
* `Matrix.lpOpNorm p A`: its operator norm, the induced matrix `p`-norm.
* `Matrix.condNumberLp p A = ‖A‖_p ‖A⁻¹‖_p`: the condition number of a square matrix in the
  induced `p`-norm (Saad §1.13.2; Quarteroni–Sacco–Saleri §3.1.1 (3.4)), with Mathlib's junk
  value `A⁻¹ = 0` for a singular `A`, so that `condNumberLp p A = 0` then.
* `Matrix.lpEquiv hA`: an invertible matrix as a continuous linear equivalence of `PiLp p`.

## Main results

* `Matrix.lpOpNorm_one_eq_sup_sum_norm`: `‖A‖₁` is the largest absolute column sum
  (Saad §1.5 (1.13); Quarteroni–Sacco–Saleri §1.11, the "column sum norm"), and
  `Matrix.lpOpNorm_two`: `‖A‖₂` is Mathlib's scoped `L2Operator` norm.
* `Matrix.lpOpNorm_mul_le`: the induced norms are submultiplicative, `‖A B‖_p ≤ ‖A‖_p ‖B‖_p`.
* `Matrix.complexSpectralRadius_le_lpOpNorm`: `ρ(A) ≤ ‖A‖_p` for a real matrix (Saad §1.5;
  Quarteroni–Sacco–Saleri Theorem 1.4 for the induced norms), the spectral radius being that of
  the complexification, `Matrix.complexSpectralRadius` of
  `Numlib/LinearAlgebra/Matrix/Complexify`.
* `Matrix.isUnit_lpCLM_iff` and `Matrix.ringInverse_lpCLM`: `lpCLM p` reflects invertibility and
  carries Mathlib's junk-valued matrix inverse to the ring inverse of the operator, junk values
  included, so that `Matrix.condNumberLp_eq_condNumber` reads `κ_p(A)` as the
  `NormedRing.condNumber` of `lpCLM p A`; `Matrix.one_le_condNumberLp` and
  `Matrix.condNumberLp_smul` follow from it.

## TODO

The rest of the planned module (`plans/Numlib/Analysis/Matrix/OperatorNorm.toml`) is the norm
induced by an *arbitrary* vector norm.  A vector norm on `n → 𝕜` is a definite
`Seminorm 𝕜 (n → 𝕜)`, unbundled exactly as `Numlib/Analysis/Normed/Module/NormEquivalence` and
`Numlib/LinearAlgebra/Matrix/EpsilonNorm` already do, and the induced norm is
`inducedNorm q p A = ⨆ x : {x // p x ≤ 1}, q (A *ᵥ x)`, a function `Matrix m n 𝕜 → ℝ` bundled on
demand as a `Seminorm` (rectangular) or an `AlgebraNorm` (square), the form that
`spectralRadius_le_algebraNorm` and `tendsto_pow_of_algebraNorm_lt_one` consume; the vector
`p`-norms are the seminorms `lpSeminorm p`, and `lpOpNorm p = inducedNorm (lpSeminorm p)
(lpSeminorm p)` connects the two descriptions.  Then, in order: consistency of a matrix norm with
a pair of vector norms (`IsConsistent`), the seminorm axioms, `‖I‖ = 1` and submultiplicativity
of an induced norm (Quarteroni–Sacco–Saleri, *Numerical Mathematics*, Theorems 1.1 and 1.3); the
row-sum formula `lpOpNorm ⊤ A = ‖A‖` for the scoped `Operator` norm and `‖A‖₁ = ‖Aᵀ‖_∞`; the
spectral norm (their Theorem 1.2): `‖A‖₂² = ρ(Aᴴ A) = ρ(A Aᴴ)`, `‖A‖₂ = σ_max(A)` (the module
`Numlib/LinearAlgebra/Matrix/SVD` has it for square matrices, and its statement generalizes to
rectangular ones in place), `‖A‖₂ = ρ(A)` for Hermitian and for normal `A`, `‖U‖₂ = 1` for
unitary `U`, unitary invariance of `‖·‖₂` and `‖·‖_F`; the comparison inequalities between
`‖·‖₁`, `‖·‖₂`, `‖·‖_∞`, `‖·‖_F` and the entrywise maximum (their §1.11 and Exercise 17),
including `‖A‖₂ ≤ √(‖A‖₁ ‖A‖_∞)` and `‖A‖_F² = ∑ σ_i²`; a consistent norm bounds the spectral
radius (their Theorem 1.4, consistency being weaker than the submultiplicativity of
`spectralRadius_le_algebraNorm`); the induced-norm form of the ε-norm of
`Numlib/LinearAlgebra/Matrix/EpsilonNorm` (their Property 1.13) and `ρ(A) = inf ‖A‖` over the
induced norms (their (1.23)); a submultiplicative matrix norm has a consistent vector norm
`x ↦ N (x yᴴ)`; and the Frobenius norm is consistent with `‖·‖₂` (their Example 1.7).  The
spectral-radius statements come in a complex form (`spectralRadius ℂ A`) and a real form
(`Matrix.complexSpectralRadius A`), as elsewhere in the backbone.
-/

open Finset

open scoped ENNReal NNReal NormedRing

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {l m n : Type*} [Fintype l] [Fintype m] [Fintype n]
  (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-! ### The operator `x ↦ A x` on `PiLp p` -/

section CLM

variable [DecidableEq n]

/-- The operator `x ↦ A x` on `PiLp p (fun _ : n ↦ 𝕜)`, whose norm is the matrix `p`-norm
`‖A‖_p` induced by the vector `p`-norm. -/
noncomputable def lpCLM (A : Matrix m n 𝕜) :
    PiLp p (fun _ : n => 𝕜) →L[𝕜] PiLp p (fun _ : m => 𝕜) :=
  LinearMap.toContinuousLinearMap (toLpLin p p A)

@[simp]
theorem lpCLM_apply (A : Matrix m n 𝕜) (x : PiLp p (fun _ : n => 𝕜)) :
    lpCLM p A x = WithLp.toLp p (A *ᵥ WithLp.ofLp x) := rfl

theorem lpCLM_one : lpCLM p (1 : Matrix n n 𝕜) = 1 := by
  ext x i; simp

/-- Matrix multiplication is composition of the induced operators. -/
theorem lpCLM_mul_eq_comp [DecidableEq m] (A : Matrix l m 𝕜) (B : Matrix m n 𝕜) :
    lpCLM p (A * B) = (lpCLM p A).comp (lpCLM p B) := by
  ext x i; simp [← mulVec_mulVec]

/-- The square case of `Matrix.lpCLM_mul_eq_comp`: `lpCLM p` is multiplicative into the operator
algebra of `PiLp p`. -/
theorem lpCLM_mul (A B : Matrix n n 𝕜) : lpCLM p (A * B) = lpCLM p A * lpCLM p B :=
  lpCLM_mul_eq_comp p A B

theorem lpCLM_add (A B : Matrix m n 𝕜) : lpCLM p (A + B) = lpCLM p A + lpCLM p B := by
  ext x i; simp [add_mulVec]

theorem lpCLM_smul (c : 𝕜) (A : Matrix m n 𝕜) : lpCLM p (c • A) = c • lpCLM p A := by
  ext x i; simp [smul_mulVec]

@[simp]
theorem lpCLM_zero : lpCLM p (0 : Matrix m n 𝕜) = 0 := by
  ext x i; simp

/-! ### The induced norm `‖A‖_p` -/

/-- The matrix norm `‖A‖_p = sup_{x ≠ 0} ‖A x‖_p / ‖x‖_p` induced by the vector `p`-norm (Saad,
*Iterative Methods for Sparse Linear Systems*, §1.5 (1.7) at `q = p`; Quarteroni–Sacco–Saleri,
*Numerical Mathematics*, §1.11 (1.19)): the operator norm of `Matrix.lpCLM p A`. -/
noncomputable def lpOpNorm (A : Matrix m n 𝕜) : ℝ := ‖lpCLM p A‖

@[simp]
theorem lpOpNorm_zero : lpOpNorm p (0 : Matrix m n 𝕜) = 0 := by
  rw [lpOpNorm, lpCLM_zero, norm_zero]

theorem lpOpNorm_nonneg (A : Matrix m n 𝕜) : 0 ≤ lpOpNorm p A := norm_nonneg _

/-- The induced norms are submultiplicative, `‖A B‖_p ≤ ‖A‖_p ‖B‖_p` (Quarteroni–Sacco–Saleri,
*Numerical Mathematics*, §1.11, after Theorem 1.3). -/
theorem lpOpNorm_mul_le [DecidableEq m] (A : Matrix l m 𝕜) (B : Matrix m n 𝕜) :
    lpOpNorm p (A * B) ≤ lpOpNorm p A * lpOpNorm p B := by
  rw [lpOpNorm, lpCLM_mul_eq_comp]
  exact ContinuousLinearMap.opNorm_comp_le _ _

open scoped Matrix.Norms.L2Operator in
/-- For `p = 2` the induced norm is Mathlib's scoped `L2Operator` matrix norm. -/
theorem lpOpNorm_two (A : Matrix m n 𝕜) : lpOpNorm 2 A = ‖A‖ :=
  (l2_opNorm_def A).symm

/-- The `1`-norm `‖A‖₁ = max_j ∑_i |a_{ij}|` is the largest absolute column sum (Saad,
*Iterative Methods for Sparse Linear Systems*, §1.5 (1.13); Quarteroni–Sacco–Saleri, *Numerical
Mathematics*, §1.11, the "column sum norm").  Mathlib carries only the row-sum formula for the
`∞`-norm (`Matrix.linfty_opNorm_def`), so this is proved from the definition of the operator norm
on `PiLp 1`: the bound is the triangle inequality column by column, and it is attained at the
standard basis vector of the largest column. -/
theorem lpOpNorm_one_eq_sup_sum_norm (A : Matrix m n 𝕜) :
    lpOpNorm 1 A = ↑(univ.sup fun j => ∑ i, ‖A i j‖₊) := by
  refine le_antisymm ?_ ?_
  · refine ContinuousLinearMap.opNorm_le_bound _
      (univ.sup fun j => ∑ i, ‖A i j‖₊).coe_nonneg fun x => ?_
    rw [lpCLM_apply, PiLp.norm_eq_of_L1, PiLp.norm_eq_of_L1]
    calc ∑ i, ‖(A *ᵥ WithLp.ofLp x) i‖
        ≤ ∑ i, ∑ j, ‖A i j‖ * ‖WithLp.ofLp x j‖ := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [mulVec_apply_eq_sum]
          exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => norm_mul_le _ _)
      _ = ∑ j, (∑ i, ‖A i j‖) * ‖WithLp.ofLp x j‖ := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun j _ => (Finset.sum_mul _ _ _).symm
      _ ≤ ∑ j, ((univ.sup fun j => ∑ i, ‖A i j‖₊ : ℝ≥0) : ℝ) * ‖WithLp.ofLp x j‖ := by
          refine Finset.sum_le_sum fun j _ => ?_
          gcongr
          have h : (∑ i, ‖A i j‖₊) ≤ univ.sup fun j => ∑ i, ‖A i j‖₊ :=
            Finset.le_sup (f := fun j => ∑ i, ‖A i j‖₊) (mem_univ j)
          have h' := NNReal.coe_le_coe.mpr h
          push_cast at h'
          exact h'
      _ = _ := by rw [Finset.mul_sum]
  · have key : ∀ j : n, ((∑ i, ‖A i j‖₊ : ℝ≥0) : ℝ) ≤ ‖lpCLM 1 A‖ := by
      intro j
      have hx : ‖(WithLp.toLp 1 (Pi.single j (1 : 𝕜)) : PiLp 1 fun _ : n => 𝕜)‖ = 1 := by
        rw [PiLp.norm_eq_of_L1]
        simp [Pi.single_apply, apply_ite (‖·‖ : 𝕜 → ℝ), Finset.sum_ite_eq']
      have hle := (lpCLM 1 A).le_opNorm
        (WithLp.toLp 1 (Pi.single j (1 : 𝕜)) : PiLp 1 fun _ : n => 𝕜)
      rw [hx, mul_one, lpCLM_apply, PiLp.norm_eq_of_L1] at hle
      simp only [mulVec_single_one, col_apply] at hle
      push_cast
      exact hle
    have hsup : (univ.sup fun j => ∑ i, ‖A i j‖₊) ≤ ‖lpCLM 1 A‖₊ :=
      Finset.sup_le fun j _ => by rw [← NNReal.coe_le_coe, coe_nnnorm]; exact key j
    rw [lpOpNorm, ← coe_nnnorm]
    exact_mod_cast hsup

/-- A consistent matrix norm dominates the spectral radius (Saad, *Iterative Methods for Sparse
Linear Systems*, §1.5; Quarteroni–Sacco–Saleri, *Numerical Mathematics*, Theorem 1.4), stated for
the induced `p`-norms of a real matrix and the spectral radius of its complexification.  The
induced norms are submultiplicative, absolutely homogeneous and positive definite, which are the
three hypotheses of `Matrix.complexSpectralRadius_le_of_norm`; only positive definiteness needs an
argument, through the columns `A e_j`. -/
theorem complexSpectralRadius_le_lpOpNorm (A : Matrix n n ℝ) :
    A.complexSpectralRadius ≤ ENNReal.ofReal (lpOpNorm p A) := by
  have hzero : ∀ B : Matrix n n ℝ, ‖lpCLM p B‖₊ = 0 → B = 0 := by
    intro B hB
    have h : lpCLM p B = 0 := by simpa using hB
    ext i j
    have h2 : (lpCLM p B) (WithLp.toLp p (Pi.single j (1 : ℝ))) = 0 := by simp [h]
    have h3 := congrArg (fun y : PiLp p (fun _ : n => ℝ) => (WithLp.ofLp y : n → ℝ) i) h2
    simpa [mulVec_single_one, col_apply] using h3
  have hle := complexSpectralRadius_le_of_norm (fun B : Matrix n n ℝ => ‖lpCLM p B‖₊) A
    (fun B C => by rw [lpCLM_mul]; exact nnnorm_mul_le _ _)
    (fun r B => by rw [lpCLM_smul]; exact nnnorm_smul _ _) hzero
  rwa [lpOpNorm, ofReal_norm, enorm_eq_nnnorm]

end CLM

/-! ### Invertible matrices, and the condition number `κ_p(A)` -/

section Square

variable [DecidableEq n]

/-- The condition number `κ_p(A) = ‖A‖_p ‖A⁻¹‖_p` in the induced `p`-norm (Saad, *Iterative
Methods for Sparse Linear Systems*, §1.13.2; Quarteroni–Sacco–Saleri, *Numerical Mathematics*,
§3.1.1 (3.4)).  Mathlib's `A⁻¹` is `0` for a singular `A`, so `condNumberLp p A = 0` then, in
agreement with the junk value of `NormedRing.condNumber`. -/
noncomputable def condNumberLp (A : Matrix n n 𝕜) : ℝ :=
  lpOpNorm p A * lpOpNorm p A⁻¹

/-- `A` invertible as a matrix, as a continuous linear equivalence of `PiLp p`. -/
noncomputable def lpEquiv {A : Matrix n n 𝕜} (hA : IsUnit A) :
    PiLp p (fun _ : n => 𝕜) ≃L[𝕜] PiLp p (fun _ : n => 𝕜) :=
  LinearEquiv.toContinuousLinearEquiv
    (LinearEquiv.ofLinearMap (toLpLin p p A) (toLpLin p p A⁻¹)
      (by rw [← toLpLin_mul_same, mul_nonsing_inv _ ((isUnit_iff_isUnit_det A).mp hA),
        toLpLin_one])
      (by rw [← toLpLin_mul_same, nonsing_inv_mul _ ((isUnit_iff_isUnit_det A).mp hA),
        toLpLin_one]))

@[simp]
theorem lpEquiv_apply {A : Matrix n n 𝕜} (hA : IsUnit A) (x : PiLp p (fun _ : n => 𝕜)) :
    lpEquiv p hA x = WithLp.toLp p (A *ᵥ WithLp.ofLp x) := rfl

@[simp]
theorem lpEquiv_symm_apply {A : Matrix n n 𝕜} (hA : IsUnit A) (x : PiLp p (fun _ : n => 𝕜)) :
    (lpEquiv p hA).symm x = WithLp.toLp p (A⁻¹ *ᵥ WithLp.ofLp x) := rfl

theorem coe_lpEquiv {A : Matrix n n 𝕜} (hA : IsUnit A) :
    ((lpEquiv p hA : PiLp p (fun _ : n => 𝕜) →L[𝕜] PiLp p (fun _ : n => 𝕜))) = lpCLM p A := by
  ext x i; simp

theorem coe_lpEquiv_symm {A : Matrix n n 𝕜} (hA : IsUnit A) :
    (((lpEquiv p hA).symm : PiLp p (fun _ : n => 𝕜) →L[𝕜] PiLp p (fun _ : n => 𝕜))) =
      lpCLM p A⁻¹ := by
  ext x i; simp

/-- The operator `x ↦ A x` on `PiLp p` is invertible exactly when `A` is: a nonzero vector in the
kernel of a singular `A` is one in the kernel of the operator, and an invertible `A` gives
`Matrix.lpEquiv`. -/
theorem isUnit_lpCLM_iff (M : Matrix n n 𝕜) : IsUnit (lpCLM p M) ↔ IsUnit M := by
  refine ⟨fun hu => ?_, fun hM => ?_⟩
  · by_contra hM
    have hdet : M.det = 0 := by
      by_contra h
      exact hM ((isUnit_iff_isUnit_det M).2 (isUnit_iff_ne_zero.2 h))
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
    have hinj := (ContinuousLinearMap.isHomeomorph_of_isUnit hu).bijective.injective
    have h0 : lpCLM p M (WithLp.toLp p v) = lpCLM p M 0 := by simp [hv]
    exact hv0 (by simpa using congrArg WithLp.ofLp (hinj h0))
  · rw [← coe_lpEquiv p hM]
    exact ⟨(lpEquiv p hM).toUnit, rfl⟩

/-- The matrix inverse and the ring inverse of the induced operator agree, junk values included:
both vanish exactly when the matrix is singular. -/
theorem ringInverse_lpCLM (M : Matrix n n 𝕜) : Ring.inverse (lpCLM p M) = lpCLM p M⁻¹ := by
  by_cases hM : IsUnit M
  · have hdet : IsUnit M.det := (isUnit_iff_isUnit_det M).1 hM
    exact Ring.inverse_unit ⟨lpCLM p M, lpCLM p M⁻¹,
      by rw [← lpCLM_mul, mul_nonsing_inv _ hdet, lpCLM_one],
      by rw [← lpCLM_mul, nonsing_inv_mul _ hdet, lpCLM_one]⟩
  · rw [Ring.inverse_non_unit _ ((isUnit_lpCLM_iff p M).not.2 hM),
      nonsing_inv_apply_not_isUnit _ fun h => hM ((isUnit_iff_isUnit_det _).2 h), lpCLM_zero]

/-- The condition number `κ_p(A)` is the `NormedRing.condNumber` of the operator `x ↦ A x` on
`PiLp p`. -/
theorem condNumberLp_eq_condNumber (A : Matrix n n 𝕜) : condNumberLp p A = κ (lpCLM p A) := by
  rw [condNumberLp, NormedRing.condNumber, ringInverse_lpCLM, lpOpNorm, lpOpNorm]

/-- `κ_p` is invariant under scaling. -/
theorem condNumberLp_smul {c : 𝕜} (hc : c ≠ 0) (A : Matrix n n 𝕜) :
    condNumberLp p (c • A) = condNumberLp p A := by
  rw [condNumberLp_eq_condNumber, condNumberLp_eq_condNumber, lpCLM_smul,
    NormedRing.condNumber_smul hc]

/-- `κ_p(A) ≥ 1` for a nonsingular `A`. -/
theorem one_le_condNumberLp [Nonempty n] {A : Matrix n n 𝕜} (hA : IsUnit A) :
    1 ≤ condNumberLp p A := by
  rw [condNumberLp_eq_condNumber]
  exact NormedRing.one_le_condNumber ((isUnit_lpCLM_iff p A).2 hA)

/-- `κ_p(α I) = 1` for `α ≠ 0`, although `det (α I) = αⁿ`: the determinant is no indication of
conditioning. -/
theorem condNumberLp_smul_one [Nonempty n] {c : 𝕜} (hc : c ≠ 0) :
    condNumberLp p (c • (1 : Matrix n n 𝕜)) = 1 := by
  rw [condNumberLp_smul p hc, condNumberLp, lpOpNorm, lpOpNorm, inv_one, lpCLM_one, norm_one,
    mul_one]

end Square

end Matrix
