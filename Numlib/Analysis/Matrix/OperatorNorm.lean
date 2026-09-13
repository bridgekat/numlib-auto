import Numlib.Analysis.Matrix.SpectralNorm
import Numlib.Analysis.Matrix.ToEuclideanLin
import Numlib.Analysis.Normed.Lp.PiLp
import Numlib.Analysis.Normed.Module.NormEquivalence
import Numlib.Analysis.Normed.Ring.CondNumber
import Numlib.LinearAlgebra.Matrix.Complexify
import Numlib.LinearAlgebra.Matrix.EpsilonNorm
import Numlib.LinearAlgebra.Matrix.Order
import Numlib.LinearAlgebra.Matrix.SVD

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

## The norm induced by an arbitrary vector norm

A vector norm on `n → 𝕜` is a definite `Seminorm 𝕜 (n → 𝕜)`, unbundled exactly as
`Numlib/Analysis/Normed/Module/NormEquivalence` and `Numlib/LinearAlgebra/Matrix/EpsilonNorm`
do, and the norm it induces (with a second vector norm `q` on the codomain) is
`Matrix.inducedNorm q p A = ⨆ x : {x // p x ≤ 1}, q (A *ᵥ x)`, a function `Matrix m n 𝕜 → ℝ`
bundled on demand as `Matrix.inducedSeminorm` (rectangular) or `Matrix.inducedAlgebraNorm`
(square), the form that `spectralRadius_le_algebraNorm` and the `AlgebraNorm` lemmas of
`Numlib/Analysis/Normed/Algebra/SpectralRadius` consume. The vector `p`-norms are the seminorms
`Matrix.lpSeminorm p`, and `Matrix.lpOpNorm_eq_inducedNorm` connects the two descriptions.

* `Matrix.IsConsistent`: a matrix norm consistent with a pair of vector norms
  ([quarteroni2000numerical] Definition 1.20); `Matrix.le_inducedNorm_mul`,
  `Matrix.isConsistent_inducedNorm`, `Matrix.inducedNorm_mul_le`, `Matrix.inducedNorm_one`,
  `Matrix.inducedNorm_eq_iSup_div`, `Matrix.exists_inducedNorm_eq` (their Theorems 1.1 and 1.3);
  `Matrix.exists_isConsistent_of_mul_le`, the consistent vector norm `x ↦ N (x yᴴ)` of a
  submultiplicative matrix norm.
* `Matrix.lpOpNorm_top`, `Matrix.lpOpNorm_one_eq_linfty_opNorm_transpose`: the row-sum and
  column-sum formulas; `Matrix.lpOpNorm_le_card_rpow_mul_lpOpNorm_of_le` and `…_of_ge`, the
  comparison of the induced `p`-norms with the constants `card ^ (1/p - 1/q)`, and their
  instances `Matrix.l2_opNorm_le_sqrt_card_mul_linfty_opNorm`,
  `Matrix.l2_opNorm_le_sqrt_card_mul_lpOpNorm_one`.
* The spectral norm (their Theorem 1.2):
  `Matrix.l2_opNorm_sq_eq_spectralRadius_conjTranspose_mul_self` (`‖A‖₂² = ρ(Aᴴ A) = ρ(A Aᴴ)`),
  `Matrix.IsHermitian.l2_opNorm_eq_spectralRadius`,
  `Matrix.l2_opNorm_eq_spectralRadius_of_isStarNormal`, `Matrix.l2_opNorm_of_mem_unitaryGroup`,
  unitary invariance `Matrix.l2_opNorm_unitary_mul_mul_unitary` and
  `Matrix.frobenius_norm_unitary_mul_mul_unitary`, `Matrix.condNumber_l2_of_mem_unitaryGroup`,
  `Matrix.condNumber_l2_unitary_mul`, and `Matrix.PosDef.condNumber_l2_eq_div_eigenvalues`
  (`κ₂ = λ_max / λ_min`, their (3.5)).
* The Frobenius norm: `Matrix.frobenius_norm_sq_eq_trace` (their (1.18)),
  `Matrix.frobenius_norm_mulVec_le` (their Example 1.7), `Matrix.frobenius_norm_one`,
  `Matrix.frobenius_norm_sq_eq_sum_sq_singularValues` (their Exercise 16),
  `Matrix.l2_opNorm_le_frobenius_norm` and `Matrix.frobenius_norm_le_sqrt_rank_mul_l2_opNorm`
  (their Exercise 17), `Matrix.norm_entry_le_l2_opNorm`,
  `Matrix.l2_opNorm_le_sqrt_card_mul_of_forall_norm_le` and
  `Matrix.l2_opNorm_sq_le_lpOpNorm_one_mul_linfty_opNorm` (the estimates of their §1.11).
* The spectral radius: `Matrix.spectralRadius_le_of_isConsistent` and
  `Matrix.complexSpectralRadius_le_of_isConsistent` (their Theorem 1.4 for a consistent, not
  necessarily submultiplicative, norm; over `ℂ` by the book's eigenvector argument, over `ℝ`
  through the induced norm), `Matrix.exists_inducedNorm_le_spectralRadius_add` and its real
  form (their Property 1.13), `Matrix.complexSpectralRadius_eq_iInf_inducedNorm` (their (1.23)),
  `Matrix.l2_opNorm_le_lpOpNorm_of_isStarNormal`, and the Neumann bounds
  `Matrix.inducedNorm_inv_one_sub_le`, `Matrix.one_div_one_add_le_inducedNorm_inv_one_sub`
  (their (1.26)).
* `Matrix.linfty_opNorm_le_of_abs_entrywiseLE`: the `∞`-norm is monotone in the entrywise
  absolute values, which turns entrywise error bounds into normwise ones.
-/

open Finset

open scoped ENNReal NNReal NormedRing

/-! ### Seminorms on `n → 𝕜` over `RCLike 𝕜` -/

section Seminorm

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]

/-- Equivalence of norms for a definite seminorm on `n → 𝕜` over `RCLike 𝕜`: the real statement
`Seminorm.exists_bounds` applied to the restriction of scalars. -/
theorem Seminorm.exists_bounds_rclike (p : Seminorm 𝕜 (n → 𝕜)) (hp : ∀ x, p x = 0 → x = 0) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x, c * ‖x‖ ≤ p x ∧ p x ≤ C * ‖x‖ :=
  (p.restrictScalars ℝ).exists_bounds hp

omit [Fintype n] in
/-- A seminorm on `n → 𝕜` over `RCLike 𝕜` is continuous. -/
theorem Seminorm.continuous_rclike [Finite n] (p : Seminorm 𝕜 (n → 𝕜)) : Continuous p := by
  cases nonempty_fintype n
  exact (p.restrictScalars ℝ).continuous_of_finiteDimensional

end Seminorm

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

/-! ### Consistency and the norm induced by a pair of vector norms -/

section Induced

/-- A matrix norm `N` on `Matrix m n 𝕜` is *consistent* (compatible) with the vector norms `q`
on the codomain `m → 𝕜` and `p` on the domain `n → 𝕜` when `q (A x) ≤ N A * p x` for all `A`
and `x`; for square matrices one takes `q = p`. [quarteroni2000numerical] Definition 1.20. -/
def IsConsistent (N : Matrix m n 𝕜 → ℝ) (q : Seminorm 𝕜 (m → 𝕜)) (p : Seminorm 𝕜 (n → 𝕜)) :
    Prop :=
  ∀ A x, q (A *ᵥ x) ≤ N A * p x

/-- The matrix norm induced by the vector norms `p` on the domain and `q` on the codomain:
`‖A‖ = sup {q (A x) | p x ≤ 1}`, [quarteroni2000numerical] (1.20). The supremum is over the
closed unit ball rather than the sphere so that the index type is nonempty (it contains `0`);
it is a bounded supremum as soon as `p` is definite. -/
noncomputable def inducedNorm (q : Seminorm 𝕜 (m → 𝕜)) (p : Seminorm 𝕜 (n → 𝕜))
    (A : Matrix m n 𝕜) : ℝ :=
  ⨆ x : {x : n → 𝕜 // p x ≤ 1}, q (A *ᵥ x)

variable (q : Seminorm 𝕜 (m → 𝕜)) (p : Seminorm 𝕜 (n → 𝕜))

instance : Nonempty {x : n → 𝕜 // p x ≤ 1} := ⟨⟨0, by simp⟩⟩

omit [Fintype m] in
open scoped Matrix.Norms.Operator in
/-- The supremum defining `inducedNorm` is bounded when `p` is definite: the unit ball of `p`
is bounded in norm, and `q (A x) ≤ C ‖A x‖ ≤ C ‖A‖ ‖x‖`. -/
theorem bddAbove_range_inducedNorm [Finite m] (hp : ∀ x, p x = 0 → x = 0) (A : Matrix m n 𝕜) :
    BddAbove (Set.range fun x : {x : n → 𝕜 // p x ≤ 1} => q (A *ᵥ x)) := by
  cases nonempty_fintype m
  obtain ⟨c, C, hc, -, hcp⟩ := p.exists_bounds_rclike hp
  obtain ⟨Cq, hCq0, hCq⟩ := (q.restrictScalars ℝ).exists_le_mul_norm
  refine ⟨Cq * ‖A‖ * c⁻¹, ?_⟩
  rintro _ ⟨⟨x, hx⟩, rfl⟩
  have hxle : ‖x‖ ≤ c⁻¹ := by
    have h1 : c * ‖x‖ ≤ 1 := (hcp x).1.trans hx
    calc ‖x‖ = c⁻¹ * (c * ‖x‖) := by field_simp
      _ ≤ c⁻¹ * 1 := by gcongr
      _ = c⁻¹ := mul_one _
  calc q (A *ᵥ x) ≤ Cq * ‖A *ᵥ x‖ := hCq (A *ᵥ x)
    _ ≤ Cq * (‖A‖ * ‖x‖) := by gcongr; exact linfty_opNorm_mulVec A x
    _ ≤ Cq * (‖A‖ * c⁻¹) := by gcongr
    _ = Cq * ‖A‖ * c⁻¹ := by ring


variable {q p}

omit [Fintype m] in
/-- The induced norm is nonnegative. -/
theorem inducedNorm_nonneg (A : Matrix m n 𝕜) : 0 ≤ inducedNorm q p A :=
  Real.iSup_nonneg fun _ => apply_nonneg _ _

omit [Fintype m] in
/-- Every vector of the unit ball of `p` witnesses a lower bound for the induced norm. -/
theorem le_inducedNorm [Finite m] (hp : ∀ x, p x = 0 → x = 0) (A : Matrix m n 𝕜) {x : n → 𝕜}
    (hx : p x ≤ 1) : q (A *ᵥ x) ≤ inducedNorm q p A :=
  le_ciSup (bddAbove_range_inducedNorm q p hp A) ⟨x, hx⟩

omit [Fintype m] in
/-- The induced norm is the least constant bounding `q (A x)` on the unit ball of `p`. -/
theorem inducedNorm_le (A : Matrix m n 𝕜) {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ x, p x ≤ 1 → q (A *ᵥ x) ≤ M) : inducedNorm q p A ≤ M :=
  Real.iSup_le (fun x => h x.1 x.2) hM

omit [Fintype n] in
/-- Normalizing a vector by a definite seminorm puts it on the unit sphere. -/
private theorem apply_smul_inv (hp : ∀ x, p x = 0 → x = 0) {x : n → 𝕜} (hx : x ≠ 0) :
    p ((RCLike.ofReal (p x)⁻¹ : 𝕜) • x) = 1 := by
  have hpx : 0 < p x := lt_of_le_of_ne (apply_nonneg p x) fun h => hx (hp x h.symm)
  rw [map_smul_eq_mul, RCLike.norm_ofReal, abs_of_pos (inv_pos.2 hpx), inv_mul_cancel₀ hpx.ne']

omit [Fintype m] in
/-- **The induced norm is consistent** (`IsConsistent (inducedNorm q p) q p`, applied):
`q (A x) ≤ ‖A‖ p x` for every `x`, [quarteroni2000numerical] Theorem 1.3 (1). -/
theorem le_inducedNorm_mul [Finite m] (hp : ∀ x, p x = 0 → x = 0) (A : Matrix m n 𝕜)
    (x : n → 𝕜) :
    q (A *ᵥ x) ≤ inducedNorm q p A * p x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hpx : 0 < p x := lt_of_le_of_ne (apply_nonneg p x) fun h => hx (hp x h.symm)
  have h := le_inducedNorm (q := q) hp A (apply_smul_inv hp hx).le
  rw [mulVec_smul, map_smul_eq_mul, RCLike.norm_ofReal, abs_of_pos (inv_pos.2 hpx),
    inv_mul_le_iff₀ hpx, mul_comm] at h
  exact h

omit [Fintype m] in
/-- **The induced norm is consistent**, [quarteroni2000numerical] Theorem 1.3 (1). -/
theorem isConsistent_inducedNorm [Finite m] (hp : ∀ x, p x = 0 → x = 0) :
    IsConsistent (inducedNorm q p) q p :=
  fun A x => le_inducedNorm_mul hp A x

omit [Fintype m] in
/-- A consistent matrix norm dominates the induced norm: `inducedNorm q p A ≤ N A` whenever
`q (A x) ≤ N A * p x` for all `x`; the induced norm is the *least* consistent one. -/
theorem inducedNorm_le_of_isConsistent {N : Matrix m n 𝕜 → ℝ} (hN : IsConsistent N q p)
    (A : Matrix m n 𝕜) (hNA : 0 ≤ N A) : inducedNorm q p A ≤ N A :=
  inducedNorm_le A hNA fun x hx =>
    (hN A x).trans (by simpa using mul_le_mul_of_nonneg_left hx hNA)

omit [Fintype m] in
/-- **(1.19) equals (1.20)**: the induced norm is the supremum of the quotients `q (A x) / p x`
over `x ≠ 0`, [quarteroni2000numerical] Theorem 1.1. -/
theorem inducedNorm_eq_iSup_div [Finite m] (hp : ∀ x, p x = 0 → x = 0) (A : Matrix m n 𝕜) :
    inducedNorm q p A = ⨆ x : {x : n → 𝕜 // x ≠ 0}, q (A *ᵥ x) / p x := by
  have hbdd : BddAbove (Set.range fun x : {x : n → 𝕜 // x ≠ 0} => q (A *ᵥ x) / p x) := by
    refine ⟨inducedNorm q p A, ?_⟩
    rintro _ ⟨⟨x, hx⟩, rfl⟩
    have hpx : 0 < p x := lt_of_le_of_ne (apply_nonneg p x) fun h => hx (hp x h.symm)
    exact (div_le_iff₀ hpx).2 (le_inducedNorm_mul hp A x)
  refine le_antisymm (inducedNorm_le A (Real.iSup_nonneg fun x => by positivity)
    fun x hx => ?_) (Real.iSup_le (fun x => ?_) (inducedNorm_nonneg A))
  · rcases eq_or_ne x 0 with rfl | hx0
    · simpa using Real.iSup_nonneg (f := fun x : {x : n → 𝕜 // x ≠ 0} => q (A *ᵥ x) / p x)
        fun x => by positivity
    have hpx : 0 < p x := lt_of_le_of_ne (apply_nonneg p x) fun h => hx0 (hp x h.symm)
    calc q (A *ᵥ x) ≤ q (A *ᵥ x) / p x := by
          rw [le_div_iff₀ hpx]
          exact mul_le_of_le_one_right (apply_nonneg _ _) hx
      _ ≤ _ := le_ciSup hbdd ⟨x, hx0⟩
  · obtain ⟨x, hx⟩ := x
    have hpx : 0 < p x := lt_of_le_of_ne (apply_nonneg p x) fun h => hx (hp x h.symm)
    exact (div_le_iff₀ hpx).2 (le_inducedNorm_mul hp A x)

omit [Fintype m] in
/-- **The supremum defining the induced norm is attained on the unit sphere** of a definite
`p`, when the index type is nonempty: the sphere is compact and `x ↦ q (A x)` is continuous.
This is the "`= ‖A w‖` with `‖w‖ = 1`" of the proof of [quarteroni2000numerical] Theorem 1.1. -/
theorem exists_inducedNorm_eq [Finite m] [Nonempty n] (hp : ∀ x, p x = 0 → x = 0)
    (A : Matrix m n 𝕜) : ∃ x, p x = 1 ∧ inducedNorm q p A = q (A *ᵥ x) := by
  classical
  cases nonempty_fintype m
  obtain ⟨c, C, hc, -, hcp⟩ := p.exists_bounds_rclike hp
  -- the unit sphere of `p` is compact and nonempty
  have hclosed : IsClosed {x : n → 𝕜 | p x = 1} :=
    isClosed_eq p.continuous_rclike continuous_const
  have hbdd : Bornology.IsBounded {x : n → 𝕜 | p x = 1} := by
    refine (Metric.isBounded_closedBall (x := (0 : n → 𝕜)) (r := c⁻¹)).subset fun x hx => ?_
    rw [Metric.mem_closedBall, dist_zero_right]
    have h1 : c * ‖x‖ ≤ 1 := (hcp x).1.trans (le_of_eq hx)
    calc ‖x‖ = c⁻¹ * (c * ‖x‖) := by field_simp
      _ ≤ c⁻¹ * 1 := by gcongr
      _ = c⁻¹ := mul_one _
  have hcompact : IsCompact {x : n → 𝕜 | p x = 1} :=
    Metric.isCompact_of_isClosed_isBounded hclosed hbdd
  have hne : ({x : n → 𝕜 | p x = 1} : Set (n → 𝕜)).Nonempty := by
    have h0 : (Pi.single (Classical.arbitrary n) (1 : 𝕜) : n → 𝕜) ≠ 0 := by
      intro h
      have := congrFun h (Classical.arbitrary n)
      simp at this
    exact ⟨_, apply_smul_inv hp h0⟩
  have hcont : Continuous fun x : n → 𝕜 => q (A *ᵥ x) :=
    q.continuous_rclike.comp (mulVecLin A).continuous_of_finiteDimensional
  obtain ⟨x, hx, hmax⟩ := hcompact.exists_isMaxOn hne hcont.continuousOn
  refine ⟨x, hx, le_antisymm (inducedNorm_le A (apply_nonneg _ _) fun y hy => ?_)
    (le_inducedNorm hp A hx.le)⟩
  rcases eq_or_ne y 0 with rfl | hy0
  · simp
  have hpy : 0 < p y := lt_of_le_of_ne (apply_nonneg p y) fun h => hy0 (hp y h.symm)
  have hmem : (RCLike.ofReal (p y)⁻¹ : 𝕜) • y ∈ {x : n → 𝕜 | p x = 1} := apply_smul_inv hp hy0
  have h := hmax hmem
  simp only [Set.mem_ofPred_eq, mulVec_smul, map_smul_eq_mul, RCLike.norm_ofReal,
    abs_of_pos (inv_pos.2 hpy)] at h
  calc q (A *ᵥ y) = p y * ((p y)⁻¹ * q (A *ᵥ y)) := by field_simp
    _ ≤ 1 * q (A *ᵥ x) := by gcongr
    _ = q (A *ᵥ x) := one_mul _

/-- **The induced norm is a seminorm on matrices**, [quarteroni2000numerical] Theorem 1.1
(items 2 and 3): absolutely homogeneous and subadditive. -/
noncomputable def inducedSeminorm (q : Seminorm 𝕜 (m → 𝕜)) (p : Seminorm 𝕜 (n → 𝕜))
    (hp : ∀ x, p x = 0 → x = 0) : Seminorm 𝕜 (Matrix m n 𝕜) where
  toFun := inducedNorm q p
  map_zero' := by simp [inducedNorm]
  add_le' A B := inducedNorm_le (A + B) (add_nonneg (inducedNorm_nonneg A) (inducedNorm_nonneg B))
    fun x hx => by
      rw [add_mulVec]
      exact (map_add_le_add q _ _).trans
        (add_le_add (le_inducedNorm hp A hx) (le_inducedNorm hp B hx))
  neg' A := by simp [inducedNorm, neg_mulVec]
  smul' c A := by
    change (⨆ x : {x : n → 𝕜 // p x ≤ 1}, q ((c • A) *ᵥ x))
      = ‖c‖ * ⨆ x : {x : n → 𝕜 // p x ≤ 1}, q (A *ᵥ x)
    simp_rw [smul_mulVec, map_smul_eq_mul]
    exact (Real.mul_iSup_of_nonneg (norm_nonneg c) _).symm

@[simp]
theorem inducedSeminorm_apply (hp : ∀ x, p x = 0 → x = 0) (A : Matrix m n 𝕜) :
    inducedSeminorm q p hp A = inducedNorm q p A := rfl

omit [Fintype m] in
/-- **The induced norm is definite** when `q` and `p` are, [quarteroni2000numerical]
Theorem 1.1 (item 1). -/
theorem inducedNorm_eq_zero_iff [Finite m] (hq : ∀ y, q y = 0 → y = 0)
    (hp : ∀ x, p x = 0 → x = 0) (A : Matrix m n 𝕜) : inducedNorm q p A = 0 ↔ A = 0 := by
  classical
  refine ⟨fun h => ?_, fun h => by simp [h, inducedNorm]⟩
  ext i j
  have hle := le_inducedNorm_mul (q := q) hp A (Pi.single j (1 : 𝕜))
  rw [h, zero_mul] at hle
  have hcol : A *ᵥ Pi.single j 1 = 0 := hq _ (le_antisymm hle (apply_nonneg _ _))
  simpa [mulVec_single_one] using congrFun hcol i

variable (r : Seminorm 𝕜 (l → 𝕜))

omit [Fintype l] in
/-- **Submultiplicativity of the induced norms**, rectangular form:
`‖A B‖_{r,p} ≤ ‖A‖_{r,q} ‖B‖_{q,p}`, [quarteroni2000numerical] Theorem 1.3 (3). -/
theorem inducedNorm_mul_le [Finite l] (hp : ∀ x, p x = 0 → x = 0) (hq : ∀ y, q y = 0 → y = 0)
    (A : Matrix l m 𝕜) (B : Matrix m n 𝕜) :
    inducedNorm r p (A * B) ≤ inducedNorm r q A * inducedNorm q p B :=
  inducedNorm_le (A * B) (mul_nonneg (inducedNorm_nonneg A) (inducedNorm_nonneg B)) fun x hx =>
    calc r ((A * B) *ᵥ x) = r (A *ᵥ (B *ᵥ x)) := by rw [mulVec_mulVec]
      _ ≤ inducedNorm r q A * q (B *ᵥ x) := le_inducedNorm_mul hq A _
      _ ≤ inducedNorm r q A * inducedNorm q p B := by
          gcongr
          · exact inducedNorm_nonneg A
          · exact le_inducedNorm hp B hx

variable {r}

/-- **The induced norm of the identity is `1`**, [quarteroni2000numerical] Theorem 1.3 (2). -/
theorem inducedNorm_one [DecidableEq n] [Nonempty n] (hp : ∀ x, p x = 0 → x = 0) :
    inducedNorm p p (1 : Matrix n n 𝕜) = 1 := by
  refine le_antisymm (inducedNorm_le 1 zero_le_one fun x hx => by simpa using hx) ?_
  have h0 : (Pi.single (Classical.arbitrary n) (1 : 𝕜) : n → 𝕜) ≠ 0 := by
    intro h
    have := congrFun h (Classical.arbitrary n)
    simp at this
  have h := le_inducedNorm (q := p) hp (1 : Matrix n n 𝕜) (apply_smul_inv hp h0).le
  rwa [one_mulVec, apply_smul_inv hp h0] at h

/-- A submultiplicative norm with `N 1 ≠ 0` has `1 ≤ N 1`: the remark after
[quarteroni2000numerical] Theorem 1.3 that submultiplicativity alone gives only `‖I‖ ≥ 1`. -/
theorem one_le_of_mul_le [DecidableEq n] {N : Matrix n n 𝕜 → ℝ}
    (hmul : ∀ A B, N (A * B) ≤ N A * N B)
    (h0 : 0 ≤ N 1) (h1 : N 1 ≠ 0) : 1 ≤ N 1 := by
  have h := hmul 1 1
  rw [mul_one] at h
  nlinarith [lt_of_le_of_ne h0 (Ne.symm h1)]

/-- **The square induced norm as an algebra norm** on `Matrix n n 𝕜`: [quarteroni2000numerical]
Theorems 1.1 and 1.3 bundled, so that `spectralRadius_le_algebraNorm`,
`tendsto_pow_of_algebraNorm_lt_one` and the `AlgebraNorm` lemmas of
`Numlib/Analysis/Normed/Algebra/SpectralRadius` apply. -/
noncomputable def inducedAlgebraNorm [DecidableEq n] (p : Seminorm 𝕜 (n → 𝕜))
    (hp : ∀ x, p x = 0 → x = 0) : AlgebraNorm 𝕜 (Matrix n n 𝕜) :=
  { inducedSeminorm p p hp with
    mul_le' := inducedNorm_mul_le p hp hp
    eq_zero_of_map_eq_zero' := fun A h => (inducedNorm_eq_zero_iff hp hp A).1 h }

@[simp]
theorem inducedAlgebraNorm_apply [DecidableEq n] (hp : ∀ x, p x = 0 → x = 0)
    (A : Matrix n n 𝕜) : inducedAlgebraNorm p hp A = inducedNorm p p A := rfl

end Induced

/-! ### The vector `p`-norms as seminorms, and `lpOpNorm` as an induced norm -/

section LpSeminorm

variable (r : ℝ≥0∞) [Fact (1 ≤ r)]

/-- The vector `r`-norm `(∑ ‖x i‖ ^ r) ^ (1 / r)` of [quarteroni2000numerical] (1.13) (the
maximum norm at `r = ∞`) as a seminorm on plain functions `n → 𝕜`: `lpSeminorm r x = ‖toLp r x‖`,
definitionally. -/
noncomputable def lpSeminorm : Seminorm 𝕜 (n → 𝕜) :=
  (normSeminorm 𝕜 (PiLp r fun _ : n => 𝕜)).comp (WithLp.linearEquiv r 𝕜 (n → 𝕜)).symm.toLinearMap

@[simp]
theorem lpSeminorm_apply (x : n → 𝕜) : lpSeminorm r x = ‖WithLp.toLp r x‖ := rfl

/-- The vector `r`-norms are definite. -/
theorem lpSeminorm_eq_zero_iff (x : n → 𝕜) : lpSeminorm r x = 0 ↔ x = 0 := by
  rw [lpSeminorm_apply, norm_eq_zero, WithLp.toLp_eq_zero]

/-- The vector `r`-norms are definite, in the form the induced-norm lemmas take. -/
theorem lpSeminorm_definite : ∀ x : n → 𝕜, lpSeminorm r x = 0 → x = 0 :=
  fun x => (lpSeminorm_eq_zero_iff r x).1

variable [DecidableEq n]

/-- **`‖A‖_r` is the norm induced by the vector `r`-norm**: the two descriptions of the matrix
`r`-norm, as the operator norm of `x ↦ A x` on `PiLp r` and as `inducedNorm` of `lpSeminorm r`,
agree. -/
theorem lpOpNorm_eq_inducedNorm (A : Matrix m n 𝕜) :
    lpOpNorm r A = inducedNorm (lpSeminorm r) (lpSeminorm r) A := by
  rw [lpOpNorm, ← ContinuousLinearMap.sSup_unitClosedBall_eq_norm, inducedNorm, iSup]
  congr 1
  ext t
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨WithLp.ofLp y, by simpa [Metric.mem_closedBall] using hy⟩, by simp⟩
  · rintro ⟨⟨x, hx⟩, rfl⟩
    exact ⟨WithLp.toLp r x, by simpa [Metric.mem_closedBall] using hx, by simp⟩

/-- **`‖A‖_r` is consistent with the vector `r`-norm**: `‖A x‖_r ≤ ‖A‖_r ‖x‖_r`. -/
theorem lpSeminorm_mulVec_le (A : Matrix m n 𝕜) (x : n → 𝕜) :
    lpSeminorm r (A *ᵥ x) ≤ lpOpNorm r A * lpSeminorm r x := by
  have h := (lpCLM r A).le_opNorm (WithLp.toLp r x)
  rwa [lpCLM_apply, WithLp.ofLp_toLp] at h

/-- `‖A‖_r` is consistent with the vector `r`-norm, bundled. -/
theorem isConsistent_lpOpNorm :
    IsConsistent (fun A : Matrix m n 𝕜 => lpOpNorm r A) (lpSeminorm r) (lpSeminorm r) :=
  fun A x => lpSeminorm_mulVec_le r A x

open scoped Matrix.Norms.Operator in
/-- **`‖A‖_∞` is the largest absolute row sum**: `lpOpNorm ⊤ A` is Mathlib's scoped `Operator`
norm (`Matrix.linfty_opNorm_def`), [quarteroni2000numerical] §1.11, the "row sum norm". -/
theorem lpOpNorm_top (A : Matrix m n 𝕜) : lpOpNorm ⊤ A = ‖A‖ := by
  rw [linfty_opNorm_eq_opNorm, lpOpNorm]
  refine le_antisymm (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_)
    (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_)
  · rw [lpCLM_apply, PiLp.norm_toLp, ← PiLp.norm_ofLp x]
    exact (ContinuousLinearMap.mk (mulVecLin A)).le_opNorm (WithLp.ofLp x)
  · have h := (lpCLM ⊤ A).le_opNorm (WithLp.toLp ⊤ v)
    rwa [lpCLM_apply, PiLp.norm_toLp, PiLp.norm_toLp, WithLp.ofLp_toLp] at h

open scoped Matrix.Norms.Operator in
/-- **`‖A‖₁ = ‖Aᵀ‖_∞`**: the column sum norm is the row sum norm of the transpose,
[quarteroni2000numerical] §1.11. -/
theorem lpOpNorm_one_eq_linfty_opNorm_transpose (A : Matrix m n 𝕜) : lpOpNorm 1 A = ‖Aᵀ‖ := by
  rw [lpOpNorm_one_eq_sup_sum_norm, linfty_opNorm_def]
  simp only [transpose_apply]

open scoped Matrix.Norms.Operator in
/-- `‖A‖₁ = ‖Aᴴ‖_∞`: conjugation does not change the absolute row sums. -/
theorem lpOpNorm_one_eq_linfty_opNorm_conjTranspose (A : Matrix m n 𝕜) :
    lpOpNorm 1 A = ‖Aᴴ‖ := by
  rw [lpOpNorm_one_eq_sup_sum_norm, linfty_opNorm_def]
  simp only [conjTranspose_apply, nnnorm_star]

open scoped Matrix.Norms.Operator in
/-- For a Hermitian matrix `‖A‖₁ = ‖A‖_∞`, [quarteroni2000numerical] §1.11. -/
theorem IsHermitian.lpOpNorm_one_eq_linfty_opNorm {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    lpOpNorm 1 A = ‖A‖ := by
  rw [lpOpNorm_one_eq_linfty_opNorm_conjTranspose, hA.eq]

end LpSeminorm

/-! ### Comparison of the induced `p`-norms -/

section Compare

variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [DecidableEq n]

/-- **The induced norms decrease in `p` up to `card m`**: for `p ≤ q`,
`‖A‖_p ≤ (card m) ^ (1 / p - 1 / q) ‖A‖_q`, from the vector comparison
`PiLp.norm_le_card_rpow_mul_norm` on the codomain and `PiLp.norm_le_norm_of_le` on the domain. -/
theorem lpOpNorm_le_card_rpow_mul_lpOpNorm_of_le (hpq : p ≤ q) (A : Matrix m n 𝕜) :
    lpOpNorm p A ≤ (Fintype.card m : ℝ) ^ (1 / p.toReal - 1 / q.toReal) * lpOpNorm q A := by
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (by positivity) (lpOpNorm_nonneg q A))
    fun x => ?_
  rw [lpCLM_apply]
  calc ‖WithLp.toLp p (A *ᵥ WithLp.ofLp x)‖
      ≤ (Fintype.card m : ℝ) ^ (1 / p.toReal - 1 / q.toReal) *
          ‖WithLp.toLp q (A *ᵥ WithLp.ofLp x)‖ := PiLp.norm_le_card_rpow_mul_norm hpq _
    _ ≤ (Fintype.card m : ℝ) ^ (1 / p.toReal - 1 / q.toReal) *
          (lpOpNorm q A * ‖WithLp.toLp q (WithLp.ofLp x)‖) := by
        gcongr
        have h := (lpCLM q A).le_opNorm (WithLp.toLp q (WithLp.ofLp x))
        rwa [lpCLM_apply, WithLp.ofLp_toLp] at h
    _ ≤ (Fintype.card m : ℝ) ^ (1 / p.toReal - 1 / q.toReal) * (lpOpNorm q A * ‖x‖) := by
        gcongr
        · exact lpOpNorm_nonneg q A
        · simpa using PiLp.norm_le_norm_of_le hpq (WithLp.ofLp x)
    _ = _ := by ring

/-- **The induced norms increase in `p` up to `card n`**: for `p ≤ q`,
`‖A‖_q ≤ (card n) ^ (1 / p - 1 / q) ‖A‖_p`, from the vector comparison
`PiLp.norm_le_norm_of_le` on the codomain and `PiLp.norm_le_card_rpow_mul_norm` on the domain. -/
theorem lpOpNorm_le_card_rpow_mul_lpOpNorm_of_ge (hpq : p ≤ q) (A : Matrix m n 𝕜) :
    lpOpNorm q A ≤ (Fintype.card n : ℝ) ^ (1 / p.toReal - 1 / q.toReal) * lpOpNorm p A := by
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (by positivity) (lpOpNorm_nonneg p A))
    fun x => ?_
  rw [lpCLM_apply]
  calc ‖WithLp.toLp q (A *ᵥ WithLp.ofLp x)‖
      ≤ ‖WithLp.toLp p (A *ᵥ WithLp.ofLp x)‖ := PiLp.norm_le_norm_of_le hpq _
    _ ≤ lpOpNorm p A * ‖WithLp.toLp p (WithLp.ofLp x)‖ := by
        have h := (lpCLM p A).le_opNorm (WithLp.toLp p (WithLp.ofLp x))
        rwa [lpCLM_apply, WithLp.ofLp_toLp] at h
    _ ≤ lpOpNorm p A * ((Fintype.card n : ℝ) ^ (1 / p.toReal - 1 / q.toReal) * ‖x‖) := by
        gcongr
        · exact lpOpNorm_nonneg p A
        · simpa using PiLp.norm_le_card_rpow_mul_norm hpq (WithLp.ofLp x)
    _ = _ := by ring

/-- **`‖A‖₂` against `‖A‖_∞`**: `‖A‖₂ ≤ √(card m) ‖A‖_∞` and `‖A‖_∞ ≤ √(card n) ‖A‖₂` for
`A : Matrix m n 𝕜`; for a square matrix of order `n`,
`n^{-1/2} ‖A‖_∞ ≤ ‖A‖₂ ≤ n^{1/2} ‖A‖_∞`, [quarteroni2000numerical] §1.11. -/
theorem l2_opNorm_le_sqrt_card_mul_linfty_opNorm (A : Matrix m n 𝕜) :
    lpOpNorm 2 A ≤ √(Fintype.card m : ℝ) * lpOpNorm ⊤ A ∧
      lpOpNorm ⊤ A ≤ √(Fintype.card n : ℝ) * lpOpNorm 2 A := by
  have h2 : (1 / (2 : ℝ≥0∞).toReal - 1 / (⊤ : ℝ≥0∞).toReal) = 1 / 2 := by norm_num
  constructor
  · have h := lpOpNorm_le_card_rpow_mul_lpOpNorm_of_le (p := 2) (q := ⊤) le_top A
    rwa [h2, ← Real.sqrt_eq_rpow] at h
  · have h := lpOpNorm_le_card_rpow_mul_lpOpNorm_of_ge (p := 2) (q := ⊤) le_top A
    rwa [h2, ← Real.sqrt_eq_rpow] at h

/-- **`‖A‖₂` against `‖A‖₁`**: `‖A‖₁ ≤ √(card m) ‖A‖₂` and `‖A‖₂ ≤ √(card n) ‖A‖₁` for
`A : Matrix m n 𝕜`; for a square matrix of order `n`,
`n^{-1/2} ‖A‖₁ ≤ ‖A‖₂ ≤ n^{1/2} ‖A‖₁`, [quarteroni2000numerical] §1.11. -/
theorem l2_opNorm_le_sqrt_card_mul_lpOpNorm_one (A : Matrix m n 𝕜) :
    lpOpNorm 1 A ≤ √(Fintype.card m : ℝ) * lpOpNorm 2 A ∧
      lpOpNorm 2 A ≤ √(Fintype.card n : ℝ) * lpOpNorm 1 A := by
  have h2 : (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) = 1 / 2 := by norm_num
  constructor
  · have h := lpOpNorm_le_card_rpow_mul_lpOpNorm_of_le (p := 1) (q := 2) (by norm_num) A
    rwa [h2, ← Real.sqrt_eq_rpow] at h
  · have h := lpOpNorm_le_card_rpow_mul_lpOpNorm_of_ge (p := 1) (q := 2) (by norm_num) A
    rwa [h2, ← Real.sqrt_eq_rpow] at h

end Compare

/-! ### The spectral radius and the induced norms -/

section SpectralRadius

variable [DecidableEq n] {p : Seminorm 𝕜 (n → 𝕜)}

/-- **A consistent norm bounds the spectral radius** ([quarteroni2000numerical] Theorem 1.4):
if `N` is consistent with a definite vector norm `p`, then `ρ(A) ≤ N A`, the spectral radius
being that of `spectrum 𝕜 A`. The book's one-line proof: for an eigenpair `A v = λ v`,
`|λ| p v = p (A v) ≤ N A p v` with `p v > 0`. No submultiplicativity of `N` is used, which is
what distinguishes this from `spectralRadius_le_algebraNorm`. Over `𝕜 = ℝ` the statement is
about the *real* spectrum; the complex spectral radius of a real matrix is
`Matrix.complexSpectralRadius_le_of_isConsistent`. -/
theorem spectralRadius_le_of_isConsistent {N : Matrix n n 𝕜 → ℝ} (hp : ∀ x, p x = 0 → x = 0)
    (hN : IsConsistent N p p) (A : Matrix n n 𝕜) :
    spectralRadius 𝕜 A ≤ ENNReal.ofReal (N A) := by
  refine iSup₂_le fun μ hμ => ?_
  obtain ⟨x, hx, hx0⟩ := ((hasEigenvalue_toEuclideanLin_iff A μ).mpr hμ).exists_hasEigenvector
  rw [Module.End.mem_eigenspace_iff, toEuclideanLin_apply] at hx
  have hv : A *ᵥ WithLp.ofLp x = μ • WithLp.ofLp x := by
    simpa using congrArg WithLp.ofLp hx
  have hv0 : WithLp.ofLp x ≠ 0 := fun h => hx0 (by simpa using congrArg (WithLp.toLp 2) h)
  have hpv : 0 < p (WithLp.ofLp x) :=
    lt_of_le_of_ne (apply_nonneg _ _) fun h => hv0 (hp _ h.symm)
  have h := hN A (WithLp.ofLp x)
  rw [hv, map_smul_eq_mul] at h
  have hle : ‖μ‖ ≤ N A := le_of_mul_le_mul_right h hpv
  calc (‖μ‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖μ‖ := (ofReal_norm μ).symm
    _ ≤ ENNReal.ofReal (N A) := ENNReal.ofReal_le_ofReal hle

/-- **Theorem 1.4 for the induced norms**: `ρ(A) ≤ ‖A‖_p` for every definite vector norm `p`
on `n → 𝕜`, the spectral radius being that of `spectrum 𝕜 A`. -/
theorem spectralRadius_le_inducedNorm (hp : ∀ x, p x = 0 → x = 0) (A : Matrix n n 𝕜) :
    spectralRadius 𝕜 A ≤ ENNReal.ofReal (inducedNorm p p A) :=
  spectralRadius_le_of_isConsistent hp (isConsistent_inducedNorm hp) A

/-- **Theorem 1.4 for the induced norms of a real matrix**: `ρ(A) ≤ ‖A‖_p` for every definite
vector norm `p` on `n → ℝ`, the spectral radius being the complex one
(`Matrix.complexSpectralRadius`). Through `Matrix.inducedAlgebraNorm` and
`Matrix.complexSpectralRadius_le_algebraNorm`. -/
theorem complexSpectralRadius_le_inducedNorm {p : Seminorm ℝ (n → ℝ)} (hp : ∀ x, p x = 0 → x = 0)
    (A : Matrix n n ℝ) : complexSpectralRadius A ≤ ENNReal.ofReal (inducedNorm p p A) :=
  complexSpectralRadius_le_algebraNorm (inducedAlgebraNorm p hp) A

/-- **Theorem 1.4 for a real matrix and a real consistent norm**: if `N` is consistent with a
definite vector norm `p` on `n → ℝ`, then `ρ(A) ≤ N A` with the complex spectral radius. The
book's eigenvector proof does not apply (the eigenvector may be complex); instead `N` dominates
the induced norm `‖·‖_p`, which is an algebra norm. -/
theorem complexSpectralRadius_le_of_isConsistent {N : Matrix n n ℝ → ℝ} {p : Seminorm ℝ (n → ℝ)}
    (hp : ∀ x, p x = 0 → x = 0) (hN : IsConsistent N p p) (A : Matrix n n ℝ) :
    complexSpectralRadius A ≤ ENNReal.ofReal (N A) := by
  rcases isEmpty_or_nonempty n with hn | hn
  · have : Subsingleton (Matrix n n ℂ) := ⟨fun _ _ => by ext i; exact isEmptyElim i⟩
    simp [complexSpectralRadius, spectralRadius, spectrum.of_subsingleton]
  have hNA : 0 ≤ N A := by
    have h0 : (Pi.single (Classical.arbitrary n) (1 : ℝ) : n → ℝ) ≠ 0 := by
      intro h
      have := congrFun h (Classical.arbitrary n)
      simp at this
    have hpx : 0 < p (Pi.single (Classical.arbitrary n) 1) :=
      lt_of_le_of_ne (apply_nonneg _ _) fun h => h0 (hp _ h.symm)
    have h := (apply_nonneg p _).trans (hN A (Pi.single (Classical.arbitrary n) 1))
    exact nonneg_of_mul_nonneg_left h hpx
  exact (complexSpectralRadius_le_inducedNorm hp A).trans
    (ENNReal.ofReal_le_ofReal (inducedNorm_le_of_isConsistent hN A hNA))

/-- **Property 1.13 in the induced-norm vocabulary, real case** ([quarteroni2000numerical]):
for every `ε > 0` there is a definite vector norm `p` on `n → ℝ` with `‖A‖_p ≤ ρ(A) + ε`. The
norm is the one of `Matrix.exists_seminorm_forall_mulVec_le`. -/
theorem exists_inducedNorm_le_complexSpectralRadius_add (A : Matrix n n ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : Seminorm ℝ (n → ℝ), (∀ x, p x = 0 → x = 0) ∧
      inducedNorm p p A ≤ (complexSpectralRadius A).toReal + ε := by
  obtain ⟨p, hle, -, hA⟩ := exists_seminorm_forall_mulVec_le A hε
  have hp : ∀ x, p x = 0 → x = 0 := fun x hx =>
    norm_le_zero_iff.1 ((hle x).trans hx.le)
  refine ⟨p, hp, inducedNorm_le A (by positivity) fun x hx => (hA x).trans ?_⟩
  simpa using mul_le_mul_of_nonneg_left hx (by positivity)

/-- **Property 1.13 as the book states it, for a complex matrix** ([quarteroni2000numerical]):
for every `ε > 0` there is a definite vector norm `p` on `n → ℂ` with `‖A‖_p ≤ ρ(A) + ε`. The
norm is the one of `Matrix.exists_seminorm_forall_mulVec_le_complex`. -/
theorem exists_inducedNorm_le_spectralRadius_add (A : Matrix n n ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : Seminorm ℂ (n → ℂ), (∀ x, p x = 0 → x = 0) ∧
      inducedNorm p p A ≤ (spectralRadius ℂ A).toReal + ε := by
  obtain ⟨p, hle, -, hA⟩ := exists_seminorm_forall_mulVec_le_complex A hε
  have hp : ∀ x, p x = 0 → x = 0 := fun x hx =>
    norm_le_zero_iff.1 ((hle x).trans hx.le)
  refine ⟨p, hp, inducedNorm_le A (by positivity) fun x hx => (hA x).trans ?_⟩
  simpa using mul_le_mul_of_nonneg_left hx (by positivity)

/-- **`ρ(A) = inf ‖A‖`** over the norms induced by the definite vector norms on `n → ℝ`,
[quarteroni2000numerical] (1.23). The book takes the infimum over all consistent norms; every
consistent norm is at least `ρ(A)` (`Matrix.complexSpectralRadius_le_of_isConsistent`) and the
induced norms are among them, so the value is the same. -/
theorem complexSpectralRadius_eq_iInf_inducedNorm (A : Matrix n n ℝ) :
    (complexSpectralRadius A).toReal =
      ⨅ p : {p : Seminorm ℝ (n → ℝ) // ∀ x, p x = 0 → x = 0}, inducedNorm p.1 p.1 A := by
  have hne : Nonempty {p : Seminorm ℝ (n → ℝ) // ∀ x, p x = 0 → x = 0} :=
    ⟨⟨normSeminorm ℝ (n → ℝ), fun x hx => norm_eq_zero.1 hx⟩⟩
  have hlow : ∀ p : {p : Seminorm ℝ (n → ℝ) // ∀ x, p x = 0 → x = 0},
      (complexSpectralRadius A).toReal ≤ inducedNorm p.1 p.1 A := fun p =>
    ENNReal.toReal_le_of_le_ofReal (inducedNorm_nonneg A)
      (complexSpectralRadius_le_inducedNorm p.2 A)
  refine le_antisymm (le_ciInf hlow) (le_of_forall_pos_le_add fun ε hε => ?_)
  obtain ⟨p, hp, hle⟩ := exists_inducedNorm_le_complexSpectralRadius_add A hε
  exact (ciInf_le ⟨_, Set.forall_mem_range.2 hlow⟩ ⟨p, hp⟩).trans hle

end SpectralRadius

/-! ### A submultiplicative norm has a consistent vector norm -/

section Submultiplicative

/-- The linear map `x ↦ x yᴴ` (the rank-one matrix `vecMulVec x (star y)`). -/
private def vecMulVecStarₗ (y : n → 𝕜) : (n → 𝕜) →ₗ[𝕜] Matrix n n 𝕜 where
  toFun x := vecMulVec x (star y)
  map_add' x₁ x₂ := add_vecMulVec x₁ x₂ (star y)
  map_smul' c x := by
    ext i j
    simp [vecMulVec_apply, mul_assoc]

/-- **A submultiplicative matrix norm has a consistent vector norm** ([quarteroni2000numerical]
§1.11, after Definition 1.21): for a seminorm `N` on `Matrix n n 𝕜` with `N (A B) ≤ N A N B` and
any `y ≠ 0`, the seminorm `p x = N (x yᴴ)` satisfies `p (A x) ≤ N A p x`; it is definite when `N`
is. -/
theorem exists_isConsistent_of_mul_le (N : Seminorm 𝕜 (Matrix n n 𝕜))
    (hmul : ∀ A B, N (A * B) ≤ N A * N B) {y : n → 𝕜} (hy : y ≠ 0) :
    ∃ p : Seminorm 𝕜 (n → 𝕜), IsConsistent N p p ∧
      ((∀ B, N B = 0 → B = 0) → ∀ x, p x = 0 → x = 0) := by
  refine ⟨N.comp (vecMulVecStarₗ y), fun A x => ?_, fun hN x hx => ?_⟩
  · simp only [Seminorm.comp_apply, vecMulVecStarₗ, LinearMap.coe_mk, AddHom.coe_mk]
    rw [← mul_vecMulVec]
    exact hmul _ _
  · have h0 : vecMulVec x (star y) = 0 := hN _ hx
    rw [vecMulVec_eq_zero] at h0
    rcases h0 with h | h
    · exact h
    · exact absurd (star_eq_zero.1 h) hy

end Submultiplicative

/-! ### The Neumann bounds (1.26) for an induced norm -/

section Neumann

variable [DecidableEq n] {p : Seminorm 𝕜 (n → 𝕜)}

/-- **`1 - A` is invertible when `‖A‖_p < 1`** for an induced norm, [quarteroni2000numerical]
Theorem 1.5 with Remark 1.1. -/
theorem isUnit_one_sub_of_inducedNorm_lt_one (hp : ∀ x, p x = 0 → x = 0) {A : Matrix n n 𝕜}
    (hA : inducedNorm p p A < 1) : IsUnit (1 - A) :=
  isUnit_one_sub_of_algebraNorm_lt_one (inducedAlgebraNorm p hp) hA

/-- **The upper bound of [quarteroni2000numerical] (1.26)**: for an induced norm with
`‖A‖ < 1`, `‖(1 - A)⁻¹‖ ≤ 1 / (1 - ‖A‖)`. -/
theorem inducedNorm_inv_one_sub_le [Nonempty n] (hp : ∀ x, p x = 0 → x = 0) {A : Matrix n n 𝕜}
    (hA : inducedNorm p p A < 1) : inducedNorm p p (1 - A)⁻¹ ≤ 1 / (1 - inducedNorm p p A) := by
  rw [nonsing_inv_eq_ringInverse]
  exact (inducedAlgebraNorm p hp).norm_inverse_one_sub_le_of_lt_one (inducedNorm_one hp) hA

/-- **The lower bound of [quarteroni2000numerical] (1.26)**: for an induced norm with
`‖A‖ < 1`, `1 / (1 + ‖A‖) ≤ ‖(1 - A)⁻¹‖`. -/
theorem one_div_one_add_le_inducedNorm_inv_one_sub [Nonempty n] (hp : ∀ x, p x = 0 → x = 0)
    {A : Matrix n n 𝕜} (hA : inducedNorm p p A < 1) :
    1 / (1 + inducedNorm p p A) ≤ inducedNorm p p (1 - A)⁻¹ := by
  rw [nonsing_inv_eq_ringInverse]
  exact (inducedAlgebraNorm p hp).one_div_one_add_le_norm_inverse_one_sub (inducedNorm_one hp) hA

end Neumann

/-! ### The spectral norm `‖A‖₂` -/

section L2Operator

open scoped Matrix.Norms.L2Operator

variable [DecidableEq n]

/-- `‖A x‖₂ ≤ ‖A‖₂ ‖x‖₂` in the `toEuclideanLin` picture, for a rectangular `A`. -/
theorem norm_toEuclideanLin_apply_le (A : Matrix m n 𝕜) (x : EuclideanSpace 𝕜 n) :
    ‖toEuclideanLin A x‖ ≤ ‖A‖ * ‖x‖ := by
  rw [l2_opNorm_def]
  exact ((toEuclideanLin ≪≫ₗ LinearMap.toContinuousLinearMap) A).le_opNorm x

/-- `‖A‖₂ ≤ M` as soon as `‖A x‖₂ ≤ M ‖x‖₂` for every `x`, for a rectangular `A`. -/
theorem l2_opNorm_le_of_forall_norm_toEuclideanLin_le (A : Matrix m n 𝕜) {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ x : EuclideanSpace 𝕜 n, ‖toEuclideanLin A x‖ ≤ M * ‖x‖) : ‖A‖ ≤ M := by
  rw [l2_opNorm_def]
  exact ContinuousLinearMap.opNorm_le_bound _ hM h

section Unitary

variable [DecidableEq m]

/-- A unitary matrix acts isometrically on `EuclideanSpace`. -/
theorem norm_toEuclideanLin_apply_of_mem_unitaryGroup {U : Matrix n n 𝕜}
    (hU : U ∈ unitaryGroup n 𝕜) (x : EuclideanSpace 𝕜 n) : ‖toEuclideanLin U x‖ = ‖x‖ := by
  rw [toEuclideanLin_apply, norm_toLp_mulVec_of_mem_unitaryGroup hU]

/-- **The spectral norm of a unitary matrix is `1`**, [quarteroni2000numerical] Theorem 1.2,
last clause. -/
theorem l2_opNorm_of_mem_unitaryGroup [Nonempty n] {U : Matrix n n 𝕜}
    (hU : U ∈ unitaryGroup n 𝕜) : ‖U‖ = 1 := by
  refine le_antisymm (l2_opNorm_le_of_forall_norm_toEuclideanLin_le U zero_le_one fun x => by
    rw [norm_toEuclideanLin_apply_of_mem_unitaryGroup hU, one_mul]) ?_
  have h := norm_toEuclideanLin_apply_le U (EuclideanSpace.single (Classical.arbitrary n) (1 : 𝕜))
  rwa [norm_toEuclideanLin_apply_of_mem_unitaryGroup hU, PiLp.norm_single, norm_one,
    mul_one] at h

/-- Multiplying by unitary matrices on both sides does not increase the spectral norm. -/
theorem l2_opNorm_unitary_mul_mul_unitary_le {U : Matrix m m 𝕜} (hU : U ∈ unitaryGroup m 𝕜)
    (A : Matrix m n 𝕜) {V : Matrix n n 𝕜} (hV : V ∈ unitaryGroup n 𝕜) : ‖U * A * V‖ ≤ ‖A‖ := by
  refine l2_opNorm_le_of_forall_norm_toEuclideanLin_le _ (norm_nonneg _) fun x => ?_
  rw [toEuclideanLin_mul_apply, toEuclideanLin_mul_apply,
    norm_toEuclideanLin_apply_of_mem_unitaryGroup hU]
  calc ‖toEuclideanLin A (toEuclideanLin V x)‖ ≤ ‖A‖ * ‖toEuclideanLin V x‖ :=
        norm_toEuclideanLin_apply_le A _
    _ = ‖A‖ * ‖x‖ := by rw [norm_toEuclideanLin_apply_of_mem_unitaryGroup hV]

/-- **Unitary invariance of the spectral norm**: `‖U A V‖₂ = ‖A‖₂` for unitary `U`, `V` and a
rectangular `A`. -/
theorem l2_opNorm_unitary_mul_mul_unitary {U : Matrix m m 𝕜} (hU : U ∈ unitaryGroup m 𝕜)
    (A : Matrix m n 𝕜) {V : Matrix n n 𝕜} (hV : V ∈ unitaryGroup n 𝕜) : ‖U * A * V‖ = ‖A‖ := by
  refine le_antisymm (l2_opNorm_unitary_mul_mul_unitary_le hU A hV) ?_
  have hU' : star U ∈ unitaryGroup m 𝕜 := Unitary.star_mem hU
  have hV' : star V ∈ unitaryGroup n 𝕜 := Unitary.star_mem hV
  have h := l2_opNorm_unitary_mul_mul_unitary_le hU' (U * A * V) hV'
  have hUU : star U * U = 1 := mem_unitaryGroup_iff'.mp hU
  have hVV : V * star V = 1 := mem_unitaryGroup_iff.mp hV
  have heq : star U * (U * A * V) * star V = A := by
    calc star U * (U * A * V) * star V = (star U * U) * A * (V * star V) := by
          simp only [Matrix.mul_assoc]
      _ = A := by rw [hUU, hVV, Matrix.one_mul, Matrix.mul_one]
  rwa [heq] at h

/-- **Unitary invariance of the spectral norm**, one-sided: `‖U A‖₂ = ‖A‖₂` for unitary `U`. -/
theorem l2_opNorm_unitary_mul {U : Matrix m m 𝕜} (hU : U ∈ unitaryGroup m 𝕜) (A : Matrix m n 𝕜) :
    ‖U * A‖ = ‖A‖ := by
  simpa using l2_opNorm_unitary_mul_mul_unitary hU A (unitaryGroup n 𝕜).one_mem

omit [DecidableEq m] in
/-- **Unitary invariance of the spectral norm**, one-sided: `‖A V‖₂ = ‖A‖₂` for unitary `V`. -/
theorem l2_opNorm_mul_unitary (A : Matrix m n 𝕜) {V : Matrix n n 𝕜} (hV : V ∈ unitaryGroup n 𝕜) :
    ‖A * V‖ = ‖A‖ := by
  classical
  simpa using l2_opNorm_unitary_mul_mul_unitary (unitaryGroup m 𝕜).one_mem A hV

/-- **The spectral condition number of a unitary matrix is `1`** ([quarteroni2000numerical]
§3.1.1: "if `A` is orthogonal, `K₂(A) = 1`"). -/
theorem condNumber_l2_of_mem_unitaryGroup [Nonempty n] {U : Matrix n n 𝕜}
    (hU : U ∈ unitaryGroup n 𝕜) : κ U = 1 := by
  rw [NormedRing.condNumber, ← nonsing_inv_eq_ringInverse, l2_opNorm_of_mem_unitaryGroup hU,
    one_mul]
  have hinv : U⁻¹ = star U := inv_eq_left_inv (mem_unitaryGroup_iff'.mp hU)
  rw [hinv]
  exact l2_opNorm_of_mem_unitaryGroup (Unitary.star_mem hU)

/-- **The spectral condition number is unchanged by a unitary factor**: `κ₂(Q R) = κ₂(R)`
([quarteroni2000numerical] §3.11, Exercise 14, `K₂(A) = K₂(R)` for the QR factorization). -/
theorem condNumber_l2_unitary_mul {Q : Matrix n n 𝕜} (hQ : Q ∈ unitaryGroup n 𝕜)
    (R : Matrix n n 𝕜) : κ (Q * R) = κ R := by
  rw [NormedRing.condNumber, NormedRing.condNumber, ← nonsing_inv_eq_ringInverse,
    ← nonsing_inv_eq_ringInverse, Matrix.mul_inv_rev, l2_opNorm_unitary_mul hQ]
  have hinv : Q⁻¹ = star Q := inv_eq_left_inv (mem_unitaryGroup_iff'.mp hQ)
  rw [hinv, l2_opNorm_mul_unitary _ (Unitary.star_mem hQ)]

end Unitary

/-- Every entry is bounded by the spectral norm: `‖A i j‖ ≤ ‖A‖₂`, the lower half of the first
estimate of [quarteroni2000numerical] §1.11 after Theorem 1.2. -/
theorem norm_entry_le_l2_opNorm (A : Matrix m n 𝕜) (i : m) (j : n) :
    ‖A i j‖ ≤ ‖A‖ := by
  have h := norm_toEuclideanLin_apply_le A (EuclideanSpace.single j (1 : 𝕜))
  rw [PiLp.norm_single, norm_one, mul_one] at h
  refine le_trans ?_ h
  have h2 := PiLp.norm_apply_le (toEuclideanLin A (EuclideanSpace.single j (1 : 𝕜))) i
  simpa [toEuclideanLin_apply, mulVec_single_one] using h2

/-- A singular value is at most the spectral norm, for a rectangular `A`. -/
theorem singularValues_le_l2_opNorm (A : Matrix m n 𝕜) (i : n) :
    A.singularValues i ≤ ‖A‖ := by
  have h := norm_toEuclideanLin_apply_le A (A.rightSingularBasis i)
  rwa [norm_toEuclideanLin_rightSingularBasis, A.rightSingularBasis.orthonormal.1 i,
    mul_one] at h

/-- A singular value is at most the spectral norm, written with `lpOpNorm 2`. -/
theorem singularValues_le_lpOpNorm_two (A : Matrix m n 𝕜) (i : n) :
    A.singularValues i ≤ lpOpNorm 2 A := by
  rw [lpOpNorm_two]
  exact singularValues_le_l2_opNorm A i

/-- **Theorem 1.2, (1.21), first equality** ([quarteroni2000numerical]): `‖A‖₂² = ρ(Aᴴ A)` for
`A : Matrix m n ℂ`. In the C⋆-algebra `Matrix n n ℂ`, `ρ(Aᴴ A) = ‖Aᴴ A‖₂` because `Aᴴ A` is
self-adjoint, and `‖Aᴴ A‖₂ = ‖A‖₂²` is the C⋆-identity. -/
theorem l2_opNorm_sq_eq_spectralRadius_conjTranspose_mul_self (A : Matrix m n ℂ) :
    (‖A‖₊ : ℝ≥0∞) ^ 2 = spectralRadius ℂ (Aᴴ * A) := by
  rw [IsSelfAdjoint.spectralRadius_eq_nnnorm (isHermitian_conjTranspose_mul_self A).isSelfAdjoint,
    l2_opNNNorm_conjTranspose_mul_self, ENNReal.coe_mul, sq]

/-- **Theorem 1.2, (1.21), second equality** ([quarteroni2000numerical]): `‖A‖₂² = ρ(A Aᴴ)` for
`A : Matrix m n ℂ`. -/
theorem l2_opNorm_sq_eq_spectralRadius_self_mul_conjTranspose [DecidableEq m]
    (A : Matrix m n ℂ) : (‖A‖₊ : ℝ≥0∞) ^ 2 = spectralRadius ℂ (A * Aᴴ) := by
  have h := l2_opNorm_sq_eq_spectralRadius_conjTranspose_mul_self Aᴴ
  rwa [conjTranspose_conjTranspose, l2_opNNNorm_conjTranspose] at h

/-- Complexification preserves the spectral `nnnorm`. -/
theorem l2_opNNNorm_complexify (A : Matrix n n ℝ) : ‖complexify A‖₊ = ‖A‖₊ :=
  Subtype.ext (l2_opNorm_complexify A)

/-- **Theorem 1.2, (1.21), for a real square matrix**: `‖A‖₂² = ρ(Aᵀ A)`, the spectral radius
being the complex one. -/
theorem l2_opNorm_sq_eq_complexSpectralRadius_conjTranspose_mul_self
    (A : Matrix n n ℝ) : (‖A‖₊ : ℝ≥0∞) ^ 2 = complexSpectralRadius (Aᴴ * A) := by
  rw [complexSpectralRadius, complexify_mul, complexify_conjTranspose,
    ← l2_opNorm_sq_eq_spectralRadius_conjTranspose_mul_self, l2_opNNNorm_complexify]

/-- **(1.22)**: the spectral norm of a Hermitian matrix is its spectral radius,
[quarteroni2000numerical] Theorem 1.2. -/
theorem IsHermitian.l2_opNorm_eq_spectralRadius {A : Matrix n n ℂ}
    (hA : A.IsHermitian) : (‖A‖₊ : ℝ≥0∞) = spectralRadius ℂ A :=
  (IsSelfAdjoint.spectralRadius_eq_nnnorm hA.isSelfAdjoint).symm

/-- **(1.22) for a real symmetric matrix**: `‖A‖₂ = ρ(A)` with the complex spectral radius; the
`toReal` form is `Matrix.l2_opNorm_eq_complexSpectralRadius_of_isHermitian`. -/
theorem IsHermitian.l2_opNNNorm_eq_complexSpectralRadius {A : Matrix n n ℝ}
    (hA : A.IsHermitian) : (‖A‖₊ : ℝ≥0∞) = complexSpectralRadius A := by
  rw [complexSpectralRadius, ← ((isHermitian_complexify_iff A).mpr hA).l2_opNorm_eq_spectralRadius,
    l2_opNNNorm_complexify]

/-- **The spectral norm of a normal matrix is its spectral radius**: Mathlib's
`IsStarNormal.spectralRadius_eq_nnnorm` in the C⋆-algebra `Matrix n n ℂ`. -/
theorem l2_opNorm_eq_spectralRadius_of_isStarNormal (A : Matrix n n ℂ)
    [IsStarNormal A] : (‖A‖₊ : ℝ≥0∞) = spectralRadius ℂ A :=
  (IsStarNormal.spectralRadius_eq_nnnorm A).symm

/-- **A normal matrix has the smallest spectral norm among all the induced `p`-norms**:
`‖A‖₂ ≤ ‖A‖_r` for every `r ≥ 1`, since `‖A‖₂ = ρ(A)` and `ρ(A) ≤ ‖A‖_r` by consistency.
[quarteroni2000numerical] §1.11 states it for `p ≥ 2`; it holds for every `p ≥ 1`. -/
theorem l2_opNorm_le_lpOpNorm_of_isStarNormal (A : Matrix n n ℂ) [IsStarNormal A]
    (r : ℝ≥0∞) [Fact (1 ≤ r)] : lpOpNorm 2 A ≤ lpOpNorm r A := by
  have h := spectralRadius_le_of_isConsistent (lpSeminorm_definite r) (isConsistent_lpOpNorm r) A
  rw [← l2_opNorm_eq_spectralRadius_of_isStarNormal, ← enorm_eq_nnnorm, ← ofReal_norm,
    ENNReal.ofReal_le_ofReal_iff (lpOpNorm_nonneg r A)] at h
  rwa [lpOpNorm_two]

end L2Operator

/-! ### The Frobenius norm -/

section Frobenius

open scoped Matrix.Norms.Frobenius

/-- The Frobenius norm squared is the sum of the squared entries. -/
theorem frobenius_norm_sq_eq_sum_sq (A : Matrix m n 𝕜) : ‖A‖ ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  rw [frobenius_norm_def, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  norm_num

/-- **(1.18)**: `‖A‖_F² = tr(Aᴴ A)`, [quarteroni2000numerical] Example 1.7 (the display there
omits the square root). -/
theorem frobenius_norm_sq_eq_trace (A : Matrix m n 𝕜) :
    ((‖A‖ ^ 2 : ℝ) : 𝕜) = trace (Aᴴ * A) := by
  rw [frobenius_norm_sq_eq_sum_sq, trace, Finset.sum_comm]
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [diag_apply, mul_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [conjTranspose_apply, RCLike.star_def, RCLike.conj_mul]

/-- **Unitary invariance of the Frobenius norm**: `‖U A V‖_F = ‖A‖_F` for unitary `U`, `V`, from
`‖A‖_F² = tr(Aᴴ A)` and the cyclicity of the trace. -/
theorem frobenius_norm_unitary_mul_mul_unitary [DecidableEq m] [DecidableEq n] {U : Matrix m m 𝕜}
    (hU : U ∈ unitaryGroup m 𝕜) (A : Matrix m n 𝕜) {V : Matrix n n 𝕜}
    (hV : V ∈ unitaryGroup n 𝕜) : ‖U * A * V‖ = ‖A‖ := by
  have hUU : Uᴴ * U = 1 := by simpa [star_eq_conjTranspose] using mem_unitaryGroup_iff'.mp hU
  have hVV : V * Vᴴ = 1 := by simpa [star_eq_conjTranspose] using mem_unitaryGroup_iff.mp hV
  have htr : trace ((U * A * V)ᴴ * (U * A * V)) = trace (Aᴴ * A) := by
    calc trace ((U * A * V)ᴴ * (U * A * V)) = trace (Vᴴ * (Aᴴ * (Uᴴ * U) * A) * V) := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = trace (Vᴴ * (Aᴴ * A) * V) := by rw [hUU, Matrix.mul_one]
      _ = trace (V * Vᴴ * (Aᴴ * A)) := trace_mul_cycle _ _ _
      _ = trace (Aᴴ * A) := by rw [hVV, Matrix.one_mul]
  have hsq : ‖U * A * V‖ ^ 2 = ‖A‖ ^ 2 := by
    have h := frobenius_norm_sq_eq_trace (U * A * V)
    rw [htr, ← frobenius_norm_sq_eq_trace] at h
    exact_mod_cast h
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 hsq

/-- **The Frobenius norm is consistent with the Euclidean vector norm**,
`‖A x‖₂ ≤ ‖A‖_F ‖x‖₂`, [quarteroni2000numerical] Example 1.7. -/
theorem frobenius_norm_mulVec_le (A : Matrix m n 𝕜) (x : n → 𝕜) :
    ‖WithLp.toLp 2 (A *ᵥ x)‖ ≤ ‖A‖ * ‖WithLp.toLp 2 x‖ := by
  rw [← frobenius_norm_replicateCol (ι := Fin 1), ← frobenius_norm_replicateCol (ι := Fin 1),
    replicateCol_mulVec]
  exact frobenius_norm_mul A _

/-- `‖I‖_F = √n`, [quarteroni2000numerical] Example 1.7. -/
theorem frobenius_norm_one [DecidableEq n] : ‖(1 : Matrix n n 𝕜)‖ = √(Fintype.card n : ℝ) := by
  have h := frobenius_nnnorm_one (n := n) (α := 𝕜)
  rw [← NNReal.coe_inj, coe_nnnorm, NNReal.coe_mul, Real.coe_sqrt, NNReal.coe_natCast,
    coe_nnnorm, (norm_one : ‖(1 : 𝕜)‖ = 1), mul_one] at h
  exact h

/-- **The spectral norm is at most the Frobenius norm**, `‖A‖₂ ≤ ‖A‖_F`
([quarteroni2000numerical] Exercise 17, `c_{2F} = 1`), written with `lpOpNorm 2` because the two
norms are scoped instances on the same type. -/
theorem l2_opNorm_le_frobenius_norm [DecidableEq n] (A : Matrix m n 𝕜) : lpOpNorm 2 A ≤ ‖A‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => by
    rw [lpCLM_apply]
    simpa using frobenius_norm_mulVec_le A (WithLp.ofLp x)

/-- **Exercise 16 of [quarteroni2000numerical]**: `‖A‖_F² = ∑ σᵢ²`, the Frobenius norm squared
is the sum of the squared singular values, since `tr(Aᴴ A)` is the sum of the eigenvalues of
`Aᴴ A`. -/
theorem frobenius_norm_sq_eq_sum_sq_singularValues [DecidableEq n] (A : Matrix m n 𝕜) :
    ‖A‖ ^ 2 = ∑ i, A.singularValues i ^ 2 := by
  have h := frobenius_norm_sq_eq_trace A
  rw [(isHermitian_conjTranspose_mul_self A).trace_eq_sum_eigenvalues] at h
  simp_rw [sq_singularValues]
  exact_mod_cast h

/-- **`‖A‖_F ≤ √(rank A) ‖A‖₂`** ([quarteroni2000numerical] Exercise 17, `C_{F2} = √n`): each
nonzero singular value is at most `‖A‖₂` and there are `rank A` of them. -/
theorem frobenius_norm_le_sqrt_rank_mul_l2_opNorm [DecidableEq n] (A : Matrix m n 𝕜) :
    ‖A‖ ≤ √(A.rank : ℝ) * lpOpNorm 2 A := by
  have hσ : ∀ i, A.singularValues i ≤ lpOpNorm 2 A := singularValues_le_lpOpNorm_two A
  have hfilter : univ.filter (fun i => A.singularValues i ^ 2 ≠ 0)
      = univ.filter (fun i => A.singularValues i ≠ 0) := by
    ext i
    simp [pow_eq_zero_iff]
  have hsq : ‖A‖ ^ 2 ≤ (A.rank : ℝ) * lpOpNorm 2 A ^ 2 := by
    rw [frobenius_norm_sq_eq_sum_sq_singularValues, ← card_singularValues_ne_zero,
      Fintype.card_subtype, ← Finset.sum_filter_ne_zero, hfilter]
    calc ∑ i ∈ univ.filter (fun i => A.singularValues i ≠ 0), A.singularValues i ^ 2
        ≤ ∑ i ∈ univ.filter (fun i => A.singularValues i ≠ 0), lpOpNorm 2 A ^ 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          exact pow_le_pow_left₀ (A.singularValues_nonneg i) (hσ i) 2
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have hr : 0 ≤ √(A.rank : ℝ) * lpOpNorm 2 A :=
    mul_nonneg (Real.sqrt_nonneg _) (lpOpNorm_nonneg 2 A)
  refine le_of_sq_le_sq ?_ hr
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  exact hsq

/-- **`‖A‖₂ ≤ √(mn) max |aᵢⱼ|`**, the upper half of the first estimate of
[quarteroni2000numerical] §1.11 after Theorem 1.2: if every entry is bounded by `M ≥ 0` then
`‖A‖₂ ≤ √(card m · card n) M` (for a square matrix of order `n`, `‖A‖₂ ≤ n M`), through the
Frobenius norm. -/
theorem l2_opNorm_le_sqrt_card_mul_of_forall_norm_le [DecidableEq n] (A : Matrix m n 𝕜) {M : ℝ}
    (hM : 0 ≤ M) (h : ∀ i j, ‖A i j‖ ≤ M) :
    lpOpNorm 2 A ≤ √((Fintype.card m : ℝ) * Fintype.card n) * M := by
  refine (l2_opNorm_le_frobenius_norm A).trans (le_of_sq_le_sq ?_ (by positivity))
  rw [mul_pow, Real.sq_sqrt (by positivity), frobenius_norm_sq_eq_sum_sq]
  calc ∑ i, ∑ j, ‖A i j‖ ^ 2 ≤ ∑ _i : m, ∑ _j : n, M ^ 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          pow_le_pow_left₀ (norm_nonneg _) (h i j) 2
    _ = (Fintype.card m : ℝ) * Fintype.card n * M ^ 2 := by
        simp [Finset.sum_const, Finset.card_univ, mul_assoc]

end Frobenius

/-! ### `‖A‖₂ ≤ √(‖A‖₁ ‖A‖_∞)` -/

section OneInfty

variable [DecidableEq n]

/-- The rows of `A` are bounded in `ℓ¹` by `‖A‖_∞`. -/
theorem sum_norm_le_lpOpNorm_top (A : Matrix m n 𝕜) (i : m) : ∑ j, ‖A i j‖ ≤ lpOpNorm ⊤ A := by
  open scoped Matrix.Norms.Operator in
  rw [lpOpNorm_top, linfty_opNorm_def]
  have h : (∑ j, ‖A i j‖₊) ≤ univ.sup fun i => ∑ j, ‖A i j‖₊ :=
    Finset.le_sup (f := fun i => ∑ j, ‖A i j‖₊) (mem_univ i)
  have h' := NNReal.coe_le_coe.mpr h
  push_cast at h'
  exact h'

/-- The columns of `A` are bounded in `ℓ¹` by `‖A‖₁`. -/
theorem sum_norm_le_lpOpNorm_one (A : Matrix m n 𝕜) (j : n) : ∑ i, ‖A i j‖ ≤ lpOpNorm 1 A := by
  rw [lpOpNorm_one_eq_sup_sum_norm]
  have h : (∑ i, ‖A i j‖₊) ≤ univ.sup fun j => ∑ i, ‖A i j‖₊ :=
    Finset.le_sup (f := fun j => ∑ i, ‖A i j‖₊) (mem_univ j)
  have h' := NNReal.coe_le_coe.mpr h
  push_cast at h'
  exact h'

/-- **`‖A‖₂² ≤ ‖A‖₁ ‖A‖_∞`**, that is `‖A‖₂ ≤ √(‖A‖₁ ‖A‖_∞)`, [quarteroni2000numerical] §1.11,
for a rectangular `A : Matrix m n 𝕜`. Row by row, the weighted Cauchy–Schwarz inequality
`(∑ⱼ |aᵢⱼ| |xⱼ|)² ≤ (∑ⱼ |aᵢⱼ|) (∑ⱼ |aᵢⱼ| |xⱼ|²)` bounds `‖A x‖₂²` by
`‖A‖_∞ ∑ⱼ |xⱼ|² ∑ᵢ |aᵢⱼ| ≤ ‖A‖_∞ ‖A‖₁ ‖x‖₂²`; no spectral theory is needed, so the statement
holds over every `RCLike 𝕜`. -/
theorem l2_opNorm_sq_le_lpOpNorm_one_mul_linfty_opNorm (A : Matrix m n 𝕜) :
    lpOpNorm 2 A ^ 2 ≤ lpOpNorm 1 A * lpOpNorm ⊤ A := by
  set C := lpOpNorm 1 A with hC
  set R := lpOpNorm ⊤ A with hR
  have hC0 : 0 ≤ C := lpOpNorm_nonneg 1 A
  have hR0 : 0 ≤ R := lpOpNorm_nonneg ⊤ A
  have hCR : 0 ≤ √(C * R) := Real.sqrt_nonneg _
  have key : lpOpNorm 2 A ≤ √(C * R) := by
    refine ContinuousLinearMap.opNorm_le_bound _ hCR fun x => ?_
    rw [lpCLM_apply]
    set v : n → 𝕜 := WithLp.ofLp x with hv
    have hx : ‖x‖ = ‖WithLp.toLp 2 v‖ := rfl
    refine le_of_sq_le_sq ?_ (by positivity)
    rw [mul_pow, Real.sq_sqrt (mul_nonneg hC0 hR0), hx, EuclideanSpace.norm_sq_eq,
      EuclideanSpace.norm_sq_eq]
    -- row by row
    have hrow : ∀ i, ‖(A *ᵥ v) i‖ ^ 2 ≤ R * ∑ j, ‖A i j‖ * ‖v j‖ ^ 2 := by
      intro i
      have h1 : ‖(A *ᵥ v) i‖ ≤ ∑ j, ‖A i j‖ * ‖v j‖ := by
        rw [mulVec_apply_eq_sum]
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => norm_mul_le _ _)
      have h2 : (∑ j, ‖A i j‖ * ‖v j‖) ^ 2 ≤ (∑ j, ‖A i j‖) * ∑ j, ‖A i j‖ * ‖v j‖ ^ 2 := by
        have hcs := Finset.sum_mul_sq_le_sq_mul_sq univ (fun j => √‖A i j‖)
          (fun j => √‖A i j‖ * ‖v j‖)
        have e1 : ∀ j, √‖A i j‖ * (√‖A i j‖ * ‖v j‖) = ‖A i j‖ * ‖v j‖ := fun j => by
          rw [← mul_assoc, Real.mul_self_sqrt (norm_nonneg _)]
        have e2 : ∀ j, (√‖A i j‖) ^ 2 = ‖A i j‖ := fun j => Real.sq_sqrt (norm_nonneg _)
        have e3 : ∀ j, (√‖A i j‖ * ‖v j‖) ^ 2 = ‖A i j‖ * ‖v j‖ ^ 2 := fun j => by
          rw [mul_pow, Real.sq_sqrt (norm_nonneg _)]
        simpa only [e1, e2, e3] using hcs
      calc ‖(A *ᵥ v) i‖ ^ 2 ≤ (∑ j, ‖A i j‖ * ‖v j‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) h1 2
        _ ≤ (∑ j, ‖A i j‖) * ∑ j, ‖A i j‖ * ‖v j‖ ^ 2 := h2
        _ ≤ R * ∑ j, ‖A i j‖ * ‖v j‖ ^ 2 :=
            mul_le_mul_of_nonneg_right (sum_norm_le_lpOpNorm_top A i)
              (Finset.sum_nonneg fun j _ => by positivity)
    calc ∑ i, ‖(A *ᵥ v) i‖ ^ 2 ≤ ∑ i, R * ∑ j, ‖A i j‖ * ‖v j‖ ^ 2 :=
          Finset.sum_le_sum fun i _ => hrow i
      _ = R * ∑ j, (∑ i, ‖A i j‖) * ‖v j‖ ^ 2 := by
          rw [← Finset.mul_sum, Finset.sum_comm]
          simp_rw [Finset.sum_mul]
      _ ≤ R * ∑ j, C * ‖v j‖ ^ 2 := by
          gcongr with j
          exact sum_norm_le_lpOpNorm_one A j
      _ = C * R * ∑ j, ‖v j‖ ^ 2 := by rw [← Finset.mul_sum]; ring
  calc lpOpNorm 2 A ^ 2 ≤ (√(C * R)) ^ 2 := pow_le_pow_left₀ (lpOpNorm_nonneg 2 A) key 2
    _ = C * R := Real.sq_sqrt (mul_nonneg hC0 hR0)

end OneInfty

/-! ### The maximum-row-sum norm and the entrywise order -/

section EntrywiseLE

open scoped Matrix.Norms.Operator

/-- **The `∞`-norm is monotone in the entrywise absolute values**: `|A| ≤ₑ |B| → ‖A‖_∞ ≤ ‖B‖_∞`
for real matrices, the row sums being monotone. This is how an entrywise backward-error bound
becomes a normwise one ([quarteroni2000numerical] (3.25), (3.65), (3.67)). -/
theorem linfty_opNorm_le_of_abs_entrywiseLE {A B : Matrix m n ℝ} (h : A.abs ≤ₑ B.abs) :
    ‖A‖ ≤ ‖B‖ := by
  rw [linfty_opNorm_def, linfty_opNorm_def, NNReal.coe_le_coe]
  refine Finset.sup_mono_fun fun i _ => Finset.sum_le_sum fun j _ => ?_
  rw [← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm, Real.norm_eq_abs, Real.norm_eq_abs]
  exact h i j

/-- The entrywise absolute value does not change the `∞`-norm. -/
theorem linfty_opNorm_abs (A : Matrix m n ℝ) : ‖A.abs‖ = ‖A‖ := by
  rw [linfty_opNorm_def, linfty_opNorm_def]
  simp only [Matrix.abs_apply, Real.nnnorm_abs]

/-- **A scaled entrywise bound gives a scaled norm bound**: `|A| ≤ₑ c |B| → ‖A‖_∞ ≤ c ‖B‖_∞`
for `0 ≤ c`. -/
theorem linfty_opNorm_le_mul_of_abs_entrywiseLE {A B : Matrix m n ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h : A.abs ≤ₑ c • B.abs) : ‖A‖ ≤ c * ‖B‖ := by
  have hle : A.abs.abs ≤ₑ (c • B.abs).abs := fun i j => by
    simp only [Matrix.abs_apply, Matrix.smul_apply, smul_eq_mul, abs_abs, abs_mul,
      abs_of_nonneg hc]
    exact h i j
  calc ‖A‖ = ‖A.abs‖ := (linfty_opNorm_abs A).symm
    _ ≤ ‖c • B.abs‖ := linfty_opNorm_le_of_abs_entrywiseLE hle
    _ = c * ‖B‖ := by rw [norm_smul, Real.norm_of_nonneg hc, linfty_opNorm_abs]

end EntrywiseLE

/-! ### The spectral condition number of a positive definite matrix -/

section PosDef

open scoped Matrix.Norms.L2Operator ComplexOrder

variable [DecidableEq n] [Nonempty n]

/-- **`κ₂(A) = λ_max / λ_min`** for a positive definite `A`, [quarteroni2000numerical] (3.5),
the eigenvalues being `hA.1.eigenvalues` (Mathlib's, in no particular order). -/
theorem PosDef.condNumber_l2_eq_div_eigenvalues {A : Matrix n n 𝕜} (hA : A.PosDef) :
    κ A = (⨆ i, hA.1.eigenvalues i) / ⨅ i, hA.1.eigenvalues i := by
  have hbddA : BddAbove (Set.range hA.1.eigenvalues) := (Set.finite_range _).bddAbove
  have hbddB : BddBelow (Set.range hA.1.eigenvalues) := (Set.finite_range _).bddBelow
  have hpos : ∀ i, 0 < hA.1.eigenvalues i := hA.eigenvalues_pos
  obtain ⟨imax, himax⟩ := exists_eq_ciSup_of_finite (f := hA.1.eigenvalues)
  obtain ⟨imin, himin⟩ := exists_eq_ciInf_of_finite (f := hA.1.eigenvalues)
  have hmin_pos : 0 < ⨅ i, hA.1.eigenvalues i := himin ▸ hpos imin
  -- the eigenvalues of `toEuclideanLin A` are `hA.1.eigenvalues`
  have heig : ∀ μ : 𝕜, Module.End.HasEigenvalue (toEuclideanLin A) μ ↔
      ∃ i, (hA.1.eigenvalues i : 𝕜) = μ := fun μ => hA.1.hasEigenvalue_toEuclideanLin_iff μ
  have hnorm : ‖A‖ = ⨆ i, hA.1.eigenvalues i := by
    refine hA.1.l2_opNorm_eq (fun μ hμ => ?_) ⟨hA.1.eigenvalues imax, (heig _).2 ⟨imax, rfl⟩, ?_⟩
    · obtain ⟨i, rfl⟩ := (heig μ).1 hμ
      rw [RCLike.ofReal_re, abs_of_pos (hpos i)]
      exact le_ciSup hbddA i
    · rw [RCLike.ofReal_re, abs_of_pos (hpos imax), himax]
  have hinv : ‖A⁻¹‖ = (⨅ i, hA.1.eigenvalues i)⁻¹ := by
    refine hA.1.l2_opNorm_inv_eq hmin_pos (fun μ hμ => ?_)
      ⟨hA.1.eigenvalues imin, (heig _).2 ⟨imin, rfl⟩, ?_⟩
    · obtain ⟨i, rfl⟩ := (heig μ).1 hμ
      rw [RCLike.ofReal_re, abs_of_pos (hpos i)]
      exact ciInf_le hbddB i
    · rw [RCLike.ofReal_re, abs_of_pos (hpos imin), himin]
  rw [NormedRing.condNumber, ← nonsing_inv_eq_ringInverse, hnorm, hinv, div_eq_mul_inv]

end PosDef

end Matrix
