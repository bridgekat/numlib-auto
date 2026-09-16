import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Numlib.Analysis.Matrix.OperatorNorm
import NumlibSurface.QuarteroniSaccoSaleri.Chapter01.Section10

/-!
# Quarteroni–Sacco–Saleri §1.11: matrix norms

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*
[quarteroni2000numerical], §1.11, over the backbone `Numlib/Analysis/Matrix/OperatorNorm` (the
norm induced by an arbitrary vector norm, the `p`-norms, the spectral norm, the Frobenius norm,
and the spectral-radius bounds), `Numlib/Analysis/Normed/Algebra/SpectralRadius` (the complex
Banach-algebra statements), `Numlib/LinearAlgebra/Matrix/Complexify` (the real matrices, whose
spectral radius `Matrix.complexSpectralRadius` is that of the complexification) and
`Numlib/Analysis/Normed/Module/NormEquivalence`.

## Conventions

A matrix norm (Definition 1.19) is a definite `Seminorm ℝ (Matrix (Fin m) (Fin n) ℝ)`, the same
object as a vector norm of Definition 1.17 on the space of matrices, and carries no declaration
of its own. The norm induced by a vector norm `p` (Theorem 1.1) is `Matrix.inducedNorm p p`; the
`p`-norms are `Matrix.lpOpNorm p`, with `Matrix.lpOpNorm_eq_inducedNorm` connecting the two.
Mathlib's scoped matrix-norm instances — `Matrix.Norms.Operator` (`‖·‖_∞`),
`Matrix.Norms.L2Operator` (`‖·‖₂`), `Matrix.Norms.Frobenius` (`‖·‖_F`) and
`Matrix.Norms.Elementwise` (`‖·‖_Δ = max |aᵢⱼ|`) — are opened declaration by declaration. The
spectral radius of a complex matrix is `spectralRadius ℂ A`, that of a real one
`Matrix.complexSpectralRadius A`, both `ℝ≥0∞`-valued; real bounds `ρ(A) ≤ ‖A‖` read
`≤ ENNReal.ofReal ‖A‖`. The book works in `ℝ^{m×n}` for the definitions and in `ℂ^{n×n}` for the
spectral statements, and the declarations follow it, with the real form beside the complex one
where the book uses both. The book's matrices have positive size (§1.2), which is the `[NeZero n]`
of the statements that need a nonempty index type.

## Contents

* `definition_1_20`, `definition_1_21`, `maxEntryNorm_not_submultiplicative`,
  `exists_consistent_vectorNorm` — consistency, submultiplicativity, the counterexample
  `‖·‖_Δ`, the consistent vector norm `‖x yᴴ‖` of a submultiplicative norm.
* `example_1_7` — the Frobenius norm, (1.18).
* `theorem_1_1`, `lpOpNorm_one_and_top`, `lpOpNorm_one_eq_linfty_opNorm_transpose` — the
  induced norm (1.19)–(1.20) and the `1`- and `∞`-norms.
* `theorem_1_2`, `theorem_1_2_hermitian`, `theorem_1_2_unitary`, `l2_opNorm_bounds`,
  `l2_opNorm_le_lpOpNorm_of_isStarNormal`, `exercise_1_16` — the spectral norm.
* `theorem_1_3` — the induced norm is consistent, `‖I‖ = 1`, submultiplicative.
* `theorem_1_4`, `theorem_1_4_real`, `property_1_13`, `equation_1_23`,
  `spectralRadius_not_subadditive`, `property_1_14` — §1.11.1, norms and the spectral radius.
* `tendsto_iff_tendsto_seminorm`, `theorem_1_5`, `theorem_1_5_series`, `equation_1_26`,
  `remark_1_1` — §1.11.2, sequences and series of matrices.

## Readings and errata

(1.18) prints `‖A‖_F = tr(A Aᴴ)` for `√tr(A Aᴴ)`. After Theorem 1.2 the text says that for
normal `A`, `‖A‖₂ ≤ ‖A‖_p` for `p ≥ 2`; it holds for every `p ≥ 1`. After Property 1.13 the text
calls the spectral radius "a sub-multiplicative seminorm"; it is neither subadditive nor
submultiplicative (`spectralRadius_not_subadditive`). (1.23)'s infimum over all consistent norms
is stated over the induced norms, which gives the same value since every consistent norm is at
least `ρ(A)` (Theorem 1.4). Theorem 1.4 for a *real* matrix and a real vector norm is stated
separately (`theorem_1_4_real`): the eigenvector of the book's proof may be complex, and the
backbone proves the real case through the induced norm instead.
-/

open Filter Finset Matrix Topology WithLp
open scoped ENNReal NNReal

namespace QuarteroniSaccoSaleri.Chapter01

/-! ### Definitions 1.20 and 1.21 -/

/-- **Definition 1.20, (1.16).** A matrix norm `‖·‖` on `ℝ^{m×n}` is *compatible* or
*consistent* with vector norms `‖·‖` on `ℝᵐ` and `ℝⁿ` when `‖A x‖ ≤ ‖A‖ ‖x‖` for all `A` and
`x`; this is the backbone's `Matrix.IsConsistent N q p`, and for square matrices one takes the
same vector norm on both sides. -/
theorem definition_1_20 {m n : ℕ} (N : Matrix (Fin m) (Fin n) ℝ → ℝ) (q : Seminorm ℝ (Fin m → ℝ))
    (p : Seminorm ℝ (Fin n → ℝ)) (N' : Matrix (Fin n) (Fin n) ℝ → ℝ) :
    (IsConsistent N q p ↔ ∀ A x, q (A *ᵥ x) ≤ N A * p x) ∧
      (IsConsistent N' p p ↔ ∀ A x, p (A *ᵥ x) ≤ N' A * p x) :=
  ⟨Iff.rfl, Iff.rfl⟩

/-- **Definition 1.21, (1.17).** A matrix norm, defined on all sizes, is *sub-multiplicative*
when `‖A B‖ ≤ ‖A‖ ‖B‖` for all `A ∈ ℝ^{n×m}`, `B ∈ ℝ^{m×q}`. The `p`-norms are
sub-multiplicative (the remark after Theorem 1.3; backbone `Matrix.lpOpNorm_mul_le`). -/
theorem definition_1_21 {n m q : ℕ} (r : ℝ≥0∞) [Fact (1 ≤ r)] (A : Matrix (Fin n) (Fin m) ℝ)
    (B : Matrix (Fin m) (Fin q) ℝ) :
    lpOpNorm r (A * B) ≤ lpOpNorm r A * lpOpNorm r B :=
  lpOpNorm_mul_le r A B

open scoped Matrix.Norms.Elementwise in
/-- **The norm `‖A‖_Δ = max |aᵢⱼ|` is not sub-multiplicative** (§1.11, the example after
Definition 1.21, from Golub–Van Loan): it is a matrix norm (Mathlib's elementwise supremum
norm), but for `A = B = [[1, 1], [1, 1]]` one has `‖A B‖_Δ = 2 > 1 = ‖A‖_Δ ‖B‖_Δ`. -/
theorem maxEntryNorm_not_submultiplicative :
    ‖(!![1, 1; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ) * !![1, 1; 1, 1]‖ = 2 ∧
      ‖(!![1, 1; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ)‖ * ‖(!![1, 1; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ)‖
        = 1 := by
  have hA : ‖(!![1, 1; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ)‖ = 1 := by
    refine le_antisymm ((norm_le_iff zero_le_one).2 fun i j => ?_) ?_
    · fin_cases i <;> fin_cases j <;> simp
    · simpa using norm_entry_le_entrywise_sup_norm (!![1, 1; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ)
        (i := 0) (j := 0)
  have hmul : (!![1, 1; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ) * !![1, 1; 1, 1] = !![2, 2; 2, 2] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num
  refine ⟨?_, by rw [hA, mul_one]⟩
  rw [hmul]
  refine le_antisymm ((norm_le_iff zero_le_two).2 fun i j => ?_) ?_
  · fin_cases i <;> fin_cases j <;> simp
  · simpa using norm_entry_le_entrywise_sup_norm (!![2, 2; 2, 2] : Matrix (Fin 2) (Fin 2) ℝ)
      (i := 0) (j := 0)

/-- **Every sub-multiplicative matrix norm has a consistent vector norm** (§1.11, after
Definition 1.21): given a sub-multiplicative norm `‖·‖_α` on `ℂ^{n×n}` and any fixed `y ≠ 0`
in `ℂⁿ`, `‖x‖ := ‖x yᴴ‖_α` is a vector norm on `ℂⁿ` consistent with `‖·‖_α`. The seminorm is
`N.comp` of the linear map `x ↦ vecMulVec x (star y)` and consistency is
`A (x yᴴ) = (A x) yᴴ` with sub-multiplicativity (backbone
`Matrix.exists_isConsistent_of_mul_le`, which does not name the norm). -/
theorem exists_consistent_vectorNorm {n : ℕ} (N : Seminorm ℂ (Matrix (Fin n) (Fin n) ℂ))
    (hN : ∀ B, N B = 0 → B = 0) (hmul : ∀ A B, N (A * B) ≤ N A * N B) {y : Fin n → ℂ}
    (hy : y ≠ 0) :
    ∃ p : Seminorm ℂ (Fin n → ℂ), (∀ x, p x = N (vecMulVec x (star y))) ∧
      IsConsistent N p p ∧ ∀ x, p x = 0 → x = 0 := by
  refine ⟨N.comp ((vecMulVecBilin ℂ ℂ).flip (star y)), fun x => rfl, fun A x => ?_,
    fun x hx => ?_⟩
  · simp only [Seminorm.comp_apply, LinearMap.flip_apply, vecMulVecBilin_apply_apply]
    rw [← mul_vecMulVec]
    exact hmul _ _
  · have h0 : vecMulVec x (star y) = 0 := hN _ hx
    rw [vecMulVec_eq_zero] at h0
    exact h0.resolve_right fun h => hy (star_eq_zero.1 h)

/-! ### Example 1.7: the Frobenius norm -/

open scoped Matrix.Norms.Frobenius in
/-- **Example 1.7, (1.18).** The Frobenius norm `‖A‖_F = √(∑ᵢⱼ |aᵢⱼ|²) = √tr(A Aᴴ)` (the
display prints `tr(A Aᴴ)` without the square root) is a matrix norm (Mathlib's scoped
`Matrix.Norms.Frobenius`), compatible with the Euclidean vector norm, `‖A x‖₂ ≤ ‖A‖_F ‖x‖₂`
(backbone `Matrix.frobenius_norm_mulVec_le`), and `‖Iₙ‖_F = √n`. -/
theorem example_1_7 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) :
    ‖A‖ = √(∑ i, ∑ j, ‖A i j‖ ^ 2) ∧ ((‖A‖ ^ 2 : ℝ) : ℂ) = trace (A * Aᴴ) ∧
      ‖toLp 2 (A *ᵥ x)‖ ≤ ‖A‖ * ‖toLp 2 x‖ ∧ ‖(1 : Matrix (Fin n) (Fin n) ℂ)‖ = √n := by
  refine ⟨?_, ?_, frobenius_norm_mulVec_le A x, by simpa using frobenius_norm_one (n := Fin n)⟩
  · rw [← frobenius_norm_sq_eq_sum_sq, Real.sqrt_sq (norm_nonneg _)]
  · have h := frobenius_norm_sq_eq_trace A
    rw [trace_mul_comm] at h
    exact_mod_cast h

/-! ### Theorem 1.1: the induced norm -/

section Induced

variable {m n : ℕ}

/-- **Theorem 1.1, (1.19)–(1.20).** Let `‖·‖` be a vector norm (on `ℝⁿ`, and a second one on
`ℝᵐ` for the rectangular case). The function `‖A‖ = sup_{x ≠ 0} ‖A x‖ / ‖x‖ = sup_{‖x‖ = 1} ‖A x‖`
is a matrix norm, the *induced* or *natural* matrix norm: it is the backbone's
`Matrix.inducedNorm q p A`, the two suprema agree and the second is attained at some `w` with
`‖w‖ = 1`; it is nonnegative, vanishes only at `A = 0`, is absolutely homogeneous and satisfies
the triangle inequality. -/
theorem theorem_1_1 [NeZero n] (q : Seminorm ℝ (Fin m → ℝ)) (p : Seminorm ℝ (Fin n → ℝ))
    (hq : ∀ y, q y = 0 → y = 0) (hp : ∀ x, p x = 0 → x = 0) (A B : Matrix (Fin m) (Fin n) ℝ)
    (α : ℝ) :
    inducedNorm q p A = ⨆ x : {x : Fin n → ℝ // x ≠ 0}, q (A *ᵥ x) / p x ∧
      inducedNorm q p A = ⨆ x : {x : Fin n → ℝ // p x = 1}, q (A *ᵥ x) ∧
      (∃ w, p w = 1 ∧ inducedNorm q p A = q (A *ᵥ w)) ∧
      (0 ≤ inducedNorm q p A ∧ (inducedNorm q p A = 0 ↔ A = 0)) ∧
      inducedNorm q p (α • A) = |α| * inducedNorm q p A ∧
      inducedNorm q p (A + B) ≤ inducedNorm q p A + inducedNorm q p B := by
  obtain ⟨w, hw, hAw⟩ := exists_inducedNorm_eq (q := q) hp A
  refine ⟨inducedNorm_eq_iSup_div hp A, ?_, ⟨w, hw, hAw⟩,
    ⟨inducedNorm_nonneg A, inducedNorm_eq_zero_iff hq hp A⟩, ?_,
    map_add_le_add (inducedSeminorm q p hp) A B⟩
  · have hne : Nonempty {x : Fin n → ℝ // p x = 1} := ⟨⟨w, hw⟩⟩
    have hbdd : BddAbove (Set.range fun x : {x : Fin n → ℝ // p x = 1} => q (A *ᵥ x)) :=
      ⟨inducedNorm q p A, by rintro _ ⟨x, rfl⟩; exact le_inducedNorm hp A x.2.le⟩
    refine le_antisymm ?_ (ciSup_le fun x => le_inducedNorm hp A x.2.le)
    rw [hAw]
    exact le_ciSup hbdd ⟨w, hw⟩
  · rw [← inducedSeminorm_apply (q := q) hp, map_smul_eq_mul, Real.norm_eq_abs,
      inducedSeminorm_apply]

/-- **The `p`-norms and the `1`- and `∞`-norms** (§1.11, after Theorem 1.1). The matrix
`p`-norm `‖A‖_p = sup_{x ≠ 0} ‖A x‖_p / ‖x‖_p` is `Matrix.lpOpNorm p A`, the norm induced by the
vector `p`-norm `Matrix.lpSeminorm p` (backbone `Matrix.lpOpNorm_eq_inducedNorm`); the `1`-norm
is the *column sum norm* `‖A‖₁ = maxⱼ ∑ᵢ |aᵢⱼ|` and the `∞`-norm the *row sum norm*
`‖A‖_∞ = maxᵢ ∑ⱼ |aᵢⱼ|` (backbone `Matrix.lpOpNorm_one_eq_sup_sum_norm`, Mathlib's
`Matrix.linfty_opNorm_def`). -/
theorem lpOpNorm_one_and_top (r : ℝ≥0∞) [Fact (1 ≤ r)] (A : Matrix (Fin m) (Fin n) ℝ) :
    lpOpNorm r A = inducedNorm (lpSeminorm r) (lpSeminorm r) A ∧
      (∀ x : Fin n → ℝ, lpSeminorm r x = ‖toLp r x‖) ∧
      lpOpNorm 1 A = ↑(univ.sup fun j => ∑ i, ‖A i j‖₊) ∧
      lpOpNorm ⊤ A = ↑(univ.sup fun i => ∑ j, ‖A i j‖₊) := by
  refine ⟨lpOpNorm_eq_inducedNorm r A, fun x => rfl, lpOpNorm_one_eq_sup_sum_norm A, ?_⟩
  open scoped Matrix.Norms.Operator in
  rw [lpOpNorm_top, linfty_opNorm_def]

/-- **`‖A‖₁ = ‖Aᵀ‖_∞`**, and `‖A‖₁ = ‖A‖_∞` if `A` is self-adjoint or real symmetric (§1.11,
after the column and row sum norms). Backbone `Matrix.lpOpNorm_one_eq_linfty_opNorm_transpose`
and `Matrix.IsHermitian.lpOpNorm_one_eq_linfty_opNorm`. -/
theorem lpOpNorm_one_eq_linfty_opNorm_transpose (A : Matrix (Fin m) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin n) ℂ) (C : Matrix (Fin n) (Fin n) ℝ) :
    lpOpNorm 1 A = lpOpNorm ⊤ Aᵀ ∧ (B.IsHermitian → lpOpNorm 1 B = lpOpNorm ⊤ B) ∧
      (C.IsSymm → lpOpNorm 1 C = lpOpNorm ⊤ C) := by
  open scoped Matrix.Norms.Operator in
  refine ⟨by rw [lpOpNorm_top, Matrix.lpOpNorm_one_eq_linfty_opNorm_transpose],
    fun hB => by rw [lpOpNorm_top, hB.lpOpNorm_one_eq_linfty_opNorm],
    fun hC => by rw [lpOpNorm_top, (isHermitian_iff_isSymm.2 hC).lpOpNorm_one_eq_linfty_opNorm]⟩

end Induced

/-! ### Theorem 1.2: the spectral norm -/

section Spectral

open scoped Matrix.Norms.L2Operator

variable {m n : ℕ}

/-- **Theorem 1.2, (1.21).** For `A ∈ ℂ^{m×n}`, `‖A‖₂ = √ρ(Aᴴ A) = √ρ(A Aᴴ)`, and for a square
`B` of positive order it is the largest singular value, `‖B‖₂ = σ₁(B) = maxᵢ σᵢ(B)`; for a real
square `C`, `‖C‖₂² = ρ(Cᵀ C)` with the complex spectral radius. The identities `‖A‖₂² = ρ(Aᴴ A)`
are the backbone's `Matrix.l2_opNorm_sq_eq_spectralRadius_conjTranspose_mul_self` and its
companions, stated in `ℝ≥0∞`; the square roots are their real form. -/
theorem theorem_1_2 [NeZero n] (A : Matrix (Fin m) (Fin n) ℂ) (B : Matrix (Fin n) (Fin n) ℂ)
    (C : Matrix (Fin n) (Fin n) ℝ) :
    ((‖A‖₊ : ℝ≥0∞) ^ 2 = spectralRadius ℂ (Aᴴ * A) ∧
        (‖A‖₊ : ℝ≥0∞) ^ 2 = spectralRadius ℂ (A * Aᴴ)) ∧
      (‖A‖ = √(spectralRadius ℂ (Aᴴ * A)).toReal ∧ ‖A‖ = √(spectralRadius ℂ (A * Aᴴ)).toReal) ∧
      ‖B‖ = ⨆ i, B.singularValues i ∧
      (‖C‖₊ : ℝ≥0∞) ^ 2 = complexSpectralRadius (Cᵀ * C) := by
  have h₁ := l2_opNorm_sq_eq_spectralRadius_conjTranspose_mul_self A
  have h₂ := l2_opNorm_sq_eq_spectralRadius_self_mul_conjTranspose A
  have hsq : ∀ ρ : ℝ≥0∞, (‖A‖₊ : ℝ≥0∞) ^ 2 = ρ → ‖A‖ = √ρ.toReal := fun ρ h => by
    rw [← h, ENNReal.toReal_pow, ENNReal.coe_toReal, coe_nnnorm, Real.sqrt_sq (norm_nonneg _)]
  refine ⟨⟨h₁, h₂⟩, ⟨hsq _ h₁, hsq _ h₂⟩, l2_opNorm_eq_iSup_singularValues B, ?_⟩
  rw [← conjTranspose_eq_transpose_of_trivial]
  exact l2_opNorm_sq_eq_complexSpectralRadius_conjTranspose_mul_self C

/-- **Theorem 1.2, (1.22).** If `A` is Hermitian (or real and symmetric) then `‖A‖₂ = ρ(A)`:
backbone `Matrix.IsHermitian.l2_opNorm_eq_spectralRadius` and
`Matrix.IsHermitian.l2_opNNNorm_eq_complexSpectralRadius`, stated in `ℝ≥0∞` and in `ℝ`. -/
theorem theorem_1_2_hermitian {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian)
    {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.IsSymm) :
    ((‖A‖₊ : ℝ≥0∞) = spectralRadius ℂ A ∧ ‖A‖ = (spectralRadius ℂ A).toReal) ∧
      ((‖B‖₊ : ℝ≥0∞) = B.complexSpectralRadius ∧ ‖B‖ = B.complexSpectralRadius.toReal) := by
  have h₁ := hA.l2_opNorm_eq_spectralRadius
  have h₂ := (isHermitian_iff_isSymm.2 hB).l2_opNNNorm_eq_complexSpectralRadius
  exact ⟨⟨h₁, by rw [← h₁, ENNReal.coe_toReal, coe_nnnorm]⟩,
    ⟨h₂, by rw [← h₂, ENNReal.coe_toReal, coe_nnnorm]⟩⟩

/-- **Theorem 1.2, last clause.** If `A` is unitary (or real orthogonal) then `‖A‖₂ = 1`
(backbone `Matrix.l2_opNorm_of_mem_unitaryGroup`). -/
theorem theorem_1_2_unitary [NeZero n] {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A ∈ unitaryGroup (Fin n) ℂ) {Q : Matrix (Fin n) (Fin n) ℝ}
    (hQ : Q ∈ orthogonalGroup (Fin n) ℝ) : ‖A‖ = 1 ∧ ‖Q‖ = 1 :=
  ⟨l2_opNorm_of_mem_unitaryGroup hA, l2_opNorm_of_mem_unitaryGroup hQ⟩

/-- `a ≤ √n b` gives `(1/√n) a ≤ b`, with Lean's `1/√0 = 0` covering the empty case. -/
private theorem one_div_sqrt_mul_le {a b : ℝ} (hb : 0 ≤ b) (h : a ≤ √(n : ℝ) * b) :
    1 / √(n : ℝ) * a ≤ b := by
  rcases eq_or_ne (√(n : ℝ)) 0 with h0 | h0
  · rw [h0, div_zero, zero_mul]; exact hb
  · calc 1 / √(n : ℝ) * a ≤ 1 / √(n : ℝ) * (√(n : ℝ) * b) := by gcongr
      _ = b := by field_simp

/-- **The estimates of `‖A‖₂` after Theorem 1.2**, for a square `A ∈ ℂ^{n×n}` (`‖·‖₂` written
`Matrix.lpOpNorm 2`, `‖·‖₁` and `‖·‖_∞` as `Matrix.lpOpNorm 1`, `Matrix.lpOpNorm ⊤`):
`maxᵢⱼ |aᵢⱼ| ≤ ‖A‖₂ ≤ n maxᵢⱼ |aᵢⱼ|`; `n^{-1/2} ‖A‖_∞ ≤ ‖A‖₂ ≤ n^{1/2} ‖A‖_∞`;
`n^{-1/2} ‖A‖₁ ≤ ‖A‖₂ ≤ n^{1/2} ‖A‖₁`; `‖A‖₂ ≤ √(‖A‖₁ ‖A‖_∞)`. Backbone
`Matrix.norm_entry_le_l2_opNorm`, `Matrix.l2_opNorm_le_sqrt_card_mul_of_forall_norm_le`,
`Matrix.l2_opNorm_le_sqrt_card_mul_linfty_opNorm`, `Matrix.l2_opNorm_le_sqrt_card_mul_lpOpNorm_one`
and `Matrix.l2_opNorm_sq_le_lpOpNorm_one_mul_linfty_opNorm`. -/
theorem l2_opNorm_bounds (A : Matrix (Fin n) (Fin n) ℂ) :
    ((∀ i j, ‖A i j‖ ≤ lpOpNorm 2 A) ∧
        ∀ M : ℝ, 0 ≤ M → (∀ i j, ‖A i j‖ ≤ M) → lpOpNorm 2 A ≤ n * M) ∧
      (1 / √(n : ℝ) * lpOpNorm ⊤ A ≤ lpOpNorm 2 A ∧ lpOpNorm 2 A ≤ √(n : ℝ) * lpOpNorm ⊤ A) ∧
      (1 / √(n : ℝ) * lpOpNorm 1 A ≤ lpOpNorm 2 A ∧ lpOpNorm 2 A ≤ √(n : ℝ) * lpOpNorm 1 A) ∧
      lpOpNorm 2 A ≤ √(lpOpNorm 1 A * lpOpNorm ⊤ A) := by
  have hinf := l2_opNorm_le_sqrt_card_mul_linfty_opNorm A
  have hone := l2_opNorm_le_sqrt_card_mul_lpOpNorm_one A
  simp only [Fintype.card_fin] at hinf hone
  refine ⟨⟨fun i j => ?_, fun M hM h => ?_⟩,
    ⟨one_div_sqrt_mul_le (lpOpNorm_nonneg 2 A) hinf.2, hinf.1⟩,
    ⟨one_div_sqrt_mul_le (lpOpNorm_nonneg 2 A) hone.1, hone.2⟩, ?_⟩
  · rw [lpOpNorm_two]
    exact norm_entry_le_l2_opNorm A i j
  · have h' := l2_opNorm_le_sqrt_card_mul_of_forall_norm_le A hM h
    rwa [Fintype.card_fin, Real.sqrt_mul_self (Nat.cast_nonneg n)] at h'
  · rw [Real.le_sqrt (lpOpNorm_nonneg 2 A)
      (mul_nonneg (lpOpNorm_nonneg 1 A) (lpOpNorm_nonneg ⊤ A))]
    exact l2_opNorm_sq_le_lpOpNorm_one_mul_linfty_opNorm A

/-- **Normal matrices** (§1.11, after the estimates): if `A` is normal then `‖A‖₂ ≤ ‖A‖_p` for
every `p`. The book states it for `p ≥ 2`; it holds for every `p ≥ 1`, since `‖A‖₂ = ρ(A)` for a
normal matrix and `ρ(A) ≤ ‖A‖_p` by consistency (backbone
`Matrix.l2_opNorm_le_lpOpNorm_of_isStarNormal`). -/
theorem l2_opNorm_le_lpOpNorm_of_isStarNormal (A : Matrix (Fin n) (Fin n) ℂ) [IsStarNormal A]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] : lpOpNorm 2 A ≤ lpOpNorm p A :=
  Matrix.l2_opNorm_le_lpOpNorm_of_isStarNormal A p

open scoped Matrix.Norms.Frobenius in
/-- **Exercise 16 (cited by §1.11 for Exercise 17's table).** `‖A‖_F² = ∑ᵢ σᵢ(A)²`, the Frobenius
norm squared is the sum of the squared singular values, and hence
`‖A‖₂ ≤ ‖A‖_F ≤ √(rank A) ‖A‖₂` (backbone `Matrix.frobenius_norm_sq_eq_sum_sq_singularValues`,
`Matrix.l2_opNorm_le_frobenius_norm`, `Matrix.frobenius_norm_le_sqrt_rank_mul_l2_opNorm`). -/
theorem exercise_1_16 (A : Matrix (Fin m) (Fin n) ℝ) :
    ‖A‖ ^ 2 = ∑ i, A.singularValues i ^ 2 ∧ lpOpNorm 2 A ≤ ‖A‖ ∧
      ‖A‖ ≤ √(A.rank : ℝ) * lpOpNorm 2 A :=
  ⟨frobenius_norm_sq_eq_sum_sq_singularValues A, l2_opNorm_le_frobenius_norm A,
    frobenius_norm_le_sqrt_rank_mul_l2_opNorm A⟩

end Spectral

/-! ### Theorem 1.3 -/

/-- **Theorem 1.3.** Let `‖|·|‖` be the matrix norm induced by a vector norm `‖·‖` on `ℝⁿ`.
Then (1) `‖A x‖ ≤ ‖|A|‖ ‖x‖`, that is, `‖|·|‖` is compatible with `‖·‖`; (2) `‖|I|‖ = 1`;
(3) `‖|A B|‖ ≤ ‖|A|‖ ‖|B|‖`, that is, `‖|·|‖` is sub-multiplicative. The remark after the
theorem: sub-multiplicativity by itself gives only `‖|I|‖ ≥ 1`, since `‖|I|‖ ≤ ‖|I|‖²`. Backbone
`Matrix.le_inducedNorm_mul`, `Matrix.isConsistent_inducedNorm`, `Matrix.inducedNorm_one`,
`Matrix.inducedNorm_mul_le`, `Matrix.one_le_of_mul_le`. -/
theorem theorem_1_3 {n : ℕ} [NeZero n] (p : Seminorm ℝ (Fin n → ℝ)) (hp : ∀ x, p x = 0 → x = 0)
    (A B : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) (N : Matrix (Fin n) (Fin n) ℝ → ℝ) :
    (p (A *ᵥ x) ≤ inducedNorm p p A * p x ∧ IsConsistent (inducedNorm p p) p p) ∧
      inducedNorm p p (1 : Matrix (Fin n) (Fin n) ℝ) = 1 ∧
      inducedNorm p p (A * B) ≤ inducedNorm p p A * inducedNorm p p B ∧
      ((∀ A B, N (A * B) ≤ N A * N B) → 0 ≤ N 1 → N 1 ≠ 0 → 1 ≤ N 1) :=
  ⟨⟨le_inducedNorm_mul hp A x, isConsistent_inducedNorm hp⟩, inducedNorm_one hp,
    inducedNorm_mul_le p hp hp A B, fun hmul h0 h1 => one_le_of_mul_le hmul h0 h1⟩

/-! ### §1.11.1 Relation between norms and the spectral radius -/

section SpectralRadius

variable {n : ℕ}

/-- **Theorem 1.4.** Let `‖·‖` be a matrix norm consistent with a vector norm on `ℂⁿ`; then
`ρ(A) ≤ ‖A‖` for every `A ∈ ℂ^{n×n}` (backbone `Matrix.spectralRadius_le_of_isConsistent`, the
book's eigenvector argument). -/
theorem theorem_1_4 {N : Matrix (Fin n) (Fin n) ℂ → ℝ} {p : Seminorm ℂ (Fin n → ℂ)}
    (hp : ∀ x, p x = 0 → x = 0) (hN : IsConsistent N p p) (A : Matrix (Fin n) (Fin n) ℂ) :
    spectralRadius ℂ A ≤ ENNReal.ofReal (N A) :=
  spectralRadius_le_of_isConsistent hp hN A

/-- **Theorem 1.4 for a real matrix** and a matrix norm consistent with a vector norm on `ℝⁿ`:
`ρ(A) ≤ ‖A‖`, the spectral radius being the complex one, in particular `ρ(A) ≤ ‖A‖_p` for the
induced norms of §1.11 and every `p`. The eigenvector of the book's proof may be complex; the
backbone (`Matrix.complexSpectralRadius_le_of_isConsistent`,
`Matrix.complexSpectralRadius_le_inducedNorm`, `Matrix.complexSpectralRadius_le_lpOpNorm`) goes
through the induced norm, which is an algebra norm. -/
theorem theorem_1_4_real {N : Matrix (Fin n) (Fin n) ℝ → ℝ} {p : Seminorm ℝ (Fin n → ℝ)}
    (hp : ∀ x, p x = 0 → x = 0) (hN : IsConsistent N p p) (A : Matrix (Fin n) (Fin n) ℝ)
    (r : ℝ≥0∞) [Fact (1 ≤ r)] :
    A.complexSpectralRadius ≤ ENNReal.ofReal (N A) ∧
      A.complexSpectralRadius ≤ ENNReal.ofReal (inducedNorm p p A) ∧
      A.complexSpectralRadius ≤ ENNReal.ofReal (lpOpNorm r A) :=
  ⟨complexSpectralRadius_le_of_isConsistent hp hN A, complexSpectralRadius_le_inducedNorm hp A,
    complexSpectralRadius_le_lpOpNorm r A⟩

/-- **Property 1.13.** Let `A ∈ ℂ^{n×n}` and `ε > 0`. Then there exists a consistent matrix norm
`‖·‖_{A,ε}` — the norm induced by a vector norm on `ℂⁿ` depending on `A` and `ε` — such that
`‖A‖_{A,ε} ≤ ρ(A) + ε`; and the same for a real `A` with a vector norm on `ℝⁿ` and the complex
spectral radius. Backbone `Matrix.exists_inducedNorm_le_spectralRadius_add` and
`Matrix.exists_inducedNorm_le_complexSpectralRadius_add`, the ε-norm of
`Numlib/LinearAlgebra/Matrix/EpsilonNorm`. -/
theorem property_1_13 (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin n) ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    (∃ p : Seminorm ℂ (Fin n → ℂ), (∀ x, p x = 0 → x = 0) ∧ IsConsistent (inducedNorm p p) p p ∧
        inducedNorm p p A ≤ (spectralRadius ℂ A).toReal + ε) ∧
      ∃ p : Seminorm ℝ (Fin n → ℝ), (∀ x, p x = 0 → x = 0) ∧ IsConsistent (inducedNorm p p) p p ∧
        inducedNorm p p B ≤ B.complexSpectralRadius.toReal + ε := by
  obtain ⟨p, hp, hle⟩ := exists_inducedNorm_le_spectralRadius_add A hε
  obtain ⟨q, hq, hle'⟩ := exists_inducedNorm_le_complexSpectralRadius_add B hε
  exact ⟨⟨p, hp, isConsistent_inducedNorm hp, hle⟩, ⟨q, hq, isConsistent_inducedNorm hq, hle'⟩⟩

/-- **(1.23).** `ρ(A) = inf ‖A‖`, the infimum being taken over the norms induced by the vector
norms on `ℝⁿ` (backbone `Matrix.complexSpectralRadius_eq_iInf_inducedNorm`). The book takes it
over all the consistent norms, which gives the same value: every consistent norm is at least
`ρ(A)` by Theorem 1.4, and the induced norms are among them. -/
theorem equation_1_23 (A : Matrix (Fin n) (Fin n) ℝ) :
    A.complexSpectralRadius.toReal =
      ⨅ p : {p : Seminorm ℝ (Fin n → ℝ) // ∀ x, p x = 0 → x = 0}, inducedNorm p.1 p.1 A :=
  complexSpectralRadius_eq_iInf_inducedNorm A

/-- The spectrum of a `2 × 2` complex matrix, read off its characteristic polynomial
`λ² - tr(M) λ + det M`. -/
private theorem mem_spectrum_fin_two (M : Matrix (Fin 2) (Fin 2) ℂ) (μ : ℂ) :
    μ ∈ spectrum ℂ M ↔ μ ^ 2 - M.trace * μ + M.det = 0 := by
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, Polynomial.IsRoot.def, Matrix.charpoly_fin_two]
  simp

/-- **The spectral radius is not a norm** (§1.11.1, after Property 1.13; book erratum). The text
says "the spectral radius is a sub-multiplicative seminorm, since it is not true that `ρ(A) = 0`
iff `A = 0`". True: `ρ` vanishes on nonzero matrices — the triangular matrix
`N = [[0, 1], [0, 0]]` with null diagonal has `ρ(N) = 0`, and so does `Nᵀ`. False: `ρ` is not
subadditive, `ρ(N + Nᵀ) = 1 > 0 = ρ(N) + ρ(Nᵀ)`, and not sub-multiplicative,
`ρ(N Nᵀ) = 1 > 0 = ρ(N) ρ(Nᵀ)`; it is absolutely homogeneous (`spectralRadius_smul`). -/
theorem spectralRadius_not_subadditive :
    (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) ≠ 0 ∧
      spectralRadius ℂ (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) = 0 ∧
      spectralRadius ℂ (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ)ᵀ = 0 ∧
      spectralRadius ℂ ((!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) + !![0, 1; 0, 0]ᵀ) = 1 ∧
      spectralRadius ℂ ((!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) * !![0, 1; 0, 0]ᵀ) = 1 := by
  have hT : (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ)ᵀ = !![0, 0; 1, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  have hsum : (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) + !![0, 0; 1, 0] = !![0, 1; 1, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  have hprod : (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) * !![0, 0; 1, 0] = !![1, 0; 0, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  -- a matrix whose only eigenvalue is `0` has spectral radius `0`
  have hnil : ∀ M : Matrix (Fin 2) (Fin 2) ℂ, M.trace = 0 → M.det = 0 → spectralRadius ℂ M = 0 := by
    intro M htr hdet
    refine le_antisymm (iSup₂_le fun μ hμ => ?_) zero_le
    rw [mem_spectrum_fin_two, htr, hdet] at hμ
    have : μ = 0 := pow_eq_zero_iff two_ne_zero |>.1 (by linear_combination hμ)
    simp [this]
  -- a matrix whose eigenvalues have modulus at most `1`, one of them being `1`
  have hone : ∀ M : Matrix (Fin 2) (Fin 2) ℂ, (∀ μ, μ ∈ spectrum ℂ M → ‖μ‖₊ ≤ 1) →
      (1 : ℂ) ∈ spectrum ℂ M → spectralRadius ℂ M = 1 := by
    intro M hle h1
    refine le_antisymm (iSup₂_le fun μ hμ => by exact_mod_cast hle μ hμ) ?_
    calc (1 : ℝ≥0∞) = ((‖(1 : ℂ)‖₊ : ℝ≥0) : ℝ≥0∞) := by simp
      _ ≤ _ := le_iSup₂ (f := fun μ (_ : μ ∈ spectrum ℂ M) => ((‖μ‖₊ : ℝ≥0) : ℝ≥0∞)) (1 : ℂ) h1
  have hmod : ∀ μ : ℂ, μ ^ 2 = 1 → ‖μ‖₊ ≤ 1 := fun μ hμ => by
    have h2 : ‖μ‖ ^ 2 = 1 := by rw [← norm_pow, hμ, norm_one]
    have h3 : ‖μ‖ = 1 :=
      (pow_left_inj₀ (norm_nonneg μ) zero_le_one two_ne_zero).mp (by rw [one_pow]; exact h2)
    exact le_of_eq (NNReal.eq (by rw [coe_nnnorm, NNReal.coe_one]; exact h3))
  refine ⟨fun h => by simpa using congrFun (congrFun h 0) 1,
    hnil _ (by simp [trace_fin_two_of]) (by simp [det_fin_two_of]),
    by rw [hT]; exact hnil _ (by simp [trace_fin_two_of]) (by simp [det_fin_two_of]),
    ?_, ?_⟩
  · rw [hT, hsum]
    refine hone _ (fun μ hμ => hmod μ ?_) ((mem_spectrum_fin_two _ _).2 ?_)
    · rw [mem_spectrum_fin_two, trace_fin_two_of, det_fin_two_of] at hμ
      linear_combination hμ
    · simp [trace_fin_two_of, det_fin_two_of]
  · rw [hT, hprod]
    refine hone _ (fun μ hμ => ?_) ((mem_spectrum_fin_two _ _).2 ?_)
    · rw [mem_spectrum_fin_two, trace_fin_two_of, det_fin_two_of] at hμ
      have h : μ * (μ - 1) = 0 := by linear_combination hμ
      rcases mul_eq_zero.1 h with h | h
      · simp [h]
      · rw [sub_eq_zero.1 h]; simp
    · simp [trace_fin_two_of, det_fin_two_of]

open scoped Matrix.Norms.L2Operator in
/-- **Property 1.14 (Gelfand's formula).** Let `A` be a square matrix and `‖·‖` a matrix norm;
then `lim_{m → ∞} ‖Aᵐ‖^{1/m} = ρ(A)`. For a real `A` and *any* matrix norm `N` on `ℝ^{n×n}`
(backbone `Matrix.tendsto_pow_rpow_complexSpectralRadius` for the spectral norm, transported to
`N` by `Seminorm.tendsto_rpow_one_div`), and for a complex `A` in the spectral norm (Mathlib's
`spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius`). The book asks for a consistent
norm; consistency is not needed, since any two norms on `ℝ^{n×n}` differ by a factor whose
`m`-th roots tend to `1`. -/
theorem property_1_14 (N : Seminorm ℝ (Matrix (Fin n) (Fin n) ℝ)) (hN : ∀ M, N M = 0 → M = 0)
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin n) ℂ) :
    Tendsto (fun m : ℕ => N (A ^ m) ^ (1 / m : ℝ)) atTop (𝓝 A.complexSpectralRadius.toReal) ∧
      Tendsto (fun m : ℕ => (‖B ^ m‖₊ : ℝ≥0∞) ^ (1 / m : ℝ)) atTop (𝓝 (spectralRadius ℂ B)) := by
  have _ : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℂ _
  exact ⟨N.tendsto_rpow_one_div hN (tendsto_pow_rpow_complexSpectralRadius A),
    spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius B⟩

end SpectralRadius

/-! ### §1.11.2 Sequences and series of matrices -/

section Sequences

variable {n : ℕ}

open scoped Matrix.Norms.Elementwise in
/-- **Convergence of a sequence of matrices** (§1.11.2). A sequence `A^(k)` in `ℝ^{n×n}` converges
to `A` when `lim_k ‖A^(k) - A‖ = 0`, and "the choice of the norm does not influence the result
since in `ℝ^{n×n}` all norms are equivalent": for every matrix norm `N` this is convergence in
the topology of `ℝ^{n×n}`, hence independent of `N`. A matrix `A` is *convergent* when
`A^k → 0`. -/
theorem tendsto_iff_tendsto_seminorm (N : Seminorm ℝ (Matrix (Fin n) (Fin n) ℝ))
    (hN : ∀ M, N M = 0 → M = 0) (M : ℕ → Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin n) ℝ) :
    Tendsto M atTop (𝓝 B) ↔ Tendsto (fun k => N (M k - B)) atTop (𝓝 0) := by
  rw [Seminorm.tendsto_apply_iff_tendsto_norm N hN fun k => M k - B]
  exact tendsto_iff_norm_sub_tendsto_zero

open scoped Matrix.Norms.L2Operator in
/-- **Theorem 1.5, (1.24).** For a square matrix `A`, `lim_k Aᵏ = 0 ⟺ ρ(A) < 1`: for a real `A`
with the complex spectral radius (backbone `Matrix.tendsto_pow_iff_complexSpectralRadius_lt_one`)
and for a complex `A` of positive order (`spectralRadius_lt_one_iff_tendsto_pow` in the Banach
algebra `ℂ^{n×n}`). -/
theorem theorem_1_5 [NeZero n] (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin n) ℂ) :
    (Tendsto (fun k => A ^ k) atTop (𝓝 0) ↔ A.complexSpectralRadius < 1) ∧
      (Tendsto (fun k => B ^ k) atTop (𝓝 0) ↔ spectralRadius ℂ B < 1) := by
  have _ : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℂ _
  exact ⟨tendsto_pow_iff_complexSpectralRadius_lt_one A,
    (spectralRadius_lt_one_iff_tendsto_pow B).symm⟩

open scoped Matrix.Norms.L2Operator in
/-- **Theorem 1.5, (1.25).** The geometric series `∑ₖ Aᵏ` is convergent iff `ρ(A) < 1`, and then
`I - A` is invertible and `∑ₖ Aᵏ = (I - A)⁻¹`: for a real `A` (backbone
`Matrix.summable_pow_iff_complexSpectralRadius_lt_one`,
`Matrix.hasSum_pow_inv_one_sub_of_complexSpectralRadius_lt_one`) and for a complex `A` of
positive order (`summable_pow_iff_spectralRadius_lt_one`,
`hasSum_pow_inverse_one_sub_of_spectralRadius_lt_one`). -/
theorem theorem_1_5_series [NeZero n] (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin n) ℂ) :
    ((Summable fun k => A ^ k) ↔ A.complexSpectralRadius < 1) ∧
      (A.complexSpectralRadius < 1 → IsUnit (1 - A) ∧ HasSum (fun k => A ^ k) (1 - A)⁻¹) ∧
      ((Summable fun k => B ^ k) ↔ spectralRadius ℂ B < 1) ∧
      (spectralRadius ℂ B < 1 → IsUnit (1 - B) ∧ HasSum (fun k => B ^ k) (1 - B)⁻¹) := by
  have _ : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℂ _
  refine ⟨summable_pow_iff_complexSpectralRadius_lt_one A,
    fun h => ⟨isUnit_one_sub_of_complexSpectralRadius_lt_one h,
      hasSum_pow_inv_one_sub_of_complexSpectralRadius_lt_one h⟩,
    summable_pow_iff_spectralRadius_lt_one B, fun h => ⟨isUnit_one_sub_of_spectralRadius_lt_one h,
      ?_⟩⟩
  rw [nonsing_inv_eq_ringInverse]
  exact hasSum_pow_inverse_one_sub_of_spectralRadius_lt_one h

/-- **(1.26).** If `‖·‖` is an induced matrix norm on `ℝ^{n×n}` with `‖A‖ < 1`, then `I - A` is
invertible and `1 / (1 + ‖A‖) ≤ ‖(I - A)⁻¹‖ ≤ 1 / (1 - ‖A‖)` (backbone
`Matrix.isUnit_one_sub_of_inducedNorm_lt_one`, `Matrix.one_div_one_add_le_inducedNorm_inv_one_sub`,
`Matrix.inducedNorm_inv_one_sub_le`). -/
theorem equation_1_26 [NeZero n] {p : Seminorm ℝ (Fin n → ℝ)} (hp : ∀ x, p x = 0 → x = 0)
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : inducedNorm p p A < 1) :
    IsUnit (1 - A) ∧ 1 / (1 + inducedNorm p p A) ≤ inducedNorm p p (1 - A)⁻¹ ∧
      inducedNorm p p (1 - A)⁻¹ ≤ 1 / (1 - inducedNorm p p A) :=
  ⟨isUnit_one_sub_of_inducedNorm_lt_one hp hA, one_div_one_add_le_inducedNorm_inv_one_sub hp hA,
    inducedNorm_inv_one_sub_le hp hA⟩

/-- **Remark 1.1.** The assumption of (1.26), that there is an induced matrix norm with
`‖A‖ < 1`, is justified by Property 1.13 whenever `A` is convergent, since then `ρ(A) < 1`:
taking `ε = (1 - ρ(A)) / 2` gives a vector norm `p` on `ℝⁿ` with `‖A‖_p < 1`. -/
theorem remark_1_1 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.complexSpectralRadius < 1) :
    ∃ p : Seminorm ℝ (Fin n → ℝ), (∀ x, p x = 0 → x = 0) ∧ inducedNorm p p A < 1 := by
  have hρ : A.complexSpectralRadius.toReal < 1 := by
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_strict_mono ENNReal.one_ne_top hA
  obtain ⟨p, hp, hle⟩ := exists_inducedNorm_le_complexSpectralRadius_add A
    (ε := (1 - A.complexSpectralRadius.toReal) / 2) (by linarith)
  exact ⟨p, hp, by linarith⟩

end Sequences

end QuarteroniSaccoSaleri.Chapter01
