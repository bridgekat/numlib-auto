import Numlib.LinearSolve.Stationary.Splitting
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Algebra.Spectrum

/-!
# Diagonal dominance and convergence of Jacobi / Gauss–Seidel

Strict (row / column) diagonal dominance, invertibility, and convergence of the Jacobi and
Gauss–Seidel iterations (Saad Thm 4.6–4.9, Cor 4.8; Kress Thm 4.2–4.3, Cor 4.4 with the explicit
`‖·‖_∞` contraction constants; Atkinson–Han Ex 5.2.2).
-/

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n]

section Def

variable {𝕜 : Type*} [RCLike 𝕜]

/-- Row strict diagonal dominance: `∑_{j ≠ i} |a_ij| < |a_ii|` for every row `i`. -/
def IsStrictDiagDominant (A : Matrix n n 𝕜) : Prop :=
  ∀ i, ∑ j ∈ Finset.univ.erase i, ‖A i j‖ < ‖A i i‖

/-- Column strict diagonal dominance. -/
def IsStrictColDiagDominant (A : Matrix n n 𝕜) : Prop :=
  ∀ j, ∑ i ∈ Finset.univ.erase j, ‖A i j‖ < ‖A j j‖

theorem IsStrictColDiagDominant.transpose_iff (A : Matrix n n 𝕜) :
    A.transpose.IsStrictDiagDominant ↔ A.IsStrictColDiagDominant := by
  sorry

theorem IsStrictDiagDominant.diag_ne_zero {A : Matrix n n 𝕜} (hA : A.IsStrictDiagDominant) (i : n) :
    A i i ≠ 0 := by
  sorry

theorem IsStrictDiagDominant.isUnit_diagPart {A : Matrix n n 𝕜} (hA : A.IsStrictDiagDominant) :
    IsUnit (diagPart A) := by
  sorry

/-- Saad Thm 4.6 / Kress: strictly diagonally dominant matrices are invertible
(Mathlib: `Matrix.det_ne_zero_of_sum_row_lt_diag`). -/
theorem IsStrictDiagDominant.isUnit {A : Matrix n n 𝕜} (hA : A.IsStrictDiagDominant) :
    IsUnit A := by
  sorry

/-- The Jacobi contraction constant `q_∞ = max_i ∑_{j ≠ i} |a_ij| / |a_ii|` (Kress Thm 4.2). -/
noncomputable def jacobiContraction [Nonempty n] (A : Matrix n n 𝕜) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun i => (∑ j ∈ Finset.univ.erase i, ‖A i j‖) / ‖A i i‖

theorem IsStrictDiagDominant.jacobiContraction_lt_one [Nonempty n] {A : Matrix n n 𝕜}
    (hA : A.IsStrictDiagDominant) : jacobiContraction A < 1 := by
  sorry

/-- Sassenfeld numbers `p_i = (∑_{j < i} |a_ij| p_j + ∑_{j > i} |a_ij|) / |a_ii|` (Kress Thm 4.3),
obtained as the solution of the lower-triangular system `(|D| - |L|) p = |U| 𝟙`. -/
noncomputable def sassenfeld (A : Matrix n n 𝕜) : n → ℝ :=
  (Matrix.of fun i j => if i = j then ‖A i i‖ else if j < i then -‖A i j‖ else 0)⁻¹ *ᵥ
    fun i => ∑ j ∈ Finset.univ.filter (i < ·), ‖A i j‖

/-- The defining recursion of the Sassenfeld numbers. -/
theorem sassenfeld_eq {A : Matrix n n 𝕜} (h : IsUnit (diagPart A)) (i : n) :
    sassenfeld A i = ((∑ j ∈ Finset.univ.filter (· < i), ‖A i j‖ * sassenfeld A j) +
      ∑ j ∈ Finset.univ.filter (i < ·), ‖A i j‖) / ‖A i i‖ := by
  sorry

end Def

section Norm

open scoped Matrix.Norms.Operator

variable {𝕜 : Type*} [RCLike 𝕜]

/-- Kress Thm 4.2: `‖G_J‖_∞ = q_∞` for the Jacobi iteration matrix. -/
theorem linfty_opNorm_jacobi_iterMatrix [Nonempty n] (A : Matrix n n 𝕜) (h : IsUnit (diagPart A)) :
    ‖(jacobiSplitting A h).iterationOperator‖ = jacobiContraction A := by
  sorry

/-- Kress Thm 4.3 (Sassenfeld): `‖G_GS‖_∞ ≤ max_i p_i`. -/
theorem linfty_opNorm_gaussSeidel_iterMatrix_le [Nonempty n] (A : Matrix n n 𝕜)
    (h : IsUnit (diagPart A)) :
    ‖(gaussSeidelSplitting A h).iterationOperator‖ ≤
      Finset.univ.sup' Finset.univ_nonempty (sassenfeld A) := by
  sorry

/-- Kress Cor 4.4: under strict row dominance the Sassenfeld numbers are `≤ q_∞ < 1`. -/
theorem sassenfeld_le_jacobiContraction [Nonempty n] {A : Matrix n n 𝕜}
    (hA : A.IsStrictDiagDominant) (i : n) :
    sassenfeld A i ≤ jacobiContraction A := by
  sorry

end Norm

section Spectral

/-- Saad Thm 4.9 (Jacobi): `ρ(G_J) < 1` for strictly diagonally dominant `A`. -/
theorem jacobi_spectralRadius_lt_one (A : Matrix n n ℂ) (hA : A.IsStrictDiagDominant)
    (h : IsUnit (diagPart A)) : spectralRadius ℂ (jacobiSplitting A h).iterationOperator < 1 := by
  sorry

/-- Saad Thm 4.9 (Gauss–Seidel): `ρ(G_GS) < 1` for strictly diagonally dominant `A`. -/
theorem gaussSeidel_spectralRadius_lt_one (A : Matrix n n ℂ) (hA : A.IsStrictDiagDominant)
    (h : IsUnit (diagPart A)) :
    spectralRadius ℂ (gaussSeidelSplitting A h).iterationOperator < 1 := by
  sorry

/-- Column dominance also suffices for Jacobi (Kress Problem 4.4). -/
theorem jacobi_spectralRadius_lt_one_of_col (A : Matrix n n ℂ) (hA : A.IsStrictColDiagDominant)
    (h : IsUnit (diagPart A)) : spectralRadius ℂ (jacobiSplitting A h).iterationOperator < 1 := by
  sorry

end Spectral

end Matrix
