import SaadSparse.Ch04.Convergence

/-!
# §4.2.3 Diagonally dominant matrices

Section 4.2.3 of Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition,
SIAM, 2003: Gershgorin's theorem (Theorem 4.6) in its row and column forms, the nonsingularity
of strictly diagonally dominant matrices (Corollary 4.8), and the convergence of the Jacobi and
Gauss–Seidel iterations for such matrices (Theorem 4.9).

Saad's Definition 4.5 as printed uses column sums for all three dominance conditions, while the
proofs of Theorems 4.6 and 4.9 use row sums; both forms are stated here, following the backbone's
`Matrix.IsStrictDiagDominant` (rows) and `Matrix.IsStrictColDiagDominant` (columns).

Left open here (phase 2 of the backbone, `tracker/saadsparse-ch1-4-5.md` §3 item 4):
Theorem 4.7 and the *irreducibly* diagonally dominant halves of Corollary 4.8 and Theorem 4.9,
which need Saad's irreducibility (`Matrix.IsIrreducible (A.map ‖·‖)`) and the path argument along
the adjacency graph; and Gauss–Seidel under strict *column* dominance.
-/

open Matrix Filter Topology Finset Stationary
open scoped SaadSparse

namespace SaadSparse.Ch04

variable {n : ℕ}

/-! ### Theorem 4.6 (Gershgorin) -/

/-- Saad, Theorem 4.6 (rows): every eigenvalue lies in one of the discs
`|λ - a_ii| ≤ ∑_{j ≠ i} |a_ij|`. -/
theorem thm_4_6 (A : Matrix (Fin n) (Fin n) ℂ) {μ : ℂ} (hμ : μ ∈ spectrum ℂ A) :
    ∃ i, ‖μ - A i i‖ ≤ ∑ j ∈ univ.erase i, ‖A i j‖ := by
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (spectrum_subset_iUnion_closedBall A hμ)
  exact ⟨i, by simpa [Metric.mem_closedBall, dist_eq_norm] using hi⟩

/-- Transposing does not change the spectrum. -/
theorem spectrum_transpose (A : Matrix (Fin n) (Fin n) ℂ) : spectrum ℂ Aᵀ = spectrum ℂ A := by
  ext μ
  have hT : (algebraMap ℂ (Matrix (Fin n) (Fin n) ℂ) μ - A)ᵀ
      = algebraMap ℂ (Matrix (Fin n) (Fin n) ℂ) μ - Aᵀ := by
    rw [transpose_sub]
    congr 1
    simp [Algebra.algebraMap_eq_smul_one]
  simp only [spectrum.mem_iff, ← hT, isUnit_iff_isUnit_det, det_transpose]

/-- Saad, Theorem 4.6 (columns): the same statement for the column sums, obtained by
transposing. -/
theorem thm_4_6_col (A : Matrix (Fin n) (Fin n) ℂ) {μ : ℂ} (hμ : μ ∈ spectrum ℂ A) :
    ∃ j, ‖μ - A j j‖ ≤ ∑ i ∈ univ.erase j, ‖A i j‖ := by
  obtain ⟨j, hj⟩ := thm_4_6 Aᵀ (by rwa [spectrum_transpose])
  exact ⟨j, hj⟩

/-! ### Corollary 4.8 -/

/-- Saad, Corollary 4.8 (strict row dominance): a strictly diagonally dominant matrix is
nonsingular. -/
theorem cor_4_8_strict {𝕜 : Type*} [RCLike 𝕜] {A : Matrix (Fin n) (Fin n) 𝕜}
    (h : A.IsStrictDiagDominant) : IsUnit A :=
  h.isUnit

/-- Saad, Corollary 4.8 (strict column dominance). -/
theorem cor_4_8_col {𝕜 : Type*} [RCLike 𝕜] {A : Matrix (Fin n) (Fin n) 𝕜}
    (h : A.IsStrictColDiagDominant) : IsUnit A := by
  have hT : IsUnit Aᵀ := ((IsStrictColDiagDominant.transpose_iff A).mpr h).isUnit
  rwa [isUnit_iff_isUnit_det, det_transpose, ← isUnit_iff_isUnit_det] at hT

/-! ### Complexification of the classical splittings -/

/-- Complexification commutes with the iteration operator `1 - m⁻¹ a` of a splitting. -/
theorem complexify_one_sub_inverse_mul (m A : Matrix (Fin n) (Fin n) ℝ) :
    complexify (1 - Ring.inverse m * A) = 1 - Ring.inverse (complexify m) * complexify A := by
  rw [complexify_sub, complexify_one, complexify_mul, ← nonsing_inv_eq_ringInverse,
    ← nonsing_inv_eq_ringInverse, complexify_inv]

/-- The complexification of a real strictly diagonally dominant matrix is strictly diagonally
dominant. -/
theorem isStrictDiagDominant_complexify {A : Matrix (Fin n) (Fin n) ℝ}
    (h : A.IsStrictDiagDominant) : (complexify A).IsStrictDiagDominant := by
  intro i
  simpa using h i

/-- The diagonal part of the complexification is a unit as soon as that of `A` is. -/
theorem isUnit_diagPart_complexify {A : Matrix (Fin n) (Fin n) ℝ} (h : IsUnit (diagPart A)) :
    IsUnit (diagPart (complexify A)) := by
  rw [← complexify_diagPart, isUnit_complexify_iff]
  exact h

/-- The Jacobi iteration matrix of `complexify A` is the complexification of that of `A`. -/
theorem complexify_jacobi_iterationOperator (A : Matrix (Fin n) (Fin n) ℝ)
    (h : IsUnit (diagPart A)) (h' : IsUnit (diagPart (complexify A))) :
    complexify (jacobiSplitting A h).iterationOperator =
      (jacobiSplitting (complexify A) h').iterationOperator := by
  have e1 : (jacobiSplitting A h).iterationOperator = 1 - Ring.inverse (diagPart A) * A := rfl
  have e2 : (jacobiSplitting (complexify A) h').iterationOperator
      = 1 - Ring.inverse (diagPart (complexify A)) * complexify A := rfl
  rw [e1, e2, ← complexify_diagPart, complexify_one_sub_inverse_mul]

/-- The Gauss–Seidel iteration matrix of `complexify A` is the complexification of that of `A`. -/
theorem complexify_gaussSeidel_iterationOperator (A : Matrix (Fin n) (Fin n) ℝ)
    (h : IsUnit (diagPart A)) (h' : IsUnit (diagPart (complexify A))) :
    complexify (gaussSeidelSplitting A h).iterationOperator =
      (gaussSeidelSplitting (complexify A) h').iterationOperator := by
  have e1 : (gaussSeidelSplitting A h).iterationOperator
      = 1 - Ring.inverse (diagPart A + strictLower A) * A := rfl
  have e2 : (gaussSeidelSplitting (complexify A) h').iterationOperator
      = 1 - Ring.inverse (diagPart (complexify A) + strictLower (complexify A)) * complexify A :=
    rfl
  rw [e1, e2, ← complexify_diagPart, ← complexify_strictLower, ← complexify_add,
    complexify_one_sub_inverse_mul]

/-! ### Theorem 4.9 -/

variable {A : Matrix (Fin n) (Fin n) ℝ}

/-- Saad, Theorem 4.9 (Jacobi, strict row dominance): the Jacobi iteration matrix has spectral
radius `< 1`. -/
theorem jacobi_complexSpectralRadius_lt_one (h : A.IsStrictDiagDominant)
    (hd : IsUnit (diagPart A)) :
    complexSpectralRadius (jacobiSplitting A hd).iterationOperator < 1 := by
  have h' := isUnit_diagPart_complexify hd
  rw [complexSpectralRadius, complexify_jacobi_iterationOperator A hd h']
  exact jacobi_spectralRadius_lt_one _ (isStrictDiagDominant_complexify h) h'

/-- Saad, Theorem 4.9 (Gauss–Seidel, strict row dominance): the Gauss–Seidel iteration matrix has
spectral radius `< 1`. -/
theorem gaussSeidel_complexSpectralRadius_lt_one (h : A.IsStrictDiagDominant)
    (hd : IsUnit (diagPart A)) :
    complexSpectralRadius (gaussSeidelSplitting A hd).iterationOperator < 1 := by
  have h' := isUnit_diagPart_complexify hd
  rw [complexSpectralRadius, complexify_gaussSeidel_iterationOperator A hd h']
  exact gaussSeidel_spectralRadius_lt_one _ (isStrictDiagDominant_complexify h) h'

/-- Saad, Theorem 4.9 (Jacobi): for a strictly diagonally dominant `A` the Jacobi iteration
converges to the solution from every starting vector. -/
theorem thm_4_9_jacobi (h : A.IsStrictDiagDominant) (b x₀ : Fin n → ℝ) :
    Tendsto (fun k => (jacobiStep A b)^[k] x₀) atTop (𝓝 (A⁻¹ *ᵥ b)) := by
  have hd := h.isUnit_diagPart
  rw [jacobiStep_eq hd]
  exact Splitting.tendsto_step _ (jacobi_complexSpectralRadius_lt_one h hd) b x₀

/-- Saad, Theorem 4.9 (Gauss–Seidel): for a strictly diagonally dominant `A` the Gauss–Seidel
iteration converges to the solution from every starting vector. -/
theorem thm_4_9_gs (h : A.IsStrictDiagDominant) (b x₀ : Fin n → ℝ) :
    Tendsto (fun k => (gsStep A b)^[k] x₀) atTop (𝓝 (A⁻¹ *ᵥ b)) := by
  have hd := h.isUnit_diagPart
  rw [gsStep_eq hd]
  exact Splitting.tendsto_step _ (gaussSeidel_complexSpectralRadius_lt_one h hd) b x₀

/-- Saad, Theorem 4.9 (Jacobi, strict column dominance): Kress's variant, from
`Matrix.jacobi_spectralRadius_lt_one_of_col`. -/
theorem thm_4_9_jacobi_col (h : A.IsStrictColDiagDominant) (hd : IsUnit (diagPart A))
    (b x₀ : Fin n → ℝ) : Tendsto (fun k => (jacobiStep A b)^[k] x₀) atTop (𝓝 (A⁻¹ *ᵥ b)) := by
  have h' := isUnit_diagPart_complexify hd
  have hcol : (complexify A).IsStrictColDiagDominant := by
    intro j
    simpa using h j
  have hρ : complexSpectralRadius (jacobiSplitting A hd).iterationOperator < 1 := by
    rw [complexSpectralRadius, complexify_jacobi_iterationOperator A hd h']
    exact jacobi_spectralRadius_lt_one_of_col _ hcol h'
  rw [jacobiStep_eq hd]
  exact Splitting.tendsto_step _ hρ b x₀

end SaadSparse.Ch04
