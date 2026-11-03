import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Numlib.Eigen.MinMax
import Numlib.LinearAlgebra.Matrix.SVD

/-! # Eigenvalues and eigenvectors

Section 2.2 of [conn2000trust] gives spectral and singular value decompositions,
Rayleigh and Gershgorin bounds, and the pseudoinverse formula.
The Gershgorin discs in the prose preceding (2.2.6) form a union.
-/

open Matrix
open scoped Matrix

namespace ConnGouldToint.Chapter02

variable {m n : ℕ}

/-- **(2.2.1)** An eigenpair consists of a nonzero eigenvector and its eigenvalue. -/
def IsEigenpair {𝕜 : Type*} [Field 𝕜] (A : Matrix (Fin n) (Fin n) 𝕜)
    (u : Fin n → 𝕜) (μ : 𝕜) : Prop :=
  u ≠ 0 ∧ A *ᵥ u = μ • u

/-- **(2.2.2)** A real symmetric matrix has an orthogonal eigendecomposition
with its eigenvalues on the diagonal. -/
theorem spectral_decomposition_2_2_2 {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.IsHermitian) :
    ∃ U ∈ Matrix.unitaryGroup (Fin n) ℝ, H = U * diagonal hH.eigenvalues * Uᵀ := by
  refine ⟨hH.eigenvectorUnitary, hH.eigenvectorUnitary.property, ?_⟩
  simpa [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
    using hH.spectral_theorem

/-- **(2.2.3)** The absolute value of a real symmetric matrix is obtained by replacing
the eigenvalues in its spectral decomposition by their absolute values. -/
noncomputable def symmetricAbs {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.IsHermitian) :
    Matrix (Fin n) (Fin n) ℝ :=
  (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) *
    diagonal (fun i => |hH.eigenvalues i|) * (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)ᵀ

/-- **(2.2.4)** Every real rectangular matrix has an SVD with orthogonal factors
and a nonnegative, decreasing diagonal. -/
theorem singular_value_decomposition_2_2_4 (A : Matrix (Fin m) (Fin n) ℝ) :
    ∃ U ∈ Matrix.unitaryGroup (Fin m) ℝ, ∃ V ∈ Matrix.unitaryGroup (Fin n) ℝ,
      ∃ σ : ℕ → ℝ, Antitone σ ∧ (∀ i, 0 ≤ σ i) ∧
        A = U * (Matrix.rectDiagonal σ : Matrix (Fin m) (Fin n) ℝ) * Vᵀ := by
  obtain ⟨U, σ, V, h⟩ := A.exists_isSVD
  exact ⟨U, h.mem_unitaryGroup_left, V, h.mem_unitaryGroup_right, σ, h.antitone, h.nonneg,
    by simpa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using h.eq_mul_mul_star⟩

/-- **(2.2.5)** Every Rayleigh quotient of a nonzero vector lies between the
least and greatest eigenvalues of a real symmetric matrix. -/
theorem rayleigh_bounds_2_2_5 {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hH : H.IsHermitian) {p : EuclideanSpace ℝ (Fin (n + 1))} (hp : p ≠ 0) :
    (⨅ i, hH.eigenvalues i) ≤ H.toEuclideanLin.rayleighQuotient p ∧
      H.toEuclideanLin.rayleighQuotient p ≤ ⨆ i, hH.eigenvalues i := by
  let hT := isSymmetric_toEuclideanLin_iff.mpr hH
  have hr : Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) =
      Fintype.card (Fin (n + 1)) := finrank_euclideanSpace
  have he (i : Fin (Fintype.card (Fin (n + 1)))) :
      hT.eigenvalues hr i = hH.eigenvalues (Fintype.equivOfCardEq (Fintype.card_fin _) i) := by
    simp [Matrix.IsHermitian.eigenvalues, Matrix.IsHermitian.eigenvalues₀]
  refine ⟨hT.le_rayleighQuotient_of_forall hr (fun i => ?_) hp,
    hT.rayleighQuotient_le_of_forall hr (fun i => ?_) hp⟩
  · rw [he]
    exact ciInf_le (Set.finite_range _).bddBelow _
  · rw [he]
    exact le_ciSup (Set.finite_range _).bddAbove _

/-- **Gershgorin's disc theorem.** Every complex eigenvalue belongs to at least one
of the row discs. This is the union of the discs in the prose preceding (2.2.6). -/
theorem gershgorin_union {A : Matrix (Fin n) (Fin n) ℂ} {u : Fin n → ℂ} {μ : ℂ}
    (h : IsEigenpair A u μ) :
    ∃ i, μ ∈ Metric.closedBall (A i i) (∑ j ∈ Finset.univ.erase i, ‖A i j‖) :=
  eigenvalue_mem_ball (Module.End.hasEigenvalue_of_hasEigenvector
    ⟨Module.End.mem_eigenspace_iff.2 (by simpa [toLin'_apply] using h.2), h.1⟩)

/-- A diagonal matrix with diagonal entries zero and one has an eigenvalue
outside one of its row discs. -/
theorem gershgorin_intersection_counterexample :
    ∃ (A : Matrix (Fin 2) (Fin 2) ℂ) (u : Fin 2 → ℂ) (μ : ℂ),
      IsEigenpair A u μ ∧
        ¬ ∀ i, μ ∈ Metric.closedBall (A i i) (∑ j ∈ Finset.univ.erase i, ‖A i j‖) := by
  let d : Fin 2 → ℂ := ![0, 1]
  refine ⟨diagonal d, ![1, 0], 0, ⟨?_, ?_⟩, ?_⟩
  · intro h
    have h0 := congrFun h (0 : Fin 2)
    simp at h0
  · funext i
    rw [mulVec_diagonal]
    fin_cases i <;> simp [d]
  · intro h
    have h1 := h (1 : Fin 2)
    have hr : (∑ j ∈ Finset.univ.erase (1 : Fin 2),
        ‖(diagonal d) (1 : Fin 2) j‖) = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      simp [Matrix.diagonal_apply_ne d (Finset.mem_erase.1 hj).1.symm]
    rw [hr, Metric.closedBall_zero, Set.mem_singleton_iff] at h1
    simp [d] at h1

/-- **(2.2.6)** The extrema of the diagonal-centered Gershgorin intervals bound
the leftmost and rightmost eigenvalues of a real symmetric matrix. -/
theorem gershgorin_bounds_2_2_6 {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hH : H.IsHermitian) :
    let r (i : Fin (n + 1)) := ∑ j ∈ Finset.univ.erase i, |H i j|
    (⨅ i, H i i - r i) ≤ (⨅ i, hH.eigenvalues i) ∧
      (⨅ i, hH.eigenvalues i) ≤ (⨆ i, hH.eigenvalues i) ∧
      (⨆ i, hH.eigenvalues i) ≤ ⨆ i, H i i + r i := by
  dsimp only
  have hg (j : Fin (n + 1)) : ∃ i, |hH.eigenvalues j - H i i| ≤
      ∑ k ∈ Finset.univ.erase i, |H i k| := by
    have hne : ⇑(hH.eigenvectorBasis j) ≠ 0 := by
      intro h
      have hz : hH.eigenvectorBasis j = 0 := by
        ext i
        exact congrFun h i
      have hnorm := hH.eigenvectorBasis.norm_eq_one j
      simp [hz] at hnorm
    obtain ⟨i, hi⟩ := eigenvalue_mem_ball (Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.2 (by
        simpa [toLin'_apply] using hH.mulVec_eigenvectorBasis j), hne⟩)
    exact ⟨i, by simpa [Metric.mem_closedBall, Real.dist_eq, Real.norm_eq_abs] using hi⟩
  refine ⟨le_ciInf fun j => ?_, ?_, ciSup_le fun j => ?_⟩
  · obtain ⟨i, hi⟩ := hg j
    exact (ciInf_le (Set.finite_range _).bddBelow i).trans (by linarith [(abs_le.1 hi).1])
  · exact (ciInf_le (Set.finite_range _).bddBelow 0).trans
      (le_ciSup (Set.finite_range _).bddAbove 0)
  · obtain ⟨i, hi⟩ := hg j
    exact (show hH.eigenvalues j ≤ _ from by linarith [(abs_le.1 hi).2]).trans
      (le_ciSup (Set.finite_range _).bddAbove i)

/-- **(2.2.7)** A generalized eigenpair of a matrix pencil solves `Au = μ Bu`
with a nonzero vector `u`. -/
def IsGeneralizedEigenpair {𝕜 : Type*} [Field 𝕜] (A B : Matrix (Fin n) (Fin n) 𝕜)
    (u : Fin n → 𝕜) (μ : 𝕜) : Prop :=
  u ≠ 0 ∧ A *ᵥ u = μ • (B *ᵥ u)

/-- **(2.2.8)** The reciprocal-diagonal SVD formula gives a solution to every
consistent linear system. Lean's inverse of zero is zero, as required for `Σ⁺`. -/
theorem svd_solution_2_2_8 {A : Matrix (Fin m) (Fin n) ℝ} {U V σ}
    (h : Matrix.IsSVD A U σ V) {b : Fin m → ℝ} (hb : ∃ x, A *ᵥ x = b) :
    A *ᵥ ((V * (Matrix.rectDiagonal fun i => (σ i)⁻¹ : Matrix (Fin n) (Fin m) ℝ) * Uᵀ) *ᵥ b) =
      b := by
  have hp : A.pinv = V * (Matrix.rectDiagonal fun i => (σ i)⁻¹ : Matrix (Fin n) (Fin m) ℝ) * Uᵀ :=
    by simpa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using h.pinv_eq
  obtain ⟨x, rfl⟩ := hb
  rw [← hp, mulVec_mulVec, mulVec_mulVec, A.mul_pinv_mul_self]

/-- **(2.2.8)** The SVD formula minimizes the residual even for an inconsistent
system and has minimum norm among the least-squares solutions, characterized by
the normal equations. -/
theorem svd_leastSquares_2_2_8 {A : Matrix (Fin m) (Fin n) ℝ} {U V σ}
    (h : Matrix.IsSVD A U σ V) (b : EuclideanSpace ℝ (Fin m)) :
    let x := Matrix.toEuclideanLin
      (V * (Matrix.rectDiagonal fun i => (σ i)⁻¹ : Matrix (Fin n) (Fin m) ℝ) * Uᵀ) b
    (∀ y, ‖A.toEuclideanLin x - b‖ ≤ ‖A.toEuclideanLin y - b‖) ∧
      (∀ y, (Aᵀ * A).toEuclideanLin y = Aᵀ.toEuclideanLin b → ‖x‖ ≤ ‖y‖) := by
  have hp : A.pinv = V * (Matrix.rectDiagonal fun i => (σ i)⁻¹ : Matrix (Fin n) (Fin m) ℝ) * Uᵀ :=
    by simpa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using h.pinv_eq
  dsimp only
  rw [← hp]
  refine ⟨A.norm_toEuclideanLin_pinv_sub_le b, fun y hy => ?_⟩
  exact A.norm_pinv_le_of_normalEquations b (by
    simpa only [conjTranspose_eq_transpose_of_trivial] using hy)

end ConnGouldToint.Chapter02
