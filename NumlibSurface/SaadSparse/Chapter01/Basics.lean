import Mathlib.Analysis.CStarAlgebra.Spectrum
import NumlibSurface.SaadSparse.Chapter01.Section13

/-!
# §1.1–§1.6 Matrices, eigenvalues, types of matrices, norms, subspaces

Sections 1.1–1.6 of Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition,
SIAM, 2003: matrices and their determinants, eigenvalues, the standard classes of matrices,
inner products and vector norms, matrix norms, and subspaces with the range and the kernel.

Almost all of this chapter is Mathlib restated in the book's notation, and the file is
correspondingly thin.  The following carry no declaration of their own, because Mathlib's is the
statement: the definitions of §1.1 and §1.3 (`Matrix.transpose`, `Matrix.conjTranspose`,
`Matrix.IsSymm`, `Matrix.IsHermitian`, `IsStarNormal`, `Matrix.IsDiag`,
`Matrix.BlockTriangular`, `Matrix.unitaryGroup`, and `Matrix.IsTridiagonal`,
`Matrix.IsUpperHessenberg` of `Numlib/LinearAlgebra/Matrix/Hessenberg`); Definition 1.1
(`Module.End.HasEigenvalue`, `spectrum`, reached from a matrix by
`Matrix.hasEigenvalue_toEuclideanLin_iff`); the determinant properties of §1.2; the inner-product
and norm axioms of §1.4 (`InnerProductSpace`, `Norm`); the `p`-norms (1.6) (`PiLp`); and §1.6 in
full (`Submodule.span`, `LinearMap.range`, `LinearMap.ker`, `IsCompl` and
`Module.End.eigenspace`, an eigenspace being invariant by `Module.End.mem_eigenspace_iff`).

Two warnings about the book.  In §1.3 Saad calls a matrix *orthogonal* when `Qᴴ Q` is merely
**diagonal** rather than the identity, which no other source uses; `Matrix.unitaryGroup` is the
standard notion and is what Proposition 1.4 is about.  And the book prints (1.18) as
`ℂⁿ = Ran(A) ⊕ Null(Aᵀ)` in a complex setting, where `Aᴴ` is meant; that is how
`SaadSparse.Ch01.equation_1_18` states it.

The matrix norms of §1.5 use Mathlib's scoped instances, one per norm, opened declaration by
declaration: `Matrix.Norms.Operator` for `‖·‖_∞`, `Matrix.Norms.L2Operator` for `‖·‖₂` and
`Matrix.Norms.Frobenius` for `‖·‖_F`.  The remaining induced norms `‖·‖_p` are the surface's own
`Matrix.lpOpNorm` of §1.13, which is why this file imports that one.
-/

open Matrix Finset Polynomial

open scoped SaadSparse ENNReal NNReal

namespace SaadSparse.Ch01

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

/-! ### §1.1–§1.2 Matrices, determinants and eigenvalues -/

/-- **Saad Proposition 1.2**: a square matrix is nonsingular — its determinant does not
vanish — exactly when it has a two-sided inverse.  The inverse is then `A⁻¹`, by
`Matrix.nonsing_inv_mul` and `Matrix.mul_nonsing_inv`. -/
theorem proposition_1_2 (A : Matrix (Fin n) (Fin n) 𝕜) :
    A.det ≠ 0 ↔ ∃ B, A * B = 1 ∧ B * A = 1 := by
  rw [← isUnit_iff_ne_zero, ← isUnit_iff_isUnit_det, isUnit_iff_exists]

/-- **Saad §1.2**: the trace of a complex matrix is the sum of its eigenvalues and the
determinant is their product, both counted with algebraic multiplicity — that is, over the roots
of the characteristic polynomial. -/
theorem trace_eq_sum_eigenvalues (A : Matrix (Fin n) (Fin n) ℂ) :
    A.trace = A.charpoly.roots.sum ∧ A.det = A.charpoly.roots.prod :=
  ⟨A.trace_eq_sum_roots_charpoly, A.det_eq_prod_roots_charpoly⟩

/-- **Saad Proposition 1.3**: if `μ` is an eigenvalue of `A` then `conj μ` is an eigenvalue of
`Aᴴ`, and an eigenvector `v` of `Aᴴ` for `conj μ` is a *left eigenvector* of `A`,
`star v ᵥ* A = μ • star v`.  The spectra correspond under conjugation because the characteristic
polynomial of `Aᴴ` is the conjugate of that of `A`. -/
theorem proposition_1_3 (A : Matrix (Fin n) (Fin n) ℂ) :
    spectrum ℂ Aᴴ = star '' spectrum ℂ A ∧
      ∀ (μ : ℂ) (v : Fin n → ℂ), Aᴴ *ᵥ v = star μ • v → star v ᵥ* A = μ • star v := by
  have hunit : ∀ M : Matrix (Fin n) (Fin n) ℂ, IsUnit Mᴴ ↔ IsUnit M := by
    intro M
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.isUnit_iff_isUnit_det, Matrix.det_conjTranspose]
    simp [isUnit_iff_ne_zero]
  have halg : ∀ μ : ℂ,
      (algebraMap ℂ (Matrix (Fin n) (Fin n) ℂ) (star μ))ᴴ =
        algebraMap ℂ (Matrix (Fin n) (Fin n) ℂ) μ := by
    intro μ
    ext i j
    by_cases h : i = j <;>
      simp [Matrix.algebraMap_eq_diagonal, h, eq_comm]
  have hspec : ∀ μ : ℂ, μ ∈ spectrum ℂ Aᴴ ↔ star μ ∈ spectrum ℂ A := by
    intro μ
    simp only [spectrum.mem_iff, not_iff_not]
    rw [← hunit (algebraMap ℂ (Matrix (Fin n) (Fin n) ℂ) (star μ) - A),
      Matrix.conjTranspose_sub, halg μ]
  refine ⟨Set.ext fun μ => ?_, fun μ v hv => ?_⟩
  · rw [hspec μ, Set.mem_image]
    exact ⟨fun h => ⟨star μ, h, star_star μ⟩, fun ⟨ν, hν, h⟩ => by
      rw [← h, star_star]; exact hν⟩
  · have h := congrArg star hv
    rwa [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose, star_smul, star_star] at h

/-! ### §1.3 Types of matrices: unitary matrices -/

/-- **Saad Proposition 1.4** and its corollary: a unitary matrix preserves the Euclidean inner
product, `(Q x, Q y) = (x, y)`, and therefore the Euclidean norm, `‖Q x‖₂ = ‖x‖₂`. -/
theorem proposition_1_4 {Q : Matrix (Fin n) (Fin n) 𝕜}
    (hQ : Q ∈ Matrix.unitaryGroup (Fin n) 𝕜) (x y : EuclideanSpace 𝕜 (Fin n)) :
    inner 𝕜 (Q ⬝ y) (Q ⬝ x) = inner 𝕜 y x ∧ ‖Q ⬝ x‖ = ‖x‖ :=
  ⟨Matrix.inner_toLp_mulVec_of_mem_unitaryGroup hQ _ _,
    Matrix.norm_toLp_mulVec_of_mem_unitaryGroup hQ _⟩

/-! ### §1.4 Inner products and vector norms -/

/-- **Saad (1.2)**, the Cauchy–Schwarz inequality: `|(x, y)| ≤ (x, x)^{1/2} (y, y)^{1/2}`, which
is `‖x‖ ‖y‖` by (1.3).  Stated for an arbitrary inner product space, which is the generality of
the book's "arbitrary inner product on a complex vector space". -/
theorem equation_1_2 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (x y : E) :
    ‖(inner 𝕜 y x : 𝕜)‖ ≤ ‖x‖ * ‖y‖ := by
  rw [mul_comm]
  exact norm_inner_le_norm (𝕜 := 𝕜) y x

/-- **Saad (1.4)–(1.5)**: the Euclidean inner product is `(x, y) = yᴴ x`, which is
`SaadSparse.inner_eq_dotProduct_star`, and the adjoint identity `(A x, y) = (x, Aᴴ y)`. -/
theorem equation_1_5 (A : Matrix (Fin n) (Fin n) 𝕜) (x y : EuclideanSpace 𝕜 (Fin n)) :
    inner 𝕜 y (A ⬝ x) = inner 𝕜 (Aᴴ ⬝ y) x := by
  rw [Matrix.toEuclideanLin_conjTranspose]
  exact (LinearMap.adjoint_inner_left _ _ _).symm

/-! ### §1.5 Matrix norms -/

section MatrixNorms

open scoped Matrix.Norms.Operator

/-- The `1`-norm operator norm `‖A‖₁ = max_j ∑_i |a_{ij}|` of **Saad (1.13)**: the largest
absolute column sum.  Mathlib carries only the infinity-operator norm, so this is proved here
from the definition of the operator norm on `PiLp 1`. -/
theorem lpOpNorm_one (A : Matrix (Fin n) (Fin n) 𝕜) :
    Matrix.lpOpNorm 1 A = ↑(univ.sup fun j => ∑ i, ‖A i j‖₊) := by
  classical
  refine le_antisymm ?_ ?_
  · refine ContinuousLinearMap.opNorm_le_bound _
      (univ.sup fun j => ∑ i, ‖A i j‖₊).coe_nonneg fun x => ?_
    rw [Matrix.lpCLM_apply, PiLp.norm_eq_of_L1, PiLp.norm_eq_of_L1]
    calc ∑ i, ‖(A *ᵥ WithLp.ofLp x) i‖
        ≤ ∑ i, ∑ j, ‖A i j‖ * ‖WithLp.ofLp x j‖ := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [Matrix.mulVec_apply_eq_sum]
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
  · have key : ∀ j : Fin n, ((∑ i, ‖A i j‖₊ : ℝ≥0) : ℝ) ≤ ‖Matrix.lpCLM 1 A‖ := by
      intro j
      have hx : ‖(WithLp.toLp 1 (Pi.single j (1 : 𝕜)) : PiLp 1 fun _ : Fin n => 𝕜)‖ = 1 := by
        rw [PiLp.norm_eq_of_L1]
        simp [Pi.single_apply, apply_ite (‖·‖ : 𝕜 → ℝ), Finset.sum_ite_eq']
      have hle := (Matrix.lpCLM 1 A).le_opNorm
        (WithLp.toLp 1 (Pi.single j (1 : 𝕜)) : PiLp 1 fun _ : Fin n => 𝕜)
      rw [hx, mul_one, Matrix.lpCLM_apply, PiLp.norm_eq_of_L1] at hle
      simp only [Matrix.mulVec_single_one, Matrix.col_apply] at hle
      push_cast
      exact hle
    have hsup : (univ.sup fun j => ∑ i, ‖A i j‖₊) ≤ ‖Matrix.lpCLM 1 A‖₊ :=
      Finset.sup_le fun j _ => by rw [← NNReal.coe_le_coe, coe_nnnorm]; exact key j
    rw [Matrix.lpOpNorm, ← coe_nnnorm]
    exact_mod_cast hsup

/-- **Saad (1.13)–(1.14)**: `‖A‖_∞` is the largest absolute row sum and `‖A‖₁` the largest
absolute column sum, so that `‖A‖₁ = ‖Aᵀ‖_∞`. -/
theorem equation_1_14 (A : Matrix (Fin n) (Fin n) 𝕜) :
    ‖A‖ = ↑(univ.sup fun i => ∑ j, ‖A i j‖₊) ∧ Matrix.lpOpNorm 1 A = ‖Aᵀ‖ := by
  refine ⟨Matrix.linfty_opNorm_def A, ?_⟩
  rw [lpOpNorm_one, Matrix.linfty_opNorm_def]
  rfl

end MatrixNorms

section L2

open scoped Matrix.Norms.L2Operator

/-- **Saad (1.15)**: `‖A‖₂² = ρ(Aᴴ A) = ρ(A Aᴴ)`.  The matrices `Aᴴ A` and `A Aᴴ` are
self-adjoint, so their spectral radii are their norms, and the C⋆-identity turns those into
`‖A‖₂²`.  The square roots of the eigenvalues of `Aᴴ A` are the singular values of `A`, so this
says that `‖A‖₂` is the largest singular value. -/
theorem equation_1_15 (A : Matrix (Fin n) (Fin n) ℂ) :
    spectralRadius ℂ (Aᴴ * A) = (‖A‖₊ : ℝ≥0∞) ^ 2 ∧
      spectralRadius ℂ (A * Aᴴ) = (‖A‖₊ : ℝ≥0∞) ^ 2 := by
  have hself : ∀ B : Matrix (Fin n) (Fin n) ℂ, IsSelfAdjoint (Bᴴ * B) := fun B => by
    rw [IsSelfAdjoint, star_eq_conjTranspose, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
  have hmul : ‖A * Aᴴ‖₊ = ‖A‖₊ * ‖A‖₊ := by
    have h := Matrix.l2_opNNNorm_conjTranspose_mul_self Aᴴ
    rwa [Matrix.conjTranspose_conjTranspose, Matrix.l2_opNNNorm_conjTranspose] at h
  refine ⟨?_, ?_⟩
  · rw [IsSelfAdjoint.spectralRadius_eq_nnnorm (hself A),
      Matrix.l2_opNNNorm_conjTranspose_mul_self, sq]
    norm_cast
  · have h := IsSelfAdjoint.spectralRadius_eq_nnnorm (hself Aᴴ)
    rw [Matrix.conjTranspose_conjTranspose] at h
    rw [h, hmul, sq]
    norm_cast

/-- **Saad (1.15)**, the Hermitian case: for a Hermitian matrix the spectral radius *is* the
`2`-norm. -/
theorem spectralRadius_eq_l2_opNNNorm_of_isHermitian {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) : spectralRadius ℂ A = (‖A‖₊ : ℝ≥0∞) :=
  IsSelfAdjoint.spectralRadius_eq_nnnorm hA

end L2

section Frobenius

open scoped Matrix.Norms.Frobenius

/-- **Saad (1.12) and (1.16)**: the Frobenius norm `‖A‖_F = (∑_{i,j} |a_{ij}|²)^{1/2}` satisfies
`‖A‖_F² = tr(Aᴴ A) = tr(A Aᴴ)`.  It is consistent (Problem P-1.5) by
`Matrix.frobenius_norm_mul`. -/
theorem equation_1_16 (A : Matrix (Fin n) (Fin n) 𝕜) :
    ‖A‖ ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ 2 ∧
      ((‖A‖ : 𝕜)) ^ 2 = (Aᴴ * A).trace ∧ ((‖A‖ : 𝕜)) ^ 2 = (A * Aᴴ).trace := by
  have hsq : ‖A‖ ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
    rw [Matrix.frobenius_norm_def, ← Real.rpow_natCast _ 2, ← Real.rpow_mul (by positivity)]
    norm_num
  have hcast : ((‖A‖ : 𝕜)) ^ 2 = ∑ i, ∑ j, ((‖A i j‖ : 𝕜)) ^ 2 := by
    rw [← RCLike.ofReal_pow, hsq]
    push_cast
    rfl
  have key : ∀ B : Matrix (Fin n) (Fin n) 𝕜,
      (Bᴴ * B).trace = ∑ i, ∑ j, ((‖B j i‖ : 𝕜)) ^ 2 := by
    intro B
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      rw [← starRingEnd_apply, RCLike.conj_mul]
  refine ⟨hsq, ?_, ?_⟩
  · rw [key A, hcast]
    exact Finset.sum_comm
  · have h := key Aᴴ
    rw [Matrix.conjTranspose_conjTranspose] at h
    rw [h, hcast]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      rw [Matrix.conjTranspose_apply, norm_star]

end Frobenius

/-- **Saad §1.5**: a consistent matrix norm dominates the spectral radius.  Stated for the
induced `p`-norms `‖·‖_p` of §1.13, which are submultiplicative, absolutely homogeneous and
positive definite — the three hypotheses of
`Matrix.complexSpectralRadius_le_of_norm`, of which only positive definiteness is a real
restriction. -/
theorem spectralRadius_le_lpOpNorm (p : ℝ≥0∞) [Fact (1 ≤ p)] (A : Matrix (Fin n) (Fin n) ℝ) :
    A.complexSpectralRadius ≤ ENNReal.ofReal (Matrix.lpOpNorm p A) := by
  classical
  have hzero : ∀ B : Matrix (Fin n) (Fin n) ℝ, ‖Matrix.lpCLM p B‖₊ = 0 → B = 0 := by
    intro B hB
    have h : Matrix.lpCLM p B = 0 := by simpa using hB
    ext i j
    have h2 : (Matrix.lpCLM p B) (WithLp.toLp p (Pi.single j (1 : ℝ))) = 0 := by simp [h]
    have h3 := congrArg (fun y : PiLp p (fun _ : Fin n => ℝ) =>
      (WithLp.ofLp y : Fin n → ℝ) i) h2
    simpa [Matrix.mulVec_single_one, Matrix.col_apply] using h3
  have hle := Matrix.complexSpectralRadius_le_of_norm (fun B => ‖Matrix.lpCLM p B‖₊) A
    (fun B C => by rw [Matrix.lpCLM_mul]; exact nnnorm_mul_le _ _)
    (fun r B => by rw [Matrix.lpCLM_smul]; exact nnnorm_smul _ _) hzero
  rwa [Matrix.lpOpNorm, ofReal_norm, enorm_eq_nnnorm]

/-- **Saad Example 1.1**: the spectral radius is not a matrix norm.  It vanishes on the nonzero
matrix `!![0, 1; 0, 0]`, and it is not subadditive, since that matrix and its transpose both have
spectral radius `0` while their sum has spectral radius `1`.  This is why every convergence
statement of Chapter 4 is about `ρ` and not about a norm. -/
theorem example_1_1 :
    (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) ≠ 0 ∧
      (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ).complexSpectralRadius = 0 ∧
      (!![0, 0; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ).complexSpectralRadius = 0 ∧
      ((!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) +
        !![0, 0; 1, 0]).complexSpectralRadius = 1 := by
  have hnil : ∀ B : Matrix (Fin 2) (Fin 2) ℝ, B ^ 2 = 0 → B.complexSpectralRadius = 0 := by
    intro B hB
    have h := Matrix.complexSpectralRadius_pow_le B (k := 2) two_ne_zero
    rw [hB, Matrix.complexSpectralRadius_zero, le_zero_iff] at h
    exact pow_eq_zero_iff two_ne_zero |>.mp h
  refine ⟨?_, hnil _ ?_, hnil _ ?_, ?_⟩
  · intro h
    have := congrFun (congrFun h 0) 1
    norm_num at this
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two]
  · have hsum : (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) + !![0, 0; 1, 0] = !![0, 1; 1, 0] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp
    have hc : Matrix.complexify (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) =
        (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) := by
      ext i j; fin_cases i <;> fin_cases j <;> simp
    have hroot : ∀ μ : ℂ, μ ∈ spectrum ℂ (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) ↔
        μ ^ 2 = 1 := by
      intro μ
      rw [Matrix.mem_spectrum_iff_isRoot_charpoly, Polynomial.IsRoot.def,
        Matrix.charpoly_fin_two, Matrix.trace_fin_two_of, Matrix.det_fin_two_of]
      simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
      constructor
      · intro h
        linear_combination h
      · intro h
        linear_combination h
    have hnorm : ∀ μ : ℂ, μ ^ 2 = 1 → ‖μ‖₊ = 1 := by
      intro μ hμ
      have h2 : ‖μ‖ ^ 2 = 1 ^ 2 := by rw [← norm_pow, hμ, norm_one, one_pow]
      have h3 : ‖μ‖ = 1 := (pow_left_inj₀ (norm_nonneg μ) zero_le_one two_ne_zero).mp h2
      exact NNReal.eq (by rw [coe_nnnorm, NNReal.coe_one]; exact h3)
    rw [hsum, Matrix.complexSpectralRadius, hc, spectralRadius]
    refine le_antisymm (iSup₂_le fun μ hμ => ?_) ?_
    · rw [hnorm μ ((hroot μ).mp hμ)]
      simp
    · have h1 : (1 : ℂ) ∈ spectrum ℂ (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) :=
        (hroot 1).mpr (one_pow 2)
      calc (1 : ℝ≥0∞) = ((‖(1 : ℂ)‖₊ : ℝ≥0) : ℝ≥0∞) := by simp
        _ ≤ _ := le_iSup₂ (f := fun μ (_ : μ ∈ _) => ((‖μ‖₊ : ℝ≥0) : ℝ≥0∞)) (1 : ℂ) h1

/-! ### §1.6 Subspaces, range and kernel -/

/-- **Saad (1.18)**: `ℂⁿ` is the direct sum of the range of `A` and the kernel of `Aᴴ`, and
likewise with `A` and `Aᴴ` exchanged.  The kernel of the adjoint is the orthogonal complement of
the range, and a subspace and its orthogonal complement are complementary.  The book prints `Aᵀ`
where `Aᴴ` is meant. -/
theorem equation_1_18 (A : Matrix (Fin n) (Fin n) 𝕜) :
    IsCompl (LinearMap.range (toEuclideanLin A)) (LinearMap.ker (toEuclideanLin Aᴴ)) ∧
      IsCompl (LinearMap.range (toEuclideanLin Aᴴ)) (LinearMap.ker (toEuclideanLin A)) := by
  have key : ∀ B : Matrix (Fin n) (Fin n) 𝕜,
      IsCompl (LinearMap.range (toEuclideanLin B)) (LinearMap.ker (toEuclideanLin Bᴴ)) := by
    intro B
    have h : (LinearMap.range (toEuclideanLin B))ᗮ = LinearMap.ker (toEuclideanLin Bᴴ) := by
      rw [Matrix.toEuclideanLin_conjTranspose]
      exact LinearMap.orthogonal_range _
    exact h ▸ Submodule.isCompl_orthogonal _
  refine ⟨key A, ?_⟩
  have := key Aᴴ
  rwa [Matrix.conjTranspose_conjTranspose] at this

end SaadSparse.Ch01
