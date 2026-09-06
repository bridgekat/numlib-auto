import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.LinearAlgebra.Matrix.IsDiag
import Numlib.Eigen.MinMax
import Numlib.Eigen.Normal
import NumlibSurface.SaadSparse.Common

/-!
# Saad §1.9: normal and Hermitian matrices

Surface file for Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM,
2003, §1.9: normal matrices (§1.9.1) with the field of values and the numerical radius, and
Hermitian matrices (§1.9.2) with the min–max theorems.

The normal theory is the backbone's `Numlib/Eigen/Normal`: Lemma 1.15 is the pair
`LinearMap.IsStarNormal.eigenspace_adjoint` and
`LinearMap.isStarNormal_of_adjoint_apply_eq_smul`, and Theorem 1.14 is
`Matrix.IsStarNormal.spectral_theorem`, whose orthonormal eigenbasis
(`LinearMap.IsStarNormal.eigenvectorBasis`) is what `SaadSparse.Chapter01.normalEigenBasis` names
here. The Hermitian theory is Mathlib's `Matrix.IsHermitian.spectral_theorem` together with the
backbone's Courant–Fischer of `Numlib/Eigen/MinMax`.

Two conventions.  Saad's inner product `(x, y)` is Mathlib's `inner 𝕜 y x`, so the Rayleigh
quotient (1.33) `μ(x) = (A x, x)/(x, x)` is `SaadSparse.Chapter01.rayleigh`, `inner ℂ x (A ⬝ x)`
over `inner ℂ x x`; the backbone's `LinearMap.rayleighQuotient` is its real part, which is all
that is needed for a Hermitian matrix.  And the book indexes the eigenvalues of a Hermitian
matrix in decreasing order `λ₁ ≥ ⋯ ≥ λ_n`, which is
`SaadSparse.Chapter01.eigenvaluesDesc` — Mathlib's `Matrix.IsHermitian.eigenvalues` is in no
particular order, while the backbone's `LinearMap.IsSymmetric.eigenvalues` is already
decreasing.

**Not formalized: the convexity half of Proposition 1.18**, the Toeplitz–Hausdorff theorem that
the field of values of an arbitrary matrix is convex.  Saad states it without proof; the standard
argument reduces to computing that the field of values of a `2 × 2` matrix is a filled ellipse,
a self-contained development with no other consumer in this library.  What is proved here is the
containment `spectrum ℂ A ⊆ fieldOfValues A`, its conditional consequence given convexity, and —
unconditionally, since there (1.34) suffices — the equality for normal matrices (Theorem 1.17).
**Also not formalized: the power inequality (1.36)**, `ν(Aᵏ) ≤ ν(A)ᵏ`, which the book attributes
to the literature and which is Berger's inequality.
-/

open Matrix Finset Module.End Polynomial

open scoped SaadSparse ComplexConjugate ENNReal

namespace SaadSparse.Chapter01

variable {n : ℕ}

/-! ### §1.9.1 Normal matrices -/

section Lemma113

variable {A : Matrix (Fin n) (Fin n) ℂ}

private theorem blockTriangular_smul {a : ℂ} {M : Matrix (Fin n) (Fin n) ℂ}
    (hM : M.BlockTriangular id) : (a • M).BlockTriangular id :=
  fun _ _ h => by rw [Matrix.smul_apply, hM h, smul_zero]

private theorem blockTriangular_pow (hA : A.BlockTriangular id) (k : ℕ) :
    (A ^ k).BlockTriangular id := by
  induction k with
  | zero => simpa using Matrix.blockTriangular_one
  | succ k ih => rw [pow_succ]; exact ih.mul hA

private theorem blockTriangular_aeval (hA : A.BlockTriangular id) (p : ℂ[X]) :
    (aeval A p).BlockTriangular id := by
  induction p using Polynomial.induction_on with
  | C a =>
      rw [aeval_C, Algebra.algebraMap_eq_smul_one]
      exact blockTriangular_smul Matrix.blockTriangular_one
  | add p q hp hq => rw [map_add]; exact hp.add hq
  | monomial k a _ =>
      rw [map_mul, aeval_C, map_pow, aeval_X, Algebra.algebraMap_eq_smul_one, smul_mul_assoc,
        one_mul]
      exact blockTriangular_smul (blockTriangular_pow hA _)

/-- **Saad Lemma 1.13**: a normal triangular matrix is diagonal.  The conjugate transpose of a
normal matrix is a polynomial in it (Problem P-1.19, the backbone's
`Matrix.IsStarNormal.exists_aeval_eq_conjTranspose`), so `Aᴴ` is upper triangular as well, and a
matrix that is upper triangular together with its conjugate transpose is diagonal. -/
theorem lemma_1_13 (hA : IsStarNormal A) (hT : A.BlockTriangular id) : Matrix.IsDiag A := by
  obtain ⟨q, hq⟩ := Matrix.IsStarNormal.exists_aeval_eq_conjTranspose hA
  have hH : Aᴴ.BlockTriangular id := hq ▸ blockTriangular_aeval hT q
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · have hji := hH h
    rw [Matrix.conjTranspose_apply, star_eq_zero] at hji
    exact hji
  · exact hT h

end Lemma113

/-- **Saad Theorem 1.14**: a complex square matrix is normal if and only if it is unitarily
similar to a diagonal matrix.  This is the backbone's `Matrix.IsStarNormal.spectral_theorem`. -/
theorem theorem_1_14 {A : Matrix (Fin n) (Fin n) ℂ} :
    IsStarNormal A ↔
      ∃ Q ∈ Matrix.unitaryGroup (Fin n) ℂ, ∃ d : Fin n → ℂ, Qᴴ * A * Q = Matrix.diagonal d :=
  Matrix.IsStarNormal.spectral_theorem

section EigenBasis

variable {A : Matrix (Fin n) (Fin n) ℂ}

/-- **Saad Theorem 1.14**, in the form the section uses it: an orthonormal basis `q₁, …, q_n` of
eigenvectors of a normal matrix.  This is the backbone's
`LinearMap.IsStarNormal.eigenvectorBasis` for `Matrix.toEuclideanLin A`. -/
noncomputable abbrev normalEigenBasis (hA : IsStarNormal A) :
    OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)) :=
  LinearMap.IsStarNormal.eigenvectorBasis (Matrix.isStarNormal_toEuclideanLin_iff.2 hA)
    finrank_euclideanSpace_fin

/-- The eigenvalues `λ₁, …, λ_n` of a normal matrix, in the order of
`SaadSparse.Chapter01.normalEigenBasis`. -/
noncomputable abbrev normalEigenvalues (hA : IsStarNormal A) : Fin n → ℂ :=
  LinearMap.IsStarNormal.eigenvalues (Matrix.isStarNormal_toEuclideanLin_iff.2 hA)
    finrank_euclideanSpace_fin

/-- `SaadSparse.Chapter01.normalEigenBasis` is a basis of eigenvectors. -/
theorem apply_normalEigenBasis (hA : IsStarNormal A) (k : Fin n) :
    (A ⬝ normalEigenBasis hA k) = normalEigenvalues hA k • normalEigenBasis hA k :=
  LinearMap.IsStarNormal.apply_eigenvectorBasis _ _ k

/-- The eigenvalues of a normal matrix in the sense of `SaadSparse.Chapter01.normalEigenvalues` are
its spectrum. -/
theorem normalEigenvalues_mem_spectrum (hA : IsStarNormal A) (k : Fin n) :
    normalEigenvalues hA k ∈ spectrum ℂ A := by
  rw [← Matrix.hasEigenvalue_toEuclideanLin_iff]
  exact hasEigenvalue_of_hasEigenvector
    ⟨mem_eigenspace_iff.2 (apply_normalEigenBasis hA k),
      (normalEigenBasis hA).toBasis.ne_zero k⟩

/-- The conjugate transpose acts on the eigenbasis by the conjugate eigenvalues; this is the
easy half of Lemma 1.15 in coordinates. -/
theorem conjTranspose_apply_normalEigenBasis (hA : IsStarNormal A) (k : Fin n) :
    (Aᴴ ⬝ normalEigenBasis hA k) = conj (normalEigenvalues hA k) • normalEigenBasis hA k := by
  have hT := Matrix.isStarNormal_toEuclideanLin_iff.2 hA
  rw [Matrix.toEuclideanLin_conjTranspose]
  refine mem_eigenspace_iff.1 ?_
  rw [LinearMap.IsStarNormal.eigenspace_adjoint hT]
  exact mem_eigenspace_iff.2 (apply_normalEigenBasis hA k)

/-- The coordinate of `A x` along an eigenvector is the eigenvalue times the coordinate of `x`:
`(q_k, A x) = λ_k (q_k, x)`. -/
theorem inner_normalEigenBasis_apply (hA : IsStarNormal A) (k : Fin n)
    (x : EuclideanSpace ℂ (Fin n)) :
    inner ℂ (normalEigenBasis hA k) (A ⬝ x) =
      normalEigenvalues hA k * inner ℂ (normalEigenBasis hA k) x := by
  have h := LinearMap.adjoint_inner_left (toEuclideanLin A) x (normalEigenBasis hA k)
  rw [← Matrix.toEuclideanLin_conjTranspose, conjTranspose_apply_normalEigenBasis hA k,
    inner_smul_left, RingHomCompTriple.comp_apply, RingHom.id_apply] at h
  exact h.symm

end EigenBasis

/-- **Saad Lemma 1.15**: a matrix is normal if and only if every eigenvector of it is an
eigenvector of `Aᴴ`.  The forward direction is the backbone's
`LinearMap.IsStarNormal.eigenspace_adjoint`, the converse its harder companion
`LinearMap.isStarNormal_of_adjoint_apply_eq_smul`. -/
theorem lemma_1_15 {A : Matrix (Fin n) (Fin n) ℂ} :
    IsStarNormal A ↔
      ∀ (μ : ℂ) (v : EuclideanSpace ℂ (Fin n)), (A ⬝ v) = μ • v → ∃ ν : ℂ, (Aᴴ ⬝ v) = ν • v := by
  rw [← Matrix.isStarNormal_toEuclideanLin_iff]
  constructor
  · intro hT μ v hv
    refine ⟨conj μ, ?_⟩
    rw [Matrix.toEuclideanLin_conjTranspose]
    refine mem_eigenspace_iff.1 ?_
    rw [LinearMap.IsStarNormal.eigenspace_adjoint hT]
    exact mem_eigenspace_iff.2 hv
  · intro h
    refine LinearMap.isStarNormal_of_adjoint_apply_eq_smul fun μ v hv => ?_
    obtain ⟨ν, hν⟩ := h μ v hv
    exact ⟨ν, by rwa [Matrix.toEuclideanLin_conjTranspose] at hν⟩

/-- **Saad Corollary 1.16**: a normal matrix with real spectrum is Hermitian.  The converse is
Theorem 1.19. -/
theorem corollary_1_16 {A : Matrix (Fin n) (Fin n) ℂ} (hA : IsStarNormal A)
    (hreal : spectrum ℂ A ⊆ Set.range ((↑) : ℝ → ℂ)) : A.IsHermitian := by
  obtain ⟨Q, hQ, d, hd⟩ := theorem_1_14.mp hA
  have hspec : Set.range d = spectrum ℂ A := by
    rw [← spectrum_diagonal d, ← hd, ← Matrix.star_eq_conjTranspose]
    exact Unitary.spectrum_star_left_conjugate
      (U := (⟨Q, hQ⟩ : unitary (Matrix (Fin n) (Fin n) ℂ)))
  have hdiag : Matrix.diagonal (star d) = Matrix.diagonal d := by
    refine congrArg Matrix.diagonal (funext fun j => ?_)
    obtain ⟨r, hr⟩ := hreal (hspec ▸ Set.mem_range_self j)
    rw [Pi.star_apply, ← hr, RCLike.star_def, Complex.conj_ofReal]
  have hstar' : Q * star Q = 1 := (Unitary.mem_iff.1 hQ).2
  have hA' : A = Q * Matrix.diagonal d * Qᴴ := by
    rw [← hd, ← Matrix.star_eq_conjTranspose]
    calc A = Q * star Q * A * (Q * star Q) := by rw [hstar', Matrix.one_mul, Matrix.mul_one]
      _ = Q * (star Q * A * Q) * star Q := by simp only [Matrix.mul_assoc]
  change Aᴴ = A
  conv_lhs => rw [hA']
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.diagonal_conjTranspose, ← Matrix.mul_assoc,
    hdiag, ← hA']

/-! ### §1.9.1 The field of values and the numerical radius -/

section FieldOfValues

open scoped Matrix.Norms.L2Operator

variable {A : Matrix (Fin n) (Fin n) ℂ}

/-- **Saad (1.33)**: the Rayleigh quotient `μ(x) = (A x, x)/(x, x)` of a complex matrix, kept
complex.  The backbone's `LinearMap.rayleighQuotient` is its real part.  As always with a
division, the value at `x = 0` is the junk value `0`. -/
noncomputable def rayleigh (A : Matrix (Fin n) (Fin n) ℂ) (x : EuclideanSpace ℂ (Fin n)) : ℂ :=
  inner ℂ x (A ⬝ x) / inner ℂ x x

/-- **Saad §1.9.1**: the *field of values* of `A`, the set of its Rayleigh quotients at nonzero
vectors. -/
def fieldOfValues (A : Matrix (Fin n) (Fin n) ℂ) : Set ℂ :=
  {z | ∃ x : EuclideanSpace ℂ (Fin n), x ≠ 0 ∧ rayleigh A x = z}

/-- **Saad §1.9.1**: the *numerical radius* `ν(A) = max_{x ≠ 0} |μ(x)|`.  The supremum here runs
over *every* `x`, which is the same number: `rayleigh A 0` is the junk value `0`, and every value
of `‖rayleigh A ·‖` is nonnegative, so admitting `x = 0` cannot raise the supremum. -/
noncomputable def numericalRadius (A : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  ⨆ x : EuclideanSpace ℂ (Fin n), ‖rayleigh A x‖

/-- A matrix acts on Euclidean space as its `L²` operator norm allows. -/
theorem norm_toEuclideanLin_le (A : Matrix (Fin n) (Fin n) ℂ) (x : EuclideanSpace ℂ (Fin n)) :
    ‖(A ⬝ x)‖ ≤ ‖A‖ * ‖x‖ :=
  (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A).le_opNorm x

/-- **Saad §1.9.1**: every value of the Rayleigh quotient is bounded by the `2`-norm,
`|μ(x)| ≤ ‖A‖₂`. -/
theorem norm_rayleigh_le (A : Matrix (Fin n) (Fin n) ℂ) (x : EuclideanSpace ℂ (Fin n)) :
    ‖rayleigh A x‖ ≤ ‖A‖ := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [rayleigh]
  · have hxx : ‖(inner ℂ x x : ℂ)‖ = ‖x‖ ^ 2 := by
      rw [inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal,
        abs_of_nonneg (norm_nonneg x)]
    have hpos : (0 : ℝ) < ‖x‖ ^ 2 := by positivity
    rw [rayleigh, norm_div, hxx, div_le_iff₀ hpos]
    calc ‖(inner ℂ x (A ⬝ x) : ℂ)‖ ≤ ‖x‖ * ‖(A ⬝ x)‖ := norm_inner_le_norm (𝕜 := ℂ) x _
      _ ≤ ‖x‖ * (‖A‖ * ‖x‖) := by gcongr; exact norm_toEuclideanLin_le A x
      _ = ‖A‖ * ‖x‖ ^ 2 := by ring

private theorem bddAbove_rayleigh (A : Matrix (Fin n) (Fin n) ℂ) :
    BddAbove (Set.range fun x : EuclideanSpace ℂ (Fin n) => ‖rayleigh A x‖) :=
  ⟨‖A‖, by rintro _ ⟨x, rfl⟩; exact norm_rayleigh_le A x⟩

/-- Every Rayleigh quotient is bounded by the numerical radius. -/
theorem norm_rayleigh_le_numericalRadius (A : Matrix (Fin n) (Fin n) ℂ)
    (x : EuclideanSpace ℂ (Fin n)) : ‖rayleigh A x‖ ≤ numericalRadius A :=
  le_ciSup (bddAbove_rayleigh A) x

/-- **Saad §1.9.1**: `ν(A) ≤ ‖A‖₂`, the second half of the chain `ρ(A) ≤ ν(A) ≤ ‖A‖₂`. -/
theorem numericalRadius_le_l2_opNorm (A : Matrix (Fin n) (Fin n) ℂ) :
    numericalRadius A ≤ ‖A‖ :=
  ciSup_le fun x => norm_rayleigh_le A x

/-- **Saad Proposition 1.18**, the containment that needs no convexity: the field of values of
a complex square matrix contains its spectrum, since an eigenvalue is the Rayleigh quotient at
its eigenvector.  Given convexity — the Toeplitz–Hausdorff theorem, which is not proved here —
the field of values then contains the convex hull of the spectrum; for a normal matrix the two
are equal unconditionally, which is `SaadSparse.Chapter01.theorem_1_17`. -/
theorem proposition_1_18 (A : Matrix (Fin n) (Fin n) ℂ) :
    spectrum ℂ A ⊆ fieldOfValues A ∧
      (Convex ℝ (fieldOfValues A) → convexHull ℝ (spectrum ℂ A) ⊆ fieldOfValues A) := by
  have hsub : spectrum ℂ A ⊆ fieldOfValues A := by
    intro μ hμ
    obtain ⟨v, hv, hv0⟩ :=
      Module.End.HasEigenvalue.exists_hasEigenvector
        ((Matrix.hasEigenvalue_toEuclideanLin_iff A μ).2 hμ)
    refine ⟨v, hv0, ?_⟩
    have hvv : (inner ℂ v v : ℂ) ≠ 0 := fun h => hv0 (inner_self_eq_zero.1 h)
    rw [rayleigh, mem_eigenspace_iff.1 hv, inner_smul_right, mul_div_assoc,
      div_self hvv, mul_one]
  exact ⟨hsub, fun hconv => convexHull_min hsub hconv⟩

/-- **Saad §1.9.1**: `ρ(A) ≤ ν(A)`, the first half of the chain `ρ(A) ≤ ν(A) ≤ ‖A‖₂`. -/
theorem spectralRadius_le_numericalRadius (A : Matrix (Fin n) (Fin n) ℂ) :
    spectralRadius ℂ A ≤ ENNReal.ofReal (numericalRadius A) := by
  refine iSup₂_le fun μ hμ => ?_
  obtain ⟨x, _, hx⟩ := (proposition_1_18 A).1 hμ
  rw [← enorm_eq_nnnorm, ← ofReal_norm, ← hx]
  exact ENNReal.ofReal_le_ofReal (norm_rayleigh_le_numericalRadius A x)

end FieldOfValues

/-! ### §1.9.1 The Rayleigh quotient of a normal matrix -/

section Normal

variable {A : Matrix (Fin n) (Fin n) ℂ}

/-- The squared eigenbasis coordinates of a vector, the weights of (1.34). -/
private noncomputable def coordSq (hA : IsStarNormal A) (x : EuclideanSpace ℂ (Fin n))
    (k : Fin n) : ℝ := ‖(inner ℂ (normalEigenBasis hA k) x : ℂ)‖ ^ 2

private theorem coordSq_def (hA : IsStarNormal A) (x : EuclideanSpace ℂ (Fin n)) (k : Fin n) :
    coordSq hA x k = ‖(inner ℂ (normalEigenBasis hA k) x : ℂ)‖ ^ 2 := rfl

private theorem coordSq_nonneg (hA : IsStarNormal A) (x : EuclideanSpace ℂ (Fin n)) (k : Fin n) :
    0 ≤ coordSq hA x k := sq_nonneg _

private theorem coordSq_cast (hA : IsStarNormal A) (x : EuclideanSpace ℂ (Fin n)) (k : Fin n) :
    ((coordSq hA x k : ℝ) : ℂ) =
      inner ℂ x (normalEigenBasis hA k) * inner ℂ (normalEigenBasis hA k) x := by
  rw [coordSq_def, ← inner_conj_symm x (normalEigenBasis hA k), RCLike.conj_mul]
  norm_cast

private theorem sum_coordSq (hA : IsStarNormal A) (x : EuclideanSpace ℂ (Fin n)) :
    ((∑ k, coordSq hA x k : ℝ) : ℂ) = inner ℂ x x := by
  rw [← (normalEigenBasis hA).sum_inner_mul_inner x x]
  push_cast
  exact Finset.sum_congr rfl fun k _ => coordSq_cast hA x k

private theorem sum_coordSq_pos (hA : IsStarNormal A) {x : EuclideanSpace ℂ (Fin n)}
    (hx : x ≠ 0) : 0 < ∑ k, coordSq hA x k := by
  rcases (Finset.sum_nonneg fun k (_ : k ∈ univ) => coordSq_nonneg hA x k).lt_or_eq with h | h
  · exact h
  · refine absurd (inner_self_eq_zero (𝕜 := ℂ).1 ?_) hx
    rw [← sum_coordSq hA x, ← h]
    simp

private theorem inner_apply_eq_sum (hA : IsStarNormal A) (x : EuclideanSpace ℂ (Fin n)) :
    (inner ℂ x (A ⬝ x) : ℂ) =
      ∑ k, ((coordSq hA x k : ℝ) : ℂ) * normalEigenvalues hA k := by
  rw [← (normalEigenBasis hA).sum_inner_mul_inner x (A ⬝ x)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [inner_normalEigenBasis_apply hA k x, coordSq_cast hA x k]
  ring

/-- **Saad (1.34)**: the Rayleigh quotient of a normal matrix at a nonzero vector is a convex
combination of its eigenvalues, with weights read off the expansion of the vector in the
orthonormal eigenbasis. -/
theorem equation_1_34 (hA : IsStarNormal A) {x : EuclideanSpace ℂ (Fin n)} (hx : x ≠ 0) :
    ∃ β : Fin n → ℝ, (∀ k, 0 ≤ β k) ∧ ∑ k, β k = 1 ∧
      rayleigh A x = ∑ k, (β k : ℂ) * normalEigenvalues hA k := by
  have hpos := sum_coordSq_pos hA hx
  refine ⟨fun k => coordSq hA x k / ∑ j, coordSq hA x j,
    fun k => div_nonneg (coordSq_nonneg hA x k) hpos.le, ?_, ?_⟩
  · rw [← Finset.sum_div, div_self hpos.ne']
  · rw [rayleigh, inner_apply_eq_sum hA x, ← sum_coordSq hA x, Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    push_cast
    ring

private theorem spectrum_subset_range_normalEigenvalues (hA : IsStarNormal A) :
    spectrum ℂ A ⊆ Set.range (normalEigenvalues hA) := by
  intro μ hμ
  obtain ⟨v, hv, hv0⟩ := Module.End.HasEigenvalue.exists_hasEigenvector
    ((Matrix.hasEigenvalue_toEuclideanLin_iff A μ).2 hμ)
  by_contra hcon
  have hall : ∀ k, (inner ℂ (normalEigenBasis hA k) v : ℂ) = 0 := by
    intro k
    have h1 : (inner ℂ (normalEigenBasis hA k) (A ⬝ v) : ℂ) =
        μ * inner ℂ (normalEigenBasis hA k) v := by
      rw [mem_eigenspace_iff.1 hv, inner_smul_right]
    rw [inner_normalEigenBasis_apply hA k v] at h1
    have h2 : (normalEigenvalues hA k - μ) * inner ℂ (normalEigenBasis hA k) v = 0 := by
      rw [sub_mul, h1, sub_self]
    exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 fun hc => hcon ⟨k, hc⟩)
  exact hv0 (((normalEigenBasis hA).sum_repr' v).symm.trans
    (Finset.sum_eq_zero fun k _ => by rw [hall k, zero_smul]))

private theorem convexCombination_mem_fieldOfValues (hA : IsStarNormal A) {β : Fin n → ℝ}
    (hβ0 : ∀ k, 0 ≤ β k) (hβ1 : ∑ k, β k = 1) :
    (∑ k, (β k : ℂ) * normalEigenvalues hA k) ∈ fieldOfValues A := by
  classical
  set x : EuclideanSpace ℂ (Fin n) :=
    ∑ k, ((Real.sqrt (β k) : ℝ) : ℂ) • normalEigenBasis hA k with hxdef
  have hinner : ∀ k, (inner ℂ (normalEigenBasis hA k) x : ℂ) = ((Real.sqrt (β k) : ℝ) : ℂ) := by
    intro k
    have hortho := orthonormal_iff_ite.1 (normalEigenBasis hA).orthonormal
    rw [hxdef, inner_sum, Finset.sum_eq_single k]
    · rw [inner_smul_right, hortho k k]
      simp
    · intro j _ hj
      rw [inner_smul_right, hortho k j]
      simp [Ne.symm hj]
    · intro hk; exact absurd (Finset.mem_univ k) hk
  have hcoord : ∀ k, coordSq hA x k = β k := by
    intro k
    rw [coordSq_def, hinner k, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (hβ0 k)]
  have hsum : ∑ k, coordSq hA x k = 1 := by simp only [hcoord]; exact hβ1
  have hx0 : x ≠ 0 := by
    intro hc
    rw [hc] at hsum
    simp [coordSq_def] at hsum
  refine ⟨x, hx0, ?_⟩
  rw [rayleigh, inner_apply_eq_sum hA x, ← sum_coordSq hA x, hsum]
  simp only [hcoord, Complex.ofReal_one, div_one]

/-- **Saad Theorem 1.17**: the field of values of a normal matrix is the convex hull of its
spectrum.  The inclusion from left to right is (1.34); the reverse holds because every convex
combination of eigenvalues is attained at a suitable combination of the eigenvectors.  Saad
deduces the statement from the Toeplitz–Hausdorff theorem, which this argument does not need. -/
theorem theorem_1_17 {A : Matrix (Fin n) (Fin n) ℂ} (hA : IsStarNormal A) :
    fieldOfValues A = convexHull ℝ (spectrum ℂ A) := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨x, hx0, rfl⟩
    obtain ⟨β, hβ0, hβ1, hβ⟩ := equation_1_34 hA hx0
    rw [hβ]
    refine (convex_convexHull ℝ (spectrum ℂ A)).sum_mem (fun k _ => hβ0 k) hβ1 fun k _ => ?_
    exact subset_convexHull ℝ _ (normalEigenvalues_mem_spectrum hA k)
  · refine convexHull_min ?_ ?_
    · intro μ hμ
      obtain ⟨k, rfl⟩ := spectrum_subset_range_normalEigenvalues hA hμ
      have h := convexCombination_mem_fieldOfValues hA
        (β := fun j => if j = k then (1 : ℝ) else 0)
        (fun j => by by_cases hj : j = k <;> simp [hj]) (by simp)
      have hsum : ∑ j, (((if j = k then (1 : ℝ) else 0) : ℝ) : ℂ) * normalEigenvalues hA j =
          normalEigenvalues hA k := by
        rw [Finset.sum_eq_single k]
        · simp
        · intro b _ hb
          simp [hb]
        · intro hk
          exact absurd (Finset.mem_univ k) hk
      rwa [hsum] at h
    · rintro z ⟨x, hx0, rfl⟩ w ⟨y, hy0, rfl⟩ a b ha hb hab
      obtain ⟨β, hβ0, hβ1, hβ⟩ := equation_1_34 hA hx0
      obtain ⟨γ, hγ0, hγ1, hγ⟩ := equation_1_34 hA hy0
      have hmem := convexCombination_mem_fieldOfValues hA
        (β := fun k => a * β k + b * γ k)
        (fun k => by have := hβ0 k; have := hγ0 k; positivity)
        (by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hβ1, hγ1,
              mul_one, mul_one, hab])
      have hcalc : ∑ k, ((a * β k + b * γ k : ℝ) : ℂ) * normalEigenvalues hA k =
          a • rayleigh A x + b • rayleigh A y := by
        rw [hβ, hγ, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [Complex.real_smul]
        push_cast
        ring
      rwa [hcalc] at hmem

end Normal

/-! ### §1.9.2 Hermitian matrices -/

section Hermitian

variable {𝕜 : Type*} [RCLike 𝕜] {A : Matrix (Fin n) (Fin n) 𝕜}

/-- **Saad Theorem 1.19**: the eigenvalues of a Hermitian matrix are real. -/
theorem theorem_1_19 (hA : A.IsHermitian) : spectrum 𝕜 A ⊆ Set.range ((↑) : ℝ → 𝕜) := by
  rw [hA.spectrum_eq_image_range]
  rintro _ ⟨r, _, rfl⟩
  exact ⟨_, rfl⟩

/-- **Saad Theorem 1.20**: a Hermitian matrix is unitarily similar to a *real* diagonal matrix,
and so has an orthonormal basis of eigenvectors.  Mathlib's
`Matrix.IsHermitian.spectral_theorem` and `Matrix.IsHermitian.eigenvectorUnitary`. -/
theorem theorem_1_20 (hA : A.IsHermitian) :
    ∃ Q ∈ Matrix.unitaryGroup (Fin n) 𝕜, ∃ d : Fin n → ℝ,
      Qᴴ * A * Q = Matrix.diagonal (RCLike.ofReal ∘ d) := by
  refine ⟨hA.eigenvectorUnitary, (hA.eigenvectorUnitary).2, hA.eigenvalues, ?_⟩
  have h := hA.conjStarAlgAut_star_eigenvectorUnitary
  rwa [Unitary.conjStarAlgAut_star_apply, Matrix.star_eq_conjTranspose] at h

/-- **Saad §1.9.2** with its converse (Problem P-1.15): a complex square matrix has real
quadratic form `(A x, x)` at every vector exactly when it is Hermitian.  Both halves fail over
`ℝ`, which is why Saad's "positive definite" of §1.11 does not force symmetry. -/
theorem inner_self_isReal_iff_isHermitian {A : Matrix (Fin n) (Fin n) ℂ} :
    (∀ x : EuclideanSpace ℂ (Fin n), (inner ℂ x (A ⬝ x) : ℂ).im = 0) ↔ A.IsHermitian := by
  constructor
  · intro h
    have hzero : ∀ x : EuclideanSpace ℂ (Fin n),
        (inner ℂ ((toEuclideanLin A - toEuclideanLin Aᴴ) x) x : ℂ) = 0 := by
      intro x
      have him : (inner ℂ ((toEuclideanLin A) x) x : ℂ).im = 0 := by
        have h1 : (inner ℂ ((toEuclideanLin A) x) x : ℂ) =
            (starRingEnd ℂ) (inner ℂ x ((toEuclideanLin A) x)) := (inner_conj_symm _ _).symm
        rw [h1, Complex.conj_im, neg_eq_zero]
        exact h x
      rw [LinearMap.sub_apply, inner_sub_left, Matrix.toEuclideanLin_conjTranspose,
        LinearMap.adjoint_inner_left, ← inner_conj_symm x (toEuclideanLin A x),
        Complex.conj_eq_iff_im.mpr him, sub_self]
    have hsub := (inner_map_self_eq_zero _).1 hzero
    rw [sub_eq_zero] at hsub
    have hAeq : toEuclideanLin Aᴴ = toEuclideanLin A := hsub.symm
    exact Matrix.toEuclideanLin.injective hAeq
  · intro hA x
    have hsym : (toEuclideanLin A).IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
    have h : conj (inner ℂ x (A ⬝ x) : ℂ) = inner ℂ x (A ⬝ x) := by
      rw [inner_conj_symm]
      exact hsym x x
    exact Complex.conj_eq_iff_im.mp h

/-- **Saad §1.9.2**: the eigenvalues `λ₁ ≥ ⋯ ≥ λ_n` of a Hermitian matrix, in the book's
decreasing order.  This is the backbone's `LinearMap.IsSymmetric.eigenvalues` for
`Matrix.toEuclideanLin A`; Mathlib's `Matrix.IsHermitian.eigenvalues` is in no particular
order. -/
noncomputable abbrev eigenvaluesDesc (hA : A.IsHermitian) : Fin n → ℝ :=
  (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvalues finrank_euclideanSpace_fin

/-- **Saad §1.9.2**: the orthonormal eigenvectors `q₁, …, q_n` of a Hermitian matrix, ordered so
that `q_k` belongs to `SaadSparse.Chapter01.eigenvaluesDesc hA k`. -/
noncomputable abbrev eigenvectorBasisDesc (hA : A.IsHermitian) :
    OrthonormalBasis (Fin n) 𝕜 (EuclideanSpace 𝕜 (Fin n)) :=
  (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvectorBasis finrank_euclideanSpace_fin

/-- The eigenvalues of `SaadSparse.Chapter01.eigenvaluesDesc` really do decrease. -/
theorem eigenvaluesDesc_antitone (hA : A.IsHermitian) : Antitone (eigenvaluesDesc hA) :=
  LinearMap.IsSymmetric.eigenvalues_antitone _ _

/-- **Saad Theorem 1.21**, the Courant–Fischer min–max principle (1.37) and its dual max–min
form (1.39): the `k`-th eigenvalue in decreasing order is the minimum over subspaces of
dimension `n - k` of the maximum of the Rayleigh quotient there, and the maximum over subspaces
of dimension `k + 1` of its minimum.  The backbone's
`LinearMap.IsSymmetric.eigenvalues_eq_iInf_iSup` and `eigenvalues_eq_iSup_iInf`. -/
theorem theorem_1_21 (hA : A.IsHermitian) (k : Fin n) :
    eigenvaluesDesc hA k =
        ⨅ S : {S : Submodule 𝕜 (EuclideanSpace 𝕜 (Fin n)) // Module.finrank 𝕜 S = n - (k : ℕ)},
          ⨆ x : {x : EuclideanSpace 𝕜 (Fin n) // x ∈ (S : Submodule 𝕜 _) ∧ x ≠ 0},
            (toEuclideanLin A).rayleighQuotient (x : EuclideanSpace 𝕜 (Fin n)) ∧
      eigenvaluesDesc hA k =
        ⨆ S : {S : Submodule 𝕜 (EuclideanSpace 𝕜 (Fin n)) // Module.finrank 𝕜 S = (k : ℕ) + 1},
          ⨅ x : {x : EuclideanSpace 𝕜 (Fin n) // x ∈ (S : Submodule 𝕜 _) ∧ x ≠ 0},
            (toEuclideanLin A).rayleighQuotient (x : EuclideanSpace 𝕜 (Fin n)) :=
  ⟨LinearMap.IsSymmetric.eigenvalues_eq_iInf_iSup _ _ k,
    LinearMap.IsSymmetric.eigenvalues_eq_iSup_iInf _ _ k⟩

/-- **Saad (1.38)**: the largest eigenvalue of a Hermitian matrix is the greatest value of the
Rayleigh quotient. -/
theorem equation_1_38 {m : ℕ} {A : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜} (hA : A.IsHermitian) :
    IsGreatest {c : ℝ | ∃ x : EuclideanSpace 𝕜 (Fin (m + 1)), x ≠ 0 ∧
      (toEuclideanLin A).rayleighQuotient x = c} (eigenvaluesDesc hA 0) := by
  have h := LinearMap.IsSymmetric.isGreatest_rayleighQuotient_orthogonal
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA) finrank_euclideanSpace_fin 0
  simpa using h

/-- **Saad (1.40)**: the smallest eigenvalue of a Hermitian matrix is the least value of the
Rayleigh quotient. -/
theorem equation_1_40 {m : ℕ} {A : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜} (hA : A.IsHermitian) :
    IsLeast {c : ℝ | ∃ x : EuclideanSpace 𝕜 (Fin (m + 1)), x ≠ 0 ∧
      (toEuclideanLin A).rayleighQuotient x = c} (eigenvaluesDesc hA (Fin.last m)) := by
  set hT := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  refine ⟨⟨hT.eigenvectorBasis finrank_euclideanSpace_fin (Fin.last m),
    hT.eigenvectorBasis_ne_zero finrank_euclideanSpace_fin _,
    hT.rayleighQuotient_eigenvectorBasis finrank_euclideanSpace_fin _⟩, ?_⟩
  rintro c ⟨x, hx0, rfl⟩
  exact hT.le_rayleighQuotient_of_forall finrank_euclideanSpace_fin
    (fun i => hT.eigenvalues_antitone finrank_euclideanSpace_fin (Fin.le_last i)) hx0

/-- **Saad Theorem 1.22**, the Courant characterization (1.41): the `k`-th eigenvalue is the
Rayleigh quotient at the `k`-th eigenvector, and is the greatest value of the Rayleigh quotient
over the vectors orthogonal to `q₁, …, q_{k-1}`.  The backbone's
`LinearMap.IsSymmetric.isGreatest_rayleighQuotient_orthogonal`. -/
theorem theorem_1_22 (hA : A.IsHermitian) (k : Fin n) :
    (toEuclideanLin A).rayleighQuotient (eigenvectorBasisDesc hA k) = eigenvaluesDesc hA k ∧
      IsGreatest {c : ℝ | ∃ x : EuclideanSpace 𝕜 (Fin n), x ≠ 0 ∧
        (∀ j < k, inner 𝕜 (eigenvectorBasisDesc hA j) x = 0) ∧
        (toEuclideanLin A).rayleighQuotient x = c} (eigenvaluesDesc hA k) :=
  ⟨LinearMap.IsSymmetric.rayleighQuotient_eigenvectorBasis _ _ k,
    LinearMap.IsSymmetric.isGreatest_rayleighQuotient_orthogonal _ _ k⟩

end Hermitian

end SaadSparse.Chapter01
