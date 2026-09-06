/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix.Kronecker`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Numlib.Analysis.Matrix.ToEuclideanLin

/-!
# The Kronecker sum and separation of variables

The **Kronecker sum** of `A : Matrix m m R` and `B : Matrix n n R` is
`A ⊕ₖ B = A ⊗ₖ 1 + 1 ⊗ₖ B : Matrix (m × n) (m × n) R`, the matrix of the operator
`x ⊗ y ↦ A x ⊗ y + x ⊗ B y`.  Mathlib has the Kronecker *product* `A ⊗ₖ B` and its algebra but
neither this construction nor any spectral statement about it, and this file supplies both.

The point is separation of variables.  On the elementary tensor `kroneckerVec v w`, whose
`(i, j)` entry is `v i * w j`, one has

`(A ⊕ₖ B) *ᵥ (v ⊗ w) = (A *ᵥ v) ⊗ w + v ⊗ (B *ᵥ w)`,

so an eigenvector `v` of `A` for `σ` and an eigenvector `w` of `B` for `μ` produce an
eigenvector `v ⊗ w` of `A ⊕ₖ B` for `σ + μ`.  Because the elementary tensors of two orthonormal
bases are again an orthonormal basis (`Matrix.kroneckerOrthonormalBasis`, whose whole proof is
`⟪v ⊗ w, v' ⊗ w'⟫ = ⟪v, v'⟫ ⟪w, w'⟫`), those eigenvectors exhaust the space: the spectrum of a
Kronecker sum of two diagonalizable matrices is the sum set of the two spectra, and a repeated
value `σ_k + μ_l` still corresponds to independent eigenvectors.

The spectral consequence is stated without naming an eigenvalue: quadratic-form bounds and
coercivity constants simply **add** under a Kronecker sum
(`Matrix.isSymmetricBoundedBy_kroneckerSum`, `Matrix.isCoerciveWith_kroneckerSum`,
`Matrix.posDef_kroneckerSum`).  That is proved by fibring `m × n` in both directions, with no
eigenvector in sight, and it is how a two-dimensional model problem enters a convergence
estimate: the five-point Laplacean is the Kronecker sum of two copies of the tridiagonal
Toeplitz matrix of `Numlib.LinearAlgebra.Matrix.TridiagonalToeplitz`, and the bounds of that
module add.  Saad, *Iterative Methods for Sparse Linear Systems*[^saad-iterative], §13.2 writes
the tensor sum as `T_x ⊕ T_y` and states its eigenvalues without proof.

Everything here is indexed by the product type `m × n`, matching Mathlib's `kroneckerMap`; a
consumer that wants `Fin (n₁ * n₂)` reindexes with `Matrix.reindex` and a `Fin`-product
equivalence.

## References

[^saad-iterative]: Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition,
  SIAM, 2003.
-/

open scoped Matrix Kronecker

namespace Matrix

/-! ### The Kronecker sum of two matrices -/

section Ring

variable {R : Type*} [CommRing R] {l m n p : Type*}

section Def

variable [DecidableEq m] [DecidableEq n]

/-- The Kronecker sum `A ⊕ₖ B = A ⊗ₖ 1 + 1 ⊗ₖ B`, the matrix of `x ⊗ y ↦ A x ⊗ y + x ⊗ B y`. -/
def kroneckerSum (A : Matrix m m R) (B : Matrix n n R) : Matrix (m × n) (m × n) R :=
  A ⊗ₖ (1 : Matrix n n R) + (1 : Matrix m m R) ⊗ₖ B

@[inherit_doc]
scoped[Kronecker] infixl:100 " ⊕ₖ " => Matrix.kroneckerSum

theorem kroneckerSum_def (A : Matrix m m R) (B : Matrix n n R) :
    A ⊕ₖ B = A ⊗ₖ (1 : Matrix n n R) + (1 : Matrix m m R) ⊗ₖ B := rfl

theorem kroneckerSum_apply (A : Matrix m m R) (B : Matrix n n R) (i₁ j₁ : m) (i₂ j₂ : n) :
    (A ⊕ₖ B) (i₁, i₂) (j₁, j₂)
      = (if i₂ = j₂ then A i₁ j₁ else 0) + (if i₁ = j₁ then B i₂ j₂ else 0) := by
  simp [kroneckerSum, one_apply, mul_ite, ite_mul]

/-- The Kronecker sum is additive as a function of the pair `(A, B)`. -/
theorem kroneckerSum_add (A₁ A₂ : Matrix m m R) (B₁ B₂ : Matrix n n R) :
    (A₁ + A₂) ⊕ₖ (B₁ + B₂) = A₁ ⊕ₖ B₁ + A₂ ⊕ₖ B₂ := by
  simp only [kroneckerSum, add_kronecker, kronecker_add]
  abel

theorem kroneckerSum_smul (c : R) (A : Matrix m m R) (B : Matrix n n R) :
    (c • A) ⊕ₖ (c • B) = c • (A ⊕ₖ B) := by
  simp only [kroneckerSum, smul_kronecker, kronecker_smul, smul_add]

@[simp]
theorem kroneckerSum_zero_zero : (0 : Matrix m m R) ⊕ₖ (0 : Matrix n n R) = 0 := by
  simp [kroneckerSum]

theorem conjTranspose_kroneckerSum [StarRing R] (A : Matrix m m R) (B : Matrix n n R) :
    (A ⊕ₖ B)ᴴ = Aᴴ ⊕ₖ Bᴴ := by
  simp [kroneckerSum, conjTranspose_add, conjTranspose_kronecker]

theorem isHermitian_kroneckerSum [StarRing R] {A : Matrix m m R} {B : Matrix n n R}
    (hA : A.IsHermitian) (hB : B.IsHermitian) : (A ⊕ₖ B).IsHermitian := by
  rw [IsHermitian, conjTranspose_kroneckerSum, hA.eq, hB.eq]

end Def

/-! ### Elementary tensors -/

/-- The Kronecker product of two vectors: `kroneckerVec v w (i, j) = v i * w j`. -/
def kroneckerVec (v : m → R) (w : n → R) : m × n → R := fun q => v q.1 * w q.2

@[simp]
theorem kroneckerVec_apply (v : m → R) (w : n → R) (i : m) (j : n) :
    kroneckerVec v w (i, j) = v i * w j := rfl

theorem kroneckerVec_smul_left (c : R) (v : m → R) (w : n → R) :
    kroneckerVec (c • v) w = c • kroneckerVec v w := by
  funext q; simp [kroneckerVec, mul_assoc]

theorem kroneckerVec_smul_right (c : R) (v : m → R) (w : n → R) :
    kroneckerVec v (c • w) = c • kroneckerVec v w := by
  funext q; simp [kroneckerVec, mul_left_comm]

theorem kroneckerVec_ne_zero [NoZeroDivisors R] {v : m → R} {w : n → R} (hv : v ≠ 0)
    (hw : w ≠ 0) : kroneckerVec v w ≠ 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hv
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hw
  intro h
  exact mul_ne_zero hi hj (by simpa using congrFun h (i, j))

/-- The Kronecker product of matrices acts on an elementary tensor factor by factor. -/
theorem kronecker_mulVec [Fintype m] [Fintype n] (A : Matrix l m R) (B : Matrix p n R)
    (v : m → R) (w : n → R) :
    (A ⊗ₖ B) *ᵥ kroneckerVec v w = kroneckerVec (A *ᵥ v) (B *ᵥ w) := by
  funext q
  simp only [mulVec_apply_eq_sum, Fintype.sum_prod_type, kroneckerVec, kroneckerMap_apply]
  rw [Fintype.sum_mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

variable [DecidableEq m] [DecidableEq n]

/-- The Leibniz rule for a Kronecker sum on an elementary tensor, Saad's (13.13). -/
theorem kroneckerSum_mulVec_kroneckerVec [Fintype m] [Fintype n] (A : Matrix m m R)
    (B : Matrix n n R) (v : m → R) (w : n → R) :
    (A ⊕ₖ B) *ᵥ kroneckerVec v w = kroneckerVec (A *ᵥ v) w + kroneckerVec v (B *ᵥ w) := by
  rw [kroneckerSum, add_mulVec, kronecker_mulVec, kronecker_mulVec, one_mulVec, one_mulVec]

/-- Separation of variables: an eigenvector `v` of `A` for `σ` and an eigenvector `w` of `B` for
`μ` give an eigenvector `v ⊗ w` of `A ⊕ₖ B` for `σ + μ`. -/
theorem kroneckerSum_mulVec_kroneckerVec_of_mulVec_eq_smul [Fintype m] [Fintype n]
    {A : Matrix m m R} {B : Matrix n n R} {v : m → R} {w : n → R} {σ μ : R}
    (hv : A *ᵥ v = σ • v) (hw : B *ᵥ w = μ • w) :
    (A ⊕ₖ B) *ᵥ kroneckerVec v w = (σ + μ) • kroneckerVec v w := by
  rw [kroneckerSum_mulVec_kroneckerVec, hv, hw, kroneckerVec_smul_left,
    kroneckerVec_smul_right, add_smul]

end Ring

/-! ### The tensor orthonormal basis -/

section RCLike

open scoped ComplexOrder

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n]

/-- The inner product of two elementary tensors factors: `⟪v ⊗ w, v' ⊗ w'⟫ = ⟪v, v'⟫ ⟪w, w'⟫`.
This one line is the whole proof that tensors of orthonormal bases are orthonormal. -/
theorem kroneckerVec_inner (v v' : m → 𝕜) (w w' : n → 𝕜) :
    inner 𝕜 (WithLp.toLp 2 (kroneckerVec v w)) (WithLp.toLp 2 (kroneckerVec v' w'))
      = inner 𝕜 (WithLp.toLp 2 v) (WithLp.toLp 2 v')
        * inner 𝕜 (WithLp.toLp 2 w) (WithLp.toLp 2 w') := by
  simp only [EuclideanSpace.inner_toLp_toLp, dotProduct, Pi.star_apply, kroneckerVec,
    Fintype.sum_prod_type]
  rw [Fintype.sum_mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
    simp only [RCLike.star_def, map_mul]; ring

/-- The `j`-th column fibre of a vector indexed by `m × n`. -/
private def colFibre (z : EuclideanSpace 𝕜 (m × n)) (j : n) : EuclideanSpace 𝕜 m :=
  WithLp.toLp 2 fun i => WithLp.ofLp z (i, j)

/-- The `i`-th row fibre of a vector indexed by `m × n`. -/
private def rowFibre (z : EuclideanSpace 𝕜 (m × n)) (i : m) : EuclideanSpace 𝕜 n :=
  WithLp.toLp 2 fun j => WithLp.ofLp z (i, j)

private theorem norm_sq_eq_sum_colFibre (z : EuclideanSpace 𝕜 (m × n)) :
    ‖z‖ ^ 2 = ∑ j, ‖colFibre z j‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, colFibre]
  rw [Fintype.sum_prod_type_right]

private theorem norm_sq_eq_sum_rowFibre (z : EuclideanSpace 𝕜 (m × n)) :
    ‖z‖ ^ 2 = ∑ i, ‖rowFibre z i‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, rowFibre]
  rw [Fintype.sum_prod_type]

variable [DecidableEq m] [DecidableEq n]

/-- The elementary tensors of two orthonormal bases form an orthonormal basis of
`EuclideanSpace 𝕜 (m × n)`.  With `Matrix.kroneckerSum_mulVec_kroneckerVec_of_mulVec_eq_smul`
this exhibits *all* eigenpairs of a Kronecker sum of two diagonalizable matrices. -/
noncomputable def kroneckerOrthonormalBasis (u : OrthonormalBasis m 𝕜 (EuclideanSpace 𝕜 m))
    (u' : OrthonormalBasis n 𝕜 (EuclideanSpace 𝕜 n)) :
    OrthonormalBasis (m × n) 𝕜 (EuclideanSpace 𝕜 (m × n)) :=
  have hon : Orthonormal 𝕜 fun q : m × n => WithLp.toLp 2
      (kroneckerVec (WithLp.ofLp (u q.1)) (WithLp.ofLp (u' q.2))) := by
    refine orthonormal_iff_ite.2 fun q q' => ?_
    rw [kroneckerVec_inner]
    simp only [WithLp.toLp_ofLp]
    rw [orthonormal_iff_ite.1 u.orthonormal, orthonormal_iff_ite.1 u'.orthonormal]
    by_cases h1 : q.1 = q'.1 <;> by_cases h2 : q.2 = q'.2 <;> simp [h1, h2, Prod.ext_iff]
  OrthonormalBasis.mk hon
    (hon.linearIndependent.span_eq_top_of_card_eq_finrank' (by simp [finrank_euclideanSpace])).ge

@[simp]
theorem kroneckerOrthonormalBasis_apply (u : OrthonormalBasis m 𝕜 (EuclideanSpace 𝕜 m))
    (u' : OrthonormalBasis n 𝕜 (EuclideanSpace 𝕜 n)) (q : m × n) :
    kroneckerOrthonormalBasis u u' q
      = WithLp.toLp 2 (kroneckerVec (WithLp.ofLp (u q.1)) (WithLp.ofLp (u' q.2))) := by
  rw [kroneckerOrthonormalBasis, OrthonormalBasis.coe_mk]

/-- The eigenpairs of a Kronecker sum, in `EuclideanSpace` form. -/
theorem hasEigenvector_kroneckerSum {A : Matrix m m 𝕜} {B : Matrix n n 𝕜} {v : m → 𝕜}
    {w : n → 𝕜} {σ μ : 𝕜} (hv : A *ᵥ v = σ • v) (hw : B *ᵥ w = μ • w) (hv0 : v ≠ 0)
    (hw0 : w ≠ 0) :
    Module.End.HasEigenvector (toEuclideanLin (A ⊕ₖ B)) (σ + μ)
      (WithLp.toLp 2 (kroneckerVec v w)) := by
  refine ⟨Module.End.mem_eigenspace_iff.2 ?_, ?_⟩
  · change WithLp.toLp 2 ((A ⊕ₖ B) *ᵥ kroneckerVec v w) = _
    rw [kroneckerSum_mulVec_kroneckerVec_of_mulVec_eq_smul hv hw]
    rfl
  · simpa using kroneckerVec_ne_zero hv0 hw0

/-! ### Quadratic-form bounds add -/

private theorem inner_kronecker_one_left (A : Matrix m m 𝕜) (z : EuclideanSpace 𝕜 (m × n)) :
    inner 𝕜 (toEuclideanLin (A ⊗ₖ (1 : Matrix n n 𝕜)) z) z
      = ∑ j, inner 𝕜 (toEuclideanLin A (colFibre z j)) (colFibre z j) := by
  have hfib : ∀ (i : m) (j : n), ((A ⊗ₖ (1 : Matrix n n 𝕜)) *ᵥ WithLp.ofLp z) (i, j)
      = (A *ᵥ WithLp.ofLp (colFibre z j)) i := by
    intro i j
    simp [colFibre, mulVec_apply_eq_sum, Fintype.sum_prod_type, one_apply]
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply]
  rw [Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [show WithLp.ofLp (toEuclideanLin (A ⊗ₖ (1 : Matrix n n 𝕜)) z)
    = (A ⊗ₖ (1 : Matrix n n 𝕜)) *ᵥ WithLp.ofLp z from rfl, hfib i j]
  rfl

private theorem inner_one_kronecker_right (B : Matrix n n 𝕜) (z : EuclideanSpace 𝕜 (m × n)) :
    inner 𝕜 (toEuclideanLin ((1 : Matrix m m 𝕜) ⊗ₖ B) z) z
      = ∑ i, inner 𝕜 (toEuclideanLin B (rowFibre z i)) (rowFibre z i) := by
  have hfib : ∀ (i : m) (j : n), (((1 : Matrix m m 𝕜) ⊗ₖ B) *ᵥ WithLp.ofLp z) (i, j)
      = (B *ᵥ WithLp.ofLp (rowFibre z i)) j := by
    intro i j
    simp [rowFibre, mulVec_apply_eq_sum, Fintype.sum_prod_type, one_apply]
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [show WithLp.ofLp (toEuclideanLin ((1 : Matrix m m 𝕜) ⊗ₖ B) z)
    = ((1 : Matrix m m 𝕜) ⊗ₖ B) *ᵥ WithLp.ofLp z from rfl, hfib i j]
  rfl

/-- The quadratic form of a Kronecker sum splits into the quadratic form of `A` on the column
fibres plus that of `B` on the row fibres.  No eigenvector, and no diagonalizability, is
involved. -/
private theorem re_inner_kroneckerSum (A : Matrix m m 𝕜) (B : Matrix n n 𝕜)
    (z : EuclideanSpace 𝕜 (m × n)) :
    RCLike.re (inner 𝕜 (toEuclideanLin (A ⊕ₖ B) z) z)
      = (∑ j, RCLike.re (inner 𝕜 (toEuclideanLin A (colFibre z j)) (colFibre z j)))
        + ∑ i, RCLike.re (inner 𝕜 (toEuclideanLin B (rowFibre z i)) (rowFibre z i)) := by
  rw [kroneckerSum_def, map_add, LinearMap.add_apply, inner_add_left, map_add,
    inner_kronecker_one_left, inner_one_kronecker_right, map_sum, map_sum]

/-- Coercivity constants add under a Kronecker sum. -/
theorem isCoerciveWith_kroneckerSum {A : Matrix m m 𝕜} {B : Matrix n n 𝕜} {c₁ c₂ : ℝ}
    (hA : (toEuclideanLin A).IsCoerciveWith c₁) (hB : (toEuclideanLin B).IsCoerciveWith c₂) :
    (toEuclideanLin (A ⊕ₖ B)).IsCoerciveWith (c₁ + c₂) := by
  intro z
  rw [re_inner_kroneckerSum, add_mul]
  refine add_le_add ?_ ?_
  · rw [norm_sq_eq_sum_colFibre z, Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => hA (colFibre z j)
  · rw [norm_sq_eq_sum_rowFibre z, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => hB (rowFibre z i)

/-- Quadratic-form bounds add under a Kronecker sum: this is the form in which a
two-dimensional model problem enters every convergence estimate, and it names no eigenvalue. -/
theorem isSymmetricBoundedBy_kroneckerSum {A : Matrix m m 𝕜} {B : Matrix n n 𝕜}
    {a₁ b₁ a₂ b₂ : ℝ} (hA : (toEuclideanLin A).IsSymmetricBoundedBy a₁ b₁)
    (hB : (toEuclideanLin B).IsSymmetricBoundedBy a₂ b₂) :
    (toEuclideanLin (A ⊕ₖ B)).IsSymmetricBoundedBy (a₁ + a₂) (b₁ + b₂) := by
  refine ⟨isSymmetric_toEuclideanLin_iff.2 (isHermitian_kroneckerSum
    (isSymmetric_toEuclideanLin_iff.1 hA.isSymmetric)
    (isSymmetric_toEuclideanLin_iff.1 hB.isSymmetric)), fun z => ?_, fun z => ?_⟩
  · exact isCoerciveWith_kroneckerSum hA.isCoerciveWith hB.isCoerciveWith z
  · rw [re_inner_kroneckerSum, add_mul]
    refine add_le_add ?_ ?_
    · rw [norm_sq_eq_sum_colFibre z, Finset.mul_sum]
      exact Finset.sum_le_sum fun j _ => hA.re_inner_le (colFibre z j)
    · rw [norm_sq_eq_sum_rowFibre z, Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ => hB.re_inner_le (rowFibre z i)

end RCLike

open scoped ComplexOrder in
/-- The Kronecker sum of two positive definite matrices is positive definite. -/
theorem posDef_kroneckerSum {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Finite m] [Finite n]
    [DecidableEq m] [DecidableEq n] {A : Matrix m m 𝕜} {B : Matrix n n 𝕜} (hA : A.PosDef)
    (hB : B.PosDef) : (A ⊕ₖ B).PosDef := by
  have := Fintype.ofFinite m
  have := Fintype.ofFinite n
  rw [posDef_iff_isSymmetricCoercive] at hA hB ⊢
  obtain ⟨c₁, hc₁, hA'⟩ := hA.isCoercive
  obtain ⟨c₂, hc₂, hB'⟩ := hB.isCoercive
  exact ⟨isSymmetric_toEuclideanLin_iff.2 (isHermitian_kroneckerSum
      (isSymmetric_toEuclideanLin_iff.1 hA.isSymmetric)
      (isSymmetric_toEuclideanLin_iff.1 hB.isSymmetric)),
    c₁ + c₂, by linarith, isCoerciveWith_kroneckerSum hA' hB'⟩

end Matrix
