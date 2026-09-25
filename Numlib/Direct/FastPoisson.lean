import Numlib.LinearAlgebra.Matrix.KroneckerSum
import Numlib.LinearAlgebra.Matrix.Sylvester

/-!
# The fast Poisson solver framework

The discretized Poisson equation on a rectangle, and every separable problem of the same shape, is
a linear system with a Kronecker-sum matrix, `(I_{n₂} ⊗ A₁ + A₂ ⊗ I_{n₁}) vec U = vec B`
([golub2013matrix] §4.8.3–4.8.7; Van Loan, *Computational Frameworks for the Fast Fourier
Transform*, §4.3–4.5). When `A₁ = V diag(ν) V⁻¹` and `A₂ = W diag(μ) W⁻¹`, the system decouples in
the eigenvector bases: with `Ũ = V⁻¹ U W⁻ᵀ` and `B̃ = V⁻¹ B W⁻ᵀ` it reads
`diag(ν) Ũ + Ũ diag(μ) = B̃`, solved entrywise by `ũ_ij = b̃_ij / (ν_i + μ_j)`
(`FastPoisson.kroneckerSum_mulVec_vec_eq_iff`). This is the specification that the fast Poisson
solvers of the surface (Algorithm 4.8.2 and its variants) are proved against; the fast transforms
that apply `V`, `W` and their inverses are what makes them fast, and the operation counts are not
formalized.

## Design

Nothing is re-derived here. The Kronecker sum `A₂ ⊕ₖ A₁` acting on Mathlib's column-major
`Matrix.vec` is the Sylvester-type map `U ↦ A₁ U + U A₂ᵀ` (`Matrix.kroneckerSum_mulVec_vec`); the
change of basis is `Matrix.sylvesterMap_conj`, and the diagonal solve is
`Matrix.sylvesterMap_diagonal_eq_iff`, both of `Numlib.LinearAlgebra.Matrix.Sylvester`.

The second-difference matrices `𝒯^{(DD)}`, `𝒯^{(DN)}`, `𝒯^{(NN)}`, `𝒯^{(P)}` that make up the model
problems, and their eigensystems (the sine and cosine transforms, the discrete Fourier transform),
are backbone matrix vocabulary: `Matrix.symmTridiagonalToeplitz`, `Matrix.secondDifferenceDN`,
`Matrix.secondDifferenceNN`, `Matrix.secondDifferencePeriodic` in
`Numlib.LinearAlgebra.Matrix.TridiagonalToeplitz`, the transforms `Matrix.dst1`, `Matrix.dst2`,
`Matrix.dct1` in `Numlib.Analysis.Fourier.SineCosineTransform` and the circulant diagonalization in
`Numlib.Analysis.Fourier.Circulant`.

## Main statements

* `FastPoisson.kroneckerSum_mulVec_vec_eq_iff`: the solution formula.
* `FastPoisson.isUnit_kroneckerSum`: the Kronecker sum is then nonsingular.

## References

* [golub2013matrix] §4.8.
-/

open scoped Kronecker

namespace FastPoisson

open Matrix

variable {K : Type*} [Field K] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
  [DecidableEq n]

/-- The eigenvector change of basis turns `A₁ U + U A₂ᵀ` into the diagonal Sylvester operator:
`V⁻¹ (A₁ U + U A₂ᵀ) W⁻ᵀ = diag(ν) Ũ + Ũ diag(μ)` with `Ũ = V⁻¹ U W⁻ᵀ`. -/
private theorem sylvesterMap_diagonal_conj {A₁ : Matrix m m K} {A₂ : Matrix n n K}
    {V : Matrix m m K} {W : Matrix n n K} (hV : IsUnit V) (hW : IsUnit W) {ν : m → K}
    {μ : n → K} (hA₁ : V⁻¹ * A₁ * V = diagonal ν) (hA₂ : W⁻¹ * A₂ * W = diagonal μ)
    (U : Matrix m n K) :
    sylvesterMap (diagonal ν) (diagonal (-μ)) (V⁻¹ * U * W⁻¹ᵀ) =
      V⁻¹ * (A₁ * U + U * A₂ᵀ) * W⁻¹ᵀ := by
  have hVd : IsUnit V.det := (isUnit_iff_isUnit_det V).mp hV
  have hWd : IsUnit W.det := (isUnit_iff_isUnit_det W).mp hW
  have hWt : IsUnit Wᵀ := (isUnit_iff_isUnit_det _).mpr (by rwa [det_transpose])
  have key := sylvesterMap_conj (isUnit_nonsing_inv_iff.mpr hV) hWt A₁ (-A₂ᵀ) U
  rw [nonsing_inv_nonsing_inv V hVd, hA₁, ← transpose_nonsing_inv] at key
  have h2 : Wᵀ * -A₂ᵀ * W⁻¹ᵀ = diagonal (-μ) := by
    rw [Matrix.mul_neg, Matrix.neg_mul, ← transpose_mul, ← transpose_mul, ← Matrix.mul_assoc,
      hA₂, diagonal_transpose, diagonal_neg]
    rfl
  rw [h2] at key
  rw [key, sylvesterMap_apply, Matrix.mul_neg, sub_neg_eq_add]

/-- **The fast Poisson solver framework** ([golub2013matrix] §4.8.4, the specification of
Algorithm 4.8.2). Let `V`, `W` be nonsingular with `V⁻¹ A₁ V = diag(ν)` and `W⁻¹ A₂ W = diag(μ)`
((4.8.13)–(4.8.14)), and `ν i + μ j ≠ 0` for all `i`, `j`. Then
`(A₂ ⊕ₖ A₁) vec U = vec B` iff `U = V Ũ Wᵀ` with `ũ_ij = (V⁻¹ B W⁻ᵀ)_ij / (ν_i + μ_j)`. -/
theorem kroneckerSum_mulVec_vec_eq_iff {A₁ : Matrix m m K} {A₂ : Matrix n n K}
    {V : Matrix m m K} {W : Matrix n n K} (hV : IsUnit V) (hW : IsUnit W) {ν : m → K}
    {μ : n → K} (hA₁ : V⁻¹ * A₁ * V = diagonal ν) (hA₂ : W⁻¹ * A₂ * W = diagonal μ)
    (hνμ : ∀ i j, ν i + μ j ≠ 0) (U B : Matrix m n K) :
    (A₂ ⊕ₖ A₁) *ᵥ vec U = vec B ↔
      U = V * (of fun i j => (V⁻¹ * B * W⁻¹ᵀ) i j / (ν i + μ j)) * Wᵀ := by
  have hVd : IsUnit V.det := (isUnit_iff_isUnit_det V).mp hV
  have hWd : IsUnit W.det := (isUnit_iff_isUnit_det W).mp hW
  have hWW : W⁻¹ᵀ * Wᵀ = 1 := by rw [← transpose_mul, mul_nonsing_inv W hWd, transpose_one]
  have hWW' : Wᵀ * W⁻¹ᵀ = 1 := by rw [← transpose_mul, nonsing_inv_mul W hWd, transpose_one]
  have hne : ∀ i j, ν i ≠ (-μ) j := fun i j h => hνμ i j (by rw [h, Pi.neg_apply, neg_add_cancel])
  rw [kroneckerSum_mulVec_vec, vec_inj]
  -- conjugate both sides by the invertible `V⁻¹ · W⁻ᵀ`
  have hconj : ∀ X Y : Matrix m n K, X = Y ↔ V⁻¹ * X * W⁻¹ᵀ = V⁻¹ * Y * W⁻¹ᵀ := by
    intro X Y
    refine ⟨fun h => h ▸ rfl, fun h => ?_⟩
    have := congrArg (fun Z => V * Z * Wᵀ) h
    simp only [← Matrix.mul_assoc, mul_nonsing_inv V hVd, Matrix.one_mul] at this
    simpa only [Matrix.mul_assoc, hWW, Matrix.mul_one] using this
  rw [hconj, ← sylvesterMap_diagonal_conj hV hW hA₁ hA₂, sylvesterMap_diagonal_eq_iff hne,
    hconj U]
  have hU : V⁻¹ * (V * (of fun i j => (V⁻¹ * B * W⁻¹ᵀ) i j / (ν i + μ j)) * Wᵀ) * W⁻¹ᵀ =
      of fun i j => (V⁻¹ * B * W⁻¹ᵀ) i j / (ν i + μ j) := by
    simp only [← Matrix.mul_assoc, nonsing_inv_mul V hVd, Matrix.one_mul]
    simp only [Matrix.mul_assoc, hWW', Matrix.mul_one]
  rw [hU]
  simp only [Pi.neg_apply, sub_neg_eq_add]

/-- Under the hypotheses of `FastPoisson.kroneckerSum_mulVec_vec_eq_iff` the Kronecker sum
`A₂ ⊕ₖ A₁` is nonsingular: every `vec B` is attained. -/
theorem isUnit_kroneckerSum {A₁ : Matrix m m K} {A₂ : Matrix n n K}
    {V : Matrix m m K} {W : Matrix n n K} (hV : IsUnit V) (hW : IsUnit W) {ν : m → K}
    {μ : n → K} (hA₁ : V⁻¹ * A₁ * V = diagonal ν) (hA₂ : W⁻¹ * A₂ * W = diagonal μ)
    (hνμ : ∀ i j, ν i + μ j ≠ 0) : IsUnit (A₂ ⊕ₖ A₁) := by
  refine mulVec_surjective_iff_isUnit.mp fun w => ?_
  obtain ⟨B, rfl⟩ := vec_bijective.2 w
  exact ⟨_, (kroneckerSum_mulVec_vec_eq_iff hV hW hA₁ hA₂ hνμ _ B).2 rfl⟩

end FastPoisson
