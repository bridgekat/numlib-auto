import Numlib.LinearAlgebra.Matrix.Schur
import NumlibSurface.QuarteroniSaccoSaleri.Chapter05.Section07

/-!
# Quarteroni–Sacco–Saleri §5.8: computing the eigenvectors and the SVD of a matrix

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*
[quarteroni2000numerical], §5.8, over the backbone `Numlib/Eigen/PowerMethod` (inverse iteration
commutes with a unitary change of coordinates), `Numlib/LinearAlgebra/Matrix/Schur` (the eigenvector
of a simple eigenvalue read off the Schur form, and similarity moving eigenvectors) and
`Numlib/LinearAlgebra/Matrix/QR` (the Golub–Kahan bidiagonalization), and over §5.3's inverse
iteration `inverseIterate`.

## Conventions

The Hessenberg inverse iteration of §5.8.1 is stated for the inverse iteration (5.28) of §5.3,
over any `RCLike` field as there, with `H = Qᴴ A Q` for a unitary `Q` (orthogonal and `Qᵀ` in the
book's real setting). The Schur form of §5.8.2 is complex, `T ∈ ℂ^{n×n}` upper triangular, and the
vector `y` of (5.56) is the backbone's `Matrix.IsUpperTriangular.schurEigenvector T k`, with the
leading block `T₁₁ = T.submatrix (Fin.castLE _) (Fin.castLE _)` of order `k`. The bidiagonalization
(5.57) is real, for `A ∈ ℝ^{m×n}` with `m ≥ n`; "upper bidiagonal" is `Matrix.IsUpperBidiagonal`.

## Contents

* `inverseIterate_conj` — §5.8.1: inverse iteration on `H = Qᴴ A Q` from `Qᴴ q⁽⁰⁾` is `Qᴴ` of the
  iteration on `A`, so `x = Q q`.
* `equation_5_56` — §5.8.2: the eigenvector of a simple eigenvalue from the Schur form, and its
  transport `x = Q y` to `A`.
* `equation_5_57` — §5.8.3: the Golub–Kahan bidiagonalization `𝒰ᵀ A 𝒱 = (B; 0)`.

## Readings

The iterative phase of the Golub–Kahan–Reinsch algorithm (§5.8.3) is described only by its limit,
whose existence is the SVD itself, and its rounding-error bound `‖δA‖₂ ≤ C_{mn} u ‖A‖₂` is quoted
without proof; neither is formalized (`golubKahan_svd`). Inverse iteration needs `λ ∉ σ(A)` for
its linear systems to be solvable, which `inverseIterate_conj` assumes, as (5.28) does.
-/

open Matrix

namespace QuarteroniSaccoSaleri.Chapter05

variable {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]

/-! ### §5.8.1: the Hessenberg inverse iteration -/

/-- **§5.8.1, the Hessenberg inverse iteration.** Let `H = Qᴴ A Q` with `Q` unitary (the
Hessenberg form of `A`, `Qᵀ A Q` for a real orthogonal `Q`), let `λ ∉ σ(A)` be an approximate
eigenvalue, and let `q⁽⁰⁾` be a unit vector. Then the inverse iteration (5.28) applied to `H` from
`Qᴴ q⁽⁰⁾` produces the vectors `Qᴴ q⁽ᵏ⁾`, `q⁽ᵏ⁾` being the inverse iterates of `A` from `q⁽⁰⁾`; so
the approximate eigenvector `q` of `H` gives the eigenvector `x = Q q` of `A`. Backbone
`Krylov.inverseIterate_conj_linearIsometryEquiv`, through `inverseIterate_eq_krylov` on both
sides. -/
theorem inverseIterate_conj {A Q : Matrix (Fin n) (Fin n) 𝕜}
    (hQ : Q ∈ Matrix.unitaryGroup (Fin n) 𝕜) {μ : 𝕜} (hμ : μ ∉ spectrum 𝕜 A)
    {q₀ : EuclideanSpace 𝕜 (Fin n)} (hq₀ : ‖q₀‖ = 1) (k : ℕ) :
    inverseIterate (Qᴴ * A * Q) μ (toEuclideanLin Qᴴ q₀) k =
      toEuclideanLin Qᴴ (inverseIterate A μ q₀ k) := by
  set U := unitaryLinearIsometryEquiv hQ with hU
  have hμ' : μ ∉ spectrum 𝕜 (Qᴴ * A * Q) := by rwa [spectrum_conjTranspose_mul_mul hQ]
  have hq₀' : ‖toEuclideanLin Qᴴ q₀‖ = 1 := by
    rw [← unitaryLinearIsometryEquiv_symm_apply hQ, LinearIsometryEquiv.norm_map, hq₀]
  have hconj : U.symm.toLinearEquiv.conj (toEuclideanLin A) = toEuclideanLin (Qᴴ * A * Q) := by
    refine LinearMap.ext fun x => ?_
    rw [LinearEquiv.conj_apply_apply, toEuclideanLin_mul_apply, toEuclideanLin_mul_apply]
    change U.symm (toEuclideanLin A (U.symm.symm x)) = _
    rw [LinearIsometryEquiv.symm_symm, hU, unitaryLinearIsometryEquiv_symm_apply,
      unitaryLinearIsometryEquiv_apply]
  rw [inverseIterate_eq_krylov hμ' hq₀' k, inverseIterate_eq_krylov hμ hq₀ k, ← hconj,
    ← unitaryLinearIsometryEquiv_symm_apply hQ, ← unitaryLinearIsometryEquiv_symm_apply hQ]
  exact Krylov.inverseIterate_conj_linearIsometryEquiv U (toEuclideanLin A) μ q₀ k

/-! ### §5.8.2: eigenvectors from the Schur form -/

/-- **§5.8.2, (5.56): the eigenvector of a simple eigenvalue from the Schur form.** Let
`T ∈ ℂ^{n×n}` be upper triangular (the Schur form `Qᴴ A Q = T` of `A`) and let `λ = t_kk` be a
simple eigenvalue, `t_ii ≠ λ` for `i ≠ k`. Partition `T = [T₁₁ v T₁₃; 0 λ wᵀ; 0 0 T₃₃]` around
row `k`. Then the vector `y = (−(T₁₁ − λI)⁻¹ v, 1, 0)` — `y_k = 1`, `y_i = 0` for `i > k`, and the
leading entries the solution of the triangular system `(T₁₁ − λI) y₁ = −v` of (5.56) — is a nonzero
eigenvector of `T` for `λ`, `T y = λ y`; and for `A = Q T Qᴴ` with `Q` unitary, `x = Q y` is an
eigenvector of `A` for `λ`. Backbone `Matrix.IsUpperTriangular.mulVec_schurEigenvector` (which
needs only `t_ii ≠ λ` for `i < k`) and `Matrix.mulVec_conj_eq_smul_of_mulVec_eq_smul`. -/
theorem equation_5_56 {T : Matrix (Fin n) (Fin n) ℂ} (hT : T.IsUpperTriangular) {k : Fin n}
    (hk : ∀ i, i ≠ k → T i i ≠ T k k) :
    let y := IsUpperTriangular.schurEigenvector T k
    y k = 1 ∧ (∀ i, k < i → y i = 0) ∧
      (∀ (i : Fin n) (h : (i : ℕ) < k), y i =
        -(((T.submatrix (Fin.castLE k.isLt.le) (Fin.castLE k.isLt.le) - T k k • 1)⁻¹ *ᵥ
          fun j => T (Fin.castLE k.isLt.le j) k) ⟨i, h⟩)) ∧
      T *ᵥ y = T k k • y ∧ y ≠ 0 ∧
      ∀ Q : Matrix (Fin n) (Fin n) ℂ, Q ∈ Matrix.unitaryGroup (Fin n) ℂ →
        (Q * T * Qᴴ) *ᵥ (Q *ᵥ y) = T k k • (Q *ᵥ y) := by
  intro y
  have hy : T *ᵥ y = T k k • y :=
    hT.mulVec_schurEigenvector fun i hi => hk i hi.ne
  refine ⟨IsUpperTriangular.schurEigenvector_apply_self T k,
    fun i hi => IsUpperTriangular.schurEigenvector_apply_of_lt T hi, fun i h => ?_, hy,
    IsUpperTriangular.schurEigenvector_ne_zero T k, fun Q hQ => ?_⟩
  · change (if h : (i : ℕ) < k then _ else _) = _
    rw [dite_eq_left h]
  · have hQQ : Q * Qᴴ = 1 := by rw [← star_eq_conjTranspose]; exact mem_unitaryGroup_iff.mp hQ
    have hu : IsUnit Qᴴ :=
      isUnit_of_mem_unitaryGroup (by rw [← star_eq_conjTranspose]; exact Unitary.star_mem hQ)
    have hinv : (Qᴴ)⁻¹ = Q := inv_eq_left_inv hQQ
    have h := mulVec_conj_eq_smul_of_mulVec_eq_smul hu hy
    rwa [hinv] at h

/-! ### §5.8.3: the Golub–Kahan bidiagonalization -/

/-- **§5.8.3, (5.57): the Golub–Kahan bidiagonalization**, the direct phase of the
Golub–Kahan–Reinsch algorithm. For `A ∈ ℝ^{m×n}` with `m ≥ n` there are orthogonal matrices
`𝒰 ∈ ℝ^{m×m}` and `𝒱 ∈ ℝ^{n×n}` such that `𝒰ᵀ A 𝒱 = (B; 0)`: the rows `n, …, m − 1` of `𝒰ᵀ A 𝒱`
vanish and its leading `n × n` block `B` is upper bidiagonal. Backbone
`Matrix.exists_orthogonal_mul_mul_orthogonal_isUpperBidiagonal`, by `n + m − 3` Householder
reflectors alternating on the two sides. -/
theorem equation_5_57 {m : ℕ} (h : n ≤ m) (A : Matrix (Fin m) (Fin n) ℝ) :
    ∃ U ∈ Matrix.orthogonalGroup (Fin m) ℝ, ∃ V ∈ Matrix.orthogonalGroup (Fin n) ℝ,
      (∀ (i : Fin m) (j : Fin n), n ≤ (i : ℕ) → (Uᵀ * A * V) i j = 0) ∧
        ((Uᵀ * A * V).submatrix (Fin.castLE h) id).IsUpperBidiagonal := by
  obtain ⟨U, hU, V, hV, h0, hB⟩ := exists_orthogonal_mul_mul_orthogonal_isUpperBidiagonal h A
  rw [conjTranspose_eq_transpose_of_trivial] at h0 hB
  exact ⟨U, hU, V, hV, h0, hB⟩

end QuarteroniSaccoSaleri.Chapter05
