import Numlib.Eigen.Pencil
import NumlibSurface.QuarteroniSaccoSaleri.Chapter03.Section04
import NumlibSurface.QuarteroniSaccoSaleri.Chapter05.Section05

/-!
# Quarteroni–Sacco–Saleri §5.9: the generalized eigenvalue problem

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*
[quarteroni2000numerical], §5.9, over the backbone `Numlib/Eigen/Pencil` (matrix pencils, their
characteristic polynomial, regularity, the eigenvalue at infinity, the generalized Schur
decomposition and the simultaneous diagonalization of a symmetric-definite pencil) and
`Numlib/LinearAlgebra/Matrix/Complexify` (the complex eigenvalues of a real pencil).

## Conventions

The pencil `(A, B)` of `A, B ∈ ℂ^{n×n}` is the pair of matrices; its spectrum
`σ(A, B) = {μ ∈ ℂ : det (A − μ B) = 0}` is `pencilSpectrum A B`, written for matrices over any
field so that the real pencil of Theorem 5.7 has both a real and a complex spectrum, and it is
the backbone's `Matrix.pencilSpectrum` by definition. The pencil is *regular* (`isRegularPencil`)
when `det (A − z B)` is not identically zero — some `z` has `det (A − z B) ≠ 0` — which is the
backbone's `Matrix.IsRegularPencil`, nonvanishing of the characteristic polynomial
`p = Matrix.pencilPoly A B`; the eigenvalue `∞` of a regular pencil has multiplicity
`n − deg p = Matrix.pencilInftyMultiplicity A B`. The book's `Uᴴ` is `Uᴴ`, its `Xᵀ` is `Xᵀ`, a
positive definite `B` is `Matrix.PosDef`.

## Contents

* `pencilSpectrum`, `equation_5_58`, `pencilSpectrum_one`, `isRegularPencil`,
  `isRegularPencil_iff`, `pencilCharpoly` — the definitions of §5.9.
* `example_5_14_conj`, `example_5_14_infty`, `example_5_14_singular` — the three pencils of
  Example 5.14.
* `pencilSpectrum_eq_spectrum_of_isUnit` — §5.9.1, `n` finite eigenvalues iff `B` is nonsingular,
  and then `σ(A, B) = σ(C)` for the solution `C` of `B C = A`.
* `property_5_10` — the generalized Schur decomposition.
* `generalizedRealSchur_of_isUnit` — the generalized *real* Schur form, for a nonsingular `B`.
* `theorem_5_7`, `theorem_5_7_eigenvectors` — symmetric-definite pencils.

## Not formalized

The generalized *real* Schur form stated after Property 5.10 for an arbitrary regular pencil
(`generalizedRealSchur`): the case of a nonsingular `B` is `generalizedRealSchur_of_isUnit`,
proved here the way the book's own QZ sketch proceeds, but for a singular `B` there is no `B⁻¹ A`
to take the real Schur form of. Also the rounding-error statement after the QR–Cholesky algorithm
(`qrCholesky_stability`), a floating-point claim the book quotes without proof; both stay open
nodes of the plan with the reason. The QZ iteration and the QR–Cholesky algorithm are described
without a theorem and are not nodes.
-/

open Finset Matrix Polynomial

namespace QuarteroniSaccoSaleri.Chapter05

variable {n : ℕ}

/-! ### The pencil, its spectrum, regularity -/

/-- **§5.9, the spectrum of a pencil.** For `A, B ∈ ℂ^{n×n}` (here: over any field) and `z ∈ ℂ`,
`A − z B` is the matrix pencil `(A, B)`, and the set of its eigenvalues is
`σ(A, B) = {μ ∈ ℂ : det (A − μ B) = 0}`. This is the backbone's `Matrix.pencilSpectrum A B` by
definition. -/
def pencilSpectrum {K : Type*} [Field K] (A B : Matrix (Fin n) (Fin n) K) : Set K :=
  {μ | (A - μ • B).det = 0}

/-- **(5.58).** The generalized eigenvalue problem: `λ ∈ σ(A, B)` exactly when there is a nonnull
`x ∈ ℂⁿ` with `A x = λ B x`; such a pair `(λ, x)` is an eigenvalue/eigenvector pair of the pencil
(`Matrix.HasPencilEigenvector`). Backbone `Matrix.mem_pencilSpectrum_iff_exists`. -/
theorem equation_5_58 {K : Type*} [Field K] (A B : Matrix (Fin n) (Fin n) K) (μ : K) :
    μ ∈ pencilSpectrum A B ↔ ∃ x : Fin n → K, x ≠ 0 ∧ A *ᵥ x = μ • (B *ᵥ x) :=
  Matrix.mem_pencilSpectrum_iff_exists A B μ

/-- Setting `B = Iₙ` in (5.58) recovers the standard eigenvalue problem: `σ(A, I) = σ(A)`.
Backbone `Matrix.pencilSpectrum_one`. -/
theorem pencilSpectrum_one {K : Type*} [Field K] (A : Matrix (Fin n) (Fin n) K) :
    pencilSpectrum A 1 = spectrum K A :=
  Matrix.pencilSpectrum_one A

/-- **§5.9, regular pencils.** The pencil `(A, B)` is *regular* if `det (A − z B)` is not
identically zero — some `z ∈ ℂ` has `det (A − z B) ≠ 0` — and *singular* otherwise. -/
def isRegularPencil (A B : Matrix (Fin n) (Fin n) ℂ) : Prop := ∃ z : ℂ, (A - z • B).det ≠ 0

/-- Regularity in the book's words agrees with the backbone's `Matrix.IsRegularPencil`, the
nonvanishing of the polynomial `p(z) = det (A − z B)` (`Matrix.pencilPoly A B`): a nonzero
polynomial over the infinite field `ℂ` has a non-root, and a root of `p` at `z` is
`det (A − z B) = 0` (`Matrix.pencilPoly_eval`). -/
theorem isRegularPencil_iff (A B : Matrix (Fin n) (Fin n) ℂ) :
    isRegularPencil A B ↔ Matrix.IsRegularPencil A B := by
  simp only [isRegularPencil, Matrix.IsRegularPencil, ← Matrix.pencilPoly_eval]
  constructor
  · rintro ⟨z, hz⟩ h
    exact hz (by rw [h, eval_zero])
  · intro h
    by_contra hc
    refine h (Polynomial.eq_zero_of_infinite_isRoot _ ?_)
    have hall : ∀ z : ℂ, (Matrix.pencilPoly A B).IsRoot z := fun z => by
      by_contra hz
      exact hc ⟨z, hz⟩
    rw [show {x | (Matrix.pencilPoly A B).IsRoot x} = Set.univ from Set.eq_univ_of_forall hall]
    exact Set.infinite_univ

/-- **§5.9, the characteristic polynomial of a regular pencil and the eigenvalue `∞`.** For a
regular pencil `(A, B)`, `p(z) = det (A − z B)` is its characteristic polynomial
(`Matrix.pencilPoly A B`, evaluated by `Matrix.pencilPoly_eval`); with `k = deg p`, the
eigenvalues of `(A, B)` are the roots of `p` (if `k = n`, all of them are finite), and `∞` with
multiplicity `n − k` if `k < n` (`Matrix.pencilInftyMultiplicity A B`). Backbone
`Matrix.mem_pencilSpectrum_iff_isRoot`, `Matrix.natDegree_pencilPoly_le`. -/
theorem pencilCharpoly {A B : Matrix (Fin n) (Fin n) ℂ} (_h : isRegularPencil A B) :
    (∀ z, (Matrix.pencilPoly A B).eval z = (A - z • B).det) ∧
      (∀ μ, μ ∈ pencilSpectrum A B ↔ (Matrix.pencilPoly A B).IsRoot μ) ∧
      (Matrix.pencilPoly A B).natDegree ≤ n ∧
      Matrix.pencilInftyMultiplicity A B = n - (Matrix.pencilPoly A B).natDegree :=
  ⟨Matrix.pencilPoly_eval A B, Matrix.mem_pencilSpectrum_iff_isRoot A B,
    by simpa using Matrix.natDegree_pencilPoly_le A B,
    by rw [Matrix.pencilInftyMultiplicity, Fintype.card_fin]⟩

/-! ### Example 5.14 -/

/-- **Example 5.14, first pencil.** `A = [[−1, 0], [0, 1]]`, `B = [[0, 1], [1, 0]]`:
`p(z) = det (A − z B) = −(z² + 1)` (the book prints `z² + 1`, the same up to sign), so
`σ(A, B) = {±i}` — a symmetric pencil, unlike a symmetric matrix, may have complex conjugate
eigenvalues. -/
theorem example_5_14_conj :
    Matrix.pencilPoly (!![-1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ) !![0, 1; 1, 0] = -(X ^ 2 + 1) ∧
      pencilSpectrum (!![-1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ) !![0, 1; 1, 0] =
        {Complex.I, -Complex.I} := by
  refine ⟨?_, ?_⟩
  · simp [Matrix.pencilPoly, Matrix.det_fin_two]
    ring
  · ext μ
    simp only [pencilSpectrum, Set.mem_ofPred_eq, Matrix.det_fin_two, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, smul_eq_mul]
    rw [← sq_eq_sq_iff_eq_or_eq_neg, Complex.I_sq]
    constructor <;> intro h <;> linear_combination -h

/-- **Example 5.14, second pencil.** `A = [[−1, 0], [0, 0]]`, `B = [[0, 0], [0, 1]]`: `p(z) = z`,
so the pencil is regular of degree `1 < 2`, `σ(A, B) = {0}` and `∞` is an eigenvalue of
multiplicity `1`: `σ(A, B) = {0, ∞}`. -/
theorem example_5_14_infty :
    Matrix.pencilPoly (!![-1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) !![0, 0; 0, 1] = X ∧
      isRegularPencil (!![-1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) !![0, 0; 0, 1] ∧
      pencilSpectrum (!![-1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) !![0, 0; 0, 1] = {0} ∧
      Matrix.pencilInftyMultiplicity (!![-1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) !![0, 0; 0, 1]
        = 1 := by
  have hp : Matrix.pencilPoly (!![-1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) !![0, 0; 0, 1] = X := by
    simp [Matrix.pencilPoly, Matrix.det_fin_two]
  refine ⟨hp, (isRegularPencil_iff _ _).mpr (by rw [Matrix.IsRegularPencil, hp]; exact X_ne_zero),
    ?_, ?_⟩
  · ext μ
    rw [pencilSpectrum, Set.mem_ofPred_eq, ← Matrix.pencilPoly_eval, hp, eval_X]
    rfl
  · rw [Matrix.pencilInftyMultiplicity, hp, natDegree_X, Fintype.card_fin]

/-- **Example 5.14, third pencil.** `A = [[1, 2], [0, 0]]`, `B = [[1, 0], [0, 0]]`: `p(z) = 0`,
so the pencil is singular and `σ(A, B) = ℂ`. Backbone
`Matrix.pencilSpectrum_eq_univ_of_not_isRegularPencil`. -/
theorem example_5_14_singular :
    Matrix.pencilPoly (!![1, 2; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) !![1, 0; 0, 0] = 0 ∧
      ¬ isRegularPencil (!![1, 2; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) !![1, 0; 0, 0] ∧
      pencilSpectrum (!![1, 2; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) !![1, 0; 0, 0] = Set.univ := by
  have hp : Matrix.pencilPoly (!![1, 2; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) !![1, 0; 0, 0] = 0 := by
    simp [Matrix.pencilPoly, Matrix.det_fin_two]
  have hreg : ¬ Matrix.IsRegularPencil (!![1, 2; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) !![1, 0; 0, 0] :=
    fun h => h hp
  exact ⟨hp, fun h => hreg ((isRegularPencil_iff _ _).mp h),
    Matrix.pencilSpectrum_eq_univ_of_not_isRegularPencil hreg⟩

/-! ### §5.9.1: reduction to a standard problem, the generalized Schur form -/

/-- **§5.9.1.** The pencil `(A, B)` has `n` finite eigenvalues — its characteristic polynomial has
degree `n` — iff `B` is nonsingular, and then problem (5.58) is equivalent to the standard
eigenvalue problem `C x = λ x` for the solution `C` of `B C = A`: `σ(A, B) = σ(C)`. Backbone
`Matrix.natDegree_pencilPoly_eq_card_iff` and `Matrix.pencilSpectrum_eq_spectrum_of_isUnit`. -/
theorem pencilSpectrum_eq_spectrum_of_isUnit (A B : Matrix (Fin n) (Fin n) ℂ) :
    ((Matrix.pencilPoly A B).natDegree = n ↔ IsUnit B) ∧
      (IsUnit B → ∀ C, B * C = A → pencilSpectrum A B = spectrum ℂ C) := by
  refine ⟨?_, fun hB C hC => ?_⟩
  · have h := Matrix.natDegree_pencilPoly_eq_card_iff A B
    rw [Fintype.card_fin] at h
    rw [h, isUnit_iff_isUnit_det]
  · have hC' : C = B⁻¹ * A := by
      rw [← hC, ← Matrix.mul_assoc, nonsing_inv_mul B ((isUnit_iff_isUnit_det B).mp hB),
        Matrix.one_mul]
    rw [hC']
    exact Matrix.pencilSpectrum_eq_spectrum_of_isUnit A hB

/-- **Property 5.10 (Generalized Schur decomposition).** Let `(A, B)` be a regular pencil. Then
there are two unitary matrices `U` and `Z` such that `Uᴴ A Z = T` and `Uᴴ B Z = S` are upper
triangular, and for `i = 1, …, n` the eigenvalues of `(A, B)` are `λ_i = t_ii / s_ii` if
`s_ii ≠ 0` and `λ_i = ∞` if `s_ii = 0` (and then `t_ii ≠ 0`): `σ(A, B)` is the set of the
quotients `t_ii / s_ii` over the indices with `s_ii ≠ 0`, and no index has `t_ii = s_ii = 0`.
Backbone `Matrix.exists_unitary_pencil_isUpperTriangular` (a Schur form and a QR factorization)
with `Matrix.pencilSpectrum_eq_of_isUpperTriangular` and
`Matrix.pencilSpectrum_mul_mul_of_isUnit`; a diagonal position with `t_ii = s_ii = 0` would make
every `μ` an eigenvalue, against the finiteness of the spectrum of a regular pencil. -/
theorem property_5_10 {A B : Matrix (Fin n) (Fin n) ℂ} (hreg : isRegularPencil A B) :
    ∃ U ∈ unitaryGroup (Fin n) ℂ, ∃ Z ∈ unitaryGroup (Fin n) ℂ,
      (Uᴴ * A * Z).IsUpperTriangular ∧ (Uᴴ * B * Z).IsUpperTriangular ∧
        pencilSpectrum A B =
          {μ | ∃ i, (Uᴴ * B * Z) i i ≠ 0 ∧ μ = (Uᴴ * A * Z) i i / (Uᴴ * B * Z) i i} ∧
        ∀ i, (Uᴴ * B * Z) i i = 0 → (Uᴴ * A * Z) i i ≠ 0 := by
  have hreg' := (isRegularPencil_iff A B).mp hreg
  obtain ⟨U, hU, Z, hZ, hT, hS⟩ := Matrix.exists_unitary_pencil_isUpperTriangular hreg'
  rw [star_eq_conjTranspose] at hT hS
  have hUs : IsUnit Uᴴ := ⟨Unitary.toUnits ⟨Uᴴ, Unitary.star_mem hU⟩, rfl⟩
  have hZu : IsUnit Z := ⟨Unitary.toUnits ⟨Z, hZ⟩, rfl⟩
  have hσ : pencilSpectrum A B = {μ | ∃ i, (Uᴴ * A * Z) i i = μ * (Uᴴ * B * Z) i i} := by
    rw [pencilSpectrum, ← Matrix.pencilSpectrum_eq_of_isUpperTriangular hT hS,
      Matrix.pencilSpectrum_mul_mul_of_isUnit A B hUs hZu]
    rfl
  have hinf : ∀ i, (Uᴴ * B * Z) i i = 0 → (Uᴴ * A * Z) i i ≠ 0 := by
    intro i hSi hTi
    have huniv : pencilSpectrum A B = Set.univ := by
      rw [hσ]
      exact Set.eq_univ_of_forall fun μ => ⟨i, by rw [hSi, hTi, mul_zero]⟩
    have hfin : (pencilSpectrum A B).Finite := hreg'.finite_pencilSpectrum
    rw [huniv] at hfin
    exact Set.infinite_univ hfin
  refine ⟨U, hU, Z, hZ, hT, hS, ?_, hinf⟩
  rw [hσ]
  ext μ
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨i, hi⟩
    have hSi : (Uᴴ * B * Z) i i ≠ 0 := fun h => hinf i h (by rw [hi, h, mul_zero])
    exact ⟨i, hSi, by rw [hi, mul_div_cancel_right₀ _ hSi]⟩
  · rintro ⟨i, hSi, rfl⟩
    exact ⟨i, by rw [div_mul_cancel₀ _ hSi]⟩

/-! ### §5.9.2: symmetric-definite pencils -/

/-- The complex spectrum of a real pencil that a real congruence carries to `(diag λ, I)`: it is
the set of the `λ_i`, read in `ℂ` (`Matrix.pencilSpectrum_mul_mul_of_isUnit` and
`Matrix.pencilSpectrum_diagonal` for the complexified matrices). The real-eigenvalue clause of
Theorem 5.7. -/
theorem pencilSpectrum_complexify_of_conj {A B X : Matrix (Fin n) (Fin n) ℝ} {lam : Fin n → ℝ}
    (hX : IsUnit X) (hA : Xᵀ * A * X = diagonal lam) (hB : Xᵀ * B * X = 1) :
    pencilSpectrum (complexify A) (complexify B) = Set.range fun i => (lam i : ℂ) := by
  have hX' : IsUnit (complexify X) := (isUnit_complexify_iff X).mpr hX
  have hXt : IsUnit (complexify X)ᵀ := (isUnit_transpose _).mpr hX'
  change Matrix.pencilSpectrum (complexify A) (complexify B) = _
  rw [← Matrix.pencilSpectrum_mul_mul_of_isUnit (complexify A) (complexify B) hXt hX',
    ← complexify_transpose, ← complexify_mul, ← complexify_mul, ← complexify_mul,
    ← complexify_mul, hA, hB, complexify_one, complexify, diagonal_map Complex.ofReal_zero,
    ← diagonal_one, Matrix.pencilSpectrum_diagonal]
  ext μ
  simp [eq_comm]

/-- **Theorem 5.7.** A symmetric-definite pencil `(A, B)` — `A`, `B` real symmetric, `B` positive
definite — has real eigenvalues and linearly independent eigenvectors, and `A` and `B` can be
simultaneously diagonalized: there is a nonsingular `X ∈ ℝ^{n×n}` with
`Xᵀ A X = Λ = diag(λ_1, …, λ_n)` and `Xᵀ B X = Iₙ`, where the `λ_i` are the eigenvalues of the
pencil `(A, B)` — its real spectrum and its complex spectrum alike are `{λ_1, …, λ_n}`. Backbone
`Matrix.exists_simultaneous_diagonalization` read over `ℝ` (the book's Cholesky factor `H` of `B`
is replaced by any `W` with `Wᵀ B W = I`), with `pencilSpectrum_complexify_of_conj` for the
complex spectrum; the eigenvector clause is `theorem_5_7_eigenvectors`. -/
theorem theorem_5_7 {A B : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) (hB : B.PosDef) :
    ∃ (X : Matrix (Fin n) (Fin n) ℝ) (lam : Fin n → ℝ), IsUnit X ∧
      Xᵀ * A * X = diagonal lam ∧ Xᵀ * B * X = 1 ∧
      pencilSpectrum A B = Set.range lam ∧
      pencilSpectrum (complexify A) (complexify B) = Set.range fun i => (lam i : ℂ) := by
  obtain ⟨X, lam, hX, hBX, hAX, hσ⟩ :=
    Matrix.exists_simultaneous_diagonalization (isHermitian_iff_isSymm.mpr hA) hB
  rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at hBX hAX
  simp only [RCLike.ofReal_real_eq_id, id] at hAX hσ
  exact ⟨X, lam, hX, hAX, hBX, hσ, pencilSpectrum_complexify_of_conj hX hAX hBX⟩

/-- **Theorem 5.7, the eigenvectors.** With `X` and `Λ = diag(λ)` as in Theorem 5.7, the columns
`x_i` of `X` are eigenvectors of the pencil, `A x_i = λ_i B x_i`, and they are linearly
independent (`X` being nonsingular). Backbone `Matrix.hasPencilEigenvector_col_of_conj_eq_diagonal`
and `Matrix.linearIndependent_cols_iff_isUnit`. -/
theorem theorem_5_7_eigenvectors {A B X : Matrix (Fin n) (Fin n) ℝ} {lam : Fin n → ℝ}
    (hX : IsUnit X) (hA : Xᵀ * A * X = diagonal lam) (hB : Xᵀ * B * X = 1) :
    (∀ i, A *ᵥ X.col i = lam i • (B *ᵥ X.col i)) ∧ LinearIndependent ℝ X.col := by
  refine ⟨fun i => ?_, linearIndependent_cols_iff_isUnit.mpr hX⟩
  have hB' : star X * B * X = 1 := by
    rwa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  have hA' : star X * A * X = diagonal lam := by
    rwa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  exact (Matrix.hasPencilEigenvector_col_of_conj_eq_diagonal hX hB' hA' i).2

/-- **The generalized real Schur form of a pencil with nonsingular `B`**, stated (without proof,
citing [GL89] §7.7) after Property 5.10: for real `A`, `B` there are orthogonal `Ŭ`, `Z̃` such that
`T̃ = Ŭᵀ A Z̃` is upper quasi-triangular and `S̃ = Ŭᵀ B Z̃` is upper triangular. As in the book's
own description of the QZ iteration, which applies the QR algorithm to `𝒜 ℬ⁻¹`, this is proved for a
nonsingular `B`: take `Z̃` from the real Schur form of `B⁻¹ A` (Property 5.8), so that
`Z̃ᵀ B⁻¹ A Z̃ = T` is quasi upper triangular, and `Ŭ` from a QR factorization `B Z̃ = Ŭ R`
(Definition 3.1); then `Ŭᵀ B Z̃ = R` is upper triangular and `Ŭᵀ A Z̃ = R T` is quasi upper
triangular, a triangular matrix times a quasi triangular one. The quasi-triangular shape is that
of Property 5.8: the blocks are the fibres of a monotone `p : Fin n → ℕ` with at most two indices
each. -/
theorem generalizedRealSchur_of_isUnit {A B : Matrix (Fin n) (Fin n) ℝ} (hB : IsUnit B.det) :
    ∃ U ∈ orthogonalGroup (Fin n) ℝ, ∃ Z ∈ orthogonalGroup (Fin n) ℝ, ∃ p : Fin n → ℕ,
      Monotone p ∧ (∀ k, #{i | p i = k} ≤ 2) ∧
        (Uᵀ * A * Z).BlockTriangular p ∧ (Uᵀ * B * Z).IsUpperTriangular := by
  obtain ⟨Z, hZ, p, hmono, hcard, htri, -⟩ := property_5_8 (B⁻¹ * A)
  obtain ⟨U, hU, R, hR, -, hBZ⟩ :=
    (Chapter03.definition_3_1_iff (B * Z)).1.1 (Chapter03.definition_3_1_iff (B * Z)).2
  have hZZ : Z * Zᵀ = 1 := (Matrix.mem_orthogonalGroup_iff _ ℝ).1 hZ
  have hUU : Uᵀ * U = 1 := (Matrix.mem_orthogonalGroup_iff' _ ℝ).1 hU
  have hkey : Uᵀ * B * Z = R := by
    rw [Matrix.mul_assoc, hBZ, ← Matrix.mul_assoc, hUU, Matrix.one_mul]
  have hRtri : R.IsUpperTriangular := fun i j hij => hR i j hij
  refine ⟨U, hU, Z, hZ, p, hmono, hcard, ?_, by rw [hkey]; exact hRtri⟩
  have hAZ : R * (Zᵀ * (B⁻¹ * A) * Z) = Uᵀ * A * Z := by
    rw [← hkey]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Z Zᵀ, hZZ, Matrix.one_mul, ← Matrix.mul_assoc B B⁻¹,
      Matrix.mul_nonsing_inv B hB, Matrix.one_mul]
  rw [← hAZ]
  refine Matrix.BlockTriangular.mul (fun i j hij => hRtri ?_) htri
  by_contra hji
  exact absurd (hmono (not_lt.1 hji)) (not_le.2 hij)

end QuarteroniSaccoSaleri.Chapter05
