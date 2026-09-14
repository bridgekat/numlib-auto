import Numlib.LinearAlgebra.Matrix.QR
import NumlibSurface.QuarteroniSaccoSaleri.Chapter05.Section04

/-!
# Quarteroni–Sacco–Saleri §5.5: the basic QR iteration

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*
[quarteroni2000numerical], §5.5, over the backbone `Numlib/Eigen/QRAlgorithm` (the convergence
theorem `Matrix.tendsto_qrIterate`, its rate `Matrix.exists_abs_qrIterate_apply_le`, the
translation `Matrix.forall_isLowerSet_disjoint_iff_isUnit_leadingPrincipal` of its general-position
hypothesis into leading principal minors, and the Hermitian invariance
`Matrix.isHermitian_qrIterate`), and over §5.4's `qrIterate`.

## Conventions

The basic QR iteration is `qrIterate` of §5.4 (`Q⁽⁰⁾ = I`, `T⁽⁰⁾ = A`). A diagonalizable
`A ∈ ℝ^{n×n}` is given, as in Theorem 5.3, by a nonsingular `X` with `X⁻¹ A X = diag(λ_1, …, λ_n)`,
the columns of `X` being the eigenvectors; the eigenvalues are indexed by `Fin n` in the order of
the book, `|λ_1| > |λ_2| > … > |λ_n|`, which is `i < j → |λ_j| < |λ_i|`. The leading principal
minor of order `m` of `X⁻¹` is the determinant of `(X⁻¹).submatrix (Fin.castLE hm) (Fin.castLE hm)`.

## Contents

* `property_5_9` — convergence of the QR iteration to triangular form, (5.36).
* `property_5_9_counterexample` — why the hypothesis the book omits is needed.
* `equation_5_37` — the rate `|t_{i,i-1}^{(k)}| = O(|λ_i/λ_{i-1}|^k)`.
* `property_5_9_symm` — the symmetric case: convergence to a diagonal matrix.
* `remark_5_2` — the LR iteration is a (nonorthogonal) similarity.

## Readings and errata

**Property 5.9 is false as printed.** With only `|λ_1| > … > |λ_n|` the matrix `A = diag(1, 2)` is
a counterexample: it is upper triangular with positive diagonal, so `Q⁽ᵏ⁾ = I` and `R⁽ᵏ⁾ = A` at
every step, the iteration leaves it fixed, and the diagonal of the "limit" is `(1, 2)` where (5.36)
demands `(λ_1, λ_2) = (2, 1)` (`property_5_9_counterexample`). Golub–Van Loan's Theorem 7.3.1,
which the book cites, also requires that `X⁻¹` have an LU factorization, that is, nonzero leading
principal minors; this is exactly the general-position hypothesis of the backbone's theorem, and
`property_5_9` carries it. The book's `|λ_n| > 0` is implicit in the statement and explicit here.
The rate (5.37) is stated with the book's base `|λ_i/λ_{i-1}|` exactly: the backbone's estimate
allows the rate parameter to equal the largest modulus among the eigenvalues after `λ_{i-1}`.
Example 5.4 is numerical and is not a node.
-/

open Filter Finset Matrix Topology

namespace QuarteroniSaccoSaleri.Chapter05

variable {N : ℕ}

/-! ### Bridges to the backbone -/

-- TODO(backbone): natural home `Numlib/Eigen/QRAlgorithm`, beside `Matrix.euclideanCol_mul`.
/-- The columns of the eigenvector matrix are eigenvectors: if `X⁻¹ A X = diag(λ)` with `X`
nonsingular then `A` sends the `j`-th column of `X` to `λ_j` times itself. -/
theorem toEuclideanLin_euclideanCol_of_conj_eq_diagonal {𝕜 : Type*} [RCLike 𝕜] {n : Type*}
    [Fintype n] [DecidableEq n] {A X : Matrix n n 𝕜} (hX : IsUnit X) {lam : n → 𝕜}
    (hD : X⁻¹ * A * X = diagonal lam) (j : n) :
    toEuclideanLin A (euclideanCol X j) = lam j • euclideanCol X j := by
  have hdet := (isUnit_iff_isUnit_det X).mp hX
  have hAX : A * X = X * diagonal lam := by
    rw [← hD, ← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_nonsing_inv X hdet, Matrix.one_mul]
  have hcol : euclideanCol (diagonal lam) j = lam j • euclideanCol (1 : Matrix n n 𝕜) j := by
    ext i
    simp [euclideanCol, diagonal_apply, one_apply]
  rw [← toEuclideanLin_euclideanCol_one, ← toEuclideanLin_mul_apply, hAX, toEuclideanLin_mul_apply,
    toEuclideanLin_euclideanCol_one, hcol, map_smul, toEuclideanLin_euclideanCol_one]

-- TODO(backbone): natural home `Numlib/Eigen/QRAlgorithm`, beside
-- `Matrix.linearIndependent_euclideanCol`.
/-- The columns of a nonsingular `n × n` matrix span `EuclideanSpace 𝕜 (Fin n)`. -/
theorem span_range_euclideanCol_eq_top {𝕜 : Type*} [RCLike 𝕜] {X : Matrix (Fin N) (Fin N) 𝕜}
    (hX : IsUnit X.det) : Submodule.span 𝕜 (Set.range (euclideanCol X)) = ⊤ :=
  (linearIndependent_euclideanCol hX).span_eq_top_of_card_eq_finrank'
    (by rw [Fintype.card_fin, finrank_euclideanSpace_fin])

/-- A matrix similar to a diagonal matrix with nonzero entries is nonsingular. -/
theorem isUnit_det_of_conj_eq_diagonal {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]
    [DecidableEq n] {A X : Matrix n n 𝕜} (hX : IsUnit X) {lam : n → 𝕜}
    (hD : X⁻¹ * A * X = diagonal lam) (hne : ∀ i, lam i ≠ 0) : IsUnit A.det := by
  have hdet := (isUnit_iff_isUnit_det X).mp hX
  have hA : A = X * diagonal lam * X⁻¹ := by
    rw [← hD, Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv X hdet, Matrix.mul_one,
      ← Matrix.mul_assoc, mul_nonsing_inv X hdet, Matrix.one_mul]
  rw [hA, det_mul, det_mul, det_diagonal, det_nonsing_inv]
  exact (hdet.mul (isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.2 fun i _ => hne i))).mul
    (Ring.inverse_unit hdet.unit ▸ hdet.unit⁻¹.isUnit)

/-- The hypotheses of Property 5.9, in the form the backbone's `Matrix.tendsto_qrIterate` takes:
the columns of `X` are a basis of eigenvectors, the eigenvalues are nonzero and strictly
decreasing in modulus, and the canonical flag is in general position with respect to them. -/
theorem property_5_9_hypotheses {A X : Matrix (Fin N) (Fin N) ℝ} (hX : IsUnit X)
    {lam : Fin N → ℝ} (hD : X⁻¹ * A * X = diagonal lam) (hne : ∀ i, lam i ≠ 0)
    (hsep : ∀ i j, i < j → |lam j| < |lam i|)
    (hminor : ∀ (m : ℕ) (hm : m ≤ N),
      IsUnit ((X⁻¹).submatrix (Fin.castLE hm) (Fin.castLE hm)).det) :
    IsUnit A.det ∧ LinearIndependent ℝ (euclideanCol X) ∧
      Submodule.span ℝ (Set.range (euclideanCol X)) = ⊤ ∧
      (∀ j, toEuclideanLin A (euclideanCol X j) = lam j • euclideanCol X j) ∧
      (∀ j k : Fin N, j < k → ‖lam k‖ < ‖lam j‖) ∧
      ∀ J : Set (Fin N), IsLowerSet J →
        Disjoint (Submodule.span ℝ (euclideanCol (1 : Matrix (Fin N) (Fin N) ℝ) '' J))
          (Submodule.span ℝ (euclideanCol X '' Jᶜ)) := by
  have hdet := (isUnit_iff_isUnit_det X).mp hX
  exact ⟨isUnit_det_of_conj_eq_diagonal hX hD hne, linearIndependent_euclideanCol hdet,
    span_range_euclideanCol_eq_top hdet, toEuclideanLin_euclideanCol_of_conj_eq_diagonal hX hD,
    fun j k h => by simpa only [Real.norm_eq_abs] using hsep j k h,
    (forall_isLowerSet_disjoint_iff_isUnit_leadingPrincipal hdet).2 hminor⟩

/-! ### Property 5.9: convergence of the QR method -/

/-- **Property 5.9 (convergence of the QR method), (5.36), with the hypothesis the book omits.**
Let `A ∈ ℝ^{n×n}` be diagonalizable, `X⁻¹ A X = diag(λ_1, …, λ_n)` with `X` nonsingular, with
`|λ_1| > |λ_2| > … > |λ_n| > 0`, and assume that every leading principal minor of `X⁻¹` is
nonzero (Golub–Van Loan Theorem 7.3.1: `X⁻¹` has an LU factorization). Then the iterates
`T⁽ᵏ⁾ = qrIterate A k` of the basic QR iteration converge to upper triangular form with the
eigenvalues in order down the diagonal: `t_{ij}^{(k)} → 0` for `i > j` and `t_{ii}^{(k)} → λ_i`.
Backbone `Matrix.tendsto_qrIterate`, whose general-position hypothesis is the minor condition by
`Matrix.forall_isLowerSet_disjoint_iff_isUnit_leadingPrincipal`. Erratum: without the minor
condition the statement is false (`property_5_9_counterexample`). -/
theorem property_5_9 {A X : Matrix (Fin N) (Fin N) ℝ} (hX : IsUnit X) {lam : Fin N → ℝ}
    (hD : X⁻¹ * A * X = diagonal lam) (hne : ∀ i, lam i ≠ 0)
    (hsep : ∀ i j, i < j → |lam j| < |lam i|)
    (hminor : ∀ (m : ℕ) (hm : m ≤ N),
      IsUnit ((X⁻¹).submatrix (Fin.castLE hm) (Fin.castLE hm)).det) :
    (∀ i j : Fin N, j < i → Tendsto (fun k => qrIterate A k i j) atTop (𝓝 0)) ∧
      ∀ i : Fin N, Tendsto (fun k => qrIterate A k i i) atTop (𝓝 (lam i)) := by
  obtain ⟨hA, hx, hxtop, heig, hsep', hgen⟩ := property_5_9_hypotheses hX hD hne hsep hminor
  simp only [qrIterate_eq]
  exact Matrix.tendsto_qrIterate hA hx hxtop heig hne hsep' hgen

/-- An upper triangular matrix with a positive diagonal is its own triangular factor, with the
identity as unitary factor: `qrQ A = 1` and `qrR A = A`, by the uniqueness of the QR
factorization (`Matrix.qr_unique`). -/
theorem qrQ_eq_one_of_isUpperTriangular {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsUpperTriangular)
    (hd : ∀ j, 0 < A j j) : qrQ A = 1 ∧ qrR A = A := by
  have hdet : IsUnit A.det := by
    rw [det_of_isUpperTriangular hA]
    exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.2 fun j _ => (hd j).ne')
  exact qr_unique (qrQ_mul_qrR A).symm (Matrix.one_mul A).symm (conjTranspose_qrQ_mul_self A)
    (by simp) (isUpperTriangular_qrR A) hA (qrR_diag_pos hdet) hd

/-- The QR iteration leaves an upper triangular matrix with a positive diagonal fixed. -/
theorem qrIterate_eq_self_of_isUpperTriangular {A : Matrix (Fin N) (Fin N) ℝ}
    (hA : A.IsUpperTriangular) (hd : ∀ j, 0 < A j j) : ∀ k, qrIterate A k = A
  | 0 => rfl
  | k + 1 => by
    rw [qrIterate, qrIterate_eq_self_of_isUpperTriangular hA hd k,
      (qrQ_eq_one_of_isUpperTriangular hA hd).1, (qrQ_eq_one_of_isUpperTriangular hA hd).2,
      Matrix.mul_one]

/-- **Why Property 5.9 needs the minor condition.** For `A = diag(1, 2)` the QR iteration is
stationary, `T⁽ᵏ⁾ = A` for every `k` (the diagonal is positive, so `qrQ A = 1` and `qrR A = A`),
and `t_{11}^{(k)} = 1` does not tend to `λ_1 = 2` as (5.36) requires, although
`|λ_1| = 2 > |λ_2| = 1 > 0`. The eigenvector matrix that orders the eigenvalues by decreasing
modulus, `X = [0 1; 1 0]` with `X⁻¹ A X = diag(2, 1)`, is orthogonal but its inverse has leading
`1 × 1` minor `0`: the hypothesis of `property_5_9` fails, and it is the only one that does. -/
theorem property_5_9_counterexample :
    let A : Matrix (Fin 2) (Fin 2) ℝ := diagonal ![1, 2]
    let X : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]
    (∀ k, qrIterate A k = A) ∧ X ∈ Matrix.orthogonalGroup (Fin 2) ℝ ∧
      X⁻¹ * A * X = diagonal ![2, 1] ∧
      ¬ IsUnit ((X⁻¹).submatrix (Fin.castLE (show 1 ≤ 2 by norm_num))
        (Fin.castLE (show 1 ≤ 2 by norm_num))).det ∧
      ¬ Tendsto (fun k => qrIterate A k 0 0) atTop (𝓝 (2 : ℝ)) := by
  intro A X
  have hXX : X * X = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [X, Matrix.mul_apply, Fin.sum_univ_two]
  have hXinv : X⁻¹ = X := inv_eq_left_inv hXX
  have hfix : ∀ k, qrIterate A k = A :=
    qrIterate_eq_self_of_isUpperTriangular (blockTriangular_diagonal _) fun j => by
      fin_cases j <;> simp [A]
  refine ⟨hfix, ?_, ?_, ?_, ?_⟩
  · rw [mem_orthogonalGroup_iff]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [X, Matrix.mul_apply, Fin.sum_univ_two]
  · rw [hXinv]
    ext i j
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> simp [X, A]
  · rw [hXinv, det_unique]
    simp [X]
  · simp only [hfix]
    rw [tendsto_const_nhds_iff]
    simp [A]

/-! ### (5.37): the rate of convergence -/

/-- **(5.37), the convergence rate.** Under the hypotheses of `property_5_9`, for `i = 2, …, n`
the subdiagonal entry `t_{i,i-1}^{(k)}` satisfies `|t_{i,i-1}^{(k)}| = O(|λ_i/λ_{i-1}|^k)` as
`k → ∞`: there is a constant `C` with `|t_{i,i-1}^{(k)}| ≤ C (|λ_i|/|λ_{i-1}|)^k` for every `k`.
Backbone `Matrix.exists_abs_qrIterate_apply_le` with the rate parameter `r = |λ_i|`, the largest
modulus among the eigenvalues after `λ_{i-1}`. -/
theorem equation_5_37 {A X : Matrix (Fin N) (Fin N) ℝ} (hX : IsUnit X) {lam : Fin N → ℝ}
    (hD : X⁻¹ * A * X = diagonal lam) (hne : ∀ i, lam i ≠ 0)
    (hsep : ∀ i j, i < j → |lam j| < |lam i|)
    (hminor : ∀ (m : ℕ) (hm : m ≤ N),
      IsUnit ((X⁻¹).submatrix (Fin.castLE hm) (Fin.castLE hm)).det)
    {i j : Fin N} (hij : (i : ℕ) = j + 1) :
    ∃ C : ℝ, ∀ k, |qrIterate A k i j| ≤ C * (|lam i| / |lam j|) ^ k := by
  obtain ⟨hA, hx, hxtop, heig, hsep', hgen⟩ := property_5_9_hypotheses hX hD hne hsep hminor
  have hji : j < i := Fin.lt_def.2 (by omega)
  have hr : ∀ j', j < j' → ‖lam j'‖ ≤ ‖lam i‖ := fun j' hj' => by
    rcases lt_trichotomy i j' with h | rfl | h
    · exact (hsep' i j' h).le
    · exact le_rfl
    · exact absurd (Fin.lt_def.1 h) (by have := Fin.lt_def.1 hj'; omega)
  obtain ⟨C, hC⟩ := Matrix.exists_abs_qrIterate_apply_le hA hx hxtop heig hsep' hgen hji
    (norm_nonneg _) hr (hsep' j i hji)
  refine ⟨C, fun k => ?_⟩
  rw [qrIterate_eq]
  simpa only [Real.norm_eq_abs] using hC k

/-! ### The symmetric case -/

/-- **Property 5.9, the symmetric case.** If in addition `A` is symmetric, the sequence `T⁽ᵏ⁾`
tends to a diagonal matrix: `t_{ij}^{(k)} → 0` for every `i ≠ j` and `t_{ii}^{(k)} → λ_i`, that is,
`T⁽ᵏ⁾ → diag(λ_1, …, λ_n)` entrywise. Every iterate is symmetric, being an orthogonal conjugate of
`A` (`Matrix.isHermitian_qrIterate`), so the entries above the diagonal are those below it. -/
theorem property_5_9_symm {A X : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsSymm) (hX : IsUnit X)
    {lam : Fin N → ℝ} (hD : X⁻¹ * A * X = diagonal lam) (hne : ∀ i, lam i ≠ 0)
    (hsep : ∀ i j, i < j → |lam j| < |lam i|)
    (hminor : ∀ (m : ℕ) (hm : m ≤ N),
      IsUnit ((X⁻¹).submatrix (Fin.castLE hm) (Fin.castLE hm)).det) :
    ∀ i j : Fin N, Tendsto (fun k => qrIterate A k i j) atTop (𝓝 (diagonal lam i j)) := by
  obtain ⟨hlow, hdiag⟩ := property_5_9 hX hD hne hsep hminor
  have hherm : A.IsHermitian := by rwa [IsHermitian, conjTranspose_eq_transpose_of_trivial]
  intro i j
  rcases lt_trichotomy j i with h | rfl | h
  · rw [diagonal_apply_ne _ h.ne']
    exact hlow i j h
  · rw [diagonal_apply_eq]
    exact hdiag _
  · rw [diagonal_apply_ne _ h.ne]
    refine (hlow j i h).congr fun k => ?_
    rw [qrIterate_eq, ← (isHermitian_qrIterate hherm k).apply j i, star_trivial]

/-! ### Remark 5.2: the LR iteration -/

/-- **Remark 5.2 (the LR iteration).** If `A = L R` with `L` unit lower triangular (hence
nonsingular) and `R` upper triangular, then `L⁻¹ A L = L⁻¹ (L R) L = R L`: the matrix `R L` of
the LR (Rutishauser) iteration is similar to `A` by the nonorthogonal transformation `L`, and in
particular has the same characteristic polynomial. The identity uses nothing about `R`. -/
theorem remark_5_2 {A L R : Matrix (Fin N) (Fin N) ℝ} (hL : L.IsUnitLowerTriangular)
    (hA : A = L * R) : L⁻¹ * A * L = R * L ∧ (R * L).charpoly = A.charpoly := by
  refine ⟨?_, by rw [hA, charpoly_mul_comm]⟩
  rw [hA, ← Matrix.mul_assoc, nonsing_inv_mul L ((isUnit_iff_isUnit_det L).mp hL.isUnit),
    Matrix.one_mul]

end QuarteroniSaccoSaleri.Chapter05
