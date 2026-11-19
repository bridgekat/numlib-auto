/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.LinearAlgebra.Matrix.QR
import NumlibSurface.QuarteroniSaccoSaleri.Chapter05.Section04

/-!
# Quarteroni, Sacco and Saleri, Section 5.5: The Basic QR Iteration

This module formalizes Section 5.5 of [quarteroni2000numerical], on the convergence of the basic QR
iteration $T^{(0)} = A$, $T^{(k-1)} = Q^{(k)} R^{(k)}$, $T^{(k)} = R^{(k)} Q^{(k)}$ of Section 5.4.
Let $A \in \mathbb{R}^{n \times n}$ be diagonalizable, $X^{-1} A X = \operatorname{diag}(\lambda_1,
\dots, \lambda_n)$, with eigenvalues of distinct moduli $|\lambda_1| > |\lambda_2| > \dots >
|\lambda_n| > 0$. If every leading principal minor of $X^{-1}$ is nonzero, then $T^{(k)}$ converges
to an upper triangular matrix with $\lambda_1, \dots, \lambda_n$ on the diagonal (Property 5.9,
(5.36)). The subdiagonal entries decay like $|\lambda_i / \lambda_{i-1}|^k$ (5.37), and for a
symmetric $A$ the limit is $\operatorname{diag}(\lambda_1, \dots, \lambda_n)$. The LR iteration of
Remark 5.2 replaces the orthogonal similarity by a similarity with a unit lower triangular matrix.

The proofs specialize the backbone module `Numlib.Eigen.QRAlgorithm`: the convergence theorem
`Matrix.tendsto_qrIterate`, its rate `Matrix.exists_abs_qrIterate_apply_le`, the translation
`Matrix.forall_isLowerSet_disjoint_iff_isUnit_leadingPrincipal` of its hypothesis of general
position into leading principal minors, and the symmetry of the iterates
`Matrix.isHermitian_qrIterate`. The iteration is `QuarteroniSaccoSaleri.Chapter05.qrIterate` of
Section 5.4.

## Main results

* Property 5.9, `QuarteroniSaccoSaleri.Chapter05.property_5_9`: under the minor condition, $T^{(k)}$
  converges to upper triangular form with the eigenvalues in order on the diagonal.
* Property 5.9, `QuarteroniSaccoSaleri.Chapter05.property_5_9_counterexample`: without the minor
  condition, the property fails for $A = \operatorname{diag}(1, 2)$.
* Equation (5.37), `QuarteroniSaccoSaleri.Chapter05.equation_5_37`: $|t_{i,i-1}^{(k)}| \le C
  |\lambda_i / \lambda_{i-1}|^k$.
* Property 5.9, `QuarteroniSaccoSaleri.Chapter05.property_5_9_symm`: for a symmetric $A$, $T^{(k)}
  \to \operatorname{diag}(\lambda_1, \dots, \lambda_n)$.
* Remark 5.2, `QuarteroniSaccoSaleri.Chapter05.remark_5_2`: the matrix $RL$ of the LR iteration is
  similar to $A = LR$.

## Conventions

* The basic QR iteration is `QuarteroniSaccoSaleri.Chapter05.qrIterate` of Section 5.4, with
  $Q^{(0)} = I$ and $T^{(0)} = A$.
* A diagonalizable $A \in \mathbb{R}^{n \times n}$ is given, as in Theorem 5.3, by a nonsingular $X$
  with $X^{-1} A X = \operatorname{diag}(\lambda_1, \dots, \lambda_n)$. The columns of $X$ are the
  eigenvectors.
* The eigenvalues are indexed by `Fin N` in the order of the book, $|\lambda_1| > |\lambda_2| >
  \dots > |\lambda_n|$, which is the hypothesis `∀ i j, i < j → |lam j| < |lam i|`.
* The leading principal minor of order $m$ of $X^{-1}$ is the determinant of `(X⁻¹).submatrix
  (Fin.castLE hm) (Fin.castLE hm)`.

## Implementation notes

* The rate (5.37) is stated with the base $|\lambda_i / \lambda_{i-1}|$ of the book. The backbone's
  estimate allows its rate parameter to be the largest modulus among the eigenvalues after
  $\lambda_{i-1}$, which is $|\lambda_i|$.

## Deviations from the source

* **Correction.** The ordered basic QR convergence and rates require nonzero eigenvalues and an
  explicit leading-minor hypothesis. See `QuarteroniSaccoSaleri.Chapter05.property_5_9_hypotheses`,
  `QuarteroniSaccoSaleri.Chapter05.property_5_9`, `QuarteroniSaccoSaleri.Chapter05.equation_5_37`,
  `QuarteroniSaccoSaleri.Chapter05.property_5_9_symm`.
* **Correction.** A stationary diagonal matrix shows why separation alone does not give the printed
  order. See `QuarteroniSaccoSaleri.Chapter05.property_5_9_counterexample`.
* **Property 5.9** (correction). With only $|\lambda_1| > \dots > |\lambda_n|$, the property is
  false: the iteration leaves $A = \operatorname{diag}(1, 2)$ fixed. The property is stated with the
  further hypothesis that every leading principal minor of $X^{-1}$ is nonzero, which the theorem of
  Golub and Van Loan that the book cites (Theorem 7.3.1) requires. See
  `QuarteroniSaccoSaleri.Chapter05.property_5_9_counterexample`.
* **Property 5.9, $|\lambda_n| > 0$** (reading). The condition is implicit in the statement of the
  book and explicit here. See `QuarteroniSaccoSaleri.Chapter05.property_5_9`.

## Not formalized

* **Example 5.4.** It is numerical.
-/

open Filter Finset Matrix Topology

namespace QuarteroniSaccoSaleri.Chapter05

variable {N : ℕ}

/-! ### Bridges to the backbone -/

/-- The hypotheses of Property 5.9 of [quarteroni2000numerical] in the form that the backbone's
`Matrix.tendsto_qrIterate` takes. Let $A, X \in \mathbb{R}^{n \times n}$ with $X$ nonsingular
and $X^{-1} A X = \operatorname{diag}(\lambda_1, \dots, \lambda_n)$, let every $\lambda_i$ be
nonzero, let $|\lambda_j| < |\lambda_i|$ for $i < j$, and let every leading principal minor of
$X^{-1}$ be nonzero. Then:

1. $A$ is nonsingular;
2. the columns $x_1, \dots, x_n$ of $X$ are a basis of $\mathbb{R}^n$, and
   $A x_j = \lambda_j x_j$ for every $j$;
3. $|\lambda_k| < |\lambda_j|$ for $j < k$;
4. the canonical flag is in general position with respect to the eigenvectors: for every initial
   segment $J$ of the indices, the span of the unit vectors $e_j$ with $j \in J$ meets the span
   of the $x_j$ with $j \notin J$ only in $0$.

The columns are `Matrix.euclideanCol X j`, and an initial segment is a lower set of `Fin N`.

**Correction.** Magnitude separation by itself does not enforce the printed order in the limit. Lean
assumes nonzero eigenvalues and nonsingular leading principal minors of the inverse eigenvector
matrix. For a general matrix it states convergence of the subdiagonal and diagonal entries only. For
symmetric input it obtains full diagonal convergence.
-/
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

/-- **Property 5.9** of [quarteroni2000numerical] (convergence of the QR method), (5.36). Let
$A \in \mathbb{R}^{n \times n}$ be diagonalizable, $X^{-1} A X = \operatorname{diag}(\lambda_1,
\dots, \lambda_n)$ with $X$ nonsingular, and
$$|\lambda_1| > |\lambda_2| > \dots > |\lambda_n| > 0.$$
Assume that every leading principal minor of $X^{-1}$ is nonzero. Then the iterates $T^{(k)}$ of
the basic QR iteration converge to upper triangular form with the eigenvalues in order on the
diagonal:
$$t_{ij}^{(k)} \to 0 \quad (i > j), \qquad t_{ii}^{(k)} \to \lambda_i.$$

**Correction.** The book assumes only the ordering of the eigenvalues. Without the minor
condition the statement is false
(`QuarteroniSaccoSaleri.Chapter05.property_5_9_counterexample`). Theorem 7.3.1 of Golub and Van
Loan, which the book cites, also requires that $X^{-1}$ have an LU factorization, that is, that
its leading principal minors be nonzero.

**Reading.** The condition $|\lambda_n| > 0$ is implicit in the statement of the book. Here it
is the explicit hypothesis that every $\lambda_i$ is nonzero.

The proof specializes the backbone's `Matrix.tendsto_qrIterate`, whose hypothesis of general
position is the minor condition by
`Matrix.forall_isLowerSet_disjoint_iff_isUnit_leadingPrincipal`.

**Correction.** Magnitude separation by itself does not enforce the printed order in the limit. Lean
assumes nonzero eigenvalues and nonsingular leading principal minors of the inverse eigenvector
matrix. For a general matrix it states convergence of the subdiagonal and diagonal entries only. For
symmetric input it obtains full diagonal convergence.
-/
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

/-- Let $A \in \mathbb{R}^{n \times n}$ be upper triangular with a positive diagonal. Then the QR
iteration leaves $A$ fixed: $T^{(k)} = A$ for every $k$. -/
theorem qrIterate_eq_self_of_isUpperTriangular {A : Matrix (Fin N) (Fin N) ℝ}
    (hA : A.IsUpperTriangular) (hd : ∀ j, 0 < A j j) : ∀ k, qrIterate A k = A
  | 0 => rfl
  | k + 1 => by
    rw [qrIterate, qrIterate_eq_self_of_isUpperTriangular hA hd k,
      (qrQ_eq_one_of_isUpperTriangular hA hd).1, (qrQ_eq_one_of_isUpperTriangular hA hd).2,
      Matrix.mul_one]

/-- **Property 5.9** of [quarteroni2000numerical], the counterexample without the minor condition.
Let $A = \operatorname{diag}(1, 2)$ and
$$X = \begin{bmatrix} 0 & 1 \\ 1 & 0 \end{bmatrix}.$$
Then:

1. the QR iteration is stationary, $T^{(k)} = A$ for every $k$;
2. $X$ is orthogonal and $X^{-1} A X = \operatorname{diag}(2, 1)$, so $\lambda_1 = 2$,
   $\lambda_2 = 1$ and $|\lambda_1| > |\lambda_2| > 0$;
3. the leading principal minor of order $1$ of $X^{-1}$ is $0$;
4. $t_{11}^{(k)}$ does not tend to $\lambda_1 = 2$, as (5.36) requires.

The diagonal of $A$ is positive, so the QR factorization of $A$ is $Q = I$, $R = A$. The minor
condition of `QuarteroniSaccoSaleri.Chapter05.property_5_9` is the only one of its hypotheses
that fails.

**Correction.** The matrix with diagonal $(1,2)$ is stationary and satisfies strict magnitude
separation when its eigenvalues are indexed $(2,1)$. Its leading minor condition fails and the
diagonal does not converge in that ordered list.
-/
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

/-! ### Equation (5.37): the rate of convergence -/

/-- **Equation (5.37)** of [quarteroni2000numerical], the rate of convergence. Under the hypotheses
of Property 5.9 (`QuarteroniSaccoSaleri.Chapter05.property_5_9`), for $i = 2, \dots, n$ the
subdiagonal entry $t_{i,i-1}^{(k)}$ satisfies $|t_{i,i-1}^{(k)}| = O(|\lambda_i /
\lambda_{i-1}|^k)$ as $k \to \infty$: there is a constant $C$ with
$$|t_{i,i-1}^{(k)}| \le C \left( \frac{|\lambda_i|}{|\lambda_{i-1}|} \right)^k \quad \text{for
  every } k.$$

The proof specializes the backbone's `Matrix.exists_abs_qrIterate_apply_le` with the rate
parameter $r = |\lambda_i|$, the largest modulus among the eigenvalues after $\lambda_{i-1}$.

**Correction.** Magnitude separation by itself does not enforce the printed order in the limit. Lean
assumes nonzero eigenvalues and nonsingular leading principal minors of the inverse eigenvector
matrix. For a general matrix it states convergence of the subdiagonal and diagonal entries only. For
symmetric input it obtains full diagonal convergence.
-/
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

/-- **Property 5.9** of [quarteroni2000numerical], the symmetric case. Under the hypotheses of
`QuarteroniSaccoSaleri.Chapter05.property_5_9`, let $A$ also be symmetric. Then the sequence
$T^{(k)}$ tends to a diagonal matrix: $t_{ij}^{(k)} \to 0$ for every $i \neq j$ and
$t_{ii}^{(k)} \to \lambda_i$, that is, $T^{(k)} \to \operatorname{diag}(\lambda_1, \dots,
\lambda_n)$ entrywise.

Every iterate is symmetric, because it is an orthogonal similarity transform of $A$
(`Matrix.isHermitian_qrIterate`). So the entries above the diagonal are those below it.

**Correction.** Magnitude separation by itself does not enforce the printed order in the limit. Lean
assumes nonzero eigenvalues and nonsingular leading principal minors of the inverse eigenvector
matrix. For a general matrix it states convergence of the subdiagonal and diagonal entries only. For
symmetric input it obtains full diagonal convergence.
-/
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

/-- **Remark 5.2** of [quarteroni2000numerical] (the LR iteration). Let
$A, L, R \in \mathbb{R}^{n \times n}$ with $L$ unit lower triangular, so that $L$ is
nonsingular, and $A = LR$. Then
$$L^{-1} A L = L^{-1} (L R) L = R L,$$
so the matrix $RL$ of the LR (Rutishauser) iteration is similar to $A$ through the
transformation $L$, which is not orthogonal. In particular, $RL$ and $A$ have the same
characteristic polynomial.

The identity uses nothing about $R$. -/
theorem remark_5_2 {A L R : Matrix (Fin N) (Fin N) ℝ} (hL : L.IsUnitLowerTriangular)
    (hA : A = L * R) : L⁻¹ * A * L = R * L ∧ (R * L).charpoly = A.charpoly := by
  refine ⟨?_, by rw [hA, charpoly_mul_comm]⟩
  rw [hA, ← Matrix.mul_assoc, nonsing_inv_mul L ((isUnit_iff_isUnit_det L).mp hL.isUnit),
    Matrix.one_mul]

end QuarteroniSaccoSaleri.Chapter05
