import Numlib.Analysis.Matrix.SingularValues
import Numlib.LinearAlgebra.Matrix.GSVD
import Numlib.LinearAlgebra.Matrix.LeastSquares.Total
import NumlibSurface.GolubVanLoan.Chapter01.Section02
import NumlibSurface.GolubVanLoan.Chapter05.Section01

/-!
# Golub–Van Loan §6.3: total least squares

Surface file for [golub2013matrix] §6.3: the least-squares problem recast as (6.3.1), the total
least-squares problem (6.3.2)–(6.3.3) and an instance with no solution, Theorem 6.3.1 (the
generic condition makes `V₂₂` nonsingular, (6.3.4) is the unique TLS perturbation and `X_TLS` the
unique TLS solution) and the `τ`-norm of the solution (§6.3.1), the single right-hand side and
Algorithm 6.3.1 (§6.3.2), the orthogonal-regression reading (6.3.6) and the distance
interpretation (§6.3.3).

## Conventions

Real matrices, 0-based. The TLS problem with weights `D = diag(d)`, `T = diag(t)` is the backbone's
`Matrix.IsTLSPerturbation d t A B E R` (the columns of `[A | B]` indexed by `Fin n ⊕ Fin k`, or
`Fin n ⊕ Unit` for one right-hand side, a column `b` being `replicateCol Unit b`), and a TLS
solution is `Matrix.IsTLSSolution`; (6.3.2) is `d = 1`, `t = 1`. The Frobenius norm is the scoped
`Matrix.Norms.Frobenius` norm, the 2-norm the scoped `Matrix.Norms.L2Operator` one. For
Theorem 6.3.1 the matrix `C = D[A | B]T = [C₁ | C₂]` is reindexed to `Fin (n + k)` columns
(`finSumFinEquiv`), and `V₁₂`, `V₂₂` are the blocks `V(1:n, n+1:n+k)`, `V(n+1:n+k, n+1:n+k)`.
For one right-hand side the book's `C = D[A | b]T` with columns `Fin (n + 1)` is `tlsMatrix`, the
backbone's `tlsWeighted` reindexed by `finSuccEquivSumUnit` (the last column `b`'s), with the
column weights `tlsWeights t`; the book's index `n − p` of `v_{n+1−p}` is `r` (0-based).

Algorithm 6.3.1 follows the algorithm conventions of `NumlibSurface/GolubVanLoan`: every product
and quotient through `rnd`; "Compute the SVD" is a monadic parameter (chapter 8's algorithm);
`p` is read off the computed singular values by exact comparisons; the Householder reflection is
chapter 5's `houseOn` and `householderApplyRight` on index lists.

## Not formalized here

The variants of §6.3.4 and the flop count are not formalized (see the chapter group).

## Sources and errata

Backbone `Numlib/LinearAlgebra/Matrix/LeastSquares/Total`, `Numlib/Analysis/Matrix/SingularValues`
(`Matrix.l2_opNorm_mul_inv_sq_eq`). The proof of Theorem 6.3.1 cites Corollary 2.4.5 for
`σ_n(C) ≥ σ_n(C₁)`; that corollary does not give it — it is column interlacing (Corollary 8.6.3).
The `τ`-norm identity after the proof needs no CS decomposition, only
`V₁₂ᵀV₁₂ + V₂₂ᵀV₂₂ = I`. The line "… `|t_{n+1}| ‖Db‖₂ ≥ σ_n(DAT₁)`" printed after §6.3.4 is a
displaced fragment of P6.3.1(b).
-/

open Matrix

namespace GolubVanLoan.Chapter06

variable {m n : ℕ}

/-- **(6.3.1).** "The problem of minimizing `‖Ax − b‖₂` where `A ∈ ℝ^{m×n}` and `b ∈ ℝᵐ` can be
recast as follows: `min_{b + r ∈ ran(A)} ‖r‖₂`": `x` is a least-squares solution iff `‖Ax − b‖₂`
is the least norm of an `r` with `b + r ∈ ran(A)` (attained at `r = Ax − b`). -/
theorem equation_6_3_1 {A : Matrix (Fin m) (Fin n) ℝ} {b : EuclideanSpace ℝ (Fin m)}
    {x : EuclideanSpace ℝ (Fin n)} :
    IsLeastSquaresSolution A b x ↔
      IsLeast ((fun r => ‖r‖) '' {r | b + r ∈ LinearMap.range (toEuclideanLin A)})
        ‖toEuclideanLin A x - b‖ := by
  constructor
  · intro h
    refine ⟨⟨toEuclideanLin A x - b, ⟨x, by abel⟩, rfl⟩, ?_⟩
    rintro _ ⟨r, ⟨y, hy⟩, rfl⟩
    have hr : r = toEuclideanLin A y - b := by rw [hy]; abel
    rw [hr]
    exact h y
  · intro h y
    exact h.2 ⟨toEuclideanLin A y - b, ⟨y, by abel⟩, rfl⟩

section Example

open scoped Matrix.Norms.Frobenius

/-- The weighted matrix with unit weights is `[E | R]`. -/
private theorem tlsWeighted_one_one {k : Type*} [Fintype k] [DecidableEq k]
    (E : Matrix (Fin 3) (Fin 2) ℝ) (R : Matrix (Fin 3) k ℝ) :
    tlsWeighted 1 1 E R = fromCols E R := by
  simp [tlsWeighted]

/-- **§6.3, a TLS problem without a solution.** "(6.3.2) may fail to have a solution altogether.
For example, if `A = [1 0; 0 0; 0 0]`, `b = [1; 1; 1]`, `E_ε = [0 0; 0 ε; 0 ε]`, then for all
`ε > 0`, `b ∈ ran(A + E_ε)`. However, there is no smallest value of `‖[E, r]‖_F` for which
`b + r ∈ ran(A + E)`." A minimizer would have `‖[E | r]‖_F ≤ ‖[E_ε | 0]‖_F = √2 ε` for every
`ε > 0`, so `[E | r] = 0`, and then `b ∈ ran(A)`, which it is not. -/
theorem tls_not_exists_example :
    ¬ ∃ (E : Matrix (Fin 3) (Fin 2) ℝ) (r : Matrix (Fin 3) Unit ℝ),
      IsTLSPerturbation 1 1 !![(1 : ℝ), 0; 0, 0; 0, 0] (replicateCol Unit ![1, 1, 1]) E r := by
  rintro ⟨E, R, hP⟩
  set E₁ : Matrix (Fin 3) (Fin 2) ℝ := !![0, 0; 0, 1; 0, 1] with hE₁
  have hfeas : ∀ ε : ℝ, 0 < ε →
      LinearMap.range (replicateCol Unit ![(1 : ℝ), 1, 1] + 0).mulVecLin ≤
        LinearMap.range (!![(1 : ℝ), 0; 0, 0; 0, 0] + ε • E₁).mulVecLin := by
    intro ε hε
    rintro _ ⟨v, rfl⟩
    refine ⟨v () • ![1, 1 / ε], ?_⟩
    ext i
    fin_cases i <;> simp [hE₁, mulVec, dotProduct, Fin.sum_univ_two] <;> field_simp
  set c := ‖fromCols E₁ (0 : Matrix (Fin 3) Unit ℝ)‖
  have hbound : ∀ ε : ℝ, 0 < ε → ‖fromCols E R‖ ≤ ε * c := by
    intro ε hε
    have h := hP.norm_le (ε • E₁) 0 (hfeas ε hε)
    rw [tlsWeighted_one_one, tlsWeighted_one_one] at h
    have e : fromCols (ε • E₁) (0 : Matrix (Fin 3) Unit ℝ) = ε • fromCols E₁ 0 := by
      ext i (j | j) <;> simp
    rwa [e, norm_smul, Real.norm_of_nonneg hε.le] at h
  have hzero : fromCols E R = 0 := by
    rw [← norm_le_zero_iff]
    refine le_of_forall_pos_le_add fun δ hδ => ?_
    have hc : 0 ≤ c := norm_nonneg _
    have h := hbound (δ / (c + 1)) (by positivity)
    have : δ / (c + 1) * c ≤ δ := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  have hE : E = 0 := by
    ext i j
    simpa using congrFun (congrFun hzero i) (Sum.inl j)
  have hR : R = 0 := by
    ext i j
    simpa using congrFun (congrFun hzero i) (Sum.inr j)
  have hb := hP.range_le ⟨fun _ => 1, rfl⟩
  obtain ⟨y, hy⟩ := hb
  have h1 := congrFun hy 1
  simp [hE, hR, mulVec, dotProduct, Fin.sum_univ_two] at h1

end Example

/-- **Theorem 6.3.1, the nonsingularity of `V₂₂`.** "Suppose `A ∈ ℝ^{m×n}` and `B ∈ ℝ^{m×k}` and
that `D = diag(d₁, …, d_m)` and `T = diag(t₁, …, t_{n+k})` are nonsingular. … let the SVD of
`C = D[A | B]T = [C₁ C₂]` be specified by `UᵀCV = diag(σ₁, …, σ_{n+k}) = Σ` … If
`σ_n(C₁) > σ_{n+1}(C)`, then … `V₂₂` is nonsingular" (the first fact of the proof, on which
`X_TLS = −T₁V₁₂V₂₂⁻¹T₂⁻¹` rests). Here `T = diag(t₁, t₂)` with `t₁` on the columns of `A` and `t₂`
on those of `B`. -/
theorem theorem_6_3_1_isUnit {k : ℕ} {A : Matrix (Fin m) (Fin n) ℝ} {B : Matrix (Fin m) (Fin k) ℝ}
    (d : Fin m → ℝ) (t₁ : Fin n → ℝ) (t₂ : Fin k → ℝ) {U : Matrix (Fin m) (Fin m) ℝ} {σ : ℕ → ℝ}
    {V : Matrix (Fin (n + k)) (Fin (n + k)) ℝ}
    (hC : IsSVD ((fromCols (diagonal d * A * diagonal t₁) (diagonal d * B * diagonal t₂)).submatrix
      id finSumFinEquiv.symm) U σ V)
    (hσ : σ n < (diagonal d * A * diagonal t₁).sortedSingularValues (n - 1)) :
    IsUnit (V.submatrix (Fin.natAdd n) (Fin.natAdd n)) :=
  isUnit_lowerRightBlock_of_lt hC hσ

/-- The weighted matrix `D[E | R]T` with `T = diag(t₁, t₂)` is `[D E T₁ | D R T₂]`. -/
private theorem tlsWeighted_sumElim {k : ℕ} (d : Fin m → ℝ) (t₁ : Fin n → ℝ) (t₂ : Fin k → ℝ)
    (E : Matrix (Fin m) (Fin n) ℝ) (R : Matrix (Fin m) (Fin k) ℝ) :
    tlsWeighted d (Sum.elim t₁ t₂) E R =
      fromCols (diagonal d * E * diagonal t₁) (diagonal d * R * diagonal t₂) := by
  ext i (j | j) <;> simp [tlsWeighted, mul_diagonal, diagonal_mul]

/-- The trailing part `U Σ' Vᵀ` of an SVD, `Σ'` keeping the singular values `σ_i`, `i ≥ n`, is
`U₂ Σ₂ V₂ᵀ` with `U₂ = U(:, n+1:n+k)`, `Σ₂ = diag(σ_{n+1}, …, σ_{n+k})` and `V₂ᵀ = [V₁₂ᵀ | V₂₂ᵀ]`
when `m ≥ n + k`. -/
private theorem mul_rectDiagonal_tail_mul_transpose {k : ℕ} (hmnk : n + k ≤ m)
    (U : Matrix (Fin m) (Fin m) ℝ) (σ : ℕ → ℝ) (V : Matrix (Fin (n + k)) (Fin (n + k)) ℝ) :
    U * (rectDiagonal (fun i => if i < n then 0 else σ i) : Matrix (Fin m) (Fin (n + k)) ℝ) *
        Vᵀ =
      U.submatrix id (fun j : Fin k => Fin.castLE hmnk (Fin.natAdd n j)) *
        diagonal (fun j : Fin k => σ (n + j)) * (V.submatrix id (Fin.natAdd n))ᵀ := by
  ext a b
  rw [mul_apply, mul_apply, Fin.sum_univ_add, Finset.sum_eq_zero fun i _ => ?_, zero_add]
  · refine Finset.sum_congr rfl fun j _ => ?_
    have hj : n + (j : ℕ) < m := by omega
    rw [mul_rectDiagonal_apply, mul_diagonal]
    simp only [Fin.val_natAdd, hj, ↓reduceDIte, add_lt_iff_neg_left, not_lt_zero, ite_false,
      submatrix_apply, id_eq, transpose_apply]
    rfl
  · rw [mul_rectDiagonal_apply]
    split_ifs with h h' <;> simp_all

/-- **Theorem 6.3.1.** "Suppose `A ∈ ℝ^{m×n}` and `B ∈ ℝ^{m×k}` and that `D = diag(d₁, …, d_m)` and
`T = diag(t₁, …, t_{n+k})` are nonsingular. Assume `m ≥ n + k` and let the SVD of
`C = D[A | B]T = [C₁ C₂]` be specified by `UᵀCV = diag(σ₁, …, σ_{n+k}) = Σ` where `U`, `V`, and `Σ`
are partitioned as follows: `U = [U₁ U₂]`, `V = [V₁₁ V₁₂; V₂₁ V₂₂]`, `Σ = [Σ₁ 0; 0 Σ₂]` (`n | k`).
If `σ_n(C₁) > σ_{n+1}(C)`, then the matrix `[E₀ | R₀]` defined by
`D[E₀ | R₀]T = −U₂Σ₂[V₁₂ᵀ | V₂₂ᵀ]` (6.3.4) solves (6.3.3). If `T₁ = diag(t₁, …, t_n)` and
`T₂ = diag(t_{n+1}, …, t_{n+k})`, then the matrix `X_TLS = −T₁V₁₂V₂₂⁻¹T₂⁻¹` exists and is the unique
TLS solution to `(A + E₀)X = B + R₀`."

Here `T = diag(t₁, t₂)` (`Sum.elim t₁ t₂` on the columns `Fin n ⊕ Fin k`), `U₂ = U(:, n+1:n+k)` is
the book's thin `U₂` and `Σ₂ = diag(σ_{n+1}, …, σ_{n+k})`. The conclusion: `(E₀, R₀)` satisfies
(6.3.4) and is a TLS perturbation — the only one (backbone
`Matrix.existsUnique_isTLSPerturbation`); `V₂₂` is nonsingular (`theorem_6_3_1_isUnit`); `X`
solves `(A + E₀)X = B + R₀` exactly when `X = X_TLS`, and `X_TLS` is the only TLS solution
(`Matrix.isTLSSolution_iff_eq`). The backbone does not need `m ≥ n + k`; it is used here only to
read the book's `U₂Σ₂[V₁₂ᵀ | V₂₂ᵀ]`. -/
theorem theorem_6_3_1 {k : ℕ} (hmnk : n + k ≤ m) {A : Matrix (Fin m) (Fin n) ℝ}
    {B : Matrix (Fin m) (Fin k) ℝ} {d : Fin m → ℝ} {t₁ : Fin n → ℝ} {t₂ : Fin k → ℝ}
    (hd : ∀ i, d i ≠ 0) (ht₁ : ∀ j, t₁ j ≠ 0) (ht₂ : ∀ j, t₂ j ≠ 0)
    {U : Matrix (Fin m) (Fin m) ℝ} {σ : ℕ → ℝ} {V : Matrix (Fin (n + k)) (Fin (n + k)) ℝ}
    (hC : IsSVD ((fromCols (diagonal d * A * diagonal t₁) (diagonal d * B * diagonal t₂)).submatrix
      id finSumFinEquiv.symm) U σ V)
    (hσ : σ n < (diagonal d * A * diagonal t₁).sortedSingularValues (n - 1)) :
    ∃ E₀ R₀,
      (fromCols (diagonal d * E₀ * diagonal t₁) (diagonal d * R₀ * diagonal t₂)).submatrix id
          finSumFinEquiv.symm =
        -(U.submatrix id (fun j : Fin k => Fin.castLE hmnk (Fin.natAdd n j)) *
          diagonal (fun j : Fin k => σ (n + j)) * (V.submatrix id (Fin.natAdd n))ᵀ) ∧
      IsTLSPerturbation d (Sum.elim t₁ t₂) A B E₀ R₀ ∧
      (∀ E R, IsTLSPerturbation d (Sum.elim t₁ t₂) A B E R → E = E₀ ∧ R = R₀) ∧
      IsUnit (V.submatrix (Fin.natAdd n) (Fin.natAdd n)) ∧
      (∀ X, (A + E₀) * X = B + R₀ ↔
        X = -(diagonal t₁ * V.submatrix (Fin.castAdd k) (Fin.natAdd n) *
          (V.submatrix (Fin.natAdd n) (Fin.natAdd n))⁻¹ * (diagonal t₂)⁻¹)) ∧
      (∀ X, IsTLSSolution d (Sum.elim t₁ t₂) A B X ↔
        X = -(diagonal t₁ * V.submatrix (Fin.castAdd k) (Fin.natAdd n) *
          (V.submatrix (Fin.natAdd n) (Fin.natAdd n))⁻¹ * (diagonal t₂)⁻¹)) := by
  have ht : ∀ j, Sum.elim t₁ t₂ j ≠ 0 := by
    rintro (j | j)
    exacts [ht₁ j, ht₂ j]
  have hC' := hC
  rw [← tlsWeighted_sumElim] at hC'
  have hσ' : σ n < (tlsWeighted d (Sum.elim t₁ t₂) A B).toCols₁.sortedSingularValues (n - 1) := by
    rwa [tlsWeighted_sumElim, toCols₁_fromCols]
  obtain ⟨⟨E₀, R₀⟩, h₀, huniq⟩ := existsUnique_isTLSPerturbation hd ht hC' hσ'
  have hX := isTLSSolution_iff_eq hd ht hC' hσ'
  simp only [Sum.elim_inl, Sum.elim_inr, RCLike.ofReal_real_eq_id, id_eq] at hX
  have hsol : ∀ X, IsTLSSolution d (Sum.elim t₁ t₂) A B X ↔ (A + E₀) * X = B + R₀ := by
    intro X
    refine ⟨fun ⟨E, R, hP, hEq⟩ => ?_, fun h => ⟨E₀, R₀, h₀, h⟩⟩
    obtain ⟨rfl, rfl⟩ := Prod.ext_iff.1 (huniq (E, R) hP)
    exact hEq
  refine ⟨E₀, R₀, ?_, h₀, fun E R h => Prod.ext_iff.1 (huniq (E, R) h),
    theorem_6_3_1_isUnit d t₁ t₂ hC hσ, fun X => (hsol X).symm.trans (hX X), hX⟩
  -- (6.3.4): `D[E₀ | R₀]T = C_n − C = −U₂Σ₂V₂ᵀ`
  have h' := (isTLSPerturbation_iff hd ht hC' hσ').1 h₀
  rw [tlsWeighted_add] at h'
  have e : (tlsWeighted d (Sum.elim t₁ t₂) E₀ R₀).submatrix id finSumFinEquiv.symm =
      -((tlsWeighted d (Sum.elim t₁ t₂) A B).submatrix id finSumFinEquiv.symm -
        svdTruncation U σ V n) := by
    rw [neg_sub, eq_sub_of_add_eq' h']
    ext i j
    simp
  rw [← tlsWeighted_sumElim, e, hC'.sub_svdTruncation,
    ← mul_rectDiagonal_tail_mul_transpose hmnk, star_eq_conjTranspose,
    conjTranspose_eq_transpose_of_trivial]
  congr 3

open scoped Matrix.Norms.L2Operator in
/-- **§6.3.1, the `τ`-norm of the TLS solution.** "Note … that
`‖X‖_τ² = ‖V₁₂V₂₂⁻¹‖₂² = (1 − σ_k(V₂₂)²)/σ_k(V₂₂)²` where we define the `τ`-norm on `ℝ^{n×k}` by
`‖Z‖_τ = ‖T₁⁻¹ZT₂‖₂`", for `X = X_TLS = −T₁V₁₂V₂₂⁻¹T₂⁻¹`, `V` orthogonal and `V₂₂` nonsingular
(Theorem 6.3.1). The book's `σ_k(V₂₂)` is `V₂₂.sortedSingularValues (k − 1)`; the identity needs
only `V₁₂ᵀV₁₂ + V₂₂ᵀV₂₂ = I`, not the thin CS decomposition the book cites. -/
theorem tls_tauNorm {k : ℕ} [NeZero k] {V : Matrix (Fin (n + k)) (Fin (n + k)) ℝ}
    (hV : V ∈ orthogonalGroup (Fin (n + k)) ℝ)
    (hV₂₂ : IsUnit (V.submatrix (Fin.natAdd n) (Fin.natAdd n))) {t₁ : Fin n → ℝ}
    {t₂ : Fin k → ℝ} (ht₁ : ∀ i, t₁ i ≠ 0) (ht₂ : ∀ j, t₂ j ≠ 0) :
    ‖(diagonal t₁)⁻¹ * -(diagonal t₁ * V.submatrix (Fin.castAdd k) (Fin.natAdd n) *
        (V.submatrix (Fin.natAdd n) (Fin.natAdd n))⁻¹ * (diagonal t₂)⁻¹) * diagonal t₂‖ ^ 2 =
      ‖V.submatrix (Fin.castAdd k) (Fin.natAdd n) *
        (V.submatrix (Fin.natAdd n) (Fin.natAdd n))⁻¹‖ ^ 2 ∧
    ‖V.submatrix (Fin.castAdd k) (Fin.natAdd n) *
        (V.submatrix (Fin.natAdd n) (Fin.natAdd n))⁻¹‖ ^ 2 =
      (1 - (V.submatrix (Fin.natAdd n) (Fin.natAdd n)).sortedSingularValues (k - 1) ^ 2) /
        (V.submatrix (Fin.natAdd n) (Fin.natAdd n)).sortedSingularValues (k - 1) ^ 2 := by
  set V₁₂ := V.submatrix (Fin.castAdd k) (Fin.natAdd n)
  set V₂₂ := V.submatrix (Fin.natAdd n) (Fin.natAdd n)
  have hd₁ : IsUnit (diagonal t₁).det := by
    rw [det_diagonal]
    exact (Finset.prod_ne_zero_iff.2 fun i _ => ht₁ i).isUnit
  have hd₂ : IsUnit (diagonal t₂).det := by
    rw [det_diagonal]
    exact (Finset.prod_ne_zero_iff.2 fun i _ => ht₂ i).isUnit
  refine ⟨?_, ?_⟩
  · congr 1
    have e : (diagonal t₁)⁻¹ * -(diagonal t₁ * V₁₂ * V₂₂⁻¹ * (diagonal t₂)⁻¹) * diagonal t₂ =
        -(((diagonal t₁)⁻¹ * diagonal t₁) * (V₁₂ * V₂₂⁻¹) * ((diagonal t₂)⁻¹ * diagonal t₂)) := by
      simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
    rw [e, nonsing_inv_mul _ hd₁, nonsing_inv_mul _ hd₂, Matrix.one_mul, Matrix.mul_one, norm_neg]
  · have hVV : Vᵀ * V = 1 := by
      have := mem_unitaryGroup_iff'.1 hV
      rwa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at this
    have hblk : V₁₂ᴴ * V₁₂ + V₂₂ᴴ * V₂₂ = 1 := by
      ext i j
      have h := congrFun (congrFun hVV (Fin.natAdd n i)) (Fin.natAdd n j)
      rw [mul_apply, Fin.sum_univ_add] at h
      rw [Matrix.add_apply, mul_apply, mul_apply]
      simp only [conjTranspose_apply, transpose_apply, star_trivial, V₁₂, V₂₂,
        submatrix_apply] at h ⊢
      rw [h, one_apply, one_apply]
      simp only [Fin.natAdd_inj]
    have := l2_opNorm_mul_inv_sq_eq hV₂₂ hblk
    rwa [Fintype.card_fin] at this

/-- **(6.3.6).** "It can be shown that the TLS solution `x_TLS` minimizes
`ψ(x) = ∑ᵢ dᵢ² |aᵢᵀx − bᵢ|² / (xᵀT₁⁻²x + t_{n+1}⁻²)`", in the generic case of Theorem 6.3.1 with one
right-hand side (`m > n`, `σ_n(C₁) > σ_{n+1}(C)` for `C = D[A | b]T`), where
`x_TLS = −T₁V₁₂V₂₂⁻¹t_{n+1}⁻¹` reads `x_i = −t_i v_{i,n+1}/(t_{n+1} v_{n+1,n+1})`. -/
theorem equation_6_3_6 (hmn : n < m) (d : Fin m → ℝ) {t : Fin (n + 1) → ℝ}
    (ht : ∀ j, t j ≠ 0) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    {U : Matrix (Fin m) (Fin m) ℝ} {σ : ℕ → ℝ} {V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hC : IsSVD ((fromCols (diagonal d * A * diagonal fun j => t (Fin.castSucc j))
      (replicateCol (Fin 1) fun i => d i * b i * t (Fin.last n))).submatrix id
        finSumFinEquiv.symm) U σ V)
    (hsep : σ n < (diagonal d * A * diagonal fun j => t (Fin.castSucc j)).sortedSingularValues
      (n - 1)) :
    IsMinOn (tlsObjective d t A b) Set.univ fun j =>
      -(t (Fin.castSucc j) * V (Fin.castSucc j) (Fin.last n)) /
        (t (Fin.last n) * V (Fin.last n) (Fin.last n)) :=
  isMinOn_tlsObjective hmn d ht A b hC hsep

/-! ### §6.3.2 The single right-hand side, Algorithm 6.3.1 -/

/-- The trailing columns `V(:, r+1 : n)` of an `n`-column matrix (0-based: the columns
`r, …, n − 1`). -/
def trailingColumns {l n : ℕ} (V : Matrix (Fin l) (Fin n) ℝ) (r : ℕ) :
    Matrix (Fin l) (Fin (n - r)) ℝ :=
  V.submatrix id fun j => ⟨r + j, by omega⟩

/-- The trailing columns of an orthogonal matrix are orthonormal. -/
theorem trailingColumns_transpose_mul_self {n : ℕ} {V : Matrix (Fin n) (Fin n) ℝ}
    (hV : V ∈ orthogonalGroup (Fin n) ℝ) (r : ℕ) :
    (trailingColumns V r)ᵀ * trailingColumns V r = 1 := by
  have hVV : Vᵀ * V = 1 := by
    have := mem_unitaryGroup_iff'.1 hV
    rwa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at this
  rw [trailingColumns, transpose_submatrix, ← submatrix_mul _ _ _ _ _ Function.bijective_id, hVV]
  exact submatrix_one _ fun a b hab => Fin.ext (by simpa using congrArg Fin.val hab)

/-- A matrix with orthonormal columns preserves dot products with itself. -/
private theorem dotProduct_mulVec_self_of_transpose_mul_self {k l : ℕ}
    {W : Matrix (Fin k) (Fin l) ℝ} (hW : Wᵀ * W = 1) (y : Fin l → ℝ) :
    (W *ᵥ y) ⬝ᵥ (W *ᵥ y) = y ⬝ᵥ y := by
  rw [dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec, hW, one_mulVec, dotProduct_comm]

/-- **`‖C w‖²` in singular coordinates**: for an SVD `UᵀCV = Σ` of a tall `C` (`k ≤ m` columns),
`‖C w‖₂² = ∑_j σ_j² ((Vᵀw)_j)²`. -/
private theorem mulVec_dotProduct_self_eq_of_isSVD {k : ℕ} {C : Matrix (Fin m) (Fin k) ℝ}
    {U : Matrix (Fin m) (Fin m) ℝ} {σ : ℕ → ℝ} {V : Matrix (Fin k) (Fin k) ℝ}
    (h : IsSVD C U σ V) (hkm : k ≤ m) (w : Fin k → ℝ) :
    (C *ᵥ w) ⬝ᵥ (C *ᵥ w) = ∑ j : Fin k, σ j ^ 2 * (Vᵀ *ᵥ w) j ^ 2 := by
  have hC := h.eq_mul_mul_star
  simp only [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial,
    RCLike.ofReal_real_eq_id, id_eq] at hC
  have hUU : Uᵀ * U = 1 := by
    have := mem_unitaryGroup_iff'.1 h.mem_unitaryGroup_left
    rwa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at this
  rw [hC, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec_self_of_transpose_mul_self hUU,
    dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec, ← conjTranspose_eq_transpose_of_trivial,
    conjTranspose_rectDiagonal_mul_self, dotProduct]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mulVec_diagonal, ite_eq_left (lt_of_lt_of_le j.isLt hkm), star_trivial]
  ring

/-- **The least singular value of a tall matrix** is the last diagonal entry of any SVD. -/
private theorem iInf_colSingularValues_eq_of_isSVD {C : Matrix (Fin m) (Fin (n + 1)) ℝ}
    {U : Matrix (Fin m) (Fin m) ℝ} {σ : ℕ → ℝ} {V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (h : IsSVD C U σ V) (hmn : n < m) : ⨅ i, C.colSingularValues i = σ n := by
  rw [← sortedSingularValues_eq_iInf_colSingularValues, Fintype.card_fin, Nat.add_sub_cancel,
    h.singularValues_eq hmn (Nat.lt_succ_self n)]

/-- **The minimizers of `‖Cw‖` on the unit sphere** (the first half): if `σ_j = σ_n` for
`j ≥ r`, every `w` whose `V`-coordinates vanish below `r` has `‖Cw‖ = σ_n ‖w‖`. -/
private theorem mulVec_dotProduct_self_of_coord_eq_zero {C : Matrix (Fin m) (Fin (n + 1)) ℝ}
    {U : Matrix (Fin m) (Fin m) ℝ} {σ : ℕ → ℝ} {V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (h : IsSVD C U σ V) (hmn : n < m) {r : ℕ} (heq : ∀ j : Fin (n + 1), r ≤ j → σ j = σ n)
    {w : Fin (n + 1) → ℝ} (hw : ∀ j : Fin (n + 1), (j : ℕ) < r → (Vᵀ *ᵥ w) j = 0) :
    (C *ᵥ w) ⬝ᵥ (C *ᵥ w) = σ n ^ 2 * (w ⬝ᵥ w) := by
  have hVV : Vᵀᵀ * Vᵀ = 1 := by
    rw [transpose_transpose]
    have := mem_unitaryGroup_iff.1 h.mem_unitaryGroup_right
    rwa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at this
  rw [mulVec_dotProduct_self_eq_of_isSVD h hmn,
    ← dotProduct_mulVec_self_of_transpose_mul_self hVV w,
    dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : (j : ℕ) < r
  · rw [hw j hj]
    ring
  · rw [heq j (not_lt.1 hj)]
    ring

/-- **The minimizers of `‖Cw‖` on the unit sphere** (the second half): if `σ_j > σ_n` for `j < r`,
then `‖Cw‖ = σ_n ‖w‖` forces the `V`-coordinates of `w` below `r` to vanish. -/
private theorem coord_eq_zero_of_mulVec_dotProduct_self {C : Matrix (Fin m) (Fin (n + 1)) ℝ}
    {U : Matrix (Fin m) (Fin m) ℝ} {σ : ℕ → ℝ} {V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (h : IsSVD C U σ V) (hmn : n < m) {r : ℕ} (hgap : ∀ j < r, σ n < σ j)
    {w : Fin (n + 1) → ℝ} (hw : (C *ᵥ w) ⬝ᵥ (C *ᵥ w) = σ n ^ 2 * (w ⬝ᵥ w)) :
    ∀ j : Fin (n + 1), (j : ℕ) < r → (Vᵀ *ᵥ w) j = 0 := by
  have hVV : Vᵀᵀ * Vᵀ = 1 := by
    rw [transpose_transpose]
    have := mem_unitaryGroup_iff.1 h.mem_unitaryGroup_right
    rwa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at this
  rw [mulVec_dotProduct_self_eq_of_isSVD h hmn,
    ← dotProduct_mulVec_self_of_transpose_mul_self hVV w,
    dotProduct, Finset.mul_sum, ← sub_eq_zero, ← Finset.sum_sub_distrib] at hw
  have hnn : ∀ j : Fin (n + 1),
      0 ≤ σ j ^ 2 * (Vᵀ *ᵥ w) j ^ 2 - σ n ^ 2 * ((Vᵀ *ᵥ w) j * (Vᵀ *ᵥ w) j) := by
    intro j
    have h1 : σ n ≤ σ j := h.antitone (Nat.le_of_lt_succ j.isLt)
    have h0 := h.nonneg n
    have : σ n ^ 2 ≤ σ j ^ 2 := pow_le_pow_left₀ h0 h1 2
    nlinarith [sq_nonneg ((Vᵀ *ᵥ w) j)]
  intro j hj
  have hz := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hnn j).1 hw j (Finset.mem_univ j)
  have hlt : σ n ^ 2 < σ j ^ 2 := pow_lt_pow_left₀ (hgap j hj) (h.nonneg n) two_ne_zero
  have : ((Vᵀ *ᵥ w) j) ^ 2 * (σ j ^ 2 - σ n ^ 2) = 0 := by linarith
  rcases mul_eq_zero.1 this with h2 | h2
  · exact pow_eq_zero_iff two_ne_zero |>.1 h2
  · linarith

/-- A vector whose `V`-coordinates vanish below `r` is a combination of the trailing columns of
`V`, with the same length. -/
private theorem exists_eq_trailingColumns_mulVec {V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hV : V ∈ orthogonalGroup (Fin (n + 1)) ℝ) {r : ℕ} {w : Fin (n + 1) → ℝ}
    (hw : ∀ j : Fin (n + 1), (j : ℕ) < r → (Vᵀ *ᵥ w) j = 0) :
    ∃ y : Fin (n + 1 - r) → ℝ, w = trailingColumns V r *ᵥ y ∧ y ⬝ᵥ y = w ⬝ᵥ w := by
  have hVV : V * Vᵀ = 1 := by
    have := mem_unitaryGroup_iff.1 hV
    rwa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at this
  set c := Vᵀ *ᵥ w with hc
  have hwc : w = V *ᵥ c := by rw [hc, mulVec_mulVec, hVV, one_mulVec]
  set f : Fin (n + 1 - r) → Fin (n + 1) := fun k => ⟨r + k, by omega⟩ with hf
  have hfinj : Function.Injective f := fun a b hab =>
    Fin.ext (by simpa [hf] using congrArg Fin.val hab)
  have hout : ∀ j, j ∉ Set.range f → c j = 0 := by
    intro j hj
    by_contra hne
    have : r ≤ (j : ℕ) := by
      by_contra hlt
      exact hne (hw j (not_le.1 hlt))
    refine hj ⟨⟨j - r, by omega⟩, Fin.ext ?_⟩
    simp only [hf]
    omega
  refine ⟨c ∘ f, ?_, ?_⟩
  · rw [hwc]
    funext i
    simp only [mulVec, dotProduct, trailingColumns, submatrix_apply, id, Function.comp]
    exact (Fintype.sum_of_injective f hfinj _ _ (fun j hj => by rw [hout j hj, mul_zero])
      (fun k => rfl)).symm
  · have hVt : Vᵀᵀ * Vᵀ = 1 := by rwa [transpose_transpose]
    rw [← dotProduct_mulVec_self_of_transpose_mul_self hVt w, ← hc, dotProduct, dotProduct]
    exact Fintype.sum_of_injective f hfinj _ _ (fun j hj => by rw [hout j hj, mul_zero])
      (fun k => rfl)

/-- The trailing columns' combinations have vanishing `V`-coordinates below `r`. -/
private theorem coord_trailingColumns_mulVec {V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hV : V ∈ orthogonalGroup (Fin (n + 1)) ℝ) (r : ℕ) (y : Fin (n + 1 - r) → ℝ) :
    ∀ j : Fin (n + 1), (j : ℕ) < r → (Vᵀ *ᵥ (trailingColumns V r *ᵥ y)) j = 0 := by
  have hVV : Vᵀ * V = 1 := by
    have := mem_unitaryGroup_iff'.1 hV
    rwa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at this
  intro j hj
  rw [mulVec_mulVec, trailingColumns, ← submatrix_id_id Vᵀ, ← submatrix_mul _ _ _ _ _
    Function.bijective_id, hVV]
  simp only [mulVec, dotProduct, submatrix_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [one_apply_ne, zero_mul]
  intro e
  have := congrArg Fin.val e
  simp at this
  omega

/-- The book's column order of `[A | b]`: `Fin (n + 1) ≃ Fin n ⊕ Unit`, the last index going to the
right-hand side. -/
def finSuccEquivSumUnit (n : ℕ) : Fin (n + 1) ≃ Fin n ⊕ Unit where
  toFun i := Fin.lastCases (Sum.inr ()) Sum.inl i
  invFun := Sum.elim Fin.castSucc fun _ => Fin.last n
  left_inv i := by
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  right_inv x := by
    rcases x with j | u <;> simp

/-- The column weights `T = diag(t₁, …, t_{n+1})` of `[A | b]` in the backbone's indexing of the
columns by `Fin n ⊕ Unit`. -/
def tlsWeights (t : Fin (n + 1) → ℝ) : Fin n ⊕ Unit → ℝ :=
  Sum.elim (fun j => t (Fin.castSucc j)) fun _ => t (Fin.last n)

/-- The book's `C = D[A | b]T` of the single right-hand side, with its columns indexed by
`Fin (n + 1)` (the last one `b`'s): the backbone's `tlsWeighted` reindexed. -/
noncomputable def tlsMatrix (d : Fin m → ℝ) (t : Fin (n + 1) → ℝ) (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) : Matrix (Fin m) (Fin (n + 1)) ℝ :=
  (tlsWeighted d (tlsWeights t) A (replicateCol Unit b)).submatrix id (finSuccEquivSumUnit n)

/-- The weights of `[A | b]` are nonzero when the book's `t_j` are. -/
theorem tlsWeights_ne_zero {t : Fin (n + 1) → ℝ} (ht : ∀ j, t j ≠ 0) (j : Fin n ⊕ Unit) :
    tlsWeights t j ≠ 0 := by
  rcases j with j | u
  · exact ht _
  · exact ht _

/-- `C w = C' (w ∘ e⁻¹)` for the reindexed `C`. -/
theorem tlsMatrix_mulVec (d : Fin m → ℝ) (t : Fin (n + 1) → ℝ) (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (w : Fin (n + 1) → ℝ) :
    tlsMatrix d t A b *ᵥ w = tlsWeighted d (tlsWeights t) A (replicateCol Unit b) *ᵥ
      (w ∘ (finSuccEquivSumUnit n).symm) := by
  rw [tlsMatrix, submatrix_mulVec_equiv]
  rfl

/-- Reindexing a vector does not change its length. -/
private theorem norm_toLp_comp_equiv {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ) (v : ι → ℝ) :
    ‖(WithLp.toLp 2 (v ∘ e.symm) : EuclideanSpace ℝ κ)‖ =
      ‖(WithLp.toLp 2 v : EuclideanSpace ℝ ι)‖ := by
  refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
  rw [← dotProduct_self_eq_norm_sq, ← dotProduct_self_eq_norm_sq, comp_equiv_symm_dotProduct]
  congr 1
  funext i
  simp

/-- **The least singular value of `D[A | b]T`** is the last diagonal entry of any SVD of the
reindexed `C`, in the backbone's column-indexed reading. -/
theorem iInf_singularValues_tlsWeighted_eq (hmn : n < m) {d : Fin m → ℝ} {t : Fin (n + 1) → ℝ}
    {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ} {U : Matrix (Fin m) (Fin m) ℝ} {σ : ℕ → ℝ}
    {V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hC : IsSVD (tlsMatrix d t A b) U σ V) :
    ⨅ i, (tlsWeighted d (tlsWeights t) A (replicateCol Unit b)).colSingularValues i = σ n := by
  rw [← iInf_colSingularValues_eq_of_isSVD hC hmn, iInf_colSingularValues_eq_iInf_norm,
    iInf_colSingularValues_eq_iInf_norm]
  set e := finSuccEquivSumUnit n
  let E : {x : EuclideanSpace ℝ (Fin (n + 1)) // ‖x‖ = 1} ≃
      {x : EuclideanSpace ℝ (Fin n ⊕ Unit) // ‖x‖ = 1} :=
    { toFun := fun y => ⟨WithLp.toLp 2 (WithLp.ofLp y.1 ∘ e.symm), by
        rw [norm_toLp_comp_equiv, WithLp.toLp_ofLp]; exact y.2⟩
      invFun := fun x => ⟨WithLp.toLp 2 (WithLp.ofLp x.1 ∘ e.symm.symm), by
        rw [norm_toLp_comp_equiv, WithLp.toLp_ofLp]; exact x.2⟩
      left_inv := fun y => by
        ext i
        simp
      right_inv := fun x => by
        ext i
        simp }
  refine (Equiv.iInf_congr E fun y => ?_).symm
  change ‖toEuclideanLin (tlsWeighted d (tlsWeights t) A (replicateCol Unit b))
      (WithLp.toLp 2 (WithLp.ofLp y.1 ∘ e.symm))‖ = ‖toEuclideanLin (tlsMatrix d t A b) y.1‖
  rw [toEuclideanLin_apply, toEuclideanLin_toLp, tlsMatrix_mulVec]

/-- **§6.3.2, the single right-hand side.** "Suppose the singular values of `C` satisfy
`σ_{n−p} > σ_{n−p+1} = ⋯ = σ_{n+1}` and let `V = [v₁ | ⋯ | v_{n+1}]` be a column partitioning of
`V`. If `Q̃` is a Householder matrix such that `V(:, n+1−p : n+1) Q̃ = [W z; 0 α]`, then the last
column of this matrix has the largest `(n+1)`st component of all the vectors in
`span{v_{n+1−p}, …, v_{n+1}}`. If `α = 0`, then the TLS problem has no solution. Otherwise
`x_TLS = −T₁z/(t_{n+1}α)`. Moreover, … `D[E₀ | r₀]T = −D[A | b]T [z; α][zᵀ | α]`."

Here `C = D[A | b]T` is `tlsMatrix d t A b` (`m > n`) with an SVD `UᵀCV = Σ`; `r` is the
0-based index `n − p` of `v_{n+1−p}`, so `σ_j > σ_n` for `j < r` and `σ_r = σ_n`; the vectors of
the span are `V(:, r:n) y`; `Q̃` is any orthogonal matrix with the zero pattern (a Householder
matrix is one). Part (a) is stated for unit `y`, (b) and (c) through the backbone's TLS problem
with weights `d`, `tlsWeights t`. The book's display
`[I_{n−1} 0; 0 Q̃] Uᵀ(D[A|b]T) V [I_{n−p} 0; 0 Q̃] = Σ` has mismatched block sizes and is not
stated. -/
theorem tls_single (hmn : n < m) {d : Fin m → ℝ} (hd : ∀ i, d i ≠ 0) {t : Fin (n + 1) → ℝ}
    (ht : ∀ j, t j ≠ 0) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    {U : Matrix (Fin m) (Fin m) ℝ} {σ : ℕ → ℝ} {V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hC : IsSVD (tlsMatrix d t A b) U σ V) {r : ℕ} (hr : r ≤ n) (hgap : ∀ j < r, σ n < σ j)
    (heq : σ r = σ n) {Q : Matrix (Fin (n + 1 - r)) (Fin (n + 1 - r)) ℝ}
    (hQ : Q ∈ orthogonalGroup (Fin (n + 1 - r)) ℝ)
    (hW : ∀ j : Fin (n + 1 - r), (j : ℕ) < n - r → (trailingColumns V r * Q) (Fin.last n) j = 0) :
    (∀ y : Fin (n + 1 - r) → ℝ, y ⬝ᵥ y = 1 →
      |(trailingColumns V r *ᵥ y) (Fin.last n)| ≤
        |(trailingColumns V r * Q) (Fin.last n) ⟨n - r, by omega⟩|) ∧
    ((trailingColumns V r * Q) (Fin.last n) ⟨n - r, by omega⟩ = 0 →
      ¬ ∃ X, IsTLSSolution d (tlsWeights t) A (replicateCol Unit b) X) ∧
    ((trailingColumns V r * Q) (Fin.last n) ⟨n - r, by omega⟩ ≠ 0 →
      ∃ E R, IsTLSPerturbation d (tlsWeights t) A (replicateCol Unit b) E R ∧
        (A + E) * replicateCol Unit (fun j =>
          -(t (Fin.castSucc j) * (trailingColumns V r * Q) (Fin.castSucc j) ⟨n - r, by omega⟩) /
            (t (Fin.last n) * (trailingColumns V r * Q) (Fin.last n) ⟨n - r, by omega⟩)) =
          replicateCol Unit b + R ∧
        tlsWeighted d (tlsWeights t) E R =
          -vecMulVec (tlsWeighted d (tlsWeights t) A (replicateCol Unit b) *ᵥ
            fun x => (trailingColumns V r * Q) ((finSuccEquivSumUnit n).symm x) ⟨n - r, by omega⟩)
            fun x => (trailingColumns V r * Q) ((finSuccEquivSumUnit n).symm x)
              ⟨n - r, by omega⟩) := by
  set e := finSuccEquivSumUnit n with he
  set Vt := trailingColumns V r with hVt
  set W := Vt * Q with hWdef
  set l : Fin (n + 1 - r) := ⟨n - r, by omega⟩ with hl
  have hV := hC.mem_unitaryGroup_right
  have hQQ : Q * Qᵀ = 1 := by
    have := mem_unitaryGroup_iff.1 hQ
    rwa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at this
  have hQQ' : Qᵀ * Q = 1 := by
    have := mem_unitaryGroup_iff'.1 hQ
    rwa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at this
  have heqall : ∀ j : Fin (n + 1), r ≤ (j : ℕ) → σ j = σ n := fun j hj =>
    le_antisymm (heq ▸ hC.antitone hj) (hC.antitone (Nat.le_of_lt_succ j.isLt))
  have hinf := iInf_singularValues_tlsWeighted_eq hmn hC
  have ht' := tlsWeights_ne_zero ht
  -- (a)
  have ha : ∀ y : Fin (n + 1 - r) → ℝ, y ⬝ᵥ y = 1 →
      |(Vt *ᵥ y) (Fin.last n)| ≤ |W (Fin.last n) l| := by
    intro y hy
    have hVtW : Vt = W * Qᵀ := by rw [hWdef, Matrix.mul_assoc, hQQ, Matrix.mul_one]
    set u := Qᵀ *ᵥ y with hu
    have hu1 : u ⬝ᵥ u = 1 := by
      rw [hu, dotProduct_mulVec_self_of_transpose_mul_self (by rwa [transpose_transpose]), hy]
    have hlast : (Vt *ᵥ y) (Fin.last n) = W (Fin.last n) l * u l := by
      rw [hVtW, ← mulVec_mulVec, ← hu, mulVec, dotProduct, Finset.sum_eq_single l]
      · intro j _ hj
        rw [hW j (by have := j.isLt; have : (j : ℕ) ≠ n - r := fun h => hj (Fin.ext h); omega),
          zero_mul]
      · simp
    have hul : u l ^ 2 ≤ 1 := by
      rw [← hu1, dotProduct]
      have := Finset.single_le_sum (f := fun k => u k * u k) (fun k _ => mul_self_nonneg (u k))
        (Finset.mem_univ l)
      simpa [sq] using this
    rw [hlast, abs_mul]
    have : |u l| ≤ 1 := by
      rw [← sq_le_one_iff_abs_le_one]
      exact hul
    exact mul_le_of_le_one_right (abs_nonneg _) this
  refine ⟨ha, fun hα => ?_, fun hα => ?_⟩
  · -- (b)
    refine not_isTLSSolution_of_forall_last_eq_zero hd ht' fun w' hw' hmin => ?_
    set w : Fin (n + 1) → ℝ := w' ∘ e with hw
    have hw'w : w' = w ∘ e.symm := by
      funext x
      simp [hw]
    have hw1 : w ⬝ᵥ w = 1 := by
      rw [dotProduct_self_eq_norm_sq, ← norm_toLp_comp_equiv e, ← hw'w, hw', one_pow]
    have hCw : (tlsMatrix d t A b *ᵥ w) ⬝ᵥ (tlsMatrix d t A b *ᵥ w) = σ n ^ 2 * (w ⬝ᵥ w) := by
      rw [hw1, mul_one, dotProduct_self_eq_norm_sq, tlsMatrix_mulVec, ← hw'w, hmin, hinf]
    obtain ⟨y, hwy, hy⟩ := exists_eq_trailingColumns_mulVec hV
      (coord_eq_zero_of_mulVec_dotProduct_self hC hmn hgap hCw)
    have h2 := ha y (hy.trans hw1)
    rw [hVt, ← hwy, hα, abs_zero] at h2
    rw [hw'w]
    exact abs_nonpos_iff.1 h2
  · -- (c)
    set w : Fin (n + 1) → ℝ := fun i => W i l with hw
    have hwV : w = Vt *ᵥ Q.col l := by
      funext i
      rfl
    have hw1 : w ⬝ᵥ w = 1 := by
      rw [hwV,
        dotProduct_mulVec_self_of_transpose_mul_self (trailingColumns_transpose_mul_self hV r)]
      have := congrFun (congrFun hQQ' l) l
      rw [mul_apply, one_apply_eq] at this
      rw [← this]
      rfl
    have hCw : (tlsMatrix d t A b *ᵥ w) ⬝ᵥ (tlsMatrix d t A b *ᵥ w) = σ n ^ 2 * (w ⬝ᵥ w) :=
      mulVec_dotProduct_self_of_coord_eq_zero hC hmn heqall (by
        rw [hwV]; exact coord_trailingColumns_mulVec hV r _)
    rw [hw1, mul_one] at hCw
    have hunit : ‖(WithLp.toLp 2 (w ∘ e.symm) : EuclideanSpace ℝ (Fin n ⊕ Unit))‖ = 1 := by
      rw [norm_toLp_comp_equiv]
      refine (sq_eq_sq₀ (norm_nonneg _) zero_le_one).1 ?_
      rw [← dotProduct_self_eq_norm_sq, hw1, one_pow]
    have hmin : ‖(WithLp.toLp 2 (tlsWeighted d (tlsWeights t) A (replicateCol Unit b) *ᵥ
        (w ∘ e.symm)) : EuclideanSpace ℝ (Fin m))‖ =
          ⨅ i, (tlsWeighted d (tlsWeights t) A (replicateCol Unit b)).colSingularValues i := by
      rw [hinf, ← tlsMatrix_mulVec]
      refine (sq_eq_sq₀ (norm_nonneg _) (hC.nonneg n)).1 ?_
      rw [← dotProduct_self_eq_norm_sq, hCw]
    obtain ⟨E, R, hP, hsol, hER⟩ := isTLSSolution_of_mem_smallest hd ht' hunit hmin hα
    refine ⟨E, R, hP, ?_, ?_⟩
    · convert hsol using 4
      simp only [Function.comp_apply, tlsWeights, Sum.elim_inl, Sum.elim_inr,
        RCLike.ofReal_real_eq_id, id_eq]
      rfl
    · rw [hER]
      congr 2
/-- The entries of `C = D[A | b]T`: `c_ij = d_i a_ij t_j`, with `a_{i,n+1} = b_i`. -/
theorem tlsMatrix_apply (d : Fin m → ℝ) (t : Fin (n + 1) → ℝ) (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (i : Fin m) (j : Fin (n + 1)) :
    tlsMatrix d t A b i j = d i * Fin.lastCases (b i) (A i) j * t j := by
  rw [tlsMatrix, submatrix_apply, tlsWeighted, mul_diagonal, diagonal_mul]
  refine Fin.lastCases ?_ (fun j => ?_) j <;>
    simp [finSuccEquivSumUnit, tlsWeights]

/-- The start `r` of the run of computed singular values equal to the last one,
`σ_r = ⋯ = σ_n` (0-based), found by exact comparisons: the book's `n − p`. -/
noncomputable def tailStart (σ : ℕ → ℝ) (n : ℕ) : ℕ :=
  open Classical in n + 1 - ((Finset.range (n + 1)).filter fun j => σ j = σ n).card

/-- For sorted values, `σ_j = σ_n` exactly from `tailStart σ n` on. -/
private theorem eq_iff_tailStart_le {σ : ℕ → ℝ} (hσ : Antitone σ) {j : ℕ} (hj : j ≤ n) :
    σ j = σ n ↔ tailStart σ n ≤ j := by
  classical
  unfold tailStart
  constructor
  · intro h
    have hsub : Finset.Icc j n ⊆ (Finset.range (n + 1)).filter fun k => σ k = σ n := by
      intro k hk
      rw [Finset.mem_Icc] at hk
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, le_antisymm (h ▸ hσ hk.1) (hσ hk.2)⟩
    have := Finset.card_le_card hsub
    rw [Nat.card_Icc] at this
    omega
  · intro h
    by_contra hne
    have hsub : ((Finset.range (n + 1)).filter fun k => σ k = σ n) ⊆ Finset.Ioc j n := by
      intro k hk
      rw [Finset.mem_filter, Finset.mem_range] at hk
      rw [Finset.mem_Ioc]
      refine ⟨?_, by omega⟩
      by_contra hkj
      have h1 : σ j ≤ σ k := hσ (not_lt.1 hkj)
      rw [hk.2] at h1
      exact hne (le_antisymm h1 (hσ hj))
    have := Finset.card_le_card hsub
    rw [Nat.card_Ioc] at this
    omega

/-- The book's `p`: the run `σ_{r} = ⋯ = σ_n` starts at `r ≤ n`, is preceded by larger values, and
`σ_r = σ_n`. -/
theorem tailStart_spec {σ : ℕ → ℝ} (hσ : Antitone σ) :
    tailStart σ n ≤ n ∧ (∀ j < tailStart σ n, σ n < σ j) ∧ σ (tailStart σ n) = σ n := by
  have hn := (eq_iff_tailStart_le (n := n) (j := n) hσ le_rfl).1 rfl
  refine ⟨hn, fun j hj => ?_, (eq_iff_tailStart_le hσ hn).2 le_rfl⟩
  refine lt_of_le_of_ne (hσ (by omega)) fun h => ?_
  have := (eq_iff_tailStart_le hσ (by omega)).1 h.symm
  omega

/-- The index list `[n, n − 1, …, r]` of the columns `V(:, r:n)` read backwards, pivot `n`. -/
def tailIndices (n r : ℕ) : List (Fin (n + 1)) :=
  (List.finRange (n + 1)).reverse.filter fun j => r ≤ (j : ℕ)

/-- Membership in `tailIndices n r`. -/
theorem mem_tailIndices {r : ℕ} {j : Fin (n + 1)} : j ∈ tailIndices n r ↔ r ≤ (j : ℕ) := by
  simp [tailIndices]

/-- `tailIndices n r` has no duplicates. -/
theorem tailIndices_nodup (r : ℕ) : (tailIndices n r).Nodup :=
  (List.nodup_reverse.2 (List.nodup_finRange _)).filter _

/-- For `r ≤ n`, `tailIndices n r` is nonempty with head `n`. -/
theorem tailIndices_ne_nil {r : ℕ} (hr : r ≤ n) : tailIndices n r ≠ [] :=
  List.ne_nil_of_mem (mem_tailIndices.2 (by simpa using hr) : Fin.last n ∈ tailIndices n r)

/-- `tailIndices n r` starts with the pivot `n`. -/
private theorem tailIndices_eq_cons {r : ℕ} (hr : r ≤ n) :
    tailIndices n r = Fin.last n ::
      ((List.finRange n).map Fin.castSucc).reverse.filter fun j => r ≤ (j : ℕ) := by
  rw [tailIndices, List.finRange_succ_last, List.reverse_append, List.reverse_singleton,
    List.singleton_append, List.filter_cons_of_pos (by simpa using hr)]

/-- The pivot of `tailIndices n r` is `n`. -/
theorem tailIndices_head {r : ℕ} (hr : r ≤ n) :
    (tailIndices n r).head (tailIndices_ne_nil hr) = Fin.last n := by
  have key : ∀ (l : List (Fin (n + 1))) (hl : l ≠ []) (t : List (Fin (n + 1))),
      l = Fin.last n :: t → l.head hl = Fin.last n := by
    rintro _ _ _ rfl
    rfl
  exact key _ _ _ (tailIndices_eq_cons hr)

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- Forming `C = D[A | b]T` entry by entry, `fl(fl(d_i a_ij) t_j)`. -/
def tlsScale (d : Fin m → ℝ) (t : Fin (n + 1) → ℝ) (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) : M (Matrix (Fin m) (Fin (n + 1)) ℝ) := do
  let C ← (List.finRange m).foldlM (fun (C : Fin m → Fin (n + 1) → ℝ) i => do
    let row ← (List.finRange (n + 1)).foldlM (fun (row : Fin (n + 1) → ℝ) j => do
      let c ← (do let p ← rnd (d i * Fin.lastCases (b i) (A i) j); rnd (p * t j))
      pure (Function.update row j c)) 0
    pure (Function.update C i row)) 0
  pure (Matrix.of C)

/-- **Algorithm 6.3.1 (total least squares, one right-hand side).** "Given `A ∈ ℝ^{m×n}` (`m > n`),
`b ∈ ℝᵐ`, nonsingular `D = diag(d₁, …, d_m)`, and nonsingular `T = diag(t₁, …, t_{n+1})`, the
following algorithm computes (if possible) a vector `x_TLS ∈ ℝⁿ` such that
`(A + E₀)x_TLS = (b + r₀)` and `‖D[E₀ | r₀]T‖_F` is minimal.
```
Compute the SVD Uᵀ(D[A | b]T)V = diag(σ₁, …, σ_{n+1}) and save V.
Determine p such that σ₁ ≥ ⋯ ≥ σ_{n−p} > σ_{n−p+1} = ⋯ = σ_{n+1}.
Compute a Householder P such that if Ṽ = VP, then Ṽ(n+1, n−p+1 : n) = 0.
if ṽ_{n+1,n+1} ≠ 0
    for i = 1:n
        x_i = −t_i ṽ_{i,n+1}/(t_{n+1} ṽ_{n+1,n+1})
    end
    x_TLS = x
end
```"
`D[A | b]T` is formed entry by entry (`tlsScale`); "Compute the SVD" is the parameter `svd`; `p`
is read off the computed `σ` by exact comparisons (`tailStart`, the index `n − p`); the
Householder `P` is chapter 5's `houseOn` on the last row of `V` over the index list
`[n, n−1, …, n−p]` (pivot `n`), applied to the columns of `V` by `householderApplyRight`. The
output is `some x` or, when `ṽ_{n+1,n+1} = 0`, `none`. -/
noncomputable def algorithm_6_3_1
    (svd : Matrix (Fin m) (Fin (n + 1)) ℝ →
      M (Matrix (Fin m) (Fin m) ℝ × (ℕ → ℝ) × Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ))
    (A : Matrix (Fin m) (Fin n) ℝ) (b d : Fin m → ℝ) (t : Fin (n + 1) → ℝ) :
    M (Option (Fin n → ℝ)) := do
  let C ← tlsScale rnd d t A b
  let S ← svd C
  let o := tailIndices n (tailStart S.2.1 n)
  let vβ ← Chapter05.houseOn rnd o (S.2.2 (Fin.last n))
  let W ← Chapter05.householderApplyRight rnd vβ.1 vβ.2 (List.finRange (n + 1)) o S.2.2
  if W (Fin.last n) (Fin.last n) ≠ 0 then do
    let x ← (List.finRange n).foldlM (fun (x : Fin n → ℝ) i => do
      let q ← (do
        let a ← rnd (t (Fin.castSucc i) * W (Fin.castSucc i) (Fin.last n))
        let c ← rnd (t (Fin.last n) * W (Fin.last n) (Fin.last n))
        rnd (-a / c))
      pure (Function.update x i q)) 0
    pure (some x)
  else pure none

end Programs

/-- In exact arithmetic, a loop writing each listed entry from a value independent of the state
writes the listed entries and keeps the others. -/
private theorem idRun_foldlM_update_const {ι β : Type} [DecidableEq ι] (g : ι → Id β)
    (l : List ι) (hl : l.Nodup) (y₀ : ι → β) (i : ι) :
    Id.run (l.foldlM (fun (y : ι → β) a => do
      let b ← g a; pure (Function.update y a b)) y₀) i =
      if i ∈ l then Id.run (g i) else y₀ i :=
  List.idRun_foldlM_update_apply (fun a _ => g a) l hl y₀ i

/-- The pure form of `idRun_foldlM_update_const`. -/
private theorem idRun_foldlM_update_pure {ι β : Type} [DecidableEq ι] (g : ι → β)
    (l : List ι) (hl : l.Nodup) (y₀ : ι → β) (i : ι) :
    Id.run (l.foldlM (fun (y : ι → β) a => pure (Function.update y a (g a))) y₀) i =
      if i ∈ l then g i else y₀ i :=
  idRun_foldlM_update_const (fun a => pure (g a)) l hl y₀ i

/-- In exact arithmetic `tlsScale` forms `D[A | b]T`. -/
theorem tlsScale_spec (d : Fin m → ℝ) (t : Fin (n + 1) → ℝ) (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) : Id.run (tlsScale pure d t A b) = tlsMatrix d t A b := by
  ext i j
  simp only [tlsScale, Id.run_bind, Id.run_pure, of_apply, pure_bind,
    idRun_foldlM_update_const _ _ (List.nodup_finRange _),
    idRun_foldlM_update_pure _ _ (List.nodup_finRange _), List.mem_finRange, ite_true]
  rw [tlsMatrix_apply]

/-- The block of a Householder matrix acting on the columns `r, …, n` is orthogonal, and the
product with the trailing columns agrees with the full product on those columns. -/
private theorem householder_tail {V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {r : ℕ}
    {v : Fin (n + 1) → ℝ} {β : ℝ} (hv : ∀ i : Fin (n + 1), (i : ℕ) < r → v i = 0)
    (hP : (1 - β • vecMulVec v v) ∈ orthogonalGroup (Fin (n + 1)) ℝ) :
    ((1 - β • vecMulVec v v : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ).submatrix
        (fun k : Fin (n + 1 - r) => (⟨r + k, by omega⟩ : Fin (n + 1)))
        (fun k : Fin (n + 1 - r) => (⟨r + k, by omega⟩ : Fin (n + 1)))) ∈
      orthogonalGroup (Fin (n + 1 - r)) ℝ ∧
    ∀ i (k : Fin (n + 1 - r)), (V * (1 - β • vecMulVec v v)) i ⟨r + k, by omega⟩ =
      (trailingColumns V r *
        (1 - β • vecMulVec v v : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ).submatrix
        (fun k : Fin (n + 1 - r) => (⟨r + k, by omega⟩ : Fin (n + 1)))
        (fun k : Fin (n + 1 - r) => (⟨r + k, by omega⟩ : Fin (n + 1)))) i k := by
  set P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := 1 - β • vecMulVec v v with hPdef
  set f : Fin (n + 1 - r) → Fin (n + 1) := fun k => ⟨r + k, by omega⟩ with hf
  have hfinj : Function.Injective f := fun a b hab =>
    Fin.ext (by simpa [hf] using congrArg Fin.val hab)
  have hoff : ∀ l, l ∉ Set.range f → ∀ k, P l (f k) = 0 := by
    intro l hl k
    have hlr : (l : ℕ) < r := by
      by_contra h
      exact hl ⟨⟨l - r, by omega⟩, Fin.ext (by simp only [hf]; omega)⟩
    have hne : l ≠ f k := fun e => by
      have := congrArg Fin.val e
      simp only [hf] at this
      omega
    rw [hPdef, Matrix.sub_apply, one_apply_ne hne, Matrix.smul_apply, vecMulVec_apply, hv l hlr]
    simp
  have hPP : Pᵀ * P = 1 := by
    have := mem_unitaryGroup_iff'.1 hP
    rwa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at this
  refine ⟨?_, fun i k => ?_⟩
  · rw [mem_orthogonalGroup_iff']
    ext k k'
    have h := congrFun (congrFun hPP (f k)) (f k')
    rw [mul_apply] at h
    have e1 : (1 : Matrix (Fin (n + 1 - r)) (Fin (n + 1 - r)) ℝ) k k' =
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (f k) (f k') := by
      simp only [one_apply, hfinj.eq_iff]
    rw [e1, ← h, mul_apply]
    exact Fintype.sum_of_injective f hfinj _ _
      (fun l hl => by rw [transpose_apply, hoff l hl k, zero_mul]) (fun _ => rfl)
  · rw [mul_apply, mul_apply]
    exact (Fintype.sum_of_injective f hfinj _ _ (fun l hl => by rw [hoff l hl k, mul_zero])
      (fun k' => rfl)).symm

/-- **Algorithm 6.3.1 is correct in exact arithmetic**: for `m > n`, nonzero weights and an `svd`
subroutine returning SVDs, the algorithm returns `some x` with `x` a TLS solution of
`(A + E₀)x = b + r₀` (weights `D`, `T`), or `none`, and then the TLS problem has no solution —
"computes (if possible) a vector `x_TLS` such that `(A + E₀)x_TLS = b + r₀` and
`‖D[E₀ | r₀]T‖_F` is minimal". -/
theorem algorithm_6_3_1_spec (hmn : n < m)
    (svd : Matrix (Fin m) (Fin (n + 1)) ℝ →
      Id (Matrix (Fin m) (Fin m) ℝ × (ℕ → ℝ) × Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ))
    (hsvd : ∀ C, IsSVD C (Id.run (svd C)).1 (Id.run (svd C)).2.1 (Id.run (svd C)).2.2)
    {d : Fin m → ℝ} (hd : ∀ i, d i ≠ 0) {t : Fin (n + 1) → ℝ} (ht : ∀ j, t j ≠ 0)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    (∀ x, Id.run (algorithm_6_3_1 pure svd A b d t) = some x →
      IsTLSSolution d (tlsWeights t) A (replicateCol Unit b) (replicateCol Unit x)) ∧
    (Id.run (algorithm_6_3_1 pure svd A b d t) = none →
      ¬ ∃ X, IsTLSSolution d (tlsWeights t) A (replicateCol Unit b) X) := by
  have hS := hsvd (tlsMatrix d t A b)
  generalize hSdef : Id.run (svd (tlsMatrix d t A b)) = S at hS
  obtain ⟨hr, hgap, heq⟩ := tailStart_spec (n := n) hS.antitone
  generalize hrdef : tailStart S.2.1 n = r at hr hgap heq
  have ho := tailIndices_nodup (n := n) r
  have hne := tailIndices_ne_nil hr
  obtain ⟨-, hvoff, -, hPorth, hPx⟩ := Chapter05.houseOn_spec ho hne (S.2.2 (Fin.last n))
  generalize hvβ : Id.run (Chapter05.houseOn pure (tailIndices n r) (S.2.2 (Fin.last n))) = vβ
    at hvoff hPorth hPx
  have hW : Id.run (Chapter05.householderApplyRight pure vβ.1 vβ.2 (List.finRange (n + 1))
      (tailIndices n r) S.2.2) = S.2.2 * (1 - vβ.2 • vecMulVec vβ.1 vβ.1) :=
    Chapter05.householderApplyRight_spec_of_forall_mem (List.nodup_finRange _) ho
      List.mem_finRange hvoff _ _
  set P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := 1 - vβ.2 • vecMulVec vβ.1 vβ.1 with hPdef
  have hrun : Id.run (algorithm_6_3_1 pure svd A b d t) =
      if (S.2.2 * P) (Fin.last n) (Fin.last n) ≠ 0 then
        some (fun i => -(t (Fin.castSucc i) * (S.2.2 * P) (Fin.castSucc i) (Fin.last n)) /
          (t (Fin.last n) * (S.2.2 * P) (Fin.last n) (Fin.last n)))
      else none := by
    simp only [algorithm_6_3_1, Id.run_bind, tlsScale_spec, hSdef, hrdef, hvβ, hW]
    split_ifs with h
    · simp only [Id.run_bind, Id.run_pure]
      congr 1
      funext i
      simp only [pure_bind, idRun_foldlM_update_pure _ _ (List.nodup_finRange n),
        List.mem_finRange, ite_true]
    · rfl
  obtain ⟨hQ, hsub⟩ := householder_tail (V := S.2.2) (r := r)
    (fun i hi => hvoff i (by rw [mem_tailIndices]; omega)) hPorth
  have hPt : Pᵀ = P := transpose_one_sub_smul_vecMulVec _ _
  have hrow : ∀ j, (S.2.2 * P) (Fin.last n) j = (P *ᵥ S.2.2 (Fin.last n)) j := by
    intro j
    conv_rhs => rw [← hPt, mulVec_transpose]
    rfl
  have hWz : ∀ j : Fin (n + 1 - r), (j : ℕ) < n - r →
      (trailingColumns S.2.2 r * P.submatrix
        (fun k : Fin (n + 1 - r) => (⟨r + k, by omega⟩ : Fin (n + 1)))
        (fun k : Fin (n + 1 - r) => (⟨r + k, by omega⟩ : Fin (n + 1)))) (Fin.last n) j = 0 := by
    intro j hj
    rw [← hsub, hrow, hPx, tailIndices_head hr]
    dsimp only
    rw [ite_eq_right (fun e => by
      have := congrArg Fin.val e; simp at this; omega),
      ite_eq_left (mem_tailIndices.2 (by simp))]
  obtain ⟨-, hb, hc⟩ := tls_single hmn hd ht A b hS hr hgap heq hQ hWz
  have hcol : ∀ i, (trailingColumns S.2.2 r * P.submatrix
      (fun k : Fin (n + 1 - r) => (⟨r + k, by omega⟩ : Fin (n + 1)))
      (fun k : Fin (n + 1 - r) => (⟨r + k, by omega⟩ : Fin (n + 1)))) i ⟨n - r, by omega⟩ =
        (S.2.2 * P) i (Fin.last n) := by
    intro i
    rw [← hsub]
    have hfl : ∀ h, (⟨r + (n - r), h⟩ : Fin (n + 1)) = Fin.last n := fun h =>
      Fin.ext (by simp only [Fin.val_last]; omega)
    exact congrArg _ (hfl _)
  rw [hrun]
  split_ifs with h
  · refine ⟨fun x hx => ?_, fun hx => absurd hx (by simp)⟩
    obtain rfl := (Option.some.inj hx).symm
    obtain ⟨E, R, hP', hsol, -⟩ := hc (by rwa [hcol])
    refine ⟨E, R, hP', ?_⟩
    simp only [hPdef] at hcol ⊢
    simpa only [hcol] using hsol
  · refine ⟨fun x hx => absurd hx (by simp), fun _ => hb ?_⟩
    rw [hcol]
    exact not_not.1 h

/-! ### §6.3.3 A geometric interpretation -/

/-- The normal `[x; −1]` of the subspace `P_x` against a vector `w`. -/
private theorem snoc_neg_one_dotProduct (x : Fin n → ℝ) (w : Fin (n + 1) → ℝ) :
    (Fin.snoc x (-1) : Fin (n + 1) → ℝ) ⬝ᵥ w =
      (x ⬝ᵥ fun j => w (Fin.castSucc j)) - w (Fin.last n) := by
  rw [dotProduct, Fin.sum_univ_castSucc, Fin.snoc_last, dotProduct]
  simp only [Fin.snoc_castSucc]
  ring

/-- The weighted squared length of the normal `[x; −1]`. -/
private theorem sum_snoc_neg_one_div_sq (x : Fin n → ℝ) (t : Fin (n + 1) → ℝ) :
    ∑ j, ((Fin.snoc x (-1) : Fin (n + 1) → ℝ) j / t j) ^ 2 =
      ∑ j : Fin n, x j ^ 2 / t (Fin.castSucc j) ^ 2 + 1 / t (Fin.last n) ^ 2 := by
  rw [Fin.sum_univ_castSucc, Fin.snoc_last]
  simp only [Fin.snoc_castSucc, div_pow, neg_one_sq]

/-- **§6.3.3, the geometric interpretation.** "`δᵢ = |aᵢᵀx − bᵢ|² / (xᵀT₁⁻²x + t_{n+1}⁻²)` is the
square of the distance from `[aᵢ; bᵢ] ∈ ℝ^{n+1}` to the nearest point in the subspace
`P_x = {[a; b] : a ∈ ℝⁿ, b ∈ ℝ, b = xᵀa}` where the distance in `ℝ^{n+1}` is measured by the norm
`‖z‖ = ‖Tz‖₂`", and the nearest point exists. -/
theorem tls_distance {t : Fin (n + 1) → ℝ} (ht : ∀ j, t j ≠ 0) (a : Fin n → ℝ) (β : ℝ)
    (x : Fin n → ℝ) :
    (⨅ w : {w : Fin (n + 1) → ℝ // w (Fin.last n) = x ⬝ᵥ fun j => w (Fin.castSucc j)},
        ‖(WithLp.toLp 2 (diagonal t *ᵥ ((Fin.snoc a β : Fin (n + 1) → ℝ) - w.1)) :
          EuclideanSpace ℝ (Fin (n + 1)))‖ ^ 2) =
      |a ⬝ᵥ x - β| ^ 2 /
        (∑ j : Fin n, x j ^ 2 / t (Fin.castSucc j) ^ 2 + 1 / t (Fin.last n) ^ 2) ∧
    ∃ w : Fin (n + 1) → ℝ, w (Fin.last n) = (x ⬝ᵥ fun j => w (Fin.castSucc j)) ∧
      ‖(WithLp.toLp 2 (diagonal t *ᵥ ((Fin.snoc a β : Fin (n + 1) → ℝ) - w)) :
          EuclideanSpace ℝ (Fin (n + 1)))‖ ^ 2 =
        |a ⬝ᵥ x - β| ^ 2 /
          (∑ j : Fin n, x j ^ 2 / t (Fin.castSucc j) ^ 2 + 1 / t (Fin.last n) ^ 2) := by
  have hν : (Fin.snoc x (-1) : Fin (n + 1) → ℝ) ≠ 0 := fun h => by
    have := congrFun h (Fin.last n)
    rw [Fin.snoc_last, Pi.zero_apply] at this
    norm_num at this
  have hiff : ∀ w : Fin (n + 1) → ℝ, w (Fin.last n) = (x ⬝ᵥ fun j => w (Fin.castSucc j)) ↔
      (Fin.snoc x (-1) : Fin (n + 1) → ℝ) ⬝ᵥ w = 0 := fun w => by
    rw [snoc_neg_one_dotProduct, sub_eq_zero, eq_comm]
  have hnum : ((Fin.snoc x (-1) : Fin (n + 1) → ℝ) ⬝ᵥ (Fin.snoc a β : Fin (n + 1) → ℝ)) ^ 2 =
      |a ⬝ᵥ x - β| ^ 2 := by
    rw [snoc_neg_one_dotProduct, sq_abs, Fin.snoc_last]
    simp only [Fin.snoc_castSucc]
    rw [dotProduct_comm]
  obtain ⟨h1, w, hw, h2⟩ :=
    iInf_sq_norm_diagonal_mulVec_sub_hyperplane ht hν (Fin.snoc a β : Fin (n + 1) → ℝ)
  rw [hnum, sum_snoc_neg_one_div_sq] at h1 h2
  refine ⟨?_, w, (hiff w).2 hw, h2⟩
  rw [← h1]
  exact Equiv.iInf_congr (Equiv.subtypeEquivRight hiff) fun _ => rfl

end GolubVanLoan.Chapter06
