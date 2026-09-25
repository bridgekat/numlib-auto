import Numlib.Eigen.ImplicitRestart
import NumlibSurface.GolubVanLoan.Chapter10.Section01

/-!
# Golub–Van Loan §10.5: Krylov methods for unsymmetric problems

Surface file for Gene H. Golub and Charles F. Van Loan, *Matrix Computations*, 4th edition, §10.5:
Algorithm 10.5.1 (Arnoldi with the modified Gram–Schmidt inner loop), (10.5.1)–(10.5.2) and the
definition of a `k`-step Arnoldi decomposition, the Ritz pair and its backward error, implicit
restarting (10.5.4)–(10.5.9) with Theorem 10.5.1, the Krylov–Schur restart, and the block
biorthogonality step (10.5.14)–(10.5.16).

## Conventions

The chapter's (`GolubVanLoan.Chapter10.Section01`): `A : Matrix (Fin n) (Fin n) ℝ` acting on
`EuclideanSpace ℝ (Fin n)` through `Matrix.toEuclideanLin`, `0`-based indices, `Q_k` is
`Arnoldi.basisMatrix A q₁ k`, `H_k` is `Arnoldi.hessenbergSq _ q₁ k`, `r_k` is
`(Arnoldi.w _ q₁ (k − 1)).ofLp`, `e_k` is `Krylov.lastVec 1 k`. The book's `k`-step Arnoldi
decomposition `IsArnoldiDecomposition` has `k` columns; the backbone's
`Matrix.IsArnoldiDecomposition` counts `k + 1` (`isArnoldiDecomposition_iff`), so in the
restarting statements the book's `m` and `j` are the backbone's `m + 1` and `j + 1`. The shifted QR
steps (10.5.4) are the backbone's `Matrix.IsShiftedQrChain Hs V R μ p` (the book's `H^{(i)}`,
`V_i`, `R_i`, `μ_{i+1}` are `Hs i`, `V i`, `R i`, `μ i`), with `V = V_0 ⋯ V_{p−1}` and
`R = R_{p−1} ⋯ R_0` as list products.

## Not formalized

The filter-polynomial eigen-expansion of (10.5.3), the exact-shift heuristic, the look-ahead idea
of §10.5.6, operation counts. The Givens program (10.5.4) and the restart loops (10.5.10) and
§10.5.3 wait for chapter 5's Givens QR (Algorithm 5.2.5); the statements about shifted QR chains
below hold for every chain with the properties the program's run has.
-/

open scoped Matrix
open Krylov FloatingPoint Polynomial
open GolubVanLoan.Chapter01

namespace GolubVanLoan.Chapter10

variable {n : ℕ}

/-! ### Arnoldi decompositions (§10.5.1) -/

/-- **A `k`-step Arnoldi decomposition** (§10.5.1, the definition after (10.5.2)):
`A Q_k = Q_k H_k + r_k e_kᵀ` with `Q_k ∈ ℝ^{n×k}` having orthonormal columns, `H_k` upper Hessenberg
and `Q_kᵀ r_k = 0`. -/
structure IsArnoldiDecomposition {k : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (Q : Matrix (Fin n) (Fin k) ℝ) (H : Matrix (Fin k) (Fin k) ℝ) (r : Fin n → ℝ) : Prop where
  /-- `Q_kᵀ Q_k = I_k`. -/
  transpose_mul_self : Qᵀ * Q = 1
  /-- `H_k` is upper Hessenberg. -/
  isUpperHessenberg : H.IsUpperHessenberg
  /-- `Q_kᵀ r_k = 0`. -/
  transpose_mulVec : Qᵀ *ᵥ r = 0
  /-- `A Q_k = Q_k H_k + r_k e_kᵀ`. -/
  mul_eq : A * Q = Q * H + Matrix.vecMulVec r (Krylov.lastVec (1 : ℝ) k)

/-- **The book's Arnoldi decomposition is the backbone's**: for `Q` with `k + 1` columns,
`IsArnoldiDecomposition A Q H r ↔ Matrix.IsArnoldiDecomposition A Q H r` (over `ℝ` the conjugate
transpose is the transpose, and `e_{k+1} = Pi.single (Fin.last k) 1` by `Krylov.lastVec_succ`). -/
theorem isArnoldiDecomposition_iff {k : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    {Q : Matrix (Fin n) (Fin (k + 1)) ℝ} {H : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ}
    {r : Fin n → ℝ} :
    IsArnoldiDecomposition A Q H r ↔ Matrix.IsArnoldiDecomposition A Q H r := by
  constructor
  · intro h
    exact ⟨⟨by rw [Matrix.conjTranspose_eq_transpose_of_trivial]; exact h.transpose_mul_self,
      by rw [Matrix.conjTranspose_eq_transpose_of_trivial]; exact h.transpose_mulVec,
      by rw [h.mul_eq, Krylov.lastVec_succ]⟩, h.isUpperHessenberg⟩
  · intro h
    refine ⟨?_, h.isUpperHessenberg, ?_, ?_⟩
    · rw [← Matrix.conjTranspose_eq_transpose_of_trivial]; exact h.conjTranspose_mul_self
    · rw [← Matrix.conjTranspose_eq_transpose_of_trivial]; exact h.conjTranspose_mulVec
    · rw [h.mul_eq, Krylov.lastVec_succ]

/-- **(10.5.1)**: the Arnoldi vectors span the Krylov subspaces,
`span {q_1, …, q_k} = span {q_1, A q_1, …, A^{k−1} q_1}`: the column space of `Q_k` is that of the
Krylov matrix `K(A, q_1, k)`. Backbone `Arnoldi.range_basisMatrix`, `Matrix.range_krylovMatrix`. -/
theorem equation_10_5_1 (A : Matrix (Fin n) (Fin n) ℝ) (q₁ : EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    LinearMap.range (Matrix.toEuclideanLin (Arnoldi.basisMatrix A q₁ k)) =
      LinearMap.range (Matrix.toEuclideanLin (Matrix.krylovMatrix A q₁.ofLp k)) := by
  rw [Arnoldi.range_basisMatrix, Matrix.range_krylovMatrix, WithLp.toLp_ofLp]

/-- **(10.5.2)**: after `k ≥ 1` steps, `A Q_k = Q_k H_k + r_k e_kᵀ` with `H_k` upper Hessenberg, and
below the grade this is a `k`-step Arnoldi decomposition. Backbone `Arnoldi.mul_basisMatrix`,
`Arnoldi.isArnoldiDecomposition_basisMatrix`. -/
theorem equation_10_5_2 (A : Matrix (Fin n) (Fin n) ℝ) (q₁ : EuclideanSpace ℝ (Fin n)) {k : ℕ}
    (hk : 1 ≤ k) :
    A * Arnoldi.basisMatrix A q₁ k =
        Arnoldi.basisMatrix A q₁ k * Arnoldi.hessenbergSq (Matrix.toEuclideanLin A) q₁ k +
          Matrix.vecMulVec (Arnoldi.w (Matrix.toEuclideanLin A) q₁ (k - 1)).ofLp
            (Krylov.lastVec (1 : ℝ) k) ∧
      (Arnoldi.hessenbergSq (Matrix.toEuclideanLin A) q₁ k).IsUpperHessenberg ∧
      (k ≤ grade (Matrix.toEuclideanLin A) q₁ →
        IsArnoldiDecomposition A (Arnoldi.basisMatrix A q₁ k)
          (Arnoldi.hessenbergSq (Matrix.toEuclideanLin A) q₁ k)
          (Arnoldi.w (Matrix.toEuclideanLin A) q₁ (k - 1)).ofLp) := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  refine ⟨by simpa using Arnoldi.mul_basisMatrix A q₁ k,
    Arnoldi.hessenbergSq_isUpperHessenberg _ q₁ _, fun hg => ?_⟩
  rw [Nat.add_sub_cancel, isArnoldiDecomposition_iff]
  exact Arnoldi.isArnoldiDecomposition_basisMatrix A q₁ hg

/-- The residual of an Arnoldi Ritz pair: if `H_{k+1} y = λ y` then `A (Q y) − λ Q y = y_{k+1} r`,
the last entry of `y` times the residual `w_k`. -/
theorem arnoldi_residual_eq (A : Matrix (Fin n) (Fin n) ℝ) (q₁ : EuclideanSpace ℝ (Fin n))
    (k : ℕ) {y : Fin (k + 1) → ℝ} {θ : ℝ}
    (hy : (Arnoldi.hessenbergSq (Matrix.toEuclideanLin A) q₁ (k + 1)) *ᵥ y = θ • y) :
    Matrix.toEuclideanLin A (WithLp.toLp 2 (Arnoldi.basisMatrix A q₁ (k + 1) *ᵥ y)) -
        θ • WithLp.toLp 2 (Arnoldi.basisMatrix A q₁ (k + 1) *ᵥ y) =
      y (Fin.last k) • Arnoldi.w (Matrix.toEuclideanLin A) q₁ k := by
  rw [toLp_basisMatrix_mulVec, Arnoldi.apply_sub_smul_sum_eq _ q₁ k _ _ hy,
    Arnoldi.coeff_succ_self, Arnoldi.vec_succ_eq]
  rcases eq_or_ne (Arnoldi.w (Matrix.toEuclideanLin A) q₁ k) 0 with h0 | h0
  · simp [h0]
  · have hn : ‖Arnoldi.w (Matrix.toEuclideanLin A) q₁ k‖ ≠ 0 := norm_ne_zero_iff.2 h0
    simp only [RCLike.ofReal_real_eq_id, id, smul_smul]
    congr 1
    field_simp

open scoped Matrix.Norms.L2Operator in
/-- The spectral norm of a rank-one matrix: `‖v xᵀ‖₂ = ‖v‖₂ ‖x‖₂`. -/
theorem l2_opNorm_vecMulVec {m : ℕ} (v : Fin n → ℝ) (x : Fin m → ℝ) :
    ‖Matrix.vecMulVec v x‖ =
      ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖ *
        ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin m))‖ := by
  have happ : ∀ z : Fin m → ℝ, Matrix.vecMulVec v x *ᵥ z = (x ⬝ᵥ z) • v := by
    intro z
    ext i
    simp only [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
    simp_rw [mul_assoc, ← Finset.mul_sum]
    ring
  refine le_antisymm ?_ ?_
  · rw [Matrix.l2_opNorm_def]
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun z => ?_
    change ‖(WithLp.toLp 2 (Matrix.vecMulVec v x *ᵥ z.ofLp) : EuclideanSpace ℝ (Fin n))‖ ≤ _
    rw [happ, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs]
    have hcs : |x ⬝ᵥ z.ofLp| ≤ ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin m))‖ * ‖z‖ := by
      have := abs_real_inner_le_norm (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin m)) z
      rwa [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm] at this
    calc |x ⬝ᵥ z.ofLp| * ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖
        ≤ ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin m))‖ * ‖z‖ *
            ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖ :=
          mul_le_mul_of_nonneg_right hcs (norm_nonneg _)
      _ = _ := by ring
  · set X : EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 x
    have h := Matrix.l2_opNorm_mulVec (Matrix.vecMulVec v x) X
    have hx : x ⬝ᵥ x = ‖X‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
    change ‖(WithLp.toLp 2 (Matrix.vecMulVec v x *ᵥ x) : EuclideanSpace ℝ (Fin n))‖ ≤ _ at h
    rw [happ, hx, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] at h
    rcases eq_or_ne ‖X‖ 0 with h0 | h0
    · rw [h0, mul_zero]
      exact norm_nonneg _
    · have hpos : 0 < ‖X‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
      nlinarith [norm_nonneg (Matrix.vecMulVec v x)]

open scoped Matrix.Norms.L2Operator in
/-- **Ritz pairs of an Arnoldi decomposition and their backward error** (§10.5.1, after the
definition): for `1 ≤ k ≤ m` (the grade), if `H_k y = λ y` with `‖y‖₂ = 1` and `x = Q_k y`, then
`(A − λI) x = (e_kᵀ y) r_k`, `(λ, x)` is a Ritz pair for `A` with respect to `𝒦(A, q₁, k)`, and
`(A + E) x = λ x` with `E = −v xᵀ`, `v = (e_kᵀ y) r_k`, where `‖E‖₂ = |y_k| ‖r_k‖₂`. Real eigenpairs
of `H_k`, as in the book. Backbone `Arnoldi.isRitzPair_of_mulVec_eq_smul`,
`Arnoldi.apply_sub_smul_sum_eq`. -/
theorem arnoldi_ritzPair_backwardError (A : Matrix (Fin n) (Fin n) ℝ)
    (q₁ : EuclideanSpace ℝ (Fin n)) {k : ℕ} (hk1 : 1 ≤ k)
    (hk : k ≤ grade (Matrix.toEuclideanLin A) q₁) {y : EuclideanSpace ℝ (Fin k)} (hy1 : ‖y‖ = 1)
    {θ : ℝ} (hy : (Arnoldi.hessenbergSq (Matrix.toEuclideanLin A) q₁ k) *ᵥ y.ofLp = θ • y.ofLp) :
    let x := Arnoldi.basisMatrix A q₁ k *ᵥ y.ofLp
    let r := (Arnoldi.w (Matrix.toEuclideanLin A) q₁ (k - 1)).ofLp
    let v := y.ofLp ⟨k - 1, by omega⟩ • r
    A *ᵥ x - θ • x = v ∧
      Krylov.IsRitzPair (Matrix.toEuclideanLin A) (Krylov.subspace (Matrix.toEuclideanLin A) q₁ k)
        θ (WithLp.toLp 2 x) ∧
      (A + -Matrix.vecMulVec v x) *ᵥ x = θ • x ∧
      ‖-Matrix.vecMulVec v x‖ =
        |y.ofLp ⟨k - 1, by omega⟩| * ‖(WithLp.toLp 2 r : EuclideanSpace ℝ (Fin n))‖ := by
  intro x r v
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hlast : (⟨k + 1 - 1, by omega⟩ : Fin (k + 1)) = Fin.last k := Fin.ext (by simp)
  have hres := arnoldi_residual_eq A q₁ k hy
  have hx1 : ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))‖ = 1 := by
    change ‖(WithLp.toLp 2 (Arnoldi.basisMatrix A q₁ (k + 1) *ᵥ y.ofLp) :
      EuclideanSpace ℝ (Fin n))‖ = 1
    rw [toLp_basisMatrix_mulVec, Krylov.norm_sum_smul_vec_eq _ q₁ _
      (fun j hj => absurd (lt_of_lt_of_le j.isLt hk) (not_lt.2 hj))]
    exact hy1
  have hxx : x ⬝ᵥ x = 1 := by
    have := real_inner_self_eq_norm_sq (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))
    rw [hx1, one_pow, EuclideanSpace.inner_eq_star_dotProduct, star_trivial] at this
    exact this
  have h1 : A *ᵥ x - θ • x = v := by
    have := congrArg WithLp.ofLp hres
    simp only [WithLp.ofLp_sub, WithLp.ofLp_smul] at this
    simp only [v, r, Nat.add_sub_cancel]
    exact this
  refine ⟨h1, ?_, ?_, ?_⟩
  · rw [toLp_basisMatrix_mulVec]
    refine Arnoldi.isRitzPair_of_mulVec_eq_smul _ q₁ hk (fun h => ?_) hy
    have : y = 0 := by ext j; simpa using congrFun h j
    rw [this, norm_zero] at hy1
    exact zero_ne_one hy1
  · have hvx : Matrix.vecMulVec v x *ᵥ x = v := by
      ext i
      simp only [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply]
      simp_rw [mul_assoc, ← Finset.mul_sum]
      rw [show ∑ j, x j * x j = x ⬝ᵥ x from rfl, hxx, mul_one]
    rw [Matrix.add_mulVec, Matrix.neg_mulVec, hvx, ← h1]
    abel
  · rw [norm_neg, l2_opNorm_vecMulVec, hx1, mul_one]
    simp only [v, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs]

/-! ### Implicit restarting (§10.5.2–10.5.3) -/

/-- **Theorem 10.5.1.** If `V = V_1 ⋯ V_p` and `R = R_p ⋯ R_1` are defined by (10.5.4), then
`V R = (H_c − μ_1 I) ⋯ (H_c − μ_p I)` (10.5.7) — for any factorizations satisfying the two lines of
(10.5.4) (`Matrix.IsShiftedQrChain`), not only the Givens ones. Backbone
`Matrix.prod_mul_prod_reverse_eq_prod_sub_smul_one` (chapter 7's (7.5.7)). -/
theorem theorem_10_5_1 {m : ℕ} {Hs V R : ℕ → Matrix (Fin m) (Fin m) ℝ} {μ : ℕ → ℝ} {p : ℕ}
    (h : Matrix.IsShiftedQrChain Hs V R μ p) :
    ((List.range p).map V).prod * ((List.range p).reverse.map R).prod =
      ((List.range p).map fun i => Hs 0 - μ i • 1).prod :=
  Matrix.prod_mul_prod_reverse_eq_prod_sub_smul_one h

/-- **(10.5.6)**: with orthogonal `V_i` (Givens QR), `V = V_1 ⋯ V_p` (10.5.5) is orthogonal and
`H₊ = Vᵀ H_c V`. Backbone `Matrix.IsShiftedQrChain.conjTranspose_mul_mul`. -/
theorem equation_10_5_6 {m : ℕ} {Hs V R : ℕ → Matrix (Fin m) (Fin m) ℝ} {μ : ℕ → ℝ} {p : ℕ}
    (h : Matrix.IsShiftedQrChain Hs V R μ p)
    (hV : ∀ i < p, V i ∈ Matrix.orthogonalGroup (Fin m) ℝ) :
    ((List.range p).map V).prod ∈ Matrix.orthogonalGroup (Fin m) ℝ ∧
      Hs p = (((List.range p).map V).prod)ᵀ * Hs 0 * ((List.range p).map V).prod := by
  obtain ⟨h1, h2⟩ := h.conjTranspose_mul_mul hV
  refine ⟨h1, ?_⟩
  rw [h2, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]

/-- A product of upper triangular matrices is upper triangular. -/
private theorem isUpperTriangular_list_prod {m : ℕ} {R : ℕ → Matrix (Fin m) (Fin m) ℝ}
    (l : List ℕ) (hR : ∀ i ∈ l, (R i).IsUpperTriangular) :
    ((l.map R).prod).IsUpperTriangular := by
  induction l with
  | nil => simpa using Matrix.blockTriangular_one
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons]
    exact (hR a List.mem_cons_self).mul (ih fun i hi => hR i (List.mem_cons_of_mem a hi))

/-- The filter polynomial `p(λ) = (λ − μ_1) ⋯ (λ − μ_p)` of (10.5.3). -/
noncomputable def filterPolynomial (μ : ℕ → ℝ) (p : ℕ) : ℝ[X] :=
  ((List.range p).map fun i => X - C (μ i)).prod

/-- `p(M) = (M − μ_1 I) ⋯ (M − μ_p I)` for a square matrix `M`. -/
theorem aeval_filterPolynomial {m : ℕ} (M : Matrix (Fin m) (Fin m) ℝ) (μ : ℕ → ℝ) (p : ℕ) :
    aeval M (filterPolynomial μ p) = ((List.range p).map fun i => M - μ i • 1).prod := by
  rw [filterPolynomial, map_list_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  simp [Algebra.algebraMap_eq_smul_one]

/-- **The filter in the first column** (§10.5.3, after Theorem 10.5.1): with upper triangular `R_i`,
`R = R_p ⋯ R_1` is upper triangular and `V(:, 1) = p(H_c) e₁ / R(1, 1)` — stated without division as
`R(1,1) · V(:, 1) = p(H_c) e₁`, which needs no `R(1,1) ≠ 0` (the book's `c = 1/R(1,1)` assumes it).
Backbone `Matrix.IsShiftedQrChain.mulVec_first`. -/
theorem filter_firstColumn {m : ℕ} {Hs V R : ℕ → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ}
    {μ : ℕ → ℝ} {p : ℕ} (h : Matrix.IsShiftedQrChain Hs V R μ p)
    (hR : ∀ i < p, (R i).IsUpperTriangular) :
    (((List.range p).reverse.map R).prod).IsUpperTriangular ∧
      ((List.range p).reverse.map R).prod 0 0 • (((List.range p).map V).prod *ᵥ Pi.single 0 1) =
        aeval (Hs 0) (filterPolynomial μ p) *ᵥ Pi.single 0 1 :=
  ⟨isUpperTriangular_list_prod _ fun i hi => hR i (List.mem_range.1 (List.mem_reverse.1 hi)),
    by rw [aeval_filterPolynomial]; exact (h.mulVec_first hR).symm⟩

/-- **(10.5.9)**: if `A Q_c = Q_c H_c + r_c e_mᵀ` (10.5.8) is an Arnoldi decomposition and (10.5.4)
is applied to `H_c` with orthogonal `V_i`, then `A Q₊ = Q₊ H₊ + r_c e_mᵀ V` with `Q₊ = Q_c V`, and
`Q₊` has orthonormal columns. Backbone `Matrix.IsKrylovDecomposition.mul_unitary`. -/
theorem equation_10_5_9 {m : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    {Q : Matrix (Fin n) (Fin (m + 1)) ℝ} {H : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ}
    {r : Fin n → ℝ} (hQ : IsArnoldiDecomposition A Q H r)
    {Hs V R : ℕ → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ} {μ : ℕ → ℝ} {p : ℕ}
    (h : Matrix.IsShiftedQrChain Hs V R μ p) (h0 : Hs 0 = H)
    (hV : ∀ i < p, V i ∈ Matrix.orthogonalGroup (Fin (m + 1)) ℝ) :
    A * (Q * ((List.range p).map V).prod) =
        (Q * ((List.range p).map V).prod) * Hs p +
          Matrix.vecMulVec r (Krylov.lastVec (1 : ℝ) (m + 1) ᵥ* ((List.range p).map V).prod) ∧
      (Q * ((List.range p).map V).prod)ᵀ * (Q * ((List.range p).map V).prod) = 1 := by
  obtain ⟨hmem, hconj⟩ := equation_10_5_6 h hV
  have hU : (((List.range p).map V).prod)ᴴ * ((List.range p).map V).prod = 1 := by
    rw [Matrix.conjTranspose_eq_transpose_of_trivial]
    exact (Matrix.mem_orthogonalGroup_iff' _ _).1 hmem
  have hK := Matrix.IsKrylovDecomposition.mul_unitary
    (isArnoldiDecomposition_iff.1 hQ).toIsKrylovDecomposition hU
  have e1 := hK.mul_eq
  have e2 := hK.conjTranspose_mul_self
  rw [Matrix.conjTranspose_eq_transpose_of_trivial, ← h0, ← hconj, ← Krylov.lastVec_succ] at e1
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at e2
  exact ⟨e1, e2⟩

/-- **The restarted starting vector** (§10.5.3, after (10.5.9)): for an Arnoldi decomposition with
`m ≥ 2` columns, `(A − μ I) Q_c e₁ = Q_c (H_c − μ I) e₁` for every `μ`; and after `p < m` shifted QR
steps with upper triangular `R_i`, `q₊ = Q₊(:, 1)` satisfies `R(1,1) · q₊ = p(A) q₁` (the book's
`q₊ = c (A − μ_1 I) ⋯ (A − μ_p I) q₁`, without dividing). Backbone
`Matrix.IsArnoldiDecomposition.aeval_mulVec_first`,
`Matrix.IsArnoldiDecomposition.implicitRestart_first`;
the book's `m` is `j + p + 1` here. -/
theorem restart_firstColumn_eq {j p : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    {Q : Matrix (Fin n) (Fin (j + p + 1)) ℝ} {H : Matrix (Fin (j + p + 1)) (Fin (j + p + 1)) ℝ}
    {r : Fin n → ℝ} (hQ : IsArnoldiDecomposition A Q H r) :
    (0 < j + p → ∀ μ : ℝ, (A - μ • 1) *ᵥ (Q *ᵥ Pi.single 0 1) =
        Q *ᵥ ((H - μ • 1) *ᵥ Pi.single 0 1)) ∧
      ∀ {Hs V R : ℕ → Matrix (Fin (j + p + 1)) (Fin (j + p + 1)) ℝ} {μ : ℕ → ℝ},
        Matrix.IsShiftedQrChain Hs V R μ p → Hs 0 = H → (∀ i < p, (R i).IsUpperTriangular) →
        ((List.range p).reverse.map R).prod 0 0 •
            ((Q * ((List.range p).map V).prod) *ᵥ Pi.single 0 1) =
          aeval A (filterPolynomial μ p) *ᵥ (Q *ᵥ Pi.single 0 1) := by
  have hQ' := isArnoldiDecomposition_iff.1 hQ
  refine ⟨fun hjp μ => ?_, fun hc h0 hR => (hQ'.implicitRestart_first hc h0 hR).symm⟩
  have h := hQ'.aeval_mulVec_first (p := X - C μ) (by
    rw [natDegree_X_sub_C]; omega)
  simpa [Algebra.algebraMap_eq_smul_one] using h

/-- **The truncated Arnoldi decomposition of implicit restarting** (§10.5.3): with upper Hessenberg
orthogonal `V_i` and upper triangular `R_i` (the Givens QR of (10.5.4)), `V` has lower bandwidth `p`
(`V(m, 1 : m−p−1) = 0`), and with `j = m − p` the leading `j` columns give a `j`-step Arnoldi
decomposition `A Q₊(:, 1:j) = Q₊(:, 1:j) H₊(1:j, 1:j) + r₊ e_jᵀ` with residual
`r₊ = h⁺_{j+1,j} Q₊(:, j+1) + v_{mj} r_c`. The book writes the residual as `v_{mj} r_c` and in the
loop "Replace `r_c` with `v_{mj} r_c`", dropping the Hessenberg term `h⁺_{j+1,j} q⁺_{j+1}` (Sorensen
1992 has it). Backbone `Matrix.IsArnoldiDecomposition.implicitRestart`; the book's `m`, `j` are
`j + p + 1`, `j + 1` here. -/
theorem implicitRestart_isArnoldiDecomposition {j p : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    {Q : Matrix (Fin n) (Fin (j + p + 1)) ℝ} {H : Matrix (Fin (j + p + 1)) (Fin (j + p + 1)) ℝ}
    {r : Fin n → ℝ} (hQ : IsArnoldiDecomposition A Q H r)
    {Hs V R : ℕ → Matrix (Fin (j + p + 1)) (Fin (j + p + 1)) ℝ} {μ : ℕ → ℝ}
    (hc : Matrix.IsShiftedQrChain Hs V R μ p) (h0 : Hs 0 = H)
    (hV : ∀ i < p, V i ∈ Matrix.orthogonalGroup (Fin (j + p + 1)) ℝ)
    (hVH : ∀ i < p, (V i).IsUpperHessenberg) (hR : ∀ i < p, (R i).IsUpperTriangular)
    (hp : 0 < p) :
    (((List.range p).map V).prod).HasLowerBandwidth p ∧
      IsArnoldiDecomposition A
        ((Q * ((List.range p).map V).prod).submatrix id
          (Fin.castLE (by omega : j + 1 ≤ j + p + 1)))
        ((Hs p).submatrix (Fin.castLE (by omega : j + 1 ≤ j + p + 1))
          (Fin.castLE (by omega : j + 1 ≤ j + p + 1)))
        (Hs p ⟨j + 1, by omega⟩ ⟨j, by omega⟩ •
            (Q * ((List.range p).map V).prod).col ⟨j + 1, by omega⟩ +
          ((List.range p).map V).prod (Fin.last (j + p)) ⟨j, by omega⟩ • r) :=
  ⟨Matrix.IsShiftedQrChain.hasLowerBandwidth_prod hVH, isArnoldiDecomposition_iff.2
    ((isArnoldiDecomposition_iff.1 hQ).implicitRestart hc h0 hV hVH hR hp)⟩

/-- **The Krylov–Schur restart** (§10.5.4): from an Arnoldi decomposition `A Q_m = Q_m H_m + r_m
e_mᵀ` and an orthogonal `U` with `Uᵀ H_m U = [T₁₁ T₁₂; 0 T₂₂]`, `T₁₁ ∈ ℝ^{j×j}` (the book's "Schur
decomposition of `A`" means of `H_m`; only the block triangularity is used): (a) with `Q₊ = Q_m U`
and `uᵀ = U(m, 1:j)`, `A Q₊(:, 1:j) = Q₊(:, 1:j) T₁₁ + r_m uᵀ` is a Krylov decomposition (the book's
display has `r_c c_mᵀ U` for `r_m e_mᵀ U`); (b) with an orthogonal `Z` such that `Zᵀ T₁₁ Z` is upper
Hessenberg and `Zᵀ u = τ e_j` (P10.5.2, `Matrix.exists_isUpperHessenberg_conj_lastCol`), `A (Q₊ Z) =
(Q₊ Z)(Zᵀ T₁₁ Z) + τ r_m e_jᵀ` is a `j`-step Arnoldi decomposition. Backbone
`Matrix.IsArnoldiDecomposition.krylovSchur`; the book's `m`, `j` are `k + 1`, `j + 1` here. -/
theorem krylovSchur_isArnoldiDecomposition {k : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    {Q : Matrix (Fin n) (Fin (k + 1)) ℝ} {H : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ}
    {r : Fin n → ℝ} (hQ : IsArnoldiDecomposition A Q H r)
    {U : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ} (hU : U ∈ Matrix.orthogonalGroup (Fin (k + 1)) ℝ)
    (j : Fin (k + 1)) (hT : ∀ i l : Fin (k + 1), l ≤ j → j < i → (Uᵀ * H * U) i l = 0) :
    Matrix.IsKrylovDecomposition A ((Q * U).submatrix id (Fin.castLE j.isLt))
        ((Uᵀ * H * U).submatrix (Fin.castLE j.isLt) (Fin.castLE j.isLt)) r
        (fun l => U (Fin.last k) (Fin.castLE j.isLt l)) ∧
      ∃ Z ∈ Matrix.orthogonalGroup (Fin (j + 1)) ℝ, ∃ τ : ℝ,
        IsArnoldiDecomposition A ((Q * U).submatrix id (Fin.castLE j.isLt) * Z)
          (Zᵀ * (Uᵀ * H * U).submatrix (Fin.castLE j.isLt) (Fin.castLE j.isLt) * Z) (τ • r) := by
  have hUs : star U = Uᵀ := by
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
  have hks := (isArnoldiDecomposition_iff.1 hQ).krylovSchur hU j (by rw [hUs]; exact hT)
  rw [hUs] at hks
  refine ⟨hks.1, ?_⟩
  obtain ⟨Z, hZ, hZH, τ, hZu⟩ := Matrix.exists_isUpperHessenberg_conj_lastCol
    ((Uᵀ * H * U).submatrix (Fin.castLE j.isLt) (Fin.castLE j.isLt))
    (star fun l => U (Fin.last k) (Fin.castLE j.isLt l))
  have hZs : star Z = Zᵀ := by
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
  have h := hks.2 Z hZ τ hZH hZu
  rw [hZs, star_trivial] at h
  exact ⟨Z, hZ, τ, isArnoldiDecomposition_iff.2 h⟩

/-! ### Block biorthogonality (§10.5.6) -/

/-- **(10.5.15)–(10.5.16)**, the block step of (10.5.14): if `S_kᵀ R_k` is nonsingular and
`B_k, C_k ∈ ℝ^{p×p}` satisfy `C_kᵀ B_k = S_kᵀ R_k`, then `B_k` and `C_k` are nonsingular and
`Q_{k+1} = R_k B_k⁻¹`, `Q̃_{k+1} = S_k C_k⁻¹` satisfy `Q̃_{k+1}ᵀ Q_{k+1} = I_p`
(`C_k⁻ᵀ (S_kᵀ R_k) B_k⁻¹ = I`). -/
theorem equation_10_5_16 {p : ℕ} {Rk Sk : Matrix (Fin n) (Fin p) ℝ}
    {B C : Matrix (Fin p) (Fin p) ℝ} (hSR : IsUnit (Skᵀ * Rk)) (hCB : Cᵀ * B = Skᵀ * Rk) :
    IsUnit B ∧ IsUnit C ∧ (Sk * C⁻¹)ᵀ * (Rk * B⁻¹) = 1 := by
  rw [← hCB, Matrix.isUnit_iff_isUnit_det, Matrix.det_mul, IsUnit.mul_iff] at hSR
  have hB : IsUnit B := (Matrix.isUnit_iff_isUnit_det B).2 hSR.2
  have hC : IsUnit C := by
    rw [Matrix.isUnit_iff_isUnit_det, ← Matrix.det_transpose]
    exact hSR.1
  refine ⟨hB, hC, ?_⟩
  have hCt : IsUnit Cᵀ.det := by
    rw [Matrix.det_transpose]; exact (Matrix.isUnit_iff_isUnit_det C).1 hC
  rw [Matrix.transpose_mul, Matrix.transpose_nonsing_inv, Matrix.mul_assoc, ← Matrix.mul_assoc Skᵀ,
    ← hCB, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hCt, Matrix.one_mul,
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det B).1 hB)]

/-! ### Algorithm 10.5.1 (the Arnoldi process) -/

/-- The state of Algorithm 10.5.1: the number `k` of Arnoldi vectors computed, the vectors (`q j` is
the book's `q_{j+1}`), the Hessenberg entries (`h i j` is the book's `h_{i+1, j+1}`), the current
residual `r` (the book's `r_k`) and the `done` flag of the `while h_{k+1,k} ≠ 0` loop. -/
structure ArnoldiState (n : ℕ) where
  /-- The book's step counter `k`. -/
  k : ℕ
  /-- The Arnoldi vectors, `0`-based. -/
  q : ℕ → Fin n → ℝ
  /-- The Hessenberg entries, `0`-based. -/
  h : ℕ → ℕ → ℝ
  /-- The residual `r_k`. -/
  r : Fin n → ℝ
  /-- Whether the loop has stopped (`h_{k+1,k} = 0`). -/
  done : Bool

section ArnoldiProgram

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- The modified Gram–Schmidt inner loop of Algorithm 10.5.1: for `i = 1 : k`,
`h_{ik} = q_iᵀ r_k`, `r_k = r_k − h_{ik} q_i`, each coefficient taken against the *current* `r_k`.
Returns the orthogonalized vector and the column of coefficients. -/
def mgsLoop (q : ℕ → Fin n → ℝ) (k : ℕ) (r : Fin n → ℝ) : M ((Fin n → ℝ) × (ℕ → ℝ)) :=
  (List.range k).foldlM (fun (p : (Fin n → ℝ) × (ℕ → ℝ)) i => do
    let c ← algorithm_1_1_1 rnd (q i) p.1
    let v ← algorithm_1_1_2 rnd (-c) (q i) p.1
    pure (v, Function.update p.2 i c)) (r, fun _ => 0)

/-- One pass of the `while` loop of Algorithm 10.5.1 (a no-op once `done`):
```
q_{k+1} = r_k/h_{k+1,k},  k = k + 1,  r_k = A q_k
for i = 1:k: h_{ik} = q_iᵀ r_k, r_k = r_k − h_{ik} q_i
h_{k+1,k} = ‖r_k‖₂
```
with `h_{10} = 1` at the first pass. -/
noncomputable def arnoldiStep (A : Matrix (Fin n) (Fin n) ℝ) (s : ArnoldiState n) :
    M (ArnoldiState n) :=
  if s.done then pure s else do
    let hk : ℝ := if s.k = 0 then 1 else s.h s.k (s.k - 1)
    let qk ← vecDiv rnd s.r hk
    let q := Function.update s.q s.k qk
    let v ← algorithm_1_1_3 rnd A qk 0
    let vh ← mgsLoop rnd q (s.k + 1) v
    let b ← vecNorm rnd vh.1
    pure
      { k := s.k + 1
        q := q
        h := fun i j => if j = s.k then (if i = s.k + 1 then b else vh.2 i) else s.h i j
        r := vh.1
        done := decide (b = 0) }

/-- **Algorithm 10.5.1 (Arnoldi Process).** "If `A ∈ ℝ^{n×n}` and `q₁ ∈ ℝⁿ` has unit 2-norm, then
the following algorithm computes a matrix `Q_t = [q_1 | ⋯ | q_t] ∈ ℝ^{n×t}` with orthonormal columns
and an upper Hessenberg matrix `H_t = (h_{ij}) ∈ ℝ^{t×t}` with the property that `A Q_t = Q_t H_t`":
```
k = 0, r_0 = q₁, h_{10} = 1
while h_{k+1,k} ≠ 0
  q_{k+1} = r_k/h_{k+1,k},  k = k + 1,  r_k = A q_k
  for i = 1:k: h_{ik} = q_iᵀ r_k, r_k = r_k − h_{ik} q_i end
  h_{k+1,k} = ‖r_k‖₂
end
t = k
```
The `while` loop is at most `fuel` passes of `arnoldiStep` (convention 3). -/
noncomputable def algorithm_10_5_1 (A : Matrix (Fin n) (Fin n) ℝ) (q₁ : Fin n → ℝ) (fuel : ℕ) :
    M (ArnoldiState n) :=
  (List.range fuel).foldlM (fun s _ => arnoldiStep rnd A s)
    { k := 0, q := fun _ => 0, h := fun _ _ => 0, r := q₁, done := false }

end ArnoldiProgram

/-- Exact semantics of the modified Gram–Schmidt loop against orthonormal Arnoldi vectors: after
`m` steps from `A v_k`, the vector is the modified Gram–Schmidt sweep and the coefficients below
`m` are the Arnoldi coefficients `h_{ik}`. -/
private theorem mgsLoop_id (A : Matrix (Fin n) (Fin n) ℝ) (q₁ : EuclideanSpace ℝ (Fin n))
    (q : ℕ → Fin n → ℝ) (k m : ℕ)
    (hq : ∀ i < m, q i = (Arnoldi.vec (Matrix.toEuclideanLin A) q₁ i).ofLp) :
    Id.run (mgsLoop pure q m (A *ᵥ (Arnoldi.vec (Matrix.toEuclideanLin A) q₁ k).ofLp)) =
      ((InnerProductSpace.modifiedGramSchmidtSweep ℝ (Arnoldi.vec (Matrix.toEuclideanLin A) q₁)
          (Matrix.toEuclideanLin A (Arnoldi.vec (Matrix.toEuclideanLin A) q₁ k)) m).ofLp,
        fun i => if i < m then Arnoldi.coeff (Matrix.toEuclideanLin A) q₁ i k else 0) := by
  set T := Matrix.toEuclideanLin A
  induction m with
  | zero => rfl
  | succ m ih =>
    have ih' := ih fun i hi => hq i (by omega)
    simp only [mgsLoop, List.range_succ, List.foldlM_append, List.foldlM_cons, List.foldlM_nil,
      Id.run_bind] at ih' ⊢
    rw [ih']
    simp only [Id.run_pure, algorithm_1_1_1_spec, algorithm_1_1_2_spec, hq m (by omega)]
    have hc : (Arnoldi.vec T q₁ m).ofLp ⬝ᵥ
        (InnerProductSpace.modifiedGramSchmidtSweep ℝ (Arnoldi.vec T q₁) (T (Arnoldi.vec T q₁ k))
          m).ofLp = Arnoldi.coeff T q₁ m k := by
      rw [Arnoldi.coeff_eq_inner_modifiedGramSchmidtSweep, EuclideanSpace.inner_eq_star_dotProduct,
        star_trivial, dotProduct_comm]
    rw [hc]
    refine Prod.ext ?_ (funext fun i => ?_)
    · simp only [InnerProductSpace.modifiedGramSchmidtSweep_succ, WithLp.ofLp_sub,
        WithLp.ofLp_smul]
      rw [← hc, EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm]
      simp [sub_eq_add_neg]
    · by_cases him : i = m
      · subst him; simp
      · simp only [Function.update_of_ne him]
        by_cases hi : i < m
        · rw [ite_eq_left hi, ite_eq_left (by omega)]
        · rw [ite_eq_right hi, ite_eq_right (by omega)]

/-- The exact run after `t + 1` passes is one more pass. -/
private theorem algorithm_10_5_1_succ (A : Matrix (Fin n) (Fin n) ℝ) (q₁ : Fin n → ℝ) (t : ℕ) :
    Id.run (algorithm_10_5_1 pure A q₁ (t + 1)) =
      Id.run (arnoldiStep pure A (Id.run (algorithm_10_5_1 pure A q₁ t))) := by
  simp only [algorithm_10_5_1, List.range_succ, List.foldlM_append, List.foldlM_cons,
    List.foldlM_nil, bind_pure, Id.run_bind]

/-- **Exact semantics of Algorithm 10.5.1.** For a unit `q₁` the exact run stops after
`t = min fuel m` passes, `m` the grade of `q₁`, and for `j < t`: `q_{j+1} = Arnoldi.vec _ q₁ j` and
`h_{i+1,j+1} = Arnoldi.coeff _ q₁ i j` for `i ≤ j + 1`; the last residual is `Arnoldi.w`. The inner
loop is `InnerProductSpace.modifiedGramSchmidtSweep`, whose coefficients are the classical ones
against the orthonormal `q_i` (`Arnoldi.coeff_eq_inner_modifiedGramSchmidtSweep`); the
normalization is `Arnoldi.vec_succ_eq` with `h_{k+1,k} = ‖w_k‖` (`Arnoldi.coeff_succ_self`), and
the exit test is `Arnoldi.coeff_succ_self_eq_zero_iff`. "P10.5.1" (orthonormality) is the backbone's
`Arnoldi.orthonormal`. -/
theorem algorithm_10_5_1_spec (A : Matrix (Fin n) (Fin n) ℝ) {q₁ : Fin n → ℝ}
    (hq : ‖(WithLp.toLp 2 q₁ : EuclideanSpace ℝ (Fin n))‖ = 1) (fuel : ℕ) :
    let s := Id.run (algorithm_10_5_1 pure A q₁ fuel)
    let T := Matrix.toEuclideanLin A
    let q : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 q₁
    s.k = min fuel (grade T q) ∧
      (∀ j < s.k, s.q j = (Arnoldi.vec T q j).ofLp ∧
        ∀ i ≤ j + 1, s.h i j = Arnoldi.coeff T q i j) ∧
      (0 < s.k → s.r = (Arnoldi.w T q (s.k - 1)).ofLp) := by
  intro s T q
  have hq0 : q ≠ 0 := by
    intro h
    have h1 : ‖q‖ = 1 := hq
    rw [h, norm_zero] at h1
    exact zero_ne_one h1
  have hg : 0 < grade T q := by
    rw [Nat.pos_iff_ne_zero, Ne, grade_eq_zero_iff]
    push Not
    exact ⟨hq0, inferInstance⟩
  let P : ℕ → ArnoldiState n → Prop := fun t s =>
    s.k = min t (grade T q) ∧ s.done = decide (grade T q ≤ s.k) ∧
      (∀ j < s.k, s.q j = (Arnoldi.vec T q j).ofLp ∧
        ∀ i ≤ j + 1, s.h i j = Arnoldi.coeff T q i j) ∧
      s.r = if s.k = 0 then q₁ else (Arnoldi.w T q (s.k - 1)).ofLp
  have hP : ∀ t, P t (Id.run (algorithm_10_5_1 pure A q₁ t)) := by
    intro t
    induction t with
    | zero =>
      refine ⟨by simp [algorithm_10_5_1], ?_, fun j hj => ?_, by simp [algorithm_10_5_1]⟩
      · simp [algorithm_10_5_1, hg.ne']
      · simp [algorithm_10_5_1] at hj
    | succ t ih =>
      rw [algorithm_10_5_1_succ]
      set s := Id.run (algorithm_10_5_1 pure A q₁ t)
      obtain ⟨hk, hdone, hvec, hr⟩ := ih
      cases hsd : s.done with
      | true =>
        have hle : grade T q ≤ s.k := by simpa [hsd] using hdone.symm
        simp only [arnoldiStep, hsd, ↓reduceIte, Id.run_pure]
        refine ⟨?_, hdone, hvec, hr⟩
        rw [hk] at hle ⊢
        omega
      | false =>
        have hlt : s.k < grade T q := by
          have : ¬ grade T q ≤ s.k := by simpa [hsd] using hdone.symm
          omega
        -- the new Arnoldi vector
        have hqk : (if s.k = 0 then 1 else s.h s.k (s.k - 1))⁻¹ • s.r =
            (Arnoldi.vec T q s.k).ofLp := by
          rcases Nat.eq_zero_or_pos s.k with h0 | hpos
          · simp only [hr, h0, ↓reduceIte]
            rw [Arnoldi.vec_zero T q hq0, show ‖q‖ = 1 from hq]
            simp [q]
          · obtain ⟨j, hj⟩ : ∃ j, s.k = j + 1 := ⟨s.k - 1, by omega⟩
            simp only [hr, hj, add_eq_zero, one_ne_zero, and_false, ↓reduceIte,
              Nat.add_sub_cancel]
            rw [((hvec j (by omega)).2 (j + 1) le_rfl), Arnoldi.coeff_succ_self,
              Arnoldi.vec_succ_eq]
            simp
        have hqs : ∀ i < s.k + 1, Function.update s.q s.k (Arnoldi.vec T q s.k).ofLp i =
            (Arnoldi.vec T q i).ofLp := fun i hi => by
          rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
          · rw [Function.update_of_ne hi.ne]; exact (hvec i hi).1
          · simp
        simp only [P, arnoldiStep, hsd, Bool.false_eq_true, ↓reduceIte, Id.run_bind,
          Id.run_pure, vecDiv_spec, algorithm_1_1_3_spec, zero_add, vecNorm_spec]
        rw [hqk, mgsLoop_id A q _ s.k (s.k + 1) hqs]
        have hsweep : InnerProductSpace.modifiedGramSchmidtSweep ℝ (Arnoldi.vec T q)
            (T (Arnoldi.vec T q s.k)) (s.k + 1) = Arnoldi.w T q s.k := by
          rw [InnerProductSpace.modifiedGramSchmidtSweep_eq_sub_sum ℝ
            (fun _ _ h => Arnoldi.inner_vec_eq_zero T q h), Arnoldi.w]
          rfl
        rw [hsweep, WithLp.toLp_ofLp]
        refine ⟨by omega, ?_, fun j hj => ⟨hqs j hj, fun i hi => ?_⟩, by simp⟩
        · have h0 := Arnoldi.coeff_succ_self_eq_zero_iff T q s.k
          rw [Arnoldi.coeff_succ_self] at h0
          simp only [RCLike.ofReal_real_eq_id, id] at h0
          simp only [h0]
        · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
          · simp only [ite_eq_right hj.ne]
            exact (hvec j hj).2 i hi
          · simp only [↓reduceIte]
            by_cases hik : i = s.k + 1
            · subst hik
              simp only [↓reduceIte]
              rw [Arnoldi.coeff_succ_self]
              rfl
            · rw [ite_eq_right hik, ite_eq_left (by omega)]
  obtain ⟨hk, -, hvec, hr⟩ := hP fuel
  have hr' : s.r = if s.k = 0 then q₁ else (Arnoldi.w T q (s.k - 1)).ofLp := hr
  refine ⟨hk, hvec, fun hpos => ?_⟩
  simp only [hr', hpos.ne', ↓reduceIte]

/-! ### The unsymmetric Lanczos process (§10.5.5) -/

/-- The state of the unsymmetric Lanczos tridiagonalization (10.5.11): the number `k` of Lanczos
vector pairs computed, the vectors (`q j`, `qt j` are the book's `q_{j+1}`, `q̃_{j+1}`), the
coefficients (`alpha j` is the book's `α_{j+1}`; `beta j`, `gamma j` are the book's `β_j`, `γ_j`,
computed at the top of the `j`-th pass), the residuals `r`, `s` (the book's `r_k`, `r̃_k = s_k`) and
the `done` flag of the loop. -/
structure UnsymLanczosState (n : ℕ) where
  /-- The book's step counter `k`. -/
  k : ℕ
  /-- The right Lanczos vectors, `0`-based. -/
  q : ℕ → Fin n → ℝ
  /-- The left Lanczos vectors, `0`-based. -/
  qt : ℕ → Fin n → ℝ
  /-- The diagonal coefficients `α`, `0`-based. -/
  alpha : ℕ → ℝ
  /-- The coefficients `β_j`, indexed by the pass. -/
  beta : ℕ → ℝ
  /-- The coefficients `γ_j`, indexed by the pass. -/
  gamma : ℕ → ℝ
  /-- The right residual `r_k`. -/
  r : Fin n → ℝ
  /-- The left residual `r̃_k`. -/
  s : Fin n → ℝ
  /-- Whether the loop has stopped (`r_k = 0`, `r̃_k = 0` or `r̃_kᵀ r_k = 0`). -/
  done : Bool

section UnsymProgram

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ) {n : ℕ}

/-- One pass of the loop of (10.5.11) (a no-op once `done`):
```
β_k = ‖r_k‖₂,  γ_k = r̃_kᵀ r_k / β_k,  q_{k+1} = r_k/β_k,  q̃_{k+1} = r̃_k/γ_k,  k = k + 1
α_k = q̃_kᵀ A q_k,  r_k = (A − α_k I) q_k − γ_{k−1} q_{k−1}
r̃_k = (A − α_k I)ᵀ q̃_k − β_{k−1} q̃_{k−1}
```
with `q_0 = q̃_0 = 0`; the loop test (`r_k ≠ 0`, `r̃_k ≠ 0`, `r̃_kᵀ r_k ≠ 0`) is evaluated on the
computed values at the end of the pass. -/
noncomputable def unsymLanczosStep (A : Matrix (Fin n) (Fin n) ℝ) (st : UnsymLanczosState n) :
    M (UnsymLanczosState n) :=
  if st.done then pure st else do
    let b ← vecNorm rnd st.r
    let sr ← algorithm_1_1_1 rnd st.s st.r
    let g ← rnd (sr / b)
    let q ← vecDiv rnd st.r b
    let qt ← vecDiv rnd st.s g
    let Aq ← algorithm_1_1_3 rnd A q 0
    let a ← algorithm_1_1_1 rnd qt Aq
    let r ← algorithm_1_1_2 rnd (-a) q Aq
    let r ← algorithm_1_1_2 rnd (-g) (if st.k = 0 then 0 else st.q (st.k - 1)) r
    let Atq ← algorithm_1_1_3 rnd Aᵀ qt 0
    let s ← algorithm_1_1_2 rnd (-a) qt Atq
    let s ← algorithm_1_1_2 rnd (-b) (if st.k = 0 then 0 else st.qt (st.k - 1)) s
    let sr' ← algorithm_1_1_1 rnd s r
    pure
      { k := st.k + 1
        q := Function.update st.q st.k q
        qt := Function.update st.qt st.k qt
        alpha := Function.update st.alpha st.k a
        beta := Function.update st.beta st.k b
        gamma := Function.update st.gamma st.k g
        r := r
        s := s
        done := decide (r = 0 ∨ s = 0 ∨ sr' = 0) }

/-- **(10.5.11), the unsymmetric Lanczos tridiagonalization** with the canonical choice
`β_k = ‖r_k‖₂`:
```
q₁, q̃₁ given unit 2-norm vectors with q̃₁ᵀq₁ ≠ 0
k = 0, q_0 = 0, r_0 = q₁, q̃_0 = 0, s_0 = q̃₁
while (r_k ≠ 0) and (r̃_k ≠ 0) and (r̃_kᵀ r_k ≠ 0)
  β_k = ‖r_k‖₂,  γ_k = r̃_kᵀ r_k/β_k,  q_{k+1} = r_k/β_k,  q̃_{k+1} = r̃_k/γ_k,  k = k + 1
  α_k = q̃_kᵀ A q_k,  r_k = (A − α_k I) q_k − γ_{k−1} q_{k−1}
  r̃_k = (A − α_k I)ᵀ q̃_k − β_{k−1} q̃_{k−1}
end
```
(the book's `s_0` is `r̃_0`). The loop is at most `fuel` passes (convention 3); the entry test is
evaluated on `q₁`, `q̃₁`. -/
noncomputable def unsymmetricLanczos (A : Matrix (Fin n) (Fin n) ℝ) (q₁ qt₁ : Fin n → ℝ)
    (fuel : ℕ) : M (UnsymLanczosState n) := do
  let sr ← algorithm_1_1_1 rnd qt₁ q₁
  (List.range fuel).foldlM (fun st _ => unsymLanczosStep rnd A st)
    { k := 0, q := fun _ => 0, qt := fun _ => 0, alpha := fun _ => 0, beta := fun _ => 0,
      gamma := fun _ => 0, r := q₁, s := qt₁, done := decide (q₁ = 0 ∨ qt₁ = 0 ∨ sr = 0) }

end UnsymProgram

/-- **A serious breakdown** (§10.5.5): the process has a serious breakdown at the state `st` if
`r_k ≠ 0` and `r̃_k ≠ 0` but `r̃_kᵀ r_k = 0` — the tridiagonalization ends without any invariant
subspace information. -/
def IsSeriousBreakdown {n : ℕ} (st : UnsymLanczosState n) : Prop :=
  st.r ≠ 0 ∧ st.s ≠ 0 ∧ st.s ⬝ᵥ st.r = 0

/-- The tridiagonal `T_k` of (10.5.12), from the computed coefficients: `α` on the diagonal, the
book's `β_1, …, β_{k−1}` below and `γ_1, …, γ_{k−1}` above. -/
def unsymTridiag {n : ℕ} (st : UnsymLanczosState n) (k : ℕ) : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of fun i j =>
    if (i : ℕ) = j then st.alpha i else if (i : ℕ) + 1 = j then st.gamma j
    else if (j : ℕ) + 1 = i then st.beta i else 0

/-- The matrix `[q_1 | ⋯ | q_k]` of computed right Lanczos vectors. -/
def unsymQ {n : ℕ} (st : UnsymLanczosState n) (k : ℕ) : Matrix (Fin n) (Fin k) ℝ :=
  Matrix.of fun i j => st.q j i

/-- The matrix `[q̃_1 | ⋯ | q̃_k]` of computed left Lanczos vectors. -/
def unsymQt {n : ℕ} (st : UnsymLanczosState n) (k : ℕ) : Matrix (Fin n) (Fin k) ℝ :=
  Matrix.of fun i j => st.qt j i

/-- The exact run after `t + 1` passes is one more pass. -/
private theorem unsymmetricLanczos_succ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (q₁ qt₁ : Fin n → ℝ) (t : ℕ) :
    Id.run (unsymmetricLanczos pure A q₁ qt₁ (t + 1)) =
      Id.run (unsymLanczosStep pure A (Id.run (unsymmetricLanczos pure A q₁ qt₁ t))) := by
  simp only [unsymmetricLanczos, List.range_succ, List.foldlM_append, List.foldlM_cons,
    List.foldlM_nil, bind_pure, Id.run_bind]

/-- The three-term relations kept by the exact run: column `j` of (10.5.12) and (10.5.13), and the
`done` flag records the loop test on the current residuals. -/
private theorem unsym_relations {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (q₁ qt₁ : Fin n → ℝ)
    (t : ℕ) :
    let st := Id.run (unsymmetricLanczos pure A q₁ qt₁ t)
    st.done = decide (st.r = 0 ∨ st.s = 0 ∨ st.s ⬝ᵥ st.r = 0) ∧
    ∀ j < st.k,
      A *ᵥ st.q j = st.gamma j • (if j = 0 then 0 else st.q (j - 1)) + st.alpha j • st.q j +
          (if j + 1 < st.k then st.beta (j + 1) • st.q (j + 1) else st.r) ∧
      Aᵀ *ᵥ st.qt j = st.beta j • (if j = 0 then 0 else st.qt (j - 1)) + st.alpha j • st.qt j +
          (if j + 1 < st.k then st.gamma (j + 1) • st.qt (j + 1) else st.s) := by
  intro st
  let P : UnsymLanczosState n → Prop := fun st =>
    st.done = decide (st.r = 0 ∨ st.s = 0 ∨ st.s ⬝ᵥ st.r = 0) ∧
    ∀ j < st.k,
      A *ᵥ st.q j = st.gamma j • (if j = 0 then 0 else st.q (j - 1)) + st.alpha j • st.q j +
          (if j + 1 < st.k then st.beta (j + 1) • st.q (j + 1) else st.r) ∧
      Aᵀ *ᵥ st.qt j = st.beta j • (if j = 0 then 0 else st.qt (j - 1)) + st.alpha j • st.qt j +
          (if j + 1 < st.k then st.gamma (j + 1) • st.qt (j + 1) else st.s)
  suffices hP : ∀ t, P (Id.run (unsymmetricLanczos pure A q₁ qt₁ t)) from hP t
  intro t
  induction t with
  | zero =>
    refine ⟨by simp [unsymmetricLanczos, algorithm_1_1_1_spec], fun j hj => ?_⟩
    simp [unsymmetricLanczos] at hj
  | succ t ih =>
    rw [unsymmetricLanczos_succ]
    set s0 := Id.run (unsymmetricLanczos pure A q₁ qt₁ t) with hs0
    obtain ⟨hdone, hrel⟩ := ih
    cases hsd : s0.done with
    | true =>
      simp only [unsymLanczosStep, hsd, ↓reduceIte, Id.run_pure]
      exact ⟨hdone, hrel⟩
    | false =>
      have htest : ¬ (s0.r = 0 ∨ s0.s = 0 ∨ s0.s ⬝ᵥ s0.r = 0) := by
        simpa [hsd] using hdone.symm
      push Not at htest
      obtain ⟨hr0, -, hsr⟩ := htest
      have hb : ‖(WithLp.toLp 2 s0.r : EuclideanSpace ℝ (Fin n))‖ ≠ 0 := by
        rw [norm_ne_zero_iff]
        intro h
        exact hr0 (by simpa using congrArg WithLp.ofLp h)
      have hg : s0.s ⬝ᵥ s0.r / ‖(WithLp.toLp 2 s0.r : EuclideanSpace ℝ (Fin n))‖ ≠ 0 :=
        div_ne_zero hsr hb
      simp only [P, unsymLanczosStep, hsd, Bool.false_eq_true, ↓reduceIte, Id.run_bind,
        Id.run_pure, vecNorm_spec, algorithm_1_1_1_spec, vecDiv_spec, algorithm_1_1_3_spec,
        algorithm_1_1_2_spec, zero_add]
      refine ⟨by simp, fun j hj => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · -- an old column
        obtain ⟨h1, h2⟩ := hrel j hj
        have hne : j ≠ s0.k := hj.ne
        simp only [Function.update_of_ne hne]
        by_cases hj1 : j + 1 < s0.k
        · have hne1 : j + 1 ≠ s0.k := hj1.ne
          have hne0 : j - 1 ≠ s0.k := by omega
          simp only [Function.update_of_ne hne1, Function.update_of_ne hne0,
            ite_eq_left (show j + 1 < s0.k + 1 by omega), ite_eq_left hj1] at h1 h2 ⊢
          exact ⟨h1, h2⟩
        · have hk : j + 1 = s0.k := by omega
          have hne0 : j - 1 ≠ s0.k := by omega
          simp only [ite_eq_right hj1] at h1 h2
          simp only [Function.update_of_ne hne0, hk, Function.update_self]
          refine ⟨?_, ?_⟩
          · rw [h1, smul_smul, mul_inv_cancel₀ hb, one_smul, ite_eq_left (lt_add_one s0.k)]
          · rw [h2, smul_smul, mul_inv_cancel₀ hg, one_smul, ite_eq_left (lt_add_one s0.k)]
      · -- the new column
        simp only [Function.update_self, ite_eq_right (show ¬ s0.k + 1 < s0.k + 1 by omega)]
        refine ⟨?_, ?_⟩
        · by_cases h0 : s0.k = 0
          · simp only [h0, ↓reduceIte]
            module
          · simp only [h0, ↓reduceIte, Function.update_of_ne (show s0.k - 1 ≠ s0.k by omega)]
            module
        · by_cases h0 : s0.k = 0
          · simp only [h0, ↓reduceIte]
            module
          · simp only [h0, ↓reduceIte, Function.update_of_ne (show s0.k - 1 ≠ s0.k by omega)]
            module

/-- A column of a product with a tridiagonal matrix given by its three diagonals: the entry
`(Q T)(x, j)` collects `c_j Q(x, j−1) + a_j Q(x, j) + b_{j+1} Q(x, j+1)`. -/
private theorem sum_mul_tridiag {k : ℕ} (f : Fin k → ℝ) (a b c : ℕ → ℝ) (j : Fin k) :
    ∑ l : Fin k, f l * (if (l : ℕ) = j then a l else if (l : ℕ) + 1 = j then c j
      else if (j : ℕ) + 1 = l then b l else 0) =
      (if h : 0 < (j : ℕ) then c j * f ⟨j - 1, by omega⟩ else 0) + a j * f j +
        (if h : (j : ℕ) + 1 < k then b (j + 1) * f ⟨j + 1, h⟩ else 0) := by
  have hsplit : ∀ l : Fin k, f l * (if (l : ℕ) = j then a l else if (l : ℕ) + 1 = j then c j
      else if (j : ℕ) + 1 = l then b l else 0) =
      (if l = j then a j * f j else 0) +
        ((if (l : ℕ) + 1 = j then c j * f l else 0) +
          (if (j : ℕ) + 1 = l then b (j + 1) * f l else 0)) := by
    intro l
    by_cases h1 : l = j
    · subst h1; simp [mul_comm]
    · have h1' : (l : ℕ) ≠ j := fun h => h1 (Fin.ext h)
      rw [ite_eq_right h1', ite_eq_right h1]
      by_cases h2 : (l : ℕ) + 1 = j
      · rw [ite_eq_left h2, ite_eq_left h2, ite_eq_right (by omega)]; ring
      · rw [ite_eq_right h2, ite_eq_right h2]
        by_cases h3 : (j : ℕ) + 1 = l
        · rw [ite_eq_left h3, ite_eq_left h3, ← h3]; ring
        · rw [ite_eq_right h3, ite_eq_right h3]; ring
  rw [Finset.sum_congr rfl fun l _ => hsplit l, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ j, ite_eq_left (Finset.mem_univ _)]
  have hlow : ∑ l : Fin k, (if (l : ℕ) + 1 = j then c j * f l else 0) =
      if h : 0 < (j : ℕ) then c j * f ⟨j - 1, by omega⟩ else 0 := by
    split_ifs with h
    · rw [Finset.sum_eq_single ⟨j - 1, by omega⟩ (fun l _ hl => ite_eq_right (fun h' =>
        hl (Fin.ext (by simp; omega)))) (fun h' => absurd (Finset.mem_univ _) h')]
      rw [ite_eq_left (by simp; omega)]
    · exact Finset.sum_eq_zero fun l _ => ite_eq_right (by omega)
  have hup : ∑ l : Fin k, (if (j : ℕ) + 1 = l then b (j + 1) * f l else 0) =
      if h : (j : ℕ) + 1 < k then b (j + 1) * f ⟨j + 1, h⟩ else 0 := by
    split_ifs with h
    · rw [Finset.sum_eq_single ⟨j + 1, h⟩ (fun l _ hl => ite_eq_right (fun h' =>
        hl (Fin.ext (by simp; omega)))) (fun h' => absurd (Finset.mem_univ _) h')]
      rw [ite_eq_left rfl]
    · exact Finset.sum_eq_zero fun l _ => ite_eq_right (fun h' => h (by omega))
  rw [hlow, hup]
  ring

/-- **(10.5.12)**: at the bottom of the loop of (10.5.11) (exact arithmetic),
`A [q_1 | ⋯ | q_k] = [q_1 | ⋯ | q_k] T_k + r_k e_kᵀ`, `T_k` the tridiagonal matrix of the computed
`α`, `β`, `γ`. Column by column from the recurrence. -/
theorem equation_10_5_12 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (q₁ qt₁ : Fin n → ℝ)
    (fuel : ℕ) :
    let st := Id.run (unsymmetricLanczos pure A q₁ qt₁ fuel)
    A * unsymQ st st.k = unsymQ st st.k * unsymTridiag st st.k +
      Matrix.vecMulVec st.r (Krylov.lastVec (1 : ℝ) st.k) := by
  intro st
  have hrel : ∀ j < st.k,
      A *ᵥ st.q j = st.gamma j • (if j = 0 then 0 else st.q (j - 1)) + st.alpha j • st.q j +
          (if j + 1 < st.k then st.beta (j + 1) • st.q (j + 1) else st.r) :=
    fun j hj => ((unsym_relations A q₁ qt₁ fuel).2 j hj).1
  ext x j
  have h := congrFun (hrel j j.isLt) x
  rw [Matrix.add_apply, Matrix.vecMulVec_apply, Matrix.mul_apply, Matrix.mul_apply]
  rw [show (∑ l, A x l * unsymQ st st.k l j) = (A *ᵥ st.q j) x from rfl, h]
  simp only [unsymQ, unsymTridiag, Matrix.of_apply]
  rw [sum_mul_tridiag (fun l : Fin st.k => st.q l x) st.alpha st.beta st.gamma j]
  simp only [Krylov.lastVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rcases Nat.eq_zero_or_pos (j : ℕ) with h0 | h0
  · by_cases h1 : 1 < st.k
    · simp [h0, h1, show (1 : ℕ) ≠ st.k by omega]
    · simp [h0, show st.k = 1 by omega]
  · by_cases h1 : (j : ℕ) + 1 < st.k
    · simp [h0.ne', h1, show (j : ℕ) + 1 ≠ st.k by omega]
    · simp [h0.ne', show (j : ℕ) + 1 = st.k by omega]

/-- **(10.5.13)**: `Aᵀ [q̃_1 | ⋯ | q̃_k] = [q̃_1 | ⋯ | q̃_k] T_kᵀ + r̃_k e_kᵀ`. Column by column
from the recurrence for `q̃`. -/
theorem equation_10_5_13 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (q₁ qt₁ : Fin n → ℝ)
    (fuel : ℕ) :
    let st := Id.run (unsymmetricLanczos pure A q₁ qt₁ fuel)
    Aᵀ * unsymQt st st.k = unsymQt st st.k * (unsymTridiag st st.k)ᵀ +
      Matrix.vecMulVec st.s (Krylov.lastVec (1 : ℝ) st.k) := by
  intro st
  have hrel : ∀ j < st.k,
      Aᵀ *ᵥ st.qt j = st.beta j • (if j = 0 then 0 else st.qt (j - 1)) + st.alpha j • st.qt j +
          (if j + 1 < st.k then st.gamma (j + 1) • st.qt (j + 1) else st.s) :=
    fun j hj => ((unsym_relations A q₁ qt₁ fuel).2 j hj).2
  ext x j
  have h := congrFun (hrel j j.isLt) x
  rw [Matrix.add_apply, Matrix.vecMulVec_apply, Matrix.mul_apply, Matrix.mul_apply]
  rw [show (∑ l, Aᵀ x l * unsymQt st st.k l j) = (Aᵀ *ᵥ st.qt j) x from rfl, h]
  have hT : ∀ l : Fin st.k, (unsymTridiag st st.k)ᵀ l j =
      (if (l : ℕ) = j then st.alpha l else if (l : ℕ) + 1 = j then st.beta j
        else if (j : ℕ) + 1 = l then st.gamma l else 0) := by
    intro l
    simp only [Matrix.transpose_apply, unsymTridiag, Matrix.of_apply]
    split_ifs <;> first | rfl | omega | congr 1
  simp only [unsymQt, Matrix.of_apply, hT]
  rw [sum_mul_tridiag (fun l : Fin st.k => st.qt l x) st.alpha st.gamma st.beta j]
  simp only [Krylov.lastVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rcases Nat.eq_zero_or_pos (j : ℕ) with h0 | h0
  · by_cases h1 : 1 < st.k
    · simp [h0, h1, show (1 : ℕ) ≠ st.k by omega]
    · simp [h0, show st.k = 1 by omega]
  · by_cases h1 : (j : ℕ) + 1 < st.k
    · simp [h0.ne', h1, show (j : ℕ) + 1 ≠ st.k by omega]
    · simp [h0.ne', show (j : ℕ) + 1 = st.k by omega]

/-- **Termination with an invariant subspace** (§10.5.5, after (10.5.13)): if `r_k = 0` then
`span {q_1, …, q_k}` is `A`-invariant, and if `r̃_k = 0` then `span {q̃_1, …, q̃_k}` is
`Aᵀ`-invariant: from (10.5.12)–(10.5.13), `A Q_k = Q_k T_k` resp. `Aᵀ Q̃_k = Q̃_k T_kᵀ`. -/
theorem unsymmetricLanczos_invariant {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (q₁ qt₁ : Fin n → ℝ) (fuel : ℕ) :
    let st := Id.run (unsymmetricLanczos pure A q₁ qt₁ fuel)
    (st.r = 0 → ∀ y : Fin st.k → ℝ, A *ᵥ (unsymQ st st.k *ᵥ y) =
      unsymQ st st.k *ᵥ (unsymTridiag st st.k *ᵥ y)) ∧
    (st.s = 0 → ∀ y : Fin st.k → ℝ, Aᵀ *ᵥ (unsymQt st st.k *ᵥ y) =
      unsymQt st st.k *ᵥ ((unsymTridiag st st.k)ᵀ *ᵥ y)) := by
  intro st
  refine ⟨fun hr y => ?_, fun hs y => ?_⟩
  · have h := equation_10_5_12 A q₁ qt₁ fuel
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h, hr, Matrix.zero_vecMulVec, add_zero]
  · have h := equation_10_5_13 A q₁ qt₁ fuel
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h, hs, Matrix.zero_vecMulVec, add_zero]

end GolubVanLoan.Chapter10
