import Numlib.Eigen.ImplicitRestart
import NumlibSurface.GolubVanLoan.Chapter05.Section02
import NumlibSurface.GolubVanLoan.Chapter10.Section01

/-!
# Golub–Van Loan §10.5: Krylov methods for unsymmetric problems

Surface file for Gene H. Golub and Charles F. Van Loan, *Matrix Computations*, 4th edition, §10.5:
Algorithm 10.5.1 (Arnoldi with the modified Gram–Schmidt inner loop), (10.5.1)–(10.5.2) and the
definition of a `k`-step Arnoldi decomposition, the Ritz pair and its backward error, implicit
restarting (10.5.4)–(10.5.9) with Theorem 10.5.1, the restart loops (10.5.10) and the implicitly
restarted framework, the Krylov–Schur restart, the unsymmetric Lanczos tridiagonalization
(10.5.11)–(10.5.13), and the block biorthogonality step (10.5.14)–(10.5.16).

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
of §10.5.6, operation counts. The filter values of the restart loops are a caller-supplied
function of `H_c` (the book leaves them to heuristics).

## Programs

The shifted QR steps (10.5.4) (`shiftedQrSteps`) call chapter 5's Givens QR of a Hessenberg matrix
(Algorithm 5.2.5) and its rotation updates; the statements about shifted QR chains hold for every
chain with the properties the program's run has (`equation_10_5_4`). Explicit restarting (10.5.10)
and the implicitly restarted framework of §10.5.3 run Algorithm 10.5.1, (10.5.4) and chapter 1's
matrix products; the implicit framework continues the Arnoldi loop body `arnoldiStep` from the
truncated decomposition, with the residual corrected as in `implicitRestart_isArnoldiDecomposition`.
The unsymmetric Lanczos process (10.5.11) is analysed directly from its recurrences.
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
/-- The spectral norm of a rank-one matrix: `‖v xᵀ‖₂ = ‖v‖₂ ‖x‖₂` (backbone
`Matrix.l2_opNorm_vecMulVec`). -/
theorem l2_opNorm_vecMulVec {m : ℕ} (v : Fin n → ℝ) (x : Fin m → ℝ) :
    ‖Matrix.vecMulVec v x‖ =
      ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖ *
        ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin m))‖ :=
  Matrix.l2_opNorm_vecMulVec v x

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

/-! ### The shifted QR steps (10.5.4) -/

section ShiftedQrProgram

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- One row of `B + μ I`: the diagonal entry `x_r ← fl(x_r + μ)`, the others copied. -/
def shiftDiagRow {m : ℕ} (μ : ℝ) (r : Fin m) (x : Fin m → ℝ) : M (Fin m → ℝ) := do
  let d ← rnd (x r + μ)
  pure (Function.update x r d)

/-- `B + μ I`, each diagonal entry rounded once (`B − μ I` is the shift by `−μ`, negation being
exact). -/
def shiftDiag {m : ℕ} (μ : ℝ) (B : Matrix (Fin m) (Fin m) ℝ) : M (Matrix (Fin m) (Fin m) ℝ) :=
  (List.finRange m).foldlM (fun (B : Fin m → Fin m → ℝ) r => do
    let b ← shiftDiagRow rnd μ r (B r)
    pure (Function.update B r b)) B

/-- `B G_1 ⋯ G_k` for the rotations `G_{j+1} = G(j, j+1, θ_j)` given by the pairs
`cs j = (c_j, s_j)` (as Algorithm 5.2.5 returns them), each applied to all rows by chapter 5's
column update `givensApplyRight`. -/
def rotationsApplyRight {k : ℕ} (cs : Fin k → ℝ × ℝ) (B : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) :
    M (Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) :=
  (List.finRange k).foldlM (fun B j =>
    Chapter05.givensApplyRight rnd j.castSucc j.succ (cs j).1 (cs j).2 (List.finRange (k + 1)) B) B

end ShiftedQrProgram

/-- The state of the shifted QR steps (10.5.4) on an `(m+1) × (m+1)` matrix: `H i` is the book's
`H^{(i)}`, `V i` and `R i` are the book's `V_{i+1}` and `R_{i+1}`, and `acc` is `V_1 ⋯ V_i` after
`i` steps. -/
structure ShiftedQrState (m : ℕ) where
  /-- The iterates `H^{(i)}`. -/
  H : ℕ → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ
  /-- The orthogonal factors, `0`-based. -/
  V : ℕ → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ
  /-- The triangular factors, `0`-based. -/
  R : ℕ → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ
  /-- The accumulated product `V = V_1 ⋯ V_i`. -/
  acc : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ

section ShiftedQrProgram

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- Step `i` of (10.5.4): `H^{(i)} − μ_{i+1} I = V_{i+1} R_{i+1}` by chapter 5's Givens QR of a
Hessenberg matrix (Algorithm 5.2.5, which returns `R` and the rotation pairs), `V_{i+1}` formed from
the rotations, `H^{(i+1)} = R_{i+1} V_{i+1} + μ_{i+1} I` (the rotations applied to `R` on the
right), and `V ← V V_{i+1}`. -/
noncomputable def shiftedQrStep {m : ℕ} (μ : ℕ → ℝ) (st : ShiftedQrState m) (i : ℕ) :
    M (ShiftedQrState m) := do
  let B ← shiftDiag rnd (-μ i) (st.H i)
  let RC ← Chapter05.algorithm_5_2_5 rnd B
  let Vi ← rotationsApplyRight rnd RC.2 1
  let RV ← rotationsApplyRight rnd RC.2 RC.1
  let Hn ← shiftDiag rnd (μ i) RV
  let acc ← rotationsApplyRight rnd RC.2 st.acc
  pure { H := Function.update st.H (i + 1) Hn, V := Function.update st.V i Vi,
         R := Function.update st.R i RC.1, acc := acc }

/-- **(10.5.4), `p` steps of the shifted QR iteration** on an upper Hessenberg `H_c`:
```
H^(0) = H_c
for i = 1:p
    H^(i−1) − μ_i I = V_i R_i   (Givens QR)
    H^(i) = R_i V_i + μ_i I
end
H₊ = H^(p)
```
(the book prints `i = 0 : p`), with `V = V_1 ⋯ V_p` (10.5.5) accumulated. The shifts are
`μ 0, …, μ (p−1)` (the book's `μ_1, …, μ_p`); the book's `m` is `m + 1` here. -/
noncomputable def shiftedQrSteps {m : ℕ} (Hc : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (μ : ℕ → ℝ) (p : ℕ) : M (ShiftedQrState m) :=
  (List.range p).foldlM (shiftedQrStep rnd μ)
    { H := fun _ => Hc, V := fun _ => 1, R := fun _ => 1, acc := 1 }

end ShiftedQrProgram

/-- Exact semantics of the diagonal shift: `B + μ I`. -/
theorem shiftDiag_spec {m : ℕ} (μ : ℝ) (B : Matrix (Fin m) (Fin m) ℝ) :
    Id.run (shiftDiag pure μ B) = B + μ • 1 := by
  ext r c
  have h := congrFun (idRun_foldlM_update_apply (fun r x => shiftDiagRow (pure : ℝ → Id ℝ) μ r x)
    (List.finRange m) (List.nodup_finRange m) B r) c
  rw [ite_eq_left (List.mem_finRange r)] at h
  refine h.trans ?_
  simp only [shiftDiagRow, Id.run_bind, Id.run_pure, Function.update_apply, Matrix.add_apply,
    Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  by_cases hrc : c = r
  · subst hrc; simp
  · simp [hrc, Ne.symm hrc]

/-- Exact semantics of the rotation sweep: `B G_1 ⋯ G_k`, the product of chapter 5's rotation
matrices `G(j, j+1, θ_j)` in increasing order (the `Q` of Algorithm 5.2.5). -/
theorem rotationsApplyRight_spec {k : ℕ} (cs : Fin k → ℝ × ℝ)
    (B : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) :
    Id.run (rotationsApplyRight pure cs B) = B * (List.ofFn fun j : Fin k =>
      Chapter05.givensRotation j.castSucc j.succ (cs j).1 (cs j).2).prod := by
  rw [List.ofFn_eq_map]
  unfold rotationsApplyRight
  generalize List.finRange k = l
  induction l generalizing B with
  | nil => simp
  | cons j l ih =>
    rw [List.foldlM_cons, Id.run_bind, Chapter05.givensApplyRight_spec_of_forall_mem
      j.castSucc_lt_succ.ne _ _ (List.nodup_finRange _) (List.mem_finRange), ih,
      List.map_cons, List.prod_cons, Matrix.mul_assoc]

/-- **Exact semantics of (10.5.4)**: for upper Hessenberg `H_c`, the run's `H^{(i)}`, `V_i`, `R_i`
form a shifted QR chain (`Matrix.IsShiftedQrChain`) starting at `H_c`, every `V_i` is orthogonal
and upper Hessenberg and every `R_i` upper triangular (chapter 5's `algorithm_5_2_5_spec`), hence
every `H^{(i)}` is upper Hessenberg (the book's "recall from §7.4.2",
`Matrix.IsShiftedQrChain.isUpperHessenberg`), and the accumulated `V` is `V_1 ⋯ V_p`. -/
theorem equation_10_5_4 {m : ℕ} {Hc : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ}
    (hH : Hc.IsUpperHessenberg) (μ : ℕ → ℝ) (p : ℕ) :
    let st := Id.run (shiftedQrSteps pure Hc μ p)
    st.H 0 = Hc ∧ Matrix.IsShiftedQrChain st.H st.V st.R μ p ∧
      (∀ i < p, st.V i ∈ Matrix.orthogonalGroup (Fin (m + 1)) ℝ ∧ (st.V i).IsUpperHessenberg ∧
        (st.R i).IsUpperTriangular) ∧
      (∀ i ≤ p, (st.H i).IsUpperHessenberg) ∧ st.acc = ((List.range p).map st.V).prod := by
  intro st
  let P : ℕ → ShiftedQrState m → Prop := fun p st =>
    st.H 0 = Hc ∧ Matrix.IsShiftedQrChain st.H st.V st.R μ p ∧
      (∀ i < p, st.V i ∈ Matrix.orthogonalGroup (Fin (m + 1)) ℝ ∧ (st.V i).IsUpperHessenberg ∧
        (st.R i).IsUpperTriangular) ∧ st.acc = ((List.range p).map st.V).prod
  have hHess : ∀ p st, P p st → ∀ i ≤ p, (st.H i).IsUpperHessenberg := by
    rintro p st ⟨h0, hc, hVR, -⟩
    exact hc.isUpperHessenberg (h0 ▸ hH) (fun i hi => (hVR i hi).2.2) (fun i hi => (hVR i hi).2.1)
  suffices hP : ∀ p, P p (Id.run (shiftedQrSteps pure Hc μ p)) by
    obtain ⟨h0, hc, hVR, hacc⟩ := hP p
    exact ⟨h0, hc, hVR, hHess p _ (hP p), hacc⟩
  intro p
  induction p with
  | zero =>
    refine ⟨rfl, ⟨fun i hi => absurd hi (Nat.not_lt_zero _),
      fun i hi => absurd hi (Nat.not_lt_zero _)⟩, fun i hi => absurd hi (Nat.not_lt_zero _), rfl⟩
  | succ p ih =>
    have hrun : Id.run (shiftedQrSteps pure Hc μ (p + 1)) =
        Id.run (shiftedQrStep pure μ (Id.run (shiftedQrSteps pure Hc μ p)) p) := by
      simp only [shiftedQrSteps, List.range_succ, List.foldlM_append, List.foldlM_cons,
        List.foldlM_nil, bind_pure, Id.run_bind]
    rw [hrun]
    set s := Id.run (shiftedQrSteps pure Hc μ p)
    obtain ⟨h0, hc, hVR, hacc⟩ := ih
    have hHp : (s.H p).IsUpperHessenberg := hHess p s ⟨h0, hc, hVR, hacc⟩ p le_rfl
    set B := s.H p + (-μ p) • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) with hB
    have hBH : B.IsUpperHessenberg := hHp.add_smul_one _
    obtain ⟨hQR, hQH⟩ := Chapter05.algorithm_5_2_5_spec B hBH
    set RC := Id.run (Chapter05.algorithm_5_2_5 pure B)
    set Q := (List.ofFn fun j : Fin m => Chapter05.givensRotation j.castSucc j.succ
      (RC.2 j).1 (RC.2 j).2).prod
    simp only [shiftedQrStep, Id.run_bind, Id.run_pure, shiftDiag_spec, rotationsApplyRight_spec]
    try rw [← hB]
    dsimp only [P]
    simp only [Matrix.one_mul]
    have hVs : ∀ i < p, Function.update s.V p Q i = s.V i := fun i hi =>
      Function.update_of_ne hi.ne _ _
    have hRs : ∀ i < p, Function.update s.R p RC.1 i = s.R i := fun i hi =>
      Function.update_of_ne hi.ne _ _
    have hHs : ∀ i ≤ p, Function.update s.H (p + 1) (RC.1 * Q + μ p • 1) i = s.H i :=
      fun i hi => Function.update_of_ne (by omega) _ _
    refine ⟨by rw [hHs 0 (Nat.zero_le _)]; exact h0, ⟨fun i hi => ?_, fun i hi => ?_⟩,
      fun i hi => ?_, ?_⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · rw [hHs i hi.le, hVs i hi, hRs i hi]; exact hc.sub_eq i hi
      · rw [hHs i le_rfl, Function.update_self, Function.update_self, hQR.mul_eq, hB,
          neg_smul, sub_eq_add_neg]
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · rw [hHs (i + 1) hi, hVs i hi, hRs i hi]; exact hc.succ_eq i hi
      · rw [Function.update_self, Function.update_self, Function.update_self]
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · rw [hVs i hi, hRs i hi]; exact hVR i hi
      · rw [Function.update_self, Function.update_self]
        exact ⟨hQR.mem_unitaryGroup, hQH, fun a b hab => hQR.apply_eq_zero a b hab⟩
    · rw [hacc, List.range_succ, List.map_append, List.prod_append, List.map_singleton,
        List.prod_singleton, Function.update_self]
      congr 1
      exact congrArg List.prod (List.map_congr_left fun i hi => (hVs i (List.mem_range.1 hi)).symm)

/-! ### Explicit restarting (10.5.10) -/

/-- The first `K` computed Arnoldi vectors of a run as the columns of an `n × K` matrix
(`Q(:, l) = q_{l+1}`), a copy. -/
def ArnoldiState.qMatrix (s : ArnoldiState n) (K : ℕ) : Matrix (Fin n) (Fin K) ℝ :=
  Matrix.of fun i l => s.q l i

/-- The leading `K × K` block `(h_{il})` of the computed Hessenberg entries of a run, a copy. -/
def ArnoldiState.hMatrix (s : ArnoldiState n) (K : ℕ) : Matrix (Fin K) (Fin K) ℝ :=
  Matrix.of fun i l => s.h i l

section RestartPrograms

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- One cycle of (10.5.10): `m = j + p + 1` steps of Algorithm 10.5.1 from `q₁` (giving `Q_c`,
`H_c`), the filter values `μ = shifts H_c`, `p` steps of (10.5.4) on `H_c`, and the new starting
vector `(Q_c V)(:, 1) = Q_c V(:, 1)` by chapter 1's gaxpy. -/
noncomputable def explicitRestartCycle (A : Matrix (Fin n) (Fin n) ℝ) (j p : ℕ)
    (shifts : Matrix (Fin (j + p + 1)) (Fin (j + p + 1)) ℝ → ℕ → ℝ) (q₁ : Fin n → ℝ) :
    M (Fin n → ℝ) := do
  let s ← algorithm_10_5_1 rnd A q₁ (j + p + 1)
  let st ← shiftedQrSteps rnd (s.hMatrix (j + p + 1)) (shifts (s.hMatrix (j + p + 1))) p
  algorithm_1_1_3 rnd (s.qMatrix (j + p + 1)) (fun i => st.acc i 0) 0

/-- **(10.5.10), explicitly restarted Arnoldi**:
```
Repeat:
  With starting vector q₁, perform m steps of the Arnoldi iteration obtaining Q_c, H_c.
  Determine filter values μ_1, …, μ_p.
  Perform p steps of the shifted QR iteration (10.5.4) obtaining H₊ and V.
  Replace q₁ with the first column of Q_c V.
```
with `m = j + p + 1`, the filter values chosen by a caller-supplied `shifts` (the book leaves the
choice to heuristics; only `shifts H_c i` for `i < p` are used), and `cycles` repetitions. -/
noncomputable def explicitlyRestartedArnoldi (A : Matrix (Fin n) (Fin n) ℝ) (j p : ℕ)
    (shifts : Matrix (Fin (j + p + 1)) (Fin (j + p + 1)) ℝ → ℕ → ℝ) (q₁ : Fin n → ℝ)
    (cycles : ℕ) : M (Fin n → ℝ) :=
  (List.range cycles).foldlM (fun q _ => explicitRestartCycle rnd A j p shifts q) q₁

end RestartPrograms

/-- The coefficients of the modified Gram–Schmidt loop vanish from index `k` on. -/
private theorem mgsLoop_snd_eq_zero (q : ℕ → Fin n → ℝ) (k : ℕ) (r : Fin n → ℝ) {i : ℕ}
    (hi : k ≤ i) : (Id.run (mgsLoop pure q k r)).2 i = 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h := ih (by omega)
    simp only [mgsLoop, List.range_succ, List.foldlM_append, List.foldlM_cons, List.foldlM_nil,
      Id.run_bind, Id.run_pure, bind_pure] at h ⊢
    rw [Function.update_of_ne (by omega)]
    exact h

/-- The exact run of Algorithm 10.5.1 has `h_{il} = 0` below the subdiagonal. -/
private theorem algorithm_10_5_1_h_eq_zero (A : Matrix (Fin n) (Fin n) ℝ) (q₁ : Fin n → ℝ)
    (t : ℕ) {i l : ℕ} (hil : l + 1 < i) : (Id.run (algorithm_10_5_1 pure A q₁ t)).h i l = 0 := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [algorithm_10_5_1_succ]
    cases hsd : (Id.run (algorithm_10_5_1 pure A q₁ t)).done with
    | true => simp only [arnoldiStep, hsd, ↓reduceIte, Id.run_pure]; exact ih
    | false =>
      simp only [arnoldiStep, hsd, Bool.false_eq_true, ↓reduceIte, Id.run_bind, Id.run_pure]
      by_cases h1 : l = (Id.run (algorithm_10_5_1 pure A q₁ t)).k
      · rw [ite_eq_left h1, ite_eq_right (by omega)]
        exact mgsLoop_snd_eq_zero _ _ _ (by omega)
      · rw [ite_eq_right h1]; exact ih

/-- Below the grade, the exact run of `K` passes of Algorithm 10.5.1 gives `Q_K`, `H_K` and `r_K`
of the backbone (`Arnoldi.basisMatrix`, `Arnoldi.hessenbergSq`, `Arnoldi.w`). -/
theorem algorithm_10_5_1_matrices (A : Matrix (Fin n) (Fin n) ℝ) {q₁ : Fin n → ℝ}
    (hq : ‖(WithLp.toLp 2 q₁ : EuclideanSpace ℝ (Fin n))‖ = 1) {K : ℕ}
    (hK : K ≤ grade (Matrix.toEuclideanLin A) (WithLp.toLp 2 q₁)) :
    (Id.run (algorithm_10_5_1 pure A q₁ K)).k = K ∧
      (Id.run (algorithm_10_5_1 pure A q₁ K)).qMatrix K =
        Arnoldi.basisMatrix A (WithLp.toLp 2 q₁) K ∧
      (Id.run (algorithm_10_5_1 pure A q₁ K)).hMatrix K =
        Arnoldi.hessenbergSq (Matrix.toEuclideanLin A) (WithLp.toLp 2 q₁) K ∧
      (0 < K → (Id.run (algorithm_10_5_1 pure A q₁ K)).r =
        (Arnoldi.w (Matrix.toEuclideanLin A) (WithLp.toLp 2 q₁) (K - 1)).ofLp) := by
  obtain ⟨hk, hvec, hr⟩ := algorithm_10_5_1_spec A hq K
  have hk' : (Id.run (algorithm_10_5_1 pure A q₁ K)).k = K := by
    rw [hk]; exact min_eq_left hK
  refine ⟨hk', ?_, ?_, fun h => (hr (by rw [hk']; exact h)).trans (by rw [hk'])⟩
  · ext i l
    simp only [ArnoldiState.qMatrix, Arnoldi.basisMatrix, Matrix.of_apply]
    rw [(hvec l (by rw [hk']; exact l.isLt)).1]
  · ext i l
    simp only [ArnoldiState.hMatrix, Arnoldi.hessenbergSq, Matrix.of_apply]
    by_cases hil : (i : ℕ) ≤ l + 1
    · exact (hvec l (by rw [hk']; exact l.isLt)).2 i hil
    · rw [algorithm_10_5_1_h_eq_zero A q₁ K (by omega),
        Arnoldi.coeff_eq_zero_of_lt _ _ (by omega)]

/-- A matrix with orthonormal columns maps `e₁` to a unit vector. -/
private theorem norm_mulVec_single_zero {K : ℕ} {W : Matrix (Fin n) (Fin (K + 1)) ℝ}
    (hW : Wᵀ * W = 1) :
    ‖(WithLp.toLp 2 (W *ᵥ Pi.single 0 1) : EuclideanSpace ℝ (Fin n))‖ = 1 := by
  have h := congrFun (congrFun hW 0) 0
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at h
  simp only [Matrix.transpose_apply] at h
  rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one]
  simpa [Matrix.mulVec_single_one, sq] using h

/-- The first column of `Q_K` is the unit starting vector. -/
private theorem basisMatrix_mulVec_single_zero (A : Matrix (Fin n) (Fin n) ℝ) {q : Fin n → ℝ}
    (hq : ‖(WithLp.toLp 2 q : EuclideanSpace ℝ (Fin n))‖ = 1) (K : ℕ) :
    Arnoldi.basisMatrix A (WithLp.toLp 2 q) (K + 1) *ᵥ Pi.single 0 1 = q := by
  have hq0 : (WithLp.toLp 2 q : EuclideanSpace ℝ (Fin n)) ≠ 0 := by
    intro h; rw [h, norm_zero] at hq; exact zero_ne_one hq
  ext i
  simp only [Matrix.mulVec_single_one, Matrix.col_apply, Arnoldi.basisMatrix,
    Matrix.of_apply, Fin.val_zero]
  rw [Arnoldi.vec_zero _ _ hq0, hq]
  simp

/-- **One cycle of (10.5.10)** (exact arithmetic, before breakdown: `m = j + p + 1 ≤ grade`): the
new starting vector `q₊` is a unit vector and `R(1,1) q₊ = p(A) q₁` for the cycle's filter
polynomial `p(λ) = (λ − μ_1) ⋯ (λ − μ_p)` (§10.5.3, "`q₊ = p(A) q₁`" with `c = 1/R(1,1)`). -/
theorem explicitRestartCycle_spec (A : Matrix (Fin n) (Fin n) ℝ) (j p : ℕ)
    (shifts : Matrix (Fin (j + p + 1)) (Fin (j + p + 1)) ℝ → ℕ → ℝ) {q : Fin n → ℝ}
    (hq : ‖(WithLp.toLp 2 q : EuclideanSpace ℝ (Fin n))‖ = 1)
    (hg : j + p + 1 ≤ grade (Matrix.toEuclideanLin A) (WithLp.toLp 2 q)) :
    let Hc := Arnoldi.hessenbergSq (Matrix.toEuclideanLin A) (WithLp.toLp 2 q) (j + p + 1)
    let st := Id.run (shiftedQrSteps pure Hc (shifts Hc) p)
    let q' := Id.run (explicitRestartCycle pure A j p shifts q)
    ‖(WithLp.toLp 2 q' : EuclideanSpace ℝ (Fin n))‖ = 1 ∧
      ((List.range p).reverse.map st.R).prod 0 0 • q' =
        aeval A (filterPolynomial (shifts Hc) p) *ᵥ q := by
  intro Hc st q'
  obtain ⟨-, hQ, hH, -⟩ := algorithm_10_5_1_matrices A hq hg
  set Q := Arnoldi.basisMatrix A (WithLp.toLp 2 q) (j + p + 1)
  have hq' : q' = (Q * st.acc) *ᵥ Pi.single 0 1 := by
    simp only [q', explicitRestartCycle, Id.run_bind, algorithm_1_1_3_spec, zero_add]
    rw [hQ, hH, ← Matrix.mulVec_mulVec]
    congr 1
    ext i
    simp [st, Hc]
  have hD := (equation_10_5_2 A (WithLp.toLp 2 q) (k := j + p + 1) (by omega)).2.2 hg
  obtain ⟨h0, hc, hVR, -, hacc⟩ :=
    equation_10_5_4 (Arnoldi.hessenbergSq_isUpperHessenberg (Matrix.toEuclideanLin A)
      (WithLp.toLp 2 q) (j + p + 1)) (shifts Hc) p
  rw [hq', hacc]
  refine ⟨norm_mulVec_single_zero (equation_10_5_9 hD hc h0 fun i hi => (hVR i hi).1).2, ?_⟩
  rw [(restart_firstColumn_eq hD).2 hc h0 fun i hi => (hVR i hi).2.2,
    basisMatrix_mulVec_single_zero A hq]

/-- The run after `ℓ + 1` cycles is one more cycle. -/
private theorem explicitlyRestartedArnoldi_succ (A : Matrix (Fin n) (Fin n) ℝ) (j p : ℕ)
    (shifts : Matrix (Fin (j + p + 1)) (Fin (j + p + 1)) ℝ → ℕ → ℝ) (q₁ : Fin n → ℝ) (ℓ : ℕ) :
    Id.run (explicitlyRestartedArnoldi pure A j p shifts q₁ (ℓ + 1)) =
      Id.run (explicitRestartCycle pure A j p shifts
        (Id.run (explicitlyRestartedArnoldi pure A j p shifts q₁ ℓ))) := by
  simp only [explicitlyRestartedArnoldi, List.range_succ, List.foldlM_append, List.foldlM_cons,
    List.foldlM_nil, bind_pure, Id.run_bind]

/-- **Exact semantics of (10.5.10)**: let `q^{(ℓ)}` be the starting vector after `ℓ` cycles and
`p_ℓ` the filter polynomial of cycle `ℓ` (the shifts chosen from its `H_c`). If no cycle `ℓ < L`
breaks down (`m = j + p + 1 ≤ grade (A, q^{(ℓ)})`), then every `q^{(ℓ)}`, `ℓ ≤ L`, is a unit
vector, `R_ℓ(1,1) q^{(ℓ+1)} = p_ℓ(A) q^{(ℓ)}` (`R_ℓ` the product of the cycle's triangular
factors), and if every `R_ℓ(1,1) ≠ 0` then `q^{(L)}` is a multiple of `p_{L−1}(A) ⋯ p_0(A) q₁`. -/
theorem equation_10_5_10 (A : Matrix (Fin n) (Fin n) ℝ) (j p : ℕ)
    (shifts : Matrix (Fin (j + p + 1)) (Fin (j + p + 1)) ℝ → ℕ → ℝ) {q₁ : Fin n → ℝ}
    (hq : ‖(WithLp.toLp 2 q₁ : EuclideanSpace ℝ (Fin n))‖ = 1) (L : ℕ) :
    let q : ℕ → Fin n → ℝ := fun ℓ => Id.run (explicitlyRestartedArnoldi pure A j p shifts q₁ ℓ)
    let Hc : ℕ → Matrix (Fin (j + p + 1)) (Fin (j + p + 1)) ℝ := fun ℓ =>
      Arnoldi.hessenbergSq (Matrix.toEuclideanLin A) (WithLp.toLp 2 (q ℓ)) (j + p + 1)
    let ρ : ℕ → ℝ := fun ℓ =>
      ((List.range p).reverse.map (Id.run (shiftedQrSteps pure (Hc ℓ) (shifts (Hc ℓ)) p)).R).prod
        0 0
    (∀ ℓ < L, j + p + 1 ≤ grade (Matrix.toEuclideanLin A) (WithLp.toLp 2 (q ℓ))) →
      (∀ ℓ ≤ L, ‖(WithLp.toLp 2 (q ℓ) : EuclideanSpace ℝ (Fin n))‖ = 1) ∧
      (∀ ℓ < L, ρ ℓ • q (ℓ + 1) = aeval A (filterPolynomial (shifts (Hc ℓ)) p) *ᵥ q ℓ) ∧
      ((∀ ℓ < L, ρ ℓ ≠ 0) → ∃ c : ℝ, q L = c •
        (aeval A ((List.range L).map fun ℓ => filterPolynomial (shifts (Hc ℓ)) p).prod *ᵥ q₁)) := by
  intro q Hc ρ hg
  have hsucc : ∀ ℓ, q (ℓ + 1) = Id.run (explicitRestartCycle pure A j p shifts (q ℓ)) :=
    explicitlyRestartedArnoldi_succ A j p shifts q₁
  have hunit : ∀ ℓ ≤ L, ‖(WithLp.toLp 2 (q ℓ) : EuclideanSpace ℝ (Fin n))‖ = 1 := by
    intro ℓ hℓ
    induction ℓ with
    | zero => exact hq
    | succ ℓ ih =>
      rw [hsucc]
      exact (explicitRestartCycle_spec A j p shifts (ih (by omega)) (hg ℓ (by omega))).1
  have hrel : ∀ ℓ < L,
      ρ ℓ • q (ℓ + 1) = aeval A (filterPolynomial (shifts (Hc ℓ)) p) *ᵥ q ℓ := by
    intro ℓ hℓ
    rw [hsucc]
    exact (explicitRestartCycle_spec A j p shifts (hunit ℓ hℓ.le) (hg ℓ hℓ)).2
  refine ⟨hunit, hrel, fun hρ => ?_⟩
  have key : ∀ L' ≤ L, ∃ c : ℝ, q L' = c •
      (aeval A ((List.range L').map fun ℓ => filterPolynomial (shifts (Hc ℓ)) p).prod *ᵥ q₁) := by
    intro L' hL'
    induction L' with
    | zero => exact ⟨1, by simp [q, explicitlyRestartedArnoldi]⟩
    | succ L' ih =>
      obtain ⟨c, hc⟩ := ih (by omega)
      refine ⟨(ρ L')⁻¹ * c, ?_⟩
      have h := hrel L' (by omega)
      rw [← eq_inv_smul_iff₀ (hρ L' (by omega))] at h
      rw [h, hc, List.range_succ, List.map_append, List.prod_append, List.map_singleton,
        List.prod_singleton, mul_comm, map_mul, ← Matrix.mulVec_mulVec, Matrix.mulVec_smul,
        smul_smul]
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← map_mul, ← map_mul,
        mul_comm (filterPolynomial (shifts (Hc L')) p), mul_comm c]
  exact key L le_rfl

/-! ### Implicit restarting (§10.5.3, the modified framework) -/

section ImplicitProgram

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- One cycle of the implicitly restarted framework from an `m`-step state (`m = j + p + 1`): the
filter values `μ = shifts H_c`, (10.5.4) on `H_c`, `Q₊ = Q_c V` (chapter 1's Algorithm 1.1.5),
`Q_c ← Q₊(:, 1:j)`, `H_c ← H₊(1:j, 1:j)`, `r_c ← h⁺_{j+1,j} Q₊(:, j+1) + v_{mj} r_c` (the
residual of `implicitRestart_isArnoldiDecomposition`; the book prints `v_{mj} r_c`),
`h_{j+1,j} = ‖r_c‖₂`, and
Arnoldi steps `j + 1, …, m` continuing from that state (`p` passes of Algorithm 10.5.1's loop body
`arnoldiStep`). The book's `j` is `j + 1` here. -/
noncomputable def implicitRestartCycle (A : Matrix (Fin n) (Fin n) ℝ) (j p : ℕ)
    (shifts : Matrix (Fin (j + p + 1)) (Fin (j + p + 1)) ℝ → ℕ → ℝ) (s : ArnoldiState n) :
    M (ArnoldiState n) := do
  let st ← shiftedQrSteps rnd (s.hMatrix (j + p + 1)) (shifts (s.hMatrix (j + p + 1))) p
  let Qp ← algorithm_1_1_5 rnd (s.qMatrix (j + p + 1)) st.acc 0
  let t ← algorithm_1_1_2 rnd (st.acc (Fin.last (j + p)) ⟨j, by omega⟩) s.r 0
  let r ← algorithm_1_1_2 rnd
    (if h : j + 1 < j + p + 1 then st.H p ⟨j + 1, h⟩ ⟨j, by omega⟩ else 0)
    (fun i => if h : j + 1 < j + p + 1 then Qp i ⟨j + 1, h⟩ else 0) t
  let b ← vecNorm rnd r
  (List.range p).foldlM (fun s _ => arnoldiStep rnd A s)
    { k := j + 1
      q := fun l i => if h : l < j + p + 1 then Qp i ⟨l, h⟩ else 0
      h := fun i l => if h : i < j + 1 ∧ l < j + 1 then st.H p ⟨i, by omega⟩ ⟨l, by omega⟩
        else if i = j + 1 ∧ l = j then b else 0
      r := r
      done := decide (b = 0) }

/-- **Implicitly restarted Arnoldi** (§10.5.3, the modification of (10.5.10)):
```
With starting vector q₁, perform m steps of the Arnoldi iteration obtaining Q_c, H_c, r_c.
Repeat:
  Determine filter values μ_1, …, μ_p.
  Perform p steps of the shifted QR iteration (10.5.4) applied to H_c obtaining H₊ and V.
  Replace Q_c with the first j columns of Q_c V, H_c with H₊(1:j, 1:j), r_c with v_{mj} r_c.
  Starting with A Q_c = Q_c H_c + r_c e_jᵀ, perform steps j+1, …, j+p = m of the Arnoldi
  iteration obtaining A Q_m = Q_m H_m + r_m e_mᵀ.
  Set Q_c = Q_m, H_c = H_m, r_c = r_m.
```
with `m = j + p + 1` (the book's `j` is `j + 1`), caller-supplied `shifts`, `cycles` repetitions,
and the residual corrected as in `implicitRestartCycle`. -/
noncomputable def implicitlyRestartedArnoldi (A : Matrix (Fin n) (Fin n) ℝ) (j p : ℕ)
    (shifts : Matrix (Fin (j + p + 1)) (Fin (j + p + 1)) ℝ → ℕ → ℝ) (q₁ : Fin n → ℝ)
    (cycles : ℕ) : M (ArnoldiState n) := do
  let s ← algorithm_10_5_1 rnd A q₁ (j + p + 1)
  (List.range cycles).foldlM (fun s _ => implicitRestartCycle rnd A j p shifts s) s

end ImplicitProgram

/-- The Arnoldi relations of a state, column by column: orthonormal `q_0, …, q_{k−1}`, the residual
orthogonal to them, `A q_b = Σ_{i<k} h_{ib} q_i (+ r for the last column)`, `h` zero below the
subdiagonal, `h_{k,k−1} = ‖r‖` and the `done` flag recording `‖r‖ = 0`. -/
private def ArnoldiInv (A : Matrix (Fin n) (Fin n) ℝ) (s : ArnoldiState n) : Prop :=
  0 < s.k ∧
    (∀ a < s.k, ∀ b < s.k, s.q a ⬝ᵥ s.q b = if a = b then 1 else 0) ∧
    (∀ a < s.k, s.q a ⬝ᵥ s.r = 0) ∧
    (∀ b < s.k, A *ᵥ s.q b =
      ∑ i ∈ Finset.range s.k, s.h i b • s.q i + if b + 1 = s.k then s.r else 0) ∧
    (∀ i l, l + 1 < i → s.h i l = 0) ∧
    s.h s.k (s.k - 1) = ‖(WithLp.toLp 2 s.r : EuclideanSpace ℝ (Fin n))‖ ∧
    s.done = decide (‖(WithLp.toLp 2 s.r : EuclideanSpace ℝ (Fin n))‖ = 0)

/-- The modified Gram–Schmidt loop against orthonormal vectors is the classical projection. -/
private theorem mgsLoop_orthonormal (q : ℕ → Fin n → ℝ) (k : ℕ) (v : Fin n → ℝ)
    (hq : ∀ a < k, ∀ b < k, q a ⬝ᵥ q b = if a = b then 1 else 0) :
    Id.run (mgsLoop pure q k v) = (v - ∑ i ∈ Finset.range k, (q i ⬝ᵥ v) • q i,
      fun i => if i < k then q i ⬝ᵥ v else 0) := by
  induction k with
  | zero => simp [mgsLoop]
  | succ k ih =>
    have ih' := ih fun a ha b hb => hq a (by omega) b (by omega)
    simp only [mgsLoop, List.range_succ, List.foldlM_append, List.foldlM_cons, List.foldlM_nil,
      Id.run_bind, Id.run_pure, bind_pure] at ih' ⊢
    rw [ih']
    simp only [algorithm_1_1_1_spec, algorithm_1_1_2_spec]
    have hc : q k ⬝ᵥ (v - ∑ i ∈ Finset.range k, (q i ⬝ᵥ v) • q i) = q k ⬝ᵥ v := by
      rw [dotProduct_sub, dotProduct_sum]
      rw [Finset.sum_eq_zero fun i hi => by
        rw [dotProduct_smul, hq k (by omega) i (by simp at hi; omega),
          ite_eq_right (by simp at hi; omega), smul_zero], sub_zero]
    rw [hc]
    refine Prod.ext ?_ (funext fun i => ?_)
    · simp only [Finset.sum_range_succ]
      rw [neg_smul, ← sub_eq_add_neg, sub_sub]
    · by_cases hik : i = k
      · subst hik; simp
      · simp only [Function.update_of_ne hik]
        by_cases hi : i < k
        · rw [ite_eq_left hi, ite_eq_left (by omega)]
        · rw [ite_eq_right hi, ite_eq_right (by omega)]

/-- The `(k+1) × (k+1)` Arnoldi decomposition of a state, column by column. -/
private theorem isArnoldiDecomposition_iff_vec (A : Matrix (Fin n) (Fin n) ℝ)
    (s : ArnoldiState n) (K : ℕ) :
    IsArnoldiDecomposition A (s.qMatrix (K + 1)) (s.hMatrix (K + 1)) s.r ↔
      (∀ a < K + 1, ∀ b < K + 1, s.q a ⬝ᵥ s.q b = if a = b then 1 else 0) ∧
      (∀ a < K + 1, s.q a ⬝ᵥ s.r = 0) ∧
      (∀ b < K + 1, A *ᵥ s.q b =
        ∑ i ∈ Finset.range (K + 1), s.h i b • s.q i + if b + 1 = K + 1 then s.r else 0) ∧
      (∀ i < K + 1, ∀ l < K + 1, l + 1 < i → s.h i l = 0) := by
  have hQQ : ∀ a b : Fin (K + 1), ((s.qMatrix (K + 1))ᵀ * s.qMatrix (K + 1)) a b =
      s.q a ⬝ᵥ s.q b := fun a b => by
    simp [Matrix.mul_apply, ArnoldiState.qMatrix, dotProduct]
  have hQr : ∀ a : Fin (K + 1), ((s.qMatrix (K + 1))ᵀ *ᵥ s.r) a = s.q a ⬝ᵥ s.r := fun a => by
    simp [Matrix.mulVec, ArnoldiState.qMatrix, dotProduct]
  have hcol : ∀ (b : Fin (K + 1)) (x : Fin n),
      (A * s.qMatrix (K + 1)) x b = (A *ᵥ s.q b) x ∧
      (s.qMatrix (K + 1) * s.hMatrix (K + 1) +
          Matrix.vecMulVec s.r (Krylov.lastVec (1 : ℝ) (K + 1))) x b =
        (∑ i ∈ Finset.range (K + 1), s.h i b • s.q i +
          if (b : ℕ) + 1 = K + 1 then s.r else 0) x := fun b x => by
    refine ⟨by simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, ArnoldiState.qMatrix], ?_⟩
    simp only [Matrix.add_apply, Matrix.mul_apply, ArnoldiState.qMatrix, ArnoldiState.hMatrix,
      Matrix.of_apply, Matrix.vecMulVec_apply, Krylov.lastVec, Pi.add_apply, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul]
    rw [Fin.sum_univ_eq_sum_range (fun i => s.q i x * s.h i b)]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    · split_ifs <;> simp
  constructor
  · intro h
    refine ⟨fun a ha b hb => ?_, fun a ha => ?_, fun b hb => ?_, fun i hi l hl hil => ?_⟩
    · have := congrFun (congrFun h.transpose_mul_self ⟨a, ha⟩) ⟨b, hb⟩
      rw [hQQ, Matrix.one_apply] at this
      rw [this]
      simp [Fin.ext_iff]
    · have := congrFun h.transpose_mulVec ⟨a, ha⟩
      rwa [hQr] at this
    · ext x
      have := congrFun (congrFun h.mul_eq x) ⟨b, hb⟩
      rw [(hcol ⟨b, hb⟩ x).1, (hcol ⟨b, hb⟩ x).2] at this
      exact this
    · exact h.isUpperHessenberg ⟨i, hi⟩ ⟨l, hl⟩
        ((GolubVanLoan.Chapter05.exists_between_iff _ _).2 hil)
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨?_, fun i l hil => ?_, ?_, ?_⟩
    · ext a b
      rw [hQQ, h1 a a.isLt b b.isLt, Matrix.one_apply]
      simp [Fin.ext_iff]
    · exact h4 i i.isLt l l.isLt ((GolubVanLoan.Chapter05.exists_between_iff _ _).1 hil)
    · ext a
      rw [hQr, h2 a a.isLt]
      rfl
    · ext x b
      rw [(hcol b x).1, (hcol b x).2, h3 b b.isLt]

/-- One exact pass of Algorithm 10.5.1's loop body keeps the Arnoldi relations and the first
vector. -/
private theorem arnoldiStep_inv (A : Matrix (Fin n) (Fin n) ℝ) {s : ArnoldiState n}
    (hs : ArnoldiInv A s) :
    ArnoldiInv A (Id.run (arnoldiStep pure A s)) ∧ (Id.run (arnoldiStep pure A s)).q 0 = s.q 0 ∧
      s.k ≤ (Id.run (arnoldiStep pure A s)).k := by
  obtain ⟨hk0, horth, hperp, hrel, hzero, hnorm, hdone⟩ := hs
  cases hsd : s.done with
  | true =>
    have hid : Id.run (arnoldiStep pure A s) = s := by simp [arnoldiStep, hsd]
    rw [hid]
    exact ⟨⟨hk0, horth, hperp, hrel, hzero, hnorm, hdone⟩, rfl, le_rfl⟩
  | false =>
    set ρ := ‖(WithLp.toLp 2 s.r : EuclideanSpace ℝ (Fin n))‖ with hρ
    have hρ0 : ρ ≠ 0 := by simpa [hsd] using hdone.symm
    have hrr : s.r ⬝ᵥ s.r = ρ ^ 2 := by
      rw [hρ, ← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct,
        star_trivial]
    have hhk : (if s.k = 0 then 1 else s.h s.k (s.k - 1)) = ρ := by
      rw [ite_eq_right (by omega), hnorm]
    set qk := ρ⁻¹ • s.r with hqk
    set q' := Function.update s.q s.k qk with hq'
    have hq'old : ∀ a < s.k, q' a = s.q a := fun a ha => Function.update_of_ne ha.ne _ _
    have hq'new : q' s.k = qk := Function.update_self _ _ _
    have horth' : ∀ a < s.k + 1, ∀ b < s.k + 1, q' a ⬝ᵥ q' b = if a = b then 1 else 0 := by
      have hnew : ∀ a < s.k, q' a ⬝ᵥ q' s.k = 0 := fun a ha => by
        rw [hq'old a ha, hq'new, hqk, dotProduct_smul, hperp a ha, smul_zero]
      intro a ha b hb
      rcases Nat.lt_succ_iff_lt_or_eq.1 ha with ha | rfl
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hb with hb | rfl
        · rw [hq'old a ha, hq'old b hb]; exact horth a ha b hb
        · rw [hnew a ha, ite_eq_right ha.ne]
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hb with hb | rfl
        · rw [dotProduct_comm, hnew b hb, ite_eq_right hb.ne']
        · rw [ite_eq_left rfl, hq'new, hqk, dotProduct_smul, smul_dotProduct, hrr, smul_eq_mul,
            smul_eq_mul]
          field_simp
    have hmgs := mgsLoop_orthonormal q' (s.k + 1) (A *ᵥ qk) horth'
    set w := A *ᵥ qk - ∑ i ∈ Finset.range (s.k + 1), (q' i ⬝ᵥ A *ᵥ qk) • q' i with hw
    have hperp' : ∀ a < s.k + 1, q' a ⬝ᵥ w = 0 := by
      intro a ha
      rw [hw, dotProduct_sub, dotProduct_sum, Finset.sum_eq_single a (fun i hi hia => by
        rw [dotProduct_smul, horth' a ha i (Finset.mem_range.1 hi), ite_eq_right (Ne.symm hia),
          smul_zero]) (fun h => absurd (Finset.mem_range.2 ha) h), dotProduct_smul,
        horth' a ha a ha, ite_eq_left rfl, smul_eq_mul, mul_one, sub_self]
    simp only [arnoldiStep, hsd, Bool.false_eq_true, ↓reduceIte, Id.run_bind, Id.run_pure,
      vecDiv_spec, algorithm_1_1_3_spec, zero_add, vecNorm_spec, hhk]
    rw [← hqk, ← hq', hmgs]
    unfold ArnoldiInv
    dsimp only
    refine ⟨⟨Nat.succ_pos _, horth', hperp', fun b hb => ?_, fun i l hil => ?_, ?_, ?_⟩,
      hq'old 0 hk0, Nat.le_succ _⟩
    · rw [Finset.sum_range_succ]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hb with hb | rfl
      · -- an old column
        rw [Finset.sum_congr rfl (g := fun i => s.h i b • s.q i) fun i hi => by
          simp only [ite_eq_right hb.ne, hq'old i (Finset.mem_range.1 hi)]]
        rw [ite_eq_right hb.ne, ite_eq_right (show b + 1 ≠ s.k + 1 by omega), hq'old b hb, hq'new,
          hrel b hb, add_zero]
        rcases Nat.lt_or_ge (b + 1) s.k with hbk | hbk
        · rw [ite_eq_right hbk.ne, hzero s.k b hbk, zero_smul, add_zero]
        · rw [ite_eq_left (by omega), show b = s.k - 1 by omega, hnorm, hqk, smul_smul,
            mul_inv_cancel₀ hρ0, one_smul]
      · -- the new column
        rw [Finset.sum_congr rfl (g := fun i => (q' i ⬝ᵥ A *ᵥ qk) • q' i) fun i hi => by
          have := Finset.mem_range.1 hi
          simp only [↓reduceIte, ite_eq_right (show i ≠ s.k + 1 by omega),
            ite_eq_left (show i < s.k + 1 by omega)]]
        simp only [↓reduceIte, ite_eq_right (show s.k ≠ s.k + 1 by omega),
          ite_eq_left (show s.k < s.k + 1 by omega)]
        rw [hw, Finset.sum_range_succ, hq'new]
        abel
    · -- zeros below the subdiagonal
      by_cases hl : l = s.k
      · rw [ite_eq_left hl, ite_eq_right (by omega), ite_eq_right (by omega)]
      · rw [ite_eq_right hl]; exact hzero i l hil
    · simp
    · rfl

/-- `t` exact passes of the loop body keep the Arnoldi relations and the first vector. -/
private theorem arnoldiSteps_inv (A : Matrix (Fin n) (Fin n) ℝ) (t : ℕ) {s : ArnoldiState n}
    (hs : ArnoldiInv A s) :
    ArnoldiInv A (Id.run ((List.range t).foldlM (fun s _ => arnoldiStep pure A s) s)) ∧
      (Id.run ((List.range t).foldlM (fun s _ => arnoldiStep pure A s) s)).q 0 = s.q 0 := by
  induction t with
  | zero => exact ⟨hs, rfl⟩
  | succ t ih =>
    simp only [List.range_succ, List.foldlM_append, List.foldlM_cons, List.foldlM_nil,
      bind_pure, Id.run_bind]
    obtain ⟨h1, h2, -⟩ := arnoldiStep_inv A ih.1
    exact ⟨h1, h2.trans ih.2⟩

/-- The exact state from which the continued Arnoldi steps of an implicit restart start:
`Q₊ = Q_c V` truncated to `j + 1` columns, `H₊` to its leading `(j+1) × (j+1)` block, the corrected
residual and `h_{j+1,j} = ‖r₊‖`. -/
private noncomputable def restartState (j p : ℕ) (s : ArnoldiState n)
    (st : ShiftedQrState (j + p)) :
    ArnoldiState n :=
  let Qp := s.qMatrix (j + p + 1) * st.acc
  let r := st.acc (Fin.last (j + p)) ⟨j, by omega⟩ • s.r +
    (if h : j + 1 < j + p + 1 then st.H p ⟨j + 1, h⟩ ⟨j, by omega⟩ else 0) •
      (fun i => if h : j + 1 < j + p + 1 then Qp i ⟨j + 1, h⟩ else 0)
  { k := j + 1
    q := fun l i => if h : l < j + p + 1 then Qp i ⟨l, h⟩ else 0
    h := fun i l => if h : i < j + 1 ∧ l < j + 1 then st.H p ⟨i, by omega⟩ ⟨l, by omega⟩
      else if i = j + 1 ∧ l = j then ‖(WithLp.toLp 2 r : EuclideanSpace ℝ (Fin n))‖ else 0
    r := r
    done := decide (‖(WithLp.toLp 2 r : EuclideanSpace ℝ (Fin n))‖ = 0) }

/-- The exact cycle is the continued Arnoldi steps from `restartState`. -/
private theorem implicitRestartCycle_eq (A : Matrix (Fin n) (Fin n) ℝ) (j p : ℕ)
    (shifts : Matrix (Fin (j + p + 1)) (Fin (j + p + 1)) ℝ → ℕ → ℝ) (s : ArnoldiState n) :
    Id.run (implicitRestartCycle pure A j p shifts s) =
      Id.run ((List.range p).foldlM (fun s _ => arnoldiStep pure A s) (restartState j p s
        (Id.run (shiftedQrSteps pure (s.hMatrix (j + p + 1))
          (shifts (s.hMatrix (j + p + 1))) p)))) := by
  simp only [implicitRestartCycle, restartState, Id.run_bind, algorithm_1_1_5_spec,
    algorithm_1_1_2_spec, vecNorm_spec, zero_add]

/-- **One cycle of the implicitly restarted framework** (exact arithmetic, `p ≥ 1`): if the input
state is an `m`-step Arnoldi decomposition (`m = j + p + 1`) and the continued Arnoldi steps do not
break down (the output again has `m` columns), then the output is an `m`-step Arnoldi decomposition
whose first column `q₊` satisfies `R(1,1) q₊ = p(A) q₁` for the cycle's filter polynomial. -/
theorem implicitRestartCycle_spec (A : Matrix (Fin n) (Fin n) ℝ) {j p : ℕ} (hp : 0 < p)
    (shifts : Matrix (Fin (j + p + 1)) (Fin (j + p + 1)) ℝ → ℕ → ℝ) {s : ArnoldiState n}
    (hs : IsArnoldiDecomposition A (s.qMatrix (j + p + 1)) (s.hMatrix (j + p + 1)) s.r) :
    let Hc := s.hMatrix (j + p + 1)
    let st := Id.run (shiftedQrSteps pure Hc (shifts Hc) p)
    let s' := Id.run (implicitRestartCycle pure A j p shifts s)
    s'.k = j + p + 1 →
      IsArnoldiDecomposition A (s'.qMatrix (j + p + 1)) (s'.hMatrix (j + p + 1)) s'.r ∧
      ((List.range p).reverse.map st.R).prod 0 0 • (s'.qMatrix (j + p + 1) *ᵥ Pi.single 0 1) =
        aeval A (filterPolynomial (shifts Hc) p) *ᵥ (s.qMatrix (j + p + 1) *ᵥ Pi.single 0 1) := by
  intro Hc st s' hk
  simp only [s', st, Hc, implicitRestartCycle_eq] at hk ⊢
  obtain ⟨h0, hc, hVR, hHs, hacc⟩ := equation_10_5_4 (Hc := s.hMatrix (j + p + 1))
    hs.isUpperHessenberg (shifts (s.hMatrix (j + p + 1))) p
  generalize Id.run (shiftedQrSteps pure (s.hMatrix (j + p + 1))
    (shifts (s.hMatrix (j + p + 1))) p) = st at hk h0 hc hVR hHs hacc ⊢
  have hjp : j + 1 < j + p + 1 := by omega
  obtain ⟨-, hT⟩ := implicitRestart_isArnoldiDecomposition hs hc h0 (fun i hi => (hVR i hi).1)
    (fun i hi => (hVR i hi).2.1) (fun i hi => (hVR i hi).2.2) hp
  rw [← hacc] at hT
  set s₀ := restartState j p s st with hs₀
  have hT' : IsArnoldiDecomposition A (s₀.qMatrix (j + 1)) (s₀.hMatrix (j + 1)) s₀.r := by
    convert hT using 1
    · ext i l
      have := l.isLt
      simp only [s₀, restartState, ArnoldiState.qMatrix, Matrix.of_apply, Matrix.submatrix_apply,
        id]
      split_ifs with h
      · rfl
      · omega
    · ext i l
      have := i.isLt
      have := l.isLt
      simp only [s₀, restartState, ArnoldiState.hMatrix, Matrix.of_apply, Matrix.submatrix_apply]
      split_ifs with h h' <;> first | rfl | exact absurd ⟨by omega, by omega⟩ h
    · simp only [s₀, restartState, hjp, ↓reduceDIte]
      rw [add_comm]
      rfl
  obtain ⟨h1, h2, h3, -⟩ := (isArnoldiDecomposition_iff_vec A s₀ j).1 hT'
  have hinv : ArnoldiInv A s₀ := by
    refine ⟨by simp [s₀, restartState], h1, h2, h3, fun i l hil => ?_, ?_, rfl⟩
    · simp only [s₀, restartState]
      split_ifs with h h'
      · exact (hHs p le_rfl) ⟨i, by omega⟩ ⟨l, by omega⟩
          ((GolubVanLoan.Chapter05.exists_between_iff _ _).2 hil)
      · omega
      · rfl
    · simp [s₀, restartState]
  obtain ⟨hinv', hq0⟩ := arnoldiSteps_inv A p hinv
  obtain ⟨-, i1, i2, i3, i4, -, -⟩ := hinv'
  rw [hk] at i1 i2 i3
  refine ⟨(isArnoldiDecomposition_iff_vec A _ (j + p)).2
    ⟨i1, i2, i3, fun i _ l _ h => i4 i l h⟩, ?_⟩
  have hfirst : ArnoldiState.qMatrix (Id.run ((List.range p).foldlM
      (fun s _ => arnoldiStep pure A s) s₀)) (j + p + 1) *ᵥ Pi.single 0 1 =
      (s.qMatrix (j + p + 1) * ((List.range p).map st.V).prod) *ᵥ Pi.single 0 1 := by
    ext x
    simp only [Matrix.mulVec_single_one, Matrix.col_apply, ArnoldiState.qMatrix,
      Matrix.of_apply, Fin.val_zero, hq0]
    simp [s₀, restartState, hacc]
    rfl
  rw [hfirst]
  exact (restart_firstColumn_eq hs).2 hc h0 fun i hi => (hVR i hi).2.2

/-- The run after `ℓ + 1` cycles is one more cycle. -/
private theorem implicitlyRestartedArnoldi_succ (A : Matrix (Fin n) (Fin n) ℝ) (j p : ℕ)
    (shifts : Matrix (Fin (j + p + 1)) (Fin (j + p + 1)) ℝ → ℕ → ℝ) (q₁ : Fin n → ℝ) (ℓ : ℕ) :
    Id.run (implicitlyRestartedArnoldi pure A j p shifts q₁ (ℓ + 1)) =
      Id.run (implicitRestartCycle pure A j p shifts
        (Id.run (implicitlyRestartedArnoldi pure A j p shifts q₁ ℓ))) := by
  simp only [implicitlyRestartedArnoldi, List.range_succ, List.foldlM_append, List.foldlM_cons,
    List.foldlM_nil, bind_pure, Id.run_bind]

/-- **Exact semantics of implicitly restarted Arnoldi** (`p ≥ 1`, unit `q₁` with
`m = j + p + 1 ≤ grade`): as long as no continued Arnoldi step breaks down (every state after
`ℓ ≤ L` cycles has `m` columns), the state after every cycle is an `m`-step Arnoldi decomposition
`A Q_m = Q_m H_m + r_m e_mᵀ`, and its first column is `R_ℓ(1,1)⁻¹ p_ℓ(A)` applied to the previous
first column (`p_ℓ` the cycle's filter polynomial, `R_ℓ` the product of its triangular factors) —
the starting vector explicit restarting (10.5.10) would use, obtained without restarting from step
1 (by the implicit Q theorem `Matrix.IsArnoldiDecomposition.implicitQ`, an unreduced such
decomposition is determined by its first column). -/
theorem implicitlyRestartedArnoldi_spec (A : Matrix (Fin n) (Fin n) ℝ) {j p : ℕ} (hp : 0 < p)
    (shifts : Matrix (Fin (j + p + 1)) (Fin (j + p + 1)) ℝ → ℕ → ℝ) {q₁ : Fin n → ℝ}
    (hq : ‖(WithLp.toLp 2 q₁ : EuclideanSpace ℝ (Fin n))‖ = 1)
    (hg : j + p + 1 ≤ grade (Matrix.toEuclideanLin A) (WithLp.toLp 2 q₁)) (L : ℕ) :
    let S : ℕ → ArnoldiState n := fun ℓ =>
      Id.run (implicitlyRestartedArnoldi pure A j p shifts q₁ ℓ)
    let H : ℕ → Matrix (Fin (j + p + 1)) (Fin (j + p + 1)) ℝ := fun ℓ =>
      (S ℓ).hMatrix (j + p + 1)
    let ρ : ℕ → ℝ := fun ℓ =>
      ((List.range p).reverse.map (Id.run (shiftedQrSteps pure (H ℓ) (shifts (H ℓ)) p)).R).prod
        0 0
    (∀ ℓ ≤ L, (S ℓ).k = j + p + 1) →
      (∀ ℓ ≤ L, IsArnoldiDecomposition A ((S ℓ).qMatrix (j + p + 1)) (H ℓ) (S ℓ).r) ∧
      (S 0).qMatrix (j + p + 1) *ᵥ Pi.single 0 1 = q₁ ∧
      ∀ ℓ < L, ρ ℓ • ((S (ℓ + 1)).qMatrix (j + p + 1) *ᵥ Pi.single 0 1) =
        aeval A (filterPolynomial (shifts (H ℓ)) p) *ᵥ
          ((S ℓ).qMatrix (j + p + 1) *ᵥ Pi.single 0 1) := by
  intro S H ρ hk
  have hsucc : ∀ ℓ, S (ℓ + 1) = Id.run (implicitRestartCycle pure A j p shifts (S ℓ)) :=
    implicitlyRestartedArnoldi_succ A j p shifts q₁
  obtain ⟨-, hQ0, hH0, hr0⟩ := algorithm_10_5_1_matrices A hq hg
  have hS0 : S 0 = Id.run (algorithm_10_5_1 pure A q₁ (j + p + 1)) := by
    simp [S, implicitlyRestartedArnoldi]
  have hdec : ∀ ℓ ≤ L, IsArnoldiDecomposition A ((S ℓ).qMatrix (j + p + 1)) (H ℓ) (S ℓ).r := by
    intro ℓ hℓ
    induction ℓ with
    | zero =>
      simp only [H]
      rw [hS0, hQ0, hH0, hr0 (by omega)]
      exact (equation_10_5_2 A (WithLp.toLp 2 q₁) (k := j + p + 1) (by omega)).2.2 hg
    | succ ℓ ih =>
      have h := implicitRestartCycle_spec A hp shifts (ih (by omega))
      simp only [H] at h ⊢
      rw [hsucc] at ⊢
      exact (h (by rw [← hsucc]; exact hk (ℓ + 1) hℓ)).1
  refine ⟨hdec, by rw [hS0, hQ0]; exact basisMatrix_mulVec_single_zero A hq _, fun ℓ hℓ => ?_⟩
  have h := implicitRestartCycle_spec A hp shifts (hdec ℓ hℓ.le)
  rw [hsucc]
  exact (h (by rw [← hsucc]; exact hk (ℓ + 1) hℓ)).2

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

/-- The biorthogonality kept by the exact run of (10.5.11): `q̃_aᵀ q_b = δ_ab`, the residuals are
orthogonal to the opposite family, the computed `β`, `γ` are nonzero, and the first vectors are
nonzero multiples of `q₁`, `q̃₁`. -/
private theorem unsym_biorth {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (q₁ qt₁ : Fin n → ℝ)
    (t : ℕ) :
    let st := Id.run (unsymmetricLanczos pure A q₁ qt₁ t)
    (∀ a < st.k, ∀ b < st.k, st.qt a ⬝ᵥ st.q b = if a = b then 1 else 0) ∧
    (∀ a < st.k, st.qt a ⬝ᵥ st.r = 0) ∧ (∀ a < st.k, st.s ⬝ᵥ st.q a = 0) ∧
    (∀ a < st.k, st.beta a ≠ 0 ∧ st.gamma a ≠ 0) ∧
    (st.k = 0 → st.r = q₁ ∧ st.s = qt₁) ∧
    (0 < st.k → st.q 0 = (st.beta 0)⁻¹ • q₁ ∧ st.qt 0 = (st.gamma 0)⁻¹ • qt₁) := by
  intro st
  let P : UnsymLanczosState n → Prop := fun st =>
    (∀ a < st.k, ∀ b < st.k, st.qt a ⬝ᵥ st.q b = if a = b then 1 else 0) ∧
    (∀ a < st.k, st.qt a ⬝ᵥ st.r = 0) ∧ (∀ a < st.k, st.s ⬝ᵥ st.q a = 0) ∧
    (∀ a < st.k, st.beta a ≠ 0 ∧ st.gamma a ≠ 0) ∧
    (st.k = 0 → st.r = q₁ ∧ st.s = qt₁) ∧
    (0 < st.k → st.q 0 = (st.beta 0)⁻¹ • q₁ ∧ st.qt 0 = (st.gamma 0)⁻¹ • qt₁)
  suffices hP : ∀ t, P (Id.run (unsymmetricLanczos pure A q₁ qt₁ t)) from hP t
  intro t
  induction t with
  | zero =>
    refine ⟨fun a ha => ?_, fun a ha => ?_, fun a ha => ?_, fun a ha => ?_, fun _ => ?_,
      fun h => ?_⟩ <;> simp [unsymmetricLanczos] at *
  | succ t ih =>
    have hrelt := unsym_relations A q₁ qt₁ t
    rw [unsymmetricLanczos_succ]
    set s0 := Id.run (unsymmetricLanczos pure A q₁ qt₁ t) with hs0
    obtain ⟨hdone, hrel⟩ := hrelt
    obtain ⟨I1, I2, I3, I4, I5, I6⟩ := ih
    cases hsd : s0.done with
    | true =>
      simp only [unsymLanczosStep, hsd, ↓reduceIte, Id.run_pure]
      exact ⟨I1, I2, I3, I4, I5, I6⟩
    | false =>
      have htest : ¬ (s0.r = 0 ∨ s0.s = 0 ∨ s0.s ⬝ᵥ s0.r = 0) := by
        simpa [hsd] using hdone.symm
      push Not at htest
      obtain ⟨hr0, -, hsr⟩ := htest
      simp only [P, unsymLanczosStep, hsd, Bool.false_eq_true, ↓reduceIte, Id.run_bind,
        Id.run_pure, vecNorm_spec, algorithm_1_1_1_spec, vecDiv_spec, algorithm_1_1_3_spec,
        algorithm_1_1_2_spec, zero_add]
      set β := ‖(WithLp.toLp 2 s0.r : EuclideanSpace ℝ (Fin n))‖ with hβ
      have hβ0 : β ≠ 0 := by
        rw [hβ, norm_ne_zero_iff]
        intro h
        exact hr0 (by simpa using congrArg WithLp.ofLp h)
      set γ := s0.s ⬝ᵥ s0.r / β with hγ
      have hγ0 : γ ≠ 0 := div_ne_zero hsr hβ0
      have hβγ : γ * β = s0.s ⬝ᵥ s0.r := by rw [hγ]; field_simp
      set qn := β⁻¹ • s0.r with hqn
      set qtn := γ⁻¹ • s0.s with hqtn
      set α := qtn ⬝ᵥ A *ᵥ qn with hα
      set pv := if s0.k = 0 then (0 : Fin n → ℝ) else s0.q (s0.k - 1) with hpv
      set pvt := if s0.k = 0 then (0 : Fin n → ℝ) else s0.qt (s0.k - 1) with hpvt
      set q' := Function.update s0.q s0.k qn with hq'
      set qt' := Function.update s0.qt s0.k qtn with hqt'
      have hq'o : ∀ a < s0.k, q' a = s0.q a := fun a ha => Function.update_of_ne ha.ne _ _
      have hqt'o : ∀ a < s0.k, qt' a = s0.qt a := fun a ha => Function.update_of_ne ha.ne _ _
      have hq'n : q' s0.k = qn := Function.update_self _ _ _
      have hqt'n : qt' s0.k = qtn := Function.update_self _ _ _
      -- the new biorthogonality
      have hqtq_new : ∀ a < s0.k, s0.qt a ⬝ᵥ qn = 0 := fun a ha => by
        rw [hqn, dotProduct_smul, I2 a ha, smul_zero]
      have hqtnq : ∀ a < s0.k, qtn ⬝ᵥ s0.q a = 0 := fun a ha => by
        rw [hqtn, smul_dotProduct, I3 a ha, smul_zero]
      have hnn : qtn ⬝ᵥ qn = 1 := by
        rw [hqtn, hqn, smul_dotProduct, dotProduct_smul, ← hβγ, smul_eq_mul, smul_eq_mul]
        field_simp
      have J1 : ∀ a < s0.k + 1, ∀ b < s0.k + 1, qt' a ⬝ᵥ q' b = if a = b then 1 else 0 := by
        intro a ha b hb
        rcases Nat.lt_succ_iff_lt_or_eq.1 ha with ha | rfl
        · rcases Nat.lt_succ_iff_lt_or_eq.1 hb with hb | rfl
          · rw [hqt'o a ha, hq'o b hb]; exact I1 a ha b hb
          · rw [hqt'o a ha, hq'n, hqtq_new a ha, ite_eq_right ha.ne]
        · rcases Nat.lt_succ_iff_lt_or_eq.1 hb with hb | rfl
          · rw [hqt'n, hq'o b hb, hqtnq b hb, ite_eq_right hb.ne']
          · rw [hqt'n, hq'n, hnn, ite_eq_left rfl]
      -- products with `A`
      have hAq : ∀ a < s0.k, s0.qt a ⬝ᵥ A *ᵥ qn = if a + 1 = s0.k then γ else 0 := by
        intro a ha
        rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, (hrel a ha).2]
        simp only [add_dotProduct, smul_dotProduct, smul_eq_mul]
        have h1 : (if a = 0 then (0 : Fin n → ℝ) else s0.qt (a - 1)) ⬝ᵥ qn = 0 := by
          split_ifs
          · simp
          · exact hqtq_new _ (by omega)
        rw [h1, hqtq_new a ha, mul_zero, mul_zero, zero_add, zero_add]
        split_ifs with h2 h3 h3
        · omega
        · rw [smul_dotProduct, hqtq_new _ h2, smul_zero]
        · rw [hqn, dotProduct_smul, smul_eq_mul, hγ]; ring
        · omega
      have hAqt : ∀ a < s0.k, qtn ⬝ᵥ A *ᵥ s0.q a = if a + 1 = s0.k then β else 0 := by
        intro a ha
        rw [(hrel a ha).1]
        simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]
        have h1 : qtn ⬝ᵥ (if a = 0 then (0 : Fin n → ℝ) else s0.q (a - 1)) = 0 := by
          split_ifs
          · simp
          · exact hqtnq _ (by omega)
        rw [h1, hqtnq a ha, mul_zero, mul_zero, zero_add, zero_add]
        split_ifs with h2 h3 h3
        · omega
        · rw [dotProduct_smul, hqtnq _ h2, smul_zero]
        · rw [hqtn, smul_dotProduct, smul_eq_mul, ← hβγ]
          field_simp
        · omega
      refine ⟨J1, fun a ha => ?_, fun a ha => ?_, fun a ha => ?_, fun h => by omega,
        fun _ => ?_⟩
      · -- `q̃_aᵀ r_{k+1} = 0`
        simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]
        rcases Nat.lt_succ_iff_lt_or_eq.1 ha with ha | rfl
        · rw [hqt'o a ha, hAq a ha, hqtq_new a ha]
          have hpv' : s0.qt a ⬝ᵥ pv = if a + 1 = s0.k then 1 else 0 := by
            rw [hpv, ite_eq_right (by omega), I1 a ha _ (by omega)]
            split_ifs <;> first | rfl | omega
          rw [hpv']
          split_ifs <;> ring
        · rw [hqt'n, ← hα, hnn]
          have : qtn ⬝ᵥ pv = 0 := by
            rw [hpv]; split_ifs
            · simp
            · exact hqtnq _ (by omega)
          rw [this]; ring
      · -- `r̃_{k+1}ᵀ q_a = 0`
        simp only [add_dotProduct, smul_dotProduct, smul_eq_mul]
        rcases Nat.lt_succ_iff_lt_or_eq.1 ha with ha | rfl
        · rw [hq'o a ha, Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec, hAqt a ha,
            hqtnq a ha]
          have hpv' : pvt ⬝ᵥ s0.q a = if a + 1 = s0.k then 1 else 0 := by
            rw [hpvt, ite_eq_right (by omega), I1 _ (by omega) a ha]
            split_ifs <;> first | rfl | omega
          rw [hpv']
          split_ifs <;> ring
        · rw [hq'n, Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec, ← hα, hnn]
          have : pvt ⬝ᵥ qn = 0 := by
            rw [hpvt]; split_ifs
            · simp
            · exact hqtq_new _ (by omega)
          rw [this]; ring
      · rcases Nat.lt_succ_iff_lt_or_eq.1 ha with ha | rfl
        · rw [Function.update_of_ne ha.ne, Function.update_of_ne ha.ne]; exact I4 a ha
        · rw [Function.update_self, Function.update_self]; exact ⟨hβ0, hγ0⟩
      · rcases Nat.eq_zero_or_pos s0.k with h0 | h0
        · obtain ⟨hr, hs⟩ := I5 h0
          rw [← h0, Function.update_self, Function.update_self, hq'n, hqt'n, hqn, hqtn, hr, hs]
          exact ⟨rfl, rfl⟩
        · rw [Function.update_of_ne h0.ne, Function.update_of_ne h0.ne, hq'o 0 h0, hqt'o 0 h0]
          exact I6 h0

/-- A three-term recurrence spans the Krylov subspaces: if `v_0` is a nonzero multiple of `v₁` and
`B v_a = c₁_a v_{a−1} + c₂_a v_a + c₃_{a+1} v_{a+1}` with `c₃_{a+1} ≠ 0` for `a + 1 < k`, then
`span {v_0, …, v_{j−1}} = 𝒦_j(B, v₁)` for `j ≤ k` (`Krylov.span_eq_subspace_of_threeTerm` in
coordinates). -/
private theorem span_eq_subspace_of_threeTerm {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (v : ℕ → Fin n → ℝ) (v₁ : Fin n → ℝ) (k : ℕ) (c c₁ c₂ c₃ : ℕ → ℝ)
    (h0 : 0 < k → v 0 = c 0 • v₁ ∧ c 0 ≠ 0)
    (hrel : ∀ a, a + 1 < k → B *ᵥ v a =
      c₁ a • (if a = 0 then 0 else v (a - 1)) + c₂ a • v a + c₃ (a + 1) • v (a + 1))
    (hne : ∀ a < k, c₃ a ≠ 0) :
    ∀ j ≤ k, Submodule.span ℝ (Set.range fun i : Fin j =>
        (WithLp.toLp 2 (v i) : EuclideanSpace ℝ (Fin n))) =
      Krylov.subspace (Matrix.toEuclideanLin B) (WithLp.toLp 2 v₁) j :=
  Krylov.span_eq_subspace_of_threeTerm (Matrix.toEuclideanLin B) (fun i => WithLp.toLp 2 (v i))
    (WithLp.toLp 2 v₁) k (c 0) c₁ c₂ c₃
    (fun hk => ⟨by rw [(h0 hk).1, WithLp.toLp_smul], (h0 hk).2⟩)
    (fun a ha => by
      rw [Matrix.toEuclideanLin_toLp, hrel a ha]
      split_ifs <;> simp only [WithLp.toLp_add, WithLp.toLp_smul, WithLp.toLp_zero])
    hne
/-- **Exact semantics of (10.5.11)**: for any run (the loop stops at breakdown, so every executed
pass had `r_k ≠ 0`, `r̃_k ≠ 0`, `r̃_kᵀ r_k ≠ 0`), with `k` passes, the computed families are
biorthonormal, `Q̃_kᵀ Q_k = I_k`; they span the Krylov subspaces,
`span {q_1, …, q_j} = 𝒦(A, q₁, j)` and `span {q̃_1, …, q̃_j} = 𝒦(Aᵀ, q̃₁, j)` for `j ≤ k`; and
`Q̃_kᵀ A Q_k = T_k`, the tridiagonal matrix of the computed `α`, `β`, `γ`. Proved directly from the
recurrences (10.5.12)–(10.5.13) (the book's derivation, whose normalization `β_k = ‖r_k‖₂` differs
from the backbone `BiLanczos`'s `δ_{j+1} = |⟪ŵ, v̂⟫|^{1/2}`). -/
theorem equation_10_5_11 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (q₁ qt₁ : Fin n → ℝ)
    (fuel : ℕ) :
    let st := Id.run (unsymmetricLanczos pure A q₁ qt₁ fuel)
    (unsymQt st st.k)ᵀ * unsymQ st st.k = 1 ∧
      (∀ j ≤ st.k, Submodule.span ℝ (Set.range fun i : Fin j =>
          (WithLp.toLp 2 (st.q i) : EuclideanSpace ℝ (Fin n))) =
        Krylov.subspace (Matrix.toEuclideanLin A) (WithLp.toLp 2 q₁) j) ∧
      (∀ j ≤ st.k, Submodule.span ℝ (Set.range fun i : Fin j =>
          (WithLp.toLp 2 (st.qt i) : EuclideanSpace ℝ (Fin n))) =
        Krylov.subspace (Matrix.toEuclideanLin Aᵀ) (WithLp.toLp 2 qt₁) j) ∧
      (unsymQt st st.k)ᵀ * A * unsymQ st st.k = unsymTridiag st st.k := by
  intro st
  obtain ⟨I1, I2, -, I4, -, I6⟩ := unsym_biorth A q₁ qt₁ fuel
  have hrel := (unsym_relations A q₁ qt₁ fuel).2
  have hQQ : (unsymQt st st.k)ᵀ * unsymQ st st.k = 1 := by
    ext a b
    have := I1 a a.isLt b b.isLt
    simp only [Matrix.mul_apply, Matrix.transpose_apply, unsymQt, unsymQ, Matrix.of_apply,
      Matrix.one_apply, Fin.ext_iff]
    exact this
  refine ⟨hQQ, span_eq_subspace_of_threeTerm A st.q q₁ st.k (fun _ => (st.beta 0)⁻¹)
    st.gamma st.alpha st.beta (fun hk => ⟨(I6 hk).1, inv_ne_zero (I4 0 hk).1⟩)
    (fun a ha => by
      have h := (hrel a (Nat.lt_of_succ_lt ha)).1
      rwa [ite_eq_left ha] at h) (fun a ha => (I4 a ha).1),
    span_eq_subspace_of_threeTerm Aᵀ st.qt qt₁ st.k (fun _ => (st.gamma 0)⁻¹)
    st.beta st.alpha st.gamma (fun hk => ⟨(I6 hk).2, inv_ne_zero (I4 0 hk).2⟩)
    (fun a ha => by
      have h := (hrel a (Nat.lt_of_succ_lt ha)).2
      rwa [ite_eq_left ha] at h) (fun a ha => (I4 a ha).2), ?_⟩
  have h12 := equation_10_5_12 A q₁ qt₁ fuel
  have hQr : (unsymQt st st.k)ᵀ *ᵥ st.r = 0 := by
    ext a
    have := I2 a a.isLt
    simpa [Matrix.mulVec, dotProduct, unsymQt] using this
  rw [Matrix.mul_assoc, h12, Matrix.mul_add, ← Matrix.mul_assoc, hQQ, Matrix.one_mul,
    Matrix.mul_vecMulVec, hQr, Matrix.zero_vecMulVec, add_zero]


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
