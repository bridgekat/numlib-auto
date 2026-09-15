import NumlibSurface.QuarteroniSaccoSaleri.Chapter03.Section12

/-!
# Quarteroni–Sacco–Saleri §3.13: undetermined systems

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*
[quarteroni2000numerical], §3.13, over the backbone `Numlib/LinearAlgebra/Matrix/LeastSquares`
(least-squares solutions, the normal equations, the QR route, the solution of least norm) and
`Numlib/LinearAlgebra/Matrix/SVD` (the pseudoinverse `Matrix.pinv`).

## Conventions

A matrix `A ∈ ℝ^{m×n}` is `Matrix (Fin m) (Fin n) ℝ`, vectors are `Fin m → ℝ`, `Fin n → ℝ`, and
the Euclidean norm of §3.1 is `‖toLp 2 x‖`; the functional of (3.73) is
`Φ(x) = ‖toLp 2 (A *ᵥ x - b)‖ ^ 2`. "`A` has full rank" for `m ≥ n` is `LinearIndependent ℝ Aᵀ`
(independent columns), and for `m < n` it is `LinearIndependent ℝ A` (independent rows), as in
§3.4.3. The backbone states everything on `EuclideanSpace ℝ (Fin m)` through
`Matrix.toEuclideanLin`; the restatements `equation_3_73` and `equation_3_76` are the book's
problems on plain vectors, and `equation_3_73_iff`, `equation_3_76_iff` are the bridges. The QR
factorization and its reduced factors `Q̃ = firstColumns Q h`, `R̃ = firstRows R h` are those of
§3.4.3 (`property_3_3`). The pseudoinverse `A⁺` of Definition 1.15 is the backbone's
`Matrix.pinv A`, the unique matrix satisfying the Penrose conditions (`Matrix.pinv_unique`); its
expression `V Σ⁺ Uᵀ` through an SVD is chapter 1's business, and Theorem 3.9's "with SVD
`A = U Σ Vᵀ`" is no hypothesis, every matrix having one.

## Contents

* `equation_3_73`, `equation_3_73_iff`, `equation_3_74`, `normalMatrix_posDef`,
  `normalEquations_cholesky` — the least-squares problem and the normal equations.
* `theorem_3_8`, `theorem_3_8_min` — the QR route, (3.75), and the value of the minimum.
* `equation_3_76`, `equation_3_76_iff`, `equation_3_76_of_linearIndependent`, `theorem_3_9`,
  `theorem_3_9_unique` — the solution of least norm and the pseudoinverse, (3.77).
* `example_3_11`, `example_3_11_perturbed` — the discontinuity of `x*` in the data.
* `underdetermined_minNorm`, `underdetermined_qr` — the underdetermined full-rank case.

The `fl(Aᵀ A)` example (a floating-point computation), Remark 3.8 (flop counts) and Example 3.12
(a numerical run on `H₁₅`) state no theorem and are not nodes.

## Readings

The book's (3.73) reads `Φ(x*) ≤ min_x Φ(x)`; it is stated as `∀ x, Φ(x*) ≤ Φ(x)`. The sums
`∑_{i = n+1}^{m}` of Theorem 3.8 are over the `0`-based indices `n ≤ i < m`. Example 3.11 says
"rank(A) = 1" and "the perturbed matrix has (full) rank 2"; the statement gives `A.rank = 1`
together with the dependence of the columns, and `A_ε.rank = 2` with their independence.
-/

open Finset Matrix WithLp

namespace QuarteroniSaccoSaleri.Chapter03

variable {m n : ℕ}

/-! ### (3.73)–(3.74): least-squares solutions and the normal equations -/

/-- **(3.73).** Given `A ∈ ℝ^{m×n}` (`m ≥ n`) and `b ∈ ℝᵐ`, `x* ∈ ℝⁿ` is a solution of `A x = b`
*in the least-squares sense* if `Φ(x*) = ‖A x* - b‖₂² ≤ min_x ‖A x - b‖₂² = min_x Φ(x)`: the
backbone's `Matrix.IsLeastSquaresSolution` on plain vectors (`equation_3_73_iff`). -/
def equation_3_73 (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (xs : Fin n → ℝ) : Prop :=
  ∀ x, ‖toLp 2 (A *ᵥ xs - b)‖ ^ 2 ≤ ‖toLp 2 (A *ᵥ x - b)‖ ^ 2

/-- (3.73) is the backbone's `Matrix.IsLeastSquaresSolution A b x*` on `EuclideanSpace`. -/
theorem equation_3_73_iff (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (xs : Fin n → ℝ) :
    equation_3_73 A b xs ↔ IsLeastSquaresSolution A (toLp 2 b) (toLp 2 xs) := by
  simp only [equation_3_73, IsLeastSquaresSolution, toEuclideanLin_toLp, ← toLp_sub,
    sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
  exact ⟨fun h y => h (ofLp y), fun h x => h (toLp 2 x)⟩

/-- **(3.74), the normal equations.** `x*` is a least-squares solution of `A x = b` iff it solves
the square system `Aᵀ A x* = Aᵀ b` (backbone `Matrix.isLeastSquaresSolution_iff_normalEquations`;
the book derives it from `∇Φ(x*) = 0`, the backbone from the projection theorem). -/
theorem equation_3_74 (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (xs : Fin n → ℝ) :
    equation_3_73 A b xs ↔ (Aᵀ * A) *ᵥ xs = Aᵀ *ᵥ b := by
  rw [equation_3_73_iff, isLeastSquaresSolution_iff_normalEquations,
    conjTranspose_eq_transpose_of_trivial, toEuclideanLin_toLp, toEuclideanLin_toLp,
    (toLp_injective 2).eq_iff]

/-- **§3.13, after (3.74).** If `A` has full rank, `B = Aᵀ A` is symmetric positive definite, the
system of normal equations is nonsingular, and the least-squares solution exists and is unique
(backbone `Matrix.posDef_conjTranspose_mul_self_of_linearIndependent`,
`Matrix.existsUnique_isLeastSquaresSolution`). -/
theorem normalMatrix_posDef {A : Matrix (Fin m) (Fin n) ℝ} (hA : LinearIndependent ℝ Aᵀ) :
    (Aᵀ * A).PosDef ∧ IsUnit (Aᵀ * A) ∧ ∀ b : Fin m → ℝ, ∃! xs, equation_3_73 A b xs := by
  have hpd : (Aᵀ * A).PosDef := by
    rw [← conjTranspose_eq_transpose_of_trivial]
    exact posDef_conjTranspose_mul_self_of_linearIndependent hA
  refine ⟨hpd, hpd.isUnit, fun b => ?_⟩
  obtain ⟨x, hx, huniq⟩ := existsUnique_isLeastSquaresSolution hA (toLp 2 b)
  refine ⟨ofLp x, ?_, fun y hy => ?_⟩
  · change equation_3_73 A b (ofLp x)
    rw [equation_3_73_iff, toLp_ofLp]
    exact hx
  · have := huniq (toLp 2 y) ((equation_3_73_iff A b y).1 hy)
    rw [← this, ofLp_toLp]

/-- **§3.13, the Cholesky route to the normal equations.** For `A` of full rank, `Aᵀ A` has the
Cholesky factorization `Aᵀ A = Hᵀ H` of Theorem 3.6, and the least-squares solution is obtained
by solving the two triangular systems `Hᵀ y = Aᵀ b` and `H x* = y`. -/
theorem normalEquations_cholesky {A : Matrix (Fin m) (Fin n) ℝ} (hA : LinearIndependent ℝ Aᵀ)
    (b : Fin m → ℝ) :
    ∃ H : Matrix (Fin n) (Fin n) ℝ, (H.IsUpperTriangular ∧ (∀ i, 0 < H i i) ∧ Hᵀ * H = Aᵀ * A) ∧
      ∀ xs, equation_3_73 A b xs ↔ ∃ y, Hᵀ *ᵥ y = Aᵀ *ᵥ b ∧ H *ᵥ xs = y := by
  obtain ⟨H, hH, -⟩ := theorem_3_6 (normalMatrix_posDef hA).1
  refine ⟨H, hH, fun xs => ?_⟩
  rw [equation_3_74, ← hH.2.2, ← mulVec_mulVec]
  exact ⟨fun h => ⟨_, h, rfl⟩, fun ⟨y, hy, hxs⟩ => hxs ▸ hy⟩

/-! ### Theorem 3.8: the QR route -/

section QR

variable {A : Matrix (Fin m) (Fin n) ℝ} {Q : Matrix (Fin m) (Fin m) ℝ}
variable {R : Matrix (Fin m) (Fin n) ℝ}

/-- **Theorem 3.8, (3.75).** Let `A ∈ ℝ^{m×n}`, `m ≥ n`, have full rank, with QR factorization
`A = Q R` and reduced factors `R̃ ∈ ℝ^{n×n}`, `Q̃ ∈ ℝ^{m×n}` of (3.48). Then the unique solution
of (3.73) is `x* = R̃⁻¹ Q̃ᵀ b` (backbone `Matrix.IsQR.isLeastSquaresSolution`; uniqueness from
`normalMatrix_posDef`). -/
theorem theorem_3_8 (hA : LinearIndependent ℝ Aᵀ) (h : IsQR A Q R) (hnm : n ≤ m)
    (b : Fin m → ℝ) :
    equation_3_73 A b ((firstRows R hnm)⁻¹ *ᵥ ((firstColumns Q hnm)ᵀ *ᵥ b)) ∧
      ∀ xs, equation_3_73 A b xs → xs = (firstRows R hnm)⁻¹ *ᵥ ((firstColumns Q hnm)ᵀ *ᵥ b) := by
  have h1 : equation_3_73 A b ((firstRows R hnm)⁻¹ *ᵥ ((firstColumns Q hnm)ᵀ *ᵥ b)) := by
    rw [equation_3_73_iff, mulVec_mulVec, ← conjTranspose_eq_transpose_of_trivial,
      ← toEuclideanLin_toLp]
    exact h.isLeastSquaresSolution hnm hA (toLp 2 b)
  obtain ⟨x, -, huniq⟩ := (normalMatrix_posDef hA).2.2 b
  exact ⟨h1, fun xs hxs => (huniq xs hxs).trans (huniq _ h1).symm⟩

/-- **Theorem 3.8, the minimum, and the displays of its proof.** Through a QR factorization
`A = Q R`, `‖A x - b‖₂² = ‖R x - Qᵀ b‖₂²` since `Q` preserves the Euclidean norm; as `R` is upper
trapezoidal, `‖R x - Qᵀ b‖₂² = ‖R̃ x - Q̃ᵀ b‖₂² + ∑_{i=n+1}^{m} ((Qᵀ b)_i)²` for every `x`; and for
`A` of full rank the minimum of `Φ` is `Φ(x*) = ∑_{i=n+1}^{m} ((Qᵀ b)_i)²` (backbone
`Matrix.IsQR.norm_sub_eq`, `Matrix.norm_sub_sq_eq_of_isQR`,
`Matrix.norm_sub_sq_eq_of_isQR_of_isLeastSquaresSolution`). -/
theorem theorem_3_8_min (h : IsQR A Q R) (hnm : n ≤ m) (b : Fin m → ℝ) :
    (∀ x, ‖toLp 2 (A *ᵥ x - b)‖ = ‖toLp 2 (R *ᵥ x - Qᵀ *ᵥ b)‖) ∧
      (∀ x, ‖toLp 2 (A *ᵥ x - b)‖ ^ 2 =
        ‖toLp 2 (firstRows R hnm *ᵥ x - (firstColumns Q hnm)ᵀ *ᵥ b)‖ ^ 2 +
          ∑ i ∈ univ.filter (fun i : Fin m => n ≤ i), ((Qᵀ *ᵥ b) i) ^ 2) ∧
      (LinearIndependent ℝ Aᵀ → ∀ xs, equation_3_73 A b xs →
        ‖toLp 2 (A *ᵥ xs - b)‖ ^ 2 =
          ∑ i ∈ univ.filter (fun i : Fin m => n ≤ i), ((Qᵀ *ᵥ b) i) ^ 2) := by
  refine ⟨fun x => ?_, fun x => ?_, fun hA xs hxs => ?_⟩
  · have := h.norm_sub_eq (toLp 2 b) (toLp 2 x)
    rwa [conjTranspose_eq_transpose_of_trivial, toEuclideanLin_toLp, toEuclideanLin_toLp,
      ← toLp_sub, ← toLp_sub] at this
  · have := norm_sub_sq_eq_of_isQR h hnm (toLp 2 b) (toLp 2 x)
    simpa only [toEuclideanLin_toLp, ← toLp_sub, conjTranspose_eq_transpose_of_trivial,
      ofLp_toLp, Real.norm_eq_abs, sq_abs] using this
  · have := norm_sub_sq_eq_of_isQR_of_isLeastSquaresSolution h hnm hA
      ((equation_3_73_iff A b xs).1 hxs)
    simpa only [toEuclideanLin_toLp, ← toLp_sub, conjTranspose_eq_transpose_of_trivial,
      ofLp_toLp, Real.norm_eq_abs, sq_abs] using this

end QR

/-! ### (3.76)–(3.77): the solution of least norm and the pseudoinverse -/

/-- **(3.76).** When `A` does not have full rank the least-squares solution is not unique
(`x* + z` with `z ∈ ker A` is one too), and the problem becomes: find `x* ∈ ℝⁿ` *with minimal
Euclidean norm* such that `‖A x* - b‖₂² ≤ min_x ‖A x - b‖₂²`: the backbone's
`Matrix.IsMinNormLeastSquaresSolution` on plain vectors (`equation_3_76_iff`). -/
def equation_3_76 (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (xs : Fin n → ℝ) : Prop :=
  equation_3_73 A b xs ∧ ∀ x, equation_3_73 A b x → ‖toLp 2 xs‖ ≤ ‖toLp 2 x‖

/-- (3.76) is the backbone's `Matrix.IsMinNormLeastSquaresSolution A b x*` on `EuclideanSpace`. -/
theorem equation_3_76_iff (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (xs : Fin n → ℝ) :
    equation_3_76 A b xs ↔ IsMinNormLeastSquaresSolution A (toLp 2 b) (toLp 2 xs) := by
  simp only [equation_3_76, IsMinNormLeastSquaresSolution, equation_3_73_iff]
  exact ⟨fun ⟨h1, h2⟩ => ⟨h1, fun y hy => h2 (ofLp y) hy⟩,
    fun ⟨h1, h2⟩ => ⟨h1, fun x hx => h2 (toLp 2 x) hx⟩⟩

/-- **§3.13, "(3.76) is consistent with (3.73) if `A` has full rank"**: the least-squares
solution is then unique, so it is the one of minimal Euclidean norm. -/
theorem equation_3_76_of_linearIndependent {A : Matrix (Fin m) (Fin n) ℝ}
    (hA : LinearIndependent ℝ Aᵀ) (b : Fin m → ℝ) (xs : Fin n → ℝ) :
    equation_3_76 A b xs ↔ equation_3_73 A b xs := by
  refine ⟨fun h => h.1, fun h => ⟨h, fun x hx => ?_⟩⟩
  obtain ⟨y, -, huniq⟩ := (normalMatrix_posDef hA).2.2 b
  rw [(huniq xs h).trans (huniq x hx).symm]

/-- **Theorem 3.9, (3.77).** Let `A ∈ ℝ^{m×n}` (with SVD `A = U Σ Vᵀ`). Then `x* = A⁺ b`, with
`A⁺` the pseudoinverse of Definition 1.15 (`Matrix.pinv`), is a solution of (3.76) (backbone
`Matrix.isMinNormLeastSquaresSolution_pinv`); it is the unique one by `theorem_3_9_unique`. -/
theorem theorem_3_9 (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    equation_3_76 A b (A.pinv *ᵥ b) := by
  rw [equation_3_76_iff, ← toEuclideanLin_toLp]
  exact isMinNormLeastSquaresSolution_pinv A (toLp 2 b)

/-- **Theorem 3.9, uniqueness.** Every solution of (3.76) is `A⁺ b` (backbone
`Matrix.IsMinNormLeastSquaresSolution.eq_pinv`). -/
theorem theorem_3_9_unique {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ} {xs : Fin n → ℝ}
    (h : equation_3_76 A b xs) : xs = A.pinv *ᵥ b := by
  have := ((equation_3_76_iff A b xs).1 h).eq_pinv
  rwa [toEuclideanLin_toLp, (toLp_injective 2).eq_iff] at this

/-! ### Example 3.11 -/

/-- **Example 3.11, the rank-deficient system.** For `A = [1 0; 0 0; 0 0]` and `b = (1, 2, 3)ᵀ`,
`rank(A) = 1` (the columns of `A` are dependent), the pseudoinverse is `A⁺ = [1 0 0; 0 0 0]` (by
the Penrose conditions, `Matrix.pinv_unique`), and the solution of (3.76) is
`x* = A⁺ b = (1, 0)ᵀ`. -/
theorem example_3_11 :
    let A : Matrix (Fin 3) (Fin 2) ℝ := !![1, 0; 0, 0; 0, 0]
    let b : Fin 3 → ℝ := ![1, 2, 3]
    A.rank = 1 ∧ ¬ LinearIndependent ℝ Aᵀ ∧ A.pinv = !![1, 0, 0; 0, 0, 0] ∧
      A.pinv *ᵥ b = ![1, 0] ∧ equation_3_76 A b ![1, 0] := by
  intro A b
  have hpinv : A.pinv = !![1, 0, 0; 0, 0, 0] := by
    symm
    refine pinv_unique A ?_ ?_ ?_ ?_
    · ext i j; fin_cases i <;> fin_cases j <;> simp [A, Matrix.mul_apply, Fin.sum_univ_succ]
    · ext i j; fin_cases i <;> fin_cases j <;> simp [A, Matrix.mul_apply, Fin.sum_univ_succ]
    · ext i j; fin_cases i <;> fin_cases j <;> simp [A, Matrix.mul_apply, Fin.sum_univ_succ]
    · ext i j; fin_cases i <;> fin_cases j <;> simp [A, Matrix.mul_apply, Fin.sum_univ_succ]
  have hsol : A.pinv *ᵥ b = ![1, 0] := by
    rw [hpinv]
    ext i; fin_cases i <;> simp [b, mulVec, dotProduct, Fin.sum_univ_succ]
  have hdep : ¬ LinearIndependent ℝ Aᵀ := fun h =>
    h.ne_zero 1 (by ext i; fin_cases i <;> simp [A])
  have hrank : A.rank = 1 := by
    have hle : A.rank ≤ 1 := by
      have : A = vecMulVec ![1, 0, 0] ![1, 0] := by
        ext i j; fin_cases i <;> fin_cases j <;> simp [A, vecMulVec_apply]
      rw [this]
      exact rank_vecMulVec_le _ _
    refine le_antisymm hle (Nat.one_le_iff_ne_zero.2 fun h0 => ?_)
    rw [rank, Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at h0
    have := congrFun (congrArg (fun f => f ![1, 0]) h0) 0
    simp [A, mulVec, dotProduct, Fin.sum_univ_succ] at this
  exact ⟨hrank, hdep, hpinv, hsol, hsol ▸ theorem_3_9 A b⟩

/-- **Example 3.11, the perturbed system.** Perturbing the null entry `a₂₂` to `ε ≠ 0` (the book
takes `ε = 10⁻¹²`) gives `A_ε = [1 0; 0 ε; 0 0]` of full rank `2`, whose least-squares solution
(unique in the sense of (3.73)) is `x̂* = (1, 2/ε)ᵀ = (1, 2 · 10¹²)ᵀ`: the solution of (3.76) is
not a continuous function of the data when `A` is rank deficient. -/
theorem example_3_11_perturbed {ε : ℝ} (hε : ε ≠ 0) :
    let Aε : Matrix (Fin 3) (Fin 2) ℝ := !![1, 0; 0, ε; 0, 0]
    let b : Fin 3 → ℝ := ![1, 2, 3]
    Aε.rank = 2 ∧ LinearIndependent ℝ Aεᵀ ∧ (∀ xs, equation_3_73 Aε b xs ↔ xs = ![1, 2 / ε]) ∧
      (ε = 1 / 10 ^ 12 → (![1, 2 / ε] : Fin 2 → ℝ) = ![1, 2 * 10 ^ 12]) := by
  intro Aε b
  have hli : LinearIndependent ℝ Aεᵀ := by
    refine Fintype.linearIndependent_iff.2 fun g hg => ?_
    have h0 : g 0 = 0 := by simpa [Aε, Fin.sum_univ_two] using congrFun hg 0
    have h1 : g 1 = 0 := by simpa [Aε, Fin.sum_univ_two, hε] using congrFun hg 1
    rw [Fin.forall_fin_two]
    exact ⟨h0, h1⟩
  refine ⟨?_, hli, fun xs => ?_, fun h => ?_⟩
  · rw [← rank_transpose]
    exact hli.rank_matrix
  · rw [equation_3_74]
    constructor
    · intro hxs
      have h0 := congrFun hxs 0
      have h1 := congrFun hxs 1
      simp [Aε, b, Matrix.mul_apply, mulVec, dotProduct, Fin.sum_univ_succ] at h0 h1
      ext i
      fin_cases i
      · simpa using h0
      · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
        rw [eq_div_iff hε]
        apply mul_left_cancel₀ hε
        linear_combination h1
    · rintro rfl
      ext i
      fin_cases i
      · simp [Aε, b, Matrix.mul_apply, mulVec, dotProduct, Fin.sum_univ_succ]
      · simp [Aε, b, Matrix.mul_apply, mulVec, dotProduct, Fin.sum_univ_succ]
        field_simp
  · rw [h]
    norm_num

/-! ### Underdetermined systems -/

/-- **§3.13, underdetermined systems.** For `m < n` and `A` of full (row) rank, the system
`A x = b` is consistent and its solution of minimal Euclidean norm is `x* = A⁺ b = Aᵀ (A Aᵀ)⁻¹ b`
(backbone `Matrix.pinv_eq_conjTranspose_mul_inv_self_mul_conjTranspose`,
`Matrix.toEuclideanLin_conjTranspose_mul_inv_self_mul_conjTranspose`, with Theorem 3.9). -/
theorem underdetermined_minNorm {A : Matrix (Fin m) (Fin n) ℝ} (hA : LinearIndependent ℝ A)
    (b : Fin m → ℝ) :
    A.pinv = Aᵀ * (A * Aᵀ)⁻¹ ∧ A *ᵥ (Aᵀ *ᵥ ((A * Aᵀ)⁻¹ *ᵥ b)) = b ∧
      equation_3_76 A b (Aᵀ *ᵥ ((A * Aᵀ)⁻¹ *ᵥ b)) ∧
        ∀ x, A *ᵥ x = b → ‖toLp 2 (Aᵀ *ᵥ ((A * Aᵀ)⁻¹ *ᵥ b))‖ ≤ ‖toLp 2 x‖ := by
  have hp : A.pinv = Aᵀ * (A * Aᵀ)⁻¹ := by
    rw [← conjTranspose_eq_transpose_of_trivial]
    exact pinv_eq_conjTranspose_mul_inv_self_mul_conjTranspose hA
  have hsol : A *ᵥ (Aᵀ *ᵥ ((A * Aᵀ)⁻¹ *ᵥ b)) = b := by
    have := toEuclideanLin_conjTranspose_mul_inv_self_mul_conjTranspose hA (toLp 2 b)
    rwa [conjTranspose_eq_transpose_of_trivial, toEuclideanLin_toLp, toEuclideanLin_toLp,
      (toLp_injective 2).eq_iff, ← mulVec_mulVec] at this
  have h76 : equation_3_76 A b (Aᵀ *ᵥ ((A * Aᵀ)⁻¹ *ᵥ b)) := by
    have := theorem_3_9 A b
    rwa [hp, ← mulVec_mulVec] at this
  refine ⟨hp, hsol, h76, fun x hx => h76.2 x fun y => ?_⟩
  rw [hx, sub_self, toLp_zero, norm_zero, zero_pow two_ne_zero]
  positivity

/-- **§3.13, the QR factorization of `Aᵀ`.** For `m < n` and `A` of full rank, the QR
factorization applied to `Aᵀ = Q R` with reduced factors `Q̃ ∈ ℝ^{n×m}`, `R̃ ∈ ℝ^{m×m}` yields the
solution of minimal Euclidean norm: `R̃` is nonsingular, `A Aᵀ = R̃ᵀ R̃`, and
`x* = Aᵀ (A Aᵀ)⁻¹ b = Q̃ R̃⁻ᵀ b`, obtained from one triangular solve. -/
theorem underdetermined_qr {A : Matrix (Fin m) (Fin n) ℝ} (hA : LinearIndependent ℝ A)
    {Q : Matrix (Fin n) (Fin n) ℝ} {R : Matrix (Fin n) (Fin m) ℝ} (h : IsQR Aᵀ Q R) (hmn : m ≤ n)
    (b : Fin m → ℝ) :
    IsUnit (firstRows R hmn) ∧ A * Aᵀ = (firstRows R hmn)ᵀ * firstRows R hmn ∧
      Aᵀ *ᵥ ((A * Aᵀ)⁻¹ *ᵥ b) = firstColumns Q hmn *ᵥ ((firstRows R hmn)ᵀ⁻¹ *ᵥ b) ∧
        equation_3_76 A b (firstColumns Q hmn *ᵥ ((firstRows R hmn)ᵀ⁻¹ *ᵥ b)) := by
  have hA' : LinearIndependent ℝ Aᵀᵀ := by rwa [transpose_transpose]
  have hR : IsUnit (firstRows R hmn) := h.isUnit_firstRows_of_linearIndependent hmn hA'
  obtain ⟨hAT, hQ, -⟩ := property_3_3 h hmn
  have hA_eq : A = (firstRows R hmn)ᵀ * (firstColumns Q hmn)ᵀ := by
    rw [← transpose_mul, ← hAT, transpose_transpose]
  have hAAT : A * Aᵀ = (firstRows R hmn)ᵀ * firstRows R hmn := by
    rw [hA_eq, transpose_mul, transpose_transpose, transpose_transpose, Matrix.mul_assoc,
      ← Matrix.mul_assoc (firstColumns Q hmn)ᵀ, hQ, Matrix.one_mul]
  have hx : Aᵀ *ᵥ ((A * Aᵀ)⁻¹ *ᵥ b) = firstColumns Q hmn *ᵥ ((firstRows R hmn)ᵀ⁻¹ *ᵥ b) := by
    rw [hAAT, mulVec_mulVec, mulVec_mulVec, hAT, Matrix.mul_inv_rev, Matrix.mul_assoc,
      ← Matrix.mul_assoc (firstRows R hmn), mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hR),
      Matrix.one_mul]
  exact ⟨hR, hAAT, hx, hx ▸ (underdetermined_minNorm hA b).2.2.1⟩

end QuarteroniSaccoSaleri.Chapter03
